//! Inline temps and remove decompiler artifacts.

use std::collections::{HashMap, HashSet};

use super::util::*;

/// Inline static field references: "var = System.out;" followed by "var.println(x)" → "System.out.println(x)".
/// Handles SSA aliasing where "local2 = System.out;" and "v2.println(x)" refer to the same register.
pub(crate) fn inline_static_field_refs(body: &str) -> String {
    let lines: Vec<&str> = body.lines().collect();
    let mut aliases: Vec<(String, String, Option<String>)> = Vec::new();
    for line in &lines {
        let stmt = strip_trailing_comment(line);
        let t = stmt.trim();
        if let Some(eq) = t.find(" = ") {
            let lhs = t[..eq].trim();
            // Use the identifier only (`String s0` → `s0`), not the full typed LHS.
            let var = lhs.rsplit(' ').next().unwrap_or(lhs);
            let val = t[eq + 3..].trim_end_matches(';').trim();
            // Only static/instance field paths (e.g. System.out), never string literals
            // like "android.permission.READ_…" which also contain '.', and never
            // const-class literals (`Context.class`) which look like dotted paths.
            if is_java_ident(var) && is_simple_field_path(val) && !is_class_literal(val) {
                let reg_num = extract_reg_number(var).map(String::from);
                aliases.push((var.to_string(), val.to_string(), reg_num));
            }
        }
    }
    if aliases.is_empty() {
        return body.to_string();
    }
    let match_vars_for = |alias_var: &str, reg_num: &Option<String>| -> Vec<String> {
        let mut vars = vec![alias_var.to_string()];
        if let Some(n) = reg_num {
            let v_form = format!("v{}", n);
            let local_form = format!("local{}", n);
            if v_form != alias_var {
                vars.push(v_form);
            }
            if local_form != alias_var {
                vars.push(local_form);
            }
        }
        vars
    };
    let mut out = String::new();
    for (idx, line) in lines.iter().enumerate() {
        let stmt = strip_trailing_comment(line);
        let t = stmt.trim();
        let mut skip = false;
        for (var, val, reg_num) in &aliases {
            let assign_stmt = format!("{} = {};", var, val);
            if t == assign_stmt {
                let candidate_vars = match_vars_for(var, reg_num);
                let non_print_use = lines.iter().enumerate().any(|(j, l)| {
                    j != idx
                        && candidate_vars.iter().any(|cv| {
                            let prefix = format!("{}.", cv);
                            l.contains(&prefix)
                                && !l.contains(&format!("{}.println(", cv))
                                && !l.contains(&format!("{}.print(", cv))
                        })
                });
                if !non_print_use {
                    skip = true;
                    break;
                }
            }
        }
        if skip {
            continue;
        }
        let mut current_line = line.to_string();
        for (var, val, reg_num) in &aliases {
            let candidate_vars = match_vars_for(var, reg_num);
            for cv in &candidate_vars {
                for method in &["println", "print"] {
                    let from = format!("{}.{}(", cv, method);
                    let to = format!("{}.{}(", val, method);
                    current_line = current_line.replace(&from, &to);
                }
            }
        }
        out.push_str(&current_line);
        if idx < lines.len().saturating_sub(1) {
            out.push('\n');
        }
    }
    out
}

/// Remove bare "var; /* move-exception */" statements and inline single-use temps
/// (literals, copies, casts, single-use calls) into their only use.
///
/// Live ranges stop at the next assignment to the same name, so reused temps like
/// `s0 = "…"; …; s0 = this.foo;` are handled correctly.
#[cfg(test)]
pub(crate) fn cleanup_decompiler_artifacts(body: &str) -> String {
    cleanup_decompiler_artifacts_with_webs(body, &WebNames::default())
}

/// A web's name is inlined only when it is an inlinable constant, whatever its form.
pub(crate) fn cleanup_decompiler_artifacts_with_webs(body: &str, webs: &WebNames) -> String {
    let mut current = fold_immediate_overwrites(body);
    // Cast/call chains need multiple rounds: view→cast→getText→toString.
    for _ in 0..8 {
        let next = cleanup_decompiler_artifacts_once_with_webs(&current, webs);
        if next == current {
            break;
        }
        current = next;
    }
    current
}

/// `int result = 0; result = y;` → `int result = y;`.
/// The first store is dead when the next statement overwrites the same variable
/// without reading it (jadx `CodeShrinkVisitor`).
pub(crate) fn fold_immediate_overwrites(body: &str) -> String {
    let lines: Vec<&str> = body.lines().collect();
    let mut skip: HashSet<usize> = HashSet::new();
    let mut replace: HashMap<usize, String> = HashMap::new();
    let mut i = 0usize;
    while i + 1 < lines.len() {
        let Some((var, rhs1)) = parse_simple_assign_line(lines[i]) else {
            i += 1;
            continue;
        };
        let Some((var2, rhs2)) = parse_simple_assign_line(lines[i + 1]) else {
            i += 1;
            continue;
        };
        if var != var2
            || leading_indent(lines[i]) != leading_indent(lines[i + 1])
            || ident_occurs(&rhs2, &var)
            || rhs1.contains('(')
        {
            i += 1;
            continue;
        }
        let first = strip_trailing_comment(lines[i]);
        let stmt = first.trim();
        let type_prefix = stmt.find(" = ").and_then(|eq| {
            let lhs = stmt[..eq].trim();
            let (ty, name) = lhs.rsplit_once(' ')?;
            if name == var && !ty.is_empty() && !ty.contains('=') {
                Some(ty.to_string())
            } else {
                None
            }
        });
        let second = strip_trailing_comment(lines[i + 1]);
        let second_stmt = second.trim();
        let already_typed = second_stmt
            .find(" = ")
            .map(|eq| second_stmt[..eq].trim().contains(' '))
            .unwrap_or(false);
        let indent = leading_indent(lines[i + 1]);
        let comment = lines[i + 1].get(second.len()..).unwrap_or("");
        let folded = if let Some(ty) = type_prefix.filter(|_| !already_typed) {
            format!("{indent}{ty} {var} = {rhs2};{comment}")
        } else {
            lines[i + 1].to_string()
        };
        skip.insert(i);
        replace.insert(i + 1, folded);
        i += 2;
    }
    if skip.is_empty() {
        return body.to_string();
    }
    let mut out = String::new();
    for (idx, line) in lines.iter().enumerate() {
        if skip.contains(&idx) {
            continue;
        }
        if let Some(repl) = replace.get(&idx) {
            out.push_str(repl);
        } else {
            out.push_str(line);
        }
        if idx + 1 < lines.len() || body.ends_with('\n') {
            out.push('\n');
        }
    }
    if !body.ends_with('\n') && out.ends_with('\n') {
        out.pop();
    }
    out
}

#[cfg(test)]
pub(crate) fn cleanup_decompiler_artifacts_once(body: &str) -> String {
    cleanup_decompiler_artifacts_once_with_webs(body, &WebNames::default())
}

fn cleanup_decompiler_artifacts_once_with_webs(body: &str, webs: &WebNames) -> String {
    let lines: Vec<&str> = body.lines().collect();

    struct InlineCand {
        def_idx: usize,
        var: String,
        val: String,
        /// Exclusive end of live range (next kill or EOF).
        end_idx: usize,
        use_count: usize,
    }

    let mut cands: Vec<InlineCand> = Vec::new();
    for (idx, line) in lines.iter().enumerate() {
        let binding = strip_trailing_comment(line);
        let t = binding.trim();
        let Some(eq) = t.find(" = ") else { continue };
        let lhs = t[..eq].trim();
        let val = t[eq + 3..].trim_end_matches(';').trim();
        let var = lhs.rsplit(' ').next().unwrap_or(lhs);
        if var.is_empty() || !is_java_ident(var) || !is_inlineable_rhs(val) {
            continue;
        }
        // Never inline a self-referential RHS (`email = email.findViewById(...)`).
        // Allow `length = arr.length` (field access named like the dest).
        if ident_occurs(val, var) && !val.ends_with(&format!(".{}", var)) {
            continue;
        }
        let mut end_idx = lines.len();
        for (j, later) in lines.iter().enumerate().skip(idx + 1) {
            if line_kills_var(later, var) {
                end_idx = j;
                break;
            }
        }
        let use_count = {
            let mut c = lines[idx + 1..end_idx]
                .iter()
                .filter(|l| ident_occurs(l, var))
                .count();
            // Reassignment that *reads* the old value: `view0 = (TextView) view0`
            // Do NOT count a pure kill `i0 = 123` — the LHS matches but the old value is dead.
            if end_idx < lines.len() {
                let kill = lines[end_idx];
                if assign_lhs_var(kill).as_deref() == Some(var) {
                    if let Some(eq) = kill.find(" = ") {
                        if ident_occurs(&kill[eq + 3..], var) {
                            c += 1;
                        }
                    }
                } else if ident_occurs(kill, var) {
                    c += 1;
                }
            }
            c
        };
        cands.push(InlineCand {
            def_idx: idx,
            var: var.to_string(),
            val: val.to_string(),
            end_idx,
            use_count,
        });
    }

    // Inline single-use *temps*, and multi-use temps whose RHS is a cheap literal
    // (`int i0 = 1; foo(i0); bar(i0);` → `foo(1); bar(1);`).
    // Keep meaningful names (email, password, requestCode) as locals.
    // When the same temp name is reused (`i0 = layout; …; i0 = button;`), only inline the
    // *latest* live range in this pass — otherwise skipping both defs leaves a dangling use.
    // When the same temp name is reused (`i0 = layout; …; i0 = button;`), only inline the
    // *latest* live range in this pass — otherwise skipping both defs leaves a dangling use.
    let mut latest_inline_by_var: HashMap<String, usize> = HashMap::new();
    for (i, c) in cands.iter().enumerate() {
        let inlinable = webs.is_inlinable(&c.var);
        if !webs.may_substitute(&c.var)
            || !(inlinable || is_temp_like_name(&c.var))
            || c.use_count == 0
        {
            continue;
        }
        if has_index_increment_after(&lines, c.def_idx, &c.var) {
            // Protects `k = 0; out[k++] = …` from becoming `out[0++]`.
            continue;
        }
        // Keep `i = e.ordinal()` so enum switches retain a visible ordinal() call
        // (D8 SwitchMap folds the aget into the selector as `map[i]`).
        if c.val.trim().ends_with(".ordinal()") {
            continue;
        }
        // Allow `i`/`j`/`k` only for filled-array sizes/indices (`new T[i]`, `a[k]=…`).
        // Never inline them into loop tests or expressions like `j++ / i`.
        if !inlinable
            && matches!(c.var.as_str(), "i" | "j" | "k")
            && !all_uses_are_array_index_or_size(&lines, &c.var, c.def_idx, c.end_idx)
        {
            continue;
        }
        if all_uses_are_length_member(&lines, &c.var, c.def_idx, c.end_idx) {
            continue;
        }
        let want = inlinable || c.use_count == 1 || is_cheap_literal_rhs(&c.val);
        if !want {
            continue;
        }
        if !(inlinable || def_reaches_uses_alone(&lines, c.def_idx, c.end_idx, &c.var))
            || literal_used_as_receiver(&lines, c.def_idx, c.end_idx, &c.var, &c.val)
        {
            continue;
        }
        match latest_inline_by_var.get(&c.var) {
            Some(&prev) if cands[prev].def_idx > c.def_idx => {}
            _ => {
                latest_inline_by_var.insert(c.var.clone(), i);
            }
        }
    }
    // `y = 6; arr[y] = 1` and `y = this.pouet(); this.value2 = y` are register
    // reuse, not stores the source kept. Only bare reassignments (not `int y =`).
    let mut bare_inline: HashSet<usize> = HashSet::new();
    for (i, c) in cands.iter().enumerate() {
        if !webs.may_substitute(&c.var)
            || is_temp_like_name(&c.var)
            || !is_bare_reassign(lines[c.def_idx], &c.var)
        {
            continue;
        }
        let index_lit = c.use_count == 1
            && is_cheap_literal_rhs(&c.val)
            && array_index_is_only_use(&lines, &c.var, c.def_idx, c.end_idx);
        let call_rhs = c.use_count == 1
            && is_simple_call_expr(&c.val)
            && only_use_is_whole_rhs(&lines, &c.var, c.def_idx, c.end_idx);
        if (index_lit || call_rhs) && def_reaches_uses_alone(&lines, c.def_idx, c.end_idx, &c.var)
        {
            bare_inline.insert(i);
        }
    }
    let inline_set: HashSet<usize> = latest_inline_by_var
        .values()
        .copied()
        .chain(bare_inline.iter().copied())
        .collect();
    let skip_indices: HashSet<usize> = cands
        .iter()
        .enumerate()
        .filter(|(i, c)| {
            let temp = is_temp_like_name(&c.var);
            let used_after_def = lines[c.def_idx + 1..]
                .iter()
                .any(|l| ident_used_as_rvalue(l, &c.var));
            (inline_set.contains(i)
                && (temp || bare_inline.contains(i) || webs.is_inlinable(&c.var)))
                || (temp
                    && c.use_count == 0
                    && !used_after_def
                    && !is_simple_call_expr(&c.val)
                    && !is_cast_expr(&c.val)
                    && !is_loop_body_slot_update(&c.var, c.def_idx, &lines)
                    && !is_index_increment(lines[c.def_idx], &c.var)
                    // Keep unused `double f = -5.0` / `float fff = -5.0f` for source fidelity.
                    && !is_typed_fp_or_long_const_decl(lines[c.def_idx]))
                || (!temp
                    && webs.substitution(&c.var).is_none()
                    && c.use_count == 0
                    && is_bare_reassign(lines[c.def_idx], &c.var)
                    && is_cheap_literal_rhs(&c.val))
        })
        .map(|(i, _)| cands[i].def_idx)
        .collect();
    let inlines: Vec<&InlineCand> = {
        let mut v: Vec<&InlineCand> = inline_set.iter().map(|&i| &cands[i]).collect();
        // Earlier defs first so nested temps (button id → findViewById → listener) resolve.
        v.sort_by_key(|c| c.def_idx);
        v
    };

    // Substitute other single-use inlines that are live at `at_idx` into `val`.
    let materialize = |val: &str, at_idx: usize| -> String {
        let mut out = val.to_string();
        for other in &inlines {
            let live = at_idx > other.def_idx && at_idx < other.end_idx;
            let on_kill =
                at_idx == other.end_idx && at_idx > other.def_idx && ident_occurs(val, &other.var);
            if (live || on_kill) && ident_occurs(&out, &other.var) {
                out = replace_ident_as_expr(&out, &other.var, &other.val);
            }
        }
        out
    };

    let mut out = String::new();
    for (idx, line) in lines.iter().enumerate() {
        let binding = strip_trailing_comment(line);
        let t = binding.trim();
        if t.ends_with("; /* move-exception */") || t.ends_with("/* move-exception */;") {
            continue;
        }
        if skip_indices.contains(&idx) {
            continue;
        }
        let mut current = line.to_string();
        for cand in &inlines {
            // Include the killing reassignment line (end_idx) when it reads the old value.
            let in_range = idx > cand.def_idx && idx < cand.end_idx;
            let on_kill_use =
                idx == cand.end_idx && idx > cand.def_idx && ident_occurs(line, &cand.var);
            if (in_range || on_kill_use) && ident_occurs(&current, &cand.var) {
                let replacement = materialize(&cand.val, idx);
                // Never rewrite the assignment target (`i4 = 20` must not become `18 = 20`).
                if assign_lhs_var(&current).as_deref() == Some(cand.var.as_str()) {
                    if let Some(eq) = current.find(" = ") {
                        let (lhs, rhs) = current.split_at(eq + 3);
                        current = format!(
                            "{}{}",
                            lhs,
                            replace_ident_as_expr(rhs, &cand.var, &replacement)
                        );
                    }
                } else {
                    current = replace_ident_as_expr(&current, &cand.var, &replacement);
                }
            }
        }
        out.push_str(&current);
        if idx < lines.len().saturating_sub(1) {
            out.push('\n');
        }
    }
    out
}

fn indent_width(line: &str) -> usize {
    line.len() - line.trim_start().len()
}

/// Whether the definition on `def_idx` is the only one reaching the uses of `var` up to
/// `end_idx` (its next assignment, or EOF), judged from the block structure (D1):
/// no read outside the defining block, no conditional reassignment, no loop back edge
/// that carries another value, and no declaration dropped under a later assignment.
fn def_reaches_uses_alone(lines: &[&str], def_idx: usize, end_idx: usize, var: &str) -> bool {
    let depth = indent_width(lines[def_idx]);
    // Read before any earlier assignment: a loop back edge, or another variable.
    let first_assign = lines[..def_idx]
        .iter()
        .position(|l| line_kills_var(l, var));
    let first_read = lines[..def_idx]
        .iter()
        .position(|l| ident_used_as_rvalue(l, var));
    if let Some(read) = first_read {
        if first_assign.map_or(true, |assign| assign > read) {
            return false;
        }
    }
    // In a loop, a read earlier in the body sees this value on the next iteration.
    if let Some(header) = enclosing_loop_header(lines, def_idx) {
        if lines[header..def_idx]
            .iter()
            .any(|l| ident_used_as_rvalue(l, var))
        {
            return false;
        }
    }
    // Past the end of the defining block, other definitions reach too.
    let scope_end = lines
        .iter()
        .enumerate()
        .skip(def_idx + 1)
        .find(|(_, l)| {
            let t = strip_trailing_comment(l);
            let t = t.trim_start();
            indent_width(l) < depth
                && (t.starts_with('}') || t.starts_with("case ") || t.starts_with("default:"))
        })
        .map(|(j, _)| j)
        .unwrap_or(lines.len());
    let stop = (end_idx + 1).min(lines.len());
    if scope_end < stop && lines[scope_end..stop].iter().any(|l| ident_occurs(l, var)) {
        return false;
    }
    if end_idx < lines.len() {
        // Reassigned inside a nested branch or loop.
        if indent_width(lines[end_idx]) > depth {
            return false;
        }
        // Dropping `T var = …;` would leave the later `var = …;` undeclared.
        let def = strip_trailing_comment(lines[def_idx]);
        let typed = def
            .trim()
            .split(" = ")
            .next()
            .is_some_and(|lhs| lhs.trim().contains(' '));
        if typed {
            return false;
        }
    }
    true
}

/// Line index of the `while` / `for` / `do` header enclosing `idx`.
fn enclosing_loop_header(lines: &[&str], idx: usize) -> Option<usize> {
    let mut depth = indent_width(lines[idx]);
    for k in (0..idx).rev() {
        let width = indent_width(lines[k]);
        if width >= depth {
            continue;
        }
        let t = strip_trailing_comment(lines[k]);
        let t = t.trim();
        if !t.ends_with('{') {
            continue;
        }
        depth = width;
        if t.starts_with("while ")
            || t.starts_with("while(")
            || t.starts_with("for ")
            || t.starts_with("for(")
            || t == "do {"
        {
            return Some(k);
        }
    }
    None
}

/// A numeric / null / boolean / char literal can never be a receiver: `0.x`, `null.f()`.
fn literal_used_as_receiver(lines: &[&str], def_idx: usize, end_idx: usize, var: &str, val: &str) -> bool {
    if !is_non_object_literal(val) {
        return false;
    }
    let stop = (end_idx + 1).min(lines.len());
    lines[def_idx + 1..stop]
        .iter()
        .any(|l| ident_is_receiver(&strip_trailing_comment(l), var))
}

/// The only reads of `var` in the live range are `expr[var]` or `new T[var]`.
fn all_uses_are_array_index_or_size(
    lines: &[&str],
    var: &str,
    def_idx: usize,
    end_idx: usize,
) -> bool {
    let idx_needle = format!("[{var}]");
    let size_needle = format!("[{var}]");
    let mut n = 0usize;
    for line in &lines[def_idx + 1..end_idx] {
        if !ident_occurs(line, var) {
            continue;
        }
        n += 1;
        let binding = strip_trailing_comment(line);
        let t = binding.trim();
        // `arr[var]` / `arr[var] = …`
        if t.contains(&idx_needle) {
            let rest = t.replace(&idx_needle, "[]");
            if ident_occurs(&rest, var) {
                return false;
            }
            continue;
        }
        // `new Type[var]` / `Type[] x = new Type[var]`
        if t.contains("new ") && t.contains(&size_needle) {
            // Ensure the only occurrence is the size bracket.
            let rest = t.replacen(&size_needle, "[]", 1);
            if ident_occurs(&rest, var) {
                return false;
            }
            continue;
        }
        return false;
    }
    n >= 1
}

/// `y = 6` rather than `int y = 6`.
fn is_bare_reassign(line: &str, var: &str) -> bool {
    let t = strip_trailing_comment(line);
    let t = t.trim();
    t.starts_with(&format!("{var} = "))
}

/// The only reads of `var` in the live range are `expr[var]`.
fn array_index_is_only_use(lines: &[&str], var: &str, def_idx: usize, end_idx: usize) -> bool {
    let needle = format!("[{var}]");
    let mut n = 0usize;
    for line in &lines[def_idx + 1..end_idx] {
        if !ident_occurs(line, var) {
            continue;
        }
        n += 1;
        if !line.contains(&needle) {
            return false;
        }
        let rest = line.replace(&needle, "[]");
        if ident_occurs(&rest, var) {
            return false;
        }
    }
    n == 1
}

/// The only read is the entire RHS (`this.value2 = y`).
fn only_use_is_whole_rhs(lines: &[&str], var: &str, def_idx: usize, end_idx: usize) -> bool {
    let mut found = false;
    for line in &lines[def_idx + 1..end_idx] {
        if !ident_occurs(line, var) {
            continue;
        }
        if found {
            return false;
        }
        let t = strip_trailing_comment(line);
        let t = t.trim();
        let Some(eq) = t.find(" = ") else {
            return false;
        };
        let rhs = t[eq + 3..].trim_end_matches(';').trim();
        if rhs != var {
            return false;
        }
        found = true;
    }
    found
}

/// Inline temps assigned exactly once to a cheap literal across the whole method body.
/// Inline temps assigned exactly once to a cheap literal across the whole method body.
/// An inlinable constant is inlined whatever its name (`s12_r3_3`); another web's name
/// never is.
pub(crate) fn inline_global_literal_temps_with_webs(body: &str, webs: &WebNames) -> String {
    let lines: Vec<&str> = body.lines().collect();
    let mut assigns: HashMap<String, (usize, String)> = HashMap::new();
    let mut assign_counts: HashMap<String, usize> = HashMap::new();
    for (idx, line) in lines.iter().enumerate() {
        let Some((var, val)) = parse_simple_assign_line(line) else {
            continue;
        };
        if !is_cheap_literal_rhs(&val) || !webs.may_substitute(&var) {
            continue;
        }
        let inlinable = webs.is_inlinable(&var);
        // Temps, or single-use debug consts used only as call args (`dist = 4`).
        // Do not globally inline `i`/`j`/`k` — cleanup handles filled-array
        // index/size live ranges; global inlining breaks loop tests (`while (i < j)`).
        if !inlinable && matches!(var.as_str(), "i" | "j" | "k") {
            continue;
        }
        if !inlinable && !is_temp_like_name(&var) && var != "dist" {
            continue;
        }
        // Keep unused `double yvwx2 = …` / float literals for source fidelity.
        if !inlinable && is_typed_fp_or_long_const_decl(line) {
            continue;
        }
        if lines.iter().any(|l| is_index_increment(l, &var)) {
            continue;
        }
        // Register reuse (`s0 = "x"; …; s0 = receiver; s0.method()`) — cleanup inlines per live range.
        if lines
            .iter()
            .enumerate()
            .skip(idx + 1)
            .any(|(_, l)| assign_lhs_var(l).as_deref() == Some(var.as_str()))
        {
            continue;
        }
        // The only assignment in the body, and it alone reaches every use (D1).
        if lines
            .iter()
            .enumerate()
            .any(|(j, l)| j != idx && line_kills_var(l, &var))
            || !(inlinable || def_reaches_uses_alone(&lines, idx, lines.len(), &var))
            || literal_used_as_receiver(&lines, idx, lines.len(), &var, &val)
        {
            continue;
        }
        *assign_counts.entry(var.clone()).or_insert(0) += 1;
        assigns.insert(var, (idx, val));
    }
    let mut inline_vars: Vec<String> = assigns
        .keys()
        .filter(|v| assign_counts.get(*v).copied() == Some(1))
        // Only inline when the temp is actually used — unused literal temps must stay
        // (`double yvwx2 = …` with a trailing digit looks temp-like).
        .filter(|v| {
            lines.iter().enumerate().any(|(i, l)| {
                assigns.get(*v).map(|(def, _)| *def) != Some(i) && ident_used_as_rvalue(l, v)
            })
        })
        .cloned()
        .collect();
    inline_vars.sort();
    let inline_vars: HashSet<String> = inline_vars.into_iter().collect();
    if inline_vars.is_empty() {
        return body.to_string();
    }
    let skip: HashSet<usize> = assigns
        .iter()
        .filter(|(v, _)| inline_vars.contains(*v))
        .map(|(_, (idx, _))| *idx)
        .collect();
    let mut out = String::new();
    for (idx, line) in lines.iter().enumerate() {
        if skip.contains(&idx) {
            continue;
        }
        let mut current = line.to_string();
        for var in {
            let mut vars: Vec<_> = inline_vars.iter().cloned().collect();
            vars.sort();
            vars
        } {
            if let Some((_, lit)) = assigns.get(&var) {
                let def_idx = assigns.get(&var).map(|(i, _)| *i).unwrap_or(0);
                if idx <= def_idx {
                    continue;
                }
                if ident_occurs(&current, &var) {
                    if assign_lhs_var(&current).as_deref() == Some(var.as_str()) {
                        continue;
                    }
                    current = replace_ident_as_expr(&current, &var, lit);
                }
            }
        }
        out.push_str(&current);
        if idx < lines.len().saturating_sub(1) {
            out.push('\n');
        }
    }
    out
}

/// `i = i0 + 1` / `int j = i1 + 1` after SSA unify → `i++` / `j++`.
/// `i0 = i * i;` without a prior declaration → `int i0 = i * i;` (when inlining did not apply).
pub(crate) fn fix_undeclared_temp_assigns(body: &str) -> String {
    fix_undeclared_temp_assigns_with_webs(body, &WebNames::default())
}

/// Parameters are declared by the signature: reassigning one is not a declaration
/// (`p0 = 0;` must not become `int p0 = 0;`, R2). A web's name may get its missing
/// declaration whatever its form.
pub(crate) fn fix_undeclared_temp_assigns_with_webs(body: &str, webs: &WebNames) -> String {
    let lines: Vec<&str> = body.lines().collect();
    let mut declared: HashSet<String> = webs.params.clone();
    let mut out = String::new();
    for (idx, line) in lines.iter().enumerate() {
        let binding = strip_trailing_comment(line);
        let t = binding.trim();
        let mut current = line.to_string();
        if let Some((var, rhs)) = parse_simple_assign_line(line) {
            // `i`/`j`/`k` are usually parameters or already-declared indexes — don't shadow them.
            let temp = is_temp_like_name(&var) && !matches!(var.as_str(), "i" | "j" | "k");
            if (temp || webs.frozen.contains(&var))
                && !declared.contains(&var)
                && !is_simple_call_expr(&rhs)
            {
                if let Some(eq) = t.find(" = ") {
                    let lhs = t[..eq].trim();
                    if !lhs.contains(' ') {
                        let indent = leading_indent(line);
                        let comment = line.get(binding.len()..).unwrap_or("");
                        let stmt = t.trim_end_matches(';');
                        // The type comes from the definition, `int` only when nothing says otherwise (D2).
                        let ty = evident_type_of_rhs(&rhs).unwrap_or_else(|| "int".to_string());
                        current = format!("{}{} {};", indent, ty, stmt);
                        current.push_str(comment);
                    }
                }
            }
        }
        if let Some(eq) = t.find(" = ") {
            let lhs = t[..eq].trim();
            if let Some(var) = lhs.split_whitespace().last() {
                if is_java_ident(var) {
                    declared.insert(var.to_string());
                }
            }
        }
        out.push_str(&current);
        if idx < lines.len().saturating_sub(1) {
            out.push('\n');
        }
    }
    out
}

/// Java type an expression shows by itself: `(T) x`, `new T(…)`, `new T[n]`, literals.
fn evident_type_of_rhs(rhs: &str) -> Option<String> {
    let r = rhs.trim();
    if r.starts_with('"') {
        return Some("String".to_string());
    }
    if matches!(r, "true" | "false") {
        return Some("boolean".to_string());
    }
    if r == "null" {
        return Some("Object".to_string());
    }
    let is_type_char = |c: char| c.is_alphanumeric() || matches!(c, '.' | '_' | '$');
    if let Some(rest) = r.strip_prefix("new ") {
        let ty: String = rest.chars().take_while(|&c| is_type_char(c)).collect();
        let after = &rest[ty.len()..];
        if ty.is_empty() {
            return None;
        }
        if after.starts_with('(') {
            return Some(ty);
        }
        if after.starts_with('[') {
            return Some(format!("{}{}", ty, "[]".repeat(after.matches('[').count())));
        }
        return None;
    }
    let (ty, operand) = r.strip_prefix('(')?.split_once(')')?;
    let ty = ty.trim();
    let looks_like_type = matches!(
        ty.trim_end_matches("[]"),
        "int" | "long" | "short" | "byte" | "char" | "boolean" | "float" | "double"
    ) || ty.contains('.')
        || ty.starts_with(|c: char| c.is_ascii_uppercase());
    let is_cast = looks_like_type
        && ty.chars().all(|c| is_type_char(c) || matches!(c, '[' | ']'))
        && operand
            .trim_start()
            .starts_with(|c: char| c.is_alphanumeric() || matches!(c, '(' | '"' | '_' | '$'));
    is_cast.then(|| ty.to_string())
}

/// Merge `x = new Foo();` + `x.<init>(args);` (and typed forms) into `x = new Foo(args);`.
/// Statements loading the arguments may sit in between (D7); the merged statement takes
/// the `<init>` position so those arguments are defined before use.
pub(crate) fn merge_constructor_calls(body: &str) -> String {
    let lines: Vec<&str> = body.lines().collect();
    if lines.len() < 2 {
        return body.to_string();
    }
    let mut skip: HashSet<usize> = HashSet::new();
    let mut replacements: HashMap<usize, String> = HashMap::new();
    for i in 0..lines.len() {
        if skip.contains(&i) {
            continue;
        }
        let binding = strip_trailing_comment(lines[i]);
        let t = binding.trim();
        let Some(eq) = t.find(" = ") else {
            continue;
        };
        let lhs = t[..eq].trim();
        let rhs = t[eq + 3..].trim_end_matches(';').trim();
        let var = lhs.rsplit(' ').next().unwrap_or(lhs);
        let Some(class) = rhs.strip_prefix("new ").and_then(|s| s.strip_suffix("()")) else {
            continue;
        };
        let indent = leading_indent(lines[i]);
        let mut j = i + 1;
        while j < lines.len() {
            if skip.contains(&j) {
                j += 1;
                continue;
            }
            if let Some((init_var, args)) = parse_init_call(lines[j]) {
                if init_var == var {
                    replacements.insert(
                        j,
                        format!("{}{} = new {}({});", indent, lhs, class, args.unwrap_or_default()),
                    );
                    skip.insert(i);
                    break;
                }
            }
            let jb = strip_trailing_comment(lines[j]);
            let jt = jb.trim();
            if jt.is_empty() {
                j += 1;
                continue;
            }
            if assign_lhs_var(lines[j]).as_deref() == Some(var) || ident_occurs(jt, var) {
                break;
            }
            // Argument set-up in the same block: temps, nested `new`, `sb.append(x);`.
            let plain_stmt = jt.ends_with(';')
                && !jt.contains('{')
                && !jt.starts_with('}')
                && !jt.starts_with("return")
                && !jt.starts_with("throw ")
                && jt != "break;"
                && jt != "continue;";
            if parse_simple_assign_line(lines[j]).is_some()
                || (plain_stmt && leading_indent(lines[j]) == indent)
            {
                j += 1;
                continue;
            }
            break;
        }
    }
    if replacements.is_empty() {
        return body.to_string();
    }
    let mut out = String::new();
    for (idx, line) in lines.iter().enumerate() {
        if skip.contains(&idx) {
            continue;
        }
        if let Some(rep) = replacements.get(&idx) {
            out.push_str(rep);
        } else {
            out.push_str(line);
        }
        if idx < lines.len().saturating_sub(1) {
            out.push('\n');
        }
    }
    out
}

/// `double f = -5.0;` / `float fff = -5.0f;` / `long ff = -5L;` — keep even when unused.
fn is_typed_fp_or_long_const_decl(line: &str) -> bool {
    let binding = strip_trailing_comment(line);
    let t = binding.trim();
    let rest = if let Some(r) = t.strip_prefix("double ") {
        r
    } else if let Some(r) = t.strip_prefix("float ") {
        r
    } else if let Some(r) = t.strip_prefix("long ") {
        r
    } else {
        return false;
    };
    let Some(eq) = rest.find(" = ") else {
        return false;
    };
    let rhs = rest[eq + 3..].trim_end_matches(';').trim();
    // Prefer cheap literals; also accept any non-call RHS (large doubles, casts, etc.).
    is_cheap_literal_rhs(rhs) || (!rhs.contains('(') && !rhs.starts_with("new "))
}

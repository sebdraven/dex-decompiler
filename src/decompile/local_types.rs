//! Local variable types from def/use constraints over def-use webs (Bellamy, Avgustinov, de Moor, Sereni, « Efficient local type inference », OOPSLA 2008, pp. 475-492, DOI 10.1145/1449764.1449802).

use super::def_webs::{DefKey, DefWebs, ENTRY_DEF};
use super::type_infer::superclass_java;
use crate::decompile::DetHashMap;
use crate::java;
use dex_bytecode::Instruction;
use dex_parser::DexFile;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

const OBJECT: &str = "java.lang.Object";
pub(crate) const THROWABLE: &str = "java.lang.Throwable";

/// Bellamy's types of integer constants: the narrowest range holding the value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum IntRange {
    Z01,
    B127,
    S32767,
    Byte,
    Short,
    Int,
}

impl IntRange {
    const ALL: [IntRange; 6] = [
        Self::Z01,
        Self::B127,
        Self::Byte,
        Self::S32767,
        Self::Short,
        Self::Int,
    ];

    fn bounds(self) -> (i64, i64) {
        match self {
            Self::Z01 => (0, 1),
            Self::B127 => (0, 127),
            Self::S32767 => (0, 32767),
            Self::Byte => (-128, 127),
            Self::Short => (-32768, 32767),
            Self::Int => (i64::from(i32::MIN), i64::from(i32::MAX)),
        }
    }

    fn covering(lo: i64, hi: i64) -> Self {
        Self::ALL
            .into_iter()
            .find(|r| {
                let (a, b) = r.bounds();
                a <= lo && hi <= b
            })
            .unwrap_or(Self::Int)
    }

    fn of(value: i64) -> Self {
        Self::covering(value, value)
    }

    fn join(self, other: Self) -> Self {
        let (a, b) = self.bounds();
        let (c, d) = other.bounds();
        Self::covering(a.min(c), b.max(d))
    }

    fn fits(self, prim: &str) -> bool {
        match self {
            Self::Z01 => matches!(prim, "boolean" | "byte" | "char" | "short" | "int"),
            Self::B127 => matches!(prim, "byte" | "char" | "short" | "int"),
            Self::S32767 => matches!(prim, "char" | "short" | "int"),
            Self::Byte => matches!(prim, "byte" | "short" | "int"),
            Self::Short => matches!(prim, "short" | "int"),
            Self::Int => prim == "int",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum LType {
    Bottom,
    /// Only the constant 0: `null` for a reference, `0` / `false` otherwise.
    Null,
    IntConst(IntRange),
    Prim(&'static str),
    Ref(String),
    Array(Box<LType>),
    Conflict,
}

impl LType {
    fn from_java(ty: &str) -> Self {
        if let Some(elem) = ty.strip_suffix("[]") {
            return Self::Array(Box::new(Self::from_java(elem)));
        }
        match prim(ty) {
            Some(p) => Self::Prim(p),
            None if ty.is_empty() || ty == "void" => Self::Bottom,
            None => Self::Ref(ty.to_string()),
        }
    }

    fn java(&self) -> Option<String> {
        match self {
            Self::Prim(p) => Some(p.to_string()),
            Self::Ref(class) => Some(class.clone()),
            Self::Array(elem) => elem.java().map(|e| e + "[]"),
            _ => None,
        }
    }

    fn is_concrete(&self) -> bool {
        matches!(self, Self::Prim(_) | Self::Ref(_) | Self::Array(_))
    }

    fn is_reference(&self) -> bool {
        matches!(self, Self::Ref(_) | Self::Array(_))
    }
}

/// Upper bound a use puts on the web it reads.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Need {
    Is(LType),
    AnyRef,
    AnyArray,
    /// Any of boolean, byte, char, short, int: bitwise operands, `if-eq` against a primitive.
    IntLike,
}

impl Need {
    fn is_primitive(&self) -> bool {
        matches!(self, Need::IntLike | Need::Is(LType::Prim(_)))
    }
}

#[derive(Clone, Debug)]
pub(crate) struct MethodSig {
    pub(crate) class: String,
    pub(crate) params: Vec<String>,
    pub(crate) ret: String,
}

/// Java types of the constant pool entries the bytecode refers to.
pub(crate) trait TypeEnv {
    fn method(&self, idx: u32) -> Option<MethodSig>;
    /// (declaring class, field type).
    fn field(&self, idx: u32) -> Option<(String, String)>;
    fn type_name(&self, idx: u32) -> Option<String>;
    fn superclass(&self, class: &str) -> Option<String>;
}

pub(crate) struct DexTypeEnv<'a> {
    dex: &'a DexFile,
    supers: RefCell<DetHashMap<String, Option<String>>>,
}

impl<'a> DexTypeEnv<'a> {
    pub(crate) fn new(dex: &'a DexFile) -> Self {
        Self {
            dex,
            supers: RefCell::new(DetHashMap::default()),
        }
    }
}

impl TypeEnv for DexTypeEnv<'_> {
    fn method(&self, idx: u32) -> Option<MethodSig> {
        let info = self.dex.get_method_info(idx).ok()?;
        Some(MethodSig {
            class: java::descriptor_to_java(&info.class),
            params: info
                .params
                .iter()
                .map(|p| java::descriptor_to_java(p))
                .collect(),
            ret: java::descriptor_to_java(&info.return_type),
        })
    }

    fn field(&self, idx: u32) -> Option<(String, String)> {
        let info = self.dex.get_field_info(idx).ok()?;
        Some((
            java::descriptor_to_java(&info.class),
            java::descriptor_to_java(&info.typ),
        ))
    }

    fn type_name(&self, idx: u32) -> Option<String> {
        let desc = self.dex.get_type(idx).ok()?;
        Some(java::descriptor_to_java(&desc))
    }

    fn superclass(&self, class: &str) -> Option<String> {
        if let Some(known) = self.supers.borrow().get(class) {
            return known.clone();
        }
        let parent = superclass_java(self.dex, class);
        self.supers
            .borrow_mut()
            .insert(class.to_string(), parent.clone());
        parent
    }
}

/// The method whose body is typed.
pub(crate) struct Frame {
    /// `None` for a static method.
    pub(crate) this_class: Option<String>,
    pub(crate) params: Vec<String>,
    pub(crate) ret: String,
    pub(crate) param_base: u32,
    /// Handler offset → type its `move-exception` receives.
    pub(crate) catch_types: DetHashMap<u32, String>,
}

#[derive(Debug, PartialEq)]
pub(crate) struct LocalTypes {
    web_types: DetHashMap<DefKey, LType>,
    /// Loads of the webs typed at their check-cast (`cast_target`).
    cast_loads: BTreeSet<DefKey>,
    /// Webs left in `Conflict`: the next step of the algorithm splits them.
    #[cfg_attr(not(test), allow(dead_code))]
    conflicts: usize,
}

enum DefSrc {
    Fixed(LType),
    Const(i64),
    High16(i64),
    Wide,
    Copy(u32),
    /// Element of the array register, else the type of the opcode suffix.
    Elem(u32, LType),
    /// `and` / `or` / `xor` on ints: `boolean` when every operand is and the literal, if
    /// any, is 0 or 1.
    Bitwise(Vec<u32>, bool),
}

enum UseSrc {
    Need(Need),
    /// `aput` value: element of the array register, else the need of the opcode suffix.
    Elem(u32, Option<Need>),
    Peer(u32),
}

impl LocalTypes {
    pub(crate) fn build(
        instructions: &[Instruction],
        webs: &DefWebs,
        frame: &Frame,
        env: &impl TypeEnv,
    ) -> Self {
        let constraints = Constraints::new(instructions, webs, frame, env);
        let max_iters = (2 * constraints.all.len()).max(1);
        solve(&constraints, env, max_iters)
    }

    /// Resolved Java type of `web`; `None` for a web without verdict or in conflict.
    pub(crate) fn java_type(&self, web: DefKey) -> Option<String> {
        self.web_types.get(&web)?.java()
    }

    pub(crate) fn java_types(&self) -> impl Iterator<Item = (DefKey, String)> + '_ {
        self.web_types
            .iter()
            .filter_map(|(web, ty)| Some((*web, ty.java()?)))
    }

    /// Definition `def` of `reg` is a load whose web takes the type of the check-cast
    /// right after it: the cast belongs in its assignment.
    pub(crate) fn is_cast_load(&self, reg: u32, def: u32) -> bool {
        self.cast_loads.contains(&(reg, def))
    }
}

/// Java literal of the 32-bit constant `value` in a variable of type `ty`, when it is not
/// the number itself.
pub(crate) fn int_literal(value: i64, ty: &str) -> Option<String> {
    match ty {
        "boolean" => match value {
            0 => Some("false".to_string()),
            1 => Some("true".to_string()),
            _ => None,
        },
        "char" => {
            let byte = u8::try_from(value).ok()?;
            if !(0x20..0x7f).contains(&byte) {
                return None;
            }
            let c = char::from(byte);
            Some(if matches!(c, '\'' | '\\') {
                format!("'\\{c}'")
            } else {
                format!("'{c}'")
            })
        }
        _ if value == 0 && prim(ty).is_none() => Some("null".to_string()),
        _ => None,
    }
}

fn prim(name: &str) -> Option<&'static str> {
    ["boolean", "byte", "char", "short", "int", "long", "float", "double"]
        .into_iter()
        .find(|p| *p == name)
}

fn is_int_like(p: &str) -> bool {
    matches!(p, "boolean" | "byte" | "char" | "short" | "int")
}

fn is_wide(ty: &str) -> bool {
    matches!(ty, "long" | "double")
}

fn widens(from: &str, to: &str) -> bool {
    from == to
        || matches!(
            (from, to),
            ("byte", "short" | "int" | "long" | "float" | "double")
                | ("short" | "char", "int" | "long" | "float" | "double")
                | ("int", "long" | "float" | "double")
                | ("long", "float" | "double")
                | ("float", "double")
        )
}

/// Leading register operands, ranges (`v2 ... v5`) expanded.
fn leading_regs(ops: &str) -> Vec<u32> {
    let mut out = Vec::new();
    for part in ops.split(',').map(str::trim) {
        let regs: Vec<u32> = part
            .split_whitespace()
            .filter_map(|t| t.strip_prefix('v')?.parse().ok())
            .collect();
        match regs.as_slice() {
            [a, b] if part.contains("..") => out.extend(*a..=*b),
            [a] => out.push(*a),
            _ => break,
        }
    }
    out
}

fn ref_index(ops: &str) -> Option<u32> {
    let (_, idx) = ops.rsplit_once('@')?;
    idx.split(|c: char| !c.is_ascii_digit()).next()?.parse().ok()
}

fn literal(ops: &str) -> Option<i64> {
    ops.rsplit(',').next()?.trim().parse().ok()
}

/// `aget-char` → `char`; `None` for `aget`, `aget-wide`, `aget-object`.
fn array_suffix(m: &str) -> Option<&'static str> {
    prim(m.rsplit_once('-')?.1)
}

/// (result, operand) types fixed by an arithmetic, conversion or comparison opcode.
fn op_types(m: &str) -> Option<(&'static str, &'static str)> {
    let base = m.split('/').next()?;
    if let Some((from, to)) = base.split_once("-to-") {
        return Some((prim(to)?, prim(from)?));
    }
    if base == "rsub-int" {
        return Some(("int", "int"));
    }
    if let Some(t) = ["cmp-", "cmpl-", "cmpg-"]
        .into_iter()
        .find_map(|p| base.strip_prefix(p))
    {
        return Some(("int", prim(t)?));
    }
    let (op, t) = base.split_once('-')?;
    let t = prim(t)?;
    let arith = [
        "add", "sub", "mul", "div", "rem", "and", "or", "xor", "shl", "shr", "ushr", "neg", "not",
    ];
    arith.contains(&op).then_some((t, t))
}

/// Declared type of the value a `move-result*` after `prev` receives.
fn result_type(prev: Option<&Instruction>, env: &impl TypeEnv) -> LType {
    let Some(prev) = prev else {
        return LType::Bottom;
    };
    let m = prev.mnemonic();
    let idx = ref_index(prev.operands());
    if m.starts_with("filled-new-array") {
        let ty = idx.and_then(|i| env.type_name(i));
        return ty.map_or(LType::Bottom, |t| LType::from_java(&t));
    }
    if !m.starts_with("invoke-")
        || m.starts_with("invoke-custom")
        || m.starts_with("invoke-polymorphic")
    {
        return LType::Bottom;
    }
    let sig = idx.and_then(|i| env.method(i));
    sig.map_or(LType::Bottom, |sig| LType::from_java(&sig.ret))
}

/// Lower bounds defined and upper bounds used by one instruction.
fn scan(
    ins: &Instruction,
    prev: Option<&Instruction>,
    frame: &Frame,
    env: &impl TypeEnv,
    defs: &mut Vec<(DefKey, DefSrc)>,
    uses: &mut Vec<(u32, u32, UseSrc)>,
) {
    let m = ins.mnemonic();
    let ops = ins.operands();
    let off = ins.offset;
    let r = leading_regs(ops);
    let mut def = |src: DefSrc| {
        if let Some(&dst) = r.first() {
            defs.push(((dst, off), src));
        }
    };
    let mut read = |reg: Option<&u32>, src: UseSrc| {
        if let Some(&reg) = reg {
            uses.push((reg, off, src));
        }
    };
    let fixed = |ty: &str| DefSrc::Fixed(LType::from_java(ty));
    let is = |ty: &str| UseSrc::Need(Need::Is(LType::from_java(ty)));
    let referenced = || ref_index(ops).and_then(|i| env.type_name(i));
    match m {
        "const/4" | "const/16" | "const" => {
            if let Some(v) = literal(ops) {
                def(DefSrc::Const(v));
            }
        }
        "const/high16" => {
            if let Some(v) = literal(ops) {
                def(DefSrc::High16(v));
            }
        }
        _ if m.starts_with("const-wide") => def(DefSrc::Wide),
        "const-string" | "const-string/jumbo" => def(fixed("java.lang.String")),
        "const-class" => def(fixed("java.lang.Class")),
        "new-instance" | "check-cast" => def(fixed(&referenced().unwrap_or_default())),
        "new-array" => {
            def(fixed(&referenced().unwrap_or_default()));
            read(r.get(1), is("int"));
        }
        "move-result" | "move-result-wide" | "move-result-object" => {
            def(DefSrc::Fixed(result_type(prev, env)));
        }
        "move-exception" => {
            let caught = frame.catch_types.get(&off);
            def(fixed(caught.map_or(THROWABLE, String::as_str)));
        }
        _ if m.starts_with("move") => {
            if let Some(&src) = r.get(1) {
                def(DefSrc::Copy(src));
            }
        }
        _ if m.starts_with("iget") || m.starts_with("sget") => {
            let (owner, ty) = ref_index(ops)
                .and_then(|i| env.field(i))
                .unwrap_or_default();
            if m.starts_with("iget") && !owner.is_empty() {
                read(r.get(1), is(&owner));
            }
            def(fixed(&ty));
        }
        _ if m.starts_with("iput") || m.starts_with("sput") => {
            if let Some((owner, ty)) = ref_index(ops).and_then(|i| env.field(i)) {
                read(r.first(), is(&ty));
                if m.starts_with("iput") {
                    read(r.get(1), is(&owner));
                }
            }
        }
        _ if m.starts_with("aget") => {
            if let Some(&array) = r.get(1) {
                let suffix = array_suffix(m).map_or(LType::Bottom, LType::Prim);
                def(DefSrc::Elem(array, suffix));
            }
            read(r.get(1), UseSrc::Need(Need::AnyArray));
            read(r.get(2), is("int"));
        }
        _ if m.starts_with("aput") => {
            if let Some(&array) = r.get(1) {
                let suffix = match array_suffix(m) {
                    Some(p) => Some(Need::Is(LType::Prim(p))),
                    None if m == "aput-object" => Some(Need::AnyRef),
                    None => None,
                };
                read(r.first(), UseSrc::Elem(array, suffix));
            }
            read(r.get(1), UseSrc::Need(Need::AnyArray));
            read(r.get(2), is("int"));
        }
        _ if m.starts_with("invoke-") => {
            let dynamic = m.starts_with("invoke-custom") || m.starts_with("invoke-polymorphic");
            let sig = ref_index(ops).and_then(|i| env.method(i));
            if let Some(sig) = sig.filter(|_| !dynamic) {
                let mut args = r.iter();
                if !m.starts_with("invoke-static") {
                    read(args.next(), is(&sig.class));
                }
                for param in &sig.params {
                    read(args.next(), is(param));
                    if is_wide(param) {
                        args.next();
                    }
                }
            }
        }
        "return" | "return-wide" | "return-object" => read(r.first(), is(&frame.ret)),
        "throw" => read(r.first(), is(THROWABLE)),
        "monitor-enter" | "monitor-exit" => read(r.first(), is(OBJECT)),
        "array-length" => {
            def(fixed("int"));
            read(r.get(1), UseSrc::Need(Need::AnyArray));
        }
        "fill-array-data" => read(r.first(), UseSrc::Need(Need::AnyArray)),
        "instance-of" => def(fixed("boolean")),
        "if-eq" | "if-ne" => {
            if let (Some(&a), Some(&b)) = (r.first(), r.get(1)) {
                read(Some(&a), UseSrc::Peer(b));
                read(Some(&b), UseSrc::Peer(a));
            }
        }
        "if-lt" | "if-ge" | "if-gt" | "if-le" => {
            read(r.first(), is("int"));
            read(r.get(1), is("int"));
        }
        "if-ltz" | "if-gez" | "if-gtz" | "if-lez" => read(r.first(), is("int")),
        _ => {
            let Some((result, operand)) = op_types(m) else {
                return;
            };
            let op = m.split('-').next();
            let bitwise = matches!(op, Some("and" | "or" | "xor")) && operand == "int";
            let shift = matches!(op, Some("shl" | "shr" | "ushr"));
            let operands = if m.ends_with("/2addr") {
                &r[..]
            } else {
                r.get(1..).unwrap_or(&[])
            };
            if bitwise {
                let literal_fits = literal(ops).is_none_or(|v| matches!(v, 0 | 1));
                def(DefSrc::Bitwise(operands.to_vec(), literal_fits));
            } else {
                def(DefSrc::Fixed(LType::Prim(result)));
            }
            for (k, reg) in operands.iter().enumerate() {
                let need = if bitwise {
                    Need::IntLike
                } else if shift && k == 1 {
                    Need::Is(LType::Prim("int"))
                } else {
                    Need::Is(LType::Prim(operand))
                };
                read(Some(reg), UseSrc::Need(need));
            }
        }
    }
}

/// Defs and uses of a body, with the webs they touch.
struct Constraints {
    defs: Vec<(DefKey, DefSrc)>,
    uses: Vec<(u32, u32, UseSrc)>,
    members: BTreeMap<DefKey, Vec<usize>>,
    pinned: BTreeSet<DefKey>,
    sources: Vec<BTreeSet<DefKey>>,
    use_webs: Vec<(BTreeSet<DefKey>, BTreeSet<DefKey>)>,
    all: BTreeSet<DefKey>,
    /// Webs where a check-cast joins the value it converts: they hold two types.
    casts: BTreeSet<DefKey>,
    /// Webs of `casts` typed at their check-cast, and their loads.
    cast_typed: BTreeMap<DefKey, LType>,
    cast_loads: BTreeSet<DefKey>,
}

impl Constraints {
    fn new(
        instructions: &[Instruction],
        webs: &DefWebs,
        frame: &Frame,
        env: &impl TypeEnv,
    ) -> Self {
        let mut defs: Vec<(DefKey, DefSrc)> = Vec::new();
        let mut uses: Vec<(u32, u32, UseSrc)> = Vec::new();
        let mut reg = frame.param_base;
        if let Some(this) = &frame.this_class {
            defs.push(((reg, ENTRY_DEF), DefSrc::Fixed(LType::Ref(this.clone()))));
            reg += 1;
        }
        for param in &frame.params {
            defs.push(((reg, ENTRY_DEF), DefSrc::Fixed(LType::from_java(param))));
            reg += if is_wide(param) { 2 } else { 1 };
        }
        for (i, ins) in instructions.iter().enumerate() {
            let prev = i.checked_sub(1).map(|j| &instructions[j]);
            scan(ins, prev, frame, env, &mut defs, &mut uses);
        }
        let web_at = |reg: u32, off: u32| -> BTreeSet<DefKey> {
            let reaching = webs.reaching(off, reg);
            reaching.into_iter().map(|d| webs.web(reg, d)).collect()
        };
        let mut members: BTreeMap<DefKey, Vec<usize>> = BTreeMap::new();
        for (i, ((reg, def), _)) in defs.iter().enumerate() {
            members.entry(webs.web(*reg, *def)).or_default().push(i);
        }
        let pinned: BTreeSet<DefKey> = defs
            .iter()
            .filter(|((_, def), _)| *def == ENTRY_DEF)
            .map(|((reg, def), _)| webs.web(*reg, *def))
            .collect();
        let sources: Vec<BTreeSet<DefKey>> = defs
            .iter()
            .map(|((_, off), src)| match src {
                DefSrc::Copy(reg) | DefSrc::Elem(reg, _) => web_at(*reg, *off),
                DefSrc::Bitwise(regs, _) => regs.iter().flat_map(|r| web_at(*r, *off)).collect(),
                _ => BTreeSet::new(),
            })
            .collect();
        let use_webs: Vec<(BTreeSet<DefKey>, BTreeSet<DefKey>)> = uses
            .iter()
            .map(|(reg, off, src)| {
                let others = match src {
                    UseSrc::Elem(other, _) | UseSrc::Peer(other) => web_at(*other, *off),
                    UseSrc::Need(_) => BTreeSet::new(),
                };
                (web_at(*reg, *off), others)
            })
            .collect();
        let mut all: BTreeSet<DefKey> = members.keys().copied().collect();
        for (targets, _) in &use_webs {
            all.extend(targets.iter().copied());
        }
        let casts: BTreeSet<DefKey> = instructions
            .iter()
            .filter(|ins| ins.mnemonic() == "check-cast")
            .filter_map(|ins| {
                let reg = *leading_regs(ins.operands()).first()?;
                let joined = !webs.reaching(ins.offset, reg).is_empty();
                joined.then(|| webs.web(reg, ins.offset))
            })
            .collect();
        let mut cast_typed = BTreeMap::new();
        let mut cast_loads = BTreeSet::new();
        for &web in &casts {
            if let Some((ty, loads)) = cast_target(web, instructions, webs, env) {
                cast_typed.insert(web, ty);
                cast_loads.extend(loads);
            }
        }
        Self {
            defs,
            uses,
            members,
            pinned,
            sources,
            use_webs,
            all,
            casts,
            cast_typed,
            cast_loads,
        }
    }
}

/// Type `T` of the cast web `web` when every other definition of it is an object load
/// (call result, field, array element) read only by a check-cast to `T`, the next
/// instruction of its block; with those loads. Parameters stay out.
fn cast_target(
    web: DefKey,
    instructions: &[Instruction],
    webs: &DefWebs,
    env: &impl TypeEnv,
) -> Option<(LType, Vec<DefKey>)> {
    let at = |off: u32| instructions.binary_search_by_key(&off, |ins| ins.offset).ok();
    let mut target: Option<String> = None;
    let mut loads = Vec::new();
    for (reg, def) in webs.members(web) {
        if def == ENTRY_DEF {
            return None;
        }
        let i = at(def)?;
        match instructions[i].mnemonic() {
            "check-cast" => {
                let ty = ref_index(instructions[i].operands()).and_then(|t| env.type_name(t))?;
                if *target.get_or_insert_with(|| ty.clone()) != ty {
                    return None;
                }
                continue;
            }
            "move-result-object" => {
                let after_invoke = i
                    .checked_sub(1)
                    .is_some_and(|j| instructions[j].mnemonic().starts_with("invoke-"));
                if !after_invoke {
                    return None;
                }
            }
            "iget-object" | "sget-object" | "aget-object" => {}
            _ => return None,
        }
        let next = webs.next_in_block(def)?;
        let cast = &instructions[at(next)?];
        let casts_reg = cast.mnemonic() == "check-cast"
            && leading_regs(cast.operands()).first() == Some(&reg);
        if !casts_reg || webs.use_sites(reg, def) != [next].as_slice() {
            return None;
        }
        loads.push((reg, def));
    }
    let target = target?;
    (!loads.is_empty()).then(|| (LType::from_java(&target), loads))
}

/// Fixpoint over `constraints`; without convergence in `max_iters` rounds, no web is typed.
fn solve(constraints: &Constraints, env: &impl TypeEnv, max_iters: usize) -> LocalTypes {
    let no_needs = BTreeSet::new();
    let mut lower: BTreeMap<DefKey, LType> = BTreeMap::new();
    let mut resolved: BTreeMap<DefKey, LType> = BTreeMap::new();
    let mut converged = false;
    for _ in 0..max_iters {
        let current = |w: &DefKey| observed(lower.get(w), resolved.get(w));
        let mut needs: BTreeMap<DefKey, BTreeSet<Need>> = BTreeMap::new();
        for ((_, _, src), (targets, others)) in constraints.uses.iter().zip(&constraints.use_webs) {
            let need = match src {
                UseSrc::Need(need) => Some(need.clone()),
                UseSrc::Elem(_, suffix) => {
                    let elem = element(others, &current);
                    elem.map(Need::Is).or_else(|| suffix.clone())
                }
                UseSrc::Peer(_) => peer_need(others, &resolved),
            };
            if let Some(need) = need {
                for web in targets {
                    needs.entry(*web).or_default().insert(need.clone());
                }
            }
        }
        let next_lower: BTreeMap<DefKey, LType> = constraints
            .members
            .iter()
            .map(|(web, idxs)| {
                let web_needs = needs.get(web).unwrap_or(&no_needs);
                let ty = idxs.iter().fold(LType::Bottom, |acc, &i| {
                    let def = def_lower(
                        &constraints.defs[i].1,
                        &constraints.sources[i],
                        web_needs,
                        &current,
                        env,
                    );
                    lub(acc, def, env)
                });
                (*web, ty)
            })
            .collect();
        let next_resolved: BTreeMap<DefKey, LType> = constraints
            .all
            .iter()
            .map(|web| {
                let low = next_lower.get(web).cloned().unwrap_or(LType::Bottom);
                let web_needs = needs.get(web).unwrap_or(&no_needs);
                let pinned = constraints.pinned.contains(web);
                (*web, resolve(&low, web_needs, pinned, env))
            })
            .collect();
        if next_lower == lower && next_resolved == resolved {
            converged = true;
            break;
        }
        lower = next_lower;
        resolved = next_resolved;
    }
    if !converged {
        return LocalTypes {
            web_types: DetHashMap::default(),
            cast_loads: BTreeSet::new(),
            conflicts: 0,
        };
    }
    let conflicts = resolved
        .values()
        .filter(|ty| **ty == LType::Conflict)
        .count();
    LocalTypes {
        web_types: resolved
            .into_iter()
            .filter_map(|(web, ty)| match constraints.cast_typed.get(&web) {
                Some(cast) => Some((web, cast.clone())),
                None => (!constraints.casts.contains(&web)).then_some((web, ty)),
            })
            .collect(),
        cast_loads: constraints.cast_loads.clone(),
        conflicts,
    }
}

/// Type a web shows to the webs copying it: its constant bound while its own uses decide
/// it, else its resolved type.
fn observed(lower: Option<&LType>, resolved: Option<&LType>) -> LType {
    match (lower, resolved) {
        (Some(low @ (LType::Null | LType::IntConst(_))), _) => low.clone(),
        (_, Some(ty)) if ty.is_concrete() => ty.clone(),
        (Some(low), _) => low.clone(),
        _ => LType::Bottom,
    }
}

fn element(arrays: &BTreeSet<DefKey>, current: &impl Fn(&DefKey) -> LType) -> Option<LType> {
    let mut found: Option<LType> = None;
    for web in arrays {
        let LType::Array(elem) = current(web) else {
            return None;
        };
        if !elem.is_concrete() || found.as_ref().is_some_and(|f| *f != *elem) {
            return None;
        }
        found = Some(*elem);
    }
    found
}

fn peer_need(others: &BTreeSet<DefKey>, resolved: &BTreeMap<DefKey, LType>) -> Option<Need> {
    let kinds: BTreeSet<bool> = others
        .iter()
        .filter_map(|web| match resolved.get(web)? {
            LType::Prim(_) => Some(false),
            LType::Ref(_) | LType::Array(_) => Some(true),
            _ => None,
        })
        .collect();
    match (kinds.len(), kinds.first()) {
        (1, Some(true)) => Some(Need::AnyRef),
        (1, Some(false)) => Some(Need::IntLike),
        _ => None,
    }
}

fn def_lower(
    src: &DefSrc,
    sources: &BTreeSet<DefKey>,
    needs: &BTreeSet<Need>,
    current: &impl Fn(&DefKey) -> LType,
    env: &impl TypeEnv,
) -> LType {
    match src {
        DefSrc::Fixed(ty) => ty.clone(),
        DefSrc::Const(0) => LType::Null,
        DefSrc::Const(v) => LType::IntConst(IntRange::of(*v)),
        DefSrc::High16(_) if needs.contains(&Need::Is(LType::Prim("float"))) => {
            LType::Prim("float")
        }
        DefSrc::High16(0) => LType::Null,
        DefSrc::High16(v) => LType::IntConst(IntRange::of(*v)),
        DefSrc::Wide => ["long", "double"]
            .into_iter()
            .find(|&p| needs.contains(&Need::Is(LType::Prim(p))))
            .map_or(LType::Bottom, LType::Prim),
        DefSrc::Copy(_) => sources
            .iter()
            .fold(LType::Bottom, |acc, web| lub(acc, current(web), env)),
        DefSrc::Elem(_, suffix) => element(sources, current).unwrap_or_else(|| suffix.clone()),
        DefSrc::Bitwise(_, literal_fits) => {
            let all_boolean = !sources.is_empty()
                && sources.iter().all(|w| current(w) == LType::Prim("boolean"));
            if *literal_fits && all_boolean {
                LType::Prim("boolean")
            } else {
                LType::Prim("int")
            }
        }
    }
}

fn lub(a: LType, b: LType, env: &impl TypeEnv) -> LType {
    use LType::{Array, Bottom, Conflict, IntConst, Null, Prim, Ref};
    match (a, b) {
        (Bottom, t) | (t, Bottom) => t,
        (Conflict, _) | (_, Conflict) => Conflict,
        (Null, Null) => Null,
        (Null, t @ (IntConst(_) | Ref(_) | Array(_)))
        | (t @ (IntConst(_) | Ref(_) | Array(_)), Null) => t,
        (Null, Prim(p)) | (Prim(p), Null) if !is_wide(p) => Prim(p),
        (IntConst(x), IntConst(y)) => IntConst(x.join(y)),
        (IntConst(r), Prim(p)) | (Prim(p), IntConst(r)) if r.fits(p) => Prim(p),
        (Prim(p), Prim(q)) => prim_lub(p, q),
        (Ref(x), Ref(y)) => Ref(class_lub(x, y, env)),
        (Array(x), Array(y)) if x == y => Array(x),
        (Array(x), Array(y)) if x.is_reference() && y.is_reference() => {
            Array(Box::new(lub(*x, *y, env)))
        }
        (Ref(_) | Array(_), Ref(_) | Array(_)) => Ref(OBJECT.to_string()),
        _ => Conflict,
    }
}

fn prim_lub(p: &'static str, q: &'static str) -> LType {
    if p == q {
        return LType::Prim(p);
    }
    let narrow = |t: &str| is_int_like(t) && t != "boolean";
    if !(narrow(p) && narrow(q)) {
        LType::Conflict
    } else if widens(p, q) {
        LType::Prim(q)
    } else if widens(q, p) {
        LType::Prim(p)
    } else {
        LType::Prim("int")
    }
}

/// Nearest common superclass; `java.lang.Object` when the chains known to the DEX never meet.
fn class_lub(x: String, y: String, env: &impl TypeEnv) -> String {
    if x == y {
        return x;
    }
    let ys = ancestors(y, env);
    ancestors(x, env)
        .into_iter()
        .find(|c| ys.contains(c))
        .unwrap_or_else(|| OBJECT.to_string())
}

fn ancestors(class: String, env: &impl TypeEnv) -> Vec<String> {
    let mut chain = vec![class];
    while let Some(parent) = chain.last().and_then(|c| env.superclass(c)) {
        if chain.contains(&parent) {
            break;
        }
        chain.push(parent);
    }
    chain
}

fn resolve(lower: &LType, needs: &BTreeSet<Need>, pinned: bool, env: &impl TypeEnv) -> LType {
    let primitive = needs.iter().any(Need::is_primitive);
    let reference = needs.iter().any(|n| !n.is_primitive());
    match lower {
        LType::Bottom => match (needs.len(), needs.first()) {
            (1, Some(Need::Is(ty))) => ty.clone(),
            _ => LType::Bottom,
        },
        LType::Prim(p) if needs.iter().all(|n| prim_accepts(p, n)) => lower.clone(),
        LType::Prim(_) | LType::Conflict => LType::Conflict,
        LType::IntConst(_) if reference => LType::Conflict,
        LType::IntConst(range) => pick_int(*range, needs),
        LType::Null if primitive && reference => LType::Conflict,
        LType::Null if reference => null_target(needs, env),
        LType::Null => pick_int(IntRange::Z01, needs),
        LType::Ref(_) | LType::Array(_) if primitive => LType::Conflict,
        LType::Ref(class) if class == OBJECT && !pinned => {
            narrowed(needs).unwrap_or_else(|| lower.clone())
        }
        LType::Ref(_) | LType::Array(_) => lower.clone(),
    }
}

fn prim_accepts(p: &str, need: &Need) -> bool {
    match need {
        Need::IntLike => is_int_like(p),
        Need::Is(LType::Prim(q)) => widens(p, q),
        _ => false,
    }
}

/// The primitive every use asks for when the constant fits it; `int` when they disagree
/// but all take an int-like value.
fn pick_int(range: IntRange, needs: &BTreeSet<Need>) -> LType {
    let wanted: BTreeSet<&'static str> = needs
        .iter()
        .filter_map(|n| match n {
            Need::IntLike => Some("int"),
            Need::Is(LType::Prim(p)) => Some(*p),
            _ => None,
        })
        .collect();
    match (wanted.len(), wanted.first()) {
        (0, _) => LType::Prim("int"),
        (1, Some(&p)) if range.fits(p) => LType::Prim(p),
        _ if wanted.iter().all(|p| is_int_like(p)) => LType::Prim("int"),
        _ => LType::Conflict,
    }
}

fn null_target(needs: &BTreeSet<Need>, env: &impl TypeEnv) -> LType {
    let mut types = needs.iter().filter_map(|n| match n {
        Need::Is(ty) => Some(ty.clone()),
        _ => None,
    });
    match types.next() {
        Some(first) => types.fold(first, |acc, ty| lub(acc, ty, env)),
        None if needs.contains(&Need::AnyRef) => LType::Ref(OBJECT.to_string()),
        None => LType::Bottom,
    }
}

/// A variable typed `Object` that every use reads as the same `T`.
fn narrowed(needs: &BTreeSet<Need>) -> Option<LType> {
    match (needs.len(), needs.first()) {
        (1, Some(Need::Is(ty))) if ty.is_reference() => Some(ty.clone()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decompile::cfg::MethodCfg;

    #[derive(Default)]
    struct Env {
        methods: Vec<MethodSig>,
        fields: Vec<(String, String)>,
        types: Vec<String>,
        supers: Vec<(String, String)>,
    }

    impl TypeEnv for Env {
        fn method(&self, idx: u32) -> Option<MethodSig> {
            self.methods.get(idx as usize).cloned()
        }

        fn field(&self, idx: u32) -> Option<(String, String)> {
            self.fields.get(idx as usize).cloned()
        }

        fn type_name(&self, idx: u32) -> Option<String> {
            self.types.get(idx as usize).cloned()
        }

        fn superclass(&self, class: &str) -> Option<String> {
            self.supers
                .iter()
                .find(|(c, _)| c == class)
                .map(|(_, s)| s.clone())
        }
    }

    fn sig(class: &str, params: &[&str], ret: &str) -> MethodSig {
        MethodSig {
            class: class.to_string(),
            params: params.iter().map(|p| p.to_string()).collect(),
            ret: ret.to_string(),
        }
    }

    fn frame(this_class: Option<&str>, params: &[&str], param_base: u32) -> Frame {
        Frame {
            this_class: this_class.map(str::to_string),
            params: params.iter().map(|p| p.to_string()).collect(),
            ret: "void".to_string(),
            param_base,
            catch_types: DetHashMap::default(),
        }
    }

    fn no_condition(_: &Instruction) -> String {
        "true".into()
    }

    fn solve_body(
        bytecode: &[u8],
        entry_regs: &[u32],
        frame: &Frame,
        env: &Env,
    ) -> (DefWebs, LocalTypes) {
        let instructions = dex_bytecode::decode_all(bytecode, 0).expect("decode");
        let cfg = MethodCfg::build(&instructions, bytecode, 0, &no_condition);
        let webs = DefWebs::build(&cfg, &instructions, &[], entry_regs);
        let types = LocalTypes::build(&instructions, &webs, frame, env);
        (webs, types)
    }

    fn type_of(solved: &(DefWebs, LocalTypes), reg: u32, def: u32) -> Option<String> {
        solved.1.java_type(solved.0.web(reg, def))
    }

    /// `0` tested by `if-eqz` and then used as a receiver is a null reference.
    #[test]
    fn zero_tested_then_dereferenced_is_a_null_string() {
        let env = Env {
            methods: vec![sig("java.lang.String", &[], "int")],
            ..Env::default()
        };
        let solved = solve_body(
            &[
                0x12, 0x00, // 0: const/4 v0, 0
                0x38, 0x00, 0x03, 0x00, // 2: if-eqz v0, +3 -> 8
                0x0e, 0x00, // 6: return-void
                0x6e, 0x10, 0x00, 0x00, 0x00, 0x00, // 8: invoke-virtual {v0}, String.length()I
                0x0e, 0x00, // 14: return-void
            ],
            &[],
            &frame(None, &[], 1),
            &env,
        );
        let ty = type_of(&solved, 0, 0).expect("typed");
        assert_eq!(ty, "java.lang.String");
        assert_eq!(
            crate::decompile::typed_zero_test("v0", true, &ty).as_deref(),
            Some("v0 == null")
        );
        assert_eq!(int_literal(0, &ty).as_deref(), Some("null"));
    }

    #[test]
    fn one_passed_as_boolean_is_true() {
        let env = Env {
            methods: vec![sig("T", &["boolean"], "void")],
            ..Env::default()
        };
        let solved = solve_body(
            &[
                0x12, 0x10, // 0: const/4 v0, 1
                0x71, 0x10, 0x00, 0x00, 0x00, 0x00, // 2: invoke-static {v0}, f(Z)V
                0x0e, 0x00, // 8: return-void
            ],
            &[],
            &frame(None, &[], 1),
            &env,
        );
        let ty = type_of(&solved, 0, 0).expect("typed");
        assert_eq!(ty, "boolean");
        assert_eq!(int_literal(1, &ty).as_deref(), Some("true"));
    }

    #[test]
    fn zero_stored_in_object_field_is_null_object() {
        let env = Env {
            fields: vec![("T".to_string(), OBJECT.to_string())],
            ..Env::default()
        };
        let solved = solve_body(
            &[
                0x12, 0x00, // 0: const/4 v0, 0
                0x5b, 0x10, 0x00, 0x00, // 2: iput-object v0, v1, T.f:Object
                0x0e, 0x00, // 6: return-void
            ],
            &[1],
            &frame(Some("T"), &[], 1),
            &env,
        );
        assert_eq!(type_of(&solved, 0, 0).as_deref(), Some(OBJECT));
        assert_eq!(type_of(&solved, 1, ENTRY_DEF).as_deref(), Some("T"));
    }

    #[test]
    fn small_constant_passed_as_char_is_a_char() {
        let env = Env {
            methods: vec![sig("T", &["char"], "void")],
            ..Env::default()
        };
        let solved = solve_body(
            &[
                0x13, 0x00, 0x41, 0x00, // 0: const/16 v0, 65
                0x71, 0x10, 0x00, 0x00, 0x00, 0x00, // 4: invoke-static {v0}, g(C)V
                0x0e, 0x00, // 10: return-void
            ],
            &[],
            &frame(None, &[], 1),
            &env,
        );
        let ty = type_of(&solved, 0, 0).expect("typed");
        assert_eq!(ty, "char");
        assert_eq!(int_literal(65, &ty).as_deref(), Some("'A'"));
    }

    fn two_subclasses_joined() -> (Env, Vec<u8>) {
        let env = Env {
            methods: vec![sig("X", &[OBJECT], "void")],
            types: vec!["p.A".to_string(), "p.B".to_string()],
            supers: vec![
                ("p.A".to_string(), "p.Base".to_string()),
                ("p.B".to_string(), "p.Base".to_string()),
            ],
            ..Env::default()
        };
        let bytecode = vec![
            0x38, 0x03, 0x06, 0x00, // 0: if-eqz v3, +6 -> 12
            0x22, 0x00, 0x00, 0x00, // 4: new-instance v0, p.A
            0x07, 0x02, // 8: move-object v2, v0
            0x28, 0x04, // 10: goto +4 -> 18
            0x22, 0x01, 0x01, 0x00, // 12: new-instance v1, p.B
            0x07, 0x12, // 16: move-object v2, v1
            0x71, 0x10, 0x00, 0x00, 0x02, 0x00, // 18: invoke-static {v2}, X.k(Object)V
            0x0e, 0x00, // 24: return-void
        ];
        (env, bytecode)
    }

    /// Two copies of sibling classes into one variable: their nearest common superclass.
    #[test]
    fn copies_of_two_subclasses_meet_at_their_superclass() {
        let (env, bytecode) = two_subclasses_joined();
        let solved = solve_body(&bytecode, &[3], &frame(None, &["int"], 3), &env);
        assert_eq!(solved.0.web(2, 8), solved.0.web(2, 16));
        assert_eq!(type_of(&solved, 2, 8).as_deref(), Some("p.Base"));
        assert_eq!(type_of(&solved, 0, 4).as_deref(), Some("p.A"));
        assert_eq!(type_of(&solved, 1, 12).as_deref(), Some("p.B"));
    }

    /// The move chain needs a second round to reach `p.Base`: one round leaves no verdict.
    #[test]
    fn unconverged_solve_types_no_web() {
        let (env, bytecode) = two_subclasses_joined();
        let method = frame(None, &["int"], 3);
        let instructions = dex_bytecode::decode_all(&bytecode, 0).expect("decode");
        let cfg = MethodCfg::build(&instructions, &bytecode, 0, &no_condition);
        let webs = DefWebs::build(&cfg, &instructions, &[], &[3]);
        let constraints = Constraints::new(&instructions, &webs, &method, &env);
        assert!(!constraints.all.is_empty());

        let starved = solve(&constraints, &env, 1);
        for web in &constraints.all {
            assert_eq!(starved.java_type(*web), None);
        }
        assert_eq!(starved.conflicts, 0);

        let full = solve(&constraints, &env, (2 * constraints.all.len()).max(1));
        assert_eq!(full.java_type(webs.web(2, 8)).as_deref(), Some("p.Base"));
        assert_eq!(full.java_type(webs.web(0, 4)).as_deref(), Some("p.A"));
        assert_eq!(full.java_type(webs.web(1, 12)).as_deref(), Some("p.B"));
        let built = LocalTypes::build(&instructions, &webs, &method, &env);
        assert_eq!(full, built);
    }

    #[test]
    fn aput_into_int_array_types_value_and_index_int() {
        let env = Env {
            types: vec!["int[]".to_string()],
            ..Env::default()
        };
        let solved = solve_body(
            &[
                0x12, 0x33, // 0: const/4 v3, 3
                0x23, 0x31, 0x00, 0x00, // 2: new-array v1, v3, int[]
                0x12, 0x50, // 6: const/4 v0, 5
                0x12, 0x02, // 8: const/4 v2, 0
                0x4b, 0x00, 0x01, 0x02, // 10: aput v0, v1, v2
                0x0e, 0x00, // 14: return-void
            ],
            &[],
            &frame(None, &[], 4),
            &env,
        );
        assert_eq!(type_of(&solved, 1, 2).as_deref(), Some("int[]"));
        assert_eq!(type_of(&solved, 0, 6).as_deref(), Some("int"));
        assert_eq!(type_of(&solved, 2, 8).as_deref(), Some("int"));
        assert_eq!(type_of(&solved, 3, 0).as_deref(), Some("int"));
    }

    const ONE_PASSED_TWICE: [u8; 16] = [
        0x12, 0x10, // 0: const/4 v0, 1
        0x71, 0x10, 0x00, 0x00, 0x00, 0x00, // 2: invoke-static {v0}, method@0
        0x71, 0x10, 0x01, 0x00, 0x00, 0x00, // 8: invoke-static {v0}, method@1
        0x0e, 0x00, // 14: return-void
    ];

    #[test]
    fn constant_for_boolean_and_int_parameters_is_int() {
        let env = Env {
            methods: vec![sig("T", &["boolean"], "void"), sig("T", &["int"], "void")],
            ..Env::default()
        };
        let solved = solve_body(&ONE_PASSED_TWICE, &[], &frame(None, &[], 1), &env);
        assert_eq!(type_of(&solved, 0, 0).as_deref(), Some("int"));
        assert_eq!(solved.1.conflicts, 0);
    }

    #[test]
    fn constant_for_boolean_and_object_parameters_conflicts() {
        let env = Env {
            methods: vec![sig("T", &["boolean"], "void"), sig("T", &[OBJECT], "void")],
            ..Env::default()
        };
        let solved = solve_body(&ONE_PASSED_TWICE, &[], &frame(None, &[], 1), &env);
        assert_eq!(type_of(&solved, 0, 0), None);
        assert_eq!(
            solved.1.web_types.get(&solved.0.web(0, 0)),
            Some(&LType::Conflict)
        );
        assert_eq!(solved.1.conflicts, 1);
    }

    #[test]
    fn same_body_resolves_to_the_same_types() {
        let (env, bytecode) = two_subclasses_joined();
        let a = solve_body(&bytecode, &[3], &frame(None, &["int"], 3), &env).1;
        let b = solve_body(&bytecode, &[3], &frame(None, &["int"], 3), &env).1;
        assert_eq!(a.web_types, b.web_types);
        assert_eq!(a, b);
    }
}

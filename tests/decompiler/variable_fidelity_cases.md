# Variable fidelity: cases the minimal DEX cannot build

`helpers::minimal_dex_with_method_code` builds one method `Simple.foo()V` with
`registers_size = 2`, `ins_size = 0`, five strings, two types and a single method id.
It has no parameters, no `<init>` method id and no method with a return value, so
the cases below are written as expected output, to turn into tests once a fixture
(APK/DEX in `tests/data/` or a helper with parameters and extra method ids) exists.
Their mechanisms are covered by unit tests in `src/decompile/`:
`def_webs.rs`, `pass.rs`, `mod.rs` (`fold_*`), `simplify/tests/mod.rs` (`variable_reuse`).

## D2: declared type comes from the definition

```smali
.method protected onCreate(Landroid/os/Bundle;)V
    .registers 4
    const-string v0, "power"
    invoke-virtual {p0, v0}, Lcom/x/MainActivity;->getSystemService(Ljava/lang/String;)Ljava/lang/Object;
    move-result-object v0
    check-cast v0, Landroid/os/PowerManager;
    const/4 v1, 0x1
    invoke-virtual {v0, v1, ...}, Landroid/os/PowerManager;->newWakeLock(...)
```

Expected: the call result is declared `Object` (callee signature), the cast result
`PowerManager`; never `int`/`long`/`String` taken from another definition of `v0`/`v1`.

```java
Object obj0 = this.getSystemService("power");      // or inlined into the cast
PowerManager pm = (PowerManager) obj0;             // name may differ, type may not
```

Must not appear: `int s4 = this.getSystemService(`, `long l2 = this.getSystemService(`,
`String i2 = this.getSharedPreferences(`.

## D5: parameter registers

```smali
.method public onRequestPermissionsResult(I[Ljava/lang/String;[I)V
    .registers 6          # p0=v2 (this), p1=v3, p2=v4, p3=v5
    const-string v0, "permissions"
    invoke-static {p2, v0}, Lf2/e;->e(Ljava/lang/Object;Ljava/lang/String;)V
    const-string v0, "grantResults"
    invoke-static {p3, v0}, Lf2/e;->e(Ljava/lang/Object;Ljava/lang/String;)V
    invoke-super {p0, p1, p2, p3}, Landroid/app/Activity;->onRequestPermissionsResult(I[Ljava/lang/String;[I)V
    const/4 p2, 0x0       # reuse of a parameter register
    ...
```

Expected:

```java
public void onRequestPermissionsResult(int i0, String[] arr1, int[] arr2) {
    f2.e.e(arr1, "permissions");
    f2.e.e(arr2, "grantResults");
    super.onRequestPermissionsResult(i0, arr1, arr2);
    int i4 = 0;                                     // not `arr1 = 0`, name may differ
```

Must not appear: `f2.e.e(1, "permissions")`, `onRequestPermissionsResult(i0, 1, 2)`.

Static method with an object parameter reused for a constant (000128, 000137):

```smali
.method static a(L0/x;)V
    .registers 3          # p0=v2
    iget-object v0, p0, L0/x;->x:L0/y;
    invoke-virtual {v0, ...}, L0/y;->j(...)
    const/4 p0, 0x0
```

Expected: `p0.x.j(...)` stays; no identifier starting with a digit (`0.x.j(`).

Wide parameter before an object parameter (`(JLjava/lang/String;)V`, debug names
`time`, `tag`): `tag` names `v(base+3)` in an instance method, not `v(base+2)`.

## D7: `new-instance` merged with its `<init>`

```smali
    new-instance v2, LD0/K;
    new-instance v3, Ljava/lang/StringBuilder;
    invoke-direct {v3}, Ljava/lang/StringBuilder;-><init>()V
    invoke-virtual {v3, v4}, Ljava/lang/StringBuilder;->append(Ljava/lang/String;)Ljava/lang/StringBuilder;
    invoke-virtual {v3}, Ljava/lang/StringBuilder;->toString()Ljava/lang/String;
    move-result-object v3
    invoke-direct {v2, v3}, LD0/K;-><init>(Ljava/lang/String;)V
```

Expected: one statement `D0.K … = new D0.K(…);` after the argument is computed;
no `.<init>(` anywhere in the method.

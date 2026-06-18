# Inventory: ./HasseWeil/EC/MulByIntAddRecurrence.lean

**File purpose**: Proves the addition recurrence `[m] ⊞ [1] = [m+1]` on the generic point of the
function field (Silverman III.5.3), and the injectivity of `[·] : ℤ → End E` on nonzero integers.
The module exists in isolation to avoid an `AddCommGroup` instance diamond on
`(W_KE W).toAffine.Point` that arises when the heavier `SilvermanIV14`/`OpenLemmaPrimitives`
modules are in scope.

**Imports**: `HasseWeil.AdditionPullback`, `HasseWeil.OmegaPullbackCoeff`,
`HasseWeil.EC.GenericPointZsmul`

**Total declarations**: 2 (both `theorem`, both `public`)

---

### `theorem addPullback_xy_mulByInt_eq_succ`

- **Type**:
  ```
  addPullback_xy_mulByInt_eq_succ (m : ℤ) (hm : m ≠ 0) (hm1 : m + 1 ≠ 0)
      (hx_ne : x_gen W ≠ mulByInt_x W m) :
      addPullback_x W (mulByInt W.toAffine m) = mulByInt_x W (m + 1) ∧
        addPullback_y W (mulByInt W.toAffine m) = mulByInt_y W (m + 1)
  ```
- **What**: States that the chord-addition pullback of the generic point against `[m]` equals the
  `[m+1]` x/y-coordinates in the function field, i.e., `P ⊞ [m]P = [m+1]P` read off at the level
  of `K(E)`-elements. This is the addition recurrence from Silverman III.5.3.
- **How**: First rewrites `[m]`-pullbacks of `x_gen`/`y_gen` via `mulByInt_pullback_x/y`
  (from `OmegaPullbackCoeff`), then unfolds `addPullback_x/y`/`addSlope`, eliminates the `slope`
  function via `WeierstrassCurve.Affine.slope_of_X_ne` (using the non-collision hypothesis
  `hx_ne`), and finally delegates the resulting field identity to
  `addX_addY_genericPoint_mulByInt_eq_succ` (from `GenericPointZsmul`). The `slope_of_X_ne` step
  is critical: it removes a `DecidableEq K(E)` choice point that would otherwise trigger an
  explosive `whnf` defeq over the `FunctionField` tower.
- **Hypotheses**: Elliptic curve `W` over a field `F` with `DecidableEq`; `m ≠ 0`; `m + 1 ≠ 0`;
  `x_gen W ≠ mulByInt_x W m` (the generic x-coordinate is not the `[m]`-x-coordinate, i.e., `P`
  and `[m]P` are not in a vertical tangent / doubling configuration).
- **Uses from project**:
  - `mulByInt_pullback_x` (from `OmegaPullbackCoeff`)
  - `mulByInt_pullback_y` (from `OmegaPullbackCoeff`)
  - `addPullback_x` (from `AdditionPullback`)
  - `addPullback_y` (from `AdditionPullback`)
  - `addSlope` (from `AdditionPullback`)
  - `x_gen` (from `MulByIntPullback` via `GenericPointZsmul`)
  - `mulByInt_x` (from `MulByIntPullback`)
  - `mulByInt_y` (from `MulByIntPullback`)
  - `addX_addY_genericPoint_mulByInt_eq_succ` (from `GenericPointZsmul`)
- **Used by**: unused in file; used by `RouteBInduction` (L150) and `TorsionGeometric` (L377)
- **Visibility**: public
- **Lines**: 31–53; proof length ~19 lines (body only)
- **Notes**: `set_option maxHeartbeats 1000000` (line 28, before this declaration; NO inline reason
  comment but the docstring explains: instance diamond / `whnf` explosion on `FunctionField`).
  Proof is under 30 lines.

---

### `theorem mulByInt_left_injective`

- **Type**:
  ```
  mulByInt_left_injective (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0)
      (hab : mulByInt W.toAffine a = mulByInt W.toAffine b) : a = b
  ```
- **What**: The multiplication-by-integer map `[·] : ℤ → End E` is injective on nonzero integers:
  if `[a] = [b]` as isogenies (with both nonzero), then `a = b`. This is Wall C / Silverman III.4.2b.
- **How**: Uses `congrArg Isogeny.pullback` to pass the isogeny equality to pullbacks, then applies
  `mulByInt_pullback_x/y` to reduce to an equality of x/y-coordinates in `K(E)`, and concludes
  by `mulByInt_xy_inj` (from `GenericPointZsmul`) which exploits the infinite order of the generic
  point.
- **Hypotheses**: Elliptic curve `W` over a field `F` with `DecidableEq`; `a ≠ 0`, `b ≠ 0`;
  `mulByInt W.toAffine a = mulByInt W.toAffine b` as isogenies.
- **Uses from project**:
  - `mulByInt_pullback_x` (from `OmegaPullbackCoeff`)
  - `mulByInt_pullback_y` (from `OmegaPullbackCoeff`)
  - `mulByInt_x` (from `MulByIntPullback`)
  - `mulByInt_y` (from `MulByIntPullback`)
  - `mulByInt_xy_inj` (from `GenericPointZsmul`)
- **Used by**: unused in file; used by `DegreeQuadraticForm` (L215)
- **Visibility**: public
- **Lines**: 60–68; proof length ~9 lines
- **Notes**: No `maxHeartbeats` override. Proof is under 30 lines.

---

## Summary

| Metric | Value |
|--------|-------|
| Total declarations | 2 |
| Theorems/lemmas | 2 |
| Defs | 0 |
| Instances | 0 |
| Sorries | none |
| `set_option maxHeartbeats` | 1 (value 1000000, before `addPullback_xy_mulByInt_eq_succ`) |
| Long proofs (>30 lines) | none |
| Unused in file | both (leaf theorems consumed by other files) |
| Key API (used by 3+ in file) | none (only 2 declarations total) |

**Notable**: The file is deliberately isolated to avoid an `AddCommGroup` instance diamond on
`(W_KE W).toAffine.Point` that arises with heavier imports; the `maxHeartbeats 1000000` override
on `addPullback_xy_mulByInt_eq_succ` is explained by `DecidableEq` / `whnf` explosion risk.
Both declarations are clean (no sorry) and serve as leaf API consumed by `RouteBInduction`,
`TorsionGeometric`, and `DegreeQuadraticForm`.

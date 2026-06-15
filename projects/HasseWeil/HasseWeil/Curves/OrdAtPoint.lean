import HasseWeil.Curves.Infinity
import HasseWeil.Curves.Valuation
import HasseWeil.Curves.Divisors

/-!
# The order at an arbitrary closed point of a smooth plane curve

For a smooth plane curve `C` over a field `F` (in our setting, a Weierstrass
curve wrapper), the function field `F(C)` carries a valuation
`ord_T : F(C) → ℤ ∪ {∞}` at every closed point `T` of `C`. The point set
`C.toAffine.Point` distinguishes between the unique point at infinity
`.zero` (= `O`) and affine smooth points `.some x y h_ns`. The project
already ships two specialised orders:

* `ordAtInfty : C.FunctionField → WithTop ℤ`
  (`Curves/Infinity.lean:81`) — order at `O = [0 : 1 : 0]`.
* `ord_P (P : C.SmoothPoint) : C.FunctionField → WithTop ℤ`
  (`Curves/Valuation.lean:71`) — order at a finite smooth point.

This file packages them into a single uniform API

```
ordAtPoint : (T : C.toAffine.Point) → C.FunctionField → WithTop ℤ
```

via a pattern match on `T`. The companion lemmas (`ordAtPoint_mul`,
`ordAtPoint_add_le`, `ordAtPoint_zero_function`, `ordAtPoint_eq_top_iff`)
delegate to the respective specialised lemmas after case-splitting.

The uniform API is consumed by `Curves/RamificationAtInfinity` /
`Hasse/OpenLemmas` (Bridge B(i): order-based kernel-to-prime
correspondence) and by future projective valuation tickets.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.1 (definitions of
  `ord_P`); IV.1 (place at infinity).
-/

namespace HasseWeil.Curves

namespace SmoothPlaneCurve

variable {F : Type*} [Field F] (C : SmoothPlaneCurve F)

/-- The order of a function `f ∈ F(C)` at a closed point `T : C.toAffine.Point`,
uniform across the point at infinity (`.zero`) and finite smooth points
(`.some x y h_ns`).

* For `T = .zero` (= `O`), this is `ordAtInfty f` (the place-at-infinity
  valuation).
* For `T = .some x y h_ns` (a finite smooth point), this is
  `ord_P ⟨x, y, h_ns⟩ f` (the local-DVR valuation at the affine point).

The two cases share a common codomain `WithTop ℤ` and a common
`ord(0) = ⊤` convention, so the uniform API delegates pointwise. -/
noncomputable def ordAtPoint (T : C.toAffine.Point) (f : C.FunctionField) :
    WithTop ℤ :=
  match T with
  | .zero => C.ordAtInfty f
  | .some x y h_ns => C.ord_P ⟨x, y, h_ns⟩ f

/-! ### Reduction lemmas to the specialised order functions -/

/-- `ordAtPoint` at the point at infinity reduces to `ordAtInfty`. -/
@[simp] theorem ordAtPoint_zero_eq_ordAtInfty (f : C.FunctionField) :
    C.ordAtPoint .zero f = C.ordAtInfty f := rfl

/-- `ordAtPoint` at a finite smooth point reduces to `ord_P`. -/
@[simp] theorem ordAtPoint_some_eq_ord_P (x y : F)
    (h_ns : C.toAffine.Nonsingular x y) (f : C.FunctionField) :
    C.ordAtPoint (.some x y h_ns) f = C.ord_P ⟨x, y, h_ns⟩ f := rfl

/-! ### Compatibility lemmas (valuation API on the uniform form) -/

/-- The order of the zero function is `⊤` (= "infinity"), uniformly at
every closed point. -/
@[simp] theorem ordAtPoint_zero_function (T : C.toAffine.Point) :
    C.ordAtPoint T 0 = ⊤ := by
  cases T with
  | zero => exact C.ordAtInfty_zero
  | some x y h_ns => exact C.ord_P_zero (P := ⟨x, y, h_ns⟩)

/-- The order of the constant function `1` is `0`, uniformly at every
closed point. -/
@[simp] theorem ordAtPoint_one (T : C.toAffine.Point) :
    C.ordAtPoint T 1 = 0 := by
  cases T with
  | zero => exact C.ordAtInfty_one
  | some x y h_ns => exact C.ord_P_one (P := ⟨x, y, h_ns⟩)

/-- `ordAtPoint T f = ⊤` iff `f = 0`, uniformly at every closed point.

This is the place-by-place version of "valuations send only zero to
infinity". -/
theorem ordAtPoint_eq_top_iff (T : C.toAffine.Point) (f : C.FunctionField) :
    C.ordAtPoint T f = ⊤ ↔ f = 0 := by
  cases T with
  | zero => exact C.ordAtInfty_eq_top_iff f
  | some x y h_ns => exact ord_P_eq_top_iff (P := ⟨x, y, h_ns⟩) f

/-- Multiplicativity of `ordAtPoint`, uniformly at every closed point. The
`T = .zero` branch delegates to `ordAtInfty_mul` (which requires both
factors to be nonzero) after a manual case-split on `f = 0` / `g = 0` to
cover the absorbing-`⊤` arithmetic; the `T = .some` branch delegates to
the unconditional `ord_P_mul`. -/
theorem ordAtPoint_mul (T : C.toAffine.Point) (f g : C.FunctionField) :
    C.ordAtPoint T (f * g) = C.ordAtPoint T f + C.ordAtPoint T g := by
  cases T with
  | zero =>
    -- `ordAtInfty_mul` is conditional on nonzero — handle the zero cases
    -- via `0 * g = 0` and `⊤ + _ = ⊤`.
    rcases eq_or_ne f 0 with rfl | hf
    · simp
    rcases eq_or_ne g 0 with rfl | hg
    · simp
    simpa using C.ordAtInfty_mul hf hg
  | some x y h_ns => simpa using C.ord_P_mul (P := ⟨x, y, h_ns⟩) f g

/-- Non-archimedean triangle inequality for `ordAtPoint`, uniformly at
every closed point. Both branches deliver the unconditional
`min ord f, ord g ≤ ord (f + g)` form. -/
theorem ordAtPoint_add_le (T : C.toAffine.Point) (f g : C.FunctionField) :
    min (C.ordAtPoint T f) (C.ordAtPoint T g) ≤ C.ordAtPoint T (f + g) := by
  cases T with
  | zero => simpa using C.ordAtInfty_add_ge_min f g
  | some x y h_ns => simpa using C.ord_P_add_le (P := ⟨x, y, h_ns⟩) f g

/-- Inverse: `ord_T(f⁻¹) = -ord_T(f)`, uniformly at every closed point.
Delegates to `ordAtInfty_inv` at `.zero` and to `ord_P_inv` at a finite
smooth point (after handling the `f = 0` case where both sides are `⊤`). -/
theorem ordAtPoint_inv (T : C.toAffine.Point) (f : C.FunctionField) :
    C.ordAtPoint T f⁻¹ = -(C.ordAtPoint T f) := by
  cases T with
  | zero => exact C.ordAtInfty_inv f
  | some x y h_ns =>
    rcases eq_or_ne f 0 with rfl | hf
    · simp [inv_zero]
    exact C.ord_P_inv (P := ⟨x, y, h_ns⟩) f hf

/-- A nonzero `F`-constant has order `0` at every closed point: it is a unit
of the local ring (resp. has degree-`0` divisor at infinity). Uniform across
`.zero` and finite smooth points; delegates to
`ordAtInfty_algebraMap_F_nonzero` and `ord_P_algebraMap_F_of_ne_zero`. -/
theorem ordAtPoint_algebraMap_F_of_ne_zero (T : C.toAffine.Point) {c : F}
    (hc : c ≠ 0) :
    C.ordAtPoint T (algebraMap F C.FunctionField c) = 0 := by
  cases T with
  | zero => exact C.ordAtInfty_algebraMap_F_nonzero hc
  | some x y h_ns => exact ord_P_algebraMap_F_of_ne_zero C hc ⟨x, y, h_ns⟩

/-- **Strict non-archimedean for `ordAtPoint`**: when `ord_T f < ord_T g`,
the dominant (smaller-order) term wins: `ord_T (f + g) = ord_T f`. Uniform
across `.zero` and finite smooth points; delegates to
`ordAtInfty_add_eq_of_lt` and `ord_P_add_eq_of_lt`. -/
theorem ordAtPoint_add_eq_of_lt (T : C.toAffine.Point) {f g : C.FunctionField}
    (h : C.ordAtPoint T f < C.ordAtPoint T g) :
    C.ordAtPoint T (f + g) = C.ordAtPoint T f := by
  cases T with
  | zero => exact C.ordAtInfty_add_eq_of_lt h
  | some x y h_ns => exact C.ord_P_add_eq_of_lt (P := ⟨x, y, h_ns⟩) h

end SmoothPlaneCurve

end HasseWeil.Curves

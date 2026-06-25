/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.AffinePointMap
import HasseWeil.EC.GenericPoint
import HasseWeil.EC.MulByIntBaseCase
import HasseWeil.EC.MulByIntComp

/-!
# `n • genericPoint W = .some (mulByInt_x W n) (mulByInt_y W n)` (T-III-4-020b-2)

Silverman III.4.2: for an elliptic curve `E` and an integer `n ≠ 0`, the point
`n • P` has x-coordinate `Φ_n(P.x) / ΨSq_n(P.x)` and y-coordinate
`ω_n(P.x, P.y) / ψ_n(P.x, P.y)³`.

Specialized to the generic point `P = genericPoint W` in `E(K(E))` (where
`E = W.toAffine` and `K(E) = W.toAffine.FunctionField`), this gives:
```
n • genericPoint W = Affine.Point.some (mulByInt_x W n) (mulByInt_y W n) _
```
for `n ≠ 0` in `ℤ`.

This is the connection lemma between the division-polynomial definition of
`mulByInt_x/y` and the group-law x/y-coordinate.

## Strategy

Strong induction on `n.natAbs`, mirroring mathlib's universal
`Affine.zsmul_point_eq_smulX_smulY` (in `Auxiliary/DivisionPolynomial.lean:423`)
but directly in our `W_KE` setting. Key steps:

1. **`n = 1` case**: `1 • genericPoint = genericPoint = .some (x_gen) (y_gen)`.
   By `mulByInt_x_one` and `mulByInt_y_one`, these equal
   `mulByInt_x W 1` and `mulByInt_y W 1`.

2. **`n = 2` case** (doubling): uses the tangent slope at `genericPoint`.

3. **`n ≥ 3` case**: induction using addition formula
   `(n+1) • P = n • P + P` where the addition is `add_of_X_ne`
   (using `mulByInt_x W n ≠ mulByInt_x W 1`).

4. **`n < 0` case**: via `mulByInt_x_neg` and negation preservation.

## Auxiliary algebraic lemmas

These are the `W_KE`-specific analogs of the universal lemmas:
- `mulByInt_x_ne_zero_at`
- `mulByInt_x_sub_mulByInt_x`
- `mulByInt_x_ne_mulByInt_x`
- `mulByInt_y_sub_negY` at the generic point
- `slope_at_genericPoint` (for doubling)
- `addX_mulByInt_x_one_one` (doubling closure)
- `addY_mulByInt_y_one_one`

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.4.2.
* mathlib: `HasseWeil/Auxiliary/DivisionPolynomial.lean:423` (universal analog).
-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-- `mulByInt_x W 1 = x_gen W`. Unfolded form of `mulByInt_x_one` with the
    `x_gen` abbreviation used directly. -/
theorem genericPoint_eq_mulByInt_one :
    genericPoint W = Affine.Point.some (mulByInt_x W 1) (mulByInt_y W 1)
      (by rw [mulByInt_x_one, mulByInt_y_one]; exact generic_nonsingular W) := by
  unfold genericPoint
  congr 1
  · exact (mulByInt_x_one W).symm
  · exact (mulByInt_y_one W).symm

/-- `1 • genericPoint W = genericPoint W` (trivial, for reference). -/
theorem one_zsmul_genericPoint :
    (1 : ℤ) • genericPoint W = genericPoint W :=
  one_zsmul _

/-- Base case for the main induction: `1 • genericPoint W` matches the
    `[1]`-coordinates. -/
theorem zsmul_genericPoint_one :
    (1 : ℤ) • genericPoint W = Affine.Point.some (mulByInt_x W 1) (mulByInt_y W 1)
      (by rw [mulByInt_x_one, mulByInt_y_one]; exact generic_nonsingular W) := by
  rw [one_zsmul_genericPoint, genericPoint_eq_mulByInt_one]

local notation "R" => W.toAffine.CoordinateRing
local notation "KE" => W.toAffine.FunctionField

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `ψ_ff W (-n) = -ψ_ff W n` in `K(E)`: negation passes through `mk` and `algebraMap`. -/
@[simp] theorem ψ_ff_neg (n : ℤ) : ψ_ff W (-n) = -ψ_ff W n := by
  unfold ψ_ff
  rw [W.ψ_neg n, map_neg, map_neg]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
private lemma W_KE_a₁ : (W_KE W).a₁ = algebraMap F KE W.a₁ := rfl

omit [DecidableEq F] [W.toAffine.IsElliptic] in
private lemma W_KE_a₃ : (W_KE W).a₃ = algebraMap F KE W.a₃ := rfl

omit [DecidableEq F] [W.toAffine.IsElliptic] in
private lemma algebraMap_mk_CC (r : F) :
    algebraMap R KE (Affine.CoordinateRing.mk W.toAffine
      (Polynomial.C (Polynomial.C r))) =
      algebraMap F KE r := by
  have h : Affine.CoordinateRing.mk W.toAffine (Polynomial.C (Polynomial.C r))
      = algebraMap F R r := rfl
  rw [h, ← IsScalarTower.algebraMap_apply F R KE r]

private lemma ω_ff_neg (n : ℤ) :
    ω_ff W (-n) = ω_ff W n
      + algebraMap F KE W.a₁ * Φ_ff W n * ψ_ff W n
      + algebraMap F KE W.a₃ * ψ_ff W n ^ 3 := by
  have h_poly : W.ω (-n) = W.ω n + Polynomial.C (Polynomial.C W.a₁) * W.φ n * W.ψ n
      + Polynomial.C (Polynomial.C W.a₃) * W.ψ n ^ 3 := W.ω_neg n
  change algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ω (-n))) = _
  rw [h_poly]
  simp only [map_add, map_mul, map_pow]
  rw [algebraMap_mk_CC W W.a₁, algebraMap_mk_CC W W.a₃, φ_ff_eq_Φ_ff]
  rfl

private lemma mulByInt_y_neg_aux
    {K : Type*} [Field K] {x y z a₁ a₃ : K} (hz : z ≠ 0) :
    (y + a₁ * x * z + a₃ * z ^ 3) / (-z) ^ 3 = -(y / z ^ 3) - a₁ * (x / z ^ 2) - a₃ := by
  have hz3 : z ^ 3 ≠ 0 := pow_ne_zero 3 hz
  field_simp
  ring

/-- **Y-coordinate negation** (Silverman III.3.7 mirror): `mulByInt_y W (-n)`
    equals `negY(mulByInt_x W n, mulByInt_y W n)` on `W_KE`. -/
theorem mulByInt_y_neg (n : ℤ) (hn : n ≠ 0) :
    mulByInt_y W (-n) =
      (W_KE W).toAffine.negY (mulByInt_x W n) (mulByInt_y W n) := by
  have hψ : ψ_ff W n ≠ 0 := ψ_ff_ne_zero W hn
  change ω_ff W (-n) / ψ_ff W (-n) ^ 3 = _
  rw [ψ_ff_neg, ω_ff_neg W n]
  change _ = -mulByInt_y W n - (W_KE W).a₁ * mulByInt_x W n - (W_KE W).a₃
  rw [W_KE_a₁, W_KE_a₃]
  unfold mulByInt_y mulByInt_x
  rw [← ψ_ff_sq_eq_ΨSq_ff W n]
  exact mulByInt_y_neg_aux hψ

private lemma Φ_ff_eq (n : ℤ) :
    Φ_ff W n = x_gen W * ψ_ff W n ^ 2 - ψ_ff W (n + 1) * ψ_ff W (n - 1) := by
  rw [← φ_ff_eq_Φ_ff, show W.φ n
    = Polynomial.C Polynomial.X * W.ψ n ^ 2 - W.ψ (n + 1) * W.ψ (n - 1) from rfl]
  simp only [map_sub, map_mul, map_pow]
  rfl

/-- **`mulByInt_x_eq`** (Silverman III.3.7 mirror): for `n ≠ 0`,
    `mulByInt_x W n = x_gen W - ψ_ff W (n+1) · ψ_ff W (n-1) / ψ_ff W n²`. -/
theorem mulByInt_x_eq (n : ℤ) (hn : n ≠ 0) :
    mulByInt_x W n = x_gen W - ψ_ff W (n + 1) * ψ_ff W (n - 1) / ψ_ff W n ^ 2 := by
  have hψ : ψ_ff W n ≠ 0 := ψ_ff_ne_zero W hn
  change Φ_ff W n / ΨSq_ff W n = _
  rw [← ψ_ff_sq_eq_ΨSq_ff, Φ_ff_eq W n]
  field_simp

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `ψ_ff W 1 = 1`: the 1-division polynomial image is the identity of `K(E)`. -/
@[simp] theorem ψ_ff_one : ψ_ff W 1 = 1 := by
  unfold ψ_ff
  rw [W.ψ_one]
  simp [Affine.CoordinateRing.mk]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
private lemma isEllSequence_ψ_ff (m n r : ℤ) :
    ψ_ff W (m + n) * ψ_ff W (m - n) * ψ_ff W r ^ 2 =
      ψ_ff W (m + r) * ψ_ff W (m - r) * ψ_ff W n ^ 2
      - ψ_ff W (n + r) * ψ_ff W (n - r) * ψ_ff W m ^ 2 := by
  have h : W.ψ (m + n) * W.ψ (m - n) * W.ψ r ^ 2 =
      W.ψ (m + r) * W.ψ (m - r) * W.ψ n ^ 2
      - W.ψ (n + r) * W.ψ (n - r) * W.ψ m ^ 2 := W.isEllSequence_ψ m n r
  have hf := congrArg ((algebraMap R KE).comp (Affine.CoordinateRing.mk W.toAffine)) h
  simp only [RingHom.comp_apply, map_mul, map_pow, map_sub] at hf
  exact hf

/-- **`mulByInt_x_sub_mulByInt_x`** (Silverman III.3.7 mirror): for `m, n ≠ 0`,
    `mulByInt_x W m - mulByInt_x W n = ψ_ff(n+m) · ψ_ff(n-m) / (ψ_ff n · ψ_ff m)²`. -/
theorem mulByInt_x_sub_mulByInt_x (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    mulByInt_x W m - mulByInt_x W n =
      ψ_ff W (n + m) * ψ_ff W (n - m) / (ψ_ff W n * ψ_ff W m) ^ 2 := by
  have hψm : ψ_ff W m ≠ 0 := ψ_ff_ne_zero W hm
  have hψn : ψ_ff W n ≠ 0 := ψ_ff_ne_zero W hn
  have hψm2 : ψ_ff W m ^ 2 ≠ 0 := pow_ne_zero 2 hψm
  have hψn2 : ψ_ff W n ^ 2 ≠ 0 := pow_ne_zero 2 hψn
  have heq := isEllSequence_ψ_ff W n m 1
  rw [ψ_ff_one, one_pow, mul_one] at heq
  rw [mulByInt_x_eq W m hm, mulByInt_x_eq W n hn,
    show x_gen W - ψ_ff W (m + 1) * ψ_ff W (m - 1) / ψ_ff W m ^ 2
        - (x_gen W - ψ_ff W (n + 1) * ψ_ff W (n - 1) / ψ_ff W n ^ 2)
      = ψ_ff W (n + 1) * ψ_ff W (n - 1) / ψ_ff W n ^ 2
        - ψ_ff W (m + 1) * ψ_ff W (m - 1) / ψ_ff W m ^ 2 from by ring,
    div_sub_div _ _ hψn2 hψm2, mul_pow, heq]
  congr 1
  ring

/-- **`mulByInt_x_ne_mulByInt_x`** (distinctness): for nonzero `m, n` with
    `m ≠ n` and `m ≠ -n`, `mulByInt_x W m ≠ mulByInt_x W n`. -/
theorem mulByInt_x_ne_mulByInt_x (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hne : m ≠ n)
    (hneg : m ≠ -n) : mulByInt_x W m ≠ mulByInt_x W n := by
  rw [← sub_ne_zero, mulByInt_x_sub_mulByInt_x W m n hm hn]
  have hnm : n + m ≠ 0 := fun h ↦ hneg (by lia)
  have hn_sub_m : n - m ≠ 0 := fun h ↦ hne (by lia)
  exact div_ne_zero (mul_ne_zero (ψ_ff_ne_zero W hnm) (ψ_ff_ne_zero W hn_sub_m))
    (pow_ne_zero _ <| mul_ne_zero (ψ_ff_ne_zero W hn) (ψ_ff_ne_zero W hm))

private lemma ψc_ff_eq (n : ℤ) :
    algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ψc n)) =
      2 * ω_ff W n + algebraMap F KE W.a₁ * Φ_ff W n * ψ_ff W n
      + algebraMap F KE W.a₃ * ψ_ff W n ^ 3 := by
  have h_poly : W.ψc n = 2 * W.ω n + Polynomial.C (Polynomial.C W.a₁) * W.φ n * W.ψ n
      + Polynomial.C (Polynomial.C W.a₃) * W.ψ n ^ 3 := (W.ω_spec n).symm
  change algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ψc n)) = _
  rw [h_poly]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  rw [algebraMap_mk_CC W W.a₁, algebraMap_mk_CC W W.a₃, φ_ff_eq_Φ_ff]
  rfl

omit [DecidableEq F] [W.toAffine.IsElliptic] in
private lemma ψ_ff_mul_ψc_eq (n : ℤ) :
    ψ_ff W n * algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ψc n)) =
      ψ_ff W (2 * n) := by
  have h_poly : W.ψ n * W.ψc n = W.ψ (2 * n) := W.ψc_spec n
  change _ = algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ψ (2 * n)))
  rw [← h_poly]
  simp only [map_mul]
  rfl

private lemma mulByInt_y_sub_negY_aux {K : Type*} [Field K]
    {x y z a₁ a₃ : K} (hz : z ≠ 0) :
    y / z ^ 3 - (-(y / z ^ 3) - a₁ * (x / z ^ 2) - a₃) =
      z * (2 * y + a₁ * x * z + a₃ * z ^ 3) / z ^ 4 := by
  field_simp
  ring

/-- **Y-coord minus negY at the generic point**: at the generic point of `W_KE`,
    `mulByInt_y W n - negY(mulByInt_x W n, mulByInt_y W n) = ψ_ff(2n) / ψ_ff(n)⁴`. -/
theorem mulByInt_y_sub_negY (n : ℤ) (hn : n ≠ 0) :
    mulByInt_y W n - (W_KE W).toAffine.negY (mulByInt_x W n) (mulByInt_y W n) =
      ψ_ff W (2 * n) / ψ_ff W n ^ 4 := by
  have hψ : ψ_ff W n ≠ 0 := ψ_ff_ne_zero W hn
  change ω_ff W n / ψ_ff W n ^ 3 -
      (-(ω_ff W n / ψ_ff W n ^ 3) - (W_KE W).a₁ * (Φ_ff W n / ΨSq_ff W n)
        - (W_KE W).a₃) = _
  rw [W_KE_a₁, W_KE_a₃, ← ψ_ff_sq_eq_ΨSq_ff, mulByInt_y_sub_negY_aux hψ,
    ← ψc_ff_eq W n, ψ_ff_mul_ψc_eq W n]

/-- Specializing to `n = 1`: `mulByInt_y W 1 - negY(...) = ψ_ff 2`. -/
theorem mulByInt_y_one_sub_negY :
    mulByInt_y W 1 - (W_KE W).toAffine.negY (mulByInt_x W 1) (mulByInt_y W 1) =
      ψ_ff W 2 := by
  rw [mulByInt_y_sub_negY W 1 one_ne_zero, mul_one, ψ_ff_one, one_pow, div_one]

/-- **Explicit form of `ψ_ff W 2`**: `ψ_ff W 2 = 2·y_gen + a₁·x_gen + a₃`. -/
theorem ψ_ff_two_eq :
    ψ_ff W 2 = 2 * mulByInt_y W 1
      + (W_KE W).a₁ * mulByInt_x W 1 + (W_KE W).a₃ := by
  rw [← mulByInt_y_one_sub_negY W]
  simp only [WeierstrassCurve.Affine.negY]
  ring

omit [DecidableEq F] [W.toAffine.IsElliptic] in
private lemma algebraMap_Poly_KE_eval₂ (p : Polynomial F) :
    algebraMap (Polynomial F) KE p =
      Polynomial.eval₂ (algebraMap F KE) (x_gen W) p := by
  have h_x : algebraMap (Polynomial F) KE Polynomial.X = x_gen W := rfl
  rw [← h_x, ← Polynomial.aeval_def, Polynomial.aeval_algebraMap_apply]
  simp

/-- **Generic Weierstrass equation** (expanded form): `y_gen² + a₁·x_gen·y_gen +
    a₃·y_gen = x_gen³ + a₂·x_gen² + a₄·x_gen + a₆` at the generic point of `W_KE`. -/
theorem generic_weierstrass :
    mulByInt_y W 1 ^ 2 + (W_KE W).a₁ * mulByInt_x W 1 * mulByInt_y W 1
        + (W_KE W).a₃ * mulByInt_y W 1 =
      mulByInt_x W 1 ^ 3 + (W_KE W).a₂ * mulByInt_x W 1 ^ 2
        + (W_KE W).a₄ * mulByInt_x W 1 + (W_KE W).a₆ := by
  rw [mulByInt_x_one, mulByInt_y_one]
  exact (WeierstrassCurve.Affine.equation_iff _ _).mp (generic_equation W)

/-- **Explicit form of `ψ_ff W 3`** evaluated at the generic x-coordinate:
    `ψ_ff W 3 = 3·x_gen⁴ + b₂·x_gen³ + 3b₄·x_gen² + 3b₆·x_gen + b₈`. -/
theorem ψ_ff_three_eq :
    ψ_ff W 3 = 3 * mulByInt_x W 1 ^ 4
      + (W_KE W).b₂ * mulByInt_x W 1 ^ 3
      + 3 * (W_KE W).b₄ * mulByInt_x W 1 ^ 2
      + 3 * (W_KE W).b₆ * mulByInt_x W 1
      + (W_KE W).b₈ := by
  change algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ψ 3)) = _
  rw [W.ψ_three]
  change algebraMap R KE (algebraMap (Polynomial F) R W.Ψ₃) = _
  rw [← IsScalarTower.algebraMap_apply (Polynomial F) R KE W.Ψ₃,
    algebraMap_Poly_KE_eval₂]
  rw [mulByInt_x_one]
  unfold WeierstrassCurve.Ψ₃
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_ofNat]
  rw [show (algebraMap F KE) W.b₂ = (W_KE W).b₂ from (WeierstrassCurve.map_b₂ _ _).symm,
    show (algebraMap F KE) W.b₄ = (W_KE W).b₄ from (WeierstrassCurve.map_b₄ _ _).symm,
    show (algebraMap F KE) W.b₆ = (W_KE W).b₆ from (WeierstrassCurve.map_b₆ _ _).symm,
    show (algebraMap F KE) W.b₈ = (W_KE W).b₈ from (WeierstrassCurve.map_b₈ _ _).symm]

/-- At the generic point, `mulByInt_y W 1 ≠ negY(mulByInt_x W 1, mulByInt_y W 1)`. -/
theorem mulByInt_y_one_ne_negY :
    mulByInt_y W 1 ≠ (W_KE W).toAffine.negY (mulByInt_x W 1) (mulByInt_y W 1) := by
  rw [← sub_ne_zero, mulByInt_y_one_sub_negY]
  exact ψ_ff_ne_zero W two_ne_zero

/-- The tangent slope at `genericPoint W` on `W_KE`. -/
noncomputable abbrev slopeOne : KE :=
  (W_KE W).toAffine.slope (mulByInt_x W 1) (mulByInt_x W 1)
    (mulByInt_y W 1) (mulByInt_y W 1)

/-- Closed form of `slopeOne` as `(3x² + 2a₂x + a₄ - a₁y) / ψ_ff 2` at the generic point. -/
theorem slopeOne_eq :
    slopeOne W =
      (3 * mulByInt_x W 1 ^ 2 + 2 * (W_KE W).a₂ * mulByInt_x W 1 + (W_KE W).a₄
        - (W_KE W).a₁ * mulByInt_y W 1)
      / ψ_ff W 2 := by
  unfold slopeOne
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl (mulByInt_y_one_ne_negY W),
    mulByInt_y_one_sub_negY]

/-- **addX doubling identity**: at the generic point of `W_KE`,
    `addX(mulByInt_x W 1, mulByInt_x W 1, slopeOne W) = mulByInt_x W 2`. -/
theorem addX_mulByInt_one_mulByInt_one :
    (W_KE W).toAffine.addX (mulByInt_x W 1) (mulByInt_x W 1) (slopeOne W) =
      mulByInt_x W 2 := by
  have hψ2 : ψ_ff W 2 ≠ 0 := ψ_ff_ne_zero W two_ne_zero
  have heq := generic_weierstrass W
  rw [WeierstrassCurve.Affine.addX, slopeOne_eq, mulByInt_x_eq W 2 two_ne_zero,
    show (2 + 1 : ℤ) = 3 from rfl, show (2 - 1 : ℤ) = 1 from rfl, ψ_ff_one,
    mul_one, ← mulByInt_x_one]
  field_simp
  rw [ψ_ff_two_eq, ψ_ff_three_eq]
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  linear_combination (-(W_KE W).a₁ ^ 2 - 4 * (W_KE W).a₂
    - 12 * mulByInt_x W 1) * heq

/-- **Negation-reduction witness**: if `n • genericPoint W` is `.some` at the
    `[n]`-coordinates, then `(-n) • genericPoint W` is `.some` at the `[-n]`-coordinates. -/
theorem zsmul_genericPoint_neg_of_pos (n : ℤ) (hn : n ≠ 0)
    (h_ns_pos : (W_KE W).toAffine.Nonsingular (mulByInt_x W n) (mulByInt_y W n))
    (h_pos : n • genericPoint W =
      Affine.Point.some (mulByInt_x W n) (mulByInt_y W n) h_ns_pos) :
    (-n) • genericPoint W =
      Affine.Point.some (mulByInt_x W (-n)) (mulByInt_y W (-n))
        (by
          rw [mulByInt_x_neg, mulByInt_y_neg W n hn]
          exact (WeierstrassCurve.Affine.nonsingular_neg ..).mpr h_ns_pos) := by
  rw [neg_zsmul, h_pos, Affine.Point.neg_some]
  congr 1
  · exact (mulByInt_x_neg W n).symm
  · exact (mulByInt_y_neg W n hn).symm

/-- **Inductive step (witness form)**: given the `n`-case and the `(n+1)`-th
    `addX`/`addY` identities, derive the `(n+1)`-case (requires `[n]x ≠ [1]x`). -/
theorem zsmul_genericPoint_add_one_of_witness (n : ℤ)
    (hx_ne : mulByInt_x W n ≠ mulByInt_x W 1)
    (h_ns_n : (W_KE W).toAffine.Nonsingular (mulByInt_x W n) (mulByInt_y W n))
    (h_n : n • genericPoint W =
      Affine.Point.some (mulByInt_x W n) (mulByInt_y W n) h_ns_n)
    (h_addX_step : (W_KE W).toAffine.addX (mulByInt_x W n) (mulByInt_x W 1)
        ((W_KE W).toAffine.slope (mulByInt_x W n) (mulByInt_x W 1)
          (mulByInt_y W n) (mulByInt_y W 1)) = mulByInt_x W (n + 1))
    (h_addY_step : (W_KE W).toAffine.addY (mulByInt_x W n) (mulByInt_x W 1)
        (mulByInt_y W n) ((W_KE W).toAffine.slope (mulByInt_x W n) (mulByInt_x W 1)
          (mulByInt_y W n) (mulByInt_y W 1)) = mulByInt_y W (n + 1))
    (h_ns_np1 : (W_KE W).toAffine.Nonsingular (mulByInt_x W (n + 1)) (mulByInt_y W (n + 1))) :
    (n + 1) • genericPoint W =
      Affine.Point.some (mulByInt_x W (n + 1)) (mulByInt_y W (n + 1)) h_ns_np1 := by
  have h_gen : genericPoint W = Affine.Point.some (mulByInt_x W 1) (mulByInt_y W 1)
      (by rw [mulByInt_x_one, mulByInt_y_one]; exact generic_nonsingular W) :=
    genericPoint_eq_mulByInt_one W
  rw [add_zsmul, one_zsmul, h_n, h_gen, Affine.Point.add_of_X_ne hx_ne,
    Affine.Point.some.injEq]
  exact ⟨h_addX_step, h_addY_step⟩

/-- **Doubling case (witness form)**: given the `addX`/`addY` doubling identities,
    derive `(2 : ℤ) • genericPoint W = .some (mulByInt_x W 2) (mulByInt_y W 2) _`. -/
theorem zsmul_genericPoint_two_of_witness
    (h_addX_two : (W_KE W).toAffine.addX (mulByInt_x W 1) (mulByInt_x W 1)
        (slopeOne W) = mulByInt_x W 2)
    (h_addY_two : (W_KE W).toAffine.addY (mulByInt_x W 1) (mulByInt_x W 1)
        (mulByInt_y W 1) (slopeOne W) = mulByInt_y W 2)
    (h_ns_two : (W_KE W).toAffine.Nonsingular (mulByInt_x W 2) (mulByInt_y W 2)) :
    (2 : ℤ) • genericPoint W =
      Affine.Point.some (mulByInt_x W 2) (mulByInt_y W 2) h_ns_two := by
  have h_gen : genericPoint W = Affine.Point.some (mulByInt_x W 1) (mulByInt_y W 1)
      (by rw [mulByInt_x_one, mulByInt_y_one]; exact generic_nonsingular W) :=
    genericPoint_eq_mulByInt_one W
  change (1 + 1 : ℤ) • genericPoint W = _
  rw [add_zsmul, one_zsmul, h_gen,
    Affine.Point.add_self_of_Y_ne (mulByInt_y_one_ne_negY W), Affine.Point.some.injEq]
  exact ⟨h_addX_two, h_addY_two⟩

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- The Jacobian point `smulEval (W_KE W) x₀ y₀ m` (the `m`-fold scalar multiple of a
    nonsingular affine point, read in Jacobian coordinates) is itself nonsingular. -/
private lemma jacobian_nonsingular_smulEval (m : ℤ) {x₀ y₀ : KE}
    (h_ns : (W_KE W).toAffine.Nonsingular x₀ y₀) :
    WeierstrassCurve.Jacobian.Nonsingular (W_KE W).toJacobian
      (smulEval (W_KE W) x₀ y₀ m) := by
  have h_smulEval := WeierstrassCurve.zsmul_eq_smulEval (W := W_KE W) h_ns m
  have h_ns_jac := (m • WeierstrassCurve.Jacobian.Point.fromAffine
    (Affine.Point.some x₀ y₀ h_ns)).nonsingular
  change WeierstrassCurve.Jacobian.NonsingularLift _ _ at h_ns_jac
  rw [h_smulEval] at h_ns_jac
  exact h_ns_jac

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- Transport across the affine ↔ Jacobian equivalence: the `m`-fold scalar multiple of an
    affine point `.some x₀ y₀ _` is the `toAffineLift` of the `m`-fold multiple of its Jacobian
    image `fromAffine (.some x₀ y₀ _)`. -/
private lemma zsmul_some_eq_toAffineLift_fromAffine (m : ℤ) {x₀ y₀ : KE}
    (h_ns : (W_KE W).toAffine.Nonsingular x₀ y₀) :
    m • Affine.Point.some x₀ y₀ h_ns =
      WeierstrassCurve.Jacobian.Point.toAffineLift
        (m • WeierstrassCurve.Jacobian.Point.fromAffine
          (Affine.Point.some x₀ y₀ h_ns)) := by
  have h_inv :
      WeierstrassCurve.Jacobian.Point.toAffineAddEquiv (W_KE W)
        (WeierstrassCurve.Jacobian.Point.fromAffine
          (Affine.Point.some x₀ y₀ h_ns)) =
      Affine.Point.some x₀ y₀ h_ns :=
    (WeierstrassCurve.Jacobian.Point.toAffineAddEquiv (W_KE W)).right_inv _
  have h := map_zsmul (WeierstrassCurve.Jacobian.Point.toAffineAddEquiv (W_KE W))
    m (WeierstrassCurve.Jacobian.Point.fromAffine
      (Affine.Point.some x₀ y₀ h_ns))
  rw [WeierstrassCurve.Jacobian.Point.toAffineAddEquiv_apply] at h
  rw [show WeierstrassCurve.Jacobian.Point.toAffineAddEquiv (W_KE W)
    (WeierstrassCurve.Jacobian.Point.fromAffine _) =
    WeierstrassCurve.Jacobian.Point.toAffineLift
      (WeierstrassCurve.Jacobian.Point.fromAffine _) from rfl] at h
  have h2 : WeierstrassCurve.Jacobian.Point.toAffineLift
      (WeierstrassCurve.Jacobian.Point.fromAffine
        (Affine.Point.some x₀ y₀ h_ns)) =
      Affine.Point.some x₀ y₀ h_ns := by
    rw [← WeierstrassCurve.Jacobian.Point.toAffineAddEquiv_apply]
    exact h_inv
  rw [h2] at h
  exact h.symm

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- The `toAffineLift` of the `m`-fold Jacobian multiple of `fromAffine (.some x₀ y₀ _)` is the
    plain `toAffine` of the explicit division-polynomial coordinate vector `smulEval`. -/
private lemma toAffineLift_zsmul_fromAffine_eq_toAffine (m : ℤ) {x₀ y₀ : KE}
    (h_ns : (W_KE W).toAffine.Nonsingular x₀ y₀) :
    WeierstrassCurve.Jacobian.Point.toAffineLift
        (m • WeierstrassCurve.Jacobian.Point.fromAffine
          (Affine.Point.some x₀ y₀ h_ns)) =
      WeierstrassCurve.Jacobian.Point.toAffine (W_KE W)
        (smulEval (W_KE W) x₀ y₀ m) := by
  unfold WeierstrassCurve.Jacobian.Point.toAffineLift
  rw [WeierstrassCurve.zsmul_eq_smulEval (W := W_KE W) h_ns m]
  rfl

/-- **Main theorem (Silverman III.4.2)**: for every `n ≠ 0`, `n • genericPoint W`
    has coordinates `(mulByInt_x W n, mulByInt_y W n)`. -/
theorem zsmul_genericPoint_eq (n : ℤ) (hn : n ≠ 0) :
    ∃ h : (W_KE W).toAffine.Nonsingular (mulByInt_x W n) (mulByInt_y W n),
      n • genericPoint W =
        Affine.Point.some (mulByInt_x W n) (mulByInt_y W n) h := by
  have hψ : ψ_ff W n ≠ 0 := ψ_ff_ne_zero W hn
  have hns := generic_nonsingular W
  have hZ : smulEval (W_KE W) (x_gen W) (y_gen W) n 2 ≠ 0 := by
    rw [smulEval_generic_Z]; exact hψ
  -- The `m`-fold multiple is nonsingular in Jacobian coordinates.
  have h_ns_smulEval := jacobian_nonsingular_smulEval W n hns
  -- Reading off the affine nonsingularity from `Z ≠ 0`, then identifying the
  -- generic-point coordinates with `Φ_ff / ψ_ff²` etc. and finally `mulByInt_x`.
  have h_ns_affine :
      (W_KE W).toAffine.Nonsingular
        (smulEval (W_KE W) (x_gen W) (y_gen W) n 0 /
          smulEval (W_KE W) (x_gen W) (y_gen W) n 2 ^ 2)
        (smulEval (W_KE W) (x_gen W) (y_gen W) n 1 /
          smulEval (W_KE W) (x_gen W) (y_gen W) n 2 ^ 3) :=
    (WeierstrassCurve.Jacobian.nonsingular_of_Z_ne_zero hZ).mp h_ns_smulEval
  rw [smulEval_generic_X, smulEval_generic_Y, smulEval_generic_Z] at h_ns_affine
  have h_x_eq : Φ_ff W n / ψ_ff W n ^ 2 = mulByInt_x W n := by
    change _ = Φ_ff W n / ΨSq_ff W n
    rw [ψ_ff_sq_eq_ΨSq_ff]
  rw [h_x_eq] at h_ns_affine
  refine ⟨h_ns_affine, ?_⟩
  -- Transport `n • genericPoint` across the affine ↔ Jacobian equivalence and unfold to
  -- the explicit `smulEval` coordinate vector, then read off both coordinates.
  change n • Affine.Point.some (x_gen W) (y_gen W) hns = _
  rw [zsmul_some_eq_toAffineLift_fromAffine W n hns,
    toAffineLift_zsmul_fromAffine_eq_toAffine W n hns,
    WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero h_ns_smulEval hZ,
    Affine.Point.some.injEq]
  refine ⟨?_, ?_⟩
  · rw [smulEval_generic_X, smulEval_generic_Z]
    exact h_x_eq
  · rw [smulEval_generic_Y, smulEval_generic_Z]
    rfl

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- **Generalized Jacobian theorem**: for any nonsingular point `(x₀, y₀)` on
    `W_KE`, `m • .some x₀ y₀ _` has Jacobian-affine coordinates given by
    `(φ_m(x₀, y₀)/ψ_m(x₀, y₀)², ω_m(x₀, y₀)/ψ_m(x₀, y₀)³)`, provided
    `ψ_m(x₀, y₀) ≠ 0`. -/
theorem zsmul_affine_point_eq (m : ℤ) {x₀ y₀ : KE}
    (h_ns : (W_KE W).toAffine.Nonsingular x₀ y₀)
    (h_ψ_ne : ((W_KE W).ψ m).evalEval x₀ y₀ ≠ 0) :
    ∃ h_ns' : (W_KE W).toAffine.Nonsingular
        (((W_KE W).φ m).evalEval x₀ y₀ / ((W_KE W).ψ m).evalEval x₀ y₀ ^ 2)
        (((W_KE W).ω m).evalEval x₀ y₀ / ((W_KE W).ψ m).evalEval x₀ y₀ ^ 3),
      m • Affine.Point.some x₀ y₀ h_ns =
        Affine.Point.some _ _ h_ns' := by
  have hZ : smulEval (W_KE W) x₀ y₀ m 2 ≠ 0 := h_ψ_ne
  have h_ns_smulEval := jacobian_nonsingular_smulEval W m h_ns
  have h_ns_affine :
      (W_KE W).toAffine.Nonsingular
        (smulEval (W_KE W) x₀ y₀ m 0 / smulEval (W_KE W) x₀ y₀ m 2 ^ 2)
        (smulEval (W_KE W) x₀ y₀ m 1 / smulEval (W_KE W) x₀ y₀ m 2 ^ 3) :=
    (WeierstrassCurve.Jacobian.nonsingular_of_Z_ne_zero hZ).mp h_ns_smulEval
  refine ⟨h_ns_affine, ?_⟩
  rw [zsmul_some_eq_toAffineLift_fromAffine W m h_ns,
    toAffineLift_zsmul_fromAffine_eq_toAffine W m h_ns,
    WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero h_ns_smulEval hZ]
  rfl

private lemma zsmul_genericPoint_ne_zero (n : ℤ) (hn : n ≠ 0) :
    (n : ℤ) • genericPoint W ≠ (0 : (W_KE W).toAffine.Point) := by
  obtain ⟨_, h_eq⟩ := zsmul_genericPoint_eq W n hn
  rw [h_eq]
  nofun

/-- **Injectivity of `n ↦ [n]` (Silverman III.4.2b)**: if two nonzero integers `a, b`
    give the same `mulByInt_x` AND `mulByInt_y` coordinates, then `a = b`. Matching the
    full point (x AND y) gives the exact `[·] : ℤ → End E` injectivity, not up to `±`. -/
theorem mulByInt_xy_inj (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : mulByInt_x W a = mulByInt_x W b) (hy : mulByInt_y W a = mulByInt_y W b) : a = b := by
  by_contra hne
  obtain ⟨h_ns_a, h_a⟩ := zsmul_genericPoint_eq W a ha
  obtain ⟨h_ns_b, h_b⟩ := zsmul_genericPoint_eq W b hb
  have hab : a • genericPoint W = b • genericPoint W := by
    rw [h_a, h_b, Affine.Point.some.injEq]; exact ⟨hx, hy⟩
  have hz : (a - b) • genericPoint W = 0 := by
    rw [sub_eq_add_neg, add_zsmul, neg_zsmul, hab, add_neg_cancel]
  exact zsmul_genericPoint_ne_zero W (a - b) (sub_ne_zero.mpr hne) hz

/-- **`ψ_m` at `(mulByInt_x W n, mulByInt_y W n)` is nonzero** when `m*n ≠ 0`. -/
theorem ψ_m_evalEval_mulByInt_ne_zero (m n : ℤ) (hn : n ≠ 0) (hmn : m * n ≠ 0) :
    ((W_KE W).ψ m).evalEval (mulByInt_x W n) (mulByInt_y W n) ≠ 0 := by
  obtain ⟨hns_n, h_n_eq⟩ := zsmul_genericPoint_eq W n hn
  have h_chain : m • Affine.Point.some (mulByInt_x W n) (mulByInt_y W n) hns_n =
      (m * n) • genericPoint W := by
    rw [← h_n_eq, ← mul_zsmul]
  have h_ne_zero : m • Affine.Point.some (mulByInt_x W n) (mulByInt_y W n) hns_n ≠
      (0 : (W_KE W).toAffine.Point) := by
    rw [h_chain]
    exact zsmul_genericPoint_ne_zero W (m * n) hmn
  intro h_Z
  apply h_ne_zero
  have h_smulEval := WeierstrassCurve.zsmul_eq_smulEval (W := W_KE W) hns_n m
  have h_Z' : smulEval (W_KE W) (mulByInt_x W n) (mulByInt_y W n) m 2 = 0 := h_Z
  have h_toAffine_eq_zero :
      WeierstrassCurve.Jacobian.Point.toAffineLift
        (m • WeierstrassCurve.Jacobian.Point.fromAffine
          (Affine.Point.some (mulByInt_x W n) (mulByInt_y W n) hns_n)) = 0 := by
    change (m • WeierstrassCurve.Jacobian.Point.fromAffine
        (Affine.Point.some (mulByInt_x W n) (mulByInt_y W n) hns_n)).point.lift _ _ = 0
    rw [h_smulEval]
    exact WeierstrassCurve.Jacobian.Point.toAffine_of_Z_eq_zero h_Z'
  rw [zsmul_some_eq_toAffineLift_fromAffine W m hns_n, h_toAffine_eq_zero]

/-- The bivariate `φ_m` at `(mulByInt_x W n, mulByInt_y W n)` equals the univariate
    `eval₂ (algebraMap F KE) (mulByInt_x W n) (W.Φ m)`. -/
theorem evalEval_φ_at_mulByInt_eq_eval₂_Φ (m n : ℤ) (hn : n ≠ 0) :
    ((W_KE W).φ m).evalEval (mulByInt_x W n) (mulByInt_y W n) =
      Polynomial.eval₂ (algebraMap F KE) (mulByInt_x W n) (W.Φ m) := by
  rw [show (W_KE W).φ m = (W.φ m).map (Polynomial.mapRingHom (algebraMap F KE)) from
    WeierstrassCurve.map_φ (W := W) (algebraMap F KE) m,
    ← Polynomial.eval₂_eval₂RingHom_apply]
  change (W.φ m).eval₂ (mulByInt_xHom W n) (mulByInt_y W n) = _
  rw [← AdjoinRoot.lift_mk (f := W.toAffine.polynomial)
    (mulByInt_weierstrass W n hn) (W.φ m), Affine.CoordinateRing.mk_φ]
  change AdjoinRoot.lift (mulByInt_xHom W n) (mulByInt_y W n)
    (mulByInt_weierstrass W n hn)
      (AdjoinRoot.of W.toAffine.polynomial (W.Φ m)) = _
  rw [AdjoinRoot.lift_of]
  rfl

/-- Same translation for `ψ_m² → ΨSq_m`. -/
theorem evalEval_ψ_sq_at_mulByInt_eq_eval₂_ΨSq (m n : ℤ) (hn : n ≠ 0) :
    ((W_KE W).ψ m).evalEval (mulByInt_x W n) (mulByInt_y W n) ^ 2 =
      Polynomial.eval₂ (algebraMap F KE) (mulByInt_x W n) (W.ΨSq m) := by
  rw [show (W_KE W).ψ m = (W.ψ m).map (Polynomial.mapRingHom (algebraMap F KE)) from
    WeierstrassCurve.map_ψ (W := W) (algebraMap F KE) m,
    ← Polynomial.eval₂_eval₂RingHom_apply]
  change ((W.ψ m).eval₂ (mulByInt_xHom W n) (mulByInt_y W n)) ^ 2 = _
  rw [show ((W.ψ m).eval₂ (mulByInt_xHom W n) (mulByInt_y W n)) ^ 2 =
      (W.ψ m ^ 2).eval₂ (mulByInt_xHom W n) (mulByInt_y W n) from by
    rw [pow_two, pow_two, Polynomial.eval₂_mul],
    ← AdjoinRoot.lift_mk (f := W.toAffine.polynomial)
      (mulByInt_weierstrass W n hn) (W.ψ m ^ 2),
    show Affine.CoordinateRing.mk W.toAffine (W.ψ m ^ 2) =
      Affine.CoordinateRing.mk W.toAffine (Polynomial.C (W.ΨSq m)) from by
    rw [map_pow, Affine.CoordinateRing.mk_ψ]
    exact Affine.CoordinateRing.mk_Ψ_sq (W := W.toAffine) m]
  change AdjoinRoot.lift (mulByInt_xHom W n) (mulByInt_y W n)
    (mulByInt_weierstrass W n hn)
      (AdjoinRoot.of W.toAffine.polynomial (W.ΨSq m)) = _
  rw [AdjoinRoot.lift_of]
  rfl

/-- **The key composition identity for x-coord**: for `m, n ≠ 0` with `m·n ≠ 0`,
    `(mulByInt W n).pullback (mulByInt_x W m) = mulByInt_x W (m·n)`. -/
theorem mulByInt_pullback_mulByInt_x_eq_mul (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m * n ≠ 0) :
    (mulByInt W.toAffine n).pullback (mulByInt_x W m) = mulByInt_x W (m * n) := by
  have hψm : ψ_ff W m ≠ 0 := ψ_ff_ne_zero W hm
  have hψm_pt : ((W_KE W).ψ m).evalEval (mulByInt_x W n) (mulByInt_y W n) ≠ 0 :=
    ψ_m_evalEval_mulByInt_ne_zero W m n hn hmn
  rw [mulByInt_pullback_mulByInt_x W n m hn, ← evalEval_φ_at_mulByInt_eq_eval₂_Φ W m n hn,
    ← evalEval_ψ_sq_at_mulByInt_eq_eval₂_ΨSq W m n hn]
  obtain ⟨hns_n, h_n_eq⟩ := zsmul_genericPoint_eq W n hn
  obtain ⟨hns_mul, h_mul_eq⟩ :=
    zsmul_affine_point_eq W m (x₀ := mulByInt_x W n) (y₀ := mulByInt_y W n)
      (h_ns := hns_n) (h_ψ_ne := hψm_pt)
  have h_chain : m • Affine.Point.some (mulByInt_x W n) (mulByInt_y W n) hns_n =
      (m * n) • genericPoint W := by
    rw [← h_n_eq, ← mul_zsmul]
  rw [h_chain] at h_mul_eq
  obtain ⟨hns_mn, h_mn_eq⟩ := zsmul_genericPoint_eq W (m * n) hmn
  rw [h_mn_eq, Affine.Point.some.injEq] at h_mul_eq
  exact h_mul_eq.1.symm

private lemma mulByInt_pullback_algebraMap_mk (n : ℤ) (hn : n ≠ 0)
    (p : Polynomial (Polynomial F)) :
    (mulByInt W.toAffine n).pullback
        (algebraMap R KE (Affine.CoordinateRing.mk W.toAffine p)) =
      mulByInt_coordHom W n hn (Affine.CoordinateRing.mk W.toAffine p) := by
  have h_pullback : (mulByInt W.toAffine n).pullback = mulByInt_pullbackAlgHom W n hn := by
    unfold mulByInt
    simp [hn]
  rw [h_pullback]
  change mulByInt_pullbackRingHom W n hn _ = _
  exact IsLocalization.lift_eq _ _

/-- `[n]*(ω_ff W m) = ((W_KE W).ω m).evalEval (mulByInt_x W n) (mulByInt_y W n)`. -/
theorem mulByInt_pullback_ω_ff_eq (m n : ℤ) (hn : n ≠ 0) :
    (mulByInt W.toAffine n).pullback (ω_ff W m) =
      ((W_KE W).ω m).evalEval (mulByInt_x W n) (mulByInt_y W n) := by
  change (mulByInt W.toAffine n).pullback
    (algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ω m))) = _
  rw [mulByInt_pullback_algebraMap_mk W n hn (W.ω m)]
  change AdjoinRoot.lift (mulByInt_xHom W n) (mulByInt_y W n)
    (mulByInt_weierstrass W n hn) _ = _
  rw [AdjoinRoot.lift_mk]
  change (W.ω m).eval₂ (Polynomial.eval₂RingHom (algebraMap F KE) (mulByInt_x W n))
    (mulByInt_y W n) = _
  rw [Polynomial.eval₂_eval₂RingHom_apply,
    show ((W.ω m).map (Polynomial.mapRingHom (algebraMap F KE))) = (W_KE W).ω m from
    (WeierstrassCurve.map_ω (W := W) (algebraMap F KE) m).symm]

/-- Helper: `[n]*(ψ_ff W m) = ((W_KE W).ψ m).evalEval (P_n)`. -/
theorem mulByInt_pullback_ψ_ff_eq (m n : ℤ) (hn : n ≠ 0) :
    (mulByInt W.toAffine n).pullback (ψ_ff W m) =
      ((W_KE W).ψ m).evalEval (mulByInt_x W n) (mulByInt_y W n) := by
  change (mulByInt W.toAffine n).pullback
    (algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ψ m))) = _
  rw [mulByInt_pullback_algebraMap_mk W n hn (W.ψ m)]
  change AdjoinRoot.lift (mulByInt_xHom W n) (mulByInt_y W n)
    (mulByInt_weierstrass W n hn) _ = _
  rw [AdjoinRoot.lift_mk]
  change (W.ψ m).eval₂ (Polynomial.eval₂RingHom (algebraMap F KE) (mulByInt_x W n))
    (mulByInt_y W n) = _
  rw [Polynomial.eval₂_eval₂RingHom_apply,
    show ((W.ψ m).map (Polynomial.mapRingHom (algebraMap F KE))) = (W_KE W).ψ m from
    (WeierstrassCurve.map_ψ (W := W) (algebraMap F KE) m).symm]

/-- **The key composition identity for y-coord**: for `m, n ≠ 0` with `m·n ≠ 0`,
    `(mulByInt W n).pullback (mulByInt_y W m) = mulByInt_y W (m·n)`. -/
theorem mulByInt_pullback_mulByInt_y_eq_mul (m n : ℤ) (hn : n ≠ 0) (hmn : m * n ≠ 0) :
    (mulByInt W.toAffine n).pullback (mulByInt_y W m) = mulByInt_y W (m * n) := by
  have hψm_pt : ((W_KE W).ψ m).evalEval (mulByInt_x W n) (mulByInt_y W n) ≠ 0 :=
    ψ_m_evalEval_mulByInt_ne_zero W m n hn hmn
  change (mulByInt W.toAffine n).pullback (ω_ff W m / ψ_ff W m ^ 3) = _
  rw [map_div₀, map_pow, mulByInt_pullback_ω_ff_eq W m n hn,
    mulByInt_pullback_ψ_ff_eq W m n hn]
  obtain ⟨hns_n, h_n_eq⟩ := zsmul_genericPoint_eq W n hn
  obtain ⟨hns_mul, h_mul_eq⟩ :=
    zsmul_affine_point_eq W m (x₀ := mulByInt_x W n) (y₀ := mulByInt_y W n)
      (h_ns := hns_n) (h_ψ_ne := hψm_pt)
  have h_chain : m • Affine.Point.some (mulByInt_x W n) (mulByInt_y W n) hns_n =
      (m * n) • genericPoint W := by
    rw [← h_n_eq, ← mul_zsmul]
  rw [h_chain] at h_mul_eq
  obtain ⟨hns_mn, h_mn_eq⟩ := zsmul_genericPoint_eq W (m * n) hmn
  rw [h_mn_eq, Affine.Point.some.injEq] at h_mul_eq
  exact h_mul_eq.2.symm

/-- **T-III-4-020b (Silverman III.4.2)**: for `m, n ≠ 0` with `m·n ≠ 0`, the
    multiplication-by-integer isogenies compose: `[m] ∘ [n] = [m·n]`. -/
theorem mulByInt_comp_eq_mul (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m * n ≠ 0) :
    (mulByInt W.toAffine m).comp (mulByInt W.toAffine n) =
      mulByInt W.toAffine (m * n) := by
  apply mulByInt_comp_eq_mul_of_generator_witness W m n hm hn hmn
  · have h_m_x_gen : (mulByInt W.toAffine m).pullback (x_gen W) = mulByInt_x W m := by
      change (mulByInt W.toAffine m).pullback
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X)) = _
      exact mulByInt_pullback_x W m hm
    rw [h_m_x_gen]
    exact mulByInt_pullback_mulByInt_x_eq_mul W m n hm hn hmn
  · have h_m_y_gen : (mulByInt W.toAffine m).pullback
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (AdjoinRoot.root W.toAffine.polynomial)) = mulByInt_y W m :=
      mulByInt_pullback_y W m hm
    rw [h_m_y_gen]
    exact mulByInt_pullback_mulByInt_y_eq_mul W m n hn hmn

/-- **Group-law successor step on the generic point** (Silverman III.5.3 prep): chord-addition
    of `P = (x_gen, y_gen)` against `[m]P = (mulByInt_x m, mulByInt_y m)` realises the
    `[m+1]`-coordinates, stated as `addX`/`addY` identities.

    The secant slope is written out as `(y_gen - mulByInt_y m)/(x_gen - mulByInt_x m)` rather
    than via the `slope` function, whose `if x₁ = x₂` branch carries a `DecidableEq K(E)`
    instance that diamonds across import boundaries (`AdditionPullback`'s
    `instDecidableEqFunctionField` vs mathlib's `FractionRing.instDecidableEq`). With `slope`
    eliminated the conclusion uses only instance-stable `K(E)` field operations, so it is
    consumed verbatim in `MulByIntAddRecurrence`. -/
theorem addX_addY_genericPoint_mulByInt_eq_succ (m : ℤ) (hm : m ≠ 0) (hm1 : m + 1 ≠ 0)
    (hx_ne : x_gen W ≠ mulByInt_x W m) :
    (W_KE W).toAffine.addX (x_gen W) (mulByInt_x W m)
        ((y_gen W - mulByInt_y W m) / (x_gen W - mulByInt_x W m))
          = mulByInt_x W (m + 1) ∧
      (W_KE W).toAffine.addY (x_gen W) (mulByInt_x W m) (y_gen W)
          ((y_gen W - mulByInt_y W m) / (x_gen W - mulByInt_x W m))
            = mulByInt_y W (m + 1) := by
  obtain ⟨h_ns_m, h_m⟩ := zsmul_genericPoint_eq W m hm
  obtain ⟨h_ns_m1, h_m1⟩ := zsmul_genericPoint_eq W (m + 1) hm1
  have key : Affine.Point.some (mulByInt_x W (m + 1)) (mulByInt_y W (m + 1)) h_ns_m1
      = genericPoint W + Affine.Point.some (mulByInt_x W m) (mulByInt_y W m) h_ns_m := by
    rw [← h_m, ← h_m1, add_comm m 1, one_add_zsmul]
  rw [show genericPoint W
        = Affine.Point.some (x_gen W) (y_gen W) (generic_nonsingular W) from rfl,
    Affine.Point.add_of_X_ne hx_ne, Affine.Point.some.injEq,
    WeierstrassCurve.Affine.slope_of_X_ne hx_ne] at key
  exact ⟨key.1.symm, key.2.symm⟩

/-- **Group-law successor step, `[m] ⊞ P` order** (pair-order mirror of
    `addX_addY_genericPoint_mulByInt_eq_succ`): chord-addition of `[m]P` against
    `P = (x_gen, y_gen)` realises the `[m+1]`-coordinates. The secant slope is written
    out rather than via `slope`, for the same `DecidableEq K(E)` instance-stability
    reason; consumed by `addPullback_xy_pair_mulByInt_one_eq_succ`
    (`MulByIntAddRecurrence`). -/
theorem addX_addY_mulByInt_genericPoint_eq_succ (m : ℤ) (hm : m ≠ 0) (hm1 : m + 1 ≠ 0)
    (hx_ne : mulByInt_x W m ≠ x_gen W) :
    (W_KE W).toAffine.addX (mulByInt_x W m) (x_gen W)
        ((mulByInt_y W m - y_gen W) / (mulByInt_x W m - x_gen W))
          = mulByInt_x W (m + 1) ∧
      (W_KE W).toAffine.addY (mulByInt_x W m) (x_gen W) (mulByInt_y W m)
          ((mulByInt_y W m - y_gen W) / (mulByInt_x W m - x_gen W))
            = mulByInt_y W (m + 1) := by
  obtain ⟨h_ns_m, h_m⟩ := zsmul_genericPoint_eq W m hm
  obtain ⟨h_ns_m1, h_m1⟩ := zsmul_genericPoint_eq W (m + 1) hm1
  have key : Affine.Point.some (mulByInt_x W (m + 1)) (mulByInt_y W (m + 1)) h_ns_m1
      = Affine.Point.some (mulByInt_x W m) (mulByInt_y W m) h_ns_m + genericPoint W := by
    rw [← h_m, ← h_m1, add_zsmul, one_zsmul]
  rw [show genericPoint W
        = Affine.Point.some (x_gen W) (y_gen W) (generic_nonsingular W) from rfl,
    Affine.Point.add_of_X_ne hx_ne, Affine.Point.some.injEq,
    WeierstrassCurve.Affine.slope_of_X_ne hx_ne] at key
  exact ⟨key.1.symm, key.2.symm⟩

/-- **Doubling step at the generic point, explicit-slope form**: the `addX`/`addY`
    doubling identities realising the `[1+1]`-coordinates, with the tangent slope
    written out in the `slope_of_Y_ne` quotient form (`slope`-free for instance
    stability). Consumed by the tangent branch of
    `addPullback_xy_pair_mulByInt_one_eq_succ` (`MulByIntAddRecurrence`). -/
theorem addX_addY_mulByInt_one_self_eq_two :
    (W_KE W).toAffine.addX (mulByInt_x W 1) (mulByInt_x W 1)
        ((3 * mulByInt_x W 1 ^ 2 + 2 * (W_KE W).toAffine.a₂ * mulByInt_x W 1
            + (W_KE W).toAffine.a₄ - (W_KE W).toAffine.a₁ * mulByInt_y W 1)
          / (mulByInt_y W 1
              - (W_KE W).toAffine.negY (mulByInt_x W 1) (mulByInt_y W 1)))
          = mulByInt_x W (1 + 1) ∧
      (W_KE W).toAffine.addY (mulByInt_x W 1) (mulByInt_x W 1) (mulByInt_y W 1)
          ((3 * mulByInt_x W 1 ^ 2 + 2 * (W_KE W).toAffine.a₂ * mulByInt_x W 1
              + (W_KE W).toAffine.a₄ - (W_KE W).toAffine.a₁ * mulByInt_y W 1)
            / (mulByInt_y W 1
                - (W_KE W).toAffine.negY (mulByInt_x W 1) (mulByInt_y W 1)))
            = mulByInt_y W (1 + 1) := by
  obtain ⟨h_ns_2, h_2⟩ := zsmul_genericPoint_eq W (1 + 1) (by norm_num)
  have key := h_2
  rw [add_zsmul, one_zsmul, genericPoint_eq_mulByInt_one W,
    Affine.Point.add_self_of_Y_ne (mulByInt_y_one_ne_negY W),
    Affine.Point.some.injEq,
    WeierstrassCurve.Affine.slope_of_Y_ne rfl (mulByInt_y_one_ne_negY W)] at key
  exact key

end HasseWeil

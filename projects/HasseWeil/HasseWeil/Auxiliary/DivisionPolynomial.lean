/-
Copyright (c) 2024 Junyan Xu, David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

import HasseWeil.Auxiliary.EllipticDivisibilitySequence
import HasseWeil.Auxiliary.Universal

/-!
# Division polynomials: omega family and integer scalar multiplication

This file extends mathlib's division polynomial development with:
- The `ω` family of division polynomials (Y-coordinate in Jacobian multiplication).
- The complement `ψc` and invariant `invar`.
- The formula `zsmul_eq_smulEval` expressing `[n]P` in division polynomial coordinates.

The degree results (`natDegree_Φ`, `leadingCoeff_Φ`, `natDegree_ΨSq`, `leadingCoeff_ΨSq`)
are already in mathlib and available via the import above.

## Main definitions

* `WeierstrassCurve.invar`: the "invariant" polynomial `6X² + b₂X + b₄`.
* `WeierstrassCurve.ψc`: the complement of `ψ(n)` in `ψ(2n)`.
* `WeierstrassCurve.ω`: the bivariate polynomials `ωₙ` (Y-coordinate in Jacobian coords).
* `WeierstrassCurve.smulEval`: evaluation of division polynomial triple at a point.

## Main theorems

* `WeierstrassCurve.ψc_spec`: `ψ(n) * ψc(n) = ψ(2n)`.
* `WeierstrassCurve.ω_spec`: `2ω(n) + a₁φ(n)ψ(n) + a₃ψ(n)³ = ψc(n)`.
* `WeierstrassCurve.zsmul_eq_smulEval`: `n • P = (φₙ(x,y) : ωₙ(x,y) : ψₙ(x,y))`.

## References

Ported from the LutzNagell project
(`LutzNagell/DivisionPolynomialOmega.lean`, `LutzNagell/ZSMul.lean`).

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]
-/

open Polynomial
open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow, map_div₀,
    Polynomial.map_ofNat, Polynomial.map_one, map_C, map_X, Polynomial.map_neg, Polynomial.map_add,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_div, coe_mapRingHom,
    apply_ite <| mapRingHom _, WeierstrassCurve.map])

namespace WeierstrassCurve

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

noncomputable section

open Affine (polynomial polynomialX polynomialY negPolynomial)
open WeierstrassCurve (ψ₂ ψ φ)

/-- The "invariant" polynomial `6X² + b₂X + b₄`. -/
def invar : R[X] := 6 * X ^ 2 + C W.b₂ * X + C W.b₄

/-- The complement of ψ(n) in ψ(2n). -/
def ψc : ℤ → R[X][Y] := complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)

lemma isEllSequence_ψ : IsEllSequence W.ψ := IsEllSequence.normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)

lemma C_Ψ₃_eq :
    C W.Ψ₃ = (3 * C X + CC W.a₂) * C W.Ψ₂Sq - polynomialX W ^ 2
      + CC W.a₁ * W.ψ₂ * polynomialX W - CC W.a₁ ^ 2 * polynomial W := by
  simp_rw [Ψ₃, Ψ₂Sq, polynomial, polynomialX, ψ₂, polynomialY, b₂, b₄, b₆, b₈, CC]; C_simp; ring

lemma preΨ₄_add_Ψ₂Sq_sq : W.preΨ₄ + W.Ψ₂Sq ^ 2 = W.invar * W.Ψ₃ := by
  rw [preΨ₄, Ψ₂Sq, invar, Ψ₃]
  linear_combination (norm := (C_simp; ring_nf)) congr(C $W.b_relation) * (@X R _) ^ 2

lemma preΨ₄_add_ψ₂_pow_four : C W.preΨ₄ + W.ψ₂ ^ 4 =
    C (W.invar * W.Ψ₃) + 8 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq) := by
  simp_rw [show 4 = 2 * 2 by rfl, pow_mul, ψ₂_sq, add_sq,
    ← add_assoc, ← C_pow, ← C_add, preΨ₄_add_Ψ₂Sq_sq]; C_simp; ring

lemma φ_mul_ψ (n : ℤ) :
    W.φ n * W.ψ n = C X * W.ψ n ^ 3 - EllSequence.invarDenom W.ψ 1 n := by
  rw [φ, EllSequence.invarDenom]; ring

/-- The `ω` family of division polynomials: `ω n` gives the Y-coordinate in
Jacobian coordinates of the scalar multiplication by `n`. -/
protected def ω (n : ℤ) : R[X][Y] :=
  redInvarDenom W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n *
    ((CC W.a₁ * polynomialY W - polynomialX W) * C W.Ψ₃
      + 4 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq))
  - complEDSAux₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n + negPolynomial W * W.ψ n ^ 3

open WeierstrassCurve (ω)

lemma ω_spec (n : ℤ) :
    2 * W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 = W.ψc n := by
  have hψ : W.ψ = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) := funext fun _ => rfl
  rw [ψc, complEDS₂_eq_redInvarNum_sub, redInvar_normEDS, preΨ₄_add_ψ₂_pow_four, mul_assoc (C _),
    φ_mul_ψ, hψ, invarDenom_normEDS_eq_redInvarDenom_mul, ω, ← hψ, invar, b₂, b₄, ψ₂,
    polynomialY, polynomialX, negPolynomial]
  C_simp; ring

lemma two_mul_ω (n : ℤ) :
    2 * W.ω n = W.ψc n - CC W.a₁ * W.φ n * W.ψ n - CC W.a₃ * W.ψ n ^ 3 := by
  rw [← ω_spec]; abel

lemma ψc_spec (n : ℤ) : W.ψ n * W.ψc n = W.ψ (2 * n) :=
  normEDS_mul_complEDS₂ _ _ _ _

@[simp] lemma ω_zero : W.ω 0 = 1 := by
  simp [ω, redInvarDenom_zero, complEDSAux₂_zero, ψ_zero]

@[simp] lemma ω_one : W.ω 1 = Y := by
  unfold ω ψ₂ negPolynomial polynomialY
  rw [redInvarDenom_one, complEDSAux₂_one, ψ_one]
  simp only [one_pow]
  C_simp
  ring

@[simp] lemma ψc_neg (n : ℤ) : W.ψc (-n) = W.ψc n := by simp [ψc]

end

section Map

open WeierstrassCurve (Ψ Φ ψ φ ω)

variable (f : R →+* S)

@[simp]
lemma map_ω (n : ℤ) : (W.map f).ω n = (W.ω n).map (mapRingHom f) := by
  simp_rw [ω, ← coe_mapRingHom, map_add, map_sub, map_mul, ← map_redInvarDenom,
    ← map_complEDSAux₂, Affine.map_polynomial, Affine.map_polynomialX, Affine.map_polynomialY,
    Affine.map_negPolynomial, map_ψ₂, map_Ψ₃, map_preΨ₄, map_Ψ₂Sq, map_ψ]; simp

private lemma universal_ω_neg (n : ℤ) : letI W := Universal.curve
    W.ω (-n) = W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 := by
  rw [← mul_cancel_left_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero Universal.Poly.two_ne_zero)]
  simp_rw [left_distrib, two_mul_ω, ψc_neg, ψ_neg, φ_neg]; ring

lemma ω_neg (n : ℤ) : W.ω (-n) = W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 := by
  rw [← W.map_specialize, map_ω, universal_ω_neg, map_φ, map_ω, map_ψ]; simp

end Map

section ZSMul

variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S)

noncomputable section

variable {x y : R}

open Universal

lemma evalEval_ψ₂ : W.ψ₂.evalEval x y = polyEval W x y curve.ψ₂ := by
  simp_rw [polyEval_apply, ← map_ψ₂, map_specialize]

lemma evalEval_Ψ₃ : (C W.Ψ₃).evalEval x y = polyEval W x y (C curve.Ψ₃) := by
  simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_Ψ₃, map_specialize]

lemma evalEval_preΨ₄ : (C W.preΨ₄).evalEval x y = polyEval W x y (C curve.preΨ₄) := by
  simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_preΨ₄, map_specialize]

variable {m n : ℤ}

lemma evalEval_ψ : (W.ψ n).evalEval x y = polyEval W x y (curve.ψ n) := by
  simp_rw [polyEval_apply, ← map_ψ, map_specialize]

lemma evalEval_φ : (W.φ n).evalEval x y = polyEval W x y (curve.φ n) := by
  simp_rw [polyEval_apply, ← map_φ, map_specialize]

lemma evalEval_ω : (W.ω n).evalEval x y = polyEval W x y (curve.ω n) := by
  simp_rw [polyEval_apply, ← map_ω, map_specialize]

open WeierstrassCurve (ψ φ ω)

lemma cusp_ψ₂ : cusp.ψ₂ = 2 * Y := by simp [cusp, ψ₂, Affine.polynomialY, C_ofNat]
lemma cusp_Ψ₃ : cusp.Ψ₃ = 3 * X ^ 4 := by simp [cusp, Ψ₃, b₂, b₄, b₆, b₈]
lemma cusp_preΨ₄ : cusp.preΨ₄ = 2 * X ^ 6 := by simp [cusp, preΨ₄, b₂, b₄, b₆, b₈]

lemma polyEval_cusp_ψ : polyEval cusp 1 1 (curve.ψ n) = n := by
  rw [ψ, map_normEDS, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄, cusp_ψ₂, cusp_Ψ₃,
    cusp_preΨ₄]
  simp [evalEval, normEDS_two_three_two]

lemma polyEval_cusp_φ : polyEval cusp 1 1 (curve.φ n) = 1 := by
  simp_rw [φ, map_sub, map_mul, map_pow, polyEval_cusp_ψ, polyEval]
  simp only [coe_eval₂RingHom, eval₂_C, eval₂_X]; ring

lemma polyEval_cusp_ψc : polyEval cusp 1 1 (curve.ψc n) = 2 := by
  rw [ψc, map_complEDS₂, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄]
  simp [cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄, evalEval, complEDS₂_two_three_two]

lemma polyEval_cusp_ω : polyEval cusp 1 1 (curve.ω n) = 1 := by
  have := congr(polyEval cusp 1 1 $(curve.two_mul_ω n))
  simp_rw [map_sub, map_mul, map_ofNat, polyEval_cusp_ψc] at this
  simpa [cusp, polyEval, specialize, curve] using this

/-- The `ψ` family of division polynomials as elements in the universal field. -/
abbrev ψᵤ (n : ℤ) : Universal.Field := polyToField (curve.ψ n)

lemma ψᵤ_eq_normEDS :
    ψᵤ = normEDS
      (polyToField curve.ψ₂) (polyToField <| C curve.Ψ₃) (polyToField <| C curve.preΨ₄) := by
  ext; rw [← map_normEDS]; rfl

lemma isEllSequence_ψᵤ : IsEllSequence ψᵤ := by
  rw [ψᵤ_eq_normEDS]; exact IsEllSequence.normEDS _ _ _

lemma net_ψᵤ (p q r s) : EllSequence.net ψᵤ p q r s = 0 := by
  rw [ψᵤ_eq_normEDS]; apply net_normEDS

lemma ψᵤ_ne_zero (h0 : n ≠ 0) : ψᵤ n ≠ 0 := fun h ↦ by
  rw [ψᵤ, polyToField_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h
  replace h := congr(ringEval cusp_equation_one_one $h)
  rw [ringEval_mk, polyEval_cusp_ψ, map_zero] at h
  exact h0 h

lemma polyToField_φ_ne_zero : polyToField (curve.φ n) ≠ 0 := fun h ↦ by
  rw [polyToField_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h
  replace h := congr(ringEval cusp_equation_one_one $h)
  rw [ringEval_mk, polyEval_cusp_φ, map_zero] at h
  exact one_ne_zero h

lemma polyToField_ψ₂Sq : polyToField (C curve.Ψ₂Sq) = ψᵤ 2 ^ 2 := by
  rw [← map_pow, ψ_two, ψ₂_sq, map_add, map_mul, polyToField_polynomial, mul_zero, add_zero]

namespace Affine

attribute [local instance] Classical.propDecidable

variable (n)
/-- The X-coordinate of `n • (X, Y)` on the universal curve. -/
def smulX : Universal.Field := polyToField (curve.φ n) / (ψᵤ n) ^ 2

/-- The Y-coordinate of `n • (X, Y)` on the universal curve. -/
def smulY : Universal.Field := polyToField (curve.ω n) / (ψᵤ n) ^ 3
variable {n}

@[simp] lemma smulX_zero : smulX 0 = 0 := by simp [smulX, ψᵤ]
@[simp] lemma smulY_zero : smulY 0 = 0 := by simp [smulY, ψᵤ]
@[simp] lemma smulX_one : smulX 1 = polyToField (C X) := by simp [smulX, ψᵤ]
@[simp] lemma smulY_one : smulY 1 = polyToField Y := by simp [smulY, ψᵤ]

lemma smulX_eq (hn : n ≠ 0) :
    smulX n = smulX 1 - ψᵤ (n + 1) * ψᵤ (n - 1) / (ψᵤ n) ^ 2 := by
  rw [smulX, eq_sub_iff_add_eq]
  simp only [φ, ψᵤ, map_sub, map_mul, map_pow, ← add_div]
  rw [div_eq_iff (pow_ne_zero 2 (ψᵤ_ne_zero hn)), smulX_one]
  abel

lemma smulX_neg : smulX (-n) = smulX n := by
  simp_rw [smulX, φ_neg, ψᵤ, ψ_neg, ← map_pow, neg_sq]

lemma smulX_ne_zero (h0 : n ≠ 0) : smulX n ≠ 0 :=
  div_ne_zero polyToField_φ_ne_zero (pow_ne_zero _ <| ψᵤ_ne_zero h0)

lemma smulX_sub_smulX (hm : m ≠ 0) (hn : n ≠ 0) :
    smulX m - smulX n = (ψᵤ (n + m) * ψᵤ (n - m)) / (ψᵤ n * ψᵤ m) ^ 2 := by
  rw [smulX_eq hm, smulX_eq hn,
    show ∀ (c a b : Universal.Field), c - a - (c - b) = b - a from fun c a b => by ring,
    div_sub_div]
  · rw [mul_pow]; congr; convert (isEllSequence_ψᵤ n m 1).symm using 1
    · ring
    · simp [ψᵤ]
  all_goals exact pow_ne_zero _ (ψᵤ_ne_zero <| by assumption)

lemma smulX_two : smulX 2 = smulX 1 - ψᵤ 3 / (ψᵤ 2) ^ 2 := by
  simp [smulX_eq two_ne_zero, ψᵤ]

lemma smulX_sub_sub_smulX_add (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    smulX (n - m) - smulX (n + m) = (ψᵤ (2 * n) * ψᵤ (2 * m)) / (ψᵤ (n + m) * ψᵤ (n - m)) ^ 2 := by
  rw [smulX_sub_smulX sub_ne add_ne]
  simp only [show n + m + (n - m) = 2 * n from by ring, show n + m - (n - m) = 2 * m from by ring]

lemma smulX_ne_smulX (ne : m ≠ n) (ne_neg : m ≠ -n) : smulX m ≠ smulX n := by
  obtain rfl | hm := eq_or_ne m 0
  · rw [smulX_zero]; exact (smulX_ne_zero ne.symm).symm
  obtain rfl | hn := eq_or_ne n 0
  · rw [smulX_zero]; exact smulX_ne_zero ne
  rw [← sub_ne_zero, smulX_sub_smulX hm hn]
  rw [ne_comm, ← sub_ne_zero] at ne
  rw [Ne, ← add_eq_zero_iff_eq_neg, add_comm] at ne_neg
  refine div_ne_zero (mul_ne_zero ?_ ?_) (pow_ne_zero _ <| mul_ne_zero ?_ ?_) <;>
    apply ψᵤ_ne_zero <;> assumption

private lemma smulY_sub_negY_aux {F} [Field F] {a₁ a₃ x y z : F} (h0 : z ≠ 0) :
    y / z ^ 3 - (-(y / z ^ 3) - a₁ * (x / z ^ 2) - a₃) =
      z * (2 * y + a₁ * x * z + a₃ * z ^ 3) / z ^ 4 := by
  field_simp; ring

lemma smulY_sub_negY (h0 : n ≠ 0) :
    smulY n - pointedCurve.toAffine.negY (smulX n) (smulY n) = ψᵤ (2 * n) / (ψᵤ n) ^ 4 := by
  simp_rw [Affine.negY, pointedCurve_a₁, pointedCurve_a₃, smulX, smulY, ψᵤ, ← ψc_spec, ← ω_spec,
    map_mul, map_add, map_mul, map_pow, map_ofNat]
  exact smulY_sub_negY_aux (ψᵤ_ne_zero h0)

lemma smulY_one_sub_negY :
    smulY 1 - pointedCurve.toAffine.negY (smulX 1) (smulY 1) = ψᵤ 2 := by
  rw [smulY_sub_negY one_ne_zero, mul_one, ψᵤ, ψᵤ, ψ_one, map_one, one_pow, div_one]

lemma smulY_one_ne_negY : smulY 1 ≠ pointedCurve.toAffine.negY (smulX 1) (smulY 1) := by
  rw [← sub_ne_zero, smulY_one_sub_negY]; exact ψᵤ_ne_zero two_ne_zero

/-- The slope of the tangent line at (X,Y) on the universal curve. -/
def slopeOne : Universal.Field :=
  pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)

lemma slopeOne_eq_neg_div : slopeOne = -polyToField curve.polynomialX / ψᵤ 2 := by
  have hψ₂ : ψᵤ 2 ≠ 0 := ψᵤ_ne_zero two_ne_zero
  rw [slopeOne, Affine.slope_of_Y_ne rfl smulY_one_ne_negY, smulY_one_sub_negY,
    Affine.polynomialX]
  simp only [smulX_one, smulY_one, pointedCurve_a₁, pointedCurve_a₂, pointedCurve_a₄,
    map_sub, map_mul, map_pow, map_ofNat, map_add]
  rw [eq_comm, ← sub_eq_zero]; field_simp; norm_num

private lemma addX_smul_one_smul_one_aux {F} [Field F] {a₁ a₂ x dx dy : F} (h0 : dy ≠ 0) :
    (-dx / dy) ^ 2 + a₁ * (-dx / dy) - a₂ - x - x - x =
      (dx ^ 2 - a₁ * dx * dy - (3 * x + a₂) * dy ^ 2) / dy ^ 2 := by
  field_simp; ring

private lemma addX_smul_ring_identity {F} [Field F] {X' ψ a₁ a₂ cx : F} :
    X' * (X' + -(ψ * a₁)) - ψ ^ 2 * a₂ - ψ ^ 2 * cx - ψ ^ 2 * cx =
    ψ ^ 2 * cx - (ψ ^ 2 * (cx * 3 + a₂) - X' ^ 2 + X' * ψ * a₁ - a₁ ^ 2 * 0) := by ring

lemma addX_smul_one_smul_one :
    pointedCurve.toAffine.addX (smulX 1) (smulX 1) slopeOne = smulX 2 := by
  have hψ₂ : polyToField (ψ₂ curve) ≠ (0 : Universal.Field) :=
    ψ_two curve ▸ ψᵤ_ne_zero two_ne_zero
  rw [Affine.addX, slopeOne_eq_neg_div, smulX_two, smulX_one]
  simp only [pointedCurve_a₁, pointedCurve_a₂, ψᵤ, ψ_two, ψ_three, C_Ψ₃_eq,
    polyToField_ψ₂Sq, map_sub, map_add, map_mul, map_pow, map_ofNat, polyToField_polynomial]
  field_simp [hψ₂]
  exact addX_smul_ring_identity

private lemma addY_smul_one_smul_one_aux {F} [Field F] {a₁ a₃ dx dy x y ψ₃ t : F} (h0 : dy ≠ 0) :
    ((a₁ * dy - dx) * ψ₃ + 0 * t + (-y - (a₁ * x + a₃)) * dy ^ 3) / dy ^ 3 =
      -(-dx / dy * (x - ψ₃ / dy ^ 2 - x) + y) - a₁ * (x - ψ₃ / dy ^ 2) - a₃ := by
  field_simp; ring

open EllSequence in
lemma addY_smul_one_smul_one :
    pointedCurve.toAffine.addY (smulX 1) (smulX 1) (smulY 1) slopeOne = smulY 2 := .symm <| by
  rw [smulY, ω, redInvarDenom_two, one_mul, complEDSAux₂_two, sub_zero, Affine.addY,
    Affine.negAddY, addX_smul_one_smul_one, smulX_two, Affine.negY, Affine.negPolynomial,
    slopeOne_eq_neg_div, ← ψ₂, ← ψ_two, smulX_one, smulY_one, ψᵤ, ψᵤ, ψ_three]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, polyToField_polynomial, mul_zero,
    pointedCurve_a₁, pointedCurve_a₃]
  exact addY_smul_one_smul_one_aux (ψᵤ_ne_zero two_ne_zero)

private lemma smulY_neg_aux {F} [Field F] {a₁ a₃ x y z : F} (hz : z ≠ 0) :
    (y + a₁ * x * z + a₃ * z ^ 3) / (-z) ^ 3 = -(y / z ^ 3) - a₁ * (x / z ^ 2) - a₃ := by
  rw [neg_pow]; field_simp; ring

lemma smulY_neg (h0 : n ≠ 0) :
    smulY (-n) = pointedCurve.toAffine.negY (smulX n) (smulY n) := by
  simp only [Affine.negY, smulX, smulY, ψ_neg, ω_neg, map_add, map_neg, map_mul, map_pow, ψᵤ]
  exact smulY_neg_aux (ψᵤ_ne_zero h0)

private lemma smulX_add_aux {F} [Field F] {m n m₂ n₂ a s : F}
    (hm : m ≠ 0) (hn : n ≠ 0) (ha : a ≠ 0) (hs : s ≠ 0) :
    n₂ / n ^ 4 * (m₂ / m ^ 4) / (a * s / (n * m) ^ 2) ^ 2 = n₂ * m₂ / (a * s) ^ 2 := by
  field_simp

lemma smulX_add (hm : m ≠ 0) (hn : n ≠ 0) (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    let ψ₂ x y := y - pointedCurve.toAffine.negY x y
    smulX (n + m) = smulX (n - m) -
      ψ₂ (smulX n) (smulY n) * ψ₂ (smulX m) (smulY m) / (smulX m - smulX n) ^ 2 := by
  change smulX (n + m) = smulX (n - m) -
    (smulY n - pointedCurve.toAffine.negY (smulX n) (smulY n)) *
    (smulY m - pointedCurve.toAffine.negY (smulX m) (smulY m)) / (smulX m - smulX n) ^ 2
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq']
  calc _ = ψᵤ (2 * n) / ψᵤ n ^ 4 * (ψᵤ (2 * m) / ψᵤ m ^ 4) /
      (ψᵤ (n + m) * ψᵤ (n - m) / (ψᵤ n * ψᵤ m) ^ 2) ^ 2 := by
        rw [smulY_sub_negY hm, smulY_sub_negY hn, smulX_sub_smulX hm hn]
      _ = ψᵤ (2 * n) * ψᵤ (2 * m) / (ψᵤ (n + m) * ψᵤ (n - m)) ^ 2 :=
        smulX_add_aux (ψᵤ_ne_zero hm) (ψᵤ_ne_zero hn)
          (ψᵤ_ne_zero add_ne) (ψᵤ_ne_zero sub_ne)
      _ = smulX (n - m) - smulX (n + m) :=
        (smulX_sub_sub_smulX_add add_ne sub_ne).symm

private lemma smulY_add_sub_negY_aux {F} [Field F] {m n m₂ n₂ a s am an : F}
    (hm : m ≠ 0) (hn : n ≠ 0) (ha : a ≠ 0) (hs : s ≠ 0) :
    (m₂ / m ^ 4 * (an * m / (a * n) ^ 2) - n₂ / n ^ 4 * (am * n / (a * m) ^ 2))
      / (a * s / (n * m) ^ 2)
      = (an * m₂ * n - am * n₂ * m) * a / (s * n * m) / a ^ 4 := by
  field_simp

lemma smulY_add_sub_negY (hm : m ≠ 0) (hn : n ≠ 0) (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    let ψ₂ x y := y - pointedCurve.toAffine.negY x y
    ψ₂ (smulX (n + m)) (smulY (n + m)) =
      (ψ₂ (smulX m) (smulY m) * (smulX n - smulX (n + m))
        - ψ₂ (smulX n) (smulY n) * (smulX m - smulX (n + m))) / (smulX m - smulX n) := by
  simp_rw [smulY_sub_negY add_ne, smulY_sub_negY hm, smulY_sub_negY hn, smulX_sub_smulX hn add_ne,
    smulX_sub_smulX hm add_ne, smulX_sub_smulX hm hn, add_sub_cancel_left, add_sub_cancel_right]
  rw [smulY_add_sub_negY_aux (ψᵤ_ne_zero hm) (ψᵤ_ne_zero hn) (ψᵤ_ne_zero add_ne)
    (ψᵤ_ne_zero sub_ne)]
  congr; rw [eq_div_iff]
  · have := (EllSequence.net_add_sub_iff _ n m).mp (net_ψᵤ _ _ _ _)
    linear_combination (norm := ring_nf) this
  apply_rules [mul_ne_zero, ψᵤ_ne_zero]

open Affine.Point

open WeierstrassCurve.Affine in
instance : AddGroup ((curve.baseChange Universal.Field).Point) := inferInstance

/-- The affine coordinates of `n • Universal.Affine.point` is given by `(smulX n, smulY n)`. -/
theorem zsmul_point_eq_smulX_smulY : n ≠ 0 →
    ∃ h : Affine.Nonsingular _ (smulX n) (smulY n),
      n • Affine.point = .some _ _ h := by
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih h0 ↦ ?_
    obtain _|_|_|n := n
    · exact (h0 rfl).elim
    · simp_rw [zero_add, Nat.cast_one, one_zsmul, smulX_one, smulY_one]
      exact ⟨Affine.equation_iff_nonsingular.mp equation_point, rfl⟩
    all_goals obtain ⟨ns, eq⟩ := ih 1 (by omega) one_ne_zero
    · erw [← addX_smul_one_smul_one, ← addY_smul_one_smul_one, zero_add, add_zsmul _ 1 1, eq]
      exact ⟨Affine.nonsingular_add ns ns fun h ↦ smulY_one_ne_negY h.2,
        add_self_of_Y_ne smulY_one_ne_negY⟩
    set n2 := n + 1 + 1
    obtain ⟨ns1, eq1⟩ := ih (n + 1) (by omega) (by omega)
    obtain ⟨ns2, eq2⟩ := ih n2 (by omega) (by omega)
    have ne : smulX n2 ≠ smulX 1 := smulX_ne_smulX (by omega) (by omega)
    simp_rw [show (n + 1 : ℕ) = n2 + (-1 : ℤ) by omega, add_zsmul, neg_smul] at eq1
    let _U := pointedCurve.toAffine
    erw [eq2, eq, add_of_X_ne ne, some_eq_some_iff] at eq1
    let L := _U.slope (smulX n2) (smulX 1) (smulY n2) (smulY 1)
    have X_eq : smulX (n2 + 1 : ℕ) = _U.addX (smulX n2) (smulX 1) L := by
      rw [Nat.cast_add, Nat.cast_one, smulX_add one_ne_zero (by omega) (by omega) (by omega),
        Affine.addX_eq_addX_negY_sub _ _ ne, sub_eq_add_neg (n2 : ℤ), ← eq1.1]; rfl
    have Y_eq : smulY (n2 + 1 : ℕ) = _U.addY (smulX n2) (smulX 1) (smulY n2) L := by
      rw [← mul_cancel_left_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero Field.two_ne_zero),
        ← add_right_cancel_iff (a := _U.a₁ * smulX (n2 + 1 : ℕ) + _U.a₃)]
      convert smulY_add_sub_negY (n := n2) one_ne_zero (by omega) (by omega) (by omega) using 1
      · simp_rw [Affine.negY, Nat.cast_add]; norm_cast
        simp only [two_mul]; abel
      convert _U.addY_sub_negY_addY (smulY n2) (smulY 1) ne using 1
      · rw [Affine.negY, ← X_eq]; ring
      · rw [← X_eq]; rfl
    rw [X_eq, Y_eq, n2.cast_add, add_zsmul, eq, eq2]
    exact ⟨Affine.nonsingular_add ns2 ns (fun h => ne h.1), add_of_X_ne ne⟩
  | neg ih n =>
    rw [neg_ne_zero]; intro h0
    obtain ⟨ns, eq⟩ := ih n h0
    simp_rw [smulX_neg, smulY_neg h0, neg_smul, eq, neg_some]
    exact ⟨(Affine.nonsingular_neg ..).mpr ns, trivial⟩

lemma zsmul_point_ne_zero (h0 : n ≠ 0) :
    n • Affine.point ≠ (0 : ((curve.baseChange Universal.Field).Point)) := by
  obtain ⟨ns, eq⟩ := zsmul_point_eq_smulX_smulY h0
  rw [eq]
  exact fun h => nomatch h

end Affine

namespace Jacobian

open WeierstrassCurve.Jacobian

lemma zsmul_point_ne_zero (h0 : n ≠ 0) :
    n • Jacobian.point ≠ (0 : Point (curve.baseChange Universal.Field)) := by
  change n • Point.fromAffine Affine.point ≠ 0
  rw [show Point.fromAffine = (Point.toAffineAddEquiv _).symm from rfl,
    ← map_zsmul (Point.toAffineAddEquiv _).symm,
    Ne, map_eq_zero_iff _ (Point.toAffineAddEquiv _).symm.injective]
  exact Affine.zsmul_point_ne_zero h0

lemma point_point : Jacobian.point.point = ⟦![polyToField (C X), polyToField Y, 1]⟧ := rfl

/-- The three families of universal division polynomials as a 3-tuple. -/
abbrev smulPoly (n : ℤ) : Fin 3 → Poly := ![curve.φ n, curve.ω n, curve.ψ n]
/-- The three families of division polynomials as elements in the universal ring. -/
abbrev smulRing (n : ℤ) : Fin 3 → Universal.Ring := AdjoinRoot.mk _ ∘ smulPoly n
/-- The three families of division polynomials as elements in the universal field. -/
abbrev smulField (n : ℤ) : Fin 3 → Universal.Field := polyToField ∘ smulPoly n

lemma algebraMap_comp_smulRing (n : ℤ) : algebraMap _ _ ∘ smulRing n = smulField n := by
  ext i; fin_cases i <;> rfl

/-- The Jacobian coordinates of `n • Universal.Jacobian.point` is given by `smulField n`. -/
theorem zsmul_point_eq_smulField : (n • Jacobian.point).point = ⟦smulField n⟧ := by
  rw [← fin3_def (smulField n), smulField, smulPoly]
  simp_rw [Function.comp, fin3_def_ext]
  obtain rfl | hn := eq_or_ne n 0
  · simp_rw [zero_zsmul, φ_zero, ω_zero, ψ_zero, map_zero, map_one]; rfl
  obtain ⟨ns, eq⟩ := Affine.zsmul_point_eq_smulX_smulY hn
  change (n • (Point.toAffineAddEquiv _).symm Affine.point).point = _
  rw [← map_zsmul, eq]
  have := ψᵤ_ne_zero hn
  refine Quotient.sound ⟨.mk0 _ (inv_ne_zero this), ?_⟩
  simp_rw [Units.smul_def, Jacobian.smul_fin3]
  ext i; fin_cases i <;> simp [Affine.smulX, Affine.smulY, this, inv_mul_eq_div]

private lemma ω_neg_eq_neg_negY : curve.ω (-n) = -negY curvePoly (smulPoly n) := by
  unfold smulPoly WeierstrassCurve.Jacobian.negY curvePoly
  simp_rw [ω_neg, fin3_def_ext, WeierstrassCurve.baseChange, WeierstrassCurve.map,
    show ∀ x, CC x = (algebraMap _ Poly) x from fun _ => rfl]
  norm_num; ring

lemma smulPoly_neg : smulPoly (-n) = (-1 : Poly) • neg curvePoly (smulPoly n) := by
  simp [smulPoly, ω_neg_eq_neg_negY, neg, smul_fin3, (show Odd 3 by decide).neg_pow]

lemma smulRing_neg : smulRing (-n) = (-1 : Universal.Ring) • neg curveRing (smulRing n) := by
  simp_rw [smulRing, smulPoly_neg, WeierstrassCurve.Jacobian.comp_smul,
    ← WeierstrassCurve.Jacobian.map_neg, map_neg, map_one]; rfl

private lemma dblZ_smulPoly : dblZ curvePoly (smulPoly n) = curve.ψ (2 * n) := by
  unfold dblZ smulPoly WeierstrassCurve.Jacobian.negY curvePoly
  simp_rw [fin3_def_ext, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  rw [← ψc_spec _ n]; congr; convert curve.ω_spec n using 1
  simp_rw [show ∀ x, CC x = (algebraMap _ Poly) x from fun _ => rfl]
  norm_num; ring

private lemma nonsingular_smulField :
    Nonsingular curveField (smulField n) := by
  simpa only [zsmul_point_eq_smulField, nonsingularLift_iff] using (n • Jacobian.point).nonsingular

private lemma two_zsmul_point_eq_dblXYZ {P : Point (baseChange curve Universal.Field)}
    {v : Fin 3 → Universal.Field} (hv : P.point = ⟦v⟧) :
    ((2 : ℤ) • P).point = ⟦dblXYZ curveField v⟧ := by
  rw [two_zsmul, Point.add_point, hv, addMap_eq, add_self]

private lemma add_point_of_ne_eq_addXYZ {P Q : Point (baseChange curve Universal.Field)}
    {v w : Fin 3 → Universal.Field} (hv : P.point = ⟦v⟧) (hw : Q.point = ⟦w⟧) (hne : P ≠ Q) :
    (P + Q).point = ⟦addXYZ curveField v w⟧ := by
  rw [Point.add_point, hv, hw, addMap_eq, add_of_not_equiv]
  intro h; exact hne (Point.ext_iff.mpr (hv ▸ hw ▸ Quotient.eq.mpr h))

private lemma zsmul_point_ne (h : m ≠ n) : m • Jacobian.point ≠ n • Jacobian.point := by
  intro heq
  apply zsmul_point_ne_zero (sub_ne_zero.mpr h)
  rw [sub_smul, heq, sub_self]

lemma dblXYZ_smulField : dblXYZ curveField (smulField n) = smulField (2 * n) := by
  obtain rfl | hn := eq_or_ne n 0
  · simp only [mul_zero, smulField, smulPoly, comp_fin3]
    simp only [dblXYZ, dblX, dblY, dblZ, dblU_eq, negY, negDblY, curveField, fin3_def_ext]
    ext i; fin_cases i <;>
      simp [fin3_def_ext] <;>
      norm_num
  refine (equiv_iff_eq_of_Z_eq ?_ (ψᵤ_ne_zero <| mul_ne_zero two_ne_zero hn)).mp
    (Quotient.exact ?_)
  · simp only [smulField, smulPoly, fin3_def_ext, Function.comp, ← dblZ_smulPoly, ← map_dblZ]; rfl
  · exact (two_zsmul_point_eq_dblXYZ zsmul_point_eq_smulField).symm.trans <|
      (congrArg Point.point (mul_zsmul _ 2 n).symm).trans zsmul_point_eq_smulField

lemma dblXYZ_smulRing : dblXYZ curveRing (smulRing n) = smulRing (2 * n) :=
  (IsFractionRing.injective _ Universal.Field).comp_left <| by
    simp_rw [← map_dblXYZ]; exact dblXYZ_smulField

private lemma addZ_smulPoly :
    addZ (smulPoly m) (smulPoly n) = curve.ψ (n + m) * curve.ψ (n - m) := by
  simp_rw [addZ, smulPoly, φ]; convert (curve.isEllSequence_ψ n m 1).symm using 1
  · simp only [fin3_def_ext]; ring
  · rw [ψ_one]; ring

private lemma smulField_neg :
    smulField (-n) = (-1 : Universal.Field) • neg curveField (smulField n) := by
  simp_rw [smulField, smulPoly_neg, Jacobian.comp_smul, ← Jacobian.map_neg, map_neg, map_one]; rfl

private lemma smulField_zero : smulField 0 = ![1, 1, 0] := by
  simp [smulField, smulPoly, comp_fin3]

lemma addXYZ_smulField :
    addXYZ curveField (smulField m) (smulField n) =
      polyToField (curve.ψ (n - m)) • smulField (n + m) := by
  obtain rfl | h := eq_or_ne m n
  · rw [sub_self, ψ_zero, map_zero, smul_fin3,
      addXYZ_self nonsingular_smulField.1, zero_pow two_ne_zero, zero_pow (by decide)]
    simp_rw [zero_mul]
  obtain rfl | ne_neg := eq_or_ne n (-m)
  · have jac_one_smul : ∀ (P : Fin 3 → Universal.Field), (1 : Universal.Field) • P = P :=
      fun _ => by simp only [smul_fin3, one_pow, one_mul, fin3_def]
    rw [← jac_one_smul (smulField m), smulField_neg, neg_add_cancel,
      addXYZ_smul, one_mul, neg_one_sq (R := Universal.Field), addXYZ_neg nonsingular_smulField.1,
      jac_one_smul, show (-m - m : ℤ) = -(2 * m) from by ring,
      ψ_neg, map_neg, ← dblZ_smulPoly, ← map_dblZ, smulField_zero]
    rfl
  refine (equiv_iff_eq_of_Z_eq ?_ ?_).mp (Quotient.exact ?_)
  · conv_rhs => rw [smulField, comp_fin3, smul_fin3, (fin3_def_ext _ _ _).2.2, mul_comm]
    simp_rw [addXYZ, fin3_def_ext, ← map_mul, ← addZ_smulPoly, ← map_addZ]
  · simp only [smul_fin3, fin3_def_ext]
    apply mul_ne_zero <;> apply ψᵤ_ne_zero <;> omega
  · rw [smul_eq _ (ψᵤ_ne_zero <| sub_ne_zero_of_ne h.symm).isUnit,
      ← zsmul_point_eq_smulField, add_comm, add_zsmul,
      add_point_of_ne_eq_addXYZ zsmul_point_eq_smulField zsmul_point_eq_smulField
        (zsmul_point_ne h)]

lemma addXYZ_smulRing :
    addXYZ curveRing (smulRing m) (smulRing n) =
      AdjoinRoot.mk curve.polynomial (curve.ψ (n - m)) • smulRing (n + m) :=
  (IsFractionRing.injective Universal.Ring Universal.Field).comp_left <| by
    simp_rw [← map_addXYZ, WeierstrassCurve.Jacobian.comp_smul]; exact addXYZ_smulField

lemma addXYZ_smulField₁ :
    addXYZ curveField (smulField n) (smulField (n + 1)) = smulField (2 * n + 1) := by
  rw [addXYZ_smulField, add_sub_cancel_left, ψ_one, map_one,
    show (1 : Universal.Field) • smulField (n + 1 + n) = smulField (n + 1 + n) by
      simp only [WeierstrassCurve.Jacobian.smul_fin3, one_pow, one_mul,
        WeierstrassCurve.Jacobian.fin3_def]]
  congr 1; omega

lemma addXYZ_smulRing₁ :
    addXYZ curveRing (smulRing n) (smulRing (n + 1)) = smulRing (2 * n + 1) := by
  rw [addXYZ_smulRing, add_sub_cancel_left, ψ_one, map_one,
    show (1 : Universal.Ring) • smulRing (n + 1 + n) = smulRing (n + 1 + n) by
      simp only [WeierstrassCurve.Jacobian.smul_fin3, one_pow, one_mul,
        WeierstrassCurve.Jacobian.fin3_def]]
  congr 1; omega

end Jacobian

variable (x y) in
/-- The evaluation of the division polynomials at a point `(x,y)`, equal to the
Jacobian coordinates of `n • (x,y)` (see `zsmul_eq_smulEval`). -/
abbrev smulEval (n : ℤ) : Fin 3 → R := evalEval x y ∘ ![W.φ n, W.ω n, W.ψ n]

variable {W} (eqn : W.toAffine.Equation x y)

open Universal Jacobian

lemma ringEval_comp_smulRing (n : ℤ) : ringEval eqn ∘ smulRing n = smulEval W x y n := by
  conv_rhs => rw [smulEval, ← W.map_specialize, map_φ, map_ω, map_ψ, ← coe_mapRingHom,
    ← WeierstrassCurve.Jacobian.comp_fin3, ← Function.comp_assoc, ← smulPoly,
    ← coe_evalEvalRingHom,
    ← RingHom.coe_comp, ← eval₂RingHom_eval₂RingHom]
  rw [smulRing, ← Function.comp_assoc, ← RingHom.coe_comp, ringEval_comp_mk, polyEval]

lemma ringEval_ψ (n : ℤ) :
    ringEval eqn (AdjoinRoot.mk _ <| curve.ψ n) = evalEval x y (W.ψ n) :=
  congr_fun (ringEval_comp_smulRing eqn n) 2

include eqn in
lemma dblXYZ_smulEval (n : ℤ) :
    dblXYZ W (smulEval W x y n) = smulEval W x y (2 * n) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← dblXYZ_smulRing, ← map_dblXYZ, curveRing_map_ringEval]

include eqn in
lemma addXYZ_smulEval (m n : ℤ) :
    addXYZ W (smulEval W x y m) (smulEval W x y n) =
      evalEval x y (W.ψ (n - m)) • smulEval W x y (n + m) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← ringEval_ψ eqn]
  rw [← WeierstrassCurve.Jacobian.comp_smul, ← addXYZ_smulRing, ← map_addXYZ]
  simp_rw [curveRing_map_ringEval]

include eqn in
lemma addXYZ_smulEval₁ (n : ℤ) :
    addXYZ W (smulEval W x y n) (smulEval W x y (n + 1)) = smulEval W x y (2 * n + 1) := by
  simp_rw [← ringEval_comp_smulRing eqn, ← addXYZ_smulRing₁, ← map_addXYZ,
    curveRing_map_ringEval]

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

open Universal

/-- The integer multiples of a nonsingular rational point `(x,y)` on a Weierstrass curve
is given by `smulEval` in Jacobian coordinates. -/
theorem zsmul_eq_smulEval {x y : F} (h : Affine.Nonsingular W x y) (n : ℤ) :
    (n • Point.fromAffine (Affine.Point.some _ _ h)).point = ⟦smulEval W x y n⟧ := by
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih ↦ ?_
    obtain _|_|n := n
    · rw [Nat.cast_zero, zero_smul, smulEval, WeierstrassCurve.Jacobian.comp_fin3]
      congrm(⟦?_⟧); simp [evalEval]
    · rw [Nat.cast_one, one_smul, smulEval, WeierstrassCurve.Jacobian.comp_fin3]
      congrm(⟦?_⟧); simp [evalEval]
    obtain ⟨n, rfl|rfl⟩ := n.even_or_odd'
    · rw [show (2 * n + 1 + 1 : ℕ) = 2 * (n + 1) from by omega]
      rw [Nat.cast_mul, mul_smul, natCast_zsmul, two_nsmul,
        Point.add_point, ih _ (by omega), addMap_eq, add_self,
        dblXYZ_smulEval h.1]; rfl
    · rw [show 2 * n + 1 + 1 + 1 = (n + 1) + (n + 1 + 1) by omega, Nat.cast_add, add_smul]
      have hne : (↑(n + 1) : ℤ) • Point.fromAffine (Affine.Point.some _ _ h) ≠
          (↑(n + 1 + 1) : ℤ) • Point.fromAffine (Affine.Point.some _ _ h) := by
        rw [ne_comm, ← sub_ne_zero, ← sub_smul]
        push_cast
        simp only [add_sub_cancel_left, one_smul]
        exact Point.fromAffine_some_ne_zero h
      rw [Point.add_point, ih (n + 1) (by omega), ih (n + 1 + 1) (by omega), addMap_eq,
        add_of_not_equiv (by
          intro hequiv
          exact hne (Point.ext_iff.mpr ((ih (n + 1) (by omega)) ▸ (ih (n + 1 + 1) (by omega)) ▸
            Quotient.eq.mpr hequiv)))]
      have : (↑(n + 1 + 1) : ℤ) = ↑(n + 1) + 1 := by push_cast; omega
      rw [this, addXYZ_smulEval₁ h.1]
      congrm(⟦W.smulEval x y ↑(?_)⟧); omega
  | neg ih n =>
    simp_rw [_root_.neg_smul, Point.neg_point, ih n, eq_comm]
    refine Quotient.sound ⟨-1, ?_⟩
    simp_rw [← ringEval_comp_smulRing h.1, smulRing_neg,
      WeierstrassCurve.Jacobian.comp_smul, ← WeierstrassCurve.Jacobian.map_neg,
      curveRing_map_ringEval, map_neg, map_one]
    rfl

end

end ZSMul

section Coprimality

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- `evalEval` factors through the coordinate ring: if two bivariate polynomials
are equal in the coordinate ring, they have the same evaluation at any point
on the curve. -/
lemma evalEval_eq_of_mk_eq {x y : R} (heq : W.toAffine.Equation x y)
    {p q : R[X][Y]} (h : Affine.CoordinateRing.mk W p = Affine.CoordinateRing.mk W q) :
    p.evalEval x y = q.evalEval x y := by
  rw [AdjoinRoot.mk_eq_mk] at h
  obtain ⟨r, hr⟩ := h
  have key : (p - q).evalEval x y = 0 := by
    rw [hr, Polynomial.evalEval_mul]
    exact mul_eq_zero_of_left heq _
  rwa [Polynomial.evalEval_sub, sub_eq_zero] at key

/-- The square of `ψ_n` evaluates to `ΨSq_n(x)` at any point `(x,y)` on the curve. -/
lemma evalEval_ψ_sq {x y : R} (heq : W.toAffine.Equation x y) (n : ℤ) :
    (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := by
  have h1 : Affine.CoordinateRing.mk W (W.ψ n ^ 2) =
      Affine.CoordinateRing.mk W (C (W.ΨSq n)) := by
    rw [map_pow, Affine.CoordinateRing.mk_ψ, Affine.CoordinateRing.mk_Ψ_sq]
  rw [← evalEval_pow x y (W.ψ n) 2, ← evalEval_C x y (W.ΨSq n)]
  exact evalEval_eq_of_mk_eq W heq h1

/-- `φ_n` evaluates to `Φ_n(x)` at any point `(x,y)` on the curve. -/
lemma evalEval_φ_eq_Φ {x y : R} (heq : W.toAffine.Equation x y) (n : ℤ) :
    (W.φ n).evalEval x y = (W.Φ n).eval x := by
  rw [← evalEval_C x y (W.Φ n)]
  exact evalEval_eq_of_mk_eq W heq (Affine.CoordinateRing.mk_φ (W := W) n)

variable {F : Type*} [Field F] (W : WeierstrassCurve F) {n : ℤ}

/-- Over an algebraically closed field, every `x`-value lifts to a point on the curve. -/
lemma exists_point_on_curve [IsAlgClosed F] (a : F) :
    ∃ b : F, W.toAffine.Equation a b := by
  set c₁ := W.a₁ * a + W.a₃
  set c₀ := a ^ 3 + W.a₂ * a ^ 2 + W.a₄ * a + W.a₆
  set p : F[X] := X ^ 2 + C c₁ * X - C c₀ with hp_def
  have hcoeff : p.coeff 2 = 1 := by
    simp [hp_def, coeff_sub, coeff_add, coeff_X_pow]
  have hp0 : p ≠ 0 := fun h => by simp [h] at hcoeff
  have hnd : p.natDegree = 2 := by
    refine le_antisymm ?_ (le_natDegree_of_ne_zero (hcoeff ▸ one_ne_zero))
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · apply (natDegree_add_le _ _).trans
      apply max_le (natDegree_X_pow_le 2)
      exact natDegree_mul_le.trans (by simp [Polynomial.natDegree_C, natDegree_X])
    · exact (Polynomial.natDegree_C _).le.trans (by omega)
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_root p (by
    rw [degree_eq_natDegree hp0, hnd, Nat.cast_ofNat]; exact two_ne_zero)
  refine ⟨b, (W.toAffine.equation_iff a b).mpr ?_⟩
  rw [IsRoot.def] at hb
  simp only [hp_def, eval_sub, eval_add, eval_pow, eval_mul, eval_C, eval_X] at hb
  change b ^ 2 + W.a₁ * a * b + W.a₃ * b = a ^ 3 + W.a₂ * a ^ 2 + W.a₄ * a + W.a₆
  linear_combination hb

/-- The division polynomials `Φ_n` and `ΨSq_n` are coprime for a nonsingular
Weierstrass curve over a field (Sutherland Lemma 6.8, Silverman Exercise III.3.7).

The hypothesis `W.Δ ≠ 0` (i.e. the curve is nonsingular) is necessary: for the cusp
`Y² = X³` (with `Δ = 0`), `Φ₂ = X⁴` and `ΨSq₂ = 4X³` share the common factor `X³`. -/
theorem isCoprime_Φ_ΨSq (hΔ : W.Δ ≠ 0) (_hn : n ≠ 0) : IsCoprime (W.Φ n) (W.ΨSq n) := by
  let f := algebraMap F (AlgebraicClosure F)
  rw [← Polynomial.isCoprime_map f, ← map_Φ, ← map_ΨSq]
  set W' := W.map f with hW'
  rw [@Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed _ _
    (AlgebraicClosure F) _ _ (Algebra.id _)]
  intro a
  by_contra h
  push Not at h
  obtain ⟨hΦ, hΨ⟩ := h
  simp only [Polynomial.aeval_def] at hΦ hΨ
  obtain ⟨b, hb⟩ := exists_point_on_curve W' a
  have hΔ' : W'.Δ ≠ 0 := by rw [hW', map_Δ]; exact map_ne_zero_iff f f.injective |>.mpr hΔ
  have hns : W'.toAffine.Nonsingular a b :=
    (W'.toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ').mp hb
  have hψ_zero : (W'.ψ n).evalEval a b = 0 :=
    pow_eq_zero_iff two_ne_zero |>.mp ((evalEval_ψ_sq W' hb n).trans hΨ)
  have hφ_zero : (W'.φ n).evalEval a b = 0 := by rwa [evalEval_φ_eq_Φ W' hb n]
  have hZ : smulEval W' a b n 2 = 0 := by simp [smulEval, Function.comp, hψ_zero]
  have hX : smulEval W' a b n 0 = 0 := by simp [smulEval, Function.comp, hφ_zero]
  have hns_smul : Jacobian.Nonsingular W' (smulEval W' a b n) := by
    rw [← Jacobian.nonsingularLift_iff, ← zsmul_eq_smulEval W' hns n]
    exact (n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)).nonsingular
  exact Jacobian.X_ne_zero_of_Z_eq_zero hns_smul hZ hX

end Coprimality

section DegreeMultByN

variable {F : Type*} [Field F] (W : WeierstrassCurve F) {n : ℤ}

/-- The degree of the rational map `[n]` on x-coordinates is `n²` (Sutherland
Theorem 6.9): since `[n](x) = Φ_n(x) / ΨSq_n(x)` is in lowest terms by coprimality,
its degree is `max (natDegree Φ_n) (natDegree ΨSq_n) = n²`. -/
theorem degree_mulByN_eq_sq [Nontrivial F] :
    max (W.Φ n).natDegree (W.ΨSq n).natDegree = n.natAbs ^ 2 := by
  rw [W.natDegree_Φ n]
  exact max_eq_left ((W.natDegree_ΨSq_le n).trans (Nat.sub_le _ _))

end DegreeMultByN

end WeierstrassCurve

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!
# The Legendre normal form `y² = x(x−1)(x−λ)` (T-E14a)

**(T-E14a leaf (b), STREAM-OMEGA 2026-07-14; board: T-E14 continuation
decomposition.)** The Legendre family and the variable-change normalisation that
produces it: over a ring in which `2` is invertible, a Weierstrass curve with a chosen
pair of disjoint fibrewise-nonzero `2`-torsion points is carried by a unique-up-to-`±1`
variable change to `y² = x(x−1)(x−λ)` with the chosen points at `x = 0` and `x = 1`
(KM 4.6.2; GME Ex. 2.2.1 p. 117). Mirrors the point-based normalisation pattern of
`ForMathlib/TateNormalForm.lean` (`toTateNF`), with mathlib's
`WeierstrassCurve.toCharNeTwoNF` as step 1.

The residual `{±1}` (the `u`-ambiguity left after pinning `x(P) = 0`, `x(Q) = 1`) is
exactly the `ω`-factor of KM's engine axiom 2 — `negVC` with `u = −1`
(`EllipticCurve/InvariantDifferential.lean`, T-OM-B8/B9).
-/

universe u

namespace ModularCurves

open WeierstrassCurve

variable {R : Type u} [CommRing R]

/-- **(T-E14a)** The Legendre Weierstrass curve `y² = x(x−1)(x−λ)`:
`a₂ = −(λ+1)`, `a₄ = λ`, `a₁ = a₃ = a₆ = 0`. -/
def legendreCurve (lam : R) : WeierstrassCurve R :=
  ⟨0, -(lam + 1), 0, lam, 0⟩

@[simp] theorem legendreCurve_a₁ (lam : R) : (legendreCurve lam).a₁ = 0 := rfl
@[simp] theorem legendreCurve_a₂ (lam : R) : (legendreCurve lam).a₂ = -(lam + 1) := rfl
@[simp] theorem legendreCurve_a₃ (lam : R) : (legendreCurve lam).a₃ = 0 := rfl
@[simp] theorem legendreCurve_a₄ (lam : R) : (legendreCurve lam).a₄ = lam := rfl
@[simp] theorem legendreCurve_a₆ (lam : R) : (legendreCurve lam).a₆ = 0 := rfl

/-- **(T-E14a)** The discriminant of the Legendre curve is `16 λ² (λ−1)²`. -/
theorem legendreCurve_Δ (lam : R) :
    (legendreCurve lam).Δ = 16 * lam ^ 2 * (lam - 1) ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, legendreCurve_a₁, legendreCurve_a₂,
    legendreCurve_a₃, legendreCurve_a₄, legendreCurve_a₆]
  ring

/-- **(T-E14a)** Over a base with `2` invertible, the Legendre curve is elliptic iff
`λ(λ−1)` is a unit. -/
theorem legendreCurve_isElliptic_iff (h2 : IsUnit (2 : R)) (lam : R) :
    (legendreCurve lam).IsElliptic ↔ IsUnit (lam * (lam - 1)) := by
  rw [WeierstrassCurve.isElliptic_iff, legendreCurve_Δ]
  constructor
  · intro h
    have h' : IsUnit ((16 : R) * (lam * (lam - 1)) ^ 2) := by
      rw [show (16 : R) * (lam * (lam - 1)) ^ 2 = 16 * lam ^ 2 * (lam - 1) ^ 2 by ring]
      exact h
    have h2t : IsUnit ((lam * (lam - 1)) ^ 2) := isUnit_of_mul_isUnit_right h'
    exact (isUnit_pow_iff (n := 2) (by norm_num)).mp h2t
  · intro h
    rw [show (16 : R) * lam ^ 2 * (lam - 1) ^ 2 = 2 ^ 4 * (lam * (lam - 1)) ^ 2 by ring]
    exact (h2.pow 4).mul (h.pow 2)

instance (lam : R) : (legendreCurve lam).IsCharNeTwoNF :=
  ⟨rfl, rfl⟩

/-- The Legendre family is natural in the base ring: coefficient-wise mapping. -/
theorem legendreCurve_map {R' : Type u} [CommRing R'] (f : R →+* R') (lam : R) :
    (legendreCurve lam).map f = legendreCurve (f lam) := by
  ext <;> simp [legendreCurve, WeierstrassCurve.map, map_neg, map_add, map_one]

/-- **(T-E14a-b0)** `(0, 0)` lies on the Legendre curve. -/
theorem legendreCurve_equation_zero (lam : R) :
    (legendreCurve lam).toAffine.Equation 0 0 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp

/-- **(T-E14a-b0)** `(1, 0)` lies on the Legendre curve. -/
theorem legendreCurve_equation_one (lam : R) :
    (legendreCurve lam).toAffine.Equation 1 0 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  show (0:R) ^ 2 + (legendreCurve lam).a₁ * 1 * 0 + (legendreCurve lam).a₃ * 0 =
    1 ^ 3 + (legendreCurve lam).a₂ * 1 ^ 2 + (legendreCurve lam).a₄ * 1 +
      (legendreCurve lam).a₆
  simp only [legendreCurve_a₁, legendreCurve_a₂, legendreCurve_a₃, legendreCurve_a₄,
    legendreCurve_a₆]
  ring

/-- **(T-E14a-b0)** `x = 0` is a `2`-torsion abscissa of the Legendre curve: the cubic
vanishes there. -/
theorem legendreCurve_cubic_zero (lam : R) :
    (0 : R) ^ 3 + (legendreCurve lam).a₂ * 0 ^ 2 + (legendreCurve lam).a₄ * 0 +
      (legendreCurve lam).a₆ = 0 := by
  simp

/-- **(T-E14a-b0)** `x = 1` is a `2`-torsion abscissa of the Legendre curve. -/
theorem legendreCurve_cubic_one (lam : R) :
    (1 : R) ^ 3 + (legendreCurve lam).a₂ * 1 ^ 2 + (legendreCurve lam).a₄ * 1 +
      (legendreCurve lam).a₆ = 0 := by
  simp only [legendreCurve_a₂, legendreCurve_a₄, legendreCurve_a₆]
  ring

/-- **(T-E14a-b1 ★, the KM 4.6.2 normalisation, existence)** A char-≠2-normal-form
curve (`a₁ = a₃ = 0`) whose cubic has the marked `2`-torsion abscissae `p` and `p + 1`
(the `x(P₂) = 0, x(Q₂) = 1`-locus shape after the `ω`-pinning of `u`) is carried by the
pure translation `x ↦ x + p` to the Legendre curve of `λ = −a₂ − 3p − 1`. No scaling is
needed — the `δ`-condition has already spent it; this is why KM's coupled problem is
rigid while the plain `Γ(2)`-naive one is not. -/
theorem translation_smul_eq_legendreCurve {W : WeierstrassCurve R}
    (h1 : W.a₁ = 0) (h3 : W.a₃ = 0) {p : R}
    (hp : p ^ 3 + W.a₂ * p ^ 2 + W.a₄ * p + W.a₆ = 0)
    (hq : (p + 1) ^ 3 + W.a₂ * (p + 1) ^ 2 + W.a₄ * (p + 1) + W.a₆ = 0) :
    (⟨1, p, 0, 0⟩ : VariableChange R) • W =
      legendreCurve (-W.a₂ - 3 * p - 1) := by
  ext
  · rw [WeierstrassCurve.variableChange_a₁, h1, legendreCurve_a₁]
    simp
  · rw [WeierstrassCurve.variableChange_a₂, h1, legendreCurve_a₂]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    ring
  · rw [WeierstrassCurve.variableChange_a₃, h1, h3, legendreCurve_a₃]
    simp
  · rw [WeierstrassCurve.variableChange_a₄, h1, h3, legendreCurve_a₄]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    linear_combination hq - hp
  · rw [WeierstrassCurve.variableChange_a₆, h1, h3, legendreCurve_a₆]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    linear_combination hp

/-- **(T-E14a-b2 ★, the KM 4.6.2 `{±1}`-rigidity)** A variable change carrying a
Legendre curve to a Legendre curve and fixing the two marked `2`-torsion abscissae
(`x' = u⁻²(x − r)` sends `0 ↦ 0` and `1 ↦ 1`) is `⟨u, 0, 0, 0⟩` with `u² = 1`, and the
`λ`-parameter is unchanged: the coupled problem has exactly the `{±1}`-ambiguity of
KM's engine group. -/
theorem legendreCurve_vc_marked (h2 : IsUnit (2 : R)) {C : VariableChange R}
    {lam lam' : R} (hC : C • legendreCurve lam = legendreCurve lam')
    (hP : ((C.u⁻¹ : Rˣ) : R) ^ 2 * (0 - C.r) = 0)
    (hQ : ((C.u⁻¹ : Rˣ) : R) ^ 2 * (1 - C.r) = 1) :
    C.r = 0 ∧ C.s = 0 ∧ C.t = 0 ∧ (C.u : R) ^ 2 = 1 ∧ lam' = lam := by
  have hu2 : ((C.u⁻¹ : Rˣ) : R) ^ 2 * (C.u : R) ^ 2 = 1 := by
    rw [← mul_pow, Units.inv_mul, one_pow]
  -- the marking pins `r = 0` and `u² = 1`
  have hr : C.r = 0 := by
    have h := hP
    rw [zero_sub, mul_neg, neg_eq_zero] at h
    calc C.r = (((C.u⁻¹ : Rˣ) : R) ^ 2 * (C.u : R) ^ 2) * C.r := by
          rw [hu2, one_mul]
      _ = (C.u : R) ^ 2 * (((C.u⁻¹ : Rˣ) : R) ^ 2 * C.r) := by ring
      _ = 0 := by rw [h, mul_zero]
  have hinv2 : ((C.u⁻¹ : Rˣ) : R) ^ 2 = 1 := by
    rw [← hQ, hr, sub_zero, mul_one]
  have huu : (C.u : R) ^ 2 = 1 := by
    have h := hu2
    rwa [hinv2, one_mul] at h
  -- the normal form pins `s = 0` and `t = 0`
  have ha₁ := congrArg WeierstrassCurve.a₁ hC
  rw [WeierstrassCurve.variableChange_a₁, legendreCurve_a₁, legendreCurve_a₁,
    zero_add] at ha₁
  have hs : C.s = 0 := by
    have h' := congrArg (fun x => (C.u : R) * x) ha₁
    simp only [← mul_assoc, Units.mul_inv, one_mul, mul_zero] at h'
    exact (h2.mul_right_eq_zero).mp h'
  have ha₃ := congrArg WeierstrassCurve.a₃ hC
  rw [WeierstrassCurve.variableChange_a₃, legendreCurve_a₃, legendreCurve_a₃,
    legendreCurve_a₁, mul_zero, add_zero, zero_add] at ha₃
  have ht : C.t = 0 := by
    have h' := congrArg (fun x => ((C.u : R) ^ 3) * x) ha₃
    simp only [← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul,
      mul_zero] at h'
    exact (h2.mul_right_eq_zero).mp h'
  -- the `a₄`-slot then transports `λ` by `u⁻⁴ = 1`
  have ha₄ := congrArg WeierstrassCurve.a₄ hC
  rw [WeierstrassCurve.variableChange_a₄, legendreCurve_a₄, legendreCurve_a₄,
    legendreCurve_a₃, legendreCurve_a₁, legendreCurve_a₂, hr, hs, ht] at ha₄
  have hlam : lam' = lam := by
    rw [← ha₄, show ((C.u⁻¹ : Rˣ) : R) ^ 4 = (((C.u⁻¹ : Rˣ) : R) ^ 2) ^ 2 from by
      ring, hinv2]
    ring
  exact ⟨hr, hs, ht, huu, hlam⟩

/-- **(T-G3a-SUB2a, the existence direction — Silverman AEC III.1 Prop 1.7(b))** A
char-≠2-normal-form curve (`a₁ = a₃ = 0`) whose cubic **splits** with roots `e₁, e₂, e₃`
is carried to Legendre form by the variable change `⟨u, e₁, 0, 0⟩`, for any unit `u`
with `u² = e₂ − e₁`: the roots become `0`, `1` and `λ = u⁻²(e₃ − e₁)`.

The splitting hypothesis is given by the three coefficient identities (Vieta); over an
algebraically closed field they hold for the roots of the cubic, and the square root `u`
exists there, which is Silverman's hypothesis "char ≠ 2 and `K` algebraically closed".
No division is used, so the statement holds over an arbitrary commutative ring. -/
theorem scale_translate_smul_eq_legendreCurve {W : WeierstrassCurve R}
    (h1 : W.a₁ = 0) (h3 : W.a₃ = 0) {e₁ e₂ e₃ : R} (u : Rˣ)
    (ha₂ : W.a₂ = -(e₁ + e₂ + e₃))
    (ha₄ : W.a₄ = e₁ * e₂ + e₁ * e₃ + e₂ * e₃)
    (ha₆ : W.a₆ = -(e₁ * e₂ * e₃))
    (hu : ((u : R)) ^ 2 = e₂ - e₁) :
    (⟨u, e₁, 0, 0⟩ : VariableChange R) • W =
      legendreCurve (((u⁻¹ : Rˣ) : R) ^ 2 * (e₃ - e₁)) := by
  have huinv : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := u.inv_mul
  have hsq : ((u⁻¹ : Rˣ) : R) ^ 2 * (e₂ - e₁) = 1 := by
    rw [← hu, ← mul_pow, huinv, one_pow]
  ext
  · rw [WeierstrassCurve.variableChange_a₁, h1, legendreCurve_a₁]
    simp
  · rw [WeierstrassCurve.variableChange_a₂, h1, legendreCurve_a₂, ha₂]
    simp only [mul_zero, sub_zero, zero_mul]
    linear_combination -hsq
  · rw [WeierstrassCurve.variableChange_a₃, h1, h3, legendreCurve_a₃]
    simp
  · rw [WeierstrassCurve.variableChange_a₄, h1, h3, legendreCurve_a₄, ha₂, ha₄]
    simp only [mul_zero, sub_zero, zero_mul, add_zero]
    linear_combination (((u⁻¹ : Rˣ) : R) ^ 2 * (e₃ - e₁)) * hsq
  · rw [WeierstrassCurve.variableChange_a₆, h1, h3, legendreCurve_a₆, ha₂, ha₄, ha₆]
    ring

/-- **(T-G3a-SUB2b, complete the square)** With `2` invertible, every Weierstrass curve
is carried to char-≠2 normal form (`a₁ = a₃ = 0`) by the variable change
`⟨1, 0, −a₁/2, −a₃/2⟩`. (Silverman AEC III.1: "if char K ≠ 2 we may complete the
square".) -/
theorem completeSquareVC_a₁ {W : WeierstrassCurve R} (h2 : IsUnit (2 : R)) :
    ((⟨1, 0, -(h2.unit⁻¹ : Rˣ) * W.a₁, -(h2.unit⁻¹ : Rˣ) * W.a₃⟩ :
      VariableChange R) • W).a₁ = 0 := by
  rw [WeierstrassCurve.variableChange_a₁]
  show (((1 : Rˣ)⁻¹ : Rˣ) : R) * (W.a₁ + 2 * (-((h2.unit⁻¹ : Rˣ) : R) * W.a₁)) = 0
  have h : (2 : R) * ((h2.unit⁻¹ : Rˣ) : R) = 1 := by
    simpa [mul_comm] using congrArg (Units.val) (h2.unit.inv_mul)
  simp only [inv_one, Units.val_one, one_mul]
  linear_combination (-W.a₁) * h

theorem completeSquareVC_a₃ {W : WeierstrassCurve R} (h2 : IsUnit (2 : R)) :
    ((⟨1, 0, -(h2.unit⁻¹ : Rˣ) * W.a₁, -(h2.unit⁻¹ : Rˣ) * W.a₃⟩ :
      VariableChange R) • W).a₃ = 0 := by
  rw [WeierstrassCurve.variableChange_a₃]
  show ((((1 : Rˣ)⁻¹ : Rˣ) : R)) ^ 3 *
    (W.a₃ + 0 * W.a₁ + 2 * (-((h2.unit⁻¹ : Rˣ) : R) * W.a₃)) = 0
  have h : (2 : R) * ((h2.unit⁻¹ : Rˣ) : R) = 1 := by
    simpa [mul_comm] using congrArg (Units.val) (h2.unit.inv_mul)
  simp only [inv_one, Units.val_one, one_pow, one_mul, zero_mul, add_zero]
  linear_combination (-W.a₃) * h

/-- **(T-G3a-SUB2, algebra level)** Composite of the two steps: complete the square,
then scale-and-translate. If, after completing the square, the cubic splits with roots
`e₁, e₂, e₃` and `e₂ − e₁` is the square of a unit, the curve is variable-change
equivalent to a Legendre curve. -/
theorem exists_variableChange_eq_legendreCurve {W : WeierstrassCurve R}
    (h2 : IsUnit (2 : R)) {e₁ e₂ e₃ : R} (u : Rˣ)
    (ha₂ : ((⟨1, 0, -(h2.unit⁻¹ : Rˣ) * W.a₁, -(h2.unit⁻¹ : Rˣ) * W.a₃⟩ :
      VariableChange R) • W).a₂ = -(e₁ + e₂ + e₃))
    (ha₄ : ((⟨1, 0, -(h2.unit⁻¹ : Rˣ) * W.a₁, -(h2.unit⁻¹ : Rˣ) * W.a₃⟩ :
      VariableChange R) • W).a₄ = e₁ * e₂ + e₁ * e₃ + e₂ * e₃)
    (ha₆ : ((⟨1, 0, -(h2.unit⁻¹ : Rˣ) * W.a₁, -(h2.unit⁻¹ : Rˣ) * W.a₃⟩ :
      VariableChange R) • W).a₆ = -(e₁ * e₂ * e₃))
    (hu : ((u : R)) ^ 2 = e₂ - e₁) :
    ∃ (C : VariableChange R) (lam : R), C • W = legendreCurve lam := by
  refine ⟨(⟨u, e₁, 0, 0⟩ : VariableChange R) *
    ⟨1, 0, -(h2.unit⁻¹ : Rˣ) * W.a₁, -(h2.unit⁻¹ : Rˣ) * W.a₃⟩,
    ((u⁻¹ : Rˣ) : R) ^ 2 * (e₃ - e₁), ?_⟩
  rw [mul_smul]
  exact scale_translate_smul_eq_legendreCurve (completeSquareVC_a₁ h2)
    (completeSquareVC_a₃ h2) u ha₂ ha₄ ha₆ hu

end ModularCurves

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Legendre normal form for elliptic curves

We prove that every elliptic curve over an algebraically closed field of characteristic ≠ 2
is isomorphic to a curve in Legendre form `Y² = X(X − 1)(X − l)` for some `l ∉ {0, 1}`.

## Main definitions

* `WeierstrassCurve.legendreCurve`: the Weierstrass curve `Y² = X(X − 1)(X − l)`.

## Main results

* `WeierstrassCurve.legendreCurve_Δ_ne_zero_iff`: the Legendre curve has `Δ ≠ 0`
  iff `l ≠ 0` and `l ≠ 1`.
* `WeierstrassCurve.exists_legendreCurve_iso`: every elliptic curve over an algebraically
  closed field of characteristic ≠ 2 is isomorphic to a Legendre curve (Silverman III.1.7).

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1.7
-/

open Polynomial WeierstrassCurve

namespace WeierstrassCurve

variable {F : Type*} [Field F]

/-! ### The Legendre curve -/

/-- The Legendre curve `Y² = X(X − 1)(X − l)`, expressed as a Weierstrass curve
`Y² = X³ − (1 + l)X² + lX`. -/
def legendreCurve (l : F) : WeierstrassCurve F :=
  { a₁ := 0, a₂ := -(1 + l), a₃ := 0, a₄ := l, a₆ := 0 }

@[simp]
theorem legendreCurve_a₁ (l : F) : (legendreCurve l).a₁ = 0 := rfl

@[simp]
theorem legendreCurve_a₂ (l : F) : (legendreCurve l).a₂ = -(1 + l) := rfl

@[simp]
theorem legendreCurve_a₃ (l : F) : (legendreCurve l).a₃ = 0 := rfl

@[simp]
theorem legendreCurve_a₄ (l : F) : (legendreCurve l).a₄ = l := rfl

@[simp]
theorem legendreCurve_a₆ (l : F) : (legendreCurve l).a₆ = 0 := rfl

instance legendreCurve_isCharNeTwoNF (l : F) : (legendreCurve l).IsCharNeTwoNF :=
  ⟨rfl, rfl⟩

/-- The discriminant of the Legendre curve `Y² = X(X − 1)(X − l)`. -/
theorem legendreCurve_Δ (l : F) :
    (legendreCurve l).Δ = 16 * l ^ 2 * (l - 1) ^ 2 := by
  simp only [Δ_of_isCharNeTwoNF, legendreCurve_a₂, legendreCurve_a₄, legendreCurve_a₆]
  ring

/-- The Legendre curve has `Δ ≠ 0` iff `l ≠ 0` and `l ≠ 1`. -/
theorem legendreCurve_Δ_ne_zero_iff [NeZero (2 : F)] (l : F) :
    (legendreCurve l).Δ ≠ 0 ↔ l ≠ 0 ∧ l ≠ 1 := by
  have h2 : (2 : F) ≠ 0 := NeZero.ne 2
  have h16 : (16 : F) ≠ 0 := by
    have : (16 : F) = 2 ^ 4 := by norm_num
    rw [this]; exact pow_ne_zero 4 h2
  rw [legendreCurve_Δ]
  constructor
  · intro h
    refine ⟨?_, ?_⟩ <;> rintro rfl <;> simp at h
  · rintro ⟨hl0, hl1⟩
    exact mul_ne_zero (mul_ne_zero h16 (pow_ne_zero 2 hl0))
      (pow_ne_zero 2 (sub_ne_zero.mpr hl1))

/-! ### Existence of Legendre form -/

section ExistsLegendre

variable [IsAlgClosed F] [NeZero (2 : F)]

omit [NeZero (2 : F)] in
/-- Helper: given a char ≠ 2 NF elliptic curve `Y² = X³ + a₂X² + a₄X` (with a₆ = 0),
produce a Legendre form. This is the core of the Legendre form construction. -/
private theorem exists_legendreCurve_of_charNeTwoNF_a₆_eq_zero
    (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharNeTwoNF] (ha₆ : W.a₆ = 0) :
    ∃ l : F, l ≠ 0 ∧ l ≠ 1 ∧
      ∃ C : VariableChange F, (C • W).IsElliptic ∧ C • W = legendreCurve l := by
  have hq_ne : (X ^ 2 + C W.a₂ * X + C W.a₄ : F[X]).degree ≠ 0 := by
    have hnd : (X ^ 2 + C W.a₂ * X + C W.a₄ : F[X]).natDegree = 2 := by compute_degree!
    have hne : (X ^ 2 + C W.a₂ * X + C W.a₄ : F[X]) ≠ 0 := fun heq => by
      simp [heq] at hnd
    rw [degree_eq_natDegree hne, hnd]; decide
  obtain ⟨e₂, he₂⟩ := IsAlgClosed.exists_root _ hq_ne
  simp only [IsRoot, eval_add, eval_mul, eval_pow, eval_X, eval_C] at he₂
  have he₂_ne : e₂ ≠ 0 := by
    intro he; subst he
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      add_zero, zero_add] at he₂
    exact W.isUnit_Δ.ne_zero (by rw [Δ_of_isCharNeTwoNF, ha₆, he₂]; ring)
  set e₃ := -W.a₂ - e₂
  have h_prod : W.a₄ = e₂ * e₃ := by
    change W.a₄ = e₂ * (-W.a₂ - e₂); linear_combination he₂
  have h_sum : W.a₂ = -(e₂ + e₃) := by
    change W.a₂ = -(e₂ + (-W.a₂ - e₂)); ring
  have he₃_ne : e₃ ≠ 0 := by
    intro he; rw [he, mul_zero] at h_prod
    exact W.isUnit_Δ.ne_zero (by rw [Δ_of_isCharNeTwoNF, ha₆, h_prod]; ring)
  have he₂₃ : e₂ ≠ e₃ := by
    intro heq; rw [heq] at h_prod h_sum
    exact W.isUnit_Δ.ne_zero (by rw [Δ_of_isCharNeTwoNF, ha₆, h_prod, h_sum]; ring)
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_eq_mul_self e₂
  have hu_ne : u ≠ 0 := by rintro rfl; exact he₂_ne (by simpa using hu)
  have hu_sq : u * u = e₂ := hu.symm
  have hu_inv_sq : u⁻¹ * u⁻¹ = e₂⁻¹ := by rw [← mul_inv, hu_sq]
  set uU := Units.mk0 u hu_ne
  set C₂ : VariableChange F := ⟨uU, 0, 0, 0⟩
  set l := e₃ * e₂⁻¹
  have ha₁ := IsCharNeTwoNF.a₁ (W := W)
  have ha₃ := IsCharNeTwoNF.a₃ (W := W)
  have huinv : ((uU : F))⁻¹ = u⁻¹ := rfl
  have hW₂_eq : C₂ • W = legendreCurve l := by
    ext
    · change (uU : F)⁻¹ * (W.a₁ + 2 * (0 : F)) = 0
      rw [ha₁]; ring
    · change (uU : F)⁻¹ ^ 2 * (W.a₂ - 0 * W.a₁ + 3 * (0 : F) - 0 ^ 2) = -(1 + e₃ * e₂⁻¹)
      rw [ha₁]; ring_nf
      rw [huinv, show u⁻¹ ^ 2 = u⁻¹ * u⁻¹ from sq u⁻¹, hu_inv_sq, h_sum]
      field_simp; ring
    · change (uU : F)⁻¹ ^ 3 * (W.a₃ + 0 * W.a₁ + 2 * (0 : F)) = 0
      rw [ha₃]; ring
    · change (uU : F)⁻¹ ^ 4 * (W.a₄ - 0 * W.a₃ + 2 * 0 * W.a₂ -
        (0 + 0 * (0 : F)) * W.a₁ + 3 * 0 ^ 2 - 2 * 0 * 0) = e₃ * e₂⁻¹
      rw [ha₁, ha₃]; ring_nf
      rw [huinv, show u⁻¹ ^ 4 = (u⁻¹ * u⁻¹) ^ 2 from by ring, hu_inv_sq, h_prod]
      field_simp
    · change (uU : F)⁻¹ ^ 6 * (W.a₆ + 0 * W.a₄ + 0 ^ 2 * W.a₂ + 0 ^ 3 -
        0 * W.a₃ - 0 ^ 2 - 0 * (0 : F) * W.a₁) = 0
      rw [ha₆]; ring
  have hl_ne_zero : l ≠ 0 := mul_ne_zero he₃_ne (inv_ne_zero he₂_ne)
  have hl_ne_one : l ≠ 1 := by
    change e₃ * e₂⁻¹ ≠ 1
    rwa [Ne, mul_inv_eq_one₀ he₂_ne, eq_comm]
  have hW₂_ell : (C₂ • W).IsElliptic := by
    rw [isElliptic_iff, variableChange_Δ]
    exact (C₂.u⁻¹.isUnit.pow 12).mul W.isUnit_Δ
  exact ⟨l, hl_ne_zero, hl_ne_one, C₂, hW₂_ell, hW₂_eq⟩

/-- Every elliptic curve over an algebraically closed field of characteristic ≠ 2 is
isomorphic to a Legendre curve `Y² = X(X − 1)(X − l)`.

**Proof sketch** (Silverman III.1.7):
1. Put E in char ≠ 2 normal form: `Y² = X³ + aX² + bX + c`.
2. The RHS has a root `e₁` over the algebraically closed field.
3. Translate `X ↦ X + e₁` to get `Y² = X³ + a'X² + b'X` (constant term vanishes).
4. Apply the helper lemma to get Legendre form. -/
theorem exists_legendreCurve_iso
    (E : WeierstrassCurve F) [E.IsElliptic] :
    ∃ l : F, l ≠ 0 ∧ l ≠ 1 ∧
      ∃ C : VariableChange F, (C • E).IsElliptic ∧ C • E = legendreCurve l := by
  have h2inv : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne 2)
  set W := E.toCharNeTwoNF • E
  have hW_nf : W.IsCharNeTwoNF := E.toCharNeTwoNF_spec
  have hW_ell : W.IsElliptic := by
    rw [isElliptic_iff, variableChange_Δ]
    exact (E.toCharNeTwoNF.u⁻¹.isUnit.pow 12).mul E.isUnit_Δ
  have hp_ne : (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ : F[X]).degree ≠ 0 := by
    have hnd : (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ : F[X]).natDegree = 3 := by
      compute_degree!
    have hne : (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆ : F[X]) ≠ 0 := fun heq => by
      simp [heq] at hnd
    rw [degree_eq_natDegree hne, hnd]; decide
  obtain ⟨e₁, he₁⟩ := IsAlgClosed.exists_root _ hp_ne
  simp only [IsRoot, eval_add, eval_mul, eval_pow, eval_X, eval_C] at he₁
  have ha₁W := hW_nf.a₁
  have ha₃W := hW_nf.a₃
  have hW₁_a₆ : ((⟨1, e₁, 0, 0⟩ : VariableChange F) • W).a₆ = 0 := by
    simp only [variableChange_def]
    have : (⟨1, e₁, 0, 0⟩ : VariableChange F).u = (1 : Fˣ) := rfl
    have : (⟨1, e₁, 0, 0⟩ : VariableChange F).r = e₁ := rfl
    have : (⟨1, e₁, 0, 0⟩ : VariableChange F).s = (0 : F) := rfl
    have : (⟨1, e₁, 0, 0⟩ : VariableChange F).t = (0 : F) := rfl
    simp_all; linear_combination he₁
  have hW₁_nf : ((⟨1, e₁, 0, 0⟩ : VariableChange F) • W).IsCharNeTwoNF := by
    refine ⟨?_, ?_⟩
    · simp only [variableChange_def]; ring_nf; rw [ha₁W]; ring
    · simp only [variableChange_def]; ring_nf; rw [ha₁W, ha₃W]; ring
  have hW₁_ell : ((⟨1, e₁, 0, 0⟩ : VariableChange F) • W).IsElliptic := by
    rw [isElliptic_iff, variableChange_Δ]
    exact ((⟨1, e₁, 0, 0⟩ : VariableChange F).u⁻¹.isUnit.pow 12).mul hW_ell.isUnit
  obtain ⟨l, hl0, hl1, C₂, hC₂_ell, hC₂_eq⟩ :=
    exists_legendreCurve_of_charNeTwoNF_a₆_eq_zero
      ((⟨1, e₁, 0, 0⟩ : VariableChange F) • W) hW₁_a₆
  exact ⟨l, hl0, hl1, C₂ * ⟨1, e₁, 0, 0⟩ * E.toCharNeTwoNF,
    by simp only [mul_smul]; exact hC₂_ell,
    by simp only [mul_smul]; exact hC₂_eq⟩

end ExistsLegendre

end WeierstrassCurve

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# The kernel of a rank-two system is spanned by the cross product

Cramer over an arbitrary commutative ring: if the cross product `v ⨯₃ w` is
unimodular (its coordinates generate the unit ideal), then a vector annihilated by
both dot products `v ⬝ᵥ ·` and `w ⬝ᵥ ·` is a multiple of `v ⨯₃ w`. No localization,
no splitting theory — the chord-and-tangent line of [GAP-A-4] is this vector.
-/

namespace ModularCurves

open Matrix

variable {R : Type*} [CommRing R]

/-- A vector whose cross product with a unimodular vector vanishes lies in the span
of that vector: Cramer coordinates `u = (∑ aᵢuᵢ) • c` from `∑ aᵢcᵢ = 1` and the
minor relations `cᵢuⱼ = cⱼuᵢ`. -/
theorem mem_span_singleton_of_crossProduct_eq_zero (c u : Fin 3 → R)
    (hc : Ideal.span (Set.range c) = ⊤)
    (h : c ⨯₃ u = 0) :
    u ∈ Submodule.span R {c} := by
  have h1 : (1 : R) ∈ Ideal.span (Set.range c) := by rw [hc]; trivial
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp h1
  have h0 := congrFun h 0
  have h1' := congrFun h 1
  have h2 := congrFun h 2
  rw [cross_apply] at h0 h1' h2
  have e12 : c 1 * u 2 = c 2 * u 1 := by
    have hz : c 1 * u 2 - c 2 * u 1 = 0 := by simpa using h0
    exact sub_eq_zero.mp hz
  have e20 : c 2 * u 0 = c 0 * u 2 := by
    have hz : c 2 * u 0 - c 0 * u 2 = 0 := by simpa using h1'
    exact sub_eq_zero.mp hz
  have e01 : c 0 * u 1 = c 1 * u 0 := by
    have hz : c 0 * u 1 - c 1 * u 0 = 0 := by simpa using h2
    exact sub_eq_zero.mp hz
  have hrel : ∀ i j, c i * u j = c j * u i := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | exact e12
        | exact e12.symm
        | exact e20
        | exact e20.symm
        | exact e01
        | exact e01.symm
  refine Submodule.mem_span_singleton.mpr ⟨∑ i, a i * u i, ?_⟩
  funext j
  simp only [Pi.smul_apply, smul_eq_mul]
  calc (∑ i, a i * u i) * c j
      = ∑ i, a i * u i * c j := by rw [Finset.sum_mul]
    _ = ∑ i, a i * (c i * u j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, mul_comm (u i) (c j), hrel j i]
    _ = (∑ i, a i * c i) * u j := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
    _ = u j := by
        have ha' : (∑ i, a i * c i) = 1 := by
          simpa [smul_eq_mul] using ha
        rw [ha', one_mul]

/-- **The kernel of a rank-two dot-product system is spanned by the cross product**
when the cross product is unimodular: BAC-CAB collapses `(v ⨯₃ w) ⨯₃ u` to zero
under the two annihilations, and the unimodular-cross span lemma finishes. -/
theorem mem_span_crossProduct_of_dotProduct_eq_zero (v w u : Fin 3 → R)
    (hc : Ideal.span (Set.range (v ⨯₃ w)) = ⊤)
    (hv : v ⬝ᵥ u = 0) (hw : w ⬝ᵥ u = 0) :
    u ∈ Submodule.span R {(v ⨯₃ w : Fin 3 → R)} := by
  refine mem_span_singleton_of_crossProduct_eq_zero _ _ hc ?_
  have h := cross_cross_eq_smul_sub_smul v w u
  rw [hv, hw] at h
  simpa using h

/-- The reverse containment: the cross product is annihilated by both rows, so the
span it generates lies in the kernel — with the previous theorem, equality. -/
theorem span_crossProduct_le_ker (v w : Fin 3 → R) (u : Fin 3 → R)
    (hu : u ∈ Submodule.span R {(v ⨯₃ w : Fin 3 → R)}) :
    v ⬝ᵥ u = 0 ∧ w ⬝ᵥ u = 0 := by
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hu
  constructor
  · rw [dotProduct_smul, dot_self_cross, smul_zero]
  · rw [dotProduct_smul, dot_cross_self, smul_zero]

/-- The two-dimensional Cramer analogue for the vertical: the kernel of a single
unimodular row `a` is spanned by its perpendicular `![-(a 1), a 0]`. -/
theorem mem_span_perp_of_dotProduct_eq_zero (a u : Fin 2 → R)
    (ha : Ideal.span (Set.range a) = ⊤)
    (h : a ⬝ᵥ u = 0) :
    u ∈ Submodule.span R {![-(a 1), a 0]} := by
  have h1 : (1 : R) ∈ Ideal.span (Set.range a) := by rw [ha]; trivial
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp h1
  have hb' : b 0 * a 0 + b 1 * a 1 = 1 := by
    simpa [Fin.sum_univ_two, smul_eq_mul] using hb
  have hdot : a 0 * u 0 + a 1 * u 1 = 0 := by
    simpa [dotProduct, Fin.sum_univ_two] using h
  refine Submodule.mem_span_singleton.mpr ⟨b 0 * u 1 - b 1 * u 0, ?_⟩
  funext j
  fin_cases j
  · show (b 0 * u 1 - b 1 * u 0) * (-(a 1)) = u 0
    have : (b 0 * u 1 - b 1 * u 0) * (-(a 1)) - u 0 =
        (b 0 * (-(a 0 * u 0 + a 1 * u 1)) +
          (b 0 * a 0 + b 1 * a 1 - 1) * u 0) := by ring
    have hz : (b 0 * u 1 - b 1 * u 0) * (-(a 1)) - u 0 = 0 := by
      rw [this, hdot, hb']
      ring
    exact sub_eq_zero.mp hz
  · show (b 0 * u 1 - b 1 * u 0) * a 0 = u 1
    have : (b 0 * u 1 - b 1 * u 0) * a 0 - u 1 =
        (b 1 * (-(a 0 * u 0 + a 1 * u 1)) +
          (b 0 * a 0 + b 1 * a 1 - 1) * u 1) := by ring
    have hz : (b 0 * u 1 - b 1 * u 0) * a 0 - u 1 = 0 := by
      rw [this, hdot, hb']
      ring
    exact sub_eq_zero.mp hz

/-- **Surjectivity makes the cross product unimodular** (Binet–Cauchy): if the two
dot-product rows `v, w` jointly surject onto `R²`, then preimages `n₀, n₁` of the
standard basis give `(v ⨯₃ w) ⬝ᵥ (n₀ ⨯₃ n₁) = det I₂ = 1`, so the coordinates of the
cross product generate the unit ideal. This discharges the unimodularity hypothesis of
`mem_span_crossProduct_of_dotProduct_eq_zero` from cohomological surjectivity alone —
no evaluation-matrix minors are ever computed. -/
theorem span_range_crossProduct_eq_top_of_surjective (v w : Fin 3 → R)
    (hsurj : ∀ y : Fin 2 → R, ∃ u : Fin 3 → R, v ⬝ᵥ u = y 0 ∧ w ⬝ᵥ u = y 1) :
    Ideal.span (Set.range (v ⨯₃ w)) = ⊤ := by
  obtain ⟨n₀, hv₀, hw₀⟩ := hsurj ![1, 0]
  obtain ⟨n₁, hv₁, hw₁⟩ := hsurj ![0, 1]
  have hbc2 : (v ⨯₃ w) ⬝ᵥ (n₀ ⨯₃ n₁) = 1 := by
    have h := cross_dot_cross v w n₀ n₁
    rw [show v ⬝ᵥ n₀ = 1 from by simpa using hv₀,
      show w ⬝ᵥ n₁ = 1 from by simpa using hw₁,
      show v ⬝ᵥ n₁ = 0 from by simpa using hv₁,
      show w ⬝ᵥ n₀ = 0 from by simpa using hw₀] at h
    rw [h]
    ring
  rw [Ideal.eq_top_iff_one]
  rw [show (1 : R) = (v ⨯₃ w) ⬝ᵥ (n₀ ⨯₃ n₁) from hbc2.symm]
  rw [dotProduct]
  exact Submodule.sum_mem _ fun i _ =>
    Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- **The converse of `span_range_crossProduct_eq_top_of_surjective`**: a unimodular
cross product makes the two-row system surjective. With `a ⬝ᵥ (v ⨯₃ w) = 1`, the vector
`-y₀ • (a ⨯₃ w) - y₁ • (v ⨯₃ a)` has prescribed dot products. -/
theorem surjective_of_span_range_crossProduct_eq_top (v w : Fin 3 → R)
    (hc : Ideal.span (Set.range (v ⨯₃ w)) = ⊤) :
    ∀ y : Fin 2 → R, ∃ u : Fin 3 → R, v ⬝ᵥ u = y 0 ∧ w ⬝ᵥ u = y 1 := by
  intro y
  have h1 : (1 : R) ∈ Ideal.span (Set.range (v ⨯₃ w)) := by rw [hc]; trivial
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp h1
  have hca : (v ⨯₃ w) ⬝ᵥ a = 1 := by
    rw [dotProduct]
    simpa [smul_eq_mul, mul_comm] using ha
  refine ⟨-(y 0) • (a ⨯₃ w) - (y 1) • (v ⨯₃ a), ?_, ?_⟩
  · have hv1 : v ⬝ᵥ (a ⨯₃ w) = -((v ⨯₃ w) ⬝ᵥ a) := by
      simp only [cross_apply, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring
    have hv2 : v ⬝ᵥ (v ⨯₃ a) = 0 := by
      simp only [cross_apply, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring
    rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, hv1, hv2, hca]
    simp [smul_eq_mul]
  · have hw1 : w ⬝ᵥ (a ⨯₃ w) = 0 := by
      simp only [cross_apply, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring
    have hw2 : w ⬝ᵥ (v ⨯₃ a) = -((v ⨯₃ w) ⬝ᵥ a) := by
      simp only [cross_apply, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring
    rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, hw1, hw2, hca]
    simp [smul_eq_mul]

/-- The rank-one analogue: a surjective single row is unimodular. -/
theorem span_range_eq_top_of_surjective (a : Fin 2 → R)
    (hsurj : ∀ y : R, ∃ u : Fin 2 → R, a ⬝ᵥ u = y) :
    Ideal.span (Set.range a) = ⊤ := by
  obtain ⟨u, hu⟩ := hsurj 1
  rw [Ideal.eq_top_iff_one, show (1 : R) = a ⬝ᵥ u from hu.symm, dotProduct]
  exact Submodule.sum_mem _ fun i _ =>
    Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- The perpendicular is annihilated by the row. -/
theorem dotProduct_perp (a : Fin 2 → R) :
    a ⬝ᵥ ![-(a 1), a 0] = 0 := by
  simp [dotProduct, Fin.sum_univ_two]
  ring

section RankThree

open Matrix

/-- **A vector annihilated by a matrix with unit determinant is zero.** The adjugate
identity turns `A *ᵥ u = 0` into `det A • u = 0`. -/
theorem eq_zero_of_mulVec_eq_zero_of_isUnit_det {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (hdet : IsUnit A.det) (u : n → R) (hu : A *ᵥ u = 0) : u = 0 := by
  have h1 : (Matrix.adjugate A) *ᵥ (A *ᵥ u) = 0 := by rw [hu, Matrix.mulVec_zero]
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec] at h1
  obtain ⟨d, hd⟩ := hdet
  funext i
  have h2 := congrFun h1 i
  have h3 : A.det * u i = 0 := by
    simpa [Pi.smul_apply, smul_eq_mul] using h2
  have h4 : (↑d⁻¹ : R) * (A.det * u i) = 0 := by rw [h3, mul_zero]
  rw [← mul_assoc, ← hd, Units.inv_mul, one_mul] at h4
  exact h4

/-- **The determinant of a system with a nonzero-kernel element is a zero divisor.**
Contrapositive form of `eq_zero_of_mulVec_eq_zero_of_isUnit_det`: if some nonzero vector
is annihilated, the determinant cannot be a unit — the rank-drop criterion feeding the
exact-order argument. -/
theorem not_isUnit_det_of_mulVec_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (u : n → R) (hu : A *ᵥ u = 0) (hne : u ≠ 0) :
    ¬ IsUnit A.det :=
  fun hdet => hne (eq_zero_of_mulVec_eq_zero_of_isUnit_det A hdet u hu)

/-- **The unit half, in Cramer form.** If a `3 × 3` system has unit determinant then it
is surjective — the companion of `eq_zero_of_mulVec_eq_zero_of_isUnit_det`, giving the
exactness of the order from non-degeneracy of the evaluation matrix. -/
theorem surjective_mulVec_of_isUnit_det {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (hdet : IsUnit A.det) (b : n → R) :
    ∃ u : n → R, A *ᵥ u = b := by
  obtain ⟨d, hd⟩ := hdet
  refine ⟨(↑d⁻¹ : R) • (Matrix.adjugate A *ᵥ b), ?_⟩
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_adjugate]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, ← hd, Units.inv_mul, one_smul]

end RankThree

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Equal principal spans give associates, for a nonzerodivisor.** The bridge
from the span-level identification of the chart multiplier
(`span_iteratedChartMultiplier₃_eq`) to the unit-level hypothesis of the trivialization
criterion. -/
theorem exists_unit_mul_of_span_eq {A : Type*} [CommRing A] (a b : A)
    (hspan : Ideal.span {a} = Ideal.span {b})
    (hnzd : ∀ t : A, a * t = 0 → t = 0) :
    ∃ u : Aˣ, a = (u : A) * b := by
  have hab : a ∈ Ideal.span {b} := by
    rw [← hspan]; exact Ideal.mem_span_singleton_self a
  have hba : b ∈ Ideal.span {a} := by
    rw [hspan]; exact Ideal.mem_span_singleton_self b
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hab
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hba
  have hcd : a * (1 - c * d) = 0 := by
    have h : c * (d * a) = a := by rw [hd, hc]
    calc a * (1 - c * d) = a - c * (d * a) := by ring
      _ = a - a := by rw [h]
      _ = 0 := sub_self a
  have hone : (1 : A) - c * d = 0 := hnzd _ hcd
  have hcd1 : c * d = 1 := by
    have := sub_eq_zero.mp hone
    exact this.symm
  refine ⟨⟨c, d, hcd1, by rw [mul_comm]; exact hcd1⟩, ?_⟩
  show a = c * b
  rw [← hc, mul_comm]

/-- **Two unit multiples of the same element differ by a unit.** The final glue of the
exact-order argument: the chord's coefficient and the twist's multiplier are both unit
multiples of the generator product, hence unit multiples of each other. -/
theorem exists_unit_mul_of_both_unit_mul {A : Type*} [CommRing A] (a b p : A)
    (u v : Aˣ) (ha : a = (u : A) * p) (hb : b = (v : A) * p) :
    ∃ w : Aˣ, a = (w : A) * b := by
  refine ⟨u * v⁻¹, ?_⟩
  rw [ha, hb]
  show (u : A) * p = ((u * v⁻¹ : Aˣ) : A) * ((v : A) * p)
  push_cast
  rw [mul_assoc, ← mul_assoc (↑v⁻¹ : A) (v : A) p]
  rw [show (↑v⁻¹ : A) * (v : A) = 1 from v.inv_mul]
  rw [one_mul]

end ModularCurves

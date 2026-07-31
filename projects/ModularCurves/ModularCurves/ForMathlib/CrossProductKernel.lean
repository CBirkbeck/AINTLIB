/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.RingTheory.Ideal.Span

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

end ModularCurves

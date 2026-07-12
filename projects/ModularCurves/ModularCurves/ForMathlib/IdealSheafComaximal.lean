/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# Product equals intersection for pairwise-comaximal ideal sheaves (YFULL route γ)

For a finite family of ideal-sheaf data `I : ι → X.IdealSheafData` that is pairwise
comaximal (`I i ⊔ I j = ⊤` for `i ≠ j`), the product equals the intersection:
`∏ i ∈ s, I i = ⨅ i ∈ s, I i`. This is checked affine-locally, where it is the classical
`Ideal.prod_eq_iInf_of_pairwise_isCoprime`.

This is the comaximality half of the `Y(N)` full-level `⊇` step: over the locus where the
`N²` torsion sections `[a]P + [b]Q` are pairwise disjoint, their kernel ideal sheaves are
pairwise comaximal, so the section divisor's ideal `∏ ker` equals `⋂ ker`.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- Evaluation of an ideal sheaf at an affine open, as a monoid homomorphism to the ideal
lattice under multiplication. -/
@[simps] def idealAt (U : X.affineOpens) : X.IdealSheafData →* Ideal Γ(X, U) where
  toFun I := I.ideal U
  map_one' := by
    show (1 : X.IdealSheafData).ideal U = 1
    rw [Ideal.one_eq_top]; exact congrFun ideal_top U
  map_mul' a b := by
    show (a * b).ideal U = a.ideal U * b.ideal U
    exact congrFun (ideal_mul (I := a) (J := b)) U

/-- **Comaximal ⟹ product = intersection for ideal sheaves.** A pairwise-comaximal finite
family of ideal-sheaf data has product equal to intersection. -/
theorem prod_eq_biInf_of_pairwise_sup_eq_top {ι : Type*} (s : Finset ι)
    (I : ι → X.IdealSheafData)
    (h : (s : Set ι).Pairwise (fun i j => I i ⊔ I j = ⊤)) :
    ∏ i ∈ s, I i = ⨅ i ∈ s, I i := by
  refine IdealSheafData.ext (funext fun U => ?_)
  have hprod := map_prod (idealAt U) I s
  simp only [idealAt_apply] at hprod
  have hinf : (⨅ i ∈ s, I i).ideal U = ⨅ i ∈ s, (I i).ideal U := by
    have h2 := congrFun (ideal_biInf I (s := (s : Set ι)) s.finite_toSet) U
    simpa using h2
  rw [hprod, hinf]
  refine Ideal.prod_eq_iInf_of_pairwise_isCoprime ?_
  intro i hi j hj hij
  have hsup : (I i).ideal U ⊔ (I j).ideal U = ⊤ := by
    have h3 := congrFun (congrArg ideal (h hi hj hij)) U
    rw [ideal_sup] at h3
    simpa using h3
  exact (Ideal.isCoprime_iff_sup_eq).mpr hsup

end AlgebraicGeometry.Scheme.IdealSheafData

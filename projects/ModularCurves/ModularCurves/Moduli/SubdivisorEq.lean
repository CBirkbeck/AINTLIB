/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.ForMathlib.ClosedImmersionFinrankIso
import ModularCurves.LevelStructure.Incidence

/-!
# A subdivisor of equal degree is the whole divisor (YFULL route γ, [YF-SUBDIV-EQ])

If `D'` is a subdivisor of a relative effective Cartier divisor `D` (`IsSubdivisor D' D`)
and they have the same degree at every point of the base, then `D' = D`. The subscheme
inclusion `j : D'.subscheme ⟶ D.subscheme` is a closed immersion between two finite locally
free `S`-schemes of equal rank, hence an isomorphism
(`isIso_of_isClosedImmersion_of_finrank_eq`); equal kernels then give equal ideal sheaves.

This is the same-degree-divisor-equality step of the `Y(N)` full-level `⊇` argument: over
the disjoint locus the section divisor is a subdivisor of `E[N]` of the same degree `N²`,
hence equals it.
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace ModularCurves

theorem RelEffCartierDiv.eq_of_isSubdivisor_of_degree_eq {C S : Scheme.{u}} {π : C ⟶ S}
    (D' D : RelEffCartierDiv π) (hsub : IsSubdivisor D' D)
    (hdeg : ∀ s, D'.degree s = D.degree s) : D' = D := by
  obtain ⟨j, hj⟩ := hsub
  haveI := D.finite; haveI := D.flat; haveI := D.lfp
  haveI := D'.finite; haveI := D'.flat; haveI := D'.lfp
  haveI hjci : IsClosedImmersion j := by
    haveI : IsClosedImmersion (j ≫ D.ideal.subschemeι) := by rw [hj]; infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion j D.ideal.subschemeι
  have hjg : j ≫ (D.ideal.subschemeι ≫ π) = D'.ideal.subschemeι ≫ π := by
    rw [← Category.assoc, hj]
  haveI : IsFinite (j ≫ (D.ideal.subschemeι ≫ π)) := by rw [hjg]; exact D'.finite
  haveI : Flat (j ≫ (D.ideal.subschemeι ≫ π)) := by rw [hjg]; exact D'.flat
  haveI : LocallyOfFinitePresentation (j ≫ (D.ideal.subschemeι ≫ π)) := by
    rw [hjg]; exact D'.lfp
  haveI : IsIso j :=
    isIso_of_isClosedImmersion_of_finrank_eq (D.ideal.subschemeι ≫ π) j (by
      intro s
      rw [show (j ≫ (D.ideal.subschemeι ≫ π)) = D'.ideal.subschemeι ≫ π from hjg]
      exact hdeg s)
  refine RelEffCartierDiv.ext ?_
  have h1 : D'.ideal = (j ≫ D.ideal.subschemeι).ker := by
    rw [hj, Scheme.IdealSheafData.ker_subschemeι]
  rw [h1, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

end ModularCurves

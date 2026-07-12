/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.LevelStructure.Incidence

/-!
# Same-degree subdivisor equality ([YF-⊇] sub-lemma ii)

A relative effective Cartier divisor `D'` that is a subdivisor of `D` and has the same fibrewise
degree everywhere is equal to `D`. This is KM 1.2's "an inclusion of finite locally free
`S`-schemes of the same rank is an isomorphism", read through the divisor↔ideal dictionary:
`IsSubdivisor D' D` gives a closed immersion `j : D'.subscheme ⟶ D.subscheme`, equal degree makes
its kernel ideal trivial (a surjection of finite locally free modules of equal rank is injective),
hence `j` is an isomorphism and the two ideals coincide (`RelEffCartierDiv.ext`).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace RelEffCartierDiv

variable {C S : Scheme.{u}} {π : C ⟶ S}

/-- The factorising morphism of a subdivisor is a closed immersion: `D'.subschemeι` factors as
`j ≫ D.subschemeι` with both `subschemeι` closed immersions, so `j` is one. -/
theorem isClosedImmersion_isSubdivisor_hom (D' D : RelEffCartierDiv π)
    (j : D'.ideal.subscheme ⟶ D.ideal.subscheme)
    (hj : j ≫ D.ideal.subschemeι = D'.ideal.subschemeι) : IsClosedImmersion j := by
  haveI : IsClosedImmersion (j ≫ D.ideal.subschemeι) := hj ▸ inferInstance
  exact IsClosedImmersion.of_comp j D.ideal.subschemeι

/-- **[YF-⊇](ii)** A subdivisor of the same fibrewise degree is equal: `IsSubdivisor D' D` and
`D'.degree = D.degree` (everywhere) force `D' = D`. -/
theorem eq_of_isSubdivisor_of_degree_eq (D' D : RelEffCartierDiv π)
    (hsub : IsSubdivisor D' D) (hdeg : ∀ s, D'.degree s = D.degree s) : D' = D := by
  obtain ⟨j, hj⟩ := hsub
  haveI : IsClosedImmersion j := isClosedImmersion_isSubdivisor_hom D' D j hj
  haveI : IsIso j := by
    rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
    sorry
  refine RelEffCartierDiv.ext ?_
  rw [← Scheme.IdealSheafData.ker_subschemeι D'.ideal, ← hj, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_subschemeι]

end RelEffCartierDiv

end ModularCurves

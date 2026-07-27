/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Cancellation for `LocallyOfFinitePresentation`

If `f ≫ g` is locally of finite presentation and `g` is locally of finite type, then
`f` is locally of finite presentation (Stacks 01TX). The ring-level statement is
mathlib's `RingHom.FinitePresentation.of_comp_finiteType`; this file glues it with the
`HasRingHomProperty` framework, mirroring the wlog cascade of
`AlgebraicGeometry.HasRingHomProperty.of_comp` while threading the finite-type side
condition. Upstream candidate.
-/

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
theorem LocallyOfFinitePresentation.of_comp_of_locallyOfFiniteType
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (h : LocallyOfFinitePresentation (f ≫ g)) (hg : LocallyOfFiniteType g) :
    LocallyOfFinitePresentation f := by
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := @LocallyOfFinitePresentation) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have H := IsZariskiLocalAtTarget.restrict h U.1
    rw [morphismRestrict_comp] at H
    exact this H (IsZariskiLocalAtTarget.restrict hg U.1) inferInstance
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := @LocallyOfFinitePresentation) _ (iSup_affineOpens_eq_top Y)]
    intro U
    have H := HasRingHomProperty.comp_of_isOpenImmersion
      (P := @LocallyOfFinitePresentation) (f ⁻¹ᵁ U.1).ι (f ≫ g) h
    rw [← morphismRestrict_ι_assoc] at H
    haveI hgI : LocallyOfFiniteType g := hg
    exact this H inferInstance inferInstance
  wlog hX : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top
      (P := @LocallyOfFinitePresentation) _ (iSup_affineOpens_eq_top X)]
    intro U
    have H := HasRingHomProperty.comp_of_isOpenImmersion
      (P := @LocallyOfFinitePresentation) U.1.ι (f ≫ g) h
    rw [← Category.assoc] at H
    exact this H inferInstance
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)] at h ⊢
  have hgring := (HasRingHomProperty.iff_of_isAffine
    (P := @LocallyOfFiniteType)).mp hg
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at h
  exact RingHom.FinitePresentation.of_comp_finiteType _ h hgring

end AlgebraicGeometry

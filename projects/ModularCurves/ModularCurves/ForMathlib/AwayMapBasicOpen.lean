import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.RingHom.Bijective

/-!
# Away maps from basic-open restrictions

This file relates isomorphisms between affine basic opens to bijectivity of
the corresponding canonical away-localized ring homomorphism.
-/

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- If the restriction of a morphism between affine opens to corresponding
basic opens is an isomorphism, then the canonical away map of its map on
sections is bijective. -/
theorem Scheme.Hom.awayMap_appLE_bijective_of_resLE_basicOpen_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : Y.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U) (r : Γ(Y, U))
    [hRestrict : IsIso
      (f.resLE (Y.basicOpen r)
        (X.basicOpen (f.appLE U V e r))
        (by simp [Scheme.Hom.appLE]))] :
    Function.Bijective
      (Localization.awayMap (f.appLE U V e).hom r) := by
  letI := hU.isLocalization_basicOpen r
  letI := hV.isLocalization_basicOpen (f.appLE U V e r)
  let eBasic :
      X.basicOpen (f.appLE U V e r) ≤
        f ⁻¹ᵁ Y.basicOpen r := by
    simp [Scheme.Hom.appLE]
  let g :=
    f.resLE (Y.basicOpen r)
      (X.basicOpen (f.appLE U V e r)) eBasic
  haveI hg : IsIso g := by
    dsimp only [g]
    exact hRestrict
  haveI hgOp : IsIso g.op := by
    infer_instance
  haveI hRestrictedAppTop : IsIso g.appTop := by
    rw [← Scheme.Γ_map_op]
    exact Scheme.Γ.map_isIso g.op
  haveI hRestrictedAppLE :
      IsIso
        (f.appLE (Y.basicOpen r)
          (X.basicOpen (f.appLE U V e r))
          (by simp [Scheme.Hom.appLE])) := by
    rw [← MorphismProperty.isomorphisms.iff]
    exact
      ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
        (arrowResLEAppIso f (Y.basicOpen r)
          (X.basicOpen (f.appLE U V e r))
          eBasic)).mp
        (by simpa only [MorphismProperty.isomorphisms.iff] using
          hRestrictedAppTop)
  have hBijective :
      Function.Bijective
        (f.appLE (Y.basicOpen r)
          (X.basicOpen (f.appLE U V e r))
          (by simp [Scheme.Hom.appLE])).hom :=
    ConcreteCategory.bijective_of_isIso _
  rw [IsAffineOpen.appLE_eq_away_map f hU hV e r,
    CommRingCat.hom_ofHom] at hBijective
  exact
    (RingHom.Bijective.respectsIso.isLocalization_away_iff
      Γ(Y, Y.basicOpen r) Γ(X, X.basicOpen (f.appLE U V e r))
      (f.appLE U V e).hom r).mpr hBijective

end AlgebraicGeometry

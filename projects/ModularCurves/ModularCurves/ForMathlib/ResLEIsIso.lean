import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Isomorphisms on smaller open restrictions

This file records a pullback criterion for shrinking an isomorphic `resLE`
comparison to smaller source and target opens.
-/

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- An isomorphic restriction remains an isomorphism after shrinking the
target and taking its exact preimage inside the original source open. -/
theorem Scheme.Hom.resLE_isIso_of_le_of_resLE_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U)
    [hBig : IsIso (f.resLE U V e)]
    {U' : Y.Opens} (hU : U' ≤ U)
    {V' : X.Opens} (hV : V' = V ⊓ f ⁻¹ᵁ U') :
    IsIso
      (f.resLE U' V'
        (by rw [hV]; exact inf_le_right)) := by
  let hVV : V' ≤ V := by
    rw [hV]
    exact inf_le_left
  let small :=
    f.resLE U' V'
      (by rw [hV]; exact inf_le_right)
  let big := f.resLE U V e
  have hComm :
      X.homOfLE hVV ≫ big =
        small ≫ Y.homOfLE hU := by
    dsimp only [big, small]
    rw [← cancel_mono U.ι]
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι,
      Scheme.homOfLE_ι]
    rw [← Category.assoc, Scheme.homOfLE_ι]
  have hRange :
      big ⁻¹ᵁ (Y.homOfLE hU).opensRange =
        (X.homOfLE hVV).opensRange := by
    dsimp only [big]
    simp only [Scheme.opensRange_homOfLE,
      Scheme.Hom.resLE_preimage]
    rw [← V.ι.image_injective.eq_iff]
    simp only [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
    rw [inf_eq_right.mpr hU, hV]
    simp only [← inf_assoc, inf_idem]
  have hPullback :
      IsPullback small (X.homOfLE hVV)
        (Y.homOfLE hU) big :=
    IsOpenImmersion.isPullback small
      (X.homOfLE hVV) (Y.homOfLE hU) big hComm hRange
  rw [← MorphismProperty.isomorphisms.iff]
  exact
    MorphismProperty.of_isPullback hPullback.flip
      (by simpa only [MorphismProperty.isomorphisms.iff] using hBig)

end AlgebraicGeometry

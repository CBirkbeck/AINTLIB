import ModularCurves.EllipticCurve.PoleSheafAwaySections
import ModularCurves.EllipticCurve.PoleSheafModel

/-!
# The marked-point complement of a Weierstrass model

This file identifies the complement of the zero section in a projective Weierstrass model
with its standard affine `Z`-chart.
-/

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace ModularCurves

noncomputable section

variable {R : Type u} [CommRing R]

/-- A residue-field fibre of a separated morphism is separated over the residue field. -/
theorem isSeparated_fiberToSpecResidueField
    {E S : Scheme.{u}} (π : E ⟶ S) [IsSeparated π] (s : S) :
    IsSeparated (π.fiberToSpecResidueField s) := by
  change IsSeparated (pullback.snd π (S.fromSpecResidueField s))
  exact AlgebraicGeometry.IsSeparated.isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback π (S.fromSpecResidueField s))
    (show IsSeparated π from inferInstance)

/-- The complement of the zero section in a projective Weierstrass model is its affine
`Z`-chart. -/
theorem sectionAway_projModelZero_eq_zChart (W : WeierstrassCurve R) :
    sectionAway (projModelZero W) (projModelZero_projModelπ W) =
      (projModelZChart W : (projModel W).Opens) := by
  ext p
  change p ∉ Set.range ⇑(projModelZero W) ↔
    p ∈ (projModelZChart W : (projModel W).Opens)
  constructor
  · intro hp
    by_contra hpZ
    exact hp (mem_range_zero_of_not_mem_zChart hpZ)
  · intro hpZ hp
    exact not_mem_zChart_of_mem_range_zero hp hpZ

/-- A pointed isomorphism pulls the complement of the target section back to the complement
of the source section. -/
theorem preimage_sectionAway_eq_of_pointedIso
    {X Y T : Scheme.{u}} {πX : X ⟶ T} {πY : Y ⟶ T}
    [IsSeparated πX] [IsSeparated πY]
    (zX : T ⟶ X) (hzX : zX ≫ πX = 𝟙 T)
    (zY : T ⟶ Y) (hzY : zY ≫ πY = 𝟙 T)
    (e : X ≅ Y) (hez : zX ≫ e.hom = zY) :
    e.hom ⁻¹ᵁ sectionAway zY hzY = sectionAway zX hzX := by
  ext x
  change e.hom.base x ∉ Set.range ⇑zY ↔ x ∉ Set.range ⇑zX
  constructor
  · intro h hx
    obtain ⟨t, rfl⟩ := hx
    apply h
    refine ⟨t, ?_⟩
    symm
    rw [show e.hom.base (zX t) = (zX ≫ e.hom) t from rfl, hez]
  · intro h hx
    obtain ⟨t, ht⟩ := hx
    apply h
    refine ⟨t, e.hom.homeomorph.injective ?_⟩
    change e.hom.base (zX t) = e.hom.base x
    rw [show e.hom.base (zX t) = (zX ≫ e.hom) t from rfl, hez, ht]

end

end ModularCurves

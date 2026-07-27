import ModularCurves.ForMathlib.SchemeModuleRestrictPushforward
import ModularCurves.Picard.DualPullback.OpenAdjunction

/-!
# Pullback--pushforward units over an isomorphism locus

This file proves that the pullback--pushforward unit is an isomorphism along an
isomorphism of schemes. It then compares the global unit with the unit of a
restriction to an open subscheme.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

private theorem restrictAdjunction_unit_app_isIso_of_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (M : Y.Modules) :
    IsIso ((restrictAdjunction f).unit.app M) := by
  rw [Hom.isIso_iff_isIso_app]
  intro U
  rw [restrictAdjunction_unit_app_app]
  let e : f ''ᵁ f ⁻¹ᵁ U ≅ U := eqToIso (by
    rw [f.image_preimage_eq_opensRange_inf, f.opensRange_of_isIso,
      top_inf_eq])
  have he : homOfLE (f.image_preimage_le U) = e.hom :=
    Subsingleton.elim _ _
  rw [he]
  letI : IsIso e.hom := e.isIso_hom
  letI : IsIso e.hom.op := inferInstance
  exact Functor.map_isIso M.presheaf e.hom.op

/-- Pullback--pushforward along an isomorphism has invertible adjunction unit. -/
instance pullbackPushforwardAdjunction_unit_app_isIso_of_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (M : Y.Modules) :
    IsIso ((pullbackPushforwardAdjunction f).unit.app M) := by
  letI (N : Y.Modules) : IsIso ((restrictAdjunction f).unit.app N) :=
    restrictAdjunction_unit_app_isIso_of_isIso f N
  letI : IsIso (restrictAdjunction f).unit :=
    NatIso.isIso_of_isIso_app _
  let hRestrict := (restrictAdjunction f).fullyFaithfulLOfIsIsoUnit
  let hPullback := hRestrict.ofIso (restrictFunctorIsoPullback f)
  letI : (pullback f).Full := hPullback.full
  letI : (pullback f).Faithful := hPullback.faithful
  infer_instance

end AlgebraicGeometry.Scheme.Modules

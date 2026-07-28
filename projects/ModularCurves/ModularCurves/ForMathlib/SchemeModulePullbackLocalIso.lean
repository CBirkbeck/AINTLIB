/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.Picard.DualPullback.Square

/-!
# Local isomorphisms and pullback of scheme modules

A module morphism that is invertible on an open remains invertible after
pullback and restriction to the inverse-image open.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

private noncomputable def pullbackRestrictIso
    (f : Y ⟶ X) (U : X.Opens) :
    restrictFunctor U.ι ⋙ pullback (f ∣_ U) ≅
      pullback f ⋙ restrictFunctor (f ⁻¹ᵁ U).ι :=
  Functor.isoWhiskerRight
      (restrictFunctorIsoPullback U.ι) (pullback (f ∣_ U)) ≪≫
    pullbackSquareIso (f ∣_ U) U.ι (f ⁻¹ᵁ U).ι f
      (morphismRestrict_ι f U) ≪≫
    Functor.isoWhiskerLeft (pullback f)
      (restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).symm

/-- Pullback preserves invertibility after restricting to the inverse image
of an open where the original module morphism is invertible. -/
theorem isIso_restrict_pullback_map_of_restrict
    (f : Y ⟶ X) {M N : X.Modules} (q : M ⟶ N) (U : X.Opens)
    [IsIso ((restrictFunctor U.ι).map q)] :
    IsIso
      ((restrictFunctor (f ⁻¹ᵁ U).ι).map ((pullback f).map q)) := by
  let e := pullbackRestrictIso f U
  let a :=
    (pullback (f ∣_ U)).map ((restrictFunctor U.ι).map q)
  let b :=
    (restrictFunctor (f ⁻¹ᵁ U).ι).map ((pullback f).map q)
  haveI ha : IsIso a := Functor.map_isIso _ _
  have h : a ≫ e.hom.app N = e.hom.app M ≫ b :=
    e.hom.naturality q
  haveI hComp : IsIso (e.hom.app M ≫ b) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_left (e.hom.app M) b

/-- Pull back a morphism from the structure module, using the canonical
identification between the pulled-back structure module and the source
structure module. -/
noncomputable def pullbackUnitHom
    (f : Y ⟶ X) {L : X.Modules} (q : unitObj X ⟶ L) :
    unitObj Y ⟶ (pullback f).obj L :=
  (pullbackUnitIso f).inv ≫ (pullback f).map q

/-- The pulled-back structure-module morphism is invertible on the preimage
of every open where the original morphism is invertible. -/
theorem isIso_restrict_pullbackUnitHom_of_restrict
    (f : Y ⟶ X) {L : X.Modules} (q : unitObj X ⟶ L)
    (U : X.Opens) [IsIso ((restrictFunctor U.ι).map q)] :
    IsIso
      ((restrictFunctor (f ⁻¹ᵁ U).ι).map
        (pullbackUnitHom f q)) := by
  let F := restrictFunctor (f ⁻¹ᵁ U).ι
  haveI :
      IsIso (F.map ((pullback f).map q)) :=
    isIso_restrict_pullback_map_of_restrict f q U
  unfold pullbackUnitHom
  rw [F.map_comp]
  infer_instance

end AlgebraicGeometry.Scheme.Modules

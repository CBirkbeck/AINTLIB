/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Adapted from the Apache-licensed
`SchemeModulePushforwardPullbackSupport.lean` in Vilin97/Clawristotle.
-/
import ModularCurves.ForMathlib.SchemeModuleRestrictPushforward
import ModularCurves.ForMathlib.SchemeModuleSupportDrop
import ModularCurves.Picard.DualPullback.OpenAdjunction
import ModularCurves.Picard.InvertibleSheafTensorQuasicoherent

/-!
# Support of a pushforward after pullback

For a finite-type quasicoherent module `M`, the support of `f_* f^* M`
is contained in the support of `M`. No finiteness or quasicoherence
hypothesis on the pushforward is needed.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable local instance pushforwardPullbackSupportMonoidal
    (Z : Scheme.{u}) :
    MonoidalCategory Z.Modules :=
  monoidalCategory Z

/-- A source module that vanishes over the inverse image of the support
complement of `M` has pushforward support contained in the support of `M`. -/
private theorem closedStalkSupport_pushforward_le_of_isZero_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [M.IsFiniteType] [M.IsQuasicoherent] (N : X.Modules)
    (hNzero :
      IsZero
        (N.restrict
          (f ⁻¹ᵁ closedStalkSupportComplement M).ι)) :
    closedStalkSupport ((pushforward f).obj N) ≤
      closedStalkSupport M := by
  let U := closedStalkSupportComplement M
  let j : U.toScheme ⟶ Y := U.ι
  let V := f ⁻¹ᵁ U
  let g : V.toScheme ⟶ U.toScheme := f ∣_ U
  have hpushforwardZero :
      IsZero ((pushforward g).obj (N.restrict V.ι)) :=
    (pushforward g).map_isZero hNzero
  have htargetZero :
      IsZero (((pushforward f).obj N).restrict j) := by
    let e := (restrictPushforwardIsoOfIsPullback
      f g V.ι j (isPullback_morphismRestrict f U)).app N
    exact e.isZero_iff.mpr hpushforwardZero
  change
    closure (stalkSupport ((pushforward f).obj N)) ⊆
      (closedStalkSupport M : Set Y)
  apply closure_minimal
  · intro y hy
    by_contra hyM
    let x : U := ⟨y, hyM⟩
    have hx :
        x ∈ j ⁻¹' stalkSupport ((pushforward f).obj N) :=
      hy
    rw [preimage_stalkSupport_of_openImmersion j] at hx
    exact hx ((underlyingStalkFunctor x).map_isZero htargetZero)
  · exact (closedStalkSupport M).2

/-- The closed stalk support of `f_* f^* M` is contained in that of `M`. -/
theorem closedStalkSupport_pushforward_pullback_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [M.IsFiniteType] [M.IsQuasicoherent] :
    closedStalkSupport
        ((pushforward f).obj ((pullback f).obj M)) ≤
      closedStalkSupport M := by
  let U := closedStalkSupportComplement M
  let j : U.toScheme ⟶ Y := U.ι
  let V := f ⁻¹ᵁ U
  let g : V.toScheme ⟶ U.toScheme := f ∣_ U
  have hMzero : IsZero (M.restrict j) :=
    isZero_restrict_closedStalkSupportComplement M
  have hleft :
      IsZero ((pullback g).obj (M.restrict j)) :=
    (pullback g).map_isZero hMzero
  have hpullbackZero :
      IsZero (((pullback f).obj M).restrict V.ι) := by
    let e := (openPullbackSquareExplicitIsoT f U).app M
    exact e.isZero_iff.mp hleft
  exact closedStalkSupport_pushforward_le_of_isZero_restrict
    f M ((pullback f).obj M) hpullbackZero

/-- The closed stalk support of the pushforward of a pullback tensored by
an invertible module is contained in the support of the original module. -/
theorem closedStalkSupport_pushforward_pullback_tensor_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (L : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    (hL : IsInvertible L) :
    closedStalkSupport
        ((pushforward f).obj (((pullback f).obj M) ⊗ L)) ≤
      closedStalkSupport M := by
  let U := closedStalkSupportComplement M
  let V := f ⁻¹ᵁ U
  let g : V.toScheme ⟶ U.toScheme := f ∣_ U
  let A := (pullback f).obj M
  have hMzero : IsZero (M.restrict U.ι) :=
    isZero_restrict_closedStalkSupportComplement M
  have hleft :
      IsZero ((pullback g).obj (M.restrict U.ι)) :=
    (pullback g).map_isZero hMzero
  have hpullbackZero : IsZero (A.restrict V.ι) := by
    let e := (openPullbackSquareExplicitIsoT f U).app M
    exact e.isZero_iff.mp hleft
  letI : (pullback V.ι).Monoidal :=
    pullbackMonoidal V.ι
  let eRestr :
      (A ⊗ L).restrict V.ι ≅
        A.restrict V.ι ⊗ L.restrict V.ι :=
    (restrictFunctorIsoPullback V.ι).app (A ⊗ L) ≪≫
      (Functor.Monoidal.μIso (pullback V.ι) A L).symm ≪≫
      ((restrictFunctorIsoPullback V.ι).symm.app A ⊗ᵢ
        (restrictFunctorIsoPullback V.ι).symm.app L)
  have hLRestrict : IsInvertible (L.restrict V.ι) :=
    (hL.pullback V.ι).of_iso
      ((restrictFunctorIsoPullback V.ι).app L)
  have hFactorsZero :
      IsZero (A.restrict V.ι ⊗ L.restrict V.ι) :=
    hLRestrict.tensorObj_isZero hpullbackZero
  have htensorZero :
      IsZero ((A ⊗ L).restrict V.ι) :=
    eRestr.isZero_iff.mpr hFactorsZero
  exact closedStalkSupport_pushforward_le_of_isZero_restrict
    f M (A ⊗ L) htensorZero

end AlgebraicGeometry.Scheme.Modules

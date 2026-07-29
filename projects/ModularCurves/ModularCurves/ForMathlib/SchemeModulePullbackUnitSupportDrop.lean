/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Adapted from the Apache-licensed
`SchemeModulePullbackUnitSupportDrop.lean` in Vilin97/Clawristotle.
-/
import ModularCurves.ForMathlib.SchemeModuleComparisonCoherent
import ModularCurves.ForMathlib.SchemeModuleComparisonSupport
import ModularCurves.ForMathlib.SchemeModuleOpenUnitIso
import ModularCurves.ForMathlib.SchemeModulePushforwardPullbackSupport

/-!
# Support drop for the pullback-pushforward unit

When a morphism is an isomorphism over an open meeting the support of a
module, both residuals of the pullback-pushforward unit have strictly
smaller closed stalk support.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Both residual supports of the pullback-pushforward unit strictly decrease
when the isomorphism locus meets the source support. -/
theorem pullbackPushforwardUnit_residualSupport_lt
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    [IsIso (f ∣_ U)]
    (M : Y.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    [(kernel
      (Abelian.factorThruImage
        ((pullbackPushforwardAdjunction f).unit.app M))).IsFiniteType]
    [(kernel
      (Abelian.factorThruImage
        ((pullbackPushforwardAdjunction f).unit.app M))).IsQuasicoherent]
    [(cokernel
      (Abelian.image.ι
        ((pullbackPushforwardAdjunction f).unit.app M))).IsFiniteType]
    [(cokernel
      (Abelian.image.ι
        ((pullbackPushforwardAdjunction f).unit.app M))).IsQuasicoherent]
    (x : U)
    (hx : U.ι x ∈ closedStalkSupport M) :
    closedStalkSupport
          (kernel
            (Abelian.factorThruImage
              ((pullbackPushforwardAdjunction f).unit.app M))) <
        closedStalkSupport M ∧
      closedStalkSupport
          (cokernel
            (Abelian.image.ι
              ((pullbackPushforwardAdjunction f).unit.app M))) <
        closedStalkSupport M := by
  letI :
      IsIso
        ((restrictFunctor U.ι).map
          ((pullbackPushforwardAdjunction f).unit.app M)) :=
    isIso_restrict_pullbackPushforward_unit_of_isIso_morphismRestrict
      f U M
  exact
    comparisonResidual_closedStalkSupport_lt U.ι
      ((pullbackPushforwardAdjunction f).unit.app M)
      (closedStalkSupport_pushforward_pullback_le f M)
      x hx

/-- On a locally Noetherian target, coherence of the source and comparison
target supplies the residual finiteness hypotheses automatically. -/
theorem pullbackPushforwardUnit_residualSupport_lt_of_isLocallyNoetherian
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (U : Y.Opens) [IsIso (f ∣_ U)]
    (M : Y.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    [((pushforward f).obj ((pullback f).obj M)).IsFiniteType]
    [((pushforward f).obj ((pullback f).obj M)).IsQuasicoherent]
    (x : U)
    (hx : U.ι x ∈ closedStalkSupport M) :
    closedStalkSupport
          (kernel
            (Abelian.factorThruImage
              ((pullbackPushforwardAdjunction f).unit.app M))) <
        closedStalkSupport M ∧
      closedStalkSupport
          (cokernel
            (Abelian.image.ι
              ((pullbackPushforwardAdjunction f).unit.app M))) <
        closedStalkSupport M := by
  let E : Y.Modules :=
    (pushforward f).obj ((pullback f).obj M)
  let η : M ⟶ E :=
    (pullbackPushforwardAdjunction f).unit.app M
  letI : E.IsFiniteType :=
    inferInstanceAs
      (((pushforward f).obj ((pullback f).obj M)).IsFiniteType)
  letI : E.IsQuasicoherent :=
    inferInstanceAs
      (((pushforward f).obj ((pullback f).obj M)).IsQuasicoherent)
  have hresidual :=
    comparisonResidual_isFiniteType_and_isQuasicoherent
      (M := M) (N := E) η
  letI :
      (kernel (Abelian.factorThruImage η)).IsFiniteType :=
    hresidual.1.1
  letI :
      (kernel (Abelian.factorThruImage η)).IsQuasicoherent :=
    hresidual.1.2
  letI :
      (cokernel (Abelian.image.ι η)).IsFiniteType :=
    hresidual.2.1
  letI :
      (cokernel (Abelian.image.ι η)).IsQuasicoherent :=
    hresidual.2.2
  exact pullbackPushforwardUnit_residualSupport_lt f U M x hx

end AlgebraicGeometry.Scheme.Modules

import ModularCurves.EllipticCurve.ProjectiveCoordinatePullbackTwistMap
import ModularCurves.ForMathlib.SchemeModuleCanonicalSupportChowChart
import ModularCurves.ForMathlib.SchemeModuleComparisonCoherent
import ModularCurves.ForMathlib.SchemeModuleComparisonSupport
import ModularCurves.ForMathlib.SchemeModuleOpenUnitIso
import ModularCurves.ForMathlib.SchemeModulePushforwardMapRestrictionIso
import ModularCurves.ForMathlib.SchemeModulePullbackQuasicoherent
import ModularCurves.ForMathlib.SchemeModulePushforwardPullbackSupport
import ModularCurves.ForMathlib.SchemeModuleRestrictionIsoMonotone
import ModularCurves.ForMathlib.RelativeProjectivePushforwardFiniteType
import ModularCurves.Picard.InvertibleSheafTensorQuasicoherent

/-!
# Coordinate-twist comparisons on support-adapted Chow charts

A support-adapted Chow chart gives a projective coordinate which is invertible over the
isomorphism locus of the Chow cover. Multiplication by a power of this coordinate therefore
produces a comparison from the original module to a twisted pushforward which is an isomorphism
on that locus.
-/

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

noncomputable local instance (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  monoidalCategory X

namespace SupportAdaptedChowChart

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable {xπ : X ⟶ Spec (.of R)} {M : X.Modules}

/-- The pullback of the model module to the source of a support-adapted Chow chart. -/
noncomputable def pulledBackModel
    (C : SupportAdaptedChowChart xπ M) : C.source.Modules :=
  (pullback C.cover).obj M

/-- The pulled-back model tensored by the selected coordinate-hyperplane pole-sheaf power. -/
noncomputable def coordinateTwist
    (C : SupportAdaptedChowChart xπ M) (n : ℕ) :
    C.source.Modules :=
  C.pulledBackModel ⊗
    (pullback C.relativeProjective.chosenProjectiveMap).obj
      (MvPolynomial.coordinateHyperplanePoleSheafPower
        (R := R) C.coordinate n)

/-- The coordinate twist of a quasicoherent model is quasicoherent. -/
theorem coordinateTwist_isQuasicoherent
    (C : SupportAdaptedChowChart xπ M) (n : ℕ)
    [M.IsQuasicoherent] :
    (C.coordinateTwist n).IsQuasicoherent := by
  let P :=
    MvPolynomial.coordinateHyperplanePoleSheafPower
      (R := R) C.coordinate n
  let L :=
    (pullback C.relativeProjective.chosenProjectiveMap).obj P
  have hP : IsInvertible P :=
    MvPolynomial.coordinateHyperplanePoleSheafPower_isInvertible
      C.coordinate n
  have hL : IsInvertible L :=
    hP.pullback C.relativeProjective.chosenProjectiveMap
  letI : C.pulledBackModel.IsQuasicoherent := by
    dsimp only [pulledBackModel]
    exact isQuasicoherent_pullback C.cover M
  change (C.pulledBackModel ⊗ L).IsQuasicoherent
  exact hL.tensorObj_isQuasicoherent

/-- The coordinate twist of a finite-type quasicoherent model is finite type. -/
theorem coordinateTwist_isFiniteType
    (C : SupportAdaptedChowChart xπ M) (n : ℕ)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    (C.coordinateTwist n).IsFiniteType := by
  let P :=
    MvPolynomial.coordinateHyperplanePoleSheafPower
      (R := R) C.coordinate n
  let L :=
    (pullback C.relativeProjective.chosenProjectiveMap).obj P
  have hP : IsInvertible P :=
    MvPolynomial.coordinateHyperplanePoleSheafPower_isInvertible
      C.coordinate n
  have hL : IsInvertible L :=
    hP.pullback C.relativeProjective.chosenProjectiveMap
  letI : C.pulledBackModel.IsQuasicoherent := by
    dsimp only [pulledBackModel]
    exact isQuasicoherent_pullback C.cover M
  letI : C.pulledBackModel.IsFiniteType := by
    dsimp only [pulledBackModel]
    exact isFiniteType_pullback C.cover M
  change (C.pulledBackModel ⊗ L).IsFiniteType
  exact hL.tensorObj_isFiniteType

/-- The coordinate-twisted model pushed down along the support-adapted Chow cover. -/
noncomputable def coordinateComodel
    (C : SupportAdaptedChowChart xπ M) (n : ℕ) : X.Modules :=
  (pushforward C.cover).obj (C.coordinateTwist n)

/-- The coordinate comodel of a quasicoherent model is quasicoherent. -/
theorem coordinateComodel_isQuasicoherent
    (C : SupportAdaptedChowChart xπ M) (n : ℕ)
    [M.IsQuasicoherent] :
    (C.coordinateComodel n).IsQuasicoherent := by
  letI : IsProper C.cover :=
    C.relativeProjective.isProper
  letI : (C.coordinateTwist n).IsQuasicoherent :=
    C.coordinateTwist_isQuasicoherent n
  exact isQuasicoherent_pushforward_of_isProper
    C.cover (C.coordinateTwist n)

/-- On a locally Noetherian target, the coordinate comodel of a finite-type
quasicoherent model is finite type. -/
theorem coordinateComodel_isFiniteType
    [IsLocallyNoetherian X]
    (C : SupportAdaptedChowChart xπ M) (n : ℕ)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    (C.coordinateComodel n).IsFiniteType := by
  letI : (C.coordinateTwist n).IsQuasicoherent :=
    C.coordinateTwist_isQuasicoherent n
  letI : (C.coordinateTwist n).IsFiniteType :=
    C.coordinateTwist_isFiniteType n
  exact C.relativeProjective.isFiniteType_pushforward
    (C.coordinateTwist n)

/-- The coordinate comodel has closed stalk support contained in that of
the original model. -/
theorem coordinateComodel_closedStalkSupport_le
    (C : SupportAdaptedChowChart xπ M) (n : ℕ)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    closedStalkSupport (C.coordinateComodel n) ≤
      closedStalkSupport M := by
  let P :=
    MvPolynomial.coordinateHyperplanePoleSheafPower
      (R := R) C.coordinate n
  let L :=
    (pullback C.relativeProjective.chosenProjectiveMap).obj P
  have hP : IsInvertible P :=
    MvPolynomial.coordinateHyperplanePoleSheafPower_isInvertible
      C.coordinate n
  have hL : IsInvertible L :=
    hP.pullback C.relativeProjective.chosenProjectiveMap
  exact
    closedStalkSupport_pushforward_pullback_tensor_le
      C.cover M L hL

/-- The adjunction unit followed by multiplication with the selected projective coordinate. -/
noncomputable def coordinateComparison
    (C : SupportAdaptedChowChart xπ M) (n : ℕ) :
    M ⟶ C.coordinateComodel n :=
  (pullbackPushforwardAdjunction C.cover).unit.app M ≫
    (pushforward C.cover).map
      (MvPolynomial.coordinateHyperplanePolePullbackTwistMap
        (R := R) C.relativeProjective.chosenProjectiveMap
        C.pulledBackModel C.coordinate n)

/-- The coordinate comparison is an isomorphism on the support-adapted target open. -/
theorem coordinateComparison_restrict_isIso
    (C : SupportAdaptedChowChart xπ M) (n : ℕ) :
    IsIso
      ((restrictFunctor C.openSubscheme.ι).map
        (C.coordinateComparison n)) := by
  let α :=
    MvPolynomial.coordinateHyperplanePolePullbackTwistMap
      (R := R) C.relativeProjective.chosenProjectiveMap
      C.pulledBackModel C.coordinate n
  letI hαChart :
      IsIso
        ((restrictFunctor
          (C.relativeProjective.chosenProjectiveMap ⁻¹ᵁ
            MvPolynomial.coordinateOpen
              (R := R) C.coordinate).ι).map α) :=
    MvPolynomial.coordinateHyperplanePolePullbackTwistMap_restrict_self_isIso
      (R := R) C.relativeProjective.chosenProjectiveMap
      C.pulledBackModel C.coordinate n
  letI hαOpen :
      IsIso
        ((restrictFunctor
          (C.cover ⁻¹ᵁ C.openSubscheme).ι).map α) :=
    isIso_restrict_map_of_le α
      C.preimage_le_coordinateOpen
  letI hPushforward :
      IsIso
        ((restrictFunctor C.openSubscheme.ι).map
          ((pushforward C.cover).map α)) :=
    isIso_restrict_pushforward_map_of_restrict
      C.cover C.openSubscheme α
  letI hCover :
      IsIso (C.cover ∣_ C.openSubscheme) :=
    C.restrictedMorphismIsIso
  letI hUnit :
      IsIso
        ((restrictFunctor C.openSubscheme.ι).map
          ((pullbackPushforwardAdjunction C.cover).unit.app M)) :=
    isIso_restrict_pullbackPushforward_unit_of_isIso_morphismRestrict
      C.cover C.openSubscheme M
  change
    IsIso
      ((restrictFunctor C.openSubscheme.ι).map
        ((pullbackPushforwardAdjunction C.cover).unit.app M ≫
          (pushforward C.cover).map α))
  rw [Functor.map_comp]
  exact IsIso.comp_isIso' hUnit hPushforward

/-- On a locally Noetherian stage, both residuals of the coordinate
comparison have strictly smaller closed stalk support than the model. -/
theorem coordinateComparison_residual_closedStalkSupport_lt
    [IsLocallyNoetherian X]
    (C : SupportAdaptedChowChart xπ M) (n : ℕ)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    closedStalkSupport
          (kernel
            (Abelian.factorThruImage (C.coordinateComparison n))) <
        closedStalkSupport M ∧
      closedStalkSupport
          (cokernel
            (Abelian.image.ι (C.coordinateComparison n))) <
        closedStalkSupport M := by
  letI : (C.coordinateComodel n).IsQuasicoherent :=
    C.coordinateComodel_isQuasicoherent n
  letI : (C.coordinateComodel n).IsFiniteType :=
    C.coordinateComodel_isFiniteType n
  have hResidual :=
    comparisonResidual_isFiniteType_and_isQuasicoherent
      (C.coordinateComparison n)
  letI :
      (kernel
        (Abelian.factorThruImage
          (C.coordinateComparison n))).IsFiniteType :=
    hResidual.1.1
  letI :
      (kernel
        (Abelian.factorThruImage
          (C.coordinateComparison n))).IsQuasicoherent :=
    hResidual.1.2
  letI :
      (cokernel
        (Abelian.image.ι
          (C.coordinateComparison n))).IsFiniteType :=
    hResidual.2.1
  letI :
      (cokernel
        (Abelian.image.ι
          (C.coordinateComparison n))).IsQuasicoherent :=
    hResidual.2.2
  letI :
      IsIso
        ((restrictFunctor C.openSubscheme.ι).map
          (C.coordinateComparison n)) :=
    C.coordinateComparison_restrict_isIso n
  obtain ⟨x, hx⟩ := C.supportPoint
  exact
    comparisonResidual_closedStalkSupport_lt
      C.openSubscheme.ι (C.coordinateComparison n)
      (C.coordinateComodel_closedStalkSupport_le n) x hx

end SupportAdaptedChowChart

end

end AlgebraicGeometry.Scheme.Modules

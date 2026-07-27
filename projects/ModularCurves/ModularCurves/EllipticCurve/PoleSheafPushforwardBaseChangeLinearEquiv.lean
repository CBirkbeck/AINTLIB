import ModularCurves.EllipticCurve.PoleSheafPowerOneBaseChange
import ModularCurves.EllipticCurve.PoleSheafPushforwardBaseChange
import ModularCurves.ForMathlib.SchemeModulePushforwardBaseChangeLinearEquiv

/-!
# Pole-section modules from pushforward base change

An isomorphic top component of the canonical pole-sheaf pushforward
base-change morphism gives the expected equivalence on base-linear global
sections. In degree one this equivalence preserves the canonical pole
section.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace TensorProduct

universe u

namespace ModularCurves

/-- If the top component of canonical pushforward base change for
`O(n[0])` is an isomorphism, then its global sections commute with the
given affine base change. -/
noncomputable abbrev
    sectionPoleSheafPower_baseSectionsBaseChangeLinearEquivOfAppTopIso
    {C S T : Scheme.{u}} [IsAffine S] [IsAffine T] {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) (n : ℕ)
    [((Scheme.Modules.pushforward π).obj
      (sectionPoleSheafPower π z hz n)).IsQuasicoherent]
    [IsIso ((sectionPoleSheafPowerPushforwardBaseChange
      hsm z hz t n).val.app (.op (⊤ : T.Opens)))] :
    let M := sectionPoleSheafPower π z hz n
    let πT := pullback.snd π t
    let zT := sectionBaseChange z hz t
    let hzT := sectionBaseChange_snd z hz t
    let MT := sectionPoleSheafPower πT zT hzT n
    let B := Γ(S, (⊤ : S.Opens))
    let A := Γ(T, (⊤ : T.Opens))
    letI : Algebra B A := t.appTop.hom.toAlgebra
    A ⊗[B] Scheme.Modules.baseSections π M ≃ₗ[A]
      Scheme.Modules.baseSections πT MT :=
  Scheme.Modules.baseSectionsPushforwardBaseChangeLinearEquivOfAppTopIso
    π t (sectionPoleSheafPower π z hz n)
      (sectionPoleSheafPower (pullback.snd π t)
        (sectionBaseChange z hz t) (sectionBaseChange_snd z hz t) n)
      (sectionPoleSheafPowerPushforwardBaseChange hsm z hz t n)

/-- The first-pole base-change equivalence sends the scalar extension of
the canonical first-pole section to the literal canonical first-pole
section on the base-changed family. -/
theorem
    sectionPoleSheafPowerOne_baseSectionsBaseChangeLinearEquivOfAppTopIso_one_tmul
    {C S T : Scheme.{u}} [IsAffine S] [IsAffine T] {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S)
    [((Scheme.Modules.pushforward π).obj
      (sectionPoleSheafPower π z hz 1)).IsQuasicoherent]
    [IsIso ((sectionPoleSheafPowerPushforwardBaseChange
      hsm z hz t 1).val.app (.op (⊤ : T.Opens)))] :
    let M := sectionPoleSheafPower π z hz 1
    let πT := pullback.snd π t
    let zT := sectionBaseChange z hz t
    let hzT := sectionBaseChange_snd z hz t
    let MT := sectionPoleSheafPower πT zT hzT 1
    let B := Γ(S, (⊤ : S.Opens))
    let A := Γ(T, (⊤ : T.Opens))
    letI : Algebra B A := t.appTop.hom.toAlgebra
    Scheme.Modules.baseSectionsPushforwardBaseChangeLinearEquivOfAppTopIso
        π t M MT
        (sectionPoleSheafPowerPushforwardBaseChange hsm z hz t 1)
        ((1 : A) ⊗ₜ[B]
          (sectionPoleSheafPowerOneSection π z hz :
            Scheme.Modules.baseSections π M)) =
      sectionPoleSheafPowerOneSection πT zT hzT := by
  dsimp only
  let M := sectionPoleSheafPower π z hz 1
  let N := (Scheme.Modules.pushforward π).obj M
  let πT := pullback.snd π t
  let zT := sectionBaseChange z hz t
  let hzT := sectionBaseChange_snd z hz t
  let MT := sectionPoleSheafPower πT zT hzT 1
  let B := Γ(S, (⊤ : S.Opens))
  let A := Γ(T, (⊤ : T.Opens))
  letI : Algebra B A := t.appTop.hom.toAlgebra
  let φ := sectionPoleSheafPowerPushforwardBaseChange
    (π := π) hsm z hz t 1
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.baseSectionsPushforwardTopIso πT MT).hom).1
  rw [Scheme.Modules.baseSectionsPushforwardTopIso_hom_apply]
  have hBaseChangeRaw :=
    Scheme.Modules.baseSectionsPushforwardBaseChangeLinearEquivOfAppTopIso_one_tmul
      (X := C) (S := S) (T := T)
      (f := π) (t := t) (M := M) (MT := MT)
      (φ := φ)
      (s := sectionPoleSheafPowerOneSection π z hz)
  rw [hBaseChangeRaw]
  have hPushforward :
      φ.app (⊤ : T.Opens)
          (Scheme.Modules.affinePullbackUnitTop t N
            (Scheme.Modules.pushforwardTopSection π M
              (sectionPoleSheafPowerOneSection π z hz))) =
        Scheme.Modules.pushforwardTopSection πT MT
          ((sectionPoleSheafPowerBaseChangeIso
              (π := π) hsm z hz t 1).hom.app
            (⊤ : (pullback π t).Opens)
              (Scheme.Modules.affinePullbackUnitTop
                (pullback.fst π t) M
                  (sectionPoleSheafPowerOneSection π z hz))) :=
    sectionPoleSheafPowerPushforwardBaseChange_app_top_pullbackUnit
      (π := π) hsm z hz t 1 (sectionPoleSheafPowerOneSection π z hz)
  have hLiteral :
      (sectionPoleSheafPowerBaseChangeIso
          (π := π) hsm z hz t 1).hom.app
        (⊤ : (pullback π t).Opens)
          (Scheme.Modules.affinePullbackUnitTop
            (pullback.fst π t) M
              (sectionPoleSheafPowerOneSection π z hz)) =
        sectionPoleSheafPowerOneSection πT zT hzT :=
    sectionPoleSheafPowerOneSection_baseChange
      (π := π) hsm z hz t
  have hLiteralPushforward :
      Scheme.Modules.pushforwardTopSection πT MT
          ((sectionPoleSheafPowerBaseChangeIso
              (π := π) hsm z hz t 1).hom.app
            (⊤ : (pullback π t).Opens)
              (Scheme.Modules.affinePullbackUnitTop
                (pullback.fst π t) M
                  (sectionPoleSheafPowerOneSection π z hz))) =
        Scheme.Modules.pushforwardTopSection πT MT
          (sectionPoleSheafPowerOneSection πT zT hzT) :=
    congrArg (Scheme.Modules.pushforwardTopSection πT MT) hLiteral
  have hAfterBaseChange :
      φ.app (⊤ : T.Opens)
          (Scheme.Modules.affinePullbackUnitTop t N
            (Scheme.Modules.pushforwardTopSection π M
              (sectionPoleSheafPowerOneSection π z hz))) =
        Scheme.Modules.pushforwardTopSection πT MT
          (sectionPoleSheafPowerOneSection πT zT hzT) :=
    hPushforward.trans hLiteralPushforward
  exact hAfterBaseChange

end ModularCurves

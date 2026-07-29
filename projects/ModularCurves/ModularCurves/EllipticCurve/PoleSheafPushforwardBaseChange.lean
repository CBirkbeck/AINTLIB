import ModularCurves.EllipticCurve.PoleSheaf
import ModularCurves.ForMathlib.SchemeModulePushforwardBaseChange

/-!
# Pushforward base change for pole sheaves

This file specializes the canonical pullback--pushforward base-change morphism to
the tensor powers `O(n[0])` of a section's pole sheaf.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

/-- The canonical base-change morphism for the pushforward of `O(n[0])`. -/
noncomputable def sectionPoleSheafPowerPushforwardBaseChange
    {C S T : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) (n : ℕ) :
    (Scheme.Modules.pullback t).obj
        ((Scheme.Modules.pushforward π).obj (sectionPoleSheafPower π z hz n)) ⟶
      (Scheme.Modules.pushforward (pullback.snd π t)).obj
        (sectionPoleSheafPower (pullback.snd π t) (sectionBaseChange z hz t)
          (sectionBaseChange_snd z hz t) n) :=
  (Scheme.Modules.pullbackPushforwardBaseChange π t).app _ ≫
    (Scheme.Modules.pushforward (pullback.snd π t)).map
      (sectionPoleSheafPowerBaseChangeIso hsm z hz t n).hom

/-- The canonical pole-sheaf pushforward base-change morphism sends a pullback-unit
section to the corresponding pullback-unit section after the pole-sheaf base-change
isomorphism. -/
theorem sectionPoleSheafPowerPushforwardBaseChange_app_top_pullbackUnit
    {C S T : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) (n : ℕ)
    (s : Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens))) :
    let M := sectionPoleSheafPower π z hz n
    let g := pullback.fst π t
    let πT := pullback.snd π t
    let zT := sectionBaseChange z hz t
    let hzT := sectionBaseChange_snd z hz t
    let MT := sectionPoleSheafPower πT zT hzT n
    (sectionPoleSheafPowerPushforwardBaseChange hsm z hz t n).app
        (⊤ : T.Opens)
          (Scheme.Modules.affinePullbackUnitTop t
            ((Scheme.Modules.pushforward π).obj M)
              (Scheme.Modules.pushforwardTopSection π M s)) =
      Scheme.Modules.pushforwardTopSection πT MT
        ((sectionPoleSheafPowerBaseChangeIso hsm z hz t n).hom.app
          (⊤ : (pullback π t).Opens)
            (Scheme.Modules.affinePullbackUnitTop g M s)) := by
  dsimp only
  let M := sectionPoleSheafPower π z hz n
  let g := pullback.fst π t
  let πT := pullback.snd π t
  let zT := sectionBaseChange z hz t
  let hzT := sectionBaseChange_snd z hz t
  let MT := sectionPoleSheafPower πT zT hzT n
  let e := sectionPoleSheafPowerBaseChangeIso hsm z hz t n
  let baseUnit := Scheme.Modules.affinePullbackUnitTop t
    ((Scheme.Modules.pushforward π).obj M)
      (Scheme.Modules.pushforwardTopSection π M s)
  let fibreUnit := Scheme.Modules.affinePullbackUnitTop g M s
  change (((Scheme.Modules.pullbackPushforwardBaseChange π t).app M ≫
      (Scheme.Modules.pushforward πT).map e.hom).app (⊤ : T.Opens))
        baseUnit = _
  calc
    _ = ((Scheme.Modules.pushforward πT).map e.hom).app (⊤ : T.Opens)
        (((Scheme.Modules.pullbackPushforwardBaseChange π t).app M).app
          (⊤ : T.Opens) baseUnit) := rfl
    _ = ((Scheme.Modules.pushforward πT).map e.hom).app (⊤ : T.Opens)
        (Scheme.Modules.pushforwardTopSection πT ((Scheme.Modules.pullback g).obj M)
          fibreUnit) := by
      apply congrArg
      exact Scheme.Modules.pullbackPushforwardBaseChange_app_top_pullbackUnit
        π t M s
    _ = _ := Scheme.Modules.pushforwardMap_app_top_pushforwardTopSection
      πT e.hom fibreUnit

end ModularCurves

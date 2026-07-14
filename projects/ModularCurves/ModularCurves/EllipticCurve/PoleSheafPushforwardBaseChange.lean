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

end ModularCurves

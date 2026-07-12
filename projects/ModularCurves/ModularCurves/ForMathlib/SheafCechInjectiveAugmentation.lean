import ModularCurves.ForMathlib.SheafCechInjectiveBicomplex
import ModularCurves.ForMathlib.SheafDerivedGlobalSections
import ModularCurves.ForMathlib.TotalComplexUpNatVerticalEdge

/-!
# The Cech augmentation into an injective resolution

Apply the native Cech functor to the augmentation of the chosen injective
resolution and record the low-column exactness used by the vertical total edge.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace TopCat.Sheaf

noncomputable section

variable {X : TopCat.{u}}
variable {ι : Type u} (U : ι → Opens X)

/-- The native Cech map induced by the augmentation into the chosen injective
resolution. -/
noncomputable def cechInjectiveResolutionAugmentation
    (F : Sheaf AddCommGrpCat.{u} X) :
    (cechComplexFunctor U).obj F.obj ⟶
      (cechInjectiveResolutionBicomplex U F).X 0 :=
  (cechComplexFunctor U).map
    ((injectiveResolution (toSiteSheaf F)).ι.f 0).hom

@[simp]
theorem cechInjectiveResolutionAugmentation_f
    (F : Sheaf AddCommGrpCat.{u} X) (p : ℕ) :
    (cechInjectiveResolutionAugmentation U F).f p =
      ((cechComplexFunctor U).map
        ((injectiveResolution (toSiteSheaf F)).ι.f 0).hom).f p :=
  rfl

@[reassoc]
theorem cechInjectiveResolutionAugmentation_f_comp_d
    (F : Sheaf AddCommGrpCat.{u} X) (p : ℕ) :
    (cechInjectiveResolutionAugmentation U F).f p ≫
      ((cechInjectiveResolutionBicomplex U F).d 0 1).f p = 0 := by
  let I := injectiveResolution (toSiteSheaf F)
  have h :
      (I.ι.f 0).hom ≫ (I.cocomplex.d 0 1).hom = 0 := by
    exact congrArg (fun f ↦ f.hom)
      (InjectiveResolution.ι_f_zero_comp_complex_d I)
  change Limits.Pi.map (fun i : Fin (p + 1) → ι ↦
      (I.ι.f 0).hom.app
        (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))) ≫
    Limits.Pi.map (fun i : Fin (p + 1) → ι ↦
      (I.cocomplex.d 0 1).hom.app
        (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))) = 0
  rw [Limits.Pi.map_comp_map]
  refine Limits.Pi.hom_ext _ _ fun i ↦ ?_
  rw [Limits.Pi.map_π]
  have hi := congr_app h
    (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))
  have hi' :
      (I.ι.f 0).hom.app
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))) ≫
        (I.cocomplex.d 0 1).hom.app
          (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k))) = 0 := by
    change ((I.ι.f 0).hom ≫ (I.cocomplex.d 0 1).hom).app _ = 0
    exact hi.trans rfl
  rw [hi', comp_zero, zero_comp]

noncomputable instance cechInjectiveResolutionAugmentation_f_mono
    (F : Sheaf AddCommGrpCat.{u} X) (p : ℕ) :
    Mono ((cechInjectiveResolutionAugmentation U F).f p) := by
  change Mono (Limits.Pi.map (fun i : Fin (p + 1) → ι ↦
    ((injectiveResolution (toSiteSheaf F)).ι.f 0).hom.app
      (Opposite.op (∏ᶜ fun k : Fin (p + 1) ↦ U (i k)))))
  infer_instance

end

end TopCat.Sheaf

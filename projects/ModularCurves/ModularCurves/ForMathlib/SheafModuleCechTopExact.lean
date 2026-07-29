/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.SheafCechInjectiveComparison
import ModularCurves.ForMathlib.SheafModuleCechTopAugmentation
import ModularCurves.ForMathlib.SchemeModuleBaseCech

/-!
# Exactness of top sections of module-valued Cech complexes

Forgetting the coefficient-ring action identifies the native Cech complex of
a module-valued sheaf with the native additive Cech complex. Consequently,
the sheaf condition gives exactness at degree zero without losing the module
structure.
-/

open AlgebraicTopology CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace TopCat.Sheaf

variable {R : Type u} [CommRing R] {X : TopCat.{u}}
variable (F : Sheaf (ModuleCat.{u} R) X)
variable {ι : Type u} (U : ι → Opens X)

private abbrev moduleToAddCommGrp
    (R : Type u) [Ring R] :
    ModuleCat.{u} R ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

/-- A module-valued sheaf with its coefficient-ring action forgotten. -/
noncomputable def moduleForgetSheaf : Sheaf AddCommGrpCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X)
    (moduleToAddCommGrp R)).obj F

private noncomputable def moduleCechCosimplicialForgetIso :
    ((FormalCoproduct.cosimplicialObjectFunctor
        (FormalCoproduct.mk _ U).cech).obj F.obj ⋙
          moduleToAddCommGrp R) ≅
      (FormalCoproduct.cosimplicialObjectFunctor
        (FormalCoproduct.mk _ U).cech).obj
          (moduleForgetSheaf F).obj :=
  Functor.isoWhiskerLeft (FormalCoproduct.mk _ U).cech.rightOp
    (AlgebraicGeometry.Scheme.Modules.evalOpForgetIso R F.obj)

private theorem moduleCechComplex_d_succ (i : ℕ) :
    ((cechComplexFunctor U).obj F.obj).d i (i + 1) =
      AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor
          (FormalCoproduct.mk _ U).cech).obj F.obj) i := by
  change ((FormalCoproduct.cochainComplexFunctor
    (FormalCoproduct.mk _ U).cech).obj F.obj).d i (i + 1) = _
  rw [FormalCoproduct.cochainComplexFunctor_obj_d]
  exact (CochainComplex.of_d _ _ i).trans rfl

private theorem additiveCechComplex_d_succ (i : ℕ) :
    ((cechComplexFunctor U).obj (moduleForgetSheaf F).obj).d i (i + 1) =
      AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor
          (FormalCoproduct.mk _ U).cech).obj
            (moduleForgetSheaf F).obj) i := by
  change ((FormalCoproduct.cochainComplexFunctor
    (FormalCoproduct.mk _ U).cech).obj
      (moduleForgetSheaf F).obj).d i (i + 1) = _
  rw [FormalCoproduct.cochainComplexFunctor_obj_d]
  exact (CochainComplex.of_d _ _ i).trans rfl

private theorem moduleCechCosimplicialForgetIso_comm_d (i : ℕ) :
    (moduleCechCosimplicialForgetIso F U).hom.app
          (SimplexCategory.mk i) ≫
        AlternatingCofaceMapComplex.objD
          ((FormalCoproduct.cosimplicialObjectFunctor
            (FormalCoproduct.mk _ U).cech).obj
              (moduleForgetSheaf F).obj) i =
      (moduleToAddCommGrp R).map
          (AlternatingCofaceMapComplex.objD
            ((FormalCoproduct.cosimplicialObjectFunctor
              (FormalCoproduct.mk _ U).cech).obj F.obj) i) ≫
        (moduleCechCosimplicialForgetIso F U).hom.app
          (SimplexCategory.mk (i + 1)) := by
  simp only [AlternatingCofaceMapComplex.objD, Functor.map_sum,
    Functor.map_zsmul, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg ((-1 : ℤ) ^ (k : ℕ) • ·)
    ((moduleCechCosimplicialForgetIso F U).hom.naturality
      (SimplexCategory.δ k)).symm

/-- Forgetting the module structure on a native Cech complex gives the
native additive Cech complex of the forgotten sheaf. -/
noncomputable def moduleCechComplexForgetIso :
    (((moduleToAddCommGrp R).mapHomologicalComplex (.up ℕ)).obj
      ((cechComplexFunctor U).obj F.obj)) ≅
        (cechComplexFunctor U).obj (moduleForgetSheaf F).obj :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (moduleCechCosimplicialForgetIso F U).app
      (SimplexCategory.mk n)) (by
        intro i j hij
        simp only [ComplexShape.up_Rel] at hij
        subst j
        rw [Functor.mapHomologicalComplex_obj_d]
        rw [moduleCechComplex_d_succ, additiveCechComplex_d_succ]
        exact moduleCechCosimplicialForgetIso_comm_d F U i)

@[simp]
theorem moduleCechComplexForgetIso_hom_f (n : ℕ) :
    (moduleCechComplexForgetIso F U).hom.f n =
      (moduleCechCosimplicialForgetIso F U).hom.app
        (SimplexCategory.mk n) :=
  rfl

/-- The forgotten-complex comparison commutes with every product projection. -/
@[reassoc]
theorem moduleCechComplexForgetIso_hom_f_π
    (n : ℕ) (i : Fin (n + 1) → ι) :
    (moduleCechComplexForgetIso F U).hom.f n ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          (moduleToAddCommGrp R).obj
            (F.obj.obj (op (∏ᶜ fun k : Fin (n + 1) => U (j k))))) i =
      (moduleToAddCommGrp R).map
        (Pi.π (fun j : Fin (n + 1) → ι =>
          F.obj.obj (op (∏ᶜ fun k : Fin (n + 1) => U (j k)))) i) := by
  exact AlgebraicGeometry.Scheme.Modules.evalOpForgetIso_hom_π
    R F.obj
      ((FormalCoproduct.mk _ U).cech.rightOp.obj
        (SimplexCategory.mk n)) i

/-- The native module-valued Cech short complex augmented by top sections. -/
noncomputable def moduleCechTopSectionsNativeShortComplex :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (moduleCechTopSectionsAugmentation F U)
    (((cechComplexFunctor U).obj F.obj).d 0 1)
    (moduleCechTopSectionsAugmentation_comp_d F U)

private noncomputable def moduleCechTopSectionsMappedShortComplex :
    ShortComplex AddCommGrpCat.{u} :=
  (moduleCechTopSectionsNativeShortComplex F U).map
    (moduleToAddCommGrp R)

private noncomputable def moduleTopSectionsGlobalSectionsIso :
    (moduleCechTopSectionsMappedShortComplex F U).X₁ ≅
      (cechGlobalSectionsNativeShortComplex U
        (moduleForgetSheaf F)).X₁ :=
  ((CategoryTheory.Sheaf.ΓNatIsoSheafSections
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      isTerminalTop).app (moduleForgetSheaf F)).symm

private noncomputable def moduleCechForgetXIso (n : ℕ) :
    (moduleToAddCommGrp R).obj
        (((cechComplexFunctor U).obj F.obj).X n) ≅
      ((cechComplexFunctor U).obj (moduleForgetSheaf F).obj).X n :=
  (HomologicalComplex.eval _ _ n).mapIso
    (moduleCechComplexForgetIso F U)

private theorem moduleCechTopSectionsMapped_comm :
    (moduleTopSectionsGlobalSectionsIso F U).hom ≫
        (cechGlobalSectionsNativeShortComplex U
          (moduleForgetSheaf F)).f =
      (moduleCechTopSectionsMappedShortComplex F U).f ≫
        (moduleCechForgetXIso F U 0).hom := by
  apply Pi.hom_ext
  intro i
  change Fin 1 → ι at i
  change
    ((moduleTopSectionsGlobalSectionsIso F U).hom ≫
        (cechGlobalSectionsNativeShortComplex U
          (moduleForgetSheaf F)).f) ≫
        Pi.π (fun j : Fin 1 → ι =>
          (moduleForgetSheaf F).obj.obj
            (op (∏ᶜ fun k : Fin 1 => U (j k)))) i =
      ((moduleCechTopSectionsMappedShortComplex F U).f ≫
        (moduleCechForgetXIso F U 0).hom) ≫
        Pi.π (fun j : Fin 1 → ι =>
          (moduleForgetSheaf F).obj.obj
            (op (∏ᶜ fun k : Fin 1 => U (j k)))) i
  have hAssocRight :
      ((moduleCechTopSectionsMappedShortComplex F U).f ≫
          (moduleCechForgetXIso F U 0).hom) ≫
        Pi.π (fun j : Fin 1 → ι =>
          (moduleForgetSheaf F).obj.obj
            (op (∏ᶜ fun k : Fin 1 => U (j k)))) i =
      (moduleCechTopSectionsMappedShortComplex F U).f ≫
        ((moduleCechForgetXIso F U 0).hom ≫
          Pi.π (fun j : Fin 1 → ι =>
            (moduleForgetSheaf F).obj.obj
              (op (∏ᶜ fun k : Fin 1 => U (j k)))) i) :=
    Category.assoc _ _ _
  erw [Category.assoc]
  erw [hAssocRight]
  erw [moduleCechComplexForgetIso_hom_f_π]
  erw [← (moduleToAddCommGrp R).map_comp,
    moduleCechTopSectionsAugmentation_π]
  ext x
  have hadd := cechGlobalSectionsAugmentation_apply
    (moduleForgetSheaf F) U
      ((moduleTopSectionsGlobalSectionsIso F U).hom x) i
  have hΓ :
      (CategoryTheory.Sheaf.ΓNatIsoSheafSections
        (Opens.grothendieckTopology X) AddCommGrpCat.{u}
          isTerminalTop).hom.app (moduleForgetSheaf F)
            ((moduleTopSectionsGlobalSectionsIso F U).hom x) = x := by
    let eΓ := (CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{u}
        isTerminalTop).app (moduleForgetSheaf F)
    change eΓ.hom (eΓ.inv x) = x
    exact eΓ.inv_hom_id_apply x
  rw [hΓ] at hadd
  rw [cechCochainAddEquiv_apply] at hadd
  change
    Pi.π (fun j : Fin 1 → ι =>
        (moduleForgetSheaf F).obj.obj
          (op (∏ᶜ fun k : Fin 1 => U (j k)))) i
      (cechGlobalSectionsAugmentation (moduleForgetSheaf F) U
        ((moduleTopSectionsGlobalSectionsIso F U).hom x)) =
      (moduleForgetSheaf F).obj.map
        (homOfLE (show
          (∏ᶜ fun k : Fin 1 => U (i k)) ≤ ⊤ from le_top)).op x
  exact hadd

private noncomputable def moduleCechTopSectionsMappedIso :
    moduleCechTopSectionsMappedShortComplex F U ≅
      cechGlobalSectionsNativeShortComplex U (moduleForgetSheaf F) :=
  ShortComplex.isoMk
    (moduleTopSectionsGlobalSectionsIso F U)
    (moduleCechForgetXIso F U 0)
    (moduleCechForgetXIso F U 1)
    (moduleCechTopSectionsMapped_comm F U)
    ((moduleCechComplexForgetIso F U).hom.comm 0 1)

/-- The native module-valued Cech short complex augmented by top sections is
exact for an open cover. -/
theorem moduleCechTopSectionsNativeShortComplex_exact
    (hU : ⨆ i, U i = ⊤) :
    (moduleCechTopSectionsNativeShortComplex F U).Exact := by
  apply (ShortComplex.exact_iff_exact_map_forget₂
    (S := moduleCechTopSectionsNativeShortComplex F U)).mpr
  exact ShortComplex.exact_of_iso
    (moduleCechTopSectionsMappedIso F U).symm
    (cechGlobalSectionsNativeShortComplex_exact U
      (moduleForgetSheaf F) hU)

/-- Restriction from top sections to Cech degree zero is monic for an open
cover. -/
theorem moduleCechTopSectionsAugmentation_mono
    (hU : ⨆ i, U i = ⊤) :
    Mono (moduleCechTopSectionsAugmentation F U) := by
  have hnative : Mono
      (cechGlobalSectionsNativeShortComplex U
        (moduleForgetSheaf F)).f := by
    change Mono (cechGlobalSectionsAugmentation
      (moduleForgetSheaf F) U)
    exact
    cechGlobalSectionsAugmentation_mono U
      (moduleForgetSheaf F) hU
  have htop : Mono (moduleTopSectionsGlobalSectionsIso F U).hom := by
    infer_instance
  have hleft : Mono ((moduleTopSectionsGlobalSectionsIso F U).hom ≫
      (cechGlobalSectionsNativeShortComplex U
        (moduleForgetSheaf F)).f) :=
    mono_comp' htop hnative
  have hcomp : Mono ((moduleCechTopSectionsMappedShortComplex F U).f ≫
      (moduleCechForgetXIso F U 0).hom) := by
    rw [← moduleCechTopSectionsMapped_comm]
    exact hleft
  letI : Mono ((moduleCechTopSectionsMappedShortComplex F U).f ≫
      (moduleCechForgetXIso F U 0).hom) := hcomp
  have hmap : Mono
      (moduleCechTopSectionsMappedShortComplex F U).f :=
    mono_of_mono_fac (show
      (moduleCechTopSectionsMappedShortComplex F U).f ≫
          (moduleCechForgetXIso F U 0).hom =
        (moduleCechTopSectionsMappedShortComplex F U).f ≫
          (moduleCechForgetXIso F U 0).hom from rfl)
  exact Functor.mono_of_mono_map (moduleToAddCommGrp R) hmap

end TopCat.Sheaf

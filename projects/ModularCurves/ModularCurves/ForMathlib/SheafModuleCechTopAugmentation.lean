/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.SheafModuleCechAugmentation
import ModularCurves.ForMathlib.SheafModuleCechTopComplex

/-!
# Top sections of module-valued sheaf Cech augmentations

The canonical restriction from top sections of a module-valued sheaf to
degree zero of its native Cech complex is natural in the sheaf and lands in
the kernel of the first differential.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace TopCat.Sheaf

variable {R : Type u} [CommRing R] {X : TopCat.{u}}
variable (F : Sheaf (ModuleCat.{u} R) X)
variable {ι : Type u} (U : ι → Opens X)

/-- Restriction from top sections of a module-valued sheaf to degree zero of
its native Cech complex. -/
noncomputable def moduleCechTopSectionsAugmentation :
    F.obj.obj (op ⊤) ⟶ ((cechComplexFunctor U).obj F.obj).X 0 :=
  (moduleCechAugmentation F U).hom.app (op ⊤) ≫
    (moduleCechTermTopSectionsIso F U 0).hom

/-- The projection of the top-sections Cech augmentation to one cover member
is the ordinary restriction map. -/
theorem moduleCechTopSectionsAugmentation_π
    (i : Fin 1 → ι) :
    moduleCechTopSectionsAugmentation F U ≫
        Pi.π (fun j : Fin 1 → ι =>
          F.obj.obj (op (∏ᶜ fun k : Fin 1 => U (j k)))) i =
      F.obj.map (homOfLE (show
        (∏ᶜ fun k : Fin 1 => U (i k)) ≤ ⊤ from le_top)).op := by
  rw [moduleCechTopSectionsAugmentation]
  erw [Category.assoc]
  erw [moduleCechTermTopSectionsIso_hom_π]
  erw [← Category.assoc]
  have haugmentation :
      (moduleCechAugmentation F U).hom.app (op ⊤) ≫
          (Pi.π (moduleCechTermFactor F U 0) i).hom.app (op ⊤) =
        ((toRestrict (ModuleCat R)
          (∏ᶜ fun k : Fin 1 => U (i k))).app F).hom.app (op ⊤) := by
    exact congrArg (fun f => f.hom.app (op ⊤))
      (Pi.lift_π (fun j : Fin 1 → ι =>
        (toRestrict (ModuleCat R)
          (∏ᶜ fun k : Fin 1 => U (j k))).app F) i)
  rw [haugmentation]
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _
  rw [← F.obj.map_comp]
  exact congrArg F.obj.map (Subsingleton.elim _ _)

/-- The top-sections Cech augmentation is natural in the module-valued
sheaf. -/
theorem moduleCechTopSectionsAugmentation_naturality
    {G : Sheaf (ModuleCat.{u} R) X} (f : F ⟶ G) :
    moduleCechTopSectionsAugmentation F U ≫
        ((cechComplexFunctor U).map f.hom).f 0 =
      f.hom.app (op ⊤) ≫ moduleCechTopSectionsAugmentation G U := by
  apply Pi.hom_ext
  intro i
  change Fin 1 → ι at i
  change
    (moduleCechTopSectionsAugmentation F U ≫
        ((cechComplexFunctor U).map f.hom).f 0) ≫
      Pi.π (fun j : Fin 1 → ι =>
        G.obj.obj (op (∏ᶜ fun k : Fin 1 => U (j k)))) i =
    (f.hom.app (op ⊤) ≫ moduleCechTopSectionsAugmentation G U) ≫
      Pi.π (fun j : Fin 1 → ι =>
        G.obj.obj (op (∏ᶜ fun k : Fin 1 => U (j k)))) i
  have hnative :
      ((cechComplexFunctor U).map f.hom).f 0 ≫
          Pi.π (fun j : Fin 1 → ι =>
            G.obj.obj (op (∏ᶜ fun k : Fin 1 => U (j k)))) i =
        Pi.π (fun j : Fin 1 → ι =>
            F.obj.obj (op (∏ᶜ fun k : Fin 1 => U (j k)))) i ≫
          f.hom.app (op (∏ᶜ fun k : Fin 1 => U (i k))) := by
    change Limits.Pi.map (fun j : Fin 1 → ι =>
      f.hom.app (op (∏ᶜ fun k : Fin 1 => U (j k)))) ≫ _ = _
    exact Limits.Pi.map_π _ i
  have hAssocLeft :
      (moduleCechTopSectionsAugmentation F U ≫
          ((cechComplexFunctor U).map f.hom).f 0) ≫
        Pi.π (fun j : Fin 1 → ι =>
          G.obj.obj (op (∏ᶜ fun k : Fin 1 => U (j k)))) i =
      moduleCechTopSectionsAugmentation F U ≫
        (((cechComplexFunctor U).map f.hom).f 0 ≫
          Pi.π (fun j : Fin 1 → ι =>
            G.obj.obj (op (∏ᶜ fun k : Fin 1 => U (j k)))) i) :=
    Category.assoc _ _ _
  have hAssocRight :
      (f.hom.app (op ⊤) ≫ moduleCechTopSectionsAugmentation G U) ≫
          Pi.π (fun j : Fin 1 → ι =>
            G.obj.obj (op (∏ᶜ fun k : Fin 1 => U (j k)))) i =
        f.hom.app (op ⊤) ≫
          (moduleCechTopSectionsAugmentation G U ≫
            Pi.π (fun j : Fin 1 → ι =>
              G.obj.obj (op (∏ᶜ fun k : Fin 1 => U (j k)))) i) :=
    Category.assoc _ _ _
  rw [hAssocLeft, hAssocRight, hnative]
  have hAssocProjectionLeft :
      moduleCechTopSectionsAugmentation F U ≫
          (Pi.π (fun j : Fin 1 → ι =>
              F.obj.obj (op (∏ᶜ fun k : Fin 1 => U (j k)))) i ≫
            f.hom.app (op (∏ᶜ fun k : Fin 1 => U (i k)))) =
        (moduleCechTopSectionsAugmentation F U ≫
            Pi.π (fun j : Fin 1 → ι =>
              F.obj.obj (op (∏ᶜ fun k : Fin 1 => U (j k)))) i) ≫
          f.hom.app (op (∏ᶜ fun k : Fin 1 => U (i k))) :=
    (Category.assoc _ _ _).symm
  erw [hAssocProjectionLeft,
    moduleCechTopSectionsAugmentation_π,
    moduleCechTopSectionsAugmentation_π]
  exact f.hom.naturality (homOfLE le_top).op

/-- The top-sections Cech augmentation followed by the first native
differential is zero. -/
@[reassoc]
theorem moduleCechTopSectionsAugmentation_comp_d :
    moduleCechTopSectionsAugmentation F U ≫
        ((cechComplexFunctor U).obj F.obj).d 0 1 = 0 := by
  rw [moduleCechTopSectionsAugmentation, Category.assoc,
    moduleCechTermTopSectionsIso_comp_d]
  rw [← Category.assoc]
  have hzero :
      (moduleCechAugmentation F U).hom.app (op ⊤) ≫
          (moduleCechDifferential F U 0).hom.app (op ⊤) = 0 := by
    change (moduleCechAugmentation F U ≫
      moduleCechDifferential F U 0).hom.app (op ⊤) = 0
    rw [moduleCechAugmentation_comp]
    rfl
  rw [hzero, zero_comp]

end TopCat.Sheaf

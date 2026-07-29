/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.SheafModuleCechTopSections

/-!
# Top sections of module-valued sheaf Cech complexes

The degreewise comparison between top sections of the sheaf-level Cech
complex and the native module-valued Cech complex commutes with cofaces and
differentials.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace TopCat.Sheaf

variable {R : Type u} [CommRing R] {X : TopCat.{u}}
variable (F : Sheaf (ModuleCat.{u} R) X)
variable {ι : Type u} (U : ι → Opens X)

attribute [local instance] moduleCechSheafPreadditive

private abbrev moduleSheafTopSectionsFunctor :
    Sheaf (ModuleCat.{u} R) X ⥤ ModuleCat.{u} R :=
  forget (ModuleCat R) X ⋙
    (evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op ⊤)

noncomputable local instance moduleSheafTopSectionsFunctor_additive :
    (moduleSheafTopSectionsFunctor (R := R) (X := X)).Additive where
  map_add := by
    intro A B f g
    rfl

private noncomputable def moduleNativeCechCoface
    (n : ℕ) (k : Fin (n + 2)) :
    ((cechComplexFunctor U).obj F.obj).X n ⟶
      ((cechComplexFunctor U).obj F.obj).X (n + 1) :=
  Pi.lift fun i : Fin (n + 2) → ι =>
    Pi.π (fun j : Fin (n + 1) → ι =>
        F.obj.obj (op (∏ᶜ fun a : Fin (n + 1) => U (j a))))
        (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
      F.obj.map (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ i).op

private theorem nativeCoface_eq_moduleNativeCechCoface
    (n : ℕ) (k : Fin (n + 2)) :
    ((FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.mk _ U).cech).obj F.obj).δ k =
      moduleNativeCechCoface F U n k := by
  rw [CosimplicialObject.δ,
    FormalCoproduct.cosimplicialObjectFunctor_obj_map,
    FormalCoproduct.cech_map]
  rfl

private theorem moduleNativeCechDifferential_eq
    (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).d n (n + 1) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        moduleNativeCechCoface F U n k := by
  change ((FormalCoproduct.cochainComplexFunctor
    (FormalCoproduct.mk _ U).cech).obj F.obj).d n (n + 1) = _
  rw [FormalCoproduct.cochainComplexFunctor_obj_d]
  refine (CochainComplex.of_d _ _ n).trans ?_
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun f => (-1 : ℤ) ^ (k : ℕ) • f)
    (nativeCoface_eq_moduleNativeCechCoface F U n k)

private theorem moduleCechTermFactorTopIso_restriction
    (n : ℕ) (k : Fin (n + 2)) (i : Fin (n + 2) → ι)
    (h : (∏ᶜ fun a : Fin (n + 2) => U (i a)) ≤
      ∏ᶜ fun a : Fin (n + 1) =>
        U ((i ∘ (SimplexCategory.δ k).toOrderHom.toFun) a)) :
    (moduleCechTermFactorRestriction F h).hom.app (op ⊤) ≫
        (moduleCechTermFactorTopIso F U (n + 1) i).hom =
      (moduleCechTermFactorTopIso F U n
          (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom ≫
        F.obj.map (homOfLE h).op := by
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
  rw [← F.obj.map_comp, ← F.obj.map_comp]
  exact congrArg F.obj.map (Subsingleton.elim _ _)

/-- The top-sections comparison commutes with each Cech coface. -/
theorem moduleCechTermTopSectionsIso_comp_coface
    (n : ℕ) (k : Fin (n + 2)) :
    (moduleCechTermTopSectionsIso F U n).hom ≫
        moduleNativeCechCoface F U n k =
      (moduleCechCoface F U n k).hom.app (op ⊤) ≫
        (moduleCechTermTopSectionsIso F U (n + 1)).hom := by
  refine Pi.hom_ext
    (f := fun j : Fin (n + 2) → ι =>
      F.obj.obj (op (∏ᶜ fun a : Fin (n + 2) => U (j a))))
    (X := (moduleCechTerm F U n).obj.obj (op ⊤)) _ _ ?_
  intro i
  change (Fin (n + 2) → ι) at i
  let h :
      (∏ᶜ fun a : Fin (n + 2) => U (i a)) ≤
        ∏ᶜ fun a : Fin (n + 1) =>
          U ((i ∘ (SimplexCategory.δ k).toOrderHom.toFun) a) :=
    leOfHom (((FormalCoproduct.mk _ U).mapPower
      (SimplexCategory.δ k).toOrderHom.toFun).φ i)
  have hcoface :
      moduleCechCoface F U n k ≫
          Pi.π (moduleCechTermFactor F U (n + 1)) i =
        Pi.π (moduleCechTermFactor F U n)
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
          moduleCechTermFactorRestriction F h := by
    unfold moduleCechCoface moduleCechTerm
    exact Pi.lift_π _ i
  have hcofaceTop := congrArg (fun f => f.hom.app (op ⊤)) hcoface
  have hcofaceTop' :
      (moduleCechCoface F U n k).hom.app (op ⊤) ≫
          (Pi.π (moduleCechTermFactor F U (n + 1)) i).hom.app
            (op ⊤) =
        (Pi.π (moduleCechTermFactor F U n)
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom.app
              (op ⊤) ≫
          (moduleCechTermFactorRestriction F h).hom.app (op ⊤) :=
    hcofaceTop
  have hfactor :=
    moduleCechTermFactorTopIso_restriction F U n k i h
  have hmap :
      F.obj.map (homOfLE h).op =
        F.obj.map (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ i).op :=
    congrArg F.obj.map (Subsingleton.elim _ _)
  have hnative :
      moduleNativeCechCoface F U n k ≫
          Pi.π (fun j : Fin (n + 2) → ι =>
            F.obj.obj (op (∏ᶜ fun a : Fin (n + 2) => U (j a)))) i =
        Pi.π (fun j : Fin (n + 1) → ι =>
            F.obj.obj (op (∏ᶜ fun a : Fin (n + 1) => U (j a))))
              (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
          F.obj.map (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i).op := by
    unfold moduleNativeCechCoface
    exact Pi.lift_π _ i
  change
    ((moduleCechTermTopSectionsIso F U n).hom ≫
        moduleNativeCechCoface F U n k) ≫
      Pi.π (fun j : Fin (n + 2) → ι =>
        F.obj.obj (op (∏ᶜ fun a : Fin (n + 2) => U (j a)))) i =
    ((moduleCechCoface F U n k).hom.app (op ⊤) ≫
        (moduleCechTermTopSectionsIso F U (n + 1)).hom) ≫
      Pi.π (fun j : Fin (n + 2) → ι =>
        F.obj.obj (op (∏ᶜ fun a : Fin (n + 2) => U (j a)))) i
  have hAssocLeft :
      ((moduleCechTermTopSectionsIso F U n).hom ≫
          moduleNativeCechCoface F U n k) ≫
        Pi.π (fun j : Fin (n + 2) → ι =>
          F.obj.obj (op (∏ᶜ fun a : Fin (n + 2) => U (j a)))) i =
      (moduleCechTermTopSectionsIso F U n).hom ≫
        (moduleNativeCechCoface F U n k ≫
          Pi.π (fun j : Fin (n + 2) → ι =>
            F.obj.obj (op (∏ᶜ fun a : Fin (n + 2) => U (j a)))) i) :=
    Category.assoc _ _ _
  have hAssocRight :
      ((moduleCechCoface F U n k).hom.app (op ⊤) ≫
          (moduleCechTermTopSectionsIso F U (n + 1)).hom) ≫
        Pi.π (fun j : Fin (n + 2) → ι =>
          F.obj.obj (op (∏ᶜ fun a : Fin (n + 2) => U (j a)))) i =
      (moduleCechCoface F U n k).hom.app (op ⊤) ≫
        ((moduleCechTermTopSectionsIso F U (n + 1)).hom ≫
          Pi.π (fun j : Fin (n + 2) → ι =>
            F.obj.obj (op (∏ᶜ fun a : Fin (n + 2) => U (j a)))) i) :=
    Category.assoc _ _ _
  rw [hAssocLeft, hAssocRight, hnative]
  have hAssocProjectionLeft :
      (moduleCechTermTopSectionsIso F U n).hom ≫
          (Pi.π (fun j : Fin (n + 1) → ι =>
              F.obj.obj (op (∏ᶜ fun a : Fin (n + 1) => U (j a))))
                (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
            F.obj.map (((FormalCoproduct.mk _ U).mapPower
              (SimplexCategory.δ k).toOrderHom.toFun).φ i).op) =
        ((moduleCechTermTopSectionsIso F U n).hom ≫
            Pi.π (fun j : Fin (n + 1) → ι =>
              F.obj.obj (op (∏ᶜ fun a : Fin (n + 1) => U (j a))))
                (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)) ≫
          F.obj.map (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i).op :=
    (Category.assoc _ _ _).symm
  have hProjectionLeft :=
    moduleCechTermTopSectionsIso_hom_π F U n
      (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)
  have hProjectionRight :=
    moduleCechTermTopSectionsIso_hom_π F U (n + 1) i
  erw [hAssocProjectionLeft, hProjectionLeft, hProjectionRight]
  have hAssocFactorLeft :
      ((Pi.π (moduleCechTermFactor F U n)
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom.app
              (op ⊤) ≫
          (moduleCechTermFactorTopIso F U n
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom) ≫
        F.obj.map (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ i).op =
      (Pi.π (moduleCechTermFactor F U n)
          (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom.app
            (op ⊤) ≫
        ((moduleCechTermFactorTopIso F U n
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom ≫
          F.obj.map (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i).op) :=
    Category.assoc _ _ _
  have hAssocCofaceRight :
      (moduleCechCoface F U n k).hom.app (op ⊤) ≫
          ((Pi.π (moduleCechTermFactor F U (n + 1)) i).hom.app
              (op ⊤) ≫
            (moduleCechTermFactorTopIso F U (n + 1) i).hom) =
        ((moduleCechCoface F U n k).hom.app (op ⊤) ≫
            (Pi.π (moduleCechTermFactor F U (n + 1)) i).hom.app
              (op ⊤)) ≫
          (moduleCechTermFactorTopIso F U (n + 1) i).hom :=
    (Category.assoc _ _ _).symm
  erw [hAssocFactorLeft, hAssocCofaceRight, hcofaceTop']
  have hAssocRestrictionRight :
      ((Pi.π (moduleCechTermFactor F U n)
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom.app
              (op ⊤) ≫
          (moduleCechTermFactorRestriction F h).hom.app (op ⊤)) ≫
        (moduleCechTermFactorTopIso F U (n + 1) i).hom =
      (Pi.π (moduleCechTermFactor F U n)
          (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)).hom.app
            (op ⊤) ≫
        ((moduleCechTermFactorRestriction F h).hom.app (op ⊤) ≫
          (moduleCechTermFactorTopIso F U (n + 1) i).hom) :=
    Category.assoc _ _ _
  erw [hAssocRestrictionRight, hfactor, hmap]
  rfl

/-- The top-sections comparison commutes with the Cech differential. -/
theorem moduleCechTermTopSectionsIso_comp_d
    (n : ℕ) :
    (moduleCechTermTopSectionsIso F U n).hom ≫
        ((cechComplexFunctor U).obj F.obj).d n (n + 1) =
      (moduleCechDifferential F U n).hom.app (op ⊤) ≫
        (moduleCechTermTopSectionsIso F U (n + 1)).hom := by
  rw [moduleNativeCechDifferential_eq, moduleCechDifferential]
  have hmap :
      ((∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        moduleCechCoface F U n k).hom.app (op ⊤)) =
        ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
          (moduleCechCoface F U n k).hom.app (op ⊤) := by
    change (moduleSheafTopSectionsFunctor
      (R := R) (X := X)).map
        (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
          moduleCechCoface F U n k) = _
    exact Functor.map_sum _ _ Finset.univ
  rw [hmap]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun f => (-1 : ℤ) ^ (k : ℕ) • f)
    (moduleCechTermTopSectionsIso_comp_coface F U n k)

/-- Taking top sections degreewise in the module-valued sheaf Cech complex
gives the native module-valued Cech complex. -/
noncomputable def moduleCechTopSectionsComplexIso :
    ((moduleSheafTopSectionsFunctor (R := R) (X := X)).mapHomologicalComplex
      (.up ℕ)).obj (moduleCechComplex F U) ≅
        (cechComplexFunctor U).obj F.obj :=
  HomologicalComplex.Hom.isoOfComponents
    (moduleCechTermTopSectionsIso F U) (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      subst j
      change (moduleCechTermTopSectionsIso F U i).hom ≫
          ((cechComplexFunctor U).obj F.obj).d i (i + 1) =
        ((moduleCechComplex F U).d i (i + 1)).hom.app (op ⊤) ≫
          (moduleCechTermTopSectionsIso F U (i + 1)).hom
      rw [moduleCechComplex_d]
      exact moduleCechTermTopSectionsIso_comp_d F U i)

end TopCat.Sheaf

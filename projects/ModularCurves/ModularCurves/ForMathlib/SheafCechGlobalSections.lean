import ModularCurves.ForMathlib.SheafCohomologyFiniteProducts
import ModularCurves.ForMathlib.SheafDerivedGlobalSections

/-!
# Global sections of the sheaf-level Cech complex

This file identifies the complex obtained by applying global sections degreewise to the
sheaf-level Cech resolution with mathlib's native Cech complex of the underlying
presheaf. The comparison is compatible with the Cech differentials.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

noncomputable section

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)

private abbrev globalSections (X : TopCat.{u}) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      AddCommGrpCat.{u} :=
  CategoryTheory.Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}

noncomputable local instance : (globalSections X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

private noncomputable def cechTopSectionsAddEquiv (n : ℕ) :
    (cechTerm F U n).obj.obj (op ⊤) ≃+
      ((cechComplexFunctor U).obj F.obj).X n := by
  exact (cechTermSectionsAddEquiv F U n (⊤ : Opens X)).trans <|
    (AddEquiv.piCongrRight fun i =>
      (F.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun k : Fin (n + 1) => U (i k)))))).addCommGroupIsoToAddEquiv).trans <|
      (cechCochainAddEquiv F.obj U n).symm

private theorem cechTopSectionsAddEquiv_apply (n : ℕ)
    (x : (cechTerm F U n).obj.obj (op ⊤))
    (i : Fin (n + 1) → ι) :
    cechCochainAddEquiv F.obj U n (cechTopSectionsAddEquiv F U n x) i =
      (F.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun k : Fin (n + 1) => U (i k)))))).hom
          (cechTermSectionsAddEquiv F U n (⊤ : Opens X) x i) := by
  let y := (AddEquiv.piCongrRight fun i =>
    (F.obj.mapIso (eqToIso (congrArg op
      (top_inf_eq (∏ᶜ fun k : Fin (n + 1) => U (i k)))))).addCommGroupIsoToAddEquiv)
        (cechTermSectionsAddEquiv F U n (⊤ : Opens X) x)
  exact congrFun ((cechCochainAddEquiv F.obj U n).apply_symm_apply y) i

private theorem addCommGrp_hom_map_sum {A B : AddCommGrpCat.{u}} {κ : Type*}
    [Fintype κ] (f : A ⟶ B) (x : κ → A) :
    ConcreteCategory.hom f (∑ k, x k) =
      ∑ k, ConcreteCategory.hom f (x k) :=
  by simp

private theorem cechTopRestriction_apply (n : ℕ) (k : Fin (n + 2))
    (i : Fin (n + 2) → ι)
    (x : F.obj.obj (op ((⊤ : Opens X) ⊓
      ∏ᶜ fun a : Fin (n + 1) =>
        U ((i ∘ (SimplexCategory.δ k).toOrderHom.toFun) a)))) :
    F.obj.map (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ i).op
        ((F.obj.mapIso (eqToIso (congrArg op
          (top_inf_eq (∏ᶜ fun a : Fin (n + 1) =>
            U ((i ∘ (SimplexCategory.δ k).toOrderHom.toFun) a)))))).hom x) =
      (F.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun a : Fin (n + 2) => U (i a)))))).hom
        (F.obj.map (homOfLE (inf_le_inf_left (⊤ : Opens X)
          (leOfHom (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op x) := by
  have h :
      F.obj.map (eqToIso (congrArg op
          (top_inf_eq (∏ᶜ fun a : Fin (n + 1) =>
            U ((i ∘ (SimplexCategory.δ k).toOrderHom.toFun) a))))).hom ≫
          F.obj.map (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i).op =
        F.obj.map (homOfLE (inf_le_inf_left (⊤ : Opens X)
            (leOfHom (((FormalCoproduct.mk _ U).mapPower
              (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op ≫
          F.obj.map (eqToIso (congrArg op
            (top_inf_eq (∏ᶜ fun a : Fin (n + 2) => U (i a))))).hom := by
    rw [← F.obj.map_comp, ← F.obj.map_comp]
    exact congrArg F.obj.map (Subsingleton.elim _ _)
  exact ConcreteCategory.congr_hom h x

private theorem cechTopCofaceSummand_apply (n : ℕ) (k : Fin (n + 2))
    (i : Fin (n + 2) → ι) (x : (cechTerm F U n).obj.obj (op ⊤)) :
    (-1 : ℤ) ^ (k : ℕ) •
        F.obj.map (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ i).op
          (cechCochainAddEquiv F.obj U n (cechTopSectionsAddEquiv F U n x)
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)) =
      (F.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun r : Fin (n + 2) => U (i r)))))).hom
        ((-1 : ℤ) ^ (k : ℕ) •
          F.obj.map (homOfLE (inf_le_inf_left (⊤ : Opens X)
            (leOfHom (((FormalCoproduct.mk _ U).mapPower
              (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op
            (cechTermSectionsAddEquiv F U n (⊤ : Opens X) x
              (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))) := by
  calc
    _ = (-1 : ℤ) ^ (k : ℕ) •
        F.obj.map (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ i).op
          ((F.obj.mapIso (eqToIso (congrArg op
            (top_inf_eq (∏ᶜ fun r : Fin (n + 1) =>
              U ((i ∘ (SimplexCategory.δ k).toOrderHom.toFun) r)))))).hom
            (cechTermSectionsAddEquiv F U n (⊤ : Opens X) x
              (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))) :=
      congrArg (fun y => (-1 : ℤ) ^ (k : ℕ) •
        F.obj.map (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ i).op y)
            (cechTopSectionsAddEquiv_apply (F := F) (U := U) n x _)
    _ = (-1 : ℤ) ^ (k : ℕ) •
        (F.obj.mapIso (eqToIso (congrArg op
          (top_inf_eq (∏ᶜ fun r : Fin (n + 2) => U (i r)))))).hom
          (F.obj.map (homOfLE (inf_le_inf_left (⊤ : Opens X)
            (leOfHom (((FormalCoproduct.mk _ U).mapPower
              (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op
            (cechTermSectionsAddEquiv F U n (⊤ : Opens X) x
              (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))) :=
      congrArg (fun y => (-1 : ℤ) ^ (k : ℕ) • y)
        (cechTopRestriction_apply (F := F) (U := U) n k i _)
    _ = _ := (map_zsmul
      (F.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun r : Fin (n + 2) => U (i r)))))).hom.hom
      ((-1 : ℤ) ^ (k : ℕ)) _).symm

private theorem cechTopAlternatingSum_apply (n : ℕ) (i : Fin (n + 2) → ι)
    (x : (cechTerm F U n).obj.obj (op ⊤)) :
    (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        F.obj.map (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ i).op
          (cechCochainAddEquiv F.obj U n (cechTopSectionsAddEquiv F U n x)
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))) =
      (F.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun r : Fin (n + 2) => U (i r)))))).hom
        (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
          F.obj.map (homOfLE (inf_le_inf_left (⊤ : Opens X)
            (leOfHom (((FormalCoproduct.mk _ U).mapPower
              (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op
            (cechTermSectionsAddEquiv F U n (⊤ : Opens X) x
              (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))) := by
  let f := (F.obj.mapIso (eqToIso (congrArg op
    (top_inf_eq (∏ᶜ fun r : Fin (n + 2) => U (i r)))))).hom
  let a := fun k : Fin (n + 2) => (-1 : ℤ) ^ (k : ℕ) •
    F.obj.map (homOfLE (inf_le_inf_left (⊤ : Opens X)
      (leOfHom (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op
      (cechTermSectionsAddEquiv F U n (⊤ : Opens X) x
        (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))
  calc
    _ = ∑ k, ConcreteCategory.hom f (a k) :=
      Finset.sum_congr rfl (fun k _ =>
        cechTopCofaceSummand_apply (F := F) (U := U) n k i x)
    _ = ConcreteCategory.hom f (∑ k, a k) :=
      (addCommGrp_hom_map_sum f a).symm

private theorem cechTopSectionsAddEquiv_d (n : ℕ) :
    (cechTopSectionsAddEquiv F U n).toAddCommGrpIso.hom ≫
        ((cechComplexFunctor U).obj F.obj).d n (n + 1) =
      (cechDifferential F U n).hom.app (op ⊤) ≫
        (cechTopSectionsAddEquiv F U (n + 1)).toAddCommGrpIso.hom := by
  ext x
  apply (cechCochainAddEquiv F.obj U (n + 1)).injective
  funext i
  change cechCochainAddEquiv F.obj U (n + 1)
      (((cechComplexFunctor U).obj F.obj).d n (n + 1)
        (cechTopSectionsAddEquiv F U n x)) i =
    cechCochainAddEquiv F.obj U (n + 1)
      (cechTopSectionsAddEquiv F U (n + 1)
        ((cechDifferential F U n).hom.app (op ⊤) x)) i
  calc
    _ = ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        F.obj.map (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ i).op
          (cechCochainAddEquiv F.obj U n (cechTopSectionsAddEquiv F U n x)
            (i ∘ (SimplexCategory.δ k).toOrderHom.toFun)) :=
      TopologicalSpace.cechDifferential_apply F.obj U n
        (cechTopSectionsAddEquiv F U n x) i
    _ = (F.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun r : Fin (n + 2) => U (i r)))))).hom
        (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
          F.obj.map (homOfLE (inf_le_inf_left (⊤ : Opens X)
            (leOfHom (((FormalCoproduct.mk _ U).mapPower
              (SimplexCategory.δ k).toOrderHom.toFun).φ i)))).op
            (cechTermSectionsAddEquiv F U n (⊤ : Opens X) x
              (i ∘ (SimplexCategory.δ k).toOrderHom.toFun))) :=
      cechTopAlternatingSum_apply (F := F) (U := U) n i x
    _ = (F.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun r : Fin (n + 2) => U (i r)))))).hom
        (cechTermSectionsAddEquiv F U (n + 1) (⊤ : Opens X)
          ((cechDifferential F U n).hom.app (op ⊤) x) i) :=
      congrArg _ (cechDifferential_apply F U n (⊤ : Opens X) x i).symm
    _ = _ := (cechTopSectionsAddEquiv_apply (F := F) (U := U) (n + 1)
      ((cechDifferential F U n).hom.app (op ⊤) x) i).symm

/-- Global sections of a sheaf-level Cech term agree with the corresponding term of
the native Cech complex of the underlying presheaf. -/
noncomputable def cechGlobalSectionsXIso (n : ℕ) :
    (globalSections X).obj (cechTerm F U n) ≅
      ((cechComplexFunctor U).obj F.obj).X n :=
  (CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).app
        (cechTerm F U n) ≪≫
    (cechTopSectionsAddEquiv F U n).toAddCommGrpIso

/-- Applying global sections degreewise to the sheaf-level Cech complex gives the
native Cech complex of the underlying presheaf. -/
noncomputable def cechGlobalSectionsComplexIso :
    ((globalSections X).mapHomologicalComplex (.up ℕ)).obj (cechComplex F U) ≅
      (cechComplexFunctor U).obj F.obj :=
  HomologicalComplex.Hom.isoOfComponents (cechGlobalSectionsXIso F U) (by
    intro i j hij
    simp only [ComplexShape.up_Rel] at hij
    subst j
    rw [Functor.mapHomologicalComplex_obj_d, cechComplex_d]
    change
      ((CategoryTheory.Sheaf.ΓNatIsoSheafSections
          (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).hom.app
            (cechTerm F U i) ≫
          (cechTopSectionsAddEquiv F U i).toAddCommGrpIso.hom) ≫
          ((cechComplexFunctor U).obj F.obj).d i (i + 1) =
        (globalSections X).map (cechDifferential F U i) ≫
          ((CategoryTheory.Sheaf.ΓNatIsoSheafSections
              (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop).hom.app
                (cechTerm F U (i + 1)) ≫
            (cechTopSectionsAddEquiv F U (i + 1)).toAddCommGrpIso.hom)
    let eΓ := CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop
    calc
      ((eΓ.hom.app (cechTerm F U i) ≫
          (cechTopSectionsAddEquiv F U i).toAddCommGrpIso.hom) ≫
          ((cechComplexFunctor U).obj F.obj).d i (i + 1)) =
        eΓ.hom.app (cechTerm F U i) ≫
          ((cechTopSectionsAddEquiv F U i).toAddCommGrpIso.hom ≫
            ((cechComplexFunctor U).obj F.obj).d i (i + 1)) :=
        Category.assoc _ _ _
      _ = eΓ.hom.app (cechTerm F U i) ≫
          ((cechDifferential F U i).hom.app (op ⊤) ≫
            (cechTopSectionsAddEquiv F U (i + 1)).toAddCommGrpIso.hom) :=
        congrArg (fun f => eΓ.hom.app (cechTerm F U i) ≫ f)
          (cechTopSectionsAddEquiv_d (F := F) (U := U) i)
      _ = (eΓ.hom.app (cechTerm F U i) ≫
            (cechDifferential F U i).hom.app (op ⊤)) ≫
          (cechTopSectionsAddEquiv F U (i + 1)).toAddCommGrpIso.hom :=
        (Category.assoc _ _ _).symm
      _ = ((globalSections X).map (cechDifferential F U i) ≫
            eΓ.hom.app (cechTerm F U (i + 1))) ≫
          (cechTopSectionsAddEquiv F U (i + 1)).toAddCommGrpIso.hom :=
        congrArg (fun f => f ≫
          (cechTopSectionsAddEquiv F U (i + 1)).toAddCommGrpIso.hom)
            (eΓ.hom.naturality (cechDifferential F U i)).symm
      _ = (globalSections X).map (cechDifferential F U i) ≫
          (eΓ.hom.app (cechTerm F U (i + 1)) ≫
            (cechTopSectionsAddEquiv F U (i + 1)).toAddCommGrpIso.hom) :=
        Category.assoc _ _ _)

end

end TopCat.Sheaf

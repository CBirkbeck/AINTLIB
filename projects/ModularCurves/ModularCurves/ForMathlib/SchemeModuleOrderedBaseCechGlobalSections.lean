import ModularCurves.ForMathlib.SchemeModuleBaseCech
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCech
import ModularCurves.ForMathlib.SheafOrderedCechSheafComplex
import ModularCurves.ForMathlib.SheafDerivedGlobalSections

/-!
# Global sections of ordered base-linear Cech complexes

After forgetting the module structure over the base, the ordered base-linear
Cech complex of a scheme module agrees with global sections of its ordered
sheaf-level Cech complex.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

open TopCat.Sheaf

variable {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

noncomputable local instance : (globalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).right_adjoint_additive

private noncomputable def orderedBaseCechTopSectionsAddEquiv (n : ℕ) :
    (orderedCechTerm M.sheaf U n).obj.obj (op ⊤) ≃+
      orderedBaseCechTerm π M U n := by
  exact
    (orderedCechTermSectionsAddEquiv
      M.sheaf U n (⊤ : X.Opens)).trans <|
      AddEquiv.piCongrRight fun i =>
        (M.sheaf.obj.mapIso (eqToIso (congrArg op
          (top_inf_eq (∏ᶜ fun k : Fin (n + 1) =>
            U (i.1 k)))))).addCommGroupIsoToAddEquiv

private theorem orderedBaseCechTopSectionsAddEquiv_apply
    (n : ℕ)
    (x : (orderedCechTerm M.sheaf U n).obj.obj (op ⊤))
    (i : OrderedCechIndex ι n) :
    orderedBaseCechTopSectionsAddEquiv π M U n x i =
      (M.sheaf.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun k : Fin (n + 1) =>
          U (i.1 k)))))).hom
        (orderedCechTermSectionsAddEquiv
          M.sheaf U n (⊤ : X.Opens) x i) := by
  rfl

private theorem orderedBaseCechRawDifferential_comp_proj
    (n : ℕ) (i : OrderedCechIndex ι (n + 1)) :
    (orderedBaseCechObjectIsoPi π M U n).inv ≫
        orderedBaseCechDifferential π M U n ≫
        (orderedBaseCechObjectIsoPi π M U (n + 1)).hom ≫
        ModuleCat.ofHom (LinearMap.proj i :
          orderedBaseCechTerm π M U (n + 1) →ₗ[
            Γ(S, (⊤ : S.Opens))]
              baseCechFactor π M U (n + 1) i.1) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        (ModuleCat.ofHom (LinearMap.proj (i.delete k) :
            orderedBaseCechTerm π M U n →ₗ[
              Γ(S, (⊤ : S.Opens))]
                baseCechFactor π M U n (i.delete k).1) ≫
          (baseModulePresheaf π M).map
            (((FormalCoproduct.mk _ U).mapPower
              (SimplexCategory.δ k).toOrderHom.toFun).φ i.1).op) := by
  have htarget :
      (orderedBaseCechObjectIsoPi π M U (n + 1)).hom ≫
          ModuleCat.ofHom (LinearMap.proj i :
            orderedBaseCechTerm π M U (n + 1) →ₗ[
              Γ(S, (⊤ : S.Opens))]
                baseCechFactor π M U (n + 1) i.1) =
        Pi.π (fun j : OrderedCechIndex ι (n + 1) =>
          baseCechFactor π M U (n + 1) j.1) i := by
    change
      (ModuleCat.piIsoPi
          (fun j : OrderedCechIndex ι (n + 1) =>
            baseCechFactor π M U (n + 1) j.1)).hom ≫
          ModuleCat.ofHom (LinearMap.proj i :
            orderedBaseCechTerm π M U (n + 1) →ₗ[
              Γ(S, (⊤ : S.Opens))]
                baseCechFactor π M U (n + 1) i.1) = _
    exact ModuleCat.piIsoPi_hom_ker_subtype _ i
  have hsource (j : OrderedCechIndex ι n) :
      (orderedBaseCechObjectIsoPi π M U n).inv ≫
          Pi.π (fun l : OrderedCechIndex ι n =>
            baseCechFactor π M U n l.1) j =
        ModuleCat.ofHom (LinearMap.proj j :
          orderedBaseCechTerm π M U n →ₗ[
            Γ(S, (⊤ : S.Opens))]
              baseCechFactor π M U n j.1) := by
    change
      (ModuleCat.piIsoPi (fun l : OrderedCechIndex ι n =>
          baseCechFactor π M U n l.1)).inv ≫
        Pi.π (fun l : OrderedCechIndex ι n =>
          baseCechFactor π M U n l.1) j = _
    exact ModuleCat.piIsoPi_inv_kernel_ι _ j
  let A :=
    ModuleCat.of Γ(S, (⊤ : S.Opens))
      (orderedBaseCechTerm π M U n)
  let B := orderedBaseCechObject π M U n
  let C := baseCechFactor π M U (n + 1) i.1
  let D : Fin (n + 2) →
      ModuleCat Γ(S, (⊤ : S.Opens)) := fun k =>
    baseCechFactor π M U n (i.delete k).1
  let f : A ⟶ B :=
    (orderedBaseCechObjectIsoPi π M U n).inv
  let p : (k : Fin (n + 2)) → (B ⟶ D k) := fun k =>
    Pi.π (fun j : OrderedCechIndex ι n =>
      baseCechFactor π M U n j.1) (i.delete k)
  let r : (k : Fin (n + 2)) → (D k ⟶ C) := fun k =>
    (baseModulePresheaf π M).map
      (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ i.1).op
  let a : Fin (n + 2) → (B ⟶ C) := fun k =>
    (-1 : ℤ) ^ (k : ℕ) • (p k ≫ r k)
  let b : Fin (n + 2) → (A ⟶ C) := fun k =>
    (-1 : ℤ) ^ (k : ℕ) • ((f ≫ p k) ≫ r k)
  simp only [htarget]
  rw [orderedBaseCechDifferential_comp_π]
  calc
    _ = f ≫ (∑ k, a k) := rfl
    _ = ∑ k, f ≫ a k := by
      change
        (Preadditive.leftComp C f) (∑ k, a k) = _
      exact
        (map_sum (Preadditive.leftComp C f)
          a Finset.univ).trans rfl
    _ = ∑ k, b k := by
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [a, b]
      rw [Preadditive.comp_zsmul]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [b, f, p, r]
      rw [hsource (i.delete k)]
      rfl

private theorem orderedBaseCechTopRestriction_apply
    (n : ℕ) (k : Fin (n + 2))
    (i : OrderedCechIndex ι (n + 1))
    (x : M.sheaf.obj.obj (op ((⊤ : X.Opens) ⊓
      ∏ᶜ fun a : Fin (n + 1) => U ((i.delete k).1 a)))) :
    M.sheaf.obj.map
        (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ i.1).op
        ((M.sheaf.obj.mapIso (eqToIso (congrArg op
          (top_inf_eq (∏ᶜ fun a : Fin (n + 1) =>
            U ((i.delete k).1 a)))))).hom x) =
      (M.sheaf.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun a : Fin (n + 2) =>
          U (i.1 a)))))).hom
        (M.sheaf.obj.map
          (homOfLE (inf_le_inf_left (⊤ : X.Opens)
            (leOfHom (((FormalCoproduct.mk _ U).mapPower
              (SimplexCategory.δ k).toOrderHom.toFun).φ i.1)))).op x) := by
  have h :
      M.sheaf.obj.map (eqToIso (congrArg op
          (top_inf_eq (∏ᶜ fun a : Fin (n + 1) =>
            U ((i.delete k).1 a))))).hom ≫
          M.sheaf.obj.map
            (((FormalCoproduct.mk _ U).mapPower
              (SimplexCategory.δ k).toOrderHom.toFun).φ i.1).op =
        M.sheaf.obj.map
            (homOfLE (inf_le_inf_left (⊤ : X.Opens)
              (leOfHom (((FormalCoproduct.mk _ U).mapPower
                (SimplexCategory.δ k).toOrderHom.toFun).φ i.1)))).op ≫
          M.sheaf.obj.map (eqToIso (congrArg op
            (top_inf_eq (∏ᶜ fun a : Fin (n + 2) =>
              U (i.1 a))))).hom := by
    exact
      (M.sheaf.obj.map_comp _ _).symm.trans
        ((congrArg M.sheaf.obj.map
          (Subsingleton.elim _ _)).trans
            (M.sheaf.obj.map_comp _ _))
  exact ConcreteCategory.congr_hom h x

private theorem orderedBaseCechTopCofaceSummand_apply
    (n : ℕ) (k : Fin (n + 2))
    (i : OrderedCechIndex ι (n + 1))
    (x : (orderedCechTerm M.sheaf U n).obj.obj (op ⊤)) :
    (-1 : ℤ) ^ (k : ℕ) •
        ((baseModulePresheaf π M).map
          (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i.1).op).hom
          (orderedBaseCechTopSectionsAddEquiv
            π M U n x (i.delete k)) =
      (M.sheaf.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun a : Fin (n + 2) =>
          U (i.1 a)))))).hom
        ((-1 : ℤ) ^ (k : ℕ) •
          M.sheaf.obj.map
            (homOfLE (inf_le_inf_left (⊤ : X.Opens)
              (leOfHom (((FormalCoproduct.mk _ U).mapPower
                (SimplexCategory.δ k).toOrderHom.toFun).φ i.1)))).op
            (orderedCechTermSectionsAddEquiv
              M.sheaf U n (⊤ : X.Opens) x (i.delete k))) := by
  have hTop :=
    orderedBaseCechTopSectionsAddEquiv_apply
      π M U n x (i.delete k)
  have hIdentify := congrArg
    (fun y => (-1 : ℤ) ^ (k : ℕ) •
      ((baseModulePresheaf π M).map
        (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ i.1).op).hom y)
    hTop
  have hRestriction :
      ((baseModulePresheaf π M).map
        (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ i.1).op).hom
        ((M.sheaf.obj.mapIso (eqToIso (congrArg op
          (top_inf_eq (∏ᶜ fun a : Fin (n + 1) =>
            U ((i.delete k).1 a)))))).hom
          (orderedCechTermSectionsAddEquiv
            M.sheaf U n (⊤ : X.Opens) x (i.delete k))) =
      (M.sheaf.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun a : Fin (n + 2) =>
          U (i.1 a)))))).hom
        (M.sheaf.obj.map
          (homOfLE (inf_le_inf_left (⊤ : X.Opens)
            (leOfHom (((FormalCoproduct.mk _ U).mapPower
              (SimplexCategory.δ k).toOrderHom.toFun).φ i.1)))).op
          (orderedCechTermSectionsAddEquiv
            M.sheaf U n (⊤ : X.Opens) x (i.delete k))) := by
    exact
      orderedBaseCechTopRestriction_apply M U n k i
        (orderedCechTermSectionsAddEquiv
          M.sheaf U n (⊤ : X.Opens) x (i.delete k))
  have hRestrict :=
    congrArg (fun y => (-1 : ℤ) ^ (k : ℕ) • y) hRestriction
  let restricted :=
    M.sheaf.obj.map
      (homOfLE (inf_le_inf_left (⊤ : X.Opens)
        (leOfHom (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ i.1)))).op
      (orderedCechTermSectionsAddEquiv
        M.sheaf U n (⊤ : X.Opens) x (i.delete k))
  have hScalar :
      (-1 : ℤ) ^ (k : ℕ) •
          (M.sheaf.obj.mapIso (eqToIso (congrArg op
            (top_inf_eq (∏ᶜ fun a : Fin (n + 2) =>
              U (i.1 a)))))).hom restricted =
        (M.sheaf.obj.mapIso (eqToIso (congrArg op
          (top_inf_eq (∏ᶜ fun a : Fin (n + 2) =>
            U (i.1 a)))))).hom
          ((-1 : ℤ) ^ (k : ℕ) • restricted) :=
    (map_zsmul
      (M.sheaf.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun a : Fin (n + 2) =>
          U (i.1 a)))))).hom.hom
      ((-1 : ℤ) ^ (k : ℕ)) restricted).symm
  exact hIdentify.trans (hRestrict.trans hScalar)

private theorem addCommGrp_hom_map_sum
    {A B : AddCommGrpCat.{u}} {κ : Type*}
    [Fintype κ] (f : A ⟶ B) (x : κ → A) :
    ConcreteCategory.hom f (∑ k, x k) =
      ∑ k, ConcreteCategory.hom f (x k) := by
  simp

private theorem orderedBaseCechTopAlternatingSum_apply
    (n : ℕ) (i : OrderedCechIndex ι (n + 1))
    (x : (orderedCechTerm M.sheaf U n).obj.obj (op ⊤)) :
    (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
      ((baseModulePresheaf π M).map
        (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ i.1).op).hom
        (orderedBaseCechTopSectionsAddEquiv
          π M U n x (i.delete k))) =
      (M.sheaf.obj.mapIso (eqToIso (congrArg op
        (top_inf_eq (∏ᶜ fun a : Fin (n + 2) =>
          U (i.1 a)))))).hom
        (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
          M.sheaf.obj.map
            (homOfLE (inf_le_inf_left (⊤ : X.Opens)
              (leOfHom (((FormalCoproduct.mk _ U).mapPower
                (SimplexCategory.δ k).toOrderHom.toFun).φ i.1)))).op
            (orderedCechTermSectionsAddEquiv
              M.sheaf U n (⊤ : X.Opens) x (i.delete k))) := by
  let f :=
    (M.sheaf.obj.mapIso (eqToIso (congrArg op
      (top_inf_eq (∏ᶜ fun a : Fin (n + 2) =>
        U (i.1 a)))))).hom
  let a := fun k : Fin (n + 2) =>
    (-1 : ℤ) ^ (k : ℕ) •
      M.sheaf.obj.map
        (homOfLE (inf_le_inf_left (⊤ : X.Opens)
          (leOfHom (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i.1)))).op
        (orderedCechTermSectionsAddEquiv
          M.sheaf U n (⊤ : X.Opens) x (i.delete k))
  calc
    _ = ∑ k, ConcreteCategory.hom f (a k) :=
      Finset.sum_congr rfl (fun k _ =>
        orderedBaseCechTopCofaceSummand_apply
          π M U n k i x)
    _ = ConcreteCategory.hom f (∑ k, a k) :=
      (addCommGrp_hom_map_sum f a).symm

private noncomputable def orderedCechGlobalToTopIso
    (n : ℕ) :
    (globalSectionsFunctor X).obj
        (orderedCechTerm M.sheaf U n) ≅
      AddCommGrpCat.of
        ((orderedCechTerm M.sheaf U n).obj.obj (op ⊤)) :=
  (CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X)
        AddCommGrpCat.{u} isTerminalTop).app
    (orderedCechTerm M.sheaf U n)

private theorem orderedCechGlobalToTopIso_naturality
    (n : ℕ) :
    (orderedCechGlobalToTopIso M U n).hom ≫
        (orderedCechDifferential M.sheaf U n).hom.app (op ⊤) =
      (globalSectionsFunctor X).map
          (orderedCechDifferential M.sheaf U n) ≫
        (orderedCechGlobalToTopIso M U (n + 1)).hom := by
  change
    (CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X)
        AddCommGrpCat.{u} isTerminalTop).hom.app
        (orderedCechTerm M.sheaf U n) ≫
      ((CategoryTheory.sheafSections
        (Opens.grothendieckTopology X)
          AddCommGrpCat.{u}).obj (op ⊤)).map
        (orderedCechDifferential M.sheaf U n) =
    (CategoryTheory.Sheaf.Γ
      (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).map
        (orderedCechDifferential M.sheaf U n) ≫
      (CategoryTheory.Sheaf.ΓNatIsoSheafSections
        (Opens.grothendieckTopology X)
          AddCommGrpCat.{u} isTerminalTop).hom.app
        (orderedCechTerm M.sheaf U (n + 1))
  exact
    (CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X)
        AddCommGrpCat.{u} isTerminalTop).hom.naturality
      (orderedCechDifferential M.sheaf U n) |>.symm

/-- Global sections of an ordered sheaf-level Cech term agree with the
corresponding forgotten ordered base-linear Cech object. -/
noncomputable def orderedBaseCechGlobalSectionsXIso
    (n : ℕ) :
    (globalSectionsFunctor X).obj
        (orderedCechTerm M.sheaf U n) ≅
      (baseModuleForget S).obj
        (orderedBaseCechObject π M U n) :=
  orderedCechGlobalToTopIso M U n ≪≫
    (orderedBaseCechTopSectionsAddEquiv
      π M U n).toAddCommGrpIso ≪≫
    (baseModuleForget S).mapIso
      (orderedBaseCechObjectIsoPi π M U n).symm

private noncomputable def orderedBaseCechRawDifferential
    (n : ℕ) :
    AddCommGrpCat.of (orderedBaseCechTerm π M U n) ⟶
      AddCommGrpCat.of (orderedBaseCechTerm π M U (n + 1)) :=
  (baseModuleForget S).map
    ((orderedBaseCechObjectIsoPi π M U n).inv ≫
      orderedBaseCechDifferential π M U n ≫
      (orderedBaseCechObjectIsoPi π M U (n + 1)).hom)

private theorem moduleCat_hom_map_sum
    {R : Type u} [Ring R] {A B : ModuleCat.{u} R}
    {κ : Type*} [Fintype κ] (f : κ → (A ⟶ B)) (x : A) :
    (∑ k, f k).hom x = ∑ k, (f k).hom x := by
  simp

private theorem orderedBaseCechRawDifferential_apply
    (n : ℕ) (x : orderedBaseCechTerm π M U n)
    (i : OrderedCechIndex ι (n + 1)) :
    orderedBaseCechRawDifferential π M U n x i =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        ((baseModulePresheaf π M).map
          (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i.1).op).hom
          (x (i.delete k)) := by
  have hx := congrArg (fun f => f.hom x)
    (orderedBaseCechRawDifferential_comp_proj π M U n i)
  have hleft :
      orderedBaseCechRawDifferential π M U n x i =
        ((orderedBaseCechObjectIsoPi π M U n).inv ≫
          orderedBaseCechDifferential π M U n ≫
          (orderedBaseCechObjectIsoPi π M U (n + 1)).hom ≫
          ModuleCat.ofHom (LinearMap.proj i :
            orderedBaseCechTerm π M U (n + 1) →ₗ[
              Γ(S, (⊤ : S.Opens))]
                baseCechFactor π M U (n + 1) i.1)).hom x := by
    rfl
  rw [hleft, hx]
  let A :=
    ModuleCat.of Γ(S, (⊤ : S.Opens))
      (orderedBaseCechTerm π M U n)
  let B := baseCechFactor π M U (n + 1) i.1
  let g : Fin (n + 2) → (A ⟶ B) := fun k =>
    (-1 : ℤ) ^ (k : ℕ) •
      (ModuleCat.ofHom (LinearMap.proj (i.delete k) :
          orderedBaseCechTerm π M U n →ₗ[
            Γ(S, (⊤ : S.Opens))]
              baseCechFactor π M U n (i.delete k).1) ≫
        (baseModulePresheaf π M).map
          (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i.1).op)
  change (∑ k, g k).hom x = _
  rw [moduleCat_hom_map_sum g x]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [g]
  rfl

private theorem orderedBaseCechTopSectionsAddEquiv_d
    (n : ℕ) :
    (orderedBaseCechTopSectionsAddEquiv
        π M U n).toAddCommGrpIso.hom ≫
        orderedBaseCechRawDifferential π M U n =
      (orderedCechDifferential
          M.sheaf U n).hom.app (op ⊤) ≫
        (orderedBaseCechTopSectionsAddEquiv
          π M U (n + 1)).toAddCommGrpIso.hom := by
  apply ConcreteCategory.hom_ext
  intro x
  funext i
  change
    orderedBaseCechRawDifferential π M U n
        (orderedBaseCechTopSectionsAddEquiv π M U n x) i =
      orderedBaseCechTopSectionsAddEquiv π M U (n + 1)
        ((orderedCechDifferential
          M.sheaf U n).hom.app (op ⊤) x) i
  rw [orderedBaseCechRawDifferential_apply]
  have hSum :=
    orderedBaseCechTopAlternatingSum_apply
      π M U n i x
  have hDifferential :=
    orderedCechDifferential_apply
      M.sheaf U n (⊤ : X.Opens) x i
  have hMapped := congrArg
    (M.sheaf.obj.mapIso (eqToIso (congrArg op
      (top_inf_eq (∏ᶜ fun a : Fin (n + 2) =>
        U (i.1 a)))))).hom hDifferential
  have hTop :=
    orderedBaseCechTopSectionsAddEquiv_apply
      π M U (n + 1)
      ((orderedCechDifferential
        M.sheaf U n).hom.app (op ⊤) x) i
  exact hSum.trans (hMapped.symm.trans hTop.symm)

private theorem orderedBaseCechTopSectionsIso_d
    (n : ℕ) :
    (orderedBaseCechTopSectionsAddEquiv
        π M U n).toAddCommGrpIso.hom ≫
        (baseModuleForget S).map
          (orderedBaseCechObjectIsoPi π M U n).inv ≫
        (baseModuleForget S).map
          (orderedBaseCechDifferential π M U n) =
      (orderedCechDifferential
          M.sheaf U n).hom.app (op ⊤) ≫
        (orderedBaseCechTopSectionsAddEquiv
          π M U (n + 1)).toAddCommGrpIso.hom ≫
        (baseModuleForget S).map
          (orderedBaseCechObjectIsoPi
            π M U (n + 1)).inv := by
  let F := baseModuleForget S
  let e := orderedBaseCechObjectIsoPi π M U
  have hraw :
      orderedBaseCechRawDifferential π M U n ≫
          F.map (e (n + 1)).inv =
        F.map (e n).inv ≫
          F.map (orderedBaseCechDifferential π M U n) := by
    change
      F.map ((e n).inv ≫
          orderedBaseCechDifferential π M U n ≫
          (e (n + 1)).hom) ≫
          F.map (e (n + 1)).inv =
        F.map (e n).inv ≫
          F.map (orderedBaseCechDifferential π M U n)
    calc
      _ = F.map (((e n).inv ≫
          orderedBaseCechDifferential π M U n ≫
          (e (n + 1)).hom) ≫ (e (n + 1)).inv) :=
        (F.map_comp _ _).symm
      _ = F.map ((e n).inv ≫
          orderedBaseCechDifferential π M U n) := by
        congr 1
        simp
      _ = _ := F.map_comp _ _
  calc
    _ = (orderedBaseCechTopSectionsAddEquiv
          π M U n).toAddCommGrpIso.hom ≫
        (orderedBaseCechRawDifferential π M U n ≫
          F.map (e (n + 1)).inv) := by
      rw [hraw]
    _ = ((orderedBaseCechTopSectionsAddEquiv
          π M U n).toAddCommGrpIso.hom ≫
        orderedBaseCechRawDifferential π M U n) ≫
          F.map (e (n + 1)).inv :=
      (Category.assoc _ _ _).symm
    _ = ((orderedCechDifferential
          M.sheaf U n).hom.app (op ⊤) ≫
        (orderedBaseCechTopSectionsAddEquiv
          π M U (n + 1)).toAddCommGrpIso.hom) ≫
          F.map (e (n + 1)).inv := by
      rw [orderedBaseCechTopSectionsAddEquiv_d]
    _ = _ := Category.assoc _ _ _

/-- Applying global sections degreewise to the ordered sheaf-level Cech
complex gives the forgotten ordered base-linear Cech complex. -/
noncomputable def orderedBaseCechGlobalSectionsComplexIso :
    ((globalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj
        (orderedCechComplex M.sheaf U) ≅
      ((baseModuleForget S).mapHomologicalComplex (.up ℕ)).obj
        (orderedBaseCechComplex π M U) :=
  HomologicalComplex.Hom.isoOfComponents
    (orderedBaseCechGlobalSectionsXIso π M U) (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      subst j
      change
        (orderedBaseCechGlobalSectionsXIso
            π M U i).hom ≫
            (baseModuleForget S).map
              ((orderedBaseCechComplex π M U).d i (i + 1)) =
          (globalSectionsFunctor X).map
              ((orderedCechComplex M.sheaf U).d i (i + 1)) ≫
            (orderedBaseCechGlobalSectionsXIso
              π M U (i + 1)).hom
      rw [orderedCechComplex_d,
        orderedBaseCechComplex_d]
      let e := orderedBaseCechObjectIsoPi π M U
      change
        ((orderedCechGlobalToTopIso M U i).hom ≫
            (orderedBaseCechTopSectionsAddEquiv
              π M U i).toAddCommGrpIso.hom ≫
            (baseModuleForget S).map (e i).inv) ≫
          (baseModuleForget S).map
            (orderedBaseCechDifferential π M U i) =
        (globalSectionsFunctor X).map
            (orderedCechDifferential M.sheaf U i) ≫
          ((orderedCechGlobalToTopIso M U (i + 1)).hom ≫
            (orderedBaseCechTopSectionsAddEquiv
              π M U (i + 1)).toAddCommGrpIso.hom ≫
            (baseModuleForget S).map (e (i + 1)).inv)
      have hTop :=
        orderedBaseCechTopSectionsIso_d π M U i
      have hGlobal :=
        orderedCechGlobalToTopIso_naturality M U i
      calc
        _ = (orderedCechGlobalToTopIso M U i).hom ≫
            ((orderedBaseCechTopSectionsAddEquiv
                π M U i).toAddCommGrpIso.hom ≫
              (baseModuleForget S).map (e i).inv ≫
              (baseModuleForget S).map
                (orderedBaseCechDifferential π M U i)) :=
          by simp only [Category.assoc]
        _ = (orderedCechGlobalToTopIso M U i).hom ≫
            ((orderedCechDifferential
                M.sheaf U i).hom.app (op ⊤) ≫
              (orderedBaseCechTopSectionsAddEquiv
                π M U (i + 1)).toAddCommGrpIso.hom ≫
              (baseModuleForget S).map (e (i + 1)).inv) := by
          exact congrArg
            (fun f =>
              (orderedCechGlobalToTopIso M U i).hom ≫ f)
            hTop
        _ = ((orderedCechGlobalToTopIso M U i).hom ≫
              (orderedCechDifferential
                M.sheaf U i).hom.app (op ⊤)) ≫
            ((orderedBaseCechTopSectionsAddEquiv
                π M U (i + 1)).toAddCommGrpIso.hom ≫
              (baseModuleForget S).map (e (i + 1)).inv) := by
          simp only [Category.assoc]
        _ = ((globalSectionsFunctor X).map
                (orderedCechDifferential M.sheaf U i) ≫
              (orderedCechGlobalToTopIso
                M U (i + 1)).hom) ≫
            ((orderedBaseCechTopSectionsAddEquiv
                π M U (i + 1)).toAddCommGrpIso.hom ≫
              (baseModuleForget S).map (e (i + 1)).inv) := by
          exact congrArg
            (fun f => f ≫
              ((orderedBaseCechTopSectionsAddEquiv
                π M U (i + 1)).toAddCommGrpIso.hom ≫
              (baseModuleForget S).map (e (i + 1)).inv))
            hGlobal
        _ = _ := by
          simp only [Category.assoc])

/-- Exactness of the ordered base-linear Cech complex is equivalent to
exactness after taking global sections of the ordered sheaf-level Cech
complex. -/
theorem orderedBaseCechComplex_exactAt_iff_globalSections
    (n : ℕ) :
    (orderedBaseCechComplex π M U).ExactAt n ↔
      (((globalSectionsFunctor X).mapHomologicalComplex
        (.up ℕ)).obj (orderedCechComplex M.sheaf U)).ExactAt n := by
  constructor
  · intro h
    have hForget :
        (((baseModuleForget S).mapHomologicalComplex
          (.up ℕ)).obj
            (orderedBaseCechComplex π M U)).ExactAt n := by
      rw [HomologicalComplex.exactAt_iff]
      change (((orderedBaseCechComplex
        π M U).sc n).map (baseModuleForget S)).Exact
      exact
        (ShortComplex.exact_iff_exact_map_forget₂
          (S := (orderedBaseCechComplex π M U).sc n)).mp h
    exact hForget.of_iso
      (orderedBaseCechGlobalSectionsComplexIso
        π M U).symm
  · intro h
    have hForget :
        (((baseModuleForget S).mapHomologicalComplex
          (.up ℕ)).obj
            (orderedBaseCechComplex π M U)).ExactAt n :=
      h.of_iso
        (orderedBaseCechGlobalSectionsComplexIso π M U)
    rw [HomologicalComplex.exactAt_iff] at hForget ⊢
    exact
      (ShortComplex.exact_iff_exact_map_forget₂
        (S := (orderedBaseCechComplex π M U).sc n)).mpr
          hForget

end

end AlgebraicGeometry.Scheme.Modules

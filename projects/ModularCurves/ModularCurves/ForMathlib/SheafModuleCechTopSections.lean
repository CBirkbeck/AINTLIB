/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.SheafModuleCechAugmentation

/-!
# Top sections of module-valued sheaf Cech terms

Top sections of a sheaf-level Cech term are identified with the corresponding
degree of the native Cech complex while retaining the coefficient-ring action.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace TopCat.Sheaf

variable {R : Type u} [CommRing R] {X : TopCat.{u}}
variable (F : Sheaf (ModuleCat.{u} R) X)
variable {ι : Type u} (U : ι → Opens X) (n : ℕ)

private noncomputable def moduleCechTermForgetDiagramIso :
    Discrete.functor (moduleCechTermFactor F U n) ⋙
        forget (ModuleCat R) X ≅
      Discrete.functor fun i : Fin (n + 1) → ι =>
        (moduleCechTermFactor F U n i).obj :=
  Discrete.natIso fun _ => Iso.refl _

private noncomputable def moduleCechTermForgetIso :
    (moduleCechTerm F U n).obj ≅
      ∏ᶜ fun i : Fin (n + 1) → ι =>
        (moduleCechTermFactor F U n i).obj := by
  letI : HasLimit (Discrete.functor (moduleCechTermFactor F U n) ⋙
      forget (ModuleCat R) X) :=
    hasLimit_of_iso (moduleCechTermForgetDiagramIso F U n).symm
  exact preservesLimitIso (forget (ModuleCat R) X)
      (Discrete.functor (moduleCechTermFactor F U n)) ≪≫
    HasLimit.isoOfNatIso (moduleCechTermForgetDiagramIso F U n)

private theorem moduleCechTermForgetIso_hom_π
    (i : Fin (n + 1) → ι) :
    (moduleCechTermForgetIso F U n).hom ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          (moduleCechTermFactor F U n j).obj) i =
      (Pi.π (moduleCechTermFactor F U n) i).hom := by
  change (moduleCechTermForgetIso F U n).hom ≫
      limit.π (Discrete.functor fun j : Fin (n + 1) → ι =>
        (moduleCechTermFactor F U n j).obj) ⟨i⟩ =
    (forget (ModuleCat R) X).map
      (limit.π (Discrete.functor (moduleCechTermFactor F U n)) ⟨i⟩)
  letI : HasLimit (Discrete.functor (moduleCechTermFactor F U n) ⋙
      forget (ModuleCat R) X) :=
    hasLimit_of_iso (moduleCechTermForgetDiagramIso F U n).symm
  have hnat :
      (HasLimit.isoOfNatIso
          (moduleCechTermForgetDiagramIso F U n)).hom ≫
          limit.π (Discrete.functor fun j : Fin (n + 1) → ι =>
            (moduleCechTermFactor F U n j).obj) ⟨i⟩ =
        limit.π (Discrete.functor (moduleCechTermFactor F U n) ⋙
          forget (ModuleCat R) X) ⟨i⟩ := by
    have happ :
        (moduleCechTermForgetDiagramIso F U n).hom.app ⟨i⟩ =
          𝟙 ((moduleCechTermFactor F U n i).obj) :=
      rfl
    have hbase :
        (HasLimit.isoOfNatIso
            (moduleCechTermForgetDiagramIso F U n)).hom ≫
            limit.π (Discrete.functor fun j : Fin (n + 1) → ι =>
              (moduleCechTermFactor F U n j).obj) ⟨i⟩ =
          limit.π (Discrete.functor (moduleCechTermFactor F U n) ⋙
              forget (ModuleCat R) X) ⟨i⟩ ≫
            (moduleCechTermForgetDiagramIso F U n).hom.app ⟨i⟩ :=
      HasLimit.isoOfNatIso_hom_π
        (moduleCechTermForgetDiagramIso F U n) ⟨i⟩
    have hcomp :
        limit.π (Discrete.functor (moduleCechTermFactor F U n) ⋙
              forget (ModuleCat R) X) ⟨i⟩ ≫
            (moduleCechTermForgetDiagramIso F U n).hom.app ⟨i⟩ =
          limit.π (Discrete.functor (moduleCechTermFactor F U n) ⋙
            forget (ModuleCat R) X) ⟨i⟩ := by
      rw [happ]
      exact Category.comp_id _
    exact hbase.trans hcomp
  have hpreserves :
      (preservesLimitIso (forget (ModuleCat R) X)
          (Discrete.functor (moduleCechTermFactor F U n))).hom ≫
          limit.π (Discrete.functor (moduleCechTermFactor F U n) ⋙
            forget (ModuleCat R) X) ⟨i⟩ =
        (forget (ModuleCat R) X).map
          (limit.π
            (Discrete.functor (moduleCechTermFactor F U n)) ⟨i⟩) :=
    preservesLimitIso_hom_π (forget (ModuleCat R) X)
      (Discrete.functor (moduleCechTermFactor F U n)) ⟨i⟩
  have hcombined :
      (preservesLimitIso (forget (ModuleCat R) X)
          (Discrete.functor (moduleCechTermFactor F U n))).hom ≫
          ((HasLimit.isoOfNatIso
              (moduleCechTermForgetDiagramIso F U n)).hom ≫
            limit.π (Discrete.functor fun j : Fin (n + 1) → ι =>
              (moduleCechTermFactor F U n j).obj) ⟨i⟩) =
        (forget (ModuleCat R) X).map
          (limit.π
            (Discrete.functor (moduleCechTermFactor F U n)) ⟨i⟩) := by
    rw [hnat]
    exact hpreserves
  change
    (preservesLimitIso (forget (ModuleCat R) X)
        (Discrete.functor (moduleCechTermFactor F U n))).hom ≫
        ((HasLimit.isoOfNatIso
            (moduleCechTermForgetDiagramIso F U n)).hom ≫
          limit.π (Discrete.functor fun j : Fin (n + 1) → ι =>
            (moduleCechTermFactor F U n j).obj) ⟨i⟩) =
      (forget (ModuleCat R) X).map
        (limit.π
          (Discrete.functor (moduleCechTermFactor F U n)) ⟨i⟩)
  exact hcombined

private noncomputable def moduleCechTermForgetSectionsIso
    (W : Opens X) :
    (moduleCechTerm F U n).obj.obj (op W) ≅
      ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op W)).obj
        (∏ᶜ fun i : Fin (n + 1) → ι =>
          (moduleCechTermFactor F U n i).obj) :=
  ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op W)).mapIso
    (moduleCechTermForgetIso F U n)

private noncomputable def moduleCechTermEvaluationDiagramIso
    (W : Opens X) :
    (Discrete.functor fun i : Fin (n + 1) → ι =>
        (moduleCechTermFactor F U n i).obj) ⋙
        (evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op W) ≅
      Discrete.functor fun i : Fin (n + 1) → ι =>
        (moduleCechTermFactor F U n i).obj.obj (op W) :=
  Discrete.natIso fun _ => Iso.refl _

private noncomputable def moduleCechTermEvaluationIso
    (W : Opens X) :
    ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op W)).obj
        (∏ᶜ fun i : Fin (n + 1) → ι =>
          (moduleCechTermFactor F U n i).obj) ≅
      ∏ᶜ fun i : Fin (n + 1) → ι =>
        (moduleCechTermFactor F U n i).obj.obj (op W) := by
  letI : HasLimit ((Discrete.functor fun i : Fin (n + 1) → ι =>
      (moduleCechTermFactor F U n i).obj) ⋙
        (evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op W)) :=
    hasLimit_of_iso (moduleCechTermEvaluationDiagramIso F U n W).symm
  exact preservesLimitIso
      ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op W))
      (Discrete.functor fun i : Fin (n + 1) → ι =>
        (moduleCechTermFactor F U n i).obj) ≪≫
    HasLimit.isoOfNatIso (moduleCechTermEvaluationDiagramIso F U n W)

private theorem moduleCechTermEvaluationIso_hom_π
    (W : Opens X) (i : Fin (n + 1) → ι) :
    (moduleCechTermEvaluationIso F U n W).hom ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          (moduleCechTermFactor F U n j).obj.obj (op W)) i =
      ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op W)).map
        (Pi.π (fun j : Fin (n + 1) → ι =>
          (moduleCechTermFactor F U n j).obj) i) := by
  change (moduleCechTermEvaluationIso F U n W).hom ≫
      limit.π (Discrete.functor fun j : Fin (n + 1) → ι =>
        (moduleCechTermFactor F U n j).obj.obj (op W)) ⟨i⟩ =
    ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op W)).map
      (limit.π (Discrete.functor fun j : Fin (n + 1) → ι =>
        (moduleCechTermFactor F U n j).obj) ⟨i⟩)
  letI : HasLimit ((Discrete.functor fun i : Fin (n + 1) → ι =>
      (moduleCechTermFactor F U n i).obj) ⋙
        (evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op W)) :=
    hasLimit_of_iso (moduleCechTermEvaluationDiagramIso F U n W).symm
  have hnat :
      (HasLimit.isoOfNatIso
          (moduleCechTermEvaluationDiagramIso F U n W)).hom ≫
          limit.π (Discrete.functor fun j : Fin (n + 1) → ι =>
            (moduleCechTermFactor F U n j).obj.obj (op W)) ⟨i⟩ =
        limit.π ((Discrete.functor fun j : Fin (n + 1) → ι =>
          (moduleCechTermFactor F U n j).obj) ⋙
            (evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op W)) ⟨i⟩ := by
    calc
      _ = limit.π ((Discrete.functor fun j : Fin (n + 1) → ι =>
            (moduleCechTermFactor F U n j).obj) ⋙
              (evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op W)) ⟨i⟩ ≫
          (moduleCechTermEvaluationDiagramIso F U n W).hom.app ⟨i⟩ :=
        HasLimit.isoOfNatIso_hom_π
          (moduleCechTermEvaluationDiagramIso F U n W) ⟨i⟩
      _ = _ := Category.comp_id _
  have hpreserves :
      (preservesLimitIso
          ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op W))
          (Discrete.functor fun j : Fin (n + 1) → ι =>
            (moduleCechTermFactor F U n j).obj)).hom ≫
          limit.π ((Discrete.functor fun j : Fin (n + 1) → ι =>
            (moduleCechTermFactor F U n j).obj) ⋙
              (evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op W)) ⟨i⟩ =
        ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op W)).map
          (limit.π (Discrete.functor fun j : Fin (n + 1) → ι =>
            (moduleCechTermFactor F U n j).obj) ⟨i⟩) :=
    preservesLimitIso_hom_π
      ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op W))
      (Discrete.functor fun j : Fin (n + 1) → ι =>
        (moduleCechTermFactor F U n j).obj) ⟨i⟩
  have hcombined :
      (preservesLimitIso
          ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op W))
          (Discrete.functor fun j : Fin (n + 1) → ι =>
            (moduleCechTermFactor F U n j).obj)).hom ≫
          ((HasLimit.isoOfNatIso
              (moduleCechTermEvaluationDiagramIso F U n W)).hom ≫
            limit.π (Discrete.functor fun j : Fin (n + 1) → ι =>
              (moduleCechTermFactor F U n j).obj.obj (op W)) ⟨i⟩) =
        ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op W)).map
          (limit.π (Discrete.functor fun j : Fin (n + 1) → ι =>
            (moduleCechTermFactor F U n j).obj) ⟨i⟩) := by
    rw [hnat]
    exact hpreserves
  simpa only [moduleCechTermEvaluationIso, Iso.trans_hom,
    Category.assoc] using hcombined

private noncomputable def moduleCechTermSectionsRawIso
    (W : Opens X) :
    (moduleCechTerm F U n).obj.obj (op W) ≅
      ∏ᶜ fun i : Fin (n + 1) → ι =>
        (moduleCechTermFactor F U n i).obj.obj (op W) :=
  moduleCechTermForgetSectionsIso F U n W ≪≫
    moduleCechTermEvaluationIso F U n W

private theorem moduleCechTermSectionsRawIso_hom_π
    (W : Opens X) (i : Fin (n + 1) → ι) :
    (moduleCechTermSectionsRawIso F U n W).hom ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          (moduleCechTermFactor F U n j).obj.obj (op W)) i =
      (Pi.π (moduleCechTermFactor F U n) i).hom.app (op W) := by
  rw [moduleCechTermSectionsRawIso, Iso.trans_hom, Category.assoc,
    moduleCechTermEvaluationIso_hom_π]
  exact congr_app (moduleCechTermForgetIso_hom_π F U n i) (op W)

private noncomputable def moduleCechTermTopRawIso :
    (moduleCechTerm F U n).obj.obj (op ⊤) ≅
      ∏ᶜ fun i : Fin (n + 1) → ι =>
        (moduleCechTermFactor F U n i).obj.obj (op ⊤) :=
  moduleCechTermSectionsRawIso F U n ⊤

private theorem moduleCechTermTopRawIso_hom_π
    (i : Fin (n + 1) → ι) :
    (moduleCechTermTopRawIso F U n).hom ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          (moduleCechTermFactor F U n j).obj.obj (op ⊤)) i =
      (Pi.π (moduleCechTermFactor F U n) i).hom.app (op ⊤) :=
  moduleCechTermSectionsRawIso_hom_π F U n ⊤ i

/-- Sections of a restriction-pushforward Cech factor on `W` are the
sections on its intersection with the indexing open. -/
noncomputable def moduleCechTermFactorSectionsIso
    (W : Opens X) (i : Fin (n + 1) → ι) :
    (moduleCechTermFactor F U n i).obj.obj (op W) ≅
      F.obj.obj
        (op (W ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k))) :=
  F.obj.mapIso (eqToIso (congrArg op
    (Opens.functor_map_eq_inf
      (∏ᶜ fun k : Fin (n + 1) => U (i k)) W)))

/-- Sections on `W` of a module-valued sheaf Cech term are the product of
sections on the intersections of `W` with its tuple opens. -/
noncomputable def moduleCechTermSectionsIso
    (W : Opens X) :
    (moduleCechTerm F U n).obj.obj (op W) ≅
      ∏ᶜ fun i : Fin (n + 1) → ι =>
        F.obj.obj
          (op (W ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k))) :=
  moduleCechTermSectionsRawIso F U n W ≪≫
    Pi.mapIso (moduleCechTermFactorSectionsIso F U n W)

/-- The arbitrary-sections comparison commutes with every product
projection. -/
theorem moduleCechTermSectionsIso_hom_π
    (W : Opens X) (i : Fin (n + 1) → ι) :
    (moduleCechTermSectionsIso F U n W).hom ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          F.obj.obj
            (op (W ⊓ ∏ᶜ fun k : Fin (n + 1) => U (j k)))) i =
      (Pi.π (moduleCechTermFactor F U n) i).hom.app (op W) ≫
        (moduleCechTermFactorSectionsIso F U n W i).hom := by
  calc
    _ = ((moduleCechTermSectionsRawIso F U n W).hom ≫
          (Pi.mapIso
            (moduleCechTermFactorSectionsIso F U n W)).hom) ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          F.obj.obj
            (op (W ⊓ ∏ᶜ fun k : Fin (n + 1) => U (j k)))) i := by
      rfl
    _ = (moduleCechTermSectionsRawIso F U n W).hom ≫
        ((Pi.mapIso
          (moduleCechTermFactorSectionsIso F U n W)).hom ≫
            Pi.π (fun j : Fin (n + 1) → ι =>
              F.obj.obj
                (op (W ⊓ ∏ᶜ fun k : Fin (n + 1) => U (j k)))) i) :=
      Category.assoc _ _ _
    _ = (moduleCechTermSectionsRawIso F U n W).hom ≫
        (Pi.π (fun j : Fin (n + 1) → ι =>
            (moduleCechTermFactor F U n j).obj.obj (op W)) i ≫
          (moduleCechTermFactorSectionsIso F U n W i).hom) := by
      rw [Pi.mapIso_hom_π]
    _ = ((moduleCechTermSectionsRawIso F U n W).hom ≫
          Pi.π (fun j : Fin (n + 1) → ι =>
            (moduleCechTermFactor F U n j).obj.obj (op W)) i) ≫
        (moduleCechTermFactorSectionsIso F U n W i).hom :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg
      (fun f => f ≫
        (moduleCechTermFactorSectionsIso F U n W i).hom)
      (moduleCechTermSectionsRawIso_hom_π F U n W i)

/-- Top sections of a restriction-pushforward Cech factor are the sections on
its indexing open. -/
noncomputable def moduleCechTermFactorTopIso
    (i : Fin (n + 1) → ι) :
    (moduleCechTermFactor F U n i).obj.obj (op ⊤) ≅
      F.obj.obj (op (∏ᶜ fun k : Fin (n + 1) => U (i k))) :=
  F.obj.mapIso (eqToIso (congrArg op
    ((Opens.functor_map_eq_inf
      (∏ᶜ fun k : Fin (n + 1) => U (i k)) ⊤).trans
        (top_inf_eq (∏ᶜ fun k : Fin (n + 1) => U (i k))))))

/-- Top sections of a module-valued sheaf Cech term agree with the
corresponding degree of the native module-valued Cech complex. -/
noncomputable def moduleCechTermTopSectionsIso :
    (moduleCechTerm F U n).obj.obj (op ⊤) ≅
      ((cechComplexFunctor U).obj F.obj).X n :=
  moduleCechTermTopRawIso F U n ≪≫
    Pi.mapIso (moduleCechTermFactorTopIso F U n)

/-- The top-sections comparison followed by a native product projection is the
sheaf-product projection followed by `⊤ ⊓ A = A`. -/
theorem moduleCechTermTopSectionsIso_hom_π
    (i : Fin (n + 1) → ι) :
    (moduleCechTermTopSectionsIso F U n).hom ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          F.obj.obj (op (∏ᶜ fun k : Fin (n + 1) => U (j k)))) i =
      (Pi.π (moduleCechTermFactor F U n) i).hom.app (op ⊤) ≫
        (moduleCechTermFactorTopIso F U n i).hom := by
  calc
    _ = ((moduleCechTermTopRawIso F U n).hom ≫
          (Pi.mapIso (moduleCechTermFactorTopIso F U n)).hom) ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          F.obj.obj (op (∏ᶜ fun k : Fin (n + 1) => U (j k)))) i := by
      rfl
    _ = (moduleCechTermTopRawIso F U n).hom ≫
        ((Pi.mapIso (moduleCechTermFactorTopIso F U n)).hom ≫
          Pi.π (fun j : Fin (n + 1) → ι =>
            F.obj.obj (op (∏ᶜ fun k : Fin (n + 1) => U (j k)))) i) :=
      Category.assoc _ _ _
    _ = (moduleCechTermTopRawIso F U n).hom ≫
        (Pi.π (fun j : Fin (n + 1) → ι =>
            (moduleCechTermFactor F U n j).obj.obj (op ⊤)) i ≫
          (moduleCechTermFactorTopIso F U n i).hom) := by
      rw [Pi.mapIso_hom_π]
    _ = ((moduleCechTermTopRawIso F U n).hom ≫
          Pi.π (fun j : Fin (n + 1) → ι =>
            (moduleCechTermFactor F U n j).obj.obj (op ⊤)) i) ≫
        (moduleCechTermFactorTopIso F U n i).hom :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg
      (fun f => f ≫ (moduleCechTermFactorTopIso F U n i).hom)
      (moduleCechTermTopRawIso_hom_π F U n i)

end TopCat.Sheaf

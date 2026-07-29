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

private noncomputable def moduleCechTermForgetTopIso :
    (moduleCechTerm F U n).obj.obj (op ⊤) ≅
      ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op ⊤)).obj
        (∏ᶜ fun i : Fin (n + 1) → ι =>
          (moduleCechTermFactor F U n i).obj) :=
  ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op ⊤)).mapIso
    (moduleCechTermForgetIso F U n)

private noncomputable def moduleCechTermEvaluationDiagramIso :
    (Discrete.functor fun i : Fin (n + 1) → ι =>
        (moduleCechTermFactor F U n i).obj) ⋙
        (evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op ⊤) ≅
      Discrete.functor fun i : Fin (n + 1) → ι =>
        (moduleCechTermFactor F U n i).obj.obj (op ⊤) :=
  Discrete.natIso fun _ => Iso.refl _

private noncomputable def moduleCechTermEvaluationIso :
    ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op ⊤)).obj
        (∏ᶜ fun i : Fin (n + 1) → ι =>
          (moduleCechTermFactor F U n i).obj) ≅
      ∏ᶜ fun i : Fin (n + 1) → ι =>
        (moduleCechTermFactor F U n i).obj.obj (op ⊤) := by
  letI : HasLimit ((Discrete.functor fun i : Fin (n + 1) → ι =>
      (moduleCechTermFactor F U n i).obj) ⋙
        (evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op ⊤)) :=
    hasLimit_of_iso (moduleCechTermEvaluationDiagramIso F U n).symm
  exact preservesLimitIso
      ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op ⊤))
      (Discrete.functor fun i : Fin (n + 1) → ι =>
        (moduleCechTermFactor F U n i).obj) ≪≫
    HasLimit.isoOfNatIso (moduleCechTermEvaluationDiagramIso F U n)

private theorem moduleCechTermEvaluationIso_hom_π
    (i : Fin (n + 1) → ι) :
    (moduleCechTermEvaluationIso F U n).hom ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          (moduleCechTermFactor F U n j).obj.obj (op ⊤)) i =
      ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op ⊤)).map
        (Pi.π (fun j : Fin (n + 1) → ι =>
          (moduleCechTermFactor F U n j).obj) i) := by
  change (moduleCechTermEvaluationIso F U n).hom ≫
      limit.π (Discrete.functor fun j : Fin (n + 1) → ι =>
        (moduleCechTermFactor F U n j).obj.obj (op ⊤)) ⟨i⟩ =
    ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op ⊤)).map
      (limit.π (Discrete.functor fun j : Fin (n + 1) → ι =>
        (moduleCechTermFactor F U n j).obj) ⟨i⟩)
  letI : HasLimit ((Discrete.functor fun i : Fin (n + 1) → ι =>
      (moduleCechTermFactor F U n i).obj) ⋙
        (evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op ⊤)) :=
    hasLimit_of_iso (moduleCechTermEvaluationDiagramIso F U n).symm
  have hnat :
      (HasLimit.isoOfNatIso
          (moduleCechTermEvaluationDiagramIso F U n)).hom ≫
          limit.π (Discrete.functor fun j : Fin (n + 1) → ι =>
            (moduleCechTermFactor F U n j).obj.obj (op ⊤)) ⟨i⟩ =
        limit.π ((Discrete.functor fun j : Fin (n + 1) → ι =>
          (moduleCechTermFactor F U n j).obj) ⋙
            (evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op ⊤)) ⟨i⟩ := by
    calc
      _ = limit.π ((Discrete.functor fun j : Fin (n + 1) → ι =>
            (moduleCechTermFactor F U n j).obj) ⋙
              (evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op ⊤)) ⟨i⟩ ≫
          (moduleCechTermEvaluationDiagramIso F U n).hom.app ⟨i⟩ :=
        HasLimit.isoOfNatIso_hom_π
          (moduleCechTermEvaluationDiagramIso F U n) ⟨i⟩
      _ = _ := Category.comp_id _
  have hpreserves :
      (preservesLimitIso
          ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op ⊤))
          (Discrete.functor fun j : Fin (n + 1) → ι =>
            (moduleCechTermFactor F U n j).obj)).hom ≫
          limit.π ((Discrete.functor fun j : Fin (n + 1) → ι =>
            (moduleCechTermFactor F U n j).obj) ⋙
              (evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op ⊤)) ⟨i⟩ =
        ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op ⊤)).map
          (limit.π (Discrete.functor fun j : Fin (n + 1) → ι =>
            (moduleCechTermFactor F U n j).obj) ⟨i⟩) :=
    preservesLimitIso_hom_π
      ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op ⊤))
      (Discrete.functor fun j : Fin (n + 1) → ι =>
        (moduleCechTermFactor F U n j).obj) ⟨i⟩
  have hcombined :
      (preservesLimitIso
          ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op ⊤))
          (Discrete.functor fun j : Fin (n + 1) → ι =>
            (moduleCechTermFactor F U n j).obj)).hom ≫
          ((HasLimit.isoOfNatIso
              (moduleCechTermEvaluationDiagramIso F U n)).hom ≫
            limit.π (Discrete.functor fun j : Fin (n + 1) → ι =>
              (moduleCechTermFactor F U n j).obj.obj (op ⊤)) ⟨i⟩) =
        ((evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op ⊤)).map
          (limit.π (Discrete.functor fun j : Fin (n + 1) → ι =>
            (moduleCechTermFactor F U n j).obj) ⟨i⟩) := by
    rw [hnat]
    exact hpreserves
  simpa only [moduleCechTermEvaluationIso, Iso.trans_hom,
    Category.assoc] using hcombined

private noncomputable def moduleCechTermTopRawIso :
    (moduleCechTerm F U n).obj.obj (op ⊤) ≅
      ∏ᶜ fun i : Fin (n + 1) → ι =>
        (moduleCechTermFactor F U n i).obj.obj (op ⊤) :=
  moduleCechTermForgetTopIso F U n ≪≫
    moduleCechTermEvaluationIso F U n

private theorem moduleCechTermTopRawIso_hom_π
    (i : Fin (n + 1) → ι) :
    (moduleCechTermTopRawIso F U n).hom ≫
        Pi.π (fun j : Fin (n + 1) → ι =>
          (moduleCechTermFactor F U n j).obj.obj (op ⊤)) i =
      (Pi.π (moduleCechTermFactor F U n) i).hom.app (op ⊤) := by
  rw [moduleCechTermTopRawIso, Iso.trans_hom, Category.assoc,
    moduleCechTermEvaluationIso_hom_π]
  exact congr_app (moduleCechTermForgetIso_hom_π F U n i) (op ⊤)

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

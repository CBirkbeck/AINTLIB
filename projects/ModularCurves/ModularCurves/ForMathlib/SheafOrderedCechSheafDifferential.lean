import ModularCurves.ForMathlib.SheafCechSheafDifferential
import ModularCurves.ForMathlib.SheafOrderedCechSheafTerms

/-!
# The differential in the ordered sheaf-level Cech resolution

This file defines the cofaces and alternating differential on the sheaf-level
Cech terms indexed by strictly increasing tuples. The component formulas
identify these maps with the ordered Cech differential on sections.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

open AlgebraicGeometry.Scheme.Modules

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} [LinearOrder ι] (U : ι → Opens X) (n : ℕ)

private theorem orderedCechTupleLE (k : Fin (n + 2))
    (i : OrderedCechIndex ι (n + 1)) :
    (∏ᶜ fun a : Fin (n + 2) => U (i.1 a)) ≤
      ∏ᶜ fun a : Fin (n + 1) => U ((i.delete k).1 a) :=
  leOfHom (((FormalCoproduct.mk _ U).mapPower
    (SimplexCategory.δ k).toOrderHom.toFun).φ i.1)

/-- The ordered sheaf-level Cech coface obtained by deleting the `k`th entry. -/
noncomputable def orderedCechCoface (k : Fin (n + 2)) :
    orderedCechTerm F U n ⟶ orderedCechTerm F U (n + 1) :=
  Pi.lift (fun i : OrderedCechIndex ι (n + 1) =>
    Pi.π (orderedCechTermFactor F U n) (i.delete k) ≫
      cechTermFactorRestriction F (orderedCechTupleLE U n k i))

/-- Under the concrete section equivalence, an ordered sheaf-level Cech
coface restricts the component indexed by deletion of the `k`th entry. -/
theorem orderedCechCoface_apply (V : Opens X)
    (x : (orderedCechTerm F U n).obj.obj (op V))
    (k : Fin (n + 2)) (i : OrderedCechIndex ι (n + 1)) :
    orderedCechTermSectionsAddEquiv F U (n + 1) V
        ((orderedCechCoface F U n k).hom.app (op V) x) i =
      F.obj.map (homOfLE (inf_le_inf_left V
        (orderedCechTupleLE U n k i))).op
        (orderedCechTermSectionsAddEquiv F U n V x (i.delete k)) := by
  rw [orderedCechTermSectionsAddEquiv_apply]
  have hcoface :
      orderedCechCoface F U n k ≫
          Pi.π (orderedCechTermFactor F U (n + 1)) i =
        Pi.π (orderedCechTermFactor F U n) (i.delete k) ≫
          cechTermFactorRestriction F (orderedCechTupleLE U n k i) := by
    change
      Pi.lift (fun i : OrderedCechIndex ι (n + 1) =>
          Pi.π (orderedCechTermFactor F U n) (i.delete k) ≫
            cechTermFactorRestriction F
              (orderedCechTupleLE U n k i)) ≫
          Pi.π (orderedCechTermFactor F U (n + 1)) i =
        Pi.π (orderedCechTermFactor F U n) (i.delete k) ≫
          cechTermFactorRestriction F (orderedCechTupleLE U n k i)
    exact Pi.lift_π _ i
  have hcomponent :
      (Pi.π (orderedCechTermFactor F U (n + 1)) i).hom.app (op V)
          ((orderedCechCoface F U n k).hom.app (op V) x) =
        (cechTermFactorRestriction F
            (orderedCechTupleLE U n k i)).hom.app (op V)
          ((Pi.π (orderedCechTermFactor F U n)
            (i.delete k)).hom.app (op V) x) := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun f => f.hom.app (op V)) hcoface) x
  rw [hcomponent, cechTermFactorRestriction_apply,
    ← orderedCechTermSectionsAddEquiv_apply]

/-- The alternating differential in the ordered sheaf-level Cech resolution. -/
noncomputable def orderedCechDifferential :
    orderedCechTerm F U n ⟶ orderedCechTerm F U (n + 1) :=
  ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
    orderedCechCoface F U n k

private theorem orderedSheafSumApplyFinset
    {A B : Sheaf AddCommGrpCat.{u} X} {κ : Type*}
    (s : Finset κ) (f : κ → (A ⟶ B)) (V : (Opens X)ᵒᵖ)
    (x : A.obj.obj V) :
    (∑ i ∈ s, f i).hom.app V x = ∑ i ∈ s, (f i).hom.app V x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      change (f a).hom.app V x + (∑ i ∈ s, f i).hom.app V x = _
      rw [ih]

private theorem orderedSheafSumApply
    {A B : Sheaf AddCommGrpCat.{u} X} {κ : Type*} [Fintype κ]
    (f : κ → (A ⟶ B)) (V : (Opens X)ᵒᵖ) (x : A.obj.obj V) :
    (∑ i, f i).hom.app V x = ∑ i, (f i).hom.app V x :=
  orderedSheafSumApplyFinset Finset.univ f V x

/-- Under the concrete section equivalence, the ordered sheaf-level Cech
differential is the alternating sum of tuple-deletion restrictions. -/
theorem orderedCechDifferential_apply (V : Opens X)
    (x : (orderedCechTerm F U n).obj.obj (op V))
    (i : OrderedCechIndex ι (n + 1)) :
    orderedCechTermSectionsAddEquiv F U (n + 1) V
        ((orderedCechDifferential F U n).hom.app (op V) x) i =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        F.obj.map (homOfLE (inf_le_inf_left V
          (orderedCechTupleLE U n k i))).op
          (orderedCechTermSectionsAddEquiv F U n V x (i.delete k)) := by
  rw [orderedCechDifferential]
  calc
    _ = orderedCechTermSectionsAddEquiv F U (n + 1) V
        (∑ k : Fin (n + 2),
          ((-1 : ℤ) ^ (k : ℕ) •
            orderedCechCoface F U n k).hom.app (op V) x) i :=
      congrArg
        (fun y => orderedCechTermSectionsAddEquiv F U (n + 1) V y i)
        (orderedSheafSumApply _ (op V) x)
    _ = (∑ k : Fin (n + 2),
        orderedCechTermSectionsAddEquiv F U (n + 1) V
          (((-1 : ℤ) ^ (k : ℕ) •
            orderedCechCoface F U n k).hom.app (op V) x)) i := by
      rw [map_sum]
    _ = ∑ k : Fin (n + 2),
        orderedCechTermSectionsAddEquiv F U (n + 1) V
          (((-1 : ℤ) ^ (k : ℕ) •
            orderedCechCoface F U n k).hom.app (op V) x) i :=
      Finset.sum_apply i Finset.univ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      change orderedCechTermSectionsAddEquiv F U (n + 1) V
          ((-1 : ℤ) ^ (k : ℕ) •
            ((orderedCechCoface F U n k).hom.app (op V) x)) i = _
      rw [map_zsmul, Pi.smul_apply, orderedCechCoface_apply]

end TopCat.Sheaf

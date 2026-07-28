import ModularCurves.ForMathlib.SheafOrderedCechSheafComplex

/-!
# Projection from native to ordered sheaf-level Cech cochains

The native all-tuples Cech complex projects onto the complex indexed by
strictly increasing tuples. This file constructs that projection as a chain
map.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
  TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

open AlgebraicGeometry.Scheme.Modules

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} [LinearOrder ι] (U : ι → Opens X)

/-- Degreewise projection from native Cech terms to ordered Cech terms. -/
noncomputable def cechToOrderedF (n : ℕ) :
    cechTerm F U n ⟶ orderedCechTerm F U n :=
  Pi.lift fun i : OrderedCechIndex ι n =>
    Pi.π (cechTermFactor F U n) i.1

theorem cechToOrderedF_comp_π (n : ℕ)
    (i : OrderedCechIndex ι n) :
    cechToOrderedF F U n ≫
        Pi.π (orderedCechTermFactor F U n) i =
      Pi.π (cechTermFactor F U n) i.1 := by
  change
    Pi.lift (fun i : OrderedCechIndex ι n =>
      Pi.π (cechTermFactor F U n) i.1) ≫
        Pi.π (orderedCechTermFactor F U n) i =
      Pi.π (cechTermFactor F U n) i.1
  exact Pi.lift_π _ i

/-- On sections, `cechToOrderedF` forgets all components except the strictly
increasing ones. -/
theorem cechToOrderedF_apply (n : ℕ) (V : Opens X)
    (x : (cechTerm F U n).obj.obj (op V))
    (i : OrderedCechIndex ι n) :
    orderedCechTermSectionsAddEquiv F U n V
        ((cechToOrderedF F U n).hom.app (op V) x) i =
      cechTermSectionsAddEquiv F U n V x i.1 := by
  rw [orderedCechTermSectionsAddEquiv_apply,
    cechTermSectionsAddEquiv_apply]
  have hcomponent :
      (Pi.π (orderedCechTermFactor F U n) i).hom.app (op V)
          ((cechToOrderedF F U n).hom.app (op V) x) =
        (Pi.π (cechTermFactor F U n) i.1).hom.app (op V) x :=
    ConcreteCategory.congr_hom
      (congrArg (fun f => f.hom.app (op V))
        (cechToOrderedF_comp_π F U n i)) x
  rw [hcomponent]

private theorem cechCoface_comp_cechToOrderedF (n : ℕ)
    (k : Fin (n + 2)) :
    cechCoface F U n k ≫ cechToOrderedF F U (n + 1) =
      cechToOrderedF F U n ≫ orderedCechCoface F U n k := by
  apply Pi.hom_ext
  intro i
  let p : orderedCechTerm F U (n + 1) ⟶
      orderedCechTermFactor F U (n + 1) i :=
    Pi.π (orderedCechTermFactor F U (n + 1)) i
  let q : cechTerm F U (n + 1) ⟶
      cechTermFactor F U (n + 1) i.1 :=
    Pi.π (cechTermFactor F U (n + 1)) i.1
  let r : orderedCechTerm F U n ⟶
      orderedCechTermFactor F U n (i.delete k) :=
    Pi.π (orderedCechTermFactor F U n) (i.delete k)
  let s : cechTerm F U n ⟶
      cechTermFactor F U n (i.delete k).1 :=
    Pi.π (cechTermFactor F U n) (i.delete k).1
  let e : cechTermFactor F U n (i.delete k).1 ⟶
      cechTermFactor F U (n + 1) i.1 :=
    cechTermFactorRestriction F
      (leOfHom (((FormalCoproduct.mk _ U).mapPower
        (SimplexCategory.δ k).toOrderHom.toFun).φ i.1))
  have hp : cechToOrderedF F U (n + 1) ≫ p = q :=
    cechToOrderedF_comp_π F U (n + 1) i
  have hr : cechToOrderedF F U n ≫ r = s :=
    cechToOrderedF_comp_π F U n (i.delete k)
  have hnative : cechCoface F U n k ≫ q = s ≫ e := by
    dsimp only [q, s, e]
    exact Pi.lift_π _ i.1
  have hordered : orderedCechCoface F U n k ≫ p = r ≫ e := by
    dsimp only [p, r, e]
    exact Pi.lift_π _ i
  calc
    (cechCoface F U n k ≫ cechToOrderedF F U (n + 1)) ≫ p =
        cechCoface F U n k ≫ q := by
      rw [Category.assoc, hp]
    _ = s ≫ e := hnative
    _ = cechToOrderedF F U n ≫
        (r ≫ e) := by
      rw [← Category.assoc, hr]
    _ = (cechToOrderedF F U n ≫
        orderedCechCoface F U n k) ≫ p := by
      rw [Category.assoc, hordered]

/-- The native-to-ordered projection commutes with Cech differentials. -/
theorem cechToOrderedF_comp_d (n : ℕ) :
    cechDifferential F U n ≫ cechToOrderedF F U (n + 1) =
      cechToOrderedF F U n ≫ orderedCechDifferential F U n := by
  rw [cechDifferential, orderedCechDifferential,
    sum_comp, comp_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [zsmul_comp, comp_zsmul, cechCoface_comp_cechToOrderedF]

/-- Projection from the native sheaf-level Cech complex to the ordered one. -/
noncomputable def cechToOrdered :
    cechComplex F U ⟶ orderedCechComplex F U :=
  CochainComplex.ofHom (cechToOrderedF F U) fun n => by
    rw [cechComplex_d, orderedCechComplex_d]
    exact (cechToOrderedF_comp_d F U n).symm

@[simp]
theorem cechToOrdered_f (n : ℕ) :
    (cechToOrdered F U).f n = cechToOrderedF F U n :=
  rfl

end TopCat.Sheaf

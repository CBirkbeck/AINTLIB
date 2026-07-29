import Mathlib.Algebra.Homology.Augment
import ModularCurves.ForMathlib.SheafCechSheafResolution
import ModularCurves.ForMathlib.SheafOrderedCechAlternatingChain

/-!
# The augmented ordered sheaf-level Cech resolution

In degree zero, every tuple is strictly increasing, so projection from native
Cech cochains to ordered Cech cochains is an isomorphism. This extends the
native-to-ordered chain retract across the augmentation and transfers
acyclicity of the native augmented resolution.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace TopCat.Sheaf

open AlgebraicGeometry.Scheme.Modules

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} [LinearOrder ι] (U : ι → Opens X)

private theorem strictMono_fin_one (i : Fin 1 → ι) : StrictMono i := by
  intro a b hab
  have hab' : a = b := Subsingleton.elim _ _
  subst b
  exact (lt_irrefl a hab).elim

/-- In degree zero, projection to increasing tuples followed by alternating
extension is the identity. -/
theorem cechToOrderedF_comp_orderedToCechAlternatingF_zero :
    cechToOrderedF F U 0 ≫
        orderedToCechAlternatingF F U 0 =
      𝟙 (cechTerm F U 0) := by
  let A : Sheaf AddCommGrpCat X := cechTerm F U 0
  let B : Sheaf AddCommGrpCat X := orderedCechTerm F U 0
  let p : A ⟶ B := cechToOrderedF F U 0
  let s : B ⟶ A := orderedToCechAlternatingF F U 0
  change p ≫ s = 𝟙 A
  change p ≫ s =
    𝟙 (∏ᶜ fun i : Fin 1 → ι => cechTermFactor F U 0 i)
  apply Pi.hom_ext
  intro i
  let hi : StrictMono i := strictMono_fin_one i
  let j : OrderedCechIndex ι 0 := ⟨i, hi⟩
  let C : Sheaf AddCommGrpCat X := cechTermFactor F U 0 i
  let r : A ⟶ C := Pi.π (cechTermFactor F U 0) i
  let q : B ⟶ C := Pi.π (orderedCechTermFactor F U 0) j
  have hs : s ≫ r = q := by
    dsimp only [s, r, q, j, A, B, C]
    exact
      orderedToCechAlternatingF_comp_π_of_strictMono F U 0 i hi
  have hp : p ≫ q = r := by
    dsimp only [p, q, r, A, B, C]
    exact cechToOrderedF_comp_π F U 0 j
  change (p ≫ s) ≫ r = 𝟙 A ≫ r
  rw [Category.assoc, hs, hp, Category.id_comp]

/-- The augmentation into the ordered sheaf-level Cech complex. -/
noncomputable def orderedCechAugmentation :
    F ⟶ orderedCechTerm F U 0 :=
  cechAugmentation F U ≫ cechToOrderedF F U 0

private theorem orderedCechAugmentation_comp :
    orderedCechAugmentation F U ≫
        orderedCechDifferential F U 0 = 0 := by
  rw [orderedCechAugmentation, Category.assoc,
    ← cechToOrderedF_comp_d, ← Category.assoc,
    cechAugmentation_comp, zero_comp]

/-- The ordered sheaf-level Cech complex augmented by the original sheaf in
degree zero. -/
noncomputable def orderedCechAugmentedComplex :
    CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ :=
  CochainComplex.augment (orderedCechComplex F U)
    (orderedCechAugmentation F U)
    (by
      rw [orderedCechComplex_d]
      exact orderedCechAugmentation_comp F U)

private noncomputable def cechAugmentedToOrderedF :
    ∀ n,
      (cechAugmentedComplex F U).X n ⟶
        (orderedCechAugmentedComplex F U).X n
  | 0 => 𝟙 F
  | n + 1 => (cechToOrdered F U).f n

private theorem cechAugmentedToOrderedF_comp_d (n : ℕ) :
    cechAugmentedToOrderedF F U n ≫
        (orderedCechAugmentedComplex F U).d n (n + 1) =
      (cechAugmentedComplex F U).d n (n + 1) ≫
        cechAugmentedToOrderedF F U (n + 1) := by
  cases n with
  | zero =>
      change 𝟙 F ≫ orderedCechAugmentation F U =
        cechAugmentation F U ≫ cechToOrderedF F U 0
      rw [Category.id_comp]
      rfl
  | succ n =>
      dsimp only [cechAugmentedToOrderedF]
      unfold orderedCechAugmentedComplex cechAugmentedComplex
      change (cechToOrdered F U).f n ≫
          (orderedCechComplex F U).d n (n + 1) =
        (cechComplex F U).d n (n + 1) ≫
          (cechToOrdered F U).f (n + 1)
      exact (cechToOrdered F U).comm n (n + 1)

private noncomputable def cechAugmentedToOrdered :
    cechAugmentedComplex F U ⟶ orderedCechAugmentedComplex F U :=
  CochainComplex.ofHom (cechAugmentedToOrderedF F U)
    (cechAugmentedToOrderedF_comp_d F U)

private noncomputable def orderedAugmentedToCechF :
    ∀ n,
      (orderedCechAugmentedComplex F U).X n ⟶
        (cechAugmentedComplex F U).X n
  | 0 => 𝟙 F
  | n + 1 => (orderedToCechAlternating F U).f n

private theorem orderedAugmentedToCechF_comp_d (n : ℕ) :
    orderedAugmentedToCechF F U n ≫
        (cechAugmentedComplex F U).d n (n + 1) =
      (orderedCechAugmentedComplex F U).d n (n + 1) ≫
        orderedAugmentedToCechF F U (n + 1) := by
  cases n with
  | zero =>
      change 𝟙 F ≫ cechAugmentation F U =
        orderedCechAugmentation F U ≫
          orderedToCechAlternatingF F U 0
      rw [Category.id_comp]
      let A : Sheaf AddCommGrpCat X := cechTerm F U 0
      let B : Sheaf AddCommGrpCat X := orderedCechTerm F U 0
      let a : F ⟶ A := cechAugmentation F U
      let p : A ⟶ B := cechToOrderedF F U 0
      let s : B ⟶ A := orderedToCechAlternatingF F U 0
      have hps : p ≫ s = 𝟙 A := by
        dsimp only [p, s, A, B]
        exact
          cechToOrderedF_comp_orderedToCechAlternatingF_zero F U
      change a = (a ≫ p) ≫ s
      rw [Category.assoc, hps, Category.comp_id]
  | succ n =>
      dsimp only [orderedAugmentedToCechF]
      unfold orderedCechAugmentedComplex cechAugmentedComplex
      change (orderedToCechAlternating F U).f n ≫
          (cechComplex F U).d n (n + 1) =
        (orderedCechComplex F U).d n (n + 1) ≫
          (orderedToCechAlternating F U).f (n + 1)
      exact (orderedToCechAlternating F U).comm n (n + 1)

private noncomputable def orderedAugmentedToCech :
    orderedCechAugmentedComplex F U ⟶ cechAugmentedComplex F U :=
  CochainComplex.ofHom (orderedAugmentedToCechF F U)
    (orderedAugmentedToCechF_comp_d F U)

private theorem orderedAugmentedToCech_comp_cechAugmentedToOrdered :
    orderedAugmentedToCech F U ≫ cechAugmentedToOrdered F U =
      𝟙 (orderedCechAugmentedComplex F U) := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
      exact Category.comp_id (𝟙 F)
  | succ n =>
      exact orderedToCechAlternatingF_comp_cechToOrderedF F U n

/-- The augmented ordered sheaf-level Cech complex of an open cover is
acyclic. -/
theorem orderedCechAugmentedComplex_acyclic (hU : ⨆ i, U i = ⊤) :
    (orderedCechAugmentedComplex F U).Acyclic := by
  have hnative := cechAugmentedComplex_acyclic F U hU
  rw [HomologicalComplex.acyclic_iff] at hnative ⊢
  intro n
  exact (hnative n).of_retract
    (orderedAugmentedToCech F U)
    (cechAugmentedToOrdered F U)
    (orderedAugmentedToCech_comp_cechAugmentedToOrdered F U)

end TopCat.Sheaf

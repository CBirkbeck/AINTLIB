module

public import BernoulliRegular.UnitQuotient.FreeLatticeComparison.FreeTrace
public import Mathlib.RepresentationTheory.Basic

/-!
# Unit quotients: mod-p free quotient representation

This file reduces the free unit quotient modulo p, constructs the even-Delta
representation, and computes the traces of its character projectors.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

open Finset

set_option linter.unusedSectionVars false

attribute [local instance] Fintype.ofFinite
attribute [local instance] NumberField.Units.instZLattice_unitLattice

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The element `-1 ∈ Delta` acts trivially on every unit class after reducing
the torsion-free quotient modulo `p`. -/
theorem cyclotomicUnitFreePartModPLinearEquiv_neg_one_apply_class
    (hp_gt_two : 2 < p) (u : CyclotomicUnitGroup K) :
    cyclotomicUnitFreePartModPLinearEquiv (p := p) K (-1)
        (cyclotomicUnitFreePartModPClass (p := p) K
          (Additive.ofMul (cyclotomicUnitFreeClass K u))) =
      cyclotomicUnitFreePartModPClass (p := p) K
        (Additive.ofMul (cyclotomicUnitFreeClass K u)) := by
  rw [cyclotomicUnitFreePartModPLinearEquiv_apply_class,
    cyclotomicUnitFreePartLinearEquiv_neg_one_apply_class
      (p := p) (K := K) hp_gt_two]

/-- The element `-1 ∈ Delta` acts trivially on the whole mod-`p` reduction of
the torsion-free unit quotient. -/
theorem cyclotomicUnitFreePartModPLinearEquiv_neg_one_apply
    (hp_gt_two : 2 < p) (x : CyclotomicUnitFreePartModP (p := p) K) :
    cyclotomicUnitFreePartModPLinearEquiv (p := p) K (-1) x = x := by
  refine Submodule.Quotient.induction_on
    (CyclotomicUnitFreePartPMultipleSubmodule (p := p) K) x ?_
  intro y
  change cyclotomicUnitFreePartModPLinearEquiv (p := p) K (-1)
      (cyclotomicUnitFreePartModPClass (p := p) K y) =
    cyclotomicUnitFreePartModPClass (p := p) K y
  rw [cyclotomicUnitFreePartModPLinearEquiv_apply_class,
    cyclotomicUnitFreePartLinearEquiv_neg_one_apply
      (p := p) (K := K) hp_gt_two]

/-- The Dirichlet basis of the torsion-free unit quotient reduces to a
`ZMod p`-basis of the mod-`p` free quotient. -/
noncomputable def cyclotomicUnitFreePartModPBasis :
    Module.Basis (Fin (NumberField.Units.rank K)) (ZMod p)
      (CyclotomicUnitFreePartModP (p := p) K) :=
  ModN.basis (cyclotomicUnitFreeBasis K)

@[simp]
theorem cyclotomicUnitFreePartModPBasis_repr_class_apply
    (x : CyclotomicUnitFreePart K) (i : Fin (NumberField.Units.rank K)) :
    (cyclotomicUnitFreePartModPBasis (p := p) K).repr
        (cyclotomicUnitFreePartModPClass (p := p) K x) i =
      ((cyclotomicUnitFreeBasis K).repr x i : ZMod p) := by
  let b := cyclotomicUnitFreeBasis K
  let bmod := cyclotomicUnitFreePartModPBasis (p := p) K
  have hsum :
      cyclotomicUnitFreePartModPClass (p := p) K x =
        ∑ j, (((b.repr x) j : ℤ) : ZMod p) • bmod j := by
    calc
      cyclotomicUnitFreePartModPClass (p := p) K x =
          cyclotomicUnitFreePartModPClass (p := p) K (∑ j, b.repr x j • b j) := by
            rw [b.sum_repr]
      _ = ∑ j, cyclotomicUnitFreePartModPClass (p := p) K (b.repr x j • b j) := by
            rw [map_sum]
      _ = ∑ j, (((b.repr x) j : ℤ) : ZMod p) •
          cyclotomicUnitFreePartModPClass (p := p) K (b j) := by
          apply Finset.sum_congr rfl
          intro j _
          simp [Int.cast_smul_eq_zsmul]
      _ = ∑ j, (((b.repr x) j : ℤ) : ZMod p) • bmod j := by
        simp [b, bmod, cyclotomicUnitFreePartModPBasis, ModN.basis_apply_eq_mkQ]
  calc
    (bmod.repr (cyclotomicUnitFreePartModPClass (p := p) K x)) i
      = (bmod.repr (∑ j, (((b.repr x) j : ℤ) : ZMod p) • bmod j)) i := by
          rw [hsum]
    _ = ((b.repr x i : ℤ) : ZMod p) := by
          rw [bmod.repr_sum_self]

/-- The mod-`p` free quotient has dimension equal to the Dirichlet unit
rank. -/
theorem cyclotomicUnitFreePartModP_finrank :
    Module.finrank (ZMod p) (CyclotomicUnitFreePartModP (p := p) K) =
      NumberField.Units.rank K := by
  rw [Module.finrank_eq_card_basis (cyclotomicUnitFreePartModPBasis (p := p) K),
    Fintype.card_fin]

/-- In the `p`-th cyclotomic field with `p > 2`, the reduced free quotient
has the expected cyclotomic unit rank `(p - 3) / 2`. -/
theorem cyclotomicUnitFreePartModP_finrank_eq
    (hp_gt_two : 2 < p) :
    Module.finrank (ZMod p) (CyclotomicUnitFreePartModP (p := p) K) =
      (p - 3) / 2 := by
  rw [cyclotomicUnitFreePartModP_finrank]
  rw [NumberField.Units.rank]
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  rw [IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := p) K hp_gt_two]
  rw [zero_add]
  rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (n := p) K]
  rw [Nat.totient_prime (Fact.out : p.Prime)]
  omega

theorem cyclotomicUnitFreePart_rank_add_one_eq_evenDelta_card
    (hp_gt_two : 2 < p) :
    NumberField.Units.rank K + 1 = Fintype.card (CyclotomicEvenDelta p) := by
  rw [← cyclotomicUnitFreePartModP_finrank (p := p) (K := K),
    cyclotomicUnitFreePartModP_finrank_eq (p := p) (K := K) hp_gt_two,
    cyclotomicEvenDelta_card (p := p) hp_gt_two]
  omega

theorem cyclotomicUnitFreePart_rank_add_one_eq_evenDelta_card_zmod
    (hp_gt_two : 2 < p) :
    (NumberField.Units.rank K : ZMod p) + 1 =
      (Fintype.card (CyclotomicEvenDelta p) : ZMod p) := by
  have h := congrArg (fun n : ℕ => (n : ZMod p))
    (cyclotomicUnitFreePart_rank_add_one_eq_evenDelta_card
      (p := p) (K := K) hp_gt_two)
  simpa [Nat.cast_add, Nat.cast_one] using h

open Classical in
/-- The reduced free quotient has dimension equal to the number of nontrivial
even `ZMod p`-valued characters. -/
theorem cyclotomicUnitFreePartModP_finrank_eq_evenDeltaNontrivialCharacter_card
    (hp_gt_two : 2 < p) :
    Module.finrank (ZMod p) (CyclotomicUnitFreePartModP (p := p) K) =
      ((Finset.univ : Finset (MulChar (CyclotomicEvenDelta p) (ZMod p))).filter
        (fun χ => χ ≠ 1)).card := by
  rw [cyclotomicUnitFreePartModP_finrank_eq (p := p) (K := K) hp_gt_two,
    evenDeltaNontrivialCharacter_card_eq (p := p) hp_gt_two]

/-- The reduced free-quotient action is `ZMod p`-linear, not only
`Z`-linear. -/
noncomputable def cyclotomicUnitFreePartModPLinearEquivZMod
    (a : CyclotomicUnitDelta p) :
    CyclotomicUnitFreePartModP (p := p) K ≃ₗ[ZMod p]
      CyclotomicUnitFreePartModP (p := p) K where
  toFun := cyclotomicUnitFreePartModPLinearEquiv (p := p) K a
  invFun := (cyclotomicUnitFreePartModPLinearEquiv (p := p) K a).symm
  left_inv := (cyclotomicUnitFreePartModPLinearEquiv (p := p) K a).left_inv
  right_inv := (cyclotomicUnitFreePartModPLinearEquiv (p := p) K a).right_inv
  map_add' x y :=
    map_add (cyclotomicUnitFreePartModPLinearEquiv (p := p) K a) x y
  map_smul' c x :=
    ZMod.map_smul
      ((cyclotomicUnitFreePartModPLinearEquiv (p := p) K a).toAddEquiv.toAddMonoidHom) c x

@[simp]
theorem cyclotomicUnitFreePartModPLinearEquivZMod_apply
    (a : CyclotomicUnitDelta p) (x : CyclotomicUnitFreePartModP (p := p) K) :
    cyclotomicUnitFreePartModPLinearEquivZMod (p := p) K a x =
      cyclotomicUnitFreePartModPLinearEquiv (p := p) K a x :=
  rfl

@[simp]
theorem cyclotomicUnitFreePartModPLinearEquiv_toMatrix_apply
    (a : CyclotomicUnitDelta p)
    (i j : Fin (NumberField.Units.rank K)) :
    LinearMap.toMatrixAlgEquiv (cyclotomicUnitFreePartModPBasis (p := p) K)
        ((cyclotomicUnitFreePartModPLinearEquivZMod (p := p) K a).toLinearMap) i j =
      ((LinearMap.toMatrixAlgEquiv (cyclotomicUnitFreeBasis K)
          ((cyclotomicUnitFreePartLinearEquiv (p := p) K a).toLinearMap) i j : ℤ) : ZMod p) := by
  rw [LinearMap.toMatrixAlgEquiv_apply]
  change ((cyclotomicUnitFreePartModPBasis (p := p) K).repr
        (cyclotomicUnitFreePartModPLinearEquiv (p := p) K a
          ((cyclotomicUnitFreePartModPBasis (p := p) K) j))) i =
      ((LinearMap.toMatrixAlgEquiv (cyclotomicUnitFreeBasis K)
          ((cyclotomicUnitFreePartLinearEquiv (p := p) K a).toLinearMap) i j : ℤ) : ZMod p)
  rw [cyclotomicUnitFreePartModPBasis, ModN.basis_apply_eq_mkQ,
    cyclotomicUnitFreePartModPLinearEquiv_apply_class,
    LinearMap.toMatrixAlgEquiv_apply]
  simpa [cyclotomicUnitFreePartModPBasis] using
    (cyclotomicUnitFreePartModPBasis_repr_class_apply (p := p) (K := K)
      ((cyclotomicUnitFreePartLinearEquiv (p := p) K a)
        ((cyclotomicUnitFreeBasis K) j)) i)

theorem cyclotomicUnitFreePartModPLinearEquiv_trace
    (a : CyclotomicUnitDelta p) :
    LinearMap.trace (ZMod p) (CyclotomicUnitFreePartModP (p := p) K)
        ((cyclotomicUnitFreePartModPLinearEquivZMod (p := p) K a).toLinearMap) =
      ((LinearMap.trace ℤ (CyclotomicUnitFreePart K)
          ((cyclotomicUnitFreePartLinearEquiv (p := p) K a).toLinearMap) : ℤ) : ZMod p) := by
  rw [LinearMap.trace_eq_matrix_trace
      (b := cyclotomicUnitFreePartModPBasis (p := p) K),
    LinearMap.trace_eq_matrix_trace (b := cyclotomicUnitFreeBasis K)]
  simp only [Matrix.trace, Matrix.diag]
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact cyclotomicUnitFreePartModPLinearEquiv_toMatrix_apply (p := p) (K := K) a i i

theorem cyclotomicUnitFreePartModPLinearEquiv_trace_formula
  [IsZLattice ℝ (NumberField.Units.unitLattice K)]
    (hp_gt_two : 2 < p) (a : CyclotomicUnitDelta p) :
    LinearMap.trace (ZMod p) (CyclotomicUnitFreePartModP (p := p) K)
        ((cyclotomicUnitFreePartModPLinearEquivZMod (p := p) K a).toLinearMap) =
      if cyclotomicEvenDeltaQuotient p a = 1 then
        (NumberField.Units.rank K : ZMod p) else -1 := by
  rw [cyclotomicUnitFreePartModPLinearEquiv_trace,
    cyclotomicUnitFreePartLinearEquiv_trace_formula (p := p) (K := K) hp_gt_two a]
  by_cases hq : cyclotomicEvenDeltaQuotient p a = 1
  · rw [if_pos hq, if_pos hq]
    norm_num
  · rw [if_neg hq, if_neg hq]
    norm_num

/-- The actual `Delta` action on the reduced free quotient, as a genuine
`ZMod p`-linear representation. -/
noncomputable def cyclotomicUnitFreePartModPDeltaActionZMod :
    CyclotomicUnitDelta p →*
      (CyclotomicUnitFreePartModP (p := p) K ≃ₗ[ZMod p]
        CyclotomicUnitFreePartModP (p := p) K) where
  toFun := cyclotomicUnitFreePartModPLinearEquivZMod (p := p) K
  map_one' := by
    ext x
    refine Submodule.Quotient.induction_on
      (CyclotomicUnitFreePartPMultipleSubmodule (p := p) K) x ?_
    intro y
    change cyclotomicUnitFreePartModPClass (p := p) K
        (cyclotomicUnitFreePartLinearEquiv (p := p) K 1 y) =
      cyclotomicUnitFreePartModPClass (p := p) K y
    have hlin :
        cyclotomicUnitFreePartLinearEquiv (p := p) K 1 =
          LinearEquiv.refl ℤ (CyclotomicUnitFreePart K) := by
      change cyclotomicUnitFreePartDeltaAction (p := p) K 1 = 1
      exact map_one (cyclotomicUnitFreePartDeltaAction (p := p) K)
    rw [hlin]
    rfl
  map_mul' := by
    intro a b
    ext x
    refine Submodule.Quotient.induction_on
      (CyclotomicUnitFreePartPMultipleSubmodule (p := p) K) x ?_
    intro y
    change cyclotomicUnitFreePartModPClass (p := p) K
        (cyclotomicUnitFreePartLinearEquiv (p := p) K (a * b) y) =
      cyclotomicUnitFreePartModPClass (p := p) K
        (cyclotomicUnitFreePartLinearEquiv (p := p) K a
          (cyclotomicUnitFreePartLinearEquiv (p := p) K b y))
    have hlin := congrFun
      (congrArg DFunLike.coe
        (map_mul (cyclotomicUnitFreePartDeltaAction (p := p) K) a b)) y
    exact congrArg (cyclotomicUnitFreePartModPClass (p := p) K) hlin

@[simp]
theorem cyclotomicUnitFreePartModPDeltaActionZMod_apply
    (a : CyclotomicUnitDelta p) (x : CyclotomicUnitFreePartModP (p := p) K) :
    cyclotomicUnitFreePartModPDeltaActionZMod (p := p) K a x =
      cyclotomicUnitFreePartModPLinearEquiv (p := p) K a x :=
  cyclotomicUnitFreePartModPLinearEquivZMod_apply (p := p) (K := K) a x

/-- The element `-1` lies in the kernel of the mod-`p` free-quotient
representation. -/
theorem cyclotomicUnitFreePartModPDeltaActionZMod_neg_one_mem_ker
    (hp_gt_two : 2 < p) :
    (-1 : CyclotomicUnitDelta p) ∈
      (cyclotomicUnitFreePartModPDeltaActionZMod (p := p) K).ker := by
  rw [MonoidHom.mem_ker]
  ext x
  rw [cyclotomicUnitFreePartModPDeltaActionZMod_apply]
  exact cyclotomicUnitFreePartModPLinearEquiv_neg_one_apply
    (p := p) (K := K) hp_gt_two x

/-- The reduced free-quotient action factors through `Delta / {±1}` as a
`ZMod p`-linear representation. -/
noncomputable def cyclotomicUnitFreePartModPEvenDeltaActionZMod
    (hp_gt_two : 2 < p) :
    CyclotomicEvenDelta p →*
      (CyclotomicUnitFreePartModP (p := p) K ≃ₗ[ZMod p]
        CyclotomicUnitFreePartModP (p := p) K) :=
  QuotientGroup.lift
    (CyclotomicEvenDeltaSubgroup p)
    (cyclotomicUnitFreePartModPDeltaActionZMod (p := p) K)
    (by
      exact Subgroup.zpowers_le_of_mem <| cyclotomicUnitFreePartModPDeltaActionZMod_neg_one_mem_ker
        (p := p) (K := K) hp_gt_two)

@[simp]
theorem cyclotomicUnitFreePartModPEvenDeltaActionZMod_apply_quotient
    (hp_gt_two : 2 < p) (a : CyclotomicUnitDelta p)
    (x : CyclotomicUnitFreePartModP (p := p) K) :
    cyclotomicUnitFreePartModPEvenDeltaActionZMod (p := p) K hp_gt_two
        (cyclotomicEvenDeltaQuotient p a) x =
      cyclotomicUnitFreePartModPLinearEquiv (p := p) K a x :=
  QuotientGroup.lift_mk' (CyclotomicEvenDeltaSubgroup p)
    (by
      exact Subgroup.zpowers_le_of_mem <| cyclotomicUnitFreePartModPDeltaActionZMod_neg_one_mem_ker
        (p := p) (K := K) hp_gt_two)
    a ▸ cyclotomicUnitFreePartModPDeltaActionZMod_apply (p := p) (K := K) a x

theorem cyclotomicUnitFreePartModPEvenDeltaActionZMod_trace
  [IsZLattice ℝ (NumberField.Units.unitLattice K)]
    (hp_gt_two : 2 < p) (a : CyclotomicEvenDelta p) :
    LinearMap.trace (ZMod p) (CyclotomicUnitFreePartModP (p := p) K)
        ((cyclotomicUnitFreePartModPEvenDeltaActionZMod
          (p := p) K hp_gt_two a).toLinearMap) =
      if a = 1 then (NumberField.Units.rank K : ZMod p) else -1 := by
  refine QuotientGroup.induction_on a ?_
  intro b
  have hlin :
      (cyclotomicUnitFreePartModPEvenDeltaActionZMod (p := p) K hp_gt_two
          (b : CyclotomicEvenDelta p)).toLinearMap =
        (cyclotomicUnitFreePartModPLinearEquivZMod (p := p) K b).toLinearMap := by
    apply LinearMap.ext
    intro x
    exact cyclotomicUnitFreePartModPEvenDeltaActionZMod_apply_quotient
      (p := p) (K := K) hp_gt_two b x
  rw [hlin, cyclotomicUnitFreePartModPLinearEquiv_trace_formula
    (p := p) (K := K) hp_gt_two b]
  change (if (b : CyclotomicEvenDelta p) = 1 then
      (NumberField.Units.rank K : ZMod p) else -1) =
    if (b : CyclotomicEvenDelta p) = 1 then
      (NumberField.Units.rank K : ZMod p) else -1
  rfl

/-- The factored reduced free-quotient action, packaged as a standard
`ZMod p`-linear representation of `Delta / {±1}`. -/
noncomputable def cyclotomicUnitFreePartModPEvenRepresentation
    (hp_gt_two : 2 < p) :
    Representation (ZMod p) (CyclotomicEvenDelta p)
      (CyclotomicUnitFreePartModP (p := p) K) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (cyclotomicUnitFreePartModPEvenDeltaActionZMod (p := p) K hp_gt_two)

@[simp]
theorem cyclotomicUnitFreePartModPEvenRepresentation_apply
    (hp_gt_two : 2 < p) (a : CyclotomicEvenDelta p)
    (x : CyclotomicUnitFreePartModP (p := p) K) :
    cyclotomicUnitFreePartModPEvenRepresentation (p := p) K hp_gt_two a x =
      cyclotomicUnitFreePartModPEvenDeltaActionZMod (p := p) K hp_gt_two a x :=
  rfl

/-- The character idempotent projector attached to an even character, acting
on the reduced free quotient. -/
noncomputable def cyclotomicUnitFreePartModPEvenCharacterProjector
    (hp_gt_two : 2 < p) (χ : MulChar (CyclotomicEvenDelta p) (ZMod p)) :
    Module.End (ZMod p) (CyclotomicUnitFreePartModP (p := p) K) := by
  classical
  letI : Invertible (Fintype.card (CyclotomicEvenDelta p) : ZMod p) :=
    cyclotomicEvenDeltaCardInvertibleZMod (p := p) hp_gt_two
  exact (cyclotomicUnitFreePartModPEvenRepresentation (p := p) K hp_gt_two).asAlgebraHom
    (charIdempotent (G := CyclotomicEvenDelta p) (R := ZMod p) χ)

theorem cyclotomicUnitFreePartModPEvenCharacterProjector_trace_of_ne_one
  [IsZLattice ℝ (NumberField.Units.unitLattice K)]
    (hp_gt_two : 2 < p)
    {χ : MulChar (CyclotomicEvenDelta p) (ZMod p)} (hχ : χ ≠ 1) :
    LinearMap.trace (ZMod p) (CyclotomicUnitFreePartModP (p := p) K)
        (cyclotomicUnitFreePartModPEvenCharacterProjector
          (p := p) K hp_gt_two χ) = 1 := by
  classical
  letI : Invertible (Fintype.card (CyclotomicEvenDelta p) : ZMod p) :=
    cyclotomicEvenDeltaCardInvertibleZMod (p := p) hp_gt_two
  let ρ := cyclotomicUnitFreePartModPEvenRepresentation (p := p) K hp_gt_two
  suffices
      (Fintype.card (CyclotomicEvenDelta p) : ZMod p)⁻¹ *
          ∑ x : CyclotomicEvenDelta p,
            χ x *
              LinearMap.trace (ZMod p) (CyclotomicUnitFreePartModP (p := p) K)
                ((cyclotomicUnitFreePartModPEvenRepresentation
                  (p := p) K hp_gt_two) x⁻¹) = 1 by
    simpa [cyclotomicUnitFreePartModPEvenCharacterProjector, charIdempotent_def] using this
  have htrace : ∀ x : CyclotomicEvenDelta p,
      LinearMap.trace (ZMod p) (CyclotomicUnitFreePartModP (p := p) K)
          ((cyclotomicUnitFreePartModPEvenRepresentation (p := p) K hp_gt_two) x⁻¹) =
        if x = 1 then (NumberField.Units.rank K : ZMod p) else -1 := by
    intro x
    change LinearMap.trace (ZMod p) (CyclotomicUnitFreePartModP (p := p) K)
        ((cyclotomicUnitFreePartModPEvenDeltaActionZMod
          (p := p) K hp_gt_two x⁻¹).toLinearMap) =
      if x = 1 then (NumberField.Units.rank K : ZMod p) else -1
    rw [cyclotomicUnitFreePartModPEvenDeltaActionZMod_trace
      (p := p) (K := K) hp_gt_two x⁻¹]
    by_cases hx : x = 1
    · simp [hx]
    · have hxinv : x⁻¹ ≠ 1 := fun h =>
        hx (inv_eq_one.mp h)
      rw [if_neg hxinv, if_neg hx]
  simp_rw [htrace]
  have hsumχ : ∑ x : CyclotomicEvenDelta p, χ x = 0 :=
    MulChar.sum_eq_zero_of_ne_one (χ := χ) hχ
  have hsum :
      ∑ x : CyclotomicEvenDelta p,
          χ x * (if x = 1 then (NumberField.Units.rank K : ZMod p) else -1) =
        (NumberField.Units.rank K : ZMod p) + 1 := by
    let r : ZMod p := NumberField.Units.rank K
    calc
      ∑ x : CyclotomicEvenDelta p, χ x * (if x = 1 then r else -1)
          = ∑ x : CyclotomicEvenDelta p,
              (χ x * (-1) + if x = 1 then χ x * (r + 1) else 0) := by
              apply Finset.sum_congr rfl
              intro x _
              by_cases hx : x = 1
              · simp [hx, r]
              · simp [hx]
      _ = (∑ x : CyclotomicEvenDelta p, χ x * (-1)) +
            ∑ x : CyclotomicEvenDelta p,
              (if x = 1 then χ x * (r + 1) else 0) := by
              rw [Finset.sum_add_distrib]
      _ = 0 + (r + 1) := by
              rw [← Finset.sum_mul, hsumχ, zero_mul]
              rw [Finset.sum_ite_eq']
              simp [r]
      _ = (NumberField.Units.rank K : ZMod p) + 1 := by
              simp [r]
  rw [hsum, cyclotomicUnitFreePart_rank_add_one_eq_evenDelta_card_zmod
    (p := p) (K := K) hp_gt_two]
  simp


end BernoulliRegular

end

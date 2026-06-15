module

public import BernoulliRegular.UnitQuotient.ModPReduction
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.RingTheory.ZMod.Torsion

/-!
# Unit quotients: the free character profile

This file records the representation-theoretic closing statement for the free
unit contribution.  The permutation representation of
`Delta / {±1}` contains one copy of every quotient character.  The free unit
part corresponds to the augmentation subrepresentation, so the trivial line is
removed and each nontrivial quotient character occurs with multiplicity one.

The comparison between the actual Dirichlet unit lattice and this augmentation
representation is the remaining number-theoretic input needed to turn this
abstract profile into the final `E/E^p` component statement.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

attribute [local instance] Fintype.ofFinite

variable (p : ℕ) [Fact p.Prime]

/-- The summation map on functions on `Delta / {±1}`.  Its kernel is the
augmentation subrepresentation. -/
def evenDeltaAugmentationMap (R : Type*) [Semiring R] :
    (CyclotomicEvenDelta p → R) →ₗ[R] R where
  toFun f := ∑ x : CyclotomicEvenDelta p, f x
  map_add' f g := by
    simp [Finset.sum_add_distrib]
  map_smul' c f := by
    simp [Finset.mul_sum]

/-- The augmentation subrepresentation of the regular permutation
representation of `Delta / {±1}`. -/
def evenDeltaAugmentationSubmodule (R : Type*) [Semiring R] :
    Submodule R (CyclotomicEvenDelta p → R) :=
  LinearMap.ker (evenDeltaAugmentationMap (p := p) R)

/-- The `χ`-eigenspace inside the augmentation subrepresentation. -/
def evenDeltaAugmentationCharacterEigenspace {R : Type*} [CommSemiring R]
    (χ : MulChar (CyclotomicEvenDelta p) R) :
    Submodule R (CyclotomicEvenDelta p → R) :=
  evenDeltaRegularCharacterEigenspace (p := p) χ ⊓
    evenDeltaAugmentationSubmodule (p := p) R

theorem evenDeltaRegularCharacterFunction_sum_of_ne_one {R : Type*}
    [Field R] (χ : MulChar (CyclotomicEvenDelta p) R) (hχ : χ ≠ 1) :
    ∑ x : CyclotomicEvenDelta p,
        evenDeltaRegularCharacterFunction (p := p) χ x = 0 := by
  simp only [evenDeltaRegularCharacterFunction]
  let invEquiv : CyclotomicEvenDelta p ≃ CyclotomicEvenDelta p := {
    toFun x := x⁻¹
    invFun x := x⁻¹
    left_inv x := inv_inv x
    right_inv x := inv_inv x
  }
  change ∑ x : CyclotomicEvenDelta p, χ (invEquiv x) = 0
  rw [Equiv.sum_comp invEquiv (fun x => χ x)]
  exact MulChar.sum_eq_zero_of_ne_one (χ := χ) hχ

theorem evenDeltaRegularCharacterFunction_mem_augmentation_of_ne_one {R : Type*}
    [Field R] (χ : MulChar (CyclotomicEvenDelta p) R) (hχ : χ ≠ 1) :
    evenDeltaRegularCharacterFunction (p := p) χ ∈
      evenDeltaAugmentationSubmodule (p := p) R := by
  rw [evenDeltaAugmentationSubmodule, LinearMap.mem_ker]
  exact evenDeltaRegularCharacterFunction_sum_of_ne_one (p := p) χ hχ

/-- Every nontrivial character eigenspace of the regular representation lies
inside the augmentation subrepresentation. -/
theorem evenDeltaRegularCharacterEigenspace_le_augmentation_of_ne_one {R : Type*}
    [Field R] (χ : MulChar (CyclotomicEvenDelta p) R) (hχ : χ ≠ 1) :
    evenDeltaRegularCharacterEigenspace (p := p) χ ≤
      evenDeltaAugmentationSubmodule (p := p) R := by
  rw [evenDeltaRegularCharacterEigenspace_eq_span (p := p) χ]
  exact Submodule.span_le.mpr (by
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    rw [hf]
    exact evenDeltaRegularCharacterFunction_mem_augmentation_of_ne_one
      (p := p) χ hχ)

/-- On a nontrivial character, passing from the regular representation to the
augmentation representation does not change the eigenspace. -/
theorem evenDeltaAugmentationCharacterEigenspace_eq_regular_of_ne_one {R : Type*}
    [Field R] (χ : MulChar (CyclotomicEvenDelta p) R) (hχ : χ ≠ 1) :
    evenDeltaAugmentationCharacterEigenspace (p := p) χ =
      evenDeltaRegularCharacterEigenspace (p := p) χ :=
  le_antisymm inf_le_left
    (le_inf le_rfl
      (evenDeltaRegularCharacterEigenspace_le_augmentation_of_ne_one
        (p := p) χ hχ))

/-- Each nontrivial quotient character occurs with multiplicity one in the
augmentation representation of `Delta / {±1}`. -/
theorem evenDeltaAugmentationCharacterEigenspace_finrank_of_ne_one {R : Type*}
    [Field R] (χ : MulChar (CyclotomicEvenDelta p) R) (hχ : χ ≠ 1) :
    Module.finrank R (evenDeltaAugmentationCharacterEigenspace (p := p) χ) = 1 := by
  rw [evenDeltaAugmentationCharacterEigenspace_eq_regular_of_ne_one (p := p) χ hχ]
  exact evenDeltaRegularCharacterEigenspace_finrank (p := p) χ

/-- The quotient `Delta / {±1}` is cyclic because it is a quotient of the
cyclic group `Delta = (ZMod p)^*`. -/
theorem cyclotomicEvenDelta_isCyclic : IsCyclic (CyclotomicEvenDelta p) := by
  letI : IsCyclic (CyclotomicUnitDelta p) := by
    dsimp [CyclotomicUnitDelta]
    exact ZMod.isCyclic_units_prime (Fact.out : p.Prime)
  exact isCyclic_of_surjective
    (cyclotomicEvenDeltaQuotient p)
    (QuotientGroup.mk'_surjective (CyclotomicEvenDeltaSubgroup p))

/-- A fixed choice of generator of `Delta / {±1}`. -/
noncomputable def cyclotomicEvenDeltaGenerator : CyclotomicEvenDelta p := by
  classical
  letI := cyclotomicEvenDelta_isCyclic (p := p)
  exact Classical.choose (IsCyclic.exists_monoid_generator (α := CyclotomicEvenDelta p))

/-- The chosen generator generates `Delta / {±1}` by nonnegative powers. -/
theorem cyclotomicEvenDeltaGenerator_spec (x : CyclotomicEvenDelta p) :
    x ∈ Submonoid.powers (cyclotomicEvenDeltaGenerator p) := by
  classical
  letI := cyclotomicEvenDelta_isCyclic (p := p)
  exact Classical.choose_spec
    (IsCyclic.exists_monoid_generator (α := CyclotomicEvenDelta p)) x

/-- The chosen generator has order equal to the cardinality of
`Delta / {±1}`. -/
theorem cyclotomicEvenDeltaGenerator_order :
    orderOf (cyclotomicEvenDeltaGenerator p) = Fintype.card (CyclotomicEvenDelta p) := by
  rw [← Nat.card_eq_fintype_card]
  exact orderOf_eq_card_of_forall_mem_powers
    (cyclotomicEvenDeltaGenerator_spec (p := p))

/-- A character of `Delta / {±1}` is determined by its value on the chosen
generator. -/
theorem evenDeltaCharacter_eq_of_apply_generator_eq {R : Type*}
    [CommMonoidWithZero R]
    {χ ψ : MulChar (CyclotomicEvenDelta p) R}
    (hχψ : χ (cyclotomicEvenDeltaGenerator p) = ψ (cyclotomicEvenDeltaGenerator p)) :
    χ = ψ := by
  apply MulChar.ext'
  intro x
  obtain ⟨n, rfl⟩ :=
    (Submonoid.mem_powers_iff x (cyclotomicEvenDeltaGenerator p)).mp
      (cyclotomicEvenDeltaGenerator_spec (p := p) x)
  rw [map_pow, map_pow, hχψ]

/-- If a character is trivial on the chosen generator, then it is the trivial
character. -/
theorem evenDeltaCharacter_eq_one_of_apply_generator_eq_one {R : Type*}
    [CommMonoidWithZero R]
    {χ : MulChar (CyclotomicEvenDelta p) R}
    (hχ : χ (cyclotomicEvenDeltaGenerator p) = 1) :
    χ = 1 := by
  have hone : (1 : MulChar (CyclotomicEvenDelta p) R)
      (cyclotomicEvenDeltaGenerator p) = 1 :=
    MulChar.one_apply (Group.isUnit (cyclotomicEvenDeltaGenerator p))
  exact evenDeltaCharacter_eq_of_apply_generator_eq (p := p)
    (ψ := (1 : MulChar (CyclotomicEvenDelta p) R)) (hχ.trans hone.symm)

/-- A nontrivial character has nontrivial value on the chosen generator. -/
theorem evenDeltaCharacter_ne_one_iff_apply_generator_ne_one {R : Type*}
    [CommMonoidWithZero R]
    {χ : MulChar (CyclotomicEvenDelta p) R} :
    χ ≠ 1 ↔ χ (cyclotomicEvenDeltaGenerator p) ≠ 1 := by
  constructor
  · intro hχ hgen
    exact hχ (evenDeltaCharacter_eq_one_of_apply_generator_eq_one (p := p) hgen)
  · intro hgen hχ
    apply hgen
    simpa [hχ] using
      (MulChar.one_apply (R := CyclotomicEvenDelta p) (R' := R)
        (x := cyclotomicEvenDeltaGenerator p)
        (Group.isUnit (cyclotomicEvenDeltaGenerator p)))

/-- For `p > 2`, the subgroup `{±1}` of `Delta = (ZMod p)^*` has order two. -/
theorem cyclotomicEvenDeltaSubgroup_card (hp_gt_two : 2 < p) :
    Fintype.card (CyclotomicEvenDeltaSubgroup p) = 2 := by
  change Fintype.card (Subgroup.zpowers (-1 : CyclotomicUnitDelta p)) = 2
  rw [Fintype.card_zpowers]
  have hp_ne_two : p ≠ 2 := by omega
  rw [← orderOf_units, Units.coe_neg_one, orderOf_neg_one, ringChar.eq (ZMod p) p,
    if_neg hp_ne_two]

/-- For `p > 2`, the quotient `Delta / {±1}` has order `(p - 1) / 2`. -/
theorem cyclotomicEvenDelta_card (hp_gt_two : 2 < p) :
    Fintype.card (CyclotomicEvenDelta p) = (p - 1) / 2 := by
  have hcard :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CyclotomicEvenDeltaSubgroup p)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    show Fintype.card (CyclotomicUnitDelta p) = p - 1 by rw [ZMod.card_units],
    cyclotomicEvenDeltaSubgroup_card (p := p) hp_gt_two] at hcard
  have hmul : 2 * Fintype.card (CyclotomicEvenDelta p) = p - 1 := by
    rw [mul_comm]
    exact hcard.symm
  exact Nat.eq_div_of_mul_eq_right (by decide) hmul

/-- The order of `Delta / {±1}` divides `p - 1`. -/
theorem cyclotomicEvenDelta_card_dvd_p_sub_one :
    Fintype.card (CyclotomicEvenDelta p) ∣ p - 1 := by
  have hcard :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CyclotomicEvenDeltaSubgroup p)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    show Fintype.card (CyclotomicUnitDelta p) = p - 1 by rw [ZMod.card_units]] at hcard
  exact ⟨Fintype.card (CyclotomicEvenDeltaSubgroup p), hcard⟩

/-- For `p > 2`, `p` does not divide the order of `Delta / {±1}`. -/
theorem cyclotomicEvenDelta_card_not_dvd_p (hp_gt_two : 2 < p) :
    ¬ p ∣ Fintype.card (CyclotomicEvenDelta p) := by
  have hlt : Fintype.card (CyclotomicEvenDelta p) < p := by
    rw [cyclotomicEvenDelta_card (p := p) hp_gt_two]
    omega
  intro hdiv
  exact not_le_of_gt hlt (Nat.le_of_dvd (Fintype.card_pos) hdiv)

/-- For `p > 2`, the order of `Delta / {±1}` is invertible in `ZMod p`. -/
@[implicit_reducible]
noncomputable def cyclotomicEvenDeltaCardInvertibleZMod (hp_gt_two : 2 < p) :
    Invertible (Fintype.card (CyclotomicEvenDelta p) : ZMod p) :=
  invertibleOfCoprime (R := ZMod p)
    (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (cyclotomicEvenDelta_card_not_dvd_p (p := p) hp_gt_two)).symm)

/-- For `p > 2`, `2` is invertible in `ZMod p`. -/
@[implicit_reducible]
noncomputable def twoInvertibleZModOfPrimeGtTwo (hp_gt_two : 2 < p) :
    Invertible (2 : ZMod p) := by
  have hp_not_dvd_two : ¬ p ∣ 2 := fun hdiv =>
    not_le_of_gt hp_gt_two (Nat.le_of_dvd (by decide) hdiv)
  exact invertibleOfCoprime (R := ZMod p)
    (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp_not_dvd_two).symm)

/-- `ZMod p` contains enough roots of unity for the quotient `Delta / {±1}`. -/
theorem cyclotomicEvenDelta_hasEnoughRootsOfUnity_zmod :
    HasEnoughRootsOfUnity (ZMod p) (Monoid.exponent (CyclotomicEvenDelta p)) := by
  haveI : NeZero (p - 1) := ⟨by have := (Fact.out : p.Prime).two_le; omega⟩
  exact HasEnoughRootsOfUnity.of_dvd (ZMod p)
    ((Group.exponent_dvd_card (G := CyclotomicEvenDelta p)).trans
      (cyclotomicEvenDelta_card_dvd_p_sub_one (p := p)))

/-- The `ZMod p`-valued character group of `Delta / {±1}` has the same order
as `Delta / {±1}`. -/
theorem evenDeltaCharacter_card_eq (hp_gt_two : 2 < p) :
    Fintype.card (MulChar (CyclotomicEvenDelta p) (ZMod p)) =
      (p - 1) / 2 := by
  classical
  have hroot : HasEnoughRootsOfUnity (ZMod p)
      (Monoid.exponent (CyclotomicEvenDelta p)) :=
    cyclotomicEvenDelta_hasEnoughRootsOfUnity_zmod (p := p)
  haveI : HasEnoughRootsOfUnity (ZMod p)
      (Monoid.exponent (CyclotomicEvenDelta p)ˣ) := by
    rw [Monoid.exponent_eq_of_mulEquiv (toUnits (G := CyclotomicEvenDelta p)).symm]
    exact hroot
  have hcard_chars :
      Nat.card (MulChar (CyclotomicEvenDelta p) (ZMod p)) =
        Nat.card (CyclotomicEvenDelta p) :=
    (MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity
        (CyclotomicEvenDelta p) (ZMod p)).trans
      (Nat.card_congr (toUnits (G := CyclotomicEvenDelta p)).symm.toEquiv)
  rw [← Nat.card_eq_fintype_card, hcard_chars, Nat.card_eq_fintype_card,
    cyclotomicEvenDelta_card (p := p) hp_gt_two]

open Classical in
/-- For `p > 2`, there are `(p - 3) / 2` nontrivial `ZMod p`-valued
characters of `Delta / {±1}`. -/
theorem evenDeltaNontrivialCharacter_card_eq (hp_gt_two : 2 < p) :
    ((Finset.univ : Finset (MulChar (CyclotomicEvenDelta p) (ZMod p))).filter
        (fun χ => χ ≠ 1)).card = (p - 3) / 2 := by
  classical
  have hfilter :
      ((Finset.univ : Finset (MulChar (CyclotomicEvenDelta p) (ZMod p))).filter
        (fun χ => χ ≠ 1)) =
        (Finset.univ : Finset (MulChar (CyclotomicEvenDelta p) (ZMod p))).erase 1 := by
    ext χ
    by_cases hχ : χ = 1 <;> simp [hχ]
  rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ,
    evenDeltaCharacter_card_eq (p := p) hp_gt_two]
  have hp_odd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨k, hk⟩ := hp_odd
  omega

/-- The expected free-unit contribution function on `Delta`-characters:
one for nontrivial even characters, zero otherwise. -/
def expectedFreeUnitContribution {R : Type*} [CommMonoidWithZero R]
    (χ : MulChar (CyclotomicUnitDelta p) R) : ℕ :=
  by
    classical
    exact if IsEvenDeltaCharacter (p := p) χ ∧
        χ ≠ (1 : MulChar (CyclotomicUnitDelta p) R) then 1 else 0

@[simp]
theorem expectedFreeUnitContribution_of_even_ne_one {R : Type*}
    [CommMonoidWithZero R] {χ : MulChar (CyclotomicUnitDelta p) R}
    (hχ_even : IsEvenDeltaCharacter (p := p) χ)
    (hχ_ne : χ ≠ (1 : MulChar (CyclotomicUnitDelta p) R)) :
    expectedFreeUnitContribution (p := p) χ = 1 := by
  classical
  simp [expectedFreeUnitContribution, hχ_even, hχ_ne]

@[simp]
theorem expectedFreeUnitContribution_of_not_even {R : Type*}
    [CommMonoidWithZero R] {χ : MulChar (CyclotomicUnitDelta p) R}
    (hχ_even : ¬ IsEvenDeltaCharacter (p := p) χ) :
    expectedFreeUnitContribution (p := p) χ = 0 := by
  classical
  simp [expectedFreeUnitContribution, hχ_even]

@[simp]
theorem expectedFreeUnitContribution_one {R : Type*} [CommMonoidWithZero R] :
    expectedFreeUnitContribution (p := p)
      (1 : MulChar (CyclotomicUnitDelta p) R) = 0 := by
  classical
  simp [expectedFreeUnitContribution]

end BernoulliRegular

end

import BernoulliRegular.CyclotomicUnits.IndexFormula
import BernoulliRegular.CyclotomicUnits.IndexDeterminant
import BernoulliRegular.CyclotomicUnits.NormalizedSubgroup
import BernoulliRegular.HMinus.ClassNumberFormula
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

/-!
# Normalized cyclotomic-unit index theorem

This file transfers the already proved squared-family prime-conductor index
formula to the TeX normalized subgroup `normalizedCPlus`.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

variable {p : ℕ} [Fact p.Prime]
variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

theorem CPlusGenerator_eq_cyclotomicUnitFamilyKplus
    (hp_three : 3 ≤ p) (i : Fin ((p - 3) / 2)) :
    CPlusGenerator (p := p) (K := K) hp_three i =
      FLT37.Sinnott.cyclotomicUnitFamilyKplus p K hp_three i := by
  apply Units.ext
  simp [CPlusGenerator, realCyclotomicUnit, FLT37.Sinnott.cyclotomicUnitFamilyKplus]

theorem cyclotomicUnitFamilyKplus_mem_CPlus
    (hp_three : 3 ≤ p) (i : Fin ((p - 3) / 2)) :
    FLT37.Sinnott.cyclotomicUnitFamilyKplus p K hp_three i ∈
      CPlus (p := p) (K := K) hp_three := by
  rw [← CPlusGenerator_eq_cyclotomicUnitFamilyKplus
    (p := p) (K := K) hp_three i]
  exact CPlusGenerator_mem (p := p) (K := K) hp_three i

theorem range_cyclotomicUnitFamilyKplusFinRank_eq
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    Set.range (FLT37.Sinnott.cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) =
      Set.range (FLT37.Sinnott.cyclotomicUnitFamilyKplus p K hp_three) := by
  classical
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    unfold FLT37.Sinnott.cyclotomicUnitFamilyKplusFinRank
    exact ⟨i.cast ((NumberField.IsCMField.units_rank_eq_units_rank (K := K)).trans
      (units_rank_eq_prime_sub_three_div_two (p := p) (K := K))), rfl⟩
  · rintro ⟨i, rfl⟩
    unfold FLT37.Sinnott.cyclotomicUnitFamilyKplusFinRank
    refine ⟨i.cast (((NumberField.IsCMField.units_rank_eq_units_rank (K := K)).trans
      (units_rank_eq_prime_sub_three_div_two (p := p) (K := K))).symm), ?_⟩
    simp

theorem torsionKplus_le_CPlus (hp_three : 3 ≤ p) :
    NumberField.Units.torsion K⁺ ≤ CPlus (p := p) (K := K) hp_three := by
  intro x hx
  rcases maximalRealSubfield_torsion_eq_one_or_neg_one
      (K := K) ⟨x, hx⟩ with h_one | h_neg
  · have hx_one : x = 1 := by
      simpa using h_one
    rw [hx_one]
    exact Subgroup.one_mem _
  · have hx_neg : x = -1 := by
      simpa using h_neg
    rw [hx_neg]
    exact neg_one_mem_CPlus (p := p) (K := K) hp_three

theorem closure_cyclotomicUnitFamilyKplus_le_CPlus
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    Subgroup.closure
        (Set.range (FLT37.Sinnott.cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ≤
      CPlus (p := p) (K := K) hp_three := by
  rw [Subgroup.closure_le, range_cyclotomicUnitFamilyKplusFinRank_eq
    (p := p) (K := K) hp_odd hp_three]
  rintro x ⟨i, rfl⟩
  exact cyclotomicUnitFamilyKplus_mem_CPlus (p := p) (K := K) hp_three i

theorem CPlus_le_cyclotomicUnitIndexSubgroup
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    CPlus (p := p) (K := K) hp_three ≤
      cyclotomicUnitIndexSubgroup (p := p) (K := K) hp_odd hp_three := by
  unfold CPlus cyclotomicUnitIndexSubgroup
  rw [Subgroup.closure_le]
  rintro x (hx | hx)
  · rcases hx with rfl
    exact Subgroup.mem_sup_right <| neg_one_mem_torsion
  · rcases hx with ⟨i, rfl⟩
    rw [CPlusGenerator_eq_cyclotomicUnitFamilyKplus (p := p) (K := K) hp_three i]
    apply Subgroup.mem_sup_left
    apply Subgroup.subset_closure
    rw [range_cyclotomicUnitFamilyKplusFinRank_eq (p := p) (K := K) hp_odd hp_three]
    exact Set.mem_range_self i

theorem cyclotomicUnitIndexSubgroup_le_CPlus
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    cyclotomicUnitIndexSubgroup (p := p) (K := K) hp_odd hp_three ≤
      CPlus (p := p) (K := K) hp_three := by
  unfold cyclotomicUnitIndexSubgroup
  exact sup_le
    (closure_cyclotomicUnitFamilyKplus_le_CPlus (p := p) (K := K) hp_odd hp_three)
    (torsionKplus_le_CPlus (p := p) (K := K) hp_three)

theorem cyclotomicUnitIndexSubgroup_eq_CPlus
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    cyclotomicUnitIndexSubgroup (p := p) (K := K) hp_odd hp_three =
      CPlus (p := p) (K := K) hp_three :=
  le_antisymm
    (cyclotomicUnitIndexSubgroup_le_CPlus (p := p) (K := K) hp_odd hp_three)
    (CPlus_le_cyclotomicUnitIndexSubgroup (p := p) (K := K) hp_odd hp_three)

set_option maxHeartbeats 20000000 in
-- The composed determinant-to-regulator bridge unfolds large matrix identities
-- from the FLT37 Sinnott pipeline.
set_option backward.isDefEq.respectTransparency false in
open Classical in
theorem kummerDirichletDeterminant_of_deletedFourier
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p) (hp_ge_five : 5 ≤ p) :
    FLT37.Sinnott.KummerDirichletDeterminant p K hp_odd hp_three := by
  have hdetAB :=
    CyclotomicUnits.detASubBSqEqProdNontrivialQeSq_of_deletedFourier
      (p := p) (K := K) hp_odd hp_three hp_two hp_ge_five
  have hreg :=
    FLT37.Sinnott.regOfFamilySqEqProdNontrivialQeSq_of_detASubBSqEqProdQeSq
      (p := p) K hp_odd hp_three hp_two hdetAB
  exact FLT37.Sinnott.KummerDirichletDeterminant_of_regOfFamilySqEqProdNontrivialQeSq
    (p := p) K hp_odd hp_three hp_two hreg

theorem cyclotomicUnitIndex_primeConductor_pPrimary_aux
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p) (hp_ge_five : 5 ≤ p) :
    p ∣ (normalizedCPlus (p := p) (K := K) hp_odd hp_three).index ↔ p ∣ hPlus K := by
  have hdet :=
    kummerDirichletDeterminant_of_deletedFourier
      (p := p) (K := K) hp_odd hp_three hp_two hp_ge_five
  have h_square :=
    cyclotomicUnitIndex_primeConductor_pPrimary_of_kummerDirichletDeterminant
      (p := p) (K := K) hp_odd hp_three hdet
  have h_CPlus :
      p ∣ (CPlus (p := p) (K := K) hp_three).index ↔ p ∣ hPlus K := by
    rw [← cyclotomicUnitIndexSubgroup_eq_CPlus (p := p) (K := K) hp_odd hp_three]
    exact h_square
  exact
    (CPlus_index_prime_dvd_iff_normalizedCPlus_index_prime_dvd
      (p := p) (K := K) hp_odd hp_three).symm.trans h_CPlus

theorem hPlus_eq_one_of_eq_three (hp_odd : p ≠ 2) (hp_eq : p = 3) :
    hPlus K = 1 := by
  subst p
  letI : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.three_pid K
  have h_dvd : hPlus K ∣ h K :=
    hPlus_dvd_h (p := 3) (hp_odd := by norm_num) (K := K)
  have h_one : h K = 1 := by
    have h_class : NumberField.classNumber K = 1 :=
      NumberField.classNumber_eq_one_iff.mpr inferInstance
    simpa [h, NumberField.classNumber] using h_class
  rw [h_one] at h_dvd
  exact Nat.eq_one_of_dvd_one h_dvd

theorem CPlus_eq_top_of_eq_three
    (hp_three : 3 ≤ p) (hp_eq : p = 3) :
    CPlus (p := p) (K := K) hp_three = ⊤ := by
  have h_rank : NumberField.Units.rank K⁺ = 0 := by
    have h_rank_eq :=
      (NumberField.IsCMField.units_rank_eq_units_rank (K := K)).trans
        (units_rank_eq_prime_sub_three_div_two (p := p) (K := K))
    simpa [hp_eq] using h_rank_eq
  apply le_antisymm le_top
  rw [← NumberField.Units.closure_fundSystem_sup_torsion_eq_top (K := K⁺)]
  refine sup_le ?_ (torsionKplus_le_CPlus (p := p) (K := K) hp_three)
  rw [Subgroup.closure_le]
  rintro x ⟨i, rfl⟩
  have hi : (i : ℕ) < 0 := by
    simpa [h_rank] using i.isLt
  omega

theorem normalizedCPlus_eq_top_of_eq_three
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_eq : p = 3) :
    normalizedCPlus (p := p) (K := K) hp_odd hp_three = ⊤ := by
  apply le_antisymm le_top
  have hle := CPlus_le_normalizedCPlus (p := p) (K := K) hp_odd hp_three
  simpa [CPlus_eq_top_of_eq_three (p := p) (K := K) hp_three hp_eq] using hle

theorem cyclotomicUnitIndex_primeConductor_pPrimary_of_eq_three
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_eq : p = 3) :
    p ∣ (normalizedCPlus (p := p) (K := K) hp_odd hp_three).index ↔ p ∣ hPlus K := by
  have h_index :
      (normalizedCPlus (p := p) (K := K) hp_odd hp_three).index = 1 := by
    rw [normalizedCPlus_eq_top_of_eq_three (p := p) (K := K) hp_odd hp_three hp_eq]
    exact Subgroup.index_top
  have h_hPlus : hPlus K = 1 :=
    hPlus_eq_one_of_eq_three (p := p) (K := K) hp_odd hp_eq
  rw [h_index, h_hPlus]

theorem cyclotomicUnitIndex_primeConductor_pPrimary_of_five_le (hp_ge_five : 5 ≤ p) :
    p ∣ (normalizedCPlus (p := p) (K := K)
        (by omega : p ≠ 2) (by omega : 3 ≤ p)).index ↔
      p ∣ hPlus K :=
  cyclotomicUnitIndex_primeConductor_pPrimary_aux
    (p := p) (K := K) (by omega) (by omega) (by omega) hp_ge_five

/-- CU-06: the prime-conductor cyclotomic-unit index theorem for the TeX
normalized subgroup `C⁺ = <-1, ε₂, ..., ε_g>`, in odd-primary form. -/
theorem cyclotomicUnitIndex_primeConductor_pPrimary (hp_odd : p ≠ 2) :
    p ∣ (normalizedCPlus (p := p) (K := K) hp_odd
        (by have hp_two := (Fact.out : Nat.Prime p).two_le; omega)).index ↔
      p ∣ hPlus K := by
  by_cases hp_eq : p = 3
  · exact cyclotomicUnitIndex_primeConductor_pPrimary_of_eq_three
      (p := p) (K := K) hp_odd
      (by have hp_two := (Fact.out : Nat.Prime p).two_le; omega) hp_eq
  · have hp_ge_five : 5 ≤ p := by
      obtain ⟨k, hk⟩ := (Fact.out : Nat.Prime p).odd_of_ne_two hp_odd
      have hp_two := (Fact.out : Nat.Prime p).two_le
      omega
    exact cyclotomicUnitIndex_primeConductor_pPrimary_of_five_le
      (p := p) (K := K) hp_ge_five

/-- **PF-1: Kummer-Dirichlet determinant identity** for p ≥ 5.

Discharges `KummerDirichletDeterminant p K hp_odd hp_three` for any
cyclotomic K of conductor an odd prime p ≥ 5, by composing the
shipped pieces:
* `detASubBSqEqProdNontrivialQeSq_of_deletedFourier` (algebraic side),
* `regOfFamilySqEqProdNontrivialQeSq_of_detASubBSqEqProdQeSq`,
* `KummerDirichletDeterminant_of_regOfFamilySqEqProdNontrivialQeSq`.

The p = 3 case is empty-family trivial (rank (p-3)/2 = 0). -/
theorem kummerDirichletDeterminant_of_cyclotomic_of_five_le
    (hp_ge_five : 5 ≤ p) :
    FLT37.Sinnott.KummerDirichletDeterminant p K
      (by omega : p ≠ 2) (by omega : 3 ≤ p) :=
  kummerDirichletDeterminant_of_deletedFourier
    (p := p) (K := K) (by omega) (by omega) (by omega) hp_ge_five

end BernoulliRegular

end

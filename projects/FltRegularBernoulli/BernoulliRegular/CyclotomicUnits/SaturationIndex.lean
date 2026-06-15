import BernoulliRegular.CyclotomicUnits.NormalizedIndex
import BernoulliRegular.CyclotomicUnits.Saturation
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# From p-saturation to p-index nondivisibility

This file records the finite-index group-theoretic step used after the
cyclotomic-unit saturation theorem.  If a finite-index subgroup contains all
`p`-torsion and is `p`-saturated in the ambient group, then `p` cannot divide
its index.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

variable {p : ℕ} [Fact p.Prime]

/-- A finite-index subgroup of a commutative group has p-prime-to index if it
is p-saturated in the whole group and contains every element killed by `p`.

The proof is Cauchy's theorem on `G / H`: a p-divisor of the index gives a
nontrivial quotient class with p-th power one.  Saturation lifts the p-th
power equality into `H`, and the torsion hypothesis forces the representative
itself back into `H`, contradiction. -/
theorem subgroup_not_dvd_index_of_pSaturated_top_of_pow_eq_one_mem
    {G : Type*} [CommGroup G] {H : Subgroup G} [H.FiniteIndex]
    (hsat : pSaturated H (⊤ : Subgroup G) p)
    (htorsion : ∀ g : G, g ^ p = 1 → g ∈ H) :
    ¬ p ∣ H.index := by
  classical
  intro hdiv
  have hcard : p ∣ Nat.card (G ⧸ H) := by
    simpa [Subgroup.index_eq_card] using hdiv
  obtain ⟨q, hq_order⟩ := exists_prime_orderOf_dvd_card' (G := G ⧸ H) p hcard
  have hq_pow : q ^ p = 1 := by
    rw [← hq_order]
    exact pow_orderOf_eq_one q
  revert hq_order hq_pow
  refine QuotientGroup.induction_on q ?_
  intro g hq_order hq_pow
  have hgpowH : g ^ p ∈ H :=
    (QuotientGroup.eq_one_iff (N := H) (g ^ p)).mp (by simpa using hq_pow)
  have hgpowTop : g ^ p ∈ pPowerSubgroup (⊤ : Subgroup G) p :=
    ⟨g, Subgroup.mem_top g, rfl⟩
  rcases pSaturated.mem_pPowerSubgroup_of_mem hsat hgpowH hgpowTop with
    ⟨h, hhH, hhp⟩
  have hgh_pow : (g * h⁻¹) ^ p = 1 := by
    simp [mul_pow, hhp]
  have hghH : g * h⁻¹ ∈ H := htorsion (g * h⁻¹) hgh_pow
  have hgH : g ∈ H := by
    simpa [mul_assoc] using H.mul_mem hghH hhH
  have hquot_one : ((g : G) : G ⧸ H) = 1 :=
    (QuotientGroup.eq_one_iff (N := H) g).mpr hgH
  have hp_one : p = 1 := by
    rw [← hq_order]
    simp [hquot_one]
  exact (Fact.out : Nat.Prime p).ne_one hp_one

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The real cyclotomic-unit subgroup has finite index in the full plus-side
unit group for prime conductor. -/
theorem CPlus_index_ne_zero (hp_three : 3 ≤ p) :
    (CPlus (p := p) (K := K) hp_three).index ≠ 0 := by
  classical
  by_cases hp_eq_three : p = 3
  · rw [CPlus_eq_top_of_eq_three (p := p) (K := K) hp_three hp_eq_three]
    simp
  · have hp_ne_four : p ≠ 4 := by
      intro hp_four
      have hprime_four : Nat.Prime 4 := hp_four ▸ (Fact.out : Nat.Prime p)
      norm_num at hprime_four
    have hp_five : 5 ≤ p := by omega
    have hp_odd : p ≠ 2 := by omega
    have hp_two : 2 < p := by omega
    have hdet :
        FLT37.Sinnott.KummerDirichletDeterminant p K hp_odd hp_three :=
      kummerDirichletDeterminant_of_deletedFourier
        (p := p) (K := K) hp_odd hp_three hp_two hp_five
    have hreg : FLT37.Sinnott.SinnottRegulatorIdentity p K hp_odd hp_three :=
      (FLT37.Sinnott.sinnottRegulatorIdentity_iff_kummerDirichletDeterminant
        (p := p) (K := K) hp_odd hp_three).1 hdet
    have hsinnott : FLT37.Sinnott.SinnottIndexFormula p K hp_odd hp_three :=
      FLT37.Sinnott.sinnottIndexFormula_of_regulatorIdentity
        p K hp_odd hp_three hreg
    have hindex :=
      FLT37.Sinnott.index_eq_twoPow_mul_hPlus_of_sinnottIndexFormula
        p K hp_odd hp_three hsinnott
    change (cyclotomicUnitIndexSubgroup (p := p) (K := K) hp_odd hp_three).index =
      2 ^ ((p - 3) / 2) * hPlus K at hindex
    rw [cyclotomicUnitIndexSubgroup_eq_CPlus (p := p) (K := K) hp_odd hp_three] at hindex
    rw [hindex]
    exact (Nat.mul_pos (pow_pos (by norm_num : 0 < 2) _)
      (Nat.pos_of_ne_zero Fintype.card_ne_zero)).ne'

/-- CU-15: p-saturation of the cyclotomic units in the full plus-side unit
group forces p not to divide the cyclotomic-unit index. -/
theorem not_dvd_index_of_pSaturated (hp_three : 3 ≤ p)
    (hsat : pSaturated (CPlus (p := p) (K := K) hp_three) (EPlus (K := K)) p) :
    ¬ p ∣ (CPlus (p := p) (K := K) hp_three).index := by
  classical
  let H : Subgroup (𝓞 K⁺)ˣ := CPlus (p := p) (K := K) hp_three
  haveI : H.FiniteIndex := ⟨by
    simpa [H] using CPlus_index_ne_zero (p := p) (K := K) hp_three⟩
  have hsatTop : pSaturated H (⊤ : Subgroup (𝓞 K⁺)ˣ) p := by
    simpa [H, EPlus] using hsat
  have htorsion : ∀ g : (𝓞 K⁺)ˣ, g ^ p = 1 → g ∈ H := by
    intro g hg
    have hg_torsion : g ∈ NumberField.Units.torsion K⁺ := by
      change g ∈ CommGroup.torsion (𝓞 K⁺)ˣ
      exact (CommGroup.mem_torsion g).mpr
        (isOfFinOrder_iff_pow_eq_one.mpr ⟨p, (Fact.out : Nat.Prime p).pos, hg⟩)
    simpa [H] using
      torsionKplus_le_CPlus (p := p) (K := K) hp_three hg_torsion
  exact subgroup_not_dvd_index_of_pSaturated_top_of_pow_eq_one_mem
    (p := p) (H := H) hsatTop htorsion

end BernoulliRegular

end

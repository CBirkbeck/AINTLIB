import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.IndexFormula
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.CyclotomicUnitFamily

/-!
# Pollaczek descent to the family subgroup

This file builds the K⁺-side family product whose image is `pollaczekUnitPlus`
and packages it as the `PollaczekInFamily` input to the Corollary 8.19 bridge.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

set_option backward.isDefEq.respectTransparency false in
/-- The K⁺-side family product whose image is `pollaczekUnitPlus`. -/
noncomputable def pollaczekUnitPlusKplus (i_irreg : ℕ) (hp_odd : p ≠ 2)
    (hp_three : 3 ≤ p) :
    (𝓞 (NumberField.maximalRealSubfield K))ˣ :=
  ∏ j : Fin (NumberField.Units.rank
      (NumberField.maximalRealSubfield K)),
    cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three j ^
      (((j : ℕ) + 2) ^ (p - 1 - i_irreg))

set_option backward.isDefEq.respectTransparency false in
/-- The K⁺-side Pollaczek family product lies in the generated family subgroup. -/
theorem pollaczekUnitPlusKplus_mem_familyClosure (i_irreg : ℕ) (hp_odd : p ≠ 2)
    (hp_three : 3 ≤ p) :
    pollaczekUnitPlusKplus p K i_irreg hp_odd hp_three ∈
      Subgroup.closure
        (Set.range (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) := by
  unfold pollaczekUnitPlusKplus
  apply Subgroup.prod_mem
  intro j _
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self j)) _

set_option backward.isDefEq.respectTransparency false in
/-- The K⁺-side Pollaczek family product lies in the family subgroup enlarged by torsion. -/
theorem pollaczekUnitPlusKplus_mem (i_irreg : ℕ) (hp_odd : p ≠ 2)
    (hp_three : 3 ≤ p) :
    pollaczekUnitPlusKplus p K i_irreg hp_odd hp_three ∈
      Subgroup.closure
        (Set.range (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ⊔
      NumberField.Units.torsion (NumberField.maximalRealSubfield K) :=
  Subgroup.mem_sup_left
    (pollaczekUnitPlusKplus_mem_familyClosure p K i_irreg hp_odd hp_three)

set_option backward.isDefEq.respectTransparency false in
/-- The proposition that the K⁺-side family product maps to `pollaczekUnitPlus`. -/
def AlgebraMapPollaczekUnitPlusKplus_eq (i_irreg : ℕ)
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
      (pollaczekUnitPlusKplus p K i_irreg hp_odd hp_three :
        𝓞 (NumberField.maximalRealSubfield K)) : 𝓞 K) =
    ((FLT37.pollaczekUnitPlus p K i_irreg : (𝓞 K)ˣ) : 𝓞 K)

set_option backward.isDefEq.respectTransparency false in
/-- The algebra-map identity and subgroup membership give `PollaczekInFamily`. -/
theorem pollaczekInFamily_of_algebraMap_eq (i_irreg : ℕ)
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (h : AlgebraMapPollaczekUnitPlusKplus_eq p K i_irreg hp_odd hp_three) :
    PollaczekInFamily p K i_irreg hp_odd hp_three :=
  ⟨pollaczekUnitPlusKplus p K i_irreg hp_odd hp_three, h,
   pollaczekUnitPlusKplus_mem p K i_irreg hp_odd hp_three⟩

set_option backward.isDefEq.respectTransparency false in
/-- Each K⁺ family element maps to the corresponding real cyclotomic unit over K. -/
theorem algebraMap_cyclotomicUnitFamilyKplus
    (j : Fin (NumberField.Units.rank
        (NumberField.maximalRealSubfield K)))
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        ((cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three j :
          (𝓞 (NumberField.maximalRealSubfield K))ˣ) :
          𝓞 (NumberField.maximalRealSubfield K)) =
      FLT37.realCyclotomicUnit p K
        ((j.cast ((NumberField.IsCMField.units_rank_eq_units_rank (K := K)).trans
          (BernoulliRegular.units_rank_eq_prime_sub_three_div_two
            (p := p) (K := K)))) + 2) := by
  unfold cyclotomicUnitFamilyKplusFinRank cyclotomicUnitFamilyKplus
  rw [realCyclotomicUnitPlusUnit_val]
  exact FLT37.algebraMap_realCyclotomicUnitPlus p K _

set_option backward.isDefEq.respectTransparency false in
/-- The value of `pollaczekUnitPlus` is the Pollaczek product of real cyclotomic units. -/
theorem pollaczekUnitPlus_val_eq_prod_realCyclotomicUnit (i : ℕ) :
    ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) =
      ∏ b ∈ (Finset.Ico 1 ((p - 1) / 2 + 1)).attach,
        FLT37.realCyclotomicUnit p K b.1 ^ ((b.1 : ℕ) ^ (p - 1 - i)) := by
  unfold FLT37.pollaczekUnitPlus
  rw [Units.val_mul]
  unfold FLT37.pollaczekUnit
  rw [Units.coe_prod]
  rw [show ((unitsComplexConj K
      (∏ b ∈ (Finset.Ico 1 ((p - 1) / 2 + 1)).attach,
        FLT37.pollaczekFactor p K b.2 ^ ((b.1 : ℕ) ^ (p - 1 - i))) :
        (𝓞 K)ˣ) : 𝓞 K) =
      ringOfIntegersComplexConj K
        ((∏ b ∈ (Finset.Ico 1 ((p - 1) / 2 + 1)).attach,
          FLT37.pollaczekFactor p K b.2 ^ ((b.1 : ℕ) ^ (p - 1 - i))) :
          (𝓞 K)ˣ).val from rfl]
  rw [Units.coe_prod, map_prod]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ ↦ ?_
  rw [Units.val_pow_eq_pow_val, map_pow, ← mul_pow]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- Remove the trivial `b = 1` term from the Pollaczek product. -/
theorem pollaczekUnitPlus_val_eq_prod_Ico_two (i : ℕ) (hp_three : 3 ≤ p) :
    ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) =
      ∏ b ∈ Finset.Ico 2 ((p - 1) / 2 + 1),
        FLT37.realCyclotomicUnit p K b ^ (b ^ (p - 1 - i)) := by
  rw [pollaczekUnitPlus_val_eq_prod_realCyclotomicUnit]
  rw [Finset.prod_attach (Finset.Ico 1 ((p - 1) / 2 + 1))
        (fun b ↦ FLT37.realCyclotomicUnit p K b ^ (b ^ (p - 1 - i)))]
  have h_half : 1 ≤ (p - 1) / 2 := by omega
  have h_split : Finset.Ico 1 ((p - 1) / 2 + 1) =
      insert 1 (Finset.Ico 2 ((p - 1) / 2 + 1)) := by
    ext x
    rw [Finset.mem_insert, Finset.mem_Ico, Finset.mem_Ico]
    omega
  have h_one_not_mem : (1 : ℕ) ∉ Finset.Ico 2 ((p - 1) / 2 + 1) := by
    rw [Finset.mem_Ico]; omega
  rw [h_split, Finset.prod_insert h_one_not_mem]
  rw [FLT37.realCyclotomicUnit_one]
  simp only [one_pow, one_mul]

set_option backward.isDefEq.respectTransparency false in
omit hp in
/-- Reindex a family product over `Fin ((p - 3) / 2)` as a product over `Ico 2`. -/
theorem prod_Fin_eq_prod_Ico_two
    {β : Type*} [CommMonoid β] (hp_three : 3 ≤ p) (f : ℕ → β) :
    ∏ j : Fin ((p - 3) / 2), f ((j : ℕ) + 2) =
      ∏ b ∈ Finset.Ico 2 ((p - 1) / 2 + 1), f b := by
  rw [show ∏ j : Fin ((p - 3) / 2), f ((j : ℕ) + 2) =
        ∏ j ∈ Finset.range ((p - 3) / 2), f (j + 2) from
        (Finset.prod_range fun j ↦ f (j + 2)).symm]
  rw [show Finset.Ico 2 ((p - 1) / 2 + 1) = Finset.Ico (0 + 2) ((p - 3) / 2 + 2) by
        congr 1
        omega]
  rw [Finset.prod_Ico_eq_prod_range]
  simp only [zero_add]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  congr 1
  omega

set_option backward.isDefEq.respectTransparency false in
/-- The K⁺ Pollaczek family product maps to the K-side `pollaczekUnitPlus`. -/
theorem algebraMapPollaczekUnitPlusKplus_eq (i_irreg : ℕ)
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    AlgebraMapPollaczekUnitPlusKplus_eq p K i_irreg hp_odd hp_three := by
  unfold AlgebraMapPollaczekUnitPlusKplus_eq pollaczekUnitPlusKplus
  rw [Units.coe_prod, map_prod]
  rw [pollaczekUnitPlus_val_eq_prod_Ico_two p K i_irreg hp_three]
  rw [show (∏ b ∈ Finset.Ico 2 ((p - 1) / 2 + 1),
        FLT37.realCyclotomicUnit p K b ^ (b ^ (p - 1 - i_irreg))) =
        ∏ j : Fin ((p - 3) / 2),
          FLT37.realCyclotomicUnit p K ((j : ℕ) + 2) ^
            (((j : ℕ) + 2) ^ (p - 1 - i_irreg)) from
        (prod_Fin_eq_prod_Ico_two (p := p) hp_three
          (fun b ↦ FLT37.realCyclotomicUnit p K b ^ (b ^ (p - 1 - i_irreg)))).symm]
  have h_rank_eq :
      NumberField.Units.rank (NumberField.maximalRealSubfield K) = (p - 3) / 2 :=
    (NumberField.IsCMField.units_rank_eq_units_rank (K := K)).trans
      (BernoulliRegular.units_rank_eq_prime_sub_three_div_two (p := p) (K := K))
  rw [Fintype.prod_equiv (finCongr h_rank_eq)
        (fun x ↦ algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
          ((cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three x ^
              (((x : ℕ) + 2) ^ (p - 1 - i_irreg)) :
              (𝓞 (NumberField.maximalRealSubfield K))ˣ) :
              𝓞 (NumberField.maximalRealSubfield K)))
        (fun j ↦ FLT37.realCyclotomicUnit p K ((j : ℕ) + 2) ^
          (((j : ℕ) + 2) ^ (p - 1 - i_irreg)))]
  intro x
  rw [Units.val_pow_eq_pow_val, map_pow]
  congr 1
  exact algebraMap_cyclotomicUnitFamilyKplus p K x hp_odd hp_three

set_option backward.isDefEq.respectTransparency false in
/-- The Pollaczek plus unit lies in the K⁺ family subgroup. -/
theorem pollaczekInFamily (i_irreg : ℕ) (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    PollaczekInFamily p K i_irreg hp_odd hp_three :=
  pollaczekInFamily_of_algebraMap_eq p K i_irreg hp_odd hp_three
    (algebraMapPollaczekUnitPlusKplus_eq p K i_irreg hp_odd hp_three)

set_option backward.isDefEq.respectTransparency false in
/-- `PollaczekForward` implies the Corollary 8.19 bridge. -/
theorem cor8_19Bridge_of_pollaczekForward_full (i : ℕ) (hp_odd : p ≠ 2)
    (hp_three : 3 ≤ p)
    (h_forward : PollaczekForward p K i hp_odd hp_three) :
    Cor8_19Bridge p K i :=
  cor8_19Bridge_of_pollaczekForward p K i hp_odd hp_three
    (pollaczekInFamily p K i hp_odd hp_three) h_forward

end Sinnott

end FLT37

end BernoulliRegular

end

import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.IndexFormula

/-!
# p-saturation for the Sinnott bridge

This file proves the group-theoretic p-saturation step used by the Sinnott
bridge. It applies a finite-index coprimality argument to the subgroup generated
by the K⁺ cyclotomic unit family and torsion.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable {G : Type*} [CommGroup G]

set_option backward.isDefEq.respectTransparency false in
/-- If `H ≤ G` has finite index coprime to `p`, then `α ^ p ∈ H` implies
`α ∈ H`. -/
theorem mem_of_pow_mem_of_index_coprime {p : ℕ} (_hp : Nat.Prime p)
    {H : Subgroup G} (_h_index : H.index ≠ 0)
    (hcop : H.index.Coprime p) {α : G} (hα : α ^ p ∈ H) : α ∈ H := by
  have h_n : α ^ H.index ∈ H := H.pow_index_mem α
  have hgcd : Nat.gcd p H.index = 1 := by
    rw [Nat.coprime_comm] at hcop
    exact hcop
  have hbezout : (1 : ℤ) = p * Nat.gcdA p H.index + H.index * Nat.gcdB p H.index := by
    have := Nat.gcd_eq_gcd_ab p H.index
    rw [hgcd] at this
    exact_mod_cast this
  have h_pow_eq : α =
      (α ^ p) ^ Nat.gcdA p H.index * (α ^ H.index) ^ Nat.gcdB p H.index := by
    calc α = α ^ (1 : ℤ) := (zpow_one α).symm
      _ = α ^ ((p : ℤ) * Nat.gcdA p H.index + (H.index : ℤ) * Nat.gcdB p H.index) := by
            rw [← hbezout]
      _ = α ^ ((p : ℤ) * Nat.gcdA p H.index) *
            α ^ ((H.index : ℤ) * Nat.gcdB p H.index) := by rw [zpow_add]
      _ = (α ^ p) ^ Nat.gcdA p H.index * (α ^ H.index) ^ Nat.gcdB p H.index := by
            rw [zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  rw [h_pow_eq]
  exact H.mul_mem (H.zpow_mem hα _) (H.zpow_mem h_n _)

set_option backward.isDefEq.respectTransparency false in
/-- Under `SinnottIndexFormula` and `¬p ∣ h⁺`, a `p`-th-power witness in
`(𝓞 K⁺)ˣ` for an element of `⟨family⟩ ⊔ torsion` descends to a witness inside
that subgroup. -/
theorem isPthPower_iff_isPthPower_of_sinnott
    (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (h_sinnott : SinnottIndexFormula p K hp_odd hp_three)
    (h_not_dvd : ¬ (p : ℕ) ∣ hPlus K)
    {α : (𝓞 (NumberField.maximalRealSubfield K))ˣ}
    (hα : α ∈ Subgroup.closure
        (Set.range (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ⊔
      NumberField.Units.torsion (NumberField.maximalRealSubfield K))
    (h_pow : ∃ β : (𝓞 (NumberField.maximalRealSubfield K))ˣ, β ^ p = α) :
    ∃ γ ∈ (Subgroup.closure
        (Set.range (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ⊔
      NumberField.Units.torsion (NumberField.maximalRealSubfield K)),
      γ ^ p = α := by
  obtain ⟨β, hβ⟩ := h_pow
  refine ⟨β, ?_, hβ⟩
  set H : Subgroup (𝓞 (NumberField.maximalRealSubfield K))ˣ :=
    Subgroup.closure
        (Set.range (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ⊔
      NumberField.Units.torsion (NumberField.maximalRealSubfield K)
  have h_β_pow_in : β ^ p ∈ H := hβ ▸ hα
  unfold SinnottIndexFormula at h_sinnott
  have h_index : H.index = 2 ^ ((p - 3) / 2) * hPlus K := h_sinnott
  have h_hPlus_pos : 0 < hPlus K :=
    Nat.pos_of_ne_zero (Fintype.card_ne_zero)
  have h_two_pow_pos : 0 < 2 ^ ((p - 3) / 2) := pow_pos (by norm_num) _
  have h_index_ne : H.index ≠ 0 := by
    rw [h_index]
    exact (Nat.mul_pos h_two_pow_pos h_hPlus_pos).ne'
  have h_index_coprime : H.index.Coprime p := by
    rw [h_index]
    have h_hp_prime : Nat.Prime p := Fact.out
    have h_two_cop : Nat.Coprime 2 p := by
      rcases h_hp_prime.eq_two_or_odd with h | h
      · exact absurd h hp_odd
      · exact (Nat.coprime_primes Nat.prime_two h_hp_prime).mpr fun h2 ↦ by omega
    have h_pow_cop : Nat.Coprime (2 ^ ((p - 3) / 2)) p := h_two_cop.pow_left _
    have h_hPlus_cop : Nat.Coprime (hPlus K) p :=
      (h_hp_prime.coprime_iff_not_dvd.mpr h_not_dvd).symm
    exact (Nat.Coprime.mul_right h_pow_cop.symm h_hPlus_cop.symm).symm
  exact mem_of_pow_mem_of_index_coprime Fact.out h_index_ne h_index_coprime h_β_pow_in

set_option backward.isDefEq.respectTransparency false in
/-- The `PollaczekInFamily` witness gives the K⁺ preimage of
`pollaczekUnitPlus` needed for the K-side p-th-power descent. -/
theorem isPthPower_descent_pollaczekUnitPlus (p : ℕ) [hp : Fact p.Prime]
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (i : ℕ) (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (h_pollaczek : PollaczekInFamily p K i hp_odd hp_three)
    (_h_pth : ∃ α : (𝓞 K)ˣ,
      ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) = ((α : (𝓞 K)ˣ) : 𝓞 K) ^ p) :
    ∃ v : (𝓞 (NumberField.maximalRealSubfield K))ˣ,
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (v : 𝓞 _) : 𝓞 K) =
        ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) := by
  obtain ⟨v, hv, _⟩ := h_pollaczek
  exact ⟨v, hv⟩

end Sinnott

end FLT37

end BernoulliRegular

end

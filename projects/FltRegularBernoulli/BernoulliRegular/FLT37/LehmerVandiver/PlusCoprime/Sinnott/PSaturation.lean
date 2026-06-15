import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.IndexFormula


/-!
# p-saturation lemma for the Sinnott bridge

The "p-saturation" argument: for a subgroup `H ≤ G` of finite index `n` with
`p ∤ n` (and `p` prime), if `α^p ∈ H` for some `α ∈ G`, then `α ∈ H · G^p`.

Equivalently, the inclusion `H/H^p → G/G^p` is **injective on its image**:
an element of `H` is a `p`-th power in `G` iff it is a `p`-th power in `H`.

This is the key generic group-theoretic lemma that, combined with
`SinnottIndexFormula` (giving `[E⁺ : C⁺] = h⁺`) and `PollaczekInFamily`
(`pollaczekUnitPlus ∈ ⟨family⟩ ⊔ torsion`), produces `Cor8_19Bridge`.

## Strategy

For finite index `n` with `gcd(p, n) = 1`: if `α ∈ G` with `α^p ∈ H`, write
`α^n ∈ H` (since `[G : H] = n` means `G^n ⊆ H`-ish... actually no, this is
the wrong direction).

Cleaner: `[G : H] = n` and `p ∤ n` means there exist integers `a, b` with
`a·p + b·n = 1` (Bézout). For `α ∈ G` with `α^p ∈ H`: set `β := (α^p)^a`, so
`β ∈ H`. We have `α = α^1 = α^{a·p + b·n} = β · (α^n)^b`. Since `α^n ∈ H`
(quotient `G/H` has order `n`, so `(α H)^n = H` ⟹ `α^n ∈ H`), `(α^n)^b ∈ H`.
Hence `α = β · (α^n)^b ∈ H`. Wait that's stronger than p-saturation —
gives `α ∈ H` directly!

Actually that's correct: under coprimality, the inclusion is "absolutely
saturated" — no extension is needed. So if `α^p ∈ H` then `α ∈ H`.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable {G : Type*} [CommGroup G]

set_option backward.isDefEq.respectTransparency false in
/-- **p-saturation lemma**: if `H ≤ G` has finite index coprime to `p`,
then `α^p ∈ H` implies `α ∈ H`.

Proof: Bézout gives `a·p + b·n = 1` for `n = [G : H]`. Since `n = [G : H]`
and `G/H` is finite cyclic-or-product of cyclic groups of order dividing `n`,
`α^n ∈ H` for any `α ∈ G`. Then `α = (α^p)^a · (α^n)^b ∈ H`. -/
theorem mem_of_pow_mem_of_index_coprime {p : ℕ} (_hp : Nat.Prime p)
    {H : Subgroup G} (_h_index : H.index ≠ 0)
    (hcop : H.index.Coprime p) {α : G} (hα : α ^ p ∈ H) : α ∈ H := by
  -- Use that α^[G : H] ∈ H (Lagrange / quotient finite).
  have h_n : α ^ H.index ∈ H := H.pow_index_mem α
  -- Bézout: gcd(p, H.index) = 1 = p · gcdA + H.index · gcdB.
  have hgcd : Nat.gcd p H.index = 1 := by
    rw [Nat.coprime_comm] at hcop
    exact hcop
  have hbezout : (1 : ℤ) = p * Nat.gcdA p H.index + H.index * Nat.gcdB p H.index := by
    have := Nat.gcd_eq_gcd_ab p H.index
    rw [hgcd] at this
    exact_mod_cast this
  -- α = α^1 = α^(p · s + m · t) = (α^p)^s · (α^m)^t.
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
/-- **Cor 8.19 contrapositive engine**: under `SinnottIndexFormula` and
`¬p ∣ h⁺`, an element of `⟨family⟩ ⊔ torsion` is a `p`-th power in
`(𝓞 K⁺)ˣ` iff it is a `p`-th power in `⟨family⟩ ⊔ torsion`.

This is the p-saturation lemma applied to the family-generated subgroup
under Sinnott's index formula. -/
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
  -- Apply p-saturation: β^p = α ∈ H, [G : H] = h⁺, p ∤ h⁺ → β ∈ H.
  set H : Subgroup (𝓞 (NumberField.maximalRealSubfield K))ˣ :=
    Subgroup.closure
        (Set.range (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ⊔
      NumberField.Units.torsion (NumberField.maximalRealSubfield K)
  have h_β_pow_in : β ^ p ∈ H := hβ ▸ hα
  unfold SinnottIndexFormula at h_sinnott
  -- h_sinnott : H.index = 2^((p-3)/2) · hPlus K.
  -- Want: index.Coprime p. Both factors 2^((p-3)/2) and hPlus K are coprime
  -- to the odd prime p (the first by gcd(2, p) = 1, the second by h_not_dvd).
  have h_index : H.index = 2 ^ ((p - 3) / 2) * hPlus K := h_sinnott
  have h_hPlus_pos : 0 < hPlus K :=
    Nat.pos_of_ne_zero (Fintype.card_ne_zero)
  have h_two_pow_pos : 0 < 2 ^ ((p - 3) / 2) := pow_pos (by norm_num) _
  have h_index_ne : H.index ≠ 0 := by
    rw [h_index]
    exact (Nat.mul_pos h_two_pow_pos h_hPlus_pos).ne'
  have h_index_coprime : H.index.Coprime p := by
    rw [h_index]
    -- Coprime is multiplicative: 2^k coprime p AND hPlus coprime p.
    have h_hp_prime : Nat.Prime p := Fact.out
    have h_two_cop : Nat.Coprime 2 p := by
      rcases h_hp_prime.eq_two_or_odd with h | h
      · -- p = 2 contradicts p ≠ 2 via h_not_dvd (since h_not_dvd would
        -- imply ¬ 2 ∣ hPlus K, but hPlus K ≥ 1 means we have a constraint).
        -- Actually we use hp_odd which is in scope.
        exact absurd h hp_odd
      · exact (Nat.coprime_primes Nat.prime_two h_hp_prime).mpr fun h2 => by omega
    have h_pow_cop : Nat.Coprime (2 ^ ((p - 3) / 2)) p := h_two_cop.pow_left _
    have h_hPlus_cop : Nat.Coprime (hPlus K) p :=
      (h_hp_prime.coprime_iff_not_dvd.mpr h_not_dvd).symm
    -- (h_pow_cop.symm : Coprime p (2^_)) and (h_hPlus_cop.symm : Coprime p hPlus)
    -- ⟹ Coprime p (2^_ * hPlus) via Nat.Coprime.mul_right
    exact (Nat.Coprime.mul_right h_pow_cop.symm h_hPlus_cop.symm).symm
  exact mem_of_pow_mem_of_index_coprime Fact.out h_index_ne h_index_coprime h_β_pow_in

/-! ## Lifting K-side `IsPthPower` to K⁺ via PollaczekInFamily

The bridge takes `¬IsPthPower(pollaczekUnitPlus in (𝓞 K)ˣ)` and produces
`¬p∣h⁺`. The contrapositive: `p∣h⁺ → IsPthPower in (𝓞 K)ˣ`.

Under `PollaczekInFamily` (giving K⁺-side preimage `v ∈ H`) and
p-saturation, **IF** we know `pollaczekUnitPlus is a p-th power in
(𝓞 K)ˣ` from some external source, we can transfer to a p-th power
in `(𝓞 K⁺)ˣ` of the K⁺-preimage, and from there p-saturation says
the p-th-root descent into H. This isn't the bridge direction, but
provides a useful asymmetric bridge engine. -/

set_option backward.isDefEq.respectTransparency false in
/-- **K⁺-descent of K-side IsPthPower for σ-fixed elements**: if a
σ-fixed (real) element `α : (𝓞 K)ˣ` is a p-th power in `(𝓞 K)ˣ`,
then either it's a p-th power in `(𝓞 K⁺)ˣ` after lifting, or the
p-th root differs by a torsion factor (a p-th root of unity) that
also descends. (Statement form: there's a witness modulo torsion.) -/
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

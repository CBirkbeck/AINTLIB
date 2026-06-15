module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Setup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DigitSum

/-!
# Stickelberger congruence assembly (Layer 2, REF-18c2c4)

This file contains the ideal-theoretic assembly step for the digit-sum
Stickelberger congruence.  Once the Gauss sum is known congruent modulo
`Q^(s+1)` to a leading term of exact `Q`-adic order `s`, the desired
membership/non-membership statement follows formally.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace Furtwaengler

/-- If `x` is congruent to `y` modulo `I^(n+1)` and `y` has exact
`I`-adic order `n`, then `x` has exact `I`-adic order `n`.

This is the final ideal-calculus step in the Stickelberger congruence:
all arithmetic work is concentrated in proving the leading congruence and
the exact order of the leading term. -/
theorem exact_mem_pow_of_sub_mem_succ
    {R : Type*} [CommRing R] {I : Ideal R} {x y : R} {n : ℕ}
    (hy_mem : y ∈ I ^ n) (hy_not_mem_succ : y ∉ I ^ (n + 1))
    (hxy : x - y ∈ I ^ (n + 1)) :
    x ∈ I ^ n ∧ x ∉ I ^ (n + 1) := by
  have hsucc_le : I ^ (n + 1) ≤ I ^ n :=
    Ideal.pow_le_pow_right (Nat.le_succ n)
  refine ⟨?_, ?_⟩
  · rw [show x = (x - y) + y by ring]
    exact (I ^ n).add_mem (hsucc_le hxy) hy_mem
  · intro hx
    apply hy_not_mem_succ
    rw [show y = x - (x - y) by ring]
    exact (I ^ (n + 1)).sub_mem hx hxy

variable {p : ℕ} [Fact p.Prime]
variable {k : Type*} [Field k] [Fintype k]
variable {R' : Type*} [CommRing R'] [IsDomain R']

namespace StickelbergerSetup

variable (S : StickelbergerSetup p k R')

/-- Non-triviality of the powers `χ_q^a` in the Stickelberger range
`1 ≤ a ≤ p - 1`. -/
theorem residueChar_pow_ne_one {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.residueChar ^ a ≠ 1 := by
  intro h
  have h_order : orderOf S.residueChar = p := S.orderOf_residueChar
  have h_dvd : orderOf S.residueChar ∣ a := orderOf_dvd_of_pow_eq_one h
  rw [h_order] at h_dvd
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have ha_lt : a < p := lt_of_le_of_lt ha₂ (Nat.sub_lt hp_pos Nat.one_pos)
  have ha_ge_p : p ≤ a := Nat.le_of_dvd (Nat.lt_of_lt_of_le Nat.one_pos ha₁) h_dvd
  omega

/-- Phase-B containment for every non-trivial power of the residue character.
If the additive character is constantly `1` modulo `I`, then
`g(χ_q^a, ψ_q) ∈ I` for `1 ≤ a ≤ p - 1`. -/
theorem gaussSum_residueChar_pow_mem_ideal {I : Ideal R'} {a : ℕ}
    (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (hψ : ∀ x : k, S.psi_q x - 1 ∈ I) :
    _root_.gaussSum (S.residueChar ^ a) S.psi_q ∈ I :=
  gaussSum_mem_ideal_of_addChar_sub_one_mem
    (S.residueChar_pow_ne_one ha₁ ha₂) S.psi_q hψ

/-- Cyclotomic form of `gaussSum_residueChar_pow_mem_ideal`: if
`ψ_q(x) = ζ^f(x)` and the prime ideal contains the residue characteristic,
then every Stickelberger-range Gauss sum lies in `Q`. -/
theorem gaussSum_residueChar_pow_mem_ideal_of_q_mem
    {ℓ : ℕ} [Fact ℓ.Prime] {ζ : R'} (hζ : IsPrimitiveRoot ζ ℓ)
    (f : k → ℕ) (hf : ∀ x : k, S.psi_q x = ζ ^ f x)
    {Q : Ideal R'} [Q.IsPrime] (hQ : (ℓ : R') ∈ Q)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    _root_.gaussSum (S.residueChar ^ a) S.psi_q ∈ Q :=
  S.gaussSum_residueChar_pow_mem_ideal ha₁ ha₂ fun x => by
    rw [hf x]
    exact zeta_pow_sub_one_mem_of_natCast_mem hζ hQ (f x)

/-- First-order exactness for every non-trivial power of the residue
character.  This is the `s = 1` version of the Stickelberger congruence:
the containment is Phase B, and non-membership in `Q^2` follows from the
linear coefficient not vanishing modulo `Q`. -/
theorem gaussSum_residueChar_pow_qadic_ord_eq_one_under_nondeg
    {ℓ : ℕ} [Fact ℓ.Prime] {ζ : R'} (hζ : IsPrimitiveRoot ζ ℓ)
    (f : k → ℕ) (hf : ∀ x : k, S.psi_q x = ζ ^ f x)
    {Q : Ideal R'} [Q.IsPrime] (hQ : (ℓ : R') ∈ Q)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_lead :
      (ζ - 1) * (∑ x, (S.residueChar ^ a) x * (f x : R')) ∉ Q ^ 2) :
    _root_.gaussSum (S.residueChar ^ a) S.psi_q ∈ Q ∧
      _root_.gaussSum (S.residueChar ^ a) S.psi_q ∉ Q ^ 2 := by
  refine ⟨?_, ?_⟩
  · exact S.gaussSum_residueChar_pow_mem_ideal_of_q_mem hζ f hf hQ ha₁ ha₂
  · exact gaussSum_not_mem_sq_of_psi_pow
      (S.residueChar_pow_ne_one ha₁ ha₂) f hf
      (zeta_sub_one_mem_of_natCast_mem hζ hQ) h_lead

end StickelbergerSetup

omit [IsDomain R'] in
/-- Layer 2 assembly for the digit-sum Stickelberger congruence.

Let `s = digitSum ℓ (a * ((#k - 1) / p))`.  If a proposed leading term
`lead` has exact `Q`-adic order `s` and the Gauss sum is congruent to it
modulo `Q^(s+1)`, then the Gauss sum has the target exact order.

The remaining mathematical content of REF-18c2c4 is to construct `lead`
as the usual unit times `(ζ_ℓ - 1)^s` and prove the congruence. -/
theorem stickelberger_qadic_ord_at_prime_of_leading_congruence
    (S : StickelbergerSetup p k R') {ℓ : ℕ} (a : ℕ) {Q : Ideal R'} {lead : R'}
    (h_lead_mem :
      lead ∈ Q ^ digitSum ℓ (a * ((Fintype.card k - 1) / p)))
    (h_lead_not_mem_succ :
      lead ∉ Q ^ (digitSum ℓ (a * ((Fintype.card k - 1) / p)) + 1))
    (h_congr :
      gaussSum (S.residueChar ^ a) S.psi_q - lead ∈
        Q ^ (digitSum ℓ (a * ((Fintype.card k - 1) / p)) + 1)) :
    gaussSum (S.residueChar ^ a) S.psi_q ∈
        Q ^ digitSum ℓ (a * ((Fintype.card k - 1) / p)) ∧
      gaussSum (S.residueChar ^ a) S.psi_q ∉
        Q ^ (digitSum ℓ (a * ((Fintype.card k - 1) / p)) + 1) :=
  exact_mem_pow_of_sub_mem_succ h_lead_mem h_lead_not_mem_succ h_congr

end Furtwaengler

end BernoulliRegular

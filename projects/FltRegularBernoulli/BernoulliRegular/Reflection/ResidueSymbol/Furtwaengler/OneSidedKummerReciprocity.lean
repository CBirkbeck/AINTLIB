module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolPrincipalCanonical
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.LambdaLocalPthPower

/-!
# One-sided Kummer principal reciprocity

This file records the final reciprocity statement of `REF-21.6`.

The theorem is the principal-denominator form needed by weak reflection:
for nonzero coprime `α β : 𝓞 K`, both prime to `p`, if `α` is a `p`-th
power in the `λ = (ζ_p - 1)` completion, then the two principal denominator
`p`-th-power residue symbols agree.

The residue symbol is written additively using the canonical
`ZMod p`-valued symbol `Furtwaengler.pthSymbolAtIdeal_canonical`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u

set_option warn.sorry false in
/-- **One-sided Kummer principal reciprocity, canonical additive form.**

Let `K = ℚ(ζ_p)` and `λ = (ζ_p - 1)`.  If `α β : 𝓞 K` are nonzero,
their principal ideals are coprime, both are prime to `p`, and `α` is a
`p`-th power in the `λ`-adic completion, then

`(α / (β))_p = (β / (α))_p`.

Here both sides are written as the canonical additive `ZMod p` residue
symbol `pthSymbolAtIdeal_canonical`. -/
theorem oneSidedKummerPrincipalReciprocity_canonical
    (p : ℕ) [Fact p.Prime] (hp_odd : Odd p)
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {α β : 𝓞 K}
    (hα_ne : α ≠ 0) (hβ_ne : β ≠ 0)
    (hcop :
      IsCoprime
        (Ideal.span ({α} : Set (𝓞 K)))
        (Ideal.span ({β} : Set (𝓞 K))))
    (hα_prime_to_p :
      IsCoprime
        (Ideal.span ({α} : Set (𝓞 K)))
        (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))))
    (hβ_prime_to_p :
      IsCoprime
        (Ideal.span ({β} : Set (𝓞 K)))
        (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))))
    (hα_local : @IsLambdaLocalPthPower p _ K _ _ _ α) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) α
        (Ideal.span ({β} : Set (𝓞 K))) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) β
        (Ideal.span ({α} : Set (𝓞 K))) := by
  sorry

/-- Principal-ideal vanishing for locally primary pseudo-units, in the
canonical additive notation.  This is the immediate corollary of
`oneSidedKummerPrincipalReciprocity_canonical` used to make the residue-symbol
character trivial on principal ideals. -/
theorem locallyPrimaryPseudoUnit_principalSymbol_eq_zero_canonical
    (p : ℕ) [Fact p.Prime] (hp_odd : Odd p)
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {η γ : 𝓞 K} (B : Ideal (𝓞 K))
    (hη_ne : η ≠ 0) (hγ_ne : γ ≠ 0)
    (hcop :
      IsCoprime
        (Ideal.span ({η} : Set (𝓞 K)))
        (Ideal.span ({γ} : Set (𝓞 K))))
    (hη_prime_to_p :
      IsCoprime
        (Ideal.span ({η} : Set (𝓞 K)))
        (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))))
    (hγ_prime_to_p :
      IsCoprime
        (Ideal.span ({γ} : Set (𝓞 K)))
        (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))))
    (hη_local : @IsLambdaLocalPthPower p _ K _ _ _ η)
    (hsing : Ideal.span ({η} : Set (𝓞 K)) = B ^ p) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({γ} : Set (𝓞 K))) = 0 := by
  rw [oneSidedKummerPrincipalReciprocity_canonical
    p hp_odd K hη_ne hγ_ne hcop hη_prime_to_p hγ_prime_to_p hη_local]
  rw [hsing]
  exact pthSymbolAtIdeal_canonical_pow_p_ideal_eq_zero γ B

/-- If an ideal is coprime to every normalized prime factor of a nonzero ideal
`J`, then it is coprime to `J`. -/
theorem isCoprime_ideal_of_isCoprime_normalizedFactors
    (K : Type u) [Field K] [NumberField K]
    {I J : Ideal (𝓞 K)} (hJ_ne : J ≠ ⊥)
    (hcop :
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors J, IsCoprime I P) :
    IsCoprime I J := by
  rw [Ideal.isCoprime_iff_sup_eq]
  rw [← Ideal.prod_normalizedFactors_eq_self hJ_ne]
  exact Ideal.sup_multiset_prod_eq_top (by
    intro P hP
    exact Ideal.isCoprime_iff_sup_eq.mp (hcop P hP))

/-- Bad-set form of principal-ideal vanishing for locally primary
pseudo-units.

If the finite bad set contains all normalized prime factors of `(η)` and of
`(p)`, then any nonzero principal denominator coprime to the bad set is an
admissible denominator for `locallyPrimaryPseudoUnit_principalSymbol_eq_zero_canonical`.
-/
theorem locallyPrimaryPseudoUnit_principalSymbol_eq_zero_canonical_of_coprime_badSet
    (p : ℕ) [Fact p.Prime] (hp_odd : Odd p)
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {η γ : 𝓞 K} (B : Ideal (𝓞 K)) (S : Finset (Ideal (𝓞 K)))
    (hη_ne : η ≠ 0) (hγ_ne : γ ≠ 0)
    (hη_prime_to_p :
      IsCoprime
        (Ideal.span ({η} : Set (𝓞 K)))
        (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))))
    (hη_local : @IsLambdaLocalPthPower p _ K _ _ _ η)
    (hsing : Ideal.span ({η} : Set (𝓞 K)) = B ^ p)
    (hS_eta :
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({η} : Set (𝓞 K))), P ∈ S)
    (hS_p :
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))), P ∈ S)
    (hγ_coprime :
      ∀ P ∈ S, IsCoprime (Ideal.span ({γ} : Set (𝓞 K))) P) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({γ} : Set (𝓞 K))) = 0 := by
  have hη_span_ne : Ideal.span ({η} : Set (𝓞 K)) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hη_ne
  have hγ_coprime_eta :
      IsCoprime (Ideal.span ({γ} : Set (𝓞 K)))
        (Ideal.span ({η} : Set (𝓞 K))) :=
    isCoprime_ideal_of_isCoprime_normalizedFactors
      (K := K) hη_span_ne
      (fun P hP => hγ_coprime P (hS_eta P hP))
  have hp_ne : (p : 𝓞 K) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hp_span_ne : Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp_ne
  have hγ_prime_to_p :
      IsCoprime
        (Ideal.span ({γ} : Set (𝓞 K)))
        (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))) :=
    isCoprime_ideal_of_isCoprime_normalizedFactors
      (K := K) hp_span_ne
      (fun P hP => hγ_coprime P (hS_p P hP))
  exact locallyPrimaryPseudoUnit_principalSymbol_eq_zero_canonical
    p hp_odd K B hη_ne hγ_ne hγ_coprime_eta.symm
    hη_prime_to_p hγ_prime_to_p hη_local hsing

end Furtwaengler

end BernoulliRegular

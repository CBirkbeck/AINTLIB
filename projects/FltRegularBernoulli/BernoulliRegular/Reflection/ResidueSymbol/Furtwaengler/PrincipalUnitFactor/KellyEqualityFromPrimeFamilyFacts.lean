module

public import Mathlib.LinearAlgebra.SModEq.Pow
public import BernoulliRegular.FLT37.PrimaryUnits
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrincipalBridge
public import BernoulliRegular.TotallyRealSubfield.Conjugation
public import BernoulliRegular.UnitQuotient.FreeLatticeComparison.ConjugationTrace
public import BernoulliRegular.UnitQuotient.TorsionQuotient
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor.SignUnitFactor

/-!
# Principal unit factor (REF-18 Phase 2, sub-piece U)

For a nonzero principal ideal `(α)`, the actual multiplicative Φ element
`Φ((α))` and the explicit Stickelberger principal generator
`α^Θ = stickelbergerPrincipalGen α` generate the same ideal. Hence they differ
by a unit:

```
Φ((α)) = u(α) · α^Θ.
```

This file formalizes the honest element-level U-chain interface:

* `PrincipalUnitFactorData α Φα` is the specific unit-factor equation for an
  actual principal Φ element `Φα`.
* `PrincipalUnitFactorData.nonempty_of_nonzero` proves existence of such a
  unit from the already formalized Φ-span theorem.
* If that specific unit is `±1`, its prime residue symbols vanish.
* `ChosenPrimaryUnitFactorProductSymbolZero α` is the reflection-facing
  chosen-object product condition: the same actual Φ element has locally
  trivial product symbols for `Φ((α)) · α` away from `α`.
* `ChosenPrimaryUnitFactorSymbolTrivial α` is the natural chosen-object
  downstream output from one normalized actual principal Φ element.
* `PrimaryUnitFactorSymbolTrivial α` is the stronger uniform downstream
  hypothesis over the current broad `PhiPrincipalElement` API.
* The concrete U4 endpoint is proved in
  `PrincipalUnitFactorData.exists_isSign_of_primary_primePhiFacts` and
  `ChosenPrimaryUnitFactorSymbolTrivial_of_primary_primePhiFacts`: for an
  actual principal Φ product, prime-level semi-primarity plus the prime
  conjugation-norm identities force the specific unit factor to be `±1`, hence
  its prime symbols vanish.

What remains outside this file is constructing the actual principal Φ product
from `K2_2SourceData` for every normalized prime factor and proving the
conjugation compatibility needed for those prime norm identities.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField NumberField.IsCMField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- Universal signed Kelly equality from actual primary prime Φ-family
facts.

This is the universal target-prime form around
`kellyPrimeNegEquality_of_primary_primePhiFamilyFacts`.  It preserves the same
source Φ-family and U4 inputs, while letting the K2-2 symbol identities and
Galois-coprimality side condition vary with the target prime. -/
theorem kellyPrimeNegEquality_all_of_primary_primePhiFamilyFacts
    [IsCMField K] (hp_odd : p ≠ 2) (hp_two : 2 ≤ p) (hp_three : 3 ≤ p)
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (primePhi :
      ∀ P : Ideal (𝓞 K),
        P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
          PhiPrimeElement (p := p) (K := K) P)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (h_prime_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (primePhi P hP).gamma)
    (h_prime_norm :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        ringOfIntegersComplexConj K (primePhi P hP).gamma *
            (primePhi P hP).gamma =
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p)
    (hcop : ∀ P' : Ideal (𝓞 K), P'.IsPrime → P' ≠ ⊥ →
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime_symbol :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        P' (_hP' : P'.IsPrime) (_hP'_ne : P' ≠ ⊥)
        Q (_hQ : Q ∈ normalizedFactors P'),
        PhiPrimeElement.PhiPrimeSymbolIdentity (p := p) (K := K)
          (primePhi P hP) Q)
    (h_coprime : ∀ P' : Ideal (𝓞 K), P'.IsPrime → P' ≠ ⊥ →
      ∀ a : CyclotomicUnitDelta p,
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    ∀ (P' : Ideal (𝓞 K)) [P'.IsPrime], P' ≠ ⊥ →
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
        -pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := fun P' hP'_prime hP'_ne =>
  kellyPrimeNegEquality_of_primary_primePhiFamilyFacts
    (p := p) (K := K) hp_odd hp_two hp_three hα_ne hαp_top primePhi
    hα_primary h_prime_semi h_prime_norm hP'_ne
    (hcop P' hP'_prime hP'_ne)
    (fun P hP Q hQ => h_prime_symbol P hP P' hP'_prime hP'_ne Q hQ)
    (h_coprime P' hP'_prime hP'_ne)

/-- Universal positive Kelly equality from actual primary prime Φ-family
facts in the reciprocal orientation. -/
theorem kellyPrimeEquality_all_of_primary_primePhiFamilyFacts
    [IsCMField K] (hp_odd : p ≠ 2) (hp_two : 2 ≤ p) (hp_three : 3 ≤ p)
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (primePhi :
      ∀ P : Ideal (𝓞 K),
        P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
          PhiPrimeElement (p := p) (K := K) P)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (h_prime_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (primePhi P hP).gamma)
    (h_prime_norm :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        ringOfIntegersComplexConj K (primePhi P hP).gamma *
            (primePhi P hP).gamma =
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p)
    (hcop : ∀ P' : Ideal (𝓞 K), P'.IsPrime → P' ≠ ⊥ →
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime_symbol :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        P' (_hP' : P'.IsPrime) (_hP'_ne : P' ≠ ⊥)
        Q (_hQ : Q ∈ normalizedFactors P'),
        PhiPrimeElement.PhiPrimeSymbolIdentityPos (p := p) (K := K)
          (primePhi P hP) Q)
    (h_coprime : ∀ P' : Ideal (𝓞 K), P'.IsPrime → P' ≠ ⊥ →
      ∀ a : CyclotomicUnitDelta p,
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    ∀ (P' : Ideal (𝓞 K)) [P'.IsPrime], P' ≠ ⊥ →
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := fun P' hP'_prime hP'_ne =>
  kellyPrimeEquality_of_primary_primePhiFamilyFacts
    (p := p) (K := K) hp_odd hp_two hp_three hα_ne hαp_top primePhi
    hα_primary h_prime_semi h_prime_norm hP'_ne
    (hcop P' hP'_prime hP'_ne)
    (fun P hP Q hQ => h_prime_symbol P hP P' hP'_prime hP'_ne Q hQ)
    (h_coprime P' hP'_prime hP'_ne)

end Furtwaengler

end BernoulliRegular

end

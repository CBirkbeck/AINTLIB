module

public import Mathlib.LinearAlgebra.SModEq.Pow
public import BernoulliRegular.FLT37.PrimaryUnits
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrincipalBridge
public import BernoulliRegular.TotallyRealSubfield.Conjugation
public import BernoulliRegular.UnitQuotient.FreeLatticeComparison.ConjugationTrace
public import BernoulliRegular.UnitQuotient.TorsionQuotient
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor.UnitSignEndpointAndKellyEquality

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

/-- Primary-version REF-18-facing U4 endpoint from prime-level Φ
semi-primarity and prime-level Φ conjugation norms.

This is the concrete U4 product theorem after the prime Gauss-sum calculations:
prime Φ factors give the principal Φ conjugation norm by multiplication, the
Stickelberger side gives the signed integer norm, and the possible sign
mismatch is ruled out by the CM complex-embedding argument
`unitsComplexConj_mul_self_ne_neg_one`. -/
theorem PrincipalUnitFactorData.isSign_of_primary_primePhiSemi_primeConjNorm_of_span_pair_p_eq_top
    [IsCMField K] (hp_odd : p ≠ 2) (hp_two : 2 ≤ p) (hp_three : 3 ≤ p)
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (h_prime_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (Φα.primePhi P hP).gamma)
    (h_prime_norm :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        ringOfIntegersComplexConj K (Φα.primePhi P hP).gamma *
            (Φα.primePhi P hP).gamma =
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p) :
    U.IsSign (p := p) (K := K) := by
  have hp_gt_two : 2 < p := by omega
  have h_phi_abs :
      ringOfIntegersComplexConj K Φα.gamma * Φα.gamma =
        (((Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)) : Ideal (𝓞 K)) : ℤ) :
          𝓞 K)) ^ p :=
    phiPrincipal_conj_mul_self_eq_absNorm_pow_of_prime_conj_norm
      (p := p) (K := K) hα_ne Φα h_prime_norm
  have h_stick_int :
      ringOfIntegersComplexConj K
          (stickelbergerPrincipalGen (p := p) (K := K) α) *
          stickelbergerPrincipalGen (p := p) (K := K) α =
        (((Algebra.norm ℤ α : ℤ) : 𝓞 K)) ^ p :=
    ringOfIntegersComplexConj_stickelbergerPrincipalGen_mul_self_eq_intNorm_pow
      (p := p) (K := K) hp_gt_two
  have h_conj :
      unitsComplexConj K U.unit_isUnit.unit * U.unit_isUnit.unit = 1 :=
    U.unitUnit_conj_mul_self_eq_one_of_conj_gamma_absNorm_pow
      (p := p) (K := K) hp_odd hα_ne h_phi_abs h_stick_int
  have h_unit_semi :
      FLT37.IsSemiPrimary p (K := K) (U.unit_isUnit.unit : 𝓞 K) :=
    U.unitUnit_isSemiPrimary_of_primePhiSemi_of_not_zetaSubOne_dvd
      (p := p) (K := K) hp_two hp_three
      (FLT37.IsPrimary.toIsSemiPrimary (p := p) (K := K) hα_primary)
      (not_zetaSubOne_dvd_of_span_pair_p_eq_top
        (p := p) (K := K) hp_three hαp_top)
      h_prime_semi
  exact U.isSign_of_unitsComplexConj_mul_self_eq_one_of_unit_isSemiPrimary
    (p := p) (K := K) hp_odd hp_three h_conj h_unit_semi

/-- Existential U4 sign theorem from the concrete prime Φ calculations.

For a fixed actual principal Φ product, the same-span theorem produces the
specific unit factor `u` in `Φ((α)) = u * α^Θ`; the prime-level semi-primary
and conjugation-norm facts then force that unit to be `±1`. -/
theorem PrincipalUnitFactorData.exists_isSign_of_primary_primePhiFacts
    [IsCMField K] (hp_odd : p ≠ 2) (hp_two : 2 ≤ p) (hp_three : 3 ≤ p)
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (h_prime_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (Φα.primePhi P hP).gamma)
    (h_prime_norm :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        ringOfIntegersComplexConj K (Φα.primePhi P hP).gamma *
            (Φα.primePhi P hP).gamma =
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p) :
    ∃ U : PrincipalUnitFactorData (p := p) (K := K) α Φα,
      U.IsSign (p := p) (K := K) := by
  let U := PrincipalUnitFactorData.ofNonzero (p := p) (K := K) hα_ne Φα
  exact ⟨U,
    U.isSign_of_primary_primePhiSemi_primeConjNorm_of_span_pair_p_eq_top
      (p := p) (K := K) hp_odd hp_two hp_three hα_ne hαp_top
      hα_primary h_prime_semi h_prime_norm⟩

/-- Symbol-trivial U4 theorem from the concrete prime Φ calculations.

This is the U-chain output needed by the K-chain: once the actual principal Φ
product has semi-primary prime factors and the expected prime conjugation
norms, the specific unit relating it to `α^Θ` has trivial prime symbols. -/
theorem PrimaryUnitFactorSymbolTrivial_of_primary_primePhiFacts
    [IsCMField K] (hp_odd : p ≠ 2) (hp_two : 2 ≤ p) (hp_three : 3 ≤ p)
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (h_prime_semi :
      ∀ Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
          (p := p) (K := K) α,
        ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
          FLT37.IsSemiPrimary p (K := K) (Φα.primePhi P hP).gamma)
    (h_prime_norm :
      ∀ Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
          (p := p) (K := K) α,
        ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
          ringOfIntegersComplexConj K (Φα.primePhi P hP).gamma *
              (Φα.primePhi P hP).gamma =
            (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p) :
    PrimaryUnitFactorSymbolTrivial (p := p) (K := K) α := by
  intro Φα
  obtain ⟨U, hU⟩ :=
    PrincipalUnitFactorData.exists_isSign_of_primary_primePhiFacts
      (p := p) (K := K) hp_odd hp_two hp_three hα_ne hαp_top Φα
      hα_primary (h_prime_semi Φα) (h_prime_norm Φα)
  exact ⟨U, U.unit_prime_symbol_zero_of_isSign
    (p := p) (K := K) ((Fact.out : Nat.Prime p).odd_of_ne_two hp_odd) hU⟩

/-- Chosen-object symbol-trivial U4 theorem from the concrete prime Φ
calculations.

This is the classical shape: construct one actual principal Φ product from the
Gauss-sum prime factors, prove the prime-level semi-primary and conjugation
norm facts for those factors, and obtain the required symbol-trivial unit. -/
theorem ChosenPrimaryUnitFactorSymbolTrivial_of_primary_primePhiFacts
    [IsCMField K] (hp_odd : p ≠ 2) (hp_two : 2 ≤ p) (hp_three : 3 ≤ p)
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (h_prime_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (Φα.primePhi P hP).gamma)
    (h_prime_norm :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        ringOfIntegersComplexConj K (Φα.primePhi P hP).gamma *
            (Φα.primePhi P hP).gamma =
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p) :
    ChosenPrimaryUnitFactorSymbolTrivial (p := p) (K := K) α := by
  obtain ⟨U, hU⟩ :=
    PrincipalUnitFactorData.exists_isSign_of_primary_primePhiFacts
      (p := p) (K := K) hp_odd hp_two hp_three hα_ne hαp_top Φα
      hα_primary h_prime_semi h_prime_norm
  exact ⟨Φα, U, U.unit_prime_symbol_zero_of_isSign
    (p := p) (K := K) ((Fact.out : Nat.Prime p).odd_of_ne_two hp_odd) hU⟩

/-- Chosen-object U4 directly from a family of actual prime Φ factors.

This constructs the actual principal Φ product internally from the prime-factor
family over `normalizedFactors (α)`. Thus the U4 consumer no longer needs a
separately supplied principal Φ product. -/
theorem ChosenPrimaryUnitFactorSymbolTrivial_of_primary_primePhiFamilyFacts
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
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p) :
    ChosenPrimaryUnitFactorSymbolTrivial (p := p) (K := K) α := by
  let Φα :=
    PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors
      (p := p) (K := K) α primePhi
  exact ChosenPrimaryUnitFactorSymbolTrivial_of_primary_primePhiFacts
    (p := p) (K := K) hp_odd hp_two hp_three hα_ne hαp_top Φα
    hα_primary h_prime_semi h_prime_norm

/-- Chosen-object product-power U-chain data from one actual principal Φ
element.

This extends `ChosenPrimaryUnitFactorSymbolTrivial_of_primary_primePhiFacts`
by retaining the exact product-power identity for the same `Φα`. -/
theorem ChosenPrimaryUnitFactorProductPower_of_primary_primePhiFacts
    [IsCMField K] (hp_odd : p ≠ 2) (hp_two : 2 ≤ p) (hp_three : 3 ≤ p)
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (h_prime_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (Φα.primePhi P hP).gamma)
    (h_prime_norm :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        ringOfIntegersComplexConj K (Φα.primePhi P hP).gamma *
            (Φα.primePhi P hP).gamma =
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p)
    (h_phi_product : ∃ β : 𝓞 K, Φα.gamma * α = β ^ p) :
    ChosenPrimaryUnitFactorProductPower (p := p) (K := K) α := by
  obtain ⟨U, hU⟩ :=
    PrincipalUnitFactorData.exists_isSign_of_primary_primePhiFacts
      (p := p) (K := K) hp_odd hp_two hp_three hα_ne hαp_top Φα
      hα_primary h_prime_semi h_prime_norm
  exact ⟨Φα, U,
    U.unit_prime_symbol_zero_of_isSign
      (p := p) (K := K) ((Fact.out : Nat.Prime p).odd_of_ne_two hp_odd) hU,
    h_phi_product⟩

/-- Chosen-object product-power U-chain data directly from a family of actual
prime Φ factors.

The exact product-power input is for the principal Φ product built from the
same `primePhi` family, so the product unit remains tied to the actual
Gauss-sum normalization. -/
theorem ChosenPrimaryUnitFactorProductPower_of_primary_primePhiFamilyFacts
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
    (h_phi_product :
      ∃ β : 𝓞 K,
        (PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors
          (p := p) (K := K) α primePhi).gamma * α = β ^ p) :
    ChosenPrimaryUnitFactorProductPower (p := p) (K := K) α := by
  let Φα :=
    PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors
      (p := p) (K := K) α primePhi
  have h_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (Φα.primePhi P hP).gamma := by
    intro P hP
    simpa [Φα, PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors,
      PhiPrimeElement.PhiIdealElement.ofPrimeFactors] using h_prime_semi P hP
  have h_norm :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        ringOfIntegersComplexConj K (Φα.primePhi P hP).gamma *
            (Φα.primePhi P hP).gamma =
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
    intro P hP
    simpa [Φα, PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors,
      PhiPrimeElement.PhiIdealElement.ofPrimeFactors] using h_prime_norm P hP
  exact ChosenPrimaryUnitFactorProductPower_of_primary_primePhiFacts
    (p := p) (K := K) hp_odd hp_two hp_three hα_ne hαp_top Φα
    hα_primary h_semi h_norm h_phi_product

/-- Chosen-object local product-symbol U-chain data from one actual principal
Φ element.

This is the local-symbol analogue of
`ChosenPrimaryUnitFactorProductPower_of_primary_primePhiFacts`; it keeps the
product input at the exact strength needed by the reflection transfer. -/
theorem ChosenPrimaryUnitFactorProductSymbolZero_of_primary_primePhiFacts
    [IsCMField K] (hp_odd : p ≠ 2) (hp_two : 2 ≤ p) (hp_three : 3 ≤ p)
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (h_prime_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (Φα.primePhi P hP).gamma)
    (h_prime_norm :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        ringOfIntegersComplexConj K (Φα.primePhi P hP).gamma *
            (Φα.primePhi P hP).gamma =
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p)
    (h_phi_product_zero :
      ∀ P : Ideal (𝓞 K), α ∉ P →
        pthSymbolAtPrime_canonical (p := p) (K := K) (Φα.gamma * α) P = 0) :
    ChosenPrimaryUnitFactorProductSymbolZero (p := p) (K := K) α := by
  obtain ⟨U, hU⟩ :=
    PrincipalUnitFactorData.exists_isSign_of_primary_primePhiFacts
      (p := p) (K := K) hp_odd hp_two hp_three hα_ne hαp_top Φα
      hα_primary h_prime_semi h_prime_norm
  exact ⟨Φα, U,
    U.unit_prime_symbol_zero_of_isSign
      (p := p) (K := K) ((Fact.out : Nat.Prime p).odd_of_ne_two hp_odd) hU,
    h_phi_product_zero⟩

/-- Chosen-object local product-symbol U-chain data directly from a family of
actual prime Φ factors.

The local product-symbol input is for the principal Φ product built from the
same `primePhi` family, so the product transfer remains tied to the actual
Gauss-sum normalization. -/
theorem ChosenPrimaryUnitFactorProductSymbolZero_of_primary_primePhiFamilyFacts
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
    (h_phi_product_zero :
      ∀ P : Ideal (𝓞 K), α ∉ P →
        pthSymbolAtPrime_canonical (p := p) (K := K)
          ((PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors
            (p := p) (K := K) α primePhi).gamma * α) P = 0) :
    ChosenPrimaryUnitFactorProductSymbolZero (p := p) (K := K) α := by
  let Φα :=
    PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors
      (p := p) (K := K) α primePhi
  have h_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (Φα.primePhi P hP).gamma := by
    intro P hP
    simpa [Φα, PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors,
      PhiPrimeElement.PhiIdealElement.ofPrimeFactors] using h_prime_semi P hP
  have h_norm :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        ringOfIntegersComplexConj K (Φα.primePhi P hP).gamma *
            (Φα.primePhi P hP).gamma =
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
    intro P hP
    simpa [Φα, PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors,
      PhiPrimeElement.PhiIdealElement.ofPrimeFactors] using h_prime_norm P hP
  have h_phi_zero :
      ∀ P : Ideal (𝓞 K), α ∉ P →
        pthSymbolAtPrime_canonical (p := p) (K := K) (Φα.gamma * α) P = 0 := by
    intro P hα_not
    simpa [Φα] using h_phi_product_zero P hα_not
  exact ChosenPrimaryUnitFactorProductSymbolZero_of_primary_primePhiFacts
    (p := p) (K := K) hp_odd hp_two hp_three hα_ne hαp_top Φα
    hα_primary h_semi h_norm h_phi_zero

/-- Data-carrying conjugation-normalized principal Φ-unit factor.

This is closer to the classical U4 proof than `NormalizedPrincipalPhiUnitData`:
the root-of-unity part is certified by the actual conjugation identity
`conj(u) * u = 1`, while the λ² congruence is recorded as semi-primarity of
the same unit. -/
structure ConjugationNormalizedPrincipalPhiUnitData
    [IsCMField K]
    (α : 𝓞 K)
    (Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α) where
  /-- The actual Φ-to-Stickelberger principal unit factor. -/
  factor : PrincipalUnitFactorData (p := p) (K := K) α Φα
  /-- The associated global unit is antisymmetric under complex conjugation. -/
  factor_conj_mul_self :
    unitsComplexConj K factor.unit_isUnit.unit * factor.unit_isUnit.unit = 1
  /-- The associated global unit is semi-primary. -/
  factor_isSemiPrimary :
    FLT37.IsSemiPrimary p (K := K) (factor.unit_isUnit.unit : 𝓞 K)

namespace ConjugationNormalizedPrincipalPhiUnitData

/-- A conjugation-normalized principal Φ-unit factor is cyclotomic torsion. -/
theorem factor_torsion
    [IsCMField K] (hp_odd : p ≠ 2)
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (D : ConjugationNormalizedPrincipalPhiUnitData (p := p) (K := K) α Φα) :
    D.factor.unit_isUnit.unit ∈ CyclotomicUnitTorsion K :=
  unit_mem_cyclotomicUnitTorsion_of_unitsComplexConj_mul_self_eq_one
    (p := p) (K := K) hp_odd D.factor.unit_isUnit.unit
    D.factor_conj_mul_self

/-- A conjugation-normalized principal Φ-unit factor supplies the previous
normalized U4 package. -/
def toNormalizedPrincipalPhiUnitData
    [IsCMField K] (hp_odd : p ≠ 2)
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (D : ConjugationNormalizedPrincipalPhiUnitData (p := p) (K := K) α Φα) :
    NormalizedPrincipalPhiUnitData (p := p) (K := K) α Φα where
  factor := D.factor
  factor_torsion := D.factor_torsion (p := p) (K := K) hp_odd
  factor_isSemiPrimary := D.factor_isSemiPrimary

/-- A conjugation-normalized principal Φ-unit factor is a sign. -/
theorem isSign
    [IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (D : ConjugationNormalizedPrincipalPhiUnitData (p := p) (K := K) α Φα) :
    D.factor.IsSign (p := p) (K := K) :=
  D.factor.isSign_of_unitsComplexConj_mul_self_eq_one_of_unit_isSemiPrimary
    (p := p) (K := K) hp_odd hp_three
    D.factor_conj_mul_self D.factor_isSemiPrimary

end ConjugationNormalizedPrincipalPhiUnitData

/-- A chosen conjugation-normalized actual principal Φ element.

This packages the two concrete classical facts that remain for U4: the
principal Φ-unit satisfies the conjugation product formula and is congruent to
an integer modulo `(ζ - 1)^2`. -/
structure ConjugationNormalizedPrincipalPhiElement (α : 𝓞 K) where
  /-- The cyclotomic field is used through its complex conjugation. -/
  [isCMField : IsCMField K]
  /-- The actual principal Φ element. -/
  phi : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement (p := p) (K := K) α
  /-- The conjugation-normalized unit data for this actual Φ element. -/
  normalized : ConjugationNormalizedPrincipalPhiUnitData (p := p) (K := K) α phi

namespace ConjugationNormalizedPrincipalPhiElement

/-- A chosen conjugation-normalized principal Φ element supplies the previous
normalized principal Φ package. -/
def toNormalizedPrincipalPhiElement
    (hp_odd : p ≠ 2)
    {α : 𝓞 K}
    (D : ConjugationNormalizedPrincipalPhiElement (p := p) (K := K) α) :
    NormalizedPrincipalPhiElement (p := p) (K := K) α where
  phi := D.phi
  normalized := by
    letI : IsCMField K := D.isCMField
    exact D.normalized.toNormalizedPrincipalPhiUnitData
      (p := p) (K := K) hp_odd

/-- A chosen conjugation-normalized actual principal Φ element supplies a
specific symbol-trivial unit factor. -/
theorem symbolTrivial
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    {α : 𝓞 K}
    (D : ConjugationNormalizedPrincipalPhiElement (p := p) (K := K) α) :
    ∃ Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
        (p := p) (K := K) α,
      ∃ U : PrincipalUnitFactorData (p := p) (K := K) α Φα,
        ∀ P : Ideal (𝓞 K),
          pthSymbolAtPrime_canonical (p := p) (K := K) U.unit P = 0 :=
  (D.toNormalizedPrincipalPhiElement (p := p) (K := K) hp_odd).symbolTrivial
    (p := p) (K := K) hp_odd hp_three

end ConjugationNormalizedPrincipalPhiElement

/-- The conjugation-normalized U4 target for semi-primary numerators. -/
def SemiPrimaryConjugationNormalizedPrincipalPhiHypothesis (α : 𝓞 K) : Prop :=
  FLT37.IsSemiPrimary p (K := K) α → α ≠ 0 →
    Nonempty (ConjugationNormalizedPrincipalPhiElement (p := p) (K := K) α)

/-- The conjugation-normalized U4 target implies the previous chosen-object
normalized U4 target. -/
theorem SemiPrimaryChosenNormalizedPrincipalPhiHypothesis_of_conjugationNormalized
    (hp_odd : p ≠ 2) {α : 𝓞 K}
    (h_norm :
      SemiPrimaryConjugationNormalizedPrincipalPhiHypothesis (p := p) (K := K) α) :
    SemiPrimaryChosenNormalizedPrincipalPhiHypothesis (p := p) (K := K) α := by
  intro hsemi hα
  obtain ⟨D⟩ := h_norm hsemi hα
  exact ⟨D.toNormalizedPrincipalPhiElement (p := p) (K := K) hp_odd⟩

/-- A chosen conjugation-normalized semi-primary principal Φ-unit theorem gives
the chosen-object primary U-chain output directly. -/
theorem ChosenPrimaryUnitFactorSymbolTrivial_of_conjugationNormalized
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) {α : 𝓞 K}
    (h_primary : FLT37.IsPrimary p (K := K) α)
    (hα : α ≠ 0)
    (h_norm :
      SemiPrimaryConjugationNormalizedPrincipalPhiHypothesis (p := p) (K := K) α) :
    ChosenPrimaryUnitFactorSymbolTrivial (p := p) (K := K) α := by
  obtain ⟨D⟩ :=
    h_norm (FLT37.IsPrimary.toIsSemiPrimary (p := p) (K := K) h_primary) hα
  exact D.symbolTrivial (p := p) (K := K) hp_odd hp_three

/-- The normalized-torsion version of U4 implies the semi-primary sign
hypothesis. The remaining mathematical work is exactly to prove this
normalization statement for the actual Gauss-sum Φ element. -/
theorem SemiPrimaryUnitFactorSignHypothesis_of_torsionNormalization
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) {α : 𝓞 K}
    (h_norm :
      SemiPrimaryUnitFactorTorsionNormalizationHypothesis (p := p) (K := K) α) :
    SemiPrimaryUnitFactorSignHypothesis (p := p) (K := K) α := by
  intro hsemi hα Φα
  obtain ⟨U, h_torsion, h_unit_semi⟩ := h_norm hsemi hα Φα
  exact ⟨U, U.isSign_of_unit_torsion_of_unit_isSemiPrimary
    (p := p) (K := K) hp_odd hp_three h_torsion h_unit_semi⟩

/-- A semi-primary sign theorem supplies the stronger project-level primary
sign theorem, because `IsPrimary` implies `IsSemiPrimary`. -/
theorem PrimaryUnitFactorSignHypothesis_of_semiPrimary
    {α : 𝓞 K}
    (h_sign : SemiPrimaryUnitFactorSignHypothesis (p := p) (K := K) α) :
    PrimaryUnitFactorSignHypothesis (p := p) (K := K) α := fun h_primary hα Φα =>
  h_sign (FLT37.IsPrimary.toIsSemiPrimary (p := p) (K := K) h_primary) hα Φα

/-- A primary sign theorem immediately gives the corrected symbol-trivial
U-chain output. -/
theorem PrimaryUnitFactorSymbolTrivial_of_signHypothesis
    (hp_odd : Odd p) {α : 𝓞 K}
    (h_primary : FLT37.IsPrimary p (K := K) α)
    (hα : α ≠ 0)
    (h_sign : PrimaryUnitFactorSignHypothesis (p := p) (K := K) α) :
    PrimaryUnitFactorSymbolTrivial (p := p) (K := K) α := by
  intro Φα
  obtain ⟨U, hU_sign⟩ := h_sign h_primary hα Φα
  exact ⟨U, U.unit_prime_symbol_zero_of_isSign (p := p) (K := K) hp_odd hU_sign⟩

/-- A chosen normalized semi-primary principal Φ-unit theorem gives the
chosen-object primary U-chain output directly. -/
theorem ChosenPrimaryUnitFactorSymbolTrivial_of_chosenNormalized
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) {α : 𝓞 K}
    (h_primary : FLT37.IsPrimary p (K := K) α)
    (hα : α ≠ 0)
    (h_norm :
      SemiPrimaryChosenNormalizedPrincipalPhiHypothesis (p := p) (K := K) α) :
    ChosenPrimaryUnitFactorSymbolTrivial (p := p) (K := K) α := by
  obtain ⟨D⟩ :=
    h_norm (FLT37.IsPrimary.toIsSemiPrimary (p := p) (K := K) h_primary) hα
  exact D.symbolTrivial (p := p) (K := K) hp_odd hp_three

/-- A uniform normalized semi-primary principal Φ-unit theorem gives the
older universal primary U-chain output directly. This is stronger than the
chosen-object classical construction because the current `PhiPrincipalElement`
API includes unit-twisted representatives. -/
theorem PrimaryUnitFactorSymbolTrivial_of_uniformNormalized
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) {α : 𝓞 K}
    (h_primary : FLT37.IsPrimary p (K := K) α)
    (hα : α ≠ 0)
    (h_norm :
      SemiPrimaryUniformNormalizedPrincipalPhiUnitHypothesis (p := p) (K := K) α) :
    PrimaryUnitFactorSymbolTrivial (p := p) (K := K) α := by
  intro Φα
  obtain ⟨D⟩ :=
    h_norm (FLT37.IsPrimary.toIsSemiPrimary (p := p) (K := K) h_primary) hα Φα
  exact D.symbolTrivial (p := p) (K := K) hp_odd hp_three

/-- A concrete `±1` unit factor supplies the corrected U-chain output for a
single principal Φ element. -/
theorem PrincipalUnitFactorData.symbolTrivial_of_isSign
    (hp_odd : Odd p)
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα)
    (hU : U.IsSign (p := p) (K := K)) :
    ∃ U' : PrincipalUnitFactorData (p := p) (K := K) α Φα,
      ∀ P : Ideal (𝓞 K),
        pthSymbolAtPrime_canonical (p := p) (K := K) U'.unit P = 0 :=
  ⟨U, U.unit_prime_symbol_zero_of_isSign (p := p) (K := K) hp_odd hU⟩

/-- U-chain data plugged into the terminal signed K-chain endpoint. -/
theorem kellyPrimeNegEquality_of_principalUnitFactorData_isSign
    (hp_odd : Odd p)
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    {P' : Ideal (𝓞 K)} [P'.IsPrime]
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα)
    (hU : U.IsSign (p := p) (K := K))
    (hP'_ne : P' ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors P'),
        PhiPrimeElement.PhiPrimeSymbolIdentity (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      -pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) :=
  kellyPrimeNegEquality_of_phi_unit_factor
    (p := p) (K := K) Φα hP'_ne hcop h_prime U.unit_isUnit
    (U.unit_prime_symbol_zero_of_isSign (p := p) (K := K) hp_odd hU)
    U.gamma_eq_unit_mul h_coprime

/-- U-chain data plugged into the terminal positive K-chain endpoint. -/
theorem kellyPrimeEquality_of_principalUnitFactorData_isSign
    (hp_odd : Odd p)
    {α : 𝓞 K}
    {Φα : PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α}
    {P' : Ideal (𝓞 K)} [P'.IsPrime]
    (U : PrincipalUnitFactorData (p := p) (K := K) α Φα)
    (hU : U.IsSign (p := p) (K := K))
    (hP'_ne : P' ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors P'),
        PhiPrimeElement.PhiPrimeSymbolIdentityPos (p := p) (K := K)
          (Φα.primePhi P hP) Q)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) :=
  kellyPrimeEquality_of_phi_unit_factor
    (p := p) (K := K) Φα hP'_ne hcop h_prime U.unit_isUnit
    (U.unit_prime_symbol_zero_of_isSign (p := p) (K := K) hp_odd hU)
    U.gamma_eq_unit_mul h_coprime

/-- Actual prime Φ-family facts plugged directly into the terminal signed
K-chain endpoint.

This is the K/U handoff in the form needed after the upstream
`K2_2SourceData` family is constructed: the prime Φ family supplies the
principal Φ product, the semi-primary and conjugation-norm facts force the
specific Φ-to-`α^Θ` unit to be a sign, and the prime Φ-symbol identities feed
the signed Kelly theorem. -/
theorem kellyPrimeNegEquality_of_primary_primePhiFamilyFacts
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
    {P' : Ideal (𝓞 K)} [P'.IsPrime]
    (hP'_ne : P' ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime_symbol :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors P'),
        PhiPrimeElement.PhiPrimeSymbolIdentity (p := p) (K := K)
          (primePhi P hP) Q)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      -pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := by
  let Φα :=
    PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors
      (p := p) (K := K) α primePhi
  have h_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (Φα.primePhi P hP).gamma := by
    intro P hP
    simpa [Φα, PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors,
      PhiPrimeElement.PhiIdealElement.ofPrimeFactors] using h_prime_semi P hP
  have h_norm :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        ringOfIntegersComplexConj K (Φα.primePhi P hP).gamma *
            (Φα.primePhi P hP).gamma =
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
    intro P hP
    simpa [Φα, PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors,
      PhiPrimeElement.PhiIdealElement.ofPrimeFactors] using h_prime_norm P hP
  have h_symbol :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors P'),
        PhiPrimeElement.PhiPrimeSymbolIdentity (p := p) (K := K)
          (Φα.primePhi P hP) Q := by
    intro P hP Q hQ
    simpa [Φα, PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors,
      PhiPrimeElement.PhiIdealElement.ofPrimeFactors] using h_prime_symbol P hP Q hQ
  obtain ⟨U, hU⟩ :=
    PrincipalUnitFactorData.exists_isSign_of_primary_primePhiFacts
      (p := p) (K := K) hp_odd hp_two hp_three hα_ne hαp_top Φα
      hα_primary h_semi h_norm
  exact kellyPrimeNegEquality_of_phi_unit_factor
    (p := p) (K := K) Φα hP'_ne hcop h_symbol U.unit_isUnit
    (U.unit_prime_symbol_zero_of_isSign
      (p := p) (K := K) ((Fact.out : Nat.Prime p).odd_of_ne_two hp_odd) hU)
    U.gamma_eq_unit_mul h_coprime

/-- Actual prime Φ-family facts plugged directly into the terminal positive
K-chain endpoint.

This is the reciprocal-orientation K/U handoff: the prime Φ family supplies
semi-primary and conjugation-norm facts exactly as in the signed endpoint, but
the prime symbol identities use `PhiPrimeSymbolIdentityPos`, so the result is
the ordinary positive concrete equality without a separate orientation
hypothesis. -/
theorem kellyPrimeEquality_of_primary_primePhiFamilyFacts
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
    {P' : Ideal (𝓞 K)} [P'.IsPrime]
    (hP'_ne : P' ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime_symbol :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors P'),
        PhiPrimeElement.PhiPrimeSymbolIdentityPos (p := p) (K := K)
          (primePhi P hP) Q)
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := by
  let Φα :=
    PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors
      (p := p) (K := K) α primePhi
  have h_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (Φα.primePhi P hP).gamma := by
    intro P hP
    simpa [Φα, PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors,
      PhiPrimeElement.PhiIdealElement.ofPrimeFactors] using h_prime_semi P hP
  have h_norm :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        ringOfIntegersComplexConj K (Φα.primePhi P hP).gamma *
            (Φα.primePhi P hP).gamma =
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
    intro P hP
    simpa [Φα, PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors,
      PhiPrimeElement.PhiIdealElement.ofPrimeFactors] using h_prime_norm P hP
  have h_symbol :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors P'),
        PhiPrimeElement.PhiPrimeSymbolIdentityPos (p := p) (K := K)
          (Φα.primePhi P hP) Q := by
    intro P hP Q hQ
    simpa [Φα, PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors,
      PhiPrimeElement.PhiIdealElement.ofPrimeFactors] using h_prime_symbol P hP Q hQ
  obtain ⟨U, hU⟩ :=
    PrincipalUnitFactorData.exists_isSign_of_primary_primePhiFacts
      (p := p) (K := K) hp_odd hp_two hp_three hα_ne hαp_top Φα
      hα_primary h_semi h_norm
  exact kellyPrimeEquality_of_phi_unit_factor
    (p := p) (K := K) Φα hP'_ne hcop h_symbol U.unit_isUnit
    (U.unit_prime_symbol_zero_of_isSign
      (p := p) (K := K) ((Fact.out : Nat.Prime p).odd_of_ne_two hp_odd) hU)
    U.gamma_eq_unit_mul h_coprime

end Furtwaengler

end BernoulliRegular

end

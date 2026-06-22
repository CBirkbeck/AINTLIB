module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.IrelandRosen.ProductSource
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor.SignUnitFactor

/-!
# Ireland--Rosen primary unit factor

This file instantiates the principal unit-factor theorem with the actual
Ireland--Rosen variable-prime product
`reciprocalPrincipalPhiElement α primePhi`.

The inputs are the concrete prime-factor semi-primary and conjugation-norm
facts for the same `primePhi` family.  No reciprocity theorem is used here.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid
open NumberField NumberField.IsCMField

namespace BernoulliRegular

namespace Furtwaengler

namespace IrelandRosen

/-- The I&R primary-unit sign lemma for the concrete variable-prime product.

For primary `α`, the actual principal Φ product differs from the explicit
Stickelberger principal generator `α^Θ` by a unit, and the prime-level
semi-primary plus conjugation-norm facts force that unit to be `±1`. -/
theorem reciprocalPrincipalPhiElement_unit_isSign
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsCMField K]
    (hp_odd : p ≠ 2) (hp_two : 2 ≤ p) (hp_three : 3 ≤ p)
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
    ∃ U : PrincipalUnitFactorData (p := p) (K := K) α
        (reciprocalPrincipalPhiElement (p := p) (K := K) α primePhi),
      U.IsSign (p := p) (K := K) := by
  let Φα := reciprocalPrincipalPhiElement (p := p) (K := K) α primePhi
  have h_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (Φα.primePhi P hP).gamma := by
    intro P hP
    simpa [Φα, reciprocalPrincipalPhiElement,
      PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors,
      PhiPrimeElement.PhiIdealElement.ofPrimeFactors] using h_prime_semi P hP
  have h_norm :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        ringOfIntegersComplexConj K (Φα.primePhi P hP).gamma *
            (Φα.primePhi P hP).gamma =
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
    intro P hP
    simpa [Φα, reciprocalPrincipalPhiElement,
      PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors,
      PhiPrimeElement.PhiIdealElement.ofPrimeFactors] using h_prime_norm P hP
  exact PrincipalUnitFactorData.exists_isSign_of_primary_primePhiFacts
    (p := p) (K := K) hp_odd hp_two hp_three hα_ne hαp_top Φα
    hα_primary h_semi h_norm

/-- The concrete unit factor from the I&R primary-unit step has trivial
prime symbols. -/
theorem reciprocalPrincipalPhiElement_unit_prime_symbol_zero
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsCMField K]
    (hp_odd : p ≠ 2) (hp_two : 2 ≤ p) (hp_three : 3 ≤ p)
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
    ∃ U : PrincipalUnitFactorData (p := p) (K := K) α
        (reciprocalPrincipalPhiElement (p := p) (K := K) α primePhi),
      U.IsSign (p := p) (K := K) ∧
        ∀ P : Ideal (𝓞 K),
          pthSymbolAtPrime_canonical (p := p) (K := K) U.unit P = 0 := by
  obtain ⟨U, hU⟩ :=
    reciprocalPrincipalPhiElement_unit_isSign
      (p := p) (K := K) hp_odd hp_two hp_three hα_ne hαp_top
      primePhi hα_primary h_prime_semi h_prime_norm
  exact ⟨U, hU,
    U.unit_prime_symbol_zero_of_isSign
      (p := p) (K := K) ((Fact.out : Nat.Prime p).odd_of_ne_two hp_odd) hU⟩

/-- The sign unit in the I&R primary-unit step contributes trivially to all
ideal-level symbols, so the concrete principal Φ product can be replaced by
the Stickelberger principal generator in the numerator. -/
theorem reciprocalPrincipalPhiElement_symbol_eq_stickelbergerPrincipalGen_symbol
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsCMField K]
    (hp_odd : p ≠ 2) (hp_two : 2 ≤ p) (hp_three : 3 ≤ p)
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
    (B : Ideal (𝓞 K)) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (reciprocalPrincipalPhiElement
          (p := p) (K := K) α primePhi).gamma B =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) B := by
  obtain ⟨U, _hU, hU_zero⟩ :=
    reciprocalPrincipalPhiElement_unit_prime_symbol_zero
      (p := p) (K := K) hp_odd hp_two hp_three hα_ne hαp_top
      primePhi hα_primary h_prime_semi h_prime_norm
  let S : 𝓞 K := stickelbergerPrincipalGen (p := p) (K := K) α
  have h_absorb :
      pthSymbolAtIdeal_canonical (p := p) (K := K) (S * U.unit) B =
        pthSymbolAtIdeal_canonical (p := p) (K := K) S B :=
    pthSymbolAtIdeal_canonical_mul_unit_α_eq_self
      (p := p) (K := K) S U.unit_isUnit hU_zero B
  calc
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (reciprocalPrincipalPhiElement
          (p := p) (K := K) α primePhi).gamma B =
        pthSymbolAtIdeal_canonical (p := p) (K := K) (S * U.unit) B := by
          rw [U.gamma_eq_unit_mul, mul_comm]
    _ = pthSymbolAtIdeal_canonical (p := p) (K := K) S B := h_absorb

end IrelandRosen

end Furtwaengler

end BernoulliRegular

end

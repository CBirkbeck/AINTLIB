module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.IrelandRosen.PrimeSource

/-!
# Ireland--Rosen variable-prime product source

This file assembles the prime source elements from `PrimeSource.lean` over the
actual normalized prime factors of the principal ideal `(α)`.

The product varies with the factor `P`; there is no fixed rational prime and
no split/order-one endpoint.  The residue-symbol theorem below takes the
prime-level equations explicitly, so it is not a renamed reciprocity target.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid
open NumberField NumberField.IsCMField

namespace BernoulliRegular

namespace Furtwaengler

namespace IrelandRosen

/-- The Ireland--Rosen principal Φ product attached to `α`.

Its factors are indexed by the actual multiset
`normalizedFactors (Ideal.span {α})`, so multiplicities in `(α)` are kept by
the multiset product. -/
noncomputable def reciprocalPrincipalPhiElement
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (α : 𝓞 K)
    (primePhi :
      ∀ P : Ideal (𝓞 K),
        P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
          PhiPrimeElement (p := p) (K := K) P) :
    PhiPrimeElement.PhiIdealElement.PhiPrincipalElement
      (p := p) (K := K) α :=
  PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors
    (p := p) (K := K) α primePhi

@[simp]
theorem reciprocalPrincipalPhiElement_gamma
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (α : 𝓞 K)
    (primePhi :
      ∀ P : Ideal (𝓞 K),
        P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
          PhiPrimeElement (p := p) (K := K) P) :
    (reciprocalPrincipalPhiElement (p := p) (K := K) α primePhi).gamma =
      ((normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))).attach.map
        fun P => (primePhi P.1 P.2).gamma).prod :=
  rfl

/-- The variable-prime principal Φ product generates `(α)^Θ`. -/
theorem reciprocalPrincipalPhiElement_span_eq_stickelbergerIdeal
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {α : 𝓞 K} (hα : α ≠ 0)
    (primePhi :
      ∀ P : Ideal (𝓞 K),
        P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
          PhiPrimeElement (p := p) (K := K) P) :
    Ideal.span
        ({(reciprocalPrincipalPhiElement
          (p := p) (K := K) α primePhi).gamma} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K)
        (Ideal.span ({α} : Set (𝓞 K))) := by
  have hA : Ideal.span ({α} : Set (𝓞 K)) ≠ ⊥ :=
    (Ideal.span_singleton_eq_bot.not).mpr hα
  exact PhiPrimeElement.PhiIdealElement.span_gamma
    (p := p) (K := K)
    (reciprocalPrincipalPhiElement (p := p) (K := K) α primePhi) hA

/-- Semi-primarity of the variable-prime principal Φ product follows from
semi-primarity of the actual prime factors. -/
theorem reciprocalPrincipalPhiElement_gamma_isSemiPrimary
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {α : 𝓞 K}
    (primePhi :
      ∀ P : Ideal (𝓞 K),
        P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
          PhiPrimeElement (p := p) (K := K) P)
    (h_prime_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (primePhi P hP).gamma) :
    FLT37.IsSemiPrimary p (K := K)
      (reciprocalPrincipalPhiElement
        (p := p) (K := K) α primePhi).gamma :=
  phiPrincipalGamma_isSemiPrimary_of_prime_semi
    (p := p) (K := K)
    (reciprocalPrincipalPhiElement (p := p) (K := K) α primePhi)
    h_prime_semi

/-- Conjugation-norm identity for the variable-prime principal Φ product,
assuming the corresponding identity for each actual prime factor. -/
theorem reciprocalPrincipalPhiElement_conj_mul_self_eq_absNorm_pow
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsCMField K]
    {α : 𝓞 K} (hα : α ≠ 0)
    (primePhi :
      ∀ P : Ideal (𝓞 K),
        P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
          PhiPrimeElement (p := p) (K := K) P)
    (h_prime_norm :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        ringOfIntegersComplexConj K (primePhi P hP).gamma *
            (primePhi P hP).gamma =
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p) :
    ringOfIntegersComplexConj K
        (reciprocalPrincipalPhiElement
          (p := p) (K := K) α primePhi).gamma *
      (reciprocalPrincipalPhiElement
        (p := p) (K := K) α primePhi).gamma =
      (((Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)) : Ideal (𝓞 K)) : ℤ) :
        𝓞 K)) ^ p :=
  phiPrincipal_conj_mul_self_eq_absNorm_pow_of_prime_conj_norm
    (p := p) (K := K) hα
    (reciprocalPrincipalPhiElement (p := p) (K := K) α primePhi)
    h_prime_norm

/-- Positive-orientation variable-prime product identity.

This is the product step in the Ireland--Rosen route: if every actual prime
factor `Φ(P)` satisfies the positive Frobenius/residue-symbol equation against
every prime factor `Q` of `B`, then the product over the actual factors of
`(α)` satisfies
`(Φ(α) / B)_p = (N B / α)_p`.

The prime input is written as the displayed equality rather than as a packaged
target proposition. -/
theorem reciprocalPrincipalPhiElement_symbol_eq_norm_principal
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {α : 𝓞 K} {B : Ideal (𝓞 K)}
    (primePhi :
      ∀ P : Ideal (𝓞 K),
        P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
          PhiPrimeElement (p := p) (K := K) P)
    (hB : B ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm B))
    (h_prime :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        Q (_hQ : Q ∈ normalizedFactors B),
        pthSymbolAtPrime_canonical (p := p) (K := K)
            (primePhi P hP).gamma Q =
          pthSymbolAtPrime_canonical (p := p) (K := K)
            (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P) :
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (reciprocalPrincipalPhiElement
          (p := p) (K := K) α primePhi).gamma B =
      pthSymbolAtPrincipal_canonical (p := p) (K := K)
        (((Ideal.absNorm B : ℤ) : 𝓞 K)) α := by
  refine PhiPrimeElement.PhiIdealElement.principal_symbol_eq_norm_principal_of_absNorm_coprime
    (p := p) (K := K)
    (reciprocalPrincipalPhiElement (p := p) (K := K) α primePhi)
    hB hcop ?_
  intro P hP Q hQ
  unfold PhiPrimeElement.PhiPrimeSymbolIdentityPos
  exact h_prime P hP Q hQ

end IrelandRosen

end Furtwaengler

end BernoulliRegular

end

module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.EisensteinReciprocityIdealNorm
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.IrelandRosen.PrimaryUnitFactor

/-!
# Ireland--Rosen ideal-norm and integer assembly

This file is the final formal assembly step from the concrete
Ireland--Rosen Φ-product facts.  It combines:

* the positive product identity for the actual variable-prime product;
* the primary unit-factor comparison with `stickelbergerPrincipalGen`;
* the denominator computation `(α / NB)_p = (α^Θ / B)_p`;
* the existing rational-integer cancellation from the ideal-norm form.

No stronger reciprocity theorem is used here.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid
open NumberField NumberField.IsCMField

namespace BernoulliRegular

namespace Furtwaengler

namespace IrelandRosen

/-- If `(NB)` is coprime to `A`, then the rational norms of `A` and `B` are
coprime.

This is the exact norm-level support condition needed by the concrete
Φ-product theorem.  It is stronger than ordinary ideal coprimality
`IsCoprime B A`, which would not rule out different primes over the same
rational prime. -/
theorem absNorm_coprime_of_idealNormPrincipal_coprime
    {K : Type*} [Field K] [NumberField K]
    {A B : Ideal (𝓞 K)}
    (hcop : IsCoprime (idealNormPrincipalIdeal (K := K) B) A) :
    (Ideal.absNorm A).Coprime (Ideal.absNorm B) := by
  by_contra hnot
  obtain ⟨ℓ, hℓ_prime, hℓA, hℓB⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hnot
  obtain ⟨P, hP_max, hP_under, hP_dvd_A⟩ :=
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hℓ_prime A hℓA
  have hA_le_P : A ≤ P := Ideal.dvd_iff_le.mp hP_dvd_A
  have hunder_abs : Ideal.absNorm (P.under ℤ) = ℓ := by
    rw [hP_under, Ideal.absNorm_span_singleton]
    simp
  have hnorm_mem : algebraMap ℤ (𝓞 K) (B.absNorm : ℤ) ∈ P := by
    change ((B.absNorm : ℤ) : 𝓞 K) ∈ P
    rw [Int.cast_mem_ideal_iff]
    rw [hunder_abs]
    exact_mod_cast hℓB
  have hnorm_le : idealNormPrincipalIdeal (K := K) B ≤ P := by
    rw [idealNormPrincipalIdeal, Ideal.span_singleton_le_iff_mem]
    exact hnorm_mem
  have htop_le : ⊤ ≤ P := by
    rw [← hcop.sup_eq]
    exact sup_le hnorm_le hA_le_P
  exact hP_max.ne_top (top_le_iff.mp htop_le)

/-- Ireland--Rosen ideal-norm reciprocity assembled from the concrete
variable-prime Φ-family facts.

The hypotheses are the actual facts produced by the direct I&R route for the
same `primePhi` family: semi-primary normalization, conjugation-norm identity,
and the positive prime-symbol identity. -/
theorem idealNormReciprocity_of_primePhiFamilyFacts
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsCMField K]
    (hp_odd : Odd p)
    {α : 𝓞 K}
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (hα_prime_to_p : IsPrimeToP (p := p) (K := K) α)
    (primePhi :
      ∀ P : Ideal (𝓞 K),
        P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
          PhiPrimeElement (p := p) (K := K) P)
    (h_prime_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (primePhi P hP).gamma)
    (h_prime_norm :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        ringOfIntegersComplexConj K (primePhi P hP).gamma *
            (primePhi P hP).gamma =
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p)
    (h_prime_symbol :
      ∀ B : Ideal (𝓞 K), IsCoprimeToPAndAlpha (p := p) (K := K) B α →
        ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
          Q (_hQ : Q ∈ normalizedFactors B),
          pthSymbolAtPrime_canonical (p := p) (K := K)
              (primePhi P hP).gamma Q =
            pthSymbolAtPrime_canonical (p := p) (K := K)
              (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P)
    (B : Ideal (𝓞 K))
    (hB : IsCoprimeToPAndAlpha (p := p) (K := K) B α) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) α
        (idealNormPrincipalIdeal (K := K) B) =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        (algebraMap ℤ (𝓞 K) (B.absNorm : ℤ))
        (Ideal.span ({α} : Set (𝓞 K))) := by
  have hp_ne_two : p ≠ 2 := by
    intro hp_eq
    rw [hp_eq] at hp_odd
    rcases hp_odd with ⟨k, hk⟩
    omega
  have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hp_three : 3 ≤ p := by omega
  have h_absNorm_coprime :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm B) :=
    absNorm_coprime_of_idealNormPrincipal_coprime
      (K := K) hB.2.2.2
  have h_den :
      pthSymbolAtIdeal_canonical (p := p) (K := K) α
          (idealNormPrincipalIdeal (K := K) B) =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) α) B :=
    pthSymbolAtIdeal_canonical_idealNormPrincipal_eq_principalGen
      (p := p) (K := K) hB.1 hB.2.2.2
  have h_unit :
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (reciprocalPrincipalPhiElement
            (p := p) (K := K) α primePhi).gamma B =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) α) B :=
    reciprocalPrincipalPhiElement_symbol_eq_stickelbergerPrincipalGen_symbol
      (p := p) (K := K) hp_ne_two hp_two hp_three hα_prime_to_p.1
      hα_prime_to_p.2 primePhi hα_primary h_prime_semi h_prime_norm B
  have h_prod :
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (reciprocalPrincipalPhiElement
            (p := p) (K := K) α primePhi).gamma B =
        pthSymbolAtPrincipal_canonical (p := p) (K := K)
          (((Ideal.absNorm B : ℤ) : 𝓞 K)) α :=
    reciprocalPrincipalPhiElement_symbol_eq_norm_principal
      (p := p) (K := K) primePhi hB.1 h_absNorm_coprime
      (h_prime_symbol B hB)
  calc
    pthSymbolAtIdeal_canonical (p := p) (K := K) α
        (idealNormPrincipalIdeal (K := K) B)
        = pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) α) B := h_den
    _ = pthSymbolAtIdeal_canonical (p := p) (K := K)
          (reciprocalPrincipalPhiElement
            (p := p) (K := K) α primePhi).gamma B := h_unit.symm
    _ = pthSymbolAtPrincipal_canonical (p := p) (K := K)
          (((Ideal.absNorm B : ℤ) : 𝓞 K)) α := h_prod
    _ = pthSymbolAtIdeal_canonical (p := p) (K := K)
          (algebraMap ℤ (𝓞 K) (B.absNorm : ℤ))
          (Ideal.span ({α} : Set (𝓞 K))) := rfl

end IrelandRosen

end Furtwaengler

end BernoulliRegular

end

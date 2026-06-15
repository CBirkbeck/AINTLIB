module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.EisensteinReciprocityBasic
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeElement

/-!
# Arbitrary-degree source data for Eisenstein reciprocity (REF-21.6b)

This file isolates the source-side facts that do not require the rational
source prime to split in `K = Q(zeta_p)`.

The central point is that the Stickelberger product is a product over all
indices `a : (ZMod p)^x`.  If the Galois orbit of a prime is not free, some
conjugate primes coincide; the formal statement below records the resulting
multiplicity as a sum over all indices that produce the same prime.

The flexible Φ-source wrappers at the end expose the existing
conductor-flexible Gauss/K2 identities without any `orderOf (ell : ZMod p) = 1`
hypothesis.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The Stickelberger multiplicity of a prime `Q` in the repeated product
`prod_a (sigma_{a^{-1}} P)^{a.val}`.

No orbit-freeness is assumed: if several indices give the same prime `Q`,
their `a.val` contributions are all added. -/
def stickelbergerRepeatedMultiplicity (P Q : Ideal (𝓞 K)) : ℕ :=
  ∑ a : CyclotomicUnitDelta p,
    if Q = cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P then
      (a : ZMod p).val
    else
      0

private theorem stickelbergerFactor_ne_zero
    {P : Ideal (𝓞 K)} [P.IsPrime] (hP_ne : P ≠ ⊥)
    (a : CyclotomicUnitDelta p) :
    (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P ^
      ((a : ZMod p).val) : Ideal (𝓞 K)) ≠ 0 := by
  rw [Ne, Ideal.zero_eq_bot]
  exact pow_ne_zero _ (cyclotomicGaloisConjugate_ne_bot a⁻¹ hP_ne)

/-- Normalized factors of one indexed Stickelberger factor, with the index
multiplicity retained. -/
theorem normalizedFactors_stickelbergerFactor_eq_repeatedSingleton
    {P : Ideal (𝓞 K)} [P.IsPrime] (hP_ne : P ≠ ⊥)
    (a : CyclotomicUnitDelta p) :
    normalizedFactors
        (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P ^
          ((a : ZMod p).val) : Ideal (𝓞 K)) =
      ((a : ZMod p).val) •
        ({cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P} :
          Multiset (Ideal (𝓞 K))) := by
  have h_ne : cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P ≠ ⊥ :=
    cyclotomicGaloisConjugate_ne_bot a⁻¹ hP_ne
  haveI : (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P).IsPrime :=
    cyclotomicGaloisConjugate_isPrime a⁻¹ P
  have h_prime :
      Prime (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P) :=
    Ideal.prime_of_isPrime h_ne inferInstance
  have h_irred :
      Irreducible (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P) :=
    h_prime.irreducible
  rw [normalizedFactors_pow, normalizedFactors_irreducible h_irred, normalize_eq]

/-- The normalized factors of `stickelbergerIdeal P` are the repeated
Stickelberger product, not a deduplicated orbit product. -/
theorem normalizedFactors_stickelbergerIdeal_eq_sum_with_repetitions
    {P : Ideal (𝓞 K)} [P.IsPrime] (hP_ne : P ≠ ⊥) :
    normalizedFactors (stickelbergerIdeal (p := p) (K := K) P) =
      ∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val) •
          ({cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P} :
            Multiset (Ideal (𝓞 K))) := by
  classical
  unfold stickelbergerIdeal
  induction (Finset.univ : Finset (CyclotomicUnitDelta p)) using
    Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.sum_empty, normalizedFactors_one]
  | insert a s has ih =>
      rw [Finset.prod_insert has, Finset.sum_insert has]
      have h_factor_ne :
          (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P ^
            ((a : ZMod p).val) : Ideal (𝓞 K)) ≠ 0 :=
        stickelbergerFactor_ne_zero (p := p) (K := K) hP_ne a
      have h_prod_ne :
          (∏ b ∈ s, cyclotomicGaloisConjugate (p := p) (K := K) b⁻¹ P ^
            ((b : ZMod p).val) : Ideal (𝓞 K)) ≠ 0 := by
        rw [Ne, Ideal.zero_eq_bot]
        refine Finset.prod_ne_zero_iff.mpr ?_
        intro b _hb
        have h := stickelbergerFactor_ne_zero (p := p) (K := K) hP_ne b
        rwa [Ne, Ideal.zero_eq_bot] at h
      rw [normalizedFactors_mul h_factor_ne h_prod_ne,
        normalizedFactors_stickelbergerFactor_eq_repeatedSingleton
          (p := p) (K := K) hP_ne a, ih]

/-- Count form of the repeated-factor Stickelberger formula.

This is the formal replacement for any split-prime/orbit-free statement:
the multiplicity of `Q` is the sum of all `a.val` for indices whose conjugate
prime equals `Q`. -/
theorem normalizedFactors_stickelbergerIdeal_count_eq_repeatedMultiplicity
    {P : Ideal (𝓞 K)} [P.IsPrime] (hP_ne : P ≠ ⊥)
    (Q : Ideal (𝓞 K)) :
    (normalizedFactors (stickelbergerIdeal (p := p) (K := K) P)).count Q =
      stickelbergerRepeatedMultiplicity (p := p) (K := K) P Q := by
  classical
  rw [normalizedFactors_stickelbergerIdeal_eq_sum_with_repetitions
    (p := p) (K := K) hP_ne]
  unfold stickelbergerRepeatedMultiplicity
  rw [Multiset.count_sum']
  refine Finset.sum_congr rfl ?_
  intro a _ha
  rw [Multiset.count_nsmul, Multiset.count_singleton]
  by_cases hQ :
      Q = cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P
  · simp [hQ]
  · simp [hQ]

/-- A repeated-exponent certificate for an actual source element `gamma`.

This is the arbitrary-degree replacement for the old orbit-faithful exact
exponent predicate.  It is intentionally indexed by the target prime `Q`, so
coincident conjugates are handled by `stickelbergerRepeatedMultiplicity`. -/
def StickelbergerRepeatedExactExponents
    (P : Ideal (𝓞 K)) (gamma : 𝓞 K) : Prop :=
  ∀ Q : Ideal (𝓞 K),
    emultiplicity Q (Ideal.span ({gamma} : Set (𝓞 K))) =
      (stickelbergerRepeatedMultiplicity (p := p) (K := K) P Q : ℕ∞)

/-- Repeated exact exponents imply the Stickelberger span factorization.

No splitness or orbit faithfulness is used; repeated conjugate primes have
already been collected in `stickelbergerRepeatedMultiplicity`. -/
theorem span_eq_stickelbergerIdeal_of_repeatedExactExponents
    {P : Ideal (𝓞 K)} [P.IsPrime] (hP_ne : P ≠ ⊥)
    {gamma : 𝓞 K} (hgamma_ne : gamma ≠ 0)
    (h_exp : StickelbergerRepeatedExactExponents (p := p) (K := K) P gamma) :
    Ideal.span ({gamma} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P := by
  classical
  have hspan_ne : Ideal.span ({gamma} : Set (𝓞 K)) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hstick_ne : stickelbergerIdeal (p := p) (K := K) P ≠ ⊥ :=
    stickelbergerIdeal_ne_bot hP_ne
  have h_dvd_left :
      Ideal.span ({gamma} : Set (𝓞 K)) ∣
        stickelbergerIdeal (p := p) (K := K) P := by
    rw [dvd_iff_normalizedFactors_le_normalizedFactors hspan_ne hstick_ne]
    rw [Multiset.le_iff_count]
    intro Q
    by_cases hQ :
        Q ∈ normalizedFactors (Ideal.span ({gamma} : Set (𝓞 K)))
    · have hQ_prime := UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ
      have hQ_irred := hQ_prime.irreducible
      have hcount_span :
          emultiplicity Q (Ideal.span ({gamma} : Set (𝓞 K))) =
            (((normalizedFactors (Ideal.span ({gamma} : Set (𝓞 K)))).count
              (normalize Q) : ℕ) : ℕ∞) :=
        emultiplicity_eq_count_normalizedFactors hQ_irred hspan_ne
      have hnorm : normalize Q = Q := by rw [normalize_eq]
      rw [hnorm] at hcount_span
      have hcount_stick :=
        normalizedFactors_stickelbergerIdeal_count_eq_repeatedMultiplicity
          (p := p) (K := K) hP_ne Q
      have h_exp_Q := h_exp Q
      rw [← hcount_stick] at h_exp_Q
      have h_eq_count :
          ((normalizedFactors (Ideal.span ({gamma} : Set (𝓞 K)))).count Q : ℕ∞) =
            (((normalizedFactors (stickelbergerIdeal (p := p) (K := K) P)).count Q) :
              ℕ∞) := by
        rw [← hcount_span]
        exact h_exp_Q
      exact_mod_cast h_eq_count.le
    · rw [Multiset.count_eq_zero.mpr hQ]
      exact Nat.zero_le _
  have h_dvd_right :
      stickelbergerIdeal (p := p) (K := K) P ∣
        Ideal.span ({gamma} : Set (𝓞 K)) := by
    rw [dvd_iff_normalizedFactors_le_normalizedFactors hstick_ne hspan_ne]
    rw [Multiset.le_iff_count]
    intro Q
    by_cases hQ :
        Q ∈ normalizedFactors (stickelbergerIdeal (p := p) (K := K) P)
    · have hQ_prime := UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ
      have hQ_irred := hQ_prime.irreducible
      have hcount_span :
          emultiplicity Q (Ideal.span ({gamma} : Set (𝓞 K))) =
            (((normalizedFactors (Ideal.span ({gamma} : Set (𝓞 K)))).count
              (normalize Q) : ℕ) : ℕ∞) :=
        emultiplicity_eq_count_normalizedFactors hQ_irred hspan_ne
      have hnorm : normalize Q = Q := by rw [normalize_eq]
      rw [hnorm] at hcount_span
      have hcount_stick :=
        normalizedFactors_stickelbergerIdeal_count_eq_repeatedMultiplicity
          (p := p) (K := K) hP_ne Q
      have h_exp_Q := h_exp Q
      rw [← hcount_stick] at h_exp_Q
      have h_eq_count :
          ((normalizedFactors (stickelbergerIdeal (p := p) (K := K) P)).count Q :
              ℕ∞) =
            ((normalizedFactors (Ideal.span ({gamma} : Set (𝓞 K)))).count Q : ℕ∞) := by
        rw [← hcount_span]
        exact h_exp_Q.symm
      exact_mod_cast h_eq_count.le
    · rw [Multiset.count_eq_zero.mpr hQ]
      exact Nat.zero_le _
  exact associated_iff_eq.mp (associated_of_dvd_dvd h_dvd_left h_dvd_right)

/-- A `PhiPrimeElement` supplies an integral, nonzero source Φ element. -/
theorem sourcePhi_ne_zero_of_arbitraryResidueDegree
    {P : Ideal (𝓞 K)} (PhiP : PhiPrimeElement (p := p) (K := K) P) :
    PhiP.gamma ≠ 0 :=
  PhiP.gamma_ne_zero

/-- A source Φ element generates the repeated Stickelberger product. -/
theorem sourcePhi_span_eq_stickelbergerIdeal_with_repetitions
    {P : Ideal (𝓞 K)} (PhiP : PhiPrimeElement (p := p) (K := K) P) :
    Ideal.span ({PhiP.gamma} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P :=
  PhiP.span_gamma

/-- Normalized-factor form of the source Φ factorization, with repetitions
made explicit. -/
theorem normalizedFactors_sourcePhi_span_eq_sum_with_repetitions
    {P : Ideal (𝓞 K)} [P.IsPrime] (hP_ne : P ≠ ⊥)
    (PhiP : PhiPrimeElement (p := p) (K := K) P) :
    normalizedFactors (Ideal.span ({PhiP.gamma} : Set (𝓞 K))) =
      ∑ a : CyclotomicUnitDelta p,
        ((a : ZMod p).val) •
          ({cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ P} :
            Multiset (Ideal (𝓞 K))) := by
  rw [PhiP.span_gamma,
    normalizedFactors_stickelbergerIdeal_eq_sum_with_repetitions
      (p := p) (K := K) hP_ne]

/-- Count form of the source Φ factorization, collecting repeated conjugates. -/
theorem normalizedFactors_sourcePhi_span_count_eq_repeatedMultiplicity
    {P : Ideal (𝓞 K)} [P.IsPrime] (hP_ne : P ≠ ⊥)
    (PhiP : PhiPrimeElement (p := p) (K := K) P)
    (Q : Ideal (𝓞 K)) :
    ((normalizedFactors (Ideal.span ({PhiP.gamma} : Set (𝓞 K)))).count Q) =
      stickelbergerRepeatedMultiplicity (p := p) (K := K) P Q := by
  rw [PhiP.span_gamma,
    normalizedFactors_stickelbergerIdeal_count_eq_repeatedMultiplicity
      (p := p) (K := K) hP_ne Q]

/-! ### Flexible Gauss-source wrappers without split/order-one hypotheses -/

/-- The conductor-flexible index-one source data gives a Φ-prime element
without any `orderOf (ell : ZMod p) = 1` hypothesis. -/
theorem sourcePhi_of_flexibleSourceData_span_eq_stickelbergerIdeal
    {ℓ : ℕ} [Fact ℓ.Prime] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : PhiPrimeElement.K2_2FlexibleSourceData (p := p) (K := K) (R' := R') S) :
    Ideal.span ({D.phi.gamma} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P :=
  D.phi.span_gamma

/-- The conductor-flexible reciprocal source data gives a Φ-prime element
without any `orderOf (ell : ZMod p) = 1` hypothesis. -/
theorem sourcePhi_of_flexibleReciprocalSourceData_span_eq_stickelbergerIdeal
    {ℓ : ℕ} [Fact ℓ.Prime] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : PhiPrimeElement.K2_2FlexibleReciprocalSourceData
      (p := p) (K := K) (R' := R') S) :
    Ideal.span ({D.phi.gamma} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P :=
  D.phi.span_gamma

/-- Flexible signed source identity.  This is the index-one orientation; it is
kept separate from the reciprocal-index identity used for Eisenstein
reciprocity. -/
theorem sourcePhi_signed_frobenius_symbol_of_flexibleSourceData
    {ℓ : ℕ} [Fact ℓ.Prime] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : PhiPrimeElement.K2_2FlexibleSourceData (p := p) (K := K) (R' := R') S)
    {Q : Ideal (𝓞 K)} [Q.IsMaximal]
    (T : PhiPrimeElement.K2_2FlexibleTargetData
      (ℓ := ℓ) (p := p) (K := K) (R' := R') Q)
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm Q)) :
    pthSymbolAtPrime_canonical (p := p) (K := K) D.phi.gamma Q =
      -pthSymbolAtPrime_canonical (p := p) (K := K)
        (algebraMap ℤ (𝓞 K) (Ideal.absNorm Q : ℤ)) P := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have h := D.symbol_eq_neg_norm_symbol T hcop
  have hN :
      Fintype.card (𝓞 K ⧸ Q) = Ideal.absNorm Q := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  simpa [hN] using h

/-- Flexible Frobenius-symbol identity in the positive orientation used by
arbitrary-degree Eisenstein reciprocity. -/
theorem sourcePhi_frobenius_symbol_of_flexibleReciprocalSourceData
    {ℓ : ℕ} [Fact ℓ.Prime] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : PhiPrimeElement.K2_2FlexibleReciprocalSourceData
      (p := p) (K := K) (R' := R') S)
    {Q : Ideal (𝓞 K)} [Q.IsMaximal]
    (T : PhiPrimeElement.K2_2FlexibleTargetData
      (ℓ := ℓ) (p := p) (K := K) (R' := R') Q)
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm Q)) :
    pthSymbolAtPrime_canonical (p := p) (K := K) D.phi.gamma Q =
      pthSymbolAtPrime_canonical (p := p) (K := K)
        (algebraMap ℤ (𝓞 K) (Ideal.absNorm Q : ℤ)) P := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have h := D.symbol_eq_norm_symbol T hcop
  have hN :
      Fintype.card (𝓞 K ⧸ Q) = Ideal.absNorm Q := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  simpa [hN] using h

end Furtwaengler

end BernoulliRegular

end

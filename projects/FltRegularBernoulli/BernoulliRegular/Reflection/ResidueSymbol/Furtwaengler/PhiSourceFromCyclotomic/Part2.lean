module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.BundleFromCyclotomic
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeElement
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor
public import Mathlib.NumberTheory.NumberField.Basic
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiSourceFromCyclotomic.Part1

/-!
# Prime Φ source data from cyclotomic split-prime bundles

This file connects the concrete cyclotomic bundle constructors from
`BundleFromCyclotomic.lean` to the corrected K2-2 source-data interface in
`PhiPrimeElement.lean`.

The constructor below is deliberately modest: it discharges the canonical
`zeta_k` and `zeta_p_int` fields from the canonical split-prime setup and
leaves the genuine arithmetic work as explicit inputs (`h_ne_zero` and
`h_span`).
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

namespace PhiPrimeElement

universe u v

/-- **Positive cyclotomic Kelly endpoint when target `P'` is prime**:
reduces the `Q ∈ normalizedFactors P'` symbol hypotheses to the single target
prime `P'`, as in the signed endpoint. -/
theorem kellyPrimeEquality_of_K2_2ReciprocalSourceDataFamily_cyclotomic_primeTarget
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (primePhi : ∀ P : Ideal (𝓞 K),
      P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
        PhiPrimeElement (p := p) (K := K) P)
    (h_prime_semi :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (primePhi P hP).gamma)
    (h_prime_norm :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        haveI : NumberField.IsCMField K :=
          IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
        NumberField.IsCMField.ringOfIntegersComplexConj K (primePhi P hP).gamma *
            (primePhi P hP).gamma =
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    {P' : Ideal (𝓞 K)} [P'.IsPrime]
    (hP'_ne : P' ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime_symbol_at_P' :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        PhiPrimeElement.PhiPrimeSymbolIdentityPos (p := p) (K := K)
          (primePhi P hP) P')
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  have hP'_irr : Irreducible P' :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mpr
      ((Ideal.isPrime_iff_bot_or_prime.mp ‹P'.IsPrime›).resolve_left hP'_ne)
  have h_factors : normalizedFactors P' = {P'} := by
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hP'_irr,
        normalize_eq]
  refine kellyPrimeEquality_of_K2_2ReciprocalSourceDataFamily_cyclotomic
    (ℓ := ℓ) (R' := R') hp_gt_two hp_three hα_ne hαp_top primePhi h_prime_semi
    h_prime_norm hα_primary hP'_ne hcop ?_ h_coprime
  intro P hP Q hQ
  rw [h_factors, Multiset.mem_singleton] at hQ
  subst hQ
  exact h_prime_symbol_at_P' P hP

/-- **Bundled positive Kelly endpoint with prime target**: folds the reciprocal
semi-primary, conjugation-norm, and positive symbol identity hypotheses into a
single per-prime conjunction. -/
theorem
    kellyPrimeEquality_of_K2_2ReciprocalSourceDataFamily_cyclotomic_primeTarget_bundled
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (primePhi : ∀ P : Ideal (𝓞 K),
      P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
        PhiPrimeElement (p := p) (K := K) P)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    {P' : Ideal (𝓞 K)} [P'.IsPrime]
    (hP'_ne : P' ≠ ⊥)
    (hcop :
      (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
        (Ideal.absNorm P'))
    (h_prime_facts :
      ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        haveI : NumberField.IsCMField K :=
          IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
        FLT37.IsSemiPrimary p (K := K) (primePhi P hP).gamma ∧
          NumberField.IsCMField.ringOfIntegersComplexConj K (primePhi P hP).gamma *
              (primePhi P hP).gamma =
            (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p ∧
          PhiPrimeSymbolIdentityPos (p := p) (K := K)
            (primePhi P hP) P')
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) :=
  kellyPrimeEquality_of_K2_2ReciprocalSourceDataFamily_cyclotomic_primeTarget
    (ℓ := ℓ) (R' := R') hp_gt_two hp_three hα_ne hαp_top primePhi
    (fun P hP => (h_prime_facts P hP).1)
    (fun P hP => (h_prime_facts P hP).2.1)
    hα_primary hP'_ne hcop
    (fun P hP => (h_prime_facts P hP).2.2)
    h_coprime

/-- **`h_span` discharge from atomic Stickelberger predicates (split case).**

Reduces the substantive `K2_2SourceData.h_span` field to:
* `StickelbergerExactConjugateExponents (phiPrimeGenDescent S 1 ...)` — the
  per-conjugate emultiplicity statement for the descended Gauss-sum element;
* totally-split ramification `e = 1, f = 1` of `S.descentPrime` over its
  rational prime;
* an equality `S.descentPrime = P` identifying the bundle's descent prime.

The support-in-orbit predicate is automatic from the descent property
(`stickelbergerSupportInOrbit_of_descentGaussSum`); the structural
`StickelbergerIdealConjugateMultiplicity` is automatic from orbit
faithfulness in the split case
(`stickelbergerIdealConjugateMultiplicity_of_orbitFaithful`); the
span-equality reduction goes through `span_eq_stickelbergerIdeal_of_atomic`.

The remaining open content is exactly the per-conjugate exact-exponent
predicate `StickelbergerExactConjugateExponents` for the descended γ —
the substantive Stickelberger order statement for Gauss sums. -/
theorem K2_2SourceData_h_span_of_atomic_split
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (h_descentPrime :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.toConcreteStickelbergerSetup.descentPrime = P)
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt 1 ^ p ≠ 0)
    (h_exp :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.StickelbergerExactConjugateExponents
        (phiPrimeGenDescent S (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero))
    (he :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).ramificationIdxIn (𝓞 K) = 1)
    (hf :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).inertiaDegIn (𝓞 K) = 1) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    Ideal.span ({phiPrimeGenDescent S
      (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  set γ := phiPrimeGenDescent S (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero
  have hγ_ne : γ ≠ 0 :=
    phiPrimeGenDescent_ne_zero S (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero
  have hγ_alg : algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt 1 ^ p :=
    algebraMap_phiPrimeGenDescent S (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero
  have h_sup : S.StickelbergerSupportInOrbit γ :=
    S.stickelbergerSupportInOrbit_of_descentGaussSum
      (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) hγ_ne hγ_alg
  have h_faithful : S.StickelbergerOrbitFaithful :=
    S.stickelbergerOrbitFaithful_of_split he hf
  have h_stickMul : S.StickelbergerIdealConjugateMultiplicity :=
    S.stickelbergerIdealConjugateMultiplicity_of_orbitFaithful h_faithful
  have h_eq := S.span_eq_stickelbergerIdeal_of_atomic hγ_ne h_exp h_sup h_stickMul
  rw [h_descentPrime] at h_eq
  exact h_eq

/-- **Reciprocal `h_span` discharge from atomic Stickelberger predicates
(split case).**

This is the reciprocal-index analogue of `K2_2SourceData_h_span_of_atomic_split`.
The descended element is the actual Gauss-sum
`phiPrimeGenDescent S (p - 1)`, matching the no-sorry REF-18 exact-exponent
theorem proved from pair-field covariance. -/
theorem K2_2ReciprocalSourceData_h_span_of_atomic_split
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (h_descentPrime :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.toConcreteStickelbergerSetup.descentPrime = P)
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt (p - 1) ^ p ≠ 0)
    (h_exp :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.StickelbergerExactConjugateExponents
        (phiPrimeGenDescent S
          (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero))
    (he :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).ramificationIdxIn (𝓞 K) = 1)
    (hf :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).inertiaDegIn (𝓞 K) = 1) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    Ideal.span ({phiPrimeGenDescent S
      (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero} :
        Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  set γ := phiPrimeGenDescent S
    (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero
  have hγ_ne : γ ≠ 0 :=
    phiPrimeGenDescent_ne_zero S
      (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero
  have hγ_alg : algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt (p - 1) ^ p :=
    algebraMap_phiPrimeGenDescent S
      (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero
  have h_sup : S.StickelbergerSupportInOrbit γ :=
    S.stickelbergerSupportInOrbit_of_descentGaussSum
      (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) hγ_ne hγ_alg
  have h_faithful : S.StickelbergerOrbitFaithful :=
    S.stickelbergerOrbitFaithful_of_split he hf
  have h_stickMul : S.StickelbergerIdealConjugateMultiplicity :=
    S.stickelbergerIdealConjugateMultiplicity_of_orbitFaithful h_faithful
  have h_eq := S.span_eq_stickelbergerIdeal_of_atomic hγ_ne h_exp h_sup h_stickMul
  rw [h_descentPrime] at h_eq
  exact h_eq

/-- The canonical compatible trace-form constructor has descent prime `P`.

This removes a bookkeeping hypothesis from source-data constructors: once
`S.toTraceFormStickelbergerSetup` is the canonical split-prime trace-form
bundle, the descent prime is forced by the K-algebra-compatible residue-field
iso. -/
theorem descentPrime_eq_of_canonicalTraceForm
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (hP_ne_bot : P ≠ ⊥)
    (hℓ_ne_p : ℓ ≠ p)
    {Q : Ideal (𝓞 R')} [Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    {iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P)}
    (h_compat :
      CyclotomicLocalSetup.IsKAlgebraCompatibleSplittingIso (K₀ := K) Q P iso)
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (h_trace :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.toTraceFormStickelbergerSetup =
        CyclotomicLocalSetup.mkTraceForm_ofSplitPrime_canonical_compat
          (K := K) (R' := R') p ℓ P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
          Q hQ_in iso h_compat) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    S.toConcreteStickelbergerSetup.descentPrime = P := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  have h_concrete :
      S.toConcreteStickelbergerSetup =
        CyclotomicLocalSetup.mkConcreteSetup_ofSplitPrime_canonical_compat
          (K := K) (R' := R') p ℓ P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
          Q hQ_in iso h_compat := by
    calc
      S.toConcreteStickelbergerSetup =
          S.toTraceFormStickelbergerSetup.toConcreteStickelbergerSetup := rfl
      _ =
          (CyclotomicLocalSetup.mkTraceForm_ofSplitPrime_canonical_compat
            (K := K) (R' := R') p ℓ P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
            Q hQ_in iso h_compat).toConcreteStickelbergerSetup := by
        rw [h_trace]
      _ =
          CyclotomicLocalSetup.mkConcreteSetup_ofSplitPrime_canonical_compat
            (K := K) (R' := R') p ℓ P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
            Q hQ_in iso h_compat := by
        simp
  rw [h_concrete]
  exact CyclotomicLocalSetup.mkConcreteSetup_ofSplitPrime_canonical_compat_descentPrime
    (K := K) (R' := R') p ℓ P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
    Q hQ_in iso h_compat

/-- In the canonical split-prime trace-form bundle, the abstract residue
degree `S.f` is the inertia degree of the source prime over `(ℓ)`. -/
theorem f_eq_inertiaDeg_of_canonicalTraceForm
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (hP_ne_bot : P ≠ ⊥)
    (hℓ_ne_p : ℓ ≠ p)
    {Q : Ideal (𝓞 R')} [Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    {iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P)}
    (h_compat :
      CyclotomicLocalSetup.IsKAlgebraCompatibleSplittingIso (K₀ := K) Q P iso)
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (h_trace :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.toTraceFormStickelbergerSetup =
        CyclotomicLocalSetup.mkTraceForm_ofSplitPrime_canonical_compat
          (K := K) (R' := R') p ℓ P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
          Q hQ_in iso h_compat) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    S.f = (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).inertiaDeg P := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  have h_concrete :
      S.toConcreteStickelbergerSetup =
        CyclotomicLocalSetup.mkConcreteSetup_ofSplitPrime_canonical_compat
          (K := K) (R' := R') p ℓ P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
          Q hQ_in iso h_compat := by
    calc
      S.toConcreteStickelbergerSetup =
          S.toTraceFormStickelbergerSetup.toConcreteStickelbergerSetup := rfl
      _ =
          (CyclotomicLocalSetup.mkTraceForm_ofSplitPrime_canonical_compat
            (K := K) (R' := R') p ℓ P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
            Q hQ_in iso h_compat).toConcreteStickelbergerSetup := by
        rw [h_trace]
      _ =
          CyclotomicLocalSetup.mkConcreteSetup_ofSplitPrime_canonical_compat
            (K := K) (R' := R') p ℓ P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
            Q hQ_in iso h_compat := by
        simp
  change S.toConcreteStickelbergerSetup.f =
    (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).inertiaDeg P
  rw [h_concrete]
  unfold CyclotomicLocalSetup.mkConcreteSetup_ofSplitPrime_canonical_compat
    CyclotomicLocalSetup.mkConcreteSetup_ofSplitPrime_canonical
    CyclotomicLocalSetup.mkConcreteSetup_ofSplitPrime
  rfl

/-- In the canonical split-prime trace-form bundle, rational splitting of
`(ℓ)` forces the concrete residue degree field `S.f` to be one. -/
theorem f_eq_one_of_canonicalTraceForm_atSpan
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (hP_ne_bot : P ≠ ⊥)
    (hℓ_ne_p : ℓ ≠ p)
    {Q : Ideal (𝓞 R')} [Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    {iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P)}
    (h_compat :
      CyclotomicLocalSetup.IsKAlgebraCompatibleSplittingIso (K₀ := K) Q P iso)
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (h_trace :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.toTraceFormStickelbergerSetup =
        CyclotomicLocalSetup.mkTraceForm_ofSplitPrime_canonical_compat
          (K := K) (R' := R') p ℓ P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
          Q hQ_in iso h_compat)
    (hf :
      (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).inertiaDegIn (𝓞 K) = 1) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    S.f = 1 := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  have hf_S :
      S.f = (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).inertiaDeg P :=
    f_eq_inertiaDeg_of_canonicalTraceForm
      (K := K) (R' := R') hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
      hQ_in h_compat h_trace
  have h_under :
      P.under ℤ = Ideal.span ({(ℓ : ℤ)} : Set ℤ) :=
    CyclotomicLocalSetup.under_eq_span_of_natCast_mem
      (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  letI : P.LiesOver (Ideal.span ({(ℓ : ℤ)} : Set ℤ)) := ⟨h_under.symm⟩
  haveI : P.IsPrime := (show P.IsMaximal from inferInstance).isPrime
  have _ : IsGaloisGroup Gal(K/ℚ) ℤ (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (Gal(K/ℚ)) ℤ (𝓞 K) ℚ K
  have hf_P :
      (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).inertiaDeg P = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg
      (p := Ideal.span ({(ℓ : ℤ)} : Set ℤ)) (P := P) (G := Gal(K/ℚ))]
    exact hf
  exact hf_S.trans hf_P

/-- **Actual K2-2 source data from the canonical trace-form split bundle
and the exact-exponent theorem.**

This is the honest source constructor for the current K/U route.  The produced
`D.phi.gamma` is the descended Gauss-sum element
`phiPrimeGenDescent S 1 ...`, because the `h_span` field is discharged by
`K2_2SourceData_h_span_of_atomic_split` for that same element.  No
`StickelbergerIdealEquality.gen` choice is introduced. -/
noncomputable def K2_2SourceData.ofCanonicalTraceForm_atomic_split
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (hP_ne_bot : P ≠ ⊥)
    (hℓ_ne_p : ℓ ≠ p)
    {Q : Ideal (𝓞 R')} [Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    {iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P)}
    (h_compat :
      CyclotomicLocalSetup.IsKAlgebraCompatibleSplittingIso (K₀ := K) Q P iso)
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (h_trace :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.toTraceFormStickelbergerSetup =
        CyclotomicLocalSetup.mkTraceForm_ofSplitPrime_canonical_compat
          (K := K) (R' := R') p ℓ P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
          Q hQ_in iso h_compat)
    (h_descentPrime :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.toConcreteStickelbergerSetup.descentPrime = P)
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.gaussSumInt 1 ^ p ≠ 0)
    (h_exp :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.StickelbergerExactConjugateExponents
        (phiPrimeGenDescent S
          (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero))
    (he :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).ramificationIdxIn (𝓞 K) = 1)
    (hf :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).inertiaDegIn (𝓞 K) = 1) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    K2_2SourceData S := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  refine K2_2SourceData.ofCanonicalTraceForm
    (P := P) (Q := Q) (iso := iso)
    hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p hQ_in h_compat h_trace
    h_ne_zero ?_
  exact K2_2SourceData_h_span_of_atomic_split
    (P := P) h_descentPrime h_ne_zero h_exp he hf

/-- Variant of `K2_2SourceData.ofCanonicalTraceForm_atomic_split` that derives
the descent-prime equality from the canonical trace-form identity and accepts
the split conditions directly for `P`. -/
noncomputable def K2_2SourceData.ofCanonicalTraceForm_atomic_split_atPrime
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (hP_ne_bot : P ≠ ⊥)
    (hℓ_ne_p : ℓ ≠ p)
    {Q : Ideal (𝓞 R')} [Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    {iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P)}
    (h_compat :
      CyclotomicLocalSetup.IsKAlgebraCompatibleSplittingIso (K₀ := K) Q P iso)
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (h_trace :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.toTraceFormStickelbergerSetup =
        CyclotomicLocalSetup.mkTraceForm_ofSplitPrime_canonical_compat
          (K := K) (R' := R') p ℓ P hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
          Q hQ_in iso h_compat)
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.gaussSumInt 1 ^ p ≠ 0)
    (h_exp :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.StickelbergerExactConjugateExponents
        (phiPrimeGenDescent S
          (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero))
    (he :
      (P.under ℤ).ramificationIdxIn (𝓞 K) = 1)
    (hf :
      (P.under ℤ).inertiaDegIn (𝓞 K) = 1) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    K2_2SourceData S := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  have h_descentPrime :
      S.toConcreteStickelbergerSetup.descentPrime = P :=
    descentPrime_eq_of_canonicalTraceForm
      (K := K) (R' := R') hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
      hQ_in h_compat h_trace
  refine K2_2SourceData.ofCanonicalTraceForm_atomic_split
    (P := P) (Q := Q) (iso := iso)
    hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p hQ_in h_compat h_trace
    h_descentPrime h_ne_zero h_exp ?_ ?_
  · rw [h_descentPrime]
    exact he
  · rw [h_descentPrime]
    exact hf

/-- Variant of `K2_2SourceData.ofCanonicalTraceForm_atomic_split_atPrime` that
derives `ℓ ≠ p` from `(ℓ : 𝓞 K) ∈ P` and `(p : 𝓞 K) ∉ P`. -/
noncomputable def K2_2SourceData.ofCanonicalTraceForm_atomic_split_atPrime_of_mem_notMem
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (hP_ne_bot : P ≠ ⊥)
    {Q : Ideal (𝓞 R')} [Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    {iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P)}
    (h_compat :
      CyclotomicLocalSetup.IsKAlgebraCompatibleSplittingIso (K₀ := K) Q P iso)
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (h_trace :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.toTraceFormStickelbergerSetup =
        CyclotomicLocalSetup.mkTraceForm_ofSplitPrime_canonical_compat
          (K := K) (R' := R') p ℓ P hℓ_in_P hp_notin_P hP_ne_bot
          (natCast_ne_of_mem_notMem_ideal hℓ_in_P hp_notin_P)
          Q hQ_in iso h_compat)
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.gaussSumInt 1 ^ p ≠ 0)
    (h_exp :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.StickelbergerExactConjugateExponents
        (phiPrimeGenDescent S
          (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero))
    (he :
      (P.under ℤ).ramificationIdxIn (𝓞 K) = 1)
    (hf :
      (P.under ℤ).inertiaDegIn (𝓞 K) = 1) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    K2_2SourceData S :=
  K2_2SourceData.ofCanonicalTraceForm_atomic_split_atPrime
    (P := P) (Q := Q) (iso := iso)
    hℓ_in_P hp_notin_P hP_ne_bot
    (natCast_ne_of_mem_notMem_ideal hℓ_in_P hp_notin_P)
    hQ_in h_compat h_trace h_ne_zero h_exp he hf

/-- Variant of
`K2_2SourceData.ofCanonicalTraceForm_atomic_split_atPrime_of_mem_notMem`
that also derives `P ≠ ⊥` from maximality of the source prime. -/
noncomputable def K2_2SourceData.ofCanonicalTraceForm_atomic_split_atPrime_of_mem_notMem_maximal
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    {Q : Ideal (𝓞 R')} [Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    {iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P)}
    (h_compat :
      CyclotomicLocalSetup.IsKAlgebraCompatibleSplittingIso (K₀ := K) Q P iso)
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (h_trace :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.toTraceFormStickelbergerSetup =
        CyclotomicLocalSetup.mkTraceForm_ofSplitPrime_canonical_compat
          (K := K) (R' := R') p ℓ P hℓ_in_P hp_notin_P
          (ringOfIntegers_maximal_ne_bot (K := K) (P := P))
          (natCast_ne_of_mem_notMem_ideal hℓ_in_P hp_notin_P)
          Q hQ_in iso h_compat)
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.gaussSumInt 1 ^ p ≠ 0)
    (h_exp :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.StickelbergerExactConjugateExponents
        (phiPrimeGenDescent S
          (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero))
    (he :
      (P.under ℤ).ramificationIdxIn (𝓞 K) = 1)
    (hf :
      (P.under ℤ).inertiaDegIn (𝓞 K) = 1) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    K2_2SourceData S :=
  K2_2SourceData.ofCanonicalTraceForm_atomic_split_atPrime_of_mem_notMem
    (P := P) (Q := Q) (iso := iso)
    hℓ_in_P hp_notin_P
    (ringOfIntegers_maximal_ne_bot (K := K) (P := P))
    hQ_in h_compat h_trace h_ne_zero h_exp he hf

/-- Variant of
`K2_2SourceData.ofCanonicalTraceForm_atomic_split_atPrime_of_mem_notMem_maximal`
that accepts splitting of the rational prime ideal `(ℓ)` instead of splitting
written on `P.under ℤ`. -/
noncomputable def K2_2SourceData.ofCanonicalTraceForm_atomic_split_atSpan_of_mem_notMem_maximal
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    {Q : Ideal (𝓞 R')} [Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    {iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P)}
    (h_compat :
      CyclotomicLocalSetup.IsKAlgebraCompatibleSplittingIso (K₀ := K) Q P iso)
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (h_trace :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.toTraceFormStickelbergerSetup =
        CyclotomicLocalSetup.mkTraceForm_ofSplitPrime_canonical_compat
          (K := K) (R' := R') p ℓ P hℓ_in_P hp_notin_P
          (ringOfIntegers_maximal_ne_bot (K := K) (P := P))
          (natCast_ne_of_mem_notMem_ideal hℓ_in_P hp_notin_P)
          Q hQ_in iso h_compat)
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.gaussSumInt 1 ^ p ≠ 0)
    (h_exp :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.StickelbergerExactConjugateExponents
        (phiPrimeGenDescent S
          (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero))
    (he :
      (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).ramificationIdxIn (𝓞 K) = 1)
    (hf :
      (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).inertiaDegIn (𝓞 K) = 1) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    K2_2SourceData S := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  have h_under :
      P.under ℤ = Ideal.span ({(ℓ : ℤ)} : Set ℤ) :=
    CyclotomicLocalSetup.under_eq_span_of_natCast_mem
      (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  refine
    K2_2SourceData.ofCanonicalTraceForm_atomic_split_atPrime_of_mem_notMem_maximal
      (P := P) (Q := Q) (iso := iso)
      hℓ_in_P hp_notin_P hQ_in h_compat h_trace h_ne_zero h_exp ?_ ?_
  · simpa [h_under] using he
  · simpa [h_under] using hf

/-- Variant of
`K2_2SourceData.ofCanonicalTraceForm_atomic_split_atSpan_of_mem_notMem_maximal`
that derives the rational-prime split equalities from the cyclotomic
ramification theorem and the honest order-one condition for `ℓ` modulo `p`. -/
noncomputable def K2_2SourceData.ofCanonicalTraceForm_atomic_split_orderOfOne_of_mem_notMem_maximal
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    {Q : Ideal (𝓞 R')} [Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    {iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P)}
    (h_compat :
      CyclotomicLocalSetup.IsKAlgebraCompatibleSplittingIso (K₀ := K) Q P iso)
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (h_trace :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.toTraceFormStickelbergerSetup =
        CyclotomicLocalSetup.mkTraceForm_ofSplitPrime_canonical_compat
          (K := K) (R' := R') p ℓ P hℓ_in_P hp_notin_P
          (ringOfIntegers_maximal_ne_bot (K := K) (P := P))
          (natCast_ne_of_mem_notMem_ideal hℓ_in_P hp_notin_P)
          Q hQ_in iso h_compat)
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.gaussSumInt 1 ^ p ≠ 0)
    (h_exp :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.StickelbergerExactConjugateExponents
        (phiPrimeGenDescent S
          (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero))
    (h_order : orderOf (ℓ : ZMod p) = 1) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    K2_2SourceData S := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  have hℓ_ne_p : ℓ ≠ p := natCast_ne_of_mem_notMem_ideal hℓ_in_P hp_notin_P
  exact
    K2_2SourceData.ofCanonicalTraceForm_atomic_split_atSpan_of_mem_notMem_maximal
      (P := P) (Q := Q) (iso := iso)
      hℓ_in_P hp_notin_P hQ_in h_compat h_trace h_ne_zero h_exp
      (ramificationIdxIn_span_natCast_eq_one_of_ne (K := K) hℓ_ne_p)
      (inertiaDegIn_span_natCast_eq_one_of_orderOf (K := K) hℓ_ne_p h_order)

end PhiPrimeElement

end Furtwaengler

end BernoulliRegular

end

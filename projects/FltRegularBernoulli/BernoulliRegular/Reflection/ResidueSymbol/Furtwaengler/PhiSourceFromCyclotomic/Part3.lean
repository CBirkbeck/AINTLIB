module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.BundleFromCyclotomic
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeElement
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor
public import Mathlib.NumberTheory.NumberField.Basic
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiSourceFromCyclotomic.Part2

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

/-- Source-data constructor for a normalized source factor of `(α)`.

This is the caller-facing version for source primes coming from
`normalizedFactors (Ideal.span {α})`: maximality of `P` is derived from
`α ≠ 0` and normalized-factor membership. -/
noncomputable def K2_2SourceData.ofCanonicalTraceForm_orderOfOne_normalizedFactor
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    {P : Ideal (𝓞 K)}
    (hP_factor : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    {Q : Ideal (𝓞 R')} [Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    {iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P)}
    (h_compat :
      CyclotomicLocalSetup.IsKAlgebraCompatibleSplittingIso (K₀ := K) Q P iso)
    {S : letI : P.IsMaximal :=
        normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (h_trace :
      letI : P.IsMaximal :=
        normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
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
      letI : P.IsMaximal :=
        normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.gaussSumInt 1 ^ p ≠ 0)
    (h_exp :
      letI : P.IsMaximal :=
        normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.StickelbergerExactConjugateExponents
        (phiPrimeGenDescent S
          (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero))
    (h_order : orderOf (ℓ : ZMod p) = 1) :
    letI : P.IsMaximal :=
      normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    K2_2SourceData S := by
  letI : P.IsMaximal :=
    normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  exact
    K2_2SourceData.ofCanonicalTraceForm_atomic_split_orderOfOne_of_mem_notMem_maximal
      (P := P) (Q := Q) (iso := iso)
      hℓ_in_P hp_notin_P hQ_in h_compat h_trace h_ne_zero h_exp h_order

/-- Source-data constructor for a normalized source factor of `(α)` that
derives `(p : 𝓞 K) ∉ P` from `(α, p) = ⊤`. -/
noncomputable def
    K2_2SourceData.ofCanonicalTraceForm_orderOfOne_normalizedFactor_pairTop
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    {P : Ideal (𝓞 K)}
    (hP_factor : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    {Q : Ideal (𝓞 R')} [Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    {iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P)}
    (h_compat :
      CyclotomicLocalSetup.IsKAlgebraCompatibleSplittingIso (K₀ := K) Q P iso)
    {S : letI : P.IsMaximal :=
        normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (h_trace :
      letI : P.IsMaximal :=
        normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.toTraceFormStickelbergerSetup =
        CyclotomicLocalSetup.mkTraceForm_ofSplitPrime_canonical_compat
          (K := K) (R' := R') p ℓ P hℓ_in_P
          (natCast_notMem_of_normalizedFactor_span_pair_eq_top
            (K := K) hα_ne hαp_top hP_factor)
          (ringOfIntegers_maximal_ne_bot (K := K) (P := P))
          (natCast_ne_of_mem_notMem_ideal hℓ_in_P
            (natCast_notMem_of_normalizedFactor_span_pair_eq_top
              (K := K) hα_ne hαp_top hP_factor))
          Q hQ_in iso h_compat)
    (h_ne_zero :
      letI : P.IsMaximal :=
        normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.gaussSumInt 1 ^ p ≠ 0)
    (h_exp :
      letI : P.IsMaximal :=
        normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.StickelbergerExactConjugateExponents
        (phiPrimeGenDescent S
          (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero))
    (h_order : orderOf (ℓ : ZMod p) = 1) :
    letI : P.IsMaximal :=
      normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    K2_2SourceData S := by
  letI : P.IsMaximal :=
    normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  exact
    K2_2SourceData.ofCanonicalTraceForm_orderOfOne_normalizedFactor
      (P := P) (Q := Q) (iso := iso)
      hα_ne hP_factor hℓ_in_P
      (natCast_notMem_of_normalizedFactor_span_pair_eq_top
        (K := K) hα_ne hαp_top hP_factor)
      hQ_in h_compat h_trace h_ne_zero h_exp h_order

/-- Source-data constructor for a normalized source factor of `(α)` that
derives `(p : 𝓞 K) ∉ P` from `(α, p) = ⊤` and derives the index-one Gauss-sum
nonvanishing from Dwork exact order. -/
noncomputable def
    K2_2SourceData.ofCanonicalTraceForm_orderOfOne_normalizedFactor_pairTop_dworkNeZero
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    {P : Ideal (𝓞 K)}
    (hP_factor : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    {Q : Ideal (𝓞 R')} [Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    {iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P)}
    (h_compat :
      CyclotomicLocalSetup.IsKAlgebraCompatibleSplittingIso (K₀ := K) Q P iso)
    {S : letI : P.IsMaximal :=
        normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (h_trace :
      letI : P.IsMaximal :=
        normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.toTraceFormStickelbergerSetup =
        CyclotomicLocalSetup.mkTraceForm_ofSplitPrime_canonical_compat
          (K := K) (R' := R') p ℓ P hℓ_in_P
          (natCast_notMem_of_normalizedFactor_span_pair_eq_top
            (K := K) hα_ne hαp_top hP_factor)
          (ringOfIntegers_maximal_ne_bot (K := K) (P := P))
          (natCast_ne_of_mem_notMem_ideal hℓ_in_P
            (natCast_notMem_of_normalizedFactor_span_pair_eq_top
              (K := K) hα_ne hαp_top hP_factor))
          Q hQ_in iso h_compat)
    (h_exp :
      letI : P.IsMaximal :=
        normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.StickelbergerExactConjugateExponents
        (phiPrimeGenDescent S
          (le_refl 1) (one_le_p_sub_one_of_prime (p := p))
          (gaussSumInt_pow_p_ne_zero_of_dwork S
            (le_refl 1) (one_le_p_sub_one_of_prime (p := p)))))
    (h_order : orderOf (ℓ : ZMod p) = 1) :
    letI : P.IsMaximal :=
      normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    K2_2SourceData S := by
  letI : P.IsMaximal :=
    normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  exact
    K2_2SourceData.ofCanonicalTraceForm_orderOfOne_normalizedFactor_pairTop
      (P := P) (Q := Q) (iso := iso)
      hα_ne hαp_top hP_factor hℓ_in_P hQ_in h_compat h_trace
      (gaussSumInt_pow_p_ne_zero_of_dwork S
        (le_refl 1) (one_le_p_sub_one_of_prime (p := p)))
      h_exp h_order

/-- **Reciprocal actual K2-2 source data from the canonical trace-form split
bundle and the pair-field exact-exponent theorem.**

This constructor is the first caller-facing bridge from the no-sorry
reciprocal exact-exponent theorem to a usable K2-2 source object. It produces
`D.phi.gamma = phiPrimeGenDescent S (p - 1) ...` and discharges the
Stickelberger span field by the atomic split theorem for that same element. -/
noncomputable def K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
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
    K2_2ReciprocalSourceData S := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  have h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0 := by
    have h_not :=
      (S.gaussSumInt_qadic_ord_at_prime_ord_dwork
        (p - 1) (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1))).2
    exact S.toConcreteStickelbergerSetup.gaussSumInt_pow_p_ne_zero_of_ne_zero
      (S.toConcreteStickelbergerSetup.gaussSumInt_ne_zero_of_not_mem_Q_pow_succ
        (a := p - 1) (d := S.stickOrdOrd (p - 1)) h_not)
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
  have hf_at_P :
      (P.under ℤ).inertiaDegIn (𝓞 K) = 1 := by
    rw [← h_descentPrime]
    exact hf
  have h_under :
      P.under ℤ = Ideal.span ({(ℓ : ℤ)} : Set ℤ) :=
    CyclotomicLocalSetup.under_eq_span_of_natCast_mem
      (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  have hf_span :
      (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).inertiaDegIn (𝓞 K) = 1 := by
    simpa [h_under] using hf_at_P
  have hS_f : S.f = 1 :=
    f_eq_one_of_canonicalTraceForm_atSpan
      (K := K) (R' := R') hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
      hQ_in h_compat h_trace hf_span
  have h_exp :
      S.StickelbergerExactConjugateExponents
        (phiPrimeGenDescent S
          (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero) :=
    StickelbergerExactConjugateExponents_phiPrimeGenDescent_sub_one_of_pairSigma_split
      (K := K) (R' := R') S hS_f he h_ne_zero
  refine
    { hP_bot := hP_ne_bot
      hℓ_in_P := hℓ_in_P
      hp_notin_P := hp_notin_P
      h_zeta_k_eq := ?_
      h_zeta_p_int_eq := ?_
      h_ne_zero := h_ne_zero
      h_span := ?_ }
  · rw [h_concrete]
    simp [CyclotomicLocalSetup.mkConcreteSetup_ofSplitPrime_canonical_compat,
      CyclotomicLocalSetup.mkConcreteSetup_ofSplitPrime_canonical]
  · rw [h_concrete]
    simp [CyclotomicLocalSetup.mkConcreteSetup_ofSplitPrime_canonical_compat,
      CyclotomicLocalSetup.mkConcreteSetup_ofSplitPrime_canonical,
      CyclotomicLocalSetup.canonical_zeta_p_int]
  · exact K2_2ReciprocalSourceData_h_span_of_atomic_split
      (P := P) h_descentPrime h_ne_zero h_exp he hf

/-- Variant of `K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split`
that derives the descent-prime equality from the canonical trace-form identity
and accepts split conditions directly for `P`. -/
noncomputable def K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split_atPrime
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
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
    (he :
      (P.under ℤ).ramificationIdxIn (𝓞 K) = 1)
    (hf :
      (P.under ℤ).inertiaDegIn (𝓞 K) = 1) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    K2_2ReciprocalSourceData S := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  have h_descentPrime :
      S.toConcreteStickelbergerSetup.descentPrime = P :=
    descentPrime_eq_of_canonicalTraceForm
      (K := K) (R' := R') hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
      hQ_in h_compat h_trace
  refine K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split
    (P := P) (Q := Q) (iso := iso)
    hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p hQ_in h_compat h_trace
    h_descentPrime ?_ ?_
  · rw [h_descentPrime]
    exact he
  · rw [h_descentPrime]
    exact hf

/-- Variant of
`K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split_atPrime` that
derives `ℓ ≠ p` from `(ℓ : 𝓞 K) ∈ P` and `(p : 𝓞 K) ∉ P`. -/
noncomputable def
    K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split_atPrime_of_mem_notMem
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
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
    (he :
      (P.under ℤ).ramificationIdxIn (𝓞 K) = 1)
    (hf :
      (P.under ℤ).inertiaDegIn (𝓞 K) = 1) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    K2_2ReciprocalSourceData S :=
  K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split_atPrime
    (P := P) (Q := Q) (iso := iso)
    hℓ_in_P hp_notin_P hP_ne_bot
    (natCast_ne_of_mem_notMem_ideal hℓ_in_P hp_notin_P)
    hQ_in h_compat h_trace he hf

/-- Variant of
`K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split_atPrime_of_mem_notMem`
that also derives `P ≠ ⊥` from maximality of the source prime. -/
noncomputable def
    K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split_atPrime_of_mem_notMem_maximal
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
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
    (he :
      (P.under ℤ).ramificationIdxIn (𝓞 K) = 1)
    (hf :
      (P.under ℤ).inertiaDegIn (𝓞 K) = 1) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    K2_2ReciprocalSourceData S :=
  K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split_atPrime_of_mem_notMem
    (P := P) (Q := Q) (iso := iso)
    hℓ_in_P hp_notin_P
    (ringOfIntegers_maximal_ne_bot (K := K) (P := P))
    hQ_in h_compat h_trace he hf

/-- Variant of
`K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split_atPrime_of_mem_notMem_maximal`
that accepts splitting of the rational prime ideal `(ℓ)` instead of splitting
written on `P.under ℤ`. -/
noncomputable def
    K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split_atSpan_of_mem_notMem_maximal
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
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
    (he :
      (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).ramificationIdxIn (𝓞 K) = 1)
    (hf :
      (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).inertiaDegIn (𝓞 K) = 1) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    K2_2ReciprocalSourceData S := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  have h_under :
      P.under ℤ = Ideal.span ({(ℓ : ℤ)} : Set ℤ) :=
    CyclotomicLocalSetup.under_eq_span_of_natCast_mem
      (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  refine
    K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split_atPrime_of_mem_notMem_maximal
      (P := P) (Q := Q) (iso := iso)
      hℓ_in_P hp_notin_P hQ_in h_compat h_trace ?_ ?_
  · simpa [h_under] using he
  · simpa [h_under] using hf

/-- Variant of
`K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split_atSpan_of_mem_notMem_maximal`
that derives the rational-prime split equalities from the cyclotomic
ramification theorem and the order-one condition for `ℓ` modulo `p`. -/
noncomputable def
    K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split_orderOfOne_of_mem_notMem_maximal
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
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
    (h_order : orderOf (ℓ : ZMod p) = 1) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    K2_2ReciprocalSourceData S := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  have hℓ_ne_p : ℓ ≠ p := natCast_ne_of_mem_notMem_ideal hℓ_in_P hp_notin_P
  exact
    K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split_atSpan_of_mem_notMem_maximal
      (P := P) (Q := Q) (iso := iso)
      hℓ_in_P hp_notin_P hQ_in h_compat h_trace
      (ramificationIdxIn_span_natCast_eq_one_of_ne (K := K) hℓ_ne_p)
      (inertiaDegIn_span_natCast_eq_one_of_orderOf (K := K) hℓ_ne_p h_order)

/-- Reciprocal source-data constructor for a normalized source factor of `(α)`.

This is the normalized-factor version of the reciprocal order-one constructor:
maximality of `P` is derived from `α ≠ 0` and
`P ∈ normalizedFactors (Ideal.span {α})`. -/
noncomputable def
    K2_2ReciprocalSourceData.ofCanonicalTraceForm_orderOfOne_normalizedFactor
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    {P : Ideal (𝓞 K)}
    (hP_factor : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    {Q : Ideal (𝓞 R')} [Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    {iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P)}
    (h_compat :
      CyclotomicLocalSetup.IsKAlgebraCompatibleSplittingIso (K₀ := K) Q P iso)
    {S : letI : P.IsMaximal :=
        normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (h_trace :
      letI : P.IsMaximal :=
        normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.toTraceFormStickelbergerSetup =
        CyclotomicLocalSetup.mkTraceForm_ofSplitPrime_canonical_compat
          (K := K) (R' := R') p ℓ P hℓ_in_P hp_notin_P
          (ringOfIntegers_maximal_ne_bot (K := K) (P := P))
          (natCast_ne_of_mem_notMem_ideal hℓ_in_P hp_notin_P)
          Q hQ_in iso h_compat)
    (h_order : orderOf (ℓ : ZMod p) = 1) :
    letI : P.IsMaximal :=
      normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    K2_2ReciprocalSourceData S := by
  letI : P.IsMaximal :=
    normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  exact
    K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split_orderOfOne_of_mem_notMem_maximal
      (P := P) (Q := Q) (iso := iso)
      hℓ_in_P hp_notin_P hQ_in h_compat h_trace h_order

/-- Reciprocal source-data constructor for a normalized source factor of `(α)`
that derives `(p : 𝓞 K) ∉ P` from `(α, p) = ⊤`. -/
noncomputable def
    K2_2ReciprocalSourceData.ofCanonicalTraceForm_orderOfOne_normalizedFactor_pairTop
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
      [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    {P : Ideal (𝓞 K)}
    (hP_factor : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    {Q : Ideal (𝓞 R')} [Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    {iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P)}
    (h_compat :
      CyclotomicLocalSetup.IsKAlgebraCompatibleSplittingIso (K₀ := K) Q P iso)
    {S : letI : P.IsMaximal :=
        normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (h_trace :
      letI : P.IsMaximal :=
        normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      S.toTraceFormStickelbergerSetup =
        CyclotomicLocalSetup.mkTraceForm_ofSplitPrime_canonical_compat
          (K := K) (R' := R') p ℓ P hℓ_in_P
          (natCast_notMem_of_normalizedFactor_span_pair_eq_top
            (K := K) hα_ne hαp_top hP_factor)
          (ringOfIntegers_maximal_ne_bot (K := K) (P := P))
          (natCast_ne_of_mem_notMem_ideal hℓ_in_P
            (natCast_notMem_of_normalizedFactor_span_pair_eq_top
              (K := K) hα_ne hαp_top hP_factor))
          Q hQ_in iso h_compat)
    (h_order : orderOf (ℓ : ZMod p) = 1) :
    letI : P.IsMaximal :=
      normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    K2_2ReciprocalSourceData S := by
  letI : P.IsMaximal :=
    normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  exact
    K2_2ReciprocalSourceData.ofCanonicalTraceForm_orderOfOne_normalizedFactor
      (P := P) (Q := Q) (iso := iso)
      hα_ne hP_factor hℓ_in_P
      (natCast_notMem_of_normalizedFactor_span_pair_eq_top
        (K := K) hα_ne hαp_top hP_factor)
      hQ_in h_compat h_trace h_order

/-- **Cyclotomic discharged facts for a single `K2_2SourceData`**: bundles
`K2_2SourceData_phi_gamma_isSemiPrimary` and
`K2_2SourceData_phi_conj_mul_self_eq_absNorm_pow_cyclotomic` into a single
named conjunction. -/
theorem K2_2SourceData_phi_facts_cyclotomic
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hpℓ : p ≠ ℓ) (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2SourceData S) :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    FLT37.IsSemiPrimary p (K := K) D.phi.gamma ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
        (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  refine ⟨?_, ?_⟩
  · exact PhiPrimeElement.K2_2SourceData_phi_gamma_isSemiPrimary
      (p := p) (K := K) D hp_three
  · exact K2_2SourceData_phi_conj_mul_self_eq_absNorm_pow_cyclotomic
      (ℓ := ℓ) (p := p) (K := K) (R' := R') hpℓ hp_gt_two D

/-- **Cyclotomic discharged facts for a single reciprocal `K2_2SourceData`**:
bundles reciprocal semi-primary and conjugation-norm facts into one named
conjunction. -/
theorem K2_2ReciprocalSourceData_phi_facts_cyclotomic
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hpℓ : p ≠ ℓ) (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2ReciprocalSourceData S) :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    FLT37.IsSemiPrimary p (K := K) D.phi.gamma ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
        (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  refine ⟨?_, ?_⟩
  · exact PhiPrimeElement.K2_2ReciprocalSourceData_phi_gamma_isSemiPrimary
      (p := p) (K := K) D hp_three
  · exact K2_2ReciprocalSourceData_phi_conj_mul_self_eq_absNorm_pow_cyclotomic
      (ℓ := ℓ) (p := p) (K := K) (R' := R') hpℓ hp_gt_two D

end PhiPrimeElement

end Furtwaengler

end BernoulliRegular

end

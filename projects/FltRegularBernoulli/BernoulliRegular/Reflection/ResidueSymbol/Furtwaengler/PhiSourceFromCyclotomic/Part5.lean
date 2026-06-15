module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.BundleFromCyclotomic
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeElement
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor
public import Mathlib.NumberTheory.NumberField.Basic
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiSourceFromCyclotomic.Part4

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

namespace K2_2PrimeFactorBundle

/-- Prime-factor bundle constructor that derives the rational-prime split
facts from `orderOf (ℓ : ZMod p) = 1`. -/
noncomputable def ofCanonicalTraceForm_atomic_split_orderOfOne_of_mem_notMem_maximal
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
    K2_2PrimeFactorBundle ℓ p K R' P where
  P_max := inferInstance
  alg_inst :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  S := S
  D :=
    K2_2SourceData.ofCanonicalTraceForm_atomic_split_orderOfOne_of_mem_notMem_maximal
      (P := P) (Q := Q) (iso := iso)
      hℓ_in_P hp_notin_P hQ_in h_compat h_trace h_ne_zero h_exp h_order

/-- Prime-factor bundle constructor for a normalized source factor of `(α)`.

This packages `K2_2SourceData.ofCanonicalTraceForm_orderOfOne_normalizedFactor`
and derives the bundle's maximality field from normalized-factor membership. -/
noncomputable def ofCanonicalTraceForm_orderOfOne_normalizedFactor
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
    K2_2PrimeFactorBundle ℓ p K R' P where
  P_max := normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
  alg_inst :=
    letI : P.IsMaximal :=
      normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  S := S
  D :=
    K2_2SourceData.ofCanonicalTraceForm_orderOfOne_normalizedFactor
      (P := P) (Q := Q) (iso := iso)
      hα_ne hP_factor hℓ_in_P hp_notin_P hQ_in h_compat
      h_trace h_ne_zero h_exp h_order

/-- Prime-factor bundle constructor for a normalized source factor of `(α)`
that derives `(p : 𝓞 K) ∉ P` from `(α, p) = ⊤`. -/
noncomputable def ofCanonicalTraceForm_orderOfOne_normalizedFactor_pairTop
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
    K2_2PrimeFactorBundle ℓ p K R' P where
  P_max := normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
  alg_inst :=
    letI : P.IsMaximal :=
      normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  S := S
  D :=
    K2_2SourceData.ofCanonicalTraceForm_orderOfOne_normalizedFactor_pairTop
      (P := P) (Q := Q) (iso := iso)
      hα_ne hαp_top hP_factor hℓ_in_P hQ_in h_compat
      h_trace h_ne_zero h_exp h_order

/-- Prime-factor bundle constructor for a normalized source factor of `(α)`
that derives `(p : 𝓞 K) ∉ P` from `(α, p) = ⊤` and derives index-one
Gauss-sum nonvanishing from Dwork exact order. -/
noncomputable def ofCanonicalTraceForm_orderOfOne_normalizedFactor_pairTop_dworkNeZero
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
    K2_2PrimeFactorBundle ℓ p K R' P where
  P_max := normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
  alg_inst :=
    letI : P.IsMaximal :=
      normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  S := S
  D :=
    K2_2SourceData.ofCanonicalTraceForm_orderOfOne_normalizedFactor_pairTop_dworkNeZero
      (P := P) (Q := Q) (iso := iso)
      hα_ne hαp_top hP_factor hℓ_in_P hQ_in h_compat
      h_trace h_exp h_order

/-- Prime-factor bundle constructor for the actual signed Φ source route
that derives the exact conjugate-exponent input from the split trace form and
the concrete Galois covariance of `phiPrimeGenDescent S 1`.

This is the honest nonreciprocal analogue of the reciprocal pair-field
constructor: callers still provide the substantive covariance equality, but
no longer provide `StickelbergerExactConjugateExponents` directly. -/
noncomputable def ofCanonicalTraceForm_orderOfOne_normalizedFactor_pairTop_covariance
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
    (h_conj :
      letI : P.IsMaximal :=
        normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
        CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      ∀ a : CyclotomicUnitDelta p,
        algebraMap (𝓞 K) (𝓞 R')
          (cyclotomicRingOfIntegersEquiv (p := p) K a
            (phiPrimeGenDescent S
              (le_refl 1) (one_le_p_sub_one_of_prime (p := p))
              (gaussSumInt_pow_p_ne_zero_of_dwork S
                (le_refl 1) (one_le_p_sub_one_of_prime (p := p))))) =
          S.gaussSumInt (p - (a : ZMod p).val) ^ p)
    (h_order : orderOf (ℓ : ZMod p) = 1) :
    K2_2PrimeFactorBundle ℓ p K R' P := by
  letI : P.IsMaximal :=
    normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  have hp_notin_P : (p : 𝓞 K) ∉ P :=
    natCast_notMem_of_normalizedFactor_span_pair_eq_top
      (K := K) hα_ne hαp_top hP_factor
  have hP_ne_bot : P ≠ ⊥ :=
    ringOfIntegers_maximal_ne_bot (K := K) (P := P)
  have hℓ_ne_p : ℓ ≠ p :=
    natCast_ne_of_mem_notMem_ideal hℓ_in_P hp_notin_P
  have hf_span :
      (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).inertiaDegIn (𝓞 K) = 1 :=
    inertiaDegIn_span_natCast_eq_one_of_orderOf (K := K) hℓ_ne_p h_order
  have hS_f : S.f = 1 :=
    f_eq_one_of_canonicalTraceForm_atSpan
      (K := K) (R' := R') hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
      hQ_in h_compat h_trace hf_span
  have h_descentPrime :
      S.toConcreteStickelbergerSetup.descentPrime = P :=
    descentPrime_eq_of_canonicalTraceForm
      (K := K) (R' := R') hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p
      hQ_in h_compat h_trace
  have h_under :
      P.under ℤ = Ideal.span ({(ℓ : ℤ)} : Set ℤ) :=
    CyclotomicLocalSetup.under_eq_span_of_natCast_mem
      (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  have he_at_P :
      (P.under ℤ).ramificationIdxIn (𝓞 K) = 1 := by
    simpa [h_under] using
      (ramificationIdxIn_span_natCast_eq_one_of_ne (K := K) hℓ_ne_p)
  have he_S :
      (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).ramificationIdxIn
        (𝓞 K) = 1 := by
    rw [h_descentPrime]
    exact he_at_P
  have h_exp :
      S.StickelbergerExactConjugateExponents
        (phiPrimeGenDescent S
          (le_refl 1) (one_le_p_sub_one_of_prime (p := p))
          (gaussSumInt_pow_p_ne_zero_of_dwork S
            (le_refl 1) (one_le_p_sub_one_of_prime (p := p)))) :=
    StickelbergerExactConjugateExponents_phiPrimeGenDescent_one_of_sub_val_conjugates_split
      (K := K) (R' := R') S hS_f he_S
      (gaussSumInt_pow_p_ne_zero_of_dwork S
        (le_refl 1) (one_le_p_sub_one_of_prime (p := p)))
      h_conj
  exact
    ofCanonicalTraceForm_orderOfOne_normalizedFactor_pairTop_dworkNeZero
      (P := P) (Q := Q) (iso := iso)
      hα_ne hαp_top hP_factor hℓ_in_P hQ_in h_compat
      h_trace h_exp h_order

/-- Family form of
`ofCanonicalTraceForm_orderOfOne_normalizedFactor_pairTop_covariance` for all
normalized source factors of `(α)`. -/
noncomputable def ofCanonicalTraceForm_orderOfOne_normalizedFactor_pairTop_covarianceFamily
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
    (hℓ_in :
      ∀ P : Ideal (𝓞 K),
        P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
          (ℓ : 𝓞 K) ∈ P)
    (Q :
      ∀ P : Ideal (𝓞 K),
        P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
          Ideal (𝓞 R'))
    (iso :
      ∀ (P : Ideal (𝓞 K))
        (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
          (𝓞 R' ⧸ Q P hP) ≃+* (𝓞 K ⧸ P))
    (hQ_prime :
      ∀ (P : Ideal (𝓞 K))
        (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
          (Q P hP).IsPrime)
    (hQ_in :
      ∀ (P : Ideal (𝓞 K))
        (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
          (ℓ : 𝓞 R') ∈ Q P hP)
    (h_compat :
      ∀ (P : Ideal (𝓞 K))
        (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        CyclotomicLocalSetup.IsKAlgebraCompatibleSplittingIso
          (K₀ := K) (Q P hP) P (iso P hP))
    (S :
      ∀ (P : Ideal (𝓞 K))
        (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        letI : P.IsMaximal :=
          normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP
        letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
        letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
          CyclotomicLocalSetup.algebra_zmod_residueField
            (ℓ₀ := ℓ) (K₀ := K) P (hℓ_in P hP)
        FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_trace :
      ∀ (P : Ideal (𝓞 K))
        (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        letI : P.IsMaximal :=
          normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP
        letI : (Q P hP).IsPrime := hQ_prime P hP
        letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
        letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
          CyclotomicLocalSetup.algebra_zmod_residueField
            (ℓ₀ := ℓ) (K₀ := K) P (hℓ_in P hP)
        (S P hP).toTraceFormStickelbergerSetup =
          CyclotomicLocalSetup.mkTraceForm_ofSplitPrime_canonical_compat
            (K := K) (R' := R') p ℓ P (hℓ_in P hP)
            (natCast_notMem_of_normalizedFactor_span_pair_eq_top
              (K := K) hα_ne hαp_top hP)
            (ringOfIntegers_maximal_ne_bot (K := K) (P := P))
            (natCast_ne_of_mem_notMem_ideal (hℓ_in P hP)
              (natCast_notMem_of_normalizedFactor_span_pair_eq_top
                (K := K) hα_ne hαp_top hP))
            (Q P hP)
            (hQ_in P hP)
            (iso P hP) (h_compat P hP))
    (h_conj :
      ∀ (P : Ideal (𝓞 K))
        (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        letI : P.IsMaximal :=
          normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP
        letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
        letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
          CyclotomicLocalSetup.algebra_zmod_residueField
            (ℓ₀ := ℓ) (K₀ := K) P (hℓ_in P hP)
        ∀ a : CyclotomicUnitDelta p,
          algebraMap (𝓞 K) (𝓞 R')
            (cyclotomicRingOfIntegersEquiv (p := p) K a
              (phiPrimeGenDescent (S P hP)
                (le_refl 1) (one_le_p_sub_one_of_prime (p := p))
                (gaussSumInt_pow_p_ne_zero_of_dwork (S P hP)
                  (le_refl 1) (one_le_p_sub_one_of_prime (p := p))))) =
            (S P hP).gaussSumInt (p - (a : ZMod p).val) ^ p)
    (h_order : orderOf (ℓ : ZMod p) = 1) :
    ∀ P : Ideal (𝓞 K),
      P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
        K2_2PrimeFactorBundle ℓ p K R' P :=
  fun P hP => by
    letI : P.IsMaximal :=
      normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP
    letI : (Q P hP).IsPrime := hQ_prime P hP
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField
        (ℓ₀ := ℓ) (K₀ := K) P (hℓ_in P hP)
    exact
      ofCanonicalTraceForm_orderOfOne_normalizedFactor_pairTop_covariance
        (p := p) (K := K) (R' := R') (P := P) (Q := Q P hP)
        (iso := iso P hP) (S := S P hP)
        hα_ne hαp_top hP (hℓ_in P hP)
        (hQ_in P hP)
        (h_compat P hP) (h_trace P hP) (h_conj P hP) h_order

end K2_2PrimeFactorBundle

/-- **Per-prime reciprocal K2-2 source-data bundle**, packaging the same
typeclass instances as `K2_2PrimeFactorBundle` but carrying reciprocal-index
source data. This is the direct positive-orientation package for REF-18. -/
structure K2_2ReciprocalPrimeFactorBundle
    (ℓ p : ℕ) [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type v) [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    (P : Ideal (𝓞 K)) where
  /-- The source prime `P` is maximal. -/
  P_max : P.IsMaximal
  /-- The residue field `𝓞 K ⧸ P` carries a `(ZMod ℓ)`-algebra structure. -/
  alg_inst : Algebra (ZMod ℓ) (𝓞 K ⧸ P)
  /-- The Dwork bundle at the residue field `𝓞 K ⧸ P`. -/
  S : letI : P.IsMaximal := P_max
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) := alg_inst
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'
  /-- The reciprocal K2-2 source data on `S`. -/
  D : letI : P.IsMaximal := P_max
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) := alg_inst
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      K2_2ReciprocalSourceData (ℓ := ℓ) (p := p) (K := K) (R' := R') S

namespace K2_2ReciprocalPrimeFactorBundle

/-- The actual reciprocal prime Φ element associated to a
`K2_2ReciprocalPrimeFactorBundle`. -/
noncomputable def phi
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} (B : K2_2ReciprocalPrimeFactorBundle ℓ p K R' P) :
    PhiPrimeElement (p := p) (K := K) P :=
  letI : P.IsMaximal := B.P_max
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) := B.alg_inst
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  B.D.phi

/-- Build a reciprocal prime-factor bundle from the canonical trace-form split
prime data and the pair-field exact-exponent theorem. -/
noncomputable def ofCanonicalTraceForm_pairSigma_split
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
    K2_2ReciprocalPrimeFactorBundle ℓ p K R' P where
  P_max := inferInstance
  alg_inst :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  S := S
  D :=
    K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split
      (P := P) (Q := Q) (iso := iso)
      hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p hQ_in h_compat h_trace
      h_descentPrime he hf

/-- Reciprocal prime-factor bundle constructor that derives the descent-prime
equality from the canonical trace-form identity and accepts split conditions
directly for `P`. -/
noncomputable def ofCanonicalTraceForm_pairSigma_split_atPrime
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
    K2_2ReciprocalPrimeFactorBundle ℓ p K R' P where
  P_max := inferInstance
  alg_inst :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  S := S
  D :=
    K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split_atPrime
      (P := P) (Q := Q) (iso := iso)
      hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p hQ_in h_compat h_trace
      he hf

/-- Reciprocal prime-factor bundle constructor that derives both the
descent-prime equality and `ℓ ≠ p` from the source-prime
membership/nonmembership hypotheses. -/
noncomputable def ofCanonicalTraceForm_pairSigma_split_atPrime_of_mem_notMem
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
    K2_2ReciprocalPrimeFactorBundle ℓ p K R' P where
  P_max := inferInstance
  alg_inst :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  S := S
  D :=
    K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split_atPrime_of_mem_notMem
      (P := P) (Q := Q) (iso := iso)
      hℓ_in_P hp_notin_P hP_ne_bot hQ_in h_compat h_trace
      he hf

/-- Reciprocal prime-factor bundle constructor that derives `P ≠ ⊥`, the
descent-prime equality, and `ℓ ≠ p` from the source-prime hypotheses. -/
noncomputable def ofCanonicalTraceForm_pairSigma_split_atPrime_of_mem_notMem_maximal
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
    K2_2ReciprocalPrimeFactorBundle ℓ p K R' P where
  P_max := inferInstance
  alg_inst :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  S := S
  D :=
    K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split_atPrime_of_mem_notMem_maximal
      (P := P) (Q := Q) (iso := iso)
      hℓ_in_P hp_notin_P hQ_in h_compat h_trace he hf

/-- Reciprocal prime-factor bundle constructor that accepts splitting of the
rational prime ideal `(ℓ)` instead of splitting written on `P.under ℤ`. -/
noncomputable def ofCanonicalTraceForm_pairSigma_split_atSpan_of_mem_notMem_maximal
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
    K2_2ReciprocalPrimeFactorBundle ℓ p K R' P where
  P_max := inferInstance
  alg_inst :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  S := S
  D :=
    K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split_atSpan_of_mem_notMem_maximal
      (P := P) (Q := Q) (iso := iso)
      hℓ_in_P hp_notin_P hQ_in h_compat h_trace he hf

end K2_2ReciprocalPrimeFactorBundle
end PhiPrimeElement

end Furtwaengler

end BernoulliRegular

end

module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.BundleFromCyclotomic
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeElement
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor
public import Mathlib.NumberTheory.NumberField.Basic
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiSourceFromCyclotomic.PrimeFactorBundleConstructors

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

namespace K2_2ReciprocalPrimeFactorBundle

/-- Reciprocal prime-factor bundle constructor that derives the rational-prime
split facts from `orderOf (ℓ : ZMod p) = 1`. -/
noncomputable def ofCanonicalTraceForm_pairSigma_split_orderOfOne_of_mem_notMem_maximal
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
    K2_2ReciprocalPrimeFactorBundle ℓ p K R' P where
  P_max := inferInstance
  alg_inst :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  S := S
  D :=
    K2_2ReciprocalSourceData.ofCanonicalTraceForm_pairSigma_split_orderOfOne_of_mem_notMem_maximal
      (P := P) (Q := Q) (iso := iso)
      hℓ_in_P hp_notin_P hQ_in h_compat h_trace h_order

/-- Reciprocal prime-factor bundle constructor for a normalized source factor
of `(α)`. -/
noncomputable def ofCanonicalTraceForm_orderOfOne_normalizedFactor
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
    K2_2ReciprocalPrimeFactorBundle ℓ p K R' P where
  P_max := normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
  alg_inst :=
    letI : P.IsMaximal :=
      normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  S := S
  D :=
    K2_2ReciprocalSourceData.ofCanonicalTraceForm_orderOfOne_normalizedFactor
      (P := P) (Q := Q) (iso := iso)
      hα_ne hP_factor hℓ_in_P hp_notin_P hQ_in h_compat
      h_trace h_order

/-- Reciprocal prime-factor bundle constructor for a normalized source factor
of `(α)` that derives `(p : 𝓞 K) ∉ P` from `(α, p) = ⊤`. -/
noncomputable def ofCanonicalTraceForm_orderOfOne_normalizedFactor_pairTop
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
    K2_2ReciprocalPrimeFactorBundle ℓ p K R' P where
  P_max := normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
  alg_inst :=
    letI : P.IsMaximal :=
      normalizedFactor_span_singleton_isMaximal (K := K) hα_ne hP_factor
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  S := S
  D :=
    K2_2ReciprocalSourceData.ofCanonicalTraceForm_orderOfOne_normalizedFactor_pairTop
      (P := P) (Q := Q) (iso := iso)
      hα_ne hαp_top hP_factor hℓ_in_P hQ_in h_compat h_trace h_order

end K2_2ReciprocalPrimeFactorBundle

/-- **Cyclotomic U4 endpoint from K2-2 source-data bundles**. Takes a
per-prime-factor `K2_2PrimeFactorBundle` family for the prime factors
of `(α)` and the α/primary data, and produces
`ChosenPrimaryUnitFactorSymbolTrivial α`. Internally derives the
per-prime `primePhi` (via `K2_2PrimeFactorBundle.phi`) and discharges
the semi-primary and conjugation-norm hypotheses via
`K2_2SourceData_phi_facts_cyclotomic`, then forwards to the
`primePhiFamilyFacts` U4 theorem. -/
theorem ChosenPrimaryUnitFactorSymbolTrivial_of_K2_2PrimeFactorBundleFamily_cyclotomic
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hpℓ : p ≠ ℓ) (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (sourceBundle : ∀ P : Ideal (𝓞 K),
      P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
        K2_2PrimeFactorBundle ℓ p K R' P) :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    ChosenPrimaryUnitFactorSymbolTrivial (p := p) (K := K) α := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  have hp_odd : p ≠ 2 := fun h => by rw [h] at hp_gt_two; omega
  have hp_two : 2 ≤ p := le_of_lt hp_gt_two
  refine ChosenPrimaryUnitFactorSymbolTrivial_of_primary_primePhiFamilyFacts
    (p := p) (K := K) hp_odd hp_two hp_three hα_ne hαp_top
    (primePhi := fun P hP => (sourceBundle P hP).phi)
    hα_primary ?_ ?_
  · intro P hP
    letI : P.IsMaximal := (sourceBundle P hP).P_max
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) := (sourceBundle P hP).alg_inst
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    exact (K2_2SourceData_phi_facts_cyclotomic
      (ℓ := ℓ) (p := p) (K := K) (R' := R')
      hpℓ hp_gt_two hp_three (sourceBundle P hP).D).1
  · intro P hP
    letI : P.IsMaximal := (sourceBundle P hP).P_max
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) := (sourceBundle P hP).alg_inst
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    exact (K2_2SourceData_phi_facts_cyclotomic
      (ℓ := ℓ) (p := p) (K := K) (R' := R')
      hpℓ hp_gt_two hp_three (sourceBundle P hP).D).2

/-- **Cyclotomic chosen product-power U4 endpoint from K2-2 source-data
bundles**.

This is the product-side strengthening of
`ChosenPrimaryUnitFactorSymbolTrivial_of_K2_2PrimeFactorBundleFamily_cyclotomic`:
the exact product-power input is tied to the principal Φ product built from
the same K2 source-bundle family. -/
theorem ChosenPrimaryUnitFactorProductPower_of_K2_2PrimeFactorBundleFamily_cyclotomic
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hpℓ : p ≠ ℓ) (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (sourceBundle : ∀ P : Ideal (𝓞 K),
      P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
        K2_2PrimeFactorBundle ℓ p K R' P)
    (h_phi_product :
      ∃ β : 𝓞 K,
        (PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors
          (p := p) (K := K) α
          (fun P hP => (sourceBundle P hP).phi)).gamma * α = β ^ p) :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    ChosenPrimaryUnitFactorProductPower (p := p) (K := K) α := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  have hp_odd : p ≠ 2 := fun h => by rw [h] at hp_gt_two; omega
  have hp_two : 2 ≤ p := le_of_lt hp_gt_two
  refine ChosenPrimaryUnitFactorProductPower_of_primary_primePhiFamilyFacts
    (p := p) (K := K) hp_odd hp_two hp_three hα_ne hαp_top
    (primePhi := fun P hP => (sourceBundle P hP).phi)
    hα_primary ?_ ?_ h_phi_product
  · intro P hP
    letI : P.IsMaximal := (sourceBundle P hP).P_max
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) := (sourceBundle P hP).alg_inst
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    exact (K2_2SourceData_phi_facts_cyclotomic
      (ℓ := ℓ) (p := p) (K := K) (R' := R')
      hpℓ hp_gt_two hp_three (sourceBundle P hP).D).1
  · intro P hP
    letI : P.IsMaximal := (sourceBundle P hP).P_max
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) := (sourceBundle P hP).alg_inst
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    exact (K2_2SourceData_phi_facts_cyclotomic
      (ℓ := ℓ) (p := p) (K := K) (R' := R')
      hpℓ hp_gt_two hp_three (sourceBundle P hP).D).2

/-- **Cyclotomic chosen local product-symbol U4 endpoint from K2-2
source-data bundles**.

This is the local-symbol analogue of
`ChosenPrimaryUnitFactorProductPower_of_K2_2PrimeFactorBundleFamily_cyclotomic`:
the product input is only local vanishing of the exact principal Φ product
built from the same K2 source-bundle family. -/
theorem ChosenPrimaryUnitFactorProductSymbolZero_of_K2_2PrimeFactorBundleFamily_cyclotomic
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hpℓ : p ≠ ℓ) (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (sourceBundle : ∀ P : Ideal (𝓞 K),
      P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
        K2_2PrimeFactorBundle ℓ p K R' P)
    (h_phi_product_zero :
      ∀ P : Ideal (𝓞 K), α ∉ P →
        pthSymbolAtPrime_canonical (p := p) (K := K)
          ((PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors
            (p := p) (K := K) α
            (fun P hP => (sourceBundle P hP).phi)).gamma * α) P = 0) :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    ChosenPrimaryUnitFactorProductSymbolZero (p := p) (K := K) α := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  have hp_odd : p ≠ 2 := fun h => by rw [h] at hp_gt_two; omega
  have hp_two : 2 ≤ p := le_of_lt hp_gt_two
  refine ChosenPrimaryUnitFactorProductSymbolZero_of_primary_primePhiFamilyFacts
    (p := p) (K := K) hp_odd hp_two hp_three hα_ne hαp_top
    (primePhi := fun P hP => (sourceBundle P hP).phi)
    hα_primary ?_ ?_ h_phi_product_zero
  · intro P hP
    letI : P.IsMaximal := (sourceBundle P hP).P_max
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) := (sourceBundle P hP).alg_inst
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    exact (K2_2SourceData_phi_facts_cyclotomic
      (ℓ := ℓ) (p := p) (K := K) (R' := R')
      hpℓ hp_gt_two hp_three (sourceBundle P hP).D).1
  · intro P hP
    letI : P.IsMaximal := (sourceBundle P hP).P_max
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) := (sourceBundle P hP).alg_inst
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    exact (K2_2SourceData_phi_facts_cyclotomic
      (ℓ := ℓ) (p := p) (K := K) (R' := R')
      hpℓ hp_gt_two hp_three (sourceBundle P hP).D).2

section CovarianceProductEndpoint

open K2_2PrimeFactorBundle

/-- Trace-form/covariance version of the chosen local product-symbol U4
endpoint.

The product input is the local vanishing statement for the exact principal
Φ-family built from the covariance-derived signed K2 source bundles. -/
theorem ChosenPrimaryUnitFactorProductSymbolZero_of_traceForm_covariance_cyclotomic
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hpℓ : p ≠ ℓ) (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
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
            (Q P hP) (hQ_in P hP) (iso P hP) (h_compat P hP))
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
    (h_order : orderOf (ℓ : ZMod p) = 1)
    (h_phi_product_zero :
      ∀ P : Ideal (𝓞 K), α ∉ P →
        pthSymbolAtPrime_canonical (p := p) (K := K)
          ((PhiPrimeElement.PhiIdealElement.PhiPrincipalElement.ofPrimeFactors
            (p := p) (K := K) α
            (fun P hP =>
              (ofCanonicalTraceForm_orderOfOne_normalizedFactor_pairTop_covarianceFamily
                (p := p) (K := K) (R' := R')
                hα_ne hαp_top hℓ_in Q iso hQ_prime hQ_in h_compat
                S h_trace h_conj h_order P hP).phi)).gamma * α) P = 0) :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    ChosenPrimaryUnitFactorProductSymbolZero (p := p) (K := K) α := by
  let sourceBundle :
      ∀ P : Ideal (𝓞 K),
        P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
          K2_2PrimeFactorBundle ℓ p K R' P :=
    ofCanonicalTraceForm_orderOfOne_normalizedFactor_pairTop_covarianceFamily
      (p := p) (K := K) (R' := R')
      hα_ne hαp_top hℓ_in Q iso hQ_prime hQ_in h_compat
      S h_trace h_conj h_order
  exact ChosenPrimaryUnitFactorProductSymbolZero_of_K2_2PrimeFactorBundleFamily_cyclotomic
    (p := p) (K := K) (ℓ := ℓ) (R' := R')
    hpℓ hp_gt_two hp_three hα_ne hαp_top hα_primary sourceBundle
    (by simpa [sourceBundle] using h_phi_product_zero)

end CovarianceProductEndpoint

/-- **Cyclotomic Kelly endpoint with prime target from K2-2 source-data
bundles and already-bundled target data**. Takes a per-prime-factor
`K2_2PrimeFactorBundle` family and a `K2_2TargetData` package for the target
`P'`, then produces `kellyPrimeNegEquality α P'`. -/
theorem kellyPrimeNegEquality_of_K2_2PrimeFactorBundleFamily_targetData
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hpℓ : p ≠ ℓ) (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (sourceBundle : ∀ P : Ideal (𝓞 K),
      P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
        K2_2PrimeFactorBundle ℓ p K R' P)
    {P' : Ideal (𝓞 K)} [P'.IsMaximal]
    (targetData :
      K2_2TargetData (ℓ := ℓ) (p := p) (K := K) (R' := R') P')
    (hcop : (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
            (Ideal.absNorm P'))
    (hcop_each :
      ∀ P (_hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        (Ideal.absNorm P).Coprime (Ideal.absNorm P'))
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    haveI : P'.IsPrime := inferInstance
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      -pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  refine kellyPrimeNegEquality_of_K2_2SourceDataFamily_cyclotomic_primeTarget_bundled
    (ℓ := ℓ) (R' := R') hp_gt_two hp_three hα_ne hαp_top
    (primePhi := fun P hP => (sourceBundle P hP).phi)
    hα_primary targetData.hP'_bot hcop ?_ h_coprime
  intro P hP
  letI : P.IsMaximal := (sourceBundle P hP).P_max
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) := (sourceBundle P hP).alg_inst
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  exact K2_2SourceData_phi_facts_at_targetData
    (ℓ := ℓ) (p := p) (K := K) (R' := R') hpℓ hp_gt_two hp_three
    (sourceBundle P hP).D targetData (hcop_each P hP)

/-- **Cyclotomic Kelly endpoint with prime target from K2-2 source-data
bundles**. Takes a per-prime-factor `K2_2PrimeFactorBundle` family plus
shared over-prime data for the target `P'`, and produces
`kellyPrimeNegEquality α P'`. Internally derives the per-prime
`primePhi` (via `K2_2PrimeFactorBundle.phi`) and the per-prime fact
conjunction (via `K2_2SourceData_phi_facts_at_primeTarget`), then
forwards to the bundled prime-target Kelly composer. -/
theorem kellyPrimeNegEquality_of_K2_2PrimeFactorBundleFamily_natCast_primeTarget
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hpℓ : p ≠ ℓ) (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (sourceBundle : ∀ P : Ideal (𝓞 K),
      P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
        K2_2PrimeFactorBundle ℓ p K R' P)
    {P' : Ideal (𝓞 K)} [P'.IsMaximal]
    (hP'_ne : P' ≠ ⊥)
    (hp_notin_P' : (p : 𝓞 K) ∉ P')
    (overPrime : Ideal (𝓞 R')) (overPrime_max : overPrime.IsMaximal)
    (ell' : ℕ) (ell'_prime : Fact ell'.Prime)
    (hell'_in_overPrime : (ell' : 𝓞 R') ∈ overPrime)
    (h_over : overPrime.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (hℓ_ne_ℓ' : ℓ ≠ ell')
    (hcop : (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
            (Ideal.absNorm P'))
    (hcop_each :
      ∀ P (_hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        (Ideal.absNorm P).Coprime (Ideal.absNorm P'))
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    haveI : P'.IsPrime := inferInstance
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      -pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) :=
  kellyPrimeNegEquality_of_K2_2PrimeFactorBundleFamily_targetData
    (R' := R') (ℓ := ℓ) hpℓ hp_gt_two hp_three hα_ne hαp_top hα_primary
    sourceBundle
    (K2_2TargetData.mk_ofOverPrime_natCast
      hP'_ne hp_notin_P' overPrime overPrime_max ell' ell'_prime
      hell'_in_overPrime h_over hℓ_ne_ℓ')
    hcop hcop_each h_coprime

/-- **Cyclotomic Kelly endpoint with target data chosen by quotient
`ringChar`.**

This is the same signed K2-2 source-bundle endpoint as
`kellyPrimeNegEquality_of_K2_2PrimeFactorBundleFamily_natCast_primeTarget`,
but the target-side `K2_2TargetData` is constructed internally from a maximal
over-prime of `P'`. The caller supplies the actual separation condition
against the quotient characteristic of every such over-prime, rather than an
auxiliary residue prime and `CharP` witness. -/
theorem kellyPrimeNegEquality_of_K2_2PrimeFactorBundleFamily_ringChar_primeTarget
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hpℓ : p ≠ ℓ) (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (sourceBundle : ∀ P : Ideal (𝓞 K),
      P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
        K2_2PrimeFactorBundle ℓ p K R' P)
    {P' : Ideal (𝓞 K)} [P'.IsMaximal]
    (hP'_ne : P' ≠ ⊥)
    (hp_notin_P' : (p : 𝓞 K) ∉ P')
    (hℓ_ne_char :
      ∀ overPrime : Ideal (𝓞 R'), overPrime.IsMaximal →
        overPrime.comap (algebraMap (𝓞 K) (𝓞 R')) = P' →
          ℓ ≠ ringChar (𝓞 R' ⧸ overPrime))
    (hcop : (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
            (Ideal.absNorm P'))
    (hcop_each :
      ∀ P (_hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        (Ideal.absNorm P).Coprime (Ideal.absNorm P'))
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    haveI : P'.IsPrime := inferInstance
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      -pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) :=
  kellyPrimeNegEquality_of_K2_2PrimeFactorBundleFamily_targetData
    (R' := R') (ℓ := ℓ) hpℓ hp_gt_two hp_three hα_ne hαp_top hα_primary
    sourceBundle
    (K2_2TargetData.mk_ofPrime_ringChar
      hP'_ne hp_notin_P' hℓ_ne_char)
    hcop hcop_each h_coprime

/-- **Away-from-`p` universal signed Kelly endpoint from K2-2 bundles**.

The ordinary K2-2 source-bundle family gives the signed
`kellyPrimeNegEquality` at every nonzero prime target away from `p`, provided
the caller supplies the corresponding target data and coprimality inputs. In
the singular REF-18 endpoint this signed form is enough, because the
right-hand norm symbol vanishes. -/
theorem kellyPrimeNegEquality_awayFromP_of_K2_2PrimeFactorBundleFamily_targetData
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hpℓ : p ≠ ℓ) (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (sourceBundle : ∀ P : Ideal (𝓞 K),
      P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
        K2_2PrimeFactorBundle ℓ p K R' P)
    (targetData :
      ∀ (P' : Ideal (𝓞 K)) (hP'_prime : P'.IsPrime) (hP'_ne : P' ≠ ⊥),
        (p : 𝓞 K) ∉ P' →
          haveI : P'.IsMaximal := Ideal.IsPrime.isMaximal hP'_prime hP'_ne
          K2_2TargetData (ℓ := ℓ) (p := p) (K := K) (R' := R') P')
    (hcop :
      ∀ (P' : Ideal (𝓞 K)) (_hP'_prime : P'.IsPrime) (_hP'_ne : P' ≠ ⊥),
        (p : 𝓞 K) ∉ P' →
          (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
            (Ideal.absNorm P'))
    (hcop_each :
      ∀ P (_hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        P' (_hP'_prime : P'.IsPrime) (_hP'_ne : P' ≠ ⊥),
          (p : 𝓞 K) ∉ P' →
            (Ideal.absNorm P).Coprime (Ideal.absNorm P'))
    (h_coprime :
      ∀ (P' : Ideal (𝓞 K)) (_hP'_prime : P'.IsPrime) (_hP'_ne : P' ≠ ⊥),
        (p : 𝓞 K) ∉ P' →
          ∀ a : CyclotomicUnitDelta p,
            cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    ∀ (P' : Ideal (𝓞 K)), P'.IsPrime → P' ≠ ⊥ → (p : 𝓞 K) ∉ P' →
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
        -pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := by
  intro P' hP'_prime hP'_ne hp_notin_P'
  haveI : P'.IsMaximal := Ideal.IsPrime.isMaximal hP'_prime hP'_ne
  exact kellyPrimeNegEquality_of_K2_2PrimeFactorBundleFamily_targetData
    (R' := R') (ℓ := ℓ) hpℓ hp_gt_two hp_three hα_ne hαp_top hα_primary
    sourceBundle (targetData P' hP'_prime hP'_ne hp_notin_P')
    (hcop P' hP'_prime hP'_ne hp_notin_P')
    (fun P hP => hcop_each P hP P' hP'_prime hP'_ne hp_notin_P')
    (h_coprime P' hP'_prime hP'_ne hp_notin_P')

/-- **Away-from-`p` universal signed Kelly endpoint with target data chosen by
quotient `ringChar`.**

This is the target-side concrete form of the universal K2-2 handoff: the only
target supplier is the proof that the fixed source characteristic `ℓ` differs
from the actual residue characteristic of every maximal over-prime above the
target. -/
theorem kellyPrimeNegEquality_awayFromP_of_K2_2PrimeFactorBundleFamily_ringChar
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hpℓ : p ≠ ℓ) (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (sourceBundle : ∀ P : Ideal (𝓞 K),
      P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
        K2_2PrimeFactorBundle ℓ p K R' P)
    (targetChar :
      ∀ (P' : Ideal (𝓞 K)) (_hP'_prime : P'.IsPrime) (_hP'_ne : P' ≠ ⊥),
        (p : 𝓞 K) ∉ P' →
          ∀ overPrime : Ideal (𝓞 R'), overPrime.IsMaximal →
            overPrime.comap (algebraMap (𝓞 K) (𝓞 R')) = P' →
              ℓ ≠ ringChar (𝓞 R' ⧸ overPrime))
    (hcop :
      ∀ (P' : Ideal (𝓞 K)) (_hP'_prime : P'.IsPrime) (_hP'_ne : P' ≠ ⊥),
        (p : 𝓞 K) ∉ P' →
          (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
            (Ideal.absNorm P'))
    (hcop_each :
      ∀ P (_hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        P' (_hP'_prime : P'.IsPrime) (_hP'_ne : P' ≠ ⊥),
          (p : 𝓞 K) ∉ P' →
            (Ideal.absNorm P).Coprime (Ideal.absNorm P'))
    (h_coprime :
      ∀ (P' : Ideal (𝓞 K)) (_hP'_prime : P'.IsPrime) (_hP'_ne : P' ≠ ⊥),
        (p : 𝓞 K) ∉ P' →
          ∀ a : CyclotomicUnitDelta p,
            cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    ∀ (P' : Ideal (𝓞 K)), P'.IsPrime → P' ≠ ⊥ → (p : 𝓞 K) ∉ P' →
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
        -pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := by
  intro P' hP'_prime hP'_ne hp_notin_P'
  haveI : P'.IsMaximal := Ideal.IsPrime.isMaximal hP'_prime hP'_ne
  exact kellyPrimeNegEquality_of_K2_2PrimeFactorBundleFamily_ringChar_primeTarget
    (R' := R') (ℓ := ℓ) hpℓ hp_gt_two hp_three hα_ne hαp_top hα_primary
    sourceBundle hP'_ne hp_notin_P'
    (targetChar P' hP'_prime hP'_ne hp_notin_P')
    (hcop P' hP'_prime hP'_ne hp_notin_P')
    (fun P hP => hcop_each P hP P' hP'_prime hP'_ne hp_notin_P')
    (h_coprime P' hP'_prime hP'_ne hp_notin_P')

/-- **Cyclotomic Kelly endpoint with prime target from K2-2 bundles and
ordinary target nonmembership.**

This is the quotient-`ringChar` target form specialized to the common caller
input `(ℓ : 𝓞 K) ∉ P'`. -/
theorem kellyPrimeNegEquality_of_K2_2Bundles_notMem_primeTarget
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hpℓ : p ≠ ℓ) (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (sourceBundle : ∀ P : Ideal (𝓞 K),
      P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
        K2_2PrimeFactorBundle ℓ p K R' P)
    {P' : Ideal (𝓞 K)} [P'.IsMaximal]
    (hP'_ne : P' ≠ ⊥)
    (hp_notin_P' : (p : 𝓞 K) ∉ P')
    (hℓ_notin_P' : (ℓ : 𝓞 K) ∉ P')
    (hcop : (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
            (Ideal.absNorm P'))
    (hcop_each :
      ∀ P (_hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        (Ideal.absNorm P).Coprime (Ideal.absNorm P'))
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    haveI : P'.IsPrime := inferInstance
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      -pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) :=
  kellyPrimeNegEquality_of_K2_2PrimeFactorBundleFamily_targetData
    (R' := R') (ℓ := ℓ) hpℓ hp_gt_two hp_three hα_ne hαp_top hα_primary
    sourceBundle
    (K2_2TargetData.mk_ofPrime_ringChar_notMem
      hP'_ne hp_notin_P' hℓ_notin_P')
    hcop hcop_each h_coprime

/-- **Away-from-`p` signed Kelly endpoint with target characteristic separated
by ordinary nonmembership.** -/
theorem kellyPrimeNegEquality_awayFromP_of_K2_2Bundles_notMem
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hpℓ : p ≠ ℓ) (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (sourceBundle : ∀ P : Ideal (𝓞 K),
      P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
        K2_2PrimeFactorBundle ℓ p K R' P)
    (targetNotMem :
      ∀ (P' : Ideal (𝓞 K)) (_hP'_prime : P'.IsPrime) (_hP'_ne : P' ≠ ⊥),
        (p : 𝓞 K) ∉ P' → (ℓ : 𝓞 K) ∉ P')
    (hcop :
      ∀ (P' : Ideal (𝓞 K)) (_hP'_prime : P'.IsPrime) (_hP'_ne : P' ≠ ⊥),
        (p : 𝓞 K) ∉ P' →
          (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
            (Ideal.absNorm P'))
    (hcop_each :
      ∀ P (_hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
        P' (_hP'_prime : P'.IsPrime) (_hP'_ne : P' ≠ ⊥),
          (p : 𝓞 K) ∉ P' →
            (Ideal.absNorm P).Coprime (Ideal.absNorm P'))
    (h_coprime :
      ∀ (P' : Ideal (𝓞 K)) (_hP'_prime : P'.IsPrime) (_hP'_ne : P' ≠ ⊥),
        (p : 𝓞 K) ∉ P' →
          ∀ a : CyclotomicUnitDelta p,
            cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    ∀ (P' : Ideal (𝓞 K)), P'.IsPrime → P' ≠ ⊥ → (p : 𝓞 K) ∉ P' →
      pthSymbolAtIdeal_canonical (p := p) (K := K)
          (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
        -pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) :=
  kellyPrimeNegEquality_awayFromP_of_K2_2PrimeFactorBundleFamily_targetData
    (R' := R') (ℓ := ℓ) hpℓ hp_gt_two hp_three hα_ne hαp_top hα_primary
    sourceBundle
    (fun P' hP'_prime hP'_ne hp_notin_P' =>
      haveI : P'.IsMaximal := Ideal.IsPrime.isMaximal hP'_prime hP'_ne
      K2_2TargetData.mk_ofPrime_ringChar_notMem
        hP'_ne hp_notin_P'
        (targetNotMem P' hP'_prime hP'_ne hp_notin_P'))
    hcop hcop_each h_coprime

/-- **Cyclotomic Kelly endpoint with prime target from K2-2 bundles, deriving
target nonmembership from one fixed source factor and norm coprimality.** -/
theorem kellyPrimeNegEquality_of_K2_2Bundles_sourceCoprime_primeTarget
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hpℓ : p ≠ ℓ) (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {α : 𝓞 K} (hα_ne : α ≠ 0)
    (hαp_top : Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) = ⊤)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (sourceBundle : ∀ P : Ideal (𝓞 K),
      P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
        K2_2PrimeFactorBundle ℓ p K R' P)
    (P₀ : Ideal (𝓞 K))
    (hP₀ : P₀ ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
    {P' : Ideal (𝓞 K)} [P'.IsMaximal]
    (hP'_ne : P' ≠ ⊥)
    (hp_notin_P' : (p : 𝓞 K) ∉ P')
    (hcop : (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
            (Ideal.absNorm P'))
    (hcop_each :
      ∀ P (_hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        (Ideal.absNorm P).Coprime (Ideal.absNorm P'))
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    haveI : P'.IsPrime := inferInstance
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      -pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := by
  let B₀ := sourceBundle P₀ hP₀
  letI : P₀.IsMaximal := B₀.P_max
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P₀) := B₀.alg_inst
  letI : Field (𝓞 K ⧸ P₀) := Ideal.Quotient.field P₀
  have hℓ_notin_P' : (ℓ : 𝓞 K) ∉ P' :=
    natCast_notMem_of_absNorm_coprime_of_natCast_mem
      (P := P₀) (P' := P') B₀.D.hP_bot hP'_ne B₀.D.hℓ_in_P
      (hcop_each P₀ hP₀)
  exact kellyPrimeNegEquality_of_K2_2Bundles_notMem_primeTarget
    (R' := R') (ℓ := ℓ) hpℓ hp_gt_two hp_three hα_ne hαp_top hα_primary
    sourceBundle hP'_ne hp_notin_P' hℓ_notin_P' hcop hcop_each h_coprime

end PhiPrimeElement

end Furtwaengler

end BernoulliRegular

end

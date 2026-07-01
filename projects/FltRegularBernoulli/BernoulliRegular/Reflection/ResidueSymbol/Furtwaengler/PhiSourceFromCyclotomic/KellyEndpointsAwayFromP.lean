module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.BundleFromCyclotomic
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeElement
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor
public import Mathlib.NumberTheory.NumberField.Basic
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiSourceFromCyclotomic.KellyEndpoints

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

/-- **Away-from-`p` signed Kelly endpoint deriving target nonmembership from one
fixed source factor and the per-source/target norm-coprimality hypotheses.** -/
theorem kellyPrimeNegEquality_awayFromP_of_K2_2Bundles_sourceCoprime
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
  let B₀ := sourceBundle P₀ hP₀
  letI : P₀.IsMaximal := B₀.P_max
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P₀) := B₀.alg_inst
  letI : Field (𝓞 K ⧸ P₀) := Ideal.Quotient.field P₀
  exact kellyPrimeNegEquality_awayFromP_of_K2_2Bundles_notMem
    (R' := R') (ℓ := ℓ) hpℓ hp_gt_two hp_three hα_ne hαp_top hα_primary
    sourceBundle
    (fun P' hP'_prime hP'_ne hp_notin_P' =>
      natCast_notMem_of_absNorm_coprime_of_natCast_mem
        (P := P₀) (P' := P') B₀.D.hP_bot hP'_ne B₀.D.hℓ_in_P
        (hcop_each P₀ hP₀ P' hP'_prime hP'_ne hp_notin_P'))
    hcop hcop_each h_coprime

/-- **Positive cyclotomic Kelly endpoint with prime target from reciprocal
K2-2 source-data bundles and already-bundled target data**. This is the
direct REF-18 handoff when the target-prime side has already been packaged as
`K2_2TargetData`. -/
theorem kellyPrimeEquality_of_K2_2ReciprocalPrimeFactorBundleFamily_targetData
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
        K2_2ReciprocalPrimeFactorBundle ℓ p K R' P)
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
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  refine
    kellyPrimeEquality_of_K2_2ReciprocalSourceDataFamily_cyclotomic_primeTarget_bundled
      (ℓ := ℓ) (R' := R') hp_gt_two hp_three hα_ne hαp_top
      (primePhi := fun P hP => (sourceBundle P hP).phi)
      hα_primary targetData.hP'_bot hcop ?_ h_coprime
  intro P hP
  letI : P.IsMaximal := (sourceBundle P hP).P_max
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) := (sourceBundle P hP).alg_inst
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  exact K2_2ReciprocalSourceData_phi_facts_at_targetData
    (ℓ := ℓ) (p := p) (K := K) (R' := R') hpℓ hp_gt_two hp_three
    (sourceBundle P hP).D targetData (hcop_each P hP)

/-- **Positive cyclotomic Kelly endpoint with prime target from reciprocal
K2-2 source-data bundles**. This is the direct REF-18 handoff: the reciprocal
per-prime bundle supplies the semi-primary, norm, and positive symbol facts
needed by the positive Kelly composer. -/
theorem
    kellyPrimeEquality_of_K2_2ReciprocalPrimeFactorBundleFamily_natCast_primeTarget
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
        K2_2ReciprocalPrimeFactorBundle ℓ p K R' P)
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
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) :=
  kellyPrimeEquality_of_K2_2ReciprocalPrimeFactorBundleFamily_targetData
    (R' := R') (ℓ := ℓ) hpℓ hp_gt_two hp_three hα_ne hαp_top hα_primary
    sourceBundle
    (K2_2TargetData.mk_ofOverPrime_natCast
      hP'_ne hp_notin_P' overPrime overPrime_max ell' ell'_prime
      hell'_in_overPrime h_over hℓ_ne_ℓ')
    hcop hcop_each h_coprime

/-- **Away-from-`p` universal positive Kelly endpoint from reciprocal K2-2
bundles**. The reciprocal source-bundle family gives `kellyPrimeEquality` at
every nonzero prime target `P'` for which `(p : 𝓞 K) ∉ P'`, provided the
caller supplies the corresponding bundled target data and coprimality inputs.

This is the honest universal form currently available from K2-2: the target
data itself includes `hp_notin_P'`, so primes above `p` remain part of the
separate λ-correction chain rather than being hidden in this theorem. -/
theorem kellyPrimeEquality_awayFromP_of_K2_2ReciprocalPrimeFactorBundleFamily_targetData
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
        K2_2ReciprocalPrimeFactorBundle ℓ p K R' P)
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
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := by
  intro P' hP'_prime hP'_ne hp_notin_P'
  haveI : P'.IsMaximal := Ideal.IsPrime.isMaximal hP'_prime hP'_ne
  exact kellyPrimeEquality_of_K2_2ReciprocalPrimeFactorBundleFamily_targetData
    (R' := R') (ℓ := ℓ) hpℓ hp_gt_two hp_three hα_ne hαp_top hα_primary
    sourceBundle (targetData P' hP'_prime hP'_ne hp_notin_P')
    (hcop P' hP'_prime hP'_ne hp_notin_P')
    (fun P hP => hcop_each P hP P' hP'_prime hP'_ne hp_notin_P')
    (h_coprime P' hP'_prime hP'_ne hp_notin_P')

/-- **Positive-Kelly endpoint with bundled target data from K2-2 source-data
bundles**. Takes a per-prime-factor `K2_2PrimeFactorBundle` family, a bundled
`K2_2TargetData` package for the target `P'`, and an explicit
sign-orientation equality. It first produces the signed Kelly identity from
the source/target data, then converts to the older positive convention. -/
theorem kellyPrimeEquality_of_K2_2PrimeFactorBundleFamily_targetData_signOrient
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
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P')
    (h_orient :
      -pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K)))) :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  have h_neg :=
    kellyPrimeNegEquality_of_K2_2PrimeFactorBundleFamily_targetData
      (R' := R') (ℓ := ℓ) hpℓ hp_gt_two hp_three hα_ne hαp_top hα_primary
      sourceBundle targetData hcop hcop_each h_coprime
  exact kellyPrimeEquality_of_neg_of_signOrientation
    (p := p) (K := K) h_neg h_orient

/-- **Positive-Kelly endpoint with prime target from K2-2 source-data
bundles**. Takes a per-prime-factor `K2_2PrimeFactorBundle` family plus
shared over-prime data for the target `P'` and an explicit sign-orientation
equality, packages the target as `K2_2TargetData`, then forwards to
`kellyPrimeEquality_of_K2_2PrimeFactorBundleFamily_targetData_signOrient`. -/
theorem kellyPrimeEquality_of_K2_2PrimeFactorBundleFamily_natCast_primeTarget_signOrient
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
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P')
    (h_orient :
      -pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) =
        pthSymbolAtIdeal_canonical (p := p) (K := K)
          ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K)))) :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) :=
  kellyPrimeEquality_of_K2_2PrimeFactorBundleFamily_targetData_signOrient
    (R' := R') (ℓ := ℓ) hpℓ hp_gt_two hp_three hα_ne hαp_top hα_primary
    sourceBundle
    (K2_2TargetData.mk_ofOverPrime_natCast
      hP'_ne hp_notin_P' overPrime overPrime_max ell' ell'_prime
      hell'_in_overPrime h_over hℓ_ne_ℓ')
    hcop hcop_each h_coprime h_orient

end PhiPrimeElement

end Furtwaengler

end BernoulliRegular

end

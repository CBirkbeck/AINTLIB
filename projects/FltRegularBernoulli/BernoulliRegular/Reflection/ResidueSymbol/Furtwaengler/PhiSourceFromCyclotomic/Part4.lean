module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.BundleFromCyclotomic
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeElement
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor
public import Mathlib.NumberTheory.NumberField.Basic
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiSourceFromCyclotomic.Part3

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

/-- The named reciprocal Φ candidate is semi-primary for the canonical
source-residue field. -/
theorem reciprocalPhiCandidate_isSemiPrimary_cyclotomic
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hp_gt_two : 2 < p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt (p - 1) ^ p ≠ 0)
    (h_zeta_p_int_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_p_int =
        (algebraMap (𝓞 K) (𝓞 R'))
          (BernoulliRegular.cyclotomicZetaInteger (p := p) K)) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    FLT37.IsSemiPrimary p (K := K)
      (reciprocalPhiCandidate
        (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R') S h_ne_zero) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have hp_three : 3 ≤ p := by omega
  simpa [reciprocalPhiCandidate] using
    S.phiPrimeGenDescent_isSemiPrimary
      (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1))
      h_ne_zero hp_three h_zeta_p_int_eq

/-- Cyclotomic conjugation-norm for the named reciprocal Φ candidate. -/
theorem reciprocalPhiCandidate_conj_mul_self_eq_absNorm_pow_cyclotomic
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hpℓ : p ≠ ℓ) (hp_gt_two : 2 < p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt (p - 1) ^ p ≠ 0)
    (h_zeta_p_int_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_p_int =
        (algebraMap (𝓞 K) (𝓞 R'))
          (BernoulliRegular.cyclotomicZetaInteger (p := p) K)) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    NumberField.IsCMField.ringOfIntegersComplexConj K
        (reciprocalPhiCandidate
          (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R') S h_ne_zero) *
      reciprocalPhiCandidate
        (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R') S h_ne_zero =
        (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  haveI : NumberField.IsCMField R' :=
    isCMField_of_cyclotomicExtension_pair_primes (p := p) (ℓ := ℓ) hpℓ
  let σ : 𝓞 R' →+* 𝓞 R' :=
    (NumberField.IsCMField.ringOfIntegersComplexConj R').toRingEquiv.toRingHom
  have hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (NumberField.IsCMField.ringOfIntegersComplexConj K x) := fun x =>
    upstairsComplexConj_lifts_downstairs (p := p) (ℓ := ℓ) hpℓ hp_gt_two x
  have hσζp :
      σ S.toConcreteStickelbergerSetup.zeta_p_int =
        S.toConcreteStickelbergerSetup.zeta_p_int ^ (p - 1) :=
    S.zeta_p_int_map_pow_sub_one_of_lifts_conj
      (p := p) (K := K) σ hσ_lifts_conj h_zeta_p_int_eq
  have hσζell :
      σ S.toConcreteStickelbergerSetup.zeta_ell_int =
        S.toConcreteStickelbergerSetup.zeta_ell_int ^ (ℓ - 1) := by
    simpa [σ] using
      S.toConcreteStickelbergerSetup.zeta_ell_int_complexConj_eq_pow_sub_one
  have hraw :
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (phiPrimeGenDescent S
            (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero) *
        phiPrimeGenDescent S
          (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero =
        (ℓ : 𝓞 K) ^ (S.toConcreteStickelbergerSetup.f * p) :=
    S.phiPrimeGenDescent_conj_mul_self_eq_ell_pow_of_rootAction
      (p := p) (K := K)
      (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1))
      h_ne_zero σ hσ_lifts_conj hσζp hσζell
  have h_abs :
      Ideal.absNorm P = ℓ ^ S.toConcreteStickelbergerSetup.f := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    exact S.toConcreteStickelbergerSetup.card_k
  simpa [reciprocalPhiCandidate] using
    (calc
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (phiPrimeGenDescent S
            (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero) *
        phiPrimeGenDescent S
          (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero
          = (ℓ : 𝓞 K) ^ (S.toConcreteStickelbergerSetup.f * p) := hraw
      _ = (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
            rw [h_abs, pow_mul]
            congr 1
            norm_num)

/-- Bundled semi-primary and conjugation-norm facts for the assembled
reciprocal Φ element. -/
theorem ofReciprocalPhiCandidateAtomicSplit_gamma_facts_cyclotomic
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hpℓ : p ≠ ℓ) (hp_gt_two : 2 < p)
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
        (reciprocalPhiCandidate
          (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R') S h_ne_zero))
    (he :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).ramificationIdxIn
        (𝓞 K) = 1)
    (hf :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).inertiaDegIn
        (𝓞 K) = 1)
    (h_zeta_p_int_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_p_int =
        (algebraMap (𝓞 K) (𝓞 R'))
          (BernoulliRegular.cyclotomicZetaInteger (p := p) K)) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    FLT37.IsSemiPrimary p (K := K)
        (ofReciprocalPhiCandidateAtomicSplit
          (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R') S
          h_descentPrime h_ne_zero h_exp he hf).gamma ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K
          (ofReciprocalPhiCandidateAtomicSplit
            (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R') S
            h_descentPrime h_ne_zero h_exp he hf).gamma *
        (ofReciprocalPhiCandidateAtomicSplit
          (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R') S
          h_descentPrime h_ne_zero h_exp he hf).gamma =
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  refine ⟨?_, ?_⟩
  · simpa using
      reciprocalPhiCandidate_isSemiPrimary_cyclotomic
        (ℓ := ℓ) (p := p) (K := K) (R' := R') hp_gt_two
        h_ne_zero h_zeta_p_int_eq
  · simpa using
      reciprocalPhiCandidate_conj_mul_self_eq_absNorm_pow_cyclotomic
        (ℓ := ℓ) (p := p) (K := K) (R' := R') hpℓ hp_gt_two
        h_ne_zero h_zeta_p_int_eq

/-- Positive K2/Kelly symbol identity for the assembled actual reciprocal Φ
candidate at a prime target norm-coprime to the source prime.

The conclusion is stated for
`ofReciprocalPhiCandidateAtomicSplit`, so the Φ generator is the named
`reciprocalPhiCandidate`; the K2 source and target packages are constructed
only inside the proof. -/
theorem ofReciprocalPhiCandidateAtomicSplit_symbol_pos_cyclotomic_sourceCoprime
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (hP_bot : P ≠ ⊥)
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
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
        (reciprocalPhiCandidate
          (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R') S h_ne_zero))
    (he :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).ramificationIdxIn
        (𝓞 K) = 1)
    (hf :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).inertiaDegIn
        (𝓞 K) = 1)
    (h_zeta_k_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_k = canonicalResidueZetaP (p := p) (K := K) P)
    (h_zeta_p_int_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_p_int =
        (algebraMap (𝓞 K) (𝓞 R'))
          (BernoulliRegular.cyclotomicZetaInteger (p := p) K))
    {P' : Ideal (𝓞 K)}
    (hP'_prime : P'.IsPrime)
    (hP'_bot : P' ≠ ⊥)
    (hp_notin_P' : (p : 𝓞 K) ∉ P')
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm P')) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    PhiPrimeSymbolIdentityPos (p := p) (K := K)
      (ofReciprocalPhiCandidateAtomicSplit
        (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R') S
        h_descentPrime h_ne_zero h_exp he hf) P' := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : P.IsPrime := (show P.IsMaximal from inferInstance).isPrime
  letI : P'.IsPrime := hP'_prime
  letI : P'.IsMaximal := Ideal.IsPrime.isMaximal hP'_prime hP'_bot
  let h_span :
      Ideal.span ({reciprocalPhiCandidate
          (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R') S h_ne_zero} :
            Set (𝓞 K)) =
        stickelbergerIdeal (p := p) (K := K) P :=
    reciprocalPhiCandidate_span_of_atomic_split
      (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R') S
      h_descentPrime h_ne_zero h_exp he hf
  let D : K2_2ReciprocalSourceData
      (ℓ := ℓ) (p := p) (K := K) (R' := R') S :=
    { hP_bot := hP_bot
      hℓ_in_P := hℓ_in_P
      hp_notin_P := hp_notin_P
      h_zeta_k_eq := h_zeta_k_eq
      h_zeta_p_int_eq := h_zeta_p_int_eq
      h_ne_zero := h_ne_zero
      h_span := by
        simpa [reciprocalPhiCandidate] using h_span }
  let T : K2_2TargetData (ℓ := ℓ) (p := p) (K := K) (R' := R') P' :=
    K2_2TargetData.mk_ofPrime_ringChar_notMem
      (ℓ := ℓ) (p := p) (K := K) (R' := R')
      hP'_bot hp_notin_P'
      (natCast_notMem_of_absNorm_coprime_of_natCast_mem
        (P := P) (P' := P') hP_bot hP'_bot hℓ_in_P hcop)
  unfold PhiPrimeSymbolIdentityPos
  have hsym := K2_2ReciprocalSourceData.symbol_eq_norm_symbol D T hcop
  simpa [K2_2ReciprocalSourceData.phi, reciprocalPhiCandidate,
    Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] using hsym

/-- **Bundled Kelly endpoint with prime target**: same as
`kellyPrimeNegEquality_of_K2_2SourceDataFamily_cyclotomic_primeTarget`,
but the three per-prime hypotheses (`h_prime_semi`, `h_prime_norm`,
`h_prime_symbol_at_P'`) are folded into a single per-prime conjunction
`h_prime_facts`. This is the natural call shape when the per-prime
facts are produced together by `K2_2SourceData_phi_facts_at_primeTarget`. -/
theorem kellyPrimeNegEquality_of_K2_2SourceDataFamily_cyclotomic_primeTarget_bundled
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
          PhiPrimeSymbolIdentity (p := p) (K := K)
            (primePhi P hP) P')
    (h_coprime : ∀ a : CyclotomicUnitDelta p,
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ α ∉ P') :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    pthSymbolAtIdeal_canonical (p := p) (K := K)
        (stickelbergerPrincipalGen (p := p) (K := K) α) P' =
      -pthSymbolAtIdeal_canonical (p := p) (K := K)
        ((P'.absNorm : ℤ) : 𝓞 K) (Ideal.span ({α} : Set (𝓞 K))) :=
  kellyPrimeNegEquality_of_K2_2SourceDataFamily_cyclotomic_primeTarget
    (ℓ := ℓ) (R' := R') hp_gt_two hp_three hα_ne hαp_top primePhi
    (fun P hP => (h_prime_facts P hP).1)
    (fun P hP => (h_prime_facts P hP).2.1)
    hα_primary hP'_ne hcop
    (fun P hP => (h_prime_facts P hP).2.2)
    h_coprime

/-- **All three K2-2-derivable per-prime facts at a fixed prime target**
for a single `K2_2SourceData`, using already-bundled target data. Bundles
`K2_2SourceData_phi_facts_cyclotomic` (semi-primary + conjugation-norm)
with `PhiPrimeSymbolIdentity.of_K2_2SourceData` at the target prime `Q`. -/
theorem K2_2SourceData_phi_facts_at_targetData
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hpℓ : p ≠ ℓ) (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2SourceData S)
    {Q : Ideal (𝓞 K)} [Q.IsMaximal]
    (T : K2_2TargetData (ℓ := ℓ) (p := p) (K := K) (R' := R') Q)
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm Q)) :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    FLT37.IsSemiPrimary p (K := K) D.phi.gamma ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
        (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p ∧
      PhiPrimeSymbolIdentity (p := p) (K := K) D.phi Q := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  obtain ⟨h_semi, h_norm⟩ :=
    K2_2SourceData_phi_facts_cyclotomic (ℓ := ℓ) (p := p) (K := K) (R' := R')
      hpℓ hp_gt_two hp_three D
  refine ⟨h_semi, h_norm, ?_⟩
  exact PhiPrimeSymbolIdentity.of_K2_2SourceData
    (ℓ := ℓ) (p := p) (K := K) (R' := R') D T hcop

/-- **All three K2-2-derivable per-prime facts at a fixed prime target**
for a single `K2_2SourceData`. Bundles `K2_2SourceData_phi_facts_cyclotomic`
(semi-primary + conjugation-norm) with `PhiPrimeSymbolIdentity.of_K2_2SourceData_natCast`
(per-prime Φ-symbol identity at the target prime `Q`). The over-prime data
in `R'` for the target `Q` is supplied inline. -/
theorem K2_2SourceData_phi_facts_at_primeTarget
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hpℓ : p ≠ ℓ) (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2SourceData S)
    {Q : Ideal (𝓞 K)} [Q.IsMaximal]
    (hQ_bot : Q ≠ ⊥)
    (hp_notin_Q : (p : 𝓞 K) ∉ Q)
    (overPrime : Ideal (𝓞 R'))
    (overPrime_max : overPrime.IsMaximal)
    (ell' : ℕ) (ell'_prime : Fact ell'.Prime)
    (hell'_in_overPrime : (ell' : 𝓞 R') ∈ overPrime)
    (h_over : overPrime.comap (algebraMap (𝓞 K) (𝓞 R')) = Q)
    (hℓ_ne_ℓ' : ℓ ≠ ell')
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm Q)) :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    FLT37.IsSemiPrimary p (K := K) D.phi.gamma ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
        (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p ∧
      PhiPrimeSymbolIdentity (p := p) (K := K) D.phi Q :=
  K2_2SourceData_phi_facts_at_targetData
    (ℓ := ℓ) (p := p) (K := K) (R' := R')
    hpℓ hp_gt_two hp_three D
    (K2_2TargetData.mk_ofOverPrime_natCast
      hQ_bot hp_notin_Q overPrime overPrime_max ell' ell'_prime
      hell'_in_overPrime h_over hℓ_ne_ℓ')
    hcop

/-- **All three reciprocal K2-2-derivable per-prime facts at a fixed prime
target**, using already-bundled target data. Bundles reciprocal
semi-primary, conjugation-norm, and the positive Φ-symbol identity at the
target prime `Q`. -/
theorem K2_2ReciprocalSourceData_phi_facts_at_targetData
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hpℓ : p ≠ ℓ) (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2ReciprocalSourceData S)
    {Q : Ideal (𝓞 K)} [Q.IsMaximal]
    (T : K2_2TargetData (ℓ := ℓ) (p := p) (K := K) (R' := R') Q)
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm Q)) :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    FLT37.IsSemiPrimary p (K := K) D.phi.gamma ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
        (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p ∧
      PhiPrimeSymbolIdentityPos (p := p) (K := K) D.phi Q := by
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  obtain ⟨h_semi, h_norm⟩ :=
    K2_2ReciprocalSourceData_phi_facts_cyclotomic
      (ℓ := ℓ) (p := p) (K := K) (R' := R')
      hpℓ hp_gt_two hp_three D
  refine ⟨h_semi, h_norm, ?_⟩
  exact PhiPrimeSymbolIdentityPos.of_K2_2ReciprocalSourceData
    (ℓ := ℓ) (p := p) (K := K) (R' := R') D T hcop

/-- **All three reciprocal K2-2-derivable per-prime facts at a fixed prime
target**. Bundles reciprocal semi-primary, conjugation-norm, and the positive
Φ-symbol identity at the target prime `Q`. -/
theorem K2_2ReciprocalSourceData_phi_facts_at_primeTarget
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    (hpℓ : p ≠ ℓ) (hp_gt_two : 2 < p) (hp_three : 3 ≤ p)
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2ReciprocalSourceData S)
    {Q : Ideal (𝓞 K)} [Q.IsMaximal]
    (hQ_bot : Q ≠ ⊥)
    (hp_notin_Q : (p : 𝓞 K) ∉ Q)
    (overPrime : Ideal (𝓞 R'))
    (overPrime_max : overPrime.IsMaximal)
    (ell' : ℕ) (ell'_prime : Fact ell'.Prime)
    (hell'_in_overPrime : (ell' : 𝓞 R') ∈ overPrime)
    (h_over : overPrime.comap (algebraMap (𝓞 K) (𝓞 R')) = Q)
    (hℓ_ne_ℓ' : ℓ ≠ ell')
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm Q)) :
    haveI : NumberField.IsCMField K :=
      IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
    FLT37.IsSemiPrimary p (K := K) D.phi.gamma ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
        (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p ∧
      PhiPrimeSymbolIdentityPos (p := p) (K := K) D.phi Q :=
  K2_2ReciprocalSourceData_phi_facts_at_targetData
    (ℓ := ℓ) (p := p) (K := K) (R' := R')
    hpℓ hp_gt_two hp_three D
    (K2_2TargetData.mk_ofOverPrime_natCast
      hQ_bot hp_notin_Q overPrime overPrime_max ell' ell'_prime
      hell'_in_overPrime h_over hℓ_ne_ℓ')
    hcop

/-- **Per-prime K2-2 source-data bundle**, packaging the typeclass
instances and source data needed by the Kelly composer family. The
fields `P_max` and `alg_inst` carry the maximality and `(ZMod ℓ)`-algebra
instances on the residue field, and `S`/`D` are the Dwork-bundle and
K2-2 source data over those instances. -/
structure K2_2PrimeFactorBundle
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
  /-- The K2-2 source data on `S`. -/
  D : letI : P.IsMaximal := P_max
      letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) := alg_inst
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      K2_2SourceData (ℓ := ℓ) (p := p) (K := K) (R' := R') S

namespace K2_2PrimeFactorBundle

/-- The actual prime Φ element associated to a `K2_2PrimeFactorBundle`. -/
noncomputable def phi
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] [IsCyclotomicExtension {p, ℓ} ℚ R']
    {P : Ideal (𝓞 K)} (B : K2_2PrimeFactorBundle ℓ p K R' P) :
    PhiPrimeElement (p := p) (K := K) P :=
  letI : P.IsMaximal := B.P_max
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) := B.alg_inst
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  B.D.phi

/-- Build a prime-factor bundle from the canonical trace-form split prime data
and the exact-exponent theorem for the index-one Φ element. -/
noncomputable def ofCanonicalTraceForm_atomic_split
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
    K2_2PrimeFactorBundle ℓ p K R' P where
  P_max := inferInstance
  alg_inst :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  S := S
  D :=
    K2_2SourceData.ofCanonicalTraceForm_atomic_split
      (P := P) (Q := Q) (iso := iso)
      hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p hQ_in h_compat h_trace
      h_descentPrime h_ne_zero h_exp he hf

/-- Prime-factor bundle constructor that derives the descent-prime equality
from the canonical trace-form identity and accepts split conditions directly on
`P`. -/
noncomputable def ofCanonicalTraceForm_atomic_split_atPrime
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
    K2_2PrimeFactorBundle ℓ p K R' P where
  P_max := inferInstance
  alg_inst :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  S := S
  D :=
    K2_2SourceData.ofCanonicalTraceForm_atomic_split_atPrime
      (P := P) (Q := Q) (iso := iso)
      hℓ_in_P hp_notin_P hP_ne_bot hℓ_ne_p hQ_in h_compat h_trace
      h_ne_zero h_exp he hf

/-- Prime-factor bundle constructor that derives both the descent-prime equality
and `ℓ ≠ p` from the source-prime membership/nonmembership hypotheses. -/
noncomputable def ofCanonicalTraceForm_atomic_split_atPrime_of_mem_notMem
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
    K2_2PrimeFactorBundle ℓ p K R' P where
  P_max := inferInstance
  alg_inst :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  S := S
  D :=
    K2_2SourceData.ofCanonicalTraceForm_atomic_split_atPrime_of_mem_notMem
      (P := P) (Q := Q) (iso := iso)
      hℓ_in_P hp_notin_P hP_ne_bot hQ_in h_compat h_trace
      h_ne_zero h_exp he hf

/-- Prime-factor bundle constructor that derives `P ≠ ⊥`, the descent-prime
equality, and `ℓ ≠ p` from the source-prime hypotheses. -/
noncomputable def ofCanonicalTraceForm_atomic_split_atPrime_of_mem_notMem_maximal
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
    K2_2PrimeFactorBundle ℓ p K R' P where
  P_max := inferInstance
  alg_inst :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  S := S
  D :=
    K2_2SourceData.ofCanonicalTraceForm_atomic_split_atPrime_of_mem_notMem_maximal
      (P := P) (Q := Q) (iso := iso)
      hℓ_in_P hp_notin_P hQ_in h_compat h_trace h_ne_zero h_exp he hf

/-- Prime-factor bundle constructor that accepts splitting of the rational
prime ideal `(ℓ)` instead of splitting written on `P.under ℤ`. -/
noncomputable def ofCanonicalTraceForm_atomic_split_atSpan_of_mem_notMem_maximal
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
    K2_2PrimeFactorBundle ℓ p K R' P where
  P_max := inferInstance
  alg_inst :=
    CyclotomicLocalSetup.algebra_zmod_residueField (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  S := S
  D :=
    K2_2SourceData.ofCanonicalTraceForm_atomic_split_atSpan_of_mem_notMem_maximal
      (P := P) (Q := Q) (iso := iso)
      hℓ_in_P hp_notin_P hQ_in h_compat h_trace h_ne_zero h_exp he hf

end K2_2PrimeFactorBundle
end PhiPrimeElement

end Furtwaengler

end BernoulliRegular

end

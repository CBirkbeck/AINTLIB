module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.ArbitraryDegreeSourceData
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor.Part2

/-!
# Ireland--Rosen prime source theorem

This file starts the direct Ireland--Rosen route for the prime source appearing
in Ch. 14, Sec. 2, Theorem 1.

The element is the actual reciprocal-index descended Gauss-sum element
`S.phiPrimeGenDescent ... (p - 1)`, not an arbitrary generator of the same
Stickelberger ideal.  The source theorem below uses the arbitrary-residue-degree
Dwork/Stickelberger calculation
`repeatedExactOnOrbit_phiPrimeGenDescent_sub_one_of_f_eq_orderOf`; it does not
use one-sided Kummer reciprocity, a Hilbert-symbol package, or any Kelly
endpoint.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField NumberField.IsCMField

namespace BernoulliRegular

namespace Furtwaengler

namespace IrelandRosen

universe u v

/-- The actual reciprocal-index prime Φ element for the Ireland--Rosen source
prime, constructed from the conductor-flexible Gauss-sum descent and the
general residue-degree Stickelberger exponent computation.

The hypothesis `hf` is the full residue-degree statement
`S.f = orderOf (ℓ mod p)`, not a split/order-one shortcut. -/
noncomputable def reciprocalPrimePhiElement_of_f_eq_orderOf
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {ℓ * (Fintype.card (𝓞 K ⧸ P) - 1)} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_psi :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.IsGalPsiShiftCompatible)
    (h_descentPrime :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.descentPrime = P)
    (h_source_coprime : ℓ.Coprime (Fintype.card (𝓞 K ⧸ P) - 1))
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt (p - 1) ^ p ≠ 0)
    (hℓp : ℓ.Coprime p)
    (hf :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.f = orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p))
    (he :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.descentRamificationIdx = ℓ - 1) :
    PhiPrimeElement (p := p) (K := K) P := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  refine PhiPrimeElement.ofFlexibleReciprocalPhiCandidateRepeatedExactOnOrbit
    (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R')
    S h_psi h_descentPrime h_ne_zero ?_
  simpa [PhiPrimeElement.flexibleReciprocalPhiCandidate] using
    S.repeatedExactOnOrbit_phiPrimeGenDescent_sub_one_of_f_eq_orderOf
      h_psi h_source_coprime h_ne_zero hℓp hf he

@[simp]
theorem reciprocalPrimePhiElement_of_f_eq_orderOf_gamma
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {ℓ * (Fintype.card (𝓞 K ⧸ P) - 1)} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_psi :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.IsGalPsiShiftCompatible)
    (h_descentPrime :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.descentPrime = P)
    (h_source_coprime : ℓ.Coprime (Fintype.card (𝓞 K ⧸ P) - 1))
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt (p - 1) ^ p ≠ 0)
    (hℓp : ℓ.Coprime p)
    (hf :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.f = orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p))
    (he :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.descentRamificationIdx = ℓ - 1) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    (reciprocalPrimePhiElement_of_f_eq_orderOf
        (ℓ := ℓ) (p := p) (K := K) (P := P) (R' := R')
        S h_psi h_descentPrime h_source_coprime h_ne_zero hℓp hf he).gamma =
      PhiPrimeElement.flexibleReciprocalPhiCandidate
        (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R')
        S h_psi h_ne_zero := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  rfl

/-- The prime source element is nonzero. -/
theorem reciprocalPrimePhiElement_gamma_ne_zero
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {ℓ * (Fintype.card (𝓞 K ⧸ P) - 1)} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_psi :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.IsGalPsiShiftCompatible)
    (h_descentPrime :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.descentPrime = P)
    (h_source_coprime : ℓ.Coprime (Fintype.card (𝓞 K ⧸ P) - 1))
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt (p - 1) ^ p ≠ 0)
    (hℓp : ℓ.Coprime p)
    (hf :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.f = orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p))
    (he :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.descentRamificationIdx = ℓ - 1) :
    (reciprocalPrimePhiElement_of_f_eq_orderOf
        (ℓ := ℓ) (p := p) (K := K) (P := P) (R' := R')
        S h_psi h_descentPrime h_source_coprime h_ne_zero hℓp hf he).gamma ≠ 0 :=
  (reciprocalPrimePhiElement_of_f_eq_orderOf
    (ℓ := ℓ) (p := p) (K := K) (P := P) (R' := R')
    S h_psi h_descentPrime h_source_coprime h_ne_zero hℓp hf he).gamma_ne_zero

/-- The prime source element generates the Stickelberger ideal. -/
theorem reciprocalPrimePhiElement_span_eq_stickelbergerIdeal
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {ℓ * (Fintype.card (𝓞 K ⧸ P) - 1)} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_psi :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.IsGalPsiShiftCompatible)
    (h_descentPrime :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.descentPrime = P)
    (h_source_coprime : ℓ.Coprime (Fintype.card (𝓞 K ⧸ P) - 1))
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt (p - 1) ^ p ≠ 0)
    (hℓp : ℓ.Coprime p)
    (hf :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.f = orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p))
    (he :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.descentRamificationIdx = ℓ - 1) :
    Ideal.span ({(reciprocalPrimePhiElement_of_f_eq_orderOf
        (ℓ := ℓ) (p := p) (K := K) (P := P) (R' := R')
        S h_psi h_descentPrime h_source_coprime h_ne_zero hℓp hf he).gamma} :
          Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P :=
  (reciprocalPrimePhiElement_of_f_eq_orderOf
    (ℓ := ℓ) (p := p) (K := K) (P := P) (R' := R')
    S h_psi h_descentPrime h_source_coprime h_ne_zero hℓp hf he).span_gamma

/-- The prime source element is semi-primary. -/
theorem reciprocalPrimePhiElement_isSemiPrimary
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {ℓ * (Fintype.card (𝓞 K ⧸ P) - 1)} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (hp_three : 3 ≤ p)
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_psi :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.IsGalPsiShiftCompatible)
    (h_descentPrime :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.descentPrime = P)
    (h_source_coprime : ℓ.Coprime (Fintype.card (𝓞 K ⧸ P) - 1))
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt (p - 1) ^ p ≠ 0)
    (hℓp : ℓ.Coprime p)
    (hf :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.f = orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p))
    (he :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.descentRamificationIdx = ℓ - 1)
    (h_zeta_p_int_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_p_int =
        (algebraMap (𝓞 K) (𝓞 R'))
          (cyclotomicZetaInteger (p := p) K)) :
    FLT37.IsSemiPrimary p (K := K)
      (reciprocalPrimePhiElement_of_f_eq_orderOf
        (ℓ := ℓ) (p := p) (K := K) (P := P) (R' := R')
        S h_psi h_descentPrime h_source_coprime h_ne_zero hℓp hf he).gamma := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  simpa [reciprocalPrimePhiElement_of_f_eq_orderOf,
    PhiPrimeElement.ofFlexibleReciprocalPhiCandidateRepeatedExactOnOrbit,
    PhiPrimeElement.flexibleReciprocalPhiCandidate] using
    S.phiPrimeGenDescent_isSemiPrimary h_psi
      (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1))
      h_ne_zero hp_three h_zeta_p_int_eq

/-- Conjugation-norm identity for the prime source element. -/
theorem reciprocalPrimePhiElement_conj_mul_self_eq_absNorm_pow
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K] [IsCMField K]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {ℓ * (Fintype.card (𝓞 K ⧸ P) - 1)} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_psi :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.IsGalPsiShiftCompatible)
    (h_descentPrime :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.descentPrime = P)
    (h_source_coprime : ℓ.Coprime (Fintype.card (𝓞 K ⧸ P) - 1))
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt (p - 1) ^ p ≠ 0)
    (hℓp : ℓ.Coprime p)
    (hf :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.f = orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p))
    (he :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.descentRamificationIdx = ℓ - 1)
    (h_zeta_p_int_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_p_int =
        (algebraMap (𝓞 K) (𝓞 R'))
          (cyclotomicZetaInteger (p := p) K))
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (hσζell :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      σ S.concrete.zeta_ell_int =
        S.concrete.zeta_ell_int ^ (ℓ - 1)) :
    ringOfIntegersComplexConj K
        (reciprocalPrimePhiElement_of_f_eq_orderOf
          (ℓ := ℓ) (p := p) (K := K) (P := P) (R' := R')
          S h_psi h_descentPrime h_source_coprime h_ne_zero hℓp hf he).gamma *
      (reciprocalPrimePhiElement_of_f_eq_orderOf
        (ℓ := ℓ) (p := p) (K := K) (P := P) (R' := R')
        S h_psi h_descentPrime h_source_coprime h_ne_zero hℓp hf he).gamma =
      (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have h_zeta_p_int_eq' :
      S.concrete.zeta_p_int =
        (algebraMap (𝓞 K) (𝓞 R'))
          (cyclotomicZetaInteger (p := p) K) := by
    simpa [ConductorFlexibleFullTeichStickelbergerSetup.concrete,
      ConductorFlexibleTraceFormStickelbergerSetup.concrete] using h_zeta_p_int_eq
  have hσζp :
      σ S.concrete.zeta_p_int =
        S.concrete.zeta_p_int ^ (p - 1) :=
    S.zeta_p_int_map_pow_sub_one_of_lifts_conj
      (p := p) (K := K) σ hσ_lifts_conj h_zeta_p_int_eq'
  have hraw :
      ringOfIntegersComplexConj K
          (S.phiPrimeGenDescent h_psi
            (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1))
            h_ne_zero) *
          S.phiPrimeGenDescent h_psi
            (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1))
            h_ne_zero =
        (ℓ : 𝓞 K) ^ (S.concrete.f * p) :=
    S.phiPrimeGenDescent_conj_mul_self_eq_ell_pow_of_rootAction
      (p := p) (K := K) h_psi
      (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1))
      h_ne_zero σ hσ_lifts_conj hσζp hσζell
  have h_abs :
      Ideal.absNorm P = ℓ ^ S.concrete.f := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    exact S.concrete.card_k
  change
    ringOfIntegersComplexConj K
          (PhiPrimeElement.flexibleReciprocalPhiCandidate
            (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R')
            S h_psi h_ne_zero) *
        PhiPrimeElement.flexibleReciprocalPhiCandidate
          (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R')
          S h_psi h_ne_zero =
      (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p
  calc
    ringOfIntegersComplexConj K
          (PhiPrimeElement.flexibleReciprocalPhiCandidate
            (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R')
            S h_psi h_ne_zero) *
        PhiPrimeElement.flexibleReciprocalPhiCandidate
          (ℓ := ℓ) (p := p) (k := 𝓞 K ⧸ P) (K := K) (R' := R')
          S h_psi h_ne_zero
        = (ℓ : 𝓞 K) ^ (S.concrete.f * p) := by
          simpa [PhiPrimeElement.flexibleReciprocalPhiCandidate] using hraw
    _ = (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
          rw [h_abs, pow_mul]
          congr 1
          norm_num

/-- Frobenius/residue-symbol identity for the prime source element. -/
theorem reciprocalPrimePhiElement_symbol_eq_norm_symbol
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [P.IsMaximal]
    [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {ℓ * (Fintype.card (𝓞 K ⧸ P) - 1)} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_psi :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.IsGalPsiShiftCompatible)
    (h_descentPrime :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.descentPrime = P)
    (h_source_coprime : ℓ.Coprime (Fintype.card (𝓞 K ⧸ P) - 1))
    (h_zeta_k_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_k = canonicalResidueZetaP (p := p) (K := K) P)
    (h_zeta_p_int_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_p_int =
        (algebraMap (𝓞 K) (𝓞 R'))
          (cyclotomicZetaInteger (p := p) K))
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt (p - 1) ^ p ≠ 0)
    (hℓp : ℓ.Coprime p)
    (hf :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.f = orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p))
    (he :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.descentRamificationIdx = ℓ - 1)
    {Q : Ideal (𝓞 K)} (hQ_bot : Q ≠ ⊥) [Q.IsMaximal]
    (hp_notin_Q : (p : 𝓞 K) ∉ Q)
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm Q))
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = Q)
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hℓ_ne_ℓ' : ℓ ≠ ℓ') :
    pthSymbolAtPrime_canonical (p := p) (K := K)
        (reciprocalPrimePhiElement_of_f_eq_orderOf
          (ℓ := ℓ) (p := p) (K := K) (P := P) (R' := R')
          S h_psi h_descentPrime h_source_coprime h_ne_zero hℓp hf he).gamma Q =
      pthSymbolAtPrime_canonical (p := p) (K := K)
        (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  haveI : P.IsPrime := (show P.IsMaximal from inferInstance).isPrime
  haveI : Q.IsPrime := (show Q.IsMaximal from inferInstance).isPrime
  let Φ : PhiPrimeElement (p := p) (K := K) P :=
    reciprocalPrimePhiElement_of_f_eq_orderOf
      (ℓ := ℓ) (p := p) (K := K) (P := P) (R' := R')
      S h_psi h_descentPrime h_source_coprime h_ne_zero hℓp hf he
  have h_phi_notin_Q :
      S.phiPrimeGenDescent h_psi
        (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero ∉ Q := by
    have h_notin := PhiPrimeElement.gamma_notMem_of_absNorm_coprime
      (p := p) (K := K) Φ hP_bot hQ_bot hcop
    simpa [Φ, reciprocalPrimePhiElement_of_f_eq_orderOf,
      PhiPrimeElement.ofFlexibleReciprocalPhiCandidateRepeatedExactOnOrbit,
      PhiPrimeElement.flexibleReciprocalPhiCandidate] using h_notin
  have h_apex := S.K2_2_path_a_pthSymbol_of_zeta_choices
    hP_bot hℓ_in_P hp_notin_P h_psi h_zeta_k_eq h_zeta_p_int_eq
    (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero
    hQ_bot hp_notin_Q h_phi_notin_Q h_over hℓ_ne_ℓ'
  have hN :
      Fintype.card (𝓞 K ⧸ Q) = Ideal.absNorm Q := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have h_apex' :
      pthSymbolAtPrime_canonical (p := p) (K := K)
          (S.phiPrimeGenDescent h_psi
            (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero) Q =
        pthSymbolAtPrime_canonical (p := p) (K := K)
          (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P := by
    rw [h_apex, hN]
    have hp_sub_one_cast : ((p - 1 : ℕ) : ZMod p) = -1 := by
      have hp_one : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
      rw [Nat.cast_sub hp_one, Nat.cast_one]
      simp
    rw [hp_sub_one_cast]
    ring
  simpa [Φ, reciprocalPrimePhiElement_of_f_eq_orderOf,
    PhiPrimeElement.ofFlexibleReciprocalPhiCandidateRepeatedExactOnOrbit,
    PhiPrimeElement.flexibleReciprocalPhiCandidate] using h_apex'

/-- Prop-form of the positive prime symbol identity, for later product
assembly. -/
theorem reciprocalPrimePhiElement_symbolIdentityPos
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [P.IsMaximal]
    [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {ℓ * (Fintype.card (𝓞 K ⧸ P) - 1)} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_psi :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.IsGalPsiShiftCompatible)
    (h_descentPrime :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.descentPrime = P)
    (h_source_coprime : ℓ.Coprime (Fintype.card (𝓞 K ⧸ P) - 1))
    (h_zeta_k_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_k = canonicalResidueZetaP (p := p) (K := K) P)
    (h_zeta_p_int_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_p_int =
        (algebraMap (𝓞 K) (𝓞 R'))
          (cyclotomicZetaInteger (p := p) K))
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt (p - 1) ^ p ≠ 0)
    (hℓp : ℓ.Coprime p)
    (hf :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.f = orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p))
    (he :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.descentRamificationIdx = ℓ - 1)
    {Q : Ideal (𝓞 K)} (hQ_bot : Q ≠ ⊥) [Q.IsMaximal]
    (hp_notin_Q : (p : 𝓞 K) ∉ Q)
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm Q))
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = Q)
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hℓ_ne_ℓ' : ℓ ≠ ℓ') :
    PhiPrimeElement.PhiPrimeSymbolIdentityPos (p := p) (K := K)
      (reciprocalPrimePhiElement_of_f_eq_orderOf
        (ℓ := ℓ) (p := p) (K := K) (P := P) (R' := R')
        S h_psi h_descentPrime h_source_coprime h_ne_zero hℓp hf he) Q := by
  unfold PhiPrimeElement.PhiPrimeSymbolIdentityPos
  exact reciprocalPrimePhiElement_symbol_eq_norm_symbol
    (ℓ := ℓ) (p := p) (K := K) (P := P) hP_bot hℓ_in_P hp_notin_P
    (R' := R') S h_psi h_descentPrime h_source_coprime
    h_zeta_k_eq h_zeta_p_int_eq h_ne_zero hℓp hf he
    hQ_bot hp_notin_Q hcop h_over hℓ_ne_ℓ'

end IrelandRosen

end Furtwaengler

end BernoulliRegular

end

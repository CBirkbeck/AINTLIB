module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.IrelandRosen.IdealNorm

/-!
# Ireland--Rosen arbitrary-degree prime family

This file assembles the per-prime Ireland--Rosen source theorem over the
actual normalized factors of `(α)`.  The input for each source prime is the
conductor-flexible setup data consumed by `IrelandRosen.PrimeSource`; the
output is exactly the `primePhi` family and three concrete fact families used
by the exact Theorem 1 proof.

No one-sided Kummer reciprocity, Kelly endpoint, target proposition, split
prime, or order-one assumption is used here.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid
open NumberField NumberField.IsCMField

namespace BernoulliRegular

namespace Furtwaengler

namespace IrelandRosen

universe u v

/-- Flexible target data from a target prime using an actual over-prime and
the quotient ring characteristic.  This is the conductor-flexible analogue of
the old pair-cyclotomic target-data constructor. -/
noncomputable def flexibleTargetDataOfOverPrimeRingChar
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R']
    {Q : Ideal (𝓞 K)} [Q.IsMaximal]
    (hQ_bot : Q ≠ ⊥)
    (hp_notin_Q : (p : 𝓞 K) ∉ Q)
    (overPrime : Ideal (𝓞 R'))
    (overPrime_max : overPrime.IsMaximal)
    (h_over : overPrime.comap (algebraMap (𝓞 K) (𝓞 R')) = Q)
    (hℓ_ne_char : ℓ ≠ ringChar (𝓞 R' ⧸ overPrime)) :
    PhiPrimeElement.K2_2FlexibleTargetData
      (ℓ := ℓ) (p := p) (K := K) (R' := R') Q := by
  letI : overPrime.IsMaximal := overPrime_max
  letI : Field (𝓞 R' ⧸ overPrime) := Ideal.Quotient.field overPrime
  letI : Fact (Nat.Prime (ringChar (𝓞 R' ⧸ overPrime))) :=
    ⟨CharP.prime_ringChar (𝓞 R' ⧸ overPrime)⟩
  exact
    { hP'_bot := hQ_bot
      hp_notin_P' := hp_notin_Q
      overPrime := overPrime
      overPrime_max := overPrime_max
      ell' := ringChar (𝓞 R' ⧸ overPrime)
      ell'_prime := inferInstance
      char_over := ringChar.charP (𝓞 R' ⧸ overPrime)
      h_over := h_over
      hℓ_ne_ℓ' := hℓ_ne_char }

/-- If the target prime does not contain the source rational prime `ℓ`, then
the actual residue characteristic of any over-prime is not `ℓ`. -/
theorem ringChar_ne_of_natCast_notMem_comap
    {K : Type u} [Field K] [NumberField K]
    {R' : Type v} [Field R'] [NumberField R']
    [Algebra K R'] [IsScalarTower ℚ K R']
    {Q : Ideal (𝓞 K)} {overPrime : Ideal (𝓞 R')}
    (h_over : overPrime.comap (algebraMap (𝓞 K) (𝓞 R')) = Q)
    {ℓ : ℕ} (hℓ_notin_Q : (ℓ : 𝓞 K) ∉ Q) :
    ℓ ≠ ringChar (𝓞 R' ⧸ overPrime) := by
  intro hℓ_eq_char
  apply hℓ_notin_Q
  rw [← h_over, Ideal.mem_comap]
  have hmem_over : (ℓ : 𝓞 R') ∈ overPrime := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change ((ℓ : 𝓞 R' ⧸ overPrime)) = 0
    rw [hℓ_eq_char]
    exact ringChar.Nat.cast_ringChar
  simpa [map_natCast] using hmem_over

/-- Flexible target data from a target prime by going up and taking the actual
quotient characteristic. -/
noncomputable def flexibleTargetDataOfPrimeRingCharNotMem
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R']
    {Q : Ideal (𝓞 K)} [Q.IsMaximal]
    (hQ_bot : Q ≠ ⊥)
    (hp_notin_Q : (p : 𝓞 K) ∉ Q)
    (hℓ_notin_Q : (ℓ : 𝓞 K) ∉ Q) :
    PhiPrimeElement.K2_2FlexibleTargetData
      (ℓ := ℓ) (p := p) (K := K) (R' := R') Q := by
  let h_exists := exists_maximal_over_of_finite_extension (K := K) (R' := R') Q
  let overPrime : Ideal (𝓞 R') := Classical.choose h_exists
  have h_overPrime : overPrime.IsMaximal ∧
      overPrime.comap (algebraMap (𝓞 K) (𝓞 R')) = Q :=
    Classical.choose_spec h_exists
  exact
    flexibleTargetDataOfOverPrimeRingChar
      (ℓ := ℓ) (p := p) (K := K) (R' := R')
      hQ_bot hp_notin_Q overPrime h_overPrime.1 h_overPrime.2
      (ringChar_ne_of_natCast_notMem_comap h_overPrime.2 hℓ_notin_Q)

/-- If a source prime `P` contains `(ℓ : 𝓞 K)` and the rational norms of `P`
and `Q` are coprime, then the target prime `Q` cannot contain `(ℓ : 𝓞 K)`. -/
theorem natCast_notMem_of_absNorm_coprime_of_natCast_mem
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
    {K : Type u} [Field K] [NumberField K]
    {P Q : Ideal (𝓞 K)} [P.IsPrime] [Q.IsPrime]
    (hP_ne : P ≠ ⊥) (hQ_ne : Q ≠ ⊥)
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm Q)) :
    (ℓ : 𝓞 K) ∉ Q := by
  haveI : NeZero P := ⟨hP_ne⟩
  haveI : NeZero Q := ⟨hQ_ne⟩
  have h_under_P_prime : (Ideal.absNorm (P.under ℤ)).Prime :=
    Nat.absNorm_under_prime P
  have h_under_Q_prime : (Ideal.absNorm (Q.under ℤ)).Prime :=
    Nat.absNorm_under_prime Q
  have h_under_P_dvd_ell : Ideal.absNorm (P.under ℤ) ∣ ℓ := by
    have hmem_int : ((ℓ : ℤ) : 𝓞 K) ∈ P := by
      exact_mod_cast hℓ_in_P
    exact_mod_cast
      ((Int.cast_mem_ideal_iff (R := 𝓞 K) (I := P) (d := (ℓ : ℤ))).mp hmem_int)
  have h_under_P_eq_ell : Ideal.absNorm (P.under ℤ) = ℓ :=
    (Nat.prime_dvd_prime_iff_eq h_under_P_prime (Fact.out : ℓ.Prime)).mp
      h_under_P_dvd_ell
  have hℓ_dvd_P : ℓ ∣ Ideal.absNorm P := by
    simpa [h_under_P_eq_ell] using (Int.absNorm_under_dvd_absNorm P)
  intro hℓ_in_Q
  have h_under_Q_dvd_ell : Ideal.absNorm (Q.under ℤ) ∣ ℓ := by
    have hmem_int : ((ℓ : ℤ) : 𝓞 K) ∈ Q := by
      exact_mod_cast hℓ_in_Q
    exact_mod_cast
      ((Int.cast_mem_ideal_iff (R := 𝓞 K) (I := Q) (d := (ℓ : ℤ))).mp hmem_int)
  have h_under_Q_eq_ell : Ideal.absNorm (Q.under ℤ) = ℓ :=
    (Nat.prime_dvd_prime_iff_eq h_under_Q_prime (Fact.out : ℓ.Prime)).mp
      h_under_Q_dvd_ell
  have hℓ_dvd_Q : ℓ ∣ Ideal.absNorm Q := by
    simpa [h_under_Q_eq_ell] using (Int.absNorm_under_dvd_absNorm Q)
  have hcop_self : ℓ.Coprime ℓ :=
    Nat.Coprime.of_dvd hℓ_dvd_P hℓ_dvd_Q hcop
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_self] at hcop_self
  exact (Fact.out : ℓ.Prime).ne_one hcop_self

/-- Per-source-prime conductor-flexible data used to build the actual
Ireland--Rosen reciprocal Φ element and its three prime-level facts.

The fields are the concrete hypotheses of `IrelandRosen.PrimeSource`, plus the
automorphism data needed for the conjugation/norm identity. -/
structure PrimeSourceData
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K] [IsCMField K]
    (P : Ideal (𝓞 K)) [P.IsMaximal] where
  ℓ : ℕ
  hℓ_prime : Fact (Nat.Prime ℓ)
  algZMod : Algebra (ZMod ℓ) (𝓞 K ⧸ P)
  R' : Type v
  field_R' : Field R'
  numberField_R' : NumberField R'
  algebra_K_R' : Algebra K R'
  scalarTower_Q_K_R' : IsScalarTower ℚ K R'
  cyclotomic_R' :
    letI : Field R' := field_R'
    letI : Algebra K R' := algebra_K_R'
    letI : IsScalarTower ℚ K R' := scalarTower_Q_K_R'
    IsCyclotomicExtension {ℓ * (Fintype.card (𝓞 K ⧸ P) - 1)} ℚ R'
  scalarTower_Z_OK_OR' :
    letI : Field R' := field_R'
    letI : NumberField R' := numberField_R'
    letI : Algebra K R' := algebra_K_R'
    letI : IsScalarTower ℚ K R' := scalarTower_Q_K_R'
    IsScalarTower ℤ (𝓞 K) (𝓞 R')
  isGalois_K_R' :
    letI : Field R' := field_R'
    letI : Algebra K R' := algebra_K_R'
    IsGalois K R'
  finiteDimensional_K_R' :
    letI : Field R' := field_R'
    letI : Algebra K R' := algebra_K_R'
    FiniteDimensional K R'
  faithfulSMul_OK_OR' :
    letI : Field R' := field_R'
    letI : NumberField R' := numberField_R'
    letI : Algebra K R' := algebra_K_R'
    letI : IsScalarTower ℚ K R' := scalarTower_Q_K_R'
    FaithfulSMul (𝓞 K) (𝓞 R')
  torsionFree_OK_OR' :
    letI : Field R' := field_R'
    letI : NumberField R' := numberField_R'
    letI : Algebra K R' := algebra_K_R'
    letI : IsScalarTower ℚ K R' := scalarTower_Q_K_R'
    Module.IsTorsionFree (𝓞 K) (𝓞 R')
  hP_bot : P ≠ ⊥
  hℓ_in_P : (ℓ : 𝓞 K) ∈ P
  hp_notin_P : (p : 𝓞 K) ∉ P
  S :
    letI : Fact (Nat.Prime ℓ) := hℓ_prime
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) := algZMod
    letI : Field R' := field_R'
    letI : NumberField R' := numberField_R'
    letI : Algebra K R' := algebra_K_R'
    letI : IsScalarTower ℚ K R' := scalarTower_Q_K_R'
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'
  h_psi :
    letI : Fact (Nat.Prime ℓ) := hℓ_prime
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) := algZMod
    letI : Field R' := field_R'
    letI : NumberField R' := numberField_R'
    letI : Algebra K R' := algebra_K_R'
    letI : IsScalarTower ℚ K R' := scalarTower_Q_K_R'
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    S.concrete.IsGalPsiShiftCompatible
  h_descentPrime :
    letI : Fact (Nat.Prime ℓ) := hℓ_prime
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) := algZMod
    letI : Field R' := field_R'
    letI : NumberField R' := numberField_R'
    letI : Algebra K R' := algebra_K_R'
    letI : IsScalarTower ℚ K R' := scalarTower_Q_K_R'
    letI : IsScalarTower ℤ (𝓞 K) (𝓞 R') := scalarTower_Z_OK_OR'
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    S.concrete.descentPrime = P
  h_source_coprime : ℓ.Coprime (Fintype.card (𝓞 K ⧸ P) - 1)
  h_zeta_k_eq :
    letI : Fact (Nat.Prime ℓ) := hℓ_prime
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) := algZMod
    letI : Field R' := field_R'
    letI : NumberField R' := numberField_R'
    letI : Algebra K R' := algebra_K_R'
    letI : IsScalarTower ℚ K R' := scalarTower_Q_K_R'
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    S.zeta_k = canonicalResidueZetaP (p := p) (K := K) P
  h_zeta_p_int_eq :
    letI : Fact (Nat.Prime ℓ) := hℓ_prime
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) := algZMod
    letI : Field R' := field_R'
    letI : NumberField R' := numberField_R'
    letI : Algebra K R' := algebra_K_R'
    letI : IsScalarTower ℚ K R' := scalarTower_Q_K_R'
    letI : IsScalarTower ℤ (𝓞 K) (𝓞 R') := scalarTower_Z_OK_OR'
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    S.zeta_p_int =
      (algebraMap (𝓞 K) (𝓞 R'))
        (cyclotomicZetaInteger (p := p) K)
  h_ne_zero :
    letI : Fact (Nat.Prime ℓ) := hℓ_prime
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) := algZMod
    letI : Field R' := field_R'
    letI : NumberField R' := numberField_R'
    letI : Algebra K R' := algebra_K_R'
    letI : IsScalarTower ℚ K R' := scalarTower_Q_K_R'
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    S.gaussSumInt (p - 1) ^ p ≠ 0
  hℓp : ℓ.Coprime p
  hf :
    letI : Fact (Nat.Prime ℓ) := hℓ_prime
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) := algZMod
    letI : Field R' := field_R'
    letI : NumberField R' := numberField_R'
    letI : Algebra K R' := algebra_K_R'
    letI : IsScalarTower ℚ K R' := scalarTower_Q_K_R'
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    S.f = orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p)
  he :
    letI : Fact (Nat.Prime ℓ) := hℓ_prime
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) := algZMod
    letI : Field R' := field_R'
    letI : NumberField R' := numberField_R'
    letI : Algebra K R' := algebra_K_R'
    letI : IsScalarTower ℚ K R' := scalarTower_Q_K_R'
    letI : IsScalarTower ℤ (𝓞 K) (𝓞 R') := scalarTower_Z_OK_OR'
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    S.concrete.descentRamificationIdx = ℓ - 1
  conjLift : 𝓞 R' →+* 𝓞 R'
  conjLift_lifts :
    letI : Field R' := field_R'
    letI : NumberField R' := numberField_R'
    letI : Algebra K R' := algebra_K_R'
    letI : IsScalarTower ℚ K R' := scalarTower_Q_K_R'
    ∀ x : 𝓞 K,
      conjLift (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x)
  conjLift_zeta_ell :
    letI : Fact (Nat.Prime ℓ) := hℓ_prime
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) := algZMod
    letI : Field R' := field_R'
    letI : NumberField R' := numberField_R'
    letI : Algebra K R' := algebra_K_R'
    letI : IsScalarTower ℚ K R' := scalarTower_Q_K_R'
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    conjLift S.concrete.zeta_ell_int =
      S.concrete.zeta_ell_int ^ (ℓ - 1)

namespace PrimeSourceData

variable {p : ℕ} [Fact (Nat.Prime p)] [NeZero p]
variable {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsGalois ℚ K] [IsCMField K]
variable {P : Ideal (𝓞 K)} [P.IsMaximal]

/-- The actual reciprocal-index prime Φ element produced by the direct
Ireland--Rosen source theorem. -/
noncomputable def phi (D : PrimeSourceData (p := p) (K := K) P) :
    PhiPrimeElement (p := p) (K := K) P := by
  letI : Fact (Nat.Prime D.ℓ) := D.hℓ_prime
  letI : Algebra (ZMod D.ℓ) (𝓞 K ⧸ P) := D.algZMod
  letI : Field D.R' := D.field_R'
  letI : NumberField D.R' := D.numberField_R'
  letI : Algebra K D.R' := D.algebra_K_R'
  letI : IsScalarTower ℚ K D.R' := D.scalarTower_Q_K_R'
  letI : IsCyclotomicExtension {D.ℓ * (Fintype.card (𝓞 K ⧸ P) - 1)} ℚ D.R' :=
    D.cyclotomic_R'
  letI : IsScalarTower ℤ (𝓞 K) (𝓞 D.R') := D.scalarTower_Z_OK_OR'
  letI : IsGalois K D.R' := D.isGalois_K_R'
  letI : FiniteDimensional K D.R' := D.finiteDimensional_K_R'
  letI : FaithfulSMul (𝓞 K) (𝓞 D.R') := D.faithfulSMul_OK_OR'
  letI : Module.IsTorsionFree (𝓞 K) (𝓞 D.R') := D.torsionFree_OK_OR'
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  exact reciprocalPrimePhiElement_of_f_eq_orderOf
    (ℓ := D.ℓ) (p := p) (K := K) (P := P) (R' := D.R')
    D.S D.h_psi D.h_descentPrime D.h_source_coprime D.h_ne_zero D.hℓp D.hf D.he

theorem phi_isSemiPrimary
    (hp_three : 3 ≤ p) (D : PrimeSourceData (p := p) (K := K) P) :
    FLT37.IsSemiPrimary p (K := K) D.phi.gamma := by
  letI : Fact (Nat.Prime D.ℓ) := D.hℓ_prime
  letI : Algebra (ZMod D.ℓ) (𝓞 K ⧸ P) := D.algZMod
  letI : Field D.R' := D.field_R'
  letI : NumberField D.R' := D.numberField_R'
  letI : Algebra K D.R' := D.algebra_K_R'
  letI : IsScalarTower ℚ K D.R' := D.scalarTower_Q_K_R'
  letI : IsCyclotomicExtension {D.ℓ * (Fintype.card (𝓞 K ⧸ P) - 1)} ℚ D.R' :=
    D.cyclotomic_R'
  letI : IsScalarTower ℤ (𝓞 K) (𝓞 D.R') := D.scalarTower_Z_OK_OR'
  letI : IsGalois K D.R' := D.isGalois_K_R'
  letI : FiniteDimensional K D.R' := D.finiteDimensional_K_R'
  letI : FaithfulSMul (𝓞 K) (𝓞 D.R') := D.faithfulSMul_OK_OR'
  letI : Module.IsTorsionFree (𝓞 K) (𝓞 D.R') := D.torsionFree_OK_OR'
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  simpa [phi] using
    reciprocalPrimePhiElement_isSemiPrimary
      (ℓ := D.ℓ) (p := p) (K := K) (P := P) (R' := D.R')
      hp_three D.S D.h_psi D.h_descentPrime D.h_source_coprime
      D.h_ne_zero D.hℓp D.hf D.he D.h_zeta_p_int_eq

theorem phi_conj_mul_self_eq_absNorm_pow
    (D : PrimeSourceData (p := p) (K := K) P) :
    ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
      (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  letI : Fact (Nat.Prime D.ℓ) := D.hℓ_prime
  letI : Algebra (ZMod D.ℓ) (𝓞 K ⧸ P) := D.algZMod
  letI : Field D.R' := D.field_R'
  letI : NumberField D.R' := D.numberField_R'
  letI : Algebra K D.R' := D.algebra_K_R'
  letI : IsScalarTower ℚ K D.R' := D.scalarTower_Q_K_R'
  letI : IsCyclotomicExtension {D.ℓ * (Fintype.card (𝓞 K ⧸ P) - 1)} ℚ D.R' :=
    D.cyclotomic_R'
  letI : IsScalarTower ℤ (𝓞 K) (𝓞 D.R') := D.scalarTower_Z_OK_OR'
  letI : IsGalois K D.R' := D.isGalois_K_R'
  letI : FiniteDimensional K D.R' := D.finiteDimensional_K_R'
  letI : FaithfulSMul (𝓞 K) (𝓞 D.R') := D.faithfulSMul_OK_OR'
  letI : Module.IsTorsionFree (𝓞 K) (𝓞 D.R') := D.torsionFree_OK_OR'
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  simpa [phi] using
    reciprocalPrimePhiElement_conj_mul_self_eq_absNorm_pow
      (ℓ := D.ℓ) (p := p) (K := K) (P := P) (R' := D.R')
      D.S D.h_psi D.h_descentPrime D.h_source_coprime D.h_ne_zero
      D.hℓp D.hf D.he D.h_zeta_p_int_eq D.conjLift
      D.conjLift_lifts D.conjLift_zeta_ell

theorem phi_symbol_eq_norm_symbol
    (D : PrimeSourceData (p := p) (K := K) P)
    {Q : Ideal (𝓞 K)} [Q.IsMaximal]
    (hQ_bot : Q ≠ ⊥)
    (hp_notin_Q : (p : 𝓞 K) ∉ Q)
    (hcop : (Ideal.absNorm P).Coprime (Ideal.absNorm Q)) :
    pthSymbolAtPrime_canonical (p := p) (K := K) D.phi.gamma Q =
      pthSymbolAtPrime_canonical (p := p) (K := K)
        (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P := by
  letI : Fact (Nat.Prime D.ℓ) := D.hℓ_prime
  letI : Algebra (ZMod D.ℓ) (𝓞 K ⧸ P) := D.algZMod
  letI : Field D.R' := D.field_R'
  letI : NumberField D.R' := D.numberField_R'
  letI : Algebra K D.R' := D.algebra_K_R'
  letI : IsScalarTower ℚ K D.R' := D.scalarTower_Q_K_R'
  letI : IsCyclotomicExtension {D.ℓ * (Fintype.card (𝓞 K ⧸ P) - 1)} ℚ D.R' :=
    D.cyclotomic_R'
  letI : IsScalarTower ℤ (𝓞 K) (𝓞 D.R') := D.scalarTower_Z_OK_OR'
  letI : IsGalois K D.R' := D.isGalois_K_R'
  letI : FiniteDimensional K D.R' := D.finiteDimensional_K_R'
  letI : FaithfulSMul (𝓞 K) (𝓞 D.R') := D.faithfulSMul_OK_OR'
  letI : Module.IsTorsionFree (𝓞 K) (𝓞 D.R') := D.torsionFree_OK_OR'
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  haveI : P.IsPrime := inferInstance
  haveI : Q.IsPrime := inferInstance
  have hℓ_notin_Q : (D.ℓ : 𝓞 K) ∉ Q :=
    natCast_notMem_of_absNorm_coprime_of_natCast_mem
      (ℓ := D.ℓ) (K := K) D.hP_bot hQ_bot D.hℓ_in_P hcop
  let T : PhiPrimeElement.K2_2FlexibleTargetData
      (ℓ := D.ℓ) (p := p) (K := K) (R' := D.R') Q :=
    flexibleTargetDataOfPrimeRingCharNotMem
      (ℓ := D.ℓ) (p := p) (K := K) (R' := D.R')
      hQ_bot hp_notin_Q hℓ_notin_Q
  letI : T.overPrime.IsMaximal := T.overPrime_max
  letI : Fact (Nat.Prime T.ell') := T.ell'_prime
  letI : CharP (𝓞 D.R' ⧸ T.overPrime) T.ell' := T.char_over
  simpa [phi] using
    reciprocalPrimePhiElement_symbol_eq_norm_symbol
      (ℓ := D.ℓ) (p := p) (K := K) (P := P) D.hP_bot
      D.hℓ_in_P D.hp_notin_P (R' := D.R') D.S D.h_psi D.h_descentPrime
      D.h_source_coprime D.h_zeta_k_eq D.h_zeta_p_int_eq D.h_ne_zero
      D.hℓp D.hf D.he hQ_bot hp_notin_Q hcop T.h_over T.hℓ_ne_ℓ'

end PrimeSourceData

/-- The variable-prime `primePhi` family built from per-prime
Ireland--Rosen source data. -/
noncomputable def primePhiFamilyOfSourceData
    {p : ℕ} [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K] [IsCMField K]
    {α : 𝓞 K}
    (source :
      ∀ P : Ideal (𝓞 K), [P.IsMaximal] →
        P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
          PrimeSourceData (p := p) (K := K) P) :
    ∀ P : Ideal (𝓞 K),
      P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
        PhiPrimeElement (p := p) (K := K) P :=
  fun P hP => by
    letI : P.IsMaximal := (isPrime_of_mem_normalizedFactors hP).2.2
    exact (source P hP).phi

/-- The three concrete fact families consumed by the exact Theorem 1 proof,
assembled globally from the arbitrary-degree Ireland--Rosen source data. -/
theorem primePhiFamilyFactsOfSourceData
    {p : ℕ} [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K] [IsCMField K]
    {α : 𝓞 K}
    (hp_three : 3 ≤ p)
    (source :
      ∀ P : Ideal (𝓞 K), [P.IsMaximal] →
        P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
          PrimeSourceData (p := p) (K := K) P) :
    let primePhi := primePhiFamilyOfSourceData (p := p) (K := K) (α := α) source
    (∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        FLT37.IsSemiPrimary p (K := K) (primePhi P hP).gamma) ∧
      (∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))),
        ringOfIntegersComplexConj K (primePhi P hP).gamma *
            (primePhi P hP).gamma =
          (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p) ∧
      (∀ B : Ideal (𝓞 K), IsCoprimeToPAndAlpha (p := p) (K := K) B α →
        ∀ P (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))))
          Q (_hQ : Q ∈ normalizedFactors B),
          pthSymbolAtPrime_canonical (p := p) (K := K)
              (primePhi P hP).gamma Q =
            pthSymbolAtPrime_canonical (p := p) (K := K)
              (((Ideal.absNorm Q : ℤ) : 𝓞 K)) P) := by
  classical
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    letI : P.IsMaximal := (isPrime_of_mem_normalizedFactors hP).2.2
    simpa [primePhiFamilyOfSourceData] using
      (source P hP).phi_isSemiPrimary hp_three
  · intro P hP
    letI : P.IsMaximal := (isPrime_of_mem_normalizedFactors hP).2.2
    simpa [primePhiFamilyOfSourceData] using
      (source P hP).phi_conj_mul_self_eq_absNorm_pow
  · intro B hB P hP Q hQ
    letI : P.IsMaximal := (isPrime_of_mem_normalizedFactors hP).2.2
    obtain ⟨_, hQ_bot, hQ_max⟩ := isPrime_of_mem_normalizedFactors hQ
    letI : Q.IsMaximal := hQ_max
    have hp_notin_Q : (p : 𝓞 K) ∉ Q :=
      natCast_notMem_of_isCoprime_span_natCast_of_mem_normalizedFactors
        (p := p) (K := K) hB.2.2.1 hQ
    have h_absNorm_coprime :
        (Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K)))).Coprime
          (Ideal.absNorm B) :=
      absNorm_coprime_of_idealNormPrincipal_coprime
        (K := K) hB.2.2.2
    have hA_le_P : Ideal.span ({α} : Set (𝓞 K)) ≤ P := by
      rw [← Ideal.dvd_iff_le]
      exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
    have hB_le_Q : B ≤ Q := by
      rw [← Ideal.dvd_iff_le]
      exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQ
    have hP_dvd_A :
        Ideal.absNorm P ∣ Ideal.absNorm (Ideal.span ({α} : Set (𝓞 K))) :=
      Ideal.absNorm_dvd_absNorm_of_le hA_le_P
    have hQ_dvd_B : Ideal.absNorm Q ∣ Ideal.absNorm B :=
      Ideal.absNorm_dvd_absNorm_of_le hB_le_Q
    have hcopPQ : (Ideal.absNorm P).Coprime (Ideal.absNorm Q) :=
      Nat.Coprime.of_dvd hP_dvd_A hQ_dvd_B h_absNorm_coprime
    simpa [primePhiFamilyOfSourceData] using
      (source P hP).phi_symbol_eq_norm_symbol hQ_bot hp_notin_Q hcopPQ

end IrelandRosen

end Furtwaengler

end BernoulliRegular

end

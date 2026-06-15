module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor.Part2.Part1

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField NumberField.IsCMField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

namespace PhiPrimeElement

/-- The index-one actual prime Φ element carried by conductor-flexible K2-2
source data is semi-primary. -/
theorem K2_2FlexibleSourceData_phi_gamma_isSemiPrimary
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2FlexibleSourceData S)
    (hp_three : 3 ≤ p) :
    FLT37.IsSemiPrimary p (K := K) D.phi.gamma := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  rw [K2_2FlexibleSourceData_phi_gamma]
  exact S.phiPrimeGenDescent_isSemiPrimary D.h_psi
    (le_refl 1) (one_le_p_sub_one_of_prime (p := p))
    D.h_ne_zero hp_three D.h_zeta_p_int_eq

/-- Conductor-flexible index-one source-data conjugation norm from an
upstairs ring endomorphism realizing complex conjugation on the concrete
character data. -/
theorem
    K2_2FlexibleSourceData_phi_conj_mul_self_eq_absNorm_pow_of_ringHomComp
    [IsCMField K]
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2FlexibleSourceData S)
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (hσχ :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      (S.concrete.residueCharInt ^ 1).ringHomComp σ =
        (S.concrete.residueCharInt ^ 1)⁻¹)
    (hσψ :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      σ.toMonoidHom.compAddChar S.concrete.psiInt =
        S.concrete.psiInt⁻¹) :
    ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
      (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have hraw :
      ringOfIntegersComplexConj K
          (S.phiPrimeGenDescent D.h_psi
            (le_refl 1) (one_le_p_sub_one_of_prime (p := p))
            D.h_ne_zero) *
          S.phiPrimeGenDescent D.h_psi
            (le_refl 1) (one_le_p_sub_one_of_prime (p := p))
            D.h_ne_zero =
        (ℓ : 𝓞 K) ^ (S.concrete.f * p) :=
    S.phiPrimeGenDescent_conj_mul_self_eq_ell_pow_of_ringHomComp
      (p := p) (K := K) D.h_psi
      (le_refl 1) (one_le_p_sub_one_of_prime (p := p))
      D.h_ne_zero σ hσ_lifts_conj hσχ hσψ
  have h_abs :
      Ideal.absNorm P = ℓ ^ S.concrete.f := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    exact S.concrete.card_k
  rw [K2_2FlexibleSourceData_phi_gamma]
  calc
    ringOfIntegersComplexConj K
          (S.phiPrimeGenDescent D.h_psi
            (le_refl 1) (one_le_p_sub_one_of_prime (p := p))
            D.h_ne_zero) *
        S.phiPrimeGenDescent D.h_psi
          (le_refl 1) (one_le_p_sub_one_of_prime (p := p))
          D.h_ne_zero
        = (ℓ : 𝓞 K) ^ (S.concrete.f * p) := hraw
    _ = (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
          rw [h_abs, pow_mul]
          congr 1
          norm_num

/-- Conductor-flexible index-one source-data conjugation norm from
source-conductor root-action compatibility of an upstairs endomorphism. -/
theorem
    K2_2FlexibleSourceData_phi_conj_mul_self_eq_absNorm_pow_of_rootAction
    [IsCMField K]
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2FlexibleSourceData S)
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (hσζp :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      σ S.concrete.zeta_p_int =
        S.concrete.zeta_p_int ^ (p - 1))
    (hσζell :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      σ S.concrete.zeta_ell_int =
        S.concrete.zeta_ell_int ^ (ℓ - 1)) :
    ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
      (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have hσχ :
      (S.concrete.residueCharInt ^ 1).ringHomComp σ =
        (S.concrete.residueCharInt ^ 1)⁻¹ :=
    S.concrete
      |>.residueCharInt_pow_ringHomComp_eq_inv_of_zeta_p_int_map_pow_sub_one
        1 σ hσζp
  have hσψ :
      σ.toMonoidHom.compAddChar S.concrete.psiInt =
        S.concrete.psiInt⁻¹ :=
    (S.toConductorFlexibleFullTeichStickelbergerSetup
      |>.toConductorFlexibleTraceFormStickelbergerSetup
      |>.psiInt_compAddChar_eq_inv_of_zeta_ell_int_map_pow_sub_one
        σ hσζell)
  exact
    K2_2FlexibleSourceData_phi_conj_mul_self_eq_absNorm_pow_of_ringHomComp
      (p := p) (K := K) D σ hσ_lifts_conj hσχ hσψ

/-- Conductor-flexible index-one source-data conjugation norm with the
`p`-root action discharged from the canonical source-data root choice. -/
theorem
    K2_2FlexibleSourceData_phi_conj_mul_self_eq_absNorm_pow_of_zetaEllRootAction
    [IsCMField K]
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2FlexibleSourceData S)
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (hσζell :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      σ S.concrete.zeta_ell_int =
        S.concrete.zeta_ell_int ^ (ℓ - 1)) :
    ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
      (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have h_zeta_p_int_eq :
      S.concrete.zeta_p_int =
        algebraMap (𝓞 K) (𝓞 R') (cyclotomicZetaInteger (p := p) K) := by
    simpa [ConductorFlexibleFullTeichStickelbergerSetup.concrete,
      ConductorFlexibleTraceFormStickelbergerSetup.concrete] using
      D.h_zeta_p_int_eq
  have hσζp :
      σ S.concrete.zeta_p_int =
        S.concrete.zeta_p_int ^ (p - 1) :=
    S.zeta_p_int_map_pow_sub_one_of_lifts_conj
      (p := p) (K := K) σ hσ_lifts_conj h_zeta_p_int_eq
  exact
    K2_2FlexibleSourceData_phi_conj_mul_self_eq_absNorm_pow_of_rootAction
      (p := p) (K := K) D σ hσ_lifts_conj hσζp hσζell

/-- Conductor-flexible index-one source-data conjugation norm using the
actual upstairs complex conjugation map. -/
theorem
    K2_2FlexibleSourceData_phi_conj_mul_self_eq_absNorm_pow_of_upstairsComplexConj
    [IsCMField K]
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    [IsCMField R']
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2FlexibleSourceData S)
    (h_upstairs_lifts_conj : ∀ x : 𝓞 K,
      ringOfIntegersComplexConj R' (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x)) :
    ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
      (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  let σ : 𝓞 R' →+* 𝓞 R' :=
    (ringOfIntegersComplexConj R').toRingEquiv.toRingHom
  have hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x) := fun x =>
    h_upstairs_lifts_conj x
  have hσζell :
      σ S.concrete.zeta_ell_int =
        S.concrete.zeta_ell_int ^ (ℓ - 1) := by
    simpa [σ] using S.concrete.zeta_ell_int_complexConj_eq_pow_sub_one
  exact
    K2_2FlexibleSourceData_phi_conj_mul_self_eq_absNorm_pow_of_zetaEllRootAction
      (p := p) (K := K) D σ hσ_lifts_conj hσζell

/-- Bundled conductor-flexible index-one Φ facts from source-conductor
root-action compatibility. -/
theorem K2_2FlexibleSourceData_phi_facts_of_zetaEllRootAction
    [IsCMField K]
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [NeZero p]
    (hp_three : 3 ≤ p)
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2FlexibleSourceData S)
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (hσζell :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      σ S.concrete.zeta_ell_int =
        S.concrete.zeta_ell_int ^ (ℓ - 1)) :
    FLT37.IsSemiPrimary p (K := K) D.phi.gamma ∧
      ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
        (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  refine ⟨?_, ?_⟩
  · exact K2_2FlexibleSourceData_phi_gamma_isSemiPrimary
      (p := p) (K := K) D hp_three
  · exact
      K2_2FlexibleSourceData_phi_conj_mul_self_eq_absNorm_pow_of_zetaEllRootAction
        (p := p) (K := K) D σ hσ_lifts_conj hσζell

/-! ### Conductor-flexible reciprocal source-data facts -/

/-- The reciprocal-index actual prime Φ element carried by
conductor-flexible K2-2 source data is semi-primary. -/
theorem K2_2FlexibleReciprocalSourceData_phi_gamma_isSemiPrimary
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2FlexibleReciprocalSourceData S)
    (hp_three : 3 ≤ p) :
    FLT37.IsSemiPrimary p (K := K) D.phi.gamma := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  rw [K2_2FlexibleReciprocalSourceData_phi_gamma]
  exact S.phiPrimeGenDescent_isSemiPrimary D.h_psi
    (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1))
    D.h_ne_zero hp_three D.h_zeta_p_int_eq

/-- Conductor-flexible reciprocal source-data conjugation norm from an
upstairs ring endomorphism realizing complex conjugation on the concrete
character data. -/
theorem
    K2_2FlexibleReciprocalSourceData_phi_conj_mul_self_eq_absNorm_pow_of_ringHomComp
    [IsCMField K]
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2FlexibleReciprocalSourceData S)
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (hσχ :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      (S.concrete.residueCharInt ^ (p - 1)).ringHomComp σ =
        (S.concrete.residueCharInt ^ (p - 1))⁻¹)
    (hσψ :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      σ.toMonoidHom.compAddChar S.concrete.psiInt =
        S.concrete.psiInt⁻¹) :
    ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
      (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have hraw :
      ringOfIntegersComplexConj K
          (S.phiPrimeGenDescent D.h_psi
            (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1))
            D.h_ne_zero) *
          S.phiPrimeGenDescent D.h_psi
            (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1))
            D.h_ne_zero =
        (ℓ : 𝓞 K) ^ (S.concrete.f * p) :=
    S.phiPrimeGenDescent_conj_mul_self_eq_ell_pow_of_ringHomComp
      (p := p) (K := K) D.h_psi
      (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1))
      D.h_ne_zero σ hσ_lifts_conj hσχ hσψ
  have h_abs :
      Ideal.absNorm P = ℓ ^ S.concrete.f := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    exact S.concrete.card_k
  rw [K2_2FlexibleReciprocalSourceData_phi_gamma]
  calc
    ringOfIntegersComplexConj K
          (S.phiPrimeGenDescent D.h_psi
            (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1))
            D.h_ne_zero) *
        S.phiPrimeGenDescent D.h_psi
          (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1))
          D.h_ne_zero
        = (ℓ : 𝓞 K) ^ (S.concrete.f * p) := hraw
    _ = (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
          rw [h_abs, pow_mul]
          congr 1
          norm_num

/-- Conductor-flexible reciprocal source-data conjugation norm from
source-conductor root-action compatibility of an upstairs endomorphism. -/
theorem
    K2_2FlexibleReciprocalSourceData_phi_conj_mul_self_eq_absNorm_pow_of_rootAction
    [IsCMField K]
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2FlexibleReciprocalSourceData S)
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (hσζp :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      σ S.concrete.zeta_p_int =
        S.concrete.zeta_p_int ^ (p - 1))
    (hσζell :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      σ S.concrete.zeta_ell_int =
        S.concrete.zeta_ell_int ^ (ℓ - 1)) :
    ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
      (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have hσχ :
      (S.concrete.residueCharInt ^ (p - 1)).ringHomComp σ =
        (S.concrete.residueCharInt ^ (p - 1))⁻¹ :=
    S.concrete
      |>.residueCharInt_pow_ringHomComp_eq_inv_of_zeta_p_int_map_pow_sub_one
        (p - 1) σ hσζp
  have hσψ :
      σ.toMonoidHom.compAddChar S.concrete.psiInt =
        S.concrete.psiInt⁻¹ :=
    (S.toConductorFlexibleFullTeichStickelbergerSetup
      |>.toConductorFlexibleTraceFormStickelbergerSetup
      |>.psiInt_compAddChar_eq_inv_of_zeta_ell_int_map_pow_sub_one
        σ hσζell)
  exact
    K2_2FlexibleReciprocalSourceData_phi_conj_mul_self_eq_absNorm_pow_of_ringHomComp
      (p := p) (K := K) D σ hσ_lifts_conj hσχ hσψ

/-- Conductor-flexible reciprocal source-data conjugation norm with the
`p`-root action discharged from the canonical source-data root choice. -/
theorem
    K2_2FlexibleReciprocalSourceData_phi_conj_mul_self_eq_absNorm_pow_of_zetaEllRootAction
    [IsCMField K]
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2FlexibleReciprocalSourceData S)
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (hσζell :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      σ S.concrete.zeta_ell_int =
        S.concrete.zeta_ell_int ^ (ℓ - 1)) :
    ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
      (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have h_zeta_p_int_eq :
      S.concrete.zeta_p_int =
        algebraMap (𝓞 K) (𝓞 R') (cyclotomicZetaInteger (p := p) K) := by
    simpa [ConductorFlexibleFullTeichStickelbergerSetup.concrete,
      ConductorFlexibleTraceFormStickelbergerSetup.concrete] using
      D.h_zeta_p_int_eq
  have hσζp :
      σ S.concrete.zeta_p_int =
        S.concrete.zeta_p_int ^ (p - 1) :=
    S.zeta_p_int_map_pow_sub_one_of_lifts_conj
      (p := p) (K := K) σ hσ_lifts_conj h_zeta_p_int_eq
  exact
    K2_2FlexibleReciprocalSourceData_phi_conj_mul_self_eq_absNorm_pow_of_rootAction
      (p := p) (K := K) D σ hσ_lifts_conj hσζp hσζell

/-- Conductor-flexible reciprocal source-data conjugation norm using the
actual upstairs complex conjugation map. -/
theorem
    K2_2FlexibleReciprocalSourceData_phi_conj_mul_self_eq_absNorm_pow_of_upstairsComplexConj
    [IsCMField K]
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    [IsCMField R']
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2FlexibleReciprocalSourceData S)
    (h_upstairs_lifts_conj : ∀ x : 𝓞 K,
      ringOfIntegersComplexConj R' (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x)) :
    ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
      (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  let σ : 𝓞 R' →+* 𝓞 R' :=
    (ringOfIntegersComplexConj R').toRingEquiv.toRingHom
  have hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x) := fun x =>
    h_upstairs_lifts_conj x
  have hσζell :
      σ S.concrete.zeta_ell_int =
        S.concrete.zeta_ell_int ^ (ℓ - 1) := by
    simpa [σ] using S.concrete.zeta_ell_int_complexConj_eq_pow_sub_one
  exact
    K2_2FlexibleReciprocalSourceData_phi_conj_mul_self_eq_absNorm_pow_of_zetaEllRootAction
      (p := p) (K := K) D σ hσ_lifts_conj hσζell

/-- Bundled conductor-flexible reciprocal Φ facts from source-conductor
root-action compatibility.  This is the reflection-handoff form of the
semi-primary plus conjugation-norm package. -/
theorem K2_2FlexibleReciprocalSourceData_phi_facts_of_zetaEllRootAction
    [IsCMField K]
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [NeZero p]
    (hp_three : 3 ≤ p)
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : K2_2FlexibleReciprocalSourceData S)
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (hσζell :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      σ S.concrete.zeta_ell_int =
        S.concrete.zeta_ell_int ^ (ℓ - 1)) :
    FLT37.IsSemiPrimary p (K := K) D.phi.gamma ∧
      ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
        (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  refine ⟨?_, ?_⟩
  · exact K2_2FlexibleReciprocalSourceData_phi_gamma_isSemiPrimary
      (p := p) (K := K) D hp_three
  · exact
      K2_2FlexibleReciprocalSourceData_phi_conj_mul_self_eq_absNorm_pow_of_zetaEllRootAction
        (p := p) (K := K) D σ hσ_lifts_conj hσζell

end PhiPrimeElement

end Furtwaengler

end BernoulliRegular

end

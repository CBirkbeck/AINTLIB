module

public import Mathlib.LinearAlgebra.SModEq.Pow
public import BernoulliRegular.FLT37.PrimaryUnits
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrincipalBridge
public import BernoulliRegular.TotallyRealSubfield.Conjugation
public import BernoulliRegular.UnitQuotient.FreeLatticeComparison.ConjugationTrace
public import BernoulliRegular.UnitQuotient.TorsionQuotient
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor.UnitFactorChainInterface

/-!
# Principal unit factor (REF-18 Phase 2, sub-piece U)

For a nonzero principal ideal `(α)`, the actual multiplicative Φ element
`Φ((α))` and the explicit Stickelberger principal generator
`α^Θ = stickelbergerPrincipalGen α` generate the same ideal. Hence they differ
by a unit:

```
Φ((α)) = u(α) · α^Θ.
```

This file formalizes the honest element-level U-chain interface:

* `PrincipalUnitFactorData α Φα` is the specific unit-factor equation for an
  actual principal Φ element `Φα`.
* `PrincipalUnitFactorData.nonempty_of_nonzero` proves existence of such a
  unit from the already formalized Φ-span theorem.
* If that specific unit is `±1`, its prime residue symbols vanish.
* `ChosenPrimaryUnitFactorProductSymbolZero α` is the reflection-facing
  chosen-object product condition: the same actual Φ element has locally
  trivial product symbols for `Φ((α)) · α` away from `α`.
* `ChosenPrimaryUnitFactorSymbolTrivial α` is the natural chosen-object
  downstream output from one normalized actual principal Φ element.
* `PrimaryUnitFactorSymbolTrivial α` is the stronger uniform downstream
  hypothesis over the current broad `PhiPrincipalElement` API.
* The concrete U4 endpoint is proved in
  `PrincipalUnitFactorData.exists_isSign_of_primary_primePhiFacts` and
  `ChosenPrimaryUnitFactorSymbolTrivial_of_primary_primePhiFacts`: for an
  actual principal Φ product, prime-level semi-primarity plus the prime
  conjugation-norm identities force the specific unit factor to be `±1`, hence
  its prime symbols vanish.

What remains outside this file is constructing the actual principal Φ product
from `K2_2SourceData` for every normalized prime factor and proving the
conjugation compatibility needed for those prime norm identities.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField NumberField.IsCMField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- A finite product of semi-primary elements is semi-primary. -/
theorem isSemiPrimary_finset_prod
    {ι : Type*} (s : Finset ι) (f : ι → 𝓞 K)
    (hf : ∀ i ∈ s, FLT37.IsSemiPrimary p (K := K) (f i)) :
    FLT37.IsSemiPrimary p (K := K) (s.prod f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using FLT37.IsSemiPrimary.one (p := p) (K := K)
  | insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (hf i (by simp)).mul
        (ih fun j hj => hf j (by simp [hj]))

/-- A multiset product of semi-primary elements is semi-primary. -/
theorem isSemiPrimary_multiset_prod
    (m : Multiset (𝓞 K))
    (hm : ∀ x ∈ m, FLT37.IsSemiPrimary p (K := K) x) :
    FLT37.IsSemiPrimary p (K := K) m.prod := by
  induction m using Multiset.induction_on with
  | empty =>
      simpa using FLT37.IsSemiPrimary.one (p := p) (K := K)
  | cons x m ih =>
      rw [Multiset.prod_cons]
      exact (hm x (by simp)).mul
        (ih fun y hy => hm y (by simp [hy]))

/-- The actual Φ-prime element constructed from a descended Gauss sum is
semi-primary. -/
theorem PhiPrimeElement.ofDescent_gamma_isSemiPrimary
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    (S : FullTeichDworkSetup ℓ p k K R') {a : ℕ}
    (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P : Ideal (𝓞 K)}
    (h_span : Ideal.span ({phiPrimeGenDescent S ha₁ ha₂ h_ne_zero} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P)
    (hp_three : 3 ≤ p)
    (h_zeta_p_int_eq :
      S.zeta_p_int =
        algebraMap (𝓞 K) (𝓞 R') (cyclotomicZetaInteger (p := p) K)) :
    FLT37.IsSemiPrimary p (K := K)
      (PhiPrimeElement.ofDescent (p := p) (K := K)
        S ha₁ ha₂ h_ne_zero h_span).gamma := by
  simpa [PhiPrimeElement.ofDescent_gamma] using
    S.phiPrimeGenDescent_isSemiPrimary
      ha₁ ha₂ h_ne_zero hp_three h_zeta_p_int_eq

/-- Index-one version of
`PhiPrimeElement.ofDescent_gamma_isSemiPrimary`. -/
theorem PhiPrimeElement.ofDescentIndexOne_gamma_isSemiPrimary
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    (S : FullTeichDworkSetup ℓ p k K R')
    (h_ne_zero : S.gaussSumInt 1 ^ p ≠ 0)
    {P : Ideal (𝓞 K)}
    (h_span : Ideal.span ({phiPrimeGenDescent S
        (le_refl 1) (one_le_p_sub_one_of_prime (p := p)) h_ne_zero} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P)
    (hp_three : 3 ≤ p)
    (h_zeta_p_int_eq :
      S.zeta_p_int =
        algebraMap (𝓞 K) (𝓞 R') (cyclotomicZetaInteger (p := p) K)) :
    FLT37.IsSemiPrimary p (K := K)
      (PhiPrimeElement.ofDescentIndexOne (p := p) (K := K)
        S h_ne_zero h_span).gamma := by
  simpa [PhiPrimeElement.ofDescentIndexOne_gamma] using
    S.phiPrimeGenDescent_isSemiPrimary
      (le_refl 1) (one_le_p_sub_one_of_prime (p := p))
      h_ne_zero hp_three h_zeta_p_int_eq

/-- Reciprocal-index version of
`PhiPrimeElement.ofDescent_gamma_isSemiPrimary`. -/
theorem PhiPrimeElement.ofDescentSubOne_gamma_isSemiPrimary
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    (S : FullTeichDworkSetup ℓ p k K R')
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0)
    {P : Ideal (𝓞 K)}
    (h_span : Ideal.span ({phiPrimeGenDescent S
        (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) h_ne_zero} :
          Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P)
    (hp_three : 3 ≤ p)
    (h_zeta_p_int_eq :
      S.zeta_p_int =
        algebraMap (𝓞 K) (𝓞 R') (cyclotomicZetaInteger (p := p) K)) :
    FLT37.IsSemiPrimary p (K := K)
      (PhiPrimeElement.ofDescentSubOne (p := p) (K := K)
        S h_ne_zero h_span).gamma := by
  simpa [PhiPrimeElement.ofDescentSubOne_gamma] using
    S.phiPrimeGenDescent_isSemiPrimary
      (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1))
      h_ne_zero hp_three h_zeta_p_int_eq

/-- The actual prime Φ element carried by K2-2 source data is semi-primary.

This is the U4-facing form of the descended Gauss-sum congruence: the same
data-carrying `D.phi` used in the corrected K2-2 symbol theorem is congruent
to `-1` modulo `(ζ_p - 1)^2`. -/
theorem PhiPrimeElement.K2_2SourceData_phi_gamma_isSemiPrimary
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : PhiPrimeElement.K2_2SourceData S)
    (hp_three : 3 ≤ p) :
    FLT37.IsSemiPrimary p (K := K) D.phi.gamma := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  simpa [PhiPrimeElement.K2_2SourceData.phi] using
    PhiPrimeElement.ofDescentIndexOne_gamma_isSemiPrimary
      (p := p) (K := K) S D.h_ne_zero D.h_span hp_three
      D.h_zeta_p_int_eq

/-- The reciprocal-index actual prime Φ element carried by K2-2 source data is
semi-primary. -/
theorem PhiPrimeElement.K2_2ReciprocalSourceData_phi_gamma_isSemiPrimary
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : PhiPrimeElement.K2_2ReciprocalSourceData S)
    (hp_three : 3 ≤ p) :
    FLT37.IsSemiPrimary p (K := K) D.phi.gamma := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  simpa [PhiPrimeElement.K2_2ReciprocalSourceData.phi] using
    PhiPrimeElement.ofDescentSubOne_gamma_isSemiPrimary
      (p := p) (K := K) S D.h_ne_zero D.h_span hp_three
      D.h_zeta_p_int_eq

theorem PhiPrimeElement.K2_2SourceData_phi_conj_mul_self_eq_absNorm_pow_of_ringHomComp
    [IsCMField K]
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : PhiPrimeElement.K2_2SourceData S)
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (hσχ :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      (S.toConcreteStickelbergerSetup.residueCharInt ^ 1).ringHomComp σ =
        (S.toConcreteStickelbergerSetup.residueCharInt ^ 1)⁻¹)
    (hσψ :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      σ.toMonoidHom.compAddChar S.toConcreteStickelbergerSetup.psiInt =
        S.toConcreteStickelbergerSetup.psiInt⁻¹) :
    ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
      (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have hraw :
      ringOfIntegersComplexConj K
          (phiPrimeGenDescent S (le_refl 1)
            (one_le_p_sub_one_of_prime (p := p)) D.h_ne_zero) *
          phiPrimeGenDescent S (le_refl 1)
            (one_le_p_sub_one_of_prime (p := p)) D.h_ne_zero =
        (ℓ : 𝓞 K) ^ (S.toConcreteStickelbergerSetup.f * p) :=
    S.phiPrimeGenDescent_conj_mul_self_eq_ell_pow_of_ringHomComp
      (p := p) (K := K) (le_refl 1) (one_le_p_sub_one_of_prime (p := p))
      D.h_ne_zero σ hσ_lifts_conj hσχ hσψ
  have h_abs :
      Ideal.absNorm P = ℓ ^ S.toConcreteStickelbergerSetup.f := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    exact S.toConcreteStickelbergerSetup.card_k
  rw [PhiPrimeElement.K2_2SourceData_phi_gamma]
  calc
    ringOfIntegersComplexConj K
          (phiPrimeGenDescent S (le_refl 1)
            (one_le_p_sub_one_of_prime (p := p)) D.h_ne_zero) *
        phiPrimeGenDescent S (le_refl 1)
          (one_le_p_sub_one_of_prime (p := p)) D.h_ne_zero
        = (ℓ : 𝓞 K) ^ (S.toConcreteStickelbergerSetup.f * p) := hraw
    _ = (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
          rw [h_abs, pow_mul]
          congr 1
          norm_num

/-- K2-2 source-data conjugation norm from root-action compatibility of the
upstairs endomorphism. This is the caller-facing arithmetic form of the
prime-Φ norm identity: the character-composition hypotheses are discharged
from `ζ_p ↦ ζ_p^(p-1)` and `ζ_ℓ ↦ ζ_ℓ^(ℓ-1)`. -/
theorem PhiPrimeElement.K2_2SourceData_phi_conj_mul_self_eq_absNorm_pow_of_rootAction
    [IsCMField K]
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : PhiPrimeElement.K2_2SourceData S)
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (hσζp :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      σ S.toConcreteStickelbergerSetup.zeta_p_int =
        S.toConcreteStickelbergerSetup.zeta_p_int ^ (p - 1))
    (hσζell :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      σ S.toConcreteStickelbergerSetup.zeta_ell_int =
        S.toConcreteStickelbergerSetup.zeta_ell_int ^ (ℓ - 1)) :
    ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
      (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have hσχ :
      (S.toConcreteStickelbergerSetup.residueCharInt ^ 1).ringHomComp σ =
        (S.toConcreteStickelbergerSetup.residueCharInt ^ 1)⁻¹ :=
    S.toConcreteStickelbergerSetup
      |>.residueCharInt_pow_ringHomComp_eq_inv_of_zeta_p_int_map_pow_sub_one
        1 σ hσζp
  have hσψ :
      σ.toMonoidHom.compAddChar S.toConcreteStickelbergerSetup.psiInt =
        S.toConcreteStickelbergerSetup.psiInt⁻¹ := by
    simpa using
      (S.toFullTeichStickelbergerSetup.toTraceFormStickelbergerSetup
        |>.psiInt_compAddChar_eq_inv_of_zeta_ell_int_map_pow_sub_one
          σ hσζell)
  exact PhiPrimeElement.K2_2SourceData_phi_conj_mul_self_eq_absNorm_pow_of_ringHomComp
    (p := p) (K := K) D σ hσ_lifts_conj hσχ hσψ

/-- K2-2 source-data conjugation norm with the `p`-root action discharged
from the canonical source-data root choice. The remaining root-action input is
only the upstairs `ℓ`-root compatibility. -/
theorem PhiPrimeElement.K2_2SourceData_phi_conj_mul_self_eq_absNorm_pow_of_zetaEllRootAction
    [IsCMField K]
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : PhiPrimeElement.K2_2SourceData S)
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (hσζell :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      σ S.toConcreteStickelbergerSetup.zeta_ell_int =
        S.toConcreteStickelbergerSetup.zeta_ell_int ^ (ℓ - 1)) :
    ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
      (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have hσζp :
      σ S.toConcreteStickelbergerSetup.zeta_p_int =
        S.toConcreteStickelbergerSetup.zeta_p_int ^ (p - 1) :=
    S.zeta_p_int_map_pow_sub_one_of_lifts_conj
      (p := p) (K := K) σ hσ_lifts_conj D.h_zeta_p_int_eq
  exact PhiPrimeElement.K2_2SourceData_phi_conj_mul_self_eq_absNorm_pow_of_rootAction
    (p := p) (K := K) D σ hσ_lifts_conj hσζp hσζell

/-- K2-2 source-data conjugation norm using the actual upstairs complex
conjugation map. The only remaining compatibility input is that upstairs
complex conjugation restricts to complex conjugation on the embedded
`𝓞 K`. -/
theorem PhiPrimeElement.K2_2SourceData_phi_conj_mul_self_eq_absNorm_pow_of_upstairsComplexConj
    [IsCMField K]
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsCMField R']
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : PhiPrimeElement.K2_2SourceData S)
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
      σ S.toConcreteStickelbergerSetup.zeta_ell_int =
        S.toConcreteStickelbergerSetup.zeta_ell_int ^ (ℓ - 1) := by
    simpa [σ] using
      S.toConcreteStickelbergerSetup.zeta_ell_int_complexConj_eq_pow_sub_one
  exact PhiPrimeElement.K2_2SourceData_phi_conj_mul_self_eq_absNorm_pow_of_zetaEllRootAction
    (p := p) (K := K) D σ hσ_lifts_conj hσζell

/-- Reciprocal source-data conjugation norm from an upstairs ring endomorphism
realizing complex conjugation on the concrete character data. -/
theorem PhiPrimeElement.K2_2ReciprocalSourceData_phi_conj_mul_self_eq_absNorm_pow_of_ringHomComp
    [IsCMField K]
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : PhiPrimeElement.K2_2ReciprocalSourceData S)
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (hσχ :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      (S.toConcreteStickelbergerSetup.residueCharInt ^ (p - 1)).ringHomComp σ =
        (S.toConcreteStickelbergerSetup.residueCharInt ^ (p - 1))⁻¹)
    (hσψ :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      σ.toMonoidHom.compAddChar S.toConcreteStickelbergerSetup.psiInt =
        S.toConcreteStickelbergerSetup.psiInt⁻¹) :
    ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
      (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have hraw :
      ringOfIntegersComplexConj K
          (phiPrimeGenDescent S
            (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) D.h_ne_zero) *
          phiPrimeGenDescent S
            (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) D.h_ne_zero =
        (ℓ : 𝓞 K) ^ (S.toConcreteStickelbergerSetup.f * p) :=
    S.phiPrimeGenDescent_conj_mul_self_eq_ell_pow_of_ringHomComp
      (p := p) (K := K) (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1))
      D.h_ne_zero σ hσ_lifts_conj hσχ hσψ
  have h_abs :
      Ideal.absNorm P = ℓ ^ S.toConcreteStickelbergerSetup.f := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    exact S.toConcreteStickelbergerSetup.card_k
  rw [PhiPrimeElement.K2_2ReciprocalSourceData_phi_gamma]
  calc
    ringOfIntegersComplexConj K
          (phiPrimeGenDescent S
            (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) D.h_ne_zero) *
        phiPrimeGenDescent S
          (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1)) D.h_ne_zero
        = (ℓ : 𝓞 K) ^ (S.toConcreteStickelbergerSetup.f * p) := hraw
    _ = (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
          rw [h_abs, pow_mul]
          congr 1
          norm_num

/-- Reciprocal source-data conjugation norm from root-action compatibility of
the upstairs endomorphism. -/
theorem PhiPrimeElement.K2_2ReciprocalSourceData_phi_conj_mul_self_eq_absNorm_pow_of_rootAction
    [IsCMField K]
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : PhiPrimeElement.K2_2ReciprocalSourceData S)
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (hσζp :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      σ S.toConcreteStickelbergerSetup.zeta_p_int =
        S.toConcreteStickelbergerSetup.zeta_p_int ^ (p - 1))
    (hσζell :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      σ S.toConcreteStickelbergerSetup.zeta_ell_int =
        S.toConcreteStickelbergerSetup.zeta_ell_int ^ (ℓ - 1)) :
    ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
      (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have hσχ :
      (S.toConcreteStickelbergerSetup.residueCharInt ^ (p - 1)).ringHomComp σ =
        (S.toConcreteStickelbergerSetup.residueCharInt ^ (p - 1))⁻¹ :=
    S.toConcreteStickelbergerSetup
      |>.residueCharInt_pow_ringHomComp_eq_inv_of_zeta_p_int_map_pow_sub_one
        (p - 1) σ hσζp
  have hσψ :
      σ.toMonoidHom.compAddChar S.toConcreteStickelbergerSetup.psiInt =
        S.toConcreteStickelbergerSetup.psiInt⁻¹ := by
    simpa using
      (S.toFullTeichStickelbergerSetup.toTraceFormStickelbergerSetup
        |>.psiInt_compAddChar_eq_inv_of_zeta_ell_int_map_pow_sub_one
          σ hσζell)
  exact
    PhiPrimeElement.K2_2ReciprocalSourceData_phi_conj_mul_self_eq_absNorm_pow_of_ringHomComp
      (p := p) (K := K) D σ hσ_lifts_conj hσχ hσψ

/-- Reciprocal source-data conjugation norm with the `p`-root action
discharged from the canonical source-data root choice. -/
theorem
    PhiPrimeElement.K2_2ReciprocalSourceData_phi_conj_mul_self_eq_absNorm_pow_of_zetaEllRootAction
    [IsCMField K]
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : PhiPrimeElement.K2_2ReciprocalSourceData S)
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (hσζell :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      σ S.toConcreteStickelbergerSetup.zeta_ell_int =
        S.toConcreteStickelbergerSetup.zeta_ell_int ^ (ℓ - 1)) :
    ringOfIntegersComplexConj K D.phi.gamma * D.phi.gamma =
      (((Ideal.absNorm P : ℤ) : 𝓞 K)) ^ p := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  have hσζp :
      σ S.toConcreteStickelbergerSetup.zeta_p_int =
        S.toConcreteStickelbergerSetup.zeta_p_int ^ (p - 1) :=
    S.zeta_p_int_map_pow_sub_one_of_lifts_conj
      (p := p) (K := K) σ hσ_lifts_conj D.h_zeta_p_int_eq
  exact
    PhiPrimeElement.K2_2ReciprocalSourceData_phi_conj_mul_self_eq_absNorm_pow_of_rootAction
      (p := p) (K := K) D σ hσ_lifts_conj hσζp hσζell

/-- Reciprocal source-data conjugation norm using the actual upstairs complex
conjugation map. -/
theorem
    PhiPrimeElement.K2_2ReciprocalSourceData_phi_conj_mul_self_eq_absNorm_pow_of_upstairsComplexConj
    [IsCMField K]
    {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [NeZero p]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsCMField R']
    {P : Ideal (𝓞 K)} [P.IsMaximal] [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    {S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      FullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R'}
    (D : PhiPrimeElement.K2_2ReciprocalSourceData S)
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
      σ S.toConcreteStickelbergerSetup.zeta_ell_int =
        S.toConcreteStickelbergerSetup.zeta_ell_int ^ (ℓ - 1) := by
    simpa [σ] using
      S.toConcreteStickelbergerSetup.zeta_ell_int_complexConj_eq_pow_sub_one
  exact
    PhiPrimeElement.K2_2ReciprocalSourceData_phi_conj_mul_self_eq_absNorm_pow_of_zetaEllRootAction
      (p := p) (K := K) D σ hσ_lifts_conj hσζell

/-! ### Conductor-flexible source-data facts -/

end Furtwaengler

end BernoulliRegular

end

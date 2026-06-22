module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PrincipalUnitFactor.GaussSumPhiDescent.GaussSumCongruences

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField NumberField.IsCMField
open UniqueFactorizationMonoid

namespace BernoulliRegular

namespace Furtwaengler

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

namespace FullTeichDworkSetup

variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]

/-- The descended actual Φ-prime element satisfies
`phiPrimeGenDescent + 1 ∈ (ζ_p - 1)^2`.

This transports the concrete Gauss-sum congruence
`g(χ)^p ≡ -1 (mod (ζ_p - 1)^2)` from the ambient cyclotomic integer ring
`𝓞 R'` back to `𝓞 K`, using principal divisibility descent. -/
theorem phiPrimeGenDescent_add_one_mem_zetaSubOne_sq
    (S : FullTeichDworkSetup ℓ p k K R') {a : ℕ}
    (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    (hp_three : 3 ≤ p)
    (h_zeta_p_int_eq :
      S.zeta_p_int =
        algebraMap (𝓞 K) (𝓞 R') (cyclotomicZetaInteger (p := p) K)) :
    phiPrimeGenDescent S ha₁ ha₂ h_ne_zero + 1 ∈
      (Ideal.span ({FLT37.zetaSubOne p K} : Set (𝓞 K))) ^ 2 := by
  let γ : 𝓞 K := phiPrimeGenDescent S ha₁ ha₂ h_ne_zero
  let ε : 𝓞 K := FLT37.zetaSubOne p K
  have hzeta_sub :
      S.zeta_p_int - 1 = algebraMap (𝓞 K) (𝓞 R') ε := by
    rw [h_zeta_p_int_eq]
    calc
      algebraMap (𝓞 K) (𝓞 R') (cyclotomicZetaInteger (p := p) K) - 1 =
          algebraMap (𝓞 K) (𝓞 R')
            (cyclotomicZetaInteger (p := p) K - 1) := by
            rw [map_sub, map_one]
      _ = algebraMap (𝓞 K) (𝓞 R') ε := by
            congr 1
  have h_ambient :
      S.gaussSumInt a ^ p + 1 ∈
        (Ideal.span ({algebraMap (𝓞 K) (𝓞 R') ε} : Set (𝓞 R'))) ^ 2 := by
    simpa [hzeta_sub] using
      (S.toConcreteStickelbergerSetup.gaussSumInt_pow_add_one_mem_zeta_p_sub_one_sq'
        a hp_three)
  have h_map :
      algebraMap (𝓞 K) (𝓞 R') (γ + 1) ∈
        (Ideal.span ({algebraMap (𝓞 K) (𝓞 R') ε} : Set (𝓞 R'))) ^ 2 := by
    rw [map_add, show algebraMap (𝓞 K) (𝓞 R') γ =
        S.gaussSumInt a ^ p by
      exact algebraMap_phiPrimeGenDescent S ha₁ ha₂ h_ne_zero, map_one]
    exact h_ambient
  have h_map_single :
      algebraMap (𝓞 K) (𝓞 R') (γ + 1) ∈
        Ideal.span ({algebraMap (𝓞 K) (𝓞 R') (ε ^ 2)} : Set (𝓞 R')) := by
    simpa [Ideal.span_singleton_pow, map_pow] using h_map
  have h_desc :
      γ + 1 ∈ Ideal.span ({ε ^ 2} : Set (𝓞 K)) :=
    mem_span_singleton_pow_two_of_algebraMap_mem_span_singleton_pow_two
      (K := K) (R' := R') (ε := ε) (x := γ + 1)
      (by
        simpa [ε] using FLT37.zetaSubOne_ne_zero (p := p) (K := K))
      h_map_single
  simpa [γ, ε, Ideal.span_singleton_pow] using h_desc

/-- The actual descended prime Φ element is semi-primary. -/
theorem phiPrimeGenDescent_isSemiPrimary
    (S : FullTeichDworkSetup ℓ p k K R') {a : ℕ}
    (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    (hp_three : 3 ≤ p)
    (h_zeta_p_int_eq :
      S.zeta_p_int =
        algebraMap (𝓞 K) (𝓞 R') (cyclotomicZetaInteger (p := p) K)) :
    FLT37.IsSemiPrimary p (K := K)
      (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) := by
  refine ⟨-1, ?_⟩
  have hmem :=
    S.phiPrimeGenDescent_add_one_mem_zetaSubOne_sq
      ha₁ ha₂ h_ne_zero hp_three h_zeta_p_int_eq
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  convert hmem using 1
  norm_num

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Prime-Φ conjugation norm from the concrete upstairs Gauss-sum
conjugation compatibility.

The only substantive input is `h_conj_lift`: after embedding the descended
element into `𝓞 R'`, complex conjugation on `𝓞 K` becomes the
inverse-character/inverse-additive Gauss sum upstairs. Once that is known,
mathlib's Gauss-sum norm relation gives
`conj(phiPrimeGenDescent) * phiPrimeGenDescent = ℓ^(f*p)` in `𝓞 K`. -/
theorem phiPrimeGenDescent_conj_mul_self_eq_ell_pow_of_algebraMap_conj_eq_inv_gauss
    [IsCMField K]
    (S : FullTeichDworkSetup ℓ p k K R') {a : ℕ}
    (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    (h_conj_lift :
      algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K
        (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero)) =
        (_root_.gaussSum
          (S.toConcreteStickelbergerSetup.residueCharInt ^ a)⁻¹
          S.toConcreteStickelbergerSetup.psiInt⁻¹) ^ p) :
    ringOfIntegersComplexConj K
        (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) *
        phiPrimeGenDescent S ha₁ ha₂ h_ne_zero =
      (ℓ : 𝓞 K) ^ (S.toConcreteStickelbergerSetup.f * p) := by
  haveI : FaithfulSMul (𝓞 K) (𝓞 R') :=
    S.toConcreteStickelbergerSetup.faithfulSMul_OK_OR'_of_cyclotomic
  apply FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 R')
  calc
    algebraMap (𝓞 K) (𝓞 R')
        (ringOfIntegersComplexConj K
          (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) *
          phiPrimeGenDescent S ha₁ ha₂ h_ne_zero)
        =
        (_root_.gaussSum
          (S.toConcreteStickelbergerSetup.residueCharInt ^ a)⁻¹
          S.toConcreteStickelbergerSetup.psiInt⁻¹) ^ p *
          S.gaussSumInt a ^ p := by
          rw [map_mul, h_conj_lift,
            algebraMap_phiPrimeGenDescent S ha₁ ha₂ h_ne_zero]
    _ = S.gaussSumInt a ^ p *
        (_root_.gaussSum
          (S.toConcreteStickelbergerSetup.residueCharInt ^ a)⁻¹
          S.toConcreteStickelbergerSetup.psiInt⁻¹) ^ p := by
          ring
    _ = (ℓ : 𝓞 R') ^ (S.toConcreteStickelbergerSetup.f * p) :=
          S.gaussSumInt_pow_p_mul_inv_pow_p_eq_ell_pow ha₁ ha₂
    _ = algebraMap (𝓞 K) (𝓞 R')
        ((ℓ : 𝓞 K) ^ (S.toConcreteStickelbergerSetup.f * p)) := by
          simp

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- The upstairs ring-endomorphism form of the remaining prime-Φ conjugation
compatibility.

If `σ : 𝓞 R' →+* 𝓞 R'` lifts complex conjugation from `𝓞 K` and sends the
integral residue/additive characters to their inverses, then the embedded
complex conjugate of the descended Φ-prime generator is exactly the
inverse-character/inverse-additive Gauss sum to the `p`-th power. -/
theorem algebraMap_conj_phiPrimeGenDescent_eq_inv_gauss_pow_of_ringHomComp
    [IsCMField K]
    (S : FullTeichDworkSetup ℓ p k K R') {a : ℕ}
    (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (hσχ :
      (S.toConcreteStickelbergerSetup.residueCharInt ^ a).ringHomComp σ =
        (S.toConcreteStickelbergerSetup.residueCharInt ^ a)⁻¹)
    (hσψ :
      σ.toMonoidHom.compAddChar S.toConcreteStickelbergerSetup.psiInt =
        S.toConcreteStickelbergerSetup.psiInt⁻¹) :
    algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K
        (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero)) =
      (_root_.gaussSum
        (S.toConcreteStickelbergerSetup.residueCharInt ^ a)⁻¹
        S.toConcreteStickelbergerSetup.psiInt⁻¹) ^ p := by
  calc
    algebraMap (𝓞 K) (𝓞 R')
        (ringOfIntegersComplexConj K
          (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero))
        =
        σ (algebraMap (𝓞 K) (𝓞 R')
          (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero)) := by
          rw [hσ_lifts_conj]
    _ = σ (S.gaussSumInt a ^ p) := by
          rw [algebraMap_phiPrimeGenDescent S ha₁ ha₂ h_ne_zero]
    _ = σ (S.gaussSumInt a) ^ p := by
          rw [map_pow]
    _ =
        (_root_.gaussSum
          (S.toConcreteStickelbergerSetup.residueCharInt ^ a)⁻¹
          S.toConcreteStickelbergerSetup.psiInt⁻¹) ^ p := by
          rw [ConcreteStickelbergerSetup.gaussSumInt]
          rw [gaussSum_map_eq_inv_inv_of_ringHomComp
            (S.toConcreteStickelbergerSetup.residueCharInt ^ a)
            S.toConcreteStickelbergerSetup.psiInt σ hσχ hσψ]

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Prime-Φ conjugation norm from an upstairs ring endomorphism realizing
complex conjugation on the concrete character data. -/
theorem phiPrimeGenDescent_conj_mul_self_eq_ell_pow_of_ringHomComp
    [IsCMField K]
    (S : FullTeichDworkSetup ℓ p k K R') {a : ℕ}
    (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (hσχ :
      (S.toConcreteStickelbergerSetup.residueCharInt ^ a).ringHomComp σ =
        (S.toConcreteStickelbergerSetup.residueCharInt ^ a)⁻¹)
    (hσψ :
      σ.toMonoidHom.compAddChar S.toConcreteStickelbergerSetup.psiInt =
        S.toConcreteStickelbergerSetup.psiInt⁻¹) :
    ringOfIntegersComplexConj K
        (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) *
        phiPrimeGenDescent S ha₁ ha₂ h_ne_zero =
      (ℓ : 𝓞 K) ^ (S.toConcreteStickelbergerSetup.f * p) :=
  S.phiPrimeGenDescent_conj_mul_self_eq_ell_pow_of_algebraMap_conj_eq_inv_gauss
    (p := p) (K := K) ha₁ ha₂ h_ne_zero
    (S.algebraMap_conj_phiPrimeGenDescent_eq_inv_gauss_pow_of_ringHomComp
      (p := p) (K := K) ha₁ ha₂ h_ne_zero σ hσ_lifts_conj hσχ hσψ)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Prime-Φ conjugation norm from root-action compatibility of an upstairs
endomorphism: `ζ_p ↦ ζ_p^(p-1)` gives the inverse residue character and
`ζ_ℓ ↦ ζ_ℓ^(ℓ-1)` gives the inverse trace-form additive character. -/
theorem phiPrimeGenDescent_conj_mul_self_eq_ell_pow_of_rootAction
    [IsCMField K]
    (S : FullTeichDworkSetup ℓ p k K R') {a : ℕ}
    (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (hσζp :
      σ S.toConcreteStickelbergerSetup.zeta_p_int =
        S.toConcreteStickelbergerSetup.zeta_p_int ^ (p - 1))
    (hσζell :
      σ S.toConcreteStickelbergerSetup.zeta_ell_int =
        S.toConcreteStickelbergerSetup.zeta_ell_int ^ (ℓ - 1)) :
    ringOfIntegersComplexConj K
        (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) *
        phiPrimeGenDescent S ha₁ ha₂ h_ne_zero =
      (ℓ : 𝓞 K) ^ (S.toConcreteStickelbergerSetup.f * p) := by
  have hσχ :
      (S.toConcreteStickelbergerSetup.residueCharInt ^ a).ringHomComp σ =
        (S.toConcreteStickelbergerSetup.residueCharInt ^ a)⁻¹ :=
    S.toConcreteStickelbergerSetup
      |>.residueCharInt_pow_ringHomComp_eq_inv_of_zeta_p_int_map_pow_sub_one
        a σ hσζp
  have hσψ :
      σ.toMonoidHom.compAddChar S.toConcreteStickelbergerSetup.psiInt =
        S.toConcreteStickelbergerSetup.psiInt⁻¹ := by
    simpa using
      (S.toFullTeichStickelbergerSetup.toTraceFormStickelbergerSetup
        |>.psiInt_compAddChar_eq_inv_of_zeta_ell_int_map_pow_sub_one
          σ hσζell)
  exact S.phiPrimeGenDescent_conj_mul_self_eq_ell_pow_of_ringHomComp
    (p := p) (K := K) ha₁ ha₂ h_ne_zero σ hσ_lifts_conj hσχ hσψ

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- The canonical source-data choice of `ζ_p` has the correct conjugation
action as soon as the upstairs endomorphism lifts complex conjugation from
`𝓞 K`. -/
theorem zeta_p_int_map_pow_sub_one_of_lifts_conj
    [IsCMField K]
    (S : FullTeichDworkSetup ℓ p k K R')
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (h_zeta_p_int_eq :
      S.toConcreteStickelbergerSetup.zeta_p_int =
        algebraMap (𝓞 K) (𝓞 R') (cyclotomicZetaInteger (p := p) K)) :
    σ S.toConcreteStickelbergerSetup.zeta_p_int =
      S.toConcreteStickelbergerSetup.zeta_p_int ^ (p - 1) := by
  rw [h_zeta_p_int_eq, hσ_lifts_conj]
  have hconj :
      ringOfIntegersComplexConj K (cyclotomicZetaInteger (p := p) K) =
        cyclotomicZetaInteger (p := p) K ^ (p - 1) := by
    simpa [cyclotomicZetaInteger] using
      (complexConj_apply_zeta (p := p) (K := K))
  rw [hconj, map_pow]

end FullTeichDworkSetup

namespace ConductorFlexibleFullTeichDworkSetup

variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsScalarTower ℤ (𝓞 K) (𝓞 R')]

/-- The conductor-flexible descended actual Φ-prime element satisfies
`phiPrimeGenDescent + 1 ∈ (ζ_p - 1)^2`. -/
theorem phiPrimeGenDescent_add_one_mem_zetaSubOne_sq
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    (hp_three : 3 ≤ p)
    (h_zeta_p_int_eq :
      S.zeta_p_int =
        algebraMap (𝓞 K) (𝓞 R') (cyclotomicZetaInteger (p := p) K)) :
    S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero + 1 ∈
      (Ideal.span ({FLT37.zetaSubOne p K} : Set (𝓞 K))) ^ 2 := by
  let γ : 𝓞 K := S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero
  let ε : 𝓞 K := FLT37.zetaSubOne p K
  have hzeta_sub :
      S.zeta_p_int - 1 = algebraMap (𝓞 K) (𝓞 R') ε := by
    rw [h_zeta_p_int_eq]
    calc
      algebraMap (𝓞 K) (𝓞 R') (cyclotomicZetaInteger (p := p) K) - 1 =
          algebraMap (𝓞 K) (𝓞 R')
            (cyclotomicZetaInteger (p := p) K - 1) := by
            rw [map_sub, map_one]
      _ = algebraMap (𝓞 K) (𝓞 R') ε := by
            congr 1
  have hzeta_sub_concrete :
      S.concrete.zeta_p_int - 1 = algebraMap (𝓞 K) (𝓞 R') ε := by
    simpa [ConductorFlexibleFullTeichStickelbergerSetup.concrete,
      ConductorFlexibleTraceFormStickelbergerSetup.concrete] using hzeta_sub
  have h_ambient_concrete :
      S.concrete.gaussSumInt a ^ p + 1 ∈
        (Ideal.span ({algebraMap (𝓞 K) (𝓞 R') ε} : Set (𝓞 R'))) ^ 2 := by
    simpa [hzeta_sub_concrete] using
      (S.concrete.gaussSumInt_pow_add_one_mem_zeta_p_sub_one_sq'
        a hp_three)
  have h_ambient :
      S.gaussSumInt a ^ p + 1 ∈
        (Ideal.span ({algebraMap (𝓞 K) (𝓞 R') ε} : Set (𝓞 R'))) ^ 2 := by
    simpa [ConductorFlexibleFullTeichStickelbergerSetup.concrete,
      ConductorFlexibleTraceFormStickelbergerSetup.concrete] using h_ambient_concrete
  have h_map :
      algebraMap (𝓞 K) (𝓞 R') (γ + 1) ∈
        (Ideal.span ({algebraMap (𝓞 K) (𝓞 R') ε} : Set (𝓞 R'))) ^ 2 := by
    rw [map_add, show algebraMap (𝓞 K) (𝓞 R') γ =
        S.gaussSumInt a ^ p by
      exact S.algebraMap_phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero, map_one]
    exact h_ambient
  have h_map_single :
      algebraMap (𝓞 K) (𝓞 R') (γ + 1) ∈
        Ideal.span ({algebraMap (𝓞 K) (𝓞 R') (ε ^ 2)} : Set (𝓞 R')) := by
    simpa [Ideal.span_singleton_pow, map_pow] using h_map
  have h_desc :
      γ + 1 ∈ Ideal.span ({ε ^ 2} : Set (𝓞 K)) :=
    mem_span_singleton_pow_two_of_algebraMap_mem_span_singleton_pow_two
      (K := K) (R' := R') (ε := ε) (x := γ + 1)
      (by
        simpa [ε] using FLT37.zetaSubOne_ne_zero (p := p) (K := K))
      h_map_single
  simpa [γ, ε, Ideal.span_singleton_pow] using h_desc

/-- The conductor-flexible actual descended prime Φ element is
semi-primary. -/
theorem phiPrimeGenDescent_isSemiPrimary
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    (hp_three : 3 ≤ p)
    (h_zeta_p_int_eq :
      S.zeta_p_int =
        algebraMap (𝓞 K) (𝓞 R') (cyclotomicZetaInteger (p := p) K)) :
    FLT37.IsSemiPrimary p (K := K)
      (S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero) := by
  refine ⟨-1, ?_⟩
  have hmem :=
    S.phiPrimeGenDescent_add_one_mem_zetaSubOne_sq
      h_psi ha₁ ha₂ h_ne_zero hp_three h_zeta_p_int_eq
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  convert hmem using 1
  norm_num

/-- Flexible prime-Φ conjugation norm from the concrete upstairs Gauss-sum
conjugation compatibility. -/
theorem phiPrimeGenDescent_conj_mul_self_eq_ell_pow_of_algebraMap_conj_eq_inv_gauss
    [IsCMField K]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    (h_conj_lift :
      algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K
        (S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero)) =
        (_root_.gaussSum
          (S.concrete.residueCharInt ^ a)⁻¹
          S.concrete.psiInt⁻¹) ^ p) :
    ringOfIntegersComplexConj K
        (S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero) *
        S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero =
      (ℓ : 𝓞 K) ^ (S.concrete.f * p) := by
  apply FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 R')
  calc
    algebraMap (𝓞 K) (𝓞 R')
        (ringOfIntegersComplexConj K
          (S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero) *
          S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero)
        =
        (_root_.gaussSum
          (S.concrete.residueCharInt ^ a)⁻¹
          S.concrete.psiInt⁻¹) ^ p *
          S.gaussSumInt a ^ p := by
          rw [map_mul, h_conj_lift,
            S.algebraMap_phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero]
    _ = S.gaussSumInt a ^ p *
        (_root_.gaussSum
          (S.concrete.residueCharInt ^ a)⁻¹
          S.concrete.psiInt⁻¹) ^ p := by
          ring
    _ = (ℓ : 𝓞 R') ^ (S.concrete.f * p) :=
          S.gaussSumInt_pow_p_mul_inv_pow_p_eq_ell_pow ha₁ ha₂
    _ = algebraMap (𝓞 K) (𝓞 R')
        ((ℓ : 𝓞 K) ^ (S.concrete.f * p)) := by
          simp

/-- Flexible upstairs ring-endomorphism form of the remaining prime-Φ
conjugation compatibility. -/
theorem algebraMap_conj_phiPrimeGenDescent_eq_inv_gauss_pow_of_ringHomComp
    [IsCMField K]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (hσχ :
      (S.concrete.residueCharInt ^ a).ringHomComp σ =
        (S.concrete.residueCharInt ^ a)⁻¹)
    (hσψ :
      σ.toMonoidHom.compAddChar S.concrete.psiInt =
        S.concrete.psiInt⁻¹) :
    algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K
        (S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero)) =
      (_root_.gaussSum
        (S.concrete.residueCharInt ^ a)⁻¹
        S.concrete.psiInt⁻¹) ^ p := by
  calc
    algebraMap (𝓞 K) (𝓞 R')
        (ringOfIntegersComplexConj K
          (S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero))
        =
        σ (algebraMap (𝓞 K) (𝓞 R')
          (S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero)) := by
          rw [hσ_lifts_conj]
    _ = σ (S.gaussSumInt a ^ p) := by
          rw [S.algebraMap_phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero]
    _ = σ (S.gaussSumInt a) ^ p := by
          rw [map_pow]
    _ =
        (_root_.gaussSum
          (S.concrete.residueCharInt ^ a)⁻¹
          S.concrete.psiInt⁻¹) ^ p := by
          change σ (S.concrete.gaussSumInt a) ^ p =
            (_root_.gaussSum
              (S.concrete.residueCharInt ^ a)⁻¹
              S.concrete.psiInt⁻¹) ^ p
          rw [ConductorFlexibleConcreteStickelbergerSetup.gaussSumInt]
          rw [gaussSum_map_eq_inv_inv_of_ringHomComp
            (S.concrete.residueCharInt ^ a)
            S.concrete.psiInt σ hσχ hσψ]

/-- Flexible prime-Φ conjugation norm from an upstairs ring endomorphism
realizing complex conjugation on the concrete character data. -/
theorem phiPrimeGenDescent_conj_mul_self_eq_ell_pow_of_ringHomComp
    [IsCMField K]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (hσχ :
      (S.concrete.residueCharInt ^ a).ringHomComp σ =
        (S.concrete.residueCharInt ^ a)⁻¹)
    (hσψ :
      σ.toMonoidHom.compAddChar S.concrete.psiInt =
        S.concrete.psiInt⁻¹) :
    ringOfIntegersComplexConj K
        (S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero) *
        S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero =
      (ℓ : 𝓞 K) ^ (S.concrete.f * p) :=
  S.phiPrimeGenDescent_conj_mul_self_eq_ell_pow_of_algebraMap_conj_eq_inv_gauss
    (p := p) (K := K) h_psi ha₁ ha₂ h_ne_zero
    (algebraMap_conj_phiPrimeGenDescent_eq_inv_gauss_pow_of_ringHomComp
      S
      (p := p) (K := K) h_psi ha₁ ha₂ h_ne_zero σ hσ_lifts_conj hσχ hσψ)

/-- Flexible prime-Φ conjugation norm from source-conductor root-action
compatibility of an upstairs endomorphism. -/
theorem phiPrimeGenDescent_conj_mul_self_eq_ell_pow_of_rootAction
    [IsCMField K]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (hσζp :
      σ S.concrete.zeta_p_int =
        S.concrete.zeta_p_int ^ (p - 1))
    (hσζell :
      σ S.concrete.zeta_ell_int =
        S.concrete.zeta_ell_int ^ (ℓ - 1)) :
    ringOfIntegersComplexConj K
        (S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero) *
        S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero =
      (ℓ : 𝓞 K) ^ (S.concrete.f * p) := by
  have hσχ :
      (S.concrete.residueCharInt ^ a).ringHomComp σ =
        (S.concrete.residueCharInt ^ a)⁻¹ :=
    S.concrete
      |>.residueCharInt_pow_ringHomComp_eq_inv_of_zeta_p_int_map_pow_sub_one
        a σ hσζp
  have hσψ :
      σ.toMonoidHom.compAddChar S.concrete.psiInt =
        S.concrete.psiInt⁻¹ := by
    exact
      (S.toConductorFlexibleFullTeichStickelbergerSetup
        |>.toConductorFlexibleTraceFormStickelbergerSetup
        |>.psiInt_compAddChar_eq_inv_of_zeta_ell_int_map_pow_sub_one
          σ hσζell)
  exact S.phiPrimeGenDescent_conj_mul_self_eq_ell_pow_of_ringHomComp
    (p := p) (K := K) h_psi ha₁ ha₂ h_ne_zero σ hσ_lifts_conj hσχ hσψ

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- The canonical source-data choice of `ζ_p` has the correct conjugation
action as soon as the source-conductor endomorphism lifts complex conjugation
from `𝓞 K`. -/
theorem zeta_p_int_map_pow_sub_one_of_lifts_conj
    [IsCMField K]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (σ : 𝓞 R' →+* 𝓞 R')
    (hσ_lifts_conj : ∀ x : 𝓞 K,
      σ (algebraMap (𝓞 K) (𝓞 R') x) =
        algebraMap (𝓞 K) (𝓞 R') (ringOfIntegersComplexConj K x))
    (h_zeta_p_int_eq :
      S.concrete.zeta_p_int =
        algebraMap (𝓞 K) (𝓞 R') (cyclotomicZetaInteger (p := p) K)) :
    σ S.concrete.zeta_p_int =
      S.concrete.zeta_p_int ^ (p - 1) := by
  rw [h_zeta_p_int_eq, hσ_lifts_conj]
  have hconj :
      ringOfIntegersComplexConj K (cyclotomicZetaInteger (p := p) K) =
        cyclotomicZetaInteger (p := p) K ^ (p - 1) := by
    simpa [cyclotomicZetaInteger] using
      (complexConj_apply_zeta (p := p) (K := K))
  rw [hconj, map_pow]

end ConductorFlexibleFullTeichDworkSetup

/-! ### Semi-primary congruences under the cyclotomic Galois action -/

/-- The cyclotomic automorphism indexed by `a` sends `ζ - 1` to
`ζ^a - 1`. -/
theorem cyclotomicRingOfIntegersEquiv_zetaSubOne
    (a : CyclotomicUnitDelta p) :
    cyclotomicRingOfIntegersEquiv (p := p) K a (FLT37.zetaSubOne p K) =
      ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) ^
        (a : ZMod p).val - 1 := by
  change cyclotomicSigmaOfUnit (p := p) K a •
      (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) =
    _
  rw [← MulSemiringAction.toRingHom_apply Gal(K / ℚ) _
      (cyclotomicSigmaOfUnit (p := p) K a)]
  simp only [map_sub, map_one, MulSemiringAction.toRingHom_apply]
  rw [show ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) =
      cyclotomicZetaInteger (p := p) K from rfl,
    cyclotomicSigmaOfUnit_smul_zetaInteger]

/-- The cyclotomic automorphism indexed by `a` preserves the prime above `p`
generated by `ζ - 1`, up to association. -/
theorem associated_zetaSubOne_cyclotomicRingOfIntegersEquiv_zetaSubOne
    (hp_two : 2 ≤ p) (a : CyclotomicUnitDelta p) :
    Associated (FLT37.zetaSubOne p K)
      (cyclotomicRingOfIntegersEquiv (p := p) K a (FLT37.zetaSubOne p K)) := by
  have ha_coprime : ((a : ZMod p).val).Coprime p := by
    have hp_prime : Nat.Prime p := Fact.out
    rw [Nat.coprime_comm, hp_prime.coprime_iff_not_dvd]
    intro h_dvd
    have ha_lt : (a : ZMod p).val < p := ZMod.val_lt (a : ZMod p)
    have ha_zero : (a : ZMod p).val = 0 :=
      Nat.eq_zero_of_dvd_of_lt h_dvd ha_lt
    have ha_cast : ((a : ZMod p).val : ZMod p) = (a : ZMod p) :=
      ZMod.natCast_zmod_val (a : ZMod p)
    rw [ha_zero] at ha_cast
    push_cast at ha_cast
    exact a.isUnit.ne_zero ha_cast.symm
  rw [cyclotomicRingOfIntegersEquiv_zetaSubOne]
  simpa [FLT37.zetaSubOne] using
    FLT37.associated_zeta_sub_one_zeta_pow_sub_one
      (p := p) (K := K) (a : ZMod p).val ha_coprime hp_two

/-- Semi-primarity is invariant under the cyclotomic Galois action. -/
theorem isSemiPrimary_cyclotomicRingOfIntegersEquiv
    (hp_two : 2 ≤ p) (a : CyclotomicUnitDelta p) {α : 𝓞 K}
    (hα : FLT37.IsSemiPrimary p (K := K) α) :
    FLT37.IsSemiPrimary p (K := K)
      (cyclotomicRingOfIntegersEquiv (p := p) K a α) := by
  obtain ⟨n, hn⟩ := hα
  refine ⟨n, ?_⟩
  have h_map :
      cyclotomicRingOfIntegersEquiv (p := p) K a (FLT37.zetaSubOne p K) ^ 2 ∣
        cyclotomicRingOfIntegersEquiv (p := p) K a (α - (n : 𝓞 K)) := by
    have h :=
      map_dvd (cyclotomicRingOfIntegersEquiv (p := p) K a).toRingHom hn
    simpa [map_pow] using h
  have h_assoc :
      Associated ((FLT37.zetaSubOne p K) ^ 2)
        (cyclotomicRingOfIntegersEquiv (p := p) K a
          (FLT37.zetaSubOne p K) ^ 2) :=
    (associated_zetaSubOne_cyclotomicRingOfIntegersEquiv_zetaSubOne
      (p := p) (K := K) hp_two a).pow_pow
  have h_sub :
      cyclotomicRingOfIntegersEquiv (p := p) K a α - (n : 𝓞 K) =
        cyclotomicRingOfIntegersEquiv (p := p) K a (α - (n : 𝓞 K)) := by
    simp
  rw [h_sub]
  exact h_assoc.dvd.trans h_map

/-- The cyclotomic Galois action preserves being prime to `ζ - 1`. -/
theorem not_zetaSubOne_dvd_cyclotomicRingOfIntegersEquiv
    (hp_two : 2 ≤ p) (a : CyclotomicUnitDelta p) {α : 𝓞 K}
    (hα : ¬ FLT37.zetaSubOne p K ∣ α) :
    ¬ FLT37.zetaSubOne p K ∣
      cyclotomicRingOfIntegersEquiv (p := p) K a α := by
  intro hdiv
  have hmap :=
    map_dvd (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹).toRingHom hdiv
  have h_assoc :
      Associated (FLT37.zetaSubOne p K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹
          (FLT37.zetaSubOne p K)) :=
    associated_zetaSubOne_cyclotomicRingOfIntegersEquiv_zetaSubOne
      (p := p) (K := K) hp_two a⁻¹
  change cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹
      (FLT37.zetaSubOne p K) ∣
    cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹
      (cyclotomicRingOfIntegersEquiv (p := p) K a α) at hmap
  rw [← cyclotomicRingOfIntegersEquiv_mul_apply, inv_mul_cancel,
    cyclotomicRingOfIntegersEquiv_one_apply] at hmap
  exact hα (h_assoc.dvd.trans hmap)

/-- Powers of semi-primary elements are semi-primary. -/
theorem isSemiPrimary_pow {α : 𝓞 K}
    (hα : FLT37.IsSemiPrimary p (K := K) α) (n : ℕ) :
    FLT37.IsSemiPrimary p (K := K) (α ^ n) := by
  induction n with
  | zero =>
      simpa using FLT37.IsSemiPrimary.one (p := p) (K := K)
  | succ n ih =>
      rw [pow_succ]
      exact ih.mul hα

end Furtwaengler

end BernoulliRegular

end

end

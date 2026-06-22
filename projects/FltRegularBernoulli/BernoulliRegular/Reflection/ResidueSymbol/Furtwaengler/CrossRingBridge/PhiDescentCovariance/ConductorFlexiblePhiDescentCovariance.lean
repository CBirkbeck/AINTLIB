module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PhiPrimeSymbol
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerIdealEquality
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Uniformizer
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicPairGalois
public import Mathlib.RingTheory.Ideal.GoingUp
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CrossRingBridge.ResidueFieldBridgeAndDescentGenerator

/-!
# Cross-ring bridge: 𝓞 K / P' inside 𝓞 R' / 𝔭

For a prime ideal `P'` of `𝓞 K` and a prime `𝔭` of `𝓞 R'` lying over `P'`
(in a finite extension `R' / K`), the residue field `𝓞 R' / 𝔭` extends
the residue field `𝓞 K / P'`. This file builds the bridge:

* Existence of `𝔭` over a maximal `P'` (via going-up).
* Canonical injection `𝓞 K / P' → 𝓞 R' / 𝔭`.
* Compatible CharP transfer.

This is the first cross-ring atomic step toward K2-2 path (a):
applying the K2-1 atom in `𝓞 R' / 𝔭` (where `gaussSumInt` lives via
`algebraMap 𝓞 K 𝓞 R'`) and pulling back to `𝓞 K / P'`.

Per AI reviewer 2026-05-05 K2-2 plan: the descent atom requires this
bridge to apply K2-1 in the right ambient ring. Multi-week scope per
the plan; this file is the first chunk.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

/-! ### Existence of a prime above `P'` in an integral extension -/

/-- If a ring hom sends the selected target primitive `p`-th root to its
`b`-th power, then it sends the concrete residue character to its `b`-th
power. This is the concrete multiplicative-character covariance needed by
the non-`K` cyclotomic automorphisms. -/
theorem ConcreteStickelbergerSetup.residueChar_ringHomComp_eq_pow_of_zeta_p_action
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : ConcreteStickelbergerSetup ℓ p k K R')
    (τ : R' →+* R') (b : ℕ)
    (hτζ : τ ((S.zeta_p : R'ˣ) : R') = ((S.zeta_p : R'ˣ) : R') ^ b) :
    S.residueChar.ringHomComp τ = S.residueChar ^ b := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact residueMulChar_ringHomComp_pow_eq
    S.zeta_k S.hzeta_k S.hdiv S.zeta_p S.hzeta_p τ b hτζ

/-- If a ring hom fixes the selected primitive `ℓ`-th root in a trace-form
bundle, then it fixes the additive character. -/
theorem TraceFormStickelbergerSetup.ringHom_compAddChar_eq_self_of_zeta_ell_fixed
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : TraceFormStickelbergerSetup ℓ p k K R')
    (τ : R' →+* R')
    (hτζ : τ S.zeta_ell = S.zeta_ell) :
    τ.toMonoidHom.compAddChar S.psi = S.psi := by
  have hval_one : ((1 : (ZMod ℓ)ˣ) : ZMod ℓ).val = 1 := by
    haveI : Fact (1 < ℓ) := ⟨(Fact.out : Nat.Prime ℓ).one_lt⟩
    simpa using (ZMod.val_one ℓ)
  have hact : τ S.zeta_ell = S.zeta_ell ^ ((1 : (ZMod ℓ)ˣ) : ZMod ℓ).val := by
    rw [hval_one]
    simpa using hτζ
  have hshift := S.psi_shift_of_zetaEll_action τ (1 : (ZMod ℓ)ˣ) hact
  simpa [AddChar.mulShift_one] using hshift

/-- Conductor-flexible analogue of
`ConcreteStickelbergerSetup.residueChar_ringHomComp_eq_pow_of_zeta_p_action`. -/
theorem ConductorFlexibleConcreteStickelbergerSetup.residueChar_ringHomComp_eq_pow_of_zeta_p_action
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R')
    (τ : R' →+* R') (b : ℕ)
    (hτζ : τ ((S.zeta_p : R'ˣ) : R') = ((S.zeta_p : R'ˣ) : R') ^ b) :
    S.residueChar.ringHomComp τ = S.residueChar ^ b := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact residueMulChar_ringHomComp_pow_eq
    S.zeta_k S.hzeta_k S.hdiv S.zeta_p S.hzeta_p τ b hτζ

/-- Conductor-flexible analogue of
`TraceFormStickelbergerSetup.ringHom_compAddChar_eq_self_of_zeta_ell_fixed`. -/
theorem ConductorFlexibleTraceFormStickelbergerSetup.ringHom_compAddChar_eq_self_of_zeta_ell_fixed
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleTraceFormStickelbergerSetup ℓ p k K R')
    (τ : R' →+* R')
    (hτζ : τ S.zeta_ell = S.zeta_ell) :
    τ.toMonoidHom.compAddChar S.psi = S.psi := by
  have hval_one : ((1 : (ZMod ℓ)ˣ) : ZMod ℓ).val = 1 := by
    haveI : Fact (1 < ℓ) := ⟨(Fact.out : Nat.Prime ℓ).one_lt⟩
    simpa using (ZMod.val_one ℓ)
  have hact : τ S.zeta_ell = S.zeta_ell ^ ((1 : (ZMod ℓ)ˣ) : ZMod ℓ).val := by
    rw [hval_one]
    simpa using hτζ
  have hshift := S.psi_shift_of_zetaEll_action τ (1 : (ZMod ℓ)ˣ) hact
  simpa [AddChar.mulShift_one] using hshift

/-- Applying a target ring hom to the conductor-flexible field-valued
integral Gauss sum changes the character and additive character by
post-composition. -/
theorem ConductorFlexibleConcreteStickelbergerSetup.ringHom_gaussSumInt_eq_of_residueChar_psi
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R')
    (τ : R' →+* R') {a b : ℕ}
    (hχ : (S.residueChar ^ a).ringHomComp τ = S.residueChar ^ b)
    (hψ : τ.toMonoidHom.compAddChar S.psi = S.psi) :
    τ (algebraMap (𝓞 R') R' (S.gaussSumInt a)) =
      algebraMap (𝓞 R') R' (S.gaussSumInt b) := by
  rw [S.algebraMap_gaussSumInt a, S.algebraMap_gaussSumInt b,
    gaussSum_ringHomComp, hχ, hψ]

/-- Index-parametrized field-level covariance for an arbitrary
`phiPrimeGenDescent S c`. The `K`-side action is indexed by `a`, while the
resulting Gauss sum index is the arbitrary `b` supplied by the
residue-character covariance. -/
theorem phiPrimeGenDescent_conjugate_covariance_of_ringHom_index
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    (S : FullTeichDworkSetup ℓ p k K R')
    {c : ℕ} (hc₁ : 1 ≤ c) (hc₂ : c ≤ p - 1)
    (h_ne_zero : S.gaussSumInt c ^ p ≠ 0)
    (a : CyclotomicUnitDelta p) (b : ℕ)
    (τ : R' →+* R')
    (hτ_K : ∀ x : 𝓞 K,
      τ (algebraMap (𝓞 R') R' (algebraMap (𝓞 K) (𝓞 R') x)) =
        algebraMap (𝓞 R') R'
          (algebraMap (𝓞 K) (𝓞 R')
            (cyclotomicRingOfIntegersEquiv (p := p) K a x)))
    (hτχ : (S.residueChar ^ c).ringHomComp τ = S.residueChar ^ b)
    (hτψ : τ.toMonoidHom.compAddChar S.psi = S.psi) :
    algebraMap (𝓞 K) (𝓞 R')
      (cyclotomicRingOfIntegersEquiv (p := p) K a
        (phiPrimeGenDescent S hc₁ hc₂ h_ne_zero)) =
      S.gaussSumInt b ^ p := by
  classical
  set γ := phiPrimeGenDescent S hc₁ hc₂ h_ne_zero with hγ_def
  apply NumberField.RingOfIntegers.coe_injective (K := R')
  rw [← hτ_K γ]
  rw [hγ_def, algebraMap_phiPrimeGenDescent S hc₁ hc₂ h_ne_zero]
  have h_gauss :
      τ (algebraMap (𝓞 R') R' (S.gaussSumInt c)) =
        algebraMap (𝓞 R') R' (S.gaussSumInt b) :=
    S.toConcreteStickelbergerSetup
      |>.ringHom_gaussSumInt_eq_of_residueChar_psi τ
        (a := c) (b := b) hτχ hτψ
  rw [map_pow, map_pow, map_pow, h_gauss]

namespace ConductorFlexibleFullTeichDworkSetup

/-- Conductor-flexible analogue of
`phiPrimeGenDescent_conjugate_covariance_of_ringHom_index`.  The source
automorphism is still abstract here; the source-conductor cyclotomic
constructor only has to supply these three covariance hypotheses. -/
theorem phiPrimeGenDescent_conjugate_covariance_of_ringHom_index
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {c : ℕ} (hc₁ : 1 ≤ c) (hc₂ : c ≤ p - 1)
    (h_ne_zero : S.gaussSumInt c ^ p ≠ 0)
    (a : CyclotomicUnitDelta p) (b : ℕ)
    (τ : R' →+* R')
    (hτ_K : ∀ x : 𝓞 K,
      τ (algebraMap (𝓞 R') R' (algebraMap (𝓞 K) (𝓞 R') x)) =
        algebraMap (𝓞 R') R'
          (algebraMap (𝓞 K) (𝓞 R')
            (cyclotomicRingOfIntegersEquiv (p := p) K a x)))
    (hτχ : (S.residueChar ^ c).ringHomComp τ = S.residueChar ^ b)
    (hτψ : τ.toMonoidHom.compAddChar S.psi = S.psi) :
    algebraMap (𝓞 K) (𝓞 R')
      (cyclotomicRingOfIntegersEquiv (p := p) K a
        (S.phiPrimeGenDescent h_psi hc₁ hc₂ h_ne_zero)) =
      S.gaussSumInt b ^ p := by
  classical
  set γ := S.phiPrimeGenDescent h_psi hc₁ hc₂ h_ne_zero with hγ_def
  apply NumberField.RingOfIntegers.coe_injective (K := R')
  rw [← hτ_K γ]
  rw [hγ_def, S.algebraMap_phiPrimeGenDescent h_psi hc₁ hc₂ h_ne_zero]
  have h_gauss :
      τ (algebraMap (𝓞 R') R' (S.gaussSumInt c)) =
        algebraMap (𝓞 R') R' (S.gaussSumInt b) :=
    S.concrete.ringHom_gaussSumInt_eq_of_residueChar_psi τ
      (a := c) (b := b) hτχ hτψ
  rw [map_pow, map_pow, map_pow, h_gauss]

/-- Reciprocal-index flexible covariance from root actions.  This is the
abstract source-conductor replacement for the old pair-conductor
`pairSigma` lemma: the later cyclotomic-conductor construction only has to
produce the ring hom and these root actions. -/
theorem phiPrimeGenDescent_sub_one_conjugate_covariance_of_ringHom_root_actions
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0)
    (a : CyclotomicUnitDelta p)
    (τ : R' →+* R')
    (hτ_K : ∀ x : 𝓞 K,
      τ (algebraMap (𝓞 R') R' (algebraMap (𝓞 K) (𝓞 R') x)) =
        algebraMap (𝓞 R') R'
          (algebraMap (𝓞 K) (𝓞 R')
            (cyclotomicRingOfIntegersEquiv (p := p) K a x)))
    (hτζp :
      τ ((S.zeta_p : R'ˣ) : R') =
        ((S.zeta_p : R'ˣ) : R') ^ (a : ZMod p).val)
    (hτζℓ : τ S.zeta_ell = S.zeta_ell) :
    algebraMap (𝓞 K) (𝓞 R')
      (cyclotomicRingOfIntegersEquiv (p := p) K a
        (S.phiPrimeGenDescent h_psi
          (by
            have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
            omega)
          (le_refl (p - 1))
          h_ne_zero)) =
      S.gaussSumInt (p - (a : ZMod p).val) ^ p := by
  apply S.phiPrimeGenDescent_conjugate_covariance_of_ringHom_index h_psi
    (by
      have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
      omega)
    (le_refl (p - 1))
    h_ne_zero a (p - (a : ZMod p).val) τ hτ_K
  · have hbase : S.residueChar.ringHomComp τ = S.residueChar ^ (a : ZMod p).val :=
      S.concrete.residueChar_ringHomComp_eq_pow_of_zeta_p_action τ
        (a : ZMod p).val hτζp
    have hχp : S.residueChar ^ p = 1 := S.concrete.abstractSetup.residueChar_pow_eq_one
    have ha_ne : (a : ZMod p) ≠ 0 := a.isUnit.ne_zero
    have ha_pos : 0 < (a : ZMod p).val := ZMod.val_pos.mpr ha_ne
    have ha_lt : (a : ZMod p).val < p := ZMod.val_lt (a : ZMod p)
    calc
      (S.residueChar ^ (p - 1)).ringHomComp τ
          = (S.residueChar.ringHomComp τ) ^ (p - 1) := by
            rw [MulChar.ringHomComp_pow]
      _ = (S.residueChar ^ (a : ZMod p).val) ^ (p - 1) := by
            rw [hbase]
      _ = S.residueChar ^ ((a : ZMod p).val * (p - 1)) := by
            rw [← pow_mul]
      _ = S.residueChar ^ (p - (a : ZMod p).val) := by
            have hmul :
                (a : ZMod p).val * (p - 1) =
                  p * ((a : ZMod p).val - 1) + (p - (a : ZMod p).val) := by
              have hp_one : 1 ≤ p := (Fact.out : Nat.Prime p).one_le
              have ha_one : 1 ≤ (a : ZMod p).val := Nat.succ_le_of_lt ha_pos
              have ha_le : (a : ZMod p).val ≤ p := Nat.le_of_lt ha_lt
              apply Nat.cast_injective (R := ℤ)
              rw [Nat.cast_mul, Nat.cast_sub hp_one, Nat.cast_one, Nat.cast_add,
                Nat.cast_mul, Nat.cast_sub ha_one, Nat.cast_sub ha_le]
              ring
            rw [hmul, pow_add, pow_mul, hχp, one_pow, one_mul]
  · exact S.toConductorFlexibleTraceFormStickelbergerSetup
      |>.ringHom_compAddChar_eq_self_of_zeta_ell_fixed τ hτζℓ

/-- Reciprocal-index flexible covariance supplied by the source conductor
`ℓ * (#k - 1)`. This is the conductor-flexible replacement for the old
pair-field `cyclotomicPairSigmaOfPAndOne` covariance theorem. -/
theorem phiPrimeGenDescent_sub_one_conjugate_covariance_of_sourceConductorSigma
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {ℓ * (Fintype.card k - 1)} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    (hcop : ℓ.Coprime (Fintype.card k - 1))
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0)
    (a : CyclotomicUnitDelta p) :
    algebraMap (𝓞 K) (𝓞 R')
      (cyclotomicRingOfIntegersEquiv (p := p) K a
        (S.phiPrimeGenDescent h_psi
          (by
            have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
            omega)
          (le_refl (p - 1))
          h_ne_zero)) =
      S.gaussSumInt (p - (a : ZMod p).val) ^ p := by
  have hn_ne : Fintype.card k - 1 ≠ 0 := by
    have hcard : 2 ≤ Fintype.card k := Fintype.one_lt_card
    omega
  letI : NeZero (Fintype.card k - 1) := ⟨hn_ne⟩
  let τ :=
    sourceConductorSigmaOfPAndOne
      (p := p) S.hdiv hcop R' a
  apply S.phiPrimeGenDescent_sub_one_conjugate_covariance_of_ringHom_root_actions
    h_psi h_ne_zero a τ
  · intro x
    exact sourceConductorSigmaOfPAndOne_ringOfIntegers_apply
      (p := p) S.hdiv hcop a x
  · have hζp_pow : (((S.zeta_p : R'ˣ) : R') ^ p) = 1 := by
      rw [← Units.val_pow_eq_pow_val, S.hzeta_p.pow_eq_one, Units.val_one]
    exact sourceConductorSigmaOfPAndOne_apply_p_root
      (p := p) S.hdiv hcop a hζp_pow
  · exact sourceConductorSigmaOfPAndOne_apply_ell_root
      (p := p) S.hdiv hcop a S.hzeta_ell.pow_eq_one

/-- Repeated-exponent version of the flexible Dwork/conjugation bridge.

This is the arbitrary-residue-degree replacement for the old atomic
per-index exponent bridge: the right-hand exponent is the repeated
Stickelberger multiplicity of the actual collapsed prime, not `a.val`.

The remaining arithmetic inputs are deliberately explicit:
* divisibility of the Dwork exact order by the descent ramification index;
* identification of the resulting quotient with the repeated multiplicity of
  the collapsed Frobenius/decomposition orbit. -/
theorem repeatedExactExponentsOnOrbit_flexiblePhiPrimeGenDescent_of_sub_val_conjugates
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {c : ℕ} (hc₁ : 1 ≤ c) (hc₂ : c ≤ p - 1)
    (h_ne_zero : S.gaussSumInt c ^ p ≠ 0)
    (h_conj :
      ∀ a : CyclotomicUnitDelta p,
        algebraMap (𝓞 K) (𝓞 R')
          (cyclotomicRingOfIntegersEquiv (p := p) K a
            (S.phiPrimeGenDescent h_psi hc₁ hc₂ h_ne_zero)) =
          S.gaussSumInt (p - (a : ZMod p).val) ^ p)
    (h_div :
      ∀ a : CyclotomicUnitDelta p,
        S.concrete.descentRamificationIdx ∣
          p * S.stickOrdOrd (p - (a : ZMod p).val))
    (h_num :
      ∀ a : CyclotomicUnitDelta p,
        (p * S.stickOrdOrd (p - (a : ZMod p).val)) /
            S.concrete.descentRamificationIdx =
          S.StickelbergerRepeatedMultiplicity
            (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
              S.concrete.descentPrime)) :
    S.StickelbergerRepeatedExactExponentsOnOrbit
      (S.phiPrimeGenDescent h_psi hc₁ hc₂ h_ne_zero) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  refine S.stickelbergerRepeatedExactExponentsOnOrbit_of_conjugate_descentPrime_emultiplicity ?_
  intro a
  set γ := S.phiPrimeGenDescent h_psi hc₁ hc₂ h_ne_zero with hγ_def
  set b : ℕ := p - (a : ZMod p).val with hb_def
  have ha_ne : (a : ZMod p) ≠ 0 := a.isUnit.ne_zero
  have ha_pos : 0 < (a : ZMod p).val := ZMod.val_pos.mpr ha_ne
  have ha_lt : (a : ZMod p).val < p := ZMod.val_lt (a : ZMod p)
  have hb₁ : 1 ≤ b := by
    rw [hb_def]
    omega
  have hb₂ : b ≤ p - 1 := by
    rw [hb_def]
    omega
  have hσγ_ne :
      cyclotomicRingOfIntegersEquiv (p := p) K a γ ≠ 0 := by
    intro h_zero
    have hγ_ne : γ ≠ 0 := by
      rw [hγ_def]
      exact S.phiPrimeGenDescent_ne_zero h_psi hc₁ hc₂ h_ne_zero
    apply hγ_ne
    have h_back :
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹
            (cyclotomicRingOfIntegersEquiv (p := p) K a γ) = γ := by
      rw [← cyclotomicRingOfIntegersEquiv_mul_apply, inv_mul_cancel,
        cyclotomicRingOfIntegersEquiv_one_apply]
    rw [← h_back, h_zero, map_zero]
  have h_emult :=
    S.descentPrime_emultiplicity_eq_of_dwork_exactOrder
      hb₁ hb₂ hσγ_ne (by simpa [γ, b, hγ_def, hb_def] using h_conj a)
      (by simpa [b, hb_def] using h_div a)
  rw [h_num a] at h_emult
  simpa [γ, hγ_def] using h_emult

/-- Source-conductor covariance plus explicit repeated-multiplicity
arithmetic gives the arbitrary-residue-degree repeated exact exponent
certificate for the reciprocal descended source element. -/
theorem repeatedExactExponentsOnOrbit_phiPrimeGenDescent_sub_one_sourceConductorSigma
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {ℓ * (Fintype.card k - 1)} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    (hcop : ℓ.Coprime (Fintype.card k - 1))
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0)
    (h_div :
      ∀ a : CyclotomicUnitDelta p,
        S.concrete.descentRamificationIdx ∣
          p * S.stickOrdOrd (p - (a : ZMod p).val))
    (h_num :
      ∀ a : CyclotomicUnitDelta p,
        (p * S.stickOrdOrd (p - (a : ZMod p).val)) /
            S.concrete.descentRamificationIdx =
          S.StickelbergerRepeatedMultiplicity
            (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
              S.concrete.descentPrime)) :
    S.StickelbergerRepeatedExactExponentsOnOrbit
      (S.phiPrimeGenDescent h_psi
        (by
          have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
          omega)
        (le_refl (p - 1))
        h_ne_zero) :=
  repeatedExactExponentsOnOrbit_flexiblePhiPrimeGenDescent_of_sub_val_conjugates
    S h_psi
    (by
      have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
      omega)
    (le_refl (p - 1))
    h_ne_zero
    (fun a ↦
      S.phiPrimeGenDescent_sub_one_conjugate_covariance_of_sourceConductorSigma
        h_psi hcop h_ne_zero a)
    h_div h_num

/-- Arbitrary-residue-degree source-conductor repeated exact exponents.

This is the same bridge as
`repeatedExactExponentsOnOrbit_phiPrimeGenDescent_sub_one_sourceConductorSigma`,
but the two Dwork exponent inputs are discharged by the Frobenius-order digit
calculation and the repeated-multiplicity coset enumeration. -/
theorem repeatedExactOnOrbit_phiPrimeGenDescent_sub_one_of_f_eq_orderOf
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {ℓ * (Fintype.card k - 1)} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    (hcop : ℓ.Coprime (Fintype.card k - 1))
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0)
    (hℓp : ℓ.Coprime p)
    (hf : S.f = orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p))
    (he : S.concrete.descentRamificationIdx = ℓ - 1) :
    S.StickelbergerRepeatedExactExponentsOnOrbit
      (S.phiPrimeGenDescent h_psi
        (by
          have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
          omega)
        (le_refl (p - 1))
        h_ne_zero) :=
  S.repeatedExactExponentsOnOrbit_phiPrimeGenDescent_sub_one_sourceConductorSigma
    h_psi hcop h_ne_zero
    (fun a ↦
      S.descentRamificationIdx_dvd_p_mul_stickOrdOrd_sub_val_of_f_eq_orderOf
        hℓp hf he a)
    (fun a ↦
      S.dworkExponent_sub_val_div_descentRamificationIdx_eq_repeatedMultiplicity_of_f_eq_orderOf
        hℓp hf he a)

/-- REF-18 exact conjugate exponents for the flexible reciprocal descended
element `S.phiPrimeGenDescent h_psi (p - 1)`, using the source-conductor
automorphism instead of the old pair-cyclotomic automorphism. -/
theorem exactExponents_phiPrimeGenDescent_sub_one_sourceConductorSigma_split
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsCyclotomicExtension {ℓ * (Fintype.card k - 1)} ℚ R']
    [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    (hcop : ℓ.Coprime (Fintype.card k - 1))
    (hf : S.f = 1)
    (he : S.concrete.descentRamificationIdx = ℓ - 1)
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0) :
    S.StickelbergerExactConjugateExponents
      (S.phiPrimeGenDescent h_psi
        (by
          have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
          omega)
        (le_refl (p - 1))
        h_ne_zero) :=
  StickelbergerExactConjugateExponents_flexiblePhiPrimeGenDescent_of_sub_val_conjugates
    S h_psi
    (by
      have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
      omega)
    (le_refl (p - 1))
    h_ne_zero
    (fun a ↦
      S.phiPrimeGenDescent_sub_one_conjugate_covariance_of_sourceConductorSigma
        h_psi hcop h_ne_zero a)
    (fun a ↦
      S.descentRamificationIdx_dvd_p_mul_stickOrdOrd_sub_val_of_f_eq_one hf he a)
    (fun a ↦
      S.dworkExponent_sub_val_div_descentRamificationIdx_eq_val_of_f_eq_one hf he a)

end ConductorFlexibleFullTeichDworkSetup

end Furtwaengler

end BernoulliRegular

end

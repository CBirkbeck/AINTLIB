module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CrossRingBridge.PhiCovariance

/-!
# Index-one covariance and cross-ring residue bridges

This file specializes the covariance of `phiPrimeGenDescent` to the indices `1` and `p - 1`.
It constructs the covariance from ring homomorphisms, root actions, and the cyclotomic pair
automorphism, then packages the reciprocal case as exact Stickelberger conjugate exponents.

The second half supplies the residue-ring interfaces used downstream: reduction of descended
generators and Gauss sums, the K2-1 identities, the embedded canonical primitive root,
the cross-ring K2-2c identity, and compatibility of the setup's chosen root with the canonical
cyclotomic root.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

/-- Index-parametrized field-level covariance for `phiPrimeGenDescent S 1`.
The `K`-side action is indexed by `a`, while the resulting Gauss sum index
is the arbitrary `b` supplied by the residue-character covariance. -/
theorem phiPrimeGenDescent_one_conjugate_covariance_of_ringHom_index
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    (S : FullTeichDworkSetup ℓ p k K R')
    (h_ne_zero : S.gaussSumInt 1 ^ p ≠ 0)
    (a : CyclotomicUnitDelta p) (b : ℕ)
    (τ : R' →+* R')
    (hτ_K : ∀ x : 𝓞 K,
      τ (algebraMap (𝓞 R') R' (algebraMap (𝓞 K) (𝓞 R') x)) =
        algebraMap (𝓞 R') R'
          (algebraMap (𝓞 K) (𝓞 R')
            (cyclotomicRingOfIntegersEquiv (p := p) K a x)))
    (hτχ : S.residueChar.ringHomComp τ = S.residueChar ^ b)
    (hτψ : τ.toMonoidHom.compAddChar S.psi = S.psi) :
    algebraMap (𝓞 K) (𝓞 R')
      (cyclotomicRingOfIntegersEquiv (p := p) K a
        (phiPrimeGenDescent S
          (le_refl 1)
          (Nat.le_sub_one_of_lt ((Fact.out : Nat.Prime p).one_lt))
          h_ne_zero)) =
      S.gaussSumInt b ^ p :=
  phiPrimeGenDescent_conjugate_covariance_of_ringHom_index
    S (le_refl 1) (Nat.le_sub_one_of_lt ((Fact.out : Nat.Prime p).one_lt))
      h_ne_zero a b τ hτ_K (by simpa using hτχ) hτψ

/-- A field-level automorphism extending the cyclotomic action on `K` and
sending the residue character/additive character to the right conjugate
proves exactly the covariance hypothesis required by
`StickelbergerExactConjugateExponents_phiPrimeGenDescent_one_of_sub_val_conjugates`.
-/
theorem phiPrimeGenDescent_one_conjugate_covariance_of_ringHom
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    (S : FullTeichDworkSetup ℓ p k K R')
    (h_ne_zero : S.gaussSumInt 1 ^ p ≠ 0)
    (a : CyclotomicUnitDelta p)
    (τ : R' →+* R')
    (hτ_K : ∀ x : 𝓞 K,
      τ (algebraMap (𝓞 R') R' (algebraMap (𝓞 K) (𝓞 R') x)) =
        algebraMap (𝓞 R') R'
          (algebraMap (𝓞 K) (𝓞 R')
            (cyclotomicRingOfIntegersEquiv (p := p) K a x)))
    (hτχ : S.residueChar.ringHomComp τ =
      S.residueChar ^ (p - (a : ZMod p).val))
    (hτψ : τ.toMonoidHom.compAddChar S.psi = S.psi) :
    algebraMap (𝓞 K) (𝓞 R')
      (cyclotomicRingOfIntegersEquiv (p := p) K a
        (phiPrimeGenDescent S
          (le_refl 1)
          (Nat.le_sub_one_of_lt ((Fact.out : Nat.Prime p).one_lt))
          h_ne_zero)) =
      S.gaussSumInt (p - (a : ZMod p).val) ^ p :=
  phiPrimeGenDescent_one_conjugate_covariance_of_ringHom_index
    S h_ne_zero a (p - (a : ZMod p).val) τ hτ_K hτχ hτψ

/-- Forall form of `phiPrimeGenDescent_one_conjugate_covariance_of_ringHom`,
matching the covariance input of the split exact-exponent composer. -/
theorem phiPrimeGenDescent_one_conjugate_covariance_of_ringHom_family
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    (S : FullTeichDworkSetup ℓ p k K R')
    (h_ne_zero : S.gaussSumInt 1 ^ p ≠ 0)
    (τ : CyclotomicUnitDelta p → R' →+* R')
    (hτ_K : ∀ a : CyclotomicUnitDelta p, ∀ x : 𝓞 K,
      τ a (algebraMap (𝓞 R') R' (algebraMap (𝓞 K) (𝓞 R') x)) =
        algebraMap (𝓞 R') R'
          (algebraMap (𝓞 K) (𝓞 R')
            (cyclotomicRingOfIntegersEquiv (p := p) K a x)))
    (hτχ : ∀ a : CyclotomicUnitDelta p,
      S.residueChar.ringHomComp (τ a) =
        S.residueChar ^ (p - (a : ZMod p).val))
    (hτψ : ∀ a : CyclotomicUnitDelta p,
      (τ a).toMonoidHom.compAddChar S.psi = S.psi) :
    ∀ a : CyclotomicUnitDelta p,
      algebraMap (𝓞 K) (𝓞 R')
        (cyclotomicRingOfIntegersEquiv (p := p) K a
          (phiPrimeGenDescent S
            (le_refl 1)
            (Nat.le_sub_one_of_lt ((Fact.out : Nat.Prime p).one_lt))
            h_ne_zero)) =
        S.gaussSumInt (p - (a : ZMod p).val) ^ p := fun a ↦
  phiPrimeGenDescent_one_conjugate_covariance_of_ringHom
    S h_ne_zero a (τ a) (hτ_K a) (hτχ a) (hτψ a)

/-- Root-action form of `phiPrimeGenDescent_one_conjugate_covariance_of_ringHom`.
The residue-character and additive-character covariance hypotheses are
derived from the actions on the selected roots `ζ_p` and `ζ_ℓ`. -/
theorem phiPrimeGenDescent_one_conjugate_covariance_of_ringHom_root_actions
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    (S : FullTeichDworkSetup ℓ p k K R')
    (h_ne_zero : S.gaussSumInt 1 ^ p ≠ 0)
    (a : CyclotomicUnitDelta p)
    (τ : R' →+* R')
    (hτ_K : ∀ x : 𝓞 K,
      τ (algebraMap (𝓞 R') R' (algebraMap (𝓞 K) (𝓞 R') x)) =
        algebraMap (𝓞 R') R'
          (algebraMap (𝓞 K) (𝓞 R')
            (cyclotomicRingOfIntegersEquiv (p := p) K a x)))
    (hτζp : τ ((S.zeta_p : R'ˣ) : R') =
      ((S.zeta_p : R'ˣ) : R') ^ (p - (a : ZMod p).val))
    (hτζℓ : τ S.zeta_ell = S.zeta_ell) :
    algebraMap (𝓞 K) (𝓞 R')
      (cyclotomicRingOfIntegersEquiv (p := p) K a
        (phiPrimeGenDescent S
          (le_refl 1)
          (Nat.le_sub_one_of_lt ((Fact.out : Nat.Prime p).one_lt))
          h_ne_zero)) =
      S.gaussSumInt (p - (a : ZMod p).val) ^ p :=
  phiPrimeGenDescent_one_conjugate_covariance_of_ringHom
    S h_ne_zero a τ hτ_K
    (S.toConcreteStickelbergerSetup
      |>.residueChar_ringHomComp_eq_pow_of_zeta_p_action τ
        (p - (a : ZMod p).val) hτζp)
    (S.toTraceFormStickelbergerSetup
      |>.ringHom_compAddChar_eq_self_of_zeta_ell_fixed τ hτζℓ)

/-- Forall form of the root-action covariance bridge. -/
theorem phiPrimeGenDescent_one_conjugate_covariance_of_ringHom_root_actions_family
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    (S : FullTeichDworkSetup ℓ p k K R')
    (h_ne_zero : S.gaussSumInt 1 ^ p ≠ 0)
    (τ : CyclotomicUnitDelta p → R' →+* R')
    (hτ_K : ∀ a : CyclotomicUnitDelta p, ∀ x : 𝓞 K,
      τ a (algebraMap (𝓞 R') R' (algebraMap (𝓞 K) (𝓞 R') x)) =
        algebraMap (𝓞 R') R'
          (algebraMap (𝓞 K) (𝓞 R')
            (cyclotomicRingOfIntegersEquiv (p := p) K a x)))
    (hτζp : ∀ a : CyclotomicUnitDelta p,
      τ a ((S.zeta_p : R'ˣ) : R') =
        ((S.zeta_p : R'ˣ) : R') ^ (p - (a : ZMod p).val))
    (hτζℓ : ∀ a : CyclotomicUnitDelta p, τ a S.zeta_ell = S.zeta_ell) :
    ∀ a : CyclotomicUnitDelta p,
      algebraMap (𝓞 K) (𝓞 R')
        (cyclotomicRingOfIntegersEquiv (p := p) K a
          (phiPrimeGenDescent S
            (le_refl 1)
            (Nat.le_sub_one_of_lt ((Fact.out : Nat.Prime p).one_lt))
            h_ne_zero)) =
        S.gaussSumInt (p - (a : ZMod p).val) ^ p := fun a ↦
  phiPrimeGenDescent_one_conjugate_covariance_of_ringHom_root_actions
    S h_ne_zero a (τ a) (hτ_K a) (hτζp a) (hτζℓ a)

/-- Concrete covariance supplied by the CRT cyclotomic automorphism with
`p`-component `a` and trivial `ℓ`-component. This proves the descended
`phiPrimeGenDescent S 1` is carried to the `a.val` Gauss-sum index by the
honest pair-field Galois automorphism. -/
theorem phiPrimeGenDescent_one_conjugate_covariance_of_pairSigma
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    (S : FullTeichDworkSetup ℓ p k K R')
    (h_ne_zero : S.gaussSumInt 1 ^ p ≠ 0)
    (a : CyclotomicUnitDelta p) :
    algebraMap (𝓞 K) (𝓞 R')
      (cyclotomicRingOfIntegersEquiv (p := p) K a
        (phiPrimeGenDescent S
          (le_refl 1)
          (Nat.le_sub_one_of_lt ((Fact.out : Nat.Prime p).one_lt))
          h_ne_zero)) =
      S.gaussSumInt (a : ZMod p).val ^ p := by
  let τ := cyclotomicPairSigmaOfPAndOneFromPair (p := p) S.hℓ_ne_p R' a
  apply phiPrimeGenDescent_one_conjugate_covariance_of_ringHom_index
    S h_ne_zero a (a : ZMod p).val τ
  · intro x
    exact cyclotomicPairSigmaOfPAndOneFromPair_ringOfIntegers_apply
      (p := p) S.hℓ_ne_p a x
  · have hζp_pow : ((S.zeta_p : R'ˣ) : R') ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, S.hzeta_p.pow_eq_one, Units.val_one]
    have hτζp :
        τ ((S.zeta_p : R'ˣ) : R') =
          ((S.zeta_p : R'ˣ) : R') ^ (a : ZMod p).val :=
      cyclotomicPairSigmaOfPAndOneFromPair_apply_p_root
        (p := p) S.hℓ_ne_p a hζp_pow
    exact S.toConcreteStickelbergerSetup
      |>.residueChar_ringHomComp_eq_pow_of_zeta_p_action τ
        (a : ZMod p).val hτζp
  · have hτζℓ : τ S.zeta_ell = S.zeta_ell :=
      cyclotomicPairSigmaOfPAndOneFromPair_apply_ell_root
        (p := p) S.hℓ_ne_p a S.hzeta_ell.pow_eq_one
    exact S.toTraceFormStickelbergerSetup
      |>.ringHom_compAddChar_eq_self_of_zeta_ell_fixed τ hτζℓ

/-- Concrete reciprocal covariance supplied by the CRT cyclotomic automorphism
with `p`-component `a` and trivial `ℓ`-component. Since the starting Gauss sum
has ordinary index `p - 1`, the same honest pair-field automorphism carries
it to the reciprocal index `p - a.val`. -/
theorem phiPrimeGenDescent_sub_one_conjugate_covariance_of_pairSigma
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    (S : FullTeichDworkSetup ℓ p k K R')
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0)
    (a : CyclotomicUnitDelta p) :
    algebraMap (𝓞 K) (𝓞 R')
      (cyclotomicRingOfIntegersEquiv (p := p) K a
        (phiPrimeGenDescent S
          (Nat.le_sub_one_of_lt ((Fact.out : Nat.Prime p).one_lt))
          (le_refl (p - 1))
          h_ne_zero)) =
      S.gaussSumInt (p - (a : ZMod p).val) ^ p := by
  let τ := cyclotomicPairSigmaOfPAndOneFromPair (p := p) S.hℓ_ne_p R' a
  apply phiPrimeGenDescent_conjugate_covariance_of_ringHom_index
    S
    (Nat.le_sub_one_of_lt ((Fact.out : Nat.Prime p).one_lt))
    (le_refl (p - 1))
    h_ne_zero a (p - (a : ZMod p).val) τ
  · intro x
    exact cyclotomicPairSigmaOfPAndOneFromPair_ringOfIntegers_apply
      (p := p) S.hℓ_ne_p a x
  · have hζp_pow : ((S.zeta_p : R'ˣ) : R') ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, S.hzeta_p.pow_eq_one, Units.val_one]
    have hτζp :
        τ ((S.zeta_p : R'ˣ) : R') =
          ((S.zeta_p : R'ˣ) : R') ^ (a : ZMod p).val :=
      cyclotomicPairSigmaOfPAndOneFromPair_apply_p_root
        (p := p) S.hℓ_ne_p a hζp_pow
    have hbase : S.residueChar.ringHomComp τ = S.residueChar ^ (a : ZMod p).val :=
      S.toConcreteStickelbergerSetup
        |>.residueChar_ringHomComp_eq_pow_of_zeta_p_action τ
          (a : ZMod p).val hτζp
    have hχp : S.residueChar ^ p = 1 :=
      S.toConcreteStickelbergerSetup.residueChar_pow_eq_one
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
  · have hτζℓ : τ S.zeta_ell = S.zeta_ell :=
      cyclotomicPairSigmaOfPAndOneFromPair_apply_ell_root
        (p := p) S.hℓ_ne_p a S.hzeta_ell.pow_eq_one
    exact S.toTraceFormStickelbergerSetup
      |>.ringHom_compAddChar_eq_self_of_zeta_ell_fixed τ hτζℓ

/-- REF-18 exact conjugate exponents for the reciprocal descended element
`phiPrimeGenDescent S (p - 1)` in the split, unramified-base case. The honest pair-field
automorphism sends the `(p - 1)`-indexed Gauss sum to the reciprocal index `p - a.val`, whose
Dwork order normalizes to `a.val`. -/
theorem StickelbergerExactConjugateExponents_phiPrimeGenDescent_sub_one_of_pairSigma_split
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] [IsScalarTower ℤ (𝓞 K) (𝓞 R')]
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : FullTeichDworkSetup ℓ p k K R')
    (hf : S.f = 1)
    (he : (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).ramificationIdxIn
        (𝓞 K) = 1)
    (h_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0) :
    S.StickelbergerExactConjugateExponents
      (phiPrimeGenDescent S
        (Nat.le_sub_one_of_lt ((Fact.out : Nat.Prime p).one_lt))
        (le_refl (p - 1))
        h_ne_zero) :=
  StickelbergerExactConjugateExponents_phiPrimeGenDescent_of_sub_val_conjugates
    S
    (Nat.le_sub_one_of_lt ((Fact.out : Nat.Prime p).one_lt))
    (le_refl (p - 1))
    h_ne_zero
    (fun a ↦ phiPrimeGenDescent_sub_one_conjugate_covariance_of_pairSigma S h_ne_zero a)
    (fun a ↦
      descentRamificationIdx_dvd_p_mul_stickOrdOrd_sub_val_of_f_eq_one_of_unramified_base
        S hf he a)
    (fun a ↦
      dworkExponent_sub_val_div_descentRamificationIdx_eq_val_of_f_eq_one_of_unramified_base
        S hf he a)

/-- **Embedding sends `phiPrimeGenDescent` to `gaussSumInt^p` mod `𝔭`**. -/
theorem residueFieldEmbedding_phiPrimeGenDescent
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 R')}
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P') :
    residueFieldEmbedding h_over
      ((Ideal.Quotient.mk P' (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero)) :
        𝓞 K ⧸ P') =
      ((Ideal.Quotient.mk 𝔭 (S.gaussSumInt a ^ p)) : 𝓞 R' ⧸ 𝔭) := by
  rw [residueFieldEmbedding_mk h_over, algebraMap_phiPrimeGenDescent]

/-- **gaussSumInt reduced mod 𝔭 is a Gauss sum** of post-composed
characters in `𝓞 R' / 𝔭`. -/
theorem ideal_quotient_mk_gaussSumInt
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    (a : ℕ)
    (𝔭 : Ideal (𝓞 R')) :
    Ideal.Quotient.mk 𝔭 (S.gaussSumInt a) =
      gaussSum
        ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar
          S.psiInt) := by
  simp only [ConcreteStickelbergerSetup.gaussSumInt]
  exact gaussSum_ringHomComp _ _ (Ideal.Quotient.mk 𝔭)

/-- **K2-1 in cross-ring `𝓞 R' / 𝔭`**: for `gaussSumInt a` reduced mod
the prime `𝔭 ⊂ 𝓞 R'` (with `𝓞 R' / 𝔭` of `CharP ℓ_P'` and the right
unit witness), the K2-1 cancellation form holds. -/
theorem ideal_quotient_mk_gaussSumInt_pow_pow_div_apply_smul_eq_one
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    (a : ℕ)
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hp : 1 < p)
    (h_χp_eq_one :
      (S.residueCharInt ^ a).ringHomComp
        (Ideal.Quotient.mk 𝔭) ^ p = 1)
    {f : ℕ} (hf : 1 ≤ ℓ' ^ f) (hN_mod_p : (ℓ' ^ f) % p = 1)
    (unit_a : kˣ) (h_unit : (unit_a : k) = (ℓ' ^ f : ℕ))
    (hg_ne :
      gaussSum
        ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar
          S.psiInt) ≠ 0) :
    ((S.residueCharInt ^ a).ringHomComp
        (Ideal.Quotient.mk 𝔭)) unit_a *
        (((Ideal.Quotient.mk 𝔭) (S.gaussSumInt a)) ^ p) ^ ((ℓ' ^ f - 1) / p) = 1 := by
  rw [ideal_quotient_mk_gaussSumInt]
  exact gaussSum_pow_p_pow_div_apply_smul_eq_one_of_charP_field hp _ h_χp_eq_one _
    hf hN_mod_p unit_a h_unit hg_ne

/-- **K2-1 direct Frobenius congruence in `𝓞 R' / 𝔭`**: for
`gaussSumInt a` reduced modulo `𝔭`, the raw Frobenius identity gives

```
χ(unit_N) * g^(ℓ' ^ f) = g.
```

This is the direct, non-cancelled form of K2-1; unlike the
`pow_pow_div_apply_smul_eq_one` form, it does not require nonvanishing of
the reduced Gauss sum. -/
theorem ideal_quotient_mk_gaussSumInt_pow_apply_smul_eq_self
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    (a : ℕ)
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hp : 1 < p)
    (h_χp_eq_one :
      (S.residueCharInt ^ a).ringHomComp
        (Ideal.Quotient.mk 𝔭) ^ p = 1)
    {f : ℕ} (hN_mod_p : (ℓ' ^ f) % p = 1)
    (unit_N : kˣ) (h_unit_N : (unit_N : k) = (ℓ' ^ f : ℕ)) :
    ((S.residueCharInt ^ a).ringHomComp
        (Ideal.Quotient.mk 𝔭)) unit_N *
        ((Ideal.Quotient.mk 𝔭) (S.gaussSumInt a)) ^ (ℓ' ^ f) =
      (Ideal.Quotient.mk 𝔭) (S.gaussSumInt a) := by
  rw [ideal_quotient_mk_gaussSumInt]
  exact gaussSum_pow_eq_inv_apply_smul_of_charP hp _ h_χp_eq_one _
    f hN_mod_p unit_N h_unit_N

/-- **residueMulChar after ringHomComp through quotient**: applying the
character to a quotient class. -/
theorem residueMulChar_ringHomComp_apply_quotient
    {p : ℕ} [NeZero p]
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R']
    {R'' : Type*} [CommRing R'']
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    (σ : R' →+* R'') (a : kˣ) :
    ((residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R).ringHomComp σ) (a : k) =
      σ ((residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) (a : k)) :=
  rfl

/-- **Embedded canonical zeta in `𝓞 R' / 𝔭`**: the image of
`canonicalResidueZetaP P'` under the residue field embedding (as an
element of `(𝓞 R' / 𝔭)ˣ`). -/
def canonicalResidueZetaP_image
    {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R']
    [Algebra K R'] [IsScalarTower ℚ K R']
    {P' : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 R')}
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P') : (𝓞 R' ⧸ 𝔭)ˣ :=
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hu : IsUnit ((residueFieldEmbedding h_over)
      (canonicalResidueZetaP (p := p) (K := K) P' : 𝓞 K ⧸ P')) :=
    (canonicalResidueZetaP (p := p) (K := K) P').isUnit.map (residueFieldEmbedding h_over)
  hu.unit

@[simp] theorem canonicalResidueZetaP_image_val
    {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R']
    [Algebra K R'] [IsScalarTower ℚ K R']
    {P' : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 R')}
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P') :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ((canonicalResidueZetaP_image (p := p) (K := K) (R' := R')
      h_over) : 𝓞 R' ⧸ 𝔭) =
      (residueFieldEmbedding h_over)
        (canonicalResidueZetaP (p := p) (K := K) P' : 𝓞 K ⧸ P') :=
  rfl

/-- **`canonicalResidueZetaP_image` underlying value is a primitive `p`-th
root in `𝓞 R' / 𝔭`**: stated at the ring-element level (not unit form). -/
theorem canonicalResidueZetaP_image_val_isPrimitiveRoot
    {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R']
    [Algebra K R'] [IsScalarTower ℚ K R']
    {P' : Ideal (𝓞 K)} (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P') :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    IsPrimitiveRoot
      ((canonicalResidueZetaP_image (p := p) (K := K) (R' := R')
        h_over) : 𝓞 R' ⧸ 𝔭) p := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [canonicalResidueZetaP_image_val h_over]
  have h_ring_prim :
      IsPrimitiveRoot (((canonicalResidueZetaP (p := p) (K := K) P') :
          𝓞 K ⧸ P')) p := by
    have := hP'_max.isPrime
    have : NeZero P' := ⟨hP'_bot⟩
    have : Field (𝓞 K ⧸ P') := Ideal.Quotient.field P'
    exact (canonicalResidueZetaP_isPrimitiveRoot hP'_bot hp_in_P').map_of_injective
      (Units.coeHom_injective)
  exact h_ring_prim.map_of_injective
    (residueFieldEmbedding_injective h_over)

/-- **K2-2c cross-ring**: residueMulChar after ringHomComp at α mod P
equals the image of zeta_R raised to the canonical residue exponent. -/
theorem residueMulChar_ringHomComp_apply_quotient_canonical_eq_pow_pthSymbol
    {p : ℕ} [Fact p.Prime] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [CommRing R']
    {R'' : Type*} [CommRing R'']
    (P : Ideal (𝓞 K)) (hbot : P ≠ ⊥) [hmax : P.IsMaximal]
    (hdiv : p ∣ Fintype.card (𝓞 K ⧸ P) - 1)
    (hp_in : (p : 𝓞 K) ∉ P)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    (σ : R' →+* R'')
    {α : 𝓞 K} (hα : α ∉ P) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    ((residueMulChar (canonicalResidueZetaP (p := p) (K := K) P)
        (canonicalResidueZetaP_isPrimitiveRoot hbot hp_in)
        hdiv zeta_R hzeta_R).ringHomComp σ)
        ((Ideal.Quotient.mk P α : 𝓞 K ⧸ P)) =
      σ ((zeta_R : R')) ^
        (BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) α P).val := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  rw [MulChar.ringHomComp_apply,
    residueMulChar_apply_quotient_canonical_eq_pow_pthSymbol
      P hbot hdiv hp_in zeta_R hzeta_R hα,
    map_pow]

/-- **Setup-zeta compatibility predicate**: in the residue ring `𝓞 R' / 𝔭`,
the setup's `zeta_p_int` reduces to the same element as the canonical
zeta from `K`. -/
def SetupZetaCompatible
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {𝔭 : Ideal (𝓞 R')} : Prop :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  Ideal.Quotient.mk 𝔭 S.zeta_p_int =
    Ideal.Quotient.mk 𝔭
      (algebraMap (𝓞 K) (𝓞 R')
        (BernoulliRegular.cyclotomicZetaInteger (p := p) K))

/-- **Setup-zeta compatibility from equality of integral lifts**: if the
setup's integral `p`-th root is literally the image of the canonical
cyclotomic integer from `K`, then `SetupZetaCompatible` holds at every
prime of `𝓞 R'`. -/
theorem setupZetaCompatible_of_zeta_p_int_eq
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {𝔭 : Ideal (𝓞 R')}
    (h_zeta_p_int_eq :
      S.zeta_p_int =
        (algebraMap (𝓞 K) (𝓞 R'))
          (BernoulliRegular.cyclotomicZetaInteger (p := p) K)) :
    SetupZetaCompatible S (𝔭 := 𝔭) := by
  exact congrArg (Ideal.Quotient.mk 𝔭) h_zeta_p_int_eq

/-- **Identification under setup-zeta compatibility**: under
`SetupZetaCompatible`, the setup's `zeta_p_int` reduced mod `𝔭` equals
the underlying value of `canonicalResidueZetaP_image`. -/
theorem ideal_quotient_mk_zeta_p_int_eq_canonicalResidueZetaP_image
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {P' : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 R')}
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : SetupZetaCompatible S (𝔭 := 𝔭)) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    Ideal.Quotient.mk 𝔭 S.zeta_p_int =
      ((canonicalResidueZetaP_image (p := p) (K := K) (R' := R')
        h_over) : 𝓞 R' ⧸ 𝔭) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [h_compat, canonicalResidueZetaP_image_val h_over,
      canonicalResidueZetaP_val P', residueFieldEmbedding_mk h_over]

/-- The residue-field embedding preserves natural powers. -/
theorem residueFieldEmbedding_pow
    {K : Type*} [Field K] [NumberField K]
    {R' : Type*} [Field R'] [NumberField R']
    [Algebra K R'] [IsScalarTower ℚ K R']
    {P : Ideal (𝓞 K)} {𝔭 : Ideal (𝓞 R')}
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P)
    (x : 𝓞 K ⧸ P) (n : ℕ) :
    residueFieldEmbedding h_over (x ^ n) =
      (residueFieldEmbedding h_over x) ^ n :=
  map_pow _ x n

end Furtwaengler

end BernoulliRegular

end

end

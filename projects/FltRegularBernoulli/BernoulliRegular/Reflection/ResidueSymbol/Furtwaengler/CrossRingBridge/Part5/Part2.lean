module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CrossRingBridge.Part5.Part1

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

theorem ConductorFlexibleFullTeichDworkSetup.descent_atom_unit_of_cross_ring
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    [hP'_max : P'.IsMaximal]
    (hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1)
    (h_phi_notin_P' : S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : ConductorFlexibleSetupZetaCompatible S (𝔭 := 𝔭))
    (t : ZMod p)
    (h_cross_ring :
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((Ideal.Quotient.mk 𝔭 (S.gaussSumInt a)) ^ p :
          𝓞 R' ⧸ 𝔭) ^ ((Fintype.card (𝓞 K ⧸ P') - 1) / p) =
        ((Ideal.Quotient.mk 𝔭
            (S.zeta_p_int)) :
          𝓞 R' ⧸ 𝔭) ^ t.val) :
    letI : Field (𝓞 K ⧸ P') := Ideal.Quotient.field P'
    Reflection.ResidueSymbol.PowerResidue.finiteFieldUnit hdiv_P'
        (Reflection.ResidueSymbol.PowerResidue.quotientUnitOfNotMem
          P' (S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero) h_phi_notin_P') =
      canonicalResidueZetaP (p := p) (K := K) P' ^ t.val := by
  letI : Field (𝓞 K ⧸ P') := Ideal.Quotient.field P'
  apply Units.ext
  change ((Ideal.Quotient.mk P' (S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero) :
      𝓞 K ⧸ P')) ^ ((Fintype.card (𝓞 K ⧸ P') - 1) / p) =
    ((canonicalResidueZetaP (p := p) (K := K) P' : 𝓞 K ⧸ P')) ^ t.val
  exact S.descent_atom_of_cross_ring h_psi ha₁ ha₂ h_ne_zero h_over h_compat
    t h_cross_ring

/-- Flexible per-index K2-2 symbol identity from the cross-ring hypotheses. -/
theorem ConductorFlexibleFullTeichDworkSetup.K2_2_path_a_pthSymbol
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1)
    (h_phi_notin_P' : S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : ConductorFlexibleSetupZetaCompatible S (𝔭 := 𝔭))
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hp : 1 < p)
    (h_χp_eq_one :
      (S.residueCharInt ^ a).ringHomComp
        (Ideal.Quotient.mk 𝔭) ^ p = 1)
    {f : ℕ} (hf : 1 ≤ ℓ' ^ f)
    (hN_eq : ℓ' ^ f = Fintype.card (𝓞 K ⧸ P'))
    (hN_mod_p : (ℓ' ^ f) % p = 1)
    (unit_a : kˣ) (h_unit : (unit_a : k) = (ℓ' ^ f : ℕ))
    (hg_ne :
      gaussSum
        ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar
          S.psiInt) ≠ 0)
    (t : ZMod p)
    (h_χ_value :
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭)) unit_a *
        ((Ideal.Quotient.mk 𝔭
            (S.zeta_p_int)) :
          𝓞 R' ⧸ 𝔭) ^ t.val = 1) :
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero) P' = t := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h_cross_ring := S.cross_ring_identity_from_K2_1_K2_2c
    a hp h_χp_eq_one hf hN_eq hN_mod_p unit_a h_unit hg_ne t h_χ_value
  have h_descent := S.descent_atom_unit_of_cross_ring
    h_psi ha₁ ha₂ h_ne_zero hdiv_P' h_phi_notin_P' h_over h_compat t h_cross_ring
  exact pthSymbolAtPrime_canonical_eq_of_descent_pow_eq
    hP'_bot hp_in_P' hdiv_P' (S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero)
    h_phi_notin_P' t h_descent

/-- Flexible per-index K2-2 symbol identity in single-power character form. -/
theorem ConductorFlexibleFullTeichDworkSetup.K2_2_path_a_pthSymbol_of_single_power
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1)
    (h_phi_notin_P' : S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : ConductorFlexibleSetupZetaCompatible S (𝔭 := 𝔭))
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hp : 1 < p)
    (h_χp_eq_one :
      (S.residueCharInt ^ a).ringHomComp
        (Ideal.Quotient.mk 𝔭) ^ p = 1)
    {f : ℕ} (hf : 1 ≤ ℓ' ^ f)
    (hN_eq : ℓ' ^ f = Fintype.card (𝓞 K ⧸ P'))
    (hN_mod_p : (ℓ' ^ f) % p = 1)
    (unit_a : kˣ) (h_unit : (unit_a : k) = (ℓ' ^ f : ℕ))
    (hg_ne :
      gaussSum
        ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar
          S.psiInt) ≠ 0)
    (h_zeta_pow_p :
      ((Ideal.Quotient.mk 𝔭
        (S.zeta_p_int)) :
          𝓞 R' ⧸ 𝔭) ^ p = 1)
    (s' : ZMod p)
    (h_χ_eval :
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭)) unit_a =
        ((Ideal.Quotient.mk 𝔭
            (S.zeta_p_int)) :
          𝓞 R' ⧸ 𝔭) ^ s'.val) :
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero) P' =
      -s' := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h_χ_value := h_chi_value_of_single_power (s := s') h_χ_eval h_zeta_pow_p
  exact S.K2_2_path_a_pthSymbol h_psi ha₁ ha₂ h_ne_zero hP'_bot hp_in_P'
    hdiv_P' h_phi_notin_P' h_over h_compat hp h_χp_eq_one hf hN_eq hN_mod_p
    unit_a h_unit hg_ne (-s') h_χ_value

/-- Flexible per-index K2-2 symbol identity in K2-2c-with-pow form. -/
theorem ConductorFlexibleFullTeichDworkSetup.K2_2_path_a_pthSymbol_of_K2_2c_pow
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1)
    (h_phi_notin_P' : S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : ConductorFlexibleSetupZetaCompatible S (𝔭 := 𝔭))
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hp : 1 < p)
    (h_χp_eq_one :
      (S.residueCharInt ^ a).ringHomComp
        (Ideal.Quotient.mk 𝔭) ^ p = 1)
    {f : ℕ} (hf : 1 ≤ ℓ' ^ f)
    (hN_eq : ℓ' ^ f = Fintype.card (𝓞 K ⧸ P'))
    (hN_mod_p : (ℓ' ^ f) % p = 1)
    (unit_a : kˣ) (h_unit : (unit_a : k) = (ℓ' ^ f : ℕ))
    (hg_ne :
      gaussSum
        ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar
          S.psiInt) ≠ 0)
    (h_zeta_pow_p :
      ((Ideal.Quotient.mk 𝔭
        (S.zeta_p_int)) :
          𝓞 R' ⧸ 𝔭) ^ p = 1)
    (s : ZMod p)
    (h_χ_eval_pow :
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭)) unit_a =
        ((Ideal.Quotient.mk 𝔭
            (S.zeta_p_int)) :
          𝓞 R' ⧸ 𝔭) ^ (a * s.val)) :
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero) P' =
      -((a : ZMod p) * s) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h_χ_eval_single :
      ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭)) unit_a =
        ((Ideal.Quotient.mk 𝔭
            (S.zeta_p_int)) :
          𝓞 R' ⧸ 𝔭) ^ (((a : ZMod p) * s).val) := by
    rw [h_χ_eval_pow, pow_natVal_mul_eq_pow_zmod_mul h_zeta_pow_p s a]
  exact S.K2_2_path_a_pthSymbol_of_single_power h_psi ha₁ ha₂ h_ne_zero
    hP'_bot hp_in_P' hdiv_P' h_phi_notin_P' h_over h_compat hp h_χp_eq_one
    hf hN_eq hN_mod_p unit_a h_unit hg_ne h_zeta_pow_p ((a : ZMod p) * s)
    h_χ_eval_single

/-- Flexible K2-2 path with setup-internal root facts discharged. -/
theorem ConductorFlexibleFullTeichDworkSetup.K2_2_path_a_pthSymbol_of_residueCharInt
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1)
    (h_phi_notin_P' : S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    (h_compat : ConductorFlexibleSetupZetaCompatible S (𝔭 := 𝔭))
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hp : 1 < p)
    {f : ℕ} (hf : 1 ≤ ℓ' ^ f)
    (hN_eq : ℓ' ^ f = Fintype.card (𝓞 K ⧸ P'))
    (hN_mod_p : (ℓ' ^ f) % p = 1)
    (unit_a : kˣ) (h_unit : (unit_a : k) = (ℓ' ^ f : ℕ))
    (hg_ne :
      gaussSum
        ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar
          S.psiInt) ≠ 0)
    (s : ZMod p)
    (h_χ_eval_pow :
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((S.residueCharInt ^ a).ringHomComp
          (Ideal.Quotient.mk 𝔭)) unit_a =
        ((Ideal.Quotient.mk 𝔭
            (S.zeta_p_int)) :
          𝓞 R' ⧸ 𝔭) ^ (a * s.val)) :
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero) P' =
      -((a : ZMod p) * s) :=
  S.K2_2_path_a_pthSymbol_of_K2_2c_pow h_psi ha₁ ha₂ h_ne_zero
    hP'_bot hp_in_P' hdiv_P' h_phi_notin_P' h_over h_compat hp
    (S.residueCharInt_ringHomComp_pow_p_eq_one a 𝔭)
    hf hN_eq hN_mod_p unit_a h_unit hg_ne
    (S.ideal_quotient_mk_zeta_p_int_pow_p_eq_one (𝔭 := 𝔭))
    s h_χ_eval_pow

/-- Caller-facing flexible K2-2 path from canonical source and target root
choices.  This is the flexible analogue of
`K2_2_path_a_pthSymbol_of_canonical_residueCharInt_of_liesOver_ne_char_notMem_of_zeta_choices`,
with the descended generator supplied by `S.phiPrimeGenDescent h_psi`. -/
theorem ConductorFlexibleFullTeichDworkSetup.K2_2_path_a_pthSymbol_of_zeta_choices
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {P : Ideal (𝓞 K)} (hP_bot : P ≠ ⊥) [hP_max : P.IsMaximal]
    [Algebra (ZMod ℓ) (𝓞 K ⧸ P)]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_in_P : (p : 𝓞 K) ∉ P)
    (S : letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R')
    (h_psi :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.concrete.IsGalPsiShiftCompatible)
    (h_zeta_k_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_k = canonicalResidueZetaP (p := p) (K := K) P)
    (h_zeta_p_int_eq :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.zeta_p_int =
        (algebraMap (𝓞 K) (𝓞 R'))
          (BernoulliRegular.cyclotomicZetaInteger (p := p) K))
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.gaussSumInt a ^ p ≠ 0)
    {P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) [hP'_max : P'.IsMaximal]
    (hp_in_P' : (p : 𝓞 K) ∉ P')
    (h_phi_notin_P' :
      letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
      S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero ∉ P')
    {𝔭 : Ideal (𝓞 R')} [𝔭.IsMaximal]
    (h_over : 𝔭.comap (algebraMap (𝓞 K) (𝓞 R')) = P')
    {ℓ' : ℕ} [Fact ℓ'.Prime] [CharP (𝓞 R' ⧸ 𝔭) ℓ']
    (hℓ_ne_ℓ' : ℓ ≠ ℓ') :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero) P' =
      -((a : ZMod p) *
        BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Field (𝓞 K ⧸ P') := Ideal.Quotient.field P'
  have hdiv_P : p ∣ Fintype.card (𝓞 K ⧸ P) - 1 :=
    canonicalResidueZetaP_card_sub_one_dvd
      (p := p) (K := K) (q := P) hP_bot hp_in_P
  have hdiv_P' : p ∣ Fintype.card (𝓞 K ⧸ P') - 1 :=
    canonicalResidueZetaP_card_sub_one_dvd
      (p := p) (K := K) (q := P') hP'_bot hp_in_P'
  have h_residue_char_eq :
      S.residueCharInt =
        residueMulChar (canonicalResidueZetaP (p := p) (K := K) P)
          (canonicalResidueZetaP_isPrimitiveRoot hP_bot hp_in_P)
          hdiv_P S.zeta_p_int_unit S.zeta_p_int_unit_isPrimitiveRoot := by
    simpa [hdiv_P] using
      S.residueCharInt_eq_canonical_of_zeta_k_eq hP_bot hp_in_P h_zeta_k_eq
  haveI : CharP (𝓞 K ⧸ P') ℓ' := charP_baseResidue_of_liesOver h_over
  obtain ⟨f, _hℓ'_prime, hcard⟩ := FiniteField.card (𝓞 K ⧸ P') ℓ'
  have hf : 1 ≤ ℓ' ^ (f : ℕ) := one_le_pow_of_natPrime
  have hN_eq : ℓ' ^ (f : ℕ) = Fintype.card (𝓞 K ⧸ P') := hcard.symm
  have hN_mod_p : (ℓ' ^ (f : ℕ)) % p = 1 :=
    Nat.mod_eq_one_of_dvd_sub_one (Fact.out : Nat.Prime p).one_lt
      (Nat.pow_pos (Fact.out : ℓ'.Prime).pos)
      (by
        rw [hN_eq]
        exact hdiv_P')
  haveI : CharP (𝓞 K ⧸ P) ℓ :=
    charP_quotient_of_natPrime_mem P (Fact.out : ℓ.Prime) hℓ_in_P
  have hℓ'_notin_P : (((ℓ' : ℕ) : 𝓞 K)) ∉ P :=
    natPrime_notMem_of_charP_quotient_ne
      (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ')
      (Fact.out : ℓ'.Prime) hℓ_ne_ℓ'
  have hn_notin_P : (((ℓ' ^ (f : ℕ) : ℕ) : 𝓞 K)) ∉ P := by
    haveI : P.IsPrime := hP_max.isPrime
    exact natCast_pow_notMem_of_natCast_notMem (K := K) (P := P) hℓ'_notin_P
  let unit_a : (𝓞 K ⧸ P)ˣ :=
    unitOfNatCast_notMem (K := K) (P := P) (ℓ' ^ (f : ℕ)) hn_notin_P
  have h_unit :
      (unit_a : 𝓞 K ⧸ P) = ((ℓ' ^ (f : ℕ) : ℕ) : 𝓞 K ⧸ P) :=
    unitOfNatCast_notMem_eq_natCast
      (K := K) (P := P) (ℓ' ^ (f : ℕ)) hn_notin_P
  have h_eval_nat := S.residueCharInt_pow_apply_unitOfNatCast
    hP_bot hp_in_P hdiv_P h_residue_char_eq (𝔭 := 𝔭) ha₁ hn_notin_P
  have hcast :
      (((ℓ' ^ (f : ℕ) : ℕ) : 𝓞 K)) =
        (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) := by
    rw [hN_eq]
    norm_num
  have h_eval :
      ((S.residueCharInt ^ a).ringHomComp (Ideal.Quotient.mk 𝔭)) unit_a =
        ((Ideal.Quotient.mk 𝔭
            S.zeta_p_int) :
          𝓞 R' ⧸ 𝔭) ^
          (a * (BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
            (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P).val) := by
    simpa [unit_a, hcast] using h_eval_nat
  have hg_ne :
      gaussSum
        ((S.residueCharInt ^ a).ringHomComp (Ideal.Quotient.mk 𝔭))
        ((Ideal.Quotient.mk 𝔭).toMonoidHom.compAddChar S.psiInt) ≠ 0 :=
    S.gaussSum_ringHomComp_ne_zero h_psi ha₁ ha₂ h_ne_zero h_phi_notin_P' h_over
  exact S.K2_2_path_a_pthSymbol_of_residueCharInt
    h_psi ha₁ ha₂ h_ne_zero hP'_bot hp_in_P' hdiv_P' h_phi_notin_P'
    h_over
    (conductorFlexibleSetupZetaCompatible_of_zeta_p_int_eq S h_zeta_p_int_eq)
    (Fact.out : Nat.Prime p).one_lt hf hN_eq hN_mod_p unit_a h_unit hg_ne
    (BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
      (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P)
    h_eval

/-! ### Explicit unit factor between two generators of the same span

Given Span(γ₁) = Span(γ₂), the unit factor `u` with `γ₁ = u * γ₂` is
extracted via Classical.choose. -/

/-- **Specific unit factor**: chooses `u` from `exists_unit_eq_of_span_eq`. -/
noncomputable def unitFactorOfSpanEq
    {K : Type*} [Field K] [NumberField K]
    {γ₁ γ₂ : 𝓞 K} (hγ₂_ne : γ₂ ≠ 0)
    (h_span : Ideal.span ({γ₁} : Set (𝓞 K)) = Ideal.span ({γ₂} : Set (𝓞 K))) :
    (𝓞 K)ˣ :=
  (exists_unit_eq_of_span_eq hγ₂_ne h_span).choose

/-- **Specific unit factor satisfies the equation**. -/
theorem unitFactorOfSpanEq_eq
    {K : Type*} [Field K] [NumberField K]
    {γ₁ γ₂ : 𝓞 K} (hγ₂_ne : γ₂ ≠ 0)
    (h_span : Ideal.span ({γ₁} : Set (𝓞 K)) = Ideal.span ({γ₂} : Set (𝓞 K))) :
    γ₁ = ((unitFactorOfSpanEq hγ₂_ne h_span : (𝓞 K)ˣ) : 𝓞 K) * γ₂ :=
  (exists_unit_eq_of_span_eq hγ₂_ne h_span).choose_spec

/-- **Specific unit factor is not in P' if γ₁ is not in P'**: from
`γ₁ = u * γ₂`, `γ₁ ∉ P'` forces both factors not in `P'` (in a maximal
ideal, prime). -/
theorem unitFactorOfSpanEq_notMem
    {K : Type*} [Field K] [NumberField K]
    {P' : Ideal (𝓞 K)} [P'.IsPrime]
    {γ₁ γ₂ : 𝓞 K} (hγ₁_notin : γ₁ ∉ P') (hγ₂_ne : γ₂ ≠ 0)
    (h_span : Ideal.span ({γ₁} : Set (𝓞 K)) = Ideal.span ({γ₂} : Set (𝓞 K))) :
    ((unitFactorOfSpanEq hγ₂_ne h_span : (𝓞 K)ˣ) : 𝓞 K) ∉ P' := by
  intro h_mem
  have h_eq := unitFactorOfSpanEq_eq hγ₂_ne h_span
  rw [h_eq] at hγ₁_notin
  exact hγ₁_notin (Ideal.mul_mem_right γ₂ P' h_mem)

/-! ### Apex via unit factor extraction

Combining `unitFactorOfSpanEq` with
`pthSymbolAtPrime_canonical_h_stick_gen_eq_K_chain_target` gives a
self-contained apex: the K-chain conclusion for h_stick.gen follows
from the K-chain output for phiPrimeGenDescent + the U-chain content
applied to the SPECIFIC extracted unit. -/

/-- **K-chain at h_stick.gen with the explicit unit correction**.  Without
assuming that the extracted unit has trivial symbol, the exact statement has
an additional correction term.  This is the generator-dependence obstruction
for the current `phiPrimeGen` API: a `StickelbergerIdealEquality` supplies
only a generator up to unit, and the p-th residue symbol is not invariant
under arbitrary unit multiples. -/
theorem K_chain_at_h_stick_gen_via_extracted_unit_with_correction
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) (hP'_max : P'.IsMaximal)
    (h_phi_notin_P' : phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ∉ P')
    (h_span : Ideal.span ({phiPrimeGenDescent S ha₁ ha₂ h_ne_zero} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P)
    (h_K_chain :
      BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) P' =
      -((a : ZMod p) *
        BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P))
    (h_stick_gen_notin :
      (StickelbergerIdealEquality.of_phiPrimeGenDescent
        S ha₁ ha₂ h_ne_zero h_span).gen ∉ P') :
    letI h_stick := StickelbergerIdealEquality.of_phiPrimeGenDescent
      S ha₁ ha₂ h_ne_zero h_span
    letI h_phi_ne := phiPrimeGenDescent_ne_zero S ha₁ ha₂ h_ne_zero
    letI h_span_eq : Ideal.span ({h_stick.gen} : Set (𝓞 K)) =
      Ideal.span ({phiPrimeGenDescent S ha₁ ha₂ h_ne_zero} : Set (𝓞 K)) := by
      rw [h_stick.span_gen, ← h_span]
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGen h_stick) P' =
      BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K)
          ((unitFactorOfSpanEq h_phi_ne h_span_eq : (𝓞 K)ˣ) : 𝓞 K) P' +
        -((a : ZMod p) *
          BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
            (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P) := by
  letI h_stick := StickelbergerIdealEquality.of_phiPrimeGenDescent
    S ha₁ ha₂ h_ne_zero h_span
  letI h_phi_ne := phiPrimeGenDescent_ne_zero S ha₁ ha₂ h_ne_zero
  letI h_span_eq : Ideal.span ({h_stick.gen} : Set (𝓞 K)) =
      Ideal.span ({phiPrimeGenDescent S ha₁ ha₂ h_ne_zero} : Set (𝓞 K)) := by
    rw [h_stick.span_gen, ← h_span]
  haveI : P'.IsPrime := hP'_max.isPrime
  have h_unit_eq := unitFactorOfSpanEq_eq h_phi_ne h_span_eq
  have h_unit_notin := unitFactorOfSpanEq_notMem h_stick_gen_notin h_phi_ne h_span_eq
  rw [phiPrimeGen_eq_gen]
  conv_lhs =>
    rw [h_unit_eq,
      BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical_mul
        hP'_bot hP'_max h_unit_notin h_phi_notin_P']
  rw [h_K_chain]

/-- **The unit correction is exactly the obstruction to the uncorrected
K2-2 target for the extracted `phiPrimeGen`.**  Under the K-chain output
for `phiPrimeGenDescent`, the desired target for the arbitrary generator
chosen by `StickelbergerIdealEquality` holds if and only if the specific
unit relating that chosen generator to the descended Gauss-sum generator
has trivial symbol. -/
theorem K_chain_at_h_stick_gen_target_iff_extracted_unit_symbol_zero
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) (hP'_max : P'.IsMaximal)
    (h_phi_notin_P' : phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ∉ P')
    (h_span : Ideal.span ({phiPrimeGenDescent S ha₁ ha₂ h_ne_zero} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P)
    (h_K_chain :
      BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) P' =
      -((a : ZMod p) *
        BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P))
    (h_stick_gen_notin :
      (StickelbergerIdealEquality.of_phiPrimeGenDescent
        S ha₁ ha₂ h_ne_zero h_span).gen ∉ P') :
    letI h_stick := StickelbergerIdealEquality.of_phiPrimeGenDescent
      S ha₁ ha₂ h_ne_zero h_span
    letI h_phi_ne := phiPrimeGenDescent_ne_zero S ha₁ ha₂ h_ne_zero
    letI h_span_eq : Ideal.span ({h_stick.gen} : Set (𝓞 K)) =
      Ideal.span ({phiPrimeGenDescent S ha₁ ha₂ h_ne_zero} : Set (𝓞 K)) := by
      rw [h_stick.span_gen, ← h_span]
    (BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGen h_stick) P' =
      -((a : ZMod p) *
        BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P)) ↔
      BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K)
        ((unitFactorOfSpanEq h_phi_ne h_span_eq : (𝓞 K)ˣ) : 𝓞 K) P' = 0 := by
  letI h_stick := StickelbergerIdealEquality.of_phiPrimeGenDescent
    S ha₁ ha₂ h_ne_zero h_span
  letI h_phi_ne := phiPrimeGenDescent_ne_zero S ha₁ ha₂ h_ne_zero
  letI h_span_eq : Ideal.span ({h_stick.gen} : Set (𝓞 K)) =
      Ideal.span ({phiPrimeGenDescent S ha₁ ha₂ h_ne_zero} : Set (𝓞 K)) := by
    rw [h_stick.span_gen, ← h_span]
  let target : ZMod p :=
    -((a : ZMod p) *
      BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P)
  let unitSymbol : ZMod p :=
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
      (p := p) (K := K)
      ((unitFactorOfSpanEq h_phi_ne h_span_eq : (𝓞 K)ˣ) : 𝓞 K) P'
  have h_corr :
      BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (phiPrimeGen h_stick) P' =
        unitSymbol + target :=
    K_chain_at_h_stick_gen_via_extracted_unit_with_correction
      S ha₁ ha₂ h_ne_zero hP'_bot hP'_max h_phi_notin_P' h_span
      h_K_chain h_stick_gen_notin
  constructor
  · intro h_target
    have h_add : unitSymbol + target = target := by
      rw [← h_corr, h_target]
    have h_add' : unitSymbol + target = 0 + target := by
      simpa using h_add
    exact add_right_cancel h_add'
  · intro h_unit
    change unitSymbol = 0 at h_unit
    rw [h_corr, h_unit, zero_add]

/-- **K-chain at h_stick.gen via unit-factor extraction**: combines
unitFactorOfSpanEq with the apex theorem. Given the K-chain output for
phiPrimeGenDescent + the U-chain symbol vanishing for the specific
extracted unit, conclude the K-chain for h_stick.gen.

The substantive open content reduces to: the SPECIFIC unit
`unitFactorOfSpanEq` (constructed via Classical.choose from the span
equality) has trivial residue symbol at `P'`. -/
theorem K_chain_at_h_stick_gen_via_extracted_unit
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    {P P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) (hP'_max : P'.IsMaximal)
    (h_phi_notin_P' : phiPrimeGenDescent S ha₁ ha₂ h_ne_zero ∉ P')
    (h_span : Ideal.span ({phiPrimeGenDescent S ha₁ ha₂ h_ne_zero} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P)
    (h_K_chain :
      BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGenDescent S ha₁ ha₂ h_ne_zero) P' =
      -((a : ZMod p) *
        BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P))
    (h_stick_gen_notin :
      (StickelbergerIdealEquality.of_phiPrimeGenDescent
        S ha₁ ha₂ h_ne_zero h_span).gen ∉ P')
    (hu_symbol_zero :
      letI h_stick := StickelbergerIdealEquality.of_phiPrimeGenDescent
        S ha₁ ha₂ h_ne_zero h_span
      letI h_phi_ne := phiPrimeGenDescent_ne_zero S ha₁ ha₂ h_ne_zero
      letI h_span_eq : Ideal.span ({h_stick.gen} : Set (𝓞 K)) =
        Ideal.span ({phiPrimeGenDescent S ha₁ ha₂ h_ne_zero} : Set (𝓞 K)) := by
        rw [h_stick.span_gen, ← h_span]
      BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K)
        ((unitFactorOfSpanEq h_phi_ne h_span_eq : (𝓞 K)ˣ) : 𝓞 K) P' = 0) :
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGen
          (StickelbergerIdealEquality.of_phiPrimeGenDescent
            S ha₁ ha₂ h_ne_zero h_span)) P' =
      -((a : ZMod p) *
        BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P) := by
  set h_stick := StickelbergerIdealEquality.of_phiPrimeGenDescent
    S ha₁ ha₂ h_ne_zero h_span with h_stick_def
  have h_phi_ne := phiPrimeGenDescent_ne_zero S ha₁ ha₂ h_ne_zero
  have h_span_eq : Ideal.span ({h_stick.gen} : Set (𝓞 K)) =
      Ideal.span ({phiPrimeGenDescent S ha₁ ha₂ h_ne_zero} : Set (𝓞 K)) := by
    rw [h_stick.span_gen, ← h_span]
  have h_unit_eq := unitFactorOfSpanEq_eq h_phi_ne h_span_eq
  haveI : P'.IsPrime := hP'_max.isPrime
  have h_unit_notin := unitFactorOfSpanEq_notMem h_stick_gen_notin h_phi_ne h_span_eq
  exact pthSymbolAtPrime_canonical_h_stick_gen_eq_K_chain_target
    S ha₁ ha₂ h_ne_zero hP'_bot hP'_max h_phi_notin_P' h_span h_K_chain
    (unitFactorOfSpanEq h_phi_ne h_span_eq)
    h_unit_eq h_unit_notin hu_symbol_zero

/-! ### K-chain at h_stick.gen for index 1 with unit extraction

Specialization of `K_chain_at_h_stick_gen_via_extracted_unit` at index `a = 1`,
giving the cleanest form: `pthSymbol (phiPrimeGen h_stick) P' = -pthSymbol NP' P`. -/

/-- **K-chain at h_stick.gen, index 1**: at index `a = 1`, the K-chain
output simplifies to `-pthSymbol NP' P` (without the `a` factor). -/
theorem K_chain_at_h_stick_gen_via_extracted_unit_index_one
    {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)] [NeZero p]
    {k : Type*} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type*} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R']
    (S : FullTeichDworkSetup ℓ p k K R')
    (h_one_le_p_minus_one : 1 ≤ p - 1)
    (h_ne_zero : S.gaussSumInt 1 ^ p ≠ 0)
    {P P' : Ideal (𝓞 K)}
    (hP'_bot : P' ≠ ⊥) (hP'_max : P'.IsMaximal)
    (h_phi_notin_P' : phiPrimeGenDescent S
      (le_refl 1) h_one_le_p_minus_one h_ne_zero ∉ P')
    (h_span : Ideal.span ({phiPrimeGenDescent S
      (le_refl 1) h_one_le_p_minus_one h_ne_zero} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K) P)
    (h_K_chain :
      BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGenDescent S
          (le_refl 1) h_one_le_p_minus_one h_ne_zero) P' =
      -BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P)
    (h_stick_gen_notin :
      (StickelbergerIdealEquality.of_phiPrimeGenDescent
        S (le_refl 1) h_one_le_p_minus_one h_ne_zero h_span).gen ∉ P')
    (hu_symbol_zero :
      letI h_stick := StickelbergerIdealEquality.of_phiPrimeGenDescent
        S (le_refl 1) h_one_le_p_minus_one h_ne_zero h_span
      letI h_phi_ne := phiPrimeGenDescent_ne_zero S
        (le_refl 1) h_one_le_p_minus_one h_ne_zero
      letI h_span_eq : Ideal.span ({h_stick.gen} : Set (𝓞 K)) =
        Ideal.span ({phiPrimeGenDescent S
          (le_refl 1) h_one_le_p_minus_one h_ne_zero} : Set (𝓞 K)) := by
        rw [h_stick.span_gen, ← h_span]
      BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K)
        ((unitFactorOfSpanEq h_phi_ne h_span_eq : (𝓞 K)ˣ) : 𝓞 K) P' = 0) :
    BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGen
          (StickelbergerIdealEquality.of_phiPrimeGenDescent
            S (le_refl 1) h_one_le_p_minus_one h_ne_zero h_span)) P' =
      -BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P := by
  -- Adapt h_K_chain to the K-chain general form.
  have h_K_chain' :
      BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
        (p := p) (K := K) (phiPrimeGenDescent S
          (le_refl 1) h_one_le_p_minus_one h_ne_zero) P' =
      -(((1 : ℕ) : ZMod p) *
        BernoulliRegular.Furtwaengler.pthSymbolAtPrime_canonical
          (p := p) (K := K) (((Fintype.card (𝓞 K ⧸ P') : ℤ) : 𝓞 K)) P) := by
    rw [h_K_chain]; push_cast; ring
  have h_apex := K_chain_at_h_stick_gen_via_extracted_unit
    (a := 1) S (le_refl 1) h_one_le_p_minus_one h_ne_zero hP'_bot hP'_max
    h_phi_notin_P' h_span h_K_chain' h_stick_gen_notin hu_symbol_zero
  rw [h_apex]
  push_cast
  ring

/-! ### Caller-facing K2-2 wrappers for the extracted Stickelberger generator -/

end Furtwaengler

end BernoulliRegular

end

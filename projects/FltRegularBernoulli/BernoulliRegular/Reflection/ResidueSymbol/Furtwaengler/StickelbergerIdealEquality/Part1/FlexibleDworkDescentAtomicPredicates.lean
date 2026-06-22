module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.StickelbergerIdealEquality.Part1.DworkDescentAtomicPredicates

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace ConductorFlexibleFullTeichDworkSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
variable [IsScalarTower ℤ (𝓞 K) (𝓞 R')]

variable (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Flexible Dwork exact-order Q-adic containment for `S.gaussSumInt a ^ p`. -/
theorem gaussSumInt_pow_p_mem_Q_pow_p_mul_stickOrdOrd
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumInt a ^ p ∈ S.Q ^ (p * S.stickOrdOrd a) := by
  classical
  have h := (S.gaussSumInt_qadic_ord_at_prime_ord_dwork a ha₁ ha₂).1
  have hpow := Ideal.pow_mem_pow h p
  rwa [← pow_mul, mul_comm] at hpow

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Flexible Dwork exact-order Q-adic non-containment for
`S.gaussSumInt a ^ p`. -/
theorem gaussSumInt_pow_p_not_mem_Q_pow_p_mul_stickOrdOrd_succ
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumInt a ^ p ∉ S.Q ^ (p * S.stickOrdOrd a + 1) := by
  classical
  set x : 𝓞 R' := S.gaussSumInt a with hx_def
  set s : ℕ := S.stickOrdOrd a with hs_def
  have h_exact := S.gaussSumInt_qadic_ord_at_prime_ord_dwork a ha₁ ha₂
  have h_mem : x ∈ S.Q ^ s := by
    simpa [x, s, hx_def, hs_def] using h_exact.1
  have h_not : x ∉ S.Q ^ (s + 1) := by
    simpa [x, s, hx_def, hs_def] using h_exact.2
  have hQ_ne : S.Q ≠ ⊥ := S.concrete.Q_ne_bot'
  have hQ_prime : Prime S.Q :=
    Ideal.prime_of_isPrime hQ_ne S.concrete.hQ_prime
  have h_dvd : S.Q ^ s ∣ Ideal.span ({x} : Set (𝓞 R')) := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h_mem
  have h_not_dvd : ¬ S.Q ^ (s + 1) ∣ Ideal.span ({x} : Set (𝓞 R')) := fun h_dvd' =>
    h_not ((Ideal.span_singleton_le_iff_mem (I := S.Q ^ (s + 1))).mp
      (Ideal.dvd_iff_le.mp h_dvd'))
  have h_emult :
      emultiplicity S.Q (Ideal.span ({x} : Set (𝓞 R'))) = (s : ℕ∞) :=
    emultiplicity_eq_coe.mpr ⟨h_dvd, h_not_dvd⟩
  have h_emult_pow :
      emultiplicity S.Q (Ideal.span ({x} : Set (𝓞 R')) ^ p) =
        ((p * s : ℕ) : ℕ∞) := by
    rw [emultiplicity_pow hQ_prime, h_emult]
    norm_num
  intro h_mem_pow
  have h_dvd_pow :
      S.Q ^ (p * s + 1) ∣ Ideal.span ({x ^ p} : Set (𝓞 R')) := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h_mem_pow
  have h_le :
      ((p * s + 1 : ℕ) : ℕ∞) ≤
        emultiplicity S.Q (Ideal.span ({x ^ p} : Set (𝓞 R')) : Ideal (𝓞 R')) :=
    pow_dvd_iff_le_emultiplicity.mp h_dvd_pow
  have h_span_pow :
      Ideal.span ({x ^ p} : Set (𝓞 R')) =
        Ideal.span ({x} : Set (𝓞 R')) ^ p :=
    (Ideal.span_singleton_pow x p).symm
  rw [h_span_pow, h_emult_pow] at h_le
  have h_le_nat : p * s + 1 ≤ p * s := by
    exact_mod_cast h_le
  exact (Nat.not_succ_le_self (p * s)) h_le_nat

/-- Flexible per-`a` descent at the flexible descent prime. -/
theorem descentPrime_pow_mem_of_dwork_exactOrder
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    {γ : 𝓞 K} (hγ_ne : γ ≠ 0)
    (hγ : algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p)
    {n : ℕ}
    (hn : S.concrete.descentRamificationIdx * n ≤ p * S.stickOrdOrd a) :
    γ ∈ S.concrete.descentPrime ^ n := by
  have h_image_mem : S.gaussSumInt a ^ p ∈ S.Q ^ (p * S.stickOrdOrd a) :=
    S.gaussSumInt_pow_p_mem_Q_pow_p_mul_stickOrdOrd ha₁ ha₂
  have h_image :
      algebraMap (𝓞 K) (𝓞 R') γ ∈ S.Q ^ (p * S.stickOrdOrd a) := hγ ▸ h_image_mem
  have h_pow_le :
      S.Q ^ (p * S.stickOrdOrd a) ≤
        S.Q ^ (S.concrete.descentRamificationIdx * n) :=
    Ideal.pow_le_pow_right hn
  have h_image' :
      algebraMap (𝓞 K) (𝓞 R') γ ∈
        S.Q ^ (S.concrete.descentRamificationIdx * n) :=
    h_pow_le h_image
  exact (S.concrete.mem_descentPrime_pow_iff_algebraMap_mem_Q_pow_mul
    hγ_ne n).mpr h_image'

/-- Flexible maximal-power descent form. -/
theorem descentPrime_pow_div_mem_of_dwork_exactOrder
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    {γ : 𝓞 K} (hγ_ne : γ ≠ 0)
    (hγ : algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p) :
    γ ∈ S.concrete.descentPrime ^
      ((p * S.stickOrdOrd a) / S.concrete.descentRamificationIdx) := by
  apply S.descentPrime_pow_mem_of_dwork_exactOrder ha₁ ha₂ hγ_ne hγ
  rw [mul_comm]
  exact Nat.div_mul_le_self (p * S.stickOrdOrd a) S.concrete.descentRamificationIdx

/-- Flexible exact descent-prime order from Dwork exact order. -/
theorem descentPrime_pow_div_mem_and_not_succ_of_dwork_exactOrder
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    {γ : 𝓞 K} (hγ_ne : γ ≠ 0)
    (hγ : algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p)
    (h_div : S.concrete.descentRamificationIdx ∣ p * S.stickOrdOrd a) :
    γ ∈ S.concrete.descentPrime ^
        ((p * S.stickOrdOrd a) / S.concrete.descentRamificationIdx) ∧
      γ ∉ S.concrete.descentPrime ^
        (((p * S.stickOrdOrd a) / S.concrete.descentRamificationIdx) + 1) := by
  classical
  set e := S.concrete.descentRamificationIdx with he_def
  set n := (p * S.stickOrdOrd a) / e with hn_def
  have h_en : e * n = p * S.stickOrdOrd a := by
    rw [hn_def, mul_comm]
    exact Nat.div_mul_cancel h_div
  rw [S.concrete.mem_descentPrime_pow_and_not_succ_iff hγ_ne n]
  constructor
  · rw [hγ, h_en]
    exact S.gaussSumInt_pow_p_mem_Q_pow_p_mul_stickOrdOrd ha₁ ha₂
  · intro h_mem
    have he_pos : 0 < e := by
      simpa [e, he_def] using S.concrete.descentRamificationIdx_pos
    have h_succ_le : p * S.stickOrdOrd a + 1 ≤ e * (n + 1) := by
      rw [Nat.mul_succ, h_en]
      omega
    have h_pow_le : S.Q ^ (e * (n + 1)) ≤
        S.Q ^ (p * S.stickOrdOrd a + 1) :=
      Ideal.pow_le_pow_right h_succ_le
    exact S.gaussSumInt_pow_p_not_mem_Q_pow_p_mul_stickOrdOrd_succ ha₁ ha₂
      (h_pow_le (hγ ▸ h_mem))

/-- Flexible descent-prime emultiplicity from Dwork exact order. -/
theorem descentPrime_emultiplicity_eq_of_dwork_exactOrder
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    {γ : 𝓞 K} (hγ_ne : γ ≠ 0)
    (hγ : algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p)
    (h_div : S.concrete.descentRamificationIdx ∣ p * S.stickOrdOrd a) :
    emultiplicity S.concrete.descentPrime (Ideal.span ({γ} : Set (𝓞 K))) =
      (((p * S.stickOrdOrd a) / S.concrete.descentRamificationIdx : ℕ) : ℕ∞) := by
  classical
  have h_exact :=
    S.descentPrime_pow_div_mem_and_not_succ_of_dwork_exactOrder
      ha₁ ha₂ hγ_ne hγ h_div
  refine emultiplicity_eq_coe.mpr ⟨?_, ?_⟩
  · rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h_exact.1
  · intro h_dvd
    exact h_exact.2
      ((Ideal.span_singleton_le_iff_mem
        (I := S.concrete.descentPrime ^
          (((p * S.stickOrdOrd a) / S.concrete.descentRamificationIdx) + 1))).mp
        (Ideal.dvd_iff_le.mp h_dvd))

/-- Flexible existence form combining Galois descent and Dwork exact order. -/
theorem exists_descentPrime_pow_mul_stickOrdOrd_div_of_isGalPsiShiftCompatible
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0) :
    ∃ γ : 𝓞 K, γ ≠ 0 ∧
      algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p ∧
      γ ∈ S.concrete.descentPrime ^
        ((p * S.stickOrdOrd a) / S.concrete.descentRamificationIdx) := by
  classical
  obtain ⟨γ, hγ_eq⟩ :=
    S.concrete.isGalDescentTo_OK_of_isGalPsiShiftCompatible a h_psi
  have hγ_ne : γ ≠ 0 := by
    intro hzero
    apply h_ne_zero
    have hsource_zero : S.concrete.gaussSumInt a ^ p = 0 := by
      rw [← hγ_eq, hzero, map_zero]
    exact hsource_zero
  refine ⟨γ, hγ_ne, hγ_eq, ?_⟩
  exact S.descentPrime_pow_div_mem_of_dwork_exactOrder ha₁ ha₂ hγ_ne hγ_eq

/-- Flexible constructive descent generator. -/
noncomputable def phiPrimeGenDescent
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0) : 𝓞 K :=
  (S.exists_descentPrime_pow_mul_stickOrdOrd_div_of_isGalPsiShiftCompatible
    h_psi ha₁ ha₂ h_ne_zero).choose

theorem phiPrimeGenDescent_ne_zero
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0) :
    S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero ≠ 0 :=
  (S.exists_descentPrime_pow_mul_stickOrdOrd_div_of_isGalPsiShiftCompatible
    h_psi ha₁ ha₂ h_ne_zero).choose_spec.1

/-- Flexible constructive descent property. -/
theorem algebraMap_phiPrimeGenDescent
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0) :
    algebraMap (𝓞 K) (𝓞 R')
        (S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero) =
      S.gaussSumInt a ^ p :=
  (S.exists_descentPrime_pow_mul_stickOrdOrd_div_of_isGalPsiShiftCompatible
    h_psi ha₁ ha₂ h_ne_zero).choose_spec.2.1

/-- Flexible exact descent-prime valuation of the actual descended Gauss sum. -/
theorem emultiplicity_descentPrime_phiPrimeGenDescent_eq_of_dwork_exactOrder
    [IsGalois K R'] [FiniteDimensional K R']
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    (h_psi : S.concrete.IsGalPsiShiftCompatible)
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0)
    (h_div : S.concrete.descentRamificationIdx ∣ p * S.stickOrdOrd a) :
    emultiplicity S.concrete.descentPrime
        (Ideal.span ({S.phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero} : Set (𝓞 K))) =
      (((p * S.stickOrdOrd a) / S.concrete.descentRamificationIdx : ℕ) : ℕ∞) :=
  S.descentPrime_emultiplicity_eq_of_dwork_exactOrder ha₁ ha₂
    (S.phiPrimeGenDescent_ne_zero h_psi ha₁ ha₂ h_ne_zero)
    (S.algebraMap_phiPrimeGenDescent h_psi ha₁ ha₂ h_ne_zero)
    h_div

/-! ### Flexible atomic Stickelberger predicates -/

/-- Flexible atomic predicate: per-conjugate exact exponent for a fixed
descended element. -/
def StickelbergerExactConjugateExponents (γ : 𝓞 K) : Prop :=
  ∀ a : CyclotomicUnitDelta p,
    emultiplicity
        (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
          S.concrete.descentPrime)
        (Ideal.span ({γ} : Set (𝓞 K))) =
      ((a : ZMod p).val : ℕ∞)

/-- Flexible atomic predicate: support of `(γ)` is contained in the
cyclotomic orbit of the flexible descent prime. -/
def StickelbergerSupportInOrbit (γ : 𝓞 K) : Prop :=
  ∀ b : Ideal (𝓞 K),
    b ∈ UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({γ} : Set (𝓞 K))) →
    b ∈ cyclotomicConjugates (p := p) (K := K) S.concrete.descentPrime

/-- Flexible atomic predicate: the cyclotomic orbit indexing of the descent
prime is faithful. -/
def StickelbergerOrbitFaithful : Prop :=
  Function.Injective (fun a : CyclotomicUnitDelta p =>
    cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ S.concrete.descentPrime)

/-- Flexible structural multiplicity predicate for the Stickelberger ideal. -/
def StickelbergerIdealConjugateMultiplicity : Prop :=
  ∀ a : CyclotomicUnitDelta p,
    (UniqueFactorizationMonoid.normalizedFactors
        (stickelbergerIdeal (p := p) (K := K) S.concrete.descentPrime)).count
      (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ S.concrete.descentPrime) =
    ((a : ZMod p).val : ℕ)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Flexible API: nontriviality of integral residue-character powers. -/
theorem residueCharInt_pow_ne_one
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.concrete.residueCharInt ^ a ≠ 1 := by
  have hfield :
      (S.concrete.residueCharInt ^ a).ringHomComp (algebraMap (𝓞 R') R') ≠ 1 := by
    rw [← MulChar.ringHomComp_pow, S.concrete.residueCharInt_ringHomComp]
    exact S.concrete.abstractSetup.residueChar_pow_ne_one ha₁ ha₂
  exact (MulChar.ringHomComp_ne_one_iff
    (R := k) (R' := 𝓞 R') (R'' := R')
    (f := algebraMap (𝓞 R') R') NumberField.RingOfIntegers.coe_injective).mp hfield

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Flexible API: the integral additive character is primitive. -/
theorem psiInt_isPrimitive :
    S.concrete.psiInt.IsPrimitive := by
  apply AddChar.IsPrimitive.of_ne_one
  intro h_eq
  have h_psi_eq : S.concrete.psi = 1 := by
    ext x
    rw [AddChar.one_apply]
    have h_alg := S.concrete.algebraMap_psiInt x
    have h_one : S.concrete.psiInt x = (1 : 𝓞 R') := by
      have := DFunLike.congr_fun h_eq x
      simpa [AddChar.one_apply] using this
    rw [h_one, map_one] at h_alg
    exact h_alg.symm
  have h_one_ne : (1 : k) ≠ 0 := one_ne_zero
  have h_shift := S.concrete.hpsi h_one_ne
  apply h_shift
  ext y
  simp [h_psi_eq, AddChar.one_apply]

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Flexible API: Gauss-sum norm relation in `𝓞 R'`. -/
theorem gaussSumInt_mul_inv_eq_card
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumInt a *
        gaussSum (S.concrete.residueCharInt ^ a)⁻¹
          S.concrete.psiInt⁻¹ =
      (Fintype.card k : 𝓞 R') := by
  have h_ne_one := S.residueCharInt_pow_ne_one ha₁ ha₂
  have h_prim := S.psiInt_isPrimitive
  exact gaussSum_mul_gaussSum_eq_card (R := k) (R' := 𝓞 R')
    (χ := S.concrete.residueCharInt ^ a)
    (ψ := S.concrete.psiInt) h_ne_one h_prim

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Flexible API: power form of the Gauss-sum norm in `𝓞 R'`. -/
theorem gaussSumInt_pow_p_mul_inv_pow_p_eq_ell_pow
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumInt a ^ p *
        gaussSum (S.concrete.residueCharInt ^ a)⁻¹
          S.concrete.psiInt⁻¹ ^ p =
      (ℓ : 𝓞 R') ^ (S.concrete.f * p) := by
  rw [← mul_pow, S.gaussSumInt_mul_inv_eq_card ha₁ ha₂,
    S.concrete.card_k, Nat.cast_pow, ← pow_mul]

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Flexible API: every prime containing `S.gaussSumInt a ^ p` contains `ℓ`. -/
theorem ell_mem_of_gaussSumInt_pow_p_mem
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    {B : Ideal (𝓞 R')} [B.IsPrime]
    (h_in : S.gaussSumInt a ^ p ∈ B) :
    (ℓ : 𝓞 R') ∈ B :=
  prime_mem_of_mul_eq_pow
    (S.gaussSumInt_pow_p_mul_inv_pow_p_eq_ell_pow ha₁ ha₂) h_in

/-- Flexible API: support of a descended Gauss sum lies in the cyclotomic orbit
of the flexible descent prime. -/
theorem stickelbergerSupportInOrbit_of_descentGaussSum
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    {γ : 𝓞 K} (hγ_ne : γ ≠ 0)
    (hγ : algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p) :
    S.StickelbergerSupportInOrbit γ := by
  classical
  intro b hb_in
  have hb_prime_in_uf :=
    UniqueFactorizationMonoid.prime_of_normalized_factor b hb_in
  haveI hb_isPrime : b.IsPrime := Ideal.isPrime_of_prime hb_prime_in_uf
  have _hspan_ne : Ideal.span ({γ} : Set (𝓞 K)) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hb_dvd : b ∣ Ideal.span ({γ} : Set (𝓞 K)) :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hb_in
  have hγ_in_b : γ ∈ b := by
    have h_span_le : Ideal.span ({γ} : Set (𝓞 K)) ≤ b := Ideal.le_of_dvd hb_dvd
    exact h_span_le (Ideal.subset_span (Set.mem_singleton _))
  have hker_le : RingHom.ker (algebraMap (𝓞 K) (𝓞 R')) ≤ b := by
    rw [NumberField.RingOfIntegers.ker_algebraMap_eq_bot K R']
    exact bot_le
  obtain ⟨B, hB_prime, hB_under⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
      (R := 𝓞 K) (S := 𝓞 R') b hker_le
  haveI : B.IsPrime := hB_prime
  have h_algMap_in_B : algebraMap (𝓞 K) (𝓞 R') γ ∈ B := by
    have : γ ∈ B.comap (algebraMap (𝓞 K) (𝓞 R')) := hB_under ▸ hγ_in_b
    rwa [Ideal.mem_comap] at this
  have h_gauss_in_B : S.gaussSumInt a ^ p ∈ B := hγ ▸ h_algMap_in_B
  have h_ell_in_B : (ℓ : 𝓞 R') ∈ B :=
    S.ell_mem_of_gaussSumInt_pow_p_mem ha₁ ha₂ h_gauss_in_B
  haveI := S.concrete.descentPrime_isPrime
  have h_descent_under :
      S.concrete.descentPrime.under ℤ =
        Ideal.span ({(ℓ : ℤ)} : Set ℤ) := by
    have h_ell_in : (ℓ : 𝓞 K) ∈ S.concrete.descentPrime :=
      S.concrete.descentPrime_contains_ell
    have h_ell_in_under : (ℓ : ℤ) ∈
        S.concrete.descentPrime.under ℤ := by
      rw [show S.concrete.descentPrime.under ℤ =
          Ideal.comap (algebraMap ℤ (𝓞 K))
            S.concrete.descentPrime from rfl]
      rw [Ideal.mem_comap]
      rw [show (algebraMap ℤ (𝓞 K) (ℓ : ℤ)) = (ℓ : 𝓞 K) from by push_cast; rfl]
      exact h_ell_in
    have h_under_ne :
        S.concrete.descentPrime.under ℤ ≠ ⊥ := by
      intro hbot
      rw [hbot, Ideal.mem_bot] at h_ell_in_under
      exact (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero : (ℓ : ℤ) ≠ 0)
        h_ell_in_under
    haveI : (S.concrete.descentPrime.under ℤ).IsPrime :=
      Ideal.IsPrime.under ℤ (P := S.concrete.descentPrime)
    haveI : (S.concrete.descentPrime.under ℤ).IsMaximal :=
      Ideal.IsPrime.isMaximal inferInstance h_under_ne
    haveI : (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).IsPrime := by
      rw [Ideal.span_singleton_prime
        (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)]
      exact Nat.prime_iff_prime_int.mp (Fact.out : ℓ.Prime)
    haveI : (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).IsMaximal :=
      Ideal.IsPrime.isMaximal inferInstance (by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)
    have h2 :
        Ideal.span ({(ℓ : ℤ)} : Set ℤ) ≤
          S.concrete.descentPrime.under ℤ := by
      rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact h_ell_in_under
    exact (Ideal.IsMaximal.eq_of_le inferInstance
      (Ideal.IsMaximal.ne_top inferInstance) h2).symm
  have h_descent_ne : S.concrete.descentPrime ≠ ⊥ :=
    S.concrete.descentPrime_ne_bot
  have h_b_eq : B.under (𝓞 K) = b := hB_under
  have h_orbit :
      B.under (𝓞 K) ∈ cyclotomicConjugates (p := p) (K := K)
        S.concrete.descentPrime :=
    Q_under_mem_cyclotomicConjugates (K := K) (p := p) (ℓ := ℓ)
      h_descent_ne h_descent_under B h_ell_in_B
  rw [h_b_eq] at h_orbit
  exact h_orbit

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Flexible API: the descent prime is non-bot. -/
private theorem descentPrime_ne_bot' :
    S.concrete.descentPrime ≠ ⊥ :=
  S.concrete.descentPrime_ne_bot

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Flexible API: each Galois conjugate of the descent prime is non-bot. -/
theorem cyclotomicGaloisConjugate_descentPrime_ne_bot
    (a : CyclotomicUnitDelta p) :
    cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.concrete.descentPrime ≠ ⊥ :=
  cyclotomicGaloisConjugate_ne_bot a⁻¹ S.descentPrime_ne_bot'

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Flexible API: each Stickelberger factor is nonzero. -/
private theorem stickelbergerFactor_ne_zero (a : CyclotomicUnitDelta p) :
    (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.concrete.descentPrime ^ ((a : ZMod p).val) :
        Ideal (𝓞 K)) ≠ 0 := by
  rw [Ne, Ideal.zero_eq_bot]
  exact pow_ne_zero _ (S.cyclotomicGaloisConjugate_descentPrime_ne_bot a)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Flexible API: normalized factors of one Stickelberger factor. -/
theorem normalizedFactors_stickelbergerFactor (a : CyclotomicUnitDelta p) :
    UniqueFactorizationMonoid.normalizedFactors
        (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
          S.concrete.descentPrime ^ ((a : ZMod p).val) : Ideal (𝓞 K)) =
      ((a : ZMod p).val) •
        ({cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
            S.concrete.descentPrime}
          : Multiset (Ideal (𝓞 K))) := by
  haveI := S.concrete.descentPrime_isPrime
  have h_ne : cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.concrete.descentPrime ≠ ⊥ :=
    S.cyclotomicGaloisConjugate_descentPrime_ne_bot a
  haveI : (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.concrete.descentPrime).IsPrime :=
    cyclotomicGaloisConjugate_isPrime a⁻¹ _
  have h_prime : Prime (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.concrete.descentPrime) :=
    Ideal.prime_of_isPrime h_ne inferInstance
  have h_irred : Irreducible (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.concrete.descentPrime) := h_prime.irreducible
  rw [UniqueFactorizationMonoid.normalizedFactors_pow,
    UniqueFactorizationMonoid.normalizedFactors_irreducible h_irred, normalize_eq]

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Flexible API: normalized factors of a finite Stickelberger product. -/
theorem normalizedFactors_stickelbergerIdeal_finset_eq
    (s : Finset (CyclotomicUnitDelta p)) :
    UniqueFactorizationMonoid.normalizedFactors
        (∏ a ∈ s, cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
          S.concrete.descentPrime ^ ((a : ZMod p).val)) =
      ∑ a ∈ s,
        ((a : ZMod p).val) •
          ({cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
              S.concrete.descentPrime}
            : Multiset (Ideal (𝓞 K))) := by
  classical
  haveI := S.concrete.descentPrime_isPrime
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty,
      UniqueFactorizationMonoid.normalizedFactors_one]
  | insert a s has ih =>
    rw [Finset.prod_insert has, Finset.sum_insert has]
    have h_factor_ne : (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
        S.concrete.descentPrime ^ ((a : ZMod p).val) :
          Ideal (𝓞 K)) ≠ 0 :=
      S.stickelbergerFactor_ne_zero a
    have h_prod_ne : (∏ b ∈ s, cyclotomicGaloisConjugate (p := p) (K := K) b⁻¹
        S.concrete.descentPrime ^ ((b : ZMod p).val) :
          Ideal (𝓞 K)) ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot]
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro b _
      have := S.stickelbergerFactor_ne_zero b
      rwa [Ne, Ideal.zero_eq_bot] at this
    rw [UniqueFactorizationMonoid.normalizedFactors_mul h_factor_ne h_prod_ne,
      S.normalizedFactors_stickelbergerFactor a, ih]

/-- The cyclotomic Galois action on ideals as a multiplicative equivalence,
for the conductor-flexible atomic API. -/
noncomputable def cyclotomicGaloisConjugateIdealMulEquiv
    (a : CyclotomicUnitDelta p) :
    Ideal (𝓞 K) ≃* Ideal (𝓞 K) where
  toFun := cyclotomicGaloisConjugate (p := p) (K := K) a
  invFun := cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
  left_inv I := by
    rw [← cyclotomicGaloisConjugate_mul, inv_mul_cancel,
      cyclotomicGaloisConjugate_one]
  right_inv I := by
    rw [← cyclotomicGaloisConjugate_mul, mul_inv_cancel,
      cyclotomicGaloisConjugate_one]
  map_mul' I J := cyclotomicGaloisConjugate_mul_ideal a I J

/-- Flexible API: cyclotomic Galois conjugation preserves ideal
emultiplicity. -/
theorem emultiplicity_cyclotomicGaloisConjugate
    (a : CyclotomicUnitDelta p) (I J : Ideal (𝓞 K)) :
    emultiplicity
        (cyclotomicGaloisConjugate (p := p) (K := K) a I)
        (cyclotomicGaloisConjugate (p := p) (K := K) a J) =
      emultiplicity I J :=
  emultiplicity_map_eq
    (cyclotomicGaloisConjugateIdealMulEquiv (p := p) (K := K) a)

/-- Flexible API: Galois conjugation transports a principal ideal generated
by `γ` to the principal ideal generated by the conjugate of `γ`. -/
theorem cyclotomicGaloisConjugate_span_singleton'
    (a : CyclotomicUnitDelta p) (γ : 𝓞 K) :
    cyclotomicGaloisConjugate (p := p) (K := K) a
        (Ideal.span ({γ} : Set (𝓞 K))) =
      Ideal.span
        ({cyclotomicRingOfIntegersEquiv (p := p) K a γ} : Set (𝓞 K)) := by
  unfold cyclotomicGaloisConjugate
  rw [Ideal.map_span, Set.image_singleton]

/-- Flexible API: multiplicity at a conjugate prime is the selected-prime
multiplicity of the conjugated element. -/
theorem emultiplicity_conjugatePrime_span_eq_descentPrime_conjugateElement
    (a : CyclotomicUnitDelta p) (q : Ideal (𝓞 K)) (γ : 𝓞 K) :
    emultiplicity
        (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q)
        (Ideal.span ({γ} : Set (𝓞 K))) =
      emultiplicity q
        (Ideal.span
          ({cyclotomicRingOfIntegersEquiv (p := p) K a γ} : Set (𝓞 K))) := by
  have h :=
    emultiplicity_cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q
      (Ideal.span
        ({cyclotomicRingOfIntegersEquiv (p := p) K a γ} : Set (𝓞 K)))
  rw [cyclotomicGaloisConjugate_span_singleton'] at h
  have h_elem :
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹
          (cyclotomicRingOfIntegersEquiv (p := p) K a γ) = γ := by
    rw [← cyclotomicRingOfIntegersEquiv_mul_apply, inv_mul_cancel,
      cyclotomicRingOfIntegersEquiv_one_apply]
  rw [h_elem] at h
  simpa using h

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Flexible API: to prove exact Stickelberger exponents of `γ`, it suffices
to prove the selected-prime valuation of every cyclotomic conjugate of `γ`. -/
theorem stickelbergerExactConjugateExponents_of_conjugate_descentPrime_emultiplicity
    {γ : 𝓞 K}
    (h :
      ∀ a : CyclotomicUnitDelta p,
        emultiplicity S.concrete.descentPrime
            (Ideal.span
              ({cyclotomicRingOfIntegersEquiv (p := p) K a γ} : Set (𝓞 K))) =
          ((a : ZMod p).val : ℕ∞)) :
    S.StickelbergerExactConjugateExponents γ := by
  intro a
  rw [emultiplicity_conjugatePrime_span_eq_descentPrime_conjugateElement]
  exact h a

end ConductorFlexibleFullTeichDworkSetup

end Furtwaengler

end BernoulliRegular

end

module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.LeadingTerm.Part1

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

/-! ### Conductor-flexible leading-term surface

The enlarged-conductor REF-K route uses
`ConductorFlexibleFullTeichDworkSetup`, not the old exact
`FullTeichDworkSetup`.  The following definitions and small arithmetic wrappers
mirror the exact setup names so the Dwork exact-order proof can be ported
without reintroducing the pair-cyclotomic typeclass. -/

namespace ConductorFlexibleTraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (S : ConductorFlexibleTraceFormStickelbergerSetup ℓ p k K R')

/-- The cofactor `d = (#k - 1) / p`. -/
def stickD (_S : ConductorFlexibleTraceFormStickelbergerSetup ℓ p k K R') : ℕ :=
  (Fintype.card k - 1) / p

/-- The predicted reciprocal `Q`-adic order `s_ℓ(a · d)`. -/
def stickOrd (S : ConductorFlexibleTraceFormStickelbergerSetup ℓ p k K R') (a : ℕ) :
    ℕ :=
  digitSum ℓ (a * S.stickD)

/-- The ordinary-character order, expressed through the reciprocal index. -/
def stickOrdOrd (S : ConductorFlexibleTraceFormStickelbergerSetup ℓ p k K R') (a : ℕ) :
    ℕ :=
  S.stickOrd (p - a)

/-- Bundle accessor for the standard digit vector at length `S.f`. -/
def standardDigitVec (a : ℕ) : digitVec ℓ S.f :=
  Furtwaengler.standardDigitVec (Fact.out : Nat.Prime ℓ).two_le S.f a

/-- The cofactor satisfies `p * d = #k - 1`. -/
theorem p_mul_stickD_eq_card_sub_one :
    p * S.stickD = Fintype.card k - 1 := by
  rw [stickD, mul_comm]
  exact Nat.div_mul_cancel S.concrete.hdiv

/-- The standard digit vector of `a * S.stickD` has the expected weight and
value. -/
theorem standardDigitVec_weight_value
    (a : ℕ) (_ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    digitWeight (S.standardDigitVec (a * ((Fintype.card k - 1) / p))) =
        digitSum ℓ (a * ((Fintype.card k - 1) / p)) ∧
      digitValue (S.standardDigitVec (a * ((Fintype.card k - 1) / p))) =
        a * ((Fintype.card k - 1) / p) := by
  set q : ℕ := Fintype.card k with hq_def
  set d : ℕ := (q - 1) / p
  set A : ℕ := a * d with hA_def
  have hℓ_prime : Nat.Prime ℓ := Fact.out
  have hp_prime : Nat.Prime p := Fact.out
  have hℓ_ge_two : 2 ≤ ℓ := hℓ_prime.two_le
  have hq_eq : q = ℓ ^ S.f := S.card_k
  have hq_ge_two : 2 ≤ q := Fintype.one_lt_card
  have hpd : p * d = q - 1 := by
    have h := S.concrete.hdiv
    rw [mul_comm]
    exact Nat.div_mul_cancel h
  have hd_pos : 1 ≤ d := by
    have hq_sub : 1 ≤ q - 1 := by omega
    have hp_dvd : p ∣ q - 1 := S.concrete.hdiv
    have : p ≤ q - 1 := Nat.le_of_dvd hq_sub hp_dvd
    exact Nat.one_le_div_iff (by exact hp_prime.pos) |>.mpr this
  have hA_lt : A < ℓ ^ S.f := by
    have : A ≤ (p - 1) * d := Nat.mul_le_mul_right _ ha₂
    have h_pd : (p - 1) * d = p * d - d := by
      have : (p - 1) * d = p * d - 1 * d := by rw [Nat.sub_mul]
      simp [this]
    rw [← hq_eq]
    omega
  refine ⟨?_, ?_⟩
  · exact digitWeight_standardDigitVec_of_lt hℓ_ge_two hA_lt
  · exact digitValue_standardDigitVec_of_lt hℓ_ge_two hA_lt

/-- The standard digit vector of `a * S.stickD` has weight `S.stickOrd a`. -/
theorem digitWeight_standardDigitVec_eq_stickOrd
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    digitWeight (S.standardDigitVec (a * S.stickD)) = S.stickOrd a := by
  unfold stickOrd stickD
  exact (S.standardDigitVec_weight_value a ha₁ ha₂).1

/-- The standard digit vector of `a * S.stickD` has value `a * S.stickD`. -/
theorem digitValue_standardDigitVec_eq
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    digitValue (S.standardDigitVec (a * S.stickD)) = a * S.stickD := by
  unfold stickD
  exact (S.standardDigitVec_weight_value a ha₁ ha₂).2

/-- No digit vector of weight strictly less than `S.stickOrd a` survives the
reciprocal divisibility test, in the conductor-flexible setup. -/
theorem no_survivor_of_weight_lt_stickOrd
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (m : digitVec ℓ S.f) (hm : digitWeight m < S.stickOrd a) :
    ¬ (Fintype.card k - 1) ∣ ((p - a) * S.stickD + digitValue m) := by
  intro hdiv
  unfold stickOrd at hm
  unfold stickD at hm hdiv
  set q : ℕ := Fintype.card k with hq_def
  set d : ℕ := (q - 1) / p with hd_def
  set A : ℕ := a * d with hA_def
  set M : ℕ := digitValue m with hM_def
  have hpd : p * d = q - 1 := by
    have h := S.concrete.hdiv
    rw [hd_def, mul_comm]
    exact Nat.div_mul_cancel h
  have hℓ_prime : Nat.Prime ℓ := Fact.out
  have hp_prime : Nat.Prime p := Fact.out
  have hℓ_ge_two : 2 ≤ ℓ := hℓ_prime.two_le
  have hq_eq : q = ℓ ^ S.f := S.card_k
  have hq_ge_two : 2 ≤ q := Fintype.one_lt_card
  have hd_pos : 1 ≤ d := by
    have hq_sub : 1 ≤ q - 1 := by omega
    have hp_dvd : p ∣ q - 1 := S.concrete.hdiv
    have : p ≤ q - 1 := Nat.le_of_dvd hq_sub hp_dvd
    rw [hd_def]
    exact Nat.one_le_div_iff (by exact hp_prime.pos) |>.mpr this
  have hM_lt : M < q := by
    rw [hM_def, hq_eq]
    exact digitValue_lt hℓ_ge_two m
  have hM_le : M ≤ q - 1 := by omega
  have hA_le : A ≤ q - 1 - d := by
    rw [hA_def]
    have h_a_le : a ≤ p - 1 := ha₂
    have h1 : a * d ≤ (p - 1) * d := Nat.mul_le_mul_right _ h_a_le
    have h2 : (p - 1) * d = p * d - d := by
      have : (p - 1) * d = p * d - 1 * d := by rw [Nat.sub_mul]
      simp [this]
    omega
  have hA_pos : 1 ≤ A := by
    rw [hA_def]
    exact Nat.one_le_iff_ne_zero.mpr (fun h => by
      rcases Nat.mul_eq_zero.mp h with h1 | h2
      · omega
      · omega)
  have hpa_d_ge : d ≤ (p - a) * d := by
    have h_pa : 1 ≤ p - a := by omega
    have : 1 * d ≤ (p - a) * d := Nat.mul_le_mul_right _ h_pa
    simpa using this
  have h_lhs_pos : 1 ≤ (p - a) * d + M := by omega
  have hpa_d_le : (p - a) * d ≤ q - 1 - d := by
    have h1 : (p - a) * d ≤ (p - 1) * d := by
      have : p - a ≤ p - 1 := by omega
      exact Nat.mul_le_mul_right _ this
    have h2 : (p - 1) * d = p * d - d := by
      have : (p - 1) * d = p * d - 1 * d := by rw [Nat.sub_mul]
      simp [this]
    omega
  have h_lhs_lt : (p - a) * d + M < 2 * (q - 1) := by omega
  have h_lhs_eq : (p - a) * d + M = q - 1 := by
    obtain ⟨c, hc⟩ := hdiv
    have hc_eq : (q - 1) * c = (p - a) * d + M := by
      change (q - 1) * c = _
      rw [show (Fintype.card k - 1) * c = (q - 1) * c from rfl] at hc
      exact hc.symm
    have hc_pos : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with hc0 | hcp
      · rw [hc0, Nat.mul_zero] at hc_eq
        omega
      · exact hcp
    have hc_lt : c < 2 := by
      have : (q - 1) * c < (q - 1) * 2 := by
        rw [hc_eq, show (q - 1) * 2 = 2 * (q - 1) by ring]
        exact h_lhs_lt
      exact Nat.lt_of_mul_lt_mul_left this
    have hc_eq1 : c = 1 := by omega
    rw [hc_eq1, Nat.mul_one] at hc_eq
    exact hc_eq.symm
  have hM_eq_A : M = A := by
    rw [hA_def]
    have h1 : (p - a) * d + M = p * d := by
      rw [h_lhs_eq]
      exact hpd.symm
    have h2 : (p - a) * d + a * d = p * d := by
      rw [show (p - a) * d + a * d = ((p - a) + a) * d by ring]
      congr 1
      omega
    omega
  have hbound : digitSum ℓ M ≤ digitWeight m := by
    rw [hM_def]
    exact digitSum_digitValue_le_digitWeight hℓ_ge_two m
  rw [← hM_eq_A] at hm
  omega

/-- At the leading weight, any surviving digit vector is the standard digit
decomposition of `a * S.stickD`, in the conductor-flexible setup. -/
theorem unique_survivor_at_stickOrd
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (m : digitVec ℓ S.f)
    (_hw : digitWeight m = S.stickOrd a)
    (hdiv : (Fintype.card k - 1) ∣ ((p - a) * S.stickD + digitValue m)) :
    m = S.standardDigitVec (a * S.stickD) := by
  classical
  set q : ℕ := Fintype.card k with hq_def
  set d : ℕ := S.stickD
  have hℓ_prime : Nat.Prime ℓ := Fact.out
  have hp_prime : Nat.Prime p := Fact.out
  have hℓ_ge_two : 2 ≤ ℓ := hℓ_prime.two_le
  have hq_eq : q = ℓ ^ S.f := S.card_k
  have hq_ge_two : 2 ≤ q := Fintype.one_lt_card
  have hpd : p * d = q - 1 := by
    rw [show d = (Fintype.card k - 1) / p by rfl, hq_def]
    have h := S.concrete.hdiv
    rw [mul_comm]
    exact Nat.div_mul_cancel h
  have hd_pos : 1 ≤ d := by
    have hq_sub : 1 ≤ q - 1 := by omega
    have hp_dvd : p ∣ q - 1 := S.concrete.hdiv
    have hp_le : p ≤ q - 1 := Nat.le_of_dvd hq_sub hp_dvd
    change 1 ≤ S.stickD
    change 1 ≤ (q - 1) / p
    exact Nat.one_le_div_iff (by exact hp_prime.pos) |>.mpr hp_le
  have hM_lt : digitValue m < q := by
    rw [hq_eq]
    exact digitValue_lt hℓ_ge_two m
  have hM_le : digitValue m ≤ q - 1 := by omega
  have hA_le : a * d ≤ q - 1 - d := by
    have h_a_le : a ≤ p - 1 := ha₂
    have h1 : a * d ≤ (p - 1) * d := Nat.mul_le_mul_right _ h_a_le
    have h2 : (p - 1) * d = p * d - d := by
      have : (p - 1) * d = p * d - 1 * d := by rw [Nat.sub_mul]
      simp [this]
    omega
  have hA_pos : 1 ≤ a * d := by
    have : 1 * 1 ≤ a * d := Nat.mul_le_mul ha₁ hd_pos
    simpa using this
  have hpa_d_le : (p - a) * d ≤ q - 1 - d := by
    have : p - a ≤ p - 1 := by omega
    have h1 : (p - a) * d ≤ (p - 1) * d := Nat.mul_le_mul_right _ this
    have h2 : (p - 1) * d = p * d - d := by
      have : (p - 1) * d = p * d - 1 * d := by rw [Nat.sub_mul]
      simp [this]
    omega
  have hpa_d_ge : d ≤ (p - a) * d := by
    have h_pa : 1 ≤ p - a := by omega
    have : 1 * d ≤ (p - a) * d := Nat.mul_le_mul_right _ h_pa
    simpa using this
  have h_lhs_lt : (p - a) * d + digitValue m < 2 * (q - 1) := by omega
  have h_lhs_pos : 1 ≤ (p - a) * d + digitValue m := by omega
  have h_lhs_eq : (p - a) * d + digitValue m = q - 1 := by
    obtain ⟨c, hc⟩ := hdiv
    have hc_eq : (q - 1) * c = (p - a) * d + digitValue m := by
      change (q - 1) * c = _
      rw [show (Fintype.card k - 1) * c = (q - 1) * c from rfl] at hc
      exact hc.symm
    have hc_pos : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with hc0 | hcp
      · rw [hc0, Nat.mul_zero] at hc_eq
        omega
      · exact hcp
    have hc_lt : c < 2 := by
      have : (q - 1) * c < (q - 1) * 2 := by
        rw [hc_eq, show (q - 1) * 2 = 2 * (q - 1) by ring]
        exact h_lhs_lt
      exact Nat.lt_of_mul_lt_mul_left this
    have hc_eq1 : c = 1 := by omega
    rw [hc_eq1, Nat.mul_one] at hc_eq
    exact hc_eq.symm
  have hM_eq_A : digitValue m = a * d := by
    have h1 : (p - a) * d + digitValue m = p * d := by
      rw [h_lhs_eq]
      exact hpd.symm
    have h2 : (p - a) * d + a * d = p * d := by
      rw [show (p - a) * d + a * d = ((p - a) + a) * d by ring]
      congr 1
      omega
    omega
  have hA_lt : a * d < ℓ ^ S.f := by
    rw [← hq_eq]
    omega
  have hstd :
      Furtwaengler.standardDigitVec (Fact.out : Nat.Prime ℓ).two_le S.f (a * d) =
        S.standardDigitVec (a * d) := rfl
  rw [← hstd]
  exact digitVec_eq_standardDigitVec_of_value hℓ_ge_two hA_lt m hM_eq_A

end ConductorFlexibleTraceFormStickelbergerSetup

namespace ConductorFlexibleFullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (S : ConductorFlexibleFullTeichStickelbergerSetup ℓ p k K R')

/-- Stick-`D` form of the flexible reciprocal residue-character identity. -/
theorem residueCharInt_rec_eq_teichUnitFull_pow_stickD
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) (x : kˣ) :
    S.residueCharInt (x : k) ^ (p - a) =
      (S.teichUnitFull x : 𝓞 R') ^ ((p - a) * S.stickD) := by
  unfold ConductorFlexibleTraceFormStickelbergerSetup.stickD
  exact S.residueCharInt_rec_eq_teichUnitFull_pow a ha₁ ha₂ x

end ConductorFlexibleFullTeichStickelbergerSetup

namespace ConductorFlexibleFullTeichDworkSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')

/-- Reciprocal-convention integral Gauss sum for flexible Dwork setups. -/
noncomputable def gaussSumIntRec (a : ℕ) : 𝓞 R' :=
  S.gaussSumInt (p - a)

/-- Flexible reciprocal Gauss sum as a sum over `kˣ`. -/
theorem gaussSumIntRec_eq_sum_units [DecidableEq k] (a : ℕ) :
    S.gaussSumIntRec a =
      ∑ x : kˣ, (S.residueCharInt ^ (p - a)) ((x : k)) * S.psiInt ((x : k)) := by
  classical
  change _root_.gaussSum (S.residueCharInt ^ (p - a)) S.psiInt = _
  unfold _root_.gaussSum
  rw [show (Finset.univ : Finset k) = insert 0 (Finset.univ.erase 0) by
    rw [Finset.insert_erase (Finset.mem_univ 0)]]
  rw [Finset.sum_insert (Finset.notMem_erase _ _)]
  rw [MulChar.map_zero, zero_mul, zero_add]
  refine (Finset.sum_bij (fun (x : kˣ) _ => (x : k)) ?_ ?_ ?_ ?_).symm
  · intro x _; simp [Units.ne_zero]
  · intro x _ y _ hxy; exact Units.ext hxy
  · intro y hy
    rw [Finset.mem_erase] at hy
    exact ⟨Units.mk0 y hy.1, Finset.mem_univ _, rfl⟩
  · intro x _; rfl

/-- Dwork digit expansion for the conductor-flexible reciprocal Gauss sum.

This is the exact `FullTeichDworkSetup` expansion with the old pair-cyclotomic
typeclass removed; the Dwork factorization is supplied by the flexible bundle
itself. -/
theorem gaussSumIntRec_dwork_expansion [DecidableEq k]
    (a N : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumIntRec a -
        (∑ m ∈ multiIndexLE S.f N,
          (∏ i : Fin S.f, S.dworkCoeff N (m i)) *
          (∑ x : kˣ,
            S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
            S.teichUnitFullVal (S.traceScale * x) ^ multiIndexValue ℓ m)) ∈
      S.Q ^ (N + 1) := by
  classical
  have h_lhs : S.gaussSumIntRec a =
      ∑ x : kˣ,
        S.teichUnitFullVal x ^ ((p - a) * S.stickD) * S.psiInt ((x : k)) := by
    rw [S.gaussSumIntRec_eq_sum_units a]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    have h :=
      ConductorFlexibleFullTeichStickelbergerSetup.residueCharInt_rec_eq_teichUnitFull_pow_stickD
        S.toConductorFlexibleFullTeichStickelbergerSetup a ha₁ ha₂ x
    rw [MulChar.pow_apply_coe]
    change S.residueCharInt ((x : k)) ^ (p - a) =
      S.teichUnitFullVal x ^ ((p - a) * S.stickD)
    exact h
  rw [h_lhs]
  have h_psi : ∀ x : kˣ,
      S.psiInt ((x : k)) -
        (∑ m ∈ multiIndexLE S.f N,
          (∏ i : Fin S.f, S.dworkCoeff N (m i)) *
          ((S.teichUnitFull (S.traceScale * x) : 𝓞 R') ^
            multiIndexValue ℓ m)) ∈ S.Q ^ (N + 1) :=
    fun x => S.psi_dwork_factorization N x
  have h_split : ∀ x : kˣ,
      S.teichUnitFullVal x ^ ((p - a) * S.stickD) * S.psiInt ((x : k)) =
        S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
          (∑ m ∈ multiIndexLE S.f N,
            (∏ i : Fin S.f, S.dworkCoeff N (m i)) *
            ((S.teichUnitFull (S.traceScale * x) : 𝓞 R') ^
              multiIndexValue ℓ m)) +
        S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
          (S.psiInt ((x : k)) -
            (∑ m ∈ multiIndexLE S.f N,
              (∏ i : Fin S.f, S.dworkCoeff N (m i)) *
              ((S.teichUnitFull (S.traceScale * x) : 𝓞 R') ^
                multiIndexValue ℓ m))) := by
    intro x
    ring
  rw [Finset.sum_congr rfl fun x _ => h_split x]
  rw [Finset.sum_add_distrib]
  have h_error_mem :
      (∑ x : kˣ,
        S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
          (S.psiInt ((x : k)) -
            (∑ m ∈ multiIndexLE S.f N,
              (∏ i : Fin S.f, S.dworkCoeff N (m i)) *
              ((S.teichUnitFull (S.traceScale * x) : 𝓞 R') ^
                multiIndexValue ℓ m)))) ∈ S.Q ^ (N + 1) := by
    refine Ideal.sum_mem _ fun x _ => ?_
    exact Ideal.mul_mem_left _ _ (h_psi x)
  have h_swap :
      (∑ x : kˣ,
        S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
        (∑ m ∈ multiIndexLE S.f N,
          (∏ i : Fin S.f, S.dworkCoeff N (m i)) *
          ((S.teichUnitFull (S.traceScale * x) : 𝓞 R') ^
            multiIndexValue ℓ m))) =
      (∑ m ∈ multiIndexLE S.f N,
        (∏ i : Fin S.f, S.dworkCoeff N (m i)) *
        (∑ x : kˣ,
          S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
          S.teichUnitFullVal (S.traceScale * x) ^ multiIndexValue ℓ m)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    refine Finset.sum_congr rfl fun x _ => ?_
    change S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
        ((∏ i : Fin S.f, S.dworkCoeff N (m i)) *
          S.teichUnitFullVal (S.traceScale * x) ^ multiIndexValue ℓ m) =
      (∏ i : Fin S.f, S.dworkCoeff N (m i)) *
        (S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
          S.teichUnitFullVal (S.traceScale * x) ^ multiIndexValue ℓ m)
    ring
  rw [h_swap, add_sub_cancel_left]
  exact h_error_mem

end ConductorFlexibleFullTeichDworkSetup

end Furtwaengler

end BernoulliRegular

end

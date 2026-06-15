module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.MultiIndexCarry

/-!
# Dwork assembly for the reciprocal Stickelberger congruence

This file replaces the deprecated denominator-cleared digit-vector assembly
with the corrected Dwork multi-index expansion.  The Dwork expansion ranges
over all multi-indices, and `MultiIndexCarry` supplies the bridge from those
multi-indices to the minimal-weight digit-vector survivor lemmas.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

/-- Product membership in an ideal power with exponent the sum of local
orders. -/
theorem prod_mem_pow_sum_of_mem {ι A : Type*} [CommRing A]
    (I : Ideal A) (s : Finset ι) (w : ι → ℕ) (F : ι → A)
    (hF : ∀ i ∈ s, F i ∈ I ^ w i) :
    (∏ i ∈ s, F i) ∈ I ^ (∑ i ∈ s, w i) := by
  classical
  revert hF
  refine Finset.induction_on s ?base ?step
  · intro hF
    simp
  · intro a s ha ih hF
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have htail : (∏ i ∈ s, F i) ∈ I ^ (∑ i ∈ s, w i) :=
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have hmul := Ideal.mul_mem_mul (hF a (Finset.mem_insert_self a s)) htail
    simpa [pow_add] using hmul

/-- If each factor is congruent one ideal-power order beyond its own
valuation, then the products are congruent one order beyond the total
valuation. -/
theorem prod_sub_prod_mem_pow_sum_succ {ι A : Type*} [CommRing A]
    (I : Ideal A) (s : Finset ι) (w : ι → ℕ) (F G : ι → A)
    (hF : ∀ i ∈ s, F i ∈ I ^ w i)
    (hG : ∀ i ∈ s, G i ∈ I ^ w i)
    (hFG : ∀ i ∈ s, F i - G i ∈ I ^ (w i + 1)) :
    (∏ i ∈ s, F i) - (∏ i ∈ s, G i) ∈
      I ^ ((∑ i ∈ s, w i) + 1) := by
  classical
  revert hF hG hFG
  refine Finset.induction_on s ?base ?step
  · intro hF hG hFG
    simp
  · intro a s ha ih hF hG hFG
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have htail_diff :
        (∏ i ∈ s, F i) - (∏ i ∈ s, G i) ∈
          I ^ ((∑ i ∈ s, w i) + 1) :=
      ih
        (fun i hi => hF i (Finset.mem_insert_of_mem hi))
        (fun i hi => hG i (Finset.mem_insert_of_mem hi))
        (fun i hi => hFG i (Finset.mem_insert_of_mem hi))
    have htail_G :
        (∏ i ∈ s, G i) ∈ I ^ (∑ i ∈ s, w i) :=
      prod_mem_pow_sum_of_mem I s w G
        (fun i hi => hG i (Finset.mem_insert_of_mem hi))
    have hterm₁ :
        F a * ((∏ i ∈ s, F i) - (∏ i ∈ s, G i)) ∈
          I ^ (w a + (∑ i ∈ s, w i) + 1) := by
      have hmul :=
        Ideal.mul_mem_mul (hF a (Finset.mem_insert_self a s)) htail_diff
      simpa [pow_add, Nat.add_assoc] using hmul
    have hterm₂_raw :
        (F a - G a) * (∏ i ∈ s, G i) ∈
          I ^ ((w a + 1) + (∑ i ∈ s, w i)) := by
      have hmul :=
        Ideal.mul_mem_mul (hFG a (Finset.mem_insert_self a s)) htail_G
      simpa [pow_add] using hmul
    have hterm₂ :
        (F a - G a) * (∏ i ∈ s, G i) ∈
          I ^ (w a + (∑ i ∈ s, w i) + 1) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hterm₂_raw
    have hsum := Ideal.add_mem _ hterm₁ hterm₂
    have hsplit :
        F a * (∏ i ∈ s, F i) - G a * (∏ i ∈ s, G i) =
          F a * ((∏ i ∈ s, F i) - (∏ i ∈ s, G i)) +
            (F a - G a) * (∏ i ∈ s, G i) := by
      ring
    rw [hsplit]
    simpa [Nat.add_assoc] using hsum

/-- A digit-vector entry is bounded by the total digit weight. -/
theorem digitVec_entry_le_weight {ℓ f : ℕ} (m : digitVec ℓ f) (i : Fin f) :
    m.1 i ≤ digitWeight m := by
  unfold digitWeight
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (m.1 j)) (Finset.mem_univ i)

namespace FullTeichDworkSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : FullTeichDworkSetup ℓ p k K R')

/-- The standard multi-index contributing the Dwork leading term. -/
def dworkLeadingMultiIndex (a : ℕ) : Fin S.f → ℕ :=
  (S.toTraceFormStickelbergerSetup.standardDigitVec (a * S.stickD)).1

/-- The product of factorials used to normalize the Dwork leading
coefficient to `π^s`. -/
def dworkLeadingFactorialProd (a : ℕ) : 𝓞 R' :=
  ∏ i : Fin S.f, (Nat.factorial (S.dworkLeadingMultiIndex a i) : 𝓞 R')

/-- The unit factor in the Dwork leading term. -/
def dworkLeadingUnit (a : ℕ) : 𝓞 R' :=
  ((Fintype.card k - 1 : ℕ) : 𝓞 R') *
    S.teichUnitFullVal S.traceScale ^ (a * S.stickD)

/-- The Dwork leading unit is not in `Q`. -/
theorem dworkLeadingUnit_not_mem_Q
    (a : ℕ) (_ha₁ : 1 ≤ a) (_ha₂ : a ≤ p - 1) :
    S.dworkLeadingUnit a ∉ S.Q := by
  classical
  unfold dworkLeadingUnit
  intro hmem
  rcases (Ideal.IsPrime.mem_or_mem (hI := inferInstance)) hmem with hcard | hpow
  · exact S.toTraceFormStickelbergerSetup.natCast_card_k_sub_one_not_mem_Q hcard
  · have h_unit : S.teichUnitFullVal S.traceScale ∉ S.Q :=
      S.toFullTeichStickelbergerSetup.teichUnitFullVal_not_mem_Q S.traceScale
    have h_base : S.teichUnitFullVal S.traceScale ∈ S.Q :=
      Ideal.IsPrime.mem_of_pow_mem (hI := inferInstance) _ hpow
    exact h_unit h_base

/-- Factorial-normalized Dwork leading coefficient is congruent to
`π^s` modulo `Q^(s+1)`. -/
theorem dworkLeadingFactorialProd_mul_coeffProd_sub_pi_pow_mem
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.dworkLeadingFactorialProd a *
        (∏ i : Fin S.f, S.dworkCoeff (S.stickOrd a) (S.dworkLeadingMultiIndex a i)) -
          S.π ^ S.stickOrd a ∈ S.Q ^ (S.stickOrd a + 1) := by
  classical
  set m₀ : digitVec ℓ S.f :=
    S.toTraceFormStickelbergerSetup.standardDigitVec (a * S.stickD) with hm₀_def
  have hm₀_wt : digitWeight m₀ = S.stickOrd a := by
    simpa [hm₀_def] using
      S.toTraceFormStickelbergerSetup.digitWeight_standardDigitVec_eq_stickOrd
        a ha₁ ha₂
  have hprod :=
    prod_sub_prod_mem_pow_sum_succ (I := S.Q) (s := Finset.univ)
      (w := fun i : Fin S.f => m₀.1 i)
      (F := fun i : Fin S.f =>
        (Nat.factorial (m₀.1 i) : 𝓞 R') * S.dworkCoeff (S.stickOrd a) (m₀.1 i))
      (G := fun i : Fin S.f => S.π ^ (m₀.1 i))
      (fun i _ =>
        Ideal.mul_mem_left _ _ (S.dworkCoeff_mem_Q_pow_to_thm (S.stickOrd a) (m₀.1 i)))
      (fun i _ => Ideal.pow_mem_pow S.π_mem_Q (m₀.1 i))
      (fun i _ => by
        have hi := digitVec_entry_le_weight m₀ i
        exact S.dworkCoeff_lt_ell_leading_to_thm (S.stickOrd a) (m₀.1 i)
          (by simpa [hm₀_wt] using hi) (m₀.2 i))
  have hsum_eq : (∑ i : Fin S.f, m₀.1 i) = S.stickOrd a := by
    simpa [digitWeight] using hm₀_wt
  have hprod' :
      (∏ i : Fin S.f,
          (Nat.factorial (m₀.1 i) : 𝓞 R') * S.dworkCoeff (S.stickOrd a) (m₀.1 i)) -
        (∏ i : Fin S.f, S.π ^ (m₀.1 i)) ∈
          S.Q ^ (S.stickOrd a + 1) := by
    simpa [hsum_eq] using hprod
  have hpi_prod : (∏ i : Fin S.f, S.π ^ (m₀.1 i)) = S.π ^ S.stickOrd a := by
    rw [Finset.prod_pow_eq_pow_sum, hsum_eq]
  rw [hpi_prod] at hprod'
  simpa [dworkLeadingFactorialProd, dworkLeadingMultiIndex, hm₀_def,
    Finset.prod_mul_distrib] using hprod'

/-- **Dwork replacement for L2c3d-7.** The reciprocal-convention integral
Gauss sum lies in `Q^{s_ℓ(a · d)}`. -/
theorem gaussSumIntRec_mem_Q_pow_stickOrd_dwork
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumIntRec a ∈ S.Q ^ S.stickOrd a := by
  classical
  set s := S.stickOrd a with hs_def
  rcases Nat.eq_zero_or_pos s with h_zero | h_pos
  · rw [h_zero, pow_zero, Ideal.one_eq_top]
    exact (Submodule.mem_top : S.gaussSumIntRec a ∈ (⊤ : Ideal (𝓞 R')))
  · set N := s - 1 with hN_def
    have hN_succ : N + 1 = s := by omega
    have h_diff := S.gaussSumIntRec_dwork_expansion a N ha₁ ha₂
    rw [hN_succ] at h_diff
    have h_sum_zero :
        (∑ m ∈ multiIndexLE S.f N,
          (∏ i : Fin S.f, S.dworkCoeff N (m i)) *
          (∑ x : kˣ,
            S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
            S.teichUnitFullVal (S.traceScale * x) ^ multiIndexValue ℓ m)) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hm_weight_le : multiIndexWeight m ≤ N := ((mem_multiIndexLE m).mp hm).2
      have hm_weight_lt : multiIndexWeight m < s := by omega
      have h_no_surv :
          ¬ (Fintype.card k - 1) ∣
              ((p - a) * S.stickD + multiIndexValue ℓ m) :=
        S.toFullTeichStickelbergerSetup.no_survivor_multiIndex_of_weight_lt_stickOrd
          a ha₁ ha₂ m (by simpa [hs_def] using hm_weight_lt)
      have h_inner_zero :
          (∑ x : kˣ,
            S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
            S.teichUnitFullVal (S.traceScale * x) ^ multiIndexValue ℓ m) = 0 := by
        rw [S.toFullTeichStickelbergerSetup.teichUnitFull_innerSum_eval
          ((p - a) * S.stickD) (multiIndexValue ℓ m) S.traceScale]
        exact if_neg h_no_surv
      rw [h_inner_zero, mul_zero]
    rw [h_sum_zero] at h_diff
    simpa [sub_zero] using h_diff

/-- Dwork leading congruence before factorial normalization. -/
theorem gaussSumIntRec_sub_dworkLeadingTerm_mem_Q_pow_succ
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumIntRec a -
        (∏ i : Fin S.f, S.dworkCoeff (S.stickOrd a) (S.dworkLeadingMultiIndex a i)) *
          S.dworkLeadingUnit a ∈ S.Q ^ (S.stickOrd a + 1) := by
  classical
  set s := S.stickOrd a with hs_def
  set m₀v : digitVec ℓ S.f :=
    S.toTraceFormStickelbergerSetup.standardDigitVec (a * S.stickD) with hm₀v_def
  set m₀ : Fin S.f → ℕ := m₀v.1 with hm₀_def
  have hm₀_wt_digit : digitWeight m₀v = s := by
    rw [hs_def]
    simpa [hm₀v_def] using
      S.toTraceFormStickelbergerSetup.digitWeight_standardDigitVec_eq_stickOrd
        a ha₁ ha₂
  have hm₀_wt : multiIndexWeight m₀ = s := by
    simpa [m₀, multiIndexWeight, digitWeight] using hm₀_wt_digit
  have hm₀_val_digit : digitValue m₀v = a * S.stickD := by
    simpa [hm₀v_def] using
      S.toTraceFormStickelbergerSetup.digitValue_standardDigitVec_eq a ha₁ ha₂
  have hm₀_val : multiIndexValue ℓ m₀ = a * S.stickD := by
    simpa [m₀, multiIndexValue, digitValue] using hm₀_val_digit
  have hm₀_mem : m₀ ∈ multiIndexLE S.f s := by
    refine (mem_multiIndexLE m₀).mpr ⟨?_, ?_⟩
    · intro i
      have hi := digitVec_entry_le_weight m₀v i
      simpa [m₀, hm₀_wt_digit] using hi
    · simp [hm₀_wt]
  have h_diff := S.gaussSumIntRec_dwork_expansion a s ha₁ ha₂
  have h_sum_eq :
      (∑ m ∈ multiIndexLE S.f s,
        (∏ i : Fin S.f, S.dworkCoeff s (m i)) *
        (∑ x : kˣ,
          S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
          S.teichUnitFullVal (S.traceScale * x) ^ multiIndexValue ℓ m)) =
        (∏ i : Fin S.f, S.dworkCoeff s (m₀ i)) * S.dworkLeadingUnit a := by
    rw [← Finset.sum_erase_add _ _ hm₀_mem]
    have h_others_zero :
        (∑ m ∈ (multiIndexLE S.f s).erase m₀,
          (∏ i : Fin S.f, S.dworkCoeff s (m i)) *
          (∑ x : kˣ,
            S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
            S.teichUnitFullVal (S.traceScale * x) ^ multiIndexValue ℓ m)) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm_erase
      rw [Finset.mem_erase] at hm_erase
      obtain ⟨hm_ne, hm_in⟩ := hm_erase
      have hm_weight_le : multiIndexWeight m ≤ s := ((mem_multiIndexLE m).mp hm_in).2
      have h_inner_zero :
          (∑ x : kˣ,
            S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
            S.teichUnitFullVal (S.traceScale * x) ^ multiIndexValue ℓ m) = 0 := by
        rw [S.toFullTeichStickelbergerSetup.teichUnitFull_innerSum_eval
          ((p - a) * S.stickD) (multiIndexValue ℓ m) S.traceScale]
        rcases lt_or_eq_of_le hm_weight_le with hm_lt | hm_eq
        · have h_no_surv :
              ¬ (Fintype.card k - 1) ∣
                  ((p - a) * S.stickD + multiIndexValue ℓ m) :=
            S.toFullTeichStickelbergerSetup.no_survivor_multiIndex_of_weight_lt_stickOrd
              a ha₁ ha₂ m (by simpa [hs_def] using hm_lt)
          exact if_neg h_no_surv
        · have h_no_surv :
              ¬ (Fintype.card k - 1) ∣
                  ((p - a) * S.stickD + multiIndexValue ℓ m) := by
            intro hdiv
            obtain ⟨_, hm_bounded, hm_std⟩ :=
              S.toFullTeichStickelbergerSetup.unique_multiIndex_survivor_at_stickOrd
                a ha₁ ha₂ m (by simpa [hs_def] using hm_eq) hdiv
            have hm_eq_m₀ : m = m₀ := by
              have hval := congrArg (fun v : digitVec ℓ S.f => v.1) hm_std
              simpa [m₀, hm₀v_def] using hval
            exact hm_ne hm_eq_m₀
          exact if_neg h_no_surv
      rw [h_inner_zero, mul_zero]
    rw [h_others_zero, zero_add]
    have h_dvd_m₀ :
        (Fintype.card k - 1) ∣
          ((p - a) * S.stickD + multiIndexValue ℓ m₀) := by
      rw [hm₀_val]
      have hpd : p * S.stickD = Fintype.card k - 1 :=
        S.toTraceFormStickelbergerSetup.p_mul_stickD_eq_card_sub_one
      have heq :
          (p - a) * S.stickD + a * S.stickD = p * S.stickD := by
        rw [show (p - a) * S.stickD + a * S.stickD =
            ((p - a) + a) * S.stickD by ring]
        congr 1
        omega
      rw [heq, hpd]
    have h_inner_m₀ :
        (∑ x : kˣ,
          S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
          S.teichUnitFullVal (S.traceScale * x) ^ multiIndexValue ℓ m₀) =
            S.dworkLeadingUnit a := by
      rw [S.toFullTeichStickelbergerSetup.teichUnitFull_innerSum_eval
        ((p - a) * S.stickD) (multiIndexValue ℓ m₀) S.traceScale]
      rw [if_pos h_dvd_m₀]
      unfold dworkLeadingUnit
      rw [hm₀_val]
      have hpos : 1 ≤ Fintype.card k := Fintype.card_pos
      rw [Nat.cast_sub hpos, Nat.cast_one]
    rw [h_inner_m₀]
  rw [h_sum_eq] at h_diff
  simpa [dworkLeadingMultiIndex, hm₀v_def, hm₀_def] using h_diff

/-- Factorial-normalized Dwork leading congruence.  This is the form used
for non-degeneracy, because the normalized coefficient is congruent to
`π^s`. -/
theorem dworkLeadingFactorialProd_mul_gaussSumIntRec_sub_unit_pi_pow_mem
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.dworkLeadingFactorialProd a * S.gaussSumIntRec a -
        S.dworkLeadingUnit a * S.π ^ S.stickOrd a ∈
      S.Q ^ (S.stickOrd a + 1) := by
  classical
  have hG := S.gaussSumIntRec_sub_dworkLeadingTerm_mem_Q_pow_succ a ha₁ ha₂
  have hGmul_raw :
      S.dworkLeadingFactorialProd a *
          (S.gaussSumIntRec a -
            (∏ i : Fin S.f, S.dworkCoeff (S.stickOrd a) (S.dworkLeadingMultiIndex a i)) *
              S.dworkLeadingUnit a) ∈
        S.Q ^ (S.stickOrd a + 1) :=
    Ideal.mul_mem_left _ _ hG
  have hGmul :
      S.dworkLeadingFactorialProd a * S.gaussSumIntRec a -
          S.dworkLeadingFactorialProd a *
            ((∏ i : Fin S.f,
                S.dworkCoeff (S.stickOrd a) (S.dworkLeadingMultiIndex a i)) *
              S.dworkLeadingUnit a) ∈
        S.Q ^ (S.stickOrd a + 1) := by
    convert hGmul_raw using 1
    ring
  have hC := S.dworkLeadingFactorialProd_mul_coeffProd_sub_pi_pow_mem a ha₁ ha₂
  have hCmul :
      (S.dworkLeadingFactorialProd a *
          (∏ i : Fin S.f, S.dworkCoeff (S.stickOrd a) (S.dworkLeadingMultiIndex a i)) -
            S.π ^ S.stickOrd a) * S.dworkLeadingUnit a ∈
        S.Q ^ (S.stickOrd a + 1) :=
    Ideal.mul_mem_right _ _ hC
  have hsum := Ideal.add_mem _ hGmul hCmul
  convert hsum using 1
  ring

/-- **Dwork replacement for L2c3e-5.** The reciprocal-convention integral
Gauss sum is not in the next power `Q^(s+1)`. -/
theorem gaussSumIntRec_not_mem_Q_pow_stickOrd_succ_dwork
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumIntRec a ∉ S.Q ^ (S.stickOrd a + 1) := by
  classical
  intro h_mem
  have h_fact_G_mem :
      S.dworkLeadingFactorialProd a * S.gaussSumIntRec a ∈
        S.Q ^ (S.stickOrd a + 1) :=
    Ideal.mul_mem_left _ _ h_mem
  have h_diff :=
    S.dworkLeadingFactorialProd_mul_gaussSumIntRec_sub_unit_pi_pow_mem a ha₁ ha₂
  have h_unit_pi_mem :
      S.dworkLeadingUnit a * S.π ^ S.stickOrd a ∈
        S.Q ^ (S.stickOrd a + 1) := by
    have htmp := Ideal.sub_mem _ h_fact_G_mem h_diff
    convert htmp using 1
    ring
  have h_unit_notQ : S.dworkLeadingUnit a ∉ S.Q :=
    S.dworkLeadingUnit_not_mem_Q a ha₁ ha₂
  exact S.toTraceFormStickelbergerSetup.unit_mul_pi_pow_not_mem_Q_pow_succ
    S.toTraceFormStickelbergerSetup.pi_ne_zero
    S.toTraceFormStickelbergerSetup.pi_not_mem_Q_sq
    (S.dworkLeadingUnit a) h_unit_notQ (S.stickOrd a) h_unit_pi_mem

/-- Dwork exact reciprocal digit-sum Stickelberger congruence. -/
theorem gaussSumIntRec_qadic_ord_at_prime_dwork
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumIntRec a ∈ S.Q ^ S.stickOrd a ∧
      S.gaussSumIntRec a ∉ S.Q ^ (S.stickOrd a + 1) :=
  ⟨S.gaussSumIntRec_mem_Q_pow_stickOrd_dwork a ha₁ ha₂,
   S.gaussSumIntRec_not_mem_Q_pow_stickOrd_succ_dwork a ha₁ ha₂⟩

/-- Ordinary-character exact order, exported with the complementary
digit-sum index dictated by the stored ordinary character convention. -/
theorem gaussSumInt_qadic_ord_at_prime_ord_dwork
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumInt a ∈ S.Q ^ S.stickOrdOrd a ∧
      S.gaussSumInt a ∉ S.Q ^ (S.stickOrdOrd a + 1) := by
  have h₁ : 1 ≤ p - a := by omega
  have h₂ : p - a ≤ p - 1 := by omega
  have hrec := S.gaussSumIntRec_qadic_ord_at_prime_dwork (p - a) h₁ h₂
  unfold TraceFormStickelbergerSetup.gaussSumIntRec at hrec
  unfold TraceFormStickelbergerSetup.stickOrdOrd
  rwa [show p - (p - a) = a by omega] at hrec

end FullTeichDworkSetup

namespace ConductorFlexibleTraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (S : ConductorFlexibleTraceFormStickelbergerSetup ℓ p k K R')

/-- The flexible selected prime `Q` is nonzero. -/
theorem Q_ne_bot_for_dwork : S.Q ≠ ⊥ := by
  intro h
  have h_in : (ℓ : 𝓞 R') ∈ (⊥ : Ideal (𝓞 R')) := h ▸ S.hQ
  rw [Ideal.mem_bot] at h_in
  have : (ℓ : 𝓞 R') ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  exact this h_in

/-- The integer `#k - 1` is a `Q`-unit in the flexible setup. -/
theorem natCast_card_k_sub_one_not_mem_Q_for_dwork :
    ((Fintype.card k - 1 : ℕ) : 𝓞 R') ∉ S.Q := by
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  intro hmem
  have hres : S.residueMap ((Fintype.card k - 1 : ℕ) : 𝓞 R') = 0 :=
    (S.concrete.mem_Q_iff_residueMap_eq_zero _).1
      (by simpa [ConductorFlexibleTraceFormStickelbergerSetup.concrete] using hmem)
  rw [map_natCast] at hres
  have hℓ_not_dvd_card_sub_one : ¬ ℓ ∣ Fintype.card k - 1 := by
    intro hdvd
    have hf_pos : 0 < S.f := by
      by_contra hf_not
      have hf0 : S.f = 0 := by omega
      have hcard_one : Fintype.card k = 1 := by
        rw [S.card_k, hf0, pow_zero]
      have hcard_gt : 1 < Fintype.card k := Fintype.one_lt_card
      omega
    have hℓ_dvd_card : ℓ ∣ Fintype.card k := by
      rw [S.card_k]
      exact dvd_pow_self ℓ hf_pos.ne'
    have hcard_pos : 1 ≤ Fintype.card k := Fintype.card_pos
    have hone : ℓ ∣ 1 := by
      have h := Nat.dvd_sub hℓ_dvd_card hdvd
      rwa [Nat.sub_sub_self hcard_pos] at h
    exact (Fact.out : Nat.Prime ℓ).one_lt.ne' (Nat.dvd_one.mp hone)
  exact hℓ_not_dvd_card_sub_one
    ((CharP.cast_eq_zero_iff k ℓ (Fintype.card k - 1)).1 hres)

/-- The flexible uniformizer candidate `π = ζ_ℓ - 1` is nonzero. -/
theorem pi_ne_zero_for_dwork : S.π ≠ 0 := by
  rw [S.hπ]
  intro hc
  have h1 : S.zeta_ell_int = 1 := by linear_combination hc
  have h_prim := S.concrete.zeta_ell_int_isPrimitiveRoot
  have h_ord_one : S.zeta_ell_int ^ 1 = 1 := by rw [pow_one]; exact h1
  have h_ord_dvd : ℓ ∣ 1 := h_prim.dvd_of_pow_eq_one 1 h_ord_one
  have : ℓ ≤ 1 := Nat.le_of_dvd zero_lt_one h_ord_dvd
  have hℓ_two : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
  omega

/-- Local non-degeneracy of powers of the flexible uniformizer candidate. -/
theorem pi_pow_not_mem_Q_pow_succ_of_not_mem_sq_for_dwork
    (h_pi_ne_zero : S.π ≠ 0) (h_pi_nondeg : S.π ∉ S.Q ^ 2) (s : ℕ) :
    S.π ^ s ∉ S.Q ^ (s + 1) := by
  classical
  intro h_in
  set I : Ideal (𝓞 R') := Ideal.span ({S.π} : Set (𝓞 R')) with hI_def
  have h_span_pi_pow : Ideal.span ({S.π ^ s} : Set (𝓞 R')) = I ^ s := by
    rw [hI_def, Ideal.span_singleton_pow]
  have h_pow_le : I ^ s ≤ S.Q ^ (s + 1) := by
    rw [← h_span_pi_pow]
    exact (Ideal.span_singleton_le_iff_mem _).mpr h_in
  have hI_ne_bot : I ≠ ⊥ := by
    rw [hI_def, Ne, Ideal.span_singleton_eq_bot]
    exact h_pi_ne_zero
  have hI_pow_ne_bot : I ^ s ≠ ⊥ := pow_ne_zero s hI_ne_bot
  have hI_le_Q : I ≤ S.Q :=
    (Ideal.span_singleton_le_iff_mem _).mpr S.concrete.π_mem_Q
  have hI_not_le_Qsq : ¬ I ≤ S.Q ^ 2 := fun h =>
    h_pi_nondeg <| h <| Ideal.mem_span_singleton_self S.π
  have h_count_I : Multiset.count S.Q
      (UniqueFactorizationMonoid.normalizedFactors I) = 1 := by
    have h_le_one : I ≤ S.Q ^ 1 := by simpa using hI_le_Q
    exact Ideal.count_normalizedFactors_eq h_le_one hI_not_le_Qsq
  have h_count_Is : Multiset.count S.Q
      (UniqueFactorizationMonoid.normalizedFactors (I ^ s)) = s := by
    rw [UniqueFactorizationMonoid.normalizedFactors_pow,
      Multiset.count_nsmul, h_count_I, mul_one]
  have hQ_irr : Irreducible S.Q := by
    have hQp : Prime S.Q := Ideal.prime_of_isPrime S.Q_ne_bot_for_dwork S.hQ_prime
    exact hQp.irreducible
  have h_count_Qpow : s + 1 ≤ Multiset.count S.Q
      (UniqueFactorizationMonoid.normalizedFactors (S.Q ^ (s + 1))) := by
    rw [UniqueFactorizationMonoid.normalizedFactors_pow,
      Multiset.count_nsmul]
    have h1 : 1 ≤ Multiset.count S.Q
        (UniqueFactorizationMonoid.normalizedFactors S.Q) := by
      rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hQ_irr,
        normalize_eq, Multiset.count_singleton_self]
    nlinarith
  have hcount := Ideal.count_le_of_ideal_ge h_pow_le hI_pow_ne_bot S.Q
  omega

/-- Unit times the flexible uniformizer power is not in the next `Q`-power. -/
theorem unit_mul_pi_pow_not_mem_Q_pow_succ_for_dwork
    (h_pi_ne_zero : S.π ≠ 0) (h_pi_nondeg : S.π ∉ S.Q ^ 2)
    (u : 𝓞 R') (hu : u ∉ S.Q) (s : ℕ) :
    u * S.π ^ s ∉ S.Q ^ (s + 1) := by
  intro h_in
  rcases Ideal.IsPrime.mul_mem_pow S.Q h_in with h_u | h_pi_pow
  · exact hu h_u
  · exact S.pi_pow_not_mem_Q_pow_succ_of_not_mem_sq_for_dwork
      h_pi_ne_zero h_pi_nondeg s h_pi_pow

end ConductorFlexibleTraceFormStickelbergerSetup

namespace ConductorFlexibleFullTeichDworkSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (S : ConductorFlexibleFullTeichDworkSetup ℓ p k K R')

/-- The standard multi-index contributing the flexible Dwork leading term. -/
def dworkLeadingMultiIndex (a : ℕ) : Fin S.f → ℕ :=
  (S.toConductorFlexibleTraceFormStickelbergerSetup.standardDigitVec (a * S.stickD)).1

/-- The product of factorials normalizing the flexible Dwork leading term. -/
def dworkLeadingFactorialProd (a : ℕ) : 𝓞 R' :=
  ∏ i : Fin S.f, (Nat.factorial (S.dworkLeadingMultiIndex a i) : 𝓞 R')

/-- The flexible Dwork leading unit. -/
def dworkLeadingUnit (a : ℕ) : 𝓞 R' :=
  ((Fintype.card k - 1 : ℕ) : 𝓞 R') *
    S.teichUnitFullVal S.traceScale ^ (a * S.stickD)

/-- The flexible Dwork leading unit is not in `Q`. -/
theorem dworkLeadingUnit_not_mem_Q
    (a : ℕ) (_ha₁ : 1 ≤ a) (_ha₂ : a ≤ p - 1) :
    S.dworkLeadingUnit a ∉ S.Q := by
  classical
  unfold dworkLeadingUnit
  intro hmem
  rcases (Ideal.IsPrime.mem_or_mem (hI := inferInstance)) hmem with hcard | hpow
  · exact
      S.toConductorFlexibleTraceFormStickelbergerSetup.natCast_card_k_sub_one_not_mem_Q_for_dwork
        hcard
  · have h_unit : S.teichUnitFullVal S.traceScale ∉ S.Q :=
      S.toConductorFlexibleFullTeichStickelbergerSetup.teichUnitFullVal_not_mem_Q
        S.traceScale
    have h_base : S.teichUnitFullVal S.traceScale ∈ S.Q :=
      Ideal.IsPrime.mem_of_pow_mem (hI := inferInstance) _ hpow
    exact h_unit h_base

/-- Factorial-normalized flexible Dwork leading coefficient is congruent to
`π^s` modulo `Q^(s+1)`. -/
theorem dworkLeadingFactorialProd_mul_coeffProd_sub_pi_pow_mem
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.dworkLeadingFactorialProd a *
        (∏ i : Fin S.f, S.dworkCoeff (S.stickOrd a) (S.dworkLeadingMultiIndex a i)) -
          S.π ^ S.stickOrd a ∈ S.Q ^ (S.stickOrd a + 1) := by
  classical
  set m₀ : digitVec ℓ S.f :=
    S.toConductorFlexibleTraceFormStickelbergerSetup.standardDigitVec (a * S.stickD)
      with hm₀_def
  have hm₀_wt : digitWeight m₀ = S.stickOrd a := by
    simpa [hm₀_def] using
      S.toConductorFlexibleTraceFormStickelbergerSetup.digitWeight_standardDigitVec_eq_stickOrd
        a ha₁ ha₂
  have hprod :=
    prod_sub_prod_mem_pow_sum_succ (I := S.Q) (s := Finset.univ)
      (w := fun i : Fin S.f => m₀.1 i)
      (F := fun i : Fin S.f =>
        (Nat.factorial (m₀.1 i) : 𝓞 R') * S.dworkCoeff (S.stickOrd a) (m₀.1 i))
      (G := fun i : Fin S.f => S.π ^ (m₀.1 i))
      (fun i _ =>
        Ideal.mul_mem_left _ _ (S.dworkCoeff_mem_Q_pow_to_thm (S.stickOrd a) (m₀.1 i)))
      (fun i _ => Ideal.pow_mem_pow S.concrete.π_mem_Q (m₀.1 i))
      (fun i _ => by
        have hi := digitVec_entry_le_weight m₀ i
        exact S.dworkCoeff_lt_ell_leading_to_thm (S.stickOrd a) (m₀.1 i)
          (by simpa [hm₀_wt] using hi) (m₀.2 i))
  have hsum_eq : (∑ i : Fin S.f, m₀.1 i) = S.stickOrd a := by
    simpa [digitWeight] using hm₀_wt
  have hprod' :
      (∏ i : Fin S.f,
          (Nat.factorial (m₀.1 i) : 𝓞 R') * S.dworkCoeff (S.stickOrd a) (m₀.1 i)) -
        (∏ i : Fin S.f, S.π ^ (m₀.1 i)) ∈
          S.Q ^ (S.stickOrd a + 1) := by
    simpa [hsum_eq] using hprod
  have hpi_prod : (∏ i : Fin S.f, S.π ^ (m₀.1 i)) = S.π ^ S.stickOrd a := by
    rw [Finset.prod_pow_eq_pow_sum, hsum_eq]
  rw [hpi_prod] at hprod'
  simpa [dworkLeadingFactorialProd, dworkLeadingMultiIndex, hm₀_def,
    Finset.prod_mul_distrib] using hprod'

/-- The flexible reciprocal-convention integral Gauss sum lies in
`Q^{s_ℓ(a · d)}`. -/
theorem gaussSumIntRec_mem_Q_pow_stickOrd_dwork
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumIntRec a ∈ S.Q ^ S.stickOrd a := by
  classical
  set s := S.stickOrd a with hs_def
  rcases Nat.eq_zero_or_pos s with h_zero | h_pos
  · rw [h_zero, pow_zero, Ideal.one_eq_top]
    exact (Submodule.mem_top : S.gaussSumIntRec a ∈ (⊤ : Ideal (𝓞 R')))
  · set N := s - 1 with hN_def
    have hN_succ : N + 1 = s := by omega
    have h_diff := S.gaussSumIntRec_dwork_expansion a N ha₁ ha₂
    rw [hN_succ] at h_diff
    have h_sum_zero :
        (∑ m ∈ multiIndexLE S.f N,
          (∏ i : Fin S.f, S.dworkCoeff N (m i)) *
          (∑ x : kˣ,
            S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
            S.teichUnitFullVal (S.traceScale * x) ^ multiIndexValue ℓ m)) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hm_weight_le : multiIndexWeight m ≤ N := ((mem_multiIndexLE m).mp hm).2
      have hm_weight_lt : multiIndexWeight m < s := by omega
      have h_no_surv :
          ¬ (Fintype.card k - 1) ∣
              ((p - a) * S.stickD + multiIndexValue ℓ m) := by
        let T := S.toConductorFlexibleFullTeichStickelbergerSetup
        exact T.no_survivor_multiIndex_of_weight_lt_stickOrd
          a ha₁ ha₂ m (by simpa [hs_def] using hm_weight_lt)
      have h_inner_zero :
          (∑ x : kˣ,
            S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
            S.teichUnitFullVal (S.traceScale * x) ^ multiIndexValue ℓ m) = 0 := by
        rw [S.toConductorFlexibleFullTeichStickelbergerSetup.teichUnitFull_innerSum_eval
          ((p - a) * S.stickD) (multiIndexValue ℓ m) S.traceScale]
        exact if_neg h_no_surv
      rw [h_inner_zero, mul_zero]
    rw [h_sum_zero] at h_diff
    simpa [sub_zero] using h_diff

/-- Flexible Dwork leading congruence before factorial normalization. -/
theorem gaussSumIntRec_sub_dworkLeadingTerm_mem_Q_pow_succ
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumIntRec a -
        (∏ i : Fin S.f, S.dworkCoeff (S.stickOrd a) (S.dworkLeadingMultiIndex a i)) *
          S.dworkLeadingUnit a ∈ S.Q ^ (S.stickOrd a + 1) := by
  classical
  set s := S.stickOrd a with hs_def
  set m₀v : digitVec ℓ S.f :=
    S.toConductorFlexibleTraceFormStickelbergerSetup.standardDigitVec (a * S.stickD)
      with hm₀v_def
  set m₀ : Fin S.f → ℕ := m₀v.1 with hm₀_def
  have hm₀_wt_digit : digitWeight m₀v = s := by
    rw [hs_def]
    simpa [hm₀v_def] using
      S.toConductorFlexibleTraceFormStickelbergerSetup.digitWeight_standardDigitVec_eq_stickOrd
        a ha₁ ha₂
  have hm₀_wt : multiIndexWeight m₀ = s := by
    simpa [m₀, multiIndexWeight, digitWeight] using hm₀_wt_digit
  have hm₀_val_digit : digitValue m₀v = a * S.stickD := by
    simpa [hm₀v_def] using
      S.toConductorFlexibleTraceFormStickelbergerSetup.digitValue_standardDigitVec_eq
        a ha₁ ha₂
  have hm₀_val : multiIndexValue ℓ m₀ = a * S.stickD := by
    simpa [m₀, multiIndexValue, digitValue] using hm₀_val_digit
  have hm₀_mem : m₀ ∈ multiIndexLE S.f s := by
    refine (mem_multiIndexLE m₀).mpr ⟨?_, ?_⟩
    · intro i
      have hi := digitVec_entry_le_weight m₀v i
      simpa [m₀, hm₀_wt_digit] using hi
    · simp [hm₀_wt]
  have h_diff := S.gaussSumIntRec_dwork_expansion a s ha₁ ha₂
  have h_sum_eq :
      (∑ m ∈ multiIndexLE S.f s,
        (∏ i : Fin S.f, S.dworkCoeff s (m i)) *
        (∑ x : kˣ,
          S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
          S.teichUnitFullVal (S.traceScale * x) ^ multiIndexValue ℓ m)) =
        (∏ i : Fin S.f, S.dworkCoeff s (m₀ i)) * S.dworkLeadingUnit a := by
    rw [← Finset.sum_erase_add _ _ hm₀_mem]
    have h_others_zero :
        (∑ m ∈ (multiIndexLE S.f s).erase m₀,
          (∏ i : Fin S.f, S.dworkCoeff s (m i)) *
          (∑ x : kˣ,
            S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
            S.teichUnitFullVal (S.traceScale * x) ^ multiIndexValue ℓ m)) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm_erase
      rw [Finset.mem_erase] at hm_erase
      obtain ⟨hm_ne, hm_in⟩ := hm_erase
      have hm_weight_le : multiIndexWeight m ≤ s := ((mem_multiIndexLE m).mp hm_in).2
      have h_inner_zero :
          (∑ x : kˣ,
            S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
            S.teichUnitFullVal (S.traceScale * x) ^ multiIndexValue ℓ m) = 0 := by
        rw [S.toConductorFlexibleFullTeichStickelbergerSetup.teichUnitFull_innerSum_eval
          ((p - a) * S.stickD) (multiIndexValue ℓ m) S.traceScale]
        rcases lt_or_eq_of_le hm_weight_le with hm_lt | hm_eq
        · have h_no_surv :
              ¬ (Fintype.card k - 1) ∣
                  ((p - a) * S.stickD + multiIndexValue ℓ m) := by
            let T := S.toConductorFlexibleFullTeichStickelbergerSetup
            exact T.no_survivor_multiIndex_of_weight_lt_stickOrd
              a ha₁ ha₂ m (by simpa [hs_def] using hm_lt)
          exact if_neg h_no_surv
        · have h_no_surv :
              ¬ (Fintype.card k - 1) ∣
                  ((p - a) * S.stickD + multiIndexValue ℓ m) := by
            intro hdiv
            let T := S.toConductorFlexibleFullTeichStickelbergerSetup
            obtain ⟨_, hm_bounded, hm_std⟩ :=
              T.unique_multiIndex_survivor_at_stickOrd
                a ha₁ ha₂ m (by simpa [hs_def] using hm_eq) hdiv
            have hm_eq_m₀ : m = m₀ := by
              have hval := congrArg (fun v : digitVec ℓ S.f => v.1) hm_std
              simpa [m₀, hm₀v_def] using hval
            exact hm_ne hm_eq_m₀
          exact if_neg h_no_surv
      rw [h_inner_zero, mul_zero]
    rw [h_others_zero, zero_add]
    have h_dvd_m₀ :
        (Fintype.card k - 1) ∣
          ((p - a) * S.stickD + multiIndexValue ℓ m₀) := by
      rw [hm₀_val]
      have hpd : p * S.stickD = Fintype.card k - 1 :=
        S.toConductorFlexibleTraceFormStickelbergerSetup.p_mul_stickD_eq_card_sub_one
      have heq :
          (p - a) * S.stickD + a * S.stickD = p * S.stickD := by
        rw [show (p - a) * S.stickD + a * S.stickD =
            ((p - a) + a) * S.stickD by ring]
        congr 1
        omega
      rw [heq, hpd]
    have h_inner_m₀ :
        (∑ x : kˣ,
          S.teichUnitFullVal x ^ ((p - a) * S.stickD) *
          S.teichUnitFullVal (S.traceScale * x) ^ multiIndexValue ℓ m₀) =
            S.dworkLeadingUnit a := by
      rw [S.toConductorFlexibleFullTeichStickelbergerSetup.teichUnitFull_innerSum_eval
        ((p - a) * S.stickD) (multiIndexValue ℓ m₀) S.traceScale]
      rw [if_pos h_dvd_m₀]
      unfold dworkLeadingUnit
      rw [hm₀_val]
      have hpos : 1 ≤ Fintype.card k := Fintype.card_pos
      rw [Nat.cast_sub hpos, Nat.cast_one]
    rw [h_inner_m₀]
  rw [h_sum_eq] at h_diff
  simpa [dworkLeadingMultiIndex, hm₀v_def, hm₀_def] using h_diff

/-- Factorial-normalized flexible Dwork leading congruence. -/
theorem dworkLeadingFactorialProd_mul_gaussSumIntRec_sub_unit_pi_pow_mem
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.dworkLeadingFactorialProd a * S.gaussSumIntRec a -
        S.dworkLeadingUnit a * S.π ^ S.stickOrd a ∈
      S.Q ^ (S.stickOrd a + 1) := by
  classical
  have hG := S.gaussSumIntRec_sub_dworkLeadingTerm_mem_Q_pow_succ a ha₁ ha₂
  have hGmul_raw :
      S.dworkLeadingFactorialProd a *
          (S.gaussSumIntRec a -
            (∏ i : Fin S.f, S.dworkCoeff (S.stickOrd a) (S.dworkLeadingMultiIndex a i)) *
              S.dworkLeadingUnit a) ∈
        S.Q ^ (S.stickOrd a + 1) :=
    Ideal.mul_mem_left _ _ hG
  have hGmul :
      S.dworkLeadingFactorialProd a * S.gaussSumIntRec a -
          S.dworkLeadingFactorialProd a *
            ((∏ i : Fin S.f,
                S.dworkCoeff (S.stickOrd a) (S.dworkLeadingMultiIndex a i)) *
              S.dworkLeadingUnit a) ∈
        S.Q ^ (S.stickOrd a + 1) := by
    convert hGmul_raw using 1
    ring
  have hC := S.dworkLeadingFactorialProd_mul_coeffProd_sub_pi_pow_mem a ha₁ ha₂
  have hCmul :
      (S.dworkLeadingFactorialProd a *
          (∏ i : Fin S.f, S.dworkCoeff (S.stickOrd a) (S.dworkLeadingMultiIndex a i)) -
            S.π ^ S.stickOrd a) * S.dworkLeadingUnit a ∈
        S.Q ^ (S.stickOrd a + 1) :=
    Ideal.mul_mem_right _ _ hC
  have hsum := Ideal.add_mem _ hGmul hCmul
  convert hsum using 1
  ring

/-- The flexible reciprocal-convention integral Gauss sum is not in the next
power `Q^(s+1)`. -/
theorem gaussSumIntRec_not_mem_Q_pow_stickOrd_succ_dwork
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumIntRec a ∉ S.Q ^ (S.stickOrd a + 1) := by
  classical
  intro h_mem
  have h_fact_G_mem :
      S.dworkLeadingFactorialProd a * S.gaussSumIntRec a ∈
        S.Q ^ (S.stickOrd a + 1) :=
    Ideal.mul_mem_left _ _ h_mem
  have h_diff :=
    S.dworkLeadingFactorialProd_mul_gaussSumIntRec_sub_unit_pi_pow_mem a ha₁ ha₂
  have h_unit_pi_mem :
      S.dworkLeadingUnit a * S.π ^ S.stickOrd a ∈
        S.Q ^ (S.stickOrd a + 1) := by
    have htmp := Ideal.sub_mem _ h_fact_G_mem h_diff
    convert htmp using 1
    ring
  have h_unit_notQ : S.dworkLeadingUnit a ∉ S.Q :=
    S.dworkLeadingUnit_not_mem_Q a ha₁ ha₂
  exact
    S.toConductorFlexibleTraceFormStickelbergerSetup.unit_mul_pi_pow_not_mem_Q_pow_succ_for_dwork
      S.toConductorFlexibleTraceFormStickelbergerSetup.pi_ne_zero_for_dwork
      S.toConductorFlexibleTraceFormStickelbergerSetup.pi_not_mem_Q_sq
      (S.dworkLeadingUnit a) h_unit_notQ (S.stickOrd a) h_unit_pi_mem

/-- Flexible Dwork exact reciprocal digit-sum Stickelberger congruence. -/
theorem gaussSumIntRec_qadic_ord_at_prime_dwork
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumIntRec a ∈ S.Q ^ S.stickOrd a ∧
      S.gaussSumIntRec a ∉ S.Q ^ (S.stickOrd a + 1) :=
  ⟨S.gaussSumIntRec_mem_Q_pow_stickOrd_dwork a ha₁ ha₂,
   S.gaussSumIntRec_not_mem_Q_pow_stickOrd_succ_dwork a ha₁ ha₂⟩

/-- Flexible ordinary-character exact order, exported with the complementary
digit-sum index dictated by the stored ordinary character convention. -/
theorem gaussSumInt_qadic_ord_at_prime_ord_dwork
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumInt a ∈ S.Q ^ S.stickOrdOrd a ∧
      S.gaussSumInt a ∉ S.Q ^ (S.stickOrdOrd a + 1) := by
  have h₁ : 1 ≤ p - a := by omega
  have h₂ : p - a ≤ p - 1 := by omega
  have hrec := S.gaussSumIntRec_qadic_ord_at_prime_dwork (p - a) h₁ h₂
  unfold ConductorFlexibleFullTeichDworkSetup.gaussSumIntRec at hrec
  unfold ConductorFlexibleTraceFormStickelbergerSetup.stickOrdOrd
  rwa [show p - (p - a) = a by omega] at hrec

end ConductorFlexibleFullTeichDworkSetup

end Furtwaengler

end BernoulliRegular

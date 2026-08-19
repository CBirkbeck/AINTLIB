import BernoulliRegular.FLT37.Eichler.CaseII.LeadingExponent.CompletedLogValuationHalf
import BernoulliRegular.UnitQuotient.Washington814ForwardD

/-!
# Cyclotomic representative reduction for `p = 37`

This file compares the completed logarithms and mod-`37` free-part classes of real units that
differ by a `37`-th power. It isolates the leading-coefficient assertion from Washington's
Exercise 8.11 and derives the corresponding bridge and eigencomponent collapse.

## Main definitions

* `LeadingExponentEx811Core37`: the leading-coefficient assertion for cyclotomic exponent vectors.

## Main results

* `caseIIEx811Bridge_exists_cyclotomic_div_mem_pPowerSubgroup`: every real unit has a cyclotomic
  representative modulo `37`-th powers.
* `leadingExponentBridge37_of_ex811Core`: the assertion implies `LeadingExponentBridge37`.
* `leadingExponentEigenCollapse37_of_ex811Core`: the assertion implies the eigencomponent collapse.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Exercises 8.10 and 8.11,
  Corollary 8.15, Theorem 8.16, and Section 9.2, Lemma 9.9.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open BernoulliRegular.CyclotomicUnits
open BernoulliRegular.CyclotomicUnits.PadicLogSetup
open BernoulliRegular.CyclotomicUnits.PadicLogSetup.DworkParameter

/-- A `37`-multiple has zero `λ`-graded coordinate through level `36`. -/
theorem caseIIEx811Bridge_evalₐ_nsmul_thirtyseven_eq_zero
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [Fact (Nat.Prime 37)] [NumberField.IsCMField K]
    {N : ℕ} (hN : N ≤ 36) (X : DworkCompleteIntegerRing 37 K) :
    AdicCompletion.evalₐ (lambdaIdeal 37 K) N ((37 : ℕ) • X) = 0 := by
  rw [map_nsmul]
  have h37mem : ((37 : ℕ) : ValuedIntegerRing 37 K) ∈ (lambdaIdeal 37 K) ^ N := by
    have h36 : ((37 : ℕ) : ValuedIntegerRing 37 K) ∈ (lambdaIdeal 37 K) ^ 36 := by
      simpa only [← span_natCast_prime_eq_lambdaIdeal_pow_pred (p := 37) (K := K)] using
        (Ideal.mem_span_singleton_self ((37 : ℕ) : ValuedIntegerRing 37 K))
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hN
    rw [hd, pow_add] at h36
    exact Ideal.mul_le_left h36
  have hzero : ((37 : ℕ) : ValuedIntegerRing 37 K ⧸ (lambdaIdeal 37 K) ^ N) = 0 := by
    rw [show ((37 : ℕ) : ValuedIntegerRing 37 K ⧸ (lambdaIdeal 37 K) ^ N) =
        Ideal.Quotient.mk ((lambdaIdeal 37 K) ^ N) ((37 : ℕ) : ValuedIntegerRing 37 K) by
      rw [map_natCast], Ideal.Quotient.eq_zero_iff_mem]
    exact h37mem
  rw [show ((37 : ℕ) • AdicCompletion.evalₐ (lambdaIdeal 37 K) N X) =
      ((37 : ℕ) : ValuedIntegerRing 37 K ⧸ (lambdaIdeal 37 K) ^ N) •
        AdicCompletion.evalₐ (lambdaIdeal 37 K) N X by
    rw [Nat.cast_smul_eq_nsmul]]
  rw [hzero, zero_smul]

/-- The completed log of a `37`-th power vanishes through `λ`-level `36`. -/
theorem caseIIEx811Bridge_completedLog_evalₐ_eq_zero_of_mem_pPowerSubgroup
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [Fact (Nat.Prime 37)] [NumberField.IsCMField K]
    {w : (𝓞 (NumberField.maximalRealSubfield K))ˣ}
    (hw : w ∈ pPowerSubgroup (EPlus (K := K)) 37)
    {N : ℕ} (hN : N ≤ 36) :
    AdicCompletion.evalₐ (lambdaIdeal 37 K) N
        (completedLog (p := 37) (K := K)
          (EPlus_completedLogDomainPowPred (p := 37) (K := K) w)) = 0 := by
  obtain ⟨Y, hY⟩ := completedLog_EPlus_completedLogDomainPowPred_mem_pPowerSubgroup
    (p := 37) (K := K) hw
  simpa only [← hY] using caseIIEx811Bridge_evalₐ_nsmul_thirtyseven_eq_zero hN Y

/-- Real units differing by a `37`-th power have equal completed-log coordinates through level
`36`. -/
theorem caseIIEx811Bridge_completedLog_evalₐ_eq_of_div_mem_pPowerSubgroup
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [Fact (Nat.Prime 37)] [NumberField.IsCMField K]
    {u v : (𝓞 (NumberField.maximalRealSubfield K))ˣ}
    (hdiv : u * v⁻¹ ∈ pPowerSubgroup (EPlus (K := K)) 37)
    {N : ℕ} (hN : N ≤ 36) :
    AdicCompletion.evalₐ (lambdaIdeal 37 K) N
        (completedLog (p := 37) (K := K)
          (EPlus_completedLogDomainPowPred (p := 37) (K := K) u)) =
      AdicCompletion.evalₐ (lambdaIdeal 37 K) N
        (completedLog (p := 37) (K := K)
          (EPlus_completedLogDomainPowPred (p := 37) (K := K) v)) := by
  rw [show u = (u * v⁻¹) * v by group, EPlus_completedLogDomainPowPred_mul,
    completedLog_mul, map_add,
    caseIIEx811Bridge_completedLog_evalₐ_eq_zero_of_mem_pPowerSubgroup hdiv hN, zero_add]

/-- Real units differing by a `37`-th power have the same mod-`37` free-part class. -/
theorem caseIIEx811Bridge_realUnitToFreePartModP_eq_of_div_mem_pPowerSubgroup
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {u v : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ}
    (hdiv : u * v⁻¹ ∈ pPowerSubgroup (EPlus (K := CyclotomicField 37 ℚ)) 37) :
    FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u) =
      FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul v) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  obtain ⟨w, _hwE, hwpow⟩ := hdiv
  have huv : u = w ^ 37 * v := by
    rw [hwpow]
    group
  rw [huv, ofMul_mul, map_add, ofMul_pow, map_nsmul]
  rw [show ((37 : ℕ) • FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
        (Additive.ofMul w)) =
      ((37 : ℕ) : ZMod 37) •
        FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul w) by
    rw [Nat.cast_smul_eq_nsmul], ZMod.natCast_self, zero_smul, zero_add]

/-- The real cyclotomic-unit subgroup for `p = 37` has index coprime to `37`. -/
theorem caseIIEx811Bridge_not_dvd_CPlus_index
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ¬ (37 : ℕ) ∣
      (BernoulliRegular.CPlus (p := 37) (K := CyclotomicField 37 ℚ) (by decide)).index := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hindex :
      (BernoulliRegular.CPlus (p := 37) (K := CyclotomicField 37 ℚ) (by decide)).index =
        2 ^ ((37 - 3) / 2) * hPlus (CyclotomicField 37 ℚ) := by
    have h := FLT37.Sinnott.index_eq_twoPow_mul_hPlus_of_sinnottIndexFormula
      (p := 37) (K := CyclotomicField 37 ℚ) (by decide) (by decide)
      caseIIGaloisEigen_sinnottIndexFormula_37
    change (cyclotomicUnitIndexSubgroup (p := 37) (K := CyclotomicField 37 ℚ)
      (by decide) (by decide)).index = _ at h
    rwa [cyclotomicUnitIndexSubgroup_eq_CPlus
      (p := 37) (K := CyclotomicField 37 ℚ) (by decide) (by decide)] at h
  rw [hindex]
  intro hdvd
  rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 37)).mp hdvd with h2 | hhplus
  · exact absurd ((Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 37)) h2) (by decide)
  · exact FLT37.Sinnott.flt37_not_dvd_hPlus hhplus

/-- Every real unit has a cyclotomic representative modulo `37`-th powers. -/
theorem caseIIEx811Bridge_exists_cyclotomic_div_mem_pPowerSubgroup
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (u : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ) :
    ∃ v ∈ BernoulliRegular.CPlus (p := 37) (K := CyclotomicField 37 ℚ) (by decide),
      u * v⁻¹ ∈ pPowerSubgroup (EPlus (K := CyclotomicField 37 ℚ)) 37 := by
  classical
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set H : Subgroup (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ :=
    BernoulliRegular.CPlus (p := 37) (K := CyclotomicField 37 ℚ) (by decide) with hH
  haveI : H.FiniteIndex := ⟨by
    rw [hH]
    exact CPlus_index_ne_zero (p := 37) (K := CyclotomicField 37 ℚ) (by decide)⟩
  haveI : Finite (_ ⧸ H) := H.finite_quotient_of_finiteIndex
  have hcard : (Nat.card (_ ⧸ H)).Coprime 37 := by
    rw [Nat.coprime_comm]
    refine (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 37)).mpr ?_
    rw [← Subgroup.index_eq_card, hH]
    exact caseIIEx811Bridge_not_dvd_CPlus_index
  set q : _ ⧸ H := QuotientGroup.mk u with hq
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective ((powCoprime hcard).symm q)
  have hqpow : q = (QuotientGroup.mk k : _ ⧸ H) ^ 37 := by
    rw [← (powCoprime hcard).apply_symm_apply q, ← hk]
    rfl
  refine ⟨u * (k ^ 37)⁻¹, ?_, ?_⟩
  ·
    rw [hH, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_pow, show (QuotientGroup.mk u : _ ⧸ H) = q from rfl, hqpow,
      ← QuotientGroup.mk_pow, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, mul_inv_cancel,
      QuotientGroup.mk_one]
  ·
    rw [show u * (u * (k ^ 37)⁻¹)⁻¹ = k ^ 37 by
      rw [mul_inv_rev, inv_inv, ← mul_assoc, mul_right_comm, mul_inv_cancel, one_mul]]
    exact ⟨k, Subgroup.mem_top k, rfl⟩

open BernoulliRegular (CPlusGenerator) in
/-- The leading-coefficient assertion of Washington's Exercise 8.11 for `p = 37`. -/
def LeadingExponentEx811Core37
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ e : Fin (kummerLogRank 37) → ℤ,
    (∀ N : ℕ, N ≤ 36 →
      AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N
          (∑ a : Fin (kummerLogRank 37),
            e a • kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ)
              (by decide) a) = 0) →
    ∀ j : Fin 18, j ≠ 15 →
      caseIIResidueProvenance_decomp
        (∑ a : Fin (kummerLogRank 37),
          e a • FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
            (Additive.ofMul
              (CPlusGenerator (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a))) j =
        0

open BernoulliRegular (CPlusGenerator) in
/-- The hypothesis of `LeadingExponentEx811Core37` is satisfied by the zero exponent vector. -/
theorem leadingExponentEx811Core37_antecedent_inhabited
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    ∃ e : Fin (kummerLogRank 37) → ℤ,
      ∀ N : ℕ, N ≤ 36 →
        AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N
            (∑ a : Fin (kummerLogRank 37),
              e a • kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ)
                (by decide) a) = 0 := by
  exact ⟨0, by simp⟩

open BernoulliRegular (CPlusExponentProduct) in
/-- The completed-log hypothesis transfers from a real unit to a cyclotomic representative. -/
theorem caseIIEx811Bridge_kummerLogSum_evalₐ_eq_zero
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {u v : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ}
    {s : ℤ} {e : Fin (kummerLogRank 37) → ℤ}
    (hse : CPlusExponentProduct (p := 37) (K := CyclotomicField 37 ℚ) (by decide) s e = v)
    (hdiv : u * v⁻¹ ∈ pPowerSubgroup (EPlus (K := CyclotomicField 37 ℚ)) 37)
    (hu : ∀ N : ℕ, N ≤ 36 →
      AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N
          (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
            (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) u)) = 0)
    {N : ℕ} (hN : N ≤ 36) :
    AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N
        (∑ a : Fin (kummerLogRank 37),
          e a • kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ)
            (by decide) a) = 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hlog_eq :
      (∑ a : Fin (kummerLogRank 37),
        e a • kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ) (by decide) a) =
      completedLog (p := 37) (K := CyclotomicField 37 ℚ)
        (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) v) :=
    hse ▸ (completedLog_EPlus_CPlusExponentProduct_powPred_eq_sum
      (p := 37) (K := CyclotomicField 37 ℚ) (by decide) (by decide) s e).symm
  calc AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N
          (∑ a : Fin (kummerLogRank 37),
            e a • kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ)
              (by decide) a)
        = AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N
          (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
            (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) v)) :=
        congrArg (AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N) hlog_eq
    _ = AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N
          (completedLog (p := 37) (K := CyclotomicField 37 ℚ)
            (EPlus_completedLogDomainPowPred (p := 37) (K := CyclotomicField 37 ℚ) u)) :=
        (caseIIEx811Bridge_completedLog_evalₐ_eq_of_div_mem_pPowerSubgroup hdiv hN).symm
    _ = 0 := hu N hN

open BernoulliRegular (CPlusGenerator CPlusExponentProduct) in
/-- The free-part class of a real unit equals that of a cyclotomic representative. -/
theorem caseIIEx811Bridge_freePartClass_eq
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {u v : (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)))ˣ}
    {s : ℤ} {e : Fin (kummerLogRank 37) → ℤ}
    (hse : CPlusExponentProduct (p := 37) (K := CyclotomicField 37 ℚ) (by decide) s e = v)
    (hdiv : u * v⁻¹ ∈ pPowerSubgroup (EPlus (K := CyclotomicField 37 ℚ)) 37) :
    (∑ a : Fin (kummerLogRank 37),
      e a • FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
        (Additive.ofMul (CPlusGenerator (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a))) =
      FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul u) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hv :
      (∑ a : Fin (kummerLogRank 37),
        e a • FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
          (Additive.ofMul
            (CPlusGenerator (p := 37) (K := CyclotomicField 37 ℚ) (by norm_num) a))) =
      FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ) (Additive.ofMul v) :=
    (FLT37.realUnitToFreePartModP_CPlusExponentProduct s e).symm.trans
      (congrArg (fun w ↦ FLT37.realUnitToFreePartModP (K := CyclotomicField 37 ℚ)
        (Additive.ofMul w)) hse)
  exact hv.trans (caseIIEx811Bridge_realUnitToFreePartModP_eq_of_div_mem_pPowerSubgroup hdiv).symm

open BernoulliRegular (CPlusGenerator CPlusExponentProduct) in
/-- The Exercise 8.11 leading-coefficient assertion implies `LeadingExponentBridge37`. -/
theorem leadingExponentBridge37_of_ex811Core
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hCore : LeadingExponentEx811Core37) :
    LeadingExponentBridge37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro u hu j hj
  obtain ⟨v, hvCPlus, hdiv⟩ :=
    caseIIEx811Bridge_exists_cyclotomic_div_mem_pPowerSubgroup u
  obtain ⟨s, e, hse⟩ :=
    exists_CPlusExponentProduct_of_mem_CPlus (p := 37) (K := CyclotomicField 37 ℚ)
      (by decide) hvCPlus
  have hcls := caseIIEx811Bridge_freePartClass_eq hse hdiv
  have hHyp : ∀ N : ℕ, N ≤ 36 →
      AdicCompletion.evalₐ (lambdaIdeal 37 (CyclotomicField 37 ℚ)) N
          (∑ a : Fin (kummerLogRank 37),
            e a • kummerLogCompletedColumn (p := 37) (K := CyclotomicField 37 ℚ)
              (by decide) a) = 0 :=
    fun N hN ↦ caseIIEx811Bridge_kummerLogSum_evalₐ_eq_zero hse hdiv hu hN
  rw [← hcls]
  exact hCore e hHyp j hj

/-- The Exercise 8.11 leading-coefficient assertion implies the eigencomponent collapse. -/
theorem leadingExponentEigenCollapse37_of_ex811Core
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hCore : LeadingExponentEx811Core37) :
    LeadingExponentEigenCollapse37 :=
  leadingExponentEigenCollapse37_of_bridge' (leadingExponentBridge37_of_ex811Core hCore)

end BernoulliRegular.FLT37.Eichler

end

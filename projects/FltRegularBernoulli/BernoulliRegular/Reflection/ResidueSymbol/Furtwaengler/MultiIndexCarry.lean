module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.LeadingTerm

/-!
# Unbounded multi-index carry reduction (REF-18c2c4-L2c3d-4e)

The Dwork expansion ranges over all multi-indices `Fin f → ℕ`, not just
digit-bounded vectors.  This file supplies the purely combinatorial bridge
from those unbounded multi-indices to the existing digit-vector survivor
lemmas: cyclic base-`ℓ` carrying preserves the weighted value modulo
`ℓ ^ f - 1` and strictly lowers total weight until all entries are `< ℓ`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace MultiIndexCarry

/-- Cyclic successor on `Fin f`.  The last index maps back to `0`. -/
def succCyclic {f : ℕ} (i : Fin f) : Fin f :=
  if h : (i : ℕ) + 1 < f then ⟨(i : ℕ) + 1, h⟩ else ⟨0, by omega⟩

/-- One carry step: subtract `ℓ` at `i`, then add `1` at the cyclic
successor.  The second update is applied after the first, so the `f = 1`
case is handled uniformly. -/
def carryStep (ℓ : ℕ) {f : ℕ} (m : Fin f → ℕ) (i : Fin f) : Fin f → ℕ :=
  Function.update (Function.update m i (m i - ℓ)) (succCyclic i)
    (Function.update m i (m i - ℓ) (succCyclic i) + 1)

theorem multiIndexWeight_update_add_eq {f : ℕ}
    (m : Fin f → ℕ) (i : Fin f) (x : ℕ) :
    multiIndexWeight (Function.update m i x) + m i =
      multiIndexWeight m + x := by
  unfold multiIndexWeight
  rw [Finset.sum_update_of_mem (s := Finset.univ) (i := i) (f := m) (b := x)
    (by simp)]
  rw [Finset.sum_eq_sum_diff_singleton_add (s := Finset.univ) (i := i) (f := m)
    (by simp)]
  omega

theorem multiIndexValue_update_add_eq {ℓ f : ℕ}
    (m : Fin f → ℕ) (i : Fin f) (x : ℕ) :
    multiIndexValue ℓ (Function.update m i x) + m i * ℓ ^ (i : ℕ) =
      multiIndexValue ℓ m + x * ℓ ^ (i : ℕ) := by
  unfold multiIndexValue
  have hupdate :
      (fun j : Fin f => Function.update m i x j * ℓ ^ (j : ℕ)) =
        Function.update (fun j : Fin f => m j * ℓ ^ (j : ℕ)) i
          (x * ℓ ^ (i : ℕ)) := by
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [Function.update_of_ne h]
  rw [hupdate]
  rw [Finset.sum_update_of_mem (s := Finset.univ) (i := i)
    (f := fun j : Fin f => m j * ℓ ^ (j : ℕ)) (b := x * ℓ ^ (i : ℕ)) (by simp)]
  rw [Finset.sum_eq_sum_diff_singleton_add (s := Finset.univ) (i := i)
    (f := fun j : Fin f => m j * ℓ ^ (j : ℕ)) (by simp)]
  omega

theorem pow_succCyclic_modEq (ℓ : ℕ) (hℓ : 2 ≤ ℓ) {f : ℕ} (i : Fin f) :
    ℓ * ℓ ^ (i : ℕ) ≡ ℓ ^ (succCyclic i : ℕ) [MOD ℓ ^ f - 1] := by
  unfold succCyclic
  by_cases h : (i : ℕ) + 1 < f
  · rw [dif_pos h]
    rw [pow_succ, mul_comm]
  · rw [dif_neg h]
    have hi_eq : (i : ℕ) + 1 = f := by omega
    have hpow : ℓ * ℓ ^ (i : ℕ) = ℓ ^ f := by
      calc
        ℓ * ℓ ^ (i : ℕ) = ℓ ^ ((i : ℕ) + 1) := by
          rw [pow_succ, mul_comm]
        _ = ℓ ^ f := by rw [hi_eq]
    rw [hpow]
    change ℓ ^ f ≡ 1 [MOD ℓ ^ f - 1]
    have hpos : 0 < ℓ ^ f := Nat.pow_pos (a := ℓ) (n := f) (by omega)
    have hmod : (ℓ ^ f - 1) * 1 + 1 ≡ 1 [MOD ℓ ^ f - 1] :=
      Nat.ModEq.modulus_mul_add
    convert hmod using 1
    omega

theorem carryStep_weight_add_eq
    {ℓ f : ℕ} (m : Fin f → ℕ) (i : Fin f) (hi : ℓ ≤ m i) :
    multiIndexWeight (carryStep ℓ m i) + ℓ = multiIndexWeight m + 1 := by
  unfold carryStep
  set m₁ : Fin f → ℕ := Function.update m i (m i - ℓ)
  have h₁ : multiIndexWeight m₁ + m i = multiIndexWeight m + (m i - ℓ) := by
    simpa [m₁] using multiIndexWeight_update_add_eq m i (m i - ℓ)
  have h₂ :
      multiIndexWeight (Function.update m₁ (succCyclic i) (m₁ (succCyclic i) + 1)) +
          m₁ (succCyclic i) =
        multiIndexWeight m₁ + (m₁ (succCyclic i) + 1) := by
    simpa using multiIndexWeight_update_add_eq m₁ (succCyclic i) (m₁ (succCyclic i) + 1)
  omega

theorem carryStep_weight_lt
    {ℓ f : ℕ} (hℓ : 2 ≤ ℓ) (m : Fin f → ℕ) (i : Fin f) (hi : ℓ ≤ m i) :
    multiIndexWeight (carryStep ℓ m i) < multiIndexWeight m := by
  have h := carryStep_weight_add_eq (ℓ := ℓ) m i hi
  omega

theorem carryStep_value_modEq
    {ℓ f : ℕ} (hℓ : 2 ≤ ℓ) (m : Fin f → ℕ) (i : Fin f) (hi : ℓ ≤ m i) :
    multiIndexValue ℓ (carryStep ℓ m i) ≡ multiIndexValue ℓ m [MOD ℓ ^ f - 1] := by
  unfold carryStep
  set m₁ : Fin f → ℕ := Function.update m i (m i - ℓ)
  have h₁raw :
      multiIndexValue ℓ m₁ + m i * ℓ ^ (i : ℕ) =
        multiIndexValue ℓ m + (m i - ℓ) * ℓ ^ (i : ℕ) := by
    simpa [m₁] using multiIndexValue_update_add_eq (ℓ := ℓ) m i (m i - ℓ)
  have h₁ : multiIndexValue ℓ m =
      multiIndexValue ℓ m₁ + ℓ * ℓ ^ (i : ℕ) := by
    have hmi :
        (m i - ℓ) * ℓ ^ (i : ℕ) + ℓ * ℓ ^ (i : ℕ) =
          m i * ℓ ^ (i : ℕ) := by
      rw [← Nat.add_mul]
      have : m i - ℓ + ℓ = m i := Nat.sub_add_cancel hi
      rw [this]
    omega
  have h₂raw :
      multiIndexValue ℓ (Function.update m₁ (succCyclic i) (m₁ (succCyclic i) + 1)) +
          m₁ (succCyclic i) * ℓ ^ (succCyclic i : ℕ) =
        multiIndexValue ℓ m₁ +
          (m₁ (succCyclic i) + 1) * ℓ ^ (succCyclic i : ℕ) := by
    simpa using
      multiIndexValue_update_add_eq (ℓ := ℓ) m₁ (succCyclic i) (m₁ (succCyclic i) + 1)
  have h₂ :
      multiIndexValue ℓ (Function.update m₁ (succCyclic i) (m₁ (succCyclic i) + 1)) =
        multiIndexValue ℓ m₁ + ℓ ^ (succCyclic i : ℕ) := by
    have hms :
        (m₁ (succCyclic i) + 1) * ℓ ^ (succCyclic i : ℕ) =
          m₁ (succCyclic i) * ℓ ^ (succCyclic i : ℕ) +
            ℓ ^ (succCyclic i : ℕ) := by
      rw [Nat.add_mul, one_mul]
    rw [hms] at h₂raw
    omega
  calc
    multiIndexValue ℓ (Function.update m₁ (succCyclic i) (m₁ (succCyclic i) + 1))
        = multiIndexValue ℓ m₁ + ℓ ^ (succCyclic i : ℕ) := h₂
    _ ≡ multiIndexValue ℓ m₁ + ℓ * ℓ ^ (i : ℕ) [MOD ℓ ^ f - 1] :=
        Nat.ModEq.add_left (multiIndexValue ℓ m₁) (pow_succCyclic_modEq ℓ hℓ i).symm
    _ = multiIndexValue ℓ m := h₁.symm

/-- Carry reduction produces a digit-bounded vector in the same residue
class modulo `ℓ ^ f - 1`, with no larger weight.  If the original
multi-index was not digit-bounded, the produced vector has strictly
smaller weight. -/
theorem exists_digitVec_modEq_of_multiIndex
    {ℓ f : ℕ} (hℓ : 2 ≤ ℓ) (m : Fin f → ℕ) :
    ∃ v : digitVec ℓ f,
      digitWeight v ≤ multiIndexWeight m ∧
      (¬ (∀ i, m i < ℓ) → digitWeight v < multiIndexWeight m) ∧
      digitValue v ≡ multiIndexValue ℓ m [MOD ℓ ^ f - 1] := by
  classical
  suffices hmain :
      ∀ W : ℕ, ∀ m : Fin f → ℕ, multiIndexWeight m = W →
        ∃ v : digitVec ℓ f,
          digitWeight v ≤ multiIndexWeight m ∧
          (¬ (∀ i, m i < ℓ) → digitWeight v < multiIndexWeight m) ∧
          digitValue v ≡ multiIndexValue ℓ m [MOD ℓ ^ f - 1] by
    exact hmain (multiIndexWeight m) m rfl
  intro W
  induction W using Nat.strong_induction_on with
  | _ W ih =>
      intro m hmW
      by_cases hb : ∀ i, m i < ℓ
      · let v : digitVec ℓ f := ⟨m, hb⟩
        refine ⟨v, ?_, ?_, ?_⟩
        · rfl
        · intro hnot
          exact (hnot hb).elim
        · rfl
      · push Not at hb
        rcases hb with ⟨i, hi_not⟩
        have hi : ℓ ≤ m i := by omega
        set m' : Fin f → ℕ := carryStep ℓ m i
        have hlt : multiIndexWeight m' < W := by
          rw [← hmW]
          exact carryStep_weight_lt hℓ m i hi
        obtain ⟨v, hv_le, hv_strict, hv_mod⟩ := ih (multiIndexWeight m') hlt m' rfl
        refine ⟨v, ?_, ?_, ?_⟩
        · have hstep_lt : multiIndexWeight m' < multiIndexWeight m :=
            carryStep_weight_lt hℓ m i hi
          omega
        · intro _hnot
          have hstep_lt : multiIndexWeight m' < multiIndexWeight m :=
            carryStep_weight_lt hℓ m i hi
          omega
        · exact hv_mod.trans (by simpa [m'] using carryStep_value_modEq hℓ m i hi)

end MultiIndexCarry

namespace TraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : TraceFormStickelbergerSetup ℓ p k K R')

theorem multiIndex_divisibility_of_digitVec_modEq
    (B : ℕ) {m : Fin S.f → ℕ} {v : digitVec ℓ S.f}
    (hmod : digitValue v ≡ multiIndexValue ℓ m [MOD Fintype.card k - 1])
    (hdiv : (Fintype.card k - 1) ∣ B + multiIndexValue ℓ m) :
    (Fintype.card k - 1) ∣ B + digitValue v := by
  have h0 : B + multiIndexValue ℓ m ≡ 0 [MOD Fintype.card k - 1] :=
    (Nat.modEq_zero_iff_dvd).2 hdiv
  have hsum : B + digitValue v ≡ B + multiIndexValue ℓ m [MOD Fintype.card k - 1] :=
    Nat.ModEq.add_left B hmod
  exact (Nat.modEq_zero_iff_dvd).1 (hsum.trans h0)

/-- No unbounded multi-index of weight below `S.stickOrd a` survives the
reciprocal residue-class divisibility test. -/
theorem no_survivor_multiIndex_of_weight_lt_stickOrd
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (m : Fin S.f → ℕ)
    (hm : multiIndexWeight m < S.stickOrd a) :
    ¬ (Fintype.card k - 1) ∣
        ((p - a) * S.stickD + multiIndexValue ℓ m) := by
  intro hdiv
  have hℓ : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
  obtain ⟨v, hv_le, _, hv_mod⟩ :=
    MultiIndexCarry.exists_digitVec_modEq_of_multiIndex (ℓ := ℓ) hℓ m
  have hv_mod_card :
      digitValue v ≡ multiIndexValue ℓ m [MOD Fintype.card k - 1] := by
    simpa [S.card_k] using hv_mod
  have hdiv_v :
      (Fintype.card k - 1) ∣ ((p - a) * S.stickD + digitValue v) :=
    S.multiIndex_divisibility_of_digitVec_modEq ((p - a) * S.stickD) hv_mod_card hdiv
  have hv_lt : digitWeight v < S.stickOrd a := lt_of_le_of_lt hv_le hm
  exact (S.no_survivor_of_weight_lt_stickOrd a ha₁ ha₂ v hv_lt) hdiv_v

/-- At the leading weight, any surviving unbounded multi-index is already
digit-bounded and is the standard digit vector of `a * S.stickD`. -/
theorem unique_multiIndex_survivor_at_stickOrd
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (m : Fin S.f → ℕ)
    (hw : multiIndexWeight m = S.stickOrd a)
    (hdiv : (Fintype.card k - 1) ∣
        ((p - a) * S.stickD + multiIndexValue ℓ m)) :
    multiIndexValue ℓ m = a * S.stickD ∧
      ∃ hm : ∀ i, m i < ℓ,
        (⟨m, hm⟩ : digitVec ℓ S.f) = S.standardDigitVec (a * S.stickD) := by
  have hℓ : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
  obtain ⟨v, hv_le, hv_strict, hv_mod⟩ :=
    MultiIndexCarry.exists_digitVec_modEq_of_multiIndex (ℓ := ℓ) hℓ m
  have hv_mod_card :
      digitValue v ≡ multiIndexValue ℓ m [MOD Fintype.card k - 1] := by
    simpa [S.card_k] using hv_mod
  have hdiv_v :
      (Fintype.card k - 1) ∣ ((p - a) * S.stickD + digitValue v) :=
    S.multiIndex_divisibility_of_digitVec_modEq ((p - a) * S.stickD) hv_mod_card hdiv
  have hv_not_lt : ¬ digitWeight v < S.stickOrd a := fun hv_lt =>
    (S.no_survivor_of_weight_lt_stickOrd a ha₁ ha₂ v hv_lt) hdiv_v
  have hm_bounded : ∀ i, m i < ℓ := by
    by_contra hnot
    have hv_lt_weight : digitWeight v < multiIndexWeight m := hv_strict hnot
    rw [hw] at hv_lt_weight
    exact hv_not_lt hv_lt_weight
  let dm : digitVec ℓ S.f := ⟨m, hm_bounded⟩
  have hdm_div :
      (Fintype.card k - 1) ∣ ((p - a) * S.stickD + digitValue dm) := by
    simpa [dm, digitValue, multiIndexValue] using hdiv
  have hdm_wt : digitWeight dm = S.stickOrd a := by
    simpa [dm, digitWeight, multiIndexWeight] using hw
  have hdm_eq : dm = S.standardDigitVec (a * S.stickD) :=
    S.unique_survivor_at_stickOrd a ha₁ ha₂ dm hdm_wt hdm_div
  refine ⟨?_, hm_bounded, hdm_eq⟩
  change digitValue dm = a * S.stickD
  rw [hdm_eq]
  exact S.digitValue_standardDigitVec_eq a ha₁ ha₂

end TraceFormStickelbergerSetup

namespace ConductorFlexibleTraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (S : ConductorFlexibleTraceFormStickelbergerSetup ℓ p k K R')

theorem multiIndex_divisibility_of_digitVec_modEq
    (B : ℕ) {m : Fin S.f → ℕ} {v : digitVec ℓ S.f}
    (hmod : digitValue v ≡ multiIndexValue ℓ m [MOD Fintype.card k - 1])
    (hdiv : (Fintype.card k - 1) ∣ B + multiIndexValue ℓ m) :
    (Fintype.card k - 1) ∣ B + digitValue v := by
  have h0 : B + multiIndexValue ℓ m ≡ 0 [MOD Fintype.card k - 1] :=
    (Nat.modEq_zero_iff_dvd).2 hdiv
  have hsum : B + digitValue v ≡ B + multiIndexValue ℓ m [MOD Fintype.card k - 1] :=
    Nat.ModEq.add_left B hmod
  exact (Nat.modEq_zero_iff_dvd).1 (hsum.trans h0)

/-- No unbounded multi-index of weight below `S.stickOrd a` survives the
conductor-flexible reciprocal residue-class divisibility test. -/
theorem no_survivor_multiIndex_of_weight_lt_stickOrd
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (m : Fin S.f → ℕ)
    (hm : multiIndexWeight m < S.stickOrd a) :
    ¬ (Fintype.card k - 1) ∣
        ((p - a) * S.stickD + multiIndexValue ℓ m) := by
  intro hdiv
  have hℓ : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
  obtain ⟨v, hv_le, _, hv_mod⟩ :=
    MultiIndexCarry.exists_digitVec_modEq_of_multiIndex (ℓ := ℓ) hℓ m
  have hv_mod_card :
      digitValue v ≡ multiIndexValue ℓ m [MOD Fintype.card k - 1] := by
    simpa [S.card_k] using hv_mod
  have hdiv_v :
      (Fintype.card k - 1) ∣ ((p - a) * S.stickD + digitValue v) :=
    S.multiIndex_divisibility_of_digitVec_modEq ((p - a) * S.stickD) hv_mod_card hdiv
  have hv_lt : digitWeight v < S.stickOrd a := lt_of_le_of_lt hv_le hm
  exact (S.no_survivor_of_weight_lt_stickOrd a ha₁ ha₂ v hv_lt) hdiv_v

/-- At the leading weight, any surviving conductor-flexible unbounded
multi-index is already digit-bounded and is the standard digit vector of
`a * S.stickD`. -/
theorem unique_multiIndex_survivor_at_stickOrd
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (m : Fin S.f → ℕ)
    (hw : multiIndexWeight m = S.stickOrd a)
    (hdiv : (Fintype.card k - 1) ∣
        ((p - a) * S.stickD + multiIndexValue ℓ m)) :
    multiIndexValue ℓ m = a * S.stickD ∧
      ∃ hm : ∀ i, m i < ℓ,
        (⟨m, hm⟩ : digitVec ℓ S.f) = S.standardDigitVec (a * S.stickD) := by
  have hℓ : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
  obtain ⟨v, hv_le, hv_strict, hv_mod⟩ :=
    MultiIndexCarry.exists_digitVec_modEq_of_multiIndex (ℓ := ℓ) hℓ m
  have hv_mod_card :
      digitValue v ≡ multiIndexValue ℓ m [MOD Fintype.card k - 1] := by
    simpa [S.card_k] using hv_mod
  have hdiv_v :
      (Fintype.card k - 1) ∣ ((p - a) * S.stickD + digitValue v) :=
    S.multiIndex_divisibility_of_digitVec_modEq ((p - a) * S.stickD) hv_mod_card hdiv
  have hv_not_lt : ¬ digitWeight v < S.stickOrd a := fun hv_lt =>
    (S.no_survivor_of_weight_lt_stickOrd a ha₁ ha₂ v hv_lt) hdiv_v
  have hm_bounded : ∀ i, m i < ℓ := by
    by_contra hnot
    have hv_lt_weight : digitWeight v < multiIndexWeight m := hv_strict hnot
    rw [hw] at hv_lt_weight
    exact hv_not_lt hv_lt_weight
  let dm : digitVec ℓ S.f := ⟨m, hm_bounded⟩
  have hdm_div :
      (Fintype.card k - 1) ∣ ((p - a) * S.stickD + digitValue dm) := by
    simpa [dm, digitValue, multiIndexValue] using hdiv
  have hdm_wt : digitWeight dm = S.stickOrd a := by
    simpa [dm, digitWeight, multiIndexWeight] using hw
  have hdm_eq : dm = S.standardDigitVec (a * S.stickD) :=
    S.unique_survivor_at_stickOrd a ha₁ ha₂ dm hdm_wt hdm_div
  refine ⟨?_, hm_bounded, hdm_eq⟩
  change digitValue dm = a * S.stickD
  rw [hdm_eq]
  exact S.digitValue_standardDigitVec_eq a ha₁ ha₂

end ConductorFlexibleTraceFormStickelbergerSetup

namespace FullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : FullTeichStickelbergerSetup ℓ p k K R')

/-- Full-Teich wrapper for unbounded multi-index no-survivor. -/
theorem no_survivor_multiIndex_of_weight_lt_stickOrd
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (m : Fin S.f → ℕ)
    (hm : multiIndexWeight m < S.stickOrd a) :
    ¬ (Fintype.card k - 1) ∣
        ((p - a) * S.stickD + multiIndexValue ℓ m) :=
  S.toTraceFormStickelbergerSetup.no_survivor_multiIndex_of_weight_lt_stickOrd
    a ha₁ ha₂ m hm

/-- Full-Teich wrapper for uniqueness of the leading unbounded
multi-index survivor. -/
theorem unique_multiIndex_survivor_at_stickOrd
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (m : Fin S.f → ℕ)
    (hw : multiIndexWeight m = S.stickOrd a)
    (hdiv : (Fintype.card k - 1) ∣
        ((p - a) * S.stickD + multiIndexValue ℓ m)) :
    multiIndexValue ℓ m = a * S.stickD ∧
      ∃ hm : ∀ i, m i < ℓ,
        (⟨m, hm⟩ : digitVec ℓ S.f) = S.standardDigitVec (a * S.stickD) :=
  S.toTraceFormStickelbergerSetup.unique_multiIndex_survivor_at_stickOrd
    a ha₁ ha₂ m hw hdiv

/-- Bundle accessor for unbounded multi-indices of weight at most `N`. -/
def multiIndexLE (N : ℕ) : Finset (Fin S.f → ℕ) :=
  Furtwaengler.multiIndexLE S.f N

end FullTeichStickelbergerSetup

namespace ConductorFlexibleFullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (S : ConductorFlexibleFullTeichStickelbergerSetup ℓ p k K R')

/-- Full-Teich wrapper for conductor-flexible unbounded multi-index
no-survivor. -/
theorem no_survivor_multiIndex_of_weight_lt_stickOrd
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (m : Fin S.f → ℕ)
    (hm : multiIndexWeight m < S.stickOrd a) :
    ¬ (Fintype.card k - 1) ∣
        ((p - a) * S.stickD + multiIndexValue ℓ m) :=
  S.toConductorFlexibleTraceFormStickelbergerSetup.no_survivor_multiIndex_of_weight_lt_stickOrd
    a ha₁ ha₂ m hm

/-- Full-Teich wrapper for uniqueness of the conductor-flexible leading
unbounded multi-index survivor. -/
theorem unique_multiIndex_survivor_at_stickOrd
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (m : Fin S.f → ℕ)
    (hw : multiIndexWeight m = S.stickOrd a)
    (hdiv : (Fintype.card k - 1) ∣
        ((p - a) * S.stickD + multiIndexValue ℓ m)) :
    multiIndexValue ℓ m = a * S.stickD ∧
      ∃ hm : ∀ i, m i < ℓ,
        (⟨m, hm⟩ : digitVec ℓ S.f) = S.standardDigitVec (a * S.stickD) :=
  S.toConductorFlexibleTraceFormStickelbergerSetup.unique_multiIndex_survivor_at_stickOrd
    a ha₁ ha₂ m hw hdiv

/-- Bundle accessor for conductor-flexible unbounded multi-indices of weight
at most `N`. -/
def multiIndexLE (N : ℕ) : Finset (Fin S.f → ℕ) :=
  Furtwaengler.multiIndexLE S.f N

end ConductorFlexibleFullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

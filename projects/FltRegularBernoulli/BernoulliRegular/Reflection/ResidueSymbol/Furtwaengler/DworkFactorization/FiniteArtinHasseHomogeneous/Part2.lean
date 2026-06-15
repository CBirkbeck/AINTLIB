module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FiniteArtinHasseHomogeneous.Part1

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace FullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (F : FullTeichStickelbergerSetup ℓ p k K R')

noncomputable def finiteArtinHasseExpCoordLogHomogeneousDegreeSum
    (N d : ℕ) (x : 𝓞 R') (hx : x ∈ F.Q) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  ∑ a ∈ (Finset.Icc 1 d).attach,
    F.finiteArtinHasseExpCoordLogHomogeneousTerm N a.1 d x hx

theorem finiteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_eval_sum
    (N d : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum N d x hx =
      ∑ a ∈ (Finset.Icc 1 d).attach,
        F.finiteLogNatDivEval N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (F.finiteArtinHasseExpCoordLogHomogeneousNumerator N a.1 d x)
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            have had : a.1 ≤ d := (Finset.mem_Icc.mp a.2).2
            have hden : a.1.factorization ℓ * (ℓ - 1) ≤ d :=
              finiteArtinHasse_den_exponent_le (ℓ := ℓ) (Nat.ne_zero_of_lt ha1) had
            simpa [finiteArtinHasseExpCoordLogHomogeneousNumerator] using
              (Ideal.pow_le_pow_right hden
                (F.finiteArtinHasseExpCoordLogHomogeneousNumerator_mem_Q_pow
                  N a.1 d hx))) := by
  classical
  unfold finiteArtinHasseExpCoordLogHomogeneousDegreeSum
  refine Finset.sum_congr rfl ?_
  intro a _ha
  have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
  have had : a.1 ≤ d := (Finset.mem_Icc.mp a.2).2
  have han : a.1 ≠ 0 := Nat.ne_zero_of_lt ha1
  have hden : a.1.factorization ℓ * (ℓ - 1) ≤ d :=
    finiteArtinHasse_den_exponent_le (ℓ := ℓ) han had
  have hcoeff :
      ((F.finiteArtinHasseExpCoordPoly N x) ^ a.1).coeff d ∈ F.Q ^ d :=
    F.finiteArtinHasseExpCoordPoly_pow_coeff_mem_Q_pow N hx a.1 d
  have hsign :
      (((-1 : 𝓞 R') ^ (a.1 + 1)) *
          ((F.finiteArtinHasseExpCoordPoly N x) ^ a.1).coeff d) ∈ F.Q ^ d :=
    F.finiteArtinHasseExpCoord_signed_pow_coeff_mem_Q_pow N a.1 d hx
  have hnum0 :
      F.finiteArtinHasseExpCoordLogHomogeneousNumerator N a.1 d x ∈
        F.Q ^ (a.1.factorization ℓ * (ℓ - 1) + 0) := by
    simpa [finiteArtinHasseExpCoordLogHomogeneousNumerator] using
      (Ideal.pow_le_pow_right hden hsign)
  have hmk :
      Ideal.Quotient.mk (F.Q ^ (N + 1)) ((-1 : 𝓞 R') ^ (a.1 + 1)) =
        ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (a.1 + 1)) := by
    simp
  rw [F.finiteArtinHasseExpCoordLogHomogeneousTerm_eq_signed_eval N a.1 d hx han had]
  rw [← hmk]
  rw [← F.finiteLogNatDivEvalAtDegree_mul_left han ((-1 : 𝓞 R') ^ (a.1 + 1))
    hcoeff hsign hden]
  rw [F.finiteLogNatDivEvalAtDegree_eq_finiteLogNatDivEval han hsign hden hnum0]
  exact F.finiteLogNatDivEval_eq_of_eq han
    (by simp [finiteArtinHasseExpCoordLogHomogeneousNumerator]) hnum0 _

theorem finiteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_zero_of_factorial_weighted_sum_mem
    (N d : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q)
    (hclear :
      (∑ n ∈ Finset.Icc 1 d,
        ((d.factorial / n : ℕ) : 𝓞 R') *
          (((-1 : 𝓞 R') ^ (n + 1)) *
            ((F.finiteArtinHasseExpCoordPoly N x) ^ n).coeff d)) ∈
        F.Q ^ (d.factorial.factorization ℓ * (ℓ - 1) + (N + 1))) :
    F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum N d x hx = 0 := by
  classical
  let z : ℕ → 𝓞 R' := fun n =>
    F.finiteArtinHasseExpCoordLogHomogeneousNumerator N n d x
  have hz0 : ∀ n ∈ Finset.Icc 1 d,
      z n ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + 0) := by
    intro n hnI
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
    have hnd : n ≤ d := (Finset.mem_Icc.mp hnI).2
    have hden : n.factorization ℓ * (ℓ - 1) ≤ d :=
      finiteArtinHasse_den_exponent_le (ℓ := ℓ) (Nat.ne_zero_of_lt hn1) hnd
    simpa using
      (Ideal.pow_le_pow_right hden
        (F.finiteArtinHasseExpCoordLogHomogeneousNumerator_mem_Q_pow N n d hx))
  have htransport :=
    F.finiteLogNatDivEval_Icc_sum_eq_zero_of_factorial_weighted_sum_mem_Q_pow
      (N := N) (d := d) (s := 0) (t := N + 1) z hz0
      (by simpa [z, finiteArtinHasseExpCoordLogHomogeneousNumerator] using hclear) le_rfl
  calc
    F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum N d x hx
        =
      ∑ a ∈ (Finset.Icc 1 d).attach,
        F.finiteLogNatDivEval N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (z a.1) (hz0 a.1 a.2) := by
        simpa [z] using
          F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_eval_sum N d hx
    _ = 0 := htransport

theorem finiteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_logTerm_of_factorial_weighted_sub_pow_mem
    (N r : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q)
    (hclear :
      (∑ n ∈ Finset.Icc 1 (ℓ ^ r),
        (((ℓ ^ r).factorial / n : ℕ) : 𝓞 R') *
          (F.finiteArtinHasseExpCoordLogHomogeneousNumerator N n (ℓ ^ r) x -
            if n = ℓ ^ r then x ^ (ℓ ^ r) else 0)) ∈
        F.Q ^ ((ℓ ^ r).factorial.factorization ℓ * (ℓ - 1) + (N + 1))) :
    F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum N (ℓ ^ r) x hx =
      F.finiteArtinHasseLogTerm N r x hx := by
  classical
  let d : ℕ := ℓ ^ r
  let num : ℕ → 𝓞 R' := fun n =>
    F.finiteArtinHasseExpCoordLogHomogeneousNumerator N n d x
  let target : ℕ → 𝓞 R' := fun n => if n = d then x ^ d else 0
  let z : ℕ → 𝓞 R' := fun n => num n - target n
  have hd_ne : d ≠ 0 := pow_ne_zero r (Fact.out : Nat.Prime ℓ).ne_zero
  have hxd : x ^ d ∈ F.Q ^ d := Ideal.pow_mem_pow hx d
  have hz0 : ∀ n ∈ Finset.Icc 1 d,
      z n ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + 0) := by
    intro n hnI
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
    have hnd : n ≤ d := (Finset.mem_Icc.mp hnI).2
    have hden : n.factorization ℓ * (ℓ - 1) ≤ d :=
      finiteArtinHasse_den_exponent_le (ℓ := ℓ) (Nat.ne_zero_of_lt hn1) hnd
    have hnum_d : num n ∈ F.Q ^ d := by
      simpa [num] using
        F.finiteArtinHasseExpCoordLogHomogeneousNumerator_mem_Q_pow N n d hx
    have htarget_d : target n ∈ F.Q ^ d := by
      by_cases hn : n = d
      · simp [target, hn, hxd]
      · simp [target, hn]
    have hz_d : z n ∈ F.Q ^ d := by
      simpa [z, sub_eq_add_neg] using (F.Q ^ d).add_mem hnum_d ((F.Q ^ d).neg_mem htarget_d)
    simpa using Ideal.pow_le_pow_right hden hz_d
  have htransport :
      (∑ a ∈ (Finset.Icc 1 d).attach,
        F.finiteLogNatDivEval N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (z a.1) (hz0 a.1 a.2)) = 0 :=
    F.finiteLogNatDivEval_Icc_sum_eq_zero_of_factorial_weighted_sum_mem_Q_pow
      (N := N) (d := d) (s := 0) (t := N + 1) z hz0
      (by simpa [d, z, num, target] using hclear) le_rfl
  have hnum0 : ∀ a : {n // n ∈ Finset.Icc 1 d},
      num a.1 ∈ F.Q ^ (a.1.factorization ℓ * (ℓ - 1) + 0) := by
    intro a
    have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
    have had : a.1 ≤ d := (Finset.mem_Icc.mp a.2).2
    have hden : a.1.factorization ℓ * (ℓ - 1) ≤ d :=
      finiteArtinHasse_den_exponent_le (ℓ := ℓ) (Nat.ne_zero_of_lt ha1) had
    simpa [num] using
      Ideal.pow_le_pow_right hden
        (F.finiteArtinHasseExpCoordLogHomogeneousNumerator_mem_Q_pow N a.1 d hx)
  have htarget0 : ∀ a : {n // n ∈ Finset.Icc 1 d},
      target a.1 ∈ F.Q ^ (a.1.factorization ℓ * (ℓ - 1) + 0) := by
    intro a
    by_cases ha : a.1 = d
    · have hden : a.1.factorization ℓ * (ℓ - 1) ≤ d := by
        simpa [ha] using finiteArtinHasse_den_exponent_le (ℓ := ℓ) hd_ne le_rfl
      simpa [target, ha] using Ideal.pow_le_pow_right hden hxd
    · simp [target, ha]
  have heval_sub :
      (∑ a ∈ (Finset.Icc 1 d).attach,
        F.finiteLogNatDivEval N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (z a.1) (hz0 a.1 a.2))
        =
      (∑ a ∈ (Finset.Icc 1 d).attach,
        F.finiteLogNatDivEval N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (num a.1) (hnum0 a)) -
      (∑ a ∈ (Finset.Icc 1 d).attach,
        F.finiteLogNatDivEval N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (target a.1) (htarget0 a)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro a _ha
    have han : a.1 ≠ 0 := by
      have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
      exact Nat.ne_zero_of_lt ha1
    have hneg : -target a.1 ∈ F.Q ^ (a.1.factorization ℓ * (ℓ - 1) + 0) :=
      (F.Q ^ (a.1.factorization ℓ * (ℓ - 1) + 0)).neg_mem (htarget0 a)
    have hz_add : z a.1 = num a.1 + -target a.1 := by
      simp [z, sub_eq_add_neg]
    have hz_add_mem :
        num a.1 + -target a.1 ∈ F.Q ^ (a.1.factorization ℓ * (ℓ - 1) + 0) := by
      simpa [← hz_add] using hz0 a.1 a.2
    have hadd :
        F.finiteLogNatDivEval N a.1 0 han (num a.1 + -target a.1) hz_add_mem =
          F.finiteLogNatDivEval N a.1 0 han (num a.1) (hnum0 a) +
            F.finiteLogNatDivEval N a.1 0 han (-target a.1) hneg :=
      F.finiteLogNatDivEval_add (N := N) (n := a.1) (s := 0) han
        (hnum0 a) hneg hz_add_mem
    calc
      F.finiteLogNatDivEval N a.1 0 han (z a.1) (hz0 a.1 a.2)
          =
        F.finiteLogNatDivEval N a.1 0 han (num a.1 + -target a.1)
          hz_add_mem :=
          F.finiteLogNatDivEval_eq_of_eq han hz_add (hz0 a.1 a.2) hz_add_mem
      _ =
        F.finiteLogNatDivEval N a.1 0 han (num a.1) (hnum0 a) +
          F.finiteLogNatDivEval N a.1 0 han (-target a.1) hneg := hadd
      _ =
        F.finiteLogNatDivEval N a.1 0 han (num a.1) (hnum0 a) -
          F.finiteLogNatDivEval N a.1 0 han (target a.1) (htarget0 a) := by
          rw [F.finiteLogNatDivEval_neg han (htarget0 a) hneg]
          ring
  have htarget_sum :
      (∑ a ∈ (Finset.Icc 1 d).attach,
        F.finiteLogNatDivEval N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (target a.1) (htarget0 a)) =
        F.finiteArtinHasseLogTerm N r x hx := by
    let a0 : {n // n ∈ Finset.Icc 1 d} := ⟨d, Finset.mem_Icc.mpr ⟨by
      have hdpos : 0 < d := Nat.pos_of_ne_zero hd_ne
      exact Nat.succ_le_of_lt hdpos, le_rfl⟩⟩
    let targetEval : {n // n ∈ Finset.Icc 1 d} → 𝓞 R' ⧸ F.Q ^ (N + 1) := fun a =>
      F.finiteLogNatDivEval N a.1 0
        (by
          have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
          exact Nat.ne_zero_of_lt ha1)
        (target a.1) (htarget0 a)
    change (∑ a ∈ (Finset.Icc 1 d).attach, targetEval a) =
      F.finiteArtinHasseLogTerm N r x hx
    calc
      (∑ a ∈ (Finset.Icc 1 d).attach, targetEval a) = targetEval a0 := by
        refine Finset.sum_eq_single (s := (Finset.Icc 1 d).attach)
          (a := a0) (f := targetEval) ?zero ?not_mem
        · intro a _ha hne
          dsimp [targetEval]
          have han : a.1 ≠ 0 := by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1
          have ha_ne : a.1 ≠ d := fun ha =>
            hne (Subtype.ext ha)
          have htarget_zero : target a.1 = 0 := by
            simp [target, ha_ne]
          have hzero : (0 : 𝓞 R') ∈ F.Q ^ (a.1.factorization ℓ * (ℓ - 1) + 0) :=
            zero_mem _
          calc
            F.finiteLogNatDivEval N a.1 0
                (by
                  have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
                  exact Nat.ne_zero_of_lt ha1)
                (target a.1) (htarget0 a)
                =
              F.finiteLogNatDivEval N a.1 0 han 0 hzero :=
                F.finiteLogNatDivEval_eq_of_eq han htarget_zero (htarget0 a) hzero
            _ = 0 :=
                F.finiteLogNatDivEval_zero (N := N) (n := a.1) (s := 0) han hzero
        · intro ha0
          simp [a0] at ha0
      _ = F.finiteArtinHasseLogTerm N r x hx := by
        dsimp [targetEval]
        have hden : d.factorization ℓ * (ℓ - 1) ≤ d :=
          finiteArtinHasse_den_exponent_le (ℓ := ℓ) hd_ne le_rfl
        have htarget0_d : x ^ d ∈ F.Q ^ (d.factorization ℓ * (ℓ - 1) + 0) :=
          Ideal.pow_le_pow_right hden hxd
        calc
          F.finiteLogNatDivEval N a0.1 0
              (by
                have ha1 : 1 ≤ a0.1 := (Finset.mem_Icc.mp a0.2).1
                exact Nat.ne_zero_of_lt ha1)
              (target a0.1) (htarget0 a0)
              =
            F.finiteLogNatDivEval N d 0 hd_ne (x ^ d) htarget0_d :=
              F.finiteLogNatDivEval_eq_of_eq hd_ne (by simp [a0, target])
                (htarget0 a0) htarget0_d
          _ =
            F.finiteArtinHasseLogTerm N r x hx := by
              rw [finiteArtinHasseLogTerm]
              exact F.finiteLogNatDivEval_eq_of_mem
                (N := N) (n := d) (s := 0)
                (t := finiteArtinHasseLogTermOrder (ℓ := ℓ) r) hd_ne htarget0_d
                (by
                  simpa [d,
                    pow_factorization_mul_pred_add_finiteArtinHasseLogTermOrder (ℓ := ℓ) r]
                    using hxd)
  have hdegree :
      F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum N d x hx =
      (∑ a ∈ (Finset.Icc 1 d).attach,
        F.finiteLogNatDivEval N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (num a.1) (hnum0 a)) := by
    simpa [num] using
      F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_eval_sum N d hx
  rw [← sub_eq_zero]
  calc
    F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum N d x hx -
        F.finiteArtinHasseLogTerm N r x hx
        =
      (∑ a ∈ (Finset.Icc 1 d).attach,
        F.finiteLogNatDivEval N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (num a.1) (hnum0 a)) -
      (∑ a ∈ (Finset.Icc 1 d).attach,
        F.finiteLogNatDivEval N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (target a.1) (htarget0 a)) := by
        rw [hdegree, htarget_sum]
    _ =
      ∑ a ∈ (Finset.Icc 1 d).attach,
        F.finiteLogNatDivEval N a.1 0
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (z a.1) (hz0 a.1 a.2) := by
        rw [heval_sub]
    _ = 0 := htransport

theorem finiteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_zero_of_not_pow
    (N d : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q)
    (hd : ¬ ∃ r : ℕ, d = ℓ ^ r) :
    F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum N d x hx = 0 :=
  F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_zero_of_factorial_weighted_sum_mem
    N d hx
    (by
      simpa [finiteArtinHasseExpCoordLogHomogeneousNumerator] using
        F.finiteArtinHasseLogHomogeneousNumerator_factorial_weighted_sum_mem_Q_pow_of_not_pow
          N d hx hd)

theorem finiteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_logTerm
    (N r : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum N (ℓ ^ r) x hx =
      F.finiteArtinHasseLogTerm N r x hx :=
  F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_logTerm_of_factorial_weighted_sub_pow_mem
    N r hx
    (by
      simpa [finiteArtinHasseExpCoordLogHomogeneousNumerator] using
        F.finiteArtinHasseLogHomogeneousNumerator_factorial_weighted_sub_pow_mem_Q_pow
          N r hx)

theorem finiteLogTermCore_finiteArtinHasseExpCoord_eq_homogeneous_support_sum
    (N n : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) (hn : n ≠ 0) :
    F.finiteLogTermCore N n (F.finiteArtinHasseExpCoord N x)
        (F.finiteArtinHasseExpCoord_mem_Q N hx) =
      ∑ d ∈ ((F.finiteArtinHasseExpCoordPoly N x) ^ n).support,
        F.finiteArtinHasseExpCoordLogHomogeneousCore N n d x hx := by
  classical
  let P : Polynomial (𝓞 R') := F.finiteArtinHasseExpCoordPoly N x
  let z : 𝓞 R' := F.finiteArtinHasseExpCoord N x
  let s : ℕ := finiteLogTermOrder (ℓ := ℓ) n
  have hz : z ∈ F.Q := by
    simpa [z] using F.finiteArtinHasseExpCoord_mem_Q N hx
  have hpow_order : z ^ n ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s) := by
    simpa [z, s, factorization_mul_pred_add_finiteLogTermOrder (ℓ := ℓ) hn] using
      Ideal.pow_mem_pow hz n
  have hcoeff_order_of_mem :
      ∀ d ∈ (P ^ n).support,
        (P ^ n).coeff d ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s) := by
    intro d hd
    have hnd : n ≤ d := by
      simpa [P] using
        finiteArtinHasseExpCoordPoly_pow_le_of_mem_support (F := F) N x hd
    have hcoeff : (P ^ n).coeff d ∈ F.Q ^ d := by
      simpa [P] using F.finiteArtinHasseExpCoordPoly_pow_coeff_mem_Q_pow N hx n d
    have hle : F.Q ^ d ≤ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s) := by
      rw [factorization_mul_pred_add_finiteLogTermOrder (ℓ := ℓ) hn]
      exact Ideal.pow_le_pow_right hnd
    exact hle hcoeff
  have hcoeff_order :
      ∀ d, (P ^ n).coeff d ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s) := by
    intro d
    by_cases hd : d ∈ (P ^ n).support
    · exact hcoeff_order_of_mem d hd
    · have hzero : (P ^ n).coeff d = 0 := by
        simpa [Polynomial.mem_support_iff] using hd
      rw [hzero]
      exact zero_mem _
  have heval :
      (P ^ n).eval 1 = ∑ d ∈ (P ^ n).support, (P ^ n).coeff d := by
    rw [Polynomial.eval_eq_sum]
    simp [Polynomial.sum]
  have hsum_eq : z ^ n = ∑ d ∈ (P ^ n).support, (P ^ n).coeff d := by
    calc
      z ^ n = ((F.finiteArtinHasseExpCoordPoly N x).eval 1) ^ n := by
        rw [F.finiteArtinHasseExpCoordPoly_eval_one]
      _ = (P ^ n).eval 1 := by
        simp [P, Polynomial.eval_pow]
      _ = ∑ d ∈ (P ^ n).support, (P ^ n).coeff d := heval
  have hsum_order :
      (∑ d ∈ (P ^ n).support, (P ^ n).coeff d) ∈
        F.Q ^ (n.factorization ℓ * (ℓ - 1) + s) := by
    rw [← hsum_eq]
    exact hpow_order
  calc
    F.finiteLogTermCore N n (F.finiteArtinHasseExpCoord N x)
        (F.finiteArtinHasseExpCoord_mem_Q N hx)
        =
      F.finiteLogNatDivEval N n s hn (z ^ n) hpow_order := by
        rw [F.finiteLogTermCore_eq_finiteLogNatDivEvalAtDegree hn hz]
        rw [finiteLogNatDivEvalAtDegree]
        exact F.finiteLogNatDivEval_eq_of_mem hn _ hpow_order
    _ =
      F.finiteLogNatDivEval N n s hn
        (∑ d ∈ (P ^ n).support, (P ^ n).coeff d) hsum_order :=
        F.finiteLogNatDivEval_eq_of_eq hn hsum_eq hpow_order hsum_order
    _ =
      ∑ d ∈ (P ^ n).support,
        F.finiteLogNatDivEval N n s hn ((P ^ n).coeff d) (hcoeff_order d) := by
        rw [F.finiteLogNatDivEval_sum hn (P ^ n).support
          (fun d => (P ^ n).coeff d) hcoeff_order hsum_order]
    _ =
      ∑ d ∈ (P ^ n).support,
        F.finiteArtinHasseExpCoordLogHomogeneousCore N n d x hx := by
        refine Finset.sum_congr rfl ?_
        intro d hd
        have hnd : n ≤ d := by
          simpa [P] using
            finiteArtinHasseExpCoordPoly_pow_le_of_mem_support (F := F) N x hd
        have hden : n.factorization ℓ * (ℓ - 1) ≤ d := by
          have h :=
            Nat.factorization_mul_pred_le_pred
              (ell := ℓ) (n := n) (Fact.out : Nat.Prime ℓ) hn
          omega
        have hcoeff : (P ^ n).coeff d ∈ F.Q ^ d := by
          simpa [P] using F.finiteArtinHasseExpCoordPoly_pow_coeff_mem_Q_pow N hx n d
        rw [finiteArtinHasseExpCoordLogHomogeneousCore, dif_neg hn, dif_pos hnd]
        exact (F.finiteLogNatDivEvalAtDegree_eq_finiteLogNatDivEval hn
          hcoeff hden (hcoeff_order d)).symm

theorem finiteLogTerm_finiteArtinHasseExpCoord_eq_homogeneous_support_sum
    (N n : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) (hn : n ≠ 0) :
    F.finiteLogTerm N n (F.finiteArtinHasseExpCoord N x)
        (F.finiteArtinHasseExpCoord_mem_Q N hx) =
      ∑ d ∈ ((F.finiteArtinHasseExpCoordPoly N x) ^ n).support,
        F.finiteArtinHasseExpCoordLogHomogeneousTerm N n d x hx := by
  rw [finiteLogTerm,
    F.finiteLogTermCore_finiteArtinHasseExpCoord_eq_homogeneous_support_sum N n hx hn,
    Finset.mul_sum]
  simp [finiteArtinHasseExpCoordLogHomogeneousTerm]

/-- Homogeneous expansion of the finite logarithm applied to the finite
Artin-Hasse principal-unit coordinate. -/
theorem finiteLog_finiteArtinHasseExpCoord_eq_homogeneous_support_sum
    (N : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteLog N (F.finiteArtinHasseExpCoord N x)
        (F.finiteArtinHasseExpCoord_mem_Q N hx) =
      ∑ n ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N),
        ∑ d ∈ ((F.finiteArtinHasseExpCoordPoly N x) ^ n).support,
          F.finiteArtinHasseExpCoordLogHomogeneousTerm N n d x hx := by
  classical
  unfold finiteLog
  refine Finset.sum_congr rfl ?_
  intro n _hn
  by_cases hn0 : n = 0
  · subst n
    simp [finiteArtinHasseExpCoordLogHomogeneousTerm,
      finiteArtinHasseExpCoordLogHomogeneousCore]
  · exact F.finiteLogTerm_finiteArtinHasseExpCoord_eq_homogeneous_support_sum N n hx hn0

theorem finiteArtinHasseExpCoordLogHomogeneousTerm_eq_zero_of_not_mem_support
    (N n d : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q)
    (hd : d ∉ ((F.finiteArtinHasseExpCoordPoly N x) ^ n).support) :
    F.finiteArtinHasseExpCoordLogHomogeneousTerm N n d x hx = 0 := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [finiteArtinHasseExpCoordLogHomogeneousTerm,
      finiteArtinHasseExpCoordLogHomogeneousCore]
  by_cases hnd : n ≤ d
  · have hcoeff_zero : ((F.finiteArtinHasseExpCoordPoly N x) ^ n).coeff d = 0 := by
      simpa [Polynomial.mem_support_iff] using hd
    have hcoeff : ((F.finiteArtinHasseExpCoordPoly N x) ^ n).coeff d ∈ F.Q ^ d :=
      F.finiteArtinHasseExpCoordPoly_pow_coeff_mem_Q_pow N hx n d
    have hden : n.factorization ℓ * (ℓ - 1) ≤ d :=
      finiteArtinHasse_den_exponent_le (ℓ := ℓ) hn hnd
    have heval_zero :
        F.finiteLogNatDivEvalAtDegree N n d hn
            (((F.finiteArtinHasseExpCoordPoly N x) ^ n).coeff d) hcoeff hden = 0 := by
      rw [finiteLogNatDivEvalAtDegree]
      let s : ℕ := d - n.factorization ℓ * (ℓ - 1)
      have hcoeff_s :
          ((F.finiteArtinHasseExpCoordPoly N x) ^ n).coeff d ∈
            F.Q ^ (n.factorization ℓ * (ℓ - 1) + s) := by
        simpa [s, Nat.add_sub_of_le hden] using hcoeff
      have hzero_s : (0 : 𝓞 R') ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + s) :=
        zero_mem _
      change F.finiteLogNatDivEval N n s hn
          (((F.finiteArtinHasseExpCoordPoly N x) ^ n).coeff d) hcoeff_s = 0
      calc
        F.finiteLogNatDivEval N n s hn
            (((F.finiteArtinHasseExpCoordPoly N x) ^ n).coeff d) hcoeff_s
            = F.finiteLogNatDivEval N n s hn 0 hzero_s :=
                F.finiteLogNatDivEval_eq_of_eq hn hcoeff_zero hcoeff_s hzero_s
        _ = 0 := F.finiteLogNatDivEval_zero hn hzero_s
    rw [F.finiteArtinHasseExpCoordLogHomogeneousTerm_eq_signed_eval N n d hx hn hnd]
    rw [heval_zero]
    simp
  · simp [finiteArtinHasseExpCoordLogHomogeneousTerm,
      finiteArtinHasseExpCoordLogHomogeneousCore, hn, hnd]

theorem finiteArtinHasseExpCoordLogHomogeneousTerm_eq_zero_of_cutoff_le_degree
    (N n d : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q)
    (hcut : finiteLogCutoff (ℓ := ℓ) N ≤ d) :
    F.finiteArtinHasseExpCoordLogHomogeneousTerm N n d x hx = 0 := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [finiteArtinHasseExpCoordLogHomogeneousTerm,
      finiteArtinHasseExpCoordLogHomogeneousCore]
  by_cases hnd : n ≤ d
  · have hcoeff : ((F.finiteArtinHasseExpCoordPoly N x) ^ n).coeff d ∈ F.Q ^ d :=
      F.finiteArtinHasseExpCoordPoly_pow_coeff_mem_Q_pow N hx n d
    have hden : n.factorization ℓ * (ℓ - 1) ≤ d :=
      finiteArtinHasse_den_exponent_le (ℓ := ℓ) hn hnd
    rw [F.finiteArtinHasseExpCoordLogHomogeneousTerm_eq_signed_eval N n d hx hn hnd]
    rw [F.finiteLogNatDivEvalAtDegree_eq_zero_of_cutoff_le
      (N := N) (n := n) (d := d) hn hnd hcut hcoeff hden]
    simp
  · simp [finiteArtinHasseExpCoordLogHomogeneousTerm,
      finiteArtinHasseExpCoordLogHomogeneousCore, hn, hnd]

theorem finiteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_sum_Icc
    (N d : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum N d x hx =
      ∑ n ∈ Finset.Icc 1 d,
        F.finiteArtinHasseExpCoordLogHomogeneousTerm N n d x hx := by
  classical
  simpa [finiteArtinHasseExpCoordLogHomogeneousDegreeSum] using
    (Finset.sum_attach (s := Finset.Icc 1 d)
      (f := fun n : ℕ =>
        F.finiteArtinHasseExpCoordLogHomogeneousTerm N n d x hx))

theorem finiteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_zero_of_cutoff_le
    (N d : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q)
    (hcut : finiteLogCutoff (ℓ := ℓ) N ≤ d) :
    F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum N d x hx = 0 := by
  classical
  rw [F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_sum_Icc N d hx]
  refine Finset.sum_eq_zero ?_
  intro n _hn
  exact F.finiteArtinHasseExpCoordLogHomogeneousTerm_eq_zero_of_cutoff_le_degree
    N n d hx hcut

theorem finiteArtinHasseLogTerm_eq_zero_of_cutoff_le_pow
    (N r : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q)
    (hcut : finiteLogCutoff (ℓ := ℓ) N ≤ ℓ ^ r) :
    F.finiteArtinHasseLogTerm N r x hx = 0 := by
  rw [← F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_logTerm N r hx]
  exact F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_zero_of_cutoff_le
    N (ℓ ^ r) hx hcut

theorem finiteLogTerm_finiteArtinHasseExpCoord_eq_homogeneous_cutoff_sum
    (N n : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteLogTerm N n (F.finiteArtinHasseExpCoord N x)
        (F.finiteArtinHasseExpCoord_mem_Q N hx) =
      ∑ d ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N),
        F.finiteArtinHasseExpCoordLogHomogeneousTerm N n d x hx := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [finiteArtinHasseExpCoordLogHomogeneousTerm,
      finiteArtinHasseExpCoordLogHomogeneousCore]
  let P : Polynomial (𝓞 R') := F.finiteArtinHasseExpCoordPoly N x
  let C : ℕ := finiteLogCutoff (ℓ := ℓ) N
  let f : ℕ → 𝓞 R' ⧸ F.Q ^ (N + 1) := fun d =>
    F.finiteArtinHasseExpCoordLogHomogeneousTerm N n d x hx
  have hsupport :
      F.finiteLogTerm N n (F.finiteArtinHasseExpCoord N x)
          (F.finiteArtinHasseExpCoord_mem_Q N hx) =
        ∑ d ∈ (P ^ n).support, f d := by
    simpa [P, f] using
      F.finiteLogTerm_finiteArtinHasseExpCoord_eq_homogeneous_support_sum N n hx hn
  have hsupport_union :
      ∑ d ∈ (P ^ n).support, f d =
        ∑ d ∈ (P ^ n).support ∪ Finset.range C, f d := by
    refine Finset.sum_subset (Finset.subset_union_left) ?_
    intro d _hdUnion hdSupport
    exact F.finiteArtinHasseExpCoordLogHomogeneousTerm_eq_zero_of_not_mem_support
      N n d hx (by simpa [P] using hdSupport)
  have hrange_union :
      ∑ d ∈ Finset.range C, f d =
        ∑ d ∈ (P ^ n).support ∪ Finset.range C, f d := by
    refine Finset.sum_subset (Finset.subset_union_right) ?_
    intro d hdUnion hdRange
    have hcut : C ≤ d :=
      Nat.le_of_not_gt (by
        intro hdlt
        exact hdRange (Finset.mem_range.mpr hdlt))
    exact F.finiteArtinHasseExpCoordLogHomogeneousTerm_eq_zero_of_cutoff_le_degree
      N n d hx (by simpa [C] using hcut)
  calc
    F.finiteLogTerm N n (F.finiteArtinHasseExpCoord N x)
        (F.finiteArtinHasseExpCoord_mem_Q N hx)
        = ∑ d ∈ (P ^ n).support, f d := hsupport
    _ = ∑ d ∈ (P ^ n).support ∪ Finset.range C, f d := hsupport_union
    _ = ∑ d ∈ Finset.range C, f d := hrange_union.symm

theorem finiteLog_finiteArtinHasseExpCoord_eq_homogeneous_degree_sum_range
    (N : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteLog N (F.finiteArtinHasseExpCoord N x)
        (F.finiteArtinHasseExpCoord_mem_Q N hx) =
      ∑ d ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N),
        F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum N d x hx := by
  classical
  let C : ℕ := finiteLogCutoff (ℓ := ℓ) N
  let f : ℕ → ℕ → 𝓞 R' ⧸ F.Q ^ (N + 1) := fun n d =>
    F.finiteArtinHasseExpCoordLogHomogeneousTerm N n d x hx
  have hterm : ∀ n ∈ Finset.range C,
      F.finiteLogTerm N n (F.finiteArtinHasseExpCoord N x)
          (F.finiteArtinHasseExpCoord_mem_Q N hx) =
        ∑ d ∈ Finset.range C, f n d := by
    intro n _hn
    simpa [C, f] using
      F.finiteLogTerm_finiteArtinHasseExpCoord_eq_homogeneous_cutoff_sum N n hx
  have hdegree : ∀ d ∈ Finset.range C,
      ∑ n ∈ Finset.range C, f n d =
        F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum N d x hx := by
    intro d hdC
    have hI_subset : Finset.Icc 1 d ⊆ Finset.range C := by
      intro n hnI
      have hnd : n ≤ d := (Finset.mem_Icc.mp hnI).2
      exact Finset.mem_range.mpr (hnd.trans_lt (Finset.mem_range.mp hdC))
    have hI_to_range :
        ∑ n ∈ Finset.Icc 1 d, f n d =
          ∑ n ∈ Finset.range C, f n d := by
      refine Finset.sum_subset hI_subset ?_
      intro n _hnRange hnI
      by_cases hn0 : n = 0
      · subst n
        simp [f, finiteArtinHasseExpCoordLogHomogeneousTerm,
          finiteArtinHasseExpCoordLogHomogeneousCore]
      · have hnd_not : ¬ n ≤ d := by
          intro hnd
          have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
          exact hnI (Finset.mem_Icc.mpr ⟨hn1, hnd⟩)
        simp [f, finiteArtinHasseExpCoordLogHomogeneousTerm,
          finiteArtinHasseExpCoordLogHomogeneousCore, hn0, hnd_not]
    calc
      ∑ n ∈ Finset.range C, f n d
          = ∑ n ∈ Finset.Icc 1 d, f n d := hI_to_range.symm
      _ = F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum N d x hx := by
          rw [F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_sum_Icc N d hx]
  calc
    F.finiteLog N (F.finiteArtinHasseExpCoord N x)
        (F.finiteArtinHasseExpCoord_mem_Q N hx)
        =
      ∑ n ∈ Finset.range C,
        F.finiteLogTerm N n (F.finiteArtinHasseExpCoord N x)
          (F.finiteArtinHasseExpCoord_mem_Q N hx) := by
        simp [finiteLog, C]
    _ = ∑ n ∈ Finset.range C, ∑ d ∈ Finset.range C, f n d := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        exact hterm n hn
    _ = ∑ d ∈ Finset.range C, ∑ n ∈ Finset.range C, f n d := by
        rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.range C,
        F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum N d x hx := by
        refine Finset.sum_congr rfl ?_
        intro d hd
        exact hdegree d hd

private theorem le_ell_pow_self (r : ℕ) : r ≤ ℓ ^ r := by
  have htwo : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
  have hpow : 2 ^ r ≤ ℓ ^ r := Nat.pow_le_pow_left htwo r
  exact (Nat.le_of_lt r.lt_two_pow_self).trans hpow

theorem finiteArtinHasseLog_eq_homogeneous_degree_sum_range
    (N : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteArtinHasseLog N x hx =
      ∑ d ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N),
        F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum N d x hx := by
  classical
  let C : ℕ := finiteLogCutoff (ℓ := ℓ) N
  let powSet : Finset ℕ := (Finset.range (C + 1)).filter fun r => ℓ ^ r < C
  let logTerm : ℕ → 𝓞 R' ⧸ F.Q ^ (N + 1) := fun r =>
    F.finiteArtinHasseLogTerm N r x hx
  let degreeTerm : ℕ → 𝓞 R' ⧸ F.Q ^ (N + 1) := fun d =>
    F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum N d x hx
  have hNC : N ≤ C := by
    have hell_pos : 1 ≤ ℓ := (Fact.out : Nat.Prime ℓ).pos
    dsimp [C, finiteLogCutoff]
    nlinarith [Nat.mul_le_mul_left (N + 1) hell_pos]
  have hfilter_sum :
      ∑ r ∈ powSet, logTerm r =
        ∑ r ∈ Finset.range (C + 1), logTerm r := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro r hrRange hrFilter
    have hnot_lt : ¬ ℓ ^ r < C := fun hrlt =>
      hrFilter (Finset.mem_filter.mpr ⟨hrRange, hrlt⟩)
    exact F.finiteArtinHasseLogTerm_eq_zero_of_cutoff_le_pow N r hx
      (Nat.le_of_not_gt hnot_lt)
  have hlog_to_degree :
      ∑ r ∈ powSet, logTerm r =
        ∑ r ∈ powSet, degreeTerm (ℓ ^ r) := by
    refine Finset.sum_congr rfl ?_
    intro r _hr
    exact (F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_logTerm N r hx).symm
  have hpow_inj : Set.InjOn (fun r : ℕ => ℓ ^ r) (powSet : Set ℕ) := fun a _ha b _hb hab =>
    Nat.pow_right_injective (Fact.out : Nat.Prime ℓ).two_le hab
  have himage_sum :
      ∑ r ∈ powSet, degreeTerm (ℓ ^ r) =
        ∑ d ∈ powSet.image (fun r : ℕ => ℓ ^ r), degreeTerm d :=
    (Finset.sum_image hpow_inj).symm
  have himage_subset : powSet.image (fun r : ℕ => ℓ ^ r) ⊆ Finset.range C := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨r, hr, rfl⟩
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hr).2
  have himage_to_range :
      ∑ d ∈ powSet.image (fun r : ℕ => ℓ ^ r), degreeTerm d =
        ∑ d ∈ Finset.range C, degreeTerm d := by
    refine Finset.sum_subset himage_subset ?_
    intro d hdRange hdImage
    have hnot_pow : ¬ ∃ r : ℕ, d = ℓ ^ r := by
      rintro ⟨r, rfl⟩
      have hrpow_lt : ℓ ^ r < C := Finset.mem_range.mp hdRange
      have hr_range : r ∈ Finset.range (C + 1) :=
        Finset.mem_range.mpr (by
          have hrle : r ≤ ℓ ^ r := le_ell_pow_self (ℓ := ℓ) r
          omega)
      have hr_powSet : r ∈ powSet := Finset.mem_filter.mpr ⟨hr_range, hrpow_lt⟩
      exact hdImage (Finset.mem_image.mpr ⟨r, hr_powSet, rfl⟩)
    exact F.finiteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_zero_of_not_pow
      N d hx hnot_pow
  calc
    F.finiteArtinHasseLog N x hx
        = ∑ r ∈ Finset.range (C + 1), logTerm r := by
            simpa [C, logTerm] using
              F.finiteArtinHasseLog_eq_sum_range_of_le (N := N) (M := C) hNC hx
    _ = ∑ r ∈ powSet, logTerm r := hfilter_sum.symm
    _ = ∑ r ∈ powSet, degreeTerm (ℓ ^ r) := hlog_to_degree
    _ = ∑ d ∈ powSet.image (fun r : ℕ => ℓ ^ r), degreeTerm d := himage_sum
    _ = ∑ d ∈ Finset.range C, degreeTerm d := himage_to_range

/-- Finite logarithm of the finite Artin-Hasse principal-unit coordinate.  This
is the assembly theorem used to rewrite each downstream Artin-Hasse factor. -/
theorem finiteLog_finiteArtinHasseExpCoord_eq_finiteArtinHasseLog
    (N : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteLog N (F.finiteArtinHasseExpCoord N x)
        (F.finiteArtinHasseExpCoord_mem_Q N hx) =
      F.finiteArtinHasseLog N x hx := by
  rw [F.finiteLog_finiteArtinHasseExpCoord_eq_homogeneous_degree_sum_range N hx]
  exact (F.finiteArtinHasseLog_eq_homogeneous_degree_sum_range N hx).symm

/-- Explicit-argument rewrite form for a single Artin-Hasse factor. -/
theorem finiteLog_finiteArtinHasseExpCoord_factor_eq_finiteArtinHasseLog
    (N : ℕ) (x : 𝓞 R') (hx : x ∈ F.Q) :
    F.finiteLog N (F.finiteArtinHasseExpCoord N x)
        (F.finiteArtinHasseExpCoord_mem_Q N hx) =
      F.finiteArtinHasseLog N x hx :=
  F.finiteLog_finiteArtinHasseExpCoord_eq_finiteArtinHasseLog N hx

/-- Full-setup wrapper for the inverse-series normalization:
`E_N(E_N^{-1}(π)) = 1 + π` in the quotient. -/
theorem artinHasseExp_trunc_eval_inverse_trunc_eval_eq_one_add_pi
    (N : ℕ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        ((PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar) =
      1 + πbar := by
  simpa using
    F.toConcreteStickelbergerSetup.artinHasseExp_trunc_eval_inverse_trunc_eval_eq_one_add_pi
      N

theorem quotient_mk_finiteArtinHasseExp_inverseParameter_eq_one_add_pi
    (N : ℕ) :
    Ideal.Quotient.mk (F.Q ^ (N + 1))
        (F.finiteArtinHasseExp N
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N)) =
      1 + Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π := by
  simpa [finiteArtinHasseExp] using
    (ConcreteStickelbergerSetup.quotient_mk_dworkThetaTrunc_artinHasseAtTo_approx_one_eq_one_add_pi
      F.toConcreteStickelbergerSetup N)

theorem quotient_mk_finiteArtinHasseExpCoord_inverseParameter_eq_pi
    (N : ℕ) :
    Ideal.Quotient.mk (F.Q ^ (N + 1))
        (F.finiteArtinHasseExpCoord N
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N)) =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π := by
  rw [finiteArtinHasseExpCoord, map_sub,
    F.quotient_mk_finiteArtinHasseExp_inverseParameter_eq_one_add_pi N]
  simp

theorem finiteArtinHasseExpCoord_inverseParameter_sub_pi_mem_Q_pow_succ
    (N : ℕ) :
    F.finiteArtinHasseExpCoord N
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) -
        F.π ∈
      F.Q ^ (N + 1) := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [map_sub, F.quotient_mk_finiteArtinHasseExpCoord_inverseParameter_eq_pi N]
  simp

theorem finiteLog_finiteArtinHasseExpCoord_inverseParameter_eq_finiteLog_pi
    (N : ℕ)
    (hδ : artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N ∈ F.Q) :
    F.finiteLog N
        (F.finiteArtinHasseExpCoord N
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N))
        (F.finiteArtinHasseExpCoord_mem_Q N hδ) =
      F.finiteLog N F.π F.π_mem_Q :=
  F.finiteLog_eq_of_sub_mem
    (F.finiteArtinHasseExpCoord_mem_Q N hδ) F.π_mem_Q
    (F.finiteArtinHasseExpCoord_inverseParameter_sub_pi_mem_Q_pow_succ N)

/-- The logarithm target for the inverse Artin-Hasse parameter: if
`h_N = AH_N(δ_N)` with `δ_N = E_N^{-1}(π)`, then `h_N` is the finite logarithm
of `1 + π`. -/
theorem finiteArtinHasseLog_inverseParameter_eq_finiteLog_pi
    (N : ℕ)
    (hδ : artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N ∈ F.Q) :
    F.finiteArtinHasseLog N
        (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) hδ =
      F.finiteLog N F.π F.π_mem_Q := by
  calc
    F.finiteArtinHasseLog N
        (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) hδ
        =
      F.finiteLog N
        (F.finiteArtinHasseExpCoord N
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N))
        (F.finiteArtinHasseExpCoord_mem_Q N hδ) :=
        (F.finiteLog_finiteArtinHasseExpCoord_eq_finiteArtinHasseLog N hδ).symm
    _ = F.finiteLog N F.π F.π_mem_Q :=
        F.finiteLog_finiteArtinHasseExpCoord_inverseParameter_eq_finiteLog_pi N hδ

theorem finiteArtinHasseLog_inverseParameter_eq_finiteLog_pi'
    (N : ℕ) :
    F.finiteArtinHasseLog N
        (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N)
        (by
          simpa using
            artinHasseDworkParameterApproxTo_mem_Q F.toConcreteStickelbergerSetup N) =
      F.finiteLog N F.π F.π_mem_Q :=
  F.finiteArtinHasseLog_inverseParameter_eq_finiteLog_pi N
    (by
      simpa using
        artinHasseDworkParameterApproxTo_mem_Q F.toConcreteStickelbergerSetup N)

/-- The inverse Artin-Hasse logarithm is killed by the `ℓ`-torsion relation on
`Log_N(1 + π)`. -/
theorem finiteArtinHasseLog_inverseParameter_ell_nsmul_eq_zero
    (N : ℕ)
    (hδ : artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N ∈ F.Q) :
    ℓ • F.finiteArtinHasseLog N
        (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) hδ = 0 := by
  rw [F.finiteArtinHasseLog_inverseParameter_eq_finiteLog_pi N hδ]
  exact F.finiteLog_pi_ell_nsmul_eq_zero N

theorem finiteArtinHasseLog_inverseParameter_ell_nsmul_eq_zero'
    (N : ℕ) :
    ℓ • F.finiteArtinHasseLog N
        (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N)
        (by
          simpa using
            artinHasseDworkParameterApproxTo_mem_Q F.toConcreteStickelbergerSetup N) = 0 :=
  F.finiteArtinHasseLog_inverseParameter_ell_nsmul_eq_zero N
    (by
      simpa using
        artinHasseDworkParameterApproxTo_mem_Q F.toConcreteStickelbergerSetup N)

/-- Multiplicative scalar form of
`finiteArtinHasseLog_inverseParameter_ell_nsmul_eq_zero`. -/
theorem finiteArtinHasseLog_inverseParameter_natCast_ell_mul_eq_zero
    (N : ℕ)
    (hδ : artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N ∈ F.Q) :
    (ℓ : 𝓞 R' ⧸ F.Q ^ (N + 1)) *
        F.finiteArtinHasseLog N
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) hδ = 0 := by
  rw [F.finiteArtinHasseLog_inverseParameter_eq_finiteLog_pi N hδ]
  exact F.finiteLog_pi_natCast_ell_mul_eq_zero N

theorem finiteArtinHasseLog_inverseParameter_natCast_ell_mul_eq_zero'
    (N : ℕ) :
    (ℓ : 𝓞 R' ⧸ F.Q ^ (N + 1)) *
        F.finiteArtinHasseLog N
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N)
          (by
            simpa using
              artinHasseDworkParameterApproxTo_mem_Q F.toConcreteStickelbergerSetup N) = 0 :=
  F.finiteArtinHasseLog_inverseParameter_natCast_ell_mul_eq_zero N
    (by
      simpa using
        artinHasseDworkParameterApproxTo_mem_Q F.toConcreteStickelbergerSetup N)

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end

end

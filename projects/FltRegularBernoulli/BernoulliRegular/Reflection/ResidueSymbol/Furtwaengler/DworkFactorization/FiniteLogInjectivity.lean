module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FiniteLogProducts
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Injectivity of the finite logarithm on `1 + Q^2`

This file proves the leading-term argument for the finite logarithm: on
principal-unit coordinates lying in `Q^2`, vanishing of the finite logarithm
modulo `Q^(N+1)` forces the coordinate itself to vanish modulo `Q^(N+1)`.
-/

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

theorem finiteLogTerm_one_eq_mk (N : ℕ) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteLogTerm N 1 x hx =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) x := by
  have h := F.finiteLogTerm_natCast_mul_eq_mk (N := N) (n := 1) (by decide) hx
  simpa using h

theorem finiteLogTerm_mem_map_Q_pow_of_mem_Q_pow {N n s : ℕ} (hn : n ≠ 0)
    {x : 𝓞 R'} (hx : x ∈ F.Q) (hxs : x ∈ F.Q ^ s)
    (hden : n.factorization ℓ * (ℓ - 1) ≤ n * s) :
    F.finiteLogTerm N n x hx ∈
      Ideal.map (Ideal.Quotient.mk (F.Q ^ (N + 1)))
        (F.Q ^ (n * s - n.factorization ℓ * (ℓ - 1))) := by
  let d : ℕ := n.factorization ℓ * (ℓ - 1)
  have hpow_high : x ^ n ∈ F.Q ^ (s * n) := by
    simpa [pow_mul] using Ideal.pow_mem_pow hxs n
  have hpow_high' : x ^ n ∈ F.Q ^ (n * s) := by
    simpa [Nat.mul_comm] using hpow_high
  have hpow_eval : x ^ n ∈ F.Q ^ (d + (n * s - d)) := by
    simpa [d, Nat.add_sub_of_le hden] using hpow_high'
  have hden_n : n.factorization ℓ * (ℓ - 1) ≤ n := by
    have hfac := Nat.factorization_mul_pred_le_pred (ell := ℓ) (n := n)
      (Fact.out : Nat.Prime ℓ) hn
    exact hfac.trans (Nat.sub_le n 1)
  have hcore_eq :
      F.finiteLogTermCore N n x hx =
        F.finiteLogNatDivEval N n (n * s - n.factorization ℓ * (ℓ - 1))
          hn (x ^ n) (by simpa [d] using hpow_eval) := by
    calc
      F.finiteLogTermCore N n x hx =
          F.finiteLogNatDivEvalAtDegree N n n hn (x ^ n) (Ideal.pow_mem_pow hx n)
            hden_n :=
            F.finiteLogTermCore_eq_finiteLogNatDivEvalAtDegree hn hx
      _ =
          F.finiteLogNatDivEval N n (n * s - n.factorization ℓ * (ℓ - 1))
            hn (x ^ n) (by simpa [d] using hpow_eval) :=
            F.finiteLogNatDivEvalAtDegree_eq_finiteLogNatDivEval hn
              (Ideal.pow_mem_pow hx n) hden_n (by simpa [d] using hpow_eval)
  rw [finiteLogTerm, hcore_eq]
  exact
    (Ideal.map (Ideal.Quotient.mk (F.Q ^ (N + 1)))
      (F.Q ^ (n * s - n.factorization ℓ * (ℓ - 1)))).mul_mem_left
        ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1))
        (F.finiteLogNatDivEval_mem_map_Q_pow hn (by simpa [d] using hpow_eval))

private theorem finiteLog_mem_Q_pow_succ_of_order {N s : ℕ}
    {y : 𝓞 R'} (hy : y ∈ F.Q) (hs2 : 2 ≤ s) (hsN : s ≤ N)
    (hys : y ∈ F.Q ^ s) (hlog : F.finiteLog N y hy = 0) :
    y ∈ F.Q ^ (s + 1) := by
  let terms : ℕ → 𝓞 R' ⧸ F.Q ^ (N + 1) :=
    fun n => F.finiteLogTerm N n y hy
  let tailSet : Finset ℕ := (Finset.range (finiteLogCutoff (ℓ := ℓ) N)).erase 1
  let tail : 𝓞 R' ⧸ F.Q ^ (N + 1) := ∑ n ∈ tailSet, terms n
  have hN2 : 2 ≤ N := hs2.trans hsN
  have hcut_one : 1 < finiteLogCutoff (ℓ := ℓ) N := by
    have hell_two : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
    have hNthree : 3 ≤ N + 1 := by omega
    have hmul : 2 * 3 ≤ ℓ * (N + 1) := Nat.mul_le_mul hell_two hNthree
    have hone : 1 < 2 * 3 := by norm_num
    exact hone.trans_le (by simpa [finiteLogCutoff] using hmul)
  have h1mem : 1 ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N) :=
    Finset.mem_range.mpr hcut_one
  have hsplit : terms 1 + tail = 0 := by
    have h := hlog
    rw [finiteLog] at h
    change (∑ n ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N), terms n) = 0 at h
    rw [← Finset.add_sum_erase (Finset.range (finiteLogCutoff (ℓ := ℓ) N)) terms h1mem] at h
    simpa [tail, tailSet] using h
  have hlinear_tail :
      Ideal.Quotient.mk (F.Q ^ (N + 1)) y + tail = 0 := by
    simpa [terms, F.finiteLogTerm_one_eq_mk (N := N) hy] using hsplit
  let I : Ideal (𝓞 R' ⧸ F.Q ^ (N + 1)) :=
    Ideal.map (Ideal.Quotient.mk (F.Q ^ (N + 1))) (F.Q ^ (s + 1))
  have htail_mem : tail ∈ I := by
    refine Ideal.sum_mem _ ?_
    intro n hn_tail
    rcases Finset.mem_erase.mp hn_tail with ⟨hn_ne_one, _hn_range⟩
    by_cases hn0 : n = 0
    · subst n
      simp [terms, I]
    · have hn2 : 2 ≤ n := by omega
      have horder :
          s + 1 ≤ n * s - n.factorization ℓ * (ℓ - 1) := by
        simpa [Nat.mul_comm] using
          Nat.succ_le_mul_sub_pred_mul_factorization
            (ell := ℓ) (n := n) (s := s) (Fact.out : Nat.Prime ℓ) hs2 hn2
      have hden : n.factorization ℓ * (ℓ - 1) ≤ n * s := by omega
      have hterm :=
        F.finiteLogTerm_mem_map_Q_pow_of_mem_Q_pow
          (N := N) (n := n) (s := s) hn0 hy hys hden
      exact (Ideal.map_mono (Ideal.pow_le_pow_right horder)) hterm
  have hmk_mem : Ideal.Quotient.mk (F.Q ^ (N + 1)) y ∈ I := by
    have hmk_eq : Ideal.Quotient.mk (F.Q ^ (N + 1)) y = -tail :=
      eq_neg_of_add_eq_zero_left hlinear_tail
    rw [hmk_eq]
    exact I.neg_mem htail_mem
  have hker_le : F.Q ^ (N + 1) ≤ F.Q ^ (s + 1) :=
    Ideal.pow_le_pow_right (Nat.succ_le_succ hsN)
  exact (Ideal.mem_quotient_iff_mem (I := F.Q ^ (N + 1))
    (J := F.Q ^ (s + 1)) hker_le).1 (by simpa [I] using hmk_mem)

theorem finiteLog_mem_Q_pow_succ_of_mem_Q_sq_of_eq_zero {N : ℕ}
    {y : 𝓞 R'} (hy : y ∈ F.Q) (hy2 : y ∈ F.Q ^ 2)
    (hlog : F.finiteLog N y hy = 0) :
    y ∈ F.Q ^ (N + 1) := by
  classical
  by_cases hsmall : N + 1 ≤ 2
  · exact Ideal.pow_le_pow_right hsmall hy2
  by_contra hnot
  have hN2 : 2 ≤ N := by omega
  let orders : Finset ℕ := (Finset.Icc 2 N).filter fun t => y ∈ F.Q ^ t
  have horders_nonempty : orders.Nonempty := by
    refine ⟨2, ?_⟩
    simp [orders, hN2, hy2]
  let s : ℕ := orders.max' horders_nonempty
  have hs_mem : s ∈ orders := by
    simpa [s] using Finset.max'_mem orders horders_nonempty
  have hs_Icc : s ∈ Finset.Icc 2 N := (Finset.mem_filter.mp hs_mem).1
  have hs2 : 2 ≤ s := (Finset.mem_Icc.mp hs_Icc).1
  have hsN : s ≤ N := (Finset.mem_Icc.mp hs_Icc).2
  have hys : y ∈ F.Q ^ s := (Finset.mem_filter.mp hs_mem).2
  have hmax : ∀ t, t ∈ orders → t ≤ s := by
    intro t ht
    have hle := Finset.le_max' orders t ht
    simpa [s] using hle
  have hysucc_not : y ∉ F.Q ^ (s + 1) := by
    intro hysucc
    by_cases hs_eq : s = N
    · exact hnot (by simpa [hs_eq] using hysucc)
    · have hsucc_le_N : s + 1 ≤ N := by omega
      have hsucc_mem : s + 1 ∈ orders := by
        rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_Icc]
          constructor <;> omega
        · exact hysucc
      have hle : s + 1 ≤ s := hmax (s + 1) hsucc_mem
      omega
  exact hysucc_not
    (F.finiteLog_mem_Q_pow_succ_of_order hy hs2 hsN hys hlog)

theorem finiteLog_mem_Q_pow_succ_of_mem_Q_sq_of_eq_zero' {N : ℕ}
    {y : 𝓞 R'} (hy2 : y ∈ F.Q ^ 2)
    (hlog : F.finiteLog N y (F.Q.pow_le_self (by decide) hy2) = 0) :
    y ∈ F.Q ^ (N + 1) :=
  F.finiteLog_mem_Q_pow_succ_of_mem_Q_sq_of_eq_zero
    (F.Q.pow_le_self (by decide) hy2) hy2 hlog

theorem finiteLog_principalUnit_eq_one_mod_of_mem_Q_sq_of_eq_zero {N : ℕ}
    {u y : 𝓞 R'} (hu : u = 1 + y) (hy : y ∈ F.Q) (hy2 : y ∈ F.Q ^ 2)
    (hlog : F.finiteLog N y hy = 0) :
    Ideal.Quotient.mk (F.Q ^ (N + 1)) u = 1 := by
  have hyN := F.finiteLog_mem_Q_pow_succ_of_mem_Q_sq_of_eq_zero hy hy2 hlog
  have hy_zero : Ideal.Quotient.mk (F.Q ^ (N + 1)) y = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hyN
  rw [hu]
  simp [hy_zero]

theorem finiteLog_principalUnit_eq_one_mod_of_mem_Q_sq_of_eq_zero' {N : ℕ}
    {u y : 𝓞 R'} (hu : u = 1 + y) (hy2 : y ∈ F.Q ^ 2)
    (hlog : F.finiteLog N y (F.Q.pow_le_self (by decide) hy2) = 0) :
    Ideal.Quotient.mk (F.Q ^ (N + 1)) u = 1 :=
  F.finiteLog_principalUnit_eq_one_mod_of_mem_Q_sq_of_eq_zero hu
    (F.Q.pow_le_self (by decide) hy2) hy2 hlog

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
module

public import BernoulliRegular.CyclotomicUnits.DworkParameter.Part3

@[expose] public section

noncomputable section

open scoped NumberField
open PowerSeries

namespace BernoulliRegular
namespace CyclotomicUnits
namespace PadicLogSetup
namespace DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local instance : CharZero (ValuedCompletion p K) :=
  algebraRat.charZero (ValuedCompletion p K)

theorem samePrimeFiniteLogProductHomogeneousGrid_degree_sub_eq_zero (N d : ℕ)
    (hd : d ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) N))
    {x y : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hy : y ∈ lambdaIdeal p K) :
    (∑ n ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) N),
      ((if hn : n = 0 then 0 else
        ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
          (if hnd : n ≤ d then
            samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
              (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).coeff d)
              (samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
                (p := p) (K := K) hx hy n d)
              (samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd)
          else 0)) -
      (if hn : n = 0 then 0 else
        ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
          (if hnd : n ≤ d then
            samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
              (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x 0) ^ n).coeff d)
              (samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
                (p := p) (K := K) hx (zero_mem (lambdaIdeal p K)) n d)
              (samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd)
          else 0)) -
      (if hn : n = 0 then 0 else
        ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
          (if hnd : n ≤ d then
            samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
              (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) y 0) ^ n).coeff d)
              (samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
                (p := p) (K := K) hy (zero_mem (lambdaIdeal p K)) n d)
              (samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd)
          else 0)))) = 0 := by
  classical
  let C : ℕ := samePrimeFiniteLogCutoff (p := p) N
  have hdC : d < C := by simpa [C] using hd
  have hsubset : Finset.Icc 1 d ⊆ Finset.range C := fun n hnI =>
    Finset.mem_range.mpr (lt_of_le_of_lt (Finset.mem_Icc.mp hnI).2 hdC)
  let f : ℕ → ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) := fun n =>
      (if hn : n = 0 then 0 else
        ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
          (if hnd : n ≤ d then
            samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
              (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).coeff d)
              (samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
                (p := p) (K := K) hx hy n d)
              (samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd)
          else 0)) -
      (if hn : n = 0 then 0 else
        ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
          (if hnd : n ≤ d then
            samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
              (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x 0) ^ n).coeff d)
              (samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
                (p := p) (K := K) hx (zero_mem (lambdaIdeal p K)) n d)
              (samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd)
          else 0)) -
      (if hn : n = 0 then 0 else
        ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
          (if hnd : n ≤ d then
            samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
              (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) y 0) ^ n).coeff d)
              (samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
                (p := p) (K := K) hy (zero_mem (lambdaIdeal p K)) n d)
              (samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd)
          else 0))
  have hzero_out : ∀ n ∈ Finset.range C, n ∉ Finset.Icc 1 d → f n = 0 := by
    intro n hnC hnI
    by_cases hn0 : n = 0
    · simp [f, hn0]
    · have hnle0 : ¬ n ≤ d := by
        intro hnd
        have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
        exact hnI (Finset.mem_Icc.mpr ⟨hn1, hnd⟩)
      simp [f, hn0, hnle0]
  calc
    (∑ n ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) N), f n)
        = ∑ n ∈ Finset.Icc 1 d, f n := by
        rw [show Finset.range (samePrimeFiniteLogCutoff (p := p) N) =
          Finset.range C by rfl]
        exact (Finset.sum_subset hsubset hzero_out).symm
    _ =
      ∑ a ∈ (Finset.Icc 1 d).attach,
        samePrimeNatDivEvalAtDegree (p := p) (K := K) N a.1 d
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            exact Nat.ne_zero_of_lt ha1)
          (samePrimeFiniteLogAdditivityNumerator (p := p) (K := K) x y d a.1)
          (samePrimeFiniteLogAdditivityNumerator_mem_lambdaIdeal_pow
            (p := p) (K := K) hx hy d a.1)
          (by
            have ha1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
            have had : a.1 ≤ d := (Finset.mem_Icc.mp a.2).2
            exact samePrimeFiniteLogAdditivity_den_exponent_le (p := p)
              (Nat.ne_zero_of_lt ha1) had) := by
        rw [← Finset.sum_attach]
        refine Finset.sum_congr rfl ?_
        intro a _ha
        have hn1 : 1 ≤ a.1 := (Finset.mem_Icc.mp a.2).1
        have hnd : a.1 ≤ d := (Finset.mem_Icc.mp a.2).2
        have hn0 : a.1 ≠ 0 := Nat.ne_zero_of_lt hn1
        simp [f, hn0, hnd,
          samePrimeFiniteLogAdditivity_term_eq (p := p) (K := K)
            N d a.1 hn0 hnd hx hy]
    _ = 0 := samePrimeFiniteLogAdditivity_degree_sum_eq_zero (p := p) (K := K) N d hx hy

theorem samePrimeFiniteLogProductHomogeneousGrid_add (N : ℕ)
    {x y : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hy : y ∈ lambdaIdeal p K) :
    samePrimeFiniteLogProductHomogeneousGrid (p := p) (K := K) N x y hx hy =
      samePrimeFiniteLogProductHomogeneousGrid (p := p) (K := K) N x 0 hx
        (zero_mem (lambdaIdeal p K)) +
        samePrimeFiniteLogProductHomogeneousGrid (p := p) (K := K) N y 0 hy
          (zero_mem (lambdaIdeal p K)) := by
  classical
  rw [← sub_eq_zero]
  rw [sub_add_eq_sub_sub]
  calc
    samePrimeFiniteLogProductHomogeneousGrid (p := p) (K := K) N x y hx hy -
      samePrimeFiniteLogProductHomogeneousGrid (p := p) (K := K) N x 0 hx
        (zero_mem (lambdaIdeal p K)) -
        samePrimeFiniteLogProductHomogeneousGrid (p := p) (K := K) N y 0 hy
          (zero_mem (lambdaIdeal p K))
        =
      ∑ d ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) N),
        ∑ n ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) N),
          ((if hn : n = 0 then 0 else
            ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
              (if hnd : n ≤ d then
                samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
                  (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).coeff d)
                  (samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
                    (p := p) (K := K) hx hy n d)
                  (samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd)
              else 0)) -
          (if hn : n = 0 then 0 else
            ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
              (if hnd : n ≤ d then
                samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
                  (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x 0) ^ n).coeff d)
                  (samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
                    (p := p) (K := K) hx (zero_mem (lambdaIdeal p K)) n d)
                  (samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd)
              else 0)) -
          (if hn : n = 0 then 0 else
            ((-1 : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)) ^ (n + 1)) *
              (if hnd : n ≤ d then
                samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
                  (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) y 0) ^ n).coeff d)
                  (samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
                    (p := p) (K := K) hy (zero_mem (lambdaIdeal p K)) n d)
                  (samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd)
              else 0))) := by
        rw [samePrimeFiniteLogProductHomogeneousGrid_eq_degree_sum (p := p) (K := K) N hx hy]
        rw [samePrimeFiniteLogProductHomogeneousGrid_eq_degree_sum
          (p := p) (K := K) N hx (zero_mem (lambdaIdeal p K))]
        rw [samePrimeFiniteLogProductHomogeneousGrid_eq_degree_sum
          (p := p) (K := K) N hy (zero_mem (lambdaIdeal p K))]
        simp only [Finset.sum_sub_distrib]
    _ = 0 :=
        Finset.sum_eq_zero fun d hd =>
          samePrimeFiniteLogProductHomogeneousGrid_degree_sub_eq_zero
            (p := p) (K := K) N d hd hx hy

theorem samePrimeFiniteLogProductHomogeneousGrid_term_eq (N n : ℕ) (hn : n ≠ 0)
    {x y : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hy : y ∈ lambdaIdeal p K)
    (hden0 : n.factorization p * (p - 1) ≤ n) :
    samePrimeNatDivEvalAtDegree (p := p) (K := K) N n n hn
        ((samePrimeFiniteLogProductCoord (p := p) (K := K) x y) ^ n)
        (Ideal.pow_mem_pow (samePrimeFiniteLogProductCoord_mem_lambdaIdeal
          (p := p) (K := K) hx hy) n)
        hden0
      =
    ∑ d ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) N),
      if hnd : n ≤ d then
        samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
          (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).coeff d)
          (samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
            (p := p) (K := K) hx hy n d)
          (samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd)
      else 0 := by
  classical
  let P : Polynomial (ValuedIntegerRing p K) :=
    (samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n
  let C : ℕ := samePrimeFiniteLogCutoff (p := p) N
  let den : ℕ := n.factorization p * (p - 1)
  let s : ℕ := n - den
  have hdenn : den ≤ n := by
    simpa [den] using hden0
  have hcoord_sum :
      (samePrimeFiniteLogProductCoord (p := p) (K := K) x y) ^ n =
        ∑ d ∈ Finset.range (P.natDegree + 1),
          if n ≤ d then P.coeff d else 0 := by
    calc
      (samePrimeFiniteLogProductCoord (p := p) (K := K) x y) ^ n = P.eval 1 := by
        simpa [P] using
          (samePrimeFiniteLogProductArgPoly_pow_eval_one (p := p) (K := K) n x y).symm
      _ = ∑ d ∈ Finset.range (P.natDegree + 1), P.coeff d := by
        rw [Polynomial.eval_eq_sum_range]
        simp
      _ = ∑ d ∈ Finset.range (P.natDegree + 1),
          if n ≤ d then P.coeff d else 0 := by
        refine Finset.sum_congr rfl ?_
        intro d _hd
        by_cases hnd : n ≤ d
        · simp [hnd]
        · have hdn : d < n := Nat.lt_of_not_ge hnd
          have hcoeff : P.coeff d = 0 := by
            simpa [P] using
              samePrimeFiniteLogProductArgPoly_pow_coeff_eq_zero_of_lt
                (p := p) (K := K) x y hdn
          simp [hnd, hcoeff]
  have hcoeff_mem_n : ∀ d, (if n ≤ d then P.coeff d else 0) ∈
      (lambdaIdeal p K) ^ n := by
    intro d
    by_cases hnd : n ≤ d
    · have hd_mem : P.coeff d ∈ (lambdaIdeal p K) ^ d := by
        simpa [P] using
          samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
            (p := p) (K := K) hx hy n d
      simpa [hnd] using Ideal.pow_le_pow_right hnd hd_mem
    · simp [hnd]
  have hcoeff_mem_s :
      ∀ d, (if n ≤ d then P.coeff d else 0) ∈ (lambdaIdeal p K) ^ (den + s) := by
    intro d
    simpa [s, Nat.add_sub_of_le hdenn] using hcoeff_mem_n d
  have hsum_mem_n :
      (∑ d ∈ Finset.range (P.natDegree + 1), if n ≤ d then P.coeff d else 0) ∈
        (lambdaIdeal p K) ^ n :=
    Ideal.sum_mem _ fun d _hd => hcoeff_mem_n d
  have hsum_mem_s :
      (∑ d ∈ Finset.range (P.natDegree + 1), if n ≤ d then P.coeff d else 0) ∈
        (lambdaIdeal p K) ^ (den + s) := by
    simpa [s, Nat.add_sub_of_le hdenn] using hsum_mem_n
  let g : ℕ → ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) := fun d =>
    if hnd : n ≤ d then
      samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn (P.coeff d)
        (by
          simpa [P] using
            samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
              (p := p) (K := K) hx hy n d)
        (by
          simpa [den] using samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd)
    else 0
  have hsplit :
      samePrimeNatDivEvalAtDegree (p := p) (K := K) N n n hn
        ((samePrimeFiniteLogProductCoord (p := p) (K := K) x y) ^ n)
        (Ideal.pow_mem_pow (samePrimeFiniteLogProductCoord_mem_lambdaIdeal
          (p := p) (K := K) hx hy) n)
        hden0
        =
      ∑ d ∈ Finset.range (P.natDegree + 1), g d := by
    calc
      samePrimeNatDivEvalAtDegree (p := p) (K := K) N n n hn
        ((samePrimeFiniteLogProductCoord (p := p) (K := K) x y) ^ n)
        (Ideal.pow_mem_pow (samePrimeFiniteLogProductCoord_mem_lambdaIdeal
          (p := p) (K := K) hx hy) n)
        hden0
          =
        samePrimeNatDivEval (p := p) (K := K) N n s hn
          ((samePrimeFiniteLogProductCoord (p := p) (K := K) x y) ^ n)
          (by
            simpa [den, s, Nat.add_sub_of_le hdenn] using
              Ideal.pow_mem_pow
                (samePrimeFiniteLogProductCoord_mem_lambdaIdeal (p := p) (K := K) hx hy) n) := by
        rw [samePrimeNatDivEvalAtDegree]
      _ =
        samePrimeNatDivEval (p := p) (K := K) N n s hn
          (∑ d ∈ Finset.range (P.natDegree + 1), if n ≤ d then P.coeff d else 0)
          hsum_mem_s :=
        samePrimeNatDivEval_eq_of_eq (p := p) (K := K) (N := N)
          (n := n) (s := s) hn hcoord_sum
          (by
            simpa [den, s, Nat.add_sub_of_le hdenn] using
              Ideal.pow_mem_pow
                (samePrimeFiniteLogProductCoord_mem_lambdaIdeal (p := p) (K := K) hx hy) n)
          hsum_mem_s
      _ =
        ∑ d ∈ Finset.range (P.natDegree + 1),
          samePrimeNatDivEval (p := p) (K := K) N n s hn
            (if n ≤ d then P.coeff d else 0) (hcoeff_mem_s d) := by
        rw [samePrimeNatDivEval_sum (p := p) (K := K) (N := N) (n := n) (s := s)
          hn (Finset.range (P.natDegree + 1))
          (fun d => if n ≤ d then P.coeff d else 0) hcoeff_mem_s hsum_mem_s]
      _ = ∑ d ∈ Finset.range (P.natDegree + 1), g d := by
        refine Finset.sum_congr rfl ?_
        intro d _hd
        by_cases hnd : n ≤ d
        · have hmem_d : P.coeff d ∈ (lambdaIdeal p K) ^ d := by
            simpa [P] using
              samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
                (p := p) (K := K) hx hy n d
          have hden_d : den ≤ d := by
            simpa [den] using samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd
          have hmem_s : P.coeff d ∈ (lambdaIdeal p K) ^ (den + s) := by
            simpa [hnd] using hcoeff_mem_s d
          simp only [g, hnd, ↓reduceIte, ↓reduceDIte]
          exact (samePrimeNatDivEvalAtDegree_eq_samePrimeNatDivEval
            (p := p) (K := K) (N := N) (n := n) (d := d) (s := s)
            hn hmem_d hden_d hmem_s).symm
        · have hzero_s : (0 : ValuedIntegerRing p K) ∈ (lambdaIdeal p K) ^ (den + s) :=
            zero_mem _
          simp [g, hnd,
            samePrimeNatDivEval_zero (p := p) (K := K)
              (N := N) (n := n) (s := s) hn hzero_s]
  let M : ℕ := max (P.natDegree + 1) C
  have hPsubset : Finset.range (P.natDegree + 1) ⊆ Finset.range M := fun d hd =>
    Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hd) (Nat.le_max_left _ _))
  have hCsubset : Finset.range C ⊆ Finset.range M := fun d hd =>
    Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hd) (Nat.le_max_right _ _))
  have hP_to_M :
      (∑ d ∈ Finset.range (P.natDegree + 1), g d) =
        ∑ d ∈ Finset.range M, g d :=
    Finset.sum_subset hPsubset (by
      intro d _hdM hdP
      by_cases hnd : n ≤ d
      · have hd_gt : P.natDegree < d := by
          have hd_not_lt : ¬ d < P.natDegree + 1 := fun hdlt =>
            hdP (Finset.mem_range.mpr hdlt)
          have hle : P.natDegree + 1 ≤ d := Nat.le_of_not_gt hd_not_lt
          omega
        have hcoeff : P.coeff d = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hd_gt
        have hden_d : den ≤ d := by
          simpa [den] using samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd
        simpa [g, hnd, hcoeff] using
          samePrimeNatDivEvalAtDegree_zero (p := p) (K := K)
            (N := N) (n := n) (d := d) hn (zero_mem _) hden_d
      · simp [g, hnd])
  have hC_to_M :
      (∑ d ∈ Finset.range C, g d) =
        ∑ d ∈ Finset.range M, g d :=
    Finset.sum_subset hCsubset (by
      intro d _hdM hdC
      have hcut : C ≤ d :=
        Nat.le_of_not_gt (mt Finset.mem_range.mpr hdC)
      by_cases hnd : n ≤ d
      · have hmem_d : P.coeff d ∈ (lambdaIdeal p K) ^ d := by
          simpa [P] using
            samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
              (p := p) (K := K) hx hy n d
        have hden_d : den ≤ d := by
          simpa [den] using samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd
        simpa [g, C, hnd] using
          samePrimeNatDivEvalAtDegree_eq_zero_of_cutoff_le
            (p := p) (K := K) (N := N) (n := n) (d := d)
            hn hnd hcut hmem_d hden_d
      · simp [g, hnd])
  calc
    samePrimeNatDivEvalAtDegree (p := p) (K := K) N n n hn
        ((samePrimeFiniteLogProductCoord (p := p) (K := K) x y) ^ n)
        (Ideal.pow_mem_pow (samePrimeFiniteLogProductCoord_mem_lambdaIdeal
          (p := p) (K := K) hx hy) n)
        hden0
        = ∑ d ∈ Finset.range (P.natDegree + 1), g d := hsplit
    _ = ∑ d ∈ Finset.range C, g d := hP_to_M.trans hC_to_M.symm
    _ =
      ∑ d ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) N),
        if hnd : n ≤ d then
          samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
            (((samePrimeFiniteLogProductArgPoly (p := p) (K := K) x y) ^ n).coeff d)
            (samePrimeFiniteLogProductArgPoly_pow_coeff_mem_lambdaIdeal_pow
              (p := p) (K := K) hx hy n d)
            (samePrimeFiniteLogAdditivity_den_exponent_le (p := p) hn hnd)
        else 0 := by
      rfl

theorem samePrimeFiniteLog_eq_productHomogeneousGrid (N : ℕ)
    {x y : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hy : y ∈ lambdaIdeal p K) :
    samePrimeFiniteLog (p := p) (K := K) N
        (samePrimeFiniteLogProductCoord (p := p) (K := K) x y)
        (samePrimeFiniteLogProductCoord_mem_lambdaIdeal (p := p) (K := K) hx hy) =
      samePrimeFiniteLogProductHomogeneousGrid (p := p) (K := K) N x y hx hy := by
  classical
  rw [samePrimeFiniteLog_eq_samePrimeFiniteLogLocalizedPolynomial (p := p) (K := K)]
  unfold samePrimeFiniteLogLocalizedPolynomial samePrimeFiniteLogProductHomogeneousGrid
  refine Finset.sum_congr rfl ?_
  intro n _hnC
  by_cases hn0 : n = 0
  · simp [samePrimeFiniteLogLocalizedTerm, hn0]
  · rw [samePrimeFiniteLogLocalizedTerm, dif_neg hn0]
    rw [samePrimeFiniteLogProductHomogeneousGrid_term_eq
      (p := p) (K := K) N n hn0 hx hy]
    rw [dif_neg hn0]

theorem samePrimeFiniteLog_add_add_mul (N : ℕ)
    {x y : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hy : y ∈ lambdaIdeal p K) :
    samePrimeFiniteLog (p := p) (K := K) N
        (samePrimeFiniteLogProductCoord (p := p) (K := K) x y)
        (samePrimeFiniteLogProductCoord_mem_lambdaIdeal (p := p) (K := K) hx hy) =
      samePrimeFiniteLog (p := p) (K := K) N x hx +
        samePrimeFiniteLog (p := p) (K := K) N y hy := by
  calc
    samePrimeFiniteLog (p := p) (K := K) N
        (samePrimeFiniteLogProductCoord (p := p) (K := K) x y)
        (samePrimeFiniteLogProductCoord_mem_lambdaIdeal (p := p) (K := K) hx hy)
        =
      samePrimeFiniteLogProductHomogeneousGrid (p := p) (K := K) N x y hx hy :=
        samePrimeFiniteLog_eq_productHomogeneousGrid (p := p) (K := K) N hx hy
    _ =
      samePrimeFiniteLogProductHomogeneousGrid (p := p) (K := K) N x 0 hx
        (zero_mem (lambdaIdeal p K)) +
        samePrimeFiniteLogProductHomogeneousGrid (p := p) (K := K) N y 0 hy
          (zero_mem (lambdaIdeal p K)) :=
        samePrimeFiniteLogProductHomogeneousGrid_add (p := p) (K := K) N hx hy
    _ =
      samePrimeFiniteLog (p := p) (K := K) N
          (samePrimeFiniteLogProductCoord (p := p) (K := K) x 0)
          (samePrimeFiniteLogProductCoord_mem_lambdaIdeal
            (p := p) (K := K) hx (zero_mem (lambdaIdeal p K))) +
        samePrimeFiniteLog (p := p) (K := K) N
          (samePrimeFiniteLogProductCoord (p := p) (K := K) y 0)
          (samePrimeFiniteLogProductCoord_mem_lambdaIdeal
            (p := p) (K := K) hy (zero_mem (lambdaIdeal p K))) := by
        rw [← samePrimeFiniteLog_eq_productHomogeneousGrid
          (p := p) (K := K) N hx (zero_mem (lambdaIdeal p K))]
        rw [← samePrimeFiniteLog_eq_productHomogeneousGrid
          (p := p) (K := K) N hy (zero_mem (lambdaIdeal p K))]
    _ = samePrimeFiniteLog (p := p) (K := K) N x hx +
        samePrimeFiniteLog (p := p) (K := K) N y hy := by
        simp [samePrimeFiniteLogProductCoord]

/-- Truncated same-prime Artin--Hasse exponential through degree `N`. -/
def samePrimeFiniteArtinHasseExp (N : ℕ)
    (x : ValuedIntegerRing p K) : ValuedIntegerRing p K :=
  (PowerSeries.trunc (N + 1) (integralExpSeries p K)).eval₂
    (RingHom.id (ValuedIntegerRing p K)) x

/-- Principal-unit coordinate `E_N(x) - 1` for the same-prime finite
Artin--Hasse exponential. -/
def samePrimeFiniteArtinHasseExpCoord (N : ℕ)
    (x : ValuedIntegerRing p K) : ValuedIntegerRing p K :=
  samePrimeFiniteArtinHasseExp (p := p) (K := K) N x - 1

@[simp] theorem samePrimeFiniteArtinHasseExpCoord_add_one
    (N : ℕ) (x : ValuedIntegerRing p K) :
    samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N x + 1 =
      samePrimeFiniteArtinHasseExp (p := p) (K := K) N x := by
  simp [samePrimeFiniteArtinHasseExpCoord]

theorem samePrimeFiniteArtinHasseExpCoord_eq_positive_sum
    (N : ℕ) (x : ValuedIntegerRing p K) :
    samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N x =
      ∑ n ∈ Finset.range N,
        (PowerSeries.coeff (R := ValuedIntegerRing p K) (n + 1))
            (integralExpSeries p K) * x ^ (n + 1) := by
  rw [samePrimeFiniteArtinHasseExpCoord, samePrimeFiniteArtinHasseExp]
  rw [PowerSeries.eval₂_trunc_eq_sum_range, Finset.sum_range_succ']
  have hcoeff0 :
      (PowerSeries.coeff (R := ValuedIntegerRing p K) 0)
          (integralExpSeries p K) = 1 := by
    ext
    simp [integralExpSeries, rIntegralRatToValuedInteger,
      rIntegralRatToValuedCompletion, FormalDwork.expSeries]
  simp [hcoeff0]

theorem samePrimeFiniteArtinHasseExpCoord_mem_lambdaIdeal
    (N : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N x ∈ lambdaIdeal p K := by
  classical
  rw [samePrimeFiniteArtinHasseExpCoord_eq_positive_sum]
  refine Ideal.sum_mem _ ?_
  intro n _hn
  have hpow : x ^ (n + 1) ∈ lambdaIdeal p K :=
    Ideal.pow_le_self (Nat.succ_ne_zero n)
      (Ideal.pow_mem_pow hx (n + 1))
  exact (lambdaIdeal p K).mul_mem_left _ hpow

/-- Homogeneous bookkeeping polynomial for the same-prime finite
Artin--Hasse principal-unit coordinate. -/
def samePrimeFiniteArtinHasseExpCoordPoly
    (N : ℕ) (x : ValuedIntegerRing p K) :
    Polynomial (ValuedIntegerRing p K) :=
  ∑ n ∈ Finset.range N,
    Polynomial.monomial (n + 1)
      ((PowerSeries.coeff (R := ValuedIntegerRing p K) (n + 1))
        (integralExpSeries p K) * x ^ (n + 1))

theorem samePrimeFiniteArtinHasseExpCoordPoly_eval_one
    (N : ℕ) (x : ValuedIntegerRing p K) :
    (samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x).eval 1 =
      samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N x := by
  rw [samePrimeFiniteArtinHasseExpCoord_eq_positive_sum]
  simp [samePrimeFiniteArtinHasseExpCoordPoly, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial]

theorem samePrimeFiniteArtinHasseExpCoordPoly_coeff_mem_lambdaIdeal_pow
    (N : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) (d : ℕ) :
    (samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x).coeff d ∈
      (lambdaIdeal p K) ^ d := by
  classical
  rw [samePrimeFiniteArtinHasseExpCoordPoly, Polynomial.finsetSum_coeff]
  refine Ideal.sum_mem _ ?_
  intro n _hn
  by_cases hnd : n + 1 = d
  · subst d
    simpa [Polynomial.coeff_monomial] using
      (((lambdaIdeal p K) ^ (n + 1)).mul_mem_left _
        (Ideal.pow_mem_pow hx (n + 1)))
  · simp [Polynomial.coeff_monomial, hnd]

theorem samePrimeFiniteArtinHasseExpCoordPoly_coeff_zero
    (N : ℕ) (x : ValuedIntegerRing p K) :
    (samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x).coeff 0 = 0 := by
  classical
  simp [samePrimeFiniteArtinHasseExpCoordPoly, Polynomial.coeff_monomial]

theorem samePrimeFiniteArtinHasseExpCoordPoly_coeff_eq_of_pos_le
    (N d : ℕ) (x : ValuedIntegerRing p K) (hd0 : d ≠ 0) (hdN : d ≤ N) :
    (samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x).coeff d =
      (PowerSeries.coeff (R := ValuedIntegerRing p K) d) (integralExpSeries p K) *
        x ^ d := by
  classical
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have hdmem : d - 1 ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  rw [samePrimeFiniteArtinHasseExpCoordPoly, Polynomial.finsetSum_coeff]
  calc
    (∑ n ∈ Finset.range N,
        (Polynomial.monomial (n + 1)
          ((PowerSeries.coeff (R := ValuedIntegerRing p K) (n + 1))
            (integralExpSeries p K) * x ^ (n + 1))).coeff d)
        =
      (Polynomial.monomial ((d - 1) + 1)
          ((PowerSeries.coeff (R := ValuedIntegerRing p K) ((d - 1) + 1))
            (integralExpSeries p K) * x ^ ((d - 1) + 1))).coeff d := by
        refine Finset.sum_eq_single (d - 1) ?_ ?_
        · intro b hb hbne
          have hbne' : b + 1 ≠ d := by
            intro hbd
            apply hbne
            omega
          simp [Polynomial.coeff_monomial, hbne']
        · intro hnot
          exact False.elim (hnot hdmem)
    _ =
      (PowerSeries.coeff (R := ValuedIntegerRing p K) d) (integralExpSeries p K) *
        x ^ d := by
        have hdsub : (d - 1) + 1 = d := Nat.sub_add_cancel hdpos
        simp [hdsub]

theorem samePrimeFiniteArtinHasseExpCoordPoly_coeff_eq_zero_of_lt
    (N d : ℕ) (x : ValuedIntegerRing p K) (hdN : N < d) :
    (samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x).coeff d = 0 := by
  classical
  rw [samePrimeFiniteArtinHasseExpCoordPoly, Polynomial.finsetSum_coeff]
  exact Finset.sum_eq_zero fun n hn =>
    by
      have hnlt : n < N := Finset.mem_range.mp hn
      have hne : n + 1 ≠ d := by omega
      simp [Polynomial.coeff_monomial, hne]

theorem samePrimeFiniteArtinHasseExpCoordPoly_pow_coeff_mem_lambdaIdeal_pow
    (N : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (n d : ℕ) :
    ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff d ∈
      (lambdaIdeal p K) ^ d := by
  induction n generalizing d with
  | zero =>
      by_cases hd : d = 0
      · subst d
        simp
      · simp [Polynomial.coeff_one, hd]
  | succ n ih =>
      rw [pow_succ, Polynomial.coeff_mul]
      refine Ideal.sum_mem _ ?_
      intro a ha
      have hsum : a.1 + a.2 = d := by
        simpa using (Finset.mem_antidiagonal.mp ha)
      have hleft :
          ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff a.1 ∈
            (lambdaIdeal p K) ^ a.1 :=
        ih a.1
      have hright :
          (samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x).coeff a.2 ∈
            (lambdaIdeal p K) ^ a.2 :=
        samePrimeFiniteArtinHasseExpCoordPoly_coeff_mem_lambdaIdeal_pow
          (p := p) (K := K) N hx a.2
      have hmul :
          ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff a.1 *
              (samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x).coeff a.2 ∈
            (lambdaIdeal p K) ^ (a.1 + a.2) := by
        simpa [pow_add] using Ideal.mul_mem_mul hleft hright
      simpa [hsum] using hmul

theorem samePrimeFiniteArtinHasseExpCoordPoly_coeff_sub_coeff_mem_lambdaIdeal_pow
    (N M d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hNM : N ≤ M) :
    (samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x).coeff d -
        (samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) M x).coeff d ∈
      (lambdaIdeal p K) ^ (if d ≤ N then N + 1 + d else d) := by
  by_cases hdN : d ≤ N
  · rw [if_pos hdN]
    by_cases hd0 : d = 0
    · subst d
      simp [samePrimeFiniteArtinHasseExpCoordPoly_coeff_zero]
    · have hdM : d ≤ M := hdN.trans hNM
      rw [samePrimeFiniteArtinHasseExpCoordPoly_coeff_eq_of_pos_le
          (p := p) (K := K) N d x hd0 hdN,
        samePrimeFiniteArtinHasseExpCoordPoly_coeff_eq_of_pos_le
          (p := p) (K := K) M d x hd0 hdM, sub_self]
      exact zero_mem _
  · rw [if_neg hdN]
    have hNmem :
        (samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x).coeff d ∈
          (lambdaIdeal p K) ^ d :=
      samePrimeFiniteArtinHasseExpCoordPoly_coeff_mem_lambdaIdeal_pow
        (p := p) (K := K) N hx d
    have hMmem :
        (samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) M x).coeff d ∈
          (lambdaIdeal p K) ^ d :=
      samePrimeFiniteArtinHasseExpCoordPoly_coeff_mem_lambdaIdeal_pow
        (p := p) (K := K) M hx d
    exact ((lambdaIdeal p K) ^ d).sub_mem hNmem hMmem

theorem samePrimeFiniteArtinHasseExpCoordPoly_pow_coeff_sub_coeff_mem_lambdaIdeal_pow
    (N M n d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hNM : N ≤ M) :
    ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff d -
        ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) M x) ^ n).coeff d ∈
      (lambdaIdeal p K) ^ (if d < N + n then N + 1 + d else d) := by
  classical
  induction n generalizing d with
  | zero =>
      simp
  | succ n ih =>
      let PN : Polynomial (ValuedIntegerRing p K) :=
        samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x
      let PM : Polynomial (ValuedIntegerRing p K) :=
        samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) M x
      rw [pow_succ, pow_succ, Polynomial.coeff_mul, Polynomial.coeff_mul]
      rw [← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ ?_
      intro a ha
      have hsum : a.1 + a.2 = d := by
        simpa using Finset.mem_antidiagonal.mp ha
      by_cases ha2z : a.2 = 0
      · simp [ha2z, samePrimeFiniteArtinHasseExpCoordPoly_coeff_zero]
      · have hPN₂ : PN.coeff a.2 ∈ (lambdaIdeal p K) ^ a.2 := by
          simpa [PN] using
            samePrimeFiniteArtinHasseExpCoordPoly_coeff_mem_lambdaIdeal_pow
              (p := p) (K := K) N hx a.2
        have hPMpow₁ :
            (PM ^ n).coeff a.1 ∈ (lambdaIdeal p K) ^ a.1 := by
          simpa [PM] using
            samePrimeFiniteArtinHasseExpCoordPoly_pow_coeff_mem_lambdaIdeal_pow
              (p := p) (K := K) M hx n a.1
        have hdiff₁ :
            (PN ^ n).coeff a.1 - (PM ^ n).coeff a.1 ∈
              (lambdaIdeal p K) ^
                (if a.1 < N + n then N + 1 + a.1 else a.1) := by
          simpa [PN, PM] using ih a.1
        have hmul₁ :
            ((PN ^ n).coeff a.1 - (PM ^ n).coeff a.1) * PN.coeff a.2 ∈
              (lambdaIdeal p K) ^
                ((if a.1 < N + n then N + 1 + a.1 else a.1) + a.2) := by
          simpa [pow_add] using Ideal.mul_mem_mul hdiff₁ hPN₂
        have hterm₁ :
            ((PN ^ n).coeff a.1 - (PM ^ n).coeff a.1) * PN.coeff a.2 ∈
              (lambdaIdeal p K) ^ (if d < N + (n + 1) then N + 1 + d else d) := by
          refine Ideal.pow_le_pow_right ?_ hmul₁
          by_cases hdsmall : d < N + (n + 1)
          · have ha1small : a.1 < N + n := by omega
            rw [if_pos hdsmall, if_pos ha1small]
            omega
          · rw [if_neg hdsmall]
            by_cases ha1small : a.1 < N + n
            · rw [if_pos ha1small]
              omega
            · rw [if_neg ha1small]
              omega
        have hterm₂ :
            (PM ^ n).coeff a.1 * (PN.coeff a.2 - PM.coeff a.2) ∈
              (lambdaIdeal p K) ^ (if d < N + (n + 1) then N + 1 + d else d) := by
          by_cases ha1lt : a.1 < n
          · have hzero : (PM ^ n).coeff a.1 = 0 := by
              have h :=
                coeff_pow_coe_eq_zero_of_lt_of_constantCoeff_eq_zero PM
                  (by
                    simpa [PM] using
                      samePrimeFiniteArtinHasseExpCoordPoly_coeff_zero
                        (p := p) (K := K) M x)
                  ha1lt
              simpa [← Polynomial.coe_pow, Polynomial.coeff_coe] using h
            rw [hzero, zero_mul]
            exact zero_mem _
          · have hna1 : n ≤ a.1 := Nat.le_of_not_gt ha1lt
            have hdiff₂ :
                PN.coeff a.2 - PM.coeff a.2 ∈
                  (lambdaIdeal p K) ^ (if a.2 ≤ N then N + 1 + a.2 else a.2) := by
              simpa [PN, PM] using
                samePrimeFiniteArtinHasseExpCoordPoly_coeff_sub_coeff_mem_lambdaIdeal_pow
                  (p := p) (K := K) N M a.2 hx hNM
            have hmul₂ :
                (PM ^ n).coeff a.1 * (PN.coeff a.2 - PM.coeff a.2) ∈
                  (lambdaIdeal p K) ^
                    (a.1 + (if a.2 ≤ N then N + 1 + a.2 else a.2)) := by
              simpa [pow_add] using Ideal.mul_mem_mul hPMpow₁ hdiff₂
            refine Ideal.pow_le_pow_right ?_ hmul₂
            by_cases hdsmall : d < N + (n + 1)
            · have ha2N : a.2 ≤ N := by omega
              rw [if_pos hdsmall, if_pos ha2N]
              omega
            · rw [if_neg hdsmall]
              by_cases ha2N : a.2 ≤ N
              · rw [if_pos ha2N]
                omega
              · rw [if_neg ha2N]
                omega
        rw [show
            (PN ^ n).coeff a.1 * PN.coeff a.2 -
                (PM ^ n).coeff a.1 * PM.coeff a.2 =
              ((PN ^ n).coeff a.1 - (PM ^ n).coeff a.1) * PN.coeff a.2 +
                (PM ^ n).coeff a.1 * (PN.coeff a.2 - PM.coeff a.2) by ring]
        exact ((lambdaIdeal p K) ^
          (if d < N + (n + 1) then N + 1 + d else d)).add_mem hterm₁ hterm₂

theorem samePrimeFiniteArtinHasseExpCoordPoly_pow_coeff_eq_zero_of_lt
    (N : ℕ) (x : ValuedIntegerRing p K) {n d : ℕ} (hdn : d < n) :
    ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff d = 0 := by
  have h :=
    coeff_pow_coe_eq_zero_of_lt_of_constantCoeff_eq_zero
      (samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x)
      (samePrimeFiniteArtinHasseExpCoordPoly_coeff_zero (p := p) (K := K) N x) hdn
  simpa [← Polynomial.coe_pow, Polynomial.coeff_coe] using h

theorem samePrimeFiniteArtinHasseExpCoordPoly_pow_le_of_mem_support
    (N : ℕ) (x : ValuedIntegerRing p K) {n d : ℕ}
    (hd : d ∈ ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).support) :
    n ≤ d := by
  by_contra hnd
  have hdn : d < n := Nat.lt_of_not_ge hnd
  have hcoeff :
      ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff d = 0 :=
    samePrimeFiniteArtinHasseExpCoordPoly_pow_coeff_eq_zero_of_lt
      (p := p) (K := K) N x hdn
  exact (Polynomial.mem_support_iff.mp hd) hcoeff

theorem samePrimeFiniteArtinHasse_den_exponent_le {n d : ℕ}
    (hn : n ≠ 0) (hnd : n ≤ d) :
    n.factorization p * (p - 1) ≤ d := by
  have h := Nat.factorization_mul_pred_le_pred
    (ell := p) (n := n) (Fact.out : Nat.Prime p) hn
  omega


end DworkParameter
end PadicLogSetup
end CyclotomicUnits
end BernoulliRegular

end

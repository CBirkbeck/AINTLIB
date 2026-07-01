module

public import BernoulliRegular.CyclotomicUnits.DworkParameter.SamePrimeLog.ArtinHasseLogDegreeSum

/-!
# The corrected Dwork parameter: same-prime finite Artin--Hasse logarithm

This file assembles the finite same-prime Artin--Hasse logarithm
`samePrimeFiniteArtinHasseLog` and identifies it with the homogeneous
degree-sum expansion built from the Artin--Hasse exponential coordinates,
culminating in `samePrimeFiniteLog_finiteArtinHasseExpCoord_eq_finiteArtinHasseLog`.

It then specialises this machinery to the Dwork inverse-parameter approximants
`dworkParameterApprox`, and develops the evaluation of integral-coefficient
power series at lambda-adically small completed elements
(`evalIntegralPowerSeriesMod`, `evalIntegralPowerSeries`), together with the
compatibility of the truncation approximations modulo powers of the principal
`lambda`-ideal.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace CyclotomicUnits
namespace PadicLogSetup
namespace DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local instance : CharZero (ValuedCompletion p K) :=
  algebraRat.charZero (ValuedCompletion p K)

/-- Same-prime finite Artin--Hasse logarithm
`sum_r x^(p^r) / p^r` in `R / lambda^(N+1)`. -/
noncomputable def samePrimeFiniteArtinHasseLog (N : ℕ)
    (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  ∑ r ∈ Finset.range (N + 1),
    samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx

/-- Extending the same-prime Artin--Hasse log sum past precision `N` does not
change its value modulo `lambda^(N+1)`. -/
theorem samePrimeFiniteArtinHasseLog_eq_sum_range_of_le {N M : ℕ} (hNM : N ≤ M)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteArtinHasseLog (p := p) (K := K) N x hx =
      ∑ r ∈ Finset.range (M + 1),
        samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx := by
  classical
  rw [samePrimeFiniteArtinHasseLog]
  refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hNM)) ?_
  intro r _hrM hrN
  have hNr : N + 1 ≤ r := Nat.le_of_not_gt (by simpa using hrN)
  exact samePrimeFiniteArtinHasseLogTerm_eq_zero_of_succ_le_index
    (p := p) (K := K) hx hNr

theorem samePrimeFiniteLog_finiteArtinHasseExpCoord_eq_homogeneous_support_sum
    (N : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLog (p := p) (K := K) N
        (samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N x)
        (samePrimeFiniteArtinHasseExpCoord_mem_lambdaIdeal (p := p) (K := K) N hx) =
      ∑ n ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) N),
        ∑ d ∈ ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).support,
          samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm
            (p := p) (K := K) N n d x hx := by
  classical
  unfold samePrimeFiniteLog
  refine Finset.sum_congr rfl ?_
  intro n _hn
  by_cases hn0 : n = 0
  · subst n
    simp [samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm,
      samePrimeFiniteArtinHasseExpCoordLogHomogeneousCore]
  · exact samePrimeFiniteLogTerm_finiteArtinHasseExpCoord_eq_homogeneous_support_sum
      (p := p) (K := K) N n hx hn0

theorem samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm_eq_zero_of_not_mem_support
    (N n d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hd : d ∉ ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).support) :
    samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm
      (p := p) (K := K) N n d x hx = 0 := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm,
      samePrimeFiniteArtinHasseExpCoordLogHomogeneousCore]
  by_cases hnd : n ≤ d
  · have hcoeff_zero :
        ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff d = 0 := by
      simpa [Polynomial.mem_support_iff] using hd
    have hcoeff :
        ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff d ∈
          (lambdaIdeal p K) ^ d :=
      samePrimeFiniteArtinHasseExpCoordPoly_pow_coeff_mem_lambdaIdeal_pow
        (p := p) (K := K) N hx n d
    have hden : n.factorization p * (p - 1) ≤ d :=
      samePrimeFiniteArtinHasse_den_exponent_le (p := p) hn hnd
    have heval_zero :
        samePrimeNatDivEvalAtDegree (p := p) (K := K) N n d hn
            (((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff d)
            hcoeff hden = 0 := by
      rw [samePrimeNatDivEvalAtDegree]
      let s : ℕ := d - n.factorization p * (p - 1)
      have hcoeff_s :
          ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff d ∈
            (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) := by
        simpa [s, Nat.add_sub_of_le hden] using hcoeff
      have hzero_s :
          (0 : ValuedIntegerRing p K) ∈
            (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) :=
        zero_mem _
      change samePrimeNatDivEval (p := p) (K := K) N n s hn
          (((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff d)
          hcoeff_s = 0
      calc
        samePrimeNatDivEval (p := p) (K := K) N n s hn
            (((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff d)
            hcoeff_s
            = samePrimeNatDivEval (p := p) (K := K) N n s hn 0 hzero_s :=
                samePrimeNatDivEval_eq_of_eq (p := p) (K := K) hn
                  hcoeff_zero hcoeff_s hzero_s
        _ = 0 := samePrimeNatDivEval_zero (p := p) (K := K) hn hzero_s
    rw [samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm_eq_signed_eval
      (p := p) (K := K) N n d hx hn hnd, heval_zero]
    simp
  · simp [samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm,
      samePrimeFiniteArtinHasseExpCoordLogHomogeneousCore, hn, hnd]

theorem samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm_eq_zero_of_cutoff_le_degree
    (N n d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hcut : samePrimeFiniteLogCutoff (p := p) N ≤ d) :
    samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm
      (p := p) (K := K) N n d x hx = 0 := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm,
      samePrimeFiniteArtinHasseExpCoordLogHomogeneousCore]
  by_cases hnd : n ≤ d
  · have hcoeff :
        ((samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x) ^ n).coeff d ∈
          (lambdaIdeal p K) ^ d :=
      samePrimeFiniteArtinHasseExpCoordPoly_pow_coeff_mem_lambdaIdeal_pow
        (p := p) (K := K) N hx n d
    have hden : n.factorization p * (p - 1) ≤ d :=
      samePrimeFiniteArtinHasse_den_exponent_le (p := p) hn hnd
    rw [samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm_eq_signed_eval
      (p := p) (K := K) N n d hx hn hnd,
      samePrimeNatDivEvalAtDegree_eq_zero_of_cutoff_le
        (p := p) (K := K) (N := N) (n := n) (d := d) hn hnd hcut hcoeff hden]
    simp
  · simp [samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm,
      samePrimeFiniteArtinHasseExpCoordLogHomogeneousCore, hn, hnd]

theorem samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_sum_Icc
    (N d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum
        (p := p) (K := K) N d x hx =
      ∑ n ∈ Finset.Icc 1 d,
        samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm
          (p := p) (K := K) N n d x hx := by
  classical
  simpa [samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum] using
    (Finset.sum_attach (s := Finset.Icc 1 d)
      (f := fun n : ℕ =>
        samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm
          (p := p) (K := K) N n d x hx))

theorem samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_zero_of_cutoff_le
    (N d : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hcut : samePrimeFiniteLogCutoff (p := p) N ≤ d) :
    samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum
      (p := p) (K := K) N d x hx = 0 := by
  classical
  rw [samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_sum_Icc
    (p := p) (K := K) N d hx]
  refine Finset.sum_eq_zero ?_
  intro n _hn
  exact samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm_eq_zero_of_cutoff_le_degree
    (p := p) (K := K) N n d hx hcut

theorem samePrimeFiniteArtinHasseLogTerm_eq_zero_of_cutoff_le_pow
    (N r : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hcut : samePrimeFiniteLogCutoff (p := p) N ≤ p ^ r) :
    samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx = 0 := by
  rw [← samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_logTerm
    (p := p) (K := K) N r hx]
  exact samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_zero_of_cutoff_le
    (p := p) (K := K) N (p ^ r) hx hcut

theorem samePrimeFiniteLogTerm_finiteArtinHasseExpCoord_eq_homogeneous_cutoff_sum
    (N n : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLogTerm (p := p) (K := K) N n
        (samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N x)
        (samePrimeFiniteArtinHasseExpCoord_mem_lambdaIdeal (p := p) (K := K) N hx) =
      ∑ d ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) N),
        samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm
          (p := p) (K := K) N n d x hx := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm,
      samePrimeFiniteArtinHasseExpCoordLogHomogeneousCore]
  let P : Polynomial (ValuedIntegerRing p K) :=
    samePrimeFiniteArtinHasseExpCoordPoly (p := p) (K := K) N x
  let C : ℕ := samePrimeFiniteLogCutoff (p := p) N
  let f : ℕ → ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) := fun d =>
    samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm (p := p) (K := K) N n d x hx
  have hsupport :
      samePrimeFiniteLogTerm (p := p) (K := K) N n
          (samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N x)
          (samePrimeFiniteArtinHasseExpCoord_mem_lambdaIdeal (p := p) (K := K) N hx) =
        ∑ d ∈ (P ^ n).support, f d := by
    simpa [P, f] using
      samePrimeFiniteLogTerm_finiteArtinHasseExpCoord_eq_homogeneous_support_sum
        (p := p) (K := K) N n hx hn
  have hsupport_union :
      ∑ d ∈ (P ^ n).support, f d =
        ∑ d ∈ (P ^ n).support ∪ Finset.range C, f d := by
    refine Finset.sum_subset (Finset.subset_union_left) ?_
    intro d _hdUnion hdSupport
    exact samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm_eq_zero_of_not_mem_support
      (p := p) (K := K) N n d hx (by simpa [P] using hdSupport)
  have hrange_union :
      ∑ d ∈ Finset.range C, f d =
        ∑ d ∈ (P ^ n).support ∪ Finset.range C, f d := by
    refine Finset.sum_subset (Finset.subset_union_right) ?_
    intro d hdUnion hdRange
    have hcut : C ≤ d :=
      Nat.le_of_not_gt (by
        intro hdlt
        exact hdRange (Finset.mem_range.mpr hdlt))
    exact samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm_eq_zero_of_cutoff_le_degree
      (p := p) (K := K) N n d hx (by simpa [C] using hcut)
  calc
    samePrimeFiniteLogTerm (p := p) (K := K) N n
        (samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N x)
        (samePrimeFiniteArtinHasseExpCoord_mem_lambdaIdeal (p := p) (K := K) N hx)
        = ∑ d ∈ (P ^ n).support, f d := hsupport
    _ = ∑ d ∈ (P ^ n).support ∪ Finset.range C, f d := hsupport_union
    _ = ∑ d ∈ Finset.range C, f d := hrange_union.symm

theorem samePrimeFiniteLog_finiteArtinHasseExpCoord_eq_homogeneous_degree_sum_range
    (N : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLog (p := p) (K := K) N
        (samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N x)
        (samePrimeFiniteArtinHasseExpCoord_mem_lambdaIdeal (p := p) (K := K) N hx) =
      ∑ d ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) N),
        samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum
          (p := p) (K := K) N d x hx := by
  classical
  let C : ℕ := samePrimeFiniteLogCutoff (p := p) N
  let f : ℕ → ℕ → ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) := fun n d =>
    samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm (p := p) (K := K) N n d x hx
  have hterm : ∀ n ∈ Finset.range C,
      samePrimeFiniteLogTerm (p := p) (K := K) N n
          (samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N x)
          (samePrimeFiniteArtinHasseExpCoord_mem_lambdaIdeal (p := p) (K := K) N hx) =
        ∑ d ∈ Finset.range C, f n d := by
    intro n _hn
    simpa [C, f] using
      samePrimeFiniteLogTerm_finiteArtinHasseExpCoord_eq_homogeneous_cutoff_sum
        (p := p) (K := K) N n hx
  have hdegree : ∀ d ∈ Finset.range C,
      ∑ n ∈ Finset.range C, f n d =
        samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum
          (p := p) (K := K) N d x hx := by
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
        simp [f, samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm,
          samePrimeFiniteArtinHasseExpCoordLogHomogeneousCore]
      · have hnd_not : ¬ n ≤ d := by
          intro hnd
          have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
          exact hnI (Finset.mem_Icc.mpr ⟨hn1, hnd⟩)
        simp [f, samePrimeFiniteArtinHasseExpCoordLogHomogeneousTerm,
          samePrimeFiniteArtinHasseExpCoordLogHomogeneousCore, hn0, hnd_not]
    calc
      ∑ n ∈ Finset.range C, f n d
          = ∑ n ∈ Finset.Icc 1 d, f n d := hI_to_range.symm
      _ = samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum
          (p := p) (K := K) N d x hx := by
          rw [samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_sum_Icc
            (p := p) (K := K) N d hx]
  calc
    samePrimeFiniteLog (p := p) (K := K) N
        (samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N x)
        (samePrimeFiniteArtinHasseExpCoord_mem_lambdaIdeal (p := p) (K := K) N hx)
        =
      ∑ n ∈ Finset.range C,
        samePrimeFiniteLogTerm (p := p) (K := K) N n
          (samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N x)
          (samePrimeFiniteArtinHasseExpCoord_mem_lambdaIdeal (p := p) (K := K) N hx) := by
        simp [samePrimeFiniteLog, C]
    _ = ∑ n ∈ Finset.range C, ∑ d ∈ Finset.range C, f n d := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        exact hterm n hn
    _ = ∑ d ∈ Finset.range C, ∑ n ∈ Finset.range C, f n d := by
        rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.range C,
        samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum
          (p := p) (K := K) N d x hx := by
        refine Finset.sum_congr rfl ?_
        intro d hd
        exact hdegree d hd

private theorem le_p_pow_self (r : ℕ) : r ≤ p ^ r := by
  have htwo : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hpow : 2 ^ r ≤ p ^ r := Nat.pow_le_pow_left htwo r
  exact (Nat.le_of_lt r.lt_two_pow_self).trans hpow

theorem samePrimeFiniteArtinHasseLog_eq_homogeneous_degree_sum_range
    (N : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteArtinHasseLog (p := p) (K := K) N x hx =
      ∑ d ∈ Finset.range (samePrimeFiniteLogCutoff (p := p) N),
        samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum
          (p := p) (K := K) N d x hx := by
  classical
  let C : ℕ := samePrimeFiniteLogCutoff (p := p) N
  let powSet : Finset ℕ := (Finset.range (C + 1)).filter fun r => p ^ r < C
  let logTerm : ℕ → ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) := fun r =>
    samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx
  let degreeTerm : ℕ → ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) := fun d =>
    samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum
      (p := p) (K := K) N d x hx
  have hNC : N ≤ C := by
    have hp_pos : 1 ≤ p := (Fact.out : Nat.Prime p).pos
    dsimp [C, samePrimeFiniteLogCutoff]
    nlinarith [Nat.mul_le_mul_left (N + 1) hp_pos]
  have hfilter_sum :
      ∑ r ∈ powSet, logTerm r =
        ∑ r ∈ Finset.range (C + 1), logTerm r := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro r hrRange hrFilter
    have hnot_lt : ¬ p ^ r < C := fun hrlt =>
      hrFilter (Finset.mem_filter.mpr ⟨hrRange, hrlt⟩)
    exact samePrimeFiniteArtinHasseLogTerm_eq_zero_of_cutoff_le_pow
      (p := p) (K := K) N r hx (Nat.le_of_not_gt hnot_lt)
  have hlog_to_degree :
      ∑ r ∈ powSet, logTerm r =
        ∑ r ∈ powSet, degreeTerm (p ^ r) := by
    refine Finset.sum_congr rfl ?_
    intro r _hr
    exact (samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_logTerm
      (p := p) (K := K) N r hx).symm
  have hpow_inj : Set.InjOn (fun r : ℕ => p ^ r) (powSet : Set ℕ) := fun a _ha b _hb hab =>
    Nat.pow_right_injective (Fact.out : Nat.Prime p).two_le hab
  have himage_sum :
      ∑ r ∈ powSet, degreeTerm (p ^ r) =
        ∑ d ∈ powSet.image (fun r : ℕ => p ^ r), degreeTerm d :=
    (Finset.sum_image hpow_inj).symm
  have himage_subset : powSet.image (fun r : ℕ => p ^ r) ⊆ Finset.range C := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨r, hr, rfl⟩
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hr).2
  have himage_to_range :
      ∑ d ∈ powSet.image (fun r : ℕ => p ^ r), degreeTerm d =
        ∑ d ∈ Finset.range C, degreeTerm d := by
    refine Finset.sum_subset himage_subset ?_
    intro d hdRange hdImage
    have hnot_pow : ¬ ∃ r : ℕ, d = p ^ r := by
      rintro ⟨r, rfl⟩
      have hrpow_lt : p ^ r < C := Finset.mem_range.mp hdRange
      have hr_range : r ∈ Finset.range (C + 1) :=
        Finset.mem_range.mpr (by
          have hrle : r ≤ p ^ r := le_p_pow_self (p := p) r
          omega)
      have hr_powSet : r ∈ powSet := Finset.mem_filter.mpr ⟨hr_range, hrpow_lt⟩
      exact hdImage (Finset.mem_image.mpr ⟨r, hr_powSet, rfl⟩)
    exact samePrimeFiniteArtinHasseExpCoordLogHomogeneousDegreeSum_eq_zero_of_not_pow
      (p := p) (K := K) N d hx hnot_pow
  calc
    samePrimeFiniteArtinHasseLog (p := p) (K := K) N x hx
        = ∑ r ∈ Finset.range (C + 1), logTerm r := by
            simpa [C, logTerm] using
              samePrimeFiniteArtinHasseLog_eq_sum_range_of_le
                (p := p) (K := K) (N := N) (M := C) hNC hx
    _ = ∑ r ∈ powSet, logTerm r := hfilter_sum.symm
    _ = ∑ r ∈ powSet, degreeTerm (p ^ r) := hlog_to_degree
    _ = ∑ d ∈ powSet.image (fun r : ℕ => p ^ r), degreeTerm d := himage_sum
    _ = ∑ d ∈ Finset.range C, degreeTerm d := himage_to_range

theorem samePrimeFiniteLog_finiteArtinHasseExpCoord_eq_finiteArtinHasseLog
    (N : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLog (p := p) (K := K) N
        (samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N x)
        (samePrimeFiniteArtinHasseExpCoord_mem_lambdaIdeal (p := p) (K := K) N hx) =
      samePrimeFiniteArtinHasseLog (p := p) (K := K) N x hx := by
  rw [samePrimeFiniteLog_finiteArtinHasseExpCoord_eq_homogeneous_degree_sum_range
    (p := p) (K := K) N hx]
  exact (samePrimeFiniteArtinHasseLog_eq_homogeneous_degree_sum_range
    (p := p) (K := K) N hx).symm

theorem samePrimeFiniteLog_finiteArtinHasseExpCoord_factor_eq_finiteArtinHasseLog
    (N : ℕ) (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteLog (p := p) (K := K) N
        (samePrimeFiniteArtinHasseExpCoord (p := p) (K := K) N x)
        (samePrimeFiniteArtinHasseExpCoord_mem_lambdaIdeal (p := p) (K := K) N hx) =
      samePrimeFiniteArtinHasseLog (p := p) (K := K) N x hx :=
  samePrimeFiniteLog_finiteArtinHasseExpCoord_eq_finiteArtinHasseLog
    (p := p) (K := K) N hx

theorem dworkParameterApprox_eq_sum_range (N : ℕ) :
    dworkParameterApprox p K N =
      ∑ n ∈ Finset.range N,
        (PowerSeries.coeff (R := ValuedIntegerRing p K) n)
            (integralInverseSeries p K) *
          valuedCyclotomicLambdaInteger p K ^ n := by
  unfold dworkParameterApprox
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  simp

@[simp]
theorem integralInverseSeries_coeff_zero :
    (PowerSeries.coeff (R := ValuedIntegerRing p K) 0)
        (integralInverseSeries p K) = 0 := by
  rw [integralInverseSeries, Furtwaengler.DieudonneDwork.IsRIntegralPS.coeff_mapTo]
  have hcoeff0 :
      (PowerSeries.coeff (R := ℚ) 0) (FormalDwork.inverseSeries p) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact FormalDwork.inverseSeries_constantCoeff p
  have hsubzero :
      (⟨(PowerSeries.coeff (R := ℚ) 0) (FormalDwork.inverseSeries p),
          FormalDwork.inverseSeries_isPIntegral p 0⟩ :
        Furtwaengler.DieudonneDwork.rIntegralRatSubring p) = 0 := by
    ext
    exact hcoeff0
  rw [hsubzero]
  exact map_zero (rIntegralRatToValuedInteger p K)

theorem dworkParameterApprox_mem_lambdaIdeal (N : ℕ) :
    dworkParameterApprox p K N ∈ lambdaIdeal p K := by
  classical
  rw [dworkParameterApprox_eq_sum_range]
  apply Ideal.sum_mem
  intro n _hn
  by_cases hn0 : n = 0
  · subst n
    have hcoeff0 := integralInverseSeries_coeff_zero (p := p) (K := K)
    simp [hcoeff0]
  · have hpow :
        valuedCyclotomicLambdaInteger p K ^ n ∈ lambdaIdeal p K :=
      Ideal.pow_le_self hn0
        (valuedCyclotomicLambdaInteger_pow_mem_lambdaIdeal_pow
          (p := p) (K := K) n)
    exact (lambdaIdeal p K).mul_mem_left _ hpow

/-- The same-prime finite Artin--Hasse logarithm specialized to the Dwork
inverse-parameter approximant. -/
noncomputable def dworkParameterFiniteArtinHasseLog (N : ℕ) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  samePrimeFiniteArtinHasseLog (p := p) (K := K) N
    (dworkParameterApprox p K (N + 1))
    (dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) (N + 1))

/-- Multiplication-by-`p^r` specification for the specialized finite
Artin--Hasse logarithm terms of the Dwork parameter approximants. -/
theorem dworkParameterFiniteArtinHasseLogTerm_natCast_prime_pow_mul_eq_mk
    (N r : ℕ) :
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        ((p : ValuedIntegerRing p K) ^ r) *
      samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r
        (dworkParameterApprox p K (N + 1))
        (dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) (N + 1)) =
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
      ((dworkParameterApprox p K (N + 1)) ^ (p ^ r)) :=
  samePrimeFiniteArtinHasseLogTerm_natCast_prime_pow_mul_eq_mk
    (p := p) (K := K) N r
    (dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) (N + 1))

theorem mem_ideal_smul_top_iff_self
    {R : Type*} [CommRing R] (I : Ideal R) {x : R} :
    x ∈ I • (⊤ : Submodule R R) ↔ x ∈ I := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) ?_
    · simpa [smul_eq_mul] using I.mul_mem_right y hr
    · intro x y hx hy
      exact I.add_mem hx hy
  · intro hx
    have h : x • (1 : R) ∈ I • (⊤ : Submodule R R) :=
      Submodule.smul_mem_smul hx Submodule.mem_top
    simpa [smul_eq_mul] using h

theorem factor_evalₐ_eq_evalₐ
    {M N : ℕ} (hMN : M ≤ N)
    (x : DworkCompleteIntegerRing p K) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) hMN
        (AdicCompletion.evalₐ (lambdaIdeal p K) N x) =
      AdicCompletion.evalₐ (lambdaIdeal p K) M x := by
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  have hx := x.property hMN
  have hN :
      Ideal.Quotient.factor (show I ^ N ≤ I ^ N • (⊤ : Ideal R) by
          exact le_of_eq (Ideal.mul_top (I ^ N)).symm)
          (AdicCompletion.evalₐ I N x) =
        AdicCompletion.eval I R N x :=
    AdicCompletion.factor_evalₐ_eq_eval (I := I) (R := R) (n := N) x
      (le_of_eq (Ideal.mul_top (I ^ N)).symm)
  have hM :
      Ideal.Quotient.factor (show I ^ M • (⊤ : Ideal R) ≤ I ^ M by
          exact le_of_eq (Ideal.mul_top (I ^ M)))
          (AdicCompletion.eval I R M x) =
        AdicCompletion.evalₐ I M x :=
    AdicCompletion.factor_eval_eq_evalₐ (I := I) (R := R) (n := M) x
      (le_of_eq (Ideal.mul_top (I ^ M)))
  dsimp [I, R] at hN hM hx ⊢
  calc
    Ideal.Quotient.factorPow (lambdaIdeal p K) hMN
        ((AdicCompletion.evalₐ (lambdaIdeal p K) N) x)
        =
      Ideal.Quotient.factor
          (show (lambdaIdeal p K) ^ M • (⊤ : Ideal (ValuedIntegerRing p K)) ≤
              (lambdaIdeal p K) ^ M by
            exact le_of_eq (Ideal.mul_top ((lambdaIdeal p K) ^ M)))
          (AdicCompletion.transitionMap (lambdaIdeal p K) (ValuedIntegerRing p K) hMN
            ((AdicCompletion.eval (lambdaIdeal p K) (ValuedIntegerRing p K) N) x)) := by
        rw [← hN]
        refine Quotient.inductionOn'
          ((AdicCompletion.evalₐ (lambdaIdeal p K) N) x)
          ?_
        intro r
        rfl
    _ =
      Ideal.Quotient.factor
          (show (lambdaIdeal p K) ^ M • (⊤ : Ideal (ValuedIntegerRing p K)) ≤
              (lambdaIdeal p K) ^ M by
            exact le_of_eq (Ideal.mul_top ((lambdaIdeal p K) ^ M)))
          ((AdicCompletion.eval (lambdaIdeal p K) (ValuedIntegerRing p K) M) x) := by
        simpa [AdicCompletion.eval] using
          congrArg
            (Ideal.Quotient.factor
              (show (lambdaIdeal p K) ^ M •
                    (⊤ : Ideal (ValuedIntegerRing p K)) ≤
                  (lambdaIdeal p K) ^ M by
                exact le_of_eq (Ideal.mul_top ((lambdaIdeal p K) ^ M))))
            hx
    _ = (AdicCompletion.evalₐ (lambdaIdeal p K) M) x := hM

theorem evalₐ_pow_eq_zero_of_evalₐ_one_eq_zero
    {x : DworkCompleteIntegerRing p K}
    (hx : AdicCompletion.evalₐ (lambdaIdeal p K) 1 x = 0)
    (N : ℕ) :
    (AdicCompletion.evalₐ (lambdaIdeal p K) N x) ^ N = 0 := by
  cases N with
  | zero =>
      have htop :
          (1 : ValuedIntegerRing p K) - 0 ∈ (lambdaIdeal p K) ^ 0 := by
        simp
      simpa [pow_zero] using
        (Ideal.Quotient.eq.mpr htop :
          (Ideal.Quotient.mk ((lambdaIdeal p K) ^ 0)
              (1 : ValuedIntegerRing p K)) =
            Ideal.Quotient.mk ((lambdaIdeal p K) ^ 0) 0)
  | succ N =>
      let I : Ideal (ValuedIntegerRing p K) := lambdaIdeal p K
      let a : ValuedIntegerRing p K ⧸ I ^ (N + 1) :=
        AdicCompletion.evalₐ I (N + 1) x
      have hfac : Ideal.Quotient.factorPow I (Nat.succ_pos N) a = 0 := by
        dsimp [a, I]
        rw [factor_evalₐ_eq_evalₐ (p := p) (K := K) (M := 1) (N := N + 1)
          (Nat.succ_pos N), hx]
      rcases Ideal.Quotient.mk_surjective a with ⟨r, hr⟩
      change a ^ (N + 1) = 0
      rw [← hr] at hfac ⊢
      have hrI : r ∈ I := by
        have hrIpow : r ∈ I ^ 1 := by
          apply Ideal.Quotient.eq_zero_iff_mem.mp
          simpa [Ideal.Quotient.factorPow] using hfac
        simpa using hrIpow
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow hrI (N + 1)

/-- Finite quotient evaluation of an integral-coefficient power series at a
completed element.  The target quotient makes the evaluation a finite
polynomial because the argument is nilpotent modulo `lambda^N`. -/
def evalIntegralPowerSeriesMod
    (F : PowerSeries (ValuedIntegerRing p K))
    (x : DworkCompleteIntegerRing p K) (N : ℕ) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ N :=
  let q : ValuedIntegerRing p K →+*
      ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ N :=
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
  (PowerSeries.trunc N (PowerSeries.map q F)).eval₂
    (RingHom.id (ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ N))
    (AdicCompletion.evalₐ (lambdaIdeal p K) N x)

theorem powerSeries_trunc_eval₂_subst_of_pow_succ_eq_zero
    {A : Type*} [CommRing A] (a : A) (N : ℕ)
    (ha : a ^ (N + 1) = 0)
    {G : PowerSeries A} (hG0 : PowerSeries.constantCoeff G = 0)
    (hEvalNil :
      ((PowerSeries.trunc (N + 1) G).eval₂ (RingHom.id A) a) ^ (N + 1) = 0)
    (F : PowerSeries A) :
    (PowerSeries.trunc (N + 1) (PowerSeries.subst G F)).eval₂
        (RingHom.id A) a =
      (PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A)
        ((PowerSeries.trunc (N + 1) G).eval₂ (RingHom.id A) a) := by
  let b : A := (PowerSeries.trunc (N + 1) G).eval₂ (RingHom.id A) a
  have hCa : PowerSeries.HasSubst (PowerSeries.C a : PowerSeries A) := by
    change IsNilpotent
      (PowerSeries.constantCoeff (PowerSeries.C a : PowerSeries A))
    exact ⟨N + 1, by simpa using ha⟩
  have hG : PowerSeries.HasSubst G :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hG0
  apply PowerSeries.C_injective
  calc
    PowerSeries.C
        ((PowerSeries.trunc (N + 1) (PowerSeries.subst G F)).eval₂
          (RingHom.id A) a) =
        PowerSeries.subst (PowerSeries.C a) (PowerSeries.subst G F) := by
          rw [Furtwaengler.powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero
            a N ha]
    _ = PowerSeries.subst (PowerSeries.subst (PowerSeries.C a) G) F := by
          rw [PowerSeries.subst_comp_subst_apply hG hCa F]
    _ = PowerSeries.subst (PowerSeries.C b) F := by
          rw [Furtwaengler.powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero
            a N ha G]
    _ = PowerSeries.C
        ((PowerSeries.trunc (N + 1) F).eval₂ (RingHom.id A) b) := by
          rw [Furtwaengler.powerSeries_subst_C_eq_C_eval₂_trunc_of_pow_succ_eq_zero
            b N hEvalNil F]

theorem evalIntegralPowerSeriesMod_factor_eq
    (F : PowerSeries (ValuedIntegerRing p K))
    {x : DworkCompleteIntegerRing p K}
    (hx : AdicCompletion.evalₐ (lambdaIdeal p K) 1 x = 0)
    {M N : ℕ} (hMN : M ≤ N) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) hMN
        (evalIntegralPowerSeriesMod p K F x N) =
      evalIntegralPowerSeriesMod p K F x M := by
  classical
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  let aM : R ⧸ I ^ M := AdicCompletion.evalₐ I M x
  let term : ℕ → R ⧸ I ^ M := fun n =>
    Ideal.Quotient.mk (I ^ M) ((PowerSeries.coeff (R := R) n) F) * aM ^ n
  have hNil : aM ^ M = 0 := by
    change (AdicCompletion.evalₐ (lambdaIdeal p K) M x) ^ M = 0
    exact evalₐ_pow_eq_zero_of_evalₐ_one_eq_zero (p := p) (K := K) hx M
  have hN :
      Ideal.Quotient.factorPow I hMN (evalIntegralPowerSeriesMod p K F x N) =
        ∑ n ∈ Finset.range N, term n := by
    change Ideal.Quotient.factorPow I hMN
        ((PowerSeries.trunc N
          (PowerSeries.map (Ideal.Quotient.mk (I ^ N)) F)).eval₂
            (RingHom.id (R ⧸ I ^ N)) (AdicCompletion.evalₐ I N x)) =
      ∑ n ∈ Finset.range N, term n
    rw [PowerSeries.eval₂_trunc_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl ?_
    intro n _hn
    have hfactor :
        Ideal.Quotient.factorPow I hMN (AdicCompletion.evalₐ I N x) = aM := by
      simpa [I, aM] using
        factor_evalₐ_eq_evalₐ (p := p) (K := K) hMN x
    rw [map_mul, map_pow, hfactor]
    simp [term]
  have hM :
      evalIntegralPowerSeriesMod p K F x M =
        ∑ n ∈ Finset.range M, term n := by
    change
      (PowerSeries.trunc M
        (PowerSeries.map (Ideal.Quotient.mk (I ^ M)) F)).eval₂
          (RingHom.id (R ⧸ I ^ M)) (AdicCompletion.evalₐ I M x) =
        ∑ n ∈ Finset.range M, term n
    rw [PowerSeries.eval₂_trunc_eq_sum_range]
    simp [term, aM]
  have htail :
      ∀ n ∈ Finset.range N, n ∉ Finset.range M → term n = 0 := by
    intro n _hnN hnM
    have hMn : M ≤ n := Nat.le_of_not_gt (by simpa using hnM)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hMn
    simp [term, pow_add, hNil]
  have hsum :
      ∑ n ∈ Finset.range N, term n =
        ∑ n ∈ Finset.range M, term n :=
    (Finset.sum_subset (Finset.range_mono hMN) htail).symm
  rw [hN, hM, hsum]

/-- Completed evaluation of an integral-coefficient power series at a
lambda-adically small completed element. -/
def evalIntegralPowerSeries
    (F : PowerSeries (ValuedIntegerRing p K))
    (x : DworkCompleteIntegerRing p K)
    (hx : AdicCompletion.evalₐ (lambdaIdeal p K) 1 x = 0) :
    DworkCompleteIntegerRing p K :=
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  ⟨fun N =>
      (Ideal.quotientEquivAlgOfEq R (by
        ext y
        simp : (I ^ N • ⊤ : Ideal R) = I ^ N)).symm
        (evalIntegralPowerSeriesMod p K F x N),
    by
      intro M N hMN
      let hEqM : (I ^ M • ⊤ : Ideal R) = I ^ M := by
        ext y
        simp
      let hEqN : (I ^ N • ⊤ : Ideal R) = I ^ N := by
        ext y
        simp
      apply (Ideal.quotientEquivAlgOfEq R hEqM).injective
      calc
        (Ideal.quotientEquivAlgOfEq R hEqM)
            (AdicCompletion.transitionMap I R hMN
              ((Ideal.quotientEquivAlgOfEq R hEqN).symm
                (evalIntegralPowerSeriesMod p K F x N)))
            =
          Ideal.Quotient.factorPow I hMN
            (evalIntegralPowerSeriesMod p K F x N) := by
            refine Quotient.inductionOn' (evalIntegralPowerSeriesMod p K F x N) ?_
            intro r
            rfl
        _ = evalIntegralPowerSeriesMod p K F x M :=
            evalIntegralPowerSeriesMod_factor_eq (p := p) (K := K) F hx hMN
        _ = (Ideal.quotientEquivAlgOfEq R hEqM)
            ((Ideal.quotientEquivAlgOfEq R hEqM).symm
              (evalIntegralPowerSeriesMod p K F x M)) := by
            refine Quotient.inductionOn' (evalIntegralPowerSeriesMod p K F x M) ?_
            intro r
            rfl
      ⟩

@[simp]
theorem evalIntegralPowerSeries_evalₐ
    (F : PowerSeries (ValuedIntegerRing p K))
    (x : DworkCompleteIntegerRing p K)
    (hx : AdicCompletion.evalₐ (lambdaIdeal p K) 1 x = 0)
    (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) N
        (evalIntegralPowerSeries p K F x hx) =
      evalIntegralPowerSeriesMod p K F x N := by
  unfold evalIntegralPowerSeries
  let hEq :
      ((lambdaIdeal p K) ^ N • ⊤ : Ideal (ValuedIntegerRing p K)) =
        (lambdaIdeal p K) ^ N := by
    ext y
    simp
  change
    (Ideal.quotientEquivAlgOfEq (ValuedIntegerRing p K) hEq)
      ((Ideal.quotientEquivAlgOfEq (ValuedIntegerRing p K) hEq).symm
        (evalIntegralPowerSeriesMod p K F x N)) =
      evalIntegralPowerSeriesMod p K F x N
  refine Quotient.inductionOn' (evalIntegralPowerSeriesMod p K F x N) ?_
  intro r
  rfl

/-- Finite truncation approximations are compatible modulo powers of the
principal `lambda`-ideal. -/
theorem quotient_mk_dworkParameterApprox_factor_eq
    {M N : ℕ} (hMN : M ≤ N) :
    let φ : ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ N →+*
        ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ M :=
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hMN)
    φ (Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
        (dworkParameterApprox p K N)) =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ M)
        (dworkParameterApprox p K M) := by
  classical
  dsimp only
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  let lam : R := valuedCyclotomicLambdaInteger p K
  let term : ℕ → R ⧸ I ^ M := fun n =>
    Ideal.Quotient.mk (I ^ M)
      (((PowerSeries.coeff (R := R) n) (integralInverseSeries p K)) * lam ^ n)
  have hN :
      Ideal.Quotient.mk (I ^ M) (dworkParameterApprox p K N) =
        ∑ n ∈ Finset.range N, term n := by
    rw [dworkParameterApprox_eq_sum_range]
    simp [term, I, lam]
  have hM :
      Ideal.Quotient.mk (I ^ M) (dworkParameterApprox p K M) =
        ∑ n ∈ Finset.range M, term n := by
    rw [dworkParameterApprox_eq_sum_range]
    simp [term, I, lam]
  have htail :
      ∀ n ∈ Finset.range N, n ∉ Finset.range M → term n = 0 := by
    intro n _hnN hnM
    have hMn : M ≤ n := Nat.le_of_not_gt (by simpa using hnM)
    have hLam :
        lam ^ n ∈ I ^ M :=
      Ideal.pow_le_pow_right hMn
        (by
          simpa [I, lam] using
            (valuedCyclotomicLambdaInteger_pow_mem_lambdaIdeal_pow
              (p := p) (K := K) n))
    have hLamBar : Ideal.Quotient.mk (I ^ M) (lam ^ n) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hLam
    change
      Ideal.Quotient.mk (I ^ M)
          (((PowerSeries.coeff (R := R) n) (integralInverseSeries p K)) * lam ^ n) = 0
    rw [map_mul, hLamBar, mul_zero]
  have hsum :
      ∑ n ∈ Finset.range N, term n =
        ∑ n ∈ Finset.range M, term n :=
    (Finset.sum_subset (Finset.range_mono hMN) htail).symm
  calc
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hMN)
        (Ideal.Quotient.mk ((lambdaIdeal p K) ^ N)
          (dworkParameterApprox p K N))
        = Ideal.Quotient.mk (I ^ M) (dworkParameterApprox p K N) := by
            rfl
    _ = Ideal.Quotient.mk (I ^ M) (dworkParameterApprox p K M) := by
            rw [hN, hM, hsum]

theorem dworkParameterApprox_sub_mem_lambdaIdeal_pow
    {M N : ℕ} (hMN : M ≤ N) :
    dworkParameterApprox p K N - dworkParameterApprox p K M ∈
      (lambdaIdeal p K) ^ M := by
  have h :=
    quotient_mk_dworkParameterApprox_factor_eq (p := p) (K := K) hMN
  dsimp only at h
  exact Ideal.Quotient.eq.mp h

theorem dworkParameterApprox_smodEq
    {M N : ℕ} (hMN : M ≤ N) :
    dworkParameterApprox p K M ≡ dworkParameterApprox p K N
      [SMOD (lambdaIdeal p K) ^ M •
        (⊤ : Submodule (ValuedIntegerRing p K) (ValuedIntegerRing p K))] := by
  rw [SModEq.sub_mem]
  have hmem :
      dworkParameterApprox p K M - dworkParameterApprox p K N ∈
        (lambdaIdeal p K) ^ M := by
    have h :=
      dworkParameterApprox_sub_mem_lambdaIdeal_pow (p := p) (K := K) hMN
    simpa [sub_eq_add_neg, add_comm] using ((lambdaIdeal p K) ^ M).neg_mem h
  exact (mem_ideal_smul_top_iff_self ((lambdaIdeal p K) ^ M)).mpr hmem


end DworkParameter
end PadicLogSetup
end CyclotomicUnits
end BernoulliRegular

end

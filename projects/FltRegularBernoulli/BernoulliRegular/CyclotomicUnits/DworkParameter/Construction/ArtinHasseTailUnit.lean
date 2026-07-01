module

public import BernoulliRegular.CyclotomicUnits.DworkParameter.Construction.ArtinHasseLogVanishing

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

theorem samePrimeArtinHasseLogTermNumerator_zero
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeArtinHasseLogTermNumerator (p := p) (K := K) 0 x hx = x := by
  have hspec :=
    (samePrimeArtinHasseLogTermNumerator_spec (p := p) (K := K) 0 hx).2
  simpa using hspec

theorem samePrimeFiniteArtinHasseLogTerm_zero_eq_mk
    (N : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N 0 x hx =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) x := by
  rw [samePrimeFiniteArtinHasseLogTerm,
    samePrimeArtinHasseLogTermNumerator_zero (p := p) (K := K) hx]

/-- Forced lambda-adic order of the `r`-th corrected Artin--Hasse tail term
`x^(p^r - 1) / p^r`. -/
def samePrimeArtinHasseTailTermOrder (r : ℕ) : ℕ :=
  p ^ r - 1 - r * (p - 1)

theorem samePrimeArtinHasseTail_den_le (r : ℕ) :
    r * (p - 1) ≤ p ^ r - 1 := by
  have hp_int : -1 ≤ (p : ℤ) := by
    have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
    omega
  have hbern :
      (1 : ℤ) + (r : ℤ) * ((p : ℤ) - 1) ≤ (p : ℤ) ^ r :=
    one_add_mul_sub_le_pow hp_int r
  have hpred_cast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
    omega
  have hbern' :
      (1 : ℤ) + (r : ℤ) * ((p - 1 : ℕ) : ℤ) ≤ ((p ^ r : ℕ) : ℤ) := by
    simpa [hpred_cast, Nat.cast_pow] using hbern
  have hnat : 1 + r * (p - 1) ≤ p ^ r := by
    exact_mod_cast hbern'
  omega

theorem samePrimeArtinHasseTail_den_add_order (r : ℕ) :
    r * (p - 1) + samePrimeArtinHasseTailTermOrder (p := p) r =
      p ^ r - 1 := by
  simp [samePrimeArtinHasseTailTermOrder,
    Nat.add_sub_cancel' (samePrimeArtinHasseTail_den_le (p := p) r)]

theorem samePrimeFiniteArtinHasseTailTerm_mem (r : ℕ)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    x ^ (p ^ r - 1) ∈
      (lambdaIdeal p K) ^
        ((p ^ r).factorization p * (p - 1) +
          samePrimeArtinHasseTailTermOrder (p := p) r) := by
  have hfac : (p ^ r).factorization p = r :=
    Nat.factorization_pow_self (Fact.out : Nat.Prime p)
  have hpow : x ^ (p ^ r - 1) ∈ (lambdaIdeal p K) ^ (p ^ r - 1) :=
    Ideal.pow_mem_pow hx (p ^ r - 1)
  simpa [hfac, Nat.Prime.factorization_self (Fact.out : Nat.Prime p),
    samePrimeArtinHasseTail_den_add_order (p := p) r] using hpow

/-- The finite quotient corrected tail term `x^(p^r - 1) / p^r`. -/
noncomputable def samePrimeFiniteArtinHasseTailTerm (N r : ℕ)
    (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  samePrimeNatDivEval (p := p) (K := K) N (p ^ r)
    (samePrimeArtinHasseTailTermOrder (p := p) r)
    (pow_ne_zero r (Fact.out : Nat.Prime p).ne_zero)
    (x ^ (p ^ r - 1))
    (samePrimeFiniteArtinHasseTailTerm_mem (p := p) (K := K) r hx)

theorem samePrimeFiniteArtinHasseTailTerm_factorPow {M N r : ℕ} (hMN : M ≤ N)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
        (samePrimeFiniteArtinHasseTailTerm (p := p) (K := K) N r x hx) =
      samePrimeFiniteArtinHasseTailTerm (p := p) (K := K) M r x hx := by
  rw [samePrimeFiniteArtinHasseTailTerm, samePrimeFiniteArtinHasseTailTerm]
  exact samePrimeNatDivEval_factorPow (p := p) (K := K) hMN
    (pow_ne_zero r (Fact.out : Nat.Prime p).ne_zero) _

theorem samePrimeFiniteArtinHasseTailTerm_eq_zero_of_succ_le
    {N r : ℕ} {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hs : N + 1 ≤ samePrimeArtinHasseTailTermOrder (p := p) r) :
    samePrimeFiniteArtinHasseTailTerm (p := p) (K := K) N r x hx = 0 := by
  rw [samePrimeFiniteArtinHasseTailTerm]
  exact samePrimeNatDivEval_eq_zero_of_succ_le (p := p) (K := K)
    (pow_ne_zero r (Fact.out : Nat.Prime p).ne_zero)
    (samePrimeFiniteArtinHasseTailTerm_mem (p := p) (K := K) r hx) hs

theorem intCast_samePrimeArtinHasseTailTermOrder (r : ℕ) :
    ((samePrimeArtinHasseTailTermOrder (p := p) r : ℕ) : ℤ) =
      FormalDwork.artinHasseTailValuationIndex p r := by
  unfold samePrimeArtinHasseTailTermOrder
    FormalDwork.artinHasseTailValuationIndex
  have hden := samePrimeArtinHasseTail_den_le (p := p) r
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have hpred_cast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    omega
  have hp_pow_one : 1 ≤ p ^ r :=
    one_le_pow₀ (show 1 ≤ p from Nat.succ_le_of_lt hp_pos)
  simp only [Nat.cast_sub hden, Nat.cast_sub hp_pow_one, Nat.cast_mul]
  rw [hpred_cast]
  rw [Nat.cast_pow]
  ring_nf

theorem one_le_samePrimeArtinHasseTailTermOrder_of_two_le
    {r : ℕ} (hr : 2 ≤ r) :
    1 ≤ samePrimeArtinHasseTailTermOrder (p := p) r := by
  have hidx := FormalDwork.artinHasseTailValuationIndex_ge_sq (p := p) hr
  have hp_one : (1 : ℤ) ≤ (p : ℤ) - 1 := by
    have hp_gt : (1 : ℤ) < p := by
      exact_mod_cast (Fact.out : Nat.Prime p).one_lt
    omega
  have hp_nonneg : (0 : ℤ) ≤ (p : ℤ) - 1 := by omega
  have hsquare : (1 : ℤ) ≤ ((p : ℤ) - 1) ^ 2 := by
    simpa [pow_two] using mul_le_mul hp_one hp_one (by norm_num) hp_nonneg
  have htail : (1 : ℤ) ≤
      (samePrimeArtinHasseTailTermOrder (p := p) r : ℤ) := by
    rw [intCast_samePrimeArtinHasseTailTermOrder (p := p) r]
    exact hsquare.trans hidx
  exact_mod_cast htail

private theorem nat_mul_add_one_le_pow_of_three_le
    {p r : ℕ} (hp_three : 3 ≤ p) (hr : 2 ≤ r) :
    p * r + 1 ≤ p ^ r := by
  induction r, hr using Nat.le_induction with
  | base =>
      have hpZ : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp_three
      have hbaseZ : (p : ℤ) * 2 + 1 ≤ (p : ℤ) ^ 2 := by
        nlinarith [sq_nonneg ((p : ℤ) - 3)]
      exact_mod_cast hbaseZ
  | succ r hr ih =>
      have hstep : p * (r + 1) + 1 ≤ p * (p * r + 1) := by
        have hp_ge_two : 2 ≤ p := by omega
        have htwo : r + 1 ≤ 2 * r := by omega
        have hpr : r + 1 ≤ p * r :=
          htwo.trans (Nat.mul_le_mul_right r hp_ge_two)
        have hmul' : p * (r + 1) ≤ p * (p * r) :=
          Nat.mul_le_mul_left p hpr
        have hp_one : 1 ≤ p := by omega
        rw [mul_add, mul_one]
        exact Nat.add_le_add hmul' hp_one
      have hmul : p * (p * r + 1) ≤ p * p ^ r :=
        Nat.mul_le_mul_left p ih
      have hpow : p * p ^ r = p ^ (r + 1) := by
        rw [pow_succ, mul_comm]
      exact hstep.trans (by simpa [hpow] using hmul)

theorem le_samePrimeArtinHasseTailTermOrder_of_two_lt
    (hp_two : 2 < p) {r : ℕ} (hr : 2 ≤ r) :
    r ≤ samePrimeArtinHasseTailTermOrder (p := p) r := by
  have hp_three : 3 ≤ p := hp_two
  have hmain : p * r + 1 ≤ p ^ r :=
    nat_mul_add_one_le_pow_of_three_le hp_three hr
  have hmainZ : (p : ℤ) * (r : ℤ) + 1 ≤ (p : ℤ) ^ r := by
    exact_mod_cast hmain
  have hgoalZ :
      (r : ℤ) ≤ (samePrimeArtinHasseTailTermOrder (p := p) r : ℤ) := by
    rw [intCast_samePrimeArtinHasseTailTermOrder (p := p) r]
    unfold FormalDwork.artinHasseTailValuationIndex
    nlinarith
  exact_mod_cast hgoalZ

theorem samePrimeFiniteArtinHasseTailTerm_eq_of_sub_mem
    {N r : ℕ} (hr : 2 ≤ r)
    {x y : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hy : y ∈ lambdaIdeal p K)
    (hxy : x - y ∈ (lambdaIdeal p K) ^ (N + 1)) :
    samePrimeFiniteArtinHasseTailTerm (p := p) (K := K) N r x hx =
      samePrimeFiniteArtinHasseTailTerm (p := p) (K := K) N r y hy := by
  let m : ℕ := p ^ r - 1
  let den : ℕ := (p ^ r).factorization p * (p - 1)
  let s : ℕ := samePrimeArtinHasseTailTermOrder (p := p) r
  have hfac : (p ^ r).factorization p = r :=
    Nat.factorization_pow_self (Fact.out : Nat.Prime p)
  have hden_add_s : den + s = p ^ r - 1 := by
    dsimp [den, s]
    rw [hfac]
    exact samePrimeArtinHasseTail_den_add_order (p := p) r
  have hp_one : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hr_pos : r ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hr)
  have hpow_gt_one : 1 < p ^ r := one_lt_pow₀ hp_one hr_pos
  have hm_ne : m ≠ 0 := by
    dsimp [m]
    omega
  have hn : p ^ r ≠ 0 := pow_ne_zero r (Fact.out : Nat.Prime p).ne_zero
  have hxpow : x ^ m ∈ (lambdaIdeal p K) ^ (den + s) := by
    simpa [m, den, s] using
      samePrimeFiniteArtinHasseTailTerm_mem (p := p) (K := K) r hx
  have hypow : y ^ m ∈ (lambdaIdeal p K) ^ (den + s) := by
    simpa [m, den, s] using
      samePrimeFiniteArtinHasseTailTerm_mem (p := p) (K := K) r hy
  have hdiff_s : x ^ m - y ^ m ∈ (lambdaIdeal p K) ^ (den + s) :=
    ((lambdaIdeal p K) ^ (den + s)).sub_mem hxpow hypow
  have hpowdiff : x ^ m - y ^ m ∈ (lambdaIdeal p K) ^ (N + m) :=
    pow_sub_pow_mem_lambdaIdeal_pow_add (p := p) (K := K) hm_ne hx hy hxy
  have hdiff_big : x ^ m - y ^ m ∈ (lambdaIdeal p K) ^ (den + (N + 1)) := by
    have horder : 1 ≤ s := by
      simpa [s] using
        one_le_samePrimeArtinHasseTailTermOrder_of_two_le (p := p) hr
    have hle : den + (N + 1) ≤ N + m := by
      dsimp [m]
      omega
    exact Ideal.pow_le_pow_right hle hpowdiff
  have hsub_eval :
      samePrimeNatDivEval (p := p) (K := K) N (p ^ r) s hn
          (x ^ m - y ^ m) hdiff_s =
        samePrimeNatDivEval (p := p) (K := K) N (p ^ r) s hn
            (x ^ m) hxpow -
          samePrimeNatDivEval (p := p) (K := K) N (p ^ r) s hn
            (y ^ m) hypow := by
    have hneg : -y ^ m ∈ (lambdaIdeal p K) ^ (den + s) :=
      ((lambdaIdeal p K) ^ (den + s)).neg_mem hypow
    have hsum_s : x ^ m + -y ^ m ∈ (lambdaIdeal p K) ^ (den + s) := by
      simpa [sub_eq_add_neg] using hdiff_s
    have hadd := samePrimeNatDivEval_add (p := p) (K := K) (N := N)
      (n := p ^ r) (s := s) hn hxpow hneg hsum_s
    rw [samePrimeNatDivEval_neg (p := p) (K := K) (N := N)
      (n := p ^ r) (s := s) hn hypow hneg] at hadd
    simpa [sub_eq_add_neg] using hadd
  have hzero_s :
      samePrimeNatDivEval (p := p) (K := K) N (p ^ r) s hn
          (x ^ m - y ^ m) hdiff_s = 0 := by
    rw [samePrimeNatDivEval_eq_of_mem (p := p) (K := K) (N := N)
      (n := p ^ r) (s := s) (t := N + 1) hn hdiff_s hdiff_big]
    exact samePrimeNatDivEval_eq_zero_of_succ_le (p := p) (K := K)
      (N := N) (n := p ^ r) (s := N + 1) hn hdiff_big le_rfl
  rw [samePrimeFiniteArtinHasseTailTerm, samePrimeFiniteArtinHasseTailTerm]
  exact sub_eq_zero.mp (by
    rw [← hsub_eval, hzero_s])

theorem samePrimeFiniteArtinHasseTailTerm_mul_left_eq_logTerm
    (N r : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) x *
        samePrimeFiniteArtinHasseTailTerm (p := p) (K := K) N r x hx =
      samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx := by
  let n : ℕ := p ^ r
  let s : ℕ := samePrimeArtinHasseTailTermOrder (p := p) r
  let z : ValuedIntegerRing p K := x ^ (p ^ r - 1)
  have hn : n ≠ 0 := pow_ne_zero r (Fact.out : Nat.Prime p).ne_zero
  have hfac : n.factorization p = r := by
    simpa [n] using Nat.factorization_pow_self (Fact.out : Nat.Prime p)
  have hz : z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) := by
    simpa [n, s, z] using
      samePrimeFiniteArtinHasseTailTerm_mem (p := p) (K := K) r hx
  have hxz_eq : x * z = x ^ (p ^ r) := by
    simpa [z, n] using (mul_pow_sub_one hn x)
  have hxz_mem :
      x * z ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) := by
    have hpow : x ^ (p ^ r) ∈ (lambdaIdeal p K) ^ (p ^ r) :=
      Ideal.pow_mem_pow hx (p ^ r)
    have hle : p ^ r - 1 ≤ p ^ r := Nat.sub_le (p ^ r) 1
    have hpow' : x ^ (p ^ r) ∈ (lambdaIdeal p K) ^ (p ^ r - 1) :=
      Ideal.pow_le_pow_right hle hpow
    rw [hxz_eq]
    simpa [n, hfac, s, Nat.Prime.factorization_self (Fact.out : Nat.Prime p),
      samePrimeArtinHasseTail_den_add_order (p := p) r] using hpow'
  have hpow_mem_s :
      x ^ (p ^ r) ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + s) := by
    simpa [hxz_eq] using hxz_mem
  have hpow_mem_zero :
      x ^ (p ^ r) ∈ (lambdaIdeal p K) ^ (n.factorization p * (p - 1) + 0) := by
    have hpow : x ^ (p ^ r) ∈ (lambdaIdeal p K) ^ (p ^ r) :=
      Ideal.pow_mem_pow hx (p ^ r)
    have hden : r * (p - 1) ≤ p ^ r :=
      samePrimeArtinHasseLog_den_le (p := p) r
    exact Ideal.pow_le_pow_right
      (by
        simpa [n, hfac, Nat.Prime.factorization_self (Fact.out : Nat.Prime p)]
          using hden)
      hpow
  calc
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) x *
        samePrimeFiniteArtinHasseTailTerm (p := p) (K := K) N r x hx
        =
      samePrimeNatDivEval (p := p) (K := K) N n s hn (x * z) hxz_mem := by
        rw [samePrimeFiniteArtinHasseTailTerm]
        exact (samePrimeNatDivEval_mul_left (p := p) (K := K) hn x hz hxz_mem).symm
    _ =
      samePrimeNatDivEval (p := p) (K := K) N n s hn
        (x ^ (p ^ r)) hpow_mem_s :=
        samePrimeNatDivEval_eq_of_eq (p := p) (K := K) hn hxz_eq
          hxz_mem hpow_mem_s
    _ =
      samePrimeNatDivEval (p := p) (K := K) N n 0 hn
        (x ^ (p ^ r)) hpow_mem_zero :=
        samePrimeNatDivEval_eq_of_mem (p := p) (K := K) hn
          hpow_mem_s hpow_mem_zero
    _ = samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx := by
        simpa [n] using
          samePrimeNatDivEval_prime_pow_zero_eq_finiteArtinHasseLogTerm
            (p := p) (K := K) N r hx hpow_mem_zero

/-- The finite corrected Artin--Hasse tail
`sum_{2 <= r <= N} x^(p^r - 1) / p^r` in `R / lambda^(N+1)`. -/
noncomputable def samePrimeFiniteArtinHasseTail (N : ℕ)
    (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  ∑ r ∈ Finset.Icc 2 N,
    samePrimeFiniteArtinHasseTailTerm (p := p) (K := K) N r x hx

/-- The finite corrected Artin--Hasse unit factor `1 + tail_N`. -/
noncomputable def samePrimeFiniteArtinHasseTailUnit (N : ℕ)
    (x : ValuedIntegerRing p K) (hx : x ∈ lambdaIdeal p K) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  1 + samePrimeFiniteArtinHasseTail (p := p) (K := K) N x hx

theorem samePrimeFiniteArtinHasseTail_eq_of_sub_mem
    {N : ℕ} {x y : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hy : y ∈ lambdaIdeal p K)
    (hxy : x - y ∈ (lambdaIdeal p K) ^ (N + 1)) :
    samePrimeFiniteArtinHasseTail (p := p) (K := K) N x hx =
      samePrimeFiniteArtinHasseTail (p := p) (K := K) N y hy := by
  classical
  unfold samePrimeFiniteArtinHasseTail
  refine Finset.sum_congr rfl ?_
  intro r hr
  exact samePrimeFiniteArtinHasseTailTerm_eq_of_sub_mem
    (p := p) (K := K) (Finset.mem_Icc.mp hr).1 hx hy hxy

theorem samePrimeFiniteArtinHasseTailUnit_eq_of_sub_mem
    {N : ℕ} {x y : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hy : y ∈ lambdaIdeal p K)
    (hxy : x - y ∈ (lambdaIdeal p K) ^ (N + 1)) :
    samePrimeFiniteArtinHasseTailUnit (p := p) (K := K) N x hx =
      samePrimeFiniteArtinHasseTailUnit (p := p) (K := K) N y hy := by
  rw [samePrimeFiniteArtinHasseTailUnit, samePrimeFiniteArtinHasseTailUnit]
  rw [samePrimeFiniteArtinHasseTail_eq_of_sub_mem
    (p := p) (K := K) hx hy hxy]

theorem samePrimeFiniteArtinHasseTail_factorPow
    (hp_two : 2 < p) {M N : ℕ} (hMN : M ≤ N)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
        (samePrimeFiniteArtinHasseTail (p := p) (K := K) N x hx) =
      samePrimeFiniteArtinHasseTail (p := p) (K := K) M x hx := by
  classical
  let termN : ℕ → ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (M + 1) :=
    fun r ↦
      Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
        (samePrimeFiniteArtinHasseTailTerm (p := p) (K := K) N r x hx)
  let termM : ℕ → ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (M + 1) :=
    fun r ↦ samePrimeFiniteArtinHasseTailTerm (p := p) (K := K) M r x hx
  have hsubset : Finset.Icc 2 M ⊆ Finset.Icc 2 N := fun r hr ↦
    Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hr).1, (Finset.mem_Icc.mp hr).2.trans hMN⟩
  have hmap :
      Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
          (samePrimeFiniteArtinHasseTail (p := p) (K := K) N x hx) =
        ∑ r ∈ Finset.Icc 2 N, termN r := by
    rw [samePrimeFiniteArtinHasseTail, map_sum]
  have htail :
      ∀ r ∈ Finset.Icc 2 N, r ∉ Finset.Icc 2 M → termN r = 0 := by
    intro r hrN hrM
    have hr_two : 2 ≤ r := (Finset.mem_Icc.mp hrN).1
    have hM_lt_r : M < r := by
      by_contra hnot
      have hr_le_M : r ≤ M := Nat.le_of_not_gt hnot
      exact hrM (Finset.mem_Icc.mpr ⟨hr_two, hr_le_M⟩)
    change Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
        (samePrimeFiniteArtinHasseTailTerm (p := p) (K := K) N r x hx) = 0
    rw [samePrimeFiniteArtinHasseTailTerm_factorPow (p := p) (K := K) hMN hx]
    exact samePrimeFiniteArtinHasseTailTerm_eq_zero_of_succ_le
      (p := p) (K := K) (N := M) hx
      ((Nat.succ_le_of_lt hM_lt_r).trans
        (le_samePrimeArtinHasseTailTermOrder_of_two_lt
          (p := p) hp_two hr_two))
  have hrestrict :
      ∑ r ∈ Finset.Icc 2 N, termN r =
        ∑ r ∈ Finset.Icc 2 M, termN r :=
    (Finset.sum_subset hsubset htail).symm
  have hterms :
      ∑ r ∈ Finset.Icc 2 M, termN r =
        ∑ r ∈ Finset.Icc 2 M, termM r := by
    refine Finset.sum_congr rfl ?_
    intro r _hr
    exact samePrimeFiniteArtinHasseTailTerm_factorPow
      (p := p) (K := K) hMN hx
  calc
    Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
        (samePrimeFiniteArtinHasseTail (p := p) (K := K) N x hx)
        = ∑ r ∈ Finset.Icc 2 N, termN r := hmap
    _ = ∑ r ∈ Finset.Icc 2 M, termN r := hrestrict
    _ = ∑ r ∈ Finset.Icc 2 M, termM r := hterms
    _ = samePrimeFiniteArtinHasseTail (p := p) (K := K) M x hx := by
        simp [samePrimeFiniteArtinHasseTail, termM]

theorem samePrimeFiniteArtinHasseTailUnit_factorPow
    (hp_two : 2 < p) {M N : ℕ} (hMN : M ≤ N)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
        (samePrimeFiniteArtinHasseTailUnit (p := p) (K := K) N x hx) =
      samePrimeFiniteArtinHasseTailUnit (p := p) (K := K) M x hx := by
  rw [samePrimeFiniteArtinHasseTailUnit, samePrimeFiniteArtinHasseTailUnit]
  rw [map_add, map_one]
  rw [samePrimeFiniteArtinHasseTail_factorPow
    (p := p) (K := K) hp_two hMN hx]

theorem samePrimeFiniteArtinHasseTail_mul_left_eq_log_tail_sum
    (N : ℕ) {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) x *
        samePrimeFiniteArtinHasseTail (p := p) (K := K) N x hx =
      ∑ r ∈ Finset.Icc 2 N,
        samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx := by
  rw [samePrimeFiniteArtinHasseTail, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro r _hr
  exact samePrimeFiniteArtinHasseTailTerm_mul_left_eq_logTerm
    (p := p) (K := K) N r hx

theorem samePrimeFiniteArtinHasseLog_eq_first_two_add_tail
    {N : ℕ} (hN : 1 ≤ N)
    {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K) :
    samePrimeFiniteArtinHasseLog (p := p) (K := K) N x hx =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) x +
        samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N 1 x hx +
          Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) x *
            samePrimeFiniteArtinHasseTail (p := p) (K := K) N x hx := by
  classical
  let terms : ℕ → ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
    fun r ↦ samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N r x hx
  have hrange :
      Finset.range (N + 1) = insert 0 (insert 1 (Finset.Icc 2 N)) := by
    ext r
    simp
    omega
  have h0not : 0 ∉ insert 1 (Finset.Icc 2 N) := by
    simp
  have h1not : 1 ∉ Finset.Icc 2 N := by
    simp
  rw [samePrimeFiniteArtinHasseLog, hrange]
  change ∑ r ∈ insert 0 (insert 1 (Finset.Icc 2 N)), terms r = _
  rw [Finset.sum_insert h0not, Finset.sum_insert h1not]
  have hterm0 :
      terms 0 = Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) x :=
    samePrimeFiniteArtinHasseLogTerm_zero_eq_mk (p := p) (K := K) N hx
  have htail :
      ∑ r ∈ Finset.Icc 2 N, terms r =
        Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1)) x *
          samePrimeFiniteArtinHasseTail (p := p) (K := K) N x hx :=
    (samePrimeFiniteArtinHasseTail_mul_left_eq_log_tail_sum
      (p := p) (K := K) N hx).symm
  rw [hterm0, htail]
  simp [terms]
  ring

/-- The finite corrected Artin--Hasse tail specialized to the Dwork parameter
approximant at precision `N + 1`. -/
noncomputable def dworkParameterFiniteArtinHasseTail (N : ℕ) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  samePrimeFiniteArtinHasseTail (p := p) (K := K) N
    (dworkParameterApprox p K (N + 1))
    (dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) (N + 1))

/-- The finite corrected Artin--Hasse tail unit specialized to the Dwork
parameter approximant at precision `N + 1`. -/
noncomputable def dworkParameterFiniteArtinHasseTailUnit (N : ℕ) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1) :=
  samePrimeFiniteArtinHasseTailUnit (p := p) (K := K) N
    (dworkParameterApprox p K (N + 1))
    (dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) (N + 1))

theorem dworkParameterFiniteArtinHasseTail_factorPow
    (hp_two : 2 < p) {M N : ℕ} (hMN : M ≤ N) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
        (dworkParameterFiniteArtinHasseTail (p := p) (K := K) N) =
      dworkParameterFiniteArtinHasseTail (p := p) (K := K) M := by
  let xN : ValuedIntegerRing p K := dworkParameterApprox p K (N + 1)
  let xM : ValuedIntegerRing p K := dworkParameterApprox p K (M + 1)
  let hxN : xN ∈ lambdaIdeal p K :=
    dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) (N + 1)
  let hxM : xM ∈ lambdaIdeal p K :=
    dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) (M + 1)
  have hMN' : M + 1 ≤ N + 1 := Nat.succ_le_succ hMN
  have hsub : xN - xM ∈ (lambdaIdeal p K) ^ (M + 1) :=
    dworkParameterApprox_sub_mem_lambdaIdeal_pow (p := p) (K := K) hMN'
  calc
    Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
        (dworkParameterFiniteArtinHasseTail (p := p) (K := K) N)
        =
      samePrimeFiniteArtinHasseTail (p := p) (K := K) M xN hxN := by
        change Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
            (samePrimeFiniteArtinHasseTail (p := p) (K := K) N xN hxN) =
          samePrimeFiniteArtinHasseTail (p := p) (K := K) M xN hxN
        exact samePrimeFiniteArtinHasseTail_factorPow
          (p := p) (K := K) hp_two hMN hxN
    _ =
      samePrimeFiniteArtinHasseTail (p := p) (K := K) M xM hxM :=
        samePrimeFiniteArtinHasseTail_eq_of_sub_mem
          (p := p) (K := K) hxN hxM hsub
    _ = dworkParameterFiniteArtinHasseTail (p := p) (K := K) M := rfl

theorem dworkParameterFiniteArtinHasseTailUnit_factorPow
    (hp_two : 2 < p) {M N : ℕ} (hMN : M ≤ N) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
        (dworkParameterFiniteArtinHasseTailUnit (p := p) (K := K) N) =
      dworkParameterFiniteArtinHasseTailUnit (p := p) (K := K) M := by
  let xN : ValuedIntegerRing p K := dworkParameterApprox p K (N + 1)
  let xM : ValuedIntegerRing p K := dworkParameterApprox p K (M + 1)
  let hxN : xN ∈ lambdaIdeal p K :=
    dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) (N + 1)
  let hxM : xM ∈ lambdaIdeal p K :=
    dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) (M + 1)
  have hMN' : M + 1 ≤ N + 1 := Nat.succ_le_succ hMN
  have hsub : xN - xM ∈ (lambdaIdeal p K) ^ (M + 1) :=
    dworkParameterApprox_sub_mem_lambdaIdeal_pow (p := p) (K := K) hMN'
  calc
    Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
        (dworkParameterFiniteArtinHasseTailUnit (p := p) (K := K) N)
        =
      samePrimeFiniteArtinHasseTailUnit (p := p) (K := K) M xN hxN := by
        change Ideal.Quotient.factorPow (lambdaIdeal p K) (Nat.succ_le_succ hMN)
            (samePrimeFiniteArtinHasseTailUnit (p := p) (K := K) N xN hxN) =
          samePrimeFiniteArtinHasseTailUnit (p := p) (K := K) M xN hxN
        exact samePrimeFiniteArtinHasseTailUnit_factorPow
          (p := p) (K := K) hp_two hMN hxN
    _ =
      samePrimeFiniteArtinHasseTailUnit (p := p) (K := K) M xM hxM :=
        samePrimeFiniteArtinHasseTailUnit_eq_of_sub_mem
          (p := p) (K := K) hxN hxM hsub
    _ = dworkParameterFiniteArtinHasseTailUnit (p := p) (K := K) M := rfl

theorem dworkParameterFiniteArtinHasseLog_eq_first_two_add_tail
    {N : ℕ} (hN : 1 ≤ N) :
    dworkParameterFiniteArtinHasseLog (p := p) (K := K) N =
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
          (dworkParameterApprox p K (N + 1)) +
        samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N 1
          (dworkParameterApprox p K (N + 1))
          (dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) (N + 1)) +
          Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
            (dworkParameterApprox p K (N + 1)) *
            dworkParameterFiniteArtinHasseTail (p := p) (K := K) N :=
  samePrimeFiniteArtinHasseLog_eq_first_two_add_tail
    (p := p) (K := K) hN
    (dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) (N + 1))

theorem dworkParameterFiniteArtinHasse_first_two_add_tail_eq_zero
    {N : ℕ} (hN : 1 ≤ N) :
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
          (dworkParameterApprox p K (N + 1)) +
        samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N 1
          (dworkParameterApprox p K (N + 1))
          (dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) (N + 1)) +
          Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
            (dworkParameterApprox p K (N + 1)) *
            dworkParameterFiniteArtinHasseTail (p := p) (K := K) N = 0 := by
  rw [← dworkParameterFiniteArtinHasseLog_eq_first_two_add_tail
    (p := p) (K := K) hN]
  exact dworkParameterFiniteArtinHasseLog_eq_zero (p := p) (K := K) N

theorem dworkParameterFinite_corrected_factor_eq_zero
    {N : ℕ} (hN : 1 ≤ N) :
    let A : Type _ := ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ (N + 1)
    let xbar : A :=
      Ideal.Quotient.mk ((lambdaIdeal p K) ^ (N + 1))
        (dworkParameterApprox p K (N + 1))
    xbar * (xbar ^ (p - 1) +
        (p : A) * dworkParameterFiniteArtinHasseTailUnit (p := p) (K := K) N) = 0 := by
  intro A xbar
  let term1 : A := samePrimeFiniteArtinHasseLogTerm (p := p) (K := K) N 1
    (dworkParameterApprox p K (N + 1))
    (dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) (N + 1))
  let tail : A := dworkParameterFiniteArtinHasseTail (p := p) (K := K) N
  let tailUnit : A := dworkParameterFiniteArtinHasseTailUnit (p := p) (K := K) N
  have hzero :
      xbar + term1 + xbar * tail = 0 := by
    simpa [A, xbar, term1, tail] using
      dworkParameterFiniteArtinHasse_first_two_add_tail_eq_zero
        (p := p) (K := K) hN
  have hmul := congrArg (fun z : A ↦ (p : A) * z) hzero
  have hmul' :
      (p : A) * xbar + xbar ^ p + (p : A) * (xbar * tail) = 0 := by
    have hterm :
        (p : A) * term1 = xbar ^ p := by
      dsimp [A, xbar, term1]
      rw [← map_pow]
      simpa [pow_one] using
        dworkParameterFiniteArtinHasseLogTerm_natCast_prime_pow_mul_eq_mk
          (p := p) (K := K) N 1
    simpa [mul_add, hterm, A] using hmul
  have htarget :
      xbar * (xbar ^ (p - 1) + (p : A) * tailUnit) =
        (p : A) * xbar + xbar ^ p + (p : A) * (xbar * tail) := by
    have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
    have hxpow : xbar * xbar ^ (p - 1) = xbar ^ p := by
      rw [mul_comm, ← pow_succ, Nat.sub_one_add_one (Nat.ne_of_gt hp_pos)]
    have htailUnit : tailUnit = 1 + tail := by
      dsimp [tailUnit, tail, dworkParameterFiniteArtinHasseTailUnit,
        dworkParameterFiniteArtinHasseTail, samePrimeFiniteArtinHasseTailUnit]
    rw [htailUnit]
    calc
      xbar * (xbar ^ (p - 1) + (p : A) * (1 + tail)) =
          xbar * xbar ^ (p - 1) + (p : A) * xbar +
            (p : A) * (xbar * tail) := by
        ring
      _ = (p : A) * xbar + xbar ^ p + (p : A) * (xbar * tail) := by
        rw [hxpow]
        ring
  rw [htarget]
  exact hmul'

noncomputable def dworkParameterFiniteArtinHasseTailCoord (N : ℕ) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ N :=
  match N with
  | 0 => 0
  | N + 1 => dworkParameterFiniteArtinHasseTail (p := p) (K := K) N

@[simp]
theorem dworkParameterFiniteArtinHasseTailCoord_zero :
    dworkParameterFiniteArtinHasseTailCoord (p := p) (K := K) 0 = 0 := rfl

@[simp]
theorem dworkParameterFiniteArtinHasseTailCoord_succ (N : ℕ) :
    dworkParameterFiniteArtinHasseTailCoord (p := p) (K := K) (N + 1) =
      dworkParameterFiniteArtinHasseTail (p := p) (K := K) N := rfl

theorem dworkParameterFiniteArtinHasseTailCoord_factorPow
    (hp_two : 2 < p) {M N : ℕ} (hMN : M ≤ N) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) hMN
        (dworkParameterFiniteArtinHasseTailCoord (p := p) (K := K) N) =
      dworkParameterFiniteArtinHasseTailCoord (p := p) (K := K) M := by
  cases M with
  | zero =>
      exact quotient_pow_zero_eq_zero (p := p) (K := K)
        (lambdaIdeal p K)
        (Ideal.Quotient.factorPow (lambdaIdeal p K) hMN
          (dworkParameterFiniteArtinHasseTailCoord (p := p) (K := K) N))
  | succ M =>
      cases N with
      | zero =>
          exact False.elim (Nat.not_succ_le_zero M hMN)
      | succ N =>
          have hMN' : M ≤ N := Nat.succ_le_succ_iff.mp hMN
          simpa using
            dworkParameterFiniteArtinHasseTail_factorPow
              (p := p) (K := K) hp_two hMN'

noncomputable def dworkParameterFiniteArtinHasseTailUnitCoord (N : ℕ) :
    ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ N :=
  match N with
  | 0 => 0
  | N + 1 => dworkParameterFiniteArtinHasseTailUnit (p := p) (K := K) N

@[simp]
theorem dworkParameterFiniteArtinHasseTailUnitCoord_zero :
    dworkParameterFiniteArtinHasseTailUnitCoord (p := p) (K := K) 0 = 0 := rfl

@[simp]
theorem dworkParameterFiniteArtinHasseTailUnitCoord_succ (N : ℕ) :
    dworkParameterFiniteArtinHasseTailUnitCoord (p := p) (K := K) (N + 1) =
      dworkParameterFiniteArtinHasseTailUnit (p := p) (K := K) N := rfl

theorem dworkParameterFiniteArtinHasseTailUnitCoord_factorPow
    (hp_two : 2 < p) {M N : ℕ} (hMN : M ≤ N) :
    Ideal.Quotient.factorPow (lambdaIdeal p K) hMN
        (dworkParameterFiniteArtinHasseTailUnitCoord (p := p) (K := K) N) =
      dworkParameterFiniteArtinHasseTailUnitCoord (p := p) (K := K) M := by
  cases M with
  | zero =>
      exact quotient_pow_zero_eq_zero (p := p) (K := K)
        (lambdaIdeal p K)
        (Ideal.Quotient.factorPow (lambdaIdeal p K) hMN
          (dworkParameterFiniteArtinHasseTailUnitCoord (p := p) (K := K) N))
  | succ M =>
      cases N with
      | zero =>
          exact False.elim (Nat.not_succ_le_zero M hMN)
      | succ N =>
          have hMN' : M ≤ N := Nat.succ_le_succ_iff.mp hMN
          simpa using
            dworkParameterFiniteArtinHasseTailUnit_factorPow
              (p := p) (K := K) hp_two hMN'

/-- The completed corrected Artin--Hasse tail of the Dwork parameter. -/
noncomputable def artinHasseTail (hp_two : 2 < p) :
    DworkCompleteIntegerRing p K :=
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  ⟨fun N ↦
      (Ideal.quotientEquivAlgOfEq R (by
        ext y
        simp : (I ^ N • ⊤ : Ideal R) = I ^ N)).symm
        (dworkParameterFiniteArtinHasseTailCoord (p := p) (K := K) N),
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
                (dworkParameterFiniteArtinHasseTailCoord (p := p) (K := K) N)))
            =
          Ideal.Quotient.factorPow I hMN
            (dworkParameterFiniteArtinHasseTailCoord (p := p) (K := K) N) := by
            refine Quotient.inductionOn'
              (dworkParameterFiniteArtinHasseTailCoord (p := p) (K := K) N) ?_
            intro r
            rfl
        _ = dworkParameterFiniteArtinHasseTailCoord (p := p) (K := K) M :=
            dworkParameterFiniteArtinHasseTailCoord_factorPow
              (p := p) (K := K) hp_two hMN
        _ = (Ideal.quotientEquivAlgOfEq R hEqM)
            ((Ideal.quotientEquivAlgOfEq R hEqM).symm
              (dworkParameterFiniteArtinHasseTailCoord (p := p) (K := K) M)) := by
            refine Quotient.inductionOn'
              (dworkParameterFiniteArtinHasseTailCoord (p := p) (K := K) M) ?_
            intro r
            rfl
      ⟩

@[simp]
theorem artinHasseTail_evalₐ (hp_two : 2 < p) (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) N
        (artinHasseTail (p := p) (K := K) hp_two) =
      dworkParameterFiniteArtinHasseTailCoord (p := p) (K := K) N := by
  unfold artinHasseTail
  let hEq :
      ((lambdaIdeal p K) ^ N • ⊤ : Ideal (ValuedIntegerRing p K)) =
        (lambdaIdeal p K) ^ N := by
    ext y
    simp
  change
    (Ideal.quotientEquivAlgOfEq (ValuedIntegerRing p K) hEq)
      ((Ideal.quotientEquivAlgOfEq (ValuedIntegerRing p K) hEq).symm
        (dworkParameterFiniteArtinHasseTailCoord (p := p) (K := K) N)) =
      dworkParameterFiniteArtinHasseTailCoord (p := p) (K := K) N
  refine Quotient.inductionOn'
    (dworkParameterFiniteArtinHasseTailCoord (p := p) (K := K) N) ?_
  intro r
  rfl

@[simp]
theorem artinHasseTail_evalₐ_succ (hp_two : 2 < p) (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) (N + 1)
        (artinHasseTail (p := p) (K := K) hp_two) =
      dworkParameterFiniteArtinHasseTail (p := p) (K := K) N := by
  simp

/-- The completed corrected Artin--Hasse tail unit `1 + tail`. -/
noncomputable def artinHasseTailUnit (hp_two : 2 < p) :
    DworkCompleteIntegerRing p K :=
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  ⟨fun N ↦
      (Ideal.quotientEquivAlgOfEq R (by
        ext y
        simp : (I ^ N • ⊤ : Ideal R) = I ^ N)).symm
        (dworkParameterFiniteArtinHasseTailUnitCoord (p := p) (K := K) N),
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
                (dworkParameterFiniteArtinHasseTailUnitCoord (p := p) (K := K) N)))
            =
          Ideal.Quotient.factorPow I hMN
            (dworkParameterFiniteArtinHasseTailUnitCoord (p := p) (K := K) N) := by
            refine Quotient.inductionOn'
              (dworkParameterFiniteArtinHasseTailUnitCoord (p := p) (K := K) N) ?_
            intro r
            rfl
        _ = dworkParameterFiniteArtinHasseTailUnitCoord (p := p) (K := K) M :=
            dworkParameterFiniteArtinHasseTailUnitCoord_factorPow
              (p := p) (K := K) hp_two hMN
        _ = (Ideal.quotientEquivAlgOfEq R hEqM)
            ((Ideal.quotientEquivAlgOfEq R hEqM).symm
              (dworkParameterFiniteArtinHasseTailUnitCoord (p := p) (K := K) M)) := by
            refine Quotient.inductionOn'
              (dworkParameterFiniteArtinHasseTailUnitCoord (p := p) (K := K) M) ?_
            intro r
            rfl
      ⟩

@[simp]
theorem artinHasseTailUnit_evalₐ (hp_two : 2 < p) (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) N
        (artinHasseTailUnit (p := p) (K := K) hp_two) =
      dworkParameterFiniteArtinHasseTailUnitCoord (p := p) (K := K) N := by
  unfold artinHasseTailUnit
  let hEq :
      ((lambdaIdeal p K) ^ N • ⊤ : Ideal (ValuedIntegerRing p K)) =
        (lambdaIdeal p K) ^ N := by
    ext y
    simp
  change
    (Ideal.quotientEquivAlgOfEq (ValuedIntegerRing p K) hEq)
      ((Ideal.quotientEquivAlgOfEq (ValuedIntegerRing p K) hEq).symm
        (dworkParameterFiniteArtinHasseTailUnitCoord (p := p) (K := K) N)) =
      dworkParameterFiniteArtinHasseTailUnitCoord (p := p) (K := K) N
  refine Quotient.inductionOn'
    (dworkParameterFiniteArtinHasseTailUnitCoord (p := p) (K := K) N) ?_
  intro r
  rfl

@[simp]
theorem artinHasseTailUnit_evalₐ_succ (hp_two : 2 < p) (N : ℕ) :
    AdicCompletion.evalₐ (lambdaIdeal p K) (N + 1)
        (artinHasseTailUnit (p := p) (K := K) hp_two) =
      dworkParameterFiniteArtinHasseTailUnit (p := p) (K := K) N := by
  simp

theorem sq_le_samePrimeArtinHasseTailTermOrder {r : ℕ} (hr : 2 ≤ r) :
    (p - 1) ^ 2 ≤ samePrimeArtinHasseTailTermOrder (p := p) r := by
  have hidx := FormalDwork.artinHasseTailValuationIndex_ge_sq (p := p) hr
  have hpred_cast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
    omega
  have hsq_cast : (((p - 1) ^ 2 : ℕ) : ℤ) = ((p : ℤ) - 1) ^ 2 := by
    rw [Nat.cast_pow, hpred_cast]
  have htail : (((p - 1) ^ 2 : ℕ) : ℤ) ≤
      (samePrimeArtinHasseTailTermOrder (p := p) r : ℤ) := by
    rw [hsq_cast, intCast_samePrimeArtinHasseTailTermOrder (p := p) r]
    exact hidx
  exact_mod_cast htail

theorem samePrimeFiniteArtinHasseTail_eq_zero_of_succ_le_sq
    {N : ℕ} {x : ValuedIntegerRing p K} (hx : x ∈ lambdaIdeal p K)
    (hN : N + 1 ≤ (p - 1) ^ 2) :
    samePrimeFiniteArtinHasseTail (p := p) (K := K) N x hx = 0 := by
  classical
  unfold samePrimeFiniteArtinHasseTail
  exact Finset.sum_eq_zero fun r hr ↦
    samePrimeFiniteArtinHasseTailTerm_eq_zero_of_succ_le
      (p := p) (K := K) (N := N) hx
      (hN.trans
        (sq_le_samePrimeArtinHasseTailTermOrder
          (p := p) (Finset.mem_Icc.mp hr).1))

theorem dworkParameterFiniteArtinHasseTail_eq_zero_of_succ_le_sq
    {N : ℕ} (hN : N + 1 ≤ (p - 1) ^ 2) :
    dworkParameterFiniteArtinHasseTail (p := p) (K := K) N = 0 := by
  rw [dworkParameterFiniteArtinHasseTail]
  exact samePrimeFiniteArtinHasseTail_eq_zero_of_succ_le_sq
    (p := p) (K := K)
    (dworkParameterApprox_mem_lambdaIdeal (p := p) (K := K) (N + 1)) hN

theorem artinHasseTail_mem_dworkCompleteLambdaIdeal_pow (hp_two : 2 < p) :
    artinHasseTail (p := p) (K := K) hp_two ∈
      (dworkCompleteLambdaIdeal p K) ^ ((p - 1) ^ 2) := by
  apply dworkComplete_mem_lambdaIdeal_pow_of_evalₐ_eq_zero (p := p) (K := K)
  obtain ⟨N, hN⟩ : ∃ N, (p - 1) ^ 2 = N + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero ?_
    have hp_pred_pos : 0 < p - 1 := by omega
    exact pow_ne_zero 2 (Nat.ne_of_gt hp_pred_pos)
  rw [hN, artinHasseTail_evalₐ_succ]
  exact dworkParameterFiniteArtinHasseTail_eq_zero_of_succ_le_sq
    (p := p) (K := K) (by omega)

theorem artinHasseTailUnit_eq_one_add_artinHasseTail (hp_two : 2 < p) :
    artinHasseTailUnit (p := p) (K := K) hp_two =
      1 + artinHasseTail (p := p) (K := K) hp_two := by
  apply AdicCompletion.ext_evalₐ
  intro N
  cases N with
  | zero =>
      exact
        (quotient_pow_zero_eq_zero (p := p) (K := K) (lambdaIdeal p K) _).trans
          (quotient_pow_zero_eq_zero (p := p) (K := K) (lambdaIdeal p K) _).symm
  | succ N =>
      rw [artinHasseTailUnit_evalₐ_succ, map_add, map_one,
        artinHasseTail_evalₐ_succ]
      rfl

theorem artinHasseTailUnit_isUnit (hp_two : 2 < p) :
    IsUnit (artinHasseTailUnit (p := p) (K := K) hp_two) := by
  rw [artinHasseTailUnit_eq_one_add_artinHasseTail (p := p) (K := K) hp_two]
  apply isUnit_one_add_of_mem_dworkCompleteLambdaIdeal (p := p) (K := K)
  have hmem :=
    artinHasseTail_mem_dworkCompleteLambdaIdeal_pow (p := p) (K := K) hp_two
  have hpow_ne : (p - 1) ^ 2 ≠ 0 := by
    have hp_pred_pos : 0 < p - 1 := by omega
    exact pow_ne_zero 2 (Nat.ne_of_gt hp_pred_pos)
  exact Ideal.pow_le_self hpow_ne hmem


end DworkParameter
end PadicLogSetup
end CyclotomicUnits
end BernoulliRegular

end

module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FiniteLogBounds
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FlexibleLocalDenominators

/-!
# Finite logarithm on principal `Q`-units

This file defines the finite logarithm

`Log_N(1 + x) = sum_{1 <= n < ell * (N + 1)} (-1)^(n+1) x^n / n`

in `𝓞 R' / Q^(N+1)` for lifts `x ∈ Q`.  Division by the `ell`-power part of
`n` uses the local-denominator bridge, while the prime-to-`Q` part of `n` is
inverted directly in the quotient.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace ConductorFlexibleFullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (F : ConductorFlexibleFullTeichStickelbergerSetup ℓ p k K R')

/-- Number of terms in the finite logarithm, including the dummy zero-th term
used for convenient `Finset.range` sums. -/
def finiteLogCutoff (N : ℕ) : ℕ :=
  ℓ * (N + 1)

/-- The forced `Q`-adic order of `x^n / n` when `x ∈ Q`. -/
def finiteLogTermOrder (n : ℕ) : ℕ :=
  n - (ℓ - 1) * n.factorization ℓ

theorem one_le_finiteLogTermOrder {n : ℕ} (hn : n ≠ 0) :
    1 ≤ finiteLogTermOrder (ℓ := ℓ) n := by
  simpa [finiteLogTermOrder] using
    Nat.one_le_sub_pred_mul_factorization (ell := ℓ) (n := n)
      (Fact.out : Nat.Prime ℓ) hn

theorem succ_le_finiteLogTermOrder_of_cutoff_le {N n : ℕ}
    (hn : finiteLogCutoff (ℓ := ℓ) N ≤ n) :
    N + 1 ≤ finiteLogTermOrder (ℓ := ℓ) n := by
  simpa [finiteLogCutoff, finiteLogTermOrder] using
    Nat.succ_le_sub_pred_mul_factorization_of_mul_succ_le
      (ell := ℓ) (N := N) (n := n) (Fact.out : Nat.Prime ℓ) hn

theorem factorization_mul_pred_add_finiteLogTermOrder {n : ℕ} (hn : n ≠ 0) :
    n.factorization ℓ * (ℓ - 1) + finiteLogTermOrder (ℓ := ℓ) n = n := by
  have hle :
      n.factorization ℓ * (ℓ - 1) ≤ n := by
    have h := Nat.factorization_mul_pred_le_pred (ell := ℓ) (n := n)
      (Fact.out : Nat.Prime ℓ) hn
    omega
  simp [finiteLogTermOrder, Nat.mul_comm (ℓ - 1) (n.factorization ℓ),
    Nat.add_sub_cancel' hle]

theorem pow_mem_Q_pow_factorization_mul_pred_add_finiteLogTermOrder
    {n : ℕ} (hn : n ≠ 0) {x : 𝓞 R'} (hx : x ∈ F.Q) :
    x ^ n ∈ F.Q ^ (n.factorization ℓ * (ℓ - 1) + finiteLogTermOrder (ℓ := ℓ) n) := by
  simpa [factorization_mul_pred_add_finiteLogTermOrder (ℓ := ℓ) hn] using
    Ideal.pow_mem_pow hx n

/-- The prime-to-`ell` part of a nonzero natural number is outside `Q`. -/
theorem natCast_ordCompl_not_mem_Q {n : ℕ} (hn : n ≠ 0) :
    ((ordCompl[ℓ] n : ℕ) : 𝓞 R') ∉ F.Q :=
  F.toConductorFlexibleTraceFormStickelbergerSetup.natCast_not_mem_Q_of_not_dvd
    (Nat.not_dvd_ordCompl (Fact.out : Nat.Prime ℓ) hn)

/-- The prime-to-`ell` part of a nonzero natural number as a quotient
denominator away from `Q`. -/
def ordComplPrimeCompl {n : ℕ} (hn : n ≠ 0) : F.Q.primeCompl :=
  ⟨(ordCompl[ℓ] n : 𝓞 R'), F.natCast_ordCompl_not_mem_Q hn⟩

theorem finiteLogTermData_exists {n : ℕ} (hn : n ≠ 0)
    {x : 𝓞 R'} (hx : x ∈ F.Q) :
    ∃ y : 𝓞 R', ∃ d : F.Q.primeCompl,
      ((ℓ : 𝓞 R') ^ n.factorization ℓ) * y = (d : 𝓞 R') * x ^ n ∧
        y ∈ F.Q ^ finiteLogTermOrder (ℓ := ℓ) n := by
  simpa [finiteLogTermOrder] using
    F.exists_primeCompl_natCast_ell_pow_denom_of_mem_Q_pow
      (m := n.factorization ℓ)
      (s := finiteLogTermOrder (ℓ := ℓ) n)
      (x := x ^ n)
      (F.pow_mem_Q_pow_factorization_mul_pred_add_finiteLogTermOrder hn hx)

/-- Chosen numerator representing `x^n / ell^v_ell(n)` locally at `Q`. -/
noncomputable def finiteLogTermNumerator (n : ℕ) (x : 𝓞 R') (hx : x ∈ F.Q) :
    𝓞 R' :=
  if hn : n = 0 then 0 else
    Classical.choose (finiteLogTermData_exists (F := F) hn hx)

/-- Chosen denominator away from `Q` representing `x^n / ell^v_ell(n)`. -/
noncomputable def finiteLogTermDenom (n : ℕ) (x : 𝓞 R') (hx : x ∈ F.Q) :
    F.Q.primeCompl :=
  if hn : n = 0 then 1 else
    Classical.choose (Classical.choose_spec (finiteLogTermData_exists (F := F) hn hx))

theorem finiteLogTermNumerator_spec {n : ℕ} (hn : n ≠ 0)
    {x : 𝓞 R'} (hx : x ∈ F.Q) :
    ((ℓ : 𝓞 R') ^ n.factorization ℓ) *
        F.finiteLogTermNumerator n x hx =
      (F.finiteLogTermDenom n x hx : 𝓞 R') * x ^ n ∧
    F.finiteLogTermNumerator n x hx ∈ F.Q ^ finiteLogTermOrder (ℓ := ℓ) n := by
  unfold finiteLogTermNumerator finiteLogTermDenom
  rw [dif_neg hn, dif_neg hn]
  exact Classical.choose_spec
    (Classical.choose_spec (finiteLogTermData_exists (F := F) hn hx))

theorem finiteLogTermNumerator_mul_spec {n : ℕ} (hn : n ≠ 0)
    {x : 𝓞 R'} (hx : x ∈ F.Q) :
    ((ℓ : 𝓞 R') ^ n.factorization ℓ) *
        F.finiteLogTermNumerator n x hx =
      (F.finiteLogTermDenom n x hx : 𝓞 R') * x ^ n :=
  (F.finiteLogTermNumerator_spec hn hx).1

theorem finiteLogTermNumerator_mem_Q_pow {n : ℕ} (hn : n ≠ 0)
    {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteLogTermNumerator n x hx ∈ F.Q ^ finiteLogTermOrder (ℓ := ℓ) n :=
  (F.finiteLogTermNumerator_spec hn hx).2

/-- Unsigned finite-log term `x^n / n` in `𝓞 R' / Q^(N+1)`. -/
noncomputable def finiteLogTermCore (N n : ℕ) (x : 𝓞 R') (hx : x ∈ F.Q) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  if hn : n = 0 then 0 else
    F.quotientFractionEvalPrimeCompl N
      (F.finiteLogTermNumerator n x hx)
      (F.finiteLogTermDenom n x hx * F.ordComplPrimeCompl hn)

/-- Signed finite-log term `(-1)^(n+1) x^n / n`. -/
noncomputable def finiteLogTerm (N n : ℕ) (x : 𝓞 R') (hx : x ∈ F.Q) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1)) *
    F.finiteLogTermCore N n x hx

@[simp]
theorem finiteLogTermCore_zero (N : ℕ) (x : 𝓞 R') (hx : x ∈ F.Q) :
    F.finiteLogTermCore N 0 x hx = 0 := by
  simp [finiteLogTermCore]

@[simp]
theorem finiteLogTerm_zero (N : ℕ) (x : 𝓞 R') (hx : x ∈ F.Q) :
    F.finiteLogTerm N 0 x hx = 0 := by
  simp [finiteLogTerm]

/-- The lift-level finite logarithm on `1 + x`, for `x ∈ Q`. -/
noncomputable def finiteLog (N : ℕ) (x : 𝓞 R') (hx : x ∈ F.Q) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  ∑ n ∈ Finset.range (finiteLogCutoff (ℓ := ℓ) N), F.finiteLogTerm N n x hx

/-- A local fraction with numerator in `Q^s` lands in `Q^s / Q^(N+1)`. -/
theorem quotientFractionEvalPrimeCompl_mem_map_Q_pow_of_mem
    (N s : ℕ) {y : 𝓞 R'} (d : F.Q.primeCompl) (hy : y ∈ F.Q ^ s) :
    F.quotientFractionEvalPrimeCompl N y d ∈
      Ideal.map (Ideal.Quotient.mk (F.Q ^ (N + 1))) (F.Q ^ s) := by
  rw [show
      F.quotientFractionEvalPrimeCompl N y d =
        F.quotientFractionEval N y (d : 𝓞 R') d.property
      from rfl]
  rw [F.quotientFractionEval_eq_mk_mul_inv]
  exact
    (Ideal.map (Ideal.Quotient.mk (F.Q ^ (N + 1))) (F.Q ^ s)).mul_mem_right
      (F.quotientInvOfNotMemQ N (d : 𝓞 R') d.property)
      (Ideal.mem_map_of_mem (Ideal.Quotient.mk (F.Q ^ (N + 1))) hy)

theorem finiteLogTermCore_mem_map_Q_pow {N n : ℕ} (hn : n ≠ 0)
    {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteLogTermCore N n x hx ∈
      Ideal.map (Ideal.Quotient.mk (F.Q ^ (N + 1)))
        (F.Q ^ finiteLogTermOrder (ℓ := ℓ) n) := by
  rw [finiteLogTermCore, dif_neg hn]
  exact F.quotientFractionEvalPrimeCompl_mem_map_Q_pow_of_mem N
    (finiteLogTermOrder (ℓ := ℓ) n)
    (F.finiteLogTermDenom n x hx * F.ordComplPrimeCompl hn)
    (F.finiteLogTermNumerator_mem_Q_pow hn hx)

theorem finiteLogTerm_mem_map_Q_pow {N n : ℕ} (hn : n ≠ 0)
    {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteLogTerm N n x hx ∈
      Ideal.map (Ideal.Quotient.mk (F.Q ^ (N + 1)))
        (F.Q ^ finiteLogTermOrder (ℓ := ℓ) n) :=
  (Ideal.map (Ideal.Quotient.mk (F.Q ^ (N + 1)))
      (F.Q ^ finiteLogTermOrder (ℓ := ℓ) n)).mul_mem_left
        ((-1 : 𝓞 R' ⧸ F.Q ^ (N + 1)) ^ (n + 1))
        (F.finiteLogTermCore_mem_map_Q_pow hn hx)

theorem eq_zero_of_mem_map_Q_pow_of_succ_le {N s : ℕ}
    {z : 𝓞 R' ⧸ F.Q ^ (N + 1)}
    (hz : z ∈ Ideal.map (Ideal.Quotient.mk (F.Q ^ (N + 1))) (F.Q ^ s))
    (hs : N + 1 ≤ s) :
    z = 0 := by
  rcases (Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk (F.Q ^ (N + 1))) Ideal.Quotient.mk_surjective).1 hz with
    ⟨y, hy, rfl⟩
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact (Ideal.pow_le_pow_right hs) hy

/-- Terms beyond the finite-log cutoff vanish in the quotient. -/
theorem finiteLogTerm_eq_zero_of_cutoff_le {N n : ℕ}
    (hn : finiteLogCutoff (ℓ := ℓ) N ≤ n)
    {x : 𝓞 R'} (hx : x ∈ F.Q) :
    F.finiteLogTerm N n x hx = 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp
  exact F.eq_zero_of_mem_map_Q_pow_of_succ_le
    (F.finiteLogTerm_mem_map_Q_pow hn0 hx)
    (succ_le_finiteLogTermOrder_of_cutoff_le (ℓ := ℓ) hn)

/-- If two `Q`-lifts agree modulo `Q^(N+1)`, their `n`-th powers differ by
enough extra `Q`-adic order to survive division by `n`. -/
theorem pow_sub_pow_mem_Q_pow_add {N n : ℕ} (hn : n ≠ 0)
    {x y : 𝓞 R'} (hx : x ∈ F.Q) (hy : y ∈ F.Q)
    (hxy : x - y ∈ F.Q ^ (N + 1)) :
    x ^ n - y ^ n ∈ F.Q ^ (N + n) := by
  classical
  let g : 𝓞 R' := ∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)
  have hg : g ∈ F.Q ^ (n - 1) := by
    refine Ideal.sum_mem _ ?_
    intro i hi
    have hi_lt : i < n := Finset.mem_range.mp hi
    have hix : x ^ i ∈ F.Q ^ i := Ideal.pow_mem_pow hx i
    have hiy : y ^ (n - 1 - i) ∈ F.Q ^ (n - 1 - i) :=
      Ideal.pow_mem_pow hy (n - 1 - i)
    have hmul : x ^ i * y ^ (n - 1 - i) ∈
        F.Q ^ i * F.Q ^ (n - 1 - i) :=
      Ideal.mul_mem_mul hix hiy
    rw [← pow_add] at hmul
    have hidx : i + (n - 1 - i) = n - 1 := by omega
    simpa [hidx] using hmul
  have hprod : (x - y) * g ∈ F.Q ^ (N + n) := by
    have hmul : (x - y) * g ∈ F.Q ^ (N + 1) * F.Q ^ (n - 1) :=
      Ideal.mul_mem_mul hxy hg
    rw [← pow_add] at hmul
    have hidx : (N + 1) + (n - 1) = N + n := by omega
    simpa [hidx] using hmul
  have hgeom : (x - y) * g = x ^ n - y ^ n := by
    change (x - y) *
        (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) = x ^ n - y ^ n
    rw [mul_comm]
    exact geom_sum₂_mul x y n
  simpa [hgeom] using hprod

private theorem finiteLogTermCore_common_num_mem {N n : ℕ} (hn : n ≠ 0)
    {x y : 𝓞 R'} (hx : x ∈ F.Q) (hy : y ∈ F.Q)
    (hxy : x - y ∈ F.Q ^ (N + 1)) :
    F.finiteLogTermNumerator n x hx *
          ((F.finiteLogTermDenom n y hy * F.ordComplPrimeCompl hn : F.Q.primeCompl) :
            𝓞 R') -
        F.finiteLogTermNumerator n y hy *
          ((F.finiteLogTermDenom n x hx * F.ordComplPrimeCompl hn : F.Q.primeCompl) :
            𝓞 R') ∈
      F.Q ^ (N + 1) := by
  classical
  let m : ℕ := n.factorization ℓ
  let c : 𝓞 R' := (F.ordComplPrimeCompl hn : 𝓞 R')
  let yx : 𝓞 R' := F.finiteLogTermNumerator n x hx
  let yy : 𝓞 R' := F.finiteLogTermNumerator n y hy
  let dx : 𝓞 R' := (F.finiteLogTermDenom n x hx : 𝓞 R')
  let dy : 𝓞 R' := (F.finiteLogTermDenom n y hy : 𝓞 R')
  let num : 𝓞 R' := yx * (dy * c) - yy * (dx * c)
  have hxspec : ((ℓ : 𝓞 R') ^ m) * yx = dx * x ^ n := by
    simpa [m, yx, dx] using F.finiteLogTermNumerator_mul_spec hn hx
  have hyspec : ((ℓ : 𝓞 R') ^ m) * yy = dy * y ^ n := by
    simpa [m, yy, dy] using F.finiteLogTermNumerator_mul_spec hn hy
  have hnum_mul :
      ((ℓ : 𝓞 R') ^ m) * num = dx * dy * c * (x ^ n - y ^ n) := by
    calc
      ((ℓ : 𝓞 R') ^ m) * num
          = (((ℓ : 𝓞 R') ^ m) * yx) * (dy * c) -
              (((ℓ : 𝓞 R') ^ m) * yy) * (dx * c) := by
                simp [num]
                ring
      _ = (dx * x ^ n) * (dy * c) - (dy * y ^ n) * (dx * c) := by
                rw [hxspec, hyspec]
      _ = dx * dy * c * (x ^ n - y ^ n) := by
                ring
  have hpowdiff_big : x ^ n - y ^ n ∈
      F.Q ^ (m * (ℓ - 1) + (N + 1)) := by
    have hpowdiff : x ^ n - y ^ n ∈ F.Q ^ (N + n) :=
      F.pow_sub_pow_mem_Q_pow_add hn hx hy hxy
    have horder : 1 ≤ finiteLogTermOrder (ℓ := ℓ) n :=
      one_le_finiteLogTermOrder (ℓ := ℓ) hn
    have hle : m * (ℓ - 1) + (N + 1) ≤ N + n := by
      have hsum : m * (ℓ - 1) + finiteLogTermOrder (ℓ := ℓ) n = n := by
        simpa [m] using factorization_mul_pred_add_finiteLogTermOrder (ℓ := ℓ) hn
      omega
    exact (Ideal.pow_le_pow_right hle) hpowdiff
  have hmul_mem :
      ((ℓ : 𝓞 R') ^ m) * num ∈ F.Q ^ (m * (ℓ - 1) + (N + 1)) := by
    rw [hnum_mul]
    exact Ideal.mul_mem_left _ (dx * dy * c) hpowdiff_big
  have hnum_mem : num ∈ F.Q ^ (N + 1) :=
    F.mem_Q_pow_of_natCast_ell_pow_mul_mem_Q_pow_add_mul_pred
      (m := m) (n := N + 1) hmul_mem
  simpa [num, yx, yy, dx, dy, c] using hnum_mem

/-- The unsigned finite-log term is independent of the chosen lift modulo
`Q^(N+1)`. -/
theorem finiteLogTermCore_eq_of_sub_mem {N n : ℕ} (hn : n ≠ 0)
    {x y : 𝓞 R'} (hx : x ∈ F.Q) (hy : y ∈ F.Q)
    (hxy : x - y ∈ F.Q ^ (N + 1)) :
    F.finiteLogTermCore N n x hx = F.finiteLogTermCore N n y hy := by
  rw [← sub_eq_zero]
  rw [finiteLogTermCore, dif_neg hn, finiteLogTermCore, dif_neg hn]
  let sx : F.Q.primeCompl := F.finiteLogTermDenom n x hx * F.ordComplPrimeCompl hn
  let sy : F.Q.primeCompl := F.finiteLogTermDenom n y hy * F.ordComplPrimeCompl hn
  let num : 𝓞 R' :=
    F.finiteLogTermNumerator n x hx * (sy : 𝓞 R') -
      F.finiteLogTermNumerator n y hy * (sx : 𝓞 R')
  have hnum : num ∈ F.Q ^ (N + 1) := by
    simpa [num, sx, sy] using
      F.finiteLogTermCore_common_num_mem hn hx hy hxy
  have hsub :=
    F.quotientFractionEvalPrimeCompl_sub
      N (F.finiteLogTermNumerator n x hx) (F.finiteLogTermNumerator n y hy) sx sy
  rw [← hsub]
  exact
    F.quotientFractionEvalPrimeCompl_eq_zero_of_mem
      N (sx * sy) hnum

/-- The signed finite-log term is independent of the chosen lift modulo
`Q^(N+1)`. -/
theorem finiteLogTerm_eq_of_sub_mem {N n : ℕ}
    {x y : 𝓞 R'} (hx : x ∈ F.Q) (hy : y ∈ F.Q)
    (hxy : x - y ∈ F.Q ^ (N + 1)) :
    F.finiteLogTerm N n x hx = F.finiteLogTerm N n y hy := by
  by_cases hn : n = 0
  · subst n
    simp
  simp [finiteLogTerm, F.finiteLogTermCore_eq_of_sub_mem hn hx hy hxy]

/-- The lift-level finite logarithm only depends on the class of `x` modulo
`Q^(N+1)`. -/
theorem finiteLog_eq_of_sub_mem {N : ℕ}
    {x y : 𝓞 R'} (hx : x ∈ F.Q) (hy : y ∈ F.Q)
    (hxy : x - y ∈ F.Q ^ (N + 1)) :
    F.finiteLog N x hx = F.finiteLog N y hy := by
  classical
  unfold finiteLog
  refine Finset.sum_congr rfl ?_
  intro n _hn
  exact F.finiteLogTerm_eq_of_sub_mem hx hy hxy

end ConductorFlexibleFullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

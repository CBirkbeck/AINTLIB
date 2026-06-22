import BernoulliRegular.FLT37.Eichler.CaseIICor823Level71FormalSum68LogRec
import BernoulliRegular.FLT37.Eichler.CaseIICor823Level71FormalSum68Value

/-!
# `(formalSum68 : ℚ) = 68!·Lr 68 = N/120`: the degree-`68` Artin-Hasse log coefficient, DISCHARGED

This file discharges the value residual `FormalSum68RatValue`
(`CaseIICor823Level71FormalSum68Value`): the degree-`68` Artin-Hasse log coefficient
`formalSum68 = ∑ₙ rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 68 n`
(`CaseIICor823Level71Factorial37Extraction.formalSum68`) equals the verified reduced rational
`N / 120`, `N = −4620…373353`.  It imports only; it does **not** modify any existing file.  No
`sorry`, no `axiom`, no `native_decide`.

## The two pieces (both proven)

* **The bridge** `formalSum68_rat_eq`: by
  `coe_sum_rationalArtinHasseNormalizedFactorialWeightedLogCoeff` (at `d = 68`),
  `(formalSum68 : ℚ) = 68!·[T⁶⁸] logOf(g_AH)`, and `[T⁶⁸] logOf(g_AH) = Lr 68` by `coeff_logG_eq`
  (`68 ≤ 68`), where `g_AH = rationalArtinHasseNormalizedExpMinusOneSeries 37`.  So
  `(formalSum68 : ℚ) = 68!·Lr 68`.

* **The value** `factorial_mul_Lr68_eq`: `68!·Lr 68 = N/120`, proved by the explicit `68`-step
  evaluation of the log-coefficient recurrence `Lr_succ` (`Lr 1 = 1/2`, …, `Lr 68 = …`), each step a
  bounded `norm_num` over the closed-form coefficients `gco j = c (j+1)`.  This is the genuine
  degree-`68` Artin-Hasse computation, the `E₃₇ ≡ exp(T)·(1 + T³⁷/37) mod T⁷⁴` structure carried all
  the way to the exact rational.

Combining: `(formalSum68 : ℚ) = N/120`, i.e. `FormalSum68RatValue` (`formalSum68RatValue_proven`).
Hence (by `formalSum68ResidueModSq37_of_ratValue`) `formalSum68 ≡ 777 = 37·21 (mod 37²)`, grounding
the corrected second digit `r₆₈ = 21` in the actual power series.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §8.4.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace BernoulliRegular.FLT37.Eichler

open PowerSeries

/-- **`(formalSum68 : ℚ) = 68!·Lr 68`** (proven, axiom-clean): the degree-`68` Artin-Hasse log
coefficient as `68!` times the explicit log-coefficient `Lr 68`.

`coe_sum_rationalArtinHasseNormalizedFactorialWeightedLogCoeff` (at `d = 68`) gives
`(formalSum68 : ℚ) = 68!·[T⁶⁸] logOf(g_AH)` with `g_AH =
rationalArtinHasseNormalizedExpMinusOneSeries 37`; `[T⁶⁸] logOf(g_AH) = [T⁶⁸] logG = Lr 68` by
`ArtinHasse37.coeff_logG_eq` (`68 ≤ 68`).  So `Lr 68` *is* the degree-`68` log coefficient, and
`formalSum68` is `68!` times it. -/
theorem formalSum68_rat_eq :
    ((formalSum68 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) : ℚ) =
      (Nat.factorial 68 : ℚ) * ArtinHasse37.Lr 68 := by
  have hcoe := CyclotomicUnits.coe_sum_rationalArtinHasseNormalizedFactorialWeightedLogCoeff
    (p := 37) 68
  -- `formalSum68 = ∑ₙ rationalArtinHasse…Coeff 68 n`, so its coercion is `68!·[T⁶⁸] logOf(g_AH)`.
  rw [show (formalSum68 : Furtwaengler.DieudonneDwork.rIntegralRatSubring 37) =
      ∑ n ∈ Finset.Icc 1 68,
        CyclotomicUnits.rationalArtinHasseNormalizedFactorialWeightedLogCoeff 37 68 n from rfl,
    hcoe]
  -- `[T⁶⁸] logOf(g_AH) = [T⁶⁸] logG = Lr 68`.
  rw [show PowerSeries.logOf
        (CyclotomicUnits.rationalArtinHasseNormalizedExpMinusOneSeries 37) =
      ArtinHasse37.logG from rfl,
    ArtinHasse37.coeff_logG_eq (by norm_num : (68 : ℕ) ≤ 68)]

/-! ## The explicit `Lr 1 … Lr 68` coefficient values

Each `lr_coeff_k` is one step of the `ArtinHasse37.Lr_succ` recurrence
`Lr (n+1) = gco (n+1) − (∑_{k<n} (k+1)·Lr (k+1)·gco (n−k)) / (n+1)`, a bounded `norm_num` over the
closed-form coefficients `gco j = c (j+1)` and the previously-computed values.  Splitting the
degree-`68` evaluation into these named per-degree facts turns `factorial_mul_Lr68_eq` into a
one-line consequence of `lr_coeff_68`. -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 1`**, the degree-`1` Artin-Hasse log coefficient: the `1`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_1 : ArtinHasse37.Lr 1 = (1 : ℚ)/2 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 2`**, the degree-`2` Artin-Hasse log coefficient: the `2`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_2 : ArtinHasse37.Lr 2 = (1 : ℚ)/24 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 3`**, the degree-`3` Artin-Hasse log coefficient: the `3`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_3 : ArtinHasse37.Lr 3 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 4`**, the degree-`4` Artin-Hasse log coefficient: the `4`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_4 : ArtinHasse37.Lr 4 = (-1 : ℚ)/2880 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 5`**, the degree-`5` Artin-Hasse log coefficient: the `5`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_5 : ArtinHasse37.Lr 5 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 6`**, the degree-`6` Artin-Hasse log coefficient: the `6`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_6 : ArtinHasse37.Lr 6 = (1 : ℚ)/181440 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 7`**, the degree-`7` Artin-Hasse log coefficient: the `7`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_7 : ArtinHasse37.Lr 7 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 8`**, the degree-`8` Artin-Hasse log coefficient: the `8`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_8 : ArtinHasse37.Lr 8 = (-1 : ℚ)/9676800 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 9`**, the degree-`9` Artin-Hasse log coefficient: the `9`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_9 : ArtinHasse37.Lr 9 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 10`**, the degree-`10` Artin-Hasse log coefficient: the `10`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_10 : ArtinHasse37.Lr 10 = (1 : ℚ)/479001600 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 11`**, the degree-`11` Artin-Hasse log coefficient: the `11`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_11 : ArtinHasse37.Lr 11 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 12`**, the degree-`12` Artin-Hasse log coefficient: the `12`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_12 : ArtinHasse37.Lr 12 = (-691 : ℚ)/15692092416000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 13`**, the degree-`13` Artin-Hasse log coefficient: the `13`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_13 : ArtinHasse37.Lr 13 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 14`**, the degree-`14` Artin-Hasse log coefficient: the `14`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_14 : ArtinHasse37.Lr 14 = (1 : ℚ)/1046139494400 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 15`**, the degree-`15` Artin-Hasse log coefficient: the `15`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_15 : ArtinHasse37.Lr 15 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 16`**, the degree-`16` Artin-Hasse log coefficient: the `16`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_16 : ArtinHasse37.Lr 16 = (-3617 : ℚ)/170729965486080000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 17`**, the degree-`17` Artin-Hasse log coefficient: the `17`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_17 : ArtinHasse37.Lr 17 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 18`**, the degree-`18` Artin-Hasse log coefficient: the `18`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_18 : ArtinHasse37.Lr 18 = (43867 : ℚ)/91963695909076992000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 19`**, the degree-`19` Artin-Hasse log coefficient: the `19`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_19 : ArtinHasse37.Lr 19 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 20`**, the degree-`20` Artin-Hasse log coefficient: the `20`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_20 : ArtinHasse37.Lr 20 = (-174611 : ℚ)/16057153253965824000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 21`**, the degree-`21` Artin-Hasse log coefficient: the `21`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_21 : ArtinHasse37.Lr 21 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 22`**, the degree-`22` Artin-Hasse log coefficient: the `22`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_22 : ArtinHasse37.Lr 22 = (77683 : ℚ)/310224200866619719680000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 23`**, the degree-`23` Artin-Hasse log coefficient: the `23`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_23 : ArtinHasse37.Lr 23 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 24`**, the degree-`24` Artin-Hasse log coefficient: the `24`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_24 : ArtinHasse37.Lr 24 = (-236364091 : ℚ)/40651779281561848066867200000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 25`**, the degree-`25` Artin-Hasse log coefficient: the `25`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_25 : ArtinHasse37.Lr 25 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 26`**, the degree-`26` Artin-Hasse log coefficient: the `26`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_26 : ArtinHasse37.Lr 26 = (657931 : ℚ)/4839497533519267627008000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 27`**, the degree-`27` Artin-Hasse log coefficient: the `27`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_27 : ArtinHasse37.Lr 27 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 28`**, the degree-`28` Artin-Hasse log coefficient: the `28`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_28 : ArtinHasse37.Lr 28 = (-3392780147 : ℚ)/1061011439248764234545233920000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 29`**, the degree-`29` Artin-Hasse log coefficient: the `29`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_29 : ArtinHasse37.Lr 29 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 30`**, the degree-`30` Artin-Hasse log coefficient: the `30`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_30 : ArtinHasse37.Lr 30 = (1723168255201 : ℚ)/22793708749381202050735260303360000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 31`**, the degree-`31` Artin-Hasse log coefficient: the `31`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_31 : ArtinHasse37.Lr 31 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 32`**, the degree-`32` Artin-Hasse log coefficient: the `32`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_32 : ArtinHasse37.Lr 32 = (-7709321041217 : ℚ)/4294295258757878412328997958451200000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 33`**, the degree-`33` Artin-Hasse log coefficient: the `33`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_33 : ArtinHasse37.Lr 33 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 34`**, the degree-`34` Artin-Hasse log coefficient: the `34`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_34 : ArtinHasse37.Lr 34 = (151628697551 : ℚ)/3542793588475249690171423315722240000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 35`**, the degree-`35` Artin-Hasse log coefficient: the `35`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_35 : ArtinHasse37.Lr 35 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 36`**, the degree-`36` Artin-Hasse log coefficient: the `36`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_36 : ArtinHasse37.Lr 36 = (18773799431927522740603911607964927408403960071 : ℚ)/694630578981318341402344729521017585664000000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 37`**, the degree-`37` Artin-Hasse log coefficient: the `37`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_37 : ArtinHasse37.Lr 37 = (1 : ℚ)/74 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 38`**, the degree-`38` Artin-Hasse log coefficient: the `38`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_38 : ArtinHasse37.Lr 38 = (382047200486925574696864298105025616378153 : ℚ)/169628957016194955165407748356780851200000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 39`**, the degree-`39` Artin-Hasse log coefficient: the `39`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_39 : ArtinHasse37.Lr 39 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 40`**, the degree-`40` Artin-Hasse log coefficient: the `40`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_40 : ArtinHasse37.Lr 40 = (-447988547290968928889543075960122114277201327623 : ℚ)/11934414899831412265617427543389673567027200000000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 41`**, the degree-`41` Artin-Hasse log coefficient: the `41`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_41 : ArtinHasse37.Lr 41 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 42`**, the degree-`42` Artin-Hasse log coefficient: the `42`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_42 : ArtinHasse37.Lr 42 = (2574305097660195090464365257404110153943558670343 : ℚ)/2880338487670039082818768999158343016292286464000000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 43`**, the degree-`43` Artin-Hasse log coefficient: the `43`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_43 : ArtinHasse37.Lr 43 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 44`**, the degree-`44` Artin-Hasse log coefficient: the `44`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_44 : ArtinHasse37.Lr 44 = (-4430606732707682706717581021244207416919143548489 : ℚ)/198292690443678881075686682118928104250870333440000000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 45`**, the degree-`45` Artin-Hasse log coefficient: the `45`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_45 : ArtinHasse37.Lr 45 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 46`**, the degree-`46` Artin-Hasse log coefficient: the `46`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_46 : ArtinHasse37.Lr 46 = (47326935553922974367210524545078970632158223458611 : ℚ)/83877808057676166695015466536306588098118151045120000000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 47`**, the degree-`47` Artin-Hasse log coefficient: the `47`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_47 : ArtinHasse37.Lr 47 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45, lr_coeff_46]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 48`**, the degree-`48` Artin-Hasse log coefficient: the `48`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_48 : ArtinHasse37.Lr 48 = (-10674230629477117053919143011149545973609645098460787231 : ℚ)/747411661815696172092608217974397840697663370880771686400000000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45, lr_coeff_46, lr_coeff_47]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 49`**, the degree-`49` Artin-Hasse log coefficient: the `49`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_49 : ArtinHasse37.Lr 49 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45, lr_coeff_46, lr_coeff_47, lr_coeff_48]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 50`**, the degree-`50` Artin-Hasse log coefficient: the `50`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_50 : ArtinHasse37.Lr 50 = (39244951174714589513733034968873334574489867727797273 : ℚ)/108504332503409889236672007511366202363725640191967232000000000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45, lr_coeff_46, lr_coeff_47, lr_coeff_48, lr_coeff_49]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 51`**, the degree-`51` Artin-Hasse log coefficient: the `51`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_51 : ArtinHasse37.Lr 51 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45, lr_coeff_46, lr_coeff_47, lr_coeff_48, lr_coeff_49, lr_coeff_50]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 52`**, the degree-`52` Artin-Hasse log coefficient: the `52`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_52 : ArtinHasse37.Lr 52 = (-127016692216716233528360746721211159087666125305554937613 : ℚ)/13864486326681163992317882443425079944941655529838314782720000000000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45, lr_coeff_46, lr_coeff_47, lr_coeff_48, lr_coeff_49, lr_coeff_50, lr_coeff_51]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 53`**, the degree-`53` Artin-Hasse log coefficient: the `53`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_53 : ArtinHasse37.Lr 53 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45, lr_coeff_46, lr_coeff_47, lr_coeff_48, lr_coeff_49, lr_coeff_50, lr_coeff_51, lr_coeff_52]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 54`**, the degree-`54` Artin-Hasse log coefficient: the `54`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_54 : ArtinHasse37.Lr 54 = (62388601083097314391937610034524444369747826630280057400343 : ℚ)/268851800155205123440632985613433095244341619041306697277636608000000000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45, lr_coeff_46, lr_coeff_47, lr_coeff_48, lr_coeff_49, lr_coeff_50, lr_coeff_51, lr_coeff_52, lr_coeff_53]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 55`**, the degree-`55` Artin-Hasse log coefficient: the `55`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_55 : ArtinHasse37.Lr 55 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45, lr_coeff_46, lr_coeff_47, lr_coeff_48, lr_coeff_49, lr_coeff_50, lr_coeff_51, lr_coeff_52, lr_coeff_53, lr_coeff_54]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 56`**, the degree-`56` Artin-Hasse log coefficient: the `56`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_56 : ArtinHasse37.Lr 56 = (-786153898496497550796440457636682252206905763412109991272831 : ℚ)/133744599219509449321733992063446639193676376567917093850395443200000000000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45, lr_coeff_46, lr_coeff_47, lr_coeff_48, lr_coeff_49, lr_coeff_50, lr_coeff_51, lr_coeff_52, lr_coeff_53, lr_coeff_54, lr_coeff_55]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 57`**, the degree-`57` Artin-Hasse log coefficient: the `57`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_57 : ArtinHasse37.Lr 57 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45, lr_coeff_46, lr_coeff_47, lr_coeff_48, lr_coeff_49, lr_coeff_50, lr_coeff_51, lr_coeff_52, lr_coeff_53, lr_coeff_54, lr_coeff_55, lr_coeff_56]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 58`**, the degree-`58` Artin-Hasse log coefficient: the `58`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_58 : ArtinHasse37.Lr 58 = (6696908917288727288692482488173390515944279363788281849015877 : ℚ)/44978308717521027806899141530937104760833365439790518661887987548160000000000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45, lr_coeff_46, lr_coeff_47, lr_coeff_48, lr_coeff_49, lr_coeff_50, lr_coeff_51, lr_coeff_52, lr_coeff_53, lr_coeff_54, lr_coeff_55, lr_coeff_56, lr_coeff_57]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 59`**, the degree-`59` Artin-Hasse log coefficient: the `59`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_59 : ArtinHasse37.Lr 59 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45, lr_coeff_46, lr_coeff_47, lr_coeff_48, lr_coeff_49, lr_coeff_50, lr_coeff_51, lr_coeff_52, lr_coeff_53, lr_coeff_54, lr_coeff_55, lr_coeff_56, lr_coeff_57, lr_coeff_58]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 60`**, the degree-`60` Artin-Hasse log coefficient: the `60`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_60 : ArtinHasse37.Lr 60 = (-2889899192406618534337244485310328645169614150010439752980232979622743 : ℚ)/766251321899553862617862106204733604510547669466214631943778331742217175040000000000000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45, lr_coeff_46, lr_coeff_47, lr_coeff_48, lr_coeff_49, lr_coeff_50, lr_coeff_51, lr_coeff_52, lr_coeff_53, lr_coeff_54, lr_coeff_55, lr_coeff_56, lr_coeff_57, lr_coeff_58, lr_coeff_59]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 61`**, the degree-`61` Artin-Hasse log coefficient: the `61`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_61 : ArtinHasse37.Lr 61 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45, lr_coeff_46, lr_coeff_47, lr_coeff_48, lr_coeff_49, lr_coeff_50, lr_coeff_51, lr_coeff_52, lr_coeff_53, lr_coeff_54, lr_coeff_55, lr_coeff_56, lr_coeff_57, lr_coeff_58, lr_coeff_59, lr_coeff_60]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 62`**, the degree-`62` Artin-Hasse log coefficient: the `62`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_62 : ArtinHasse37.Lr 62 = (975051594043339785055558361194097188609551327443665632606628933 : ℚ)/10206477814179871629941553196200247812328307285597264494755622134428467200000000000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45, lr_coeff_46, lr_coeff_47, lr_coeff_48, lr_coeff_49, lr_coeff_50, lr_coeff_51, lr_coeff_52, lr_coeff_53, lr_coeff_54, lr_coeff_55, lr_coeff_56, lr_coeff_57, lr_coeff_58, lr_coeff_59, lr_coeff_60, lr_coeff_61]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 63`**, the degree-`63` Artin-Hasse log coefficient: the `63`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_63 : ArtinHasse37.Lr 63 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45, lr_coeff_46, lr_coeff_47, lr_coeff_48, lr_coeff_49, lr_coeff_50, lr_coeff_51, lr_coeff_52, lr_coeff_53, lr_coeff_54, lr_coeff_55, lr_coeff_56, lr_coeff_57, lr_coeff_58, lr_coeff_59, lr_coeff_60, lr_coeff_61, lr_coeff_62]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 64`**, the degree-`64` Artin-Hasse log coefficient: the `64`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_64 : ArtinHasse37.Lr 64 = (-270867738965420172807370829286155031102028255999034036545315812106541 : ℚ)/111934850447223219360434211564855965767717039133436623604564698173162376921088000000000000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45, lr_coeff_46, lr_coeff_47, lr_coeff_48, lr_coeff_49, lr_coeff_50, lr_coeff_51, lr_coeff_52, lr_coeff_53, lr_coeff_54, lr_coeff_55, lr_coeff_56, lr_coeff_57, lr_coeff_58, lr_coeff_59, lr_coeff_60, lr_coeff_61, lr_coeff_62, lr_coeff_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 65`**, the degree-`65` Artin-Hasse log coefficient: the `65`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_65 : ArtinHasse37.Lr 65 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45, lr_coeff_46, lr_coeff_47, lr_coeff_48, lr_coeff_49, lr_coeff_50, lr_coeff_51, lr_coeff_52, lr_coeff_53, lr_coeff_54, lr_coeff_55, lr_coeff_56, lr_coeff_57, lr_coeff_58, lr_coeff_59, lr_coeff_60, lr_coeff_61, lr_coeff_62, lr_coeff_63, lr_coeff_64]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 66`**, the degree-`66` Artin-Hasse log coefficient: the `66`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_66 : ArtinHasse37.Lr 66 = (350193326959277853367603351866287159043988523158509655571239924496908843 : ℚ)/5713150240049232971099896846592574914050367953519757960678233480744678656338558976000000000000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45, lr_coeff_46, lr_coeff_47, lr_coeff_48, lr_coeff_49, lr_coeff_50, lr_coeff_51, lr_coeff_52, lr_coeff_53, lr_coeff_54, lr_coeff_55, lr_coeff_56, lr_coeff_57, lr_coeff_58, lr_coeff_59, lr_coeff_60, lr_coeff_61, lr_coeff_62, lr_coeff_63, lr_coeff_64, lr_coeff_65]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 67`**, the degree-`67` Artin-Hasse log coefficient: the `67`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_67 : ArtinHasse37.Lr 67 = (0 : ℚ)/1 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45, lr_coeff_46, lr_coeff_47, lr_coeff_48, lr_coeff_49, lr_coeff_50, lr_coeff_51, lr_coeff_52, lr_coeff_53, lr_coeff_54, lr_coeff_55, lr_coeff_56, lr_coeff_57, lr_coeff_58, lr_coeff_59, lr_coeff_60, lr_coeff_61, lr_coeff_62, lr_coeff_63, lr_coeff_64, lr_coeff_65, lr_coeff_66]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 800000 in
/-- **`ArtinHasse37.Lr 68`**, the degree-`68` Artin-Hasse log coefficient: the `68`-th step of
the `Lr_succ` recurrence, a bounded `norm_num` over the closed-form coefficients `gco`/`c` and
the previously-computed coefficients. -/
private theorem lr_coeff_68 : ArtinHasse37.Lr 68 = (-12488489445723169150509296621411434098546266945112512408183823600388469 : ℚ)/8043358516011342485192401357521637560153727139530922180665007798978015499607080960000000000000000 := by
  rw [ArtinHasse37.Lr_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num [ArtinHasse37.gco, ArtinHasse37.c, lr_coeff_1, lr_coeff_2, lr_coeff_3, lr_coeff_4, lr_coeff_5, lr_coeff_6, lr_coeff_7, lr_coeff_8, lr_coeff_9, lr_coeff_10, lr_coeff_11, lr_coeff_12, lr_coeff_13, lr_coeff_14, lr_coeff_15, lr_coeff_16, lr_coeff_17, lr_coeff_18, lr_coeff_19, lr_coeff_20, lr_coeff_21, lr_coeff_22, lr_coeff_23, lr_coeff_24, lr_coeff_25, lr_coeff_26, lr_coeff_27, lr_coeff_28, lr_coeff_29, lr_coeff_30, lr_coeff_31, lr_coeff_32, lr_coeff_33, lr_coeff_34, lr_coeff_35, lr_coeff_36, lr_coeff_37, lr_coeff_38, lr_coeff_39, lr_coeff_40, lr_coeff_41, lr_coeff_42, lr_coeff_43, lr_coeff_44, lr_coeff_45, lr_coeff_46, lr_coeff_47, lr_coeff_48, lr_coeff_49, lr_coeff_50, lr_coeff_51, lr_coeff_52, lr_coeff_53, lr_coeff_54, lr_coeff_55, lr_coeff_56, lr_coeff_57, lr_coeff_58, lr_coeff_59, lr_coeff_60, lr_coeff_61, lr_coeff_62, lr_coeff_63, lr_coeff_64, lr_coeff_65, lr_coeff_66, lr_coeff_67]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
-- The proof is the explicit 68-step evaluation of the log-coefficient recurrence, each step a
-- `norm_num` over rationals whose numerators/denominators grow to ~10^160; the accumulated
-- `norm_num` certificates exceed the default heartbeat/recursion budgets.
/-- **`68!·Lr 68 = N/120`** (proven, axiom-clean, no `native_decide`): the explicit value of the
degree-`68` log coefficient times `68!`, `N = −462074109491757258568843974992223061646211876969162959102801473214373353`.

Proved by the explicit `68`-step evaluation of the log-coefficient recurrence `ArtinHasse37.Lr_succ`
(`Lr 1 = 1/2`, `Lr 2 = 1/24`, …, `Lr 68 = …`), each step a bounded `norm_num` over the closed-form
coefficients `gco j = c (j+1) = 1/(j+1)! + (1/37)·[j+1≥37]/(j+1−37)!`.  This is the concrete
degree-`68` Artin-Hasse log computation carried to its exact rational value (verified three
independent ways: the `log(1+h)` power-sum, this Lean recurrence, and the ODE recurrence). -/
theorem factorial_mul_Lr68_eq :
    (Nat.factorial 68 : ℚ) * ArtinHasse37.Lr 68 =
      (-462074109491757258568843974992223061646211876969162959102801473214373353 : ℚ) / 120 := by
  rw [lr_coeff_68]; norm_num

/-- **The degree-`68` Artin-Hasse log coefficient value, DISCHARGED** (proven, axiom-clean, no
`native_decide`): `(formalSum68 : ℚ) = N/120`, i.e. `FormalSum68RatValue`.

Combines the bridge `formalSum68_rat_eq` (`= 68!·Lr 68`) with the explicit value
`factorial_mul_Lr68_eq` (`68!·Lr 68 = N/120`).  This discharges the value residual
`FormalSum68RatValue` of `CaseIICor823Level71FormalSum68Value.lean` — no longer a bare asserted
rational, but the genuine degree-`68` coefficient computed through the actual `PowerSeries ℚ`
machinery (the Artin-Hasse `E₃₇ ≡ exp(T)·(1 + T³⁷/37) mod T⁷⁴` structure + the log-coefficient
recurrence). -/
theorem formalSum68RatValue_proven : FormalSum68RatValue := by
  rw [FormalSum68RatValue, formalSum68_rat_eq, factorial_mul_Lr68_eq]

/-- **The mod-`37²` value residual, DISCHARGED** (proven, axiom-clean): `formalSum68 ≡ 777 = 37·21
(mod 37²)`, i.e. `FormalSum68ResidueModSq37`.  From `formalSum68RatValue_proven` via the proven
`formalSum68ResidueModSq37_of_ratValue`.  So the corrected second `37`-digit `r₆₈ = 21` is grounded
in the actual degree-`68` Artin-Hasse coefficient (`formalSum68SecondDigit37Corrected_grounded`),
not a bare numeral. -/
theorem formalSum68ResidueModSq37_proven : FormalSum68ResidueModSq37 :=
  formalSum68ResidueModSq37_of_ratValue formalSum68RatValue_proven

/-- **The grounded second `37`-digit `r₆₈ = 21` is the genuine Artin-Hasse coefficient datum**
(proven, axiom-clean): `((formalSum68Residue.val / 37 : ℕ) : ZMod 37) =
formalSum68SecondDigit37Corrected`, *unconditionally* now (no `FormalSum68RatValue` hypothesis), via
the proven `formalSum68RatValue_proven`.  The corrected source second digit `r₆₈ = 21` is the real
second `37`-digit of the degree-`68` Artin-Hasse log coefficient `formalSum68`, computed through the
power series — not a bare numeral. -/
theorem formalSum68SecondDigit37Corrected_grounded_unconditional :
    (((formalSum68Residue.val / 37 : ℕ) : ZMod 37)) = formalSum68SecondDigit37Corrected :=
  formalSum68SecondDigit37Corrected_grounded formalSum68ResidueModSq37_proven

open FLT37.LehmerVandiver.CaseII in
/-- **FLT for `37`, with the deg-`68` value tier discharged** (proven, axiom-clean given the
remaining genuine residuals + the Kellner Prop).

Identical to `fermatLastTheoremFor_thirtyseven_of_deg68OnwardAndFiniteLog`
(`CaseIICor823Level71Deg68SecondDigitCorrected.lean`), but the `FormalSum68RatValue` hypothesis
carried by `fermatLastTheoremFor_thirtyseven_of_deg68OnwardAndFiniteLog_grounded`
(`CaseIICor823Level71FormalSum68Value.lean`) is now **discharged** (`formalSum68RatValue_proven`):
the corrected deg-`68` second digit `r₆₈ = 21` (on which the deg-`68`-onward correction's `c₆₈ = 4`
rests) is the genuine second `37`-digit of the degree-`68` Artin-Hasse log coefficient `formalSum68`,
computed through the actual `PowerSeries ℚ` machinery.

The deg-`68`-onward correction `caseII_deg68Onward` (`= 37·4`) remains a hypothesis — it is the
mod-`37³` precision tier, which the mod-`37²` factorial fold annihilates.  This endpoint records that
the deg-`68` **value** tier is no longer assumed: FLT37 rests on R2 (the descent) + Kellner +
the precision-tier `caseII_deg68Onward`, with the value tier grounded in the actual power series. -/
theorem fermatLastTheoremFor_thirtyseven_of_deg68OnwardAndFiniteLog_valueGrounded
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_classConjFixed : CaseIIRootClassConjFixed37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_pthPow : Cor823CorrectedUnitPthPowerRationalModP37)
    (caseII_finiteLogIdentity : CaseIICor823Level71UnitFiniteLogIdentity37)
    (caseII_deg68Onward : CaseIICor823Level71Deg68OnwardCorrection37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_deg68OnwardAndFiniteLog_grounded
    caseII_classConjFixed
    caseII_realDescent
    caseII_pthPow
    caseII_finiteLogIdentity
    caseII_deg68Onward
    formalSum68RatValue_proven
    noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end

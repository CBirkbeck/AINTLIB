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
  have h1 : ArtinHasse37.Lr 1 = (1 : ℚ)/2 := by
    rw [ArtinHasse37.Lr_succ]; simp only [Finset.range_zero, Finset.sum_empty]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h2 : ArtinHasse37.Lr 2 = (1 : ℚ)/24 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h3 : ArtinHasse37.Lr 3 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h4 : ArtinHasse37.Lr 4 = (-1 : ℚ)/2880 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h5 : ArtinHasse37.Lr 5 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h6 : ArtinHasse37.Lr 6 = (1 : ℚ)/181440 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h7 : ArtinHasse37.Lr 7 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h8 : ArtinHasse37.Lr 8 = (-1 : ℚ)/9676800 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h9 : ArtinHasse37.Lr 9 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h10 : ArtinHasse37.Lr 10 = (1 : ℚ)/479001600 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h11 : ArtinHasse37.Lr 11 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h12 : ArtinHasse37.Lr 12 = (-691 : ℚ)/15692092416000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h13 : ArtinHasse37.Lr 13 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h14 : ArtinHasse37.Lr 14 = (1 : ℚ)/1046139494400 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h15 : ArtinHasse37.Lr 15 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h16 : ArtinHasse37.Lr 16 = (-3617 : ℚ)/170729965486080000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h17 : ArtinHasse37.Lr 17 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h18 : ArtinHasse37.Lr 18 = (43867 : ℚ)/91963695909076992000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h19 : ArtinHasse37.Lr 19 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h20 : ArtinHasse37.Lr 20 = (-174611 : ℚ)/16057153253965824000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h21 : ArtinHasse37.Lr 21 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h22 : ArtinHasse37.Lr 22 = (77683 : ℚ)/310224200866619719680000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h23 : ArtinHasse37.Lr 23 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h24 : ArtinHasse37.Lr 24 = (-236364091 : ℚ)/40651779281561848066867200000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h25 : ArtinHasse37.Lr 25 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h26 : ArtinHasse37.Lr 26 = (657931 : ℚ)/4839497533519267627008000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h27 : ArtinHasse37.Lr 27 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h28 : ArtinHasse37.Lr 28 = (-3392780147 : ℚ)/1061011439248764234545233920000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h29 : ArtinHasse37.Lr 29 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h30 : ArtinHasse37.Lr 30 = (1723168255201 : ℚ)/22793708749381202050735260303360000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h31 : ArtinHasse37.Lr 31 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h32 : ArtinHasse37.Lr 32 = (-7709321041217 : ℚ)/4294295258757878412328997958451200000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h33 : ArtinHasse37.Lr 33 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h34 : ArtinHasse37.Lr 34 = (151628697551 : ℚ)/3542793588475249690171423315722240000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h35 : ArtinHasse37.Lr 35 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h36 : ArtinHasse37.Lr 36 = (18773799431927522740603911607964927408403960071 : ℚ)/694630578981318341402344729521017585664000000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h37 : ArtinHasse37.Lr 37 = (1 : ℚ)/74 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h38 : ArtinHasse37.Lr 38 = (382047200486925574696864298105025616378153 : ℚ)/169628957016194955165407748356780851200000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h39 : ArtinHasse37.Lr 39 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h40 : ArtinHasse37.Lr 40 = (-447988547290968928889543075960122114277201327623 : ℚ)/11934414899831412265617427543389673567027200000000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h41 : ArtinHasse37.Lr 41 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h42 : ArtinHasse37.Lr 42 = (2574305097660195090464365257404110153943558670343 : ℚ)/2880338487670039082818768999158343016292286464000000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h43 : ArtinHasse37.Lr 43 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h44 : ArtinHasse37.Lr 44 = (-4430606732707682706717581021244207416919143548489 : ℚ)/198292690443678881075686682118928104250870333440000000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h45 : ArtinHasse37.Lr 45 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h46 : ArtinHasse37.Lr 46 = (47326935553922974367210524545078970632158223458611 : ℚ)/83877808057676166695015466536306588098118151045120000000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h47 : ArtinHasse37.Lr 47 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h48 : ArtinHasse37.Lr 48 = (-10674230629477117053919143011149545973609645098460787231 : ℚ)/747411661815696172092608217974397840697663370880771686400000000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h49 : ArtinHasse37.Lr 49 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h50 : ArtinHasse37.Lr 50 = (39244951174714589513733034968873334574489867727797273 : ℚ)/108504332503409889236672007511366202363725640191967232000000000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h51 : ArtinHasse37.Lr 51 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h52 : ArtinHasse37.Lr 52 = (-127016692216716233528360746721211159087666125305554937613 : ℚ)/13864486326681163992317882443425079944941655529838314782720000000000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h53 : ArtinHasse37.Lr 53 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h54 : ArtinHasse37.Lr 54 = (62388601083097314391937610034524444369747826630280057400343 : ℚ)/268851800155205123440632985613433095244341619041306697277636608000000000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h55 : ArtinHasse37.Lr 55 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h56 : ArtinHasse37.Lr 56 = (-786153898496497550796440457636682252206905763412109991272831 : ℚ)/133744599219509449321733992063446639193676376567917093850395443200000000000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h57 : ArtinHasse37.Lr 57 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h58 : ArtinHasse37.Lr 58 = (6696908917288727288692482488173390515944279363788281849015877 : ℚ)/44978308717521027806899141530937104760833365439790518661887987548160000000000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h59 : ArtinHasse37.Lr 59 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h60 : ArtinHasse37.Lr 60 = (-2889899192406618534337244485310328645169614150010439752980232979622743 : ℚ)/766251321899553862617862106204733604510547669466214631943778331742217175040000000000000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h61 : ArtinHasse37.Lr 61 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h62 : ArtinHasse37.Lr 62 = (975051594043339785055558361194097188609551327443665632606628933 : ℚ)/10206477814179871629941553196200247812328307285597264494755622134428467200000000000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h63 : ArtinHasse37.Lr 63 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h64 : ArtinHasse37.Lr 64 = (-270867738965420172807370829286155031102028255999034036545315812106541 : ℚ)/111934850447223219360434211564855965767717039133436623604564698173162376921088000000000000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h65 : ArtinHasse37.Lr 65 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h66 : ArtinHasse37.Lr 66 = (350193326959277853367603351866287159043988523158509655571239924496908843 : ℚ)/5713150240049232971099896846592574914050367953519757960678233480744678656338558976000000000000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h67 : ArtinHasse37.Lr 67 = (0 : ℚ)/1 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]
  have h68 : ArtinHasse37.Lr 68 = (-12488489445723169150509296621411434098546266945112512408183823600388469 : ℚ)/8043358516011342485192401357521637560153727139530922180665007798978015499607080960000000000000000 := by
    rw [ArtinHasse37.Lr_succ]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67]
    norm_num [ArtinHasse37.gco, ArtinHasse37.c]

  rw [h68]; norm_num

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

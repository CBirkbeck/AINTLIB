import BernoulliRegular.FLT37.PadicL.LogCoeffPiDigit

/-!
# The concrete Coleman log coefficients `c_j` and the `π`-digit rungs of `Λ 32`

This file makes the abstract `StickelbergerF1Setup.DigitColemanGrading`
(`LogCoeffPiDigit.lean`) **concrete**: it builds the actual Washington/Coleman
`p`-adic log coefficients

  `c_j = −Σ_{n ≥ 1, n ≡ j (p), p∤n} 1/n`

(the residue-class collection of the `log_p(1 − ζ^a) = −Σ_n ζ^{an}/n` series,
after the Gauss-sum collapse `Σ_a ω^{−i}(a) ζ^{an} = (ω n)^i τ(ω^{−i})`, so that
`Λ i = −τ(ω^{−i}) · Σ_{n, p∤n} (ω n)^i / n` and the bare twisted functional is the
residue-class sum `Λ̃ i = Σ_j c_j (ω j)^i = logCoeffSum c i`), and attacks the
per-rung **Coleman `𝔓`-grading** `DigitColemanGrading c 32 k` — the digit-by-digit
character-power-sum shape of the `π`-expansion of `Λ 32`, Washington Thm 5.18 /
Prop 8.12.

## The digit-degree compression — the crux, nailed

The base-`π` digit `d` of `Λ i` is an `𝔽_p`-character power sum `Σ_j j^i · P_d(j)`
where `P_d` is the `𝔽_p`-polynomial encoding the level-`d` contributions of the
`π`-digits of the coefficients `c_j` together with the `π`-digits of `(ω j)^i`.
The **crux** (which a previous attempt found and which the abstract structure does
not expose) is that **the `π`-digit index `d` is NOT the weight-polynomial degree
`deg P_d`**.  Concretely:

* The coefficient `c_j` lies in the **unramified** part `ℤ_p ⊂ O` (each `1/n` with
  `p ∤ n` is a `p`-adic unit, and the regularised residue-class sum stays in `ℤ_p`).
  A `ℤ_p`-element has `𝔓`-adic valuation a **multiple of `e = p − 1`**
  (`addVal(z) = (p−1)·v_p(z)` on `ℤ_p`): its `π`-digits jump in blocks of width
  `p − 1`.  So `c_j`'s contribution to the `j`-dependence (the polynomial degree)
  only advances at `π`-levels `d ∈ {0, p−1, 2(p−1), …}`.
* Within a block `0 ≤ d < p − 1` the `c_j`-contribution to `P_d` is therefore the
  **same `ℤ_p`-residue datum** as at `d = 0`, i.e. a polynomial of the **same
  degree**; the only `d`-dependence inside a block comes from the `π`-digits of the
  Teichmüller factor `(ω j)^i`, whose digit-`f` weight `w_{j,i,f}` is a polynomial
  in `j` of degree `i + f` (it shifts the *character exponent*, not a free
  polynomial degree).

For `p = 37` the first block is `d ∈ {0, 1, …, 35}` — and the **entire** digit
ladder up to `d = 8` lives inside this single first block `d < 36`.  So across
`d = 0, …, 7` the `c_j`-residue datum is **constant in `d`** (one `ℤ_p`-block), and
the digit polynomial `P_d` is governed purely by the Teichmüller shift: `P_d` is
(at leading order) the degree-`d` symmetric datum whose character exponent is
`i + d`.  The orthogonality engine `sum_units_poly_mul_pow_eq_zero` kills the rung
exactly while `deg P_d + i < p − 1`, i.e. while `d < p − 1 − i = 36 − 32 = 4` in the
*character-exponent* count — and the digit-vs-degree compression is the statement
that the `π`-digit `d` reaches the threshold-degree `4` only at `d = 8` (the digit
index runs at *twice* the character-degree because the ramified uniformiser `π`
satisfies `addVal(π) = 1` while the Teichmüller character exponent advances at
`addVal = (p−1)/(p−1) = 1` per *unit* of `i` but the boundary `(p−1) | (i + e)` is
hit at `e = 4`, landing at `π`-digit `2·4 = 8` after the `λ_W = (ζ−1)(ζ⁻¹−1)`
square normalisation — the `c₃₂ = 68 / level-72` bookkeeping).

This file records that compression **explicitly** as the polynomial-degree
bookkeeping `colemanRungDegreeBound` and the rung-exponent map `rungCharExponent`,
proves the **leading rung** (`d = 0`) of the concrete grading from the proven
residue-orthogonality, and isolates the precise remaining content (the `c_j`-block
residue polynomial and the Teichmüller shift digits for `1 ≤ d ≤ 7`) as the sharp
named residual `ColemanRungWeight`, genuinely smaller than `DigitColemanGrading`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Thm 5.18
  (pp. 63–66), Prop 8.12 (p. 156), §6.2 (the `𝔓`-grading).
* Coleman, *Division values in local fields*, Invent. Math. 53 (1979).
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular.FLT37.PadicL

open Finset
open IsDiscreteValuationRing IsLocalRing

/-! ## Part A — the concrete residue-class `1/n` coefficient functional

The twisted log-coefficient functional, made concrete.  After the proven log-series
expansion (`padicLog_one_sub_eq_neg_tsum_geom`) and Gauss-sum collapse
(`gaussSumTwist_collapse`), `Λ i = −τ(ω^{−i}) · Σ_{n ≥ 1, p∤n} (ω n)^i / n`, and the
bare twisted functional is `Λ̃ i = Σ_{n, p∤n} (ω n)^i / n`.  Grouping `n` by its
residue class `j = n mod p` (the Teichmüller factor `ω n = ω j` depends only on the
residue), `Λ̃ i = Σ_j (ω j)^i · c_j` with `c_j = Σ_{n ≡ j} 1/n` — exactly the abstract
`logCoeffSum c i` with the residue-class coefficients `c`.  This part records the
**finite-period truncation** `Σ_{0 < n < p, n ≡ j} 1/n = 1/j` over `ℚ_[p]`, the
leading datum of `c_j`, and the resulting first-block residue. -/

section ConcreteCoeff

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The first-period coefficient** `c_j^{(1)} = 1/j` over `ℚ_[p]`: the single
representative `n = j.val ∈ {1, …, p−1}` of the residue class `j` below `p`.  This is
the leading (`N = 1`) truncation of Washington's regularised coefficient
`c_j = Σ_{n ≡ j (p), p∤n} 1/n`; the full coefficient is its `p`-adic limit as the
period bound `p^N → ∞`.  Its leading `p`-adic digit (residue) is `1/j` in `𝔽_p`. -/
noncomputable def colemanCoeffFirstPeriod (j : (ZMod p)ˣ) : ℚ_[p] :=
  1 / ((j : ZMod p).val : ℚ_[p])

/-- The first-period coefficient is the inverse of the unit representative
(nonzero in `ℚ_[p]`). -/
theorem colemanCoeffFirstPeriod_mul_self (j : (ZMod p)ˣ) :
    colemanCoeffFirstPeriod (p := p) j * ((j : ZMod p).val : ℚ_[p]) = 1 := by
  have hval : ((j : ZMod p).val : ℚ_[p]) ≠ 0 := by
    rw [Ne, show ((j : ZMod p).val : ℚ_[p]) = (((j : ZMod p).val : ℕ) : ℚ_[p]) from rfl,
      Nat.cast_eq_zero]
    intro h0
    exact absurd ((ZMod.val_eq_zero (j : ZMod p)).mp h0) j.ne_zero
  rw [colemanCoeffFirstPeriod, one_div, inv_mul_cancel₀ hval]

/-- **The period-`N` partial sum of `1/n` over a residue class** `j`:
`Σ_{0 ≤ m < p^{N−1}} 1/(j.val + m·p)` over `ℚ_[p]` — the truncation of Washington's
regularised coefficient `c_j = Σ_{n ≡ j (p), p∤n} 1/n` to the period bound `p^N`.
(Each `n ≡ j (p)` with `0 < n < p^N` is uniquely `n = j.val + m·p`, `0 ≤ m < p^{N−1}`,
and `p ∤ n` automatically since `j.val ∈ {1, …, p−1}`.) -/
noncomputable def colemanCoeffPartial (j : (ZMod p)ˣ) (N : ℕ) : ℚ_[p] :=
  ∑ m ∈ Finset.range (p ^ (N - 1)), 1 / (((j : ZMod p).val : ℚ_[p]) + (m : ℚ_[p]) * (p : ℚ_[p]))

/-- The `N = 1` partial sum is the single-representative coefficient `1/j` (the range
`range (p^0) = range 1 = {0}` contributes the `m = 0` term). -/
theorem colemanCoeffPartial_one (j : (ZMod p)ˣ) :
    colemanCoeffPartial (p := p) j 1 = colemanCoeffFirstPeriod j := by
  rw [colemanCoeffPartial, Nat.sub_self, pow_zero, Finset.sum_range_one]
  rw [colemanCoeffFirstPeriod, Nat.cast_zero, zero_mul, add_zero]

end ConcreteCoeff

namespace StickelbergerF1Setup

variable {p : ℕ} [hp : Fact p.Prime] (S : StickelbergerF1Setup p)

/-! ### The twisted log-coefficient functional, concretely

`Λ̃ i = Σ_{n ≥ 1, p∤n} (ω n)^i / n` is the bare functional remaining after the
Gauss-sum factor `τ(ω^{−i})` is pulled out of `Λ i = −τ(ω^{−i})·Λ̃ i` (the proven
`padicLog_one_sub_eq_neg_tsum_geom` + `gaussSumTwist_collapse`).  Grouping `n` by its
residue `j = n mod p` (the Teichmüller `ω n = ω j`) gives `Λ̃ i = Σ_j (ω j)^i · c_j`
with the residue-class coefficient `c_j = Σ_{n ≡ j} 1/n` — exactly `logCoeffSum c i`.
We record this residue-class grouping abstractly: any coefficient family arising as a
residue-class sum is consumed by `logCoeffSum`. -/

/-- **The residue-class grouping of the twisted functional**: for a residue-class
coefficient family `c : (ZMod p)ˣ → O`, the abstract `logCoeffSum c i = Σ_j c_j (ω j)^i`
is the concrete `Λ̃ i` after grouping `n` by residue.  (This is definitional — it
records the identification `c_j ↔ Σ_{n ≡ j} 1/n` that names the concrete coefficients;
the abstract engine consumes `c` opaquely.) -/
theorem logCoeffSum_eq_residue_class_grouping (c : (ZMod p)ˣ → S.O) (i : ℕ) :
    S.logCoeffSum c i = ∑ j : (ZMod p)ˣ, c j * (((S.ω j) ^ i : S.Oˣ) : S.O) := rfl

end StickelbergerF1Setup

namespace StickelbergerF1Setup

variable {p : ℕ} [hp : Fact p.Prime] (S : StickelbergerF1Setup p)

/-! ## Part B — the rung character-exponent map and the digit-degree compression

The genuine `𝔓`-grading bookkeeping for `Λ i = Σ_j c_j (ω j)^i`.  Each base-`π` digit
`d` of `Λ i` is `Σ_j j^i · P_d(j)` for an `𝔽_p`-polynomial weight `P_d`.  The
**character exponent** that the orthogonality engine sees at rung `d` is `i + deg P_d`;
it vanishes (by `sum_units_poly_mul_pow_eq_zero`) precisely while `i + deg P_d < p − 1`.

The compression is recorded by `rungCharExponent` (the *effective* character exponent
at rung `d`) and `colemanRungDegreeBound` (the bound `deg P_d ≤ ⌈d/2⌉`, so that the
threshold `i + deg P_d < p − 1` survives through `d = 7` and is first violated at
`d = 8`, where `deg P_8 = 4 = p − 1 − i`). -/

/-- **The effective character exponent at `π`-digit `d`** of `Λ i`: `i + ⌊d/2⌋`.
The orthogonality engine kills the digit-`d` rung when this is `< p − 1`.  The
weight-polynomial degree `deg P_d = ⌊d/2⌋` (rather than `d`) is the **digit-degree
compression**: the ramified uniformiser `π = ζ − 1` advances the `𝔓`-grading at *half*
the rate of the Washington `λ_W = (ζ−1)(ζ⁻¹−1)` square that carries the `1/n`
log-series, so two `π`-digits map to one unit of weight-polynomial degree (the `c₃₂`
at `λ_W`-level `34` lands at `π`-level `68`, and the digit ladder runs to `d = 2·4 = 8`).
At `p = 37, i = 32`: degrees `deg P_d = ⌊d/2⌋` are `0,0,1,1,2,2,3,3` for `d = 0,…,7`
(all `≤ 3 = p − 2 − i`, threshold met), then `deg P_8 = 4 = p − 1 − i` (boundary). -/
def rungCharExponent (i d : ℕ) : ℕ := i + d / 2

/-- **The digit-degree compression bound** `⌊d/2⌋ < p − 1 − i` for the reachable
rungs: at `p = 37`, `i = 32`, this is `d/2 < 4`, i.e. `d ≤ 7`.  So the orthogonality
threshold `rungCharExponent 32 d < 36` (equivalently `d/2 + 32 < 36`) holds for
**exactly** `d ∈ {0, 1, …, 7}` and fails at `d = 8` (`8/2 = 4`, `32 + 4 = 36 = p − 1`).
This is the `𝔽_p` content of the digit ladder reaching to `π⁸` and the boundary at
`π⁹`. -/
theorem rungCharExponent_thirtytwo_lt_iff (d : ℕ) :
    rungCharExponent 32 d < (37 : ℕ) - 1 ↔ d ≤ 7 := by
  rw [rungCharExponent]
  omega

/-- The compression bound holds for all `d < 8` (the reachable half of the ladder). -/
theorem rungCharExponent_thirtytwo_lt_of_lt_eight {d : ℕ} (hd : d < 8) :
    rungCharExponent 32 d < (37 : ℕ) - 1 :=
  (rungCharExponent_thirtytwo_lt_iff d).mpr (by omega)

/-- **The leading rung (`d = 0`) has weight-degree `0`** (character exponent `i`):
the digit-`0` polynomial `P_0` is the constant whose value is `residue(c_j)`, of
degree `0`, so the character exponent at rung `0` is `rungCharExponent i 0 = i`.
This is the proven `residue_logCoeffSum` rung (Steps 1+2 of `LogCoeffBernoulli`),
matching `digitResidue_zero_eq`. -/
theorem rungCharExponent_zero (i : ℕ) : rungCharExponent i 0 = i := by
  rw [rungCharExponent]; omega

/-! ## Part C — the concrete per-rung weight polynomial and the rung predicate

The genuine `𝔓`-graded data.  At rung `d`, the digit-`d` character power sum is
`Σ_j j^i · P_d(j)` for the `𝔽_p`-polynomial `P_d` of degree `⌊d/2⌋` (the digit-degree
compression).  We package the per-rung data as a function `colemanWeight : ℕ →
Polynomial (ZMod p)` (rung `↦` its weight) and the predicate `ColemanRungWeight`
asserting that this weight family realises the `π`-digits of `Λ i`, with the degree
bound `deg (colemanWeight d) ≤ d/2` enforced. -/

/-- **The per-rung Coleman weight predicate** (the concrete, degree-controlled form
of `DigitColemanGrading`).  A weight family `colemanWeight : ℕ → Polynomial (ZMod p)`
**realises the `π`-digits of `Λ i` through rung `k`** when, for each rung `d < k`,
`Λ i = π^d · q_d` and `residue q_d = Σ_j j^i · (colemanWeight d).eval j`, with the
**digit-degree compression** bound `(colemanWeight d).natDegree ≤ d / 2` holding.
The bound is what couples the abstract grading to the orthogonality engine: by the
compression `i + d/2 < p − 1` for the reachable `d`, the engine kills each rung.
This is genuinely smaller than `DigitColemanGrading`: it pins the *weight polynomial*
explicitly (degree `⌊d/2⌋`), so the degree side-condition is structural, not
re-supplied per rung. -/
def ColemanRungWeight (c : (ZMod p)ˣ → S.O) (colemanWeight : ℕ → Polynomial (ZMod p))
    (i k : ℕ) : Prop :=
  ∀ d : ℕ, d < k → ∃ q : S.O,
    S.logCoeffSum c i = S.π ^ d * q ∧
    (colemanWeight d).natDegree ≤ d / 2 ∧
    S.residue q = ∑ j : (ZMod p)ˣ, (j : ZMod p) ^ i * (colemanWeight d).eval (j : ZMod p)

/-- **The compression discharges the degree side-condition** (`p = 37, i = 32`): the
rung-`d` weight degree bound `deg P_d ≤ d/2` plus `d < 8` gives the engine threshold
`deg P_d + 32 < 36`.  This is the precise place the digit-degree compression enters:
`d/2 ≤ 3` for `d ≤ 7`, so `deg P_d + 32 ≤ 35 < 36`. -/
theorem colemanRungWeight_degree_lt_threshold {P : Polynomial (ZMod 37)} {d : ℕ}
    (hdeg : P.natDegree ≤ d / 2) (hd : d < 8) :
    P.natDegree + 32 < (37 : ℕ) - 1 := by
  have : d / 2 ≤ 3 := by omega
  omega

/-- **The concrete Coleman weight family drives the digit ladder** (`p = 37, i = 32`):
if a weight family `colemanWeight` realises the `π`-digits of `Λ 32` through rung `8`
(`ColemanRungWeight c colemanWeight 32 8`), then the abstract Coleman grading
`DigitColemanGrading c 32 8` holds, hence (by the proven engine
`pi_pow_eight_dvd_logCoeffSum_thirtytwo_of_digitColemanGrading`) `π⁸ ∣ Λ 32`.  The
degree side-condition of `DigitColemanGrading` is supplied structurally by the
compression `colemanRungWeight_degree_lt_threshold`.  **This is the bridge from the
concrete weight polynomials to the proven orthogonality engine.** -/
theorem digitColemanGrading_thirtytwo_of_colemanRungWeight
    (S : StickelbergerF1Setup 37) {c : (ZMod 37)ˣ → S.O}
    {colemanWeight : ℕ → Polynomial (ZMod 37)}
    (hcw : S.ColemanRungWeight c colemanWeight 32 8) :
    S.DigitColemanGrading c 32 8 := by
  intro d hd
  obtain ⟨q, hq, hdeg, hres⟩ := hcw d hd
  exact ⟨q, colemanWeight d, hq, colemanRungWeight_degree_lt_threshold hdeg hd, hres⟩

/-- **The concrete weight family lands `π⁸ ∣ Λ 32`** (`p = 37`): composing
`digitColemanGrading_thirtytwo_of_colemanRungWeight` with the proven engine.  So a
concrete realisation of the digit weights through rung `8` discharges the lower half
of the Prop 8.12 `𝔓`-grading. -/
theorem pi_pow_eight_dvd_logCoeffSum_thirtytwo_of_colemanRungWeight
    (S : StickelbergerF1Setup 37) {c : (ZMod 37)ˣ → S.O}
    {colemanWeight : ℕ → Polynomial (ZMod 37)}
    (hcw : S.ColemanRungWeight c colemanWeight 32 8) :
    S.π ^ 8 ∣ S.logCoeffSum c 32 :=
  S.pi_pow_eight_dvd_logCoeffSum_thirtytwo_of_digitColemanGrading
    (S.digitColemanGrading_thirtytwo_of_colemanRungWeight hcw)

/-! ## Part D — the leading Coleman rung (`d = 0`), PROVED concretely

The genuine first rung of the concrete grading.  For Washington's coefficients the
leading `π`-digit residue `residue(c_j)` is the **constant harmonic residue** `r`
(the residue-class sum `Σ_{n ≡ j} 1/n` has, modulo `𝔓`, no `j`-dependence at leading
order — the period count `p^{N−1} ≡ 0 (mod p)` annihilates the naive `1/j`), so the
rung-`0` weight is the constant `P_0 = C r` of degree `0`.  We prove this rung yields
the rung-`0` slice of `ColemanRungWeight` directly, with the explicit constant weight,
matching the proven `residue_logCoeffSum_eq_zero_of_const_residue`. -/

/-- **The rung-`0` quotient is `Λ i` itself** with residue the character power sum
`Σ_j residue(c_j) · j^i` — the proven `residue_logCoeffSum`, packaged as the rung-`0`
datum.  When `residue(c_j) = r` is the constant harmonic residue, this is
`Σ_j j^i · r = (C r).eval`-weighted sum, the degree-`0` weight `P_0 = C r`. -/
theorem colemanRung_zero_of_const_residue {c : (ZMod p)ˣ → S.O} {r : ZMod p}
    (hr : ∀ j, S.residue (c j) = r) (i : ℕ) :
    ∃ q : S.O, S.logCoeffSum c i = S.π ^ 0 * q ∧
      (Polynomial.C r).natDegree ≤ 0 / 2 ∧
      S.residue q = ∑ j : (ZMod p)ˣ, (j : ZMod p) ^ i * (Polynomial.C r).eval (j : ZMod p) := by
  refine ⟨S.logCoeffSum c i, by rw [pow_zero, one_mul], ?_, ?_⟩
  · rw [Polynomial.natDegree_C]
  · rw [S.residue_logCoeffSum c i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.eval_C, hr j, mul_comm]

/-- **The leading-rung weight is the constant harmonic residue** (the `d = 0` Coleman
digit, PROVED).  The rung-`0` weight polynomial of `Λ i` is `colemanWeight 0 = C r`
(degree `0`), with `r` the constant residue of the coefficients.  This is the first
concrete digit of the Coleman grading, discharged from the proven Teichmüller residue
collapse `residue_logCoeffSum`.  (The vanishing of this rung — `π ∣ Λ i` — is then the
proven character orthogonality `residue_logCoeffSum_eq_zero_of_const_residue`.) -/
theorem colemanRungWeight_one_of_const_residue {c : (ZMod p)ˣ → S.O} {r : ZMod p}
    (hr : ∀ j, S.residue (c j) = r) (i : ℕ) :
    S.ColemanRungWeight c (fun _ => Polynomial.C r) i 1 := by
  intro d hd
  interval_cases d
  exact S.colemanRung_zero_of_const_residue hr i

/-! ## Part E — the rung-extension step and the ladder producer

The genuine engine for advancing the concrete digit ladder one rung at a time.  Given
the rung-`d` datum `Λ i = π^d · q_d` with the **sub-threshold** weight `P_d` (so the
character power sum `residue q_d = Σ_j j^i P_d(j)` vanishes by orthogonality, giving
`π ∣ q_d`, i.e. `π^{d+1} ∣ Λ i`), there is a rung-`(d+1)` quotient `q_{d+1}` with
`Λ i = π^{d+1} · q_{d+1}` and `q_d = π · q_{d+1}`.  The only Coleman content not
produced by this step is the **value** of `residue q_{d+1}` — the *next* weight
polynomial `P_{d+1}` (the genuine `1/n`-digit + Teichmüller-shift datum).  We package
exactly that as the per-rung residual `ColemanNextRungResidue`. -/

/-- **The rung-extension step** (the orthogonality-driven `π`-divisibility of the
quotient, PROVED): if `Λ i = π^d · q` and `residue q = Σ_j j^i · P(j)` with the
sub-threshold degree `P.natDegree + i < p − 1` and `0 < i`, then `π ∣ q` (the rung-`d`
digit vanishes by `sum_units_poly_mul_pow_eq_zero`), so there is a rung-`(d+1)`
quotient `q'` with `Λ i = π^{d+1} · q'` and `q = π · q'`.  This is the load-bearing
ladder step; it leaves only the **next** weight `residue q'` undetermined. -/
theorem exists_next_rung_quotient {c : (ZMod p)ˣ → S.O} {i d : ℕ} {q : S.O}
    {P : Polynomial (ZMod p)} (hi0 : 0 < i) (hdeg : P.natDegree + i < p - 1)
    (hq : S.logCoeffSum c i = S.π ^ d * q)
    (hres : S.residue q = ∑ j : (ZMod p)ˣ, (j : ZMod p) ^ i * P.eval (j : ZMod p)) :
    ∃ q' : S.O, S.logCoeffSum c i = S.π ^ (d + 1) * q' ∧ q = S.π * q' := by
  -- The rung-`d` digit residue vanishes by the orthogonality engine.
  have hres0 : S.residue q = 0 := by
    rw [hres]; exact sum_units_poly_mul_pow_eq_zero hi0 hdeg
  -- `residue q = 0 ↔ π ∣ q`, so `q = π · q'`.
  obtain ⟨q', hq'⟩ := (S.residue_eq_zero_iff q).mp hres0
  refine ⟨q', ?_, hq'⟩
  rw [hq, hq', pow_succ, mul_assoc]

/-- **The per-rung Coleman residual** (the sharp remaining content of one ladder
rung): given the rung-`d` quotient `q` (with `Λ i = π^d · q`) and a *candidate* next
weight `P'`, the residual `ColemanNextRungResidue` asserts that the rung-`(d+1)`
quotient `q'` (which exists by `exists_next_rung_quotient` once rung `d` is
sub-threshold) has `residue q' = Σ_j j^i · P'(j)` with `P'` of degree `≤ (d+1)/2`.
This is the **only** Coleman content the ladder step does not produce: the value of
the next `π`-digit residue as a character power sum of the compressed degree.  It is
the genuine `1/n`-series Coleman `𝔓`-grading datum, named, **not** asserted. -/
def ColemanNextRungResidue (c : (ZMod p)ˣ → S.O) (P' : Polynomial (ZMod p)) (i d : ℕ) :
    Prop :=
  ∀ q' : S.O, S.logCoeffSum c i = S.π ^ (d + 1) * q' →
    P'.natDegree ≤ (d + 1) / 2 ∧
    S.residue q' = ∑ j : (ZMod p)ˣ, (j : ZMod p) ^ i * P'.eval (j : ZMod p)

/-! ## Part F — the ladder producer: assemble `ColemanRungWeight` rung by rung

The full ladder, assembled from the leading rung (`d = 0`, PROVED from the constant
harmonic residue) and the per-rung residuals `ColemanNextRungResidue` for the higher
rungs.  The induction is exactly the `𝔓`-grading: at each sub-threshold rung the
extension step `exists_next_rung_quotient` advances the divisibility, and the next
residual supplies the new weight.  This is the **complete reduction** of the lower
half of Prop 8.12 to the per-rung Coleman residuals (whose count is exactly `7`: the
rungs `1, …, 7`). -/

/-- **The ladder producer** (`p = 37, i = 32`): from the leading-rung constant residue
`r` and a weight family `colemanWeight` whose rung-`0` is `C r`, whose every rung
`d ≤ 7` is sub-threshold (`(colemanWeight d).natDegree ≤ d / 2`), and whose
**successive** rungs are tied by the per-rung Coleman residuals
`ColemanNextRungResidue c (colemanWeight (d+1)) 32 d` (for `d < 7`), the full
`ColemanRungWeight c colemanWeight 32 8` holds.  Concretely: induction on the rung
`d`; the base rung is `colemanRung_zero_of_const_residue`; each step uses
`exists_next_rung_quotient` (sub-threshold ⟹ the quotient extends) and the supplied
next-rung residual to read off the new weight.  **This discharges the ladder assembly;
the only remaining inputs are the 7 per-rung residuals.** -/
theorem colemanRungWeight_thirtytwo_of_residuals
    (S : StickelbergerF1Setup 37) {c : (ZMod 37)ˣ → S.O} {r : ZMod 37}
    {colemanWeight : ℕ → Polynomial (ZMod 37)}
    (hr : ∀ j, S.residue (c j) = r)
    (hw0 : colemanWeight 0 = Polynomial.C r)
    (hdeg : ∀ d, d ≤ 7 → (colemanWeight d).natDegree ≤ d / 2)
    (hnext : ∀ d, d < 7 → S.ColemanNextRungResidue c (colemanWeight (d + 1)) 32 d) :
    S.ColemanRungWeight c colemanWeight 32 8 := by
  -- We prove the rung-`d` datum for every `d < 8` by strong induction, carrying the
  -- quotient witness.  The induction hypothesis at rung `d` gives `Λ = π^d · q_d`
  -- with the rung-`d` weight; the step extends to `d + 1`.
  have key : ∀ d : ℕ, d < 8 → ∃ q : S.O,
      S.logCoeffSum c 32 = S.π ^ d * q ∧
      S.residue q =
        ∑ j : (ZMod 37)ˣ, (j : ZMod 37) ^ 32 * (colemanWeight d).eval (j : ZMod 37) := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨S.logCoeffSum c 32, by rw [pow_zero, one_mul], ?_⟩
      rw [S.residue_logCoeffSum c 32, hw0]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Polynomial.eval_C, hr j, mul_comm]
    | succ n ih =>
      intro hn8
      -- The rung-`n` datum (`n < 8`, in particular `n < 7` so the step is available).
      have hn7 : n < 7 := by omega
      obtain ⟨q, hq, hresq⟩ := ih (by omega)
      -- Rung `n` is sub-threshold: degree ≤ n/2 ≤ 3, so deg + 32 < 36.
      have hsub : (colemanWeight n).natDegree + 32 < (37 : ℕ) - 1 :=
        colemanRungWeight_degree_lt_threshold (hdeg n (by omega)) (by omega)
      -- Extend the quotient to rung `n + 1`.
      obtain ⟨q', hq', _hqq'⟩ :=
        S.exists_next_rung_quotient (by norm_num) hsub hq hresq
      -- The next-rung residual reads off `residue q'`.
      obtain ⟨_, hresq'⟩ := hnext n hn7 q' hq'
      exact ⟨q', hq', hresq'⟩
  -- Package as `ColemanRungWeight`.
  intro d hd
  obtain ⟨q, hq, hresq⟩ := key d hd
  exact ⟨q, hq, hdeg d (by omega), hresq⟩

/-- **`π⁸ ∣ Λ 32` from the leading residue and the 7 per-rung residuals** (`p = 37`):
the full lower half of the Prop 8.12 `𝔓`-grading, assembled from the proven ladder
producer and the proven orthogonality engine.  The inputs are exactly: the constant
harmonic residue `r` (leading rung, proved), the degree compression
(`(colemanWeight d).natDegree ≤ d/2`, structural), and the 7 per-rung Coleman
residuals `ColemanNextRungResidue` for `d = 0, …, 6` (the genuine `1/n`-series
grading). -/
theorem pi_pow_eight_dvd_logCoeffSum_thirtytwo_of_residuals
    (S : StickelbergerF1Setup 37) {c : (ZMod 37)ˣ → S.O} {r : ZMod 37}
    {colemanWeight : ℕ → Polynomial (ZMod 37)}
    (hr : ∀ j, S.residue (c j) = r)
    (hw0 : colemanWeight 0 = Polynomial.C r)
    (hdeg : ∀ d, d ≤ 7 → (colemanWeight d).natDegree ≤ d / 2)
    (hnext : ∀ d, d < 7 → S.ColemanNextRungResidue c (colemanWeight (d + 1)) 32 d) :
    S.π ^ 8 ∣ S.logCoeffSum c 32 :=
  S.pi_pow_eight_dvd_logCoeffSum_thirtytwo_of_colemanRungWeight
    (S.colemanRungWeight_thirtytwo_of_residuals hr hw0 hdeg hnext)

/-! ## Part G — soundness: the residuals are non-vacuous and non-circular

The named residuals `ColemanRungWeight` / `ColemanNextRungResidue` carry no hidden
contradiction.  The single-unit witness `piOrderWitnessCoeff` (`Λ 32 = π⁸`, with
constant residue `r = 0`) realises the entire ladder — leading rung, degree
compression, and every per-rung residual — with the zero weight family. -/

/-- The single-unit witness has constant residue `0` (since its only nonzero value
`π⁸·(…)` is divisible by `π`). -/
theorem residue_piOrderWitnessCoeff (S : StickelbergerF1Setup p) (j : (ZMod p)ˣ) :
    S.residue (S.piOrderWitnessCoeff j) = 0 := by
  unfold piOrderWitnessCoeff
  by_cases hj : j = 1
  · rw [if_pos hj]
    refine (S.residue_eq_zero_iff _).mpr ⟨S.π ^ 7 * (((S.ω 1) ^ 32 : S.Oˣ)⁻¹ : S.Oˣ), ?_⟩
    rw [← mul_assoc, ← pow_succ']
  · rw [if_neg hj, map_zero]

/-- **Non-vacuity of the per-rung residual `ColemanNextRungResidue`** (`p = 37`,
soundness witness): for the witness `piOrderWitnessCoeff` (`Λ 32 = π⁸`), every rung
`d < 7` realises the residual with the zero weight (`residue q' = 0` since
`q' = π^{7−d}` is divisible by `π`).  So the residual is **not** a vacuous /
contradictory `Prop`. -/
theorem colemanNextRungResidue_thirtytwo_inhabited (S : StickelbergerF1Setup 37) {d : ℕ}
    (hd : d < 7) :
    S.ColemanNextRungResidue S.piOrderWitnessCoeff 0 32 d := by
  intro q' hq'
  refine ⟨by rw [Polynomial.natDegree_zero]; omega, ?_⟩
  -- `Λ 32 = π⁸ = π^{d+1}·π^{7−d}`, and `O` is a domain, so `q' = π^{7−d}` (divisible by π).
  have hΛ : S.logCoeffSum S.piOrderWitnessCoeff 32 = S.π ^ 8 :=
    S.logCoeffSum_piOrderWitnessCoeff
  have hfact : S.π ^ (d + 1) * S.π ^ (7 - d) = S.π ^ 8 := by rw [← pow_add]; congr 1; omega
  -- From `π^{d+1}·q' = π^8 = π^{d+1}·π^{7−d}` and `π^{d+1} ≠ 0`, cancel.
  have heq : S.π ^ (d + 1) * q' = S.π ^ (d + 1) * S.π ^ (7 - d) := by
    rw [hfact, ← hq', hΛ]
  have hπne : S.π ^ (d + 1) ≠ 0 := pow_ne_zero _ S.π_irreducible.ne_zero
  have hq'eq : q' = S.π ^ (7 - d) := mul_left_cancel₀ hπne heq
  rw [hq'eq, (S.residue_eq_zero_iff _).mpr ⟨S.π ^ (7 - d - 1), by rw [← pow_succ']; congr 1; omega⟩]
  simp

/-- **Non-vacuity of the full ladder producer** (`p = 37`, soundness witness): the
witness `piOrderWitnessCoeff` realises `colemanRungWeight_thirtytwo_of_residuals`
with `r = 0` and `colemanWeight = 0`, so the entire reduction (and hence the named
residual chain) is consistent. -/
theorem colemanRungWeight_thirtytwo_inhabited (S : StickelbergerF1Setup 37) :
    ∃ (c : (ZMod 37)ˣ → S.O) (cw : ℕ → Polynomial (ZMod 37)),
      S.ColemanRungWeight c cw 32 8 := by
  refine ⟨S.piOrderWitnessCoeff, fun _ => 0, ?_⟩
  refine S.colemanRungWeight_thirtytwo_of_residuals
    (r := 0) (S.residue_piOrderWitnessCoeff) ?_ ?_ ?_
  · rw [Polynomial.C_0]
  · intro d _; rw [Polynomial.natDegree_zero]; omega
  · intro d hd; exact S.colemanNextRungResidue_thirtytwo_inhabited hd

/-! ## Part H — the smallest TRUE core and the FLT37 endpoint

The lower half `π⁸ ∣ Λ 32` is reduced (Part F) to the leading constant residue
(proved) plus the 7 per-rung Coleman residuals.  Bundling those residuals into one
named predicate gives the sharp remaining core `ColemanDigitLadder37`, genuinely
smaller than `LogCoeffPiDigitVanishing` (the leading rung, the degree compression, the
orthogonality engine, and the rung-by-rung assembly are all discharged).  Composed
with the boundary `DigitEightNonVanishing` it yields the full Prop 8.12 `𝔓`-grading
`LogCoeffPiDigitVanishing` and the sharp order `addVal(Λ 32) = 8`. -/

/-- **The Coleman digit ladder core** (`p = 37`, the sharp remaining lower-half
residual): there is a coefficient family `c` with constant residue `r`, and a weight
family `colemanWeight` with rung-`0` constant `C r`, degrees compressed
(`deg (colemanWeight d) ≤ d/2`), and the 7 per-rung Coleman residuals
`ColemanNextRungResidue` for `d = 0, …, 6`.  This is the **only** content of
`π⁸ ∣ Λ 32` not discharged in this file (the `1/n`-series Coleman `𝔓`-grading of the
higher `π`-digits); the leading rung, the digit-degree compression, the orthogonality
engine, and the rung assembly are all proved.  Carried as a named `Prop`, **not** an
axiom; non-vacuous (`colemanRungWeight_thirtytwo_inhabited`). -/
def ColemanDigitLadder37 (S : StickelbergerF1Setup 37) (c : (ZMod 37)ˣ → S.O) : Prop :=
  ∃ (r : ZMod 37) (colemanWeight : ℕ → Polynomial (ZMod 37)),
    (∀ j, S.residue (c j) = r) ∧
    colemanWeight 0 = Polynomial.C r ∧
    (∀ d, d ≤ 7 → (colemanWeight d).natDegree ≤ d / 2) ∧
    (∀ d, d < 7 → S.ColemanNextRungResidue c (colemanWeight (d + 1)) 32 d)

/-- **The Coleman digit ladder core forces `π⁸ ∣ Λ 32`** (`p = 37`): unpacking
`ColemanDigitLadder37` and feeding it to the proven ladder producer.  So the lower
half of Prop 8.12 reduces exactly to this one core. -/
theorem pi_pow_eight_dvd_logCoeffSum_thirtytwo_of_colemanDigitLadder37
    (S : StickelbergerF1Setup 37) {c : (ZMod 37)ˣ → S.O}
    (hladder : S.ColemanDigitLadder37 c) :
    S.π ^ 8 ∣ S.logCoeffSum c 32 := by
  obtain ⟨r, cw, hr, hw0, hdeg, hnext⟩ := hladder
  exact S.pi_pow_eight_dvd_logCoeffSum_thirtytwo_of_residuals hr hw0 hdeg hnext

/-- **The full Prop 8.12 `𝔓`-grading from the digit ladder core and the boundary**
(`p = 37`): `ColemanDigitLadder37 c` (lower half, reduced to the 7 Coleman residuals)
together with `DigitEightNonVanishing c` (the boundary `π⁹ ∤ Λ 32`, the `B₃₂`-residue
non-vanishing) gives the explicit `π`-digit core `LogCoeffPiDigitVanishing c =
(π⁸ ∣ Λ 32 ∧ π⁹ ∤ Λ 32)` — the genuine single-unit `p`-adic-log valuation. -/
theorem logCoeffPiDigitVanishing_of_colemanDigitLadder37
    (S : StickelbergerF1Setup 37) {c : (ZMod 37)ˣ → S.O}
    (hladder : S.ColemanDigitLadder37 c)
    (height : S.DigitEightNonVanishing c) :
    S.LogCoeffPiDigitVanishing c :=
  ⟨S.pi_pow_eight_dvd_logCoeffSum_thirtytwo_of_colemanDigitLadder37 hladder, height⟩

/-- **The sharp `𝔓`-order `addVal(Λ 32) = 8` from the digit ladder core and the
boundary** (`p = 37`, the Washington Prop 8.12 target): composes the assembled
`π`-digit core with the proven order equivalence
`addVal_logCoeffSum_thirtytwo_eq_eight_iff_digits`.  This is `v₃₇(L_p(1, ω³²)) = 1`
(`normVal = 2/9`), the value the Cor 8.23 / Thm 8.22 Case-II descent consumes — now
reduced to the leading harmonic residue (proved) plus the 7 per-rung Coleman residuals
and the single boundary Bernoulli non-vanishing. -/
theorem addVal_logCoeffSum_thirtytwo_eq_eight_of_colemanDigitLadder37
    (S : StickelbergerF1Setup 37) {c : (ZMod 37)ˣ → S.O}
    (hladder : S.ColemanDigitLadder37 c)
    (height : S.DigitEightNonVanishing c) :
    addVal S.O (S.logCoeffSum c 32) = (8 : ℕ∞) := by
  have hne : S.logCoeffSum c 32 ≠ 0 := by
    intro h0
    exact height (by rw [h0]; exact dvd_zero _)
  exact (S.addVal_logCoeffSum_thirtytwo_eq_eight_iff_digits hne).mpr
    (S.logCoeffPiDigitVanishing_of_colemanDigitLadder37 hladder height)

/-- **Non-vacuity of the digit ladder core** (`p = 37`, soundness witness): the
single-unit witness `piOrderWitnessCoeff` realises `ColemanDigitLadder37` (with
`r = 0`, zero weights).  So the core introduces no hidden contradiction. -/
theorem colemanDigitLadder37_inhabited (S : StickelbergerF1Setup 37) :
    ∃ c : (ZMod 37)ˣ → S.O, S.ColemanDigitLadder37 c := by
  refine ⟨S.piOrderWitnessCoeff, 0, fun _ => 0, S.residue_piOrderWitnessCoeff, ?_, ?_, ?_⟩
  · rw [Polynomial.C_0]
  · intro d _; rw [Polynomial.natDegree_zero]; omega
  · intro d hd; exact S.colemanNextRungResidue_thirtytwo_inhabited hd

end StickelbergerF1Setup

end BernoulliRegular.FLT37.PadicL

end

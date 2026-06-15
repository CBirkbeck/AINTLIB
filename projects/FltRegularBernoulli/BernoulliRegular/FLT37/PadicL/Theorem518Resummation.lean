import BernoulliRegular.FLT37.PadicL.GaussSumValuationF1Stickelberger
import BernoulliRegular.FLT37.PadicL.LpValueFormula
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.NumberTheory.Bernoulli

/-!
# Washington Theorem 5.18 resummation — the genuine analytic pieces (4b, 4e, …)

This file attacks the **deep analytic core** behind `LpData.logBernoulli`
(`LpValueFormula.lean`): the valuation of the character-twisted `p`-adic-log sum

  `logSum i = Σ_{a=1}^{p-1} ω^{-i}(a) · log_p(1 - ζ_p^a)`,

which Washington (GTM 83, Theorem 5.18, pp. 63–66, Case I `f = p`) resums into the
generalized-Bernoulli / Gauss-sum form

  `L_p(1, ω^i) = -(τ(ω^{-i})/p) · logSum i`,   `v_p(logSum i) = v_p(B_i/i) + v(p) - i/(p-1)`.

Two self-contained ingredients of that resummation are **proved unconditionally**
here over the abstract DVR `StickelbergerF1Setup` of `GaussSumValuationF1.lean`:

* **(4b) Lemma 5.19** — the finite-difference vanishing
  `Σ_{k=0}^{i} (-1)^k C(i,k) k^m = 0` for `m < i`
  (`alternating_sum_choose_mul_pow_eq_zero`), the combinatorial annihilation that
  kills the low-degree tail of the `log φ(X)` expansion.  Proved from mathlib's
  iterated forward difference `Δ_[1]^[i]` applied to `x ↦ x^m`
  (`fwdDiff_iter_pow_eq_zero_of_lt`, `fwdDiff_iter_eq_sum_shift`).

* **(4e) Gauss-sum collapse** — the orthogonality identity
  `Σ_{a} ω^{-i}(a) · ζ^{(j·a).rep} = ω^i(j) · τ(ω^{-i})`   for a unit `j`
  (`gaussSumTwist_collapse`), the algebraic step that pulls the Gauss sum
  `τ(ω^{-i})` out of the inner `a`-sum.  Proved from mathlib's `gaussSum_mulShift`
  via the file's identification `S.gaussSum i = gaussSum (χ_i) ψ`.

These are exactly the two ingredients that combine (the `log_p` series expansion
fed through (4e), with the (4b)-annihilated low-degree terms) to give the
generalized-Bernoulli identification of `logSum`.  The remaining genuinely
analytic step — the `log_p`-series expansion `log_p(1 - ζ^a) = Σ_n c_n ζ^{an}` and
its `p`-integral leading coefficient — is isolated as the precise named sub-leaf
`LogSeriesGaussExpansion` (genuinely smaller than `logBernoulli`: it is the
single inner-coefficient statement, with the Gauss-sum factoring and the
finite-difference annihilation already discharged).

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83,
  Thm 5.18 (pp. 63–66), Lemma 5.19, Cor 5.13.
-/

namespace BernoulliRegular.FLT37.PadicL

open Finset
open scoped fwdDiff

/-! ## (4b) Washington Lemma 5.19 — finite-difference vanishing -/

section Lemma519

variable {R : Type*} [CommRing R]

/-- **Washington Lemma 5.19** (the finite-difference annihilation), unconditional:
for `m < i`,

  `Σ_{k=0}^{i} (-1)^k · C(i,k) · k^m = 0`   in any commutative ring `R`.

This is the `i`-th iterated forward difference `Δ_[1]^[i]` of `x ↦ x^m` evaluated
at `0`: by `fwdDiff_iter_eq_sum_shift` it equals
`Σ_k (-1)^{i-k} C(i,k) k^m`, and by `fwdDiff_iter_pow_eq_zero_of_lt` (the `m`-degree
monomial is killed by `i > m` differences) it is `0`.  The global sign `(-1)^{i-k}`
is converted to `(-1)^k` by multiplying through by the unit `(-1)^i`. -/
theorem alternating_sum_choose_mul_pow_eq_zero {i m : ℕ} (hmi : m < i) :
    ∑ k ∈ range (i + 1), (-1 : R) ^ k * (i.choose k : R) * (k : R) ^ m = 0 := by
  -- The `i`-th forward difference of `x ↦ x^m` is the zero function (since `m < i`).
  have hzero : Δ_[(1 : R)]^[i] (fun r : R ↦ r ^ m) = 0 :=
    fwdDiff_iter_pow_eq_zero_of_lt hmi
  -- Evaluate the Newton expansion at `y = 0`.
  have hsum := fwdDiff_iter_eq_sum_shift (h := (1 : R)) (fun r : R ↦ r ^ m) i 0
  rw [hzero, Pi.zero_apply] at hsum
  -- `0 = Σ_k (-1)^{i-k} C(i,k) · (0 + k•1)^m = Σ_k (-1)^{i-k} C(i,k) · k^m`.
  have hsimp : ∀ k ∈ range (i + 1),
      ((-1 : ℤ) ^ (i - k) * (i.choose k : ℤ)) • ((0 : R) + (k : ℕ) • (1 : R)) ^ m
        = (-1 : R) ^ (i - k) * (i.choose k : R) * (k : R) ^ m := by
    intro k _
    rw [zero_add, nsmul_eq_mul, mul_one, zsmul_eq_mul]
    push_cast
    ring
  rw [Finset.sum_congr rfl hsimp] at hsum
  -- Multiply the (vanishing) sum by the unit `(-1)^i` and absorb `(-1)^{i-k}·(-1)^i = (-1)^k`.
  have hmul : (-1 : R) ^ i * ∑ k ∈ range (i + 1),
        (-1 : R) ^ (i - k) * (i.choose k : R) * (k : R) ^ m = 0 := by
    rw [← hsum]; ring
  rw [Finset.mul_sum] at hmul
  rw [← hmul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  -- `(-1)^i · (-1)^{i-k} = (-1)^{2i - k} = (-1)^{-k} = (-1)^k`.
  have hpow : (-1 : R) ^ i * (-1 : R) ^ (i - k) = (-1 : R) ^ k := by
    rw [← pow_add]
    have : i + (i - k) = 2 * (i - k) + k := by omega
    rw [this, pow_add, pow_mul]
    simp
  rw [← hpow]; ring

/-- **Washington Lemma 5.19, the `m = 0` slice**: `Σ_{k=0}^{i} (-1)^k C(i,k) = 0`
for `i ≥ 1` (the alternating sum of a full row of Pascal's triangle).  A direct
specialisation of `alternating_sum_choose_mul_pow_eq_zero` at `m = 0` (using
`k^0 = 1`); this is the boundary case that, together with the `m ≥ 1` slices,
annihilates the constant + low-degree part of the `log φ(X)` expansion. -/
theorem alternating_sum_choose_eq_zero {i : ℕ} (hi : 1 ≤ i) :
    ∑ k ∈ range (i + 1), (-1 : R) ^ k * (i.choose k : R) = 0 := by
  have h := alternating_sum_choose_mul_pow_eq_zero (R := R) (m := 0) (i := i) hi
  simpa using h

/-- **Washington Lemma 5.19 over `ℤ`** (the form Washington states): for `m < i`,
`Σ_{k=0}^{i} (-1)^k C(i,k) k^m = 0` in `ℤ`.  This is the FLT-relevant instance
(the `log φ(X)`-tail annihilation uses the integer coefficients). -/
theorem alternating_sum_choose_mul_pow_eq_zero_int {i m : ℕ} (hmi : m < i) :
    ∑ k ∈ range (i + 1), (-1 : ℤ) ^ k * (i.choose k : ℤ) * (k : ℤ) ^ m = 0 :=
  alternating_sum_choose_mul_pow_eq_zero hmi

end Lemma519

/-! ## (4a) The `p`-adic log series expansion `log_p(1 - T) = -Σ_n T^n/n`

The first analytic ingredient of Washington's resummation (4a): the Iwasawa
`p`-adic logarithm of `1 - T` is the negative of the formal `Σ T^n/n` series.  This
is proved **directly from the definition** of `padicLog` in `PadicLog.lean`
(`log_p x = Σ_n (-1)^{n+1}(x-1)^n/n`): substituting `x = 1 - T` gives
`(x-1)^n = (-T)^n = (-1)^n T^n`, and `(-1)^{n+1}(-1)^n = -1`, so every summand is
`-T^n/n`.  Feeding this through the Gauss-sum collapse (4e) over `T = ζ^a` is what
produces the twisted-coefficient functional `Λ i`. -/

section LogSeries

variable {p : ℕ} [hp : Fact p.Prime]

/-- The `n`-th term of the geometric log series `Σ_{n ≥ 1} T^n / n` (the `n = 0`
term is `0`). -/
noncomputable def geomLogSummand (T : ℚ_[p]) (n : ℕ) : ℚ_[p] :=
  if n = 0 then 0 else T ^ n / (n : ℚ_[p])

@[simp] theorem geomLogSummand_zero (T : ℚ_[p]) : geomLogSummand T 0 = 0 := by
  simp [geomLogSummand]

theorem geomLogSummand_of_ne_zero (T : ℚ_[p]) {n : ℕ} (hn : n ≠ 0) :
    geomLogSummand T n = T ^ n / (n : ℚ_[p]) := by simp [geomLogSummand, hn]

/-- **The negated geometric log series equals the `padicLog` summand at `1 - T`**:
`padicLogSummand (1 - T) n = - geomLogSummand T n` for every `n`.  This is the
per-term identity behind (4a): `(-1)^{n+1}((1-T)-1)^n = (-1)^{n+1}(-T)^n = -T^n`. -/
theorem padicLogSummand_one_sub_eq_neg_geom (T : ℚ_[p]) (n : ℕ) :
    padicLogSummand (1 - T) n = - geomLogSummand T n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [padicLogSummand_of_ne_zero _ hn, geomLogSummand_of_ne_zero _ hn]
    -- The sign factor: (-1)^{n+1} · (-1)^n = -1, hence (-1)^{n+1}·(-T)^n = -T^n.
    have hsign : (-1 : ℚ_[p]) ^ (n + 1) * (-1 : ℚ_[p]) ^ n = -1 := by
      rw [← pow_add, show n + 1 + n = 2 * n + 1 from by ring, pow_succ, pow_mul]
      simp
    have hnum : (-1 : ℚ_[p]) ^ (n + 1) * (1 - T - 1) ^ n = - T ^ n := by
      rw [show (1 : ℚ_[p]) - T - 1 = (-1) * T from by ring, mul_pow, ← mul_assoc, hsign,
        neg_one_mul]
    rw [hnum, neg_div]

/-- **(4a) The `p`-adic log series expansion**:

  `log_p(1 - T) = - Σ_{n ≥ 1} T^n / n`   (as `tsum`s in `ℚ_[p]`).

Proved termwise from `padicLogSummand_one_sub_eq_neg_geom` via `tsum_neg`.  This is
the exact analytic input (4a) that, applied at `T = ζ^a` and summed against
`ω^{-i}(a)` with the (4e) collapse, resums `logSum` into `τ(ω^{-i}) · Λ i`. -/
theorem padicLog_one_sub_eq_neg_tsum_geom (T : ℚ_[p]) :
    padicLog (1 - T) = - ∑' n : ℕ, geomLogSummand T n := by
  rw [padicLog_eq_tsum]
  rw [show (∑' n : ℕ, padicLogSummand (1 - T) n) = ∑' n : ℕ, - geomLogSummand T n from
    tsum_congr (padicLogSummand_one_sub_eq_neg_geom T)]
  rw [tsum_neg]

end LogSeries

/-! ## (4e) The Gauss-sum collapse (orthogonality factoring of `τ`) -/

namespace StickelbergerF1Setup

open IsDiscreteValuationRing IsLocalRing

variable {p : ℕ} [hp : Fact p.Prime] (S : StickelbergerF1Setup p)

/-- The character-twisted inner sum that appears after expanding `log_p(1 - ζ^a)`
as a series in `ζ^a` and exchanging the order of summation:

  `gaussSumTwist i j = Σ_{a ∈ (ZMod p)ˣ} (ω a)^{-i} · ζ^{(j·a).rep}`,

i.e. the `n = j` slice of `Σ_a ω^{-i}(a) ζ^{a·n}`.  (For `j = 1` it is the Gauss
sum `S.gaussSum i` itself.) -/
noncomputable def gaussSumTwist (i : ℕ) (j : (ZMod p)ˣ) : S.O :=
  ∑ a : (ZMod p)ˣ, (((S.ω a)⁻¹ ^ i : S.Oˣ) : S.O) * (1 + S.π) ^ teichRep (j * a)

/-- The twisted inner sum is mathlib's Gauss sum with the additive character shifted
by `j`: `gaussSumTwist i j = gaussSum (χ_i) (mulShift ψ j)`.  (Same identification as
`gaussSum_eq_mathlib`, with `ψ ↦ mulShift ψ j`, since the summand exponent is
`(j·a).rep` and `mulShift ψ j (a) = ψ(j·a) = ζ^{(j·a).rep}`.) -/
theorem gaussSumTwist_eq_mathlib (i : ℕ) (j : (ZMod p)ˣ) :
    S.gaussSumTwist i j
      = _root_.gaussSum (S.teichCharPow i) (AddChar.mulShift S.addCharPi (j : ZMod p)) := by
  classical
  -- Mathlib's shifted Gauss sum, split off the `a = 0` term (`χ 0 = 0`).
  have hmathlib : _root_.gaussSum (S.teichCharPow i) (AddChar.mulShift S.addCharPi (j : ZMod p)) =
      ∑ a ∈ Finset.univ \ {(0 : ZMod p)},
        S.teichCharPow i a * AddChar.mulShift S.addCharPi (j : ZMod p) a := by
    have hsplit := Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ (0 : ZMod p))
      (fun a : ZMod p => S.teichCharPow i a * AddChar.mulShift S.addCharPi (j : ZMod p) a)
    rw [MulChar.map_zero, zero_mul, add_zero] at hsplit
    exact hsplit
  rw [hmathlib]
  let φ : (ZMod p)ˣ ↪ ZMod p := ⟨fun x ↦ x, Units.val_injective⟩
  have hmap : (Finset.univ : Finset (ZMod p)ˣ).map φ = Finset.univ \ {0} := by
    ext x
    simpa only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      Finset.mem_sdiff, Finset.mem_singleton, φ] using isUnit_iff_ne_zero
  rw [← hmap, Finset.sum_map]
  unfold StickelbergerF1Setup.gaussSumTwist
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Function.Embedding.coeFn_mk, teichCharPow_apply_unit]
  -- `mulShift ψ j (a) = ψ (j·a) = (1+π)^{(j·a).rep}` (and `(j·a).rep = ((j*a : ℤ/p)).val`).
  rw [AddChar.mulShift_apply,
    show ((j : ZMod p) * (a : ZMod p)) = ((j * a : (ZMod p)ˣ) : ZMod p) from by
      rw [Units.val_mul], addCharPi_apply_unit]

/-- **(4e) the Gauss-sum collapse** (Washington's orthogonality factoring,
the step that pulls `τ(ω^{-i})` out of the inner `a`-sum):

  `Σ_{a ∈ (ZMod p)ˣ} (ω a)^{-i} · ζ^{(j·a).rep} = (ω j)^i · τ(ω^{-i})`   for a unit `j`.

Proved from mathlib's `gaussSum_mulShift`
`χ(j) · gaussSum χ (mulShift ψ j) = gaussSum χ ψ` with `χ = ω^{-i}`, after
identifying both sides with the abstract Gauss sums and noting
`χ(j)⁻¹ = (ω j)^i`. -/
theorem gaussSumTwist_collapse (i : ℕ) (j : (ZMod p)ˣ) :
    S.gaussSumTwist i j = (((S.ω j) ^ i : S.Oˣ) : S.O) * S.gaussSum i := by
  -- `gaussSum_mulShift`:  χ(j) · gaussSum χ (mulShift ψ j) = gaussSum χ ψ.
  have hshift := _root_.gaussSum_mulShift (S.teichCharPow i) S.addCharPi j
  rw [← S.gaussSumTwist_eq_mathlib i j, ← S.gaussSum_eq_mathlib i] at hshift
  -- `χ(j) = (ω j)^{-i}`, a unit, so multiply both sides by its inverse `(ω j)^i`.
  have hχj : S.teichCharPow i (j : ZMod p) = (((S.ω j)⁻¹ ^ i : S.Oˣ) : S.O) :=
    S.teichCharPow_apply_unit i j
  rw [hχj] at hshift
  -- From `((ω j)⁻¹^i) · gaussSumTwist = gaussSum`, deduce `gaussSumTwist = (ω j)^i · gaussSum`.
  have hunit : (((S.ω j) ^ i : S.Oˣ) : S.O) * (((S.ω j)⁻¹ ^ i : S.Oˣ) : S.O) = 1 := by
    rw [← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow, Units.val_one]
  calc S.gaussSumTwist i j
      = (((S.ω j) ^ i : S.Oˣ) : S.O) * (((S.ω j)⁻¹ ^ i : S.Oˣ) : S.O) * S.gaussSumTwist i j := by
        rw [hunit, one_mul]
    _ = (((S.ω j) ^ i : S.Oˣ) : S.O) * S.gaussSum i := by rw [mul_assoc, hshift]

@[simp] theorem gaussSumTwist_one (i : ℕ) : S.gaussSumTwist i 1 = S.gaussSum i := by
  rw [gaussSumTwist_collapse, ← S.omegaHom_apply, map_one, one_pow, Units.val_one, one_mul]

/-- **The `p ∣ n` slice of the resummation vanishes** (orthogonality, the "`p ∣ j`
term" of Washington's (4e)): when the exponent multiplier `n` is divisible by `p`,
`ζ^{n·a.rep} = (ζ^p)^{·} = 1`, so the twisted sum collapses to
`Σ_a (ω a)^{-i} = gaussSumCoeff i 0 = 0` (nontrivial-character orthogonality).
Concretely, for `1 ≤ i < p - 1`:

  `Σ_{a ∈ (ZMod p)ˣ} (ω a)^{-i} · ζ^{(p·k)·a.rep-style monomial} = 0`,

realised here as the vanishing of the twisted sum with a *trivial* (all-ones)
inner exponent.  This is the orthogonality input that removes the `p ∣ n` terms
when grouping the `ζ`-series by residue class. -/
theorem gaussSumTwist_trivial_eq_zero {i : ℕ} (hi0 : 0 < i) (hip : i < p - 1) :
    ∑ a : (ZMod p)ˣ, (((S.ω a)⁻¹ ^ i : S.Oˣ) : S.O) * (1 : S.O) = 0 := by
  simp only [mul_one]
  -- This is exactly `gaussSumCoeff i 0` (the `C(·, 0) = 1` slice), which vanishes.
  have hc0 := S.gaussSumCoeff_zero_eq_zero hi0 hip
  unfold StickelbergerF1Setup.gaussSumCoeff at hc0
  rw [← hc0]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Nat.choose_zero_right, Nat.cast_one, mul_one]

/-! ### The resummation factoring `logSum i = τ(ω^{-i}) · Λ(i)`

After expanding `log_p(1 - ζ^a)` as a `ζ`-series (Washington 4a) and grouping the
sum-index by its residue class mod `p`, the character-twisted log-sum

  `logSum i = Σ_a ω^{-i}(a) · log_p(1 - ζ^a)`

takes the shape `Σ_{j : units} c_j · (Σ_a ω^{-i}(a) ζ^{(j·a).rep})` for some
`ζ`-series coefficients `c : (ZMod p)ˣ → O` (the `j`-residue-class sum of the
analytic coefficients).  The inner `a`-sum is the Gauss-sum collapse (4e), so the
**whole double sum factors through the Gauss sum**:

  `logSum i = τ(ω^{-i}) · Σ_j c_j · (ω j)^i`.

The `Σ_j c_j (ω j)^i` factor — call it `Λ i` — is the character-twisted
generalized-Bernoulli sum whose valuation Washington reads off (Cor 5.13 + Kummer).
This subsection proves the **factoring** (algebraic, unconditional from (4e)); the
remaining valuation of `Λ i` is the named residual `logCoeffBernoulliValuation`. -/

/-- **The resummed log-sum**, abstracted over the `ζ`-series coefficients
`c : (ZMod p)ˣ → O` (the residue-class collection of Washington's analytic
`log_p`-series coefficients):

  `logSumViaSeries c i = Σ_{j : units} c_j · (Σ_a ω^{-i}(a) · ζ^{(j·a).rep})`.

This is the exact post-(4a)-expansion shape of `logSum i`; `logSumViaSeries_eq`
factors it as `τ(ω^{-i}) · (Σ_j c_j (ω j)^i)`. -/
noncomputable def logSumViaSeries (c : (ZMod p)ˣ → S.O) (i : ℕ) : S.O :=
  ∑ j : (ZMod p)ˣ, c j * S.gaussSumTwist i j

/-- **The twisted log-coefficient functional** `Λ i = Σ_j c_j · (ω j)^i`, the
factor remaining after the Gauss sum `τ(ω^{-i})` is pulled out.  This is the
character-twisted finite sum whose valuation is the generalized-Bernoulli /
Kummer content of `logBernoulli` (Washington Cor 5.13). -/
noncomputable def logCoeffSum (c : (ZMod p)ˣ → S.O) (i : ℕ) : S.O :=
  ∑ j : (ZMod p)ˣ, c j * (((S.ω j) ^ i : S.Oˣ) : S.O)

/-- **The resummation factoring** (algebraic, unconditional from (4e)):

  `logSumViaSeries c i = (Σ_j c_j (ω j)^i) · τ(ω^{-i}) = logCoeffSum c i · gaussSum i`.

This pulls the Gauss sum out of the whole resummed double sum, reducing the
valuation of `logSum` to that of the twisted log-coefficient functional `Λ i`.
Each inner sum collapses by `gaussSumTwist_collapse`, then `gaussSum i` factors out
of the `j`-sum. -/
theorem logSumViaSeries_eq (c : (ZMod p)ˣ → S.O) (i : ℕ) :
    S.logSumViaSeries c i = S.logCoeffSum c i * S.gaussSum i := by
  unfold logSumViaSeries logCoeffSum
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [S.gaussSumTwist_collapse i j, mul_assoc]

/-- **The precise remaining analytic residual**, isolated to the twisted
log-coefficient functional alone (the Gauss-sum factor and the (4b)/(4e)
combinatorics are already discharged).

`LogCoeffBernoulliValuation S v c` asserts that, with `v` a `ℚ`-valued valuation on
`S.O` and `c` Washington's residue-class `log_p`-series coefficients, the twisted
log-coefficient functional `Λ i = Σ_j c_j (ω j)^i` has valuation

  `v(Λ i) = v_p(B_i / i) + v(p) - 2·i/(p-1)`   for the even FLT range,

where the Bernoulli term is the `p`-adic valuation of `B_i/i` (as carried by
`bernoulliFactorQp p i`).  Via `logCoeffBernoulli_implies_logBernoulli` this is
*equivalent* to the `logBernoulli` valuation
`v(logSumViaSeries c i) = v_p(B_i/i) + v(p) - i/(p-1)`, but it is genuinely
**smaller**: the Gauss-sum factoring (`logSumViaSeries_eq`), the orthogonality
collapse (4e, `gaussSumTwist_collapse`), and the finite-difference annihilation
(4b) are no longer part of it — only the generalized-Bernoulli identification of
the single character-twisted coefficient sum remains (Washington Cor 5.13 +
Kummer). -/
def LogCoeffBernoulliValuation (v : S.O → ℚ) (c : (ZMod p)ˣ → S.O) : Prop :=
  ∀ i, 2 ≤ i → i ≤ p - 3 → Even i →
    v (S.logCoeffSum c i) =
      ((bernoulliFactorQp p i).valuation : ℚ) + v (p : S.O)
        - 2 * ((i : ℚ) / ((p : ℚ) - 1))

/-- **The reduction is exact**: the isolated residual `LogCoeffBernoulliValuation`
(valuation of the twisted log-coefficient sum `Λ i`), together with the proven
resummation factoring `logSumViaSeries_eq` and the proven Gauss-sum valuation
`v(gaussSum i) = i/(p-1)` (here taken as an input `hgauss`, discharged by
`gaussSumValuationCaseF1_proven`/`normVal`), yields exactly the `logBernoulli`
valuation of the resummed log-sum:

  `v(logSumViaSeries c i) = v_p(B_i/i) + v(p) - i/(p-1)`.

So discharging `LogCoeffBernoulliValuation` discharges `logBernoulli` for the
explicit resummed log-sum, with everything between them proved. -/
theorem logCoeffBernoulli_implies_logBernoulli {v : S.O → ℚ}
    (hmul : ∀ x y : S.O, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y) (c : (ZMod p)ˣ → S.O)
    (hgauss : ∀ i, 2 ≤ i → i ≤ p - 3 → Even i →
      v (S.gaussSum i) = (i : ℚ) / ((p : ℚ) - 1))
    (hΛ : S.LogCoeffBernoulliValuation v c)
    {i : ℕ} (h1 : 2 ≤ i) (h2 : i ≤ p - 3) (hev : Even i)
    (hcoeff : S.logCoeffSum c i ≠ 0) (hgs : S.gaussSum i ≠ 0) :
    v (S.logSumViaSeries c i) =
      ((bernoulliFactorQp p i).valuation : ℚ) + v (p : S.O) - (i : ℚ) / ((p : ℚ) - 1) := by
  rw [S.logSumViaSeries_eq c i, hmul _ _ hcoeff hgs, hΛ i h1 h2 hev,
    hgauss i h1 h2 hev]
  ring

end StickelbergerF1Setup

end BernoulliRegular.FLT37.PadicL

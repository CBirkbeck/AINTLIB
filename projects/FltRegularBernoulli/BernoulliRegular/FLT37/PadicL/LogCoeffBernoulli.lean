import BernoulliRegular.FLT37.PadicL.Theorem518Resummation
import BernoulliRegular.IrregularPrimes.KummerCongruenceFull

/-!
# The Kubota–Leopoldt core of Washington Theorem 5.18 — `LogCoeffBernoulliValuation`

This file attacks the **deep analytic heart** isolated as
`StickelbergerF1Setup.LogCoeffBernoulliValuation` in `Theorem518Resummation.lean`:
the valuation of the character-twisted log-coefficient functional

  `Λ i = logCoeffSum c i = Σ_{j ∈ (ZMod p)ˣ} c_j · (ω j)^i`

equals `v_p(B_i / i) + v(p) − 2·i/(p−1)` for the even FLT range.  After the proven
Gauss-sum collapse (`logSumViaSeries_eq`) the whole resummation is reduced to this
functional, and `Λ i` is — for Washington's residue-class `log_p`-series
coefficients `c_j = −Σ_{n ≡ j (p), p∤n} 1/n` — the **regularized character-power
sum** `Λ i = −Σ_{n≥1, p∤n} (ω n)^i / n`, whose valuation is the Kubota–Leopoldt
`p`-adic `L`-value `↔` generalized-Bernoulli identification (Cor 5.13 + Kummer).

## What is PROVED here (the genuine Kubota–Leopoldt content)

The genuine mathematics of this step is two-fold; both halves are **proved
unconditionally** over the abstract DVR `StickelbergerF1Setup`.

### Step 2 — the Teichmüller correction `(ω j)^i ≡ j^i (mod 𝔓)`

`omega_residue` gives `residue(ω j) = j`, hence `residue((ω j)^i) = j^i` in `ZMod p`
(`residue_omega_pow`).  Consequently the **residue of any character-twisted
coefficient sum is the corresponding `ZMod p` character-power sum**
(`residue_logCoeffSum`): for `c : (ZMod p)ˣ → O`,

  `residue(Σ_j c_j (ω j)^i) = Σ_j residue(c_j) · j^i`.

This is the Teichmüller-vs-naive correction in sharp residue form: the higher
corrections `(ω j)^i − j^i ∈ 𝔓` drop out modulo `𝔓`.

### Step 1 — the power-sum ↔ Bernoulli bridge (Faulhaber / Cor 5.13)

The **mathlib power-sum formula** `sum_range_pow` feeds the repo's
`sum_range_pow_sub_p_mul_bernoulli_strong` (`Σ_{k<p} k^i − p·B_i = i·p²·z`).  We
transport it to the **units** power-sum `Σ_{j ∈ 𝔽_p^×} (j.val)^i` via
`sum_units_val_pow_eq_sum_range` (`sum_units_val_pow_sub_p_mul_bernoulli`), and read
off the **sharp `p`-adic valuation** `v_p(Σ_j (j.val)^i) = 1` in the regular regime
`v_p(B_i) = 0` (`valuation_sum_units_val_pow`), using the exactness lemma
`Padic.valuation_sub_eq_of_lt` (the perturbation `i·p²·z` has order `≥ 2`, the
leading `p·B_i` has order exactly `1`).  This is the genuine `v_p ≤ 1` Kubota–Leopoldt
read-off, fully proved.  Its `ZMod p` shadow `Σ_j j^i = 0` (orthogonality,
`sum_units_pow_eq_zero_of_lt`) is the residue-level vanishing.

## The isolated smallest TRUE core

After Steps 1+2, the only remaining content is the lift of the mod-`𝔓` residue
identification to the sharp **valuation** of `Λ i` in the *boundary* regime
`v_p(B_i/i) ≥ 1` (which is where the regular-regime read-off
`valuation_sum_units_val_pow` does not apply, and is exactly the FLT37 index
`i = 32` with `v₃₇(B₃₂/32) = 1`).  It is isolated as the integral `𝔓`-adic order
`IntegralLogCoeffValuationAt c i` (`addVal(Λ i) + 2i = (p−1)(v_p(B_i/i)+1)`) — the
analogue of `IntegralStickelbergerValuationF1` for the log-coefficient functional,
*at a single index* (the universal-range form is false: for indices with
`2i/(p−1) > v_p(B_i/i)+1` the functional has a `𝔓`-pole and leaves `O`).  The
normalisation read-off `addVal → normVal` (division by `p−1`) is proved
(`normVal_logCoeffSum_of_integralAt`, `logCoeffBernoulli_target_normVal_of_integralAt`),
and the concrete `p = 37, i = 32` target `normVal(Λ 32) = 2/9`
(`logCoeffBernoulli_target_thirtytwo`) is produced with the Bernoulli arithmetic
`v₃₇(B₃₂/32) = 1` already discharged.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83,
  Thm 5.18 (pp. 63–66), Cor 5.13, Lemma 5.19, §5.4 (the `L_p` limit).
-/

namespace BernoulliRegular.FLT37.PadicL

open Finset

namespace StickelbergerF1Setup

open IsDiscreteValuationRing IsLocalRing

variable {p : ℕ} [hp : Fact p.Prime] (S : StickelbergerF1Setup p)

/-! ## Step 2 — the Teichmüller correction `(ω j)^i ≡ j^i (mod 𝔓)` -/

/-- **The Teichmüller power residue** `residue((ω j)^i) = (j : ZMod p)^i`.  This is
the sharp form of the Teichmüller-vs-naive correction: `ω j ≡ j (mod 𝔓)`
(`omega_residue`), so raising to the `i`-th power and applying the residue
homomorphism gives `j^i` exactly.  The higher corrections `(ω j)^i − j^i` live in
the maximal ideal `𝔓` and vanish modulo it. -/
theorem residue_omega_pow (i : ℕ) (j : (ZMod p)ˣ) :
    S.residue ((((S.ω j) ^ i : S.Oˣ) : S.O)) = (j : ZMod p) ^ i := by
  rw [Units.val_pow_eq_pow_val, map_pow, S.omega_residue j]

/-- **The residue of a character-twisted coefficient sum is the `ZMod p`
character-power sum.**  For any coefficient family `c : (ZMod p)ˣ → O`,

  `residue(logCoeffSum c i) = Σ_j residue(c_j) · (j : ZMod p)^i`.

This is Step 2 in functional form: the Teichmüller correction is applied
term-by-term, so `Λ i = Σ_j c_j (ω j)^i` reduces, modulo `𝔓`, to the naive
character-power sum `Σ_j residue(c_j) · j^i`.  No hypothesis on `c` is needed —
this is the *purely algebraic* residue compatibility, the bridge from the abstract
Gauss-sum functional to the `𝔽_p`-arithmetic of Faulhaber/Bernoulli. -/
theorem residue_logCoeffSum (c : (ZMod p)ˣ → S.O) (i : ℕ) :
    S.residue (S.logCoeffSum c i) = ∑ j : (ZMod p)ˣ, S.residue (c j) * (j : ZMod p) ^ i := by
  unfold logCoeffSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, S.residue_omega_pow i j]

end StickelbergerF1Setup

/-! ## Step 1 — the `ZMod p` character-power-sum collapse (Faulhaber mod `p`)

The pure-`𝔽_p` shadow of the power-sum/Bernoulli bridge.  This is the residue of
the Faulhaber identity `Σ_{k<p} k^i = (B_{i+1}(p) − B_{i+1})/(i+1)` (mathlib
`sum_range_pow`): grouping by residue class, `Σ_{j ∈ 𝔽_p^×} j^i` is the leading
character-orthogonality term.  By `FiniteField.sum_pow_units` it equals `−1` when
`(p−1) ∣ i` and `0` otherwise — the residue shadow of `p · B_{1,ω^{−i}}`. -/

section ZModPowerSum

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The `𝔽_p^×` character-power sum** (mathlib `FiniteField.sum_pow_units`):

  `Σ_{j ∈ (ZMod p)ˣ} (j : ZMod p)^i = if (p − 1) ∣ i then −1 else 0`.

This is the `ZMod p` shadow of the generalized-Bernoulli leading term: for the
relevant even range `2 ≤ i ≤ p − 3` one has `(p − 1) ∤ i`, so the sum **vanishes**
(orthogonality of the nontrivial character `j ↦ j^i`), exactly the
`gaussSumCoeff i 0 = 0` collapse.  At `(p − 1) ∣ i` it is `−1`, the value of the
boundary character `ω^{−1}` (Washington's exceptional term `(p − 1)/p`). -/
theorem sum_units_pow_eq (i : ℕ) :
    ∑ j : (ZMod p)ˣ, (j : ZMod p) ^ i = if (p - 1) ∣ i then (-1 : ZMod p) else 0 := by
  classical
  have h := FiniteField.sum_pow_units (K := ZMod p) i
  rw [ZMod.card] at h
  simpa using h

/-- **The character-power sum vanishes on the FLT range** `2 ≤ i ≤ p − 3`:
`Σ_{j ∈ (ZMod p)ˣ} (j : ZMod p)^i = 0`.  Since `0 < i < p − 1`, `(p − 1) ∤ i`, so
the `FiniteField.sum_pow_units` branch is `0` — the orthogonality of the
nontrivial character `j ↦ j^i`.  This is the residue-level statement that the
**naive** truncation `Σ_j c_j (ω j)^i` with constant `c` has positive valuation;
the genuine Bernoulli content lives in the `j`-dependence of `residue(c_j)`. -/
theorem sum_units_pow_eq_zero_of_lt {i : ℕ} (hi0 : 0 < i) (hip : i < p - 1) :
    ∑ j : (ZMod p)ˣ, (j : ZMod p) ^ i = 0 := by
  rw [sum_units_pow_eq i, if_neg]
  intro hdvd
  exact absurd (Nat.le_of_dvd hi0 hdvd) (by omega)

/-! ### The Faulhaber → Bernoulli bridge in `ℚ_[p]` (the genuine second-order content)

The `ZMod p` collapse above is `0` on the FLT range, so it only pins
`v(Λ i) ≥ v(p)`.  The **sharp** valuation comes from the `ℚ_[p]`-level Faulhaber
identity, where the repo already proves (mathlib `sum_range_pow`):

  `Σ_{k<p} (k : ℚ_[p])^i − p·B_i = i·p²·z`   (`sum_range_pow_sub_p_mul_bernoulli_strong`),

i.e. `Σ_{k<p} k^i ≡ p·B_i (mod p²·ℤ_[p])`.  Since the `k = 0` term vanishes for
`i > 0`, the **units** power-sum `Σ_{j ∈ (ZMod p)ˣ} (j.val : ℚ_[p])^i` carries the
same congruence — this is the second-order datum that, for the boundary case
`v_p(B_i) ≥ 1` (e.g. `p = 37, i = 32`), distinguishes `v = 1` from `v ≥ 1`. -/

/-- **The units power-sum equals the range power-sum** in `ℚ_[p]` for `i > 0`:
`Σ_{j ∈ (ZMod p)ˣ} (j.val : ℚ_[p])^i = Σ_{k < p} (k : ℚ_[p])^i`.  The only missing
term is the `k = 0` summand, which vanishes for `i > 0` (`0^i = 0`).  The units are
reindexed to `{1, …, p−1} = range p \ {0}` via `ZMod.val`. -/
theorem sum_units_val_pow_eq_sum_range {i : ℕ} (hi0 : 0 < i) :
    ∑ j : (ZMod p)ˣ, ((j : ZMod p).val : ℚ_[p]) ^ i =
      ∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ i := by
  classical
  -- Reindex the range sum: split off `k = 0`, which contributes `0`.
  have hp : Nat.Prime p := hp.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  -- First: `Σ_{k<p} k^i = Σ_{x:ZMod p} (x.val)^i` via the full bijection `range p ≃ ZMod p`.
  have hfull : ∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ i =
      ∑ x : ZMod p, ((x : ZMod p).val : ℚ_[p]) ^ i := by
    refine (Finset.sum_nbij' (fun x => (x : ZMod p).val) (fun k => (k : ZMod p))
      ?_ ?_ ?_ ?_ ?_).symm
    · intro a _
      simp only [Finset.mem_range]
      exact ZMod.val_lt a
    · intro k _
      exact Finset.mem_univ _
    · intro a _
      exact ZMod.natCast_zmod_val a
    · intro k hk
      simp only [Finset.mem_range] at hk
      exact ZMod.val_natCast_of_lt hk
    · intro a _
      rfl
  -- Then drop the `x = 0` term (`0^i = 0` for `i > 0`).
  have hsplit : ∑ x : ZMod p, ((x : ZMod p).val : ℚ_[p]) ^ i =
      ∑ k ∈ Finset.univ \ {(0 : ZMod p)}, ((k : ZMod p).val : ℚ_[p]) ^ i := by
    rw [← Finset.sum_sdiff (Finset.subset_univ ({0} : Finset (ZMod p))),
      Finset.sum_singleton]
    simp [hi0.ne']
  rw [hfull, hsplit]
  -- The units sum is the same `range p \ {0}` sum, reindexed by `ZMod.val`.
  let φ : (ZMod p)ˣ ↪ ZMod p := ⟨fun x ↦ x, Units.val_injective⟩
  have hmap : (Finset.univ : Finset (ZMod p)ˣ).map φ = Finset.univ \ {0} := by
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      Finset.mem_sdiff, Finset.mem_singleton, φ]
    exact isUnit_iff_ne_zero
  rw [← hmap, Finset.sum_map]
  rfl

/-- **The Faulhaber → Bernoulli congruence for the units power-sum** (the genuine
second-order Kubota–Leopoldt datum), for `5 ≤ p`, `0 < i` even, `(p − 1) ∤ i`:

  `Σ_{j ∈ (ZMod p)ˣ} (j.val : ℚ_[p])^i − p·B_i = i·p²·z`   for some `z ∈ ℤ_[p]`.

This is the repo's `sum_range_pow_sub_p_mul_bernoulli_strong` (built on mathlib's
power-sum formula `sum_range_pow`) transported to the units sum via
`sum_units_val_pow_eq_sum_range`.  It says `Σ_j (j.val)^i ≡ p·B_i (mod p²)` — the
sharp datum behind `v_p(Λ i)` in the boundary case `v_p(B_i) ≥ 1`. -/
theorem sum_units_val_pow_sub_p_mul_bernoulli {i : ℕ} (hp_ge_five : 5 ≤ p)
    (hi0 : 0 < i) (hi_even : Even i) (hnot : ¬ (p - 1) ∣ i) :
    ∃ z : ℤ_[p],
      (∑ j : (ZMod p)ˣ, ((j : ZMod p).val : ℚ_[p]) ^ i) -
          (p : ℚ_[p]) * ((bernoulli i : ℚ) : ℚ_[p]) =
        (i : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := by
  obtain ⟨z, hz⟩ := sum_range_pow_sub_p_mul_bernoulli_strong (p := p) (h := i)
    hp_ge_five hi0 hi_even hnot
  exact ⟨z, by rw [sum_units_val_pow_eq_sum_range hi0]; exact hz⟩

/-- **The SHARP `p`-adic valuation of the units power-sum** (the genuine
Kubota–Leopoldt valuation read-off in the `v_p ≤ 1` regime), fully proved.  For
`5 ≤ p`, `0 < i < p − 1` even, `i` not a boundary index, and the Bernoulli factor
a `p`-adic **unit** (`v_p(B_i) = 0`):

  `v_p(Σ_{j ∈ (ZMod p)ˣ} (j.val : ℚ_[p])^i) = 1`.

This is the sharp valuation obtained from the Faulhaber congruence
`Σ_j (j.val)^i − p·B_i = i·p²·z` (`sum_units_val_pow_sub_p_mul_bernoulli`) via the
exactness lemma `Padic.valuation_sub_eq_of_lt`: the perturbation `i·p²·z` has
valuation `≥ 2`, while `p·B_i` has valuation exactly `1` (since `v_p(B_i) = 0` and
`v_p(p) = 1`), so the difference is dominated and the sum inherits `v_p = 1`.  This
is the residue shadow `↔` second-order datum that pins `v_p(L_p(1, ω^i))` in the
regular regime; the boundary case `v_p(B_i) ≥ 1` (e.g. `p = 37, i = 32`) needs the
full regularized limit, isolated as `IntegralLogCoeffValuationAt`. -/
theorem valuation_sum_units_val_pow {i : ℕ} (hp_ge_five : 5 ≤ p)
    (hi0 : 0 < i) (hip : i < p - 1) (hi_even : Even i) (hnot : ¬ (p - 1) ∣ i)
    (hBunit : padicValRat p (bernoulli i) = 0) (hB_ne : (bernoulli i : ℚ) ≠ 0) :
    Padic.valuation (∑ j : (ZMod p)ˣ, ((j : ZMod p).val : ℚ_[p]) ^ i) = 1 := by
  have hp : Nat.Prime p := hp.out
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hpQ_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hvp : Padic.valuation (p : ℚ_[p]) = 1 := by
    rw [show (p : ℚ_[p]) = ((p : ℕ) : ℚ_[p]) from rfl, Padic.valuation_natCast,
      padicValNat_self]
    rfl
  have hvB : Padic.valuation (((bernoulli i : ℚ) : ℚ_[p])) = 0 := by
    rw [Padic.valuation_ratCast, hBunit]
  -- Set `y = p·B_i` (valuation 1) and the units sum `x`; Faulhaber gives `x - y = perturbation`.
  obtain ⟨z, hz⟩ := sum_units_val_pow_sub_p_mul_bernoulli (p := p) hp_ge_five hi0 hi_even hnot
  set x : ℚ_[p] := ∑ j : (ZMod p)ˣ, ((j : ZMod p).val : ℚ_[p]) ^ i with hx
  set y : ℚ_[p] := (p : ℚ_[p]) * ((bernoulli i : ℚ) : ℚ_[p]) with hy
  have hBcast_ne : (((bernoulli i : ℚ) : ℚ_[p])) ≠ 0 := Rat.cast_ne_zero.mpr hB_ne
  have hy0 : y ≠ 0 := mul_ne_zero hpQ_ne hBcast_ne
  -- `v_p(y) = 1`:  v(p) + v(B_i) = 1 + 0.
  have hvy : y.valuation = 1 := by
    rw [hy, Padic.valuation_mul hpQ_ne hBcast_ne, hvp, hvB, add_zero]
  -- `x - y = i·p²·z` (Faulhaber).  Branch on whether the perturbation vanishes.
  have hxy_eq : x - y = (i : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * (z : ℚ_[p]) := hz
  by_cases hzz : (z : ℚ_[p]) = 0
  · -- perturbation `= 0` ⟹ `x = y`, so `v(x) = v(y) = 1`.
    have : x = y := by rw [← sub_eq_zero, hxy_eq, hzz, mul_zero]
    rw [this, hvy]
  · -- `v_p(x - y) ≥ 2`: `v(i)=0` (i<p), `v(p²)=2`, `v(z)≥0`.
    have hcong : (2 : ℤ) ≤ (x - y).valuation := by
      rw [hxy_eq]
      have hi_ne : (i : ℚ_[p]) ≠ 0 := by
        rw [show (i : ℚ_[p]) = ((i : ℕ) : ℚ_[p]) from rfl, Ne,
          Nat.cast_eq_zero]; omega
      have hp2_ne : ((p : ℚ_[p]) ^ 2) ≠ 0 := pow_ne_zero _ hpQ_ne
      rw [Padic.valuation_mul (mul_ne_zero hi_ne hp2_ne) hzz,
        Padic.valuation_mul hi_ne hp2_ne]
      have hvi : Padic.valuation (i : ℚ_[p]) = 0 := by
        rw [show (i : ℚ_[p]) = ((i : ℕ) : ℚ_[p]) from rfl, Padic.valuation_natCast]
        have hpvi0 : padicValNat p i = 0 := by
          rw [padicValNat.eq_zero_iff]; right; right
          exact Nat.not_dvd_of_pos_of_lt hi0 (by omega)
        rw [hpvi0]; rfl
      have hvp2 : Padic.valuation ((p : ℚ_[p]) ^ 2) = 2 := by
        rw [Padic.valuation_pow, hvp]; ring
      have hvz : (0 : ℤ) ≤ (z : ℚ_[p]).valuation := PadicInt.valuation_coe_nonneg
      rw [hvi, hvp2]; omega
    -- Exactness: v(x) = v(y) = 1.
    rw [hx] at *
    rw [Padic.valuation_sub_eq_of_lt hy0 hcong (by rw [hvy]; norm_num), hvy]

end ZModPowerSum

/-! ## The reduction of `LogCoeffBernoulliValuation` to the regularized-limit core

The mod-`𝔓` content of `Λ i = logCoeffSum c i` is fully captured by Steps 1+2:
`residue(Λ i) = Σ_j residue(c_j)·j^i` (Step 2) is the `ZMod p` character-power sum
whose value the Faulhaber bridge (Step 1) identifies with the Bernoulli residue.
What remains for the **sharp valuation** is purely the Kubota–Leopoldt
regularized-limit content of Washington's `1/n` coefficients — carried as the named
`RegularizedLogCoeffValuation` and shown to *be* the only remaining input. -/

namespace StickelbergerF1Setup

open IsDiscreteValuationRing IsLocalRing

variable {p : ℕ} [hp : Fact p.Prime] (S : StickelbergerF1Setup p)

/-- **`normVal(p) = 1`**: the normalised valuation has `v(p) = 1` by construction,
since `addVal(p) = p − 1` (the ramification index `addVal_p_eq`) and `normVal`
divides by `p − 1`.  This is the normalisation that makes the `LogCoeffBernoulli`
target read `v_p(B_i/i) + 1 − 2i/(p−1)`. -/
theorem normVal_p_eq_one : S.normVal (p : S.O) = 1 := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hpne : ((p : ℚ) - 1) ≠ 0 := by
    have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp2
    linarith
  rw [normVal, S.addVal_p_eq]
  rw [show ((((p - 1 : ℕ) : ℕ∞)).toNat : ℚ) = ((p : ℚ) - 1) from by
    rw [ENat.toNat_coe, Nat.cast_sub (by omega : 1 ≤ p)]; push_cast; ring]
  exact div_self hpne

/-- **The leading residue datum of `Λ i`** (Step 1 + Step 2 combined): when the
coefficients have *constant* residue `r ∈ ZMod p` (i.e. `residue(c_j) = r` for all
`j`, the leading approximation in which the residue-class sums `−Σ_{n≡j} 1/n` are
replaced by their common leading value), the residue of `Λ i` vanishes on the FLT
range:

  `residue(logCoeffSum c i) = r · Σ_j j^i = r · 0 = 0`   for `0 < i < p − 1`.

This is the precise sense in which `v(Λ i) ≥ v(p)` is *forced* by Steps 1+2 (the
character orthogonality `Σ_j j^i = 0`), and equally the precise sense in which the
**leading** term contributes nothing to the sharp valuation — the genuine value
lives entirely in the `j`-dependence of `residue(c_j)`, i.e. in the regularized
`1/n` structure. -/
theorem residue_logCoeffSum_eq_zero_of_const_residue {c : (ZMod p)ˣ → S.O}
    {r : ZMod p} (hr : ∀ j, S.residue (c j) = r) {i : ℕ}
    (hi0 : 0 < i) (hip : i < p - 1) :
    S.residue (S.logCoeffSum c i) = 0 := by
  rw [S.residue_logCoeffSum c i]
  rw [show (∑ j : (ZMod p)ˣ, S.residue (c j) * (j : ZMod p) ^ i)
        = r * ∑ j : (ZMod p)ˣ, (j : ZMod p) ^ i from by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [hr j]]
  rw [sum_units_pow_eq_zero_of_lt hi0 hip, mul_zero]

/-- **The `𝔓`-adic order lower bound from Steps 1+2**: when the coefficients have
constant residue, `π ∣ Λ i`, hence `addVal(Λ i) ≥ 1`.  This is the load-bearing
consequence of the proven Teichmüller correction + orthogonality collapse: the
residue of `Λ i` vanishes (`residue_logCoeffSum_eq_zero_of_const_residue`), and
`residue x = 0 ↔ π ∣ x` (`residue_eq_zero_iff`), so the leading order is at least
the maximal-ideal order.  It is the first nontrivial digit of the integral order
`IntegralLogCoeffValuation`; the higher digits are the Faulhaber/`1/n` content. -/
theorem pi_dvd_logCoeffSum_of_const_residue {c : (ZMod p)ˣ → S.O}
    {r : ZMod p} (hr : ∀ j, S.residue (c j) = r) {i : ℕ}
    (hi0 : 0 < i) (hip : i < p - 1) :
    S.π ∣ S.logCoeffSum c i :=
  (S.residue_eq_zero_iff _).mp (S.residue_logCoeffSum_eq_zero_of_const_residue hr hi0 hip)

theorem one_le_addVal_logCoeffSum_of_const_residue {c : (ZMod p)ˣ → S.O}
    {r : ZMod p} (hr : ∀ j, S.residue (c j) = r) {i : ℕ}
    (hi0 : 0 < i) (hip : i < p - 1) :
    (1 : ℕ∞) ≤ addVal S.O (S.logCoeffSum c i) := by
  have h := S.pi_dvd_logCoeffSum_of_const_residue hr hi0 hip
  have := (S.le_addVal_iff_pi_pow_dvd (S.logCoeffSum c i) 1).mpr (by simpa using h)
  simpa using this

/-- **The genuine remaining analytic core — the integral `𝔓`-adic order of `Λ i`.**

The regularized character sum `Λ i = −Σ_{n≥1, p∤n} (ω n)^i / n` is realised, in the
`Theorem518Resummation` abstraction, as `logCoeffSum c i = Σ_j c_j (ω j)^i ∈ O` with
`c : (ZMod p)ˣ → O` Washington's residue-class `log_p`-series coefficients.  When
`Λ i ∈ O` is integral (which holds exactly when the `LogCoeffBernoulli` target is
nonnegative, e.g. `v_p(B_i/i) + 1 ≥ 2i/(p−1)` — in particular at `p = 37, i = 32`
where it reads `2 ≥ 64/36`), it has a well-defined `𝔓`-adic order `addVal(Λ i)`,
and the Kubota–Leopoldt resummation (Washington §5.4 / pp. 63–66, Cor 5.13 +
Kummer) gives, in the `addVal` normalisation (`v_𝔓(p) = p − 1`, `v_𝔓(π) = 1`):

  `addVal(Λ i) + 2i = (p − 1)·(v_p(B_i/i) + 1)`     (no `ℕ∞` subtraction).

`IntegralLogCoeffValuationAt c i` names that order *at a single index* `i` (it is
**not** asserted as a universal over the whole range: for indices `i` with
`2i/(p−1) > v_p(B_i/i) + 1` the functional `Λ i` has a `𝔓`-adic pole, leaves `O`,
and the `addVal`/`O`-valued statement does not apply — the abstract field
valuation in `LogCoeffBernoulliValuation` is what handles those).  At the integral
indices it is the **analogue of `IntegralStickelbergerValuationF1`** for the
log-coefficient functional: a single `ℕ`-valued order statement about the explicit
element, with the normalisation step (`addVal → normVal`, division by `p − 1`)
proved below.  Steps 1+2 above (`residue_logCoeffSum`, the Faulhaber bridge
`sum_units_val_pow_sub_p_mul_bernoulli`, the orthogonality collapse
`residue_logCoeffSum_eq_zero_of_const_residue`) discharge the mod-`𝔓` class and the
leading-term vanishing; what `IntegralLogCoeffValuationAt` isolates is exactly the
*order* contributed by the `1/n`-regularized limit. -/
def IntegralLogCoeffValuationAt (c : (ZMod p)ˣ → S.O) (i : ℕ) : Prop :=
  (addVal S.O (S.logCoeffSum c i)).toNat + 2 * i
    = (p - 1) * ((bernoulliFactorQp p i).valuation.toNat + 1)

/-- **The normalisation read-off** (`addVal → normVal`, the genuine reduction, at a
single index `i`): if the integral order `IntegralLogCoeffValuationAt c i` holds and
`v_p(B_i/i) ≥ 0`, then the `normVal`-valuation of `Λ i` is the
`LogCoeffBernoulliValuation` target

  `normVal(Λ i) = v_p(B_i/i) + 1 − 2i/(p−1)`.

This is the `(p − 1)`-division step (matching `gaussSumValuationCaseF1_of_integralValuation`):
`normVal x = addVal(x).toNat/(p−1)` and `normVal(p) = 1`, so dividing the integral
identity `addVal(Λ i) + 2i = (p − 1)(v_p(B_i/i) + 1)` through by `p − 1` gives the
target.  (`bernoulliFactorQp p i).valuation ≥ 0` for the `p`-integral `B_i/i`; in
particular `v₃₇(B₃₂/32) = 1 ≥ 0`.) -/
theorem normVal_logCoeffSum_of_integralAt {c : (ZMod p)ˣ → S.O} {i : ℕ}
    (hint : S.IntegralLogCoeffValuationAt c i)
    (hvalnn : 0 ≤ (bernoulliFactorQp p i).valuation) :
    S.normVal (S.logCoeffSum c i) =
      ((bernoulliFactorQp p i).valuation : ℚ) + 1 - 2 * ((i : ℚ) / ((p : ℚ) - 1)) := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hpne : ((p : ℚ) - 1) ≠ 0 := by
    have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp2
    linarith
  -- `valuation.toNat = valuation` since `valuation ≥ 0`.
  have hvcast : (((bernoulliFactorQp p i).valuation.toNat : ℕ) : ℚ)
      = ((bernoulliFactorQp p i).valuation : ℚ) := by
    have : ((bernoulliFactorQp p i).valuation.toNat : ℤ)
        = (bernoulliFactorQp p i).valuation := Int.toNat_of_nonneg hvalnn
    exact_mod_cast this
  have hpsub : (((p - 1 : ℕ)) : ℚ) = ((p : ℚ) - 1) := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]; push_cast; ring
  -- The integral identity, cast to ℚ.
  have hIQ : ((addVal S.O (S.logCoeffSum c i)).toNat : ℚ) + 2 * (i : ℚ)
      = ((p : ℚ) - 1) * (((bernoulliFactorQp p i).valuation : ℚ) + 1) := by
    have hcast := congrArg (fun n : ℕ => (n : ℚ)) hint
    push_cast at hcast
    rw [hpsub, hvcast] at hcast
    linarith [hcast]
  rw [normVal]
  field_simp
  linarith [hIQ]

/-- **The reduction of the `LogCoeffBernoulli` target to the integral core**, for the
`normVal` normalisation, **at a single index** `i`.  Given the integral order
`IntegralLogCoeffValuationAt c i` and `p`-integrality `0 ≤ v_p(B_i/i)`, the
`LogCoeffBernoulliValuation` target valuation holds at `i` with `v = normVal`.  This
consumes the integral core through the proved normalisation read-off
`normVal_logCoeffSum_of_integralAt`. -/
theorem logCoeffBernoulli_target_normVal_of_integralAt {c : (ZMod p)ˣ → S.O} {i : ℕ}
    (hint : S.IntegralLogCoeffValuationAt c i)
    (hvalnn : 0 ≤ (bernoulliFactorQp p i).valuation) :
    S.normVal (S.logCoeffSum c i) =
      ((bernoulliFactorQp p i).valuation : ℚ) + S.normVal (p : S.O)
        - 2 * ((i : ℚ) / ((p : ℚ) - 1)) := by
  rw [S.normVal_p_eq_one, S.normVal_logCoeffSum_of_integralAt hint hvalnn]

/-! ### The `p = 37, i = 32` instance — the only index FLT37 Case II consumes -/

/-- **The concrete `i = 32` integral order target** (`p = 37`): from the integral
order `IntegralLogCoeffValuationAt c 32`, with `v₃₇(B₃₂/32) = 1` resolved (proved),
the `LogCoeffBernoulli` target at `32` reads

  `normVal(Λ 32) = 1 + normVal(37) − 2·32/36 = 1 + 1 − 16/9 = 2/9`,

i.e. `addVal(Λ 32) = 8`.  This is the sharp value that the Cor 8.23 / Thm 8.22
Case-II descent consumes — produced here from the explicit log-coefficient
functional, with the Bernoulli arithmetic already discharged and the only input
the integral order `IntegralLogCoeffValuationAt c 32`. -/
theorem logCoeffBernoulli_target_thirtytwo
    (S : StickelbergerF1Setup 37) {c : (ZMod 37)ˣ → S.O}
    (hint : S.IntegralLogCoeffValuationAt c 32) :
    S.normVal (S.logCoeffSum c 32) =
      (1 : ℚ) + S.normVal ((37 : ℕ) : S.O) - 2 * ((32 : ℚ) / ((37 : ℚ) - 1)) := by
  have hval : (0 : ℤ) ≤ (bernoulliFactorQp 37 32).valuation := by
    rw [valuation_bernoulliFactorQp_thirtytwo]; norm_num
  have h := S.logCoeffBernoulli_target_normVal_of_integralAt hint hval
  rw [valuation_bernoulliFactorQp_thirtytwo] at h
  rw [h]; push_cast; ring

end StickelbergerF1Setup

end BernoulliRegular.FLT37.PadicL

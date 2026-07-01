import BernoulliRegular.FLT37.PadicL.LogCoeffBernoulli

/-!
# The mod-`p³` power-sum / Bernoulli refinement at the boundary index `i = 32`

This file extends the repo's strong Faulhaber congruence
`sum_range_pow_sub_p_mul_bernoulli_strong`

  `Σ_{k<p} k^h − p·B_h = h·p²·z`   (mod `p²`, the second-order datum)

by **one further order** at the boundary index `i = 32` for `p = 37`, to the
**mod-`p³`** refinement

  `Σ_{k<p} k^32 − 37·B_32 = 32·37³·W`   (`W ∈ ℤ_[37]`).

The point of the boundary index is that `v₃₇(B₃₂) = 1`, so the leading term
`37·B₃₂` has `p`-adic valuation **exactly 2**, while the mod-`p²` remainder
`32·37²·z` only carries `v ≥ 2` — a second-order cancellation could a priori push
the power-sum valuation above 2.  The mod-`p³` refinement **closes this gap
unconditionally**: at `h = 32`, `p = 37`, every non-leading Faulhaber term carries
`p^{s+1}` with `s + 1 ≥ 3` and its Bernoulli coefficient `B_{32−s}` is a `37`-unit
(since `36 ∤ (32−s)` for `s ≥ 1`, von Staudt gives no `37` in the denominator, and
`37` is irregular **only** at index `32`, so no `37` in the numerator either, for
`s ≥ 1`).  Hence the entire remainder lands in `32·37³·ℤ_[37]`, has `v ≥ 3 > 2`,
and the ultrametric pins

  `v₃₇(Σ_{k<37} k^32) = 2`   (`power_sum_valuation_thirtytwo`, **unconditional**).

## The Kellner verdict (soundness-critical, honest)

The mod-`p³` Faulhaber expansion of `Σ_{k<p} k^32` involves **only** `B_j` for
`j ≤ 32`.  The **second-order coefficient is `B₃₀·C(32,2)/3`** (the `s = 2` term),
**not** `B_{1184} = B_{32·37}` (`secondOrderFaulhaberTerm_thirtytwo_eq`).  The
Kellner datum `NoSecondOrderIrregularPair 37 32 = ¬ 37³ ∣ B_{1184}.num` governs the
**Iwasawa second-order** structure (the `λ`-invariant / whether `L_p(s, ω³²)` has a
simple vs. higher-order zero in the `s`-direction); `B_{1184}` does **not** appear
in this finite power-sum at all.  Consequently:

* **The elementary power-sum order `v₃₇(Σ k^32) = 2` is pinned UNCONDITIONALLY**,
  with **no** Kellner input.
* **`IntegralLogCoeffValuationAt c 32` is NOT this power-sum order.**  `Λ 32 =
  Σ_j c_j (ω j)^32 ∈ O` is the character-twisted (Teichmüller) Stickelberger-graded
  functional in the **ramified** ring `O` (`e = p − 1 = 36`, `addVal(p) = 36`); its
  target order is `addVal(Λ 32) = 8`, i.e. `normVal = 2/9`, a *fractional-power* `π`-
  graded order.  The naive power-sum, viewed in `O`, has order `36·2 = 72 ≠ 8`.  The
  `π`-graded order of `Λ 32` is the **genuine Washington Prop 8.12 single-unit
  `p`-adic-log valuation** `v_p(log_p E_{32}^{(N)}) = 32/(p−1) + v_p(L_p(1, ω³²))`,
  the deep core, which is a **separate** datum and is **not** reduced to Kellner by
  the mod-`p³` power-sum refinement.

So this file **discharges the tractable analytic content** (the mod-`p³` Faulhaber
refinement and the unconditional power-sum valuation), and records the honest
finding that the `Λ`-order deep core is the Prop 8.12 `π`-graded Stickelberger
valuation — **not** the elementary power-sum, and **not** controlled by Kellner's
`B_{1184}` via this route.  The smallest TRUE remaining core for the `Λ`-order is
named `LogCoeffPiOrderAtThirtytwo`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Thm 5.18,
  Cor 5.13, Prop 8.12, §6.2 (the Stickelberger `π`-grading).
* Kellner, Math. Comp. 76 (2007), Prop 2.7 (the Iwasawa second-order test —
  `B_{1184}`, **not** the Faulhaber coefficient).
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular.FLT37.PadicL

open Finset BernoulliRegular

/-! ## Step A — the cubic non-leading Faulhaber term

Each non-leading Faulhaber summand `B_{h−s}·C(h,s)·p^{s+1}/(s+1)` with `s ≥ 2`,
whose **Bernoulli factor `B_{h−s}` is `p`-integral** (no von Staudt `p` in the
denominator, i.e. `(p−1) ∤ (h−s)`), is an `h·p³` multiple.  This sharpens
`shifted_faulhaber_term_mem_h_p_sq_of_two_le` (which lands in `h·p²`, losing one
power to absorb a possible von-Staudt `p`): when `B_{h−s}` is already integral, the
full cubic strength of `binomial_divisor_term_mem_h_p_cubed` survives. -/

/-- **Cubic non-leading term, `s ≥ 2`, integral Bernoulli factor.** If `B_{h−s}` is
`p`-integral (`(p−1) ∤ (h−s)`, supplied as a `ℤ_[p]`-witness `hbern`), then the
reindexed Faulhaber summand at `s` is an `h·p³` multiple. -/
theorem shifted_faulhaber_term_mem_h_p_cubed_of_integral_bernoulli
    {p h s : ℕ} [Fact p.Prime] (hp_ge_five : 5 ≤ p)
    (hh_pos : 0 < h) (hs_two : 2 ≤ s) (hs_le : s ≤ h)
    (hbern : ∃ b : ℤ_[p], ((bernoulli (h - s) : ℚ) : ℚ_[p]) = (b : ℚ_[p])) :
    ∃ z : ℤ_[p],
      ((bernoulli (h - s) : ℚ) : ℚ_[p]) *
          ((((Nat.choose h s : ℕ) : ℚ_[p]) *
            ((p : ℚ_[p]) ^ (s + 1)) / ((s + 1 : ℕ) : ℚ_[p]))) =
        (h : ℚ_[p]) * (p : ℚ_[p]) ^ 3 * (z : ℚ_[p]) := by
  obtain ⟨c, hc⟩ :=
    binomial_divisor_term_mem_h_p_cubed (p := p) hp_ge_five hh_pos hs_two hs_le
  obtain ⟨b, hb⟩ := hbern
  refine ⟨b * c, ?_⟩
  rw [hc, hb]
  push_cast
  ring

/-! ## Step B — the full mod-`p³` remainder at `h = 32`, `p = 37`

At the boundary `h = 32`, `p = 37`, every reindexed remainder term with `s ∈
[1, 32)` is an `h·p³` multiple:

* `s = 1`: the term vanishes (`B_{31} = 0`, odd index `> 1`).
* `s ≥ 2`: by Step A, since `B_{32−s}` is a `37`-unit — `36 ∤ (32−s)` for
  `1 ≤ s ≤ 31` (so von Staudt gives no `37` in the denominator) — hence `p`-integral
  and the cubic bound holds.

Summing, the whole non-leading remainder `Σ_{i<32} (term i)` is an `h·p³` multiple,
giving the mod-`p³` power-sum congruence. -/

/-- For `0 ≤ m ≤ 32`, `36 ∤ m` whenever `m ≠ 0`, so by von Staudt `B_m` is
`37`-integral (no `37` in its denominator).  Auxiliary fact threaded into the cubic
remainder bound. -/
theorem bernoulli_le_thirtytwo_integral_thirtyseven {m : ℕ} (hm_pos : 0 < m)
    (hm_le : m ≤ 32) (hm_even : Even m) :
    ∃ b : ℤ_[37], ((bernoulli m : ℚ) : ℚ_[37]) = (b : ℚ_[37]) := by
  haveI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  refine bernoulli_mem_padicInt_vonStaudt_of_not_sub_one_dvd (p := 37) hm_even ?_
  -- `37 − 1 = 36`; for `0 < m ≤ 32`, `36 ∤ m`.
  intro hdvd
  have hle : (36 : ℕ) ≤ m := Nat.le_of_dvd hm_pos (by simpa using hdvd)
  omega

/-- **Each reindexed non-leading remainder term at `h = 32`, `p = 37` is a `32·37³`
multiple.**  The `s = h − i` reindexing matches `faulhaber_remainder_term_mem_h_p_sq`;
the cubic strength comes from the unit Bernoulli factors at the boundary index. -/
theorem faulhaber_remainder_term_thirtytwo_mem_h_p_cubed
    {i : ℕ} (hi : i < 32) :
    ∃ z : ℤ_[37],
      ((bernoulli i : ℚ) : ℚ_[37]) * ((Nat.choose (32 + 1) i : ℕ) : ℚ_[37]) *
          ((37 : ℚ_[37]) ^ (32 + 1 - i)) / ((32 + 1 : ℕ) : ℚ_[37]) =
        (32 : ℚ_[37]) * (37 : ℚ_[37]) ^ 3 * (z : ℚ_[37]) := by
  haveI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  set s : ℕ := 32 - i with hs_def
  have hs_pos : 0 < s := by omega
  have hs_le : s ≤ 32 := by omega
  have hi_eq : i = 32 - s := by omega
  have hexp_hs : 32 + 1 - (32 - s) = s + 1 := by omega
  -- Reduce the summand to the TeX form indexed by `s`.
  have hcoef :
      ((Nat.choose (32 + 1) (32 - s) : ℕ) : ℚ_[37]) *
          ((37 : ℚ_[37]) ^ (s + 1)) / ((32 + 1 : ℕ) : ℚ_[37]) =
        ((Nat.choose 32 s : ℕ) : ℚ_[37]) *
          ((37 : ℚ_[37]) ^ (s + 1)) / ((s + 1 : ℕ) : ℚ_[37]) := by
    have hchoose := choose_succ_div_eq_choose_div (p := 37) (h := 32) (s := s) hs_le
    calc
      ((Nat.choose (32 + 1) (32 - s) : ℕ) : ℚ_[37]) *
          ((37 : ℚ_[37]) ^ (s + 1)) / ((32 + 1 : ℕ) : ℚ_[37]) =
          (((Nat.choose (32 + 1) (32 - s) : ℕ) : ℚ_[37]) / ((32 + 1 : ℕ) : ℚ_[37])) *
            ((37 : ℚ_[37]) ^ (s + 1)) := by ring
      _ = (((Nat.choose 32 s : ℕ) : ℚ_[37]) / ((s + 1 : ℕ) : ℚ_[37])) *
            ((37 : ℚ_[37]) ^ (s + 1)) := by rw [hchoose]
      _ = ((Nat.choose 32 s : ℕ) : ℚ_[37]) *
            ((37 : ℚ_[37]) ^ (s + 1)) / ((s + 1 : ℕ) : ℚ_[37]) := by ring
  by_cases hs_one : s = 1
  · -- `s = 1`: `B_{31} = 0` (odd index, `> 1`), the term vanishes.
    refine ⟨0, ?_⟩
    have h_odd : Odd (32 - s) := by rw [hs_one]; decide
    have h_gt : 1 < 32 - s := by omega
    rw [hi_eq, bernoulli_eq_zero_of_odd h_odd h_gt]
    push_cast
    ring
  · -- `s ≥ 2`: cubic bound via the integral Bernoulli factor.
    have hs_two : 2 ≤ s := by omega
    have hbern : ∃ b : ℤ_[37], ((bernoulli (32 - s) : ℚ) : ℚ_[37]) = (b : ℚ_[37]) := by
      rcases Nat.even_or_odd (32 - s) with heven | hodd
      · -- even index: `B_0 = 1` (a unit) or `0 < 32−s ≤ 30` integral by von Staudt.
        rcases Nat.eq_zero_or_pos (32 - s) with hz | hpos
        · refine ⟨1, ?_⟩; rw [hz, bernoulli_zero]; push_cast; ring
        · exact bernoulli_le_thirtytwo_integral_thirtyseven hpos (by omega) heven
      · -- odd index: either `32−s = 1` (`B_1 = −1/2`, integral at 37) or `B_{32−s} = 0`.
        rcases eq_or_ne (32 - s) 1 with h1 | hne
        · -- `B_1 = −1/2`; `2` is a `37`-unit, so `−2⁻¹ ∈ ℤ_[37]`.
          have h2_unit : IsUnit ((2 : ℕ) : ℤ_[37]) :=
            padicInt_natCast_isUnit_of_not_dvd (p := 37) (n := 2) (by decide)
          set twoInv : ℤ_[37] := (h2_unit.unit⁻¹ : (ℤ_[37])ˣ).val with htwoInv
          have htwo_mul_inv : ((2 : ℕ) : ℤ_[37]) * twoInv = 1 := by
            rw [htwoInv]
            change ((h2_unit.unit * h2_unit.unit⁻¹ : (ℤ_[37])ˣ).val : ℤ_[37]) = 1
            simp
          have htwo_mul_inv_Qp : (2 : ℚ_[37]) * ((twoInv : ℤ_[37]) : ℚ_[37]) = 1 := by
            have := congrArg (fun x : ℤ_[37] => (x : ℚ_[37])) htwo_mul_inv
            push_cast at this; exact this
          refine ⟨-twoInv, ?_⟩
          rw [h1, bernoulli_one]
          have h2Q_ne : (2 : ℚ_[37]) ≠ 0 := by norm_num
          push_cast
          rw [show ((twoInv : ℤ_[37]) : ℚ_[37]) = (2 : ℚ_[37])⁻¹ from
            (inv_eq_of_mul_eq_one_right htwo_mul_inv_Qp).symm]
          field_simp
        · refine ⟨0, ?_⟩
          have hmod : (32 - s) % 2 = 1 := Nat.odd_iff.mp hodd
          have hgt : 1 < 32 - s := by omega
          rw [bernoulli_eq_zero_of_odd hodd hgt]; simp
    obtain ⟨z, hz⟩ :=
      shifted_faulhaber_term_mem_h_p_cubed_of_integral_bernoulli (p := 37) (h := 32) (s := s)
        (by norm_num) (by norm_num) hs_two hs_le hbern
    refine ⟨z, ?_⟩
    calc
      ((bernoulli i : ℚ) : ℚ_[37]) * ((Nat.choose (32 + 1) i : ℕ) : ℚ_[37]) *
          ((37 : ℚ_[37]) ^ (32 + 1 - i)) / ((32 + 1 : ℕ) : ℚ_[37]) =
        ((bernoulli (32 - s) : ℚ) : ℚ_[37]) *
          (((Nat.choose (32 + 1) (32 - s) : ℕ) : ℚ_[37]) *
            ((37 : ℚ_[37]) ^ (s + 1)) / ((32 + 1 : ℕ) : ℚ_[37])) := by
          rw [hi_eq, hexp_hs]; ring
      _ = ((bernoulli (32 - s) : ℚ) : ℚ_[37]) *
          (((Nat.choose 32 s : ℕ) : ℚ_[37]) *
            ((37 : ℚ_[37]) ^ (s + 1)) / ((s + 1 : ℕ) : ℚ_[37])) := by rw [hcoef]
      _ = (32 : ℚ_[37]) * (37 : ℚ_[37]) ^ 3 * (z : ℚ_[37]) := hz

/-- **The full non-leading remainder sum at `h = 32`, `p = 37` is a `32·37³`
multiple.**  Cubic analogue of `faulhaber_remainder_sum_mem_h_p_sq`, valid at the
boundary because all the Bernoulli factors are `37`-units. -/
theorem faulhaber_remainder_sum_thirtytwo_mem_h_p_cubed :
    ∃ W : ℤ_[37],
      (∑ i ∈ Finset.range 32,
        ((bernoulli i : ℚ) : ℚ_[37]) * ((Nat.choose (32 + 1) i : ℕ) : ℚ_[37]) *
          ((37 : ℚ_[37]) ^ (32 + 1 - i)) / ((32 + 1 : ℕ) : ℚ_[37])) =
        (32 : ℚ_[37]) * (37 : ℚ_[37]) ^ 3 * (W : ℚ_[37]) := by
  choose w hw using (fun (i : ℕ) (hi : i < 32) =>
    faulhaber_remainder_term_thirtytwo_mem_h_p_cubed (i := i) hi)
  set W : ℤ_[37] := ∑ i ∈ Finset.attach (Finset.range 32),
    w i.1 (Finset.mem_range.mp i.2) with hW_def
  refine ⟨W, ?_⟩
  rw [← Finset.sum_attach]
  rw [show ((32 : ℚ_[37]) * (37 : ℚ_[37]) ^ 3 * (W : ℚ_[37])) =
      ∑ i ∈ Finset.attach (Finset.range 32),
        (32 : ℚ_[37]) * (37 : ℚ_[37]) ^ 3 *
          ((w i.1 (Finset.mem_range.mp i.2) : ℤ_[37]) : ℚ_[37]) from ?_]
  · exact Finset.sum_congr rfl fun i _ => hw i.1 (Finset.mem_range.mp i.2)
  · rw [hW_def]
    simp [PadicInt.coe_sum, Finset.mul_sum]

/-! ## Step C — the mod-`p³` power-sum congruence and the unconditional valuation -/

/-- **The mod-`p³` strong Faulhaber congruence at `h = 32`, `p = 37`:**

  `Σ_{k<37} k^32 − 37·B_32 = 32·37³·W`,   `W ∈ ℤ_[37]`,

i.e. `Σ_{k<37} k^32 ≡ 37·B₃₂ (mod 37³)`.  This is one order beyond
`sum_range_pow_sub_p_mul_bernoulli_strong` (mod `37²`), available at the boundary
index because every non-leading Faulhaber term carries `37³` (its `37`-unit
Bernoulli factor never erodes the `p^{s+1}` with `s + 1 ≥ 3`). -/
theorem sum_range_pow_thirtytwo_sub_p_mul_bernoulli_cubed :
    ∃ W : ℤ_[37],
      ((∑ k ∈ Finset.range 37, (k : ℚ_[37]) ^ 32)) -
          (37 : ℚ_[37]) * ((bernoulli 32 : ℚ) : ℚ_[37]) =
        (32 : ℚ_[37]) * (37 : ℚ_[37]) ^ 3 * (W : ℚ_[37]) := by
  haveI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  obtain ⟨W, hW⟩ := faulhaber_remainder_sum_thirtytwo_mem_h_p_cubed
  refine ⟨W, ?_⟩
  -- Faulhaber over ℚ then cast to ℚ_[37].  The only `push_cast` friction at the
  -- concrete literals is the denominator `↑32 + 1` vs `33`, fixed by `norm_num`.
  have h_faulhaber_Qp : (∑ k ∈ Finset.range 37, (k : ℚ_[37]) ^ 32) =
      ∑ i ∈ Finset.range (32 + 1),
        ((bernoulli i : ℚ) : ℚ_[37]) * ((Nat.choose (32 + 1) i : ℕ) : ℚ_[37]) *
          ((37 : ℚ_[37]) ^ (32 + 1 - i)) / ((32 + 1 : ℕ) : ℚ_[37]) := by
    have h2 := congrArg (fun q : ℚ => (q : ℚ_[37])) (sum_range_pow 37 32)
    push_cast at h2 ⊢
    rw [show ((32 : ℚ_[37]) + 1) = 33 from by norm_num] at h2
    exact h2
  have hterm_h :
      ((bernoulli 32 : ℚ) : ℚ_[37]) * ((Nat.choose (32 + 1) 32 : ℕ) : ℚ_[37]) *
          ((37 : ℚ_[37]) ^ (32 + 1 - 32)) / ((32 + 1 : ℕ) : ℚ_[37]) =
        (37 : ℚ_[37]) * ((bernoulli 32 : ℚ) : ℚ_[37]) := by
    have hhp1_ne : ((32 + 1 : ℕ) : ℚ_[37]) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Nat.choose_succ_self_right 32, show 32 + 1 - 32 = 1 by omega]
    push_cast
    field_simp [hhp1_ne]
  have h_split :
      (∑ k ∈ Finset.range 37, (k : ℚ_[37]) ^ 32) -
          (37 : ℚ_[37]) * ((bernoulli 32 : ℚ) : ℚ_[37]) =
        ∑ i ∈ Finset.range 32,
          ((bernoulli i : ℚ) : ℚ_[37]) * ((Nat.choose (32 + 1) i : ℕ) : ℚ_[37]) *
            ((37 : ℚ_[37]) ^ (32 + 1 - i)) / ((32 + 1 : ℕ) : ℚ_[37]) := by
    rw [h_faulhaber_Qp, Finset.sum_range_succ, hterm_h]
    ring
  rw [h_split]
  exact hW

/-- **The second-order Faulhaber coefficient at `i = 32` is `B₃₀·C(32,2)/3`** — the
`s = 2` term — **not** `B_{1184}`.  This makes the soundness verdict explicit at the
level of the expansion: the mod-`p³` correction to `Σ k^32` past the leading `37·B₃₂`
is governed by `B₃₀` (a `37`-unit), so it contributes a clean `37³`-order term, and
`B_{1184} = B_{32·37}` (the Kellner datum) **does not appear**. -/
theorem secondOrderFaulhaberTerm_thirtytwo_eq :
    ((bernoulli 30 : ℚ) : ℚ_[37]) * ((Nat.choose 32 2 : ℕ) : ℚ_[37]) *
        ((37 : ℚ_[37]) ^ 3) / ((3 : ℕ) : ℚ_[37]) =
      ((bernoulli (32 - 2) : ℚ) : ℚ_[37]) *
        (((Nat.choose 32 2 : ℕ) : ℚ_[37]) *
          ((37 : ℚ_[37]) ^ (2 + 1)) / ((2 + 1 : ℕ) : ℚ_[37])) := by
  rw [show (32 - 2 : ℕ) = 30 from rfl, show (2 + 1 : ℕ) = 3 from rfl]
  ring

/-- **The `s = 2` term is a unit times `37³` (valuation exactly 3)**: with `B₃₀` a
`37`-unit and `C(32,2) = 496`, `3` both `37`-units, the second-order Faulhaber term
`B₃₀·C(32,2)·37³/3` has `v₃₇ = 3`.  This is the explicit non-cancelling second-order
datum — the concrete witness that the mod-`p³` remainder genuinely has `v ≥ 3` (in
fact `= 3`), independent of any Kellner / `B_{1184}` input. -/
theorem valuation_secondOrderFaulhaberTerm_thirtytwo :
    Padic.valuation (((bernoulli 30 : ℚ) : ℚ_[37]) * ((Nat.choose 32 2 : ℕ) : ℚ_[37]) *
        ((37 : ℚ_[37]) ^ 3) / ((3 : ℕ) : ℚ_[37])) = 3 := by
  haveI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  -- `B₃₀ = 8615841276005 / 14322`, a 37-unit; `C(32,2) = 496`; `3` a 37-unit.
  have hnum30 : (bernoulli 30).num = 8615841276005 := by bernoulli_decide
  have hden30 : (bernoulli 30).den = 14322 := by bernoulli_decide
  have hB30_ne' : (bernoulli 30 : ℚ) ≠ 0 := Rat.num_ne_zero.mp (by rw [hnum30]; decide)
  have hv_B30 : Padic.valuation (((bernoulli 30 : ℚ) : ℚ_[37])) = 0 := by
    rw [Padic.valuation_ratCast, padicValRat_def, hnum30, hden30]
    have h1 : padicValInt 37 8615841276005 = 0 := by
      rw [padicValInt]; exact padicValNat.eq_zero_of_not_dvd (by decide)
    have h2 : padicValNat 37 14322 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
    rw [h1, h2]; norm_num
  have hv_choose : Padic.valuation ((Nat.choose 32 2 : ℕ) : ℚ_[37]) = 0 := by
    rw [show (Nat.choose 32 2 : ℕ) = 496 from rfl, Padic.valuation_natCast,
      padicValNat.eq_zero_of_not_dvd (by decide : ¬(37 : ℕ) ∣ 496)]; rfl
  have hv_three : Padic.valuation ((3 : ℕ) : ℚ_[37]) = 0 := by
    rw [Padic.valuation_natCast, padicValNat.eq_zero_of_not_dvd (by decide : ¬(37 : ℕ) ∣ 3)]; rfl
  have hv_pow : Padic.valuation ((37 : ℚ_[37]) ^ 3) = 3 := by
    rw [Padic.valuation_pow]
    have hvp : Padic.valuation (37 : ℚ_[37]) = 1 := by
      rw [show (37 : ℚ_[37]) = ((37 : ℕ) : ℚ_[37]) from by norm_num, Padic.valuation_p]
    rw [hvp]; ring
  have hB30_ne : (((bernoulli 30 : ℚ) : ℚ_[37])) ≠ 0 := Rat.cast_ne_zero.mpr hB30_ne'
  have hchoose_ne : ((Nat.choose 32 2 : ℕ) : ℚ_[37]) ≠ 0 := by
    rw [show (Nat.choose 32 2 : ℕ) = 496 from rfl]; norm_num
  have hpow_ne : ((37 : ℚ_[37]) ^ 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hthree_ne : ((3 : ℕ) : ℚ_[37]) ≠ 0 := by norm_num
  have hnum_ne : (((bernoulli 30 : ℚ) : ℚ_[37]) * ((Nat.choose 32 2 : ℕ) : ℚ_[37])
      * ((37 : ℚ_[37]) ^ 3)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hB30_ne hchoose_ne) hpow_ne
  rw [div_eq_mul_inv, Padic.valuation_mul hnum_ne (inv_ne_zero hthree_ne)]
  rw [Padic.valuation_mul (mul_ne_zero hB30_ne hchoose_ne) hpow_ne]
  rw [Padic.valuation_mul hB30_ne hchoose_ne]
  rw [Padic.valuation_inv]
  rw [hv_B30, hv_choose, hv_pow, hv_three]; ring

/-- **UNCONDITIONAL sharp valuation of the power-sum at the boundary index:**

  `v₃₇(Σ_{k<37} k^32) = 2`.

This is the boundary-index analogue of `valuation_sum_units_val_pow` (the regular-
regime `v = 1` read-off), but at the boundary `v₃₇(B₃₂) = 1` where the mod-`p²`
remainder alone does not suffice.  It is obtained from the **mod-`p³`** congruence
`sum_range_pow_thirtytwo_sub_p_mul_bernoulli_cubed`: the leading term `37·B₃₂` has
valuation `2`, the remainder `32·37³·W` has valuation `≥ 3 > 2`, so by the exactness
lemma `Padic.valuation_sub_eq_of_lt` the power-sum inherits valuation exactly `2`.

**Crucially, NO Kellner / `B_{1184}` input is used** — the second-order
non-cancellation is forced by the elementary `37`-unit structure of the Faulhaber
coefficients at `h = 32` (`secondOrderFaulhaberTerm_thirtytwo_eq` +
`valuation_secondOrderFaulhaberTerm_thirtytwo`). -/
theorem power_sum_valuation_thirtytwo :
    Padic.valuation (∑ k ∈ Finset.range 37, (k : ℚ_[37]) ^ 32) = 2 := by
  haveI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  -- `v(37·B₃₂) = 2`.
  have hvp : Padic.valuation (37 : ℚ_[37]) = 1 := by
    rw [show (37 : ℚ_[37]) = ((37 : ℕ) : ℚ_[37]) from by norm_num, Padic.valuation_p]
  have hvB : Padic.valuation (((bernoulli 32 : ℚ) : ℚ_[37])) = 1 := by
    rw [Padic.valuation_ratCast]
    exact padicValRat_bernoulli_thirtytwo
  have hpQ_ne : (37 : ℚ_[37]) ≠ 0 := by norm_num
  have hBcast_ne : (((bernoulli 32 : ℚ) : ℚ_[37])) ≠ 0 :=
    Rat.cast_ne_zero.mpr (Rat.num_ne_zero.mp (by rw [bernoulli_thirtytwo_num_eq]; decide))
  set y : ℚ_[37] := (37 : ℚ_[37]) * ((bernoulli 32 : ℚ) : ℚ_[37]) with hy
  set x : ℚ_[37] := ∑ k ∈ Finset.range 37, (k : ℚ_[37]) ^ 32 with hx
  have hy0 : y ≠ 0 := mul_ne_zero hpQ_ne hBcast_ne
  have hvy : y.valuation = 2 := by
    rw [hy, Padic.valuation_mul hpQ_ne hBcast_ne, hvp, hvB]; ring
  -- mod-p³: `x − y = 32·37³·W`.
  obtain ⟨W, hW⟩ := sum_range_pow_thirtytwo_sub_p_mul_bernoulli_cubed
  have hxy_eq : x - y = (32 : ℚ_[37]) * (37 : ℚ_[37]) ^ 3 * (W : ℚ_[37]) := hW
  by_cases hWW : (W : ℚ_[37]) = 0
  · -- remainder vanishes ⟹ `x = y`, valuation 2.
    have : x = y := by rw [← sub_eq_zero, hxy_eq, hWW, mul_zero]
    rw [hx] at this ⊢; rw [this, hvy]
  · -- `v(x − y) ≥ 3`: `v(32)=0`, `v(37³)=3`, `v(W)≥0`.
    have hcong : (3 : ℤ) ≤ (x - y).valuation := by
      rw [hxy_eq]
      have h32_ne : (32 : ℚ_[37]) ≠ 0 := by norm_num
      have hp3_ne : ((37 : ℚ_[37]) ^ 3) ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [Padic.valuation_mul (mul_ne_zero h32_ne hp3_ne) hWW,
        Padic.valuation_mul h32_ne hp3_ne]
      have hv32 : Padic.valuation (32 : ℚ_[37]) = 0 := by
        rw [show (32 : ℚ_[37]) = ((32 : ℕ) : ℚ_[37]) from by norm_num, Padic.valuation_natCast,
          padicValNat.eq_zero_of_not_dvd (by decide : ¬(37 : ℕ) ∣ 32)]; rfl
      have hvp3 : Padic.valuation ((37 : ℚ_[37]) ^ 3) = 3 := by
        rw [Padic.valuation_pow, hvp]; ring
      have hvW : (0 : ℤ) ≤ (W : ℚ_[37]).valuation := PadicInt.valuation_coe_nonneg
      rw [hv32, hvp3]; omega
    rw [hx] at *
    rw [Padic.valuation_sub_eq_of_lt hy0 hcong (by rw [hvy]; norm_num), hvy]

/-- **The units power-sum has valuation 2 as well** (the only `k = 0` term dropped,
`0^32 = 0`).  This is the boundary-index strengthening of the regular-regime
`valuation_sum_units_val_pow` (`v = 1`), specialised and proved at `p = 37`,
`i = 32`, **unconditionally**.  It is the sharp `v₃₇(Σ_{j∈𝔽₃₇ˣ} (j.val)^32) = 2`
that the mod-`p³` refinement delivers; whether it feeds the `π`-graded `addVal(Λ 32)`
is a *separate* matter (see the module docstring / `LogCoeffPiOrderAtThirtytwo`). -/
theorem units_power_sum_valuation_thirtytwo :
    Padic.valuation (∑ j : (ZMod 37)ˣ, ((j : ZMod 37).val : ℚ_[37]) ^ 32) = 2 := by
  haveI : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  rw [sum_units_val_pow_eq_sum_range (by norm_num : 0 < 32)]
  exact power_sum_valuation_thirtytwo

/-! ## The smallest TRUE remaining core for the `Λ`-order (honest isolation)

The target `IntegralLogCoeffValuationAt c 32` asks for `addVal(Λ 32) = 8` in the
**ramified** ring `O`, where `Λ 32 = Σ_j c_j (ω j)^32` is the Teichmüller-twisted
log-coefficient functional with Washington's `1/n`-series coefficients `c`.  This is
the `π`-graded Stickelberger order, **not** the elementary power-sum order above:

* The naive units power-sum `Σ_j (j.val)^32`, viewed in `O`, has `addVal = (p−1)·2 =
  72`, whereas the target is `addVal(Λ 32) = 8`.  The `2i = 64` shift is the
  Gauss-sum / Teichmüller `π^i`-grading (Washington §6.2, Gross–Koblitz).
* Steps 1+2 of `LogCoeffBernoulli.lean` (`residue_logCoeffSum`, the Faulhaber bridge,
  `residue_logCoeffSum_eq_zero_of_const_residue`) discharge the mod-`𝔓` class
  (`addVal(Λ 32) ≥ 1`).  The remaining order `addVal(Λ 32) = 8` is exactly the
  Washington **Prop 8.12** single-unit `p`-adic-log valuation
  `v_p(log_p E_{32}^{(N)}) = 32/(p−1) + v_p(L_p(1, ω³²))`.

This is genuinely a **separate datum** from the elementary power-sum valuation, and
it is **not** reduced to Kellner's `NoSecondOrderIrregularPair 37 32` by the mod-`p³`
power-sum refinement: that datum (`¬ 37³ ∣ B_{1184}`) is the **Iwasawa second-order**
input governing whether `L_p(s, ω³²)` has a simple zero in the `s`-direction, and
`B_{1184}` does **not** appear in the finite Faulhaber expansion of `Σ k^32` at all.

`LogCoeffPiOrderAtThirtytwo S c` names this remaining `π`-graded core *as a Prop*
(it is exactly `IntegralLogCoeffValuationAt c 32` re-exposed at the boundary index),
recording that — at `p = 37`, `i = 32` — the elementary-arithmetic content is
discharged (`power_sum_valuation_thirtytwo`) and what remains is precisely the
Prop 8.12 `π`-adic Stickelberger order, **not** the power-sum and **not** Kellner. -/
def StickelbergerF1Setup.LogCoeffPiOrderAtThirtytwo
    (S : StickelbergerF1Setup 37) (c : (ZMod 37)ˣ → S.O) : Prop :=
  S.IntegralLogCoeffValuationAt c 32

/-- **The `Λ`-order core, re-exposed at the boundary index**: `addVal(Λ 32) = 8`
(`normVal = 2/9`) holds iff the named `π`-graded core does.  Trivial unfolding — its
purpose is to mark, in the dependency graph, that the boundary `Λ`-order is the
remaining Prop-8.12 datum, distinct from the now-discharged power-sum valuation.  Use
with `logCoeffBernoulli_target_thirtytwo` to land the `LogCoeffBernoulli` target. -/
theorem StickelbergerF1Setup.integralLogCoeffValuationAt_thirtytwo_iff_piOrder
    (S : StickelbergerF1Setup 37) (c : (ZMod 37)ˣ → S.O) :
    S.IntegralLogCoeffValuationAt c 32 ↔ S.LogCoeffPiOrderAtThirtytwo c :=
  Iff.rfl

end BernoulliRegular.FLT37.PadicL

end

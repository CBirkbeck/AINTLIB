module

public import BernoulliRegular.BernoulliGeneralized
public import Mathlib.NumberTheory.Bernoulli

/-!
# Kummer congruences — Von Staudt–Clausen + Step 2 (power-sum mod `p²`)

This module proves the `p`-adic integrality ingredients for the Kummer
congruence chain:

- **Adams' integrality** (restricted to `k < p - 1`):
  `bernoulli_div_mem_padicInt`.
- **Von Staudt–Clausen (generic case, restricted)**:
  `bernoulli_mem_padicInt_of_not_pSubOne_dvd`.
- **Faulhaber term bound** (helper): `faulhaber_term_mem_p_sq`.
- **Pre-division Step 2**: `sum_range_pow_sub_p_mul_bernoulli_weighted`.
- **Step 2** (power-sum mod `p²`): `sum_range_pow_sModEq_p_mul_bernoulli`.
- **Von Staudt–Clausen (unified, restricted)**:
  `p_mul_bernoulli_mem_padicInt_restricted`.

See the umbrella `BernoulliRegular.KummerCongruence` for the full
proof strategy and the T011/T012/T013 statements derived from these
ingredients.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

/-! ### Step 2 — Power-sum congruence `∑ a^t ≡ p · B_t (mod p²)`

This is the non-trivial elementary ingredient that, combined with
the sharper Teichmüller `ω(a) ≡ (a.val)^p (mod p²)` from Step 1,
produces the bridge T012.

**Proof outline** (Faulhaber + p-adic valuation bookkeeping, following
reviewer's clean formulation):

Faulhaber's formula (mathlib `sum_range_pow`) gives, for any `N`:
  `∑_{a=0}^{N-1} a^t = (1/(t+1)) ∑_{i=0}^{t} B_i · C(t+1, i) · N^{t+1-i}`.
Setting `N = p` and multiplying by `(t+1)` keeps everything in `ℤ_p`:
  `(t+1) · ∑_{a=0}^{p-1} a^t = ∑_{i=0}^{t} B_i · C(t+1, i) · p^{t+1-i}`.
Splitting off the `i = t` term (which is `(t+1) · p · B_t`) leaves
  `(t+1) · (∑ a^t − p · B_t) = ∑_{i=0}^{t-1} B_i · C(t+1, i) · p^{t+1-i}`.

Each `i < t` term is in `p²·ℤ_p`. Case-by-case valuation bound:

| case | `v_p(B_i · C(t+1,i) · p^{t+1-i})` |
|------|-------------------------------------|
| `i = 0`                              | `≥ t+1 ≥ 3`        (Bernoulli `1`, huge `p^{t+1}` factor) |
| `i = 1`                              | `≥ t ≥ 2`          (`v_p(−1/2) = 0` for odd `p`)          |
| odd `i ≥ 3`                          | `= ∞`              (`bernoulli i = 0`)                    |
| even `i ∈ [2, t-2]`, `(p-1) ∤ i`     | `≥ t+1-i ≥ 3`      (`v_p(B_i) ≥ 0` by vSC)                |
| even `i ∈ [2, t-2]`, `(p-1) ∣ i`     | `≥ (t+1-i)−1 ≥ 2`  (`v_p(B_i) ≥ −1` by vSC)               |
| `i = t−1 = 1` (so `t = 2`)           | `= 2`              (`B_1 = −1/2`, factor `p²`)            |

(`v_p(C(t+1,i)) ≥ 0` is automatic from the integer-valued-ness of
the binomial coefficient; no Kummer-on-binomials needed.)

So `(t+1) · (∑ a^t − p · B_t) ∈ p²·ℤ_p`. Dividing by `(t+1)` (a `p`-unit,
since `p ∤ (t+1)`) gives the claim.

Needed infrastructure:
- `Finset.sum_range_pow` (mathlib, Faulhaber). ✓
- `_root_.bernoulli_odd_eq_zero` for odd `i ≥ 3`. ✓
- `bernoulli_mem_padicInt_of_lt_sub_one` (this file, T010-era work)
  for `i < p-1`. ✓
- `p_mul_bernoulli_mem_padicInt_restricted` (this file): `p · B_k ∈ ℤ_p`
  for even `k ≥ 2` with `¬ p^3 ∣ (k+1)`. ✓ (unified vSC, proved by
  strong induction on `k`, splitting on `v_p(k+1) ∈ {0, 1, 2}`).
-/

/-! ### Generalized von Staudt–Clausen bounds (prerequisites for Step 2)

The other agent has proved `bernoulli_mem_padicInt_of_lt_sub_one` (bound
`k < p - 1`). For Step 2 we need the full valuation bounds for
arbitrary `k`. Two theorems handle this:

- `bernoulli_mem_padicInt_of_not_pSubOne_dvd`: for `k < p - 1`, `B_k ∈ ℤ_p`
  (no `(p-1) ∣ k` restriction needed in this range). Derived from the
  restricted Adams theorem `bernoulli_div_mem_padicInt` (also restricted
  to `k < p - 1`).

- `p_mul_bernoulli_mem_padicInt_restricted`: for even `k ≥ 2` with
  `¬ p^3 ∣ (k+1)`, `p · B_k ∈ ℤ_p`. Unified over `(p-1) ∣ k` (vSC
  boundary) and `(p-1) ∤ k` (vSC generic). Proved by strong induction on
  `k`, splitting on `v_p(k+1)`:

  - **Case A** (`p ∤ (k+1)`): apply Step 2 with `t = k`. Gives
    `∑ a^k - p · B_k = p² · z` in ℚ_[p]; conclude `p · B_k ∈ ℤ_p`.
  - **Case B** (`v_p(k+1) = 1`): use the pre-division form of Step 2:
    `(k+1) · (∑ a^k − p · B_k) = p² · W`. With `k+1 = p · m'`,
    `p ∤ m'`, divide by `m'` to conclude.
  - **Case B'** (`v_p(k+1) = 2`): same pre-division form. Write
    `k+1 = p² · q` with `p ∤ q`; cancel `p²`, divide by `q`.
  - **Case C** (`v_p(k+1) ≥ 3`): ruled out by the hypothesis
    `¬ p^3 ∣ (k+1)`.

The `¬ p^3 ∣ (k+1)` restriction is essentially `t + 1 < p^3`, which is
automatic for the Main theorem's pipeline (which uses `t = p·n + 1`
with `n ≤ p - 3`, so `t + 1 < p^2 < p^3`).

This unified formulation breaks the Adams → T011 → Voronoi → Faulhaber
→ Adams dependency cycle: the Faulhaber Cases 4 and 5 are merged and
use only `p · B_j ∈ ℤ_[p]` (weaker than Adams's `B_j/j ∈ ℤ_[p]`).
Adams is consequently only needed at `k < p - 1` in the Main pipeline.
-/

/-- **Adams' integrality** (Cohen Prop 9.5.23), **restricted form**: for
positive even `k < p - 1` with `(p-1) ∤ k`, `B_k/k ∈ ℤ_p`.

This is the classical Adams integrality theorem, but **restricted to
`k < p - 1`**. The unrestricted form `k ≥ p - 1 ∧ (p-1) ∤ k` is
classically true (Cohen Prop 9.5.23), but its formalisation via the
natural strong-induction-on-`k` route creates a **dependency cycle**:

  Adams(k)
    → T011 (`bernoulli_div_sModEq_of_modEq`)
    → voronoi_congruence_mod_p
    → sum_range_pow_sub_p_mul_bernoulli_weighted
    → faulhaber_term_mem_p_sq
    → vSC generic for `i < k`
    → Adams(i).

In this file we work around the cycle by inlining vSC boundary as an
explicit IH parameter in the Faulhaber chain, which unifies vSC
boundary/generic into `p_mul_bernoulli_mem_padicInt_restricted` and
breaks the cycle for the Main theorem's pipeline (which never needs
Adams at `k ≥ p - 1`). The Main theorem caller (T012) uses Adams only at
`k = n + 1 < p - 1`, where the proof goes directly via
`bernoulli_mem_padicInt_of_lt_sub_one`.

Classical textbooks (Cohen, Washington) derive the full Adams theorem
**jointly** with Kummer's congruence via the Voronoi identity; a
formalisation following that route would refactor the file so `B_k/k ∈ ℤ_[p]`
and `B_m/m ≡ B_n/n (mod p)` are extracted simultaneously from one
Voronoi lemma, avoiding the cycle entirely. That is left as future
work. -/
theorem bernoulli_div_mem_padicInt
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {k : ℕ} (hk_pos : 0 < k) (hk_small : k < p - 1) :
    ∃ z : ℤ_[p], (((bernoulli k : ℚ) / k : ℚ) : ℚ_[p]) = (z : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  -- `k < p - 1`: `B_k ∈ ℤ_p` directly, `k` is a `p`-unit.
  obtain ⟨b, hb⟩ := bernoulli_mem_padicInt_of_lt_sub_one hp_odd k hk_small
  have hk_lt_p : k < p := by omega
  have hk_unit : IsUnit ((k : ℕ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt hk_pos hk_lt_p)
  set kInv : ℤ_[p] := (hk_unit.unit⁻¹ : (ℤ_[p])ˣ).val
  have hkInv_mul : ((k : ℕ) : ℤ_[p]) * kInv = 1 := by
    change ((hk_unit.unit * hk_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1; simp
  have hkQ_ne : ((k : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hk_pos.ne'
  refine ⟨kInv * b, ?_⟩
  have hkInv_mul_Qp : ((k : ℕ) : ℚ_[p]) * ((kInv : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] ↦ (x : ℚ_[p])) hkInv_mul
  have h_div : (((bernoulli k : ℚ) / (k : ℕ) : ℚ) : ℚ_[p]) =
      ((bernoulli k : ℚ) : ℚ_[p]) / ((k : ℕ) : ℚ_[p]) := by push_cast; rfl
  rw [h_div, hb, div_eq_mul_inv, inv_eq_of_mul_eq_one_right hkInv_mul_Qp]
  push_cast; ring

/-- **Von Staudt–Clausen (generic case, restricted)**: `B_k ∈ ℤ_p` for
even `k < p - 1` with `(p-1) ∤ k`. For `k = 0`, handled as `B_0 = 1`;
for `k = 1`, `B_1 = -1/2` and `p` is odd so `1/2 ∈ ℤ_p`; for odd
`k ≥ 3`, `B_k = 0`.

Derived from restricted Adams `bernoulli_div_mem_padicInt` when `k ≥ 2`. -/
theorem bernoulli_mem_padicInt_of_not_pSubOne_dvd
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    (k : ℕ) (hk_small : k < p - 1) :
    ∃ z : ℤ_[p], (((bernoulli k : ℚ)) : ℚ_[p]) = (z : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  -- Case k = 0.
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · exact ⟨1, by simp [_root_.bernoulli_zero]⟩
  -- Case k = 1. B_1 = -1/2, which is in ℤ_p since p is odd.
  rcases eq_or_ne k 1 with rfl | hk_ne_one
  · have h2_unit : IsUnit ((2 : ℕ) : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact hp.coprime_iff_not_dvd.mpr fun h ↦
        absurd (Nat.le_of_dvd (by omega) h) (by omega)
    set w : ℤ_[p] := (h2_unit.unit⁻¹ : (ℤ_[p])ˣ).val with hw_def
    have hw_mul : ((2 : ℕ) : ℤ_[p]) * w = 1 := by
      change ((h2_unit.unit * h2_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1; simp
    have hw_mul_Qp : (2 : ℚ_[p]) * ((w : ℤ_[p]) : ℚ_[p]) = 1 := by
      have hcast : (((2 : ℕ) : ℤ_[p]) : ℚ_[p]) = (2 : ℚ_[p]) := by
        rw [PadicInt.coe_natCast]; norm_num
      rw [← hcast, ← PadicInt.coe_mul, hw_mul, PadicInt.coe_one]
    refine ⟨-w, ?_⟩
    rw [_root_.bernoulli_one]
    have h2Q_ne : (2 : ℚ_[p]) ≠ 0 := by norm_num
    refine mul_left_cancel₀ h2Q_ne ?_
    push_cast; linear_combination hw_mul_Qp
  -- Case k ≥ 2.
  have hk_ge : 2 ≤ k := by omega
  rcases Nat.even_or_odd k with hk_even | hk_odd
  swap
  · -- odd k ≥ 3: B_k = 0.
    refine ⟨0, ?_⟩
    rw [_root_.bernoulli_eq_zero_of_odd hk_odd (by omega : 1 < k)]; push_cast; ring
  -- Case k ≥ 2, even, k < p - 1: derive from restricted Adams.
  obtain ⟨b, hb⟩ :=
    bernoulli_div_mem_padicInt hp_odd hk_pos hk_small
  refine ⟨(k : ℤ_[p]) * b, ?_⟩
  -- B_k = k · (B_k / k).
  have hkQ_ne : ((k : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hk_pos.ne'
  have h_div : (((bernoulli k : ℚ) / (k : ℕ) : ℚ) : ℚ_[p]) =
      ((bernoulli k : ℚ) : ℚ_[p]) / ((k : ℕ) : ℚ_[p]) := by push_cast; rfl
  rw [h_div] at hb
  have hb' : ((bernoulli k : ℚ) : ℚ_[p]) = ((k : ℕ) : ℚ_[p]) * ((b : ℤ_[p]) : ℚ_[p]) := by
    rw [← hb, mul_div_assoc', mul_div_cancel_left₀ _ hkQ_ne]
  rw [hb']; push_cast; ring

/-- **Pointwise Faulhaber term bound** (helper for Step 2): for `i < t`
with `t` even and `t ≥ 2`, each Faulhaber summand `B_i · C(t+1, i) · p^{t+1-i}`
is in `p² · ℤ_p`.

Takes an explicit **unified** IH `ih_pB` giving `p · B_j ∈ ℤ_[p]` for every
even `2 ≤ j < t`, covering both `(p-1) ∣ j` (vSC boundary) and `(p-1) ∤ j`
(vSC generic) cases. The extra factor of `p` from the IH is absorbed by
`p^{t+1-i}` (since `t - i ≥ 2` for `i ∈ [2, t-2]`), so no separate Adams
integrality hypothesis is needed.

Case analysis:
- `i = 0`: `p^{t+1}`, `t+1 ≥ 3`.
- `i = 1`: `B_1 = −1/2` (odd `p`), factor `p^t ≥ p²`.
- odd `i ≥ 3`: `B_i = 0`.
- even `i ∈ [2, t-2]`: `p · B_i ∈ ℤ_p` **from `ih_pB`**,
  `B_i · p^{t+1-i} = (p·B_i) · p^{t-i}` with `t-i ≥ 2`.
- `i = t-1`: for `t = 2`, handled in `i = 1` case; for `t ≥ 4`, odd ≥ 3,
  `B_{t-1} = 0`. -/
lemma faulhaber_term_mem_p_sq
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {t : ℕ} (ht_two : 2 ≤ t) (ht_even : Even t)
    (ih_pB : ∀ j, j < t → 2 ≤ j → Even j →
      ∃ z : ℤ_[p], (p : ℚ_[p]) * ((bernoulli j : ℚ) : ℚ_[p]) = (z : ℚ_[p]))
    {i : ℕ} (hi : i < t) :
    ∃ z : ℤ_[p],
      ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (t + 1 - i)) =
        ((p : ℚ_[p]) ^ 2) * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  -- Case 1: i = 0. Term = 1·1·p^(t+1) = p²·p^(t-1).
  rcases Nat.eq_zero_or_pos i with rfl | hi_pos
  · refine ⟨(p : ℤ_[p]) ^ (t - 1), ?_⟩
    simp only [_root_.bernoulli_zero, Rat.cast_one, one_mul,
      Nat.choose_zero_right, Nat.cast_one]
    rw [show (t + 1 - 0 : ℕ) = 2 + (t - 1) by omega, pow_add]; push_cast; ring
  -- Case 2: i = 1. B_1 = -1/2 ∈ ℤ_[p] (odd p). Term = -(t+1)/2·p^t.
  rcases eq_or_ne i 1 with rfl | hi_ne_one
  · have h2_unit : IsUnit ((2 : ℕ) : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact hp.coprime_iff_not_dvd.mpr fun h ↦
        absurd (Nat.le_of_dvd (by omega) h) (by omega)
    set w : ℤ_[p] := (h2_unit.unit⁻¹ : (ℤ_[p])ˣ).val with hw_def
    have hw_mul : ((2 : ℕ) : ℤ_[p]) * w = 1 := by
      change ((h2_unit.unit * h2_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1; simp
    have hw_mul_Qp : (2 : ℚ_[p]) * ((w : ℤ_[p]) : ℚ_[p]) = 1 := by
      have hcast : (((2 : ℕ) : ℤ_[p]) : ℚ_[p]) = (2 : ℚ_[p]) := by
        rw [PadicInt.coe_natCast]; norm_num
      rw [← hcast, ← PadicInt.coe_mul, hw_mul, PadicInt.coe_one]
    refine ⟨-((Nat.choose (t + 1) 1 : ℤ_[p]) * w * (p : ℤ_[p]) ^ (t - 2)), ?_⟩
    rw [_root_.bernoulli_one,
      show (t + 1 - 1 : ℕ) = 2 + (t - 2) by omega, pow_add]
    have h2Q_ne : (2 : ℚ_[p]) ≠ 0 := by norm_num
    have h_half : ((-1 / 2 : ℚ) : ℚ_[p]) = -((w : ℤ_[p]) : ℚ_[p]) :=
      mul_left_cancel₀ h2Q_ne (by push_cast; linear_combination hw_mul_Qp)
    rw [h_half]; push_cast; ring
  -- i ≥ 2.
  have hi_ge : 2 ≤ i := by omega
  rcases Nat.even_or_odd i with hi_even | hi_odd
  · -- Case 4/5 (unified): i even, 2 ≤ i ≤ t - 2. Use `p · B_i ∈ ℤ_[p]` (IH).
    have hi_le : i ≤ t - 2 := by
      rcases hi_even with ⟨k, hk⟩; rcases ht_even with ⟨m, hm⟩; omega
    obtain ⟨c, hc⟩ := ih_pB i hi hi_ge hi_even
    refine ⟨c * (Nat.choose (t + 1) i : ℤ_[p]) * (p : ℤ_[p]) ^ (t - i - 2), ?_⟩
    rw [show t + 1 - i = 1 + (t - i - 2) + 2 from by omega,
      show (p : ℚ_[p]) ^ (1 + (t - i - 2) + 2) =
        (p : ℚ_[p]) * (p : ℚ_[p]) ^ (t - i - 2) * (p : ℚ_[p]) ^ 2 from by
        rw [pow_add, pow_add]; ring]
    have hbc : ((bernoulli i : ℚ) : ℚ_[p]) * ((p : ℚ_[p])) = ((c : ℤ_[p]) : ℚ_[p]) := by
      rw [← hc]; ring
    push_cast
    linear_combination
      (((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) * ((p : ℚ_[p]) ^ (t - i - 2)) *
        ((p : ℚ_[p]) ^ 2)) * hbc
  · -- Case 3: i odd, i ≥ 3 ⟹ B_i = 0.
    refine ⟨0, ?_⟩
    have hi_gt : 1 < i := by omega
    rw [bernoulli_eq_zero_of_odd hi_odd hi_gt]; push_cast; ring

/-- **Pre-division Step 2**: the `(t+1)`-weighted Faulhaber identity for
`∑ a^t − p · B_t`. This is the intermediate form used in both:
- `sum_range_pow_sModEq_p_mul_bernoulli` (Step 2 proper, after dividing
  by `(t+1)` when `p ∤ (t+1)`);
- `p_mul_bernoulli_mem_padicInt_restricted` Case B (when
  `v_p(t+1) = 1`, where dividing by `(t+1)/p` still lands in `ℤ_p`).

Takes a unified IH `ih_pB` giving `p · B_j ∈ ℤ_[p]` for all even
`2 ≤ j < t`. -/
theorem sum_range_pow_sub_p_mul_bernoulli_weighted
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {t : ℕ} (ht_two : 2 ≤ t) (ht_even : Even t)
    (ih_pB : ∀ j, j < t → 2 ≤ j → Even j →
      ∃ z : ℤ_[p], (p : ℚ_[p]) * ((bernoulli j : ℚ) : ℚ_[p]) = (z : ℚ_[p])) :
    ∃ W : ℤ_[p],
      ((t + 1 : ℕ) : ℚ_[p]) *
          ((∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t) -
            (p : ℚ_[p]) * ((bernoulli t : ℚ) : ℚ_[p])) =
        ((p : ℚ_[p]) ^ 2) * ((W : ℤ_[p]) : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  -- Per-`i` witness from `faulhaber_term_mem_p_sq` (threading the IH through).
  choose w hw using (fun (i : ℕ) (hi : i < t) ↦
    faulhaber_term_mem_p_sq hp_odd ht_two ht_even ih_pB hi)
  -- Set witness `W : ℤ_[p]` = ∑ w_i.
  set W : ℤ_[p] :=
    ∑ i ∈ Finset.attach (Finset.range t), w i.1 (Finset.mem_range.mp i.2) with hW_def
  refine ⟨W, ?_⟩
  -- Faulhaber in ℚ, multiplied by (t+1).
  have h_faulhaber_Q : ((t + 1 : ℚ)) * (∑ k ∈ Finset.range p, (k : ℚ) ^ t) =
      ∑ i ∈ Finset.range (t + 1),
        bernoulli i * (Nat.choose (t + 1) i : ℚ) * (p : ℚ) ^ (t + 1 - i) := by
    rw [sum_range_pow p t, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have htp1Q_ne : (((t + 1 : ℕ)) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  -- Cast to ℚ_[p].
  have h_faulhaber_Qp : ((t + 1 : ℕ) : ℚ_[p]) * (∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t) =
      ∑ i ∈ Finset.range (t + 1),
        ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p])) ^ (t + 1 - i) := by
    have := congrArg (fun q : ℚ ↦ (q : ℚ_[p])) h_faulhaber_Q
    push_cast at this; push_cast; exact this
  -- Split off i = t: the term is `B_t · (t+1) · p`.
  have h_split_sum : ((t + 1 : ℕ) : ℚ_[p]) * (∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t) -
        ((t + 1 : ℕ) : ℚ_[p]) * ((p : ℚ_[p])) * ((bernoulli t : ℚ) : ℚ_[p]) =
      ∑ i ∈ Finset.range t,
        ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p])) ^ (t + 1 - i) := by
    rw [h_faulhaber_Qp, Finset.sum_range_succ, Nat.choose_succ_self_right t,
      show (t + 1 - t : ℕ) = 1 from by omega]
    push_cast; ring
  -- The RHS sum equals `p² · W` using `faulhaber_term_mem_p_sq` for each `i`.
  have h_rhs_eq : (∑ i ∈ Finset.range t,
        ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p])) ^ (t + 1 - i)) =
      ((p : ℚ_[p])) ^ 2 * ((W : ℤ_[p]) : ℚ_[p]) := by
    rw [← Finset.sum_attach]
    rw [show (((p : ℚ_[p])) ^ 2 * ((W : ℤ_[p]) : ℚ_[p])) =
        ∑ i ∈ Finset.attach (Finset.range t),
          ((p : ℚ_[p])) ^ 2 * ((w i.1 (Finset.mem_range.mp i.2) : ℤ_[p]) : ℚ_[p]) from ?_]
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      exact hw i.1 (Finset.mem_range.mp i.2)
    · rw [hW_def]
      simp [PadicInt.coe_sum, Finset.mul_sum]
  rw [mul_sub, ← h_rhs_eq, ← h_split_sum]; push_cast; ring

/-- **Step 2** (needed for T012): for an odd prime `p` and even `t ≥ 2`
with `p ∤ (t+1)`, the power sum `∑_{a=0}^{p-1} a^t` is congruent to
`p · B_t` modulo `p²` (viewed in `ℚ_[p]`, with the difference a `p`-adic
integer times `p²`).

Note: the statement does *not* require `(p-1) ∤ t`. It also applies when
`(p-1) ∣ t`, in which case Fermat gives `∑ a^t ≡ -1 (mod p)` and the
conclusion becomes `p · B_t ≡ -1 (mod p)`, i.e., `B_t + 1/p ∈ ℤ_p`
(von Staudt–Clausen boundary). In that case the extra `p` comes from
the sum's congruence, not from assumptions on `t`.

Derived from the pre-division form `sum_range_pow_sub_p_mul_bernoulli_weighted`
by dividing by `(t+1)` (a `p`-unit when `p ∤ (t+1)`). -/
theorem sum_range_pow_sModEq_p_mul_bernoulli
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {t : ℕ} (ht_two : 2 ≤ t) (ht_even : Even t)
    (h_p_not_dvd_t_plus_one : ¬ (p : ℕ) ∣ (t + 1))
    (ih_pB : ∀ j, j < t → 2 ≤ j → Even j →
      ∃ z : ℤ_[p], (p : ℚ_[p]) * ((bernoulli j : ℚ) : ℚ_[p]) = (z : ℚ_[p])) :
    ∃ z : ℤ_[p],
      ((∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t)) -
          (p : ℚ_[p]) * ((bernoulli t : ℚ) : ℚ_[p]) =
        ((p : ℚ_[p]) ^ 2) * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  -- `(t+1)` is a p-unit.
  have htp1_unit : IsUnit ((t + 1 : ℕ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr h_p_not_dvd_t_plus_one
  set u : ℤ_[p] := (htp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val with hu_def
  have hu_mul : ((t + 1 : ℕ) : ℤ_[p]) * u = 1 := by
    change ((htp1_unit.unit * htp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1; simp
  have hu_mul_Qp : ((t + 1 : ℕ) : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] ↦ (x : ℚ_[p])) hu_mul
  obtain ⟨W, hW⟩ := sum_range_pow_sub_p_mul_bernoulli_weighted hp_odd ht_two ht_even ih_pB
  refine ⟨u * W, ?_⟩
  -- Multiply hW by u to divide out (t+1).
  have : ((u : ℤ_[p]) : ℚ_[p]) *
      (((t + 1 : ℕ) : ℚ_[p]) *
        ((∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t) -
          (p : ℚ_[p]) * ((bernoulli t : ℚ) : ℚ_[p]))) =
      ((u : ℤ_[p]) : ℚ_[p]) * ((p : ℚ_[p]) ^ 2 * ((W : ℤ_[p]) : ℚ_[p])) := by
    rw [hW]
  push_cast
  linear_combination this - ((∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t) -
    (p : ℚ_[p]) * ((bernoulli t : ℚ) : ℚ_[p])) * hu_mul_Qp

/-- **Von Staudt–Clausen (unified, restricted to `v_p(k+1) ≤ 2`)**: for
every even `k ≥ 2` with `¬ p^3 ∣ (k+1)` we have `p · B_k ∈ ℤ_[p]`. This
subsumes both the classical boundary case `(p-1) ∣ k` (where the naive
statement `B_k ∈ ℤ_[p]` fails) and the generic case `(p-1) ∤ k` (where
the stronger `B_k ∈ ℤ_[p]` is known; multiplying by `p` still holds).
The extra factor of `p` absorbs the potential pole in `B_k`.

**Proof structure** (strong induction on `k`, split on `v_p(k+1)`):
- **Case A** (`p ∤ (k+1)`): apply Step 2
  (`sum_range_pow_sModEq_p_mul_bernoulli`) with `t = k`, using the IH
  for `i < k`. Step 2 gives `∑ a^k − p · B_k = p² · z`; since
  `∑ a^k ∈ ℤ ⊂ ℤ_p`, conclude `p · B_k ∈ ℤ_p`.
- **Case B** (`v_p(k+1) = 1`): use the pre-division form
  `sum_range_pow_sub_p_mul_bernoulli_weighted`: `(k+1) · (∑ a^k − p · B_k)
  = p² · W`. Write `k+1 = p · m'` with `p ∤ m'`; divide by `p`, then by
  `m'` (a `p`-unit), to conclude.
- **Case B'** (`v_p(k+1) = 2`): same pre-division form. Write
  `k+1 = p² · q` with `p ∤ q`; cancel `p²`, divide by `q`.
- **Case C** (`v_p(k+1) ≥ 3`): ruled out by the `h_not_pCube` hypothesis.

**Reachability note**: For the main theorem application via
`bernoulliGen_teichmuller_pow_sModEq_div` (T012), Step 2 is invoked with
`t = p·n + 1` where `n ∈ [1, p-4]` (odd). So `t ≤ p² − 4p + 1 < p²`, and
the recursive calls involve `j < t < p²`, giving `v_p(j+1) ≤ 1`. Cases A
and B suffice; Case C is unreachable for the Main theorem, which is why
we restrict the statement rather than prove full generality.

The unified formulation (no `(p-1) ∣ k` hypothesis) lets us also replace
the Adams-derived `B_i ∈ ℤ_[p]` in `faulhaber_term_mem_p_sq` Case 4,
breaking the Adams → T011 → Voronoi → Faulhaber → Adams dependency
cycle that otherwise blocks Adams's `k ≥ p - 1` branch. -/
theorem p_mul_bernoulli_mem_padicInt_restricted
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {k : ℕ} (hk_two : 2 ≤ k) (hk_even : Even k)
    (h_below : ∀ j, j ≤ k → ¬ (p : ℕ) ^ 3 ∣ (j + 1)) :
    ∃ z : ℤ_[p], (p : ℚ_[p]) * (((bernoulli k : ℚ)) : ℚ_[p]) = (z : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  have hpQ_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.ne_zero
  -- Strong induction on k. Revert hypotheses to make them universally quantified over k.
  revert hk_two hk_even h_below
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk_two hk_even h_below
    -- `ih : ∀ m < k, 2 ≤ m → Even m → (∀ j ≤ m, ¬ p^3 ∣ (j+1)) → ∃ z, p · B_m = z`.
    -- IH for `faulhaber_term_mem_p_sq`: `∀ j < k, 2 ≤ j → Even j → ∃ z, p · B_j = z`.
    have ih_pB : ∀ j, j < k → 2 ≤ j → Even j →
        ∃ z : ℤ_[p], (p : ℚ_[p]) * ((bernoulli j : ℚ) : ℚ_[p]) = (z : ℚ_[p]) := by
      intro j hj hj_two hj_even
      exact ih j hj hj_two hj_even (fun j' hj' ↦ h_below j' (Nat.le_trans hj' hj.le))
    -- Main hypothesis: `¬ p^3 ∣ (k+1)`.
    have h_not_pCube : ¬ (p : ℕ) ^ 3 ∣ (k + 1) := h_below k (le_refl k)
    -- Shared: S_nat := ∑ j^k, cast lemma.
    set S_nat : ℕ := ∑ j ∈ Finset.range p, j ^ k with hS_def
    have hS_cast : (∑ j ∈ Finset.range p, (j : ℚ_[p]) ^ k) = ((S_nat : ℕ) : ℚ_[p]) := by
      simp only [hS_def]; push_cast; rfl
    by_cases h_p_dvd : (p : ℕ) ∣ (k + 1)
    · -- `p | (k+1)`. Split further on `v_p(k+1)`.
      by_cases h_p_sq : (p : ℕ) ^ 2 ∣ (k + 1)
      · -- `v_p(k+1) ≥ 2`. Since `¬ p^3 ∣ (k+1)`, must have `v_p(k+1) = 2`.
        -- Case B' : k+1 = p² · q, p ∤ q.
        obtain ⟨q, hq⟩ := h_p_sq
        have hq_coprime : ¬ (p : ℕ) ∣ q := by
          intro hdvd
          apply h_not_pCube
          rw [hq, pow_succ]
          exact mul_dvd_mul_left (p ^ 2) hdvd
        have hq_unit : IsUnit ((q : ℕ) : ℤ_[p]) := by
          rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
          exact hp.coprime_iff_not_dvd.mpr hq_coprime
        set qInv : ℤ_[p] := (hq_unit.unit⁻¹ : (ℤ_[p])ˣ).val
        have hqInv_mul : ((q : ℕ) : ℤ_[p]) * qInv = 1 := by
          change ((hq_unit.unit * hq_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1; simp
        have hqInv_mul_Qp : ((q : ℕ) : ℚ_[p]) * ((qInv : ℤ_[p]) : ℚ_[p]) = 1 := by
          simpa using congrArg (fun x : ℤ_[p] ↦ (x : ℚ_[p])) hqInv_mul
        obtain ⟨W, hW⟩ := sum_range_pow_sub_p_mul_bernoulli_weighted hp_odd hk_two hk_even ih_pB
        have h_kp1_eq : ((k + 1 : ℕ) : ℚ_[p]) = (p : ℚ_[p])^2 * ((q : ℕ) : ℚ_[p]) := by
          have : (k + 1 : ℕ) = p^2 * q := hq
          push_cast [this]; ring
        rw [h_kp1_eq] at hW
        -- p² · q · X = p² · W, cancel p²: q · X = W.
        have hp_sq_ne : (p : ℚ_[p])^2 ≠ 0 := pow_ne_zero 2 hpQ_ne
        have hW'' : ((q : ℕ) : ℚ_[p]) *
            ((∑ k' ∈ Finset.range p, (k' : ℚ_[p]) ^ k) -
              (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p])) =
            ((W : ℤ_[p]) : ℚ_[p]) :=
          mul_left_cancel₀ hp_sq_ne (by linear_combination hW)
        -- Multiply by qInv: X = qInv · W.
        have h_sub : ((∑ k' ∈ Finset.range p, (k' : ℚ_[p]) ^ k) -
              (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p])) =
            ((qInv : ℤ_[p]) : ℚ_[p]) * ((W : ℤ_[p]) : ℚ_[p]) := by
          linear_combination ((qInv : ℤ_[p]) : ℚ_[p]) * hW'' -
            (((∑ k' ∈ Finset.range p, (k' : ℚ_[p]) ^ k) -
              (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p]))) * hqInv_mul_Qp
        rw [hS_cast] at h_sub
        refine ⟨(S_nat : ℤ_[p]) - qInv * W, ?_⟩
        have h_rearr : (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p]) =
            ((S_nat : ℕ) : ℚ_[p]) - ((qInv : ℤ_[p]) : ℚ_[p]) * ((W : ℤ_[p]) : ℚ_[p]) := by
          linear_combination -h_sub
        rw [h_rearr]; push_cast; ring
      · -- Case B: `v_p(k+1) = 1`. Use pre-division form.
        obtain ⟨m', hm'⟩ := h_p_dvd
        have hm'_coprime : ¬ (p : ℕ) ∣ m' := by
          intro hdvd
          apply h_p_sq
          rw [hm', pow_two]
          exact mul_dvd_mul_left p hdvd
        have hm'_unit : IsUnit ((m' : ℕ) : ℤ_[p]) := by
          rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
          exact hp.coprime_iff_not_dvd.mpr hm'_coprime
        set mInv : ℤ_[p] := (hm'_unit.unit⁻¹ : (ℤ_[p])ˣ).val
        have hmInv_mul : ((m' : ℕ) : ℤ_[p]) * mInv = 1 := by
          change ((hm'_unit.unit * hm'_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1; simp
        have hmInv_mul_Qp : ((m' : ℕ) : ℚ_[p]) * ((mInv : ℤ_[p]) : ℚ_[p]) = 1 := by
          simpa using congrArg (fun x : ℤ_[p] ↦ (x : ℚ_[p])) hmInv_mul
        -- Pre-division form.
        obtain ⟨W, hW⟩ := sum_range_pow_sub_p_mul_bernoulli_weighted hp_odd hk_two hk_even ih_pB
        -- Rewrite (k + 1) = p * m'.
        have h_kp1_eq : ((k + 1 : ℕ) : ℚ_[p]) = (p : ℚ_[p]) * ((m' : ℕ) : ℚ_[p]) := by
          have : (k + 1 : ℕ) = p * m' := hm'
          push_cast [this]; ring
        rw [h_kp1_eq] at hW
        -- Divide by p: m' · (∑ a^k - p · B_k) = p · W.
        have hW'' : ((m' : ℕ) : ℚ_[p]) *
            ((∑ k' ∈ Finset.range p, (k' : ℚ_[p]) ^ k) -
              (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p])) =
            (p : ℚ_[p]) * ((W : ℤ_[p]) : ℚ_[p]) :=
          mul_left_cancel₀ hpQ_ne (by linear_combination hW)
        -- Multiply by mInv: (∑ a^k - p · B_k) = mInv · (p · W).
        have h_sub : ((∑ k' ∈ Finset.range p, (k' : ℚ_[p]) ^ k) -
              (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p])) =
            ((mInv : ℤ_[p]) : ℚ_[p]) * ((p : ℚ_[p]) * ((W : ℤ_[p]) : ℚ_[p])) := by
          linear_combination ((mInv : ℤ_[p]) : ℚ_[p]) * hW'' -
            (((∑ k' ∈ Finset.range p, (k' : ℚ_[p]) ^ k) -
              (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p]))) * hmInv_mul_Qp
        rw [hS_cast] at h_sub
        refine ⟨(S_nat : ℤ_[p]) - mInv * (p : ℤ_[p]) * W, ?_⟩
        have h_rearr : (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p]) =
            ((S_nat : ℕ) : ℚ_[p]) - ((mInv : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) *
              ((W : ℤ_[p]) : ℚ_[p]) := by
          linear_combination -h_sub
        rw [h_rearr]; push_cast; ring
    · -- Case A: `p ∤ (k+1)`, apply Step 2.
      obtain ⟨w, hw⟩ :=
        sum_range_pow_sModEq_p_mul_bernoulli hp_odd hk_two hk_even h_p_dvd ih_pB
      -- hw : ∑ a^k − p · B_k = p² · w.
      rw [hS_cast] at hw
      refine ⟨(S_nat : ℤ_[p]) - (p : ℤ_[p]) ^ 2 * w, ?_⟩
      have h_rearr : (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p]) =
          ((S_nat : ℕ) : ℚ_[p]) - (p : ℚ_[p]) ^ 2 * ((w : ℤ_[p]) : ℚ_[p]) := by
        linear_combination -hw
      rw [h_rearr]; push_cast; ring

end BernoulliRegular

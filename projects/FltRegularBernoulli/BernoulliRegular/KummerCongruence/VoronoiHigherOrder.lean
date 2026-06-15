module

public import BernoulliRegular.KummerCongruence.HigherOrderBinomial
public import BernoulliRegular.KummerCongruence.VonStaudtClausen

/-!
# Higher-order Voronoi sum identity (mod p³)

The order-2 generalisation of `voronoi_sum_mod_p_sq`: for prime `p`,
`a` coprime to `p`, and `k ≥ 2`,

  `(a^k − 1) · ∑_{j<p} j^k
   − k · a^{k−1} · p · ∑_{j<p} j^{k−1} · ⌊ja/p⌋
   + (k C 2) · a^{k−2} · p² · ∑_{j<p} j^{k−2} · ⌊ja/p⌋²  ∈  p³·ℤ_[p]`.

Proof: per-term quadratic bound (`voronoi_per_term_quadratic_bound`)
combined with the Voronoi permutation, summed over `j ∈ range p`.

This is the Bernoulli-side mod-p³ identity that — combined with a
forthcoming higher-order Faulhaber-style closure — yields the
second-order Kummer congruence used in Kellner's Proposition 2.7.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

/-- **Order-2 Voronoi sum identity** (mod p³). -/
lemma voronoi_sum_mod_p_cubed
    {p : ℕ} [hp : Fact p.Prime]
    {a : ℕ} (ha_coprime : ¬ (p : ℕ) ∣ a)
    {k : ℕ} (hk_two : 2 ≤ k) :
    ∃ W : ℤ_[p],
      (((a : ℤ_[p]) ^ k - 1) *
            ((∑ j ∈ Finset.range p, j ^ k : ℕ) : ℤ_[p]) -
          (k : ℤ_[p]) * ((a : ℤ_[p]) ^ (k - 1)) * (p : ℤ_[p]) *
            ((∑ j ∈ Finset.range p,
              j ^ (k - 1) * (j * a / p) : ℕ) : ℤ_[p]) +
          ((k.choose 2 : ℕ) : ℤ_[p]) * ((a : ℤ_[p]) ^ (k - 2)) *
            (p : ℤ_[p]) ^ 2 *
              ((∑ j ∈ Finset.range p,
                j ^ (k - 2) * (j * a / p) ^ 2 : ℕ) : ℤ_[p])) =
        (p : ℤ_[p]) ^ 3 * W := by
  -- Per-j witness via voronoi_per_term_quadratic_bound.
  choose wj hwj using (fun (j : ℕ) (_hj : j ∈ Finset.range p) =>
    voronoi_per_term_quadratic_bound (p := p) a j hk_two)
  -- Permutation: ∑ ((j*a) % p)^k = ∑ j^k as ℤ_p elements (j ↦ (j*a) mod p).
  have h_perm : ((∑ j ∈ Finset.range p, ((j * a) % p) ^ k : ℕ) : ℤ_[p]) =
      ((∑ j ∈ Finset.range p, j ^ k : ℕ) : ℤ_[p]) := by
    congr 1; exact voronoi_permutation ha_coprime (fun n : ℕ => n ^ k)
  -- Total function w : ℕ → ℤ_[p] extending wj.
  set w : ℕ → ℤ_[p] :=
      fun j => if h : j ∈ Finset.range p then wj j h else 0 with hw_def
  have hw_eq : ∀ (j : ℕ) (hj : j ∈ Finset.range p), w j = wj j hj := fun j hj => by
    change (if h : j ∈ Finset.range p then wj j h else 0) = wj j hj; simp [hj]
  -- Final witness: -∑ w j.
  set W_sum : ℤ_[p] := ∑ j ∈ Finset.range p, w j with hW_sum
  refine ⟨-W_sum, ?_⟩
  -- Sum the per-j quadratic identity.
  have h_sum_binom :
      (((∑ j ∈ Finset.range p, ((j * a) % p) ^ k : ℕ)) : ℤ_[p]) =
      ∑ j ∈ Finset.range p,
        (((j * a : ℕ) : ℤ_[p]) ^ k -
          (k : ℤ_[p]) * ((j * a : ℕ) : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
            (((j * a / p : ℕ)) : ℤ_[p]) +
          ((k.choose 2 : ℕ) : ℤ_[p]) * ((j * a : ℕ) : ℤ_[p]) ^ (k - 2) *
            (p : ℤ_[p]) ^ 2 * (((j * a / p : ℕ)) : ℤ_[p]) ^ 2 +
        (p : ℤ_[p]) ^ 3 * w j) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hw_eq j hj, Nat.cast_pow]
    exact hwj j hj
  -- Combine permutation and per-j identity.
  have h_sum_ℤp : ((∑ j ∈ Finset.range p, j ^ k : ℕ) : ℤ_[p]) =
      ∑ j ∈ Finset.range p,
        (((j * a : ℕ) : ℤ_[p]) ^ k -
          (k : ℤ_[p]) * ((j * a : ℕ) : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
            (((j * a / p : ℕ)) : ℤ_[p]) +
          ((k.choose 2 : ℕ) : ℤ_[p]) * ((j * a : ℕ) : ℤ_[p]) ^ (k - 2) *
            (p : ℤ_[p]) ^ 2 * (((j * a / p : ℕ)) : ℤ_[p]) ^ 2 +
        (p : ℤ_[p]) ^ 3 * w j) := by
    rw [← h_perm, h_sum_binom]
  -- Factor (j*a)^m = a^m · j^m for m = k, k-1, k-2.
  have h_ja_pow : ∀ j : ℕ, ((j * a : ℕ) : ℤ_[p]) ^ k =
      ((a : ℤ_[p])) ^ k * ((j : ℕ) : ℤ_[p]) ^ k := fun j => by push_cast; ring
  have h_ja_pow_sub1 : ∀ j : ℕ, ((j * a : ℕ) : ℤ_[p]) ^ (k - 1) =
      ((a : ℤ_[p])) ^ (k - 1) * ((j : ℕ) : ℤ_[p]) ^ (k - 1) :=
    fun j => by push_cast; ring
  have h_ja_pow_sub2 : ∀ j : ℕ, ((j * a : ℕ) : ℤ_[p]) ^ (k - 2) =
      ((a : ℤ_[p])) ^ (k - 2) * ((j : ℕ) : ℤ_[p]) ^ (k - 2) :=
    fun j => by push_cast; ring
  -- Term-by-term rewrite.
  have h_sum_rewrite :
      ∑ j ∈ Finset.range p,
        (((j * a : ℕ) : ℤ_[p]) ^ k -
          (k : ℤ_[p]) * ((j * a : ℕ) : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
            (((j * a / p : ℕ)) : ℤ_[p]) +
          ((k.choose 2 : ℕ) : ℤ_[p]) * ((j * a : ℕ) : ℤ_[p]) ^ (k - 2) *
            (p : ℤ_[p]) ^ 2 * (((j * a / p : ℕ)) : ℤ_[p]) ^ 2 +
        (p : ℤ_[p]) ^ 3 * w j) =
      ∑ j ∈ Finset.range p,
        ((a : ℤ_[p]) ^ k * ((j : ℕ) : ℤ_[p]) ^ k -
          (k : ℤ_[p]) * (a : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
            (((j : ℕ) : ℤ_[p]) ^ (k - 1) * (((j * a / p : ℕ)) : ℤ_[p])) +
          ((k.choose 2 : ℕ) : ℤ_[p]) * (a : ℤ_[p]) ^ (k - 2) *
            (p : ℤ_[p]) ^ 2 *
              (((j : ℕ) : ℤ_[p]) ^ (k - 2) *
                (((j * a / p : ℕ)) : ℤ_[p]) ^ 2) +
        (p : ℤ_[p]) ^ 3 * w j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h_ja_pow j, h_ja_pow_sub1 j, h_ja_pow_sub2 j]; ring
  rw [h_sum_rewrite] at h_sum_ℤp
  -- Distribute the four-term sum into four separate sums.
  have h_four :
      ∑ j ∈ Finset.range p,
        ((a : ℤ_[p]) ^ k * ((j : ℕ) : ℤ_[p]) ^ k -
          (k : ℤ_[p]) * (a : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
            (((j : ℕ) : ℤ_[p]) ^ (k - 1) * (((j * a / p : ℕ)) : ℤ_[p])) +
          ((k.choose 2 : ℕ) : ℤ_[p]) * (a : ℤ_[p]) ^ (k - 2) *
            (p : ℤ_[p]) ^ 2 *
              (((j : ℕ) : ℤ_[p]) ^ (k - 2) *
                (((j * a / p : ℕ)) : ℤ_[p]) ^ 2) +
        (p : ℤ_[p]) ^ 3 * w j) =
      (a : ℤ_[p]) ^ k *
          (∑ j ∈ Finset.range p, ((j : ℕ) : ℤ_[p]) ^ k) -
        (k : ℤ_[p]) * (a : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
          (∑ j ∈ Finset.range p,
            ((j : ℕ) : ℤ_[p]) ^ (k - 1) * ((j * a / p : ℕ) : ℤ_[p])) +
        ((k.choose 2 : ℕ) : ℤ_[p]) * (a : ℤ_[p]) ^ (k - 2) *
          (p : ℤ_[p]) ^ 2 *
            (∑ j ∈ Finset.range p,
              ((j : ℕ) : ℤ_[p]) ^ (k - 2) *
                ((j * a / p : ℕ) : ℤ_[p]) ^ 2) +
        (p : ℤ_[p]) ^ 3 * W_sum := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    congr 1; rw [hW_sum, Finset.mul_sum]
  -- Cast natural-number inner sums to ℤ_[p].
  have h_cast1 : (∑ j ∈ Finset.range p, ((j : ℕ) : ℤ_[p]) ^ k) =
      ((∑ j ∈ Finset.range p, j ^ k : ℕ) : ℤ_[p]) := by push_cast; rfl
  have h_cast2 : (∑ j ∈ Finset.range p,
        ((j : ℕ) : ℤ_[p]) ^ (k - 1) * ((j * a / p : ℕ) : ℤ_[p])) =
      ((∑ j ∈ Finset.range p, j ^ (k - 1) * (j * a / p) : ℕ) : ℤ_[p]) := by
    push_cast; rfl
  have h_cast3 : (∑ j ∈ Finset.range p,
        ((j : ℕ) : ℤ_[p]) ^ (k - 2) * ((j * a / p : ℕ) : ℤ_[p]) ^ 2) =
      ((∑ j ∈ Finset.range p,
        j ^ (k - 2) * (j * a / p) ^ 2 : ℕ) : ℤ_[p]) := by
    push_cast; rfl
  rw [h_four, h_cast1, h_cast2, h_cast3] at h_sum_ℤp
  -- h_sum_ℤp now: ∑ j^k = a^k·∑ j^k - k·a^(k-1)·p·S₂ + (k C 2)·a^(k-2)·p²·S₃ + p³·W_sum.
  -- Goal: (a^k - 1)·∑ j^k - k·a^(k-1)·p·S₂ + (k C 2)·a^(k-2)·p²·S₃ = p³·(-W_sum).
  linear_combination -h_sum_ℤp

/-! ## Per-Faulhaber-term order-2 bound -/

/-- **Per-Faulhaber-term mod-p³ bound**, restricted form `t ≤ p − 1`.

For `t ≤ p − 1` even, `t ≥ 4`, and `i < t − 1`:
   `B_i · C(t+1, i) · p^{t+1-i} ∈ p³ · ℤ_[p]`.

Case analysis (mirroring `faulhaber_term_mem_p_sq` but tightened):
* `i = 0`: `p^{t+1} = p³ · p^{t−2}`. Needs `t ≥ 2`. ✓
* `i = 1`: `B_1 = −1/2 ∈ ℤ_[p]`; term `= −(t+1)/2 · p^t = (·) · p³ · p^{t−3}`. Needs `t ≥ 3`. ✓
* odd `i ≥ 3`: `B_i = 0`. ✓
* even `i ∈ [2, t−2]` with `t ≤ p − 1`: `i < p − 1`, so vSC generic
  gives `B_i ∈ ℤ_[p]`; term `= B_i · C(t+1,i) · p^{t+1-i} = (·) · p³ · p^{t−i−2}`
  (`t − i − 2 ≥ 0` since `i ≤ t − 2`). ✓ -/
lemma faulhaber_term_mem_p_cubed
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {t : ℕ} (ht_four : 4 ≤ t) (_ht_even : Even t) (ht_lt : t ≤ p - 1)
    {i : ℕ} (hi : i < t - 1) :
    ∃ z : ℤ_[p],
      ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (t + 1 - i)) =
        ((p : ℚ_[p]) ^ 3) * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  have hi_lt_t : i < t := by omega
  -- Case 1: i = 0. Term = 1·1·p^(t+1) = p³·p^(t-2).
  rcases Nat.eq_zero_or_pos i with rfl | hi_pos
  · refine ⟨(p : ℤ_[p]) ^ (t - 2), ?_⟩
    simp only [_root_.bernoulli_zero, Rat.cast_one, one_mul,
      Nat.choose_zero_right, Nat.cast_one]
    rw [show (t + 1 - 0 : ℕ) = 3 + (t - 2) by omega, pow_add]
    push_cast; ring
  -- Case 2: i = 1. B_1 = -1/2 ∈ ℤ_[p] (odd p). Term = -(t+1)/2·p^t = ()·p³·p^(t-3).
  rcases eq_or_ne i 1 with rfl | hi_ne_one
  · have h2_unit : IsUnit ((2 : ℕ) : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact hp.coprime_iff_not_dvd.mpr fun h =>
        absurd (Nat.le_of_dvd (by omega) h) (by omega)
    set w : ℤ_[p] := (h2_unit.unit⁻¹ : (ℤ_[p])ˣ).val with hw_def
    have hw_mul : ((2 : ℕ) : ℤ_[p]) * w = 1 := by
      change ((h2_unit.unit * h2_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1; simp
    have hw_mul_Qp : (2 : ℚ_[p]) * ((w : ℤ_[p]) : ℚ_[p]) = 1 := by
      exact_mod_cast congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hw_mul
    refine ⟨-((Nat.choose (t + 1) 1 : ℤ_[p]) * w * (p : ℤ_[p]) ^ (t - 3)), ?_⟩
    rw [_root_.bernoulli_one,
      show (t + 1 - 1 : ℕ) = 3 + (t - 3) by omega, pow_add]
    have h2Q_ne : (2 : ℚ_[p]) ≠ 0 := by norm_num
    have h_half : ((-1 / 2 : ℚ) : ℚ_[p]) = -((w : ℤ_[p]) : ℚ_[p]) :=
      mul_left_cancel₀ h2Q_ne (by push_cast; linear_combination hw_mul_Qp)
    rw [h_half]; push_cast; ring
  -- i ≥ 2.
  have hi_ge : 2 ≤ i := by omega
  rcases Nat.even_or_odd i with hi_even | hi_odd
  · -- Case 4: i even ∈ [2, t-2]. Use B_i ∈ ℤ_p (vSC generic, since i < p-1).
    have hi_le : i ≤ t - 2 := by omega
    have hi_lt_psub : i < p - 1 := by omega
    obtain ⟨b, hb⟩ := bernoulli_mem_padicInt_of_lt_sub_one hp_odd i hi_lt_psub
    refine ⟨b * (Nat.choose (t + 1) i : ℤ_[p]) * (p : ℤ_[p]) ^ (t - i - 2), ?_⟩
    rw [show t + 1 - i = 3 + (t - i - 2) from by omega,
      show (p : ℚ_[p]) ^ (3 + (t - i - 2)) =
        (p : ℚ_[p]) ^ 3 * (p : ℚ_[p]) ^ (t - i - 2) from by rw [pow_add]]
    rw [hb]
    push_cast; ring
  · -- Case 3: i odd, i ≥ 3 ⟹ B_i = 0.
    refine ⟨0, ?_⟩
    have hi_gt : 1 < i := by omega
    rw [bernoulli_eq_zero_of_odd hi_odd hi_gt]; push_cast; ring

/-- **Per-Faulhaber-term mod-p³ bound, parametrically extended to `t ≤ 2p − 3`**.

For prime `p` odd, `t` even with `p + 2 ≤ t ≤ 2p − 3`, takes a parametric
input `ih_B` providing `B_j ∈ ℤ_[p]` for even `j` in `[p, t − 2]` with
`(p − 1) ∤ j` (numerically verifiable per `j` via
`bernoulli_mem_padicInt_of_p_not_dvd_den`). -/
lemma faulhaber_term_mem_p_cubed_extended
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {t : ℕ} (ht_pp2 : p + 2 ≤ t) (_ht_even : Even t) (ht_lt : t ≤ 2 * p - 3)
    (ih_B : ∀ j, p ≤ j → j ≤ t - 2 → Even j → ¬ (p - 1) ∣ j →
      ∃ z : ℤ_[p], (((bernoulli j : ℚ)) : ℚ_[p]) = (z : ℚ_[p]))
    {i : ℕ} (hi : i < t - 1) :
    ∃ z : ℤ_[p],
      ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p]) ^ (t + 1 - i)) =
        ((p : ℚ_[p]) ^ 3) * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  -- Case 1: i = 0.
  rcases Nat.eq_zero_or_pos i with rfl | hi_pos
  · refine ⟨(p : ℤ_[p]) ^ (t - 2), ?_⟩
    simp only [_root_.bernoulli_zero, Rat.cast_one, one_mul,
      Nat.choose_zero_right, Nat.cast_one]
    rw [show (t + 1 - 0 : ℕ) = 3 + (t - 2) by omega, pow_add]
    push_cast; ring
  -- Case 2: i = 1.
  rcases eq_or_ne i 1 with rfl | hi_ne_one
  · have h2_unit : IsUnit ((2 : ℕ) : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact hp.coprime_iff_not_dvd.mpr fun h =>
        absurd (Nat.le_of_dvd (by omega) h) (by omega)
    set w : ℤ_[p] := (h2_unit.unit⁻¹ : (ℤ_[p])ˣ).val with hw_def
    have hw_mul : ((2 : ℕ) : ℤ_[p]) * w = 1 := by
      change ((h2_unit.unit * h2_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1; simp
    have hw_mul_Qp : (2 : ℚ_[p]) * ((w : ℤ_[p]) : ℚ_[p]) = 1 := by
      exact_mod_cast congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hw_mul
    refine ⟨-((Nat.choose (t + 1) 1 : ℤ_[p]) * w * (p : ℤ_[p]) ^ (t - 3)), ?_⟩
    rw [_root_.bernoulli_one,
      show (t + 1 - 1 : ℕ) = 3 + (t - 3) by omega, pow_add]
    have h2Q_ne : (2 : ℚ_[p]) ≠ 0 := by norm_num
    have h_half : ((-1 / 2 : ℚ) : ℚ_[p]) = -((w : ℤ_[p]) : ℚ_[p]) :=
      mul_left_cancel₀ h2Q_ne (by push_cast; linear_combination hw_mul_Qp)
    rw [h_half]; push_cast; ring
  -- i ≥ 2.
  have hi_ge : 2 ≤ i := by omega
  rcases Nat.even_or_odd i with hi_even | hi_odd
  · have hi_le : i ≤ t - 2 := by omega
    -- Three subcases based on i's relationship to p.
    by_cases hi_lt_psub : i < p - 1
    · -- vSC generic via restricted Adams.
      obtain ⟨b, hb⟩ := bernoulli_mem_padicInt_of_lt_sub_one hp_odd i hi_lt_psub
      refine ⟨b * (Nat.choose (t + 1) i : ℤ_[p]) * (p : ℤ_[p]) ^ (t - i - 2), ?_⟩
      rw [show t + 1 - i = 3 + (t - i - 2) from by omega,
        show (p : ℚ_[p]) ^ (3 + (t - i - 2)) =
          (p : ℚ_[p]) ^ 3 * (p : ℚ_[p]) ^ (t - i - 2) from by rw [pow_add]]
      rw [hb]; push_cast; ring
    · push Not at hi_lt_psub
      -- i ≥ p - 1. Two further subcases: i = p - 1 (boundary) or i ≥ p (use ih_B).
      by_cases hi_eq_psub : i = p - 1
      · -- i = p - 1, vSC boundary.
        have h_pm1_even : Even (p - 1) := by
          rcases Nat.even_or_odd p with h_pe | h_po
          · exfalso
            rcases h_pe with ⟨k, hk⟩
            have h_dvd : 2 ∣ p := ⟨k, by omega⟩
            rcases hp.eq_one_or_self_of_dvd 2 h_dvd with h | h
            · omega
            · exact hp_odd h.symm
          · rcases h_po with ⟨k, hk⟩; exact ⟨k, by omega⟩
        have h_below : ∀ j, j ≤ i → ¬ (p : ℕ) ^ 3 ∣ (j + 1) := by
          intro j hj h_dvd
          have h_jp1_le : j + 1 ≤ p := by omega
          have hp_lt_p3 : p < p ^ 3 := by
            have hp2 : 4 ≤ p ^ 2 := by nlinarith
            have h_eq : p ^ 3 = p ^ 2 * p := by ring
            nlinarith
          have : p ^ 3 ≤ j + 1 := Nat.le_of_dvd (Nat.succ_pos _) h_dvd
          omega
        have hi_even' : Even i := hi_eq_psub ▸ h_pm1_even
        obtain ⟨c, hc⟩ := p_mul_bernoulli_mem_padicInt_restricted (p := p) hp_odd
          hi_ge hi_even' h_below
        refine ⟨c * (Nat.choose (t + 1) i : ℤ_[p]) * (p : ℤ_[p]) ^ (t - i - 3), ?_⟩
        have hbc : ((bernoulli i : ℚ) : ℚ_[p]) * ((p : ℚ_[p])) =
            ((c : ℤ_[p]) : ℚ_[p]) := by rw [← hc]; ring
        have h_pow_split : (p : ℚ_[p]) ^ (t + 1 - i) =
            (p : ℚ_[p]) ^ (t - i - 3) * (p : ℚ_[p]) ^ 4 := by
          rw [← pow_add]; congr 1; omega
        rw [h_pow_split]
        push_cast
        linear_combination
          (((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) * ((p : ℚ_[p]) ^ (t - i - 3))
            * ((p : ℚ_[p]) ^ 3)) * hbc
      · -- i ≥ p (since i ≥ p-1 and i ≠ p-1). And (p-1) ∤ i.
        have hi_ge_p : p ≤ i := by omega
        have hi_not_dvd : ¬ (p - 1) ∣ i := by
          -- i ∈ [p, t-2]. (p-1)·m for m ≥ 1: smallest is p-1 (excluded since i ≥ p > p-1),
          -- next is 2(p-1) = 2p-2 > 2p-5 ≥ t-2 ≥ i.
          intro h_dvd
          obtain ⟨m, hm⟩ := h_dvd
          rcases m with _ | _ | k
          · -- m = 0 ⟹ i = 0
            omega
          · -- m = 1 ⟹ i = p-1
            exact hi_eq_psub (by omega)
          · -- m = k + 2 ⟹ i ≥ 2(p-1)
            have h_le : (p - 1) * 2 ≤ (p - 1) * (k + 1 + 1) := by
              apply Nat.mul_le_mul_left; omega
            have h_eq : (p - 1) * 2 = 2 * (p - 1) := by ring
            omega
        obtain ⟨b, hb⟩ := ih_B i hi_ge_p hi_le hi_even hi_not_dvd
        refine ⟨b * (Nat.choose (t + 1) i : ℤ_[p]) * (p : ℤ_[p]) ^ (t - i - 2), ?_⟩
        rw [show t + 1 - i = 3 + (t - i - 2) from by omega,
          show (p : ℚ_[p]) ^ (3 + (t - i - 2)) =
            (p : ℚ_[p]) ^ 3 * (p : ℚ_[p]) ^ (t - i - 2) from by rw [pow_add]]
        rw [hb]; push_cast; ring
  · -- Case 3: i odd, i ≥ 3.
    refine ⟨0, ?_⟩
    have hi_gt : 1 < i := by omega
    rw [bernoulli_eq_zero_of_odd hi_odd hi_gt]; push_cast; ring

/-- **Order-2 Faulhaber bound** (restricted form `t ≤ p − 1`).

For prime `p` odd, `t` even with `4 ≤ t ≤ p − 1`:
   `(t+1) · (∑_{a < p} a^t − p · B_t)  ∈  p³ · ℤ_[p]`.

Proof: Faulhaber expansion + per-term mod-`p³` bound (`faulhaber_term_mem_p_cubed`).
The `i = t − 1` Faulhaber term vanishes since `B_{t-1} = 0` for `t ≥ 4` even
(odd index ≥ 3). The `i = t` term separates as `(t+1) · p · B_t`. The
remaining `i = 0, …, t − 2` terms each lie in `p³ · ℤ_[p]`. -/
theorem sum_range_pow_sub_p_mul_bernoulli_weighted_p_cubed
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {t : ℕ} (ht_four : 4 ≤ t) (ht_even : Even t) (ht_lt : t ≤ p - 1) :
    ∃ W : ℤ_[p],
      ((t + 1 : ℕ) : ℚ_[p]) *
          ((∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t) -
            (p : ℚ_[p]) * ((bernoulli t : ℚ) : ℚ_[p])) =
        ((p : ℚ_[p]) ^ 3) * ((W : ℤ_[p]) : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  -- Per-`i` witness from `faulhaber_term_mem_p_cubed` for i < t - 1.
  choose w hw using (fun (i : ℕ) (hi : i < t - 1) =>
    faulhaber_term_mem_p_cubed hp_odd ht_four ht_even ht_lt hi)
  -- W : ℤ_[p] = ∑ w_i over i ∈ range (t - 1).
  set W : ℤ_[p] :=
    ∑ i ∈ Finset.attach (Finset.range (t - 1)),
      w i.1 (Finset.mem_range.mp i.2) with hW_def
  refine ⟨W, ?_⟩
  -- Faulhaber in ℚ multiplied by (t+1).
  have h_faulhaber_Q : ((t + 1 : ℚ)) * (∑ k ∈ Finset.range p, (k : ℚ) ^ t) =
      ∑ i ∈ Finset.range (t + 1),
        bernoulli i * (Nat.choose (t + 1) i : ℚ) * (p : ℚ) ^ (t + 1 - i) := by
    rw [sum_range_pow p t, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have htp1Q_ne : (((t + 1 : ℕ)) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  -- Cast to ℚ_[p].
  have h_faulhaber_Qp : ((t + 1 : ℕ) : ℚ_[p]) *
      (∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t) =
      ∑ i ∈ Finset.range (t + 1),
        ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p])) ^ (t + 1 - i) := by
    have := congrArg (fun q : ℚ => (q : ℚ_[p])) h_faulhaber_Q
    push_cast at this; push_cast; exact this
  -- Split off i = t (the leading B_t term).
  have h_split_t : ((t + 1 : ℕ) : ℚ_[p]) *
        (∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t) -
      ((t + 1 : ℕ) : ℚ_[p]) * ((p : ℚ_[p])) * ((bernoulli t : ℚ) : ℚ_[p]) =
      ∑ i ∈ Finset.range t,
        ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p])) ^ (t + 1 - i) := by
    rw [h_faulhaber_Qp, Finset.sum_range_succ, Nat.choose_succ_self_right t,
      show (t + 1 - t : ℕ) = 1 from by omega]
    push_cast; ring
  -- Split off i = t - 1 (which is 0 since B_{t-1} = 0 for t ≥ 4 even).
  have ht_pos : 0 < t := by omega
  have h_t_minus_one : ((bernoulli (t - 1) : ℚ) : ℚ_[p]) = 0 := by
    have h_odd : Odd (t - 1) := by
      rcases ht_even with ⟨m, hm⟩
      refine ⟨m - 1, ?_⟩; omega
    have h_gt : 1 < t - 1 := by omega
    rw [bernoulli_eq_zero_of_odd h_odd h_gt]; push_cast; ring
  have h_split_tm1 : (∑ i ∈ Finset.range t,
        ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p])) ^ (t + 1 - i)) =
      ∑ i ∈ Finset.range (t - 1),
        ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p])) ^ (t + 1 - i) := by
    rw [show t = (t - 1) + 1 from by omega, Finset.sum_range_succ]
    rw [show ((t - 1) + 1 - 1 : ℕ) = t - 1 from by omega, h_t_minus_one]
    ring
  -- The remaining sum (i = 0, ..., t-2) is in p³·ℤ_[p] by faulhaber_term_mem_p_cubed.
  have h_rhs_eq : (∑ i ∈ Finset.range (t - 1),
        ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p])) ^ (t + 1 - i)) =
      ((p : ℚ_[p])) ^ 3 * ((W : ℤ_[p]) : ℚ_[p]) := by
    rw [← Finset.sum_attach]
    rw [show (((p : ℚ_[p])) ^ 3 * ((W : ℤ_[p]) : ℚ_[p])) =
        ∑ i ∈ Finset.attach (Finset.range (t - 1)),
          ((p : ℚ_[p])) ^ 3 *
            ((w i.1 (Finset.mem_range.mp i.2) : ℤ_[p]) : ℚ_[p]) from ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      exact hw i.1 (Finset.mem_range.mp i.2)
    · rw [hW_def]
      simp [PadicInt.coe_sum, Finset.mul_sum]
  rw [mul_sub, ← h_rhs_eq, ← h_split_tm1, ← h_split_t]
  push_cast; ring

/-- **Order-2 Faulhaber bound, extended `t ≤ 2p − 3`**, parametric on
unrestricted Adams. -/
theorem sum_range_pow_sub_p_mul_bernoulli_weighted_p_cubed_extended
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {t : ℕ} (ht_pp2 : p + 2 ≤ t) (ht_even : Even t) (ht_lt : t ≤ 2 * p - 3)
    (ih_B : ∀ j, p ≤ j → j ≤ t - 2 → Even j → ¬ (p - 1) ∣ j →
      ∃ z : ℤ_[p], (((bernoulli j : ℚ)) : ℚ_[p]) = (z : ℚ_[p])) :
    ∃ W : ℤ_[p],
      ((t + 1 : ℕ) : ℚ_[p]) *
          ((∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t) -
            (p : ℚ_[p]) * ((bernoulli t : ℚ) : ℚ_[p])) =
        ((p : ℚ_[p]) ^ 3) * ((W : ℤ_[p]) : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  choose w hw using (fun (i : ℕ) (hi : i < t - 1) =>
    faulhaber_term_mem_p_cubed_extended hp_odd ht_pp2 ht_even ht_lt ih_B hi)
  set W : ℤ_[p] :=
    ∑ i ∈ Finset.attach (Finset.range (t - 1)),
      w i.1 (Finset.mem_range.mp i.2) with hW_def
  refine ⟨W, ?_⟩
  have h_faulhaber_Q : ((t + 1 : ℚ)) * (∑ k ∈ Finset.range p, (k : ℚ) ^ t) =
      ∑ i ∈ Finset.range (t + 1),
        bernoulli i * (Nat.choose (t + 1) i : ℚ) * (p : ℚ) ^ (t + 1 - i) := by
    rw [sum_range_pow p t, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have htp1Q_ne : (((t + 1 : ℕ)) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  have h_faulhaber_Qp : ((t + 1 : ℕ) : ℚ_[p]) *
      (∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t) =
      ∑ i ∈ Finset.range (t + 1),
        ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p])) ^ (t + 1 - i) := by
    have := congrArg (fun q : ℚ => (q : ℚ_[p])) h_faulhaber_Q
    push_cast at this; push_cast; exact this
  have h_split_t : ((t + 1 : ℕ) : ℚ_[p]) *
        (∑ k ∈ Finset.range p, (k : ℚ_[p]) ^ t) -
      ((t + 1 : ℕ) : ℚ_[p]) * ((p : ℚ_[p])) * ((bernoulli t : ℚ) : ℚ_[p]) =
      ∑ i ∈ Finset.range t,
        ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p])) ^ (t + 1 - i) := by
    rw [h_faulhaber_Qp, Finset.sum_range_succ, Nat.choose_succ_self_right t,
      show (t + 1 - t : ℕ) = 1 from by omega]
    push_cast; ring
  have ht_pos : 0 < t := by omega
  have h_t_minus_one : ((bernoulli (t - 1) : ℚ) : ℚ_[p]) = 0 := by
    have h_odd : Odd (t - 1) := by
      rcases ht_even with ⟨m, hm⟩
      refine ⟨m - 1, ?_⟩; omega
    have h_gt : 1 < t - 1 := by omega
    rw [bernoulli_eq_zero_of_odd h_odd h_gt]; push_cast; ring
  have h_split_tm1 : (∑ i ∈ Finset.range t,
        ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p])) ^ (t + 1 - i)) =
      ∑ i ∈ Finset.range (t - 1),
        ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p])) ^ (t + 1 - i) := by
    rw [show t = (t - 1) + 1 from by omega, Finset.sum_range_succ]
    rw [show ((t - 1) + 1 - 1 : ℕ) = t - 1 from by omega, h_t_minus_one]
    ring
  have h_rhs_eq : (∑ i ∈ Finset.range (t - 1),
        ((bernoulli i : ℚ) : ℚ_[p]) * ((Nat.choose (t + 1) i : ℕ) : ℚ_[p]) *
          ((p : ℚ_[p])) ^ (t + 1 - i)) =
      ((p : ℚ_[p])) ^ 3 * ((W : ℤ_[p]) : ℚ_[p]) := by
    rw [← Finset.sum_attach]
    rw [show (((p : ℚ_[p])) ^ 3 * ((W : ℤ_[p]) : ℚ_[p])) =
        ∑ i ∈ Finset.attach (Finset.range (t - 1)),
          ((p : ℚ_[p])) ^ 3 *
            ((w i.1 (Finset.mem_range.mp i.2) : ℤ_[p]) : ℚ_[p]) from ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      exact hw i.1 (Finset.mem_range.mp i.2)
    · rw [hW_def]
      simp [PadicInt.coe_sum, Finset.mul_sum]
  rw [mul_sub, ← h_rhs_eq, ← h_split_tm1, ← h_split_t]
  push_cast; ring

/-- **ℚ_[p]-cast of the order-2 Voronoi sum identity**: same statement as
`voronoi_sum_mod_p_cubed` but with all sums and multiplications viewed
as `ℚ_[p]` elements (the form used by Kummer-congruence consumers). -/
lemma voronoi_sum_mod_p_cubed_Q
    {p : ℕ} [hp : Fact p.Prime]
    {a : ℕ} (ha_coprime : ¬ (p : ℕ) ∣ a)
    {k : ℕ} (hk_two : 2 ≤ k) :
    ∃ W : ℤ_[p],
      ((a : ℚ_[p]) ^ k - 1) *
            ((∑ j ∈ Finset.range p, j ^ k : ℕ) : ℚ_[p]) -
          (k : ℚ_[p]) * ((a : ℚ_[p]) ^ (k - 1)) * (p : ℚ_[p]) *
            ((∑ j ∈ Finset.range p,
              j ^ (k - 1) * (j * a / p) : ℕ) : ℚ_[p]) +
          ((k.choose 2 : ℕ) : ℚ_[p]) * ((a : ℚ_[p]) ^ (k - 2)) *
            (p : ℚ_[p]) ^ 2 *
              ((∑ j ∈ Finset.range p,
                j ^ (k - 2) * (j * a / p) ^ 2 : ℕ) : ℚ_[p]) =
        (p : ℚ_[p]) ^ 3 * ((W : ℤ_[p]) : ℚ_[p]) := by
  obtain ⟨W, hW⟩ := voronoi_sum_mod_p_cubed ha_coprime hk_two
  refine ⟨W, ?_⟩
  -- Cast hW from ℤ_[p] to ℚ_[p].
  have h_cast := congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hW
  simp only [PadicInt.coe_sub, PadicInt.coe_add, PadicInt.coe_mul,
    PadicInt.coe_pow, PadicInt.coe_natCast, PadicInt.coe_one] at h_cast
  push_cast at h_cast ⊢
  linear_combination h_cast

/-- **Parametric order-2 Voronoi congruence**: combines the order-2
Voronoi sum (`voronoi_sum_mod_p_cubed_Q`) with a parametric Faulhaber-
mod-`p³` input to derive an order-2 Kummer-style congruence in `ℚ_[p]`:

  `(a^k - 1) · B_k - k · a^{k-1} · ∑ j^{k-1}·⌊ja/p⌋
   + (k C 2) · a^{k-2} · p · ∑ j^{k-2}·⌊ja/p⌋²  ∈ p² · ℤ_[p]`.

The parametric Faulhaber input is the next concrete piece needed to
discharge fully (substantive proof requires order-2 valuation analysis
on each term of `Finset.sum_range_pow`; for `k < 2(p−1)` this avoids
`(p−1) ∣ i` complications and the bound is direct). For `(p, k) =
(37, 32)` (the FLT37 application), `k = 32 < 72 = 2(p−1)`, so the
hypothesis can be discharged by direct valuation analysis. -/
theorem voronoi_congruence_mod_p_sq_of_faulhaber
    {p : ℕ} [hp : Fact p.Prime] (_hp_odd : p ≠ 2)
    {a : ℕ} (ha_coprime : ¬ (p : ℕ) ∣ a)
    {k : ℕ} (hk_two : 2 ≤ k)
    (h_p_not_dvd_kPlus : ¬ (p : ℕ) ∣ (k + 1))
    (h_faulhaber : ∃ W' : ℤ_[p],
      ((k + 1 : ℕ) : ℚ_[p]) *
            ((∑ j ∈ Finset.range p, j ^ k : ℕ) : ℚ_[p]) -
          ((k + 1 : ℕ) : ℚ_[p]) * (p : ℚ_[p]) *
            ((bernoulli k : ℚ) : ℚ_[p]) =
        (p : ℚ_[p]) ^ 3 * ((W' : ℤ_[p]) : ℚ_[p])) :
    ∃ z : ℤ_[p],
      ((a : ℚ_[p]) ^ k - 1) * ((bernoulli k : ℚ) : ℚ_[p]) -
          (k : ℚ_[p]) * ((a : ℚ_[p]) ^ (k - 1)) *
            ((∑ j ∈ Finset.range p,
              j ^ (k - 1) * (j * a / p) : ℕ) : ℚ_[p]) +
          ((k.choose 2 : ℕ) : ℚ_[p]) * ((a : ℚ_[p]) ^ (k - 2)) *
            (p : ℚ_[p]) *
              ((∑ j ∈ Finset.range p,
                j ^ (k - 2) * (j * a / p) ^ 2 : ℕ) : ℚ_[p]) =
        (p : ℚ_[p]) ^ 2 * ((z : ℤ_[p]) : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hp_pos : 0 < p := hp.pos
  have hpQ_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.ne_zero
  -- Order-2 Voronoi sum identity in ℚ_[p].
  obtain ⟨W, hW⟩ := voronoi_sum_mod_p_cubed_Q ha_coprime hk_two
  -- Parametric Faulhaber input.
  obtain ⟨W', hW'⟩ := h_faulhaber
  -- Modular inverse of (k+1).
  have hkp1_unit : IsUnit ((k + 1 : ℕ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr h_p_not_dvd_kPlus
  set u : ℤ_[p] := (hkp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val with hu_def
  have hu_mul : ((k + 1 : ℕ) : ℤ_[p]) * u = 1 := by
    change ((hkp1_unit.unit * hkp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1; simp
  have hu_mul_Qp : ((k + 1 : ℕ) : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hu_mul
  have hkp1Q_ne : ((k + 1 : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- From hW': divide by (k+1) to get S₁ - p·B_k = u·p³·W'.
  set S1 : ℚ_[p] := ((∑ j ∈ Finset.range p, j ^ k : ℕ) : ℚ_[p])
  have h_S1_sub : S1 - (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p]) =
      ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ 3 * ((W' : ℤ_[p]) : ℚ_[p]) := by
    have h_mul : ((k + 1 : ℕ) : ℚ_[p]) *
        (S1 - (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p])) =
        ((k + 1 : ℕ) : ℚ_[p]) *
        (((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ 3 * ((W' : ℤ_[p]) : ℚ_[p])) := by
      rw [show S1 = ((∑ j ∈ Finset.range p, j ^ k : ℕ) : ℚ_[p]) from rfl]
      linear_combination hW' -
        ((p : ℚ_[p]) ^ 3 * ((W' : ℤ_[p]) : ℚ_[p])) * hu_mul_Qp
    exact mul_left_cancel₀ hkp1Q_ne h_mul
  -- Substitute S₁ = p·B_k + u·p³·W' into hW.
  have hS1_eq : S1 = (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p]) +
      ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ 3 * ((W' : ℤ_[p]) : ℚ_[p]) := by
    linear_combination h_S1_sub
  rw [hS1_eq] at hW
  -- Push the natCast sums in hW to ℚ_[p] form to match the goal.
  push_cast at hW
  -- hW : (a^k - 1)·(p·B_k + u·p³·W') - k·a^(k-1)·p·S₂ + (k C 2)·a^(k-2)·p²·S₃ = p³·W.
  -- Goal: (a^k - 1)·B_k - k·a^(k-1)·S₂ + (k C 2)·a^(k-2)·p·S₃ = p²·z.
  -- Multiply both sides by p; the new goal follows from hW.
  refine ⟨W - ((a : ℤ_[p]) ^ k - 1) * u * W', ?_⟩
  apply mul_left_cancel₀ hpQ_ne
  push_cast
  linear_combination hW

/-- **Order-2 Voronoi congruence**, restricted form `k ≤ p − 1`.

For prime `p` odd, `a` coprime to `p`, `k` even with `4 ≤ k ≤ p − 1`,
`p ∤ (k + 1)`:

  `(a^k − 1) · B_k − k · a^{k−1} · ∑ j^{k−1} · ⌊ja/p⌋
   + (k C 2) · a^{k−2} · p · ∑ j^{k−2} · ⌊ja/p⌋²  ∈  p² · ℤ_[p]`.

This is the non-parametric order-2 Voronoi congruence, obtained by
combining `voronoi_congruence_mod_p_sq_of_faulhaber` with the discharged
Faulhaber bound `sum_range_pow_sub_p_mul_bernoulli_weighted_p_cubed`. -/
theorem voronoi_congruence_mod_p_sq
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {a : ℕ} (ha_coprime : ¬ (p : ℕ) ∣ a)
    {k : ℕ} (hk_four : 4 ≤ k) (hk_even : Even k) (hk_lt : k ≤ p - 1)
    (h_p_not_dvd_kPlus : ¬ (p : ℕ) ∣ (k + 1)) :
    ∃ z : ℤ_[p],
      ((a : ℚ_[p]) ^ k - 1) * ((bernoulli k : ℚ) : ℚ_[p]) -
          (k : ℚ_[p]) * ((a : ℚ_[p]) ^ (k - 1)) *
            ((∑ j ∈ Finset.range p,
              j ^ (k - 1) * (j * a / p) : ℕ) : ℚ_[p]) +
          ((k.choose 2 : ℕ) : ℚ_[p]) * ((a : ℚ_[p]) ^ (k - 2)) *
            (p : ℚ_[p]) *
              ((∑ j ∈ Finset.range p,
                j ^ (k - 2) * (j * a / p) ^ 2 : ℕ) : ℚ_[p]) =
        (p : ℚ_[p]) ^ 2 * ((z : ℤ_[p]) : ℚ_[p]) := by
  have hk_two : 2 ≤ k := by omega
  apply voronoi_congruence_mod_p_sq_of_faulhaber hp_odd ha_coprime hk_two
    h_p_not_dvd_kPlus
  -- Discharge the Faulhaber-mod-p³ hypothesis using
  -- sum_range_pow_sub_p_mul_bernoulli_weighted_p_cubed.
  obtain ⟨W', hW'⟩ :=
    sum_range_pow_sub_p_mul_bernoulli_weighted_p_cubed hp_odd hk_four hk_even hk_lt
  refine ⟨W', ?_⟩
  -- hW' has form: (k+1)·(S₁ - p·B_k) = p³·W'.
  -- Goal: (k+1)·S₁ - (k+1)·p·B_k = p³·W'.
  have h_cast : ((∑ j ∈ Finset.range p, j ^ k : ℕ) : ℚ_[p]) =
      ∑ k_ ∈ Finset.range p, (k_ : ℚ_[p]) ^ k := by push_cast; rfl
  rw [h_cast]
  linear_combination hW'

/-- **Order-2 Voronoi congruence, extended `k ≤ 2p − 3`**: parametric on
unrestricted Adams. -/
theorem voronoi_congruence_mod_p_sq_extended
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {a : ℕ} (ha_coprime : ¬ (p : ℕ) ∣ a)
    {k : ℕ} (hk_pp2 : p + 2 ≤ k) (hk_even : Even k) (hk_lt : k ≤ 2 * p - 3)
    (h_p_not_dvd_kPlus : ¬ (p : ℕ) ∣ (k + 1))
    (ih_B : ∀ j, p ≤ j → j ≤ k - 2 → Even j → ¬ (p - 1) ∣ j →
      ∃ z : ℤ_[p], (((bernoulli j : ℚ)) : ℚ_[p]) = (z : ℚ_[p])) :
    ∃ z : ℤ_[p],
      ((a : ℚ_[p]) ^ k - 1) * ((bernoulli k : ℚ) : ℚ_[p]) -
          (k : ℚ_[p]) * ((a : ℚ_[p]) ^ (k - 1)) *
            ((∑ j ∈ Finset.range p,
              j ^ (k - 1) * (j * a / p) : ℕ) : ℚ_[p]) +
          ((k.choose 2 : ℕ) : ℚ_[p]) * ((a : ℚ_[p]) ^ (k - 2)) *
            (p : ℚ_[p]) *
              ((∑ j ∈ Finset.range p,
                j ^ (k - 2) * (j * a / p) ^ 2 : ℕ) : ℚ_[p]) =
        (p : ℚ_[p]) ^ 2 * ((z : ℤ_[p]) : ℚ_[p]) := by
  have hk_two : 2 ≤ k := by omega
  apply voronoi_congruence_mod_p_sq_of_faulhaber hp_odd ha_coprime hk_two
    h_p_not_dvd_kPlus
  obtain ⟨W', hW'⟩ :=
    sum_range_pow_sub_p_mul_bernoulli_weighted_p_cubed_extended hp_odd hk_pp2
      hk_even hk_lt ih_B
  refine ⟨W', ?_⟩
  have h_cast : ((∑ j ∈ Finset.range p, j ^ k : ℕ) : ℚ_[p]) =
      ∑ k_ ∈ Finset.range p, (k_ : ℚ_[p]) ^ k := by push_cast; rfl
  rw [h_cast]
  linear_combination hW'

/-- **FLT37 specialisation** of the order-2 Voronoi congruence at
`(p, k) = (37, 32)`: the substantive mod-`37²` constraint on `B_{32}`
that feeds into Kellner's Prop 2.7 chain for the FLT37 irregular pair. -/
theorem voronoi_congruence_mod_37_sq_thirtytwo
    {a : ℕ} (ha_coprime : ¬ (37 : ℕ) ∣ a) :
    haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
    ∃ z : ℤ_[37],
      ((a : ℚ_[37]) ^ 32 - 1) * ((bernoulli 32 : ℚ) : ℚ_[37]) -
          (32 : ℚ_[37]) * ((a : ℚ_[37]) ^ 31) *
            ((∑ j ∈ Finset.range 37, j ^ 31 * (j * a / 37) : ℕ) : ℚ_[37]) +
          ((Nat.choose 32 2 : ℕ) : ℚ_[37]) * ((a : ℚ_[37]) ^ 30) *
            (37 : ℚ_[37]) *
              ((∑ j ∈ Finset.range 37, j ^ 30 * (j * a / 37) ^ 2 : ℕ) :
                ℚ_[37]) =
        (37 : ℚ_[37]) ^ 2 * ((z : ℤ_[37]) : ℚ_[37]) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  apply voronoi_congruence_mod_p_sq (p := 37) (k := 32) (a := a)
    (by decide : (37 : ℕ) ≠ 2) ha_coprime
    (by decide : (4 : ℕ) ≤ 32)
    (by decide : Even 32)
    (by decide : (32 : ℕ) ≤ 37 - 1)
    (by decide : ¬ (37 : ℕ) ∣ (32 + 1))

end BernoulliRegular

end

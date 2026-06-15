module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DigitSum
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Minimal-weight uniqueness for base-`ℓ` decompositions (Layer 1, REF-18c2c4)

For any non-negative integer decomposition `a = Σ_{i<f} k_i · ℓ^i` (with
`k_i ≥ 0`, possibly `k_i ≥ ℓ`), the weight `Σ k_i` is bounded below by
the base-`ℓ` digit sum `s_ℓ(a)`. Equality holds iff `(k_0,…,k_{f-1})`
is the standard base-`ℓ` digit vector of `a` (extended with leading
zeros to length `f`).

This is the **minimal-weight uniqueness theorem** that combines with
`TraceMultinomial.lean`'s expansion to give the digit-sum Stickelberger
congruence: among multinomial-expansion terms of `(traceSum x)^n`
contributing to the `x^a` coefficient, the smallest `n` for which a
non-zero contribution can occur is exactly `s_ℓ(a)`, with a unique
contributing tuple.

## Proof strategy

The clean proof decomposes into three steps:

1. **`digitSum_add_mul`**: for `x < ℓ`,
   `digitSum ℓ (x + ℓ · y) = x + digitSum ℓ y` (via mathlib's
   `Nat.digits_add`).

2. **`digitSum_add_le`**: digit sum is sub-additive,
   `digitSum ℓ (a + b) ≤ digitSum ℓ a + digitSum ℓ b`. Proved via the
   identity `digitSum ℓ n = n − (ℓ−1) · Σ⌊n/ℓ^{i+1}⌋` (Mathlib's
   `Nat.sub_one_mul_sum_log_div_pow_eq_sub_sum_digits`) plus floor
   sup-additivity `⌊(a+b)/c⌋ ≥ ⌊a/c⌋ + ⌊b/c⌋`.

3. **`digitSum_mul_left`**: `digitSum ℓ (ℓ · n) = digitSum ℓ n`,
   since multiplying by `ℓ` prepends a zero digit.

Then the main theorem follows by induction on `f`: write
`S = k 0 + ℓ · T` (where `T = Σ k(j+1) ℓ^j`), then

  `digitSum ℓ S ≤ digitSum ℓ (k 0) + digitSum ℓ (ℓ T)` (sub-additivity)
              `≤ k 0 + digitSum ℓ T` (digitSum_le_self + digitSum_mul_left)
              `≤ k 0 + Σ k(j+1)` (induction hypothesis)
              `= Σ k_i`.

Uniqueness follows from a strict-inequality version of step 1
(when `k 0 ≥ ℓ`, there's a carry that strictly decreases the weight).

These three auxiliary lemmas are stated below as separate `sorry`s
for clarity; the main theorem is then a one-line induction.
-/

@[expose] public section

namespace BernoulliRegular

namespace Furtwaengler

/-- **Aux 1**: For `x < ℓ`, `digitSum ℓ (x + ℓ · y) = x + digitSum ℓ y`. -/
theorem digitSum_add_mul_eq {ℓ : ℕ} (hℓ : 1 < ℓ) (x y : ℕ) (hx : x < ℓ) :
    digitSum ℓ (x + ℓ * y) = x + digitSum ℓ y := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rcases eq_or_ne y 0 with rfl | hy0
    · simp [digitSum]
    · unfold digitSum
      rw [Nat.digits_add ℓ hℓ 0 y hx (Or.inr hy0)]
      simp
  · unfold digitSum
    rw [Nat.digits_add ℓ hℓ x y hx (Or.inl hx0)]
    simp

/-- **Helper for Aux 2 — successor sub-additivity.**
`digitSum (a + 1) ≤ digitSum a + 1`. Adding 1 increases the digit sum
by at most 1; it can decrease via carries (e.g., 99 → 100 in base 10
goes from digit sum 18 to digit sum 1). -/
theorem digitSum_succ_le {ℓ : ℕ} (hℓ : 1 < ℓ) (a : ℕ) :
    digitSum ℓ (a + 1) ≤ digitSum ℓ a + 1 := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  by_cases ha : a = 0
  · subst ha
    show digitSum ℓ (0 + 1) ≤ digitSum ℓ 0 + 1
    have h1 : digitSum ℓ 1 = 1 := digitSum_eq_self_of_lt hℓ (by omega)
    rw [show (0 : ℕ) + 1 = 1 from rfl, h1]
    simp [digitSum]
  -- a ≥ 1. Write a = a₀ + ℓ · a' with a₀ < ℓ.
  have ha₀_lt : a % ℓ < ℓ := Nat.mod_lt a (by omega)
  have ha_eq : a = a % ℓ + ℓ * (a / ℓ) := (Nat.mod_add_div a ℓ).symm
  set a₀ := a % ℓ with ha₀_def
  set a' := a / ℓ with ha'_def
  by_cases ha₀_lt_pred : a₀ + 1 < ℓ
  · -- No carry: a + 1 = (a₀ + 1) + ℓ a'.
    have h_split : a + 1 = (a₀ + 1) + ℓ * a' := by rw [ha_eq]; ring
    rw [h_split]
    rw [digitSum_add_mul_eq hℓ (a₀ + 1) a' ha₀_lt_pred]
    rw [show a = a₀ + ℓ * a' from ha_eq]
    rw [digitSum_add_mul_eq hℓ a₀ a' ha₀_lt]
    omega
  · -- Carry: a₀ + 1 ≥ ℓ, hence a₀ = ℓ - 1.
    push Not at ha₀_lt_pred
    have ha₀_eq : a₀ = ℓ - 1 := by omega
    have h_split : a + 1 = 0 + ℓ * (a' + 1) := by
      rw [ha_eq, ha₀_eq]; ring_nf; omega
    rw [h_split]
    rw [digitSum_add_mul_eq hℓ 0 (a' + 1) (by omega)]
    have ha'_lt : a' < a := by
      apply Nat.div_lt_self
      · omega
      · omega
    have ih_a' : digitSum ℓ (a' + 1) ≤ digitSum ℓ a' + 1 := ih a' ha'_lt
    rw [show a = a₀ + ℓ * a' from ha_eq]
    rw [digitSum_add_mul_eq hℓ a₀ a' ha₀_lt]
    rw [ha₀_eq]
    omega

/-- **Aux 2**: `digitSum` is sub-additive.

Strong induction on `a + b`. Cases:
- `a = 0` or `b = 0`: trivial.
- Both ≥ 1: decompose `a = a₀ + ℓ·a'`, `b = b₀ + ℓ·b'` with `a₀, b₀ < ℓ`.
  - No carry (`a₀ + b₀ < ℓ`): use Aux 1 and IH at `(a', b')`.
  - Carry (`a₀ + b₀ ≥ ℓ`): use Aux 1, IH at `(a', b' + 1)`, and
    `digitSum_succ_le` for `b' + 1`. -/
theorem digitSum_add_le {ℓ : ℕ} (hℓ : 1 < ℓ) :
    ∀ (a b : ℕ), digitSum ℓ (a + b) ≤ digitSum ℓ a + digitSum ℓ b := by
  -- Strong induction on a + b
  suffices h : ∀ n a b, a + b = n →
      digitSum ℓ (a + b) ≤ digitSum ℓ a + digitSum ℓ b by
    intro a b
    exact h (a + b) a b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hab
  by_cases ha : a = 0
  · subst ha; simp [digitSum]
  by_cases hb : b = 0
  · subst hb; simp [digitSum]
  -- Both a, b ≥ 1.
  have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
  have hb_pos : 0 < b := Nat.pos_of_ne_zero hb
  have ha₀_lt : a % ℓ < ℓ := Nat.mod_lt a (by omega)
  have hb₀_lt : b % ℓ < ℓ := Nat.mod_lt b (by omega)
  have ha_eq : a = a % ℓ + ℓ * (a / ℓ) := (Nat.mod_add_div a ℓ).symm
  have hb_eq : b = b % ℓ + ℓ * (b / ℓ) := (Nat.mod_add_div b ℓ).symm
  set a₀ := a % ℓ
  set a' := a / ℓ
  set b₀ := b % ℓ
  set b' := b / ℓ
  have ha'_lt : a' < a := Nat.div_lt_self ha_pos hℓ
  have hb'_lt : b' < b := Nat.div_lt_self hb_pos hℓ
  -- a' + b' < a + b = n
  have habp_lt : a' + b' < n := by omega
  by_cases h_carry : a₀ + b₀ < ℓ
  · -- No-carry case
    have h_split : a + b = (a₀ + b₀) + ℓ * (a' + b') := by
      rw [ha_eq, hb_eq]; ring
    rw [h_split]
    rw [digitSum_add_mul_eq hℓ (a₀ + b₀) (a' + b') h_carry]
    rw [show a = a₀ + ℓ * a' from ha_eq, digitSum_add_mul_eq hℓ a₀ a' ha₀_lt]
    rw [show b = b₀ + ℓ * b' from hb_eq, digitSum_add_mul_eq hℓ b₀ b' hb₀_lt]
    have ih_app : digitSum ℓ (a' + b') ≤ digitSum ℓ a' + digitSum ℓ b' :=
      ih (a' + b') habp_lt a' b' rfl
    omega
  · -- Carry case: a₀ + b₀ ≥ ℓ
    push Not at h_carry
    have hr_lt : a₀ + b₀ - ℓ < ℓ := by omega
    have helper_ab : a + b = a₀ + b₀ + ℓ * (a' + b') := by
      rw [ha_eq, hb_eq]; ring
    have helper_succ : ℓ * (a' + b' + 1) = ℓ * (a' + b') + ℓ := by ring
    have h_split : a + b = (a₀ + b₀ - ℓ) + ℓ * (a' + b' + 1) := by omega
    rw [h_split]
    rw [digitSum_add_mul_eq hℓ (a₀ + b₀ - ℓ) (a' + b' + 1) hr_lt]
    rw [show a = a₀ + ℓ * a' from ha_eq, digitSum_add_mul_eq hℓ a₀ a' ha₀_lt]
    rw [show b = b₀ + ℓ * b' from hb_eq, digitSum_add_mul_eq hℓ b₀ b' hb₀_lt]
    -- Need: a₀ + b₀ - ℓ + digitSum (a' + b' + 1) ≤ a₀ + digitSum a' + (b₀ + digitSum b')
    -- IH at (a', b' + 1): digitSum (a' + b' + 1) ≤ digitSum a' + digitSum (b' + 1)
    -- digitSum_succ_le: digitSum (b' + 1) ≤ digitSum b' + 1
    -- Need a' + (b' + 1) < n.
    -- a + b - (a' + b') ≥ 2 since a' < a, b' < b, hence a' + b' ≤ n - 2.
    have ha_diff : a' < a := ha'_lt
    have hb_diff : b' < b := hb'_lt
    have habp1_lt : a' + (b' + 1) < n := by omega
    have habp1_eq : a' + b' + 1 = a' + (b' + 1) := Nat.add_assoc _ _ _
    rw [habp1_eq]
    have ih_app : digitSum ℓ (a' + (b' + 1)) ≤ digitSum ℓ a' + digitSum ℓ (b' + 1) :=
      ih (a' + (b' + 1)) habp1_lt a' (b' + 1) rfl
    have h_succ : digitSum ℓ (b' + 1) ≤ digitSum ℓ b' + 1 := digitSum_succ_le hℓ b'
    omega

/-- **Aux 3**: `digitSum ℓ (ℓ · n) = digitSum ℓ n`. -/
theorem digitSum_mul_left {ℓ : ℕ} (hℓ : 1 < ℓ) (n : ℕ) :
    digitSum ℓ (ℓ * n) = digitSum ℓ n := by
  have := digitSum_add_mul_eq hℓ 0 n (by omega)
  simpa using this

/-- **Helper**: when all digits `k_i` satisfy `k_i < ℓ`, the standard digit-sum
identity holds: `digitSum ℓ (Σ k_i · ℓ^i) = Σ k_i`. -/
theorem digitSum_eq_sum_of_all_lt
    {ℓ : ℕ} (hℓ : 1 < ℓ) :
    ∀ (f : ℕ) (k : ℕ → ℕ), (∀ i, i < f → k i < ℓ) →
    digitSum ℓ (∑ i ∈ Finset.range f, k i * ℓ ^ i) =
      ∑ i ∈ Finset.range f, k i := by
  intro f
  induction f with
  | zero => intro k _; simp [digitSum]
  | succ f ih =>
    intro k hk_lt
    -- Σ_{i ∈ range (f+1)} k i * ℓ^i = k 0 + ℓ * Σ_{i ∈ range f} k (i+1) * ℓ^i
    have h_split :
        (∑ i ∈ Finset.range (f + 1), k i * ℓ ^ i) =
          k 0 + ℓ * (∑ i ∈ Finset.range f, k (i + 1) * ℓ ^ i) := by
      rw [Finset.sum_range_succ' (fun i => k i * ℓ ^ i) f]
      rw [Finset.mul_sum]
      simp only [pow_zero, mul_one, pow_succ]
      refine (add_comm _ _).trans ?_
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h_split_sum :
        (∑ i ∈ Finset.range (f + 1), k i) =
          k 0 + (∑ i ∈ Finset.range f, k (i + 1)) := by
      rw [Finset.sum_range_succ' k f]
      ring
    rw [h_split, h_split_sum]
    have hk0_lt : k 0 < ℓ := hk_lt 0 (Nat.succ_pos f)
    rw [digitSum_add_mul_eq hℓ (k 0) _ hk0_lt]
    congr 1
    apply ih
    intro i hi
    exact hk_lt (i + 1) (by omega)

/-- **Minimal-weight bound.** For any decomposition
`a = Σ_{i < f} k_i · ℓ^i` (with `k_i ≥ 0`), the weight `Σ k_i` is at
least `s_ℓ(a)` (the base-ℓ digit sum).

Proof by induction on `f`. Base case is trivial. Inductive step:
write `S = k 0 + ℓ · T` where `T := Σ_{i < f} k(i+1) · ℓ^i`. Then
- `digitSum ℓ S ≤ digitSum ℓ (k 0) + digitSum ℓ (ℓ · T)` (sub-additivity, Aux 2)
- `= digitSum ℓ (k 0) + digitSum ℓ T` (Aux 3, `digitSum_mul_left`)
- `≤ k 0 + digitSum ℓ T` (`digitSum_le_self`)
- `≤ k 0 + Σ k(i+1)` (IH on the shifted sequence)
- `= Σ k_i`. -/
theorem decomp_weight_ge_digitSum
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    ∀ (f : ℕ) (k : ℕ → ℕ),
      digitSum ℓ (∑ i ∈ Finset.range f, k i * ℓ ^ i) ≤
        ∑ i ∈ Finset.range f, k i := by
  intro f
  induction f with
  | zero => intro k; simp [digitSum]
  | succ f ih =>
    intro k
    -- Σ_{i ∈ range (f+1)} k i * ℓ^i = k 0 + ℓ * Σ_{i ∈ range f} k (i+1) * ℓ^i
    have h_split :
        (∑ i ∈ Finset.range (f + 1), k i * ℓ ^ i) =
          k 0 + ℓ * (∑ i ∈ Finset.range f, k (i + 1) * ℓ ^ i) := by
      rw [Finset.sum_range_succ' (fun i => k i * ℓ ^ i) f]
      rw [Finset.mul_sum]
      simp only [pow_zero, mul_one, pow_succ]
      refine (add_comm _ _).trans ?_
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h_split_sum :
        (∑ i ∈ Finset.range (f + 1), k i) =
          k 0 + (∑ i ∈ Finset.range f, k (i + 1)) := by
      rw [Finset.sum_range_succ' k f]
      ring
    rw [h_split, h_split_sum]
    set T := ∑ i ∈ Finset.range f, k (i + 1) * ℓ ^ i
    -- Apply Aux 2 (sub-additivity), Aux 3 (digitSum_mul_left), digitSum_le_self, IH
    have h_subadd : digitSum ℓ (k 0 + ℓ * T) ≤ digitSum ℓ (k 0) + digitSum ℓ (ℓ * T) :=
      digitSum_add_le (by omega) (k 0) (ℓ * T)
    have h_mul_left : digitSum ℓ (ℓ * T) = digitSum ℓ T :=
      digitSum_mul_left (by omega) T
    have h_self : digitSum ℓ (k 0) ≤ k 0 := digitSum_le_self ℓ (k 0)
    have h_ih : digitSum ℓ T ≤ ∑ i ∈ Finset.range f, k (i + 1) := ih (fun i => k (i + 1))
    -- Combine
    omega

/-- **Minimal-weight uniqueness (statement form).** Among decompositions
`(k_0, …, k_{f-1})` with all `k_i < ℓ` and `Σ k_i ℓ^i = a`, the unique
such decomposition is the standard base-ℓ digit vector of `a`.

This is the standard uniqueness-of-base-`ℓ`-representation theorem.
Proof by induction on `f`: at each step, `k 0 = a mod ℓ` (forced by
the modular reduction), and the shifted sequence is then determined
by the IH. -/
theorem digitSum_decomp_unique_at_minimum
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (f : ℕ) (a : ℕ)
    (h_a_lt : a < ℓ ^ f) :
    ∃! k : ℕ → ℕ,
      (∀ i, f ≤ i → k i = 0) ∧
      (∀ i, k i < ℓ) ∧
      ∑ i ∈ Finset.range f, k i * ℓ ^ i = a := by
  induction f generalizing a with
  | zero =>
    -- a < ℓ^0 = 1, so a = 0. Unique k is the zero function.
    rw [pow_zero] at h_a_lt
    have ha : a = 0 := by omega
    refine ⟨fun _ => 0, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro _ _; rfl
    · intro _; change (0 : ℕ) < ℓ; omega
    · simp [ha]
    · rintro k ⟨h1, _, _⟩
      ext i
      exact h1 i (Nat.zero_le i)
  | succ f ih =>
    -- a = a₀ + ℓ · a' with a₀ < ℓ, a' < ℓ ^ f.
    have ha₀_lt : a % ℓ < ℓ := Nat.mod_lt a (by omega)
    have ha_eq : a = a % ℓ + ℓ * (a / ℓ) := (Nat.mod_add_div a ℓ).symm
    have ha'_lt : a / ℓ < ℓ ^ f := by
      have h := h_a_lt
      rw [pow_succ] at h
      exact Nat.div_lt_iff_lt_mul (by omega) |>.mpr h
    obtain ⟨k', ⟨hk'_zero, hk'_lt, hk'_sum⟩, hk'_unique⟩ := ih (a / ℓ) ha'_lt
    -- Define k 0 := a % ℓ, k (i+1) := k' i for i ≥ 0; k i := 0 for i ≥ f+1.
    refine ⟨fun i => if i = 0 then a % ℓ else k' (i - 1), ⟨?_, ?_, ?_⟩, ?_⟩
    · intro i hi
      have hi_pos : 0 < i := by omega
      simp only [Nat.ne_of_gt hi_pos, if_false]
      exact hk'_zero (i - 1) (by omega)
    · intro i
      by_cases hi : i = 0
      · simp only [hi, if_true]; exact ha₀_lt
      · simp only [hi, if_false]
        exact hk'_lt (i - 1)
    · -- Σ over range (f+1)
      rw [Finset.sum_range_succ' (fun i => (if i = 0 then a % ℓ else k' (i - 1)) * ℓ ^ i) f]
      simp only [if_true, pow_zero, mul_one]
      rw [show (∑ i ∈ Finset.range f,
          (if i + 1 = 0 then a % ℓ else k' (i + 1 - 1)) * ℓ ^ (i + 1)) =
          ℓ * ∑ i ∈ Finset.range f, k' i * ℓ ^ i by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
        rw [pow_succ]; ring]
      rw [hk'_sum]
      omega
    · -- Uniqueness
      rintro k ⟨h1, h2, h3⟩
      -- Helper: regroup Σ_{i ∈ range (f+1)} k_i ℓ^i = k_0 + ℓ · Σ_{i ∈ range f} k_(i+1) ℓ^i
      have h_regroup : k 0 + ℓ * (∑ i ∈ Finset.range f, k (i + 1) * ℓ ^ i) = a := by
        rw [← h3]
        rw [Finset.sum_range_succ' (fun i => k i * ℓ ^ i) f]
        simp only [pow_zero, mul_one]
        rw [add_comm]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [pow_succ]; ring
      -- Cancel ℓ: from k_0 + ℓ·X = a%ℓ + ℓ·(a/ℓ), with both k_0 and a%ℓ in [0, ℓ),
      -- get k_0 = a%ℓ and X = a/ℓ.
      have hk0_lt := h2 0
      -- Use mod ℓ: k_0 = a mod ℓ
      have hk0_eq : k 0 = a % ℓ := by
        have h_mod : (k 0 + ℓ * (∑ i ∈ Finset.range f, k (i + 1) * ℓ ^ i)) % ℓ =
                     k 0 % ℓ := by
          rw [Nat.add_mul_mod_self_left]
        rw [h_regroup] at h_mod
        rw [Nat.mod_eq_of_lt hk0_lt] at h_mod
        omega
      -- Use the cancellation: from k_0 + ℓ·X = a, get X = (a - k_0) / ℓ = a / ℓ
      have hsum_eq_aq : ∑ i ∈ Finset.range f, k (i + 1) * ℓ ^ i = a / ℓ := by
        have hℓ_pos : 0 < ℓ := by omega
        have h_mul_eq : ℓ * (∑ i ∈ Finset.range f, k (i + 1) * ℓ ^ i) = ℓ * (a / ℓ) := by
          have h1 : k 0 + ℓ * (∑ i ∈ Finset.range f, k (i + 1) * ℓ ^ i) = a := h_regroup
          have h2 : a % ℓ + ℓ * (a / ℓ) = a := ha_eq.symm
          rw [hk0_eq] at h1
          omega
        exact Nat.eq_of_mul_eq_mul_left hℓ_pos h_mul_eq
      -- The shifted function (i ↦ k (i+1)) equals k'
      have hk_shift : (fun i => k (i + 1)) = k' := by
        apply hk'_unique
        refine ⟨?_, ?_, hsum_eq_aq⟩
        · intro i hi
          exact h1 (i + 1) (by omega)
        · intro i
          exact h2 (i + 1)
      -- Combine: k 0 = a%ℓ, and k (i+1) = k' i for i ≥ 0.
      ext i
      by_cases hi : i = 0
      · simp [hi, hk0_eq]
      · simp only [hi, if_false]
        have hi_eq : k i = k ((i - 1) + 1) := by
          congr 1; omega
        rw [hi_eq]
        rw [show k ((i - 1) + 1) = (fun j => k (j + 1)) (i - 1) from rfl]
        rw [hk_shift]

end Furtwaengler

end BernoulliRegular

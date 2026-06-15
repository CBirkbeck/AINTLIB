/-
Copyright (c) 2026 Bernoulli-Regular project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bernoulli-Regular project contributors
-/
import BernoulliRegular.BernoulliFast.Computation
import Mathlib.Data.List.GetD

/-!
# Correctness of `bernoulliCompute`

This module proves `bernoulliCompute n = bernoulli n`, connecting the fast
computable definition to Mathlib's noncomputable `bernoulli`.

## Proof strategy

1. **`binomSum` agrees with `Finset.sum` + `Nat.choose`** (`binomSum_eq`):
   By induction on the list, maintaining the invariant that the running
   coefficient `c` equals `↑(Nat.choose m k)`.  The key identity is
   `(k+1) · C(m, k+1) = (m − k) · C(m, k)` lifted to `ℚ`.

2. **`bernoulliList` properties**:
   - `bernoulliList_length`: `(bernoulliList n).length = n + 1`.
   - `bernoulliList_getD`: earlier entries are preserved on extension.

3. **Main theorem** (`bernoulliCompute_eq`):
   By strong induction on `n` using `sum_bernoulli (n+2)`:
     `∑_{k≤n+1} C(n+2,k) · Bₖ = 0`
   Split off the last term `(n+2) · B_{n+1}`, substitute the IH via
   `Finset.sum_congr`, and equate with the definition of `bernoulliCompute`.

## Main declarations

* `binomSum_eq` — `binomSum bs m = ∑ k ∈ range |bs|, ↑(m.choose k) · bs.getD k 0`
* `bernoulliCompute_eq` — `bernoulliCompute n = bernoulli n`
* `bernoulliCompute_num_eq` — `(bernoulliCompute n).num = (bernoulli n).num`
* `bernoulliCompute_den_eq` — `(bernoulliCompute n).den = (bernoulli n).den`
-/

namespace BernoulliRegular.BernoulliFast

open Finset Nat

/-! ### Binomial coefficient identity -/

/-- The multiplicative recurrence for binomial coefficients, cast to `ℚ`:
`↑C(m, k+1) = ↑C(m, k) · (↑m − ↑k) / (↑k + 1)`.

Follows from `(k+1) · C(m, k+1) = (m − k) · C(m, k)` for `k < m`. -/
theorem cast_choose_mul_eq (m k : ℕ) (hk : k < m) :
    (↑(m.choose (k + 1)) : ℚ) =
      ↑(m.choose k) * ((m : ℚ) - k) / ((k : ℚ) + 1) := by
  have h := Nat.choose_succ_right_eq m k
  have hq :
      ((m.choose (k + 1) * (k + 1) : ℕ) : ℚ) =
        ((m.choose k * (m - k) : ℕ) : ℚ) := by
    exact_mod_cast h
  have hkq : ((k : ℚ) + 1) ≠ 0 := by positivity
  rw [eq_div_iff hkq]
  simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hk.le,
    add_comm, add_left_comm, add_assoc,
    sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hq

/-- When `k ≥ m`, `C(m, k+1) = 0` and the incremental formula also gives 0. -/
theorem cast_choose_mul_eq_of_le (m k : ℕ) (hk : m ≤ k) :
    (↑(m.choose (k + 1)) : ℚ) = 0 := by
  norm_num [Nat.choose_eq_zero_of_lt (Nat.lt_succ_of_le hk)]

/-! ### `binomSum` agrees with `Finset.sum` -/

/-- Loop invariant: `binomSum.loop m bs k c acc` equals
`acc + ∑_{j<|bs|} ↑C(m, k+j) · bs.getD j 0` provided `c = ↑C(m, k)`. -/
theorem binomSum_loop_eq (m : ℕ) (bs : List ℚ) (k : ℕ) (c acc : ℚ)
    (hc : c = ↑(m.choose k)) :
    binomSum.loop m bs k c acc =
      acc + ∑ j ∈ range bs.length, ↑(m.choose (k + j)) * bs.getD j 0 := by
  induction bs generalizing k c acc with
  | nil =>
      simp [binomSum.loop]
  | cons b rest ih =>
      simp only [binomSum.loop, List.length_cons]
      have hc' :
          c * ((m : ℚ) - k) / ((k : ℚ) + 1) = ↑(m.choose (k + 1)) := by
        rw [hc]
        by_cases hkm_lt : k < m
        · rw [cast_choose_mul_eq m k hkm_lt]
        · have hkm : m ≤ k := Nat.le_of_not_gt hkm_lt
          rw [cast_choose_mul_eq_of_le m k hkm]
          rw [div_eq_zero_iff]
          left
          by_cases hEq : m = k
          · subst hEq
            norm_num
          · have hchoose0 : (↑(m.choose k) : ℚ) = 0 := by
              norm_num [Nat.choose_eq_zero_of_lt (lt_of_le_of_ne hkm hEq)]
            rw [hchoose0]
            simp
      rw [ih (k := k + 1) (c := c * ((m : ℚ) - k) / ((k : ℚ) + 1))
        (acc := acc + c * b) hc']
      rw [sum_range_succ']
      rw [hc]
      simp [add_assoc, add_left_comm, add_comm, mul_comm]

/-- `binomSum bs m = ∑_{k<|bs|} C(m,k) · bs.getD k 0`. -/
theorem binomSum_eq (bs : List ℚ) (m : ℕ) :
    binomSum bs m =
      ∑ k ∈ range bs.length, ↑(m.choose k) * bs.getD k 0 := by
  unfold binomSum
  rw [binomSum_loop_eq m bs 0 1 0 (by simp)]
  simp

/-! ### `bernoulliList` properties -/

theorem bernoulliList_length (n : ℕ) : (bernoulliList n).length = n + 1 := by
  induction n with
  | zero =>
      simp [bernoulliList]
  | succ n ih =>
      simp [bernoulliList, ih]

theorem bernoulliList_getD_lt (n k : ℕ) (hk : k ≤ n) :
    (bernoulliList (n + 1)).getD k 0 = (bernoulliList n).getD k 0 := by
  simpa [bernoulliList] using
    (List.getD_append (bernoulliList n)
      [- binomSum (bernoulliList n) (n + 2) / ((n : ℚ) + 2)] 0 k
      (by simpa [bernoulliList_length] using Nat.lt_succ_of_le hk))

theorem bernoulliList_getLast (n : ℕ) :
    (bernoulliList (n + 1)).getLast! =
      - binomSum (bernoulliList n) (n + 2) / ((n : ℚ) + 2) := by
  simp [bernoulliList]

/-! ### Main correctness theorem -/

theorem bernoulliList_getD_eq : ∀ n k : ℕ, k ≤ n → (bernoulliList n).getD k 0 = bernoulli k := by
  intro n
  induction n with
  | zero =>
      intro k hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      simp [bernoulliList]
  | succ n ih =>
      intro k hk
      cases Nat.eq_or_lt_of_le hk with
      | inr hlt =>
          rw [bernoulliList_getD_lt n k (Nat.lt_succ_iff.mp hlt)]
          exact ih k (Nat.lt_succ_iff.mp hlt)
      | inl hEq =>
          subst hEq
          have hlast :
              (bernoulliList (n + 1)).getD (n + 1) 0 =
                - binomSum (bernoulliList n) (n + 2) / ((n : ℚ) + 2) := by
            rw [bernoulliList]
            rw [List.getD_append_right _ _ _ _]
            · rw [bernoulliList_length]
              simp
            · rw [bernoulliList_length]
          rw [hlast]
          have hsum :
              binomSum (bernoulliList n) (n + 2) =
                ∑ x ∈ range (n + 1), ↑((n + 2).choose x) * bernoulli x := by
            rw [binomSum_eq, bernoulliList_length]
            apply sum_congr rfl
            intro x hx
            rw [ih x (Nat.lt_succ_iff.mp (mem_range.mp hx))]
          rw [hsum]
          have hb :
              (∑ x ∈ range (n + 2), ↑((n + 2).choose x) * bernoulli x) = 0 := by
            simpa only [Nat.succ_succ_ne_one, if_false] using sum_bernoulli (n + 2)
          rw [sum_range_succ] at hb
          have hchooseNat : (n + 2).choose (n + 1) = n + 2 := by
            simp
          have hchoose : (↑((n + 2).choose (n + 1)) : ℚ) = (n + 2 : ℚ) := by
            exact_mod_cast hchooseNat
          rw [hchoose] at hb
          have hden : (n + 2 : ℚ) ≠ 0 := by positivity
          have hmul :
              bernoulli (n + 1) * (n + 2 : ℚ) =
                -∑ x ∈ range (n + 1), ↑((n + 2).choose x) * bernoulli x := by
            linarith
          exact ((eq_div_iff hden).2 hmul).symm

/-- **Uniqueness of the Bernoulli sequence.** If `f` satisfies
`∑_{k<n} C(n,k) · f(k) = δ_{n,1}` for all `n ≥ 1`, then `f = bernoulli`.

This is proved by strong induction: the recurrence pins down each `f(n)`
from the previous values, and `sum_bernoulli` shows `bernoulli` satisfies
the same recurrence. -/
theorem eq_bernoulli_of_sum_eq (f : ℕ → ℚ)
    (hf : ∀ n, 1 ≤ n →
      (∑ k ∈ range n, ↑(n.choose k) * f k) = if n = 1 then 1 else 0) :
    ∀ n, f n = bernoulli n := by
  intro n
  have hmain : ∀ m k : ℕ, k ≤ m → f k = bernoulli k := by
    intro m
    induction m with
    | zero =>
        intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
        subst hk0
        have h0 := hf 1 (by omega)
        simpa using h0
    | succ m ihm =>
        intro k hk
        cases Nat.eq_or_lt_of_le hk with
        | inr hlt =>
            exact ihm k (Nat.lt_succ_iff.mp hlt)
        | inl hEq =>
            subst hEq
            have hf0 :
                (∑ x ∈ range (m + 2), ↑((m + 2).choose x) * f x) = 0 := by
              simpa using hf (m + 2) (by omega)
            have hb0 :
                (∑ x ∈ range (m + 2), ↑((m + 2).choose x) * bernoulli x) = 0 := by
              simpa only [Nat.succ_succ_ne_one, if_false] using sum_bernoulli (m + 2)
            rw [sum_range_succ] at hf0 hb0
            have hsum :
                (∑ x ∈ range (m + 1), ↑((m + 2).choose x) * f x) =
                  ∑ x ∈ range (m + 1), ↑((m + 2).choose x) * bernoulli x := by
              apply sum_congr rfl
              intro x hx
              rw [ihm x (Nat.lt_succ_iff.mp (mem_range.mp hx))]
            rw [hsum] at hf0
            have hchooseNat : (m + 2).choose (m + 1) = m + 2 := by
              simp
            have hchoose : (↑((m + 2).choose (m + 1)) : ℚ) = (m + 2 : ℚ) := by
              exact_mod_cast hchooseNat
            rw [hchoose] at hf0 hb0
            have hmul :
                (m + 2 : ℚ) * f (m + 1) = (m + 2 : ℚ) * bernoulli (m + 1) := by
              linarith
            have hmul' :
                f (m + 1) * (m + 2 : ℚ) = bernoulli (m + 1) * (m + 2 : ℚ) := by
              simpa [mul_comm] using hmul
            have hden : (m + 2 : ℚ) ≠ 0 := by positivity
            exact mul_right_cancel₀ hden hmul'
  exact hmain n n le_rfl

/-- `bernoulliCompute n = bernoulli n`. -/
theorem bernoulliCompute_eq (n : ℕ) : bernoulliCompute n = bernoulli n := by
  unfold bernoulliCompute
  rw [List.getLast!_eq_getElem!, List.getElem!_eq_getElem?_getD,
    ← List.getD_eq_getElem?_getD]
  simpa [bernoulliList_length] using bernoulliList_getD_eq n n le_rfl

/-- `bernoulliCompute` satisfies the Bernoulli recurrence. -/
theorem bernoulliCompute_sum (n : ℕ) (_hn : 1 ≤ n) :
    (∑ k ∈ range n, ↑(n.choose k) * bernoulliCompute k) =
      if n = 1 then 1 else 0 := by
  simpa only [bernoulliCompute_eq] using sum_bernoulli n

/-- Corollary for numerator goals. -/
theorem bernoulliCompute_num_eq (n : ℕ) :
    (bernoulliCompute n).num = (bernoulli n).num := by
  rw [bernoulliCompute_eq]

/-- Corollary for denominator goals. -/
theorem bernoulliCompute_den_eq (n : ℕ) :
    (bernoulliCompute n).den = (bernoulli n).den := by
  rw [bernoulliCompute_eq]

end BernoulliRegular.BernoulliFast

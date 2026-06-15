module

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Base-`ℓ` digit sum (Layer 1, REF-18c2c4)

The base-`ℓ` digit sum `s_ℓ(a) = Σ digit_i` where `a = Σ digit_i · ℓ^i`.
This is the right-hand side of the **digit-sum Stickelberger congruence**

  `g(χ^a, ψ) ≡ −u_a · π^{s_ℓ(a)} (mod Q^{s_ℓ(a)+1})`

(REF-18c2c4 corrected target). This file collects elementary properties
of `digitSum` used downstream by the Stickelberger congruence and the
Jacobi-sum carry formula.

This is **Layer 1** in the architecture from the AI-reviewer's
recommendation: pure finite-field/integer combinatorics, no cyclotomic
fields. The later Stickelberger congruence files consume these
combinatorial results.

## References

* Conrad, *Jacobi sums and Stickelberger's congruence*.
* Katre, *Stickelberger ideal and Gauss sums* (arXiv math/0303226).
-/

@[expose] public section

namespace BernoulliRegular

namespace Furtwaengler

/-- Base-`ℓ` digit sum of `a`, i.e. `s_ℓ(a) = Σ digit_i` where
`a = Σ digit_i · ℓ^i`. Wraps `Nat.digits ℓ a` summation for legibility. -/
def digitSum (ℓ a : ℕ) : ℕ := (Nat.digits ℓ a).sum

@[simp] theorem digitSum_zero (ℓ : ℕ) : digitSum ℓ 0 = 0 := by
  simp [digitSum]

/-- `digitSum ℓ a ≤ a`: the digit sum never exceeds the number itself. -/
theorem digitSum_le_self (ℓ a : ℕ) : digitSum ℓ a ≤ a := by
  unfold digitSum
  exact Nat.digit_sum_le ℓ a

/-- For `a < ℓ` and `2 ≤ ℓ`, the only digit is `a` itself, so
`digitSum ℓ a = a`. -/
theorem digitSum_eq_self_of_lt {ℓ a : ℕ} (hℓ : 2 ≤ ℓ) (ha : a < ℓ) :
    digitSum ℓ a = a := by
  unfold digitSum
  rcases a with _ | a
  · simp
  · rw [Nat.digits_def' hℓ (Nat.succ_pos a)]
    have hlt : a + 1 < ℓ := ha
    rw [Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt]
    simp

end Furtwaengler

end BernoulliRegular

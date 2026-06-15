/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.Infinity

/-!
# WithTop ℤ arithmetic helpers for ordAtInfty calculations

Closed-form one-liners that consolidate the repetitive `WithTop` rw chains
encountered in `ordAtInfty` arithmetic. Built on top of the basic API in
`HasseWeil/Curves/Infinity.lean`.

These avoid the unification glitches around `(↑a : WithTop ℤ) + (↑b)` vs
`↑(a + b)` that consume tactic budget in downstream proofs.

## Main lemmas

* `coe_add_coe`, `coe_neg_coe`, `coe_sub_coe`: cast-normalize.
* `ord_div_concrete`: closed-form ord of a quotient with int-valued ords.
* `ord_pow_concrete`: closed-form ord of a power with int-valued ord.
* `ord_add_lt_concrete`: strict non-archimedean for elements with int-valued ords.

## Tactical notes for `WithTop ℤ` rewrites

A few sharp edges discovered while shipping the Frobenius-pullback
ord computations in `HasseWeil/AdditionPullback/Frobenius.lean` (Day 1
of the addPullbackNumerator route). File these so the next session
doesn't rediscover them.

- `rw [← WithTop.coe_add]` may **fail to find its pattern** when Lean has
  display-normalized the cast: a goal like `((-2 * (#K : ℤ)) : WithTop ℤ)
  + ((-3 * (#K : ℤ)) : WithTop ℤ)` displays as `-2 * ↑↑#K + -3 * ↑↑#K`,
  and the rewrite engine treats the underlying term as multiplication
  in `WithTop` (not as `↑x + ↑y`). Workaround: insert an explicit
  `change ((m₁ * (#K : ℤ)) : WithTop ℤ) + ((m₂ * (#K : ℤ)) : WithTop ℤ)
  = ...` to force the coe form, then `rw [← WithTop.coe_add]; congr 1;
  ring`.

- `rw [h₁, h₂]` for a chain of `ordAtInfty_*` rewrites in the same step
  can fail with "Did not find an occurrence of the pattern" even though
  the patterns appear syntactically identical to the goal. Cause: the
  intermediate goal after the first rewrite may carry hidden cast/instance
  normalization that breaks pattern-matching for later rewrites. Workaround:
  use `congrArg₂ (· + ·) h₁ h₂` (term-level substitution) followed by
  `.trans ?_`, or split into separate `have h_inner_eq := …` lemmas to
  isolate the rewrites.

- The `0` in `ordAtInfty_algebraMap_F_nonzero hc : C.ordAtInfty (algebraMap c) = 0`
  is `(0 : WithTop ℤ)`, **not** `((0 : ℤ) : WithTop ℤ)`. If you write a
  helper expecting `((0 : ℤ) : WithTop ℤ)`, downstream `zero_add` rewrites
  silently fail; just plumb the bare `0` through and the API rules fire.

- `ring` does not work on `WithTop ℤ` directly (it is not a `CommRing`).
  Lift to `ℤ` via `change` to coe form, then `rw [← WithTop.coe_add];
  congr 1; ring`.

- **Dot-notation `rw` failures generalize**: `rw [(C).ordAtInfty_neg]`
  fails with "pattern not found" even when the pattern visibly matches.
  Workaround: term-mode `((C).ordAtInfty_neg _).trans (...)` chains
  cleanly. Same applies to `(C).ordAtInfty_sub_eq_of_lt` etc. — when
  `rw` chokes, switch to `Eq.trans` term construction.

- **`(eq).symm.le` pattern** for goals `↑x ≤ (C).ordAtInfty f` when
  the existing lemma gives `(C).ordAtInfty f = ↑x` exactly: instead
  of `rw [lemma]; exact le_refl _` (which can fail due to dot-notation
  rw issues), write `exact (lemma).symm.le`. The `.symm` flips the
  direction; `.le` extracts the `≤` from the resulting equation.
  One-liner replacement for a 2-line tactic block.
-/

namespace HasseWeil.Curves.SmoothPlaneCurve

variable {F : Type*} [Field F] (C : SmoothPlaneCurve F)

/-! ### Cast-normalization for `WithTop ℤ` -/

@[simp] theorem coe_add_coe (a b : ℤ) :
    ((a : ℤ) : WithTop ℤ) + ((b : ℤ) : WithTop ℤ) =
      (((a + b : ℤ)) : WithTop ℤ) := by
  rw [← WithTop.coe_add]

@[simp] theorem coe_neg_coe (a : ℤ) :
    -(((a : ℤ)) : WithTop ℤ) = (((-a : ℤ)) : WithTop ℤ) := rfl

/-! ### Closed-form ord computations -/

/-- Closed-form `ord(a/b) = m - n` from integer-valued ords on numerator
and denominator. -/
theorem ord_div_concrete {a b : C.FunctionField} (hb : b ≠ 0) (m n : ℤ)
    (h_a : C.ordAtInfty a = ((m : ℤ) : WithTop ℤ))
    (h_b : C.ordAtInfty b = ((n : ℤ) : WithTop ℤ)) :
    C.ordAtInfty (a / b) = (((m - n : ℤ)) : WithTop ℤ) :=
  C.ordAtInfty_div_of_ord_eq hb m n h_a h_b

/-- Closed-form `ord(a^k) = k·m` from integer-valued ord on `a`. -/
theorem ord_pow_concrete {a : C.FunctionField} (hf : a ≠ 0) (m : ℤ) (k : ℕ)
    (h_a : C.ordAtInfty a = ((m : ℤ) : WithTop ℤ)) :
    C.ordAtInfty (a ^ k) = (((k : ℤ) * m : ℤ) : WithTop ℤ) :=
  C.ordAtInfty_pow_of_ord_eq hf m k h_a

/-- Strict non-archimedean with integer-valued ords: when `m < n`,
`ord(a + b) = m`. -/
theorem ord_add_lt_concrete {a b : C.FunctionField} (m n : ℤ) (hmn : m < n)
    (h_a : C.ordAtInfty a = ((m : ℤ) : WithTop ℤ))
    (h_b : C.ordAtInfty b = ((n : ℤ) : WithTop ℤ)) :
    C.ordAtInfty (a + b) = ((m : ℤ) : WithTop ℤ) := by
  have h_lt : C.ordAtInfty a < C.ordAtInfty b := by
    rw [h_a, h_b]; exact_mod_cast hmn
  exact (C.ordAtInfty_add_eq_of_lt h_lt).trans h_a

/-- Strict non-archimedean (sub variant): when `m < n`, `ord(a - b) = m`. -/
theorem ord_sub_lt_concrete {a b : C.FunctionField} (m n : ℤ) (hmn : m < n)
    (h_a : C.ordAtInfty a = ((m : ℤ) : WithTop ℤ))
    (h_b : C.ordAtInfty b = ((n : ℤ) : WithTop ℤ)) :
    C.ordAtInfty (a - b) = ((m : ℤ) : WithTop ℤ) := by
  have h_lt : C.ordAtInfty a < C.ordAtInfty b := by
    rw [h_a, h_b]; exact_mod_cast hmn
  exact (C.ordAtInfty_sub_eq_of_lt h_lt).trans h_a

/-- Strict non-archimedean upper-bound (sym): when `m < n` and the smaller
ord term is `a`, `ord(a + b) ≤ ((m : ℤ) : WithTop ℤ)`. Useful for chaining. -/
theorem ord_add_le_concrete_of_lt {a b : C.FunctionField} (m n : ℤ) (hmn : m < n)
    (h_a : C.ordAtInfty a = ((m : ℤ) : WithTop ℤ))
    (h_b : C.ordAtInfty b = ((n : ℤ) : WithTop ℤ)) :
    C.ordAtInfty (a + b) ≤ ((m : ℤ) : WithTop ℤ) :=
  (C.ord_add_lt_concrete m n hmn h_a h_b).le

end HasseWeil.Curves.SmoothPlaneCurve

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.TranslationOrd

/-!
# Step (B'') localRingAt-image lifts for x_gen, y_gen, and constants

This file contains Worker A's localRingAt-image lifting bridges,
separated from `EC/TranslationOrd.lean` to avoid parallel-edit collisions
with Worker B's stream there.

Each lemma uses the biconditional integer characterisation
`mem_localRingAt_image_of_pointValuation_le_one` (commit a1aa4d7) plus
the underlying valuation bounds.

## Main results

- `x_gen_sub_const_mem_localRingAt_image`: `x_gen − algMap c` lifts to
  `(W_smooth W).localRingAt P` for any constant `c : F`.
- `y_gen_sub_const_mem_localRingAt_image`: companion for the y-coord.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

/-- **`x_gen W - algMap c` lifts to `localRingAt P`** for any constant `c`.
Direct via the strong triangle inequality (Valuation.map_sub) applied
to two ≤ 1 valuations. -/
theorem x_gen_sub_const_mem_localRingAt_image
    (P : (W_smooth W).SmoothPoint) (c : F) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u =
        x_gen W - algebraMap F KE c := by
  apply Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one
  exact le_trans (((W_smooth W).pointValuation P).map_sub _ _)
    (max_le (pointValuation_x_gen_le_one W P)
      ((W_smooth W).pointValuation_algebraMap_F_le_one P c))

/-- **`y_gen W - algMap c` lifts to `localRingAt P`** for any constant `c`.
Companion to `x_gen_sub_const_mem_localRingAt_image`. -/
theorem y_gen_sub_const_mem_localRingAt_image
    (P : (W_smooth W).SmoothPoint) (c : F) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u =
        y_gen W - algebraMap F KE c := by
  apply Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one
  exact le_trans (((W_smooth W).pointValuation P).map_sub _ _)
    (max_le (pointValuation_y_gen_le_one W P)
      ((W_smooth W).pointValuation_algebraMap_F_le_one P c))

/-- **Combined lifts**: both x-side and y-side `algMap c` differences lift
to `localRingAt P`. Useful for downstream consumers needing both. -/
theorem xy_gen_sub_const_mem_localRingAt_image
    (P : (W_smooth W).SmoothPoint) (c d : F) :
    (∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u =
        x_gen W - algebraMap F KE c) ∧
    (∃ v : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField v =
        y_gen W - algebraMap F KE d) :=
  ⟨x_gen_sub_const_mem_localRingAt_image W P c,
   y_gen_sub_const_mem_localRingAt_image W P d⟩

/-- **Sum lifts**: if two elements of K(E) lift to localRingAt P, their
sum does too. Direct from the strong triangle inequality. -/
theorem add_mem_localRingAt_image
    (P : (W_smooth W).SmoothPoint) {f g : (W_smooth W).FunctionField}
    (hf : (W_smooth W).pointValuation P f ≤ 1)
    (hg : (W_smooth W).pointValuation P g ≤ 1) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u =
        f + g := by
  apply Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one
  exact le_trans (((W_smooth W).pointValuation P).map_add _ _) (max_le hf hg)

/-- **Difference lifts**: if two elements of K(E) lift to localRingAt P,
their difference does too. -/
theorem sub_mem_localRingAt_image
    (P : (W_smooth W).SmoothPoint) {f g : (W_smooth W).FunctionField}
    (hf : (W_smooth W).pointValuation P f ≤ 1)
    (hg : (W_smooth W).pointValuation P g ≤ 1) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u =
        f - g := by
  apply Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one
  exact le_trans (((W_smooth W).pointValuation P).map_sub _ _) (max_le hf hg)

/-- **Product lifts**: if two elements lift to localRingAt P, their
product does too. -/
theorem mul_mem_localRingAt_image
    (P : (W_smooth W).SmoothPoint) {f g : (W_smooth W).FunctionField}
    (hf : (W_smooth W).pointValuation P f ≤ 1)
    (hg : (W_smooth W).pointValuation P g ≤ 1) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u =
        f * g := by
  apply Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one
  rw [Valuation.map_mul]
  exact mul_le_one' hf hg

/-- **Power lifts**: if `f` lifts to localRingAt P, then `f^n` does too. -/
theorem pow_mem_localRingAt_image
    (P : (W_smooth W).SmoothPoint) {f : (W_smooth W).FunctionField}
    (hf : (W_smooth W).pointValuation P f ≤ 1) (n : ℕ) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u =
        f ^ n := by
  apply Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one
  rw [Valuation.map_pow]
  exact pow_le_one' hf n

/-- **`x_gen W ^ n` lifts to localRingAt P** for any `n : ℕ`. -/
theorem x_gen_pow_mem_localRingAt_image
    (P : (W_smooth W).SmoothPoint) (n : ℕ) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u =
        x_gen W ^ n :=
  pow_mem_localRingAt_image W P (pointValuation_x_gen_le_one W P) n

/-- **`y_gen W ^ n` lifts to localRingAt P** for any `n : ℕ`. -/
theorem y_gen_pow_mem_localRingAt_image
    (P : (W_smooth W).SmoothPoint) (n : ℕ) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u =
        y_gen W ^ n :=
  pow_mem_localRingAt_image W P (pointValuation_y_gen_le_one W P) n

/-- **`(x_gen)^m * (y_gen)^n` lifts to localRingAt P**: monomial in x_gen,
y_gen with positive integer exponents. -/
theorem x_gen_pow_mul_y_gen_pow_mem_localRingAt_image
    (P : (W_smooth W).SmoothPoint) (m n : ℕ) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u =
        x_gen W ^ m * y_gen W ^ n := by
  apply Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one
  refine le_trans (le_of_eq (((W_smooth W).pointValuation P).map_mul _ _)) ?_
  exact mul_le_one'
    (le_trans (le_of_eq (((W_smooth W).pointValuation P).map_pow _ _))
      (pow_le_one' (pointValuation_x_gen_le_one W P) m))
    (le_trans (le_of_eq (((W_smooth W).pointValuation P).map_pow _ _))
      (pow_le_one' (pointValuation_y_gen_le_one W P) n))

/-- **`algMap c * (x_gen)^m * (y_gen)^n` lifts to localRingAt P**:
monomial with F-constant coefficient. -/
theorem algebraMap_F_mul_x_gen_pow_mul_y_gen_pow_mem_localRingAt_image
    (P : (W_smooth W).SmoothPoint) (c : F) (m n : ℕ) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u =
        algebraMap F KE c * x_gen W ^ m * y_gen W ^ n := by
  apply Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one
  refine le_trans (le_of_eq (((W_smooth W).pointValuation P).map_mul _ _)) ?_
  refine mul_le_one' ?_
    (le_trans (le_of_eq (((W_smooth W).pointValuation P).map_pow _ _))
      (pow_le_one' (pointValuation_y_gen_le_one W P) n))
  refine le_trans (le_of_eq (((W_smooth W).pointValuation P).map_mul _ _)) ?_
  exact mul_le_one'
    ((W_smooth W).pointValuation_algebraMap_F_le_one P c)
    (le_trans (le_of_eq (((W_smooth W).pointValuation P).map_pow _ _))
      (pow_le_one' (pointValuation_x_gen_le_one W P) m))

/-- **Zero lifts to localRingAt P**: trivially, 0 ∈ algMap '' localRingAt P. -/
theorem zero_mem_localRingAt_image (P : (W_smooth W).SmoothPoint) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u = 0 :=
  ⟨0, map_zero _⟩

/-- **One lifts to localRingAt P**: trivially, 1 ∈ algMap '' localRingAt P. -/
theorem one_mem_localRingAt_image (P : (W_smooth W).SmoothPoint) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u = 1 :=
  ⟨1, map_one _⟩

/-- **Negation lifts**: if `f` lifts to localRingAt P, so does `-f`. -/
theorem neg_mem_localRingAt_image
    (P : (W_smooth W).SmoothPoint) {f : (W_smooth W).FunctionField}
    (hf : (W_smooth W).pointValuation P f ≤ 1) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u =
        -f := by
  apply Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one
  rw [Valuation.map_neg]
  exact hf

/-! ### Strict (< 1) closure lemmas

For elements of valuation strictly less than 1 (i.e., in the maximal
ideal at P), we have closure under addition and multiplication-by-an
integer-element. -/

/-- **Multiplication: ≤ 1 * < 1 → < 1** (the < 1 factor dominates). -/
theorem pointValuation_mul_lt_one_of_le_and_lt
    (P : (W_smooth W).SmoothPoint) {f g : (W_smooth W).FunctionField}
    (hf : (W_smooth W).pointValuation P f ≤ 1)
    (hg : (W_smooth W).pointValuation P g < 1) :
    (W_smooth W).pointValuation P (f * g) < 1 := by
  rw [Valuation.map_mul]
  by_cases hf_zero : (W_smooth W).pointValuation P f = 0
  · rw [hf_zero, zero_mul]; exact zero_lt_one
  · have hf_pos : 0 < (W_smooth W).pointValuation P f := lt_of_le_of_ne
      (by exact zero_le') (Ne.symm hf_zero)
    calc _ ≤ 1 * (W_smooth W).pointValuation P g :=
            mul_le_mul_right' hf _
      _ = (W_smooth W).pointValuation P g := one_mul _
      _ < 1 := hg

/-! ### iff forms -/

/-- **iff form**: an element of K(E) lifts to localRingAt P iff it has
pointValuation ≤ 1. Restatement of the biconditional integer
characterisation `mem_localRingAt_image_iff_pointValuation_le_one`
(commit a1aa4d7). -/
theorem mem_localRingAt_image_iff_le_one
    (P : (W_smooth W).SmoothPoint) (f : (W_smooth W).FunctionField) :
    (∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u = f) ↔
    (W_smooth W).pointValuation P f ≤ 1 :=
  Curves.SmoothPlaneCurve.mem_localRingAt_image_iff_pointValuation_le_one f

/-- **algebraMap localRingAt P → KE is injective**: localRing → fraction
field. Direct via `IsFractionRing.injective`. -/
theorem algebraMap_localRingAt_injective (P : (W_smooth W).SmoothPoint) :
    Function.Injective
      (algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField) :=
  IsFractionRing.injective ((W_smooth W).localRingAt P) (W_smooth W).FunctionField

/-- **algebraMap CoordinateRing → KE images lift to localRingAt P**:
elements of the CoordinateRing always have ≤ 1 valuation, so their
images in K(E) lift. -/
theorem algebraMap_CoordinateRing_mem_localRingAt_image
    (P : (W_smooth W).SmoothPoint) (r : (W_smooth W).CoordinateRing) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u =
        algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField r :=
  Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one
    _ ((W_smooth W).pointValuation_algebraMap_le_one r P)

/-- **`x_gen W ^ n - algMap c` lifts to localRingAt P**: any power of x_gen
shifted by an F-constant lifts. -/
theorem x_gen_pow_sub_const_mem_localRingAt_image
    (P : (W_smooth W).SmoothPoint) (n : ℕ) (c : F) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u =
        x_gen W ^ n - algebraMap F KE c := by
  apply Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one
  refine le_trans (((W_smooth W).pointValuation P).map_sub _ _) ?_
  exact max_le
    (le_trans (le_of_eq (((W_smooth W).pointValuation P).map_pow _ _))
      (pow_le_one' (pointValuation_x_gen_le_one W P) n))
    ((W_smooth W).pointValuation_algebraMap_F_le_one P c)

/-- **`y_gen W ^ n - algMap c` lifts to localRingAt P**: companion. -/
theorem y_gen_pow_sub_const_mem_localRingAt_image
    (P : (W_smooth W).SmoothPoint) (n : ℕ) (c : F) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u =
        y_gen W ^ n - algebraMap F KE c := by
  apply Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one
  refine le_trans (((W_smooth W).pointValuation P).map_sub _ _) ?_
  exact max_le
    (le_trans (le_of_eq (((W_smooth W).pointValuation P).map_pow _ _))
      (pow_le_one' (pointValuation_y_gen_le_one W P) n))
    ((W_smooth W).pointValuation_algebraMap_F_le_one P c)

/-! ### Direct valuation bounds (≤ 1 forms without lifts) -/

/-- **Sum bound**: if `f, g` have valuation ≤ 1, so does `f + g`. -/
theorem pointValuation_add_le_one
    (P : (W_smooth W).SmoothPoint) {f g : (W_smooth W).FunctionField}
    (hf : (W_smooth W).pointValuation P f ≤ 1)
    (hg : (W_smooth W).pointValuation P g ≤ 1) :
    (W_smooth W).pointValuation P (f + g) ≤ 1 :=
  le_trans (((W_smooth W).pointValuation P).map_add _ _) (max_le hf hg)

/-- **Difference bound**: if `f, g` have valuation ≤ 1, so does `f - g`. -/
theorem pointValuation_sub_le_one
    (P : (W_smooth W).SmoothPoint) {f g : (W_smooth W).FunctionField}
    (hf : (W_smooth W).pointValuation P f ≤ 1)
    (hg : (W_smooth W).pointValuation P g ≤ 1) :
    (W_smooth W).pointValuation P (f - g) ≤ 1 :=
  le_trans (((W_smooth W).pointValuation P).map_sub _ _) (max_le hf hg)

/-- **Product bound**: if `f, g` have valuation ≤ 1, so does `f * g`. -/
theorem pointValuation_mul_le_one
    (P : (W_smooth W).SmoothPoint) {f g : (W_smooth W).FunctionField}
    (hf : (W_smooth W).pointValuation P f ≤ 1)
    (hg : (W_smooth W).pointValuation P g ≤ 1) :
    (W_smooth W).pointValuation P (f * g) ≤ 1 := by
  rw [Valuation.map_mul]
  exact mul_le_one' hf hg

/-- **Power bound**: if `f` has valuation ≤ 1, so does `f^n`. -/
theorem pointValuation_pow_le_one
    (P : (W_smooth W).SmoothPoint) {f : (W_smooth W).FunctionField}
    (hf : (W_smooth W).pointValuation P f ≤ 1) (n : ℕ) :
    (W_smooth W).pointValuation P (f ^ n) ≤ 1 := by
  rw [Valuation.map_pow]
  exact pow_le_one' hf n

/-- **Negation bound**: if `f` has valuation ≤ 1, so does `-f`. -/
theorem pointValuation_neg_le_one
    (P : (W_smooth W).SmoothPoint) {f : (W_smooth W).FunctionField}
    (hf : (W_smooth W).pointValuation P f ≤ 1) :
    (W_smooth W).pointValuation P (-f) ≤ 1 := by
  rw [Valuation.map_neg]
  exact hf

/-! ### Linear combinations of generators -/

/-- **`a · x_gen + b · y_gen + c` has valuation ≤ 1** for any constants
`a, b, c : F`. -/
theorem pointValuation_linear_combination_le_one
    (P : (W_smooth W).SmoothPoint) (a b c : F) :
    (W_smooth W).pointValuation P
        (algebraMap F KE a * x_gen W + algebraMap F KE b * y_gen W +
          algebraMap F KE c) ≤ 1 := by
  apply pointValuation_add_le_one W P
  · apply pointValuation_add_le_one W P
    · exact pointValuation_mul_le_one W P
        ((W_smooth W).pointValuation_algebraMap_F_le_one P a)
        (pointValuation_x_gen_le_one W P)
    · exact pointValuation_mul_le_one W P
        ((W_smooth W).pointValuation_algebraMap_F_le_one P b)
        (pointValuation_y_gen_le_one W P)
  · exact (W_smooth W).pointValuation_algebraMap_F_le_one P c

/-- **Linear combination lifts**: companion lift form. -/
theorem linear_combination_mem_localRingAt_image
    (P : (W_smooth W).SmoothPoint) (a b c : F) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u =
        algebraMap F KE a * x_gen W + algebraMap F KE b * y_gen W +
          algebraMap F KE c :=
  Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one _
    (pointValuation_linear_combination_le_one W P a b c)

/-! ### Negation forms -/

/-- **`-x_gen + algMap c` lifts**: companion of `x_gen - algMap c` lift. -/
theorem neg_x_gen_add_const_mem_localRingAt_image
    (P : (W_smooth W).SmoothPoint) (c : F) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u =
        -(x_gen W) + algebraMap F KE c := by
  apply Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one
  apply pointValuation_add_le_one W P
  · exact pointValuation_neg_le_one W P (pointValuation_x_gen_le_one W P)
  · exact (W_smooth W).pointValuation_algebraMap_F_le_one P c

/-- **`algMap c - x_gen` lifts**: by ring rearrangement, equivalent to
`-(x_gen - algMap c)`. -/
theorem const_sub_x_gen_mem_localRingAt_image
    (P : (W_smooth W).SmoothPoint) (c : F) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u =
        algebraMap F KE c - x_gen W := by
  apply Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one
  apply pointValuation_sub_le_one
  · exact (W_smooth W).pointValuation_algebraMap_F_le_one P c
  · exact pointValuation_x_gen_le_one W P

/-- **`algMap c - y_gen` lifts**: companion. -/
theorem const_sub_y_gen_mem_localRingAt_image
    (P : (W_smooth W).SmoothPoint) (c : F) :
    ∃ u : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField u =
        algebraMap F KE c - y_gen W := by
  apply Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one
  apply pointValuation_sub_le_one
  · exact (W_smooth W).pointValuation_algebraMap_F_le_one P c
  · exact pointValuation_y_gen_le_one W P

end HasseWeil

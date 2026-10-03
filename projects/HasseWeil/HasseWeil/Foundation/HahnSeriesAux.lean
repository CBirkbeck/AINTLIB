/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.LaurentSeries

/-!
# Auxiliary order and leading coefficient lemmas for Hahn series

This file contains auxiliary lemmas for orders and leading coefficients of inverses and
quotients of Hahn series.

* `HahnSeries.orderTop_inv_eq_neg` — `(s⁻¹).orderTop = −s.orderTop` for
  nonzero `s` in a HahnSeries over a field.
* `HahnSeries.orderTop_div` — the division analogue.
* `HahnSeries.leadingCoeff_inv` — the leading coefficient analogue for inverses.
* `HahnSeries.leadingCoeff_div` — the leading coefficient analogue for quotients.
-/

@[expose] public section

namespace HahnSeries

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
variable {R : Type*} [Field R]

/-- The order top of the inverse of a nonzero Hahn series is the negation of the original
order top. -/
theorem orderTop_inv_eq_neg {s : HahnSeries Γ R} (hs : s ≠ 0) :
    s⁻¹.orderTop = -s.orderTop := by
  have hs_inv : s⁻¹ ≠ 0 := inv_ne_zero hs
  have h_mul_one : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  have h_ord_mul : (s * s⁻¹).orderTop = s.orderTop + s⁻¹.orderTop :=
    HahnSeries.orderTop_mul s s⁻¹
  rw [h_mul_one, HahnSeries.orderTop_one] at h_ord_mul
  have hs_ord : s.orderTop ≠ ⊤ := HahnSeries.orderTop_ne_top.mpr hs
  have hs_inv_ord : s⁻¹.orderTop ≠ ⊤ := HahnSeries.orderTop_ne_top.mpr hs_inv
  lift s.orderTop to Γ using hs_ord with a ha
  lift s⁻¹.orderTop to Γ using hs_inv_ord with b hb
  rw [← WithTop.coe_add, show (0 : WithTop Γ) = ((0 : Γ) : WithTop Γ) from rfl,
      WithTop.coe_eq_coe] at h_ord_mul
  have hab : b = -a := by
    have h1 : a + b = 0 := h_ord_mul.symm
    have h2 : b + a = 0 := by
      rw [add_comm]
      exact h1
    exact eq_neg_of_add_eq_zero_left h2
  rw [hab]
  rfl

/-- The order top of a quotient of Hahn series is the difference of the order tops. -/
theorem orderTop_div {s t : HahnSeries Γ R} (ht : t ≠ 0) :
    (s / t).orderTop = s.orderTop - t.orderTop := by
  rw [div_eq_mul_inv, HahnSeries.orderTop_mul s t⁻¹, orderTop_inv_eq_neg ht,
      sub_eq_add_neg]

/-- The leading coefficient of the inverse of a Hahn series is the inverse of the leading
coefficient. -/
theorem leadingCoeff_inv {s : HahnSeries Γ R} (hs : s ≠ 0) :
    s⁻¹.leadingCoeff = s.leadingCoeff⁻¹ := by
  have h_mul_one : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  have h_lead_mul : (s * s⁻¹).leadingCoeff = s.leadingCoeff * s⁻¹.leadingCoeff :=
    HahnSeries.leadingCoeff_mul s s⁻¹
  rw [h_mul_one, HahnSeries.leadingCoeff_one] at h_lead_mul
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm, ← h_lead_mul])

/-- The leading coefficient of a quotient of Hahn series is the quotient of the leading
coefficients. -/
theorem leadingCoeff_div {s t : HahnSeries Γ R} (ht : t ≠ 0) :
    (s / t).leadingCoeff = s.leadingCoeff / t.leadingCoeff := by
  rw [div_eq_mul_inv, HahnSeries.leadingCoeff_mul, leadingCoeff_inv ht,
      div_eq_mul_inv]

end HahnSeries

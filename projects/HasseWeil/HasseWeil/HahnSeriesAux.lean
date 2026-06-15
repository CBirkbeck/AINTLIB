import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.LaurentSeries

/-!
# Auxiliary orderTop lemmas for HahnSeries (mathlib upstream candidates)

This file contains orderTop lemmas for HahnSeries that are missing from
mathlib as of this writing:

* `HahnSeries.orderTop_inv_eq_neg` — `(s⁻¹).orderTop = −s.orderTop` for
  nonzero `s` in a HahnSeries over a field.
* `HahnSeries.orderTop_div` — the division analogue.

Both are standard results: division in a HahnSeries field inverts the
leading coefficient and negates the order. Derived from `orderTop_mul` +
`orderTop_one`.

TODO: upstream to `Mathlib.RingTheory.HahnSeries.Multiplication` proper.
-/

namespace HahnSeries

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
variable {R : Type*} [Field R]

/-- The orderTop of the inverse of a nonzero Hahn series over a field
    equals the negation of the original orderTop.

    Proof: from `s · s⁻¹ = 1`, both sides have orderTop `0`; using
    `orderTop_mul` this gives `s.orderTop + (s⁻¹).orderTop = 0`, so
    `(s⁻¹).orderTop = -s.orderTop`. -/
theorem orderTop_inv_eq_neg {s : HahnSeries Γ R} (hs : s ≠ 0) :
    s⁻¹.orderTop = -s.orderTop := by
  have hs_inv : s⁻¹ ≠ 0 := inv_ne_zero hs
  have h_mul_one : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  have h_ord_mul : (s * s⁻¹).orderTop = s.orderTop + s⁻¹.orderTop :=
    HahnSeries.orderTop_mul s s⁻¹
  rw [h_mul_one, HahnSeries.orderTop_one] at h_ord_mul
  -- h_ord_mul : 0 = s.orderTop + s⁻¹.orderTop
  have hs_ord : s.orderTop ≠ ⊤ := HahnSeries.orderTop_ne_top.mpr hs
  have hs_inv_ord : s⁻¹.orderTop ≠ ⊤ := HahnSeries.orderTop_ne_top.mpr hs_inv
  lift s.orderTop to Γ using hs_ord with a ha
  lift s⁻¹.orderTop to Γ using hs_inv_ord with b hb
  rw [← WithTop.coe_add, show (0 : WithTop Γ) = ((0 : Γ) : WithTop Γ) from rfl,
      WithTop.coe_eq_coe] at h_ord_mul
  -- h_ord_mul : 0 = a + b  in Γ
  have hab : b = -a := by
    have h1 : a + b = 0 := h_ord_mul.symm
    have h2 : b + a = 0 := by rw [add_comm]; exact h1
    exact eq_neg_of_add_eq_zero_left h2
  rw [hab]; rfl

/-- The orderTop of a quotient in a HahnSeries field is the difference
    of orderTops.

    Proof: `s / t = s · t⁻¹`, then use `orderTop_mul` + `orderTop_inv_eq_neg`. -/
theorem orderTop_div {s t : HahnSeries Γ R} (ht : t ≠ 0) :
    (s / t).orderTop = s.orderTop - t.orderTop := by
  rw [div_eq_mul_inv, HahnSeries.orderTop_mul s t⁻¹, orderTop_inv_eq_neg ht,
      sub_eq_add_neg]

/-- The leading coefficient of the inverse is the inverse of the leading
    coefficient, over a HahnSeries field.

    Proof: `s · s⁻¹ = 1`, so `s.leadingCoeff * s⁻¹.leadingCoeff = 1` (via
    `leadingCoeff_mul` for NoZeroDivisors fields); solve for `s⁻¹.leadingCoeff`. -/
theorem leadingCoeff_inv {s : HahnSeries Γ R} (hs : s ≠ 0) :
    s⁻¹.leadingCoeff = s.leadingCoeff⁻¹ := by
  have h_mul_one : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  have h_lead_mul : (s * s⁻¹).leadingCoeff = s.leadingCoeff * s⁻¹.leadingCoeff :=
    HahnSeries.leadingCoeff_mul s s⁻¹
  rw [h_mul_one, HahnSeries.leadingCoeff_one] at h_lead_mul
  -- h_lead_mul : 1 = s.leadingCoeff * s⁻¹.leadingCoeff
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm, ← h_lead_mul])

/-- The leading coefficient of a quotient in a HahnSeries field is the
    quotient of leading coefficients.

    Proof: `s / t = s · t⁻¹`, then use `leadingCoeff_mul` + `leadingCoeff_inv`. -/
theorem leadingCoeff_div {s t : HahnSeries Γ R} (ht : t ≠ 0) :
    (s / t).leadingCoeff = s.leadingCoeff / t.leadingCoeff := by
  rw [div_eq_mul_inv, HahnSeries.leadingCoeff_mul, leadingCoeff_inv ht,
      div_eq_mul_inv]

end HahnSeries

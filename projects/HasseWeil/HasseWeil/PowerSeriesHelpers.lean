import Mathlib.RingTheory.PowerSeries.Order

/-!
# Auxiliary lemmas for `PowerSeries`

This file collects power-series lemmas that are used across the Hasse–Weil
development but are not yet available in mathlib. Each lemma is stated at
maximum generality (the weakest typeclass the proof needs).

## Main result

* `PowerSeries.eq_zero_of_self_eq_mul_self` — if `f = g * f` in `R⟦X⟧` and
  `g` has zero constant coefficient, then `f = 0`. This is a self-multiplication
  cancellation lemma derived from the order valuation: `order (g * f) ≥
  order g + order f ≥ 1 + order f`, forcing `order f = ⊤` and hence `f = 0`.

Used by formal-group uniqueness arguments, e.g. `formalW_unique`
(Silverman IV.1.1(b)), where the hypothesis `f = g · f` arises by factoring
a difference of Weierstrass recurrences.
-/

namespace PowerSeries

variable {R : Type*} [Semiring R]

/-- **Self-multiplication cancellation**: if `f = g * f` in `R⟦X⟧` and the
constant coefficient of `g` is zero, then `f = 0`.

Derived from the order valuation: `1 ≤ order g` combined with
`order g + order f ≤ order (g * f) = order f` forces `order f = ⊤`. -/
theorem eq_zero_of_self_eq_mul_self {f g : R⟦X⟧}
    (hg : constantCoeff g = 0) (h : f = g * f) : f = 0 := by
  by_contra hf
  have hg_order : (1 : ℕ∞) ≤ g.order := one_le_order_iff_constCoeff_eq_zero.mpr hg
  have h_absurd : f.order + 1 ≤ f.order :=
    calc f.order + 1 = 1 + f.order := by rw [add_comm]
      _ ≤ g.order + f.order := by gcongr
      _ ≤ (g * f).order := le_order_mul g f
      _ = f.order := (congrArg _ h).symm
  exact absurd ((ENat.add_one_le_iff <| order_eq_top.not.mpr hf).mp h_absurd)
    (lt_irrefl _)

/-- Commutative variant: if `f = f * g` and `constantCoeff g = 0`, then `f = 0`.
Follows from `eq_zero_of_self_eq_mul_self` by commuting the multiplication. -/
theorem eq_zero_of_self_eq_self_mul {R : Type*} [CommSemiring R]
    {f g : R⟦X⟧} (hg : constantCoeff g = 0) (h : f = f * g) : f = 0 :=
  eq_zero_of_self_eq_mul_self hg (h.trans (mul_comm f g))

end PowerSeries

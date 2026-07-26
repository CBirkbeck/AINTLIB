/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.StandardSmoothHypersurface
import ModularCurves.Moduli.UniversalLevelThree

/-!
# The `ℰ₃` moduli scheme is smooth of relative dimension one

`E3ModuliRing R = R[β, γ][((a₁³−27a₃)a₃γ)⁻¹] / (β³ − (β+γ)³)` is a **localized
hypersurface**, so `ForMathlib/StandardSmoothHypersurface.lean` applies once the relevant
partial derivative is inverted. The Jacobian bookkeeping:

* `f = β³ − (β+γ)³`, hence `∂f/∂γ = −3(β+γ)²`;
* the flex relation is `γ·(3β² + 3βγ + γ²) = 0`, which gives
  `(β+γ) · (3γ² − 3(β+γ)γ) = γ³`, i.e. **`β+γ` divides `γ³`**;
* `γ` divides `e3Delta`, so `β+γ` divides `e3Delta³` and is therefore a **unit** in
  `E3ModuliRing`; with `3` invertible, so is `∂f/∂γ`.

This is the level-`3` counterpart of `Moduli/LegendreSmooth.lean`, and it is what lets the
`Y(ρ̄)` smoothness leaf run on the (axiom-clean) level-`3` rigidifier instead of the
Legendre one.
-/

noncomputable section

universe u

open MvPolynomial

namespace ModularCurves

variable (R : CommRingCat.{u})

/-- The image of `β + γ` in the flex-locus ring. -/
def e3S : E3Quotient R :=
  Ideal.Quotient.mk _ (X 0 + X 1)

/-- **(brick 1a)** The flex relation forces `β + γ` to divide `γ³`:
`(β+γ)·(3γ² − 3(β+γ)γ) = γ³` in `R[β,γ]/(β³ − (β+γ)³)`. -/
theorem e3S_mul_eq_gamma_cube :
    e3S R * (3 * (Ideal.Quotient.mk _ (X 1) : E3Quotient R) ^ 2 -
        3 * e3S R * Ideal.Quotient.mk _ (X 1)) =
      (Ideal.Quotient.mk _ (X 1) : E3Quotient R) ^ 3 := by
  have hrel : (Ideal.Quotient.mk (Ideal.span {e3Rel R}) (e3Rel R) : E3Quotient R) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hrel' : ((Ideal.Quotient.mk (Ideal.span {e3Rel R}) (X 0) : E3Quotient R) ^ 3 -
      (Ideal.Quotient.mk (Ideal.span {e3Rel R}) (X 0) +
        Ideal.Quotient.mk (Ideal.span {e3Rel R}) (X 1)) ^ 3) = 0 := by
    rw [← hrel, e3Rel]
    push_cast
    simp only [map_sub, map_pow, map_add]
  show _ = _
  simp only [e3S, map_add]
  linear_combination hrel'

/-- **(brick 1b)** `β + γ` divides `e3Delta³` (since it divides `γ³` and `γ` divides
`e3Delta`). -/
theorem e3S_dvd_e3Delta_pow : e3S R ∣ (e3Delta R) ^ 3 := by
  refine ⟨(3 * (Ideal.Quotient.mk _ (X 1) : E3Quotient R) ^ 2 -
      3 * e3S R * Ideal.Quotient.mk _ (X 1)) *
    (Ideal.Quotient.mk _ ((e3A₁Poly R ^ 3 - 27 * e3A₃Poly R) * e3A₃Poly R) :
      E3Quotient R) ^ 3, ?_⟩
  rw [e3Delta, show ((Ideal.Quotient.mk (Ideal.span {e3Rel R})
      ((e3A₁Poly R ^ 3 - 27 * e3A₃Poly R) * e3A₃Poly R * X 1) : E3Quotient R)) ^ 3 =
    ((Ideal.Quotient.mk (Ideal.span {e3Rel R})
      ((e3A₁Poly R ^ 3 - 27 * e3A₃Poly R) * e3A₃Poly R) : E3Quotient R)) ^ 3 *
    ((Ideal.Quotient.mk (Ideal.span {e3Rel R}) (X 1) : E3Quotient R)) ^ 3 from by
    rw [map_mul, mul_pow], ← e3S_mul_eq_gamma_cube R]
  ring

/-- **(brick 1b)** `β + γ` is a **unit** in `E3ModuliRing`. -/
theorem isUnit_e3S_map :
    IsUnit (algebraMap (E3Quotient R) (E3ModuliRing R) (e3S R)) := by
  refine isUnit_of_dvd_unit (map_dvd _ (e3S_dvd_e3Delta_pow R)) ?_
  rw [map_pow]
  exact (IsLocalization.Away.algebraMap_isUnit (S := E3ModuliRing R) (e3Delta R)).pow 3

end ModularCurves

end

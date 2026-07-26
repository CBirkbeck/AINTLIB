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

/-- **(brick 1c)** The Jacobian entry: `∂/∂γ (β³ − (β+γ)³) = −3(β+γ)²`. -/
theorem pderiv_one_e3Rel :
    pderiv 1 (e3Rel R) = -3 * (X 0 + X 1) ^ 2 := by
  simp only [e3Rel, map_sub, pderiv_pow, pderiv_X, map_add, Pi.single_apply]
  norm_num

/-- **(brick 1c)** Hence the Jacobian entry is a **unit** in `E3ModuliRing` once `3` is
invertible. -/
theorem isUnit_pderiv_e3Rel_map (hR : IsUnit (3 : R)) :
    IsUnit (algebraMap (E3Quotient R) (E3ModuliRing R)
      (Ideal.Quotient.mk _ (pderiv 1 (e3Rel R)))) := by
  have h3 : IsUnit (algebraMap (E3Quotient R) (E3ModuliRing R)
      (Ideal.Quotient.mk (Ideal.span {e3Rel R}) (3 : MvPolynomial (Fin 2) R))) := by
    have := ((hR.map (algebraMap R (MvPolynomial (Fin 2) R))).map
      (Ideal.Quotient.mk (Ideal.span {e3Rel R}))).map
      (algebraMap (E3Quotient R) (E3ModuliRing R))
    rwa [show (algebraMap R (MvPolynomial (Fin 2) R)) 3 = 3 from map_ofNat _ 3] at this
  rw [pderiv_one_e3Rel]
  have hval : (Ideal.Quotient.mk (Ideal.span {e3Rel R})
      (-3 * (X 0 + X 1) ^ 2 : MvPolynomial (Fin 2) R)) =
      -(Ideal.Quotient.mk (Ideal.span {e3Rel R}) (3 : MvPolynomial (Fin 2) R)) *
        (e3S R) ^ 2 := by
    rw [e3S]
    push_cast
    simp only [map_mul, map_neg, map_pow, map_add]
  rw [hval, map_mul, map_neg, map_pow]
  exact ((h3.neg).mul ((isUnit_e3S_map R).pow 2))

/-- **(brick 1d)** `E3ModuliRing R` is *also* the localization away from
`e3Delta · ∂f/∂γ` (the extra factor is already a unit there). -/
theorem isLocalization_away_e3Delta_mul_pderiv (hR : IsUnit (3 : R)) :
    IsLocalization.Away (e3Delta R *
      Ideal.Quotient.mk (Ideal.span {e3Rel R}) (pderiv 1 (e3Rel R))) (E3ModuliRing R) := by
  set p : E3Quotient R := Ideal.Quotient.mk (Ideal.span {e3Rel R}) (pderiv 1 (e3Rel R)) with hp
  have hpu : IsUnit (algebraMap (E3Quotient R) (E3ModuliRing R) p) :=
    isUnit_pderiv_e3Rel_map R hR
  refine IsLocalization.Away.mk _ ?_ (fun z => ?_) (fun a b h => ?_)
  · rw [map_mul]
    exact (IsLocalization.Away.algebraMap_isUnit (S := E3ModuliRing R) (e3Delta R)).mul hpu
  · obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (S := E3ModuliRing R) (e3Delta R) z
    refine ⟨n, a * p ^ n, ?_⟩
    simp only [map_mul, map_pow]
    rw [mul_pow, ← mul_assoc, ha]
  · obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (S := E3ModuliRing R)
      (x := e3Delta R) h
    refine ⟨n, ?_⟩
    calc (e3Delta R * p) ^ n * a = p ^ n * ((e3Delta R) ^ n * a) := by rw [mul_pow]; ring
      _ = p ^ n * ((e3Delta R) ^ n * b) := by rw [hn]
      _ = (e3Delta R * p) ^ n * b := by rw [mul_pow]; ring

end ModularCurves

end

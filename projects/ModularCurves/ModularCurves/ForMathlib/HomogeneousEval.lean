/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Evaluating a homogeneous polynomial on a rescaled point (ForMathlib)

`MvPolynomial.IsHomogeneous.eval₂_mul_left`: for `φ` homogeneous of degree `n`,
`eval₂ f (c * g ·) φ = c ^ n * eval₂ f g φ`. Mathlib has the homogeneity API and the
`eval₂_eq` monomial expansion but no scaling lemma; this is the missing link between the two,
and it is the reason a projective triple satisfying a homogeneous equation still satisfies the
dehomogenised equation after dividing by an invertible coordinate.

Upstream candidate.
-/

open Finset

namespace MvPolynomial.IsHomogeneous

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S]

/-- Evaluating a homogeneous polynomial of degree `n` at a rescaled point multiplies the value
by `c ^ n`. -/
theorem eval₂_mul_left {φ : MvPolynomial σ R} {n : ℕ} (hφ : φ.IsHomogeneous n)
    (f : R →+* S) (g : σ → S) (c : S) :
    MvPolynomial.eval₂ f (fun i => c * g i) φ = c ^ n * MvPolynomial.eval₂ f g φ := by
  classical
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : n = ∑ i ∈ d.support, d i := hφ.degree_eq_sum_deg_support hd
  calc f (coeff d φ) * ∏ i ∈ d.support, (c * g i) ^ d i
      = f (coeff d φ) * ((∏ i ∈ d.support, c ^ d i) * ∏ i ∈ d.support, g i ^ d i) := by
        simp_rw [mul_pow]
        rw [Finset.prod_mul_distrib]
    _ = c ^ n * (f (coeff d φ) * ∏ i ∈ d.support, g i ^ d i) := by
        rw [Finset.prod_pow_eq_pow_sum, ← hdeg]
        ring

/-- The `aeval` form of `eval₂_mul_left`. -/
theorem aeval_mul_left [Algebra R S] {φ : MvPolynomial σ R} {n : ℕ} (hφ : φ.IsHomogeneous n)
    (g : σ → S) (c : S) :
    MvPolynomial.aeval (fun i => c * g i) φ = c ^ n * MvPolynomial.aeval g φ :=
  hφ.eval₂_mul_left (algebraMap R S) g c

end MvPolynomial.IsHomogeneous

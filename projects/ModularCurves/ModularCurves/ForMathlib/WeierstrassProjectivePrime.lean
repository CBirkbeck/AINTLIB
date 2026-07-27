/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Prime

import ModularCurves.EllipticCurve.WeierstrassModel

/-!
# The projective Weierstrass cubic is prime

For a Weierstrass curve `W` over a field `K`, the homogeneous Weierstrass polynomial
`W(X, Y, Z) = Y²Z + a₁XYZ + a₃YZ² − (X³ + a₂X²Z + a₄XZ² + a₆Z³)` is prime in
`MvPolynomial (Fin 3) K`. Consequently the projective coordinate ring
`ModularCurves.projCoordRing W = K[X,Y,Z] / (W)` is an integral domain.

## Main results

* `WeierstrassCurve.projective_polynomial_prime`: `W.toProjective.polynomial` is prime.
* the `IsDomain (ModularCurves.projCoordRing W)` instance.

## Strategy

Extract the variable `X = X 0` via `MvPolynomial.finSuccEquiv K 2`, viewing the cubic as a
polynomial in `X` over `S := MvPolynomial (Fin 2) K` (whose generators `X 0, X 1` play the
roles of `Y` and `Z`). Up to sign this image is the **monic** cubic

  `Gm = X³ + C(a₂·Z)·X² + C(a₄·Z² − a₁·Y·Z)·X
    + C(a₆·Z³ − a₃·Y·Z² − Y²·Z)`,

which is **Eisenstein at the prime `Z = X 1`** of `S`: the lower coefficients are all
divisible by `Z`, and the constant coefficient `Z·(a₆Z² − a₃YZ − Y²)` is not divisible by
`Z²` because `Z ∤ Y²`. Hence `Gm` is irreducible (`Polynomial.IsEisensteinAt.irreducible`),
hence prime (`S[X]` is a UFD), hence so is its unit multiple `finSuccEquiv K 2 (W.polynomial)`,
hence — transporting along the ring isomorphism `finSuccEquiv` — so is `W.polynomial`.

The argument is independent of `a₁, …, a₆` and of any discriminant/ellipticity hypothesis.
-/

open scoped Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve

private theorem weierstrass_constant_not_mem_span_X_sq_aux {K : Type*} [Field K]
    (W : WeierstrassCurve K) (b0 : MvPolynomial (Fin 2) K)
    (hb0 : b0 = MvPolynomial.C W.a₆ * MvPolynomial.X 1 ^ 3
        - MvPolynomial.C W.a₃ * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2
        - MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1) :
    b0 ∉ (Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}) ^ 2 := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  intro hdvd
  have hXne : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ≠ 0 := MvPolynomial.X_ne_zero 1
  have hXprime : Prime (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) :=
    MvPolynomial.X_prime
  have key : (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^ 2 * MvPolynomial.X 1 =
      MvPolynomial.X 1 ^ 2 * (MvPolynomial.C W.a₆ * MvPolynomial.X 1
        - MvPolynomial.C W.a₃ * MvPolynomial.X 0) - b0 := by
    rw [hb0]
    ring
  have hdvd2 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ 2 ∣
      MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 := by
    rw [key]
    exact dvd_sub (dvd_mul_right _ _) hdvd
  rw [mul_comm ((MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^ 2) (MvPolynomial.X 1),
    pow_two (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K),
    mul_dvd_mul_iff_left hXne] at hdvd2
  have hcontra : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ∣ MvPolynomial.X 0 :=
    hXprime.dvd_of_dvd_pow hdvd2
  rw [MvPolynomial.X_dvd_X] at hcontra
  exact absurd hcontra (by decide)

private theorem monic_weierstrass_cubic_prime_aux {K : Type*} [Field K]
    (W : WeierstrassCurve K) (b0 b1 b2 : MvPolynomial (Fin 2) K)
    (hb0 : b0 = MvPolynomial.C W.a₆ * MvPolynomial.X 1 ^ 3
        - MvPolynomial.C W.a₃ * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2
        - MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1)
    (hb1 : b1 = MvPolynomial.C W.a₄ * MvPolynomial.X 1 ^ 2
        - MvPolynomial.C W.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1)
    (hb2 : b2 = MvPolynomial.C W.a₂ * MvPolynomial.X 1) :
    Prime (Polynomial.X ^ 3 + Polynomial.C b2 * Polynomial.X ^ 2
      + Polynomial.C b1 * Polynomial.X + Polynomial.C b0) := by
  set Gm : (MvPolynomial (Fin 2) K)[X] :=
    Polynomial.X ^ 3 + Polynomial.C b2 * Polynomial.X ^ 2
      + Polynomial.C b1 * Polynomial.X + Polynomial.C b0 with hGm
  have hmonic : Gm.Monic := by
    rw [hGm]
    monicity!
  have hdeg : Gm.natDegree = 3 := by
    rw [hGm]
    compute_degree!
  have hc0 : Gm.coeff 0 = b0 := by
    rw [hGm]
    simp
  have hc1 : Gm.coeff 1 = b1 := by
    rw [hGm]
    simp
  have hc2 : Gm.coeff 2 = b2 := by
    rw [hGm]
    simp
  have hXne : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ≠ 0 := MvPolynomial.X_ne_zero 1
  have hXprime : Prime (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) :=
    MvPolynomial.X_prime
  have hPprime : (Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}).IsPrime :=
    (Ideal.span_singleton_prime hXne).mpr hXprime
  have hEis : Gm.IsEisensteinAt (Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hmonic]
      exact (Ideal.ne_top_iff_one _).mp hPprime.ne_top
    · intro n hn
      rw [hdeg] at hn
      interval_cases n
      · rw [hc0]
        exact Ideal.mem_span_singleton.mpr ⟨MvPolynomial.C W.a₆ * MvPolynomial.X 1 ^ 2
          - MvPolynomial.C W.a₃ * MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.X 0 ^ 2,
          by
            rw [hb0]
            ring⟩
      · rw [hc1]
        exact Ideal.mem_span_singleton.mpr ⟨MvPolynomial.C W.a₄ * MvPolynomial.X 1
          - MvPolynomial.C W.a₁ * MvPolynomial.X 0,
          by
            rw [hb1]
            ring⟩
      · rw [hc2]
        exact Ideal.mem_span_singleton.mpr ⟨MvPolynomial.C W.a₂,
          by
            rw [hb2]
            ring⟩
    · rw [hc0]
      exact weierstrass_constant_not_mem_span_X_sq_aux W b0 hb0
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp <|
    hEis.irreducible hPprime hmonic.isPrimitive (by simp [hdeg])

private theorem finSuccEquiv_projective_polynomial_aux {K : Type*} [Field K]
    (W : WeierstrassCurve K) (b0 b1 b2 : MvPolynomial (Fin 2) K)
    (hb0 : b0 = MvPolynomial.C W.a₆ * MvPolynomial.X 1 ^ 3
        - MvPolynomial.C W.a₃ * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2
        - MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1)
    (hb1 : b1 = MvPolynomial.C W.a₄ * MvPolynomial.X 1 ^ 2
        - MvPolynomial.C W.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1)
    (hb2 : b2 = MvPolynomial.C W.a₂ * MvPolynomial.X 1) :
    MvPolynomial.finSuccEquiv K 2 W.toProjective.polynomial =
      -(Polynomial.X ^ 3 + Polynomial.C b2 * Polynomial.X ^ 2
        + Polynomial.C b1 * Polynomial.X + Polynomial.C b0) := by
  have hX1 : MvPolynomial.finSuccEquiv K 2 (MvPolynomial.X 1) =
      Polynomial.C (MvPolynomial.X 0) := by
    rw [show (1 : Fin 3) = (0 : Fin 2).succ by decide]
    exact MvPolynomial.finSuccEquiv_X_succ
  have hX2 : MvPolynomial.finSuccEquiv K 2 (MvPolynomial.X 2) =
      Polynomial.C (MvPolynomial.X 1) := by
    rw [show (2 : Fin 3) = (1 : Fin 2).succ by decide]
    exact MvPolynomial.finSuccEquiv_X_succ
  have hC : ∀ a : K, MvPolynomial.finSuccEquiv K 2 (MvPolynomial.C a) =
      Polynomial.C (MvPolynomial.C a) := by
    intro a
    rw [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]
    rfl
  simp only [hb0, hb1, hb2, WeierstrassCurve.Projective.polynomial, map_add, map_sub,
    map_mul, map_pow, MvPolynomial.finSuccEquiv_X_zero, hX1, hX2, hC]
  ring

/-- **The projective Weierstrass cubic is prime.** For any Weierstrass curve `W` over a
field `K`, the homogeneous Weierstrass polynomial `W.toProjective.polynomial` is a prime
element of `MvPolynomial (Fin 3) K`. No ellipticity or discriminant hypothesis is needed. -/
theorem projective_polynomial_prime {K : Type*} [Field K] (W : WeierstrassCurve K) :
    Prime W.toProjective.polynomial := by
  set b2 : MvPolynomial (Fin 2) K := MvPolynomial.C W.a₂ * MvPolynomial.X 1 with hb2
  set b1 : MvPolynomial (Fin 2) K := MvPolynomial.C W.a₄ * MvPolynomial.X 1 ^ 2
      - MvPolynomial.C W.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1 with hb1
  set b0 : MvPolynomial (Fin 2) K := MvPolynomial.C W.a₆ * MvPolynomial.X 1 ^ 3
      - MvPolynomial.C W.a₃ * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2
      - MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 with hb0
  rw [← (MulEquiv.prime_iff (MvPolynomial.finSuccEquiv K 2)),
    finSuccEquiv_projective_polynomial_aux W b0 b1 b2 hb0 hb1 hb2]
  exact (monic_weierstrass_cubic_prime_aux W b0 b1 b2 hb0 hb1 hb2).neg

end WeierstrassCurve

/-- The projective coordinate ring of a Weierstrass curve over a field is an integral domain. -/
instance ModularCurves.instIsDomainProjCoordRing {K : Type*} [Field K] (W : WeierstrassCurve K) :
    IsDomain (ModularCurves.projCoordRing W) := by
  have hp : Prime W.toProjective.polynomial := WeierstrassCurve.projective_polynomial_prime W
  rw [Ideal.Quotient.isDomain_iff_prime, ModularCurves.projIdeal_toIdeal]
  exact (Ideal.span_singleton_prime hp.ne_zero).mpr hp

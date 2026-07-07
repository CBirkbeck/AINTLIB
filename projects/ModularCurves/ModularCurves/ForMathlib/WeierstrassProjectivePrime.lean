/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.EllipticCurve.WeierstrassModel
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# The projective Weierstrass cubic is prime

For a Weierstrass curve `W` over a field `K`, the homogeneous Weierstrass polynomial
`W(X, Y, Z) = Y²Z + a₁XYZ + a₃YZ² − (X³ + a₂X²Z + a₄XZ² + a₆Z³)` is a prime element of
`MvPolynomial (Fin 3) K`. Consequently the projective coordinate ring
`ModularCurves.projCoordRing W = K[X,Y,Z] / (W)` is an integral domain.

## Main results

* `WeierstrassCurve.projective_polynomial_prime`: `W.toProjective.polynomial` is prime.
* the `IsDomain (ModularCurves.projCoordRing W)` instance.

## Strategy

Extract the variable `X = X 0` via `MvPolynomial.finSuccEquiv K 2`, viewing the cubic as a
polynomial in `X` over `S := MvPolynomial (Fin 2) K` (whose generators `X 0, X 1` play the
roles of `Y` and `Z`). Up to sign this image is the **monic** cubic

  `Gm = X³ + C(a₂·Z)·X² + C(a₄·Z² − a₁·Y·Z)·X + C(a₆·Z³ − a₃·Y·Z² − Y²·Z)`,

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

/-- **The projective Weierstrass cubic is prime.** For any Weierstrass curve `W` over a
field `K`, the homogeneous Weierstrass polynomial `W.toProjective.polynomial` is a prime
element of `MvPolynomial (Fin 3) K`. No ellipticity or discriminant hypothesis is needed. -/
theorem projective_polynomial_prime {K : Type*} [Field K] (W : WeierstrassCurve K) :
    Prime W.toProjective.polynomial := by
  -- The lower coefficients of the monic cubic `Gm`, as elements of `S = MvPolynomial (Fin 2) K`.
  set b2 : MvPolynomial (Fin 2) K := MvPolynomial.C W.a₂ * MvPolynomial.X 1 with hb2
  set b1 : MvPolynomial (Fin 2) K := MvPolynomial.C W.a₄ * MvPolynomial.X 1 ^ 2
      - MvPolynomial.C W.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1 with hb1
  set b0 : MvPolynomial (Fin 2) K := MvPolynomial.C W.a₆ * MvPolynomial.X 1 ^ 3
      - MvPolynomial.C W.a₃ * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2
      - MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 with hb0
  -- The monic cubic obtained by extracting `X 0` (up to sign).
  set Gm : (MvPolynomial (Fin 2) K)[X] :=
    Polynomial.X ^ 3 + Polynomial.C b2 * Polynomial.X ^ 2
      + Polynomial.C b1 * Polynomial.X + Polynomial.C b0 with hGm
  -- Action of `finSuccEquiv K 2` on the generators and on constants.
  have hX0 : MvPolynomial.finSuccEquiv K 2 (MvPolynomial.X 0) = Polynomial.X :=
    MvPolynomial.finSuccEquiv_X_zero
  have hX1 : MvPolynomial.finSuccEquiv K 2 (MvPolynomial.X 1)
      = Polynomial.C (MvPolynomial.X 0) := by
    have h : (1 : Fin 3) = (0 : Fin 2).succ := by decide
    rw [h]; exact MvPolynomial.finSuccEquiv_X_succ
  have hX2 : MvPolynomial.finSuccEquiv K 2 (MvPolynomial.X 2)
      = Polynomial.C (MvPolynomial.X 1) := by
    have h : (2 : Fin 3) = (1 : Fin 2).succ := by decide
    rw [h]; exact MvPolynomial.finSuccEquiv_X_succ
  have hC : ∀ a : K, MvPolynomial.finSuccEquiv K 2 (MvPolynomial.C a)
      = Polynomial.C (MvPolynomial.C a) := by
    intro a
    rw [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]; rfl
  -- Extracting `X 0` sends the Weierstrass cubic to `-Gm`.
  have hmap : MvPolynomial.finSuccEquiv K 2 W.toProjective.polynomial = -Gm := by
    simp only [hGm, hb0, hb1, hb2, WeierstrassCurve.Projective.polynomial,
      map_add, map_sub, map_mul, map_pow, hX0, hX1, hX2, hC]
    ring
  -- `Gm` is monic of degree three with the advertised lower coefficients.
  have hmonic : Gm.Monic := by rw [hGm]; monicity!
  have hdeg : Gm.natDegree = 3 := by rw [hGm]; compute_degree!
  have hc0 : Gm.coeff 0 = b0 := by rw [hGm]; simp
  have hc1 : Gm.coeff 1 = b1 := by rw [hGm]; simp
  have hc2 : Gm.coeff 2 = b2 := by rw [hGm]; simp
  -- `Z = X 1` is a nonzero prime of `S`, so `span {Z}` is a prime ideal.
  have hXne : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ≠ 0 := MvPolynomial.X_ne_zero 1
  have hXprime : Prime (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) :=
    MvPolynomial.X_prime
  have hPprime : (Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}).IsPrime :=
    (Ideal.span_singleton_prime hXne).mpr hXprime
  -- `Gm` is Eisenstein at `span {Z}`.
  have hEis : Gm.IsEisensteinAt (Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 2) K)}) := by
    refine ⟨?_, ?_, ?_⟩
    · -- the leading coefficient `1` is not in the (proper) prime ideal
      rw [show Gm.leadingCoeff = 1 from hmonic]
      exact (Ideal.ne_top_iff_one _).mp hPprime.ne_top
    · -- every lower coefficient is divisible by `Z`
      intro n hn
      rw [hdeg] at hn
      interval_cases n
      · rw [hc0]
        exact Ideal.mem_span_singleton.mpr ⟨MvPolynomial.C W.a₆ * MvPolynomial.X 1 ^ 2
          - MvPolynomial.C W.a₃ * MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.X 0 ^ 2,
          by rw [hb0]; ring⟩
      · rw [hc1]
        exact Ideal.mem_span_singleton.mpr ⟨MvPolynomial.C W.a₄ * MvPolynomial.X 1
          - MvPolynomial.C W.a₁ * MvPolynomial.X 0, by rw [hb1]; ring⟩
      · rw [hc2]
        exact Ideal.mem_span_singleton.mpr ⟨MvPolynomial.C W.a₂, by rw [hb2]; ring⟩
    · -- the constant coefficient is not divisible by `Z²`, because `Z ∤ Y²`
      rw [hc0, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      intro hdvd
      have key : (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^ 2 * MvPolynomial.X 1 =
          MvPolynomial.X 1 ^ 2 * (MvPolynomial.C W.a₆ * MvPolynomial.X 1
            - MvPolynomial.C W.a₃ * MvPolynomial.X 0) - b0 := by rw [hb0]; ring
      have hdvd2 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^ 2 ∣
          MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 := by
        rw [key]; exact dvd_sub (dvd_mul_right _ _) hdvd
      rw [show (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^ 2 * MvPolynomial.X 1
          = MvPolynomial.X 1 * MvPolynomial.X 0 ^ 2 from by ring,
        pow_two (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K),
        mul_dvd_mul_iff_left hXne] at hdvd2
      have hcontra : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ∣ MvPolynomial.X 0 :=
        hXprime.dvd_of_dvd_pow hdvd2
      rw [MvPolynomial.X_dvd_X] at hcontra
      exact absurd hcontra (by decide)
  -- Eisenstein ⇒ irreducible ⇒ prime, then transport back through `finSuccEquiv`.
  have hGm_irred : Irreducible Gm :=
    hEis.irreducible hPprime hmonic.isPrimitive (by rw [hdeg]; norm_num)
  have hGm_prime : Prime Gm := UniqueFactorizationMonoid.irreducible_iff_prime.mp hGm_irred
  have hassoc : Associated (-Gm) Gm := ⟨-1, by rw [Units.val_neg, Units.val_one]; ring⟩
  have hnegGm_prime : Prime (-Gm) := hassoc.prime_iff.mpr hGm_prime
  rw [← hmap] at hnegGm_prime
  exact (MulEquiv.prime_iff (MvPolynomial.finSuccEquiv K 2)).mp hnegGm_prime

end WeierstrassCurve

/-- The projective coordinate ring `K[X,Y,Z] / (W)` of a Weierstrass curve over a field is an
integral domain, since the Weierstrass cubic is prime
(`WeierstrassCurve.projective_polynomial_prime`). -/
instance ModularCurves.instIsDomainProjCoordRing {K : Type*} [Field K] (W : WeierstrassCurve K) :
    IsDomain (ModularCurves.projCoordRing W) := by
  have hp : Prime W.toProjective.polynomial := WeierstrassCurve.projective_polynomial_prime W
  have hI : (ModularCurves.projIdeal W).toIdeal.IsPrime := by
    rw [ModularCurves.projIdeal_toIdeal]
    exact (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  exact (Ideal.Quotient.isDomain_iff_prime _).mpr hI

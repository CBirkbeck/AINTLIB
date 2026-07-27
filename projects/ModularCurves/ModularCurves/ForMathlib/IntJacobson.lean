/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# `ℤ` is a Jacobson ring

`Int.instIsJacobsonRing` : the ring of integers is a Jacobson ring. Mathlib provides Jacobson-ness
for algebras of finite type over a Jacobson base (`isJacobsonRing_MvPolynomial_fin`,
`isJacobsonRing_localization`, `Polynomial.isJacobsonRing`) but does **not** provide the base case
`IsJacobsonRing ℤ` (even `import Mathlib` + `exact?` fails). This is the missing base instance: it
makes `MvPolynomial (Fin n) ℤ` and its localizations — e.g. the universal Weierstrass atlas ring
`WeierstrassAtlasRing = Localization.Away (universalWeierstrass.Δ)` — Jacobson automatically, which
is what the Bosma–Lenstra group-law base-change transport needs.

`ℤ` is Jacobson because it is a PID (so every non-zero prime is maximal, hence equals its own
Jacobson radical) whose nilradical/`⊥` has Jacobson radical `⊥`: an integer lying in every maximal
ideal `(p)` — equivalently `x·y + 1` a unit for all `y` — must be `0` (take `y = 1, 2`).
-/

open Ideal

/-- **`ℤ` is a Jacobson ring.** The base instance mathlib is missing. -/
instance Int.instIsJacobsonRing : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  rcases eq_or_ne P ⊥ with rfl | hne
  · -- `⊥.jacobson = ⊥`: an integer in every maximal ideal is `0`.
    rw [eq_bot_iff]
    intro x hx
    rw [Ideal.mem_jacobson_bot] at hx
    have h1 := hx 1
    have h2 := hx 2
    rw [Int.isUnit_iff] at h1 h2
    rw [Ideal.mem_bot]
    omega
  · -- a non-zero prime of a PID is maximal, hence its own Jacobson radical.
    haveI := hP
    exact jacobson_eq_self_of_isMaximal (H := _root_.IsPrime.to_maximal_ideal hne)

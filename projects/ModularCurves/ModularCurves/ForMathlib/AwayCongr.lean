/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Transport of homogeneous localizations along element equalities

`HomogeneousLocalization.Away 𝒜 s` depends on the element `s`; propositional
equalities `s = t` therefore change the type. This file provides the transport
ring isomorphism together with a `subst`-derived API on `Away.mk` normal forms and
naturality against `Away.map`, so that downstream proofs never juggle `eqToHom`s.

AINTLIB ModularCurves (T-A5a-iso); upstream candidate.
-/

namespace ModularCurves

open HomogeneousLocalization

variable {ι R A : Type*} [AddCommMonoid ι] [DecidableEq ι]
  [CommRing R] [CommRing A] [Algebra R A]
  {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]

/-- Transport an `Away` ring along an equality of localization elements. -/
noncomputable def awayCongr {s t : A} (h : s = t) : Away 𝒜 s ≃+* Away 𝒜 t := by
  subst h
  exact RingEquiv.refl _

@[simp]
lemma awayCongr_rfl {s : A} :
    (awayCongr (rfl : s = s) : Away 𝒜 s ≃+* Away 𝒜 s) = RingEquiv.refl _ :=
  rfl

lemma awayCongr_mk {s t : A} (h : s = t) {i : ι} (hs : s ∈ 𝒜 i) (n : ℕ) (a : A)
    (ha : a ∈ 𝒜 (n • i)) :
    awayCongr (𝒜 := 𝒜) h (HomogeneousLocalization.Away.mk 𝒜 hs n a ha) =
      HomogeneousLocalization.Away.mk 𝒜 (h ▸ hs) n a ha := by
  subst h
  rfl

variable {σ B S : Type*} [CommRing S] [CommRing B] [Algebra S B]
  {ℬ : ι → Submodule S B} [GradedAlgebra ℬ]

/-- `awayCongr` is natural against the graded `Away.map`. -/
lemma awayCongr_map {s t : A} (h : s = t) (g : GradedRingHom 𝒜 ℬ) (x : Away 𝒜 s) :
    HomogeneousLocalization.Away.map g t (awayCongr (𝒜 := 𝒜) h x) =
      awayCongr (𝒜 := ℬ) (congrArg g h)
        (HomogeneousLocalization.Away.map g s x) := by
  subst h
  rfl

end ModularCurves

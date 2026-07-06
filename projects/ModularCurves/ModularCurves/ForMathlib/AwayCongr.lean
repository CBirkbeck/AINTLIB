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

lemma awayCongr_trans {s t u : A} (h₁ : s = t) (h₂ : t = u) (x : Away 𝒜 s) :
    awayCongr (𝒜 := 𝒜) h₂ (awayCongr (𝒜 := 𝒜) h₁ x) =
      awayCongr (𝒜 := 𝒜) (h₁.trans h₂) x := by
  subst h₁; subst h₂; rfl

lemma awayCongr_self {s : A} (h : s = s) (x : Away 𝒜 s) :
    awayCongr (𝒜 := 𝒜) h x = x := by
  rw [Subsingleton.elim h rfl]
  rfl

/-- `Away.map` only depends on the graded hom up to propositional equality, through
the transport. -/
lemma awayMap_congr {g₁ g₂ : GradedRingHom 𝒜 ℬ} (h : g₁ = g₂) (s : A) (x : Away 𝒜 s) :
    HomogeneousLocalization.Away.map g₂ s x =
      awayCongr (𝒜 := ℬ) (congrArg (fun g : GradedRingHom 𝒜 ℬ => g s) h)
        (HomogeneousLocalization.Away.map g₁ s x) := by
  subst h
  exact (awayCongr_self _ _).symm

variable {τ C T : Type*} [CommRing T] [CommRing C] [Algebra T C]
  {𝒞 : ι → Submodule T C} [GradedAlgebra 𝒞]

/-- Applied form of `Away.map_comp`. -/
lemma awayMap_map (f : GradedRingHom 𝒜 ℬ) (g : GradedRingHom ℬ 𝒞) (s : A)
    (x : Away 𝒜 s) :
    HomogeneousLocalization.Away.map g (f s)
        (HomogeneousLocalization.Away.map f s x) =
      HomogeneousLocalization.Away.map (g.comp f) s x :=
  (DFunLike.congr_fun (HomogeneousLocalization.Away.map_comp f g s) x).symm

variable {S' B' : Type*} [CommRing S'] [CommRing B'] [Algebra S' B']
  {ℬ' : ι → Submodule S' B'} [GradedAlgebra ℬ']

/-- Comparing the two ways around a commuting square of graded homs, with
transports along any equalities of the localization elements. -/
lemma awayMap_square {f₁ : GradedRingHom 𝒜 ℬ} {g₁ : GradedRingHom ℬ 𝒞}
    {f₂ : GradedRingHom 𝒜 ℬ'} {g₂ : GradedRingHom ℬ' 𝒞}
    (hsq : g₁.comp f₁ = g₂.comp f₂) (s : A) (x : Away 𝒜 s)
    {t : C} (h₁ : g₁ (f₁ s) = t) (h₂ : g₂ (f₂ s) = t) :
    awayCongr (𝒜 := 𝒞) h₁
        (HomogeneousLocalization.Away.map g₁ (f₁ s)
          (HomogeneousLocalization.Away.map f₁ s x)) =
      awayCongr (𝒜 := 𝒞) h₂
        (HomogeneousLocalization.Away.map g₂ (f₂ s)
          (HomogeneousLocalization.Away.map f₂ s x)) := by
  rw [awayMap_map, awayMap_map, awayMap_congr hsq s x]
  refine Eq.trans ?_ (awayCongr_trans (𝒜 := 𝒞)
    (congrArg (fun g : GradedRingHom 𝒜 𝒞 => g s) hsq) h₂
    ((HomogeneousLocalization.Away.map (g₁.comp f₁) s) x)).symm
  exact congrArg (fun hh => awayCongr (𝒜 := 𝒞) hh
    ((HomogeneousLocalization.Away.map (g₁.comp f₁) s) x)) (Subsingleton.elim _ _)

end ModularCurves

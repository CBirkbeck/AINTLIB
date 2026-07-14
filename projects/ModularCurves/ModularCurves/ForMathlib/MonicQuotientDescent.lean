/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Monic descent for `AdjoinRoot`, and domains of homogeneous localizations (ForMathlib)

Two reusable facts extracted while closing `T-W7.0c-c5β`:

* `AdjoinRoot.mapRingHom_injective` — for a **monic** `f` over `A` and an injective coefficient
  map `φ : A →+* B` into a domain, the induced `AdjoinRoot f →+* AdjoinRoot (f.map φ)` is
  injective. Consequently `IsDomain (AdjoinRoot (f.map φ))` descends to `IsDomain (AdjoinRoot f)`
  (`AdjoinRoot.isDomain_of_monic_of_map`). This is the abstract form of the trick mathlib uses
  by hand for `WeierstrassCurve.Affine.CoordinateRing`.
* `HomogeneousLocalization.isDomain_away` — the degree-zero part of a graded domain localized at
  a nonzero element is a domain (the `IsDomain` sibling of `AlgebraicGeometry.Proj.isReduced_away`).

Both are stated for arbitrary commutative rings and are upstream candidates.
-/

open Polynomial

namespace AdjoinRoot

variable {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (f : A[X])

/-- A monic polynomial divides `p` as soon as it does so after an injective coefficient map into
a domain: reduce `p` mod `f` and compare degrees. -/
theorem _root_.Polynomial.dvd_of_monic_of_map_dvd_map [Nontrivial A] [IsDomain B]
    {φ : A →+* B} (hφ : Function.Injective φ) {f p : A[X]} (hf : f.Monic)
    (h : f.map φ ∣ p.map φ) : f ∣ p := by
  have hsplit : p %ₘ f + f * (p /ₘ f) = p := modByMonic_add_div p f
  have hr : (p %ₘ f).map φ = p.map φ - (f.map φ) * ((p /ₘ f).map φ) := by
    rw [← Polynomial.map_mul, ← Polynomial.map_sub]
    congr 1
    linear_combination hsplit
  have hdvd : f.map φ ∣ (p %ₘ f).map φ := by
    rw [hr]
    exact dvd_sub h (Dvd.intro _ rfl)
  have hlt : ((p %ₘ f).map φ).degree < (f.map φ).degree := by
    refine lt_of_le_of_lt (degree_map_le) ?_
    rw [hf.degree_map]
    exact degree_modByMonic_lt p hf
  have hzero : (p %ₘ f).map φ = 0 := by
    by_contra h0
    exact absurd (degree_le_of_dvd hdvd h0) (not_le.mpr hlt)
  have hr0 : p %ₘ f = 0 :=
    Polynomial.map_injective φ hφ (by rw [hzero, Polynomial.map_zero])
  rw [← hsplit, hr0, zero_add]
  exact Dvd.intro _ rfl

/-- The coefficient map induced on `AdjoinRoot`s. -/
noncomputable def mapRingHom : AdjoinRoot f →+* AdjoinRoot (f.map φ) :=
  AdjoinRoot.lift ((AdjoinRoot.of (f.map φ)).comp φ) (AdjoinRoot.root (f.map φ)) <| by
    rw [← Polynomial.eval₂_map]
    exact AdjoinRoot.eval₂_root _

@[simp]
lemma mapRingHom_mk (p : A[X]) :
    mapRingHom φ f (AdjoinRoot.mk f p) = AdjoinRoot.mk (f.map φ) (p.map φ) := by
  rw [mapRingHom, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map]
  exact AdjoinRoot.aeval_eq _

/-- **Monic descent.** For monic `f` and injective `φ` into a domain, the induced map of
`AdjoinRoot`s is injective. -/
theorem mapRingHom_injective [Nontrivial A] [IsDomain B] (hf : f.Monic)
    (hφ : Function.Injective φ) : Function.Injective (mapRingHom φ f) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [mapRingHom_mk, AdjoinRoot.mk_eq_zero] at hx
  rw [AdjoinRoot.mk_eq_zero]
  exact Polynomial.dvd_of_monic_of_map_dvd_map hφ hf hx

/-- **Monic descent of `IsDomain`.** If `f` is monic and its image under an injective coefficient
map is such that `AdjoinRoot (f.map φ)` is a domain, then `AdjoinRoot f` is a domain. This is the
abstract form of mathlib's `WeierstrassCurve.Affine.CoordinateRing` domain argument. -/
theorem isDomain_of_monic_of_map [Nontrivial A] [IsDomain B] (hf : f.Monic)
    (hφ : Function.Injective φ) [IsDomain (AdjoinRoot (f.map φ))] : IsDomain (AdjoinRoot f) :=
  Function.Injective.isDomain (mapRingHom φ f) (mapRingHom_injective φ f hf hφ)

end AdjoinRoot

namespace HomogeneousLocalization

variable {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The degree-zero part of a graded domain localized at a nonzero element is a domain: it embeds
into the (domain) localization via `val`. The `IsDomain` sibling of
`AlgebraicGeometry.Proj.isReduced_away`. -/
theorem isDomain_away [IsDomain A] {f : A} (hf : f ≠ 0) : IsDomain (Away 𝒜 f) := by
  haveI : IsDomain (Localization (Submonoid.powers f)) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  exact Function.Injective.isDomain
    (algebraMap (Away 𝒜 f) (Localization (Submonoid.powers f)))
    (HomogeneousLocalization.val_injective _)

end HomogeneousLocalization

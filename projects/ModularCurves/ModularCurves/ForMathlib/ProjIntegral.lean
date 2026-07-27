/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# `Proj` of a graded domain is an integral scheme

If a graded ring `A` (graded by `𝒜 : ℕ → σ`) is an integral domain and has a nonzero
homogeneous element of positive degree, then `Proj 𝒜` is an integral scheme.

## Main results

* `AlgebraicGeometry.Proj.isReduced_away`: each homogeneous localization `Away 𝒜 f` of a
  domain is reduced (it embeds into the localization `Localization (Submonoid.powers f)`, which
  is reduced).
* `AlgebraicGeometry.Proj.isIntegral_of_isDomain`: `Proj 𝒜` is integral.

## Strategy

`IsIntegral X ↔ IrreducibleSpace X ∧ IsReduced X`
(`AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced`).

* **Reduced.** `Proj 𝒜` is covered by the affine opens `Spec (Away 𝒜 f)`
  (`AlgebraicGeometry.Proj.affineOpenCover`). Each ring `Away 𝒜 f = HomogeneousLocalization 𝒜
  (Submonoid.powers f)` injects (via `HomogeneousLocalization.val`) into the localization
  `Localization (Submonoid.powers f)` of the domain `A`, which is reduced; hence `Away 𝒜 f` is
  reduced, so each `Spec (Away 𝒜 f)` is reduced, and `IsReduced.of_openCover` finishes.
* **Irreducible.** For a domain `A`, the zero ideal is a homogeneous prime, and it is relevant
  exactly because there is a nonzero positive-degree element. Thus it is a point whose closure is
  the whole space (`zeroLocus` of `⊥` is everything), i.e. a generic point, so the space is
  irreducible.

The positivity hypothesis is `∃ i, 0 < i ∧ ∃ x ∈ 𝒜 i, x ≠ 0` ("nonzero positive-degree part"),
which is exactly what makes the zero ideal *relevant* (not containing the irrelevant ideal).
-/

open AlgebraicGeometry HomogeneousLocalization ProjectiveSpectrum TopologicalSpace

namespace AlgebraicGeometry.Proj

variable {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Each homogeneous localization `Away 𝒜 f` of an integral domain is reduced: it embeds into the
localization `Localization (Submonoid.powers f)` (which is reduced), via the injective ring map
`HomogeneousLocalization.val`. -/
instance isReduced_away [IsDomain A] (f : A) : _root_.IsReduced (Away 𝒜 f) :=
  isReduced_of_injective
    (algebraMap (Away 𝒜 f) (Localization (Submonoid.powers f)))
    (HomogeneousLocalization.val_injective _)

/-- **`Proj` of a graded domain is integral.** If the graded ring `A` is an integral domain with a
nonzero homogeneous element of positive degree, then `Proj 𝒜` is an integral scheme. -/
theorem isIntegral_of_isDomain [IsDomain A] (h : ∃ i, 0 < i ∧ ∃ x ∈ 𝒜 i, x ≠ 0) :
    IsIntegral (Proj 𝒜) := by
  -- The zero ideal is relevant: it does not contain the irrelevant ideal.
  have hrel : ¬ HomogeneousIdeal.irrelevant 𝒜 ≤ (⊥ : HomogeneousIdeal 𝒜) := by
    obtain ⟨i, hi, x, hx, hx0⟩ := h
    rw [SetLike.not_le_iff_exists]
    exact ⟨x, HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hi hx, fun hc => hx0 (Ideal.mem_bot.mp hc)⟩
  -- The zero ideal as a point of the projective spectrum (the generic point).
  let p : ProjectiveSpectrum 𝒜 := ⟨⊥, Ideal.isPrime_bot, hrel⟩
  -- Reduced: cover by `Spec (Away 𝒜 f)`, each reduced.
  haveI hred : IsReduced (Proj 𝒜) := by
    haveI : ∀ i, IsReduced ((Proj.affineOpenCover 𝒜).openCover.X i) := by
      intro i
      show IsReduced (Spec ((Proj.affineOpenCover 𝒜).X i))
      haveI : _root_.IsReduced (↥((Proj.affineOpenCover 𝒜).X i)) := isReduced_away 𝒜 _
      infer_instance
    exact IsReduced.of_openCover _ (Proj.affineOpenCover 𝒜).openCover
  -- Irreducible: the generic point `p` is dense.
  have hclosure : closure ({p} : Set (ProjectiveSpectrum 𝒜)) = Set.univ := by
    rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      ProjectiveSpectrum.vanishingIdeal_singleton]
    exact ProjectiveSpectrum.zeroLocus_bot 𝒜
  haveI hirr : IrreducibleSpace (ProjectiveSpectrum 𝒜) := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← hclosure]
    exact isIrreducible_singleton.closure
  haveI : IrreducibleSpace (Proj 𝒜) := hirr
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end AlgebraicGeometry.Proj

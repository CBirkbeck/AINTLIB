/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import ModularCurves.ForMathlib.IdealSheafComaximal

/-!
# Pointwise-distinct sections of a separated morphism have comaximal kernels

If `σ₁, σ₂ : U ⟶ X` are two sections of a separated morphism `ρ : X ⟶ U`
(`σᵢ ≫ ρ = 𝟙 U`) whose base maps never agree (`∀ u, σ₁ u ≠ σ₂ u`), then their kernel
ideal sheaves are comaximal: `σ₁.ker ⊔ σ₂.ker = ⊤`.

Each section is a closed immersion (`IsClosedImmersion.of_comp`, as `σᵢ ≫ ρ = 𝟙` is one and
`ρ` is separated), so `σᵢ.ker.support = range σᵢ` (`Scheme.Hom.support_ker`, closed range).
The retraction `ρ` forces two agreeing image points to share the same `U`-fibre, so
pointwise-distinctness makes the images — hence the supports — disjoint, and disjoint
supports are comaximal (`sup_eq_top_of_disjoint_support`).

This is the pairwise-disjointness engine for the `Y(N)` full-level `⊇` argument (route γ):
over the locus where every nonzero combination `[c]P + [d]Q` is nowhere-vanishing, the `N²`
section combinations `[a]P + [b]Q` are pairwise pointwise-distinct, hence their kernels are
comaximal, so `∏ ker = ⋂ ker`.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X U : Scheme.{u}}

/-- Two sections of a separated morphism whose base maps never coincide have comaximal
kernel ideal sheaves. -/
theorem sup_ker_eq_top_of_sections_pointwise_ne (ρ : X ⟶ U) [IsSeparated ρ]
    (σ₁ σ₂ : U ⟶ X) (hσ₁ : σ₁ ≫ ρ = 𝟙 U) (hσ₂ : σ₂ ≫ ρ = 𝟙 U)
    (h : ∀ u : U, σ₁.base u ≠ σ₂.base u) :
    σ₁.ker ⊔ σ₂.ker = ⊤ := by
  haveI : IsClosedImmersion σ₁ := by
    haveI : IsClosedImmersion (σ₁ ≫ ρ) := by rw [hσ₁]; infer_instance
    exact IsClosedImmersion.of_comp σ₁ ρ
  haveI : IsClosedImmersion σ₂ := by
    haveI : IsClosedImmersion (σ₂ ≫ ρ) := by rw [hσ₂]; infer_instance
    exact IsClosedImmersion.of_comp σ₂ ρ
  have hr : Disjoint (Set.range σ₁.base) (Set.range σ₂.base) := by
    rw [Set.disjoint_left]
    rintro p ⟨u₁, rfl⟩ ⟨u₂, hu₂⟩
    have e1 : ρ.base (σ₁.base u₁) = u₁ := by
      have := congrArg (fun m : U ⟶ U => m.base u₁) hσ₁; simpa using this
    have e2 : ρ.base (σ₂.base u₂) = u₂ := by
      have := congrArg (fun m : U ⟶ U => m.base u₂) hσ₂; simpa using this
    have hu : u₂ = u₁ := by
      have := congrArg ρ.base hu₂; rwa [e2, e1] at this
    exact h u₁ (by rw [← hu₂, hu])
  apply sup_eq_top_of_disjoint_support
  have hc1 : closure (Set.range σ₁.base) = Set.range σ₁.base :=
    σ₁.isClosedEmbedding.isClosed_range.closure_eq
  have hc2 : closure (Set.range σ₂.base) = Set.range σ₂.base :=
    σ₂.isClosedEmbedding.isClosed_range.closure_eq
  rw [disjoint_iff, ← SetLike.coe_set_eq, Closeds.coe_inf, Closeds.coe_bot,
    Scheme.Hom.support_ker, Scheme.Hom.support_ker, hc1, hc2]
  exact Set.disjoint_iff_inter_eq_empty.mp hr

end AlgebraicGeometry.Scheme.IdealSheafData

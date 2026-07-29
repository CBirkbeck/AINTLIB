/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.FiniteAffineOpenCover
import ModularCurves.ForMathlib.SchemeTheoreticImage

/-!
# Finite affine covers of scheme-theoretic images

This file replaces a scheme by the scheme-theoretic image of the common intersection of an
affine open cover. The pulled-back affine opens still cover the image, and the common open maps
scheme-theoretically dominantly into it.
-/

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.FiniteAffineImageCover

noncomputable section

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)

/-- The common intersection of a family of opens. -/
abbrev commonOpen : X.Opens := ⨅ i, U i

/-- The scheme-theoretic image of the common intersection in the original scheme. -/
abbrev obj : Scheme.{u} := (commonOpen U).ι.image

/-- The closed immersion of the scheme-theoretic image into the original scheme. -/
abbrev inclusion : obj U ⟶ X := (commonOpen U).ι.imageι

/-- The canonical map from the common intersection to its scheme-theoretic image. -/
abbrev toImage : (commonOpen U).toScheme ⟶ obj U :=
  (commonOpen U).ι.toImage

/-- The pullback of one member of the original cover to the scheme-theoretic image. -/
abbrev chart (i : ι) : (obj U).Opens := inclusion U ⁻¹ᵁ U i

/-- Pulling an affine chart back to the scheme-theoretic image preserves affineness. -/
lemma chart_isAffineOpen (hU : ∀ i, IsAffineOpen (U i)) (i : ι) :
    IsAffineOpen (chart U i) :=
  (hU i).preimage (inclusion U)

/-- The pulled-back charts cover the scheme-theoretic image. -/
lemma iSup_chart_eq_top (hU : ⨆ i, U i = ⊤) :
    ⨆ i, chart U i = ⊤ :=
  Scheme.Hom.iSup_preimage_eq_top (inclusion U) hU

/-- The common intersection lifted to one pulled-back chart. -/
def toChart (i : ι) : (commonOpen U).toScheme ⟶ (chart U i).toScheme :=
  IsOpenImmersion.lift (chart U i).ι (toImage U) (by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨toImage U x, ?_⟩, rfl⟩
    change ((toImage U ≫ inclusion U) x) ∈ U i
    rw [Scheme.Hom.toImage_imageι]
    change x.1 ∈ U i
    exact (show commonOpen U ≤ U i from iInf_le U i) x.2)

@[reassoc (attr := simp)]
lemma toChart_chartι (i : ι) :
    toChart U i ≫ (chart U i).ι = toImage U :=
  IsOpenImmersion.lift_fac _ _ _

/-- The common intersection is scheme-theoretically dense in its image. -/
lemma toImage_isSchemeTheoreticallyDominant [QuasiCompact (commonOpen U).ι] :
    IsSchemeTheoreticallyDominant (toImage U) :=
  Scheme.Hom.toImage_isSchemeTheoreticallyDominant _

/-- If the common intersection is topologically dense, its image inclusion is surjective. -/
lemma inclusion_surjective [QuasiCompact (commonOpen U).ι]
    (hU : Dense ((commonOpen U : X.Opens) : Set X)) :
    Surjective (inclusion U) := by
  haveI : IsDominant (commonOpen U).ι := by
    rw [isDominant_iff, DenseRange, Scheme.Opens.range_ι]
    exact hU
  exact Scheme.Hom.imageι_surjective_of_isDominant (commonOpen U).ι

/-- The scheme-theoretic image remains Noetherian when the original scheme is Noetherian. -/
lemma obj_isNoetherian [IsNoetherian X] : IsNoetherian (obj U) :=
  Scheme.Hom.image_isNoetherian (commonOpen U).ι

end

end AlgebraicGeometry.Scheme.FiniteAffineImageCover

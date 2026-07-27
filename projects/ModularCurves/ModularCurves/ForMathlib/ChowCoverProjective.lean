/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.ChowAmbientProjective
import ModularCurves.ForMathlib.ProperAffineIntersectionModel
import ModularCurves.ForMathlib.RelativeProjectiveFactorization

/-!
# Projectivity of the Chow cover

For a proper family, the open Chow source is also closed in its projective ambient scheme.
Consequently the Chow source is projective over the affine base and relative projective over
the original family.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FiniteAffineImageCover

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (xπ : X ⟶ Spec (.of R)) {ι : Type u} [Finite ι]
variable (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
variable [IsNoetherian X] [LocallyOfFinitePresentation xπ] [IsProper xπ]

/-- For a proper family, the open Chow source is also closed in its projective ambient. -/
lemma chowImmersion_isClosedImmersion_of_isProper
    (hcover : ⨆ i, U i = ⊤) :
    IsClosedImmersion (chowImmersion xπ U hU) := by
  letI : IsOpenImmersion (chowImmersion xπ U hU) :=
    chowImmersion_isOpenImmersion xπ U hU
  letI : IsProper (chowToTarget xπ U hU) :=
    chowToTarget_isProper xπ U hU hcover
  letI : IsProper (chowToTarget xπ U hU ≫ xπ) := by
    infer_instance
  letI : IsProper (chowAmbientπ xπ U hU) :=
    chowAmbientπ_isProper xπ U hU
  have hcomp :
      IsProper (chowImmersion xπ U hU ≫ chowAmbientπ xπ U hU) := by
    rw [← chowToTarget_comp_xπ xπ U hU]
    infer_instance
  letI : IsProper
      (chowImmersion xπ U hU ≫ chowAmbientπ xπ U hU) := hcomp
  exact IsClosedImmersion.of_isOpenImmersion_comp_isProper
    (chowImmersion xπ U hU) (chowAmbientπ xπ U hU)

/-- The Chow source of a proper family is projective over the affine base. -/
lemma chowSourceπ_isProjectiveFactorization [Nonempty ι]
    (hcover : ⨆ i, U i = ⊤) :
    AlgebraicGeometry.IsProjectiveFactorization
      (chowToTarget xπ U hU ≫ xπ) := by
  have hi : IsClosedImmersion (chowImmersion xπ U hU) :=
    chowImmersion_isClosedImmersion_of_isProper xπ U hU hcover
  rw [chowToTarget_comp_xπ xπ U hU]
  exact (chowAmbientπ_isProjectiveFactorization xπ U hU).comp_isClosedImmersion
    (chowImmersion xπ U hU) hi

/-- The Chow cover of a proper family is projective relative to the original family. -/
lemma chowToTarget_isRelativeProjectiveFactorization [Nonempty ι]
    (hcover : ⨆ i, U i = ⊤) :
    AlgebraicGeometry.IsRelativeProjectiveFactorization xπ
      (chowToTarget xπ U hU) :=
  (chowSourceπ_isProjectiveFactorization xπ U hU hcover).relative

end AlgebraicGeometry.Scheme.FiniteAffineImageCover

/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.AffineProjectiveClosure
import ModularCurves.ForMathlib.FiniteAffineImageCover

/-!
# Projective compactifications of finite affine image covers

Over a Noetherian affine base, each affine chart pulled back to the scheme-theoretic image has
a proper projective compactification. The standard open immersion commutes with the chart's
structure morphism.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.FiniteAffineImageCover

noncomputable section

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (xπ : X ⟶ Spec (.of R)) {ι : Type u} (U : ι → X.Opens)

/-- The scheme-theoretic image over the original affine base. -/
abbrev imageπ : obj U ⟶ Spec (.of R) := inclusion U ≫ xπ

/-- The structure morphism of one pulled-back affine chart. -/
abbrev chartπ (i : ι) : (chart U i).toScheme ⟶ Spec (.of R) :=
  (chart U i).ι ≫ imageπ xπ U

/-- The scheme-theoretic image remains locally of finite presentation over the affine base. -/
lemma imageπ_locallyOfFinitePresentation [IsNoetherian X]
    [LocallyOfFinitePresentation xπ] :
    LocallyOfFinitePresentation (imageπ xπ U) := by
  infer_instance

/-- Each pulled-back affine chart is locally of finite presentation over the affine base. -/
lemma chartπ_locallyOfFinitePresentation [IsNoetherian X]
    [LocallyOfFinitePresentation xπ] (i : ι) :
    LocallyOfFinitePresentation (chartπ xπ U i) := by
  infer_instance

/-- The projective compactification of one pulled-back affine chart. -/
noncomputable abbrev projectiveObj [IsNoetherian X]
    [LocallyOfFinitePresentation xπ] (hU : ∀ i, IsAffineOpen (U i)) (i : ι) :
    Scheme.{u} := by
  letI : IsAffine (chart U i).toScheme := chart_isAffineOpen U hU i
  letI : LocallyOfFinitePresentation (chartπ xπ U i) :=
    chartπ_locallyOfFinitePresentation xπ U i
  exact AffineProjectiveClosure.obj (chartπ xπ U i)

/-- The structure morphism of one chart's projective compactification. -/
noncomputable def projectiveπ [IsNoetherian X]
    [LocallyOfFinitePresentation xπ] (hU : ∀ i, IsAffineOpen (U i)) (i : ι) :
    projectiveObj xπ U hU i ⟶ Spec (.of R) := by
  letI : IsAffine (chart U i).toScheme := chart_isAffineOpen U hU i
  letI : LocallyOfFinitePresentation (chartπ xπ U i) :=
    chartπ_locallyOfFinitePresentation xπ U i
  exact AffineProjectiveClosure.π (chartπ xπ U i)

/-- The pulled-back affine chart as the standard open of its compactification. -/
noncomputable def projectiveOpen [IsNoetherian X]
    [LocallyOfFinitePresentation xπ] (hU : ∀ i, IsAffineOpen (U i)) (i : ι) :
    (chart U i).toScheme ⟶ projectiveObj xπ U hU i := by
  letI : IsAffine (chart U i).toScheme := chart_isAffineOpen U hU i
  letI : LocallyOfFinitePresentation (chartπ xπ U i) :=
    chartπ_locallyOfFinitePresentation xπ U i
  exact AffineProjectiveClosure.openImmersion (chartπ xπ U i)

/-- Every chart compactification is proper over the affine base. -/
lemma projectiveπ_isProper [IsNoetherian X]
    [LocallyOfFinitePresentation xπ] (hU : ∀ i, IsAffineOpen (U i)) (i : ι) :
    IsProper (projectiveπ xπ U hU i) := by
  letI : IsAffine (chart U i).toScheme := chart_isAffineOpen U hU i
  letI : LocallyOfFinitePresentation (chartπ xπ U i) :=
    chartπ_locallyOfFinitePresentation xπ U i
  exact AffineProjectiveClosure.π_isProper (chartπ xπ U i)

/-- Every standard chart map is an open immersion. -/
lemma projectiveOpen_isOpenImmersion [IsNoetherian X]
    [LocallyOfFinitePresentation xπ] (hU : ∀ i, IsAffineOpen (U i)) (i : ι) :
    IsOpenImmersion (projectiveOpen xπ U hU i) := by
  letI : IsAffine (chart U i).toScheme := chart_isAffineOpen U hU i
  letI : LocallyOfFinitePresentation (chartπ xπ U i) :=
    chartπ_locallyOfFinitePresentation xπ U i
  exact AffineProjectiveClosure.openImmersion_isOpenImmersion (chartπ xπ U i)

/-- The standard chart immersion commutes with the structure maps to the affine base. -/
@[reassoc (attr := simp)]
lemma projectiveOpen_comp_projectiveπ [IsNoetherian X]
    [LocallyOfFinitePresentation xπ] (hU : ∀ i, IsAffineOpen (U i)) (i : ι) :
    projectiveOpen xπ U hU i ≫ projectiveπ xπ U hU i = chartπ xπ U i := by
  letI : IsAffine (chart U i).toScheme := chart_isAffineOpen U hU i
  letI : LocallyOfFinitePresentation (chartπ xπ U i) :=
    chartπ_locallyOfFinitePresentation xπ U i
  exact AffineProjectiveClosure.openImmersion_comp_π (chartπ xπ U i)

end


end AlgebraicGeometry.Scheme.FiniteAffineImageCover

/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.PresentationProjectiveClosure
import ModularCurves.ForMathlib.SmoothSectionLift

/-!
# Projective closures of affine finitely presented morphisms

An affine scheme locally of finite presentation over `Spec R` has a finite presentation of its
coordinate algebra. Homogenizing that presentation embeds the scheme as an open subscheme of a
proper `R`-scheme.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.AffineProjectiveClosure

noncomputable section

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of R)) [IsAffine X] [LocallyOfFinitePresentation f]

/-- The `R`-algebra structure on the global sections induced by the structure morphism. -/
@[instance_reducible]
noncomputable def algebra : Algebra R Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom.toAlgebra

/-- The coordinate algebra of an affine locally finitely presented morphism is finitely
presented. -/
lemma finitePresentation :
    letI := algebra f
    Algebra.FinitePresentation R Γ(X, ⊤) := by
  letI := algebra f
  change RingHom.FinitePresentation
    (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
  rw [CommRingCat.hom_comp,
    RingHom.finitePresentation_respectsIso.cancel_left_isIso]
  exact Scheme.Hom.finitePresentation_appTop f

/-- A chosen finite presentation of the induced coordinate algebra. -/
noncomputable def presentation :
    letI := algebra f
    letI := finitePresentation f
    Algebra.Presentation R Γ(X, ⊤)
      (Fin (Algebra.Presentation.ofFinitePresentationVars R Γ(X, ⊤)))
      (Fin (Algebra.Presentation.ofFinitePresentationRels R Γ(X, ⊤))) := by
  letI := algebra f
  letI := finitePresentation f
  exact Algebra.Presentation.ofFinitePresentation R Γ(X, ⊤)

/-- The projective closure obtained by homogenizing the chosen finite presentation. -/
noncomputable abbrev obj : Scheme.{u} := by
  letI := algebra f
  letI := finitePresentation f
  exact Algebra.Presentation.projectiveClosure (presentation f)

/-- The structure morphism of the projective closure. -/
noncomputable def π : obj f ⟶ Spec (.of R) := by
  letI := algebra f
  letI := finitePresentation f
  exact Algebra.Presentation.projectiveClosureπ (presentation f)

/-- The original affine scheme as the standard open of its projective closure. -/
noncomputable def openImmersion : X ⟶ obj f := by
  letI := algebra f
  letI := finitePresentation f
  exact X.isoSpec.hom ≫ Algebra.Presentation.affineOpen (presentation f)

/-- The projective closure is proper over the affine base. -/
lemma π_isProper : IsProper (π f) := by
  letI := algebra f
  letI := finitePresentation f
  exact Algebra.Presentation.projectiveClosureπ_isProper (presentation f)

/-- The standard affine chart is an open immersion. -/
lemma openImmersion_isOpenImmersion : IsOpenImmersion (openImmersion f) := by
  letI := algebra f
  letI := finitePresentation f
  unfold openImmersion
  exact @IsOpenImmersion.comp _ _ _ _ _ (by infer_instance)
    (Algebra.Presentation.affineOpen_isOpenImmersion (presentation f))

/-- The projective structure morphism restricts to the original affine morphism. -/
@[reassoc (attr := simp)]
lemma openImmersion_comp_π : openImmersion f ≫ π f = f := by
  letI := algebra f
  letI := finitePresentation f
  unfold openImmersion π
  rw [Category.assoc,
    Algebra.Presentation.affineOpen_comp_projectiveClosureπ]
  exact (toSpecΓ_appTop_triangle f).symm

end


end AlgebraicGeometry.Scheme.AffineProjectiveClosure

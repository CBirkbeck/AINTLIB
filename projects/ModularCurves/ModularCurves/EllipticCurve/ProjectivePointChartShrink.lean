/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveCoordinatePullbackTwistMap
import ModularCurves.ForMathlib.SchemeIsomorphismOpenShrink

/-!
# Shrinking an isomorphism locus to a projective chart

Every point of polynomial projective space belongs to a standard
coordinate chart. Over an open where a morphism is an isomorphism, the
chart through the lifted point transports to a smaller target open.
-/

open CategoryTheory

noncomputable section

universe u

namespace MvPolynomial

open AlgebraicGeometry HomogeneousIdeal TopologicalSpace

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem exists_coordinateOpenIndexAt
    (x : Proj (homogeneousSubmodule σ R)) :
    ∃ j : σ, x ∈ coordinateOpen (R := R) j := by
  have hx : x ∈ (⊤ :
      (Proj (homogeneousSubmodule σ R)).Opens) :=
    trivial
  rw [← iSup_coordinateOpen_eq_top (R := R)] at hx
  exact Opens.mem_iSup.mp hx

/-- A chosen standard coordinate chart containing a projective point. -/
noncomputable def coordinateOpenIndexAt
    (x : Proj (homogeneousSubmodule σ R)) : σ :=
  Classical.choose (exists_coordinateOpenIndexAt x)

/-- A projective point belongs to its chosen coordinate chart. -/
theorem mem_coordinateOpenIndexAt
    (x : Proj (homogeneousSubmodule σ R)) :
    x ∈ coordinateOpen (R := R)
      (coordinateOpenIndexAt x) :=
  Classical.choose_spec (exists_coordinateOpenIndexAt x)

end MvPolynomial

namespace AlgebraicGeometry.Scheme.Hom

open MvPolynomial HomogeneousIdeal

variable {R : Type u} {σ : Type} [CommRing R]
variable {X Y : Scheme.{u}}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The unique source point above a point of an isomorphism open. -/
noncomputable def projectiveChartSourcePoint
    (f : X ⟶ Y) (U : Y.Opens) [IsIso (f ∣_ U)]
    (x : U.toScheme) : X :=
  (f ⁻¹ᵁ U).ι ((inv (f ∣_ U)) x)

/-- The projective coordinate selected at the lifted source point. -/
noncomputable def projectiveChartCoordinateAt
    (f : X ⟶ Y)
    (g : X ⟶ Proj (homogeneousSubmodule σ R))
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (x : U.toScheme) : σ :=
  coordinateOpenIndexAt
    (g (f.projectiveChartSourcePoint U x))

/-- The inverse image of the selected projective coordinate chart. -/
noncomputable def projectiveChartOpenAt
    (f : X ⟶ Y)
    (g : X ⟶ Proj (homogeneousSubmodule σ R))
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (x : U.toScheme) : X.Opens :=
  g ⁻¹ᵁ coordinateOpen (R := R)
    (f.projectiveChartCoordinateAt g U x)

/-- The target shrink obtained by transporting the projective chart
through the inverse over the isomorphism open. -/
noncomputable def projectiveChartTargetShrinkAt
    (f : X ⟶ Y)
    (g : X ⟶ Proj (homogeneousSubmodule σ R))
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (x : U.toScheme) : Y.Opens :=
  f.isomorphismTargetShrink U
    (f.projectiveChartOpenAt g U x)

/-- The lifted source point belongs to the selected projective chart. -/
theorem projectiveChartSourcePoint_mem
    (f : X ⟶ Y)
    (g : X ⟶ Proj (homogeneousSubmodule σ R))
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (x : U.toScheme) :
    f.projectiveChartSourcePoint U x ∈
      f.projectiveChartOpenAt g U x :=
  mem_coordinateOpenIndexAt
    (g (f.projectiveChartSourcePoint U x))

/-- The original point lies in the transported target shrink. -/
theorem mem_projectiveChartTargetShrinkAt
    (f : X ⟶ Y)
    (g : X ⟶ Proj (homogeneousSubmodule σ R))
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (x : U.toScheme) :
    U.ι x ∈ f.projectiveChartTargetShrinkAt g U x :=
  f.mem_isomorphismTargetShrink U
    (f.projectiveChartOpenAt g U x) x
    (f.projectiveChartSourcePoint_mem g U x)

/-- The transported projective-chart open is contained in the original
isomorphism open. -/
theorem projectiveChartTargetShrinkAt_le
    (f : X ⟶ Y)
    (g : X ⟶ Proj (homogeneousSubmodule σ R))
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (x : U.toScheme) :
    f.projectiveChartTargetShrinkAt g U x ≤ U :=
  f.isomorphismTargetShrink_le U
    (f.projectiveChartOpenAt g U x)

/-- The morphism remains an isomorphism over the projective-chart
target shrink. -/
theorem isIso_projectiveChartTargetShrinkAt
    (f : X ⟶ Y)
    (g : X ⟶ Proj (homogeneousSubmodule σ R))
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (x : U.toScheme) :
    IsIso (f ∣_ f.projectiveChartTargetShrinkAt g U x) :=
  f.isIso_isomorphismTargetShrink U
    (f.projectiveChartOpenAt g U x)

/-- The inverse image of the target shrink is the part of the selected
projective chart over the original isomorphism open. -/
theorem preimage_projectiveChartTargetShrinkAt
    (f : X ⟶ Y)
    (g : X ⟶ Proj (homogeneousSubmodule σ R))
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (x : U.toScheme) :
    f ⁻¹ᵁ f.projectiveChartTargetShrinkAt g U x =
      (f ⁻¹ᵁ U) ⊓ f.projectiveChartOpenAt g U x :=
  f.preimage_isomorphismTargetShrink U
    (f.projectiveChartOpenAt g U x)

/-- Over the transported target open, the source lies in the selected
standard projective chart. -/
theorem preimage_projectiveChartTargetShrinkAt_le_chart
    (f : X ⟶ Y)
    (g : X ⟶ Proj (homogeneousSubmodule σ R))
    (U : Y.Opens) [IsIso (f ∣_ U)]
    (x : U.toScheme) :
    f ⁻¹ᵁ f.projectiveChartTargetShrinkAt g U x ≤
      g ⁻¹ᵁ coordinateOpen (R := R)
        (f.projectiveChartCoordinateAt g U x) := by
  change
    f ⁻¹ᵁ f.projectiveChartTargetShrinkAt g U x ≤
      f.projectiveChartOpenAt g U x
  rw [f.preimage_projectiveChartTargetShrinkAt g U x]
  exact inf_le_right

end AlgebraicGeometry.Scheme.Hom

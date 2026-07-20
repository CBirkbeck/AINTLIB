/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.ProjectiveSpaceHyperplane
import ModularCurves.EllipticCurve.PoleSheaf

/-!
# Twists on polynomial projective space

This file starts the concrete construction of projective-space twists by showing
that the ideal module of a coordinate hyperplane is invertible. It is the model
of `O(-1)` used in the standard-cover cohomology calculation.
-/

namespace MvPolynomial

open AlgebraicGeometry HomogeneousIdeal

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ideal module of a coordinate hyperplane is invertible. This is the
concrete model of `O(-1)` on polynomial projective space. -/
theorem coordinateHyperplaneIdealModule_isInvertible (j : σ) :
    Scheme.Modules.IsInvertible
      (ModularCurves.idealModule (coordinateHyperplaneι (R := R) j)) := by
  classical
  letI : IsClosedImmersion (coordinateHyperplaneι (R := R) j) :=
    coordinateHyperplaneι_isClosedImmersion j
  letI : QuasiCompact (coordinateHyperplaneι (R := R) j) := inferInstance
  apply ModularCurves.idealModule_isInvertible_of_locallyPrincipal
  intro y
  have hy : y ∈ ⨆ i : σ, coordinateOpen (R := R) i := by
    rw [iSup_coordinateOpen_eq_top]
    trivial
  obtain ⟨i, hyi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  let U : (Proj (homogeneousSubmodule σ R)).affineOpens :=
    ⟨coordinateOpen (R := R) i, coordinateOpen_isAffineOpen i⟩
  refine ⟨U, hyi, ?_⟩
  by_cases hji : j = i
  · subst i
    refine ⟨1, ?_, Submonoid.one_mem _⟩
    rw [coordinateHyperplaneι_ker_ideal_coordinateOpen_self,
      Ideal.span_singleton_one]
  · let r : Γ(Proj (homogeneousSubmodule σ R), coordinateOpen (R := R) i) :=
      (Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (X i)
        (X_mem_homogeneousSubmodule_one R i) one_pos).hom.hom
          (awayVar R i ⟨j, hji⟩)
    refine ⟨r, ?_, ?_⟩
    · exact coordinateHyperplaneι_ker_ideal_coordinateOpen_of_ne i j hji
    · let e := (Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (X i)
          (X_mem_homogeneousSubmodule_one R i) one_pos).commRingCatIsoToRingEquiv
      change e (awayVar R i ⟨j, hji⟩) ∈
        nonZeroDivisors Γ(Proj (homogeneousSubmodule σ R), coordinateOpen (R := R) i)
      rw [← MulEquivClass.map_nonZeroDivisors e]
      exact ⟨awayVar R i ⟨j, hji⟩, awayVar_mem_nonZeroDivisors R i ⟨j, hji⟩, rfl⟩

/-- The dual of the coordinate-hyperplane ideal module, giving the concrete
model of `O(1)` on polynomial projective space. -/
noncomputable def coordinateHyperplanePoleSheaf (j : σ) :
    (Proj (homogeneousSubmodule σ R)).Modules :=
  Scheme.Modules.dualObj
    (ModularCurves.idealModule (coordinateHyperplaneι (R := R) j))

/-- The concrete `O(1)` on polynomial projective space is invertible. -/
theorem coordinateHyperplanePoleSheaf_isInvertible (j : σ) :
    Scheme.Modules.IsInvertible (coordinateHyperplanePoleSheaf (R := R) j) :=
  (coordinateHyperplaneIdealModule_isInvertible (R := R) j).dual

end

end MvPolynomial

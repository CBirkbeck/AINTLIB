import ModularCurves.ForMathlib.GrassmannianChart
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The chart-overlap criterion for the Grassmannian ([NISOG-GRASS], [GR-E2])

For a chart member `N` at the coordinate tuple of `ι : Fin k ↪ Fin n`, membership in a
second chart `ι'` is a determinant condition: the **pointwise transition matrix** `T`
(column `i₂` = the ι-retraction values on the `ι' i₂`-th coordinate vector) satisfies

`IsChartAt (ι'-tuple) N ↔ IsUnit T.det`

— Stacks 089T step (4): the overlap is the basic open `D(det T)` of the ι-chart. The
generic-matrix-ring half of this statement lives in `GrassmannianTransition.lean`
([GR-E3]); the spec tying the two is the next increment.

Decomposition artifact: `.mathlib-quality/decomposition-nisog-grass.md` ([STREAM-FP],
fable-FP, [GR-E] design).
-/

universe u

namespace Module.Grassmannian

open Matrix

variable {A : Type u} [CommRing A] {k n : ℕ}

/-- The pointwise transition matrix of a chart member `N` at `ι`, toward a second chart
`ι'`: column `i₂` is the value of `N`'s ι-retraction on the `ι' i₂`-th coordinate
vector. Kronecker columns where `ι'` meets `range ι`, `chartMatrix`-columns elsewhere. -/
noncomputable def transitionMatrixAt (ι ι' : Fin k ↪ Fin n) (N : G(k, (Fin n → A); A))
    (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N) :
    Matrix (Fin k) (Fin k) A :=
  Matrix.of fun i₁ i₂ =>
    (LinearEquiv.ofBijective
        (N.toSubmodule.mkQ ∘ₗ coordMap (fun i => Pi.single (ι i) (1 : A))) h).symm
      (N.toSubmodule.mkQ (Pi.single (ι' i₂) 1)) i₁

/-- **[GR-E2]** The overlap criterion: a chart member at `ι` lies in the `ι'`-chart iff
its pointwise transition matrix is invertible (Stacks 089T step (4) — the overlap is
`D(det T)`). -/
theorem isChartAt_iff_isUnit_det (ι ι' : Fin k ↪ Fin n) (N : G(k, (Fin n → A); A))
    (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N) :
    IsChartAt (fun i => Pi.single (ι' i) (1 : A)) N ↔
      IsUnit (transitionMatrixAt ι ι' N h).det := by
  classical
  have h' : Function.Bijective
      ⇑(N.toSubmodule.mkQ ∘ₗ coordMap (fun i => Pi.single (ι i) (1 : A))) := h
  -- the ι'-chart composite factors through the ι-chart iso and the transition matrix
  have hsquare : N.toSubmodule.mkQ ∘ₗ coordMap (fun i => Pi.single (ι' i) (1 : A))
      = (N.toSubmodule.mkQ ∘ₗ coordMap (fun i => Pi.single (ι i) (1 : A))) ∘ₗ
        Matrix.toLin' (transitionMatrixAt ι ι' N h) := by
    refine (Pi.basisFun A (Fin k)).ext fun i₂ => ?_
    rw [Pi.basisFun_apply, LinearMap.comp_apply, coordMap_single, LinearMap.comp_apply,
      Matrix.toLin'_apply]
    have hcol : transitionMatrixAt ι ι' N h *ᵥ Pi.single i₂ 1
        = (LinearEquiv.ofBijective
            (N.toSubmodule.mkQ ∘ₗ coordMap (fun i => Pi.single (ι i) (1 : A))) h').symm
          (N.toSubmodule.mkQ (Pi.single (ι' i₂) 1)) := by
      funext i₁
      rw [Matrix.mulVec_single]
      exact mul_one _
    rw [hcol]
    exact ((LinearEquiv.ofBijective _ h').apply_symm_apply _).symm
  -- bijectivity of the composite reduces to invertibility of the matrix
  simp only [IsChartAt]
  rw [hsquare, LinearMap.coe_comp, Function.Bijective.of_comp_iff' h']
  have hAlg : (Matrix.toLinAlgEquiv' (transitionMatrixAt ι ι' N h) :
      (Fin k → A) →ₗ[A] (Fin k → A)) = Matrix.toLin' (transitionMatrixAt ι ι' N h) := by
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]
  rw [← hAlg, ← Module.End.isUnit_iff, ← Matrix.isUnit_iff_isUnit_det]
  constructor
  · intro hu
    simpa using hu.map (Matrix.toLinAlgEquiv' (n := Fin k) (R := A)).symm
  · intro hu
    exact hu.map (Matrix.toLinAlgEquiv' (n := Fin k) (R := A))

end Module.Grassmannian

/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.ForMathlib.GrassmannianChart
import ModularCurves.ForMathlib.GrassmannianTransition
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

section Spec

open MvPolynomial

variable (ι ι' : Fin k ↪ Fin n) (N : G(k, (Fin n → A); A))

/-- **[GR-SPEC]** Evaluation of the generic ι-chart coordinate ring at a chart member:
the generic matrix variable `X (j, i)` goes to the member's chart-matrix entry. -/
noncomputable def evalAt (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N) :
    ChartRing A ι →+* A :=
  eval₂Hom (RingHom.id A) (fun p => chartMatrix n ι N h p.1 p.2)

/-- `evalAt` sends the generic ι-column of any index `j` to the ι-retraction values of
the `j`-th coordinate vector. -/
lemma evalAt_column (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N)
    (h' : Function.Bijective
      ⇑(N.toSubmodule.mkQ ∘ₗ coordMap (fun i => Pi.single (ι i) (1 : A))))
    (j : Fin n) :
    (fun i₁ => evalAt ι N h (Transition.column ι j i₁))
      = (LinearEquiv.ofBijective _ h').symm (N.toSubmodule.mkQ (Pi.single j 1)) := by
  classical
  by_cases hj : j ∈ Set.range ι
  · obtain ⟨i₀, rfl⟩ := hj
    have hR : (LinearEquiv.ofBijective _ h').symm
        (N.toSubmodule.mkQ (Pi.single (ι i₀) 1)) = Pi.single i₀ (1 : A) := by
      rw [LinearEquiv.symm_apply_eq]
      show N.toSubmodule.mkQ (Pi.single (ι i₀) 1)
        = (N.toSubmodule.mkQ ∘ₗ coordMap (fun i => Pi.single (ι i) (1 : A)))
          (Pi.single i₀ 1)
      rw [LinearMap.comp_apply, coordMap_single]
    rw [hR]
    funext i₁
    rw [congrFun (Transition.column_mem ι i₀) i₁, Pi.single_apply, Pi.single_apply]
    split <;> simp [evalAt]
  · funext i₁
    rw [congrFun (Transition.column_notMem ι hj) i₁, evalAt, eval₂Hom_X']
    rfl

/-- `evalAt` carries the generic transition matrix to the pointwise one. -/
lemma evalAt_matrix (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N)
    (h' : Function.Bijective
      ⇑(N.toSubmodule.mkQ ∘ₗ coordMap (fun i => Pi.single (ι i) (1 : A)))) :
    (Transition.matrix ι ι').map ⇑(evalAt ι N h) = transitionMatrixAt ι ι' N h := by
  funext i₁ i₂
  show evalAt ι N h (Transition.column ι (ι' i₂) i₁) = _
  exact congrFun (evalAt_column ι N h h' (ι' i₂)) i₁

/-- The generic transition determinant evaluates to a unit on the chart overlap. -/
lemma isUnit_evalAt_det (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N)
    (hι' : IsChartAt (fun i => Pi.single (ι' i) (1 : A)) N) :
    IsUnit (evalAt ι N h (Transition.det (R := A) ι ι')) := by
  have h' : Function.Bijective
      ⇑(N.toSubmodule.mkQ ∘ₗ coordMap (fun i => Pi.single (ι i) (1 : A))) := h
  have hmap : evalAt ι N h (Transition.det (R := A) ι ι')
      = (transitionMatrixAt ι ι' N h).det := by
    rw [Transition.det, RingHom.map_det, RingHom.mapMatrix_apply,
      evalAt_matrix ι ι' N h h']
  rw [hmap]
  exact (isChartAt_iff_isUnit_det ι ι' N h).mp hι'

/-- **[GR-SPEC]** The evaluation of the ι-chart ring at a chart member, extended over
the overlap localization. -/
noncomputable def evalAwayAt (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N)
    (hι' : IsChartAt (fun i => Pi.single (ι' i) (1 : A)) N) :
    Localization.Away (Transition.det (R := A) ι ι') →+* A :=
  IsLocalization.Away.lift (Transition.det (R := A) ι ι')
    (isUnit_evalAt_det ι ι' N h hι')

/-- The pointwise transition matrix acting on coordinates, expressed through the chart
isomorphism: `T *ᵥ w` is the ι-retraction of the ι'-combination of `w`. -/
private lemma transitionMatrixAt_mulVec
    (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N)
    (h' : Function.Bijective
      ⇑(N.toSubmodule.mkQ ∘ₗ coordMap (fun i => Pi.single (ι i) (1 : A))))
    (w : Fin k → A) :
    transitionMatrixAt ι ι' N h *ᵥ w
      = (LinearEquiv.ofBijective _ h').symm
          (N.toSubmodule.mkQ (coordMap (fun i => Pi.single (ι' i) (1 : A)) w)) := by
  rw [coordMap_apply, map_sum, map_sum]
  funext i₁
  rw [Finset.sum_apply]
  simp only [map_smul]
  rw [show (transitionMatrixAt ι ι' N h *ᵥ w) i₁
      = ∑ i₂, w i₂ * transitionMatrixAt ι ι' N h i₁ i₂ by
    simp [Matrix.mulVec, dotProduct, mul_comm]]
  refine Finset.sum_congr rfl fun i₂ _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  rfl

/-- The generic-variable case of `evalAwayAt_comp_ringHom`: for the chart variable
`X_{j',i'}`, the extended ι-evaluation of the transition image equals the ι'-evaluation.
The localized solution vector `u = (matrixAway)⁻¹ ·(ι-column of j')` and the ι'-chart
matrix both solve `T *ᵥ ? = evalAt(ι-column j')`, so cancelling the invertible `T` matches
them. Extracted from `evalAwayAt_comp_ringHom` (the `ringHom_ext` generator branch). -/
private lemma evalAwayAt_comp_ringHom_X
    (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N)
    (hι' : IsChartAt (fun i => Pi.single (ι' i) (1 : A)) N)
    (p : {j : Fin n // j ∉ Set.range ι'} × Fin k) :
    (evalAwayAt ι ι' N h hι').comp (Transition.ringHom (R := A) ι ι') (X p)
      = evalAt ι' N hι' (X p) := by
  classical
  have h'ι : Function.Bijective
      ⇑(N.toSubmodule.mkQ ∘ₗ coordMap (fun i => Pi.single (ι i) (1 : A))) := h
  have h'ι' : Function.Bijective
      ⇑(N.toSubmodule.mkQ ∘ₗ coordMap (fun i => Pi.single (ι' i) (1 : A))) := hι'
  have hlift : ∀ q : ChartRing A ι,
      evalAwayAt ι ι' N h hι'
        (algebraMap (ChartRing A ι) (Localization.Away (Transition.det (R := A) ι ι')) q)
      = evalAt ι N h q :=
    fun q => IsLocalization.Away.lift_eq _ (isUnit_evalAt_det ι ι' N h hι') q
  have hdetT : IsUnit (transitionMatrixAt ι ι' N h).det :=
    (isChartAt_iff_isUnit_det ι ι' N h).mp hι'
  obtain ⟨⟨j', hj'⟩, i'⟩ := p
  rw [RingHom.comp_apply, Transition.ringHom, eval₂Hom_X']
  -- the localized solution vector and its image under the extended evaluation
  set T := transitionMatrixAt ι ι' N h with hT
  set u : Fin k → Localization.Away (Transition.det (R := A) ι ι') :=
    (Transition.matrixAway (R := A) ι ι')⁻¹ *ᵥ
      (fun i₁ => algebraMap (ChartRing A ι) _ (Transition.column ι j' i₁)) with hu
  -- the extended evaluation carries the localized matrix to `T`
  have hMap : (Transition.matrixAway (R := A) ι ι').map ⇑(evalAwayAt ι ι' N h hι')
      = T := by
    funext i₁ i₂
    simp only [Transition.matrixAway, Matrix.map_apply]
    rw [hlift]
    exact congrFun (congrFun (evalAt_matrix ι ι' N h h'ι) i₁) i₂
  -- the evaluated solution solves `T *ᵥ ? = (ι-retraction of the j'-column)`
  have hTu : T *ᵥ (⇑(evalAwayAt ι ι' N h hι') ∘ u)
      = fun i₁ => evalAt ι N h (Transition.column ι j' i₁) := by
    funext i₁
    rw [← hMap, ← RingHom.map_mulVec, hu]
    rw [show (Transition.matrixAway (R := A) ι ι') *ᵥ
        ((Transition.matrixAway (R := A) ι ι')⁻¹ *ᵥ
          (fun i₁ => algebraMap (ChartRing A ι) _ (Transition.column ι j' i₁)))
        = fun i₁ => algebraMap (ChartRing A ι) _ (Transition.column ι j' i₁) by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
        (Transition.isUnit_det_matrixAway ι ι'), Matrix.one_mulVec]]
    exact hlift _
  -- the ι'-chart matrix solves the same equation
  have hTw : T *ᵥ chartMatrix n ι' N hι' ⟨j', hj'⟩
      = fun i₁ => evalAt ι N h (Transition.column ι j' i₁) := by
    rw [hT, transitionMatrixAt_mulVec ι ι' N h h'ι]
    have hmk : N.toSubmodule.mkQ
        (coordMap (fun i => Pi.single (ι' i) (1 : A))
          (chartMatrix n ι' N hι' ⟨j', hj'⟩))
        = N.toSubmodule.mkQ (Pi.single j' 1) := by
      show (N.toSubmodule.mkQ ∘ₗ coordMap (fun i => Pi.single (ι' i) (1 : A)))
        (chartMatrix n ι' N hι' ⟨j', hj'⟩) = _
      rw [show chartMatrix n ι' N hι' ⟨j', hj'⟩
          = (LinearEquiv.ofBijective _ h'ι').symm
            (N.toSubmodule.mkQ (Pi.single j' 1)) from rfl]
      exact (LinearEquiv.ofBijective _ h'ι').apply_symm_apply _
    rw [hmk]
    exact (evalAt_column ι N h h'ι j').symm
  -- cancel the invertible matrix
  have hcancel : ⇑(evalAwayAt ι ι' N h hι') ∘ u
      = chartMatrix n ι' N hι' ⟨j', hj'⟩ := by
    have hEq := hTu.trans hTw.symm
    have := congrArg (fun v => T⁻¹ *ᵥ v) hEq
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdetT,
      Matrix.one_mulVec] using this
  have hfin := congrFun hcancel i'
  rw [Function.comp_apply] at hfin
  rw [hfin, evalAt, eval₂Hom_X']

/-- **[GR-SPEC], the spec**: extending the ι-evaluation over the overlap and
precomposing with the generic transition map recovers the ι'-evaluation — the glue
square of the chart atlas commutes with evaluation at every chart member. -/
theorem evalAwayAt_comp_ringHom
    (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N)
    (hι' : IsChartAt (fun i => Pi.single (ι' i) (1 : A)) N) :
    (evalAwayAt ι ι' N h hι').comp (Transition.ringHom (R := A) ι ι')
      = evalAt ι' N hι' := by
  classical
  have hlift : ∀ q : ChartRing A ι,
      evalAwayAt ι ι' N h hι'
        (algebraMap (ChartRing A ι) (Localization.Away (Transition.det (R := A) ι ι')) q)
      = evalAt ι N h q :=
    fun q => IsLocalization.Away.lift_eq _ (isUnit_evalAt_det ι ι' N h hι') q
  apply MvPolynomial.ringHom_ext
  · intro a
    rw [RingHom.comp_apply, Transition.ringHom, eval₂Hom_C, RingHom.comp_apply, hlift]
    rw [evalAt, eval₂Hom_C, evalAt, eval₂Hom_C]
  · intro p
    exact evalAwayAt_comp_ringHom_X ι ι' N h hι' p

end Spec

end Module.Grassmannian

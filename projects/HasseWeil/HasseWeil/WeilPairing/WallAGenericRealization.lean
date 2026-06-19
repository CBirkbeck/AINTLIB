/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.IsogenyBaseChangeConcrete
import HasseWeil.EC.GenericPoint

/-!
# Wall A: the concrete base-changed pullback realized at the generic point (CoordHom-free)

This file discharges the **G-004 compatibility square** — the genuine residual for realizing the
opaque base-changed pullback `pullback_L = baseChangePullback f = Φ ∘ (id_L ⊗ f) ∘ Φ⁻¹`
(`IsogenyBaseChangeConcrete.lean`) on the generic-point coordinates over `L = K̄`.

## The core compatibility (the conceptually-hard, reusable Wall A content)

* `tensorFunctionFieldEquiv_one_tmul` (Silverman I.2 / base change): the function-field
  scalar-extension iso `Φ : (L ⊗_F K(C)) ≃ₐ[L] K(C_L)` collapses on `algebraMap`'d elements to the
  *natural inclusion* `functionFieldMap`:

    `Φ (1 ⊗ z) = functionFieldMap L z`.

  Proved CoordHom-free by `IsFractionRing.ringHom_ext` over `C.CR`: both `Φ ∘ (1 ⊗ ·)` and
  `functionFieldMap` are `F`-algebra homs out of the fraction field `K(C) = Frac(C.CR)`, so they
  agree iff they agree on `C.CR`, where both reduce to `coordRingMap` (via the localization-uniqueness
  characterisations of the two component isos `IsLocalization.algEquiv` / `IsFractionRing.algEquivOfAlgEquiv`).

* `baseChangePullback_functionFieldMap`: the immediate corollary — the conjugate `baseChangePullback`
  intertwines `f` with `functionFieldMap`:

    `baseChangePullback f (functionFieldMap z) = functionFieldMap (f z)`.

  (Apply `Φ⁻¹(functionFieldMap z) = 1 ⊗ z`, then `lTensorMap_tmul`, then `Φ(1 ⊗ f z) = functionFieldMap (f z)`.)

* `functionFieldMap_x_gen` / `functionFieldMap_y_gen`: base change sends the `K`-level generic
  coordinates to the `K̄`-level generic coordinates (`functionFieldMap (x_gen W) = x_gen (W.baseChange L)`,
  similarly `y_gen`), via `functionFieldMap_algebraMap` + `CoordinateRing.map_mk` on the `X`/root generators.

* `ffBaseChangePoint` and `ffBaseChangePoint_genericPoint`: the function-field base-change point map
  `Affine.Point.map (functionField_baseChange)` sends `genericPoint W ↦ genericPoint (W.baseChange L)`.

## The payoff for `1 − π`

`oneSubFrobeniusPullback_L_x_gen` / `_y_gen`: the **concrete** base-changed pullback of `1 − π`,
evaluated at the `K̄`-generic coordinates, is the `functionFieldMap`-image of the `K`-level
addition-formula pullback:

  `oneSubFrobeniusPullback_L (x_gen^{K̄}) = functionFieldMap ((1 − π).pullback x_gen^K)`,

CoordHom-free and axiom-clean.  This is exactly the G-004 sketch in `CurveMapBaseChange.lean`, but
realized **without** the CoordHom the sketch assumes — purely from the function-field base-change
naturality (`functionFieldMap`) which is complete in the project.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, I.2 (base change), III.4.2 (generic point),
  III.8.2 (translation covariance).
-/

open WeierstrassCurve HasseWeil.Curves
open scoped TensorProduct

namespace HasseWeil.WeilPairing.IsogenyBaseChangeConcrete

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

section Compat

variable {F : Type*} [Field F] (C : SmoothPlaneCurve F)
variable (L : Type*) [Field L] [Algebra F L] [Algebra.IsAlgebraic F L]

/-- **The function-field scalar-extension iso collapses to the natural inclusion on `algebraMap`'d
elements** (Silverman I.2):

  `Φ (1 ⊗ z) = functionFieldMap z`   for `z : K(C)`,

where `Φ = tensorFunctionFieldEquiv : (L ⊗_F K(C)) ≃ₐ[L] K(C_L)`.  This is the G-004 compatibility
square, proved CoordHom-free.

Proof: both `Φ ∘ (1 ⊗ ·)` (the `F`-algebra hom `z ↦ Φ (1 ⊗ z) = Φ (includeRight z)`) and
`functionFieldMap` are ring homs `K(C) →+* K(C_L)`; by `IsFractionRing.ringHom_ext` over `C.CR`
(`K(C) = Frac(C.CR)`) they agree iff they agree on `algebraMap C.CR K(C)`-elements.  There the LHS
reduces — via `1 ⊗ (algMap u) = structureHom (1 ⊗ u) = algebraMap (L⊗C.CR) (L⊗K(C)) (1 ⊗ u)`, the
inner equiv commuting with `algebraMap (L⊗C.CR)` (`AlgEquiv.commutes`), the outer
`IsFractionRing.algEquivOfAlgEquiv_algebraMap`, and `fwdPinned_tmul` — to
`algebraMap (C_L).CR (C_L).FF (coordRingMap u)`, which is exactly `functionFieldMap (algMap u)`
(`functionFieldMap_algebraMap`). -/
theorem tensorFunctionFieldEquiv_one_tmul (z : C.toAffine.FunctionField) :
    letI := C.isDomain_tensorCoordRing L
    tensorFunctionFieldEquiv C L (1 ⊗ₜ[F] z) = C.functionFieldMap L z := by
  letI := C.isDomain_tensorCoordRing L
  have hrh : ((tensorFunctionFieldEquiv C L).toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := F) (A := L)
          (B := C.toAffine.FunctionField)).toRingHom) =
      (C.functionFieldMap L) := by
    refine IsFractionRing.ringHom_ext (A := C.toAffine.CoordinateRing) ?_
    intro u
    rw [RingHom.comp_apply]
    rw [C.functionFieldMap_algebraMap L u]
    show tensorFunctionFieldEquiv C L
        (Algebra.TensorProduct.includeRight
          (algebraMap C.toAffine.CoordinateRing C.toAffine.FunctionField u)) = _
    rw [Algebra.TensorProduct.includeRight_apply]
    have hstruct : (1 : L) ⊗ₜ[F]
          (algebraMap C.toAffine.CoordinateRing C.toAffine.FunctionField u) =
        C.tensorFunctionFieldStructureHom L (1 ⊗ₜ[F] u) := by
      show _ = Algebra.TensorProduct.map (AlgHom.id L L)
        (IsScalarTower.toAlgHom F C.toAffine.CoordinateRing C.toAffine.FunctionField) (1 ⊗ₜ[F] u)
      rw [Algebra.TensorProduct.map_tmul]
      rfl
    rw [hstruct]
    letI := C.tensorFunctionFieldAlgebra L
    letI : IsScalarTower L (L ⊗[F] C.toAffine.CoordinateRing)
        (L ⊗[F] C.toAffine.FunctionField) :=
      IsScalarTower.of_algebraMap_eq fun l ↦
        ((C.tensorFunctionFieldStructureHom L).commutes l).symm
    have halg : C.tensorFunctionFieldStructureHom L (1 ⊗ₜ[F] u) =
        algebraMap (L ⊗[F] C.toAffine.CoordinateRing) (L ⊗[F] C.toAffine.FunctionField)
           (1 ⊗ₜ[F] u) := rfl
    rw [halg]
    show (C.functionField_baseChange_fracEquiv L)
        (C.functionField_tensor_locBaseChange L
          (algebraMap (L ⊗[F] C.toAffine.CoordinateRing) (L ⊗[F] C.toAffine.FunctionField)
            (1 ⊗ₜ[F] u))) = _
    rw [show C.functionField_tensor_locBaseChange L
          (algebraMap (L ⊗[F] C.toAffine.CoordinateRing) (L ⊗[F] C.toAffine.FunctionField)
            (1 ⊗ₜ[F] u)) =
        algebraMap (L ⊗[F] C.toAffine.CoordinateRing)
          (FractionRing (L ⊗[F] C.toAffine.CoordinateRing)) (1 ⊗ₜ[F] u) from ?_]
    · rw [show C.functionField_baseChange_fracEquiv L =
            IsFractionRing.algEquivOfAlgEquiv (C.coordRingScalarExtPinned L) from rfl]
      rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
      congr 1
      show C.fwdPinned L (1 ⊗ₜ[F] u) = C.coordRingMap L u
      rw [C.fwdPinned_tmul, one_smul]
    · haveI := C.tensor_functionField_isFractionRing L
      have hinner : C.functionField_tensor_locBaseChange L =
          (IsLocalization.algEquiv (nonZeroDivisors (L ⊗[F] C.toAffine.CoordinateRing))
            (L ⊗[F] C.toAffine.FunctionField)
            (FractionRing (L ⊗[F] C.toAffine.CoordinateRing))).restrictScalars L := rfl
      rw [hinner, AlgEquiv.restrictScalars_apply]
      exact (IsLocalization.algEquiv (nonZeroDivisors (L ⊗[F] C.toAffine.CoordinateRing))
          (L ⊗[F] C.toAffine.FunctionField)
          (FractionRing (L ⊗[F] C.toAffine.CoordinateRing))).commutes (1 ⊗ₜ[F] u)
  have h := RingHom.congr_fun hrh z
  rw [RingHom.comp_apply] at h
  rw [← h]
  rfl

/-- **The base-changed pullback intertwines `f` with the natural inclusion** (Silverman I.2):

  `baseChangePullback f (functionFieldMap z) = functionFieldMap (f z)`.

Immediate from `tensorFunctionFieldEquiv_one_tmul`: `Φ⁻¹(functionFieldMap z) = 1 ⊗ z`,
`(id_L ⊗ f)(1 ⊗ z) = 1 ⊗ f z` (`lTensorMap_tmul`), `Φ(1 ⊗ f z) = functionFieldMap (f z)`. -/
theorem baseChangePullback_functionFieldMap
    (f : C.toAffine.FunctionField →ₐ[F] C.toAffine.FunctionField)
    (z : C.toAffine.FunctionField) :
    baseChangePullback C L f (C.functionFieldMap L z) =
      C.functionFieldMap L (f z) := by
  letI := C.isDomain_tensorCoordRing L
  rw [baseChangePullback_apply]
  rw [show (tensorFunctionFieldEquiv C L).symm (C.functionFieldMap L z) = 1 ⊗ₜ[F] z from ?_]
  · rw [lTensorMap_tmul, tensorFunctionFieldEquiv_one_tmul]
  · rw [← tensorFunctionFieldEquiv_one_tmul C L z, AlgEquiv.symm_apply_apply]

end Compat

/-! ### Step 2: `functionFieldMap` on the generic coordinates -/

section GenericCoords

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
variable (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  [(W.baseChange L).toAffine.IsElliptic]

/-- `coordRingMap` sends the `X`-generator class to the `X`-generator class. -/
theorem coordRingMap_X_gen :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).coordRingMap L
        (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X) =
      algebraMap (Polynomial L) (W.baseChange L).toAffine.CoordinateRing Polynomial.X := by
  change WeierstrassCurve.Affine.CoordinateRing.map W.toAffine (algebraMap K L)
    (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)) = _
  rw [WeierstrassCurve.Affine.CoordinateRing.map_mk]
  rw [show ((Polynomial.C Polynomial.X : Polynomial (Polynomial K)).map
        (Polynomial.mapRingHom (algebraMap K L))) =
        Polynomial.C Polynomial.X by
      rw [Polynomial.map_C, Polynomial.coe_mapRingHom, Polynomial.map_X]]
  show WeierstrassCurve.Affine.CoordinateRing.mk (W.baseChange L).toAffine (Polynomial.C Polynomial.X) =
    algebraMap (Polynomial L) (W.baseChange L).toAffine.CoordinateRing Polynomial.X
  rfl

/-- `coordRingMap` sends the `Y`-generator (the `AdjoinRoot` root) to the `Y`-generator. -/
theorem coordRingMap_Y_gen :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).coordRingMap L
        (AdjoinRoot.root W.toAffine.polynomial) =
      AdjoinRoot.root (W.baseChange L).toAffine.polynomial := by
  rw [← AdjoinRoot.mk_X]
  change WeierstrassCurve.Affine.CoordinateRing.map W.toAffine (algebraMap K L)
    (AdjoinRoot.mk W.toAffine.polynomial Polynomial.X) = _
  rw [WeierstrassCurve.Affine.CoordinateRing.map_mk, Polynomial.map_X, AdjoinRoot.mk_X]
  rfl

/-- **Base change sends `x_gen^K` to `x_gen^{K̄}`** (Silverman I.2): `functionFieldMap (x_gen W) =
x_gen (W.baseChange L)`. -/
theorem functionFieldMap_x_gen :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (HasseWeil.x_gen W) =
      HasseWeil.x_gen (W.baseChange L) := by
  rw [HasseWeil.x_gen]
  rw [SmoothPlaneCurve.functionFieldMap_algebraMap, coordRingMap_X_gen]
  rfl

/-- **Base change sends `y_gen^K` to `y_gen^{K̄}`** (Silverman I.2): `functionFieldMap (y_gen W) =
y_gen (W.baseChange L)`. -/
theorem functionFieldMap_y_gen :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (HasseWeil.y_gen W) =
      HasseWeil.y_gen (W.baseChange L) := by
  rw [HasseWeil.y_gen]
  rw [SmoothPlaneCurve.functionFieldMap_algebraMap, coordRingMap_Y_gen]
  rfl

end GenericCoords

/-! ### Step 3: the function-field base-change point map on the generic point -/

section PointMap

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
variable (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [Algebra.IsAlgebraic K L]
  [(W.baseChange L).toAffine.IsElliptic]

/-- **The function-field base-change point map** `Affine.Point.map (functionField_baseChange)`, typed
via `W' := W` over the base field `K` (so the codomain `W.baseChange (K(E_L))` is definitionally
`W_KE (W.baseChange L)` by the scalar tower `K → L → K(E_L)`).  The geometric realization of the
function-field inclusion `functionFieldMap : K(E) → K(E_L)` on `E`-points. -/
noncomputable def ffBaseChangePoint :=
  WeierstrassCurve.Affine.Point.map (W' := W) (S := K)
    ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionField_baseChange L)

/-- **`ffBaseChangePoint` on a `some` point**: applies `functionFieldMap` to both coordinates
(`Affine.Point.map_some`). -/
theorem ffBaseChangePoint_some (x y : W.toAffine.FunctionField)
    (h : (W_KE W).toAffine.Nonsingular x y) :
    ffBaseChangePoint W L (Affine.Point.some x y h) =
      Affine.Point.some
        ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L x)
        ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L y)
        ((WeierstrassCurve.Affine.baseChange_nonsingular W.toAffine
          ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionField_baseChange L).injective x y).mpr h) :=
  rfl

/-- **The base-change point map sends the generic point to the generic point** (Silverman I.2/III.4.2):
`ffBaseChangePoint (genericPoint W) = genericPoint (W.baseChange L)`.  Both are `some` of the
respective generic coordinates; `Affine.Point.map` of a `some` is definitionally a `some` whose
coordinates are the `functionFieldMap`-images, which are the base-changed generic coordinates
(`functionFieldMap_x_gen` / `functionFieldMap_y_gen`). -/
theorem ffBaseChangePoint_genericPoint :
    ffBaseChangePoint W L (HasseWeil.genericPoint W) =
      HasseWeil.genericPoint (W.baseChange L) := by
  rw [HasseWeil.genericPoint, HasseWeil.genericPoint]
  apply (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr
  exact ⟨functionFieldMap_x_gen W L, functionFieldMap_y_gen W L⟩

end PointMap

/-! ### The payoff for `1 − π`: the concrete pullback on the generic coordinates -/

section OneSub

open HasseWeil.WeilPairing

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
variable (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [Algebra.IsAlgebraic K L]
  [(W.baseChange L).toAffine.IsElliptic]

/-- **The concrete base-changed pullback of `1 − π` on the `K̄`-generic x-coordinate** (the G-004
square, CoordHom-free): `oneSubFrobeniusPullback_L (x_gen^{K̄}) = functionFieldMap ((1 − π).pullback x_gen^K)`.

Pure chaining of `functionFieldMap_x_gen` (`x_gen^{K̄} = functionFieldMap x_gen^K`) and
`baseChangePullback_functionFieldMap` (the conjugate intertwines `(1 − π).pullback` with
`functionFieldMap`).  This is the value of the *opaque* base-changed pullback on the generic
x-coordinate, realized as the function-field base-change of the explicit `K`-level
addition-formula pullback — exactly the G-004 sketch, but **without** the CoordHom it assumes. -/
theorem oneSubFrobeniusPullback_L_x_gen (hq : 2 ≤ Fintype.card K) :
    oneSubFrobeniusPullback_L W L hq (HasseWeil.x_gen (W.baseChange L)) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L
        ((HasseWeil.isogOneSub_negFrobenius W hq).pullback (HasseWeil.x_gen W)) := by
  rw [oneSubFrobeniusPullback_L, ← functionFieldMap_x_gen W L]
  exact baseChangePullback_functionFieldMap (⟨W.toAffine⟩ : SmoothPlaneCurve K) L
    (HasseWeil.isogOneSub_negFrobenius W hq).pullback (HasseWeil.x_gen W)

/-- **The concrete base-changed pullback of `1 − π` on the `K̄`-generic y-coordinate** (the G-004
square, CoordHom-free): `oneSubFrobeniusPullback_L (y_gen^{K̄}) = functionFieldMap ((1 − π).pullback y_gen^K)`.
The `y`-analogue of `oneSubFrobeniusPullback_L_x_gen`. -/
theorem oneSubFrobeniusPullback_L_y_gen (hq : 2 ≤ Fintype.card K) :
    oneSubFrobeniusPullback_L W L hq (HasseWeil.y_gen (W.baseChange L)) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L
        ((HasseWeil.isogOneSub_negFrobenius W hq).pullback (HasseWeil.y_gen W)) := by
  rw [oneSubFrobeniusPullback_L, ← functionFieldMap_y_gen W L]
  exact baseChangePullback_functionFieldMap (⟨W.toAffine⟩ : SmoothPlaneCurve K) L
    (HasseWeil.isogOneSub_negFrobenius W hq).pullback (HasseWeil.y_gen W)

end OneSub

end HasseWeil.WeilPairing.IsogenyBaseChangeConcrete

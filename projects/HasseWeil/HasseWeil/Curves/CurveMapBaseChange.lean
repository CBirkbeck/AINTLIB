/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.BaseChange
import HasseWeil.Curves.CurveMap
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.RingTheory.AlgebraTower
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Base change of curves and curve maps

For a smooth plane curve `C / F` and an `F`-algebra extension `L`, this file builds the
natural scalar-extension maps and identifies the scalar extension of the coordinate ring
and function field with the base-changed curve. These are foundations for the
Galois-descent route to the unconditional `AddHomProperty` (Phase G of the Pic⁰ roadmap).

## Main definitions

* `SmoothPlaneCurve.coordRingMap` — the include of coordinate rings.
* `SmoothPlaneCurve.functionFieldMap` — the include of function fields.
* `SmoothPlaneCurve.coordRingScalarExt` — the scalar-extension iso
  `L ⊗[F] C.CoordinateRing ≃ₐ[L] (C.baseChange L).CoordinateRing`.
* `CurveMap.CoordHom.baseChangeAlgHom` — the base-changed coordinate-ring alg hom of a `CoordHom`.

## Main results

* `SmoothPlaneCurve.isDomain_tensorCoordRing` — `L ⊗[F] C.CoordinateRing` is a domain.
* `SmoothPlaneCurve.tensor_functionField_isFractionRing` — `L ⊗[F] C.FunctionField` is the
  fraction ring of `L ⊗[F] C.CoordinateRing`.
* `SmoothPlaneCurve.functionField_tensor_locBaseChange` — localization commutes with the base
  change `L/F`: `L ⊗[F] C.FunctionField ≃ₐ[L] FractionRing (L ⊗[F] C.CoordinateRing)`.

## Implementation notes

The `Algebra F` / `Algebra F[X]` instances on `AdjoinRoot W.polynomial` form a typeclass
diamond that blocks synthesis of the tensor-product algebra/module structures. Section
`PhaseGInstances` pins the F-route instances at high priority so signatures mentioning
`L ⊗[F] C.CoordinateRing` (and its function-field analogue) elaborate diamond-free.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], I.2 — base change.
-/

open WeierstrassCurve
open scoped TensorProduct

namespace HasseWeil.Curves

namespace SmoothPlaneCurve

variable {F : Type*} [Field F] (C : SmoothPlaneCurve F)

/-- The ring hom on coordinate rings induced by the base change `F → L`.
This is `WeierstrassCurve.Affine.CoordinateRing.map` applied to the
algebra map. -/
noncomputable def coordRingMap (L : Type*) [Field L] [Algebra F L] :
    C.CoordinateRing →+* (C.baseChange L).CoordinateRing :=
  WeierstrassCurve.Affine.CoordinateRing.map C.toAffine (algebraMap F L)

theorem coordRingMap_injective (L : Type*) [Field L] [Algebra F L] :
    Function.Injective (C.coordRingMap L) :=
  WeierstrassCurve.Affine.CoordinateRing.map_injective
    (FaithfulSMul.algebraMap_injective F L)

/-- The induced field hom on function fields, lifted from `coordRingMap`
via `IsFractionRing.map`. -/
noncomputable def functionFieldMap (L : Type*) [Field L] [Algebra F L] :
    C.FunctionField →+* (C.baseChange L).FunctionField :=
  IsFractionRing.map (C.coordRingMap_injective L)

theorem functionFieldMap_injective (L : Type*) [Field L] [Algebra F L] :
    Function.Injective (C.functionFieldMap L) :=
  (C.functionFieldMap L).injective

@[simp] theorem functionFieldMap_algebraMap (L : Type*) [Field L]
    [Algebra F L] (u : C.CoordinateRing) :
    C.functionFieldMap L (algebraMap C.CoordinateRing C.FunctionField u) =
      algebraMap (C.baseChange L).CoordinateRing
        (C.baseChange L).FunctionField (C.coordRingMap L u) := by
  unfold functionFieldMap
  exact IsLocalization.map_eq _ _

end SmoothPlaneCurve

namespace CurveMap.CoordHom

variable {F : Type*} [Field F] {C₁ C₂ : SmoothPlaneCurve F}

/-- L-base-changed image of `cd.toAlgHom` applied to the canonical X
class in `C₂.CoordinateRing`. This is where X of `(C₂.baseChange L).CR`
maps under the base-changed alg hom. -/
noncomputable def baseChangeXImage {φ : CurveMap C₁ C₂} (cd : φ.CoordHom)
    (L : Type*) [Field L] [Algebra F L] :
    (C₁.baseChange L).CoordinateRing :=
  C₁.coordRingMap L
    (cd.toAlgHom (algebraMap (Polynomial F) C₂.CoordinateRing Polynomial.X))

/-- L-base-changed image of `cd.toAlgHom` applied to the canonical Y
(i.e., the AdjoinRoot root) in `C₂.CoordinateRing`. -/
noncomputable def baseChangeYImage {φ : CurveMap C₁ C₂} (cd : φ.CoordHom)
    (L : Type*) [Field L] [Algebra F L] :
    (C₁.baseChange L).CoordinateRing :=
  C₁.coordRingMap L (cd.toAlgHom (AdjoinRoot.root C₂.toAffine.polynomial))

/-- The inner `L[X]`-algebra hom needed for `AdjoinRoot.liftAlgHom`:
sends X of L[X] to `baseChangeXImage`. -/
noncomputable def baseChangeInnerAlgHom {φ : CurveMap C₁ C₂} (cd : φ.CoordHom)
    (L : Type*) [Field L] [Algebra F L] :
    Polynomial L →ₐ[L] (C₁.baseChange L).CoordinateRing :=
  Polynomial.aeval (cd.baseChangeXImage L)

/-- The composition `(coordRingMap C₁ L).comp cd.toAlgHom.toRingHom` as
a ring hom `C₂.CR →+* (C₁.baseChange L).CR`. -/
noncomputable abbrev coordCompose {φ : CurveMap C₁ C₂} (cd : φ.CoordHom)
    (L : Type*) [Field L] [Algebra F L] :
    C₂.CoordinateRing →+* (C₁.baseChange L).CoordinateRing :=
  (C₁.coordRingMap L).comp cd.toAlgHom.toRingHom

/-- `coordRingMap` commutes with the F-algebra-map of constants:
applying `coordRingMap` to `algebraMap F C.CR a` gives
`algebraMap F (C.baseChange L).CR a`. -/
theorem _root_.HasseWeil.Curves.SmoothPlaneCurve.coordRingMap_algebraMap_F
    (C : SmoothPlaneCurve F) (L : Type*) [Field L] [Algebra F L] (a : F) :
    C.coordRingMap L (algebraMap F C.CoordinateRing a) =
      algebraMap F (C.baseChange L).CoordinateRing a := by
  change WeierstrassCurve.Affine.CoordinateRing.map C.toAffine (algebraMap F L)
    (WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine
      (Polynomial.C (Polynomial.C a))) = _
  rw [WeierstrassCurve.Affine.CoordinateRing.map_mk,
    show ((Polynomial.C (Polynomial.C a) : Polynomial (Polynomial F)).map
        (Polynomial.mapRingHom (algebraMap F L))) =
        Polynomial.C (Polynomial.C ((algebraMap F L) a)) by
      rw [Polynomial.map_C, Polynomial.coe_mapRingHom, Polynomial.map_C]]
  rfl

/-- The base-change include `K(C) → K(C ⊗ L)` commutes with `algebraMap F`. -/
theorem _root_.HasseWeil.Curves.SmoothPlaneCurve.functionFieldMap_algebraMap_F
    (C : SmoothPlaneCurve F) (L : Type*) [Field L] [Algebra F L] (a : F) :
    C.functionFieldMap L (algebraMap F C.FunctionField a) =
      algebraMap F (C.baseChange L).FunctionField a := by
  rw [show algebraMap F C.FunctionField a =
        algebraMap C.CoordinateRing C.FunctionField (algebraMap F C.CoordinateRing a)
      from (IsScalarTower.algebraMap_apply F C.CoordinateRing C.FunctionField a),
    SmoothPlaneCurve.functionFieldMap_algebraMap,
    SmoothPlaneCurve.coordRingMap_algebraMap_F C L a]
  exact (IsScalarTower.algebraMap_apply F (C.baseChange L).CoordinateRing
    (C.baseChange L).FunctionField a).symm

/-- The base-change include `K(C) → K(C ⊗ L)` packaged as an F-algebra hom. -/
noncomputable def _root_.HasseWeil.Curves.SmoothPlaneCurve.functionField_baseChange
    (C : SmoothPlaneCurve F) (L : Type*) [Field L] [Algebra F L] :
    C.FunctionField →ₐ[F] (C.baseChange L).FunctionField where
  toRingHom := C.functionFieldMap L
  commutes' a := SmoothPlaneCurve.functionFieldMap_algebraMap_F C L a

@[simp] theorem _root_.HasseWeil.Curves.SmoothPlaneCurve.functionField_baseChange_apply
    (C : SmoothPlaneCurve F) (L : Type*) [Field L] [Algebra F L]
    (f : C.FunctionField) :
    C.functionField_baseChange L f = C.functionFieldMap L f := rfl

theorem baseChange_inner_comp_mapRingHom_eq {φ : CurveMap C₁ C₂}
    (cd : φ.CoordHom) (L : Type*) [Field L] [Algebra F L] :
    ((cd.baseChangeInnerAlgHom L).toRingHom.comp
        (Polynomial.mapRingHom (algebraMap F L))) =
      (cd.coordCompose L).comp
        (algebraMap (Polynomial F) C₂.CoordinateRing) := by
  apply Polynomial.ringHom_ext
  · intro a
    change (cd.baseChangeInnerAlgHom L)
        ((Polynomial.C a).map (algebraMap F L)) =
      C₁.coordRingMap L (cd.toAlgHom
        (algebraMap (Polynomial F) C₂.CoordinateRing (Polynomial.C a)))
    rw [Polynomial.map_C]
    change (cd.baseChangeInnerAlgHom L) (Polynomial.C (algebraMap F L a)) = _
    unfold baseChangeInnerAlgHom
    rw [Polynomial.aeval_C, show (algebraMap (Polynomial F) C₂.CoordinateRing) (Polynomial.C a) =
          algebraMap F C₂.CoordinateRing a from
        (IsScalarTower.algebraMap_apply F (Polynomial F) C₂.CoordinateRing a),
      AlgHom.commutes, SmoothPlaneCurve.coordRingMap_algebraMap_F C₁ L a,
      IsScalarTower.algebraMap_apply F L (C₁.baseChange L).CoordinateRing a]
  · change (cd.baseChangeInnerAlgHom L) (Polynomial.X.map (algebraMap F L)) =
      C₁.coordRingMap L (cd.toAlgHom
        (algebraMap (Polynomial F) C₂.CoordinateRing Polynomial.X))
    rw [Polynomial.map_X]
    change Polynomial.aeval (cd.baseChangeXImage L) Polynomial.X = _
    rw [Polynomial.aeval_X]
    rfl

theorem baseChange_eval₂_zero {φ : CurveMap C₁ C₂} (cd : φ.CoordHom)
    (L : Type*) [Field L] [Algebra F L] :
    (C₂.toAffine.baseChange L).toAffine.polynomial.eval₂
        (cd.baseChangeInnerAlgHom L).toRingHom (cd.baseChangeYImage L) = 0 := by
  rw [show (C₂.toAffine.baseChange L).toAffine.polynomial =
        C₂.toAffine.polynomial.map (Polynomial.mapRingHom (algebraMap F L)) from
      WeierstrassCurve.Affine.map_polynomial (algebraMap F L) (W := C₂.toAffine),
    Polynomial.eval₂_map, baseChange_inner_comp_mapRingHom_eq]
  change Polynomial.eval₂ ((cd.coordCompose L).comp
        (algebraMap (Polynomial F) C₂.CoordinateRing))
      ((cd.coordCompose L) (AdjoinRoot.root C₂.toAffine.polynomial))
      C₂.toAffine.polynomial = 0
  rw [← Polynomial.hom_eval₂ C₂.toAffine.polynomial
      (algebraMap (Polynomial F) C₂.CoordinateRing) (cd.coordCompose L)
      (AdjoinRoot.root C₂.toAffine.polynomial),
    show C₂.toAffine.polynomial.eval₂
        (algebraMap (Polynomial F) C₂.CoordinateRing)
        (AdjoinRoot.root C₂.toAffine.polynomial) = 0 from
      AdjoinRoot.eval₂_root C₂.toAffine.polynomial]
  exact map_zero _

/-- The base-changed alg hom on coordinate rings, lifting `cd.toAlgHom`
along F → L. Constructed via `AdjoinRoot.liftAlgHom`. -/
noncomputable def baseChangeAlgHom {φ : CurveMap C₁ C₂} (cd : φ.CoordHom)
    (L : Type*) [Field L] [Algebra F L] :
    (C₂.baseChange L).CoordinateRing →ₐ[L]
      (C₁.baseChange L).CoordinateRing :=
  AdjoinRoot.liftAlgHom (C₂.toAffine.baseChange L).toAffine.polynomial
    (cd.baseChangeInnerAlgHom L) (cd.baseChangeYImage L)
    (cd.baseChange_eval₂_zero L)

end CurveMap.CoordHom

namespace SmoothPlaneCurve

variable {F : Type*} [Field F] (C : SmoothPlaneCurve F)

/-- `coordRingMap` packaged as an F-algebra hom (it commutes with
`algebraMap F`, as proved by `coordRingMap_algebraMap_F`). -/
noncomputable def coordRingAlgHom (L : Type*) [Field L] [Algebra F L] :
    C.CoordinateRing →ₐ[F] (C.baseChange L).CoordinateRing where
  toRingHom := C.coordRingMap L
  commutes' a := C.coordRingMap_algebraMap_F L a

@[simp] theorem coordRingAlgHom_apply (L : Type*) [Field L] [Algebra F L]
    (u : C.CoordinateRing) :
    C.coordRingAlgHom L u = C.coordRingMap L u := rfl

end SmoothPlaneCurve

section PhaseGInstances

variable {F : Type*} [Field F] (C : SmoothPlaneCurve F)

/-- F-Algebra structure on the coordinate ring, pinned at high priority
to win the diamond against the F[X]-base. -/
noncomputable instance (priority := 100000) coordRingAlgebraBase :
    Algebra F C.toAffine.CoordinateRing :=
  inferInstance

/-- F-Module structure on the coordinate ring (derived from F-Algebra). -/
noncomputable instance (priority := 100000) coordRingModuleBase :
    Module F C.toAffine.CoordinateRing :=
  Algebra.toModule

/-- `CommRing` on the scalar-extension tensor `L ⊗[F] C.CR`, pinned at high
priority. The default synthesis loses to the `Algebra F` / `Algebra F[X]`
diamond on `AdjoinRoot W.polynomial` (it tries the `F[X]`-route algebra on
`C.CR`); pinning the F-route `CommRing` here unblocks any signature that
mentions `L ⊗[F] C.CR` (e.g. `FractionRing (L ⊗[F] C.CR)`). -/
noncomputable instance (priority := 100000) tensorCoordRingCommRing
    (L : Type*) [Field L] [Algebra F L] :
    CommRing (L ⊗[F] C.toAffine.CoordinateRing) :=
  Algebra.TensorProduct.instCommRing

/-- `L`-algebra structure on the scalar-extension tensor, pinned (left factor). -/
noncomputable instance (priority := 100000) tensorCoordRingLAlgebra
    (L : Type*) [Field L] [Algebra F L] :
    Algebra L (L ⊗[F] C.toAffine.CoordinateRing) :=
  Algebra.TensorProduct.leftAlgebra

/-- `F`-algebra (base-ring) structure on the scalar-extension tensor `L ⊗[F] C.CR`,
pinned. This is the canonical `Algebra.TensorProduct.instAlgebra`, whose `toModule`
is the standard `TensorProduct` `F`-module (so it is compatible with
`TensorProduct.ext'`). Needed so `Algebra.toModule`/`LinearMap.restrictScalars F`
in `tensorFunctionFieldStructureHom_injective` synthesize against the pinned
high-priority `CommRing` (which otherwise shadows the default `Algebra F` route). -/
noncomputable instance (priority := 100000) tensorCoordRingFAlgebra
    (L : Type*) [Field L] [Algebra F L] :
    Algebra F (L ⊗[F] C.toAffine.CoordinateRing) :=
  Algebra.TensorProduct.instAlgebra

/-- `IsScalarTower F L (L ⊗[F] C.CR)`, pinned (companion to the base-ring algebra). -/
noncomputable instance (priority := 100000) tensorCoordRingFLScalarTower
    (L : Type*) [Field L] [Algebra F L] :
    IsScalarTower F L (L ⊗[F] C.toAffine.CoordinateRing) :=
  inferInstance

/-- `F`-algebra (base-ring) structure on the function-field scalar-extension tensor
`L ⊗[F] C.FF`, pinned. Companion of `tensorCoordRingFAlgebra` at the function-field
level (codomain of `tensorFunctionFieldStructureHom`). -/
noncomputable instance (priority := 100000) tensorFunctionFieldFAlgebra
    (L : Type*) [Field L] [Algebra F L] :
    Algebra F (L ⊗[F] C.toAffine.FunctionField) :=
  Algebra.TensorProduct.instAlgebra

/-- `IsScalarTower F L (L ⊗[F] C.FF)`, pinned. -/
noncomputable instance (priority := 100000) tensorFunctionFieldFLScalarTower
    (L : Type*) [Field L] [Algebra F L] :
    IsScalarTower F L (L ⊗[F] C.toAffine.FunctionField) :=
  inferInstance

/-- `CommRing` on the function-field scalar-extension tensor `L ⊗[F] C.FF`,
pinned at high priority. The same `Algebra F` / `Algebra F[X]` diamond on
`AdjoinRoot W.polynomial` that taints `L ⊗[F] C.CR` recurs at the function-field
level (since `C.FF = FractionRing C.CR` carries the `C.CR`-algebra, which routes
back through the diamond). Pinning the F-route `CommRing` unblocks any signature
mentioning `L ⊗[F] C.FF`. -/
noncomputable instance (priority := 100000) tensorFunctionFieldCommRing
    (L : Type*) [Field L] [Algebra F L] :
    CommRing (L ⊗[F] C.toAffine.FunctionField) :=
  Algebra.TensorProduct.instCommRing

/-- `L`-algebra structure on the function-field scalar-extension tensor, pinned
(left factor). -/
noncomputable instance (priority := 100000) tensorFunctionFieldLAlgebra
    (L : Type*) [Field L] [Algebra F L] :
    Algebra L (L ⊗[F] C.toAffine.FunctionField) :=
  Algebra.TensorProduct.leftAlgebra

/-- `CommRing` on the reversed coordinate-ring tensor `C.CR ⊗[F] L`, pinned. The reversed
`· ⊗[F] L` orientation (used by `Algebra.TensorProduct.isField_of_isAlgebraic` in
`tensor_functionField_isField`) re-triggers the `AdjoinRoot W.polynomial` diamond, so its
companions are pinned here too. -/
noncomputable instance (priority := 100000) tensorCoordRingCommRing'
    (L : Type*) [Field L] [Algebra F L] :
    CommRing (C.toAffine.CoordinateRing ⊗[F] L) :=
  Algebra.TensorProduct.instCommRing

/-- `F`-algebra (base-ring) structure on the reversed coordinate-ring tensor, pinned. -/
noncomputable instance (priority := 100000) tensorCoordRingFAlgebra'
    (L : Type*) [Field L] [Algebra F L] :
    Algebra F (C.toAffine.CoordinateRing ⊗[F] L) :=
  Algebra.TensorProduct.instAlgebra

/-- `C.CR`-algebra structure on the reversed coordinate-ring tensor (left factor), pinned. -/
noncomputable instance (priority := 100000) tensorCoordRingLeftAlgebra'
    (L : Type*) [Field L] [Algebra F L] :
    Algebra C.toAffine.CoordinateRing (C.toAffine.CoordinateRing ⊗[F] L) :=
  Algebra.TensorProduct.leftAlgebra

/-- `IsScalarTower F C.CR (C.CR ⊗[F] L)`, pinned (companion to the left-factor algebra).
Built explicitly via `of_algebraMap_eq` since the reversed-order `SMul` path is
diamond-affected and `inferInstance` fails. -/
noncomputable instance (priority := 100000) tensorCoordRingFLeftScalarTower'
    (L : Type*) [Field L] [Algebra F L] :
    IsScalarTower F C.toAffine.CoordinateRing (C.toAffine.CoordinateRing ⊗[F] L) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- `CommRing` on the reversed function-field tensor `C.FF ⊗[F] L`, pinned. -/
noncomputable instance (priority := 100000) tensorFunctionFieldCommRing'
    (L : Type*) [Field L] [Algebra F L] :
    CommRing (C.toAffine.FunctionField ⊗[F] L) :=
  Algebra.TensorProduct.instCommRing

/-- `F`-algebra (base-ring) structure on the reversed function-field tensor, pinned. -/
noncomputable instance (priority := 100000) tensorFunctionFieldFAlgebra'
    (L : Type*) [Field L] [Algebra F L] :
    Algebra F (C.toAffine.FunctionField ⊗[F] L) :=
  Algebra.TensorProduct.instAlgebra

end PhaseGInstances

namespace SmoothPlaneCurve

variable {F : Type*} [Field F] (C : SmoothPlaneCurve F)

/-- Forward direction of the scalar-extension equivalence:
`L ⊗_F C.CR →ₐ[L] (C.baseChange L).CR` via mathlib's `AlgHom.liftEquiv`
(the universal property of base change). The result type is omitted
intentionally: Lean infers the unambiguous one from the body, avoiding
typeclass-instance-path mismatches between the result-type and
body-elaboration phases. -/
noncomputable def coordRingScalarExtFwd (L : Type*) [Field L] [Algebra F L] :=
  AlgHom.liftEquiv F L C.toAffine.CoordinateRing
    (C.baseChange L).toAffine.CoordinateRing
    (C.coordRingAlgHom L)

@[simp] theorem coordRingScalarExtFwd_tmul (L : Type*) [Field L] [Algebra F L]
    (l : L) (u : C.toAffine.CoordinateRing) :
    C.coordRingScalarExtFwd L (l ⊗ₜ u) = l • C.coordRingMap L u :=
  AlgHom.liftEquiv_tmul (C.coordRingAlgHom L) l u

/-- The forward scalar-extension map sends `1 ⊗ u` to `coordRingMap L u`. -/
@[simp] theorem coordRingScalarExtFwd_one_tmul (L : Type*) [Field L] [Algebra F L]
    (u : C.toAffine.CoordinateRing) :
    C.coordRingScalarExtFwd L (1 ⊗ₜ u) = C.coordRingMap L u := by
  rw [coordRingScalarExtFwd_tmul, one_smul]

/-- The base-changed coordinate ring is `L`-generated by the image of `X` and the root:
`Algebra.adjoin L {of X, root} = ⊤`. -/
private theorem adjoin_baseChange_of_X_root_eq_top (L : Type*) [Field L] [Algebra F L] :
    Algebra.adjoin L
      ({AdjoinRoot.of (C.baseChange L).toAffine.polynomial Polynomial.X,
        AdjoinRoot.root (C.baseChange L).toAffine.polynomial} :
        Set (C.baseChange L).toAffine.CoordinateRing) = ⊤ := by
  rw [show ({AdjoinRoot.of (C.baseChange L).toAffine.polynomial Polynomial.X,
        AdjoinRoot.root (C.baseChange L).toAffine.polynomial} :
        Set (C.baseChange L).toAffine.CoordinateRing) =
      (algebraMap (Polynomial L) (C.baseChange L).toAffine.CoordinateRing ''
        {Polynomial.X}) ∪ {AdjoinRoot.root (C.baseChange L).toAffine.polynomial} by
      rw [Set.image_singleton, Set.insert_eq]; rfl,
    ← Algebra.adjoin_eq_adjoin_union L
    (A := Polynomial L) ({Polynomial.X} : Set (Polynomial L))
    ({AdjoinRoot.root (C.baseChange L).toAffine.polynomial} :
      Set (C.baseChange L).toAffine.CoordinateRing) Polynomial.adjoin_X,
    AdjoinRoot.adjoinRoot_eq_top, Subalgebra.restrictScalars_top]

/-- The forward scalar-extension map is surjective: every element of the
base-changed coordinate ring is hit. -/
theorem coordRingScalarExtFwd_surjective (L : Type*) [Field L] [Algebra F L] :
    Function.Surjective (C.coordRingScalarExtFwd L) := by
  rw [← AlgHom.range_eq_top, eq_top_iff]
  have hroot : AdjoinRoot.root (C.baseChange L).toAffine.polynomial ∈
      (C.coordRingScalarExtFwd L).range := by
    refine ⟨1 ⊗ₜ AdjoinRoot.root C.toAffine.polynomial, ?_⟩
    change C.coordRingScalarExtFwd L (1 ⊗ₜ AdjoinRoot.root C.toAffine.polynomial) = _
    rw [coordRingScalarExtFwd_one_tmul, ← AdjoinRoot.mk_X]
    change WeierstrassCurve.Affine.CoordinateRing.map C.toAffine (algebraMap F L)
      (AdjoinRoot.mk C.toAffine.polynomial Polynomial.X) = _
    rw [WeierstrassCurve.Affine.CoordinateRing.map_mk, Polynomial.map_X, AdjoinRoot.mk_X]
    rfl
  have hX : AdjoinRoot.of (C.baseChange L).toAffine.polynomial Polynomial.X ∈
      (C.coordRingScalarExtFwd L).range := by
    refine ⟨1 ⊗ₜ AdjoinRoot.mk C.toAffine.polynomial (Polynomial.C Polynomial.X), ?_⟩
    change C.coordRingScalarExtFwd L
      (1 ⊗ₜ AdjoinRoot.mk C.toAffine.polynomial (Polynomial.C Polynomial.X)) = _
    rw [coordRingScalarExtFwd_one_tmul]
    change WeierstrassCurve.Affine.CoordinateRing.map C.toAffine (algebraMap F L)
      (AdjoinRoot.mk C.toAffine.polynomial (Polynomial.C Polynomial.X)) = _
    rw [WeierstrassCurve.Affine.CoordinateRing.map_mk,
      show (Polynomial.C Polynomial.X :
          Polynomial (Polynomial F)).map (Polynomial.mapRingHom (algebraMap F L)) =
        Polynomial.C Polynomial.X by
      rw [Polynomial.map_C, Polynomial.coe_mapRingHom, Polynomial.map_X]]
    rfl
  rw [← C.adjoin_baseChange_of_X_root_eq_top L, Algebra.adjoin_le_iff]
  rintro x (rfl | rfl)
  exacts [hX, hroot]

/-- `CoordinateRing.map` matches the two affine coordinate-ring basis elements:
it sends the base `1`-element (`bᵢ` at `i = 0`) and the class of `X` (`bᵢ` at
`i = 1`) to the corresponding base-changed elements. The `Xⁿ` prefactor is handled
separately in `coordRingScalarExtFwd_tensorBasis_eq` via `map_smul`. -/
private theorem coordRingMap_basis_eq (L : Type*) [Field L] [Algebra F L]
    (i : Fin 2) :
    WeierstrassCurve.Affine.CoordinateRing.map C.toAffine (algebraMap F L)
        (WeierstrassCurve.Affine.CoordinateRing.basis C.toAffine i) =
      WeierstrassCurve.Affine.CoordinateRing.basis (C.baseChange L).toAffine i := by
  fin_cases i
  · simp only [Fin.isValue, Fin.mk_zero, Affine.CoordinateRing.basis_zero, map_one]
    rfl
  · simp only [Fin.isValue, Fin.mk_one,
      WeierstrassCurve.Affine.CoordinateRing.basis_one]
    change WeierstrassCurve.Affine.CoordinateRing.map C.toAffine (algebraMap F L)
      (AdjoinRoot.mk C.toAffine.polynomial Polynomial.X) = _
    rw [WeierstrassCurve.Affine.CoordinateRing.map_mk, Polynomial.map_X]
    rfl

/-- The forward scalar-extension map carries the tensored monomial basis
`bLA = (L ⊗) (X-monomials ⊗ affine basis)` of `L ⊗[F] C.CoordinateRing` to the
monomial basis `bD` of the base-changed coordinate ring, index by index. -/
private theorem coordRingScalarExtFwd_tensorBasis_eq (L : Type*) [Field L]
    [Algebra F L] (ij : ℕ × Fin 2) :
    (C.coordRingScalarExtFwd L).toLinearMap
        (Algebra.TensorProduct.basis L
          ((Polynomial.basisMonomials F).smulTower
            (WeierstrassCurve.Affine.CoordinateRing.basis C.toAffine)) ij) =
      (Polynomial.basisMonomials L).smulTower
        (WeierstrassCurve.Affine.CoordinateRing.basis (C.baseChange L).toAffine) ij := by
  obtain ⟨n, i⟩ := ij
  rw [Algebra.TensorProduct.basis_apply]
  change C.coordRingScalarExtFwd L
    (1 ⊗ₜ (Polynomial.basisMonomials F).smulTower
      (WeierstrassCurve.Affine.CoordinateRing.basis C.toAffine) (n, i)) = _
  rw [coordRingScalarExtFwd_one_tmul, Module.Basis.smulTower_apply,
    Module.Basis.smulTower_apply]
  simp only [Polynomial.coe_basisMonomials, Polynomial.monomial_one_right_eq_X_pow]
  show WeierstrassCurve.Affine.CoordinateRing.map C.toAffine (algebraMap F L)
      (Polynomial.X ^ n •
        WeierstrassCurve.Affine.CoordinateRing.basis C.toAffine i) = _
  rw [WeierstrassCurve.Affine.CoordinateRing.map_smul, Polynomial.map_pow,
    Polynomial.map_X]
  congr 1
  exact C.coordRingMap_basis_eq L i

/-- The forward scalar-extension map is injective: it carries the `L`-basis
`{Xⁿ • bᵢ}` of `L ⊗[F] C.CoordinateRing` to the corresponding basis of the
base-changed coordinate ring. -/
theorem coordRingScalarExtFwd_injective (L : Type*) [Field L] [Algebra F L] :
    Function.Injective (C.coordRingScalarExtFwd L) := by
  classical
  set bLA : Module.Basis (ℕ × Fin 2) L (L ⊗[F] C.toAffine.CoordinateRing) :=
    Algebra.TensorProduct.basis L
      ((Polynomial.basisMonomials F).smulTower
        (WeierstrassCurve.Affine.CoordinateRing.basis C.toAffine))
  set bD : Module.Basis (ℕ × Fin 2) L (C.baseChange L).toAffine.CoordinateRing :=
    (Polynomial.basisMonomials L).smulTower
      (WeierstrassCurve.Affine.CoordinateRing.basis (C.baseChange L).toAffine)
  have heq : (C.coordRingScalarExtFwd L).toLinearMap =
      (bLA.equiv bD (Equiv.refl _)).toLinearMap := by
    refine bLA.ext fun ij ↦ (C.coordRingScalarExtFwd_tensorBasis_eq L ij).trans ?_
    exact (Module.Basis.equiv_apply bLA ij bD (Equiv.refl _)).symm
  rw [show ⇑(C.coordRingScalarExtFwd L) =
      ⇑(C.coordRingScalarExtFwd L).toLinearMap from rfl, heq]
  exact (bLA.equiv bD (Equiv.refl _)).injective

/-- The scalar-extension equivalence on coordinate rings:
`L ⊗_F C.CR ≃ₐ[L] (C.baseChange L).CR`, packaged from bijectivity of the forward
direction. The result type is omitted intentionally: written explicitly, the
`Semiring (L ⊗[F] C.CR)` instance fails to synthesize because of the `Algebra F` /
`Algebra F[X]` diamond on `AdjoinRoot`. Inferring it from `coordRingScalarExtFwd`'s
type — which carries the instance via `AlgHom.liftEquiv`'s machinery — avoids the
diamond. -/
noncomputable def coordRingScalarExt (L : Type*) [Field L] [Algebra F L] :=
  AlgEquiv.ofBijective (C.coordRingScalarExtFwd L)
    ⟨C.coordRingScalarExtFwd_injective L, C.coordRingScalarExtFwd_surjective L⟩

@[simp] theorem coordRingScalarExt_tmul (L : Type*) [Field L] [Algebra F L]
    (l : L) (u : C.toAffine.CoordinateRing) :
    C.coordRingScalarExt L (l ⊗ₜ u) = l • C.coordRingMap L u :=
  C.coordRingScalarExtFwd_tmul L l u

/-- Forward scalar-extension alg hom built against the **pinned** instances via
`Algebra.TensorProduct.lift` (so its domain carries the pinned `CommRing`). A separate
copy of `coordRingScalarExtFwd` is needed because the latter is typed against the
`CommRing` that `AlgHom.liftEquiv` synthesizes internally, which is not defeq to the
pinned `tensorCoordRingCommRing` that `IsFractionRing.algEquivOfAlgEquiv` requires. -/
noncomputable def fwdPinned (L : Type*) [Field L] [Algebra F L] :
    (L ⊗[F] C.toAffine.CoordinateRing) →ₐ[L] (C.baseChange L).toAffine.CoordinateRing :=
  Algebra.TensorProduct.lift
    (Algebra.ofId L (C.baseChange L).toAffine.CoordinateRing)
    ((C.coordRingAlgHom L).restrictScalars F)
    (fun _ _ ↦ mul_comm _ _)

@[simp] theorem fwdPinned_tmul (L : Type*) [Field L] [Algebra F L]
    (l : L) (u : C.toAffine.CoordinateRing) :
    C.fwdPinned L (l ⊗ₜ u) = l • C.coordRingMap L u := by
  simp only [fwdPinned]
  rw [Algebra.smul_def]
  rfl

/-- `fwdPinned` is surjective: its range contains `root` and the `X`-image, which
generate the codomain over `L` (same adjoin argument as
`coordRingScalarExtFwd_surjective`). -/
theorem fwdPinned_surjective (L : Type*) [Field L] [Algebra F L] :
    Function.Surjective (C.fwdPinned L) := by
  rw [← AlgHom.range_eq_top, eq_top_iff]
  have hroot : AdjoinRoot.root (C.baseChange L).toAffine.polynomial ∈
      (C.fwdPinned L).range := by
    refine ⟨1 ⊗ₜ AdjoinRoot.root C.toAffine.polynomial, ?_⟩
    change C.fwdPinned L (1 ⊗ₜ AdjoinRoot.root C.toAffine.polynomial) = _
    rw [fwdPinned_tmul, one_smul, ← AdjoinRoot.mk_X]
    change WeierstrassCurve.Affine.CoordinateRing.map C.toAffine (algebraMap F L)
      (AdjoinRoot.mk C.toAffine.polynomial Polynomial.X) = _
    rw [WeierstrassCurve.Affine.CoordinateRing.map_mk, Polynomial.map_X, AdjoinRoot.mk_X]
    rfl
  have hX : AdjoinRoot.of (C.baseChange L).toAffine.polynomial Polynomial.X ∈
      (C.fwdPinned L).range := by
    refine ⟨1 ⊗ₜ AdjoinRoot.mk C.toAffine.polynomial (Polynomial.C Polynomial.X), ?_⟩
    change C.fwdPinned L (1 ⊗ₜ AdjoinRoot.mk C.toAffine.polynomial (Polynomial.C Polynomial.X)) = _
    rw [fwdPinned_tmul, one_smul]
    change WeierstrassCurve.Affine.CoordinateRing.map C.toAffine (algebraMap F L)
      (AdjoinRoot.mk C.toAffine.polynomial (Polynomial.C Polynomial.X)) = _
    rw [WeierstrassCurve.Affine.CoordinateRing.map_mk,
      show (Polynomial.C Polynomial.X :
          Polynomial (Polynomial F)).map (Polynomial.mapRingHom (algebraMap F L)) =
        Polynomial.C Polynomial.X by
      rw [Polynomial.map_C, Polynomial.coe_mapRingHom, Polynomial.map_X]]
    rfl
  rw [← C.adjoin_baseChange_of_X_root_eq_top L, Algebra.adjoin_le_iff]
  rintro x (rfl | rfl)
  exacts [hX, hroot]

/-- `fwdPinned` is injective: it carries the `L`-basis `{Xⁿ • bᵢ}` of
`L ⊗[F] C.CoordinateRing` to the corresponding basis of the base-changed coordinate
ring (the pinned-instance analogue of `coordRingScalarExtFwd_injective`). -/
theorem fwdPinned_injective (L : Type*) [Field L] [Algebra F L] :
    Function.Injective (C.fwdPinned L) := by
  classical
  set bA : Module.Basis (ℕ × Fin 2) F C.toAffine.CoordinateRing :=
    (Polynomial.basisMonomials F).smulTower
      (WeierstrassCurve.Affine.CoordinateRing.basis C.toAffine) with hbA
  set bLA : Module.Basis (ℕ × Fin 2) L (L ⊗[F] C.toAffine.CoordinateRing) :=
    Algebra.TensorProduct.basis L bA with hbLA
  set bD : Module.Basis (ℕ × Fin 2) L (C.baseChange L).toAffine.CoordinateRing :=
    (Polynomial.basisMonomials L).smulTower
      (WeierstrassCurve.Affine.CoordinateRing.basis (C.baseChange L).toAffine) with hbD
  have hbasis : ∀ ij : ℕ × Fin 2,
      (C.fwdPinned L).toLinearMap (bLA ij) = bD ij := by
    rintro ⟨n, i⟩
    rw [hbLA, Algebra.TensorProduct.basis_apply]
    change C.fwdPinned L (1 ⊗ₜ bA (n, i)) = bD (n, i)
    rw [fwdPinned_tmul, one_smul, hbA, Module.Basis.smulTower_apply,
      hbD, Module.Basis.smulTower_apply]
    simp only [Polynomial.coe_basisMonomials, Polynomial.monomial_one_right_eq_X_pow]
    change WeierstrassCurve.Affine.CoordinateRing.map C.toAffine (algebraMap F L)
        (Polynomial.X ^ n •
          WeierstrassCurve.Affine.CoordinateRing.basis C.toAffine i) =
        Polynomial.X ^ n •
          WeierstrassCurve.Affine.CoordinateRing.basis (C.baseChange L).toAffine i
    rw [WeierstrassCurve.Affine.CoordinateRing.map_smul, Polynomial.map_pow,
      Polynomial.map_X]
    congr 1
    exact C.coordRingMap_basis_eq L i
  have heq : (C.fwdPinned L).toLinearMap =
      (bLA.equiv bD (Equiv.refl _)).toLinearMap := by
    refine bLA.ext fun ij ↦ (hbasis ij).trans ?_
    exact (Module.Basis.equiv_apply bLA ij bD (Equiv.refl _)).symm
  rw [show ⇑(C.fwdPinned L) =
      ⇑(C.fwdPinned L).toLinearMap from rfl, heq]
  exact (bLA.equiv bD (Equiv.refl _)).injective

/-- `fwdPinned` packaged as an `AlgEquiv` (it is bijective). This is the
scalar-extension iso typed against the **pinned** instances, suitable for
`IsFractionRing.algEquivOfAlgEquiv`. -/
noncomputable def coordRingScalarExtPinned (L : Type*) [Field L] [Algebra F L] :
    (L ⊗[F] C.toAffine.CoordinateRing) ≃ₐ[L] (C.baseChange L).toAffine.CoordinateRing :=
  AlgEquiv.ofBijective (C.fwdPinned L)
    ⟨C.fwdPinned_injective L, C.fwdPinned_surjective L⟩

/-- `L ⊗[F] C.CR` is a domain (over the pinned `CommRing`): transported from the
codomain coordinate ring (a domain) via injectivity of `fwdPinned`. -/
theorem isDomain_tensorCoordRing (L : Type*) [Field L] [Algebra F L] :
    IsDomain (L ⊗[F] C.toAffine.CoordinateRing) :=
  Function.Injective.isDomain (C.fwdPinned L).toRingHom (C.fwdPinned_injective L)

/-- **Function-field base-change iso**:
`FractionRing (L ⊗[F] C.CR) ≃ₐ[L] (C.baseChange L).FunctionField`, via
`IsFractionRing.algEquivOfAlgEquiv` applied to `coordRingScalarExtPinned`. The
base-ring localization instances on `FractionRing (L ⊗[F] C.CR)` synthesize once
`isDomain_tensorCoordRing` is in scope. -/
noncomputable def functionField_baseChange_fracEquiv (L : Type*) [Field L] [Algebra F L] :
    letI := C.isDomain_tensorCoordRing L
    FractionRing (L ⊗[F] C.toAffine.CoordinateRing) ≃ₐ[L]
      (C.baseChange L).toAffine.FunctionField :=
  letI := C.isDomain_tensorCoordRing L
  IsFractionRing.algEquivOfAlgEquiv (C.coordRingScalarExtPinned L)

/-- **Function-field base-change iso (tensor-side orientation)**:
`(C.baseChange L).FunctionField ≃ₐ[L] FractionRing (L ⊗[F] C.CR)`, the `.symm` of
`functionField_baseChange_fracEquiv`.

NOTE (soundness): the codomain is `FractionRing (L ⊗[F] C.CR)`, **not**
`L ⊗[F] C.FunctionField`. The latter is generally not a field (e.g.
`L ⊗[K] L` for `L/K` non-trivial), so no `L`-algebra iso to the (field)
function field can exist; the genuinely-correct tensor object is the fraction
field of `L ⊗[F] C.CR`. -/
noncomputable def functionField_baseChange_tensorEquiv (L : Type*) [Field L] [Algebra F L] :
    letI := C.isDomain_tensorCoordRing L
    (C.baseChange L).toAffine.FunctionField ≃ₐ[L]
      FractionRing (L ⊗[F] C.toAffine.CoordinateRing) :=
  letI := C.isDomain_tensorCoordRing L
  (C.functionField_baseChange_fracEquiv L).symm

/-- The natural base-changed localization map `L ⊗[F] C.CR →ₐ[L] L ⊗[F] C.FF`
(the `lTensor` of the localization map `C.CR → C.FF`), packaged as an
`L`-algebra hom. This is the structure map witnessing `L ⊗[F] C.FF` as a
localization/fraction ring of `L ⊗[F] C.CR`. -/
noncomputable def tensorFunctionFieldStructureHom (L : Type*) [Field L] [Algebra F L] :
    (L ⊗[F] C.toAffine.CoordinateRing) →ₐ[L] (L ⊗[F] C.toAffine.FunctionField) :=
  Algebra.TensorProduct.map (AlgHom.id L L)
    (IsScalarTower.toAlgHom F C.toAffine.CoordinateRing C.toAffine.FunctionField)

/-- The `L ⊗[F] C.CR`-algebra structure on `L ⊗[F] C.FF` via the natural localization
map `tensorFunctionFieldStructureHom`. Bundled so that
`tensor_functionField_isFractionRing` and the iso below share exactly one
algebra-instance spelling. -/
noncomputable abbrev tensorFunctionFieldAlgebra (L : Type*) [Field L] [Algebra F L] :
    Algebra (L ⊗[F] C.toAffine.CoordinateRing) (L ⊗[F] C.toAffine.FunctionField) :=
  (C.tensorFunctionFieldStructureHom L).toRingHom.toAlgebra

/-- The base-changed localization map `algebraMap (L ⊗[F] C.CoordinateRing) (L ⊗[F] C.FF)`
is injective: it is `lTensor L` of the injective localization `C.CoordinateRing → C.FF`,
and `L/F` is flat. Stated against the pinned `tensorFunctionFieldAlgebra` so it composes
diamond-free. -/
theorem tensorFunctionFieldStructureHom_injective (L : Type*) [Field L] [Algebra F L] :
    letI := C.tensorFunctionFieldAlgebra L
    Function.Injective
      (algebraMap (L ⊗[F] C.toAffine.CoordinateRing) (L ⊗[F] C.toAffine.FunctionField)) := by
  change Function.Injective (C.tensorFunctionFieldStructureHom L)
  set gF : C.toAffine.CoordinateRing →ₗ[F] C.toAffine.FunctionField :=
    (Algebra.linearMap C.toAffine.CoordinateRing C.toAffine.FunctionField).restrictScalars F
      with hgF
  have hg : Function.Injective gF := IsFractionRing.injective _ _
  have hlin : Function.Injective (LinearMap.lTensor L gF) :=
    Module.Flat.lTensor_preserves_injective_linearMap gF hg
  have hfun : ⇑(C.tensorFunctionFieldStructureHom L) = ⇑(LinearMap.lTensor L gF) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l u =>
        rw [LinearMap.lTensor_tmul]
        change Algebra.TensorProduct.map (AlgHom.id L L)
            (IsScalarTower.toAlgHom F C.toAffine.CoordinateRing C.toAffine.FunctionField)
            (l ⊗ₜ u) = l ⊗ₜ gF u
        rw [Algebra.TensorProduct.map_tmul]
        rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [hfun]
  exact hlin

/-- `C.CoordinateRing ⊗[F] L` is a domain, for any field extension `L/F`. Obtained from the
sibling `isDomain_tensorCoordRing` (which gives the `L`-on-the-left orientation
`L ⊗[F] C.CoordinateRing`) by transporting the domain structure across the commutativity
ring-iso `Algebra.TensorProduct.comm`. -/
private theorem tensorCoordRing_comm_isDomain (L : Type*) [Field L] [Algebra F L] :
    IsDomain (C.toAffine.CoordinateRing ⊗[F] L) := by
  letI := C.isDomain_tensorCoordRing L
  exact (Algebra.TensorProduct.comm F L C.toAffine.CoordinateRing).symm.toRingEquiv.toMulEquiv.isDomain
    (L ⊗[F] C.toAffine.CoordinateRing)

/-- The image, under the structure map `C.CoordinateRing → C.CoordinateRing ⊗[F] L`, of the
nonzerodivisors of `C.CoordinateRing` lands inside the nonzerodivisors of
`C.CoordinateRing ⊗[F] L`. The structure map is `Algebra.TensorProduct.includeLeft`, injective
because `C.CoordinateRing` is free (hence flat) over the field `F`; injective maps into a
`NoZeroDivisors` ring carry nonzerodivisors to nonzerodivisors. -/
private theorem tensorCoordRing_algebraMapSubmonoid_le_nonZeroDivisors
    (L : Type*) [Field L] [Algebra F L] :
    Algebra.algebraMapSubmonoid (C.toAffine.CoordinateRing ⊗[F] L)
        (nonZeroDivisors C.toAffine.CoordinateRing) ≤
      nonZeroDivisors (C.toAffine.CoordinateRing ⊗[F] L) := by
  haveI hflatCR : Module.Flat F C.toAffine.CoordinateRing := Module.Flat.of_free
  letI := C.tensorCoordRing_comm_isDomain L
  haveI hnzdCR : NoZeroDivisors (C.toAffine.CoordinateRing ⊗[F] L) :=
    isCancelMulZero_iff_noZeroDivisors.mp ‹IsDomain _›.toIsCancelMulZero
  have hinjL : Function.Injective
      (Algebra.TensorProduct.includeLeft :
        C.toAffine.CoordinateRing →ₐ[F] C.toAffine.CoordinateRing ⊗[F] L) :=
    @Algebra.TensorProduct.includeLeft_injective F F C.toAffine.CoordinateRing L
      _ _ _ _ _ _ _ _ hflatCR
      (RingHom.injective (algebraMap F L))
  exact map_le_nonZeroDivisors_of_injective
    (M₀' := C.toAffine.CoordinateRing ⊗[F] L)
    (algebraMap C.toAffine.CoordinateRing (C.toAffine.CoordinateRing ⊗[F] L))
    hinjL le_rfl

/-- `C.FunctionField ⊗[F] L` is a localization of `C.CoordinateRing ⊗[F] L` at the image of the
nonzerodivisors of `C.CoordinateRing`, with respect to the natural `lTensor`-of-localization
algebra structure `algBC`. This is the tensor–tensor localization
`IsLocalization.tensorProduct_tensorProduct` for the localization `C.CoordinateRing → C.FunctionField`
base-changed along `L/F`, with the scalar tower and structure-map equations discharged by `rfl`/`simp`. -/
private theorem tensorFunctionField_isLocalization (L : Type*) [Field L] [Algebra F L] :
    letI _algBC : Algebra (C.toAffine.CoordinateRing ⊗[F] L) (C.toAffine.FunctionField ⊗[F] L) :=
      (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom F C.toAffine.CoordinateRing C.toAffine.FunctionField)
        (AlgHom.id F L)).toRingHom.toAlgebra
    IsLocalization
      (Algebra.algebraMapSubmonoid (C.toAffine.CoordinateRing ⊗[F] L)
        (nonZeroDivisors C.toAffine.CoordinateRing))
      (C.toAffine.FunctionField ⊗[F] L) := by
  letI algBC : Algebra (C.toAffine.CoordinateRing ⊗[F] L) (C.toAffine.FunctionField ⊗[F] L) :=
    (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom F C.toAffine.CoordinateRing C.toAffine.FunctionField)
      (AlgHom.id F L)).toRingHom.toAlgebra
  haveI tower : IsScalarTower C.toAffine.CoordinateRing (C.toAffine.CoordinateRing ⊗[F] L)
      (C.toAffine.FunctionField ⊗[F] L) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact @IsLocalization.tensorProduct_tensorProduct F L _ _ _ C.toAffine.CoordinateRing _ _
    (nonZeroDivisors C.toAffine.CoordinateRing) C.toAffine.FunctionField _ _ _ _ _ algBC tower
    (by ext x
        change (Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom F C.toAffine.CoordinateRing C.toAffine.FunctionField)
          (AlgHom.id F L)) (1 ⊗ₜ x) = 1 ⊗ₜ x
        rw [Algebra.TensorProduct.map_tmul]
        simp)

/-- The base-changed function field `C.FunctionField ⊗[F] L` is a domain, for any extension
`L/F` (no algebraicity needed). It is the localization of the domain
`C.CoordinateRing ⊗[F] L` at the image of the nonzerodivisors of `C.CoordinateRing`, and
that image lands inside the nonzerodivisors (via flatness of `C.CoordinateRing` over `F`),
so the localization stays a domain.

This is the domain half of `tensor_functionField_isField`; kept separate so that
`isField_of_isAlgebraic` can pick it up as the required `IsDomain` instance. Phrased with
the function field on the **left** (`FunctionField ⊗[F] L`) to match that consumer. -/
private theorem tensorFunctionField_isDomain (L : Type*) [Field L] [Algebra F L] :
    IsDomain (C.toAffine.FunctionField ⊗[F] L) := by
  -- `C.CoordinateRing ⊗[F] L` is a domain (the base ring of the localization below).
  letI := C.tensorCoordRing_comm_isDomain L
  -- The natural `lTensor`-of-localization algebra structure exhibiting the function field
  -- tensor as a localization of the coordinate-ring tensor.
  letI _algBC : Algebra (C.toAffine.CoordinateRing ⊗[F] L) (C.toAffine.FunctionField ⊗[F] L) :=
    (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom F C.toAffine.CoordinateRing C.toAffine.FunctionField)
      (AlgHom.id F L)).toRingHom.toAlgebra
  haveI := C.tensorFunctionField_isLocalization L
  -- A localization of a domain at a submonoid of nonzerodivisors is again a domain.
  exact IsLocalization.isDomain_of_le_nonZeroDivisors (C.toAffine.FunctionField ⊗[F] L)
    (C.tensorCoordRing_algebraMapSubmonoid_le_nonZeroDivisors L)

/-- `L ⊗[F] C.FunctionField` is a field, for any algebraic extension `L/F`. This is the
geometric-integrality content: the scalar extension of the function field stays a field.
Stated as `IsField` (w.r.t. the pinned `CommRing`) to avoid a `Field`-instance diamond
when consumed by `tensor_functionField_isFractionRing`. -/
theorem tensor_functionField_isField (L : Type*) [Field L] [Algebra F L]
    [Algebra.IsAlgebraic F L] :
    IsField (L ⊗[F] C.toAffine.FunctionField) := by
  haveI := C.tensorFunctionField_isDomain L
  have hF : IsField (C.toAffine.FunctionField ⊗[F] L) :=
    Algebra.TensorProduct.isField_of_isAlgebraic F C.toAffine.FunctionField L
      (Or.inr (inferInstance : Algebra.IsAlgebraic F L))
  exact MulEquiv.isField hF
    (Algebra.TensorProduct.comm F L C.toAffine.FunctionField).toRingEquiv.toMulEquiv

/-- For a flat (here: free) extension `L/F`, the right-tensor inclusion
`c ↦ (1 ⊗ₜ c : L ⊗[F] C.CoordinateRing)` is injective. It is the composite of the
inverse left-unitor with the injective `rTensor` of `Algebra.linearMap F L`, which is
injective because `C.CoordinateRing` is flat over `F`. -/
private theorem oneTmulRight_injective (L : Type*) [Field L] [Algebra F L]
    [Module.Flat F L] :
    Function.Injective
      (fun c : C.toAffine.CoordinateRing ↦ (1 ⊗ₜ c : L ⊗[F] C.toAffine.CoordinateRing)) := by
  have hrt : Function.Injective
      (LinearMap.rTensor C.toAffine.CoordinateRing (Algebra.linearMap F L)) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := C.toAffine.CoordinateRing)
      (Algebra.linearMap F L) (RingHom.injective (algebraMap F L))
  have hcomp := hrt.comp (TensorProduct.lid F C.toAffine.CoordinateRing).symm.injective
  have heq : (fun c : C.toAffine.CoordinateRing ↦ (1 ⊗ₜ c : L ⊗[F] C.toAffine.CoordinateRing))
      = (LinearMap.rTensor C.toAffine.CoordinateRing (Algebra.linearMap F L))
          ∘ (TensorProduct.lid F C.toAffine.CoordinateRing).symm := by
    funext c
    simp only [Function.comp_apply, TensorProduct.lid_symm_apply,
      LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
  rw [heq]
  exact hcomp

/-- For a flat (here: free) extension `L/F`, a nonzero divisor `b` of `C.CoordinateRing`
stays a nonzero divisor after base change: `1 ⊗ₜ b` is a nonzero divisor of
`L ⊗[F] C.CoordinateRing`. Reduces to nonvanishing via `oneTmulRight_injective`. -/
private theorem oneTmul_mem_nonZeroDivisors (L : Type*) [Field L] [Algebra F L]
    [Module.Flat F L] (b : C.toAffine.CoordinateRing)
    (hb : b ∈ nonZeroDivisors C.toAffine.CoordinateRing) :
    (1 ⊗ₜ b : L ⊗[F] C.toAffine.CoordinateRing)
      ∈ nonZeroDivisors (L ⊗[F] C.toAffine.CoordinateRing) := by
  letI := C.isDomain_tensorCoordRing L
  rw [mem_nonZeroDivisors_iff_ne_zero]
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  intro hc
  exact hb0 (C.oneTmulRight_injective L (hc.trans (TensorProduct.tmul_zero _ _).symm))

/-- Surjectivity onto fractions: every element of `L ⊗[F] C.FF` is expressible as
`algebraMap a / algebraMap b` with `a : L ⊗ C.CR` and `b` a nonzero divisor, phrased
localization-style as `z * algebraMap b = algebraMap a`. Stated w.r.t. the pinned
algebra so it composes diamond-free into `tensor_functionField_isFractionRing`. -/
theorem tensor_functionField_surj (L : Type*) [Field L] [Algebra F L] :
    letI := C.tensorFunctionFieldAlgebra L
    ∀ z : L ⊗[F] C.toAffine.FunctionField,
      ∃ x : (L ⊗[F] C.toAffine.CoordinateRing) ×
          (nonZeroDivisors (L ⊗[F] C.toAffine.CoordinateRing)),
        z * algebraMap (L ⊗[F] C.toAffine.CoordinateRing)
            (L ⊗[F] C.toAffine.FunctionField) x.2
          = algebraMap (L ⊗[F] C.toAffine.CoordinateRing)
            (L ⊗[F] C.toAffine.FunctionField) x.1 := by
  letI alg := C.tensorFunctionFieldAlgebra L
  letI := C.isDomain_tensorCoordRing L
  haveI hflatL : Module.Flat F L := Module.Flat.of_free
  have halg : ∀ (l : L) (u : C.toAffine.CoordinateRing),
      algebraMap (L ⊗[F] C.toAffine.CoordinateRing) (L ⊗[F] C.toAffine.FunctionField) (l ⊗ₜ u)
        = l ⊗ₜ algebraMap C.toAffine.CoordinateRing C.toAffine.FunctionField u :=
    fun l u ↦ rfl
  refine fun z ↦ ?_
  induction z using TensorProduct.induction_on with
  | zero =>
      exact ⟨(0, 1), by rw [zero_mul, map_zero]⟩
  | tmul l f =>
      obtain ⟨a, b, hbmem, hab⟩ := IsFractionRing.div_surjective (A := C.toAffine.CoordinateRing) f
      refine ⟨(l ⊗ₜ a, ⟨1 ⊗ₜ b, C.oneTmul_mem_nonZeroDivisors L b hbmem⟩), ?_⟩
      rw [halg, halg, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      have hb0 : algebraMap C.toAffine.CoordinateRing C.toAffine.FunctionField b ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hbmem
      rw [← hab, div_mul_cancel₀ _ hb0]
  | add x y hx hy =>
      obtain ⟨⟨nx, dx⟩, hxeq⟩ := hx
      obtain ⟨⟨ny, dy⟩, hyeq⟩ := hy
      refine ⟨(nx * (dy : L ⊗[F] C.toAffine.CoordinateRing) + ny * dx, dx * dy), ?_⟩
      rw [Submonoid.coe_mul, map_mul, map_add, map_mul, map_mul]
      linear_combination (algebraMap (L ⊗[F] C.toAffine.CoordinateRing)
            (L ⊗[F] C.toAffine.FunctionField) (dy : L ⊗[F] C.toAffine.CoordinateRing)) * hxeq
        + (algebraMap (L ⊗[F] C.toAffine.CoordinateRing)
            (L ⊗[F] C.toAffine.FunctionField) (dx : L ⊗[F] C.toAffine.CoordinateRing)) * hyeq

/-- `L ⊗[F] C.FunctionField` is the fraction ring of `L ⊗[F] C.CoordinateRing`, for any
algebraic extension `L/F`. Stated w.r.t. the pinned `tensorFunctionFieldAlgebra`. -/
theorem tensor_functionField_isFractionRing (L : Type*) [Field L] [Algebra F L]
    [Algebra.IsAlgebraic F L] :
    @IsFractionRing (L ⊗[F] C.toAffine.CoordinateRing) _
      (L ⊗[F] C.toAffine.FunctionField) _ (C.tensorFunctionFieldAlgebra L) := by
  letI alg := C.tensorFunctionFieldAlgebra L
  letI := C.isDomain_tensorCoordRing L
  have hinj : Function.Injective
      (algebraMap (L ⊗[F] C.toAffine.CoordinateRing) (L ⊗[F] C.toAffine.FunctionField)) :=
    C.tensorFunctionFieldStructureHom_injective L
  have hfield : IsField (L ⊗[F] C.toAffine.FunctionField) := C.tensor_functionField_isField L
  rw [IsFractionRing, isLocalization_iff]
  refine ⟨fun y ↦ ?_, C.tensor_functionField_surj L, fun {x y} h ↦ ⟨1, by rw [hinj h]⟩⟩
  have hy : algebraMap (L ⊗[F] C.toAffine.CoordinateRing)
      (L ⊗[F] C.toAffine.FunctionField) y.1 ≠ 0 := by
    intro hc
    exact (mem_nonZeroDivisors_iff_ne_zero.mp y.2) (hinj (by rw [hc, map_zero]))
  obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hy
  exact IsUnit.of_mul_eq_one b hb

/-- Localization commutes with the base change `L/F`:
`L ⊗[F] C.FunctionField ≃ₐ[L] FractionRing (L ⊗[F] C.CoordinateRing)`, i.e.
`L ⊗[F] Frac(C.CR) ≃ₐ[L] Frac(L ⊗[F] C.CR)`. Both sides are localizations of the domain
`L ⊗[F] C.CR` at its nonzero divisors, so uniqueness of localizations gives the iso. -/
noncomputable def functionField_tensor_locBaseChange (L : Type*) [Field L] [Algebra F L]
    [Algebra.IsAlgebraic F L] :
    letI := C.isDomain_tensorCoordRing L
    (L ⊗[F] C.toAffine.FunctionField) ≃ₐ[L]
      FractionRing (L ⊗[F] C.toAffine.CoordinateRing) :=
  letI := C.isDomain_tensorCoordRing L
  letI := C.tensorFunctionFieldAlgebra L
  letI := C.tensor_functionField_isFractionRing L
  haveI : IsScalarTower L (L ⊗[F] C.toAffine.CoordinateRing)
      (L ⊗[F] C.toAffine.FunctionField) :=
    IsScalarTower.of_algebraMap_eq fun l ↦
      ((C.tensorFunctionFieldStructureHom L).commutes l).symm
  (IsLocalization.algEquiv (nonZeroDivisors (L ⊗[F] C.toAffine.CoordinateRing))
    (L ⊗[F] C.toAffine.FunctionField)
    (FractionRing (L ⊗[F] C.toAffine.CoordinateRing))).restrictScalars L

end SmoothPlaneCurve

end HasseWeil.Curves

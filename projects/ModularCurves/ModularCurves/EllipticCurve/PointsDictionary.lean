/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import ModularCurves.ForMathlib.ProjIntegral
import ModularCurves.ForMathlib.WeierstrassProjectivePrime
import ModularCurves.Moduli.WeierstrassAtlas

/-!
# T-W7 lane P2 — geometric integrality of `E_U^n` and the field-points dictionary

**Canonical P2 file** (consolidated 2026-07-07 per the coordinator directive; supersedes the
parallel `Moduli/PointsDictionary.lean`, now deleted).

* **T-W7.0e** the universal Weierstrass curve `E_U → U` is `GeometricallyIntegral`, hence its fibre
  powers `E_U ×_U … ×_U E_U` are **integral** (and so reduced) schemes — the source-integrality
  input to the generic-point argument establishing the group axioms over `U` (T-W7.0g). The
  "`smooth ⟹ geometrically reduced`" engine is **absent from mathlib**, so the route is the
  chart/domain fallback: `IsDomain (projCoordRing W)` (`ForMathlib/WeierstrassProjectivePrime.lean`
  — the projective Weierstrass cubic is prime, Eisenstein at `Z`; no `Δ ≠ 0` needed) + `Proj` of a
  graded domain is integral (`ForMathlib/ProjIntegral.lean`) ⟹ `IsIntegral (projModel W_K)`;
  base-change transport (`isPullback_projModelBaseChange`) ⟹
  `GeometricallyIntegral universalCurveπ`.

* **T-W7.0f** the field-points dictionary: `projModelPointsEquiv` (`K`-points of `projModel W`
  biject with `(W.baseChange K).toAffine.Point`, pointed at `[0:1:0] ↦ 0`), choice-extracted from
  the proven existential `projModel_points` (T-A2e). **REMAINING leaf (value-characterization):**
  the bare equiv pins only the zero value; the consumers `negModelHom_specPoints`,
  `T-W7.0c-iii`, and `T-W7.0g` need the *chartwise value* `projModelPointsEquiv_some` (an affine
  `Z`-chart point `(x,y) ↦ .some ⟨x,y⟩`). This requires `projModel_points`' currently-`private`
  chart components (`zSolutionsToAffine`, `affinePointSplit`, `infPoint`, WeierstrassModel.lean) to
  be exposed / `projModel_points` strengthened to characterise the equiv on chart points — tracked
  as **T-W7.0f-val**.

* **T-W7.0g-ext** `hom_ext_of_forall_specPoint` — the field-points extensionality principle
  (kept as a P0/0g leaf; now unblocked on its `[IsReduced X]` hypothesis by the 0e integrality
  here). Discharge names (verified): `isClosedImmersion_equalizer_ι_left`,
  `isIso_of_isClosedImmersion_of_surjective`, `fromSpecResidueField`.
-/

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace ModularCurves

/-! ## T-W7.0e — integrality of the universal curve and its fibre powers -/

/-- The atlas `U = Spec ℤ[a₁..a₆][Δ⁻¹]` is an integral scheme (Spec of the domain
`WeierstrassAtlasRing`; the domain instance lives upstream in `Moduli/WeierstrassAtlas.lean`). -/
instance : IsIntegral weierstrassAtlas := by rw [weierstrassAtlas]; infer_instance

/-- The atlas `U` is locally noetherian. -/
instance : IsLocallyNoetherian weierstrassAtlas := by rw [weierstrassAtlas]; infer_instance

instance : SmoothOfRelativeDimension 1 universalCurveπ := universalCurve_smooth
instance : Smooth universalCurveπ := SmoothOfRelativeDimension.smooth 1 universalCurveπ
instance : LocallyOfFinitePresentation universalCurveπ := inferInstance
instance : Flat universalCurveπ := inferInstance
instance : UniversallyOpen universalCurveπ := inferInstance

/-- `IsIntegral` is closed under isomorphism as a property of schemes (it is
`IrreducibleSpace ⊓ IsReduced`, both closed under isomorphism). -/
instance : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) (IsIntegral ·) where
  of_iso e hX := by
    rw [isIntegral_iff_irreducibleSpace_and_isReduced] at hX ⊢
    exact ⟨ObjectProperty.prop_of_iso (C := Scheme) (IrreducibleSpace ·) e hX.1,
           ObjectProperty.prop_of_iso (C := Scheme) (IsReduced ·) e hX.2⟩

/-- **(T-W7.0e-proj applied)** The projective model of a Weierstrass curve over a field is an
integral scheme: `projModel W = Proj (projCoordRing W)`, `projCoordRing W` is a graded domain with
nonzero positive-degree part `[X₀]`, so `AlgebraicGeometry.Proj.isIntegral_of_isDomain` applies. -/
instance isIntegral_projModel {K : Type} [Field K] (W : WeierstrassCurve K) :
    IsIntegral (projModel W) := by
  show IsIntegral (Proj (quotientGrading (projIdeal W)))
  refine AlgebraicGeometry.Proj.isIntegral_of_isDomain (𝒜 := quotientGrading (projIdeal W)) ?_
  refine ⟨1, one_pos, Ideal.Quotient.mk _ (MvPolynomial.X 0), ?_, ?_⟩
  · exact mk_mem_quotientGrading _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (MvPolynomial.isHomogeneous_X _ _))
  · rw [Ne, Ideal.Quotient.eq_zero_iff_mem, projIdeal_toIdeal, Ideal.mem_span_singleton]
    intro hdvd
    have hX0 : (MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) K) ≠ 0 :=
      MvPolynomial.X_ne_zero _
    have hF0 : W.toProjective.polynomial ≠ 0 := by
      rintro h
      rw [h] at hdvd
      exact hX0 (zero_dvd_iff.mp hdvd)
    have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdvd hX0
    rw [(projective_polynomial_isHomogeneous W).totalDegree hF0, MvPolynomial.totalDegree_X] at hle
    omega

/-- **(T-W7.0e crux — geometric integrality of the universal curve)** Each geometric fibre of
`E_U → U` is a projective plane Weierstrass cubic, hence an integral scheme. A field-valued point
`y : Spec K ⟶ U` makes `K` a `WeierstrassAtlasRing`-algebra (`Spec.preimage`), and
`isPullback_projModelBaseChange` identifies the base change with
`projModel (universalWeierstrassLoc.map (algebraMap _ K))`, integral by `isIntegral_projModel`;
transport across the pullback isomorphism finishes. -/
instance geometricallyIntegral_universalCurveπ : GeometricallyIntegral universalCurveπ := by
  rw [geometricallyIntegral_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  letI : Algebra WeierstrassAtlasRing K := (Spec.preimage y).hom.toAlgebra
  have hy : y = Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRing K)) := by
    have h1 : CommRingCat.ofHom (algebraMap WeierstrassAtlasRing K) = Spec.preimage y :=
      CommRingCat.ofHom_hom _
    rw [h1]
    exact (Spec.map_preimage y).symm
  have hpb := isPullback_projModelBaseChange (R := WeierstrassAtlasRing) (R' := K)
    universalWeierstrassLoc
  rw [← hy] at hpb
  exact ObjectProperty.prop_of_iso (IsIntegral ·) hpb.isoPullback (isIntegral_projModel _)

/-- The universal curve `E_U` is an integral scheme (geometrically integral, flat, universally
open over the integral, locally noetherian atlas). -/
instance : IsIntegral universalCurve :=
  GeometricallyIntegral.isIntegral_of_isLocallyNoetherian universalCurveπ

/-- The universal curve `E_U` is locally noetherian (locally of finite type over `U`). -/
instance : IsLocallyNoetherian universalCurve :=
  LocallyOfFiniteType.isLocallyNoetherian universalCurveπ

/-- **(T-W7.0e-i)** The universal curve is reduced (integral ⟹ reduced). -/
instance : IsReduced universalCurve := inferInstance

/-- **(T-W7.0e, n = 2)** The fibre square `E_U ×_U E_U` is an integral scheme. -/
instance : IsIntegral (pullback universalCurveπ universalCurveπ) := inferInstance

/-- **(T-W7.0e-ii)** The fibre square is reduced. -/
instance : IsReduced (pullback universalCurveπ universalCurveπ) := inferInstance

/-- **(T-W7.0e, n = 3)** The triple fibre power `E_U ×_U E_U ×_U E_U` is integral (both the
`snd`-associated and `fst`-associated spellings of the associativity source). -/
instance : IsIntegral (pullback universalCurveπ (pullback.snd universalCurveπ universalCurveπ ≫
    universalCurveπ)) := inferInstance

instance : IsIntegral (pullback (pullback.fst universalCurveπ universalCurveπ ≫ universalCurveπ)
    universalCurveπ) := inferInstance

/-- **(T-W7.0e-iii)** The fibre cube is reduced. -/
instance : IsReduced (pullback (pullback.fst universalCurveπ universalCurveπ ≫ universalCurveπ)
    universalCurveπ) := inferInstance

/-! ## T-W7.0f — the field-points dictionary (canonical form) -/

variable {R : Type u} [CommRing R]

/-- **(T-W7.0f-i — the field-points dictionary)** For an elliptic Weierstrass curve `W` over `R`
and any field `K`, the `K`-points of the projective model `projModel W` biject with mathlib's
affine points `(W.baseChange K).toAffine.Point`. Canonical (choice-extracted) form of the proven
existential dictionary `projModel_points` (T-A2e).

**Value-characterisation (T-W7.0f-val) is now available:** `projModelPointsEquiv` is the *explicit*
bijection `projModelPointsEquivEll` (not the choice-extracted one), so its values are pinned —
`projModelPointsEquiv_zero` (`[0:1:0] ↦ 0`) and `projModelPointsEquiv_some` (a `Z`-chart point with
coordinates `(x,y) ↦ some x y`), which the consumers `negModelHom_specPoints`, `T-W7.0c-iii` and
`T-W7.0g` read the coordinates through. -/
noncomputable def projModelPointsEquiv (W : WeierstrassCurve R) [W.IsElliptic]
    (K : Type u) [Field K] [Algebra R K] :
    SpecPoints (projModel W) (projModelπ W) K ≃ (W.baseChange K).toAffine.Point :=
  projModelPointsEquivEll W ‹W.IsElliptic› K

/-- **(T-W7.0f-ii — the dictionary is pointed)** The point at infinity `[0:1:0]` — the zero
section evaluated over `K` — corresponds under `projModelPointsEquiv` to the group identity `0`. -/
theorem projModelPointsEquiv_zero (W : WeierstrassCurve R) [W.IsElliptic]
    (K : Type u) [Field K] [Algebra R K] :
    projModelPointsEquiv W K ⟨Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ projModelZero W, by
      rw [Category.assoc, projModelZero_projModelπ, Category.comp_id]⟩ = 0 :=
  projModelPointsEquivEll_zero W ‹W.IsElliptic› K

/-- **(T-W7.0f-val — the dictionary on affine chart points)** A `K`-point of the model factoring
through the `Z`-chart with dehomogenised coordinates `(x, y)` corresponds under
`projModelPointsEquiv` to the affine point `some x y`. The value-characterisation the negation and
multiplication specs (`negModelHom_specPoints`, `mulModelHom_specPoints`) and the group axioms read
through. Coordinates and their nonsingularity are hypotheses, so callers supply their own
witness. -/
theorem projModelPointsEquiv_some (W : WeierstrassCurve R) [W.IsElliptic]
    (K : Type u) [Field K] [Algebra R K]
    (g : SpecPoints (projModel W) (projModelπ W) K) (hZ : InZChart W g)
    (x y : K) (hxy : (W.baseChange K).toAffine.Nonsingular x y)
    (hx : x = (chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨g, hZ⟩)).1 ⟨0, by decide⟩)
    (hy : y = (chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨g, hZ⟩)).1 ⟨1, by decide⟩) :
    projModelPointsEquiv W K g = WeierstrassCurve.Affine.Point.some x y hxy :=
  projModelPointsEquivEll_some W ‹W.IsElliptic› K g hZ x y hxy hx hy

/-- **(T-W7.0g-ext)** The field-points extensionality principle: two morphisms from a *reduced*
scheme to a *separated* scheme agreeing on composition with every field-valued point are equal.
Every point of `X` is hit by its residue-field point, so the (closed, by separatedness) equalizer
is topologically all of `X`; reducedness upgrades this to a scheme equality. The `[IsReduced X]`
hypothesis is now discharged for `X = E_U^n` by the 0e integrality above. Discharge names
(verified): `isClosedImmersion_equalizer_ι_left`, `isIso_of_isClosedImmersion_of_surjective`,
`fromSpecResidueField`. -/
theorem hom_ext_of_forall_specPoint {X Y : Scheme.{u}} [IsReduced X] [Y.IsSeparated]
    {f g : X ⟶ Y}
    (h : ∀ (K : Type u) [Field K] (p : Spec (CommRingCat.of K) ⟶ X), p ≫ f = p ≫ g) :
    f = g :=
  ext_of_fromSpecResidueField_eq f g (terminal.from Y) Set.univ dense_univ
    (fun x _ => h (X.residueField x) (X.fromSpecResidueField x)) (Subsingleton.elim _ _)

end ModularCurves

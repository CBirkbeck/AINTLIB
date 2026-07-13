import ModularCurves.EllipticCurve.ModelRecord
import ModularCurves.EllipticCurve.PointsDictionary
import ModularCurves.EllipticCurve.FinrankFractionField
import HasseWeil.Foundation.Basic

/-!
# The degree of `[N]` on the projective model: `finrank = N²` (K4 field-level crux)

This file builds the **field-level crux** of the endomorphism-degree keystone (STREAM-KM):
over a field `K`, the scheme-theoretic fibre rank `Scheme.Hom.finrank` of multiplication-by-`N`
on the projective Weierstrass model `projModel W` is `N²`.

It is the anchor that connects the *scheme* world (`Scheme.Hom.finrank`, `modelEllipticCurve`,
`mulByHom`) to AINTLIB's *HasseWeil* function-field world (`WeierstrassCurve.Affine.Isogeny.degree`,
`mulByInt_degree = N²`). The bridge factors as:

* `Scheme.Hom.finrank` of the model `[N]` at the generic point = the degree of the induced
  function-field extension `[K(projModel W) : K(projModel W)]` via `[N]*`
  (`FinrankFractionField.finrank_SpecMap_algebraMap_eq_finrank`, the algebraic core, over the
  domain coordinate ring);
* the model `[N]` and HasseWeil's `mulByInt W N` agree on points via the *green* dictionary
  `PointsDictionary.projModelPointsEquiv` (+ `modelEllipticCurve_point_add_val`), hence induce
  the same function-field pullback (points determine morphisms on reduced/separated schemes,
  `hom_ext_of_forall_specPoint`);
* `mulByInt_degree` (HasseWeil) gives that degree `= N²`.

For an arbitrary elliptic curve `E/S`, `Torsion.mulByHom_finrank` reduces to this field-level
statement fibre-by-fibre (the fibre `E_s` over `κ(s)` is `≅ projModel W_s` by
`E.localModel : LocallyWeierstrass`, `S = Spec κ(s)` being a one-point base).
-/

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace ModularCurves

namespace EllipticCurve

/-- **(dictionary additivity)** The points dictionary `projModelPointsEquiv` carries the model's
group addition (`modelEllipticCurve_point_add_val` via `mulModelHom`) to mathlib's `Affine.Point`
addition. This is `mulModelHom_specPoints` re-read through `modelEllipticCurve_point_add_val`, so
`projModelPointsEquiv` is an additive bijection of point groups. -/
theorem projModelPointsEquiv_add {K : Type u} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    {K' : Type u} [Field K'] [Algebra K K'] [DecidableEq K']
    (P Q : (modelEllipticCurve W).Point
      (Spec.map (CommRingCat.ofHom (algebraMap K K')))) :
    projModelPointsEquiv W K' (P + Q)
      = projModelPointsEquiv W K' P + projModelPointsEquiv W K' Q := by
  rw [← mulModelHom_specPoints W K' P Q]
  congr 1

/-- **(dictionary as an additive equivalence)** The points dictionary bundled with its additivity
(`projModelPointsEquiv_add`): the model's `K'`-point group is `≃+` to mathlib's `Affine.Point`. -/
noncomputable def projModelPointsAddEquiv {K : Type u} [Field K] (W : WeierstrassCurve K)
    [W.IsElliptic] (K' : Type u) [Field K'] [Algebra K K'] [DecidableEq K'] :
    (modelEllipticCurve W).Point (Spec.map (CommRingCat.ofHom (algebraMap K K')))
      ≃+ (W.baseChange K').toAffine.Point :=
  { projModelPointsEquiv W K' with map_add' := projModelPointsEquiv_add W }

/-- **(K4 point-`[N]`-match)** Under the points dictionary, the model's `zsmul` (multiplication
by `n` in the point group) is mathlib's `zsmul` on `Affine.Point`. Specialised to `n = N` this is
the point-level statement that the scheme `mulByHom N` realises mathlib's `[N]` (via
`point_smul_eq_comp_mulBy`, which rewrites `(n • P).1 = P.1 ≫ mulByHom n`). -/
theorem projModelPointsEquiv_zsmul {K : Type u} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    {K' : Type u} [Field K'] [Algebra K K'] [DecidableEq K'] (n : ℤ)
    (P : (modelEllipticCurve W).Point (Spec.map (CommRingCat.ofHom (algebraMap K K')))) :
    projModelPointsEquiv W K' (n • P) = n • projModelPointsEquiv W K' P :=
  map_zsmul (projModelPointsAddEquiv W K') n P

/-- **(K4 (B): function-field identity)** The scheme function field of the integral projective
model `projModel W` (mathlib `Scheme.functionField`) is `W.toAffine.FunctionField`: both are
fraction fields of the isomorphic coordinate rings `Γ(projModel W, Z-chart) ≃+* W.CoordinateRing`
(`coordRingToZSection`), via `functionField_isFractionRing_of_isAffineOpen`. -/
noncomputable def projModelFunctionFieldEquiv {K : Type u} [Field K] (W : WeierstrassCurve K)
    [W.IsElliptic] :
    (projModel W).functionField ≃+* W.toAffine.FunctionField := by
  set Z : (projModel W).Opens := Proj.basicOpen (quotientGrading (projIdeal W))
    ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) with hZ
  haveI hZaff : IsAffineOpen Z :=
    Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2) one_pos
  haveI hNe : Nonempty Z := by sorry
  haveI : IsFractionRing Γ(projModel W, Z) (projModel W).functionField :=
    functionField_isFractionRing_of_isAffineOpen (projModel W) Z hZaff
  exact (IsLocalization.ringEquivOfRingEquiv (M := (nonZeroDivisors Γ(projModel W, Z)))
    (T := (nonZeroDivisors W.toAffine.CoordinateRing))
    (projModel W).functionField W.toAffine.FunctionField
    (coordRingToZSection W).symm (by sorry))

/-- **(K4 field-level target)** Over a field `K`, the scheme-theoretic fibre rank of
multiplication-by-`N` on the projective model of an elliptic Weierstrass curve is `N²`.

The finiteness/flatness of `[N]` (the accepted KM 2.3.1 `BB-QF`/`BB-FLAT` fibre inputs) are taken
as hypotheses — this lemma supplies the *degree* content on top of them (the charter's scope (i)),
anchored in HasseWeil `mulByInt_degree`. The arbitrary-`E/S` assembly (`Torsion.mulByHom_finrank`)
discharges them from `mulByHom_flat`/`mulByHom_isFinite`. -/
theorem modelEllipticCurve_mulByHom_finrank {K : Type u} [Field K] (W : WeierstrassCurve K)
    [W.IsElliptic] (N : ℕ) [NeZero N]
    [Flat ((modelEllipticCurve W).mulByHom N)] [IsFinite ((modelEllipticCurve W).mulByHom N)]
    (x : (modelEllipticCurve W).E) :
    ((modelEllipticCurve W).mulByHom N).finrank x = N ^ 2 := by
  sorry

end EllipticCurve

end ModularCurves

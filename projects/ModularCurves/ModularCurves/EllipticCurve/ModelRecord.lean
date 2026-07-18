/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.GroupLawAxioms
import ModularCurves.EllipticCurve.Rigidity
import ModularCurves.EllipticCurve.Comparison

/-!
# [T-B6′ step (b)] — the model working record, and point-addition rigidity

**The mulOver-based `EllipticCurve (Spec R)` record on the projective model** — the "trivial
packaging" half of the v10.123-CASCADE gate verdict, unlocked by T-G4 (v10.138-CLOSER: all five
Over-level group laws at every commutative ring):

* `modelEllipticCurve W` — the working record on `projModel W`: geometry the projective model
  (`Fibre.geom`-pattern), group structure `mulOver`/`oneOver`/`invOver` with the T-G4 laws,
  commutativity `mulOver_comm`, unit normalisation `oneOver_left`.
* `modelEllipticCurve_point_add_val` — addition of `Spec`-points of the model record **computes
  as `mulModelHom`**: `(P + Q).1 = pullback.lift P.1 Q.1 _ ≫ mulModelHom W`.

**The rigidity driver** (GIT Cor 6.6 consequence, point level): over a locally noetherian base
two records with the same geometry have the same point-addition —
`point_add_val_of_geom_eq`. Route: `Point.baseChangeEquiv` (additive) moves both additions to
the base-changed records, whose geometries agree definitionally
(`baseChange_toGeom_congr`), and `abelEnrichment_unique_of_isLocallyNoetherian` (PROVEN,
Rigidity.lean) forces the base-changed records equal. This is the bridge that fills
`geomFibrePointAddEquiv.map_add'` ([T-B6′]): an abstract record with model geometry and
pinned zero adds like `mulModelHom` on field points.

Lean-ops note (registry-grade, discovered here): a structure-LITERAL record
`(⟨geom, grp, comm, hone⟩ : EllipticCurve S).Point g` defeats synthesis of
`pointAddCommGroup` (projection-on-literal reduction destroys the instance key), so every
statement about point addition below keeps its records as *variables*; the record
destructurings live in instance-free helper lemmas, and cross-record morphism equalities are
spelled with `eqToHom` (homogeneous) rather than `HEq`.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

variable {R : Type u} [CommRing R]

/-- **(T-B6′ packaging, the group object)** The `GrpObj` structure on the projective model
of an elliptic Weierstrass curve over any commutative ring: multiplication `mulOver`, unit
`oneOver`, inverse `invOver`; the axioms are the T-G4 transports (`mulOver_assoc`,
`oneOver_mulOver`, `mulOver_oneOver`, `invOver_mulOver`), the right inverse law derived from
the left one by commutativity and the braiding. -/
@[reducible] noncomputable def modelGrpObj (W : WeierstrassCurve R) [W.IsElliptic] :
    GrpObj (modelOver W) where
  one := oneOver W
  mul := mulOver W
  one_mul := oneOver_mulOver W
  mul_one := mulOver_oneOver W
  mul_assoc := mulOver_assoc W
  inv := invOver W
  left_inv := invOver_mulOver W
  right_inv := by
    rw [← mulOver_comm W, ← Category.assoc, lift_braiding_hom]
    exact invOver_mulOver W

/-- **(T-B6′ packaging, the working record)** The projective model of an elliptic
Weierstrass curve as a working record `EllipticCurve (Spec R)`: geometry as in
`MarkedChartData.Fibre.geom`, group structure `modelGrpObj` (the T-G4 laws at every ring),
commutativity `mulOver_comm`, unit normalisation `oneOver_left`. -/
noncomputable def modelEllipticCurve (W : WeierstrassCurve R) [W.IsElliptic] :
    EllipticCurve (Spec (CommRingCat.of R)) where
  E := projModel W
  π := projModelπ W
  zero := projModelZero W
  zero_π := projModelZero_projModelπ W
  smooth := projModel_smooth W
  proper := projModelπ_isProper W
  localModel := locallyWeierstrass_projModel W
  grp := modelGrpObj W
  comm := letI := modelGrpObj W; ⟨mulOver_comm W⟩
  one_eq_zero := by exact oneOver_left W

@[simp] theorem modelEllipticCurve_E (W : WeierstrassCurve R) [W.IsElliptic] :
    (modelEllipticCurve W).E = projModel W := rfl

@[simp] theorem modelEllipticCurve_π (W : WeierstrassCurve R) [W.IsElliptic] :
    (modelEllipticCurve W).π = projModelπ W := rfl

@[simp] theorem modelEllipticCurve_zero (W : WeierstrassCurve R) [W.IsElliptic] :
    (modelEllipticCurve W).zero = projModelZero W := rfl

namespace EllipticCurve

/-- Point-addition transport along an equality of records and of base morphisms. Both
records stay *variables* (see the file-head Lean-ops note); the cross-record comparison of
underlying morphisms is `eqToHom`-spelled. -/
theorem point_add_val_congr {S T : Scheme.{u}} {A B : EllipticCurve S} (hAB : A = B)
    {g g' : T ⟶ S} (hg : g = g') (x y : A.Point g) (x' y' : B.Point g')
    (hE : A.E = B.E)
    (hx : x.1 ≫ eqToHom hE = x'.1) (hy : y.1 ≫ eqToHom hE = y'.1) :
    (x + y).1 ≫ eqToHom hE = (x' + y').1 := by
  subst hAB; subst hg
  obtain rfl : x = x' := Subtype.ext (by simpa using hx)
  obtain rfl : y = y' := Subtype.ext (by simpa using hy)
  simp

/-- Point-addition transport along an equality of base morphisms (one record). -/
theorem point_add_val_congr_base {S T : Scheme.{u}} (A : EllipticCurve S)
    {g g' : T ⟶ S} (hg : g = g') (x : A.Point g) (x' : A.Point g') (y : A.Point g)
    (y' : A.Point g') (hx : x.1 = x'.1) (hy : y.1 = y'.1) :
    (x + y).1 = (x' + y').1 := by
  subst hg
  obtain rfl : x = x' := Subtype.ext hx
  obtain rfl : y = y' := Subtype.ext hy
  rfl

/-- The underlying morphism of `(Point.baseChangeEquiv E σ t).symm y` is the pullback lift. -/
theorem Point.baseChangeEquiv_symm_apply_coe {S : Scheme.{u}} (E : EllipticCurve S)
    {T T' : Scheme.{u}} (σ : T ⟶ S) (t : T' ⟶ T) (y : E.Point (t ≫ σ)) :
    ((Point.baseChangeEquiv E σ t).symm y).1 = pullback.lift y.1 t y.2 := rfl

/-- Extensionality for the geometric record from `eqToHom`-spelled field equalities: the
`Prop` fields are proof-irrelevant, so total space, structure morphism, and zero section
determine the record. Instance-free. -/
theorem _root_.ModularCurves.EllipticCurveGeom.ext_of_eqToHom {S : Scheme.{u}}
    {G G' : EllipticCurveGeom S} (hE : G.E = G'.E) (hπ : G.π = eqToHom hE ≫ G'.π)
    (hz : G.zero ≫ eqToHom hE = G'.zero) : G = G' := by
  obtain ⟨EE, π, z, hzπ, hsm, hpr, hlm⟩ := G
  obtain ⟨EE', π', z', hzπ', hsm', hpr', hlm'⟩ := G'
  obtain rfl : EE = EE' := hE
  obtain rfl : π = π' := by simpa using hπ
  obtain rfl : z = z' := by simpa using hz
  rfl

/-- Records with equal geometry have base changes with equal geometry (the `grp` data does
not enter the base-changed geometry). Instance-free, so the records may be destructured. -/
theorem baseChange_toGeom_congr {S : Scheme.{u}} {E E' : EllipticCurve S}
    (h : E.toEllipticCurveGeom = E'.toEllipticCurveGeom) {T : Scheme.{u}} (g : T ⟶ S) :
    (E.baseChange g).toEllipticCurveGeom = (E'.baseChange g).toEllipticCurveGeom := by
  obtain ⟨geomE, grp, comm, hone⟩ := E
  obtain ⟨geomE', grp', comm', hone'⟩ := E'
  obtain rfl : geomE = geomE' := h
  rfl

/-- The structure morphisms of records with equal geometry agree across the `eqToHom` of
their total spaces. Instance-free. -/
theorem eqToHom_π_congr {S : Scheme.{u}} {E E' : EllipticCurve S}
    (h : E.toEllipticCurveGeom = E'.toEllipticCurveGeom) (hEE : E.E = E'.E) :
    eqToHom hEE ≫ E'.π = E.π := by
  obtain ⟨geomE, grp, comm, hone⟩ := E
  obtain ⟨geomE', grp', comm', hone'⟩ := E'
  obtain rfl : geomE = geomE' := h
  simp

/-- `pullback.fst` commutes with the `eqToHom`s of a geometry equality. Instance-free. -/
theorem pullback_fst_eqToHom_congr {S : Scheme.{u}} {E E' : EllipticCurve S}
    (h : E.toEllipticCurveGeom = E'.toEllipticCurveGeom) {T : Scheme.{u}} (g : T ⟶ S)
    (hbcE : pullback E.π g = pullback E'.π g) (hEE : E.E = E'.E) :
    pullback.fst E.π g ≫ eqToHom hEE = eqToHom hbcE ≫ pullback.fst E'.π g := by
  obtain ⟨geomE, grp, comm, hone⟩ := E
  obtain ⟨geomE', grp', comm', hone'⟩ := E'
  obtain rfl : geomE = geomE' := h
  simp

/-- `pullback.lift` into the base change commutes with the `eqToHom`s of a geometry
equality. Instance-free. -/
theorem pullback_lift_eqToHom_congr {S : Scheme.{u}} {E E' : EllipticCurve S}
    (h : E.toEllipticCurveGeom = E'.toEllipticCurveGeom) {T T' : Scheme.{u}} (g : T ⟶ S)
    (hbcE : pullback E.π g = pullback E'.π g) (hEE : E.E = E'.E)
    (t : T' ⟶ T) (a : T' ⟶ E.E) (w : a ≫ E.π = t ≫ g) (w' : (a ≫ eqToHom hEE) ≫ E'.π = t ≫ g) :
    pullback.lift a t w ≫ eqToHom hbcE = pullback.lift (a ≫ eqToHom hEE) t w' := by
  obtain ⟨geomE, grp, comm, hone⟩ := E
  obtain ⟨geomE', grp', comm', hone'⟩ := E'
  obtain rfl : geomE = geomE' := h
  simp

/-- Transport of a single point's base-changed section across a working-record geometry
equality: the pullback-lift of `P₁` into `E`'s base-changed record, moved along the record
equality `hbcE`, is the corresponding lift for `E'`, provided the two sections agree via
`eqToHom hEE`. The per-point core shared by the two summands of `point_add_val_of_geom_eq`. -/
private lemma baseChangeEquiv_symm_val_comp_eqToHom {S : Scheme.{u}} {E E' : EllipticCurve S}
    (h : E.toEllipticCurveGeom = E'.toEllipticCurveGeom) {T : Scheme.{u}} {g : T ⟶ S}
    (hbcE : pullback E.π g = pullback E'.π g) (hEE : E.E = E'.E)
    (P₁ : E.Point (𝟙 T ≫ g)) (P₁' : E'.Point (𝟙 T ≫ g))
    (hP : P₁.1 ≫ eqToHom hEE = P₁'.1) :
    ((Point.baseChangeEquiv E g (𝟙 T)).symm P₁).1 ≫ eqToHom hbcE =
      ((Point.baseChangeEquiv E' g (𝟙 T)).symm P₁').1 :=
  (pullback_lift_eqToHom_congr h g hbcE hEE (𝟙 T) P₁.1 P₁.2
      ((Category.assoc _ _ _).trans ((congrArg (P₁.1 ≫ ·)
        (eqToHom_π_congr h hEE)).trans P₁.2))).trans
    (pullback.hom_ext
      ((pullback.lift_fst _ _ _).trans (hP.trans (pullback.lift_fst _ _ _).symm))
      ((pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm))

/-- **(T-B6′, the rigidity driver — GIT Cor 6.6 at the point level)** Over a locally
noetherian base `T`, two working records on `S` with the same geometry add points over
`g : T ⟶ S` identically (`eqToHom`-spelled). Fibrewise route (v10.123-CASCADE audit):
`Point.baseChangeEquiv` (additive, proven) moves both additions to the base-changed records
over `T`; those have equal geometry (`baseChange_toGeom_congr`), so
`abelEnrichment_unique_of_isLocallyNoetherian` (PROVEN, Rigidity.lean) forces them equal;
transport back. No noetherian hypothesis on `S` anywhere. -/
theorem point_add_val_of_geom_eq {S : Scheme.{u}} {E E' : EllipticCurve S}
    (h : E.toEllipticCurveGeom = E'.toEllipticCurveGeom)
    {T : Scheme.{u}} [IsLocallyNoetherian T] {g : T ⟶ S}
    (P Q : E.Point g) (P' Q' : E'.Point g) (hEE : E.E = E'.E)
    (hP : P.1 ≫ eqToHom hEE = P'.1) (hQ : Q.1 ≫ eqToHom hEE = Q'.1) :
    (P + Q).1 ≫ eqToHom hEE = (P' + Q').1 := by
  -- the base-changed records coincide: rigidity over the locally noetherian `T`
  have hbc : E.baseChange g = E'.baseChange g :=
    abelEnrichment_unique_of_isLocallyNoetherian _ _ (baseChange_toGeom_congr h g)
  have hbcE : pullback E.π g = pullback E'.π g :=
    congrArg (fun G : EllipticCurveGeom T => G.E) (baseChange_toGeom_congr h g)
  -- repackage the points over the composite `𝟙 T ≫ g`
  have hgc : g = 𝟙 T ≫ g := (Category.id_comp g).symm
  let P₁ : E.Point (𝟙 T ≫ g) := ⟨P.1, P.2.trans hgc⟩
  let Q₁ : E.Point (𝟙 T ≫ g) := ⟨Q.1, Q.2.trans hgc⟩
  let P₁' : E'.Point (𝟙 T ≫ g) := ⟨P'.1, P'.2.trans hgc⟩
  let Q₁' : E'.Point (𝟙 T ≫ g) := ⟨Q'.1, Q'.2.trans hgc⟩
  -- their sections of the base-changed records
  have hsumE : (P₁ + Q₁).1 =
      ((Point.baseChangeEquiv E g (𝟙 T)).symm P₁ + (Point.baseChangeEquiv E g (𝟙 T)).symm Q₁).1 ≫
        pullback.fst E.π g :=
    (congrArg Subtype.val (show P₁ + Q₁ = Point.baseChangeEquiv E g (𝟙 T)
        ((Point.baseChangeEquiv E g (𝟙 T)).symm P₁ +
          (Point.baseChangeEquiv E g (𝟙 T)).symm Q₁) by
      rw [map_add, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply])).trans
      (Point.baseChangeEquiv_apply_coe E g (𝟙 T) _)
  have hsumE' : (P₁' + Q₁').1 =
      ((Point.baseChangeEquiv E' g (𝟙 T)).symm P₁' +
          (Point.baseChangeEquiv E' g (𝟙 T)).symm Q₁').1 ≫
        pullback.fst E'.π g :=
    (congrArg Subtype.val (show P₁' + Q₁' = Point.baseChangeEquiv E' g (𝟙 T)
        ((Point.baseChangeEquiv E' g (𝟙 T)).symm P₁' +
          (Point.baseChangeEquiv E' g (𝟙 T)).symm Q₁') by
      rw [map_add, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply])).trans
      (Point.baseChangeEquiv_apply_coe E' g (𝟙 T) _)
  -- the sections' underlying morphisms match across the geometry equality
  have hx := baseChangeEquiv_symm_val_comp_eqToHom h hbcE hEE P₁ P₁' hP
  have hy := baseChangeEquiv_symm_val_comp_eqToHom h hbcE hEE Q₁ Q₁' hQ
  -- the middle transport across the record equality, then reassemble
  have hmid : ((Point.baseChangeEquiv E g (𝟙 T)).symm P₁ +
        (Point.baseChangeEquiv E g (𝟙 T)).symm Q₁).1 ≫ eqToHom hbcE =
      ((Point.baseChangeEquiv E' g (𝟙 T)).symm P₁' +
        (Point.baseChangeEquiv E' g (𝟙 T)).symm Q₁').1 :=
    point_add_val_congr hbc rfl _ _ _ _ hbcE hx hy
  calc (P + Q).1 ≫ eqToHom hEE
      = (P₁ + Q₁).1 ≫ eqToHom hEE :=
        congrArg (· ≫ eqToHom hEE) (point_add_val_congr_base E hgc P P₁ Q Q₁ rfl rfl)
    _ = (((Point.baseChangeEquiv E g (𝟙 T)).symm P₁ +
          (Point.baseChangeEquiv E g (𝟙 T)).symm Q₁).1 ≫ pullback.fst E.π g) ≫
            eqToHom hEE := congrArg (· ≫ eqToHom hEE) hsumE
    _ = ((Point.baseChangeEquiv E g (𝟙 T)).symm P₁ +
          (Point.baseChangeEquiv E g (𝟙 T)).symm Q₁).1 ≫
            (pullback.fst E.π g ≫ eqToHom hEE) := Category.assoc _ _ _
    _ = ((Point.baseChangeEquiv E g (𝟙 T)).symm P₁ +
          (Point.baseChangeEquiv E g (𝟙 T)).symm Q₁).1 ≫
            (eqToHom hbcE ≫ pullback.fst E'.π g) :=
        congrArg (_ ≫ ·) (pullback_fst_eqToHom_congr h g hbcE hEE)
    _ = (((Point.baseChangeEquiv E g (𝟙 T)).symm P₁ +
          (Point.baseChangeEquiv E g (𝟙 T)).symm Q₁).1 ≫ eqToHom hbcE) ≫
            pullback.fst E'.π g := (Category.assoc _ _ _).symm
    _ = ((Point.baseChangeEquiv E' g (𝟙 T)).symm P₁' +
          (Point.baseChangeEquiv E' g (𝟙 T)).symm Q₁').1 ≫ pullback.fst E'.π g :=
        congrArg (· ≫ pullback.fst E'.π g) hmid
    _ = (P₁' + Q₁').1 := hsumE'.symm
    _ = (P' + Q').1 := point_add_val_congr_base E' hgc.symm P₁' P' Q₁' Q' rfl rfl

end EllipticCurve

/-- **(T-B6′ packaging, the addition spec)** Point-addition of the model record computes as
the model multiplication morphism: for points `P Q` of `modelEllipticCurve W` over any
`g : T ⟶ Spec R`, `(P + Q).1 = pullback.lift P.1 Q.1 _ ≫ mulModelHom W`. This is the
`Hom.commGroup` multiplication unfolded through `pointEquivOverHom_add`, with
`μ[(modelEllipticCurve W).asOver] = mulOver W` by construction. -/
theorem modelEllipticCurve_point_add_val (W : WeierstrassCurve R) [W.IsElliptic]
    {T : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of R)}
    (P Q : (modelEllipticCurve W).Point g) :
    (P + Q).1 = pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ mulModelHom W := by
  have hx : (P + Q).1 =
      (lift ((modelEllipticCurve W).pointEquivOverHom g P)
          ((modelEllipticCurve W).pointEquivOverHom g Q)).left ≫
        (μ[(modelEllipticCurve W).asOver]).left :=
    (congrArg CommaMorphism.left
      ((modelEllipticCurve W).pointEquivOverHom_add g P Q)).trans
      (Over.comp_left _ _ _ _ _)
  have hfst : (lift ((modelEllipticCurve W).pointEquivOverHom g P)
        ((modelEllipticCurve W).pointEquivOverHom g Q)).left ≫
        pullback.fst (projModelπ W) (projModelπ W) = P.1 :=
    (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left (lift_fst _ _))
  have hsnd : (lift ((modelEllipticCurve W).pointEquivOverHom g P)
        ((modelEllipticCurve W).pointEquivOverHom g Q)).left ≫
        pullback.snd (projModelπ W) (projModelπ W) = Q.1 :=
    (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left (lift_snd _ _))
  have hlift : (lift ((modelEllipticCurve W).pointEquivOverHom g P)
        ((modelEllipticCurve W).pointEquivOverHom g Q)).left =
      pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) :=
    pullback.hom_ext (hfst.trans (pullback.lift_fst _ _ _).symm)
      (hsnd.trans (pullback.lift_snd _ _ _).symm)
  exact hx.trans (congrArg (· ≫ (μ[(modelEllipticCurve W).asOver]).left) hlift)

end ModularCurves

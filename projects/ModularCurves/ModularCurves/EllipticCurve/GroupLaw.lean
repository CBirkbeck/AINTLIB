/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import ModularCurves.ForMathlib.FunctorMapZpow
import ModularCurves.ForMathlib.OverPullbackMul
import Mathlib.AlgebraicGeometry.Group.Smooth

/-!
# The working record: elliptic curves with their group structure

Per the expert-review integration (2026-07-05, Q1/Q3): the group law is **part of the
working record**, not a registered sorried construction and not a prerequisite chain.
`EllipticCurve S` extends the geometric record `EllipticCurveGeom S` by

* a group-object structure on `E` in `Over S` (mathlib `GrpObj`, cartesian monoidal
  structure via pullbacks),
* commutativity, and
* the normalisation that the unit is the zero section.

This is exactly the object KM Ch. 1 consumes: "a smooth commutative S-group-scheme of
relative dimension one" (KM 1.4.1). Mathematically the extra data is redundant:

**The deferred canonicity ("purity/comparison") project** — `abelEnrichment_exists` /
`abelEnrichment_unique` below — proves every `EllipticCurveGeom` admits a unique such
enrichment, via Abel's theorem `E(T) ≅ Pic⁰(E_T/T)` (KM 2.1.2). Its named black boxes,
fixed once and not allowed to grow (reviewer's list, Q3):
`coherent-base-change` (`π_*O_E ≅ O_S` compatibly with base change);
`relative-duality-genus-one` (`R¹π_*O_E` a line bundle, base-change compatible);
`relative-Picard` (representability of `Pic_{E/S}`, `Pic⁰_{E/S}`, rigidified variants);
`Poincare` (Poincaré bundle); `Abel-isomorphism` (`E ≅ Pic⁰_{E/S}` carrying zero to
`O_E`, base-change compatible); `group-law-from-Abel` (induced structure; uniqueness).
⧗KM-gate: KM 2.1–2.3 are on the do-not-formalize-from-memory list.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

variable {S : Scheme.{u}}

/-- The **working record**: an elliptic curve over `S` together with its commutative
group-scheme structure, normalised so the unit is the zero section.
Source: KM 1.4.1 ("smooth commutative S-group-scheme of relative dimension one");
design per expert review (2026-07-05). The data is canonically unique —
`abelEnrichment_unique`. -/
structure EllipticCurve (S : Scheme.{u}) extends EllipticCurveGeom S where
  /-- The group-object structure on `E` in `Over S`. -/
  grp : GrpObj (Over.mk π)
  /-- The group law is commutative. -/
  comm : letI := grp; IsCommMonObj (Over.mk π)
  /-- The unit of the group structure is the zero section. -/
  one_eq_zero :
    letI := grp
    (η[Over.mk π] : _ ⟶ Over.mk π).left = (𝟙_ (Over S)).hom ≫ zero

namespace EllipticCurve

variable (E : EllipticCurve S)

/-- `E/S` as an object of `Over S`. -/
noncomputable abbrev asOver : Over S := Over.mk E.π

noncomputable instance grpObj : GrpObj E.asOver := E.grp

instance isCommMonObj : IsCommMonObj E.asOver := E.comm

/-- **(T-A6b, canonicity — Abel/KM 2.1.2; deferred purity project)** Every geometric
elliptic curve admits an enrichment to the working record. -/
theorem abelEnrichment_exists (G : EllipticCurveGeom S) :
    ∃ E : EllipticCurve S, E.toEllipticCurveGeom = G := by sorry

/-- **(T-A6c, uniqueness — KM 2.1.2 + rigidity; deferred purity project)** The
enrichment is unique: two working records with the same geometry are equal. -/
theorem abelEnrichment_unique (E E' : EllipticCurve S)
    (h : E.toEllipticCurveGeom = E'.toEllipticCurveGeom) : E = E' := by sorry

/-- Multiplication by `n` on `E/S`, as an endomorphism over `S`: the `n`-th power of
the identity in the group `Hom_{Over S}(E, E)` induced by the group structure.
Source: KM 2.3 ("the structure of `[N]`" — ⧗KM for its theorems). -/
noncomputable def mulBy (n : ℤ) : E.asOver ⟶ E.asOver :=
  letI : Group (E.asOver ⟶ E.asOver) := Hom.group
  (𝟙 E.asOver) ^ n

/-- The underlying scheme morphism of `mulBy`. -/
noncomputable abbrev mulByHom (n : ℤ) : E.E ⟶ E.E := (E.mulBy n).left

/-- `mulByHom n` is a morphism over `S`: it commutes with the structure map `π`. -/
@[simp]
theorem mulByHom_π (n : ℤ) : E.mulByHom n ≫ E.π = E.π :=
  Over.w (E.mulBy n)

/-- The `T`-points of `E/S` along `g : T ⟶ S`: morphisms `T ⟶ E` lifting `g`.
Source: Loeffler §3.3. -/
abbrev Point {T : Scheme.{u}} (g : T ⟶ S) : Type u :=
  { h : T ⟶ E.E // h ≫ E.π = g }

/-- The zero `T`-point. -/
def zeroPoint {T : Scheme.{u}} (g : T ⟶ S) : E.Point g :=
  ⟨g ≫ E.zero, by rw [Category.assoc, E.zero_π, Category.comp_id]⟩

/-- Points of `E` over `g` are the `Over S`-morphisms `Over.mk g ⟶ E.asOver`. -/
noncomputable def pointEquivOverHom {T : Scheme.{u}} (g : T ⟶ S) :
    E.Point g ≃ (Over.mk g ⟶ E.asOver) where
  toFun P := Over.homMk P.1 P.2
  invFun f := ⟨f.left, Over.w f⟩
  left_inv P := rfl
  right_inv f := by ext; rfl

/-- The additive commutative group structure on `T`-points, transported from the
hom-group into the group object `E` (mathlib `Hom.commGroup`), commutativity from the
`comm` field. Specification tying it to `mulBy`: `point_smul_eq_comp_mulBy`. -/
noncomputable instance pointAddCommGroup {T : Scheme.{u}} (g : T ⟶ S) :
    AddCommGroup (E.Point g) :=
  letI : CommGroup (Over.mk g ⟶ E.asOver) := Hom.commGroup
  ((E.pointEquivOverHom g).trans Additive.ofMul).addCommGroup

/-- `pointEquivOverHom` carries point-addition to multiplication of `Over`-homs (the
transport that defines `pointAddCommGroup`). -/
theorem pointEquivOverHom_add {T : Scheme.{u}} (g : T ⟶ S) (P Q : E.Point g) :
    letI : CommGroup (Over.mk g ⟶ E.asOver) := Hom.commGroup
    (E.pointEquivOverHom g) (P + Q) =
      (E.pointEquivOverHom g) P * (E.pointEquivOverHom g) Q := rfl

/-- **(T-A6d, specification)** Scalar multiplication on points is composition with
`mulBy`: `(n • P) = P ≫ [n]`. Provable from `pointEquivOverHom` +
`GrpObj.comp_zpow`; keeps the point-level and morphism-level `[n]` from diverging. -/
theorem point_smul_eq_comp_mulBy {T : Scheme.{u}} (g : T ⟶ S) (n : ℤ) (P : E.Point g) :
    ((n • P : E.Point g) : T ⟶ E.E) = (P : T ⟶ E.E) ≫ E.mulByHom n := by
  letI : CommGroup (Over.mk g ⟶ E.asOver) := Hom.commGroup
  have h1 : ((E.pointEquivOverHom g) (n • P)) = ((E.pointEquivOverHom g) P) ^ n := rfl
  have h2 : ((E.pointEquivOverHom g) P) ^ n =
      (E.pointEquivOverHom g) P ≫ (𝟙 E.asOver) ^ n := by
    rw [GrpObj.comp_zpow, Category.comp_id]
  have h3 := congrArg CommaMorphism.left (h1.trans h2)
  simp only [Over.comp_left] at h3
  exact h3

/-- Restriction of a point along `k : T' ⟶ T` (functoriality of the points functor). -/
def Point.restrict {T T' : Scheme.{u}} {g : T ⟶ S} (k : T' ⟶ T) (P : E.Point g) :
    E.Point (k ≫ g) :=
  ⟨k ≫ P.1, by rw [Category.assoc, P.2]⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- **(T-A5)** Base change of the working record along `g : T ⟶ S`: total space
`E ×_S T`; the group structure is mathlib's group-object structure on the pullback
(`Over.grpObjMkPullbackSnd`). Geometry Props are base-change stability (mathlib
instances + fibre transitivity); ticket `T-A5`. -/
noncomputable def baseChange {T : Scheme.{u}} (g : T ⟶ S) : EllipticCurve T where
  E := pullback E.π g
  π := pullback.snd E.π g
  zero := pullback.lift (g ≫ E.zero) (𝟙 T)
    (by rw [Category.assoc, E.zero_π, Category.comp_id, Category.id_comp])
  zero_π := pullback.lift_snd _ _ _
  smooth := by
    have : MorphismProperty.IsStableUnderBaseChange
        (@SmoothOfRelativeDimension 1) :=
      AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange 1
    exact MorphismProperty.pullback_snd _ _ E.smooth
  proper := MorphismProperty.pullback_snd _ _ E.proper
  localModel := E.localModel.baseChange g
  grp := Over.grpObjMkPullbackSnd
  comm := by exact Over.isCommMonObj_mk_pullbackSnd
  one_eq_zero := by
    apply pullback.hom_ext
    all_goals dsimp [Over.grpObjMkPullbackSnd_one]
    all_goals simp only [Over.grpObjMkPullbackSnd_one, Over.pullback, Over.comp_left,
      Over.homMk_left, Category.id_comp, E.one_eq_zero]
    all_goals
      have hε2 : (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
          pullback.snd (𝟙 S) g = 𝟙 T := Over.w _
    · have hε1 : (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
          pullback.fst (𝟙 S) g = g := by
        have hc : pullback.fst (𝟙 S) g = pullback.snd (𝟙 S) g ≫ g := by
          simpa using pullback.condition (f := 𝟙 S) (g := g)
        calc (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫ pullback.fst (𝟙 S) g
            = (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
              pullback.snd (𝟙 S) g ≫ g := congrArg
                (fun q ↦ (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫ q) hc
          _ = ((Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
              pullback.snd (𝟙 S) g) ≫ g := (Category.assoc _ _ _).symm
          _ = 𝟙 T ≫ g := congrArg (· ≫ g) hε2
          _ = g := Category.id_comp g
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans (congrArg
        (fun q ↦ (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫ q)
        (pullback.lift_fst _ _ _)) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg (· ≫ E.zero) hε1) ?_
      exact (pullback.lift_fst _ _ _).symm
    · refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans (congrArg
        (fun q ↦ (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫ q)
        (pullback.lift_snd _ _ _)) ?_
      exact hε2.trans (pullback.lift_snd _ _ _).symm

/-- **(T-D6a-ii)** Multiplication by `n` commutes with base change: on the base-changed
curve `E ×_S T`, the endomorphism `[n]` is the image of `E`'s `[n]` under the monoidal
functor `Over.pullback g`. Both are the `n`-th power of the identity in the respective
hom-groups, and `Over.pullback g` preserves those powers.

Proof: `Functor.map_zpow'` (ForMathlib, the `zpow` companion of mathlib's
`Functor.map_inv'`) + `Functor.map_id`; the `open scoped CategoryTheory.Obj`
inside `map_zpow'` resolves the `GrpObj (F.obj G)` instance that otherwise diamonds
with `Hom.group`. -/
theorem mulBy_baseChange {T : Scheme.{u}} (g : T ⟶ S) (n : ℤ) :
    (E.baseChange g).mulBy n =
      (Over.pullback g).map (E.mulBy n) := by
  simp only [EllipticCurve.mulBy, Functor.map_zpow', CategoryTheory.Functor.map_id]
  rfl

/-- The underlying scheme morphism of `[n]` on the base-changed curve is the pullback
of `E`'s `[n]` (the `.left` of `mulBy_baseChange`, in explicit `pullback.lift` form). -/
theorem mulByHom_baseChange {T : Scheme.{u}} (g : T ⟶ S) (n : ℤ) :
    (E.baseChange g).mulByHom n =
      Limits.pullback.lift (Limits.pullback.fst E.π g ≫ E.mulByHom n)
        (Limits.pullback.snd E.π g) (by simp [Limits.pullback.condition]) := by
  have h := congrArg CommaMorphism.left (mulBy_baseChange E g n)
  exact h

@[reassoc (attr := simp)]
lemma mulByHom_baseChange_fst {T : Scheme.{u}} (g : T ⟶ S) (n : ℤ) :
    (E.baseChange g).mulByHom n ≫ pullback.fst E.π g =
      pullback.fst E.π g ≫ E.mulByHom n := by
  rw [mulByHom_baseChange]; exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma mulByHom_baseChange_snd {T : Scheme.{u}} (g : T ⟶ S) (n : ℤ) :
    (E.baseChange g).mulByHom n ≫ pullback.snd E.π g = pullback.snd E.π g := by
  rw [mulByHom_baseChange]; exact pullback.lift_snd _ _ _

/-- A point of `E` over `g : T ⟶ S`, viewed as a section of the base-changed curve
`E ×_S T / T`. -/
noncomputable def Point.asSection {T : Scheme.{u}} (g : T ⟶ S) (P : E.Point g) :
    (E.baseChange g).Point (𝟙 T) :=
  ⟨pullback.lift P.1 (𝟙 T) (by rw [P.2, Category.id_comp]),
    pullback.lift_snd _ _ _⟩

@[simp]
lemma Point.asSection_coe {T : Scheme.{u}} (g : T ⟶ S) (P : E.Point g) :
    (Point.asSection E g P).1 =
      pullback.lift P.1 (𝟙 T) (by rw [P.2, Category.id_comp]) := rfl

@[reassoc (attr := simp)]
lemma Point.asSection_val_fst {T : Scheme.{u}} (g : T ⟶ S) (P : E.Point g) :
    (Point.asSection E g P).1 ≫ pullback.fst E.π g = P.1 :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma Point.asSection_val_snd {T : Scheme.{u}} (g : T ⟶ S) (P : E.Point g) :
    (Point.asSection E g P).1 ≫ pullback.snd E.π g = 𝟙 T :=
  pullback.lift_snd _ _ _

/-- **(T-D6a-ii, final ingredient)** `asSection` intertwines integer scalar
multiplication. Both underlying maps are `pullback.lift (P.1 ≫ [n]) (𝟙 T)` — LHS by
`point_smul_eq_comp_mulBy` on `E`, RHS by the same plus `mulByHom_baseChange`.

PROVEN (2026-07-07, axiom-clean): the previously-diagnosed friction was a single wall —
`EllipticCurve.baseChange` is a semireducible `def`, so `(E.baseChange g).E` is defeq to
`pullback E.π g` only at *default* transparency; every `rw`/`simp` route dies because its
matcher (`kabstract`) re-checks the composition at `instances` transparency, where an
`(E.baseChange g).E`-typed coercion against `pullback.fst/snd E.π g` is not type-correct.
A **term-mode** proof (`Eq.trans`/`congrArg`/`Category.assoc` chains, elaborated at default
transparency) sidesteps `kabstract` entirely — no structural refactor needed. -/
theorem Point.asSection_zsmul {T : Scheme.{u}} (g : T ⟶ S) (n : ℤ) (P : E.Point g) :
    Point.asSection E g (n • P) = n • Point.asSection E g P := by
  -- Both underlying morphisms are `pullback.lift (↑P ≫ E.mulByHom n) (𝟙 T) _`.  The proof
  -- is deliberately term-mode: `(E.baseChange g).E` is only defeq to `pullback E.π g` at
  -- default transparency, so any `rw`/`simp` step whose matcher (`kabstract`) re-checks a
  -- composition of an `(E.baseChange g).E`-typed coercion against `pullback.fst E.π g`
  -- fails ("not type-correct under instances").  `Eq.trans`/`congrArg` chains elaborate at
  -- default transparency and sidestep this.  `pullback.hom_ext` splits into the two legs,
  -- each reduced by the base-change naturality bridges `mulByHom_baseChange_fst/snd` and
  -- the section identities `Point.asSection_val_fst/snd`; `point_smul_eq_comp_mulBy` ties
  -- the point-level `[n]` to `mulByHom` on both `E` and `E.baseChange g`.
  refine Subtype.ext (pullback.hom_ext ?_ ?_)
  · -- fst leg: both sides equal `↑P ≫ E.mulByHom n`
    have lhs : (Point.asSection E g (n • P)).1 ≫ pullback.fst E.π g = ↑P ≫ E.mulByHom n :=
      (Point.asSection_val_fst E g (n • P)).trans (point_smul_eq_comp_mulBy E g n P)
    have rhs : (n • Point.asSection E g P).1 ≫ pullback.fst E.π g = ↑P ≫ E.mulByHom n :=
      (congrArg (· ≫ pullback.fst E.π g)
          (point_smul_eq_comp_mulBy (E.baseChange g) (𝟙 T) n (Point.asSection E g P))).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg ((Point.asSection E g P).1 ≫ ·) (mulByHom_baseChange_fst E g n)).trans <|
            (Category.assoc _ _ _).symm.trans <|
              congrArg (· ≫ E.mulByHom n) (Point.asSection_val_fst E g P)
    exact lhs.trans rhs.symm
  · -- snd leg: both sides equal `𝟙 T`
    have lhs : (Point.asSection E g (n • P)).1 ≫ pullback.snd E.π g = 𝟙 T :=
      Point.asSection_val_snd E g (n • P)
    have rhs : (n • Point.asSection E g P).1 ≫ pullback.snd E.π g = 𝟙 T :=
      (congrArg (· ≫ pullback.snd E.π g)
          (point_smul_eq_comp_mulBy (E.baseChange g) (𝟙 T) n (Point.asSection E g P))).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg ((Point.asSection E g P).1 ≫ ·) (mulByHom_baseChange_snd E g n)).trans <|
            Point.asSection_val_snd E g P
    exact lhs.trans rhs.symm

/-- The forward map of the base-change point dictionary: compose with the projection. -/
private noncomputable def pointBaseChangeFun {T T' : Scheme.{u}} (σ : T ⟶ S) (t : T' ⟶ T)
    (x : (E.baseChange σ).Point t) : E.Point (t ≫ σ) :=
  ⟨x.1 ≫ pullback.fst E.π σ,
    (Category.assoc _ _ _).trans <|
      (congrArg (x.1 ≫ ·) pullback.condition).trans <|
      (Category.assoc _ _ _).symm.trans <|
      congrArg (· ≫ σ) x.2⟩

/-- The underlying morphism of a point sum, through `pointEquivOverHom_add` (the
`Hom.commGroup` multiplication made explicit as `lift … ≫ μ`). -/
private lemma point_add_coe {T : Scheme.{u}} (g : T ⟶ S) (P Q : E.Point g) :
    (P + Q : E.Point g).1 =
      (lift (E.pointEquivOverHom g P) (E.pointEquivOverHom g Q)).left ≫
        (μ[E.asOver]).left :=
  (congrArg CommaMorphism.left (E.pointEquivOverHom_add g P Q)).trans
    (Over.comp_left _ _ _ _ _)

/-- The comparison morphism of the pullback identifies the base-changed lifted pair
`(x, y)` over `T'` with the composite lifted pair over `t ≫ σ`; the intertwining core of
`pointBaseChangeFun_add`. -/
private lemma pointBaseChangeFun_lift_comparison {T T' : Scheme.{u}} (σ : T ⟶ S)
    (t : T' ⟶ T) (x y : (E.baseChange σ).Point t) :
    (lift ((E.baseChange σ).pointEquivOverHom t x)
        ((E.baseChange σ).pointEquivOverHom t y)).left
        ≫ pullback.lift
          (pullback.fst (pullback.snd E.π σ) (pullback.snd E.π σ) ≫ pullback.fst E.π σ)
          (pullback.snd (pullback.snd E.π σ) (pullback.snd E.π σ) ≫ pullback.fst E.π σ)
          ((Category.assoc _ _ _).trans <|
            (congrArg (pullback.fst (pullback.snd E.π σ) (pullback.snd E.π σ) ≫ ·)
              pullback.condition).trans <|
            (Category.assoc _ _ _).symm.trans <|
            (congrArg (· ≫ σ) pullback.condition).trans <|
            (Category.assoc _ _ _).trans <|
            (congrArg (pullback.snd (pullback.snd E.π σ) (pullback.snd E.π σ) ≫ ·)
              pullback.condition.symm).trans <|
            (Category.assoc _ _ _).symm)
      = (lift (E.pointEquivOverHom (t ≫ σ) (pointBaseChangeFun E σ t x))
          (E.pointEquivOverHom (t ≫ σ) (pointBaseChangeFun E σ t y))).left := by
  have hbx : (lift ((E.baseChange σ).pointEquivOverHom t x)
        ((E.baseChange σ).pointEquivOverHom t y)).left
        ≫ pullback.fst (pullback.snd E.π σ) (pullback.snd E.π σ) = x.1 :=
    (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left (lift_fst _ _))
  have hby : (lift ((E.baseChange σ).pointEquivOverHom t x)
        ((E.baseChange σ).pointEquivOverHom t y)).left
        ≫ pullback.snd (pullback.snd E.π σ) (pullback.snd E.π σ) = y.1 :=
    (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left (lift_snd _ _))
  have hSx : (lift (E.pointEquivOverHom (t ≫ σ) (pointBaseChangeFun E σ t x))
        (E.pointEquivOverHom (t ≫ σ) (pointBaseChangeFun E σ t y))).left
        ≫ pullback.fst E.π E.π = x.1 ≫ pullback.fst E.π σ :=
    (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left (lift_fst _ _))
  have hSy : (lift (E.pointEquivOverHom (t ≫ σ) (pointBaseChangeFun E σ t x))
        (E.pointEquivOverHom (t ≫ σ) (pointBaseChangeFun E σ t y))).left
        ≫ pullback.snd E.π E.π = y.1 ≫ pullback.fst E.π σ :=
    (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left (lift_snd _ _))
  exact Over.tensorObj_ext (S := E.asOver) (T := E.asOver) _ _
      ((Category.assoc _ _ _).trans <|
        (congrArg ((lift ((E.baseChange σ).pointEquivOverHom t x)
            ((E.baseChange σ).pointEquivOverHom t y)).left ≫ ·)
          (pullback.lift_fst _ _ _)).trans <|
        (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ pullback.fst E.π σ) hbx).trans <|
        hSx.symm)
      ((Category.assoc _ _ _).trans <|
        (congrArg ((lift ((E.baseChange σ).pointEquivOverHom t x)
            ((E.baseChange σ).pointEquivOverHom t y)).left ≫ ·)
          (pullback.lift_snd _ _ _)).trans <|
        (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ pullback.fst E.π σ) hby).trans <|
        hSy.symm)

private lemma pointBaseChangeFun_add {T T' : Scheme.{u}} (σ : T ⟶ S) (t : T' ⟶ T)
    (x y : (E.baseChange σ).Point t) :
    pointBaseChangeFun E σ t (x + y)
      = pointBaseChangeFun E σ t x + pointBaseChangeFun E σ t y := by
  refine Subtype.ext ?_
  have hx : (x + y).1
      = (lift ((E.baseChange σ).pointEquivOverHom t x)
          ((E.baseChange σ).pointEquivOverHom t y)).left
        ≫ (μ[(E.baseChange σ).asOver]).left :=
    point_add_coe (E.baseChange σ) t x y
  have hR : (pointBaseChangeFun E σ t x + pointBaseChangeFun E σ t y).1
      = (lift (E.pointEquivOverHom (t ≫ σ) (pointBaseChangeFun E σ t x))
          (E.pointEquivOverHom (t ≫ σ) (pointBaseChangeFun E σ t y))).left
        ≫ (μ[E.asOver]).left :=
    point_add_coe E (t ≫ σ) (pointBaseChangeFun E σ t x) (pointBaseChangeFun E σ t y)
  have hlift := pointBaseChangeFun_lift_comparison E σ t x y
  show (x + y).1 ≫ pullback.fst E.π σ = _
  rw [hR]
  exact (congrArg (· ≫ pullback.fst E.π σ) hx).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg ((lift ((E.baseChange σ).pointEquivOverHom t x)
        ((E.baseChange σ).pointEquivOverHom t y)).left ≫ ·)
      (Over.grpObjMkPullbackSnd_mul_left_fst E.π σ)).trans <|
    (Category.assoc _ _ _).symm.trans <|
    congrArg (· ≫ (μ[E.asOver]).left) hlift

/-- **(T-H2b)** The additive base-change point dictionary: `T'`-points of the base-changed
curve are `T'`-points of `E` over the composite, additively. The underlying bijection is
the universal property of the pullback; additivity of the forward map is
`Over.grpObjMkPullbackSnd_mul_left_fst` (the projection intertwines the pullback
multiplication). -/
noncomputable def Point.baseChangeEquiv {T T' : Scheme.{u}} (σ : T ⟶ S) (t : T' ⟶ T) :
    (E.baseChange σ).Point t ≃+ E.Point (t ≫ σ) where
  toFun := pointBaseChangeFun E σ t
  invFun y := ⟨pullback.lift y.1 t y.2, pullback.lift_snd _ _ _⟩
  left_inv x := Subtype.ext <| by
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans x.2.symm
  right_inv y := Subtype.ext (pullback.lift_fst _ _ _)
  map_add' := pointBaseChangeFun_add E σ t

@[simp]
lemma Point.baseChangeEquiv_apply_coe {T T' : Scheme.{u}} (σ : T ⟶ S) (t : T' ⟶ T)
    (x : (E.baseChange σ).Point t) :
    (Point.baseChangeEquiv E σ t x).1 = x.1 ≫ pullback.fst E.π σ := rfl

end EllipticCurve

end ModularCurves
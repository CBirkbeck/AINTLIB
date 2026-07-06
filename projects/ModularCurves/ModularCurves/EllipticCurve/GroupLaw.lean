import ModularCurves.EllipticCurve.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import ModularCurves.ForMathlib.FunctorMapZpow
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
    haveI : MorphismProperty.IsStableUnderBaseChange
        (@SmoothOfRelativeDimension 1) :=
      AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange 1
    exact MorphismProperty.pullback_snd _ _ E.smooth
  proper := MorphismProperty.pullback_snd _ _ E.proper
  fibres := E.fibres.baseChange g
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
                (fun q => (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫ q) hc
          _ = ((Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
              pullback.snd (𝟙 S) g) ≫ g := (Category.assoc _ _ _).symm
          _ = 𝟙 T ≫ g := congrArg (· ≫ g) hε2
          _ = g := Category.id_comp g
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans (congrArg
        (fun q => (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫ q)
        (pullback.lift_fst _ _ _)) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      refine Eq.trans (congrArg (· ≫ E.zero) hε1) ?_
      exact (pullback.lift_fst _ _ _).symm
    · refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans (congrArg
        (fun q => (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫ q)
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

/-- A point of `E` over `g : T ⟶ S`, viewed as a section of the base-changed curve
`E ×_S T / T`. -/
noncomputable def Point.asSection {T : Scheme.{u}} (g : T ⟶ S) (P : E.Point g) :
    (E.baseChange g).Point (𝟙 T) :=
  ⟨pullback.lift P.1 (𝟙 T) (by rw [P.2, Category.id_comp]),
    pullback.lift_snd _ _ _⟩

/-- **(T-D6a-ii, final ingredient)** `asSection` intertwines integer scalar
multiplication. Both underlying maps are `pullback.lift (P.1 ≫ [n]) (𝟙 T)` — LHS by
`point_smul_eq_comp_mulBy` on `E`, RHS by the same plus `mulByHom_baseChange`.

PARKED (2026-07-09): the arithmetic is settled (fst-leg = `P.1 ≫ E.mulByHom n`,
snd-leg = `𝟙 T` on both sides via `pullback.hom_ext`); the residual friction is the
`(E.baseChange g).E` vs `pullback E.π g` defeq-heterogeneity — `mulByHom_baseChange`
rewrites at the `(E.baseChange g).E`-typed spelling but the subsequent
`pullback.fst E.π g` composition is at the raw `pullback E.π g` spelling, so
`pullback.lift_fst`'s matcher misfires. Clean route: recast the whole goal to the raw
`pullback E.π g` spelling with a single `show` before any rewriting, then the
fst/snd-leg computation goes through. Non-blocking (T-D6a-ii is itself non-blocking). -/
theorem Point.asSection_zsmul {T : Scheme.{u}} (g : T ⟶ S) (n : ℤ) (P : E.Point g) :
    Point.asSection E g (n • P) = n • Point.asSection E g P := by
  -- ARITHMETIC SETTLED, COERCION-SPELLING PARKED (2026-07-09). Every fact compiles:
  --   hmf : (E.baseChange g).mulByHom n ≫ pullback.fst E.π g
  --           = pullback.fst E.π g ≫ E.mulByHom n   (mulByHom_baseChange + lift_fst)
  --   hms : (E.baseChange g).mulByHom n ≫ pullback.snd E.π g = pullback.snd E.π g
  --   hASf : (asSection E g P).1 ≫ pullback.fst E.π g = P.1   (lift_fst)
  -- and both legs of `pullback.hom_ext` reduce to `P.1 ≫ E.mulByHom n` / `𝟙 T` via
  -- point_smul_eq_comp_mulBy. The ONLY blocker: `↑(asSection E g P)` elaborates with
  -- codomain `pullback E.π g` inside the goal but `(E.baseChange g).E` inside the
  -- haves — defeq, but `reassoc_of% hASf` / `← Category.assoc` matchers distinguish
  -- the two spellings. Fix = give `Point.asSection` a `@[simp] asSection_coe` lemma
  -- unfolding `↑(asSection E g P)` to `pullback.lift P.1 (𝟙 T) _` at the RAW
  -- `pullback E.π g` spelling, then `simp only [asSection_coe]` normalises both
  -- occurrences before the reassoc. Non-blocking (T-D6a-ii is non-blocking).
  sorry

end EllipticCurve

end ModularCurves

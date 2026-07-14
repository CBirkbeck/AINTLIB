/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.LevelStructure.Basic
import ModularCurves.LevelStructure.ExactOrder
import ModularCurves.ForMathlib.IdealSheafComapMul

/-!
# The divisor apparatus under a pointed group isomorphism (the T-H8a iso-leg)

The Drinfeld level-structure predicates (`Section.HasExactOrder`, `IsFullLevel`) are built from
the divisor apparatus: `RelEffCartierDiv.sectionsDivisor`, `Section.orderDivisor`,
`RelEffCartierDiv.IsSubgroup`, `torsionIdeal`. Their functor laws ([T-H8a], the Drinfeld `map`
memberships) require transporting these along the pointed comparison isomorphism of an
`Ell/R`-morphism's cartesian square — the **iso-leg** of the two-leg transport (the base-change
leg, `HasExactOrder.baseChange` / `IsSubgroup.baseChange` / `baseChange_ideal` /
`torsion_baseChange_isPullback`, is already proven).

This file proves the iso-leg **hypothesis-funneled**, the `transportSection_add_of_isMonHom`
pattern (`Moduli/PullSectionCanonicity.lean`): every lemma takes the pointedness and
multiplication-compatibility of the isomorphism as *hypotheses*

* `hη : η[E.asOver] ≫ e.hom = η[E'.asOver]`
* `hμ : μ[E.asOver] ≫ e.hom = tensorHom e.hom e.hom ≫ μ[E'.asOver]`

so the file is **sorry-free**: nothing here gates on the canonicity primitive. At T-W7a the
falls-sweep supplies `hμ` from `isMonHom_of_one_comp_eq'_of_finitePresentation` (route (a)) or
the endgame canonicity (route (c)), and both Drinfeld memberships become mechanical.

## Main results

* `mulBy_comp_monHom` / `mulByHom_comp_monHom` / `zero_comp_monHom`: a pointed
  multiplication-compatible morphism intertwines `[n]` and the zero section.
* `pointAddEquiv`: the induced additive equivalence `E.Point g ≃+ E'.Point g` at every base
  point `g : T ⟶ S`.
* `sectionsDivisor_pointMap_ideal`: the sections-divisor of the transported family of points,
  as the `comap` of the original along the inverse.
* `torsionIdeal_eq_comap`: `torsionIdeal` transports along the isomorphism.
* `RelEffCartierDiv.IsSubgroup.of_ideal_comap`: the subgroup-divisor property transports.
* `Section.HasExactOrder.pointMap`: exact order transports (the `IsGammaOne` iso-leg).
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} {E E' : EllipticCurve S}

section PostcompHom

/-! The postcomposition algebra: postcomposing with a pointed multiplication-compatible
morphism is a group homomorphism of `Hom`-groups. (Precomposition is always one —
`MonObj.comp_mul`/`GrpObj.comp_zpow` in mathlib; the postcomposition half needs `hη`/`hμ`.) -/

variable (e : E.asOver ⟶ E'.asOver)

/-- Postcomposition with a pointed morphism preserves the `Hom`-group unit. -/
lemma one_comp_monHom (hη : η[E.asOver] ≫ e = η[E'.asOver]) (A : Over S) :
    (1 : A ⟶ E.asOver) ≫ e = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, hη]

/-- Postcomposition with a multiplication-compatible morphism preserves the `Hom`-group
multiplication. -/
lemma mul_comp_monHom
    (hμ : μ[E.asOver] ≫ e = MonoidalCategory.tensorHom e e ≫ μ[E'.asOver])
    {A : Over S} (f g : A ⟶ E.asOver) :
    (f * g) ≫ e = (f ≫ e) * (g ≫ e) := by
  rw [Hom.mul_def, Hom.mul_def, Category.assoc, hμ, ← Category.assoc, lift_map]

/-- Postcomposition with a multiplication-compatible morphism preserves `Hom`-group integer
powers. -/
lemma zpow_comp_monHom
    (hμ : μ[E.asOver] ≫ e = MonoidalCategory.tensorHom e e ≫ μ[E'.asOver])
    {A : Over S} (f : A ⟶ E.asOver) (n : ℤ) :
    (f ^ n) ≫ e = (f ≫ e) ^ n :=
  map_zpow (MonoidHom.mk' (fun z : A ⟶ E.asOver ↦ z ≫ e)
    (fun f g ↦ mul_comp_monHom e hμ f g)) f n

/-- **The `[n]`-intertwining**: a pointed multiplication-compatible morphism commutes with
multiplication-by-`n`. Both sides are `e ^ n` in the `Hom`-group `E.asOver ⟶ E'.asOver`:
the left by postcomposition (`zpow_comp_monHom`, needs `hμ`), the right by precomposition
(`GrpObj.comp_zpow`, free). -/
lemma mulBy_comp_monHom
    (hμ : μ[E.asOver] ≫ e = MonoidalCategory.tensorHom e e ≫ μ[E'.asOver]) (n : ℤ) :
    E.mulBy n ≫ e = e ≫ E'.mulBy n := by
  show ((𝟙 E.asOver) ^ n) ≫ e = e ≫ ((𝟙 E'.asOver) ^ n)
  rw [zpow_comp_monHom e hμ, GrpObj.comp_zpow, Category.id_comp, Category.comp_id]

/-- Scheme-level form of the `[n]`-intertwining. -/
lemma mulByHom_comp_monHom
    (hμ : μ[E.asOver] ≫ e = MonoidalCategory.tensorHom e e ≫ μ[E'.asOver]) (n : ℤ) :
    E.mulByHom n ≫ (e.left : E.E ⟶ E'.E) = (e.left : E.E ⟶ E'.E) ≫ E'.mulByHom n := by
  have h : (E.mulBy n ≫ e).left = (e ≫ E'.mulBy n).left :=
    congrArg CommaMorphism.left (mulBy_comp_monHom e hμ n)
  exact (Over.comp_left _ _ _ _ _).symm.trans (h.trans (Over.comp_left _ _ _ _ _))

/-- Scheme-level form of pointedness: the zero section is intertwined. -/
lemma zero_comp_monHom (hη : η[E.asOver] ≫ e = η[E'.asOver]) :
    E.zero ≫ (e.left : E.E ⟶ E'.E) = E'.zero := by
  have h0 : (η[E.asOver] : _ ⟶ E.asOver).left ≫ e.left = (η[E'.asOver] : _ ⟶ E'.asOver).left :=
    (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left hη)
  have h1 : ((𝟙_ (Over S)).hom ≫ E.zero) ≫ e.left = (𝟙_ (Over S)).hom ≫ E'.zero :=
    (congrArg (· ≫ e.left) E.one_eq_zero).symm.trans (h0.trans E'.one_eq_zero)
  rw [Category.assoc] at h1
  exact (cancel_epi (𝟙 S)).mp h1

end PostcompHom

section PointTransport

/-! The point-level transport: a pointed multiplication-compatible isomorphism induces an
additive equivalence on `T`-points at every base point `g : T ⟶ S`. -/

/-- The image of a point under a morphism of curves over `S`. -/
noncomputable def pointMapOfHom (e : E.asOver ⟶ E'.asOver) {T : Scheme.{u}} {g : T ⟶ S}
    (P : E.Point g) : E'.Point g :=
  ⟨P.1 ≫ e.left,
    (Category.assoc _ _ _).trans ((congrArg (P.1 ≫ ·) (Over.w e)).trans P.2)⟩

@[simp]
lemma pointMapOfHom_coe (e : E.asOver ⟶ E'.asOver) {T : Scheme.{u}} {g : T ⟶ S}
    (P : E.Point g) : (pointMapOfHom e P : T ⟶ E'.E) = P.1 ≫ e.left := rfl

/-- The scheme components of an `Over`-isomorphism compose to the identity. -/
lemma iso_hom_left_inv_left (e : E.asOver ≅ E'.asOver) :
    e.hom.left ≫ e.inv.left = 𝟙 E.E :=
  ((Over.comp_left _ _ _ _ _).symm.trans
    (congrArg CommaMorphism.left e.hom_inv_id)).trans (Over.id_left _)

/-- The scheme components of an `Over`-isomorphism compose to the identity (other order). -/
lemma iso_inv_left_hom_left (e : E.asOver ≅ E'.asOver) :
    e.inv.left ≫ e.hom.left = 𝟙 E'.E :=
  ((Over.comp_left _ _ _ _ _).symm.trans
    (congrArg CommaMorphism.left e.inv_hom_id)).trans (Over.id_left _)

/-- `pointMapOfHom` is additive when `e` is multiplication-compatible: the
`transportSection_add_of_isMonHom` pattern at an arbitrary base point. -/
lemma pointMapOfHom_add (e : E.asOver ⟶ E'.asOver)
    (hμ : μ[E.asOver] ≫ e = MonoidalCategory.tensorHom e e ≫ μ[E'.asOver])
    {T : Scheme.{u}} {g : T ⟶ S} (P Q : E.Point g) :
    pointMapOfHom e (P + Q) = pointMapOfHom e P + pointMapOfHom e Q := by
  letI : CommGroup (Over.mk g ⟶ E.asOver) := Hom.commGroup
  letI : CommGroup (Over.mk g ⟶ E'.asOver) := Hom.commGroup
  apply (E'.pointEquivOverHom g).injective
  have hcomm : ∀ R : E.Point g,
      (E'.pointEquivOverHom g) (pointMapOfHom e R) = (E.pointEquivOverHom g) R ≫ e :=
    fun R ↦ Over.OverMorphism.ext rfl
  rw [pointEquivOverHom_add, hcomm, hcomm, hcomm, pointEquivOverHom_add]
  exact mul_comp_monHom e hμ _ _

/-- **The point-level additive equivalence** induced by a pointed multiplication-compatible
isomorphism of elliptic curves over `S`, at every base point `g : T ⟶ S`. -/
@[simps -fullyApplied apply]
noncomputable def pointAddEquiv (e : E.asOver ≅ E'.asOver)
    (hμ : μ[E.asOver] ≫ e.hom = MonoidalCategory.tensorHom e.hom e.hom ≫ μ[E'.asOver])
    {T : Scheme.{u}} (g : T ⟶ S) :
    E.Point g ≃+ E'.Point g where
  toFun := pointMapOfHom e.hom
  invFun := pointMapOfHom e.inv
  left_inv P := Subtype.ext <|
    (Category.assoc _ _ _).trans
      ((congrArg (P.1 ≫ ·) (iso_hom_left_inv_left e)).trans (Category.comp_id _))
  right_inv P := Subtype.ext <|
    (Category.assoc _ _ _).trans
      ((congrArg (P.1 ≫ ·) (iso_inv_left_hom_left e)).trans (Category.comp_id _))
  map_add' := pointMapOfHom_add e.hom hμ

end PointTransport

section DivisorTransport

/-! The divisor-apparatus transport: `sectionsDivisor`, `torsionIdeal`, `IsSubgroup`, and
`HasExactOrder` along a pointed multiplication-compatible isomorphism. -/

open Scheme.IdealSheafData

/-- The scheme-level isomorphism of total spaces underlying an `Over`-isomorphism. -/
@[simps]
noncomputable def schemeIsoOfOverIso (e : E.asOver ≅ E'.asOver) : E.E ≅ E'.E where
  hom := e.hom.left
  inv := e.inv.left
  hom_inv_id := iso_hom_left_inv_left e
  inv_hom_id := iso_inv_left_hom_left e

/-- The sections-divisor of the transported family of points is the `comap` of the original
sections-divisor along the inverse isomorphism. -/
lemma sectionsDivisor_pointMap_ideal (e : E.asOver ≅ E'.asOver) {n : ℕ}
    (P : Fin n → E.Point (𝟙 S)) :
    (RelEffCartierDiv.sectionsDivisor E'.π
        (fun i ↦ pointMapOfHom e.hom (P i))).ideal
      = (RelEffCartierDiv.sectionsDivisor E.π P).ideal.comap e.inv.left := by
  have hpos : IsSeparated E.π ∧ SmoothOfRelativeDimension 1 E.π :=
    ⟨inferInstance, E.smooth⟩
  have hpos' : IsSeparated E'.π ∧ SmoothOfRelativeDimension 1 E'.π :=
    ⟨inferInstance, E'.smooth⟩
  rw [RelEffCartierDiv.sectionsDivisor, dif_pos hpos', RelEffCartierDiv.sectionsDivisor,
    dif_pos hpos, Scheme.IdealSheafData.comap_prod]
  show (∏ i, Scheme.Hom.ker ((pointMapOfHom e.hom (P i)).1 : S ⟶ E'.E))
    = ∏ i, (Scheme.Hom.ker ((P i).1 : S ⟶ E.E)).comap (schemeIsoOfOverIso e).inv
  exact Finset.prod_congr rfl fun a _ ↦
    Scheme.Hom.ker_comp_iso ((P a).1 : S ⟶ E.E) (schemeIsoOfOverIso e)

/-- `torsionIdeal` transports along a pointed multiplication-compatible isomorphism: the
`N`-torsion ideal of the target is the `comap` of the source's along the inverse. The
`[N]`-intertwining (`mulByHom_comp_monHom`) matches the two kernel pullbacks. -/
lemma torsionIdeal_eq_comap (e : E.asOver ≅ E'.asOver)
    (hη : η[E.asOver] ≫ e.hom = η[E'.asOver])
    (hμ : μ[E.asOver] ≫ e.hom = MonoidalCategory.tensorHom e.hom e.hom ≫ μ[E'.asOver])
    (N : ℕ) :
    E'.torsionIdeal N = (E.torsionIdeal N).comap e.inv.left := by
  show E'.torsionIdeal N = (E.torsionIdeal N).comap (schemeIsoOfOverIso e).inv
  rw [← map_hom_eq_comap_inv (schemeIsoOfOverIso e), torsionIdeal, torsionIdeal,
    ← Scheme.Hom.ker_comp]
  have hsq : E.mulByHom (N : ℤ) ≫ (schemeIsoOfOverIso e).hom
      = (schemeIsoOfOverIso e).hom ≫ E'.mulByHom (N : ℤ) :=
    mulByHom_comp_monHom e.hom hμ N
  have hz : E.zero ≫ (schemeIsoOfOverIso e).hom = 𝟙 S ≫ E'.zero :=
    (zero_comp_monHom e.hom hη).trans (Category.id_comp _).symm
  rw [show E.torsionι N ≫ (schemeIsoOfOverIso e).hom
      = pullback.map (E.mulByHom N) E.zero (E'.mulByHom N) E'.zero
          (schemeIsoOfOverIso e).hom (𝟙 S) (schemeIsoOfOverIso e).hom hsq hz
        ≫ E'.torsionι N from (pullback.lift_fst _ _ _).symm]
  have : IsIso (pullback.map (E.mulByHom (N : ℤ)) E.zero (E'.mulByHom (N : ℤ)) E'.zero
      (schemeIsoOfOverIso e).hom (𝟙 S) (schemeIsoOfOverIso e).hom hsq hz) :=
    pullback.map_isIso _ _ _ _ _ _ _ hsq hz
  exact (Scheme.Hom.ker_iso_comp
    (pullback.map (E.mulByHom (N : ℤ)) E.zero (E'.mulByHom (N : ℤ)) E'.zero
      (schemeIsoOfOverIso e).hom (𝟙 S) (schemeIsoOfOverIso e).hom hsq hz)
    (E'.torsionι N)).symm

/-- The subgroup-divisor property transports along a pointed multiplication-compatible
isomorphism, at the level of ideal equality: if `D'` on `E'` has the `comap`ped ideal of a
subgroup divisor `D` on `E`, then `D'` is a subgroup divisor. The point groups correspond by
`pointAddEquiv`; the factoring correspondence is `exists_factor_comap_iff`. -/
lemma _root_.ModularCurves.RelEffCartierDiv.IsSubgroup.of_ideal_comap
    (e : E.asOver ≅ E'.asOver)
    (hμ : μ[E.asOver] ≫ e.hom = MonoidalCategory.tensorHom e.hom e.hom ≫ μ[E'.asOver])
    {D : RelEffCartierDiv E.π} {D' : RelEffCartierDiv E'.π}
    (hI : D'.ideal = D.ideal.comap e.inv.left) (hD : D.IsSubgroup E) :
    D'.IsSubgroup E' := by
  intro T g
  obtain ⟨H, hH⟩ := hD g
  refine ⟨H.comap ((pointAddEquiv e hμ g).symm : E'.Point g ≃+ E.Point g).toAddMonoidHom,
    fun P ↦ ?_⟩
  rw [AddSubgroup.mem_comap, hH, hI]
  exact (Scheme.IdealSheafData.exists_factor_comap_iff D.ideal e.inv.left P.1).symm

/-- **Exact order transports along a multiplication-compatible isomorphism** (the
`IsGammaOne` iso-leg): the image of a point of exact order `N` has exact order `N`.
Pointedness is not needed — an additive map of point groups preserves zero automatically. -/
theorem Section.HasExactOrder.pointMap (e : E.asOver ≅ E'.asOver)
    (hμ : μ[E.asOver] ≫ e.hom = MonoidalCategory.tensorHom e.hom e.hom ≫ μ[E'.asOver])
    {P : E.Section} {N : ℕ} [NeZero N] (h : P.HasExactOrder E N) :
    Section.HasExactOrder E' (pointMapOfHom e.hom P) N := by
  show (Section.orderDivisor E' (pointMapOfHom e.hom P) N).IsSubgroup E'
  refine RelEffCartierDiv.IsSubgroup.of_ideal_comap e hμ ?_ h
  rw [Section.orderDivisor, Section.orderDivisor,
    show (fun a : Fin N ↦ ((((a : ℕ) : ℤ) + 1) • pointMapOfHom e.hom P : E'.Point (𝟙 S)))
        = fun a : Fin N ↦
          pointMapOfHom e.hom (((((a : ℕ) : ℤ) + 1) • P : E.Point (𝟙 S))) from
      funext fun a ↦ (map_zsmul (pointAddEquiv e hμ (𝟙 S)) _ _).symm]
  exact sectionsDivisor_pointMap_ideal e _

end DivisorTransport

end EllipticCurve

end ModularCurves

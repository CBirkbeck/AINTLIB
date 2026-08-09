/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.DivisorClass
import ModularCurves.WeilPairing.ChartGroupSum

/-!
# The normalized biextension class, and `[N]^* κ(Q) = κ(Q)^N` (DS4, `(★)` upper half)

This file supplies the last missing input of `Picard/SelfAdjointN.lean`: pullback along
`[N]` is the `N`-th power on the classes `κ(Q) = [𝒪(D_Q − D_0)]`.

## The route (class-level; no Poincaré *sheaf* is built)

The docstring of `ModularCurves.exists_pic_map_snd_picMap_mulByHom_kappa` proposes building
`𝒫 = m^*𝒜 ⊗ p₁^*𝒜⁻¹ ⊗ p₂^*𝒜⁻¹` on `E_T ×_T E_T` and using `τ^*𝒫 ≅ 𝒫`. That is more
machinery than the statement needs. Everything here happens in `Pic`, and the symmetry is
*definitional* rather than proved:

For an elliptic curve `𝔈 / T` write `a = [𝒪(D_0)] ∈ Pic 𝔈.E` (`zeroPicCls`). For a
`T`-scheme `g : Z ⟶ T` the `T`-morphisms `Z ⟶ 𝔈.E` form the group `𝔈.Point g`, and we set

* `xiCls h = h^* a ∈ Pic Z`   (`xiCls`);
* `bilCls h k = ξ(h+k) · ξ(h)⁻¹ · ξ(k)⁻¹ · ξ(0)`  (`bilCls`).

`bilCls` is symmetric because its defining expression is (`bilCls_comm`), is trivial when a
slot is `0` (`bilCls_zero_left`), and is natural for `Pic.map` along `T`-morphisms
(`bilCls_picMap`). Pulling `β` back along `(φ, ψ) : Z ⟶ 𝔈.E ×_T 𝔈.E` recovers the classical
`𝒫`; we never need `𝒫` itself, only the values.

The dictionary with `κ` is `κ(Q) = β(1, −Q∘π)` (`kappaCls`, identified with any class in
`Ker(0^*)` congruent to `[𝒪(D_Q − D_0)]` by `eq_kappaCls`, through the zero-section splitting
`Ker(0^*) ∩ Im(π^*) = 1`), whose two ingredients are

* `xiCls_eq_sectionPicCls`: `ξ(h) = [𝒪(D_P)]` when `h` is an automorphism of `𝔈.E` over `T`
  carrying `P` to the zero section — i.e. `t_{-P}^{-1}(D_0) = D_P`. This is the *only*
  geometric input beyond the theorem of the square, and it is
  `nonempty_pullback_idealModule_ker_of_iso` (`WeilPairing/TheoremOfSquareBaseChange.lean`)
  read in `Pic` through `picMap_picClass`.
* `Point.baseChangeEquiv` (`EllipticCurve/GroupLaw.lean`) for the level bridge.

The theorem of the square (`isSquareIdentity_point_add`) says `β(1, ·)` is additive on the
*constant* arguments `Q ∘ π`; naturality upgrades the first slot to an arbitrary
`T`-morphism, and running the same statement one level up — for `𝔈.baseChange 𝔈.π`, where the
constants are all of `𝔈.Point 𝔈.π` — upgrades the second slot too. That is exactly the
"symmetry turns additivity in the second variable into additivity in the first" step of the
sketch, with `𝔅` symmetric for free. Full biadditivity (`bilCls_add_right`) gives
`β(N·1, k) = β(1, k)^N`, and the `κ`-dictionary turns that into the headline
`picMap_mulByHom_eq_pow`.

## Relation to `GroupScheme/TranslationBySection.lean`

That file already builds translation by a section as an automorphism `translateByIso` of
`E.asOver` in `Over S`, from `Hom.commGroup`. The translation used here (`translPt`) is the
same map, but expressed inside the `𝔈.Point g` groups that carry the whole argument
(`ptComp`, `onePt`, `constPoint`), so that `xiCls_eq_sectionPicCls`, base change and the level
bridge all speak one language. `EllipticCurve.constPoint` here is deliberately *not*
`EllipticCurve.constPt` there (that one is the constant *endomorphism* of `E.asOver`); the
names are kept distinct because both live in `namespace ModularCurves.EllipticCurve`.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

/- **Name-clash disambiguation, no statement changed.** `ModularCurves.idealModule`
(`EllipticCurve/PoleSheaf.lean`, the ideal module of a *morphism*) shadows
`AlgebraicGeometry.Scheme.Modules.idealModule` (`Picard/IdealModule.lean`) inside
`namespace ModularCurves`; the same `local notation` pin is used in
`Picard/SelfAdjointN.lean`. `modPullback` abbreviates the module pullback functor, whose
short name `Modules.pullback` is likewise shadowed here. -/
local notation "idealModule" => AlgebraicGeometry.Scheme.Modules.idealModule
local notation "modPullback" => AlgebraicGeometry.Scheme.Modules.pullback

/-! ## Transporting a divisor class along a pullback -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The `Pic.map` reading of an ideal-module comparison.** If pulling `I(D)` back along
`g` is `I(D')`, then `Pic.map g` carries `[D]` to `[D']`. This is the bridge between the
module-level transport lemmas of `WeilPairing/TheoremOfSquareBaseChange.lean` and the
class-level algebra used below. -/
theorem picMap_picClass {C S C' S' : Scheme.{u}} {π : C ⟶ S} {π' : C' ⟶ S'} [IsSeparated π]
    [IsSeparated π'] (g : C' ⟶ C) {D : RelEffCartierDiv π} {D' : RelEffCartierDiv π'}
    (h : IsOfficialCartier π D.ideal) (h' : IsOfficialCartier π' D'.ideal)
    (e : Nonempty ((modPullback g).obj (idealModule D.ideal) ≅ idealModule D'.ideal)) :
    Scheme.Pic.map g (D.picClass h) = D'.picClass h' := by
  letI := AlgebraicGeometry.Scheme.Modules.monoidalCategory C
  letI := AlgebraicGeometry.Scheme.Modules.monoidalCategory C'
  show Scheme.Pic.map g ((D.isInvertible_idealModule h).isUnit_toSkeleton.unit⁻¹) =
    (D'.isInvertible_idealModule h').isUnit_toSkeleton.unit⁻¹
  rw [map_inv]
  refine congrArg Inv.inv (Units.ext ?_)
  rw [Scheme.Pic.map_val, IsUnit.unit_spec, IsUnit.unit_spec,
    Functor.mapSkeleton_obj_toSkeleton (modPullback g) (idealModule D.ideal)]
  exact toSkeleton_eq_toSkeleton_iff.mpr e

namespace EllipticCurve

variable {T : Scheme.{u}} (𝔈 : EllipticCurve T)

/-! ### Pure commutative-group algebra

Stated over *abstract* elements: the classes below are enormous terms, and AC-normalising
them directly does not terminate (the same discipline as `kappa_ratio_algebra` in
`Picard/SelfAdjointN.lean`). -/

private theorem cg_norm_ratio {G : Type*} [CommGroup G] (a b c d : G) :
    (a * d⁻¹) * ((b * d⁻¹) * (c * d⁻¹))⁻¹ = (a * d) * (b * c)⁻¹ := by
  group
  simp only [mul_comm, mul_assoc, mul_left_comm]

/-! ## Precomposition of points, as an additive map -/

/-- Precomposition of a `T`-point with a morphism over `T`. The index of the target is taken
as an explicit equation, so that the result can always be produced at the wanted index
without a transport. -/
def ptComp {Z Z' : Scheme.{u}} {g : Z ⟶ T} {g' : Z' ⟶ T} (σ : Z' ⟶ Z) (hσ : σ ≫ g = g')
    (P : 𝔈.Point g) : 𝔈.Point g' :=
  ⟨σ ≫ P.1, by rw [Category.assoc, P.2, hσ]⟩

@[simp] theorem ptComp_val {Z Z' : Scheme.{u}} {g : Z ⟶ T} {g' : Z' ⟶ T} (σ : Z' ⟶ Z)
    (hσ : σ ≫ g = g') (P : 𝔈.Point g) : (𝔈.ptComp σ hσ P).1 = σ ≫ P.1 := rfl

/-- Precomposition of points is additive: it is composition with an `Over T`-morphism, and
composition on the left distributes over the multiplication of a group object. -/
theorem ptComp_add {Z Z' : Scheme.{u}} {g : Z ⟶ T} {g' : Z' ⟶ T} (σ : Z' ⟶ Z)
    (hσ : σ ≫ g = g') (P Q : 𝔈.Point g) :
    𝔈.ptComp σ hσ (P + Q) = 𝔈.ptComp σ hσ P + 𝔈.ptComp σ hσ Q := by
  letI : CommGroup (Over.mk g ⟶ 𝔈.asOver) := CategoryTheory.Hom.commGroup
  letI : CommGroup (Over.mk g' ⟶ 𝔈.asOver) := CategoryTheory.Hom.commGroup
  have h1 : ∀ R : 𝔈.Point g, (𝔈.pointEquivOverHom g') (𝔈.ptComp σ hσ R) =
      (Over.homMk σ hσ : Over.mk g' ⟶ Over.mk g) ≫ (𝔈.pointEquivOverHom g) R := by
    intro R; ext; rfl
  refine (𝔈.pointEquivOverHom g').injective ?_
  rw [h1, 𝔈.pointEquivOverHom_add, 𝔈.pointEquivOverHom_add, h1, h1]
  exact MonObj.comp_mul _ _ _

/-- Precomposition of points, packaged as an additive map. -/
@[simps] def ptCompHom {Z Z' : Scheme.{u}} {g : Z ⟶ T} {g' : Z' ⟶ T} (σ : Z' ⟶ Z)
    (hσ : σ ≫ g = g') : 𝔈.Point g →+ 𝔈.Point g' where
  toFun := 𝔈.ptComp σ hσ
  map_zero' := by
    refine Subtype.ext ?_
    rw [ptComp_val, 𝔈.point_zero_val g, 𝔈.point_zero_val g', ← Category.assoc, hσ]
  map_add' := 𝔈.ptComp_add σ hσ

/-! ## The tautological, constant and translation points -/

/-- The tautological point `1 : 𝔈.E ⟶ 𝔈.E`, as a point of `𝔈` over `𝔈.π`. -/
def onePt : 𝔈.Point 𝔈.π := ⟨𝟙 𝔈.E, Category.id_comp _⟩

@[simp] theorem onePt_val : (𝔈.onePt).1 = 𝟙 𝔈.E := rfl

/-- A `T`-point read as a *constant* point over an arbitrary `T`-scheme `g : Z ⟶ T`. -/
def constPoint {Z : Scheme.{u}} (g : Z ⟶ T) (Q : 𝔈.Point (𝟙 T)) : 𝔈.Point g :=
  𝔈.ptComp g (Category.comp_id g) Q

@[simp] theorem constPoint_val {Z : Scheme.{u}} (g : Z ⟶ T) (Q : 𝔈.Point (𝟙 T)) :
    (𝔈.constPoint g Q).1 = g ≫ Q.1 := rfl

theorem constPoint_add {Z : Scheme.{u}} (g : Z ⟶ T) (Q Q' : 𝔈.Point (𝟙 T)) :
    𝔈.constPoint g (Q + Q') = 𝔈.constPoint g Q + 𝔈.constPoint g Q' :=
  𝔈.ptComp_add g (Category.comp_id g) Q Q'

theorem constPoint_neg {Z : Scheme.{u}} (g : Z ⟶ T) (Q : 𝔈.Point (𝟙 T)) :
    𝔈.constPoint g (-Q) = -𝔈.constPoint g Q :=
  (𝔈.ptCompHom g (Category.comp_id g)).map_neg Q

/-- Precomposition sends the tautological point to the precomposing morphism itself. -/
theorem ptComp_onePt {Z' : Scheme.{u}} {g' : Z' ⟶ T} (σ : Z' ⟶ 𝔈.E) (hσ : σ ≫ 𝔈.π = g') :
    𝔈.ptComp σ hσ 𝔈.onePt = ⟨σ, hσ⟩ :=
  Subtype.ext (Category.comp_id σ)

/-- Precomposition sends a constant point to the constant point at the new index. -/
theorem ptComp_constPoint {Z Z' : Scheme.{u}} {g : Z ⟶ T} {g' : Z' ⟶ T} (σ : Z' ⟶ Z)
    (hσ : σ ≫ g = g') (Q : 𝔈.Point (𝟙 T)) :
    𝔈.ptComp σ hσ (𝔈.constPoint g Q) = 𝔈.constPoint g' Q :=
  Subtype.ext (by rw [ptComp_val, constPoint_val, constPoint_val, ← Category.assoc, hσ])

/-- A `T`-point read as a constant point over `T` itself is itself. -/
theorem constPoint_id (Q : 𝔈.Point (𝟙 T)) : 𝔈.constPoint (𝟙 T) Q = Q :=
  Subtype.ext (Category.id_comp _)

/-- **Translation by `-Q`**, as a point over `𝔈.π`: the `T`-automorphism `x ↦ x - Q` of
`𝔈.E`, which carries the section `Q` to the zero section. -/
noncomputable def translPt (Q : 𝔈.Point (𝟙 T)) : 𝔈.Point 𝔈.π := 𝔈.onePt - 𝔈.constPoint 𝔈.π Q

theorem ptComp_translPt {Z' : Scheme.{u}} {g' : Z' ⟶ T} (σ : Z' ⟶ 𝔈.E) (hσ : σ ≫ 𝔈.π = g')
    (Q : 𝔈.Point (𝟙 T)) :
    𝔈.ptComp σ hσ (𝔈.translPt Q) = 𝔈.ptComp σ hσ 𝔈.onePt - 𝔈.constPoint g' Q := by
  rw [translPt, sub_eq_add_neg, ← 𝔈.constPoint_neg 𝔈.π, 𝔈.ptComp_add σ hσ,
    𝔈.ptComp_constPoint σ hσ, 𝔈.constPoint_neg g', ← sub_eq_add_neg]

theorem translPt_comp_translPt_neg (Q : 𝔈.Point (𝟙 T)) :
    (𝔈.translPt Q).1 ≫ (𝔈.translPt (-Q)).1 = 𝟙 𝔈.E := by
  have h : 𝔈.ptComp (𝔈.translPt Q).1 (𝔈.translPt Q).2 (𝔈.translPt (-Q)) = 𝔈.onePt := by
    rw [𝔈.ptComp_translPt _ (𝔈.translPt Q).2, 𝔈.ptComp_onePt _ (𝔈.translPt Q).2,
      𝔈.constPoint_neg 𝔈.π, sub_neg_eq_add]
    exact sub_add_cancel _ _
  exact congrArg Subtype.val h

instance isIso_translPt_val (Q : 𝔈.Point (𝟙 T)) : IsIso (𝔈.translPt Q).1 := by
  refine ⟨(𝔈.translPt (-Q)).1, 𝔈.translPt_comp_translPt_neg Q, ?_⟩
  simpa using 𝔈.translPt_comp_translPt_neg (-Q)

theorem comp_translPt (Q : 𝔈.Point (𝟙 T)) : Q.1 ≫ (𝔈.translPt Q).1 = 𝔈.zero := by
  have h : 𝔈.ptComp Q.1 Q.2 (𝔈.translPt Q) = (0 : 𝔈.Point (𝟙 T)) := by
    rw [𝔈.ptComp_translPt _ Q.2, 𝔈.ptComp_onePt _ Q.2, 𝔈.constPoint_id]
    exact sub_self _
  rw [show Q.1 ≫ (𝔈.translPt Q).1 = (𝔈.ptComp Q.1 Q.2 (𝔈.translPt Q)).1 from rfl, h,
    𝔈.point_zero_val (𝟙 T), Category.id_comp]

variable [IsSeparated 𝔈.π]

/-! ## The classes `ξ` and `β` -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `[𝒪(D_P)]`, the Picard class of the divisor of a section. Definitionally
`ModularCurves.sectionCls` of `Picard/SelfAdjointN.lean`, read on a bare working record. -/
noncomputable def sectionPicCls (P : T ⟶ 𝔈.E) (hP : P ≫ 𝔈.π = 𝟙 T) : Scheme.Pic 𝔈.E :=
  (RelEffCartierDiv.sectionDivisor 𝔈.π P hP).picClass
    (RelEffCartierDiv.sectionDivisor_isOfficial 𝔈.smooth P hP)

/-- `a = [𝒪(D_0)]`, the class of the zero-section divisor. -/
noncomputable def zeroPicCls : Scheme.Pic 𝔈.E := 𝔈.sectionPicCls 𝔈.zero 𝔈.zero_π

/-- `ξ(h) = h^* [𝒪(D_0)]`, for `h` a `T`-morphism `Z ⟶ 𝔈.E`. -/
noncomputable def xiCls {Z : Scheme.{u}} {g : Z ⟶ T} (h : 𝔈.Point g) : Scheme.Pic Z :=
  Scheme.Pic.map h.1 𝔈.zeroPicCls

/-- **The normalized biextension class.**
`β(h, k) = ξ(h+k) · ξ(h)⁻¹ · ξ(k)⁻¹ · ξ(0)`. Pulled back along `(φ, ψ)`, this is the
classical `𝒫 = m^*𝒜 ⊗ p₁^*𝒜⁻¹ ⊗ p₂^*𝒜⁻¹` normalized along the zero section; the point of
this presentation is that its symmetry is definitional. -/
noncomputable def bilCls {Z : Scheme.{u}} {g : Z ⟶ T} (h k : 𝔈.Point g) : Scheme.Pic Z :=
  𝔈.xiCls (h + k) * (𝔈.xiCls h)⁻¹ * (𝔈.xiCls k)⁻¹ * 𝔈.xiCls (0 : 𝔈.Point g)

/-- **`β` is symmetric** — for free, because its defining expression is. This is the
`τ^*𝒫 ≅ 𝒫` of the sketch. -/
theorem bilCls_comm {Z : Scheme.{u}} {g : Z ⟶ T} (h k : 𝔈.Point g) :
    𝔈.bilCls h k = 𝔈.bilCls k h := by
  rw [bilCls, bilCls, add_comm h k,
    mul_right_comm (𝔈.xiCls (k + h)) (𝔈.xiCls h)⁻¹ (𝔈.xiCls k)⁻¹]

/-- `β` is trivial when its first slot is `0`: the biextension is trivial on the axes. -/
@[simp] theorem bilCls_zero_left {Z : Scheme.{u}} {g : Z ⟶ T} (k : 𝔈.Point g) :
    𝔈.bilCls 0 k = 1 := by
  rw [bilCls, zero_add,
    mul_right_comm (𝔈.xiCls k) (𝔈.xiCls (0 : 𝔈.Point g))⁻¹ (𝔈.xiCls k)⁻¹,
    mul_inv_cancel, one_mul, inv_mul_cancel]

/-- `β` is trivial when its second slot is `0`. -/
@[simp] theorem bilCls_zero_right {Z : Scheme.{u}} {g : Z ⟶ T} (h : 𝔈.Point g) :
    𝔈.bilCls h 0 = 1 := by rw [bilCls_comm, bilCls_zero_left]

/-- `ξ` is natural for pullback along a morphism over `T`. -/
theorem xiCls_picMap {Z Z' : Scheme.{u}} {g : Z ⟶ T} {g' : Z' ⟶ T} (σ : Z' ⟶ Z)
    (hσ : σ ≫ g = g') (h : 𝔈.Point g) :
    Scheme.Pic.map σ (𝔈.xiCls h) = 𝔈.xiCls (𝔈.ptComp σ hσ h) := by
  show Scheme.Pic.map σ (Scheme.Pic.map h.1 𝔈.zeroPicCls) =
    Scheme.Pic.map (σ ≫ h.1) 𝔈.zeroPicCls
  rw [Scheme.Pic.map_comp]; rfl

/-- **`β` is natural for pullback along a morphism over `T`.** -/
theorem bilCls_picMap {Z Z' : Scheme.{u}} {g : Z ⟶ T} {g' : Z' ⟶ T} (σ : Z' ⟶ Z)
    (hσ : σ ≫ g = g') (h k : 𝔈.Point g) :
    Scheme.Pic.map σ (𝔈.bilCls h k) =
      𝔈.bilCls (𝔈.ptComp σ hσ h) (𝔈.ptComp σ hσ k) := by
  have e1 : 𝔈.ptComp σ hσ (h + k) = 𝔈.ptComp σ hσ h + 𝔈.ptComp σ hσ k := 𝔈.ptComp_add σ hσ h k
  have e2 : 𝔈.ptComp σ hσ (0 : 𝔈.Point g) = (0 : 𝔈.Point g') := (𝔈.ptCompHom σ hσ).map_zero
  rw [bilCls, map_mul, map_mul, map_mul, map_inv, map_inv, 𝔈.xiCls_picMap σ hσ,
    𝔈.xiCls_picMap σ hσ, 𝔈.xiCls_picMap σ hσ, 𝔈.xiCls_picMap σ hσ, e1, e2, bilCls]

/-! ## `ξ` on the tautological, constant, zero and translation points -/

@[simp] theorem xiCls_onePt : 𝔈.xiCls 𝔈.onePt = 𝔈.zeroPicCls := by
  show Scheme.Pic.map (𝟙 𝔈.E) 𝔈.zeroPicCls = _
  rw [Scheme.Pic.map_id]; rfl

theorem xiCls_constPoint {Z : Scheme.{u}} (g : Z ⟶ T) (Q : 𝔈.Point (𝟙 T)) :
    𝔈.xiCls (𝔈.constPoint g Q) = Scheme.Pic.map g (Scheme.Pic.map Q.1 𝔈.zeroPicCls) := by
  show Scheme.Pic.map (g ≫ Q.1) 𝔈.zeroPicCls = _
  rw [Scheme.Pic.map_comp]; rfl

theorem xiCls_zero {Z : Scheme.{u}} (g : Z ⟶ T) :
    𝔈.xiCls (0 : 𝔈.Point g) = Scheme.Pic.map g (Scheme.Pic.map 𝔈.zero 𝔈.zeroPicCls) := by
  show Scheme.Pic.map ((0 : 𝔈.Point g).1) 𝔈.zeroPicCls = _
  rw [𝔈.point_zero_val g, Scheme.Pic.map_comp]; rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The one geometric input beyond the theorem of the square**: `t_{-P}^{-1}(D_0) = D_P`.
If `h` is an automorphism of `𝔈.E` over `T` carrying the section `P` to the zero section,
then `ξ(h) = [𝒪(D_P)]`. Ideal-module content: `nonempty_pullback_idealModule_ker_of_iso`. -/
theorem xiCls_eq_sectionPicCls (h : 𝔈.Point 𝔈.π) [IsIso h.1] {P : T ⟶ 𝔈.E}
    (hP : P ≫ 𝔈.π = 𝟙 T) (hPh : P ≫ h.1 = 𝔈.zero) :
    𝔈.xiCls h = 𝔈.sectionPicCls P hP := by
  have hα : (asIso h.1).hom ≫ 𝔈.π = 𝔈.π ≫ (Iso.refl T).hom := by
    rw [Iso.refl_hom, Category.comp_id]; exact h.2
  have hPP : (Iso.refl T).inv ≫ P ≫ (asIso h.1).hom = 𝔈.zero := by
    rw [Iso.refl_inv, Category.id_comp]; exact hPh
  exact picMap_picClass h.1
    (RelEffCartierDiv.sectionDivisor_isOfficial 𝔈.smooth 𝔈.zero 𝔈.zero_π)
    (RelEffCartierDiv.sectionDivisor_isOfficial 𝔈.smooth P hP)
    (nonempty_pullback_idealModule_ker_of_iso 𝔈.smooth 𝔈.smooth (asIso h.1) (Iso.refl T)
      hα hP hPP)

/-- `ξ` of the translation point is the class of the section divisor: `t_{-Q}^{-1}(D_0)
= D_Q`. -/
theorem xiCls_translPt (Q : 𝔈.Point (𝟙 T)) :
    𝔈.xiCls (𝔈.translPt Q) = 𝔈.sectionPicCls Q.1 Q.2 :=
  𝔈.xiCls_eq_sectionPicCls (𝔈.translPt Q) Q.2 (𝔈.comp_translPt Q)

/-! ## The zero-section splitting, and reduction modulo `Im(π^*)` -/

omit [IsSeparated 𝔈.π] in
/-- `0^*` undoes `π^*`. -/
theorem picMap_zero_picMap_pi (M : Scheme.Pic T) :
    Scheme.Pic.map 𝔈.zero (Scheme.Pic.map 𝔈.π M) = M := by
  rw [show Scheme.Pic.map 𝔈.zero (Scheme.Pic.map 𝔈.π M)
        = Scheme.Pic.map (𝔈.zero ≫ 𝔈.π) M from by rw [Scheme.Pic.map_comp]; rfl,
    𝔈.zero_π, Scheme.Pic.map_id]
  rfl

/-- Reduction of a Picard class modulo the classes pulled back from the base. Working in
this quotient keeps every "differs by a class from the base" step to a `map_mul`, so no
`sectionPicCls` term is ever AC-normalised. -/
noncomputable def picModBase :
    Scheme.Pic 𝔈.E →* Scheme.Pic 𝔈.E ⧸ (Scheme.Pic.map 𝔈.π).range :=
  QuotientGroup.mk' _

omit [IsSeparated 𝔈.π] in
@[simp] theorem picModBase_picMap_pi (M : Scheme.Pic T) :
    𝔈.picModBase (Scheme.Pic.map 𝔈.π M) = 1 :=
  QuotientGroup.eq_one_iff _ |>.mpr ⟨M, rfl⟩

omit [IsSeparated 𝔈.π] in
/-- **`Ker(0^*) ∩ Im(π^*) = 1`** (GME p. 109): two classes killed by the zero-section
pullback and congruent modulo the base are equal. Same content as
`ModularCurves.eq_of_mul_inv_eq_picMap_snd` (`Picard/SelfAdjointN.lean`), re-proved here
because this file is imported by that one. -/
theorem eq_of_picModBase_eq {x y : Scheme.Pic 𝔈.E}
    (hx : Scheme.Pic.map 𝔈.zero x = 1) (hy : Scheme.Pic.map 𝔈.zero y = 1)
    (h : 𝔈.picModBase x = 𝔈.picModBase y) : x = y := by
  obtain ⟨M, hM⟩ := QuotientGroup.eq.mp h
  have h0 := congrArg (Scheme.Pic.map 𝔈.zero) hM
  rw [𝔈.picMap_zero_picMap_pi, map_mul, map_inv, hx, hy, inv_one, one_mul] at h0
  rw [h0, map_one] at hM
  exact inv_mul_eq_one.mp hM.symm

/-! ## `κ` in the `β` presentation -/

/-- `[𝒪(D_Q)] · [𝒪(D_0)]⁻¹`, the unnormalized `κ`. -/
noncomputable def normCls (Q : 𝔈.Point (𝟙 T)) : Scheme.Pic 𝔈.E :=
  𝔈.sectionPicCls Q.1 Q.2 * (𝔈.zeroPicCls)⁻¹

/-- **`κ(Q)` in biextension form**: `β(1, −Q∘π)`. That this really is `κ(Q)` is
`eq_kappaCls`, through the zero-section splitting. -/
noncomputable def kappaCls (Q : 𝔈.Point (𝟙 T)) : Scheme.Pic 𝔈.E :=
  𝔈.bilCls 𝔈.onePt (-(𝔈.constPoint 𝔈.π Q))

omit [IsSeparated 𝔈.π] in
theorem ptComp_zero_onePt : 𝔈.ptComp 𝔈.zero 𝔈.zero_π 𝔈.onePt = (0 : 𝔈.Point (𝟙 T)) := by
  rw [𝔈.ptComp_onePt 𝔈.zero 𝔈.zero_π]
  exact Subtype.ext (by rw [𝔈.point_zero_val (𝟙 T), Category.id_comp])

/-- Any `β(1, ·)` is killed by the zero-section pullback: `β` is trivial on the axes and
the tautological point restricts to `0` there. -/
theorem picMap_zero_bilCls_onePt (k : 𝔈.Point 𝔈.π) :
    Scheme.Pic.map 𝔈.zero (𝔈.bilCls 𝔈.onePt k) = 1 := by
  rw [𝔈.bilCls_picMap 𝔈.zero 𝔈.zero_π, 𝔈.ptComp_zero_onePt, bilCls_zero_left]

@[simp] theorem picMap_zero_kappaCls (Q : 𝔈.Point (𝟙 T)) :
    Scheme.Pic.map 𝔈.zero (𝔈.kappaCls Q) = 1 :=
  𝔈.picMap_zero_bilCls_onePt _

/-- The explicit shape of `β(1, −Q∘π)`: it is `[𝒪(D_Q − D_0)]` twisted by a class from the
base. -/
theorem kappaCls_eq_normCls_mul (Q : 𝔈.Point (𝟙 T)) :
    𝔈.kappaCls Q = 𝔈.normCls Q * Scheme.Pic.map 𝔈.π
      ((Scheme.Pic.map (-Q).1 𝔈.zeroPicCls)⁻¹ * Scheme.Pic.map 𝔈.zero 𝔈.zeroPicCls) := by
  rw [kappaCls, bilCls,
    show 𝔈.onePt + -(𝔈.constPoint 𝔈.π Q) = 𝔈.translPt Q from (sub_eq_add_neg _ _).symm,
    𝔈.xiCls_translPt, 𝔈.xiCls_onePt,
    show -(𝔈.constPoint 𝔈.π Q) = 𝔈.constPoint 𝔈.π (-Q) from (𝔈.constPoint_neg 𝔈.π Q).symm,
    𝔈.xiCls_constPoint, 𝔈.xiCls_zero, normCls, map_mul, map_inv, mul_assoc]

@[simp] theorem picModBase_kappaCls (Q : 𝔈.Point (𝟙 T)) :
    𝔈.picModBase (𝔈.kappaCls Q) = 𝔈.picModBase (𝔈.normCls Q) := by
  rw [𝔈.kappaCls_eq_normCls_mul Q, map_mul, 𝔈.picModBase_picMap_pi, mul_one]

/-- **The dictionary.** Any class killed by `0^*` and agreeing with `[𝒪(D_Q − D_0)]` modulo
`Im(π^*)` — in particular `ModularCurves.kappa` — is `β(1, −Q∘π)`. -/
theorem eq_kappaCls {Q : 𝔈.Point (𝟙 T)} {x : Scheme.Pic 𝔈.E}
    (hker : Scheme.Pic.map 𝔈.zero x = 1)
    (hx : 𝔈.picModBase x = 𝔈.picModBase (𝔈.normCls Q)) : x = 𝔈.kappaCls Q :=
  𝔈.eq_of_picModBase_eq hker (𝔈.picMap_zero_kappaCls Q)
    (hx.trans (𝔈.picModBase_kappaCls Q).symm)

/-! ## The theorem of the square, in `β` form -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The relative theorem of the square, Picard form.** `isSquareIdentity_point_add`
(`WeilPairing/ChartGroupSum.lean`) read through
`RelEffCartierDiv.exists_pic_map_of_nonempty_tensor_pullback_iso`. This is the bare-record
form of `ModularCurves.exists_pic_map_snd_sectionCls_add`. -/
theorem exists_picMap_pi_sectionPicCls_add (Q Q' : 𝔈.Point (𝟙 T)) :
    ∃ M : Scheme.Pic T,
      (𝔈.sectionPicCls (Q + Q').1 (Q + Q').2 * 𝔈.zeroPicCls) *
          (𝔈.sectionPicCls Q.1 Q.2 * 𝔈.sectionPicCls Q'.1 Q'.2)⁻¹
        = Scheme.Pic.map 𝔈.π M := by
  obtain ⟨N, hN, e⟩ := isSquareIdentity_point_add 𝔈 Q Q'
  exact RelEffCartierDiv.exists_pic_map_of_nonempty_tensor_pullback_iso
    (RelEffCartierDiv.sectionDivisor_isOfficial 𝔈.smooth Q.1 Q.2)
    (RelEffCartierDiv.sectionDivisor_isOfficial 𝔈.smooth Q'.1 Q'.2)
    (RelEffCartierDiv.sectionDivisor_isOfficial 𝔈.smooth (Q + Q').1 (Q + Q').2)
    (RelEffCartierDiv.sectionDivisor_isOfficial 𝔈.smooth 𝔈.zero 𝔈.zero_π) hN e

theorem picModBase_normCls_add (Q Q' : 𝔈.Point (𝟙 T)) :
    𝔈.picModBase (𝔈.normCls (Q + Q'))
      = 𝔈.picModBase (𝔈.normCls Q) * 𝔈.picModBase (𝔈.normCls Q') := by
  obtain ⟨M, hM⟩ := 𝔈.exists_picMap_pi_sectionPicCls_add Q Q'
  have h : 𝔈.normCls (Q + Q') * (𝔈.normCls Q * 𝔈.normCls Q')⁻¹ = Scheme.Pic.map 𝔈.π M := by
    rw [normCls, normCls, normCls, cg_norm_ratio]; exact hM
  have h2 := congrArg 𝔈.picModBase h
  rw [map_mul, map_inv, map_mul, 𝔈.picModBase_picMap_pi] at h2
  exact mul_inv_eq_one.mp h2

/-- **`κ` is additive** — the bare-record form of `ModularCurves.kappa_add`, in the `β`
presentation. -/
theorem kappaCls_add (Q Q' : 𝔈.Point (𝟙 T)) :
    𝔈.kappaCls (Q + Q') = 𝔈.kappaCls Q * 𝔈.kappaCls Q' := by
  refine 𝔈.eq_of_picModBase_eq (𝔈.picMap_zero_kappaCls _) ?_ ?_
  · rw [map_mul, 𝔈.picMap_zero_kappaCls, 𝔈.picMap_zero_kappaCls, one_mul]
  · rw [map_mul, 𝔈.picModBase_kappaCls, 𝔈.picModBase_kappaCls, 𝔈.picModBase_kappaCls,
      𝔈.picModBase_normCls_add]

/-- **`β(1, ·)` is additive on constants.** This is exactly the theorem of the square: for a
constant `Q ∘ π`, `β(1, Q ∘ π) = κ(−Q)`. -/
theorem bilCls_onePt_constPoint_add (Q Q' : 𝔈.Point (𝟙 T)) :
    𝔈.bilCls 𝔈.onePt (𝔈.constPoint 𝔈.π Q + 𝔈.constPoint 𝔈.π Q')
      = 𝔈.bilCls 𝔈.onePt (𝔈.constPoint 𝔈.π Q) * 𝔈.bilCls 𝔈.onePt (𝔈.constPoint 𝔈.π Q') := by
  have hc : ∀ R : 𝔈.Point (𝟙 T),
      𝔈.bilCls 𝔈.onePt (𝔈.constPoint 𝔈.π R) = 𝔈.kappaCls (-R) := by
    intro R
    rw [kappaCls, 𝔈.constPoint_neg 𝔈.π, neg_neg]
  rw [hc, hc, ← 𝔈.constPoint_add 𝔈.π, hc, ← 𝔈.kappaCls_add, neg_add]

/-- **`β(·, ·)` is additive in the second slot on constants, for an arbitrary first slot.**
Naturality of `β` moves the theorem of the square from the tautological point to any
`T`-morphism into `𝔈.E`. -/
theorem bilCls_constPoint_add {Z : Scheme.{u}} {g : Z ⟶ T} (σ : 𝔈.Point g)
    (Q Q' : 𝔈.Point (𝟙 T)) :
    𝔈.bilCls σ (𝔈.constPoint g Q + 𝔈.constPoint g Q')
      = 𝔈.bilCls σ (𝔈.constPoint g Q) * 𝔈.bilCls σ (𝔈.constPoint g Q') := by
  have hσ : 𝔈.ptComp σ.1 σ.2 𝔈.onePt = σ := 𝔈.ptComp_onePt σ.1 σ.2
  have hnat : ∀ k : 𝔈.Point 𝔈.π, Scheme.Pic.map σ.1 (𝔈.bilCls 𝔈.onePt k)
      = 𝔈.bilCls σ (𝔈.ptComp σ.1 σ.2 k) := by
    intro k; rw [𝔈.bilCls_picMap σ.1 σ.2, hσ]
  have h := congrArg (Scheme.Pic.map σ.1) (𝔈.bilCls_onePt_constPoint_add Q Q')
  rw [map_mul, hnat, hnat, hnat, 𝔈.ptComp_add σ.1 σ.2, 𝔈.ptComp_constPoint σ.1 σ.2,
    𝔈.ptComp_constPoint σ.1 σ.2] at h
  exact h

/-! ## One level up: `𝔈` base-changed along its own structure map

Over the base `𝔈.E`, the *constant* points of `𝔈.baseChange 𝔈.π` are **all** the
`T`-morphisms `𝔈.E ⟶ 𝔈.E`. So the theorem of the square applied one level up, transported
back by `Point.baseChangeEquiv`, upgrades `bilCls_constPoint_add` to full additivity in the
second slot — and hence, by `bilCls_comm`, to biadditivity. This is the "symmetry upgrades
additivity in the second variable to additivity in the first" step. -/

omit [IsSeparated 𝔈.π] in
/-- Reindexing a point along an equality of structure maps. -/
noncomputable def ptReindex {Z : Scheme.{u}} {g g' : Z ⟶ T} (h : g = g') :
    𝔈.Point g ≃+ 𝔈.Point g' := by
  subst h; exact AddEquiv.refl _

omit [IsSeparated 𝔈.π] in
@[simp] theorem ptReindex_val {Z : Scheme.{u}} {g g' : Z ⟶ T} (h : g = g') (x : 𝔈.Point g) :
    (𝔈.ptReindex h x).1 = x.1 := by subst h; rfl

instance isSeparated_baseChange_pi : IsSeparated (𝔈.baseChange 𝔈.π).π :=
  MorphismProperty.pullback_snd (P := @IsSeparated) 𝔈.π 𝔈.π ‹_›

omit [IsSeparated 𝔈.π] in
/-- **The level bridge.** A point of `𝔈 ×_T 𝔈.E` over `Z` is a `T`-morphism `Z ⟶ 𝔈.E`,
additively — `Point.baseChangeEquiv`, reindexed to the wanted structure map. -/
noncomputable def bcePt {Z : Scheme.{u}} {g : Z ⟶ 𝔈.E} {g' : Z ⟶ T} (hg : g ≫ 𝔈.π = g') :
    (𝔈.baseChange 𝔈.π).Point g →+ 𝔈.Point g' :=
  (𝔈.ptReindex hg).toAddMonoidHom.comp (Point.baseChangeEquiv 𝔈 𝔈.π g).toAddMonoidHom

omit [IsSeparated 𝔈.π] in
@[simp] theorem bcePt_val {Z : Scheme.{u}} {g : Z ⟶ 𝔈.E} {g' : Z ⟶ T} (hg : g ≫ 𝔈.π = g')
    (x : (𝔈.baseChange 𝔈.π).Point g) :
    (𝔈.bcePt hg x).1 = x.1 ≫ Limits.pullback.fst 𝔈.π 𝔈.π :=
  𝔈.ptReindex_val hg _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The zero-section class base-changes: `p₁^*[𝒪(D_0)] = [𝒪(D_{0'})]`. -/
theorem picMap_fst_zeroPicCls :
    Scheme.Pic.map (Limits.pullback.fst 𝔈.π 𝔈.π) 𝔈.zeroPicCls
      = (𝔈.baseChange 𝔈.π).zeroPicCls :=
  picMap_picClass _ (RelEffCartierDiv.sectionDivisor_isOfficial 𝔈.smooth 𝔈.zero 𝔈.zero_π)
    (RelEffCartierDiv.sectionDivisor_isOfficial (𝔈.baseChange 𝔈.π).smooth
      (𝔈.baseChange 𝔈.π).zero (𝔈.baseChange 𝔈.π).zero_π)
    (nonempty_pullback_idealModule_ker_sectionBaseChange 𝔈.smooth 𝔈.zero 𝔈.zero_π 𝔈.π)

theorem xiCls_baseChange {Z : Scheme.{u}} {g : Z ⟶ 𝔈.E} {g' : Z ⟶ T} (hg : g ≫ 𝔈.π = g')
    (x : (𝔈.baseChange 𝔈.π).Point g) :
    (𝔈.baseChange 𝔈.π).xiCls x = 𝔈.xiCls (𝔈.bcePt hg x) := by
  -- term-mode throughout: `(𝔈.baseChange 𝔈.π).E` is defeq to `pullback 𝔈.π 𝔈.π` only at
  -- default transparency, so `rw`'s matcher rejects the mixed composites
  have h1 : 𝔈.xiCls (𝔈.bcePt hg x)
      = Scheme.Pic.map (x.1 ≫ Limits.pullback.fst 𝔈.π 𝔈.π) 𝔈.zeroPicCls :=
    congrArg (fun m => Scheme.Pic.map m 𝔈.zeroPicCls) (𝔈.bcePt_val hg x)
  have h2 : Scheme.Pic.map (x.1 ≫ Limits.pullback.fst 𝔈.π 𝔈.π) 𝔈.zeroPicCls
      = Scheme.Pic.map x.1 (Scheme.Pic.map (Limits.pullback.fst 𝔈.π 𝔈.π) 𝔈.zeroPicCls) :=
    DFunLike.congr_fun (Scheme.Pic.map_comp x.1 (Limits.pullback.fst 𝔈.π 𝔈.π)) 𝔈.zeroPicCls
  have h3 : Scheme.Pic.map x.1 (Scheme.Pic.map (Limits.pullback.fst 𝔈.π 𝔈.π) 𝔈.zeroPicCls)
      = (𝔈.baseChange 𝔈.π).xiCls x :=
    congrArg (Scheme.Pic.map x.1) 𝔈.picMap_fst_zeroPicCls
  exact (h1.trans (h2.trans h3)).symm

theorem bilCls_baseChange {Z : Scheme.{u}} {g : Z ⟶ 𝔈.E} {g' : Z ⟶ T} (hg : g ≫ 𝔈.π = g')
    (x y : (𝔈.baseChange 𝔈.π).Point g) :
    (𝔈.baseChange 𝔈.π).bilCls x y = 𝔈.bilCls (𝔈.bcePt hg x) (𝔈.bcePt hg y) := by
  rw [bilCls, bilCls, 𝔈.xiCls_baseChange hg, 𝔈.xiCls_baseChange hg, 𝔈.xiCls_baseChange hg,
    𝔈.xiCls_baseChange hg, map_add, map_zero]

omit [IsSeparated 𝔈.π] in
/-- The section of `p₂ : 𝔈.E ×_T 𝔈.E ⟶ 𝔈.E` attached to a `T`-endomorphism of `𝔈.E`:
the graph. -/
noncomputable def graphPt (w : 𝔈.Point 𝔈.π) : (𝔈.baseChange 𝔈.π).Point (𝟙 𝔈.E) :=
  ⟨Limits.pullback.lift w.1 (𝟙 𝔈.E) (by rw [w.2, Category.id_comp]),
    Limits.pullback.lift_snd _ _ _⟩

omit [IsSeparated 𝔈.π] in
@[simp] theorem bcePt_graphPt (w : 𝔈.Point 𝔈.π) :
    𝔈.bcePt (Category.id_comp 𝔈.π) (𝔈.graphPt w) = w :=
  Subtype.ext ((𝔈.bcePt_val (Category.id_comp 𝔈.π) _).trans (Limits.pullback.lift_fst _ _ _))

/-- **Full additivity of `β` in the second slot.** The theorem of the square for
`𝔈.baseChange 𝔈.π`, whose constants exhaust `𝔈.Point 𝔈.π`, transported back down. -/
theorem bilCls_add_right (u v v' : 𝔈.Point 𝔈.π) :
    𝔈.bilCls u (v + v') = 𝔈.bilCls u v * 𝔈.bilCls u v' := by
  have key := (𝔈.baseChange 𝔈.π).bilCls_constPoint_add (𝔈.graphPt u) (𝔈.graphPt v)
    (𝔈.graphPt v')
  rw [(𝔈.baseChange 𝔈.π).constPoint_id, (𝔈.baseChange 𝔈.π).constPoint_id,
    𝔈.bilCls_baseChange (Category.id_comp 𝔈.π),
    𝔈.bilCls_baseChange (Category.id_comp 𝔈.π),
    𝔈.bilCls_baseChange (Category.id_comp 𝔈.π), map_add, 𝔈.bcePt_graphPt,
    𝔈.bcePt_graphPt, 𝔈.bcePt_graphPt] at key
  exact key

/-- **Full additivity of `β` in the first slot**, by symmetry. -/
theorem bilCls_add_left (u u' v : 𝔈.Point 𝔈.π) :
    𝔈.bilCls (u + u') v = 𝔈.bilCls u v * 𝔈.bilCls u' v := by
  rw [bilCls_comm, 𝔈.bilCls_add_right, bilCls_comm, 𝔈.bilCls_comm u' v]

theorem bilCls_nsmul_right (u v : 𝔈.Point 𝔈.π) (n : ℕ) :
    𝔈.bilCls u (n • v) = (𝔈.bilCls u v) ^ n := by
  induction n with
  | zero => rw [zero_smul, bilCls_zero_right, pow_zero]
  | succ n ih => rw [succ_nsmul, 𝔈.bilCls_add_right, ih, pow_succ]

/-! ## The headline: `[N]^* κ(Q) = κ(Q)^N` -/

omit [IsSeparated 𝔈.π] in
theorem ptComp_mulByHom_onePt (n : ℤ) :
    𝔈.ptComp (𝔈.mulByHom n) (𝔈.mulByHom_π n) 𝔈.onePt = n • 𝔈.onePt := by
  refine Subtype.ext ?_
  rw [ptComp_val, onePt_val, Category.comp_id, 𝔈.point_smul_eq_comp_mulBy 𝔈.π n 𝔈.onePt,
    onePt_val, Category.id_comp]

/-- **`[N]^* κ(Q) = κ(Q)^N`.** Naturality of `β` turns `[N]^*` into `N · 1` in the first
slot; symmetry moves it to the second, where biadditivity finishes. -/
theorem picMap_mulByHom_kappaCls (N : ℕ) (Q : 𝔈.Point (𝟙 T)) :
    Scheme.Pic.map (𝔈.mulByHom (N : ℤ)) (𝔈.kappaCls Q) = 𝔈.kappaCls Q ^ N := by
  have hm := 𝔈.mulByHom_π (N : ℤ)
  have hnat := 𝔈.bilCls_picMap (𝔈.mulByHom (N : ℤ)) hm 𝔈.onePt (-(𝔈.constPoint 𝔈.π Q))
  have hone : 𝔈.ptComp (𝔈.mulByHom (N : ℤ)) hm 𝔈.onePt = (N : ℕ) • 𝔈.onePt := by
    rw [𝔈.ptComp_mulByHom_onePt, natCast_zsmul]
  have hk : 𝔈.ptComp (𝔈.mulByHom (N : ℤ)) hm (-(𝔈.constPoint 𝔈.π Q))
      = -(𝔈.constPoint 𝔈.π Q) :=
    calc 𝔈.ptComp (𝔈.mulByHom (N : ℤ)) hm (-(𝔈.constPoint 𝔈.π Q))
        = -(𝔈.ptComp (𝔈.mulByHom (N : ℤ)) hm (𝔈.constPoint 𝔈.π Q)) :=
          (𝔈.ptCompHom (𝔈.mulByHom (N : ℤ)) hm).map_neg _
      _ = -(𝔈.constPoint 𝔈.π Q) := congrArg Neg.neg (𝔈.ptComp_constPoint _ hm Q)
  rw [hone, hk] at hnat
  rw [kappaCls, hnat, 𝔈.bilCls_comm (N • 𝔈.onePt), 𝔈.bilCls_nsmul_right,
    𝔈.bilCls_comm (-(𝔈.constPoint 𝔈.π Q))]

/-- **The consumer form.** Any class killed by the zero-section pullback and agreeing with
`[𝒪(D_Q)] · [𝒪(D_0)]⁻¹` up to a class from the base — i.e. `ModularCurves.kappa` — satisfies
`[N]^* x = x^N`. -/
theorem picMap_mulByHom_eq_pow (N : ℕ) (Q : 𝔈.Point (𝟙 T)) (x : Scheme.Pic 𝔈.E)
    (hker : Scheme.Pic.map 𝔈.zero x = 1) (M : Scheme.Pic T)
    (hx : x * (𝔈.sectionPicCls Q.1 Q.2 * (𝔈.zeroPicCls)⁻¹)⁻¹ = Scheme.Pic.map 𝔈.π M) :
    Scheme.Pic.map (𝔈.mulByHom (N : ℤ)) x = x ^ N := by
  have hmod : 𝔈.picModBase x = 𝔈.picModBase (𝔈.normCls Q) := by
    have h := congrArg 𝔈.picModBase hx
    rw [map_mul, map_inv, 𝔈.picModBase_picMap_pi] at h
    exact mul_inv_eq_one.mp h
  rw [𝔈.eq_kappaCls hker hmod]
  exact 𝔈.picMap_mulByHom_kappaCls N Q

end EllipticCurve

end ModularCurves

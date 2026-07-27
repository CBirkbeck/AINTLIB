/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.LevelStructure.ExactOrder
import ModularCurves.ForMathlib.CartierDual
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Deligne's order theorem — Layer B: the geometric bridge (BB-DELIGNE)

Layer A (`ModularCurves.CartierDual.deligne_pointConv_pow_finrank` /
`deligne_point_pow_eq_one`) proves Deligne's theorem **abstractly**: for a commutative
cocommutative Hopf algebra `A` finite free over a ring `R`, every `B`-point `φ : A →ₐ[R] B`
satisfies `(toConv φ) ^ (finrank R A) = 1` in the convolution group of points
`WithConv (A →ₐ[R] B)` — i.e. the group of points of `G = Spec A` is killed by the order.

This file is **Layer B**: the bridge from that abstract statement to the geometric box
`RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors` (`LevelStructure/ExactOrder.lean`) — a
subgroup divisor `D ⊂ E` of constant degree `N` kills every point factoring through it,
`(N : ℤ) • Q = 0`. This is KM 1.4.2 / Tate CSS §3.8: *"a finite locally free commutative group
scheme of rank `N` is killed by `N`."*

## The route (source-faithful to Tate: `G` finite flat ⟹ `G = Spec A`, `A` a Hopf algebra)

The substrate audit (2026-07-08) confirmed **all of Layer B is absent** from both the project and
mathlib — there is no scheme group-object ↔ Hopf-algebra duality, and the group-object
multiplication on `D.subscheme` is deliberately deferred in `GroupScheme/Subgroup.lean`. The bridge
is therefore built here from scratch, along these leaves:

* **L1 (reduction to an affine base).** `(N : ℤ) • Q = 0` is local on `T` and stable under base
  change (`Point.pull_zsmul`/`_zero`, `RelEffCartierDiv.IsSubgroup.baseChange`, all proven), so the
  box reduces to `S = Spec R` affine and `T = Spec B` affine — where a genuine ring `R` and a point
  `φ : A →ₐ[R] B` are available.
* **L2 (the coordinate algebra).** `D.subscheme` is finite over `Spec R`, hence affine
  (`isAffine_of_isAffineHom`), so `A := Γ(D.subscheme, ⊤)` is a finite `R`-algebra (the
  `torsionAlgebra` pattern of `WeilPairing/EtaleDescent.lean`).
* **L3 (the Hopf structure).** The curve group law restricts to `D` (by `IsSubgroup`), giving a
  comultiplication `Δ : A →ₐ[R] A ⊗_R A` dual to `m : D ×_S D → D` (built by Yoneda from the sum of
  the two universal points of `D ×_S D`, which factors through `D`); counit dual to the unit
  section; antipode dual to inversion. `A` becomes a commutative cocommutative `HopfAlgebra R A`.
* **L5 (free-vs-projective).** `A` is finite *projective* (locally free); Deligne needs *free*, so
  Zariski-localize `Spec R` over a cover trivialising `A`, apply Deligne on each piece, and glue
  (the goal is local on `Spec R`).
* **L6 (points ↔ convolution).** The factoring points `Q ∈ D(Spec B)` correspond to `φ : A →ₐ[R] B`
  (`ΓSpec` adjunction, `Scheme.isoSpec`), and the curve group law on `D(Spec B)` matches convolution
  in `WithConv (A →ₐ[R] B)` (dual to `Δ`); in particular `(N : ℤ) • Q ↔ (toConv φ) ^ N` and
  `0 ↔ 1`.
* **L7 (assembly).** `deligne_point_pow_eq_one` gives `(toConv φ) ^ N = 1`, i.e. `N • Q = 0`.

Full plan: `.mathlib-quality/plan-deligne.md`. `sorry`s here are Layer-B leaves, tracked as
sub-tickets T-D5h..k (WIP, producer discipline).
-/

open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

universe u

namespace ModularCurves

namespace EllipticCurve

section PointRestrict

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- **(Layer B, L4 infrastructure.)** Restriction of a point along `k : T' ⟶ T` is additive — it is
a group homomorphism `E.Point g → E.Point (k ≫ g)`. Like `Point.pull_add`, this is precomposition
in the `Over S`-category (`Over.homMk k`), which distributes over the point group multiplication
because `E.asOver` is a group object (`MonObj.comp_mul`). This is the transport lemma underlying the
scheme-level group axioms (m assoc/comm, unit, inverse) that dualize to the Hopf laws. -/
theorem Point.restrict_add {T T' : Scheme.{u}} {g : T ⟶ S} (k : T' ⟶ T) (P Q : E.Point g) :
    Point.restrict E k (P + Q) = Point.restrict E k P + Point.restrict E k Q := by
  letI : CommGroup (Over.mk g ⟶ E.asOver) := Hom.commGroup
  letI : CommGroup (Over.mk (k ≫ g) ⟶ E.asOver) := Hom.commGroup
  refine (E.pointEquivOverHom (k ≫ g)).injective ?_
  have hw : k ≫ (Over.mk g).hom = (Over.mk (k ≫ g)).hom := rfl
  have corr : ∀ R : E.Point g, (E.pointEquivOverHom (k ≫ g)) (Point.restrict E k R) =
      (Over.homMk k hw : Over.mk (k ≫ g) ⟶ Over.mk g) ≫ (E.pointEquivOverHom g) R := by
    intro R
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    rfl
  rw [pointEquivOverHom_add, corr, corr, corr, pointEquivOverHom_add, MonObj.comp_mul]

/-- Restriction of a point is additive, hence sends the zero point to the zero point. -/
theorem Point.restrict_zero {T T' : Scheme.{u}} {g : T ⟶ S} (k : T' ⟶ T) :
    Point.restrict E k (0 : E.Point g) = 0 := by
  have h := Point.restrict_add E k (0 : E.Point g) 0
  rw [add_zero] at h
  exact (add_left_cancel (a := Point.restrict E k (0 : E.Point g)) (by rw [add_zero]; exact h)).symm

open MonoidalCategory CartesianMonoidalCategory MonObj in
/-- The underlying morphism of the zero point is the pulled-back zero section
(`(0 : E.Point g).1 = g ≫ E.zero`); the group-object unit of `Hom.commGroup` unfolds to `E.zero`
via the terminal map of `Over S`. Used to identify restrictions through the unit section. -/
theorem point_zero_val {T : Scheme.{u}} (g : T ⟶ S) :
    ((0 : E.Point g) : T ⟶ E.E) = g ≫ E.zero := by
  have h0 : (0 : E.Point g) = (E.pointEquivOverHom g).symm
      (Additive.toMul (0 : Additive (Over.mk g ⟶ E.asOver))) := rfl
  rw [h0, toMul_zero]
  show ((1 : Over.mk g ⟶ E.asOver)).left = g ≫ E.zero
  rw [Hom.one_def, Over.comp_left, E.one_eq_zero]
  have hw : (toUnit (Over.mk g)).left ≫ (𝟙_ (Over S)).hom = g :=
    Over.w (toUnit (Over.mk g))
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun m ↦ m ≫ E.zero) hw)

/-- The underlying morphism of the negation of a point is composition with `[-1]`
(`(-P).1 = P.1 ≫ mulByHom (-1)`); specialises `point_smul_eq_comp_mulBy` at `-1`. Used to identify
restrictions through the inversion morphism. -/
theorem point_neg_val {T : Scheme.{u}} {g : T ⟶ S} (P : E.Point g) :
    ((-P : E.Point g) : T ⟶ E.E) = (P : T ⟶ E.E) ≫ E.mulByHom (-1) := by
  have h := E.point_smul_eq_comp_mulBy g (-1) P
  rwa [neg_one_zsmul] at h

open MonoidalCategory CartesianMonoidalCategory MonObj in
/-- **(Layer B, L4 infrastructure — the point-addition underlying-map spec.)** The underlying
morphism of a sum of points is the cartesian lift of the two summands' morphisms into
`E ×_S E`, post-composed with the group law `μ[E.asOver]`. This is the analog of
`point_smul_eq_comp_mulBy` for binary addition (dualizing to the coproduct in the Hopf structure);
it lets the scheme group axioms (m assoc/comm/unit/inv) be proven at the level of underlying
morphisms — no base-dependent transport. Same 2-line proof as `PullSectionAdd`'s `hx`. -/
theorem point_add_eq_lift {T : Scheme.{u}} (g : T ⟶ S) (P Q : E.Point g) :
    (P + Q).1 =
      (lift (E.pointEquivOverHom g P) (E.pointEquivOverHom g Q)).left ≫ (μ[E.asOver]).left :=
  (congrArg CommaMorphism.left (E.pointEquivOverHom_add g P Q)).trans
    (Over.comp_left _ _ _ _ _)

end PointRestrict

section AffineBase

variable {R : Type u} [CommRing R] (E : EllipticCurve (Spec (CommRingCat.of R)))
  (D : RelEffCartierDiv E.π)

/-- The structure map `q = subschemeι ≫ π : D.subscheme ⟶ Spec R` of the divisor's total space
over the affine base. -/
noncomputable abbrev subgroupStructMap : D.ideal.subscheme ⟶ Spec (CommRingCat.of R) :=
  D.ideal.subschemeι ≫ E.π

/-- **(Layer B, L2 — the coordinate algebra structure.)** `D.subscheme` is finite over the affine
base `Spec R` (`D.finite`), hence affine (`isAffine_of_isAffineHom`); its global sections
`Γ(D.subscheme, ⊤)` therefore carry an `R`-algebra structure through `R ≅ Γ(Spec R, ⊤)`. This is the
Hopf algebra `A_D` of Deligne's proof (Hopf structure added in L3). Mirrors the `torsionAlgebra`
construction of `WeilPairing/EtaleDescent.lean`. -/
noncomputable def subgroupAlgebra : Algebra R Γ(D.ideal.subscheme, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom.toAlgebra

/-- With the `R`-algebra structure `subgroupAlgebra`, the coordinate algebra `Γ(D.subscheme, ⊤)` is
a finite `R`-module — from finiteness of `D.subscheme` over `Spec R` (`D.finite`). -/
theorem subgroupAlgebra_finite :
    letI := E.subgroupAlgebra D
    Module.Finite R Γ(D.ideal.subscheme, ⊤) := by
  haveI : IsFinite (E.subgroupStructMap D) := D.finite
  haveI : IsAffine D.ideal.subscheme := isAffine_of_isAffineHom (E.subgroupStructMap D)
  letI := E.subgroupAlgebra D
  have h : RingHom.Finite
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom := by
    rw [CommRingCat.hom_comp]
    exact (RingHom.finite_respectsIso.cancel_left_isIso _ _).mpr
      ((E.subgroupStructMap D).finite_app ⊤ (isAffineOpen_top _))
  exact h

/-- **(Layer B, affine core.)** The box `smul_eq_zero_of_factors` over an *affine* base
`Spec R`, with the point taken as a section `Q : E.Section`: a subgroup divisor `D` of constant
degree `N` kills every section factoring through it. This is where Deligne's abstract theorem
applies (a genuine ring `R` and coordinate Hopf algebra `A = Γ(D.subscheme, ⊤)` are available). The
general box (`smul_eq_zero_of_factors'`, arbitrary base `S` and `T`-point `Q`) reduces to this by
L1. Proven via L2 (algebra) + L3/L4 (Hopf structure) + L5 (localise to free) + L6 (points ↔
convolution) + L7 (`deligne_point_pow_eq_one`). -/
theorem smul_eq_zero_of_factors_affine {N : ℕ} [NeZero N] (hD : D.IsSubgroup E)
    (hdeg : ∀ s, D.degree s = N) (Q : E.Section)
    (hQ : ∃ h : Spec (CommRingCat.of R) ⟶ D.ideal.subscheme, h ≫ D.ideal.subschemeι = Q.1) :
    (N : ℤ) • Q = 0 := by
  sorry

end AffineBase

section GroupObject

variable {S : Scheme.{u}} (E : EllipticCurve S) {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E)

/-- The base structure map `D ×_S D ⟶ S` of the self-product of the divisor's total space. -/
noncomputable abbrev bimulBase :
    pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) ⟶ S :=
  pullback.fst _ _ ≫ D.ideal.subschemeι ≫ E.π

/-- The first universal point of `D ×_S D`: the first projection, viewed as a point of `E`
factoring through `D`. -/
noncomputable def bipt₁ : E.Point (E.bimulBase (D := D)) :=
  ⟨pullback.fst _ _ ≫ D.ideal.subschemeι, by rw [Category.assoc]⟩

/-- The second universal point of `D ×_S D`: the second projection, viewed as a point of `E`
factoring through `D`. -/
noncomputable def bipt₂ : E.Point (E.bimulBase (D := D)) :=
  ⟨pullback.snd _ _ ≫ D.ideal.subschemeι, by
    rw [Category.assoc]; exact (pullback.condition).symm⟩

/-- The universal point of `D.subscheme`: the identity morphism, viewed as a point of `E` factoring
through `D` (over the structure map `subschemeι ≫ π`). Its negation gives the inversion morphism. -/
noncomputable def upt : E.Point (D.ideal.subschemeι ≫ E.π) :=
  ⟨D.ideal.subschemeι, rfl⟩

include hD

/-- **(Layer B, L3 core — the group-scheme multiplication exists.)** The sum `bipt₁ + bipt₂` of the
two universal points of `D ×_S D`, taken in the curve group `E.Point (bimulBase)`, factors through
`D` — because both summands factor through `D` and `D(T)` is a subgroup (`IsSubgroup`). This is the
Yoneda input for the multiplication morphism `m : D ×_S D ⟶ D`. -/
theorem exists_factor_bimul :
    ∃ m : pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) ⟶ D.ideal.subscheme,
      m ≫ D.ideal.subschemeι = ((E.bipt₁ (D := D)) + (E.bipt₂ (D := D))).1 := by
  obtain ⟨H, hH⟩ := hD (E.bimulBase (D := D))
  exact (hH _).mp (H.add_mem ((hH _).mpr ⟨pullback.fst _ _, rfl⟩)
    ((hH _).mpr ⟨pullback.snd _ _, rfl⟩))

/-- **(Layer B, L3 core.)** The multiplication morphism `m : D ×_S D ⟶ D.subscheme` of the group
scheme structure on `D.subscheme` induced by `IsSubgroup` (the restriction of the curve group law).
Well-defined up to the mono `subschemeι`; its Hopf-dual `Δ = m^♯` is the comultiplication. -/
noncomputable def subgroupMul :
    pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) ⟶ D.ideal.subscheme :=
  (E.exists_factor_bimul hD).choose

/-- The defining property of `subgroupMul`: composing with `subschemeι` recovers the curve sum of
the two universal points. -/
theorem subgroupMul_subschemeι :
    E.subgroupMul hD ≫ D.ideal.subschemeι = ((E.bipt₁ (D := D)) + (E.bipt₂ (D := D))).1 :=
  (E.exists_factor_bimul hD).choose_spec

open MonoidalCategory CartesianMonoidalCategory MonObj in
/-- **(Layer B, L4 — commutativity of the group-scheme multiplication.)** `swap ≫ m = m`. Proven at
the level of underlying morphisms via `point_add_eq_lift`: `swap` exchanges the two universal points
(`pullbackSymmetry_hom_comp_fst`/`_snd`), and `add_comm` in the point group closes it. No
base-dependent transport. Dualizes to cocommutativity of `Δ` (`IsCocomm`). -/
theorem subgroupMul_comm :
    (Limits.pullbackSymmetry (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)).hom ≫
      E.subgroupMul hD = E.subgroupMul hD := by
  have projfst : ∀ (a b : Over.mk (E.bimulBase (D := D)) ⟶ E.asOver),
      (lift a b).left ≫ pullback.fst E.asOver.hom E.asOver.hom = a.left :=
    fun a b => (Over.comp_left _ _ _ (lift a b) (fst E.asOver E.asOver)).symm.trans
      (congrArg Over.Hom.left (lift_fst a b))
  have projsnd : ∀ (a b : Over.mk (E.bimulBase (D := D)) ⟶ E.asOver),
      (lift a b).left ≫ pullback.snd E.asOver.hom E.asOver.hom = b.left :=
    fun a b => (Over.comp_left _ _ _ (lift a b) (snd E.asOver E.asOver)).symm.trans
      (congrArg Over.Hom.left (lift_snd a b))
  have hswap :
      (Limits.pullbackSymmetry (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)).hom ≫
          (lift (E.pointEquivOverHom (E.bimulBase (D := D)) (E.bipt₁ (D := D)))
            (E.pointEquivOverHom (E.bimulBase (D := D)) (E.bipt₂ (D := D)))).left
        = (lift (E.pointEquivOverHom (E.bimulBase (D := D)) (E.bipt₂ (D := D)))
            (E.pointEquivOverHom (E.bimulBase (D := D)) (E.bipt₁ (D := D)))).left := by
    have hsf : (Limits.pullbackSymmetry (D.ideal.subschemeι ≫ E.π)
          (D.ideal.subschemeι ≫ E.π)).hom ≫ (E.bipt₁ (D := D)).1 = (E.bipt₂ (D := D)).1 := by
      show (Limits.pullbackSymmetry (D.ideal.subschemeι ≫ E.π)
            (D.ideal.subschemeι ≫ E.π)).hom ≫ (pullback.fst (D.ideal.subschemeι ≫ E.π)
            (D.ideal.subschemeι ≫ E.π) ≫ D.ideal.subschemeι)
          = pullback.snd (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) ≫
            D.ideal.subschemeι
      rw [← Category.assoc, Limits.pullbackSymmetry_hom_comp_fst]
    have hss : (Limits.pullbackSymmetry (D.ideal.subschemeι ≫ E.π)
          (D.ideal.subschemeι ≫ E.π)).hom ≫ (E.bipt₂ (D := D)).1 = (E.bipt₁ (D := D)).1 := by
      show (Limits.pullbackSymmetry (D.ideal.subschemeι ≫ E.π)
            (D.ideal.subschemeι ≫ E.π)).hom ≫ (pullback.snd (D.ideal.subschemeι ≫ E.π)
            (D.ideal.subschemeι ≫ E.π) ≫ D.ideal.subschemeι)
          = pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) ≫
            D.ideal.subschemeι
      rw [← Category.assoc, Limits.pullbackSymmetry_hom_comp_snd]
    apply Over.tensorObj_ext
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun m => (Limits.pullbackSymmetry (D.ideal.subschemeι ≫ E.π)
              (D.ideal.subschemeι ≫ E.π)).hom ≫ m)
          (projfst (E.pointEquivOverHom (E.bimulBase (D := D)) (E.bipt₁ (D := D)))
            (E.pointEquivOverHom (E.bimulBase (D := D)) (E.bipt₂ (D := D))))).trans
          (hsf.trans (projfst (E.pointEquivOverHom (E.bimulBase (D := D)) (E.bipt₂ (D := D)))
            (E.pointEquivOverHom (E.bimulBase (D := D)) (E.bipt₁ (D := D)))).symm))
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun m => (Limits.pullbackSymmetry (D.ideal.subschemeι ≫ E.π)
              (D.ideal.subschemeι ≫ E.π)).hom ≫ m)
          (projsnd (E.pointEquivOverHom (E.bimulBase (D := D)) (E.bipt₁ (D := D)))
            (E.pointEquivOverHom (E.bimulBase (D := D)) (E.bipt₂ (D := D))))).trans
          (hss.trans (projsnd (E.pointEquivOverHom (E.bimulBase (D := D)) (E.bipt₂ (D := D)))
            (E.pointEquivOverHom (E.bimulBase (D := D)) (E.bipt₁ (D := D)))).symm))
  rw [← cancel_mono D.ideal.subschemeι, Category.assoc, E.subgroupMul_subschemeι hD]
  refine Eq.trans ?_ (congrArg Subtype.val (add_comm (E.bipt₂ (D := D)) (E.bipt₁ (D := D))))
  rw [E.point_add_eq_lift, E.point_add_eq_lift]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (μ[E.asOver]).left) hswap)

/-- **(Layer B, L3 core — the unit section exists.)** The zero section factors through `D` (it lies
in the subgroup `D(S)`), giving the identity section of the group scheme `D.subscheme`. -/
theorem exists_factor_unit :
    ∃ e : S ⟶ D.ideal.subscheme, e ≫ D.ideal.subschemeι = (0 : E.Point (𝟙 S)).1 := by
  obtain ⟨H, hH⟩ := hD (𝟙 S)
  exact (hH 0).mp H.zero_mem

/-- **(Layer B, L3 core.)** The unit (identity-section) morphism `e : S ⟶ D.subscheme` of the group
scheme structure on `D.subscheme`. Its Hopf-dual is the counit `ε : A →ₐ[R] R`. -/
noncomputable def subgroupUnit : S ⟶ D.ideal.subscheme :=
  (E.exists_factor_unit hD).choose

theorem subgroupUnit_subschemeι :
    E.subgroupUnit hD ≫ D.ideal.subschemeι = (0 : E.Point (𝟙 S)).1 :=
  (E.exists_factor_unit hD).choose_spec

/-- **(Layer B, L3 core — the inversion morphism exists.)** The negation `-upt` of the universal
point of `D.subscheme` factors through `D` (it lies in the subgroup `D(D.subscheme)`), giving the
inversion of the group scheme. -/
theorem exists_factor_inv :
    ∃ n : D.ideal.subscheme ⟶ D.ideal.subscheme,
      n ≫ D.ideal.subschemeι = (-(E.upt (D := D))).1 := by
  obtain ⟨H, hH⟩ := hD (D.ideal.subschemeι ≫ E.π)
  exact (hH _).mp (H.neg_mem ((hH _).mpr ⟨𝟙 _, Category.id_comp _⟩))

/-- **(Layer B, L3 core.)** The inversion morphism `n : D.subscheme ⟶ D.subscheme` of the group
scheme structure on `D.subscheme`. Its Hopf-dual is the antipode `S : A →ₐ[R] A`. -/
noncomputable def subgroupInv : D.ideal.subscheme ⟶ D.ideal.subscheme :=
  (E.exists_factor_inv hD).choose

theorem subgroupInv_subschemeι :
    E.subgroupInv hD ≫ D.ideal.subschemeι = (-(E.upt (D := D))).1 :=
  (E.exists_factor_inv hD).choose_spec

/-- The unit section `e` is a section of the structure map over a general base `S`
(`e ≫ (subschemeι ≫ π) = 𝟙 S`); the zero point lies over `𝟙 S`. -/
theorem subgroupUnit_over :
    E.subgroupUnit hD ≫ (D.ideal.subschemeι ≫ E.π) = 𝟙 S := by
  rw [← Category.assoc, E.subgroupUnit_subschemeι hD]; exact (0 : E.Point (𝟙 S)).2

/-- **(Layer B, L4 — left unit law of the group scheme.)** `(e ×_S id) ≫ m = id`, where
`e ×_S id : D ⟶ D ×_S D` is the cartesian lift `⟨structMap ≫ e, id⟩`. Proven at the point level:
the restriction of the universal sum `bipt₁ + bipt₂` along this lift is `0 + upt = upt` (`bipt₁`
factors through the unit `e`, so restricts to the zero point via `point_zero_val`; `bipt₂` restricts
to `upt`), and `upt.1 = subschemeι`. Dualizes to the left counit law of the coalgebra. -/
theorem subgroupMul_unit_left :
    pullback.lift ((D.ideal.subschemeι ≫ E.π) ≫ E.subgroupUnit hD) (𝟙 _)
        (by rw [Category.assoc, E.subgroupUnit_over hD, Category.comp_id, Category.id_comp])
      ≫ E.subgroupMul hD = 𝟙 D.ideal.subscheme := by
  set uL := pullback.lift ((D.ideal.subschemeι ≫ E.π) ≫ E.subgroupUnit hD) (𝟙 _)
    (by rw [Category.assoc, E.subgroupUnit_over hD, Category.comp_id, Category.id_comp]) with huL
  rw [← cancel_mono D.ideal.subschemeι, Category.assoc, E.subgroupMul_subschemeι hD,
    Category.id_comp]
  have hbase : uL ≫ E.bimulBase (D := D) = D.ideal.subschemeι ≫ E.π := by
    show uL ≫ (pullback.fst _ _ ≫ _) = _
    rw [← Category.assoc, huL, pullback.lift_fst, Category.assoc, E.subgroupUnit_over hD,
      Category.comp_id]
  have key : uL ≫ ((E.bipt₁ (D := D)) + (E.bipt₂ (D := D))).1
      = (Point.restrict E uL ((E.bipt₁ (D := D)) + (E.bipt₂ (D := D)))).1 := rfl
  rw [key, Point.restrict_add]
  have h1 : Point.restrict E uL (E.bipt₁ (D := D))
      = (0 : E.Point (uL ≫ E.bimulBase (D := D))) := by
    apply Subtype.ext
    show uL ≫ (pullback.fst _ _ ≫ D.ideal.subschemeι) = (0 : E.Point (uL ≫ E.bimulBase (D := D))).1
    rw [E.point_zero_val, hbase, ← Category.assoc, huL, pullback.lift_fst, Category.assoc,
      E.subgroupUnit_subschemeι hD, E.point_zero_val, Category.id_comp]
  rw [h1, zero_add]
  show uL ≫ (pullback.snd _ _ ≫ D.ideal.subschemeι) = D.ideal.subschemeι
  rw [← Category.assoc, huL, pullback.lift_snd, Category.id_comp]

/-- **(Layer B, L4 — right unit law of the group scheme.)** `(id ×_S e) ≫ m = id`. Mirror of
`subgroupMul_unit_left` (`bipt₂` factors through the unit, restricting to `0`; `bipt₁` restricts to
`upt`). Dualizes to the right counit law of the coalgebra. -/
theorem subgroupMul_unit_right :
    pullback.lift (𝟙 _) ((D.ideal.subschemeι ≫ E.π) ≫ E.subgroupUnit hD)
        (by rw [Category.id_comp, Category.assoc, E.subgroupUnit_over hD, Category.comp_id])
      ≫ E.subgroupMul hD = 𝟙 D.ideal.subscheme := by
  set uR := pullback.lift (𝟙 _) ((D.ideal.subschemeι ≫ E.π) ≫ E.subgroupUnit hD)
    (by rw [Category.id_comp, Category.assoc, E.subgroupUnit_over hD, Category.comp_id]) with huR
  rw [← cancel_mono D.ideal.subschemeι, Category.assoc, E.subgroupMul_subschemeι hD,
    Category.id_comp]
  have hbase : uR ≫ E.bimulBase (D := D) = D.ideal.subschemeι ≫ E.π := by
    show uR ≫ (pullback.fst _ _ ≫ _) = _
    rw [← Category.assoc, huR, pullback.lift_fst, Category.id_comp]
  have key : uR ≫ ((E.bipt₁ (D := D)) + (E.bipt₂ (D := D))).1
      = (Point.restrict E uR ((E.bipt₁ (D := D)) + (E.bipt₂ (D := D)))).1 := rfl
  rw [key, Point.restrict_add]
  have h2 : Point.restrict E uR (E.bipt₂ (D := D))
      = (0 : E.Point (uR ≫ E.bimulBase (D := D))) := by
    apply Subtype.ext
    show uR ≫ (pullback.snd _ _ ≫ D.ideal.subschemeι) = (0 : E.Point (uR ≫ E.bimulBase (D := D))).1
    rw [E.point_zero_val, hbase, ← Category.assoc, huR, pullback.lift_snd, Category.assoc,
      E.subgroupUnit_subschemeι hD, E.point_zero_val, Category.id_comp]
  rw [h2, add_zero]
  show uR ≫ (pullback.fst _ _ ≫ D.ideal.subschemeι) = D.ideal.subschemeι
  rw [← Category.assoc, huR, pullback.lift_fst, Category.id_comp]

/-- The inversion `n` is a morphism over the base for a general `S`
(`n ≫ (subschemeι ≫ π) = subschemeι ≫ π`); `-upt` lies over the same base map as `upt`. -/
theorem subgroupInv_over :
    E.subgroupInv hD ≫ (D.ideal.subschemeι ≫ E.π) = D.ideal.subschemeι ≫ E.π := by
  rw [← Category.assoc, E.subgroupInv_subschemeι hD]; exact (-(E.upt (D := D))).2

/-- **(Layer B, L4 — inverse law of the group scheme.)** `⟨n, id⟩ ≫ m = structMap ≫ e`, the
"multiply by the inverse gives the unit" law. Proven at the point level: the restriction of
`bipt₁ + bipt₂` along `⟨n, id⟩` is `(-upt) + upt = 0` (`bipt₁` restricts through `n` to `-upt`
via `subgroupInv_subschemeι` + `point_neg_val`, `bipt₂` to `upt`; `neg_add_cancel`), and
`0.1 = structMap ≫ E.zero`. Dualizes to the antipode law of the Hopf algebra. -/
theorem subgroupMul_inv :
    pullback.lift (E.subgroupInv hD) (𝟙 _)
        (by rw [Category.id_comp]; exact E.subgroupInv_over hD)
      ≫ E.subgroupMul hD = (D.ideal.subschemeι ≫ E.π) ≫ E.subgroupUnit hD := by
  set uV : D.ideal.subscheme ⟶ pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) :=
    pullback.lift (E.subgroupInv hD) (𝟙 _)
      (by rw [Category.id_comp]; exact E.subgroupInv_over hD) with huV
  rw [← cancel_mono D.ideal.subschemeι, Category.assoc, E.subgroupMul_subschemeι hD,
    Category.assoc, E.subgroupUnit_subschemeι hD, E.point_zero_val, Category.id_comp]
  have hbase : uV ≫ E.bimulBase (D := D) = D.ideal.subschemeι ≫ E.π := by
    show uV ≫ (pullback.fst _ _ ≫ _) = _
    rw [← Category.assoc, huV, pullback.lift_fst, E.subgroupInv_over hD]
  have key : uV ≫ ((E.bipt₁ (D := D)) + (E.bipt₂ (D := D))).1
      = (Point.restrict E uV ((E.bipt₁ (D := D)) + (E.bipt₂ (D := D)))).1 := rfl
  rw [key, Point.restrict_add]
  have hinv : Point.restrict E uV (E.bipt₁ (D := D))
      = -(Point.restrict E uV (E.bipt₂ (D := D))) := by
    apply Subtype.ext
    rw [E.point_neg_val]
    show uV ≫ (pullback.fst _ _ ≫ D.ideal.subschemeι)
      = (uV ≫ (pullback.snd _ _ ≫ D.ideal.subschemeι)) ≫ E.mulByHom (-1)
    rw [← Category.assoc, huV, pullback.lift_fst, E.subgroupInv_subschemeι hD, ← Category.assoc,
      pullback.lift_snd, Category.id_comp, E.point_neg_val]
    rfl
  rw [hinv, neg_add_cancel]
  show ((0 : E.Point (uV ≫ E.bimulBase (D := D)))).1 = (D.ideal.subschemeι ≫ E.π) ≫ E.zero
  rw [E.point_zero_val, hbase]

/-- **(Layer B, L4 — right inverse axiom.)** `⟨id, n⟩ ≫ m = (subschemeι ≫ π) ≫ e`: the leg-swapped
mirror of `subgroupMul_inv` (`upt + (-upt) = 0`). Dualizes to the right antipode law
(`mul' ∘ (id ⊗ S) ∘ Δ = η ∘ ε`). -/
theorem subgroupMul_inv' :
    pullback.lift (𝟙 _) (E.subgroupInv hD)
        (by rw [Category.id_comp]; exact (E.subgroupInv_over hD).symm)
      ≫ E.subgroupMul hD = (D.ideal.subschemeι ≫ E.π) ≫ E.subgroupUnit hD := by
  set uV : D.ideal.subscheme ⟶ pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) :=
    pullback.lift (𝟙 _) (E.subgroupInv hD)
      (by rw [Category.id_comp]; exact (E.subgroupInv_over hD).symm) with huV
  rw [← cancel_mono D.ideal.subschemeι, Category.assoc, E.subgroupMul_subschemeι hD,
    Category.assoc, E.subgroupUnit_subschemeι hD, E.point_zero_val, Category.id_comp]
  have hbase : uV ≫ E.bimulBase (D := D) = D.ideal.subschemeι ≫ E.π := by
    show uV ≫ (pullback.fst _ _ ≫ _) = _
    rw [← Category.assoc, huV, pullback.lift_fst, Category.id_comp]
  have key : uV ≫ ((E.bipt₁ (D := D)) + (E.bipt₂ (D := D))).1
      = (Point.restrict E uV ((E.bipt₁ (D := D)) + (E.bipt₂ (D := D)))).1 := rfl
  rw [key, Point.restrict_add]
  have hinv : Point.restrict E uV (E.bipt₂ (D := D))
      = -(Point.restrict E uV (E.bipt₁ (D := D))) := by
    apply Subtype.ext
    rw [E.point_neg_val]
    show uV ≫ (pullback.snd _ _ ≫ D.ideal.subschemeι)
      = (uV ≫ (pullback.fst _ _ ≫ D.ideal.subschemeι)) ≫ E.mulByHom (-1)
    rw [← Category.assoc, huV, pullback.lift_snd, E.subgroupInv_subschemeι hD, ← Category.assoc,
      pullback.lift_fst, Category.id_comp, E.point_neg_val]
    rfl
  rw [hinv, add_neg_cancel]
  show ((0 : E.Point (uV ≫ E.bimulBase (D := D)))).1 = (D.ideal.subschemeι ≫ E.π) ≫ E.zero
  rw [E.point_zero_val, hbase]

end GroupObject

section PairCompare

/-! ### General coordinate-ring comparison for a pair of affine schemes

For any two affine schemes `X`, `Y` over `Spec R` (with chosen structure maps `qX`, `qY`), the
canonical map `Γ(X) ⊗_R Γ(Y) → Γ(X ×ₛ Y)` is an `R`-algebra isomorphism — the coordinate-ring
incarnation of `pullbackSpecIso`. This is the reusable engine behind `κ` (the case `X = Y =
D.subscheme`) and behind the triple comparison `κ_DP` (the case `X = D.subscheme`, `Y = D ×ₛ D`)
used to dualize associativity into coassociativity. -/

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
  (qX : X ⟶ Spec (CommRingCat.of R)) (qY : Y ⟶ Spec (CommRingCat.of R))

/-- Algebra structure on `Γ(X)` for an affine `X` with a chosen structure map to `Spec R`. -/
noncomputable def schemeAlg : Algebra R Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ qX.appTop).hom.toAlgebra

/-- Base structure map of the pullback `X ×ₛ Y`. -/
noncomputable abbrev pairBase : pullback qX qY ⟶ Spec (CommRingCat.of R) :=
  pullback.fst qX qY ≫ qX

/-- The general kbase: `Spec.map (algebraMap R Γ(X)) = X.isoSpec.inv ≫ qX`. -/
theorem schemeSpecAlgebraMap_eq :
    letI := schemeAlg (R := R) qX
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤))) = X.isoSpec.inv ≫ qX := by
  letI := schemeAlg (R := R) qX
  have hnat := Scheme.isoSpec_inv_naturality qX
  rw [Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at hnat
  have hAM : CommRingCat.ofHom (algebraMap R Γ(X, ⊤))
      = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ qX.appTop :=
    CommRingCat.ofHom_hom _
  rw [hAM]; exact hnat

/-- First coordinate projection `Γ(X) →ₐ Γ(X ×ₛ Y)`, i.e. `Γ(fst)`. -/
noncomputable def pairProj₁ :
    letI := schemeAlg (R := R) qX
    letI : Algebra R Γ(pullback qX qY, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pairBase qX qY).appTop).hom.toAlgebra
    Γ(X, ⊤) →ₐ[R] Γ(pullback qX qY, ⊤) :=
  letI := schemeAlg (R := R) qX
  letI : Algebra R Γ(pullback qX qY, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pairBase qX qY).appTop).hom.toAlgebra
  { (pullback.fst qX qY).appTop.hom with
    commutes' := fun r => by
      have hcomp :
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ qX.appTop) ≫
            (pullback.fst qX qY).appTop =
            (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pairBase qX qY).appTop := by
        rw [Category.assoc, ← Scheme.Hom.comp_appTop]
      show (pullback.fst qX qY).appTop.hom
          (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ qX.appTop).hom r) =
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pairBase qX qY).appTop).hom r
      rw [← CommRingCat.comp_apply, hcomp] }

/-- Second coordinate projection `Γ(Y) →ₐ Γ(X ×ₛ Y)`, i.e. `Γ(snd)`. -/
noncomputable def pairProj₂ :
    letI := schemeAlg (R := R) qY
    letI : Algebra R Γ(pullback qX qY, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pairBase qX qY).appTop).hom.toAlgebra
    Γ(Y, ⊤) →ₐ[R] Γ(pullback qX qY, ⊤) :=
  letI := schemeAlg (R := R) qY
  letI : Algebra R Γ(pullback qX qY, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pairBase qX qY).appTop).hom.toAlgebra
  { (pullback.snd qX qY).appTop.hom with
    commutes' := fun r => by
      have hbase2 : pairBase qX qY = pullback.snd qX qY ≫ qY := pullback.condition
      have hcomp :
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ qY.appTop) ≫
            (pullback.snd qX qY).appTop =
            (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pairBase qX qY).appTop := by
        rw [Category.assoc, ← Scheme.Hom.comp_appTop, ← hbase2]
      show (pullback.snd qX qY).appTop.hom
          (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ qY.appTop).hom r) =
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pairBase qX qY).appTop).hom r
      rw [← CommRingCat.comp_apply, hcomp] }

/-- The general tensor comparison `Γ(X) ⊗_R Γ(Y) →ₐ Γ(X ×ₛ Y)`. -/
noncomputable def pairTensorCompare :
    letI := schemeAlg (R := R) qX
    letI := schemeAlg (R := R) qY
    letI : Algebra R Γ(pullback qX qY, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pairBase qX qY).appTop).hom.toAlgebra
    TensorProduct R Γ(X, ⊤) Γ(Y, ⊤) →ₐ[R] Γ(pullback qX qY, ⊤) :=
  letI := schemeAlg (R := R) qX
  letI := schemeAlg (R := R) qY
  letI : Algebra R Γ(pullback qX qY, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pairBase qX qY).appTop).hom.toAlgebra
  Algebra.TensorProduct.lift (pairProj₁ qX qY) (pairProj₂ qX qY) (fun _ _ => Commute.all _ _)

/-- `pairTensorCompare qX qY (a ⊗ b) = Γ(fst) a · Γ(snd) b`. -/
theorem pairTensorCompare_tmul :
    letI := schemeAlg (R := R) qX
    letI := schemeAlg (R := R) qY
    letI : Algebra R Γ(pullback qX qY, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pairBase qX qY).appTop).hom.toAlgebra
    ∀ (a : Γ(X, ⊤)) (b : Γ(Y, ⊤)),
      pairTensorCompare qX qY (a ⊗ₜ[R] b) = pairProj₁ qX qY a * pairProj₂ qX qY b := by
  letI := schemeAlg (R := R) qX
  letI := schemeAlg (R := R) qY
  letI : Algebra R Γ(pullback qX qY, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pairBase qX qY).appTop).hom.toAlgebra
  intro a b
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- **(Layer B, reusable comparison.)** The pair comparison `Γ(X) ⊗_R Γ(Y) → Γ(X ×ₛ Y)` is
bijective:
it becomes an iso after `Spec`, via `pullbackSpecIso` and `isoSpec`, reflected back through the
fully
faithful `Spec`. -/
theorem pairTensorCompare_bijective :
    letI := schemeAlg (R := R) qX
    letI := schemeAlg (R := R) qY
    letI : Algebra R Γ(pullback qX qY, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pairBase qX qY).appTop).hom.toAlgebra
    Function.Bijective (pairTensorCompare qX qY) := by
  letI := schemeAlg (R := R) qX
  letI := schemeAlg (R := R) qY
  letI : Algebra R Γ(pullback qX qY, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pairBase qX qY).appTop).hom.toAlgebra
  haveI : IsAffine (pullback qX qY) := by
    haveI : IsAffineHom (pullback.fst qX qY) := MorphismProperty.pullback_fst _ _ inferInstance
    exact isAffine_of_isAffineHom (pullback.fst qX qY)
  have hbaseX : Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤))) = X.isoSpec.inv ≫ qX :=
    schemeSpecAlgebraMap_eq qX
  have hbaseY : Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y, ⊤))) = Y.isoSpec.inv ≫ qY :=
    schemeSpecAlgebraMap_eq qY
  have eX : Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤))) ≫ 𝟙 (Spec (CommRingCat.of R))
      = X.isoSpec.inv ≫ qX := (Category.comp_id _).trans hbaseX
  have eY : Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y, ⊤))) ≫ 𝟙 (Spec (CommRingCat.of R))
      = Y.isoSpec.inv ≫ qY := (Category.comp_id _).trans hbaseY
  set ρ := asIso (pullback.map
      (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, ⊤))))
      (Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y, ⊤))))
      qX qY X.isoSpec.inv Y.isoSpec.inv (𝟙 _) eX eY) with hρ
  set κ := pairTensorCompare qX qY with hκ
  have hL : κ.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom
      = (pairProj₁ qX qY).toRingHom :=
    congrArg AlgHom.toRingHom (Algebra.TensorProduct.lift_comp_includeLeft
      (pairProj₁ qX qY) (pairProj₂ qX qY) (fun _ _ => Commute.all _ _))
  have hR : κ.toRingHom.comp (Algebra.TensorProduct.includeRight).toRingHom
      = (pairProj₂ qX qY).toRingHom :=
    congrArg AlgHom.toRingHom (Algebra.TensorProduct.lift_comp_includeRight
      (pairProj₁ qX qY) (pairProj₂ qX qY) (fun _ _ => Commute.all _ _))
  set pbS := pullbackSpecIso R Γ(X, ⊤) Γ(Y, ⊤) with hpbS
  have key : ((ρ.hom ≫ (pullback qX qY).isoSpec.hom)
        ≫ Spec.map (CommRingCat.ofHom κ.toRingHom)) ≫ pbS.inv = 𝟙 _ := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hpbS, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hL,
        show CommRingCat.ofHom (pairProj₁ qX qY).toRingHom
          = (pullback.fst qX qY).appTop from CommRingCat.ofHom_hom _,
        Scheme.isoSpec_hom_naturality, hρ, asIso_hom]
      rw [← Category.assoc]
      erw [pullback.lift_fst]
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc]
      rw [hpbS, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      erw [hR]
      rw [show CommRingCat.ofHom (pairProj₂ qX qY).toRingHom
          = (pullback.snd qX qY).appTop from CommRingCat.ofHom_hom _,
        Scheme.isoSpec_hom_naturality, hρ, asIso_hom]
      rw [← Category.assoc]
      erw [pullback.lift_snd]
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  have hstar : (ρ.hom ≫ (pullback qX qY).isoSpec.hom)
        ≫ Spec.map (CommRingCat.ofHom κ.toRingHom) = pbS.hom := by
    have h := (Iso.comp_inv_eq pbS).mp key
    rwa [Category.id_comp] at h
  haveI hg : IsIso (ρ.hom ≫ (pullback qX qY).isoSpec.hom) := inferInstance
  haveI hcomp : IsIso ((ρ.hom ≫ (pullback qX qY).isoSpec.hom)
      ≫ Spec.map (CommRingCat.ofHom κ.toRingHom)) := by rw [hstar]; infer_instance
  haveI hiso : IsIso (Spec.map (CommRingCat.ofHom κ.toRingHom)) :=
    IsIso.of_isIso_comp_left (ρ.hom ≫ (pullback qX qY).isoSpec.hom)
      (Spec.map (CommRingCat.ofHom κ.toRingHom))
  haveI : IsIso (Scheme.Spec.map (CommRingCat.ofHom κ.toRingHom).op) :=
    inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom κ.toRingHom)))
  have hringiso : IsIso (CommRingCat.ofHom κ.toRingHom) :=
    (isIso_op_iff _).mp (Spec.fullyFaithful.isIso_of_isIso_map (CommRingCat.ofHom κ.toRingHom).op)
  exact (ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom κ.toRingHom)).mp hringiso

end PairCompare

section AffineHopf

variable {R : Type u} [CommRing R] (E : EllipticCurve (Spec (CommRingCat.of R)))
  {D : RelEffCartierDiv E.π}

/-- The `R`-algebra structure on `Γ(D ×_{Spec R} D, ⊤)` induced by the base map `bimulBase`
(mirrors `subgroupAlgebra`). The tensor comparison `A ⊗_R A ≅ Γ(D ×_R D)` below is an `R`-algebra
iso for this structure; it is the coordinate-ring incarnation of `pullbackSpecIso`. -/
noncomputable def biproductAlgebra :
    Algebra R Γ(pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π), ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop).hom.toAlgebra

set_option backward.isDefEq.respectTransparency.types false in
/-- **(Layer B, κ-bijectivity foundation.)** `D ×_{Spec R} D` is affine: `D.subscheme` is finite —
hence affine — over `Spec R`, so both projections are affine morphisms and the fibre product of
affines over an affine base is affine. This is what makes `Γ(D ×_R D)` a genuine coordinate ring and
`κ : A ⊗_R A → Γ(D ×_R D)` an isomorphism (`pullbackSpecIso`). -/
theorem subgroupBiproduct_isAffine :
    IsAffine (pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)) := by
  haveI : IsFinite (E.subgroupStructMap D) := D.finite
  haveI : IsAffine D.ideal.subscheme := isAffine_of_isAffineHom (E.subgroupStructMap D)
  haveI : IsAffineHom (Limits.pullback.fst (D.ideal.subschemeι ≫ E.π)
      (D.ideal.subschemeι ≫ E.π)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  exact isAffine_of_isAffineHom
    (Limits.pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π))

/-- `bimulBase` is the first projection followed by the structure map (by definition, up to
associativity). -/
theorem bimulBase_eq_fst_structMap :
    E.bimulBase (D := D) =
      Limits.pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) ≫
        E.subgroupStructMap D :=
  (Category.assoc _ _ _).symm

/-- `bimulBase` is also the second projection followed by the structure map (pullback condition). -/
theorem bimulBase_eq_snd_structMap :
    E.bimulBase (D := D) =
      Limits.pullback.snd (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) ≫
        E.subgroupStructMap D := by
  rw [bimulBase_eq_fst_structMap]
  exact Limits.pullback.condition

/-- The first coordinate projection `A →ₐ[R] Γ(D ×_R D)`, i.e. `Γ(pullback.fst)`. It is an
`R`-algebra map because `fst ≫ structMap = bimulBase` (`bimulBase_eq_fst_structMap`). -/
noncomputable def subgroupProj₁ :
    letI := E.subgroupAlgebra D
    letI := E.biproductAlgebra (D := D)
    Γ(D.ideal.subscheme, ⊤) →ₐ[R]
      Γ(pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π), ⊤) :=
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  { (Limits.pullback.fst (D.ideal.subschemeι ≫ E.π)
      (D.ideal.subschemeι ≫ E.π)).appTop.hom with
    commutes' := fun r => by
      have hcomp :
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop) ≫
            (Limits.pullback.fst (D.ideal.subschemeι ≫ E.π)
              (D.ideal.subschemeι ≫ E.π)).appTop =
            (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop := by
        rw [Category.assoc, ← Scheme.Hom.comp_appTop, ← bimulBase_eq_fst_structMap]
      show (Limits.pullback.fst (D.ideal.subschemeι ≫ E.π)
            (D.ideal.subschemeι ≫ E.π)).appTop.hom
          (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom r) =
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop).hom r
      rw [← CommRingCat.comp_apply, hcomp] }

/-- The second coordinate projection `A →ₐ[R] Γ(D ×_R D)`, i.e. `Γ(pullback.snd)`. -/
noncomputable def subgroupProj₂ :
    letI := E.subgroupAlgebra D
    letI := E.biproductAlgebra (D := D)
    Γ(D.ideal.subscheme, ⊤) →ₐ[R]
      Γ(pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π), ⊤) :=
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  { (Limits.pullback.snd (D.ideal.subschemeι ≫ E.π)
      (D.ideal.subschemeι ≫ E.π)).appTop.hom with
    commutes' := fun r => by
      have hcomp :
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop) ≫
            (Limits.pullback.snd (D.ideal.subschemeι ≫ E.π)
              (D.ideal.subschemeι ≫ E.π)).appTop =
            (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop := by
        rw [Category.assoc, ← Scheme.Hom.comp_appTop, ← bimulBase_eq_snd_structMap]
      show (Limits.pullback.snd (D.ideal.subschemeι ≫ E.π)
            (D.ideal.subschemeι ≫ E.π)).appTop.hom
          (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom r) =
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop).hom r
      rw [← CommRingCat.comp_apply, hcomp] }

/-- The tensor comparison `κ : A ⊗_R A →ₐ[R] Γ(D ×_R D)`, `κ = ⟨Γ(fst), Γ(snd)⟩` — the
coordinate-ring incarnation of the canonical map `Spec Γ(D ×_R D) ⟶ Spec A ×_{Spec R} Spec A`. It
is an isomorphism (`pullbackSpecIso` transported across `D.subscheme.isoSpec` on each factor); its
inverse composed with `Γ(m)` is the comultiplication. -/
noncomputable def subgroupTensorCompare :
    letI := E.subgroupAlgebra D
    letI := E.biproductAlgebra (D := D)
    TensorProduct R Γ(D.ideal.subscheme, ⊤) Γ(D.ideal.subscheme, ⊤) →ₐ[R]
      Γ(pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π), ⊤) :=
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  Algebra.TensorProduct.lift (E.subgroupProj₁ (D := D)) (E.subgroupProj₂ (D := D))
    (fun _ _ => Commute.all _ _)

/-- **(Layer B, κ-bijectivity — base compatibility.)** Under the affine identification
`D.subscheme ≅ Spec A` (`isoSpec`, `A = Γ(D.subscheme, ⊤)`), the structure map
`q = subschemeι ≫ π : D.subscheme ⟶ Spec R` becomes `Spec.map` of the `R`-algebra structure map
`R → A`. This is `isoSpec` inverse-naturality composed with `Spec (ΓSpecIso)⁻¹` on the affine base.
It is what lets `pullbackSpecIso R A A` be transported onto `D ×_R D` (isomorphic cospans). -/
theorem subgroupSpecAlgebraMap_eq :
    letI := E.subgroupAlgebra D
    haveI : IsFinite (E.subgroupStructMap D) := D.finite
    haveI : IsAffine D.ideal.subscheme := isAffine_of_isAffineHom (E.subgroupStructMap D)
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(D.ideal.subscheme, ⊤)))
      = D.ideal.subscheme.isoSpec.inv ≫ D.ideal.subschemeι ≫ E.π := by
  letI := E.subgroupAlgebra D
  haveI : IsFinite (E.subgroupStructMap D) := D.finite
  haveI : IsAffine D.ideal.subscheme := isAffine_of_isAffineHom (E.subgroupStructMap D)
  have hnat := Scheme.isoSpec_inv_naturality (E.subgroupStructMap D)
  rw [Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at hnat
  have hAM : CommRingCat.ofHom (algebraMap R Γ(D.ideal.subscheme, ⊤))
      = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop :=
    CommRingCat.ofHom_hom _
  rw [hAM]; exact hnat

/-- **`[T-D5h-κbij]` — DISCHARGED.** The tensor comparison
`κ = ⟨Γ(fst), Γ(snd)⟩ : A ⊗_R A →ₐ[R] Γ(D ×_R D)` is bijective. Route: `κ` is `Γ` of the canonical
scheme iso `Spec(A ⊗_R A) ≅ D ×_R D` got by transporting `pullbackSpecIso R A A` across
`D.subscheme.isoSpec` on each factor (base compatibility: `subgroupSpecAlgebraMap_eq`; both factors
affine as `D.subscheme` is finite over `Spec R`). Concretely `Spec.map κ` is shown equal to a
composite of isos `isoSpec.inv ≫ ρ.inv ≫ pullbackSpecIso.hom` via a `pullback.hom_ext` matching
`κ ∘ includeLeft/Right = Γ(fst)/Γ(snd)` (`lift_comp_includeLeft/Right`); bijectivity then follows by
reflecting `IsIso` through the fully faithful `Spec`. The sole genuinely-heavy leaf under `Δ`. -/
theorem subgroupTensorCompare_bijective :
    letI := E.subgroupAlgebra D
    letI := E.biproductAlgebra (D := D)
    Function.Bijective (E.subgroupTensorCompare (D := D)) := by
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  haveI : IsFinite (E.subgroupStructMap D) := D.finite
  haveI : IsAffine D.ideal.subscheme := isAffine_of_isAffineHom (E.subgroupStructMap D)
  haveI : IsAffine (pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)) :=
    E.subgroupBiproduct_isAffine (D := D)
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap R Γ(D.ideal.subscheme, ⊤)))
      = D.ideal.subscheme.isoSpec.inv ≫ D.ideal.subschemeι ≫ E.π :=
    E.subgroupSpecAlgebraMap_eq (D := D)
  have e₁ : Spec.map (CommRingCat.ofHom (algebraMap R Γ(D.ideal.subscheme, ⊤)))
        ≫ 𝟙 (Spec (CommRingCat.of R)) =
      D.ideal.subscheme.isoSpec.inv ≫ (D.ideal.subschemeι ≫ E.π) :=
    (Category.comp_id _).trans hbase
  set ρ := asIso (pullback.map
      (Spec.map (CommRingCat.ofHom (algebraMap R Γ(D.ideal.subscheme, ⊤))))
      (Spec.map (CommRingCat.ofHom (algebraMap R Γ(D.ideal.subscheme, ⊤))))
      (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)
      D.ideal.subscheme.isoSpec.inv D.ideal.subscheme.isoSpec.inv (𝟙 _) e₁ e₁) with hρ
  set κ := E.subgroupTensorCompare (D := D) with hκ
  have hL : κ.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom
      = (E.subgroupProj₁ (D := D)).toRingHom :=
    congrArg AlgHom.toRingHom (Algebra.TensorProduct.lift_comp_includeLeft
      (E.subgroupProj₁ (D := D)) (E.subgroupProj₂ (D := D)) (fun _ _ => Commute.all _ _))
  have hR : κ.toRingHom.comp (Algebra.TensorProduct.includeRight).toRingHom
      = (E.subgroupProj₂ (D := D)).toRingHom :=
    congrArg AlgHom.toRingHom (Algebra.TensorProduct.lift_comp_includeRight
      (E.subgroupProj₁ (D := D)) (E.subgroupProj₂ (D := D)) (fun _ _ => Commute.all _ _))
  set pbS := pullbackSpecIso R Γ(D.ideal.subscheme, ⊤) Γ(D.ideal.subscheme, ⊤) with hpbS
  -- `(ρ ≫ isoSpec) ≫ Spec.map κ`, composed with `pbS.inv`, is the identity of the tensor pullback.
  have key : ((ρ.hom ≫ (pullback (D.ideal.subschemeι ≫ E.π)
        (D.ideal.subschemeι ≫ E.π)).isoSpec.hom)
        ≫ Spec.map (CommRingCat.ofHom κ.toRingHom)) ≫ pbS.inv = 𝟙 _ := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hpbS, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hL,
        show CommRingCat.ofHom (E.subgroupProj₁ (D := D)).toRingHom
          = (pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)).appTop from
          CommRingCat.ofHom_hom _, Scheme.isoSpec_hom_naturality, hρ, asIso_hom]
      rw [← Category.assoc]
      erw [pullback.lift_fst]
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc]
      rw [hpbS, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      erw [hR]
      rw [show CommRingCat.ofHom (E.subgroupProj₂ (D := D)).toRingHom
          = (pullback.snd (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)).appTop from
          CommRingCat.ofHom_hom _, Scheme.isoSpec_hom_naturality, hρ, asIso_hom]
      rw [← Category.assoc]
      erw [pullback.lift_snd]
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  have hstar : (ρ.hom ≫ (pullback (D.ideal.subschemeι ≫ E.π)
        (D.ideal.subschemeι ≫ E.π)).isoSpec.hom)
        ≫ Spec.map (CommRingCat.ofHom κ.toRingHom) = pbS.hom := by
    have h := (Iso.comp_inv_eq pbS).mp key
    rwa [Category.id_comp] at h
  haveI hg : IsIso (ρ.hom ≫ (pullback (D.ideal.subschemeι ≫ E.π)
      (D.ideal.subschemeι ≫ E.π)).isoSpec.hom) := inferInstance
  haveI hcomp : IsIso ((ρ.hom ≫ (pullback (D.ideal.subschemeι ≫ E.π)
      (D.ideal.subschemeι ≫ E.π)).isoSpec.hom) ≫ Spec.map (CommRingCat.ofHom κ.toRingHom)) := by
    rw [hstar]; infer_instance
  haveI hiso : IsIso (Spec.map (CommRingCat.ofHom κ.toRingHom)) :=
    IsIso.of_isIso_comp_left (ρ.hom ≫ (pullback (D.ideal.subschemeι ≫ E.π)
      (D.ideal.subschemeι ≫ E.π)).isoSpec.hom) (Spec.map (CommRingCat.ofHom κ.toRingHom))
  haveI : IsIso (Scheme.Spec.map (CommRingCat.ofHom κ.toRingHom).op) :=
    inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom κ.toRingHom)))
  have hringiso : IsIso (CommRingCat.ofHom κ.toRingHom) :=
    (isIso_op_iff _).mp (Spec.fullyFaithful.isIso_of_isIso_map (CommRingCat.ofHom κ.toRingHom).op)
  exact (ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom κ.toRingHom)).mp hringiso

/-- The multiplication is a morphism over the base: `m ≫ structMap = bimulBase` (dualizing to the
`R`-linearity of `Γ(m)`). -/
theorem subgroupMul_structMap (hD : D.IsSubgroup E) :
    E.subgroupMul hD ≫ E.subgroupStructMap D = E.bimulBase (D := D) := by
  show E.subgroupMul hD ≫ (D.ideal.subschemeι ≫ E.π) = E.bimulBase (D := D)
  rw [← Category.assoc, E.subgroupMul_subschemeι hD]
  exact ((E.bipt₁ (D := D)) + (E.bipt₂ (D := D))).2

/- **(Layer B, L4 — scheme associativity toward coassoc.)** Triple-pullback multiplication maps
`v`, `v'` (right/left associated) and `subgroupMul_assoc : v' ≫ m = v ≫ m`, with `Point`
base-transport
helpers to invoke `add_assoc` across the reassociation. Dualizes to `Coalgebra.coassoc`. -/
/-- base-congruence for points: transport preserves the underlying morphism. -/
theorem Point.base_congr {T : Scheme.{u}} {g g' : T ⟶ Spec (CommRingCat.of R)} (h : g = g')
    (P : E.Point g) : (h ▸ P : E.Point g').1 = P.1 := by subst h; rfl

/-- base transport is additive. -/
theorem Point.base_congr_add {T : Scheme.{u}} {g g' : T ⟶ Spec (CommRingCat.of R)} (h : g = g')
    (P Q : E.Point g) : (h ▸ (P + Q) : E.Point g') = (h ▸ P) + (h ▸ Q) := by subst h; rfl

/-- Transported restriction of a universal point is identified by its underlying morphism. -/
theorem Point.restrictT_eq {T T' : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of R)} {k : T' ⟶ T}
    {g' : T' ⟶ Spec (CommRingCat.of R)} (h : k ≫ g = g') (P : E.Point g) (Q : E.Point g')
    (hPQ : k ≫ P.1 = Q.1) : (h ▸ Point.restrict E k P : E.Point g') = Q :=
  Subtype.ext ((Point.base_congr (E := E) h (Point.restrict E k P)).trans hPQ)

-- v : P₃ → P₂,  ⟨fst₃, snd₃ ≫ m⟩
noncomputable def vmap (hD : D.IsSubgroup E) :
    pullback (E.subgroupStructMap D) (E.bimulBase (D := D)) ⟶
    pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) :=
  pullback.lift (pullback.fst (E.subgroupStructMap D) (E.bimulBase (D := D)))
    (pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D)) ≫ E.subgroupMul hD)
    (by
      rw [Category.assoc, E.subgroupMul_structMap hD]
      exact pullback.condition (f := E.subgroupStructMap D) (g := E.bimulBase (D := D)))

-- u : P₃ → P₂,  ⟨fst₃, snd₃ ≫ fst₂⟩
noncomputable def umap : pullback (E.subgroupStructMap D) (E.bimulBase (D := D)) ⟶
    pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) :=
  pullback.lift (pullback.fst (E.subgroupStructMap D) (E.bimulBase (D := D)))
    (pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D)) ≫
      pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π))
    (by
      rw [Category.assoc, ← Category.assoc (pullback.fst _ _), ← E.bimulBase_eq_fst_structMap]
      exact pullback.condition (f := E.subgroupStructMap D) (g := E.bimulBase (D := D)))

-- v' : P₃ → P₂,  ⟨u ≫ m, snd₃ ≫ snd₂⟩
noncomputable def vmap' (hD : D.IsSubgroup E) :
    pullback (E.subgroupStructMap D) (E.bimulBase (D := D)) ⟶
    pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) :=
  pullback.lift (E.umap (D := D) ≫ E.subgroupMul hD)
    (pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D)) ≫
      pullback.snd (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π))
    (by
      have e1 : (E.umap (D := D) ≫ E.subgroupMul hD) ≫ (D.ideal.subschemeι ≫ E.π)
          = pullback.fst (E.subgroupStructMap D) (E.bimulBase (D := D)) ≫
            E.subgroupStructMap D := by
        rw [Category.assoc, E.subgroupMul_structMap hD]
        show E.umap (D := D) ≫ (pullback.fst (D.ideal.subschemeι ≫ E.π)
            (D.ideal.subschemeι ≫ E.π) ≫ (D.ideal.subschemeι ≫ E.π)) = _
        rw [← Category.assoc, umap, pullback.lift_fst]
      have e2 : (pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D)) ≫
            pullback.snd (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π))
            ≫ (D.ideal.subschemeι ≫ E.π)
          = pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D)) ≫ E.bimulBase (D := D) := by
        simp only [Category.assoc]; rw [← E.bimulBase_eq_snd_structMap]
      rw [e1, e2]
      exact pullback.condition (f := E.subgroupStructMap D) (g := E.bimulBase (D := D)))

/-- Transported restriction of the universal sum splits as a sum of the identified points. -/
theorem Point.restrictT_add_eq {T' : Scheme.{u}}
    (k : T' ⟶ pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π))
    {g' : T' ⟶ Spec (CommRingCat.of R)} (h : k ≫ E.bimulBase (D := D) = g')
    (P Q : E.Point g') (hP : k ≫ (E.bipt₁ (D := D)).1 = P.1)
    (hQ : k ≫ (E.bipt₂ (D := D)).1 = Q.1) :
    (h ▸ Point.restrict E k (E.bipt₁ (D := D) + E.bipt₂ (D := D)) : E.Point g') = P + Q := by
  rw [Point.restrict_add, Point.base_congr_add,
    Point.restrictT_eq (E := E) h (E.bipt₁ (D := D)) P hP,
    Point.restrictT_eq (E := E) h (E.bipt₂ (D := D)) Q hQ]

noncomputable def tpt₁ :
    E.Point (pullback.fst (E.subgroupStructMap D) (E.bimulBase (D := D)) ≫ E.subgroupStructMap D) :=
  ⟨pullback.fst (E.subgroupStructMap D) (E.bimulBase (D := D)) ≫ D.ideal.subschemeι, by
    rw [Category.assoc]⟩

noncomputable def tpt₂ :
    E.Point (pullback.fst (E.subgroupStructMap D) (E.bimulBase (D := D)) ≫ E.subgroupStructMap D) :=
  ⟨pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D)) ≫
      pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) ≫ D.ideal.subschemeι, by
    rw [pullback.condition (f := E.subgroupStructMap D) (g := E.bimulBase (D := D)),
      E.bimulBase_eq_fst_structMap]
    simp only [Category.assoc]⟩

noncomputable def tpt₃ :
    E.Point (pullback.fst (E.subgroupStructMap D) (E.bimulBase (D := D)) ≫ E.subgroupStructMap D) :=
  ⟨pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D)) ≫
      pullback.snd (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) ≫ D.ideal.subschemeι, by
    rw [pullback.condition (f := E.subgroupStructMap D) (g := E.bimulBase (D := D)),
      E.bimulBase_eq_snd_structMap]
    simp only [Category.assoc]⟩

/-- **(Layer B, L4 — associativity of the group-scheme multiplication.)** `(m ×ₛ id) ≫ m` and
`(id ×ₛ m) ≫ m` agree (over the triple pullback `D ×ₛ D ×ₛ D`); dualizes to coassociativity. -/
theorem subgroupMul_assoc (hD : D.IsSubgroup E) :
    E.vmap' hD ≫ E.subgroupMul hD = E.vmap hD ≫ E.subgroupMul hD := by
  rw [← cancel_mono D.ideal.subschemeι, Category.assoc, Category.assoc,
    E.subgroupMul_subschemeι hD]
  have hv : E.vmap hD ≫ E.bimulBase (D := D)
      = pullback.fst (E.subgroupStructMap D) (E.bimulBase (D := D)) ≫ E.subgroupStructMap D := by
    show E.vmap hD ≫ (pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)
        ≫ (D.ideal.subschemeι ≫ E.π)) = _
    rw [← Category.assoc, vmap, pullback.lift_fst]
  have hu : E.umap (D := D) ≫ E.bimulBase (D := D)
      = pullback.fst (E.subgroupStructMap D) (E.bimulBase (D := D)) ≫ E.subgroupStructMap D := by
    show E.umap (D := D) ≫ (pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)
        ≫ (D.ideal.subschemeι ≫ E.π)) = _
    rw [← Category.assoc, umap, pullback.lift_fst]
  have hv' : E.vmap' hD ≫ E.bimulBase (D := D)
      = pullback.fst (E.subgroupStructMap D) (E.bimulBase (D := D)) ≫ E.subgroupStructMap D := by
    show E.vmap' hD ≫ (pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)
        ≫ (D.ideal.subschemeι ≫ E.π)) = _
    rw [← Category.assoc, vmap', pullback.lift_fst, Category.assoc, E.subgroupMul_structMap hD]
    show E.umap (D := D) ≫ (pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)
        ≫ (D.ideal.subschemeι ≫ E.π)) = _
    rw [← Category.assoc, umap, pullback.lift_fst]
  have hs : pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D)) ≫ E.bimulBase (D := D)
      = pullback.fst (E.subgroupStructMap D) (E.bimulBase (D := D)) ≫ E.subgroupStructMap D :=
    (pullback.condition (f := E.subgroupStructMap D) (g := E.bimulBase (D := D))).symm
  -- inner: tpt₂ + tpt₃
  have Es : (hs ▸ Point.restrict E (pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D)))
      (E.bipt₁ (D := D) + E.bipt₂ (D := D)) :
        E.Point (pullback.fst (E.subgroupStructMap D) (E.bimulBase (D := D)) ≫
          E.subgroupStructMap D))
      = E.tpt₂ + E.tpt₃ :=
    Point.restrictT_add_eq E _ hs E.tpt₂ E.tpt₃
      (by show _ ≫ (pullback.fst _ _ ≫ D.ideal.subschemeι) = _; rw [tpt₂])
      (by show _ ≫ (pullback.snd _ _ ≫ D.ideal.subschemeι) = _; rw [tpt₃])
  -- inner: tpt₁ + tpt₂
  have Eu : (hu ▸ Point.restrict E (E.umap (D := D))
      (E.bipt₁ (D := D) + E.bipt₂ (D := D)) :
        E.Point (pullback.fst (E.subgroupStructMap D) (E.bimulBase (D := D)) ≫
          E.subgroupStructMap D))
      = E.tpt₁ + E.tpt₂ :=
    Point.restrictT_add_eq E _ hu E.tpt₁ E.tpt₂
      (by
        show E.umap (D := D) ≫ (pullback.fst _ _ ≫ D.ideal.subschemeι) = _
        rw [← Category.assoc, umap, pullback.lift_fst, tpt₁])
      (by
        show E.umap (D := D) ≫ (pullback.snd _ _ ≫ D.ideal.subschemeι) = _
        rw [← Category.assoc, umap, pullback.lift_snd, tpt₂]; simp only [Category.assoc])
  -- v: tpt₁ + (tpt₂ + tpt₃)
  have Ev : (hv ▸ Point.restrict E (E.vmap hD)
      (E.bipt₁ (D := D) + E.bipt₂ (D := D)) :
        E.Point (pullback.fst (E.subgroupStructMap D) (E.bimulBase (D := D)) ≫
          E.subgroupStructMap D))
      = E.tpt₁ + (E.tpt₂ + E.tpt₃) :=
    Point.restrictT_add_eq E _ hv E.tpt₁ (E.tpt₂ + E.tpt₃)
      (by
        show E.vmap hD ≫ (pullback.fst _ _ ≫ D.ideal.subschemeι) = _
        rw [← Category.assoc, vmap, pullback.lift_fst, tpt₁])
      (by
        have hR : (E.tpt₂ + E.tpt₃).1 = pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D))
            ≫ (E.bipt₁ (D := D) + E.bipt₂ (D := D)).1 := by
          rw [← Es]; exact Point.base_congr (E := E) hs _
        rw [hR]
        show E.vmap hD ≫ (pullback.snd _ _ ≫ D.ideal.subschemeι) = _
        rw [← Category.assoc, vmap, pullback.lift_snd, Category.assoc, E.subgroupMul_subschemeι hD])
  -- v': (tpt₁ + tpt₂) + tpt₃
  have Ev' : (hv' ▸ Point.restrict E (E.vmap' hD)
      (E.bipt₁ (D := D) + E.bipt₂ (D := D)) :
        E.Point (pullback.fst (E.subgroupStructMap D) (E.bimulBase (D := D)) ≫
          E.subgroupStructMap D))
      = (E.tpt₁ + E.tpt₂) + E.tpt₃ :=
    Point.restrictT_add_eq E _ hv' (E.tpt₁ + E.tpt₂) E.tpt₃
      (by
        have hR : (E.tpt₁ + E.tpt₂).1 = E.umap (D := D)
            ≫ (E.bipt₁ (D := D) + E.bipt₂ (D := D)).1 := by
          rw [← Eu]; exact Point.base_congr (E := E) hu _
        rw [hR]
        show E.vmap' hD ≫ (pullback.fst _ _ ≫ D.ideal.subschemeι) = _
        rw [← Category.assoc, vmap', pullback.lift_fst, Category.assoc,
          E.subgroupMul_subschemeι hD])
      (by
        show E.vmap' hD ≫ (pullback.snd _ _ ≫ D.ideal.subschemeι) = _
        rw [← Category.assoc, vmap', pullback.lift_snd, tpt₃]; simp only [Category.assoc])
  -- assemble
  have key : (hv' ▸ Point.restrict E (E.vmap' hD) (E.bipt₁ (D := D) + E.bipt₂ (D := D)) :
        E.Point _)
      = hv ▸ Point.restrict E (E.vmap hD) (E.bipt₁ (D := D) + E.bipt₂ (D := D)) := by
    rw [Ev, Ev', add_assoc]
  have hgoal := congrArg Subtype.val key
  rw [Point.base_congr, Point.base_congr] at hgoal
  exact hgoal


/-- `Γ(m) : A →ₐ[R] Γ(D ×_R D)`, the algebra map underlying the comultiplication (before the tensor
identification). `R`-linear because `m` is a morphism over the base (`subgroupMul_structMap`). -/
noncomputable def subgroupComulHom (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    letI := E.biproductAlgebra (D := D)
    Γ(D.ideal.subscheme, ⊤) →ₐ[R]
      Γ(pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π), ⊤) :=
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  { (E.subgroupMul hD).appTop.hom with
    commutes' := fun r => by
      have hcomp :
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop) ≫
            (E.subgroupMul hD).appTop =
            (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop := by
        rw [Category.assoc, ← Scheme.Hom.comp_appTop, E.subgroupMul_structMap hD]
      show (E.subgroupMul hD).appTop.hom
          (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom r) =
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop).hom r
      rw [← CommRingCat.comp_apply, hcomp] }

/-- **(Layer B, L3 — the comultiplication.)** `Δ = m^♯ : A →ₐ[R] A ⊗_R A`, the Hopf-dual of the
group-scheme multiplication `subgroupMul` (`m : D ×_S D ⟶ D`) over the affine base: `Δ = κ⁻¹ ∘
Γ(m)`,
where `Γ(m)` pulls regular functions back along `m` into `Γ(D ×_{Spec R} D)` and `κ⁻¹` identifies
that with `A ⊗_R A` (`subgroupTensorCompare`). Coassociativity dualizes associativity of `m`. -/
noncomputable def subgroupComul (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    Γ(D.ideal.subscheme, ⊤) →ₐ[R]
      TensorProduct R Γ(D.ideal.subscheme, ⊤) Γ(D.ideal.subscheme, ⊤) :=
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  (AlgEquiv.ofBijective (E.subgroupTensorCompare (D := D))
      (E.subgroupTensorCompare_bijective (D := D))).symm.toAlgHom.comp (E.subgroupComulHom hD)

/-- **The comultiplication interface pin (v10.24(b) opaque interface).** `κ (Δ a) = Γ(m) a`: `Δ` is
characterised by pushing forward through the tensor comparison `κ` to `Γ(m)`. Downstream (Hopf
axioms, L6 points↔convolution) consumes only this pin; `subgroupComul` is then marked `irreducible`
so its heavy `κ⁻¹` core is never unfolded — dodging the whnf/kernel-poison wall that scheme-iso
definitions trigger (the T-W7.1b lesson). -/
theorem subgroupTensorCompare_subgroupComul (hD : D.IsSubgroup E)
    (a : Γ(D.ideal.subscheme, ⊤)) :
    letI := E.subgroupAlgebra D
    letI := E.biproductAlgebra (D := D)
    E.subgroupTensorCompare (D := D) (E.subgroupComul hD a) = E.subgroupComulHom hD a := by
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  exact AlgEquiv.apply_symm_apply
    (AlgEquiv.ofBijective (E.subgroupTensorCompare (D := D))
      (E.subgroupTensorCompare_bijective (D := D))) (E.subgroupComulHom hD a)

attribute [irreducible] subgroupComul

/-- `swap ≫ bimulBase = bimulBase` (the exchange automorphism preserves the base). -/
theorem swap_bimulBase :
    (Limits.pullbackSymmetry (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)).hom
        ≫ E.bimulBase (D := D) = E.bimulBase (D := D) := by
  show _ ≫ (pullback.fst _ _ ≫ _) = _
  rw [← Category.assoc, Limits.pullbackSymmetry_hom_comp_fst, E.bimulBase_eq_snd_structMap]

/-- `Γ(swap)` packaged as an `R`-algebra automorphism of `Γ(D ×_R D)`. -/
noncomputable def swapAlg (hD : D.IsSubgroup E) :
    letI := E.biproductAlgebra (D := D)
    Γ(pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π), ⊤) →ₐ[R]
      Γ(pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π), ⊤) :=
  letI := E.biproductAlgebra (D := D)
  { (Limits.pullbackSymmetry (D.ideal.subschemeι ≫ E.π)
      (D.ideal.subschemeι ≫ E.π)).hom.appTop.hom with
    commutes' := fun r => by
      have hcomp :
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop) ≫
            (Limits.pullbackSymmetry (D.ideal.subschemeι ≫ E.π)
              (D.ideal.subschemeι ≫ E.π)).hom.appTop =
            (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop := by
        rw [Category.assoc, ← Scheme.Hom.comp_appTop, E.swap_bimulBase]
      show (Limits.pullbackSymmetry (D.ideal.subschemeι ≫ E.π)
            (D.ideal.subschemeι ≫ E.π)).hom.appTop.hom
          (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop).hom r) =
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop).hom r
      rw [← CommRingCat.comp_apply, hcomp] }

/-- **(Layer B, cocommutativity.)** `comm ∘ Δ = Δ`: the comultiplication is cocommutative, dualizing
`swap ≫ m = m` (`subgroupMul_comm`). Gives `IsCocomm R A`. -/
theorem subgroupComul_comm (hD : D.IsSubgroup E) (a : Γ(D.ideal.subscheme, ⊤)) :
    letI := E.subgroupAlgebra D
    Algebra.TensorProduct.comm R Γ(D.ideal.subscheme, ⊤) Γ(D.ideal.subscheme, ⊤)
        (E.subgroupComul hD a) = E.subgroupComul hD a := by
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  -- κ ∘ comm = swapAlg ∘ κ
  have hproj₁ : ∀ b, E.swapAlg hD (E.subgroupProj₁ (D := D) b) = E.subgroupProj₂ (D := D) b := by
    intro b
    show (Limits.pullbackSymmetry (D.ideal.subschemeι ≫ E.π)
        (D.ideal.subschemeι ≫ E.π)).hom.appTop.hom
        ((pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)).appTop.hom b) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      show (Limits.pullbackSymmetry (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)).hom
        ≫ pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)
        = pullback.snd (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) from
          Limits.pullbackSymmetry_hom_comp_fst _ _]
    rfl
  have hproj₂ : ∀ b, E.swapAlg hD (E.subgroupProj₂ (D := D) b) = E.subgroupProj₁ (D := D) b := by
    intro b
    show (Limits.pullbackSymmetry (D.ideal.subschemeι ≫ E.π)
        (D.ideal.subschemeι ≫ E.π)).hom.appTop.hom
        ((pullback.snd (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)).appTop.hom b) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      show (Limits.pullbackSymmetry (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)).hom
        ≫ pullback.snd (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)
        = pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) from
          Limits.pullbackSymmetry_hom_comp_snd _ _]
    rfl
  have intertwine : (E.subgroupTensorCompare (D := D)).comp
        (Algebra.TensorProduct.comm R Γ(D.ideal.subscheme, ⊤) Γ(D.ideal.subscheme, ⊤)).toAlgHom
      = (E.swapAlg hD).comp (E.subgroupTensorCompare (D := D)) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    show E.subgroupTensorCompare (D := D) (y ⊗ₜ[R] x)
      = E.swapAlg hD (E.subgroupTensorCompare (D := D) (x ⊗ₜ[R] y))
    rw [subgroupTensorCompare, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul,
      map_mul, hproj₁, hproj₂, mul_comm]
  -- swapAlg fixes Γ(m)a (from subgroupMul_comm)
  have hswap : E.swapAlg hD (E.subgroupComulHom hD a) = E.subgroupComulHom hD a := by
    show (Limits.pullbackSymmetry (D.ideal.subschemeι ≫ E.π)
        (D.ideal.subschemeι ≫ E.π)).hom.appTop.hom
        ((E.subgroupMul hD).appTop.hom a) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      show (Limits.pullbackSymmetry (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)).hom
          ≫ E.subgroupMul hD = E.subgroupMul hD from E.subgroupMul_comm hD]
    rfl
  have happ := DFunLike.congr_fun intertwine (E.subgroupComul hD a)
  rw [AlgHom.comp_apply, AlgHom.comp_apply, subgroupTensorCompare_subgroupComul, hswap] at happ
  -- happ : κ(comm(Δa)) = subgroupComulHom a
  apply (E.subgroupTensorCompare_bijective (D := D)).injective
  rw [subgroupTensorCompare_subgroupComul]
  exact happ


/-- The unit section `e` is a section of the structure map: `e ≫ (subschemeι ≫ π) = 𝟙 S`
(the zero point lies over the identity of the base). -/
theorem subgroupUnit_structMap (hD : D.IsSubgroup E) :
    E.subgroupUnit hD ≫ E.subgroupStructMap D = 𝟙 (Spec (CommRingCat.of R)) := by
  show E.subgroupUnit hD ≫ (D.ideal.subschemeι ≫ E.π) = 𝟙 _
  rw [← Category.assoc, E.subgroupUnit_subschemeι hD]
  exact (0 : E.Point (𝟙 (Spec (CommRingCat.of R)))).2

/-! ### Triple comparison `κ₃` (for coassociativity)

`Δ` is coassociative because `m` is associative (`subgroupMul_assoc`). Dualizing that equality of
scheme maps into an equality of comultiplications requires comparing `A ⊗ (A ⊗ A)` with the triple
product's coordinate ring `Γ(P₃)`, `P₃ = D ×ₛ (D ×ₛ D)`. This comparison `κ₃ = κ_DP ∘ (id ⊗ κ)` is
an isomorphism, so injective — the tool that turns `subgroupMul_assoc` into `Coalgebra.coassoc`. -/

/-- Algebra on `Γ(P₃)`, `P₃ = D ×ₛ (D ×ₛ D)`. Matches the codomain algebra of
`κ_DP = pairTensorCompare (subgroupStructMap D) bimulBase`. -/
@[reducible] noncomputable def tripleAlgebra :
    Algebra R Γ(pullback (E.subgroupStructMap D) (E.bimulBase (D := D)), ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    (pairBase (E.subgroupStructMap D) (E.bimulBase (D := D))).appTop).hom.toAlgebra

set_option backward.isDefEq.respectTransparency.types false in
/-- `P₃ = D ×ₛ (D ×ₛ D)` is affine: `pullback.snd` is a base change of the finite (hence affine)
`subgroupStructMap D`, and `D ×ₛ D` is affine. -/
theorem subgroupTriple_isAffine :
    IsAffine (pullback (E.subgroupStructMap D) (E.bimulBase (D := D))) := by
  haveI : IsFinite (E.subgroupStructMap D) := D.finite
  haveI : IsAffine (pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)) :=
    E.subgroupBiproduct_isAffine (D := D)
  haveI : IsAffineHom (pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D))) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  exact isAffine_of_isAffineHom (pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D)))

/-- `id_A ⊗ κ : A ⊗ (A ⊗ A) → A ⊗ Γ(D ×ₛ D)`, built homogeneously via `lift`
(`includeLeft`, `includeRight ∘ κ`) to avoid the heterobasic `TensorProduct.map` instance clash. -/
noncomputable def subgroupIdTensorCompare (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    letI := E.biproductAlgebra (D := D)
    (Γ(D.ideal.subscheme, ⊤) ⊗[R] (Γ(D.ideal.subscheme, ⊤) ⊗[R] Γ(D.ideal.subscheme, ⊤)))
      →ₐ[R] (Γ(D.ideal.subscheme, ⊤) ⊗[R]
        Γ(pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π), ⊤)) :=
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft
    (Algebra.TensorProduct.includeRight.comp (E.subgroupTensorCompare (D := D)))
    (fun _ _ => Commute.all _ _)

/-- `(id ⊗ κ)(a ⊗ b) = a ⊗ κ b`. (`∀` inside `letI` so the tensor-typed binder sees the algebra.) -/
theorem subgroupIdTensorCompare_tmul (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    letI := E.biproductAlgebra (D := D)
    ∀ (a : Γ(D.ideal.subscheme, ⊤))
      (b : Γ(D.ideal.subscheme, ⊤) ⊗[R] Γ(D.ideal.subscheme, ⊤)),
      E.subgroupIdTensorCompare hD (a ⊗ₜ[R] b)
        = a ⊗ₜ[R] (E.subgroupTensorCompare (D := D) b) := by
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  intro a b
  rw [subgroupIdTensorCompare, Algebra.TensorProduct.lift_tmul,
    Algebra.TensorProduct.includeLeft_apply, AlgHom.comp_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, mul_one]

/-- `id_A ⊗ κ` is injective (`κ` is an iso), via the retraction `lift includeLeft (includeRight ∘
κ⁻¹)`. -/
theorem subgroupIdTensorCompare_injective (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    letI := E.biproductAlgebra (D := D)
    Function.Injective (E.subgroupIdTensorCompare hD) := by
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  haveI : IsFinite (E.subgroupStructMap D) := D.finite
  haveI : IsAffine D.ideal.subscheme := isAffine_of_isAffineHom (E.subgroupStructMap D)
  haveI : IsAffine (pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)) :=
    E.subgroupBiproduct_isAffine (D := D)
  letI κe := AlgEquiv.ofBijective (E.subgroupTensorCompare (D := D))
    (E.subgroupTensorCompare_bijective (D := D))
  set ret : (Γ(D.ideal.subscheme, ⊤) ⊗[R]
        Γ(pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π), ⊤)) →ₐ[R]
      (Γ(D.ideal.subscheme, ⊤) ⊗[R] (Γ(D.ideal.subscheme, ⊤) ⊗[R] Γ(D.ideal.subscheme, ⊤))) :=
    Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft
      (Algebra.TensorProduct.includeRight.comp κe.symm.toAlgHom)
      (fun _ _ => Commute.all _ _) with hret
  have hret_tmul : ∀ (a : Γ(D.ideal.subscheme, ⊤))
      (w : Γ(pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π), ⊤)),
      ret (a ⊗ₜ[R] w) = a ⊗ₜ[R] (κe.symm.toAlgHom w) := by
    intro a w
    rw [hret, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.includeLeft_apply,
      AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  have hcomp : ret.comp (E.subgroupIdTensorCompare hD) = AlgHom.id R _ := by
    apply Algebra.TensorProduct.ext'
    intro a b
    rw [AlgHom.comp_apply, E.subgroupIdTensorCompare_tmul hD, hret_tmul, AlgHom.id_apply]
    congr 1
    exact κe.symm_apply_apply b
  exact Function.LeftInverse.injective (g := ret)
    (fun x => by rw [← AlgHom.comp_apply, hcomp, AlgHom.id_apply])

/-- The triple comparison `κ₃ : A ⊗ (A ⊗ A) →ₐ Γ(P₃)`, `κ₃ = κ_DP ∘ (id ⊗ κ)`. Injective (both
factors iso). Dualizes associativity of `m` (`subgroupMul_assoc`) into coassociativity of `Δ`. -/
noncomputable def subgroupTripleCompare (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    letI := E.tripleAlgebra (D := D)
    (Γ(D.ideal.subscheme, ⊤) ⊗[R] (Γ(D.ideal.subscheme, ⊤) ⊗[R] Γ(D.ideal.subscheme, ⊤)))
      →ₐ[R] Γ(pullback (E.subgroupStructMap D) (E.bimulBase (D := D)), ⊤) :=
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  letI := E.tripleAlgebra (D := D)
  (pairTensorCompare (E.subgroupStructMap D) (E.bimulBase (D := D))).comp
    (E.subgroupIdTensorCompare hD)

/-- `κ₃` is injective. -/
theorem subgroupTripleCompare_injective (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    letI := E.tripleAlgebra (D := D)
    Function.Injective (E.subgroupTripleCompare hD) := by
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  letI := E.tripleAlgebra (D := D)
  haveI : IsFinite (E.subgroupStructMap D) := D.finite
  haveI : IsAffine D.ideal.subscheme := isAffine_of_isAffineHom (E.subgroupStructMap D)
  haveI : IsAffine (pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)) :=
    E.subgroupBiproduct_isAffine (D := D)
  have hpair : Function.Injective
      (pairTensorCompare (E.subgroupStructMap D) (E.bimulBase (D := D))) :=
    (pairTensorCompare_bijective (E.subgroupStructMap D) (E.bimulBase (D := D))).injective
  exact hpair.comp (E.subgroupIdTensorCompare_injective hD)

/-! ### The `baseGate` dualization gateway

Each triple-multiplication map `w : P₃ ⟶ P₂` over the base pulls functions back to `Γ(w) : Γ(P₂) →
Γ(P₃)`; packaged as an `R`-algebra hom (`baseGate`), it collapses `κ (Δ a)` to `Γ(w ≫ m) a` (via the
`Δ`-pin) and `κ (x ⊗ y)` to `Γ(w ≫ fst₂) x · Γ(w ≫ snd₂) y`. These two facts turn the scheme
identity `subgroupMul_assoc` into `Coalgebra.coassoc`. -/

/-- Gateway: `Γ(w)` packaged as an `R`-algebra hom `Γ(D ×ₛ D) →ₐ Γ(P₃)`, for any `w : P₃ ⟶ P₂`
whose base agrees (`w ≫ bimulBase = pairBase = base P₃`). -/
noncomputable def baseGate (hD : D.IsSubgroup E)
    (w : pullback (E.subgroupStructMap D) (E.bimulBase (D := D)) ⟶
        pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π))
    (hw : w ≫ E.bimulBase (D := D)
      = pairBase (E.subgroupStructMap D) (E.bimulBase (D := D))) :
    letI := E.biproductAlgebra (D := D)
    letI := E.tripleAlgebra (D := D)
    Γ(pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π), ⊤) →ₐ[R]
      Γ(pullback (E.subgroupStructMap D) (E.bimulBase (D := D)), ⊤) :=
  letI := E.biproductAlgebra (D := D)
  letI := E.tripleAlgebra (D := D)
  { w.appTop.hom with
    commutes' := fun r => by
      have hcomp :
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop) ≫ w.appTop =
            (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
              (pairBase (E.subgroupStructMap D) (E.bimulBase (D := D))).appTop := by
        rw [Category.assoc, ← Scheme.Hom.comp_appTop, hw]
      show w.appTop.hom
          (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop).hom r) =
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
          (pairBase (E.subgroupStructMap D) (E.bimulBase (D := D))).appTop).hom r
      rw [← CommRingCat.comp_apply, hcomp] }

/-- `baseGate w (Γ(m) a) = Γ(w ≫ m) a`. -/
theorem baseGate_comul (hD : D.IsSubgroup E)
    (w : pullback (E.subgroupStructMap D) (E.bimulBase (D := D)) ⟶
        pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π))
    (hw : w ≫ E.bimulBase (D := D)
      = pairBase (E.subgroupStructMap D) (E.bimulBase (D := D))) :
    letI := E.subgroupAlgebra D
    letI := E.biproductAlgebra (D := D)
    letI := E.tripleAlgebra (D := D)
    ∀ (a : Γ(D.ideal.subscheme, ⊤)),
      E.baseGate hD w hw (E.subgroupComulHom hD a) = (w ≫ E.subgroupMul hD).appTop.hom a := by
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  letI := E.tripleAlgebra (D := D)
  intro a
  show w.appTop.hom ((E.subgroupMul hD).appTop.hom a) = _
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]

/-- `baseGate w (κ (x ⊗ y)) = Γ(w ≫ fst₂) x · Γ(w ≫ snd₂) y`. -/
theorem baseGate_kappa_tmul (hD : D.IsSubgroup E)
    (w : pullback (E.subgroupStructMap D) (E.bimulBase (D := D)) ⟶
        pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π))
    (hw : w ≫ E.bimulBase (D := D)
      = pairBase (E.subgroupStructMap D) (E.bimulBase (D := D))) :
    letI := E.subgroupAlgebra D
    letI := E.biproductAlgebra (D := D)
    letI := E.tripleAlgebra (D := D)
    ∀ (x y : Γ(D.ideal.subscheme, ⊤)),
      E.baseGate hD w hw (E.subgroupTensorCompare (D := D) (x ⊗ₜ[R] y))
        = (w ≫ pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)).appTop.hom x
          * (w ≫ pullback.snd (D.ideal.subschemeι ≫ E.π)
              (D.ideal.subschemeι ≫ E.π)).appTop.hom y := by
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  letI := E.tripleAlgebra (D := D)
  intro x y
  have h1 : E.baseGate hD w hw (E.subgroupProj₁ (D := D) x)
      = (w ≫ pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)).appTop.hom x := by
    show w.appTop.hom ((pullback.fst (D.ideal.subschemeι ≫ E.π)
      (D.ideal.subschemeι ≫ E.π)).appTop.hom x) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  have h2 : E.baseGate hD w hw (E.subgroupProj₂ (D := D) y)
      = (w ≫ pullback.snd (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)).appTop.hom y := by
    show w.appTop.hom ((pullback.snd (D.ideal.subschemeι ≫ E.π)
      (D.ideal.subschemeι ≫ E.π)).appTop.hom y) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  rw [subgroupTensorCompare, Algebra.TensorProduct.lift_tmul, map_mul, h1, h2]

/-! ### The three triple-multiplication maps `P₃ ⟶ P₂` and their base compatibility

`vmap = ⟨fst₃, snd₃ ≫ m⟩`, `umap = ⟨fst₃, snd₃ ≫ fst₂⟩`, `vmap' = ⟨umap ≫ m, snd₃ ≫ snd₂⟩` — the
right- and left-associated triple products, with `subgroupMul_assoc : vmap' ≫ m = vmap ≫ m`. Each is
a `baseGate` map (`w ≫ bimulBase = pairBase`), established below. -/

theorem vmap_fst (hD : D.IsSubgroup E) :
    E.vmap hD ≫ pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)
      = pullback.fst (E.subgroupStructMap D) (E.bimulBase (D := D)) := pullback.lift_fst _ _ _

theorem vmap_snd (hD : D.IsSubgroup E) :
    E.vmap hD ≫ pullback.snd (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)
      = pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D)) ≫ E.subgroupMul hD :=
  pullback.lift_snd _ _ _

theorem umap_fst :
    E.umap (D := D) ≫ pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)
      = pullback.fst (E.subgroupStructMap D) (E.bimulBase (D := D)) := pullback.lift_fst _ _ _

theorem umap_snd :
    E.umap (D := D) ≫ pullback.snd (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)
      = pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D))
        ≫ pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) :=
  pullback.lift_snd _ _ _

theorem vmap'_fst (hD : D.IsSubgroup E) :
    E.vmap' hD ≫ pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)
      = E.umap (D := D) ≫ E.subgroupMul hD := pullback.lift_fst _ _ _

theorem vmap'_snd (hD : D.IsSubgroup E) :
    E.vmap' hD ≫ pullback.snd (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)
      = pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D))
        ≫ pullback.snd (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) :=
  pullback.lift_snd _ _ _

theorem vmap_base (hD : D.IsSubgroup E) :
    E.vmap hD ≫ E.bimulBase (D := D) = pairBase (E.subgroupStructMap D) (E.bimulBase (D := D)) := by
  have h1 : E.vmap hD ≫ E.bimulBase (D := D)
      = (E.vmap hD ≫ pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π))
        ≫ E.subgroupStructMap D := by
    rw [Category.assoc, ← E.bimulBase_eq_fst_structMap]
  rw [h1, E.vmap_fst hD]

theorem umap_base :
    E.umap (D := D) ≫ E.bimulBase (D := D)
      = pairBase (E.subgroupStructMap D) (E.bimulBase (D := D)) := by
  have h1 : E.umap (D := D) ≫ E.bimulBase (D := D)
      = (E.umap (D := D) ≫ pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π))
        ≫ E.subgroupStructMap D := by
    rw [Category.assoc, ← E.bimulBase_eq_fst_structMap]
  rw [h1, E.umap_fst]

theorem vmap'_base (hD : D.IsSubgroup E) :
    E.vmap' hD ≫ E.bimulBase (D := D)
      = pairBase (E.subgroupStructMap D) (E.bimulBase (D := D)) := by
  have h1 : E.vmap' hD ≫ E.bimulBase (D := D)
      = (E.vmap' hD ≫ pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π))
        ≫ E.subgroupStructMap D := by
    rw [Category.assoc, ← E.bimulBase_eq_fst_structMap]
  rw [h1, E.vmap'_fst hD, Category.assoc, E.subgroupMul_structMap hD, E.umap_base]

/-! ### `κ` and `κ₃` on pure tensors, and the `hZ` assoc-factoring lemma -/

/-- `κ (x ⊗ y) = proj₁ x · proj₂ y`. -/
theorem subgroupTensorCompare_tmul (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    letI := E.biproductAlgebra (D := D)
    ∀ (x y : Γ(D.ideal.subscheme, ⊤)),
      E.subgroupTensorCompare (D := D) (x ⊗ₜ[R] y)
        = E.subgroupProj₁ (D := D) x * E.subgroupProj₂ (D := D) y := by
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  intro x y
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- `κ₃ (a ⊗ b) = Γ(fst₃) a · Γ(snd₃) (κ b)`. -/
theorem subgroupTripleCompare_tmul (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    letI := E.tripleAlgebra (D := D)
    ∀ (a : Γ(D.ideal.subscheme, ⊤))
      (b : Γ(D.ideal.subscheme, ⊤) ⊗[R] Γ(D.ideal.subscheme, ⊤)),
      E.subgroupTripleCompare hD (a ⊗ₜ[R] b)
        = (pullback.fst (E.subgroupStructMap D) (E.bimulBase (D := D))).appTop.hom a
          * (pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D))).appTop.hom
              (E.subgroupTensorCompare (D := D) b) := by
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  letI := E.tripleAlgebra (D := D)
  haveI : IsFinite (E.subgroupStructMap D) := D.finite
  haveI : IsAffine D.ideal.subscheme := isAffine_of_isAffineHom (E.subgroupStructMap D)
  haveI : IsAffine (pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)) :=
    E.subgroupBiproduct_isAffine (D := D)
  intro a b
  have h1 : E.subgroupTripleCompare hD (a ⊗ₜ[R] b)
      = pairTensorCompare (E.subgroupStructMap D) (E.bimulBase (D := D))
          (E.subgroupIdTensorCompare hD (a ⊗ₜ[R] b)) := rfl
  rw [h1, E.subgroupIdTensorCompare_tmul hD]
  exact pairTensorCompare_tmul (E.subgroupStructMap D) (E.bimulBase (D := D)) a
    (E.subgroupTensorCompare (D := D) b)

/-- **hZ (assoc factoring).** `κ₃ (assoc (z ⊗ y)) = baseGate umap (κ z) · Γ(snd₃ ≫ snd₂) y`. Linear
in `z`; this is what lets the inner `Δ` collapse (over `umap`) happen inside the `LEFT` `ext'`. -/
theorem subgroupTripleCompare_assoc_tmul (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    letI := E.tripleAlgebra (D := D)
    ∀ (y : Γ(D.ideal.subscheme, ⊤))
      (z : Γ(D.ideal.subscheme, ⊤) ⊗[R] Γ(D.ideal.subscheme, ⊤)),
      E.subgroupTripleCompare hD ((TensorProduct.assoc R _ _ _) (z ⊗ₜ[R] y))
        = E.baseGate hD (E.umap (D := D)) E.umap_base (E.subgroupTensorCompare (D := D) z)
          * (pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D))
              ≫ pullback.snd (D.ideal.subschemeι ≫ E.π)
                (D.ideal.subschemeι ≫ E.π)).appTop.hom y := by
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  letI := E.tripleAlgebra (D := D)
  haveI : IsFinite (E.subgroupStructMap D) := D.finite
  haveI : IsAffine D.ideal.subscheme := isAffine_of_isAffineHom (E.subgroupStructMap D)
  haveI : IsAffine (pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)) :=
    E.subgroupBiproduct_isAffine (D := D)
  intro y z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z1 z2 h1 h2 =>
    simp only [TensorProduct.add_tmul, map_add, add_mul, h1, h2]
  | tmul p q =>
    have hpq : (pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D))).appTop.hom
          (E.subgroupProj₁ (D := D) q)
        = (pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D))
            ≫ pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)).appTop.hom q := by
      show (pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D))).appTop.hom
        ((pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)).appTop.hom q) = _
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
    have hpy : (pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D))).appTop.hom
          (E.subgroupProj₂ (D := D) y)
        = (pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D))
            ≫ pullback.snd (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)).appTop.hom y := by
      show (pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D))).appTop.hom
        ((pullback.snd (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)).appTop.hom y) = _
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
    rw [TensorProduct.assoc_tmul]
    rw [E.subgroupTripleCompare_tmul hD]
    rw [E.baseGate_kappa_tmul hD (E.umap (D := D)) E.umap_base]
    simp only [E.umap_fst, E.umap_snd]
    rw [E.subgroupTensorCompare_tmul hD]
    simp only [map_mul, hpq, hpy]
    ring

/-- **(coassoc, RIGHT half.)** `κ₃ (lTensor Δ w) = baseGate vmap (κ w)`. The comultiplication in the
outer (second) tensor slot collapses along `vmap`. Proven by `TensorProduct.induction_on w`; the
`tmul` case uses `κ₃(a⊗b) = Γ(fst₃) a · Γ(snd₃)(κ b)` and the pin `κ(Δy) = subgroupComulHom y`. -/
theorem subgroupComul_coassoc_right (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    letI := E.tripleAlgebra (D := D)
    ∀ (w : Γ(D.ideal.subscheme, ⊤) ⊗[R] Γ(D.ideal.subscheme, ⊤)),
      E.subgroupTripleCompare hD
          (LinearMap.lTensor Γ(D.ideal.subscheme, ⊤) (E.subgroupComul hD).toLinearMap w)
        = E.baseGate hD (E.vmap hD) (E.vmap_base hD) (E.subgroupTensorCompare (D := D) w) := by
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  letI := E.tripleAlgebra (D := D)
  intro w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w1 w2 h1 h2 => simp only [map_add, h1, h2]
  | tmul x y =>
    have hcm : (pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D))).appTop.hom
          (E.subgroupComulHom hD y)
        = (pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D))
            ≫ E.subgroupMul hD).appTop.hom y := by
      show (pullback.snd (E.subgroupStructMap D) (E.bimulBase (D := D))).appTop.hom
        ((E.subgroupMul hD).appTop.hom y) = _
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
    rw [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, E.subgroupTripleCompare_tmul hD,
      E.subgroupTensorCompare_subgroupComul hD,
      E.baseGate_kappa_tmul hD (E.vmap hD) (E.vmap_base hD)]
    simp only [E.vmap_fst, E.vmap_snd, hcm]

/-- **(coassoc, LEFT half.)** `κ₃ (assoc (rTensor Δ w)) = baseGate vmap' (κ w)`. The
comultiplication
in the inner (first) tensor slot collapses along `vmap'`. Proven by `TensorProduct.induction_on w`;
the `tmul` case uses the assoc-factoring `subgroupTripleCompare_assoc_tmul` (hZ), the pin, and the
`baseGate` collapse over `umap` (which `vmap'` factors through). -/
theorem subgroupComul_coassoc_left (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    letI := E.tripleAlgebra (D := D)
    ∀ (w : Γ(D.ideal.subscheme, ⊤) ⊗[R] Γ(D.ideal.subscheme, ⊤)),
      E.subgroupTripleCompare hD ((TensorProduct.assoc R _ _ _)
          (LinearMap.rTensor Γ(D.ideal.subscheme, ⊤) (E.subgroupComul hD).toLinearMap w))
        = E.baseGate hD (E.vmap' hD) (E.vmap'_base hD) (E.subgroupTensorCompare (D := D) w) := by
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  letI := E.tripleAlgebra (D := D)
  intro w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w1 w2 h1 h2 => simp only [map_add, h1, h2]
  | tmul x y =>
    rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, E.subgroupTripleCompare_assoc_tmul hD,
      E.subgroupTensorCompare_subgroupComul hD, E.baseGate_comul hD (E.umap (D := D)) E.umap_base,
      E.baseGate_kappa_tmul hD (E.vmap' hD) (E.vmap'_base hD)]
    simp only [E.vmap'_fst, E.vmap'_snd]

/-- **(Layer B, L3 — coassociativity.)** `Δ` is coassociative:
`assoc ∘ (Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ`. Dualizes the scheme associativity
`subgroupMul_assoc` (`vmap' ≫ m = vmap ≫ m`) through the injective triple comparison `κ₃`:
apply `κ₃` to both sides, reduce each via the RIGHT/LEFT halves to `baseGate vmap (Δa)` /
`baseGate vmap' (Δa)`, i.e. `Γ(vmap ≫ m) a` / `Γ(vmap' ≫ m) a`, then `subgroupMul_assoc` closes it.
-/
theorem subgroupComul_coassoc (hD : D.IsSubgroup E) (a : Γ(D.ideal.subscheme, ⊤)) :
    letI := E.subgroupAlgebra D
    (TensorProduct.assoc R Γ(D.ideal.subscheme, ⊤) Γ(D.ideal.subscheme, ⊤) Γ(D.ideal.subscheme, ⊤))
        (LinearMap.rTensor Γ(D.ideal.subscheme, ⊤) (E.subgroupComul hD).toLinearMap
          (E.subgroupComul hD a))
      = LinearMap.lTensor Γ(D.ideal.subscheme, ⊤) (E.subgroupComul hD).toLinearMap
          (E.subgroupComul hD a) := by
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  letI := E.tripleAlgebra (D := D)
  apply E.subgroupTripleCompare_injective hD
  have hR := E.subgroupComul_coassoc_right hD (E.subgroupComul hD a)
  have hL := E.subgroupComul_coassoc_left hD (E.subgroupComul hD a)
  rw [E.subgroupTensorCompare_subgroupComul hD,
    E.baseGate_comul hD (E.vmap hD) (E.vmap_base hD)] at hR
  rw [E.subgroupTensorCompare_subgroupComul hD,
    E.baseGate_comul hD (E.vmap' hD) (E.vmap'_base hD)] at hL
  rw [hL, hR, E.subgroupMul_assoc hD]

/-- **(Layer B, L3 — the counit.)** `ε : A →ₐ[R] R`, the Hopf-dual of the unit section
`subgroupUnit` (`e : S ⟶ D`). Concretely `ε = Γ(e)` followed by `Γ(Spec R, ⊤) ≅ R`; it is
`R`-linear because `e` is a section of the structure map (`subgroupUnit_structMap`). Counit laws
dualize the unit laws of the group scheme. -/
noncomputable def subgroupCounit (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    Γ(D.ideal.subscheme, ⊤) →ₐ[R] R :=
  letI := E.subgroupAlgebra D
  { ((E.subgroupUnit hD).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom with
    commutes' := fun r => by
      have hcomp :
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop) ≫
            ((E.subgroupUnit hD).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom) =
            𝟙 (CommRingCat.of R) := by
        rw [Category.assoc, ← Category.assoc (E.subgroupStructMap D).appTop,
          ← Scheme.Hom.comp_appTop,
          show E.subgroupUnit hD ≫ E.subgroupStructMap D = 𝟙 _ from E.subgroupUnit_structMap hD]
        simp
      show ((E.subgroupUnit hD).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom
        (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom r) = r
      rw [← CommRingCat.comp_apply, hcomp, CommRingCat.id_apply] }

/-- The inversion `n` is a morphism over the base: `n ≫ (subschemeι ≫ π) = subschemeι ≫ π`
(the negation of the universal point lies over the same base map). -/
theorem subgroupInv_structMap (hD : D.IsSubgroup E) :
    E.subgroupInv hD ≫ E.subgroupStructMap D = E.subgroupStructMap D := by
  show E.subgroupInv hD ≫ (D.ideal.subschemeι ≫ E.π) = D.ideal.subschemeι ≫ E.π
  rw [← Category.assoc, E.subgroupInv_subschemeι hD]
  exact (-(E.upt (D := D))).2

/-- **(Layer B, L3 — the antipode.)** `antipode : A →ₐ[R] A`, the Hopf-dual of the inversion
`subgroupInv` (`n : D ⟶ D`). Concretely `Γ(n)`; it is `R`-linear because `n` is a morphism over
the base (`subgroupInv_structMap`). The antipode laws dualize the inverse laws of the group scheme.
-/
noncomputable def subgroupAntipode (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    Γ(D.ideal.subscheme, ⊤) →ₐ[R] Γ(D.ideal.subscheme, ⊤) :=
  letI := E.subgroupAlgebra D
  { (E.subgroupInv hD).appTop.hom with
    commutes' := fun r => by
      have hcomp :
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop) ≫
            (E.subgroupInv hD).appTop =
            (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop := by
        rw [Category.assoc, ← Scheme.Hom.comp_appTop, E.subgroupInv_structMap hD]
      show (E.subgroupInv hD).appTop.hom
          (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom r) =
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom r
      rw [← CommRingCat.comp_apply, hcomp] }

/-- The `e × id` section `D ⟶ D ×_S D` (unit on the left factor, identity on the right).
Dualizing it gives the algebra hom that witnesses the left counit law. -/
noncomputable def uLmap (hD : D.IsSubgroup E) : D.ideal.subscheme ⟶
    pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) :=
  pullback.lift ((D.ideal.subschemeι ≫ E.π) ≫ E.subgroupUnit hD) (𝟙 _)
    (by rw [Category.assoc, E.subgroupUnit_over hD, Category.comp_id, Category.id_comp])

theorem uLmap_bimulBase (hD : D.IsSubgroup E) :
    E.uLmap hD ≫ E.bimulBase (D := D) = D.ideal.subschemeι ≫ E.π := by
  show E.uLmap hD ≫ (pullback.fst _ _ ≫ _) = _
  rw [← Category.assoc, uLmap, pullback.lift_fst, Category.assoc, E.subgroupUnit_over hD,
    Category.comp_id]

/-- `uLmap.appTop` packaged as an `R`-algebra hom `Γ(D ×_S D) →ₐ Γ(D)`. -/
noncomputable def uLAlg (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    letI := E.biproductAlgebra (D := D)
    Γ(pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π), ⊤) →ₐ[R]
      Γ(D.ideal.subscheme, ⊤) :=
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  { (E.uLmap hD).appTop.hom with
    commutes' := fun r => by
      have hcomp :
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop) ≫
            (E.uLmap hD).appTop =
            (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop := by
        rw [Category.assoc, ← Scheme.Hom.comp_appTop, E.uLmap_bimulBase hD]
      show (E.uLmap hD).appTop.hom
          (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop).hom r) =
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom r
      rw [← CommRingCat.comp_apply, hcomp] }

/-- The left counit law for the subgroup Hopf structure: `(ε ⊗ id) ∘ Δ = 1 ⊗ ·`.
Proven by dualizing the scheme identity `uLmap ≫ m = 𝟙` through the `κ`-intertwine. -/
theorem subgroupCounit_rTensor_comul (hD : D.IsSubgroup E) (a : Γ(D.ideal.subscheme, ⊤)) :
    letI := E.subgroupAlgebra D
    LinearMap.rTensor Γ(D.ideal.subscheme, ⊤) (E.subgroupCounit hD).toLinearMap
        (E.subgroupComul hD a)
      = (1 : R) ⊗ₜ[R] a := by
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  -- uLAlg ∘ proj₂ = id
  have key2 : ∀ b, E.uLAlg hD (E.subgroupProj₂ (D := D) b) = b := by
    intro b
    show (E.uLmap hD).appTop.hom ((pullback.snd (D.ideal.subschemeι ≫ E.π)
        (D.ideal.subschemeι ≫ E.π)).appTop.hom b) = b
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      show E.uLmap hD ≫ pullback.snd (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)
        = 𝟙 _ from by rw [uLmap, pullback.lift_snd], Scheme.Hom.id_appTop, CommRingCat.id_apply]
  -- uLAlg ∘ proj₁ = algebraMap ∘ ε
  have key1 : ∀ b, E.uLAlg hD (E.subgroupProj₁ (D := D) b) = algebraMap R Γ(D.ideal.subscheme, ⊤)
      (E.subgroupCounit hD b) := by
    intro b
    show (E.uLmap hD).appTop.hom ((pullback.fst (D.ideal.subschemeι ≫ E.π)
        (D.ideal.subschemeι ≫ E.π)).appTop.hom b) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      show E.uLmap hD ≫ pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)
        = (D.ideal.subschemeι ≫ E.π) ≫ E.subgroupUnit hD from by rw [uLmap, pullback.lift_fst]]
    show ((E.subgroupUnit hD).appTop ≫ (D.ideal.subschemeι ≫ E.π).appTop).hom b = _
    show ((E.subgroupUnit hD).appTop ≫ (E.subgroupStructMap D).appTop).hom b
      = ((E.subgroupUnit hD).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom
          ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom b
    rw [Iso.hom_inv_id_assoc]
  -- intertwine: lid ∘ (ε ⊗ id) = uLAlg ∘ κ, as algebra homs A ⊗ A → A
  have intertwine : (Algebra.TensorProduct.lid R Γ(D.ideal.subscheme, ⊤)).toAlgHom.comp
        (Algebra.TensorProduct.map (E.subgroupCounit hD) (AlgHom.id R Γ(D.ideal.subscheme, ⊤)))
      = (E.uLAlg hD).comp (E.subgroupTensorCompare (D := D)) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    show Algebra.TensorProduct.lid R Γ(D.ideal.subscheme, ⊤) ((E.subgroupCounit hD x) ⊗ₜ[R] y)
      = E.uLAlg hD (E.subgroupTensorCompare (D := D) (x ⊗ₜ[R] y))
    rw [Algebra.TensorProduct.lid_tmul, subgroupTensorCompare, Algebra.TensorProduct.lift_tmul,
      map_mul, key1, key2, Algebra.smul_def]
  -- assemble
  have happ := DFunLike.congr_fun intertwine (E.subgroupComul hD a)
  rw [AlgHom.comp_apply, AlgHom.comp_apply, subgroupTensorCompare_subgroupComul] at happ
  have hunit : E.uLmap hD ≫ E.subgroupMul hD = 𝟙 D.ideal.subscheme := E.subgroupMul_unit_left hD
  have hcomul : E.uLAlg hD (E.subgroupComulHom hD a) = a := by
    show (E.uLmap hD).appTop.hom ((E.subgroupMul hD).appTop.hom a) = a
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hunit,
      Scheme.Hom.id_appTop, CommRingCat.id_apply]
  rw [hcomul] at happ
  have hmap : Algebra.TensorProduct.map (E.subgroupCounit hD)
      (AlgHom.id R Γ(D.ideal.subscheme, ⊤)) (E.subgroupComul hD a)
      = LinearMap.rTensor Γ(D.ideal.subscheme, ⊤) (E.subgroupCounit hD).toLinearMap
          (E.subgroupComul hD a) := rfl
  rw [hmap] at happ
  apply (Algebra.TensorProduct.lid R Γ(D.ideal.subscheme, ⊤)).injective
  rw [Algebra.TensorProduct.lid_tmul, one_smul]
  exact happ

/-- The `id × e` section `D ⟶ D ×_S D` (identity on the left factor, unit on the right).
Dualizing it gives the algebra hom that witnesses the right counit law. -/
noncomputable def uRmap (hD : D.IsSubgroup E) : D.ideal.subscheme ⟶
    pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) :=
  pullback.lift (𝟙 _) ((D.ideal.subschemeι ≫ E.π) ≫ E.subgroupUnit hD)
    (by rw [Category.id_comp, Category.assoc, E.subgroupUnit_over hD, Category.comp_id])

theorem uRmap_bimulBase (hD : D.IsSubgroup E) :
    E.uRmap hD ≫ E.bimulBase (D := D) = D.ideal.subschemeι ≫ E.π := by
  show E.uRmap hD ≫ (pullback.fst _ _ ≫ _) = _
  rw [← Category.assoc, uRmap, pullback.lift_fst, Category.id_comp]

/-- `uRmap.appTop` packaged as an `R`-algebra hom `Γ(D ×_S D) →ₐ Γ(D)`. -/
noncomputable def uRAlg (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    letI := E.biproductAlgebra (D := D)
    Γ(pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π), ⊤) →ₐ[R]
      Γ(D.ideal.subscheme, ⊤) :=
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  { (E.uRmap hD).appTop.hom with
    commutes' := fun r => by
      have hcomp :
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop) ≫
            (E.uRmap hD).appTop =
            (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop := by
        rw [Category.assoc, ← Scheme.Hom.comp_appTop, E.uRmap_bimulBase hD]
      show (E.uRmap hD).appTop.hom
          (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop).hom r) =
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom r
      rw [← CommRingCat.comp_apply, hcomp] }

/-- The right counit law for the subgroup Hopf structure: `(id ⊗ ε) ∘ Δ = · ⊗ 1`.
Mirror of `subgroupCounit_rTensor_comul`, dualizing `uRmap ≫ m = 𝟙`. -/
theorem subgroupCounit_lTensor_comul (hD : D.IsSubgroup E) (a : Γ(D.ideal.subscheme, ⊤)) :
    letI := E.subgroupAlgebra D
    LinearMap.lTensor Γ(D.ideal.subscheme, ⊤) (E.subgroupCounit hD).toLinearMap
        (E.subgroupComul hD a)
      = a ⊗ₜ[R] (1 : R) := by
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  -- uRAlg ∘ proj₁ = id
  have key1 : ∀ b, E.uRAlg hD (E.subgroupProj₁ (D := D) b) = b := by
    intro b
    show (E.uRmap hD).appTop.hom ((pullback.fst (D.ideal.subschemeι ≫ E.π)
        (D.ideal.subschemeι ≫ E.π)).appTop.hom b) = b
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      show E.uRmap hD ≫ pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)
        = 𝟙 _ from by rw [uRmap, pullback.lift_fst], Scheme.Hom.id_appTop, CommRingCat.id_apply]
  -- uRAlg ∘ proj₂ = algebraMap ∘ ε
  have key2 : ∀ b, E.uRAlg hD (E.subgroupProj₂ (D := D) b) = algebraMap R Γ(D.ideal.subscheme, ⊤)
      (E.subgroupCounit hD b) := by
    intro b
    show (E.uRmap hD).appTop.hom ((pullback.snd (D.ideal.subschemeι ≫ E.π)
        (D.ideal.subschemeι ≫ E.π)).appTop.hom b) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      show E.uRmap hD ≫ pullback.snd (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)
        = (D.ideal.subschemeι ≫ E.π) ≫ E.subgroupUnit hD from by rw [uRmap, pullback.lift_snd]]
    show ((E.subgroupUnit hD).appTop ≫ (D.ideal.subschemeι ≫ E.π).appTop).hom b = _
    show ((E.subgroupUnit hD).appTop ≫ (E.subgroupStructMap D).appTop).hom b
      = ((E.subgroupUnit hD).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom
          ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom b
    rw [Iso.hom_inv_id_assoc]
  -- intertwine: rid ∘ (id ⊗ ε) = uRAlg ∘ κ, as algebra homs A ⊗ A → A
  have intertwine : (Algebra.TensorProduct.rid R R Γ(D.ideal.subscheme, ⊤)).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id R Γ(D.ideal.subscheme, ⊤)) (E.subgroupCounit hD))
      = (E.uRAlg hD).comp (E.subgroupTensorCompare (D := D)) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    show Algebra.TensorProduct.rid R R Γ(D.ideal.subscheme, ⊤) (x ⊗ₜ[R] (E.subgroupCounit hD y))
      = E.uRAlg hD (E.subgroupTensorCompare (D := D) (x ⊗ₜ[R] y))
    rw [Algebra.TensorProduct.rid_tmul, subgroupTensorCompare, Algebra.TensorProduct.lift_tmul,
      map_mul, key1, key2, Algebra.smul_def, mul_comm]
  -- assemble
  have happ := DFunLike.congr_fun intertwine (E.subgroupComul hD a)
  rw [AlgHom.comp_apply, AlgHom.comp_apply, subgroupTensorCompare_subgroupComul] at happ
  have hunit : E.uRmap hD ≫ E.subgroupMul hD = 𝟙 D.ideal.subscheme := E.subgroupMul_unit_right hD
  have hcomul : E.uRAlg hD (E.subgroupComulHom hD a) = a := by
    show (E.uRmap hD).appTop.hom ((E.subgroupMul hD).appTop.hom a) = a
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hunit,
      Scheme.Hom.id_appTop, CommRingCat.id_apply]
  rw [hcomul] at happ
  have hmap : Algebra.TensorProduct.map (AlgHom.id R Γ(D.ideal.subscheme, ⊤))
      (E.subgroupCounit hD) (E.subgroupComul hD a)
      = LinearMap.lTensor Γ(D.ideal.subscheme, ⊤) (E.subgroupCounit hD).toLinearMap
          (E.subgroupComul hD a) := rfl
  rw [hmap] at happ
  apply (Algebra.TensorProduct.rid R R Γ(D.ideal.subscheme, ⊤)).injective
  rw [Algebra.TensorProduct.rid_tmul, one_smul]
  exact happ

/-- The `⟨n, id⟩` section `D ⟶ D ×_S D` (inversion on the left factor, identity on the right).
Dualizing it gives the algebra hom witnessing the left (`rTensor`) antipode law. -/
noncomputable def nLmap (hD : D.IsSubgroup E) : D.ideal.subscheme ⟶
    pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) :=
  pullback.lift (E.subgroupInv hD) (𝟙 _)
    (by rw [Category.id_comp]; exact E.subgroupInv_over hD)

theorem nLmap_bimulBase (hD : D.IsSubgroup E) :
    E.nLmap hD ≫ E.bimulBase (D := D) = D.ideal.subschemeι ≫ E.π := by
  show E.nLmap hD ≫ (pullback.fst _ _ ≫ _) = _
  rw [← Category.assoc, nLmap, pullback.lift_fst, E.subgroupInv_over hD]

/-- `nLmap.appTop` packaged as an `R`-algebra hom `Γ(D ×_S D) →ₐ Γ(D)`. -/
noncomputable def nLAlg (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    letI := E.biproductAlgebra (D := D)
    Γ(pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π), ⊤) →ₐ[R]
      Γ(D.ideal.subscheme, ⊤) :=
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  { (E.nLmap hD).appTop.hom with
    commutes' := fun r => by
      have hcomp :
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop) ≫
            (E.nLmap hD).appTop =
            (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop := by
        rw [Category.assoc, ← Scheme.Hom.comp_appTop, E.nLmap_bimulBase hD]
      show (E.nLmap hD).appTop.hom
          (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop).hom r) =
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom r
      rw [← CommRingCat.comp_apply, hcomp] }

/-- The left antipode law: `mul' ∘ (S ⊗ id) ∘ Δ = η ∘ ε`. Dualizes `nLmap ≫ m = e ∘ π`
(`subgroupMul_inv`) through the `κ`-intertwine. -/
theorem subgroupAntipode_rTensor_comul (hD : D.IsSubgroup E) (a : Γ(D.ideal.subscheme, ⊤)) :
    letI := E.subgroupAlgebra D
    LinearMap.mul' R Γ(D.ideal.subscheme, ⊤)
        (LinearMap.rTensor Γ(D.ideal.subscheme, ⊤) (E.subgroupAntipode hD).toLinearMap
          (E.subgroupComul hD a))
      = algebraMap R Γ(D.ideal.subscheme, ⊤) (E.subgroupCounit hD a) := by
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  have key1 : ∀ b, E.nLAlg hD (E.subgroupProj₁ (D := D) b) = E.subgroupAntipode hD b := by
    intro b
    show (E.nLmap hD).appTop.hom ((pullback.fst (D.ideal.subschemeι ≫ E.π)
        (D.ideal.subschemeι ≫ E.π)).appTop.hom b) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      show E.nLmap hD ≫ pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)
        = E.subgroupInv hD from by rw [nLmap, pullback.lift_fst]]
    rfl
  have key2 : ∀ b, E.nLAlg hD (E.subgroupProj₂ (D := D) b) = b := by
    intro b
    show (E.nLmap hD).appTop.hom ((pullback.snd (D.ideal.subschemeι ≫ E.π)
        (D.ideal.subschemeι ≫ E.π)).appTop.hom b) = b
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      show E.nLmap hD ≫ pullback.snd (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)
        = 𝟙 _ from by rw [nLmap, pullback.lift_snd], Scheme.Hom.id_appTop, CommRingCat.id_apply]
  have intertwine : (LinearMap.mul' R Γ(D.ideal.subscheme, ⊤)).comp
        (LinearMap.rTensor Γ(D.ideal.subscheme, ⊤) (E.subgroupAntipode hD).toLinearMap)
      = ((E.nLAlg hD).toLinearMap).comp ((E.subgroupTensorCompare (D := D)).toLinearMap) := by
    apply TensorProduct.ext'
    intro x y
    show LinearMap.mul' R Γ(D.ideal.subscheme, ⊤)
        (LinearMap.rTensor _ (E.subgroupAntipode hD).toLinearMap (x ⊗ₜ[R] y))
      = E.nLAlg hD (E.subgroupTensorCompare (D := D) (x ⊗ₜ[R] y))
    rw [LinearMap.rTensor_tmul, LinearMap.mul'_apply, subgroupTensorCompare,
      Algebra.TensorProduct.lift_tmul, map_mul, key1, key2, AlgHom.toLinearMap_apply]
  have happ := DFunLike.congr_fun intertwine (E.subgroupComul hD a)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    AlgHom.toLinearMap_apply, subgroupTensorCompare_subgroupComul] at happ
  have hunit : E.nLmap hD ≫ E.subgroupMul hD
      = (D.ideal.subschemeι ≫ E.π) ≫ E.subgroupUnit hD := E.subgroupMul_inv hD
  have hcomul : E.nLAlg hD (E.subgroupComulHom hD a)
      = algebraMap R Γ(D.ideal.subscheme, ⊤) (E.subgroupCounit hD a) := by
    show (E.nLmap hD).appTop.hom ((E.subgroupMul hD).appTop.hom a) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hunit]
    show ((E.subgroupUnit hD).appTop ≫ (D.ideal.subschemeι ≫ E.π).appTop).hom a = _
    show ((E.subgroupUnit hD).appTop ≫ (E.subgroupStructMap D).appTop).hom a
      = ((E.subgroupUnit hD).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom
          ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom a
    rw [Iso.hom_inv_id_assoc]
  rw [hcomul] at happ
  exact happ

/-- The `⟨id, n⟩` section `D ⟶ D ×_S D` (identity on the left factor, inversion on the right).
Dualizing it gives the algebra hom witnessing the right (`lTensor`) antipode law. -/
noncomputable def nRmap (hD : D.IsSubgroup E) : D.ideal.subscheme ⟶
    pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π) :=
  pullback.lift (𝟙 _) (E.subgroupInv hD)
    (by rw [Category.id_comp]; exact (E.subgroupInv_over hD).symm)

theorem nRmap_bimulBase (hD : D.IsSubgroup E) :
    E.nRmap hD ≫ E.bimulBase (D := D) = D.ideal.subschemeι ≫ E.π := by
  show E.nRmap hD ≫ (pullback.fst _ _ ≫ _) = _
  rw [← Category.assoc, nRmap, pullback.lift_fst, Category.id_comp]

/-- `nRmap.appTop` packaged as an `R`-algebra hom `Γ(D ×_S D) →ₐ Γ(D)`. -/
noncomputable def nRAlg (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    letI := E.biproductAlgebra (D := D)
    Γ(pullback (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π), ⊤) →ₐ[R]
      Γ(D.ideal.subscheme, ⊤) :=
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  { (E.nRmap hD).appTop.hom with
    commutes' := fun r => by
      have hcomp :
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop) ≫
            (E.nRmap hD).appTop =
            (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop := by
        rw [Category.assoc, ← Scheme.Hom.comp_appTop, E.nRmap_bimulBase hD]
      show (E.nRmap hD).appTop.hom
          (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.bimulBase (D := D)).appTop).hom r) =
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom r
      rw [← CommRingCat.comp_apply, hcomp] }

/-- The right antipode law: `mul' ∘ (id ⊗ S) ∘ Δ = η ∘ ε`. Dualizes `nRmap ≫ m = e ∘ π`
(`subgroupMul_inv'`) through the `κ`-intertwine. -/
theorem subgroupAntipode_lTensor_comul (hD : D.IsSubgroup E) (a : Γ(D.ideal.subscheme, ⊤)) :
    letI := E.subgroupAlgebra D
    LinearMap.mul' R Γ(D.ideal.subscheme, ⊤)
        (LinearMap.lTensor Γ(D.ideal.subscheme, ⊤) (E.subgroupAntipode hD).toLinearMap
          (E.subgroupComul hD a))
      = algebraMap R Γ(D.ideal.subscheme, ⊤) (E.subgroupCounit hD a) := by
  letI := E.subgroupAlgebra D
  letI := E.biproductAlgebra (D := D)
  have key1 : ∀ b, E.nRAlg hD (E.subgroupProj₁ (D := D) b) = b := by
    intro b
    show (E.nRmap hD).appTop.hom ((pullback.fst (D.ideal.subschemeι ≫ E.π)
        (D.ideal.subschemeι ≫ E.π)).appTop.hom b) = b
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      show E.nRmap hD ≫ pullback.fst (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)
        = 𝟙 _ from by rw [nRmap, pullback.lift_fst], Scheme.Hom.id_appTop, CommRingCat.id_apply]
  have key2 : ∀ b, E.nRAlg hD (E.subgroupProj₂ (D := D) b) = E.subgroupAntipode hD b := by
    intro b
    show (E.nRmap hD).appTop.hom ((pullback.snd (D.ideal.subschemeι ≫ E.π)
        (D.ideal.subschemeι ≫ E.π)).appTop.hom b) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      show E.nRmap hD ≫ pullback.snd (D.ideal.subschemeι ≫ E.π) (D.ideal.subschemeι ≫ E.π)
        = E.subgroupInv hD from by rw [nRmap, pullback.lift_snd]]
    rfl
  have intertwine : (LinearMap.mul' R Γ(D.ideal.subscheme, ⊤)).comp
        (LinearMap.lTensor Γ(D.ideal.subscheme, ⊤) (E.subgroupAntipode hD).toLinearMap)
      = ((E.nRAlg hD).toLinearMap).comp ((E.subgroupTensorCompare (D := D)).toLinearMap) := by
    apply TensorProduct.ext'
    intro x y
    show LinearMap.mul' R Γ(D.ideal.subscheme, ⊤)
        (LinearMap.lTensor _ (E.subgroupAntipode hD).toLinearMap (x ⊗ₜ[R] y))
      = E.nRAlg hD (E.subgroupTensorCompare (D := D) (x ⊗ₜ[R] y))
    rw [LinearMap.lTensor_tmul, LinearMap.mul'_apply, subgroupTensorCompare,
      Algebra.TensorProduct.lift_tmul, map_mul, key1, key2, AlgHom.toLinearMap_apply]
  have happ := DFunLike.congr_fun intertwine (E.subgroupComul hD a)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    AlgHom.toLinearMap_apply, subgroupTensorCompare_subgroupComul] at happ
  have hunit : E.nRmap hD ≫ E.subgroupMul hD
      = (D.ideal.subschemeι ≫ E.π) ≫ E.subgroupUnit hD := E.subgroupMul_inv' hD
  have hcomul : E.nRAlg hD (E.subgroupComulHom hD a)
      = algebraMap R Γ(D.ideal.subscheme, ⊤) (E.subgroupCounit hD a) := by
    show (E.nRmap hD).appTop.hom ((E.subgroupMul hD).appTop.hom a) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hunit]
    show ((E.subgroupUnit hD).appTop ≫ (D.ideal.subschemeι ≫ E.π).appTop).hom a = _
    show ((E.subgroupUnit hD).appTop ≫ (E.subgroupStructMap D).appTop).hom a
      = ((E.subgroupUnit hD).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom
          ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (E.subgroupStructMap D).appTop).hom a
    rw [Iso.hom_inv_id_assoc]
  rw [hcomul] at happ
  exact happ

/-- **(Layer B, L3 — the coalgebra.)** `A = Γ(D.subscheme, ⊤)` as an `R`-coalgebra: comultiplication
`Δ = subgroupComul`, counit `ε = subgroupCounit`; coassociativity (`subgroupComul_coassoc`) and the
two counit laws (`subgroupCounit_rTensor/lTensor_comul`) are the dualized group-scheme axioms. -/
@[reducible] noncomputable def subgroupCoalgebra (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    Coalgebra R Γ(D.ideal.subscheme, ⊤) :=
  letI := E.subgroupAlgebra D
  { comul := (E.subgroupComul hD).toLinearMap
    counit := (E.subgroupCounit hD).toLinearMap
    coassoc := LinearMap.ext fun a => E.subgroupComul_coassoc hD a
    rTensor_counit_comp_comul := LinearMap.ext fun a => E.subgroupCounit_rTensor_comul hD a
    lTensor_counit_comp_comul := LinearMap.ext fun a => E.subgroupCounit_lTensor_comul hD a }

/-- **(Layer B, L3 — the bialgebra.)** `Δ` and `ε` are algebra homs
(`subgroupComul`/`subgroupCounit`
are `AlgHom`s over `subgroupAlgebra`), so `A` is an `R`-bialgebra. -/
@[reducible] noncomputable def subgroupBialgebra (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    Bialgebra R Γ(D.ideal.subscheme, ⊤) :=
  letI := E.subgroupAlgebra D
  letI := E.subgroupCoalgebra hD
  Bialgebra.mk' R Γ(D.ideal.subscheme, ⊤)
    (map_one (E.subgroupCounit hD))
    (fun {a b} => map_mul (E.subgroupCounit hD) a b)
    (map_one (E.subgroupComul hD))
    (fun {a b} => map_mul (E.subgroupComul hD) a b)

/-- **(Layer B, L3 — the Hopf algebra.)** Antipode `S = subgroupAntipode`, dual to inversion; the
two
antipode axioms are the dualized inverse laws (`subgroupAntipode_rTensor/lTensor_comul`). `A` is a
commutative `R`-Hopf algebra — the coordinate Hopf algebra `A_D` of Deligne's argument. -/
@[reducible] noncomputable def subgroupHopfAlgebra (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    HopfAlgebra R Γ(D.ideal.subscheme, ⊤) :=
  letI := E.subgroupAlgebra D
  letI := E.subgroupBialgebra hD
  { antipode := (E.subgroupAntipode hD).toLinearMap
    mul_antipode_rTensor_comul :=
      LinearMap.ext fun a => E.subgroupAntipode_rTensor_comul hD a
    mul_antipode_lTensor_comul :=
      LinearMap.ext fun a => E.subgroupAntipode_lTensor_comul hD a }

/-- **(Layer B, L3 — cocommutativity.)** `A` is cocommutative (`comm ∘ Δ = Δ`,
`subgroupComul_comm`),
dualizing the commutativity of the elliptic-curve group law. Gives `IsCocomm R A`, the last
hypothesis Deligne's order theorem (`deligne_point_pow_eq_one`) needs on `A`. -/
theorem subgroupIsCocomm (hD : D.IsSubgroup E) :
    letI := E.subgroupAlgebra D
    letI := E.subgroupCoalgebra hD
    Coalgebra.IsCocomm R Γ(D.ideal.subscheme, ⊤) :=
  letI := E.subgroupAlgebra D
  letI := E.subgroupCoalgebra hD
  { comm_comp_comul := LinearMap.ext fun a => E.subgroupComul_comm hD a }

end AffineHopf

section GeneralBase

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- **(Layer B, L1 intermediate — section over a general base.)** The box for a *section*
`Q : E.Section` over an arbitrary base `S` (not yet assumed affine). Reduces to the affine core
`smul_eq_zero_of_factors_affine` by covering `S` with affine opens and using locality of morphism
equality on `S` (`(N : ℤ) • Q = 0 ↔ (N • Q).1 = 0.1 : S ⟶ E.E`, checkable on an affine cover; each
restriction is handled by the affine core after `Scheme.isoSpec`). The general box
`smul_eq_zero_of_factors'` in turn reduces to *this* by base-changing along `g : T ⟶ S`
(`Point.asSection`, `RelEffCartierDiv.IsSubgroup.baseChange`). -/
theorem smul_eq_zero_of_factors_section {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E) {N : ℕ}
    [NeZero N] (hdeg : ∀ s : S, D.degree s = N) (Q : E.Section)
    (hQ : ∃ h : S ⟶ D.ideal.subscheme, h ≫ D.ideal.subschemeι = Q.1) :
    (N : ℤ) • Q = 0 := by
  sorry

set_option backward.isDefEq.respectTransparency.types false in
/-- **(Layer B, L1 — the relative degree is base-change invariant.)** BOARDED `[T-D5h-degBC]`.
The degree (fibre `finrank` of the finite flat structure map `D.subscheme ⟶ S`) is stable under
base change: constant degree `N` on `S` gives constant degree `N` on any `T`. This is the
`finrank`-base-change fact for the finite locally free module, applied fibrewise
(`Module.finrank_baseChange` at the affine-local level; the fibre of `D.baseChange g` over `t`
is that of `D` over `g t`, base-changed to `κ(t)`). Sole genuinely-absent input to the L1
reduction below; everything else (factoring transport, `asSection` descent) is proven. -/
theorem degree_baseChange_apply (D : RelEffCartierDiv E.π) {T : Scheme.{u}} (g : T ⟶ S)
    (t : T) : (D.baseChange g).degree t = D.degree (g t) := by
  haveI := D.finite
  haveI := D.flat
  haveI : IsClosedImmersion (pullback.snd D.ideal.subschemeι (pullback.fst E.π g)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  -- the base-changed total space `D ×_S T` is the pasted pullback of `D.subscheme → S ← T`;
  -- its structure map (a closed immersion followed by `pullback.snd`) has the same fibre rank as
  -- the original structure map at `g t`, so degree is base-change invariant.
  have hsq := (IsPullback.of_hasPullback D.ideal.subschemeι
    (pullback.fst E.π g)).paste_vert (IsPullback.of_hasPullback E.π g)
  haveI hfin : IsFinite (pullback.snd D.ideal.subschemeι (pullback.fst E.π g)
      ≫ pullback.snd E.π g) := MorphismProperty.of_isPullback hsq D.finite
  haveI hfl : Flat (pullback.snd D.ideal.subschemeι (pullback.fst E.π g)
      ≫ pullback.snd E.π g) := MorphismProperty.of_isPullback hsq D.flat
  have hι : (pullback.snd D.ideal.subschemeι (pullback.fst E.π g)).ker.subschemeι
      = inv (pullback.snd D.ideal.subschemeι (pullback.fst E.π g)).toImage
        ≫ pullback.snd D.ideal.subschemeι (pullback.fst E.π g) := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  show ((D.baseChange g).ideal.subschemeι ≫ (E.baseChange g).π).finrank t = D.degree (g t)
  have hstruct : (D.baseChange g).ideal.subschemeι ≫ (E.baseChange g).π
      = inv (pullback.snd D.ideal.subschemeι (pullback.fst E.π g)).toImage
        ≫ (pullback.snd D.ideal.subschemeι (pullback.fst E.π g) ≫ pullback.snd E.π g) := by
    show (pullback.snd D.ideal.subschemeι (pullback.fst E.π g)).ker.subschemeι
        ≫ pullback.snd E.π g = _
    rw [hι, Category.assoc]
  have h1 : Scheme.Hom.finrank
        (inv (pullback.snd D.ideal.subschemeι (pullback.fst E.π g)).toImage
          ≫ (pullback.snd D.ideal.subschemeι (pullback.fst E.π g) ≫ pullback.snd E.π g))
      = Scheme.Hom.finrank
          (pullback.snd D.ideal.subschemeι (pullback.fst E.π g) ≫ pullback.snd E.π g) :=
    Scheme.Hom.finrank_comp_left_of_isIso _ _
  have h2 := Scheme.Hom.finrank_of_isPullback _ _ _ _ hsq t
  rw [hstruct]
  exact (congrFun h1 t).trans h2

/-- **(Layer B, L1 — the relative degree is base-change invariant.)** BOARDED `[T-D5h-degBC]`.
Constant degree `N` on `S` gives constant degree `N` on any `T` (the pointwise
`degree_baseChange_apply`). -/
theorem degree_baseChange_eq {D : RelEffCartierDiv E.π} {N : ℕ}
    (hdeg : ∀ s : S, D.degree s = N) {T : Scheme.{u}} (g : T ⟶ S) (t : T) :
    (D.baseChange g).degree t = N :=
  (degree_baseChange_apply E D g t).trans (hdeg (g t))

/-- **(Layer B, L1 + assembly — the box.)** Deligne's order theorem in the project's
subgroup-divisor encoding, over an arbitrary base `S` and for an arbitrary `T`-point `Q`
(the statement of `RelEffCartierDiv.IsSubgroup.smul_eq_zero_of_factors`,
`LevelStructure/ExactOrder.lean`). Reduces to the affine core `smul_eq_zero_of_factors_affine`:
`(N : ℤ) • Q = 0` is stable under base change (`RelEffCartierDiv.IsSubgroup.baseChange`,
`Point.pull_zsmul`/`_zero`) and local on `S`, so one may assume `S = Spec R` affine and `Q` a
section. Once landed sorry-free this discharges the `ExactOrder.lean` box (final wiring step). -/
theorem smul_eq_zero_of_factors' {D : RelEffCartierDiv E.π} (hD : D.IsSubgroup E) {N : ℕ}
    [NeZero N] (hdeg : ∀ s : S, D.degree s = N) {T : Scheme.{u}} (g : T ⟶ S) (Q : E.Point g)
    (hQ : ∃ h : T ⟶ D.ideal.subscheme, h ≫ D.ideal.subschemeι = Q.1) :
    (N : ℤ) • Q = 0 := by
  -- Base-change along `g : T ⟶ S`. `Q` becomes the section `asSection Q` of `E ×_S T / T`, `D`
  -- becomes the subgroup divisor `D.baseChange g` (`IsSubgroup.baseChange`) of constant degree `N`
  -- (`degree_baseChange_eq`), and `asSection Q` factors through it (`exists_factor_comap_iff` +
  -- `asSection_val_fst`). The section box kills it; `asSection`, injective and `zsmul`-linear,
  -- descends the vanishing back to `Q`.
  have hfac : ∃ h : T ⟶ (D.baseChange g).ideal.subscheme,
      h ≫ (D.baseChange g).ideal.subschemeι = (Point.asSection E g Q).1 := by
    rw [RelEffCartierDiv.baseChange_ideal]
    refine (AlgebraicGeometry.Scheme.IdealSheafData.exists_factor_comap_iff D.ideal
      (Limits.pullback.fst E.π g) (Point.asSection E g Q).1).mpr ?_
    obtain ⟨h, hh⟩ := hQ
    exact ⟨h, hh.trans (Point.asSection_val_fst E g Q).symm⟩
  have hbc : (N : ℤ) • Point.asSection E g Q = 0 :=
    smul_eq_zero_of_factors_section (E.baseChange g)
      (RelEffCartierDiv.IsSubgroup.baseChange E hD g)
      (fun t => degree_baseChange_eq E hdeg g t) (Point.asSection E g Q) hfac
  -- `asSection` is injective and intertwines `zsmul`, and sends `0` to `0`.
  have hzero : Point.asSection E g (0 : E.Point g) = 0 := by
    have h := Point.asSection_zsmul E g 0 (0 : E.Point g)
    rwa [zero_zsmul, zero_zsmul] at h
  have hinj : Function.Injective (Point.asSection E g) := by
    intro P P' hPP'
    apply Subtype.ext
    have h := congrArg
      (fun s : (E.baseChange g).Point (𝟙 T) => s.1 ≫ Limits.pullback.fst E.π g) hPP'
    simpa only [Point.asSection_val_fst] using h
  exact hinj (by rw [Point.asSection_zsmul, hbc, hzero])

end GeneralBase

end EllipticCurve

end ModularCurves

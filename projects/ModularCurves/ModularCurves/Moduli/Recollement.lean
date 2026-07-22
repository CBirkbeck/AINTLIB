/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.ProblemBaseChange
import ModularCurves.Moduli.QuotientProblem
import ModularCurves.Moduli.Stack
import ModularCurves.EllipticCurve.GroupLawDescent
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# [T-E5f] The Katz–Mazur recollement theorem

Representability of a moduli problem glued from its base-changes over a Zariski cover of
`Spec R` (Katz–Mazur Cor. 4.7.1: `𝕸(𝒫)⊗ℤ[1/2] = 𝕸(𝒫,Legendre)/G`,
`𝕸(𝒫)⊗ℤ[1/3] = 𝕸(𝒫,naive-3)/G`, glued over `ℤ[1/6]` since `Spec ℤ = D(2) ∪ D(3)`).

This file contains the abstract recollement infrastructure on `ModularCurves.EllObj`:

* **[R-comp]** base-change composition `EllObj.restrictScalars_comp` /
  `ModuliProblem.baseChange_comp` — **fully proven**.
* the localization ring maps `R ⟶ R[1/a]` and the Bézout ⟹ Zariski-cover bridge —
  **fully proven**.
* **[T-E5f-main]** `representable_of_baseChange_cover` — **stated**; the proof (the
  Scheme-gluing recollement of the two representing `Ell`-objects) is decomposed in the
  docstring and left as the outstanding engine gap.
-/


/-!
# The Katz–Mazur recollement ([T-E5f], KM Cor 4.7.1)

`representable_of_baseChange_cover`: a moduli problem `P` over `R` representable after base change to
`R[1/a]` and to `R[1/b]`, for `a, b` generating the unit ideal (so `Spec R = D(a) ∪ D(b)`), is
representable over `R` — glue the two representing objects over `D(ab)`. Stated consumable for the
`Y(N)` assembly (instantiate `a = 2` Legendre, `b = 3` naive level 3).

* `EllObj.restrictScalars_comp` / `ModuliProblem.baseChange_comp` — base-change functoriality [R-comp].
* `awayHom`, `EllObj.baseChangeRing`, `basicOpen_sup_basicOpen_eq_top` — the gluing primitives.
* `representable_of_baseChange_cover` — the recollement (the group-scheme Zariski-gluing core is WIP:
  mathlib has no group-scheme-gluing API, so [R-glue-obj] is a from-scratch development).
-/

open CategoryTheory AlgebraicGeometry Opposite Limits

universe u

namespace ModularCurves

variable {R R' R'' : CommRingCat.{u}}

/-! ## EllHom projection helpers

These push `baseHom`/`top` through composition and `eqToHom`, and give a heterogeneous
ext lemma; they are the bureaucracy that makes functor equalities on `Ell/R` provable. -/

@[simp]
theorem EllHom.comp_baseHom {X Y Z : EllObj R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).baseHom = f.baseHom ≫ g.baseHom := rfl

@[simp]
theorem EllHom.comp_top {X Y Z : EllObj R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).top = f.top ≫ g.top := rfl

@[simp]
theorem EllHom.eqToHom_baseHom {X Y : EllObj R} (h : X = Y) :
    (eqToHom h).baseHom = eqToHom (congrArg EllObj.base h) := by subst h; rfl

@[simp]
theorem EllHom.eqToHom_top {X Y : EllObj R} (h : X = Y) :
    (eqToHom h).top = eqToHom (congrArg (fun Z => Z.curve.E) h) := by subst h; rfl

/-- A heterogeneous ext for `EllHom`: two morphisms over equal source/target objects agree
if their `baseHom` and `top` agree (heterogeneously). -/
theorem EllHom.hext {X Y X' Y' : EllObj R} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (hb : HEq f.baseHom g.baseHom) (ht : HEq f.top g.top) :
    HEq f g := by
  subst hX; subst hY
  exact heq_of_eq (EllHom.ext (eq_of_heq hb) (eq_of_heq ht))

/-! ## [R-comp] base-change composition -/

variable (ρ : R ⟶ R') (σ : R' ⟶ R'')

/-- **[R-comp] Base-change composition.** Restriction of scalars along `ρ ≫ σ` is
restriction along `σ` followed by restriction along `ρ` (same base scheme and curve, the
structure maps compose via `Spec.map_comp`). -/
theorem EllObj.restrictScalars_comp :
    EllObj.restrictScalars (ρ ≫ σ) =
      EllObj.restrictScalars σ ⋙ EllObj.restrictScalars ρ := by
  have hobj : ∀ X : EllObj R'',
      (EllObj.restrictScalars (ρ ≫ σ)).obj X
        = (EllObj.restrictScalars σ ⋙ EllObj.restrictScalars ρ).obj X := fun X => by
    show EllObj.mk X.base (X.structMap ≫ Spec.map (ρ ≫ σ)) X.curve =
        EllObj.mk X.base ((X.structMap ≫ Spec.map σ) ≫ Spec.map ρ) X.curve
    rw [Spec.map_comp, ← Category.assoc]
  refine CategoryTheory.Functor.hext hobj (fun X Y f =>
    EllHom.hext (hobj X) (hobj Y) ?_ ?_)
  · exact heq_of_eq (by simp only [Functor.comp_map, EllObj.restrictScalars_map_baseHom])
  · exact heq_of_eq (by simp only [Functor.comp_map, EllObj.restrictScalars_map_top])

/-- **[R-comp] Base-change composition for moduli problems.**
`P.baseChange (ρ ≫ σ) = (P.baseChange ρ).baseChange σ`. This is what identifies both
`P.baseChange`s to `R[1/ab]` in the recollement (the overlap `D(ab) = D(a) ∩ D(b)`), so the
two representing objects agree there by uniqueness of representing objects. -/
theorem ModuliProblem.baseChange_comp (P : ModuliProblem R) :
    P.baseChange (ρ ≫ σ) = (P.baseChange ρ).baseChange σ := by
  unfold ModuliProblem.baseChange
  rw [EllObj.restrictScalars_comp]
  rfl

/-! ## Localization ring maps and the Zariski cover -/

/-- The structural ring map `R ⟶ R[1/a] = Localization.Away a`. -/
noncomputable def awayHom (a : R) : R ⟶ CommRingCat.of (Localization.Away a) :=
  CommRingCat.ofHom (algebraMap R (Localization.Away a))

/-- **[T-E5f-g-away]** The localization map `R[1/a] ⟶ R[1/(a*b)]` (inverting the extra factor
`b`); the overlap `D(ab) ⊆ D(a)`. -/
noncomputable def awayProdHomLeft (a b : R) :
    CommRingCat.of (Localization.Away a) ⟶ CommRingCat.of (Localization.Away (a * b)) :=
  CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight a b)

/-- **[T-E5f-g-away]** The localization map `R[1/b] ⟶ R[1/(a*b)]` (inverting the extra factor
`a`); the overlap `D(ab) ⊆ D(b)`. -/
noncomputable def awayProdHomRight (a b : R) :
    CommRingCat.of (Localization.Away b) ⟶ CommRingCat.of (Localization.Away (a * b)) :=
  CommRingCat.ofHom (IsLocalization.Away.awayToAwayLeft b a)

/-- The `a`-tower commutes: `R ⟶ R[1/a] ⟶ R[1/(a*b)]` equals `R ⟶ R[1/(a*b)]`. -/
theorem awayHom_comp_awayProdHomLeft (a b : R) :
    awayHom a ≫ awayProdHomLeft a b = awayHom (a * b) := by
  ext r
  exact IsLocalization.Away.awayToAwayRight_eq a b r

/-- The `b`-tower commutes: `R ⟶ R[1/b] ⟶ R[1/(a*b)]` equals `R ⟶ R[1/(a*b)]`. -/
theorem awayHom_comp_awayProdHomRight (a b : R) :
    awayHom b ≫ awayProdHomRight a b = awayHom (a * b) := by
  ext r
  exact IsLocalization.Away.awayToAwayLeft_eq b a r

/-- `Spec.map (awayHom a)` is an open immersion (`D(a) ↪ Spec R`). -/
instance isOpenImmersion_SpecMap_awayHom (a : R) : IsOpenImmersion (Spec.map (awayHom a)) :=
  Scheme.isOpenImmersion_SpecMap_localizationAway a

/-- **The overlap inclusion `D(ab) ↪ D(a)` is an open immersion.** Proved by cancelling the open
immersion `D(a) ↪ Spec R` from the open immersion `D(ab) ↪ Spec R` (the tower factors). -/
instance isOpenImmersion_SpecMap_awayProdHomLeft (a b : R) :
    IsOpenImmersion (Spec.map (awayProdHomLeft a b)) := by
  haveI : IsOpenImmersion (Spec.map (awayProdHomLeft a b) ≫ Spec.map (awayHom a)) := by
    rw [← Spec.map_comp, awayHom_comp_awayProdHomLeft]
    infer_instance
  exact IsOpenImmersion.of_comp _ (Spec.map (awayHom a))

/-- **The overlap inclusion `D(ab) ↪ D(b)` is an open immersion.** -/
instance isOpenImmersion_SpecMap_awayProdHomRight (a b : R) :
    IsOpenImmersion (Spec.map (awayProdHomRight a b)) := by
  haveI : IsOpenImmersion (Spec.map (awayProdHomRight a b) ≫ Spec.map (awayHom b)) := by
    rw [← Spec.map_comp, awayHom_comp_awayProdHomRight]
    infer_instance
  exact IsOpenImmersion.of_comp _ (Spec.map (awayHom b))

/-- **Base change of an `Ell`-object along a ring map** `τ : R' ⟶ R''`: pull the base scheme
back along `Spec.map τ` and base-change the curve. This is the left-adjoint direction to
`EllObj.restrictScalars τ`; it is used to compare the two representing objects over `R[1/ab]`
in the recollement (the [compat] step — `Xₐ` and `X_b` both base-change to representatives of
`P.baseChange (away ab)`, hence agree). -/
@[simps]
noncomputable def EllObj.baseChangeRing (X : EllObj R') (τ : R' ⟶ R'') : EllObj R'' where
  base := pullback X.structMap (Spec.map τ)
  structMap := pullback.snd X.structMap (Spec.map τ)
  curve := X.curve.baseChange (pullback.fst X.structMap (Spec.map τ))

/-- **Bézout ⟹ Zariski cover.** If `x·a + y·b = 1` then the basic opens `D(a)` and `D(b)`
cover `Spec R`. This is the geometric content of the recollement hypothesis
(`Spec ℤ = D(2) ∪ D(3)` for `x·2 + y·3 = 1`). -/
theorem basicOpen_sup_basicOpen_eq_top (a b : R) (hab : ∃ x y : R, x * a + y * b = 1) :
    PrimeSpectrum.basicOpen a ⊔ PrimeSpectrum.basicOpen b = ⊤ := by
  obtain ⟨x, y, hxy⟩ := hab
  have hspan : Ideal.span ({a, b} : Set R) = ⊤ := by
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_pair]
    exact ⟨x, y, hxy⟩
  have hcover := (PrimeSpectrum.iSup_basicOpen_eq_top_iff' (s := ({a, b} : Set R))).mpr hspan
  rw [← hcover, iSup_pair]

/-! ## [T-E5f-g0] the base-change ⊣ restrict-scalars hom-equivalence

For `X : Ell/R'` and a ring map `τ : R' ⟶ R''`, morphisms `Y ⟶ X.baseChangeRing τ` in `Ell/R''`
biject naturally with morphisms `(restrictScalars τ) Y ⟶ X` in `Ell/R'`. This is the universal
property of `baseChangeRing` as a pullback — the base-change ⊣ restrict-scalars adjunction — and is
the primitive from which representability transfers under base change, giving the gluing datum over
`D(ab)` in the recollement. -/

section BaseChangeAdjunction

variable {R' R'' : CommRingCat.{u}}

set_option backward.isDefEq.respectTransparency false

/-- The zero section of the ring-base-changed curve, composed with the first projection, is the
base pullback map composed with the original zero section. -/
theorem baseChangeRing_curve_zero_comp_fst (X : EllObj R') (τ : R' ⟶ R'') :
    (X.baseChangeRing τ).curve.zero ≫
        pullback.fst X.curve.π (pullback.fst X.structMap (Spec.map τ))
      = pullback.fst X.structMap (Spec.map τ) ≫ X.curve.zero :=
  pullback.lift_fst _ _ _

/-- The zero section of the ring-base-changed curve, composed with the second projection, is the
identity (it is a section of `π`). -/
theorem baseChangeRing_curve_zero_comp_snd (X : EllObj R') (τ : R' ⟶ R'') :
    (X.baseChangeRing τ).curve.zero ≫
        pullback.snd X.curve.π (pullback.fst X.structMap (Spec.map τ))
      = 𝟙 (X.baseChangeRing τ).base :=
  pullback.lift_snd _ _ _

/-! ### Forward map -/

/-- Forward map of the base-change hom-equivalence: post-compose the base and curve legs of
`f : Y ⟶ X.baseChangeRing τ` with the pullback first-projections. -/
@[simps]
noncomputable def baseChangeRingHomEquivFwd (X : EllObj R') (τ : R' ⟶ R'') (Y : EllObj R'')
    (f : Y ⟶ X.baseChangeRing τ) : (EllObj.restrictScalars τ).obj Y ⟶ X where
  baseHom := f.baseHom ≫ pullback.fst X.structMap (Spec.map τ)
  base_w := by
    have hbw : f.baseHom ≫ pullback.snd X.structMap (Spec.map τ) = Y.structMap := f.base_w
    show (f.baseHom ≫ pullback.fst X.structMap (Spec.map τ)) ≫ X.structMap
      = Y.structMap ≫ Spec.map τ
    rw [Category.assoc, pullback.condition, ← Category.assoc, hbw]
  top := f.top ≫ pullback.fst X.curve.π (pullback.fst X.structMap (Spec.map τ))
  isPullback :=
    f.isPullback.paste_horiz
      (IsPullback.of_hasPullback X.curve.π (pullback.fst X.structMap (Spec.map τ)))
  zero_w := by
    have hz : Y.curve.zero ≫ f.top = f.baseHom ≫ (X.baseChangeRing τ).curve.zero := f.zero_w
    show Y.curve.zero ≫ f.top ≫ pullback.fst X.curve.π (pullback.fst X.structMap (Spec.map τ))
      = (f.baseHom ≫ pullback.fst X.structMap (Spec.map τ)) ≫ X.curve.zero
    rw [← Category.assoc, hz, Category.assoc, Category.assoc]
    congr 1
    exact pullback.lift_fst _ _ _

/-! ### Inverse map (via base/curve pullback lifts) -/

/-- Base leg of the inverse map: lift `g.baseHom` and `Y.structMap` through the base pullback. -/
noncomputable def bcInvBase (X : EllObj R') (τ : R' ⟶ R'') (Y : EllObj R'')
    (g : (EllObj.restrictScalars τ).obj Y ⟶ X) : Y.base ⟶ (X.baseChangeRing τ).base :=
  pullback.lift g.baseHom Y.structMap g.base_w

@[simp]
theorem bcInvBase_fst (X : EllObj R') (τ : R' ⟶ R'') (Y : EllObj R'')
    (g : (EllObj.restrictScalars τ).obj Y ⟶ X) :
    bcInvBase X τ Y g ≫ pullback.fst X.structMap (Spec.map τ) = g.baseHom :=
  pullback.lift_fst _ _ _

@[simp]
theorem bcInvBase_snd (X : EllObj R') (τ : R' ⟶ R'') (Y : EllObj R'')
    (g : (EllObj.restrictScalars τ).obj Y ⟶ X) :
    bcInvBase X τ Y g ≫ pullback.snd X.structMap (Spec.map τ) = Y.structMap :=
  pullback.lift_snd _ _ _

/-- Curve leg of the inverse map: lift `g.top` and `Y.curve.π ≫ bcInvBase` through the curve
pullback. -/
noncomputable def bcInvTop (X : EllObj R') (τ : R' ⟶ R'') (Y : EllObj R'')
    (g : (EllObj.restrictScalars τ).obj Y ⟶ X) : Y.curve.E ⟶ (X.baseChangeRing τ).curve.E :=
  pullback.lift g.top (Y.curve.π ≫ bcInvBase X τ Y g) (by
    have hgw : g.top ≫ X.curve.π = Y.curve.π ≫ g.baseHom := g.isPullback.w
    rw [Category.assoc, bcInvBase_fst]; exact hgw)

@[simp]
theorem bcInvTop_fst (X : EllObj R') (τ : R' ⟶ R'') (Y : EllObj R'')
    (g : (EllObj.restrictScalars τ).obj Y ⟶ X) :
    bcInvTop X τ Y g ≫ pullback.fst X.curve.π (pullback.fst X.structMap (Spec.map τ)) = g.top :=
  pullback.lift_fst _ _ _

@[simp]
theorem bcInvTop_snd (X : EllObj R') (τ : R' ⟶ R'') (Y : EllObj R'')
    (g : (EllObj.restrictScalars τ).obj Y ⟶ X) :
    bcInvTop X τ Y g ≫ pullback.snd X.curve.π (pullback.fst X.structMap (Spec.map τ))
      = Y.curve.π ≫ bcInvBase X τ Y g :=
  pullback.lift_snd _ _ _

/-- Inverse map of the base-change hom-equivalence. -/
@[simps]
noncomputable def baseChangeRingHomEquivInv (X : EllObj R') (τ : R' ⟶ R'') (Y : EllObj R'')
    (g : (EllObj.restrictScalars τ).obj Y ⟶ X) : Y ⟶ X.baseChangeRing τ where
  baseHom := bcInvBase X τ Y g
  base_w := bcInvBase_snd X τ Y g
  top := bcInvTop X τ Y g
  isPullback := by
    have hgpb : IsPullback g.top Y.curve.π X.curve.π g.baseHom := g.isPullback
    refine IsPullback.of_right
      (h₁₂ := pullback.fst X.curve.π (pullback.fst X.structMap (Spec.map τ)))
      ?_ (bcInvTop_snd X τ Y g)
      (IsPullback.of_hasPullback X.curve.π (pullback.fst X.structMap (Spec.map τ)))
    rw [bcInvTop_fst, bcInvBase_fst]; exact hgpb
  zero_w := by
    have hgz : Y.curve.zero ≫ g.top = g.baseHom ≫ X.curve.zero := g.zero_w
    apply pullback.hom_ext
    · rw [Category.assoc, bcInvTop_fst, Category.assoc, baseChangeRing_curve_zero_comp_fst,
        hgz, ← bcInvBase_fst, Category.assoc]
    · rw [Category.assoc, bcInvTop_snd, Category.assoc, baseChangeRing_curve_zero_comp_snd,
        Category.comp_id, ← Category.assoc, Y.curve.zero_π, Category.id_comp]

/-! ### The hom-equivalence -/

/-- **[T-E5f-g0]** The base-change ⊣ restrict-scalars hom-equivalence. -/
noncomputable def baseChangeRingHomEquiv (X : EllObj R') (τ : R' ⟶ R'') (Y : EllObj R'') :
    (Y ⟶ X.baseChangeRing τ) ≃ ((EllObj.restrictScalars τ).obj Y ⟶ X) where
  toFun := baseChangeRingHomEquivFwd X τ Y
  invFun := baseChangeRingHomEquivInv X τ Y
  left_inv f := by
    have hbase : bcInvBase X τ Y (baseChangeRingHomEquivFwd X τ Y f) = f.baseHom := by
      apply pullback.hom_ext
      · rw [bcInvBase_fst, baseChangeRingHomEquivFwd_baseHom]
      · rw [bcInvBase_snd]
        exact f.base_w.symm
    refine EllHom.ext hbase ?_
    apply pullback.hom_ext
    · rw [baseChangeRingHomEquivInv_top, bcInvTop_fst, baseChangeRingHomEquivFwd_top]
    · rw [baseChangeRingHomEquivInv_top, bcInvTop_snd, hbase]
      exact f.isPullback.w.symm
  right_inv g := by
    refine EllHom.ext ?_ ?_
    · rw [baseChangeRingHomEquivFwd_baseHom, baseChangeRingHomEquivInv_baseHom, bcInvBase_fst]
    · rw [baseChangeRingHomEquivFwd_top, baseChangeRingHomEquivInv_top, bcInvTop_fst]

/-! ### [T-E5f-g-transfer] representability transfers under base change -/

/-- The forward map is natural: it commutes with precomposition by `(restrictScalars τ).map`. -/
theorem baseChangeRingHomEquivFwd_comp (X : EllObj R') (τ : R' ⟶ R'') {Y' Y : EllObj R''}
    (f : Y' ⟶ Y) (g : Y ⟶ X.baseChangeRing τ) :
    baseChangeRingHomEquivFwd X τ Y' (f ≫ g)
      = (EllObj.restrictScalars τ).map f ≫ baseChangeRingHomEquivFwd X τ Y g := by
  apply EllHom.ext
  · simp only [baseChangeRingHomEquivFwd_baseHom, EllHom.comp_baseHom,
      EllObj.restrictScalars_map_baseHom, Category.assoc]
  · simp only [baseChangeRingHomEquivFwd_top, EllHom.comp_top,
      EllObj.restrictScalars_map_top, Category.assoc]

/-- **[T-E5f-g-transfer]** Representability transfers under base change: if `X` represents `Q`
over `R'`, then `X.baseChangeRing τ` represents `Q.baseChange τ` over `R''`. This is the
gluing datum over `D(ab)` in the recollement. -/
noncomputable def representableBy_baseChangeRing {Q : ModuliProblem R'} {X : EllObj R'}
    (h : Q.RepresentableBy X) (τ : R' ⟶ R'') :
    (Q.baseChange τ).RepresentableBy (X.baseChangeRing τ) where
  homEquiv {Y} := (baseChangeRingHomEquiv X τ Y).trans h.homEquiv
  homEquiv_comp {Y' Y} f g := by
    show h.homEquiv (baseChangeRingHomEquivFwd X τ Y' (f ≫ g))
      = (Q.baseChange τ).map f.op (h.homEquiv (baseChangeRingHomEquivFwd X τ Y g))
    rw [baseChangeRingHomEquivFwd_comp, h.homEquiv_comp]
    rfl

end BaseChangeAdjunction

/-! ## [T-E5f-g-uniq] the overlap iso over `D(ab)` -/

/-- **[T-E5f-g-uniq]** The overlap iso: the two representing objects, base-changed to
`R[1/(a*b)]`, are canonically isomorphic — both represent `P.baseChange (awayHom (a*b))` (by the
localization tower `awayHom a ≫ awayProdHomLeft = awayHom (a*b)` and `representableBy_baseChangeRing`).
This is the gluing datum over the overlap `D(ab) = D(a) ∩ D(b)` in the recollement. -/
noncomputable def overlapIso {P : ModuliProblem R} (a b : R)
    {Xa : EllObj (CommRingCat.of (Localization.Away a))}
    {Xb : EllObj (CommRingCat.of (Localization.Away b))}
    (repr_a : (P.baseChange (awayHom a)).RepresentableBy Xa)
    (repr_b : (P.baseChange (awayHom b)).RepresentableBy Xb) :
    Xa.baseChangeRing (awayProdHomLeft a b) ≅ Xb.baseChangeRing (awayProdHomRight a b) :=
  have e_a : (P.baseChange (awayHom a)).baseChange (awayProdHomLeft a b)
      = P.baseChange (awayHom (a * b)) := by
    rw [← ModuliProblem.baseChange_comp, awayHom_comp_awayProdHomLeft]
  have e_b : (P.baseChange (awayHom b)).baseChange (awayProdHomRight a b)
      = P.baseChange (awayHom (a * b)) := by
    rw [← ModuliProblem.baseChange_comp, awayHom_comp_awayProdHomRight]
  ((representableBy_baseChangeRing repr_a (awayProdHomLeft a b)).ofIso
      (eqToIso e_a)).uniqueUpToIso
    ((representableBy_baseChangeRing repr_b (awayProdHomRight a b)).ofIso (eqToIso e_b))

/-! ## [R-glue-obj] Two-chart Zariski gluing (pushouts of open immersions)

The pushout of a span of open immersions exists in `Scheme` — a `WidePushoutShape`-diagram of
open immersions is a locally directed diagram, so mathlib's locally-directed gluing
(`AlgebraicGeometry.Scheme.IsLocallyDirected`) provides the colimit with open-immersion
coprojections — and the two coprojections are jointly surjective and are identified exactly
along the span apex.  This is the entire (`Scheme.GlueData`-free) glue engine for
[R-glue-obj]: `Spec R = D(a) ∪ D(b)` glues the two representing objects as the pushout of
their overlap. -/

section TwoChartGlue

variable {W A B : Scheme.{u}} (f : W ⟶ A) (g : W ⟶ B)

private theorem isOpenImmersion_span_map [IsOpenImmersion f] [IsOpenImmersion g] :
    ∀ {i j : WalkingSpan} (h : i ⟶ j), IsOpenImmersion ((span f g).map h) := by
  intro i j h
  cases h with
  | id i => rw [span_map_id]; infer_instance
  | init j =>
    cases j with
    | left => rw [show (span f g).map (WidePushoutShape.Hom.init WalkingPair.left) = f from
        span_map_fst f g]; assumption
    | right => rw [show (span f g).map (WidePushoutShape.Hom.init WalkingPair.right) = g from
        span_map_snd f g]; assumption

variable [IsOpenImmersion f] [IsOpenImmersion g]

private instance hasPushout_of_isOpenImmersion : HasPushout f g :=
  haveI : ∀ {i j : WalkingSpan} (h : i ⟶ j), IsOpenImmersion ((span f g).map h) :=
    isOpenImmersion_span_map f g
  inferInstanceAs (HasColimit (span f g))

private instance isOpenImmersion_pushout_inl : IsOpenImmersion (pushout.inl f g) :=
  haveI : ∀ {i j : WalkingSpan} (h : i ⟶ j), IsOpenImmersion ((span f g).map h) :=
    isOpenImmersion_span_map f g
  inferInstanceAs (IsOpenImmersion (colimit.ι (span f g) WalkingSpan.left))

private instance isOpenImmersion_pushout_inr : IsOpenImmersion (pushout.inr f g) :=
  haveI : ∀ {i j : WalkingSpan} (h : i ⟶ j), IsOpenImmersion ((span f g).map h) :=
    isOpenImmersion_span_map f g
  inferInstanceAs (IsOpenImmersion (colimit.ι (span f g) WalkingSpan.right))

/-- Points of the two charts of the pushout of open immersions are identified exactly along
the apex: `inl x = inr y` iff both come from a common point of `W`. -/
private theorem pushout_inl_eq_inr_iff (x : A) (y : B) :
    pushout.inl f g x = pushout.inr f g y ↔ ∃ w : W, f w = x ∧ g w = y := by
  haveI : ∀ {i j : WalkingSpan} (h : i ⟶ j), IsOpenImmersion ((span f g).map h) :=
    isOpenImmersion_span_map f g
  have hiff := Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span f g)
    (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x) (xj := y)
  constructor
  · intro h
    obtain ⟨k, fi, fj, z, hz1, hz2⟩ := hiff.mp h
    cases fi with
    | id i => cases fj
    | init j =>
      cases fj with
      | init j' =>
        exact ⟨z, (congr($(span_map_fst f g) z)).symm.trans hz1,
          (congr($(span_map_snd f g) z)).symm.trans hz2⟩
  · rintro ⟨w, hw1, hw2⟩
    exact hiff.mpr
      ⟨WalkingSpan.zero, WalkingSpan.Hom.fst, WalkingSpan.Hom.snd, w,
        (congr($(span_map_fst f g) w)).trans hw1, (congr($(span_map_snd f g) w)).trans hw2⟩

/-- The two charts of the pushout of open immersions are jointly surjective. -/
private theorem pushout_exists_inl_or_inr (x : ↑(pushout f g)) :
    (∃ u : A, pushout.inl f g u = x) ∨ (∃ v : B, pushout.inr f g v = x) := by
  haveI : ∀ {i j : WalkingSpan} (h : i ⟶ j), IsOpenImmersion ((span f g).map h) :=
    isOpenImmersion_span_map f g
  obtain ⟨i, xi, hxi⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span f g) x
  match i, xi, hxi with
  | .some WalkingPair.left, xi, hxi => exact Or.inl ⟨xi, hxi⟩
  | .some WalkingPair.right, xi, hxi => exact Or.inr ⟨xi, hxi⟩
  | .none, xi, hxi =>
    refine Or.inl ⟨(span f g).map WalkingSpan.Hom.fst xi, ?_⟩
    have hw := congr($(colimit.w (span f g) WalkingSpan.Hom.fst) xi)
    rw [Scheme.Hom.comp_apply] at hw
    exact hw.trans hxi

end TwoChartGlue

/-- **[RECOLL-LW-transport]** Transport of a `LocallyWeierstrass` chart *down* an open-immersion
cartesian square. Given an open immersion `j : S' ⟶ S` sitting in a cartesian square
`IsPullback jE π' π j`, compatible zero sections (`z' ≫ jE = j ≫ z`), and a locally-Weierstrass
structure upstairs on `π'`, every point of `S` in the image of `j` admits the downstairs chart
datum for `π`: push the affine chart `U'` forward to `j ''ᵁ U'` (affine, since `j` is an open
immersion), transport the Weierstrass curve `W` along the section-ring iso `j.appIso U'`, and paste
the base-change square for `projModel` onto the (cancelled) chart pullback squares. The `isoSpec`
compatibility is the `SpecMap_appLE_fromSpec`/`appIso` bridge. This is the per-point engine behind
`glue_locallyWeierstrass`. -/
private theorem lw_chart_transport
    {E' S' E S : Scheme.{u}} {π' : E' ⟶ S'} {z' : S' ⟶ E'} {hz' : z' ≫ π' = 𝟙 S'}
    {π : E ⟶ S} {z : S ⟶ E} {hz : z ≫ π = 𝟙 S}
    {j : S' ⟶ S} {jE : E' ⟶ E} [IsOpenImmersion j]
    (hsq : IsPullback jE π' π j) (hzc : z' ≫ jE = j ≫ z)
    (hlw' : LocallyWeierstrass π' z' hz') (s' : S') :
    ∃ (U : S.affineOpens) (_ : (j.base s') ∈ U.1) (W : WeierstrassCurve Γ(S, U.1)),
      W.IsElliptic ∧
      ∃ e : pullback π U.1.ι ≅ projModel W,
        e.hom ≫ projModelπ W = pullback.snd π U.1.ι ≫ U.2.isoSpec.hom ∧
        (U.2.isoSpec.inv ≫ pullback.lift (U.1.ι ≫ z) (𝟙 _)
            (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp])) ≫ e.hom =
          projModelZero W := by
  obtain ⟨U', hsU', W, hell, e', heπ', hez'⟩ := hlw' s'
  haveI := hell
  -- The image affine open downstairs, and its affineness.
  have hAff : IsAffineOpen (j ''ᵁ U'.1) := U'.2.image_of_isOpenImmersion j
  -- Membership of the target point.
  have hmem : j.base s' ∈ (j ''ᵁ U'.1) := ⟨s', hsU', rfl⟩
  -- The corestriction iso θ : ↥U' ≅ ↥(j ''ᵁ U').
  have hrange : Set.range (U'.1.ι ≫ j) = Set.range (j ''ᵁ U'.1).ι := by
    simp [Scheme.Hom.comp_base, Set.range_comp]
  set θ : (U'.1 : Scheme) ≅ ((j ''ᵁ U'.1) : Scheme) :=
    IsOpenImmersion.isoOfRangeEq (U'.1.ι ≫ j) (j ''ᵁ U'.1).ι hrange with hθ
  have hθfac : θ.hom ≫ (j ''ᵁ U'.1).ι = U'.1.ι ≫ j :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  -- The transported Weierstrass curve.
  set f : Γ(S', U'.1) ⟶ Γ(S, j ''ᵁ U'.1) := (j.appIso U'.1).inv with hf
  set W_new : WeierstrassCurve Γ(S, j ''ᵁ U'.1) := W.map f.hom with hWnew
  haveI : W_new.IsElliptic := by rw [hWnew]; infer_instance
  -- The base-change square for projModel.
  have hB : IsPullback (projModelBaseChangeOf f.hom W W_new rfl) (projModelπ W_new)
      (projModelπ W) (Spec.map (CommRingCat.ofHom f.hom)) :=
    isPullback_projModelBaseChangeOf f.hom W W_new rfl
  set bc := projModelBaseChangeOf f.hom W W_new rfl with hbc
  set Specφ := Spec.map (CommRingCat.ofHom f.hom) with hSpecφ
  have hSpecφ_eq : Specφ = Spec.map f := by rw [hSpecφ, hf, CommRingCat.ofHom_hom]
  haveI : IsIso Specφ := by rw [hSpecφ_eq]; infer_instance
  haveI : IsIso bc := hB.isIso_fst_of_isIso
  -- Base pullback square with the new base map.
  have sq_paste : IsPullback (pullback.fst π' U'.1.ι ≫ jE) (pullback.snd π' U'.1.ι) π
      (U'.1.ι ≫ j) := (IsPullback.of_hasPullback π' U'.1.ι).paste_horiz hsq
  have hP_new : IsPullback (pullback.fst π' U'.1.ι ≫ jE)
      (pullback.snd π' U'.1.ι ≫ θ.hom) π (j ''ᵁ U'.1).ι := by
    refine sq_paste.of_iso (Iso.refl _) (Iso.refl _) θ (Iso.refl _) (by simp) (by simp) (by simp) ?_
    simp [hθfac]
  -- The chart iso downstairs.
  set e_new : pullback π (j ''ᵁ U'.1).ι ≅ projModel W_new :=
    hP_new.isoPullback.symm ≪≫ e' ≪≫ (asIso bc).symm with he_new
  -- Bridge: isoSpec compatibility.
  have hbridge0 : Spec.map (j.appIso U'.1).hom ≫ hAff.isoSpec.inv =
      U'.2.isoSpec.inv ≫ θ.hom := by
    have hsp := IsAffineOpen.SpecMap_appLE_fromSpec j hAff U'.2 (j.preimage_image_eq U'.1).ge
    rw [← Scheme.Hom.appIso_hom', ← IsAffineOpen.isoSpec_inv_ι hAff,
      ← IsAffineOpen.isoSpec_inv_ι U'.2] at hsp
    simp only [Category.assoc] at hsp
    rw [← hθfac] at hsp
    exact (cancel_mono (j ''ᵁ U'.1).ι).mp (by simp only [Category.assoc]; exact hsp)
  have hinvSpecφ : inv Specφ = Spec.map (j.appIso U'.1).hom := by
    have h1 : Specφ ≫ Spec.map (j.appIso U'.1).hom = 𝟙 _ := by
      rw [hSpecφ_eq, hf, ← Spec.map_comp, Iso.hom_inv_id]; exact Spec.map_id _
    exact IsIso.inv_eq_of_hom_inv_id h1
  have hbr1 : θ.inv ≫ U'.2.isoSpec.hom ≫ inv Specφ = hAff.isoSpec.hom := by
    rw [hinvSpecφ, ← cancel_mono hAff.isoSpec.inv]
    simp only [Category.assoc, hbridge0]
    simp
  have hzbc : projModelZero W_new ≫ bc = Specφ ≫ projModelZero W := by
    rw [hbc, hSpecφ]; exact projModelZero_baseChangeOf f.hom W W_new rfl
  refine ⟨⟨j ''ᵁ U'.1, hAff⟩, hmem, W_new, inferInstance, e_new, ?_, ?_⟩
  · -- condition 1: `e.hom ≫ projModelπ = snd ≫ isoSpec.hom`
    have hsnd : hP_new.isoPullback.inv ≫ pullback.snd π' U'.1.ι
        = pullback.snd π (j ''ᵁ U'.1).ι ≫ θ.inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, hP_new.isoPullback_hom_snd, Category.assoc,
        θ.hom_inv_id, Category.comp_id]
    have hinvbc : inv bc ≫ projModelπ W_new = projModelπ W ≫ inv Specφ := by
      rw [IsIso.inv_comp_eq, ← Category.assoc, hB.w, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]
    rw [he_new]
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc]
    rw [hinvbc, reassoc_of% heπ', ← Category.assoc, hsnd, Category.assoc, hbr1]
  · -- condition 2: the zero-section compatibility
    show (hAff.isoSpec.inv ≫ pullback.lift ((j ''ᵁ U'.1).ι ≫ z) (𝟙 _)
        (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp])) ≫ e_new.hom =
      projModelZero W_new
    set sU := pullback.lift ((j ''ᵁ U'.1).ι ≫ z) (𝟙 _)
      (show ((j ''ᵁ U'.1).ι ≫ z) ≫ π = 𝟙 _ ≫ (j ''ᵁ U'.1).ι by
        rw [Category.assoc, hz, Category.comp_id, Category.id_comp]) with hsU
    set sU' := pullback.lift (U'.1.ι ≫ z') (𝟙 _)
      (show (U'.1.ι ≫ z') ≫ π' = 𝟙 _ ≫ U'.1.ι by
        rw [Category.assoc, hz', Category.comp_id, Category.id_comp]) with hsU'
    have hsec0 : sU = θ.inv ≫ sU' ≫ hP_new.isoPullback.hom := by
      refine pullback.hom_ext ?_ ?_
      · rw [hsU, pullback.lift_fst, Category.assoc, Category.assoc,
          hP_new.isoPullback_hom_fst, hsU', pullback.lift_fst_assoc,
          Category.assoc, hzc, ← reassoc_of% hθfac, θ.inv_hom_id_assoc]
      · rw [hsU, pullback.lift_snd, Category.assoc, Category.assoc,
          hP_new.isoPullback_hom_snd, hsU', pullback.lift_snd_assoc,
          Category.id_comp, θ.inv_hom_id]
    have hsecinv : sU ≫ hP_new.isoPullback.inv = θ.inv ≫ sU' := by
      rw [hsec0, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hsU'e : sU' ≫ e'.hom = U'.2.isoSpec.hom ≫ projModelZero W := by
      rw [← hez', ← Category.assoc, Iso.hom_inv_id_assoc]
    have hz0invbc : projModelZero W ≫ inv bc = inv Specφ ≫ projModelZero W_new := by
      rw [IsIso.comp_inv_eq, Category.assoc, hzbc, IsIso.inv_hom_id_assoc]
    rw [he_new]
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc]
    rw [reassoc_of% hsecinv, reassoc_of% hsU'e, hz0invbc, reassoc_of% hbr1,
      Iso.inv_hom_id_assoc]

/-! ## [R-glue-obj] the glued `Ell`-object

Glue the two representing objects `Xa/R[1/a]` and `Xb/R[1/b]` along the overlap iso `φ` over
`R[1/ab]` into a single object of `Ell/R`:

* the **base** `S := Xa.base ⊔_W Xb.base` is the pushout of the open immersions
  `W = Xa.base ×_{Spec R[1/a]} Spec R[1/ab] ⟶ Xa.base` and (through `φ.hom.baseHom`)
  `W ⟶ Xb.base`;
* the **total space** `E := Xa.curve.E ⊔_{W_E} Xb.curve.E` likewise on the curve level;
* `π`, `zero`, and the structure map to `Spec R` are pushout-descents; each chart square
  `(Xa.curve.E → E, Xa.base → S)` is **cartesian** (the chart ranges match up:
  `range inlE = π⁻¹ (range inl)`);
* smoothness, properness and the local Weierstrass model transfer chart-by-chart
  (Zariski-local at the target), and the group structure is re-derived from the glued
  *geometry* by `EllipticCurveGeom.toEllipticCurve` (T-W7) — **no group-scheme gluing**. -/

section GlueObj

/-- `baseHom` of an `Ell`-isomorphism is an isomorphism of schemes. -/
private theorem isIso_baseHom_of_iso {R₀ : CommRingCat.{u}} {X Y : EllObj R₀} (e : X ≅ Y) :
    IsIso e.hom.baseHom :=
  ⟨e.inv.baseHom, by rw [← EllHom.comp_baseHom, e.hom_inv_id]; rfl,
    by rw [← EllHom.comp_baseHom, e.inv_hom_id]; rfl⟩

/-- `top` of an `Ell`-isomorphism is an isomorphism of schemes. -/
private theorem isIso_top_of_iso {R₀ : CommRingCat.{u}} {X Y : EllObj R₀} (e : X ≅ Y) :
    IsIso e.hom.top :=
  ⟨e.inv.top, by rw [← EllHom.comp_top, e.hom_inv_id]; rfl,
    by rw [← EllHom.comp_top, e.inv_hom_id]; rfl⟩

private theorem baseChangeRing_curve_pi {R' R'' : CommRingCat.{u}} (X : EllObj R')
    (τ : R' ⟶ R'') :
    (X.baseChangeRing τ).curve.π
      = pullback.snd X.curve.π (pullback.fst X.structMap (Spec.map τ)) := rfl

variable (a b : R)
variable (Xa : EllObj (CommRingCat.of (Localization.Away a)))
variable (Xb : EllObj (CommRingCat.of (Localization.Away b)))
variable (φ : Xa.baseChangeRing (awayProdHomLeft a b) ≅ Xb.baseChangeRing (awayProdHomRight a b))

/-- Left leg of the base span: the overlap `W ⟶ Xa.base` (base change of `D(ab) ↪ D(a)`). -/
private noncomputable def glueBaseFst :
    (Xa.baseChangeRing (awayProdHomLeft a b)).base ⟶ Xa.base :=
  pullback.fst Xa.structMap (Spec.map (awayProdHomLeft a b))

/-- Right leg of the base span: `W ⟶ Xb.base` through the overlap iso `φ`. -/
private noncomputable def glueBasePsi :
    (Xa.baseChangeRing (awayProdHomLeft a b)).base ⟶ Xb.base :=
  φ.hom.baseHom ≫ pullback.fst Xb.structMap (Spec.map (awayProdHomRight a b))

private instance : IsOpenImmersion (glueBaseFst a b Xa) :=
  inferInstanceAs (IsOpenImmersion (pullback.fst Xa.structMap (Spec.map (awayProdHomLeft a b))))

private instance : IsOpenImmersion (glueBasePsi a b Xa Xb φ) := by
  haveI : IsIso φ.hom.baseHom := isIso_baseHom_of_iso φ
  exact @IsOpenImmersion.comp _ (pullback Xb.structMap (Spec.map (awayProdHomRight a b))) _
    φ.hom.baseHom (pullback.fst Xb.structMap (Spec.map (awayProdHomRight a b)))
    (IsOpenImmersion.of_isIso φ.hom.baseHom) _

/-- **[R-glue-obj], base.** The glued base scheme `S = Xa.base ∪_W Xb.base`. -/
private noncomputable def glueBase : Scheme.{u} :=
  pushout (glueBaseFst a b Xa) (glueBasePsi a b Xa Xb φ)

/-- The `a`-chart of the glued base. -/
private noncomputable def glueBaseInl : Xa.base ⟶ glueBase a b Xa Xb φ := pushout.inl _ _

/-- The `b`-chart of the glued base. -/
private noncomputable def glueBaseInr : Xb.base ⟶ glueBase a b Xa Xb φ := pushout.inr _ _

private instance : IsOpenImmersion (glueBaseInl a b Xa Xb φ) :=
  inferInstanceAs (IsOpenImmersion (pushout.inl (glueBaseFst a b Xa) (glueBasePsi a b Xa Xb φ)))

private instance : IsOpenImmersion (glueBaseInr a b Xa Xb φ) :=
  inferInstanceAs (IsOpenImmersion (pushout.inr (glueBaseFst a b Xa) (glueBasePsi a b Xa Xb φ)))

private theorem glueBase_condition :
    glueBaseFst a b Xa ≫ glueBaseInl a b Xa Xb φ
      = glueBasePsi a b Xa Xb φ ≫ glueBaseInr a b Xa Xb φ :=
  pushout.condition

private theorem glueBase_hom_ext {Z : Scheme.{u}} {u v : glueBase a b Xa Xb φ ⟶ Z}
    (h1 : glueBaseInl a b Xa Xb φ ≫ u = glueBaseInl a b Xa Xb φ ≫ v)
    (h2 : glueBaseInr a b Xa Xb φ ≫ u = glueBaseInr a b Xa Xb φ ≫ v) : u = v :=
  pushout.hom_ext h1 h2

private theorem glueBase_inl_eq_inr_iff (x : Xa.base) (y : Xb.base) :
    glueBaseInl a b Xa Xb φ x = glueBaseInr a b Xa Xb φ y ↔
      ∃ w, glueBaseFst a b Xa w = x ∧ glueBasePsi a b Xa Xb φ w = y :=
  pushout_inl_eq_inr_iff _ _ x y

private theorem glueBase_exists (x : glueBase a b Xa Xb φ) :
    (∃ u, glueBaseInl a b Xa Xb φ u = x) ∨ (∃ v, glueBaseInr a b Xa Xb φ v = x) :=
  pushout_exists_inl_or_inr _ _ x

/-- The two structure maps to `Spec R` agree on the overlap (both are the `R[1/ab]`-structure
map of the overlap followed by `D(ab) ↪ Spec R`, via the localization towers). -/
private theorem glueQ_w :
    glueBaseFst a b Xa ≫ Xa.structMap ≫ Spec.map (awayHom a)
      = glueBasePsi a b Xa Xb φ ≫ Xb.structMap ≫ Spec.map (awayHom b) := by
  have ha : glueBaseFst a b Xa ≫ Xa.structMap
      = (Xa.baseChangeRing (awayProdHomLeft a b)).structMap ≫ Spec.map (awayProdHomLeft a b) :=
    pullback.condition
  have hpsi : glueBasePsi a b Xa Xb φ ≫ Xb.structMap
      = (Xa.baseChangeRing (awayProdHomLeft a b)).structMap ≫ Spec.map (awayProdHomRight a b) := by
    rw [glueBasePsi, Category.assoc, ← φ.hom.base_w, Category.assoc]
    congr 1
    exact pullback.condition
  rw [reassoc_of% ha, reassoc_of% hpsi, ← Spec.map_comp, ← Spec.map_comp,
    awayHom_comp_awayProdHomLeft, awayHom_comp_awayProdHomRight]

/-- **[R-glue-obj], structure map.** `S ⟶ Spec R`, glued from the two localized structure
maps. -/
private noncomputable def glueQ : glueBase a b Xa Xb φ ⟶ Spec R :=
  pushout.desc (Xa.structMap ≫ Spec.map (awayHom a)) (Xb.structMap ≫ Spec.map (awayHom b))
    (glueQ_w a b Xa Xb φ)

private theorem glueBaseInl_glueQ :
    glueBaseInl a b Xa Xb φ ≫ glueQ a b Xa Xb φ = Xa.structMap ≫ Spec.map (awayHom a) :=
  pushout.inl_desc _ _ _

private theorem glueBaseInr_glueQ :
    glueBaseInr a b Xa Xb φ ≫ glueQ a b Xa Xb φ = Xb.structMap ≫ Spec.map (awayHom b) :=
  pushout.inr_desc _ _ _

/-! ### The glued total space -/

/-- Left leg of the curve span: the overlap curve `W_E ⟶ Xa.curve.E`. -/
private noncomputable def glueCurveFst :
    (Xa.baseChangeRing (awayProdHomLeft a b)).curve.E ⟶ Xa.curve.E :=
  pullback.fst Xa.curve.π (pullback.fst Xa.structMap (Spec.map (awayProdHomLeft a b)))

/-- Right leg of the curve span: `W_E ⟶ Xb.curve.E` through `φ.hom.top`. -/
private noncomputable def glueCurvePsi :
    (Xa.baseChangeRing (awayProdHomLeft a b)).curve.E ⟶ Xb.curve.E :=
  φ.hom.top ≫ pullback.fst Xb.curve.π (pullback.fst Xb.structMap (Spec.map (awayProdHomRight a b)))

private instance : IsOpenImmersion (glueCurveFst a b Xa) :=
  inferInstanceAs (IsOpenImmersion
    (pullback.fst Xa.curve.π (pullback.fst Xa.structMap (Spec.map (awayProdHomLeft a b)))))

private instance : IsOpenImmersion (glueCurvePsi a b Xa Xb φ) := by
  haveI : IsIso φ.hom.top := isIso_top_of_iso φ
  exact @IsOpenImmersion.comp _
    (pullback Xb.curve.π (pullback.fst Xb.structMap (Spec.map (awayProdHomRight a b)))) _
    φ.hom.top
    (pullback.fst Xb.curve.π (pullback.fst Xb.structMap (Spec.map (awayProdHomRight a b))))
    (IsOpenImmersion.of_isIso φ.hom.top) _

/-- **[R-glue-obj], total space.** The glued total space `E = Xa.curve.E ∪_{W_E} Xb.curve.E`. -/
private noncomputable def glueTotal : Scheme.{u} :=
  pushout (glueCurveFst a b Xa) (glueCurvePsi a b Xa Xb φ)

private noncomputable def glueTotalInl : Xa.curve.E ⟶ glueTotal a b Xa Xb φ := pushout.inl _ _

private noncomputable def glueTotalInr : Xb.curve.E ⟶ glueTotal a b Xa Xb φ := pushout.inr _ _

private instance : IsOpenImmersion (glueTotalInl a b Xa Xb φ) :=
  inferInstanceAs (IsOpenImmersion (pushout.inl (glueCurveFst a b Xa) (glueCurvePsi a b Xa Xb φ)))

private instance : IsOpenImmersion (glueTotalInr a b Xa Xb φ) :=
  inferInstanceAs (IsOpenImmersion (pushout.inr (glueCurveFst a b Xa) (glueCurvePsi a b Xa Xb φ)))

private theorem glueTotal_condition :
    glueCurveFst a b Xa ≫ glueTotalInl a b Xa Xb φ
      = glueCurvePsi a b Xa Xb φ ≫ glueTotalInr a b Xa Xb φ :=
  pushout.condition

private theorem glueTotal_hom_ext {Z : Scheme.{u}} {u v : glueTotal a b Xa Xb φ ⟶ Z}
    (h1 : glueTotalInl a b Xa Xb φ ≫ u = glueTotalInl a b Xa Xb φ ≫ v)
    (h2 : glueTotalInr a b Xa Xb φ ≫ u = glueTotalInr a b Xa Xb φ ≫ v) : u = v :=
  pushout.hom_ext h1 h2

private theorem glueTotal_inl_eq_inr_iff (x : Xa.curve.E) (y : Xb.curve.E) :
    glueTotalInl a b Xa Xb φ x = glueTotalInr a b Xa Xb φ y ↔
      ∃ w, glueCurveFst a b Xa w = x ∧ glueCurvePsi a b Xa Xb φ w = y :=
  pushout_inl_eq_inr_iff _ _ x y

private theorem glueTotal_exists (x : glueTotal a b Xa Xb φ) :
    (∃ u, glueTotalInl a b Xa Xb φ u = x) ∨ (∃ v, glueTotalInr a b Xa Xb φ v = x) :=
  pushout_exists_inl_or_inr _ _ x

/-- The two chart projections agree on the overlap curve. -/
private theorem gluePi_w :
    glueCurveFst a b Xa ≫ Xa.curve.π ≫ glueBaseInl a b Xa Xb φ
      = glueCurvePsi a b Xa Xb φ ≫ Xb.curve.π ≫ glueBaseInr a b Xa Xb φ := by
  have ha : glueCurveFst a b Xa ≫ Xa.curve.π
      = (Xa.baseChangeRing (awayProdHomLeft a b)).curve.π ≫ glueBaseFst a b Xa :=
    pullback.condition
  have hcurve : glueCurvePsi a b Xa Xb φ ≫ Xb.curve.π
      = (Xa.baseChangeRing (awayProdHomLeft a b)).curve.π ≫ glueBasePsi a b Xa Xb φ := by
    rw [glueCurvePsi, glueBasePsi]
    simp only [Category.assoc]
    rw [← reassoc_of% φ.hom.isPullback.w]
    congr 1
    exact pullback.condition
  rw [reassoc_of% ha, glueBase_condition, reassoc_of% hcurve]

/-- **[R-glue-obj], projection.** `π : E ⟶ S`, glued from the chart projections. -/
private noncomputable def gluePi : glueTotal a b Xa Xb φ ⟶ glueBase a b Xa Xb φ :=
  pushout.desc (Xa.curve.π ≫ glueBaseInl a b Xa Xb φ) (Xb.curve.π ≫ glueBaseInr a b Xa Xb φ)
    (gluePi_w a b Xa Xb φ)

private theorem glueTotalInl_gluePi :
    glueTotalInl a b Xa Xb φ ≫ gluePi a b Xa Xb φ = Xa.curve.π ≫ glueBaseInl a b Xa Xb φ :=
  pushout.inl_desc _ _ _

private theorem glueTotalInr_gluePi :
    glueTotalInr a b Xa Xb φ ≫ gluePi a b Xa Xb φ = Xb.curve.π ≫ glueBaseInr a b Xa Xb φ :=
  pushout.inr_desc _ _ _

/-- The two chart zero sections agree on the overlap. -/
private theorem glueZero_w :
    glueBaseFst a b Xa ≫ Xa.curve.zero ≫ glueTotalInl a b Xa Xb φ
      = glueBasePsi a b Xa Xb φ ≫ Xb.curve.zero ≫ glueTotalInr a b Xa Xb φ := by
  have ha : (Xa.baseChangeRing (awayProdHomLeft a b)).curve.zero ≫ glueCurveFst a b Xa
      = glueBaseFst a b Xa ≫ Xa.curve.zero :=
    baseChangeRing_curve_zero_comp_fst Xa (awayProdHomLeft a b)
  have hzero : glueBasePsi a b Xa Xb φ ≫ Xb.curve.zero
      = (Xa.baseChangeRing (awayProdHomLeft a b)).curve.zero ≫ glueCurvePsi a b Xa Xb φ := by
    rw [glueBasePsi, glueCurvePsi]
    simp only [Category.assoc]
    rw [reassoc_of% φ.hom.zero_w]
    congr 1
    exact (baseChangeRing_curve_zero_comp_fst Xb (awayProdHomRight a b)).symm
  rw [← reassoc_of% ha, glueTotal_condition, reassoc_of% hzero]

/-- **[R-glue-obj], zero section.** `zero : S ⟶ E`, glued from the chart zero sections. -/
private noncomputable def glueZero : glueBase a b Xa Xb φ ⟶ glueTotal a b Xa Xb φ :=
  pushout.desc (Xa.curve.zero ≫ glueTotalInl a b Xa Xb φ)
    (Xb.curve.zero ≫ glueTotalInr a b Xa Xb φ) (glueZero_w a b Xa Xb φ)

private theorem glueBaseInl_glueZero :
    glueBaseInl a b Xa Xb φ ≫ glueZero a b Xa Xb φ
      = Xa.curve.zero ≫ glueTotalInl a b Xa Xb φ :=
  pushout.inl_desc _ _ _

private theorem glueBaseInr_glueZero :
    glueBaseInr a b Xa Xb φ ≫ glueZero a b Xa Xb φ
      = Xb.curve.zero ≫ glueTotalInr a b Xa Xb φ :=
  pushout.inr_desc _ _ _

private theorem glueZero_gluePi :
    glueZero a b Xa Xb φ ≫ gluePi a b Xa Xb φ = 𝟙 (glueBase a b Xa Xb φ) := by
  apply glueBase_hom_ext
  · rw [← Category.assoc, glueBaseInl_glueZero, Category.assoc, glueTotalInl_gluePi,
      ← Category.assoc, Xa.curve.zero_π, Category.id_comp, Category.comp_id]
  · rw [← Category.assoc, glueBaseInr_glueZero, Category.assoc, glueTotalInr_gluePi,
      ← Category.assoc, Xb.curve.zero_π, Category.id_comp, Category.comp_id]

/-! ### The chart squares are cartesian -/

/-- Range of the top of a cartesian square of schemes: `range fst = f ⁻¹' (range g)`
(the general-`IsPullback` version of `Scheme.Pullback.range_fst`). -/
private theorem range_fst_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) :
    Set.range fst = f ⁻¹' Set.range g := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨snd p, ?_⟩
    have := congr($(h.w) p)
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at this
    exact this.symm
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y hy.symm
    refine ⟨h.isoPullback.inv z, ?_⟩
    have := congr($(h.isoPullback_inv_fst) z)
    rw [Scheme.Hom.comp_apply] at this
    exact this.trans hz1

/-- The `b`-side overlap square, pasted through `φ`: `W_E` is the pullback of
`Xb.curve.E` along `W ⟶ Xb.base`. -/
private theorem isPullback_glueCurvePsi :
    IsPullback (glueCurvePsi a b Xa Xb φ) (Xa.baseChangeRing (awayProdHomLeft a b)).curve.π
      Xb.curve.π (glueBasePsi a b Xa Xb φ) := by
  have h2 : IsPullback
      (pullback.fst Xb.curve.π (pullback.fst Xb.structMap (Spec.map (awayProdHomRight a b))))
      (Xb.baseChangeRing (awayProdHomRight a b)).curve.π Xb.curve.π
      (pullback.fst Xb.structMap (Spec.map (awayProdHomRight a b))) := by
    rw [baseChangeRing_curve_pi]
    exact IsPullback.of_hasPullback _ _
  exact φ.hom.isPullback.paste_horiz h2

/-- The `a`-side overlap square: `W_E` is the pullback of `Xa.curve.E` along `W ⟶ Xa.base`. -/
private theorem isPullback_glueCurveFst :
    IsPullback (glueCurveFst a b Xa) (Xa.baseChangeRing (awayProdHomLeft a b)).curve.π
      Xa.curve.π (glueBaseFst a b Xa) := by
  rw [baseChangeRing_curve_pi]
  exact IsPullback.of_hasPullback _ _

/-- **The key chart-range identity**: the `a`-chart of the total space is exactly the
`π`-preimage of the `a`-chart of the base. -/
private theorem range_glueTotalInl :
    Set.range (glueTotalInl a b Xa Xb φ)
      = gluePi a b Xa Xb φ ⁻¹' Set.range (glueBaseInl a b Xa Xb φ) := by
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨Xa.curve.π e, ?_⟩
    have := congr($(glueTotalInl_gluePi a b Xa Xb φ) e)
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at this
    exact this.symm
  · intro hx
    obtain ⟨u, hu⟩ := hx
    rcases glueTotal_exists a b Xa Xb φ x with ⟨e, rfl⟩ | ⟨e, rfl⟩
    · exact ⟨e, rfl⟩
    · -- `x = inrE e` with `π x ∈ range inl`: the base point comes from the overlap, hence
      -- so does `e`, hence `x` is in the image of the `a`-chart via the glue relation.
      have hpi : gluePi a b Xa Xb φ (glueTotalInr a b Xa Xb φ e)
          = glueBaseInr a b Xa Xb φ (Xb.curve.π e) := by
        have := congr($(glueTotalInr_gluePi a b Xa Xb φ) e)
        rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at this
      obtain ⟨w, hw1, hw2⟩ := (glueBase_inl_eq_inr_iff a b Xa Xb φ u (Xb.curve.π e)).mp
        (by rw [hu, hpi])
      have he : e ∈ Set.range (glueCurvePsi a b Xa Xb φ) := by
        rw [range_fst_of_isPullback (isPullback_glueCurvePsi a b Xa Xb φ)]
        exact ⟨w, hw2⟩
      obtain ⟨z, rfl⟩ := he
      refine ⟨glueCurveFst a b Xa z, ?_⟩
      have := congr($(glueTotal_condition a b Xa Xb φ) z)
      rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at this

/-- The mirrored chart-range identity for the `b`-chart. -/
private theorem range_glueTotalInr :
    Set.range (glueTotalInr a b Xa Xb φ)
      = gluePi a b Xa Xb φ ⁻¹' Set.range (glueBaseInr a b Xa Xb φ) := by
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨Xb.curve.π e, ?_⟩
    have := congr($(glueTotalInr_gluePi a b Xa Xb φ) e)
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at this
    exact this.symm
  · intro hx
    obtain ⟨u, hu⟩ := hx
    rcases glueTotal_exists a b Xa Xb φ x with ⟨e, rfl⟩ | ⟨e, rfl⟩
    · have hpi : gluePi a b Xa Xb φ (glueTotalInl a b Xa Xb φ e)
          = glueBaseInl a b Xa Xb φ (Xa.curve.π e) := by
        have := congr($(glueTotalInl_gluePi a b Xa Xb φ) e)
        rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at this
      obtain ⟨w, hw1, hw2⟩ := (glueBase_inl_eq_inr_iff a b Xa Xb φ (Xa.curve.π e) u).mp
        ((hu.trans hpi).symm)
      have he : e ∈ Set.range (glueCurveFst a b Xa) := by
        rw [range_fst_of_isPullback (isPullback_glueCurveFst a b Xa)]
        exact ⟨w, hw1⟩
      obtain ⟨z, rfl⟩ := he
      refine ⟨glueCurvePsi a b Xa Xb φ z, ?_⟩
      have := congr($(glueTotal_condition a b Xa Xb φ) z)
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at this
      exact this.symm
    · exact ⟨e, rfl⟩

/-- **[R-glue-obj], chart square `a`.** The `a`-chart square of the glued curve is
cartesian: `Xa.curve.E` is the restriction of the glued curve to the `a`-chart. -/
private theorem isPullback_glueTotalInl :
    IsPullback (glueTotalInl a b Xa Xb φ) Xa.curve.π (gluePi a b Xa Xb φ)
      (glueBaseInl a b Xa Xb φ) := by
  have hrange : Set.range (glueTotalInl a b Xa Xb φ)
      = Set.range (pullback.fst (gluePi a b Xa Xb φ) (glueBaseInl a b Xa Xb φ)) := by
    rw [Scheme.Pullback.range_fst, range_glueTotalInl]
  have hcomm : CommSq (glueTotalInl a b Xa Xb φ) Xa.curve.π (gluePi a b Xa Xb φ)
      (glueBaseInl a b Xa Xb φ) := ⟨glueTotalInl_gluePi a b Xa Xb φ⟩
  refine IsPullback.of_iso_pullback hcomm
    (IsOpenImmersion.isoOfRangeEq (glueTotalInl a b Xa Xb φ)
      (pullback.fst (gluePi a b Xa Xb φ) (glueBaseInl a b Xa Xb φ)) hrange) ?_ ?_
  · exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  · rw [← cancel_mono (glueBaseInl a b Xa Xb φ), Category.assoc, ← pullback.condition,
      ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, glueTotalInl_gluePi]

/-- **[R-glue-obj], chart square `b`.** -/
private theorem isPullback_glueTotalInr :
    IsPullback (glueTotalInr a b Xa Xb φ) Xb.curve.π (gluePi a b Xa Xb φ)
      (glueBaseInr a b Xa Xb φ) := by
  have hrange : Set.range (glueTotalInr a b Xa Xb φ)
      = Set.range (pullback.fst (gluePi a b Xa Xb φ) (glueBaseInr a b Xa Xb φ)) := by
    rw [Scheme.Pullback.range_fst, range_glueTotalInr]
  have hcomm : CommSq (glueTotalInr a b Xa Xb φ) Xb.curve.π (gluePi a b Xa Xb φ)
      (glueBaseInr a b Xa Xb φ) := ⟨glueTotalInr_gluePi a b Xa Xb φ⟩
  refine IsPullback.of_iso_pullback hcomm
    (IsOpenImmersion.isoOfRangeEq (glueTotalInr a b Xa Xb φ)
      (pullback.fst (gluePi a b Xa Xb φ) (glueBaseInr a b Xa Xb φ)) hrange) ?_ ?_
  · exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  · rw [← cancel_mono (glueBaseInr a b Xa Xb φ), Category.assoc, ← pullback.condition,
      ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, glueTotalInr_gluePi]

/-- **[R-glue-obj], property transfer.** Any morphism property `P` that is Zariski-local at the
target and holds for both chart projections `Xa.curve.π`, `Xb.curve.π` holds for the glued
projection `gluePi`: the two chart opens cover the glued base (`glueBase_exists`), and over each
chart the restriction of `gluePi` is, as an arrow, the corresponding chart projection (the
cartesian squares `isPullback_glueTotalInl/Inr` composed with `morphismRestrictOpensRange`). -/
private theorem glue_zariskiLocalAtTarget (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] (hPa : P Xa.curve.π) (hPb : P Xb.curve.π) :
    P (gluePi a b Xa Xb φ) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun i : Bool => cond i (glueBaseInr a b Xa Xb φ).opensRange
      (glueBaseInl a b Xa Xb φ).opensRange) ?_ ?_
  · refine top_le_iff.mp fun x _ => ?_
    rcases glueBase_exists a b Xa Xb φ x with ⟨u, rfl⟩ | ⟨v, rfl⟩
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨false, u, rfl⟩
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨true, v, rfl⟩
  · intro i
    cases i
    · refine (P.arrow_mk_iso_iff
        (morphismRestrictOpensRange (gluePi a b Xa Xb φ) (glueBaseInl a b Xa Xb φ))).mpr ?_
      refine (P.arrow_mk_iso_iff (Arrow.isoMk
        (isPullback_glueTotalInl a b Xa Xb φ).isoPullback.symm (Iso.refl _) ?_)).mpr hPa
      simp only [Arrow.mk_hom, Iso.symm_hom, Iso.refl_hom]
      exact (isPullback_glueTotalInl a b Xa Xb φ).isoPullback_inv_snd
    · refine (P.arrow_mk_iso_iff
        (morphismRestrictOpensRange (gluePi a b Xa Xb φ) (glueBaseInr a b Xa Xb φ))).mpr ?_
      refine (P.arrow_mk_iso_iff (Arrow.isoMk
        (isPullback_glueTotalInr a b Xa Xb φ).isoPullback.symm (Iso.refl _) ?_)).mpr hPb
      simp only [Arrow.mk_hom, Iso.symm_hom, Iso.refl_hom]
      exact (isPullback_glueTotalInr a b Xa Xb φ).isoPullback_inv_snd

/-! ### The glued geometric elliptic curve and the glued `Ell/R`-object

The three geometry `Prop`s (`smooth`, `proper`, `localModel`) are Zariski-local on the glued
base and transfer from the charts; all three ([RECOLL-SM], [RECOLL-PR], [RECOLL-LW]) are now
**proven** below (`smooth`/`proper` via `glue_zariskiLocalAtTarget`, `localModel` via the
per-point chart transport `lw_chart_transport`). -/

/-- **[RECOLL-SM] (proven).** Smoothness of relative dimension 1 for the glued projection.

*Recipe.* `SmoothOfRelativeDimension 1` is `IsZariskiLocalAtTarget` (mathlib). Apply
`IsZariskiLocalAtTarget.of_iSup_eq_top` with the two chart opens
`(glueBaseInl …).opensRange ⊔ (glueBaseInr …).opensRange = ⊤` (from `glueBase_exists`), or
`of_openCover` with the two-chart open cover; on each chart the restriction of `gluePi` is
isomorphic (as an arrow) to `Xa.curve.π` resp. `Xb.curve.π` via
`isPullback_glueTotalInl/Inr` (`IsPullback.isoPullback` against
`pullback (gluePi …) (glueBaseInl …)`), and `Xa.curve.smooth`/`Xb.curve.smooth` finish. -/
private theorem glue_smooth :
    SmoothOfRelativeDimension 1 (gluePi a b Xa Xb φ) :=
  glue_zariskiLocalAtTarget a b Xa Xb φ (@SmoothOfRelativeDimension 1)
    Xa.curve.smooth Xb.curve.smooth

/-- **[RECOLL-PR] (proven).** Properness of the glued projection, via `glue_zariskiLocalAtTarget`
with `IsProper` (`IsZariskiLocalAtTarget`) and `Xa.curve.proper`/`Xb.curve.proper`. -/
private theorem glue_proper : IsProper (gluePi a b Xa Xb φ) :=
  glue_zariskiLocalAtTarget a b Xa Xb φ (@IsProper) Xa.curve.proper Xb.curve.proper

/-- **[RECOLL-LW] (proven).** The glued curve is locally Weierstrass.

`LocallyWeierstrass` is a pointwise condition on the base: given `s : glueBase …`,
`glueBase_exists` writes it as `glueBaseInl … sa` (or the mirrored `b`-case), and the
per-point chart transport `lw_chart_transport` (above) produces the downstairs chart datum
from the chart of `Xa.curve`/`Xb.curve` through the cartesian chart square
`isPullback_glueTotalInl/Inr` and the zero-section compatibility `glueBaseInl/Inr_glueZero`. -/
private theorem glue_locallyWeierstrass :
    LocallyWeierstrass (gluePi a b Xa Xb φ) (glueZero a b Xa Xb φ)
      (glueZero_gluePi a b Xa Xb φ) := by
  intro s
  rcases glueBase_exists a b Xa Xb φ s with ⟨sa, rfl⟩ | ⟨sb, rfl⟩
  · exact lw_chart_transport (hz := glueZero_gluePi a b Xa Xb φ)
      (isPullback_glueTotalInl a b Xa Xb φ)
      (glueBaseInl_glueZero a b Xa Xb φ).symm Xa.curve.localModel sa
  · exact lw_chart_transport (hz := glueZero_gluePi a b Xa Xb φ)
      (isPullback_glueTotalInr a b Xa Xb φ)
      (glueBaseInr_glueZero a b Xa Xb φ).symm Xb.curve.localModel sb

/-- **[R-glue-obj], geometry.** The glued geometric elliptic curve over the glued base. -/
private noncomputable def glueGeom : EllipticCurveGeom (glueBase a b Xa Xb φ) where
  E := glueTotal a b Xa Xb φ
  π := gluePi a b Xa Xb φ
  zero := glueZero a b Xa Xb φ
  zero_π := glueZero_gluePi a b Xa Xb φ
  smooth := glue_smooth a b Xa Xb φ
  proper := glue_proper a b Xa Xb φ
  localModel := glue_locallyWeierstrass a b Xa Xb φ

/-- **[R-glue-obj].** The glued `Ell/R`-object: base `S = Xa.base ∪_W Xb.base`, structure map
`glueQ`, and the glued curve with its group structure re-derived from the geometry by
`EllipticCurveGeom.toEllipticCurve` (T-W7) — no group-scheme gluing. -/
private noncomputable def glueEllObj : EllObj R where
  base := glueBase a b Xa Xb φ
  structMap := glueQ a b Xa Xb φ
  curve := (glueGeom a b Xa Xb φ).toEllipticCurve

/-- The `a`-chart inclusion, as a morphism of `Ell/R`. -/
private noncomputable def glueJa :
    (EllObj.restrictScalars (awayHom a)).obj Xa ⟶ glueEllObj a b Xa Xb φ where
  baseHom := glueBaseInl a b Xa Xb φ
  base_w := glueBaseInl_glueQ a b Xa Xb φ
  top := glueTotalInl a b Xa Xb φ
  isPullback := isPullback_glueTotalInl a b Xa Xb φ
  zero_w := (glueBaseInl_glueZero a b Xa Xb φ).symm

/-- The `b`-chart inclusion, as a morphism of `Ell/R`. -/
private noncomputable def glueJb :
    (EllObj.restrictScalars (awayHom b)).obj Xb ⟶ glueEllObj a b Xa Xb φ where
  baseHom := glueBaseInr a b Xa Xb φ
  base_w := glueBaseInr_glueQ a b Xa Xb φ
  top := glueTotalInr a b Xa Xb φ
  isPullback := isPullback_glueTotalInr a b Xa Xb φ
  zero_w := (glueBaseInr_glueZero a b Xa Xb φ).symm

end GlueObj

/-! ## [R-glue-descent] Zariski descent of the moduli functor — chart inclusions

The descent is parametrized over the Zariski-sheaf property of `P`. We first build, for every test
object `Y : Ell/R`, the two chart inclusions `Y|D(a) ⟶ Y`, `Y|D(b) ⟶ Y` and the overlap
`Y|D(ab)` with its inclusions into the two charts, all as morphisms of `Ell/R`. These are the
diagram the sheaf condition (`ZariskiSheaf`) is stated against. -/

section ZariskiDescent

set_option backward.isDefEq.respectTransparency false

variable (a b : R)

/-- The `a`-chart inclusion of a test object `Y : Ell/R`: `Y|D(a) ⟶ Y`, the restriction of `Y` to
`Y.structMap ⁻¹ D(a)` viewed over `R`. Built from the base-change ⊣ restrict-scalars adjunction
`baseChangeRingHomEquivFwd` applied to `𝟙`. Its `baseHom` is `pullback.fst Y.structMap (Spec.map
(awayHom a))`, the open immersion `Y|D(a) ↪ Y`. -/
noncomputable def yChartInclA (Y : EllObj R) :
    (EllObj.restrictScalars (awayHom a)).obj (Y.baseChangeRing (awayHom a)) ⟶ Y :=
  baseChangeRingHomEquivFwd Y (awayHom a) (Y.baseChangeRing (awayHom a)) (𝟙 _)

/-- The `b`-chart inclusion `Y|D(b) ⟶ Y`. -/
noncomputable def yChartInclB (Y : EllObj R) :
    (EllObj.restrictScalars (awayHom b)).obj (Y.baseChangeRing (awayHom b)) ⟶ Y :=
  baseChangeRingHomEquivFwd Y (awayHom b) (Y.baseChangeRing (awayHom b)) (𝟙 _)

/-- The overlap-chart inclusion `Y|D(ab) ⟶ Y`. -/
noncomputable def yChartInclAB (Y : EllObj R) :
    (EllObj.restrictScalars (awayHom (a * b))).obj (Y.baseChangeRing (awayHom (a * b))) ⟶ Y :=
  baseChangeRingHomEquivFwd Y (awayHom (a * b)) (Y.baseChangeRing (awayHom (a * b))) (𝟙 _)

@[simp] theorem yChartInclA_baseHom (Y : EllObj R) :
    (yChartInclA a Y).baseHom = pullback.fst Y.structMap (Spec.map (awayHom a)) := by
  rw [yChartInclA, baseChangeRingHomEquivFwd_baseHom]
  exact Category.id_comp _

@[simp] theorem yChartInclB_baseHom (Y : EllObj R) :
    (yChartInclB b Y).baseHom = pullback.fst Y.structMap (Spec.map (awayHom b)) := by
  rw [yChartInclB, baseChangeRingHomEquivFwd_baseHom]
  exact Category.id_comp _

@[simp] theorem yChartInclAB_baseHom (Y : EllObj R) :
    (yChartInclAB a b Y).baseHom = pullback.fst Y.structMap (Spec.map (awayHom (a * b))) := by
  rw [yChartInclAB, baseChangeRingHomEquivFwd_baseHom]
  exact Category.id_comp _

@[simp] theorem yChartInclA_top (Y : EllObj R) :
    (yChartInclA a Y).top
      = pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom a))) := by
  rw [yChartInclA, baseChangeRingHomEquivFwd_top]
  exact Category.id_comp _

@[simp] theorem yChartInclB_top (Y : EllObj R) :
    (yChartInclB b Y).top
      = pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom b))) := by
  rw [yChartInclB, baseChangeRingHomEquivFwd_top]
  exact Category.id_comp _

@[simp] theorem yChartInclAB_top (Y : EllObj R) :
    (yChartInclAB a b Y).top
      = pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom (a * b)))) := by
  rw [yChartInclAB, baseChangeRingHomEquivFwd_top]
  exact Category.id_comp _

/-! ### Overlap-into-chart inclusions `Y|D(ab) ⟶ Y|D(a)`, `Y|D(ab) ⟶ Y|D(b)` -/

/-- Base leg of the overlap-into-`a`-chart inclusion: `Y|D(ab) ⟶ Y|D(a)` on bases, induced by the
localization tower `D(ab) ↪ D(a)`. -/
noncomputable def yOverlapBaseA (Y : EllObj R) :
    ((EllObj.restrictScalars (awayHom (a * b))).obj (Y.baseChangeRing (awayHom (a * b)))).base ⟶
      ((EllObj.restrictScalars (awayHom a)).obj (Y.baseChangeRing (awayHom a))).base :=
  pullback.lift (pullback.fst Y.structMap (Spec.map (awayHom (a * b))))
    (pullback.snd Y.structMap (Spec.map (awayHom (a * b))) ≫ Spec.map (awayProdHomLeft a b))
    (by rw [Category.assoc, ← Spec.map_comp, awayHom_comp_awayProdHomLeft]; exact pullback.condition)

@[simp] theorem yOverlapBaseA_fst (Y : EllObj R) :
    yOverlapBaseA a b Y ≫ pullback.fst Y.structMap (Spec.map (awayHom a))
      = pullback.fst Y.structMap (Spec.map (awayHom (a * b))) :=
  pullback.lift_fst _ _ _

@[simp] theorem yOverlapBaseA_snd (Y : EllObj R) :
    yOverlapBaseA a b Y ≫ pullback.snd Y.structMap (Spec.map (awayHom a))
      = pullback.snd Y.structMap (Spec.map (awayHom (a * b))) ≫ Spec.map (awayProdHomLeft a b) :=
  pullback.lift_snd _ _ _

/-- Curve leg of the overlap-into-`a`-chart inclusion. -/
noncomputable def yOverlapTopA (Y : EllObj R) :
    ((EllObj.restrictScalars (awayHom (a * b))).obj (Y.baseChangeRing (awayHom (a * b)))).curve.E ⟶
      ((EllObj.restrictScalars (awayHom a)).obj (Y.baseChangeRing (awayHom a))).curve.E :=
  pullback.lift
    (pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom (a * b)))))
    (pullback.snd Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom (a * b))))
      ≫ yOverlapBaseA a b Y)
    (by rw [Category.assoc, yOverlapBaseA_fst]; exact pullback.condition)

@[simp] theorem yOverlapTopA_fst (Y : EllObj R) :
    yOverlapTopA a b Y ≫ pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom a)))
      = pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom (a * b)))) :=
  pullback.lift_fst _ _ _

@[simp] theorem yOverlapTopA_snd (Y : EllObj R) :
    yOverlapTopA a b Y ≫ pullback.snd Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom a)))
      = pullback.snd Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom (a * b))))
        ≫ yOverlapBaseA a b Y :=
  pullback.lift_snd _ _ _

/-- The overlap-into-`a`-chart inclusion `Y|D(ab) ⟶ Y|D(a)` in `Ell/R`. -/
noncomputable def yOverlapInclA (Y : EllObj R) :
    (EllObj.restrictScalars (awayHom (a * b))).obj (Y.baseChangeRing (awayHom (a * b))) ⟶
      (EllObj.restrictScalars (awayHom a)).obj (Y.baseChangeRing (awayHom a)) where
  baseHom := yOverlapBaseA a b Y
  base_w := by
    show yOverlapBaseA a b Y
        ≫ (pullback.snd Y.structMap (Spec.map (awayHom a)) ≫ Spec.map (awayHom a))
      = pullback.snd Y.structMap (Spec.map (awayHom (a * b))) ≫ Spec.map (awayHom (a * b))
    rw [← Category.assoc, yOverlapBaseA_snd, Category.assoc, ← Spec.map_comp,
      awayHom_comp_awayProdHomLeft]
  top := yOverlapTopA a b Y
  isPullback := by
    refine IsPullback.of_right (h₁₂ := (yChartInclA a Y).top) ?_ ?_ (yChartInclA a Y).isPullback
    · have e := (yChartInclAB a b Y).isPullback
      rw [yChartInclAB_top, yChartInclAB_baseHom] at e
      rw [yChartInclA_top, yChartInclA_baseHom, yOverlapTopA_fst, yOverlapBaseA_fst]
      exact e
    · show yOverlapTopA a b Y
          ≫ pullback.snd Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom a)))
        = pullback.snd Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom (a * b))))
          ≫ yOverlapBaseA a b Y
      exact yOverlapTopA_snd a b Y
  zero_w := by
    show (Y.baseChangeRing (awayHom (a * b))).curve.zero ≫ yOverlapTopA a b Y
      = yOverlapBaseA a b Y ≫ (Y.baseChangeRing (awayHom a)).curve.zero
    refine pullback.hom_ext (f := Y.curve.π)
      (g := pullback.fst Y.structMap (Spec.map (awayHom a))) ?_ ?_
    · rw [Category.assoc, yOverlapTopA_fst, baseChangeRing_curve_zero_comp_fst, Category.assoc,
        baseChangeRing_curve_zero_comp_fst, ← Category.assoc, yOverlapBaseA_fst]
    · rw [Category.assoc, yOverlapTopA_snd, ← Category.assoc, baseChangeRing_curve_zero_comp_snd,
        Category.id_comp, Category.assoc, baseChangeRing_curve_zero_comp_snd]
      exact (Category.comp_id _).symm

/-- The overlap-into-`a`-chart inclusion composes with the `a`-chart inclusion to the overlap
inclusion into `Y`. -/
theorem yOverlapInclA_chartInclA (Y : EllObj R) :
    yOverlapInclA a b Y ≫ yChartInclA a Y = yChartInclAB a b Y := by
  refine EllHom.ext ?_ ?_
  · show yOverlapBaseA a b Y ≫ (yChartInclA a Y).baseHom = (yChartInclAB a b Y).baseHom
    rw [yChartInclA_baseHom, yChartInclAB_baseHom, yOverlapBaseA_fst]
  · show yOverlapTopA a b Y ≫ (yChartInclA a Y).top = (yChartInclAB a b Y).top
    rw [yChartInclA_top, yChartInclAB_top, yOverlapTopA_fst]

/-- Base leg of the overlap-into-`b`-chart inclusion `Y|D(ab) ⟶ Y|D(b)`. -/
noncomputable def yOverlapBaseB (Y : EllObj R) :
    ((EllObj.restrictScalars (awayHom (a * b))).obj (Y.baseChangeRing (awayHom (a * b)))).base ⟶
      ((EllObj.restrictScalars (awayHom b)).obj (Y.baseChangeRing (awayHom b))).base :=
  pullback.lift (pullback.fst Y.structMap (Spec.map (awayHom (a * b))))
    (pullback.snd Y.structMap (Spec.map (awayHom (a * b))) ≫ Spec.map (awayProdHomRight a b))
    (by rw [Category.assoc, ← Spec.map_comp, awayHom_comp_awayProdHomRight]; exact pullback.condition)

@[simp] theorem yOverlapBaseB_fst (Y : EllObj R) :
    yOverlapBaseB a b Y ≫ pullback.fst Y.structMap (Spec.map (awayHom b))
      = pullback.fst Y.structMap (Spec.map (awayHom (a * b))) :=
  pullback.lift_fst _ _ _

@[simp] theorem yOverlapBaseB_snd (Y : EllObj R) :
    yOverlapBaseB a b Y ≫ pullback.snd Y.structMap (Spec.map (awayHom b))
      = pullback.snd Y.structMap (Spec.map (awayHom (a * b))) ≫ Spec.map (awayProdHomRight a b) :=
  pullback.lift_snd _ _ _

/-- Curve leg of the overlap-into-`b`-chart inclusion. -/
noncomputable def yOverlapTopB (Y : EllObj R) :
    ((EllObj.restrictScalars (awayHom (a * b))).obj (Y.baseChangeRing (awayHom (a * b)))).curve.E ⟶
      ((EllObj.restrictScalars (awayHom b)).obj (Y.baseChangeRing (awayHom b))).curve.E :=
  pullback.lift
    (pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom (a * b)))))
    (pullback.snd Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom (a * b))))
      ≫ yOverlapBaseB a b Y)
    (by rw [Category.assoc, yOverlapBaseB_fst]; exact pullback.condition)

@[simp] theorem yOverlapTopB_fst (Y : EllObj R) :
    yOverlapTopB a b Y ≫ pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom b)))
      = pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom (a * b)))) :=
  pullback.lift_fst _ _ _

@[simp] theorem yOverlapTopB_snd (Y : EllObj R) :
    yOverlapTopB a b Y ≫ pullback.snd Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom b)))
      = pullback.snd Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom (a * b))))
        ≫ yOverlapBaseB a b Y :=
  pullback.lift_snd _ _ _

/-- The overlap-into-`b`-chart inclusion `Y|D(ab) ⟶ Y|D(b)` in `Ell/R`. -/
noncomputable def yOverlapInclB (Y : EllObj R) :
    (EllObj.restrictScalars (awayHom (a * b))).obj (Y.baseChangeRing (awayHom (a * b))) ⟶
      (EllObj.restrictScalars (awayHom b)).obj (Y.baseChangeRing (awayHom b)) where
  baseHom := yOverlapBaseB a b Y
  base_w := by
    show yOverlapBaseB a b Y
        ≫ (pullback.snd Y.structMap (Spec.map (awayHom b)) ≫ Spec.map (awayHom b))
      = pullback.snd Y.structMap (Spec.map (awayHom (a * b))) ≫ Spec.map (awayHom (a * b))
    rw [← Category.assoc, yOverlapBaseB_snd, Category.assoc, ← Spec.map_comp,
      awayHom_comp_awayProdHomRight]
  top := yOverlapTopB a b Y
  isPullback := by
    refine IsPullback.of_right (h₁₂ := (yChartInclB b Y).top) ?_ ?_ (yChartInclB b Y).isPullback
    · have e := (yChartInclAB a b Y).isPullback
      rw [yChartInclAB_top, yChartInclAB_baseHom] at e
      rw [yChartInclB_top, yChartInclB_baseHom, yOverlapTopB_fst, yOverlapBaseB_fst]
      exact e
    · show yOverlapTopB a b Y
          ≫ pullback.snd Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom b)))
        = pullback.snd Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom (a * b))))
          ≫ yOverlapBaseB a b Y
      exact yOverlapTopB_snd a b Y
  zero_w := by
    show (Y.baseChangeRing (awayHom (a * b))).curve.zero ≫ yOverlapTopB a b Y
      = yOverlapBaseB a b Y ≫ (Y.baseChangeRing (awayHom b)).curve.zero
    refine pullback.hom_ext (f := Y.curve.π)
      (g := pullback.fst Y.structMap (Spec.map (awayHom b))) ?_ ?_
    · rw [Category.assoc, yOverlapTopB_fst, baseChangeRing_curve_zero_comp_fst, Category.assoc,
        baseChangeRing_curve_zero_comp_fst, ← Category.assoc, yOverlapBaseB_fst]
    · rw [Category.assoc, yOverlapTopB_snd, ← Category.assoc, baseChangeRing_curve_zero_comp_snd,
        Category.id_comp, Category.assoc, baseChangeRing_curve_zero_comp_snd]
      exact (Category.comp_id _).symm

/-- The overlap-into-`b`-chart inclusion composes with the `b`-chart inclusion to the overlap
inclusion into `Y`. -/
theorem yOverlapInclB_chartInclB (Y : EllObj R) :
    yOverlapInclB a b Y ≫ yChartInclB b Y = yChartInclAB a b Y := by
  refine EllHom.ext ?_ ?_
  · show yOverlapBaseB a b Y ≫ (yChartInclB b Y).baseHom = (yChartInclAB a b Y).baseHom
    rw [yChartInclB_baseHom, yChartInclAB_baseHom, yOverlapBaseB_fst]
  · show yOverlapTopB a b Y ≫ (yChartInclB b Y).top = (yChartInclAB a b Y).top
    rw [yChartInclB_top, yChartInclAB_top, yOverlapTopB_fst]

/-- **Overlap compatibility (cocycle base condition).** The two overlap inclusions into the `a`-
and `b`-charts of `Y` agree after including into `Y`: both equal `Y|D(ab) ⟶ Y`. -/
theorem yOverlap_compat (Y : EllObj R) :
    yOverlapInclA a b Y ≫ yChartInclA a Y = yOverlapInclB a b Y ≫ yChartInclB b Y := by
  rw [yOverlapInclA_chartInclA, yOverlapInclB_chartInclB]

end ZariskiDescent

/-! ## [R-hom-glue] toolkit — cancellation, casts and localization ranges

Generic helpers for the geometric descent `homGlueDescentData` below: mono-cancellation of
`Ell/R`-morphisms, the `P.map`-of-`eqToHom` ↔ `cast` bridge, the ranges of the localization
opens `D(a)`, `D(ab)` and their preimages in a test object, the map into the overlap chart,
and the factorization of a morphism into the glued object through one of its charts. -/

section HomGlueToolkit

set_option backward.isDefEq.respectTransparency false

/-- Cancel an `Ell/R`-morphism whose `baseHom` and `top` are monomorphisms. -/
private theorem ellHom_cancel_mono {Z V Y₀ : EllObj R} (j : V ⟶ Y₀)
    (hb : Mono j.baseHom) (ht : Mono j.top) {v w : Z ⟶ V}
    (h : v ≫ j = w ≫ j) : v = w := by
  have hbase : v.baseHom ≫ j.baseHom = w.baseHom ≫ j.baseHom := by
    have hc := congrArg EllHom.baseHom h
    simpa only [EllHom.comp_baseHom] using hc
  have htop : v.top ≫ j.top = w.top ≫ j.top := by
    have hc := congrArg EllHom.top h
    simpa only [EllHom.comp_top] using hc
  exact EllHom.ext ((cancel_mono j.baseHom).mp hbase) ((cancel_mono j.top).mp htop)

/-- `P.map` of an `eqToHom` is the type-level cast. -/
private theorem map_eqToHom_op {P : ModuliProblem R} {X₁ X₂ : EllObj R} (h : X₁ = X₂)
    (x : P.obj (op X₂)) :
    P.map (eqToHom h).op x = cast (congrArg (fun Z => P.obj (op Z)) h.symm) x := by
  subst h
  rw [eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Two casts of equal elements along (possibly different) proofs of the same type
equality agree. -/
private theorem cast_eq_cast {A B : Type u} (p₁ p₂ : A = B) {x y : A} (h : x = y) :
    cast p₁ x = cast p₂ y := by
  subst h
  subst p₁
  rfl

/-- `P.map` along two `Ell/R`-morphisms with (heterogeneously) equal components, over an
equality of source objects, agree up to cast. The equality proof stays opaque, so this is
kernel-cheap at use sites. -/
private theorem map_congr_ellHom {P : ModuliProblem R} {X X' Y₀ : EllObj R} (h : X = X')
    (f : X ⟶ Y₀) (g : X' ⟶ Y₀) (hb : HEq f.baseHom g.baseHom) (ht : HEq f.top g.top)
    (x : P.obj (op Y₀)) :
    P.map f.op x = cast (congrArg (fun Z => P.obj (op Z)) h.symm) (P.map g.op x) := by
  subst h
  obtain rfl : f = g := EllHom.ext (eq_of_heq hb) (eq_of_heq ht)
  rfl

/-- In `Type u`, an `eqToHom` acts as the cast. -/
private theorem eqToHom_apply_type {A B : Type u} (h : A = B) (x : A) :
    eqToHom h x = cast h x := by
  subst h
  rfl

/-- The range of `Spec R[1/c] ⟶ Spec R` is the basic open `D(c)`. -/
private theorem range_SpecMap_awayHom (c : R) :
    Set.range (Spec.map (awayHom c))
      = (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum R)) := by
  show Set.range (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away c)))) = _
  rw [← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_localizationAway]

/-- Restriction of scalars is full over a mono: an `Ell/R`-morphism between two
restricted objects lifts to `Ell/R'`. -/
private noncomputable def unRestrictScalars {R' : CommRingCat.{u}} (ρ : R ⟶ R')
    [Mono (Spec.map ρ)] {Z Z' : EllObj R'}
    (w : (EllObj.restrictScalars ρ).obj Z ⟶ (EllObj.restrictScalars ρ).obj Z') : Z ⟶ Z' where
  baseHom := w.baseHom
  base_w := by
    have hw : w.baseHom ≫ Z'.structMap ≫ Spec.map ρ = Z.structMap ≫ Spec.map ρ := w.base_w
    rw [← Category.assoc] at hw
    exact (cancel_mono (Spec.map ρ)).mp hw
  top := w.top
  isPullback := w.isPullback
  zero_w := w.zero_w

private theorem restrictScalars_map_unRestrictScalars {R' : CommRingCat.{u}} (ρ : R ⟶ R')
    [Mono (Spec.map ρ)] {Z Z' : EllObj R'}
    (w : (EllObj.restrictScalars ρ).obj Z ⟶ (EllObj.restrictScalars ρ).obj Z') :
    (EllObj.restrictScalars ρ).map (unRestrictScalars ρ w) = w :=
  EllHom.ext rfl rfl

variable (a b : R)

/-- Range condition for the overlap chart: a base map through both `D(a)` and `D(b)`
lands in `D(ab)` after the structure map. -/
private theorem range_toOverlap_cond (Y : EllObj R) {T : Scheme.{u}} (w : T ⟶ Y.base)
    (H1 : ∀ t : T, Y.structMap (w t) ∈ Set.range (Spec.map (awayHom a)))
    (H2 : ∀ t : T, Y.structMap (w t) ∈ Set.range (Spec.map (awayHom b))) :
    Set.range (w ≫ Y.structMap) ⊆ Set.range (Spec.map (awayHom (a * b))) := by
  rintro - ⟨t, rfl⟩
  rw [Scheme.Hom.comp_apply, range_SpecMap_awayHom, PrimeSpectrum.basicOpen_mul]
  refine ⟨?_, ?_⟩
  · have h := H1 t; rwa [range_SpecMap_awayHom] at h
  · have h := H2 t; rwa [range_SpecMap_awayHom] at h

/-- The canonical map from a scheme over `D(ab)` into the overlap chart
`Y ×_{Spec R} Spec R[1/ab]`. -/
private noncomputable def toOverlapBase (Y : EllObj R) {T : Scheme.{u}} (w : T ⟶ Y.base)
    (H : Set.range (w ≫ Y.structMap) ⊆ Set.range (Spec.map (awayHom (a * b)))) :
    T ⟶ pullback Y.structMap (Spec.map (awayHom (a * b))) :=
  pullback.lift w (IsOpenImmersion.lift (Spec.map (awayHom (a * b))) (w ≫ Y.structMap) H)
    (IsOpenImmersion.lift_fac _ _ _).symm

@[simp]
private theorem toOverlapBase_fst (Y : EllObj R) {T : Scheme.{u}} (w : T ⟶ Y.base)
    (H : Set.range (w ≫ Y.structMap) ⊆ Set.range (Spec.map (awayHom (a * b)))) :
    toOverlapBase a b Y w H ≫ pullback.fst Y.structMap (Spec.map (awayHom (a * b))) = w :=
  pullback.lift_fst _ _ _

/-- The overlap map composed with the overlap-into-`a`-chart base leg recovers any given
factorization through the `a`-chart. -/
private theorem toOverlapBase_yOverlapBaseA (Y : EllObj R) {T : Scheme.{u}} (w : T ⟶ Y.base)
    (H : Set.range (w ≫ Y.structMap) ⊆ Set.range (Spec.map (awayHom (a * b))))
    (wA : T ⟶ pullback Y.structMap (Spec.map (awayHom a)))
    (hwA : wA ≫ pullback.fst Y.structMap (Spec.map (awayHom a)) = w) :
    toOverlapBase a b Y w H ≫ yOverlapBaseA a b Y = wA := by
  rw [← cancel_mono (pullback.fst Y.structMap (Spec.map (awayHom a))), Category.assoc,
    yOverlapBaseA_fst, toOverlapBase_fst, hwA]

/-- The mirrored triangle through the `b`-chart. -/
private theorem toOverlapBase_yOverlapBaseB (Y : EllObj R) {T : Scheme.{u}} (w : T ⟶ Y.base)
    (H : Set.range (w ≫ Y.structMap) ⊆ Set.range (Spec.map (awayHom (a * b))))
    (wB : T ⟶ pullback Y.structMap (Spec.map (awayHom b)))
    (hwB : wB ≫ pullback.fst Y.structMap (Spec.map (awayHom b)) = w) :
    toOverlapBase a b Y w H ≫ yOverlapBaseB a b Y = wB := by
  rw [← cancel_mono (pullback.fst Y.structMap (Spec.map (awayHom b))), Category.assoc,
    yOverlapBaseB_fst, toOverlapBase_fst, hwB]

end HomGlueToolkit

/-! ## [R-chart-eqv] factorization through the charts of the glued object

A morphism `V ⟶ glueEllObj …` whose structure map lands in `D(a)` factors uniquely through
the `a`-chart inclusion `glueJa` (and symmetrically for `b`). This is the geometric half of
the per-chart bijection `(Y|D(a) ⟶ glueEllObj) ≃ (Y|D(a) ⟶ Xa over R[1/a])`. -/

section ChartFactor

set_option backward.isDefEq.respectTransparency false

variable (a b : R)
variable (Xa : EllObj (CommRingCat.of (Localization.Away a)))
variable (Xb : EllObj (CommRingCat.of (Localization.Away b)))
variable (φ : Xa.baseChangeRing (awayProdHomLeft a b) ≅ Xb.baseChangeRing (awayProdHomRight a b))

private theorem scheme_id_apply {X : Scheme.{u}} (x : X) : (𝟙 X : X ⟶ X) x = x := by
  simp

/-- A point of the glued base over `D(a)` lies in the `a`-chart. -/
private theorem mem_range_glueBaseInl (z : ↑(glueBase a b Xa Xb φ))
    (hz : glueQ a b Xa Xb φ z ∈ Set.range (Spec.map (awayHom a))) :
    z ∈ Set.range (glueBaseInl a b Xa Xb φ) := by
  rcases glueBase_exists a b Xa Xb φ z with ⟨u, rfl⟩ | ⟨v, rfl⟩
  · exact ⟨u, rfl⟩
  · have h1 : glueQ a b Xa Xb φ (glueBaseInr a b Xa Xb φ v)
        = Spec.map (awayHom b) (Xb.structMap v) := by
      have hc := congr($(glueBaseInr_glueQ a b Xa Xb φ) v)
      rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hc
    have hinj : Function.Injective (Spec.map (awayHom b)) :=
      (Spec.map (awayHom b)).isOpenEmbedding.injective
    have hrr : Set.range (Spec.map (awayProdHomRight a b))
        = Spec.map (awayHom b) ⁻¹' Set.range (Spec.map (awayHom (a * b))) := by
      have hcomp : Spec.map (awayProdHomRight a b) ≫ Spec.map (awayHom b)
          = Spec.map (awayHom (a * b)) := by
        rw [← Spec.map_comp, awayHom_comp_awayProdHomRight]
      have himg : Set.range (Spec.map (awayProdHomRight a b) ≫ Spec.map (awayHom b))
          = Spec.map (awayHom b) '' Set.range (Spec.map (awayProdHomRight a b)) := by
        simp [Scheme.Hom.comp_base, Set.range_comp]
      rw [← hcomp, himg, Set.preimage_image_eq _ hinj]
    have h2 : Xb.structMap v ∈ Set.range (Spec.map (awayProdHomRight a b)) := by
      rw [hrr, Set.mem_preimage, range_SpecMap_awayHom, PrimeSpectrum.basicOpen_mul]
      refine ⟨?_, ?_⟩
      · have h := hz; rw [h1, range_SpecMap_awayHom] at h; exact h
      · have h : Spec.map (awayHom b) (Xb.structMap v)
            ∈ Set.range (Spec.map (awayHom b)) := ⟨Xb.structMap v, rfl⟩
        rwa [range_SpecMap_awayHom] at h
    have h3 : v ∈ Set.range (pullback.fst Xb.structMap (Spec.map (awayProdHomRight a b))) := by
      rw [Scheme.Pullback.range_fst]; exact h2
    obtain ⟨w', hw'⟩ := h3
    haveI : IsIso φ.hom.baseHom := isIso_baseHom_of_iso φ
    refine ⟨glueBaseFst a b Xa (inv φ.hom.baseHom w'), ?_⟩
    have hcond := congr($(glueBase_condition a b Xa Xb φ) (inv φ.hom.baseHom w'))
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hcond
    rw [hcond]
    have hpsidef : glueBasePsi a b Xa Xb φ
        = φ.hom.baseHom ≫ pullback.fst Xb.structMap (Spec.map (awayProdHomRight a b)) := rfl
    have hpsi : glueBasePsi a b Xa Xb φ (inv φ.hom.baseHom w')
        = pullback.fst Xb.structMap (Spec.map (awayProdHomRight a b))
            (φ.hom.baseHom (inv φ.hom.baseHom w')) := by
      have hc := congr($(hpsidef) (inv φ.hom.baseHom w'))
      rwa [Scheme.Hom.comp_apply] at hc
    have hio : φ.hom.baseHom (inv φ.hom.baseHom w') = w' := by
      have hc := congr($(IsIso.inv_hom_id φ.hom.baseHom) w')
      rwa [Scheme.Hom.comp_apply, scheme_id_apply] at hc
    rw [hpsi, hio, hw']

/-- A point of the glued base over `D(b)` lies in the `b`-chart. -/
private theorem mem_range_glueBaseInr (z : ↑(glueBase a b Xa Xb φ))
    (hz : glueQ a b Xa Xb φ z ∈ Set.range (Spec.map (awayHom b))) :
    z ∈ Set.range (glueBaseInr a b Xa Xb φ) := by
  rcases glueBase_exists a b Xa Xb φ z with ⟨u, rfl⟩ | ⟨v, rfl⟩
  · have h1 : glueQ a b Xa Xb φ (glueBaseInl a b Xa Xb φ u)
        = Spec.map (awayHom a) (Xa.structMap u) := by
      have hc := congr($(glueBaseInl_glueQ a b Xa Xb φ) u)
      rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hc
    have hinj : Function.Injective (Spec.map (awayHom a)) :=
      (Spec.map (awayHom a)).isOpenEmbedding.injective
    have hrr : Set.range (Spec.map (awayProdHomLeft a b))
        = Spec.map (awayHom a) ⁻¹' Set.range (Spec.map (awayHom (a * b))) := by
      have hcomp : Spec.map (awayProdHomLeft a b) ≫ Spec.map (awayHom a)
          = Spec.map (awayHom (a * b)) := by
        rw [← Spec.map_comp, awayHom_comp_awayProdHomLeft]
      have himg : Set.range (Spec.map (awayProdHomLeft a b) ≫ Spec.map (awayHom a))
          = Spec.map (awayHom a) '' Set.range (Spec.map (awayProdHomLeft a b)) := by
        simp [Scheme.Hom.comp_base, Set.range_comp]
      rw [← hcomp, himg, Set.preimage_image_eq _ hinj]
    have h2 : Xa.structMap u ∈ Set.range (Spec.map (awayProdHomLeft a b)) := by
      rw [hrr, Set.mem_preimage, range_SpecMap_awayHom, PrimeSpectrum.basicOpen_mul]
      refine ⟨?_, ?_⟩
      · have h : Spec.map (awayHom a) (Xa.structMap u)
            ∈ Set.range (Spec.map (awayHom a)) := ⟨Xa.structMap u, rfl⟩
        rwa [range_SpecMap_awayHom] at h
      · have h := hz; rw [h1, range_SpecMap_awayHom] at h; exact h
    have h3 : u ∈ Set.range (pullback.fst Xa.structMap (Spec.map (awayProdHomLeft a b))) := by
      rw [Scheme.Pullback.range_fst]; exact h2
    obtain ⟨w', hw'⟩ := h3
    refine ⟨glueBasePsi a b Xa Xb φ w', ?_⟩
    have hcond := congr($(glueBase_condition a b Xa Xb φ) w')
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hcond
    rw [← hcond]
    show glueBaseInl a b Xa Xb φ (glueBaseFst a b Xa w') = glueBaseInl a b Xa Xb φ u
    rw [show glueBaseFst a b Xa w' = u from hw']
  · exact ⟨v, rfl⟩

variable {V : EllObj R}

/-- Base range condition for factoring through the `a`-chart. -/
private theorem factor_range_base_a (v : V ⟶ glueEllObj a b Xa Xb φ)
    (hσ : Set.range V.structMap ⊆ Set.range (Spec.map (awayHom a))) :
    Set.range v.baseHom ⊆ Set.range (glueBaseInl a b Xa Xb φ) := by
  rintro - ⟨x, rfl⟩
  refine mem_range_glueBaseInl a b Xa Xb φ _ ?_
  have hb : glueQ a b Xa Xb φ (v.baseHom x) = V.structMap x := by
    have hc := congr($(v.base_w) x)
    rwa [Scheme.Hom.comp_apply] at hc
  rw [hb]
  exact hσ ⟨x, rfl⟩

/-- Total-space range condition for factoring through the `a`-chart. -/
private theorem factor_range_top_a (v : V ⟶ glueEllObj a b Xa Xb φ)
    (hσ : Set.range V.structMap ⊆ Set.range (Spec.map (awayHom a))) :
    Set.range v.top ⊆ Set.range (glueTotalInl a b Xa Xb φ) := by
  show Set.range (v.top : V.curve.E ⟶ glueTotal a b Xa Xb φ)
    ⊆ Set.range (glueTotalInl a b Xa Xb φ)
  rw [range_glueTotalInl]
  rintro - ⟨e, rfl⟩
  rw [Set.mem_preimage]
  have hw : (v.top : V.curve.E ⟶ glueTotal a b Xa Xb φ) ≫ gluePi a b Xa Xb φ
      = V.curve.π ≫ (v.baseHom : V.base ⟶ glueBase a b Xa Xb φ) := v.isPullback.w
  have hc := congr($(hw) e)
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hc
  exact Set.mem_of_eq_of_mem hc
    (factor_range_base_a a b Xa Xb φ v hσ ⟨V.curve.π e, rfl⟩)

/-- Base range condition for factoring through the `b`-chart. -/
private theorem factor_range_base_b (v : V ⟶ glueEllObj a b Xa Xb φ)
    (hσ : Set.range V.structMap ⊆ Set.range (Spec.map (awayHom b))) :
    Set.range v.baseHom ⊆ Set.range (glueBaseInr a b Xa Xb φ) := by
  rintro - ⟨x, rfl⟩
  refine mem_range_glueBaseInr a b Xa Xb φ _ ?_
  have hb : glueQ a b Xa Xb φ (v.baseHom x) = V.structMap x := by
    have hc := congr($(v.base_w) x)
    rwa [Scheme.Hom.comp_apply] at hc
  rw [hb]
  exact hσ ⟨x, rfl⟩

/-- Total-space range condition for factoring through the `b`-chart. -/
private theorem factor_range_top_b (v : V ⟶ glueEllObj a b Xa Xb φ)
    (hσ : Set.range V.structMap ⊆ Set.range (Spec.map (awayHom b))) :
    Set.range v.top ⊆ Set.range (glueTotalInr a b Xa Xb φ) := by
  show Set.range (v.top : V.curve.E ⟶ glueTotal a b Xa Xb φ)
    ⊆ Set.range (glueTotalInr a b Xa Xb φ)
  rw [range_glueTotalInr]
  rintro - ⟨e, rfl⟩
  rw [Set.mem_preimage]
  have hw : (v.top : V.curve.E ⟶ glueTotal a b Xa Xb φ) ≫ gluePi a b Xa Xb φ
      = V.curve.π ≫ (v.baseHom : V.base ⟶ glueBase a b Xa Xb φ) := v.isPullback.w
  have hc := congr($(hw) e)
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hc
  exact Set.mem_of_eq_of_mem hc
    (factor_range_base_b a b Xa Xb φ v hσ ⟨V.curve.π e, rfl⟩)

/-- Structure-map compatibility of an `a`-chart factorization. -/
private theorem factor_base_w_a (v : V ⟶ glueEllObj a b Xa Xb φ)
    (tb : V.base ⟶ Xa.base) (hb : tb ≫ glueBaseInl a b Xa Xb φ = v.baseHom) :
    tb ≫ Xa.structMap ≫ Spec.map (awayHom a) = V.structMap := by
  rw [show Xa.structMap ≫ Spec.map (awayHom a)
      = glueBaseInl a b Xa Xb φ ≫ glueQ a b Xa Xb φ from
    (glueBaseInl_glueQ a b Xa Xb φ).symm, ← Category.assoc, hb]
  exact v.base_w

/-- The cartesian square of an `a`-chart factorization. -/
private theorem factor_isPullback_a (v : V ⟶ glueEllObj a b Xa Xb φ)
    (tb : V.base ⟶ Xa.base) (tt : V.curve.E ⟶ Xa.curve.E)
    (hb : tb ≫ glueBaseInl a b Xa Xb φ = v.baseHom)
    (ht : tt ≫ glueTotalInl a b Xa Xb φ = v.top) :
    IsPullback tt V.curve.π Xa.curve.π tb := by
  have hbig : IsPullback v.top V.curve.π (gluePi a b Xa Xb φ) v.baseHom := v.isPullback
  rw [← ht, ← hb] at hbig
  refine IsPullback.of_right hbig ?_ (isPullback_glueTotalInl a b Xa Xb φ)
  rw [← cancel_mono (glueBaseInl a b Xa Xb φ)]
  calc (tt ≫ Xa.curve.π) ≫ glueBaseInl a b Xa Xb φ
      = tt ≫ glueTotalInl a b Xa Xb φ ≫ gluePi a b Xa Xb φ := by
        rw [Category.assoc, glueTotalInl_gluePi]
    _ = v.top ≫ gluePi a b Xa Xb φ := by rw [← Category.assoc, ht]
    _ = V.curve.π ≫ v.baseHom := v.isPullback.w
    _ = (V.curve.π ≫ tb) ≫ glueBaseInl a b Xa Xb φ := by
        rw [Category.assoc, hb]

/-- Zero-section compatibility of an `a`-chart factorization. -/
private theorem factor_zero_w_a (v : V ⟶ glueEllObj a b Xa Xb φ)
    (tb : V.base ⟶ Xa.base) (tt : V.curve.E ⟶ Xa.curve.E)
    (hb : tb ≫ glueBaseInl a b Xa Xb φ = v.baseHom)
    (ht : tt ≫ glueTotalInl a b Xa Xb φ = v.top) :
    V.curve.zero ≫ tt = tb ≫ Xa.curve.zero := by
  rw [← cancel_mono (glueTotalInl a b Xa Xb φ)]
  calc (V.curve.zero ≫ tt) ≫ glueTotalInl a b Xa Xb φ
      = V.curve.zero ≫ v.top := by rw [Category.assoc, ht]
    _ = v.baseHom ≫ glueZero a b Xa Xb φ := v.zero_w
    _ = tb ≫ glueBaseInl a b Xa Xb φ ≫ glueZero a b Xa Xb φ := by
        rw [← Category.assoc, hb]
    _ = (tb ≫ Xa.curve.zero) ≫ glueTotalInl a b Xa Xb φ := by
        rw [glueBaseInl_glueZero, ← Category.assoc]

/-- **Factorization through the `a`-chart**: a morphism into the glued object whose base
lies over `D(a)` factors through `glueJa`. -/
private noncomputable def factorGlueJa (v : V ⟶ glueEllObj a b Xa Xb φ)
    (hσ : Set.range V.structMap ⊆ Set.range (Spec.map (awayHom a))) :
    V ⟶ (EllObj.restrictScalars (awayHom a)).obj Xa where
  baseHom := IsOpenImmersion.lift (glueBaseInl a b Xa Xb φ) v.baseHom
    (factor_range_base_a a b Xa Xb φ v hσ)
  base_w := factor_base_w_a a b Xa Xb φ v _ (IsOpenImmersion.lift_fac _ _ _)
  top := IsOpenImmersion.lift (glueTotalInl a b Xa Xb φ) v.top
    (factor_range_top_a a b Xa Xb φ v hσ)
  isPullback := factor_isPullback_a a b Xa Xb φ v _ _
    (IsOpenImmersion.lift_fac _ _ _) (IsOpenImmersion.lift_fac _ _ _)
  zero_w := factor_zero_w_a a b Xa Xb φ v _ _
    (IsOpenImmersion.lift_fac _ _ _) (IsOpenImmersion.lift_fac _ _ _)

/-- The defining triangle of the `a`-chart factorization. -/
private theorem factorGlueJa_glueJa (v : V ⟶ glueEllObj a b Xa Xb φ)
    (hσ : Set.range V.structMap ⊆ Set.range (Spec.map (awayHom a))) :
    factorGlueJa a b Xa Xb φ v hσ ≫ glueJa a b Xa Xb φ = v := by
  refine EllHom.ext ?_ ?_
  · show IsOpenImmersion.lift (glueBaseInl a b Xa Xb φ) v.baseHom
        (factor_range_base_a a b Xa Xb φ v hσ) ≫ glueBaseInl a b Xa Xb φ = v.baseHom
    exact IsOpenImmersion.lift_fac _ _ _
  · show IsOpenImmersion.lift (glueTotalInl a b Xa Xb φ) v.top
        (factor_range_top_a a b Xa Xb φ v hσ) ≫ glueTotalInl a b Xa Xb φ = v.top
    exact IsOpenImmersion.lift_fac _ _ _

/-- Structure-map compatibility of a `b`-chart factorization. -/
private theorem factor_base_w_b (v : V ⟶ glueEllObj a b Xa Xb φ)
    (tb : V.base ⟶ Xb.base) (hb : tb ≫ glueBaseInr a b Xa Xb φ = v.baseHom) :
    tb ≫ Xb.structMap ≫ Spec.map (awayHom b) = V.structMap := by
  rw [show Xb.structMap ≫ Spec.map (awayHom b)
      = glueBaseInr a b Xa Xb φ ≫ glueQ a b Xa Xb φ from
    (glueBaseInr_glueQ a b Xa Xb φ).symm, ← Category.assoc, hb]
  exact v.base_w

/-- The cartesian square of a `b`-chart factorization. -/
private theorem factor_isPullback_b (v : V ⟶ glueEllObj a b Xa Xb φ)
    (tb : V.base ⟶ Xb.base) (tt : V.curve.E ⟶ Xb.curve.E)
    (hb : tb ≫ glueBaseInr a b Xa Xb φ = v.baseHom)
    (ht : tt ≫ glueTotalInr a b Xa Xb φ = v.top) :
    IsPullback tt V.curve.π Xb.curve.π tb := by
  have hbig : IsPullback v.top V.curve.π (gluePi a b Xa Xb φ) v.baseHom := v.isPullback
  rw [← ht, ← hb] at hbig
  refine IsPullback.of_right hbig ?_ (isPullback_glueTotalInr a b Xa Xb φ)
  rw [← cancel_mono (glueBaseInr a b Xa Xb φ)]
  calc (tt ≫ Xb.curve.π) ≫ glueBaseInr a b Xa Xb φ
      = tt ≫ glueTotalInr a b Xa Xb φ ≫ gluePi a b Xa Xb φ := by
        rw [Category.assoc, glueTotalInr_gluePi]
    _ = v.top ≫ gluePi a b Xa Xb φ := by rw [← Category.assoc, ht]
    _ = V.curve.π ≫ v.baseHom := v.isPullback.w
    _ = (V.curve.π ≫ tb) ≫ glueBaseInr a b Xa Xb φ := by
        rw [Category.assoc, hb]

/-- Zero-section compatibility of a `b`-chart factorization. -/
private theorem factor_zero_w_b (v : V ⟶ glueEllObj a b Xa Xb φ)
    (tb : V.base ⟶ Xb.base) (tt : V.curve.E ⟶ Xb.curve.E)
    (hb : tb ≫ glueBaseInr a b Xa Xb φ = v.baseHom)
    (ht : tt ≫ glueTotalInr a b Xa Xb φ = v.top) :
    V.curve.zero ≫ tt = tb ≫ Xb.curve.zero := by
  rw [← cancel_mono (glueTotalInr a b Xa Xb φ)]
  calc (V.curve.zero ≫ tt) ≫ glueTotalInr a b Xa Xb φ
      = V.curve.zero ≫ v.top := by rw [Category.assoc, ht]
    _ = v.baseHom ≫ glueZero a b Xa Xb φ := v.zero_w
    _ = tb ≫ glueBaseInr a b Xa Xb φ ≫ glueZero a b Xa Xb φ := by
        rw [← Category.assoc, hb]
    _ = (tb ≫ Xb.curve.zero) ≫ glueTotalInr a b Xa Xb φ := by
        rw [glueBaseInr_glueZero, ← Category.assoc]

/-- **Factorization through the `b`-chart.** -/
private noncomputable def factorGlueJb (v : V ⟶ glueEllObj a b Xa Xb φ)
    (hσ : Set.range V.structMap ⊆ Set.range (Spec.map (awayHom b))) :
    V ⟶ (EllObj.restrictScalars (awayHom b)).obj Xb where
  baseHom := IsOpenImmersion.lift (glueBaseInr a b Xa Xb φ) v.baseHom
    (factor_range_base_b a b Xa Xb φ v hσ)
  base_w := factor_base_w_b a b Xa Xb φ v _ (IsOpenImmersion.lift_fac _ _ _)
  top := IsOpenImmersion.lift (glueTotalInr a b Xa Xb φ) v.top
    (factor_range_top_b a b Xa Xb φ v hσ)
  isPullback := factor_isPullback_b a b Xa Xb φ v _ _
    (IsOpenImmersion.lift_fac _ _ _) (IsOpenImmersion.lift_fac _ _ _)
  zero_w := factor_zero_w_b a b Xa Xb φ v _ _
    (IsOpenImmersion.lift_fac _ _ _) (IsOpenImmersion.lift_fac _ _ _)

/-- The defining triangle of the `b`-chart factorization. -/
private theorem factorGlueJb_glueJb (v : V ⟶ glueEllObj a b Xa Xb φ)
    (hσ : Set.range V.structMap ⊆ Set.range (Spec.map (awayHom b))) :
    factorGlueJb a b Xa Xb φ v hσ ≫ glueJb a b Xa Xb φ = v := by
  refine EllHom.ext ?_ ?_
  · show IsOpenImmersion.lift (glueBaseInr a b Xa Xb φ) v.baseHom
        (factor_range_base_b a b Xa Xb φ v hσ) ≫ glueBaseInr a b Xa Xb φ = v.baseHom
    exact IsOpenImmersion.lift_fac _ _ _
  · show IsOpenImmersion.lift (glueTotalInr a b Xa Xb φ) v.top
        (factor_range_top_b a b Xa Xb φ v hσ) ≫ glueTotalInr a b Xa Xb φ = v.top
    exact IsOpenImmersion.lift_fac _ _ _

/-- `glueJa` is a mono-pair, so factorizations through it are unique. -/
private theorem glueJa_cancel {Z : EllObj R}
    {v w : Z ⟶ (EllObj.restrictScalars (awayHom a)).obj Xa}
    (h : v ≫ glueJa a b Xa Xb φ = w ≫ glueJa a b Xa Xb φ) : v = w :=
  ellHom_cancel_mono (glueJa a b Xa Xb φ)
    (inferInstanceAs (Mono (glueBaseInl a b Xa Xb φ)))
    (inferInstanceAs (Mono (glueTotalInl a b Xa Xb φ))) h

private theorem glueJb_cancel {Z : EllObj R}
    {v w : Z ⟶ (EllObj.restrictScalars (awayHom b)).obj Xb}
    (h : v ≫ glueJb a b Xa Xb φ = w ≫ glueJb a b Xa Xb φ) : v = w :=
  ellHom_cancel_mono (glueJb a b Xa Xb φ)
    (inferInstanceAs (Mono (glueBaseInr a b Xa Xb φ)))
    (inferInstanceAs (Mono (glueTotalInr a b Xa Xb φ))) h

end ChartFactor

/-! ## [R-chart-eqv] the overlap bridge

The overlap compatibility of the two chart values, matched through `overlapIso`. The two
`P`-restrictions to the overlap chart `Y|D(ab)` are computed through the representations of
`P.baseChange (awayHom (a*b))` by the two base-changed representing objects, and equality of
the values is equivalent to a geometric equality of comparison morphisms through
`overlapIso` — which in turn is equivalent to agreement of the two glued chart morphisms. -/

section OverlapBridge

set_option backward.isDefEq.respectTransparency false

variable (a b : R)

/-- The overlap-into-`a`-chart inclusion at the `R[1/a]`-level (same underlying data as
`yOverlapInclA`, viewed as a morphism of `Ell/R[1/a]`). -/
private noncomputable def yOverlapLiftA (Y : EllObj R) :
    (EllObj.restrictScalars (awayProdHomLeft a b)).obj (Y.baseChangeRing (awayHom (a * b)))
      ⟶ Y.baseChangeRing (awayHom a) where
  baseHom := yOverlapBaseA a b Y
  base_w := yOverlapBaseA_snd a b Y
  top := yOverlapTopA a b Y
  isPullback := (yOverlapInclA a b Y).isPullback
  zero_w := (yOverlapInclA a b Y).zero_w

/-- The overlap-into-`b`-chart inclusion at the `R[1/b]`-level. -/
private noncomputable def yOverlapLiftB (Y : EllObj R) :
    (EllObj.restrictScalars (awayProdHomRight a b)).obj (Y.baseChangeRing (awayHom (a * b)))
      ⟶ Y.baseChangeRing (awayHom b) where
  baseHom := yOverlapBaseB a b Y
  base_w := yOverlapBaseB_snd a b Y
  top := yOverlapTopB a b Y
  isPullback := (yOverlapInclB a b Y).isPullback
  zero_w := (yOverlapInclB a b Y).zero_w

/-- Restriction along `awayHom (a*b)` is restriction along `awayProdHomLeft` then
`awayHom a`, on objects. -/
private theorem restrictScalars_obj_overlapA (Y : EllObj R) :
    (EllObj.restrictScalars (awayHom (a * b))).obj (Y.baseChangeRing (awayHom (a * b)))
      = (EllObj.restrictScalars (awayHom a)).obj
          ((EllObj.restrictScalars (awayProdHomLeft a b)).obj
            (Y.baseChangeRing (awayHom (a * b)))) := by
  have h1 : awayHom (R := R) (a * b) = awayHom a ≫ awayProdHomLeft a b :=
    (awayHom_comp_awayProdHomLeft a b).symm
  calc (EllObj.restrictScalars (awayHom (a * b))).obj (Y.baseChangeRing (awayHom (a * b)))
      = (EllObj.restrictScalars (awayHom a ≫ awayProdHomLeft a b)).obj
          (Y.baseChangeRing (awayHom (a * b))) :=
        congrArg (fun ρ => (EllObj.restrictScalars ρ).obj (Y.baseChangeRing (awayHom (a * b)))) h1
    _ = _ :=
        Functor.congr_obj (EllObj.restrictScalars_comp (awayHom a) (awayProdHomLeft a b))
          (Y.baseChangeRing (awayHom (a * b)))

private theorem restrictScalars_obj_overlapB (Y : EllObj R) :
    (EllObj.restrictScalars (awayHom (a * b))).obj (Y.baseChangeRing (awayHom (a * b)))
      = (EllObj.restrictScalars (awayHom b)).obj
          ((EllObj.restrictScalars (awayProdHomRight a b)).obj
            (Y.baseChangeRing (awayHom (a * b)))) := by
  have h1 : awayHom (R := R) (a * b) = awayHom b ≫ awayProdHomRight a b :=
    (awayHom_comp_awayProdHomRight a b).symm
  calc (EllObj.restrictScalars (awayHom (a * b))).obj (Y.baseChangeRing (awayHom (a * b)))
      = (EllObj.restrictScalars (awayHom b ≫ awayProdHomRight a b)).obj
          (Y.baseChangeRing (awayHom (a * b))) :=
        congrArg (fun ρ => (EllObj.restrictScalars ρ).obj (Y.baseChangeRing (awayHom (a * b)))) h1
    _ = _ :=
        Functor.congr_obj (EllObj.restrictScalars_comp (awayHom b) (awayProdHomRight a b))
          (Y.baseChangeRing (awayHom (a * b)))

/-- `ofIso` along an `eqToIso` of moduli problems is a cast of the value. -/
private theorem ofIso_eqToIso_homEquiv {R₀ : CommRingCat.{u}} {F F' : ModuliProblem R₀}
    {X : EllObj R₀} (e : F.RepresentableBy X) (h : F = F') {Z : EllObj R₀} (m : Z ⟶ X) :
    (e.ofIso (eqToIso h)).homEquiv m
      = cast (congrArg (fun G : ModuliProblem R₀ => G.obj (op Z)) h) (e.homEquiv m) := by
  subst h
  show ((eqToIso rfl).app (op Z)).toEquiv (e.homEquiv m) = _
  rw [eqToIso_refl]
  rfl

variable {P : ModuliProblem R}
variable {Xa : EllObj (CommRingCat.of (Localization.Away a))}
variable {Xb : EllObj (CommRingCat.of (Localization.Away b))}

/-- The representation of `P.baseChange (awayHom (a*b))` by `Xa.baseChangeRing …` used in
`overlapIso` (the `a`-side). -/
private noncomputable def reprOverlapA
    (repr_a : (P.baseChange (awayHom a)).RepresentableBy Xa) :
    (P.baseChange (awayHom (a * b))).RepresentableBy
      (Xa.baseChangeRing (awayProdHomLeft a b)) :=
  (representableBy_baseChangeRing repr_a (awayProdHomLeft a b)).ofIso
    (eqToIso (by rw [← ModuliProblem.baseChange_comp, awayHom_comp_awayProdHomLeft]))

/-- The `b`-side. -/
private noncomputable def reprOverlapB
    (repr_b : (P.baseChange (awayHom b)).RepresentableBy Xb) :
    (P.baseChange (awayHom (a * b))).RepresentableBy
      (Xb.baseChangeRing (awayProdHomRight a b)) :=
  (representableBy_baseChangeRing repr_b (awayProdHomRight a b)).ofIso
    (eqToIso (by rw [← ModuliProblem.baseChange_comp, awayHom_comp_awayProdHomRight]))

/-- `overlapIso` is the comparison of the two overlap representations. -/
private theorem overlapIso_eq (repr_a : (P.baseChange (awayHom a)).RepresentableBy Xa)
    (repr_b : (P.baseChange (awayHom b)).RepresentableBy Xb) :
    overlapIso a b repr_a repr_b
      = (reprOverlapA a b repr_a).uniqueUpToIso (reprOverlapB a b repr_b) := rfl

/-- The Yoneda preimage of a transformation between representables is its value at the
identity. -/
private theorem yoneda_fullyFaithful_preimage_eq {C : Type*} [Category C] {X X' : C}
    (τ : yoneda.obj X ⟶ yoneda.obj X') :
    Yoneda.fullyFaithful.preimage τ = τ.app (op X) (𝟙 X) := by
  conv_rhs => rw [← Functor.FullyFaithful.map_preimage Yoneda.fullyFaithful τ]
  rw [yoneda_map_app]
  show Yoneda.fullyFaithful.preimage τ = 𝟙 X ≫ Yoneda.fullyFaithful.preimage τ
  rw [Category.id_comp]

universe u₁ u₂

/-- Generic form of the `uniqueUpToIso` compatibility: composing with the canonical
comparison of two representing objects intertwines the two `homEquiv`s. Stated with the
representations as variables, so all reductions are structural. -/
private theorem uniqueUpToIso_homEquiv_hom {C : Type u₂} [Category.{u₁} C]
    {F : Cᵒᵖ ⥤ Type u₁} {X₁ X₂ : C} (e₁ : F.RepresentableBy X₁) (e₂ : F.RepresentableBy X₂)
    {Z : C} (m : Z ⟶ X₁) :
    e₂.homEquiv (m ≫ (e₁.uniqueUpToIso e₂).hom) = e₁.homEquiv m := by
  rw [Functor.RepresentableBy.homEquiv_comp, Functor.RepresentableBy.uniqueUpToIso_hom,
    yoneda_fullyFaithful_preimage_eq]
  show F.map m.op (e₂.homEquiv (e₂.homEquiv.symm (e₁.homEquiv (𝟙 X₁)))) = e₁.homEquiv m
  rw [Equiv.apply_symm_apply, ← Functor.RepresentableBy.homEquiv_eq]

/-- The two overlap representations agree through `overlapIso`. -/
private theorem reprOverlap_homEquiv_hom
    (repr_a : (P.baseChange (awayHom a)).RepresentableBy Xa)
    (repr_b : (P.baseChange (awayHom b)).RepresentableBy Xb)
    {Z : EllObj (CommRingCat.of (Localization.Away (a * b)))}
    (m : Z ⟶ Xa.baseChangeRing (awayProdHomLeft a b)) :
    (reprOverlapB a b repr_b).homEquiv (m ≫ (overlapIso a b repr_a repr_b).hom)
      = (reprOverlapA a b repr_a).homEquiv m := by
  rw [overlapIso_eq a b repr_a repr_b]
  exact uniqueUpToIso_homEquiv_hom (reprOverlapA a b repr_a) (reprOverlapB a b repr_b) m

/-- The comparison morphism from `Y|D(ab)` into the `a`-side overlap object, induced by a
chart morphism `ka`. -/
private noncomputable def overlapCompareA (Y : EllObj R)
    (ka : Y.baseChangeRing (awayHom a) ⟶ Xa) :
    Y.baseChangeRing (awayHom (a * b)) ⟶ Xa.baseChangeRing (awayProdHomLeft a b) :=
  baseChangeRingHomEquivInv Xa (awayProdHomLeft a b) (Y.baseChangeRing (awayHom (a * b)))
    (yOverlapLiftA a b Y ≫ ka)

private noncomputable def overlapCompareB (Y : EllObj R)
    (kb : Y.baseChangeRing (awayHom b) ⟶ Xb) :
    Y.baseChangeRing (awayHom (a * b)) ⟶ Xb.baseChangeRing (awayProdHomRight a b) :=
  baseChangeRingHomEquivInv Xb (awayProdHomRight a b) (Y.baseChangeRing (awayHom (a * b)))
    (yOverlapLiftB a b Y ≫ kb)

private theorem overlapCompareA_baseHom (Y : EllObj R)
    (ka : Y.baseChangeRing (awayHom a) ⟶ Xa) :
    (overlapCompareA a b Y ka).baseHom
      = bcInvBase Xa (awayProdHomLeft a b) (Y.baseChangeRing (awayHom (a * b)))
          (yOverlapLiftA a b Y ≫ ka) := rfl

private theorem overlapCompareA_top (Y : EllObj R)
    (ka : Y.baseChangeRing (awayHom a) ⟶ Xa) :
    (overlapCompareA a b Y ka).top
      = bcInvTop Xa (awayProdHomLeft a b) (Y.baseChangeRing (awayHom (a * b)))
          (yOverlapLiftA a b Y ≫ ka) := rfl

private theorem overlapCompareB_baseHom (Y : EllObj R)
    (kb : Y.baseChangeRing (awayHom b) ⟶ Xb) :
    (overlapCompareB a b Y kb).baseHom
      = bcInvBase Xb (awayProdHomRight a b) (Y.baseChangeRing (awayHom (a * b)))
          (yOverlapLiftB a b Y ≫ kb) := rfl

private theorem overlapCompareB_top (Y : EllObj R)
    (kb : Y.baseChangeRing (awayHom b) ⟶ Xb) :
    (overlapCompareB a b Y kb).top
      = bcInvTop Xb (awayProdHomRight a b) (Y.baseChangeRing (awayHom (a * b)))
          (yOverlapLiftB a b Y ≫ kb) := rfl

private theorem overlapA_hinner
    (repr_a : (P.baseChange (awayHom a)).RepresentableBy Xa) (Y : EllObj R)
    (ka : Y.baseChangeRing (awayHom a) ⟶ Xa) :
    P.map ((EllObj.restrictScalars (awayHom a)).map (yOverlapLiftA a b Y)).op
      (repr_a.homEquiv ka) = repr_a.homEquiv (yOverlapLiftA a b Y ≫ ka) :=
  (repr_a.homEquiv_comp (yOverlapLiftA a b Y) ka).symm

private theorem overlapA_hfwd (Y : EllObj R)
    (ka : Y.baseChangeRing (awayHom a) ⟶ Xa) :
    baseChangeRingHomEquivFwd Xa (awayProdHomLeft a b)
      (Y.baseChangeRing (awayHom (a * b))) (overlapCompareA a b Y ka)
      = yOverlapLiftA a b Y ≫ ka := by
  show (baseChangeRingHomEquiv Xa (awayProdHomLeft a b) (Y.baseChangeRing (awayHom (a * b))))
      ((baseChangeRingHomEquiv Xa (awayProdHomLeft a b)
        (Y.baseChangeRing (awayHom (a * b)))).symm (yOverlapLiftA a b Y ≫ ka))
    = yOverlapLiftA a b Y ≫ ka
  exact Equiv.apply_symm_apply _ _

/-- Syntactic middle normal form of the double restriction
`(restrictScalars (awayHom a)).obj ((restrictScalars (awayProdHomLeft a b)).obj (Y|D(ab)))`.
Spelled as an explicit structure literal so that kernel comparisons against either
presentation are cheap head-mismatch cascades (never a doomed congruence descent through
mismatched localization instance towers). -/
private noncomputable def overlapMidA (Y : EllObj R) : EllObj R where
  base := ((EllObj.restrictScalars (awayProdHomLeft a b)).obj
    (Y.baseChangeRing (awayHom (a * b)))).base
  structMap := ((EllObj.restrictScalars (awayProdHomLeft a b)).obj
    (Y.baseChangeRing (awayHom (a * b)))).structMap ≫ Spec.map (awayHom a)
  curve := ((EllObj.restrictScalars (awayProdHomLeft a b)).obj
    (Y.baseChangeRing (awayHom (a * b)))).curve

private theorem overlapMidA_eq (Y : EllObj R) :
    overlapMidA a b Y
      = (EllObj.restrictScalars (awayHom a)).obj
          ((EllObj.restrictScalars (awayProdHomLeft a b)).obj
            (Y.baseChangeRing (awayHom (a * b)))) := rfl

/-- The object identification `Y|D(ab)` (over `R`) with the middle normal form. -/
private theorem overlapObjA_eq (Y : EllObj R) :
    (EllObj.restrictScalars (awayHom (a * b))).obj (Y.baseChangeRing (awayHom (a * b)))
      = overlapMidA a b Y :=
  (restrictScalars_obj_overlapA a b Y).trans (overlapMidA_eq a b Y).symm

/-- The overlap-into-`a`-chart inclusion re-typed at the middle normal form. -/
private noncomputable def overlapMidHomA (Y : EllObj R) :
    overlapMidA a b Y ⟶ (EllObj.restrictScalars (awayHom a)).obj (Y.baseChangeRing (awayHom a))
    where
  baseHom := yOverlapBaseA a b Y
  base_w := by
    show yOverlapBaseA a b Y
        ≫ pullback.snd Y.structMap (Spec.map (awayHom a)) ≫ Spec.map (awayHom a)
      = (pullback.snd Y.structMap (Spec.map (awayHom (a * b)))
          ≫ Spec.map (awayProdHomLeft a b)) ≫ Spec.map (awayHom a)
    rw [← Category.assoc, yOverlapBaseA_snd]
  top := yOverlapTopA a b Y
  isPullback := (yOverlapInclA a b Y).isPullback
  zero_w := (yOverlapInclA a b Y).zero_w

/-- The middle-typed inclusion is the scalar restriction of the `R[1/a]`-level one. -/
private theorem overlapMidHomA_eq (Y : EllObj R) :
    overlapMidHomA a b Y
      = ((EllObj.restrictScalars (awayHom a)).map (yOverlapLiftA a b Y) :
          overlapMidA a b Y
            ⟶ (EllObj.restrictScalars (awayHom a)).obj (Y.baseChangeRing (awayHom a))) :=
  EllHom.ext rfl rfl

private theorem overlapA_hmap
    (repr_a : (P.baseChange (awayHom a)).RepresentableBy Xa) (Y : EllObj R)
    (ka : Y.baseChangeRing (awayHom a) ⟶ Xa) :
    P.map (yOverlapInclA a b Y).op (repr_a.homEquiv ka)
      = cast (congrArg (fun Z => P.obj (op Z)) (overlapObjA_eq a b Y).symm)
          (P.map ((EllObj.restrictScalars (awayHom a)).map (yOverlapLiftA a b Y)).op
            (repr_a.homEquiv ka)) := by
  have h1 : P.map (yOverlapInclA a b Y).op (repr_a.homEquiv ka)
      = cast (congrArg (fun Z => P.obj (op Z)) (overlapObjA_eq a b Y).symm)
          (P.map (overlapMidHomA a b Y).op (repr_a.homEquiv ka)) :=
    map_congr_ellHom (overlapObjA_eq a b Y) (yOverlapInclA a b Y) (overlapMidHomA a b Y)
      HEq.rfl HEq.rfl (repr_a.homEquiv ka)
  rw [overlapMidHomA_eq a b Y] at h1
  exact h1

private theorem overlapA_hRHS
    (repr_a : (P.baseChange (awayHom a)).RepresentableBy Xa) (Y : EllObj R)
    (ka : Y.baseChangeRing (awayHom a) ⟶ Xa) :
    (reprOverlapA a b repr_a).homEquiv (overlapCompareA a b Y ka)
      = cast (congrArg (fun G : ModuliProblem (CommRingCat.of (Localization.Away (a * b))) =>
            G.obj (op (Y.baseChangeRing (awayHom (a * b)))))
          (show (P.baseChange (awayHom a)).baseChange (awayProdHomLeft a b)
              = P.baseChange (awayHom (a * b)) by
            rw [← ModuliProblem.baseChange_comp, awayHom_comp_awayProdHomLeft]))
          (repr_a.homEquiv (yOverlapLiftA a b Y ≫ ka)) := by
  rw [show (reprOverlapA a b repr_a).homEquiv (overlapCompareA a b Y ka)
      = ((representableBy_baseChangeRing repr_a (awayProdHomLeft a b)).ofIso
          (eqToIso (by rw [← ModuliProblem.baseChange_comp,
            awayHom_comp_awayProdHomLeft]))).homEquiv (overlapCompareA a b Y ka) from rfl]
  rw [ofIso_eqToIso_homEquiv]
  refine cast_eq_cast _ _ ?_
  show repr_a.homEquiv (baseChangeRingHomEquivFwd Xa (awayProdHomLeft a b)
      (Y.baseChangeRing (awayHom (a * b))) (overlapCompareA a b Y ka)) = _
  rw [overlapA_hfwd a b Y ka]

/-- **[OVL-a]** The `P`-restriction of an `a`-chart value to the overlap chart, computed
through the `a`-side overlap representation. -/
private theorem map_overlapA_homEquiv
    (repr_a : (P.baseChange (awayHom a)).RepresentableBy Xa) (Y : EllObj R)
    (ka : Y.baseChangeRing (awayHom a) ⟶ Xa) :
    P.map (yOverlapInclA a b Y).op (repr_a.homEquiv ka)
      = (reprOverlapA a b repr_a).homEquiv (overlapCompareA a b Y ka) := by
  rw [overlapA_hmap a b repr_a Y ka, overlapA_hinner a b repr_a Y ka]
  exact (cast_eq_cast _ _ rfl).trans (overlapA_hRHS a b repr_a Y ka).symm

private theorem overlapB_hinner
    (repr_b : (P.baseChange (awayHom b)).RepresentableBy Xb) (Y : EllObj R)
    (kb : Y.baseChangeRing (awayHom b) ⟶ Xb) :
    P.map ((EllObj.restrictScalars (awayHom b)).map (yOverlapLiftB a b Y)).op
      (repr_b.homEquiv kb) = repr_b.homEquiv (yOverlapLiftB a b Y ≫ kb) :=
  (repr_b.homEquiv_comp (yOverlapLiftB a b Y) kb).symm

private theorem overlapB_hfwd (Y : EllObj R)
    (kb : Y.baseChangeRing (awayHom b) ⟶ Xb) :
    baseChangeRingHomEquivFwd Xb (awayProdHomRight a b)
      (Y.baseChangeRing (awayHom (a * b))) (overlapCompareB a b Y kb)
      = yOverlapLiftB a b Y ≫ kb := by
  show (baseChangeRingHomEquiv Xb (awayProdHomRight a b) (Y.baseChangeRing (awayHom (a * b))))
      ((baseChangeRingHomEquiv Xb (awayProdHomRight a b)
        (Y.baseChangeRing (awayHom (a * b)))).symm (yOverlapLiftB a b Y ≫ kb))
    = yOverlapLiftB a b Y ≫ kb
  exact Equiv.apply_symm_apply _ _

/-- Mirrored middle normal form for the `b`-side. -/
private noncomputable def overlapMidB (Y : EllObj R) : EllObj R where
  base := ((EllObj.restrictScalars (awayProdHomRight a b)).obj
    (Y.baseChangeRing (awayHom (a * b)))).base
  structMap := ((EllObj.restrictScalars (awayProdHomRight a b)).obj
    (Y.baseChangeRing (awayHom (a * b)))).structMap ≫ Spec.map (awayHom b)
  curve := ((EllObj.restrictScalars (awayProdHomRight a b)).obj
    (Y.baseChangeRing (awayHom (a * b)))).curve

private theorem overlapMidB_eq (Y : EllObj R) :
    overlapMidB a b Y
      = (EllObj.restrictScalars (awayHom b)).obj
          ((EllObj.restrictScalars (awayProdHomRight a b)).obj
            (Y.baseChangeRing (awayHom (a * b)))) := rfl

private theorem overlapObjB_eq (Y : EllObj R) :
    (EllObj.restrictScalars (awayHom (a * b))).obj (Y.baseChangeRing (awayHom (a * b)))
      = overlapMidB a b Y :=
  (restrictScalars_obj_overlapB a b Y).trans (overlapMidB_eq a b Y).symm

private noncomputable def overlapMidHomB (Y : EllObj R) :
    overlapMidB a b Y ⟶ (EllObj.restrictScalars (awayHom b)).obj (Y.baseChangeRing (awayHom b))
    where
  baseHom := yOverlapBaseB a b Y
  base_w := by
    show yOverlapBaseB a b Y
        ≫ pullback.snd Y.structMap (Spec.map (awayHom b)) ≫ Spec.map (awayHom b)
      = (pullback.snd Y.structMap (Spec.map (awayHom (a * b)))
          ≫ Spec.map (awayProdHomRight a b)) ≫ Spec.map (awayHom b)
    rw [← Category.assoc, yOverlapBaseB_snd]
  top := yOverlapTopB a b Y
  isPullback := (yOverlapInclB a b Y).isPullback
  zero_w := (yOverlapInclB a b Y).zero_w

private theorem overlapMidHomB_eq (Y : EllObj R) :
    overlapMidHomB a b Y
      = ((EllObj.restrictScalars (awayHom b)).map (yOverlapLiftB a b Y) :
          overlapMidB a b Y
            ⟶ (EllObj.restrictScalars (awayHom b)).obj (Y.baseChangeRing (awayHom b))) :=
  EllHom.ext rfl rfl

private theorem overlapB_hmap
    (repr_b : (P.baseChange (awayHom b)).RepresentableBy Xb) (Y : EllObj R)
    (kb : Y.baseChangeRing (awayHom b) ⟶ Xb) :
    P.map (yOverlapInclB a b Y).op (repr_b.homEquiv kb)
      = cast (congrArg (fun Z => P.obj (op Z)) (overlapObjB_eq a b Y).symm)
          (P.map ((EllObj.restrictScalars (awayHom b)).map (yOverlapLiftB a b Y)).op
            (repr_b.homEquiv kb)) := by
  have h1 : P.map (yOverlapInclB a b Y).op (repr_b.homEquiv kb)
      = cast (congrArg (fun Z => P.obj (op Z)) (overlapObjB_eq a b Y).symm)
          (P.map (overlapMidHomB a b Y).op (repr_b.homEquiv kb)) :=
    map_congr_ellHom (overlapObjB_eq a b Y) (yOverlapInclB a b Y) (overlapMidHomB a b Y)
      HEq.rfl HEq.rfl (repr_b.homEquiv kb)
  rw [overlapMidHomB_eq a b Y] at h1
  exact h1

private theorem overlapB_hRHS
    (repr_b : (P.baseChange (awayHom b)).RepresentableBy Xb) (Y : EllObj R)
    (kb : Y.baseChangeRing (awayHom b) ⟶ Xb) :
    (reprOverlapB a b repr_b).homEquiv (overlapCompareB a b Y kb)
      = cast (congrArg (fun G : ModuliProblem (CommRingCat.of (Localization.Away (a * b))) =>
            G.obj (op (Y.baseChangeRing (awayHom (a * b)))))
          (show (P.baseChange (awayHom b)).baseChange (awayProdHomRight a b)
              = P.baseChange (awayHom (a * b)) by
            rw [← ModuliProblem.baseChange_comp, awayHom_comp_awayProdHomRight]))
          (repr_b.homEquiv (yOverlapLiftB a b Y ≫ kb)) := by
  rw [show (reprOverlapB a b repr_b).homEquiv (overlapCompareB a b Y kb)
      = ((representableBy_baseChangeRing repr_b (awayProdHomRight a b)).ofIso
          (eqToIso (by rw [← ModuliProblem.baseChange_comp,
            awayHom_comp_awayProdHomRight]))).homEquiv (overlapCompareB a b Y kb) from rfl]
  rw [ofIso_eqToIso_homEquiv]
  refine cast_eq_cast _ _ ?_
  show repr_b.homEquiv (baseChangeRingHomEquivFwd Xb (awayProdHomRight a b)
      (Y.baseChangeRing (awayHom (a * b))) (overlapCompareB a b Y kb)) = _
  rw [overlapB_hfwd a b Y kb]

/-- **[OVL-b]** The mirrored computation for the `b`-chart. -/
private theorem map_overlapB_homEquiv
    (repr_b : (P.baseChange (awayHom b)).RepresentableBy Xb) (Y : EllObj R)
    (kb : Y.baseChangeRing (awayHom b) ⟶ Xb) :
    P.map (yOverlapInclB a b Y).op (repr_b.homEquiv kb)
      = (reprOverlapB a b repr_b).homEquiv (overlapCompareB a b Y kb) := by
  rw [overlapB_hmap a b repr_b Y kb, overlapB_hinner a b repr_b Y kb]
  exact (cast_eq_cast _ _ rfl).trans (overlapB_hRHS a b repr_b Y kb).symm

/-- **Value agreement on the overlap ⟺ the comparison morphisms match through
`overlapIso`.** -/
private theorem overlap_value_iff
    (repr_a : (P.baseChange (awayHom a)).RepresentableBy Xa)
    (repr_b : (P.baseChange (awayHom b)).RepresentableBy Xb) (Y : EllObj R)
    (ka : Y.baseChangeRing (awayHom a) ⟶ Xa) (kb : Y.baseChangeRing (awayHom b) ⟶ Xb) :
    (P.map (yOverlapInclA a b Y).op (repr_a.homEquiv ka)
        = P.map (yOverlapInclB a b Y).op (repr_b.homEquiv kb))
      ↔ overlapCompareA a b Y ka ≫ (overlapIso a b repr_a repr_b).hom
          = overlapCompareB a b Y kb := by
  rw [map_overlapA_homEquiv a b repr_a Y ka, map_overlapB_homEquiv a b repr_b Y kb,
    ← reprOverlap_homEquiv_hom a b repr_a repr_b]
  exact ⟨fun h => (reprOverlapB a b repr_b).homEquiv.injective h, fun h => congrArg _ h⟩

/-- **[(⋆) ⟹ (†)]** If the two overlap comparison morphisms match through `overlapIso`,
the glued chart morphisms agree on the overlap chart. -/
private theorem overlap_agree_of_compare
    (repr_a : (P.baseChange (awayHom a)).RepresentableBy Xa)
    (repr_b : (P.baseChange (awayHom b)).RepresentableBy Xb) (Y : EllObj R)
    (ka : Y.baseChangeRing (awayHom a) ⟶ Xa) (kb : Y.baseChangeRing (awayHom b) ⟶ Xb)
    (h3 : overlapCompareA a b Y ka ≫ (overlapIso a b repr_a repr_b).hom
      = overlapCompareB a b Y kb) :
    yOverlapInclA a b Y ≫ (EllObj.restrictScalars (awayHom a)).map ka
        ≫ glueJa a b Xa Xb (overlapIso a b repr_a repr_b)
      = yOverlapInclB a b Y ≫ (EllObj.restrictScalars (awayHom b)).map kb
        ≫ glueJb a b Xa Xb (overlapIso a b repr_a repr_b) := by
  set φ := overlapIso a b repr_a repr_b with hφ
  have h3base : (overlapCompareA a b Y ka).baseHom ≫ φ.hom.baseHom
      = (overlapCompareB a b Y kb).baseHom := by
    have hc := congrArg EllHom.baseHom h3
    simpa only [EllHom.comp_baseHom] using hc
  have h3top : (overlapCompareA a b Y ka).top ≫ φ.hom.top
      = (overlapCompareB a b Y kb).top := by
    have hc := congrArg EllHom.top h3
    simpa only [EllHom.comp_top] using hc
  have hA1 : (overlapCompareA a b Y ka).baseHom ≫ glueBaseFst a b Xa
      = yOverlapBaseA a b Y ≫ ka.baseHom := by
    rw [overlapCompareA_baseHom]
    exact bcInvBase_fst _ _ _ _
  have hB1 : (overlapCompareB a b Y kb).baseHom
        ≫ pullback.fst Xb.structMap (Spec.map (awayProdHomRight a b))
      = yOverlapBaseB a b Y ≫ kb.baseHom := by
    rw [overlapCompareB_baseHom]
    exact bcInvBase_fst _ _ _ _
  have hA1t : (overlapCompareA a b Y ka).top ≫ glueCurveFst a b Xa
      = yOverlapTopA a b Y ≫ ka.top := by
    rw [overlapCompareA_top]
    exact bcInvTop_fst _ _ _ _
  have hB1t : (overlapCompareB a b Y kb).top
        ≫ pullback.fst Xb.curve.π (pullback.fst Xb.structMap (Spec.map (awayProdHomRight a b)))
      = yOverlapTopB a b Y ≫ kb.top := by
    rw [overlapCompareB_top]
    exact bcInvTop_fst _ _ _ _
  have hpsib : φ.hom.baseHom ≫ pullback.fst Xb.structMap (Spec.map (awayProdHomRight a b))
      = glueBasePsi a b Xa Xb φ := rfl
  have hpsit : φ.hom.top
        ≫ pullback.fst Xb.curve.π (pullback.fst Xb.structMap (Spec.map (awayProdHomRight a b)))
      = glueCurvePsi a b Xa Xb φ := rfl
  refine EllHom.ext ?_ ?_
  · show yOverlapBaseA a b Y ≫ ka.baseHom ≫ glueBaseInl a b Xa Xb φ
      = yOverlapBaseB a b Y ≫ kb.baseHom ≫ glueBaseInr a b Xa Xb φ
    rw [← reassoc_of% hA1, glueBase_condition, ← hpsib, Category.assoc,
      reassoc_of% h3base, reassoc_of% hB1]
  · show yOverlapTopA a b Y ≫ ka.top ≫ glueTotalInl a b Xa Xb φ
      = yOverlapTopB a b Y ≫ kb.top ≫ glueTotalInr a b Xa Xb φ
    rw [← reassoc_of% hA1t, glueTotal_condition, ← hpsit, Category.assoc,
      reassoc_of% h3top, reassoc_of% hB1t]

/-- **[(†) ⟹ (⋆)]** If the glued chart morphisms agree on the overlap chart, the
comparison morphisms match through `overlapIso`. -/
private theorem overlap_compare_of_agree
    (repr_a : (P.baseChange (awayHom a)).RepresentableBy Xa)
    (repr_b : (P.baseChange (awayHom b)).RepresentableBy Xb) (Y : EllObj R)
    (ka : Y.baseChangeRing (awayHom a) ⟶ Xa) (kb : Y.baseChangeRing (awayHom b) ⟶ Xb)
    (hagr : yOverlapInclA a b Y ≫ (EllObj.restrictScalars (awayHom a)).map ka
        ≫ glueJa a b Xa Xb (overlapIso a b repr_a repr_b)
      = yOverlapInclB a b Y ≫ (EllObj.restrictScalars (awayHom b)).map kb
        ≫ glueJb a b Xa Xb (overlapIso a b repr_a repr_b)) :
    overlapCompareA a b Y ka ≫ (overlapIso a b repr_a repr_b).hom
      = overlapCompareB a b Y kb := by
  set φ := overlapIso a b repr_a repr_b with hφ
  have hagrb : yOverlapBaseA a b Y ≫ ka.baseHom ≫ glueBaseInl a b Xa Xb φ
      = yOverlapBaseB a b Y ≫ kb.baseHom ≫ glueBaseInr a b Xa Xb φ := by
    have hc := congrArg EllHom.baseHom hagr
    simp only [EllHom.comp_baseHom] at hc
    exact hc
  have hagrt : yOverlapTopA a b Y ≫ ka.top ≫ glueTotalInl a b Xa Xb φ
      = yOverlapTopB a b Y ≫ kb.top ≫ glueTotalInr a b Xa Xb φ := by
    have hc := congrArg EllHom.top hagr
    simp only [EllHom.comp_top] at hc
    exact hc
  have hA1 : (overlapCompareA a b Y ka).baseHom ≫ glueBaseFst a b Xa
      = yOverlapBaseA a b Y ≫ ka.baseHom := by
    rw [overlapCompareA_baseHom]
    exact bcInvBase_fst _ _ _ _
  have hB1 : (overlapCompareB a b Y kb).baseHom
        ≫ pullback.fst Xb.structMap (Spec.map (awayProdHomRight a b))
      = yOverlapBaseB a b Y ≫ kb.baseHom := by
    rw [overlapCompareB_baseHom]
    exact bcInvBase_fst _ _ _ _
  have hA1t : (overlapCompareA a b Y ka).top ≫ glueCurveFst a b Xa
      = yOverlapTopA a b Y ≫ ka.top := by
    rw [overlapCompareA_top]
    exact bcInvTop_fst _ _ _ _
  have hB1t : (overlapCompareB a b Y kb).top
        ≫ pullback.fst Xb.curve.π (pullback.fst Xb.structMap (Spec.map (awayProdHomRight a b)))
      = yOverlapTopB a b Y ≫ kb.top := by
    rw [overlapCompareB_top]
    exact bcInvTop_fst _ _ _ _
  have hpsib : φ.hom.baseHom ≫ pullback.fst Xb.structMap (Spec.map (awayProdHomRight a b))
      = glueBasePsi a b Xa Xb φ := rfl
  have hpsit : φ.hom.top
        ≫ pullback.fst Xb.curve.π (pullback.fst Xb.structMap (Spec.map (awayProdHomRight a b)))
      = glueCurvePsi a b Xa Xb φ := rfl
  have hbase : (overlapCompareA a b Y ka).baseHom ≫ φ.hom.baseHom
      = (overlapCompareB a b Y kb).baseHom := by
    refine pullback.hom_ext ?_ ?_
    · rw [← cancel_mono (glueBaseInr a b Xa Xb φ)]
      simp only [Category.assoc]
      rw [reassoc_of% hpsib, ← glueBase_condition, reassoc_of% hA1, hagrb,
        ← reassoc_of% hB1]
    · have hw : φ.hom.baseHom ≫ pullback.snd Xb.structMap (Spec.map (awayProdHomRight a b))
          = pullback.snd Xa.structMap (Spec.map (awayProdHomLeft a b)) := φ.hom.base_w
      rw [Category.assoc, hw, overlapCompareA_baseHom, overlapCompareB_baseHom, bcInvBase_snd,
        bcInvBase_snd]
  refine EllHom.ext hbase ?_
  show (overlapCompareA a b Y ka).top ≫ φ.hom.top = (overlapCompareB a b Y kb).top
  refine pullback.hom_ext ?_ ?_
  · rw [← cancel_mono (glueTotalInr a b Xa Xb φ)]
    simp only [Category.assoc]
    rw [reassoc_of% hpsit, ← glueTotal_condition, reassoc_of% hA1t, hagrt,
      ← reassoc_of% hB1t]
  · have hw : φ.hom.top
        ≫ pullback.snd Xb.curve.π (pullback.fst Xb.structMap (Spec.map (awayProdHomRight a b)))
        = pullback.snd Xa.curve.π (pullback.fst Xa.structMap (Spec.map (awayProdHomLeft a b)))
          ≫ φ.hom.baseHom := φ.hom.isPullback.w
    rw [Category.assoc, hw]
    rw [reassoc_of% (show (overlapCompareA a b Y ka).top
          ≫ pullback.snd Xa.curve.π (pullback.fst Xa.structMap (Spec.map (awayProdHomLeft a b)))
        = (Y.baseChangeRing (awayHom (a * b))).curve.π ≫ (overlapCompareA a b Y ka).baseHom
        from by rw [overlapCompareA_top, overlapCompareA_baseHom]; exact bcInvTop_snd _ _ _ _)]
    rw [show (overlapCompareB a b Y kb).top
          ≫ pullback.snd Xb.curve.π (pullback.fst Xb.structMap (Spec.map (awayProdHomRight a b)))
        = (Y.baseChangeRing (awayHom (a * b))).curve.π ≫ (overlapCompareB a b Y kb).baseHom
        from by rw [overlapCompareB_top, overlapCompareB_baseHom]; exact bcInvTop_snd _ _ _ _]
    rw [hbase]

end OverlapBridge

/-! ## [R-hom-glue] source-cover gluing of an `Ell/R`-morphism into the glued object

A pair of chart morphisms `Y|D(a) ⟶ glueEllObj`, `Y|D(b) ⟶ glueEllObj` agreeing on the
overlap chart glues to a morphism `Y ⟶ glueEllObj`: the underlying scheme morphisms glue
along the two-chart open covers of `Y.base` and `Y.curve.E` (`Scheme.Cover.glueMorphisms`),
and the cartesian field is checked chart-by-chart via `Scheme.isPullback_of_openCover`. -/

section SourceCover

set_option backward.isDefEq.respectTransparency false

variable (a b : R)

/-- The structure map of the `a`-chart of `Y` lands in `D(a)`. -/
private theorem chartA_structMap_range (Y : EllObj R) :
    Set.range ((EllObj.restrictScalars (awayHom a)).obj
        (Y.baseChangeRing (awayHom a))).structMap
      ⊆ Set.range (Spec.map (awayHom a)) := by
  rintro - ⟨x, rfl⟩
  show ((Y.baseChangeRing (awayHom a)).structMap ≫ Spec.map (awayHom a)) x ∈ _
  rw [Scheme.Hom.comp_apply]
  exact ⟨_, rfl⟩

private theorem chartB_structMap_range (Y : EllObj R) :
    Set.range ((EllObj.restrictScalars (awayHom b)).obj
        (Y.baseChangeRing (awayHom b))).structMap
      ⊆ Set.range (Spec.map (awayHom b)) := by
  rintro - ⟨x, rfl⟩
  show ((Y.baseChangeRing (awayHom b)).structMap ≫ Spec.map (awayHom b)) x ∈ _
  rw [Scheme.Hom.comp_apply]
  exact ⟨_, rfl⟩

/-- The two-chart open cover of the base of a test object (`true ↦ D(a)`-chart,
`false ↦ D(b)`-chart). -/
private noncomputable def yBaseCover (Y : EllObj R) (hab : ∃ x y : R, x * a + y * b = 1) :
    Y.base.OpenCover :=
  Scheme.Cover.mkOfCovers Bool
    (fun i => i.casesOn (pullback Y.structMap (Spec.map (awayHom b)))
      (pullback Y.structMap (Spec.map (awayHom a))))
    (fun i => i.casesOn (pullback.fst Y.structMap (Spec.map (awayHom b)))
      (pullback.fst Y.structMap (Spec.map (awayHom a))))
    (fun x => by
      have hx : Y.structMap x ∈ (⊤ : TopologicalSpace.Opens (PrimeSpectrum R)) := trivial
      rw [← basicOpen_sup_basicOpen_eq_top a b hab] at hx
      rcases hx with hxa | hxb
      · have hr : Y.structMap x ∈ Set.range (Spec.map (awayHom a)) := by
          rw [range_SpecMap_awayHom]; exact hxa
        obtain ⟨s, hs⟩ := hr
        obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback
          (f := Y.structMap) (g := Spec.map (awayHom a)) x s hs.symm
        exact ⟨true, z, hz1⟩
      · have hr : Y.structMap x ∈ Set.range (Spec.map (awayHom b)) := by
          rw [range_SpecMap_awayHom]; exact hxb
        obtain ⟨s, hs⟩ := hr
        obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback
          (f := Y.structMap) (g := Spec.map (awayHom b)) x s hs.symm
        exact ⟨false, z, hz1⟩)
    (fun i => by cases i <;> infer_instance)

/-- The two-chart open cover of the total space of a test object. -/
private noncomputable def yTotalCover (Y : EllObj R) (hab : ∃ x y : R, x * a + y * b = 1) :
    Y.curve.E.OpenCover :=
  Scheme.Cover.mkOfCovers Bool
    (fun i => i.casesOn
      (pullback Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom b))))
      (pullback Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom a)))))
    (fun i => i.casesOn
      (pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom b))))
      (pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom a)))))
    (fun e => by
      have hx : Y.structMap (Y.curve.π e) ∈ (⊤ : TopologicalSpace.Opens (PrimeSpectrum R)) :=
        trivial
      rw [← basicOpen_sup_basicOpen_eq_top a b hab] at hx
      rcases hx with hxa | hxb
      · have hr : Y.structMap (Y.curve.π e) ∈ Set.range (Spec.map (awayHom a)) := by
          rw [range_SpecMap_awayHom]; exact hxa
        obtain ⟨s, hs⟩ := hr
        obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback
          (f := Y.structMap) (g := Spec.map (awayHom a)) (Y.curve.π e) s hs.symm
        obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback
          (f := Y.curve.π) (g := pullback.fst Y.structMap (Spec.map (awayHom a)))
          e z hz1.symm
        exact ⟨true, w, hw1⟩
      · have hr : Y.structMap (Y.curve.π e) ∈ Set.range (Spec.map (awayHom b)) := by
          rw [range_SpecMap_awayHom]; exact hxb
        obtain ⟨s, hs⟩ := hr
        obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback
          (f := Y.structMap) (g := Spec.map (awayHom b)) (Y.curve.π e) s hs.symm
        obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback
          (f := Y.curve.π) (g := pullback.fst Y.structMap (Spec.map (awayHom b)))
          e z hz1.symm
        exact ⟨false, w, hw1⟩)
    (fun i => by cases i <;> infer_instance)

variable (Xa : EllObj (CommRingCat.of (Localization.Away a)))
variable (Xb : EllObj (CommRingCat.of (Localization.Away b)))
variable (φ : Xa.baseChangeRing (awayProdHomLeft a b) ≅ Xb.baseChangeRing (awayProdHomRight a b))
variable (Y : EllObj R) (hab : ∃ x y : R, x * a + y * b = 1)
variable (fa : (EllObj.restrictScalars (awayHom a)).obj (Y.baseChangeRing (awayHom a))
  ⟶ glueEllObj a b Xa Xb φ)
variable (fb : (EllObj.restrictScalars (awayHom b)).obj (Y.baseChangeRing (awayHom b))
  ⟶ glueEllObj a b Xa Xb φ)

/-- The chart pair of base morphisms, indexed over the base cover. -/
private noncomputable def glueHomBaseFun :
    ∀ i : Bool, (yBaseCover a b Y hab).X i ⟶ glueBase a b Xa Xb φ :=
  fun i => i.casesOn fb.baseHom fa.baseHom

/-- Base compatibility of the chart pair over the four cover overlaps. -/
private theorem glueHomBase_compat
    (hagr : yOverlapInclA a b Y ≫ fa = yOverlapInclB a b Y ≫ fb) :
    ∀ i j : Bool,
      pullback.fst ((yBaseCover a b Y hab).f i) ((yBaseCover a b Y hab).f j)
          ≫ glueHomBaseFun a b Xa Xb φ Y hab fa fb i
        = pullback.snd ((yBaseCover a b Y hab).f i) ((yBaseCover a b Y hab).f j)
          ≫ glueHomBaseFun a b Xa Xb φ Y hab fa fb j := by
  have hagrb : yOverlapBaseA a b Y ≫ fa.baseHom = yOverlapBaseB a b Y ≫ fb.baseHom := by
    have hc := congrArg EllHom.baseHom hagr
    simp only [EllHom.comp_baseHom] at hc
    exact hc
  intro i j
  cases i <;> cases j
  · -- (b, b): diagonal, cancel the mono
    show pullback.fst (pullback.fst Y.structMap (Spec.map (awayHom b)))
        (pullback.fst Y.structMap (Spec.map (awayHom b))) ≫ fb.baseHom
      = pullback.snd _ _ ≫ fb.baseHom
    rw [show pullback.fst (pullback.fst Y.structMap (Spec.map (awayHom b)))
          (pullback.fst Y.structMap (Spec.map (awayHom b)))
        = pullback.snd (pullback.fst Y.structMap (Spec.map (awayHom b)))
          (pullback.fst Y.structMap (Spec.map (awayHom b))) from
      (cancel_mono (pullback.fst Y.structMap (Spec.map (awayHom b)))).mp pullback.condition]
  · -- (b, a): cross, through the overlap chart
    show pullback.fst (pullback.fst Y.structMap (Spec.map (awayHom b)))
        (pullback.fst Y.structMap (Spec.map (awayHom a))) ≫ fb.baseHom
      = pullback.snd _ _ ≫ fa.baseHom
    have H : Set.range ((pullback.fst (pullback.fst Y.structMap (Spec.map (awayHom b)))
          (pullback.fst Y.structMap (Spec.map (awayHom a)))
          ≫ pullback.fst Y.structMap (Spec.map (awayHom b))) ≫ Y.structMap)
        ⊆ Set.range (Spec.map (awayHom (a * b))) := by
      refine range_toOverlap_cond a b Y _ ?_ ?_
      · intro t
        have hc := congr($(pullback.condition (f := pullback.fst Y.structMap
          (Spec.map (awayHom b))) (g := pullback.fst Y.structMap (Spec.map (awayHom a)))) t)
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hc
        rw [Scheme.Hom.comp_apply, hc]
        have hp := congr($(pullback.condition (f := Y.structMap)
          (g := Spec.map (awayHom a))) (pullback.snd (pullback.fst Y.structMap
            (Spec.map (awayHom b))) (pullback.fst Y.structMap (Spec.map (awayHom a))) t))
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hp
        rw [hp]
        exact ⟨_, rfl⟩
      · intro t
        rw [Scheme.Hom.comp_apply]
        have hp := congr($(pullback.condition (f := Y.structMap)
          (g := Spec.map (awayHom b))) (pullback.fst (pullback.fst Y.structMap
            (Spec.map (awayHom b))) (pullback.fst Y.structMap (Spec.map (awayHom a))) t))
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hp
        rw [hp]
        exact ⟨_, rfl⟩
    set dq := toOverlapBase a b Y _ H with hdq
    have h1 : dq ≫ yOverlapBaseB a b Y
        = pullback.fst (pullback.fst Y.structMap (Spec.map (awayHom b)))
            (pullback.fst Y.structMap (Spec.map (awayHom a))) :=
      toOverlapBase_yOverlapBaseB a b Y _ H _ rfl
    have h2 : dq ≫ yOverlapBaseA a b Y
        = pullback.snd (pullback.fst Y.structMap (Spec.map (awayHom b)))
            (pullback.fst Y.structMap (Spec.map (awayHom a))) :=
      toOverlapBase_yOverlapBaseA a b Y _ H _ pullback.condition.symm
    rw [← h1, ← h2, Category.assoc, Category.assoc, hagrb]
  · -- (a, b): cross
    show pullback.fst (pullback.fst Y.structMap (Spec.map (awayHom a)))
        (pullback.fst Y.structMap (Spec.map (awayHom b))) ≫ fa.baseHom
      = pullback.snd _ _ ≫ fb.baseHom
    have H : Set.range ((pullback.fst (pullback.fst Y.structMap (Spec.map (awayHom a)))
          (pullback.fst Y.structMap (Spec.map (awayHom b)))
          ≫ pullback.fst Y.structMap (Spec.map (awayHom a))) ≫ Y.structMap)
        ⊆ Set.range (Spec.map (awayHom (a * b))) := by
      refine range_toOverlap_cond a b Y _ ?_ ?_
      · intro t
        rw [Scheme.Hom.comp_apply]
        have hp := congr($(pullback.condition (f := Y.structMap)
          (g := Spec.map (awayHom a))) (pullback.fst (pullback.fst Y.structMap
            (Spec.map (awayHom a))) (pullback.fst Y.structMap (Spec.map (awayHom b))) t))
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hp
        rw [hp]
        exact ⟨_, rfl⟩
      · intro t
        have hc := congr($(pullback.condition (f := pullback.fst Y.structMap
          (Spec.map (awayHom a))) (g := pullback.fst Y.structMap (Spec.map (awayHom b)))) t)
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hc
        rw [Scheme.Hom.comp_apply, hc]
        have hp := congr($(pullback.condition (f := Y.structMap)
          (g := Spec.map (awayHom b))) (pullback.snd (pullback.fst Y.structMap
            (Spec.map (awayHom a))) (pullback.fst Y.structMap (Spec.map (awayHom b))) t))
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hp
        rw [hp]
        exact ⟨_, rfl⟩
    set dq := toOverlapBase a b Y _ H with hdq
    have h1 : dq ≫ yOverlapBaseA a b Y
        = pullback.fst (pullback.fst Y.structMap (Spec.map (awayHom a)))
            (pullback.fst Y.structMap (Spec.map (awayHom b))) :=
      toOverlapBase_yOverlapBaseA a b Y _ H _ rfl
    have h2 : dq ≫ yOverlapBaseB a b Y
        = pullback.snd (pullback.fst Y.structMap (Spec.map (awayHom a)))
            (pullback.fst Y.structMap (Spec.map (awayHom b))) :=
      toOverlapBase_yOverlapBaseB a b Y _ H _ pullback.condition.symm
    rw [← h1, ← h2, Category.assoc, Category.assoc, hagrb]
  · -- (a, a): diagonal
    show pullback.fst (pullback.fst Y.structMap (Spec.map (awayHom a)))
        (pullback.fst Y.structMap (Spec.map (awayHom a))) ≫ fa.baseHom
      = pullback.snd _ _ ≫ fa.baseHom
    rw [show pullback.fst (pullback.fst Y.structMap (Spec.map (awayHom a)))
          (pullback.fst Y.structMap (Spec.map (awayHom a)))
        = pullback.snd (pullback.fst Y.structMap (Spec.map (awayHom a)))
          (pullback.fst Y.structMap (Spec.map (awayHom a))) from
      (cancel_mono (pullback.fst Y.structMap (Spec.map (awayHom a)))).mp pullback.condition]

/-- The glued base morphism `Y.base ⟶ glueBase`. -/
private noncomputable def glueHomBase
    (hagr : yOverlapInclA a b Y ≫ fa = yOverlapInclB a b Y ≫ fb) :
    Y.base ⟶ glueBase a b Xa Xb φ :=
  (yBaseCover a b Y hab).glueMorphisms (glueHomBaseFun a b Xa Xb φ Y hab fa fb)
    (glueHomBase_compat a b Xa Xb φ Y hab fa fb hagr)

private theorem glueHomBase_res_a
    (hagr : yOverlapInclA a b Y ≫ fa = yOverlapInclB a b Y ≫ fb) :
    pullback.fst Y.structMap (Spec.map (awayHom a)) ≫ glueHomBase a b Xa Xb φ Y hab fa fb hagr
      = fa.baseHom :=
  (yBaseCover a b Y hab).ι_glueMorphisms _ _ true

private theorem glueHomBase_res_b
    (hagr : yOverlapInclA a b Y ≫ fa = yOverlapInclB a b Y ≫ fb) :
    pullback.fst Y.structMap (Spec.map (awayHom b)) ≫ glueHomBase a b Xa Xb φ Y hab fa fb hagr
      = fb.baseHom :=
  (yBaseCover a b Y hab).ι_glueMorphisms _ _ false

/-- Overlap range condition, `(a,b)`-order. -/
private theorem overlap_range_ab :
    Set.range ((pullback.fst (pullback.fst Y.structMap (Spec.map (awayHom a)))
        (pullback.fst Y.structMap (Spec.map (awayHom b)))
        ≫ pullback.fst Y.structMap (Spec.map (awayHom a))) ≫ Y.structMap)
      ⊆ Set.range (Spec.map (awayHom (a * b))) := by
  refine range_toOverlap_cond a b Y _ ?_ ?_
  · intro t
    rw [Scheme.Hom.comp_apply]
    have hp := congr($(pullback.condition (f := Y.structMap)
      (g := Spec.map (awayHom a))) (pullback.fst (pullback.fst Y.structMap
        (Spec.map (awayHom a))) (pullback.fst Y.structMap (Spec.map (awayHom b))) t))
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hp
    rw [hp]
    exact ⟨_, rfl⟩
  · intro t
    have hc := congr($(pullback.condition (f := pullback.fst Y.structMap
      (Spec.map (awayHom a))) (g := pullback.fst Y.structMap (Spec.map (awayHom b)))) t)
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hc
    rw [Scheme.Hom.comp_apply, hc]
    have hp := congr($(pullback.condition (f := Y.structMap)
      (g := Spec.map (awayHom b))) (pullback.snd (pullback.fst Y.structMap
        (Spec.map (awayHom a))) (pullback.fst Y.structMap (Spec.map (awayHom b))) t))
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hp
    rw [hp]
    exact ⟨_, rfl⟩

/-- Overlap range condition, `(b,a)`-order. -/
private theorem overlap_range_ba :
    Set.range ((pullback.fst (pullback.fst Y.structMap (Spec.map (awayHom b)))
        (pullback.fst Y.structMap (Spec.map (awayHom a)))
        ≫ pullback.fst Y.structMap (Spec.map (awayHom b))) ≫ Y.structMap)
      ⊆ Set.range (Spec.map (awayHom (a * b))) := by
  refine range_toOverlap_cond a b Y _ ?_ ?_
  · intro t
    have hc := congr($(pullback.condition (f := pullback.fst Y.structMap
      (Spec.map (awayHom b))) (g := pullback.fst Y.structMap (Spec.map (awayHom a)))) t)
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hc
    rw [Scheme.Hom.comp_apply, hc]
    have hp := congr($(pullback.condition (f := Y.structMap)
      (g := Spec.map (awayHom a))) (pullback.snd (pullback.fst Y.structMap
        (Spec.map (awayHom b))) (pullback.fst Y.structMap (Spec.map (awayHom a))) t))
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hp
    rw [hp]
    exact ⟨_, rfl⟩
  · intro t
    rw [Scheme.Hom.comp_apply]
    have hp := congr($(pullback.condition (f := Y.structMap)
      (g := Spec.map (awayHom b))) (pullback.fst (pullback.fst Y.structMap
        (Spec.map (awayHom b))) (pullback.fst Y.structMap (Spec.map (awayHom a))) t))
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hp
    rw [hp]
    exact ⟨_, rfl⟩

/-- The chart pair of total-space morphisms, indexed over the total cover. -/
private noncomputable def glueHomTopFun :
    ∀ i : Bool, (yTotalCover a b Y hab).X i ⟶ glueTotal a b Xa Xb φ :=
  fun i => i.casesOn fb.top fa.top

/-- Total-space compatibility of the chart pair over the four cover overlaps. -/
private theorem glueHomTop_compat
    (hagr : yOverlapInclA a b Y ≫ fa = yOverlapInclB a b Y ≫ fb) :
    ∀ i j : Bool,
      pullback.fst ((yTotalCover a b Y hab).f i) ((yTotalCover a b Y hab).f j)
          ≫ glueHomTopFun a b Xa Xb φ Y hab fa fb i
        = pullback.snd ((yTotalCover a b Y hab).f i) ((yTotalCover a b Y hab).f j)
          ≫ glueHomTopFun a b Xa Xb φ Y hab fa fb j := by
  have hagrt : yOverlapTopA a b Y ≫ fa.top = yOverlapTopB a b Y ≫ fb.top := by
    have hc := congrArg EllHom.top hagr
    simp only [EllHom.comp_top] at hc
    exact hc
  intro i j
  cases i <;> cases j
  · -- (b, b)
    show pullback.fst (pullback.fst Y.curve.π (pullback.fst Y.structMap
        (Spec.map (awayHom b)))) (pullback.fst Y.curve.π (pullback.fst Y.structMap
        (Spec.map (awayHom b)))) ≫ fb.top = pullback.snd _ _ ≫ fb.top
    rw [show pullback.fst (pullback.fst Y.curve.π (pullback.fst Y.structMap
          (Spec.map (awayHom b)))) (pullback.fst Y.curve.π (pullback.fst Y.structMap
          (Spec.map (awayHom b))))
        = pullback.snd (pullback.fst Y.curve.π (pullback.fst Y.structMap
          (Spec.map (awayHom b)))) (pullback.fst Y.curve.π (pullback.fst Y.structMap
          (Spec.map (awayHom b)))) from
      (cancel_mono (pullback.fst Y.curve.π (pullback.fst Y.structMap
        (Spec.map (awayHom b))))).mp pullback.condition]
  · -- (b, a)
    show pullback.fst (pullback.fst Y.curve.π (pullback.fst Y.structMap
          (Spec.map (awayHom b)))) (pullback.fst Y.curve.π (pullback.fst Y.structMap
          (Spec.map (awayHom a)))) ≫ fb.top
      = pullback.snd _ _ ≫ fa.top
    set gaP := pullback.fst Y.structMap (Spec.map (awayHom a)) with hgaP
    set gbP := pullback.fst Y.structMap (Spec.map (awayHom b)) with hgbP
    set tA := pullback.fst Y.curve.π gaP with htA
    set tB := pullback.fst Y.curve.π gbP with htB
    have hπc1 : tB ≫ Y.curve.π = pullback.snd Y.curve.π gbP ≫ gbP := pullback.condition
    have hπc2 : tA ≫ Y.curve.π = pullback.snd Y.curve.π gaP ≫ gaP := pullback.condition
    set πpb := pullback.map tB tA gbP gaP (pullback.snd Y.curve.π gbP)
      (pullback.snd Y.curve.π gaP) Y.curve.π hπc1 hπc2 with hπpb
    set dq := toOverlapBase a b Y _ (overlap_range_ba a b Y) with hdq
    have hdq1 : dq ≫ yOverlapBaseB a b Y = pullback.fst gbP gaP :=
      toOverlapBase_yOverlapBaseB a b Y _ _ _ rfl
    have hdq2 : dq ≫ yOverlapBaseA a b Y = pullback.snd gbP gaP :=
      toOverlapBase_yOverlapBaseA a b Y _ _ _ pullback.condition.symm
    have h2 : dq ≫ pullback.fst Y.structMap (Spec.map (awayHom (a * b)))
        = pullback.fst gbP gaP ≫ gbP := toOverlapBase_fst a b Y _ _
    have h3 : πpb ≫ pullback.fst gbP gaP = pullback.fst tB tA ≫ pullback.snd Y.curve.π gbP :=
      pullback.lift_fst _ _ _
    have hcommE : (pullback.fst tB tA ≫ tB) ≫ Y.curve.π
        = (πpb ≫ dq) ≫ pullback.fst Y.structMap (Spec.map (awayHom (a * b))) := by
      rw [Category.assoc, hπc1, Category.assoc, h2, reassoc_of% h3]
    set dE := pullback.lift (pullback.fst tB tA ≫ tB) (πpb ≫ dq) hcommE with hdE
    have hdE1 : dE ≫ yOverlapTopB a b Y = pullback.fst tB tA := by
      rw [← cancel_mono tB, Category.assoc]
      rw [show yOverlapTopB a b Y ≫ tB
          = pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom (a * b))))
          from yOverlapTopB_fst a b Y]
      exact pullback.lift_fst _ _ _
    have hdE2 : dE ≫ yOverlapTopA a b Y = pullback.snd tB tA := by
      rw [← cancel_mono tA, Category.assoc]
      rw [show yOverlapTopA a b Y ≫ tA
          = pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom (a * b))))
          from yOverlapTopA_fst a b Y]
      rw [show dE ≫ pullback.fst Y.curve.π (pullback.fst Y.structMap
          (Spec.map (awayHom (a * b)))) = pullback.fst tB tA ≫ tB from pullback.lift_fst _ _ _]
      exact pullback.condition
    rw [← hdE1, ← hdE2, Category.assoc, Category.assoc, ← hagrt]
  · -- (a, b)
    show pullback.fst (pullback.fst Y.curve.π (pullback.fst Y.structMap
          (Spec.map (awayHom a)))) (pullback.fst Y.curve.π (pullback.fst Y.structMap
          (Spec.map (awayHom b)))) ≫ fa.top
      = pullback.snd _ _ ≫ fb.top
    set gaP := pullback.fst Y.structMap (Spec.map (awayHom a)) with hgaP
    set gbP := pullback.fst Y.structMap (Spec.map (awayHom b)) with hgbP
    set tA := pullback.fst Y.curve.π gaP with htA
    set tB := pullback.fst Y.curve.π gbP with htB
    have hπc1 : tA ≫ Y.curve.π = pullback.snd Y.curve.π gaP ≫ gaP := pullback.condition
    have hπc2 : tB ≫ Y.curve.π = pullback.snd Y.curve.π gbP ≫ gbP := pullback.condition
    set πpb := pullback.map tA tB gaP gbP (pullback.snd Y.curve.π gaP)
      (pullback.snd Y.curve.π gbP) Y.curve.π hπc1 hπc2 with hπpb
    set dq := toOverlapBase a b Y _ (overlap_range_ab a b Y) with hdq
    have hdq1 : dq ≫ yOverlapBaseA a b Y = pullback.fst gaP gbP :=
      toOverlapBase_yOverlapBaseA a b Y _ _ _ rfl
    have hdq2 : dq ≫ yOverlapBaseB a b Y = pullback.snd gaP gbP :=
      toOverlapBase_yOverlapBaseB a b Y _ _ _ pullback.condition.symm
    have h2 : dq ≫ pullback.fst Y.structMap (Spec.map (awayHom (a * b)))
        = pullback.fst gaP gbP ≫ gaP := toOverlapBase_fst a b Y _ _
    have h3 : πpb ≫ pullback.fst gaP gbP = pullback.fst tA tB ≫ pullback.snd Y.curve.π gaP :=
      pullback.lift_fst _ _ _
    have hcommE : (pullback.fst tA tB ≫ tA) ≫ Y.curve.π
        = (πpb ≫ dq) ≫ pullback.fst Y.structMap (Spec.map (awayHom (a * b))) := by
      rw [Category.assoc, hπc1, Category.assoc, h2, reassoc_of% h3]
    set dE := pullback.lift (pullback.fst tA tB ≫ tA) (πpb ≫ dq) hcommE with hdE
    have hdE1 : dE ≫ yOverlapTopA a b Y = pullback.fst tA tB := by
      rw [← cancel_mono tA, Category.assoc]
      rw [show yOverlapTopA a b Y ≫ tA
          = pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom (a * b))))
          from yOverlapTopA_fst a b Y]
      exact pullback.lift_fst _ _ _
    have hdE2 : dE ≫ yOverlapTopB a b Y = pullback.snd tA tB := by
      rw [← cancel_mono tB, Category.assoc]
      rw [show yOverlapTopB a b Y ≫ tB
          = pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom (a * b))))
          from yOverlapTopB_fst a b Y]
      rw [show dE ≫ pullback.fst Y.curve.π (pullback.fst Y.structMap
          (Spec.map (awayHom (a * b)))) = pullback.fst tA tB ≫ tA from pullback.lift_fst _ _ _]
      exact pullback.condition
    rw [← hdE1, ← hdE2, Category.assoc, Category.assoc, hagrt]
  · -- (a, a)
    show pullback.fst (pullback.fst Y.curve.π (pullback.fst Y.structMap
        (Spec.map (awayHom a)))) (pullback.fst Y.curve.π (pullback.fst Y.structMap
        (Spec.map (awayHom a)))) ≫ fa.top = pullback.snd _ _ ≫ fa.top
    rw [show pullback.fst (pullback.fst Y.curve.π (pullback.fst Y.structMap
          (Spec.map (awayHom a)))) (pullback.fst Y.curve.π (pullback.fst Y.structMap
          (Spec.map (awayHom a))))
        = pullback.snd (pullback.fst Y.curve.π (pullback.fst Y.structMap
          (Spec.map (awayHom a)))) (pullback.fst Y.curve.π (pullback.fst Y.structMap
          (Spec.map (awayHom a)))) from
      (cancel_mono (pullback.fst Y.curve.π (pullback.fst Y.structMap
        (Spec.map (awayHom a))))).mp pullback.condition]

/-- The glued total-space morphism `Y.curve.E ⟶ glueTotal`. -/
private noncomputable def glueHomTop
    (hagr : yOverlapInclA a b Y ≫ fa = yOverlapInclB a b Y ≫ fb) :
    Y.curve.E ⟶ glueTotal a b Xa Xb φ :=
  (yTotalCover a b Y hab).glueMorphisms (glueHomTopFun a b Xa Xb φ Y hab fa fb)
    (glueHomTop_compat a b Xa Xb φ Y hab fa fb hagr)

private theorem glueHomTop_res_a
    (hagr : yOverlapInclA a b Y ≫ fa = yOverlapInclB a b Y ≫ fb) :
    pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom a)))
        ≫ glueHomTop a b Xa Xb φ Y hab fa fb hagr
      = fa.top :=
  (yTotalCover a b Y hab).ι_glueMorphisms _ _ true

private theorem glueHomTop_res_b
    (hagr : yOverlapInclA a b Y ≫ fa = yOverlapInclB a b Y ≫ fb) :
    pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom b)))
        ≫ glueHomTop a b Xa Xb φ Y hab fa fb hagr
      = fb.top :=
  (yTotalCover a b Y hab).ι_glueMorphisms _ _ false

/-- Structure-map compatibility of the glued base morphism. -/
private theorem glueHomBase_w
    (hagr : yOverlapInclA a b Y ≫ fa = yOverlapInclB a b Y ≫ fb) :
    glueHomBase a b Xa Xb φ Y hab fa fb hagr ≫ glueQ a b Xa Xb φ = Y.structMap := by
  refine (yBaseCover a b Y hab).hom_ext _ _ fun i => ?_
  cases i
  · show pullback.fst Y.structMap (Spec.map (awayHom b))
        ≫ glueHomBase a b Xa Xb φ Y hab fa fb hagr ≫ glueQ a b Xa Xb φ
      = pullback.fst Y.structMap (Spec.map (awayHom b)) ≫ Y.structMap
    rw [← Category.assoc, glueHomBase_res_b]
    have hb1 : fb.baseHom ≫ glueQ a b Xa Xb φ
        = ((EllObj.restrictScalars (awayHom b)).obj
            (Y.baseChangeRing (awayHom b))).structMap := fb.base_w
    rw [hb1]
    exact (pullback.condition (f := Y.structMap) (g := Spec.map (awayHom b))).symm
  · show pullback.fst Y.structMap (Spec.map (awayHom a))
        ≫ glueHomBase a b Xa Xb φ Y hab fa fb hagr ≫ glueQ a b Xa Xb φ
      = pullback.fst Y.structMap (Spec.map (awayHom a)) ≫ Y.structMap
    rw [← Category.assoc, glueHomBase_res_a]
    have hb1 : fa.baseHom ≫ glueQ a b Xa Xb φ
        = ((EllObj.restrictScalars (awayHom a)).obj
            (Y.baseChangeRing (awayHom a))).structMap := fa.base_w
    rw [hb1]
    exact (pullback.condition (f := Y.structMap) (g := Spec.map (awayHom a))).symm

/-- Projection compatibility of the glued morphisms. -/
private theorem glueHomTop_w
    (hagr : yOverlapInclA a b Y ≫ fa = yOverlapInclB a b Y ≫ fb) :
    glueHomTop a b Xa Xb φ Y hab fa fb hagr ≫ gluePi a b Xa Xb φ
      = Y.curve.π ≫ glueHomBase a b Xa Xb φ Y hab fa fb hagr := by
  refine (yTotalCover a b Y hab).hom_ext _ _ fun i => ?_
  cases i
  · show pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom b)))
        ≫ glueHomTop a b Xa Xb φ Y hab fa fb hagr ≫ gluePi a b Xa Xb φ
      = pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom b)))
        ≫ Y.curve.π ≫ glueHomBase a b Xa Xb φ Y hab fa fb hagr
    rw [← Category.assoc, glueHomTop_res_b]
    have h1 : fb.top ≫ gluePi a b Xa Xb φ
        = pullback.snd Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom b)))
          ≫ fb.baseHom := fb.isPullback.w
    rw [h1, reassoc_of% (pullback.condition (f := Y.curve.π)
      (g := pullback.fst Y.structMap (Spec.map (awayHom b)))), glueHomBase_res_b]
  · show pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom a)))
        ≫ glueHomTop a b Xa Xb φ Y hab fa fb hagr ≫ gluePi a b Xa Xb φ
      = pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom a)))
        ≫ Y.curve.π ≫ glueHomBase a b Xa Xb φ Y hab fa fb hagr
    rw [← Category.assoc, glueHomTop_res_a]
    have h1 : fa.top ≫ gluePi a b Xa Xb φ
        = pullback.snd Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom a)))
          ≫ fa.baseHom := fa.isPullback.w
    rw [h1, reassoc_of% (pullback.condition (f := Y.curve.π)
      (g := pullback.fst Y.structMap (Spec.map (awayHom a)))), glueHomBase_res_a]

/-- Zero-section compatibility of the glued morphisms. -/
private theorem glueHom_zero_w
    (hagr : yOverlapInclA a b Y ≫ fa = yOverlapInclB a b Y ≫ fb) :
    Y.curve.zero ≫ glueHomTop a b Xa Xb φ Y hab fa fb hagr
      = glueHomBase a b Xa Xb φ Y hab fa fb hagr ≫ glueZero a b Xa Xb φ := by
  refine (yBaseCover a b Y hab).hom_ext _ _ fun i => ?_
  cases i
  · show pullback.fst Y.structMap (Spec.map (awayHom b))
        ≫ Y.curve.zero ≫ glueHomTop a b Xa Xb φ Y hab fa fb hagr
      = pullback.fst Y.structMap (Spec.map (awayHom b))
        ≫ glueHomBase a b Xa Xb φ Y hab fa fb hagr ≫ glueZero a b Xa Xb φ
    have hz : (Y.baseChangeRing (awayHom b)).curve.zero
          ≫ pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom b)))
        = pullback.fst Y.structMap (Spec.map (awayHom b)) ≫ Y.curve.zero :=
      baseChangeRing_curve_zero_comp_fst Y (awayHom b)
    have hzw : (Y.baseChangeRing (awayHom b)).curve.zero ≫ fb.top
        = fb.baseHom ≫ glueZero a b Xa Xb φ := fb.zero_w
    rw [← reassoc_of% hz, glueHomTop_res_b, hzw, reassoc_of% glueHomBase_res_b]
  · show pullback.fst Y.structMap (Spec.map (awayHom a))
        ≫ Y.curve.zero ≫ glueHomTop a b Xa Xb φ Y hab fa fb hagr
      = pullback.fst Y.structMap (Spec.map (awayHom a))
        ≫ glueHomBase a b Xa Xb φ Y hab fa fb hagr ≫ glueZero a b Xa Xb φ
    have hz : (Y.baseChangeRing (awayHom a)).curve.zero
          ≫ pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom a)))
        = pullback.fst Y.structMap (Spec.map (awayHom a)) ≫ Y.curve.zero :=
      baseChangeRing_curve_zero_comp_fst Y (awayHom a)
    have hzw : (Y.baseChangeRing (awayHom a)).curve.zero ≫ fa.top
        = fa.baseHom ≫ glueZero a b Xa Xb φ := fa.zero_w
    rw [← reassoc_of% hz, glueHomTop_res_a, hzw, reassoc_of% glueHomBase_res_a]

/-- The two-chart open cover of the glued total space. -/
private noncomputable def glueTotalCover : (glueTotal a b Xa Xb φ).OpenCover :=
  Scheme.Cover.mkOfCovers Bool
    (fun i => i.casesOn Xb.curve.E Xa.curve.E)
    (fun i => i.casesOn (glueTotalInr a b Xa Xb φ) (glueTotalInl a b Xa Xb φ))
    (fun x => by
      rcases glueTotal_exists a b Xa Xb φ x with ⟨u, hu⟩ | ⟨v, hv⟩
      · exact ⟨true, u, hu⟩
      · exact ⟨false, v, hv⟩)
    (fun i => by cases i <;> infer_instance)

/-- **The glued morphism square is cartesian.** Checked chart-by-chart over the two-chart
cover of the glued total space via `Scheme.isPullback_of_openCover`: over each chart the
square is, up to the canonical identifications, the pasting of the chart factorization's
cartesian square with the base-level chart square. -/
private theorem glueHom_isPullback
    (hagr : yOverlapInclA a b Y ≫ fa = yOverlapInclB a b Y ≫ fb) :
    IsPullback (glueHomTop a b Xa Xb φ Y hab fa fb hagr) Y.curve.π (gluePi a b Xa Xb φ)
      (glueHomBase a b Xa Xb φ Y hab fa fb hagr) := by
  have hw := glueHomTop_w a b Xa Xb φ Y hab fa fb hagr
  have hbw := glueHomBase_w a b Xa Xb φ Y hab fa fb hagr
  refine Scheme.isPullback_of_openCover _ _ _ _ (glueTotalCover a b Xa Xb φ) ?_
  intro i
  cases i
  · -- `b`-chart
    show IsPullback
      (pullback.snd (glueHomTop a b Xa Xb φ Y hab fa fb hagr) (glueTotalInr a b Xa Xb φ))
      (pullback.fst (glueHomTop a b Xa Xb φ Y hab fa fb hagr) (glueTotalInr a b Xa Xb φ)
        ≫ Y.curve.π)
      (glueTotalInr a b Xa Xb φ ≫ gluePi a b Xa Xb φ)
      (glueHomBase a b Xa Xb φ Y hab fa fb hagr)
    rw [glueTotalInr_gluePi a b Xa Xb φ]
    set uT := glueHomTop a b Xa Xb φ Y hab fa fb hagr with huT
    set uB := glueHomBase a b Xa Xb φ Y hab fa fb hagr with huB
    set gbP := pullback.fst Y.structMap (Spec.map (awayHom b)) with hgbP
    set tB := pullback.fst Y.curve.π gbP with htB
    set vb := factorGlueJb a b Xa Xb φ fb (chartB_structMap_range b Y) with hvb
    have hvb1 : vb.baseHom ≫ glueBaseInr a b Xa Xb φ = fb.baseHom :=
      IsOpenImmersion.lift_fac _ _ _
    have hvb2 : vb.top ≫ glueTotalInr a b Xa Xb φ = fb.top :=
      IsOpenImmersion.lift_fac _ _ _
    have hres : gbP ≫ uB = fb.baseHom := glueHomBase_res_b a b Xa Xb φ Y hab fa fb hagr
    have hrest : tB ≫ uT = fb.top := glueHomTop_res_b a b Xa Xb φ Y hab fa fb hagr
    have hrange : Set.range gbP = uB ⁻¹' Set.range (glueBaseInr a b Xa Xb φ) := by
      apply Set.Subset.antisymm
      · rintro - ⟨p, rfl⟩
        rw [Set.mem_preimage]
        have hc := congr($(hres) p)
        rw [Scheme.Hom.comp_apply] at hc
        rw [hc]
        exact factor_range_base_b a b Xa Xb φ fb (chartB_structMap_range b Y) ⟨p, rfl⟩
      · intro y hy
        rw [Set.mem_preimage] at hy
        obtain ⟨z, hz⟩ := hy
        have hmem : Y.structMap y ∈ Set.range (Spec.map (awayHom b)) := by
          have hc := congr($(hbw) y)
          rw [Scheme.Hom.comp_apply] at hc
          rw [← hc, ← hz]
          have hq := congr($(glueBaseInr_glueQ a b Xa Xb φ) z)
          rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hq
          rw [hq]
          exact ⟨_, rfl⟩
        obtain ⟨s, hs⟩ := hmem
        obtain ⟨z', hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback
          (f := Y.structMap) (g := Spec.map (awayHom b)) y s hs.symm
        exact ⟨z', hz1⟩
    have hBSQ : IsPullback vb.baseHom gbP (glueBaseInr a b Xa Xb φ) uB := by
      have hrange2 : Set.range gbP
          = Set.range (pullback.snd (glueBaseInr a b Xa Xb φ) uB) := by
        rw [Scheme.Pullback.range_snd, hrange]
      refine IsPullback.of_iso_pullback ⟨?_⟩
        (IsOpenImmersion.isoOfRangeEq gbP (pullback.snd (glueBaseInr a b Xa Xb φ) uB)
          hrange2) ?_ ?_
      · rw [hvb1, hres]
      · rw [← cancel_mono (glueBaseInr a b Xa Xb φ), Category.assoc, pullback.condition,
          ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, hres, hvb1]
      · exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    have hvb_sq : IsPullback vb.top (pullback.snd Y.curve.π gbP) Xb.curve.π vb.baseHom :=
      vb.isPullback
    have hpaste : IsPullback vb.top (pullback.snd Y.curve.π gbP ≫ gbP)
        (Xb.curve.π ≫ glueBaseInr a b Xa Xb φ) uB := hvb_sq.paste_vert hBSQ
    have hαcomm : tB ≫ uT = vb.top ≫ glueTotalInr a b Xa Xb φ := by
      rw [hvb2]; exact hrest
    set α := pullback.lift tB vb.top hαcomm with hα
    have hβcomm : pullback.snd uT (glueTotalInr a b Xa Xb φ)
          ≫ Xb.curve.π ≫ glueBaseInr a b Xa Xb φ
        = (pullback.fst uT (glueTotalInr a b Xa Xb φ) ≫ Y.curve.π) ≫ uB := by
      rw [← glueTotalInr_gluePi a b Xa Xb φ, ← Category.assoc,
        ← pullback.condition (f := uT) (g := glueTotalInr a b Xa Xb φ), Category.assoc, hw,
        ← Category.assoc]
    set β := hpaste.lift (pullback.snd uT (glueTotalInr a b Xa Xb φ))
      (pullback.fst uT (glueTotalInr a b Xa Xb φ) ≫ Y.curve.π) hβcomm with hβ
    have hβ1 : β ≫ vb.top = pullback.snd uT (glueTotalInr a b Xa Xb φ) :=
      hpaste.lift_fst _ _ _
    have hβ2 : β ≫ (pullback.snd Y.curve.π gbP ≫ gbP)
        = pullback.fst uT (glueTotalInr a b Xa Xb φ) ≫ Y.curve.π :=
      hpaste.lift_snd _ _ _
    have hαβ : α ≫ β = 𝟙 _ := by
      refine hpaste.hom_ext ?_ ?_
      · rw [Category.assoc, hβ1, Category.id_comp, pullback.lift_snd]
      · rw [Category.assoc, hβ2, Category.id_comp, ← Category.assoc, pullback.lift_fst]
        exact pullback.condition
    have hrangeE : Set.range (pullback.fst uT (glueTotalInr a b Xa Xb φ))
        ⊆ Set.range tB := by
      intro e he
      obtain ⟨p, rfl⟩ := he
      have h1 : uT (pullback.fst uT (glueTotalInr a b Xa Xb φ) p)
          ∈ Set.range (glueTotalInr a b Xa Xb φ) := by
        have hc := congr($(pullback.condition (f := uT)
          (g := glueTotalInr a b Xa Xb φ)) p)
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hc
        rw [hc]
        exact ⟨_, rfl⟩
      rw [range_glueTotalInr, Set.mem_preimage] at h1
      have h2 : uB (Y.curve.π (pullback.fst uT (glueTotalInr a b Xa Xb φ) p))
          ∈ Set.range (glueBaseInr a b Xa Xb φ) := by
        have hc := congr($(hw) (pullback.fst uT (glueTotalInr a b Xa Xb φ) p))
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hc
        rw [← hc]
        exact h1
      have h3 : Y.curve.π (pullback.fst uT (glueTotalInr a b Xa Xb φ) p)
          ∈ Set.range gbP := by
        rw [hrange]
        exact Set.mem_preimage.mpr h2
      obtain ⟨q, hq⟩ := h3
      obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := Y.curve.π) (g := gbP)
        (pullback.fst uT (glueTotalInr a b Xa Xb φ) p) q hq.symm
      exact ⟨w, hw1⟩
    set liftq := IsOpenImmersion.lift tB (pullback.fst uT (glueTotalInr a b Xa Xb φ))
      hrangeE with hliftq
    have hliftq1 : liftq ≫ tB = pullback.fst uT (glueTotalInr a b Xa Xb φ) :=
      IsOpenImmersion.lift_fac _ _ _
    have hβliftq : β = liftq := by
      refine hpaste.hom_ext ?_ ?_
      · rw [hβ1, ← cancel_mono (glueTotalInr a b Xa Xb φ), Category.assoc, hvb2, ← hrest,
          ← Category.assoc, hliftq1]
        exact pullback.condition.symm
      · rw [hβ2, ← pullback.condition (f := Y.curve.π) (g := gbP), ← Category.assoc,
          hliftq1]
    have hβα : β ≫ α = 𝟙 _ := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, Category.id_comp]
        rw [show α ≫ pullback.fst uT (glueTotalInr a b Xa Xb φ) = tB from
          pullback.lift_fst _ _ _]
        rw [hβliftq, hliftq1]
      · rw [Category.assoc, Category.id_comp]
        rw [show α ≫ pullback.snd uT (glueTotalInr a b Xa Xb φ) = vb.top from
          pullback.lift_snd _ _ _]
        exact hβ1
    refine IsPullback.of_iso_pullback ⟨hβcomm⟩
      ({ hom := β ≫ hpaste.isoPullback.hom
         inv := hpaste.isoPullback.inv ≫ α
         hom_inv_id := by
           rw [Category.assoc, Iso.hom_inv_id_assoc, hβα]
         inv_hom_id := by
           rw [Category.assoc, reassoc_of% hαβ, Iso.inv_hom_id] }) ?_ ?_
    · rw [Category.assoc, IsPullback.isoPullback_hom_fst]
      exact hβ1
    · rw [Category.assoc, IsPullback.isoPullback_hom_snd]
      exact hβ2
  · -- `a`-chart
    show IsPullback
      (pullback.snd (glueHomTop a b Xa Xb φ Y hab fa fb hagr) (glueTotalInl a b Xa Xb φ))
      (pullback.fst (glueHomTop a b Xa Xb φ Y hab fa fb hagr) (glueTotalInl a b Xa Xb φ)
        ≫ Y.curve.π)
      (glueTotalInl a b Xa Xb φ ≫ gluePi a b Xa Xb φ)
      (glueHomBase a b Xa Xb φ Y hab fa fb hagr)
    rw [glueTotalInl_gluePi a b Xa Xb φ]
    set uT := glueHomTop a b Xa Xb φ Y hab fa fb hagr with huT
    set uB := glueHomBase a b Xa Xb φ Y hab fa fb hagr with huB
    set gaP := pullback.fst Y.structMap (Spec.map (awayHom a)) with hgaP
    set tA := pullback.fst Y.curve.π gaP with htA
    set va := factorGlueJa a b Xa Xb φ fa (chartA_structMap_range a Y) with hva
    have hva1 : va.baseHom ≫ glueBaseInl a b Xa Xb φ = fa.baseHom :=
      IsOpenImmersion.lift_fac _ _ _
    have hva2 : va.top ≫ glueTotalInl a b Xa Xb φ = fa.top :=
      IsOpenImmersion.lift_fac _ _ _
    have hres : gaP ≫ uB = fa.baseHom := glueHomBase_res_a a b Xa Xb φ Y hab fa fb hagr
    have hrest : tA ≫ uT = fa.top := glueHomTop_res_a a b Xa Xb φ Y hab fa fb hagr
    have hrange : Set.range gaP = uB ⁻¹' Set.range (glueBaseInl a b Xa Xb φ) := by
      apply Set.Subset.antisymm
      · rintro - ⟨p, rfl⟩
        rw [Set.mem_preimage]
        have hc := congr($(hres) p)
        rw [Scheme.Hom.comp_apply] at hc
        rw [hc]
        exact factor_range_base_a a b Xa Xb φ fa (chartA_structMap_range a Y) ⟨p, rfl⟩
      · intro y hy
        rw [Set.mem_preimage] at hy
        obtain ⟨z, hz⟩ := hy
        have hmem : Y.structMap y ∈ Set.range (Spec.map (awayHom a)) := by
          have hc := congr($(hbw) y)
          rw [Scheme.Hom.comp_apply] at hc
          rw [← hc, ← hz]
          have hq := congr($(glueBaseInl_glueQ a b Xa Xb φ) z)
          rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hq
          rw [hq]
          exact ⟨_, rfl⟩
        obtain ⟨s, hs⟩ := hmem
        obtain ⟨z', hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback
          (f := Y.structMap) (g := Spec.map (awayHom a)) y s hs.symm
        exact ⟨z', hz1⟩
    have hBSQ : IsPullback va.baseHom gaP (glueBaseInl a b Xa Xb φ) uB := by
      have hrange2 : Set.range gaP
          = Set.range (pullback.snd (glueBaseInl a b Xa Xb φ) uB) := by
        rw [Scheme.Pullback.range_snd, hrange]
      refine IsPullback.of_iso_pullback ⟨?_⟩
        (IsOpenImmersion.isoOfRangeEq gaP (pullback.snd (glueBaseInl a b Xa Xb φ) uB)
          hrange2) ?_ ?_
      · rw [hva1, hres]
      · rw [← cancel_mono (glueBaseInl a b Xa Xb φ), Category.assoc, pullback.condition,
          ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, hres, hva1]
      · exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    have hva_sq : IsPullback va.top (pullback.snd Y.curve.π gaP) Xa.curve.π va.baseHom :=
      va.isPullback
    have hpaste : IsPullback va.top (pullback.snd Y.curve.π gaP ≫ gaP)
        (Xa.curve.π ≫ glueBaseInl a b Xa Xb φ) uB := hva_sq.paste_vert hBSQ
    have hαcomm : tA ≫ uT = va.top ≫ glueTotalInl a b Xa Xb φ := by
      rw [hva2]; exact hrest
    set α := pullback.lift tA va.top hαcomm with hα
    have hβcomm : pullback.snd uT (glueTotalInl a b Xa Xb φ)
          ≫ Xa.curve.π ≫ glueBaseInl a b Xa Xb φ
        = (pullback.fst uT (glueTotalInl a b Xa Xb φ) ≫ Y.curve.π) ≫ uB := by
      rw [← glueTotalInl_gluePi a b Xa Xb φ, ← Category.assoc,
        ← pullback.condition (f := uT) (g := glueTotalInl a b Xa Xb φ), Category.assoc, hw,
        ← Category.assoc]
    set β := hpaste.lift (pullback.snd uT (glueTotalInl a b Xa Xb φ))
      (pullback.fst uT (glueTotalInl a b Xa Xb φ) ≫ Y.curve.π) hβcomm with hβ
    have hβ1 : β ≫ va.top = pullback.snd uT (glueTotalInl a b Xa Xb φ) :=
      hpaste.lift_fst _ _ _
    have hβ2 : β ≫ (pullback.snd Y.curve.π gaP ≫ gaP)
        = pullback.fst uT (glueTotalInl a b Xa Xb φ) ≫ Y.curve.π :=
      hpaste.lift_snd _ _ _
    have hαβ : α ≫ β = 𝟙 _ := by
      refine hpaste.hom_ext ?_ ?_
      · rw [Category.assoc, hβ1, Category.id_comp, pullback.lift_snd]
      · rw [Category.assoc, hβ2, Category.id_comp, ← Category.assoc, pullback.lift_fst]
        exact pullback.condition
    have hrangeE : Set.range (pullback.fst uT (glueTotalInl a b Xa Xb φ))
        ⊆ Set.range tA := by
      intro e he
      obtain ⟨p, rfl⟩ := he
      have h1 : uT (pullback.fst uT (glueTotalInl a b Xa Xb φ) p)
          ∈ Set.range (glueTotalInl a b Xa Xb φ) := by
        have hc := congr($(pullback.condition (f := uT)
          (g := glueTotalInl a b Xa Xb φ)) p)
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hc
        rw [hc]
        exact ⟨_, rfl⟩
      rw [range_glueTotalInl, Set.mem_preimage] at h1
      have h2 : uB (Y.curve.π (pullback.fst uT (glueTotalInl a b Xa Xb φ) p))
          ∈ Set.range (glueBaseInl a b Xa Xb φ) := by
        have hc := congr($(hw) (pullback.fst uT (glueTotalInl a b Xa Xb φ) p))
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hc
        rw [← hc]
        exact h1
      have h3 : Y.curve.π (pullback.fst uT (glueTotalInl a b Xa Xb φ) p)
          ∈ Set.range gaP := by
        rw [hrange]
        exact Set.mem_preimage.mpr h2
      obtain ⟨q, hq⟩ := h3
      obtain ⟨w', hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := Y.curve.π) (g := gaP)
        (pullback.fst uT (glueTotalInl a b Xa Xb φ) p) q hq.symm
      exact ⟨w', hw1⟩
    set liftq := IsOpenImmersion.lift tA (pullback.fst uT (glueTotalInl a b Xa Xb φ))
      hrangeE with hliftq
    have hliftq1 : liftq ≫ tA = pullback.fst uT (glueTotalInl a b Xa Xb φ) :=
      IsOpenImmersion.lift_fac _ _ _
    have hβliftq : β = liftq := by
      refine hpaste.hom_ext ?_ ?_
      · rw [hβ1, ← cancel_mono (glueTotalInl a b Xa Xb φ), Category.assoc, hva2, ← hrest,
          ← Category.assoc, hliftq1]
        exact pullback.condition.symm
      · rw [hβ2, ← pullback.condition (f := Y.curve.π) (g := gaP), ← Category.assoc,
          hliftq1]
    have hβα : β ≫ α = 𝟙 _ := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, Category.id_comp]
        rw [show α ≫ pullback.fst uT (glueTotalInl a b Xa Xb φ) = tA from
          pullback.lift_fst _ _ _]
        rw [hβliftq, hliftq1]
      · rw [Category.assoc, Category.id_comp]
        rw [show α ≫ pullback.snd uT (glueTotalInl a b Xa Xb φ) = va.top from
          pullback.lift_snd _ _ _]
        exact hβ1
    refine IsPullback.of_iso_pullback ⟨hβcomm⟩
      ({ hom := β ≫ hpaste.isoPullback.hom
         inv := hpaste.isoPullback.inv ≫ α
         hom_inv_id := by
           rw [Category.assoc, Iso.hom_inv_id_assoc, hβα]
         inv_hom_id := by
           rw [Category.assoc, reassoc_of% hαβ, Iso.inv_hom_id] }) ?_ ?_
    · rw [Category.assoc, IsPullback.isoPullback_hom_fst]
      exact hβ1
    · rw [Category.assoc, IsPullback.isoPullback_hom_snd]
      exact hβ2

/-- **[R-hom-glue] the glued `Ell/R`-morphism** from a compatible pair of chart
morphisms into the glued object. -/
private noncomputable def glueHomOfCharts
    (hagr : yOverlapInclA a b Y ≫ fa = yOverlapInclB a b Y ≫ fb) :
    Y ⟶ glueEllObj a b Xa Xb φ where
  baseHom := glueHomBase a b Xa Xb φ Y hab fa fb hagr
  base_w := glueHomBase_w a b Xa Xb φ Y hab fa fb hagr
  top := glueHomTop a b Xa Xb φ Y hab fa fb hagr
  isPullback := glueHom_isPullback a b Xa Xb φ Y hab fa fb hagr
  zero_w := glueHom_zero_w a b Xa Xb φ Y hab fa fb hagr

/-- The glued morphism restricts to `fa` on the `a`-chart. -/
private theorem yChartInclA_glueHomOfCharts
    (hagr : yOverlapInclA a b Y ≫ fa = yOverlapInclB a b Y ≫ fb) :
    yChartInclA a Y ≫ glueHomOfCharts a b Xa Xb φ Y hab fa fb hagr = fa := by
  refine EllHom.ext ?_ ?_
  · show (yChartInclA a Y).baseHom ≫ glueHomBase a b Xa Xb φ Y hab fa fb hagr = fa.baseHom
    rw [yChartInclA_baseHom]
    exact glueHomBase_res_a a b Xa Xb φ Y hab fa fb hagr
  · show (yChartInclA a Y).top ≫ glueHomTop a b Xa Xb φ Y hab fa fb hagr = fa.top
    rw [yChartInclA_top]
    exact glueHomTop_res_a a b Xa Xb φ Y hab fa fb hagr

/-- The glued morphism restricts to `fb` on the `b`-chart. -/
private theorem yChartInclB_glueHomOfCharts
    (hagr : yOverlapInclA a b Y ≫ fa = yOverlapInclB a b Y ≫ fb) :
    yChartInclB b Y ≫ glueHomOfCharts a b Xa Xb φ Y hab fa fb hagr = fb := by
  refine EllHom.ext ?_ ?_
  · show (yChartInclB b Y).baseHom ≫ glueHomBase a b Xa Xb φ Y hab fa fb hagr = fb.baseHom
    rw [yChartInclB_baseHom]
    exact glueHomBase_res_b a b Xa Xb φ Y hab fa fb hagr
  · show (yChartInclB b Y).top ≫ glueHomTop a b Xa Xb φ Y hab fa fb hagr = fb.top
    rw [yChartInclB_top]
    exact glueHomTop_res_b a b Xa Xb φ Y hab fa fb hagr

include hab in
/-- Two morphisms into the glued object agreeing on both charts of the source agree. -/
private theorem glueHom_source_ext {v w : Y ⟶ glueEllObj a b Xa Xb φ}
    (hA : yChartInclA a Y ≫ v = yChartInclA a Y ≫ w)
    (hB : yChartInclB b Y ≫ v = yChartInclB b Y ≫ w) : v = w := by
  have hAb : (yChartInclA a Y).baseHom ≫ v.baseHom
      = (yChartInclA a Y).baseHom ≫ w.baseHom := by
    have hc := congrArg EllHom.baseHom hA
    simpa only [EllHom.comp_baseHom] using hc
  have hBb : (yChartInclB b Y).baseHom ≫ v.baseHom
      = (yChartInclB b Y).baseHom ≫ w.baseHom := by
    have hc := congrArg EllHom.baseHom hB
    simpa only [EllHom.comp_baseHom] using hc
  have hAt : (yChartInclA a Y).top ≫ v.top = (yChartInclA a Y).top ≫ w.top := by
    have hc := congrArg EllHom.top hA
    simpa only [EllHom.comp_top] using hc
  have hBt : (yChartInclB b Y).top ≫ v.top = (yChartInclB b Y).top ≫ w.top := by
    have hc := congrArg EllHom.top hB
    simpa only [EllHom.comp_top] using hc
  refine EllHom.ext ?_ ?_
  · refine (yBaseCover a b Y hab).hom_ext _ _ fun i => ?_
    cases i
    · show pullback.fst Y.structMap (Spec.map (awayHom b)) ≫ v.baseHom
        = pullback.fst Y.structMap (Spec.map (awayHom b)) ≫ w.baseHom
      rw [← yChartInclB_baseHom]
      exact hBb
    · show pullback.fst Y.structMap (Spec.map (awayHom a)) ≫ v.baseHom
        = pullback.fst Y.structMap (Spec.map (awayHom a)) ≫ w.baseHom
      rw [← yChartInclA_baseHom]
      exact hAb
  · refine (yTotalCover a b Y hab).hom_ext _ _ fun i => ?_
    cases i
    · show pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom b))) ≫ v.top
        = pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom b))) ≫ w.top
      rw [← yChartInclB_top]
      exact hBt
    · show pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom a))) ≫ v.top
        = pullback.fst Y.curve.π (pullback.fst Y.structMap (Spec.map (awayHom a))) ≫ w.top
      rw [← yChartInclA_top]
      exact hAt

end SourceCover

/-! ## [R-chart-eqv] the per-chart hom-equivalences and chart naturality -/

section ChartHomEquiv

set_option backward.isDefEq.respectTransparency false

variable (a b : R)
variable (Xa : EllObj (CommRingCat.of (Localization.Away a)))
variable (Xb : EllObj (CommRingCat.of (Localization.Away b)))
variable (φ : Xa.baseChangeRing (awayProdHomLeft a b) ≅ Xb.baseChangeRing (awayProdHomRight a b))

/-- **[R-chart-eqv], geometric half (`a`-side):** morphisms `Y|D(a) ⟶ glueEllObj` in
`Ell/R` biject with morphisms `Y|D(a) ⟶ Xa` in `Ell/R[1/a]`, via the unique factorization
through the chart inclusion `glueJa`. -/
private noncomputable def glueChartHomEquivA (Y : EllObj R) :
    ((EllObj.restrictScalars (awayHom a)).obj (Y.baseChangeRing (awayHom a))
      ⟶ glueEllObj a b Xa Xb φ) ≃ (Y.baseChangeRing (awayHom a) ⟶ Xa) where
  toFun v := unRestrictScalars (awayHom a)
    (factorGlueJa a b Xa Xb φ v (chartA_structMap_range a Y))
  invFun k := (EllObj.restrictScalars (awayHom a)).map k ≫ glueJa a b Xa Xb φ
  left_inv v := by
    dsimp only
    have h1 : (EllObj.restrictScalars (awayHom a)).map
        (unRestrictScalars (awayHom a)
          (factorGlueJa a b Xa Xb φ v (chartA_structMap_range a Y)))
        = factorGlueJa a b Xa Xb φ v (chartA_structMap_range a Y) :=
      restrictScalars_map_unRestrictScalars _ _
    rw [h1]
    exact factorGlueJa_glueJa a b Xa Xb φ v (chartA_structMap_range a Y)
  right_inv k := by
    dsimp only
    apply (EllObj.restrictScalars (awayHom a)).map_injective
    rw [restrictScalars_map_unRestrictScalars]
    refine glueJa_cancel a b Xa Xb φ ?_
    rw [factorGlueJa_glueJa]

/-- The `b`-side. -/
private noncomputable def glueChartHomEquivB (Y : EllObj R) :
    ((EllObj.restrictScalars (awayHom b)).obj (Y.baseChangeRing (awayHom b))
      ⟶ glueEllObj a b Xa Xb φ) ≃ (Y.baseChangeRing (awayHom b) ⟶ Xb) where
  toFun v := unRestrictScalars (awayHom b)
    (factorGlueJb a b Xa Xb φ v (chartB_structMap_range b Y))
  invFun k := (EllObj.restrictScalars (awayHom b)).map k ≫ glueJb a b Xa Xb φ
  left_inv v := by
    dsimp only
    have h1 : (EllObj.restrictScalars (awayHom b)).map
        (unRestrictScalars (awayHom b)
          (factorGlueJb a b Xa Xb φ v (chartB_structMap_range b Y)))
        = factorGlueJb a b Xa Xb φ v (chartB_structMap_range b Y) :=
      restrictScalars_map_unRestrictScalars _ _
    rw [h1]
    exact factorGlueJb_glueJb a b Xa Xb φ v (chartB_structMap_range b Y)
  right_inv k := by
    dsimp only
    apply (EllObj.restrictScalars (awayHom b)).map_injective
    rw [restrictScalars_map_unRestrictScalars]
    refine glueJb_cancel a b Xa Xb φ ?_
    rw [factorGlueJb_glueJb]

/-- The inverse of the chart hom-equivalence is composition with `glueJa`. -/
private theorem glueChartHomEquivA_symm_apply (Y : EllObj R)
    (k : Y.baseChangeRing (awayHom a) ⟶ Xa) :
    (glueChartHomEquivA a b Xa Xb φ Y).symm k
      = (EllObj.restrictScalars (awayHom a)).map k ≫ glueJa a b Xa Xb φ := rfl

private theorem glueChartHomEquivB_symm_apply (Y : EllObj R)
    (k : Y.baseChangeRing (awayHom b) ⟶ Xb) :
    (glueChartHomEquivB a b Xa Xb φ Y).symm k
      = (EllObj.restrictScalars (awayHom b)).map k ≫ glueJb a b Xa Xb φ := rfl

/-- Naturality of the `a`-chart inclusion: any `f : Y' ⟶ Y` lifts to the `a`-charts,
compatibly with the inclusions. -/
private theorem yChartInclA_naturality (Y' Y : EllObj R) (f : Y' ⟶ Y) :
    (EllObj.restrictScalars (awayHom a)).map
        (baseChangeRingHomEquivInv Y (awayHom a) (Y'.baseChangeRing (awayHom a))
          (yChartInclA a Y' ≫ f))
      ≫ yChartInclA a Y = yChartInclA a Y' ≫ f := by
  have hfwd : ∀ (m : Y'.baseChangeRing (awayHom a) ⟶ Y.baseChangeRing (awayHom a)),
      baseChangeRingHomEquivFwd Y (awayHom a) (Y'.baseChangeRing (awayHom a)) m
        = (EllObj.restrictScalars (awayHom a)).map m ≫ yChartInclA a Y := by
    intro m
    conv_lhs => rw [← Category.comp_id m]
    rw [baseChangeRingHomEquivFwd_comp]
    rfl
  rw [← hfwd]
  exact (baseChangeRingHomEquiv Y (awayHom a)
    (Y'.baseChangeRing (awayHom a))).right_inv (yChartInclA a Y' ≫ f)

/-- Naturality of the `b`-chart inclusion. -/
private theorem yChartInclB_naturality (Y' Y : EllObj R) (f : Y' ⟶ Y) :
    (EllObj.restrictScalars (awayHom b)).map
        (baseChangeRingHomEquivInv Y (awayHom b) (Y'.baseChangeRing (awayHom b))
          (yChartInclB b Y' ≫ f))
      ≫ yChartInclB b Y = yChartInclB b Y' ≫ f := by
  have hfwd : ∀ (m : Y'.baseChangeRing (awayHom b) ⟶ Y.baseChangeRing (awayHom b)),
      baseChangeRingHomEquivFwd Y (awayHom b) (Y'.baseChangeRing (awayHom b)) m
        = (EllObj.restrictScalars (awayHom b)).map m ≫ yChartInclB b Y := by
    intro m
    conv_lhs => rw [← Category.comp_id m]
    rw [baseChangeRingHomEquivFwd_comp]
    rfl
  rw [← hfwd]
  exact (baseChangeRingHomEquiv Y (awayHom b)
    (Y'.baseChangeRing (awayHom b))).right_inv (yChartInclB b Y' ≫ f)

end ChartHomEquiv


/-! ## [R-sheaf-P] The Zariski-sheaf hypothesis on `P` and the parametrized descent

The recollement's inverse direction needs *exactly one* global input about `P`: that it is a
Zariski sheaf for the two-chart cover `Spec R = D(a) ∪ D(b)` pulled back to every test object `Y`.
We package that as `ZariskiSheaf`, taking it as an explicit hypothesis (`zglue`). The half that
fails for a bare presheaf (the `𝔽₄ × 𝔽₉` counterexample) is exactly the surjectivity of the
restriction map onto the compatible pairs; the separatedness is its injectivity. -/

/-- **Compatible chart-pairs.** For a test object `Y : Ell/R`, a pair of `P`-sections over the two
charts `Y|D(a)`, `Y|D(b)` that agree over the overlap `Y|D(ab)` (restriction via the overlap
inclusions `yOverlapInclA`/`yOverlapInclB`). This is the value-object of the two-chart Zariski
sheaf condition — the equaliser of `P(Y|D(a)) ⇉ P(Y|D(ab)) ⇇ P(Y|D(b))`. -/
def CompatPair (P : ModuliProblem R) (a b : R) (Y : EllObj R) : Type u :=
  { p : P.obj (op ((EllObj.restrictScalars (awayHom a)).obj (Y.baseChangeRing (awayHom a))))
          × P.obj (op ((EllObj.restrictScalars (awayHom b)).obj (Y.baseChangeRing (awayHom b)))) //
      P.map (yOverlapInclA a b Y).op p.1 = P.map (yOverlapInclB a b Y).op p.2 }

/-- **[R-sheaf-P] The two-chart Zariski-sheaf property of `P` (the `zglue` hypothesis).**

For every test object `Y : Ell/R`, restriction to the two charts `Y|D(a)`, `Y|D(b)` is a
*bijection* `P(Y) ≃ CompatPair P a b Y` onto the pairs agreeing over the overlap `Y|D(ab)`. The
`fst_eq`/`snd_eq` fields pin the bijection to be genuine chart-restriction (`P.map` along the chart
inclusions `yChartInclA`/`yChartInclB`), so this is the honest sheaf condition for the cover, not a
mere abstract iso.

This is precisely what the sorry-free `Stack.lean` lemmas `moduliProblem_fppf_separated`
(injectivity) and `moduliProblem_fppf_descent` (surjectivity) supply for a
`RelativelyRepresentable` `P`, applied to the fppf cover `Y|D(a) ⊔ Y|D(b) ⟶ Y` (open immersions
are flat + locally of finite presentation, and joint surjectivity comes from
`basicOpen_sup_basicOpen_eq_top`). The coordinator discharges `zglue` from those. -/
structure ZariskiSheaf (P : ModuliProblem R) (a b : R) where
  /-- Restriction to the two charts is a bijection onto compatible pairs. -/
  equiv : ∀ Y : EllObj R, P.obj (op Y) ≃ CompatPair P a b Y
  /-- The first component of the equivalence is restriction along the `a`-chart inclusion. -/
  fst_eq : ∀ (Y : EllObj R) (s : P.obj (op Y)),
    (equiv Y s).val.1 = P.map (yChartInclA a Y).op s
  /-- The second component of the equivalence is restriction along the `b`-chart inclusion. -/
  snd_eq : ∀ (Y : EllObj R) (s : P.obj (op Y)),
    (equiv Y s).val.2 = P.map (yChartInclB b Y).op s

/-- **[R-hom-glue] Zariski descent of `Hom(-, G)` (the geometric leaf).** For the glued object `G`,
morphisms `Y ⟶ G` biject naturally with compatible chart-pairs of `P` — i.e. `Hom(-, G)` is the
same two-chart Zariski sheaf as `P`. This bundles the three geometric facts of the descent: the
per-chart representability `repr_a`/`repr_b` (turning `Y|D(a) ⟶ Xa` into `P(Y|D(a))` via the
base-change ⊣ restrict-scalars adjunction), the identification of the `a`-chart of `G` with `Xa`,
and the source-cover gluing of an `Ell/R`-morphism from its two chart legs
(`Scheme.Cover.glueMorphisms` + `Scheme.isPullback_of_openCover` for the cartesian field). -/
structure HomGlueDescent {P : ModuliProblem R} (a b : R) (zglue : ZariskiSheaf P a b)
    (G : EllObj R) where
  /-- Morphisms into `G` biject with compatible chart-pairs. -/
  toEquiv : ∀ Y : EllObj R, (Y ⟶ G) ≃ CompatPair P a b Y
  /-- The bijection is natural in `Y` and compatible with the sheaf structure on `P`. -/
  natural : ∀ {Y' Y : EllObj R} (f : Y' ⟶ Y) (g : Y ⟶ G),
    toEquiv Y' (f ≫ g) = zglue.equiv Y' (P.map f.op ((zglue.equiv Y).symm (toEquiv Y g)))

/-! ## [R-hom-glue] the forward map to compatible pairs -/

section HomGlueAssembly

set_option backward.isDefEq.respectTransparency false

variable {P : ModuliProblem R} (a b : R)
variable {Xa : EllObj (CommRingCat.of (Localization.Away a))}
variable {Xb : EllObj (CommRingCat.of (Localization.Away b))}
variable (repr_a : (P.baseChange (awayHom a)).RepresentableBy Xa)
variable (repr_b : (P.baseChange (awayHom b)).RepresentableBy Xb)

/-- The chart pair of a morphism into the glued object is compatible on the overlap. -/
private theorem homGlueForward_compat (Y : EllObj R)
    (u : Y ⟶ glueEllObj a b Xa Xb (overlapIso a b repr_a repr_b)) :
    P.map (yOverlapInclA a b Y).op
        (repr_a.homEquiv
          ((glueChartHomEquivA a b Xa Xb (overlapIso a b repr_a repr_b) Y)
            (yChartInclA a Y ≫ u)))
      = P.map (yOverlapInclB a b Y).op
        (repr_b.homEquiv
          ((glueChartHomEquivB a b Xa Xb (overlapIso a b repr_a repr_b) Y)
            (yChartInclB b Y ≫ u))) := by
  rw [overlap_value_iff a b repr_a repr_b Y]
  refine overlap_compare_of_agree a b repr_a repr_b Y _ _ ?_
  have hA : (EllObj.restrictScalars (awayHom a)).map
      ((glueChartHomEquivA a b Xa Xb (overlapIso a b repr_a repr_b) Y)
        (yChartInclA a Y ≫ u))
      ≫ glueJa a b Xa Xb (overlapIso a b repr_a repr_b) = yChartInclA a Y ≫ u :=
    (glueChartHomEquivA a b Xa Xb (overlapIso a b repr_a repr_b) Y).symm_apply_apply
      (yChartInclA a Y ≫ u)
  have hB : (EllObj.restrictScalars (awayHom b)).map
      ((glueChartHomEquivB a b Xa Xb (overlapIso a b repr_a repr_b) Y)
        (yChartInclB b Y ≫ u))
      ≫ glueJb a b Xa Xb (overlapIso a b repr_a repr_b) = yChartInclB b Y ≫ u :=
    (glueChartHomEquivB a b Xa Xb (overlapIso a b repr_a repr_b) Y).symm_apply_apply
      (yChartInclB b Y ≫ u)
  rw [hA, hB, ← Category.assoc, yOverlapInclA_chartInclA, ← Category.assoc,
    yOverlapInclB_chartInclB]

/-- **[R-hom-glue] the forward map**: the compatible chart pair of a morphism into the
glued object. -/
private noncomputable def homGlueForwardFun (Y : EllObj R)
    (u : Y ⟶ glueEllObj a b Xa Xb (overlapIso a b repr_a repr_b)) : CompatPair P a b Y :=
  ⟨(repr_a.homEquiv
      ((glueChartHomEquivA a b Xa Xb (overlapIso a b repr_a repr_b) Y)
        (yChartInclA a Y ≫ u)),
    repr_b.homEquiv
      ((glueChartHomEquivB a b Xa Xb (overlapIso a b repr_a repr_b) Y)
        (yChartInclB b Y ≫ u))),
    homGlueForward_compat a b repr_a repr_b Y u⟩

private theorem homGlueForwardFun_injective (Y : EllObj R)
    (hab : ∃ x y : R, x * a + y * b = 1) :
    Function.Injective (homGlueForwardFun a b repr_a repr_b Y) := by
  intro u v huv
  have h1 : repr_a.homEquiv
      ((glueChartHomEquivA a b Xa Xb (overlapIso a b repr_a repr_b) Y)
        (yChartInclA a Y ≫ u))
      = repr_a.homEquiv
      ((glueChartHomEquivA a b Xa Xb (overlapIso a b repr_a repr_b) Y)
        (yChartInclA a Y ≫ v)) := congrArg (fun p => p.val.1) huv
  have h2 : repr_b.homEquiv
      ((glueChartHomEquivB a b Xa Xb (overlapIso a b repr_a repr_b) Y)
        (yChartInclB b Y ≫ u))
      = repr_b.homEquiv
      ((glueChartHomEquivB a b Xa Xb (overlapIso a b repr_a repr_b) Y)
        (yChartInclB b Y ≫ v)) := congrArg (fun p => p.val.2) huv
  have hjA : yChartInclA a Y ≫ u = yChartInclA a Y ≫ v :=
    (glueChartHomEquivA a b Xa Xb (overlapIso a b repr_a repr_b) Y).injective
      (repr_a.homEquiv.injective h1)
  have hjB : yChartInclB b Y ≫ u = yChartInclB b Y ≫ v :=
    (glueChartHomEquivB a b Xa Xb (overlapIso a b repr_a repr_b) Y).injective
      (repr_b.homEquiv.injective h2)
  exact glueHom_source_ext a b Xa Xb (overlapIso a b repr_a repr_b) Y hab hjA hjB

private theorem homGlueForwardFun_surjective (Y : EllObj R)
    (hab : ∃ x y : R, x * a + y * b = 1) :
    Function.Surjective (homGlueForwardFun a b repr_a repr_b Y) := by
  rintro ⟨⟨p1, p2⟩, hp⟩
  set kA := repr_a.homEquiv.symm p1 with hkA
  set kB := repr_b.homEquiv.symm p2 with hkB
  have e1 : repr_a.homEquiv kA = p1 := by
    rw [hkA]; exact Equiv.apply_symm_apply _ _
  have e2 : repr_b.homEquiv kB = p2 := by
    rw [hkB]; exact Equiv.apply_symm_apply _ _
  have hp' : P.map (yOverlapInclA a b Y).op (repr_a.homEquiv kA)
      = P.map (yOverlapInclB a b Y).op (repr_b.homEquiv kB) := by
    rw [e1, e2]
    exact hp
  have hstar := (overlap_value_iff a b repr_a repr_b Y kA kB).mp hp'
  have hagr := overlap_agree_of_compare a b repr_a repr_b Y kA kB hstar
  refine ⟨glueHomOfCharts a b Xa Xb (overlapIso a b repr_a repr_b) Y hab _ _ hagr, ?_⟩
  refine Subtype.ext (Prod.ext ?_ ?_)
  · show repr_a.homEquiv
        ((glueChartHomEquivA a b Xa Xb (overlapIso a b repr_a repr_b) Y)
          (yChartInclA a Y
            ≫ glueHomOfCharts a b Xa Xb (overlapIso a b repr_a repr_b) Y hab _ _ hagr))
      = p1
    rw [yChartInclA_glueHomOfCharts]
    rw [show (glueChartHomEquivA a b Xa Xb (overlapIso a b repr_a repr_b) Y)
        ((EllObj.restrictScalars (awayHom a)).map kA
          ≫ glueJa a b Xa Xb (overlapIso a b repr_a repr_b)) = kA from
      (glueChartHomEquivA a b Xa Xb (overlapIso a b repr_a repr_b) Y).apply_symm_apply kA]
    exact e1
  · show repr_b.homEquiv
        ((glueChartHomEquivB a b Xa Xb (overlapIso a b repr_a repr_b) Y)
          (yChartInclB b Y
            ≫ glueHomOfCharts a b Xa Xb (overlapIso a b repr_a repr_b) Y hab _ _ hagr))
      = p2
    rw [yChartInclB_glueHomOfCharts]
    rw [show (glueChartHomEquivB a b Xa Xb (overlapIso a b repr_a repr_b) Y)
        ((EllObj.restrictScalars (awayHom b)).map kB
          ≫ glueJb a b Xa Xb (overlapIso a b repr_a repr_b)) = kB from
      (glueChartHomEquivB a b Xa Xb (overlapIso a b repr_a repr_b) Y).apply_symm_apply kB]
    exact e2

/-- Naturality of the forward chart value (`a`-side). -/
private theorem homGlueForward_natural_a {Y' Y : EllObj R} (f : Y' ⟶ Y)
    (g : Y ⟶ glueEllObj a b Xa Xb (overlapIso a b repr_a repr_b)) :
    (glueChartHomEquivA a b Xa Xb (overlapIso a b repr_a repr_b) Y')
        (yChartInclA a Y' ≫ f ≫ g)
      = baseChangeRingHomEquivInv Y (awayHom a) (Y'.baseChangeRing (awayHom a))
          (yChartInclA a Y' ≫ f)
        ≫ (glueChartHomEquivA a b Xa Xb (overlapIso a b repr_a repr_b) Y)
          (yChartInclA a Y ≫ g) := by
  refine (glueChartHomEquivA a b Xa Xb (overlapIso a b repr_a repr_b) Y').symm.injective ?_
  rw [Equiv.symm_apply_apply, glueChartHomEquivA_symm_apply, Functor.map_comp,
    Category.assoc]
  rw [show (EllObj.restrictScalars (awayHom a)).map
      ((glueChartHomEquivA a b Xa Xb (overlapIso a b repr_a repr_b) Y)
        (yChartInclA a Y ≫ g))
      ≫ glueJa a b Xa Xb (overlapIso a b repr_a repr_b) = yChartInclA a Y ≫ g from
    (glueChartHomEquivA a b Xa Xb (overlapIso a b repr_a repr_b) Y).symm_apply_apply
      (yChartInclA a Y ≫ g)]
  rw [reassoc_of% (yChartInclA_naturality a Y' Y f)]

/-- Naturality of the forward chart value (`b`-side). -/
private theorem homGlueForward_natural_b {Y' Y : EllObj R} (f : Y' ⟶ Y)
    (g : Y ⟶ glueEllObj a b Xa Xb (overlapIso a b repr_a repr_b)) :
    (glueChartHomEquivB a b Xa Xb (overlapIso a b repr_a repr_b) Y')
        (yChartInclB b Y' ≫ f ≫ g)
      = baseChangeRingHomEquivInv Y (awayHom b) (Y'.baseChangeRing (awayHom b))
          (yChartInclB b Y' ≫ f)
        ≫ (glueChartHomEquivB a b Xa Xb (overlapIso a b repr_a repr_b) Y)
          (yChartInclB b Y ≫ g) := by
  refine (glueChartHomEquivB a b Xa Xb (overlapIso a b repr_a repr_b) Y').symm.injective ?_
  rw [Equiv.symm_apply_apply, glueChartHomEquivB_symm_apply, Functor.map_comp,
    Category.assoc]
  rw [show (EllObj.restrictScalars (awayHom b)).map
      ((glueChartHomEquivB a b Xa Xb (overlapIso a b repr_a repr_b) Y)
        (yChartInclB b Y ≫ g))
      ≫ glueJb a b Xa Xb (overlapIso a b repr_a repr_b) = yChartInclB b Y ≫ g from
    (glueChartHomEquivB a b Xa Xb (overlapIso a b repr_a repr_b) Y).symm_apply_apply
      (yChartInclB b Y ≫ g)]
  rw [reassoc_of% (yChartInclB_naturality b Y' Y f)]

end HomGlueAssembly

set_option linter.unusedVariables false in
/-- **[R-hom-glue], the geometric descent for the glued object (the single remaining `sorry`).**

`Hom(-, glueEllObj …)` is the two-chart Zariski sheaf `CompatPair P a b`. This is the sole
irreducible geometric content left in the recollement: assembling an `Ell/R`-morphism `Y ⟶ G` from
its two chart legs `Y|D(a) ⟶ Xa`, `Y|D(b) ⟶ Xb` (glued via `Scheme.Cover.glueMorphisms` on the
base and total space over the cover `Y.base = Y|D(a) ∪ Y|D(b)`, the cartesian `isPullback` field
checked Zariski-locally via `Scheme.isPullback_of_openCover`), together with the per-chart
representability equivalences from `repr_a`/`repr_b` and the identification of the `a`-chart of `G`
with `Xa`. Everything it consumes — the chart/overlap inclusions, the glued object and its
cartesian chart squares `isPullback_glueTotalInl/Inr`, `glueBase_hom_ext`/`glueTotal_hom_ext`, the
adjunction `baseChangeRingHomEquiv`, and `repr_a`/`repr_b` — is already proven above and in the
file. -/
private noncomputable def homGlueDescentData {P : ModuliProblem R} (a b : R)
    (hab : ∃ x y : R, x * a + y * b = 1) (hrel : P.RelativelyRepresentable)
    {Xa : EllObj (CommRingCat.of (Localization.Away a))}
    {Xb : EllObj (CommRingCat.of (Localization.Away b))}
    (repr_a : (P.baseChange (awayHom a)).RepresentableBy Xa)
    (repr_b : (P.baseChange (awayHom b)).RepresentableBy Xb)
    (zglue : ZariskiSheaf P a b) :
    HomGlueDescent a b zglue (glueEllObj a b Xa Xb (overlapIso a b repr_a repr_b)) :=
  { toEquiv := fun Y => Equiv.ofBijective (homGlueForwardFun a b repr_a repr_b Y)
      ⟨homGlueForwardFun_injective a b repr_a repr_b Y hab,
        homGlueForwardFun_surjective a b repr_a repr_b Y hab⟩
    natural := fun {Y' Y} f g => by
      show homGlueForwardFun a b repr_a repr_b Y' (f ≫ g)
        = zglue.equiv Y' (P.map f.op ((zglue.equiv Y).symm
            (homGlueForwardFun a b repr_a repr_b Y g)))
      refine Subtype.ext (Prod.ext ?_ ?_)
      · show repr_a.homEquiv
            ((glueChartHomEquivA a b Xa Xb (overlapIso a b repr_a repr_b) Y')
              (yChartInclA a Y' ≫ f ≫ g))
          = (zglue.equiv Y' (P.map f.op ((zglue.equiv Y).symm
              (homGlueForwardFun a b repr_a repr_b Y g)))).val.1
        rw [zglue.fst_eq]
        have hs1 : P.map (yChartInclA a Y).op
            ((zglue.equiv Y).symm (homGlueForwardFun a b repr_a repr_b Y g))
            = repr_a.homEquiv
              ((glueChartHomEquivA a b Xa Xb (overlapIso a b repr_a repr_b) Y)
                (yChartInclA a Y ≫ g)) := by
          have h0 : zglue.equiv Y
              ((zglue.equiv Y).symm (homGlueForwardFun a b repr_a repr_b Y g))
              = homGlueForwardFun a b repr_a repr_b Y g :=
            (zglue.equiv Y).apply_symm_apply _
          have h1 := zglue.fst_eq Y
            ((zglue.equiv Y).symm (homGlueForwardFun a b repr_a repr_b Y g))
          rw [h0] at h1
          exact h1.symm
        rw [← Functor.map_comp_apply, ← op_comp, ← yChartInclA_naturality a Y' Y f,
          op_comp, Functor.map_comp_apply, hs1]
        exact (congrArg repr_a.homEquiv
          (homGlueForward_natural_a a b repr_a repr_b f g)).trans
          (repr_a.homEquiv_comp _ _)
      · show repr_b.homEquiv
            ((glueChartHomEquivB a b Xa Xb (overlapIso a b repr_a repr_b) Y')
              (yChartInclB b Y' ≫ f ≫ g))
          = (zglue.equiv Y' (P.map f.op ((zglue.equiv Y).symm
              (homGlueForwardFun a b repr_a repr_b Y g)))).val.2
        rw [zglue.snd_eq]
        have hs1 : P.map (yChartInclB b Y).op
            ((zglue.equiv Y).symm (homGlueForwardFun a b repr_a repr_b Y g))
            = repr_b.homEquiv
              ((glueChartHomEquivB a b Xa Xb (overlapIso a b repr_a repr_b) Y)
                (yChartInclB b Y ≫ g)) := by
          have h0 : zglue.equiv Y
              ((zglue.equiv Y).symm (homGlueForwardFun a b repr_a repr_b Y g))
              = homGlueForwardFun a b repr_a repr_b Y g :=
            (zglue.equiv Y).apply_symm_apply _
          have h1 := zglue.snd_eq Y
            ((zglue.equiv Y).symm (homGlueForwardFun a b repr_a repr_b Y g))
          rw [h0] at h1
          exact h1.symm
        rw [← Functor.map_comp_apply, ← op_comp, ← yChartInclB_naturality b Y' Y f,
          op_comp, Functor.map_comp_apply, hs1]
        exact (congrArg repr_b.homEquiv
          (homGlueForward_natural_b a b repr_a repr_b f g)).trans
          (repr_b.homEquiv_comp _ _) }

/-- **[R-glue-repr], parametrized over the sheaf property.** `glueEllObj a b Xa Xb (overlapIso …)`
represents `P`, *given* the two-chart Zariski-sheaf property `zglue` of `P`. This is the full
functor-of-points descent (KM Cor. 4.7.1 core): the representing bijection `(Y ⟶ G) ≃ P(Y)` is the
composite of the geometric descent `Hom(-, G) ≃ CompatPair P a b` (`homGlueDescentData`) with the
inverse of the sheaf bijection `P ≃ CompatPair P a b` (`zglue`). Naturality (`homEquiv_comp`) is
immediate from `HomGlueDescent.natural`.

The coordinator discharges the `:1141` `glueEllObj_representableBy` sorry as
`glueEllObj_representableBy_of_zariskiGlue a b hab hrel repr_a repr_b zglue`, where `zglue` is the
`ZariskiSheaf P a b` produced from the `Stack.lean` fppf-sheaf lemmas. -/
private noncomputable def glueEllObj_representableBy_of_zariskiGlue {P : ModuliProblem R} (a b : R)
    (hab : ∃ x y : R, x * a + y * b = 1) (hrel : P.RelativelyRepresentable)
    {Xa : EllObj (CommRingCat.of (Localization.Away a))}
    {Xb : EllObj (CommRingCat.of (Localization.Away b))}
    (repr_a : (P.baseChange (awayHom a)).RepresentableBy Xa)
    (repr_b : (P.baseChange (awayHom b)).RepresentableBy Xb)
    (zglue : ZariskiSheaf P a b) :
    P.RepresentableBy (glueEllObj a b Xa Xb (overlapIso a b repr_a repr_b)) :=
  let hgd := homGlueDescentData a b hab hrel repr_a repr_b zglue
  { homEquiv := fun {Y} => (hgd.toEquiv Y).trans (zglue.equiv Y).symm
    homEquiv_comp := fun {Y' Y} f g => by
      show (zglue.equiv Y').symm (hgd.toEquiv Y' (f ≫ g))
        = P.map f.op ((zglue.equiv Y).symm (hgd.toEquiv Y g))
      rw [hgd.natural f g, Equiv.symm_apply_apply] }

/-! ## [R-sheaf-P] the two-chart Zariski-sheaf property from relative representability

`P`-sections are classified, at every test object, by sections of the relative
representing scheme (`hrel`, KM Cor. 4.7.1's standing "relatively representable" clause —
the same clause the fppf lemmas of `Moduli/Stack.lean` consume); sections of a scheme over
the base glue along the two-chart open cover (`Scheme.Cover.glueMorphisms`), so `P` is a
two-chart Zariski sheaf. -/

section ZariskiSheafConstruction

set_option backward.isDefEq.respectTransparency false

variable {P : ModuliProblem R} (a b : R)

/-- Presentation-independent naturality of a relative representation datum (clone of the
`Moduli/QuotientProblem.lean` helper, which is `private` there): transporting a chart value
along *any* `Ell/R`-morphism `w` of charts which lies over `k` and commutes with the chart
projections computes as precomposition of the classifying section by `k`. -/
private theorem map_eqv_recoll {X₀ : EllObj R}
    (d₀ : ModuliProblem.RelRepData P X₀) {T T' : Scheme.{u}}
    {g : T ⟶ X₀.base} {g' : T' ⟶ X₀.base}
    (w : X₀.pullbackAlong g' ⟶ X₀.pullbackAlong g) (k : T' ⟶ T)
    (hbk : w.baseHom = k) (hk : k ≫ g = g')
    (hwπ : w ≫ X₀.pullbackAlongπ g = X₀.pullbackAlongπ g')
    (h : { h : T ⟶ d₀.Z // h ≫ d₀.f = g }) :
    P.map w.op (d₀.eqv g h) =
      d₀.eqv g' ⟨k ≫ h.1, by rw [Category.assoc, h.2, hk]⟩ := by
  subst hk
  have hw : w = X₀.pullbackAlongMap g k := by
    apply (EllObj.homPullbackAlongEquiv X₀ g (X₀.pullbackAlong (k ≫ g))).injective
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show w ≫ X₀.pullbackAlongπ g =
        X₀.pullbackAlongMap g k ≫ X₀.pullbackAlongπ g
      rw [hwπ, ModuliProblem.pullbackAlongMap_pullbackAlongπ]
    · exact hbk
  rw [hw]
  exact (d₀.nat g k h).symm

/-- Restriction along an `Ell/R`-isomorphism is injective on `P`-values. -/
private theorem map_iso_op_injective {V W : EllObj R} (e : V ≅ W) :
    Function.Injective (P.map e.hom.op : P.obj (op W) → P.obj (op V)) := by
  intro x y hxy
  have h := congrArg (P.map e.inv.op) hxy
  rwa [← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id, op_id, Functor.map_id_apply,
    ← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id, op_id, Functor.map_id_apply] at h

variable (Y : EllObj R)

private theorem isoPA_id_hom_π :
    (EllObj.isoPullbackAlong (𝟙 Y)).hom ≫ Y.pullbackAlongπ (𝟙 Y.base) = 𝟙 Y :=
  EllObj.toPullbackAlong_pullbackAlongπ (𝟙 Y)

private theorem isoPA_inv_comp {V : EllObj R} (j : V ⟶ Y) :
    (EllObj.isoPullbackAlong j).inv ≫ j = Y.pullbackAlongπ j.baseHom := by
  rw [Iso.inv_comp_eq]
  exact (EllObj.toPullbackAlong_pullbackAlongπ j).symm

private theorem isoPA_hom_π {V : EllObj R} (j : V ⟶ Y) :
    (EllObj.isoPullbackAlong j).hom ≫ Y.pullbackAlongπ j.baseHom = j :=
  EllObj.toPullbackAlong_pullbackAlongπ j

/-- The `a`-chart inclusion, conjugated into the tautological charts. -/
private noncomputable def chartWA :
    Y.pullbackAlong (yChartInclA a Y).baseHom ⟶ Y.pullbackAlong (𝟙 Y.base) :=
  (EllObj.isoPullbackAlong (yChartInclA a Y)).inv ≫ yChartInclA a Y
    ≫ (EllObj.isoPullbackAlong (𝟙 Y)).hom

private noncomputable def chartWB :
    Y.pullbackAlong (yChartInclB b Y).baseHom ⟶ Y.pullbackAlong (𝟙 Y.base) :=
  (EllObj.isoPullbackAlong (yChartInclB b Y)).inv ≫ yChartInclB b Y
    ≫ (EllObj.isoPullbackAlong (𝟙 Y)).hom

private theorem chartWA_baseHom :
    (chartWA a Y).baseHom = (yChartInclA a Y).baseHom := by
  show (𝟙 _ ≫ (yChartInclA a Y).baseHom ≫ 𝟙 _ : _) = (yChartInclA a Y).baseHom
  rw [Category.id_comp, Category.comp_id]

private theorem chartWB_baseHom :
    (chartWB b Y).baseHom = (yChartInclB b Y).baseHom := by
  show (𝟙 _ ≫ (yChartInclB b Y).baseHom ≫ 𝟙 _ : _) = (yChartInclB b Y).baseHom
  rw [Category.id_comp, Category.comp_id]

private theorem chartWA_π :
    chartWA a Y ≫ Y.pullbackAlongπ (𝟙 Y.base)
      = Y.pullbackAlongπ (yChartInclA a Y).baseHom := by
  rw [chartWA, Category.assoc, Category.assoc, isoPA_id_hom_π, Category.comp_id]
  exact isoPA_inv_comp Y (yChartInclA a Y)

private theorem chartWB_π :
    chartWB b Y ≫ Y.pullbackAlongπ (𝟙 Y.base)
      = Y.pullbackAlongπ (yChartInclB b Y).baseHom := by
  rw [chartWB, Category.assoc, Category.assoc, isoPA_id_hom_π, Category.comp_id]
  exact isoPA_inv_comp Y (yChartInclB b Y)

/-- The overlap-into-`a`-chart inclusion, conjugated into the tautological charts. -/
private noncomputable def overlapWA :
    Y.pullbackAlong (yChartInclAB a b Y).baseHom
      ⟶ Y.pullbackAlong (yChartInclA a Y).baseHom :=
  (EllObj.isoPullbackAlong (yChartInclAB a b Y)).inv ≫ yOverlapInclA a b Y
    ≫ (EllObj.isoPullbackAlong (yChartInclA a Y)).hom

private noncomputable def overlapWB :
    Y.pullbackAlong (yChartInclAB a b Y).baseHom
      ⟶ Y.pullbackAlong (yChartInclB b Y).baseHom :=
  (EllObj.isoPullbackAlong (yChartInclAB a b Y)).inv ≫ yOverlapInclB a b Y
    ≫ (EllObj.isoPullbackAlong (yChartInclB b Y)).hom

private theorem overlapWA_baseHom :
    (overlapWA a b Y).baseHom = yOverlapBaseA a b Y := by
  show (𝟙 _ ≫ yOverlapBaseA a b Y ≫ 𝟙 _ : _) = yOverlapBaseA a b Y
  rw [Category.id_comp, Category.comp_id]

private theorem overlapWB_baseHom :
    (overlapWB a b Y).baseHom = yOverlapBaseB a b Y := by
  show (𝟙 _ ≫ yOverlapBaseB a b Y ≫ 𝟙 _ : _) = yOverlapBaseB a b Y
  rw [Category.id_comp, Category.comp_id]

private theorem overlapWA_k :
    yOverlapBaseA a b Y ≫ (yChartInclA a Y).baseHom = (yChartInclAB a b Y).baseHom := by
  rw [yChartInclA_baseHom, yChartInclAB_baseHom]
  exact yOverlapBaseA_fst a b Y

private theorem overlapWB_k :
    yOverlapBaseB a b Y ≫ (yChartInclB b Y).baseHom = (yChartInclAB a b Y).baseHom := by
  rw [yChartInclB_baseHom, yChartInclAB_baseHom]
  exact yOverlapBaseB_fst a b Y

private theorem overlapWA_π :
    overlapWA a b Y ≫ Y.pullbackAlongπ (yChartInclA a Y).baseHom
      = Y.pullbackAlongπ (yChartInclAB a b Y).baseHom := by
  rw [overlapWA, Category.assoc, Category.assoc, isoPA_hom_π Y (yChartInclA a Y),
    yOverlapInclA_chartInclA]
  exact isoPA_inv_comp Y (yChartInclAB a b Y)

private theorem overlapWB_π :
    overlapWB a b Y ≫ Y.pullbackAlongπ (yChartInclB b Y).baseHom
      = Y.pullbackAlongπ (yChartInclAB a b Y).baseHom := by
  rw [overlapWB, Category.assoc, Category.assoc, isoPA_hom_π Y (yChartInclB b Y),
    yOverlapInclB_chartInclB]
  exact isoPA_inv_comp Y (yChartInclAB a b Y)

/-- The chart value of a `P`-section, computed through the classifying section of the
relative representing scheme (`a`-side). -/
private theorem map_yChartInclA_eqv (d : ModuliProblem.RelRepData P Y) (s : P.obj (op Y)) :
    P.map (yChartInclA a Y).op s
      = P.map (EllObj.isoPullbackAlong (yChartInclA a Y)).hom.op
          (d.eqv (yChartInclA a Y).baseHom
            ⟨(yChartInclA a Y).baseHom
                ≫ ((d.eqv (𝟙 Y.base)).symm
                  (P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op s)).1, by
              rw [Category.assoc,
                ((d.eqv (𝟙 Y.base)).symm
                  (P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op s)).2,
                Category.comp_id]⟩) := by
  set s0 := P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op s with hs0
  set σ := (d.eqv (𝟙 Y.base)).symm s0 with hσdef
  have hrec : s = P.map (EllObj.isoPullbackAlong (𝟙 Y)).hom.op (d.eqv (𝟙 Y.base) σ) := by
    rw [hσdef, Equiv.apply_symm_apply, hs0, ← Functor.map_comp_apply, ← op_comp,
      Iso.hom_inv_id, op_id, Functor.map_id_apply]
  calc P.map (yChartInclA a Y).op s
      = P.map (yChartInclA a Y).op
          (P.map (EllObj.isoPullbackAlong (𝟙 Y)).hom.op (d.eqv (𝟙 Y.base) σ)) := by
        rw [← hrec]
    _ = P.map (yChartInclA a Y ≫ (EllObj.isoPullbackAlong (𝟙 Y)).hom).op
          (d.eqv (𝟙 Y.base) σ) := by
        rw [← Functor.map_comp_apply, ← op_comp]
    _ = P.map ((EllObj.isoPullbackAlong (yChartInclA a Y)).hom ≫ chartWA a Y).op
          (d.eqv (𝟙 Y.base) σ) := by
        rw [show yChartInclA a Y ≫ (EllObj.isoPullbackAlong (𝟙 Y)).hom
            = (EllObj.isoPullbackAlong (yChartInclA a Y)).hom ≫ chartWA a Y from by
          rw [chartWA]
          simp only [Iso.hom_inv_id_assoc]]
        rfl
    _ = P.map (EllObj.isoPullbackAlong (yChartInclA a Y)).hom.op
          (P.map (chartWA a Y).op (d.eqv (𝟙 Y.base) σ)) := by
        rw [op_comp, Functor.map_comp_apply]
    _ = _ :=
        congrArg (P.map (EllObj.isoPullbackAlong (yChartInclA a Y)).hom.op)
          (map_eqv_recoll d (chartWA a Y) (yChartInclA a Y).baseHom (chartWA_baseHom a Y)
            (Category.comp_id _) (chartWA_π a Y) σ)

/-- The `b`-side. -/
private theorem map_yChartInclB_eqv (d : ModuliProblem.RelRepData P Y) (s : P.obj (op Y)) :
    P.map (yChartInclB b Y).op s
      = P.map (EllObj.isoPullbackAlong (yChartInclB b Y)).hom.op
          (d.eqv (yChartInclB b Y).baseHom
            ⟨(yChartInclB b Y).baseHom
                ≫ ((d.eqv (𝟙 Y.base)).symm
                  (P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op s)).1, by
              rw [Category.assoc,
                ((d.eqv (𝟙 Y.base)).symm
                  (P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op s)).2,
                Category.comp_id]⟩) := by
  set s0 := P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op s with hs0
  set σ := (d.eqv (𝟙 Y.base)).symm s0 with hσdef
  have hrec : s = P.map (EllObj.isoPullbackAlong (𝟙 Y)).hom.op (d.eqv (𝟙 Y.base) σ) := by
    rw [hσdef, Equiv.apply_symm_apply, hs0, ← Functor.map_comp_apply, ← op_comp,
      Iso.hom_inv_id, op_id, Functor.map_id_apply]
  calc P.map (yChartInclB b Y).op s
      = P.map (yChartInclB b Y).op
          (P.map (EllObj.isoPullbackAlong (𝟙 Y)).hom.op (d.eqv (𝟙 Y.base) σ)) := by
        rw [← hrec]
    _ = P.map (yChartInclB b Y ≫ (EllObj.isoPullbackAlong (𝟙 Y)).hom).op
          (d.eqv (𝟙 Y.base) σ) := by
        rw [← Functor.map_comp_apply, ← op_comp]
    _ = P.map ((EllObj.isoPullbackAlong (yChartInclB b Y)).hom ≫ chartWB b Y).op
          (d.eqv (𝟙 Y.base) σ) := by
        rw [show yChartInclB b Y ≫ (EllObj.isoPullbackAlong (𝟙 Y)).hom
            = (EllObj.isoPullbackAlong (yChartInclB b Y)).hom ≫ chartWB b Y from by
          rw [chartWB]
          simp only [Iso.hom_inv_id_assoc]]
        rfl
    _ = P.map (EllObj.isoPullbackAlong (yChartInclB b Y)).hom.op
          (P.map (chartWB b Y).op (d.eqv (𝟙 Y.base) σ)) := by
        rw [op_comp, Functor.map_comp_apply]
    _ = _ :=
        congrArg (P.map (EllObj.isoPullbackAlong (yChartInclB b Y)).hom.op)
          (map_eqv_recoll d (chartWB b Y) (yChartInclB b Y).baseHom (chartWB_baseHom b Y)
            (Category.comp_id _) (chartWB_π b Y) σ)

/-- The overlap value of an `a`-chart value, computed on classifying sections. -/
private theorem map_yOverlapInclA_eqv (d : ModuliProblem.RelRepData P Y)
    (σA : { h : ((EllObj.restrictScalars (awayHom a)).obj
        (Y.baseChangeRing (awayHom a))).base ⟶ d.Z //
      h ≫ d.f = (yChartInclA a Y).baseHom }) :
    P.map (yOverlapInclA a b Y).op
        (P.map (EllObj.isoPullbackAlong (yChartInclA a Y)).hom.op
          (d.eqv (yChartInclA a Y).baseHom σA))
      = P.map (EllObj.isoPullbackAlong (yChartInclAB a b Y)).hom.op
          (d.eqv (yChartInclAB a b Y).baseHom
            ⟨yOverlapBaseA a b Y ≫ σA.1, by
              rw [Category.assoc, σA.2, overlapWA_k]⟩) := by
  calc P.map (yOverlapInclA a b Y).op
        (P.map (EllObj.isoPullbackAlong (yChartInclA a Y)).hom.op
          (d.eqv (yChartInclA a Y).baseHom σA))
      = P.map (yOverlapInclA a b Y ≫ (EllObj.isoPullbackAlong (yChartInclA a Y)).hom).op
          (d.eqv (yChartInclA a Y).baseHom σA) := by
        rw [← Functor.map_comp_apply, ← op_comp]
    _ = P.map ((EllObj.isoPullbackAlong (yChartInclAB a b Y)).hom ≫ overlapWA a b Y).op
          (d.eqv (yChartInclA a Y).baseHom σA) := by
        rw [show yOverlapInclA a b Y ≫ (EllObj.isoPullbackAlong (yChartInclA a Y)).hom
            = (EllObj.isoPullbackAlong (yChartInclAB a b Y)).hom ≫ overlapWA a b Y from by
          rw [overlapWA]
          simp only [Iso.hom_inv_id_assoc]]
    _ = P.map (EllObj.isoPullbackAlong (yChartInclAB a b Y)).hom.op
          (P.map (overlapWA a b Y).op (d.eqv (yChartInclA a Y).baseHom σA)) := by
        rw [op_comp, Functor.map_comp_apply]
    _ = _ :=
        congrArg (P.map (EllObj.isoPullbackAlong (yChartInclAB a b Y)).hom.op)
          (map_eqv_recoll d (overlapWA a b Y) (yOverlapBaseA a b Y)
            (overlapWA_baseHom a b Y) (overlapWA_k a b Y) (overlapWA_π a b Y) σA)

private theorem map_yOverlapInclB_eqv (d : ModuliProblem.RelRepData P Y)
    (σB : { h : ((EllObj.restrictScalars (awayHom b)).obj
        (Y.baseChangeRing (awayHom b))).base ⟶ d.Z //
      h ≫ d.f = (yChartInclB b Y).baseHom }) :
    P.map (yOverlapInclB a b Y).op
        (P.map (EllObj.isoPullbackAlong (yChartInclB b Y)).hom.op
          (d.eqv (yChartInclB b Y).baseHom σB))
      = P.map (EllObj.isoPullbackAlong (yChartInclAB a b Y)).hom.op
          (d.eqv (yChartInclAB a b Y).baseHom
            ⟨yOverlapBaseB a b Y ≫ σB.1, by
              rw [Category.assoc, σB.2, overlapWB_k]⟩) := by
  calc P.map (yOverlapInclB a b Y).op
        (P.map (EllObj.isoPullbackAlong (yChartInclB b Y)).hom.op
          (d.eqv (yChartInclB b Y).baseHom σB))
      = P.map (yOverlapInclB a b Y ≫ (EllObj.isoPullbackAlong (yChartInclB b Y)).hom).op
          (d.eqv (yChartInclB b Y).baseHom σB) := by
        rw [← Functor.map_comp_apply, ← op_comp]
    _ = P.map ((EllObj.isoPullbackAlong (yChartInclAB a b Y)).hom ≫ overlapWB a b Y).op
          (d.eqv (yChartInclB b Y).baseHom σB) := by
        rw [show yOverlapInclB a b Y ≫ (EllObj.isoPullbackAlong (yChartInclB b Y)).hom
            = (EllObj.isoPullbackAlong (yChartInclAB a b Y)).hom ≫ overlapWB a b Y from by
          rw [overlapWB]
          simp only [Iso.hom_inv_id_assoc]]
    _ = P.map (EllObj.isoPullbackAlong (yChartInclAB a b Y)).hom.op
          (P.map (overlapWB a b Y).op (d.eqv (yChartInclB b Y).baseHom σB)) := by
        rw [op_comp, Functor.map_comp_apply]
    _ = _ :=
        congrArg (P.map (EllObj.isoPullbackAlong (yChartInclAB a b Y)).hom.op)
          (map_eqv_recoll d (overlapWB a b Y) (yOverlapBaseB a b Y)
            (overlapWB_baseHom a b Y) (overlapWB_k a b Y) (overlapWB_π a b Y) σB)

/-- The two-chart restriction map, valued in compatible pairs. -/
private noncomputable def zariskiSheafRestrict (Y : EllObj R) (s : P.obj (op Y)) :
    CompatPair P a b Y :=
  ⟨(P.map (yChartInclA a Y).op s, P.map (yChartInclB b Y).op s), by
    rw [← Functor.map_comp_apply, ← op_comp, yOverlapInclA_chartInclA,
      ← Functor.map_comp_apply, ← op_comp, yOverlapInclB_chartInclB]⟩

/-- **[R-sheaf-P]** The two-chart restriction map is bijective: `P`-sections are classified
by sections of the relative representing scheme, and those glue uniquely along the
two-chart open cover of the base. -/
private theorem zariskiSheafRestrict_bijective
    (hab : ∃ x y : R, x * a + y * b = 1) (hrel : P.RelativelyRepresentable)
    (Y : EllObj R) :
    Function.Bijective (zariskiSheafRestrict (P := P) a b Y) := by
  obtain ⟨d⟩ := (ModuliProblem.relativelyRepresentable_iff_nonempty_relRepData P).mp hrel Y
  refine ⟨?_, ?_⟩
  · -- injectivity
    intro s t hst
    have h1 : P.map (yChartInclA a Y).op s = P.map (yChartInclA a Y).op t :=
      congrArg (fun p => p.val.1) hst
    have h2 : P.map (yChartInclB b Y).op s = P.map (yChartInclB b Y).op t :=
      congrArg (fun p => p.val.2) hst
    rw [map_yChartInclA_eqv a Y d s, map_yChartInclA_eqv a Y d t] at h1
    rw [map_yChartInclB_eqv b Y d s, map_yChartInclB_eqv b Y d t] at h2
    have h1' := congrArg Subtype.val
      ((d.eqv (yChartInclA a Y).baseHom).injective
        (map_iso_op_injective (EllObj.isoPullbackAlong (yChartInclA a Y)) h1))
    have h2' := congrArg Subtype.val
      ((d.eqv (yChartInclB b Y).baseHom).injective
        (map_iso_op_injective (EllObj.isoPullbackAlong (yChartInclB b Y)) h2))
    have hσ : ((d.eqv (𝟙 Y.base)).symm
          (P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op s)).1
        = ((d.eqv (𝟙 Y.base)).symm
          (P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op t)).1 := by
      refine (yBaseCover a b Y hab).hom_ext _ _ fun i => ?_
      cases i
      · show pullback.fst Y.structMap (Spec.map (awayHom b)) ≫ _
          = pullback.fst Y.structMap (Spec.map (awayHom b)) ≫ _
        have hb1 := h2'
        rw [yChartInclB_baseHom] at hb1
        exact hb1
      · show pullback.fst Y.structMap (Spec.map (awayHom a)) ≫ _
          = pullback.fst Y.structMap (Spec.map (awayHom a)) ≫ _
        have ha1 := h1'
        rw [yChartInclA_baseHom] at ha1
        exact ha1
    have hs0 : P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op s
        = P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op t := by
      have := congrArg (d.eqv (𝟙 Y.base)) (Subtype.ext hσ :
        ((d.eqv (𝟙 Y.base)).symm (P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op s))
          = ((d.eqv (𝟙 Y.base)).symm
            (P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op t)))
      rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    have hfin := congrArg (P.map (EllObj.isoPullbackAlong (𝟙 Y)).hom.op) hs0
    rwa [← Functor.map_comp_apply, ← op_comp, Iso.hom_inv_id, op_id, Functor.map_id_apply,
      ← Functor.map_comp_apply, ← op_comp, Iso.hom_inv_id, op_id,
      Functor.map_id_apply] at hfin
  · -- surjectivity
    rintro ⟨⟨p1, p2⟩, hp⟩
    set σA := (d.eqv (yChartInclA a Y).baseHom).symm
      (P.map (EllObj.isoPullbackAlong (yChartInclA a Y)).inv.op p1) with hσA
    set σB := (d.eqv (yChartInclB b Y).baseHom).symm
      (P.map (EllObj.isoPullbackAlong (yChartInclB b Y)).inv.op p2) with hσB
    have hp1 : p1 = P.map (EllObj.isoPullbackAlong (yChartInclA a Y)).hom.op
        (d.eqv (yChartInclA a Y).baseHom σA) := by
      rw [hσA, Equiv.apply_symm_apply, ← Functor.map_comp_apply, ← op_comp,
        Iso.hom_inv_id, op_id, Functor.map_id_apply]
    have hp2 : p2 = P.map (EllObj.isoPullbackAlong (yChartInclB b Y)).hom.op
        (d.eqv (yChartInclB b Y).baseHom σB) := by
      rw [hσB, Equiv.apply_symm_apply, ← Functor.map_comp_apply, ← op_comp,
        Iso.hom_inv_id, op_id, Functor.map_id_apply]
    -- the classifying sections agree on the overlap chart
    have hagree : yOverlapBaseA a b Y ≫ σA.1 = yOverlapBaseB a b Y ≫ σB.1 := by
      have h0 := hp
      rw [hp1, hp2, map_yOverlapInclA_eqv a b Y d σA, map_yOverlapInclB_eqv a b Y d σB]
        at h0
      exact congrArg Subtype.val
        ((d.eqv (yChartInclAB a b Y).baseHom).injective
          (map_iso_op_injective (EllObj.isoPullbackAlong (yChartInclAB a b Y)) h0))
    -- glue the classifying sections along the base cover
    set secFun : ∀ i : Bool, (yBaseCover a b Y hab).X i ⟶ d.Z
      := fun i => i.casesOn σB.1 σA.1 with hsecFun
    have hcompat : ∀ i j : Bool,
        pullback.fst ((yBaseCover a b Y hab).f i) ((yBaseCover a b Y hab).f j) ≫ secFun i
          = pullback.snd ((yBaseCover a b Y hab).f i) ((yBaseCover a b Y hab).f j)
            ≫ secFun j := by
      intro i j
      cases i <;> cases j
      · show pullback.fst (pullback.fst Y.structMap (Spec.map (awayHom b)))
            (pullback.fst Y.structMap (Spec.map (awayHom b))) ≫ σB.1
          = pullback.snd _ _ ≫ σB.1
        rw [show pullback.fst (pullback.fst Y.structMap (Spec.map (awayHom b)))
              (pullback.fst Y.structMap (Spec.map (awayHom b)))
            = pullback.snd (pullback.fst Y.structMap (Spec.map (awayHom b)))
              (pullback.fst Y.structMap (Spec.map (awayHom b))) from
          (cancel_mono (pullback.fst Y.structMap (Spec.map (awayHom b)))).mp
            pullback.condition]
      · show pullback.fst (pullback.fst Y.structMap (Spec.map (awayHom b)))
            (pullback.fst Y.structMap (Spec.map (awayHom a))) ≫ σB.1
          = pullback.snd _ _ ≫ σA.1
        have hdq1 : toOverlapBase a b Y _ (overlap_range_ba a b Y) ≫ yOverlapBaseB a b Y
            = pullback.fst (pullback.fst Y.structMap (Spec.map (awayHom b)))
              (pullback.fst Y.structMap (Spec.map (awayHom a))) :=
          toOverlapBase_yOverlapBaseB a b Y _ _ _ rfl
        have hdq2 : toOverlapBase a b Y _ (overlap_range_ba a b Y) ≫ yOverlapBaseA a b Y
            = pullback.snd (pullback.fst Y.structMap (Spec.map (awayHom b)))
              (pullback.fst Y.structMap (Spec.map (awayHom a))) :=
          toOverlapBase_yOverlapBaseA a b Y _ _ _ pullback.condition.symm
        rw [← hdq1, ← hdq2, Category.assoc, Category.assoc, ← hagree]
      · show pullback.fst (pullback.fst Y.structMap (Spec.map (awayHom a)))
            (pullback.fst Y.structMap (Spec.map (awayHom b))) ≫ σA.1
          = pullback.snd _ _ ≫ σB.1
        have hdq1 : toOverlapBase a b Y _ (overlap_range_ab a b Y) ≫ yOverlapBaseA a b Y
            = pullback.fst (pullback.fst Y.structMap (Spec.map (awayHom a)))
              (pullback.fst Y.structMap (Spec.map (awayHom b))) :=
          toOverlapBase_yOverlapBaseA a b Y _ _ _ rfl
        have hdq2 : toOverlapBase a b Y _ (overlap_range_ab a b Y) ≫ yOverlapBaseB a b Y
            = pullback.snd (pullback.fst Y.structMap (Spec.map (awayHom a)))
              (pullback.fst Y.structMap (Spec.map (awayHom b))) :=
          toOverlapBase_yOverlapBaseB a b Y _ _ _ pullback.condition.symm
        rw [← hdq1, ← hdq2, Category.assoc, Category.assoc, hagree]
      · show pullback.fst (pullback.fst Y.structMap (Spec.map (awayHom a)))
            (pullback.fst Y.structMap (Spec.map (awayHom a))) ≫ σA.1
          = pullback.snd _ _ ≫ σA.1
        rw [show pullback.fst (pullback.fst Y.structMap (Spec.map (awayHom a)))
              (pullback.fst Y.structMap (Spec.map (awayHom a)))
            = pullback.snd (pullback.fst Y.structMap (Spec.map (awayHom a)))
              (pullback.fst Y.structMap (Spec.map (awayHom a))) from
          (cancel_mono (pullback.fst Y.structMap (Spec.map (awayHom a)))).mp
            pullback.condition]
    set σ := (yBaseCover a b Y hab).glueMorphisms secFun hcompat with hσdef
    have hresA : pullback.fst Y.structMap (Spec.map (awayHom a)) ≫ σ = σA.1 :=
      (yBaseCover a b Y hab).ι_glueMorphisms _ _ true
    have hresB : pullback.fst Y.structMap (Spec.map (awayHom b)) ≫ σ = σB.1 :=
      (yBaseCover a b Y hab).ι_glueMorphisms _ _ false
    have hσf : σ ≫ d.f = 𝟙 Y.base := by
      refine (yBaseCover a b Y hab).hom_ext _ _ fun i => ?_
      cases i
      · show pullback.fst Y.structMap (Spec.map (awayHom b)) ≫ σ ≫ d.f
          = pullback.fst Y.structMap (Spec.map (awayHom b)) ≫ 𝟙 Y.base
        rw [← Category.assoc, hresB, σB.2, yChartInclB_baseHom, Category.comp_id]
      · show pullback.fst Y.structMap (Spec.map (awayHom a)) ≫ σ ≫ d.f
          = pullback.fst Y.structMap (Spec.map (awayHom a)) ≫ 𝟙 Y.base
        rw [← Category.assoc, hresA, σA.2, yChartInclA_baseHom, Category.comp_id]
    refine ⟨P.map (EllObj.isoPullbackAlong (𝟙 Y)).hom.op (d.eqv (𝟙 Y.base) ⟨σ, hσf⟩), ?_⟩
    have hback : P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op
        (P.map (EllObj.isoPullbackAlong (𝟙 Y)).hom.op (d.eqv (𝟙 Y.base) ⟨σ, hσf⟩))
        = d.eqv (𝟙 Y.base) ⟨σ, hσf⟩ := by
      rw [← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id, op_id, Functor.map_id_apply]
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show P.map (yChartInclA a Y).op
          (P.map (EllObj.isoPullbackAlong (𝟙 Y)).hom.op (d.eqv (𝟙 Y.base) ⟨σ, hσf⟩)) = p1
      rw [map_yChartInclA_eqv a Y d, hback]
      rw [show ((d.eqv (𝟙 Y.base)).symm (d.eqv (𝟙 Y.base) ⟨σ, hσf⟩)) = ⟨σ, hσf⟩ from
        Equiv.symm_apply_apply _ _]
      rw [hp1]
      refine congrArg _ (congrArg _ (Subtype.ext ?_))
      show (yChartInclA a Y).baseHom ≫ σ = σA.1
      have hresA' := hresA
      rw [← yChartInclA_baseHom a Y] at hresA'
      exact hresA'
    · show P.map (yChartInclB b Y).op
          (P.map (EllObj.isoPullbackAlong (𝟙 Y)).hom.op (d.eqv (𝟙 Y.base) ⟨σ, hσf⟩)) = p2
      rw [map_yChartInclB_eqv b Y d, hback]
      rw [show ((d.eqv (𝟙 Y.base)).symm (d.eqv (𝟙 Y.base) ⟨σ, hσf⟩)) = ⟨σ, hσf⟩ from
        Equiv.symm_apply_apply _ _]
      rw [hp2]
      refine congrArg _ (congrArg _ (Subtype.ext ?_))
      show (yChartInclB b Y).baseHom ≫ σ = σB.1
      have hresB' := hresB
      rw [← yChartInclB_baseHom b Y] at hresB'
      exact hresB'

/-- **[R-sheaf-P]** `P` is a two-chart Zariski sheaf: the `zglue` datum, from relative
representability alone. -/
private noncomputable def zariskiSheaf_of_relativelyRepresentable
    (hab : ∃ x y : R, x * a + y * b = 1) (hrel : P.RelativelyRepresentable) :
    ZariskiSheaf P a b where
  equiv Y := Equiv.ofBijective (zariskiSheafRestrict a b Y)
    (zariskiSheafRestrict_bijective a b hab hrel Y)
  fst_eq _ _ := rfl
  snd_eq _ _ := rfl

end ZariskiSheafConstruction

/-! ## [R-glue-repr] the glued object represents `P` -/

/-- **[R-glue-repr] — the YFULL Zariski-descent leaf (quarantined; `sorry`).**

`glueEllObj a b Xa Xb (overlapIso …)` represents `P`, completing KM Cor. 4.7.1. This is the one
genuinely global step: Zariski descent of the moduli functor along the cover
`Spec R = D(a) ∪ D(b)` pulled back to each test object `Y : Ell/R`. Every *engine* input it
consumes is already proven above; the gap is the descent bookkeeping (NEW-Y1's `YFULL` lane).

*Recipe.* Produce `homEquiv {Y} : (Y ⟶ glueEllObj …) ≃ P.obj (op Y)`, natural in `Y`. Cover
`Y.base` by `Ya := Y.structMap ⁻¹ᵁ (Spec.map (awayHom a)).opensRange` and `Yb` likewise; their
union is `⊤` since `Y.structMap` lands in `Spec R = D(a) ∪ D(b)`
(`basicOpen_sup_basicOpen_eq_top a b hab`).

* **`P` is a Zariski sheaf on `Ell/R` — the crux, and the sole role of `hrel`.** By `hrel`, for
  every `X : Ell/R`, `P.obj (op X) ≃ {sections of the relative representing scheme `Z_X ⟶ X.base`}`
  (`hrel X` at `g = 𝟙 X.base`, via `X.pullbackAlong (𝟙 _) ≅ X`). Sections of a scheme over
  `X.base` form a Zariski sheaf, so `P` glues and is separated along open covers of the base. This
  is exactly what fails for the `𝔽₄ × 𝔽₉` counterexample (a bare presheaf is not a sheaf).

* **Backward `P.obj (op Y) → (Y ⟶ glueEllObj)`.** Restrict `s : P(Y)` along the open immersions
  `Ya.ι, Yb.ι` (functoriality of `P`) to `s_a, s_b`. Over `Ya` the restricted object factors
  through `Spec R[1/a]`, so `s_a ∈ (P.baseChange (awayHom a)) (…)`; `repr_a.homEquiv.symm` turns it
  into a morphism into `Xa` and `glueJa` post-composes to `Y|_{Ya} ⟶ glueEllObj`; symmetrically on
  `Yb`. The two agree over `Y|_{Yab}` because `overlapIso` is *the* comparison of the two
  representations over `D(ab)` (`representableBy_baseChangeRing` + uniqueness). Glue into
  `Y ⟶ glueEllObj` by the pushout universal properties of `glueBase`/`glueTotal`
  (`glueBase_hom_ext`, `pushout.desc`; morphisms into a glued scheme form a Zariski sheaf).

* **Forward `(Y ⟶ glueEllObj) → P.obj (op Y)`.** Restrict `u` over `Ya` (it lands in the `a`-chart
  `glueBaseInl`), pull back through the cartesian chart square `isPullback_glueTotalInl` to a
  morphism into `Xa`, apply `repr_a.homEquiv` to land in `P(Y|_{Ya})`; symmetrically on `Yb`; glue
  by the sheaf property of `P`.

* **`left_inv`/`right_inv`/`homEquiv_comp`.** Both round-trips reduce chart-by-chart to the
  `left_inv`/`right_inv` of `repr_a`/`repr_b` and `baseChangeRingHomEquiv`, then to separatedness of
  the two sheaves; naturality is chart-wise `repr_a.homEquiv_comp`/`repr_b.homEquiv_comp`.

Sub-leaves for a future worker: `[R-sheaf-P]` (`hrel ⟹ P` is a Zariski sheaf), `[R-hom-glue]`
(Hom into `glueEllObj` is a sheaf, from the two pushouts), `[R-chart-eqv]` (the per-chart bijection
via `repr_a`/`glueJa`).

**Status (this session).** All *geometry* inputs are now sorry-free: `glueEllObj` is a genuine
`EllObj R` (the last geometry leaf `glue_locallyWeierstrass` is discharged via `lw_chart_transport`),
so this `def` no longer depends on any geometry `sorry` — only on the descent bookkeeping below.

**Sharpened on-ramp for `[R-sheaf-P]` (the crux).** The separated + gluing halves of "`P` is an
fppf sheaf for a relatively representable `P`" are already proven, sorry-free, in
`Moduli/Stack.lean`: `moduliProblem_fppf_separated` and `moduliProblem_fppf_descent` (they consume
exactly the `RelativelyRepresentable` naturality clause + "fppf covers are effective epis"). A
Zariski two-chart open cover `Y.base = Ya ∪ Yb` is the fppf cover `Ya ⊔ Yb ⟶ Y.base` (open
immersions are flat + LFP; joint surjectivity from `basicOpen_sup_basicOpen_eq_top` gives
surjectivity of the coproduct map), and `P(X.pullbackAlong (Ya ⊔ Yb → Y.base)) ≃ P(Y|Ya) × P(Y|Yb)`
(Hom out of a coproduct); the kernel pair `(Ya ⊔ Yb) ×_Y (Ya ⊔ Yb)` restricts the cocycle to
agreement over `Yab = Ya ∩ Yb`. So `[R-sheaf-P]` is now an *assembly* of the two `Stack.lean`
lemmas, not a from-scratch sheaf development.

**Remaining genuinely-new work (register-box-class, NEW-Y1's `YFULL` lane — do not duplicate).**
`[R-hom-glue]` (gluing an `Ell/R`-morphism `Y ⟶ glueEllObj` — its `baseHom`, `top`, cartesian
`isPullback`, and `zero_w` — from the two chart morphisms via the `glueBase`/`glueTotal` pushout
universal properties `glueBase_hom_ext`/`pushout.desc`), `[R-chart-eqv]` (per-chart bijection: factor
`Y|Ya`'s structure through `Spec R[1/a]`, pass `P(Y|Ya) ≃ (P.baseChange (awayHom a))(…)` through the
`restrictScalars`/`baseChange` adjunction, then `repr_a.homEquiv` + `glueJa`, matched on `Yab` by
`overlapIso`), and assembling the `Equiv` + `homEquiv_comp` naturality. This remains the single
`sorry` and is a multi-session development overlapping NEW-Y1's active curve-assembly charter. -/
private noncomputable def glueEllObj_representableBy {P : ModuliProblem R} (a b : R)
    (hab : ∃ x y : R, x * a + y * b = 1) (hrel : P.RelativelyRepresentable)
    {Xa : EllObj (CommRingCat.of (Localization.Away a))}
    {Xb : EllObj (CommRingCat.of (Localization.Away b))}
    (repr_a : (P.baseChange (awayHom a)).RepresentableBy Xa)
    (repr_b : (P.baseChange (awayHom b)).RepresentableBy Xb) :
    P.RepresentableBy (glueEllObj a b Xa Xb (overlapIso a b repr_a repr_b)) :=
  glueEllObj_representableBy_of_zariskiGlue a b hab hrel repr_a repr_b
    (zariskiSheaf_of_relativelyRepresentable a b hab hrel)

/-! ## [T-E5f-main] the recollement theorem -/

/-- **[T-E5f] The Katz–Mazur recollement theorem (KM Cor. 4.7.1).**
Let `P` be a moduli problem over `R`, and let `a b : R` with `x·a + y·b = 1`, so that
`Spec R = D(a) ∪ D(b)` is a Zariski cover. If the base-changed problems `P.baseChange` to
`R[1/a]` and to `R[1/b]` are each representable, then `P` is representable.

This is the engine-side recollement consumed by the `Y(N)` curve assembly: it will be
instantiated at `(a, b) = (2, 3)`, with `P.baseChange (away 2)` represented by
`𝕸(𝒫,Legendre)/G` (over `ℤ[1/2]`) and `P.baseChange (away 3)` by `𝕸(𝒫,naive-3)/G`
(over `ℤ[1/3]`), glued over `ℤ[1/6]`.

**Proof decomposition** (KM Cor. 4.7.1; ticket `[T-E5f]`). Per the confirmed engine/assembly
seam (coordinator v10.155; charter line "FP4 builds engine application, NEW-Y1 builds curve
assembly"), the **engine** below is delivered in this file; the **assembly** ([R-glue-obj]/
[R-glue-repr]) is NEW-Y1's `Y(N)` curve assembly, built on these primitives.

* *[extract]* ✅ From `h_a`/`h_b`, `Xₐ := Functor.reprX (P.baseChange (awayHom a))` representing
  `P.baseChange (awayHom a)` (`Functor.representableBy`), likewise `X_b`. (In the proof body.)

* *[compat]* ✅ **Engine, delivered.** The localization tower `awayHom a ≫ awayProdHomLeft a b =
  awayHom (a*b) = awayHom b ≫ awayProdHomRight a b` (`awayHom_comp_awayProdHomLeft/Right`) plus
  `representableBy_baseChangeRing` (the base-change ⊣ restrict-scalars adjunction
  `baseChangeRingHomEquiv`) give the **overlap iso** `overlapIso a b repr_a repr_b :
  Xₐ.baseChangeRing (awayProdHomLeft a b) ≅ X_b.baseChangeRing (awayProdHomRight a b)` in
  `Ell/R[1/ab]` — the gluing datum over `D(ab)`. The overlap inclusions are open immersions
  (`isOpenImmersion_SpecMap_awayProdHomLeft/Right`).

* *[R-glue-obj]* ⟵ **NEW-Y1 curve assembly.** Glue `Xₐ.base` (over `D(a) ⊆ Spec R`) and
  `X_b.base` (over `D(b)`) along `D(ab)` via `overlapIso`'s base iso into a scheme over `Spec R`
  (`Scheme.GlueData`, 2 charts; `basicOpen_sup_basicOpen_eq_top` gives `D(a) ∪ D(b) = ⊤`), and
  glue the geometric curves likewise — the KEY INSIGHT (banked): glue the *geometric*
  `EllipticCurveGeom` (`E` via `Scheme.GlueData`, `π`, `zero`, Zariski-local `localModel`) and
  re-derive the group law via `EllipticCurveGeom.toEllipticCurve` (T-W7, now axiom-clean), so no
  group-scheme gluing is needed — producing `X_glued : EllObj R`.

* *[R-glue-repr]* ⟵ **NEW-Y1 curve assembly.** `X_glued` represents `P` via functor-of-points
  descent along the cover, using the local `repr_a`/`repr_b` and `overlapIso` on `D(ab)`.

* *[assemble]* `⟨X_glued, ⟨repr⟩⟩`.

**Status.** Engine ([extract]/[compat]) delivered and axiom-clean:
`baseChangeRingHomEquiv`, `representableBy_baseChangeRing`, `awayProdHomLeft/Right` (+ tower
compat), `overlapIso`, `isOpenImmersion_SpecMap_awayProdHomLeft/Right`. The remaining
[R-glue-obj]/[R-glue-repr] scheme-and-curve assembly is NEW-Y1's charter (`YFULL` curve
assembly, in progress: `[YF-SUBDIV-EQ]`/`[YF-COMAX]`/`[YF-⊆⊇]` scheme plumbing) — consumed here
as the single remaining gap, to avoid duplicating that lane's active work.

**B2 STATEMENT AMENDMENT (v10.326, logged in `b2_log.jsonl`).** The bare-presheaf form (no
hypothesis on `P` beyond the two localized representabilities) is REFUTABLE: over `R = ℤ`,
`a = 2`, `b = 3`, take `X₀` the mixed curve over `Spec (𝔽₄ × 𝔽₉)` and
`P := yoneda.obj X₀ × C` where `C(Y)` collapses to `PUnit` exactly when `2` or `3` is a unit
on `Γ(Y.base, ⊤)` and is `ULift Bool` otherwise — both localized base-changes are then
representable (by `representableBy_baseChangeRing` on the tautological representation), but
`P(X₀)` has two elements agreeing on the clopen cover `Spec 𝔽₄ ⊔ Spec 𝔽₉`, so `P` is not
representable: the inverse direction of [R-glue-repr] needs the gluing half of a Zariski-sheaf
condition, unavailable for a bare presheaf. KM Cor. 4.7.1's verbatim standing hypothesis is
"any *relatively representable* moduli problem 𝒫 …" — we restore exactly that clause as
`hrel`. Both intended consumers (`representable_iff`, `representable_iff_rigidNoeth`) carry
`AffineOverEll`, which supplies `hrel` via `AffineOverEll.relativelyRepresentable`;
localized instantiations transfer by `RelativelyRepresentable.baseChange`. -/
theorem representable_of_baseChange_cover (P : ModuliProblem R) (a b : R)
    (hab : ∃ x y : R, x * a + y * b = 1)
    (hrel : P.RelativelyRepresentable)
    (h_a : (P.baseChange (awayHom a)).Representable)
    (h_b : (P.baseChange (awayHom b)).Representable) :
    P.Representable := by
  classical
  -- [extract] the two representing objects over R[1/a] and R[1/b]
  haveI := h_a; haveI := h_b
  set Xa : EllObj (CommRingCat.of (Localization.Away a)) :=
    Functor.reprX (P.baseChange (awayHom a)) with hXa
  set Xb : EllObj (CommRingCat.of (Localization.Away b)) :=
    Functor.reprX (P.baseChange (awayHom b)) with hXb
  have repr_a : (P.baseChange (awayHom a)).RepresentableBy Xa :=
    Functor.representableBy _
  have repr_b : (P.baseChange (awayHom b)).RepresentableBy Xb :=
    Functor.representableBy _
  -- [compat]/[R-glue-obj] ✅ engine, delivered: `overlapIso` is the gluing datum over `D(ab)` and
  -- `glueEllObj a b Xa Xb (overlapIso …)` is the glued `Ell/R`-object (base/total pushouts of the
  -- open-immersion charts; `glue_smooth`/`glue_proper`/`glue_locallyWeierstrass` all proven, so
  -- `glueEllObj` is a genuine `EllObj R`).
  -- [R-glue-repr]/[assemble]: it represents `P` by Zariski descent along the cover (`hrel` supplies
  -- the sheaf condition that kills the bare-presheaf counterexample).
  exact (glueEllObj_representableBy a b hab hrel repr_a repr_b).isRepresentable


/-- **[Y0-AFF4] `∃`-affine-hom form of the recollement** (KM 8.1.1 print p. 224:
"(and so patches together)"): if both localized legs are representable by objects with
affine bases, the glued representing object over `R` has affine structure morphism —
`IsAffineHom` is Zariski-local on the target over `D(a) ∪ D(b) = Spec R`, and over each
piece the glued base restricts to the (affine) leg base. -/
theorem exists_representableBy_isAffineHom_of_baseChange_cover (P : ModuliProblem R)
    (a b : R) (hab : ∃ x y : R, x * a + y * b = 1)
    (hrel : P.RelativelyRepresentable)
    (h_a : ∃ Xa : EllObj (CommRingCat.of (Localization.Away a)),
      IsAffine Xa.base ∧ Nonempty ((P.baseChange (awayHom a)).RepresentableBy Xa))
    (h_b : ∃ Xb : EllObj (CommRingCat.of (Localization.Away b)),
      IsAffine Xb.base ∧ Nonempty ((P.baseChange (awayHom b)).RepresentableBy Xb)) :
    ∃ X : EllObj R, IsAffineHom X.structMap ∧ Nonempty (P.RepresentableBy X) := by
  sorry

end ModularCurves

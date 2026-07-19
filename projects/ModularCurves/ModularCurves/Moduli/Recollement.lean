/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.ProblemBaseChange
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
    P.RepresentableBy (glueEllObj a b Xa Xb (overlapIso a b repr_a repr_b)) := by
  sorry

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

end ModularCurves

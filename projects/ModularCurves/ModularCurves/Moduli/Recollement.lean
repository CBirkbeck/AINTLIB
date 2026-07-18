/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.ProblemBaseChange
import Mathlib.RingTheory.Spectrum.Prime.Topology

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
  -- [compat] ✅ engine: the gluing datum over `D(ab)` is the overlap iso in `Ell/R[1/ab]`.
  have hcover : PrimeSpectrum.basicOpen a ⊔ PrimeSpectrum.basicOpen b = ⊤ :=
    basicOpen_sup_basicOpen_eq_top a b hab
  let _glue_datum : Xa.baseChangeRing (awayProdHomLeft a b) ≅ Xb.baseChangeRing (awayProdHomRight a b) :=
    overlapIso a b repr_a repr_b
  -- [R-glue-obj]/[R-glue-repr]/[assemble] ⟵ NEW-Y1 curve assembly (YFULL): glue `Xa`, `Xb` over
  -- `Spec R = D(a) ∪ D(b)` into `X_glued : EllObj R` (via `_glue_datum` + the open-immersion
  -- inclusions) and show it represents `P` by functor-of-points descent along the cover.
  sorry

end ModularCurves

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.QuotientProblem

/-!
# Products of moduli problems

**[T-YR-6-APP (P1)]** The pointwise product of two moduli problems, and the fact that
it is represented by the total space of a relative representation of the second
problem over a representing object of the first: "a point of `Z` = a point of `X`
(i.e. a `P`-datum) together with a `Q`-datum on the curve it classifies".

This is the tool that identifies the two orders of "add a ρ-level structure" and
"add a Legendre datum" for the `Y(ρ̄)` smoothness leaf.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace ModularCurves

namespace ModuliProblem

variable {R : CommRingCat.{u}}

/-- The pointwise product of two moduli problems. -/
def prod (P Q : ModuliProblem R) : ModuliProblem R where
  obj X := P.obj X × Q.obj X
  map {X Y} f := ↾fun a => (P.map f a.1, Q.map f a.2)
  map_id X := by
    ext a
    · simp only [FunctorToTypes.map_id_apply]
      rfl
    · simp only [FunctorToTypes.map_id_apply]
      rfl
  map_comp f g := by
    ext a
    · simp only [FunctorToTypes.map_comp_apply]
      rfl
    · simp only [FunctorToTypes.map_comp_apply]
      rfl

@[simp] lemma prod_map_apply (P Q : ModuliProblem R) {X Y : (EllObj R)ᵒᵖ} (f : X ⟶ Y)
    (a : P.obj X × Q.obj X) :
    (P.prod Q).map f a = (P.map f a.1, Q.map f a.2) := rfl

/-- The product of moduli problems is symmetric. -/
def prodComm (P Q : ModuliProblem R) : P.prod Q ≅ Q.prod P where
  hom := { app := fun _ => ↾fun a => (a.2, a.1) }
  inv := { app := fun _ => ↾fun a => (a.2, a.1) }

section Prod

variable {P Q : ModuliProblem R} {X : EllObj R} (r : P.RepresentableBy X)
  {Z : Scheme.{u}} (f : Z ⟶ X.base)
  (eqv : ∀ {T : Scheme.{u}} (g : T ⟶ X.base),
    { h : T ⟶ Z // h ≫ f = g } ≃ Q.obj (op (X.pullbackAlong g)))

/-- (Implementation) The `Q`-datum attached to a classifying morphism together with a
factorization of its base map through `Z`. -/
def prodSndOf {W : EllObj R} (v : W ⟶ X) (h : W.base ⟶ Z) (hh : h ≫ f = v.baseHom) :
    Q.obj (op W) :=
  Q.map (EllObj.toPullbackAlong v).op (eqv v.baseHom ⟨h, hh⟩)

theorem prodSndOf_congr {W : EllObj R} {v v' : W ⟶ X} (e : v = v') (h : W.base ⟶ Z)
    (hh : h ≫ f = v.baseHom) (hh' : h ≫ f = v'.baseHom) :
    prodSndOf f eqv v h hh = prodSndOf f eqv v' h hh' := by
  subst e; rfl

theorem prodSndOf_congr_hom {W : EllObj R} (v : W ⟶ X) {h h' : W.base ⟶ Z}
    (e : h = h') (hh : h ≫ f = v.baseHom) (hh' : h' ≫ f = v.baseHom) :
    prodSndOf f eqv v h hh = prodSndOf f eqv v h' hh' := by
  subst e; rfl

/-- (Implementation) The `Q`-datum attached to a morphism into the total space. -/
def prodSnd {W : EllObj R} (u : W ⟶ X.pullbackAlong f) : Q.obj (op W) :=
  prodSndOf f eqv (u ≫ X.pullbackAlongπ f) u.baseHom rfl

/-- (Implementation) The morphism into the total space attached to a classifying
morphism together with a `Q`-datum. -/
def prodHomOf {W : EllObj R} (v : W ⟶ X) (q : Q.obj (op W)) :
    W ⟶ X.pullbackAlong f :=
  EllObj.homToPullbackAlong v
    ((eqv v.baseHom).symm (Q.map (EllObj.isoPullbackAlong v).inv.op q)).1
    ((eqv v.baseHom).symm (Q.map (EllObj.isoPullbackAlong v).inv.op q)).2

/-- (Implementation) The morphism into the total space attached to a pair. -/
def prodHom {W : EllObj R} (a : P.obj (op W) × Q.obj (op W)) :
    W ⟶ X.pullbackAlong f :=
  prodHomOf f eqv (r.homEquiv.symm a.1) a.2

/-- (Implementation) `homToPullbackAlong` only depends on the base factorization. -/
theorem homToPullbackAlong_congr_hom {Y X' : EllObj R} {T : Scheme.{u}}
    {g : T ⟶ X'.base} (u : Y ⟶ X') {h h' : Y.base ⟶ T}
    (hh : h ≫ g = u.baseHom) (hh' : h' ≫ g = u.baseHom) (e : h = h') :
    EllObj.homToPullbackAlong u h hh = EllObj.homToPullbackAlong u h' hh' := by
  subst e; rfl

/-- (Implementation) A morphism into the total space is determined by its base map and
its composite with the tautological projection. -/
theorem homToPullbackAlong_self {W : EllObj R} (u : W ⟶ X.pullbackAlong f) :
    EllObj.homToPullbackAlong (u ≫ X.pullbackAlongπ f) u.baseHom rfl = u := by
  refine EllHom.ext rfl ?_
  show Limits.pullback.lift (u ≫ X.pullbackAlongπ f).top
    (W.curve.π ≫ u.baseHom) _ = u.top
  apply Limits.pullback.hom_ext
  · rw [Limits.pullback.lift_fst]
    rfl
  · rw [Limits.pullback.lift_snd]
    exact u.isPullback.w.symm

/-- (Implementation) The first roundtrip. -/
theorem prodHom_pair {W : EllObj R} (u : W ⟶ X.pullbackAlong f) :
    prodHom r f eqv (r.homEquiv (u ≫ X.pullbackAlongπ f), prodSnd f eqv u) = u := by
  have hq : Q.map (EllObj.isoPullbackAlong (u ≫ X.pullbackAlongπ f)).inv.op
      (prodSnd f eqv u) =
        eqv (u ≫ X.pullbackAlongπ f).baseHom ⟨u.baseHom, rfl⟩ := by
    rw [prodSnd, prodSndOf, ← FunctorToTypes.map_comp_apply, ← op_comp]
    rw [show (EllObj.isoPullbackAlong (u ≫ X.pullbackAlongπ f)).inv ≫
      EllObj.toPullbackAlong (u ≫ X.pullbackAlongπ f) = 𝟙 _ from
      (EllObj.isoPullbackAlong (u ≫ X.pullbackAlongπ f)).inv_hom_id]
    simp
  rw [prodHom, Equiv.symm_apply_apply]
  show EllObj.homToPullbackAlong (u ≫ X.pullbackAlongπ f)
      ((eqv (u ≫ X.pullbackAlongπ f).baseHom).symm
        (Q.map (EllObj.isoPullbackAlong (u ≫ X.pullbackAlongπ f)).inv.op
          (prodSnd f eqv u))).1 _ = u
  simp only [hq]
  have hsub : ((eqv (u.baseHom ≫ f)).symm ((eqv (u.baseHom ≫ f))
      ⟨u.baseHom, rfl⟩)) = ⟨u.baseHom, rfl⟩ := Equiv.symm_apply_apply _ _
  have hfst : (((eqv (u.baseHom ≫ f)).symm ((eqv (u.baseHom ≫ f))
      ⟨u.baseHom, rfl⟩)) : W.base ⟶ Z) = u.baseHom := congrArg Subtype.val hsub
  show EllObj.homToPullbackAlong (u ≫ X.pullbackAlongπ f)
      (((eqv (u.baseHom ≫ f)).symm ((eqv (u.baseHom ≫ f)) ⟨u.baseHom, rfl⟩)) :
        W.base ⟶ Z) _ = u
  refine (homToPullbackAlong_congr_hom (u ≫ X.pullbackAlongπ f) _ rfl hfst).trans ?_
  exact homToPullbackAlong_self f u

/-- (Implementation) The second roundtrip, first component: the classifying morphism
of the assembled point is the one we started from. -/
theorem prodHom_fst {W : EllObj R} (a : P.obj (op W) × Q.obj (op W)) :
    prodHom r f eqv a ≫ X.pullbackAlongπ f = r.homEquiv.symm a.1 := by
  rw [prodHom, prodHomOf]
  exact EllObj.homToPullbackAlong_pullbackAlongπ _ _ _

/-- (Implementation) The base map of the assembled point is the chosen factorization. -/
theorem prodHom_baseHom {W : EllObj R} (v : W ⟶ X) (q : Q.obj (op W)) :
    (prodHomOf f eqv v q).baseHom =
      ((eqv v.baseHom).symm (Q.map (EllObj.isoPullbackAlong v).inv.op q)).1 := by
  rw [prodHomOf]
  exact EllObj.homToPullbackAlong_baseHom _ _ _

/-- **[T-YR-6-APP P1, remaining step]** The second roundtrip's `Q`-component.
The proof is the mirror of `prodHom_pair`: rewrite the tautological projection through
`prodHom_fst`, identify the `eqv`-index via `prodHom_baseHom`, and cancel
`isoPullbackAlong`. -/
theorem prodSnd_prodHomOf {W : EllObj R} (v : W ⟶ X) (q : Q.obj (op W)) :
    prodSnd f eqv (prodHomOf f eqv v q) = q := by
  set w := (eqv v.baseHom).symm (Q.map (EllObj.isoPullbackAlong v).inv.op q) with hw
  have hb : (prodHomOf f eqv v q).baseHom = w.1 :=
    EllObj.homToPullbackAlong_baseHom _ _ _
  have hπ : prodHomOf f eqv v q ≫ X.pullbackAlongπ f = v := by
    rw [prodHomOf]
    exact EllObj.homToPullbackAlong_pullbackAlongπ _ _ _
  rw [prodSnd, prodSndOf_congr f eqv hπ _ rfl (hb ▸ w.2),
    prodSndOf_congr_hom f eqv v hb (hb ▸ w.2) w.2, prodSndOf, hw,
    Equiv.apply_symm_apply, ← FunctorToTypes.map_comp_apply, ← op_comp,
    show EllObj.toPullbackAlong v ≫ (EllObj.isoPullbackAlong v).inv = 𝟙 _ from
      (EllObj.isoPullbackAlong v).hom_inv_id]
  simp

/-- (Implementation) Naturality of the comparison morphism in the source. -/
theorem toPullbackAlong_comp_pullbackAlongMap {W W' : EllObj R} (k : W ⟶ W')
    (v : W' ⟶ X) :
    EllObj.toPullbackAlong (k ≫ v) ≫ X.pullbackAlongMap v.baseHom k.baseHom =
      k ≫ EllObj.toPullbackAlong v := by
  refine EllHom.ext ?_ ?_
  · show 𝟙 W.base ≫ k.baseHom = k.baseHom ≫ 𝟙 W'.base
    rw [Category.id_comp, Category.comp_id]
  · apply Limits.pullback.hom_ext
    · show ((k ≫ v).isPullback.isoPullback.hom ≫
        Limits.pullback.map X.curve.π (k.baseHom ≫ v.baseHom) X.curve.π v.baseHom
          (𝟙 X.curve.E) k.baseHom (𝟙 X.base) (by simp) (by simp)) ≫
          Limits.pullback.fst X.curve.π v.baseHom =
        (k.top ≫ v.isPullback.isoPullback.hom) ≫
          Limits.pullback.fst X.curve.π v.baseHom
      rw [Category.assoc, Limits.pullback.lift_fst, Category.comp_id,
        Category.assoc, v.isPullback.isoPullback_hom_fst]
      exact (k ≫ v).isPullback.isoPullback_hom_fst
    · show ((k ≫ v).isPullback.isoPullback.hom ≫
        Limits.pullback.map X.curve.π (k.baseHom ≫ v.baseHom) X.curve.π v.baseHom
          (𝟙 X.curve.E) k.baseHom (𝟙 X.base) (by simp) (by simp)) ≫
          Limits.pullback.snd X.curve.π v.baseHom =
        (k.top ≫ v.isPullback.isoPullback.hom) ≫
          Limits.pullback.snd X.curve.π v.baseHom
      have h1 : (k ≫ v).isPullback.isoPullback.hom ≫
          Limits.pullback.snd X.curve.π (k.baseHom ≫ v.baseHom) = W.curve.π :=
        (k ≫ v).isPullback.isoPullback_hom_snd
      rw [Category.assoc, Limits.pullback.lift_snd, ← Category.assoc, h1,
        Category.assoc, v.isPullback.isoPullback_hom_snd]
      exact k.isPullback.w.symm

variable (nat : ∀ {T T' : Scheme.{u}} (g : T ⟶ X.base) (k : T' ⟶ T)
  (h : { h : T ⟶ Z // h ≫ f = g }),
  eqv (k ≫ g) ⟨k ≫ h.1, by rw [Category.assoc, h.2]⟩ =
    Q.map (X.pullbackAlongMap g k).op (eqv g h))

/-- **[T-YR-6-APP P1]** The total space of a relative representation of `Q` over a
representing object of `P` represents the product problem `P.prod Q`. -/
noncomputable def representableByProd :
    (P.prod Q).RepresentableBy (X.pullbackAlong f) where
  homEquiv {W} :=
    { toFun := fun u => (r.homEquiv (u ≫ X.pullbackAlongπ f), prodSnd f eqv u)
      invFun := fun a => prodHom r f eqv a
      left_inv := fun u => prodHom_pair r f eqv u
      right_inv := fun a => by
        refine Prod.ext ?_ ?_
        · show r.homEquiv (prodHom r f eqv a ≫ X.pullbackAlongπ f) = a.1
          rw [prodHom_fst, Equiv.apply_symm_apply]
        · show prodSnd f eqv (prodHom r f eqv a) = a.2
          rw [prodHom]
          exact prodSnd_prodHomOf f eqv _ _ }
  homEquiv_comp {W W'} k u := by
    refine Prod.ext ?_ ?_
    · show r.homEquiv ((k ≫ u) ≫ X.pullbackAlongπ f) =
        P.map k.op (r.homEquiv (u ≫ X.pullbackAlongπ f))
      rw [Category.assoc, r.homEquiv_comp]
    · show prodSnd f eqv (k ≫ u) = Q.map k.op (prodSnd f eqv u)
      have h2 : (k ≫ u).baseHom ≫ f = (k ≫ u ≫ X.pullbackAlongπ f).baseHom :=
        Category.assoc k.baseHom u.baseHom f
      have hnat := nat (u ≫ X.pullbackAlongπ f).baseHom k.baseHom
        (⟨u.baseHom, rfl⟩ : { h : W'.base ⟶ Z // h ≫ f = u.baseHom ≫ f })
      conv_lhs =>
        rw [prodSnd, prodSndOf_congr f eqv (Category.assoc k u (X.pullbackAlongπ f))
          (k ≫ u).baseHom rfl h2]
      rw [prodSndOf, prodSnd, prodSndOf]
      show Q.map (EllObj.toPullbackAlong (k ≫ u ≫ X.pullbackAlongπ f)).op
          (eqv (k.baseHom ≫ (u ≫ X.pullbackAlongπ f).baseHom)
            ⟨k.baseHom ≫ u.baseHom, _⟩) =
        Q.map k.op (Q.map (EllObj.toPullbackAlong (u ≫ X.pullbackAlongπ f)).op
          (eqv (u ≫ X.pullbackAlongπ f).baseHom ⟨u.baseHom, rfl⟩))
      rw [hnat, ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply,
        ← op_comp, ← op_comp,
        toPullbackAlong_comp_pullbackAlongMap k (u ≫ X.pullbackAlongπ f)]
      rfl

end Prod

end ModuliProblem

end ModularCurves

end

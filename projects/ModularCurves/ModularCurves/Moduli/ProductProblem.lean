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

section Prod

variable {P Q : ModuliProblem R} {X : EllObj R} (r : P.RepresentableBy X)
  {Z : Scheme.{u}} (f : Z ⟶ X.base)
  (eqv : ∀ {T : Scheme.{u}} (g : T ⟶ X.base),
    { h : T ⟶ Z // h ≫ f = g } ≃ Q.obj (op (X.pullbackAlong g)))

/-- (Implementation) The `Q`-datum attached to a morphism into the total space. -/
def prodSnd {W : EllObj R} (u : W ⟶ X.pullbackAlong f) : Q.obj (op W) :=
  Q.map (EllObj.toPullbackAlong (u ≫ X.pullbackAlongπ f)).op
    (eqv (u.baseHom ≫ f) ⟨u.baseHom, rfl⟩)

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
      (prodSnd f eqv u) = eqv (u.baseHom ≫ f) ⟨u.baseHom, rfl⟩ := by
    rw [prodSnd, ← FunctorToTypes.map_comp_apply, ← op_comp]
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

end Prod

end ModuliProblem

end ModularCurves

end

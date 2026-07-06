/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Ticket T-Q6 (quotients of rigidified moduli problems — the KM 4.7 ⇐ engine).
-/
import ModularCurves.Moduli.EllCategory

/-!
# The simultaneous moduli problem and the Katz–Mazur 4.7 engine (T-Q6)

Katz–Mazur prove `representable ⟺ relatively representable + rigid` (KM 4.7.0,
Loeffler Thm 3.7.4) by an axiomatized quotient argument (KM p. 112): for `δ` a
relatively representable moduli problem that is representable by an affine scheme
and on which a finite group `G` acts with `δ_{E/S}` a finite étale `G`-torsor, a
rigid relatively representable `𝒫` is represented by `𝕸(𝒫,δ)/G`, where `𝕸(𝒫,δ)`
represents the *simultaneous problem* `(𝒫,δ)`.

This file develops the engine's formal layer:

* `ModuliProblem.simul` — the simultaneous problem `(𝒫,δ)` as a pointwise-product
  presheaf (KM p. 112: "the simultaneous problem (𝒫,δ)").
* `EllObj.pullbackAlongπ` — the tautological cartesian projection
  `X ×_{X.base} T ⟶ X` over `g : T ⟶ X.base`.
* `EllObj.isoPullbackAlong` — **every `Ell/R`-morphism is cartesian**: the
  comparison isomorphism `Y ≅ X.pullbackAlong u.baseHom` induced by `u : Y ⟶ X`.
* `ModuliProblem.simul_representable` — KM 4.7 step (i): if `δ` is representable
  and `𝒫` is relatively representable, the simultaneous problem is representable,
  by `𝕸(𝒫,δ) = 𝒫_{E/𝕸(δ)}` (T-Q6c).

The group action, freeness-from-rigidity, and the quotient assembly are the
subsequent T-Q6 leaves; the étale-torsor input is `ForMathlib/InvariantTorsor.lean`
(T-Q2, SGA III Exp. V 4.1) and the affine quotient is
`ForMathlib/AffineQuotient.lean` (T-Q3).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace ModularCurves

variable {R : CommRingCat.{u}}

namespace EllObj

/-- The tautological cartesian projection `X ×_{X.base} T ⟶ X` in `Ell/R`
lying over `g : T ⟶ X.base`. -/
noncomputable def pullbackAlongπ (X : EllObj R) {T : Scheme.{u}}
    (g : T ⟶ X.base) : X.pullbackAlong g ⟶ X where
  baseHom := g
  base_w := rfl
  top := pullback.fst X.curve.π g
  isPullback := IsPullback.of_hasPullback X.curve.π g
  zero_w := pullback.lift_fst _ _ _

@[simp]
theorem pullbackAlongπ_baseHom (X : EllObj R) {T : Scheme.{u}}
    (g : T ⟶ X.base) : (X.pullbackAlongπ g).baseHom = g := rfl

/-- The comparison morphism `Y ⟶ X.pullbackAlong u.baseHom` induced by an
`Ell/R`-morphism `u : Y ⟶ X` (the canonical map to the chosen pullback). -/
noncomputable def toPullbackAlong {Y X : EllObj R} (u : Y ⟶ X) :
    Y ⟶ X.pullbackAlong u.baseHom where
  baseHom := 𝟙 Y.base
  base_w := by
    show 𝟙 Y.base ≫ u.baseHom ≫ X.structMap = Y.structMap
    rw [Category.id_comp, u.base_w]
  top := u.isPullback.isoPullback.hom
  isPullback :=
    IsPullback.of_horiz_isIso (fst := u.isPullback.isoPullback.hom)
      (g := 𝟙 Y.base)
      ⟨by
        show u.isPullback.isoPullback.hom ≫ pullback.snd X.curve.π u.baseHom =
          Y.curve.π ≫ 𝟙 Y.base
        rw [u.isPullback.isoPullback_hom_snd, Category.comp_id]⟩
  zero_w := by
    apply pullback.hom_ext
    · show Y.curve.zero ≫ u.isPullback.isoPullback.hom ≫
          pullback.fst X.curve.π u.baseHom =
        (𝟙 Y.base ≫ pullback.lift (u.baseHom ≫ X.curve.zero) (𝟙 Y.base) _) ≫
          pullback.fst X.curve.π u.baseHom
      rw [u.isPullback.isoPullback_hom_fst, Category.id_comp, pullback.lift_fst,
        u.zero_w]
    · show Y.curve.zero ≫ u.isPullback.isoPullback.hom ≫
          pullback.snd X.curve.π u.baseHom =
        (𝟙 Y.base ≫ pullback.lift (u.baseHom ≫ X.curve.zero) (𝟙 Y.base) _) ≫
          pullback.snd X.curve.π u.baseHom
      rw [u.isPullback.isoPullback_hom_snd, Category.id_comp, pullback.lift_snd,
        Y.curve.zero_π]

@[simp]
theorem toPullbackAlong_baseHom {Y X : EllObj R} (u : Y ⟶ X) :
    (toPullbackAlong u).baseHom = 𝟙 Y.base := rfl

/-- The comparison morphism composed with the tautological projection recovers the
original morphism: `toPullbackAlong u ≫ pullbackAlongπ = u`. -/
@[reassoc (attr := simp)]
theorem toPullbackAlong_pullbackAlongπ {Y X : EllObj R} (u : Y ⟶ X) :
    toPullbackAlong u ≫ X.pullbackAlongπ u.baseHom = u := by
  refine EllHom.ext ?_ ?_
  · show 𝟙 Y.base ≫ u.baseHom = u.baseHom
    rw [Category.id_comp]
  · show u.isPullback.isoPullback.hom ≫ pullback.fst X.curve.π u.baseHom = u.top
    exact u.isPullback.isoPullback_hom_fst

/-- **Every `Ell/R`-morphism is cartesian**: the comparison isomorphism
`Y ≅ X.pullbackAlong u.baseHom` induced by `u : Y ⟶ X`. Loeffler Def 3.7.1's
"morphisms are squares where `E ≅ E' ×_T S`", packaged as an iso onto the chosen
pullback. -/
noncomputable def isoPullbackAlong {Y X : EllObj R} (u : Y ⟶ X) :
    Y ≅ X.pullbackAlong u.baseHom where
  hom := toPullbackAlong u
  inv :=
    { baseHom := 𝟙 Y.base
      base_w := by
        show 𝟙 Y.base ≫ Y.structMap = u.baseHom ≫ X.structMap
        rw [Category.id_comp, u.base_w]
      top := u.isPullback.isoPullback.inv
      isPullback :=
        IsPullback.of_horiz_isIso (fst := u.isPullback.isoPullback.inv)
          (g := 𝟙 Y.base)
          ⟨by
            show u.isPullback.isoPullback.inv ≫ Y.curve.π =
              pullback.snd X.curve.π u.baseHom ≫ 𝟙 Y.base
            rw [Category.comp_id, Iso.inv_comp_eq,
              u.isPullback.isoPullback_hom_snd]⟩
      zero_w := by
        rw [Iso.comp_inv_eq]
        show pullback.lift (u.baseHom ≫ X.curve.zero) (𝟙 Y.base) _ =
          𝟙 Y.base ≫ Y.curve.zero ≫ u.isPullback.isoPullback.hom
        rw [Category.id_comp]
        apply pullback.hom_ext
        · rw [pullback.lift_fst, Category.assoc, u.isPullback.isoPullback_hom_fst,
            u.zero_w]
        · rw [pullback.lift_snd, Category.assoc, u.isPullback.isoPullback_hom_snd,
            Y.curve.zero_π] }
  hom_inv_id := by
    refine EllHom.ext ?_ ?_
    · show 𝟙 Y.base ≫ 𝟙 Y.base = 𝟙 Y.base
      rw [Category.id_comp]
    · show u.isPullback.isoPullback.hom ≫ u.isPullback.isoPullback.inv = 𝟙 _
      exact u.isPullback.isoPullback.hom_inv_id
  inv_hom_id := by
    refine EllHom.ext ?_ ?_
    · show 𝟙 Y.base ≫ 𝟙 Y.base = 𝟙 _
      rw [Category.id_comp]
    · show u.isPullback.isoPullback.inv ≫ u.isPullback.isoPullback.hom = 𝟙 _
      exact u.isPullback.isoPullback.inv_hom_id

@[simp]
theorem isoPullbackAlong_hom {Y X : EllObj R} (u : Y ⟶ X) :
    (isoPullbackAlong u).hom = toPullbackAlong u := rfl

end EllObj

namespace ModuliProblem

/-- **The simultaneous moduli problem** `(𝒫,δ)` (KM p. 112): the pointwise product
presheaf, whose value on `E/S` is `𝒫(E/S) × δ(E/S)`. -/
def simul (P Q : ModuliProblem R) : ModuliProblem R where
  obj X := P.obj X × Q.obj X
  map f := ↾fun a => (P.map f a.1, Q.map f a.2)
  map_id X := by
    ext a
    · show P.map (𝟙 X) a.1 = a.1
      rw [Functor.map_id_apply]
    · show Q.map (𝟙 X) a.2 = a.2
      rw [Functor.map_id_apply]
  map_comp f g := by
    ext a
    · show P.map (f ≫ g) a.1 = P.map g (P.map f a.1)
      rw [Functor.map_comp_apply]
    · show Q.map (f ≫ g) a.2 = Q.map g (Q.map f a.2)
      rw [Functor.map_comp_apply]

@[simp]
theorem simul_obj (P Q : ModuliProblem R) (X : (EllObj R)ᵒᵖ) :
    (P.simul Q).obj X = (P.obj X × Q.obj X) := rfl

@[simp]
theorem simul_map (P Q : ModuliProblem R) {X Y : (EllObj R)ᵒᵖ} (f : X ⟶ Y)
    (a : (P.simul Q).obj X) :
    (P.simul Q).map f a = (P.map f a.1, Q.map f a.2) := rfl

end ModuliProblem

end ModularCurves

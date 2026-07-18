/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Ticket T-Q6 (quotients of rigidified moduli problems — the KM 4.7 ⇐ engine).
-/
import ModularCurves.Moduli.EllCategory
import ModularCurves.ForMathlib.RepresentableAut
import ModularCurves.ForMathlib.SchemeQuotient

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

/-- The morphism `Y ⟶ X.pullbackAlong g` assembled from `u : Y ⟶ X` and a base
factorization `h : Y.base ⟶ T` with `h ≫ g = u.baseHom` (the universal property
of the tautological cartesian square, map-in direction). -/
noncomputable def homToPullbackAlong {Y X : EllObj R} {T : Scheme.{u}}
    {g : T ⟶ X.base} (u : Y ⟶ X) (h : Y.base ⟶ T) (hh : h ≫ g = u.baseHom) :
    Y ⟶ X.pullbackAlong g where
  baseHom := h
  base_w := by
    show h ≫ g ≫ X.structMap = Y.structMap
    rw [← Category.assoc, hh, u.base_w]
  top := pullback.lift u.top (Y.curve.π ≫ h)
    (by rw [Category.assoc, hh]; exact u.isPullback.w)
  isPullback := by
    have hbig : IsPullback
        (pullback.lift u.top (Y.curve.π ≫ h)
          (by rw [Category.assoc, hh]; exact u.isPullback.w) ≫
            pullback.fst X.curve.π g)
        Y.curve.π X.curve.π (h ≫ g) := by
      rw [pullback.lift_fst, hh]
      exact u.isPullback
    exact IsPullback.of_right hbig (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback X.curve.π g)
  zero_w := by
    apply pullback.hom_ext
    · show Y.curve.zero ≫ pullback.lift u.top (Y.curve.π ≫ h) _ ≫
          pullback.fst X.curve.π g =
        (h ≫ pullback.lift (g ≫ X.curve.zero) (𝟙 T) _) ≫ pullback.fst X.curve.π g
      rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, u.zero_w,
        ← Category.assoc, hh]
    · show Y.curve.zero ≫ pullback.lift u.top (Y.curve.π ≫ h) _ ≫
          pullback.snd X.curve.π g =
        (h ≫ pullback.lift (g ≫ X.curve.zero) (𝟙 T) _) ≫ pullback.snd X.curve.π g
      rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id,
        ← Category.assoc, Y.curve.zero_π, Category.id_comp]

@[simp]
theorem homToPullbackAlong_baseHom {Y X : EllObj R} {T : Scheme.{u}}
    {g : T ⟶ X.base} (u : Y ⟶ X) (h : Y.base ⟶ T) (hh : h ≫ g = u.baseHom) :
    (homToPullbackAlong u h hh).baseHom = h := rfl

/-- Projecting the assembled morphism back to `X` recovers `u`. -/
@[reassoc (attr := simp)]
theorem homToPullbackAlong_pullbackAlongπ {Y X : EllObj R} {T : Scheme.{u}}
    {g : T ⟶ X.base} (u : Y ⟶ X) (h : Y.base ⟶ T) (hh : h ≫ g = u.baseHom) :
    homToPullbackAlong u h hh ≫ X.pullbackAlongπ g = u := by
  refine EllHom.ext ?_ ?_
  · show h ≫ g = u.baseHom
    exact hh
  · show pullback.lift u.top (Y.curve.π ≫ h) _ ≫ pullback.fst X.curve.π g = u.top
    exact pullback.lift_fst _ _ _

/-- **The universal property of the tautological cartesian square**: morphisms
`Y ⟶ X ×_{X.base} T` correspond to pairs `(u : Y ⟶ X, h : Y.base ⟶ T)` with
`h ≫ g = u.baseHom`. -/
noncomputable def homPullbackAlongEquiv (X : EllObj R) {T : Scheme.{u}}
    (g : T ⟶ X.base) (Y : EllObj R) :
    (Y ⟶ X.pullbackAlong g) ≃
      {p : (Y ⟶ X) × (Y.base ⟶ T) // p.2 ≫ g = p.1.baseHom} where
  toFun v := ⟨(v ≫ X.pullbackAlongπ g, v.baseHom), rfl⟩
  invFun p := homToPullbackAlong p.1.1 p.1.2 p.2
  left_inv v := by
    refine EllHom.ext ?_ ?_
    · rfl
    · exact pullback.hom_ext (pullback.lift_fst _ _ _)
        ((pullback.lift_snd _ _ _).trans v.isPullback.w.symm)
  right_inv p := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact homToPullbackAlong_pullbackAlongπ p.1.1 p.1.2 p.2
    · rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Decomposing a morphism into the tautological square over a composite base
map: `v : Y ⟶ X ×_{X.base} T` factors as the comparison of `v ≫ π` followed by
the base-change functoriality map. -/
theorem toPullbackAlong_pullbackAlongMap {Y X : EllObj R} {T : Scheme.{u}}
    {g : T ⟶ X.base} (v : Y ⟶ X.pullbackAlong g) :
    toPullbackAlong (v ≫ X.pullbackAlongπ g) ≫
      X.pullbackAlongMap g v.baseHom = v := by
  refine EllHom.ext ?_ ?_
  · show 𝟙 Y.base ≫ v.baseHom = v.baseHom
    rw [Category.id_comp]
  · apply pullback.hom_ext
    · show ((v ≫ X.pullbackAlongπ g).isPullback.isoPullback.hom ≫
          Limits.pullback.map X.curve.π (v.baseHom ≫ g) X.curve.π g
            (𝟙 X.curve.E) v.baseHom (𝟙 X.base) rfl rfl) ≫
            pullback.fst X.curve.π g = v.top ≫ pullback.fst X.curve.π g
      rw [Category.assoc]
      erw [pullback.lift_fst]
      rw [Category.comp_id]
      exact (v ≫ X.pullbackAlongπ g).isPullback.isoPullback_hom_fst
    · show ((v ≫ X.pullbackAlongπ g).isPullback.isoPullback.hom ≫
          Limits.pullback.map X.curve.π (v.baseHom ≫ g) X.curve.π g
            (𝟙 X.curve.E) v.baseHom (𝟙 X.base) rfl rfl) ≫
            pullback.snd X.curve.π g = v.top ≫ pullback.snd X.curve.π g
      rw [Category.assoc]
      erw [pullback.lift_snd]
      erw [(v ≫ X.pullbackAlongπ g).isPullback.isoPullback_hom_snd_assoc]
      exact v.isPullback.w.symm

set_option backward.isDefEq.respectTransparency.types false in
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

/-- **Two `Ell/R`-morphisms with equal base maps differ by an endomorphism over
the identity** (the connecting endomorphism; KM p. 113's `θ(g)`). -/
noncomputable def connectHom {V X : EllObj R} (v' v : V ⟶ X)
    (hb : v'.baseHom = v.baseHom) : V ⟶ V :=
  homToPullbackAlong v' (𝟙 V.base) (by rw [Category.id_comp, hb]) ≫
    (isoPullbackAlong v).inv

theorem connectHom_baseHom {V X : EllObj R} (v' v : V ⟶ X)
    (hb : v'.baseHom = v.baseHom) :
    (connectHom v' v hb).baseHom = 𝟙 V.base := by
  show 𝟙 V.base ≫ 𝟙 V.base = 𝟙 V.base
  rw [Category.id_comp]

/-- The defining property of the connecting endomorphism. -/
@[reassoc]
theorem connectHom_comp {V X : EllObj R} (v' v : V ⟶ X)
    (hb : v'.baseHom = v.baseHom) :
    connectHom v' v hb ≫ v = v' := by
  have h1 : (isoPullbackAlong v).inv ≫ v = X.pullbackAlongπ v.baseHom := by
    rw [Iso.inv_comp_eq]
    exact (toPullbackAlong_pullbackAlongπ v).symm
  rw [connectHom, Category.assoc, h1, homToPullbackAlong_pullbackAlongπ]

/-- An endomorphism over the identity fixing one morphism is the identity
(cartesianness makes `v` "relatively mono" over its base map). -/
theorem eq_id_of_baseHom_of_comp {V X : EllObj R} (v : V ⟶ X) (ξ : V ⟶ V)
    (h1 : ξ.baseHom = 𝟙 V.base) (h2 : ξ ≫ v = v) : ξ = 𝟙 V := by
  haveI : IsIso (toPullbackAlong v) :=
    inferInstanceAs (IsIso (isoPullbackAlong v).hom)
  have key : ξ ≫ toPullbackAlong v = toPullbackAlong v := by
    apply (homPullbackAlongEquiv X v.baseHom V).injective
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show (ξ ≫ toPullbackAlong v) ≫ X.pullbackAlongπ v.baseHom =
        toPullbackAlong v ≫ X.pullbackAlongπ v.baseHom
      rw [Category.assoc, toPullbackAlong_pullbackAlongπ, h2]
    · show ξ.baseHom ≫ 𝟙 V.base = 𝟙 V.base
      rw [Category.comp_id, h1]
  exact (cancel_mono (toPullbackAlong v)).mp
    (key.trans (Category.id_comp (toPullbackAlong v)).symm)

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

section SimulRepresentable

open EllObj

variable (P : ModuliProblem R) {Xδ : EllObj R} {Z : Scheme.{u}} {f : Z ⟶ Xδ.base}

/-- Transport of relative `P`-values along the cartesian-comparison isos: the value
of the universal element `eqv f ⟨𝟙 Z, _⟩` pulled back along `v` agrees with the
`eqv`-value of `v`'s base map, transported along `isoPullbackAlong`. -/
private theorem map_val_eq
    (eqv : ∀ {T : Scheme.{u}} (g : T ⟶ Xδ.base),
      { h : T ⟶ Z // h ≫ f = g } ≃ P.obj (Opposite.op (Xδ.pullbackAlong g)))
    (hnat : ∀ {T T' : Scheme.{u}} (g : T ⟶ Xδ.base) (k : T' ⟶ T)
      (h : { h : T ⟶ Z // h ≫ f = g }),
      eqv (k ≫ g) ⟨k ≫ h.1, by rw [Category.assoc, h.2]⟩ =
        P.map (Xδ.pullbackAlongMap g k).op (eqv g h))
    {Y : EllObj R} (v : Y ⟶ Xδ.pullbackAlong f) (u : Y ⟶ Xδ)
    (hu : v ≫ Xδ.pullbackAlongπ f = u) :
    P.map v.op (eqv f ⟨𝟙 Z, Category.id_comp f⟩) =
      P.map (isoPullbackAlong u).hom.op
        (eqv u.baseHom ⟨v.baseHom, by rw [← hu]; rfl⟩) := by
  subst hu
  rw [show (⟨v.baseHom, by rfl⟩ :
        { h : Y.base ⟶ Z // h ≫ f = (v ≫ Xδ.pullbackAlongπ f).baseHom }) =
      ⟨v.baseHom ≫ 𝟙 Z, by
        show (v.baseHom ≫ 𝟙 Z) ≫ f = v.baseHom ≫ f
        exact (Category.assoc _ _ _).trans
          (congrArg (fun t => v.baseHom ≫ t) (Category.id_comp f))⟩ from
    Subtype.ext (Category.comp_id _).symm]
  erw [hnat f v.baseHom ⟨𝟙 Z, Category.id_comp f⟩]
  conv_lhs => rw [← toPullbackAlong_pullbackAlongMap v]
  erw [op_comp, Functor.map_comp_apply]
  exact rfl

/-- **KM 4.7, step (i)** (KM p. 112: "Because `δ` is representable, and `𝒫` is
relatively representable, the simultaneous problem `(𝒫,δ)` is representable, by
`𝕸(𝒫,δ) = 𝒫_{E/𝕸(δ)}`"): the explicit `RepresentableBy` structure on the relative
representing object over the universal curve. -/
noncomputable def simulRepresentableBy (Q : ModuliProblem R)
    (rδ : Q.RepresentableBy Xδ)
    (eqv : ∀ {T : Scheme.{u}} (g : T ⟶ Xδ.base),
      { h : T ⟶ Z // h ≫ f = g } ≃ P.obj (Opposite.op (Xδ.pullbackAlong g)))
    (hnat : ∀ {T T' : Scheme.{u}} (g : T ⟶ Xδ.base) (k : T' ⟶ T)
      (h : { h : T ⟶ Z // h ≫ f = g }),
      eqv (k ≫ g) ⟨k ≫ h.1, by rw [Category.assoc, h.2]⟩ =
        P.map (Xδ.pullbackAlongMap g k).op (eqv g h)) :
    (P.simul Q).RepresentableBy (Xδ.pullbackAlong f) where
  homEquiv {Y} :=
    { toFun := fun v => (P.map v.op (eqv f ⟨𝟙 Z, Category.id_comp f⟩),
        Q.map v.op (rδ.homEquiv (Xδ.pullbackAlongπ f)))
      invFun := fun a =>
        homToPullbackAlong (rδ.homEquiv.symm a.2)
          ((eqv (rδ.homEquiv.symm a.2).baseHom).symm
            (P.map (isoPullbackAlong (rδ.homEquiv.symm a.2)).inv.op a.1)).1
          ((eqv (rδ.homEquiv.symm a.2).baseHom).symm
            (P.map (isoPullbackAlong (rδ.homEquiv.symm a.2)).inv.op a.1)).2
      left_inv := fun v => by
        dsimp only
        have hu₀ : rδ.homEquiv.symm
            (Q.map v.op (rδ.homEquiv (Xδ.pullbackAlongπ f))) =
            v ≫ Xδ.pullbackAlongπ f := by
          rw [← rδ.homEquiv_comp, Equiv.symm_apply_apply]
        have hh : (eqv (rδ.homEquiv.symm
              (Q.map v.op (rδ.homEquiv (Xδ.pullbackAlongπ f)))).baseHom).symm
            (P.map (isoPullbackAlong (rδ.homEquiv.symm
              (Q.map v.op (rδ.homEquiv (Xδ.pullbackAlongπ f))))).inv.op
              (P.map v.op (eqv f ⟨𝟙 Z, Category.id_comp f⟩))) =
            ⟨v.baseHom, by rw [← hu₀.symm]; rfl⟩ := by
          rw [map_val_eq P eqv hnat v _ hu₀.symm, ← Functor.map_comp_apply,
            ← op_comp, Iso.inv_hom_id, op_id, Functor.map_id_apply,
            Equiv.symm_apply_apply]
        rw [hh]
        refine EllHom.ext ?_ ?_
        · exact rfl
        · exact pullback.hom_ext
            ((pullback.lift_fst _ _ _).trans (congrArg EllHom.top hu₀))
            ((pullback.lift_snd _ _ _).trans v.isPullback.w.symm)
      right_inv := fun a => by
        dsimp only
        have hproj := homToPullbackAlong_pullbackAlongπ (rδ.homEquiv.symm a.2)
          ((eqv (rδ.homEquiv.symm a.2).baseHom).symm
            (P.map (isoPullbackAlong (rδ.homEquiv.symm a.2)).inv.op a.1)).1
          ((eqv (rδ.homEquiv.symm a.2).baseHom).symm
            (P.map (isoPullbackAlong (rδ.homEquiv.symm a.2)).inv.op a.1)).2
        refine Prod.ext ?_ ?_
        · rw [map_val_eq P eqv hnat _ _ hproj]
          rw [show (⟨(homToPullbackAlong (rδ.homEquiv.symm a.2)
                ((eqv (rδ.homEquiv.symm a.2).baseHom).symm
                  (P.map (isoPullbackAlong (rδ.homEquiv.symm a.2)).inv.op a.1)).1
                ((eqv (rδ.homEquiv.symm a.2).baseHom).symm
                  (P.map (isoPullbackAlong
                    (rδ.homEquiv.symm a.2)).inv.op a.1)).2).baseHom,
              ((eqv (rδ.homEquiv.symm a.2).baseHom).symm
                (P.map (isoPullbackAlong (rδ.homEquiv.symm a.2)).inv.op a.1)).2⟩ :
              { h : Y.base ⟶ Z // h ≫ f = (rδ.homEquiv.symm a.2).baseHom }) =
              (eqv (rδ.homEquiv.symm a.2).baseHom).symm
                (P.map (isoPullbackAlong (rδ.homEquiv.symm a.2)).inv.op a.1) from
            Subtype.ext rfl]
          rw [Equiv.apply_symm_apply, ← Functor.map_comp_apply, ← op_comp,
            Iso.hom_inv_id, op_id, Functor.map_id_apply]
        · show Q.map _ (rδ.homEquiv (Xδ.pullbackAlongπ f)) = a.2
          rw [← rδ.homEquiv_comp, hproj, Equiv.apply_symm_apply] }
  homEquiv_comp {Y Y'} k v := by
    refine Prod.ext ?_ ?_
    · show P.map (k ≫ v).op _ = P.map k.op (P.map v.op _)
      rw [op_comp, Functor.map_comp_apply]
    · show Q.map (k ≫ v).op _ = Q.map k.op (Q.map v.op _)
      rw [op_comp, Functor.map_comp_apply]

/-- **KM 4.7, step (i), existence form**: if `δ` is representable and `𝒫` is
relatively representable, the simultaneous problem `(𝒫,δ)` is representable. -/
theorem simul_representable (P Q : ModuliProblem R)
    (hQ : Q.Representable) (hP : P.RelativelyRepresentable) :
    (P.simul Q).Representable := by
  obtain ⟨Xδ, ⟨rδ⟩⟩ := hQ.has_representation
  obtain ⟨Z, f, eqv, hnat⟩ := hP Xδ
  exact ⟨⟨Xδ.pullbackAlong f,
    ⟨simulRepresentableBy P Q rδ @eqv @hnat⟩⟩⟩

end SimulRepresentable

section GroupAction

variable (P Q : ModuliProblem R)

/-- The natural transformation of simultaneous problems acting through the second
factor. -/
def simulMapSnd {Q Q' : ModuliProblem R} (η : Q ⟶ Q') :
    P.simul Q ⟶ P.simul Q' where
  app X := ↾fun a => (a.1, η.app X a.2)
  naturality X X' f := by
    ext a
    show ((P.map f a.1, η.app X' (Q.map f a.2)) : P.obj X' × Q'.obj X') =
      (P.map f a.1, Q'.map f (η.app X a.2))
    exact Prod.ext rfl (NatTrans.naturality_apply η f a.2)

@[simp]
theorem simulMapSnd_app {Q Q' : ModuliProblem R} (η : Q ⟶ Q')
    (X : (EllObj R)ᵒᵖ) (a : (P.simul Q).obj X) :
    (P.simulMapSnd η).app X a = (a.1, η.app X a.2) := rfl

@[simp]
theorem simulMapSnd_id : P.simulMapSnd (𝟙 Q) = 𝟙 (P.simul Q) := by
  ext X a
  rfl

theorem simulMapSnd_comp {Q Q' Q'' : ModuliProblem R} (η : Q ⟶ Q')
    (θ : Q' ⟶ Q'') :
    P.simulMapSnd (η ≫ θ) = P.simulMapSnd η ≫ P.simulMapSnd θ := by
  ext X a
  rfl

/-- **The action of `Aut δ` on the simultaneous problem `(𝒫,δ)` through the
second factor** (KM p. 112: `G` acts on `(𝒫,δ)` through its action on `δ`). -/
def simulAutSnd : Aut Q →* Aut (P.simul Q) where
  toFun e :=
    { hom := P.simulMapSnd e.hom
      inv := P.simulMapSnd e.inv
      hom_inv_id := by rw [← simulMapSnd_comp, e.hom_inv_id, simulMapSnd_id]
      inv_hom_id := by rw [← simulMapSnd_comp, e.inv_hom_id, simulMapSnd_id] }
  map_one' := by
    ext1
    exact P.simulMapSnd_id Q
  map_mul' e₁ e₂ := by
    ext1
    exact P.simulMapSnd_comp e₂.hom e₁.hom

@[simp]
theorem simulAutSnd_apply_hom (e : Aut Q) :
    ((P.simulAutSnd Q) e).hom = P.simulMapSnd e.hom := rfl

end GroupAction

end ModuliProblem

namespace EllObj

/-- Base-scheme projection of `Ell/R`-automorphisms: an automorphism of an
`Ell/R`-object restricts to an automorphism of its base scheme. -/
def autBase (X : EllObj R) : Aut X →* Aut X.base where
  toFun e :=
    { hom := e.hom.baseHom
      inv := e.inv.baseHom
      hom_inv_id := congrArg EllHom.baseHom e.hom_inv_id
      inv_hom_id := congrArg EllHom.baseHom e.inv_hom_id }
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem autBase_apply_hom (X : EllObj R) (e : Aut X) :
    (X.autBase e).hom = e.hom.baseHom := rfl

/-- **([a1], total-space projection)** Total-space projection of `Ell/R`-automorphisms: an
automorphism of an `Ell/R`-object restricts to an automorphism of the total space of its
curve. This is the map that turns KM's cocycle `θ(g) : g*(E, α_univ) ≅ (E, α_univ)`
(KM p. 113) into an honest `G`-action **on the universal curve `E`** — the observation on
which route (a) of `[T-E5c-ROUTE-A]` rests: the curve descended along the torsor is `E/G`,
so no effective descent of projective schemes (SGA I Exp. VIII 7.8) is needed. -/
def autTotal (X : EllObj R) : Aut X →* Aut X.curve.E where
  toFun e :=
    { hom := e.hom.top
      inv := e.inv.top
      hom_inv_id := congrArg EllHom.top e.hom_inv_id
      inv_hom_id := congrArg EllHom.top e.inv_hom_id }
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem autTotal_apply_hom (X : EllObj R) (e : Aut X) :
    (X.autTotal e).hom = e.hom.top := rfl

end EllObj

namespace ModuliProblem

open CategoryTheory.Functor

/-- **The KM 4.7 geometric action** (KM p. 112–113: "Let `G` operate upon
`𝕸(𝒫,δ)` through its action on `δ`", then "The action of `g ∈ G` on `𝕸(𝒫,δ)` is
defined as follows: the curve `E` with `(α_univ, g·β_univ)` is classified by a
unique morphism `g : 𝕸(𝒫,δ) → 𝕸(𝒫,δ)`"): the scheme action of `G` on the base of
any representing object of the simultaneous problem `(𝒫,δ)`, induced by an action
`φ : G →* Aut δ` on the auxiliary problem. -/
noncomputable def simulSchemeAction (P Q : ModuliProblem R) {G : Type*} [Group G]
    (φ : G →* Aut Q) {XM : EllObj R}
    (rM : (P.simul Q).RepresentableBy XM) :
    AlgebraicGeometry.SchemeAction G XM.base :=
  AlgebraicGeometry.SchemeAction.ofAut
    ((XM.autBase.comp rM.autMulHom).comp ((P.simulAutSnd Q).comp φ))

/-- **([a1], the `G`-action on the universal curve)** The same KM 4.7 action, on the *total
space* of the universal curve over the representing object of `(𝒫,δ)`.

KM (p. 113) produces, for each `g ∈ G`, a canonical isomorphism `θ(g)` of the pulled-back
curve; because every `Ell/R`-morphism carries its top map (`EllHom.top`) functorially, the
monoid homomorphism `g ↦ rM.autMulHom (g · β_univ)` already *is* an action on `E`. -/
noncomputable def simulSchemeActionTotal (P Q : ModuliProblem R) {G : Type*} [Group G]
    (φ : G →* Aut Q) {XM : EllObj R}
    (rM : (P.simul Q).RepresentableBy XM) :
    AlgebraicGeometry.SchemeAction G XM.curve.E :=
  AlgebraicGeometry.SchemeAction.ofAut
    ((XM.autTotal.comp rM.autMulHom).comp ((P.simulAutSnd Q).comp φ))

/-- **([a1], `π` is equivariant)** The structure morphism of the universal curve intertwines
the action on `E` with the action on the base — the cartesian-square axiom `EllHom.isPullback`
read as equivariance. -/
theorem simulSchemeActionTotal_π (P Q : ModuliProblem R) {G : Type*} [Group G]
    (φ : G →* Aut Q) {XM : EllObj R} (rM : (P.simul Q).RepresentableBy XM) (γ : G) :
    (P.simulSchemeActionTotal Q φ rM).hom γ ≫ XM.curve.π =
      XM.curve.π ≫ (P.simulSchemeAction Q φ rM).hom γ :=
  (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv.isPullback.w

/-- **([a1], the zero section is equivariant)** -/
theorem simulSchemeActionTotal_zero (P Q : ModuliProblem R) {G : Type*} [Group G]
    (φ : G →* Aut Q) {XM : EllObj R} (rM : (P.simul Q).RepresentableBy XM) (γ : G) :
    XM.curve.zero ≫ (P.simulSchemeActionTotal Q φ rM).hom γ =
      (P.simulSchemeAction Q φ rM).hom γ ≫ XM.curve.zero :=
  (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv.zero_w

/-- **([a1], each `γ` acts cartesianly)** Every `γ ∈ G` acts on `E` by an isomorphism whose
square over the base action is **cartesian**. Equivalently: `E` is the pullback of itself
along `σ_base γ`. This is what makes `E → E/G` a `G`-torsor over `X → X/G` in `[a3]`. -/
theorem simulSchemeActionTotal_isPullback (P Q : ModuliProblem R) {G : Type*} [Group G]
    (φ : G →* Aut Q) {XM : EllObj R} (rM : (P.simul Q).RepresentableBy XM) (γ : G) :
    IsPullback ((P.simulSchemeActionTotal Q φ rM).hom γ) XM.curve.π XM.curve.π
      ((P.simulSchemeAction Q φ rM).hom γ) :=
  (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv.isPullback

section Engine

open AlgebraicGeometry

/-- A **relative representation datum** for `Q` at `X : Ell/R` — the components
of one instance of `RelativelyRepresentable` (T-E3), bundled as data so the
KM 4.7 engine can consume them functionally. -/
structure RelRepData (Q : ModuliProblem R) (X : EllObj R) where
  /-- The relative representing scheme. -/
  Z : Scheme.{u}
  /-- Its structure map to the base. -/
  f : Z ⟶ X.base
  /-- The representing bijections. -/
  eqv : ∀ {T : Scheme.{u}} (g : T ⟶ X.base),
    { h : T ⟶ Z // h ≫ f = g } ≃ Q.obj (Opposite.op (X.pullbackAlong g))
  /-- Naturality of the representing bijections in `T`. -/
  nat : ∀ {T T' : Scheme.{u}} (g : T ⟶ X.base) (k : T' ⟶ T)
    (h : { h : T ⟶ Z // h ≫ f = g }),
    eqv (k ≫ g) ⟨k ≫ h.1, by rw [Category.assoc, h.2]⟩ =
      Q.map (X.pullbackAlongMap g k).op (eqv g h)

/-- The bundled and the `∃`-form of relative representability agree. -/
theorem relativelyRepresentable_iff_nonempty_relRepData (Q : ModuliProblem R) :
    Q.RelativelyRepresentable ↔ ∀ X : EllObj R, Nonempty (RelRepData Q X) := by
  constructor
  · intro hQ X
    obtain ⟨Z, f, eqv, hnat⟩ := hQ X
    exact ⟨⟨Z, f, @eqv, @hnat⟩⟩
  · intro hQ X
    obtain ⟨d⟩ := hQ X
    exact ⟨d.Z, d.f, @d.eqv, @d.nat⟩

/-- **KM 4.7, axiom 2 vocabulary** (KM p. 112: "G operates upon δ, in such a way
that for every elliptic curve E/S […] the S-scheme `δ_{E/S}` is a finite etale
G-torsor"): a relative representation datum for the auxiliary problem carrying a
compatible `G`-action which makes it a finite étale `G`-torsor over the base.

Convention (attack-adjudicated): the `G`-action on classifying maps is by
precomposition with `σZ.hom γ`, intertwining `(φ γ).hom` on values. -/
structure TorsorData {Q : ModuliProblem R} {G : Type u} [Group G] [Finite G]
    (φ : G →* Aut Q) (X : EllObj R) extends RelRepData Q X where
  /-- The `G`-action on the relative representing scheme. -/
  σZ : SchemeAction G Z
  /-- The action lies over the base. -/
  over_base : ∀ γ : G, σZ.hom γ ≫ f = f
  /-- The representing bijections are `G`-equivariant. -/
  equivariant : ∀ {T : Scheme.{u}} (g : T ⟶ X.base)
    (h : { h : T ⟶ Z // h ≫ f = g }) (γ : G),
    eqv g ⟨h.1 ≫ σZ.hom γ, by rw [Category.assoc, over_base, h.2]⟩ =
      (φ γ).hom.app (Opposite.op (X.pullbackAlong g)) (eqv g h)
  /-- The structure map is finite. -/
  finite : IsFinite f
  /-- The structure map is étale. -/
  etale : AlgebraicGeometry.Etale f
  /-- The structure map is surjective (torsors cover their base; see the attack
  block — KM's Legendre example is a torsor only over `S[1/2]`, and the engine
  is invoked over bases where the axiom holds with honest content). -/
  surjective : Surjective f
  /-- The torsor condition: `(γ, z) ↦ (γ·z, z)` identifies `∐_G Z` with
  `Z ×_{X.base} Z`. -/
  torsor : IsIso ((Limits.Sigma.desc fun γ : G =>
    Limits.pullback.lift (σZ.hom γ) (𝟙 Z)
      (by rw [Category.id_comp]; exact over_base γ)) :
    (∐ fun _ : G => Z) ⟶ Limits.pullback f f)

set_option backward.isDefEq.respectTransparency.types false in
/-- **Freeness of the KM action** (KM p. 113: "By axiom 2) and the rigidity of
`𝒫`, `G` operates freely on `𝕸(𝒫,δ)`"): if `𝒫` is rigid and the auxiliary
problem is a rigidifier, no `g ≠ 1` fixes a point of the representing object of
the simultaneous problem over a nonempty scheme.

Proof (KM p. 113): a fixed `T`-point yields two `Ell/R`-morphisms over the same
base map, hence (`connectHom`) an automorphism `θ(γ)` of the pulled-back curve
over `𝟙 T` fixing the `𝒫`-value; rigidity forces `θ(γ) = 𝟙`, so the `δ`-value
is `γ`-fixed; the equivariance of the torsor datum turns this into a `γ`-fixed
classifying map to `Z`, and the torsor comparison then factors the point through
two distinct summands of `∐_G Z`, which are disjoint
(`isEmpty_of_commSq_sigmaι_of_ne`). -/
theorem simulSchemeAction_free_of_rigid (P Q : ModuliProblem R)
    {G : Type u} [Group G] [Finite G] (φ : G →* Aut Q) {XM : EllObj R}
    (rM : (P.simul Q).RepresentableBy XM)
    (hrig : P.Rigid) (htors : ∀ X : EllObj R, Nonempty (TorsorData φ X))
    (γ : G) (hγ : γ ≠ 1) (T : Scheme.{u}) (t : T ⟶ XM.base)
    (hfix : t ≫ (P.simulSchemeAction Q φ rM).hom γ = t) :
    IsEmpty T := by
  have hfix' : t ≫ (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv.baseHom = t :=
    hfix
  -- the Ell/R-level lift of `t` and the two morphisms it compares
  have hb : (XM.pullbackAlongπ t ≫
      (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv).baseHom =
      (XM.pullbackAlongπ t).baseHom := hfix'
  have hb2 : (XM.pullbackAlongπ t ≫
      (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).hom).baseHom =
      (XM.pullbackAlongπ t).baseHom := by
    show t ≫ _ = t
    have hcan : (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv.baseHom ≫
        (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).hom.baseHom = 𝟙 XM.base :=
      congrArg EllHom.baseHom (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv_hom_id
    conv_lhs => rw [← hfix']
    rw [Category.assoc, hcan, Category.comp_id]
  -- the connecting endomorphism θ(γ) and its inverse
  have hξw := EllObj.connectHom_comp _ _ hb
  have hξ'w := EllObj.connectHom_comp _ _ hb2
  have hii : EllObj.connectHom _ _ hb ≫ EllObj.connectHom _ _ hb2 =
      𝟙 (XM.pullbackAlong t) := by
    refine EllObj.eq_id_of_baseHom_of_comp (XM.pullbackAlongπ t) _ ?_ ?_
    · show (EllObj.connectHom _ _ hb).baseHom ≫
        (EllObj.connectHom _ _ hb2).baseHom = 𝟙 _
      rw [EllObj.connectHom_baseHom, EllObj.connectHom_baseHom,
        Category.id_comp]
    · rw [Category.assoc, hξ'w, ← Category.assoc, hξw, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
  have hii' : EllObj.connectHom _ _ hb2 ≫ EllObj.connectHom _ _ hb =
      𝟙 (XM.pullbackAlong t) := by
    refine EllObj.eq_id_of_baseHom_of_comp (XM.pullbackAlongπ t) _ ?_ ?_
    · show (EllObj.connectHom _ _ hb2).baseHom ≫
        (EllObj.connectHom _ _ hb).baseHom = 𝟙 _
      rw [EllObj.connectHom_baseHom, EllObj.connectHom_baseHom,
        Category.id_comp]
    · rw [Category.assoc, hξw, ← Category.assoc, hξ'w, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
  -- value comparison: the P-component is θ(γ)-fixed, the Q-component γ-moved
  have h1 : rM.homEquiv (XM.pullbackAlongπ t ≫
      (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv) =
      ((rM.homEquiv (XM.pullbackAlongπ t)).1,
        (φ γ).inv.app (Opposite.op (XM.pullbackAlong t))
          (rM.homEquiv (XM.pullbackAlongπ t)).2) :=
    rM.homEquiv_comp_transportHom (P.simulMapSnd (φ γ).inv) (XM.pullbackAlongπ t)
  have h2 : rM.homEquiv (XM.pullbackAlongπ t ≫
      (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv) =
      (P.map (EllObj.connectHom _ _ hb).op
        (rM.homEquiv (XM.pullbackAlongπ t)).1,
       Q.map (EllObj.connectHom _ _ hb).op
        (rM.homEquiv (XM.pullbackAlongπ t)).2) := by
    conv_lhs => rw [← hξw]
    rw [rM.homEquiv_comp]
    exact rfl
  have c1 : P.map (EllObj.connectHom _ _ hb).op
      (rM.homEquiv (XM.pullbackAlongπ t)).1 =
      (rM.homEquiv (XM.pullbackAlongπ t)).1 :=
    congrArg Prod.fst (h2.symm.trans h1)
  have c2 : Q.map (EllObj.connectHom _ _ hb).op
      (rM.homEquiv (XM.pullbackAlongπ t)).2 =
      (φ γ).inv.app (Opposite.op (XM.pullbackAlong t))
        (rM.homEquiv (XM.pullbackAlongπ t)).2 :=
    congrArg Prod.snd (h2.symm.trans h1)
  -- rigidity forces θ(γ) = 𝟙
  have hΘ : EllObj.connectHom _ _ hb = 𝟙 (XM.pullbackAlong t) := by
    by_contra hne
    exact hrig (XM.pullbackAlong t)
      ⟨EllObj.connectHom _ _ hb, EllObj.connectHom _ _ hb2, hii, hii'⟩
      (EllObj.connectHom_baseHom _ _ hb)
      (fun hEq => hne (congrArg Iso.hom hEq))
      (rM.homEquiv (XM.pullbackAlongπ t)).1 c1
  -- hence the δ-value is γ-fixed
  have hfixval : (φ γ).hom.app (Opposite.op (XM.pullbackAlong t))
      (rM.homEquiv (XM.pullbackAlongπ t)).2 =
      (rM.homEquiv (XM.pullbackAlongπ t)).2 := by
    have c2' : (rM.homEquiv (XM.pullbackAlongπ t)).2 =
        (φ γ).inv.app (Opposite.op (XM.pullbackAlong t))
          (rM.homEquiv (XM.pullbackAlongπ t)).2 := by
      rw [← c2, hΘ, op_id, Functor.map_id_apply]
    conv_lhs => rw [c2']
    exact congrArg
      (fun η : Q ⟶ Q => η.app (Opposite.op (XM.pullbackAlong t))
        (rM.homEquiv (XM.pullbackAlongπ t)).2) (φ γ).inv_hom_id
  -- transport into the torsor chart at the identity base map
  obtain ⟨td⟩ := htors (XM.pullbackAlong t)
  -- `β` is the δ-value read in the chart at the identity base map, and `z` its classifying
  -- map to the torsor `td.Z`
  set β := Q.map (EllObj.isoPullbackAlong (𝟙 (XM.pullbackAlong t))).inv.op
    (rM.homEquiv (XM.pullbackAlongπ t)).2 with hβ_def
  set z := ((td.eqv (𝟙 (XM.pullbackAlong t).base)).symm β).1 with hz_def
  have hβ : (φ γ).hom.app
      (Opposite.op ((XM.pullbackAlong t).pullbackAlong (𝟙 _))) β = β := by
    rw [hβ_def, NatTrans.naturality_apply, hfixval]
  have hZfix : z ≫ td.σZ.hom γ = z := by
    have heq := td.equivariant (𝟙 (XM.pullbackAlong t).base)
      ((td.eqv (𝟙 (XM.pullbackAlong t).base)).symm β) γ
    rw [Equiv.apply_symm_apply, hβ] at heq
    exact congrArg Subtype.val ((td.eqv _).injective
      (heq.trans (Equiv.apply_symm_apply _ _).symm))
  -- torsor endgame: the point factors through two distinct summands
  haveI := td.torsor
  have hpt : z ≫ Limits.Sigma.ι (fun _ : G => td.Z) γ =
      z ≫ Limits.Sigma.ι (fun _ : G => td.Z) (1 : G) := by
    rw [← cancel_mono ((Limits.Sigma.desc fun γ' : G =>
      Limits.pullback.lift (td.σZ.hom γ') (𝟙 td.Z)
        (by rw [Category.id_comp]; exact td.over_base γ')) :
      (∐ fun _ : G => td.Z) ⟶ Limits.pullback td.f td.f),
      Category.assoc, Category.assoc, Limits.Sigma.ι_desc,
      Limits.Sigma.ι_desc]
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Limits.pullback.lift_fst, Category.assoc,
        Limits.pullback.lift_fst, hZfix, td.σZ.hom_one, Category.comp_id]
    · rw [Category.assoc, Limits.pullback.lift_snd, Category.assoc,
        Limits.pullback.lift_snd]
  exact isEmpty_of_commSq_sigmaι_of_ne ⟨hpt⟩ hγ

/-- **([a1], the action on the universal curve is free)** If `𝒫` is rigid and `δ` is a
finite étale `G`-torsor rigidifier, then `G` acts **freely on the total space of the
universal curve** `E` over `𝕸(𝒫,δ)`: no `γ ≠ 1` fixes a `T`-point of `E` over a nonempty
`T`.

Immediate from freeness on the base (`simulSchemeAction_free_of_rigid`) and equivariance of
`π` (`simulSchemeActionTotal_π`): a `γ`-fixed `T`-point `t` of `E` projects to a `γ`-fixed
`T`-point `t ≫ π` of the base. -/
theorem simulSchemeActionTotal_free_of_rigid (P Q : ModuliProblem R)
    {G : Type u} [Group G] [Finite G] (φ : G →* Aut Q) {XM : EllObj R}
    (rM : (P.simul Q).RepresentableBy XM)
    (hrig : P.Rigid) (htors : ∀ X : EllObj R, Nonempty (TorsorData φ X))
    (γ : G) (hγ : γ ≠ 1) (T : Scheme.{u}) (t : T ⟶ XM.curve.E)
    (hfix : t ≫ (P.simulSchemeActionTotal Q φ rM).hom γ = t) :
    IsEmpty T := by
  refine simulSchemeAction_free_of_rigid P Q φ rM hrig htors γ hγ T (t ≫ XM.curve.π) ?_
  rw [Category.assoc, ← simulSchemeActionTotal_π, ← Category.assoc, hfix]

/-- **The Katz–Mazur 4.7 engine** (SCHOLIE 4.7.0, axiomatized claim, KM p. 112:
"We claim that over `ℤ[1/N]`, `𝒫` is represented by the affine `ℤ[1/N]`-scheme
`𝕸(𝒫,δ)/G`"): a rigid, relatively representable moduli problem that is affine
over `(Ell)` is representable, given an auxiliary problem `δ` that is
representable by an affine scheme and carries a `G`-action making its relative
representing schemes finite étale `G`-torsors.

Proof route (banked; KM pp. 112–116): `𝕸(𝒫,δ)` represents `𝒫.simul δ`
(`simul_representable`, PROVEN); `G` acts via `simulSchemeAction` (PROVEN);
rigidity makes the action free (`simulSchemeAction_free_of_rigid`); the base is
affine, so the T-Q3 affine quotient applies and `π` is a finite étale `G`-torsor
[SGA III Exp. V 4.1 = `ForMathlib/InvariantTorsor.lean` T-Q2 interface]; the
universal curve and its `𝒫`-structure descend [SGA I Exp. VIII = stream-DESC
black box, `levelledCurve_descent_of_torsor` shape]; the descended pair
represents `𝒫` by the torsor argument of KM pp. 114–116. WIP `sorry` (T-Q6d.γ);
gated on T-Q2's SGA III V 4.1 statements and the stream-DESC descent engine. -/
theorem representable_of_rigid_of_torsor (P Q : ModuliProblem R)
    {G : Type u} [Group G] [Finite G] (φ : G →* Aut Q)
    (hQrep : Q.Representable)
    (hQaff : ∀ {XQ : EllObj R}, Q.RepresentableBy XQ → IsAffine XQ.base)
    (hPaff : ∀ X : EllObj R, ∃ d : RelRepData P X, IsAffineHom d.f)
    (htors : ∀ X : EllObj R, Nonempty (TorsorData φ X))
    (hrig : P.Rigid) :
    P.Representable := by
  sorry

/-! ### [B1] α_univ-descent (KM 4.7.0, p. 114) -/

/-- The chart-comparison morphism composed with the chart projection is the chart
projection of the composite base map: `pullbackAlongMap g k ≫ π_g = π_{k ≫ g}`. -/
private theorem pullbackAlongMap_pullbackAlongπ {R : CommRingCat.{u}} (X : EllObj R)
    {T T' : Scheme.{u}} (g : T ⟶ X.base) (k : T' ⟶ T) :
    X.pullbackAlongMap g k ≫ X.pullbackAlongπ g = X.pullbackAlongπ (k ≫ g) := by
  refine EllHom.ext rfl ?_
  show Limits.pullback.map X.curve.π (k ≫ g) X.curve.π g (𝟙 _) k (𝟙 _)
      (by simp) (by simp) ≫ Limits.pullback.fst X.curve.π g =
    Limits.pullback.fst X.curve.π (k ≫ g)
  rw [Limits.pullback.lift_fst, Category.comp_id]

/-- Presentation-independent naturality of a relative representation datum: transporting
a chart value along *any* `Ell/R`-morphism `w` of charts which lies over `k` and commutes
with the chart projections computes as precomposition of the classifying section by `k`. -/
private theorem map_eqv {R : CommRingCat.{u}} {P : ModuliProblem R} {X₀ : EllObj R}
    (d₀ : RelRepData P X₀) {T T' : Scheme.{u}}
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
      rw [hwπ, pullbackAlongMap_pullbackAlongπ]
    · exact hbk
  rw [hw]
  exact (d₀.nat g k h).symm

/-- **([B1], α_univ-descent — KM 4.7.0, p. 114)** A `G`-invariant `P`-class upstairs descends
uniquely through an `Ell/R`-morphism `q` whose base has the quotient universal property. -/
theorem existsUnique_alpha_descent {R : CommRingCat.{u}} {P : ModuliProblem R}
    {XE X₀ : EllObj R} (q : XE ⟶ X₀) (d₀ : RelRepData P X₀)
    {G : Type u} [Group G] (σ : SchemeAction G XE.base)
    (actE : G → (XE ⟶ XE))
    (hbase : ∀ γ, (actE γ).baseHom = σ.hom γ)
    (hqcoeq : ∀ γ, actE γ ≫ q = q)
    (hlift : ∀ {Y : Scheme.{u}} (F : XE.base ⟶ Y), (∀ γ, σ.hom γ ≫ F = F) →
      ∃ F₀ : X₀.base ⟶ Y, q.baseHom ≫ F₀ = F)
    (hepi : Epi q.baseHom)
    (α : P.obj (Opposite.op XE)) (hinv : ∀ γ, P.map (actE γ).op α = α) :
    ∃! α₀ : P.obj (Opposite.op X₀), P.map q.op α₀ = α := by
  haveI := hepi
  -- the inverse cartesian comparison collapses to the chart projection
  have hqinv : (EllObj.isoPullbackAlong q).inv ≫ q = X₀.pullbackAlongπ q.baseHom := by
    rw [Iso.inv_comp_eq]
    exact (EllObj.toPullbackAlong_pullbackAlongπ q).symm
  -- present α in the chart over b = q.baseHom as a section sα of d₀.f
  obtain ⟨sα, hsα⟩ : ∃ s : { h : XE.base ⟶ d₀.Z // h ≫ d₀.f = q.baseHom },
      d₀.eqv q.baseHom s = P.map (EllObj.isoPullbackAlong q).inv.op α :=
    ⟨(d₀.eqv q.baseHom).symm _, (d₀.eqv q.baseHom).apply_symm_apply _⟩
  -- G-invariance of the classifying section
  have step2 : ∀ γ : G, σ.hom γ ≫ sα.1 = sα.1 := by
    intro γ
    have hσb : σ.hom γ ≫ q.baseHom = q.baseHom := by
      rw [← hbase γ]
      exact congrArg EllHom.baseHom (hqcoeq γ)
    obtain ⟨wγ, hwγb, hwγπ, hwγinv⟩ :
        ∃ wγ : X₀.pullbackAlong q.baseHom ⟶ X₀.pullbackAlong q.baseHom,
          wγ.baseHom = σ.hom γ ∧
            wγ ≫ X₀.pullbackAlongπ q.baseHom = X₀.pullbackAlongπ q.baseHom ∧
              wγ ≫ (EllObj.isoPullbackAlong q).inv =
                (EllObj.isoPullbackAlong q).inv ≫ actE γ := by
      refine ⟨(EllObj.isoPullbackAlong q).inv ≫ actE γ ≫
        (EllObj.isoPullbackAlong q).hom, ?_, ?_, ?_⟩
      · show 𝟙 XE.base ≫ (actE γ).baseHom ≫ 𝟙 XE.base = σ.hom γ
        rw [Category.id_comp, Category.comp_id]
        exact hbase γ
      · rw [Category.assoc, Category.assoc, EllObj.isoPullbackAlong_hom,
          EllObj.toPullbackAlong_pullbackAlongπ, hqcoeq γ, hqinv]
      · simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hkey := map_eqv d₀ wγ (σ.hom γ) hwγb hσb hwγπ sα
    rw [hsα, ← Functor.map_comp_apply, ← op_comp, hwγinv, op_comp,
      Functor.map_comp_apply, hinv γ, ← hsα] at hkey
    exact (congrArg Subtype.val ((d₀.eqv q.baseHom).injective hkey)).symm
  -- descend the section through the quotient
  obtain ⟨s₀, hs₀⟩ := hlift sα.1 step2
  have hsec : s₀ ≫ d₀.f = 𝟙 X₀.base := by
    rw [← cancel_epi q.baseHom, ← Category.assoc, hs₀, sα.2, Category.comp_id]
  -- the identity-chart inclusion ι and the chart comparison w over b
  obtain ⟨ι, w, hιπ, hwπ, hwb, hqιb⟩ :
      ∃ (ι : X₀ ⟶ X₀.pullbackAlong (𝟙 X₀.base))
        (w : X₀.pullbackAlong q.baseHom ⟶ X₀.pullbackAlong (𝟙 X₀.base)),
        ι ≫ X₀.pullbackAlongπ (𝟙 X₀.base) = 𝟙 X₀ ∧
          w ≫ X₀.pullbackAlongπ (𝟙 X₀.base) = X₀.pullbackAlongπ q.baseHom ∧
            w.baseHom = q.baseHom ∧
              (q ≫ ι).baseHom = ((EllObj.isoPullbackAlong q).hom ≫ w).baseHom := by
    refine ⟨EllObj.homToPullbackAlong (𝟙 X₀) (𝟙 X₀.base) (Category.id_comp _),
      EllObj.homToPullbackAlong (X₀.pullbackAlongπ q.baseHom) q.baseHom
        (Category.comp_id _),
      EllObj.homToPullbackAlong_pullbackAlongπ _ _ _,
      EllObj.homToPullbackAlong_pullbackAlongπ _ _ _, rfl, ?_⟩
    show q.baseHom ≫ 𝟙 X₀.base = 𝟙 XE.base ≫ q.baseHom
    rw [Category.comp_id, Category.id_comp]
  -- the descended chart value transports back to α's chart value over b
  have hweqv : P.map w.op (d₀.eqv (𝟙 X₀.base) ⟨s₀, hsec⟩) =
      P.map (EllObj.isoPullbackAlong q).inv.op α := by
    rw [map_eqv d₀ w q.baseHom hwb (Category.comp_id q.baseHom) hwπ ⟨s₀, hsec⟩, ← hsα]
    exact congrArg (d₀.eqv q.baseHom) (Subtype.ext hs₀)
  -- q composed with the identity-chart inclusion factors through w
  have hqι : q ≫ ι = (EllObj.isoPullbackAlong q).hom ≫ w := by
    apply (EllObj.homPullbackAlongEquiv X₀ (𝟙 X₀.base) XE).injective
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show (q ≫ ι) ≫ X₀.pullbackAlongπ (𝟙 X₀.base) =
        ((EllObj.isoPullbackAlong q).hom ≫ w) ≫ X₀.pullbackAlongπ (𝟙 X₀.base)
      rw [Category.assoc, Category.assoc, hιπ, hwπ, Category.comp_id,
        EllObj.isoPullbackAlong_hom, EllObj.toPullbackAlong_pullbackAlongπ]
    · exact hqιb
  -- existence
  have hexist : P.map q.op (P.map ι.op (d₀.eqv (𝟙 X₀.base) ⟨s₀, hsec⟩)) = α := by
    rw [← Functor.map_comp_apply, ← op_comp, hqι, op_comp, Functor.map_comp_apply,
      hweqv, ← Functor.map_comp_apply, ← op_comp, Iso.hom_inv_id, op_id,
      Functor.map_id_apply]
  refine ⟨P.map ι.op (d₀.eqv (𝟙 X₀.base) ⟨s₀, hsec⟩), hexist, fun β hβ => ?_⟩
  -- uniqueness: any β pulling back to α has the same classifying section
  obtain ⟨tβ, htβ⟩ : ∃ t : { h : X₀.base ⟶ d₀.Z // h ≫ d₀.f = 𝟙 X₀.base },
      d₀.eqv (𝟙 X₀.base) t = P.map (X₀.pullbackAlongπ (𝟙 X₀.base)).op β :=
    ⟨(d₀.eqv (𝟙 X₀.base)).symm _, (d₀.eqv (𝟙 X₀.base)).apply_symm_apply _⟩
  have hkeyβ := map_eqv d₀ w q.baseHom hwb (Category.comp_id q.baseHom) hwπ tβ
  rw [htβ, ← Functor.map_comp_apply, ← op_comp, hwπ, ← hqinv, op_comp,
    Functor.map_comp_apply, hβ, ← hsα] at hkeyβ
  have hts : tβ.1 = s₀ := by
    refine (cancel_epi q.baseHom).mp ?_
    exact ((congrArg Subtype.val
      ((d₀.eqv q.baseHom).injective hkeyβ)).symm).trans hs₀.symm
  have hval : P.map (X₀.pullbackAlongπ (𝟙 X₀.base)).op β =
      d₀.eqv (𝟙 X₀.base) ⟨s₀, hsec⟩ := by
    rw [← htβ]
    exact congrArg (d₀.eqv (𝟙 X₀.base)) (Subtype.ext hts)
  rw [← hval, ← Functor.map_comp_apply, ← op_comp, hιπ, op_id, Functor.map_id_apply]

end Engine

end ModuliProblem

end ModularCurves

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.EngineDescent

/-!
# [T-Q6d.γ] The KM 4.7 engine mouth

`representable_of_rigidNoeth_of_torsor` / `representable_of_rigid_of_torsor` — the
representability engine of Katz–Mazur pp. 112–116, assembled from the simultaneous
representation ([a1], `Moduli/QuotientProblem.lean`), the free-action quotient machinery
(route-(a) Phase A, `Moduli/EngineDescent.lean` + `ForMathlib/SchemeQuotient.lean` +
`ForMathlib/SchemeActionFree.lean`), and the [B1] `α_univ`-descent.

This file sits **downstream of `EngineDescent`** precisely so the geometric interface
`exists_engineQuotient` can be discharged from the assembled Phase-A engine (the mouth was
first assembled inside `QuotientProblem.lean`, where that machinery is not importable; the
`section EngineMouth` was moved here verbatim — v10.327 import surgery, statements unchanged).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace ModularCurves

variable {R : CommRingCat.{u}}

namespace ModuliProblem

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


/-! ### [B3] The engine mouth — assembly of KM pp. 112–116 at `RigidNoeth`

The Katz–Mazur representability bijection, assembled *in this file* from the [B1]
α-descent above and the T-Q2 torsor toolkit (`ForMathlib/TorsorMap.lean`). The geometric
core — the free quotient `q : 𝕸(𝒫,δ) ⟶ 𝕸(𝒫,δ)/G` in `Ell/R` — is the route-(a) Phase-A
engine, which lives *downstream* of this file (`Moduli/EngineDescent.lean` **imports**
this file), so it enters here as the single precisely-stated private interface
`exists_engineQuotient` (sorried; see its docstring for the exact downstream discharge).
Everything around it is proven.

Design note (why no rigidity appears in the bijection): the two `Rigid` calls of the
downstream [B3] assembly (`Moduli/QuotientRepresentability.lean`: `coreData_qinv_full`
and `coreData_hom_eq_of_baseHom_eq`) are avoidable. The `Ell/R`-level `q`-invariance is
exposed by the quotient construction itself (`hqfull` in `exists_engineQuotient`: the
curve-level quotient projection is `G`-invariant by construction, no rigidity re-derivation
needed), and the uniqueness half of the representability bijection is a *retraction*
computation (`eq_descended`): any `v` inducing `α` satisfies
`π_{s(v)} ≫ v = θ̃ ≫ classifyTorsor α ≫ q` over the `q`-pulled-back chart, hence equals
the canonically descended morphism after cancelling the fppf epi `π_{s(v)}` componentwise
— no connecting automorphism, so no rigidity at the arbitrary test object. Rigidity is
consumed exactly once, at `RigidNoeth` strength ([T-W7.8]): freeness of the `G`-action,
`simulSchemeAction_free_of_rigidNoeth` (PROVEN above). -/

section EngineMouth

open Opposite

/-- **(θ-tautology, KM p. 113)** For the KM `Ell/R`-automorphism
`A γ = rM.autMulHom (simulAutSnd (φ γ))`, the `P`-component of the simultaneous universal
class is `(A γ).inv`-invariant: `G` acts only through the `δ`-component. -/
private theorem map_fst_autMulHom_inv {P Q : ModuliProblem R} {G : Type u} [Group G]
    (φ : G →* Aut Q) {XM : EllObj R} (rM : (P.simul Q).RepresentableBy XM) (γ : G) :
    P.map (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv.op (rM.homEquiv (𝟙 XM)).1 =
      (rM.homEquiv (𝟙 XM)).1 := by
  set η : Aut (P.simul Q) := (P.simulAutSnd Q) (φ γ) with hη
  have key : rM.homEquiv ((rM.autMulHom η).inv) =
      (P.simul Q).map (rM.autMulHom η).inv.op (rM.homEquiv (𝟙 XM)) := by
    conv_lhs => rw [show (rM.autMulHom η).inv =
      (rM.autMulHom η).inv ≫ 𝟙 XM from (Category.comp_id _).symm]
    exact rM.homEquiv_comp _ _
  have key2 : rM.homEquiv ((rM.autMulHom η).inv) =
      η.inv.app (op XM) (rM.homEquiv (𝟙 XM)) := by
    have h := rM.homEquiv_comp_transportHom η.inv (𝟙 XM)
    rw [Category.id_comp] at h
    exact h
  calc P.map (rM.autMulHom η).inv.op (rM.homEquiv (𝟙 XM)).1
      = (rM.homEquiv ((rM.autMulHom η).inv)).1 := (congrArg Prod.fst key).symm
    _ = (η.inv.app (op XM) (rM.homEquiv (𝟙 XM))).1 := congrArg Prod.fst key2
    _ = (rM.homEquiv (𝟙 XM)).1 := rfl

/-- **([a2]–[a5] interface — the geometric core of the KM 4.7.0 engine; residual sorry.)**
The free quotient of the simultaneous representing object by the KM action, as an
`Ell/R`-morphism `q : XM ⟶ X₀` exposing exactly what the representability bijection
consumes:

* `hqfull` — `Ell/R`-level `G`-invariance `(A γ).inv ≫ q = q` (both the base and the
  curve-level quotient projections are invariant *by construction*);
* `hqepi`/`hqlift` — the quotient universal property on the base (consumed by the [B1]
  α-descent `existsUnique_alpha_descent`);
* `hqsurj`/`hqetale` — `q.baseHom` is a surjective étale cover (finite étale `G`-torsor
  grade; consumed by the KM pp. 114–116 bijection through `Flat`+`Surjective`).

**Why this is a sorry here**: the construction is the route-(a) Phase-A engine —
`SchemeAction.quotient` on the `⊤`-atlas of the affine base, `exists_quotient_π_zero` +
`locallyWeierstrass_quotientπ` ([a5]) + `isPullback_quotientπ` for the descended curve
(`exists_ellipticCurveGeom_quotient`, `Moduli/EngineDescent.lean`), and
`etale_quotientπ`/`quotientπ_surjective`/`existsUnique_quotientπ_lift`/`quotientπ_hom_ext`
(`ForMathlib/SchemeActionFree.lean` + `ForMathlib/SchemeQuotient.lean`) for the exposed
properties — but `EngineDescent.lean` **imports this file**, so the assembled engine cannot
be consumed here. Discharge downstream by proving this exact statement from those pieces
(mirroring `exists_coreData`, `Moduli/QuotientRepresentability.lean`, which does precisely
this at the `_of_globalModel` variant; note the model-free
`exists_ellipticCurveGeom_quotient` interface does not expose the curve-level invariance
`hqinv_eng` — take it from `SchemeAction.hom_quotientπ` on the internals, as
`exists_coreData` does). Freeness is a *hypothesis* here, so no rigidity enters. -/
private theorem exists_engineQuotient (P Q : ModuliProblem R) {G : Type u} [Group G]
    [Finite G] (φ : G →* Aut Q) {XM : EllObj R}
    (rM : (P.simul Q).RepresentableBy XM) (haff : IsAffine XM.base)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ XM.base),
      t ≫ (P.simulSchemeAction Q φ rM).hom γ = t → IsEmpty T) :
    ∃ (X₀ : EllObj R) (q : XM ⟶ X₀),
      (∀ γ : G, (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv ≫ q = q) ∧
      Epi q.baseHom ∧
      (∀ {W : Scheme.{u}} (F : XM.base ⟶ W),
        (∀ γ : G, (P.simulSchemeAction Q φ rM).hom γ ≫ F = F) →
          ∃ F₀ : X₀.base ⟶ W, q.baseHom ≫ F₀ = F) ∧
      Surjective q.baseHom ∧ Etale q.baseHom := by
  sorry

/-- The δ-torsor classifying morphism of a `P`-class (KM p. 114): the `Ell/R`-morphism
`Y ×_{Y.base} δ_{E_Y} ⟶ 𝕸(𝒫,δ)` classifying the pair `(α|_chart, β_univ)` — the pulled-back
`P`-class together with the tautological `δ`-structure of the torsor chart. -/
private noncomputable def classifyTorsor {P Q : ModuliProblem R} {G : Type u} [Group G]
    [Finite G] {φ : G →* Aut Q} {XM : EllObj R} (rM : (P.simul Q).RepresentableBy XM)
    {Y : EllObj R} (td : TorsorData φ Y) (α : P.obj (op Y)) :
    Y.pullbackAlong td.f ⟶ XM :=
  rM.homEquiv.symm (P.map (Y.pullbackAlongπ td.f).op α,
    td.eqv td.f ⟨𝟙 td.Z, Category.id_comp td.f⟩)

private theorem classifyTorsor_homEquiv {P Q : ModuliProblem R} {G : Type u} [Group G]
    [Finite G] {φ : G →* Aut Q} {XM : EllObj R} (rM : (P.simul Q).RepresentableBy XM)
    {Y : EllObj R} (td : TorsorData φ Y) (α : P.obj (op Y)) :
    rM.homEquiv (classifyTorsor rM td α) =
      (P.map (Y.pullbackAlongπ td.f).op α,
        td.eqv td.f ⟨𝟙 td.Z, Category.id_comp td.f⟩) :=
  rM.homEquiv.apply_symm_apply _

/-- **G-equivariance of the classifying morphism** (KM p. 115): the deck transformation
`σZ.hom γ` of the δ-torsor precomposes into `classifyTorsor` as postcomposition by
`(A γ⁻¹).hom` on `𝕸(𝒫,δ)` (the `γ⁻¹` is the [B2-TD-CONV] convention of
`TorsorData.equivariant`; consumers absorb it through their `∀ γ`-invariance inputs). -/
private theorem deck_classifyTorsor_comm {P Q : ModuliProblem R} {G : Type u} [Group G]
    [Finite G] {φ : G →* Aut Q} {XM : EllObj R} (rM : (P.simul Q).RepresentableBy XM)
    {Y : EllObj R} (td : TorsorData φ Y) (α : P.obj (op Y)) (γ : G) :
    EllObj.homToPullbackAlong (Y.pullbackAlongπ td.f) (td.σZ.hom γ) (td.over_base γ) ≫
        classifyTorsor rM td α =
      classifyTorsor rM td α ≫ (rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).hom := by
  set ρ : Y.pullbackAlong td.f ⟶ Y.pullbackAlong td.f :=
    EllObj.homToPullbackAlong (Y.pullbackAlongπ td.f) (td.σZ.hom γ) (td.over_base γ) with hρ
  have hHEc := classifyTorsor_homEquiv rM td α
  apply rM.homEquiv.injective
  rw [rM.homEquiv_comp, hHEc,
    show (rM.autMulHom ((P.simulAutSnd Q) (φ γ⁻¹))).hom
        = rM.transportHom ((P.simulAutSnd Q) (φ γ⁻¹)).hom from rfl,
    rM.homEquiv_comp_transportHom, hHEc]
  refine Prod.ext ?_ ?_
  · show P.map ρ.op (P.map (Y.pullbackAlongπ td.f).op α)
        = P.map (Y.pullbackAlongπ td.f).op α
    rw [← Functor.map_comp_apply, ← op_comp, hρ,
      EllObj.homToPullbackAlong_pullbackAlongπ]
  · show Q.map ρ.op (td.eqv td.f ⟨𝟙 td.Z, Category.id_comp td.f⟩) =
      (φ γ⁻¹).hom.app (op (Y.pullbackAlong td.f))
        (td.eqv td.f ⟨𝟙 td.Z, Category.id_comp td.f⟩)
    rw [hρ, map_eqv td.toRelRepData
      (EllObj.homToPullbackAlong (Y.pullbackAlongπ td.f) (td.σZ.hom γ) (td.over_base γ))
      (td.σZ.hom γ) (EllObj.homToPullbackAlong_baseHom _ _ _) (td.over_base γ)
      (EllObj.homToPullbackAlong_pullbackAlongπ _ _ _) ⟨𝟙 td.Z, Category.id_comp td.f⟩]
    exact Eq.trans (congrArg (td.eqv td.f) (Subtype.ext
        (show td.σZ.hom γ ≫ 𝟙 td.Z = 𝟙 td.Z ≫ td.σZ.hom γ by
          rw [Category.comp_id, Category.id_comp])))
      (td.equivariant td.f ⟨𝟙 td.Z, Category.id_comp td.f⟩ γ)

/-- **Descent of a `G`-deck-invariant `Ell/R`-morphism along the δ-torsor** (KM p. 115):
a morphism `g : Y ×_{Y.base} δ_{E_Y} ⟶ X` invariant under the deck action descends through
the torsor chart projection. The base map descends by `existsUnique_descent_of_torsor`, the
curve top by the same on the fppf curve-torsor (base change of `td.f`,
`isIso_torsorCompare_pullback`), `base_w`/`zero_w` by `td.f` epi, and the cartesian square
by fppf descent (`isPullback_of_fppf_baseChange`). -/
private theorem descend_deckInvariant {Q : ModuliProblem R} {G : Type u} [Group G]
    [Finite G] {φ : G →* Aut Q} {Y : EllObj R} (td : TorsorData φ Y)
    [Surjective td.f] [Flat td.f] [QuasiCompact td.f] {X : EllObj R}
    (g : Y.pullbackAlong td.f ⟶ X)
    (hg : ∀ γ, EllObj.homToPullbackAlong (Y.pullbackAlongπ td.f) (td.σZ.hom γ)
      (td.over_base γ) ≫ g = g) :
    ∃ v : Y ⟶ X, Y.pullbackAlongπ td.f ≫ v = g := by
  haveI : Epi td.f := AlgebraicGeometry.Flat.epi_of_flat_of_surjective td.f
  -- pin the deck endomorphism's type so its `.top`/`.isPullback` are well-formed
  let ρ : G → (Y.pullbackAlong td.f ⟶ Y.pullbackAlong td.f) :=
    fun γ => EllObj.homToPullbackAlong (Y.pullbackAlongπ td.f) (td.σZ.hom γ) (td.over_base γ)
  have hρg : ∀ γ, ρ γ ≫ g = g := hg
  have hρπ : ∀ γ, ρ γ ≫ Y.pullbackAlongπ td.f = Y.pullbackAlongπ td.f :=
    fun γ => EllObj.homToPullbackAlong_pullbackAlongπ _ _ _
  -- (a) descend the base map
  have hgb : ∀ γ, td.σZ.hom γ ≫ g.baseHom = g.baseHom :=
    fun γ => congrArg EllHom.baseHom (hρg γ)
  obtain ⟨f₀, hf₀, -⟩ :=
    existsUnique_descent_of_torsor td.σZ td.over_base td.torsor g.baseHom hgb
  -- (b) descend the curve top along the fppf curve-torsor `pullback.snd td.f Y.curve.π`
  haveI : Surjective (pullback.snd td.f Y.curve.π) :=
    MorphismProperty.pullback_snd _ _ ‹Surjective td.f›
  haveI : Flat (pullback.snd td.f Y.curve.π) := MorphismProperty.pullback_snd _ _ ‹Flat td.f›
  haveI : QuasiCompact (pullback.snd td.f Y.curve.π) :=
    MorphismProperty.pullback_snd _ _ ‹QuasiCompact td.f›
  -- the curve deck action, typed as an endomorphism of `pullback Y.curve.π td.f`
  let τ : G → (pullback Y.curve.π td.f ⟶ pullback Y.curve.π td.f) := fun γ => (ρ γ).top
  have hτg : ∀ γ, τ γ ≫ g.top = g.top := fun γ => congrArg EllHom.top (hρg γ)
  have hmap : ∀ γ, (pullbackTorsorAction td.σZ td.over_base Y.curve.π).hom γ ≫
      pullback.fst td.f Y.curve.π = pullback.fst td.f Y.curve.π ≫ td.σZ.hom γ := by
    intro γ; rw [pullbackTorsorAction_hom]; simp [pullback.map, pullback.lift_fst]
  have hcomm : ∀ γ, (pullbackTorsorAction td.σZ td.over_base Y.curve.π).hom γ ≫
        (pullbackSymmetry td.f Y.curve.π).hom =
      (pullbackSymmetry td.f Y.curve.π).hom ≫ τ γ := by
    intro γ
    have hρfst : τ γ ≫ pullback.fst Y.curve.π td.f = pullback.fst Y.curve.π td.f :=
      congrArg EllHom.top (hρπ γ)
    have hρsnd : τ γ ≫ pullback.snd Y.curve.π td.f =
        pullback.snd Y.curve.π td.f ≫ td.σZ.hom γ := (ρ γ).isPullback.w
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, pullbackTorsorAction_over,
        Category.assoc, hρfst, pullbackSymmetry_hom_comp_fst]
    · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, Category.assoc, hρsnd, ← Category.assoc,
        pullbackSymmetry_hom_comp_snd]
      exact hmap γ
  have hinv_curve : ∀ γ, (pullbackTorsorAction td.σZ td.over_base Y.curve.π).hom γ ≫
      ((pullbackSymmetry td.f Y.curve.π).hom ≫ g.top) =
      (pullbackSymmetry td.f Y.curve.π).hom ≫ g.top := by
    intro γ
    rw [← Category.assoc, hcomm γ, Category.assoc, hτg γ]
  obtain ⟨vtop, hvtop_raw, -⟩ :=
    existsUnique_descent_of_torsor (pullbackTorsorAction td.σZ td.over_base Y.curve.π)
      (pullbackTorsorAction_over td.σZ td.over_base Y.curve.π)
      (isIso_torsorCompare_pullback td.σZ td.over_base td.torsor Y.curve.π)
      ((pullbackSymmetry td.f Y.curve.π).hom ≫ g.top) hinv_curve
  have hvtop : (Y.pullbackAlongπ td.f).top ≫ vtop = g.top := by
    have h := hvtop_raw
    rw [← pullbackSymmetry_hom_comp_fst td.f Y.curve.π, Category.assoc] at h
    exact (cancel_epi (pullbackSymmetry td.f Y.curve.π).hom).mp h
  -- (c) `base_w`/`zero_w` by `td.f`-epi; the cartesian square is the fppf descent of
  -- `g.isPullback`.
  have hbw : f₀ ≫ X.structMap = Y.structMap := by
    refine (cancel_epi td.f).mp ?_
    rw [← Category.assoc, hf₀]; exact g.base_w
  have hz0 : (Y.pullbackAlong td.f).curve.zero ≫ (Y.pullbackAlongπ td.f).top =
      td.f ≫ Y.curve.zero := (Y.pullbackAlongπ td.f).zero_w
  have hzero : Y.curve.zero ≫ vtop = f₀ ≫ X.curve.zero := by
    refine (cancel_epi td.f).mp ?_
    rw [← Category.assoc, ← Category.assoc, hf₀]
    exact (congrArg (· ≫ vtop) hz0.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg ((Y.pullbackAlong td.f).curve.zero ≫ ·) hvtop).trans g.zero_w))
  -- the curve cartesian square is the fppf descent of `g.isPullback` along `td.f`.
  have hvtop' : pullback.fst Y.curve.π td.f ≫ vtop = g.top := hvtop
  have hbc : IsPullback (pullback.fst Y.curve.π td.f ≫ vtop) (pullback.snd Y.curve.π td.f)
      X.curve.π (td.f ≫ f₀) := by
    rw [hvtop', hf₀]; exact g.isPullback
  have hw : vtop ≫ X.curve.π = Y.curve.π ≫ f₀ := by
    refine (cancel_epi (pullback.fst Y.curve.π td.f)).mp ?_
    rw [reassoc_of% hvtop', reassoc_of% pullback.condition, hf₀]
    exact g.isPullback.w
  have hsq : IsPullback vtop Y.curve.π X.curve.π f₀ :=
    isPullback_of_fppf_baseChange hw td.f hbc
  exact ⟨{ baseHom := f₀, base_w := hbw, top := vtop, isPullback := hsq, zero_w := hzero },
    EllHom.ext hf₀ hvtop⟩

/-- **fppf-separatedness of a relatively representable `P` along a flat cover** (KM 4.1):
restriction of `P`-values along the chart projection `Y.pullbackAlongπ f` of a flat,
locally-finitely-presented, surjective `f` is injective, given a relative representation
datum for `P` at `Y`. -/
private theorem map_pullbackAlongπ_injective {P : ModuliProblem R} {Y : EllObj R}
    (d : RelRepData P Y) {Z : Scheme.{u}} (f : Z ⟶ Y.base)
    [Flat f] [LocallyOfFinitePresentation f] [Surjective f]
    {a b : P.obj (op Y)}
    (hab : P.map (Y.pullbackAlongπ f).op a = P.map (Y.pullbackAlongπ f).op b) : a = b := by
  haveI : Epi f := AlgebraicGeometry.Flat.epi_of_flat_of_surjective f
  -- comparison `w = π_f ≫ (Y ≅ Y.pullbackAlong 𝟙)` from the identity chart, lying over `f`
  have hmid : (EllObj.isoPullbackAlong (𝟙 Y)).hom ≫ Y.pullbackAlongπ (𝟙 Y.base) = 𝟙 Y :=
    EllObj.toPullbackAlong_pullbackAlongπ (𝟙 Y)
  have hwπ : (Y.pullbackAlongπ f ≫ (EllObj.isoPullbackAlong (𝟙 Y)).hom) ≫
      Y.pullbackAlongπ (𝟙 Y.base) = Y.pullbackAlongπ f := by
    rw [Category.assoc, hmid, Category.comp_id]
  -- each `P`-value over `Y`, restricted along `π_f`, is the chart-`f` value of `f ≫ (its
  -- identity-chart classifying section)` (`map_eqv` handles the `k ≫ g` bookkeeping)
  have hae : ∀ c : P.obj (op Y), P.map (Y.pullbackAlongπ f).op c =
      d.eqv f ⟨f ≫ ((d.eqv (𝟙 Y.base)).symm
          (P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op c)).1,
        by rw [Category.assoc, ((d.eqv (𝟙 Y.base)).symm
          (P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op c)).2, Category.comp_id]⟩ := by
    intro c
    have hc : c = P.map (EllObj.isoPullbackAlong (𝟙 Y)).hom.op (d.eqv (𝟙 Y.base)
        ((d.eqv (𝟙 Y.base)).symm (P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op c))) := by
      rw [Equiv.apply_symm_apply, ← Functor.map_comp_apply, ← op_comp, Iso.hom_inv_id, op_id,
        Functor.map_id_apply]
    conv_lhs => rw [hc, ← Functor.map_comp_apply, ← op_comp]
    exact map_eqv d (Y.pullbackAlongπ f ≫ (EllObj.isoPullbackAlong (𝟙 Y)).hom) f
      (by show f ≫ 𝟙 Y.base = f; exact Category.comp_id f)
      (Category.comp_id f) hwπ _
  rw [hae a, hae b] at hab
  have hfeq : f ≫ ((d.eqv (𝟙 Y.base)).symm
        (P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op a)).1 =
      f ≫ ((d.eqv (𝟙 Y.base)).symm
        (P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op b)).1 :=
    congrArg Subtype.val ((d.eqv f).injective hab)
  have hsec : (d.eqv (𝟙 Y.base)).symm (P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op a) =
      (d.eqv (𝟙 Y.base)).symm (P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op b) :=
    Subtype.ext ((cancel_epi f).mp hfeq)
  have hval : P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op a =
      P.map (EllObj.isoPullbackAlong (𝟙 Y)).inv.op b := by
    have hh := congrArg (d.eqv (𝟙 Y.base)) hsec
    rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hh
  have hfin := congrArg (P.map (EllObj.isoPullbackAlong (𝟙 Y)).hom.op) hval
  rwa [← Functor.map_comp_apply, ← op_comp, Iso.hom_inv_id, op_id, Functor.map_id_apply,
    ← Functor.map_comp_apply, ← op_comp, Iso.hom_inv_id, op_id, Functor.map_id_apply] at hfin

/-- **Existence of the descended morphism** (KM p. 115, the surjectivity substrate): the
composite `classifyTorsor α ≫ q` is deck-invariant (equivariance of the classifier + the
`Ell/R`-level `q`-invariance), hence descends through the δ-torsor chart projection. -/
private theorem exists_descended {P Q : ModuliProblem R} {G : Type u} [Group G] [Finite G]
    {φ : G →* Aut Q} {XM X₀ : EllObj R} (rM : (P.simul Q).RepresentableBy XM)
    (q : XM ⟶ X₀)
    (hqfull : ∀ γ : G, (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv ≫ q = q)
    {Y : EllObj R} (td : TorsorData φ Y) (α : P.obj (op Y)) :
    ∃ v : Y ⟶ X₀, Y.pullbackAlongπ td.f ≫ v = classifyTorsor rM td α ≫ q := by
  haveI := td.surjective
  haveI := td.etale
  haveI := td.finite
  haveI : Flat td.f := inferInstance
  haveI : QuasiCompact td.f := inferInstance
  have hAq : ∀ γ : G, (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).hom ≫ q = q := by
    intro γ
    calc (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).hom ≫ q
        = (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).hom ≫
            ((rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv ≫ q) := by rw [hqfull γ]
      _ = ((rM.autMulHom ((P.simulAutSnd Q) (φ γ))).hom ≫
            (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv) ≫ q :=
          (Category.assoc _ _ _).symm
      _ = 𝟙 XM ≫ q := by rw [(rM.autMulHom ((P.simulAutSnd Q) (φ γ))).hom_inv_id]
      _ = q := Category.id_comp q
  have hg_inv : ∀ γ,
      EllObj.homToPullbackAlong (Y.pullbackAlongπ td.f) (td.σZ.hom γ) (td.over_base γ) ≫
        (classifyTorsor rM td α ≫ q) = classifyTorsor rM td α ≫ q := by
    intro γ
    rw [← Category.assoc, deck_classifyTorsor_comm rM td α γ, Category.assoc, hAq γ⁻¹]
  exact descend_deckInvariant td (classifyTorsor rM td α ≫ q) hg_inv

/-- **The descended morphism classifies `α`** (KM p. 115, surjectivity): if
`π_td ≫ v = classifyTorsor α ≫ q`, then `P.map v.op α₀ = α` — both sides restrict equally
along the fppf chart projection, which is injective on `P`-values. -/
private theorem map_descended {P Q : ModuliProblem R} {G : Type u} [Group G] [Finite G]
    {φ : G →* Aut Q} {XM X₀ : EllObj R} (rM : (P.simul Q).RepresentableBy XM)
    (q : XM ⟶ X₀) (α₀ : P.obj (op X₀))
    (hα₀ : P.map q.op α₀ = (rM.homEquiv (𝟙 XM)).1)
    {Y : EllObj R} (td : TorsorData φ Y) (dY : RelRepData P Y) (α : P.obj (op Y))
    (v : Y ⟶ X₀) (hv : Y.pullbackAlongπ td.f ≫ v = classifyTorsor rM td α ≫ q) :
    P.map v.op α₀ = α := by
  haveI := td.surjective
  haveI := td.etale
  haveI := td.finite
  haveI : Flat td.f := inferInstance
  haveI : LocallyOfFinitePresentation td.f := inferInstance
  have key : P.map (Y.pullbackAlongπ td.f).op (P.map v.op α₀) =
      P.map (Y.pullbackAlongπ td.f).op α := by
    have e1 : P.map (Y.pullbackAlongπ td.f).op (P.map v.op α₀) =
        P.map (classifyTorsor rM td α ≫ q).op α₀ := by
      rw [← Functor.map_comp_apply, ← op_comp, hv]
    have hHE : rM.homEquiv (classifyTorsor rM td α) =
        (P.simul Q).map (classifyTorsor rM td α).op (rM.homEquiv (𝟙 XM)) := by
      conv_lhs => rw [← Category.comp_id (classifyTorsor rM td α)]
      exact rM.homEquiv_comp _ _
    have e2 : P.map (classifyTorsor rM td α ≫ q).op α₀ =
        (rM.homEquiv (classifyTorsor rM td α)).1 := by
      rw [op_comp, Functor.map_comp_apply, hα₀]
      exact (congrArg Prod.fst hHE).symm
    have e3 : (rM.homEquiv (classifyTorsor rM td α)).1 =
        P.map (Y.pullbackAlongπ td.f).op α :=
      congrArg Prod.fst (classifyTorsor_homEquiv rM td α)
    rw [e1, e2, e3]
  exact map_pullbackAlongπ_injective dY td.f key

/-- **Uniqueness by retraction** (KM pp. 115–116, rigidity-free form): any `v` inducing `α`
equals the canonically descended morphism `v'`. Over the `q`-pulled-back chart of `v`, the
lift `μv` of `π ≫ v` through `q` is classified by `(α|_chart, δ-value)`, so it factors as
`θ̃ ≫ classifyTorsor α`; composing with `q` gives `π_s ≫ v = π_s ≫ v'`, and the fppf chart
projection `π_s` cancels componentwise. No rigidity at `Y` is consumed — this is the
statement-level discovery that lets the engine mouth run at `RigidNoeth`. -/
private theorem eq_descended {P Q : ModuliProblem R} {G : Type u} [Group G] [Finite G]
    {φ : G →* Aut Q} {XM X₀ : EllObj R} (rM : (P.simul Q).RepresentableBy XM)
    (q : XM ⟶ X₀) (α₀ : P.obj (op X₀))
    (hα₀ : P.map q.op α₀ = (rM.homEquiv (𝟙 XM)).1)
    (hqsurj : Surjective q.baseHom) (hqetale : Etale q.baseHom)
    {Y : EllObj R} (td : TorsorData φ Y) (α : P.obj (op Y)) (v' : Y ⟶ X₀)
    (hv' : Y.pullbackAlongπ td.f ≫ v' = classifyTorsor rM td α ≫ q)
    (v : Y ⟶ X₀) (hvα : P.map v.op α₀ = α) : v = v' := by
  haveI := hqsurj
  haveI := hqetale
  haveI : Flat q.baseHom := inferInstance
  -- the pulled-back `G`-torsor chart of `v` along `q.baseHom`
  set fstv : pullback q.baseHom v.baseHom ⟶ XM.base := pullback.fst q.baseHom v.baseHom
    with hfstv
  set sndv : pullback q.baseHom v.baseHom ⟶ Y.base := pullback.snd q.baseHom v.baseHom
    with hsndv
  have hcond : fstv ≫ q.baseHom = sndv ≫ v.baseHom := pullback.condition
  -- the lift `μv` of `π_sndv ≫ v` through `q`, over the pulled-back chart
  have hqiso : (EllObj.isoPullbackAlong q).inv ≫ q = X₀.pullbackAlongπ q.baseHom := by
    rw [Iso.inv_comp_eq]
    exact (EllObj.toPullbackAlong_pullbackAlongπ q).symm
  have hh : fstv ≫ q.baseHom = (Y.pullbackAlongπ sndv ≫ v).baseHom := hcond
  set muv : Y.pullbackAlong sndv ⟶ XM :=
    EllObj.homToPullbackAlong (Y.pullbackAlongπ sndv ≫ v) fstv hh ≫
      (EllObj.isoPullbackAlong q).inv with hmuv
  have hmuvq : muv ≫ q = Y.pullbackAlongπ sndv ≫ v := by
    rw [hmuv, Category.assoc, hqiso, EllObj.homToPullbackAlong_pullbackAlongπ]
  -- the `P`-value of `μv`
  have hHE : rM.homEquiv muv = (P.simul Q).map muv.op (rM.homEquiv (𝟙 XM)) := by
    conv_lhs => rw [← Category.comp_id muv]
    exact rM.homEquiv_comp muv (𝟙 XM)
  have hPval : (rM.homEquiv muv).1 = P.map (Y.pullbackAlongπ sndv).op α := by
    have hP1 : (rM.homEquiv muv).1 = P.map muv.op (rM.homEquiv (𝟙 XM)).1 :=
      congrArg Prod.fst hHE
    rw [hP1, ← hα₀, ← Functor.map_comp_apply, ← op_comp, hmuvq, op_comp,
      Functor.map_comp_apply, hvα]
  -- the `δ`-value of `μv`, classified into the δ-torsor `td.Z`
  set dv : Q.obj (op (Y.pullbackAlong sndv)) := (rM.homEquiv muv).2 with hdv
  set θs : { h : pullback q.baseHom v.baseHom ⟶ td.Z // h ≫ td.f = sndv } :=
    (td.eqv sndv).symm dv with hθs
  have hθeqv : td.eqv sndv θs = dv := (td.eqv sndv).apply_symm_apply dv
  -- the chart comparison over `θs.1`
  set θtil : Y.pullbackAlong sndv ⟶ Y.pullbackAlong td.f :=
    EllObj.homToPullbackAlong (Y.pullbackAlongπ sndv) θs.1 θs.2 with hθtil
  have hθtilπ : θtil ≫ Y.pullbackAlongπ td.f = Y.pullbackAlongπ sndv :=
    EllObj.homToPullbackAlong_pullbackAlongπ _ _ _
  -- KEY classifier identity: `μv = θtil ≫ classifyTorsor α`
  have hmuv_eq : muv = θtil ≫ classifyTorsor rM td α := by
    apply rM.homEquiv.injective
    rw [rM.homEquiv_comp θtil (classifyTorsor rM td α), classifyTorsor_homEquiv]
    refine Prod.ext ?_ ?_
    · show (rM.homEquiv muv).1 = P.map θtil.op (P.map (Y.pullbackAlongπ td.f).op α)
      rw [hPval]
      conv_rhs => rw [← Functor.map_comp_apply, ← op_comp, hθtilπ]
    · show (rM.homEquiv muv).2 =
        Q.map θtil.op (td.eqv td.f ⟨𝟙 td.Z, Category.id_comp td.f⟩)
      rw [← hdv, ← hθeqv, hθtil,
        map_eqv td.toRelRepData _ θs.1 (EllObj.homToPullbackAlong_baseHom _ _ _) θs.2
          (EllObj.homToPullbackAlong_pullbackAlongπ _ _ _)
          ⟨𝟙 td.Z, Category.id_comp td.f⟩]
      exact congrArg (td.eqv sndv) (Subtype.ext (Category.comp_id θs.1).symm)
  -- the retraction: `π_sndv ≫ v = π_sndv ≫ v'`
  have hchain : Y.pullbackAlongπ sndv ≫ v = Y.pullbackAlongπ sndv ≫ v' := by
    calc Y.pullbackAlongπ sndv ≫ v
        = muv ≫ q := hmuvq.symm
      _ = (θtil ≫ classifyTorsor rM td α) ≫ q := by rw [← hmuv_eq]
      _ = θtil ≫ classifyTorsor rM td α ≫ q := Category.assoc _ _ _
      _ = θtil ≫ Y.pullbackAlongπ td.f ≫ v' := by rw [← hv']
      _ = (θtil ≫ Y.pullbackAlongπ td.f) ≫ v' := (Category.assoc _ _ _).symm
      _ = Y.pullbackAlongπ sndv ≫ v' := by rw [hθtilπ]
  -- cancel the fppf chart projection componentwise
  haveI : Flat sndv := by
    rw [hsndv]; exact MorphismProperty.pullback_snd _ _ ‹Flat q.baseHom›
  haveI : Surjective sndv := by
    rw [hsndv]; exact MorphismProperty.pullback_snd _ _ ‹Surjective q.baseHom›
  haveI : Epi sndv := AlgebraicGeometry.Flat.epi_of_flat_of_surjective sndv
  haveI : Flat (pullback.fst Y.curve.π sndv) :=
    MorphismProperty.pullback_fst _ _ ‹Flat sndv›
  haveI : Surjective (pullback.fst Y.curve.π sndv) :=
    MorphismProperty.pullback_fst _ _ ‹Surjective sndv›
  haveI : Epi (pullback.fst Y.curve.π sndv) :=
    AlgebraicGeometry.Flat.epi_of_flat_of_surjective _
  refine EllHom.ext ?_ ?_
  · exact (cancel_epi sndv).mp (congrArg EllHom.baseHom hchain)
  · exact (cancel_epi (pullback.fst Y.curve.π sndv)).mp (congrArg EllHom.top hchain)

/-- **The Katz–Mazur 4.7 engine at noetherian-local rigidity** ([T-W7.8] variant mouth,
CHARTER-GH wire): `representable_of_rigid_of_torsor` with the rigidity input weakened to
`RigidNoeth` — the form the `Γ_H` headline chain supplies (`representable_iff_rigidNoeth`'s
`⇐` consumes THIS statement at the two bootstrap instantiations).

Proof (KM pp. 112–116): `𝕸(𝒫,δ) = Xδ ×_{𝕸(δ)} Z_P` represents `𝒫.simul δ`
(`simulRepresentableBy`, PROVEN) with affine base; rigidity makes the KM action free —
the single rigidity call, already at `RigidNoeth` (`simulSchemeAction_free_of_rigidNoeth`,
PROVEN: emptiness of the fixed locus is detected on residue-field points); the free
quotient `q : 𝕸(𝒫,δ) ⟶ 𝕸(𝒫,δ)/G` in `Ell/R` is the route-(a) Phase-A engine
(`exists_engineQuotient` — the residual interface sorry, geometric and rigidity-free);
the universal `P`-class descends along `q` by the [B1] α-descent
(`existsUnique_alpha_descent`, PROVEN); and `(𝕸(𝒫,δ)/G, α₀)` represents `𝒫` by the
KM pp. 114–116 torsor bijection — surjectivity via `exists_descended`/`map_descended`,
uniqueness via the rigidity-free retraction `eq_descended` (all PROVEN). -/
theorem representable_of_rigidNoeth_of_torsor (P Q : ModuliProblem R)
    {G : Type u} [Group G] [Finite G] (φ : G →* Aut Q)
    (hQrep : Q.Representable)
    (hQaff : ∀ {XQ : EllObj R}, Q.RepresentableBy XQ → IsAffine XQ.base)
    (hPaff : ∀ X : EllObj R, ∃ d : RelRepData P X, IsAffineHom d.f)
    (htors : ∀ X : EllObj R, Nonempty (TorsorData φ X))
    (hrig : P.RigidNoeth) :
    P.Representable := by
  classical
  -- `𝕸(𝒫,δ)`: the simultaneous representing object, with affine base (KM 4.7 step (i))
  obtain ⟨Xδ, ⟨rδ⟩⟩ := hQrep.has_representation
  haveI hXδaff : IsAffine Xδ.base := hQaff rδ
  obtain ⟨dP, hdPf⟩ := hPaff Xδ
  haveI := hdPf
  set XM : EllObj R := Xδ.pullbackAlong dP.f with hXMdef
  set rM : (P.simul Q).RepresentableBy XM :=
    P.simulRepresentableBy Q rδ @dP.eqv @dP.nat with hrMdef
  have haffZ : IsAffine dP.Z := isAffine_of_isAffineHom dP.f
  have haff : IsAffine XM.base := haffZ
  -- freeness of the KM action, at `RigidNoeth` (the single rigidity call; PROVEN)
  have hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ XM.base),
      t ≫ (P.simulSchemeAction Q φ rM).hom γ = t → IsEmpty T :=
    fun γ hγ T t ht =>
      simulSchemeAction_free_of_rigidNoeth P Q φ rM hrig htors γ hγ T t ht
  -- the geometric core: the free quotient `q : 𝕸(𝒫,δ) ⟶ 𝕸(𝒫,δ)/G` (Phase A)
  obtain ⟨X₀, q, hqfull, hqepi, hqlift, hqsurj, hqetale⟩ :=
    exists_engineQuotient P Q φ rM haff hfree
  -- descend the universal `P`-class along `q` ([B1] α-descent, PROVEN)
  obtain ⟨d₀, -⟩ := hPaff X₀
  obtain ⟨α₀, hα₀, -⟩ :=
    existsUnique_alpha_descent q d₀ (P.simulSchemeAction Q φ rM)
      (fun γ => (rM.autMulHom ((P.simulAutSnd Q) (φ γ))).inv) (fun γ => rfl) hqfull
      (fun {W} F hF => hqlift F hF) hqepi
      ((rM.homEquiv (𝟙 XM)).1) (map_fst_autMulHom_inv φ rM)
  -- the representability bijection (KM pp. 114–116)
  suffices h : P.RepresentableBy X₀ from h.isRepresentable
  refine ⟨fun {Y} => Equiv.ofBijective (fun v => P.map v.op α₀) ⟨?_, ?_⟩, ?_⟩
  · -- injectivity: both morphisms retract onto the canonically descended one
    intro v₁ v₂ h12
    obtain ⟨td⟩ := htors Y
    obtain ⟨v0, hv0⟩ := exists_descended rM q hqfull td (P.map v₂.op α₀)
    exact (eq_descended rM q α₀ hα₀ hqsurj hqetale td _ v0 hv0 v₁ h12).trans
      (eq_descended rM q α₀ hα₀ hqsurj hqetale td _ v0 hv0 v₂ rfl).symm
  · -- surjectivity: descend the classifying morphism through the δ-torsor
    intro α
    obtain ⟨td⟩ := htors Y
    obtain ⟨dY, -⟩ := hPaff Y
    obtain ⟨v0, hv0⟩ := exists_descended rM q hqfull td α
    exact ⟨v0, map_descended rM q α₀ hα₀ td dY α v0 hv0⟩
  · -- naturality of the representation
    intro Y Y' k v
    show P.map (k ≫ v).op α₀ = P.map k.op (P.map v.op α₀)
    rw [op_comp, Functor.map_comp_apply]

/-- **The Katz–Mazur 4.7 engine** (SCHOLIE 4.7.0, axiomatized claim, KM p. 112:
"We claim that over `ℤ[1/N]`, `𝒫` is represented by the affine `ℤ[1/N]`-scheme
`𝕸(𝒫,δ)/G`"): a rigid, relatively representable moduli problem that is affine
over `(Ell)` is representable, given an auxiliary problem `δ` that is
representable by an affine scheme and carries a `G`-action making its relative
representing schemes finite étale `G`-torsors.

Immediate from the `RigidNoeth` form (`representable_of_rigidNoeth_of_torsor`) via
`Rigid.rigidNoeth`: the engine consumes rigidity only through freeness of the KM action,
which noetherian-local rigidity already yields. -/
theorem representable_of_rigid_of_torsor (P Q : ModuliProblem R)
    {G : Type u} [Group G] [Finite G] (φ : G →* Aut Q)
    (hQrep : Q.Representable)
    (hQaff : ∀ {XQ : EllObj R}, Q.RepresentableBy XQ → IsAffine XQ.base)
    (hPaff : ∀ X : EllObj R, ∃ d : RelRepData P X, IsAffineHom d.f)
    (htors : ∀ X : EllObj R, Nonempty (TorsorData φ X))
    (hrig : P.Rigid) :
    P.Representable :=
  representable_of_rigidNoeth_of_torsor P Q φ hQrep hQaff hPaff htors hrig.rigidNoeth

end EngineMouth

end ModuliProblem

end ModularCurves

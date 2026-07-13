/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.GammaHRepresentability
import ModularCurves.Moduli.QuotientRepresentability

/-!
# The Γ_H MASTER assembly (KM 4.7.0 applied to `P_H`) — interface

`Y_H` as a fine moduli scheme: the quotient problem `P_H = [Γ(N)]/H` (GHC1,
`gammaH_relativelyRepresentable`) fed to the [B3]/FP4 representability engine
(`representable_of_rigid_of_torsor_of_globalModel`, KM SCHOLIE 4.7.0 route (a)) with the
full-level problem as the auxiliary rigidifier.

**Interface-first** (fleet norm, v10.154 precedent): every input the engine needs is a
NAMED HYPOTHESIS here, so the seams are visible pins:

* `qpd` — GHC1's output (`gammaH_relativelyRepresentable`; sorryAx currently via [GH1]
  `gammaHAut` + [GHA3] `levelSpaceΓπ_etale` only);
* `hQrep` — representability of the full-level problem = the Y(N) MASTER
  (STREAM-YN's (C); consume by name when it lands);
* `htors` — the full-group torsor datum on the level scheme (c5β's
  `glSchemeSmul`/L4-seam layer; KM axiom 2 "δ_{E/S} is a finite étale G-torsor");
* `hrig` — rigidity of `P_H` (the classical `N ≥ 3` + `H`-condition; the geometric
  bridge `QuotientProblemData.rigid_of_geom_free` reduces it to orbit-freeness of
  `Aut(E)` on `H`-orbits over geometric points);
* `hQaff`/`hPaff`/`hmodel` — the engine's affineness/Weierstrass-model clauses
  (KM's standing "affine over (Ell)" hypotheses).

The assembly itself is pure: relative representability of `P_H` is repackaged from
`qpd.relRep` and everything else is the engine.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace ModularCurves

variable {R : CommRingCat.{u}}

/-! ### [RIG-3a] Fibres of base-identical `Ell/R`-endomorphisms

The geometric-fibre transport needed by the rigidity bridge: an endomorphism `e : X ⟶ X`
over the identity of the base restricts, along any `t : T ⟶ X.base`, to an endomorphism
of `X.pullbackAlong t` over `𝟙 T`, compatibly with the projection `pullbackAlongπ` and
with composition — so isos restrict to isos. -/

/-- The top-leg square of a base-identical endomorphism. -/
private theorem fibre_w₁ {X : EllObj R} (e : X ⟶ X) (he : e.baseHom = 𝟙 X.base) :
    X.curve.π ≫ 𝟙 X.base = e.top ≫ X.curve.π :=
  (Category.comp_id _).trans (e.isPullback.w.trans (by rw [he, Category.comp_id])).symm

private theorem fibre_w₂ {X : EllObj R} {T : Scheme.{u}} (t : T ⟶ X.base) :
    t ≫ 𝟙 X.base = 𝟙 T ≫ t := by
  rw [Category.comp_id, Category.id_comp]

open Limits in
/-- The fibre of a base-identical `Ell/R`-endomorphism along `t : T ⟶ X.base`. -/
noncomputable def EllHom.fibre {X : EllObj R} (e : X ⟶ X) (he : e.baseHom = 𝟙 X.base)
    {T : Scheme.{u}} (t : T ⟶ X.base) : X.pullbackAlong t ⟶ X.pullbackAlong t where
  baseHom := 𝟙 T
  base_w := Category.id_comp _
  top := pullback.map X.curve.π t X.curve.π t e.top (𝟙 T) (𝟙 X.base)
    (fibre_w₁ e he) (fibre_w₂ t)
  isPullback := by
    have hesq : IsPullback e.top X.curve.π X.curve.π (𝟙 X.base) := he ▸ e.isPullback
    have hbig := (IsPullback.of_hasPullback X.curve.π t).paste_horiz hesq
    rw [Category.comp_id] at hbig
    have hfst : pullback.map X.curve.π t X.curve.π t e.top (𝟙 T) (𝟙 X.base)
          (fibre_w₁ e he) (fibre_w₂ t) ≫ pullback.fst X.curve.π t =
        pullback.fst X.curve.π t ≫ e.top := pullback.lift_fst _ _ _
    rw [← hfst] at hbig
    refine IsPullback.of_right hbig ?_ (IsPullback.of_hasPullback X.curve.π t)
    show pullback.map X.curve.π t X.curve.π t e.top (𝟙 T) (𝟙 X.base)
        (fibre_w₁ e he) (fibre_w₂ t) ≫ pullback.snd X.curve.π t =
      pullback.snd X.curve.π t ≫ 𝟙 T
    rw [pullback.lift_snd]
  zero_w := by
    refine pullback.hom_ext ?_ ?_
    · show (pullback.lift (t ≫ X.curve.zero) (𝟙 T) _ ≫
          pullback.map X.curve.π t X.curve.π t e.top (𝟙 T) (𝟙 X.base)
            (fibre_w₁ e he) (fibre_w₂ t)) ≫ pullback.fst X.curve.π t =
        (𝟙 T ≫ pullback.lift (t ≫ X.curve.zero) (𝟙 T) _) ≫ pullback.fst X.curve.π t
      have hz : X.curve.zero ≫ e.top = X.curve.zero := by
        rw [e.zero_w, he, Category.id_comp]
      rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc, hz,
        Category.id_comp, pullback.lift_fst]
    · show (pullback.lift (t ≫ X.curve.zero) (𝟙 T) _ ≫
          pullback.map X.curve.π t X.curve.π t e.top (𝟙 T) (𝟙 X.base)
            (fibre_w₁ e he) (fibre_w₂ t)) ≫ pullback.snd X.curve.π t =
        (𝟙 T ≫ pullback.lift (t ≫ X.curve.zero) (𝟙 T) _) ≫ pullback.snd X.curve.π t
      rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id,
        Category.id_comp, pullback.lift_snd]

@[simp]
theorem EllHom.fibre_baseHom {X : EllObj R} (e : X ⟶ X) (he : e.baseHom = 𝟙 X.base)
    {T : Scheme.{u}} (t : T ⟶ X.base) : (e.fibre he t).baseHom = 𝟙 T := rfl

/-- The fibre construction is compatible with the tautological projection:
`fibre e ≫ π = π ≫ e`. -/
theorem EllHom.fibre_pullbackAlongπ {X : EllObj R} (e : X ⟶ X) (he : e.baseHom = 𝟙 X.base)
    {T : Scheme.{u}} (t : T ⟶ X.base) :
    e.fibre he t ≫ X.pullbackAlongπ t = X.pullbackAlongπ t ≫ e := by
  refine EllHom.ext ?_ ?_
  · show 𝟙 T ≫ t = t ≫ e.baseHom
    rw [Category.id_comp, he, Category.comp_id]
  · show Limits.pullback.map X.curve.π t X.curve.π t e.top (𝟙 T) (𝟙 X.base)
        (fibre_w₁ e he) (fibre_w₂ t) ≫ Limits.pullback.fst X.curve.π t =
      Limits.pullback.fst X.curve.π t ≫ e.top
    rw [Limits.pullback.lift_fst]

/-- The fibre construction is functorial: proof-irrelevant congruence. -/
theorem EllHom.fibre_congr {X : EllObj R} {e e' : X ⟶ X} (h : e = e')
    (he : e.baseHom = 𝟙 X.base) (he' : e'.baseHom = 𝟙 X.base)
    {T : Scheme.{u}} (t : T ⟶ X.base) : e.fibre he t = e'.fibre he' t := by
  subst h; rfl

/-- The fibre construction is functorial: composition. -/
theorem EllHom.fibre_comp {X : EllObj R} (e₁ e₂ : X ⟶ X)
    (he₁ : e₁.baseHom = 𝟙 X.base) (he₂ : e₂.baseHom = 𝟙 X.base)
    (hbc : (e₁ ≫ e₂).baseHom = 𝟙 X.base) {T : Scheme.{u}} (t : T ⟶ X.base) :
    (e₁ ≫ e₂).fibre hbc t = e₁.fibre he₁ t ≫ e₂.fibre he₂ t := by
  refine EllHom.ext ?_ ?_
  · show 𝟙 T = 𝟙 T ≫ 𝟙 T
    rw [Category.comp_id]
  · refine Limits.pullback.hom_ext ?_ ?_
    · show Limits.pullback.map X.curve.π t X.curve.π t (e₁ ≫ e₂).top (𝟙 T) (𝟙 X.base)
            (fibre_w₁ (e₁ ≫ e₂) hbc) (fibre_w₂ t) ≫ Limits.pullback.fst X.curve.π t =
        (Limits.pullback.map X.curve.π t X.curve.π t e₁.top (𝟙 T) (𝟙 X.base)
            (fibre_w₁ e₁ he₁) (fibre_w₂ t) ≫
          Limits.pullback.map X.curve.π t X.curve.π t e₂.top (𝟙 T) (𝟙 X.base)
            (fibre_w₁ e₂ he₂) (fibre_w₂ t)) ≫ Limits.pullback.fst X.curve.π t
      rw [Limits.pullback.lift_fst, Category.assoc, Limits.pullback.lift_fst,
        Limits.pullback.lift_fst_assoc]
      show Limits.pullback.fst X.curve.π t ≫ e₁.top ≫ e₂.top = _
      rw [← Category.assoc]
    · show Limits.pullback.map X.curve.π t X.curve.π t (e₁ ≫ e₂).top (𝟙 T) (𝟙 X.base)
            (fibre_w₁ (e₁ ≫ e₂) hbc) (fibre_w₂ t) ≫ Limits.pullback.snd X.curve.π t =
        (Limits.pullback.map X.curve.π t X.curve.π t e₁.top (𝟙 T) (𝟙 X.base)
            (fibre_w₁ e₁ he₁) (fibre_w₂ t) ≫
          Limits.pullback.map X.curve.π t X.curve.π t e₂.top (𝟙 T) (𝟙 X.base)
            (fibre_w₁ e₂ he₂) (fibre_w₂ t)) ≫ Limits.pullback.snd X.curve.π t
      rw [Limits.pullback.lift_snd, Category.assoc, Limits.pullback.lift_snd,
        Limits.pullback.lift_snd_assoc, Category.comp_id, Category.comp_id]

/-- The fibre construction is functorial: identity. -/
theorem EllHom.fibre_id (X : EllObj R) {T : Scheme.{u}} (t : T ⟶ X.base) :
    (𝟙 X : X ⟶ X).fibre rfl t = 𝟙 (X.pullbackAlong t) := by
  refine EllHom.ext rfl ?_
  refine Limits.pullback.hom_ext ?_ ?_
  · show Limits.pullback.map X.curve.π t X.curve.π t (𝟙 X : X ⟶ X).top (𝟙 T) (𝟙 X.base)
        (fibre_w₁ (𝟙 X) rfl) (fibre_w₂ t) ≫ Limits.pullback.fst X.curve.π t =
      (𝟙 (X.pullbackAlong t) : X.pullbackAlong t ⟶ X.pullbackAlong t).top ≫
        Limits.pullback.fst X.curve.π t
    rw [Limits.pullback.lift_fst]
    show Limits.pullback.fst X.curve.π t ≫ 𝟙 X.curve.E = 𝟙 _ ≫ Limits.pullback.fst X.curve.π t
    rw [Category.comp_id, Category.id_comp]
  · show Limits.pullback.map X.curve.π t X.curve.π t (𝟙 X : X ⟶ X).top (𝟙 T) (𝟙 X.base)
        (fibre_w₁ (𝟙 X) rfl) (fibre_w₂ t) ≫ Limits.pullback.snd X.curve.π t =
      (𝟙 (X.pullbackAlong t) : X.pullbackAlong t ⟶ X.pullbackAlong t).top ≫
        Limits.pullback.snd X.curve.π t
    rw [Limits.pullback.lift_snd, Category.comp_id]
    show Limits.pullback.snd X.curve.π t = 𝟙 _ ≫ Limits.pullback.snd X.curve.π t
    rw [Category.id_comp]

/-- The base component of the inverse of a base-identical iso is the identity. -/
theorem EllObj.isoInv_baseHom {X : EllObj R} (e : X ≅ X) (he : e.hom.baseHom = 𝟙 X.base) :
    e.inv.baseHom = 𝟙 X.base := by
  have h := congrArg EllHom.baseHom e.hom_inv_id
  show e.inv.baseHom = 𝟙 X.base
  calc e.inv.baseHom = e.hom.baseHom ≫ e.inv.baseHom := by rw [he, Category.id_comp]
    _ = 𝟙 X.base := h

/-- **The fibre of a base-identical iso** of an `Ell/R`-object along a point of the base. -/
noncomputable def EllObj.isoFibre {X : EllObj R} (e : X ≅ X) (he : e.hom.baseHom = 𝟙 X.base)
    {T : Scheme.{u}} (t : T ⟶ X.base) : X.pullbackAlong t ≅ X.pullbackAlong t where
  hom := e.hom.fibre he t
  inv := e.inv.fibre (EllObj.isoInv_baseHom e he) t
  hom_inv_id := by
    have h₁₂ : (e.hom ≫ e.inv).baseHom = 𝟙 X.base := by rw [e.hom_inv_id]; rfl
    rw [← EllHom.fibre_comp e.hom e.inv he (EllObj.isoInv_baseHom e he) h₁₂ t,
      EllHom.fibre_congr e.hom_inv_id h₁₂ rfl t, EllHom.fibre_id]
  inv_hom_id := by
    have h₂₁ : (e.inv ≫ e.hom).baseHom = 𝟙 X.base := by rw [e.inv_hom_id]; rfl
    rw [← EllHom.fibre_comp e.inv e.hom (EllObj.isoInv_baseHom e he) he h₂₁ t,
      EllHom.fibre_congr e.inv_hom_id h₂₁ rfl t, EllHom.fibre_id]

/-- Over an empty base every `Ell/R`-self-iso is the identity: the base and the total
space are initial schemes. -/
theorem EllObj.iso_eq_refl_of_isEmpty {X : EllObj R} (h : IsEmpty X.base) (e : X ≅ X) :
    e = Iso.refl X := by
  haveI := h
  haveI : IsEmpty X.curve.E := X.curve.π.base.hom.1.isEmpty
  refine Iso.ext (EllHom.ext ?_ ?_)
  · exact (isInitialOfIsEmpty (X := X.base)).hom_ext _ _
  · exact (isInitialOfIsEmpty (X := X.curve.E)).hom_ext _ _

/-- **[RIG-3b] The rigidity bridge**: a quotient problem datum is rigid provided
(1) nontriviality of base-identical isos is DETECTED on some geometric fibre
(`hdetect` — [RIG-1], KM 2.7-adjacent), and (2) no nontrivial geometric iso fixes a
`γ`-twisted value of `Q` (`hfree` — [RIG-2], the k̄ orbit-freeness; for `Γ_H` this is
the `N ≥ 3` Serre argument + the `H`-condition).

Route: a fixed `prob`-value transports to a geometric fibre where the iso stays
nontrivial (`EllHom.fibre` machinery); `geom_surjective` lifts the fibre value to `Q`;
`geom_orbits` converts fixedness into a `γ`-twisted `Q`-fixed point, killed by `hfree`. -/
theorem ModuliProblem.QuotientProblemData.rigid_of_geom_free {Q : ModuliProblem R}
    {G : Type*} [Group G] [Finite G] {φ : G →* Aut Q}
    (qpd : ModuliProblem.QuotientProblemData φ)
    (hdetect : ∀ (X : EllObj R) (e : X ≅ X) (he : e.hom.baseHom = 𝟙 X.base),
      e ≠ Iso.refl X → Nonempty X.base →
      ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k)
        (t : Spec (CommRingCat.of k) ⟶ X.base), EllObj.isoFibre e he t ≠ Iso.refl _)
    (hfree : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (sm : Spec (CommRingCat.of k) ⟶ Spec R)
      (E : EllipticCurve (Spec (CommRingCat.of k)))
      (e : (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R) ≅
        (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)),
      e.hom.baseHom = 𝟙 _ → e ≠ Iso.refl _ →
      ∀ (b : Q.obj (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))) (γ : G),
        (φ γ).hom.app (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))
          (Q.map e.hom.op b) ≠ b) :
    qpd.prob.Rigid := by
  intro X e he hne a hfix
  by_cases hbase : Nonempty X.base
  · -- geometric fibre where `e` stays nontrivial
    obtain ⟨k, _, _, t, hfib⟩ := hdetect X e he hne hbase
    set eT := EllObj.isoFibre e he t with heT
    have hcomp : eT.hom ≫ X.pullbackAlongπ t = X.pullbackAlongπ t ≫ e.hom :=
      EllHom.fibre_pullbackAlongπ e.hom he t
    set aT := qpd.prob.map (X.pullbackAlongπ t).op a with haT
    have hfixT : qpd.prob.map eT.hom.op aT = aT := by
      calc qpd.prob.map eT.hom.op aT
          = qpd.prob.map ((X.pullbackAlongπ t).op ≫ eT.hom.op) a := by
            rw [haT, ← Functor.map_comp_apply]
        _ = qpd.prob.map (e.hom.op ≫ (X.pullbackAlongπ t).op) a := by
            rw [← op_comp, ← op_comp, hcomp]
        _ = qpd.prob.map (X.pullbackAlongπ t).op (qpd.prob.map e.hom.op a) := by
            rw [Functor.map_comp_apply]
        _ = aT := by rw [hfix, haT]
    obtain ⟨b, hb⟩ := qpd.geom_surjective k (t ≫ X.structMap) (X.curve.baseChange t) aT
    -- recast the lift at the `pullbackAlong` spelling (definitionally equal object)
    have hb' : qpd.proj.app (Opposite.op (X.pullbackAlong t)) b = aT := hb
    have horb : qpd.proj.app (Opposite.op (X.pullbackAlong t)) (Q.map eT.hom.op b) =
        qpd.proj.app (Opposite.op (X.pullbackAlong t)) b := by
      calc qpd.proj.app (Opposite.op (X.pullbackAlong t)) (Q.map eT.hom.op b)
          = qpd.prob.map eT.hom.op
              (qpd.proj.app (Opposite.op (X.pullbackAlong t)) b) :=
            NatTrans.naturality_apply qpd.proj eT.hom.op b
        _ = qpd.prob.map eT.hom.op aT := by rw [hb']
        _ = aT := hfixT
        _ = qpd.proj.app (Opposite.op (X.pullbackAlong t)) b := hb'.symm
    obtain ⟨γ, hγ⟩ := (qpd.geom_orbits k (t ≫ X.structMap) (X.curve.baseChange t)
      (Q.map eT.hom.op b) b).mp horb
    exact hfree k (t ≫ X.structMap) (X.curve.baseChange t) eT rfl hfib b γ hγ
  · exact hne (EllObj.iso_eq_refl_of_isEmpty (not_nonempty_iff.mp hbase) e)

variable (R : CommRingCat.{u})

/-- **[Γ_H MASTER, interface] (KM 4.7.0 for `P_H`; Loeffler 3.8.2 upgraded to a fine
scheme)** — the quotient problem `P_H` is representable, given the engine's pin-set: the
Y(N) representability (`hQrep`, STREAM-YN), the full-group torsor datum (`htors`, c5β's
layer), rigidity of `P_H` (`hrig`), and the affineness/global-model clauses. The
representing object is KM's `𝕸(P_H, δ)/G`, i.e. `Y_H(N)`. -/
theorem gammaH_representable (N : ℕ) [NeZero N]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (qpd : ModuliProblem.QuotientProblemData (gammaHAut R N H))
    {G : Type u} [Group G] [Finite G] (φfull : G →* Aut (gammaFullNaiveProblem R N))
    (hQrep : (gammaFullNaiveProblem R N).Representable)
    (htors : ∀ X : EllObj R, Nonempty (ModuliProblem.TorsorData φfull X))
    (hrig : qpd.prob.Rigid)
    (hQaff : ∀ {Xδ : EllObj R}, (gammaFullNaiveProblem R N).RepresentableBy Xδ →
      IsAffine Xδ.base)
    (hPaff : ∀ (X : EllObj R) (dP : ModuliProblem.RelRepData qpd.prob X), IsAffine dP.Z)
    (hmodel : ∀ {Xδ : EllObj R} [IsAffine Xδ.base],
      (gammaFullNaiveProblem R N).RepresentableBy Xδ →
      ∃ (WQ : WeierstrassCurve ↑Γ(Xδ.base, ⊤)) (φQ : Xδ.curve.E ≅ projModel WQ),
        WQ.IsElliptic ∧
        φQ.hom ≫ projModelπ WQ = Xδ.curve.π ≫ Xδ.base.isoSpec.hom ∧
        Xδ.curve.zero ≫ φQ.hom = Xδ.base.isoSpec.hom ≫ projModelZero WQ) :
    qpd.prob.Representable :=
  ModuliProblem.representable_of_rigid_of_torsor_of_globalModel qpd.prob
    (gammaFullNaiveProblem R N) φfull hQrep
    ((ModuliProblem.relativelyRepresentable_iff_nonempty_relRepData qpd.prob).mpr
      (fun X => ⟨(qpd.relRep X).choose⟩))
    htors hrig hQaff hPaff hmodel

end ModularCurves

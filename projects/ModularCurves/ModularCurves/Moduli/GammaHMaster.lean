/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.GammaHRepresentability
import ModularCurves.Moduli.QuotientRepresentability
import ModularCurves.Moduli.KeystoneGeometricPoint
import ModularCurves.Moduli.EngineWiring
import ModularCurves.EllipticCurve.TorsionRestrict
import ModularCurves.EllipticCurve.ExactOrderRigidity
import ModularCurves.ForMathlib.UnramifiedEqualizer
import ModularCurves.Moduli.DrinfeldRepresentability

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

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory

-- `open MonObj` is deliberately AVOIDED: since the KM 4.7.0 engine (`Moduli/EngineWiring`,
-- consumed by the receipts below) transitively imports mathlib's
-- `CategoryTheory/Monoidal/Mod.lean`, `MonObj` now also carries the scoped notation
-- `notation "γ" => ModObj.smul`, which would shadow this file's 25 `γ`-binders (group
-- elements). We reproduce the one `MonObj` notation actually used here — the unit
-- `η[·]` — file-locally instead; every other `MonObj`/`GrpObj` use is already qualified.
local notation "η[" M "]" => CategoryTheory.MonObj.one (X := M)

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

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

/-! ### [RIG-1] Geometric detection of nontrivial base-identical isos

A base-identical iso trivial on every geometric fibre is trivial: its top map `c`
restricts to the finite étale `M`-torsion (`torsionRestrict`), where fibrewise
agreement with the identity globalises by the `UnramifiedEqualizer` engine; the
`M`-torsion fix then forces `c = 𝟙` through `aut_endo_eq_one` (KM 2.7.2; consumed as
the register-box keystone, v10.212-§D). -/

open EllipticCurve in
/-- **[RIG-1] (detection, contrapositive form)** — a base-identical self-iso of an
`Ell/R`-object that restricts to the identity on every geometric fibre is the identity,
given an invertible torsion level `M ≥ 3` on the (locally noetherian) base. -/
theorem EllObj.eq_refl_of_forall_isoFibre_eq_refl {X : EllObj R}
    [IsLocallyNoetherian X.base] (M : ℕ) [NeZero M] (hM : 3 ≤ (M : ℤ))
    (hinv : NIsInvertible X.base M)
    (e : X ≅ X) (he : e.hom.baseHom = 𝟙 X.base)
    (htriv : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (t : Spec (CommRingCat.of k) ⟶ X.base), EllObj.isoFibre e he t = Iso.refl _) :
    e = Iso.refl X := by
  classical
  set E := X.curve with hE
  set c := e.hom.top with hc
  -- `c` as an `Over X.base`-endomorphism
  have hcπ : c ≫ E.π = E.π := by
    have h := e.hom.isPullback.w
    rw [he, Category.comp_id] at h
    exact h
  set εO : E.asOver ⟶ E.asOver := Over.homMk c hcπ with hεO
  -- `εO` is pointed
  have hzc : E.zero ≫ c = E.zero := by
    have h := e.hom.zero_w
    rw [he, Category.id_comp] at h
    exact h
  have hη : η[E.asOver] ≫ εO = η[E.asOver] := by
    refine Over.OverMorphism.ext ?_
    show (η[E.asOver]).left ≫ c = (η[E.asOver]).left
    rw [E.one_eq_zero]
    have s1 : ((𝟙_ (Over X.base)).hom ≫ E.zero) ≫ c
        = (𝟙_ (Over X.base)).hom ≫ E.zero ≫ c := Category.assoc _ _ _
    have s2 : (𝟙_ (Over X.base)).hom ≫ E.zero ≫ c
        = (𝟙_ (Over X.base)).hom ≫ E.zero :=
      congrArg (fun m => (𝟙_ (Over X.base)).hom ≫ m) hzc
    exact s1.trans s2
  -- `εO` is an isomorphism (inverse from `e.inv`)
  have hcπ' : e.inv.top ≫ E.π = E.π := by
    have h := e.inv.isPullback.w
    rw [EllObj.isoInv_baseHom e he, Category.comp_id] at h
    exact h
  have htop_hom_inv : c ≫ e.inv.top = 𝟙 E.E := by
    have h := congrArg EllHom.top e.hom_inv_id
    exact h
  have htop_inv_hom : e.inv.top ≫ c = 𝟙 E.E := by
    have h := congrArg EllHom.top e.inv_hom_id
    exact h
  haveI : IsIso εO := by
    refine ⟨Over.homMk e.inv.top hcπ', ?_, ?_⟩
    · exact Over.OverMorphism.ext htop_hom_inv
    · exact Over.OverMorphism.ext htop_inv_hom
  -- **[v10.322-FIN keystone-free rewire]** `htriv` is far stronger than an `E[M]`-fix:
  -- the difference endomorphism `δ = ε − 1` is FIBREWISE ZERO, which is exactly the
  -- GIT 6.1 collapse hypothesis of the PROVEN rigidity factor engine
  -- (`exists_factor_of_forall_component` + `fibre_subset_eqLocus_of_collapsed`).
  -- `δ.left` collapses every `π`-fibre to the zero point, hence factors through the
  -- base; pointedness pins the factor to the zero section, so `δ = 0` and `ε = 𝟙` —
  -- with NO endomorphism-degree input (the former `aut_endo_eq_one` consumption and
  -- its five sorried degree leaves are gone from this route).
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  set δ : E.asOver ⟶ E.asOver := εO * (𝟙 E.asOver)⁻¹ with hδdef
  have hδη : η[E.asOver] ≫ δ = η[E.asOver] := E.sub_one_pointed εO hη
  have hδπ : δ.left ≫ E.π = E.π := Over.w δ
  -- re-type the underlying morphism at `E.E` (kills the `asOver.left`-vs-`E.E`
  -- elaboration friction in the factor-engine plumbing below)
  have hd : ∃ d : E.E ⟶ E.E, d = δ.left := ⟨δ.left, rfl⟩
  obtain ⟨d, hd⟩ := hd
  have hdπ : d ≫ E.π = E.π := by rw [hd]; exact hδπ
  -- the unit of any point-hom-group has underlying morphism `t ≫ zero`
  have hunit_left : ∀ {T : Scheme.{u}} (t : T ⟶ X.base),
      letI : CommGroup (Over.mk t ⟶ E.asOver) := Hom.commGroup
      (1 : Over.mk t ⟶ E.asOver).left = t ≫ E.zero := by
    intro T t
    letI : CommGroup (Over.mk t ⟶ E.asOver) := Hom.commGroup
    rw [Hom.one_def]
    show (toUnit (Over.mk t)).left ≫ (η[E.asOver]).left = t ≫ E.zero
    rw [E.one_eq_zero]
    exact ((Category.assoc _ _ _).symm).trans
      (congrArg (· ≫ E.zero) (Over.w (toUnit (Over.mk t))))
  -- a `c`-fixed point is `δ`-killed (pure group-object algebra)
  have hkill_of_fix : ∀ {T : Scheme.{u}} (t : T ⟶ X.base) (P : Over.mk t ⟶ E.asOver),
      P ≫ εO = P →
      letI : CommGroup (Over.mk t ⟶ E.asOver) := Hom.commGroup
      P ≫ δ = 1 := by
    intro T t P hPfix
    letI : CommGroup (Over.mk t ⟶ E.asOver) := Hom.commGroup
    rw [hδdef, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, hPfix, mul_inv_cancel]
  -- `δ.left` collapses every set-theoretic fibre of `π` to the zero point
  have hcollapse : ∀ s : X.base,
      Set.Subsingleton (d.base '' (E.π.base ⁻¹' {s})) := by
    intro s
    suffices h : ∀ x ∈ E.π.base ⁻¹' {s}, d.base x = E.zero.base s by
      rintro y ⟨x, hx, rfl⟩ y' ⟨x', hx', rfl⟩
      rw [h x hx, h x' hx']
    intro x hx
    -- the geometric point through `x`
    set κx := E.E.residueField x with hκx
    set kx := AlgebraicClosure κx with hkx
    set xbar : Spec (CommRingCat.of kx) ⟶ E.E :=
      Spec.map (CommRingCat.ofHom (algebraMap κx kx)) ≫
        E.E.fromSpecResidueField x with hxbar
    set t : Spec (CommRingCat.of kx) ⟶ X.base := xbar ≫ E.π with ht
    -- fibre triviality at `t`, projected to the top map of the fibre
    have htt := htriv kx t
    have htop : (EllObj.isoFibre e he t).hom.top = (Iso.refl (X.pullbackAlong t)).hom.top :=
      congrArg EllHom.top (congrArg Iso.hom htt)
    -- `xbar` is fixed by `c` (the isoFibre-square plumbing)
    have hxc : xbar ≫ c = xbar := by
      set ℓ : Spec (CommRingCat.of kx) ⟶ Limits.pullback E.π t :=
        Limits.pullback.lift xbar (𝟙 _) (by rw [Category.id_comp]) with hℓ
      have hfix' : ℓ ≫ (EllObj.isoFibre e he t).hom.top = ℓ := by
        refine (congrArg (fun m => ℓ ≫ m) htop).trans ?_
        show ℓ ≫ 𝟙 _ = ℓ
        rw [Category.comp_id]
      calc xbar ≫ c = (ℓ ≫ Limits.pullback.fst E.π t) ≫ c := by
            rw [hℓ, Limits.pullback.lift_fst]
        _ = ℓ ≫ Limits.pullback.fst E.π t ≫ c := Category.assoc _ _ _
        _ = ℓ ≫ (EllObj.isoFibre e he t).hom.top ≫ Limits.pullback.fst E.π t := by
            refine congrArg (fun m => ℓ ≫ m) ?_
            exact (Limits.pullback.lift_fst _ _ _).symm
        _ = (ℓ ≫ (EllObj.isoFibre e he t).hom.top) ≫ Limits.pullback.fst E.π t :=
            (Category.assoc _ _ _).symm
        _ = ℓ ≫ Limits.pullback.fst E.π t := congrArg
            (fun m => m ≫ Limits.pullback.fst E.π t) hfix'
        _ = xbar := by rw [hℓ, Limits.pullback.lift_fst]
    -- hence `xbar` is `δ`-killed, and the value of `δ.left` at `x` is the zero point
    letI : CommGroup (Over.mk t ⟶ E.asOver) := Hom.commGroup
    set P : Over.mk t ⟶ E.asOver := Over.homMk xbar rfl with hP
    have hPε : P ≫ εO = P := by
      refine Over.OverMorphism.ext ?_
      show xbar ≫ c = xbar
      exact hxc
    have hPδ : P ≫ δ = 1 := hkill_of_fix t P hPε
    have hPδl : xbar ≫ d = t ≫ E.zero := by
      rw [hd]
      have h1 := congrArg CommaMorphism.left hPδ
      exact h1.trans (hunit_left t)
    obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of kx)) :=
      inferInstanceAs (Nonempty (PrimeSpectrum kx))
    have hxbase : xbar.base pt = x := by
      rw [hxbar, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    have htbase : t.base pt = s := by
      rw [ht, Scheme.Hom.comp_apply, hxbase]
      exact hx
    calc d.base x = d.base (xbar.base pt) := by rw [hxbase]
      _ = (xbar ≫ d).base pt := rfl
      _ = (t ≫ E.zero).base pt :=
          congrArg (fun m : Spec (CommRingCat.of kx) ⟶ E.E => m.base pt) hPδl
      _ = E.zero.base (t.base pt) := rfl
      _ = E.zero.base s := congrArg E.zero.base htbase
  -- the GIT 6.1 factor engine: `δ.left` factors through the equalizer with the constant
  haveI : Smooth E.π := SmoothOfRelativeDimension.smooth (n := 1) (f := E.π)
  haveI : IsProper E.π := E.proper
  haveI : IsSeparated E.π := inferInstance
  haveI : Flat E.π := inferInstance
  have hg : (E.π ≫ (E.zero ≫ d)) ≫ E.π = E.π := by
    calc (E.π ≫ (E.zero ≫ d)) ≫ E.π
        = E.π ≫ (E.zero ≫ (d ≫ E.π)) := by
          rw [Category.assoc, Category.assoc]
      _ = E.π ≫ (E.zero ≫ E.π) := congrArg (fun m => E.π ≫ (E.zero ≫ m)) hdπ
      _ = E.π ≫ 𝟙 _ := congrArg (fun m => E.π ≫ m) E.zero_π
      _ = E.π := Category.comp_id _
  obtain ⟨w, hw⟩ := exists_factor_of_forall_component (p := E.π) (q := E.π)
    E.toEllipticCurveGeom.universallyOConnected E.zero E.zero_π
    d (E.π ≫ (E.zero ≫ d)) hdπ hg rfl
    (fun s => ⟨s, mem_connectedComponent,
      fibre_subset_eqLocus_of_collapsed E.toEllipticCurveGeom.universallyOConnected
        E.zero E.zero_π d hdπ s (hcollapse s)⟩)
  -- read the factorization: `d` equals the constant morphism
  have hfg : d = E.π ≫ (E.zero ≫ d) := by
    have hcond := eqLocusι_comp_eq d (E.π ≫ (E.zero ≫ d)) hdπ hg
    have h2 : w ≫ (eqLocusι d (E.π ≫ (E.zero ≫ d)) hdπ hg ≫ d)
        = w ≫ (eqLocusι d (E.π ≫ (E.zero ≫ d)) hdπ hg ≫ (E.π ≫ (E.zero ≫ d))) :=
      congrArg (fun m => w ≫ m) hcond
    have h3 : (w ≫ eqLocusι d (E.π ≫ (E.zero ≫ d)) hdπ hg) ≫ d
        = (w ≫ eqLocusι d (E.π ≫ (E.zero ≫ d)) hdπ hg) ≫ (E.π ≫ (E.zero ≫ d)) :=
      (Category.assoc _ _ _).trans (h2.trans (Category.assoc _ _ _).symm)
    rw [hw] at h3
    rw [Category.id_comp, Category.id_comp] at h3
    exact h3
  -- pointedness pins the constant: `zero ≫ d = zero`
  have hδz : E.zero ≫ d = E.zero := by
    rw [hd]
    letI : CommGroup (Over.mk (𝟙 X.base) ⟶ E.asOver) := Hom.commGroup
    set P0 : Over.mk (𝟙 X.base) ⟶ E.asOver := Over.homMk E.zero E.zero_π with hP0
    have hP0ε : P0 ≫ εO = P0 := by
      refine Over.OverMorphism.ext ?_
      show E.zero ≫ c = E.zero
      exact hzc
    have hP0δ : P0 ≫ δ = 1 := hkill_of_fix (𝟙 X.base) P0 hP0ε
    have h1 := congrArg CommaMorphism.left hP0δ
    exact h1.trans ((hunit_left (𝟙 X.base)).trans (Category.id_comp E.zero))
  -- conclude: `δ = 1`, so `ε = 𝟙`, so `e = refl`
  have hδone : δ = (1 : E.asOver ⟶ E.asOver) := by
    refine Over.OverMorphism.ext ?_
    show δ.left = (1 : E.asOver ⟶ E.asOver).left
    rw [← hd]
    exact hfg.trans ((congrArg (fun m => E.π ≫ m) hδz).trans (hunit_left E.π).symm)
  have hεid : εO = 𝟙 E.asOver := by
    have h := hδdef.symm.trans hδone
    exact _root_.mul_inv_eq_one.mp h
  have hcid : c = 𝟙 E.E := congrArg CommaMorphism.left hεid
  refine Iso.ext (EllHom.ext ?_ ?_)
  · exact he
  · exact hcid

/-- **[RIG-1] (detection, existential form — the bridge's `hdetect` shape)** — a
base-identical self-iso `e ≠ refl` stays nontrivial on SOME geometric fibre, given an
invertible torsion level `M ≥ 3` on the locally noetherian base. Contrapositive of
`eq_refl_of_forall_isoFibre_eq_refl`. -/
theorem EllObj.exists_isoFibre_ne_refl {X : EllObj R}
    [IsLocallyNoetherian X.base] (M : ℕ) [NeZero M] (hM : 3 ≤ (M : ℤ))
    (hinv : NIsInvertible X.base M)
    (e : X ≅ X) (he : e.hom.baseHom = 𝟙 X.base) (hne : e ≠ Iso.refl X) :
    ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k)
      (t : Spec (CommRingCat.of k) ⟶ X.base),
      EllObj.isoFibre e he t ≠ Iso.refl (X.pullbackAlong t) := by
  by_contra hcon
  refine hne (EllObj.eq_refl_of_forall_isoFibre_eq_refl M hM hinv e he ?_)
  intro k _ _ t
  by_contra hne'
  exact hcon ⟨k, ‹_›, ‹_›, t, hne'⟩

open EllipticCurve in
/-- **[RIG-2-wrap, `H = ⊥` core] (classical Γ(N) k̄-rigidity)** — over an algebraically
closed field, no nontrivial base-identical self-iso fixes a naive full level-`N`
structure (`N ≥ 3`). The fixed basis spans the geometric `N`-torsion
(`IsNaiveFullLevel`'s span clause), the fixed locus of the induced endomorphism is a
subgroup of the points at every geometric extension, so the torsion restriction agrees
with the identity on every point of the finite étale `E[N]` — the `UnramifiedEqualizer`
engine globalises, and `aut_endo_eq_one` (KM 2.7.2, register-box keystone) closes. -/
theorem gammaFullNaive_eq_refl_of_fix_sections (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (hinv : IsUnit (N : R))
    (k : Type u) [Field k] [IsAlgClosed k]
    (sm : Spec (CommRingCat.of k) ⟶ Spec R)
    (E : EllipticCurve (Spec (CommRingCat.of k)))
    (e : (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R) ≅
      (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))
    (he : e.hom.baseHom = 𝟙 _)
    (b : (gammaFullNaiveProblem R N).obj
      (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)))
    (hPc : b.1.1.1 ≫ e.hom.top = b.1.1.1)
    (hQc : b.1.2.1 ≫ e.hom.top = b.1.2.1) : e = Iso.refl _ := by
  classical
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of k)) := by
    haveI : IsNoetherianRing k := inferInstance
    infer_instance
  set c := e.hom.top with hc
  -- `c` as a pointed `Over`-automorphism (as in the detection theorem)
  have hcπ : c ≫ E.π = E.π := by
    have h := e.hom.isPullback.w
    rw [he, Category.comp_id] at h
    exact h
  set εO : E.asOver ⟶ E.asOver := Over.homMk c hcπ with hεO
  have hzc : E.zero ≫ c = E.zero := by
    have h := e.hom.zero_w
    rw [he, Category.id_comp] at h
    exact h
  have hη : η[E.asOver] ≫ εO = η[E.asOver] := by
    refine Over.OverMorphism.ext ?_
    show (η[E.asOver]).left ≫ c = (η[E.asOver]).left
    rw [E.one_eq_zero]
    have s1 : ((𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ E.zero) ≫ c
        = (𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ E.zero ≫ c := Category.assoc _ _ _
    have s2 : (𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ E.zero ≫ c
        = (𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ E.zero :=
      congrArg (fun m => (𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ m) hzc
    exact s1.trans s2
  haveI : IsIso εO := by
    have hcπ' : e.inv.top ≫ E.π = E.π := by
      have h := e.inv.isPullback.w
      rw [EllObj.isoInv_baseHom e he, Category.comp_id] at h
      exact h
    refine ⟨Over.homMk e.inv.top hcπ', ?_, ?_⟩
    · exact Over.OverMorphism.ext (congrArg EllHom.top e.hom_inv_id)
    · exact Over.OverMorphism.ext (congrArg EllHom.top e.inv_hom_id)
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  haveI : IsMonHom εO := { one_hom := hη, mul_hom := E.endMonHom εO hη }
  -- the fixed locus is a subgroup of the points at every geometric extension
  have hfixed : ∀ (k' : Type u) [Field k'] [IsAlgClosed k']
      (t' : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k)) (x : E.Point t'),
      x ∈ AddSubgroup.closure {Point.pull E t' b.1.1, Point.pull E t' b.1.2} →
      (E.pointEquivOverHom t') x ≫ εO = (E.pointEquivOverHom t') x := by
    intro k' _ _ t' x hx
    letI : CommGroup (Over.mk t' ⟶ E.asOver) := Hom.commGroup
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · subst hy
        refine Over.OverMorphism.ext ?_
        show (t' ≫ b.1.1.1) ≫ c = t' ≫ b.1.1.1
        rw [Category.assoc, hPc]
      · subst hy
        refine Over.OverMorphism.ext ?_
        show (t' ≫ b.1.2.1) ≫ c = t' ≫ b.1.2.1
        rw [Category.assoc, hQc]
    | zero =>
      have hmap := (IsMonHom.monoidHom εO (Over.mk t')).map_one
      simp only [IsMonHom.monoidHom_apply] at hmap
      exact hmap
    | add y z _ _ hy hz =>
      have hmap := (IsMonHom.monoidHom εO (Over.mk t')).map_mul
        ((E.pointEquivOverHom t') y) ((E.pointEquivOverHom t') z)
      simp only [IsMonHom.monoidHom_apply] at hmap
      show (E.pointEquivOverHom t') (y + z) ≫ εO = (E.pointEquivOverHom t') (y + z)
      have htr : (E.pointEquivOverHom t') (y + z)
          = (E.pointEquivOverHom t') y * (E.pointEquivOverHom t') z :=
        E.pointEquivOverHom_add t' y z
      rw [htr, hmap, hy, hz]
    | neg y _ hy =>
      have hmap := (IsMonHom.monoidHom εO (Over.mk t')).map_inv
        ((E.pointEquivOverHom t') y)
      simp only [IsMonHom.monoidHom_apply] at hmap
      have htr : (E.pointEquivOverHom t') (-y) = ((E.pointEquivOverHom t') y)⁻¹ := rfl
      rw [htr, hmap, hy]
  -- **[STRAND-3, KVC route]** `εO` fixes EVERY `N`-torsion point (`hfixed` on the
  -- `IsNaiveFullLevel` span `b.2.2`, at the geometric point `k` itself), so the
  -- Hasse-/degree-free `k̄`-point master closes — replacing the former
  -- `aut_endo_eq_one` (KM 2.7.2) route and its five EndomorphismDegree leaves.
  have hinvk : IsUnit ((N : ℕ) : k) := by
    have h := hinv.map (Spec.preimage sm).hom
    rwa [map_natCast] at h
  have hNnat : 3 ≤ N := by exact_mod_cast hN
  have hfixAll : ∀ x : E.Point (𝟙 (Spec (CommRingCat.of k))), (N : ℤ) • x = 0 →
      (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) x ≫ εO =
        (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) x :=
    fun x hx => hfixed k (𝟙 _) x (b.2.2 k (𝟙 _) x hx)
  have hεid : εO = 𝟙 E.asOver :=
    EllipticCurve.pointedAuto_eq_id_of_fixes_torsion_kvc E εO ‹IsIso εO› hη N hNnat
      hinvk.ne_zero hfixAll
  have hcid : c = 𝟙 E.E := congrArg CommaMorphism.left hεid
  exact Iso.ext (EllHom.ext he hcid)

open EllipticCurve in
/-- **[RIG-2-wrap, `H = ⊥` core] (classical Γ(N) k̄-rigidity)** — no nontrivial
base-identical self-iso fixes a naive full level-`N` structure over k̄ (`N ≥ 3`
invertible): the fixed sections force `e = refl` (`gammaFullNaive_eq_refl_of_fix_sections`). -/
theorem gammaFullNaive_fix_absurd (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (hinv : IsUnit (N : R))
    (k : Type u) [Field k] [IsAlgClosed k]
    (sm : Spec (CommRingCat.of k) ⟶ Spec R)
    (E : EllipticCurve (Spec (CommRingCat.of k)))
    (e : (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R) ≅
      (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))
    (he : e.hom.baseHom = 𝟙 _) (hne : e ≠ Iso.refl _)
    (b : (gammaFullNaiveProblem R N).obj
      (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)))
    (hfix : (gammaFullNaiveProblem R N).map e.hom.op b = b) : False := by
  have h1 : EllHom.pullSection R e.hom b.1.1 = b.1.1 := congrArg (fun z => z.1.1) hfix
  have h2 : EllHom.pullSection R e.hom b.1.2 = b.1.2 := congrArg (fun z => z.1.2) hfix
  have hPc : b.1.1.1 ≫ e.hom.top = b.1.1.1 := by
    have hlf : (EllHom.pullSection R e.hom b.1.1).1 ≫ e.hom.top
        = e.hom.baseHom ≫ b.1.1.1 := e.hom.isPullback.lift_fst _ _ _
    rw [h1, he, Category.id_comp] at hlf
    exact hlf
  have hQc : b.1.2.1 ≫ e.hom.top = b.1.2.1 := by
    have hlf : (EllHom.pullSection R e.hom b.1.2).1 ≫ e.hom.top
        = e.hom.baseHom ≫ b.1.2.1 := e.hom.isPullback.lift_fst _ _ _
    rw [h2, he, Category.id_comp] at hlf
    exact hlf
  exact hne (gammaFullNaive_eq_refl_of_fix_sections N hN hinv k sm E e he b hPc hQc)

/-- Iterated composition of a self-isomorphism. -/
noncomputable def isoPow {C : Type*} [Category C] {X : C} (e : X ≅ X) : ℕ → (X ≅ X)
  | 0 => Iso.refl X
  | (n + 1) => isoPow e n ≪≫ e

/-- The pure group-arithmetic engine of the `γ`-twist: an additive endomorphism sending
the `M`-columns of an `N`-torsion pair back to the pair has its `m`-th iterate fix the
pair, whenever `M ^ m ≡ 1 mod N` entrywise. -/
private theorem iterate_fix_of_matrix_rel {A : Type*} [AddCommGroup A]
    {P Q : A} {N : ℕ} (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0)
    (φ : A →+ A) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hrel0 : φ (M 0 0 • P + M 1 0 • Q) = P)
    (hrel1 : φ (M 0 1 • P + M 1 1 • Q) = Q)
    (m : ℕ)
    (hMm : ∀ i j, (N : ℤ) ∣ (M ^ m) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j) :
    φ^[m] P = P ∧ φ^[m] Q = Q := by
  classical
  set pt : (Fin 2 → ℤ) → A := fun v => v 0 • P + v 1 • Q with hpt
  have pt_congr : ∀ v w : Fin 2 → ℤ, (∀ i, (N : ℤ) ∣ v i - w i) → pt v = pt w := by
    intro v w hdvd
    obtain ⟨c0, hc0⟩ := hdvd 0
    obtain ⟨c1, hc1⟩ := hdvd 1
    have hv0 : v 0 = w 0 + N * c0 := by linarith
    have hv1 : v 1 = w 1 + N * c1 := by linarith
    show v 0 • P + v 1 • Q = w 0 • P + w 1 • Q
    rw [hv0, hv1, add_smul, add_smul, mul_smul, mul_smul, smul_comm (N : ℤ) c0,
      smul_comm (N : ℤ) c1, hP, hQ, smul_zero, smul_zero, add_zero, add_zero]
  have hexp : ∀ (A' : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → ℤ) (i : Fin 2),
      A'.mulVec v i = A' i 0 * v 0 + A' i 1 * v 1 := by
    intro A' v i
    simp [Matrix.mulVec]
  have hgen : ∀ v : Fin 2 → ℤ, φ (pt (M.mulVec v)) = pt v := by
    intro v
    have hdecomp : pt (M.mulVec v)
        = v 0 • (M 0 0 • P + M 1 0 • Q) + v 1 • (M 0 1 • P + M 1 1 • Q) := by
      show (M.mulVec v) 0 • P + (M.mulVec v) 1 • Q = _
      rw [hexp M v 0, hexp M v 1]
      module
    rw [hdecomp, map_add, map_zsmul, map_zsmul, hrel0, hrel1]
  have hiter : ∀ (mm : ℕ) (v : Fin 2 → ℤ), φ^[mm] (pt ((M ^ mm).mulVec v)) = pt v := by
    intro mm
    induction mm with
    | zero =>
      intro v
      rw [pow_zero, Matrix.one_mulVec]
      rfl
    | succ n ih =>
      intro v
      rw [pow_succ', Function.iterate_succ_apply]
      have hgrp : (M * M ^ n).mulVec v = M.mulVec ((M ^ n).mulVec v) := by
        rw [← Matrix.mulVec_mulVec]
      rw [hgrp, hgen ((M ^ n).mulVec v)]
      exact ih v
  have hMmv : ∀ v : Fin 2 → ℤ, pt ((M ^ m).mulVec v) = pt v := by
    intro v
    refine pt_congr _ _ ?_
    intro i
    have hv : (M ^ m).mulVec v i - v i
        = ((M ^ m) i 0 - (1 : Matrix (Fin 2) (Fin 2) ℤ) i 0) * v 0
          + ((M ^ m) i 1 - (1 : Matrix (Fin 2) (Fin 2) ℤ) i 1) * v 1 := by
      have h1v : v i = (1 : Matrix (Fin 2) (Fin 2) ℤ).mulVec v i := by
        rw [Matrix.one_mulVec]
      rw [hexp (M ^ m) v i]
      nth_rewrite 1 [h1v]
      rw [hexp (1 : Matrix (Fin 2) (Fin 2) ℤ) v i]
      ring
    rw [hv]
    exact dvd_add ((hMm i 0).mul_right _) ((hMm i 1).mul_right _)
  constructor
  · have hstd : pt ![1, 0] = P := by
      show (1 : ℤ) • P + (0 : ℤ) • Q = P
      rw [one_smul, zero_smul, add_zero]
    calc φ^[m] P = φ^[m] (pt ![1, 0]) := by rw [hstd]
      _ = φ^[m] (pt ((M ^ m).mulVec ![1, 0])) := by rw [hMmv]
      _ = pt ![1, 0] := hiter m _
      _ = P := hstd
  · have hstd : pt ![0, 1] = Q := by
      show (0 : ℤ) • P + (1 : ℤ) • Q = Q
      rw [one_smul, zero_smul, zero_add]
    calc φ^[m] Q = φ^[m] (pt ![0, 1]) := by rw [hstd]
      _ = φ^[m] (pt ((M ^ m).mulVec ![0, 1])) := by rw [hMmv]
      _ = pt ![0, 1] := hiter m _
      _ = Q := hstd

/-- Entrywise congruence of the `orderOf`-power of an integer lift of a `GL₂(ℤ/N)`
element: `M ^ orderOf g ≡ 1 mod N`. -/
private theorem pow_entry_dvd_of_map_eq (N : ℕ) [NeZero N]
    (M : Matrix (Fin 2) (Fin 2) ℤ) (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (hMg : M.map (Int.cast : ℤ → ZMod N) = (g : Matrix (Fin 2) (Fin 2) (ZMod N)))
    (i j : Fin 2) :
    (N : ℤ) ∣ (M ^ orderOf g) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j := by
  have hcast : (M ^ orderOf g).map (Int.cast : ℤ → ZMod N) = 1 := by
    have hring : (M ^ orderOf g).map (Int.cast : ℤ → ZMod N)
        = ((Int.castRingHom (ZMod N)).mapMatrix M) ^ orderOf g := by
      have h := map_pow ((Int.castRingHom (ZMod N)).mapMatrix) M (orderOf g)
      rw [RingHom.mapMatrix_apply] at h
      exact h
    rw [hring]
    have hMg' : (Int.castRingHom (ZMod N)).mapMatrix M
        = (g : Matrix (Fin 2) (Fin 2) (ZMod N)) := hMg
    rw [hMg']
    have hpow : ((g : Matrix (Fin 2) (Fin 2) (ZMod N))) ^ orderOf g
        = (((g ^ orderOf g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))) :
          Matrix (Fin 2) (Fin 2) (ZMod N)) := (Units.val_pow_eq_pow_val _ _).symm
    rw [hpow, pow_orderOf_eq_one, Units.val_one]
  have hij : (((M ^ orderOf g) i j : ℤ) : ZMod N)
      = (((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod N) := by
    have hl : (((M ^ orderOf g) i j : ℤ) : ZMod N)
        = ((M ^ orderOf g).map (Int.cast : ℤ → ZMod N)) i j := rfl
    rw [hl, hcast, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hmod := (ZMod.intCast_eq_intCast_iff _ _ _).mp hij
  exact dvd_sub_comm.mp (Int.ModEq.dvd hmod)

open EllipticCurve in
/-- **[TWIST] (the `γ`-twist iterate — general-`H` engine)** — if a base-identical
self-iso `e` carries a full level structure to its `glSmul g`-translate, then
`e^(orderOf g)` is the identity: the induced additive action on points sends the
`g`-matrix combinations of the basis back to the basis, so its `orderOf g`-th iterate
fixes the basis outright (the integer matrix power is congruent to `1` mod `N`, and the
basis is `N`-torsion), and the Γ(N) k̄-rigidity extraction
(`gammaFullNaive_eq_refl_of_fix_sections`) forces the iterate to be `refl`.

This is the whole geometric content of general-`H` rigidity: the per-`H` arithmetic
residue is exactly "no `e ≠ refl` with `e^(orderOf γ) = refl` can twist by `γ ∈ H`" —
the CM-unit/`H`-intersection condition fed by KM's endomorphism-degree keystone. -/theorem gammaFullNaive_twist_pow_refl (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (hinv : IsUnit (N : R))
    (k : Type u) [Field k] [IsAlgClosed k]
    (sm : Spec (CommRingCat.of k) ⟶ Spec R)
    (E : EllipticCurve (Spec (CommRingCat.of k)))
    (e : (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R) ≅
      (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))
    (he : e.hom.baseHom = 𝟙 _)
    (b : (gammaFullNaiveProblem R N).obj
      (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)))
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))
    (hcon : (gammaFullNaiveProblem R N).map e.hom.op b = E.glSmul g b) :
    isoPow e (orderOf g) = Iso.refl _ := by
  classical
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of k)) := by
    haveI : IsNoetherianRing k := inferInstance
    infer_instance
  set c := e.hom.top with hc
  -- `c` as a pointed `Over`-automorphism
  have hcπ : c ≫ E.π = E.π := by
    have h := e.hom.isPullback.w
    rw [he, Category.comp_id] at h
    exact h
  set εO : E.asOver ⟶ E.asOver := Over.homMk c hcπ with hεO
  have hzc : E.zero ≫ c = E.zero := by
    have h := e.hom.zero_w
    rw [he, Category.id_comp] at h
    exact h
  have hη : η[E.asOver] ≫ εO = η[E.asOver] := by
    refine Over.OverMorphism.ext ?_
    show (η[E.asOver]).left ≫ c = (η[E.asOver]).left
    rw [E.one_eq_zero]
    have s1 : ((𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ E.zero) ≫ c
        = (𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ E.zero ≫ c := Category.assoc _ _ _
    have s2 : (𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ E.zero ≫ c
        = (𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ E.zero :=
      congrArg (fun mm => (𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ mm) hzc
    exact s1.trans s2
  letI : CommGroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ E.asOver) := Hom.commGroup
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  haveI : IsMonHom εO := { one_hom := hη, mul_hom := E.endMonHom εO hη }
  -- the additive point action of `c`
  set cAct : E.Point (𝟙 (Spec (CommRingCat.of k))) →+
      E.Point (𝟙 (Spec (CommRingCat.of k))) := AddMonoidHom.mk'
    (fun x => (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))).symm
      ((E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) x ≫ εO))
    (by
      intro x y
      have htr : (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) (x + y)
          = (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) x *
            (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) y :=
        E.pointEquivOverHom_add (𝟙 (Spec (CommRingCat.of k))) x y
      have hmul := (IsMonHom.monoidHom εO (Over.mk (𝟙 (Spec (CommRingCat.of k))))).map_mul
        ((E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) x)
        ((E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) y)
      simp only [IsMonHom.monoidHom_apply] at hmul
      rw [htr, hmul]
      refine ((E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))).symm_apply_eq).mpr ?_
      rw [E.pointEquivOverHom_add]
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]) with hcAct
  have cAct_val : ∀ x : E.Point (𝟙 (Spec (CommRingCat.of k))),
      (cAct x).1 = x.1 ≫ c := fun x => rfl
  -- the lifted matrix and the two column relations from the twist
  set M : Matrix (Fin 2) (Fin 2) ℤ :=
    fun i j => (((g : Matrix (Fin 2) (Fin 2) (ZMod N)) i j).val : ℤ) with hM
  have h1 : EllHom.pullSection R e.hom b.1.1 = M 0 0 • b.1.1 + M 1 0 • b.1.2 :=
    congrArg (fun z => z.1.1) hcon
  have h2 : EllHom.pullSection R e.hom b.1.2 = M 0 1 • b.1.1 + M 1 1 • b.1.2 :=
    congrArg (fun z => z.1.2) hcon
  have hrel0 : cAct (M 0 0 • b.1.1 + M 1 0 • b.1.2) = b.1.1 := by
    refine Subtype.ext ?_
    rw [cAct_val]
    show (M 0 0 • b.1.1 + M 1 0 • b.1.2 : E.Point _).1 ≫ c = b.1.1.1
    rw [← congrArg Subtype.val h1]
    have hlf : (EllHom.pullSection R e.hom b.1.1).1 ≫ e.hom.top
        = e.hom.baseHom ≫ b.1.1.1 := e.hom.isPullback.lift_fst _ _ _
    rw [he, Category.id_comp] at hlf
    exact hlf
  have hrel1 : cAct (M 0 1 • b.1.1 + M 1 1 • b.1.2) = b.1.2 := by
    refine Subtype.ext ?_
    rw [cAct_val]
    show (M 0 1 • b.1.1 + M 1 1 • b.1.2 : E.Point _).1 ≫ c = b.1.2.1
    rw [← congrArg Subtype.val h2]
    have hlf : (EllHom.pullSection R e.hom b.1.2).1 ≫ e.hom.top
        = e.hom.baseHom ≫ b.1.2.1 := e.hom.isPullback.lift_fst _ _ _
    rw [he, Category.id_comp] at hlf
    exact hlf
  -- the abstract iterate engine
  have hdvd : ∀ i j, (N : ℤ) ∣ (M ^ orderOf g) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j :=
    pow_entry_dvd_of_map_eq N M g (by
      funext i j
      show ((((g : Matrix (Fin 2) (Fin 2) (ZMod N)) i j).val : ℤ) : ZMod N)
        = (g : Matrix (Fin 2) (Fin 2) (ZMod N)) i j
      simp [ZMod.natCast_val, ZMod.cast_id])
  obtain ⟨hfixP, hfixQ⟩ := iterate_fix_of_matrix_rel (N := N) (P := b.1.1) (Q := b.1.2)
    b.2.1.1 b.2.1.2 cAct M hrel0 hrel1 (orderOf g) hdvd
  -- compositional translation to the iterated iso, then the rigidity extraction
  have hbase : ∀ mm : ℕ, (isoPow e mm).hom.baseHom = 𝟙 (Spec (CommRingCat.of k)) := by
    intro mm
    induction mm with
    | zero => rfl
    | succ n ih =>
      show ((isoPow e n).hom ≫ e.hom).baseHom = 𝟙 _
      show (isoPow e n).hom.baseHom ≫ e.hom.baseHom = 𝟙 _
      rw [ih, he, Category.comp_id]
  have hval : ∀ (mm : ℕ) (x : E.Point (𝟙 (Spec (CommRingCat.of k)))),
      (cAct^[mm] x).1 = x.1 ≫ (isoPow e mm).hom.top := by
    intro mm
    induction mm with
    | zero =>
      intro x
      show x.1 = x.1 ≫ 𝟙 E.E
      rw [Category.comp_id]
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', cAct_val, ih]
      show (x.1 ≫ (isoPow e n).hom.top) ≫ c = x.1 ≫ ((isoPow e n).hom.top ≫ c)
      rw [Category.assoc]
  have hPfix : b.1.1.1 ≫ (isoPow e (orderOf g)).hom.top = b.1.1.1 := by
    have h := congrArg Subtype.val hfixP
    rw [hval] at h
    exact h
  have hQfix : b.1.2.1 ≫ (isoPow e (orderOf g)).hom.top = b.1.2.1 := by
    have h := congrArg Subtype.val hfixQ
    rw [hval] at h
    exact h
  exact gammaFullNaive_eq_refl_of_fix_sections N hN hinv k sm E (isoPow e (orderOf g))
    (hbase (orderOf g)) b hPfix hQfix

open EllipticCurve in
/-- **[Γ_H hfree, general `H`] — the `γ`-twist reduction.** The `hfree` pin of
`gammaH_rigid` follows from the per-`H` finite-order pin `hH`: a `γ`-twisted fix is an
untwisted `glSmul γ`-translate fix (undo the twist by the inverse action), so the
`[TWIST]` engine forces `e^(orderOf γ) = refl`, which `hH` (the CM-unit/`H`
intersection arithmetic — KM-keystone territory) forbids for `e ≠ refl`. At `H = ⊥`
the pin is vacuously dischargeable (`orderOf 1 = 1`, `isoPow e 1 = e`-fix), recovering
`gammaFullNaive_hfree_bot`. -/
theorem gammaH_hfree_of_orderOf_absurd (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (hinv : IsUnit (N : R))
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hH : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (sm : Spec (CommRingCat.of k) ⟶ Spec R)
      (E : EllipticCurve (Spec (CommRingCat.of k)))
      (e : (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R) ≅
        (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)),
      e.hom.baseHom = 𝟙 _ → e ≠ Iso.refl _ → ∀ γ : ↥H,
        isoPow e (orderOf ((γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))) =
          Iso.refl _ → False)
    (k : Type u) [Field k] [IsAlgClosed k]
    (sm : Spec (CommRingCat.of k) ⟶ Spec R)
    (E : EllipticCurve (Spec (CommRingCat.of k)))
    (e : (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R) ≅
      (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))
    (he : e.hom.baseHom = 𝟙 _) (hne : e ≠ Iso.refl _)
    (b : (gammaFullNaiveProblem R N).obj
      (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)))
    (γ : ↥H) :
    (gammaHAut R N H γ).hom.app
      (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))
      ((gammaFullNaiveProblem R N).map e.hom.op b) ≠ b := by
  intro hcon
  rw [gammaHAut_app_val] at hcon
  have hcon2 := congrArg
    (E.glSmul (((γ⁻¹ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))⁻¹) hcon
  rw [← E.glSmul_mul, mul_inv_cancel, E.glSmul_one] at hcon2
  have hu : (((γ⁻¹ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))⁻¹
      = (γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)) := by
    rw [show (((γ⁻¹ : ↥H) : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
        = ((γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))⁻¹ from rfl, inv_inv]
  rw [hu] at hcon2
  exact hH k sm E e he hne γ
    (gammaFullNaive_twist_pow_refl N hN hinv k sm E e he b
      ((γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N))) hcon2)

/-- **[RIG-2-wrap at `H = ⊥`]** — the `hfree` pin of `gammaH_rigid` holds outright for
the trivial subgroup (`γ = 1` forced, so the twisted fix is a plain fix, killed by the
Γ(N) k̄-rigidity `gammaFullNaive_fix_absurd`). With `hLN`, this makes `P_⊥ = [Γ(N)]`
rigidity UNCONDITIONAL (mod the register-box keystones). -/
theorem gammaFullNaive_hfree_bot (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (hinv : IsUnit (N : R)) (k : Type u) [Field k] [IsAlgClosed k]
    (sm : Spec (CommRingCat.of k) ⟶ Spec R)
    (E : EllipticCurve (Spec (CommRingCat.of k)))
    (e : (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R) ≅
      (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))
    (he : e.hom.baseHom = 𝟙 _) (hne : e ≠ Iso.refl _)
    (b : (gammaFullNaiveProblem R N).obj
      (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)))
    (γ : ↥(⊥ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))) :
    (gammaHAut R N ⊥ γ).hom.app
      (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))
      ((gammaFullNaiveProblem R N).map e.hom.op b) ≠ b := by
  intro hcon
  have hγ1 : γ = 1 := Subtype.ext ((Subgroup.mem_bot).mp γ.2)
  rw [hγ1, map_one] at hcon
  exact gammaFullNaive_fix_absurd N hN hinv k sm E e he hne b hcon

theorem EllObj.iso_eq_refl_of_isEmpty {X : EllObj R} (h : IsEmpty X.base) (e : X ≅ X) :
    e = Iso.refl X := by
  haveI := h
  haveI : IsEmpty X.curve.E := X.curve.π.base.hom.1.isEmpty
  refine Iso.ext (EllHom.ext ?_ ?_)
  · exact (isInitialOfIsEmpty (X := X.base)).hom_ext _ _
  · exact (isInitialOfIsEmpty (X := X.curve.E)).hom_ext _ _

/-- **[RIG-3b core] The rigidity bridge at a fixed test object**: the per-object body of
`rigid_of_geom_free`, with the geometric-fibre detection demanded only at `X` itself.
Factored out so the bridge serves both the unrestricted form (`rigid_of_geom_free`) and
the noetherian-local form (`rigidNoeth_of_geom_free`, the [T-W7.8] variant — detection is
only available over locally noetherian bases until EGA IV §8 spreading-out exists).

Route: a fixed `prob`-value transports to a geometric fibre where the iso stays
nontrivial (`EllHom.fibre` machinery); `geom_surjective` lifts the fibre value to `Q`;
`geom_orbits` converts fixedness into a `γ`-twisted `Q`-fixed point, killed by `hfree`. -/
theorem ModuliProblem.QuotientProblemData.rigid_at_of_geom_free {Q : ModuliProblem R}
    {G : Type*} [Group G] [Finite G] {φ : G →* Aut Q}
    (qpd : ModuliProblem.QuotientProblemData φ) (X : EllObj R)
    (hdetectX : ∀ (e : X ≅ X) (he : e.hom.baseHom = 𝟙 X.base),
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
    ∀ (e : X ≅ X), e.hom.baseHom = 𝟙 X.base → e ≠ Iso.refl X →
      ∀ a : qpd.prob.obj (Opposite.op X), qpd.prob.map e.hom.op a ≠ a := by
  intro e he hne a hfix
  by_cases hbase : Nonempty X.base
  · -- geometric fibre where `e` stays nontrivial
    obtain ⟨k, _, _, t, hfib⟩ := hdetectX e he hne hbase
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

/-- **[RIG-3b] The rigidity bridge**: a quotient problem datum is rigid provided
(1) nontriviality of base-identical isos is DETECTED on some geometric fibre
(`hdetect` — [RIG-1], KM 2.7-adjacent), and (2) no nontrivial geometric iso fixes a
`γ`-twisted value of `Q` (`hfree` — [RIG-2], the k̄ orbit-freeness; for `Γ_H` this is
the `N ≥ 3` Serre argument + the `H`-condition). Body: `rigid_at_of_geom_free`. -/
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
    qpd.prob.Rigid :=
  fun X => qpd.rigid_at_of_geom_free X (hdetect X) hfree

/-- **[RIG-3b, noetherian-local] The rigidity bridge at `RigidNoeth`** ([T-W7.8] variant,
owner ruling v10.298): same bridge, with the geometric-fibre detection required only over
locally noetherian bases — which is all the T-W7.7 detection engine
(`exists_isoFibre_ne_refl`) can honestly supply without EGA IV §8 spreading-out. The
conclusion `RigidNoeth` is everything the KM 4.7.0 representability engine consumes
(`simulSchemeAction_free_of_rigidNoeth`), so the `Γ_H` headline sheds the `hLN` pin. -/
theorem ModuliProblem.QuotientProblemData.rigidNoeth_of_geom_free {Q : ModuliProblem R}
    {G : Type*} [Group G] [Finite G] {φ : G →* Aut Q}
    (qpd : ModuliProblem.QuotientProblemData φ)
    (hdetect : ∀ (X : EllObj R), IsLocallyNoetherian X.base →
      ∀ (e : X ≅ X) (he : e.hom.baseHom = 𝟙 X.base),
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
    qpd.prob.RigidNoeth :=
  fun X hX => qpd.rigid_at_of_geom_free X (hdetect X hX) hfree

variable (R : CommRingCat.{u})

/-- **[Γ_H rigidity, noetherian-local] (KM 4.7.2-shape at `RigidNoeth`, [T-W7.8]
variant)** — the quotient problem `P_H` is noetherian-locally rigid, assembled from the
PROVEN spine with **no `hLN` pin**: the bridge `rigidNoeth_of_geom_free` fed by the
PROVEN detection `exists_isoFibre_ne_refl` (at the level `N ≥ 3` itself, invertible by
`hinv` on every base through `nIsInvertible_over_spec`; the detection engine's
`IsLocallyNoetherian` instance now comes from the test object itself). The one remaining
NAMED PIN is `hfree` — the k̄ `H`-orbit-freeness: no nontrivial base-identical iso fixes
a `γ`-twisted full level structure. Its discharge is the [RIG-2] core
(`aut_endo_eq_one_of_fixes_point`, PROVEN clean) through the `glSmul`-matrix
translation + KM's keystone `hbound` (register-box until the K4 bridge lands). -/
theorem gammaH_rigidNoeth (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hinv : IsUnit (N : R))
    (qpd : ModuliProblem.QuotientProblemData (gammaHAut R N H))
    (hfree : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (sm : Spec (CommRingCat.of k) ⟶ Spec R)
      (E : EllipticCurve (Spec (CommRingCat.of k)))
      (e : (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R) ≅
        (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)),
      e.hom.baseHom = 𝟙 _ → e ≠ Iso.refl _ →
      ∀ (b : (gammaFullNaiveProblem R N).obj
          (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))) (γ : ↥H),
        (gammaHAut R N H γ).hom.app
          (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))
          ((gammaFullNaiveProblem R N).map e.hom.op b) ≠ b) :
    qpd.prob.RigidNoeth := by
  refine qpd.rigidNoeth_of_geom_free ?_ hfree
  intro X hX e he hne hbase
  haveI := hX
  exact EllObj.exists_isoFibre_ne_refl N hN
    (YFull.nIsInvertible_over_spec R X.structMap hinv) e he hne

/-- **[Γ_H rigidity, interface] (KM 4.7.2-shape)** — the literal KM 4.4 `Rigid` form,
from `gammaH_rigidNoeth` plus the `hLN` pin (T-W7.8: local noetherianity of all
`Ell/R`-bases — the unrestricted-detection gate, parked as [T-W7.8-L2-PARKED]; the
`.Representable` headline no longer consumes this form). -/
theorem gammaH_rigid (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hinv : IsUnit (N : R))
    (qpd : ModuliProblem.QuotientProblemData (gammaHAut R N H))
    (hLN : ∀ X : EllObj R, IsLocallyNoetherian X.base)
    (hfree : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (sm : Spec (CommRingCat.of k) ⟶ Spec R)
      (E : EllipticCurve (Spec (CommRingCat.of k)))
      (e : (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R) ≅
        (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)),
      e.hom.baseHom = 𝟙 _ → e ≠ Iso.refl _ →
      ∀ (b : (gammaFullNaiveProblem R N).obj
          (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))) (γ : ↥H),
        (gammaHAut R N H γ).hom.app
          (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))
          ((gammaFullNaiveProblem R N).map e.hom.op b) ≠ b) :
    qpd.prob.Rigid :=
  fun X => gammaH_rigidNoeth R N hN H hinv qpd hfree X (hLN X)

/-- **[Γ_H rigidity, general `H`, noetherian-local] (the charter goal at `RigidNoeth`,
[T-W7.8] variant)** — the quotient problem `P_H` is noetherian-locally rigid for any `H`,
given the ONE honest pin: the per-`H` finite-order arithmetic `hH` (no nontrivial
base-identical iso has `e^(orderOf γ) = refl` for `γ ∈ H` — the CM-unit/`H` intersection
condition, fed by KM's endomorphism-degree keystone). No `hLN`. Subsumes `Γ₁`/`Γ₀` as
special `H`. -/
theorem gammaH_rigidNoeth_of_orderOf (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hinv : IsUnit (N : R))
    (qpd : ModuliProblem.QuotientProblemData (gammaHAut R N H))
    (hH : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (sm : Spec (CommRingCat.of k) ⟶ Spec R)
      (E : EllipticCurve (Spec (CommRingCat.of k)))
      (e : (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R) ≅
        (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)),
      e.hom.baseHom = 𝟙 _ → e ≠ Iso.refl _ → ∀ γ : ↥H,
        isoPow e (orderOf ((γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))) =
          Iso.refl _ → False) :
    qpd.prob.RigidNoeth :=
  gammaH_rigidNoeth R N hN H hinv qpd
    (fun k _ _ sm E e he hne b γ =>
      gammaH_hfree_of_orderOf_absurd N hN hinv H hH k sm E e he hne b γ)

/-- **[Γ_H rigidity, general `H`] (KM 4.7.x-shape)** — the literal `Rigid` form, from
`gammaH_rigidNoeth_of_orderOf` plus the `hLN` pin (T-W7.8; the `.Representable` headline
no longer consumes this form). -/
theorem gammaH_rigid_of_orderOf (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hinv : IsUnit (N : R))
    (qpd : ModuliProblem.QuotientProblemData (gammaHAut R N H))
    (hLN : ∀ X : EllObj R, IsLocallyNoetherian X.base)
    (hH : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (sm : Spec (CommRingCat.of k) ⟶ Spec R)
      (E : EllipticCurve (Spec (CommRingCat.of k)))
      (e : (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R) ≅
        (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)),
      e.hom.baseHom = 𝟙 _ → e ≠ Iso.refl _ → ∀ γ : ↥H,
        isoPow e (orderOf ((γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))) =
          Iso.refl _ → False) :
    qpd.prob.Rigid :=
  fun X => gammaH_rigidNoeth_of_orderOf R N hN H hinv qpd hH X (hLN X)

/-- **[Γ_H `.Representable`, PREPPED on the shared engine]** — the moment OMEGA's T-E14
de-sorries the KM 4.7.0 engine (instantiated at level 3 + Legendre, consumed here through
`representable_iff_rigidNoeth`), `P_H` is representable: relative representability and
affineness come from `qpd` itself, rigidity from `gammaH_rigidNoeth_of_orderOf`. Pin:
`hH` (per-`H` finite-order, KM keystone) — nothing else. The former `hLN` pin (T-W7.8) is
GONE: the engine only ever consumes rigidity at locally noetherian bases
(owner ruling v10.298). -/
theorem gammaH_representable_of_orderOf (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))
    (hinv : IsUnit (N : R))
    (qpd : ModuliProblem.QuotientProblemData (gammaHAut R N H))
    (hH : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (sm : Spec (CommRingCat.of k) ⟶ Spec R)
      (E : EllipticCurve (Spec (CommRingCat.of k)))
      (e : (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R) ≅
        (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)),
      e.hom.baseHom = 𝟙 _ → e ≠ Iso.refl _ → ∀ γ : ↥H,
        isoPow e (orderOf ((γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))) =
          Iso.refl _ → False) :
    qpd.prob.Representable :=
  ModuliProblem.representable_of_affineOverEll_of_rigidNoeth qpd.prob qpd.affineOverEll
    qpd.affineOverEll.relativelyRepresentable
    (gammaH_rigidNoeth_of_orderOf R N hN H hinv qpd hH)

open EllipticCurve in
/-- **[Γ₁ k̄-core] (T-H9's rigidity content at a geometric point)** — over k̄, no
nontrivial base-identical self-iso fixes a Drinfeld `Γ₁(N)`-structure (`N ≥ 4`
invertible), modulo the two register-box pins: the T-D6b geometric-order box
(`HasExactOrder.pull_nsmul_ne_zero`, consumed through the statement) and the KM
kernel-degree keystone `hbound` (the **[RIG-2′] NARROWED contract**, v10.320
SUSPECT-RIG2: an ISO `ε` fixing a point of exact geometric order `N` is the identity —
the former all-pointed-`ε`/∀-`pts` shape was refutable by `ε = [N+1]`, and
iso-restricted at `N = 4` by `ε = [-1]` on `E[2]`; the single-exact-order-point form is
exactly what this consumer holds and survives both). Route: the fixed section is
`c`-fixed (`pullSection` `lift_fst`), its small multiples are nonzero (T-D6b at
`t = 𝟙`), `εO` is invertible from `e`, and the narrowed keystone kills. -/
theorem gammaOneDrinfeld_fix_absurd (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (hinv : IsUnit (N : R))
    (k : Type u) [Field k] [IsAlgClosed k]
    (sm : Spec (CommRingCat.of k) ⟶ Spec R)
    (E : EllipticCurve (Spec (CommRingCat.of k)))
    (e : (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R) ≅
      (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R))
    (he : e.hom.baseHom = 𝟙 _) (hne : e ≠ Iso.refl _)
    (b : (gammaOneDrinfeldProblem R N).obj
      (Opposite.op (⟨Spec (CommRingCat.of k), sm, E⟩ : EllObj R)))
    (hbound : ∀ ε : E.asOver ⟶ E.asOver, IsIso ε → η[E.asOver] ≫ ε = η[E.asOver] →
      ∀ P : E.Point (𝟙 (Spec (CommRingCat.of k))),
        (∀ a : ℕ, 0 < a → a < N → (a : ℤ) • P ≠ 0) →
        (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) P ≫ ε
          = (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) P →
        ε = 𝟙 E.asOver)
    (hfix : (gammaOneDrinfeldProblem R N).map e.hom.op b = b) : False := by
  classical
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of k)) := by
    haveI : IsNoetherianRing k := inferInstance
    infer_instance
  set c := e.hom.top with hc
  -- the section is fixed by `c`
  have h1 : EllHom.pullSection R e.hom b.1 = b.1 := congrArg (fun z => z.1) hfix
  have hPc : b.1.1 ≫ c = b.1.1 := by
    have hlf : (EllHom.pullSection R e.hom b.1).1 ≫ e.hom.top
        = e.hom.baseHom ≫ b.1.1 := e.hom.isPullback.lift_fst _ _ _
    rw [h1, he, Category.id_comp] at hlf
    exact hlf
  -- `c` as a pointed `Over`-endomorphism
  have hcπ : c ≫ E.π = E.π := by
    have h := e.hom.isPullback.w
    rw [he, Category.comp_id] at h
    exact h
  set εO : E.asOver ⟶ E.asOver := Over.homMk c hcπ with hεO
  have hzc : E.zero ≫ c = E.zero := by
    have h := e.hom.zero_w
    rw [he, Category.id_comp] at h
    exact h
  have hη : η[E.asOver] ≫ εO = η[E.asOver] := by
    refine Over.OverMorphism.ext ?_
    show (η[E.asOver]).left ≫ c = (η[E.asOver]).left
    rw [E.one_eq_zero]
    have s1 : ((𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ E.zero) ≫ c
        = (𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ E.zero ≫ c := Category.assoc _ _ _
    have s2 : (𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ E.zero ≫ c
        = (𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ E.zero :=
      congrArg (fun mm => (𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ mm) hzc
    exact s1.trans s2
  -- the geometric order facts at the base point itself (T-E4F1/T-E4F2: the
  -- invertible-`N` instances, bypassing the statement-protected over-`ℤ` boxes)
  have hinvSpec : NIsInvertible (Spec (CommRingCat.of k)) N := by
    have hinvk : IsUnit ((N : ℕ) : k) := by
      have h := hinv.map (Spec.preimage sm).hom
      rwa [map_natCast] at h
    show IsUnit ((N : ℕ) : Γ(Spec (CommRingCat.of k), ⊤))
    have h2 := hinvk.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    rwa [map_natCast] at h2
  have hpull_id : Point.pull E (𝟙 (Spec (CommRingCat.of k))) b.1 = b.1 :=
    Subtype.ext (Category.id_comp _)
  have hord : ∀ a : ℕ, 0 < a → a < N → (a : ℤ) • b.1 ≠ 0 := by
    intro a ha0 haN
    have h := b.2.pull_nsmul_ne_zero_of_invertible E hinvSpec k
      (𝟙 (Spec (CommRingCat.of k))) ha0 haN
    rwa [hpull_id] at h
  -- the equiv-form fix and the [RIG-2′] core (the NARROWED keystone contract:
  -- `εO` is an automorphism — invertible from `e` — fixing the exact-order-`N` point)
  have hfix' : (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) b.1 ≫ εO
      = (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) b.1 := by
    refine Over.OverMorphism.ext ?_
    show b.1.1 ≫ c = b.1.1
    exact hPc
  haveI hIsoε : IsIso εO := by
    have hcπ' : e.inv.top ≫ E.π = E.π := by
      have h := e.inv.isPullback.w
      rw [EllObj.isoInv_baseHom e he, Category.comp_id] at h
      exact h
    exact ⟨Over.homMk e.inv.top hcπ',
      Over.OverMorphism.ext (congrArg EllHom.top e.hom_inv_id),
      Over.OverMorphism.ext (congrArg EllHom.top e.inv_hom_id)⟩
  have hεid : εO = 𝟙 E.asOver := hbound εO hIsoε hη b.1 hord hfix'
  have hcid : c = 𝟙 E.E := congrArg CommaMorphism.left hεid
  exact hne (Iso.ext (EllHom.ext he hcid))

open EllipticCurve in
/-- **[Γ₁ rigidity, noetherian-local] (T-H9's Rigid half at `RigidNoeth`; [T-W7.8]
variant)** — the Drinfeld `Γ₁(N)` problem is noetherian-locally rigid for `N ≥ 4`
invertible, at the pins `hbound` (the KM kernel-degree keystone, ∀-geometric-point form)
+ the T-D6b register box (in the statement of the k̄-core) — **no `hLN`**: the detection
engine's `IsLocallyNoetherian` instance comes from the test object. Route: the PROVEN
detection (`exists_isoFibre_ne_refl`, at level `N`) finds a geometric fibre where the iso
stays nontrivial; the fixed structure transports along the fibre square; the k̄-core
(`gammaOneDrinfeld_fix_absurd`) kills. Unblocks KM's Drinfeld `.Representable` wiring
(with their `gammaOneDrinfeld_affineOverEll` + the shared T-E14 engine). -/
theorem gammaOneDrinfeld_rigidNoeth (N : ℕ) [NeZero N] (hN : 4 ≤ N) (hinv : IsUnit (N : R))
    (hbound : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (sm : Spec (CommRingCat.of k) ⟶ Spec R)
      (E : EllipticCurve (Spec (CommRingCat.of k)))
      (ε : E.asOver ⟶ E.asOver), IsIso ε → η[E.asOver] ≫ ε = η[E.asOver] →
      ∀ P : E.Point (𝟙 (Spec (CommRingCat.of k))),
        (∀ a : ℕ, 0 < a → a < N → (a : ℤ) • P ≠ 0) →
        (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) P ≫ ε
          = (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) P →
        ε = 𝟙 E.asOver) :
    (gammaOneDrinfeldProblem R N).RigidNoeth := by
  intro X hX e he hne a hfix
  haveI := hX
  have hN3 : 3 ≤ (N : ℤ) := by exact_mod_cast Nat.le_of_succ_le hN
  obtain ⟨k, _, _, t, hfib⟩ := EllObj.exists_isoFibre_ne_refl N hN3
    (YFull.nIsInvertible_over_spec R X.structMap hinv) e he hne
  set eT := EllObj.isoFibre e he t with heT
  have hcomp : eT.hom ≫ X.pullbackAlongπ t = X.pullbackAlongπ t ≫ e.hom :=
    EllHom.fibre_pullbackAlongπ e.hom he t
  set aT := (gammaOneDrinfeldProblem R N).map (X.pullbackAlongπ t).op a with haT
  have hfixT : (gammaOneDrinfeldProblem R N).map eT.hom.op aT = aT := by
    calc (gammaOneDrinfeldProblem R N).map eT.hom.op aT
        = (gammaOneDrinfeldProblem R N).map ((X.pullbackAlongπ t).op ≫ eT.hom.op) a := by
          rw [haT, ← Functor.map_comp_apply]
      _ = (gammaOneDrinfeldProblem R N).map (e.hom.op ≫ (X.pullbackAlongπ t).op) a := by
          rw [← op_comp, ← op_comp, hcomp]
      _ = (gammaOneDrinfeldProblem R N).map (X.pullbackAlongπ t).op
            ((gammaOneDrinfeldProblem R N).map e.hom.op a) := by
          rw [Functor.map_comp_apply]
      _ = aT := by rw [hfix, haT]
  exact gammaOneDrinfeld_fix_absurd R N hN hinv k (t ≫ X.structMap) (X.curve.baseChange t)
    eT rfl hfib aT (hbound k (t ≫ X.structMap) (X.curve.baseChange t)) hfixT

open EllipticCurve in
/-- **[Γ₁ rigidity] (T-H9's Rigid half; KM 5.x-shape)** — the literal `Rigid` form, from
`gammaOneDrinfeld_rigidNoeth` plus the `hLN` pin (T-W7.8; the `.Representable` headline
no longer consumes this form). -/
theorem gammaOneDrinfeld_rigid (N : ℕ) [NeZero N] (hN : 4 ≤ N) (hinv : IsUnit (N : R))
    (hLN : ∀ X : EllObj R, IsLocallyNoetherian X.base)
    (hbound : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (sm : Spec (CommRingCat.of k) ⟶ Spec R)
      (E : EllipticCurve (Spec (CommRingCat.of k)))
      (ε : E.asOver ⟶ E.asOver), IsIso ε → η[E.asOver] ≫ ε = η[E.asOver] →
      ∀ P : E.Point (𝟙 (Spec (CommRingCat.of k))),
        (∀ a : ℕ, 0 < a → a < N → (a : ℤ) • P ≠ 0) →
        (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) P ≫ ε
          = (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) P →
        ε = 𝟙 E.asOver) :
    (gammaOneDrinfeldProblem R N).Rigid :=
  fun X => gammaOneDrinfeld_rigidNoeth R N hN hinv hbound X (hLN X)

/-- **[Γ₁ `.Representable`, PREPPED on the shared engine]** — the moment OMEGA's T-E14
lands (consumed through `representable_iff_rigidNoeth`), the Drinfeld `Γ₁(N)` problem is
representable: affineness is KM's `gammaOneDrinfeld_affineOverEll`, rigidity is
`gammaOneDrinfeld_rigidNoeth`. Pin: `hbound` (+ the register boxes in the statements).
The former `hLN` pin (T-W7.8) is GONE (owner ruling v10.298). -/
theorem gammaOneDrinfeld_representable_prep (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (hinv : IsUnit (N : R))
    (hbound : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (sm : Spec (CommRingCat.of k) ⟶ Spec R)
      (E : EllipticCurve (Spec (CommRingCat.of k)))
      (ε : E.asOver ⟶ E.asOver), IsIso ε → η[E.asOver] ≫ ε = η[E.asOver] →
      ∀ P : E.Point (𝟙 (Spec (CommRingCat.of k))),
        (∀ a : ℕ, 0 < a → a < N → (a : ℤ) • P ≠ 0) →
        (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) P ≫ ε
          = (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) P →
        ε = 𝟙 E.asOver) :
    (gammaOneDrinfeldProblem R N).Representable :=
  ModuliProblem.representable_of_affineOverEll_of_rigidNoeth _
    (gammaOneDrinfeld_affineOverEll N hinv)
    (gammaOneDrinfeld_affineOverEll N hinv).relativelyRepresentable
    (gammaOneDrinfeld_rigidNoeth R N hN hinv hbound)

/-- **[Γ(N) rigidity] (KM 2.7.2 upgraded to the quotient problem at `H = ⊥`)** — the
quotient problem `P_⊥ = [Γ(N)]` is rigid for `N ≥ 3` invertible, with the k̄
orbit-freeness discharged OUTRIGHT (`gammaFullNaive_hfree_bot`); only the `hLN`
locally-noetherian pin (T-W7.8 gate) remains. -/
theorem gammaBot_rigid (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ)) (hinv : IsUnit (N : R))
    (qpd : ModuliProblem.QuotientProblemData
      (gammaHAut R N (⊥ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N)))))
    (hLN : ∀ X : EllObj R, IsLocallyNoetherian X.base) :
    qpd.prob.Rigid :=
  gammaH_rigid R N hN ⊥ hinv qpd hLN
    (fun k _ _ sm E e he hne b γ =>
      gammaFullNaive_hfree_bot N hN hinv k sm E e he hne b γ)

/-- **[Γ(N) rigidity, noetherian-local]** — `gammaBot_rigid` at `RigidNoeth` ([T-W7.8]
variant): PIN-FREE — the k̄ orbit-freeness is discharged outright
(`gammaFullNaive_hfree_bot`) and no `hLN` is consumed. `P_⊥ = [Γ(N)]` is
noetherian-locally rigid, unconditionally (for `N ≥ 3` invertible). -/
theorem gammaBot_rigidNoeth (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ)) (hinv : IsUnit (N : R))
    (qpd : ModuliProblem.QuotientProblemData
      (gammaHAut R N (⊥ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N))))) :
    qpd.prob.RigidNoeth :=
  gammaH_rigidNoeth R N hN ⊥ hinv qpd
    (fun k _ _ sm E e he hne b γ =>
      gammaFullNaive_hfree_bot N hN hinv k sm E e he hne b γ)

/-- **[Γ(N) = Y(N) `.Representable`, PREPPED]** — at `H = ⊥` the `hH` pin is free and the
former `hLN` pin is GONE (owner ruling v10.298), so Y(N)'s representability is gated on
EXACTLY the shared T-E14 engine (`representable_iff_rigidNoeth`'s ⇐) — no other pin. -/
theorem gammaBot_representable (N : ℕ) [NeZero N] (hN : 3 ≤ (N : ℤ))
    (hinv : IsUnit (N : R))
    (qpd : ModuliProblem.QuotientProblemData
      (gammaHAut R N (⊥ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod N))))) :
    qpd.prob.Representable :=
  ModuliProblem.representable_of_affineOverEll_of_rigidNoeth qpd.prob qpd.affineOverEll
    qpd.affineOverEll.relativelyRepresentable
    (gammaBot_rigidNoeth R N hN hinv qpd)


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

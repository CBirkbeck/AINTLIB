/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.WeierstrassModel
import Mathlib.AlgebraicGeometry.Fiber

/-!
# Elliptic curves over a base scheme: the geometric record

Per the expert-review integration (2026-07-05), elliptic curves are packaged in **two
records**:

* `EllipticCurveGeom` (this file): the pure geometry — a morphism `π : E ⟶ S`, smooth of
  relative dimension 1 and proper, a section `0 : S ⟶ E`, and — the **definition of record**
  (owner-directed + expert-review v8, 2026-07-06) — the **Zariski-local-Weierstrass**
  condition `localModel : LocallyWeierstrass` (`E` is locally on `S` the projective
  Weierstrass model of an elliptic Weierstrass curve). This is the *executable* route to
  modular curves: it gives explicit local equations, coordinate changes, and the
  quotient-stack atlas without coherent cohomology. It **implies** the abstract genus-1
  fibre condition (`fibrewiseElliptic` / `FibrewiseElliptic`, kept below as the derived,
  Phase-4-comparison target — DR II.1.1 / KM 2.1.1 / Loeffler Def 3.3.1: *"a scheme `ℰ`
  with `π : ℰ → S` proper and flat, all fibres smooth genus-1, and a section `0`"*). The
  converse (genus-1 ⟹ locally Weierstrass) is the deferred Chain-A7 comparison (`T-W-cmp`,
  coherent-cohomology stream), off the critical path to `Y(N)`.
* `EllipticCurve` (`GroupLaw.lean`): the working record for the Katz–Mazur programme —
  the geometry **together with** a commutative group-scheme structure whose identity is
  the zero section. Mathematically the group datum is redundant (Abel), but it is the
  object KM Ch. 1 actually consumes ("a smooth commutative group-scheme of relative
  dimension one", KM 1.4.1), and carrying it as data unblocks the entire
  level-structure theory from the Picard/Abel chain. The canonicity theorems
  (`EllipticCurveGeom` admits a unique such enrichment) are the deferred
  "purity/comparison" project — see `GroupLaw.lean`.

## The genus-1 fibre condition (bridge form)

Mathlib has no coherent cohomology yet, so "genus 1" is not directly expressible. We
use the classical equivalent (Riemann–Roch over a field, black box BB-RR; Silverman
III.3.1): *a pointed smooth proper geometrically connected genus-1 curve over a field
is exactly a pointed plane Weierstrass cubic with unit discriminant.* Per the expert
review (Q2 answer), the condition is phrased as a **pointed isomorphism of
`κ(s)`-schemes** with the projective Weierstrass model — not as a functor-of-points
identification. Once coherent cohomology lands, the equivalence with the genus
formulation becomes a theorem (ticket `T-A9`, API gap AG-COH) and the geometric-fibre
genus form becomes the statement of record.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

/-- The point of the fibre `π.fiber s` induced by a section `z : S ⟶ E` of `π`. -/
noncomputable def sectionFiberPoint {E S : Scheme.{u}} (π : E ⟶ S) (z : S ⟶ E)
    (hz : z ≫ π = 𝟙 S) (s : S) : Spec (S.residueField s) ⟶ π.fiber s :=
  pullback.lift (S.fromSpecResidueField s ≫ z) (𝟙 _)
    (by simp [Category.assoc, hz])

/-- **The fibre condition** (bridge form, per expert review Q2): every fibre of `π`,
pointed by the zero section, is *pointed-isomorphic as a `κ(s)`-scheme* to the
projective Weierstrass model of some elliptic (unit-discriminant) Weierstrass curve
over the residue field. By Riemann–Roch over a field (black box BB-RR) this is
equivalent to: every fibre is a smooth proper geometrically connected genus-1 curve.
Source: Loeffler Def 3.3.1; KM 2.1.1; phrasing per reviewer (scheme isomorphism, not
functor of points). -/
def FibrewiseElliptic {E S : Scheme.{u}} (π : E ⟶ S) (z : S ⟶ E) (hz : z ≫ π = 𝟙 S) :
    Prop :=
  ∀ s : S, ∃ W : WeierstrassCurve (S.residueField s), W.IsElliptic ∧
    ∃ e : π.fiber s ≅ projModel W,
      e.hom ≫ projModelπ W = π.fiberToSpecResidueField s ∧
      sectionFiberPoint π z hz s ≫ e.hom = projModelZero W

set_option backward.isDefEq.respectTransparency false in
/-- **(T-A5b)** Fibrewise ellipticity is stable under base change: the fibre of the
pulled-back family at `t` is the fibre at `g t` extended to `κ(t)`, and the projective
Weierstrass model base-changes accordingly (`isPullback_projModelBaseChange`). -/
lemma FibrewiseElliptic.baseChange {E S T : Scheme.{u}} {π : E ⟶ S} {z : S ⟶ E}
    {hz : z ≫ π = 𝟙 S} (h : FibrewiseElliptic π z hz) (g : T ⟶ S) :
    FibrewiseElliptic (pullback.snd π g)
      (pullback.lift (g ≫ z) (𝟙 T)
        (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp]))
      (pullback.lift_snd _ _ _) := by
  intro t
  obtain ⟨W, hell, e_s, heπ, hez⟩ := h (g t)
  letI : Algebra (S.residueField (g t)) (T.residueField t) :=
    (g.residueFieldMap t).hom.toAlgebra
  haveI := hell
  have hA : IsPullback
      (((pullback.map (pullback.snd π g) (T.fromSpecResidueField t) π
          (S.fromSpecResidueField (g t)) (pullback.fst π g)
          (Spec.map (g.residueFieldMap t)) g
          (IsPullback.of_hasPullback π g).w.symm (by simp)) :
        (pullback.snd π g).fiber t ⟶ π.fiber (g t)) ≫ e_s.hom)
      ((pullback.snd π g).fiberToSpecResidueField t)
      (projModelπ W) (Spec.map (g.residueFieldMap t)) := by
    refine (isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback π g) t).of_iso (Iso.refl _) e_s (Iso.refl _) (Iso.refl _)
      (by simp) (by simp)
      (by rw [Iso.refl_hom, Category.comp_id]; exact heπ.symm) (by simp)
  have hB : IsPullback
      (projModelBaseChange (algebraMap (S.residueField (g t)) (T.residueField t)) W)
      (projModelπ (W.map (algebraMap (S.residueField (g t)) (T.residueField t))))
      (projModelπ W) (Spec.map (g.residueFieldMap t)) := by
    have hbc := isPullback_projModelBaseChange (R' := T.residueField t) W
    rwa [show CommRingCat.ofHom
      (algebraMap (S.residueField (g t)) (T.residueField t)) =
      g.residueFieldMap t from rfl] at hbc
  refine ⟨W.map (algebraMap (S.residueField (g t)) (T.residueField t)), inferInstance,
    hA.isoPullback ≪≫ hB.isoPullback.symm, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [(Iso.inv_comp_eq _).mpr hB.isoPullback_hom_snd.symm, hA.isoPullback_hom_snd]
  · rw [← cancel_mono hB.isoPullback.hom]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    have hnat : sectionFiberPoint (pullback.snd π g) (pullback.lift (g ≫ z) (𝟙 T)
          (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp]))
          (pullback.lift_snd _ _ _) t ≫
        ((pullback.map (pullback.snd π g) (T.fromSpecResidueField t) π
          (S.fromSpecResidueField (g t)) (pullback.fst π g)
          (Spec.map (g.residueFieldMap t)) g
          (IsPullback.of_hasPullback π g).w.symm (by simp)) :
          (pullback.snd π g).fiber t ⟶ π.fiber (g t)) =
        Spec.map (g.residueFieldMap t) ≫ sectionFiberPoint π z hz (g t) := by
      apply pullback.hom_ext
      · simp [sectionFiberPoint, Category.assoc]
      · simp [sectionFiberPoint, Category.assoc]
        exact Category.id_comp _
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hA.isoPullback_hom_fst, hB.isoPullback_hom_fst, projModelZero_baseChange,
        show Spec.map (CommRingCat.ofHom (algebraMap (S.residueField (g t))
          (T.residueField t))) = Spec.map (g.residueFieldMap t) from rfl,
        ← hez, reassoc_of% hnat]
    · simp only [Category.assoc]
      rw [hA.isoPullback_hom_snd, hB.isoPullback_hom_snd, projModelZero_projModelπ]
      exact pullback.lift_snd _ _ _

/-- **The local-model condition** (v2, owner-directed 2026-07-06): every point of `S`
has an affine open neighbourhood `U` over which `E`, pointed by the zero section, is
isomorphic — as a scheme over `Γ(S, U)` (via `U ≅ Spec Γ(S, U)`), compatibly with `π`
and the section — to the projective Weierstrass model of some elliptic Weierstrass curve
`W / Γ(S, U)`. A-priori stronger than `FibrewiseElliptic`, which it implies
(`EllipticCurveGeom.fibrewiseElliptic`); the converse is the Chain-A7 comparison
(`T-A7-cmp`, gated on coherent cohomology + BB-RR). Source: KM 2.2.5–2.2.6; GME 2.2.4;
owner directive 2026-07-06. -/
def LocallyWeierstrass {E S : Scheme.{u}} (π : E ⟶ S) (z : S ⟶ E) (hz : z ≫ π = 𝟙 S) :
    Prop :=
  ∀ s : S, ∃ (U : S.affineOpens) (_ : s ∈ U.1) (W : WeierstrassCurve Γ(S, U.1)),
    W.IsElliptic ∧
    ∃ e : pullback π U.1.ι ≅ projModel W,
      e.hom ≫ projModelπ W = pullback.snd π U.1.ι ≫ U.2.isoSpec.hom ∧
      (U.2.isoSpec.inv ≫ pullback.lift (U.1.ι ≫ z) (𝟙 _)
          (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp])) ≫ e.hom =
        projModelZero W

/-- **The `isoSpec`–`appLE` bridge.** For affine opens `V ⊆ g ⁻¹ᵁ U`, conjugating the
ring-level restriction `g.appLE U V` by the two `isoSpec` isomorphisms recovers the induced
scheme morphism `V ⟶ U` — namely `homOfLE` into `g ⁻¹ᵁ U` followed by the restriction
`g ∣_ U`. This is the geometric content of `IsAffineOpen.SpecMap_appLE_fromSpec` transported
across the `isoSpec` identifications. -/
lemma isoSpec_appLE_bridge {S T : Scheme.{u}} (g : T ⟶ S) (U : S.affineOpens)
    (V : T.affineOpens) (hVle : V.1 ≤ g ⁻¹ᵁ U.1) :
    V.2.isoSpec.hom ≫ Spec.map (g.appLE U.1 V.1 hVle) =
      (T.homOfLE hVle ≫ (g ∣_ U.1)) ≫ U.2.isoSpec.hom := by
  have hgVfac : (T.homOfLE hVle ≫ (g ∣_ U.1)) ≫ U.1.ι = V.1.ι ≫ g := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  have hsp := IsAffineOpen.SpecMap_appLE_fromSpec g U.2 V.2 hVle
  rw [← IsAffineOpen.isoSpec_inv_ι U.2, ← IsAffineOpen.isoSpec_inv_ι V.2, ← Category.assoc,
    Category.assoc V.2.isoSpec.inv, ← hgVfac, ← Category.assoc] at hsp
  have hsp2 := (cancel_mono U.1.ι).mp hsp
  rw [← Iso.comp_inv_eq, Category.assoc, hsp2, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- **(T-A8a)** The local-model condition is stable under base change: shrink the model's
affine open `U ∋ g t` to an affine `V ∋ t` inside `g⁻¹ U`, transport the Weierstrass
curve `W` along `Γ(S, U) → Γ(T, V)` (`g.appLE`), and paste the pullbacks. -/
lemma LocallyWeierstrass.baseChange {E S T : Scheme.{u}} {π : E ⟶ S} {z : S ⟶ E}
    {hz : z ≫ π = 𝟙 S} (h : LocallyWeierstrass π z hz) (g : T ⟶ S) :
    LocallyWeierstrass (pullback.snd π g)
      (pullback.lift (g ≫ z) (𝟙 T)
        (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp]))
      (pullback.lift_snd _ _ _) := by
  intro t
  obtain ⟨U, hsU, W, hell, e, heπ, hez⟩ := h (g.base t)
  obtain ⟨V, hVaff, htV, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    T.isBasis_affineOpens (show t ∈ g ⁻¹ᵁ U.1 from hsU)
  replace hVaff : IsAffineOpen V := hVaff
  letI : Algebra ↑Γ(S, U.1) ↑Γ(T, V) := ((g.appLE U.1 V hVle).hom).toAlgebra
  refine ⟨⟨V, hVaff⟩, htV, W.map (algebraMap ↑Γ(S, U.1) ↑Γ(T, V)), inferInstance, ?_⟩
  -- `gV : V ⟶ U` factoring `V.ι ≫ g` through the open immersion `U.ι`
  set Vι := (⟨V, hVaff⟩ : T.affineOpens).1.ι
  set gV := T.homOfLE hVle ≫ (g ∣_ U.1) with hgV
  have hgVfac : gV ≫ U.1.ι = Vι ≫ g := by
    rw [hgV, Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  have hB : IsPullback (projModelBaseChange (algebraMap ↑Γ(S, U.1) ↑Γ(T, V)) W)
      (projModelπ (W.map (algebraMap ↑Γ(S, U.1) ↑Γ(T, V)))) (projModelπ W)
      (Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(S, U.1) ↑Γ(T, V)))) :=
    isPullback_projModelBaseChange W
  -- the restriction is a pullback of `π` along `Vι ≫ g` (paste the two base squares)
  have hP1 : IsPullback (pullback.fst (pullback.snd π g) Vι ≫ pullback.fst π g)
      (pullback.snd (pullback.snd π g) Vι) π (Vι ≫ g) :=
    (IsPullback.of_hasPullback (pullback.snd π g) Vι).paste_horiz
      (IsPullback.of_hasPullback π g)
  have hP1' : IsPullback (pullback.fst (pullback.snd π g) Vι ≫ pullback.fst π g)
      (pullback.snd (pullback.snd π g) Vι) π (gV ≫ U.1.ι) := by rw [hgVfac]; exact hP1
  -- cancel the U-square: the restriction is a pullback of `pullback.snd π U.1.ι` along `gV`
  have hP2 := hP1'.of_right' (IsPullback.of_hasPullback π U.1.ι)
  -- the isoSpec ↔ appLE bridge (comm₄): `Spec.map φ` conjugated by the two `isoSpec`s is `gV`
  have hbridge : hVaff.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(S, U.1) ↑Γ(T, V))) = gV ≫ U.2.isoSpec.hom :=
    isoSpec_appLE_bridge g U ⟨V, hVaff⟩ hVle
  -- `e' := restriction ≅ pullback(snd π U.1.ι, gV) ≅ pullback(projModelπ W, Spec.map φ)`
  -- `      ≅ projModel W'`
  refine ⟨hP2.isoPullback ≪≫ asIso (pullback.map (pullback.snd π U.1.ι) gV (projModelπ W)
      (Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(S, U.1) ↑Γ(T, V)))) e.hom hVaff.isoSpec.hom
      U.2.isoSpec.hom heπ.symm hbridge.symm) ≪≫ hB.isoPullback.symm, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
    rw [(Iso.inv_comp_eq _).mpr hB.isoPullback_hom_snd.symm, pullback.lift_snd, ← Category.assoc,
      hP2.isoPullback_hom_snd]
  · rw [← cancel_mono hB.isoPullback.hom]
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    apply pullback.hom_ext
    · -- h₀ (fst / section). After `simp only [Category.assoc, pullback.lift_fst,
      -- hB.isoPullback_hom_fst]` the goal is
      --   `isoSpecV.inv ≫ sVlift ≫ hP2top ≫ e.hom = projModelZero W' ≫ projModelBaseChange`.
      -- FINAL STEP (T-A8a, fully derived): the section naturality
      --   `hnat : sVlift ≫ hP2top = gV ≫ sU`  (sU := pullback.lift (U.1.ι ≫ z) (𝟙 ↑U) …),
      -- proven by `pullback.hom_ext` on `pullback π U.1.ι`:
      --   · fst: sVlift≫hP2top≫fst(π,U.1.ι) = Vι≫g≫z = gV≫U.1.ι≫z = (gV≫sU)≫fst
      --     [lift_fst ×3 + hgVfac];
      --   · snd: sVlift≫hP2top≫snd(π,U.1.ι) = 𝟙≫gV = gV = (gV≫sU)≫snd            [lift_snd ×2].
      -- Then rw hnat; from hez, `sU ≫ e.hom = isoSpecU.hom ≫ projModelZero W`; from hbridge,
      -- `isoSpecV.inv ≫ gV ≫ isoSpecU.hom = Spec.map φ`; finish with `projModelZero_baseChange`.
      simp only [Category.assoc, pullback.lift_fst, hB.isoPullback_hom_fst]
      have hnat : pullback.lift (Vι ≫ pullback.lift (g ≫ z) (𝟙 T)
            (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp])) (𝟙 _)
            (by rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]) ≫
            hP2.isoPullback.hom ≫ pullback.fst (pullback.snd π U.1.ι) gV =
          gV ≫ pullback.lift (U.1.ι ≫ z) (𝟙 _)
            (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp]) := by
        refine pullback.hom_ext ?_ ?_
        · simp only [Category.assoc, hP2.isoPullback_hom_fst_assoc, IsPullback.lift_fst,
            pullback.lift_fst_assoc, pullback.lift_fst]
          rw [reassoc_of% hgVfac]
        · simp only [Category.assoc, hP2.isoPullback_hom_fst_assoc, IsPullback.lift_snd,
            pullback.lift_snd_assoc, pullback.lift_snd, Category.id_comp, Category.comp_id]
      have hsU : pullback.lift (U.1.ι ≫ z) (𝟙 _)
            (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp]) ≫ e.hom =
          U.2.isoSpec.hom ≫ projModelZero W := by
        rw [← hez]; simp
      rw [reassoc_of% hnat, hsU, ← reassoc_of% hbridge, Iso.inv_hom_id_assoc,
        projModelZero_baseChange]
    · simp only [Category.assoc, hB.isoPullback_hom_snd, pullback.lift_snd]
      rw [hP2.isoPullback_hom_snd_assoc, pullback.lift_snd_assoc, Category.id_comp,
        Iso.inv_hom_id]
      exact (projModelZero_projModelπ _).symm

/-- `LocallyWeierstrass` respects isomorphisms of the total space over the same base: transport
the chart isos through the induced pullback comparison (`IsPullback.of_iso` + `isoIsPullback`). -/
theorem LocallyWeierstrass.of_iso_over {E₁ E₂ S : Scheme.{u}}
    {π₁ : E₁ ⟶ S} {z₁ : S ⟶ E₁} {hz₁ : z₁ ≫ π₁ = 𝟙 S}
    {π₂ : E₂ ⟶ S} {z₂ : S ⟶ E₂} {hz₂ : z₂ ≫ π₂ = 𝟙 S}
    (h : LocallyWeierstrass π₁ z₁ hz₁) (e : E₂ ≅ E₁)
    (hπ : e.hom ≫ π₁ = π₂) (hzc : z₂ ≫ e.hom = z₁) :
    LocallyWeierstrass π₂ z₂ hz₂ := by
  intro s
  obtain ⟨U, hsU, W, hell, e₁, heπ, hez⟩ := h s
  have hP₂ : IsPullback (pullback.fst π₂ U.1.ι ≫ e.hom) (pullback.snd π₂ U.1.ι) π₁ U.1.ι := by
    refine (IsPullback.of_hasPullback π₂ U.1.ι).of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.id_comp]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    · rw [Iso.refl_hom, Category.comp_id, hπ]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  set eP : pullback π₂ U.1.ι ≅ pullback π₁ U.1.ι :=
    hP₂.isoIsPullback _ _ (IsPullback.of_hasPullback π₁ U.1.ι) with heP
  refine ⟨U, hsU, W, hell, eP ≪≫ e₁, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, heπ, ← Category.assoc, heP,
      IsPullback.isoIsPullback_hom_snd]
  · rw [← hez, Iso.trans_hom, ← Category.assoc]
    congr 1
    rw [Category.assoc, cancel_epi (U.2.isoSpec.inv)]
    apply pullback.hom_ext
    · rw [Category.assoc, IsPullback.isoIsPullback_hom_fst, pullback.lift_fst_assoc,
        pullback.lift_fst, Category.assoc, hzc]
    · rw [Category.assoc, IsPullback.isoIsPullback_hom_snd, pullback.lift_snd, pullback.lift_snd]

/-- `LocallyWeierstrass` respects isomorphisms of the whole triple (total space AND base):
base-change along `eS.hom` (`LocallyWeierstrass.baseChange`) + the canonical iso
`E₂ ≅ pullback π₁ eS.hom` (`of_horiz_isIso`) + `of_iso_over`. Used to transport the quotient
curve's local model from `Spec Γ(X,⊤)ᴳ` back to `X/G` in `[a5]`. -/
theorem LocallyWeierstrass.of_iso {E₁ S₁ E₂ S₂ : Scheme.{u}}
    {π₁ : E₁ ⟶ S₁} {z₁ : S₁ ⟶ E₁} {hz₁ : z₁ ≫ π₁ = 𝟙 S₁}
    {π₂ : E₂ ⟶ S₂} {z₂ : S₂ ⟶ E₂} {hz₂ : z₂ ≫ π₂ = 𝟙 S₂}
    (h : LocallyWeierstrass π₁ z₁ hz₁) (eE : E₂ ≅ E₁) (eS : S₂ ≅ S₁)
    (hπc : eE.hom ≫ π₁ = π₂ ≫ eS.hom) (hzc : eS.hom ≫ z₁ = z₂ ≫ eE.hom) :
    LocallyWeierstrass π₂ z₂ hz₂ := by
  have hsq : IsPullback eE.hom π₂ π₁ eS.hom := IsPullback.of_horiz_isIso ⟨hπc⟩
  refine (h.baseChange eS.hom).of_iso_over hsq.isoPullback hsq.isoPullback_hom_snd ?_
  apply pullback.hom_ext
  · rw [Category.assoc, hsq.isoPullback_hom_fst, pullback.lift_fst, ← hzc]
  · rw [Category.assoc, hsq.isoPullback_hom_snd, pullback.lift_snd, hz₂]

/-- On the spectrum of a ring, the canonical map from the residue field at a point is
`Spec` of the ring-level residue composite. -/
lemma Spec_fromSpecResidueField_eq (R : Type u) [CommRing R] (p : ↥(Spec (CommRingCat.of R))) :
    (Spec (CommRingCat.of R)).fromSpecResidueField p
      = Spec.map (StructureSheaf.toStalk R p ≫ (Spec (CommRingCat.of R)).residue p) := by
  show Spec.map ((Spec (CommRingCat.of R)).residue p)
      ≫ (Spec (CommRingCat.of R)).fromSpecStalk p = _
  rw [Spec.fromSpecStalk_eq']
  exact (Spec.map_comp _ _).symm

/-- **(T-A8-4, sub-lemma)** The fibres of a projective Weierstrass model over any ring are
elliptic: the fibre at `p` is the model of `W` extended to the residue field `κ(p)`
(`isPullback_projModelBaseChange` against the fibre square, both over
`Spec κ(p) ⟶ Spec R`). -/
theorem fibrewiseElliptic_projModel {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    [W.IsElliptic] :
    FibrewiseElliptic (projModelπ W) (projModelZero W) (projModelZero_projModelπ W) := by
  intro p
  letI : Algebra R ↑((Spec (CommRingCat.of R)).residueField p) :=
    (StructureSheaf.toStalk R p ≫ (Spec (CommRingCat.of R)).residue p).hom.toAlgebra
  -- everything below is stated over the single canonical morphism `ψ`
  have hfib : IsPullback ((projModelπ W).fiberι p)
      ((projModelπ W).fiberToSpecResidueField p) (projModelπ W)
      (Spec.map (StructureSheaf.toStalk R p ≫ (Spec (CommRingCat.of R)).residue p)) :=
    Spec_fromSpecResidueField_eq R p ▸ IsPullback.of_hasPullback (projModelπ W)
      ((Spec (CommRingCat.of R)).fromSpecResidueField p)
  have hbc : IsPullback
      (projModelBaseChange (algebraMap R ↑((Spec (CommRingCat.of R)).residueField p)) W)
      (projModelπ (W.map (algebraMap R ↑((Spec (CommRingCat.of R)).residueField p))))
      (projModelπ W)
      (Spec.map (StructureSheaf.toStalk R p ≫ (Spec (CommRingCat.of R)).residue p)) := by
    have hbc0 := isPullback_projModelBaseChange
      (R' := ↑((Spec (CommRingCat.of R)).residueField p)) W
    rwa [show CommRingCat.ofHom
        (algebraMap R ↑((Spec (CommRingCat.of R)).residueField p))
      = StructureSheaf.toStalk R p ≫ (Spec (CommRingCat.of R)).residue p from rfl] at hbc0
  refine ⟨W.map (algebraMap R ↑((Spec (CommRingCat.of R)).residueField p)), inferInstance,
    hfib.isoPullback ≪≫ hbc.isoPullback.symm, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [(Iso.inv_comp_eq _).mpr hbc.isoPullback_hom_snd.symm, hfib.isoPullback_hom_snd]
  · rw [← cancel_mono hbc.isoPullback.hom]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hfib.isoPullback_hom_fst, hbc.isoPullback_hom_fst, projModelZero_baseChange,
        show CommRingCat.ofHom
            (algebraMap R ↑((Spec (CommRingCat.of R)).residueField p))
          = StructureSheaf.toStalk R p ≫ (Spec (CommRingCat.of R)).residue p from rfl]
      simp only [sectionFiberPoint, Scheme.Hom.fiberι]
      exact (pullback.lift_fst _ _ _).trans
        (congrArg (· ≫ projModelZero W) (Spec_fromSpecResidueField_eq R p))
    · simp only [Category.assoc]
      rw [hfib.isoPullback_hom_snd, hbc.isoPullback_hom_snd]
      simp only [sectionFiberPoint, Scheme.Hom.fiberToSpecResidueField,
        projModelZero_projModelπ]
      exact pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- **(T-A8-4)** The definition of record implies the abstract fibre condition: a locally
Weierstrass family is fibrewise elliptic. The fibre at `s` is the fibre of the local model
at the corresponding point of `Spec Γ(S, U)` (two pastes of cartesian squares; the residue
fields agree since the chart inclusion is an open immersion through an isomorphism), and
model fibres are elliptic by `fibrewiseElliptic_projModel`. -/
theorem LocallyWeierstrass.fibrewiseElliptic {E S : Scheme.{u}} {π : E ⟶ S} {z : S ⟶ E}
    {hz : z ≫ π = 𝟙 S} (h : LocallyWeierstrass π z hz) :
    FibrewiseElliptic π z hz := by
  intro s
  obtain ⟨U, hsU, W, hell, e, heπ, hez⟩ := h s
  haveI := hell
  -- the local model as a cartesian square over `S`
  have hsq : IsPullback (e.inv ≫ pullback.fst π U.1.ι) (projModelπ W) π
      (U.2.isoSpec.inv ≫ U.1.ι) := by
    refine (IsPullback.of_hasPullback π U.1.ι).of_iso e (Iso.refl _) U.2.isoSpec
      (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
    · exact heπ.symm
    · simp
    · simp
  -- the corresponding point of the chart
  set q : ↥(Spec (CommRingCat.of Γ(S, U.1))) := U.2.isoSpec.hom.base ⟨s, hsU⟩ with hqdef
  have hq : (U.2.isoSpec.inv ≫ U.1.ι).base q = s := by
    rw [hqdef, ← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
    simp
  haveI : IsOpenImmersion (U.2.isoSpec.inv ≫ U.1.ι) := inferInstance
  haveI : IsIso ((U.2.isoSpec.inv ≫ U.1.ι).residueFieldMap q) := inferInstance
  -- the residue transport `Γ(S, U) ⟶ κ(s)` through the chart point
  letI : Algebra ↑Γ(S, U.1) ↑(S.residueField s) :=
    ((StructureSheaf.toStalk ↑Γ(S, U.1) q ≫ (Spec (CommRingCat.of ↑Γ(S, U.1))).residue q)
      ≫ inv ((U.2.isoSpec.inv ≫ U.1.ι).residueFieldMap q)
      ≫ (S.residueFieldCongr hq).hom).hom.toAlgebra
  -- the model of `W` over `κ(s)` is the fibre: paste the base-change square onto the
  -- family square, and identify the resulting bottom with `fromSpecResidueField s`
  have hbc : IsPullback
      (projModelBaseChange (algebraMap ↑Γ(S, U.1) ↑(S.residueField s)) W)
      (projModelπ (W.map (algebraMap ↑Γ(S, U.1) ↑(S.residueField s))))
      (projModelπ W)
      (Spec.map ((StructureSheaf.toStalk ↑Γ(S, U.1) q
          ≫ (Spec (CommRingCat.of ↑Γ(S, U.1))).residue q)
        ≫ inv ((U.2.isoSpec.inv ≫ U.1.ι).residueFieldMap q)
        ≫ (S.residueFieldCongr hq).hom)) := by
    have hbc0 := isPullback_projModelBaseChange (R' := ↑(S.residueField s)) W
    rwa [show CommRingCat.ofHom (algebraMap ↑Γ(S, U.1) ↑(S.residueField s))
      = (StructureSheaf.toStalk ↑Γ(S, U.1) q
          ≫ (Spec (CommRingCat.of ↑Γ(S, U.1))).residue q)
        ≫ inv ((U.2.isoSpec.inv ≫ U.1.ι).residueFieldMap q)
        ≫ (S.residueFieldCongr hq).hom from rfl] at hbc0
  have hbot : Spec.map ((StructureSheaf.toStalk ↑Γ(S, U.1) q
          ≫ (Spec (CommRingCat.of ↑Γ(S, U.1))).residue q)
        ≫ inv ((U.2.isoSpec.inv ≫ U.1.ι).residueFieldMap q)
        ≫ (S.residueFieldCongr hq).hom)
      ≫ (U.2.isoSpec.inv ≫ U.1.ι) = S.fromSpecResidueField s := by
    rw [Spec.map_comp, Category.assoc, ← Spec_fromSpecResidueField_eq,
      ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Spec.map_comp_assoc]
    simp only [IsIso.hom_inv_id_assoc]
    exact Scheme.residueFieldCongr_fromSpecResidueField hq
  -- pasted: the model of `W` over `κ(s)` IS the fibre of `π` at `s`
  have hgrand := hbc.paste_horiz hsq
  rw [hbot] at hgrand
  -- the zero-leg of the base-change square, in the transported spelling
  have hzbc : projModelZero (W.map (algebraMap ↑Γ(S, U.1) ↑(S.residueField s)))
      ≫ projModelBaseChange (algebraMap ↑Γ(S, U.1) ↑(S.residueField s)) W
      = Spec.map ((StructureSheaf.toStalk ↑Γ(S, U.1) q
          ≫ (Spec (CommRingCat.of ↑Γ(S, U.1))).residue q)
        ≫ inv ((U.2.isoSpec.inv ≫ U.1.ι).residueFieldMap q)
        ≫ (S.residueFieldCongr hq).hom) ≫ projModelZero W := by
    have h0 := projModelZero_baseChange (R' := ↑(S.residueField s)) W
    rwa [show CommRingCat.ofHom (algebraMap ↑Γ(S, U.1) ↑(S.residueField s))
      = (StructureSheaf.toStalk ↑Γ(S, U.1) q
          ≫ (Spec (CommRingCat.of ↑Γ(S, U.1))).residue q)
        ≫ inv ((U.2.isoSpec.inv ≫ U.1.ι).residueFieldMap q)
        ≫ (S.residueFieldCongr hq).hom from rfl] at h0
  refine ⟨W.map (algebraMap ↑Γ(S, U.1) ↑(S.residueField s)), inferInstance,
    hgrand.isoPullback.symm, ?_, ?_⟩
  · exact (Iso.inv_comp_eq _).mpr hgrand.isoPullback_hom_snd.symm
  · rw [Iso.symm_hom, Iso.comp_inv_eq]
    apply pullback.hom_ext
    · rw [Category.assoc, hgrand.isoPullback_hom_fst, reassoc_of% hzbc,
        reassoc_of% (show projModelZero W ≫ e.inv
          = U.2.isoSpec.inv ≫ pullback.lift (U.1.ι ≫ z) (𝟙 _)
            (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp]) from
          by rw [← hez, Category.assoc, Iso.hom_inv_id, Category.comp_id])]
      simp only [sectionFiberPoint, pullback.lift_fst]
      rw [← hbot]
      simp only [Category.assoc]
    · rw [Category.assoc, hgrand.isoPullback_hom_snd]
      simp only [sectionFiberPoint, pullback.lift_snd, projModelZero_projModelπ]
      rfl

/-- The **geometric record** of an elliptic curve over the scheme `S`: a smooth proper
relative curve with a section whose fibres are (pointed) genus-1 curves, the latter
expressed via `FibrewiseElliptic`.

This record carries *no group structure*; the working record `EllipticCurve`
(`GroupLaw.lean`) extends it with the (canonically unique) commutative group-scheme
datum. Source: KM 2.1.1; Deligne–Rapoport II.1.1; Loeffler Def 3.3.1. -/
structure EllipticCurveGeom (S : Scheme.{u}) where
  /-- The total space. -/
  E : Scheme.{u}
  /-- The structure morphism. -/
  π : E ⟶ S
  /-- The zero section. -/
  zero : S ⟶ E
  zero_π : zero ≫ π = 𝟙 S
  smooth : SmoothOfRelativeDimension 1 π
  proper : IsProper π
  /-- **The local-model condition** (v2 definition of record, owner-directed + expert-review
  v8): `E` is Zariski-locally on `S` the projective Weierstrass model of an elliptic
  Weierstrass curve. This *implies* the fibrewise genus-1 condition
  (`EllipticCurveGeom.fibrewiseElliptic`, T-A8 step 4); the converse is the deferred Chain-A7
  comparison (`T-W-cmp`, coherent-cohomology stream). `smooth`/`proper` are kept as fields
  (derivable from `localModel` via T-A3 + `projModelπ_isProper`, the deliberate `grp`-pattern). -/
  localModel : LocallyWeierstrass π zero zero_π

namespace EllipticCurveGeom

attribute [instance] EllipticCurveGeom.smooth EllipticCurveGeom.proper

/-- **(T-A8 step 4, closing the derived-fibre-condition gap)** The record's local-model
field implies the abstract fibrewise genus-1 condition: the definition of record is at
least as strong as the sources' class (DR II.1.1 / KM 2.1.1 / Loeffler 3.3.1). The
converse is the deferred coherent-cohomology comparison `T-A7-cmp`/`T-W-cmp`. -/
theorem fibrewiseElliptic {S : Scheme.{u}} (G : EllipticCurveGeom S) :
    FibrewiseElliptic G.π G.zero G.zero_π :=
  G.localModel.fibrewiseElliptic

end EllipticCurveGeom

end ModularCurves

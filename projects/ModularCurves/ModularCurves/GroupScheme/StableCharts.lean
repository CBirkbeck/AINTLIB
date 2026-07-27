/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.GroupScheme.TranslationAction
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Stable opens for the translation action

Construction support for `[CHARTER-HOPF]` Wave C leaf `[HG-C1a]`
(`.mathlib-quality/decomposition-hopf-crux.md`): an open `U ⊆ E` is **stable** under the
translation action of `G` when translating a point of `U` by any `G`-point stays in `U` —
scheme-theoretically, the `actionProj`-preimage of `U` (the locus `{(t,x) | x ∈ U}`) is
contained in the `translationAction`-preimage (the locus `{(t,x) | x + t ∈ U}`). On a
stable open the action restricts (`restrictedAction`), which is the geometric input to
the chart co-action `[HG-C1b]`.

## Main definitions
* `FiniteLocallyFreeSubgroup.IsStableOpen` — the stability predicate.
* `FiniteLocallyFreeSubgroup.restrictedAction` / `restrictedProj` — the two legs of the
  action restricted to a stable open, as morphisms `(pr⁻¹U) ⟶ U`.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} {E : EllipticCurve S}

namespace FiniteLocallyFreeSubgroup

/-- An open `U ⊆ E` is **stable** under translation by `G` when the projection-preimage
`{(t,x) | x ∈ U}` lies inside the action-preimage `{(t,x) | x + t ∈ U}`: translating a
point of `U` by any `G`-point stays in `U`. -/
def IsStableOpen (G : FiniteLocallyFreeSubgroup E) (U : E.E.Opens) : Prop :=
  G.actionProj.left ⁻¹ᵁ U ≤ G.translationAction.left ⁻¹ᵁ U

/-- The whole curve is stable. -/
theorem isStableOpen_top (G : FiniteLocallyFreeSubgroup E) : G.IsStableOpen ⊤ :=
  le_rfl

/-- The translation action restricted to a stable open: `(pr⁻¹U) ⟶ U`. -/
noncomputable def restrictedAction (G : FiniteLocallyFreeSubgroup E) {U : E.E.Opens}
    (hU : G.IsStableOpen U) :
    (G.actionProj.left ⁻¹ᵁ U).toScheme ⟶ U.toScheme :=
  G.translationAction.left.resLE U (G.actionProj.left ⁻¹ᵁ U) hU

/-- The projection restricted to a stable open: `(pr⁻¹U) ⟶ U`. -/
noncomputable def restrictedProj (G : FiniteLocallyFreeSubgroup E) (U : E.E.Opens) :
    (G.actionProj.left ⁻¹ᵁ U).toScheme ⟶ U.toScheme :=
  G.actionProj.left.resLE U (G.actionProj.left ⁻¹ᵁ U) le_rfl

/-- The domain of the restricted action, identified with the fibre product
`(G ×_S E) ×_E U` along the projection (`[HG-C1b]` opener: the first leg of the chart
Künneth chain `pr⁻¹U ≅ (G ×_S E) ×_E U ≅ G ×_S U`). -/
noncomputable def restrictedDomainIso (G : FiniteLocallyFreeSubgroup E) (U : E.E.Opens) :
    (G.actionProj.left ⁻¹ᵁ U).toScheme ≅ pullback G.actionProj.left U.ι :=
  (pullbackRestrictIsoRestrict G.actionProj.left U).symm

/-- **The chart Künneth identification, scheme level** (`[HG-C1b]` leg 2): the domain of
the restricted action is the fibre product `G ×_S U` (with `U` as an `S`-scheme via
`U.ι ≫ E.π`). Composite of `restrictedDomainIso` with the vertical pasting of fibre
products along the projection `G ×_S E → E`. -/
noncomputable def chartPullbackIso (G : FiniteLocallyFreeSubgroup E) (U : E.E.Opens) :
    (G.actionProj.left ⁻¹ᵁ U).toScheme ≅ pullback G.π (U.ι ≫ E.π) :=
  G.restrictedDomainIso U ≪≫ pullbackLeftPullbackSndIso G.π E.π U.ι

/-- **An affine chart patch** for the per-chart Hopf–Galois argument (`[HG-C1b]` leg 3):
an affine open `V` of the base, together with a `G`-stable affine chart `U` of `E` lying
over it. On such a patch the restricted translation action dualizes to a co-action of
`Γ(G|_V)` on `Γ(U)` (the chart co-action), which is the input to the abstract
Hopf–Galois theorem. Existence of covers by such patches is `[HG-C3]`. -/
structure AffineChartPatch (G : FiniteLocallyFreeSubgroup E) where
  /-- The affine base patch. -/
  V : S.Opens
  /-- The base patch is affine. -/
  hV : IsAffineOpen V
  /-- The stable chart. -/
  U : E.E.Opens
  /-- The chart is affine. -/
  hU : IsAffineOpen U
  /-- The chart is stable under translation by `G`. -/
  hstable : G.IsStableOpen U
  /-- The chart lies over the base patch. -/
  hover : U ≤ E.π ⁻¹ᵁ V

namespace AffineChartPatch

variable {G : FiniteLocallyFreeSubgroup E} (P : G.AffineChartPatch)

/-- The base ring of the patch: sections over the affine base patch. -/
noncomputable abbrev baseRing : CommRingCat := Γ(S, P.V)

/-- The chart ring: sections over the stable affine chart. -/
noncomputable abbrev chartRing : CommRingCat := Γ(E.E, P.U)

/-- The group-patch open: the part of `G` lying over the base patch. -/
noncomputable abbrev groupOpen : (G.G).Opens := G.π ⁻¹ᵁ P.V

/-- The Hopf-side ring: sections of `G` over the base patch. -/
noncomputable abbrev groupRing : CommRingCat := Γ(G.G, P.groupOpen)

/-- The chart ring is an algebra over the base ring (restriction along `E.π`). -/
noncomputable instance : Algebra P.baseRing P.chartRing :=
  (E.π.appLE P.V P.U P.hover).hom.toAlgebra

/-- The group ring is an algebra over the base ring (restriction along `G.π`). -/
noncomputable instance : Algebra P.baseRing P.groupRing :=
  (G.π.appLE P.V P.groupOpen le_rfl).hom.toAlgebra

/-- The chart co-action, into the sections of the fibre product (`[HG-C1b]` leg 3, first
half): pull sections of the chart back along the restricted action, then transport to
the fibre product `G ×_S U` along the Künneth identification. The remaining half is the
affine identification `Γ(G ×_S U) ≅ B ⊗ A` over the patch. -/
noncomputable def coactionToPullback :
    P.chartRing ⟶ Γ(pullback G.π (P.U.ι ≫ E.π), ⊤) :=
  P.U.topIso.inv ≫ (G.restrictedAction P.hstable).appTop
    ≫ ((G.chartPullbackIso P.U).inv.appTop)

/-- The chart, as a scheme over the base patch. -/
noncomputable def chartToBase : P.U.toScheme ⟶ P.V.toScheme :=
  E.π.resLE P.V P.U P.hover

@[reassoc]
theorem chartToBase_comp_ι : P.chartToBase ≫ P.V.ι = P.U.ι ≫ E.π :=
  Scheme.Hom.resLE_comp_ι _ _

/-- **The `S`-level fibre product is the `V`-level one** (`[HG-C1b]` leg 3, step 1): the
chart leg factors through the base patch, so the product only sees the part of `G` over
`V`. -/
noncomputable def pullbackToVLevel :
    pullback G.π (P.U.ι ≫ E.π) ≅ pullback (pullback.snd G.π P.V.ι) P.chartToBase :=
  (pullback.congrHom rfl P.chartToBase_comp_ι).symm
    ≪≫ (pullbackLeftPullbackSndIso G.π P.V.ι P.chartToBase).symm

/-- The `V`-level structure map of the group patch. -/
noncomputable def groupToBase : P.groupOpen.toScheme ⟶ P.V.toScheme :=
  G.π ∣_ P.V

/-- **Step 2 of the chart Künneth**: replace the pullback-presented `G`-leg by the group
patch, giving the honest `V`-level fibre product of the two affines. -/
noncomputable def pullbackToPatchLevel :
    pullback (pullback.snd G.π P.V.ι) P.chartToBase
      ≅ pullback P.groupToBase P.chartToBase :=
  asIso (pullback.map (pullback.snd G.π P.V.ι) P.chartToBase P.groupToBase P.chartToBase
    (pullbackRestrictIsoRestrict G.π P.V).hom (𝟙 _) (𝟙 _)
    (by
      rw [Category.comp_id]
      exact (pullbackRestrictIsoRestrict_hom_morphismRestrict G.π P.V).symm)
    (by rw [Category.comp_id, Category.id_comp]))

/-- The combined identification: the `S`-level fibre product against the chart is the
patch-level product of the two affine pieces. -/
noncomputable def chartKunnethSchemeIso :
    pullback G.π (P.U.ι ≫ E.π) ≅ pullback P.groupToBase P.chartToBase :=
  P.pullbackToVLevel ≪≫ P.pullbackToPatchLevel

/-- The group patch is affine: `G` is finite (hence affine) over `S` and the base patch
is affine. -/
theorem isAffineOpen_groupOpen : IsAffineOpen P.groupOpen := by
  haveI : IsFinite G.π := G.finite
  exact P.hV.preimage G.π

/-- On an affine open, `toSpecΓ` is the `isoSpec` isomorphism. -/
private theorem isIso_toSpecΓ_of_isAffineOpen {X : Scheme.{u}} {W : X.Opens}
    (hW : IsAffineOpen W) : IsIso W.toSpecΓ :=
  hW.isoSpec_hom ▸ inferInstanceAs (IsIso hW.isoSpec.hom)

/-- The three patch pieces are affine, so their `toSpecΓ` maps are isomorphisms. -/
theorem isIso_toSpecΓ_V : IsIso P.V.toSpecΓ := isIso_toSpecΓ_of_isAffineOpen P.hV

theorem isIso_toSpecΓ_U : IsIso P.U.toSpecΓ := isIso_toSpecΓ_of_isAffineOpen P.hU

theorem isIso_toSpecΓ_groupOpen : IsIso P.groupOpen.toSpecΓ :=
  isIso_toSpecΓ_of_isAffineOpen P.isAffineOpen_groupOpen

/-- **Step 4a of the chart Künneth**: write the patch-level fibre product with
`Spec`-legs, via the `toSpecΓ` isomorphisms and the `appLE`-naturality squares. -/
noncomputable def kunnethToSpec :
    pullback P.groupToBase P.chartToBase
      ≅ pullback (Spec.map (G.π.appLE P.V P.groupOpen le_rfl))
          (Spec.map (E.π.appLE P.V P.U P.hover)) := by
  haveI := P.isIso_toSpecΓ_V
  haveI := P.isIso_toSpecΓ_U
  haveI := P.isIso_toSpecΓ_groupOpen
  exact asIso (pullback.map P.groupToBase P.chartToBase _ _
    P.groupOpen.toSpecΓ P.U.toSpecΓ P.V.toSpecΓ
    (by
      rw [show P.groupToBase = G.π.resLE P.V P.groupOpen le_rfl from
        (Scheme.Hom.resLE_eq_morphismRestrict (f := G.π) (U := P.V)).symm]
      exact (Scheme.Opens.toSpecΓ_SpecMap_appLE G.π P.V P.groupOpen le_rfl).symm)
    (by
      exact (Scheme.Opens.toSpecΓ_SpecMap_appLE E.π P.V P.U P.hover).symm))

/-- **Step 4b of the chart Künneth**: the patch-level fibre product is the `Spec` of the
tensor product of the patch rings (the legs align with `pullbackSpecIso`'s by `rfl`:
the algebra structures were *defined* as the `appLE` maps). -/
noncomputable def kunnethSpecIso :
    pullback P.groupToBase P.chartToBase
      ≅ Spec (.of (P.groupRing ⊗[P.baseRing] P.chartRing)) :=
  P.kunnethToSpec ≪≫ pullbackSpecIso P.baseRing P.groupRing P.chartRing

/-- The full scheme-level identification, assembled. -/
noncomputable def chartSpecIso :
    pullback G.π (P.U.ι ≫ E.π) ≅ Spec (.of (P.groupRing ⊗[P.baseRing] P.chartRing)) :=
  P.chartKunnethSchemeIso ≪≫ P.kunnethSpecIso

/-- **The chart co-action, ring level**: chart sections pulled back along the restricted
translation action, landing in the tensor product of the patch rings (`A ⊗[R] B`,
group-factor first; the comodule-convention swap to `B ⊗[R] A` happens in the
`StableAffineChartData` assembly `[HG-C1d]`). -/
noncomputable def coactionRing :
    P.chartRing ⟶ CommRingCat.of (P.groupRing ⊗[P.baseRing] P.chartRing) :=
  P.coactionToPullback ≫ P.chartSpecIso.inv.appTop
    ≫ (Scheme.ΓSpecIso (.of (P.groupRing ⊗[P.baseRing] P.chartRing))).hom

/-- The restricted-action domain lies over the base patch. -/
theorem prOpen_le_preimage :
    G.actionProj.left ⁻¹ᵁ P.U ≤ ((Over.mk G.π ⊗ E.asOver).hom) ⁻¹ᵁ P.V := by
  rw [show (Over.mk G.π ⊗ E.asOver).hom = G.actionProj.left ≫ E.π from
    (G.actionProj_left_π).symm, Scheme.Hom.comp_preimage]
  exact Scheme.Hom.preimage_mono _ P.hover

/-- The restricted-action domain, as a scheme over the base patch. -/
noncomputable def prOpenToBase :
    (G.actionProj.left ⁻¹ᵁ P.U).toScheme ⟶ P.V.toScheme :=
  ((Over.mk G.π ⊗ E.asOver).hom).resLE P.V (G.actionProj.left ⁻¹ᵁ P.U)
    P.prOpen_le_preimage

/-- Both legs of the action restrict to the *same* morphism over the base patch: each is
`resLE` of a morphism lying over `S` (`translationAction_left_π` / `actionProj_left_π`), so
`resLE_comp_resLE` collapses it against `chartToBase` to `prOpenToBase`. -/
private theorem resLE_comp_chartToBase (f : ((Over.mk G.π) ⊗ E.asOver).left ⟶ E.E)
    (hf : f ≫ E.π = ((Over.mk G.π) ⊗ E.asOver).hom)
    (e : G.actionProj.left ⁻¹ᵁ P.U ≤ f ⁻¹ᵁ P.U) :
    f.resLE P.U (G.actionProj.left ⁻¹ᵁ P.U) e ≫ P.chartToBase = P.prOpenToBase := by
  rw [chartToBase]
  refine (Scheme.Hom.resLE_comp_resLE (f := f)
    (U := P.U) (V := G.actionProj.left ⁻¹ᵁ P.U) (e := e) E.π (W := P.V) P.hover).trans ?_
  simp only [hf, prOpenToBase]

/-- **The restricted action is a morphism over the base patch** (`[HG-C1c]` piece (i)):
the source of the R-linearity square. -/
theorem restrictedAction_comp_chartToBase :
    G.restrictedAction P.hstable ≫ P.chartToBase = P.prOpenToBase :=
  P.resLE_comp_chartToBase _ (G.translationAction_left_π) P.hstable

/-- The restricted projection is likewise over the base patch. -/
theorem restrictedProj_comp_chartToBase :
    G.restrictedProj P.U ≫ P.chartToBase = P.prOpenToBase :=
  P.resLE_comp_chartToBase _ (G.actionProj_left_π) le_rfl

/-- The chart co-action as a single scheme morphism `Spec (A ⊗[R] B) ⟶ U` (the
`Spec`-side composite of the whole Künneth chain with the restricted action). Its
`appTop`, conjugated by the section isos, is `coactionRing`. -/
noncomputable def chartCoactionSpec :
    (Spec (.of (P.groupRing ⊗[P.baseRing] P.chartRing)) : Scheme) ⟶ P.U.toScheme :=
  P.chartSpecIso.inv ≫ (G.chartPullbackIso P.U).inv ≫ G.restrictedAction P.hstable

/-- `coactionRing` is the `appTop` of the single scheme morphism, in the section isos. -/
theorem coactionRing_eq_appTop :
    P.coactionRing = P.U.topIso.inv ≫ P.chartCoactionSpec.appTop
      ≫ (Scheme.ΓSpecIso (.of (P.groupRing ⊗[P.baseRing] P.chartRing))).hom := by
  rw [coactionRing, coactionToPullback, chartCoactionSpec]
  simp only [Scheme.Hom.comp_appTop, Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- **(L2)**: the Künneth identification carries the patch structure map to the
second-projection-side structure map — compared after the mono `V.ι`, where everything
is `pullback.condition` algebra. -/
theorem chartPullbackIso_inv_comp_prOpenToBase :
    (G.chartPullbackIso P.U).inv ≫ P.prOpenToBase
      = pullback.snd G.π (P.U.ι ≫ E.π) ≫ P.chartToBase := by
  rw [← cancel_mono P.V.ι]
  have h1 : (G.restrictedDomainIso P.U).inv ≫ (G.actionProj.left ⁻¹ᵁ P.U).ι
      = pullback.fst G.actionProj.left P.U.ι :=
    pullbackRestrictIsoRestrict_hom_ι _ _
  have h2 : pullback.fst G.actionProj.left P.U.ι ≫ (Over.mk G.π ⊗ E.asOver).hom
      = pullback.snd G.actionProj.left P.U.ι ≫ P.U.ι ≫ E.π := by
    rw [show (Over.mk G.π ⊗ E.asOver).hom = G.actionProj.left ≫ E.π from
      (G.actionProj_left_π).symm, ← Category.assoc, pullback.condition]
    exact Category.assoc _ _ _
  have h3 : (pullbackLeftPullbackSndIso G.π E.π P.U.ι).inv
        ≫ pullback.snd G.actionProj.left P.U.ι
      = pullback.snd G.π (P.U.ι ≫ E.π) :=
    pullbackLeftPullbackSndIso_inv_snd_snd _ _ _
  rw [Category.assoc, Category.assoc, P.chartToBase_comp_ι,
    show P.prOpenToBase ≫ P.V.ι
      = (G.actionProj.left ⁻¹ᵁ P.U).ι ≫ (Over.mk G.π ⊗ E.asOver).hom from
    Scheme.Hom.resLE_comp_ι _ _,
    chartPullbackIso, Iso.trans_inv, Category.assoc,
    reassoc_of% h1, h2]
  exact (reassoc_of% h3) (P.U.ι ≫ E.π)

/-- **(L3)**: the full Spec-writing carries the second projection's patch structure to
the canonical algebra map of the tensor product. -/
theorem chartSpecIso_hom_base :
    P.chartSpecIso.hom
        ≫ Spec.map (CommRingCat.ofHom
          (algebraMap P.baseRing (P.groupRing ⊗[P.baseRing] P.chartRing)))
      = pullback.snd G.π (P.U.ι ≫ E.π) ≫ P.chartToBase ≫ P.V.toSpecΓ := by
  haveI := P.isIso_toSpecΓ_V
  haveI := P.isIso_toSpecΓ_U
  haveI := P.isIso_toSpecΓ_groupOpen
  -- the Spec-level base compat, through the fst-side
  have hbase : (pullbackSpecIso P.baseRing P.groupRing P.chartRing).hom
        ≫ Spec.map (CommRingCat.ofHom
          (algebraMap P.baseRing (P.groupRing ⊗[P.baseRing] P.chartRing)))
      = pullback.fst (Spec.map (G.π.appLE P.V P.groupOpen le_rfl))
          (Spec.map (E.π.appLE P.V P.U P.hover))
        ≫ Spec.map (G.π.appLE P.V P.groupOpen le_rfl) :=
    pullbackSpecIso_hom_base _ _ _
  -- kunnethToSpec carries fst to the group-side toSpecΓ
  have hkfst : P.kunnethToSpec.hom ≫ pullback.fst _ _
      = pullback.fst P.groupToBase P.chartToBase ≫ P.groupOpen.toSpecΓ := by
    rw [kunnethToSpec]
    exact pullback.lift_fst _ _ _
  -- the appLE naturality on the group side
  have hg : P.groupOpen.toSpecΓ ≫ Spec.map (G.π.appLE P.V P.groupOpen le_rfl)
      = G.π.resLE P.V P.groupOpen le_rfl ≫ P.V.toSpecΓ :=
    Scheme.Opens.toSpecΓ_SpecMap_appLE G.π P.V P.groupOpen le_rfl
  -- the patch-level condition swaps to the chart side
  have hcond : pullback.fst P.groupToBase P.chartToBase ≫ P.groupToBase
      = pullback.snd P.groupToBase P.chartToBase ≫ P.chartToBase :=
    pullback.condition
  -- the Künneth chain carries snd to snd
  have hsnd : P.chartKunnethSchemeIso.hom ≫ pullback.snd P.groupToBase P.chartToBase
      = pullback.snd G.π (P.U.ι ≫ E.π) := by
    rw [chartKunnethSchemeIso, Iso.trans_hom, Category.assoc]
    rw [show P.pullbackToPatchLevel.hom ≫ pullback.snd P.groupToBase P.chartToBase
        = pullback.snd (pullback.snd G.π P.V.ι) P.chartToBase from by
      rw [pullbackToPatchLevel]
      refine (pullback.lift_snd _ _ _).trans ?_
      exact Category.comp_id _]
    rw [pullbackToVLevel, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, Category.assoc]
    rw [pullbackLeftPullbackSndIso_inv_snd_snd]
    rw [show (pullback.congrHom rfl P.chartToBase_comp_ι).inv
          ≫ pullback.snd G.π (P.chartToBase ≫ P.V.ι)
        = pullback.snd G.π (P.U.ι ≫ E.π) from by
      rw [pullback.congrHom_inv]
      refine (pullback.lift_snd _ _ _).trans ?_
      exact Category.comp_id _]
  -- assemble
  rw [chartSpecIso, Iso.trans_hom, Category.assoc, kunnethSpecIso, Iso.trans_hom,
    Category.assoc, hbase, reassoc_of% hkfst, hg]
  rw [show G.π.resLE P.V P.groupOpen le_rfl = P.groupToBase from
    Scheme.Hom.resLE_eq_morphismRestrict (f := G.π) (U := P.V)]
  rw [reassoc_of% hcond, reassoc_of% hsnd]

/-- **The chart co-action is a morphism over the base patch** (`[HG-C1c-ii]` over-lemma):
the Spec-side co-action composed with the patch structure is the canonical algebra map.
This is the scheme-level content of the `R`-linearity of `coactionRing`. -/
theorem chartCoactionSpec_over :
    P.chartCoactionSpec ≫ P.chartToBase ≫ P.V.toSpecΓ
      = Spec.map (CommRingCat.ofHom
          (algebraMap P.baseRing (P.groupRing ⊗[P.baseRing] P.chartRing))) := by
  rw [chartCoactionSpec, Category.assoc, Category.assoc,
    ← Category.assoc (G.restrictedAction P.hstable),
    P.restrictedAction_comp_chartToBase,
    ← Category.assoc ((G.chartPullbackIso P.U).inv),
    P.chartPullbackIso_inv_comp_prOpenToBase,
    Category.assoc, ← P.chartSpecIso_hom_base, Iso.inv_hom_id_assoc]

/-- **`R`-linearity of the chart co-action** (`[HG-C1c-ii]` Γ-level): the co-action ring
map commutes with the base-patch algebra structures — the `appTop` of the over-lemma,
unwound through the section isomorphisms. -/
theorem appLE_comp_coactionRing :
    E.π.appLE P.V P.U P.hover ≫ P.coactionRing
      = CommRingCat.ofHom
          (algebraMap P.baseRing (P.groupRing ⊗[P.baseRing] P.chartRing)) := by
  -- the appTop of the over-lemma
  have hover := congrArg
    (fun f : (Spec (.of (P.groupRing ⊗[P.baseRing] P.chartRing)) : Scheme)
        ⟶ (Spec Γ(S, P.V) : Scheme) => Scheme.Hom.appTop f)
    P.chartCoactionSpec_over
  simp only [Scheme.Hom.comp_appTop] at hover
  -- unfold toSpecΓ.appTop on the left of hover
  rw [show P.V.toSpecΓ.appTop
      = (Scheme.ΓSpecIso Γ(S, P.V)).hom ≫ P.V.topIso.inv from
    Scheme.Opens.toSpecΓ_appTop P.V] at hover
  -- pre-compose the inverse iso to isolate
  have hover2 : P.V.topIso.inv ≫ P.chartToBase.appTop ≫ P.chartCoactionSpec.appTop
      = (Scheme.ΓSpecIso Γ(S, P.V)).inv
        ≫ (Spec.map (CommRingCat.ofHom
            (algebraMap P.baseRing (P.groupRing ⊗[P.baseRing] P.chartRing)))).appTop := by
    rw [← hover]
    simp only [← Category.assoc, Iso.inv_hom_id]
    simp only [Category.assoc, Category.id_comp]
  -- the resLE appTop is the appLE, in the section isos
  have hres : P.chartToBase.appTop
      = P.V.topIso.hom ≫ E.π.appLE P.V P.U P.hover ≫ P.U.topIso.inv :=
    Scheme.Hom.resLE_app_top (f := E.π) (U := P.V) (V := P.U) P.hover
  -- assemble
  rw [P.coactionRing_eq_appTop, ← Category.assoc, ← Category.assoc]
  rw [show E.π.appLE P.V P.U P.hover ≫ P.U.topIso.inv
      = P.V.topIso.inv ≫ P.chartToBase.appTop from by
    rw [hres, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]]
  rw [Category.assoc, Category.assoc, reassoc_of% hover2,
    Scheme.ΓSpecIso_naturality]
  rw [show (Scheme.ΓSpecIso (CommRingCat.of P.baseRing)).hom
      = (Scheme.ΓSpecIso Γ(S, P.V)).hom from rfl]
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- **The chart co-action as an `R`-algebra map** into `A ⊗[R] B` (group factor first). -/
noncomputable def coactionAlgLeft :
    P.chartRing →ₐ[P.baseRing] (P.groupRing ⊗[P.baseRing] P.chartRing) where
  toRingHom := P.coactionRing.hom
  commutes' := fun r => by
    have h := congrArg (fun f : P.baseRing ⟶ _ => f.hom r) P.appLE_comp_coactionRing
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    exact h

/-- **The chart co-action in comodule convention** `ρ_U : B →ₐ[R] B ⊗[R] A`: swap the two
tensor factors of `coactionAlgLeft`. This is the map fed to `IsCoaction` and, through it,
to the Hopf–Galois theorem. -/
noncomputable def chartCoaction :
    P.chartRing →ₐ[P.baseRing] (P.chartRing ⊗[P.baseRing] P.groupRing) :=
  (Algebra.TensorProduct.comm P.baseRing P.groupRing P.chartRing).toAlgHom.comp
    P.coactionAlgLeft

end AffineChartPatch

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves

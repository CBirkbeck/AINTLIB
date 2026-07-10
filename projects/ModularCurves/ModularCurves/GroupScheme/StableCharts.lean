import ModularCurves.GroupScheme.TranslationAction

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

end AffineChartPatch

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves

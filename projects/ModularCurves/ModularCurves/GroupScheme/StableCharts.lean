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

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves

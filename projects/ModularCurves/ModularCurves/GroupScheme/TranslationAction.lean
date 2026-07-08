import ModularCurves.GroupScheme.Subgroup

/-!
# The translation action of a finite locally free subgroup scheme

**Construction support for `T-G3d-infra`** (`GroupScheme/SubgroupQuotient.lean`). The quotient
`E/G` is the coequalizer of the two maps `G ×_S E ⇉ E` — the translation action `(t, x) ↦ x + t`
and the projection `(t, x) ↦ x`. This file builds those two maps in `Over S` (where the group
multiplication `μ[E.asOver]` and the over-`S` compatibility live), as the foundation of the
construction (Piece 2 of `.mathlib-quality/decomposition-g3d-infra.md`: the translation co-action
`ρ : O_E → O_E ⊗ O_G` is the structure-sheaf dual of `translationAction`).

Working in `Over S` keeps the two maps morphisms of the cartesian-monoidal group object `E.asOver`,
so their over-`S` compatibility (`… ≫ E.π = pr ≫ E.π`) is `Over.w`, free.

## Main definitions
* `FiniteLocallyFreeSubgroup.translationAction` — `G ×_S E ⟶ E`, `(t, x) ↦ x + ι t`, as an
  `Over S`-morphism `(Over.mk G.π) ⊗ E.asOver ⟶ E.asOver`.
* `FiniteLocallyFreeSubgroup.actionProj` — the projection `G ×_S E ⟶ E`, `(t, x) ↦ x`.

## Main results
* `translationAction_left_π` / `actionProj_left_π` — both are morphisms over `S` (free from `Over`).
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} {E : EllipticCurve S}

namespace FiniteLocallyFreeSubgroup

/-- The closed immersion `ι : G ⟶ E` as a morphism over `S` (`G.ι ≫ E.π = G.π` definitionally). -/
noncomputable def ιOver (G : FiniteLocallyFreeSubgroup E) : Over.mk G.π ⟶ E.asOver :=
  Over.homMk G.ι rfl

@[simp]
theorem ιOver_left (G : FiniteLocallyFreeSubgroup E) : G.ιOver.left = G.ι := rfl

/-- **The translation action `G ×_S E ⟶ E`, `(t, x) ↦ x + ι t`**, as an `Over S`-morphism: include
`G` into `E` on the first factor, then apply the group multiplication `μ[E.asOver]`. The quotient
`E/G` is the coequalizer of this with `actionProj`; the structure-sheaf dual of its underlying map
is the translation co-action `ρ` cutting out the co-invariants (Piece 2). -/
noncomputable def translationAction (G : FiniteLocallyFreeSubgroup E) :
    (Over.mk G.π) ⊗ E.asOver ⟶ E.asOver :=
  (G.ιOver ⊗ₘ 𝟙 E.asOver) ≫ μ[E.asOver]

/-- The other coequalizer leg: the projection `G ×_S E ⟶ E`, `(t, x) ↦ x`. -/
noncomputable def actionProj (G : FiniteLocallyFreeSubgroup E) :
    (Over.mk G.π) ⊗ E.asOver ⟶ E.asOver :=
  snd (Over.mk G.π) E.asOver

/-- The translation action is a morphism over `S`: `act ≫ E.π = (G ×_S E ⟶ S)`. Free from `Over`. -/
@[reassoc]
theorem translationAction_left_π (G : FiniteLocallyFreeSubgroup E) :
    G.translationAction.left ≫ E.π = ((Over.mk G.π) ⊗ E.asOver).hom :=
  Over.w G.translationAction

/-- The projection leg is a morphism over `S`. Free from `Over`. -/
@[reassoc]
theorem actionProj_left_π (G : FiniteLocallyFreeSubgroup E) :
    G.actionProj.left ≫ E.π = ((Over.mk G.π) ⊗ E.asOver).hom :=
  Over.w G.actionProj

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves

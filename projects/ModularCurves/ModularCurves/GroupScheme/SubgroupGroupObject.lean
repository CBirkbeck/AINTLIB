/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.GroupScheme.TranslationAction
import ModularCurves.GroupScheme.DeligneOrder

/-!
# The group-scheme structure on a finite locally free subgroup

Construction support for `[CHARTER-HOPF]` Wave C, leaf `[HG-C1c-0]`
(`.mathlib-quality/decomposition-hopf-crux.md`): `FiniteLocallyFreeSubgroup` carries its
subgroup condition only in *functor-of-points* form (`pointSubgroup`), with no
multiplication, unit or inverse morphism as data. This file extracts them.

Each structure map is obtained by feeding the relevant *universal* point into the
`pointSubgroup` closure property and choosing the factoring morphism through the closed
immersion `ι`; since `ι` is a monomorphism, the choice is unique, and every group law
transports from `E.Point`'s `AddCommGroup` by cancelling `ι`.

## Main definitions
* `FiniteLocallyFreeSubgroup.unitHom` — the unit section `S ⟶ G`.
* `FiniteLocallyFreeSubgroup.invHom` — inversion `G ⟶ G`.
* `FiniteLocallyFreeSubgroup.mulHom` — multiplication `G ×_S G ⟶ G`.

## Main results
* the defining specifications `unitHom_ι`, `invHom_ι`, `mulHom_ι`, each characterising the
  map by its composite with `ι` (unique by `cancel_mono`).
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} {E : EllipticCurve S}

namespace FiniteLocallyFreeSubgroup

variable (G : FiniteLocallyFreeSubgroup E)

/-- The unit section `S ⟶ G`: the zero point of `E` over `𝟙 S` factors through `G`. -/
noncomputable def unitHom : S ⟶ G.G :=
  ((G.pointSubgroup (𝟙 S)).zero_mem).choose

@[reassoc (attr := simp)]
theorem unitHom_ι : G.unitHom ≫ G.ι = E.zero := by
  have h := ((G.pointSubgroup (𝟙 S)).zero_mem).choose_spec
  rw [unitHom, h, E.point_zero_val (𝟙 S), Category.id_comp]

/-- The unit section is a section of the structure morphism. -/
@[reassoc (attr := simp)]
theorem unitHom_π : G.unitHom ≫ G.π = 𝟙 S := by
  rw [← G.ι_π, ← Category.assoc, G.unitHom_ι, E.zero_π]

/-- The universal `G`-point of `E`: `ι` itself, over the structure morphism. -/
def universalPoint : E.Point G.π := ⟨G.ι, rfl⟩

theorem universalPoint_mem : G.universalPoint ∈ G.pointSubgroup G.π :=
  ⟨𝟙 G.G, Category.id_comp _⟩

/-- Inversion `G ⟶ G`: the negative of the universal point factors through `G`. -/
noncomputable def invHom : G.G ⟶ G.G :=
  ((G.pointSubgroup G.π).neg_mem G.universalPoint_mem).choose

@[reassoc (attr := simp)]
theorem invHom_ι : G.invHom ≫ G.ι = ((-G.universalPoint : E.Point G.π) : G.G ⟶ E.E) :=
  ((G.pointSubgroup G.π).neg_mem G.universalPoint_mem).choose_spec

/-- The two universal `G`-points of the square `G ×_S G`, as `E`-points over the
structure morphism of the square. -/
noncomputable def sqFstPoint : E.Point ((Over.mk G.π ⊗ Over.mk G.π).hom) :=
  (E.pointEquivOverHom _).symm (fst (Over.mk G.π) (Over.mk G.π) ≫ G.ιOver)

noncomputable def sqSndPoint : E.Point ((Over.mk G.π ⊗ Over.mk G.π).hom) :=
  (E.pointEquivOverHom _).symm (snd (Over.mk G.π) (Over.mk G.π) ≫ G.ιOver)

theorem sqFstPoint_mem :
    G.sqFstPoint ∈ G.pointSubgroup ((Over.mk G.π ⊗ Over.mk G.π).hom) :=
  ⟨(fst (Over.mk G.π) (Over.mk G.π)).left, rfl⟩

theorem sqSndPoint_mem :
    G.sqSndPoint ∈ G.pointSubgroup ((Over.mk G.π ⊗ Over.mk G.π).hom) :=
  ⟨(snd (Over.mk G.π) (Over.mk G.π)).left, rfl⟩

/-- Multiplication `G ×_S G ⟶ G`: the sum of the two universal points factors through
`G`. -/
noncomputable def mulHom : (Over.mk G.π ⊗ Over.mk G.π).left ⟶ G.G :=
  ((G.pointSubgroup _).add_mem G.sqFstPoint_mem G.sqSndPoint_mem).choose

@[reassoc (attr := simp)]
theorem mulHom_ι : G.mulHom ≫ G.ι
    = ((G.sqFstPoint + G.sqSndPoint : E.Point _) : _ ⟶ E.E) :=
  ((G.pointSubgroup _).add_mem G.sqFstPoint_mem G.sqSndPoint_mem).choose_spec

/-! ### The structure maps in `Over S`, and the `ι`-cancellation principle -/

/-- Multiplication is a morphism over `S`. -/
@[reassoc (attr := simp)]
theorem mulHom_π : G.mulHom ≫ G.π = (Over.mk G.π ⊗ Over.mk G.π).hom := by
  have h : G.mulHom ≫ G.ι ≫ E.π = (Over.mk G.π ⊗ Over.mk G.π).hom := by
    rw [← Category.assoc, G.mulHom_ι]
    exact (G.sqFstPoint + G.sqSndPoint : E.Point _).2
  exact h

/-- Inversion is a morphism over `S`. -/
@[reassoc (attr := simp)]
theorem invHom_π : G.invHom ≫ G.π = G.π := by
  have h : G.invHom ≫ G.ι ≫ E.π = G.π := by
    rw [← Category.assoc, G.invHom_ι]
    exact (-G.universalPoint : E.Point G.π).2
  exact h

/-- Multiplication, as an `Over S`-morphism `G ⊗ G ⟶ G`. -/
noncomputable def mulOver : (Over.mk G.π ⊗ Over.mk G.π) ⟶ Over.mk G.π :=
  Over.homMk G.mulHom G.mulHom_π

/-- The unit, as an `Over S`-morphism `𝟙_ ⟶ G`. -/
noncomputable def unitOver : (𝟙_ (Over S)) ⟶ Over.mk G.π :=
  Over.homMk G.unitHom G.unitHom_π

/-- Inversion, as an `Over S`-morphism `G ⟶ G`. -/
noncomputable def invOver : Over.mk G.π ⟶ Over.mk G.π :=
  Over.homMk G.invHom G.invHom_π

/-- **The `ι`-cancellation principle**: two `Over S`-morphisms into `G` agree as soon as
their `ι`-images do (`ι` is a closed immersion, hence a monomorphism). -/
theorem over_hom_ext {X : Over S} {f g : X ⟶ Over.mk G.π}
    (h : f ≫ G.ιOver = g ≫ G.ιOver) : f = g :=
  (cancel_mono G.ιOver).mp h

/-- **The hom-group form of multiplication**: `ι ∘ μ = (pr₁ ∘ ι) · (pr₂ ∘ ι)` in the
pointwise group of `Over S`-morphisms into the group object `E.asOver`. This is the shape
in which the group-object laws are checked. -/
theorem mulOver_comp_ιOver :
    G.mulOver ≫ G.ιOver
      = (fst (Over.mk G.π) (Over.mk G.π) ≫ G.ιOver)
        * (snd (Over.mk G.π) (Over.mk G.π) ≫ G.ιOver) := by
  refine Over.OverMorphism.ext ?_
  show G.mulHom ≫ G.ι = _
  rw [G.mulHom_ι]
  rfl

/-- The hom-group form of the unit. -/
theorem unitOver_comp_ιOver :
    G.unitOver ≫ G.ιOver = 1 := by
  refine Over.OverMorphism.ext ?_
  show G.unitHom ≫ G.ι = _
  have h1 : ((1 : (𝟙_ (Over S)) ⟶ E.asOver)).left = E.zero := by
    have h3 : ((1 : (𝟙_ (Over S)) ⟶ E.asOver)).left
        = ((0 : E.Point (𝟙 S)) : S ⟶ E.E) := rfl
    rw [h3, E.point_zero_val (𝟙 S), Category.id_comp]
  rw [G.unitHom_ι, h1]

/-- The hom-group form of inversion. -/
theorem invOver_comp_ιOver :
    G.invOver ≫ G.ιOver = (G.ιOver)⁻¹ := by
  refine Over.OverMorphism.ext ?_
  show G.invHom ≫ G.ι = _
  rw [G.invHom_ι]
  rfl

/-! ### The group-object laws, by `ι`-cancellation

The pointwise `CommGroup` on homs into `E.asOver` is the scoped instance
`MonObj.Hom.commGroup`, active here through the `MonObj` namespace. -/

/-- The general precomposition form of `mulOver_comp_ιOver`. -/
theorem comp_mulOver_comp_ιOver {X : Over S} (h : X ⟶ Over.mk G.π ⊗ Over.mk G.π) :
    h ≫ G.mulOver ≫ G.ιOver
      = (h ≫ fst (Over.mk G.π) (Over.mk G.π) ≫ G.ιOver)
        * (h ≫ snd (Over.mk G.π) (Over.mk G.π) ≫ G.ιOver) := by
  rw [G.mulOver_comp_ιOver, MonObj.comp_mul]

/-- **Associativity**: `μ ∘ (𝟙 ⊗ μ) ∘ α = μ ∘ (μ ⊗ 𝟙)`. -/
theorem mulOver_assoc :
    (α_ (Over.mk G.π) (Over.mk G.π) (Over.mk G.π)).hom
        ≫ (𝟙 (Over.mk G.π) ⊗ₘ G.mulOver) ≫ G.mulOver
      = (G.mulOver ⊗ₘ 𝟙 (Over.mk G.π)) ≫ G.mulOver := by
  refine G.over_hom_ext ?_
  simp only [Category.assoc, G.comp_mulOver_comp_ιOver, MonObj.comp_mul,
    tensorHom_fst_assoc, tensorHom_snd_assoc, associator_hom_fst_assoc,
    associator_hom_snd_fst_assoc, associator_hom_snd_snd_assoc, Category.id_comp]
  rw [_root_.mul_assoc]

/-- **Left unit law**: `μ ∘ (e ⊗ 𝟙) = λ`. -/
theorem unitOver_mulOver_left :
    (G.unitOver ⊗ₘ 𝟙 (Over.mk G.π)) ≫ G.mulOver = (λ_ (Over.mk G.π)).hom := by
  refine G.over_hom_ext ?_
  rw [Category.assoc, G.comp_mulOver_comp_ιOver]
  simp only [tensorHom_fst_assoc, tensorHom_snd_assoc, Category.id_comp,
    G.unitOver_comp_ιOver, MonObj.comp_one, _root_.one_mul, leftUnitor_hom]

/-- **Commutativity**: `μ ∘ β = μ`. -/
theorem mulOver_comm :
    (β_ (Over.mk G.π) (Over.mk G.π)).hom ≫ G.mulOver = G.mulOver := by
  refine G.over_hom_ext ?_
  rw [Category.assoc, G.comp_mulOver_comp_ιOver, G.mulOver_comp_ιOver]
  simp only [← Category.assoc, braiding_hom_fst, braiding_hom_snd]
  rw [_root_.mul_comm]

/-- **Right unit law**: `μ ∘ (𝟙 ⊗ e) = ρ`. -/
theorem unitOver_mulOver_right :
    (𝟙 (Over.mk G.π) ⊗ₘ G.unitOver) ≫ G.mulOver = (ρ_ (Over.mk G.π)).hom := by
  refine G.over_hom_ext ?_
  rw [Category.assoc, G.comp_mulOver_comp_ιOver]
  simp only [tensorHom_fst_assoc, tensorHom_snd_assoc, Category.id_comp,
    G.unitOver_comp_ιOver, MonObj.comp_one, _root_.mul_one, rightUnitor_hom]

/-- **Left inverse law**: `μ ∘ ⟨S, 𝟙⟩ = e ∘ !`. -/
theorem invOver_mulOver_left :
    lift G.invOver (𝟙 (Over.mk G.π)) ≫ G.mulOver
      = toUnit (Over.mk G.π) ≫ G.unitOver := by
  refine G.over_hom_ext ?_
  rw [Category.assoc, G.comp_mulOver_comp_ιOver]
  simp only [lift_fst_assoc, lift_snd_assoc, Category.id_comp,
    G.invOver_comp_ιOver, _root_.inv_mul_cancel, Category.assoc,
    G.unitOver_comp_ιOver, MonObj.comp_one]

/-- **Right inverse law**: `μ ∘ ⟨𝟙, S⟩ = e ∘ !`. -/
theorem invOver_mulOver_right :
    lift (𝟙 (Over.mk G.π)) G.invOver ≫ G.mulOver
      = toUnit (Over.mk G.π) ≫ G.unitOver := by
  refine G.over_hom_ext ?_
  rw [Category.assoc, G.comp_mulOver_comp_ιOver]
  simp only [lift_fst_assoc, lift_snd_assoc, Category.id_comp,
    G.invOver_comp_ιOver, _root_.mul_inv_cancel, Category.assoc,
    G.unitOver_comp_ιOver, MonObj.comp_one]

/-! ### The action diagrams

The translation action `act = (ι ⊗ 𝟙) ≫ μ[E]` of `G` on `E` satisfies the two axioms of a
group-object action. Both are hom-group computations against `translationAction_eq_mul`,
using that `ι` carries `μ_G` and `e_G` to the group law of `E` (`mulOver_comp_ιOver`,
`unitOver_comp_ιOver`). They are the scheme-level sources of the two `IsCoaction` axioms
for the chart co-action `[HG-C1c]`. -/

/-- **The action-unit axiom**: acting by the unit section is the identity,
`act ∘ (e ⊗ 𝟙) = λ`. -/
theorem translationAction_unit :
    (G.unitOver ⊗ₘ 𝟙 E.asOver) ≫ G.translationAction = (λ_ E.asOver).hom := by
  rw [G.translationAction_eq_mul, MonObj.comp_mul]
  simp only [tensorHom_fst_assoc, tensorHom_snd, Category.id_comp, Category.comp_id,
    G.unitOver_comp_ιOver, MonObj.comp_one, _root_.one_mul, leftUnitor_hom]

/-- **The action-associativity axiom**: `act ∘ (μ ⊗ 𝟙) = act ∘ (𝟙 ⊗ act) ∘ α`. -/
theorem translationAction_assoc :
    (α_ (Over.mk G.π) (Over.mk G.π) E.asOver).hom
        ≫ (𝟙 (Over.mk G.π) ⊗ₘ G.translationAction) ≫ G.translationAction
      = (G.mulOver ⊗ₘ 𝟙 E.asOver) ≫ G.translationAction := by
  simp only [G.translationAction_eq_mul, MonObj.comp_mul, G.mulOver_comp_ιOver,
    tensorHom_fst_assoc, tensorHom_snd_assoc, tensorHom_snd, tensorHom_fst,
    associator_hom_fst_assoc, associator_hom_snd_fst_assoc, associator_hom_snd_snd_assoc,
    associator_hom_snd_snd, Category.id_comp, Category.comp_id, Category.assoc]
  rw [_root_.mul_assoc]

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves

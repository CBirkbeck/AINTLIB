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

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves

import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Finite products of proper schemes over a base

This file packages the finite product in `Over S` of a family of schemes proper over `S`.
-/

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.FiniteProperProduct

noncomputable section

variable {S : Scheme.{u}} {ι : Type u} [Finite ι]
variable {Z : ι → Scheme.{u}} (p : ∀ i, Z i ⟶ S)

/-- The finite product over `S` of the family of structure maps `p`. -/
abbrev obj : Scheme.{u} :=
  (∏ᶜ fun i ↦ Over.mk (p i)).left

/-- The structure map from the finite product to `S`. -/
abbrev π : obj p ⟶ S :=
  (∏ᶜ fun i ↦ Over.mk (p i)).hom

/-- The projection from the finite product to its `i`-th factor. -/
abbrev proj (i : ι) : obj p ⟶ Z i :=
  (Pi.π (fun i ↦ Over.mk (p i)) i).left

@[reassoc]
lemma proj_comp (i : ι) : proj p i ≫ p i = π p :=
  (Pi.π (fun i ↦ Over.mk (p i)) i).w

/-- The universal map to the finite product from a compatible family of maps over `S`. -/
def lift {T : Scheme.{u}} (q : T ⟶ S) (f : ∀ i, T ⟶ Z i)
    (hf : ∀ i, f i ≫ p i = q) : T ⟶ obj p :=
  (Pi.lift (f := fun i ↦ Over.mk (p i)) (P := Over.mk q) fun i ↦
    Over.homMk (U := Over.mk q) (V := Over.mk (p i)) (f i) (hf i)).left

@[reassoc]
lemma lift_proj {T : Scheme.{u}} (q : T ⟶ S) (f : ∀ i, T ⟶ Z i)
    (hf : ∀ i, f i ≫ p i = q) (i : ι) : lift p q f hf ≫ proj p i = f i := by
  have h := Pi.lift_π (f := fun i ↦ Over.mk (p i)) (P := Over.mk q)
    (fun i ↦ Over.homMk (U := Over.mk q) (V := Over.mk (p i)) (f i) (hf i)) i
  exact congrArg Over.Hom.left h

@[reassoc]
lemma lift_comp {T : Scheme.{u}} (q : T ⟶ S) (f : ∀ i, T ⟶ Z i)
    (hf : ∀ i, f i ≫ p i = q) : lift p q f hf ≫ π p = q :=
  (Pi.lift (f := fun i ↦ Over.mk (p i)) (P := Over.mk q) fun i ↦
    Over.homMk (U := Over.mk q) (V := Over.mk (p i)) (f i) (hf i)).w

/-- A map to a nonempty finite product is an immersion if all its coordinates are
immersions. -/
lemma lift_isImmersion [Nonempty ι] {T : Scheme.{u}} (q : T ⟶ S)
    (f : ∀ i, T ⟶ Z i) (hf : ∀ i, f i ≫ p i = q)
    (hfi : ∀ i, IsImmersion (f i)) : IsImmersion (lift p q f hf) := by
  let i : ι := Classical.choice (inferInstance : Nonempty ι)
  have hcomp : IsImmersion (lift p q f hf ≫ proj p i) :=
    (lift_proj p q f hf i).symm ▸ hfi i
  letI : IsImmersion (lift p q f hf ≫ proj p i) := hcomp
  exact IsImmersion.of_comp (lift p q f hf) (proj p i)

private lemma properOverObj_isClosedUnderBinaryProducts :
    (MorphismProperty.overObj
      (@IsProper : MorphismProperty Scheme.{u}) (X := S)).IsClosedUnderBinaryProducts := by
  constructor
  rintro Y ⟨d⟩
  let d' := d.toLimitPresentation.changeDiag (diagramIsoPair d.diag).symm
  let c : BinaryFan (d.diag.obj ⟨WalkingPair.left⟩)
      (d.diag.obj ⟨WalkingPair.right⟩) := d'.cone
  have hc : IsLimit c := d'.isLimit
  have hpb := Over.isPullback_of_binaryFan_isLimit c hc
  have hleft := d.prop_diag_obj ⟨WalkingPair.left⟩
  have hright := d.prop_diag_obj ⟨WalkingPair.right⟩
  change IsProper (d.diag.obj ⟨WalkingPair.left⟩).hom at hleft
  change IsProper (d.diag.obj ⟨WalkingPair.right⟩).hom at hright
  have hfst : IsProper c.fst.left :=
    MorphismProperty.of_isPullback hpb.flip hright
  change IsProper c.pt.hom
  have hw : c.fst.left ≫ (d.diag.obj ⟨WalkingPair.left⟩).hom = c.pt.hom := by
    simpa using c.fst.w
  rw [← hw]
  exact MorphismProperty.comp_mem (@IsProper : MorphismProperty Scheme.{u}) _ _ hfst hleft

/-- A finite product over `S` of proper morphisms is proper over `S`. -/
lemma π_isProper (hp : ∀ i, IsProper (p i)) : IsProper (π p) := by
  let hmul : MorphismProperty.IsMultiplicative
      (@IsProper : MorphismProperty Scheme.{u}) := inferInstance
  letI : MorphismProperty.ContainsIdentities
      (@IsProper : MorphismProperty Scheme.{u}) := hmul.toContainsIdentities
  letI : (MorphismProperty.overObj
      (@IsProper : MorphismProperty Scheme.{u}) (X := S)).IsClosedUnderLimitsOfShape
      (Discrete PEmpty.{1}) :=
    Over.closedUnderLimitsOfShape_discrete_empty
      (@IsProper : MorphismProperty Scheme.{u})
  letI := properOverObj_isClosedUnderBinaryProducts (S := S)
  letI : (MorphismProperty.overObj
      (@IsProper : MorphismProperty Scheme.{u}) (X := S)).IsClosedUnderFiniteProducts :=
    ObjectProperty.IsClosedUnderFiniteProducts.mk'
  exact ObjectProperty.prop_product
    (MorphismProperty.overObj (@IsProper : MorphismProperty Scheme.{u}) (X := S)) hp

/-- Every projection from a finite product of proper schemes over `S` is proper. -/
lemma proj_isProper (hp : ∀ i, IsProper (p i)) (i : ι) : IsProper (proj p i) := by
  letI : IsProper (p i) := hp i
  have hπ : IsProper (π p) := π_isProper p hp
  have hcomp : IsProper (proj p i ≫ p i) := (proj_comp p i).symm ▸ hπ
  letI : IsProper (proj p i ≫ p i) := hcomp
  exact IsProper.of_comp (proj p i) (p i)

end

end AlgebraicGeometry.Scheme.FiniteProperProduct

import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.FinCategory.Basic
import ModularCurves.ForMathlib.FinitePresentationDescent

/-!
# Spreading finite functors of finitely presented algebras

This file assembles the object, map, and relation spreading results from
`FinitePresentationDescent` into an actual functor over one stage of a filtered algebra
system. The finite category supplies exactly the finite families of objects, arrows,
identities, and composable pairs which must be synchronized.
-/

open CategoryTheory

universe u

namespace Algebra

section SpreadFunctor

variable {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
  {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
  {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
  {A : Type u} [CommRing A] [Algebra R A] {u : ∀ i, 𝒮 i →ₐ[R] A}

/-- Assemble stage algebras and stage maps satisfying the functor laws into a functor to
commutative algebras over the stage base. -/
noncomputable def SpreadData.stageFunctor
    {J : Type u} [SmallCategory J]
    (B : J → Type u) [∀ X, CommRing (B X)] [∀ X, Algebra A (B X)]
    (D : ∀ X, SpreadData 𝒮 u (B X))
    {i : ι} (h : ∀ X, (D X).i₀ ≤ i)
    (map : ∀ {X Y : J}, (X ⟶ Y) →
      (D X).spreadStage (t := t) (h X) →ₐ[𝒮 i]
        (D Y).spreadStage (t := t) (h Y))
    (map_id : ∀ X,
      map (𝟙 X) = AlgHom.id (𝒮 i) ((D X).spreadStage (t := t) (h X)))
    (map_comp : ∀ {X Y Z : J} (f : X ⟶ Y) (g : Y ⟶ Z),
      map (f ≫ g) = (map g).comp (map f)) :
    J ⥤ CommAlgCat (𝒮 i) where
  obj X := CommAlgCat.of (𝒮 i) ((D X).spreadStage (t := t) (h X))
  map f := CommAlgCat.ofHom (map f)
  map_id X := by
    apply CommAlgCat.hom_ext
    simpa using map_id X
  map_comp f g := by
    apply CommAlgCat.hom_ext
    simpa using map_comp f g

/-- A realization over one stage of a functor of algebras over the filtered colimit.
The object presentations, literal functor laws, and compatibility of every map with the
colimit are retained as data for later geometric spreading arguments. -/
structure SpreadData.FunctorModel
    {J : Type u} [SmallCategory J] (F : J ⥤ CommAlgCat.{u} A)
    (H : IsFilteredAlgColimit R 𝒮 t A u) where
  stage : ι
  object : ∀ X, SpreadData 𝒮 u (F.obj X)
  le_stage : ∀ X, (object X).i₀ ≤ stage
  map : ∀ {X Y : J}, (X ⟶ Y) →
    (object X).spreadStage (t := t) (le_stage X) →ₐ[𝒮 stage]
      (object Y).spreadStage (t := t) (le_stage Y)
  map_id : ∀ X,
    map (𝟙 X) = AlgHom.id (𝒮 stage)
      ((object X).spreadStage (t := t) (le_stage X))
  map_comp : ∀ {X Y Z : J} (f : X ⟶ Y) (g : Y ⟶ Z),
    map (f ≫ g) = (map g).comp (map f)
  map_colimit : ∀ {X Y : J} (f : X ⟶ Y) x,
    (object Y).stageToColimit H ⟨stage, le_stage Y⟩ (map f x) =
      (F.map f).hom ((object X).stageToColimit H ⟨stage, le_stage X⟩ x)

/-- The categorical finite-stage diagram underlying a `FunctorModel`. -/
noncomputable def SpreadData.FunctorModel.toFunctor
    {J : Type u} [SmallCategory J] {F : J ⥤ CommAlgCat.{u} A}
    {H : IsFilteredAlgColimit R 𝒮 t A u}
    (M : SpreadData.FunctorModel F H) : J ⥤ CommAlgCat (𝒮 M.stage) :=
  SpreadData.stageFunctor (fun X => F.obj X) M.object M.le_stage M.map M.map_id M.map_comp

@[simp]
theorem SpreadData.FunctorModel.toFunctor_obj
    {J : Type u} [SmallCategory J] {F : J ⥤ CommAlgCat.{u} A}
    {H : IsFilteredAlgColimit R 𝒮 t A u}
    (M : SpreadData.FunctorModel F H) (X : J) :
    M.toFunctor.obj X = CommAlgCat.of (𝒮 M.stage)
      ((M.object X).spreadStage (t := t) (M.le_stage X)) := rfl

@[simp]
theorem SpreadData.FunctorModel.toFunctor_map_hom
    {J : Type u} [SmallCategory J] {F : J ⥤ CommAlgCat.{u} A}
    {H : IsFilteredAlgColimit R 𝒮 t A u}
    (M : SpreadData.FunctorModel F H) {X Y : J} (f : X ⟶ Y) :
    (M.toFunctor.map f).hom = M.map f := rfl

/-- Every object of the stage functor remains finitely presented over the stage base. -/
theorem SpreadData.FunctorModel.toFunctor_obj_finitePresentation
    {J : Type u} [SmallCategory J] {F : J ⥤ CommAlgCat.{u} A}
    {H : IsFilteredAlgColimit R 𝒮 t A u}
    (M : SpreadData.FunctorModel F H) (X : J) :
    FinitePresentation (𝒮 M.stage) (M.toFunctor.obj X) :=
  (M.object X).spreadStage_finitePresentation (t := t) (M.le_stage X)

/-- A map in the stage functor commutes with the corresponding map in the colimit
functor. -/
theorem SpreadData.FunctorModel.toFunctor_map_colimit
    {J : Type u} [SmallCategory J] {F : J ⥤ CommAlgCat.{u} A}
    {H : IsFilteredAlgColimit R 𝒮 t A u}
    (M : SpreadData.FunctorModel F H) {X Y : J} (f : X ⟶ Y) x :
    (M.object Y).stageToColimit H ⟨M.stage, M.le_stage Y⟩
        ((M.toFunctor.map f).hom x) =
      (F.map f).hom ((M.object X).stageToColimit H ⟨M.stage, M.le_stage X⟩ x) :=
  M.map_colimit f x

/-- Base change of each object of the stage functor to the colimit recovers the
corresponding object of the original functor. -/
theorem SpreadData.FunctorModel.toFunctor_obj_baseChange
    {J : Type u} [SmallCategory J] {F : J ⥤ CommAlgCat.{u} A}
    {H : IsFilteredAlgColimit R 𝒮 t A u}
    (M : SpreadData.FunctorModel F H) (X : J) :
    letI : Algebra (𝒮 M.stage) A := (u M.stage).toRingHom.toAlgebra
    Nonempty ((TensorProduct (𝒮 M.stage) A
      ((M.object X).spreadStage (t := t) (M.le_stage X))) ≃ₐ[A] F.obj X) :=
  (M.object X).baseChange_colim (t := t) (M.le_stage X) H

private abbrev FunctorArrow (J : Type u) [SmallCategory J] :=
  Σ p : J × J, p.1 ⟶ p.2

private abbrev FunctorComposition (J : Type u) [SmallCategory J] :=
  Σ p : J × (J × J), (p.1 ⟶ p.2.1) × (p.2.1 ⟶ p.2.2)

private abbrev FunctorRelation (J : Type u) [SmallCategory J] :=
  J ⊕ FunctorComposition J

private def FunctorRelation.src
    {J : Type u} [SmallCategory J] : FunctorRelation J → J
  | Sum.inl X => X
  | Sum.inr c => c.1.1

private def FunctorRelation.dst
    {J : Type u} [SmallCategory J] : FunctorRelation J → J
  | Sum.inl X => X
  | Sum.inr c => c.1.2.2

private noncomputable def SpreadData.functorRelationLeft
    {J : Type u} [SmallCategory J]
    (B : J → Type u) [∀ X, CommRing (B X)] [∀ X, Algebra A (B X)]
    (D : ∀ X, SpreadData 𝒮 u (B X)) {i : ι} (h : ∀ X, (D X).i₀ ≤ i)
    (map : ∀ a : FunctorArrow J,
      (D a.1.1).spreadStage (t := t) (h a.1.1) →ₐ[𝒮 i]
        (D a.1.2).spreadStage (t := t) (h a.1.2)) :
    ∀ r : FunctorRelation J,
      (D r.src).spreadStage (t := t) (h r.src) →ₐ[𝒮 i]
        (D r.dst).spreadStage (t := t) (h r.dst)
  | Sum.inl X => map ⟨(X, X), 𝟙 X⟩
  | Sum.inr c => map ⟨(c.1.1, c.1.2.2), c.2.1 ≫ c.2.2⟩

private noncomputable def SpreadData.functorRelationRight
    {J : Type u} [SmallCategory J]
    (B : J → Type u) [∀ X, CommRing (B X)] [∀ X, Algebra A (B X)]
    (D : ∀ X, SpreadData 𝒮 u (B X)) {i : ι} (h : ∀ X, (D X).i₀ ≤ i)
    (map : ∀ a : FunctorArrow J,
      (D a.1.1).spreadStage (t := t) (h a.1.1) →ₐ[𝒮 i]
        (D a.1.2).spreadStage (t := t) (h a.1.2)) :
    ∀ r : FunctorRelation J,
      (D r.src).spreadStage (t := t) (h r.src) →ₐ[𝒮 i]
        (D r.dst).spreadStage (t := t) (h r.dst)
  | Sum.inl X => AlgHom.id (𝒮 i) ((D X).spreadStage (t := t) (h X))
  | Sum.inr c =>
      (map ⟨(c.1.2.1, c.1.2.2), c.2.2⟩).comp
        (map ⟨(c.1.1, c.1.2.1), c.2.1⟩)

private theorem SpreadData.functorRelation_colimit_eq
    {J : Type u} [SmallCategory J]
    (F : J ⥤ CommAlgCat.{u} A)
    (D : ∀ X, SpreadData 𝒮 u (F.obj X)) (H : IsFilteredAlgColimit R 𝒮 t A u)
    {i : ι} (h : ∀ X, (D X).i₀ ≤ i)
    (map : ∀ a : FunctorArrow J,
      (D a.1.1).spreadStage (t := t) (h a.1.1) →ₐ[𝒮 i]
        (D a.1.2).spreadStage (t := t) (h a.1.2))
    (map_colimit : ∀ (a : FunctorArrow J) x,
      (D a.1.2).stageToColimit H ⟨i, h a.1.2⟩ (map a x) =
        (F.map a.2).hom ((D a.1.1).stageToColimit H ⟨i, h a.1.1⟩ x))
    (r : FunctorRelation J) x :
    (D r.dst).stageToColimit H ⟨i, h r.dst⟩
        (SpreadData.functorRelationLeft (fun X => F.obj X) D h map r x) =
      (D r.dst).stageToColimit H ⟨i, h r.dst⟩
        (SpreadData.functorRelationRight (fun X => F.obj X) D h map r x) := by
  revert x
  rcases r with X | c
  · intro x
    change (D X).spreadStage (t := t) (h X) at x
    change (D X).stageToColimit H ⟨i, h X⟩
        (map ⟨(X, X), 𝟙 X⟩ x) =
      (D X).stageToColimit H ⟨i, h X⟩
        (AlgHom.id (𝒮 i) ((D X).spreadStage (t := t) (h X)) x)
    rw [AlgHom.id_apply, map_colimit ⟨(X, X), 𝟙 X⟩ x]
    simp
  · intro x
    change (D c.1.1).spreadStage (t := t) (h c.1.1) at x
    change (D c.1.2.2).stageToColimit H ⟨i, h c.1.2.2⟩
        (map ⟨(c.1.1, c.1.2.2), c.2.1 ≫ c.2.2⟩ x) =
      (D c.1.2.2).stageToColimit H ⟨i, h c.1.2.2⟩
        (((map ⟨(c.1.2.1, c.1.2.2), c.2.2⟩).comp
          (map ⟨(c.1.1, c.1.2.1), c.2.1⟩)) x)
    rw [map_colimit ⟨(c.1.1, c.1.2.2), c.2.1 ≫ c.2.2⟩ x]
    rw [AlgHom.comp_apply]
    rw [map_colimit ⟨(c.1.2.1, c.1.2.2), c.2.2⟩
      (map ⟨(c.1.1, c.1.2.1), c.2.1⟩ x)]
    rw [map_colimit ⟨(c.1.1, c.1.2.1), c.2.1⟩ x]
    exact ConcreteCategory.congr_hom (F.map_comp c.2.1 c.2.2)
      ((D c.1.1).stageToColimit H ⟨i, h c.1.1⟩ x)

/-- A finite functor of finitely presented algebras over a filtered colimit descends to
one common stage, with all functor laws holding literally there and all maps compatible
with the original functor after passage to the colimit. -/
theorem IsFilteredAlgColimit.exists_spreadFunctor
    (H : IsFilteredAlgColimit R 𝒮 t A u)
    {J : Type u} [SmallCategory J] [FinCategory J]
    (F : J ⥤ CommAlgCat.{u} A) [∀ X, FinitePresentation A (F.obj X)] :
    Nonempty (SpreadData.FunctorModel F H) := by
  classical
  obtain ⟨i₀, D, h₀⟩ := H.exists_common_spreadData (fun X => F.obj X)
  obtain ⟨i, hi, map, map_colimit⟩ := SpreadData.exists_common_maps_at_stage H
    (fun X => F.obj X) D i₀ h₀
    (fun a : FunctorArrow J => a.1.1) (fun a : FunctorArrow J => a.1.2)
    (fun a : FunctorArrow J => (F.map a.2).hom)
  let h : ∀ X, (D X).i₀ ≤ i := fun X => (h₀ X).le.trans hi
  let left := SpreadData.functorRelationLeft (fun X => F.obj X) D h map
  let right := SpreadData.functorRelationRight (fun X => F.obj X) D h map
  have relation_colimit : ∀ (r : FunctorRelation J) x,
      (D r.dst).stageToColimit H ⟨i, h r.dst⟩ (left r x) =
        (D r.dst).stageToColimit H ⟨i, h r.dst⟩ (right r x) :=
    fun r x => SpreadData.functorRelation_colimit_eq F D H h map map_colimit r x
  let C := Classical.choice (SpreadData.exists_common_eq_mapFamilyAtLaterStage
    (fun X => F.obj X) D H h FunctorRelation.src FunctorRelation.dst
    left right relation_colimit)
  refine ⟨⟨C.stage, D, fun X => (h X).trans C.le_stage,
    fun {X Y} f => (D X).mapAtLaterStage (D Y) H (h X) (h Y) C.le_stage
      (map ⟨(X, Y), f⟩), ?_, ?_, ?_⟩⟩
  · intro X
    calc
      (D X).mapAtLaterStage (D X) H (h X) (h X) C.le_stage
          (map ⟨(X, X), 𝟙 X⟩) =
        (D X).mapAtLaterStage (D X) H (h X) (h X) C.le_stage
          (AlgHom.id (𝒮 i) ((D X).spreadStage (t := t) (h X))) :=
            C.maps_agree (Sum.inl X)
      _ = AlgHom.id (𝒮 C.stage)
          ((D X).spreadStage (t := t) ((h X).trans C.le_stage)) :=
        (D X).mapAtLaterStage_id H (h X) C.le_stage
  · intro X Y Z f g
    change (D X).mapAtLaterStage (D Z) H (h X) (h Z) C.le_stage
        (map ⟨(X, Z), f ≫ g⟩) =
      ((D Y).mapAtLaterStage (D Z) H (h Y) (h Z) C.le_stage
        (map ⟨(Y, Z), g⟩)).comp
      ((D X).mapAtLaterStage (D Y) H (h X) (h Y) C.le_stage
        (map ⟨(X, Y), f⟩))
    let r : FunctorRelation J := Sum.inr ⟨(X, (Y, Z)), (f, g)⟩
    calc
      (D X).mapAtLaterStage (D Z) H (h X) (h Z) C.le_stage
          (map ⟨(X, Z), f ≫ g⟩) =
        (D X).mapAtLaterStage (D Z) H (h X) (h Z) C.le_stage
          ((map ⟨(Y, Z), g⟩).comp (map ⟨(X, Y), f⟩)) := C.maps_agree r
      _ = ((D Y).mapAtLaterStage (D Z) H (h Y) (h Z) C.le_stage
          (map ⟨(Y, Z), g⟩)).comp
          ((D X).mapAtLaterStage (D Y) H (h X) (h Y) C.le_stage
            (map ⟨(X, Y), f⟩)) :=
        (D X).mapAtLaterStage_comp (D Y) (D Z) H
          (h X) (h Y) (h Z) C.le_stage (map ⟨(X, Y), f⟩) (map ⟨(Y, Z), g⟩)
  · intro X Y f x
    exact (D X).mapAtLaterStage_colimit (D Y) H (h X) (h Y) C.le_stage
      (map ⟨(X, Y), f⟩) (F.map f).hom (map_colimit ⟨(X, Y), f⟩) x

end SpreadFunctor

end Algebra

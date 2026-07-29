import ModularCurves.ForMathlib.FinitePresentationFunctor
import ModularCurves.ForMathlib.FinitePresentationLocalization

/-!
# Base change of spread functor models

A finite-stage functor model becomes naturally isomorphic to its original functor after
extension of scalars to the filtered colimit. The construction uses the same tensor-product
objects and maps as mathlib's `CommRingCat.tensorProd` functor.
-/

universe u

open CategoryTheory

namespace Algebra

noncomputable section

variable {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
  {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
  {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
  {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, 𝒮 i →ₐ[R] A}
  {J : Type u} [SmallCategory J] {F : J ⥤ CommAlgCat.{u} A}
  {H : IsFilteredAlgColimit R 𝒮 t A uA}

/-- Extend every algebra in a finite-stage functor model to the filtered-colimit base. -/
noncomputable def SpreadData.FunctorModel.baseChangeFunctor
    (M : SpreadData.FunctorModel F H) : J ⥤ CommAlgCat A := by
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  exact
    { obj := fun X => CommAlgCat.of A
        (TensorProduct (𝒮 M.stage) A (M.toFunctor.obj X))
      map := fun f => CommAlgCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id A A) (M.toFunctor.map f).hom)
      map_id := fun X => by
        apply CommAlgCat.hom_ext
        change Algebra.TensorProduct.map (AlgHom.id A A) (M.toFunctor.map (𝟙 X)).hom =
          AlgHom.id A (TensorProduct (𝒮 M.stage) A (M.toFunctor.obj X))
        have hmap : (M.toFunctor.map (𝟙 X)).hom =
            AlgHom.id (𝒮 M.stage) (M.toFunctor.obj X) :=
          congrArg (fun q => q.hom) (M.toFunctor.map_id X)
        rw [hmap]
        exact Algebra.TensorProduct.map_id
      map_comp := fun f g => by
        apply CommAlgCat.hom_ext
        simp only [CommAlgCat.hom_ofHom, CommAlgCat.hom_comp, Functor.map_comp]
        exact Algebra.TensorProduct.map_id_comp _ _ }

@[simp]
theorem SpreadData.FunctorModel.baseChangeFunctor_obj
    (M : SpreadData.FunctorModel F H) (X : J) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    M.baseChangeFunctor.obj X = CommAlgCat.of A
      (TensorProduct (𝒮 M.stage) A
        ((M.object X).spreadStage (t := t) (M.le_stage X))) :=
  rfl

@[simp]
theorem SpreadData.FunctorModel.baseChangeFunctor_map_hom
    (M : SpreadData.FunctorModel F H) {X Y : J} (f : X ⟶ Y) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    (M.baseChangeFunctor.map f).hom =
      Algebra.TensorProduct.map (AlgHom.id A A) (M.toFunctor.map f).hom :=
  rfl

/-- The colimit base-change equivalences commute with every map in the modeled functor. -/
theorem SpreadData.FunctorModel.baseChangeColimEquiv_naturality
    (M : SpreadData.FunctorModel F H) {X Y : J} (f : X ⟶ Y) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    ((M.object Y).baseChangeColimEquiv (M.le_stage Y) H).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id A A) (M.toFunctor.map f).hom) =
      (F.map f).hom.comp
        ((M.object X).baseChangeColimEquiv (M.le_stage X) H).toAlgHom := by
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  change ((M.object Y).baseChangeColimEquiv (M.le_stage Y) H).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id A A) (M.map f)) =
    (F.map f).hom.comp
      ((M.object X).baseChangeColimEquiv (M.le_stage X) H).toAlgHom
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy =>
      rw [map_add, map_add]
      exact congrArg₂ (· + ·) hx hy
  | tmul a x =>
      rw [TensorProduct.tmul_eq_smul_one_tmul]
      simp only [AlgHom.comp_apply, map_smul]
      rw [Algebra.TensorProduct.map_tmul]
      simp only [AlgHom.id_apply]
      apply congrArg (a • ·)
      calc
        (M.object Y).baseChangeColimEquiv (M.le_stage Y) H
              (1 ⊗ₜ[(𝒮 M.stage)] M.map f x) =
            (M.object Y).stageToColimit H ⟨M.stage, M.le_stage Y⟩
              (M.map f x) :=
          (M.object Y).baseChangeColimEquiv_tmul (M.le_stage Y) H _
        _ = (F.map f).hom
              ((M.object X).stageToColimit H ⟨M.stage, M.le_stage X⟩ x) :=
          M.map_colimit f x
        _ = (F.map f).hom
              ((M.object X).baseChangeColimEquiv (M.le_stage X) H
                (1 ⊗ₜ[(𝒮 M.stage)] x)) :=
          congrArg (F.map f).hom
            ((M.object X).baseChangeColimEquiv_tmul (M.le_stage X) H x).symm

/-- Extension of scalars of a finite-stage functor model recovers the original functor. -/
noncomputable def SpreadData.FunctorModel.baseChangeIso
    (M : SpreadData.FunctorModel F H) : M.baseChangeFunctor ≅ F := by
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  refine NatIso.ofComponents (fun X => ?_) ?_
  · change CommAlgCat.of A
      (TensorProduct (𝒮 M.stage) A
        ((M.object X).spreadStage (t := t) (M.le_stage X))) ≅ F.obj X
    exact CommAlgCat.isoMk ((M.object X).baseChangeColimEquiv (M.le_stage X) H)
  intro X Y f
  apply CommAlgCat.hom_ext
  exact M.baseChangeColimEquiv_naturality f

end

end Algebra

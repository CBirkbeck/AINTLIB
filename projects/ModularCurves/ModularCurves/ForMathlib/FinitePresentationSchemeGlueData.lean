import ModularCurves.ForMathlib.FinitePresentationOpenImmersionFamily
import ModularCurves.ForMathlib.FinitePresentationPushoutFamily
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Constructors
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Affine finite-intersection glue data

An augmented functor on finite subsets records the coordinate rings of affine
charts and all their finite intersections.  If the singleton-to-pair maps are
open immersions on spectra and the singleton/pair/triple squares are pushouts,
the functor determines scheme glue data.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.GlueData

noncomputable section

variable {S J : Type u} [CommRing S]

private noncomputable abbrev singletonIndex (i : J) : Finset J := by
  classical
  exact {i}

private noncomputable abbrev pairIndex (i j : J) : Finset J := by
  classical
  exact {i, j}

private noncomputable abbrev tripleIndex (i j k : J) : Finset J := by
  classical
  exact {i, j, k}

private noncomputable def singletonToPair (i j : J) :
    singletonIndex i ⟶ pairIndex i j :=
  homOfLE (by
    classical
    simp [singletonIndex, pairIndex])

private noncomputable def pairToSingletonSelf (i : J) :
    pairIndex i i ⟶ singletonIndex i :=
  homOfLE (by
    classical
    simp [singletonIndex, pairIndex])

private noncomputable def pairToTripleLeft (i j k : J) :
    pairIndex i j ⟶ tripleIndex i j k :=
  homOfLE (by
    classical
    simp [pairIndex, tripleIndex])

private noncomputable def pairToTripleMiddle (i j k : J) :
    pairIndex j k ⟶ tripleIndex i j k :=
  homOfLE (by
    classical
    simp [pairIndex, tripleIndex])

private noncomputable def pairToTripleRight (i j k : J) :
    pairIndex i k ⟶ tripleIndex i j k :=
  homOfLE (by
    classical
    simp [pairIndex, tripleIndex])

private noncomputable def pairSwap (i j : J) : pairIndex j i ⟶ pairIndex i j :=
  homOfLE (by
    classical
    intro x hx
    simpa [pairIndex, or_comm] using hx)

private noncomputable def tripleCycle (i j k : J) :
    tripleIndex j k i ⟶ tripleIndex i j k :=
  homOfLE (by
    classical
    intro x hx
    simp [tripleIndex] at hx ⊢
    tauto)

private noncomputable abbrev ringObj
    (F : Finset J ⥤ CommAlgCat.{u} S) (s : Finset J) : CommRingCat.{u} :=
  CommRingCat.of (F.obj s)

private noncomputable def ringMap
    (F : Finset J ⥤ CommAlgCat.{u} S) {s t : Finset J} (f : s ⟶ t) :
    ringObj F s ⟶ ringObj F t :=
  CommRingCat.ofHom (F.map f).hom

private lemma ringMap_id (F : Finset J ⥤ CommAlgCat.{u} S) (s : Finset J) :
    ringMap F (𝟙 s) = 𝟙 _ := by
  ext x
  exact ConcreteCategory.congr_hom (F.map_id s) x

private lemma ringMap_comp (F : Finset J ⥤ CommAlgCat.{u} S)
    {r s t : Finset J} (f : r ⟶ s) (g : s ⟶ t) :
    ringMap F (f ≫ g) = ringMap F f ≫ ringMap F g := by
  ext x
  exact ConcreteCategory.congr_hom (F.map_comp f g) x

/-- The singleton index used by an affine finite-intersection functor. -/
noncomputable abbrev affineIntersectionSingletonIndex (i : J) : Finset J :=
  singletonIndex i

/-- The pair index used by an affine finite-intersection functor. -/
noncomputable abbrev affineIntersectionPairIndex (i j : J) : Finset J :=
  pairIndex i j

/-- The triple index used by an affine finite-intersection functor. -/
noncomputable abbrev affineIntersectionTripleIndex (i j k : J) : Finset J :=
  tripleIndex i j k

/-- The canonical inclusion from a singleton index to a pair index. -/
noncomputable abbrev affineIntersectionSingletonToPair (i j : J) :
    affineIntersectionSingletonIndex i ⟶ affineIntersectionPairIndex i j :=
  singletonToPair i j

/-- The canonical inclusion from the first pair index to a triple index. -/
noncomputable abbrev affineIntersectionPairToTripleLeft (i j k : J) :
    affineIntersectionPairIndex i j ⟶ affineIntersectionTripleIndex i j k :=
  pairToTripleLeft i j k

/-- The canonical inclusion from the middle pair index to a triple index. -/
noncomputable abbrev affineIntersectionPairToTripleMiddle (i j k : J) :
    affineIntersectionPairIndex j k ⟶ affineIntersectionTripleIndex i j k :=
  pairToTripleMiddle i j k

/-- The canonical inclusion from the outer pair index to a triple index. -/
noncomputable abbrev affineIntersectionPairToTripleRight (i j k : J) :
    affineIntersectionPairIndex i k ⟶ affineIntersectionTripleIndex i j k :=
  pairToTripleRight i j k

/-- The canonical index map interchanging an ordered pair. -/
noncomputable abbrev affineIntersectionPairSwap (i j : J) :
    affineIntersectionPairIndex j i ⟶ affineIntersectionPairIndex i j :=
  pairSwap i j

/-- The canonical inclusion from the second singleton into an ordered pair index. -/
noncomputable def affineIntersectionSingletonToPairRight (i j : J) :
    affineIntersectionSingletonIndex j ⟶ affineIntersectionPairIndex i j :=
  affineIntersectionSingletonToPair j i ≫ affineIntersectionPairSwap i j

/-- The canonical map from the tensor product of two singleton-chart rings to their
pair-intersection ring. -/
noncomputable def affineIntersectionPairMap
    (F : Finset J ⥤ CommAlgCat.{u} S) (i j : J) :
    TensorProduct S
        (F.obj (affineIntersectionSingletonIndex i) : Type u)
        (F.obj (affineIntersectionSingletonIndex j) : Type u) →ₐ[S]
      (F.obj (affineIntersectionPairIndex i j) : Type u) :=
  Algebra.TensorProduct.productMap
    (F.map (affineIntersectionSingletonToPair i j)).hom
    (F.map (affineIntersectionSingletonToPairRight i j)).hom

/-- The affine chart indexed by a singleton in a finite-intersection functor. -/
noncomputable abbrev affineIntersectionChart
    (F : Finset J ⥤ CommAlgCat.{u} S) (i : J) : Scheme :=
  Spec (ringObj F (affineIntersectionSingletonIndex i))

/-- The affine overlap indexed by a pair in a finite-intersection functor. -/
noncomputable abbrev affineIntersectionOverlap
    (F : Finset J ⥤ CommAlgCat.{u} S) (i j : J) : Scheme :=
  Spec (ringObj F (affineIntersectionPairIndex i j))

/-- The overlap leg induced by the singleton-to-pair inclusion. -/
noncomputable def affineIntersectionOverlapι
    (F : Finset J ⥤ CommAlgCat.{u} S) (i j : J) :
    affineIntersectionOverlap F i j ⟶ affineIntersectionChart F i :=
  Spec.map (ringMap F (affineIntersectionSingletonToPair i j))

/-- The singleton-to-pair maps of an affine finite-intersection functor induce open
immersions on spectra. -/
def IsOpenAffineIntersectionFunctor (F : Finset J ⥤ CommAlgCat.{u} S) : Prop :=
  ∀ i j, IsOpenImmersion (affineIntersectionOverlapι F i j)

/-- The singleton/pair/triple squares of an affine finite-intersection functor are
pushouts. -/
def IsPushoutAffineIntersectionFunctor (F : Finset J ⥤ CommAlgCat.{u} S) : Prop :=
  ∀ i j k, IsPushout
    (ringMap F (singletonToPair i j))
    (ringMap F (singletonToPair i k))
    (ringMap F (pairToTripleLeft i j k))
    (ringMap F (pairToTripleRight i j k))

/-- An affine finite-intersection functor has separated pair maps if every canonical map
from the tensor product of two singleton-chart rings onto their pair-intersection ring is
surjective. -/
def IsSeparatedAffineIntersectionFunctor (F : Finset J ⥤ CommAlgCat.{u} S) : Prop :=
  ∀ i j, Function.Surjective (affineIntersectionPairMap F i j)

section Spread

variable {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
  {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
  {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
  [Algebra R S] {uS : ∀ i, 𝒮 i →ₐ[R] S}
  {F : Finset J ⥤ CommAlgCat.{u} S}
  {H : Algebra.IsFilteredAlgColimit R 𝒮 t S uS}

section Separated

open Algebra TensorProduct

private noncomputable def pairTensorBaseChangeEquiv
    {S₀ T C₁ C₂ : Type u}
    [CommRing S₀] [CommRing T] [CommRing C₁] [CommRing C₂]
    [Algebra S₀ T] [Algebra S₀ C₁] [Algebra S₀ C₂] :
    (T ⊗[S₀] (C₁ ⊗[S₀] C₂)) ≃ₐ[T]
      (T ⊗[S₀] C₁) ⊗[T] (T ⊗[S₀] C₂) :=
  (Algebra.TensorProduct.assoc S₀ S₀ T T C₁ C₂).symm.trans
    (Algebra.TensorProduct.cancelBaseChange S₀ T T (T ⊗[S₀] C₁) C₂).symm

private theorem pairTensorBaseChangeEquiv_tmul
    {S₀ T C₁ C₂ : Type u}
    [CommRing S₀] [CommRing T] [CommRing C₁] [CommRing C₂]
    [Algebra S₀ T] [Algebra S₀ C₁] [Algebra S₀ C₂]
    (a : T) (x : C₁) (y : C₂) :
    pairTensorBaseChangeEquiv (S₀ := S₀) (T := T) (C₁ := C₁) (C₂ := C₂)
        (a ⊗ₜ[S₀] (x ⊗ₜ[S₀] y)) =
      (a ⊗ₜ[S₀] x) ⊗ₜ[T] (1 ⊗ₜ[S₀] y) := by
  rw [pairTensorBaseChangeEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.assoc_symm_tmul,
    Algebra.TensorProduct.cancelBaseChange_symm_tmul]

private abbrev separatedStageSingleton
    (M : SpreadData.FunctorModel F H) (i : J) : Type u :=
  (M.object (affineIntersectionSingletonIndex i)).spreadStage
    (t := t) (M.le_stage (affineIntersectionSingletonIndex i))

private abbrev separatedStagePairTensor
    (M : SpreadData.FunctorModel F H) (i j : J) : Type u :=
  TensorProduct (𝒮 M.stage) (separatedStageSingleton M i) (separatedStageSingleton M j)

private abbrev separatedStagePair
    (M : SpreadData.FunctorModel F H) (i j : J) : Type u :=
  (M.object (affineIntersectionPairIndex i j)).spreadStage
    (t := t) (M.le_stage (affineIntersectionPairIndex i j))

private abbrev separatedLaterStageSingleton
    (M : SpreadData.FunctorModel F H) {k : ι} (hik : M.stage ≤ k) (i : J) : Type u :=
  (M.object (affineIntersectionSingletonIndex i)).spreadStage
    (t := t) ((M.le_stage (affineIntersectionSingletonIndex i)).trans hik)

private abbrev separatedLaterStagePairTensor
    (M : SpreadData.FunctorModel F H) {k : ι} (hik : M.stage ≤ k) (i j : J) : Type u :=
  TensorProduct (𝒮 k) (separatedLaterStageSingleton M hik i)
    (separatedLaterStageSingleton M hik j)

private abbrev separatedLaterStagePair
    (M : SpreadData.FunctorModel F H) {k : ι} (hik : M.stage ≤ k) (i j : J) : Type u :=
  (M.object (affineIntersectionPairIndex i j)).spreadStage
    (t := t) ((M.le_stage (affineIntersectionPairIndex i j)).trans hik)

private noncomputable instance separatedScalarExtensionCommRing
    (M : SpreadData.FunctorModel F H) (i j : J)
    [hA : Algebra (𝒮 M.stage) S] :
    CommRing (TensorProduct (𝒮 M.stage) S (separatedStagePairTensor M i j)) :=
  @TensorProduct.instCommRing
    (𝒮 M.stage) S (separatedStagePairTensor M i j)
    (inferInstance) (inferInstance) hA (inferInstance) (inferInstance)

private noncomputable instance separatedScalarExtensionAlgebra
    (M : SpreadData.FunctorModel F H) (i j : J)
    [hA : Algebra (𝒮 M.stage) S] :
    Algebra S (TensorProduct (𝒮 M.stage) S (separatedStagePairTensor M i j)) :=
  @Algebra.TensorProduct.leftAlgebra
    (𝒮 M.stage) S S (separatedStagePairTensor M i j)
    (inferInstance) (inferInstance) hA
    (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance)

private abbrev separatedPairStageScalarExtension
    (M : SpreadData.FunctorModel F H) (k : ι) (i j : J)
    [Algebra (𝒮 M.stage) (𝒮 k)] : Type u :=
  TensorProduct (𝒮 M.stage) (𝒮 k) (separatedStagePairTensor M i j)

private noncomputable instance separatedPairStageScalarExtensionCommRing
    (M : SpreadData.FunctorModel F H) (k : ι) (i j : J)
    [h : Algebra (𝒮 M.stage) (𝒮 k)] :
    CommRing (separatedPairStageScalarExtension M k i j) :=
  @TensorProduct.instCommRing
    (𝒮 M.stage) (𝒮 k) (separatedStagePairTensor M i j)
    (inferInstance) (inferInstance) h (inferInstance) (inferInstance)

private noncomputable instance separatedPairStageScalarExtensionAlgebra
    (M : SpreadData.FunctorModel F H) (k : ι) (i j : J)
    [h : Algebra (𝒮 M.stage) (𝒮 k)] :
    Algebra (𝒮 k) (separatedPairStageScalarExtension M k i j) :=
  @Algebra.TensorProduct.leftAlgebra
    (𝒮 M.stage) (𝒮 k) (𝒮 k) (separatedStagePairTensor M i j)
    (inferInstance) (inferInstance) h
    (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance)

private noncomputable def separatedStagePairMap
    (M : SpreadData.FunctorModel F H) (i j : J) :
    (M.object (affineIntersectionSingletonIndex i)).spreadStage
          (t := t) (M.le_stage (affineIntersectionSingletonIndex i)) ⊗[𝒮 M.stage]
        (M.object (affineIntersectionSingletonIndex j)).spreadStage
          (t := t) (M.le_stage (affineIntersectionSingletonIndex j)) →ₐ[𝒮 M.stage]
      (M.object (affineIntersectionPairIndex i j)).spreadStage
        (t := t) (M.le_stage (affineIntersectionPairIndex i j)) :=
  Algebra.TensorProduct.productMap
    (M.map (affineIntersectionSingletonToPair i j))
    (M.map (affineIntersectionSingletonToPairRight i j))

private noncomputable def separatedPairMapColimitSourceEquiv
    (M : SpreadData.FunctorModel F H) (i j : J) :
    letI : Algebra (𝒮 M.stage) S := (uS M.stage).toRingHom.toAlgebra
    TensorProduct (𝒮 M.stage) S (separatedStagePairTensor M i j) ≃ₐ[S]
      (F.obj (affineIntersectionSingletonIndex i) ⊗[S]
        F.obj (affineIntersectionSingletonIndex j)) := by
  letI : Algebra (𝒮 M.stage) S := (uS M.stage).toRingHom.toAlgebra
  exact (pairTensorBaseChangeEquiv
      (S₀ := 𝒮 M.stage) (T := S)
      (C₁ := separatedStageSingleton M i)
      (C₂ := separatedStageSingleton M j)).trans
    (Algebra.TensorProduct.congr
      ((M.object (affineIntersectionSingletonIndex i)).baseChangeColimEquiv
        (M.le_stage (affineIntersectionSingletonIndex i)) H)
      ((M.object (affineIntersectionSingletonIndex j)).baseChangeColimEquiv
        (M.le_stage (affineIntersectionSingletonIndex j)) H))

private noncomputable def separatedPairMapStageSourceEquiv
    (M : SpreadData.FunctorModel F H) {k : ι} (hik : M.stage ≤ k) (i j : J) :
    letI : Algebra (𝒮 M.stage) (𝒮 k) := (t hik).toRingHom.toAlgebra
    separatedPairStageScalarExtension M k i j ≃ₐ[𝒮 k]
      separatedLaterStagePairTensor M hik i j := by
  letI : Algebra (𝒮 M.stage) (𝒮 k) := (t hik).toRingHom.toAlgebra
  exact (pairTensorBaseChangeEquiv
      (S₀ := 𝒮 M.stage) (T := 𝒮 k)
      (C₁ := separatedStageSingleton M i)
      (C₂ := separatedStageSingleton M j)).trans
    (Algebra.TensorProduct.congr
      ((M.object (affineIntersectionSingletonIndex i)).spreadStageBaseChangeEquiv
        hik (M.le_stage (affineIntersectionSingletonIndex i)) H)
      ((M.object (affineIntersectionSingletonIndex j)).spreadStageBaseChangeEquiv
        hik (M.le_stage (affineIntersectionSingletonIndex j)) H))

private theorem separatedPairMapStageSourceEquiv_tmul
    (M : SpreadData.FunctorModel F H) {k : ι} (hik : M.stage ≤ k) (i j : J)
    (x : separatedStageSingleton M i) (y : separatedStageSingleton M j) :
    letI : Algebra (𝒮 M.stage) (𝒮 k) := (t hik).toRingHom.toAlgebra
    separatedPairMapStageSourceEquiv M hik i j
        (1 ⊗ₜ[𝒮 M.stage] (x ⊗ₜ[𝒮 M.stage] y)) =
      (M.object (affineIntersectionSingletonIndex i)).spreadStageBaseChangeEquiv
          hik (M.le_stage (affineIntersectionSingletonIndex i)) H
          (1 ⊗ₜ[𝒮 M.stage] x) ⊗ₜ[𝒮 k]
        (M.object (affineIntersectionSingletonIndex j)).spreadStageBaseChangeEquiv
          hik (M.le_stage (affineIntersectionSingletonIndex j)) H
          (1 ⊗ₜ[𝒮 M.stage] y) := by
  letI : Algebra (𝒮 M.stage) (𝒮 k) := (t hik).toRingHom.toAlgebra
  rw [separatedPairMapStageSourceEquiv, AlgEquiv.trans_apply,
    pairTensorBaseChangeEquiv_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  rfl

private noncomputable def separatedLaterStagePairMap
    (M : SpreadData.FunctorModel F H) {k : ι} (hik : M.stage ≤ k) (i j : J) :
    separatedLaterStagePairTensor M hik i j →ₐ[𝒮 k] separatedLaterStagePair M hik i j :=
  Algebra.TensorProduct.productMap
    ((M.object (affineIntersectionSingletonIndex i)).mapAtLaterStage
      (M.object (affineIntersectionPairIndex i j)) H
      (M.le_stage (affineIntersectionSingletonIndex i))
      (M.le_stage (affineIntersectionPairIndex i j)) hik
      (M.map (affineIntersectionSingletonToPair i j)))
    ((M.object (affineIntersectionSingletonIndex j)).mapAtLaterStage
      (M.object (affineIntersectionPairIndex i j)) H
      (M.le_stage (affineIntersectionSingletonIndex j))
      (M.le_stage (affineIntersectionPairIndex i j)) hik
      (M.map (affineIntersectionSingletonToPairRight i j)))

private theorem separatedLaterStagePairMap_baseChange_tmul
    (M : SpreadData.FunctorModel F H) {k : ι} (hik : M.stage ≤ k) (i j : J)
    (x : separatedStageSingleton M i) (y : separatedStageSingleton M j) :
    letI : Algebra (𝒮 M.stage) (𝒮 k) := (t hik).toRingHom.toAlgebra
    separatedLaterStagePairMap M hik i j
        (separatedPairMapStageSourceEquiv M hik i j
          (1 ⊗ₜ[𝒮 M.stage] (x ⊗ₜ[𝒮 M.stage] y))) =
      (M.object (affineIntersectionPairIndex i j)).spreadStageBaseChangeEquiv
        hik (M.le_stage (affineIntersectionPairIndex i j)) H
        (Algebra.TensorProduct.map (AlgHom.id (𝒮 k) (𝒮 k))
          (separatedStagePairMap M i j)
          (1 ⊗ₜ[𝒮 M.stage] (x ⊗ₜ[𝒮 M.stage] y))) := by
  letI : Algebra (𝒮 M.stage) (𝒮 k) := (t hik).toRingHom.toAlgebra
  rw [separatedPairMapStageSourceEquiv_tmul,
    (M.object (affineIntersectionSingletonIndex i)).spreadStageBaseChangeEquiv_tmul,
    (M.object (affineIntersectionSingletonIndex j)).spreadStageBaseChangeEquiv_tmul,
    separatedLaterStagePairMap, Algebra.TensorProduct.productMap_apply_tmul,
    (M.object (affineIntersectionSingletonIndex i)).mapAtLaterStage_stageTransition,
    (M.object (affineIntersectionSingletonIndex j)).mapAtLaterStage_stageTransition,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, separatedStagePairMap,
    Algebra.TensorProduct.productMap_apply_tmul,
    (M.object (affineIntersectionPairIndex i j)).spreadStageBaseChangeEquiv_tmul,
    map_mul]

private theorem separatedLaterStagePairMap_baseChange_one_tmul
    (M : SpreadData.FunctorModel F H) {k : ι} (hik : M.stage ≤ k) (i j : J)
    (z : separatedStagePairTensor M i j) :
    letI : Algebra (𝒮 M.stage) (𝒮 k) := (t hik).toRingHom.toAlgebra
    separatedLaterStagePairMap M hik i j
        (separatedPairMapStageSourceEquiv M hik i j
          (1 ⊗ₜ[𝒮 M.stage] z)) =
      (M.object (affineIntersectionPairIndex i j)).spreadStageBaseChangeEquiv
        hik (M.le_stage (affineIntersectionPairIndex i j)) H
        (Algebra.TensorProduct.map (AlgHom.id (𝒮 k) (𝒮 k))
          (separatedStagePairMap M i j) (1 ⊗ₜ[𝒮 M.stage] z)) := by
  letI : Algebra (𝒮 M.stage) (𝒮 k) := (t hik).toRingHom.toAlgebra
  induction z using TensorProduct.induction_on with
  | zero => simp only [tmul_zero, map_zero]
  | add x y hx hy =>
      rw [tmul_add]
      calc
        _ = separatedLaterStagePairMap M hik i j
            (separatedPairMapStageSourceEquiv M hik i j (1 ⊗ₜ[𝒮 M.stage] x) +
              separatedPairMapStageSourceEquiv M hik i j (1 ⊗ₜ[𝒮 M.stage] y)) :=
          congrArg _ ((separatedPairMapStageSourceEquiv M hik i j).map_add _ _)
        _ = separatedLaterStagePairMap M hik i j
                (separatedPairMapStageSourceEquiv M hik i j (1 ⊗ₜ[𝒮 M.stage] x)) +
              separatedLaterStagePairMap M hik i j
                (separatedPairMapStageSourceEquiv M hik i j (1 ⊗ₜ[𝒮 M.stage] y)) :=
          (separatedLaterStagePairMap M hik i j).map_add _ _
        _ = (M.object (affineIntersectionPairIndex i j)).spreadStageBaseChangeEquiv
                hik (M.le_stage (affineIntersectionPairIndex i j)) H
                (Algebra.TensorProduct.map (AlgHom.id (𝒮 k) (𝒮 k))
                  (separatedStagePairMap M i j) (1 ⊗ₜ[𝒮 M.stage] x)) +
              (M.object (affineIntersectionPairIndex i j)).spreadStageBaseChangeEquiv
                hik (M.le_stage (affineIntersectionPairIndex i j)) H
                (Algebra.TensorProduct.map (AlgHom.id (𝒮 k) (𝒮 k))
                  (separatedStagePairMap M i j) (1 ⊗ₜ[𝒮 M.stage] y)) :=
          congrArg₂ (· + ·) hx hy
        _ = (M.object (affineIntersectionPairIndex i j)).spreadStageBaseChangeEquiv
              hik (M.le_stage (affineIntersectionPairIndex i j)) H
              (Algebra.TensorProduct.map (AlgHom.id (𝒮 k) (𝒮 k))
                  (separatedStagePairMap M i j) (1 ⊗ₜ[𝒮 M.stage] x) +
                Algebra.TensorProduct.map (AlgHom.id (𝒮 k) (𝒮 k))
                  (separatedStagePairMap M i j) (1 ⊗ₜ[𝒮 M.stage] y)) :=
          ((M.object (affineIntersectionPairIndex i j)).spreadStageBaseChangeEquiv
            hik (M.le_stage (affineIntersectionPairIndex i j)) H).map_add _ _ |>.symm
        _ = _ := congrArg _
          ((Algebra.TensorProduct.map (AlgHom.id (𝒮 k) (𝒮 k))
            (separatedStagePairMap M i j)).map_add _ _).symm
  | tmul x y => exact separatedLaterStagePairMap_baseChange_tmul M hik i j x y

private theorem separatedLaterStagePairMap_baseChange
    (M : SpreadData.FunctorModel F H) {k : ι} (hik : M.stage ≤ k) (i j : J) :
    letI : Algebra (𝒮 M.stage) (𝒮 k) := (t hik).toRingHom.toAlgebra
    (separatedLaterStagePairMap M hik i j).comp
        (separatedPairMapStageSourceEquiv M hik i j).toAlgHom =
      ((M.object (affineIntersectionPairIndex i j)).spreadStageBaseChangeEquiv
        hik (M.le_stage (affineIntersectionPairIndex i j)) H).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id (𝒮 k) (𝒮 k))
          (separatedStagePairMap M i j)) := by
  letI : Algebra (𝒮 M.stage) (𝒮 k) := (t hik).toRingHom.toAlgebra
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy =>
      let lhs := (separatedLaterStagePairMap M hik i j).comp
        (separatedPairMapStageSourceEquiv M hik i j).toAlgHom
      let rhs :=
        ((M.object (affineIntersectionPairIndex i j)).spreadStageBaseChangeEquiv
          hik (M.le_stage (affineIntersectionPairIndex i j)) H).toAlgHom.comp
          (Algebra.TensorProduct.map (AlgHom.id (𝒮 k) (𝒮 k))
            (separatedStagePairMap M i j))
      change lhs (x + y) = rhs (x + y)
      calc
        lhs (x + y) = lhs x + lhs y := lhs.map_add x y
        _ = rhs x + rhs y := congrArg₂ (· + ·) hx hy
        _ = rhs (x + y) := (rhs.map_add x y).symm
  | tmul a x =>
      rw [TensorProduct.tmul_eq_smul_one_tmul]
      simp only [AlgHom.comp_apply, map_smul]
      exact congrArg (a • ·) (separatedLaterStagePairMap_baseChange_one_tmul M hik i j x)

private theorem separatedLaterStagePairMap_surjective_of_baseChange
    (M : SpreadData.FunctorModel F H) {k : ι} (hik : M.stage ≤ k) (i j : J)
    (hbase :
      letI : Algebra (𝒮 M.stage) (𝒮 k) := (t hik).toRingHom.toAlgebra
      Function.Surjective
        (Algebra.TensorProduct.map (AlgHom.id (𝒮 M.stage) (𝒮 k))
          (separatedStagePairMap M i j))) :
    Function.Surjective (separatedLaterStagePairMap M hik i j) := by
  letI : Algebra (𝒮 M.stage) (𝒮 k) := (t hik).toRingHom.toAlgebra
  let sourceEquiv := separatedPairMapStageSourceEquiv M hik i j
  let targetEquiv :=
    (M.object (affineIntersectionPairIndex i j)).spreadStageBaseChangeEquiv
      hik (M.le_stage (affineIntersectionPairIndex i j)) H
  intro y
  obtain ⟨yBase, hy⟩ := targetEquiv.surjective y
  obtain ⟨zBase, hz⟩ := hbase yBase
  refine ⟨sourceEquiv zBase, ?_⟩
  calc
    separatedLaterStagePairMap M hik i j (sourceEquiv zBase) =
        targetEquiv
          (Algebra.TensorProduct.map (AlgHom.id (𝒮 k) (𝒮 k))
            (separatedStagePairMap M i j) zBase) :=
      AlgHom.congr_fun (separatedLaterStagePairMap_baseChange M hik i j) zBase
    _ = targetEquiv yBase := congrArg targetEquiv hz
    _ = y := hy

private theorem separatedLaterStagePairMap_trans
    (M : SpreadData.FunctorModel F H) {k l : ι}
    (hik : M.stage ≤ k) (hkl : k ≤ l) (i j : J) :
    separatedLaterStagePairMap (M.mapToStage hik) hkl i j =
      separatedLaterStagePairMap M (hik.trans hkl) i j := by
  change Algebra.TensorProduct.productMap
      ((M.object (affineIntersectionSingletonIndex i)).mapAtLaterStage
        (M.object (affineIntersectionPairIndex i j)) H
        ((M.le_stage (affineIntersectionSingletonIndex i)).trans hik)
        ((M.le_stage (affineIntersectionPairIndex i j)).trans hik) hkl
        ((M.object (affineIntersectionSingletonIndex i)).mapAtLaterStage
          (M.object (affineIntersectionPairIndex i j)) H
          (M.le_stage (affineIntersectionSingletonIndex i))
          (M.le_stage (affineIntersectionPairIndex i j)) hik
          (M.map (affineIntersectionSingletonToPair i j))))
      ((M.object (affineIntersectionSingletonIndex j)).mapAtLaterStage
        (M.object (affineIntersectionPairIndex i j)) H
        ((M.le_stage (affineIntersectionSingletonIndex j)).trans hik)
        ((M.le_stage (affineIntersectionPairIndex i j)).trans hik) hkl
        ((M.object (affineIntersectionSingletonIndex j)).mapAtLaterStage
          (M.object (affineIntersectionPairIndex i j)) H
          (M.le_stage (affineIntersectionSingletonIndex j))
          (M.le_stage (affineIntersectionPairIndex i j)) hik
          (M.map (affineIntersectionSingletonToPairRight i j)))) =
    Algebra.TensorProduct.productMap
      ((M.object (affineIntersectionSingletonIndex i)).mapAtLaterStage
        (M.object (affineIntersectionPairIndex i j)) H
        (M.le_stage (affineIntersectionSingletonIndex i))
        (M.le_stage (affineIntersectionPairIndex i j)) (hik.trans hkl)
        (M.map (affineIntersectionSingletonToPair i j)))
      ((M.object (affineIntersectionSingletonIndex j)).mapAtLaterStage
        (M.object (affineIntersectionPairIndex i j)) H
        (M.le_stage (affineIntersectionSingletonIndex j))
        (M.le_stage (affineIntersectionPairIndex i j)) (hik.trans hkl)
        (M.map (affineIntersectionSingletonToPairRight i j)))
  rw [(M.object (affineIntersectionSingletonIndex i)).mapAtLaterStage_trans,
    (M.object (affineIntersectionSingletonIndex j)).mapAtLaterStage_trans]

private theorem separatedLaterStagePairMap_surjective_trans
    (M : SpreadData.FunctorModel F H) {k l : ι}
    (hik : M.stage ≤ k) (hkl : k ≤ l) (i j : J)
    (hk : Function.Surjective (separatedLaterStagePairMap M hik i j)) :
    Function.Surjective (separatedLaterStagePairMap M (hik.trans hkl) i j) := by
  have hkl' : (M.mapToStage hik).stage ≤ l := by
    change k ≤ l
    exact hkl
  have hbase :
      letI : Algebra (𝒮 k) (𝒮 l) := (t hkl).toRingHom.toAlgebra
      Function.Surjective
        (Algebra.TensorProduct.map (AlgHom.id (𝒮 k) (𝒮 l))
          (separatedLaterStagePairMap M hik i j)) := by
    letI hklAlgebra : Algebra (𝒮 k) (𝒮 l) := (t hkl).toRingHom.toAlgebra
    let hkkAlgebra : Algebra (𝒮 k) (𝒮 k) := inferInstance
    let hSourceAlgebra : Algebra (𝒮 k) (separatedLaterStagePairTensor M hik i j) :=
      inferInstance
    let hTargetAlgebra : Algebra (𝒮 k) (separatedLaterStagePair M hik i j) :=
      inferInstance
    let hTower : IsScalarTower (𝒮 k) (𝒮 k) (𝒮 l) :=
      IsScalarTower.of_algebraMap_eq'
        (R := 𝒮 k) (S := 𝒮 k) (A := 𝒮 l) rfl
    exact @Algebra.TensorProduct.map_surjective
      (𝒮 k) (𝒮 k) (inferInstance) (inferInstance) hkkAlgebra
      (𝒮 l) (𝒮 l) (separatedLaterStagePairTensor M hik i j)
      (separatedLaterStagePair M hik i j)
      (inferInstance) (inferInstance) (inferInstance) (inferInstance)
      hklAlgebra hklAlgebra hSourceAlgebra hTargetAlgebra
      hklAlgebra hklAlgebra hTower hTower
      (AlgHom.id (𝒮 k) (𝒮 l)) (separatedLaterStagePairMap M hik i j)
      Function.surjective_id hk
  have hbase' :
      letI : Algebra (𝒮 (M.mapToStage hik).stage) (𝒮 l) :=
        (t hkl').toRingHom.toAlgebra
      Function.Surjective
        (Algebra.TensorProduct.map
          (AlgHom.id (𝒮 (M.mapToStage hik).stage) (𝒮 l))
          (separatedStagePairMap (M.mapToStage hik) i j)) := by
    intro y
    obtain ⟨x, hx⟩ := hbase y
    refine ⟨x, ?_⟩
    exact hx
  have hN := separatedLaterStagePairMap_surjective_of_baseChange
    (M.mapToStage hik) hkl' i j hbase'
  rw [separatedLaterStagePairMap_trans M hik hkl i j] at hN
  exact hN

private theorem separatedPairMapColimitSourceEquiv_tmul
    (M : SpreadData.FunctorModel F H) (i j : J)
    (x : (M.object (affineIntersectionSingletonIndex i)).spreadStage
      (t := t) (M.le_stage (affineIntersectionSingletonIndex i)))
    (y : (M.object (affineIntersectionSingletonIndex j)).spreadStage
      (t := t) (M.le_stage (affineIntersectionSingletonIndex j))) :
    letI : Algebra (𝒮 M.stage) S := (uS M.stage).toRingHom.toAlgebra
    separatedPairMapColimitSourceEquiv M i j
        (1 ⊗ₜ[𝒮 M.stage] (x ⊗ₜ[𝒮 M.stage] y)) =
      (M.object (affineIntersectionSingletonIndex i)).baseChangeColimEquiv
          (M.le_stage (affineIntersectionSingletonIndex i)) H
          (1 ⊗ₜ[𝒮 M.stage] x) ⊗ₜ[S]
        (M.object (affineIntersectionSingletonIndex j)).baseChangeColimEquiv
          (M.le_stage (affineIntersectionSingletonIndex j)) H
          (1 ⊗ₜ[𝒮 M.stage] y) := by
  letI : Algebra (𝒮 M.stage) S := (uS M.stage).toRingHom.toAlgebra
  rw [separatedPairMapColimitSourceEquiv, AlgEquiv.trans_apply,
    pairTensorBaseChangeEquiv_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  rfl

private theorem separatedPairMap_baseChangeColimit_tmul
    (M : SpreadData.FunctorModel F H) (i j : J)
    (x : (M.object (affineIntersectionSingletonIndex i)).spreadStage
      (t := t) (M.le_stage (affineIntersectionSingletonIndex i)))
    (y : (M.object (affineIntersectionSingletonIndex j)).spreadStage
      (t := t) (M.le_stage (affineIntersectionSingletonIndex j))) :
    letI : Algebra (𝒮 M.stage) S := (uS M.stage).toRingHom.toAlgebra
    (M.object (affineIntersectionPairIndex i j)).baseChangeColimEquiv
          (M.le_stage (affineIntersectionPairIndex i j)) H
          (Algebra.TensorProduct.map (AlgHom.id S S)
            (separatedStagePairMap M i j)
            (1 ⊗ₜ[𝒮 M.stage] (x ⊗ₜ[𝒮 M.stage] y))) =
      affineIntersectionPairMap F i j
        (separatedPairMapColimitSourceEquiv M i j
          (1 ⊗ₜ[𝒮 M.stage] (x ⊗ₜ[𝒮 M.stage] y))) := by
  letI : Algebra (𝒮 M.stage) S := (uS M.stage).toRingHom.toAlgebra
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    (M.object (affineIntersectionPairIndex i j)).baseChangeColimEquiv_tmul,
    separatedStagePairMap, Algebra.TensorProduct.productMap_apply_tmul, map_mul,
    M.map_colimit (affineIntersectionSingletonToPair i j) x,
    M.map_colimit (affineIntersectionSingletonToPairRight i j) y,
    separatedPairMapColimitSourceEquiv_tmul,
    (M.object (affineIntersectionSingletonIndex i)).baseChangeColimEquiv_tmul,
    (M.object (affineIntersectionSingletonIndex j)).baseChangeColimEquiv_tmul,
    affineIntersectionPairMap, Algebra.TensorProduct.productMap_apply_tmul]

private theorem separatedPairMap_baseChangeColimit_one_tmul
    (M : SpreadData.FunctorModel F H) (i j : J)
    (z : (M.object (affineIntersectionSingletonIndex i)).spreadStage
          (t := t) (M.le_stage (affineIntersectionSingletonIndex i)) ⊗[𝒮 M.stage]
        (M.object (affineIntersectionSingletonIndex j)).spreadStage
          (t := t) (M.le_stage (affineIntersectionSingletonIndex j))) :
    letI : Algebra (𝒮 M.stage) S := (uS M.stage).toRingHom.toAlgebra
    (M.object (affineIntersectionPairIndex i j)).baseChangeColimEquiv
          (M.le_stage (affineIntersectionPairIndex i j)) H
          (Algebra.TensorProduct.map (AlgHom.id S S)
            (separatedStagePairMap M i j)
            (1 ⊗ₜ[𝒮 M.stage] z)) =
      affineIntersectionPairMap F i j
        (separatedPairMapColimitSourceEquiv M i j
          (1 ⊗ₜ[𝒮 M.stage] z)) := by
  letI : Algebra (𝒮 M.stage) S := (uS M.stage).toRingHom.toAlgebra
  induction z using TensorProduct.induction_on with
  | zero => simp only [tmul_zero, map_zero]
  | add x y hx hy => rw [tmul_add, map_add, map_add, map_add, map_add, hx, hy]
  | tmul x y => exact separatedPairMap_baseChangeColimit_tmul M i j x y

private theorem separatedPairMap_baseChangeColimit
    (M : SpreadData.FunctorModel F H) (i j : J) :
    letI : Algebra (𝒮 M.stage) S := (uS M.stage).toRingHom.toAlgebra
    ((M.object (affineIntersectionPairIndex i j)).baseChangeColimEquiv
        (M.le_stage (affineIntersectionPairIndex i j)) H).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id S S)
          (separatedStagePairMap M i j)) =
      (affineIntersectionPairMap F i j).comp
        (separatedPairMapColimitSourceEquiv M i j).toAlgHom := by
  letI : Algebra (𝒮 M.stage) S := (uS M.stage).toRingHom.toAlgebra
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a x =>
      rw [TensorProduct.tmul_eq_smul_one_tmul]
      simp only [AlgHom.comp_apply, map_smul]
      exact congrArg (a • ·) (separatedPairMap_baseChangeColimit_one_tmul M i j x)

private theorem separatedStagePairMap_baseChangeColimit_surjective
    (M : SpreadData.FunctorModel F H)
    (hsep : IsSeparatedAffineIntersectionFunctor F) (i j : J) :
    letI : Algebra (𝒮 M.stage) S := (uS M.stage).toRingHom.toAlgebra
    Function.Surjective
      (Algebra.TensorProduct.map (AlgHom.id S S) (separatedStagePairMap M i j)) := by
  letI : Algebra (𝒮 M.stage) S := (uS M.stage).toRingHom.toAlgebra
  let sourceEquiv := separatedPairMapColimitSourceEquiv M i j
  let targetEquiv :=
    (M.object (affineIntersectionPairIndex i j)).baseChangeColimEquiv
      (M.le_stage (affineIntersectionPairIndex i j)) H
  intro y
  obtain ⟨zF, hzF⟩ := hsep i j (targetEquiv y)
  obtain ⟨z, hz⟩ := sourceEquiv.surjective zF
  refine ⟨z, targetEquiv.injective ?_⟩
  change (targetEquiv.toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id S S) (separatedStagePairMap M i j))) z =
    targetEquiv y
  rw [separatedPairMap_baseChangeColimit M i j]
  change affineIntersectionPairMap F i j
      (separatedPairMapColimitSourceEquiv M i j z) = targetEquiv y
  rw [show separatedPairMapColimitSourceEquiv M i j z = zF from hz]
  exact hzF

private theorem exists_separatedStagePairMap_baseChange_surjective
    (M : SpreadData.FunctorModel F H)
    (hsep : IsSeparatedAffineIntersectionFunctor F) (i j : J) :
    ∃ (k : ι) (hik : M.stage ≤ k),
      letI : Algebra (𝒮 M.stage) (𝒮 k) := (t hik).toRingHom.toAlgebra
      Function.Surjective
        (Algebra.TensorProduct.map (AlgHom.id (𝒮 M.stage) (𝒮 k))
          (separatedStagePairMap M i j)) := by
  letI : FinitePresentation (𝒮 M.stage) (separatedStageSingleton M i) :=
    (M.object (affineIntersectionSingletonIndex i)).spreadStage_finitePresentation
      (M.le_stage (affineIntersectionSingletonIndex i))
  letI : FinitePresentation (𝒮 M.stage) (separatedStageSingleton M j) :=
    (M.object (affineIntersectionSingletonIndex j)).spreadStage_finitePresentation
      (M.le_stage (affineIntersectionSingletonIndex j))
  letI : Algebra (separatedStageSingleton M i) (separatedStagePairTensor M i j) :=
    @Algebra.TensorProduct.leftAlgebra
      (𝒮 M.stage) (separatedStageSingleton M i)
      (separatedStageSingleton M i) (separatedStageSingleton M j)
      (inferInstance) (inferInstance) (inferInstance)
      (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance)
  letI : IsScalarTower (𝒮 M.stage) (separatedStageSingleton M i)
      (separatedStagePairTensor M i j) :=
    IsScalarTower.of_algebraMap_eq'
      (R := 𝒮 M.stage) (S := separatedStageSingleton M i)
      (A := separatedStagePairTensor M i j) rfl
  letI : FinitePresentation (separatedStageSingleton M i) (separatedStagePairTensor M i j) :=
    Algebra.FinitePresentation.baseChange
      (R := 𝒮 M.stage) (A := separatedStageSingleton M j) (separatedStageSingleton M i)
  letI : FinitePresentation (𝒮 M.stage) (separatedStagePairTensor M i j) :=
    Algebra.FinitePresentation.trans (𝒮 M.stage)
      (separatedStageSingleton M i) (separatedStagePairTensor M i j)
  letI : FinitePresentation (𝒮 M.stage) (separatedStagePair M i j) :=
    (M.object (affineIntersectionPairIndex i j)).spreadStage_finitePresentation
      (M.le_stage (affineIntersectionPairIndex i j))
  let hC₁Ring : CommRing (separatedStagePairTensor M i j) := inferInstance
  let hC₂Ring : CommRing (separatedStagePair M i j) := inferInstance
  let hC₁Algebra : Algebra (𝒮 M.stage) (separatedStagePairTensor M i j) := inferInstance
  let hC₂Algebra : Algebra (𝒮 M.stage) (separatedStagePair M i j) := inferInstance
  let hC₁Finite : FinitePresentation (𝒮 M.stage) (separatedStagePairTensor M i j) :=
    inferInstance
  let hC₂Finite : FinitePresentation (𝒮 M.stage) (separatedStagePair M i j) :=
    inferInstance
  let hf := separatedStagePairMap_baseChangeColimit_surjective M hsep i j
  exact @IsFilteredAlgColimit.exists_tensorProductMap_surjective
    R (inferInstance) ι (inferInstance) 𝒮 (inferInstance) (inferInstance)
    t S (inferInstance) (inferInstance) uS H M.stage
    (separatedStagePairTensor M i j) (separatedStagePair M i j)
    hC₁Ring hC₂Ring hC₁Algebra hC₂Algebra hC₁Finite hC₂Finite
    (separatedStagePairMap M i j) hf

private theorem exists_separatedLaterStagePairMap_surjective
    (M : SpreadData.FunctorModel F H)
    (hsep : IsSeparatedAffineIntersectionFunctor F) (i j : J) :
    ∃ (k : ι) (hik : M.stage ≤ k),
      Function.Surjective (separatedLaterStagePairMap M hik i j) := by
  obtain ⟨k, hik, hk⟩ := exists_separatedStagePairMap_baseChange_surjective M hsep i j
  exact ⟨k, hik, separatedLaterStagePairMap_surjective_of_baseChange M hik i j hk⟩

private structure SeparatedPairStage
    (M : SpreadData.FunctorModel F H) (i j : J) where
  stage : ι
  le_stage : M.stage ≤ stage
  pairMap_surjective : Function.Surjective
    (separatedLaterStagePairMap M le_stage i j)

private theorem nonempty_separatedPairStage
    (M : SpreadData.FunctorModel F H)
    (hsep : IsSeparatedAffineIntersectionFunctor F) (i j : J) :
    Nonempty (SeparatedPairStage M i j) := by
  obtain ⟨k, hik, hk⟩ := exists_separatedLaterStagePairMap_surjective M hsep i j
  exact ⟨⟨k, hik, hk⟩⟩

private theorem exists_separatedAffineIntersectionFunctorAtLaterStage
    [Finite J] (M : SpreadData.FunctorModel F H)
    (hsep : IsSeparatedAffineIntersectionFunctor F) :
    ∃ (k : ι) (hik : M.stage ≤ k),
      IsSeparatedAffineIntersectionFunctor (M.mapToStage hik).toFunctor := by
  classical
  let C : ∀ r : J × J, SeparatedPairStage M r.1 r.2 := fun r =>
    Classical.choice (nonempty_separatedPairStage M hsep r.1 r.2)
  letI : Fintype (J × J) := Fintype.ofFinite (J × J)
  haveI := H.directed
  haveI := H.nonempty
  obtain ⟨k, hkall⟩ :=
    (insert M.stage (Finset.univ.image fun r : J × J => (C r).stage)).exists_le
  have hMk : M.stage ≤ k := hkall M.stage (Finset.mem_insert_self M.stage _)
  have hC : ∀ r : J × J, (C r).stage ≤ k := fun r => hkall (C r).stage
    (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem (fun q : J × J => (C q).stage)
        (Finset.mem_univ r)))
  refine ⟨k, hMk, fun i j => ?_⟩
  change Function.Surjective (separatedLaterStagePairMap M hMk i j)
  let Cij := C (i, j)
  exact separatedLaterStagePairMap_surjective_trans M Cij.le_stage (hC (i, j)) i j
    Cij.pairMap_surjective

private theorem separatedAffineIntersectionFunctor_mapToStage_trans
    (M : SpreadData.FunctorModel F H)
    {i j : ι} (hMi : M.stage ≤ i) (hij : i ≤ j)
    (hsep : IsSeparatedAffineIntersectionFunctor (M.mapToStage hMi).toFunctor) :
    IsSeparatedAffineIntersectionFunctor (M.mapToStage (hMi.trans hij)).toFunctor := by
  intro p q
  have hpq := hsep p q
  change Function.Surjective (separatedLaterStagePairMap M hMi p q) at hpq
  change Function.Surjective (separatedLaterStagePairMap M (hMi.trans hij) p q)
  exact separatedLaterStagePairMap_surjective_trans M hMi hij p q hpq


end Separated


private theorem exists_openAffineIntersectionFunctorAtLaterStage
    [Finite J] (M : Algebra.SpreadData.FunctorModel F H)
    (hopen : IsOpenAffineIntersectionFunctor F) :
    ∃ (j : ι) (hij : M.stage ≤ j),
      IsOpenAffineIntersectionFunctor (M.mapToStage hij).toFunctor := by
  classical
  obtain ⟨j, hij, hj⟩ := M.exists_common_isOpenImmersion_mapToStage
    (fun r : J × J => singletonIndex r.1)
    (fun r : J × J => pairIndex r.1 r.2)
    (fun r : J × J => singletonToPair r.1 r.2)
    (fun r => by
      simpa [affineIntersectionOverlapι, ringMap] using hopen r.1 r.2)
  refine ⟨j, hij, fun i k => ?_⟩
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    ((M.mapToStage hij).map (singletonToPair i k)).toRingHom))
  exact hj (i, k)

private theorem exists_pushoutAffineIntersectionFunctorAtLaterStage
    [Finite J] (M : Algebra.SpreadData.FunctorModel F H)
    (hpush : IsPushoutAffineIntersectionFunctor F) :
    ∃ (j : ι) (hij : M.stage ≤ j),
      IsPushoutAffineIntersectionFunctor (M.mapToStage hij).toFunctor := by
  classical
  obtain ⟨j, hij, hj⟩ := M.exists_common_isPushout_mapToStage
    (fun r : J × (J × J) => singletonIndex r.1)
    (fun r : J × (J × J) => pairIndex r.1 r.2.1)
    (fun r : J × (J × J) => pairIndex r.1 r.2.2)
    (fun r : J × (J × J) => tripleIndex r.1 r.2.1 r.2.2)
    (fun r : J × (J × J) => singletonToPair r.1 r.2.1)
    (fun r : J × (J × J) => singletonToPair r.1 r.2.2)
    (fun r : J × (J × J) => pairToTripleLeft r.1 r.2.1 r.2.2)
    (fun r : J × (J × J) => pairToTripleRight r.1 r.2.1 r.2.2)
    (fun _ => Subsingleton.elim _ _)
    (fun r => by
      simpa [ringMap] using hpush r.1 r.2.1 r.2.2)
  refine ⟨j, hij, fun i k l => ?_⟩
  change IsPushout
    (CommRingCat.ofHom
      ((M.mapToStage hij).map (singletonToPair i k)).toRingHom)
    (CommRingCat.ofHom
      ((M.mapToStage hij).map (singletonToPair i l)).toRingHom)
    (CommRingCat.ofHom
      ((M.mapToStage hij).map (pairToTripleLeft i k l)).toRingHom)
    (CommRingCat.ofHom
      ((M.mapToStage hij).map (pairToTripleRight i k l)).toRingHom)
  exact hj (i, k, l)

private theorem openAffineIntersectionFunctor_mapToStage_trans
    (M : Algebra.SpreadData.FunctorModel F H)
    {i j : ι} (hMi : M.stage ≤ i) (hij : i ≤ j)
    (hopen : IsOpenAffineIntersectionFunctor
      ((M.mapToStage hMi).mapToStage hij).toFunctor) :
    IsOpenAffineIntersectionFunctor (M.mapToStage (hMi.trans hij)).toFunctor := by
  intro p q
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    ((M.object (singletonIndex p)).mapAtLaterStage
      (M.object (pairIndex p q)) H
      (M.le_stage (singletonIndex p)) (M.le_stage (pairIndex p q))
      (hMi.trans hij) (M.map (singletonToPair p q))).toRingHom))
  rw [← (M.object (singletonIndex p)).mapAtLaterStage_trans
    (M.object (pairIndex p q)) H
    (M.le_stage (singletonIndex p)) (M.le_stage (pairIndex p q))
    hMi hij (M.map (singletonToPair p q))]
  have hpq := hopen p q
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (((M.mapToStage hMi).mapToStage hij).map
      (singletonToPair p q)).toRingHom)) at hpq
  exact hpq

private theorem pushoutAffineIntersectionFunctor_mapToStage_trans
    (M : Algebra.SpreadData.FunctorModel F H)
    {i j : ι} (hMi : M.stage ≤ i) (hij : i ≤ j)
    (hpush : IsPushoutAffineIntersectionFunctor (M.mapToStage hMi).toFunctor) :
    IsPushoutAffineIntersectionFunctor (M.mapToStage (hMi.trans hij)).toFunctor := by
  intro p q r
  have h := (M.object (singletonIndex p)).isPushout_mapAtLaterStage_trans
    (M.object (pairIndex p q)) (M.object (pairIndex p r))
    (M.object (tripleIndex p q r)) H
    (M.le_stage (singletonIndex p)) (M.le_stage (pairIndex p q))
    (M.le_stage (pairIndex p r)) (M.le_stage (tripleIndex p q r))
    hMi hij (M.map (singletonToPair p q)) (M.map (singletonToPair p r))
    (M.map (pairToTripleLeft p q r)) (M.map (pairToTripleRight p q r))
    (by
      have hpqr := hpush p q r
      change IsPushout
        (CommRingCat.ofHom
          ((M.mapToStage hMi).map (singletonToPair p q)).toRingHom)
        (CommRingCat.ofHom
          ((M.mapToStage hMi).map (singletonToPair p r)).toRingHom)
        (CommRingCat.ofHom
          ((M.mapToStage hMi).map (pairToTripleLeft p q r)).toRingHom)
        (CommRingCat.ofHom
          ((M.mapToStage hMi).map (pairToTripleRight p q r)).toRingHom) at hpqr
      exact hpqr)
  change IsPushout
    (CommRingCat.ofHom
      ((M.mapToStage (hMi.trans hij)).map (singletonToPair p q)).toRingHom)
    (CommRingCat.ofHom
      ((M.mapToStage (hMi.trans hij)).map (singletonToPair p r)).toRingHom)
    (CommRingCat.ofHom
      ((M.mapToStage (hMi.trans hij)).map (pairToTripleLeft p q r)).toRingHom)
    (CommRingCat.ofHom
      ((M.mapToStage (hMi.trans hij)).map (pairToTripleRight p q r)).toRingHom)
  exact h

private theorem pushoutAffineIntersectionFunctor_mapToStage_reconcile
    (M : Algebra.SpreadData.FunctorModel F H)
    {i j : ι} (hMi : M.stage ≤ i) (hij : i ≤ j)
    (hpush : IsPushoutAffineIntersectionFunctor
      ((M.mapToStage hMi).mapToStage hij).toFunctor) :
    IsPushoutAffineIntersectionFunctor (M.mapToStage (hMi.trans hij)).toFunctor := by
  intro p q r
  change IsPushout
    (CommRingCat.ofHom
      ((M.object (singletonIndex p)).mapAtLaterStage
        (M.object (pairIndex p q)) H
        (M.le_stage (singletonIndex p)) (M.le_stage (pairIndex p q))
        (hMi.trans hij) (M.map (singletonToPair p q))).toRingHom)
    (CommRingCat.ofHom
      ((M.object (singletonIndex p)).mapAtLaterStage
        (M.object (pairIndex p r)) H
        (M.le_stage (singletonIndex p)) (M.le_stage (pairIndex p r))
        (hMi.trans hij) (M.map (singletonToPair p r))).toRingHom)
    (CommRingCat.ofHom
      ((M.object (pairIndex p q)).mapAtLaterStage
        (M.object (tripleIndex p q r)) H
        (M.le_stage (pairIndex p q)) (M.le_stage (tripleIndex p q r))
        (hMi.trans hij) (M.map (pairToTripleLeft p q r))).toRingHom)
    (CommRingCat.ofHom
      ((M.object (pairIndex p r)).mapAtLaterStage
        (M.object (tripleIndex p q r)) H
        (M.le_stage (pairIndex p r)) (M.le_stage (tripleIndex p q r))
        (hMi.trans hij) (M.map (pairToTripleRight p q r))).toRingHom)
  rw [← (M.object (singletonIndex p)).mapAtLaterStage_trans
      (M.object (pairIndex p q)) H
      (M.le_stage (singletonIndex p)) (M.le_stage (pairIndex p q))
      hMi hij (M.map (singletonToPair p q)),
    ← (M.object (singletonIndex p)).mapAtLaterStage_trans
      (M.object (pairIndex p r)) H
      (M.le_stage (singletonIndex p)) (M.le_stage (pairIndex p r))
      hMi hij (M.map (singletonToPair p r)),
    ← (M.object (pairIndex p q)).mapAtLaterStage_trans
      (M.object (tripleIndex p q r)) H
      (M.le_stage (pairIndex p q)) (M.le_stage (tripleIndex p q r))
      hMi hij (M.map (pairToTripleLeft p q r)),
    ← (M.object (pairIndex p r)).mapAtLaterStage_trans
      (M.object (tripleIndex p q r)) H
      (M.le_stage (pairIndex p r)) (M.le_stage (tripleIndex p q r))
      hMi hij (M.map (pairToTripleRight p q r))]
  have hpqr := hpush p q r
  change IsPushout
    (CommRingCat.ofHom
      (((M.mapToStage hMi).mapToStage hij).map (singletonToPair p q)).toRingHom)
    (CommRingCat.ofHom
      (((M.mapToStage hMi).mapToStage hij).map (singletonToPair p r)).toRingHom)
    (CommRingCat.ofHom
      (((M.mapToStage hMi).mapToStage hij).map (pairToTripleLeft p q r)).toRingHom)
    (CommRingCat.ofHom
      (((M.mapToStage hMi).mapToStage hij).map (pairToTripleRight p q r)).toRingHom) at hpqr
  exact hpqr

/-- The open-immersion and pushout conditions of a finite affine-intersection
functor hold simultaneously at one later spread stage. -/
theorem _root_.Algebra.SpreadData.FunctorModel.exists_affineIntersectionConditionsAtLaterStage
    [Finite J] (M : Algebra.SpreadData.FunctorModel F H)
    (hopen : IsOpenAffineIntersectionFunctor F)
    (hpush : IsPushoutAffineIntersectionFunctor F) :
    ∃ (j : ι) (hij : M.stage ≤ j),
      IsOpenAffineIntersectionFunctor (M.mapToStage hij).toFunctor ∧
        IsPushoutAffineIntersectionFunctor (M.mapToStage hij).toFunctor := by
  obtain ⟨i, hMi, hpush_i⟩ :=
    exists_pushoutAffineIntersectionFunctorAtLaterStage M hpush
  obtain ⟨j, hij, hopen_j⟩ :=
    exists_openAffineIntersectionFunctorAtLaterStage (M.mapToStage hMi) hopen
  exact ⟨j, hMi.trans hij,
    openAffineIntersectionFunctor_mapToStage_trans M hMi hij hopen_j,
    pushoutAffineIntersectionFunctor_mapToStage_trans M hMi hij hpush_i⟩

/-- The open-immersion, pushout, and separatedness conditions of a finite
affine-intersection functor hold simultaneously at one later spread stage. -/
theorem _root_.Algebra.SpreadData.FunctorModel.exists_affineIntersectionConditionsAndSeparatedAtLaterStage
    [Finite J] (M : Algebra.SpreadData.FunctorModel F H)
    (hopen : IsOpenAffineIntersectionFunctor F)
    (hpush : IsPushoutAffineIntersectionFunctor F)
    (hsep : IsSeparatedAffineIntersectionFunctor F) :
    ∃ (j : ι) (hij : M.stage ≤ j),
      IsOpenAffineIntersectionFunctor (M.mapToStage hij).toFunctor ∧
        IsPushoutAffineIntersectionFunctor (M.mapToStage hij).toFunctor ∧
          IsSeparatedAffineIntersectionFunctor (M.mapToStage hij).toFunctor := by
  obtain ⟨i, hMi, hsep_i⟩ :=
    exists_separatedAffineIntersectionFunctorAtLaterStage M hsep
  obtain ⟨j, hij, hopen_j, hpush_j⟩ :=
    (M.mapToStage hMi).exists_affineIntersectionConditionsAtLaterStage hopen hpush
  exact ⟨j, hMi.trans hij,
    openAffineIntersectionFunctor_mapToStage_trans M hMi hij hopen_j,
    pushoutAffineIntersectionFunctor_mapToStage_reconcile M hMi hij hpush_j,
    separatedAffineIntersectionFunctor_mapToStage_trans M hMi hij hsep_i⟩

end Spread

private noncomputable def overlapTransition
    (F : Finset J ⥤ CommAlgCat.{u} S) (i j : J) :
    affineIntersectionOverlap F i j ⟶ affineIntersectionOverlap F j i :=
  Spec.map (ringMap F (affineIntersectionPairSwap i j))

private lemma overlapTransition_self (F : Finset J ⥤ CommAlgCat.{u} S) (i : J) :
    overlapTransition F i i = 𝟙 _ := by
  rw [overlapTransition]
  have h : affineIntersectionPairSwap i i = 𝟙 _ := Subsingleton.elim _ _
  rw [h, ringMap_id, Spec.map_id]

private theorem affineIntersectionOverlapι_self_isIso
    (F : Finset J ⥤ CommAlgCat.{u} S) (i : J) :
    IsIso (affineIntersectionOverlapι F i i) := by
  rw [affineIntersectionOverlapι]
  refine ⟨⟨Spec.map (ringMap F (pairToSingletonSelf i)), ?_, ?_⟩⟩
  · rw [← Spec.map_comp, ← ringMap_comp]
    have h : pairToSingletonSelf i ≫ singletonToPair i i = 𝟙 _ := Subsingleton.elim _ _
    rw [h, ringMap_id, Spec.map_id]
  · rw [← Spec.map_comp, ← ringMap_comp]
    have h : singletonToPair i i ≫ pairToSingletonSelf i = 𝟙 _ := Subsingleton.elim _ _
    rw [h, ringMap_id, Spec.map_id]

private theorem tripleIsPullback
    (F : Finset J ⥤ CommAlgCat.{u} S) (hpush : IsPushoutAffineIntersectionFunctor F)
    (i j k : J) :
    IsPullback
      (Spec.map (ringMap F (pairToTripleLeft i j k)))
      (Spec.map (ringMap F (pairToTripleRight i j k)))
      (affineIntersectionOverlapι F i j) (affineIntersectionOverlapι F i k) := by
  exact (hpush i j k).op.flip.map Scheme.Spec

private noncomputable def triplePullbackIso
    (F : Finset J ⥤ CommAlgCat.{u} S) (hpush : IsPushoutAffineIntersectionFunctor F)
    (i j k : J) :
    Spec (ringObj F (tripleIndex i j k)) ≅
      pullback (affineIntersectionOverlapι F i j) (affineIntersectionOverlapι F i k) :=
  (tripleIsPullback F hpush i j k).isoPullback

@[reassoc]
private lemma triplePullbackIso_hom_fst
    (F : Finset J ⥤ CommAlgCat.{u} S) (hpush : IsPushoutAffineIntersectionFunctor F)
    (i j k : J) :
    (triplePullbackIso F hpush i j k).hom ≫ pullback.fst _ _ =
      Spec.map (ringMap F (pairToTripleLeft i j k)) :=
  (tripleIsPullback F hpush i j k).isoPullback_hom_fst

@[reassoc]
private lemma triplePullbackIso_hom_snd
    (F : Finset J ⥤ CommAlgCat.{u} S) (hpush : IsPushoutAffineIntersectionFunctor F)
    (i j k : J) :
    (triplePullbackIso F hpush i j k).hom ≫ pullback.snd _ _ =
      Spec.map (ringMap F (pairToTripleRight i j k)) :=
  (tripleIsPullback F hpush i j k).isoPullback_hom_snd

private noncomputable def tripleTransition
    (F : Finset J ⥤ CommAlgCat.{u} S) (hpush : IsPushoutAffineIntersectionFunctor F)
    (i j k : J) :
    pullback (affineIntersectionOverlapι F i j) (affineIntersectionOverlapι F i k) ⟶
      pullback (affineIntersectionOverlapι F j k) (affineIntersectionOverlapι F j i) :=
  (triplePullbackIso F hpush i j k).inv ≫
    Spec.map (ringMap F (tripleCycle i j k)) ≫
      (triplePullbackIso F hpush j k i).hom

private lemma tripleTransition_fac
    (F : Finset J ⥤ CommAlgCat.{u} S) (hpush : IsPushoutAffineIntersectionFunctor F)
    (i j k : J) :
    tripleTransition F hpush i j k ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ overlapTransition F i j := by
  rw [← cancel_epi (triplePullbackIso F hpush i j k).hom]
  simp only [tripleTransition, Category.assoc, Iso.hom_inv_id_assoc]
  rw [triplePullbackIso_hom_snd, triplePullbackIso_hom_fst_assoc]
  rw [overlapTransition]
  rw [← Spec.map_comp, ← Spec.map_comp, ← ringMap_comp, ← ringMap_comp]
  congr 2

private lemma tripleCycle_scheme
    (F : Finset J ⥤ CommAlgCat.{u} S) (i j k : J) :
    Spec.map (ringMap F (tripleCycle i j k)) ≫
        Spec.map (ringMap F (tripleCycle j k i)) ≫
          Spec.map (ringMap F (tripleCycle k i j)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← ringMap_comp, ← ringMap_comp]
  have h : (tripleCycle k i j ≫ tripleCycle j k i) ≫ tripleCycle i j k = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [h, ringMap_id, Spec.map_id]

private lemma tripleTransition_cocycle
    (F : Finset J ⥤ CommAlgCat.{u} S) (hpush : IsPushoutAffineIntersectionFunctor F)
    (i j k : J) :
    tripleTransition F hpush i j k ≫ tripleTransition F hpush j k i ≫
      tripleTransition F hpush k i j = 𝟙 _ := by
  rw [← cancel_epi (triplePullbackIso F hpush i j k).hom]
  simp only [tripleTransition, Category.assoc, Iso.hom_inv_id_assoc]
  simp only [Category.comp_id]
  have hcycle :
      (Spec.map (ringMap F (tripleCycle i j k)) ≫
          Spec.map (ringMap F (tripleCycle j k i))) ≫
        Spec.map (ringMap F (tripleCycle k i j)) = 𝟙 _ := by
    rw [Category.assoc]
    exact tripleCycle_scheme F i j k
  rw [← Category.assoc, ← Category.assoc, hcycle, Category.id_comp]

/-- The scheme glue data associated to an augmented affine finite-intersection
functor. -/
noncomputable abbrev ofAffineIntersectionFunctor
    (F : Finset J ⥤ CommAlgCat.{u} S)
    (hopen : IsOpenAffineIntersectionFunctor F)
    (hpush : IsPushoutAffineIntersectionFunctor F) : Scheme.GlueData.{u} where
  J := J
  U := affineIntersectionChart F
  V := fun p ↦ affineIntersectionOverlap F p.1 p.2
  f := affineIntersectionOverlapι F
  f_mono i j := by
    letI := hopen i j
    infer_instance
  f_id i := affineIntersectionOverlapι_self_isIso F i
  t := overlapTransition F
  t_id := overlapTransition_self F
  t' := tripleTransition F hpush
  t_fac := tripleTransition_fac F hpush
  cocycle := tripleTransition_cocycle F hpush
  f_open := hopen

/-- The charts of `ofAffineIntersectionFunctor` are the singleton spectra. -/
@[simp]
lemma ofAffineIntersectionFunctor_U
    (F : Finset J ⥤ CommAlgCat.{u} S)
    (hopen : IsOpenAffineIntersectionFunctor F)
    (hpush : IsPushoutAffineIntersectionFunctor F) (i : J) :
    (ofAffineIntersectionFunctor F hopen hpush).U i = affineIntersectionChart F i :=
  rfl

/-- The overlaps of `ofAffineIntersectionFunctor` are the pair spectra. -/
@[simp]
lemma ofAffineIntersectionFunctor_V
    (F : Finset J ⥤ CommAlgCat.{u} S)
    (hopen : IsOpenAffineIntersectionFunctor F)
    (hpush : IsPushoutAffineIntersectionFunctor F) (i j : J) :
    (ofAffineIntersectionFunctor F hopen hpush).V (i, j) =
      affineIntersectionOverlap F i j :=
  rfl

/-- The overlap legs of `ofAffineIntersectionFunctor` are induced by singleton-to-pair maps. -/
@[simp]
lemma ofAffineIntersectionFunctor_f
    (F : Finset J ⥤ CommAlgCat.{u} S)
    (hopen : IsOpenAffineIntersectionFunctor F)
    (hpush : IsPushoutAffineIntersectionFunctor F) (i j : J) :
    (ofAffineIntersectionFunctor F hopen hpush).f i j =
      affineIntersectionOverlapι F i j :=
  rfl

/-- The canonical morphism from a singleton chart to the spectrum of the base ring. -/
noncomputable def affineIntersectionChartToSpec
    (F : Finset J ⥤ CommAlgCat.{u} S) (i : J) :
    affineIntersectionChart F i ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap S (F.obj (affineIntersectionSingletonIndex i))))

private theorem affineIntersectionChartToSpec_compatible
    (F : Finset J ⥤ CommAlgCat.{u} S) (i j : J) :
    affineIntersectionOverlapι F i j ≫ affineIntersectionChartToSpec F i =
      overlapTransition F i j ≫ affineIntersectionOverlapι F j i ≫
        affineIntersectionChartToSpec F j := by
  simp only [affineIntersectionOverlapι, affineIntersectionChartToSpec, overlapTransition]
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  simp [ringMap]

/-- The affine-intersection glued scheme carries the structural morphism induced by the
base-algebra structure on every chart. -/
noncomputable def affineIntersectionToSpec
    (F : Finset J ⥤ CommAlgCat.{u} S)
    (hopen : IsOpenAffineIntersectionFunctor F)
    (hpush : IsPushoutAffineIntersectionFunctor F) :
    (ofAffineIntersectionFunctor F hopen hpush).glued ⟶ Spec (CommRingCat.of S) := by
  let D : Scheme.GlueData := ofAffineIntersectionFunctor F hopen hpush
  change D.glued ⟶ Spec (CommRingCat.of S)
  letI : HasMulticoequalizer D.diagram :=
    _root_.AlgebraicGeometry.Scheme.GlueData.instHasMulticoequalizerDiagram D
  fapply Multicoequalizer.desc D.diagram
  · exact affineIntersectionChartToSpec F
  rintro ⟨i, j⟩
  exact affineIntersectionChartToSpec_compatible F i j

/-- The structural morphism of an affine-intersection glue restricts to the canonical
structural morphism on each singleton chart. -/
@[reassoc]
theorem ofAffineIntersectionFunctor_ι_affineIntersectionToSpec
    (F : Finset J ⥤ CommAlgCat.{u} S)
    (hopen : IsOpenAffineIntersectionFunctor F)
    (hpush : IsPushoutAffineIntersectionFunctor F) (i : J) :
    (ofAffineIntersectionFunctor F hopen hpush).ι i ≫
        affineIntersectionToSpec F hopen hpush =
      affineIntersectionChartToSpec F i := by
  let D : Scheme.GlueData := ofAffineIntersectionFunctor F hopen hpush
  change D.ι i ≫ affineIntersectionToSpec F hopen hpush =
    affineIntersectionChartToSpec F i
  letI : HasMulticoequalizer D.diagram :=
    _root_.AlgebraicGeometry.Scheme.GlueData.instHasMulticoequalizerDiagram D
  change Multicoequalizer.π D.diagram i ≫ _ = _
  exact Multicoequalizer.π_desc _ _ _ _ _

private noncomputable def affineIntersectionOverlapPullbackIso
    (F : Finset J ⥤ CommAlgCat.{u} S)
    (hopen : IsOpenAffineIntersectionFunctor F)
    (hpush : IsPushoutAffineIntersectionFunctor F) (i j : J) :
    affineIntersectionOverlap F i j ≅
      pullback ((ofAffineIntersectionFunctor F hopen hpush).ι i)
        ((ofAffineIntersectionFunctor F hopen hpush).ι j) :=
  ((ofAffineIntersectionFunctor F hopen hpush).vPullbackConeIsLimit i j).conePointUniqueUpToIso
    (limit.isLimit _)

private noncomputable def affineIntersectionChartProductIso
    (F : Finset J ⥤ CommAlgCat.{u} S)
    (hopen : IsOpenAffineIntersectionFunctor F)
    (hpush : IsPushoutAffineIntersectionFunctor F) (i j : J) :
    pullback
        (((ofAffineIntersectionFunctor F hopen hpush).ι i) ≫
          affineIntersectionToSpec F hopen hpush)
        (((ofAffineIntersectionFunctor F hopen hpush).ι j) ≫
          affineIntersectionToSpec F hopen hpush) ≅
      Spec (CommRingCat.of
        (TensorProduct S
          (F.obj (affineIntersectionSingletonIndex i) : Type u)
          (F.obj (affineIntersectionSingletonIndex j) : Type u))) :=
  pullback.congrHom
      (ofAffineIntersectionFunctor_ι_affineIntersectionToSpec F hopen hpush i)
      (ofAffineIntersectionFunctor_ι_affineIntersectionToSpec F hopen hpush j) ≪≫
    pullbackSpecIso S
      (F.obj (affineIntersectionSingletonIndex i) : Type u)
      (F.obj (affineIntersectionSingletonIndex j) : Type u)

private lemma affineIntersectionOverlapPullbackIso_hom_fst
    (F : Finset J ⥤ CommAlgCat.{u} S)
    (hopen : IsOpenAffineIntersectionFunctor F)
    (hpush : IsPushoutAffineIntersectionFunctor F) (i j : J) :
    (affineIntersectionOverlapPullbackIso F hopen hpush i j).hom ≫
        pullback.fst ((ofAffineIntersectionFunctor F hopen hpush).ι i)
          ((ofAffineIntersectionFunctor F hopen hpush).ι j) =
      affineIntersectionOverlapι F i j := by
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    ((ofAffineIntersectionFunctor F hopen hpush).vPullbackConeIsLimit i j)
    (limit.isLimit _) WalkingCospan.left

private lemma affineIntersectionOverlapPullbackIso_hom_snd
    (F : Finset J ⥤ CommAlgCat.{u} S)
    (hopen : IsOpenAffineIntersectionFunctor F)
    (hpush : IsPushoutAffineIntersectionFunctor F) (i j : J) :
    (affineIntersectionOverlapPullbackIso F hopen hpush i j).hom ≫
        pullback.snd ((ofAffineIntersectionFunctor F hopen hpush).ι i)
          ((ofAffineIntersectionFunctor F hopen hpush).ι j) =
      (ofAffineIntersectionFunctor F hopen hpush).t i j ≫
        (ofAffineIntersectionFunctor F hopen hpush).f j i := by
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    ((ofAffineIntersectionFunctor F hopen hpush).vPullbackConeIsLimit i j)
    (limit.isLimit _) WalkingCospan.right

private lemma affineIntersectionPairMap_includeLeft
    (F : Finset J ⥤ CommAlgCat.{u} S) (i j : J) :
    (affineIntersectionPairMap F i j).comp
        (Algebra.TensorProduct.includeLeft
          (R := S) (S := S)
          (A := (F.obj (affineIntersectionSingletonIndex i) : Type u))
          (B := (F.obj (affineIntersectionSingletonIndex j) : Type u))) =
      (F.map (affineIntersectionSingletonToPair i j)).hom := by
  ext x
  exact Algebra.TensorProduct.productMap_left_apply _ _ x

private lemma affineIntersectionPairMap_includeRight
    (F : Finset J ⥤ CommAlgCat.{u} S) (i j : J) :
    (affineIntersectionPairMap F i j).comp
        ((Algebra.TensorProduct.includeRight
          (R := S)
          (A := (F.obj (affineIntersectionSingletonIndex i) : Type u))
          (B := (F.obj (affineIntersectionSingletonIndex j) : Type u))).restrictScalars S) =
      (F.map (affineIntersectionSingletonToPairRight i j)).hom := by
  ext x
  exact Algebra.TensorProduct.productMap_right_apply _ _ x

private lemma affineIntersectionChartProductIso_inv_fst
    (F : Finset J ⥤ CommAlgCat.{u} S)
    (hopen : IsOpenAffineIntersectionFunctor F)
    (hpush : IsPushoutAffineIntersectionFunctor F) (i j : J) :
    (affineIntersectionChartProductIso F hopen hpush i j).inv ≫
        pullback.fst
          (((ofAffineIntersectionFunctor F hopen hpush).ι i) ≫
            affineIntersectionToSpec F hopen hpush)
          (((ofAffineIntersectionFunctor F hopen hpush).ι j) ≫
            affineIntersectionToSpec F hopen hpush) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom
          (R := S)
          (A := (F.obj (affineIntersectionSingletonIndex i) : Type u))
          (B := (F.obj (affineIntersectionSingletonIndex j) : Type u)))) := by
  rw [affineIntersectionChartProductIso, Iso.trans_inv, Category.assoc,
    pullback.congrHom_inv]
  simp only [pullback.map, pullback.lift_fst, Category.comp_id]
  exact pullbackSpecIso_inv_fst S
    (F.obj (affineIntersectionSingletonIndex i) : Type u)
    (F.obj (affineIntersectionSingletonIndex j) : Type u)

private lemma affineIntersectionChartProductIso_inv_snd
    (F : Finset J ⥤ CommAlgCat.{u} S)
    (hopen : IsOpenAffineIntersectionFunctor F)
    (hpush : IsPushoutAffineIntersectionFunctor F) (i j : J) :
    (affineIntersectionChartProductIso F hopen hpush i j).inv ≫
        pullback.snd
          (((ofAffineIntersectionFunctor F hopen hpush).ι i) ≫
            affineIntersectionToSpec F hopen hpush)
          (((ofAffineIntersectionFunctor F hopen hpush).ι j) ≫
            affineIntersectionToSpec F hopen hpush) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight
          (R := S)
          (A := (F.obj (affineIntersectionSingletonIndex i) : Type u))
          (B := (F.obj (affineIntersectionSingletonIndex j) : Type u))).toRingHom) := by
  rw [affineIntersectionChartProductIso, Iso.trans_inv, Category.assoc,
    pullback.congrHom_inv]
  simp only [pullback.map, pullback.lift_snd, Category.comp_id]
  exact pullbackSpecIso_inv_snd S
    (F.obj (affineIntersectionSingletonIndex i) : Type u)
    (F.obj (affineIntersectionSingletonIndex j) : Type u)

private lemma spec_affineIntersectionPairMap_comp_includeLeft
    (F : Finset J ⥤ CommAlgCat.{u} S) (i j : J) :
    Spec.map (CommRingCat.ofHom (affineIntersectionPairMap F i j).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom
            (R := S)
            (A := (F.obj (affineIntersectionSingletonIndex i) : Type u))
            (B := (F.obj (affineIntersectionSingletonIndex j) : Type u)))) =
      affineIntersectionOverlapι F i j := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.Hom.ext
  exact congrArg AlgHom.toRingHom (affineIntersectionPairMap_includeLeft F i j)

private lemma spec_affineIntersectionPairMap_comp_includeRight
    (F : Finset J ⥤ CommAlgCat.{u} S)
    (hopen : IsOpenAffineIntersectionFunctor F)
    (hpush : IsPushoutAffineIntersectionFunctor F) (i j : J) :
    Spec.map (CommRingCat.ofHom (affineIntersectionPairMap F i j).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight
            (R := S)
            (A := (F.obj (affineIntersectionSingletonIndex i) : Type u))
            (B := (F.obj (affineIntersectionSingletonIndex j) : Type u))).toRingHom) =
      (ofAffineIntersectionFunctor F hopen hpush).t i j ≫
        (ofAffineIntersectionFunctor F hopen hpush).f j i := by
  change Spec.map _ ≫ Spec.map _ =
    Spec.map (CommRingCat.ofHom
      (F.map (affineIntersectionPairSwap i j)).hom.toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      (F.map (affineIntersectionSingletonToPair j i)).hom.toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.Hom.ext
  ext x
  change affineIntersectionPairMap F i j (1 ⊗ₜ[S] x) =
    (F.map (affineIntersectionPairSwap i j)).hom
      ((F.map (affineIntersectionSingletonToPair j i)).hom x)
  rw [affineIntersectionPairMap, Algebra.TensorProduct.productMap_right_apply]
  exact ConcreteCategory.congr_hom
    (F.map_comp (affineIntersectionSingletonToPair j i)
      (affineIntersectionPairSwap i j)) x

private lemma affineIntersectionPairMap_spec
    (F : Finset J ⥤ CommAlgCat.{u} S)
    (hopen : IsOpenAffineIntersectionFunctor F)
    (hpush : IsPushoutAffineIntersectionFunctor F) (i j : J) :
    (affineIntersectionOverlapPullbackIso F hopen hpush i j).hom ≫
        pullback.mapDesc
          ((ofAffineIntersectionFunctor F hopen hpush).ι i)
          ((ofAffineIntersectionFunctor F hopen hpush).ι j)
          (affineIntersectionToSpec F hopen hpush) ≫
        (affineIntersectionChartProductIso F hopen hpush i j).hom =
      Spec.map (CommRingCat.ofHom (affineIntersectionPairMap F i j).toRingHom) := by
  rw [← cancel_mono (affineIntersectionChartProductIso F hopen hpush i j).inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply pullback.hom_ext
  · calc
      (affineIntersectionOverlapPullbackIso F hopen hpush i j).hom ≫
            pullback.mapDesc
              ((ofAffineIntersectionFunctor F hopen hpush).ι i)
              ((ofAffineIntersectionFunctor F hopen hpush).ι j)
              (affineIntersectionToSpec F hopen hpush) ≫
            pullback.fst
              (((ofAffineIntersectionFunctor F hopen hpush).ι i) ≫
                affineIntersectionToSpec F hopen hpush)
              (((ofAffineIntersectionFunctor F hopen hpush).ι j) ≫
                affineIntersectionToSpec F hopen hpush) =
          (affineIntersectionOverlapPullbackIso F hopen hpush i j).hom ≫
            pullback.fst ((ofAffineIntersectionFunctor F hopen hpush).ι i)
              ((ofAffineIntersectionFunctor F hopen hpush).ι j) := by
        simp only [pullback.mapDesc, pullback.map, pullback.lift_fst, Category.comp_id]
      _ = affineIntersectionOverlapι F i j :=
        affineIntersectionOverlapPullbackIso_hom_fst F hopen hpush i j
      _ = Spec.map (CommRingCat.ofHom (affineIntersectionPairMap F i j).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom
              (R := S)
              (A := (F.obj (affineIntersectionSingletonIndex i) : Type u))
              (B := (F.obj (affineIntersectionSingletonIndex j) : Type u)))) :=
        (spec_affineIntersectionPairMap_comp_includeLeft F i j).symm
      _ = Spec.map (CommRingCat.ofHom (affineIntersectionPairMap F i j).toRingHom) ≫
          (affineIntersectionChartProductIso F hopen hpush i j).inv ≫
            pullback.fst
              (((ofAffineIntersectionFunctor F hopen hpush).ι i) ≫
                affineIntersectionToSpec F hopen hpush)
              (((ofAffineIntersectionFunctor F hopen hpush).ι j) ≫
                affineIntersectionToSpec F hopen hpush) := by
        rw [affineIntersectionChartProductIso_inv_fst F hopen hpush i j]
  · calc
      (affineIntersectionOverlapPullbackIso F hopen hpush i j).hom ≫
            pullback.mapDesc
              ((ofAffineIntersectionFunctor F hopen hpush).ι i)
              ((ofAffineIntersectionFunctor F hopen hpush).ι j)
              (affineIntersectionToSpec F hopen hpush) ≫
            pullback.snd
              (((ofAffineIntersectionFunctor F hopen hpush).ι i) ≫
                affineIntersectionToSpec F hopen hpush)
              (((ofAffineIntersectionFunctor F hopen hpush).ι j) ≫
                affineIntersectionToSpec F hopen hpush) =
          (affineIntersectionOverlapPullbackIso F hopen hpush i j).hom ≫
            pullback.snd ((ofAffineIntersectionFunctor F hopen hpush).ι i)
              ((ofAffineIntersectionFunctor F hopen hpush).ι j) := by
        simp only [pullback.mapDesc, pullback.map, pullback.lift_snd, Category.comp_id]
      _ = (ofAffineIntersectionFunctor F hopen hpush).t i j ≫
          (ofAffineIntersectionFunctor F hopen hpush).f j i :=
        affineIntersectionOverlapPullbackIso_hom_snd F hopen hpush i j
      _ = Spec.map (CommRingCat.ofHom (affineIntersectionPairMap F i j).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight
              (R := S)
              (A := (F.obj (affineIntersectionSingletonIndex i) : Type u))
              (B := (F.obj (affineIntersectionSingletonIndex j) : Type u))).toRingHom) :=
        (spec_affineIntersectionPairMap_comp_includeRight F hopen hpush i j).symm
      _ = Spec.map (CommRingCat.ofHom (affineIntersectionPairMap F i j).toRingHom) ≫
          (affineIntersectionChartProductIso F hopen hpush i j).inv ≫
            pullback.snd
              (((ofAffineIntersectionFunctor F hopen hpush).ι i) ≫
                affineIntersectionToSpec F hopen hpush)
              (((ofAffineIntersectionFunctor F hopen hpush).ι j) ≫
                affineIntersectionToSpec F hopen hpush) := by
        rw [affineIntersectionChartProductIso_inv_snd F hopen hpush i j]

/-- Surjectivity of the canonical pair maps makes the structural morphism of an
affine-intersection glue separated. -/
theorem isSeparated_affineIntersectionToSpec
    (F : Finset J ⥤ CommAlgCat.{u} S)
    (hopen : IsOpenAffineIntersectionFunctor F)
    (hpush : IsPushoutAffineIntersectionFunctor F)
    (hsep : IsSeparatedAffineIntersectionFunctor F) :
    IsSeparated (affineIntersectionToSpec F hopen hpush) := by
  refine { isClosedImmersion_diagonal := ?_ }
  haveI (i : (ofAffineIntersectionFunctor F hopen hpush).openCover.I₀) :
      IsAffine ((ofAffineIntersectionFunctor F hopen hpush).openCover.X i) := by
    change IsAffine (Spec (CommRingCat.of
      (F.obj (affineIntersectionSingletonIndex i))))
    infer_instance
  letI : HasAffineProperty @IsClosedImmersion
      (AffineTargetMorphismProperty.of @IsClosedImmersion) :=
    HasAffineProperty.of_isZariskiLocalAtTarget @IsClosedImmersion
  apply (HasAffineProperty.diagonal_iff
    (@IsClosedImmersion)
    (Q := AffineTargetMorphismProperty.of @IsClosedImmersion)).mp
  apply AffineTargetMorphismProperty.diagonal_of_openCover_source
    (Q := AffineTargetMorphismProperty.of @IsClosedImmersion)
    (affineIntersectionToSpec F hopen hpush)
    (ofAffineIntersectionFunctor F hopen hpush).openCover
  intro i j
  change IsClosedImmersion
    (pullback.mapDesc
      ((ofAffineIntersectionFunctor F hopen hpush).ι i)
      ((ofAffineIntersectionFunctor F hopen hpush).ι j)
      (affineIntersectionToSpec F hopen hpush))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
    (affineIntersectionOverlapPullbackIso F hopen hpush i j).hom
    (pullback.mapDesc
      ((ofAffineIntersectionFunctor F hopen hpush).ι i)
      ((ofAffineIntersectionFunctor F hopen hpush).ι j)
      (affineIntersectionToSpec F hopen hpush))]
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion
    ((affineIntersectionOverlapPullbackIso F hopen hpush i j).hom ≫
      pullback.mapDesc
        ((ofAffineIntersectionFunctor F hopen hpush).ι i)
        ((ofAffineIntersectionFunctor F hopen hpush).ι j)
        (affineIntersectionToSpec F hopen hpush))
    (affineIntersectionChartProductIso F hopen hpush i j).hom]
  rw [Category.assoc, affineIntersectionPairMap_spec F hopen hpush i j]
  exact IsClosedImmersion.spec_of_surjective _ (hsep i j)

/-- If the singleton charts of an affine-intersection functor are finitely presented over
the base, then the structural morphism of the glued scheme is locally of finite
presentation. -/
theorem locallyOfFinitePresentation_affineIntersectionToSpec
    (F : Finset J ⥤ CommAlgCat.{u} S)
    (hopen : IsOpenAffineIntersectionFunctor F)
    (hpush : IsPushoutAffineIntersectionFunctor F)
    (hfinite : ∀ i : J,
      Algebra.FinitePresentation S
        (F.obj (affineIntersectionSingletonIndex i))) :
    LocallyOfFinitePresentation (affineIntersectionToSpec F hopen hpush) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation)
    (ofAffineIntersectionFunctor F hopen hpush).openCover
  intro i
  change LocallyOfFinitePresentation
    ((ofAffineIntersectionFunctor F hopen hpush).ι i ≫
      affineIntersectionToSpec F hopen hpush)
  rw [ofAffineIntersectionFunctor_ι_affineIntersectionToSpec]
  change LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom
      (algebraMap S (F.obj (affineIntersectionSingletonIndex i)))))
  apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
  change (algebraMap S
    (F.obj (affineIntersectionSingletonIndex i))).FinitePresentation
  exact RingHom.finitePresentation_algebraMap.mpr (hfinite i)

/-- If the chart index of an affine-intersection functor is finite, then the
structural morphism of the glued scheme is quasi-compact. -/
theorem quasiCompact_affineIntersectionToSpec [Finite J]
    (F : Finset J ⥤ CommAlgCat.{u} S)
    (hopen : IsOpenAffineIntersectionFunctor F)
    (hpush : IsPushoutAffineIntersectionFunctor F) :
    QuasiCompact (affineIntersectionToSpec F hopen hpush) := by
  rw [quasiCompact_iff_compactSpace]
  let D := ofAffineIntersectionFunctor F hopen hpush
  haveI : Finite D.openCover.I₀ := by
    change Finite J
    infer_instance
  haveI (i : D.openCover.I₀) : CompactSpace (D.openCover.X i) := by
    change CompactSpace
      (Spec (CommRingCat.of (F.obj (affineIntersectionSingletonIndex i))))
    infer_instance
  exact D.openCover.compactSpace

end

end AlgebraicGeometry.Scheme.GlueData

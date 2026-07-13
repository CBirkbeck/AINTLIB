import ModularCurves.ForMathlib.FinitePresentationPushoutFamily
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Gluing

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

/-- The affine chart indexed by a singleton in a finite-intersection functor. -/
noncomputable abbrev affineIntersectionChart
    (F : Finset J ⥤ CommAlgCat.{u} S) (i : J) : Scheme :=
  Spec (ringObj F (singletonIndex i))

/-- The affine overlap indexed by a pair in a finite-intersection functor. -/
noncomputable abbrev affineIntersectionOverlap
    (F : Finset J ⥤ CommAlgCat.{u} S) (i j : J) : Scheme :=
  Spec (ringObj F (pairIndex i j))

/-- The overlap leg induced by the singleton-to-pair inclusion. -/
noncomputable def affineIntersectionOverlapι
    (F : Finset J ⥤ CommAlgCat.{u} S) (i j : J) :
    affineIntersectionOverlap F i j ⟶ affineIntersectionChart F i :=
  Spec.map (ringMap F (singletonToPair i j))

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

private noncomputable def overlapTransition
    (F : Finset J ⥤ CommAlgCat.{u} S) (i j : J) :
    affineIntersectionOverlap F i j ⟶ affineIntersectionOverlap F j i :=
  Spec.map (ringMap F (pairSwap i j))

private lemma overlapTransition_self (F : Finset J ⥤ CommAlgCat.{u} S) (i : J) :
    overlapTransition F i i = 𝟙 _ := by
  rw [overlapTransition]
  have h : pairSwap i i = 𝟙 _ := Subsingleton.elim _ _
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
noncomputable def ofAffineIntersectionFunctor
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

end

end AlgebraicGeometry.Scheme.GlueData

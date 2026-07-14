import ModularCurves.ForMathlib.FinitePresentationOpenImmersionFamily
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

/-- The singleton index used by an affine finite-intersection functor. -/
noncomputable abbrev affineIntersectionSingletonIndex (i : J) : Finset J :=
  singletonIndex i

/-- The pair index used by an affine finite-intersection functor. -/
noncomputable abbrev affineIntersectionPairIndex (i j : J) : Finset J :=
  pairIndex i j

/-- The canonical inclusion from a singleton index to a pair index. -/
noncomputable abbrev affineIntersectionSingletonToPair (i j : J) :
    affineIntersectionSingletonIndex i ⟶ affineIntersectionPairIndex i j :=
  singletonToPair i j

/-- The canonical index map interchanging an ordered pair. -/
noncomputable abbrev affineIntersectionPairSwap (i j : J) :
    affineIntersectionPairIndex j i ⟶ affineIntersectionPairIndex i j :=
  pairSwap i j

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

section Spread

variable {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
  {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
  {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
  [Algebra R S] {uS : ∀ i, 𝒮 i →ₐ[R] S}
  {F : Finset J ⥤ CommAlgCat.{u} S}
  {H : Algebra.IsFilteredAlgColimit R 𝒮 t S uS}

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

end

end AlgebraicGeometry.Scheme.GlueData

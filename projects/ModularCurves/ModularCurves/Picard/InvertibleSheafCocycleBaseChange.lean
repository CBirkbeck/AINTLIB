import ModularCurves.Picard.AffineIntersectionUnitCocycleFiniteStage

/-!
# Base change of finite-stage affine-intersection cocycles

This file compares finite-stage affine-intersection unit cocycles with their images over
the filtered-colimit base and synchronizes cocycle descent with the affine gluing conditions.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Mapping every transition unit through its stage-to-colimit homomorphism sends a
finite-stage affine-intersection cocycle to the original affine-intersection functor. -/
noncomputable def AffineIntersectionUnitCocycle.mapToColimit
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor) :
    AffineIntersectionUnitCocycle G where
  transition i j :=
    Units.map ((M.object
      (Scheme.GlueData.affineIntersectionPairIndex i j)).stageToColimit H
        ⟨M.stage, M.le_stage
          (Scheme.GlueData.affineIntersectionPairIndex i j)⟩).toMonoidHom
      (cM.transition i j)
  cocycle i j k := by
    have hc := cM.cocycle i j k
    simp only [M.toFunctor_map_hom] at hc
    rw [← M.map_unit_colimit
      (Scheme.GlueData.affineIntersectionPairToTripleLeft i j k)
      (cM.transition i j)]
    rw [← M.map_unit_colimit
      (Scheme.GlueData.affineIntersectionPairToTripleMiddle i j k)
      (cM.transition j k)]
    rw [← M.map_unit_colimit
      (Scheme.GlueData.affineIntersectionPairToTripleRight i j k)
      (cM.transition i k)]
    rw [← map_mul]
    exact congrArg
      (Units.map ((M.object
        (Scheme.GlueData.affineIntersectionTripleIndex i j k)).stageToColimit H
          ⟨M.stage, M.le_stage
            (Scheme.GlueData.affineIntersectionTripleIndex i j k)⟩).toMonoidHom) hc

/-- Moving a finite-stage cocycle to a later stage does not change the colimit image of
any transition unit. -/
theorem AffineIntersectionUnitCocycle.mapToColimit_mapToStage_transition
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    {q : ι} (hMq : M.stage ≤ q) (i j : J) :
    (AffineIntersectionUnitCocycle.mapToColimit (M.mapToStage hMq)
        (AffineIntersectionUnitCocycle.mapToStage M cM hMq)).transition i j =
      (AffineIntersectionUnitCocycle.mapToColimit M cM).transition i j := by
  apply Units.ext
  let X := Scheme.GlueData.affineIntersectionPairIndex i j
  let g :
      ((M.object X).spreadStage (t := t) (M.le_stage X))ˣ :=
    cM.transition i j
  change (M.object X).stageToColimit H
      ⟨q, (M.le_stage X).trans hMq⟩
        ((M.object X).stageTransition H
          (P := ⟨M.stage, M.le_stage X⟩)
          (Q := ⟨q, (M.le_stage X).trans hMq⟩) hMq (g : _)) =
    (M.object X).stageToColimit H ⟨M.stage, M.le_stage X⟩ (g : _)
  exact (M.object X).stageToColimit_stageTransition H
    (M.le_stage X) hMq (g : _)

/-- A cocycle on a finite affine-intersection functor descends to one spread stage where
the affine gluing conditions also hold. -/
theorem AffineIntersectionUnitCocycle.exists_modelWithAffineIntersectionConditions
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} [Finite J] {G : Functor (Finset J) (CommAlgCat.{u} A)}
    (c : AffineIntersectionUnitCocycle G)
    (H : Algebra.IsFilteredAlgColimit R Sstage t A uA)
    (M : Algebra.SpreadData.FunctorModel G H)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G) :
    ∃ (M' : Algebra.SpreadData.FunctorModel G H)
      (_ : Scheme.GlueData.IsOpenAffineIntersectionFunctor M'.toFunctor)
      (_ : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M'.toFunctor)
      (cM' : AffineIntersectionUnitCocycle M'.toFunctor),
      ∀ i j, (AffineIntersectionUnitCocycle.mapToColimit M' cM').transition i j =
        c.transition i j := by
  obtain ⟨q, hMq, r, hqr, cMr, hcMr⟩ := c.exists_modelAtLaterStage H M
  let Mr := (M.mapToStage hMq).mapToStage hqr
  obtain ⟨s, hrs, hopenMs, hpushMs⟩ :=
    Mr.exists_affineIntersectionConditionsAtLaterStage hopenG hpushG
  let Ms := Mr.mapToStage hrs
  let cMs := AffineIntersectionUnitCocycle.mapToStage Mr cMr hrs
  refine ⟨Ms, hopenMs, hpushMs, cMs, fun i j => ?_⟩
  calc
    (AffineIntersectionUnitCocycle.mapToColimit Ms cMs).transition i j =
        (AffineIntersectionUnitCocycle.mapToColimit Mr cMr).transition i j :=
      AffineIntersectionUnitCocycle.mapToColimit_mapToStage_transition
        Mr cMr hrs i j
    _ = c.transition i j := hcMr i j

/-- A cocycle on a separated finite affine-intersection functor descends to one stage
where the open, pushout, and separatedness conditions all hold. -/
theorem AffineIntersectionUnitCocycle.exists_modelWithAffineIntersectionConditionsAndSeparated
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} [Finite J] {G : Functor (Finset J) (CommAlgCat.{u} A)}
    (c : AffineIntersectionUnitCocycle G)
    (H : Algebra.IsFilteredAlgColimit R Sstage t A uA)
    (M : Algebra.SpreadData.FunctorModel G H)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hsepG : Scheme.GlueData.IsSeparatedAffineIntersectionFunctor G) :
    ∃ (M' : Algebra.SpreadData.FunctorModel G H)
      (_ : Scheme.GlueData.IsOpenAffineIntersectionFunctor M'.toFunctor)
      (_ : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M'.toFunctor)
      (_ : Scheme.GlueData.IsSeparatedAffineIntersectionFunctor M'.toFunctor)
      (cM' : AffineIntersectionUnitCocycle M'.toFunctor),
      ∀ i j, (AffineIntersectionUnitCocycle.mapToColimit M' cM').transition i j =
        c.transition i j := by
  obtain ⟨q, hMq, r, hqr, cMr, hcMr⟩ := c.exists_modelAtLaterStage H M
  let Mr := (M.mapToStage hMq).mapToStage hqr
  obtain ⟨s, hrs, hopenMs, hpushMs, hsepMs⟩ :=
    Mr.exists_affineIntersectionConditionsAndSeparatedAtLaterStage hopenG hpushG hsepG
  let Ms := Mr.mapToStage hrs
  let cMs := AffineIntersectionUnitCocycle.mapToStage Mr cMr hrs
  refine ⟨Ms, hopenMs, hpushMs, hsepMs, cMs, fun i j => ?_⟩
  calc
    (AffineIntersectionUnitCocycle.mapToColimit Ms cMs).transition i j =
        (AffineIntersectionUnitCocycle.mapToColimit Mr cMr).transition i j :=
      AffineIntersectionUnitCocycle.mapToColimit_mapToStage_transition
        Mr cMr hrs i j
    _ = c.transition i j := hcMr i j

end

end AlgebraicGeometry.Scheme.Modules

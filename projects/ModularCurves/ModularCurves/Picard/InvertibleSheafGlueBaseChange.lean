import ModularCurves.Picard.InvertibleSheafGlueEffectivity

/-!
# Base change of affine-intersection line-bundle descent

This file compares the concrete Cech-glued invertible sheaf attached to a finite-stage
unit cocycle with its pullback to the filtered-colimit base.
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

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

/-- The local affine base-change map sends a finite-stage overlap transition section
to the overlap transition section of the colimit cocycle. -/
theorem AffineIntersectionUnitCocycle.mapToColimit_overlapTransitionSection
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor) (i j : J) :
    letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let q :=
      (M.baseChangeSpecIso
          (Scheme.GlueData.affineIntersectionPairIndex i j)).inv ≫
        pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A)))
          (Spec.map (CommRingCat.ofHom
            (algebraMap (Sstage M.stage)
              (M.toFunctor.obj
                (Scheme.GlueData.affineIntersectionPairIndex i j)))))
    Units.map q.appTop.hom.toMonoidHom (cM.overlapTransitionSection i j) =
      (AffineIntersectionUnitCocycle.mapToColimit M cM).overlapTransitionSection i j := by
  classical
  letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
  let X := Scheme.GlueData.affineIntersectionPairIndex i j
  let f := CommRingCat.ofHom
    ((M.baseChangeIso.app X).hom.hom.toRingHom.comp
      (Algebra.TensorProduct.includeRight
        (R := Sstage M.stage) (A := A)
        (B := M.toFunctor.obj X)).toRingHom)
  rw [M.baseChangeSpecIso_inv_snd X]
  apply Units.ext
  have hnat := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality f) (cM.transition i j : M.toFunctor.obj X)
  change
    (Spec.map f).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (M.toFunctor.obj X))).inv.hom
          (cM.transition i j : M.toFunctor.obj X)) =
      (Scheme.ΓSpecIso (CommRingCat.of (G.obj X))).inv.hom
        ((M.object X).stageToColimit H ⟨M.stage, M.le_stage X⟩
          (cM.transition i j : M.toFunctor.obj X))
  have hnat' :
      (Spec.map f).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of (M.toFunctor.obj X))).inv.hom
            (cM.transition i j : M.toFunctor.obj X)) =
        (Scheme.ΓSpecIso (CommRingCat.of (G.obj X))).inv.hom
          (f.hom (cM.transition i j : M.toFunctor.obj X)) := by
    simpa only [CommRingCat.comp_apply, ConcreteCategory.comp_apply] using hnat.symm
  rw [hnat']
  congr 1
  exact (M.object X).baseChangeColimEquiv_tmul (M.le_stage X) H
    (cM.transition i j : M.toFunctor.obj X)

/-- Pulling back the scalar overlap transition of a finite-stage cocycle gives the
scalar overlap transition of its colimit cocycle. -/
theorem AffineIntersectionUnitCocycle.mapToColimit_overlapTransitionIso
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor) (i j : J) :
    letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let q :=
      (M.baseChangeSpecIso
          (Scheme.GlueData.affineIntersectionPairIndex i j)).inv ≫
        pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A)))
          (Spec.map (CommRingCat.ofHom
            (algebraMap (Sstage M.stage)
              (M.toFunctor.obj
                (Scheme.GlueData.affineIntersectionPairIndex i j)))))
    (pullbackUnitIso q).inv ≫
        (pullback q).map (cM.overlapTransitionIso i j).hom ≫
        (pullbackUnitIso q).hom =
      ((AffineIntersectionUnitCocycle.mapToColimit M cM).overlapTransitionIso i j).hom := by
  classical
  letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
  dsimp only
  rw [AffineIntersectionUnitCocycle.overlapTransitionIso,
    ModularCurves.unitAutomorphismOfTopUnit_hom,
    ModularCurves.pullback_unitEndomorphismOfTopSection]
  change ModularCurves.unitEndomorphismOfTopSection
      (((M.baseChangeSpecIso
          (Scheme.GlueData.affineIntersectionPairIndex i j)).inv ≫
        pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A)))
          (Spec.map (CommRingCat.ofHom
            (algebraMap (Sstage M.stage)
              (M.toFunctor.obj
                (Scheme.GlueData.affineIntersectionPairIndex i j)))))).appTop.hom
        (cM.overlapTransitionSection i j : _)) =
    ModularCurves.unitEndomorphismOfTopSection
      ((AffineIntersectionUnitCocycle.mapToColimit M cM).overlapTransitionSection i j : _)
  have h := congrArg Units.val
    (AffineIntersectionUnitCocycle.mapToColimit_overlapTransitionSection M cM i j)
  exact congrArg ModularCurves.unitEndomorphismOfTopSection h

/-- The pullback of a finite-stage glued module has its canonical trivialization on every
base-changed singleton chart. -/
noncomputable def AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i : J) :
    letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
    let g := M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM
    (pullback (DG.ι i)).obj
        ((pullback g).obj (cM.gluedModule hopenM hpushM)) ≅ unitObj (DG.U i) := by
  classical
  letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
  let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
  let DM := Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopenM hpushM
  let g := M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM
  let chartMap : DG.U i ⟶ DM.U i :=
    (M.baseChangeSpecIso
        (Scheme.GlueData.affineIntersectionSingletonIndex i)).inv ≫
      pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A)))
        (Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor i)
  let h : DG.ι i ≫ g = chartMap ≫ DM.ι i :=
    M.affineIntersectionGluedBaseChange_ι hopenG hpushG hopenM hpushM i
  exact pullbackSquareTrivialization (DG.ι i) g chartMap (DM.ι i) h
    (cM.gluedModule hopenM hpushM) (cM.gluedModuleLocalIso hopenM hpushM i)

private theorem normalized_conjugation_left
    {C : Type u} [Category C] {P B D E U V : C}
    {x : P ⟶ U} {U₁ : U ≅ E} {U₂ : V ≅ E} {transition : U ⟶ V}
    {L : P ≅ B} {K : B ⟶ D} {T : D ≅ E} {scalar : E ⟶ E}
    (hnormalized : x ≫ U₁.hom = L.hom ≫ K ≫ T.hom)
    (htransition : U₁.inv ≫ transition ≫ U₂.hom = scalar) :
    (x ≫ transition) ≫ U₂.hom = (L.hom ≫ K ≫ T.hom) ≫ scalar := by
  have htransition' : transition ≫ U₂.hom = U₁.hom ≫ scalar := by
    apply (cancel_epi U₁.inv).1
    calc
      U₁.inv ≫ (transition ≫ U₂.hom) = scalar := htransition
      _ = U₁.inv ≫ (U₁.hom ≫ scalar) := by
        simp only [Iso.inv_hom_id_assoc]
  calc
    (x ≫ transition) ≫ U₂.hom = x ≫ (transition ≫ U₂.hom) :=
      Category.assoc _ _ _
    _ = x ≫ (U₁.hom ≫ scalar) := congrArg (x ≫ ·) htransition'
    _ = (x ≫ U₁.hom) ≫ scalar := (Category.assoc _ _ _).symm
    _ = (L.hom ≫ K ≫ T.hom) ≫ scalar := congrArg (· ≫ scalar) hnormalized

private def normalized_conjugation_uncancelled
    {C : Type u} [Category C] {P Q B D E : C}
    (L₁ : P ≅ B) (L₂ : Q ≅ B) (K : B ⟶ D) (T₂ : D ≅ E) : P ⟶ E :=
  (L₁.hom ≫ L₂.inv) ≫ (L₂.hom ≫ K ≫ T₂.hom)

private theorem normalized_conjugation_right_head
    {C : Type u} [Category C] {P Q B D E V : C}
    {x : Q ⟶ V} {U : V ≅ E} {L₁ : P ≅ B} {L₂ : Q ≅ B}
    {K : B ⟶ D} {T₂ : D ≅ E}
    (hnormalized : x ≫ U.hom = L₂.hom ≫ K ≫ T₂.hom) :
    ((L₁.hom ≫ L₂.inv) ≫ x) ≫ U.hom =
      normalized_conjugation_uncancelled L₁ L₂ K T₂ := by
  change ((L₁.hom ≫ L₂.inv) ≫ x) ≫ U.hom =
    (L₁.hom ≫ L₂.inv) ≫ (L₂.hom ≫ K ≫ T₂.hom)
  calc
    ((L₁.hom ≫ L₂.inv) ≫ x) ≫ U.hom =
        (L₁.hom ≫ L₂.inv) ≫ (x ≫ U.hom) := Category.assoc _ _ _
    _ = (L₁.hom ≫ L₂.inv) ≫ (L₂.hom ≫ K ≫ T₂.hom) :=
      congrArg ((L₁.hom ≫ L₂.inv) ≫ ·) hnormalized

private theorem normalized_conjugation_right_cancel
    {C : Type u} [Category C] {P Q B D E : C}
    {L₁ : P ≅ B} {L₂ : Q ≅ B} {K : B ⟶ D} {T₂ : D ≅ E} :
    normalized_conjugation_uncancelled L₁ L₂ K T₂ =
      L₁.hom ≫ K ≫ T₂.hom := by
  change (L₁.hom ≫ L₂.inv) ≫ (L₂.hom ≫ K ≫ T₂.hom) =
    L₁.hom ≫ K ≫ T₂.hom
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem normalized_conjugation_right_scalar
    {C : Type u} [Category C] {P B D E : C}
    {L₁ : P ≅ B} {K : B ⟶ D} {T₁ T₂ : D ≅ E}
    {scalar : E ⟶ E} (hscalar : T₁.inv ≫ T₂.hom = scalar) :
    L₁.hom ≫ K ≫ T₂.hom = (L₁.hom ≫ K ≫ T₁.hom) ≫ scalar := by
  rw [← hscalar]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]



private theorem eq_of_left_reverse {α : Sort u} {a b e : α}
    (hab : a = b) (heb : e = b) : a = e :=
  hab.trans heb.symm



private theorem common_target_of_commuting_square
    {C : Type u} [Category C] {T X Y W Z : C}
    {p : T ⟶ X} {i : X ⟶ Y} {g : Y ⟶ Z} {chart : X ⟶ W} {j : W ⟶ Z}
    {s : T ⟶ Y} {q : T ⟶ Z} (hp : p ≫ i = s) (hchart : i ≫ g = chart ≫ j)
    (hq : (p ≫ chart) ≫ j = q) : s ≫ g = q := by
  calc
    s ≫ g = (p ≫ i) ≫ g := congrArg (· ≫ g) hp.symm
    _ = p ≫ (i ≫ g) := Category.assoc _ _ _
    _ = p ≫ (chart ≫ j) := congrArg (p ≫ ·) hchart
    _ = (p ≫ chart) ≫ j := (Category.assoc _ _ _).symm
    _ = q := hq

private theorem map_to_common_of_commuting_square
    {C : Type u} [Category C] {T X Y W Z : C}
    {p : T ⟶ X} {i : X ⟶ Y} {g : Y ⟶ Z} {chart : X ⟶ W} {j : W ⟶ Z}
    {s : T ⟶ Y} {q : T ⟶ Z} (hp : p ≫ i = s) (hchart : i ≫ g = chart ≫ j)
    (hcommon : s ≫ g = q) : (p ≫ chart) ≫ j = q := by
  calc
    (p ≫ chart) ≫ j = p ≫ (chart ≫ j) := Category.assoc _ _ _
    _ = p ≫ (i ≫ g) := congrArg (p ≫ ·) hchart.symm
    _ = (p ≫ i) ≫ g := (Category.assoc _ _ _).symm
    _ = s ≫ g := congrArg (· ≫ g) hp
    _ = q := hcommon


private theorem AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalize
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (k : J) :
    letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
    let DM := Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopenM hpushM
    let g := M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM
    let N := cM.gluedModule hopenM hpushM
    let chartMap : DG.U k ⟶ DM.U k :=
      (M.baseChangeSpecIso
          (Scheme.GlueData.affineIntersectionSingletonIndex k)).inv ≫
        pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A)))
          (Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor k)
    ∀ {T : Scheme.{u}} (p : T ⟶ DG.U k) (s : T ⟶ DG.glued)
      (hp : p ≫ DG.ι k = s) (q : T ⟶ DM.glued)
      (hCommon : s ≫ g = q) (hq : (p ≫ chartMap) ≫ DM.ι k = q),
      (pullback p).map
            (AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization
              M cM hopenG hpushG hopenM hpushM k).hom ≫
          (pullbackUnitIso p).hom =
        ((((pullbackComp p (DG.ι k)).app ((pullback g).obj N)) ≪≫
            ((pullbackCongr hp).app ((pullback g).obj N))).hom) ≫
          ((((pullbackComp s g).app N) ≪≫
            ((pullbackCongr hCommon).app N)).hom) ≫
          (pullbackCompositeTrivialization (p ≫ chartMap) (DM.ι k) q hq N
            (cM.gluedModuleLocalIso hopenM hpushM k)).hom := by
  classical
  letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
  dsimp only
  intro T p s hp q hCommon hq
  let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
  let DM := Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopenM hpushM
  let g := M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM
  let N := cM.gluedModule hopenM hpushM
  let chartMap : DG.U k ⟶ DM.U k :=
    (M.baseChangeSpecIso
        (Scheme.GlueData.affineIntersectionSingletonIndex k)).inv ≫
      pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A)))
        (Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor k)
  have hChart : DG.ι k ≫ g = chartMap ≫ DM.ι k :=
    M.affineIntersectionGluedBaseChange_ι hopenG hpushG hopenM hpushM k
  have hSource : p ≫ (DG.ι k ≫ g) = s ≫ g := by
    rw [← Category.assoc, hp]
  have hnormalized := pullbackSquareTrivialization_precomp_normalize
    p (DG.ι k) g s hp chartMap (DM.ι k) q hChart hSource hCommon hq
    N (cM.gluedModuleLocalIso hopenM hpushM k)
  have e_eq :
      AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization
          M cM hopenG hpushG hopenM hpushM k =
        pullbackSquareTrivialization (DG.ι k) g chartMap (DM.ι k) hChart N
          (cM.gluedModuleLocalIso hopenM hpushM k) := by
    rfl
  rw [e_eq]
  exact hnormalized

private theorem AffineIntersectionUnitCocycle.baseChangeGluedModuleTail_transition
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : J) :
    letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
    let DM := Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopenM hpushM
    let base := Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A))
    let chartMap (k : J) : DG.U k ⟶ DM.U k :=
      (M.baseChangeSpecIso
          (Scheme.GlueData.affineIntersectionSingletonIndex k)).inv ≫
        pullback.snd base
          (Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor k)
    let leftMap : DG.V (i, j) ⟶ DM.U i := DG.f i j ≫ chartMap i
    let rightMap : DG.V (i, j) ⟶ DM.U j :=
      (DG.t i j ≫ DG.f j i) ≫ chartMap j
    let q : DG.V (i, j) ⟶ DM.glued := leftMap ≫ DM.ι i
    ∀ (hqRight : rightMap ≫ DM.ι j = q),
    (pullbackCompositeTrivialization leftMap (DM.ι i) q rfl
          (cM.gluedModule hopenM hpushM)
          (cM.gluedModuleLocalIso hopenM hpushM i)).inv ≫
        (pullbackCompositeTrivialization rightMap (DM.ι j) q hqRight
          (cM.gluedModule hopenM hpushM)
          (cM.gluedModuleLocalIso hopenM hpushM j)).hom =
      ((AffineIntersectionUnitCocycle.mapToColimit M cM).overlapTransitionIso i j).hom := by
  classical
  letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
  dsimp only
  intro hqRight
  let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
  let DM := Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopenM hpushM
  let base := Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A))
  let chartMap (k : J) : DG.U k ⟶ DM.U k :=
    (M.baseChangeSpecIso
        (Scheme.GlueData.affineIntersectionSingletonIndex k)).inv ≫
      pullback.snd base
        (Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor k)
  let overlapMap (k l : J) : DG.V (k, l) ⟶ DM.V (k, l) :=
    (M.baseChangeSpecIso
        (Scheme.GlueData.affineIntersectionPairIndex k l)).inv ≫
      pullback.snd base
        (Spec.map (CommRingCat.ofHom
          (algebraMap (Sstage M.stage)
            (M.toFunctor.obj
              (Scheme.GlueData.affineIntersectionPairIndex k l)))))
  let leftMap : DG.V (i, j) ⟶ DM.U i := DG.f i j ≫ chartMap i
  let rightMap : DG.V (i, j) ⟶ DM.U j :=
    (DG.t i j ≫ DG.f j i) ≫ chartMap j
  have hleft : overlapMap i j ≫ DM.f i j = leftMap := by
    exact (M.baseChangeSpecIso_inv_affineIntersectionOverlapι i j).symm
  have hright : overlapMap i j ≫ (DM.t i j ≫ DM.f j i) = rightMap := by
    have ht := M.baseChangeSpecIso_inv_affineIntersectionTransition
      hopenG hpushG hopenM hpushM i j
    have hj := M.baseChangeSpecIso_inv_affineIntersectionOverlapι j i
    have ht' : overlapMap i j ≫ DM.t i j = DG.t i j ≫ overlapMap j i := by
      dsimp only [overlapMap, DG, DM]
      simpa only [Category.assoc] using ht
    have hj' : overlapMap j i ≫ DM.f j i = DG.f j i ≫ chartMap j := by
      dsimp only [overlapMap, chartMap, DG, DM]
      simpa only [Category.assoc] using hj.symm
    calc
      overlapMap i j ≫ (DM.t i j ≫ DM.f j i) =
          (overlapMap i j ≫ DM.t i j) ≫ DM.f j i :=
        (Category.assoc _ _ _).symm
      _ = (DG.t i j ≫ overlapMap j i) ≫ DM.f j i :=
        congrArg (· ≫ DM.f j i) ht'
      _ = DG.t i j ≫ (overlapMap j i ≫ DM.f j i) := Category.assoc _ _ _
      _ = DG.t i j ≫ (DG.f j i ≫ chartMap j) :=
        congrArg (DG.t i j ≫ ·) hj'
      _ = rightMap := (Category.assoc _ _ _).symm
  let q : DG.V (i, j) ⟶ DM.glued := leftMap ≫ DM.ι i
  have hqLeft : leftMap ≫ DM.ι i = q := rfl
  have htransition := cM.gluedModuleCompositeTrivialization_transition
    hopenM hpushM i j q (overlapMap i j) leftMap rightMap
    hqLeft hqRight hleft hright
  calc
    _ = cM.chartTransitionIsoCoordinatePullback hopenM hpushM i j
          (overlapMap i j) := htransition
    _ = (pullbackUnitIso (overlapMap i j)).inv ≫
          (pullback (overlapMap i j)).map (cM.overlapTransitionIso i j).hom ≫
          (pullbackUnitIso (overlapMap i j)).hom :=
      cM.chartTransitionIsoCoordinatePullback_eq hopenM hpushM i j (overlapMap i j)
    _ = ((AffineIntersectionUnitCocycle.mapToColimit M cM).overlapTransitionIso i j).hom :=
      AffineIntersectionUnitCocycle.mapToColimit_overlapTransitionIso M cM i j


private theorem AffineIntersectionUnitCocycle.baseChangeGluedModuleNormalizedTail_transition
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : J) :
    letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
    let DM := Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopenM hpushM
    let base := Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A))
    let chartMap (k : J) : DG.U k ⟶ DM.U k :=
      (M.baseChangeSpecIso
          (Scheme.GlueData.affineIntersectionSingletonIndex k)).inv ≫
        pullback.snd base
          (Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor k)
    let leftMap : DG.V (i, j) ⟶ DM.U i := DG.f i j ≫ chartMap i
    let rightMap : DG.V (i, j) ⟶ DM.U j :=
      (DG.t i j ≫ DG.f j i) ≫ chartMap j
    let q : DG.V (i, j) ⟶ DM.glued := leftMap ≫ DM.ι i
    let hqLeft : leftMap ≫ DM.ι i = q := rfl
    ∀ (hqRight : rightMap ≫ DM.ι j = q),
    let T₁ := pullbackCompositeTrivialization leftMap (DM.ι i) q hqLeft
      (cM.gluedModule hopenM hpushM)
      (cM.gluedModuleLocalIso hopenM hpushM i)
    let T₂ := pullbackCompositeTrivialization rightMap (DM.ι j) q hqRight
      (cM.gluedModule hopenM hpushM)
      (cM.gluedModuleLocalIso hopenM hpushM j)
    let scalar :=
      ((AffineIntersectionUnitCocycle.mapToColimit M cM).overlapTransitionIso i j).hom
    T₁.inv ≫ T₂.hom = scalar := by
  classical
  letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
  dsimp only
  intro hqRight
  exact AffineIntersectionUnitCocycle.baseChangeGluedModuleTail_transition
    M cM hopenG hpushG hopenM hpushM i j hqRight

private theorem AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_left
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : J) :
    letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
    let DM := Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopenM hpushM
    let g := M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM
    let N := cM.gluedModule hopenM hpushM
    let base := Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A))
    let chartMap (k : J) : DG.U k ⟶ DM.U k :=
      (M.baseChangeSpecIso
          (Scheme.GlueData.affineIntersectionSingletonIndex k)).inv ≫
        pullback.snd base
          (Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor k)
    let pLeft : DG.V (i, j) ⟶ DG.U i := DG.f i j
    let pRight : DG.V (i, j) ⟶ DG.U j := DG.t i j ≫ DG.f j i
    let s : DG.V (i, j) ⟶ DG.glued := pLeft ≫ DG.ι i
    let q : DG.V (i, j) ⟶ DM.glued := (pLeft ≫ chartMap i) ≫ DM.ι i
    let hpLeft : pLeft ≫ DG.ι i = s := rfl
    let hqLeft : (pLeft ≫ chartMap i) ≫ DM.ι i = q := rfl
    let L₁ := ((pullbackComp pLeft (DG.ι i)).app ((pullback g).obj N)) ≪≫
      ((pullbackCongr hpLeft).app ((pullback g).obj N))
    ∀ (hCommon : s ≫ g = q),
    let K := (((pullbackComp s g).app N) ≪≫ ((pullbackCongr hCommon).app N)).hom
    let T₁ := pullbackCompositeTrivialization (pLeft ≫ chartMap i) (DM.ι i) q hqLeft
      N (cM.gluedModuleLocalIso hopenM hpushM i)
    let e := AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization
      M cM hopenG hpushG hopenM hpushM
    let scalar :=
      ((AffineIntersectionUnitCocycle.mapToColimit M cM).overlapTransitionIso i j).hom
    ((pullback pLeft).map (e i).hom ≫
        ((AffineIntersectionUnitCocycle.mapToColimit M cM).chartTransitionIso
          hopenG hpushG i j).hom) ≫ (pullbackUnitIso pRight).hom =
      (L₁.hom ≫ K ≫ T₁.hom) ≫ scalar := by
  classical
  intro DG DM g N base chartMap pLeft pRight s q hpLeft hqLeft L₁ hCommon K T₁ e scalar
  have hnormalized :=
    AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalize
      M cM hopenG hpushG hopenM hpushM i pLeft s hpLeft q hCommon hqLeft
  have htransition :=
    (AffineIntersectionUnitCocycle.mapToColimit M cM).chartTransitionIso_toUnit
      hopenG hpushG i j
  exact normalized_conjugation_left hnormalized htransition

private theorem AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_right_chart
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : J) :
    letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
    let DM := Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopenM hpushM
    let g := M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM
    let base := Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A))
    let chartMap (k : J) : DG.U k ⟶ DM.U k :=
      (M.baseChangeSpecIso
          (Scheme.GlueData.affineIntersectionSingletonIndex k)).inv ≫
        pullback.snd base
          (Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor k)
    let pLeft : DG.V (i, j) ⟶ DG.U i := DG.f i j
    let pRight : DG.V (i, j) ⟶ DG.U j := DG.t i j ≫ DG.f j i
    let s : DG.V (i, j) ⟶ DG.glued := pLeft ≫ DG.ι i
    let q : DG.V (i, j) ⟶ DM.glued := (pLeft ≫ chartMap i) ≫ DM.ι i
    let hpRight : pRight ≫ DG.ι j = s := DG.glue_condition i j
    ∀ (hqRight : (pRight ≫ chartMap j) ≫ DM.ι j = q)
      (hCommon : s ≫ g = q),
      type_of%
        (AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalize
          M cM hopenG hpushG hopenM hpushM j pRight s hpRight q hCommon hqRight) := by
  classical
  intro DG DM g base chartMap pLeft pRight s q hpRight hqRight hCommon
  exact AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalize
    M cM hopenG hpushG hopenM hpushM j pRight s hpRight q hCommon hqRight

private theorem AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_right_head
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : J) :
    letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
    let DM := Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopenM hpushM
    let g := M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM
    let N := cM.gluedModule hopenM hpushM
    let base := Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A))
    let chartMap (k : J) : DG.U k ⟶ DM.U k :=
      (M.baseChangeSpecIso
          (Scheme.GlueData.affineIntersectionSingletonIndex k)).inv ≫
        pullback.snd base
          (Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor k)
    let pLeft : DG.V (i, j) ⟶ DG.U i := DG.f i j
    let pRight : DG.V (i, j) ⟶ DG.U j := DG.t i j ≫ DG.f j i
    let s : DG.V (i, j) ⟶ DG.glued := pLeft ≫ DG.ι i
    let q : DG.V (i, j) ⟶ DM.glued := (pLeft ≫ chartMap i) ≫ DM.ι i
    let hpLeft : pLeft ≫ DG.ι i = s := rfl
    let L₁ := ((pullbackComp pLeft (DG.ι i)).app ((pullback g).obj N)) ≪≫
      ((pullbackCongr hpLeft).app ((pullback g).obj N))
    ∀ (hqRight : (pRight ≫ chartMap j) ≫ DM.ι j = q)
      (hCommon : s ≫ g = q),
    type_of%
      (normalized_conjugation_right_head (L₁ := L₁)
        (AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_right_chart
          M cM hopenG hpushG hopenM hpushM i j hqRight hCommon)) := by
  classical
  intro DG DM g N base chartMap pLeft pRight s q hpLeft L₁
    hqRight hCommon
  have hnormalized :=
    AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_right_chart
      M cM hopenG hpushG hopenM hpushM i j hqRight hCommon
  exact normalized_conjugation_right_head (L₁ := L₁) hnormalized

private theorem AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_right_cancel
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : J) :
    letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
    let DM := Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopenM hpushM
    let g := M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM
    let N := cM.gluedModule hopenM hpushM
    let base := Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A))
    let chartMap (k : J) : DG.U k ⟶ DM.U k :=
      (M.baseChangeSpecIso
          (Scheme.GlueData.affineIntersectionSingletonIndex k)).inv ≫
        pullback.snd base
          (Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor k)
    let pLeft : DG.V (i, j) ⟶ DG.U i := DG.f i j
    let pRight : DG.V (i, j) ⟶ DG.U j := DG.t i j ≫ DG.f j i
    let s : DG.V (i, j) ⟶ DG.glued := pLeft ≫ DG.ι i
    let q : DG.V (i, j) ⟶ DM.glued := (pLeft ≫ chartMap i) ≫ DM.ι i
    let hpLeft : pLeft ≫ DG.ι i = s := rfl
    let hpRight : pRight ≫ DG.ι j = s := DG.glue_condition i j
    let L₁ := ((pullbackComp pLeft (DG.ι i)).app ((pullback g).obj N)) ≪≫
      ((pullbackCongr hpLeft).app ((pullback g).obj N))
    let L₂ := ((pullbackComp pRight (DG.ι j)).app ((pullback g).obj N)) ≪≫
      ((pullbackCongr hpRight).app ((pullback g).obj N))
    ∀ (hqRight : (pRight ≫ chartMap j) ≫ DM.ι j = q)
      (hCommon : s ≫ g = q),
    let K := (((pullbackComp s g).app N) ≪≫ ((pullbackCongr hCommon).app N)).hom
    let T₂ := pullbackCompositeTrivialization (pRight ≫ chartMap j) (DM.ι j) q hqRight
      N (cM.gluedModuleLocalIso hopenM hpushM j)
    type_of%
      (normalized_conjugation_right_cancel
        (L₁ := L₁) (L₂ := L₂) (K := K) (T₂ := T₂)) := by
  classical
  intro DG DM g N base chartMap pLeft pRight s q hpLeft hpRight L₁ L₂
    hqRight hCommon K T₂
  exact normalized_conjugation_right_cancel
    (L₁ := L₁) (L₂ := L₂) (K := K) (T₂ := T₂)

private theorem AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_right_scalar
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : J) :
    letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
    let DM := Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopenM hpushM
    let g := M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM
    let N := cM.gluedModule hopenM hpushM
    let base := Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A))
    let chartMap (k : J) : DG.U k ⟶ DM.U k :=
      (M.baseChangeSpecIso
          (Scheme.GlueData.affineIntersectionSingletonIndex k)).inv ≫
        pullback.snd base
          (Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor k)
    let pLeft : DG.V (i, j) ⟶ DG.U i := DG.f i j
    let pRight : DG.V (i, j) ⟶ DG.U j := DG.t i j ≫ DG.f j i
    let s : DG.V (i, j) ⟶ DG.glued := pLeft ≫ DG.ι i
    let q : DG.V (i, j) ⟶ DM.glued := (pLeft ≫ chartMap i) ≫ DM.ι i
    let L₁ := ((pullbackComp pLeft (DG.ι i)).app ((pullback g).obj N)) ≪≫
      ((pullbackCongr rfl).app ((pullback g).obj N))
    ∀ (hqRight : (pRight ≫ chartMap j) ≫ DM.ι j = q)
      (hCommon : s ≫ g = q),
    let K := (((pullbackComp s g).app N) ≪≫ ((pullbackCongr hCommon).app N)).hom
    type_of%
      (normalized_conjugation_right_scalar (L₁ := L₁) (K := K)
        (AffineIntersectionUnitCocycle.baseChangeGluedModuleNormalizedTail_transition
          M cM hopenG hpushG hopenM hpushM i j hqRight)) := by
  classical
  intro DG DM g N base chartMap pLeft pRight s q L₁
    hqRight hCommon K
  exact normalized_conjugation_right_scalar (L₁ := L₁) (K := K)
    (AffineIntersectionUnitCocycle.baseChangeGluedModuleTail_transition
      M cM hopenG hpushG hopenM hpushM i j hqRight)

private theorem AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_left_to_tail
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : J) :
    type_of%
      (fun hqRight hCommon =>
        eq_of_left_reverse
          (AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_left
            M cM hopenG hpushG hopenM hpushM i j hCommon)
          (AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_right_scalar
            M cM hopenG hpushG hopenM hpushM i j hqRight hCommon)) := by
  classical
  exact fun hqRight hCommon => eq_of_left_reverse
    (AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_left
      M cM hopenG hpushG hopenM hpushM i j hCommon)
    (AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_right_scalar
      M cM hopenG hpushG hopenM hpushM i j hqRight hCommon)

private theorem AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_tail_to_uncancelled
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : J) :
    type_of%
      (fun hqRight hCommon =>
        (AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_right_cancel
          M cM hopenG hpushG hopenM hpushM i j hqRight hCommon).symm) := by
  classical
  exact fun hqRight hCommon =>
    (AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_right_cancel
      M cM hopenG hpushG hopenM hpushM i j hqRight hCommon).symm

private theorem AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_uncancelled_to_right
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : J) :
    type_of%
      (fun hqRight hCommon =>
        (AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_right_head
          M cM hopenG hpushG hopenM hpushM i j hqRight hCommon).symm) := by
  classical
  exact fun hqRight hCommon =>
    (AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_right_head
      M cM hopenG hpushG hopenM hpushM i j hqRight hCommon).symm

private theorem AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_left_to_uncancelled
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : J) :
    type_of%
      (fun hqRight hCommon =>
        (AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_left_to_tail
          M cM hopenG hpushG hopenM hpushM i j hqRight hCommon).trans
        (AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_tail_to_uncancelled
          M cM hopenG hpushG hopenM hpushM i j hqRight hCommon)) := by
  classical
  exact fun hqRight hCommon =>
    (AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_left_to_tail
      M cM hopenG hpushG hopenM hpushM i j hqRight hCommon).trans
    (AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_tail_to_uncancelled
      M cM hopenG hpushG hopenM hpushM i j hqRight hCommon)


private noncomputable def AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivializationCompatibilityLeft
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : J) := by
  classical
  letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
  let sq := affineIntersectionChartChosenPullback hopenG hpushG
  let e := AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization
    M cM hopenG hpushG hopenM hpushM
  exact
    (pullbackPseudofunctor.map (sq i j).p₁.op.toLoc).toFunctor.map (e i).hom ≫
      ((AffineIntersectionUnitCocycle.mapToColimit M cM).chartTransitionIso
        hopenG hpushG i j).hom

private noncomputable def AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivializationCompatibilityRight
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : J) := by
  classical
  letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
  let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
  let sq := affineIntersectionChartChosenPullback hopenG hpushG
  let g := M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM
  let N := (pullback g).obj (cM.gluedModule hopenM hpushM)
  let e := AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization
    M cM hopenG hpushG hopenM hpushM
  exact
    ((((pullbackComp (sq i j).p₁ (DG.ι i)).app N) ≪≫
          ((pullbackCongr (sq i j).hp₁).app N)).hom ≫
        (((pullbackComp (sq i j).p₂ (DG.ι j)).app N) ≪≫
          ((pullbackCongr (sq i j).hp₂).app N)).inv) ≫
      (pullbackPseudofunctor.map (sq i j).p₂.op.toLoc).toFunctor.map (e j).hom


private def AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivializationCompatibleAt
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : J) : Prop :=
  letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
  AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivializationCompatibilityLeft
      M cM hopenG hpushG hopenM hpushM i j =
    AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivializationCompatibilityRight
      M cM hopenG hpushG hopenM hpushM i j



private theorem AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_hCommon
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : J) :
    letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
    let DM := Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopenM hpushM
    let g := M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM
    let base := Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A))
    let chartMap (k : J) : DG.U k ⟶ DM.U k :=
      (M.baseChangeSpecIso
          (Scheme.GlueData.affineIntersectionSingletonIndex k)).inv ≫
        pullback.snd base
          (Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor k)
    let pLeft : DG.V (i, j) ⟶ DG.U i := DG.f i j
    let s : DG.V (i, j) ⟶ DG.glued := pLeft ≫ DG.ι i
    let q : DG.V (i, j) ⟶ DM.glued := (pLeft ≫ chartMap i) ≫ DM.ι i
    s ≫ g = q := by
  classical
  letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
  dsimp only
  let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
  let DM := Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopenM hpushM
  let g := M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM
  let base := Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A))
  let chartMap (k : J) : DG.U k ⟶ DM.U k :=
    (M.baseChangeSpecIso
        (Scheme.GlueData.affineIntersectionSingletonIndex k)).inv ≫
      pullback.snd base
        (Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor k)
  let pLeft : DG.V (i, j) ⟶ DG.U i := DG.f i j
  let s : DG.V (i, j) ⟶ DG.glued := pLeft ≫ DG.ι i
  let q : DG.V (i, j) ⟶ DM.glued := (pLeft ≫ chartMap i) ≫ DM.ι i
  let hpLeft : pLeft ≫ DG.ι i = s := rfl
  let hChart : DG.ι i ≫ g = chartMap i ≫ DM.ι i :=
    M.affineIntersectionGluedBaseChange_ι hopenG hpushG hopenM hpushM i
  let hqLeft : (pLeft ≫ chartMap i) ≫ DM.ι i = q := rfl
  exact common_target_of_commuting_square hpLeft hChart hqLeft

private theorem AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_hqRight
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : J) :
    letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
    let DM := Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopenM hpushM
    let base := Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A))
    let chartMap (k : J) : DG.U k ⟶ DM.U k :=
      (M.baseChangeSpecIso
          (Scheme.GlueData.affineIntersectionSingletonIndex k)).inv ≫
        pullback.snd base
          (Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor k)
    let pLeft : DG.V (i, j) ⟶ DG.U i := DG.f i j
    let pRight : DG.V (i, j) ⟶ DG.U j := DG.t i j ≫ DG.f j i
    let q : DG.V (i, j) ⟶ DM.glued := (pLeft ≫ chartMap i) ≫ DM.ι i
    (pRight ≫ chartMap j) ≫ DM.ι j = q := by
  classical
  letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
  dsimp only
  let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
  let DM := Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopenM hpushM
  let g := M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM
  let base := Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A))
  let chartMap (k : J) : DG.U k ⟶ DM.U k :=
    (M.baseChangeSpecIso
        (Scheme.GlueData.affineIntersectionSingletonIndex k)).inv ≫
      pullback.snd base
        (Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor k)
  let pLeft : DG.V (i, j) ⟶ DG.U i := DG.f i j
  let pRight : DG.V (i, j) ⟶ DG.U j := DG.t i j ≫ DG.f j i
  let s : DG.V (i, j) ⟶ DG.glued := pLeft ≫ DG.ι i
  let q : DG.V (i, j) ⟶ DM.glued := (pLeft ≫ chartMap i) ≫ DM.ι i
  let hpRight : pRight ≫ DG.ι j = s := DG.glue_condition i j
  let hChart : DG.ι j ≫ g = chartMap j ≫ DM.ι j :=
    M.affineIntersectionGluedBaseChange_ι hopenG hpushG hopenM hpushM j
  let hCommon :=
    AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_hCommon
      M hopenG hpushG hopenM hpushM i j
  exact map_to_common_of_commuting_square hpRight hChart hCommon



private theorem AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_left_to_middle_raw
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : J) :
    letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
    let DM := Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopenM hpushM
    let g := M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM
    let base := Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A))
    let chartMap (k : J) : DG.U k ⟶ DM.U k :=
      (M.baseChangeSpecIso
          (Scheme.GlueData.affineIntersectionSingletonIndex k)).inv ≫
        pullback.snd base
          (Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor k)
    let pLeft : DG.V (i, j) ⟶ DG.U i := DG.f i j
    let pRight : DG.V (i, j) ⟶ DG.U j := DG.t i j ≫ DG.f j i
    let s : DG.V (i, j) ⟶ DG.glued := pLeft ≫ DG.ι i
    let q : DG.V (i, j) ⟶ DM.glued := (pLeft ≫ chartMap i) ≫ DM.ι i
    ∀ (hqRight : (pRight ≫ chartMap j) ≫ DM.ι j = q)
      (hCommon : s ≫ g = q),
      type_of%
        (show
          AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivializationCompatibilityLeft
              M cM hopenG hpushG hopenM hpushM i j ≫ (pullbackUnitIso pRight).hom = _ from
          AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_left_to_uncancelled
            M cM hopenG hpushG hopenM hpushM i j hqRight hCommon) := by
  classical
  intro DG DM g base chartMap pLeft pRight s q hqRight hCommon
  exact
    (show
      AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivializationCompatibilityLeft
          M cM hopenG hpushG hopenM hpushM i j ≫ (pullbackUnitIso pRight).hom = _ from
      AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_left_to_uncancelled
        M cM hopenG hpushG hopenM hpushM i j hqRight hCommon)

private theorem AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_middle_to_right_raw
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : J) :
    letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
    let DM := Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopenM hpushM
    let g := M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM
    let base := Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A))
    let chartMap (k : J) : DG.U k ⟶ DM.U k :=
      (M.baseChangeSpecIso
          (Scheme.GlueData.affineIntersectionSingletonIndex k)).inv ≫
        pullback.snd base
          (Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor k)
    let pLeft : DG.V (i, j) ⟶ DG.U i := DG.f i j
    let pRight : DG.V (i, j) ⟶ DG.U j := DG.t i j ≫ DG.f j i
    let s : DG.V (i, j) ⟶ DG.glued := pLeft ≫ DG.ι i
    let q : DG.V (i, j) ⟶ DM.glued := (pLeft ≫ chartMap i) ≫ DM.ι i
    ∀ (hqRight : (pRight ≫ chartMap j) ≫ DM.ι j = q)
      (hCommon : s ≫ g = q),
      type_of%
        (show _ =
          AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivializationCompatibilityRight
              M cM hopenG hpushG hopenM hpushM i j ≫ (pullbackUnitIso pRight).hom from
          AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_uncancelled_to_right
            M cM hopenG hpushG hopenM hpushM i j hqRight hCommon) := by
  classical
  intro DG DM g base chartMap pLeft pRight s q hqRight hCommon
  exact
    (show _ =
      AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivializationCompatibilityRight
          M cM hopenG hpushG hopenM hpushM i j ≫ (pullbackUnitIso pRight).hom from
      AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_normalized_uncancelled_to_right
        M cM hopenG hpushG hopenM hpushM i j hqRight hCommon)

private theorem AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_postcomp_of_commuting
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : J) :
    type_of% (fun hqRight hCommon =>
      (AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_left_to_middle_raw
        M cM hopenG hpushG hopenM hpushM i j hqRight hCommon).trans
      (AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_middle_to_right_raw
        M cM hopenG hpushG hopenM hpushM i j hqRight hCommon)) := by
  classical
  exact fun hqRight hCommon =>
    (AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_left_to_middle_raw
      M cM hopenG hpushG hopenM hpushM i j hqRight hCommon).trans
    (AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_middle_to_right_raw
      M cM hopenG hpushG hopenM hpushM i j hqRight hCommon)

private theorem AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_compatibleAt_of_commuting
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : J) :
    letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
    let DM := Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopenM hpushM
    let g := M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM
    let base := Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A))
    let chartMap (k : J) : DG.U k ⟶ DM.U k :=
      (M.baseChangeSpecIso
          (Scheme.GlueData.affineIntersectionSingletonIndex k)).inv ≫
        pullback.snd base
          (Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor k)
    let pLeft : DG.V (i, j) ⟶ DG.U i := DG.f i j
    let pRight : DG.V (i, j) ⟶ DG.U j := DG.t i j ≫ DG.f j i
    let s : DG.V (i, j) ⟶ DG.glued := pLeft ≫ DG.ι i
    let q : DG.V (i, j) ⟶ DM.glued := (pLeft ≫ chartMap i) ≫ DM.ι i
    ∀ (_ : (pRight ≫ chartMap j) ≫ DM.ι j = q)
      (_ : s ≫ g = q),
      AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivializationCompatibleAt
        M cM hopenG hpushG hopenM hpushM i j := by
  classical
  intro DG DM g base chartMap pLeft pRight s q hqRight hCommon
  dsimp only [AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivializationCompatibleAt]
  apply (cancel_mono (pullbackUnitIso pRight).hom).1
  exact
    AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_postcomp_of_commuting
      M cM hopenG hpushG hopenM hpushM i j hqRight hCommon

private theorem AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_compatibleAt
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : J) :
    AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivializationCompatibleAt
      M cM hopenG hpushG hopenM hpushM i j := by
  classical
  letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
  let hCommon :=
    AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_hCommon
      M hopenG hpushG hopenM hpushM i j
  let hqRight :=
    AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_hqRight
      M hopenG hpushG hopenM hpushM i j
  exact
    AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_compatibleAt_of_commuting
      (R := R) (ι := ι) (Sstage := Sstage) (t := t) (A := A) (uA := uA)
      (J := J) (G := G) (H := H)
      M cM hopenG hpushG hopenM hpushM i j hqRight hCommon

/-- The canonical chart trivializations of a finite-stage glued module remain compatible with
the transported cocycle after base change to the filtered colimit. -/
theorem AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_isCompatible
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor) :
    letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let g := M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM
    (AffineIntersectionUnitCocycle.mapToColimit M cM).IsCompatibleChartTrivialization
      hopenG hpushG
      ((pullback g).obj (cM.gluedModule hopenM hpushM))
      (AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization
        M cM hopenG hpushG hopenM hpushM) := by
  classical
  letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
  change ∀ i j,
    AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivializationCompatibleAt
      M cM hopenG hpushG hopenM hpushM i j
  exact fun i j =>
    AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_compatibleAt
      M cM hopenG hpushG hopenM hpushM i j

/-- Pulling a finite-stage Cech-glued module back to the filtered colimit gives the
Cech-glued module of the transported transition cocycle. -/
noncomputable def AffineIntersectionUnitCocycle.baseChangeGluedModuleIso
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor) :
    letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let g := M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM
    (pullback g).obj (cM.gluedModule hopenM hpushM) ≅
      (AffineIntersectionUnitCocycle.mapToColimit M cM).gluedModule hopenG hpushG := by
  classical
  letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
  let g := M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM
  exact
    AffineIntersectionUnitCocycle.gluedModuleIsoOfCompatibleChartTrivialization
      (c := AffineIntersectionUnitCocycle.mapToColimit M cM)
      hopenG hpushG
      ((pullback g).obj (cM.gluedModule hopenM hpushM))
      (AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization
        M cM hopenG hpushG hopenM hpushM)
      (AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization_isCompatible
        M cM hopenG hpushG hopenM hpushM)

end

end AlgebraicGeometry.Scheme.Modules

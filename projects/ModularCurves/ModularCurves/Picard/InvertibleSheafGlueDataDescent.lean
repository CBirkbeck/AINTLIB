import ModularCurves.Picard.InvertibleSheafGlueData

/-!
# Descent data from affine-intersection unit cocycles

This file turns the chart transition morphisms attached to an
`AffineIntersectionUnitCocycle` into module descent data on the glued scheme.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

private theorem eq_id_of_conjugate
    {C : Type u} [Category C] {O A : C} (e : A ≅ O) (p : A ⟶ A)
    (h : e.inv ≫ p ≫ e.hom = 𝟙 O) :
    p = 𝟙 A := by
  calc
    p = e.hom ≫ (e.inv ≫ p ≫ e.hom) ≫ e.inv := by simp
    _ = e.hom ≫ 𝟙 O ≫ e.inv := by rw [h]
    _ = 𝟙 A := by simp

private theorem comp_eq_of_conjugates
    {C : Type u} [Category C] {O A B D : C}
    (eA : A ≅ O) (eB : B ≅ O) (eD : D ≅ O)
    (p : A ⟶ B) (q : B ⟶ D) (r : A ⟶ D)
    (p' q' r' : O ⟶ O)
    (hp : eA.inv ≫ p ≫ eB.hom = p')
    (hq : eB.inv ≫ q ≫ eD.hom = q')
    (hr : eA.inv ≫ r ≫ eD.hom = r')
    (hcoord : p' ≫ q' = r') :
    p ≫ q = r := by
  calc
    p ≫ q =
        eA.hom ≫ (eA.inv ≫ p ≫ eB.hom) ≫
          (eB.inv ≫ q ≫ eD.hom) ≫ eD.inv := by simp
    _ = eA.hom ≫ (p' ≫ q') ≫ eD.inv := by rw [hp, hq, Category.assoc]
    _ = eA.hom ≫ r' ≫ eD.inv := by rw [hcoord]
    _ = eA.hom ≫ (eA.inv ≫ r ≫ eD.hom) ≫ eD.inv := by rw [hr]
    _ = r := by simp

private theorem comp_of_eq
    {C : Type u} [Category C] {A B D : C}
    {p p' : A ⟶ B} {q q' : B ⟶ D} {r r' : A ⟶ D}
    (hp : p = p') (hq : q = q') (hr : r = r')
    (hcomp : p' ≫ q' = r') :
    p ≫ q = r :=
  ((congrArg₂ (fun a b => a ≫ b) hp hq).trans hcomp).trans hr.symm

/-- Congruence for a composite whose middle object is only definitionally equal to the other
one. Under lean4#14806 the kernel does not compare the arguments of `≫` before unfolding it, so
two composites that differ only in definitionally equal leaves (e.g. `D.U i` against the reduced
chart) are expensive to identify; with this lemma the kernel compares the middle objects and the
two factors separately, at top level. -/
private theorem comp_congr_heq
    {C : Type u} [Category C] {B Z Z' O : C}
    (p : B ⟶ Z) (p' : B ⟶ Z') (q : Z ⟶ O) (q' : Z' ⟶ O)
    (hZ : Z = Z') (hp : HEq p p') (hq : HEq q q') :
    p ≫ q = p' ≫ q' := by
  subst hZ
  obtain rfl := eq_of_heq hp
  obtain rfl := eq_of_heq hq
  rfl

/-- Transport an equation `p' ≫ q' = r'` to an equation between composites whose objects and
morphisms are only definitionally equal to the primed ones, comparing each piece separately
(see `comp_congr_heq`). -/
private theorem comp_eq_comp_of_heq
    {C : Type u} [Category C] {A B D A' B' D' : C}
    {p' : A' ⟶ B'} {q' : B' ⟶ D'} {r' : A' ⟶ D'} (h : p' ≫ q' = r')
    {p : A ⟶ B} {q : B ⟶ D} {r : A ⟶ D}
    (hA : A = A') (hB : B = B') (hD : D = D')
    (hp : HEq p p') (hq : HEq q q') (hr : HEq r r') :
    p ≫ q = r := by
  subst hA hB hD
  obtain rfl := eq_of_heq hp
  obtain rfl := eq_of_heq hq
  obtain rfl := eq_of_heq hr
  exact h

private noncomputable def AffineIntersectionUnitCocycle.chartTransitionPullHom
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) {T : Scheme.{u}}
    (g : T ⟶ (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).V (i, j))
    (gLeft : T ⟶ (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).U i)
    (gRight : T ⟶ (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).U j)
    (hLeft : g ≫
      (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).f i j = gLeft)
    (hRight : g ≫
      ((Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).t i j ≫
        (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).f j i) = gRight) :
    (pullback gLeft).obj (unitObj
        ((Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).U i)) ⟶
      (pullback gRight).obj (unitObj
        ((Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).U j)) :=
  Pseudofunctor.LocallyDiscreteOpToCat.pullHom
    (F := pullbackPseudofunctor)
    (c.chartTransitionIso hopen hpush i j).hom g gLeft gRight hLeft hRight

/-- An arbitrary pullback of a chart transition, expressed in unit coordinates, is its
coordinate pullback. -/
theorem AffineIntersectionUnitCocycle.chartTransitionPullHom_toUnit
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) {T : Scheme.{u}}
    (g : T ⟶ (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).V (i, j))
    (gLeft : T ⟶ (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).U i)
    (gRight : T ⟶ (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).U j)
    (hLeft : g ≫
      (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).f i j = gLeft)
    (hRight : g ≫
      ((Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).t i j ≫
        (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).f j i) = gRight) :
    (pullbackUnitIso gLeft).inv ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := pullbackPseudofunctor)
          (c.chartTransitionIso hopen hpush i j).hom g gLeft gRight hLeft hRight ≫
        (pullbackUnitIso gRight).hom =
      c.chartTransitionIsoCoordinatePullback hopen hpush i j g := by
  -- The statement elaborates the implicit arguments of `pullHom` in the reduced forms
  -- (`affineIntersectionChart`, `affineIntersectionOverlapι`), while the unit coherence
  -- lemmas use the glue-datum projections `D.U`/`D.f`. Matching the two forms inside the
  -- `≫`-composite costs the lean4#14806 kernel an unbounded check, so first restate the
  -- `pullHom` in glue-datum form via `comp_congr_heq` (a top-level comparison).
  have hct := c.chartTransitionIsoCoordinatePullback_chartTransition hopen hpush i j g
  refine Eq.trans (congrArg (fun x => (pullbackUnitIso gLeft).inv ≫ x)
    (comp_congr_heq _
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := pullbackPseudofunctor)
        (X₁ := (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).U i)
        (X₂ := (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).U j)
        (Y := (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).V (i, j))
        (f₁ := (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).f i j)
        (f₂ := (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).t i j ≫
          (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).f j i)
        (c.chartTransitionIso hopen hpush i j).hom g gLeft gRight hLeft hRight)
      _ _ rfl HEq.rfl HEq.rfl)) ?_
  exact (pullbackPseudofunctor_pullHom_unit _ _ _ _ _ _ _ _).trans hct.symm

private theorem AffineIntersectionUnitCocycle.chartTransitionIsoCoordinatePullback_self
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i : J) {T : Scheme.{u}}
    (g : T ⟶ (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).V (i, i)) :
    c.chartTransitionIsoCoordinatePullback hopen hpush i i g = 𝟙 _ := by
  rw [c.chartTransitionIsoCoordinatePullback_eq,
    c.overlapTransitionIso_self]
  simp

private theorem AffineIntersectionUnitCocycle.chartTransitionPullHom_self
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i : J)
    (g : (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).U i ⟶
      (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).V (i, i))
    (hLeft : g ≫
      (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).f i i = 𝟙 _)
    (hRight : g ≫
      ((Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).t i i ≫
        (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).f i i) = 𝟙 _) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := pullbackPseudofunctor)
        (c.chartTransitionIso hopen hpush i i).hom g (𝟙 _) (𝟙 _) hLeft hRight = 𝟙 _ := by
  -- Let the elaborator instantiate `chartTransitionPullHom_toUnit` against the goal instead of
  -- restating the conjugate with `D.U i`: the restated form differs from the statement's
  -- reduced `pullHom` arguments inside a `≫`-composite, which the lean4#14806 kernel cannot
  -- identify within the default budget.
  apply eq_id_of_conjugate (pullbackUnitIso (𝟙 _))
  exact (c.chartTransitionPullHom_toUnit hopen hpush i i g (𝟙 _) (𝟙 _) hLeft hRight).trans
    (c.chartTransitionIsoCoordinatePullback_self hopen hpush i g)

private theorem AffineIntersectionUnitCocycle.chartTransitionPullHom_comp
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j k : J) :
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := pullbackPseudofunctor)
          (c.chartTransitionIso hopen hpush i j).hom
          t.p₁₂ t.p₁ t.p₂ t.p₁₂_p₁ t.p₁₂_p₂ ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := pullbackPseudofunctor)
          (c.chartTransitionIso hopen hpush j k).hom
          t.p₂₃ t.p₂ t.p₃ t.p₂₃_p₂ t.p₂₃_p₃ =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := pullbackPseudofunctor)
        (c.chartTransitionIso hopen hpush i k).hom
        t.p₁₃ t.p₁ t.p₃ t.p₁₃_p₁ t.p₁₃_p₃ := by
  -- Keep `t` let-bound: `dsimp only` would unfold the `abbrev` glue datum inside the
  -- `pullHom` arguments, and the mixed forms cost the lean4#14806 kernel an unbounded check.
  -- With `intro t` the goal's `pullHom`s are syntactically the `chartTransitionPullHom_toUnit`
  -- instances. The cocycle is stated on the triple intersection's `Spec.map`s, so it is
  -- transported to `t.p₁₂`/`t.p₂₃`/`t.p₁₃` piece by piece with `comp_eq_comp_of_heq`.
  intro t
  have hco : c.chartTransitionIsoCoordinatePullback hopen hpush i j t.p₁₂ ≫
      c.chartTransitionIsoCoordinatePullback hopen hpush j k t.p₂₃ =
      c.chartTransitionIsoCoordinatePullback hopen hpush i k t.p₁₃ :=
    comp_eq_comp_of_heq (c.chartTransitionIsoCoordinatePullback_cocycle hopen hpush i j k)
      rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl
  exact comp_eq_of_conjugates
    (pullbackUnitIso t.p₁) (pullbackUnitIso t.p₂) (pullbackUnitIso t.p₃) _ _ _
    (c.chartTransitionIsoCoordinatePullback hopen hpush i j t.p₁₂)
    (c.chartTransitionIsoCoordinatePullback hopen hpush j k t.p₂₃)
    (c.chartTransitionIsoCoordinatePullback hopen hpush i k t.p₁₃)
    (c.chartTransitionPullHom_toUnit hopen hpush i j t.p₁₂ t.p₁ t.p₂ t.p₁₂_p₁ t.p₁₂_p₂)
    (c.chartTransitionPullHom_toUnit hopen hpush j k t.p₂₃ t.p₂ t.p₃ t.p₂₃_p₂ t.p₂₃_p₃)
    (c.chartTransitionPullHom_toUnit hopen hpush i k t.p₁₃ t.p₁ t.p₃ t.p₁₃_p₁ t.p₁₃_p₃)
    hco

/-- The unit module on an affine chart, viewed in the fibre of the pullback pseudofunctor. -/
noncomputable def chartDescentObj
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i : J) :
    pullbackPseudofunctor.obj (.mk (Opposite.op
      ((Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).U i))) :=
  unitObj _

/-- The overlap morphism between chartwise unit modules defined by the transition cocycle.

This is irreducible so that dependent descent-data elaboration uses the transition morphism's
public coherence lemmas instead of unfolding its pullback-unit conjugations. -/
noncomputable irreducible_def AffineIntersectionUnitCocycle.chartDescentHom
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) :
    let sq := affineIntersectionChartChosenPullback hopen hpush
    (pullbackPseudofunctor.map (sq i j).p₁.op.toLoc).toFunctor.obj
        (chartDescentObj hopen hpush i) ⟶
      (pullbackPseudofunctor.map (sq i j).p₂.op.toLoc).toFunctor.obj
        (chartDescentObj hopen hpush j) :=
  (c.chartTransitionIso hopen hpush i j).hom

private theorem AffineIntersectionUnitCocycle.chartDescentPullHom_comp_raw
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j k : J) :
    let t := affineIntersectionChartChosenPullback₃ hopen hpush i j k
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := pullbackPseudofunctor) (c.chartDescentHom hopen hpush i j)
          t.p₁₂ t.p₁ t.p₂ t.p₁₂_p₁ t.p₁₂_p₂ ≫
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := pullbackPseudofunctor) (c.chartDescentHom hopen hpush j k)
          t.p₂₃ t.p₂ t.p₃ t.p₂₃_p₂ t.p₂₃_p₃ =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := pullbackPseudofunctor) (c.chartDescentHom hopen hpush i k)
        t.p₁₃ t.p₁ t.p₃ t.p₁₃_p₁ t.p₁₃_p₃ := by
  -- Keep `t` let-bound (see `chartTransitionPullHom_comp`). After unfolding
  -- `chartDescentHom`, the `pullHom`s still carry the chosen-pullback (`sq`) forms of their
  -- implicit arguments, while `chartTransitionPullHom_comp` carries the glue-datum forms;
  -- `comp_eq_comp_of_heq` identifies them piece by piece instead of inside the composite.
  intro t
  rw [AffineIntersectionUnitCocycle.chartDescentHom_def,
    AffineIntersectionUnitCocycle.chartDescentHom_def,
    AffineIntersectionUnitCocycle.chartDescentHom_def]
  exact comp_eq_comp_of_heq (c.chartTransitionPullHom_comp hopen hpush i j k)
    rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl

theorem AffineIntersectionUnitCocycle.chartDescentHom_self
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i : J) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    let sq := affineIntersectionChartChosenPullback hopen hpush
    Pseudofunctor.DescentData'.pullHom'
      (F := pullbackPseudofunctor) (sq := sq)
      (c.chartDescentHom hopen hpush) (D.ι i) (𝟙 (D.U i)) (𝟙 (D.U i)) = 𝟙 _ := by
  dsimp only
  let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
  let sq := affineIntersectionChartChosenPullback hopen hpush
  let w : (𝟙 (D.U i)) ≫ D.ι i = (𝟙 (D.U i)) ≫ D.ι i := by simp
  let p := (sq i i).isPullback.lift (𝟙 (D.U i)) (𝟙 (D.U i)) w
  have hp₁ : p ≫ (sq i i).p₁ = 𝟙 (D.U i) :=
    (sq i i).isPullback.lift_fst (𝟙 (D.U i)) (𝟙 (D.U i)) w
  have hp₂ : p ≫ (sq i i).p₂ = 𝟙 (D.U i) :=
    (sq i i).isPullback.lift_snd (𝟙 (D.U i)) (𝟙 (D.U i)) w
  rw [Pseudofunctor.DescentData'.pullHom'_eq_pullHom _ _ _ _ p]
  rw [AffineIntersectionUnitCocycle.chartDescentHom_def]
  exact c.chartTransitionPullHom_self hopen hpush i p hp₁ hp₂

private theorem AffineIntersectionUnitCocycle.chartDescentHom_pullHom₁₂
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j k : J) :
    let sq := affineIntersectionChartChosenPullback hopen hpush
    let sq₃ := affineIntersectionChartChosenPullback₃ hopen hpush
    Pseudofunctor.DescentData'.pullHom'
        (F := pullbackPseudofunctor) (sq := sq)
        (c.chartDescentHom hopen hpush) (sq₃ i j k).p
        (sq₃ i j k).p₁ (sq₃ i j k).p₂ =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := pullbackPseudofunctor)
        (c.chartDescentHom hopen hpush i j)
        (sq₃ i j k).p₁₂ (sq₃ i j k).p₁ (sq₃ i j k).p₂
        (sq₃ i j k).p₁₂_p₁ (sq₃ i j k).p₁₂_p₂ := by
  dsimp only
  exact Pseudofunctor.DescentData'.pullHom'₁₂_eq_pullHom_of_chosenPullback₃
    (F := pullbackPseudofunctor) (affineIntersectionChartChosenPullback₃ hopen hpush)
    (c.chartDescentHom hopen hpush) i j k

private theorem AffineIntersectionUnitCocycle.chartDescentHom_pullHom₂₃
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j k : J) :
    let sq := affineIntersectionChartChosenPullback hopen hpush
    let sq₃ := affineIntersectionChartChosenPullback₃ hopen hpush
    Pseudofunctor.DescentData'.pullHom'
        (F := pullbackPseudofunctor) (sq := sq)
        (c.chartDescentHom hopen hpush) (sq₃ i j k).p
        (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := pullbackPseudofunctor)
        (c.chartDescentHom hopen hpush j k)
        (sq₃ i j k).p₂₃ (sq₃ i j k).p₂ (sq₃ i j k).p₃
        (sq₃ i j k).p₂₃_p₂ (sq₃ i j k).p₂₃_p₃ := by
  dsimp only
  exact Pseudofunctor.DescentData'.pullHom'₂₃_eq_pullHom_of_chosenPullback₃
    (F := pullbackPseudofunctor) (affineIntersectionChartChosenPullback₃ hopen hpush)
    (c.chartDescentHom hopen hpush) i j k

private theorem AffineIntersectionUnitCocycle.chartDescentHom_pullHom₁₃
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j k : J) :
    let sq := affineIntersectionChartChosenPullback hopen hpush
    let sq₃ := affineIntersectionChartChosenPullback₃ hopen hpush
    Pseudofunctor.DescentData'.pullHom'
        (F := pullbackPseudofunctor) (sq := sq)
        (c.chartDescentHom hopen hpush) (sq₃ i j k).p
        (sq₃ i j k).p₁ (sq₃ i j k).p₃ =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := pullbackPseudofunctor)
        (c.chartDescentHom hopen hpush i k)
        (sq₃ i j k).p₁₃ (sq₃ i j k).p₁ (sq₃ i j k).p₃
        (sq₃ i j k).p₁₃_p₁ (sq₃ i j k).p₁₃_p₃ := by
  dsimp only
  exact Pseudofunctor.DescentData'.pullHom'₁₃_eq_pullHom_of_chosenPullback₃
    (F := pullbackPseudofunctor) (affineIntersectionChartChosenPullback₃ hopen hpush)
    (c.chartDescentHom hopen hpush) i j k

/-- The chart transition morphisms satisfy the triple-overlap descent compatibility. -/
theorem AffineIntersectionUnitCocycle.chartDescentHom_comp
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j k : J) :
    Pseudofunctor.DescentData'.pullHom'
          (F := pullbackPseudofunctor)
          (sq := affineIntersectionChartChosenPullback hopen hpush)
          (obj := chartDescentObj hopen hpush)
          (obj' := chartDescentObj hopen hpush)
          (c.chartDescentHom hopen hpush)
          (affineIntersectionChartChosenPullback₃ hopen hpush i j k).p
          (affineIntersectionChartChosenPullback₃ hopen hpush i j k).p₁
          (affineIntersectionChartChosenPullback₃ hopen hpush i j k).p₂ ≫
        Pseudofunctor.DescentData'.pullHom'
          (F := pullbackPseudofunctor)
          (sq := affineIntersectionChartChosenPullback hopen hpush)
          (obj := chartDescentObj hopen hpush)
          (obj' := chartDescentObj hopen hpush)
          (c.chartDescentHom hopen hpush)
          (affineIntersectionChartChosenPullback₃ hopen hpush i j k).p
          (affineIntersectionChartChosenPullback₃ hopen hpush i j k).p₂
          (affineIntersectionChartChosenPullback₃ hopen hpush i j k).p₃ =
      Pseudofunctor.DescentData'.pullHom'
        (F := pullbackPseudofunctor)
        (sq := affineIntersectionChartChosenPullback hopen hpush)
        (obj := chartDescentObj hopen hpush)
        (obj' := chartDescentObj hopen hpush)
        (c.chartDescentHom hopen hpush)
        (affineIntersectionChartChosenPullback₃ hopen hpush i j k).p
        (affineIntersectionChartChosenPullback₃ hopen hpush i j k).p₁
        (affineIntersectionChartChosenPullback₃ hopen hpush i j k).p₃ := by
  exact comp_of_eq
    (c.chartDescentHom_pullHom₁₂ hopen hpush i j k)
    (c.chartDescentHom_pullHom₂₃ hopen hpush i j k)
    (c.chartDescentHom_pullHom₁₃ hopen hpush i j k)
    (c.chartDescentPullHom_comp_raw hopen hpush i j k)

/-- The module descent datum defined by an affine-intersection unit cocycle. -/
noncomputable def AffineIntersectionUnitCocycle.chartDescentData
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F) :
    let D := Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush
    @Pseudofunctor.DescentData'
      Scheme _ pullbackPseudofunctor J D.glued D.U D.ι
      (affineIntersectionChartChosenPullback hopen hpush)
      (affineIntersectionChartChosenPullback₃ hopen hpush) := by
  dsimp only
  refine
    { obj := chartDescentObj hopen hpush
      hom := c.chartDescentHom hopen hpush
      pullHom'_hom_self := ?_
      pullHom'_hom_comp := ?_ }
  · intro i
    as_aux_lemma => exact c.chartDescentHom_self hopen hpush i
  · intro i j k
    as_aux_lemma =>
      exact comp_of_eq
        (c.chartDescentHom_pullHom₁₂ hopen hpush i j k)
        (c.chartDescentHom_pullHom₂₃ hopen hpush i j k)
        (c.chartDescentHom_pullHom₁₃ hopen hpush i j k)
        (c.chartDescentPullHom_comp_raw hopen hpush i j k)

/-- Pulling the chart descent morphism along a map through the chosen overlap is the
corresponding pullback of the chart transition. -/
theorem AffineIntersectionUnitCocycle.chartDescent_pullHom_eq
    {A J : Type u} [CommRing A] {F : Functor (Finset J) (CommAlgCat.{u} A)}
    (c : AffineIntersectionUnitCocycle F)
    (hopen : Scheme.GlueData.IsOpenAffineIntersectionFunctor F)
    (hpush : Scheme.GlueData.IsPushoutAffineIntersectionFunctor F)
    (i j : J) {T : Scheme.{u}}
    (q : T ⟶ (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).glued)
    (g : T ⟶ (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).V (i, j))
    (gLeft : T ⟶ (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).U i)
    (gRight : T ⟶ (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).U j)
    (hqLeft : gLeft ≫
      (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).ι i = q)
    (hqRight : gRight ≫
      (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).ι j = q)
    (hLeft : g ≫
      (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).f i j = gLeft)
    (hRight : g ≫
      ((Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).t i j ≫
        (Scheme.GlueData.ofAffineIntersectionFunctor F hopen hpush).f j i) = gRight) :
    Pseudofunctor.DescentData'.pullHom'
        (c.chartDescentData hopen hpush).hom q gLeft gRight hqLeft hqRight =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := pullbackPseudofunctor)
        (c.chartTransitionIso hopen hpush i j).hom
        g gLeft gRight hLeft hRight := by
  change Pseudofunctor.DescentData'.pullHom'
      (c.chartDescentHom hopen hpush) q gLeft gRight hqLeft hqRight = _
  rw [Pseudofunctor.DescentData'.pullHom'_eq_pullHom
    _ q gLeft gRight g hqLeft hqRight hLeft hRight]
  rw [AffineIntersectionUnitCocycle.chartDescentHom_def]
  congr 1

end

end AlgebraicGeometry.Scheme.Modules

import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import ModularCurves.ForMathlib.FiniteIntersectionFunctorGeometry
import ModularCurves.ForMathlib.SpecBasicOpenAway

/-!
# Comparison of finite-intersection gluing with the original scheme

The affine-intersection algebra functor of an affine open cover produces scheme
glue data. This file identifies its singleton and pair spectra with the original
geometric opens and proves that the resulting glued scheme is the original scheme.
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

noncomputable section

variable {X S : Scheme.{u}} {J : Type u}

private noncomputable def glueDataDesc {Y : Scheme.{u}} (D : Scheme.GlueData.{u})
    (k : ∀ i, D.U i ⟶ Y)
    (hk : ∀ i j, D.f i j ≫ k i = D.t i j ≫ D.f j i ≫ k j) : D.glued ⟶ Y := by
  fapply Multicoequalizer.desc
  · exact k
  rintro ⟨i, j⟩
  exact hk i j

private theorem glueDataDesc_ι {Y : Scheme.{u}} (D : Scheme.GlueData.{u})
    (k : ∀ i, D.U i ⟶ Y)
    (hk : ∀ i j, D.f i j ≫ k i = D.t i j ≫ D.f j i ≫ k j) (i : D.J) :
    D.ι i ≫ glueDataDesc D k hk = k i :=
  Multicoequalizer.π_desc _ _ _ _ _

private noncomputable abbrev comparisonSingletonIndex (i : J) : Finset J := by
  classical
  exact {i}

private noncomputable abbrev comparisonPairIndex (i j : J) : Finset J := by
  classical
  exact {i, j}

private noncomputable def comparisonSingletonToPair (i j : J) :
    comparisonSingletonIndex i ⟶ comparisonPairIndex i j :=
  homOfLE (by
    classical
    simp [comparisonSingletonIndex, comparisonPairIndex])

private noncomputable def comparisonPairSwap (i j : J) :
    comparisonPairIndex j i ⟶ comparisonPairIndex i j :=
  homOfLE (by
    classical
    intro x hx
    simpa [comparisonPairIndex, or_comm] using hx)

private theorem finiteIntersectionOpen_pair (U : J → X.Opens) (i j : J) :
    X.finiteIntersectionOpen U (comparisonPairIndex i j) = U i ⊓ U j := by
  classical
  apply le_antisymm
  · exact le_inf
      (iInf_le_of_le i (iInf_le_of_le (by simp [comparisonPairIndex]) le_rfl))
      (iInf_le_of_le j (iInf_le_of_le (by simp [comparisonPairIndex]) le_rfl))
  · rw [Scheme.finiteIntersectionOpen]
    refine le_iInf fun k => le_iInf fun hk => ?_
    have hk' : k = i ∨ k = j := by
      simpa [comparisonPairIndex] using hk
    rcases hk' with rfl | rfl
    · exact inf_le_left
    · exact inf_le_right

/-- The spectrum attached to a nonempty finite-intersection functor object is
canonically the corresponding geometric open subscheme. -/
noncomputable def Scheme.Hom.affineIntersectionSchemeIso
    (π : X ⟶ S) (U : J → X.Opens) (s : Finset J) (hs : s.Nonempty)
    (hUs : IsAffineOpen (X.finiteIntersectionOpen U s)) :
    Spec (CommRingCat.of ((π.affineIntersectionFunctor U).obj s)) ≅
      (X.finiteIntersectionOpen U s).toScheme := by
  letI : IsAffine (X.finiteIntersectionOpen U s).toScheme := hUs
  change Spec ((forget₂ (CommAlgCat Γ(S, (⊤ : S.Opens))) CommRingCat).obj
      ((π.affineIntersectionFunctor U).obj s)) ≅
    (X.finiteIntersectionOpen U s).toScheme
  exact Scheme.Spec.mapIso (π.finiteIntersectionRingIso U s hs).op ≪≫
    (X.finiteIntersectionOpen U s).toScheme.isoSpec.symm

private theorem Scheme.Hom.affineIntersectionSpecMap_ringIso
    (π : X ⟶ S) (U : J → X.Opens) {s t : Finset J} (f : s ⟶ t)
    (hs : s.Nonempty) (ht : t.Nonempty) :
    Spec.map (CommRingCat.ofHom
        ((π.affineIntersectionFunctor U).map f).hom.toRingHom) ≫
        Spec.map (π.finiteIntersectionRingIso U s hs).op.hom.unop =
      Spec.map (π.finiteIntersectionRingIso U t ht).op.hom.unop ≫
        Spec.map (CommRingCat.ofHom
          (π.finiteIntersectionRestriction U (leOfHom f)).hom.toRingHom) := by
  have hRing := π.finiteIntersectionRestriction_ringIso U f hs ht
  have hSpec := congrArg (fun q => Spec.map q) hRing
  rw [Spec.map_comp, Spec.map_comp] at hSpec
  change Spec.map (CommRingCat.ofHom
        ((π.affineIntersectionFunctor U).map f).hom.toRingHom) ≫
        Spec.map (π.finiteIntersectionRingIso U s hs).hom =
      Spec.map (π.finiteIntersectionRingIso U t ht).hom ≫
        Spec.map (CommRingCat.ofHom
          (π.finiteIntersectionRestriction U (leOfHom f)).hom.toRingHom)
  exact hSpec.symm

private theorem Scheme.Hom.finiteIntersectionRingIso_isoSpec_inv_naturality
    (π : X ⟶ S) (U : J → X.Opens) (t : Finset J) (ht : t.Nonempty)
    [IsAffine (X.finiteIntersectionOpen U t).toScheme]
    {Y : Scheme.{u}} [IsAffine Y] (g : (X.finiteIntersectionOpen U t).toScheme ⟶ Y) :
    Spec.map (π.finiteIntersectionRingIso U t ht).op.hom.unop ≫
        Spec.map g.appTop ≫ Y.isoSpec.symm.hom =
      Spec.map (π.finiteIntersectionRingIso U t ht).op.hom.unop ≫
        (X.finiteIntersectionOpen U t).toScheme.isoSpec.symm.hom ≫ g := by
  apply (cancel_epi (Spec.map (π.finiteIntersectionRingIso U t ht).op.hom.unop)).mpr
  exact Scheme.isoSpec_inv_naturality g

private theorem Scheme.Hom.affineIntersectionSchemeMap_naturality
    (π : X ⟶ S) (U : J → X.Opens) {s t : Finset J} (f : s ⟶ t)
    (hs : s.Nonempty) (ht : t.Nonempty)
    [IsAffine (X.finiteIntersectionOpen U s).toScheme]
    [IsAffine (X.finiteIntersectionOpen U t).toScheme] :
    Spec.map (CommRingCat.ofHom ((π.affineIntersectionFunctor U).map f).hom.toRingHom) ≫
        Spec.map (π.finiteIntersectionRingIso U s hs).op.hom.unop ≫
          (X.finiteIntersectionOpen U s).toScheme.isoSpec.symm.hom =
      Spec.map (π.finiteIntersectionRingIso U t ht).op.hom.unop ≫
        (X.finiteIntersectionOpen U t).toScheme.isoSpec.symm.hom ≫
          X.homOfLE (X.finiteIntersectionOpen_antitone U (leOfHom f)) := by
  let g := X.homOfLE (X.finiteIntersectionOpen_antitone U (leOfHom f))
  calc
    _ = Spec.map (π.finiteIntersectionRingIso U t ht).op.hom.unop ≫
        Spec.map (CommRingCat.ofHom
          (π.finiteIntersectionRestriction U (leOfHom f)).hom.toRingHom) ≫
          (X.finiteIntersectionOpen U s).toScheme.isoSpec.symm.hom := by
        rw [← Category.assoc, π.affineIntersectionSpecMap_ringIso U f hs ht,
          Category.assoc]
    _ = _ := by
      rw [π.finiteIntersectionRestriction_forget U f]
      exact π.finiteIntersectionRingIso_isoSpec_inv_naturality U t ht g

/-- The scheme comparisons for nonempty finite intersections intertwine functor
maps with the corresponding inclusions of geometric intersections. -/
theorem Scheme.Hom.affineIntersectionSchemeIso_hom_homOfLE
    (π : X ⟶ S) (U : J → X.Opens) {s t : Finset J} (f : s ⟶ t)
    (hs : s.Nonempty) (ht : t.Nonempty)
    (hUs : IsAffineOpen (X.finiteIntersectionOpen U s))
    (hUt : IsAffineOpen (X.finiteIntersectionOpen U t)) :
    Spec.map (CommRingCat.ofHom ((π.affineIntersectionFunctor U).map f).hom.toRingHom) ≫
        (π.affineIntersectionSchemeIso U s hs hUs).hom =
      (π.affineIntersectionSchemeIso U t ht hUt).hom ≫
        X.homOfLE (X.finiteIntersectionOpen_antitone U (leOfHom f)) := by
  letI : IsAffine (X.finiteIntersectionOpen U s).toScheme := hUs
  letI : IsAffine (X.finiteIntersectionOpen U t).toScheme := hUt
  change Spec.map _ ≫ (Spec.map _ ≫ _) = (Spec.map _ ≫ _) ≫ _
  simpa only [Category.assoc] using
    π.affineIntersectionSchemeMap_naturality U f hs ht

/-- After inclusion into `X`, the comparison maps are natural for every inclusion
of nonempty finite index sets. -/
theorem Scheme.Hom.affineIntersectionSchemeIso_hom_ι
    (π : X ⟶ S) (U : J → X.Opens) {s t : Finset J} (f : s ⟶ t)
    (hs : s.Nonempty) (ht : t.Nonempty)
    (hUs : IsAffineOpen (X.finiteIntersectionOpen U s))
    (hUt : IsAffineOpen (X.finiteIntersectionOpen U t)) :
    Spec.map (CommRingCat.ofHom ((π.affineIntersectionFunctor U).map f).hom.toRingHom) ≫
        (π.affineIntersectionSchemeIso U s hs hUs).hom ≫
          (X.finiteIntersectionOpen U s).ι =
      (π.affineIntersectionSchemeIso U t ht hUt).hom ≫
        (X.finiteIntersectionOpen U t).ι := by
  rw [← Category.assoc, π.affineIntersectionSchemeIso_hom_homOfLE U f hs ht hUs hUt,
    Category.assoc, Scheme.homOfLE_ι]

/-- The scheme glue data associated to the actual finite-intersection diagram of
a family of opens. -/
noncomputable abbrev Scheme.Hom.affineIntersectionGlueData
    (π : X ⟶ S) (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s)) :
    Scheme.GlueData :=
  Scheme.GlueData.ofAffineIntersectionFunctor (π.affineIntersectionFunctor U)
    (π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU)
    (π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU)

/-- The singleton spectrum chart in the affine-intersection glue data is
canonically the corresponding original open subscheme. -/
noncomputable def Scheme.Hom.affineIntersectionChartIso
    (π : X ⟶ S) (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i : J) : (π.affineIntersectionGlueData U hU).U i ≅ (U i).toScheme := by
  classical
  have hi : (comparisonSingletonIndex i).Nonempty := by
    simp [comparisonSingletonIndex]
  change Spec (CommRingCat.of ((π.affineIntersectionFunctor U).obj
      (comparisonSingletonIndex i))) ≅ (U i).toScheme
  exact π.affineIntersectionSchemeIso U (comparisonSingletonIndex i) hi (hU _ hi) ≪≫
    X.isoOfEq (X.finiteIntersectionOpen_singleton U i)

/-- The pair spectrum overlap in the affine-intersection glue data is
canonically the corresponding intersection of original opens. -/
noncomputable def Scheme.Hom.affineIntersectionOverlapIso
    (π : X ⟶ S) (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) : (π.affineIntersectionGlueData U hU).V (i, j) ≅ (U i ⊓ U j).toScheme := by
  classical
  have hij : (comparisonPairIndex i j).Nonempty := by
    simp [comparisonPairIndex]
  change Spec (CommRingCat.of ((π.affineIntersectionFunctor U).obj
      (comparisonPairIndex i j))) ≅ (U i ⊓ U j).toScheme
  exact π.affineIntersectionSchemeIso U (comparisonPairIndex i j) hij (hU _ hij) ≪≫
    X.isoOfEq (finiteIntersectionOpen_pair U i j)

private noncomputable def Scheme.Hom.affineIntersectionChartMap
    (π : X ⟶ S) (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i : J) : (π.affineIntersectionGlueData U hU).U i ⟶ X := by
  classical
  have hi : (comparisonSingletonIndex i).Nonempty := by
    simp [comparisonSingletonIndex]
  change Spec (CommRingCat.of ((π.affineIntersectionFunctor U).obj
      (comparisonSingletonIndex i))) ⟶ X
  exact (π.affineIntersectionSchemeIso U (comparisonSingletonIndex i) hi (hU _ hi)).hom ≫
    (X.finiteIntersectionOpen U (comparisonSingletonIndex i)).ι

private noncomputable def Scheme.Hom.affineIntersectionOverlapMap
    (π : X ⟶ S) (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) : (π.affineIntersectionGlueData U hU).V (i, j) ⟶ X := by
  classical
  have hij : (comparisonPairIndex i j).Nonempty := by
    simp [comparisonPairIndex]
  change Spec (CommRingCat.of ((π.affineIntersectionFunctor U).obj
      (comparisonPairIndex i j))) ⟶ X
  exact (π.affineIntersectionSchemeIso U (comparisonPairIndex i j) hij (hU _ hij)).hom ≫
    (X.finiteIntersectionOpen U (comparisonPairIndex i j)).ι

private theorem Scheme.Hom.affineIntersectionChartIso_hom_ι
    (π : X ⟶ S) (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i : J) :
    (π.affineIntersectionChartIso U hU i).hom ≫ (U i).ι =
      π.affineIntersectionChartMap U hU i := by
  classical
  have hi : (comparisonSingletonIndex i).Nonempty := by
    simp [comparisonSingletonIndex]
  change (π.affineIntersectionSchemeIso U (comparisonSingletonIndex i) hi (hU _ hi)).hom ≫
        (X.isoOfEq (X.finiteIntersectionOpen_singleton U i)).hom ≫ (U i).ι =
    (π.affineIntersectionSchemeIso U (comparisonSingletonIndex i) hi (hU _ hi)).hom ≫
      (X.finiteIntersectionOpen U (comparisonSingletonIndex i)).ι
  rw [Scheme.isoOfEq_hom, Scheme.homOfLE_ι]

private theorem Scheme.Hom.affineIntersectionOverlapIso_hom_ι
    (π : X ⟶ S) (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    (π.affineIntersectionOverlapIso U hU i j).hom ≫ (U i ⊓ U j).ι =
      π.affineIntersectionOverlapMap U hU i j := by
  classical
  have hij : (comparisonPairIndex i j).Nonempty := by
    simp [comparisonPairIndex]
  change (π.affineIntersectionSchemeIso U (comparisonPairIndex i j) hij (hU _ hij)).hom ≫
        (X.isoOfEq (finiteIntersectionOpen_pair U i j)).hom ≫ (U i ⊓ U j).ι =
    (π.affineIntersectionSchemeIso U (comparisonPairIndex i j) hij (hU _ hij)).hom ≫
      (X.finiteIntersectionOpen U (comparisonPairIndex i j)).ι
  rw [Scheme.isoOfEq_hom, Scheme.homOfLE_ι]

private theorem Scheme.Hom.affineIntersectionGlueData_f_chartMap
    (π : X ⟶ S) (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    (π.affineIntersectionGlueData U hU).f i j ≫ π.affineIntersectionChartMap U hU i =
      π.affineIntersectionOverlapMap U hU i j := by
  classical
  have hi : (comparisonSingletonIndex i).Nonempty := by
    simp [comparisonSingletonIndex]
  have hij : (comparisonPairIndex i j).Nonempty :=
    hi.mono (leOfHom (comparisonSingletonToPair i j))
  change Spec.map (CommRingCat.ofHom ((π.affineIntersectionFunctor U).map
      (comparisonSingletonToPair i j)).hom.toRingHom) ≫
        (π.affineIntersectionSchemeIso U (comparisonSingletonIndex i) hi (hU _ hi)).hom ≫
          (X.finiteIntersectionOpen U (comparisonSingletonIndex i)).ι =
    (π.affineIntersectionSchemeIso U (comparisonPairIndex i j) hij (hU _ hij)).hom ≫
      (X.finiteIntersectionOpen U (comparisonPairIndex i j)).ι
  exact π.affineIntersectionSchemeIso_hom_ι U
    (comparisonSingletonToPair i j) hi hij (hU _ hi) (hU _ hij)

private theorem Scheme.Hom.affineIntersectionGlueData_t_overlapMap
    (π : X ⟶ S) (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    (π.affineIntersectionGlueData U hU).t i j ≫
        π.affineIntersectionOverlapMap U hU j i =
      π.affineIntersectionOverlapMap U hU i j := by
  classical
  have hji : (comparisonPairIndex j i).Nonempty := by
    simp [comparisonPairIndex]
  have hij : (comparisonPairIndex i j).Nonempty :=
    hji.mono (leOfHom (comparisonPairSwap i j))
  change Spec.map (CommRingCat.ofHom ((π.affineIntersectionFunctor U).map
      (comparisonPairSwap i j)).hom.toRingHom) ≫
        (π.affineIntersectionSchemeIso U (comparisonPairIndex j i) hji (hU _ hji)).hom ≫
          (X.finiteIntersectionOpen U (comparisonPairIndex j i)).ι =
    (π.affineIntersectionSchemeIso U (comparisonPairIndex i j) hij (hU _ hij)).hom ≫
      (X.finiteIntersectionOpen U (comparisonPairIndex i j)).ι
  exact π.affineIntersectionSchemeIso_hom_ι U
    (comparisonPairSwap i j) hji hij (hU _ hji) (hU _ hij)

private theorem Scheme.Hom.affineIntersectionGlueData_f_chartIso
    (π : X ⟶ S) (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    (π.affineIntersectionGlueData U hU).f i j ≫
        (π.affineIntersectionChartIso U hU i).hom =
      (π.affineIntersectionOverlapIso U hU i j).hom ≫
        X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) := by
  apply (cancel_mono (U i).ι).mp
  simp only [Category.assoc]
  rw [π.affineIntersectionChartIso_hom_ι U hU i,
    π.affineIntersectionGlueData_f_chartMap U hU i j, Scheme.homOfLE_ι,
    π.affineIntersectionOverlapIso_hom_ι U hU i j]

private theorem Scheme.Hom.affineIntersectionGlueData_t_f_chartIso
    (π : X ⟶ S) (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    (π.affineIntersectionGlueData U hU).t i j ≫
        (π.affineIntersectionGlueData U hU).f j i ≫
          (π.affineIntersectionChartIso U hU j).hom =
      (π.affineIntersectionOverlapIso U hU i j).hom ≫
        X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) := by
  apply (cancel_mono (U j).ι).mp
  simp only [Category.assoc]
  rw [π.affineIntersectionChartIso_hom_ι U hU j,
    π.affineIntersectionGlueData_f_chartMap U hU j i,
    π.affineIntersectionGlueData_t_overlapMap U hU i j, Scheme.homOfLE_ι,
    π.affineIntersectionOverlapIso_hom_ι U hU i j]

private theorem Scheme.Hom.affineIntersectionGlueData_chartMap_compat
    (π : X ⟶ S) (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    (π.affineIntersectionGlueData U hU).f i j ≫ π.affineIntersectionChartMap U hU i =
      (π.affineIntersectionGlueData U hU).t i j ≫
        (π.affineIntersectionGlueData U hU).f j i ≫
          π.affineIntersectionChartMap U hU j := by
  rw [π.affineIntersectionGlueData_f_chartMap U hU i j,
    π.affineIntersectionGlueData_f_chartMap U hU j i,
    π.affineIntersectionGlueData_t_overlapMap U hU i j]

@[reassoc]
private theorem Scheme.Hom.affineIntersectionOverlapToChartInverse_left
    (π : X ⟶ S) (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    (π.affineIntersectionOverlapIso U hU i j).hom ≫
        X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫
          (π.affineIntersectionChartIso U hU i).inv =
      (π.affineIntersectionGlueData U hU).f i j := by
  rw [← Category.assoc, ← π.affineIntersectionGlueData_f_chartIso U hU i j, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

@[reassoc]
private theorem Scheme.Hom.affineIntersectionOverlapToChartInverse_right
    (π : X ⟶ S) (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    (π.affineIntersectionOverlapIso U hU i j).hom ≫
        X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫
          (π.affineIntersectionChartIso U hU j).inv =
      (π.affineIntersectionGlueData U hU).t i j ≫
        (π.affineIntersectionGlueData U hU).f j i := by
  rw [← Category.assoc, ← π.affineIntersectionGlueData_t_f_chartIso U hU i j, Category.assoc,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem Scheme.Hom.affineIntersectionChartInverse_compat
    (π : X ⟶ S) (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j : J) :
    X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫
        (π.affineIntersectionChartIso U hU i).inv ≫
          (π.affineIntersectionGlueData U hU).ι i =
      X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫
        (π.affineIntersectionChartIso U hU j).inv ≫
          (π.affineIntersectionGlueData U hU).ι j := by
  apply (cancel_epi (π.affineIntersectionOverlapIso U hU i j).hom).mp
  rw [π.affineIntersectionOverlapToChartInverse_left_assoc U hU i j,
    π.affineIntersectionOverlapToChartInverse_right_assoc U hU i j]
  exact (π.affineIntersectionGlueData U hU).glue_condition i j |>.symm

private theorem glueMorphisms_hf_of_openCover_agree
    (U : J → X.Opens) (hcover : IsOpenCover U) {Y : Scheme.{u}}
    (F : ∀ i, (U i).toScheme ⟶ Y)
    (hF : ∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ F i =
      X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ F j) (i j : J) :
    pullback.fst ((X.openCoverOfIsOpenCover U hcover).f i)
        ((X.openCoverOfIsOpenCover U hcover).f j) ≫ F i =
      pullback.snd ((X.openCoverOfIsOpenCover U hcover).f i)
          ((X.openCoverOfIsOpenCover U hcover).f j) ≫ F j := by
  change pullback.fst (U i).ι (U j).ι ≫ F i = pullback.snd (U i).ι (U j).ι ≫ F j
  apply (cancel_epi (isPullback_opens_inf (U i) (U j)).isoPullback.hom).mp
  rw [IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
  exact hF i j

private noncomputable def Scheme.Hom.affineIntersectionOriginalToGlued
    (π : X ⟶ S) (U : J → X.Opens) (hcover : IsOpenCover U)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s)) :
    X ⟶ (π.affineIntersectionGlueData U hU).glued :=
  (X.openCoverOfIsOpenCover U hcover).glueMorphisms
    (fun i => (π.affineIntersectionChartIso U hU i).inv ≫
      (π.affineIntersectionGlueData U hU).ι i)
    (glueMorphisms_hf_of_openCover_agree U hcover _
      (π.affineIntersectionChartInverse_compat U hU))

/-- The canonical morphism from the scheme glued from the affine-intersection
diagram to the original scheme. -/
noncomputable def Scheme.Hom.affineIntersectionGluedToOriginal
    (π : X ⟶ S) (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s)) :
    (π.affineIntersectionGlueData U hU).glued ⟶ X :=
  glueDataDesc (π.affineIntersectionGlueData U hU)
    (π.affineIntersectionChartMap U hU)
    (π.affineIntersectionGlueData_chartMap_compat U hU)

/-- On every singleton chart, the canonical glued-to-original morphism is the
coordinate comparison followed by inclusion of that open into `X`. -/
theorem Scheme.Hom.affineIntersectionGlueData_ι_affineIntersectionGluedToOriginal
    (π : X ⟶ S) (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i : J) :
    (π.affineIntersectionGlueData U hU).ι i ≫
        π.affineIntersectionGluedToOriginal U hU =
      π.affineIntersectionChartMap U hU i := by
  unfold Scheme.Hom.affineIntersectionGluedToOriginal
  exact glueDataDesc_ι (π.affineIntersectionGlueData U hU)
    (π.affineIntersectionChartMap U hU)
    (π.affineIntersectionGlueData_chartMap_compat U hU) i

private theorem Scheme.Hom.affineIntersectionOriginalToGlued_restrict
    (π : X ⟶ S) (U : J → X.Opens) (hcover : IsOpenCover U)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i : J) :
    (U i).ι ≫ π.affineIntersectionOriginalToGlued U hcover hU =
      (π.affineIntersectionChartIso U hU i).inv ≫
        (π.affineIntersectionGlueData U hU).ι i := by
  unfold Scheme.Hom.affineIntersectionOriginalToGlued
  exact Scheme.Cover.ι_glueMorphisms (X.openCoverOfIsOpenCover U hcover) _ _ i

private theorem Scheme.Hom.affineIntersectionGluedToOriginal_comp_restrict
    (π : X ⟶ S) (U : J → X.Opens) (hcover : IsOpenCover U)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i : J) :
    (π.affineIntersectionGlueData U hU).ι i ≫
        (π.affineIntersectionGluedToOriginal U hU ≫
          π.affineIntersectionOriginalToGlued U hcover hU) =
      (π.affineIntersectionGlueData U hU).ι i := by
  rw [← Category.assoc,
    π.affineIntersectionGlueData_ι_affineIntersectionGluedToOriginal U hU i,
    ← π.affineIntersectionChartIso_hom_ι U hU i, Category.assoc,
    π.affineIntersectionOriginalToGlued_restrict U hcover hU i,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

private theorem Scheme.Hom.affineIntersectionOriginalToGlued_comp_restrict
    (π : X ⟶ S) (U : J → X.Opens) (hcover : IsOpenCover U)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i : J) :
    (U i).ι ≫
        (π.affineIntersectionOriginalToGlued U hcover hU ≫
          π.affineIntersectionGluedToOriginal U hU) =
      (U i).ι := by
  rw [← Category.assoc, π.affineIntersectionOriginalToGlued_restrict U hcover hU i,
    Category.assoc, π.affineIntersectionGlueData_ι_affineIntersectionGluedToOriginal U hU i,
    ← π.affineIntersectionChartIso_hom_ι U hU i,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem Scheme.Hom.affineIntersectionGluedToOriginal_comp
    (π : X ⟶ S) (U : J → X.Opens) (hcover : IsOpenCover U)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s)) :
    π.affineIntersectionGluedToOriginal U hU ≫
        π.affineIntersectionOriginalToGlued U hcover hU =
      𝟙 (π.affineIntersectionGlueData U hU).glued := by
  apply (π.affineIntersectionGlueData U hU).openCover.hom_ext
  intro i
  change (π.affineIntersectionGlueData U hU).ι i ≫
      (π.affineIntersectionGluedToOriginal U hU ≫
        π.affineIntersectionOriginalToGlued U hcover hU) =
    (π.affineIntersectionGlueData U hU).ι i ≫ 𝟙 _
  rw [Category.comp_id]
  exact π.affineIntersectionGluedToOriginal_comp_restrict U hcover hU i

private theorem Scheme.Hom.affineIntersectionOriginalToGlued_comp
    (π : X ⟶ S) (U : J → X.Opens) (hcover : IsOpenCover U)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s)) :
    π.affineIntersectionOriginalToGlued U hcover hU ≫
        π.affineIntersectionGluedToOriginal U hU =
      𝟙 X := by
  apply (X.openCoverOfIsOpenCover U hcover).hom_ext
  intro i
  change (U i).ι ≫
      (π.affineIntersectionOriginalToGlued U hcover hU ≫
        π.affineIntersectionGluedToOriginal U hU) =
    (U i).ι ≫ 𝟙 X
  rw [Category.comp_id]
  exact π.affineIntersectionOriginalToGlued_comp_restrict U hcover hU i

/-- The canonical morphism from affine-intersection gluing to the original
scheme is an isomorphism whenever the opens cover. -/
theorem Scheme.Hom.isIso_affineIntersectionGluedToOriginal
    (π : X ⟶ S) (U : J → X.Opens) (hcover : IsOpenCover U)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s)) :
    IsIso (π.affineIntersectionGluedToOriginal U hU) := by
  refine ⟨⟨π.affineIntersectionOriginalToGlued U hcover hU, ?_, ?_⟩⟩
  · exact π.affineIntersectionGluedToOriginal_comp U hcover hU
  · exact π.affineIntersectionOriginalToGlued_comp U hcover hU

end

end AlgebraicGeometry

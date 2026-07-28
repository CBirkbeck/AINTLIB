import ModularCurves.ForMathlib.SheafOrderedCechCohomologyFiniteProducts
import ModularCurves.ForMathlib.SheafOrderedCechSheafResolution
import ModularCurves.ForMathlib.SheafCechAcyclicComparison

/-!
# Ordered Cech comparison for acyclic covers

The augmented ordered Cech resolution gives short exact sequences between
successive cycle sheaves. Dimension shifting along these sequences compares
positive sheaf cohomology with exactness of ordered Cech global sections.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

noncomputable section

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} [LinearOrder ι] (U : ι → Opens X)

private noncomputable abbrev orderedCechPositiveShortComplex (n : ℕ) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (orderedCechDifferential F U n)
    (orderedCechDifferential F U (n + 1))
    (orderedCechDifferential_comp F U n)

private noncomputable abbrev orderedCechCycleStepShortComplex (n : ℕ) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  let T := orderedCechPositiveShortComplex F U n
  let T' := orderedCechPositiveShortComplex F U (n + 1)
  ShortComplex.mk T.iCycles T'.toCycles (by
    rw [← cancel_mono T'.iCycles, Category.assoc, T'.toCycles_i, zero_comp]
    exact T.iCycles_g)

private noncomputable abbrev orderedCechInitialCycleShortComplex :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  let T := orderedCechPositiveShortComplex F U 0
  ShortComplex.mk (orderedCechAugmentation F U) T.toCycles (by
    rw [← cancel_mono T.iCycles, Category.assoc, T.toCycles_i, zero_comp]
    rw [orderedCechAugmentation, Category.assoc,
      ← cechToOrderedF_comp_d, ← Category.assoc,
      cechAugmentation_comp, zero_comp])

private noncomputable def cechOrderedZeroIso :
    cechTerm F U 0 ≅ orderedCechTerm F U 0 where
  hom := cechToOrderedF F U 0
  inv := orderedToCechAlternatingF F U 0
  hom_inv_id := cechToOrderedF_comp_orderedToCechAlternatingF_zero F U
  inv_hom_id := orderedToCechAlternatingF_comp_cechToOrderedF F U 0

private theorem orderedCechAugmentation_mono
    (hU : ⨆ i, U i = ⊤) :
    Mono (orderedCechAugmentation F U) := by
  letI : Mono (cechAugmentation F U) :=
    cechAugmentation_mono F U hU
  letI : IsIso (cechToOrderedF F U 0) := by
    change IsIso (cechOrderedZeroIso F U).hom
    infer_instance
  rw [orderedCechAugmentation]
  infer_instance

private theorem orderedCechPositiveShortComplex_exact
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    (orderedCechPositiveShortComplex F U n).Exact := by
  have h := orderedCechAugmentedComplex_acyclic F U hU
  rw [HomologicalComplex.acyclic_iff] at h
  have hn := h (n + 2)
  rw [HomologicalComplex.exactAt_iff' _ (n + 1) (n + 2) (n + 3)
    (by simp) (by simp)] at hn
  simpa only [HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor',
    orderedCechAugmentedComplex, CochainComplex.augment,
    CochainComplex.augment_X_succ, CochainComplex.augment_d_succ_succ,
    orderedCechComplex_X, orderedCechComplex_d,
    orderedCechPositiveShortComplex] using hn

private theorem orderedCechAugmentedShortComplex_exact
    (hU : ⨆ i, U i = ⊤) :
    (ShortComplex.mk (orderedCechAugmentation F U)
      (orderedCechDifferential F U 0)
      (by
        rw [orderedCechAugmentation, Category.assoc,
          ← cechToOrderedF_comp_d, ← Category.assoc,
          cechAugmentation_comp, zero_comp])).Exact := by
  have h := orderedCechAugmentedComplex_acyclic F U hU
  rw [HomologicalComplex.acyclic_iff] at h
  have h1 := h 1
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2
    (by simp) (by simp)] at h1
  let S := ShortComplex.mk (orderedCechAugmentation F U)
    (orderedCechDifferential F U 0)
    (by
      rw [orderedCechAugmentation, Category.assoc,
        ← cechToOrderedF_comp_d, ← Category.assoc,
        cechAugmentation_comp, zero_comp])
  let C := (orderedCechAugmentedComplex F U).sc' 0 1 2
  let e : S ≅ C :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        simp only [Iso.refl_hom]
        change orderedCechAugmentation F U =
          (orderedCechAugmentedComplex F U).d 0 1
        rfl)
      (by
        simp only [Iso.refl_hom]
        change orderedCechDifferential F U 0 =
          (orderedCechAugmentedComplex F U).d 1 2
        rfl)
  change S.Exact
  exact ShortComplex.exact_of_iso e.symm h1

private theorem orderedCechInitialCycleShortComplex_shortExact
    (hU : ⨆ i, U i = ⊤) :
    (orderedCechInitialCycleShortComplex F U).ShortExact := by
  let T := orderedCechPositiveShortComplex F U 0
  let S := orderedCechInitialCycleShortComplex F U
  let A := ShortComplex.mk (orderedCechAugmentation F U)
    (orderedCechDifferential F U 0)
    (by
      rw [orderedCechAugmentation, Category.assoc,
        ← cechToOrderedF_comp_d, ← Category.assoc,
        cechAugmentation_comp, zero_comp])
  have hA : A.Exact := orderedCechAugmentedShortComplex_exact F U hU
  haveI : Mono S.f := by
    change Mono (orderedCechAugmentation F U)
    exact orderedCechAugmentation_mono F U hU
  haveI : Mono A.f := by
    change Mono (orderedCechAugmentation F U)
    exact orderedCechAugmentation_mono F U hU
  have hker : IsLimit (KernelFork.ofι S.f S.zero) :=
    isKernelOfComp T.iCycles T.f hA.fIsKernel S.zero T.toCycles_i
  have hS : S.Exact := ShortComplex.exact_of_f_is_kernel S hker
  have hT : T.Exact :=
    orderedCechPositiveShortComplex_exact F U hU 0
  haveI : Epi S.g := by
    change Epi T.toCycles
    exact hT.epi_toCycles
  exact { exact := hS }

private theorem orderedCechCycleStepShortComplex_shortExact
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    (orderedCechCycleStepShortComplex F U n).ShortExact := by
  let T := orderedCechPositiveShortComplex F U n
  let T' := orderedCechPositiveShortComplex F U (n + 1)
  let S := orderedCechCycleStepShortComplex F U n
  have hT' : T'.Exact :=
    orderedCechPositiveShortComplex_exact F U hU (n + 1)
  haveI : Mono S.f := by
    change Mono T.iCycles
    infer_instance
  have hker : IsLimit (KernelFork.ofι S.f S.zero) :=
    isKernelOfComp T'.iCycles T'.f T.cyclesIsKernel S.zero
      T'.toCycles_i
  have hS : S.Exact := ShortComplex.exact_of_f_is_kernel S hker
  haveI : Epi S.g := by
    change Epi T'.toCycles
    exact hT'.epi_toCycles
  exact { exact := hS }

private theorem orderedCechPositiveCycles_subsingleton_H
    (hU : ⨆ i, U i = ⊤)
    (hterm : ∀ (p q : ℕ), 1 ≤ q →
      Subsingleton (CategoryTheory.Sheaf.H
        (orderedCechTerm F U p) q))
    (n q : ℕ) (hq : 1 ≤ q)
    (hF : Subsingleton
      (CategoryTheory.Sheaf.H F (q + n + 1))) :
    Subsingleton (CategoryTheory.Sheaf.H
      (orderedCechPositiveShortComplex F U n).cycles q) := by
  induction n generalizing q with
  | zero =>
      have hF' : Subsingleton
          (CategoryTheory.Sheaf.H F (q + 1)) := by
        simpa using hF
      simpa [orderedCechInitialCycleShortComplex,
        orderedCechPositiveShortComplex] using
        subsingleton_H_X₃_of_shortExact
          (orderedCechInitialCycleShortComplex_shortExact F U hU) q
          (hterm 0 q hq) hF'
  | succ n ih =>
      have hleft : Subsingleton (CategoryTheory.Sheaf.H
          (orderedCechPositiveShortComplex F U n).cycles
          (q + 1)) := by
        apply ih (q + 1) (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hF
      simpa [orderedCechCycleStepShortComplex,
        orderedCechPositiveShortComplex] using
        subsingleton_H_X₃_of_shortExact
          (orderedCechCycleStepShortComplex_shortExact F U hU n) q
          (hterm (n + 1) q hq) hleft

private theorem orderedCechTopSections_exact_succ
    (hU : ⨆ i, U i = ⊤)
    (hterm : ∀ (p q : ℕ), 1 ≤ q →
      Subsingleton (CategoryTheory.Sheaf.H
        (orderedCechTerm F U p) q))
    (n : ℕ)
    (hF : Subsingleton (CategoryTheory.Sheaf.H F (n + 1)))
    (x : (orderedCechTerm F U (n + 1)).obj.obj (op ⊤))
    (hx : (orderedCechDifferential F U (n + 1)).hom.app
      (op ⊤) x = 0) :
    ∃ y : (orderedCechTerm F U n).obj.obj (op ⊤),
      (orderedCechDifferential F U n).hom.app (op ⊤) y = x := by
  let T := orderedCechPositiveShortComplex F U n
  let K := ShortComplex.mk T.iCycles T.g T.iCycles_g
  have hK : K.Exact :=
    ShortComplex.exact_of_f_is_kernel K T.cyclesIsKernel
  obtain ⟨z, hz⟩ := Sheaf.sections_exact_of_left_exact hK
    (inferInstance : Mono K.f) x hx
  cases n with
  | zero =>
      let S := orderedCechInitialCycleShortComplex F U
      have hS : S.ShortExact :=
        orderedCechInitialCycleShortComplex_shortExact F U hU
      letI : Subsingleton (CategoryTheory.Sheaf.H S.X₁ 1) := by
        change Subsingleton (CategoryTheory.Sheaf.H F 1)
        simpa using hF
      obtain ⟨y, hy⟩ :=
        CategoryTheory.Sheaf.H.longSequence_surjective_of_subsingleton_H
          hS isTerminalTop z
      refine ⟨y, ?_⟩
      calc
        T.f.hom.app (op (⊤ : Opens X)) y =
            (T.toCycles ≫ T.iCycles).hom.app (op ⊤) y := by
              rw [T.toCycles_i]
        _ = T.iCycles.hom.app (op ⊤)
            (T.toCycles.hom.app (op ⊤) y) := rfl
        _ = T.iCycles.hom.app (op ⊤) z := congrArg _ hy
        _ = x := hz
  | succ n =>
      let S := orderedCechCycleStepShortComplex F U n
      have hS : S.ShortExact :=
        orderedCechCycleStepShortComplex_shortExact F U hU n
      letI : Subsingleton (CategoryTheory.Sheaf.H S.X₁ 1) := by
        change Subsingleton (CategoryTheory.Sheaf.H
          (orderedCechPositiveShortComplex F U n).cycles 1)
        apply orderedCechPositiveCycles_subsingleton_H
          F U hU hterm n 1 (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hF
      obtain ⟨y, hy⟩ :=
        CategoryTheory.Sheaf.H.longSequence_surjective_of_subsingleton_H
          hS isTerminalTop z
      refine ⟨y, ?_⟩
      calc
        T.f.hom.app (op (⊤ : Opens X)) y =
            (T.toCycles ≫ T.iCycles).hom.app (op ⊤) y := by
              rw [T.toCycles_i]
        _ = T.iCycles.hom.app (op ⊤)
            (T.toCycles.hom.app (op ⊤) y) := rfl
        _ = T.iCycles.hom.app (op ⊤) z := congrArg _ hy
        _ = x := hz

private abbrev globalSections (X : TopCat.{u}) :
    CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
        AddCommGrpCat.{u} :=
  CategoryTheory.Sheaf.Γ
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}

noncomputable local instance orderedAcyclicComparison_globalSections_additive :
    (globalSections X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).right_adjoint_additive

noncomputable local instance
    orderedAcyclicComparison_globalSections_preservesZeroMorphisms :
    (globalSections X).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive
    (F := globalSections X)

private abbrev orderedCechSiteDifferential (n : ℕ) :
    toSiteSheaf (orderedCechTerm F U n) ⟶
      toSiteSheaf (orderedCechTerm F U (n + 1)) :=
  orderedCechDifferential F U n

/-- If all positive cohomology of the ordered Cech terms vanishes, vanishing
of `H^(n+1)(F)` implies exactness of ordered Cech global sections in degree
`n+1`. -/
theorem orderedCechGlobalSections_exactAt_succ_of_subsingleton_H
    (hU : ⨆ i, U i = ⊤)
    (hterm : ∀ (p q : ℕ), 1 ≤ q →
      Subsingleton (CategoryTheory.Sheaf.H
        (orderedCechTerm F U p) q))
    (n : ℕ)
    (hF : Subsingleton (CategoryTheory.Sheaf.H F (n + 1))) :
    (((globalSections X).mapHomologicalComplex (.up ℕ)).obj
      (orderedCechComplex F U)).ExactAt (n + 1) := by
  let S : ShortComplex AddCommGrpCat.{u} :=
    ShortComplex.mk
      ((globalSections X).map (orderedCechSiteDifferential F U n))
      ((globalSections X).map
        (orderedCechSiteDifferential F U (n + 1))) (by
        calc
          _ = (globalSections X).map
              (orderedCechSiteDifferential F U n ≫
                orderedCechSiteDifferential F U (n + 1)) :=
            ((globalSections X).map_comp _ _).symm
          _ = (globalSections X).map 0 :=
            congrArg (globalSections X).map
              (orderedCechDifferential_comp F U n)
          _ = 0 := (globalSections X).map_zero
            (toSiteSheaf (orderedCechTerm F U n))
            (toSiteSheaf (orderedCechTerm F U (n + 2))))
  have hS : S.Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro x hx
    let eΓ := CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      isTerminalTop
    let xTop := eΓ.hom.app
      (toSiteSheaf (orderedCechTerm F U (n + 1))) x
    have hxTop :
        (orderedCechDifferential F U (n + 1)).hom.app
          (op ⊤) xTop = 0 := by
      calc
        _ = eΓ.hom.app
            (toSiteSheaf (orderedCechTerm F U (n + 2)))
            ((globalSections X).map
              (orderedCechSiteDifferential F U (n + 1)) x) :=
          (ConcreteCategory.congr_hom
            (eΓ.hom.naturality
              (orderedCechSiteDifferential F U (n + 1))) x).symm
        _ = 0 := by rw [hx, map_zero]
    obtain ⟨yTop, hyTop⟩ :=
      orderedCechTopSections_exact_succ
        F U hU hterm n hF xTop hxTop
    let y := eΓ.inv.app
      (toSiteSheaf (orderedCechTerm F U n)) yTop
    have hyInv :
        eΓ.hom.app (toSiteSheaf (orderedCechTerm F U n)) y =
          yTop :=
      Iso.inv_hom_id_apply
        (eΓ.app (toSiteSheaf (orderedCechTerm F U n))) yTop
    refine ⟨y, ?_⟩
    change (globalSections X).map
      (orderedCechSiteDifferential F U n) y = x
    apply (AddCommGrpCat.mono_iff_injective
      (eΓ.hom.app
        (toSiteSheaf (orderedCechTerm F U (n + 1))))).mp
          inferInstance
    have hnat :
        eΓ.hom.app
            (toSiteSheaf (orderedCechTerm F U (n + 1)))
            ((globalSections X).map
              (orderedCechSiteDifferential F U n) y) =
          (orderedCechDifferential F U n).hom.app (op ⊤)
            (eΓ.hom.app
              (toSiteSheaf (orderedCechTerm F U n)) y) :=
      ConcreteCategory.congr_hom
        (eΓ.hom.naturality
          (orderedCechSiteDifferential F U n)) y
    refine hnat.trans ?_
    rw [hyInv]
    exact hyTop
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1)
    ((n + 1) + 1) (by simp) (by simp)]
  let C := ((globalSections X).mapHomologicalComplex (.up ℕ)).obj
    (orderedCechComplex F U)
  let e : S ≅ C.sc' n (n + 1) ((n + 1) + 1) :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        simp only [Iso.refl_hom]
        change (globalSections X).map
            ((orderedCechComplex F U).d n (n + 1)) =
          (globalSections X).map
            (orderedCechSiteDifferential F U n)
        exact congrArg (globalSections X).map
          (orderedCechComplex_d F U n))
      (by
        simp only [Iso.refl_hom]
        change (globalSections X).map
            ((orderedCechComplex F U).d
              (n + 1) ((n + 1) + 1)) =
          (globalSections X).map
            (orderedCechSiteDifferential F U (n + 1))
        exact congrArg (globalSections X).map
          (orderedCechComplex_d F U (n + 1)))
  exact ShortComplex.exact_of_iso e hS

end

end TopCat.Sheaf

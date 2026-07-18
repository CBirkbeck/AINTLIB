import ModularCurves.ForMathlib.SheafCechGlobalSections
import ModularCurves.ForMathlib.SheafCechSheafResolution
import ModularCurves.ForMathlib.SheafCohomologyExact

/-!
# Cech comparison for acyclic covers

This file uses the short exact sequences between consecutive cycle sheaves in the
augmented sheaf-level Cech resolution. Dimension shifting then turns vanishing of
positive cohomology of the Cech terms into exactness of the Cech complex of global
sections.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

noncomputable section

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)

private noncomputable abbrev cechPositiveShortComplex (n : ℕ) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (cechDifferential F U n) (cechDifferential F U (n + 1))
    (cechDifferential_comp F U n)

private noncomputable abbrev cechCycleStepShortComplex (n : ℕ) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  let T := cechPositiveShortComplex F U n
  let T' := cechPositiveShortComplex F U (n + 1)
  ShortComplex.mk T.iCycles T'.toCycles (by
    rw [← cancel_mono T'.iCycles, Category.assoc, T'.toCycles_i, zero_comp]
    exact T.iCycles_g)

private noncomputable abbrev cechInitialCycleShortComplex :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  let T := cechPositiveShortComplex F U 0
  ShortComplex.mk (cechAugmentation F U) T.toCycles (by
    rw [← cancel_mono T.iCycles, Category.assoc, T.toCycles_i, zero_comp,
      cechAugmentation_comp])

private theorem cechInitialCycleShortComplex_shortExact
    (hU : ⨆ i, U i = ⊤) :
    (cechInitialCycleShortComplex F U).ShortExact := by
  let T := cechPositiveShortComplex F U 0
  let S := cechInitialCycleShortComplex F U
  let A := cechAugmentedShortComplex F U
  have hA : A.Exact := cechAugmentedShortComplex_exact F U hU
  haveI : Mono S.f := by
    change Mono (cechAugmentation F U)
    exact cechAugmentation_mono F U hU
  haveI : Mono A.f := by
    change Mono (cechAugmentation F U)
    exact cechAugmentation_mono F U hU
  have hker : IsLimit (KernelFork.ofι S.f S.zero) :=
    isKernelOfComp T.iCycles T.f hA.fIsKernel S.zero T.toCycles_i
  have hS : S.Exact := ShortComplex.exact_of_f_is_kernel S hker
  have hT : T.Exact := cechShortComplex_exact F U hU 0
  haveI : Epi S.g := by
    change Epi T.toCycles
    exact hT.epi_toCycles
  exact { exact := hS }

private theorem cechCycleStepShortComplex_shortExact
    (hU : ⨆ i, U i = ⊤) (n : ℕ) :
    (cechCycleStepShortComplex F U n).ShortExact := by
  let T := cechPositiveShortComplex F U n
  let T' := cechPositiveShortComplex F U (n + 1)
  let S := cechCycleStepShortComplex F U n
  have hT' : T'.Exact := cechShortComplex_exact F U hU (n + 1)
  haveI : Mono S.f := by
    change Mono T.iCycles
    infer_instance
  have hker : IsLimit (KernelFork.ofι S.f S.zero) :=
    isKernelOfComp T'.iCycles T'.f T.cyclesIsKernel S.zero T'.toCycles_i
  have hS : S.Exact := ShortComplex.exact_of_f_is_kernel S hker
  haveI : Epi S.g := by
    change Epi T'.toCycles
    exact hT'.epi_toCycles
  exact { exact := hS }

private theorem subsingleton_H_X₃_of_shortExact
    {S : ShortComplex (Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (q : ℕ) (hmiddle : Subsingleton (H S.X₂ q))
    (hleft : Subsingleton (H S.X₁ (q + 1))) :
    Subsingleton (H S.X₃ q) := by
  letI : Subsingleton (H S.X₂ q) := hmiddle
  letI : Subsingleton (H S.X₁ (q + 1)) := hleft
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨x₂, hx₂⟩ := CategoryTheory.Sheaf.H.longSequence_exact₃
    hS q (q + 1) rfl x (Subsingleton.elim _ _)
  rw [Subsingleton.elim x₂ 0, map_zero] at hx₂
  exact hx₂.symm

private theorem cechPositiveCycles_subsingleton_H
    (hU : ⨆ i, U i = ⊤)
    (hterm : ∀ (p q : ℕ), 1 ≤ q → Subsingleton (H (cechTerm F U p) q))
    (n q : ℕ) (hq : 1 ≤ q)
    (hF : Subsingleton (H F (q + n + 1))) :
    Subsingleton (H (cechPositiveShortComplex F U n).cycles q) := by
  induction n generalizing q with
  | zero =>
      have hF' : Subsingleton (H F (q + 1)) := by
        simpa using hF
      simpa [cechInitialCycleShortComplex, cechPositiveShortComplex] using
        subsingleton_H_X₃_of_shortExact
          (cechInitialCycleShortComplex_shortExact F U hU) q
            (hterm 0 q hq) hF'
  | succ n ih =>
      have hleft :
          Subsingleton (H (cechPositiveShortComplex F U n).cycles (q + 1)) := by
        apply ih (q + 1) (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hF
      simpa [cechCycleStepShortComplex, cechPositiveShortComplex] using
        subsingleton_H_X₃_of_shortExact
          (cechCycleStepShortComplex_shortExact F U hU n) q
            (hterm (n + 1) q hq) hleft

private theorem cechTopSections_exact_succ
    (hU : ⨆ i, U i = ⊤)
    (hterm : ∀ (p q : ℕ), 1 ≤ q → Subsingleton (H (cechTerm F U p) q))
    (n : ℕ) (hF : Subsingleton (H F (n + 1)))
    (x : (cechTerm F U (n + 1)).obj.obj (op ⊤))
    (hx : (cechDifferential F U (n + 1)).hom.app (op ⊤) x = 0) :
    ∃ y : (cechTerm F U n).obj.obj (op ⊤),
      (cechDifferential F U n).hom.app (op ⊤) y = x := by
  let T := cechPositiveShortComplex F U n
  let K := ShortComplex.mk T.iCycles T.g T.iCycles_g
  have hK : K.Exact := ShortComplex.exact_of_f_is_kernel K T.cyclesIsKernel
  obtain ⟨z, hz⟩ := Sheaf.sections_exact_of_left_exact hK
    (inferInstance : Mono K.f) x hx
  cases n with
  | zero =>
      let S := cechInitialCycleShortComplex F U
      have hS : S.ShortExact := cechInitialCycleShortComplex_shortExact F U hU
      letI : Subsingleton (H S.X₁ 1) := by
        change Subsingleton (H F 1)
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
      let S := cechCycleStepShortComplex F U n
      have hS : S.ShortExact := cechCycleStepShortComplex_shortExact F U hU n
      letI : Subsingleton (H S.X₁ 1) := by
        change Subsingleton
          (H (cechPositiveShortComplex F U n).cycles 1)
        apply cechPositiveCycles_subsingleton_H F U hU hterm n 1 (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hF
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
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      AddCommGrpCat.{u} :=
  CategoryTheory.Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}

noncomputable local instance acyclicComparison_globalSections_additive :
    (globalSections X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

noncomputable local instance acyclicComparison_globalSections_preservesZeroMorphisms :
    (globalSections X).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive (F := globalSections X)

private abbrev cechSiteDifferential (n : ℕ) :
    toSiteSheaf (cechTerm F U n) ⟶ toSiteSheaf (cechTerm F U (n + 1)) :=
  cechDifferential F U n

private theorem cechGlobalSections_exactAt_succ
    (hU : ⨆ i, U i = ⊤)
    (hterm : ∀ (p q : ℕ), 1 ≤ q → Subsingleton (H (cechTerm F U p) q))
    (n : ℕ) (hF : Subsingleton (H F (n + 1))) :
    (((globalSections X).mapHomologicalComplex (.up ℕ)).obj
      (cechComplex F U)).ExactAt (n + 1) := by
  let S : ShortComplex AddCommGrpCat.{u} :=
    ShortComplex.mk
      ((globalSections X).map (cechSiteDifferential F U n))
      ((globalSections X).map (cechSiteDifferential F U (n + 1))) (by
        calc
          _ = (globalSections X).map
              (cechSiteDifferential F U n ≫ cechSiteDifferential F U (n + 1)) :=
            ((globalSections X).map_comp _ _).symm
          _ = (globalSections X).map 0 :=
            congrArg (globalSections X).map (cechDifferential_comp F U n)
          _ = 0 := (globalSections X).map_zero
            (toSiteSheaf (cechTerm F U n))
            (toSiteSheaf (cechTerm F U (n + 2))))
  have hS : S.Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro x hx
    let eΓ := CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop
    let xTop := eΓ.hom.app (toSiteSheaf (cechTerm F U (n + 1))) x
    have hxTop :
        (cechDifferential F U (n + 1)).hom.app (op ⊤) xTop = 0 := by
      calc
        _ = eΓ.hom.app (toSiteSheaf (cechTerm F U (n + 2)))
            ((globalSections X).map (cechSiteDifferential F U (n + 1)) x) :=
          (ConcreteCategory.congr_hom
            (eΓ.hom.naturality (cechSiteDifferential F U (n + 1))) x).symm
        _ = 0 := by rw [hx, map_zero]
    obtain ⟨yTop, hyTop⟩ :=
      cechTopSections_exact_succ F U hU hterm n hF xTop hxTop
    let y := eΓ.inv.app (toSiteSheaf (cechTerm F U n)) yTop
    have hyInv :
        eΓ.hom.app (toSiteSheaf (cechTerm F U n)) y = yTop :=
      Iso.inv_hom_id_apply (eΓ.app (toSiteSheaf (cechTerm F U n))) yTop
    refine ⟨y, ?_⟩
    change (globalSections X).map (cechSiteDifferential F U n) y = x
    apply (AddCommGrpCat.mono_iff_injective
      (eΓ.hom.app (toSiteSheaf (cechTerm F U (n + 1))))).mp inferInstance
    have hnat :
        eΓ.hom.app (toSiteSheaf (cechTerm F U (n + 1)))
            ((globalSections X).map (cechSiteDifferential F U n) y) =
        (cechDifferential F U n).hom.app (op ⊤)
          (eΓ.hom.app (toSiteSheaf (cechTerm F U n)) y) :=
      ConcreteCategory.congr_hom
        (eΓ.hom.naturality (cechSiteDifferential F U n)) y
    refine hnat.trans ?_
    rw [hyInv]
    exact hyTop
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) ((n + 1) + 1) (by simp) (by simp)]
  let C := ((globalSections X).mapHomologicalComplex (.up ℕ)).obj
    (cechComplex F U)
  let e : S ≅ C.sc' n (n + 1) ((n + 1) + 1) :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        simp only [Iso.refl_hom]
        change (globalSections X).map ((cechComplex F U).d n (n + 1)) =
          (globalSections X).map (cechSiteDifferential F U n)
        exact congrArg (globalSections X).map (cechComplex_d F U n))
      (by
        simp only [Iso.refl_hom]
        change (globalSections X).map ((cechComplex F U).d (n + 1) ((n + 1) + 1)) =
          (globalSections X).map (cechSiteDifferential F U (n + 1))
        exact congrArg (globalSections X).map (cechComplex_d F U (n + 1)))
  exact ShortComplex.exact_of_iso e hS

/-- If all positive cohomology of the Cech terms vanishes, vanishing of
`H^(n+1)(F)` implies exactness of the native Cech complex in degree `n+1`. -/
theorem cechComplex_exactAt_succ_of_subsingleton_H
    (hU : ⨆ i, U i = ⊤)
    (hterm : ∀ (p q : ℕ), 1 ≤ q → Subsingleton (H (cechTerm F U p) q))
    (n : ℕ) (hF : Subsingleton (H F (n + 1))) :
    ((cechComplexFunctor U).obj F.obj).ExactAt (n + 1) :=
  (cechGlobalSections_exactAt_succ F U hU hterm n hF).of_iso
    (cechGlobalSectionsComplexIso F U)

end

end TopCat.Sheaf

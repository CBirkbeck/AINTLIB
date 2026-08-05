/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.YStalks
import «Adic spaces».SheafyPair

/-!
# The subset-relative all-open sheaf condition (YB6c-3e-1/2)

Tate-free, `S`-relative copies of the `SheafyPair` engines: the valid
intersection datum `interValid` over a general Huber ring (power certificates
in place of `span = ⊤`), the R3 bridge, the finite rational refinement at a
compactness hypothesis, the three arbitrary-cover engines at `IsSheafyOn`
(coverings whose base lies inside `S`), the bundled `IsLimitSheafOn`, and its
`Hom`-gluing core. Instantiated at `S := Y` over `A_inf` by `YSheaf`.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal TopologicalSpace Topology Filter

noncomputable section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [PlusSubring A] [IsHuberRing A] [DecidableEq A] [DecidableEq (RationalLocData A)]
  [IsRingOfIntegralElements (A⁺ : Subring A)] [HasLocLiftPowerBounded A]

/-- **The valid intersection datum over a general Huber ring** (the Tate-free
`interRational`): the `interDatumOpen` at power certificates chosen from the
openness of the two tray spans. -/
noncomputable def RationalLocData.interValid (D E : RationalLocData A)
    (hD : D.IsRational) (hE : E.IsRational) : RationalLocData A :=
  D.interDatumOpen E
    (exists_pow_le_of_isRational_pair D.P D hD).choose
    (exists_pow_le_of_isRational_pair D.P E hE).choose
    (exists_pow_le_of_isRational_pair D.P D hD).choose_spec
    (exists_pow_le_of_isRational_pair D.P E hE).choose_spec

omit [DecidableEq (RationalLocData A)] [IsRingOfIntegralElements A⁺] [HasLocLiftPowerBounded A] in
theorem RationalLocData.interValid_rationalOpen (D E : RationalLocData A)
    (hD : D.IsRational) (hE : E.IsRational) :
    rationalOpen (D.interValid E hD hE).T (D.interValid E hD hE).s =
      rationalOpen D.T D.s ∩ rationalOpen E.T E.s :=
  D.interDatumOpen_rationalOpen E _ _ _ _

omit [DecidableEq (RationalLocData A)] [IsRingOfIntegralElements A⁺] [HasLocLiftPowerBounded A] in
theorem RationalLocData.interValid_isRational (D E : RationalLocData A)
    (hD : D.IsRational) (hE : E.IsRational) :
    (D.interValid E hD hE).IsRational :=
  RationalLocData.isRational_of_pow_le _
    (D.interDatumOpen_pow_le E _ _ _ _)

theorem RationalLocData.interValid_subset_left (D E : RationalLocData A)
    (hD : D.IsRational) (hE : E.IsRational) :
    rationalOpen (D.interValid E hD hE).T (D.interValid E hD hE).s ⊆
      rationalOpen D.T D.s := by
  rw [D.interValid_rationalOpen E hD hE]
  exact Set.inter_subset_left

theorem RationalLocData.interValid_subset_right (D E : RationalLocData A)
    (hD : D.IsRational) (hE : E.IsRational) :
    rationalOpen (D.interValid E hD hE).T (D.interValid E hD hE).s ⊆
      rationalOpen E.T E.s := by
  rw [D.interValid_rationalOpen E hD hE]
  exact Set.inter_subset_right

omit [DecidableEq A] [DecidableEq (RationalLocData A)] in
/-- Separation from the subset-relative sheaf condition. -/
theorem IsSheafyOn.separationSub [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    {S : Set (Spv A)} (hOn : IsSheafyOn S)
    (C : RationalCoveringData A) (hC : C.IsRational)
    (hbase : rationalOpen C.base.T C.base.s ⊆ S) :
    Function.Injective (productRestrictionSub A C) :=
  (hOn.embedding C hC hbase).injective

omit [DecidableEq (RationalLocData A)] [IsRingOfIntegralElements A⁺] [HasLocLiftPowerBounded A] in
/-- A rational datum whose trace lies in a trace-subset of `S` has its
rational open inside `S`. -/
theorem RationalLocData.rationalOpen_subset_of_trace {S : Set (Spv A)}
    {D : RationalLocData A} {W : Set ↥(Spa A A⁺)}
    (hDW : spaOpen D ⊆ W) (hWS : W ⊆ Subtype.val ⁻¹' S) :
    rationalOpen D.T D.s ⊆ S :=
  fun v hv => hWS (hDW (show (⟨v, rationalOpen_subset_spa hv⟩
    : ↥(Spa A A⁺)) ∈ spaOpen D from hv))

/-- **Finite rational refinement over a general Huber ring** (the Tate-free
`exists_finite_rational_refinement`): compactness supplied as a hypothesis,
the basis from `exists_isRational_spaOpen_subset_huber`. -/
theorem exists_finite_rational_refinement_huber (D : RationalLocData A)
    (_hD : D.IsRational) (hcomp : IsCompact (spaOpen D))
    {ι : Type*} (U : ι → Set ↥(Spa A A⁺)) (hUopen : ∀ i, IsOpen (U i))
    (hUcov : spaOpen D ⊆ ⋃ i, U i) :
    ∃ t : Finset (RefinementIndex D U),
      spaOpen D ⊆ ⋃ q ∈ t, spaOpen (q : RefinementIndex D U).1.1 := by
  classical
  have hcov : spaOpen D ⊆ ⋃ q : RefinementIndex D U, spaOpen q.1.1 := by
    intro v hv
    obtain ⟨i, hvU⟩ := Set.mem_iUnion.mp (hUcov hv)
    obtain ⟨E, hErat, hvE, hEsub⟩ := exists_isRational_spaOpen_subset_huber
      ((isOpen_spaOpen D).inter (hUopen i)) (Set.mem_inter hv hvU)
    exact Set.mem_iUnion.mpr ⟨⟨(E, i), hErat, hEsub⟩, hvE⟩
  obtain ⟨t, ht⟩ := hcomp.elim_finite_subcover
    (fun q : RefinementIndex D U => spaOpen q.1.1)
    (fun q => isOpen_spaOpen _) hcov
  exact ⟨t, ht⟩

variable [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
    CompleteSpace A]

/-- **Separation of the all-open presheaf on arbitrary covers, `S`-relative**
(the Tate-free `limitRestrict_injective` at `IsSheafyOn`). -/
theorem limitRestrict_injective_on {S : Set (Spv A)} (hOn : IsSheafyOn S)
    (hcomp : ∀ D : RationalLocData A, D.IsRational → IsCompact (spaOpen D))
    {V : Opens ↥(Spa A A⁺)} (hVS : (V : Set ↥(Spa A A⁺)) ⊆ Subtype.val ⁻¹' S)
    {ι : Type*} {U : ι → Opens ↥(Spa A A⁺)}
    (hle : ∀ i, U i ≤ V) (hcov : (V : Set ↥(Spa A A⁺)) ⊆ ⋃ i, (U i : Set ↥(Spa A A⁺)))
    {x y : ↥(limitSections V)}
    (h : ∀ i, limitRestrict (hle i) x = limitRestrict (hle i) y) : x = y := by
  classical
  refine Subtype.ext (funext fun D => ?_)
  obtain ⟨t, ht⟩ := exists_finite_rational_refinement_huber D.D D.isRational
    (hcomp D.D D.isRational)
    (fun i => (U i : Set ↥(Spa A A⁺))) (fun i => (U i).2)
    (D.subset.trans hcov)
  set C := refinementCovering D.D t ht with hC
  have hCrat : C.IsRational := refinementCovering_isRational D.D D.isRational t ht
  have hprod : productRestrictionSub A C
        ((x : ∀ j : RationalIndex V, presheafValue j.D) D) =
      productRestrictionSub A C
        ((y : ∀ j : RationalIndex V, presheafValue j.D) D) := by
    funext ⟨E, hE⟩
    obtain ⟨q, hqt, rfl⟩ := Finset.mem_image.mp
      (show E ∈ t.image (fun q => q.1.1) from hE)
    have hEUi : spaOpen q.1.1 ⊆ (U q.1.2 : Set ↥(Spa A A⁺)) :=
      q.2.2.trans Set.inter_subset_right
    have hEV : spaOpen q.1.1 ⊆ (V : Set ↥(Spa A A⁺)) := hEUi.trans (hle q.1.2)
    have hED : rationalOpen q.1.1.T q.1.1.s ⊆ rationalOpen D.D.T D.D.s :=
      spaOpen_subset_iff.mp (q.2.2.trans Set.inter_subset_left)
    have hx : restrictionMap D.D q.1.1 hED
        ((x : ∀ j : RationalIndex V, presheafValue j.D) D) =
        (x : ∀ j : RationalIndex V, presheafValue j.D) ⟨q.1.1, q.2.1, hEV⟩ :=
      x.2 D ⟨q.1.1, q.2.1, hEV⟩ hED
    have hy : restrictionMap D.D q.1.1 hED
        ((y : ∀ j : RationalIndex V, presheafValue j.D) D) =
        (y : ∀ j : RationalIndex V, presheafValue j.D) ⟨q.1.1, q.2.1, hEV⟩ :=
      y.2 D ⟨q.1.1, q.2.1, hEV⟩ hED
    show restrictionMap D.D q.1.1 hED _ = restrictionMap D.D q.1.1 hED _
    rw [hx, hy]
    have := congr_fun (congrArg (fun z : ↥(limitSections (U q.1.2)) =>
      (z : ∀ j : RationalIndex (U q.1.2), presheafValue j.D)) (h q.1.2))
      ⟨q.1.1, q.2.1, hEUi⟩
    exact this
  exact hOn.separationSub C hCrat
    (RationalLocData.rationalOpen_subset_of_trace D.subset hVS) hprod

/-- **The R3 bridge, Tate-free** (`interValid` in place of `interRational`):
valid-rational-refinement compatibility implies all-raw-data compatibility
over any Huber ring. -/
theorem RationalCoveringData.RationalRefinementCompatible.allData_huber
    {C : RationalCoveringData A} (hC : C.IsRational)
    {f : ∀ D : ↥C.covers, presheafValue D.1}
    (hf : C.RationalRefinementCompatible f) : C.AllDataCompatible f := by
  intro D₁ D₂ D₃ h₃₁ h₃₂
  set I := D₁.1.interValid D₂.1 (hC.piece D₁.2) (hC.piece D₂.2) with hI
  have h₃I : rationalOpen D₃.T D₃.s ⊆ rationalOpen I.T I.s := by
    rw [hI, RationalLocData.interValid_rationalOpen]
    exact Set.subset_inter h₃₁ h₃₂
  have hIL : rationalOpen I.T I.s ⊆ rationalOpen D₁.1.T D₁.1.s :=
    RationalLocData.interValid_subset_left _ _ _ _
  have hIR : rationalOpen I.T I.s ⊆ rationalOpen D₂.1.T D₂.1.s :=
    RationalLocData.interValid_subset_right _ _ _ _
  have hIval : I.IsRational :=
    RationalLocData.interValid_isRational _ _ (hC.piece D₁.2) (hC.piece D₂.2)
  have hagree := hf D₁ D₂ I hIval hIL hIR
  have c₁ := restrictionMap_restrictionMap D₁.1 I D₃ hIL h₃I (f D₁)
  have c₂ := restrictionMap_restrictionMap D₂.1 I D₃ hIR h₃I (f D₂)
  calc restrictionMap D₁.1 D₃ h₃₁ (f D₁)
      = restrictionMap I D₃ h₃I (restrictionMap D₁.1 I hIL (f D₁)) := c₁.symm
    _ = restrictionMap I D₃ h₃I (restrictionMap D₂.1 I hIR (f D₂)) := by
        rw [hagree]
    _ = restrictionMap D₂.1 D₃ h₃₂ (f D₂) := c₂

/-- The pieces of the valid intersection covering (`interValid` form of
`interCoveringPieces`). -/
def interCoveringPiecesV (E' : RationalLocData A) (hE' : E'.IsRational)
    (C : RationalCoveringData A) (hC : C.IsRational) : Finset (RationalLocData A) :=
  C.covers.attach.image fun E => E'.interValid E.1 hE' (hC.piece E.2)

theorem mem_interCoveringPiecesV (E' : RationalLocData A) (hE' : E'.IsRational)
    (C : RationalCoveringData A) (hC : C.IsRational) {F : RationalLocData A} :
    F ∈ interCoveringPiecesV E' hE' C hC ↔
      ∃ E : ↥C.covers, E'.interValid E.1 hE' (hC.piece E.2) = F := by
  unfold interCoveringPiecesV
  simp only [Finset.mem_image, Finset.mem_attach, true_and]

/-- The covering of a valid rational `E'` inside `C.base` by its valid
intersections with the pieces of `C` (`interValid` form of `interCovering`). -/
def interCoveringV (E' : RationalLocData A) (hE' : E'.IsRational)
    (C : RationalCoveringData A) (hC : C.IsRational)
    (hsub : rationalOpen E'.T E'.s ⊆ rationalOpen C.base.T C.base.s) :
    RationalCoveringData A where
  base := E'
  covers := interCoveringPiecesV E' hE' C hC
  hsubset := by
    intro F hF
    obtain ⟨E, hFeq⟩ := (mem_interCoveringPiecesV E' hE' C hC).mp hF
    exact hFeq ▸ RationalLocData.interValid_subset_left _ _ _ _
  hcover := by
    intro v hv
    obtain ⟨E, hEC, hvE⟩ := C.hcover v (hsub hv)
    refine ⟨E'.interValid E hE' (hC.piece hEC),
      (mem_interCoveringPiecesV E' hE' C hC).mpr ⟨⟨E, hEC⟩, rfl⟩, ?_⟩
    rw [RationalLocData.interValid_rationalOpen]
    exact ⟨hv, hvE⟩

theorem interCoveringV_isRational (E' : RationalLocData A) (hE' : E'.IsRational)
    (C : RationalCoveringData A) (hC : C.IsRational)
    (hsub : rationalOpen E'.T E'.s ⊆ rationalOpen C.base.T C.base.s) :
    (interCoveringV E' hE' C hC hsub).IsRational := by
  refine ⟨hE', ?_⟩
  intro F hF
  obtain ⟨E, hFeq⟩ := (mem_interCoveringPiecesV E' hE' C hC).mp hF
  exact hFeq ▸ RationalLocData.interValid_isRational _ _ _ _

/-- **The per-rational-datum gluing step, relative version**: for every valid rational `D₀`
inside `V` (hence inside the trace set `S`), a section over `D₀` restricting, on every rational
refinement piece contained in some `U i`, to the given family. Extracted from
`exists_limitSections_glue_on`, where it was the opening 75-line `have`. -/
private theorem exists_glue_at_rational_on {S : Set (Spv A)} (hOn : IsSheafyOn S)
    (hcomp : ∀ D : RationalLocData A, D.IsRational → IsCompact (spaOpen D))
    {V : Opens ↥(Spa A A⁺)} (hVS : (V : Set ↥(Spa A A⁺)) ⊆ Subtype.val ⁻¹' S)
    {ι : Type*} {U : ι → Opens ↥(Spa A A⁺)}
    (hcov : (V : Set ↥(Spa A A⁺)) ⊆ ⋃ i, (U i : Set ↥(Spa A A⁺)))
    (s : ∀ i, ↥(limitSections (U i)))
    (hs : ∀ i j, limitRestrict (inf_le_left (a := U i) (b := U j)) (s i) =
                 limitRestrict (inf_le_right (a := U i) (b := U j)) (s j)) :
    ∀ (D₀ : RationalLocData A), D₀.IsRational →
      spaOpen D₀ ⊆ (V : Set ↥(Spa A A⁺)) →
      ∃ z : presheafValue D₀,
        ∀ (E : RationalLocData A) (hErat : E.IsRational)
          (hED : rationalOpen E.T E.s ⊆ rationalOpen D₀.T D₀.s) (i : ι)
          (hEUi : spaOpen E ⊆ (U i : Set ↥(Spa A A⁺))),
          restrictionMap D₀ E hED z = (s i).1 ⟨E, hErat, hEUi⟩ := by
  intro D₀ hD₀ hD₀V
  have hD₀S : rationalOpen D₀.T D₀.s ⊆ S := RationalLocData.rationalOpen_subset_of_trace hD₀V hVS
  obtain ⟨t, ht⟩ := exists_finite_rational_refinement_huber D₀ hD₀ (hcomp D₀ hD₀)
    (fun i => (U i : Set ↥(Spa A A⁺))) (fun i => (U i).2) (hD₀V.trans hcov)
  set C := refinementCovering D₀ t ht with hCdef
  have hCrat : C.IsRational := refinementCovering_isRational D₀ hD₀ t ht
  have hexE : ∀ E : ↥C.covers, E.1.IsRational ∧ ∃ i : ι, spaOpen E.1 ⊆ (U i : Set ↥(Spa A A⁺)) := by
    rintro ⟨E, hE⟩
    obtain ⟨q, hqt, rfl⟩ := Finset.mem_image.mp (show E ∈ t.image (fun q => q.1.1) from hE)
    exact ⟨q.2.1, q.1.2, q.2.2.trans Set.inter_subset_right⟩
  set f : ∀ E : ↥C.covers, presheafValue E.1 := fun E =>
    (s (hexE E).2.choose).1 ⟨E.1, (hexE E).1, (hexE E).2.choose_spec⟩ with hfdef
  have hfcompat : C.RationalRefinementCompatible f :=
    choiceFamily_rationalRefinementCompatible s hs C hexE
  obtain ⟨z, hz⟩ := hOn.gluing C hCrat hD₀S f (hfcompat.allData_huber hCrat)
  refine ⟨z, ?_⟩
  intro E hErat hED i hEUi
  have hEbase : rationalOpen E.T E.s ⊆ rationalOpen C.base.T C.base.s := hED
  set CE := interCoveringV E hErat C hCrat hEbase with hCEdef
  have hCErat : CE.IsRational := interCoveringV_isRational E hErat C hCrat hEbase
  have hES : rationalOpen E.T E.s ⊆ S := hED.trans hD₀S
  refine hOn.separationSub CE hCErat hES ?_
  funext q
  obtain ⟨E₀, hFeq⟩ := (mem_interCoveringPiecesV E hErat C hCrat).mp q.2
  have hFrat : q.1.IsRational := hCErat.piece q.2
  have hFE : rationalOpen q.1.T q.1.s ⊆ rationalOpen E.T E.s := CE.hsubset q.1 q.2
  have hFE₀ : rationalOpen q.1.T q.1.s ⊆ rationalOpen E₀.1.T E₀.1.s :=
    hFeq ▸ RationalLocData.interValid_subset_right _ _ _ _
  have hFU_i : spaOpen q.1 ⊆ (U i : Set ↥(Spa A A⁺)) :=
    (spaOpen_subset_of_rationalOpen_subset hFE).trans hEUi
  have hi₀ := (hexE E₀).2.choose_spec
  have hFU_i₀ : spaOpen q.1 ⊆ (U (hexE E₀).2.choose : Set ↥(Spa A A⁺)) :=
    (spaOpen_subset_of_rationalOpen_subset hFE₀).trans hi₀
  have hcompL := restrictionMap_restrictionMap D₀ E₀.1 q.1 (C.hsubset E₀.1 E₀.2) hFE₀ z
  have hcompR := restrictionMap_restrictionMap D₀ E q.1 hED hFE z
  show restrictionMap E q.1 hFE (restrictionMap D₀ E hED z) =
    restrictionMap E q.1 hFE ((s i).1 ⟨E, hErat, hEUi⟩)
  calc restrictionMap E q.1 hFE (restrictionMap D₀ E hED z)
      = restrictionMap D₀ q.1 (hFE.trans hED) z := hcompR
    _ = restrictionMap E₀.1 q.1 hFE₀ (restrictionMap D₀ E₀.1 (C.hsubset E₀.1 E₀.2) z) := hcompL.symm
    _ = restrictionMap E₀.1 q.1 hFE₀ (f E₀) := by rw [hz E₀]
    _ = (s (hexE E₀).2.choose).1 ⟨q.1, hFrat, hFU_i₀⟩ :=
        (s _).2 ⟨E₀.1, (hexE E₀).1, hi₀⟩ ⟨q.1, hFrat, hFU_i₀⟩ hFE₀
    _ = (s i).1 ⟨q.1, hFrat, hFU_i⟩ :=
        limitFamily_eval_eq s hs q.1 hFrat _ _ hFU_i₀ hFU_i
    _ = restrictionMap E q.1 hFE ((s i).1 ⟨E, hErat, hEUi⟩) :=
        ((s i).2 ⟨E, hErat, hEUi⟩ ⟨q.1, hFrat, hFU_i⟩ hFE).symm

/-- **Gluing of the all-open presheaf on arbitrary covers, `S`-relative**
(the Tate-free `exists_limitSections_glue` at `IsSheafyOn`). -/
theorem exists_limitSections_glue_on {S : Set (Spv A)} (hOn : IsSheafyOn S)
    (hcomp : ∀ D : RationalLocData A, D.IsRational → IsCompact (spaOpen D))
    {V : Opens ↥(Spa A A⁺)} (hVS : (V : Set ↥(Spa A A⁺)) ⊆ Subtype.val ⁻¹' S)
    {ι : Type*} {U : ι → Opens ↥(Spa A A⁺)}
    (hle : ∀ i, U i ≤ V) (hcov : (V : Set ↥(Spa A A⁺)) ⊆ ⋃ i, (U i : Set ↥(Spa A A⁺)))
    (s : ∀ i, ↥(limitSections (U i)))
    (hs : ∀ i j, limitRestrict (inf_le_left (a := U i) (b := U j)) (s i) =
                 limitRestrict (inf_le_right (a := U i) (b := U j)) (s j)) :
    ∃ x : ↥(limitSections V), ∀ i, limitRestrict (hle i) x = s i := by
  classical
  choose z hzchar using exists_glue_at_rational_on hOn hcomp hVS hcov s hs
  refine ⟨⟨fun D => z D.D D.isRational D.subset, ?_⟩, ?_⟩
  · intro D D' hD'D
    obtain ⟨t', ht'⟩ := exists_finite_rational_refinement_huber D'.D D'.isRational
      (hcomp D'.D D'.isRational)
      (fun i => (U i : Set ↥(Spa A A⁺))) (fun i => (U i).2) (D'.subset.trans hcov)
    set C' := refinementCovering D'.D t' ht' with hC'def
    have hC'rat : C'.IsRational := refinementCovering_isRational D'.D D'.isRational t' ht'
    refine hOn.separationSub C' hC'rat
      (RationalLocData.rationalOpen_subset_of_trace D'.subset hVS) ?_
    funext ⟨E', hE'⟩
    obtain ⟨q', hq't, rfl⟩ := Finset.mem_image.mp (show E' ∈ t'.image (fun q => q.1.1) from hE')
    have hE'rat : q'.1.1.IsRational := q'.2.1
    have hE'D' : rationalOpen q'.1.1.T q'.1.1.s ⊆ rationalOpen D'.D.T D'.D.s :=
      spaOpen_subset_iff.mp (q'.2.2.trans Set.inter_subset_left)
    have hE'U : spaOpen q'.1.1 ⊆ (U q'.1.2 : Set ↥(Spa A A⁺)) := q'.2.2.trans Set.inter_subset_right
    have hcomp' := restrictionMap_restrictionMap D.D D'.D q'.1.1 hD'D hE'D'
      (z D.D D.isRational D.subset)
    show restrictionMap D'.D q'.1.1 hE'D'
        (restrictionMap D.D D'.D hD'D (z D.D D.isRational D.subset)) =
      restrictionMap D'.D q'.1.1 hE'D' (z D'.D D'.isRational D'.subset)
    rw [hcomp', hzchar D.D D.isRational D.subset q'.1.1 hE'rat (hE'D'.trans hD'D) q'.1.2 hE'U,
      hzchar D'.D D'.isRational D'.subset q'.1.1 hE'rat hE'D' q'.1.2 hE'U]
  · intro i
    refine Subtype.ext (funext fun F => ?_)
    show z F.D F.isRational (F.subset.trans (hle i)) = (s i).1 F
    obtain ⟨tF, htF⟩ := exists_finite_rational_refinement_huber F.D F.isRational
      (hcomp F.D F.isRational)
      (fun j => (U j : Set ↥(Spa A A⁺))) (fun j => (U j).2)
      ((F.subset.trans (hle i)).trans hcov)
    set CF := refinementCovering F.D tF htF with hCFdef
    have hCFrat : CF.IsRational := refinementCovering_isRational F.D F.isRational tF htF
    refine hOn.separationSub CF hCFrat
      (RationalLocData.rationalOpen_subset_of_trace (F.subset.trans (hle i)) hVS) ?_
    funext ⟨E, hE⟩
    obtain ⟨q, hqt, rfl⟩ := Finset.mem_image.mp (show E ∈ tF.image (fun q => q.1.1) from hE)
    have hErat : q.1.1.IsRational := q.2.1
    have hEF : rationalOpen q.1.1.T q.1.1.s ⊆ rationalOpen F.D.T F.D.s :=
      spaOpen_subset_iff.mp (q.2.2.trans Set.inter_subset_left)
    have hEU : spaOpen q.1.1 ⊆ (U q.1.2 : Set ↥(Spa A A⁺)) := q.2.2.trans Set.inter_subset_right
    have hEUi : spaOpen q.1.1 ⊆ (U i : Set ↥(Spa A A⁺)) :=
      (spaOpen_subset_of_rationalOpen_subset hEF).trans (Set.Subset.trans F.subset
        (by exact fun v hv => hv))
    show restrictionMap F.D q.1.1 hEF (z F.D F.isRational (F.subset.trans (hle i))) =
      restrictionMap F.D q.1.1 hEF ((s i).1 F)
    rw [hzchar F.D F.isRational (F.subset.trans (hle i)) q.1.1 hErat hEF q.1.2 hEU,
      (s i).2 F ⟨q.1.1, hErat, hEUi⟩ hEF]
    exact limitFamily_eval_eq s hs q.1.1 hErat _ _ hEU hEUi

/-- **The arbitrary-cover topological embedding, `S`-relative**
(the Tate-free `isEmbedding_limitRestrictProd` at `IsSheafyOn`). -/
theorem isEmbedding_limitRestrictProd_on {S : Set (Spv A)} (hOn : IsSheafyOn S)
    (hcomp : ∀ D : RationalLocData A, D.IsRational → IsCompact (spaOpen D))
    {V : Opens ↥(Spa A A⁺)} (hVS : (V : Set ↥(Spa A A⁺)) ⊆ Subtype.val ⁻¹' S)
    {ι : Type*} {U : ι → Opens ↥(Spa A A⁺)}
    (hle : ∀ i, U i ≤ V) (hcov : (V : Set ↥(Spa A A⁺)) ⊆ ⋃ i, (U i : Set ↥(Spa A A⁺))) :
    Topology.IsEmbedding (limitRestrictProd hle) := by
  classical
  refine ⟨Topology.isInducing_iff_nhds.mpr fun x => le_antisymm ?_ ?_, ?_⟩
  · exact ((limitRestrictProd_continuous hle).tendsto x).le_comap
  · rw [nhds_limitSections x]
    refine le_iInf fun D => ?_
    obtain ⟨t, ht⟩ := exists_finite_rational_refinement_huber D.D D.isRational
      (hcomp D.D D.isRational)
      (fun i => (U i : Set ↥(Spa A A⁺))) (fun i => (U i).2) (D.subset.trans hcov)
    exact comap_limitRestrictProd_le_comap_eval hle x D ht
      (hOn.embedding _ (refinementCovering_isRational D.D D.isRational t ht)
        (RationalLocData.rationalOpen_subset_of_trace D.subset hVS))
  · intro x y hxy
    exact limitRestrict_injective_on hOn hcomp hVS hle hcov
      fun i => congr_fun hxy i

universe u

/-- **The subset-relative all-open sheaf condition** (the `S`-guarded
`IsLimitSheaf`): the three fields for opens inside the trace of `S`. -/
structure IsLimitSheafOn {A : Type u} [CommRing A] [TopologicalSpace A]
    [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]
    (S : Set (Spv A)) : Prop where
  injective : ∀ {V : Opens ↥(Spa A A⁺)},
    ((V : Set ↥(Spa A A⁺)) ⊆ Subtype.val ⁻¹' S) →
    ∀ {ι : Type u} {U : ι → Opens ↥(Spa A A⁺)}
    (hle : ∀ i, U i ≤ V),
    ((V : Set ↥(Spa A A⁺)) ⊆ ⋃ i, (U i : Set ↥(Spa A A⁺))) →
    ∀ {x y : ↥(limitSections V)},
    (∀ i, limitRestrict (hle i) x = limitRestrict (hle i) y) → x = y
  glue : ∀ {V : Opens ↥(Spa A A⁺)},
    ((V : Set ↥(Spa A A⁺)) ⊆ Subtype.val ⁻¹' S) →
    ∀ {ι : Type u} {U : ι → Opens ↥(Spa A A⁺)}
    (hle : ∀ i, U i ≤ V),
    ((V : Set ↥(Spa A A⁺)) ⊆ ⋃ i, (U i : Set ↥(Spa A A⁺))) →
    ∀ (s : ∀ i, ↥(limitSections (U i))),
    (∀ i j, limitRestrict (inf_le_left (a := U i) (b := U j)) (s i) =
            limitRestrict (inf_le_right (a := U i) (b := U j)) (s j)) →
    ∃ x : ↥(limitSections V), ∀ i, limitRestrict (hle i) x = s i
  isEmbedding : ∀ {V : Opens ↥(Spa A A⁺)},
    ((V : Set ↥(Spa A A⁺)) ⊆ Subtype.val ⁻¹' S) →
    ∀ {ι : Type u} {U : ι → Opens ↥(Spa A A⁺)}
    (hle : ∀ i, U i ≤ V),
    ((V : Set ↥(Spa A A⁺)) ⊆ ⋃ i, (U i : Set ↥(Spa A A⁺))) →
    Topology.IsEmbedding (limitRestrictProd hle)

/-- The subset-relative finite rational criterion implies the subset-relative
all-open condition (the Tate-free `isLimitSheaf_of_isSheafy`). -/
theorem isLimitSheafOn_of_isSheafyOn {A : Type u} [CommRing A]
    [TopologicalSpace A] [PlusSubring A] [IsHuberRing A] [DecidableEq A]
    [DecidableEq (RationalLocData A)]
    [IsRingOfIntegralElements (A⁺ : Subring A)] [HasLocLiftPowerBounded A]
    [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    {S : Set (Spv A)} (hOn : IsSheafyOn S)
    (hcomp : ∀ D : RationalLocData A, D.IsRational → IsCompact (spaOpen D)) :
    IsLimitSheafOn S :=
  { injective := fun {V} hVS {ι U} hle hcov {_x _y} h =>
      limitRestrict_injective_on hOn hcomp hVS hle hcov h
    glue := fun {V} hVS {ι U} hle hcov s hs =>
      exists_limitSections_glue_on hOn hcomp hVS hle hcov s hs
    isEmbedding := fun {V} hVS {ι U} hle hcov =>
      isEmbedding_limitRestrictProd_on hOn hcomp hVS hle hcov }

/-- **The `Hom`-gluing core, `S`-relative** (the guarded `IsLimitSheaf.homGlue`):
compatible families of continuous ring homomorphisms into the sections over an
open cover inside the trace of `S` glue uniquely. -/
theorem IsLimitSheafOn.homGlue {A : Type u} [CommRing A] [TopologicalSpace A]
    [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]
    {S : Set (Spv A)} (h : IsLimitSheafOn S)
    {T : Type u} [CommRing T] [TopologicalSpace T]
    {V : Opens ↥(Spa A A⁺)} (hVS : (V : Set ↥(Spa A A⁺)) ⊆ Subtype.val ⁻¹' S)
    {ι : Type u} {U : ι → Opens ↥(Spa A A⁺)}
    (hle : ∀ i, U i ≤ V)
    (hcov : (V : Set ↥(Spa A A⁺)) ⊆ ⋃ i, (U i : Set ↥(Spa A A⁺)))
    (f : ∀ i, T →+* ↥(limitSections (U i))) (hfc : ∀ i, Continuous (f i))
    (hcompat : ∀ i j, (limitRestrict (inf_le_left (a := U i) (b := U j))).comp (f i) =
        (limitRestrict (inf_le_right (a := U i) (b := U j))).comp (f j)) :
    ∃! g : {g : T →+* ↥(limitSections V) // Continuous g},
      ∀ i, (limitRestrict (hle i)).comp g.1 = f i := by
  classical
  have hglue : ∀ t : T, ∃ x : ↥(limitSections V),
      ∀ i, limitRestrict (hle i) x = f i t := by
    intro t
    exact h.glue hVS hle hcov (fun i => f i t)
      (fun i j => DFunLike.congr_fun (hcompat i j) t)
  choose g₀ hg₀ using hglue
  have huniq : ∀ (x y : ↥(limitSections V)),
      (∀ i, limitRestrict (hle i) x = limitRestrict (hle i) y) → x = y :=
    fun x y hxy => h.injective hVS hle hcov hxy
  have hg_add : ∀ t₁ t₂, g₀ (t₁ + t₂) = g₀ t₁ + g₀ t₂ := by
    intro t₁ t₂
    refine huniq _ _ fun i => ?_
    rw [hg₀ (t₁ + t₂) i, map_add, map_add, hg₀ t₁ i, hg₀ t₂ i]
  have hg_mul : ∀ t₁ t₂, g₀ (t₁ * t₂) = g₀ t₁ * g₀ t₂ := by
    intro t₁ t₂
    refine huniq _ _ fun i => ?_
    rw [hg₀ (t₁ * t₂) i, map_mul, map_mul, hg₀ t₁ i, hg₀ t₂ i]
  have hg_one : g₀ 1 = 1 := by
    refine huniq _ _ fun i => ?_
    rw [hg₀ 1 i, map_one, map_one]
  have hg_zero : g₀ 0 = 0 := by
    refine huniq _ _ fun i => ?_
    rw [hg₀ 0 i, map_zero, map_zero]
  set g : T →+* ↥(limitSections V) :=
    { toFun := g₀, map_one' := hg_one, map_mul' := hg_mul,
      map_zero' := hg_zero, map_add' := hg_add } with hgdef
  have hgc : Continuous g := by
    rw [(h.isEmbedding hVS hle hcov).isInducing.continuous_iff]
    have : limitRestrictProd hle ∘ g = fun t i => f i t := by
      funext t i
      exact hg₀ t i
    rw [this]
    exact continuous_pi fun i => (hfc i)
  refine ⟨⟨g, hgc⟩, fun i => RingHom.ext fun t => hg₀ t i, ?_⟩
  rintro ⟨g', hg'c⟩ hg'
  refine Subtype.ext (RingHom.ext fun t => ?_)
  refine huniq _ _ fun i => ?_
  exact (DFunLike.congr_fun (hg' i) t).trans (hg₀ t i).symm

end ValuationSpectrum

end

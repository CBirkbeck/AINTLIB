/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.FiniteJetSheafTransfer
import «Adic spaces».MilnorSheafTransfer

/-!
# The finite-jet square as a `MilnorSquareData` (campaign B, T620)

Instantiates the abstract strict-Milnor-descent criterion
(`isSheafy_of_milnorSquare`) at the finite-jet square
`𝓐 = 𝓑 ×_𝓓 𝓒` — the regression target re-deriving `isSheafy_JetA` through the
abstract criterion, and the template for the `⟨V₁,…,Vₙ⟩`-extended square.

The pushes are the rationality-gated `pushDatum*` constructors behind a
classical `dite` (the abstract laws only quantify over rational data, where
`dif_pos` collapses the gate). The value maps are definitionally the generic
`presheafValueMapOfHom` (that is how `presheafValueMap*` are defined).
-/

@[expose] public section

noncomputable section

namespace FiniteJet

open ValuationSpectrum TopologicalRing

variable (F : Type*) [Field F]

open Classical in
/-- The total `B`-push: `pushDatumB` on rational data, a trivial datum elsewhere. -/
noncomputable def jetPushB : RationalLocData (JetA F) → RationalLocData (JetB F) :=
  fun D => if h : D.IsRational then pushDatumB D h else trivialPlusDatum (JetB F) (podB F) 1

open Classical in
/-- The total `C`-push. -/
noncomputable def jetPushC : RationalLocData (JetA F) → RationalLocData (JetC F) :=
  fun D => if h : D.IsRational then pushDatumC D h else trivialPlusDatum (JetC F) (podC F) 1

open Classical in
/-- The total `D`-push. -/
noncomputable def jetPushD : RationalLocData (JetA F) → RationalLocData (JetD F) :=
  fun D => if h : D.IsRational then pushDatumD D h else trivialPlusDatum (JetD F) (podD F) 1

theorem jetPushB_eq {D : RationalLocData (JetA F)} (hD : D.IsRational) :
    jetPushB F D = pushDatumB D hD := by
  simp [jetPushB, dif_pos hD]

theorem jetPushC_eq {D : RationalLocData (JetA F)} (hD : D.IsRational) :
    jetPushC F D = pushDatumC D hD := by
  simp [jetPushC, dif_pos hD]

theorem jetPushD_eq {D : RationalLocData (JetA F)} (hD : D.IsRational) :
    jetPushD F D = pushDatumD D hD := by
  simp [jetPushD, dif_pos hD]

/-- **The finite-jet square as a strict Milnor square-with-rows.** -/
noncomputable def jetSquare :
    MilnorSquareData (jB F) (iotaC F) ((rhoC F).comp (iotaC F))
      (continuous_jB) (continuous_iotaC)
      (by rw [RingHom.coe_comp]; exact (continuous_rhoC).comp (continuous_iotaC)) where
  pushB := jetPushB F
  pushC := jetPushC F
  pushD := jetPushD F
  pushB_s := by
    intro U hU
    rw [jetPushB_eq F hU]
    rfl
  pushC_s := by
    intro U hU
    rw [jetPushC_eq F hU]
    rfl
  pushD_s := by
    intro U hU
    rw [jetPushD_eq F hU]
    rfl
  pushB_T := by
    classical
    intro U hU t ht
    rw [jetPushB_eq F hU]
    exact Finset.mem_image_of_mem _ ht
  pushC_T := by
    classical
    intro U hU t ht
    rw [jetPushC_eq F hU]
    exact Finset.mem_image_of_mem _ ht
  pushD_T := by
    classical
    intro U hU t ht
    rw [jetPushD_eq F hU]
    exact Finset.mem_image_of_mem _ ht
  pushB_isRational := by
    intro U hU
    rw [jetPushB_eq F hU]
    exact pushDatumB_isRational hU
  pushC_isRational := by
    intro U hU
    rw [jetPushC_eq F hU]
    exact pushDatumC_isRational hU
  pushD_isRational := by
    intro U hU
    rw [jetPushD_eq F hU]
    exact pushDatumD_isRational hU
  legB := rhoB F
  legC := rhoC F
  hlegB := continuous_rhoB
  hlegC := continuous_rhoC
  legB_s := by sorry
  legC_s := by sorry
  legB_T := by sorry
  legC_T := by sorry
  row_injective := by sorry
  row_glue := by sorry
  row_embedding := by sorry
  pushB_mono := by sorry
  pushC_mono := by sorry
  push_natural_B := by sorry
  push_natural_C := by sorry
  pushB_cover := by sorry
  pushC_cover := by sorry
  pushD_cover := by sorry
  pushD_mono := by sorry
  leg_natural_B := by sorry
  leg_natural_C := by sorry
  row_comm := by sorry
  pushedCompat_B := by sorry
  pushedCompat_C := by sorry

end FiniteJet

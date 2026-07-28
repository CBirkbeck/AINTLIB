/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WP.CoeffLocalization
import «Adic spaces».SheafyRing
import «Adic spaces».StructureSheaf
import «Adic spaces».SheafyEndpoints
import «Adic spaces».RelativeStandardRefinement
import «Adic spaces».StructurePresheafBundled

/-!
# `𝒜` is (strongly) sheafy ([WP] §6.5, thm:parity-strongly-sheafy)

The two `IsSheafy` fields (finite rational covers: topological embedding + gluing)
are produced by the finite-head Čech argument:

1. Push the covering data into one head: scale entries into the unit ball, choose
   integral Bezout relations, approximate by head elements (density,
   `exists_head_approx`) and apply the small perturbation lemma — none of this
   changes the rational subsets or the section rings ([WP] proof of
   thm:parity-strongly-sheafy, first two paragraphs).
2. The pushed data are rational in the head `P_M` (apply the coefficient retraction
   `ρ_M` to the Bezout relation), and the corresponding rational subsets COVER
   `Spa(P_M, P_M°)` — via the split surjection
   `Spa(E,E°) → Spa(P_M,P_M°)` induced by the isometric pair
   `P_M → E → P_M` ([WP], "We verify that the `V_i` cover", eq:split-spectrum-map;
   the paper warns: do NOT identify `U` with the maximal-pair spectrum).
3. The head is sheafy (Wedhorn 8.28(b), `isSheafy_WPHead`); its Čech equalizer
   isomorphism has a BOUNDED inverse (closed range + open mapping — the no-Baire
   route `isInducing_of_closedRange_of_topNilpUnit` of `WedhornBanachTheorem.lean`,
   at the normed model `QHead`); gluing then proceeds coefficientwise with uniform
   norm control, and the glued family is again null
   ([WP] eq:head-cech, eq:coefficientwise-gluing-bound).

**Strong sheafiness**: the whole construction is uniform in the weight `w`; the Tate
extension `𝒜⟨V_1,…,V_s⟩` is the weighted-parity algebra at the shifted weight
(`shiftWeight`), so `isSheafy_WPA` applied at `shiftWeight w s` gives sheafiness of
every finite Tate extension ([WP] eq:strong-sheafy-decomposition: "the preceding
proof applies verbatim").  The bridge to the project's own Tate-extension
(`restrictedMvPowerSeriesSubring`) is `tateExtEquiv`.
-/

@[expose] public section

namespace WeightedParity

open ValuationSpectrum FiniteJetOver

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (w : ℕ → ℕ)

variable {K w} in
/-- The embedding half of the sheaf condition for `𝒜` (the
`productRestrictionSub_isEmbedding_JetA` shape, `FJP/Over/SheafTransfer.lean:667`). -/
theorem productRestrictionSub_isEmbedding_WPA (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (C : RationalCoveringData (WPA K w)) (hC : C.IsRational) :
    Topology.IsEmbedding (productRestrictionSub (WPA K w) C) := by sorry

variable {K w} in
/-- The gluing half of the sheaf condition for `𝒜` (the `gluing_JetA` shape,
`FJP/Over/SheafTransfer.lean:376`; [WP] proof of thm:parity-strongly-sheafy,
coefficientwise Čech gluing with the head bound `C`). -/
theorem gluing_WPA (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (C : RationalCoveringData (WPA K w)) (hC : C.IsRational)
    (f : ∀ D : ↥C.covers, presheafValue D.1)
    (hcompat : ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData (WPA K w))
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) :
    ∃ x : presheafValue C.base, ∀ D : ↥C.covers,
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D := by sorry

variable {K w} in
/-- **`𝒜` is sheafy** — the finite-rational-cover form
([WP] thm:parity-strongly-sheafy; the `isSheafy_JetA` assembly,
`FJP/Over/SheafTransfer.lean:730`). -/
theorem isSheafy_WPA (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    ValuationSpectrum.IsSheafy (WPA K w) where
  embedding := fun C hC => productRestrictionSub_isEmbedding_WPA ϖ hK₀ C hC
  gluing := fun C hC f hcompat => gluing_WPA ϖ hK₀ C hC f hcompat

/-- The distinguished ring of integral elements: the power-bounded subring
(the `finiteJetPlus` pattern, `FJP/Over/SheafyEndpoints.lean:87`). -/
noncomputable def wpPlus : RingOfIntegralElements (WPA K w) :=
  ⟨((WPA K w)⁺ : Subring (WPA K w)), inferInstance⟩

variable {K w} in
/-- **Pair-level sheafiness** ([WP] thm 6.2 (2), one pair; the
`finiteJet_isSheafyFor` pivot, `FJP/Over/SheafyEndpoints.lean:95`). -/
theorem wp_isSheafyFor (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsSheafyFor (WPA K w) (wpPlus K w) := by sorry

variable {K w} in
/-- **All-pairs sheafiness** (via the unconditional `A⁺`-independence
`isSheafyFor_iff_isSheafyComplete`). -/
theorem wp_isSheafyComplete (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsSheafyComplete (WPA K w) := by sorry

variable {K w} in
theorem wp_isSheafyFor_all (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (Bplus : RingOfIntegralElements (WPA K w)) :
    IsSheafyFor (WPA K w) Bplus :=
  wp_isSheafyComplete ϖ hK₀ Bplus

variable {K w} in
/-- The genuine all-open structure presheaf of `Spa(𝒜, B⁺)` is a sheaf, for every
valid `B⁺` (the `finiteJet_structurePresheaf_isSheaf_all` shape,
`FJP/Over/SheafyEndpoints.lean:213`). -/
theorem wp_structurePresheaf_isSheaf_all (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (Bplus : RingOfIntegralElements (WPA K w)) :
    letI := Bplus.toPlusSubring
    haveI : IsRingOfIntegralElements ((WPA K w)⁺ : Subring (WPA K w)) := Bplus.2
    haveI : HasLocLiftPowerBounded (WPA K w) := hasLocLiftPowerBounded_faithful
    (ValuationSpectrum.structurePresheaf (WPA K w)).IsSheaf := by sorry

/-! ### Strong sheafiness ([WP] thm:parity-strongly-sheafy, last paragraph) -/

variable {K w} in
/-- Sheafiness of every shifted-weight algebra — the Tate extensions in the concrete
model ([WP] eq:strong-sheafy-decomposition: "the preceding proof applies verbatim").
This is `isSheafy_WPA` at the shifted weight; recorded as its own statement because
it is the mathematical content of strong sheafiness. -/
theorem isSheafy_WPA_shiftWeight (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) (s : ℕ) :
    ValuationSpectrum.IsSheafy (WPA K (shiftWeight w s)) :=
  isSheafy_WPA ϖ hK₀

variable {K w} in
/-- The bridge between the project's Tate extension of `𝒜` and the shifted-weight
weighted-parity algebra: `𝒜⟨V_1,…,V_s⟩ ≅ WPA (shiftWeight w s)` (Fubini + reindex
of restricted power series; nested-vs-flat plumbing). -/
noncomputable def tateExtEquiv (s : ℕ) :
    ↥(restrictedMvPowerSeriesSubring s (WPA K w)) ≃+* WPA K (shiftWeight w s) := by
  sorry

-- The topological refinement of `tateExtEquiv` (bicontinuity for the project's
-- Tate-algebra topology on `restrictedMvPowerSeriesSubring`, cf.
-- `MvTateAlgebraTopology`) is specified at ticket level; the bare subtype carries no
-- `TopologicalSpace` instance, so the statement needs the `mvTateAlgebraTopology'`
-- `letI` and is deferred to execution.

variable {K w} in
/-- **Strong sheafiness** ([WP] thm 6.2 (2): "(𝒜,𝒜°) is strongly sheafy"): for every
`s`, the weighted-parity model of the Tate extension `𝒜⟨V_1,…,V_s⟩` is sheafy for
every valid ring of integral elements.  Combined with the identification
`tateExtEquiv` this is the statement in the project's own Tate-extension
vocabulary. -/
theorem wp_stronglySheafy (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) (s : ℕ) :
    IsSheafyComplete (WPA K (shiftWeight w s)) :=
  wp_isSheafyComplete ϖ hK₀

end WeightedParity

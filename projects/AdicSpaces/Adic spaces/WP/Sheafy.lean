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

/-- The forward slot map of the Tate-extension bridge. -/
def slotTo (s : ℕ) (n : ℕ) : Fin s ⊕ ℕ :=
  if h : 1 ≤ n ∧ n ≤ s then Sum.inl ⟨n - 1, by omega⟩
  else if n = 0 then Sum.inr 0 else Sum.inr (n - s)

/-- The inverse slot map. -/
def slotInv (s : ℕ) : Fin s ⊕ ℕ → ℕ
  | Sum.inl i => i.1 + 1
  | Sum.inr m => if m = 0 then 0 else m + s

/-- The interleaving slot bijection of the Tate-extension bridge: `0 ↦ inr 0`,
`i ∈ [1..s] ↦ inl (i−1)`, `n > s ↦ inr (n−s)` (the exponent-side realization of
`shiftWeight`: the freed slots `1..s` carry the new Tate variables). -/
def slotEquiv (s : ℕ) : ℕ ≃ (Fin s ⊕ ℕ) where
  toFun := slotTo s
  invFun := slotInv s
  left_inv n := by
    simp only [slotTo]
    split_ifs with h1 h2
    · show n - 1 + 1 = n
      omega
    · show (if (0 : ℕ) = 0 then 0 else 0 + s) = n
      rw [if_pos rfl]
      omega
    · show (if n - s = 0 then 0 else n - s + s) = n
      rw [if_neg (by omega)]
      omega
  right_inv x := by
    rcases x with i | m
    · show slotTo s (i.1 + 1) = Sum.inl i
      simp only [slotTo]
      rw [dif_pos ⟨by omega, by have := i.2; omega⟩]
      congr 1
    · by_cases hm : m = 0
      · subst hm
        show slotTo s (if (0 : ℕ) = 0 then 0 else 0 + s) = Sum.inr 0
        rw [if_pos rfl]
        simp [slotTo]
      · show slotTo s (if m = 0 then 0 else m + s) = Sum.inr m
        rw [if_neg hm]
        simp only [slotTo]
        rw [dif_neg (by omega), if_neg (by omega)]
        congr 1
        omega

variable {K} in
/-- Stage 1 of the Tate-extension bridge: the ambient flatten
`(MvPowerSeries ℕ K)⟦Fin s⟧ ≅ K⟦Fin s ⊕ ℕ⟧ ≅ K⟦ℕ⟧` (Xia `sumAlgEquiv` +
mathlib `renameEquiv` along `slotEquiv`). -/
noncomputable def tateExtAmbient (s : ℕ) :
    MvPowerSeries (Fin s) (MvPowerSeries ℕ K) ≃+* MvPowerSeries ℕ K :=
  ((MvPowerSeries.sumAlgEquiv (Fin s) ℕ K).symm.trans
    (MvPowerSeries.renameEquiv K (slotEquiv s).symm)).toRingEquiv

variable {K} in
/-- Coefficients of the ambient flatten: transport the exponent through
`slotEquiv` and read the nested coefficient. -/
theorem tateExtAmbient_coeff (s : ℕ)
    (F : MvPowerSeries (Fin s) (MvPowerSeries ℕ K)) (u : ℕ →₀ ℕ) :
    MvPowerSeries.coeff u (tateExtAmbient (K := K) s F) =
      MvPowerSeries.coeff
        (Finsupp.comapDomain Sum.inr (Finsupp.equivMapDomain (slotEquiv s) u)
          Sum.inr_injective.injOn)
        (MvPowerSeries.coeff
          (Finsupp.comapDomain Sum.inl (Finsupp.equivMapDomain (slotEquiv s) u)
            Sum.inl_injective.injOn) F) := by
  have hu : u = Finsupp.embDomain (slotEquiv s).symm.toEmbedding
      (Finsupp.equivMapDomain (slotEquiv s) u) := by
    rw [Finsupp.embDomain_eq_mapDomain,
      show (⇑((slotEquiv s).symm.toEmbedding) : (Fin s ⊕ ℕ) → ℕ) =
        ⇑(slotEquiv s).symm from rfl,
      ← Finsupp.equivMapDomain_eq_mapDomain, ← Finsupp.equivMapDomain_trans,
      Equiv.self_trans_symm, Finsupp.equivMapDomain_refl]
  show MvPowerSeries.coeff u
    (MvPowerSeries.rename (⇑((slotEquiv s).symm.toEmbedding))
      ((MvPowerSeries.sumAlgEquiv (Fin s) ℕ K).symm F)) = _
  conv_lhs => rw [hu]
  rw [MvPowerSeries.coeff_embDomain_rename]
  rfl

variable {K w} in
/-- The coefficient-value hom `𝒜 → K⟦U⟧` (two subtype layers). -/
noncomputable def wpaVal : WPA K w →+* MvPowerSeries ℕ K :=
  ((MvPowerSeries.isSubring (R := K) (fun _ : ℕ => (1 : ℝ))).subtype).comp
    ((wpSupport K w).subtype)

variable {K w} in
theorem wpaVal_injective : Function.Injective (wpaVal (K := K) (w := w)) := by
  intro a b hab
  have h1 : a.1.1 = b.1.1 := hab
  exact Subtype.ext (Subtype.ext h1)

variable {K w} in
/-- The flatten hom on the nested Tate extension (stage 2 of the bridge). -/
noncomputable def tateExtToFlat (s : ℕ) :
    ↥(restrictedMvPowerSeriesSubring s (WPA K w)) →+* MvPowerSeries ℕ K :=
  ((tateExtAmbient (K := K) s).toRingHom.comp
    (MvPowerSeries.map (wpaVal (K := K) (w := w)))).comp
    (restrictedMvPowerSeriesSubring s (WPA K w)).subtype

variable {K w} in
theorem tateExtToFlat_injective (s : ℕ) :
    Function.Injective (tateExtToFlat (K := K) (w := w) s) := by
  rw [tateExtToFlat, RingHom.coe_comp, RingHom.coe_comp]
  refine Function.Injective.comp (Function.Injective.comp ?_ ?_) ?_
  · exact (tateExtAmbient (K := K) s).injective
  · exact MvPowerSeries.map_injective (wpaVal_injective (K := K) (w := w))
  · exact Subring.subtype_injective _

variable {K w} in
/-- Coefficients of the flatten hom: nested coefficient values at the
slot-transported exponent. -/
theorem tateExtToFlat_coeff (s : ℕ)
    (F : ↥(restrictedMvPowerSeriesSubring s (WPA K w))) (u : ℕ →₀ ℕ) :
    MvPowerSeries.coeff u (tateExtToFlat (K := K) (w := w) s F) =
      MvPowerSeries.coeff
        (Finsupp.comapDomain Sum.inr (Finsupp.equivMapDomain (slotEquiv s) u)
          Sum.inr_injective.injOn)
        (wpaVal (K := K) (w := w)
          (MvPowerSeries.coeff
            (Finsupp.comapDomain Sum.inl
              (Finsupp.equivMapDomain (slotEquiv s) u)
              Sum.inl_injective.injOn) F.1)) := by
  rw [show tateExtToFlat (K := K) (w := w) s F =
    tateExtAmbient (K := K) s
      (MvPowerSeries.map (wpaVal (K := K) (w := w)) F.1) from rfl,
    tateExtAmbient_coeff, MvPowerSeries.coeff_map]

/-- The `inr`-pull of a flat exponent through the slot bijection. -/
noncomputable def slotInr (s : ℕ) (u : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  Finsupp.comapDomain Sum.inr (Finsupp.equivMapDomain (slotEquiv s) u)
    Sum.inr_injective.injOn

theorem slotInr_apply (s : ℕ) (u : ℕ →₀ ℕ) (m : ℕ) :
    slotInr s u m = u (if m = 0 then 0 else m + s) := by
  rw [slotInr, Finsupp.comapDomain_apply, Finsupp.equivMapDomain_apply]
  by_cases hm : m = 0
  · subst hm
    rw [if_pos rfl]
    rfl
  · rw [if_neg hm]
    show u ((slotEquiv s).symm (Sum.inr m)) = u (m + s)
    congr 1
    show slotInv s (Sum.inr m) = m + s
    simp only [slotInv]
    rw [if_neg hm]

theorem slotInr_zero_apply (s : ℕ) (u : ℕ →₀ ℕ) : slotInr s u 0 = u 0 := by
  rw [slotInr_apply, if_pos rfl]

/-- The parity weight at the shifted weight is computed by the `inr`-pull
(the freed slots `1..s` have weight `0`). -/
theorem wpWeight_shiftWeight_eq (w : ℕ → ℕ) (s : ℕ) (u : ℕ →₀ ℕ) :
    wpWeight (shiftWeight w s) u = wpWeight w (slotInr s u) := by
  classical
  have hL : wpWeight (shiftWeight w s) u =
      ∑ n ∈ u.support.filter (fun n => u n % 2 = 1 ∧ s < n), w (n - s) := by
    rw [wpWeight, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h1 : u n % 2 = 1 ∧ n ≠ 0
    · rw [if_pos h1]
      by_cases h2 : s < n
      · rw [if_pos ⟨h1.1, h2⟩]
        show (if n ≤ s then 0 else w (n - s)) = w (n - s)
        rw [if_neg (by omega)]
      · rw [if_neg (fun hc => h2 hc.2)]
        show (if n ≤ s then 0 else w (n - s)) = 0
        rw [if_pos (by omega)]
    · rw [if_neg h1, if_neg (fun hc => h1 ⟨hc.1, by omega⟩)]
  have hR : wpWeight w (slotInr s u) =
      ∑ m ∈ (slotInr s u).support.filter
        (fun m => slotInr s u m % 2 = 1 ∧ m ≠ 0), w m := by
    rw [wpWeight, Finset.sum_filter]
  rw [hL, hR]
  refine Finset.sum_nbij' (fun n => n - s) (fun m => m + s) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter] at hn ⊢
    have hv : slotInr s u (n - s) = u n := by
      rw [slotInr_apply, if_neg (by omega),
        show n - s + s = n from by omega]
    refine ⟨Finsupp.mem_support_iff.mpr ?_, ?_, by omega⟩
    · rw [hv]
      exact Finsupp.mem_support_iff.mp hn.1
    · rw [hv]
      exact hn.2.1
  · intro m hm
    rw [Finset.mem_filter] at hm ⊢
    have hv : slotInr s u m = u (m + s) := by
      rw [slotInr_apply, if_neg hm.2.2]
    refine ⟨Finsupp.mem_support_iff.mpr ?_, ?_, by omega⟩
    · rw [← hv]
      exact Finsupp.mem_support_iff.mp hm.1
    · rw [← hv]
      exact hm.2.1
  · intro n hn
    rw [Finset.mem_filter] at hn
    omega
  · intro m hm
    rw [Finset.mem_filter] at hm
    omega
  · intro n _
    rfl

/-- Membership transport for the support condition along the slot bijection. -/
theorem wpMem_shiftWeight_iff (w : ℕ → ℕ) (s : ℕ) (u : ℕ →₀ ℕ) :
    WPMem (shiftWeight w s) u ↔ WPMem w (slotInr s u) := by
  rw [WPMem, WPMem, wpWeight_shiftWeight_eq, slotInr_zero_apply]

variable {K w} in
/-- The flatten hom lands in the shifted-weight support: coefficients vanish off
`WPMem (shiftWeight w s)` (the support condition of the nested `𝒜`-coefficient,
transported along the slot bijection). -/
theorem tateExtToFlat_support (s : ℕ)
    (F : ↥(restrictedMvPowerSeriesSubring s (WPA K w))) (u : ℕ →₀ ℕ)
    (hu : ¬ WPMem (shiftWeight w s) u) :
    MvPowerSeries.coeff u (tateExtToFlat (K := K) (w := w) s F) = 0 := by
  rw [tateExtToFlat_coeff]
  have hX := (MvPowerSeries.coeff
    (Finsupp.comapDomain Sum.inl (Finsupp.equivMapDomain (slotEquiv s) u)
      Sum.inl_injective.injOn) F.1).2
  exact hX (slotInr s u)
    (fun hc => hu ((wpMem_shiftWeight_iff w s u).mpr hc))

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

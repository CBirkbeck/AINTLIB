/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.FDBoundaryReparametrization
import LeanModularForms.ForMathlib.FDWindingDataFullSeg1Seg4
import LeanModularForms.ForMathlib.ResidueSide

/-!
# Fully-ForMathlib Valence Formula (via bridged residue/modular sides)

This file combines:
- `valence_formula_unconditional_mkD` (the top-level valence formula with
  `mkD` baked in, requiring residue/modular side Tendsto hypotheses)
- the old-chain residue/modular sides `cpv_residue_side_forMathlib` /
  `cpv_modular_side_forMathlib`, converted on the fly via
  `hasCauchyPVOn_of_cauchyPVOn'_tendsto` from
  `FDBoundaryReparametrization.lean`

The end result is a ForMathlib-native, axiom-clean final valence formula
theorem that requires only `hf : f ≠ 0` as input.

## Main result

* `valence_formula_textbook_unconditional_FM` — the fully unconditional
  valence formula in the ForMathlib chain
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-- The integrand combining residue and modular sides:
`F_int_FM f S H ε = ∫ t in 0..1, cpvIntegrandOn (sArcOfS S ∪ sVertOfS S) (logDeriv f) γ.extend ε t`
where `γ = (fdWindingDataFull_unconditional hH).boundary`, or `0` when `H ≤ 1`. -/
private def F_int_FM (S : Finset UpperHalfPlane) (H : ℝ) (ε : ℝ) : ℂ :=
  if hH : 1 < H then
    ∫ t in (0 : ℝ)..1,
      cpvIntegrandOn (sArcOfS S ∪ sVertOfS S)
        (logDeriv (modularFormCompOfComplex f))
        (fdWindingDataFull_unconditional hH).boundary.toPath.extend ε t
  else 0

/-- Per-point bridge from `generalizedWindingNumber'` to `generalizedWindingNumber`
for points of `𝒟` below height `H`, splitting into the three elliptic points,
strict interior, and the remaining boundary case. -/
private lemma gwnPrime_eq_gwn_of_mem_fd {H : ℝ} (hH : 1 < H)
    {s : UpperHalfPlane} (hs_fd : s ∈ 𝒟) (hs_im_lt : (s : ℂ).im < H) :
    generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) =
      generalizedWindingNumber (fdWindingDataFull_unconditional hH).boundary (↑s : ℂ) := by
  set D := fdWindingDataFull_unconditional hH
  set γ := D.boundary
  have hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t := D.boundary_eq
  suffices h : ∃ w : ℂ, HasGeneralizedWindingNumber γ (↑s : ℂ) w by
    obtain ⟨w, h_gwn⟩ := h
    exact (generalizedWindingNumberPrime_eq_of_hasGeneralizedWindingNumber γ hγ h_gwn).trans
      h_gwn.eq.symm
  by_cases hsi : (s : ℂ) = I
  · exact ⟨-1/2, hsi ▸ D.winding_at_i⟩
  by_cases hsρ : (s : ℂ) = ellipticPointRho
  · exact ⟨-1/6, hsρ ▸ D.winding_at_rho⟩
  by_cases hsρ1 : (s : ℂ) = ellipticPointRhoPlusOne
  · exact ⟨-1/6, hsρ1 ▸ D.winding_at_rho_plus_one⟩
  by_cases hint : ‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2
  · exact ⟨-1, D.toFDWindingData.interior_winding (↑s : ℂ) hint.1 hint.2 s.2 hs_im_lt⟩
  · exact ⟨-1/2, D.boundary_winding (↑s : ℂ) s.2 hs_im_lt hsi hsρ hsρ1 hint hs_fd.1 hs_fd.2⟩

include hf in
/-- **Final unconditional valence formula**, combining
`valence_formula_unconditional_mkD` with the residue and modular side
`Tendsto` results `cpv_residue_side_forMathlib` / `cpv_modular_side_forMathlib`,
converted on the fly into `HasCauchyPVOn` form via
`hasCauchyPVOn_of_cauchyPVOn'_tendsto`. -/
theorem valence_formula_textbook_unconditional_FM
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (H_S : ℝ) (hH_S : ∀ s ∈ S, (s : ℂ).im < H_S) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne' ∧
        ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2),
      ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ sLeftVertFM S, ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
      ↑(orderOfVanishingAt' (⇑f) s) =
    (k : ℂ) / 12 := by
  obtain ⟨H₀_res, hH₀_res, h_res_old⟩ :=
    cpv_residue_side_forMathlib f hf S hS hS_complete
  obtain ⟨H₀_mod, hH₀_mod, h_mod_old⟩ :=
    cpv_modular_side_forMathlib f hf S hS hS_complete
  set M := max (max (max H₀_res H₀_mod) H_S) 1
  set H_res := M + 1
  have hM_res : H₀_res ≤ M := by simp [M]
  have hM_mod : H₀_mod ≤ M := by simp [M]
  have hM_S : H_S ≤ M := by simp [M]
  have hM_one : (1 : ℝ) ≤ M := by simp [M]
  have hH_res_gt : (1 : ℝ) < H_res := by linarith
  have hH₀_res_le : H₀_res ≤ H_res := by linarith
  have hH₀_mod_le : H₀_mod ≤ H_res := by linarith
  have hH_S_le : H_S ≤ H_res := by linarith
  refine valence_formula_unconditional_mkD f S hS hS_complete H_S hH_S (F_int_FM f S)
    H_res hH_res_gt ?_ H_res hH_res_gt ?_
  · intro H hH_ge hH
    have hH_ge_res : H₀_res ≤ H := hH₀_res_le.trans hH_ge
    set γ := (fdWindingDataFull_unconditional hH).boundary with hγ_def
    have hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t :=
      (fdWindingDataFull_unconditional hH).boundary_eq
    have hH_above : ∀ s ∈ S, (s : ℂ).im < H := fun s hs =>
      (hH_S s hs).trans_le (hH_S_le.trans hH_ge)
    have h_sum_eq :
        (∑ s ∈ S, generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) *
          (orderOfVanishingAt' (⇑f) s : ℂ)) =
        ∑ s ∈ S, generalizedWindingNumber γ (↑s : ℂ) *
          (orderOfVanishingAt' (⇑f) s : ℂ) :=
      Finset.sum_congr rfl fun s hs => by
        rw [gwnPrime_eq_gwn_of_mem_fd hH (hS s hs) (hH_above s hs)]
    rw [← h_sum_eq]
    refine (hasCauchyPVOn_of_cauchyPVOn'_tendsto γ hγ (h_res_old hH_ge_res)).congr' ?_
    filter_upwards with ε
    simp only [F_int_FM, dif_pos hH, hγ_def]
  · intro H hH_ge hH
    have hH_ge_mod : H₀_mod ≤ H := hH₀_mod_le.trans hH_ge
    set γ := (fdWindingDataFull_unconditional hH).boundary with hγ_def
    have hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t :=
      (fdWindingDataFull_unconditional hH).boundary_eq
    refine (hasCauchyPVOn_of_cauchyPVOn'_tendsto γ hγ (h_mod_old hH_ge_mod)).congr' ?_
    filter_upwards with ε
    simp only [F_int_FM, dif_pos hH, hγ_def]

include hf in
/-- **The Valence Formula** for weight-`k` modular forms on `SL₂(ℤ)`, in textbook
finsum-over-orbits form. This is the same statement as the original
`valence_formula_textbook_orbit_finsum` in `ValenceFormula/TextbookForm.lean`,
but proved unconditionally via the new ForMathlib chain.

For any nonzero modular form `f` of weight `k` for `SL₂(ℤ)`:

$$\operatorname{ord}_\infty(f) + \tfrac{1}{2}\operatorname{ord}_i(f)
  + \tfrac{1}{3}\operatorname{ord}_\rho(f)
  + \sum_{q\;\text{non-ell}} \operatorname{ord}_q(f) = \frac{k}{12}$$
-/
theorem valence_formula_textbook_orbit_finsum_FM :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ᶠ (q : NonEllOrbitFM), ordOrbitQ f q =
    (k : ℂ) / 12 := by
  refine valence_formula_textbook_orbit_finsum f hf fun S hS hS_complete => ?_
  set H_S := S.sum (fun s : UpperHalfPlane => (s : ℂ).im) + 1
  have hH_S : ∀ s ∈ S, (s : ℂ).im < H_S := fun s hs => by
    have h_le : (s : ℂ).im ≤ S.sum (fun s : UpperHalfPlane => (s : ℂ).im) :=
      Finset.single_le_sum (f := fun s : UpperHalfPlane => (s : ℂ).im)
        (fun x _ => x.2.le) hs
    linarith
  exact valence_formula_textbook_unconditional_FM f hf S hS hS_complete H_S hH_S

end

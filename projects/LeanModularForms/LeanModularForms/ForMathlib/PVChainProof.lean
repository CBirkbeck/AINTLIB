/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.CoreIdentityProof

/-!
# PV Chain Proof

This file packages the principal-value chain identity used in the valence formula proof.

## Main definitions

* `PVChainData`: winding data, a height bound, and two limits for a common integrand.

## Main results

* `pvChainIdentity`: extracts the PV chain identity from `PVChainData`.
* `valence_formula_of_two_sides_Hgt1`: valence formula variant using data over heights `H > 1`.

## References

* Diamond--Shurman, *A First Course in Modular Forms*, Theorem 3.1.1
* Serre, *A Course in Arithmetic*, Chapter VII
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

omit f hf in
private lemma pvChain_two_pi_I_ne_zero : (2 : ℂ) * ↑Real.pi * I ≠ 0 := by
  simp [Real.pi_ne_zero]

/-- Data for the PV chain identity at height `H`, including winding data, a height
bound, and the two limits of a common integrand. -/
structure PVChainData (S : Finset UpperHalfPlane) (H : ℝ) where
  /-- The full winding data at height `H`. -/
  D : FDWindingDataFull H
  /-- All points in `S` lie below the horizontal segment. -/
  hH_above : ∀ s ∈ S, (s : ℂ).im < H
  /-- The common epsilon-dependent integrand. -/
  F_eps : ℝ → ℂ
  /-- The residue-side limit: `F_eps` converges (as `epsilon -> 0+`) to
  `2 pi i * Sigma gWN * ord`. -/
  h_res : Tendsto F_eps (𝓝[>] 0)
    (𝓝 (2 * ↑Real.pi * I *
      ∑ s ∈ S,
        generalizedWindingNumber D.boundary (↑s : ℂ) *
          (orderOfVanishingAt' (⇑f) s : ℂ)))
  /-- The modular-side limit: `F_eps` converges (as `epsilon -> 0+`) to
  `-(2 pi i * (k/12 - ord_cusp))`. -/
  h_mod : Tendsto F_eps (𝓝[>] 0)
    (𝓝 (-(2 * ↑Real.pi * I *
      ((k : ℂ) / 12 - (orderAtCusp' f : ℂ)))))

/-- Extracts the PV chain identity from the two limits bundled in `PVChainData`. -/
theorem pvChainIdentity (S : Finset UpperHalfPlane) {H : ℝ} (data : PVChainData f S H) :
    ∑ s ∈ S,
      generalizedWindingNumber data.D.boundary (↑s : ℂ) *
        (orderOfVanishingAt' (⇑f) s : ℂ) =
    -((k : ℂ) / 12 - (orderAtCusp' f : ℂ)) := by
  refine mul_left_cancel₀ pvChain_two_pi_I_ne_zero ?_
  linear_combination tendsto_nhds_unique data.h_res data.h_mod

/-- Variant of `valence_formula_of_two_sides` whose boundary data is available
over heights satisfying `H > 1`. -/
theorem valence_formula_of_two_sides_Hgt1
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (mkD : ∀ H : ℝ, 1 < H → FDWindingDataFull H)
    (H_S : ℝ) (hH_S : ∀ s ∈ S, (s : ℂ).im < H_S)
    (F : ℝ → ℝ → ℂ)
    (H_res : ℝ) (hH_res_gt : 1 < H_res)
    (h_res : ∀ (H : ℝ), H_res ≤ H → (hH : 1 < H) →
      Tendsto (F H) (𝓝[>] 0)
        (𝓝 (2 * ↑Real.pi * I *
          ∑ s ∈ S,
            generalizedWindingNumber (mkD H hH).boundary (↑s : ℂ) *
              (orderOfVanishingAt' (⇑f) s : ℂ))))
    (H_mod : ℝ) (_hH_mod_gt : 1 < H_mod)
    (h_mod : ∀ (H : ℝ), H_mod ≤ H → (hH : 1 < H) →
      Tendsto (F H) (𝓝[>] 0)
        (𝓝 (-(2 * ↑Real.pi * I *
          ((k : ℂ) / 12 - (orderAtCusp' f : ℂ)))))) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ s ∈ S.filter (fun p ↦
        p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne' ∧
        ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2),
      ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ sLeftVertFM S, ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ S.filter (fun p ↦
        p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
      ↑(orderOfVanishingAt' (⇑f) s) =
    (k : ℂ) / 12 := by
  refine valence_formula_orbit_sum_of_pvChain f S hS hS_complete ?_
  set H := max (max H_res H_mod) H_S + 1
  have hH_ge_res : H_res ≤ H :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans (lt_add_one _).le
  have hH_ge_mod : H_mod ≤ H :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans (lt_add_one _).le
  have hH_gt_1 : 1 < H := hH_res_gt.trans_le hH_ge_res
  have hH_above : ∀ s ∈ S, (s : ℂ).im < H := fun s hs ↦
    (hH_S s hs).trans_le ((le_max_right _ _).trans (lt_add_one _).le)
  exact ⟨H, mkD H hH_gt_1, hH_above, pvChainIdentity f S
    ⟨mkD H hH_gt_1, hH_above, F H,
      h_res H hH_ge_res hH_gt_1, h_mod H hH_ge_mod hH_gt_1⟩⟩

end

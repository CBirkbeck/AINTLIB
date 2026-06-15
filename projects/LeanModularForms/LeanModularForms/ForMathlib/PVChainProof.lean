/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.CoreIdentityProof

/-!
# PV Chain Proof: Discharging h_pvChain

This file discharges the `h_pvChain` hypothesis from `CoreIdentityProof.lean`,
which bundles:
1. `FDWindingDataFull H` for some large `H`
2. Height bound: all S points below H
3. PV chain identity: `Sigma gWN(boundary, s) * ord(f,s) = -(k/12 - ord_cusp)`

## Strategy

Both sides of the PV chain identity are limits of the *same* epsilon-truncated
integral of `logDeriv(f)` around the FD boundary:

- **Residue side**: the CPV integral tends to `2 pi i * Sigma gWN * ord`,
  by the generalized residue theorem applied to `logDeriv(f)` (which has
  simple poles with residue = order of vanishing).

- **Modular side**: the same CPV integral tends to `-(2 pi i)(k/12 - ord_inf)`,
  via T-cancellation of verticals, S-arc contribution, and horizontal winding.

By `tendsto_nhds_unique` the two limits agree, and cancelling `2 pi i` gives
the PV chain identity.

## Architecture

### `PVChainData`

Bundles the two `Tendsto` hypotheses for a common integrand `F_eps` at a
given height `H`, together with the `FDWindingDataFull` at that height.

### `pvChainIdentity`

The core theorem: from `PVChainData` extract the identity
  `Sigma gWN * ord = -(k/12 - ord_cusp)`
via uniqueness of limits and algebraic manipulation.

### `discharge_pvChain`

Assembles `h_pvChain` from `PVChainData` by packaging the identity with
the height bound.

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

/-- Data for the PV chain identity at height `H`.

This bundles:
1. `FDWindingDataFull H` -- winding weights at all FD boundary points
2. A common integrand function `F_eps : R -> C` (the epsilon-truncated
   integral of `logDeriv(f)` around the FD boundary)
3. The residue-side limit: `F_eps` tends to the winding-weighted ord sum
4. The modular-side limit: `F_eps` tends to the modular-side expression
5. Height bound: all points in `S` lie below `H`

The two Tendsto hypotheses share the same integrand, so
`tendsto_nhds_unique` applies. -/
structure PVChainData
    (S : Finset UpperHalfPlane) (H : ℝ) where
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

/-- **The PV chain identity**: from `PVChainData`, extract

  `Sigma gWN(gamma, s) * ord(f, s) = -(k/12 - ord_cusp)`

by uniqueness of limits (both the residue and modular sides are limits
of the same epsilon-truncated integral) and cancellation of `2 pi i`.

This is the heart of the valence formula proof: the analytical content
is in constructing the two `Tendsto` hypotheses; the algebraic content
is this uniqueness + cancellation argument. -/
theorem pvChainIdentity
    (S : Finset UpperHalfPlane)
    {H : ℝ} (data : PVChainData f S H) :
    ∑ s ∈ S,
      generalizedWindingNumber data.D.boundary (↑s : ℂ) *
        (orderOfVanishingAt' (⇑f) s : ℂ) =
    -((k : ℂ) / 12 - (orderAtCusp' f : ℂ)) := by
  refine mul_left_cancel₀ pvChain_two_pi_I_ne_zero ?_
  linear_combination tendsto_nhds_unique data.h_res data.h_mod

/-- Variant of `valence_formula_of_two_sides` with `mkD` over `H > 1` instead
of `H > √3/2`. Useful when the `FDWindingDataFull` constructor only works
for `H > 1` (e.g. the unconditional `mkFDWindingDataFull_unconditional`). -/
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
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne' ∧
        ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2),
      ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ sLeftVertFM S, ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ S.filter (fun p =>
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
  have hH_above : ∀ s ∈ S, (s : ℂ).im < H := fun s hs =>
    (hH_S s hs).trans_le ((le_max_right _ _).trans (lt_add_one _).le)
  exact ⟨H, mkD H hH_gt_1, hH_above, pvChainIdentity f S
    ⟨mkD H hH_gt_1, hH_above, F H,
      h_res H hH_ge_res hH_gt_1, h_mod H hH_ge_mod hH_gt_1⟩⟩

end

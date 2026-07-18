/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.ArcFTCAtI
import LeanModularForms.ForMathlib.ArcGenericFTCProvider
import LeanModularForms.ForMathlib.CornerFTCAtRho
import LeanModularForms.ForMathlib.CrossingAtI
import LeanModularForms.ForMathlib.CrossingAtRho
import LeanModularForms.ForMathlib.FDWindingDataFullAssembly
import LeanModularForms.ForMathlib.InteriorContourIntegral
import LeanModularForms.ForMathlib.PVChainProof
import LeanModularForms.ForMathlib.Seg1FTCProvider
import LeanModularForms.ForMathlib.Seg4FTCProvider
import LeanModularForms.ForMathlib.WindingWeightsUnconditional

/-!
# `FDWindingDataFull` from all three FTC providers (fully unconditional)

This file plugs the now-unconditional seg1, seg4, and arc FTC providers into
`mkFDWindingDataFull_of_ftcProviders`, yielding a fully unconditional
`FDWindingDataFull` constructor from just a `FDWindingData`.

## Main results

* `mkFDWindingDataFull_unconditional` — `FDWindingDataFull` from
  `FDWindingData` alone; all three FTC providers (seg1, seg4, arc) are
  filled in from the unconditional constructors.
* `mkFDWindingDataFull_seg1seg4_unconditional` — legacy version still
  taking an arc FTC provider as hypothesis.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `√3 / 2 < H` whenever `1 < H`, used to feed the seg1/seg4 FTC providers. -/
private lemma sqrt_three_div_two_lt_of_one_lt {H : ℝ} (hH : 1 < H) : Real.sqrt 3 / 2 < H := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3:ℝ)]

/-- `FDWindingDataFull H` constructor where seg1 and seg4 FTC providers are
filled in unconditionally; only the arc FTC provider is required. -/
def mkFDWindingDataFull_seg1seg4_unconditional {H : ℝ} (hH : 1 < H)
    (D : FDWindingData H)
    (ftc_arc : ∀ θ₀ : ℝ, Real.pi / 3 < θ₀ → θ₀ < 2 * Real.pi / 3 →
      ArcFTCHyp D.boundary (exp (↑θ₀ * I)) (arcT₀ θ₀) arcsinDelta
        (arcThreshold H θ₀) (-(↑Real.pi * I))) :
    FDWindingDataFull H :=
  let hH_sqrt3 := sqrt_three_div_two_lt_of_one_lt hH
  mkFDWindingDataFull_of_ftcProviders hH D
    (fun _ hz_re hi_lo hi_hi ↦
      arcFTCHyp_seg1 hH_sqrt3 D.boundary D.boundary_eq hz_re hi_lo hi_hi)
    (fun _ hz_re hi_lo hi_hi ↦
      arcFTCHyp_seg4 hH_sqrt3 D.boundary D.boundary_eq hz_re hi_lo hi_hi)
    ftc_arc

/-- `FDWindingDataFull H` constructor from `FDWindingData H` alone.
All three FTC providers (seg1, seg4, arc) are supplied unconditionally. -/
def mkFDWindingDataFull_unconditional {H : ℝ} (hH : 1 < H) (D : FDWindingData H) :
    FDWindingDataFull H :=
  mkFDWindingDataFull_seg1seg4_unconditional hH D
    (fun _ h_lo h_hi ↦ arcFTCHyp_arc_generic hH D.boundary D.boundary_eq h_lo h_hi)

/-! ### Fully unconditional FDWindingData from the FD boundary path -/

/-- Unconditional `FDWindingData H` using the canonical `fdBoundaryPC1Path`
and the three unconditional elliptic-point FTC providers. -/
def fdWindingData_unconditional {H : ℝ} (hH : 1 < H) : FDWindingData H :=
  let hH_sqrt3 := sqrt_three_div_two_lt_of_one_lt hH
  let γ : PiecewiseC1Path (fdStart H) (fdStart H) := fdBoundaryPC1Path H hH_sqrt3
  let hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t :=
    fdBoundaryPC1Path_eq H hH_sqrt3
  { boundary := γ
    boundary_eq := hγ
    interior_winding := fun _ hz_norm hz_re hz_im_pos hz_im_lt ↦
      fdBoundary_interior_winding_complete hH_sqrt3
        ⟨hz_norm, hz_re, hz_im_pos, hz_im_lt⟩ hγ
    winding_at_i := hasWindingNumber_atI_of_scd
      (singleCrossingData_atI_of_ftcHyp hH γ hγ (arcFTCHyp_atI hH hγ)) rfl
    winding_at_rho := hasWindingNumber_atRho_of_cornerFtcHyp hH γ hγ
      (cornerFTCHyp_atRho hH hγ)
    winding_at_rho_plus_one := hasWindingNumber_atRhoPlusOne_of_cornerFtcHyp hH γ hγ
      (cornerFTCHyp_atRhoPlusOne_unconditional hH hγ) }

/-- Fully unconditional `FDWindingDataFull H` — no hypotheses beyond `1 < H`. -/
def fdWindingDataFull_unconditional {H : ℝ} (hH : 1 < H) : FDWindingDataFull H :=
  mkFDWindingDataFull_unconditional hH (fdWindingData_unconditional hH)

/-! ### Top-level unconditional valence formula -/

/-- **The valence formula, fully unconditional in `mkD`**.

This is `valence_formula_of_two_sides_Hgt1` with the `mkD` parameter
supplied unconditionally via `fdWindingDataFull_unconditional`. The
only remaining hypotheses are the residue-side and modular-side
Tendsto results. -/
theorem valence_formula_unconditional_mkD {k : ℤ} (f : ModularForm (Gamma 1) k)
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (H_S : ℝ) (hH_S : ∀ s ∈ S, (s : ℂ).im < H_S) (F : ℝ → ℝ → ℂ)
    (H_res : ℝ) (hH_res_gt : 1 < H_res)
    (h_res : ∀ (H : ℝ), H_res ≤ H → (hH : 1 < H) →
      Tendsto (F H) (𝓝[>] 0)
        (𝓝 (2 * ↑Real.pi * I *
          ∑ s ∈ S,
            generalizedWindingNumber
              (fdWindingDataFull_unconditional hH).boundary (↑s : ℂ) *
              (orderOfVanishingAt' (⇑f) s : ℂ))))
    (H_mod : ℝ) (hH_mod_gt : 1 < H_mod)
    (h_mod : ∀ (H : ℝ), H_mod ≤ H → (_hH : 1 < H) →
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
    (k : ℂ) / 12 :=
  valence_formula_of_two_sides_Hgt1 f S hS hS_complete
    (fun _ ↦ fdWindingDataFull_unconditional)
    H_S hH_S F H_res hH_res_gt h_res H_mod hH_mod_gt h_mod

end

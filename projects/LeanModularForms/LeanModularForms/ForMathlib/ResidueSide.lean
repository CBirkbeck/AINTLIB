/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.ValenceFormula.PVChain.Assembly
import LeanModularForms.ForMathlib.ValenceFormula.PVChain.Assembly.ResidueSide

/-!
# Residue Side of the Valence Formula

This file provides the "residue side" of the valence formula: applying the
generalized residue theorem to `logDeriv(f)` along the FD boundary.

## Architecture

The full proof proceeds in three steps:

### Step 1: Residue side (CPV → winding-weighted ord sum)

The CPV integral of `logDeriv(f)` around the FD boundary at height `H` converges
(as the exclusion radius `ε → 0⁺`) to `2πi · Σ gWN(γ, s) · ord(f, s)`, where:
- `gWN(γ, s)` is the generalized winding number of the boundary around `s`
- `ord(f, s)` is the order of vanishing of `f` at `s`

This uses:
- `logDeriv(f)` has simple poles with residue = order (`LogDerivModularForm`)
- The generalized residue theorem for simple poles (`GeneralizedResidueTheorem`)

### Step 2: Modular side (CPV → modular transformation)

The same CPV integral is computed using modular invariance:
- T-cancellation of vertical integrals
- S-arc contribution = `-(2πi)(k/12)`
- Horizontal contribution = `2πi · ord_∞(f)`

### Step 3: Equate by uniqueness of limits

Both sides compute limits of the same quantity, so by uniqueness of limits
in a Hausdorff space and cancellation of `2πi`:

  `Σ gWN · ord = -(k/12 - ord_∞)`

## Main results

* `cpv_residue_side_forMathlib` — CPV integral tends to `2πi · Σ gWN · ord`
* `cpv_modular_side_forMathlib` — CPV integral tends to `-(2πi)(k/12 - ord_∞)`

## References

* Diamond–Shurman, *A First Course in Modular Forms*, Theorem 3.1.1
* Hungerbühler–Wasem, *A generalized residue theorem*, arXiv:1808.00997v2
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

include hf in
/-- **Residue side**: the ε-truncated integral of `logDeriv(f)` around the FD
boundary at height `H` converges to `2πi · Σ gWN(γ, s) · ord(f, s)`.

For `H ≥ H₀` (where `H₀` depends on the zeros of `f` in `𝒟`), the limit
exists and equals the winding-number-weighted sum of orders.

This delegates to `cpv_residue_side_tendsto` from
`ValenceFormula.PVChain.Assembly.ResidueSide`, which constructs the
holomorphic remainder via the generalized residue theorem, proves the CPV
exists at each singular point, and shows the integrand eventually agrees
with the restriction to on-curve singularities. -/
theorem cpv_residue_side_forMathlib (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧ ∀ {H : ℝ}, H₀ ≤ H →
      Tendsto (fun ε => ∫ t in (0:ℝ)..5,
          pvIntegrand f (fdBoundary_H H) (sArcOfS S ∪ sVertOfS S) ε t)
        (𝓝[>] 0)
        (𝓝 (2 * ↑Real.pi * I * ∑ s ∈ S, generalizedWindingNumber'
          (fdBoundary_H H) 0 5 (↑s : ℂ) * (orderOfVanishingAt' (⇑f) s : ℂ))) :=
  cpv_residue_side_tendsto f hf S hS hS_complete

include hf in
/-- **Modular side**: the ε-truncated integral of `logDeriv(f)` around the FD
boundary at height `H` converges to `-(2πi)(k/12 - ord_∞)`.

This combines:
1. T-cancellation of vertical segments (periodicity of `logDeriv f`)
2. S-arc contribution `-(2πi)(k/12)` (modular identity `f(Sz) = z^k f(z)`)
3. Horizontal contribution `2πi · ord_∞` (q-expansion winding number) -/
theorem cpv_modular_side_forMathlib (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧ ∀ {H : ℝ}, H₀ ≤ H →
      Tendsto (fun ε => ∫ t in (0:ℝ)..5,
          pvIntegrand f (fdBoundary_H H) (sArcOfS S ∪ sVertOfS S) ε t)
        (𝓝[>] 0)
        (𝓝 (-(2 * ↑Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))))) :=
  cpv_modular_side_tendsto f hf S hS hS_complete

end

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.TorsionGeometric
import HasseWeil.WeilPairing.TorsionKernelRational

/-!
# `#E[ℓ] = ℓ²` — assembly of the separable-kernel torsor at `φ = [ℓ]`

This file assembles `#E[ℓ] = ℓ²` from the capstone
`HasseWeil.card_kernel_eq_degree_of_separable_concrete` (`SeparableKernelTorsor.lean`)
instantiated at `φ = mulByInt W.toAffine ℓ`, together with the `[ℓ]`-specific reducers
in `TorsionGeometric.lean`.

`card_torsion_ell_of_discharges` is the wiring **parametric** on the three geometric
discharges for `[ℓ]`:
* `hxy` — the addition-formula coordinate translation-invariance (R1), fed through
  `hcov_mulByInt_of_xy` to produce the capstone's `hcov`;
* `h_normal` — normality of `KE / [ℓ]*KE` (R2);
* `hdesc` — the generic-point descent torsor (R3);

with `hsep` discharged unconditionally by `mulByInt_isSeparable`. Once the three are
discharged (over `K̄`), `card_torsion_ell` is immediate.

Reference: Silverman III.4.10c (the torsor), III.6.4(a) (`#E[m] = m²`).
-/

open WeierstrassCurve

namespace HasseWeil.WeilPairing.TorsionGeometric

open HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
  (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-- **`#E[ℓ] = ℓ²`, parametric on the three `[ℓ]` geometric discharges.** Given the
addition-formula translation-invariance `hxy` (R1), normality `h_normal` (R2), and the
descent torsor `hdesc` (R3) for `[ℓ]`, the capstone gives `#ker[ℓ] = deg[ℓ] = ℓ²`, hence
`#E[ℓ] = ℓ²`. Separability is supplied unconditionally by `mulByInt_isSeparable`. -/
theorem card_torsion_ell_of_discharges (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (hxy : ∀ k : (mulByInt W.toAffine ℓ).kernel,
      translateAlgEquivOfPoint W k.val (mulByInt_x W ℓ) = mulByInt_x W ℓ ∧
      translateAlgEquivOfPoint W k.val (mulByInt_y W ℓ) = mulByInt_y W ℓ)
    (h_normal : letI := (mulByInt W.toAffine ℓ).toAlgebra
      Normal W.toAffine.FunctionField W.toAffine.FunctionField)
    (hdesc : ∀ σ : (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ _
        (mulByInt W.toAffine ℓ).toAlgebra (mulByInt W.toAffine ℓ).toAlgebra),
      ∃ k : W.toAffine.Point, k ∈ (mulByInt W.toAffine ℓ).kernel ∧
        liftPointToKE W k =
          genericPointAct W (mulByInt W.toAffine ℓ) σ - genericPoint W) :
    (Nat.card W.toAffine[ℓ] : ℤ) = ℓ ^ 2 := by
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at hℓ
  have h_ker_deg :
      Nat.card (mulByInt W.toAffine ℓ).kernel = (mulByInt W.toAffine ℓ).degree :=
    card_kernel_eq_degree_of_separable_concrete W (mulByInt W.toAffine ℓ)
      (mulByInt_isSeparable W ℓ hℓ)
      (hcov_mulByInt_of_xy W ℓ hℓ0 hxy)
      h_normal hdesc
  exact card_torsion_ell_of_ker_deg W ℓ hℓ0 h_ker_deg

/-- **`#E[ℓ] = ℓ²` over an algebraically closed field `F`** (Silverman III.6.4(a)), for `ℓ ≠ 0`
in `F` (`ℓ ≠ p`). The three `[ℓ]` geometric discharges over `K̄` are supplied by:
* `hxy_mulByInt` (R1, addition-formula translation-invariance ⟹ `hcov`);
* `h_normal_mulByInt` (R2, normality of `K(E)/[ℓ]*K(E)`, Silverman III.4.10c);
* `hdesc_mulByInt` (R3, the generic-point descent torsor via kernel-rationality).
Assembled through `card_torsion_ell_of_discharges`. -/
theorem card_torsion_ell [IsAlgClosed F] (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) :
    (Nat.card W.toAffine[ℓ] : ℤ) = ℓ ^ 2 := by
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at hℓ
  exact card_torsion_ell_of_discharges W ℓ hℓ
    (hxy_mulByInt W ℓ hℓ0)
    (h_normal_mulByInt W ℓ hℓ0)
    (hdesc_mulByInt W ℓ hℓ0)

end HasseWeil.WeilPairing.TorsionGeometric

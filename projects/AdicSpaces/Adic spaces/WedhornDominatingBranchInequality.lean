/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornDominatingUnitInequality

/-!
# Wedhorn dominating-unit branch candidate inequality

Branch-level pointwise candidate inequality for the Wedhorn 8.34(ii)
σ-clearing argument. Composes the pointwise primitives from
`WedhornDominatingUnitInequality.lean` (commit `e2f688f`) into the
shape directly consumed by the membership-side
`v.vle f C.base.s` verification at a single Spa-point `v`.

## What this file provides

* `vle_C_base_s_of_dominating_branch_at` — point-level branch candidate
  inequality: from σ-domination `v.vle (σ : A) τ`, an algebraic equality
  `f = (σ : A) * a` for the candidate, and a branch-residual inequality
  `v.vle (τ * a) C_base_s` already established under the τ-branch,
  derive `v.vle f C_base_s`. Direct σ-replacement.

* `vle_C_base_s_of_dominating_branch_with_t_pow_at` — the explicit
  Wedhorn-shape `f := (σ : A) * t * D_s ^ N` variant: takes the
  per-branch chain `v.vle (τ * t * D_s ^ N) C_base_s` and produces
  `v.vle f C_base_s`.

* `vle_cancel_unit_left` — left-cancellation by a unit `σ : Aˣ` on the
  `vle`-relation: `v.vle ((σ : A) * a) b → v.vle a (((σ⁻¹ : Aˣ) : A) * b)`.
  Algebraic-side primitive for the SUBSET-direction transfer; useful
  when a candidate equality is reduced to extract the non-σ factor.

* `vle_cancel_unit_left_iff` — iff form of `vle_cancel_unit_left`.

## Subset-direction status (the multi-`T_D` residual)

The full subset-side σ-clearing
`R(insert f C.base.T, C.base.s) ⊆ R(D.T, D.s)` requires per-`w` case
analysis on which `τ ∈ T_test` wins σ-domination at `w`, plus the
specific Cor 7.32 σ-power-decay structure that makes
`w(σ) * w(D.s) ^ N ≤ w(C.base.s)` simultaneously bound `w(t') ≤ w(D.s)`
for every `t' ∈ D.T`. That step is genuinely beyond simple
σ-replacement: the key residual statement is documented at the bottom
of this file as `subset_inequality_target`.

## Notes

* No root import; leaf-level.
* No final-acyclicity hypotheses, no Lane B / Cor 8.32 / Jacobson / T001
  / faithful-flatness content.
* Does not edit `WedhornLocalizationLiftContinuity.lean`,
  `WedhornValuationLocalizationLift.lean`,
  `WedhornC1StrongSupplierCore.lean`,
  `WedhornStandardCoverRefinement.lean`, or any in-flight file.
* Imports only `«Adic spaces».WedhornDominatingUnitInequality` plus its
  transitive closure (`ValuationSpectrum`).
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-- **Branch candidate inequality** (point-level Wedhorn 8.34(ii) Step 3).

From σ-domination `v.vle (σ : A) τ` and a branch-residual inequality
`v.vle (τ * a) C_base_s`, plus the algebraic equality `f = (σ : A) * a`
for the candidate, derive `v.vle f C_base_s`. Direct application of
`vle_replace_dominating_at`. -/
theorem vle_C_base_s_of_dominating_branch_at
    (v : Spv A) {σ : Aˣ} {τ a C_base_s f : A}
    (hf : f = (σ : A) * a)
    (hστ : v.vle (σ : A) τ)
    (h_branch_chain : v.vle (τ * a) C_base_s) :
    v.vle f C_base_s :=
  hf ▸ vle_replace_dominating_at v hστ h_branch_chain

/-- **Wedhorn-shape branch candidate inequality**. Specialisation of
`vle_C_base_s_of_dominating_branch_at` to the explicit candidate shape
`f := (σ : A) * t * D_s ^ N` appearing in Wedhorn 8.34(ii). The
branch-residual inequality `v.vle (τ * t * D_s ^ N) C_base_s` is the
input the user supplies for the τ-branch, derived from `v ∈ R(D.T, D.s)`
and the Cor 7.32 σ-power decay choice for `N`. -/
theorem vle_C_base_s_of_dominating_branch_with_t_pow_at
    (v : Spv A) {σ : Aˣ} {τ t D_s C_base_s f : A} (N : ℕ)
    (hf : f = (σ : A) * t * D_s ^ N)
    (hστ : v.vle (σ : A) τ)
    (h_branch_chain : v.vle (τ * t * D_s ^ N) C_base_s) :
    v.vle f C_base_s := by
  rw [hf, mul_assoc]
  apply vle_replace_dominating_at v hστ
  rwa [← mul_assoc]

/-- **Left-cancellation of a unit on `vle`**. From
`v.vle ((σ : A) * a) b`, deduce `v.vle a (((σ⁻¹ : Aˣ) : A) * b)`.
Multiplies both sides by `σ⁻¹` on the left and uses the unit-inverse
identity. -/
theorem vle_cancel_unit_left
    (v : Spv A) {σ : Aˣ} {a b : A}
    (h : v.vle ((σ : A) * a) b) :
    v.vle a (((σ⁻¹ : Aˣ) : A) * b) := by
  letI : ValuativeRel A := v.toValuativeRel
  have hmul := ValuativeRel.mul_vle_mul_right h ((σ⁻¹ : Aˣ) : A)
  rwa [← mul_assoc, Units.inv_mul, one_mul] at hmul

/-- **Iff form of unit left-cancellation**: a `vle`-relation involving a
unit factor on the left can be cancelled in either direction. -/
theorem vle_cancel_unit_left_iff
    (v : Spv A) (σ : Aˣ) (a b : A) :
    v.vle ((σ : A) * a) b ↔ v.vle a (((σ⁻¹ : Aˣ) : A) * b) := by
  letI : ValuativeRel A := v.toValuativeRel
  refine ⟨vle_cancel_unit_left v, fun h => ?_⟩
  have hmul := ValuativeRel.mul_vle_mul_right h ((σ : A))
  rwa [← mul_assoc, Units.mul_inv, one_mul] at hmul

/-! ### Subset-direction residual (recorded for the next ticket)

The subset-side σ-clearing `R(insert f C.base.T, C.base.s) ⊆ R(D.T, D.s)`
requires the following multi-`T_D` theorem, which is **NOT** discharged
by this file:

```
theorem subset_inequality_target
    {A : Type*} [CommRing A] (P : PairOfDefinition A)
    (σ : Aˣ) (D_s C_base_s : A) (T_D : Finset A) (N : ℕ)
    (f : A) (hf : f = (σ : A) * (T_D.prod id) * D_s ^ N)
    (hσ_dom : ∀ w ∈ Spa A A⁺, ∃ τ ∈ insert D_s T_D,
      w.vle (σ : A) τ ∧ ¬ w.vle τ (σ : A))
    {w : Spv A} (hw_spa : w ∈ Spa A A⁺)
    (hw_f_C_base_s : w.vle f C_base_s) :
    (∀ t' ∈ T_D, w.vle t' D_s) ∧ ¬ w.vle D_s 0
```

The genuinely new content beyond this file's primitives is the per-`w`
case analysis on which `τ ∈ insert D_s T_D` wins σ-domination at `w`
(branch case-split), plus exploitation of Cor 7.32's strict σ-power
decay structure to compare `w(σ)`-bounds against `w(D_s)^N`-bounds.

Both sub-steps are documented as next-ticket targets in
`WedhornStandardCoverRefinement.lean:301`. -/

end ValuationSpectrum

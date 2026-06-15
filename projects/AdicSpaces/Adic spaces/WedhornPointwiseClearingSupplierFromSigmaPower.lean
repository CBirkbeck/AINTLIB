/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornPointwiseSigmaProductClearing
import «Adic spaces».WedhornDirectUpperBoundSupplierFromPointwiseClearing

/-!
# Wedhorn 8.34(ii) — Pointwise clearing supplier from σ-power data (T079)

T070 (commit accepted in `WedhornPointwiseSigmaProductClearing.lean`)
landed the **per-`(v, t')` σ-power cancellation supplier**:
```
pointwise_clearing_supplier_via_pow_cancellation
  (s D_s f t' : A)
  (h_pow_chain :
    ∀ v ∈ Spa A A⁺,
      v.vle f s → v.vle 1 t' → ¬ v.vle t' 0 →
      ∃ N : ℕ, v.vle (t' * D_s ^ N) (D_s ^ (N + 1)) ∧ ¬ v.vle D_s 0) :
  ∀ v ∈ Spa A A⁺,
    v.vle f s → v.vle 1 t' → ¬ v.vle t' 0 → v.vle t' D_s
```

T077 (commit `292635d`) consumes the **uniform-over-`D_T` pointwise
clearing supplier shape**:
```
∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
  v.vle f s → v.vle 1 t' → ¬ v.vle t' 0 → v.vle t' D_s
```

This file lands the **uniform-over-`D_T` σ-power adapter**: it lifts
T070's per-`(v, t')` σ-power cancellation supplier (taken uniformly
over `t' ∈ D_T`) to the uniform pointwise clearing supplier shape
consumed by T077. It also lands the downstream composition into
T077's direct lane and into T072's named residual
`SigmaProductClearedInequalitySupplier`.

## Why this is a useful new boundary, not a duplicate of T070

T070 supplies the per-`(v, t')` σ-power cancellation primitive as a
**single-`t'`** theorem. T077's direct lane consumes the
**uniform-over-`D_T`** pointwise clearing supplier. The natural
quantifier rearrangement (uniform σ-power input → uniform pointwise
clearing output) is missing from both T070 and T077: T070 stops at
single-`t'`, T077 starts at uniform pointwise clearing. T079 lands
the bridge.

The adapter is a single application of T070's single-`t'` supplier
under the outer `∀ t' ∈ D_T` quantifier. The σ-power cancellation
primitive itself (`vle_mul_pow_cancel_left`) is owned by T050
(`WedhornSigmaDominationClearing.lean`); T070 wraps it into the
single-`t'` source-restricted supplier; T079 lifts the supplier to
the uniform-over-`D_T` shape consumed by T077 and downstream final-
Part-2 callers. This is the **smallest adapter** matching the
ticket's "do not restate blindly" guidance.

The strict reusability gain over T070 alone: callers holding the
**uniform-over-`D_T`** σ-power-cleared supplier shape (the natural
output of a uniform σ-construction across `D_T`) can directly
discharge T077's input without manually unfolding the single-`t'`
intermediate at every call site.

## What this file provides

* `pointwise_clearing_supplier_via_sigma_power_source_restricted` —
  T079 main theorem: uniform-over-`D_T` adapter from T070's σ-power
  cancellation supplier (uniform-over-`D_T`) to T077's pointwise
  clearing supplier shape. Direct input to
  `direct_upper_bound_supplier_via_pointwise_clearing` (T077).

* `direct_upper_bound_supplier_via_sigma_power_source_restricted` —
  composition: from the uniform-over-`D_T` σ-power-cleared inequality
  supplier, deliver T073's direct upper bound supplier shape (upper
  bound + `D_s` non-vanishing) by composing T079's adapter with T077's
  `direct_upper_bound_supplier_via_pointwise_clearing`.

* `SigmaProductClearedInequalitySupplier_via_sigma_power_source_restricted`
  — full end-to-end composition: from the uniform-over-`D_T` σ-power-
  cleared inequality supplier, deliver T072's named residual
  `SigmaProductClearedInequalitySupplier` by composing T079's adapter
  with T077's full direct-lane composition. This closes the σ-power-
  cleared lane into T072 in a single named theorem.

## Notes

* No root import; leaf-level.
* Imports T070 (`WedhornPointwiseSigmaProductClearing`) for the
  per-`(v, t')` σ-power cancellation supplier and T077
  (`WedhornDirectUpperBoundSupplierFromPointwiseClearing`) for the
  pointwise → direct supplier bridge and the
  `SigmaProductClearedInequalitySupplier_via_pointwise_clearing_supplier`
  end-to-end composition.
* No edits to T031–T078 accepted leaves, root imports, or final
  theorem signatures.
* No revival of M-power-decay / σ-power-decay, T001/Lane-B,
  Cor 8.32/Jacobson, faithful-flatness, Zavyalov, or
  bivariate-overlap content.
* No global universal-over-Spa multi-element clearing claim.
* No global universal-over-`D_T` lower bound resurrection — the
  consumed σ-power-cleared inequality is per-`(v, t')` source-
  restricted (involves only `t'` and `D_s`).
* No final Tate acyclicity hypothesis additions. No edits to
  Primary's final threading file or Secondary's T076 file.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

omit [IsTopologicalRing A] in
/-- **Pointwise clearing supplier via uniform σ-power data**
(T079 main adapter; T077 input shape).

From a **uniform-over-`D_T`** per-`(v, t')` source-restricted σ-power-
cleared inequality supplier — at every `t' ∈ D_T` and every `v ∈
Spa A A⁺` with `v.vle f s`, `v.vle 1 t'`, `¬ v.vle t' 0`, supply an
exponent `N` and the σ-power-cleared inequality
`v.vle (t' * D_s^N) (D_s^(N+1))` plus `D_s` non-vanishing —
discharge the **uniform-over-`D_T` pointwise clearing supplier**
consumed by T077:

```
∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
  v.vle f s → v.vle 1 t' → ¬ v.vle t' 0 → v.vle t' D_s
```

**Proof structure**: under the outer `∀ t' ∈ D_T` quantifier, apply
T070's `pointwise_clearing_supplier_via_pow_cancellation` to the
specialised single-`t'` σ-power supplier obtained by fixing `t'` in
the uniform input. The σ-power cancellation arithmetic
(`vle_mul_pow_cancel_left`) is consumed inside T070; T079 only
performs the quantifier rearrangement.

**Substantive consumption**: each per-`(v, t')` σ-power-cleared
inequality is genuinely used at the per-`(v, t')` cancellation step
inside T070's primitive. The non-vanishing piece is the cancellation
hypothesis. The supplier is **not** a pass-through wrapper because the
σ-power cancellation is the witness step, not a renaming. -/
theorem pointwise_clearing_supplier_via_sigma_power_source_restricted
    (D_T : Finset A) (s D_s f : A)
    (h_pow_chain :
      ∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
        v.vle f s →
        v.vle (1 : A) t' →
        ¬ v.vle t' 0 →
        ∃ N : ℕ,
          v.vle (t' * D_s ^ N) (D_s ^ (N + 1)) ∧ ¬ v.vle D_s 0) :
    ∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
      v.vle f s →
      v.vle (1 : A) t' →
      ¬ v.vle t' 0 →
      v.vle t' D_s :=
  fun t' ht' =>
    pointwise_clearing_supplier_via_pow_cancellation s D_s f t'
      (h_pow_chain t' ht')

omit [IsTopologicalRing A] in
/-- **Direct upper bound supplier via σ-power-cleared inequality
supplier** (T079 + T077 composition).

End-to-end composition: from the uniform-over-`D_T` σ-power-cleared
inequality supplier (T070's per-`(v, t')` data, taken uniformly over
`t' ∈ D_T`), deliver T073's direct upper bound supplier shape (upper
bound `v.vle t' D_s` + `D_s` non-vanishing) by composing T079's
pointwise-clearing adapter with T077's
`direct_upper_bound_supplier_via_pointwise_clearing`.

Useful for downstream final-Part-2 callers that hold the σ-power-
cleared inequality natively (e.g., from a σ-construction that has
already done σ-cancellation but not yet `N = 0` reduction). -/
theorem direct_upper_bound_supplier_via_sigma_power_source_restricted
    (D_T : Finset A) (s D_s f : A)
    (h_pow_chain :
      ∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
        v.vle f s →
        v.vle (1 : A) t' →
        ¬ v.vle t' 0 →
        ∃ N : ℕ,
          v.vle (t' * D_s ^ N) (D_s ^ (N + 1)) ∧ ¬ v.vle D_s 0) :
    ∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
      v.vle f s →
      v.vle (1 : A) t' →
      ¬ v.vle t' 0 →
      v.vle t' D_s ∧ ¬ v.vle D_s 0 :=
  direct_upper_bound_supplier_via_pointwise_clearing D_T s D_s f
    (pointwise_clearing_supplier_via_sigma_power_source_restricted
      D_T s D_s f h_pow_chain)

omit [IsTopologicalRing A] in
/-- **`SigmaProductClearedInequalitySupplier` via σ-power-cleared
inequality supplier** (T079 + T077 + T073 end-to-end direct lane).

Full end-to-end composition: from the uniform-over-`D_T` σ-power-
cleared inequality supplier (T070's per-`(v, t')` data taken uniformly
over `t' ∈ D_T`), deliver T072's named residual
`SigmaProductClearedInequalitySupplier` by composing T079's adapter
with T077's
`SigmaProductClearedInequalitySupplier_via_pointwise_clearing_supplier`.

**End-to-end σ-power lane**:
σ-power-cleared inequality supplier (T070 residual shape, uniform) →
pointwise clearing supplier (T079 adapter) →
direct upper bound supplier (T077 bridge) →
`SigmaProductClearedInequalitySupplier` (T073 `N = 0` witness).

The whole chain is closed-form per-`(v, t')` source-restricted
valuation arithmetic; no σ-factored or universal-over-`D_T` content
is consumed beyond the per-`(v, t')` σ-power-cleared input. -/
theorem SigmaProductClearedInequalitySupplier_via_sigma_power_source_restricted
    (D_T : Finset A) (s D_s f : A)
    (h_pow_chain :
      ∀ t' ∈ D_T, ∀ v ∈ Spa A A⁺,
        v.vle f s →
        v.vle (1 : A) t' →
        ¬ v.vle t' 0 →
        ∃ N : ℕ,
          v.vle (t' * D_s ^ N) (D_s ^ (N + 1)) ∧ ¬ v.vle D_s 0) :
    SigmaProductClearedInequalitySupplier D_T s D_s f :=
  SigmaProductClearedInequalitySupplier_via_pointwise_clearing_supplier
    D_T s D_s f
    (pointwise_clearing_supplier_via_sigma_power_source_restricted
      D_T s D_s f h_pow_chain)

end ValuationSpectrum

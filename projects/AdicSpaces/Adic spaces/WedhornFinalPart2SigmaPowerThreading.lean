/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornFinalPart2NoExtraHypThreading
import «Adic spaces».WedhornPointwiseClearingSupplierFromSigmaPower

/-!
# Wedhorn 8.34(ii) — Final Part-2 boundary threading T079 σ-power lane (T080)

T074 (`WedhornFinalPart2NoExtraHypThreading`) lands the **final Part-2
boundary** consuming `SigmaProductClearedInequalitySupplier` per-call
inside an outer per-call σ-construction supply
(`tateAcyclicity_Part2_via_sigma_C1_and_integrated_laneB` and its
`_allow_empty` variant). T079
(`WedhornPointwiseClearingSupplierFromSigmaPower`) lands
`SigmaProductClearedInequalitySupplier_via_sigma_power_source_restricted`,
delivering `SigmaProductClearedInequalitySupplier` from the **per-`(w, t')`
source-restricted σ-power-cleared inequality supplier**:
```
∀ t' ∈ D_T, ∀ w ∈ Spa A A⁺,
  w.vle f s → w.vle 1 t' → ¬ w.vle t' 0 →
  ∃ N : ℕ, w.vle (t' * D_s ^ N) (D_s ^ (N + 1)) ∧ ¬ w.vle D_s 0
```

This file lands the **final Part-2 σ-power threading boundary**: a
leaf-level theorem-level wrapper composing T079's converter with
T074's integrated consumer so the per-call consumer-facing residual is
the source-restricted σ-power-cleared inequality supplier directly,
**not** `SigmaProductClearedInequalitySupplier`, and **not** any
universal-over-`D_T` or universal-Spa lower-bound form.

## Why threading T079 here and not just citing T074

T074's per-call hypothesis carries the named Prop residual
`SigmaProductClearedInequalitySupplier D.T C.base.s D.s f`. Callers
holding the **σ-power-cleared inequality supplier** shape natively
(e.g., from a σ-construction that has already done σ-cancellation but
not yet packaged the `N = 0` witness into the named residual) need
T079's adapter to discharge T074's input. T080 inserts that adapter
inside the per-call delivery without touching T074 or T079, exposing a
final Part-2 boundary whose **single consumer-facing residual** is the
per-`(w, t')` σ-power-cleared inequality supplier — the natural output
of a σ-construction's algebraic identity at each Laurent piece, prior
to `N = 0` packaging.

This is **consumer-threading only**: no new arithmetic, no new
intermediate residuals. T079's converter is consumed mechanically;
T074's consumer is consumed mechanically.

## What this file provides

* `tateAcyclicity_Part2_via_sigma_power_and_integrated_laneB` — main
  wrapper. Inputs: T074's standard inputs, with the per-call
  σ-construction supply replacing `SigmaProductClearedInequalitySupplier`
  by the **per-`(w, t')` source-restricted σ-power-cleared inequality
  supplier**. Output: Part 2 of `tateAcyclicity` (Wedhorn 8.28(b)).

* `tateAcyclicity_Part2_via_sigma_power_and_integrated_laneB_allow_empty`
  — empty-piece-tolerant variant matching T074's `_allow_empty`
  consumer shape.

## Composition pipeline

```
σ-power-cleared inequality supplier per-call             [T079 source]
  + base-side rationalOpen membership / non-degeneracy /
    σ-rescaled Laurent cover hypotheses
   ↓ (SigmaProductClearedInequalitySupplier_via_sigma_power_source_restricted, T079)
SigmaProductClearedInequalitySupplier per-call           [T072 residual / T074 input]
   ↓ (tateAcyclicity_Part2_via_sigma_C1_and_integrated_laneB, T074)
Part 2 of tateAcyclicity (Wedhorn 8.28(b))
```

Both T074 and T079 are consumed mechanically. No new σ-construction
algebra is performed at this layer. No edits to T074 or T079.

## No-extra-hypothesis firewall

The deliverable explicitly does **NOT** add any hypothesis to the
final `ValuationSpectrum.tateAcyclicity` theorem. All inputs are
documented intermediate supplier-boundary inputs of the consumer
wrappers in this file, **not** changes to the root theorem
signature. The σ-construction's algebraic content is now captured by
the **per-`(w, t')` source-restricted σ-power-cleared inequality
supplier** (T079 source shape), the strictly-weaker upstream form of
T072's `SigmaProductClearedInequalitySupplier`.

## Notes

* No root import; leaf-level.
* Imports T074 (`WedhornFinalPart2NoExtraHypThreading`) and T079
  (`WedhornPointwiseClearingSupplierFromSigmaPower`).
* No edits to T031–T079 accepted leaves, root imports, or final
  theorem signatures.
* No revival of T001 / Jacobson / bivariate-overlap / Zavyalov /
  global universal-Spa-bound / σ-power-decay / M-power-decay routes;
  only mechanical composition of two accepted bridges.
* No global universal-over-`D_T` or universal-over-Spa lower bound
  resurrection — the σ-power-cleared inequality supplier is per-`(w, t')`
  source-restricted (involves only `t'` and `D.s`).
* No edits to Primary's T078 pointwise-clearing final threading file
  or Secondary's T076 localized σ-factored file.
* The deliverable matches T080's acceptance: a theorem-level wrapper
  composes T079 with T074 without adding hypotheses to the final
  `ValuationSpectrum.tateAcyclicity` signature.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsHuberRing A] [HasLocLiftPowerBounded A] [DecidableEq A]

/-- **Final Part-2 wrapper threading T079 σ-power lane through T074
integrated consumer** (T080 main deliverable).

Composes T079's
`SigmaProductClearedInequalitySupplier_via_sigma_power_source_restricted`
with T074's
`tateAcyclicity_Part2_via_sigma_C1_and_integrated_laneB` to produce
Part 2 of Wedhorn Theorem 8.28(b) tate acyclicity directly from a
per-call σ-construction supply where the σ-product algebraic content
is delivered as the **per-`(w, t')` source-restricted σ-power-cleared
inequality supplier**:
```
∀ t' ∈ D.T, ∀ w ∈ Spa A A⁺,
  w.vle f C.base.s → w.vle 1 t' → ¬ w.vle t' 0 →
  ∃ N : ℕ, w.vle (t' * D.s ^ N) (D.s ^ (N + 1)) ∧ ¬ w.vle D.s 0
```

**The single source-restricted σ-construction algebraic residual at
the consumer boundary is now the σ-power-cleared inequality
supplier**, strictly upstream of T072's
`SigmaProductClearedInequalitySupplier`. All other inputs are
already-named intermediate supplier-boundary residuals or routine
σ-construction outputs of T074.

**Output:** the gluing existential `∃ x : presheafValue C.base,
∀ E ∈ C.covers, restrictionMap C.base E _ x = fC E` from compatible
cover-level sections — exactly Part 2 of `tateAcyclicity` (Wedhorn
8.28(b)).

**No-extra-hypothesis firewall.** The hypotheses of this wrapper are
intermediate supplier-boundary inputs of the consumer; they are
**NOT** changes to the final `ValuationSpectrum.tateAcyclicity`
theorem signature. The root theorem retains its existing form. -/
theorem tateAcyclicity_Part2_via_sigma_power_and_integrated_laneB
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCovering A) (hne : C.covers.Nonempty)
    [IsNoetherianRing C.base.P.A₀]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    (h_per_call_sigma_power :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
      ∃ (_ : Aˣ) (f : A),
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
        ¬ v.vle f 0 ∧
        (∀ t' ∈ D.T, ∀ w ∈ Spa A A⁺,
          w.vle f C.base.s →
          w.vle (1 : A) t' →
          ¬ w.vle t' 0 →
          ∃ N : ℕ,
            w.vle (t' * D.s ^ N) (D.s ^ (N + 1)) ∧ ¬ w.vle D.s 0) ∧
        (∀ w ∈ rationalOpen (insert f C.base.T) C.base.s,
          ∃ t' ∈ D.T,
            w ∈ rationalOpen ({(1 : A)} : Finset A) t'))
    (f₀ : A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (separation_supplier : ∀ C' : RationalCovering A, C'.covers.Nonempty →
      ∀ a b : presheafValue C'.base,
        (∀ (D : RationalLocData A) (hD : D ∈ C'.covers),
          restrictionMap C'.base D (C'.hsubset D hD) a =
            restrictionMap C'.base D (C'.hsubset D hD) b) →
        a = b)
    (per_E_nonempty : ∀ (S' : StandardCover A)
      (hS'_per_E : refines_cover_per_E C S'.elts)
      (_hS'_contain : refines_contain C S'.elts)
      (E : { E // E ∈ C.covers }),
      (C.per_E_local_covering S'.elts f₀ E hS'_per_E).covers.Nonempty)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  tateAcyclicity_Part2_via_sigma_C1_and_integrated_laneB
    P hA₀_le hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C hne
    h_base_eq_Spa h_covers_nonempty
    (fun D hD v hv t ht hvt hvD => by
      obtain ⟨σ_choice, f, hv_base, hf_ne, h_pow_chain, h_laurent⟩ :=
        h_per_call_sigma_power D hD v hv t ht hvt hvD
      refine ⟨σ_choice, f, hv_base, hf_ne, ?_, h_laurent⟩
      exact SigmaProductClearedInequalitySupplier_via_sigma_power_source_restricted
        D.T C.base.s D.s f h_pow_chain)
    f₀ fC hC_compat separation_supplier per_E_nonempty hLaneA

/-- **Final Part-2 wrapper threading T079 σ-power lane through T074
integrated consumer**, allow-empty variant (T080 allow-empty
deliverable).

Identical caller signature to
`tateAcyclicity_Part2_via_sigma_power_and_integrated_laneB` modulo
the relaxed Lane B shape (per-E nonemptiness derived structurally
from `(rationalOpen E.1.T E.1.s).Nonempty` rather than supplied
explicitly), composing through T074's allow-empty integrated
consumer. The named source-restricted residual remains the
**per-`(w, t')` σ-power-cleared inequality supplier**. -/
theorem tateAcyclicity_Part2_via_sigma_power_and_integrated_laneB_allow_empty
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCovering A) (hne : C.covers.Nonempty)
    [IsNoetherianRing C.base.P.A₀]
    [IsNoetherianRing (locSubring C.base.P C.base.T C.base.s)]
    [LaurentNormalized C.base]
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    (h_per_call_sigma_power :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
      ∃ (_ : Aˣ) (f : A),
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
        ¬ v.vle f 0 ∧
        (∀ t' ∈ D.T, ∀ w ∈ Spa A A⁺,
          w.vle f C.base.s →
          w.vle (1 : A) t' →
          ¬ w.vle t' 0 →
          ∃ N : ℕ,
            w.vle (t' * D.s ^ N) (D.s ^ (N + 1)) ∧ ¬ w.vle D.s 0) ∧
        (∀ w ∈ rationalOpen (insert f C.base.T) C.base.s,
          ∃ t' ∈ D.T,
            w ∈ rationalOpen ({(1 : A)} : Finset A) t'))
    (f₀ : A)
    (fC : ∀ E : { E // E ∈ C.covers }, presheafValue E.1)
    (hC_compat : ∀ (E₁ E₂ : { E // E ∈ C.covers }) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₁.1.T E₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen E₂.1.T E₂.1.s),
      restrictionMap E₁.1 D₃ h₃₁ (fC E₁) = restrictionMap E₂.1 D₃ h₃₂ (fC E₂))
    (separation_supplier : ∀ C' : RationalCovering A, C'.covers.Nonempty →
      ∀ a b : presheafValue C'.base,
        (∀ (D : RationalLocData A) (hD : D ∈ C'.covers),
          restrictionMap C'.base D (C'.hsubset D hD) a =
            restrictionMap C'.base D (C'.hsubset D hD) b) →
        a = b)
    (hLaneA : PrimaryLaneAInputs C f₀) :
    ∃ x : presheafValue C.base, ∀ E : { E // E ∈ C.covers },
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E :=
  tateAcyclicity_Part2_via_sigma_C1_and_integrated_laneB_allow_empty
    P hA₀_le hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C hne
    h_base_eq_Spa h_covers_nonempty
    (fun D hD v hv t ht hvt hvD => by
      obtain ⟨σ_choice, f, hv_base, hf_ne, h_pow_chain, h_laurent⟩ :=
        h_per_call_sigma_power D hD v hv t ht hvt hvD
      refine ⟨σ_choice, f, hv_base, hf_ne, ?_, h_laurent⟩
      exact SigmaProductClearedInequalitySupplier_via_sigma_power_source_restricted
        D.T C.base.s D.s f h_pow_chain)
    f₀ fC hC_compat separation_supplier hLaneA

end ValuationSpectrum

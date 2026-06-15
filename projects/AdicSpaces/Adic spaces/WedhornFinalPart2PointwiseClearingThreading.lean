/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornFinalPart2NoExtraHypThreading
import «Adic spaces».WedhornDirectUpperBoundSupplierFromPointwiseClearing

/-!
# Wedhorn 8.34(ii) — Part-2 boundary consuming T077 pointwise-clearing
lane (T078)

T074 (commit `3355f41`) lands the final Part-2 threading wrapper
`tateAcyclicity_Part2_via_sigma_C1_and_integrated_laneB` consuming
the named residual `SigmaProductClearedInequalitySupplier`. T077
(`WedhornDirectUpperBoundSupplierFromPointwiseClearing`) lands the
**direct lane** producing `SigmaProductClearedInequalitySupplier`
from a per-`(v, t')` pointwise clearing supplier (upper bound only)
via the closed-form derivation
`SigmaProductClearedInequalitySupplier_via_pointwise_clearing_supplier`.

This file lands the **final-consumer threading layer** for T077's
direct lane: theorem-level wrappers that compose T074 with T077,
exposing the per-call pointwise clearing supplier shape (T067 /
T077 residual) at the consumer boundary instead of the σ-factored
supplier (T075) or `SigmaProductClearedInequalitySupplier` (T074).
The result is the **simplest σ-construction supplier shape** — pure
pointwise upper bound only — at the Part-2 consumer boundary, with
no addition of hypotheses to the final
`ValuationSpectrum.tateAcyclicity` theorem.

## What this file provides

* `tateAcyclicity_Part2_via_pointwise_clearing_and_integrated_laneB`
  — main wrapper composing T074 with T077's pointwise-clearing →
  `SigmaProductClearedInequalitySupplier` lane. Per-call named
  residual: pointwise clearing supplier `∀ t' ∈ D.T, ∀ w ∈ Spa A A⁺,
  w.vle f C.base.s → w.vle 1 t' → ¬ w.vle t' 0 → w.vle t' D.s`. The
  `D.s` non-vanishing is auto-derived inside T077 via the lower bound
  `w.vle 1 t'`.

* `tateAcyclicity_Part2_via_pointwise_clearing_and_integrated_laneB_allow_empty`
  — empty-piece-tolerant variant matching T071's allow-empty consumer
  shape.

## Composition pipeline

```
pointwise clearing supplier (per-call)
  ↓ (SigmaProductClearedInequalitySupplier_via_pointwise_clearing_supplier, T077)
SigmaProductClearedInequalitySupplier (per-call)
  ↓ (tateAcyclicity_Part2_via_sigma_C1_and_integrated_laneB, T074)
∃ x ∈ presheafValue C.base, ∀ E ∈ C.covers,
  restrictionMap C.base E _ x = fC E         [Part 2 of tateAcyclicity]
```

T077 is consumed mechanically; T074 is consumed mechanically. T078
introduces no σ-construction content beyond what T067 / T077 already
expose. The pointwise clearing shape is the simplest σ-construction
supplier shape — the upper bound `w.vle t' D.s` per-`(v, t')` —
matching Wedhorn 8.34(ii)'s natural per-Laurent-piece refinement
output.

## No-extra-hypothesis firewall

This file does **NOT** add any hypothesis to the final
`ValuationSpectrum.tateAcyclicity` theorem. All inputs are documented
intermediate supplier-boundary inputs of the consumer wrappers in
this file, **not** changes to the root theorem signature.

## Notes

* No root import; leaf-level.
* Imports T074's `WedhornFinalPart2NoExtraHypThreading` and T077's
  `WedhornDirectUpperBoundSupplierFromPointwiseClearing`.
* No edits to T031–T077 accepted leaves, root imports, or final
  theorem signatures.
* No revival of T001 / Jacobson / bivariate-overlap / Zavyalov /
  global universal-Spa-bound / σ-power-decay / M-power-decay routes;
  only mechanical composition of two accepted bridges.
* Both wrappers are fully axiom-clean.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsHuberRing A] [HasLocLiftPowerBounded A] [DecidableEq A]

/-- **Final Part-2 wrapper consuming T077's pointwise-clearing direct
lane** (T078 main deliverable, full form).

Composes T074's
`tateAcyclicity_Part2_via_sigma_C1_and_integrated_laneB` with T077's
`SigmaProductClearedInequalitySupplier_via_pointwise_clearing_supplier`.
The per-call σ-construction supply now exposes a **per-`(v, t')`
pointwise clearing supplier** (upper bound only) as the named
source-restricted residual:

```
∀ t' ∈ D.T, ∀ w ∈ Spa A A⁺,
  w.vle f C.base.s → w.vle 1 t' → ¬ w.vle t' 0 →
  w.vle t' D.s
```

This is the simplest σ-construction supplier shape: pure pointwise
upper bound, **no `D.s` non-vanishing required at this layer** (T077
derives it internally via the lower bound `w.vle 1 t'`). It matches
Wedhorn 8.34(ii)'s natural per-Laurent-piece refinement output and
is equivalent to T067's pointwise clearing residual shape.

Output: Part 2 of `tateAcyclicity`. **No hypothesis added to the
root theorem signature.** -/
theorem tateAcyclicity_Part2_via_pointwise_clearing_and_integrated_laneB
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
    (h_per_call_pointwise :
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
          w.vle t' D.s) ∧
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
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  refine tateAcyclicity_Part2_via_sigma_C1_and_integrated_laneB
    P hA₀_le hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C hne
    h_base_eq_Spa h_covers_nonempty ?_ f₀ fC hC_compat
    separation_supplier per_E_nonempty hLaneA
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨σ_choice, f, hv_in_plus, hvf_nz, h_pointwise, h_cover⟩ :=
    h_per_call_pointwise D hD v hv t ht hvt hvD_s
  exact ⟨σ_choice, f, hv_in_plus, hvf_nz,
    SigmaProductClearedInequalitySupplier_via_pointwise_clearing_supplier
      D.T C.base.s D.s f h_pointwise,
    h_cover⟩

/-- **Final Part-2 wrapper consuming T077's pointwise-clearing direct
lane**, allow-empty variant (T078 allow-empty deliverable).

Identical caller signature to
`tateAcyclicity_Part2_via_pointwise_clearing_and_integrated_laneB`
modulo the relaxed Lane B shape (per-E nonemptiness derived
structurally from `(rationalOpen E.1.T E.1.s).Nonempty`), composing
through T074's allow-empty integrated consumer. The named
source-restricted residual remains the per-`(v, t')` pointwise
clearing supplier. -/
theorem tateAcyclicity_Part2_via_pointwise_clearing_and_integrated_laneB_allow_empty
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
    (h_per_call_pointwise :
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
          w.vle t' D.s) ∧
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
      restrictionMap C.base E.1 (C.hsubset E.1 E.2) x = fC E := by
  refine tateAcyclicity_Part2_via_sigma_C1_and_integrated_laneB_allow_empty
    P hA₀_le hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C hne
    h_base_eq_Spa h_covers_nonempty ?_ f₀ fC hC_compat
    separation_supplier hLaneA
  intro D hD v hv t ht hvt hvD_s
  obtain ⟨σ_choice, f, hv_in_plus, hvf_nz, h_pointwise, h_cover⟩ :=
    h_per_call_pointwise D hD v hv t ht hvt hvD_s
  exact ⟨σ_choice, f, hv_in_plus, hvf_nz,
    SigmaProductClearedInequalitySupplier_via_pointwise_clearing_supplier
      D.T C.base.s D.s f h_pointwise,
    h_cover⟩

end ValuationSpectrum

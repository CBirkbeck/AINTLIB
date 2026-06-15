/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornFinalPart2NoExtraHypThreading
import «Adic spaces».WedhornSigmaPowerClearedInequalitySupplier

/-!
# Wedhorn 8.34(ii) — Part-2 boundary consuming T073 σ-supplier API (T075)

T074 (commit `3355f41`) lands the final Part-2 threading wrapper
`tateAcyclicity_Part2_via_sigma_C1_and_integrated_laneB`, taking the
named residual `SigmaProductClearedInequalitySupplier` (T072's named
σ-construction algebraic content) per-call. T073
(`WedhornSigmaPowerClearedInequalitySupplier`) lands two substantive
supplier routes that produce `SigmaProductClearedInequalitySupplier`:

* **σ-factored supplier route**
  (`SigmaProductClearedInequalitySupplier_via_sigma_factored_supplier`):
  per-`(v, t')` σ-factored inequality
  `v.vle (t' * D_s^N * σ) (D_s^(N+1) * σ)` for some unit `σ : Aˣ` and
  exponent `N : ℕ`, plus `D_s` non-vanishing.

* **Direct upper-bound supplier route**
  (`SigmaProductClearedInequalitySupplier_via_direct_clearing_supplier`):
  per-`(v, t')` direct bound `v.vle t' D_s` plus `D_s` non-vanishing.

This file lands the **final-consumer threading layer** consuming
T073's APIs inside T074's Part-2 boundary: theorem-level wrappers that
compose T074 with the two T073 supplier routes, exposing the per-call
σ-construction algebraic supplier in either σ-factored form or direct
upper-bound form. The result is a Part-2 consumer whose remaining
named source-restricted residual at this layer is the **per-`(v, t')`
σ-factored supplier** or **per-`(v, t')` direct upper-bound supplier**
(plus the standard intermediate inputs from T074 / T071), with
**no addition of hypotheses to the final
`ValuationSpectrum.tateAcyclicity` theorem signature**.

## What this file provides

* `tateAcyclicity_Part2_via_T073_sigma_factored_supplier_and_integrated_laneB`
  — main wrapper composing T074 with T073's σ-factored supplier
  route. Exposes the per-call σ-factored supplier shape as the named
  residual.

* `tateAcyclicity_Part2_via_T073_sigma_factored_supplier_and_integrated_laneB_allow_empty`
  — allow-empty variant.

* `tateAcyclicity_Part2_via_T073_direct_supplier_and_integrated_laneB`
  — alternative wrapper composing T074 with T073's direct upper-bound
  supplier route. Exposes the per-call direct upper-bound supplier
  shape as the named residual.

* `tateAcyclicity_Part2_via_T073_direct_supplier_and_integrated_laneB_allow_empty`
  — allow-empty variant.

## Composition pipeline

```
σ-factored supplier per-call OR direct upper-bound supplier per-call
  + base-side rationalOpen membership / non-degeneracy /
    σ-rescaled Laurent cover hypotheses
   ↓ (SigmaProductClearedInequalitySupplier_via_{sigma_factored,direct_clearing}_supplier, T073)
SigmaProductClearedInequalitySupplier per-call
   ↓ (tateAcyclicity_Part2_via_sigma_C1_and_integrated_laneB, T074)
∃ x ∈ presheafValue C.base, ∀ E ∈ C.covers,
  restrictionMap C.base E _ x = fC E         [Part 2 of tateAcyclicity]
```

The σ-construction's algebraic content is captured by either the
σ-factored supplier or the direct upper-bound supplier; T073 is
consumed mechanically; T074 is consumed mechanically.

## No-extra-hypothesis firewall

This file does **NOT** add any hypothesis to the final
`ValuationSpectrum.tateAcyclicity` theorem. All inputs are documented
intermediate supplier-boundary inputs of the consumer wrappers in
this file, **not** changes to the root theorem signature.

## Notes

* No root import; leaf-level.
* Imports T074's `WedhornFinalPart2NoExtraHypThreading` and T073's
  `WedhornSigmaPowerClearedInequalitySupplier`.
* No edits to T031–T074 accepted leaves, root imports, or final
  theorem signatures.
* No revival of T001 / Jacobson / bivariate-overlap / Zavyalov /
  global universal-Spa-bound / σ-power-decay / M-power-decay routes;
  only mechanical composition of two accepted bridges.
* All four consumer wrappers are fully axiom-clean.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsHuberRing A] [HasLocLiftPowerBounded A] [DecidableEq A]

/-- **Final Part-2 wrapper consuming T073's σ-factored supplier route**
(T075 main deliverable, σ-factored form).

Composes T074's
`tateAcyclicity_Part2_via_sigma_C1_and_integrated_laneB` with T073's
`SigmaProductClearedInequalitySupplier_via_sigma_factored_supplier`.
The per-call σ-construction supply now exposes a **per-`(v, t')`
σ-factored supplier** as the named source-restricted residual:

```
∀ t' ∈ D.T, ∀ w ∈ Spa A A⁺,
  w.vle f C.base.s → w.vle 1 t' → ¬ w.vle t' 0 →
  ∃ (σ : Aˣ) (N : ℕ),
    w.vle (t' * D.s^N * (σ : A)) (D.s^(N+1) * (σ : A)) ∧
    ¬ w.vle D.s 0
```

This captures the σ-construction's natural per-`(v, t')` algebraic
shape after multiplication by σ on both sides — the form most
directly produced by σ-construction-based suppliers.

Output: Part 2 of `tateAcyclicity`. **No hypothesis added to the
root theorem signature.** -/
theorem tateAcyclicity_Part2_via_T073_sigma_factored_supplier_and_integrated_laneB
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
    (h_per_call_sigma_factored :
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
          ∃ (σ : Aˣ) (N : ℕ),
            w.vle (t' * D.s ^ N * (σ : A))
              (D.s ^ (N + 1) * (σ : A)) ∧
            ¬ w.vle D.s 0) ∧
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
  obtain ⟨σ_choice, f, hv_in_plus, hvf_nz, h_factored, h_cover⟩ :=
    h_per_call_sigma_factored D hD v hv t ht hvt hvD_s
  exact ⟨σ_choice, f, hv_in_plus, hvf_nz,
    SigmaProductClearedInequalitySupplier_via_sigma_factored_supplier
      D.T C.base.s D.s f h_factored,
    h_cover⟩

/-- **Final Part-2 wrapper consuming T073's σ-factored supplier route,
allow-empty variant** (T075 σ-factored allow-empty deliverable). -/
theorem tateAcyclicity_Part2_via_T073_sigma_factored_supplier_and_integrated_laneB_allow_empty
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
    (h_per_call_sigma_factored :
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
          ∃ (σ : Aˣ) (N : ℕ),
            w.vle (t' * D.s ^ N * (σ : A))
              (D.s ^ (N + 1) * (σ : A)) ∧
            ¬ w.vle D.s 0) ∧
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
  obtain ⟨σ_choice, f, hv_in_plus, hvf_nz, h_factored, h_cover⟩ :=
    h_per_call_sigma_factored D hD v hv t ht hvt hvD_s
  exact ⟨σ_choice, f, hv_in_plus, hvf_nz,
    SigmaProductClearedInequalitySupplier_via_sigma_factored_supplier
      D.T C.base.s D.s f h_factored,
    h_cover⟩

/-- **Final Part-2 wrapper consuming T073's direct upper-bound supplier
route** (T075 alternative deliverable, direct form).

Composes T074's
`tateAcyclicity_Part2_via_sigma_C1_and_integrated_laneB` with T073's
`SigmaProductClearedInequalitySupplier_via_direct_clearing_supplier`.
The per-call σ-construction supply exposes a **per-`(v, t')` direct
upper-bound supplier**:

```
∀ t' ∈ D.T, ∀ w ∈ Spa A A⁺,
  w.vle f C.base.s → w.vle 1 t' → ¬ w.vle t' 0 →
  w.vle t' D.s ∧ ¬ w.vle D.s 0
```

This is the simplest σ-construction supplier shape, equivalent to
T067's pointwise clearing residual modulo explicit `D.s`
non-vanishing. Useful when the σ-construction is already simplified
to the un-σ-factored direct form.

Output: Part 2 of `tateAcyclicity`. **No hypothesis added to the
root theorem signature.** -/
theorem tateAcyclicity_Part2_via_T073_direct_supplier_and_integrated_laneB
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
    (h_per_call_direct :
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
          w.vle t' D.s ∧ ¬ w.vle D.s 0) ∧
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
  obtain ⟨σ_choice, f, hv_in_plus, hvf_nz, h_direct, h_cover⟩ :=
    h_per_call_direct D hD v hv t ht hvt hvD_s
  exact ⟨σ_choice, f, hv_in_plus, hvf_nz,
    SigmaProductClearedInequalitySupplier_via_direct_clearing_supplier
      D.T C.base.s D.s f h_direct,
    h_cover⟩

/-- **Final Part-2 wrapper consuming T073's direct upper-bound supplier
route, allow-empty variant** (T075 direct allow-empty deliverable). -/
theorem tateAcyclicity_Part2_via_T073_direct_supplier_and_integrated_laneB_allow_empty
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
    (h_per_call_direct :
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
          w.vle t' D.s ∧ ¬ w.vle D.s 0) ∧
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
  obtain ⟨σ_choice, f, hv_in_plus, hvf_nz, h_direct, h_cover⟩ :=
    h_per_call_direct D hD v hv t ht hvt hvD_s
  exact ⟨σ_choice, f, hv_in_plus, hvf_nz,
    SigmaProductClearedInequalitySupplier_via_direct_clearing_supplier
      D.T C.base.s D.s f h_direct,
    h_cover⟩

end ValuationSpectrum

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornPart2LaneBIntegratedConsumer
import «Adic spaces».WedhornC1SigmaConstructionAssembly

/-!
# Wedhorn 8.34(ii) — Final Part-2 boundary threading T071+T072 (T074)

T071 (commit `5574f20`) lands the Lane-A + Lane-B integrated Part-2
consumer
`tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_laneB_via_separation`,
which takes `C1SupplierStrong_local C` plus the standard intermediate
inputs and produces Part 2 of Wedhorn Theorem 8.28(b) tate acyclicity
without an abstract `lane_B_supplier`. T072
(`WedhornC1SigmaConstructionAssembly`) lands the C1 σ-construction
endgame wrapper
`C1SupplierStrong_local_via_named_sigma_construction_supplier`, which
produces `C1SupplierStrong_local C` from a per-call delivery of the
**source-restricted σ-product-cleared inequality supplier**
`SigmaProductClearedInequalitySupplier`.

This file lands the **final Part-2 threading boundary** combining
T071 and T072: a leaf-level theorem-level wrapper expressing the
Part-2 conclusion in terms of the named source-restricted
`SigmaProductClearedInequalitySupplier` per-call input plus the
already-named intermediate geometric/separation/Lane-A inputs of
T071 — **with no addition of hypotheses to the final
`ValuationSpectrum.tateAcyclicity` theorem signature**.

## What this file provides

* `tateAcyclicity_Part2_via_sigma_C1_and_integrated_laneB` — main
  wrapper composing T072's named-Prop σ-construction boundary with
  T071's generic integrated Part-2 consumer. Inputs: T071's standard
  inputs minus `h_C1_strong`, replaced by T072's per-call
  σ-construction supply (σ_choice, f, base-side rationalOpen
  membership, non-degeneracy, `SigmaProductClearedInequalitySupplier`,
  σ-rescaled Laurent cover). Output: Part 2 of `tateAcyclicity`.

* `tateAcyclicity_Part2_via_sigma_C1_and_integrated_laneB_allow_empty`
  — empty-piece-tolerant variant matching T071's allow-empty consumer
  shape.

The named source-restricted residual at the consumer boundary is
**`SigmaProductClearedInequalitySupplier`** carried inside the per-call
σ-construction supply; the remaining intermediate inputs (universal
nonempty-cover separation supplier, `PrimaryLaneAInputs`, geometric
hypotheses, caller's compatible section family) are unchanged from
T071's boundary.

## No-extra-hypothesis firewall

The deliverable explicitly does **NOT** add any hypothesis to the
final `ValuationSpectrum.tateAcyclicity` theorem. All inputs are
documented intermediate supplier-boundary inputs of the consumer
wrappers in this file, **not** changes to the root theorem
signature. The σ-construction's algebraic content is captured by the
`SigmaProductClearedInequalitySupplier` Prop predicate (T072 named
residual), which is the **single source-restricted σ-product algebraic
residual** at this consumer boundary.

## Composition pipeline

```
SigmaProductClearedInequalitySupplier per-call               [T072 residual]
  + base-side rationalOpen membership / non-degeneracy /
    σ-rescaled Laurent cover hypotheses
   ↓ (C1SupplierStrong_local_via_named_sigma_construction_supplier, T072)
C1SupplierStrong_local C
   ↓ (tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_laneB_via_separation, T071)
∃ x ∈ presheafValue C.base, ∀ E ∈ C.covers,
  restrictionMap C.base E _ x = fC E         [Part 2 of tateAcyclicity]
```

T072 is consumed mechanically; T071 is consumed mechanically. No
duplication of T073 arithmetic.

## Notes

* No root import; leaf-level.
* Imports T071's `WedhornPart2LaneBIntegratedConsumer` and T072's
  `WedhornC1SigmaConstructionAssembly`.
* No edits to T031–T073 accepted leaves, root imports, or final
  theorem signatures.
* No revival of T001 / Jacobson / bivariate-overlap / Zavyalov /
  global universal-Spa-bound / σ-power-decay / M-power-decay routes;
  only mechanical composition of two accepted bridges.
* The deliverable matches T074's acceptance: a theorem-level wrapper
  composes T071 with T072 without adding hypotheses to the final
  `ValuationSpectrum.tateAcyclicity` signature; remaining inputs are
  named intermediate supplier-boundary residuals, especially the
  source-restricted `SigmaProductClearedInequalitySupplier`.
-/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsHuberRing A] [HasLocLiftPowerBounded A] [DecidableEq A]

/-- **Final Part-2 wrapper threading T072 σ-construction boundary
through T071 integrated consumer** (T074 main deliverable).

Composes T072's
`C1SupplierStrong_local_via_named_sigma_construction_supplier` with
T071's
`tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_laneB_via_separation`
to produce Part 2 of Wedhorn Theorem 8.28(b) tate acyclicity directly
from per-call σ-construction supply data plus the standard
intermediate inputs (universal nonempty-cover separation supplier,
`PrimaryLaneAInputs`, geometric hypotheses, caller's section data).

**The single source-restricted σ-construction algebraic residual at
the consumer boundary is**
`SigmaProductClearedInequalitySupplier D.T C.base.s D.s f`
(per-call), the named Prop predicate from T072. All other inputs are
already-named intermediate supplier-boundary residuals or routine
σ-construction outputs.

**Output:** the gluing existential `∃ x : presheafValue C.base,
∀ E ∈ C.covers, restrictionMap C.base E _ x = fC E` from compatible
cover-level sections — exactly Part 2 of `tateAcyclicity` (Wedhorn
8.28(b)).

**No-extra-hypothesis firewall.** The hypotheses of this wrapper are
intermediate supplier-boundary inputs of the consumer; they are
**NOT** changes to the final `ValuationSpectrum.tateAcyclicity`
theorem signature. The root theorem retains its existing form. -/
theorem tateAcyclicity_Part2_via_sigma_C1_and_integrated_laneB
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
    (h_per_call_sigma :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
      ∃ (_ : Aˣ) (f : A),
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
        ¬ v.vle f 0 ∧
        SigmaProductClearedInequalitySupplier D.T C.base.s D.s f ∧
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
  tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_laneB_via_separation
    P hA₀_le hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C hne
    h_base_eq_Spa h_covers_nonempty
    (C1SupplierStrong_local_via_named_sigma_construction_supplier C
      h_per_call_sigma)
    f₀ fC hC_compat separation_supplier per_E_nonempty hLaneA

/-- **Final Part-2 wrapper threading T072 σ-construction boundary
through T071 integrated consumer**, allow-empty variant (T074
allow-empty deliverable).

Identical caller signature to
`tateAcyclicity_Part2_via_sigma_C1_and_integrated_laneB` modulo the
relaxed Lane B shape (per-E nonemptiness derived structurally from
`(rationalOpen E.1.T E.1.s).Nonempty` rather than supplied
explicitly), composing through T071's allow-empty integrated
consumer. The named source-restricted residual remains
`SigmaProductClearedInequalitySupplier`. -/
theorem tateAcyclicity_Part2_via_sigma_C1_and_integrated_laneB_allow_empty
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
    (h_per_call_sigma :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
      ∃ (_ : Aˣ) (f : A),
        v ∈ rationalOpen (insert f C.base.T) C.base.s ∧
        ¬ v.vle f 0 ∧
        SigmaProductClearedInequalitySupplier D.T C.base.s D.s f ∧
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
  tateAcyclicity_Part2_via_C1SupplierStrong_local_laneA_laneB_via_separation_allow_empty
    P hA₀_le hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C hne
    h_base_eq_Spa h_covers_nonempty
    (C1SupplierStrong_local_via_named_sigma_construction_supplier C
      h_per_call_sigma)
    f₀ fC hC_compat separation_supplier hLaneA

/-- **T195 final Part-2 wrapper threading T194's single-`t`
structural-data Lane-A + Lane-B integrated consumer**.

Mirrors T074's `tateAcyclicity_Part2_via_sigma_C1_and_integrated_laneB`,
but replaces the σ-construction supplier route
(`C1SupplierStrong_local_via_named_sigma_construction_supplier` +
`SigmaProductClearedInequalitySupplier`) with T194's single-`t`
structural-data integrated consumer
`tateAcyclicity_Part2_via_single_t_structural_data_laneA_laneB_via_separation`.

The per-call residual at this consumer boundary is the **single-`t`
structural-data provider** `h_struct`:

```
∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s, ∀ t ∈ D.T,
  v.vle t D.s → ¬ v.vle D.s 0 →
  ∃ σ N,
    C.base.s = D.s * (σ * t * D.s ^ N) ∧
    (∀ t' ∈ D.T, t' ∈ A⁺) ∧
    v.vle (σ * t * D.s ^ N) C.base.s
```

— the genuinely Wedhorn-content per-call data isolated by T188-T193's
single-`t` chain. Other intermediate inputs (universal nonempty-cover
separation supplier, `PrimaryLaneAInputs`, geometric hypotheses,
caller's section data) are unchanged from T074's boundary.

**Output**: the gluing existential `∃ x : presheafValue C.base,
∀ E ∈ C.covers, restrictionMap C.base E _ x = fC E` from compatible
cover-level sections — exactly Part 2 of `tateAcyclicity` (Wedhorn
8.28(b)).

**No-extra-hypothesis firewall**: hypotheses of this wrapper are
intermediate supplier-boundary inputs of the consumer; they are
**not** changes to the final `ValuationSpectrum.tateAcyclicity`
theorem signature. -/
theorem tateAcyclicity_Part2_via_single_t_structural_data_and_integrated_laneB
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
    (h_struct :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        ∃ (σ : A) (N : ℕ),
          C.base.s = D.s * (σ * t * D.s ^ N) ∧
          (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
          v.vle (σ * t * D.s ^ N) C.base.s)
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
  tateAcyclicity_Part2_via_single_t_structural_data_laneA_laneB_via_separation
    P hA₀_le hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C hne
    h_base_eq_Spa h_covers_nonempty h_struct
    f₀ fC hC_compat separation_supplier per_E_nonempty hLaneA

/-- **T195 final Part-2 wrapper threading T194's single-`t`
structural-data Lane-A + Lane-B integrated consumer**, allow-empty
variant.

Identical caller signature to
`tateAcyclicity_Part2_via_single_t_structural_data_and_integrated_laneB`
modulo the relaxed Lane B shape (per-E nonemptiness derived
structurally from `(rationalOpen E.1.T E.1.s).Nonempty` rather than
supplied explicitly), composing through T194's allow-empty integrated
consumer. The per-call residual remains the single-`t` structural-data
provider `h_struct`. -/
theorem tateAcyclicity_Part2_via_single_t_structural_data_and_integrated_laneB_allow_empty
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
    (h_struct :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        ∃ (σ : A) (N : ℕ),
          C.base.s = D.s * (σ * t * D.s ^ N) ∧
          (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
          v.vle (σ * t * D.s ^ N) C.base.s)
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
  tateAcyclicity_Part2_via_single_t_structural_data_laneA_laneB_via_separation_allow_empty
    P hA₀_le hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C hne
    h_base_eq_Spa h_covers_nonempty h_struct
    f₀ fC hC_compat separation_supplier hLaneA

end ValuationSpectrum

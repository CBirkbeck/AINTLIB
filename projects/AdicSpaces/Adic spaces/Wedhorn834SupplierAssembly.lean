/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornBaseSpaFinalBridgeStrong
import «Adic spaces».WedhornC1StrongSupplierBridge

/-!
# Wedhorn 8.34(ii) Supplier Assembly Skeleton

Highest-level caller theorem on the Wedhorn 8.34(ii) supplier route
toward Tate acyclicity. Composes the **unnormalized** abstract strong
C1 supplier `C1SupplierStrong_local C` with the existing chain of
landed bridges, producing the `hZavyalov_per_E` discharge consumed by
the final acyclicity assembly. All remaining dependencies are exposed
as named theorem hypotheses.

## Composition pipeline (each piece committed; see git log)

```
C1SupplierStrong_local C                                 ← residual H₃ (Tertiary lane)
  ↓  (via WedhornC1StrongSupplierBridge.C1SupplierStrong_local_insertDenom_lift,
     under H₂: ∀ D ∈ C.covers, D.T.Nonempty)
C1SupplierStrong_local C.insertDenom
  ↓  (via WedhornNormalizedC1AssemblyStrong.exists_per_D_finset_via_normalized_C1Strong_supplier
     under standard Tate hypotheses H₀)
∃ mk_S_D, h_in_D ∧ h_cover_D_nonzero          (per-D Finset, strong coverage)
  ↓  (via WedhornStage2SpanExtractor.span_top_via_strengthened_cover_and_outside_rescue
     under H₁: rationalOpen C.base.T C.base.s = Spa A A⁺
     and WedhornOutsideRescue.outside_rescue_pointwise_of_base_eq_Spa)
Ideal.span (biUnion mk_S_D) = ⊤  (h_span)
  ↓  (via StandardCover.hZavyalov_per_E_of_per_D_construction
     under standard rational-open ≠ ∅ premise)
∃ S, refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S
                                                  ← consumed by Tate acyclicity
```

`hZavyalov_per_E_via_normalized_C1Strong_supplier_of_base_eq_Spa`
(commit `b152aa7`) already wires steps 2-5; this file adds step 1
(the `insertDenom` lift) on top, exposing the unnormalized supplier as
a residual.

## What this file provides

* `hZavyalov_per_E_via_unnormalized_C1Strong_supplier_of_base_eq_Spa`
  — the assembly theorem composing all currently-landed pieces. Inputs:
  the standard Tate hypothesis bundle (H₀), the base-equals-Spa
  specialization (H₁), the cover-piece nonempty hypothesis (H₂), and
  the unnormalized abstract strong supplier (H₃). Output: the
  `hZavyalov_per_E` shape consumed by Tate acyclicity. Sorry-free,
  axiom-clean.

## Residual hypothesis list (shortest remaining dependency for closing acyclicity)

* **H₃ — `C1SupplierStrong_local C`**: the Wedhorn 8.34(ii) σ-and-ratio
  construction on the original (un-normalized) cover. Documented as
  the missing target signature `produce_C1SupplierStrong_local_via_Wedhorn_834`
  at `WedhornC1StrongSupplierBridge.lean:66`. Proof would proceed via
  pre-localisation at `C.base.s`, Cor 7.32 inside `Spa(A_loc, A_loc⁺)`,
  denominator clearing, and `f := σ * t * D.s ^ N`. Tertiary's
  `WEDHORN-EXTEND-VALUATION-LOC-TOPOLOGY-CONTINUITY` and Secondary's
  `WEDHORN-DOMINATING-UNIT-INEQUALITY-CORE` lanes are working toward
  this. Once landed, `H₃` is dischargeable directly from the Tate
  hypothesis bundle and the cover.

* **H₁ — `rationalOpen C.base.T C.base.s = Spa A A⁺`**: the base-Spa
  specialization assumed by `WedhornBaseSpaFinalBridgeStrong`. For
  rational coverings of the *full* adic spectrum (`C.base.T = ∅`,
  `C.base.s = 1`), this is automatic; for nested rational subsets the
  user must reduce to this case via a base-restriction step. The
  base-restriction reduction is a separate generalization (not in this
  file's scope).

* **H₂ — `∀ D ∈ C.covers, D.T.Nonempty`**: a mild non-emptiness
  hypothesis on cover-piece test families, required by
  `WedhornC1StrongSupplierBridge.C1SupplierStrong_local_insertDenom_lift`.
  Excludes only the degenerate `D.T = ∅` (basic-open-at-`D.s`) subcase.
  Trivially satisfied in any practical Wedhorn-style cover.

## Notes

* No root import; leaf-level file. Imports only the two highest-level
  Wedhorn supplier files (`WedhornBaseSpaFinalBridgeStrong`,
  `WedhornC1StrongSupplierBridge`) plus their transitive closure.
* No edits to other files. No final-acyclicity signature changes,
  no T001 / Lane B / Cor832 / Jacobson / faithful-flatness /
  non-open-prime content.
* Axioms (verified post-build): only `propext`, `Classical.choice`,
  `Quot.sound`. -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsTopologicalRing A]

/-- **Wedhorn 8.34(ii) supplier assembly — `hZavyalov_per_E` discharge
under the standard Tate hypothesis bundle, base-equals-Spa
specialization, cover-piece nonemptiness, and the abstract unnormalized
strong C1 supplier on the original cover.**

Composes:

1. `WedhornC1StrongSupplierBridge.C1SupplierStrong_local_insertDenom_lift`
   — lifts the unnormalized strong supplier (H₃) to the normalized
   cover under H₂.
2. `WedhornBaseSpaFinalBridgeStrong.hZavyalov_per_E_via_normalized_C1Strong_supplier_of_base_eq_Spa`
   — closes the chain to `hZavyalov_per_E` under H₀ and H₁.

The output is exactly the
`rationalOpen C.base.T C.base.s ≠ ∅ → ∃ S, refines_cover_per_E ∧
refines_contain ∧ refines_span_top` shape consumed by the final Tate
acyclicity assembly. -/
theorem hZavyalov_per_E_via_unnormalized_C1Strong_supplier_of_base_eq_Spa
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCovering A)
    -- Residual H₁: base-Spa specialization (consumed by the outside-rescue
    -- pointwise-of-base-eq-Spa branch).
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    -- Residual H₂: cover-piece test-family non-emptiness (consumed by the
    -- insertDenom strong-supplier lift).
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    -- Residual H₃: the genuine Wedhorn 8.34(ii) σ-and-ratio supplier on
    -- the original (un-normalized) cover. The current external target.
    (h_C1_unnormalized : C1SupplierStrong_local C) :
    rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S := by
  -- Step 1: lift the unnormalized supplier to the normalized cover.
  have h_C1_normalized : C1SupplierStrong_local C.insertDenom :=
    C1SupplierStrong_local_insertDenom_lift C h_covers_nonempty h_C1_unnormalized
  -- Step 2: close to hZavyalov_per_E via the base-Spa final bridge strong.
  exact hZavyalov_per_E_via_normalized_C1Strong_supplier_of_base_eq_Spa
    P hA₀_le hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C h_base_eq_Spa h_C1_normalized

/-- **Wedhorn 8.34(ii) supplier assembly — `hZavyalov_per_E` discharge
from honest Wedhorn 8.34-style single-`t` structural per-call data**
(T192 sibling of `hZavyalov_per_E_via_unnormalized_C1Strong_supplier_of_base_eq_Spa`).

Replaces the abstract residual `h_C1_unnormalized : C1SupplierStrong_local C`
with the **explicit single-`t` σ/N structural per-call provider**
`h_struct` consumed by T191's
`C1SupplierStrong_local_insertDenom_via_single_t_structural_data`. The
provider supplies, for each `D ∈ C.covers`, `v ∈ rationalOpen D.T D.s`,
and `t ∈ D.T` with `v.vle t D.s ∧ ¬ v.vle D.s 0`, an explicit
`(σ : A) (N : ℕ)` with:

* the base-side factorization `C.base.s = D.s * (σ * t * D.s ^ N)`,
* test-family integrality `∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)`,
* and the `f`-membership `v.vle (σ * t * D.s ^ N) C.base.s`.

These are exactly the honest Wedhorn 8.34(ii) σ/N data delivered by
T188's `rationalOpen_subset_via_single_t_sigma_N_data` and the T185
power-cleared `f`-construction lane.

Composition pipeline:

1. T191 (`C1SupplierStrong_local_insertDenom_via_single_t_structural_data`)
   → `C1SupplierStrong_local C.insertDenom` directly from `h_struct`
   under `h_covers_nonempty`. (T191 internally wraps the lift via
   `C1SupplierStrong_local_insertDenom_lift`, so no separate
   un-normalized lift step is needed here.)
2. `WedhornBaseSpaFinalBridgeStrong.hZavyalov_per_E_via_normalized_C1Strong_supplier_of_base_eq_Spa`
   → closes to `hZavyalov_per_E` under H₀ (Tate hypothesis bundle) and
   H₁ (`rationalOpen C.base.T C.base.s = Spa A A⁺`).

This sibling theorem is the **same conclusion** as the unnormalized-
supplier version above, with the `h_C1_unnormalized` residual replaced
by the strictly-stronger explicit single-`t` structural provider. The
output is exactly the `hZavyalov_per_E` shape consumed by the final
Tate acyclicity assembly. Sorry-free, axiom-clean. -/
theorem hZavyalov_per_E_via_single_t_structural_data_of_base_eq_Spa
    [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [DecidableEq A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    [IsAdicComplete P.I P.A₀]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCovering A)
    -- Residual H₁: base-Spa specialization (consumed by the outside-rescue
    -- pointwise-of-base-eq-Spa branch).
    (h_base_eq_Spa : rationalOpen C.base.T C.base.s = Spa A A⁺)
    -- Residual H₂: cover-piece test-family non-emptiness (consumed by the
    -- T191 insertDenom strong-supplier from-structural-data wrapper).
    (h_covers_nonempty : ∀ D ∈ C.covers, D.T.Nonempty)
    -- Residual H₃: explicit single-`t` σ/N structural per-call provider —
    -- the strictly-stronger replacement of the abstract `C1SupplierStrong_local C`,
    -- matching T188's σ/N data shape and T191's structural-data input.
    (h_struct :
      ∀ (D : RationalLocData A), D ∈ C.covers →
      ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
      ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
        ∃ (σ : A) (N : ℕ),
          C.base.s = D.s * (σ * t * D.s ^ N) ∧
          (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
          v.vle (σ * t * D.s ^ N) C.base.s) :
    rationalOpen C.base.T C.base.s ≠ ∅ →
      ∃ S : Finset A,
        refines_cover_per_E C S ∧ refines_contain C S ∧ refines_span_top S := by
  -- Step 1: build the normalized strong C1 supplier directly from h_struct
  -- via T191. T191 internally bundles the un-normalized supplier and the
  -- insertDenom lift; we consume its output directly.
  have h_C1_normalized : C1SupplierStrong_local C.insertDenom :=
    C1SupplierStrong_local_insertDenom_via_single_t_structural_data
      C h_covers_nonempty h_struct
  -- Step 2: close to hZavyalov_per_E via the base-Spa final bridge strong.
  exact hZavyalov_per_E_via_normalized_C1Strong_supplier_of_base_eq_Spa
    P hA₀_le hAplus_le_A₀ π hI hπ_tn hπ_unit hArch C h_base_eq_Spa h_C1_normalized

/-! ### T197 blocker packet: first missing upstream theorem for the
T192/T195 `h_struct` per-call provider

The T192 theorem `hZavyalov_per_E_via_single_t_structural_data_of_base_eq_Spa`
and the final-threading T195 wrappers all consume the per-call
single-`t` structural-data provider

```
h_struct :
  ∀ D ∈ C.covers, ∀ v ∈ rationalOpen D.T D.s, ∀ t ∈ D.T,
    v.vle t D.s → ¬ v.vle D.s 0 →
    ∃ (σ : A) (N : ℕ),
      C.base.s = D.s * (σ * t * D.s ^ N) ∧
      (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
      v.vle (σ * t * D.s ^ N) C.base.s
```

Producing this provider from concrete Tate / pseudouniformizer / cover
setup data requires a **per-`(D, t)` algebraic factorization in `A`
itself** — not via denominator clearing in `Localization.Away C.base.s`
(which gives only power-cleared identities; see T185) — captured by
the precise missing Lean type:

```
def wedhorn_834_h_struct_factorization_first_missing_upstream
    [DecidableEq A]
    (C : RationalCovering A) : Prop :=
  ∀ (D : RationalLocData A), D ∈ C.covers →
  ∀ (t : A), t ∈ D.T →
    ∃ (σ : A) (N : ℕ), C.base.s = D.s * (σ * t * D.s ^ N)
```

(target file: `Adic spaces/Wedhorn834SupplierAssembly.lean` or a new
leaf-level helper).

**Existing APIs checked — none produce this factorization**:

* `Cor732.exists_dominating_unit` — produces a unit `σ : Aˣ` with
  σ-strict-domination over a test family, but NOT the multiplicative
  identity `C.base.s = D.s · σ · t · D.s^N` in `A`. The σ-strict-dom
  output is a per-`v` valuative inequality, not an algebraic factor.

* `WedhornLocalizationDenominatorClearing.exists_away_denominator_cleared`
  — produces `(a : A, n : ℕ)` with `x · (algebraMap C.base.s)^n =
  algebraMap a` in `Loc C.base.s`. The identity is in the
  **localization**, not in `A`; T185/T186 confirmed exact lifts back to
  `A` require the structural condition `n = 0` (not derivable from
  standard denominator clearing).

* `RationalCovering.hsubset` — gives only the rational-open subset
  relation `rationalOpen D.T D.s ⊆ rationalOpen C.base.T C.base.s`, no
  underlying algebraic identity.

* `StandardCover` — finite family generating the unit ideal in `A`;
  ideal-theoretic, no per-`(D, t)` factorization data.

* The Wedhorn 8.34(ii) Step-2 algebraic identity in the literature
  picks `f := σ · t · D.s^(N - 1)` for σ from Cor 7.32 and `N` chosen
  via Spa-quasi-compactness; the identity `C.base.s = D.s · f` then
  holds **by the cover-refinement choice of `f`** — i.e., the
  factorization is **enforced by the construction of `f`**, not
  derived from standard denominator clearing.

**Why this blocker boundary avoids the parked false lanes**:

* **No σ-power-decay**: this is a single per-`(D, t)` algebraic identity
  in `A`, not a Spa-uniform `w.vle (C_base) (σ · D.s^(N+1))` shape.
* **No M_power_decay**: no Spa-quasi-compactness / M-choice over Spa
  points.
* **No locSubring-integrally-closed**: no integral closure axiom; the
  identity is in `A`, no localization or integrality hypothesis.
* **No multi-product exact `h_alg`**: no `∏ D.T.image` product; the
  factorization is single-`t` (uses one chosen `t ∈ D.T`).
* **No denominator-clearing `n = 0`**: the factorization is in `A`
  directly, not via a power-cleared lift from `Loc C.base.s`.
* **No σ-strict-domination clause-2**: no σ-strict-domination over a
  test family; the σ in this factorization is an arbitrary `A`-element,
  not a Cor 7.32 unit.

**Resolution paths** (the next theorem-level ticket would):

(a) **Specific cover construction**: prove the factorization for a
    concrete cover-refinement family (e.g., the per-`E` localized cover
    `C.per_E_local_covering`, or an explicit Wedhorn 8.34(ii) Step-2
    construction with `f := σ · t · D.s^(N-1)`).

(b) **Add as structural hypothesis**: thread the algebraic
    factorization through a new T192/T195 variant that takes it as
    an explicit per-call structural input, with the source f-bound and
    Tate condition derived (or supplied) separately.

The preferred path is (a) for an end-to-end discharge from concrete
Tate/cover data; the acceptable path is (b) for a precise structural
boundary at a fresh manager-designed level.

Note: this blocker is the genuine Wedhorn 8.34(ii) cover-refinement
element construction at the algebraic level — distinct from all the
parked false lanes above. Its discharge is the next critical-path
theorem-level work after the accepted T188-T195 honest single-`t`
chain. -/

/-! ### T198: concrete cover construction supplying the h_struct factorization

This section addresses T197's resolution path (a): produce a concrete
cover construction supplying the `h_struct` factorization of T191/T192
/T195. The deliverable is two-fold:

1. A **concrete compiled theorem** (`h_struct_for_global_trivial_covering`)
   for the **degenerate whole-Spa covering** with base and single piece
   both `globalLocData P` (so `T = {1}, s = 1`); the factorization holds
   trivially via `σ := 1, N := 0, t := 1`.

2. A **precise blocker packet** for the general non-trivial case,
   identifying why existing concrete constructions
   (`per_E_local_covering`, `laurentPlusDatum`, `laurentMinusDatum`) do
   NOT supply the factorization, and naming the **missing constructor/
   API** for a non-trivial Wedhorn 8.34(ii) Step-2 cover with the
   algebraic factorization data carried by construction.

## Why the trivial whole-Spa covering works

Take `C := { base := globalLocData P, covers := {globalLocData P} }`.
Then for the unique `D = globalLocData P`:

* `D.s = 1`, so `D.s | C.base.s = 1` trivially.
* `D.T = {1}`, so the only `t ∈ D.T` is `t = 1`.
* The factorization `C.base.s = D.s * (σ * t * D.s^N) = 1 = 1 * (1 * 1
  * 1^0) = 1` holds with `σ = 1, N = 0, t = 1`.
* The Tate condition `1 ∈ A⁺` holds in any subring.
* The f-bound `v.vle (1 * 1 * 1^0) 1 = v.vle 1 1` is reflexive.

This is a **valid concrete cover construction** supplying `h_struct`
exactly. It is the simplest such construction in the project, and
demonstrates that path (a) is feasible at least for whole-Spa Tate
acyclicity. It does **not** generalize: for any non-trivial cover with
`D.T ⊋ {1}` or `D.s ≠ 1`, the factorization fails (see audit below).

## Why non-trivial concrete constructions fail

Audit of existing `RationalLocData`/`RationalCovering` constructors,
checking whether each supplies `C.base.s = D.s * (σ * t * D.s ^ N)` in
`A` for `D ∈ C.covers` and `t ∈ D.T`:

* **`laurentPlusDatum D₀ f`** (in `Adic spaces/LaurentRefinement.lean`,
  line 102): `s := D₀.s`, `T := insert f D₀.T`. So for `C.base = D₀`
  and `D = laurentPlusDatum D₀ f`, `D.s = C.base.s` and
  `D.T = insert f C.base.T`. The factorization
  `C.base.s = C.base.s * (σ * t * C.base.s^N)` requires
  `σ * t * C.base.s^N = 1`. For arbitrary `t ∈ D.T = insert f C.base.T`,
  this is restrictive (requires `t * C.base.s^N` to be a unit in `A`
  with `σ = 1/(t * C.base.s^N)` an actual `A`-element).

* **`laurentMinusDatum D₀ f`** (in `Adic spaces/LaurentRefinement.lean`,
  line 203): `s := D₀.s * f`, `T := (insert D₀.s D₀.T).product
  ({D₀.s, f} : Finset A) |>.image (fun p => p.1 * p.2)`. So
  `D.s = C.base.s * f`. Then the factorization
  `C.base.s = D.s * (σ * t * D.s^N) = (C.base.s * f)^(N+1) * σ * t`.
  For `N = 0`: `C.base.s = C.base.s * f * σ * t`, requiring
  `f * σ * t = 1`. Restrictive (requires `f * t` to be a unit). For
  `N ≥ 1`: even more restrictive due to the `(C.base.s * f)^(N+1)`
  factor. **Wrong direction**: `D.s` is a multiple of `C.base.s`, not
  a divisor.

* **`RationalCovering.per_E_local_covering C S f₀ E hprecise`** (in
  `Adic spaces/GeometricReduction.lean`, line 5431): base = `E.1`,
  covers built from `laurentPlusDatum`/`laurentMinusDatum` of
  `C.plusDatum f` for filtered `f ∈ S`. The pieces inherit the
  `laurentPlus`/`laurentMinus` structure from `C.plusDatum f`, so the
  factorization fails for the same reasons as above (with
  `C.base.s ↦ E.1.s`).

* **`globalLocData P`** (in `Adic spaces/Presheaf.lean`, line 547):
  `T := {1}, s := 1`. The trivial whole-Spa covering using this for
  both base and single piece DOES supply the factorization (see
  `h_struct_for_global_trivial_covering` below) — but only because all
  factorization parameters reduce to `1` in `A`. No non-trivial cover
  data.

* **`RationalCovering.insertDenom`** (in
  `Adic spaces/WedhornCoverNormalization.lean`, line 104): adds `D.s`
  to `D.T` without changing `D.s`. Does not introduce any algebraic
  factorization data; same issue as the underlying covering.

* **`WedhornStandardCoverRefinement.exists_single_f_refinement_at_t_via_dominating_unit`**
  (target signature, line 419-462, **MISSING in project**): proposes
  `f := σ * t * D.s ^ (N-1)` with `R(insert f C.base.T, C.base.s) ⊆
  R(D.T, D.s)` (rationalOpen subset, NOT algebraic equality). Even if
  this target signature were filled, it would NOT supply the algebraic
  identity `C.base.s = D.s * f` in `A` — that is a **strictly stronger
  property** than the rationalOpen subset relation Wedhorn's actual
  cover-refinement provides.

## Missing constructor/API (proposed signature)

The lowest missing construction is a **Wedhorn 8.34(ii) Step-2 cover
construction with algebraic factorization data carried by
construction** — a refinement of the existing missing
`exists_single_f_refinement_at_t_via_dominating_unit` that ALSO supplies
the per-piece algebraic identity in `A`:

```
def WedhornStep2RefinementCarryingFactor (C : RationalCovering A) :
    Type :=
  { D : RationalLocData A //
      D ∈ C.covers ∧
      ∀ (t : A), t ∈ D.T →
        ∃ (σ : A) (N : ℕ), C.base.s = D.s * (σ * t * D.s ^ N) }

theorem RationalCovering.exists_step2_refinement_carrying_factor
    [DecidableEq A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) (hA₀_le : P.A₀ ≤ A⁺)
    (π : P.A₀) (hI : P.I = Ideal.span {π})
    (hπ_tn : IsTopologicallyNilpotent (P.A₀.subtype π))
    (hπ_unit : IsUnit (P.A₀.subtype π))
    (hArch : ∀ v : Spv A, letI : ValuativeRel A := v.toValuativeRel
        MulArchimedean (ValuativeRel.ValueGroupWithZero A))
    (C : RationalCovering A) :
    Nonempty (∀ D ∈ C.covers, WedhornStep2RefinementCarryingFactor C)
```

This constructor does NOT exist in the project. Its construction is
genuine Wedhorn 8.34(ii) Step-2 content beyond what
`exists_single_f_refinement_at_t_via_dominating_unit` (parameterized
target) provides. The natural way to discharge it is to construct, for
each piece D and each `t ∈ D.T`, a NEW cover-piece D' with `D'.s :=
σ * t * D.s ^ N` for some `(σ, N)` chosen via Cor 7.32 +
Spa-quasi-compactness, and then VERIFY both the rationalOpen inclusion
`R(D'.T, D'.s) ⊆ R(D.T, D.s)` AND the algebraic identity
`D.s * D'.s = C.base.s` (or similar). Constructing such D' AND showing
it covers the right rationalOpens is non-trivial.

**How this feeds T195 h_struct**: given
`exists_step2_refinement_carrying_factor`, the per-call provider
`h_struct` for a refined covering `C'` (where each piece carries the
factorization) is direct extraction of the `(σ, N)` plus auxiliary
verification of `D'.T ⊆ A⁺` and `v.vle (σ * t * D.s ^ N) C.base.s`.
The first follows from the cover-refinement integrality (D' is built
from t ∈ A⁺ and powers of D.s ∈ A⁺); the second from the rationalOpen
subset relation evaluated at `v`.

## Why this avoids the parked false lanes

* **No σ-power-decay**: the factorization is per-`(D, t)` algebraic,
  not Spa-uniform.
* **No M-power-decay**: no Spa-quasi-compactness M-choice over the
  whole Spa.
* **No locSubring-integrally-closed**: no integral closure axiom in the
  factorization.
* **No multi-product exact `h_alg`**: single-`t` factorization, no
  `∏ D.T.image`.
* **No denominator-clearing `n = 0`**: the factorization is in `A`
  directly; lifting from `Loc C.base.s` is irrelevant.
* **No σ-strict-domination clause-2**: the σ in the factorization is
  an arbitrary `A`-element produced by the construction, not a Cor 7.32
  unit (though Cor 7.32 may be used inside the construction). -/

/-- The trivial whole-Spa rational covering using `globalLocData P` for
both base and single cover-piece. -/
noncomputable def globalTrivialCovering (P : PairOfDefinition A) :
    RationalCovering A :=
  letI : DecidableEq (RationalLocData A) := Classical.decEq _
  { base := globalLocData P
    covers := ({globalLocData P} : Finset (RationalLocData A))
    hsubset := by
      intro D hD
      rw [Finset.mem_singleton] at hD
      subst hD
      exact subset_rfl
    hcover := by
      intro v hv
      exact ⟨globalLocData P, Finset.mem_singleton_self _, hv⟩ }

/-- **T198: concrete cover construction** — the trivial whole-Spa
rational covering (using `globalLocData P` for both base and single
cover-piece) supplies T191/T192/T195's `h_struct` factorization
trivially.

For this covering, the unique cover-piece is `globalLocData P` with
`T = {1}, s = 1`. The factorization
`C.base.s = D.s * (σ * t * D.s ^ N)` with `σ := 1, N := 0, t := 1`
reduces to `1 = 1 * (1 * 1 * 1) = 1`, holding by `ring` in `A`. The
Tate condition `∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)` is satisfied
since `D.T = {1}` and `1 ∈ A⁺`. The f-bound
`v.vle (σ * t * D.s ^ N) C.base.s = v.vle 1 1` is reflexive.

This is a **proof-of-concept** that path (a) is feasible in narrow
cases. It is **not** directly useful as a general h_struct producer
for Tate acyclicity (which needs covers with non-trivial `D.T` and
`D.s`); see the blocker packet above for the missing
`exists_step2_refinement_carrying_factor` construction. -/
theorem h_struct_for_globalTrivialCovering
    [DecidableEq A]
    (P : PairOfDefinition A) :
    ∀ (D : RationalLocData A), D ∈ (globalTrivialCovering P).covers →
    ∀ (v : Spv A), v ∈ rationalOpen D.T D.s →
    ∀ (t : A), t ∈ D.T → v.vle t D.s → ¬ v.vle D.s 0 →
      ∃ (σ : A) (N : ℕ),
        (globalTrivialCovering P).base.s = D.s * (σ * t * D.s ^ N) ∧
        (∀ t' ∈ D.T, t' ∈ ((A⁺) : Subring A)) ∧
        v.vle (σ * t * D.s ^ N) (globalTrivialCovering P).base.s := by
  letI : DecidableEq (RationalLocData A) := Classical.decEq _
  intro D hD v _hv t ht _hvt _hvD_s
  -- Unfold globalTrivialCovering.covers = {globalLocData P}.
  have hD' : D ∈ ({globalLocData P} : Finset (RationalLocData A)) := hD
  obtain rfl : D = globalLocData P := Finset.mem_singleton.mp hD'
  -- D.T = {1}, so t = 1.
  obtain rfl : t = 1 := Finset.mem_singleton.mp ht
  -- Pick σ = 1, N = 0.
  refine ⟨1, 0, ?_, ?_, ?_⟩
  · -- (globalTrivialCovering P).base.s = 1 = 1 * (1 * 1 * 1^0) = 1.
    show ((globalTrivialCovering P).base.s : A) =
      (globalLocData P).s * (1 * 1 * (globalLocData P).s ^ 0)
    show (1 : A) = 1 * (1 * 1 * (1 : A) ^ 0)
    ring
  · -- ∀ t' ∈ {1}, t' ∈ A⁺.
    intro t' ht'
    obtain rfl : t' = 1 := Finset.mem_singleton.mp ht'
    exact (A⁺).one_mem
  · -- v.vle (1 * 1 * 1^0) (globalTrivialCovering P).base.s = v.vle 1 1.
    show v.vle (1 * 1 * (1 : A) ^ 0) (globalTrivialCovering P).base.s
    show v.vle (1 * 1 * (1 : A) ^ 0) (1 : A)
    have heq : (1 * 1 * (1 : A) ^ 0) = 1 := by ring
    rw [heq]
    rcases v.vle_total 1 1 with h' | h' <;> exact h'

end ValuationSpectrum

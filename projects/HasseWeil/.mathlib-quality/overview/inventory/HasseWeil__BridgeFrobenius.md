# Inventory: ./HasseWeil/BridgeFrobenius.lean

**File**: `HasseWeil/BridgeFrobenius.lean`
**Lines**: 176
**Imports**: `HasseWeil.FormalIsogenySeries`, `HasseWeil.Frobenius`, `HasseWeil.Hasse.PointFix`, `HasseWeil.Hasse.Separability`, `HasseWeil.LocalExpansion`
**Namespace**: `HasseWeil`
**No `set_option maxHeartbeats`**, **No `sorry`**

---

## Summary

This file is the T-IV-BRIDGE-004 bridge: it connects the formal group side (local expansion) to the differential/pullback-coefficient side for the Frobenius isogeny over a finite field. There are 8 theorems, 0 defs, 0 instances. All proofs are axiom-clean.

---

## Declaration Inventory

---

### `theorem localExpand_localParam_pow`

- **Type**: `(q : ℕ) → localExpand W ((localParam W) ^ q) = HahnSeries.single (q : ℤ) (1 : K)`
- **What**: Shows that the local expansion of `(localParam W)^q` (the local coordinate `t = −x/y` raised to the `q`-th power) equals the Hahn series `T^q`, i.e., `HahnSeries.single q 1`.
- **How**: Applies `map_pow` (ring hom), then `localExpand_localParam` (which says `localExpand(t) = HahnSeries.single 1 1`), then `HahnSeries.single_pow` and arithmetic simplification (`one_pow`, `nsmul_eq_mul`, `mul_one`).
- **Hypotheses**: `W` is an elliptic curve over a field `K`. The `Fintype K` assumption is omitted (`omit [Fintype K]`).
- **Uses from project**: `localExpand` (LocalExpansion.lean), `localParam` (LocalExpansion.lean), `localExpand_localParam` (LocalExpansion.lean)
- **Used by**: `formalIsogenySeries_frobenius` (in this file)
- **Visibility**: public
- **Lines**: 42–46, proof length 2 lines
- **Notes**: omit [Fintype K] so it works over any field.

---

### `theorem frobeniusIsog_pullback_localParam`

- **Type**: `(frobeniusIsog W).pullback (localParam W) = (localParam W) ^ Fintype.card K`
- **What**: States that the Frobenius isogeny pulls back the local parameter `t` to `t^q`, where `q = #K`.
- **How**: Direct application of `frobeniusIsog_pullback_apply` (Frobenius.lean), which records that `frobeniusIsog W` acts as the `q`-power map on any element of the function field.
- **Hypotheses**: `W` is an elliptic curve over a finite field `K`.
- **Uses from project**: `frobeniusIsog` (Frobenius.lean), `localParam` (LocalExpansion.lean), `frobeniusIsog_pullback_apply` (Frobenius.lean)
- **Used by**: `formalIsogenySeries_frobenius` (in this file)
- **Visibility**: public
- **Lines**: 49–52, proof length 1 line (term-mode)
- **Notes**: One-line term proof; pure restatement of `frobeniusIsog_pullback_apply` at `localParam`.

---

### `theorem formalIsogenySeries_frobenius` `[@simp]`

- **Type**: `formalIsogenySeries W (frobeniusIsog W) = (PowerSeries.X : PowerSeries K) ^ Fintype.card K`
- **What**: **T-IV-BRIDGE-004** (Silverman IV.4 / III.5.5): the formal isogeny series of the Frobenius is `X^q`, where `q = #K`. Equivalently, the unique `q`-th coefficient is `1` and all others are `0`.
- **How**: Proves coefficient-wise equality using `formalIsogenySeries_coeff` to reduce to a Hahn series coefficient comparison, then applies `frobeniusIsog_pullback_localParam` and `localExpand_localParam_pow` to evaluate the series at `n = q` and `n ≠ q` via `HahnSeries.coeff_single_same` and `HahnSeries.coeff_single_of_ne`.
- **Hypotheses**: `W` elliptic over finite field `K`.
- **Uses from project**: `formalIsogenySeries` (FormalIsogenySeries.lean), `formalIsogenySeries_coeff` (FormalIsogenySeries.lean), `frobeniusIsog` (Frobenius.lean), `frobeniusIsog_pullback_localParam` (this file), `localExpand_localParam_pow` (this file)
- **Used by**: `coeff_one_formalIsogenySeries_frobenius_of_card_ne_one` (this file); also consumed by `AdditionPullback/SilvermanIV14.lean` and `AdditionPullback/Differential.lean` outside this file
- **Visibility**: public (`@[simp]`)
- **Lines**: 61–70, proof length 9 lines
- **Notes**: Key bridge theorem. Tagged `@[simp]`.

---

### `theorem coeff_one_formalIsogenySeries_frobenius_of_card_ne_one`

- **Type**: `(h : Fintype.card K ≠ 1) → PowerSeries.coeff 1 (formalIsogenySeries W (frobeniusIsog W)) = 0`
- **What**: The linear coefficient (coefficient of `X^1`) of the Frobenius formal series is `0`, provided `q ≠ 1`. Since `q ≥ 2` for any non-trivial finite field, this expresses pure inseparability from the formal-series side.
- **How**: Rewrites via `formalIsogenySeries_frobenius` to reduce to `PowerSeries.coeff_X_pow`, then concludes by `if_neg` since `1 ≠ q`.
- **Hypotheses**: `Fintype.card K ≠ 1` (equivalently `q ≥ 2`).
- **Uses from project**: `formalIsogenySeries` (FormalIsogenySeries.lean), `frobeniusIsog` (Frobenius.lean), `formalIsogenySeries_frobenius` (this file)
- **Used by**: `omegaPullbackCoeff_eq_formalIsogenyLeading_frobenius` (this file); also referenced in `AdditionPullback/SilvermanIV14.lean`
- **Visibility**: public
- **Lines**: 76–80, proof length 2 lines
- **Notes**: Corollary of the main bridge theorem.

---

### `theorem omegaPullbackCoeff_frobenius`

- **Type**: `omegaPullbackCoeff W (frobeniusIsog W) = 0`
- **What**: The ω-pullback coefficient of the Frobenius isogeny is `0` (Silverman III.5.5 + II.4.4). This is the differential/separability-side statement of pure inseparability: `D(x^q) = q · x^(q-1) · D(x) = 0` in characteristic `p` with `q = p^k`.
- **How**: Uses `omegaPullbackCoeff_unique` to reduce to showing `0 · ω = π^*(ω)`. After `omegaPullbackCoeff_spec` and `frobeniusIsog_pullback_apply`, applies `Derivation.leibniz_pow` to expand `D(x^q)`, then `Nat.cast_smul_eq_nsmul` to move to a scalar action, and `FiniteField.cast_card_eq_zero` to conclude `(q : K) = 0`.
- **Hypotheses**: `W` elliptic over a finite field `K`.
- **Uses from project**: `omegaPullbackCoeff` (OmegaPullbackCoeff.lean), `frobeniusIsog` (Frobenius.lean), `omegaPullbackCoeff_unique` (OmegaPullbackCoeff.lean), `omegaPullbackCoeff_spec` (OmegaPullbackCoeff.lean), `frobeniusIsog_pullback_apply` (Frobenius.lean)
- **Used by**: `frobenius_pullbackKaehler_invariantDifferential`, `not_isSeparable_frobenius_of_witness`, `omegaPullbackCoeff_m_plus_n_frob_of_witness`, `omegaPullbackCoeff_eq_formalIsogenyLeading_frobenius` (all in this file); also heavily used by `GapSpines.lean`, `GapQfKernel.lean`, `AdditionPullback/Differential.lean`, `Hasse/OpenLemmas.lean` outside this file
- **Visibility**: public
- **Lines**: 96–108, proof length 9 lines
- **Notes**: Central result of this file; most-referenced declaration in the project from here.

---

### `theorem frobenius_pullbackKaehler_invariantDifferential`

- **Type**: `(frobeniusIsog W).pullbackKaehler (invariantDifferential W.toAffine) = 0`
- **What**: The pullback of the invariant differential `ω` under Frobenius is `0` (Silverman III.5.5). Direct corollary of `omegaPullbackCoeff_frobenius = 0` at the Kähler differential level.
- **How**: Applies `pullbackKaehler_invariantDifferential_of_coeff_witness` (Hasse/Separability.lean) with coefficient `0` and the proof that `omegaPullbackCoeff_frobenius = 0` witnesses this, then simplifies `zero_smul`.
- **Hypotheses**: `W` elliptic over a finite field `K`.
- **Uses from project**: `frobeniusIsog` (Frobenius.lean), `invariantDifferential` (mathlib/project), `omegaPullbackCoeff_frobenius` (this file), `pullbackKaehler_invariantDifferential_of_coeff_witness` (Hasse/Separability.lean)
- **Used by**: unused in file (leaf; potentially consumed by other files)
- **Visibility**: public
- **Lines**: 114–119, proof length 5 lines
- **Notes**: Leaf declaration within this file.

---

### `theorem not_isSeparable_frobenius_of_witness`

- **Type**: `(h_sep_iff : (frobeniusIsog W).IsSeparable ↔ omegaPullbackCoeff W (frobeniusIsog W) ≠ 0) → ¬ (frobeniusIsog W).IsSeparable`
- **What**: The Frobenius isogeny is not separable (Silverman III.5.5 + II.4.4), given the equivalence "separable iff ω-pullback coefficient ≠ 0" as an explicit witness. Witness-parametric design: takes T-II-4-004's criterion as input.
- **How**: Rewrites using the hypothesis `h_sep_iff`, substitutes `omegaPullbackCoeff_frobenius = 0`, and concludes that the goal `0 ≠ 0` is absurd.
- **Hypotheses**: The biconditional `IsSeparable (frobeniusIsog W) ↔ omegaPullbackCoeff W (frobeniusIsog W) ≠ 0` must be supplied.
- **Uses from project**: `frobeniusIsog` (Frobenius.lean), `omegaPullbackCoeff` (OmegaPullbackCoeff.lean), `omegaPullbackCoeff_frobenius` (this file)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 127–132, proof length 3 lines
- **Notes**: Witness-parametric style; the separability criterion is not imported directly, must be passed in. Leaf declaration within this file.

---

### `theorem omegaPullbackCoeff_m_plus_n_frob_of_witness`

- **Type**: `(β : Isogeny W.toAffine W.toAffine) → (m n : ℤ) → (h_sum_coeff : omegaPullbackCoeff W β = (m : FunctionField) * omegaPullbackCoeff W (Isogeny.id W.toAffine) + (n : FunctionField) * omegaPullbackCoeff W (frobeniusIsog W)) → omegaPullbackCoeff W β = (m : FunctionField)`
- **What**: Witness closer for the coefficient formula: given that the ω-pullback coefficient of `β` equals `m · a_id + n · a_π`, the fact that `a_id = 1` and `a_π = 0` (Frobenius) collapses this to `m`. Used to close the coefficient computation for isogenies of the form `m·id + n·π`.
- **How**: Applies `omegaPullbackCoeff_of_pullback_eq_id` (Hasse/PointFix.lean) to get `a_id = 1`, substitutes `omegaPullbackCoeff_frobenius = 0`, then simplifies `m·1 + n·0 = m` by `mul_one`, `mul_zero`, `add_zero`.
- **Hypotheses**: Additivity of `omegaPullbackCoeff` for the specific isogeny `β` with the `(m·id + n·π)` decomposition is supplied as hypothesis.
- **Uses from project**: `omegaPullbackCoeff` (OmegaPullbackCoeff.lean), `frobeniusIsog` (Frobenius.lean), `Isogeny.id`, `omegaPullbackCoeff_of_pullback_eq_id` (Hasse/PointFix.lean), `omegaPullbackCoeff_frobenius` (this file)
- **Used by**: unused in file; consumed by `AdditionPullback/Differential.lean` outside this file
- **Visibility**: public
- **Lines**: 149–159, proof length 8 lines
- **Notes**: Leaf within file; the outer-file consumer is `AdditionPullback/Differential.lean:85`.

---

### `theorem omegaPullbackCoeff_eq_formalIsogenyLeading_frobenius`

- **Type**: `(h : Fintype.card K ≠ 1) → omegaPullbackCoeff W (frobeniusIsog W) = algebraMap K W.toAffine.FunctionField (PowerSeries.coeff 1 (formalIsogenySeries W (frobeniusIsog W)))`
- **What**: **BRIDGE-001 for Frobenius**: the ω-pullback coefficient equals the leading (linear) coefficient of the formal isogeny series, embedded into the function field. Both sides equal `0` when `q ≠ 1`, proving the bridge identity for Frobenius.
- **How**: Rewrites the RHS using `coeff_one_formalIsogenySeries_frobenius_of_card_ne_one` to get `algebraMap K ... 0 = 0`, then `map_zero`, and finishes with `omegaPullbackCoeff_frobenius`.
- **Hypotheses**: `Fintype.card K ≠ 1`.
- **Uses from project**: `omegaPullbackCoeff` (OmegaPullbackCoeff.lean), `frobeniusIsog` (Frobenius.lean), `formalIsogenySeries` (FormalIsogenySeries.lean), `coeff_one_formalIsogenySeries_frobenius_of_card_ne_one` (this file), `omegaPullbackCoeff_frobenius` (this file)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 167–173, proof length 3 lines
- **Notes**: Connects formal-series (IV.4) and differential (III.5.5) perspectives. Both sides are `0`; somewhat degenerate bridge instance (non-trivially bridging the two formulations).

---

## Cross-reference summary

| Declaration | Used by (in file) |
|---|---|
| `localExpand_localParam_pow` | `formalIsogenySeries_frobenius` |
| `frobeniusIsog_pullback_localParam` | `formalIsogenySeries_frobenius` |
| `formalIsogenySeries_frobenius` | `coeff_one_formalIsogenySeries_frobenius_of_card_ne_one` |
| `coeff_one_formalIsogenySeries_frobenius_of_card_ne_one` | `omegaPullbackCoeff_eq_formalIsogenyLeading_frobenius` |
| `omegaPullbackCoeff_frobenius` | `frobenius_pullbackKaehler_invariantDifferential`, `not_isSeparable_frobenius_of_witness`, `omegaPullbackCoeff_m_plus_n_frob_of_witness`, `omegaPullbackCoeff_eq_formalIsogenyLeading_frobenius` |
| `frobenius_pullbackKaehler_invariantDifferential` | (unused in file) |
| `not_isSeparable_frobenius_of_witness` | (unused in file) |
| `omegaPullbackCoeff_m_plus_n_frob_of_witness` | (unused in file) |
| `omegaPullbackCoeff_eq_formalIsogenyLeading_frobenius` | (unused in file) |

**Key API** (`omegaPullbackCoeff_frobenius`): referenced by 4 other declarations in this file, and is also the most-consumed result from this file in the wider project.

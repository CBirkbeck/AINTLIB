# Inventory: ./HasseWeil/EC/IsogenyOrdTransport.lean

**File**: `HasseWeil/EC/IsogenyOrdTransport.lean`
**Lines**: 168
**Import**: `HasseWeil.EC.TranslateOrdInfty`
**Purpose**: Abstract DVR order-transport for a field hom (Silverman II.2.5, unramified case). Provides the "same place + e=1 ⟹ ord_P(φg) = ord_Q(g)" engine used by `[ℓ]`, `1−π`, and `rπ−s` downstream files.

---

## Declarations

### `theorem pointValuation_surjective'`

- **Type**: `(P : C.SmoothPoint) : Function.Surjective (C.pointValuation P)`
  where `C : SmoothPlaneCurve F`, `[Field F] [DecidableEq F]`
- **What**: The point valuation at a smooth point `P` is surjective onto `ℤᵐ⁰`. Fintype-free re-derivation of a version in `Hasse/L6Witnesses.lean`.
- **How**: Obtains a uniformizer `t` via `C.exists_uniformizer P`, establishes `pointValuation P t = exp(−1)` using `pointValuation_eq_exp_neg_of_ord_P_eq`, then maps any target `z ≠ 0` to `t ^ (−log z)` using `map_zpow₀` and `WithZero.exp_log`.
- **Hypotheses**: `C` is a smooth plane curve over a field `F` with `DecidableEq`.
- **Uses from project**: `C.exists_uniformizer`, `SmoothPlaneCurve.Uniformizer`, `SmoothPlaneCurve.ord_P_zero`, `pointValuation_eq_exp_neg_of_ord_P_eq` (all from `TranslateOrdInfty`).
- **Used by**: `comap_pointValuation_surjective_of_ord_eq_one` (indirectly, shares structure); directly used by callers in other files (`SamePlace.lean`, `DivisorPullback.lean`, `IsogenySurjective.lean`).
- **Visibility**: public (in `Curves.SmoothPlaneCurve` namespace)
- **Lines**: 47–62; proof length ~14 lines
- **Notes**: Marked as a "Fintype-free re-derivation" of `L6Witnesses.lean:pointValuation_surjective` to avoid `[Fintype K]` dependency. The mathlib lemma `WithZero.exp_log` is the key closure step.

---

### `theorem Valuation.isEquiv_eq_of_surjective_withZeroInt`

- **Type**:
  ```
  {E : Type*} [Field E]
  (v w : Valuation E (WithZero (Multiplicative ℤ)))
  (hv : Function.Surjective v) (hw : Function.Surjective w)
  (h : v.IsEquiv w) : v = w
  ```
- **What**: Two equivalent surjective `ℤᵐ⁰`-valued valuations on a field are actually equal. The key point is that `ℤ` has no positive divisors of 1 other than 1 itself, so the underlying order-isomorphism of value groups must be the identity.
- **How**: Picks a preimage `e` of `exp(1)` under `v`, establishes that `w(e) = (w e)^(log v x)` for all nonzero `x` using the `IsEquiv` compatibility `h.eq_one_iff_eq_one`. Determines `log(w e) = 1` by showing `log(w e) | 1` and ruling out `−1` via `w e > 1`. Concludes `v x = w x` for all `x` by `Valuation.ext`.
- **Hypotheses**: Both `v` and `w` are surjective `ℤᵐ⁰`-valued valuations; they are `Valuation.IsEquiv`.
- **Uses from project**: none (pure mathlib/stdlib: `Valuation.IsEquiv`, `WithZero.exp`, `WithZero.log`, `Int.isUnit_iff`, `isUnit_of_dvd_one`, `Valuation.ext`, `WithZero.lt_log_iff_exp_lt`).
- **Used by**: `comap_pointValuation_eq_of_isEquiv_of_ord_eq_one` (directly), also referenced externally in `IsogenySurjective.lean`.
- **Visibility**: public (in `HasseWeil` root namespace)
- **Lines**: 69–113; proof length ~44 lines
- **Notes**: **Long proof (44 lines) — flagged.** Pure valuation theory, no elliptic curve content. The `IntegralUnits`/divisibility argument at lines 98–107 is the mathematical core. Suspected to overlap with `L6Witnesses.lean:Valuation.isEquiv_iff_eq_of_surjective_withZeroInt` (the docstring says "Fintype-free re-derivation").

---

### `theorem comap_pointValuation_surjective_of_ord_eq_one`

- **Type**:
  ```
  {E : Type*} [Field E] (φ : E →+* C.FunctionField)
  {P : C.SmoothPoint} {t : E}
  (ht : C.ord_P P (φ t) = ((1 : ℤ) : WithTop ℤ)) :
  Function.Surjective ((C.pointValuation P).comap φ)
  ```
- **What**: Given a ring hom `φ : E → K(C)` and `t : E` such that `φ t` is a uniformizer at `P` (`ord_P P (φ t) = 1`), the comap valuation `(pointValuation P).comap φ` is surjective onto `ℤᵐ⁰`.
- **How**: Establishes `(pointValuation P).comap φ t = exp(−1)` via `pointValuation_eq_exp_neg_of_ord_P_eq` (from `TranslateOrdInfty`), then maps any `z ≠ 0` to `t ^ (−log z)`, using `map_zpow₀` and `WithZero.exp_log`.
- **Hypotheses**: `φ` is a ring hom into the function field of `C`; `t` maps to a uniformizer at `P` under `φ` (i.e., `ord_P P (φ t) = 1`).
- **Uses from project**: `pointValuation_eq_exp_neg_of_ord_P_eq` (from `TranslateOrdInfty`), `SmoothPlaneCurve.ord_P_zero`.
- **Used by**: `comap_pointValuation_eq_of_isEquiv_of_ord_eq_one` (directly — it supplies the surjectivity argument).
- **Visibility**: public (in `Curves.SmoothPlaneCurve` namespace)
- **Lines**: 123–138; proof length ~15 lines
- **Notes**: Structurally a copy of `pointValuation_surjective'` but for the comap valuation rather than the base valuation. The two proofs share the same `t ^ (−log z)` pattern.

---

### `theorem comap_pointValuation_eq_of_isEquiv_of_ord_eq_one`

- **Type**:
  ```
  {E : Type*} [Field E] (φ : E →+* C.FunctionField) (P : C.SmoothPoint)
  (v_Q : Valuation E (WithZero (Multiplicative ℤ))) (hv_Q : Function.Surjective v_Q)
  (h_equiv : ((C.pointValuation P).comap φ).IsEquiv v_Q)
  {t : E} (ht_ord : C.ord_P P (φ t) = ((1 : ℤ) : WithTop ℤ)) :
  (C.pointValuation P).comap φ = v_Q
  ```
- **What**: The main export of the file. Under the "same place" assumption (`comap` valuation is equivalent to `v_Q`) and the "e=1" normalization (`ord_P P (φ t) = 1` for some `t`), the comap valuation equals `v_Q` exactly. Reading off orders, this gives `ord_P (φ g) = ord_Q g` for all `g` with no ramification factor.
- **How**: One-line proof: applies `Valuation.isEquiv_eq_of_surjective_withZeroInt` with surjectivity of the comap supplied by `comap_pointValuation_surjective_of_ord_eq_one` and surjectivity of `v_Q` supplied by the hypothesis `hv_Q`.
- **Hypotheses**: `φ` is a ring hom from a field `E` to `K(C)`; `v_Q` is a surjective `ℤᵐ⁰`-valued valuation on `E`; the comap valuation is `IsEquiv` to `v_Q`; some `t` satisfies `ord_P P (φ t) = 1`.
- **Uses from project**: `Valuation.isEquiv_eq_of_surjective_withZeroInt` and `comap_pointValuation_surjective_of_ord_eq_one` (both in this file).
- **Used by**: used by callers in `SamePlace.lean` (×3), `DivisorPullback.lean` (×2), `MulByIntSamePlace.lean` (in docs and likely body), `MulByIntUnramified.lean`, `ProjOrdTransportLocal.lean` — the central API export.
- **Visibility**: public (in `Curves.SmoothPlaneCurve` namespace)
- **Lines**: 155–163; proof length ~3 lines (one-line body)
- **Notes**: This is the main export. It is the composition lemma tying the other three declarations together. Highly reused across the project.

---

## Summary statistics

| Metric | Value |
|--------|-------|
| Total declarations | 4 |
| `def`s / `noncomputable def`s | 0 |
| `lemma`/`theorem`s | 4 |
| `instance`s | 0 |
| Declarations with `sorry` | 0 |
| `set_option maxHeartbeats` | 0 |
| Long proofs (>30 lines) | 1 (`Valuation.isEquiv_eq_of_surjective_withZeroInt`, 44 lines) |

## Key API
- `comap_pointValuation_eq_of_isEquiv_of_ord_eq_one` — the main export, used by many downstream files.
- `Valuation.isEquiv_eq_of_surjective_withZeroInt` — the abstract DVR uniqueness lemma.
- `pointValuation_surjective'` — Fintype-free surjectivity used widely in other files.

## Unused declarations (within this file)
- `pointValuation_surjective'` — not called by any other declaration in this file (it is used only in other files).
- `Valuation.isEquiv_eq_of_surjective_withZeroInt` — likewise only transitively used via `comap_pointValuation_eq_of_isEquiv_of_ord_eq_one`.
- `comap_pointValuation_surjective_of_ord_eq_one` — only called by `comap_pointValuation_eq_of_isEquiv_of_ord_eq_one`.

## Notes
This is a small, clean leaf file (168 lines, 4 theorems, 0 sorries, no `maxHeartbeats`). It isolates abstract DVR machinery for reuse. `Valuation.isEquiv_eq_of_surjective_withZeroInt` is a Fintype-free re-derivation of a result in `Hasse/L6Witnesses.lean`, and `pointValuation_surjective'` similarly. There is some duplication suspicion with those `L6Witnesses` counterparts, but the intent is deliberate decoupling.

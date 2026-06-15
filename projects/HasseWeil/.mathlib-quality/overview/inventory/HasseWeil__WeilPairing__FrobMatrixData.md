# Inventory: ./HasseWeil/WeilPairing/FrobMatrixData.lean

**File purpose**: Final geometric reduction step for the Hasse bound. Supplies the per-ℓ Frobenius-matrix determinant data `hres` needed by `hasse_bound_via_weil_pairing` (HasseAssembly.lean) by base-changing `E/K` to the algebraic closure `K̄ = AlgebraicClosure K` and invoking the abstract `DetDeg.frob_det_residual_of_weil_scaling` machinery.

**Imports**: `HasseWeil.WeilPairing.HasseAssembly`, `HasseWeil.IsogenyBaseChange`

**Total declarations**: 14 (7 `def`/`noncomputable def`, 1 `local instance`, 6 `theorem`)

---

## Declarations

### `noncomputable def frobeniusHomBaseChange`
- **Type**: `(p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)] (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [ExpChar L p] [(W.baseChange L).toAffine.IsElliptic] : (W.baseChange L).toAffine.Point →+ (W.baseChange L).toAffine.Point`
- **What**: The q-power Frobenius `AddMonoidHom` on the L-points of the base-changed curve `E_L`, defined as the underlying point map of `Isogeny.frobeniusIsog_baseChange_charP_pow`.
- **How**: One-liner: `(Isogeny.frobeniusIsog_baseChange_charP_pow p r W L).toAddMonoidHom`.
- **Hypotheses**: `K` finite field of characteristic `p`, `#K = p^r`, `L/K` an extension with `ExpChar L p`, and the base-changed curve `E_L` is elliptic.
- **Uses from project**: `Isogeny.frobeniusIsog_baseChange_charP_pow` (IsogenyBaseChange.lean)
- **Used by**: `FrobeniusScaling` (L128), `OneSubFrobeniusScaling` (L144), `PencilScaling` (L160), `PencilScalingCoprime` (L180), `frob_det_residual_baseChange` (L256)
- **Visibility**: public
- **Lines**: 99–104, proof length: 1 line
- **Notes**: Noncomputable due to isogeny construction.

---

### `def FrobeniusScaling`
- **Type**: `(p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)] (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p] [(W.baseChange L).toAffine.IsElliptic] : Prop`
- **What**: The proposition (Leaf 1) that the Weil pairing satisfies `e_ℓ(πbar S, πbar T) = e_ℓ(S, T)^{#K}` for all primes `ℓ ≠ p`, where `πbar = frobeniusHomBaseChange`. This is Silverman III.8.1d (Galois/Frobenius equivariance), the only genuinely new content among the three leaves.
- **How**: Pure definition (Prop-valued); body is a universal statement using `WeilScales`.
- **Hypotheses**: `L` algebraically closed with characteristic `p`, base-changed curve is elliptic.
- **Uses from project**: `frobeniusHomBaseChange` (this file), `WeilScales` (from HasseAssembly/DetDeg import chain)
- **Used by**: `FrobBaseChangeScalings` (L193), `FrobBaseChangeScalingsCoprime` (L205)
- **Visibility**: public
- **Lines**: 122–129, proof length: definition only

---

### `def OneSubFrobeniusScaling`
- **Type**: `(p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)] (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p] [(W.baseChange L).toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) : Prop`
- **What**: The proposition (Leaf 2) that the Weil pairing satisfies `e_ℓ((id − πbar) S, (id − πbar) T) = e_ℓ(S, T)^{deg(1−π)}` for all primes `ℓ ≠ p`, where the exponent is `(isogOneSub_negFrobenius W hq).degree`. This is Silverman III.8.6.1 for the separable `1 − π` isogeny.
- **How**: Pure definition; exponent uses the K-level degree `(isogOneSub_negFrobenius W hq).degree` to avoid base-change degree preservation.
- **Hypotheses**: Same as `FrobeniusScaling` plus `2 ≤ #K` (needed for `isogOneSub_negFrobenius`).
- **Uses from project**: `frobeniusHomBaseChange` (this file), `isogOneSub_negFrobenius` (HasseAssembly), `WeilScales`
- **Used by**: `FrobBaseChangeScalings` (L193), `FrobBaseChangeScalingsCoprime` (L205)
- **Visibility**: public
- **Lines**: 136–146, proof length: definition only

---

### `def PencilScaling`
- **Type**: `(p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)] (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p] [(W.baseChange L).toAffine.IsElliptic] (deg : ℤ → ℤ → ℤ) : Prop`
- **What**: The proposition (Leaf 3, full form) that the Weil pairing satisfies `e_ℓ((r'·πbar − s'·id) S, ...) = e_ℓ(S, T)^{(deg r' s').toNat}` for all `p ∤ s'` and all primes `ℓ ≠ p`. This covers the separable pencil `rπ − s` with only the `p ∤ s'` condition.
- **How**: Pure definition; the abstractly supplied `deg` function provides the exponent.
- **Hypotheses**: Same as `FrobeniusScaling` plus abstract degree function `deg : ℤ → ℤ → ℤ` and condition `p ∤ s'`.
- **Uses from project**: `frobeniusHomBaseChange` (this file), `WeilScales`
- **Used by**: `FrobBaseChangeScalings` (L193)
- **Visibility**: public
- **Lines**: 152–163, proof length: definition only

---

### `def PencilScalingCoprime`
- **Type**: `(p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)] (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p] [(W.baseChange L).toAffine.IsElliptic] (deg : ℤ → ℤ → ℤ) : Prop`
- **What**: The proposition (Leaf 3, coprime-BOTH form, reviewer round-23 Route B) that the Weil pairing scaling holds for the pencil `rπ − s` restricted to the locus `p ∤ r' ∧ p ∤ s'`. Strictly weaker than `PencilScaling` (adds `¬ p ∣ r'`), but avoids the `p ∣ r'` sorry that `PencilScaling` cannot discharge.
- **How**: Pure definition; identical in structure to `PencilScaling` but adds `¬ ((ringChar K : ℤ)) ∣ r'` as a hypothesis.
- **Hypotheses**: Same as `PencilScaling` plus `p ∤ r'`.
- **Uses from project**: `frobeniusHomBaseChange` (this file), `WeilScales`
- **Used by**: `FrobBaseChangeScalingsCoprime` (L205)
- **Visibility**: public
- **Lines**: 171–183, proof length: definition only
- **Notes**: Designed specifically to bypass the `p ∣ r'` sorry isolated in `PencilComapWitnesses.lean`.

---

### `def FrobBaseChangeScalings`
- **Type**: `(p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)] (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p] [(W.baseChange L).toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) (deg : ℤ → ℤ → ℤ) : Prop`
- **What**: The conjunction of all three per-isogeny scaling leaves `FrobeniusScaling ∧ OneSubFrobeniusScaling ∧ PencilScaling`. This is the single bundled geometric residual consumed by `hasse_bound_unconditional_of_baseChange_scalings`.
- **How**: Pure conjunction; body is `FrobeniusScaling W p r L ∧ OneSubFrobeniusScaling W p r L hq ∧ PencilScaling W p r L deg`.
- **Hypotheses**: All hypotheses of the three component leaves combined.
- **Uses from project**: `FrobeniusScaling`, `OneSubFrobeniusScaling`, `PencilScaling` (this file)
- **Used by**: `hres_of_baseChange_scalings` (L290), `hasse_bound_unconditional_of_baseChange_scalings` (L345)
- **Visibility**: public
- **Lines**: 188–194, proof length: definition only

---

### `def FrobBaseChangeScalingsCoprime`
- **Type**: `(p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)] (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p] [(W.baseChange L).toAffine.IsElliptic] (hq : 2 ≤ Fintype.card K) (deg : ℤ → ℤ → ℤ) : Prop`
- **What**: The conjunction `FrobeniusScaling ∧ OneSubFrobeniusScaling ∧ PencilScalingCoprime`. The axiom-clean variant of `FrobBaseChangeScalings` consumed by the capstone `hasse_bound_unconditional_of_baseChange_scalings_coprime`.
- **How**: Same conjunction structure as `FrobBaseChangeScalings` but with the coprime-BOTH pencil leaf.
- **Hypotheses**: Same as `FrobBaseChangeScalings` but uses `PencilScalingCoprime` instead of `PencilScaling`.
- **Uses from project**: `FrobeniusScaling`, `OneSubFrobeniusScaling`, `PencilScalingCoprime` (this file)
- **Used by**: `hres_of_baseChange_scalings_coprime` (L318), `hasse_bound_unconditional_of_baseChange_scalings_coprime` (L375)
- **Visibility**: public
- **Lines**: 200–206, proof length: definition only

---

### `theorem card_add_one_sub_isogTrace_eq_degree`
- **Type**: `(hq : 2 ≤ Fintype.card K) : (Fintype.card K + 1 - isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) : ℤ) = ((isogOneSub_negFrobenius W hq).degree : ℤ)`
- **What**: Pure arithmetic trace identity: `#K + 1 − t = deg(1 − π)` as integers, where `t = isogTrace`. This discharges the `d1` degree identification in `frob_det_residual_of_weil_scaling` without any base-change degree-preservation lemma.
- **How**: Unfolds `isogTrace` definition and rewrites with `frobeniusIsog_degree` (which gives `deg π = #K`), then closes by `ring`.
- **Hypotheses**: `2 ≤ Fintype.card K`. The `[Fintype W.toAffine.Point]` instance is omitted via `omit`.
- **Uses from project**: `isogTrace`, `frobeniusIsog`, `isogOneSub_negFrobenius` (HasseAssembly), `frobeniusIsog_degree` (Frobenius/FrobeniusIsogeny files)
- **Used by**: `frob_det_residual_baseChange` (L262)
- **Visibility**: public
- **Lines**: 213–220, proof length: 3 lines

---

### `theorem frob_det_residual_baseChange`
- **Type**: Takes `(p r : ℕ) [...]` base-change hypotheses, `(hq : 2 ≤ Fintype.card K)`, `(deg : ℤ → ℤ → ℤ)`, `(hdeg_nonneg : ∀ r s, 0 ≤ deg r s)`, `(r' s' : ℤ)`, `(ℓ : ℕ)`, `(hℓp : ℓ.Prime)`, `(hℓF : (ℓ : L) ≠ 0)`, and the conjunction `hsc` of the three `WeilScales`, and produces `∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ), M.det = ... ∧ (1−M).det = ... ∧ (r'•M − s'•1).det = ...`
- **What**: For a single `(r', s', ℓ)`, invokes the abstract `frob_det_residual_of_weil_scaling` to produce the Frobenius matrix `M` with the three determinant identities, after discharging the degree-cast `(deg r' s').toNat = deg r' s'` using `hdeg_nonneg` and using `card_add_one_sub_isogTrace_eq_degree` for the trace identity.
- **How**: Destructs `hsc`, proves `hDd : ((deg r' s').toNat : ℤ) = deg r' s'` via `Int.toNat_of_nonneg`, then applies `frob_det_residual_of_weil_scaling` directly with `card_add_one_sub_isogTrace_eq_degree W hq` as the `d1` identification.
- **Hypotheses**: Full base-change setup, `ℓ` prime, `(ℓ : L) ≠ 0`, the three `WeilScales` as a conjunction.
- **Uses from project**: `frob_det_residual_of_weil_scaling` (DetDeg, via HasseAssembly), `frobeniusHomBaseChange`, `isogOneSub_negFrobenius`, `isogTrace`, `frobeniusIsog`, `card_add_one_sub_isogTrace_eq_degree` (this file)
- **Used by**: `hres_of_baseChange_scalings` (L302), `hres_of_baseChange_scalings_coprime` (L331)
- **Visibility**: public
- **Lines**: 229–264, proof length: 13 lines

---

### `theorem natCast_ne_zero_of_prime_ne_ringChar`
- **Type**: `{p : ℕ} (hp : p.Prime) (L : Type*) [Field L] [CharP L p] (ℓ : ℕ) (hℓp : ℓ.Prime) (hℓne : ℓ ≠ p) : (ℓ : L) ≠ 0`
- **What**: If `L` has characteristic `p` and `ℓ` is a prime different from `p`, then `(ℓ : L) ≠ 0`. Used to discharge the `(ℓ : K̄) ≠ 0` side-condition from `ℓ ≠ ringChar K`.
- **How**: Rewrites using `CharP.cast_eq_zero_iff L p ℓ`, then shows divisibility `p ∣ ℓ` forces `p = ℓ` (since both are prime) via `Nat.prime_dvd_prime_iff_eq`, contradicting `hℓne`.
- **Hypotheses**: `p` prime, `L` a field of characteristic `p`, `ℓ` a prime different from `p`.
- **Uses from project**: None (only mathlib lemmas)
- **Used by**: `hres_of_baseChange_scalings` (L301), `hres_of_baseChange_scalings_coprime` (L330)
- **Visibility**: public
- **Lines**: 270–275, proof length: 4 lines

---

### `theorem hres_of_baseChange_scalings`
- **Type**: Takes full base-change setup, `(hq : 2 ≤ Fintype.card K)`, `(deg : ℤ → ℤ → ℤ)`, `(hdeg_nonneg : ∀ r s, 0 ≤ deg r s)`, `(hpchar : ringChar K = p)`, `(hscale : FrobBaseChangeScalings W p r L hq deg)`, and concludes the `hres` existential universally quantified over `r', s', ℓ`.
- **What**: Assembles `frob_det_residual_baseChange` across all `(r', s', ℓ)` with `p ∤ s'` and `ℓ ≠ p`, yielding the exact `hres` hypothesis of `hasse_bound_via_weil_pairing`, from the single geometric leaf `FrobBaseChangeScalings`.
- **How**: Destructs `FrobBaseChangeScalings` into its three components, derives `CharP L p` by injectivity of `algebraMap K L`, uses `natCast_ne_zero_of_prime_ne_ringChar` for `(ℓ : L) ≠ 0`, then calls `frob_det_residual_baseChange` with the three individual `WeilScales` reconstructed by applying each leaf hypothesis.
- **Hypotheses**: Full base-change, `2 ≤ #K`, non-negative degree function, `ringChar K = p`, and `FrobBaseChangeScalings`.
- **Uses from project**: `FrobBaseChangeScalings` (this file), `frob_det_residual_baseChange` (this file), `natCast_ne_zero_of_prime_ne_ringChar` (this file)
- **Used by**: `hasse_bound_unconditional_of_baseChange_scalings` (L361)
- **Visibility**: public
- **Lines**: 283–303, proof length: 20 lines

---

### `theorem hres_of_baseChange_scalings_coprime`
- **Type**: Identical shape to `hres_of_baseChange_scalings` except the quantifier includes `¬ ((ringChar K : ℤ)) ∣ r'` as an extra hypothesis and consumes `FrobBaseChangeScalingsCoprime` instead of `FrobBaseChangeScalings`.
- **What**: Mirror of `hres_of_baseChange_scalings` for the coprime-BOTH leaf: assembles `frob_det_residual_baseChange` across `(r', s', ℓ)` with `p ∤ r' ∧ p ∤ s'`, yielding the coprime-BOTH `hres` for `hasse_bound_via_weil_pairing_both`.
- **How**: Same proof structure as `hres_of_baseChange_scalings`; the only difference is `hPencil r' s' hpr hps` (both coprime conditions) vs `hPencil r' s' hps` (only `p ∤ s'`).
- **Hypotheses**: Same as `hres_of_baseChange_scalings` with `FrobBaseChangeScalingsCoprime` and the extra `¬ p ∣ r'` quantifier condition.
- **Uses from project**: `FrobBaseChangeScalingsCoprime` (this file), `frob_det_residual_baseChange` (this file), `natCast_ne_zero_of_prime_ne_ringChar` (this file)
- **Used by**: `hasse_bound_unconditional_of_baseChange_scalings_coprime` (L390)
- **Visibility**: public
- **Lines**: 311–332, proof length: 21 lines

---

### `noncomputable local instance : DecidableEq (AlgebraicClosure K)`
- **Type**: `DecidableEq (AlgebraicClosure K)`
- **What**: Derives `DecidableEq` on the algebraic closure via `Classical.decEq`. Needed for the two capstone theorems which mention `AlgebraicClosure K` explicitly.
- **How**: `Classical.decEq _`.
- **Hypotheses**: None beyond `K : Type*` in context.
- **Uses from project**: None
- **Used by**: `hasse_bound_unconditional_of_baseChange_scalings`, `hasse_bound_unconditional_of_baseChange_scalings_coprime`
- **Visibility**: local (scoped to file via `local`)
- **Lines**: 340, proof length: 1 line

---

### `theorem hasse_bound_unconditional_of_baseChange_scalings`
- **Type**: `(hq : 2 ≤ Fintype.card K) (deg : ℤ → ℤ → ℤ) (hdeg_nonneg : ∀ r s, 0 ≤ deg r s) (hscale : ∀ (p r : ℕ) (_ : Fact p.Prime) (_ : CharP K p) (_ : Fact (Fintype.card K = p ^ r)), FrobBaseChangeScalings W p r (AlgebraicClosure K) hq deg) : |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤ 2 * Real.sqrt (Fintype.card K : ℝ)`
- **What**: The unconditional Hasse bound `|#E(𝔽_q) − q − 1| ≤ 2√q`, assembled from the single geometric leaf `FrobBaseChangeScalings` over `K̄ = AlgebraicClosure K`, via `hres_of_baseChange_scalings` and the shipped `hasse_bound_via_weil_pairing`.
- **How**: Extracts `p`, `n`, characteristic and cardinality data from `FiniteField.card' K`; derives `ExpChar (AlgebraicClosure K) p` by first showing `CharP (AlgebraicClosure K) p` via injectivity of `algebraMap`; uses `inferInstance` for `IsElliptic`; then calls `hasse_bound_via_weil_pairing` with `hres_of_baseChange_scalings`.
- **Hypotheses**: `2 ≤ #K`, non-negative degree function `deg`, and `FrobBaseChangeScalings` for every prime-power decomposition of `#K`.
- **Uses from project**: `FrobBaseChangeScalings` (this file), `hres_of_baseChange_scalings` (this file), `hasse_bound_via_weil_pairing` (HasseAssembly)
- **Used by**: `HasseBound.lean` (external: `hasse_bound_unconditional_of_baseChange_scalings_coprime` is used there; this full-form version may also be referenced)
- **Visibility**: public
- **Lines**: 342–363, proof length: 21 lines

---

### `theorem hasse_bound_unconditional_of_baseChange_scalings_coprime`
- **Type**: Same shape as `hasse_bound_unconditional_of_baseChange_scalings` but with `FrobBaseChangeScalingsCoprime` in place of `FrobBaseChangeScalings`.
- **What**: The axiom-clean capstone: `|#E(𝔽_q) − q − 1| ≤ 2√q` from the coprime-BOTH scaling leaf, via `hresse_bound_via_weil_pairing_both`. The pencil scaling is only requested on `p ∤ r' ∧ p ∤ s'`, so the inseparable `p ∣ r'` sorry is never triggered.
- **How**: Identical instance bookkeeping to `hasse_bound_unconditional_of_baseChange_scalings`; uses `hasse_bound_via_weil_pairing_both` and `hres_of_baseChange_scalings_coprime`.
- **Hypotheses**: Same as `hasse_bound_unconditional_of_baseChange_scalings` but with `FrobBaseChangeScalingsCoprime`.
- **Uses from project**: `FrobBaseChangeScalingsCoprime` (this file), `hres_of_baseChange_scalings_coprime` (this file), `hasse_bound_via_weil_pairing_both` (HasseAssembly)
- **Used by**: `HasseBound.lean` (directly invoked at L74)
- **Visibility**: public
- **Lines**: 372–392, proof length: 20 lines

---

## Cross-reference summary

| Declaration | Used by (within file) |
|---|---|
| `frobeniusHomBaseChange` | `FrobeniusScaling`, `OneSubFrobeniusScaling`, `PencilScaling`, `PencilScalingCoprime`, `frob_det_residual_baseChange` |
| `FrobeniusScaling` | `FrobBaseChangeScalings`, `FrobBaseChangeScalingsCoprime` |
| `OneSubFrobeniusScaling` | `FrobBaseChangeScalings`, `FrobBaseChangeScalingsCoprime` |
| `PencilScaling` | `FrobBaseChangeScalings` |
| `PencilScalingCoprime` | `FrobBaseChangeScalingsCoprime` |
| `FrobBaseChangeScalings` | `hres_of_baseChange_scalings`, `hasse_bound_unconditional_of_baseChange_scalings` |
| `FrobBaseChangeScalingsCoprime` | `hres_of_baseChange_scalings_coprime`, `hasse_bound_unconditional_of_baseChange_scalings_coprime` |
| `card_add_one_sub_isogTrace_eq_degree` | `frob_det_residual_baseChange` |
| `frob_det_residual_baseChange` | `hres_of_baseChange_scalings`, `hres_of_baseChange_scalings_coprime` |
| `natCast_ne_zero_of_prime_ne_ringChar` | `hres_of_baseChange_scalings`, `hres_of_baseChange_scalings_coprime` |
| `hres_of_baseChange_scalings` | `hasse_bound_unconditional_of_baseChange_scalings` |
| `hres_of_baseChange_scalings_coprime` | `hasse_bound_unconditional_of_baseChange_scalings_coprime` |
| `(local instance DecidableEq)` | both capstone theorems |

**Key API** (used by 3+ declarations in file): `frobeniusHomBaseChange` (used by 5 declarations)

**Unused in file**: `PencilScaling` is used only by `FrobBaseChangeScalings`, but `FrobBaseChangeScalings` itself is superseded in practice by the coprime variant — however, since `FrobBaseChangeScalings` is still referenced within the file by `hasse_bound_unconditional_of_baseChange_scalings`, `PencilScaling` is not truly dead. No declarations are completely unreferenced within the file.

## Notes on file structure

- No `sorry` anywhere in the file (the word appears only in comments).
- No `set_option maxHeartbeats` in the file.
- Longest proofs: `hres_of_baseChange_scalings` (~20 lines), `hres_of_baseChange_scalings_coprime` (~21 lines), `hasse_bound_unconditional_of_baseChange_scalings` (~21 lines), `hasse_bound_unconditional_of_baseChange_scalings_coprime` (~20 lines). None exceed 30 lines.
- The file is a thin wiring/reduction layer: no sorry, no heavy tactics, all proofs are short.
- The parallel `...scalings` / `...scalings_coprime` pairs are structural duplication (coprime-BOTH route-B design).
- `set_option linter.style.longLine false` suppresses long-line style lint only.

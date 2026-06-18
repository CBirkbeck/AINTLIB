# Inventory: ./HasseWeil/WeilPairing/FrobeniusGalois.lean

**File path**: `HasseWeil/WeilPairing/FrobeniusGalois.lean`
**Total lines**: 200
**Imports**: `HasseWeil.WeilPairing.PairingAdjoint`, `HasseWeil.WeilPairing.FrobMatrixData`

---

## Purpose

Discharges the Weil-pairing Frobenius scaling leaf (`FrobeniusScaling`, Silverman III.8.1d / III.8.6.1) without an `Isogeny.CoordHom`, via a CoordHom-free core theorem and a bundled geometric witness predicate.

---

## Declaration Inventory

---

### `theorem weilPairing_scaling_core`

- **Type**:
  ```
  weilPairing_scaling_core (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
      (φ : Isogeny W.toAffine W.toAffine) (d : ℕ)
      (S T U : W.toAffine.Point) (hS hT hφS hφT hU : ...)
      (hcomm : translation covariance at φT)
      (hfact : φ^*(g_{φT}) = c · g_U · [ℓ]^* k)
      (hdual : U = d • T) :
    e_ℓ(φS, φT) = e_ℓ(S, T) ^ d
  ```
- **What**: For any isogeny `φ` on `E` (over an algebraically closed field `F`) with ℓ-torsion inputs `S`, `T`, `φS`, `φT` and a dual point `U = d • T`, this proves the Weil-pairing scaling `e_ℓ(φS, φT) = e_ℓ(S, T)^d`. It is the CoordHom-free version of Silverman III.8.6.1 and, specialised to `φ = π`, gives III.8.1d.
- **How**: Three steps: (1) apply `weilPairing_adjoint_core` to get `e_ℓ(φS, φT) = e_ℓ(S, U)`; (2) use `weilPairing_congr_right` with `hdual : U = d • T`; (3) apply `weilPairing_nsmul_right` to collapse `e_ℓ(S, d • T) = e_ℓ(S, T)^d`. The torsion condition `ℓ • (d • T) = 0` is supplied by `smul_nsmul_eq_zero_right`.
- **Hypotheses**: `F` algebraically closed; `W/F` an elliptic curve; `IsIntegrallyClosed` on the coordinate ring; `φ` an endoisogeny; `S, T, U, φS, φT` all ℓ-torsion; translation covariance `hcomm` and divisor factorisation `hfact` witnesses; dual relation `U = d • T`.
- **Uses from project**: `weilPairing_adjoint_core` (PairingAdjoint), `weilPairing_congr_right` (PairingAdjoint), `weilPairing_nsmul_right` (PairingAdjoint), `smul_nsmul_eq_zero_right` (PairingAdjoint), `weilFunction`, `translateAlgEquivOfPoint`, `mulByInt`, `weilPairing`.
- **Used by**: `frobeniusScaling_of_witnesses` (in this file).
- **Visibility**: public
- **Lines**: 83–108; proof length: ~8 lines (lines 100–107).
- **Notes**: No `sorry`, no `maxHeartbeats` override. Proof is short and clean.

---

### `def FrobeniusScalingWitnesses`

- **Type**:
  ```
  FrobeniusScalingWitnesses (p r : ℕ) [Fact p.Prime] [CharP K p]
      [Fact (Fintype.card K = p^r)]
      (L : Type*) [Field L] [...IsAlgClosed L] [ExpChar L p] [...] : Prop :=
  ∀ ℓ hℓ S T hS hT hφT,
    ∃ U hU c k,
      (translation covariance for Frobenius^*g_{φT} at S) ∧
      (divisor factorisation φ^*g_{φT} = c · g_U · [ℓ]^*k) ∧
      U = (#K) • T
  ```
- **What**: A `Prop`-valued predicate bundling, per ℓ-torsion pair `(S, T)` on `E_{K̄}`, the two geometric witnesses that `weilPairing_scaling_core` needs for the base-changed Frobenius `φ = frobeniusIsog_baseChange_charP_pow`: the translation covariance `hcomm` (Frobenius commutes with translation at the function-field level) and the divisor factorisation `hfact` with dual point `U = q • T`.
- **How**: Pure `Prop` definition (existential) — no proof content. Mirrors the project's witness-parametric style (`ProjOrdTransport`, `Naturality`, `PicDualDivisorClass`).
- **Hypotheses**: `K` a finite field of characteristic `p` with `#K = p^r`; `L/K` algebraically closed with `ExpChar L p`; `(W.baseChange L)` elliptic; integrally closed coordinate ring.
- **Uses from project**: `Isogeny.frobeniusIsog_baseChange_charP_pow` (FrobMatrixData/FrobeniusIsogeny), `translateAlgEquivOfPoint`, `weilFunction`, `mulByInt`, `weilPairing`.
- **Used by**: `frobeniusScaling_of_witnesses` (in this file).
- **Visibility**: public
- **Lines**: 139–164; definition (no proof body beyond `:= ∀ ...`).
- **Notes**: No `sorry`. This is the single geometric residual leaf for the Frobenius scaling; it is referenced in a comment in `OneSubScaling.lean` and `MapTranslateGenericAdditive.lean` as a project pattern.

---

### `theorem frobeniusScaling_of_witnesses`

- **Type**:
  ```
  frobeniusScaling_of_witnesses (p r : ℕ) [...] (L : Type*) [...]
      (hwit : FrobeniusScalingWitnesses W p r L) :
    FrobeniusScaling W p r L
  ```
- **What**: Proves the leaf `FrobeniusScaling W p r L` (i.e., `e_ℓ(π̄ S, π̄ T) = e_ℓ(S, T)^{#K}` for all ℓ-torsion `S`, `T` on `E_{K̄}`, for all primes `ℓ ≠ char K`) from the single bundled geometric witness `FrobeniusScalingWitnesses`. This is Silverman III.8.1d discharged CoordHom-free.
- **How**: Unfolds `FrobeniusScaling` to `WeilScales`; unpacks torsion conditions for `S`, `T` and their Frobenius images using `zsmul_eq_zero_of_mem_torsion` and `map_zsmul`; obtains the witnesses `(U, hU, c, k, hcomm, hfact, hdual)` from `hwit`; then applies `weilPairing_scaling_core` with `d = #K`.
- **Hypotheses**: Same finite field / base-change setup as `FrobeniusScalingWitnesses`; the geometric witness predicate `hwit`.
- **Uses from project**: `FrobeniusScalingWitnesses` (this file), `weilPairing_scaling_core` (this file), `zsmul_eq_zero_of_mem_torsion` (DetDeg), `Isogeny.frobeniusIsog_baseChange_charP_pow` (FrobMatrixData/FrobeniusIsogeny), `FrobeniusScaling` (FrobMatrixData).
- **Used by**: Unused within this file (leaf theorem consumed by FrobMatrixData assembly, referenced externally as the discharged leaf).
- **Visibility**: public
- **Lines**: 172–196; proof length: ~17 lines (lines 179–196).
- **Notes**: No `sorry`, no `maxHeartbeats` override. Proof is straightforward bookkeeping + delegation to `weilPairing_scaling_core`.

---

## Summary statistics

| Kind | Count |
|---|---|
| `theorem` | 2 |
| `def` | 1 |
| `instance` | 0 |
| **Total declarations** | **3** |

## Key API

- `weilPairing_scaling_core`: used by `frobeniusScaling_of_witnesses` (and docstring references), making it the central export of the `Core` section.
- `FrobeniusScalingWitnesses`: used as the hypothesis of `frobeniusScaling_of_witnesses`.

## Unused declarations (within this file)

- `frobeniusScaling_of_witnesses` — not called by any other declaration in this file; it is the terminal export.
- `FrobeniusScalingWitnesses` — only appears as a hypothesis type in `frobeniusScaling_of_witnesses`, so not "called" as a function within the file beyond that.
- `weilPairing_scaling_core` — only called once, by `frobeniusScaling_of_witnesses`.

(All three are leaf/export declarations; "unused in file" means no internal callers beyond the direct caller chain.)

## Notes on special options

- `set_option linter.unusedSectionVars false` (line 55) — no justifying comment.
- `set_option linter.unusedDecidableInType false` (line 56) — no justifying comment.
- `set_option linter.style.longLine false` (line 57) — no justifying comment; likely needed for the very long `FrobeniusScalingWitnesses` statement.
- No `set_option maxHeartbeats` overrides.

## Sorries

None.

## Long proofs (> 30 lines)

None — the longest proof is `frobeniusScaling_of_witnesses` at ~17 lines.

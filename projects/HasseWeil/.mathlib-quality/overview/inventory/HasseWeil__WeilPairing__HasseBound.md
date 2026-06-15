# Inventory: ./HasseWeil/WeilPairing/HasseBound.lean

**File**: `HasseWeil/WeilPairing/HasseBound.lean`  
**Lines**: 1–88  
**Module**: `HasseWeil.WeilPairing`  
**Imports**: `PencilComapWitnesses`, `FrobeniusGaloisScaling`, `OneSubProjOrdTransport`, `FrobMatrixData`

**Summary**: Capstone file. Assembles the unconditional Hasse bound `|#E(𝔽_q)−q−1|≤2√q` from the three per-isogeny Weil-pairing scalings (Frobenius, 1−π, rπ−s) plus the matrix-data reduction theorem. The file contains exactly **two declarations**: one anonymous local instance and one public theorem.

---

## Declarations

---

### `noncomputable local instance` (anonymous, line 49)

- **Type**: `DecidableEq (AlgebraicClosure K)`
- **What**: Provides a `DecidableEq` instance on the algebraic closure of `K` via `Classical.decEq`, needed so that downstream tactic calls into `AlgebraicClosure K` do not stall on instance synthesis.
- **How**: Direct term `Classical.decEq _`.
- **Hypotheses**: `K` a field (from section variable).
- **Uses from project**: none
- **Used by**: `hasse_bound_unconditional` (implicitly, via typeclass lookup)
- **Visibility**: local (anonymous)
- **Lines**: 49, proof length: 1 line
- **Notes**: Anonymous instance; not separately nameable.

---

### `theorem hasse_bound_unconditional`

- **Type**:
  ```
  hasse_bound_unconditional (hq : 2 ≤ Fintype.card K) :
      |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤
        2 * Real.sqrt (Fintype.card K : ℝ)
  ```
- **What**: The unconditional Hasse bound for an elliptic curve `E/𝔽_q`: the number of rational points satisfies `|#E(𝔽_q) − q − 1| ≤ 2√q`, with no geometric hypotheses beyond `2 ≤ #K` (which ensures a non-trivial prime characteristic). This is Silverman V.1.1.
- **How**: Calls the matrix-data driver `hasse_bound_unconditional_of_baseChange_scalings_coprime` (from `FrobMatrixData.lean`), supplying:
  1. The degree function `deg₀ := pencilKerCard W p₀ n₀ (pencilJunkPullback W)` (frozen via `set` to prevent `whnf` reduction of the heavy `Nat.card (…ker)` term during unification).
  2. Non-negativity `pencilKerCard_nonneg` (rewritten via `hdeg₀ ▸`).
  3. The `FrobBaseChangeScalingsCoprime` bundle, discharged for arbitrary `(p, r)` by:
     - Forcing `p = p₀` via `CharP.eq` (uniqueness of characteristic).
     - Forcing `r = n₀` via `Nat.pow_right_injective` on `#K = p^r = p^n₀`.
     - Supplying `frobeniusScaling_holds`, `oneSubFrobeniusScaling_holds`, and `pencilScaling_holds_coprime`.
- **Hypotheses**: `K` finite field, `W` an elliptic curve over `K` with `Fintype W.toAffine.Point`, and `2 ≤ Fintype.card K` (ensures `p.two_le` for `Nat.pow_right_injective`).
- **Uses from project**:
  - `hasse_bound_unconditional_of_baseChange_scalings_coprime` (`FrobMatrixData.lean`)
  - `pencilKerCard` (`PencilComapScaling.lean`)
  - `pencilKerCard_nonneg` (`PencilComapScaling.lean`)
  - `pencilJunkPullback` (`PencilComapWitnesses.lean`)
  - `frobeniusScaling_holds` (`FrobeniusGaloisScaling.lean`)
  - `oneSubFrobeniusScaling_holds` (`OneSubProjOrdTransport.lean`)
  - `pencilScaling_holds_coprime` (`PencilComapWitnesses.lean`)
- **Used by**: unused in file (capstone; consumed externally or not at all within this repo)
- **Visibility**: public
- **Lines**: 63–86, proof length: ~22 lines
- **Notes**: `set_option maxHeartbeats 2000000` is set file-globally at line 51 with **NO justifying comment** (the docstring mentions the `whnf`-freeze for `pencilKerCard` via `set`, but the heartbeat value itself is uncommented). No `sorry`. The proof is under 30 lines.

---

## File-level options

| Location | Option | Value | Comment present? |
|---|---|---|---|
| Line 51 | `maxHeartbeats` | 2000000 | NO-COMMENT |
| Line 43 | `linter.unusedSectionVars` | false | — |
| Line 44 | `linter.style.longLine` | false | — |

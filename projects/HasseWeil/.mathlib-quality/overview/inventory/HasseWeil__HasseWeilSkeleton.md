# Inventory: ./HasseWeil/HasseWeilSkeleton.lean

**File**: `HasseWeil/HasseWeilSkeleton.lean`
**Total lines**: 36
**Imports**: `HasseWeil.GapSpines`, `HasseWeil.Hasse.QuadraticForm`
**Namespace**: `HasseWeil`
**Opens**: `WeierstrassCurve`, `Real`

---

## Summary

This is a minimal 1-declaration assembly file. Its sole purpose is to close `hasse_bound_skeleton` (Silverman V.1.1, the universal Hasse bound `|#E(𝔽_q)−q−1|≤2√q`) by combining three results already established in `GapSpines` and `Hasse.QuadraticForm`. The file is not a development file; it is the milestone "top leaf" that wires the skeleton together.

---

## Declarations

### `theorem hasse_bound_skeleton`

- **Type**:
  ```
  theorem hasse_bound_skeleton (hq : 2 ≤ Fintype.card K) :
      |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤
        2 * Real.sqrt (Fintype.card K : ℝ)
  ```
  Context variables: `{K : Type*} [Field K] [Fintype K] [DecidableEq K]`, `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]`.

- **What**: Proves the universal Hasse bound `|#E(𝔽_q)−q−1|≤2√q` for an elliptic curve `W` over any finite field `K` of cardinality `q≥2`. This is Silverman V.1.1.

- **How**: Pure term-mode application of `hasse_bound_of_full_qf_nonneg_witnesses` (from `Hasse.QuadraticForm`) to four witnesses produced by `GapSpines`: the genuine `1−π` isogeny `isogOneSub_negFrobenius W hq`, its point-map identification `isogOneSub_negFrobenius_toAddMonoidHom W hq`, the kernel-degree equality `ker_deg_skeleton W hq`, and the quadratic-form non-negativity `qf_nonneg_skeleton W hq`.

- **Hypotheses**: `K` a finite field with `Fintype.card K ≥ 2`; `W` an elliptic curve (IsElliptic) over `K` with finitely many points.

- **Uses from project**:
  - `hasse_bound_of_full_qf_nonneg_witnesses` (from `HasseWeil.Hasse.QuadraticForm`)
  - `isogOneSub_negFrobenius` (from `HasseWeil.AdditionPullback.Frobenius`)
  - `isogOneSub_negFrobenius_toAddMonoidHom` (from `HasseWeil.AdditionPullback.Frobenius`)
  - `ker_deg_skeleton` (from `HasseWeil.GapSpines`)
  - `qf_nonneg_skeleton` (from `HasseWeil.GapSpines`)

- **Used by**: Unused in this file (this is the top leaf; callers are in other files, e.g. `HasseWeil.HasseBound`).

- **Visibility**: public

- **Lines**: 27–34 (declaration), proof body lines 30–33 (4 lines)

- **Notes**: No `set_option maxHeartbeats`. No `sorry` in body. Proof is 4 lines (well under the 30-line threshold). No sorries, no TODOs. The proof is a simple term-mode application; all the mathematical content lives in `GapSpines` and `QuadraticForm`. The `#print axioms` of this theorem propagates `sorryAx` only through the skeleton leaves `qf_nonneg_skeleton` and (formerly) `ker_deg_skeleton`; per the module-doc, `ker_deg_skeleton` is now PROVED, so `sorryAx` traces only to `qf_nonneg_skeleton`. This file is the "milestone assembly" top leaf.

---

## Cross-reference table

| Declaration | Calls into project | Called by (in file) |
|---|---|---|
| `hasse_bound_skeleton` | `hasse_bound_of_full_qf_nonneg_witnesses`, `isogOneSub_negFrobenius`, `isogOneSub_negFrobenius_toAddMonoidHom`, `ker_deg_skeleton`, `qf_nonneg_skeleton` | — (top leaf) |

---

## Statistics

- **Total declarations**: 1
- **Theorems/lemmas**: 1
- **Defs**: 0
- **Instances**: 0
- **Sorries in bodies**: none
- **`set_option maxHeartbeats`**: none
- **Long proofs (>30 lines)**: none
- **Key API (used by 3+ others in file)**: none (only 1 declaration)
- **Unused in file**: `hasse_bound_skeleton` (only declaration, top leaf — used by other files)

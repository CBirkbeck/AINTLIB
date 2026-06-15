# Inventory: ./HasseWeil/Hasse/SumTrace.lean

**File**: `HasseWeil/Hasse/SumTrace.lean`
**Total lines**: 137
**Total declarations**: 2 (both theorems, no defs, no instances)
**Sorries**: none
**set_option maxHeartbeats**: none

---

## Context

This file formalises the Frobenius+Verschiebung sum-trace identity
π + V = [tr π] at the `toAddMonoidHom` level (Silverman III.6.2(b)), serving
as a bridge between the Verschiebung dual construction (Worker C) and the
quadratic-form degree machinery (Worker D).  It has exactly two public theorems
and no private declarations.

---

### `theorem sum_trace_frobenius_witness`

- **Type**:
  ```
  (hq : 2 ≤ Fintype.card K)
  (h_subset : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
                (frobeniusIsog W).pullback.range)
  (one_sub_V : Isogeny W.toAffine W.toAffine)
  (h_one_sub_V_hom : one_sub_V.toAddMonoidHom =
      AddMonoidHom.id _ - (verschiebungIsog_of_witness W h_subset).toAddMonoidHom)
  (h_one_sub_isDual : IsDualOf W.toAffine one_sub_V (isogOneSub_negFrobenius W hq)) :
      (frobeniusIsog W).toAddMonoidHom + (verschiebungIsog_of_witness W h_subset).toAddMonoidHom =
      (mulByInt W.toAffine (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom
  ```
- **What**: Proves the Hasse-critical instance of the bilinear sum-trace identity π + V = [tr π], i.e., that the pointwise sum of the Frobenius and Verschiebung isogenies' hom maps equals multiplication-by-trace, where the trace is computed via `isogTrace`.
- **How**: The proof calls `trace_identity_of_dual_chain` (from `DegreeQuadraticForm.lean`) with three goals. Goal 1 (π ∘ V = [deg π]) and Goal 3 ((1−π) ∘ (1−V) = [deg(1−π)]) are both discharged by the same pattern: apply `congrArg Isogeny.toAddMonoidHom` to the `IsDualOf.2` field, specialize via `DFunLike.congr_fun`, then rewrite with `Isogeny.comp_apply` and `mulByInt_apply`. Goal 2 (the hom-form of (1−π)) is provided directly by `isogOneSub_negFrobenius_toAddMonoidHom`. The IsDualOf V π instance is derived from `verschiebungIsog_of_witness_isDualOf_frobenius`.
- **Hypotheses**: The field K is finite with ≥ 2 elements. The image of [q] in the function-field pullback is contained in the image of Frobenius (the Session-3 inclusion enabling `verschiebungIsog_of_witness`). An abstract `1−V` isogeny is given with its hom-form constraint. The substantive III.6.2(b) input `IsDualOf (1−V) (1−π)` is carried as a hypothesis.
- **Uses from project**:
  - `verschiebungIsog_of_witness` (Verschiebung/IsDual)
  - `verschiebungIsog_of_witness_isDualOf_frobenius` (Verschiebung/IsDual)
  - `frobeniusIsog` (FrobeniusIsogeny)
  - `isogOneSub_negFrobenius` (AdditionPullback/Frobenius)
  - `isogOneSub_negFrobenius_toAddMonoidHom` (AdditionPullback/Frobenius)
  - `IsDualOf` (DualIsogeny or similar)
  - `isogTrace` (DegreeQuadraticForm)
  - `trace_identity_of_dual_chain` (DegreeQuadraticForm)
  - `mulByInt_apply` (mulByInt infrastructure)
- **Used by**: unused in file; referenced in comments in `HasseWeil/WallA/VSideDual.lean` (L37, L163) and `HasseWeil/Hasse/QuadraticForm.lean` (L346, L353)
- **Visibility**: public
- **Lines**: 66–112, proof length ~32 lines (L82–112)
- **Notes**: Proof is slightly over 30 lines. The `IsDualOf (1−V) (1−π)` input is explicitly described as the "substantive III.6.2(b) ingredient" that is carried rather than derived, making this theorem witness-parametric. No sorry, no maxHeartbeats.

---

### `theorem dual_comp_frobenius_witness`

- **Type**:
  ```
  (h_subset : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
                (frobeniusIsog W).pullback.range)
  (P : W.toAffine.Point) :
      (verschiebungIsog_of_witness W h_subset).toAddMonoidHom
          ((frobeniusIsog W).toAddMonoidHom P) =
        ((frobeniusIsog W).degree : ℤ) • P
  ```
- **What**: Proves V(π(P)) = (deg π) • P pointwise, i.e., the dual-composition identity for Frobenius followed by Verschiebung, where deg π = q.
- **How**: Extracts `IsDualOf.1` (the composition field `V ∘ π = [deg π]`) from `verschiebungIsog_of_witness_isDualOf_frobenius`, then unpacks it via `congrArg Isogeny.toAddMonoidHom`, specializes at P with `DFunLike.congr_fun`, and rewrites with `Isogeny.comp_apply` and `mulByInt_apply`.
- **Hypotheses**: The Session-3 pullback-range inclusion `Im([q]) ⊆ Im(π*)` enabling `verschiebungIsog_of_witness`. A point P on the elliptic curve.
- **Uses from project**:
  - `verschiebungIsog_of_witness` (Verschiebung/IsDual)
  - `verschiebungIsog_of_witness_isDualOf_frobenius` (Verschiebung/IsDual)
  - `frobeniusIsog` (FrobeniusIsogeny)
  - `mulByInt_apply` (mulByInt infrastructure)
- **Used by**: unused in file; no references found in other files (dead-code candidate)
- **Visibility**: public
- **Lines**: 114–136, proof length ~22 lines (L126–136)
- **Notes**: The doc-string mentions `frobeniusIsog_degree` as a motivation but the proof does not call it explicitly (the degree field appears via `IsDualOf.1`). Only referenced in SumTrace.lean itself; no external callers found.

---

## Summary

| Declaration | Kind | Lines | Sorry | Long proof |
|---|---|---|---|---|
| `sum_trace_frobenius_witness` | theorem | 66–112 | no | yes (≈31 lines) |
| `dual_comp_frobenius_witness` | theorem | 119–136 | no | no |

**Key API used**: `trace_identity_of_dual_chain`, `verschiebungIsog_of_witness_isDualOf_frobenius`, `isogOneSub_negFrobenius_toAddMonoidHom`, `mulByInt_apply` — each appears in multiple goals across both proofs.

**Unused declarations**: `dual_comp_frobenius_witness` has no callers in any other file and is unused within this file.

**Notable**: The file is a clean, no-sorry, witness-parametric bridge. `sum_trace_frobenius_witness` explicitly leaves the hardest piece (`IsDualOf (1−V) (1−π)`) as a carried hypothesis; `dual_comp_frobenius_witness` appears to be a helper that was written but not yet wired into any downstream proof.

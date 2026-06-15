# Inventory: ./HasseWeil/Hasse/Witnesses.lean

**File**: `HasseWeil/Hasse/Witnesses.lean`  
**Lines**: 1–90  
**Imports**: `HasseWeil.AdditionPullback.Frobenius`, `HasseWeil.Frobenius`, `HasseWeil.EC.IsogenyKernel`

---

## Summary

A definition-only file (no proofs, no lemmas, no instances) containing one `structure` that bundles the four deferred inputs needed for the Hasse bound. No `set_option maxHeartbeats`, no `sorry`, no long proofs.

---

## Declaration Inventory

### `structure HasseWitnesses`

- **Type**:
  ```
  structure HasseWitnesses (hq : 2 ≤ Fintype.card K) where
    pc_sep              : (isogOneSub_negFrobenius W hq).IsSeparable
    pc_fin              : @FiniteDimensional W.toAffine.FunctionField
                            W.toAffine.FunctionField _ _
                            (isogOneSub_negFrobenius W hq).toAlgebra.toModule
    pc_sepDeg_eq_pointCount :
                          (isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine
    qf_nonneg           : ∀ r s : ℤ,
                            0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
                              isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) *
                                r * s + s ^ 2
  ```
  where `K : Type*` is a finite field (`[Field K] [Fintype K] [DecidableEq K]`),
  `W : WeierstrassCurve K` with `[W.toAffine.IsElliptic]` and `[Fintype W.toAffine.Point]`,
  and `hq : 2 ≤ Fintype.card K`.

- **What**: A record bundling the four deferred witness inputs sufficient to derive the Hasse bound `|#E(F_q) − q − 1| ≤ 2√q`. The four fields are: (1) separability of `1 − π`, (2) finite-dimensionality of `K(E)` over itself via `(1 − π)*`, (3) V.1.3 identity `sepDegree(1 − π) = #E(F_q)`, and (4) non-negativity of the quadratic form `q·r² − tr·r·s + s²`.

- **How**: Pure structure definition — no proof body. Each field is a Prop or typeclass-valued data field anchored on `isogOneSub_negFrobenius W hq` (the genuine `1 − π` isogeny from `AdditionPullback/Frobenius.lean`).

- **Hypotheses**: `K` a finite field with `card K ≥ 2`; `W` an elliptic curve over `K` with finitely many rational points.

- **Uses from project**:
  - `HasseWeil.isogOneSub_negFrobenius` (from `AdditionPullback/Frobenius.lean`) — the genuine `1 − π` isogeny
  - `HasseWeil.frobeniusIsog` (from `Frobenius.lean`) — the Frobenius endomorphism
  - `HasseWeil.isogTrace` (from `DegreeQuadraticForm.lean` or `EC/IsogenyKernel.lean`) — the isogeny trace
  - `HasseWeil.pointCount` (from `Frobenius.lean`) — cardinality of `E(F_q)`

- **Used by**: unused within this file; used externally by `Hasse/Final.lean` (in `hasse_bound_of_witnesses` and `hasse_bound_nat_of_witnesses`), `Hasse/OneSubFrobenius.lean` (assembles a `HasseWitnesses`), `Hasse/OpenLemmas.lean` (assembles the full bundle), and `Hasse/QuadraticForm.lean` (documents the `qf_nonneg` field).

- **Visibility**: public

- **Lines**: 42–88; no proof body (structure declaration only, ~47 lines of doc + field specs)

- **Notes**: No `sorry`, no `set_option maxHeartbeats`. The `pc_sepDeg_eq_pointCount` field carries detailed documentation (lines 54–78) explaining why the previous fiber-witness shape was circular and what the non-circular discharge route is; this documentation is the substantive mathematical content of the file.

# Inventory: ./HasseWeil/WeilPairing/OneSubProjOrdTransport.lean

**File summary**: Short assembly/wiring file (298 lines, 8 declarations) that closes leaf 2 (`OneSubFrobeniusScaling`) of the Hasse bound proof by connecting the general reduction `projOrdTransport_of_comap_pointValuation` (from `ProjOrdTransportLocal.lean`) and the proved Wall A covariance `oneSub_hcommPrime_discharged` (from `WallAGeometricRealization.lean`) with the now-fully-proved local comap witnesses for `1 − π` (from `OneSubAffineResidues.lean` and `OneSubInftyResidues.lean`).  The final theorem `oneSubFrobeniusScaling_holds` carries zero geometric hypotheses and is axiom-clean per the docstring.

---

## Declarations

### `noncomputable local instance instDecEqACOSPOT`
- **Type**: `DecidableEq (AlgebraicClosure K)`
- **What**: Provides decidable equality on the algebraic closure `K̄`, needed by downstream constructions that require `DecidableEq`.
- **How**: `Classical.decEq _` — non-constructive instance.
- **Hypotheses**: `[Field K]`
- **Uses from project**: none
- **Used by**: Used implicitly by all theorems in the `Assemble` section that work over `AlgebraicClosure K`.
- **Visibility**: private (local instance)
- **Lines**: 65 (single line)
- **Notes**: `local` instance to avoid polluting the namespace.

---

### `theorem oneSub_hproj_of_comapWitness`
- **Type**: `(hq : 2 ≤ Fintype.card K) → ComapPointValuationWitness (W.baseChange (AlgebraicClosure K)) (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)) → ProjOrdTransport (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))`
- **What**: Derives `ProjOrdTransport` (the divisor-pullback functoriality `div((1−π)^* h) = (1−π)^*(div h)`) for the base-changed `1 − π` from the local comap-valuation witnesses `ComapPointValuationWitness`, via the general engine `projOrdTransport_of_comap_pointValuation`.
- **How**: Single-step application of `projOrdTransport_of_comap_pointValuation hcomap` — the general reduction from `ProjOrdTransportLocal.lean` that packages the SamePlace + e = 1 content.
- **Hypotheses**: `W` an elliptic curve over a finite field `K` with `#K ≥ 2`; the local comap-valuation witnesses `hcomap` for the base-changed `(1 − π)_{K̄}`.
- **Uses from project**: `projOrdTransport_of_comap_pointValuation` (ProjOrdTransportLocal.lean), `oneSubFrobeniusIsogBaseChange`, `oneSubFrobeniusPullback_L`, `ComapPointValuationWitness`, `ProjOrdTransport`
- **Used by**: `oneSubFrobeniusScaling_of_comapWitness` (L115), `oneSubFrobeniusScaling_of_comapWitness_noδ` (L222)
- **Visibility**: public
- **Lines**: 77–84 (proof is 1 line: `projOrdTransport_of_comap_pointValuation hcomap`)
- **Notes**: None.

---

### `theorem oneSubFrobeniusScaling_of_comapWitness`
- **Type**: `(hq : 2 ≤ Fintype.card K) → hdeg_eq → hcomap → hsurj → OneSubFrobeniusScaling W p r (AlgebraicClosure K) hq`
  where `hdeg_eq : (oneSubFrobeniusIsogBaseChange ...).degree = pointCount W.toAffine`, `hcomap : ComapPointValuationWitness ...`, `hsurj : Function.Surjective (...).toAddMonoidHom`
- **What**: Closes `OneSubFrobeniusScaling` (the Weil-pairing scaling `e_ℓ((id−π̄)S,(id−π̄)T) = e_ℓ(S,T)^{deg(1−π)}` for all primes `ℓ ≠ p`) from three inputs: the V.1.3 degree identity, the local comap-valuation witnesses, and surjectivity of `(1−π)_{K̄}`. The translation covariance `hcomm'` is discharged internally.
- **How**: Calls `oneSubFrobeniusScaling_of_divisorDual` feeding `oneSub_hproj_of_comapWitness` for `hproj` and `oneSub_hcommPrime_discharged` for `hcomm'`. The divisor-pushforward dual `δ`/`hdc` is built automatically inside `oneSubFrobeniusScaling_of_divisorDual` using `hsurj`.
- **Hypotheses**: Finite field `K` with `#K ≥ 2`, base-changed elliptic curve `W_{K̄}` integrally closed; degree identity (V.1.3 + degree base change); local comap witnesses; surjectivity of `(1−π)_{K̄}`.
- **Uses from project**: `oneSubFrobeniusScaling_of_divisorDual` (OneSubDualDivisor.lean), `oneSub_hproj_of_comapWitness` (this file), `oneSub_hcommPrime_discharged` (WallAGeometricRealization.lean)
- **Used by**: `oneSubFrobeniusScaling_of_comapWitness_surj` (L162)
- **Visibility**: public
- **Lines**: 103–117 (proof is 4 lines)
- **Notes**: This is the intermediate form carrying all three residuals; the `_surj` and `_noδ` variants below progressively discharge them.

---

### `theorem oneSubFrobeniusIsogBaseChange_degree_eq_pointCount`
- **Type**: `(hq : 2 ≤ Fintype.card K) → (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).degree = pointCount W.toAffine`
- **What**: Proves `deg(1 − π)_{K̄} = #E(𝔽_q)` by chaining the base-change degree invariance `oneSubFrobeniusIsogBaseChange_degree_eq_of_finrankBaseChange` (giving `deg(1−π)_{K̄} = deg(1−π)` over `K`) with the V.1.3 sharp residual `isogOneSub_negFrobenius_degree_eq_pointCount` (giving `deg(1−π) = pointCount` over `K`).
- **How**: `Trans.trans` / `.trans` chaining two equalities from separate files.  Carries `sorryAx` upstream via V.1.3.
- **Hypotheses**: Finite field `K` with `#K ≥ 2`.
- **Uses from project**: `oneSubFrobeniusIsogBaseChange_degree_eq_of_finrankBaseChange` (imported, degree base-change), `isogOneSub_negFrobenius_degree_eq_pointCount` (GapSpines.lean, V.1.3 residual)
- **Used by**: `oneSubFrobeniusScaling_of_comapWitness_surj` (L163), `oneSubFrobeniusScaling_of_comapWitness_noδ_clean` (L245)
- **Visibility**: public
- **Lines**: 132–136 (proof is 2 lines)
- **Notes**: The sole sorryAx carrier in the file (via V.1.3 upstream).

---

### `theorem oneSubFrobeniusScaling_of_comapWitness_surj`
- **Type**: `(hq : 2 ≤ Fintype.card K) → hcomap → hsurj → OneSubFrobeniusScaling W p r (AlgebraicClosure K) hq`
- **What**: Closes `OneSubFrobeniusScaling` from just the local comap witnesses and surjectivity, with the degree identity discharged internally via `oneSubFrobeniusIsogBaseChange_degree_eq_pointCount`.
- **How**: Calls `oneSubFrobeniusScaling_of_comapWitness` with `oneSubFrobeniusIsogBaseChange_degree_eq_pointCount` supplying `hdeg_eq`.
- **Hypotheses**: Same as `oneSubFrobeniusScaling_of_comapWitness` minus the explicit `hdeg_eq` argument.
- **Uses from project**: `oneSubFrobeniusScaling_of_comapWitness` (this file), `oneSubFrobeniusIsogBaseChange_degree_eq_pointCount` (this file)
- **Used by**: Unused in this file (entry point for callers wanting the `δ`-based route with surjectivity; used in MEMORY notes; see HasseBound.lean for the routing decision)
- **Visibility**: public
- **Lines**: 154–165 (proof is 4 lines)
- **Notes**: Dead-code candidate within this file; the preferred route is `oneSubFrobeniusScaling_holds`.

---

### `theorem oneSubFrobeniusScaling_of_comapWitness_noδ`
- **Type**: `(hq : 2 ≤ Fintype.card K) → hdeg_eq → hcomap → OneSubFrobeniusScaling W p r (AlgebraicClosure K) hq`
- **What**: Closes `OneSubFrobeniusScaling` via the `δ`-free route `weilScales_noδ`, eliminating the surjectivity hypothesis entirely.  The dual point is read off the σ-bridge as `#ker · T` rather than via an abstract endomorphism `δ`.
- **How**: Applies `weilScales_noδ` with the abstract isogeny `φL` (= `oneSubFrobeniusIsogBaseChange`), supplying: `ProjOrdTransport` from `oneSub_hproj_of_comapWitness`, the degree equality from `oneSubFrobeniusIsogBaseChange_degree_eq_of_finrankBaseChange`, commutativity with `[ℓ]` from `oneSubFrobeniusIsogBaseChange_commute_mulByInt`, the `#ker = deg` identity from `oneSubFrobeniusIsogBaseChange_hkerdeg_of_degree_eq_pointCount`, and the translation covariance per torsion point from `oneSub_hcommPrime_discharged`.
- **Hypotheses**: Finite field `K` with `#K ≥ 2`; V.1.3 degree identity `hdeg_eq`; local comap witnesses `hcomap`.  No surjectivity.
- **Uses from project**: `weilScales_noδ` (SeparableScaling.lean), `oneSubFrobeniusIsogBaseChange_finiteKer`, `oneSubFrobeniusIsogBaseChange_toAddMonoidHom`, `oneSubFrobeniusIsogBaseChange_degree_eq_of_finrankBaseChange`, `oneSubFrobeniusIsogBaseChange_commute_mulByInt`, `oneSubFrobeniusIsogBaseChange_hkerdeg_of_degree_eq_pointCount`, `oneSub_hproj_of_comapWitness` (this file), `oneSub_hcommPrime_discharged` (WallAGeometricRealization.lean), `frobeniusHomBaseChange` (FrobMatrixData.lean), `oneSubFrobeniusPullback_L`, `oneSubFrobeniusIsogBaseChange`, `isogOneSub_negFrobenius` (for `.degree`)
- **Used by**: `oneSubFrobeniusScaling_of_comapWitness_noδ_clean` (L244)
- **Visibility**: public
- **Lines**: 196–231 (proof is 28 lines, tactic `by` block)
- **Notes**: Longest proof in the file at 28 lines. Uses `set φL` to abbreviate the isogeny and `letI`/`haveI` to install typeclass instances inline.

---

### `theorem oneSubFrobeniusScaling_of_comapWitness_noδ_clean`
- **Type**: `(hq : 2 ≤ Fintype.card K) → hcomap → OneSubFrobeniusScaling W p r (AlgebraicClosure K) hq`
- **What**: The leanest carried form: closes `OneSubFrobeniusScaling` from only the local comap witnesses, with the degree identity also discharged internally.
- **How**: Calls `oneSubFrobeniusScaling_of_comapWitness_noδ` with `oneSubFrobeniusIsogBaseChange_degree_eq_pointCount` supplying `hdeg_eq`.
- **Hypotheses**: `#K ≥ 2`; local comap witnesses `hcomap`.  No degree hypothesis, no surjectivity.
- **Uses from project**: `oneSubFrobeniusScaling_of_comapWitness_noδ` (this file), `oneSubFrobeniusIsogBaseChange_degree_eq_pointCount` (this file)
- **Used by**: `oneSubFrobeniusScaling_holds` (L292)
- **Visibility**: public
- **Lines**: 239–246 (proof is 3 lines)
- **Notes**: None.

---

### `theorem comapPointValuationWitness_oneSub`
- **Type**: `(hq : 2 ≤ Fintype.card K) → ComapPointValuationWitness (W.baseChange (AlgebraicClosure K)) (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))`
- **What**: Assembles the three fields of `ComapPointValuationWitness` for the base-changed `1 − π`: the affine comap identity, the affine-to-infinity comap identity, and the infinity order-transport.  Carries zero geometric hypotheses: all three fields are now unconditionally proved in their respective files.
- **How**: Structure literal: `affine` ← `comap_pointValuation_oneSub_eq_affine` (OneSubAffineResidues.lean); `affineToInfty` ← `comap_pointValuation_oneSub_eq_infty` (OneSubInftyResidues.lean); `infinity` ← `inftyOrdTransport_oneSub` (OneSubInftyResidues.lean).
- **Hypotheses**: `#K ≥ 2`.
- **Uses from project**: `comap_pointValuation_oneSub_eq_affine` (OneSubAffineResidues.lean), `comap_pointValuation_oneSub_eq_infty` (OneSubInftyResidues.lean), `inftyOrdTransport_oneSub` (OneSubInftyResidues.lean)
- **Used by**: `oneSubFrobeniusScaling_holds` (L293)
- **Visibility**: public
- **Lines**: 269–275 (proof is 4 lines, structure literal)
- **Notes**: The key assembly point; its axiom-cleanliness (per the docstring) is the culmination of the marathon witness work.

---

### `theorem oneSubFrobeniusScaling_holds`
- **Type**: `(hq : 2 ≤ Fintype.card K) → OneSubFrobeniusScaling W p r (AlgebraicClosure K) hq`
- **What**: Leaf 2 of `FrobBaseChangeScalings`, discharged with zero carried geometric hypotheses.  The symplectic Weil-pairing scaling `e_ℓ((id−π̄)S,(id−π̄)T) = e_ℓ(S,T)^{#E(𝔽_q)}` for all primes `ℓ ≠ p` follows from only the structural setup hypotheses on `W`.  Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
- **How**: Calls `oneSubFrobeniusScaling_of_comapWitness_noδ_clean` with `comapPointValuationWitness_oneSub` supplying the comap witnesses.
- **Hypotheses**: `#K ≥ 2` only (plus standard structural typeclasses on `W`).
- **Uses from project**: `oneSubFrobeniusScaling_of_comapWitness_noδ_clean` (this file), `comapPointValuationWitness_oneSub` (this file)
- **Used by**: `HasseBound.lean` (referenced directly in the assembly of `hasse_bound_unconditional`)
- **Visibility**: public
- **Lines**: 290–293 (proof is 2 lines)
- **Notes**: The capstone declaration; per the docstring it is axiom-clean (no `sorryAx`). Used externally by `HasseBound.lean`.

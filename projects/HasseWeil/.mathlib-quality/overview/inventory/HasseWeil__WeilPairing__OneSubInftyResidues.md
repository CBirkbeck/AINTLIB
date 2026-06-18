# Inventory: ./HasseWeil/WeilPairing/OneSubInftyResidues.lean

**Total lines:** 423  
**Total declarations:** 13 (1 noncomputable local instance, 1 def, 11 theorems)

---

## File overview

Builds the two non-affine fields — `infinity` (`InftyOrdTransport`) and `affineToInfty` — of `ComapPointValuationWitness W (1 − π)` for the base-changed `(1 − π)` over `K̄ = AlgebraicClosure K`. The key reduction: both fields follow from the two infinity-order values `ord_∞((1 − π)^* x_gen) = -2` and `ord_∞((1 − π)^* y_gen) = -3`, which are proved by chaining Wall A base-change realizations with K-level order computations and the discharged order-transport at infinity `ordAtInftyBaseChange_holds`. The file also provides two field-general abstractions (over an arbitrary field `F`) for `InftyOrdTransport` and the infinity comap identity, mirroring the `[ℓ]` proofs. No `sorry`, no `maxHeartbeats` overrides.

---

## Declarations

---

### `noncomputable local instance instDecEqACOSIR`

- **Type**: `DecidableEq (AlgebraicClosure K)`
- **What**: Installs classical decidable equality on the algebraic closure of `K`.
- **How**: `Classical.decEq _`
- **Hypotheses**: `K` a field.
- **Uses from project**: none
- **Used by**: used implicitly throughout the file for the `AlgebraicClosure K` baseChange computations
- **Visibility**: private (local)
- **Lines**: 90–90, proof length 1
- **Notes**: Standard pattern for `AlgebraicClosure` instances.

---

### `theorem ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen_K`

- **Type**: `(hq : 2 ≤ Fintype.card K) : (W_smooth W).ordAtInfty ((HasseWeil.isogOneSub_negFrobenius W hq).pullback (HasseWeil.x_gen W)) = ((-2 : ℤ) : WithTop ℤ)`
- **What**: The K-level order of `(1 − π)^K^* x_gen` at infinity is `-2` (double pole).
- **How**: Rewrites via `isogOneSub_negFrobenius_pullback` and `addPullbackAlgHom_negFrobenius_x_gen_eq` to identify the pullback as `addPullback_x (−π)`, then applies `ord_addPullback_x_negFrobenius`.
- **Hypotheses**: `2 ≤ Fintype.card K` (at least 4 elements, ensures `(1 − π)` is nontrivial).
- **Uses from project**: `HasseWeil.isogOneSub_negFrobenius_pullback`, `HasseWeil.addPullbackAlgHom_negFrobenius_x_gen_eq`, `HasseWeil.ord_addPullback_x_negFrobenius`
- **Used by**: `ordAtInfty_oneSub_pullback_x_gen`
- **Visibility**: public
- **Lines**: 104–108, proof length 2
- **Notes**: None.

---

### `theorem ordAtInfty_isogOneSub_negFrobenius_pullback_y_gen_K`

- **Type**: `(hq : 2 ≤ Fintype.card K) : (W_smooth W).ordAtInfty ((HasseWeil.isogOneSub_negFrobenius W hq).pullback (HasseWeil.y_gen W)) = ((-3 : ℤ) : WithTop ℤ)`
- **What**: The K-level order of `(1 − π)^K^* y_gen` at infinity is `-3` (triple pole).
- **How**: Same structure as `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen_K`, using the y-analogues `addPullbackAlgHom_negFrobenius_y_gen_eq` and `ord_addPullback_y_negFrobenius`.
- **Hypotheses**: `2 ≤ Fintype.card K`.
- **Uses from project**: `HasseWeil.isogOneSub_negFrobenius_pullback`, `HasseWeil.addPullbackAlgHom_negFrobenius_y_gen_eq`, `HasseWeil.ord_addPullback_y_negFrobenius`
- **Used by**: `ordAtInfty_oneSub_pullback_y_gen`
- **Visibility**: public
- **Lines**: 113–117, proof length 3
- **Notes**: None.

---

### `def OrdAtInftyBaseChange`

- **Type**: `(L : Type*) [Field L] [Algebra K L] [(W.baseChange L).toAffine.IsElliptic] : Prop` = `∀ z : W.toAffine.FunctionField, z ≠ 0 → (W_smooth (W.baseChange L)).ordAtInfty ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L z) = (W_smooth W).ordAtInfty z`
- **What**: A `Prop` asserting the infinity order is preserved under function-field base change `K(E) → L(E)` (Silverman I.2 + IV.1): the point at infinity `O` stays rational with `e = 1` under `K → L`.
- **How**: Pure `Prop` definition (no proof body).
- **Hypotheses**: `K` a finite field, `L` an extension field, `W/K` elliptic, `W_L/L` elliptic.
- **Uses from project**: `HasseWeil.Curves.SmoothPlaneCurve`, `W_smooth`
- **Used by**: `ordAtInftyBaseChange_holds` (as return type)
- **Visibility**: public
- **Lines**: 143–148, no proof body
- **Notes**: The docstring explicitly says this Prop is "kept only to read the statement; no theorem of this file carries it" — it is a documentation artifact. Only used as the return type of `ordAtInftyBaseChange_holds`.

---

### `theorem ordAtInftyBaseChange_holds`

- **Type**: `(L : Type*) [Field L] [Algebra K L] [(W.baseChange L).toAffine.IsElliptic] : OrdAtInftyBaseChange W L`
- **What**: Discharges `OrdAtInftyBaseChange`: the infinity order transports under base change because `ord_∞(f) = −intDegree(N(f))` and the norm/degree base-change is a polynomial identity commuting with `K[X] → L[X]`.
- **How**: Single application of `HasseWeil.Curves.SmoothPlaneCurve.ordAtInfty_functionFieldMap` from `Curves/OrdAtInftyBaseChange.lean`.
- **Hypotheses**: Same as `OrdAtInftyBaseChange`.
- **Uses from project**: `HasseWeil.Curves.SmoothPlaneCurve.ordAtInfty_functionFieldMap`, `OrdAtInftyBaseChange`
- **Used by**: `ordAtInfty_oneSub_pullback_x_gen`, `ordAtInfty_oneSub_pullback_y_gen`
- **Visibility**: public
- **Lines**: 156–159, proof length 2
- **Notes**: None.

---

### `theorem ordAtInfty_oneSub_pullback_x_gen`

- **Type**: `(hq : 2 ≤ Fintype.card K) : (W_smooth (W.baseChange (AlgebraicClosure K))).ordAtInfty ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)))) = ((-2 : ℤ) : WithTop ℤ)`
- **What**: Over `K̄`, the pullback of `x_gen` under `(1 − π)_{K̄}` has order `-2` at infinity.
- **How**: Rewrites via `oneSubFrobeniusIsogBaseChange_pullback` and Wall A `oneSubFrobeniusPullback_L_x_gen` (reducing `(1−π)_{K̄}^* x_gen` to `functionFieldMap((1−π)^K^* x_gen)`), then applies the discharged `ordAtInftyBaseChange_holds` (with a nonzero-check using `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen_K`), and concludes with the K-level order `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen_K`.
- **Hypotheses**: `2 ≤ Fintype.card K`.
- **Uses from project**: `ordAtInftyBaseChange_holds`, `IsogenyBaseChangeConcrete.oneSubFrobeniusPullback_L_x_gen`, `oneSubFrobeniusIsogBaseChange_pullback`, `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen_K`, `W_smooth`
- **Used by**: `inftyOrdTransport_oneSub`, `comap_pointValuation_oneSub_eq_infty`
- **Visibility**: public
- **Lines**: 168–183, proof length ~14
- **Notes**: None.

---

### `theorem ordAtInfty_oneSub_pullback_y_gen`

- **Type**: `(hq : 2 ≤ Fintype.card K) : (W_smooth (W.baseChange (AlgebraicClosure K))).ordAtInfty ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K)))) = ((-3 : ℤ) : WithTop ℤ)`
- **What**: Over `K̄`, the pullback of `y_gen` under `(1 − π)_{K̄}` has order `-3` at infinity.
- **How**: Identical structure to `ordAtInfty_oneSub_pullback_x_gen`, using the y-variants `oneSubFrobeniusPullback_L_y_gen` and `ordAtInfty_isogOneSub_negFrobenius_pullback_y_gen_K`.
- **Hypotheses**: `2 ≤ Fintype.card K`.
- **Uses from project**: `ordAtInftyBaseChange_holds`, `IsogenyBaseChangeConcrete.oneSubFrobeniusPullback_L_y_gen`, `oneSubFrobeniusIsogBaseChange_pullback`, `ordAtInfty_isogOneSub_negFrobenius_pullback_y_gen_K`, `W_smooth`
- **Used by**: `inftyOrdTransport_oneSub`, `comap_pointValuation_oneSub_eq_infty`
- **Visibility**: public
- **Lines**: 187–202, proof length ~14
- **Notes**: None.

---

### `theorem inftyOrdTransport_of_ordAtInfty_x_y`

- **Type**: `(W' : WeierstrassCurve F) [W'.toAffine.IsElliptic] (φ : Isogeny W'.toAffine W'.toAffine) (hx : ord_∞(φ^* x_gen) = -2) (hy : ord_∞(φ^* y_gen) = -3) : DivisorPullback.InftyOrdTransport φ`
- **What**: Field-general lemma: any isogeny `φ` of an elliptic curve over `F` with `ord_∞(φ^* x_gen) = -2` and `ord_∞(φ^* y_gen) = -3` satisfies `InftyOrdTransport φ` (i.e., `ord_∞(φ^* h) = ord_∞ h` for all `h`).
- **How**: Forms the comap valuation `w = ordAtInftyValuation ∘ φ^*`, shows it sends `x_gen ↦ exp 2`, `y_gen ↦ exp 3`, and fixes `F^×` (via `φ^*` commuting with algebraMap and `ordAtInfty_algebraMap_F_nonzero`), then applies the master pinning `eq_ordAtInftyValuation_of_x_y` to conclude `w = ordAtInftyValuation`, and reads off the order equality for nonzero elements via `ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq` and `WithZero.exp_inj`.
- **Hypotheses**: `F` a field with `DecidableEq`; `W'` an elliptic curve over `F`; two infinity-order hypotheses on `φ`.
- **Uses from project**: `HasseWeil.eq_ordAtInftyValuation_of_x_y`, `HasseWeil.ordAtInfty_algebraMap_F_nonzero`, `HasseWeil.ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq`, `DivisorPullback.InftyOrdTransport`
- **Used by**: `inftyOrdTransport_oneSub`
- **Visibility**: public
- **Lines**: 220–276, proof length ~56
- **Notes**: **Proof >30 lines (56 lines).** Field-general abstraction of `inftyOrdTransport_mulByInt` from `DivisorPullback.lean`.

---

### `theorem neg_mem_kernel_of_image_zero`

- **Type**: `(W' : WeierstrassCurve F) [W'.toAffine.IsElliptic] (φ : Isogeny W'.toAffine W'.toAffine) (Q : W'.toAffine.Point) (hQ : φ.toAddMonoidHom Q = 0) : (-Q : W'.toAffine.Point) ∈ φ.kernel`
- **What**: If `φ(Q) = O`, then `−Q ∈ ker φ` (since `φ(−Q) = −φ(Q) = −O = O`).
- **How**: `map_neg` on the additive group homomorphism `φ.toAddMonoidHom`, then `neg_zero`.
- **Hypotheses**: `F` a field; `W'` an elliptic curve; `φ` an isogeny; `φ(Q) = O`.
- **Uses from project**: `HasseWeil.Isogeny.mem_kernel_iff`
- **Used by**: `comap_pointValuation_eq_infty_of_ordAtInfty_x_y_of_kernelInvariant`
- **Visibility**: public
- **Lines**: 288–292, proof length 2
- **Notes**: Small helper lemma; could potentially be in a more general isogeny kernel file.

---

### `theorem comap_pointValuation_eq_infty_of_ordAtInfty_x_y_of_kernelInvariant`

- **Type**: `(W' : WeierstrassCurve F) [W'.toAffine.IsElliptic] (φ : Isogeny W'.toAffine W'.toAffine) (hx : ...) (hy : ...) (hcov : ∀ k ∈ ker φ, ∀ z, τ_k(φ^* z) = φ^* z) (P : SmoothPoint) (hQ : φ(P) = O) : (pointValuation P).comap φ^* = ordAtInftyValuation`
- **What**: Field-general lemma: for any isogeny `φ` over `F`, a smooth point `P` in the kernel, two infinity-order hypotheses, and kernel-translation invariance, the comap of `pointValuation P` through `φ^*` equals `ordAtInftyValuation`.
- **How**: Sets `k = −P ∈ ker φ` via `neg_mem_kernel_of_image_zero`; uses the field-general translation transport `ord_P_eq_ordAtInfty_of_invariant_and_compatible` (from `isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint`) together with kernel-invariance to conclude `ord_P(φ^* x_gen) = -2` and `ord_P(φ^* y_gen) = -3`; then pins the comap via `pointValuation_eq_exp_neg_of_ord_P_eq` and `eq_ordAtInftyValuation_of_x_y`.
- **Hypotheses**: As above; `F` a field with `DecidableEq`; `W'` elliptic; `φ` an isogeny with the stated order and invariance hypotheses; `P` a smooth point with `φ(P) = O`.
- **Uses from project**: `neg_mem_kernel_of_image_zero`, `HasseWeil.isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint`, `HasseWeil.ord_P_eq_ordAtInfty_of_invariant_and_compatible`, `HasseWeil.pointValuation_eq_exp_neg_of_ord_P_eq`, `HasseWeil.pointValuation_algebraMap_F_eq_one_of_ne_zero`, `HasseWeil.eq_ordAtInftyValuation_of_x_y`
- **Used by**: `comap_pointValuation_oneSub_eq_infty`
- **Visibility**: public
- **Lines**: 305–351, proof length ~46
- **Notes**: **Proof >30 lines (46 lines).** Field-general abstraction of `comap_pointValuation_mulByInt_eq_infty` from `DivisorPullback.lean`.

---

### `theorem inftyOrdTransport_oneSub`

- **Type**: `(hq : 2 ≤ Fintype.card K) : DivisorPullback.InftyOrdTransport (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))`
- **What**: The `infinity` field of `ComapPointValuationWitness` for `(1 − π)_{K̄}`: the order at infinity is transported under `(1 − π)_{K̄}^*`.
- **How**: Term-mode application of `inftyOrdTransport_of_ordAtInfty_x_y` to the two `K̄` infinity orders `ordAtInfty_oneSub_pullback_x_gen` and `ordAtInfty_oneSub_pullback_y_gen`.
- **Hypotheses**: `2 ≤ Fintype.card K`.
- **Uses from project**: `inftyOrdTransport_of_ordAtInfty_x_y`, `ordAtInfty_oneSub_pullback_x_gen`, `ordAtInfty_oneSub_pullback_y_gen`
- **Used by**: `OneSubProjOrdTransport.lean` (the `infinity` field of the witness bundle)
- **Visibility**: public
- **Lines**: 360–368, proof length ~8 (term mode)
- **Notes**: None.

---

### `theorem oneSub_hcov_kernel`

- **Type**: `(hq : 2 ≤ Fintype.card K) (k : (oneSubFrobeniusIsogBaseChange ...).kernel) (z : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) : translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) k.val ((oneSubFrobeniusIsogBaseChange ...).pullback z) = (oneSubFrobeniusIsogBaseChange ...).pullback z`
- **What**: For any `k ∈ ker(1 − π)_{K̄}`, the translation `τ_k` fixes the pullback range: `τ_k((1 − π)^* z) = (1 − π)^* z`.
- **How**: Term-mode application of `hcov_of_mapTranslateGenericPoint_canonical` to the Wall A covariance `mapTranslateGenericPoint_oneSub_canonical` (which proves generic-point translation covariance for `(1 − π)_{K̄}` CoordHom-free).
- **Hypotheses**: `2 ≤ Fintype.card K`.
- **Uses from project**: `hcov_of_mapTranslateGenericPoint_canonical`, `mapTranslateGenericPoint_oneSub_canonical`
- **Used by**: `comap_pointValuation_oneSub_eq_infty`
- **Visibility**: public
- **Lines**: 379–391, proof length ~11 (term mode)
- **Notes**: None.

---

### `theorem comap_pointValuation_oneSub_eq_infty`

- **Type**: `(hq : 2 ≤ Fintype.card K) (P : SmoothPoint) (hQ : (oneSubFrobeniusIsogBaseChange ...).toAddMonoidHom (P.toAffinePoint) = 0) : (pointValuation P).comap (oneSubFrobeniusIsogBaseChange ...).pullback.toRingHom = ordAtInftyValuation`
- **What**: The `affineToInfty` field: for a kernel point `P` of `(1 − π)_{K̄}`, the comap of `pointValuation P` through `(1 − π)^*` equals `ordAtInftyValuation`.
- **How**: Term-mode application of `comap_pointValuation_eq_infty_of_ordAtInfty_x_y_of_kernelInvariant` with `ordAtInfty_oneSub_pullback_x_gen`, `ordAtInfty_oneSub_pullback_y_gen`, and `oneSub_hcov_kernel`.
- **Hypotheses**: `2 ≤ Fintype.card K`; `P` a smooth point of `E_{K̄}` in the kernel of `(1 − π)`.
- **Uses from project**: `comap_pointValuation_eq_infty_of_ordAtInfty_x_y_of_kernelInvariant`, `ordAtInfty_oneSub_pullback_x_gen`, `ordAtInfty_oneSub_pullback_y_gen`, `oneSub_hcov_kernel`
- **Used by**: `OneSubProjOrdTransport.lean` (the `affineToInfty` field of the witness bundle)
- **Visibility**: public
- **Lines**: 403–421, proof length ~17 (term mode)
- **Notes**: None.

---

## Summary statistics

- **Definitions**: 1 (`OrdAtInftyBaseChange`)
- **Theorems/Lemmas**: 11 + 1 instance = 12 non-def declarations
- **Sorry**: none
- **maxHeartbeats overrides**: none
- **Long proofs (>30 lines)**: `inftyOrdTransport_of_ordAtInfty_x_y` (~56 lines), `comap_pointValuation_eq_infty_of_ordAtInfty_x_y_of_kernelInvariant` (~46 lines)
- **Key API (used by 2+ in-file callers)**: `ordAtInftyBaseChange_holds` (by `ordAtInfty_oneSub_pullback_x_gen` and `ordAtInfty_oneSub_pullback_y_gen`); `ordAtInfty_oneSub_pullback_x_gen` (by `inftyOrdTransport_oneSub` and `comap_pointValuation_oneSub_eq_infty`); `ordAtInfty_oneSub_pullback_y_gen` (by same pair)
- **Unused within file**: `OrdAtInftyBaseChange` (the Prop def — used only as the return type of `ordAtInftyBaseChange_holds`, which is used in-file; the def itself is "documentation-only"), `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen_K` (used only by `ordAtInfty_oneSub_pullback_x_gen`), `ordAtInfty_isogOneSub_negFrobenius_pullback_y_gen_K` (used only by `ordAtInfty_oneSub_pullback_y_gen`), `neg_mem_kernel_of_image_zero` (used only by `comap_pointValuation_eq_infty_of_ordAtInfty_x_y_of_kernelInvariant`), `inftyOrdTransport_of_ordAtInfty_x_y` (used only by `inftyOrdTransport_oneSub`), `comap_pointValuation_eq_infty_of_ordAtInfty_x_y_of_kernelInvariant` (used only by `comap_pointValuation_oneSub_eq_infty`). Exported API: `inftyOrdTransport_oneSub` and `comap_pointValuation_oneSub_eq_infty` (consumed by `OneSubProjOrdTransport.lean`); `inftyOrdTransport_of_ordAtInfty_x_y` and `comap_pointValuation_eq_infty_of_ordAtInfty_x_y_of_kernelInvariant` (reused by `PencilComapWitnesses.lean`).

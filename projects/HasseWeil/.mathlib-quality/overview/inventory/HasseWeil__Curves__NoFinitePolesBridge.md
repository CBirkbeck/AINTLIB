# Inventory: ./HasseWeil/Curves/NoFinitePolesBridge.lean

**File**: `HasseWeil/Curves/NoFinitePolesBridge.lean`
**Total lines**: 386
**Imports**: `HasseWeil.Curves.AFConditional`, `HasseWeil.Curves.NormValuation`, `Mathlib.RingTheory.DedekindDomain.AdicValuation`

**Purpose**: Bridges the project's `ord_P`/`pointValuation` framework with
mathlib's `HeightOneSpectrum.valuation` framework to discharge
`NoFinitePolesBridge W` — the claim that a function-field element with
non-negative order at every smooth point lies in the coordinate ring.

---

## Declaration Index

### `noncomputable def smoothPointToHeightOne`

- **Type**: `[IsDedekindDomain CR] → (P : SmoothPoint) → HeightOneSpectrum CR`
  (where `CR = (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing`)
- **What**: Constructs the `HeightOneSpectrum` element corresponding to a
  smooth point `P` by setting `asIdeal := maximalIdealAt P`. The three
  `HeightOneSpectrum` fields (asIdeal, isPrime, ne_bot) are filled
  directly from project lemmas.
- **How**: Uses `maximalIdealAt_isMaximal P` for primeness and
  `maximalIdealAt_ne_bot P` for non-triviality. Pure constructor.
- **Hypotheses**: `IsDedekindDomain CR` (so `maximalIdealAt_ne_bot` applies).
- **Uses from project**: `SmoothPlaneCurve.maximalIdealAt`, `SmoothPlaneCurve.maximalIdealAt_isMaximal`, `SmoothPlaneCurve.maximalIdealAt_ne_bot`
- **Used by**: `smoothPointToHeightOne_asIdeal`, `smoothPointToHeightOne_surjective`, `PointValuationEqHeightOneValuation`, `noFinitePolesBridge_of_valuationEq`, `pointValuation_eq_heightOneValuation_algebraMap`, `pointValuation_eq_heightOneValuation`, `noFinitePolesBridge_unconditional`
- **Visibility**: public
- **Lines**: 46–52, proof length: 3 lines (structure body)
- **Notes**: No sorries, no maxHeartbeats.

---

### `@[simp] theorem smoothPointToHeightOne_asIdeal`

- **Type**: `(smoothPointToHeightOne W P).asIdeal = (⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt P`
- **What**: States that the ideal underlying `smoothPointToHeightOne W P` is
  definitionally equal to `maximalIdealAt P`. Marked `@[simp]` for
  automation.
- **How**: Proof by `rfl` (definitional equality from the constructor).
- **Hypotheses**: `IsDedekindDomain CR`.
- **Uses from project**: `smoothPointToHeightOne` (the definition being
  unfolded)
- **Used by**: `pointValuation_eq_heightOneValuation_algebraMap` (in a `rw`)
- **Visibility**: public
- **Lines**: 54–58, proof length: 1 line (`rfl`)
- **Notes**: No sorries, no maxHeartbeats.

---

### `theorem smoothPointToHeightOne_surjective`

- **Type**: `[IsAlgClosed F] [IsElliptic] [IsDedekindDomain CR] → (v : HeightOneSpectrum CR) → ∃ P : SmoothPoint, smoothPointToHeightOne W P = v`
- **What**: Every height-one prime of the coordinate ring is of the form
  `maximalIdealAt P` for some smooth point `P`; equivalently,
  `smoothPointToHeightOne` is surjective.
- **How**: Uses mathlib's `Ring.DimensionLEOne.maximalOfPrime` to promote
  the height-one prime to a maximal ideal, then invokes the project's
  `maximalIdealAt_range` (from `NormValuation.lean`) which states that
  the range of `maximalIdealAt` is exactly the set of maximal ideals of
  the coordinate ring. Concludes via `HeightOneSpectrum.ext`.
- **Hypotheses**: `IsAlgClosed F` (needed for `maximalIdealAt_range`),
  `IsElliptic`, `IsDedekindDomain CR`.
- **Uses from project**: `smoothPointToHeightOne`, `SmoothPlaneCurve.maximalIdealAt_range`
- **Used by**: `noFinitePolesBridge_of_valuationEq`, `pointValuation_eq_heightOneValuation`
- **Visibility**: public
- **Lines**: 69–87, proof length: 14 lines
- **Notes**: No sorries, no maxHeartbeats.

---

### `def PointValuationEqHeightOneValuation`

- **Type**: `[IsDedekindDomain CR] → Prop`
  (the statement `∀ P f, pointValuation P f = (smoothPointToHeightOne W P).valuation FunctionField f`)
- **What**: A named `Prop` asserting that the project's `pointValuation P`
  and mathlib's `HeightOneSpectrum.valuation` (for the corresponding
  height-one prime) agree everywhere on the function field. Acts as the
  "outstanding hypothesis" factored out for the conditional bridge.
- **How**: Pure `def` of a `Prop`; no proof content.
- **Hypotheses**: `IsDedekindDomain CR`.
- **Uses from project**: `smoothPointToHeightOne`, `SmoothPlaneCurve.pointValuation`, `SmoothPlaneCurve.FunctionField`
- **Used by**: `noFinitePolesBridge_of_valuationEq` (consumed as hypothesis), `pointValuation_eq_heightOneValuation` (discharged unconditionally)
- **Visibility**: public
- **Lines**: 132–138, proof length: 0 (def, not a theorem)
- **Notes**: No sorries. This is a "factored hypothesis" pattern common in
  the project. The predicate is discharged by
  `pointValuation_eq_heightOneValuation` below.

---

### `theorem pointValuation_le_one_of_ord_nonneg`

- **Type**: `{f : FunctionField} → (hf : f ≠ 0) → (P : SmoothPoint) → (h_ord : 0 ≤ ord_P P f) → pointValuation P f ≤ 1`
- **What**: If `ord_P P f ≥ 0` (no pole at `P`) then `pointValuation P f ≤ 1`
  (the valuative criterion for membership in the integral closure). Connects
  the project's integer-valued order to the multiplicative valuation.
- **How**: Unfolds `ord_P` (defined as the negation of `toAdd` of the
  multiplicative valuation) to extract `(WithZero.unzero h_zero).toAdd ≤ 0`,
  then uses `WithZero.coe_le_coe` and `Multiplicative.toAdd` monotonicity
  to conclude `pointValuation P f ≤ 1 = ofAdd 0`. The case `pointValuation P f = 0` is handled separately (trivially `0 ≤ 1`).
- **Hypotheses**: `f ≠ 0` (needed to unzero the valuation), `ord_P P f ≥ 0`.
- **Uses from project**: `SmoothPlaneCurve.ord_P`, `SmoothPlaneCurve.pointValuation`
- **Used by**: `noFinitePolesBridge_of_valuationEq`
- **Visibility**: public
- **Lines**: 143–168, proof length: 22 lines
- **Notes**: No sorries, no maxHeartbeats. The proof involves manual
  `WithTop`/`WithZero`/`Multiplicative` coercion arithmetic. Uses `exact_mod_cast`, `omega` for integer arithmetic.

---

### `theorem noFinitePolesBridge_of_valuationEq`

- **Type**: `[IsAlgClosed F] [IsElliptic] [IsDedekindDomain CR] [IsIntegrallyClosed CR] → (h_id : PointValuationEqHeightOneValuation W) → NoFinitePolesBridge W`
- **What**: The conditional bridge: given that `pointValuation = heightOneValuation`
  everywhere (the technically-outstanding identification), proves
  `NoFinitePolesBridge W` (every function with non-negative orders at all
  smooth points lies in the coordinate ring).
- **How**: Applies the project's `mem_coordinateRing_of_valuation_le_one`
  (which takes: valuation `≤ 1` at every height-one prime implies f is
  integral), fills each height-one prime by `smoothPointToHeightOne_surjective`,
  then rewrites using `h_id` and applies `pointValuation_le_one_of_ord_nonneg`.
- **Hypotheses**: `IsAlgClosed F`, `IsElliptic`, `IsDedekindDomain CR`,
  `IsIntegrallyClosed CR`, and the hypothesis `h_id :
  PointValuationEqHeightOneValuation W`.
- **Uses from project**: `SmoothPlaneCurve.mem_coordinateRing_of_valuation_le_one`, `smoothPointToHeightOne_surjective`, `pointValuation_le_one_of_ord_nonneg`, `PointValuationEqHeightOneValuation`
- **Used by**: `noFinitePolesBridge_unconditional`
- **Visibility**: public
- **Lines**: 176–187, proof length: 8 lines
- **Notes**: No sorries, no maxHeartbeats. This is the "conditional" form;
  the unconditional version below plugs in the discharged `h_id`.

---

### `theorem pointValuation_eq_heightOneValuation_algebraMap`

- **Type**: `[IsAlgClosed F] [IsElliptic] [IsDedekindDomain CR] [IsIntegrallyClosed CR] → (P : SmoothPoint) → (u : CR) → pointValuation P (algebraMap CR FunctionField u) = (smoothPointToHeightOne W P).valuation FunctionField (algebraMap CR FunctionField u)`
- **What**: Establishes the valuation identification for elements in the
  image of `algebraMap` (i.e., elements of the coordinate ring viewed in
  the function field). Both sides equal `exp(-count_M (Ideal.span {u}))` for
  nonzero `u`, and both are `0` when `u = 0`.
- **How**: Case-splits on `u = 0` (handled by `simp`). For `u ≠ 0`, rewrites
  the left side using the project's `pointValuation_algebraMap_eq_exp_count`
  (from `NormValuation.lean`) and the right side using mathlib's
  `HeightOneSpectrum.valuation_of_algebraMap` and
  `HeightOneSpectrum.intValuation_if_neg`, then applies
  `smoothPointToHeightOne_asIdeal` to identify the ideals.
- **Hypotheses**: `IsAlgClosed F`, `IsElliptic`, `IsDedekindDomain CR`,
  `IsIntegrallyClosed CR`.
- **Uses from project**: `SmoothPlaneCurve.pointValuation_algebraMap_eq_exp_count`, `smoothPointToHeightOne_asIdeal`
- **Used by**: `pointValuation_eq_heightOneValuation`
- **Visibility**: public
- **Lines**: 203–222, proof length: 9 lines
- **Notes**: No sorries, no maxHeartbeats. This is the key lemma that closes
  the valuation identification for the algMap case; the full identification
  then follows by `IsFractionRing.div_surjective`.

---

### `theorem pointValuation_eq_heightOneValuation`

- **Type**: `[IsAlgClosed F] [IsElliptic] [IsDedekindDomain CR] [IsIntegrallyClosed CR] → PointValuationEqHeightOneValuation W`
- **What**: Unconditionally proves that the project's `pointValuation P`
  and mathlib's `HeightOneSpectrum.valuation` agree for every element of
  the function field. Discharges the predicate
  `PointValuationEqHeightOneValuation W` without any additional hypotheses.
- **How**: Case-splits on `f = 0` (handled by `simp`). For `f ≠ 0`, uses
  `IsFractionRing.div_surjective` to write `f = algMap u / algMap v`, then
  rewrites via `Valuation.map_div` on both sides, and applies
  `pointValuation_eq_heightOneValuation_algebraMap` twice.
- **Hypotheses**: `IsAlgClosed F`, `IsElliptic`, `IsDedekindDomain CR`,
  `IsIntegrallyClosed CR`.
- **Uses from project**: `pointValuation_eq_heightOneValuation_algebraMap`, `PointValuationEqHeightOneValuation`
- **Used by**: `noFinitePolesBridge_unconditional`
- **Visibility**: public
- **Lines**: 232–247, proof length: 12 lines
- **Notes**: No sorries, no maxHeartbeats. This is the central technical
  result of the file — it discharges the "outstanding" valuation identification
  mentioned in the file's module docstring.

---

### `theorem noFinitePolesBridge_unconditional`

- **Type**: `[IsAlgClosed F] [IsElliptic] [IsDedekindDomain CR] [IsIntegrallyClosed CR] → NoFinitePolesBridge W`
- **What**: The fully unconditional `NoFinitePolesBridge W`: every
  function-field element with non-negative order at all smooth points is
  in the coordinate ring.
- **How**: One-line composition: applies `noFinitePolesBridge_of_valuationEq`
  with `pointValuation_eq_heightOneValuation W` as the `h_id` witness.
- **Hypotheses**: `IsAlgClosed F`, `IsElliptic`, `IsDedekindDomain CR`,
  `IsIntegrallyClosed CR`.
- **Uses from project**: `noFinitePolesBridge_of_valuationEq`, `pointValuation_eq_heightOneValuation`
- **Used by**: `pointMinusOPrincipalEqZero_unconditional`, `AddHomProperty_of_miller_divZeroReduce`, `picZeroIsoE_of_AFInputs` (indirectly), external files: `Miller.lean`, `Constancy.lean`
- **Visibility**: public
- **Lines**: 251–256, proof length: 2 lines (term-mode)
- **Notes**: No sorries, no maxHeartbeats. This is the key export of the
  file.

---

### `theorem pointMinusOPrincipalEqZero_unconditional`

- **Type**: `[IsAlgClosed F] [IsElliptic] [IsDedekindDomain CR] [IsIntegrallyClosed CR] → PointMinusOPrincipalEqZero W`
- **What**: If the divisor `(P) − (O)` is principal on a smooth-plane
  elliptic curve over an algebraically-closed field with integrally-closed
  coordinate ring, then `P = O`. This is one of the two AF witnesses
  for the Pic⁰ chain.
- **How**: One-line: applies `pointMinusO_of_bridge` (from `AFConditional.lean`)
  with `noFinitePolesBridge_unconditional W` as the bridge.
- **Hypotheses**: `IsAlgClosed F`, `IsElliptic`, `IsDedekindDomain CR`,
  `IsIntegrallyClosed CR`.
- **Uses from project**: `pointMinusO_of_bridge` (from `AFConditional.lean`), `noFinitePolesBridge_unconditional`
- **Used by**: External file `OpenLemmas.lean` (which re-exports it)
- **Visibility**: public
- **Lines**: 264–269, proof length: 2 lines (term-mode)
- **Notes**: No sorries, no maxHeartbeats.

---

### `theorem AddHomProperty_of_miller_divZeroReduce`

- **Type**: `{W₁ W₂ : Affine F} [IsElliptic₁] [IsElliptic₂] [IsAlgClosed F] [NeZero 2] [NeZero 3] [IsDedekindDomain CR₁] [IsDedekindDomain CR₂] [IsIntegrallyClosed CR₁] [IsIntegrallyClosed CR₂] → (φ : Isogeny W₁ W₂) → (cd : CoordHom) → (h_miller₁ : MillerHypothesis W₁) → (h_miller₂ : MillerHypothesis W₂) → (h_dzr₁ : DivZeroReduce W₁) → (h_dzr₂ : DivZeroReduce W₂) → (h_pres : ...) → φ.AddHomProperty cd`
- **What**: Given `MillerHypothesis` and `DivZeroReduce` for both curves
  and the pushforward-preserves-principal hypothesis `h_pres`, proves
  the universal group homomorphism property of `φ`. The unconditional
  `noFinitePolesBridge` is filled in automatically, reducing the interface
  to the two remaining mathematical pieces.
- **How**: Applies `AddHomProperty_of_AFInputs` (from `AFConditional.lean`)
  with the two `AFInputs` bundles formed from the given Miller/DivZeroReduce
  witnesses, `noFinitePolesBridge_unconditional` for each curve, and
  `SmoothPlaneCurve.principal_mem_degZero` for the degree-zero condition.
- **Hypotheses**: `IsAlgClosed F`, `NeZero 2`, `NeZero 3`, `IsElliptic` for
  both curves, `IsDedekindDomain CR` and `IsIntegrallyClosed CR` for both,
  plus `MillerHypothesis`, `DivZeroReduce`, and `h_pres` as explicit
  hypotheses.
- **Uses from project**: `AddHomProperty_of_AFInputs` (from `AFConditional.lean`), `noFinitePolesBridge_unconditional`, `SmoothPlaneCurve.principal_mem_degZero`
- **Used by**: External file `Miller.lean` (applied unconditionally once
  Miller and DivZeroReduce land)
- **Visibility**: public
- **Lines**: 287–308, proof length: 7 lines
- **Notes**: No sorries, no maxHeartbeats. The doc-comment carefully lists
  the three remaining gates (MillerHypothesis for both, DivZeroReduce for
  both, h_pres).

---

### `noncomputable def picZeroIsoE_of_AFInputs`

- **Type**: `{W : Affine F} [IsElliptic] [IsAlgClosed F] [NeZero 2] [NeZero 3] [IsDedekindDomain CR] [IsIntegrallyClosed CR] → (a : AFInputs W) → PicProj₀ (⟨W⟩) ≃+ W.Point`
- **What**: Constructs the additive equivalence `Pic⁰(E) ≃+ E.Point`
  (Silverman III.3.4) parametric on `AFInputs W`. This is T-III-3-004.
  The forward map is `σ̄ = picZeroSumOfWitness`, the inverse is
  `κ = picZeroOfPoint`, and the four `AddEquiv` axioms are verified
  from the supplied witnesses.
- **How**: Builds an `AddEquiv` record:
  - `toFun = sigmaBar := picZeroSumOfWitness W h_van` (the group hom from Pic⁰ to E.Point)
  - `invFun = picZeroOfPoint W`
  - `left_inv`: uses `h_inj_of_divZeroReduce W a.divZeroReduce h_van`
  - `right_inv`: uses `picZeroSumOfWitness_picZeroOfPoint W h_van P`
  - `map_add'`: directly `sigmaBar.map_add`
  The `h_van` witness that `σ` vanishes on principal divisors is obtained
  from `a.h_van` with `principal_mem_degZero`.
- **Hypotheses**: `IsAlgClosed F`, `NeZero 2`, `NeZero 3`, `IsElliptic`,
  `IsDedekindDomain CR`, `IsIntegrallyClosed CR`, and `AFInputs W`
  (which bundles `MillerHypothesis`, `DivZeroReduce`, `NoFinitePolesBridge`).
- **Uses from project**: `AFInputs.h_van`, `SmoothPlaneCurve.principal_mem_degZero`, `HasseWeil.EC.Isogeny.picZeroSumOfWitness`, `picZeroOfPoint`, `h_inj_of_divZeroReduce`, `HasseWeil.EC.Isogeny.picZeroSumOfWitness_picZeroOfPoint`
- **Used by**: `picZeroIsoE_baseChange_of_AFInputs`, external files `Miller.lean` and `OpenLemmaPrimitives.lean`
- **Visibility**: public
- **Lines**: 335–354, proof length: ~18 lines (let-body)
- **Notes**: No sorries, no maxHeartbeats. `noncomputable` because
  `picZeroSumOfWitness` and `picZeroOfPoint` are noncomputable.

---

### `noncomputable def picZeroIsoE_baseChange_of_AFInputs`

- **Type**: `{F L : Type*} [Field F] [Field L] [Algebra F L] [DecidableEq L] [IsAlgClosed L] [NeZero 2] [NeZero 3] (W : Affine F) [IsElliptic] [IsDedekindDomain CR_L] [IsIntegrallyClosed CR_L] → (a : AFInputs (W.baseChange L)) → PicProj₀ (⟨W.baseChange L⟩) ≃+ (W.baseChange L).Point`
- **What**: The T-III-3-004 isomorphism instantiated at `L = AlgebraicClosure F`
  (or any algebraically closed extension). Wrapper around
  `picZeroIsoE_of_AFInputs` for the base-changed curve `W.baseChange L`.
- **How**: One-line: `picZeroIsoE_of_AFInputs (W := W.baseChange L) a`.
- **Hypotheses**: `IsAlgClosed L`, `NeZero 2 L`, `NeZero 3 L`,
  `IsDedekindDomain` and `IsIntegrallyClosed` for the coordinate ring of
  `W.baseChange L`, and `AFInputs (W.baseChange L)`.
- **Uses from project**: `picZeroIsoE_of_AFInputs`
- **Used by**: External files (cascade in `OpenLemmaPrimitives.lean`)
- **Visibility**: public
- **Lines**: 373–384, proof length: 2 lines (term-mode)
- **Notes**: No sorries, no maxHeartbeats. Explicit type-variable separation
  (`F` and `L` distinct) allows clean instantiation at `L = AlgebraicClosure F`.

---

## Cross-reference summary

| Declaration | Used by (in this file) |
|---|---|
| `smoothPointToHeightOne` | `smoothPointToHeightOne_asIdeal`, `smoothPointToHeightOne_surjective`, `PointValuationEqHeightOneValuation`, `noFinitePolesBridge_of_valuationEq`, `pointValuation_eq_heightOneValuation_algebraMap`, `pointValuation_eq_heightOneValuation`, `noFinitePolesBridge_unconditional` |
| `smoothPointToHeightOne_asIdeal` | `pointValuation_eq_heightOneValuation_algebraMap` |
| `smoothPointToHeightOne_surjective` | `noFinitePolesBridge_of_valuationEq`, `pointValuation_eq_heightOneValuation` |
| `PointValuationEqHeightOneValuation` | `noFinitePolesBridge_of_valuationEq`, `pointValuation_eq_heightOneValuation` |
| `pointValuation_le_one_of_ord_nonneg` | `noFinitePolesBridge_of_valuationEq` |
| `noFinitePolesBridge_of_valuationEq` | `noFinitePolesBridge_unconditional` |
| `pointValuation_eq_heightOneValuation_algebraMap` | `pointValuation_eq_heightOneValuation` |
| `pointValuation_eq_heightOneValuation` | `noFinitePolesBridge_unconditional` |
| `noFinitePolesBridge_unconditional` | `pointMinusOPrincipalEqZero_unconditional`, `AddHomProperty_of_miller_divZeroReduce`, `picZeroIsoE_of_AFInputs` (indirectly) |
| `pointMinusOPrincipalEqZero_unconditional` | (none in file; exported) |
| `AddHomProperty_of_miller_divZeroReduce` | (none in file; exported) |
| `picZeroIsoE_of_AFInputs` | `picZeroIsoE_baseChange_of_AFInputs` |
| `picZeroIsoE_baseChange_of_AFInputs` | (none in file; exported) |

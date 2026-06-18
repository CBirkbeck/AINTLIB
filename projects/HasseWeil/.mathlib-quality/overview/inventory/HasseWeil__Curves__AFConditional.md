# Inventory: ./HasseWeil/Curves/AFConditional.lean

**File summary**: 297 lines. Conditional witness file wiring the AF unified package (Silverman III.4.8) for elliptic curves. Introduces three Prop-valued predicates capturing outstanding proof obligations, plus theorems deriving the two required witnesses `h_inj` and `h_van` from those predicates, a bundling structure `AFInputs`, and a final `AddHomProperty` wrapper. No `sorry` and no `set_option maxHeartbeats`.

---

### `def DivZeroReduce`

- **Type**: `(W : Affine F) [W.IsElliptic] → Prop`
  `∀ D : ProjectiveDivisor.degZero C, ProjLinearlyEquiv C D.val (kappaDivisor W (projectiveDivisorSum W D.val))`
- **What**: States that every degree-zero projective divisor `D` is linearly equivalent to `(σD) − (O)` (the image of the Divisor-to-Point map minus the identity section). This is the divisor-reduction hypothesis needed to show `κ ∘ σ̄ = id`.
- **How**: Pure `Prop` definition; no proof body.
- **Hypotheses**: `W` is an elliptic curve over a field `F` with `DecidableEq`.
- **Uses from project**: `kappaDivisor`, `projectiveDivisorSum`, `SmoothPlaneCurve.ProjLinearlyEquiv`
- **Used by**: `h_inj_of_divZeroReduce`, `h_van_degZero_of_divZeroReduce_and_pointMinusO`, `AFInputs` (as field), `AFInputs.h_inj`, `AFInputs.h_van_degZero`
- **Visibility**: public
- **Lines**: 40–43 (def only)
- **Notes**: docstring notes this requires Miller + Finsupp-to-list bridge (both outstanding tickets).

---

### `def PointMinusOPrincipalEqZero`

- **Type**: `(W : Affine F) [W.IsElliptic] → Prop`
  `∀ P : W.Point, ProjIsPrincipal C (kappaDivisor W P) → P = 0`
- **What**: States that if the divisor `(P) − (O)` is principal, then `P` is the identity. This is the "point-minus-O" property needed to close the injectivity argument.
- **How**: Pure `Prop` definition; no proof body.
- **Hypotheses**: `W` an elliptic curve.
- **Uses from project**: `kappaDivisor`, `SmoothPlaneCurve.ProjIsPrincipal`
- **Used by**: `h_van_degZero_of_divZeroReduce_and_pointMinusO`, `AFInputs.pointMinusO`, `AFInputs.h_van_degZero`
- **Visibility**: public
- **Lines**: 49–53 (def only)
- **Notes**: docstring references `point_minus_O_principal_eq_zero_of_coord` (PoleOrderParity) + no-finite-poles bridge as the required proof route.

---

### `theorem h_inj_of_divZeroReduce`

- **Type**:
  ```
  (h_reduce : DivZeroReduce W)
  (h_van : ∀ D, D ∈ projPrincipalSubgroup → projectiveDivisorSum W D = 0)
  (D : SmoothPlaneCurve.PicProj₀ C) →
  picZeroOfPoint W (picZeroSumOfWitness W h_van D) = D
  ```
- **What**: Proves the `h_inj` witness: the composition `κ ∘ σ̄ = id` on `Pic⁰`. Given divisor reduction, each class `D` satisfies `picZeroOfPoint W (σ̄ D) = D`.
- **How**: Induction on the quotient group via `QuotientAddGroup.induction_on`; unfolds `picZeroSumOfWitness_apply_mk`; converts the goal to a membership in `projPrincipalSubgroup` using `Quot.sound` + `QuotientAddGroup.leftRel_apply`; the algebraic identity `−κ(σD) + D = D − κ(σD)` is resolved by `abel`; then `h_reduce D` supplies membership directly.
- **Hypotheses**: `DivZeroReduce W` (divisor reduction); `h_van` (vanishing on principals, a separate hypothesis).
- **Uses from project**: `picZeroOfPoint`, `HasseWeil.EC.Isogeny.picZeroSumOfWitness`, `HasseWeil.EC.Isogeny.picZeroSumOfWitness_apply_mk`, `kappaDivisor`, `projectiveDivisorSum`
- **Used by**: `AFInputs.h_inj`, `AddHomProperty_of_AFInputs`
- **Visibility**: public
- **Lines**: 62–83 (proof ~14 lines)
- **Notes**: None.

---

### `theorem h_van_degZero_of_divZeroReduce_and_pointMinusO`

- **Type**:
  ```
  (h_reduce : DivZeroReduce W) (h_pmO : PointMinusOPrincipalEqZero W)
  (D : ProjectiveDivisor.degZero C)
  (hD : D.val ∈ projPrincipalSubgroup) →
  projectiveDivisorSum W D.val = 0
  ```
- **What**: Proves the `h_van` witness for degree-zero divisors: if `D` is principal and lies in `Div⁰`, then `σD = 0`. The argument is: `D ~ κ(σD)` by reduction; both `D` and `D − κ(σD)` are principal, so `κ(σD)` is principal; then point-minus-O gives `σD = 0`.
- **How**: `h_reduce D` gives `D − κ(σD) ∈ projPrincipalSubgroup`; the identity `κ(σD) = D − (D − κ(σD))` (by `abel`) plus `sub_mem hD h_diff_principal` gives `κ(σD)` principal; then `h_pmO` concludes.
- **Hypotheses**: `DivZeroReduce W`, `PointMinusOPrincipalEqZero W`, `D` principal.
- **Uses from project**: `kappaDivisor`, `projectiveDivisorSum`, `DivZeroReduce`, `PointMinusOPrincipalEqZero`
- **Used by**: `AFInputs.h_van_degZero`
- **Visibility**: public
- **Lines**: 92–116 (proof ~19 lines)
- **Notes**: None.

---

### `def NoFinitePolesBridge`

- **Type**: `(W : Affine F) [W.IsElliptic] → Prop`
  `∀ f : FunctionField C, f ≠ 0 → (∀ P : SmoothPoint C, 0 ≤ ord_P P f) → ∃ u : CoordinateRing C, algebraMap _ _ u = f`
- **What**: States that any nonzero function with all local orders nonneg (no finite poles) lies in the image of the coordinate ring. This is the algebraic bridge from "no finite poles" to "lies in CR".
- **How**: Pure `Prop` definition.
- **Hypotheses**: `W` an elliptic curve.
- **Uses from project**: `SmoothPlaneCurve.ord_P`, `SmoothPlaneCurve.FunctionField`, `SmoothPlaneCurve.CoordinateRing`
- **Used by**: `pointMinusO_of_bridge`, `AFInputs` (as field), `AFInputs.pointMinusO`
- **Visibility**: public
- **Lines**: 125–131 (def only)
- **Notes**: docstring notes this is an ~80–150 LOC follow-up ticket; references `pointValuation_algebraMap_le_one`, `smoothPointEquivMaxIdeal`, `mem_coordinateRing_of_valuation_le_one` as the route.

---

### `theorem pointMinusO_of_bridge`

- **Type**:
  ```
  (h_bridge : NoFinitePolesBridge W) → PointMinusOPrincipalEqZero W
  ```
- **What**: Derives `PointMinusOPrincipalEqZero W` from the no-finite-poles bridge. If `(P) − (O)` is principal, extracts the witness function `f`, shows it has no finite poles (via casework on `kappaDivisor` Finsupp values), then applies `point_minus_O_principal_eq_zero_of_coord`.
- **How**: Unfolds `kappaDivisor` as `Finsupp.single P.toProj 1 − Finsupp.single ∞ 1`; uses `Finsupp.sub_apply` + `Finsupp.single_apply` to evaluate at `affine Q`; the `∞ ≠ affine Q` fact is closed by `nomatch`; case-splits on equality of `P.toProj` and `affine Q` and on `WithTop` values of `ord_P Q f`; applies `SmoothPlaneCurve.ord_P_eq_top_iff` for the `f = 0` contradiction; delegates to `point_minus_O_principal_eq_zero_of_coord`.
- **Hypotheses**: `NoFinitePolesBridge W`.
- **Uses from project**: `point_minus_O_principal_eq_zero_of_coord`, `kappaDivisor`, `SmoothPlaneCurve.projectiveDivisorOf_apply_affine`, `SmoothPlaneCurve.ord_P_eq_top_iff`
- **Used by**: `AFInputs.pointMinusO`
- **Visibility**: public
- **Lines**: 138–193 (proof ~50 lines)
- **Notes**: Proof is >30 lines (50 lines). No sorry. Substantial case analysis on `WithTop ℤ` values.

---

### `structure AFInputs`

- **Type**: `(W : Affine F) [W.IsElliptic] → Type`
  Fields: `miller : MillerHypothesis W`, `divZeroReduce : DivZeroReduce W`, `noFinitePolesBridge : NoFinitePolesBridge W`
- **What**: Bundles the three outstanding hypotheses — Miller's geometric chord/tangent identity, the divisor reduction `DivZeroReduce`, and the no-finite-poles bridge `NoFinitePolesBridge` — needed to discharge B-4-003 on a single curve.
- **How**: Plain structure definition.
- **Hypotheses**: `W` an elliptic curve.
- **Uses from project**: `MillerHypothesis`, `DivZeroReduce`, `NoFinitePolesBridge`
- **Used by**: `AFInputs.pointMinusO`, `AFInputs.h_inj`, `AFInputs.h_van_degZero`, `AFInputs.h_van`, `AddHomProperty_of_AFInputs`
- **Visibility**: public
- **Lines**: 208–211 (structure declaration)
- **Notes**: `MillerHypothesis` is defined in `EffectiveSumReduce.lean`.

---

### `theorem AFInputs.pointMinusO`

- **Type**:
  ```
  (a : AFInputs W) → PointMinusOPrincipalEqZero W
  ```
- **What**: Convenience wrapper: derives `PointMinusOPrincipalEqZero W` from an `AFInputs` record by applying `pointMinusO_of_bridge` with `a.noFinitePolesBridge`.
- **How**: One-liner delegation to `pointMinusO_of_bridge`.
- **Hypotheses**: `AFInputs W`.
- **Uses from project**: `pointMinusO_of_bridge`, `NoFinitePolesBridge`
- **Used by**: `AFInputs.h_van_degZero`
- **Visibility**: public
- **Lines**: 216–218 (term-mode, 1 line proof)
- **Notes**: None.

---

### `theorem AFInputs.h_inj`

- **Type**:
  ```
  (a : AFInputs W)
  (h_van : ∀ D, D ∈ projPrincipalSubgroup → projectiveDivisorSum W D = 0)
  (D : SmoothPlaneCurve.PicProj₀ C) →
  picZeroOfPoint W (picZeroSumOfWitness W h_van D) = D
  ```
- **What**: Convenience wrapper that derives the `h_inj` witness from `AFInputs` by delegating to `h_inj_of_divZeroReduce` with `a.divZeroReduce`.
- **How**: One-liner delegation.
- **Hypotheses**: `AFInputs W`; `h_van` (vanishing on principals).
- **Uses from project**: `h_inj_of_divZeroReduce`, `DivZeroReduce`, `picZeroOfPoint`, `HasseWeil.EC.Isogeny.picZeroSumOfWitness`
- **Used by**: `AddHomProperty_of_AFInputs`
- **Visibility**: public
- **Lines**: 221–228 (term-mode, 1 line proof)
- **Notes**: None.

---

### `theorem AFInputs.h_van_degZero`

- **Type**:
  ```
  (a : AFInputs W)
  (D : ProjectiveDivisor.degZero C)
  (hD : D.val ∈ projPrincipalSubgroup) →
  projectiveDivisorSum W D.val = 0
  ```
- **What**: Convenience wrapper: derives the `h_van` witness on degree-zero divisors from `AFInputs` by combining `a.divZeroReduce` and `a.pointMinusO`.
- **How**: One-liner delegation to `h_van_degZero_of_divZeroReduce_and_pointMinusO`.
- **Hypotheses**: `AFInputs W`; `D` principal.
- **Uses from project**: `h_van_degZero_of_divZeroReduce_and_pointMinusO`, `DivZeroReduce`, `PointMinusOPrincipalEqZero`
- **Used by**: `AFInputs.h_van`
- **Visibility**: public
- **Lines**: 231–236 (term-mode, 1 line proof)
- **Notes**: None.

---

### `def PrincipalImpliesDegZero`

- **Type**: `(W : Affine F) [W.IsElliptic] → Prop`
  `∀ D : ProjectiveDivisor C, D ∈ projPrincipalSubgroup → D ∈ ProjectiveDivisor.degZero C`
- **What**: States that every principal projective divisor has degree zero. This is worker-K's T-II-3-009 (`projectiveDivisorOf_degree_zero`), carried as a hypothesis here to keep the wrapper conditional.
- **How**: Pure `Prop` definition.
- **Hypotheses**: `W` an elliptic curve.
- **Uses from project**: `SmoothPlaneCurve.projPrincipalSubgroup`, `ProjectiveDivisor.degZero`
- **Used by**: `AFInputs.h_van`, `AddHomProperty_of_AFInputs`
- **Visibility**: public
- **Lines**: 246–249 (def only)
- **Notes**: docstring names the outstanding ticket T-II-3-009 (proved under `[IsAlgClosed F]`).

---

### `theorem AFInputs.h_van`

- **Type**:
  ```
  (a : AFInputs W) (h_pdz : PrincipalImpliesDegZero W)
  (D : ProjectiveDivisor C)
  (hD : D ∈ projPrincipalSubgroup) →
  projectiveDivisorSum W D = 0
  ```
- **What**: Full `h_van` witness (not restricted to `degZero` subtype): lifts `h_van_degZero` to arbitrary principal divisors using `PrincipalImpliesDegZero` to construct the `degZero` subtype element.
- **How**: Applies `h_pdz D hD` to get the degZero membership, constructs the subtype `⟨D, h_dz⟩`, then delegates to `a.h_van_degZero`.
- **Hypotheses**: `AFInputs W`; `PrincipalImpliesDegZero W`; `D` principal.
- **Uses from project**: `PrincipalImpliesDegZero`, `AFInputs.h_van_degZero`, `projectiveDivisorSum`
- **Used by**: `AddHomProperty_of_AFInputs`
- **Visibility**: public
- **Lines**: 255–263 (proof ~5 lines)
- **Notes**: None.

---

### `theorem AddHomProperty_of_AFInputs`

- **Type**:
  ```
  (φ : HasseWeil.EC.Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom)
  (a₁ : AFInputs W₁) (a₂ : AFInputs W₂)
  (h_pdz₁ : PrincipalImpliesDegZero W₁)
  (h_pdz₂ : PrincipalImpliesDegZero W₂)
  (h_pres : pushforwardProjectiveDivisor φ cd preserves principal subgroup) →
  φ.AddHomProperty cd
  ```
- **What**: The final conditional B-4-003 theorem: given `AFInputs` for both curves, the principal-degZero bridges, and the pushforward-preserves-principal hypothesis (T-PIC-C-003), the isogeny satisfies the add-hom property.
- **How**: Delegates entirely to `HasseWeil.EC.Isogeny.AddHomProperty_of_picZero_witnesses`, supplying `a₁.h_van h_pdz₁`, `a₂.h_van h_pdz₂`, `h_pres`, and `a₁.h_inj (a₁.h_van h_pdz₁)`.
- **Hypotheses**: `AFInputs` for both curves; `PrincipalImpliesDegZero` for both; pushforward-preserves-principal (T-PIC-C-003).
- **Uses from project**: `HasseWeil.EC.Isogeny.AddHomProperty_of_picZero_witnesses`, `AFInputs.h_van`, `AFInputs.h_inj`, `PrincipalImpliesDegZero`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 281–296 (proof ~2 lines)
- **Notes**: The main exported theorem of the file. All outstanding proof obligations are explicit hypotheses.

---

## Summary

- **Total declarations**: 13
- **Defs** (including structure): 5 (`DivZeroReduce`, `PointMinusOPrincipalEqZero`, `NoFinitePolesBridge`, `AFInputs`, `PrincipalImpliesDegZero`)
- **Theorems/lemmas**: 8 (`h_inj_of_divZeroReduce`, `h_van_degZero_of_divZeroReduce_and_pointMinusO`, `pointMinusO_of_bridge`, `AFInputs.pointMinusO`, `AFInputs.h_inj`, `AFInputs.h_van_degZero`, `AFInputs.h_van`, `AddHomProperty_of_AFInputs`)
- **Instances**: 0
- **Sorries**: none
- **maxHeartbeats**: none
- **Long proofs (>30 lines)**: `pointMinusO_of_bridge` (~50 lines)
- **Key API** (used by 3+ declarations in file): `DivZeroReduce` (5), `kappaDivisor` (3+), `projectiveDivisorSum` (3+), `PointMinusOPrincipalEqZero` (3), `NoFinitePolesBridge` (3)
- **Unused in file**: `AddHomProperty_of_AFInputs` (the top-level theorem; not called within this file, intended for external use)

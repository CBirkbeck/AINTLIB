# Inventory: ./HasseWeil/Curves/CurveMap.lean

**File**: `HasseWeil/Curves/CurveMap.lean`
**Lines**: 447
**Summary**: Defines `CurveMap` (smooth plane curve maps via function-field pullback), `degree`, separable/inseparable degree, ramification index (two flavours), `IsUnramifiedAt`, pushforward (norm map), `CoordHom` witness structure, and Silverman II.2.6(a)/II.2.7 combinatorial results. No sorries.

---

## Declarations

---

### `structure CurveMap`

- **Type**: `{F : Type*} [Field F] (C₁ C₂ : SmoothPlaneCurve F) : Type*` — one field: `pullback : C₂.FunctionField →ₐ[F] C₁.FunctionField`
- **What**: A curve map from `C₁` to `C₂` defined purely by its pullback on function fields; the structure models nonconstant maps (Silverman II.2.4(b)).
- **How**: Pure data structure; injectivity of the pullback is automatic (F-algebra hom between fields).
- **Hypotheses**: `F` a field, `C₁ C₂` smooth plane curves over `F`.
- **Uses from project**: `SmoothPlaneCurve.FunctionField`
- **Used by**: Every declaration in the file.
- **Visibility**: public
- **Lines**: 38–41 (structure body 2 lines)
- **Notes**: None.

---

### `theorem pullback_injective`

- **Type**: `(φ : CurveMap C₁ C₂) : Function.Injective φ.pullback`
- **What**: The pullback of any curve map is injective (as any F-algebra homomorphism between fields).
- **How**: One-liner via `φ.pullback.toRingHom.injective` — ring hom between fields is injective by Mathlib's `RingHom.injective`.
- **Hypotheses**: None beyond the curve map.
- **Uses from project**: `CurveMap`
- **Used by**: `ramificationIndex_ne_top`, `pullback_ne_zero`, `pullback_surjective_of_degree_one` (indirectly)
- **Visibility**: public
- **Lines**: 48–50 (proof 1 line)
- **Notes**: None.

---

### `noncomputable def id`

- **Type**: `(C : SmoothPlaneCurve F) : CurveMap C C`
- **What**: The identity curve map, whose pullback is the identity algebra homomorphism.
- **How**: Direct construction: `pullback := AlgHom.id F C.FunctionField`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap`, `SmoothPlaneCurve.FunctionField`
- **Used by**: `id_pullback`, `degree_id`, `id_comp`, `comp_id`, `ramificationIndex_id`, `ramificationIndexℤ_id`, `id_isUnramifiedAt`
- **Visibility**: public
- **Lines**: 53–55 (body 2 lines)
- **Notes**: None.

---

### `theorem id_pullback`

- **Type**: `(C : SmoothPlaneCurve F) : (id C).pullback = AlgHom.id F C.FunctionField`
- **What**: Simp lemma: the pullback of the identity map is `AlgHom.id`.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.id`
- **Used by**: unused in file (simp lemma for external use)
- **Visibility**: public
- **Lines**: 56–57 (proof 1 line)
- **Notes**: `@[simp]`.

---

### `noncomputable def comp`

- **Type**: `(ψ : CurveMap C₂ C₃) (φ : CurveMap C₁ C₂) : CurveMap C₁ C₃`
- **What**: Composition of curve maps; pullback is `φ.pullback ∘ ψ.pullback` (contravariant).
- **How**: Direct construction: `pullback := φ.pullback.comp ψ.pullback`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap`
- **Used by**: `comp_pullback`, `comp_assoc`, `id_comp`, `comp_id`, `degree_comp`, `ramificationIndex_comp`, `ramificationIndexℤ_comp`, `comp_algebraMap_eq`
- **Visibility**: public
- **Lines**: 60–62 (body 2 lines)
- **Notes**: None.

---

### `theorem comp_pullback`

- **Type**: `(ψ : CurveMap C₂ C₃) (φ : CurveMap C₁ C₂) : (ψ.comp φ).pullback = φ.pullback.comp ψ.pullback`
- **What**: Simp lemma: the pullback of a composition is the composition of pullbacks.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.comp`
- **Used by**: unused in file (simp lemma for external use)
- **Visibility**: public
- **Lines**: 63–64 (proof 1 line)
- **Notes**: `@[simp]`.

---

### `theorem ext`

- **Type**: `{φ ψ : CurveMap C₁ C₂} (h : φ.pullback = ψ.pullback) : φ = ψ`
- **What**: Extensionality for curve maps: equality is determined by equality of pullbacks.
- **How**: Pattern match via `cases φ; cases ψ; congr`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap`
- **Used by**: `comp_assoc`, `id_comp`, `comp_id`
- **Visibility**: public
- **Lines**: 67–70 (proof 2 lines)
- **Notes**: `@[ext]`.

---

### `theorem comp_assoc`

- **Type**: `(χ : CurveMap C₃ C₄) (ψ : CurveMap C₂ C₃) (φ : CurveMap C₁ C₂) : (χ.comp ψ).comp φ = χ.comp (ψ.comp φ)`
- **What**: Composition of curve maps is associative.
- **How**: Applies `CurveMap.ext` and uses `AlgHom.comp_assoc` from Mathlib.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.ext`, `CurveMap.comp`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 72–75 (proof 1 line)
- **Notes**: None.

---

### `theorem id_comp`

- **Type**: `(φ : CurveMap C₁ C₂) : (id C₂).comp φ = φ`
- **What**: Left identity: composing with the identity on the right curve gives the original map.
- **How**: `CurveMap.ext` and `AlgHom.comp_id`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.ext`, `CurveMap.comp`, `CurveMap.id`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 78–79 (proof 1 line)
- **Notes**: `@[simp]`.

---

### `theorem comp_id`

- **Type**: `(φ : CurveMap C₁ C₂) : φ.comp (id C₁) = φ`
- **What**: Right identity: composing with the identity on the left curve gives the original map.
- **How**: `CurveMap.ext` and `AlgHom.id_comp`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.ext`, `CurveMap.comp`, `CurveMap.id`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 82–83 (proof 1 line)
- **Notes**: `@[simp]`.

---

### `noncomputable def toAlgebra`

- **Type**: `(φ : CurveMap C₁ C₂) : Algebra C₂.FunctionField C₁.FunctionField`
- **What**: The algebra structure on `K(C₁)` over `K(C₂)` induced by the pullback of `φ`.
- **How**: `φ.pullback.toRingHom.toAlgebra`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap`
- **Used by**: `degree`, `separableDegree`, `pushforward`, `degree_id`, `degree_comp`, `pushforward_pullback`, `pullback_surjective_of_degree_one`, `sum_ramificationIdx_mul_inertiaDeg_eq_degree`
- **Visibility**: public (`@[reducible]`)
- **Lines**: 89–91 (body 1 line)
- **Notes**: `@[reducible]` so instances synthesized from it are transparent.

---

### `noncomputable def degree`

- **Type**: `(φ : CurveMap C₁ C₂) : ℕ`
- **What**: The degree of a curve map `φ`, defined as `[K(C₁) : φ*K(C₂)]` — the finrank of `K(C₁)` as a `K(C₂)`-module via `toAlgebra`.
- **How**: `@Module.finrank C₂.FunctionField C₁.FunctionField _ _ φ.toAlgebra.toModule`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.toAlgebra`
- **Used by**: `degree_id`, `degree_comp`, `inseparableDegree`, `pushforward_pullback`, `fiber_card_eq_degree_iff_all_ramificationIndexℤ_one`, `pullback_surjective_of_degree_one`, `sum_ramificationIdx_mul_inertiaDeg_eq_degree`
- **Visibility**: public
- **Lines**: 96–97 (body 1 line)
- **Notes**: Key API — used by 7+ declarations.

---

### `theorem degree_id`

- **Type**: `(C : SmoothPlaneCurve F) : (id C).degree = 1`
- **What**: The identity map has degree 1.
- **How**: Uses `Module.finrank_self` after unfolding `degree` and `toAlgebra`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.id`, `CurveMap.degree`, `CurveMap.toAlgebra`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 100–103 (proof 3 lines)
- **Notes**: `@[simp]`.

---

### `theorem comp_algebraMap_eq`

- **Type**: `(ψ : CurveMap C₂ C₃) (φ : CurveMap C₁ C₂) (x : C₃.FunctionField) : (ψ.comp φ).pullback x = φ.pullback (ψ.pullback x)`
- **What**: The pullback of a composition evaluates as the composition of pullbacks pointwise.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.comp`
- **Used by**: `degree_comp` (inline proof of `IsScalarTower`)
- **Visibility**: public
- **Lines**: 106–108 (proof 1 line)
- **Notes**: Helper for the scalar-tower instance in `degree_comp`.

---

### `theorem degree_comp`

- **Type**: `(ψ : CurveMap C₂ C₃) (φ : CurveMap C₁ C₂) : (ψ.comp φ).degree = φ.degree * ψ.degree`
- **What**: Degree is multiplicative under composition: `deg(ψ∘φ) = deg(φ)·deg(ψ)`.
- **How**: Sets up three algebra instances and a scalar-tower `C₃.FF →ₐ C₂.FF →ₐ C₁.FF`, declares `Module.Free` (as division ring), then applies Mathlib's `Module.finrank_mul_finrank` (tower law).
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.degree`, `CurveMap.toAlgebra`, `CurveMap.comp`, `comp_algebraMap_eq` (inline rfl)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 115–129 (proof 14 lines)
- **Notes**: `set_option maxHeartbeats 800000` with comment "The tower law for `FunctionField` needs extra heartbeats."

---

### `noncomputable def separableDegree`

- **Type**: `(φ : CurveMap C₁ C₂) : ℕ`
- **What**: The separable degree of `φ`, defined as `Field.finSepDegree C₂.FF C₁.FF` via `φ.toAlgebra`.
- **How**: `@Field.finSepDegree C₂.FunctionField C₁.FunctionField _ _ φ.toAlgebra`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.toAlgebra`
- **Used by**: `inseparableDegree`, `IsPurelyInseparable`
- **Visibility**: public
- **Lines**: 134–135 (body 1 line)
- **Notes**: None.

---

### `noncomputable def inseparableDegree`

- **Type**: `(φ : CurveMap C₁ C₂) : ℕ`
- **What**: The inseparable degree of `φ`, defined as `degree φ / separableDegree φ`.
- **How**: Direct: `φ.degree / φ.separableDegree`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.degree`, `CurveMap.separableDegree`
- **Used by**: `IsSeparable`
- **Visibility**: public
- **Lines**: 139–140 (body 1 line)
- **Notes**: None.

---

### `def IsSeparable`

- **Type**: `(φ : CurveMap C₁ C₂) : Prop`
- **What**: Predicate: a curve map is separable if its inseparable degree equals 1.
- **How**: `φ.inseparableDegree = 1`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.inseparableDegree`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 143 (body 1 line)
- **Notes**: Unused in this file — dead-code candidate locally (likely used by other files).

---

### `def IsPurelyInseparable`

- **Type**: `(φ : CurveMap C₁ C₂) : Prop`
- **What**: Predicate: a curve map is purely inseparable if its separable degree equals 1.
- **How**: `φ.separableDegree = 1`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.separableDegree`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 146 (body 1 line)
- **Notes**: Unused in this file — dead-code candidate locally (likely used by other files).

---

### `noncomputable def ramificationIndex`

- **Type**: `(φ : CurveMap C₁ C₂) (P : C₁.SmoothPoint) (t : C₂.FunctionField) : WithTop ℤ`
- **What**: The ramification index of `φ` at `P` with test function `t`: `ord_P(φ*(t))`.
- **How**: `C₁.ord_P P (φ.pullback t)` — direct application of the project's `ord_P`.
- **Hypotheses**: None.
- **Uses from project**: `SmoothPlaneCurve.ord_P`, `CurveMap.pullback`
- **Used by**: `ramificationIndex_id`, `ramificationIndex_comp`, `ramificationIndex_ne_top`, `ramificationIndexℤ`, `IsUnramifiedAt`, `isUnramifiedAt_iff_uniformizer_pullback`, `one_le_ramificationIndex_of_pullback_pointValuation_lt_one`
- **Visibility**: public
- **Lines**: 170–172 (body 1 line)
- **Notes**: Key API — used by 7+ declarations.

---

### `theorem ramificationIndex_id`

- **Type**: `(C : SmoothPlaneCurve F) (P : C.SmoothPoint) (t : C.FunctionField) : (id C).ramificationIndex P t = C.ord_P P t`
- **What**: Ramification index of the identity reduces to `ord_P`.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.id`, `CurveMap.ramificationIndex`, `SmoothPlaneCurve.ord_P`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 175–177 (proof 1 line)
- **Notes**: `@[simp]`.

---

### `theorem ramificationIndex_comp`

- **Type**: `(ψ : CurveMap C₂ C₃) (φ : CurveMap C₁ C₂) (P : C₁.SmoothPoint) (t : C₃.FunctionField) : (ψ.comp φ).ramificationIndex P t = φ.ramificationIndex P (ψ.pullback t)`
- **What**: Chain rule for ramification index: `ord_P((ψ∘φ)*(t)) = ord_P(φ*(ψ*(t)))`.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.comp`, `CurveMap.ramificationIndex`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 182–185 (proof 1 line)
- **Notes**: None.

---

### `theorem ramificationIndex_ne_top`

- **Type**: `(φ : CurveMap C₁ C₂) (P : C₁.SmoothPoint) {t : C₂.FunctionField} (ht : t ≠ 0) : φ.ramificationIndex P t ≠ ⊤`
- **What**: The ramification index of a nonzero function is never `⊤` (i.e., `φ*(t) ≠ 0` in `K(C₁)`).
- **How**: Uses `SmoothPlaneCurve.ord_P_eq_top_iff` and `pullback_injective` to reduce `φ*(t) = 0` to `t = 0`.
- **Hypotheses**: `t ≠ 0`.
- **Uses from project**: `CurveMap.ramificationIndex`, `SmoothPlaneCurve.ord_P_eq_top_iff`, `CurveMap.pullback_injective`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 189–193 (proof 2 lines)
- **Notes**: None.

---

### `theorem pullback_ne_zero`

- **Type**: `(φ : CurveMap C₁ C₂) {t : C₂.FunctionField} (ht : t ≠ 0) : φ.pullback t ≠ 0`
- **What**: Pullback preserves nonzeroness.
- **How**: Injectivity of `φ.pullback` and `map_zero`.
- **Hypotheses**: `t ≠ 0`.
- **Uses from project**: `CurveMap.pullback_injective`
- **Used by**: `one_le_ramificationIndex_of_pullback_pointValuation_lt_one`
- **Visibility**: public
- **Lines**: 196–198 (proof 1 line)
- **Notes**: None.

---

### `noncomputable def ramificationIndexℤ`

- **Type**: `(φ : CurveMap C₁ C₂) (P : C₁.SmoothPoint) (t : C₂.FunctionField) : ℤ`
- **What**: Integer-valued ramification index, obtained from the `WithTop ℤ`-valued one by `untopD 0`.
- **How**: `(φ.ramificationIndex P t).untopD 0`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.ramificationIndex`
- **Used by**: `ramificationIndexℤ_id`, `ramificationIndexℤ_comp`, `fiber_card_eq_degree_iff_all_ramificationIndexℤ_one`
- **Visibility**: public
- **Lines**: 202–204 (body 1 line)
- **Notes**: None.

---

### `theorem ramificationIndexℤ_id`

- **Type**: `(C : SmoothPlaneCurve F) (P : C.SmoothPoint) (t : C.FunctionField) : (id C).ramificationIndexℤ P t = (C.ord_P P t).untopD 0`
- **What**: Integer ramification index of the identity is `(ord_P t).untopD 0`.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.id`, `CurveMap.ramificationIndexℤ`, `SmoothPlaneCurve.ord_P`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 207–209 (proof 1 line)
- **Notes**: `@[simp]`.

---

### `theorem ramificationIndexℤ_comp`

- **Type**: `(ψ : CurveMap C₂ C₃) (φ : CurveMap C₁ C₂) (P : C₁.SmoothPoint) (t : C₃.FunctionField) : (ψ.comp φ).ramificationIndexℤ P t = φ.ramificationIndexℤ P (ψ.pullback t)`
- **What**: Chain rule for the integer ramification index.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.comp`, `CurveMap.ramificationIndexℤ`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 213–216 (proof 1 line)
- **Notes**: `@[simp]`.

---

### `def IsUnramifiedAt`

- **Type**: `(φ : CurveMap C₁ C₂) (P : C₁.SmoothPoint) (t : C₂.FunctionField) : Prop`
- **What**: Predicate: `φ` is unramified at `P` (with test function `t`) iff `φ.ramificationIndex P t = 1`.
- **How**: `φ.ramificationIndex P t = 1`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.ramificationIndex`
- **Used by**: `isUnramifiedAt_iff_uniformizer_pullback`, `id_isUnramifiedAt`, `fiber_card_eq_degree_iff_all_ramificationIndexℤ_one` (docstring mention)
- **Visibility**: public
- **Lines**: 223–225 (body 1 line)
- **Notes**: None.

---

### `theorem isUnramifiedAt_iff_uniformizer_pullback`

- **Type**: `(φ : CurveMap C₁ C₂) (P : C₁.SmoothPoint) (t : C₂.FunctionField) : φ.IsUnramifiedAt P t ↔ SmoothPlaneCurve.Uniformizer C₁ P (φ.pullback t)`
- **What**: Being unramified at `P` is equivalent to `φ*(t)` being a uniformizer at `P`.
- **How**: `Iff.rfl` — the two definitions are definitionally equal.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.IsUnramifiedAt`, `SmoothPlaneCurve.Uniformizer`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 227–230 (proof 1 line)
- **Notes**: None.

---

### `theorem id_isUnramifiedAt`

- **Type**: `(C : SmoothPlaneCurve F) (P : C.SmoothPoint) {t : C.FunctionField} (ht : SmoothPlaneCurve.Uniformizer C P t) : (id C).IsUnramifiedAt P t`
- **What**: The identity map is unramified at every point tested with a uniformizer there.
- **How**: `ht` directly; `ramificationIndex_id` makes this `rfl`.
- **Hypotheses**: `t` is a uniformizer of `C` at `P`.
- **Uses from project**: `CurveMap.id`, `CurveMap.IsUnramifiedAt`, `SmoothPlaneCurve.Uniformizer`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 234–236 (proof 1 line)
- **Notes**: None.

---

### `theorem one_le_ramificationIndex_of_pullback_pointValuation_lt_one`

- **Type**: `(φ : CurveMap C₁ C₂) (P : C₁.SmoothPoint) {t : C₂.FunctionField} (ht : t ≠ 0) (h : C₁.pointValuation P (φ.pullback t) < 1) : (1 : WithTop ℤ) ≤ φ.ramificationIndex P t`
- **What**: If the pullback of `t` lies in the maximal ideal at `P` (pointValuation < 1), then the ramification index is ≥ 1.
- **How**: Applies `SmoothPlaneCurve.one_le_ord_P_iff_pointValuation_lt_one` and `pullback_ne_zero`.
- **Hypotheses**: `t ≠ 0`, `pointValuation P (φ.pullback t) < 1`.
- **Uses from project**: `CurveMap.ramificationIndex`, `SmoothPlaneCurve.one_le_ord_P_iff_pointValuation_lt_one`, `CurveMap.pullback_ne_zero`
- **Used by**: unused in file (mentioned in docstring of `fiber_card_eq_degree_iff_all_ramificationIndexℤ_one`)
- **Visibility**: public
- **Lines**: 244–248 (proof 1 line)
- **Notes**: None.

---

### `noncomputable def pushforward`

- **Type**: `(φ : CurveMap C₁ C₂) : C₁.FunctionField →* C₂.FunctionField`
- **What**: The pushforward (norm map) `φ_* : K(C₁) →* K(C₂)`, defined as the `K(C₂)`-algebra norm via `φ.toAlgebra`.
- **How**: `@Algebra.norm C₂.FunctionField C₁.FunctionField _ _ φ.toAlgebra`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.toAlgebra`
- **Used by**: `pushforward_pullback`, `pushforward_mul`, `pushforward_one`
- **Visibility**: public
- **Lines**: 257–259 (body 1 line)
- **Notes**: None.

---

### `theorem pushforward_pullback`

- **Type**: `(φ : CurveMap C₁ C₂) (g : C₂.FunctionField) : φ.pushforward (φ.pullback g) = g ^ φ.degree`
- **What**: `φ_*(φ*(g)) = g^(deg φ)` — the norm of a pullback element equals a power.
- **How**: Applies `Algebra.norm_algebraMap` after setting up `letI : Algebra ... := φ.toAlgebra`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.pushforward`, `CurveMap.degree`, `CurveMap.toAlgebra`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 264–267 (proof 2 lines)
- **Notes**: None.

---

### `theorem pushforward_mul`

- **Type**: `(φ : CurveMap C₁ C₂) (f g : C₁.FunctionField) : φ.pushforward (f * g) = φ.pushforward f * φ.pushforward g`
- **What**: Pushforward is multiplicative.
- **How**: `φ.pushforward.map_mul f g`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.pushforward`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 270–272 (proof 1 line)
- **Notes**: `@[simp]`.

---

### `theorem pushforward_one`

- **Type**: `(φ : CurveMap C₁ C₂) : φ.pushforward (1 : C₁.FunctionField) = 1`
- **What**: Pushforward sends 1 to 1.
- **How**: `φ.pushforward.map_one`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.pushforward`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 275–277 (proof 1 line)
- **Notes**: `@[simp]`.

---

### `theorem _root_.Finset.sum_eq_card_iff_forall_eq_one_of_one_le`

- **Type**: `{α : Type*} {S : Finset α} {e : α → ℤ} (hle : ∀ P ∈ S, 1 ≤ e P) : ∑ P ∈ S, e P = (S.card : ℤ) ↔ ∀ P ∈ S, e P = 1`
- **What**: Combinatorial lemma: if `e ≥ 1` pointwise on `S`, then the sum equals `#S` iff every value is exactly 1.
- **How**: Reduces to showing `Σ(e P − 1) = 0` and applying `Finset.sum_eq_zero_iff_of_nonneg` (Mathlib), then `linarith`.
- **Hypotheses**: `1 ≤ e P` for all `P ∈ S`.
- **Uses from project**: (none — pure combinatorics in `_root_` namespace)
- **Used by**: `fiber_card_eq_degree_iff_all_ramificationIndexℤ_one`
- **Visibility**: public (placed in `_root_` namespace)
- **Lines**: 295–310 (proof 13 lines)
- **Notes**: Placed in `_root_.Finset` namespace, slightly unusual. May have Mathlib overlap.

---

### `theorem fiber_card_eq_degree_iff_all_ramificationIndexℤ_one`

- **Type**: `(φ : CurveMap C₁ C₂) (t : C₂.FunctionField) (S : Finset C₁.SmoothPoint) (hle : ∀ P ∈ S, 1 ≤ φ.ramificationIndexℤ P t) (hsum : ∑ P ∈ S, φ.ramificationIndexℤ P t = (φ.degree : ℤ)) : (S.card : ℤ) = (φ.degree : ℤ) ↔ ∀ P ∈ S, φ.ramificationIndexℤ P t = 1`
- **What**: Witness-parametric Silverman II.2.7: given that ramification indices sum to `deg(φ)`, the fiber size equals `deg(φ)` iff every index is 1.
- **How**: Rewrites using `hsum` and `eq_comm`, then applies `Finset.sum_eq_card_iff_forall_eq_one_of_one_le`.
- **Hypotheses**: Indices ≥ 1 on `S`; sum equals `deg(φ)` (Silverman II.2.6(a) supplied as hypothesis).
- **Uses from project**: `CurveMap.ramificationIndexℤ`, `CurveMap.degree`, `Finset.sum_eq_card_iff_forall_eq_one_of_one_le`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 325–333 (proof 3 lines)
- **Notes**: None.

---

### `theorem pullback_surjective_of_degree_one`

- **Type**: `(φ : CurveMap C₁ C₂) (h : φ.degree = 1) : Function.Surjective φ.pullback`
- **What**: If a curve map has degree 1, its pullback is surjective (Silverman II.2.4.1).
- **How**: Uses `finrank_eq_one_iff'` to get a basis vector `v`, constructs an inverse via `c / c₀` (finding `c₀` from `hv 1`), then verifies `algebraMap ... (c / c₀) = w` via `map_div₀` and `eq_inv_of_mul_eq_one_right`.
- **Hypotheses**: `φ.degree = 1`.
- **Uses from project**: `CurveMap.degree`, `CurveMap.toAlgebra`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 340–360 (proof 20 lines)
- **Notes**: None.

---

### `structure CoordHom`

- **Type**: `(φ : CurveMap C₁ C₂) : Type*` — fields: `toAlgHom : C₂.CoordinateRing →ₐ[F] C₁.CoordinateRing`, `compat : ∀ u, φ.pullback (algebraMap ... u) = algebraMap ... (toAlgHom u)`
- **What**: Auxiliary data: a coordinate-ring algebra hom compatible with the function-field pullback. Needed because not every function-field pullback restricts to coordinate rings.
- **How**: Data structure with a compatibility condition.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap`, `SmoothPlaneCurve.CoordinateRing`, `SmoothPlaneCurve.FunctionField`
- **Used by**: `CoordHom.toAlgebra`, `sum_ramificationIdx_mul_inertiaDeg_eq_degree`
- **Visibility**: public
- **Lines**: 378–386 (body 8 lines)
- **Notes**: None.

---

### `noncomputable def CoordHom.toAlgebra`

- **Type**: `{φ : CurveMap C₁ C₂} (coordHom : φ.CoordHom) : Algebra C₂.CoordinateRing C₁.CoordinateRing`
- **What**: The algebra structure on `C₁.CoordinateRing` over `C₂.CoordinateRing` induced by a `CoordHom`.
- **How**: `coordHom.toAlgHom.toRingHom.toAlgebra`.
- **Hypotheses**: None.
- **Uses from project**: `CurveMap.CoordHom`
- **Used by**: `sum_ramificationIdx_mul_inertiaDeg_eq_degree`
- **Visibility**: public (`@[reducible]`)
- **Lines**: 391–393 (body 1 line)
- **Notes**: `@[reducible]`.

---

### `theorem sum_ramificationIdx_mul_inertiaDeg_eq_degree`

- **Type**: `[IsIntegrallyClosed C₂.CoordinateRing] [IsIntegrallyClosed C₁.CoordinateRing] (φ : CurveMap C₁ C₂) (coordHom : φ.CoordHom) (hfin : @Module.Finite C₂.CR C₁.CR _ _ coordHom.toAlgebra.toModule) {p : Ideal C₂.CR} (hpMax : p.IsMaximal) (hp0 : p ≠ ⊥) : ∑ P ∈ primesOverFinset p C₁.CR, ramificationIdx (...) p P * inertiaDeg p P = φ.degree`
- **What**: Silverman II.2.6(a): the sum `Σ_{P over p} e_P · f_P` equals `deg(φ)`. Generic `CurveMap` version requiring a `CoordHom` witness and finite-module condition.
- **How**: Establishes two scalar tower instances (`C₂.CR → C₁.CR → C₁.FF` by inference, `C₂.CR → C₂.FF → C₁.FF` via `IsScalarTower.of_algebraMap_smul` using `coordHom.compat`), then applies Mathlib's `Ideal.sum_ramification_inertia`.
- **Hypotheses**: `C₁.CoordinateRing` and `C₂.CoordinateRing` integrally closed; finite module structure via `coordHom`; `p` maximal, `p ≠ ⊥`.
- **Uses from project**: `CurveMap.degree`, `CurveMap.toAlgebra`, `CurveMap.CoordHom`, `CurveMap.CoordHom.toAlgebra`, `SmoothPlaneCurve.CoordinateRing`, `SmoothPlaneCurve.FunctionField`, `primesOverFinset`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 411–443 (proof 31 lines)
- **Notes**: `set_option synthInstance.maxHeartbeats 200000` and `set_option maxHeartbeats 1600000` (no justifying comment on `synthInstance`, main comment says "tower law for FunctionField"). Proof is 31 lines — barely exceeds threshold. The scalar-tower dance is the key difficulty.

---

## Cross-reference summary

### Key API (used by 3+ other declarations in this file)

- `CurveMap` (the structure): used by virtually all declarations
- `CurveMap.toAlgebra`: used by `degree`, `separableDegree`, `pushforward`, `degree_id`, `degree_comp`, `pushforward_pullback`, `pullback_surjective_of_degree_one`, `sum_ramificationIdx_mul_inertiaDeg_eq_degree`
- `CurveMap.degree`: used by `degree_id`, `degree_comp`, `inseparableDegree`, `pushforward_pullback`, `fiber_card_eq_degree_iff_all_ramificationIndexℤ_one`, `pullback_surjective_of_degree_one`, `sum_ramificationIdx_mul_inertiaDeg_eq_degree`
- `CurveMap.ramificationIndex`: used by `ramificationIndex_id`, `ramificationIndex_comp`, `ramificationIndex_ne_top`, `ramificationIndexℤ`, `IsUnramifiedAt`, `isUnramifiedAt_iff_uniformizer_pullback`, `one_le_ramificationIndex_of_pullback_pointValuation_lt_one`
- `CurveMap.pullback_injective`: used by `ramificationIndex_ne_top`, `pullback_ne_zero`
- `CurveMap.comp`: used by `comp_pullback`, `comp_assoc`, `id_comp`, `comp_id`, `degree_comp`, `ramificationIndex_comp`, `ramificationIndexℤ_comp`, `comp_algebraMap_eq`
- `CurveMap.id`: used by `id_pullback`, `degree_id`, `id_comp`, `comp_id`, `ramificationIndex_id`, `ramificationIndexℤ_id`, `id_isUnramifiedAt`

### Locally unused (dead-code candidates in this file)

The following declarations are not referenced by any other declaration in this file (but may be used by external files):

- `id_pullback`, `comp_pullback`, `comp_assoc`, `id_comp`, `comp_id`, `degree_id`, `degree_comp`, `IsSeparable`, `IsPurelyInseparable`, `ramificationIndex_id`, `ramificationIndex_comp`, `ramificationIndex_ne_top`, `ramificationIndexℤ_id`, `ramificationIndexℤ_comp`, `isUnramifiedAt_iff_uniformizer_pullback`, `id_isUnramifiedAt`, `one_le_ramificationIndex_of_pullback_pointValuation_lt_one`, `pushforward_pullback`, `pushforward_mul`, `pushforward_one`, `fiber_card_eq_degree_iff_all_ramificationIndexℤ_one`, `pullback_surjective_of_degree_one`, `sum_ramificationIdx_mul_inertiaDeg_eq_degree`

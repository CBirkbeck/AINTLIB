# Inventory: ./HasseWeil/Curves/Valuation.lean

File: `HasseWeil/Curves/Valuation.lean`
Total lines: 336
Imports: `HasseWeil.Curves.DVR`, `Mathlib.RingTheory.Valuation.Discrete.Basic`

**Purpose.** Extracts the additive order-of-vanishing valuation `ord_P : F(C) → WithTop ℤ` at a smooth point `P` of a smooth plane curve `C` from the DVR local ring structure (ticket T-II-1-002). Also defines uniformizers (T-II-1-003) and proves basic valuation identities.

---

## Declarations

### `instance maximalIdealAt_isPrime`
- **Type**: `(C : SmoothPlaneCurve F) → (P : C.SmoothPoint) → (C.maximalIdealAt P).IsPrime`
- **What**: Witnesses that the maximal ideal at a smooth point is a prime ideal, enabling `Localization.AtPrime` to work.
- **How**: One-liner: `(C.maximalIdealAt_isMaximal P).isPrime` (every maximal ideal is prime).
- **Hypotheses**: `F` a field; `C` a smooth plane curve; `P` a smooth point.
- **Uses from project**: `C.maximalIdealAt`, `C.maximalIdealAt_isMaximal` (from `HasseWeil.Curves.Basic` / `DVR` dependencies).
- **Used by**: Implicitly by `localRingAt` (as the `IsPrime` instance for `Localization.AtPrime`); not explicitly referenced by name in this file.
- **Visibility**: public
- **Lines**: 36–38, proof length 1
- **Notes**: Instance glue; likely picked up implicitly.

---

### `noncomputable abbrev localRingAt`
- **Type**: `(C : SmoothPlaneCurve F) → (P : C.SmoothPoint) → Type _`  
  equals `Localization.AtPrime (C.maximalIdealAt P)`
- **What**: Defines the local ring of the curve at a smooth point as the localization of the coordinate ring at the maximal ideal of `P`.
- **How**: Pure abbreviation (unfolds to `Localization.AtPrime`).
- **Hypotheses**: None beyond `F` a field.
- **Uses from project**: `C.maximalIdealAt` (project-defined maximal ideal).
- **Used by**: `localRingAt.instIsDVR`, `localRingAt.instIsFractionRing`, `pointValuation`, `exists_uniformizer`.
- **Visibility**: public
- **Lines**: 41–43, proof length 0 (abbrev)
- **Notes**: None.

---

### `noncomputable instance localRingAt.instIsDVR`
- **Type**: `(C : SmoothPlaneCurve F) → (P : C.SmoothPoint) → IsDiscreteValuationRing (C.localRingAt P)`
- **What**: Packages the DVR property of the local ring at a smooth point as a typeclass instance, enabling mathlib's DVR/valuation machinery.
- **How**: Delegates to `C.localRing_isDVR_of_smooth P` from `HasseWeil.Curves.DVR` (T-II-1-001 result).
- **Hypotheses**: `F` a field; `C` smooth plane curve; `P` smooth point.
- **Uses from project**: `localRingAt` (abbrev above), `C.localRing_isDVR_of_smooth` (from `DVR.lean`).
- **Used by**: `pointValuation` (implicitly via `IsDiscreteValuationRing.maximalIdeal`); `exists_uniformizer` (implicitly via `valuation_exists_uniformizer`).
- **Visibility**: public
- **Lines**: 45–48, proof length 1
- **Notes**: Bridge instance from T-II-1-001 to the valuation machinery.

---

### `noncomputable instance localRingAt.instIsFractionRing`
- **Type**: `(C : SmoothPlaneCurve F) → (P : C.SmoothPoint) → IsFractionRing (C.localRingAt P) C.FunctionField`
- **What**: Witnesses that the function field `F(C)` is the fraction field of the local ring at `P`, enabling `HeightOneSpectrum.valuation` to produce a valuation on `C.FunctionField`.
- **How**: `inferInstanceAs` with unfolded types `Localization.AtPrime (C.maximalIdealAt P)` and `FractionRing C.CoordinateRing` (both are localizations of the same ring).
- **Hypotheses**: `F` a field; standard algebra instances.
- **Uses from project**: `localRingAt`, `C.FunctionField`, `C.CoordinateRing`.
- **Used by**: `pointValuation` (implicitly; `HeightOneSpectrum.valuation` needs this instance).
- **Visibility**: public
- **Lines**: 53–58, proof length 3
- **Notes**: Key bridge between the local ring and the global function field; allows the valuation to live on `C.FunctionField`.

---

### `noncomputable def pointValuation`
- **Type**: `(C : SmoothPlaneCurve F) → (P : C.SmoothPoint) → Valuation C.FunctionField (WithZero (Multiplicative ℤ))`
- **What**: The multiplicative `v`-adic valuation on the function field `F(C)` induced by the maximal ideal at `P`, taking values in `ℤᵐ⁰ = WithZero (Multiplicative ℤ)`. This is the standard adic valuation for a DVR / height-one prime.
- **How**: Applies `IsDedekindDomain.HeightOneSpectrum.valuation` to the maximal ideal of `C.localRingAt P` (viewed as a `HeightOneSpectrum` element) extended to the fraction field.
- **Hypotheses**: DVR instance `localRingAt.instIsDVR`; fraction ring instance `localRingAt.instIsFractionRing`.
- **Uses from project**: `localRingAt`, `localRingAt.instIsDVR`, `localRingAt.instIsFractionRing`.
- **Used by**: `ord_P`, `pointValuation_eq_zero_iff`, `ord_P_eq_top_iff`, `one_le_ord_P_iff_pointValuation_lt_one`, `ord_P_mul`, `ord_P_add_le`, `ord_P_inv`, `ord_P_one`, `ord_P_neg`, `exists_uniformizer`.
- **Visibility**: public
- **Lines**: 63–65, proof length 1
- **Notes**: Core definition; everything else in the file uses this.

---

### `noncomputable def ord_P`
- **Type**: `(C : SmoothPlaneCurve F) → (P : C.SmoothPoint) → C.FunctionField → WithTop ℤ`
- **What**: The order-of-vanishing (additive valuation) of a function at a smooth point. Returns `⊤` for the zero function, and `−toAdd(unzero(v(f)))` for nonzero `f`, converting the multiplicative `ℤᵐ⁰` value to additive `WithTop ℤ` with the sign convention `ord_P(uniformizer) = 1`.
- **How**: Direct if-then-else on `pointValuation P f = 0`, using `WithZero.unzero` and `Multiplicative.toAdd` to extract the integer exponent.
- **Hypotheses**: None (works for zero via the `⊤` branch).
- **Uses from project**: `pointValuation`.
- **Used by**: `ord_P_zero`, `ord_P_eq_top_iff`, `ord_P_of_ne`, `one_le_ord_P_iff_pointValuation_lt_one`, `ord_P_mul`, `ord_P_add_le`, `ord_P_inv`, `ord_P_one`, `ord_P_pow`, `ord_P_neg`, `ord_P_add_eq_of_lt`, `ord_P_sub_eq_of_lt`, `Uniformizer.unit_quotient`, `Uniformizer.ne_zero`, `Uniformizer.exists_ord_P_eq`, `exists_uniformizer`.
- **Visibility**: public
- **Lines**: 71–74, proof length 0 (def by if-then-else)
- **Notes**: The additive convention (negating `toAdd`) is chosen so uniformizers have order +1.

---

### `theorem pointValuation_eq_zero_iff`
- **Type**: `(f : C.FunctionField) → (C.pointValuation P f = 0 ↔ f = 0)`
- **What**: The multiplicative valuation vanishes if and only if the function is zero. This connects the multiplicative convention to the zero-function test.
- **How**: Forward: contrapositive using `Valuation.ne_zero_iff`; backward: `map_zero`.
- **Hypotheses**: Standard.
- **Uses from project**: `pointValuation`.
- **Used by**: `ord_P_eq_top_iff` (line 90).
- **Visibility**: public
- **Lines**: 78–82, proof length 5
- **Notes**: None.

---

### `@[simp] theorem ord_P_zero`
- **Type**: `C.ord_P P 0 = ⊤`
- **What**: The order at any smooth point of the zero function is `⊤`.
- **How**: `simp [ord_P]` with `map_zero`.
- **Hypotheses**: None.
- **Uses from project**: `ord_P`.
- **Used by**: `ord_P_add_le` (line 145).
- **Visibility**: public
- **Lines**: 84–85, proof length 1
- **Notes**: `@[simp]` tagged.

---

### `theorem ord_P_eq_top_iff`
- **Type**: `(f : C.FunctionField) → (C.ord_P P f = ⊤ ↔ f = 0)`
- **What**: The additive order is `⊤` if and only if the function is zero.
- **How**: Cases on the `dif` in `ord_P` definition; uses `pointValuation_eq_zero_iff` and `WithTop.coe_ne_top`.
- **Hypotheses**: None.
- **Uses from project**: `ord_P`, `pointValuation_eq_zero_iff`.
- **Used by**: (not explicitly referenced in this file; available to external callers).
- **Visibility**: public
- **Lines**: 87–92, proof length 6
- **Notes**: Unused within this file.

---

### `private lemma ord_P_of_ne`
- **Type**: `(f : C.FunctionField) → (h : C.pointValuation P f ≠ 0) → C.ord_P P f = (-(WithZero.unzero h).toAdd : ℤ)`
- **What**: Private unfolding lemma: when `f ≠ 0`, the `dif_neg` branch of `ord_P` gives an explicit integer cast.
- **How**: `dif_neg h`.
- **Hypotheses**: `f ≠ 0` encoded as `C.pointValuation P f ≠ 0`.
- **Uses from project**: `ord_P`, `pointValuation`.
- **Used by**: `one_le_ord_P_iff_pointValuation_lt_one`, `ord_P_mul` (×3), `ord_P_add_le` (×3), `ord_P_inv` (×2), `ord_P_one`, `ord_P_neg` (×2), `exists_uniformizer`. Used by 8 distinct declarations.
- **Visibility**: private
- **Lines**: 94–96, proof length 1
- **Notes**: Key internal tool; effectively the "private API" of `ord_P`.

---

### `theorem one_le_ord_P_iff_pointValuation_lt_one`
- **Type**: `(hf : f ≠ 0) → ((1 : WithTop ℤ) ≤ C.ord_P P f ↔ C.pointValuation P f < 1)`
- **What**: Order-positivity bridge: `ord_P(f) ≥ 1` if and only if the multiplicative valuation is strictly less than 1 (i.e., `f` lies in the maximal ideal). This is the defining property of the maximal ideal in a DVR.
- **How**: Unfolds `ord_P_of_ne`, converts between `WithTop ℤ` comparison and the `Multiplicative ℤ` ordering using `Multiplicative.toAdd_lt` and `omega`.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: `ord_P_of_ne`, `pointValuation`.
- **Used by**: Not explicitly referenced in this file.
- **Visibility**: public
- **Lines**: 102–117, proof length 16
- **Notes**: Unused within this file; presumably consumed by `CurveMap.lean` or order-transport lemmas.

---

### `theorem ord_P_mul`
- **Type**: `(f g : C.FunctionField) → C.ord_P P (f * g) = C.ord_P P f + C.ord_P P g`
- **What**: The order function is additive under multiplication: `ord_P(fg) = ord_P(f) + ord_P(g)`.
- **How**: Cases on `f = 0`, `g = 0`; for nonzero case uses `ord_P_of_ne` on all three and applies `toAdd_mul` + `WithZero.coe_mul` + `map_mul` to extract `unzero(v(fg)) = unzero(v(f)) · unzero(v(g))`; sign-flips add correctly via `neg_add`.
- **Hypotheses**: None (zero cases handled via `simp`).
- **Uses from project**: `ord_P_of_ne`, `pointValuation`.
- **Used by**: `ord_P_pow`, `Uniformizer.unit_quotient`.
- **Visibility**: public
- **Lines**: 119–136, proof length 18
- **Notes**: None.

---

### `theorem ord_P_add_le`
- **Type**: `(f g : C.FunctionField) → min (C.ord_P P f) (C.ord_P P g) ≤ C.ord_P P (f + g)`
- **What**: Non-archimedean inequality: the order of a sum is at least the minimum of the orders.
- **How**: Zero cases reduce via `simp`/`le_top`. Nonzero case uses `Valuation.map_add` (`v(f+g) ≤ max(v(f),v(g))`) and `ord_P_of_ne` on all three; case-splits on which maximum term dominates, using `WithTop.coe_le_coe` and `neg_le_neg_iff` to transfer the `WithZero` inequality to `WithTop ℤ`.
- **Hypotheses**: None.
- **Uses from project**: `ord_P_of_ne`, `ord_P_zero`, `pointValuation`.
- **Used by**: `ord_P_add_eq_of_lt` (×2).
- **Visibility**: public
- **Lines**: 138–164, proof length 27
- **Notes**: None.

---

### `theorem ord_P_inv`
- **Type**: `(f : C.FunctionField) → (hf : f ≠ 0) → C.ord_P P f⁻¹ = -(C.ord_P P f)`
- **What**: The order of the inverse is the negative of the order: `ord_P(f⁻¹) = −ord_P(f)`.
- **How**: Uses `ord_P_of_ne` on both `f` and `f⁻¹`, then shows `unzero(v(f⁻¹)).toAdd = −unzero(v(f)).toAdd` via `toAdd_inv` and `map_inv₀` in `WithZero`; finishes with `push_cast`.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: `ord_P_of_ne`, `pointValuation`.
- **Used by**: `Uniformizer.unit_quotient`, `Uniformizer.exists_ord_P_eq`.
- **Visibility**: public
- **Lines**: 166–181, proof length 16
- **Notes**: None.

---

### `@[simp] theorem ord_P_one`
- **Type**: `C.ord_P P (1 : C.FunctionField) = 0`
- **What**: The order of the constant function 1 is 0 (it is a unit, so it has no zeros or poles).
- **How**: Uses `ord_P_of_ne` (since `v(1) = 1 ≠ 0`), then shows `unzero(v(1)) = 1` via `map_one` and `WithZero.coe_inj`.
- **Hypotheses**: None.
- **Uses from project**: `ord_P_of_ne`, `pointValuation`.
- **Used by**: Consumed by `simp` in `ord_P_pow` base case and `ord_P_mul` base (indirectly); not explicitly referenced.
- **Visibility**: public
- **Lines**: 183–188, proof length 6
- **Notes**: `@[simp]` tagged.

---

### `theorem ord_P_pow`
- **Type**: `(f : C.FunctionField) → (n : ℕ) → C.ord_P P (f ^ n) = n • C.ord_P P f`
- **What**: The order of a power: `ord_P(f^n) = n · ord_P(f)`.
- **How**: Induction on `n`; base `simp`; step uses `pow_succ`, `ord_P_mul`, induction hypothesis, and `succ_nsmul`.
- **Hypotheses**: None.
- **Uses from project**: `ord_P_mul`.
- **Used by**: `Uniformizer.exists_ord_P_eq`.
- **Visibility**: public
- **Lines**: 190–194, proof length 5
- **Notes**: None.

---

### `@[simp] theorem ord_P_neg`
- **Type**: `(f : C.FunctionField) → C.ord_P P (-f) = C.ord_P P f`
- **What**: The order of the negation equals the order: `ord_P(−f) = ord_P(f)`.
- **How**: Zero case by `neg_zero`. Nonzero case: uses `ord_P_of_ne` on `f` and `−f` (nonzero via `Valuation.map_neg`), then shows the `unzero` values agree via `WithZero.coe_injective` and `Valuation.map_neg`.
- **Hypotheses**: None.
- **Uses from project**: `ord_P_of_ne`, `pointValuation`.
- **Used by**: `ord_P_add_eq_of_lt` (line 219), `ord_P_sub_eq_of_lt` (line 233).
- **Visibility**: public
- **Lines**: 196–207, proof length 12
- **Notes**: `@[simp]` tagged.

---

### `theorem ord_P_add_eq_of_lt`
- **Type**: `(h : C.ord_P P f < C.ord_P P g) → C.ord_P P (f + g) = C.ord_P P f`
- **What**: Strict non-archimedean principle: when `ord_P(f) < ord_P(g)`, the dominant term wins and `ord_P(f + g) = ord_P(f)`.
- **How**: Lower bound from `ord_P_add_le` with `min_eq_left h.le`. Upper bound by writing `f = (f+g) + (−g)`, applying `ord_P_add_le` to `(f+g, −g)`, `ord_P_neg`, and case-splitting; the case `ord_P(f+g) ≥ ord_P(g)` leads to contradiction with `h`.
- **Hypotheses**: `C.ord_P P f < C.ord_P P g`.
- **Uses from project**: `ord_P_add_le`, `ord_P_neg`.
- **Used by**: `ord_P_sub_eq_of_lt`.
- **Visibility**: public
- **Lines**: 211–224, proof length 14
- **Notes**: None.

---

### `theorem ord_P_sub_eq_of_lt`
- **Type**: `(h : C.ord_P P f < C.ord_P P g) → C.ord_P P (f - g) = C.ord_P P f`
- **What**: Subtraction variant of `ord_P_add_eq_of_lt`: `ord_P(f − g) = ord_P(f)` when `ord_P(f) < ord_P(g)`.
- **How**: Rewrites `f − g = f + (−g)`, applies `ord_P_add_eq_of_lt` using `ord_P_neg`.
- **Hypotheses**: `C.ord_P P f < C.ord_P P g`.
- **Uses from project**: `ord_P_add_eq_of_lt`, `ord_P_neg`.
- **Used by**: Not referenced in this file.
- **Visibility**: public
- **Lines**: 228–233, proof length 6
- **Notes**: Unused within this file.

---

### `def Uniformizer`
- **Type**: `(C : SmoothPlaneCurve F) → (P : C.SmoothPoint) → (t : C.FunctionField) → Prop`  
  defined as `C.ord_P P t = 1`
- **What**: A uniformizer at `P` is a function with order exactly 1 there; it generates the maximal ideal of the local ring.
- **How**: Pure definition.
- **Hypotheses**: None.
- **Uses from project**: `ord_P`.
- **Used by**: `exists_uniformizer`, `exists_K_uniformizer`, `Uniformizer.unit_quotient`, `Uniformizer.ne_zero`, `Uniformizer.exists_ord_P_eq`.
- **Visibility**: public
- **Lines**: 247–249, proof length 0 (def)
- **Notes**: None.

---

### `theorem exists_uniformizer`
- **Type**: `(C : SmoothPlaneCurve F) → (P : C.SmoothPoint) → ∃ t : C.FunctionField, Uniformizer C P t`
- **What**: Every smooth point has a uniformizer in the function field `F(C)` (Silverman II.1.1).
- **How**: Calls `valuation_exists_uniformizer` from mathlib's DVR/HeightOneSpectrum API to get `π` with `v(π) = Multiplicative.ofAdd (−1)`. Uses `ord_P_of_ne` and `WithZero.coe_unzero` to verify `ord_P P π = 1`.
- **Hypotheses**: None (uses DVR instance and fraction ring instance implicitly).
- **Uses from project**: `localRingAt`, `pointValuation`, `ord_P_of_ne`, `Uniformizer`.
- **Used by**: `exists_K_uniformizer`.
- **Visibility**: public
- **Lines**: 255–270, proof length 16
- **Notes**: Uses `WithZero.exp_ne_zero` (mathlib) to confirm `v(π) ≠ 0`.

---

### `abbrev RationalPoint`
- **Type**: `(C : SmoothPlaneCurve F) → Type _` equals `C.SmoothPoint`
- **What**: An alias for `C.SmoothPoint` that matches Silverman's notation `C(K)` for `K`-rational points. In this thin wrapper every smooth point is `F`-rational by construction.
- **How**: Pure abbreviation.
- **Hypotheses**: None.
- **Uses from project**: `C.SmoothPoint`.
- **Used by**: `exists_K_uniformizer`.
- **Visibility**: public
- **Lines**: 278, proof length 0 (abbrev)
- **Notes**: None.

---

### `theorem exists_K_uniformizer`
- **Type**: `(C : SmoothPlaneCurve F) → (P : C.RationalPoint) → ∃ t : C.FunctionField, Uniformizer C P t`
- **What**: Every `F`-rational smooth point has a uniformizer defined over `F` (Silverman II.1.1.1 / Exercise 2.16). In this formulation it is the same as `exists_uniformizer` since all smooth points are rational.
- **How**: Directly applies `C.exists_uniformizer P`.
- **Hypotheses**: None.
- **Uses from project**: `exists_uniformizer`, `RationalPoint`, `Uniformizer`.
- **Used by**: Not referenced in this file.
- **Visibility**: public
- **Lines**: 286–288, proof length 1
- **Notes**: Unused within this file; documentation/alias lemma.

---

### `theorem Uniformizer.unit_quotient`
- **Type**: `(ht : Uniformizer C P t) → (hs : Uniformizer C P s) → C.ord_P P (t / s) = 0`
- **What**: The ratio of two uniformizers is a unit at `P`: `ord_P(t/s) = 0`.
- **How**: Unfolds `div` as `mul_inv`, applies `ord_P_mul` and `ord_P_inv`, and uses both `ht : ord_P P t = 1` and `hs : ord_P P s = 1` with `ne_zero` hypotheses from `simp [Uniformizer]`.
- **Hypotheses**: `t` and `s` are both uniformizers at `P`.
- **Uses from project**: `Uniformizer`, `ord_P`, `ord_P_mul`, `ord_P_inv`.
- **Used by**: Not referenced in this file.
- **Visibility**: public
- **Lines**: 293–303, proof length 11
- **Notes**: Unused within this file.

---

### `theorem Uniformizer.ne_zero`
- **Type**: `(ht : Uniformizer C P t) → t ≠ 0`
- **What**: Every uniformizer is nonzero.
- **How**: Assumes `t = 0`, substitutes, and `simp [Uniformizer]` derives `ord_P P 0 = 1 → ⊤ = 1` contradiction.
- **Hypotheses**: `t` a uniformizer at `P`.
- **Uses from project**: `Uniformizer`, `ord_P`.
- **Used by**: `Uniformizer.exists_ord_P_eq` (line 316: `ht.ne_zero`).
- **Visibility**: public
- **Lines**: 306–308, proof length 3
- **Notes**: None.

---

### `theorem Uniformizer.exists_ord_P_eq`
- **Type**: `(ht : Uniformizer C P t) → (n : ℤ) → ∃ s : C.FunctionField, s ≠ 0 ∧ C.ord_P P s = n`
- **What**: Given a uniformizer `t`, for every integer `n` there exists a function with order exactly `n` at `P` (using `t^|n|` or its inverse).
- **How**: Cases on `n < 0` vs `n ≥ 0`. Negative: witness `(t^(−n).toNat)⁻¹`, using `ord_P_inv` and `ord_P_pow` and `Int.toNat_of_nonneg`. Nonneg: witness `t^n.toNat`, using `ord_P_pow` and `Int.toNat_of_nonneg`.
- **Hypotheses**: `t` a uniformizer at `P`.
- **Uses from project**: `Uniformizer`, `Uniformizer.ne_zero`, `ord_P_inv`, `ord_P_pow`.
- **Used by**: Not referenced in this file.
- **Visibility**: public
- **Lines**: 313–332, proof length 20
- **Notes**: Unused within this file.

---

## Cross-reference summary

**`ord_P_of_ne`** (private): used inside 8 declarations — the key internal tool.
**`pointValuation`**: used in effectively every non-trivial theorem.
**`ord_P`**: the central output definition, used throughout.
**`ord_P_add_le`**: used in `ord_P_add_eq_of_lt`.
**`ord_P_neg`**: used in `ord_P_add_eq_of_lt` and `ord_P_sub_eq_of_lt`.
**`ord_P_mul`**: used in `ord_P_pow` and `Uniformizer.unit_quotient`.

**Declarations not referenced within this file** (dead-code candidates here; may be used by other files):
- `ord_P_eq_top_iff`
- `one_le_ord_P_iff_pointValuation_lt_one`
- `ord_P_sub_eq_of_lt`
- `exists_K_uniformizer`
- `Uniformizer.unit_quotient`
- `Uniformizer.exists_ord_P_eq`
- `maximalIdealAt_isPrime` (used only implicitly as an instance)

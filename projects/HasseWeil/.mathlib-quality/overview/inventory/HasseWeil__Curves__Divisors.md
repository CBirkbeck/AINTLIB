# Inventory: ./HasseWeil/Curves/Divisors.lean

**File**: `HasseWeil/Curves/Divisors.lean`  
**Total lines**: 324  
**Imports**: `HasseWeil.Curves.Basic`, `HasseWeil.Curves.Infinity`, `Mathlib.Data.Finsupp.Defs`  
**Tickets closed**: T-II-3-001 (`Divisor`), T-II-3-002 (`Divisor.degree`, `Divisor.degreeHom`), T-II-3-005 (`divisorOf`), T-II-3-006 (`IsPrincipal`, `LinearlyEquiv`), T-II-3-007 (`Pic`, `Pic₀`), T-II-3-008 (`divisorOf_algebraMap_F`, `const_of_valuation_le_one_of_ordAtInfty_nonneg`)

---

### `abbrev Divisor`
- **Type**: `(C : SmoothPlaneCurve F) : Type _ := C.SmoothPoint →₀ ℤ`
- **What**: The divisor group of a smooth plane curve as finitely-supported integer-valued functions on smooth points; i.e., the free abelian group on `C.SmoothPoint`.
- **How**: Definitional abbreviation using `Finsupp`; inherits the additive group structure of `Finsupp` automatically.
- **Hypotheses**: `F` a field.
- **Uses from project**: `SmoothPlaneCurve`, `SmoothPoint`
- **Used by**: every other declaration in this file
- **Visibility**: public
- **Lines**: 30 (1-line definition)
- **Notes**: Silverman II.3. The abbreviation (not `def`) means unification sees through it; important for instance inheritance.

---

### `def Divisor.degree`
- **Type**: `(D : Divisor C) : ℤ`  
  `= D.sum fun _ n => n`
- **What**: The degree of a divisor, i.e., the sum of all integer coefficients `Σ_P n_P`.
- **How**: `Finsupp.sum` summing the coefficient function.
- **Hypotheses**: none beyond the field `F`.
- **Uses from project**: `Divisor`
- **Used by**: `degree_zero`, `degree_add`, `degreeHom_apply`, `degree_neg`, `degree_sub`, `mem_degZero`, `degree_nonneg_of_isEffective`
- **Visibility**: public
- **Lines**: 38–39 (2 lines)
- **Notes**: none

---

### `@[simp] theorem degree_zero`
- **Type**: `degree (0 : Divisor C) = 0`
- **What**: The zero divisor has degree zero.
- **How**: One-liner via `Finsupp.sum_zero_index`.
- **Hypotheses**: none
- **Uses from project**: `Divisor.degree`
- **Used by**: `degreeHom`
- **Visibility**: public
- **Lines**: 41–42 (1 line)
- **Notes**: none

---

### `@[simp] theorem degree_add`
- **Type**: `(D₁ + D₂).degree = D₁.degree + D₂.degree`
- **What**: The degree map is additive.
- **How**: `Finsupp.sum_add_index'` with trivial zero/add proofs.
- **Hypotheses**: none
- **Uses from project**: `Divisor.degree`
- **Used by**: `degreeHom`
- **Visibility**: public
- **Lines**: 44–46 (3 lines)
- **Notes**: none

---

### `def Divisor.degreeHom`
- **Type**: `(C : SmoothPlaneCurve F) : Divisor C →+ ℤ`
- **What**: The degree function packaged as an additive group homomorphism from `Div(C)` to `ℤ`.
- **How**: Structure fields filled with `degree_zero` and `degree_add`.
- **Hypotheses**: none
- **Uses from project**: `Divisor`, `Divisor.degree`, `degree_zero`, `degree_add`
- **Used by**: `degreeHom_apply`, `degree_neg`, `degree_sub`, `degZero`
- **Visibility**: public
- **Lines**: 50–54 (5 lines)
- **Notes**: none

---

### `@[simp] theorem degreeHom_apply`
- **Type**: `degreeHom C D = D.degree`
- **What**: `degreeHom C` evaluates to `degree` pointwise.
- **How**: `rfl`
- **Hypotheses**: none
- **Uses from project**: `Divisor.degreeHom`, `Divisor.degree`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 55 (1 line)
- **Notes**: none

---

### `@[simp] theorem degree_neg`
- **Type**: `(-D).degree = -D.degree`
- **What**: The degree of the negation of a divisor is the negation of the degree.
- **How**: `(degreeHom C).map_neg D`.
- **Hypotheses**: none
- **Uses from project**: `Divisor.degreeHom`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 57–58 (2 lines)
- **Notes**: none

---

### `@[simp] theorem degree_sub`
- **Type**: `(D₁ - D₂).degree = D₁.degree - D₂.degree`
- **What**: The degree map is compatible with subtraction.
- **How**: `(degreeHom C).map_sub`.
- **Hypotheses**: none
- **Uses from project**: `Divisor.degreeHom`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 60–62 (3 lines)
- **Notes**: none

---

### `noncomputable def Divisor.degZero`
- **Type**: `(C : SmoothPlaneCurve F) : AddSubgroup (Divisor C)`
- **What**: The kernel of `degreeHom`, i.e., the subgroup `Div⁰(C)` of degree-zero divisors.
- **How**: `(degreeHom C).ker`
- **Hypotheses**: none
- **Uses from project**: `Divisor.degreeHom`
- **Used by**: `mem_degZero`, `Divisor₀`, `Pic₀`
- **Visibility**: public
- **Lines**: 66–67 (2 lines)
- **Notes**: `noncomputable` because `degreeHom` is not computable (due to finsupp sum). Used in `Pic₀` and as the ambient group for `Divisor₀`.

---

### `@[simp] theorem mem_degZero`
- **Type**: `D ∈ degZero C ↔ D.degree = 0`
- **What**: Membership in `Div⁰(C)` is equivalent to degree zero.
- **How**: `AddMonoidHom.mem_ker`
- **Hypotheses**: none
- **Uses from project**: `Divisor.degZero`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 69–70 (2 lines)
- **Notes**: none

---

### `def Divisor.IsEffective`
- **Type**: `(D : Divisor C) : Prop := ∀ P, 0 ≤ D P`
- **What**: A divisor is effective (written `D ≥ 0` in Silverman) if all coefficients are non-negative.
- **How**: Definitional predicate.
- **Hypotheses**: none
- **Uses from project**: `Divisor`
- **Used by**: `isEffective_zero`, `IsEffective.add`, `degree_nonneg_of_isEffective`
- **Visibility**: public
- **Lines**: 75 (1 line)
- **Notes**: none

---

### `@[simp] theorem isEffective_zero`
- **Type**: `IsEffective (0 : Divisor C)`
- **What**: The zero divisor is effective.
- **How**: `fun _ => le_refl 0`
- **Hypotheses**: none
- **Uses from project**: `Divisor.IsEffective`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 77 (1 line)
- **Notes**: none

---

### `theorem IsEffective.add`
- **Type**: `D₁.IsEffective → D₂.IsEffective → (D₁ + D₂).IsEffective`
- **What**: The sum of two effective divisors is effective.
- **How**: Uses `Finsupp.add_apply` to reduce to pointwise `add_nonneg`.
- **Hypotheses**: none
- **Uses from project**: `Divisor.IsEffective`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 79–82 (4 lines)
- **Notes**: none

---

### `theorem degree_nonneg_of_isEffective`
- **Type**: `D.IsEffective → 0 ≤ D.degree`
- **What**: An effective divisor has non-negative degree.
- **How**: `Finsupp.sum_nonneg` using the pointwise non-negativity from `IsEffective`.
- **Hypotheses**: none
- **Uses from project**: `Divisor.IsEffective`, `Divisor.degree`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 83–85 (3 lines)
- **Notes**: none

---

### `noncomputable abbrev Divisor₀`
- **Type**: `(C : SmoothPlaneCurve F) : AddSubgroup (Divisor C) := Divisor.degZero C`
- **What**: Alias for `Divisor.degZero C`; the subgroup `Div⁰(C)` of degree-zero divisors.
- **How**: Definitional abbreviation.
- **Hypotheses**: none
- **Uses from project**: `Divisor.degZero`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 90–91 (2 lines)
- **Notes**: Redundant with `Divisor.degZero` — exists as a convenient short alias in the outer namespace.

---

### `noncomputable def divisorOf`
- **Type**: `(C : SmoothPlaneCurve F) (f : C.FunctionField) : Divisor C`
- **What**: The principal divisor `div(f) = Σ_P ord_P(f)·(P)` of a rational function; returns the zero divisor when `f = 0`.
- **How**: Uses `Finsupp.ofSupportFinite` with `C.ord_P P f` unwrapped from `WithTop ℤ` via `untopD 0`; finiteness of support is `C.finite_setOf_ord_P_nonzero` (from `Infinity.lean`, Silverman II.1.2).
- **Hypotheses**: none (handles `f = 0` by case split)
- **Uses from project**: `SmoothPlaneCurve.ord_P`, `SmoothPlaneCurve.finite_setOf_ord_P_nonzero`, `SmoothPlaneCurve.ord_P_zero`
- **Used by**: `divisorOf_apply`, `divisorOf_zero`, `divisorOf_mul`, `divisorOf_one`, `divisorOf_inv`, `divisorOf_pow`, `divisorHom`, `divisorOf_algebraMap_F`
- **Visibility**: public
- **Lines**: 103–119 (17 lines)
- **Notes**: `classical` instance used for decidability of `P`-support membership.

---

### `theorem divisorOf_apply`
- **Type**: `C.divisorOf f P = (C.ord_P P f).untopD 0`
- **What**: Evaluating the principal divisor at a smooth point `P` gives `ord_P(f)` (with `⊤` mapped to `0`).
- **How**: `rfl` (definitional unfolding of `Finsupp.ofSupportFinite`).
- **Hypotheses**: none
- **Uses from project**: `SmoothPlaneCurve.divisorOf`
- **Used by**: `divisorOf_zero`, `divisorOf_mul`, `divisorOf_inv`, `divisorOf_pow`, `divisorOf_algebraMap_F`
- **Visibility**: public
- **Lines**: 120–122 (3 lines)
- **Notes**: Key computation lemma — used 5 times in this file.

---

### `@[simp] theorem divisorOf_zero`
- **Type**: `C.divisorOf (0 : C.FunctionField) = 0`
- **What**: The principal divisor of zero is the zero divisor.
- **How**: `Finsupp.ext` + `divisorOf_apply` + `C.ord_P_zero`.
- **Hypotheses**: none
- **Uses from project**: `SmoothPlaneCurve.divisorOf_apply`, `SmoothPlaneCurve.ord_P_zero`
- **Used by**: `divisorOf_algebraMap_F`
- **Visibility**: public
- **Lines**: 124–128 (5 lines)
- **Notes**: none

---

### `theorem divisorOf_mul`
- **Type**: `f ≠ 0 → g ≠ 0 → C.divisorOf (f * g) = C.divisorOf f + C.divisorOf g`
- **What**: The principal divisor of a product is the sum of the principal divisors (for nonzero factors).
- **How**: `Finsupp.ext` + `divisorOf_apply` + `C.ord_P_mul` + `WithTop.ne_top_iff_exists` to extract integer values from the `WithTop ℤ` valuations, then `WithTop.coe_add` / `untopD_coe`.
- **Hypotheses**: both `f` and `g` are nonzero
- **Uses from project**: `SmoothPlaneCurve.divisorOf_apply`, `SmoothPlaneCurve.ord_P_mul`, `SmoothPlaneCurve.ord_P_eq_top_iff`
- **Used by**: `divisorHom`, `IsPrincipal.add`
- **Visibility**: public
- **Lines**: 130–142 (13 lines)
- **Notes**: none

---

### `@[simp] theorem divisorOf_one`
- **Type**: `C.divisorOf (1 : C.FunctionField) = 0`
- **What**: The principal divisor of the constant function 1 is the zero divisor.
- **How**: `Finsupp.ext` + `divisorOf_apply` + `ord_P_one`.
- **Hypotheses**: none
- **Uses from project**: `SmoothPlaneCurve.divisorOf_apply`, `SmoothPlaneCurve.ord_P_one`
- **Used by**: `isPrincipal_zero`
- **Visibility**: public
- **Lines**: 143–147 (5 lines)
- **Notes**: none

---

### `theorem divisorOf_inv`
- **Type**: `f ≠ 0 → C.divisorOf f⁻¹ = -(C.divisorOf f)`
- **What**: The principal divisor of the inverse of a nonzero function is the negation of its divisor.
- **How**: `Finsupp.ext` + `divisorOf_apply` + `C.ord_P_inv`, then `WithTop.ne_top_iff_exists` to extract the integer value and `untopD_coe`.
- **Hypotheses**: `f ≠ 0`
- **Uses from project**: `SmoothPlaneCurve.divisorOf_apply`, `SmoothPlaneCurve.ord_P_inv`, `SmoothPlaneCurve.ord_P_eq_top_iff`
- **Used by**: `IsPrincipal.neg`
- **Visibility**: public
- **Lines**: 150–159 (10 lines)
- **Notes**: none

---

### `theorem divisorOf_pow`
- **Type**: `f ≠ 0 → (n : ℕ) → C.divisorOf (f ^ n) = n • C.divisorOf f`
- **What**: The principal divisor of a power `fⁿ` is `n` times the principal divisor of `f`.
- **How**: `Finsupp.ext` + `divisorOf_apply` + `C.ord_P_pow`, then `WithTop.ne_top_iff_exists` to extract integer and `WithTop.coe_nsmul` / `untopD_coe`.
- **Hypotheses**: `f ≠ 0`
- **Uses from project**: `SmoothPlaneCurve.divisorOf_apply`, `SmoothPlaneCurve.ord_P_pow`, `SmoothPlaneCurve.ord_P_eq_top_iff`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 162–171 (10 lines)
- **Notes**: Dead code within this file; used elsewhere in the project potentially.

---

### `noncomputable def divisorHom`
- **Type**: `(C : SmoothPlaneCurve F) : C.FunctionFieldˣ →* Multiplicative (Divisor C)`
- **What**: The divisor map packaged as a multiplicative monoid homomorphism from the units of the function field to the (multiplicatively written) divisor group.
- **How**: Supplies `toFun` via `Multiplicative.ofAdd ∘ divisorOf`, and `map_mul'` via `divisorOf_mul` applied to the unit nonzero witnesses.
- **Hypotheses**: none
- **Uses from project**: `SmoothPlaneCurve.divisorOf`, `SmoothPlaneCurve.divisorOf_mul`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 174–182 (9 lines)
- **Notes**: Dead code within this file. The multiplicative wrapper (`Multiplicative`) is the standard trick for an additive group to satisfy a multiplicative monoid hom interface.

---

### `def IsPrincipal`
- **Type**: `(C : SmoothPlaneCurve F) (D : Divisor C) : Prop := ∃ f : C.FunctionField, f ≠ 0 ∧ C.divisorOf f = D`
- **What**: A divisor is principal if it equals the principal divisor of some nonzero rational function.
- **How**: Existential definition.
- **Hypotheses**: none
- **Uses from project**: `SmoothPlaneCurve.divisorOf`, `Divisor`
- **Used by**: `isPrincipal_zero`, `IsPrincipal.add`, `IsPrincipal.neg`, `principalSubgroup`, `mem_principalSubgroup`, `LinearlyEquiv`, `LinearlyEquiv.refl`, `LinearlyEquiv.symm`, `LinearlyEquiv.trans`
- **Visibility**: public
- **Lines**: 189–190 (2 lines)
- **Notes**: The key Api predicate for the Picard group theory.

---

### `theorem isPrincipal_zero`
- **Type**: `C.IsPrincipal 0`
- **What**: The zero divisor is principal (witnessed by the constant function 1).
- **How**: Provides the witness `⟨1, one_ne_zero, C.divisorOf_one⟩`.
- **Hypotheses**: none
- **Uses from project**: `SmoothPlaneCurve.IsPrincipal`, `SmoothPlaneCurve.divisorOf_one`
- **Used by**: `principalSubgroup`, `LinearlyEquiv.refl`
- **Visibility**: public
- **Lines**: 192–193 (2 lines)
- **Notes**: none

---

### `theorem IsPrincipal.add`
- **Type**: `C.IsPrincipal D₁ → C.IsPrincipal D₂ → C.IsPrincipal (D₁ + D₂)`
- **What**: The sum of two principal divisors is principal.
- **How**: Destructs both witnesses `f`, `g`; witness is `f * g` with `divisorOf_mul`.
- **Hypotheses**: none
- **Uses from project**: `SmoothPlaneCurve.IsPrincipal`, `SmoothPlaneCurve.divisorOf_mul`
- **Used by**: `principalSubgroup`
- **Visibility**: public
- **Lines**: 195–200 (6 lines)
- **Notes**: none

---

### `theorem IsPrincipal.neg`
- **Type**: `C.IsPrincipal D → C.IsPrincipal (-D)`
- **What**: The negation of a principal divisor is principal.
- **How**: Destructs witness `f`; new witness is `f⁻¹` via `divisorOf_inv`.
- **Hypotheses**: none
- **Uses from project**: `SmoothPlaneCurve.IsPrincipal`, `SmoothPlaneCurve.divisorOf_inv`
- **Used by**: `principalSubgroup`, `LinearlyEquiv.symm`
- **Visibility**: public
- **Lines**: 202–206 (5 lines)
- **Notes**: none

---

### `noncomputable def principalSubgroup`
- **Type**: `(C : SmoothPlaneCurve F) : AddSubgroup (Divisor C)`
- **What**: The subgroup of principal divisors in `Div(C)`.
- **How**: Direct `AddSubgroup` construction using `IsPrincipal` as carrier, `isPrincipal_zero`, `IsPrincipal.add`, `IsPrincipal.neg`.
- **Hypotheses**: none
- **Uses from project**: `SmoothPlaneCurve.IsPrincipal`, `SmoothPlaneCurve.isPrincipal_zero`, `SmoothPlaneCurve.IsPrincipal.add`, `SmoothPlaneCurve.IsPrincipal.neg`
- **Used by**: `mem_principalSubgroup`, `Pic`, `Pic₀`
- **Visibility**: public
- **Lines**: 210–215 (6 lines)
- **Notes**: `noncomputable` due to `divisorOf` noncomputability.

---

### `@[simp] theorem mem_principalSubgroup`
- **Type**: `D ∈ C.principalSubgroup ↔ C.IsPrincipal D`
- **What**: Membership in the principal subgroup is equivalent to being a principal divisor.
- **How**: `Iff.rfl` (definitional).
- **Hypotheses**: none
- **Uses from project**: `SmoothPlaneCurve.principalSubgroup`, `SmoothPlaneCurve.IsPrincipal`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 217–218 (2 lines)
- **Notes**: none

---

### `def LinearlyEquiv`
- **Type**: `(C : SmoothPlaneCurve F) (D₁ D₂ : Divisor C) : Prop := C.IsPrincipal (D₁ - D₂)`
- **What**: Two divisors are linearly equivalent (`D₁ ~ D₂` in Silverman notation) if their difference is a principal divisor.
- **How**: Definitional — reduces to `IsPrincipal`.
- **Hypotheses**: none
- **Uses from project**: `SmoothPlaneCurve.IsPrincipal`, `Divisor`
- **Used by**: `LinearlyEquiv.refl`, `LinearlyEquiv.symm`, `LinearlyEquiv.trans`
- **Visibility**: public
- **Lines**: 222–223 (2 lines)
- **Notes**: none

---

### `theorem LinearlyEquiv.refl`
- **Type**: `C.LinearlyEquiv D D`
- **What**: Linear equivalence is reflexive.
- **How**: Reduces to `IsPrincipal (D - D)`; `simp` gives `D - D = 0` and `isPrincipal_zero` closes it.
- **Hypotheses**: none
- **Uses from project**: `SmoothPlaneCurve.LinearlyEquiv`, `SmoothPlaneCurve.isPrincipal_zero`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 225–228 (4 lines)
- **Notes**: none

---

### `theorem LinearlyEquiv.symm`
- **Type**: `C.LinearlyEquiv D₁ D₂ → C.LinearlyEquiv D₂ D₁`
- **What**: Linear equivalence is symmetric.
- **How**: Uses `D₂ - D₁ = -(D₁ - D₂)` by `abel`, then `IsPrincipal.neg`.
- **Hypotheses**: none
- **Uses from project**: `SmoothPlaneCurve.LinearlyEquiv`, `SmoothPlaneCurve.IsPrincipal.neg`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 230–234 (5 lines)
- **Notes**: none

---

### `theorem LinearlyEquiv.trans`
- **Type**: `C.LinearlyEquiv D₁ D₂ → C.LinearlyEquiv D₂ D₃ → C.LinearlyEquiv D₁ D₃`
- **What**: Linear equivalence is transitive.
- **How**: Uses `D₁ - D₃ = (D₁ - D₂) + (D₂ - D₃)` by `abel`, then `IsPrincipal.add`.
- **Hypotheses**: none
- **Uses from project**: `SmoothPlaneCurve.LinearlyEquiv`, `SmoothPlaneCurve.IsPrincipal.add`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 236–241 (6 lines)
- **Notes**: none

---

### `theorem ord_P_algebraMap_F_of_ne_zero`
- **Type**: `c ≠ 0 → (P : C.SmoothPoint) → C.ord_P P (algebraMap F C.FunctionField c) = 0`
- **What**: A nonzero constant (image of a field element) has valuation zero at every smooth point.
- **How**: Factors `algebraMap F → F(C)` through `CoordinateRing` via the scalar tower; shows the coordinate ring element `u = algebraMap F C.CoordinateRing c` is not in `maximalIdealAt P` using `mem_maximalIdealAt_iff_eval_zero` (it evaluates to `c ≠ 0`); then uses `ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt` to convert non-membership to valuation zero; finally uses `IsScalarTower.algebraMap_apply` to align the scalar tower.
- **Hypotheses**: `c ≠ 0`
- **Uses from project**: `SmoothPlaneCurve.ord_P`, `SmoothPlaneCurve.maximalIdealAt`, `SmoothPlaneCurve.mem_maximalIdealAt_iff_eval_zero`, `SmoothPlaneCurve.ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt`
- **Used by**: `divisorOf_algebraMap_F`
- **Visibility**: public
- **Lines**: 248–280 (33 lines)
- **Notes**: **Proof longer than 30 lines.** The proof navigates the scalar tower `F → CoordinateRing → FunctionField` carefully, and uses `FaithfulSMul.algebraMap_injective` for injectivity. The non-membership argument rewrites `u` as `(C c) • 1 + 0 • Y` to apply the bivariate membership lemma.

---

### `@[simp] theorem divisorOf_algebraMap_F`
- **Type**: `C.divisorOf (algebraMap F C.FunctionField c) = 0`
- **What**: The principal divisor of any constant (F-element) is the zero divisor; the `c = 0` case maps to `divisorOf_zero`, the `c ≠ 0` case to `ord_P_algebraMap_F_of_ne_zero`.
- **How**: Case split on `c = 0`; the nonzero case uses `Finsupp.ext` + `divisorOf_apply` + `ord_P_algebraMap_F_of_ne_zero`.
- **Hypotheses**: none (handles both `c = 0` and `c ≠ 0`)
- **Uses from project**: `SmoothPlaneCurve.divisorOf_zero`, `SmoothPlaneCurve.divisorOf_apply`, `SmoothPlaneCurve.ord_P_algebraMap_F_of_ne_zero`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 285–290 (6 lines)
- **Notes**: None

---

### `theorem const_of_valuation_le_one_of_ordAtInfty_nonneg`
- **Type**: `[IsIntegrallyClosed C.CoordinateRing] → (f : C.FunctionField) → (∀ v : IsDedekindDomain.HeightOneSpectrum C.CoordinateRing, v.valuation C.FunctionField f ≤ 1) → (0 : WithTop ℤ) ≤ C.ordAtInfty f → ∃ c : F, f = algebraMap F C.FunctionField c`
- **What**: If `f` has valuation at most 1 at every height-one prime of the coordinate ring and nonneg order at infinity, then `f` is a constant (the prime-indexed reformulation of Silverman II.3.1(a) ⇒). This is the T-II-3-008 (⇒) direction.
- **How**: One-line delegation to `C.const_of_no_poles_of_valuation_of_ordAtInfty` (defined in `Infinity.lean`).
- **Hypotheses**: `IsIntegrallyClosed C.CoordinateRing`; prime-indexed no-poles hypothesis; nonneg order at infinity.
- **Uses from project**: `SmoothPlaneCurve.const_of_no_poles_of_valuation_of_ordAtInfty`, `SmoothPlaneCurve.ordAtInfty`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 301–307 (7 lines)
- **Notes**: The SmoothPoint-indexed version (which would require surjectivity of `SmoothPoint.toHeightOneSpectrum` under `[IsAlgClosed F]`) is not yet available; this prime-indexed form is what the current IC-006 infrastructure supports.

---

### `abbrev Pic`
- **Type**: `(C : SmoothPlaneCurve F) : Type _ := Divisor C ⧸ C.principalSubgroup`
- **What**: The Picard group `Pic(C)` — quotient of the divisor group by the principal subgroup.
- **How**: Quotient group abbreviation.
- **Hypotheses**: none
- **Uses from project**: `Divisor`, `SmoothPlaneCurve.principalSubgroup`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 313–314 (2 lines)
- **Notes**: none

---

### `abbrev Pic₀`
- **Type**: `(C : SmoothPlaneCurve F) : Type _ := (Divisor.degZero C) ⧸ (C.principalSubgroup.addSubgroupOf (Divisor.degZero C))`
- **What**: The degree-zero Picard group `Pic⁰(C)` — quotient of degree-zero divisors by (the restriction of) principal divisors.
- **How**: Quotient group abbreviation using `addSubgroupOf` to restrict the principal subgroup to `Div⁰(C)`.
- **Hypotheses**: none (implicitly uses that principal divisors have degree 0, tracked separately as T-II-3-009)
- **Uses from project**: `Divisor.degZero`, `SmoothPlaneCurve.principalSubgroup`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 319–320 (2 lines)
- **Notes**: The fact that `principalSubgroup` sits inside `degZero` (principal divisors have degree 0, Silverman II.3.1(b)) is not yet formally verified in this file — it's a pending ticket T-II-3-009. The `addSubgroupOf` construction is still well-typed regardless.

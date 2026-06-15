# Inventory: ./HasseWeil/Curves/ProjectiveDivisor.lean

**File**: `HasseWeil/Curves/ProjectiveDivisor.lean`
**Lines**: 541
**Imports**: `HasseWeil.Curves.Divisors`, `Mathlib.FieldTheory.IsAlgClosed.Basic`, `Mathlib.FieldTheory.RatFunc.Degree`

**Summary**: Defines the projective divisor group on a smooth plane curve by adjoining the point at infinity to the affine divisor group (`Finsupp`). Includes the embedding `Divisor.toProjective`, degree arithmetic, principal projective divisors, linear equivalence, `PicProj`/`PicProj₀` types, and two lemmas toward the Helper A product formula (rational-function field, algebraically-closed case).

---

## Declarations

### `inductive ProjectiveSmoothPoint`
- **Type**: `(C : SmoothPlaneCurve F) → Type _` with constructors `affine (P : C.SmoothPoint)` and `infinity`
- **What**: Inductive type of places on the projective closure of `C`: either an affine smooth point or the unique place at infinity.
- **How**: Plain inductive definition; no proof content.
- **Hypotheses**: Field `F`.
- **Uses from project**: `SmoothPlaneCurve`, `SmoothPoint` (from `Divisors`/`Basic`).
- **Used by**: `ProjectiveDivisor`, `toProjective`, `projectiveDivisorOf`, `projectiveDivisorOf_apply_affine`, `projectiveDivisorOf_apply_infinity`, `ProjIsPrincipal`, `projPrincipalSubgroup`, `ProjLinearlyEquiv`, `PicProj`, `PicProj₀`.
- **Visibility**: public
- **Lines**: 46–48
- **Notes**: Core type; no heartbeat issue.

---

### `theorem affine_injective`
- **Type**: `Function.Injective (ProjectiveSmoothPoint.affine (C := C))`
- **What**: The `affine` constructor is injective as a function from `C.SmoothPoint` to `ProjectiveSmoothPoint C`.
- **How**: Pattern-matching via `cases h; rfl`.
- **Hypotheses**: None beyond the ambient `C : SmoothPlaneCurve F`.
- **Uses from project**: None.
- **Used by**: `projectiveDivisorOf_apply_affine` (used as `ProjectiveSmoothPoint.affine_injective` in `Finsupp.mapDomain_apply`).
- **Visibility**: public
- **Lines**: 55–59 (proof: 3 lines)
- **Notes**: None.

---

### `noncomputable instance DecidableEq (ProjectiveSmoothPoint C)`
- **Type**: `DecidableEq (ProjectiveSmoothPoint C)` (anonymous instance)
- **What**: Provides decidable equality on `ProjectiveSmoothPoint C` via classical logic.
- **How**: `Classical.decEq _`.
- **Hypotheses**: None.
- **Uses from project**: None.
- **Used by**: Needed implicitly by `Finsupp` operations (`mapDomain`, `single`, etc.) on `ProjectiveDivisor C`.
- **Visibility**: public
- **Lines**: 62–64 (proof: 2 lines)
- **Notes**: None.

---

### `abbrev ProjectiveDivisor`
- **Type**: `(C : SmoothPlaneCurve F) → Type _` defined as `ProjectiveSmoothPoint C →₀ ℤ`
- **What**: The free abelian group of formal `ℤ`-linear combinations of places on the projective closure.
- **How**: Abbreviation unfolding to `Finsupp`.
- **Hypotheses**: None.
- **Uses from project**: `ProjectiveSmoothPoint`.
- **Used by**: All subsequent declarations in the file.
- **Visibility**: public
- **Lines**: 71–72
- **Notes**: Using `abbrev` (not `def`) so the `Finsupp` API applies transparently.

---

### `def degree`
- **Type**: `ProjectiveDivisor C → ℤ`
- **What**: The degree of a projective divisor, the sum of all coefficients.
- **How**: Defined as `Finsupp.sum` with `fun _ n => n`.
- **Hypotheses**: None.
- **Uses from project**: None.
- **Used by**: `degree_zero`, `degree_add`, `degreeHom`, `degreeHom_apply`, `degree_neg`, `degree_sub`, `degZero`, `mem_degZero`, `degree_toProjective`, `degreeHom_comp_toProjectiveHom`, `toProjective_mem_degZero`, `projectiveDivisorOf_degree`, `projectiveDivisorOf_degree_zero`, `projectiveDivisorOf_degree_eq_zero_iff`, `projectiveDivisorOf_degree_mul`, `projectiveDivisorOf_degree_inv`, `projectiveDivisorOf_degree_one`, `toProjective_eq_projectiveDivisorOf_of_aff_degZero_of_proj_degZero`.
- **Visibility**: public
- **Lines**: 80–81
- **Notes**: Key API used throughout; `Finsupp.sum` formulation mirrors `Divisor.degree`.

---

### `@[simp] theorem degree_zero`
- **Type**: `degree (0 : ProjectiveDivisor C) = 0`
- **What**: Degree of the zero divisor is zero.
- **How**: `Finsupp.sum_zero_index`.
- **Hypotheses**: None.
- **Uses from project**: None (pure `Finsupp` lemma).
- **Used by**: `degreeHom`, `projectiveDivisorOf_degree_zero`, `projectiveDivisorOf_degree_one`.
- **Visibility**: public
- **Lines**: 83–84 (proof: 1 line)
- **Notes**: None.

---

### `@[simp] theorem degree_add`
- **Type**: `(D₁ + D₂).degree = D₁.degree + D₂.degree`
- **What**: Degree is additive on projective divisors.
- **How**: `Finsupp.sum_add_index'` with the trivial witnesses.
- **Hypotheses**: None.
- **Uses from project**: None.
- **Used by**: `degreeHom`, `projectiveDivisorOf_degree`, `projectiveDivisorOf_degree_mul`.
- **Visibility**: public
- **Lines**: 86–88 (proof: 1 line)
- **Notes**: None.

---

### `def degreeHom`
- **Type**: `ProjectiveDivisor C →+ ℤ`
- **What**: The degree map packaged as an additive group homomorphism.
- **How**: Assembles `toFun := degree`, `map_zero' := degree_zero`, `map_add' := degree_add`.
- **Hypotheses**: None.
- **Uses from project**: `degree`, `degree_zero`, `degree_add`.
- **Used by**: `degreeHom_apply`, `degree_neg`, `degree_sub`, `degZero`, `degreeHom_comp_toProjectiveHom`.
- **Visibility**: public
- **Lines**: 92–95
- **Notes**: None.

---

### `@[simp] theorem degreeHom_apply`
- **Type**: `degreeHom C D = D.degree`
- **What**: `degreeHom` unfolds to `degree` on elements.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `degreeHom`, `degree`.
- **Used by**: Downstream callers that may use the hom form; unused inside this file's proofs directly.
- **Visibility**: public
- **Lines**: 97–98 (proof: 1 line)
- **Notes**: None.

---

### `@[simp] theorem degree_neg`
- **Type**: `(-D).degree = -D.degree`
- **What**: Degree negates under additive negation.
- **How**: `(degreeHom C).map_neg D`.
- **Hypotheses**: None.
- **Uses from project**: `degreeHom`.
- **Used by**: `projectiveDivisorOf_degree_inv`.
- **Visibility**: public
- **Lines**: 100–102 (proof: 1 line)
- **Notes**: None.

---

### `@[simp] theorem degree_sub`
- **Type**: `(D₁ - D₂).degree = D₁.degree - D₂.degree`
- **What**: Degree is compatible with subtraction.
- **How**: `(degreeHom C).map_sub D₁ D₂`.
- **Hypotheses**: None.
- **Uses from project**: `degreeHom`.
- **Used by**: Unused within this file (no callers found).
- **Visibility**: public
- **Lines**: 104–106 (proof: 1 line)
- **Notes**: Dead-code candidate in this file; may be used externally.

---

### `noncomputable def degZero`
- **Type**: `AddSubgroup (ProjectiveDivisor C)`
- **What**: The subgroup of degree-zero projective divisors, `ker(degreeHom C)`.
- **How**: Defined as `(degreeHom C).ker`.
- **Hypotheses**: None.
- **Uses from project**: `degreeHom`.
- **Used by**: `mem_degZero`, `toProjective_mem_degZero`, `toProjectiveDegZeroHom`, `PicProj₀`.
- **Visibility**: public
- **Lines**: 110–112
- **Notes**: None.

---

### `@[simp] theorem mem_degZero`
- **Type**: `D ∈ degZero C ↔ D.degree = 0`
- **What**: Membership in `degZero C` is equivalent to the degree being zero.
- **How**: `AddMonoidHom.mem_ker`.
- **Hypotheses**: None.
- **Uses from project**: `degZero`, `degree`.
- **Used by**: `toProjective_mem_degZero`.
- **Visibility**: public
- **Lines**: 114–116 (proof: 1 line)
- **Notes**: None.

---

### `noncomputable def toProjective`
- **Type**: `Divisor C → ProjectiveDivisor C`
- **What**: Embeds the affine divisor group into the projective one by mapping each affine smooth point `P` to `ProjectiveSmoothPoint.affine P`.
- **How**: `Finsupp.mapDomain ProjectiveSmoothPoint.affine`.
- **Hypotheses**: None.
- **Uses from project**: `Divisor` (from `HasseWeil.Curves.Divisors`), `ProjectiveSmoothPoint.affine`.
- **Used by**: `toProjective_zero`, `toProjective_add`, `degree_toProjective`, `toProjectiveHom`, `toProjective_mem_degZero`, `toProjectiveDegZeroHom`, `toProjectiveDegZeroHom_coe`, `projectiveDivisorOf`, `projectiveDivisorOf_zero`, `projectiveDivisorOf_apply_affine`, `projectiveDivisorOf_apply_infinity`, `projectiveDivisorOf_eq_toProjective_of_ordAtInfty_zero`, `projectiveDivisorOf_eq_toProjective_of_intDegree_zero`, `toProjective_eq_projectiveDivisorOf_of_aff_degZero_of_proj_degZero`, `toProjective_eq_projectiveDivisorOf_of_helperB`, `toProjective_eq_projectiveDivisorOf_witness_of_helperB`.
- **Visibility**: public
- **Lines**: 126–127
- **Notes**: The most-referenced declaration in this file.

---

### `@[simp] theorem toProjective_zero`
- **Type**: `toProjective (0 : Divisor C) = (0 : ProjectiveDivisor C)`
- **What**: `toProjective` preserves the zero divisor.
- **How**: `Finsupp.mapDomain_zero`.
- **Hypotheses**: None.
- **Uses from project**: `toProjective`.
- **Used by**: `toProjectiveHom`, `projectiveDivisorOf_zero`, `projectiveDivisorOf_one`.
- **Visibility**: public
- **Lines**: 129–131 (proof: 1 line)
- **Notes**: None.

---

### `@[simp] theorem toProjective_add`
- **Type**: `toProjective (D₁ + D₂) = toProjective D₁ + toProjective D₂`
- **What**: `toProjective` is additive.
- **How**: `Finsupp.mapDomain_add`.
- **Hypotheses**: None.
- **Uses from project**: `toProjective`.
- **Used by**: `toProjectiveHom`, `projectiveDivisorOf_mul`.
- **Visibility**: public
- **Lines**: 133–135 (proof: 1 line)
- **Notes**: None.

---

### `theorem degree_toProjective`
- **Type**: `(toProjective D).degree = D.degree`
- **What**: The affine-to-projective embedding preserves degrees.
- **How**: Uses `Finsupp.sum_mapDomain_index` with the injectivity witnesses.
- **Hypotheses**: None.
- **Uses from project**: `toProjective`, `degree` (both `ProjectiveDivisor.degree` and `Divisor.degree`).
- **Used by**: `degreeHom_comp_toProjectiveHom`, `toProjective_mem_degZero`, `projectiveDivisorOf_degree`, `toProjective_mem_degZero`.
- **Visibility**: public
- **Lines**: 140–144 (proof: 4 lines)
- **Notes**: None.

---

### `noncomputable def toProjectiveHom`
- **Type**: `Divisor C →+ ProjectiveDivisor C`
- **What**: The embedding `toProjective` packaged as an additive group hom.
- **How**: Assembles from `toProjective`, `toProjective_zero`, `toProjective_add`.
- **Hypotheses**: None.
- **Uses from project**: `toProjective`, `toProjective_zero`, `toProjective_add`.
- **Used by**: `toProjectiveHom_apply`, `degreeHom_comp_toProjectiveHom`, `toProjectiveDegZeroHom`.
- **Visibility**: public
- **Lines**: 148–152
- **Notes**: None.

---

### `@[simp] theorem toProjectiveHom_apply`
- **Type**: `toProjectiveHom C D = D.toProjective`
- **What**: `toProjectiveHom` applies as dot notation `toProjective`.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `toProjectiveHom`, `toProjective`.
- **Used by**: Unused within this file.
- **Visibility**: public
- **Lines**: 154–155 (proof: 1 line)
- **Notes**: Dead-code candidate within this file.

---

### `theorem degreeHom_comp_toProjectiveHom`
- **Type**: `(ProjectiveDivisor.degreeHom C).comp (toProjectiveHom C) = Divisor.degreeHom C`
- **What**: Degree commutes with the affine-to-projective embedding at the level of additive homs.
- **How**: `AddMonoidHom.ext` plus `Divisor.degree_toProjective`.
- **Hypotheses**: None.
- **Uses from project**: `degreeHom` (both `ProjectiveDivisor.degreeHom` and `Divisor.degreeHom`), `toProjectiveHom`, `degree_toProjective`.
- **Used by**: Unused within this file.
- **Visibility**: public
- **Lines**: 159–161 (proof: 1 line)
- **Notes**: Dead-code candidate within this file.

---

### `theorem toProjective_mem_degZero`
- **Type**: `D ∈ Divisor.degZero C → D.toProjective ∈ ProjectiveDivisor.degZero C`
- **What**: `toProjective` sends affine degree-zero divisors to projective degree-zero divisors.
- **How**: Rewrites with `mem_degZero` and `degree_toProjective`, then uses `Divisor.mem_degZero.mp`.
- **Hypotheses**: `D ∈ Divisor.degZero C`.
- **Uses from project**: `toProjective`, `degZero` (both), `mem_degZero` (both), `degree_toProjective`, `Divisor.mem_degZero`.
- **Used by**: `toProjectiveDegZeroHom`.
- **Visibility**: public
- **Lines**: 165–169 (proof: 3 lines)
- **Notes**: None.

---

### `noncomputable def toProjectiveDegZeroHom`
- **Type**: `Divisor.degZero C →+ ProjectiveDivisor.degZero C`
- **What**: Restricts `toProjectiveHom` to the degree-zero subgroups.
- **How**: `AddMonoidHom.codRestrict` applied to the composite with `subtype`.
- **Hypotheses**: None.
- **Uses from project**: `toProjectiveHom`, `degZero` (both), `toProjective_mem_degZero`.
- **Used by**: `toProjectiveDegZeroHom_coe`.
- **Visibility**: public
- **Lines**: 173–178
- **Notes**: None.

---

### `@[simp] theorem toProjectiveDegZeroHom_coe`
- **Type**: `((toProjectiveDegZeroHom C D : ProjectiveDivisor.degZero C) : ProjectiveDivisor C) = (D : Divisor C).toProjective`
- **What**: The coercion of `toProjectiveDegZeroHom` back to `ProjectiveDivisor C` equals `toProjective`.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `toProjectiveDegZeroHom`, `toProjective`.
- **Used by**: Unused within this file.
- **Visibility**: public
- **Lines**: 180–183 (proof: 1 line)
- **Notes**: Dead-code candidate within this file.

---

### `noncomputable def projectiveDivisorOf`
- **Type**: `SmoothPlaneCurve F → C.FunctionField → ProjectiveDivisor C`
- **What**: The full projective divisor of a rational function: affine part embedded projectively plus the coefficient `ordAtInfty(f)` placed at the point at infinity.
- **How**: Sum of `(C.divisorOf f).toProjective` and `Finsupp.single infinity (ordAtInfty f).untopD 0`.
- **Hypotheses**: None (returns zero for `f = 0` by convention).
- **Uses from project**: `Divisor.toProjective`, `divisorOf` (from `Divisors`), `ordAtInfty` (from `Infinity`), `ProjectiveSmoothPoint.infinity`.
- **Used by**: `projectiveDivisorOf_zero`, `projectiveDivisorOf_apply_affine`, `projectiveDivisorOf_apply_infinity`, `projectiveDivisorOf_eq_toProjective_of_ordAtInfty_zero`, `projectiveDivisorOf_degree`, `projectiveDivisorOf_degree_zero`, `projectiveDivisorOf_degree_eq_zero_iff`, `projectiveDivisorOf_mul`, `projectiveDivisorOf_one`, `projectiveDivisorOf_inv`, `projectiveDivisorOf_degree_one`, `projectiveDivisorOf_degree_mul`, `projectiveDivisorOf_degree_inv`, `toProjective_eq_projectiveDivisorOf_of_aff_degZero_of_proj_degZero`, `projectiveDivisorOf_degree_eq_zero_of_helperB`, `projectiveDivisorOf_eq_toProjective_of_intDegree_zero`, `toProjective_eq_projectiveDivisorOf_of_helperB`, `toProjective_eq_projectiveDivisorOf_witness_of_helperB`, `ProjIsPrincipal`.
- **Visibility**: public
- **Lines**: 201–204
- **Notes**: Central definition; the most-referenced `def` in the `SmoothPlaneCurve` section.

---

### `@[simp] theorem projectiveDivisorOf_zero`
- **Type**: `C.projectiveDivisorOf (0 : C.FunctionField) = 0`
- **What**: Projective divisor of zero is zero (convention).
- **How**: Uses `divisorOf_zero`, `toProjective_zero`, `ordAtInfty_zero`, `WithTop.untopD_top`, `Finsupp.single_zero`.
- **Hypotheses**: None.
- **Uses from project**: `projectiveDivisorOf`, `Divisor.toProjective_zero`, `divisorOf_zero` (from `Divisors`), `ordAtInfty_zero` (from `Infinity`).
- **Used by**: `projectiveDivisorOf_degree_zero`.
- **Visibility**: public
- **Lines**: 206–210 (proof: 3 lines)
- **Notes**: None.

---

### `theorem projectiveDivisorOf_apply_affine`
- **Type**: `C.projectiveDivisorOf f (ProjectiveSmoothPoint.affine P) = (C.ord_P P f).untopD 0`
- **What**: The coefficient at an affine place equals the affine order of `f` at `P`.
- **How**: Unfolds, proves `affine P ≠ infinity` by `nomatch`, uses `Finsupp.mapDomain_apply` (with `affine_injective`) and `divisorOf_apply`.
- **Hypotheses**: None.
- **Uses from project**: `projectiveDivisorOf`, `Divisor.toProjective`, `ProjectiveSmoothPoint.affine_injective`, `divisorOf_apply` (from `Divisors`), `ord_P` (from `OrdAtPoint`).
- **Used by**: Unused within this file.
- **Visibility**: public
- **Lines**: 212–222 (proof: 9 lines)
- **Notes**: Dead-code candidate within this file.

---

### `theorem projectiveDivisorOf_apply_infinity`
- **Type**: `C.projectiveDivisorOf f ProjectiveSmoothPoint.infinity = (C.ordAtInfty f).untopD 0`
- **What**: The coefficient at the infinity place equals `ordAtInfty f` (untopD-ed).
- **How**: Proves infinity ∉ support of the `mapDomain` part by `nomatch`, then uses `Finsupp.notMem_support_iff.mp` and `Finsupp.single_eq_same`.
- **Hypotheses**: None.
- **Uses from project**: `projectiveDivisorOf`, `Divisor.toProjective`, `ordAtInfty` (from `Infinity`).
- **Used by**: Unused within this file.
- **Visibility**: public
- **Lines**: 224–236 (proof: 12 lines)
- **Notes**: Dead-code candidate within this file.

---

### `theorem projectiveDivisorOf_eq_toProjective_of_ordAtInfty_zero`
- **Type**: `C.ordAtInfty f = 0 → C.projectiveDivisorOf f = (C.divisorOf f).toProjective`
- **What**: When the order at infinity is zero, the projective divisor equals the embedded affine divisor.
- **How**: Rewrites with the hypothesis, `WithTop.untopD_coe`, `Finsupp.single_zero`, `add_zero`.
- **Hypotheses**: `C.ordAtInfty f = ((0 : ℤ) : WithTop ℤ)`.
- **Uses from project**: `projectiveDivisorOf`, `Divisor.toProjective`, `ordAtInfty`.
- **Used by**: `toProjective_eq_projectiveDivisorOf_of_aff_degZero_of_proj_degZero`, `projectiveDivisorOf_eq_toProjective_of_intDegree_zero`.
- **Visibility**: public
- **Lines**: 243–247 (proof: 3 lines)
- **Notes**: None.

---

### `theorem projectiveDivisorOf_degree`
- **Type**: `(C.projectiveDivisorOf f).degree = (C.divisorOf f).degree + (C.ordAtInfty f).untopD 0`
- **What**: Structural decomposition of the degree: affine part degree plus order at infinity.
- **How**: Uses `degree_add`, `degree_toProjective`, and `Finsupp.sum_single_index`.
- **Hypotheses**: None.
- **Uses from project**: `projectiveDivisorOf`, `degree_add`, `degree_toProjective`, `Divisor.degree` (via `divisorOf`), `ordAtInfty`.
- **Used by**: `projectiveDivisorOf_degree_zero`, `projectiveDivisorOf_degree_eq_zero_iff`, `projectiveDivisorOf_degree_eq_zero_of_helperB`.
- **Visibility**: public
- **Lines**: 256–263 (proof: 6 lines)
- **Notes**: None.

---

### `@[simp] theorem projectiveDivisorOf_degree_zero`
- **Type**: `(C.projectiveDivisorOf (0 : C.FunctionField)).degree = 0`
- **What**: Degree of the projective divisor of 0 is zero.
- **How**: `projectiveDivisorOf_zero` then `degree_zero`.
- **Hypotheses**: None.
- **Uses from project**: `projectiveDivisorOf_zero`, `degree_zero`.
- **Used by**: Unused within this file.
- **Visibility**: public
- **Lines**: 267–269 (proof: 2 lines)
- **Notes**: Dead-code candidate within this file.

---

### `theorem projectiveDivisorOf_degree_eq_zero_iff`
- **Type**: `(C.projectiveDivisorOf f).degree = 0 ↔ (C.divisorOf f).degree = -((C.ordAtInfty f).untopD 0)`
- **What**: The projective divisor of `f` has degree zero iff the affine degree equals minus the order at infinity.
- **How**: `projectiveDivisorOf_degree` then `omega`.
- **Hypotheses**: None.
- **Uses from project**: `projectiveDivisorOf_degree`, `Divisor.degree`, `ordAtInfty`.
- **Used by**: `toProjective_eq_projectiveDivisorOf_of_aff_degZero_of_proj_degZero`.
- **Visibility**: public
- **Lines**: 274–278 (proof: 3 lines)
- **Notes**: None.

---

### `theorem projectiveDivisorOf_mul`
- **Type**: `f ≠ 0 → g ≠ 0 → C.projectiveDivisorOf (f * g) = C.projectiveDivisorOf f + C.projectiveDivisorOf g`
- **What**: Multiplicativity of the projective principal divisor map on nonzero inputs.
- **How**: Uses `ordAtInfty_eq_top_iff` to extract `WithTop` representatives, then rewrites with `divisorOf_mul`, `toProjective_add`, `ordAtInfty_mul`, cast/`WithTop.coe_add`/`untopD_coe`, and `Finsupp.single_add`; closes with `abel`.
- **Hypotheses**: `f ≠ 0`, `g ≠ 0`.
- **Uses from project**: `projectiveDivisorOf`, `divisorOf_mul` (from `Divisors`), `Divisor.toProjective_add`, `ordAtInfty_mul`, `ordAtInfty_eq_top_iff` (from `Infinity`).
- **Used by**: `projectiveDivisorOf_inv`, `projectiveDivisorOf_degree_mul`, `ProjIsPrincipal.add`.
- **Visibility**: public
- **Lines**: 281–294 (proof: 12 lines)
- **Notes**: The nonzero hypotheses are essential; uses `WithTop` arithmetic carefully.

---

### `@[simp] theorem projectiveDivisorOf_one`
- **Type**: `C.projectiveDivisorOf (1 : C.FunctionField) = 0`
- **What**: The projective principal divisor of 1 is zero.
- **How**: Uses `ordAtInfty_one`, `divisorOf_one`, `toProjective_zero`, `Finsupp.single_zero`.
- **Hypotheses**: None.
- **Uses from project**: `projectiveDivisorOf`, `divisorOf_one` (from `Divisors`), `ordAtInfty_one` (from `Infinity`), `toProjective_zero`.
- **Used by**: `projectiveDivisorOf_inv`, `projectiveDivisorOf_degree_one`, `projIsPrincipal_zero`.
- **Visibility**: public
- **Lines**: 296–302 (proof: 6 lines)
- **Notes**: None.

---

### `theorem projectiveDivisorOf_inv`
- **Type**: `f ≠ 0 → C.projectiveDivisorOf f⁻¹ = -(C.projectiveDivisorOf f)`
- **What**: The projective divisor of the inverse equals the negation.
- **How**: Applies `projectiveDivisorOf_mul` to `f⁻¹ * f = 1`, then uses `projectiveDivisorOf_one` and `eq_neg_of_add_eq_zero_left`.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: `projectiveDivisorOf_mul`, `projectiveDivisorOf_one`.
- **Used by**: `projectiveDivisorOf_degree_inv`, `ProjIsPrincipal.neg`.
- **Visibility**: public
- **Lines**: 305–310 (proof: 5 lines)
- **Notes**: None.

---

### `@[simp] theorem projectiveDivisorOf_degree_one`
- **Type**: `(C.projectiveDivisorOf (1 : C.FunctionField)).degree = 0`
- **What**: Degree of the projective divisor of 1 is zero.
- **How**: `projectiveDivisorOf_one` then `degree_zero`.
- **Hypotheses**: None.
- **Uses from project**: `projectiveDivisorOf_one`, `degree_zero`.
- **Used by**: Unused within this file.
- **Visibility**: public
- **Lines**: 314–316 (proof: 2 lines)
- **Notes**: Dead-code candidate within this file.

---

### `theorem projectiveDivisorOf_degree_mul`
- **Type**: `f ≠ 0 → g ≠ 0 → (C.projectiveDivisorOf (f * g)).degree = (C.projectiveDivisorOf f).degree + (C.projectiveDivisorOf g).degree`
- **What**: Multiplicativity of degree at the level of projective divisors.
- **How**: `projectiveDivisorOf_mul` then `degree_add`.
- **Hypotheses**: `f ≠ 0`, `g ≠ 0`.
- **Uses from project**: `projectiveDivisorOf_mul`, `degree_add`.
- **Used by**: Unused within this file.
- **Visibility**: public
- **Lines**: 321–325 (proof: 2 lines)
- **Notes**: Dead-code candidate within this file.

---

### `theorem projectiveDivisorOf_degree_inv`
- **Type**: `f ≠ 0 → (C.projectiveDivisorOf f⁻¹).degree = -(C.projectiveDivisorOf f).degree`
- **What**: Degree of the projective divisor of the inverse equals the negation.
- **How**: `projectiveDivisorOf_inv` then `degree_neg`.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: `projectiveDivisorOf_inv`, `degree_neg`.
- **Used by**: Unused within this file.
- **Visibility**: public
- **Lines**: 328–330 (proof: 2 lines)
- **Notes**: Dead-code candidate within this file.

---

### `theorem toProjective_eq_projectiveDivisorOf_of_aff_degZero_of_proj_degZero`
- **Type**: `f ≠ 0 → (C.projectiveDivisorOf f).degree = 0 → (C.divisorOf f).degree = 0 → (C.divisorOf f).toProjective = C.projectiveDivisorOf f`
- **What**: Under the full II.3.1(b) condition plus zero affine degree, the embedded affine divisor equals the projective principal divisor.
- **How**: Extracts `ordAtInfty f = 0` from the two degree conditions via `projectiveDivisorOf_degree_eq_zero_iff` and `omega`; peels the `WithTop` witness with `ne_top_iff_exists`; applies `projectiveDivisorOf_eq_toProjective_of_ordAtInfty_zero`.
- **Hypotheses**: `f ≠ 0`, `(C.projectiveDivisorOf f).degree = 0`, `(C.divisorOf f).degree = 0`.
- **Uses from project**: `projectiveDivisorOf_degree_eq_zero_iff`, `ordAtInfty_eq_top_iff`, `projectiveDivisorOf_eq_toProjective_of_ordAtInfty_zero`.
- **Used by**: `toProjective_eq_projectiveDivisorOf_of_helperB`.
- **Visibility**: public
- **Lines**: 340–355 (proof: 15 lines)
- **Notes**: None.

---

### `theorem projectiveDivisorOf_degree_eq_zero_of_helperB`
- **Type**: `f ≠ 0 → (C.divisorOf f).degree = RatFunc.intDegree (C.normAsRatFunc f) → (C.projectiveDivisorOf f).degree = 0`
- **What**: Full II.3.1(b) closure: the projective divisor of a nonzero `f` has degree zero, parametric on Helper B (`(divisorOf f).degree = intDegree(normAsRatFunc f)`).
- **How**: Rewrites with `projectiveDivisorOf_degree`, `hHelperB`, `ordAtInfty_of_ne`, `WithTop.untopD_coe`, and `ring`.
- **Hypotheses**: `f ≠ 0`, `(C.divisorOf f).degree = RatFunc.intDegree (C.normAsRatFunc f)`.
- **Uses from project**: `projectiveDivisorOf_degree`, `ordAtInfty_of_ne` (from `Infinity`), `normAsRatFunc` (from `Curves/Basic` or similar).
- **Used by**: `toProjective_eq_projectiveDivisorOf_of_helperB`.
- **Visibility**: public
- **Lines**: 370–376 (proof: 5 lines)
- **Notes**: The `ordAtInfty_of_ne` lemma is the key link to the `normAsRatFunc` definition.

---

### `theorem projectiveDivisorOf_eq_toProjective_of_intDegree_zero`
- **Type**: `f ≠ 0 → RatFunc.intDegree (C.normAsRatFunc f) = 0 → C.projectiveDivisorOf f = (C.divisorOf f).toProjective`
- **What**: When the integer degree of the norm is zero, the projective divisor is the embedded affine divisor.
- **How**: Reconstructs `ordAtInfty f = 0` via `ordAtInfty_of_ne` and `h`, then applies `projectiveDivisorOf_eq_toProjective_of_ordAtInfty_zero`.
- **Hypotheses**: `f ≠ 0`, `RatFunc.intDegree (C.normAsRatFunc f) = 0`.
- **Uses from project**: `ordAtInfty_of_ne`, `projectiveDivisorOf_eq_toProjective_of_ordAtInfty_zero`, `normAsRatFunc`.
- **Used by**: Unused within this file.
- **Visibility**: public
- **Lines**: 383–389 (proof: 5 lines)
- **Notes**: Dead-code candidate within this file.

---

### `theorem toProjective_eq_projectiveDivisorOf_of_helperB`
- **Type**: `f ≠ 0 → (C.divisorOf f).degree = RatFunc.intDegree (C.normAsRatFunc f) → (C.divisorOf f).degree = 0 → (C.divisorOf f).toProjective = C.projectiveDivisorOf f`
- **What**: Under Helper B and zero affine degree, the embedded affine principal equals the projective principal. The chained form for Pic⁰ constructions.
- **How**: Applies `projectiveDivisorOf_degree_eq_zero_of_helperB` then `toProjective_eq_projectiveDivisorOf_of_aff_degZero_of_proj_degZero`.
- **Hypotheses**: `f ≠ 0`, Helper B identity, `(C.divisorOf f).degree = 0`.
- **Uses from project**: `projectiveDivisorOf_degree_eq_zero_of_helperB`, `toProjective_eq_projectiveDivisorOf_of_aff_degZero_of_proj_degZero`.
- **Used by**: `toProjective_eq_projectiveDivisorOf_witness_of_helperB`.
- **Visibility**: public
- **Lines**: 399–406 (proof: 4 lines)
- **Notes**: None.

---

### `theorem toProjective_eq_projectiveDivisorOf_witness_of_helperB`
- **Type**: `C.IsPrincipal D → D.degree = 0 → (∀ f ≠ 0, (C.divisorOf f).degree = RatFunc.intDegree (C.normAsRatFunc f)) → ∃ g ≠ 0, C.projectiveDivisorOf g = D.toProjective`
- **What**: Under universal Helper B and affine degree-zero, an affine principal divisor of degree zero lifts to a projective principal. Packages the witness for `ProjIsPrincipal`.
- **How**: Destructs the `IsPrincipal` witness `f`, rewrites `degree` via the witness, applies `toProjective_eq_projectiveDivisorOf_of_helperB`.
- **Hypotheses**: `C.IsPrincipal D`, `D.degree = 0`, universal Helper B.
- **Uses from project**: `Divisor.IsPrincipal` (from `Divisors`), `Divisor.toProjective`, `toProjective_eq_projectiveDivisorOf_of_helperB`, `divisorOf` (from `Divisors`), `normAsRatFunc`.
- **Used by**: Unused within this file.
- **Visibility**: public
- **Lines**: 416–425 (proof: 8 lines)
- **Notes**: Dead-code candidate within this file; likely intended for downstream Pic⁰ constructions.

---

### `def ProjIsPrincipal`
- **Type**: `SmoothPlaneCurve F → ProjectiveDivisor C → Prop`
- **What**: A projective divisor is principal if it equals `projectiveDivisorOf f` for some nonzero `f ∈ F(C)*`.
- **How**: Existential definition `∃ f, f ≠ 0 ∧ C.projectiveDivisorOf f = D`.
- **Hypotheses**: None.
- **Uses from project**: `projectiveDivisorOf`.
- **Used by**: `projIsPrincipal_zero`, `ProjIsPrincipal.add`, `ProjIsPrincipal.neg`, `projPrincipalSubgroup`, `mem_projPrincipalSubgroup`, `ProjLinearlyEquiv`, `ProjLinearlyEquiv.refl`, `ProjLinearlyEquiv.symm`, `ProjLinearlyEquiv.trans`.
- **Visibility**: public
- **Lines**: 431–432
- **Notes**: Key notion; used by 9+ declarations.

---

### `theorem projIsPrincipal_zero`
- **Type**: `C.ProjIsPrincipal 0`
- **What**: The zero divisor is principal (witnessed by `f = 1`).
- **How**: Uses `projectiveDivisorOf_one`.
- **Hypotheses**: None.
- **Uses from project**: `ProjIsPrincipal`, `projectiveDivisorOf_one`.
- **Used by**: `projPrincipalSubgroup`, `ProjLinearlyEquiv.refl`.
- **Visibility**: public
- **Lines**: 434–435 (proof: 1 line)
- **Notes**: None.

---

### `theorem ProjIsPrincipal.add`
- **Type**: `C.ProjIsPrincipal D₁ → C.ProjIsPrincipal D₂ → C.ProjIsPrincipal (D₁ + D₂)`
- **What**: The sum of two principal divisors is principal.
- **How**: Destructs both witnesses, applies `projectiveDivisorOf_mul`.
- **Hypotheses**: `C.ProjIsPrincipal D₁`, `C.ProjIsPrincipal D₂`.
- **Uses from project**: `ProjIsPrincipal`, `projectiveDivisorOf_mul`.
- **Used by**: `projPrincipalSubgroup`, `ProjLinearlyEquiv.trans`.
- **Visibility**: public
- **Lines**: 437–443 (proof: 5 lines)
- **Notes**: None.

---

### `theorem ProjIsPrincipal.neg`
- **Type**: `C.ProjIsPrincipal D → C.ProjIsPrincipal (-D)`
- **What**: The negation of a principal divisor is principal.
- **How**: Destructs the witness, applies `projectiveDivisorOf_inv`.
- **Hypotheses**: `C.ProjIsPrincipal D`.
- **Uses from project**: `ProjIsPrincipal`, `projectiveDivisorOf_inv`.
- **Used by**: `projPrincipalSubgroup`, `ProjLinearlyEquiv.symm`.
- **Visibility**: public
- **Lines**: 445–448 (proof: 3 lines)
- **Notes**: None.

---

### `noncomputable def projPrincipalSubgroup`
- **Type**: `AddSubgroup (ProjectiveDivisor C)`
- **What**: The subgroup of principal projective divisors.
- **How**: Explicitly assembles carrier, `zero_mem'`, `add_mem'`, `neg_mem'` from `projIsPrincipal_zero`, `ProjIsPrincipal.add`, `ProjIsPrincipal.neg`.
- **Hypotheses**: None.
- **Uses from project**: `ProjIsPrincipal`, `projIsPrincipal_zero`, `ProjIsPrincipal.add`, `ProjIsPrincipal.neg`.
- **Used by**: `mem_projPrincipalSubgroup`, `ProjLinearlyEquiv` (via `ProjIsPrincipal`), `PicProj`, `PicProj₀`.
- **Visibility**: public
- **Lines**: 451–456
- **Notes**: None.

---

### `@[simp] theorem mem_projPrincipalSubgroup`
- **Type**: `D ∈ C.projPrincipalSubgroup ↔ C.ProjIsPrincipal D`
- **What**: Membership in `projPrincipalSubgroup` is `ProjIsPrincipal`.
- **How**: `Iff.rfl`.
- **Hypotheses**: None.
- **Uses from project**: `projPrincipalSubgroup`, `ProjIsPrincipal`.
- **Used by**: Unused within this file.
- **Visibility**: public
- **Lines**: 458–459 (proof: 1 line)
- **Notes**: Dead-code candidate within this file.

---

### `def ProjLinearlyEquiv`
- **Type**: `SmoothPlaneCurve F → ProjectiveDivisor C → ProjectiveDivisor C → Prop`
- **What**: Two projective divisors are linearly equivalent if their difference is principal.
- **How**: `C.ProjIsPrincipal (D₁ - D₂)`.
- **Hypotheses**: None.
- **Uses from project**: `ProjIsPrincipal`.
- **Used by**: `ProjLinearlyEquiv.refl`, `ProjLinearlyEquiv.symm`, `ProjLinearlyEquiv.trans`.
- **Visibility**: public
- **Lines**: 463–464
- **Notes**: None.

---

### `theorem ProjLinearlyEquiv.refl`
- **Type**: `C.ProjLinearlyEquiv D D`
- **What**: Linear equivalence is reflexive.
- **How**: `D - D = 0` via `simpa`, then `projIsPrincipal_zero`.
- **Hypotheses**: None.
- **Uses from project**: `ProjLinearlyEquiv`, `projIsPrincipal_zero`.
- **Used by**: Unused within this file.
- **Visibility**: public
- **Lines**: 466–469 (proof: 3 lines)
- **Notes**: Dead-code candidate within this file.

---

### `theorem ProjLinearlyEquiv.symm`
- **Type**: `C.ProjLinearlyEquiv D₁ D₂ → C.ProjLinearlyEquiv D₂ D₁`
- **What**: Linear equivalence is symmetric.
- **How**: Rewrites `D₂ - D₁ = -(D₁ - D₂)` via `abel`, then applies `ProjIsPrincipal.neg`.
- **Hypotheses**: `C.ProjLinearlyEquiv D₁ D₂`.
- **Uses from project**: `ProjLinearlyEquiv`, `ProjIsPrincipal.neg`.
- **Used by**: Unused within this file.
- **Visibility**: public
- **Lines**: 471–475 (proof: 4 lines)
- **Notes**: Dead-code candidate within this file.

---

### `theorem ProjLinearlyEquiv.trans`
- **Type**: `C.ProjLinearlyEquiv D₁ D₂ → C.ProjLinearlyEquiv D₂ D₃ → C.ProjLinearlyEquiv D₁ D₃`
- **What**: Linear equivalence is transitive.
- **How**: Rewrites `D₁ - D₃ = (D₁ - D₂) + (D₂ - D₃)` via `abel`, then applies `ProjIsPrincipal.add`.
- **Hypotheses**: `C.ProjLinearlyEquiv D₁ D₂`, `C.ProjLinearlyEquiv D₂ D₃`.
- **Uses from project**: `ProjLinearlyEquiv`, `ProjIsPrincipal.add`.
- **Used by**: Unused within this file.
- **Visibility**: public
- **Lines**: 477–482 (proof: 5 lines)
- **Notes**: Dead-code candidate within this file.

---

### `abbrev PicProj`
- **Type**: `SmoothPlaneCurve F → Type _`, defined as `ProjectiveDivisor C ⧸ C.projPrincipalSubgroup`
- **What**: The projective Picard group: quotient of the projective divisor group by the principal subgroup.
- **How**: `abbrev` unfolding to `QuotientAddGroup.quotient`.
- **Hypotheses**: None.
- **Uses from project**: `ProjectiveDivisor`, `projPrincipalSubgroup`.
- **Used by**: Unused within this file.
- **Visibility**: public
- **Lines**: 488–489
- **Notes**: Dead-code candidate within this file; foundational type for future work.

---

### `abbrev PicProj₀`
- **Type**: `SmoothPlaneCurve F → Type _`, defined as `(ProjectiveDivisor.degZero C) ⧸ (C.projPrincipalSubgroup.addSubgroupOf (ProjectiveDivisor.degZero C))`
- **What**: The degree-zero projective Picard group: quotient of degree-zero divisors by degree-zero principals.
- **How**: `abbrev` unfolding to a quotient of subgroups.
- **Hypotheses**: None.
- **Uses from project**: `ProjectiveDivisor.degZero`, `projPrincipalSubgroup`.
- **Used by**: Unused within this file.
- **Visibility**: public
- **Lines**: 492–494
- **Notes**: Dead-code candidate within this file; foundational type for future Pic⁰ correspondence.

---

### `theorem Polynomial.sum_rootMultiplicity_eq_natDegree`
- **Type**: `[IsAlgClosed F] → [DecidableEq F] → (p : Polynomial F) → ∑ a ∈ p.roots.toFinset, p.rootMultiplicity a = p.natDegree`
- **What**: For a polynomial over an algebraically closed field, the sum of root multiplicities over the root set equals the polynomial degree. (Polynomial avatar of the product formula.)
- **How**: Rewrites with `IsAlgClosed.card_roots_eq_natDegree`, `Multiset.toFinset_sum_count_eq`, and `Polynomial.count_roots`.
- **Hypotheses**: `F` algebraically closed, `DecidableEq F`.
- **Uses from project**: None (pure mathlib).
- **Used by**: `RatFunc.intDegree_eq_sum_sub_of_isAlgClosed`.
- **Visibility**: public
- **Lines**: 518–523 (proof: 4 lines)
- **Notes**: May overlap with mathlib; suspected to be near-mathlib content.

---

### `theorem RatFunc.intDegree_eq_sum_sub_of_isAlgClosed`
- **Type**: `[IsAlgClosed F] → [DecidableEq F] → (g : RatFunc F) → (g.intDegree : ℤ) = (∑ a ∈ g.num.roots.toFinset, ...) - (∑ a ∈ g.denom.roots.toFinset, ...)`
- **What**: For `g : RatFunc F` over an algebraically closed field, the integer degree equals the signed sum of root multiplicities (numerator minus denominator).
- **How**: Uses `RatFunc.intDegree`, applies `Polynomial.sum_rootMultiplicity_eq_natDegree` to numerator and denominator, then `push_cast; rfl`.
- **Hypotheses**: `F` algebraically closed, `DecidableEq F`.
- **Uses from project**: `Polynomial.sum_rootMultiplicity_eq_natDegree` (this file).
- **Used by**: Unused within this file (intended for Helper A/B chain).
- **Visibility**: public
- **Lines**: 528–537 (proof: 7 lines)
- **Notes**: Dead-code candidate within this file; intended as supporting infrastructure for Silverman II.3.1(b) via the Helper A product formula. Possible mathlib duplication or near-overlap.

---

## Cross-file reference summary

**Project declarations from `Divisors.lean` used in proofs**:
- `Divisor` (the `abbrev`)
- `Divisor.degree`, `Divisor.degreeHom`, `Divisor.degZero`, `Divisor.mem_degZero`
- `SmoothPlaneCurve.divisorOf`, `divisorOf_zero`, `divisorOf_one`, `divisorOf_mul`, `divisorOf_apply`
- `SmoothPlaneCurve.IsPrincipal`

**Project declarations from `Infinity.lean` (via `Divisors`)** assumed:
- `SmoothPlaneCurve.ordAtInfty`, `ordAtInfty_zero`, `ordAtInfty_one`, `ordAtInfty_mul`, `ordAtInfty_eq_top_iff`, `ordAtInfty_of_ne`

**Project declarations from elsewhere**:
- `SmoothPlaneCurve.ord_P` (from `OrdAtPoint`), `SmoothPlaneCurve.normAsRatFunc` (from `Basic` or `Divisors`)

---

## Statistics
- **Total declarations**: 51
- **Defs** (def/abbrev/noncomputable def): 15
- **Lemmas/theorems**: 34
- **Instances**: 1 (`DecidableEq`)
- **Sorries**: none
- **`set_option maxHeartbeats`**: none
- **Long proofs (>30 lines)**: none

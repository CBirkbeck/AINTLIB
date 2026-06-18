# Inventory: ./HasseWeil/DegreeQuadraticForm.lean

**File**: `HasseWeil/DegreeQuadraticForm.lean`
**Lines**: 658
**Imports**: `HasseWeil.DualIsogeny`, `HasseWeil.Endomorphism`, `HasseWeil.AdditionPullback`, `HasseWeil.EC.MulByIntAddRecurrence`

**Purpose**: Establishes the degree map as a positive-definite quadratic form (Silverman III.6.3). No `sorry` in any proof body; all declarations are axiom-clean.

---

## Declarations

### `private theorem quadratic_expansion`
- **Type**: `(α : Isogeny E E) (one_sub_α : Isogeny E E) (r s : ℤ) (h_sum_trace : α.toAddMonoidHom + (isogDual E α).toAddMonoidHom = (mulByInt E (isogTrace α one_sub_α)).toAddMonoidHom) → ∀ P : E.Point, (r • (isogDual E α).toAddMonoidHom - s • id) ((r • α.toAddMonoidHom - s • id) P) = ((α.degree : ℤ) * r² - isogTrace α one_sub_α * r * s + s²) • P`
- **What**: Pointwise algebraic expansion showing the composition `(rα̂ − s) ∘ (rα − s)` acts as the quadratic integer `d·r² − t·r·s + s²` on every point.
- **How**: Uses `isogDual_comp_self_apply` for `α̂ ∘ α = [deg α]`, `isogTrace_eq_dual` to express `α̂P = tP − αP`, then the `module` tactic for the final linear-algebra step.
- **Hypotheses**: Field `F`, `E.IsElliptic`, trace-sum identity at the `toAddMonoidHom` level.
- **Uses from project**: `isogDual`, `isogDual_comp_self_apply`, `isogTrace_eq_dual`, `isogTrace`, `mulByInt`
- **Used by**: Not called by any other declaration in this file (dead-code candidate — was superseded by `comp_toAddMonoidHom_eq_mulByInt_of_quadratic`).
- **Visibility**: private
- **Lines**: 55–79 (proof body ~15 lines)
- **Notes**: Private; appears to be the original algebra lemma that was refactored into `comp_toAddMonoidHom_eq_mulByInt_of_quadratic`. No longer called within the file; retained in source.

---

### `theorem comp_toAddMonoidHom_eq_mulByInt_of_quadratic`
- **Type**: Given `α α_dual : Isogeny E E`, `tr r s : ℤ`, `β β_dual : Isogeny E E` with `β.toAddMonoidHom = r • α − s • id` and `β_dual.toAddMonoidHom = r • α_dual − s • id`, plus dual-composition and trace-sum hypotheses, concludes `(β_dual.comp β).toAddMonoidHom = (mulByInt E N).toAddMonoidHom` where `N = (α.degree)·r² − tr·r·s + s²`.
- **What**: Packages the quadratic algebraic expansion as an `AddMonoidHom` equality, taking the dual `α_dual` as an explicit witness instead of using `isogDual` (avoids the `exists_dual` gate).
- **How**: `Isogeny.comp_toAddMonoidHom` + `AddMonoidHom.comp_apply` to unfold; then re-runs the same pointwise algebra as `quadratic_expansion` using `h_dual_comp` and `h_sum_trace`; `module` closes the linear-algebra step.
- **Hypotheses**: `toAddMonoidHom`-level dual-composition `α_dual ∘ α = [deg α]` and trace-sum `α + α_dual = [tr]`.
- **Uses from project**: `Isogeny.comp_toAddMonoidHom`, `mulByInt`
- **Used by**: `degree_quadratic_closed` (line 479)
- **Visibility**: public
- **Lines**: 100–132 (proof body ~33 lines)
- **Notes**: Proof is 33 lines (just over the 30-line threshold). No `set_option`. Replaces the private `quadratic_expansion` with a more general witness-parametric form.

---

### `theorem degree_quadratic_nonneg_of_witness`
- **Type**: `(α one_sub_α β : Isogeny E E) (r s : ℤ) (h_deg_eq : (β.degree : ℤ) = (α.degree : ℤ) * r² − (isogTrace α one_sub_α) * r * s + s²) → 0 ≤ (α.degree : ℤ) * r² − (isogTrace α one_sub_α) * r * s + s²`
- **What**: The non-negativity of the quadratic form value, given the degree equality as an explicit hypothesis (parametric on the III.6.3 witness).
- **How**: Rewrites by `h_deg_eq` then uses `Int.natCast_nonneg` (degree is a natural number cast to ℤ).
- **Hypotheses**: Degree equality at the integer level.
- **Uses from project**: `isogTrace`
- **Used by**: Not called by any other declaration in this file.
- **Visibility**: public
- **Lines**: 162–169 (proof body 2 lines)
- **Notes**: Extremely short; exists as a standalone bridge for callers that already have the III.6.3 degree identity.

---

### `theorem signed_degree_of_isDualOf_and_comp_eq`
- **Type**: `{W : WeierstrassCurve F} (α β : Isogeny W.toAffine W.toAffine) (N : ℤ) (hN : N ≠ 0) (h_isDual : IsDualOf W.toAffine β α) (h_alpha_pos : 0 < α.degree) (h_comp_eq : β.comp α = mulByInt W.toAffine N) → (α.degree : ℤ) = N`
- **What**: Extracts the signed degree identity from an `IsDualOf` witness plus a composition equality, using injectivity of `mulByInt` (Wall C / `mulByInt_left_injective`).
- **How**: `IsDualOf.1` gives `β.comp α = mulByInt α.degree`; chained with `h_comp_eq` yields `mulByInt (α.degree) = mulByInt N`, then `mulByInt_left_injective` extracts equality.
- **Hypotheses**: `IsDualOf β α`, `0 < α.degree`, `β.comp α = mulByInt N`, `N ≠ 0`.
- **Uses from project**: `IsDualOf`, `mulByInt`, `mulByInt_left_injective`
- **Used by**: `signed_degree_of_genuine_dual_pair` (line 240)
- **Visibility**: public
- **Lines**: 202–215 (proof body ~6 lines)
- **Notes**: Acts as a subroutine to the specialised pair form below.

---

### `theorem signed_degree_of_genuine_dual_pair`
- **Type**: `{W : WeierstrassCurve F} (β β_dual : Isogeny W.toAffine W.toAffine) (N : ℤ) (hN : N ≠ 0) (h_isDual : IsDualOf W.toAffine β_dual β) (h_beta_pos : 0 < β.degree) (h_comp_eq : β_dual.comp β = mulByInt W.toAffine N) → (β.degree : ℤ) = N`
- **What**: Specialisation of `signed_degree_of_isDualOf_and_comp_eq` for the genuine `r·π − s·id` family, with roles relabelled for readability.
- **How**: One-line delegation to `signed_degree_of_isDualOf_and_comp_eq`.
- **Hypotheses**: Same as the general form above, applied with `β` in the role of `α`.
- **Uses from project**: `IsDualOf`, `mulByInt`, `signed_degree_of_isDualOf_and_comp_eq`
- **Used by**: Not called by any other declaration in this file.
- **Visibility**: public
- **Lines**: 233–240 (proof body 1 line)
- **Notes**: Thin wrapper; may be unused in file.

---

### `theorem sq_degree_eq_sq_of_dual_comp_witness`
- **Type**: `(β β_dual : Isogeny E E) (N : ℤ) (hN : N ≠ 0) (h_comp : β_dual.comp β = mulByInt E N) (h_dual_deg : β_dual.degree = β.degree) → (β.degree : ℤ)² = N²`
- **What**: From the dual-composition equality at the full isogeny level and `β_dual.degree = β.degree`, derives `deg(β)² = N²` in ℤ.
- **How**: Uses `Isogeny.comp_degree` to expand composition degree, `mulByInt_degree` to compute `(mulByInt N).degree = (N²).toNat`, casts via `Int.toNat_of_nonneg`, then rewrites with `ring`.
- **Hypotheses**: Isogeny-level composition equality, degree symmetry, `N ≠ 0`.
- **Uses from project**: `Isogeny.comp_degree`, `mulByInt_degree`, `mulByInt`
- **Used by**: `degree_eq_abs_of_dual_comp_witness` (line 275)
- **Visibility**: public
- **Lines**: 249–266 (proof body ~18 lines)
- **Notes**: None.

---

### `theorem degree_eq_abs_of_dual_comp_witness`
- **Type**: `(β β_dual : Isogeny E E) (N : ℤ) (hN : N ≠ 0) (h_comp : β_dual.comp β = mulByInt E N) (h_dual_deg : β_dual.degree = β.degree) → (β.degree : ℤ) = |N|`
- **What**: Extracts the absolute-value degree identity: given the squared-degree equality and both factors being non-negative, concludes `deg(β) = |N|`.
- **How**: Calls `sq_degree_eq_sq_of_dual_comp_witness` for `deg(β)² = N²`; then `mul_eq_zero` on the difference-product `(deg − |N|)(deg + |N|) = 0`; both cases give linarith contradictions except the positive root `deg = |N|`.
- **Hypotheses**: Same as `sq_degree_eq_sq_of_dual_comp_witness`.
- **Uses from project**: `sq_degree_eq_sq_of_dual_comp_witness`, `mulByInt`
- **Used by**: `degree_quadratic_of_dualChain_witnesses` (line 321)
- **Visibility**: public
- **Lines**: 270–289 (proof body ~20 lines)
- **Notes**: None.

---

### `theorem degree_quadratic_of_dualChain_witnesses`
- **Type**: `(α one_sub_α β β_dual : Isogeny E E) (r s : ℤ) (h_N_ne : N ≠ 0) (h_comp : β_dual.comp β = mulByInt E N) (h_dual_deg : β_dual.degree = β.degree) (h_nonneg_N : 0 ≤ N) → (β.degree : ℤ) = N` where `N = (α.degree)·r² − (tr α)·r·s + s²`.
- **What**: Closes the III.6.3 degree identity from the full isogeny-level dual-composition witness plus non-negativity; the strong form requiring `N ≠ 0`.
- **How**: Uses `degree_eq_abs_of_dual_comp_witness` to get `deg(β) = |N|`, then `abs_of_nonneg` to strip the absolute value.
- **Hypotheses**: Isogeny-level composition equality, degree symmetry, non-negativity, `N ≠ 0`.
- **Uses from project**: `degree_eq_abs_of_dual_comp_witness`, `isogTrace`, `mulByInt`
- **Used by**: Not called by any other declaration in this file.
- **Visibility**: public
- **Lines**: 307–323 (proof body ~7 lines)
- **Notes**: Not called within this file; intended for external consumers once witness chain ships.

---

### `theorem sq_degree_eq_sq_of_dual_deg_prod_witness`
- **Type**: `(β β_dual : Isogeny E E) (N : ℤ) (h_deg_prod : β.degree * β_dual.degree = (N²).toNat) (h_dual_deg : β_dual.degree = β.degree) → (β.degree : ℤ)² = N²`
- **What**: Degree-level variant: derives `deg(β)² = N²` from a product-of-degrees identity, without needing the full isogeny equality.
- **How**: Substitutes `h_dual_deg` to get `deg(β)² = (N²).toNat` as naturals, casts via `Int.toNat_of_nonneg` and `ring`.
- **Hypotheses**: Product of degrees equals `(N²).toNat`, degree symmetry.
- **Uses from project**: (none beyond basic arithmetic)
- **Used by**: `sq_degree_eq_sq_of_comp_deg_witness` (line 374), `degree_eq_abs_of_dual_deg_prod_witness` (line 387)
- **Visibility**: public
- **Lines**: 351–363 (proof body ~13 lines)
- **Notes**: None.

---

### `theorem sq_degree_eq_sq_of_comp_deg_witness`
- **Type**: `(β β_dual : Isogeny E E) (N : ℤ) (h_comp_deg : (β_dual.comp β).degree = (N²).toNat) (h_dual_deg : β_dual.degree = β.degree) → (β.degree : ℤ)² = N²`
- **What**: Alternative form taking the composition's degree directly; chains via `Isogeny.comp_degree` to reduce to the product form.
- **How**: One-line: `sq_degree_eq_sq_of_dual_deg_prod_witness` with `(Isogeny.comp_degree β_dual β).symm.trans h_comp_deg`.
- **Hypotheses**: Composition degree equals `(N²).toNat`, degree symmetry.
- **Uses from project**: `Isogeny.comp_degree`, `sq_degree_eq_sq_of_dual_deg_prod_witness`
- **Used by**: Not called by any other declaration in this file.
- **Visibility**: public
- **Lines**: 369–375 (proof body ~2 lines)
- **Notes**: Thin wrapper.

---

### `theorem degree_eq_abs_of_dual_deg_prod_witness`
- **Type**: `(β β_dual : Isogeny E E) (N : ℤ) (h_deg_prod : β.degree * β_dual.degree = (N²).toNat) (h_dual_deg : β_dual.degree = β.degree) → (β.degree : ℤ) = |N|`
- **What**: Degree-level version of `degree_eq_abs_of_dual_comp_witness`; does not require `N ≠ 0` (the `N = 0` case forces `β.degree = 0 = |N|`).
- **How**: Calls `sq_degree_eq_sq_of_dual_deg_prod_witness`; then `mul_eq_zero` on the difference-product with `linarith` for both cases.
- **Hypotheses**: Product-of-degrees equals `(N²).toNat`, degree symmetry.
- **Uses from project**: `sq_degree_eq_sq_of_dual_deg_prod_witness`
- **Used by**: `degree_quadratic_of_dualChain_deg_witnesses` (line 423)
- **Visibility**: public
- **Lines**: 382–401 (proof body ~20 lines)
- **Notes**: None.

---

### `theorem degree_quadratic_of_dualChain_deg_witnesses`
- **Type**: Same conclusion as `degree_quadratic_of_dualChain_witnesses` but takes a product-of-degrees hypothesis instead of a full isogeny composition equality; also does not require `N ≠ 0`.
- **What**: Degree-level closure of III.6.3 from a weaker (product-of-degrees) witness plus non-negativity.
- **How**: Uses `degree_eq_abs_of_dual_deg_prod_witness` then `abs_of_nonneg`.
- **Hypotheses**: Product of degrees equals `(N²).toNat`, degree symmetry, `N ≥ 0`.
- **Uses from project**: `degree_eq_abs_of_dual_deg_prod_witness`, `isogTrace`
- **Used by**: `degree_quadratic_closed` (line 487)
- **Visibility**: public
- **Lines**: 411–425 (proof body ~15 lines)
- **Notes**: None.

---

### `theorem degree_quadratic_closed`
- **Type**: Given `α α_dual one_sub_α β β_dual : Isogeny E E` and `r s : ℤ` with `hβ_hom`, `hβ_dual_hom` (witness hom equalities), `h_dual_comp`, `h_sum_trace`, `h_deg_bridge`, `h_dual_deg`, `h_nonneg_N`, concludes `(β.degree : ℤ) = (α.degree : ℤ) * r² − (isogTrace α one_sub_α) * r * s + s²`.
- **What**: The T-III-6-009 composite call site that closes the III.6.3 degree identity from a complete III.6 witness bundle at the `AddMonoidHom` level. Chains `comp_toAddMonoidHom_eq_mulByInt_of_quadratic` → `h_deg_bridge` → `degree_quadratic_of_dualChain_deg_witnesses`.
- **How**: Applies `comp_toAddMonoidHom_eq_mulByInt_of_quadratic` to get the composition hom equality, feeds it through `h_deg_bridge` to get the degree equality, then delegates to `degree_quadratic_of_dualChain_deg_witnesses`.
- **Hypotheses**: Full witness bundle at `AddMonoidHom` level including a `toAddMonoidHom → degree` bridge hypothesis.
- **Uses from project**: `comp_toAddMonoidHom_eq_mulByInt_of_quadratic`, `degree_quadratic_of_dualChain_deg_witnesses`, `isogTrace`, `Isogeny.comp_degree`
- **Used by**: `degree_quadratic_genuine_addIsog` (line 640)
- **Visibility**: public
- **Lines**: 457–488 (proof body ~32 lines)
- **Notes**: Proof is 32 lines (over 30-line threshold). No `sorry`.

---

### `theorem trace_identity_of_dual_chain`
- **Type**: Given `α α_dual one_sub_α one_sub_α_dual : Isogeny E E` and point-map hypotheses (`h_dual_comp_right`, `h_one_sub_α_hom`, `h_one_sub_α_dual_hom`, `h_one_sub_one_sub_dual`), concludes `α.toAddMonoidHom + α_dual.toAddMonoidHom = (mulByInt E (isogTrace α one_sub_α)).toAddMonoidHom`.
- **What**: Derives the trace identity `α + α̂ = [tr α]` at the `toAddMonoidHom` level from the dual-composition halves (including `(1−α) ∘ (1−α̂) = [deg(1−α)]`), bypassing universal dual additivity.
- **How**: Expands `(1−α_dual)` and `(1−α)` via their hom definitions, applies `h_one_sub_one_sub_dual`, and uses `h_dual_comp_right` to recover `(α.degree)·P`; then unfolds `isogTrace` and closes with `abel`.
- **Hypotheses**: Two "one-minus" hom identities at `AddMonoidHom` level, composition identity for `(1−α) ∘ (1−α̂) = [deg(1−α)]`, and one half of `IsDualOf`.
- **Uses from project**: `mulByInt`, `mulByInt_apply`, `isogTrace`
- **Used by**: Not called by any other declaration in this file.
- **Visibility**: public
- **Lines**: 559–592 (proof body ~34 lines)
- **Notes**: Proof is 34 lines (over 30-line threshold). The hypothesis `h_one_sub_one_sub_dual` is the substantive Hasse-critical content; labelled as being discharged by Worker C's Frobenius-specific dual chain.

---

### `theorem degree_quadratic_genuine_addIsog`
- **Type**: For genuine `addIsog`-built isogenies `β = addIsog hxy_β hinj_β` and `β_dual = addIsog hxy_β_dual hinj_β_dual` (with `α.zsmul r` and `mulByInt (-s)` components), given the III.6 witness bundle (dual-comp, trace-sum, deg-bridge, dual-deg, nonneg), concludes `((addIsog hxy_β hinj_β).degree : ℤ) = (α.degree : ℤ) * r² − (isogTrace α one_sub_α) * r * s + s²`.
- **What**: Silverman III.6.3 specialised to the genuine `r·α − s·id` family built by `addIsog`; auto-discharges `hβ_hom`/`hβ_dual_hom` via `addIsog_toAddMonoidHom` and `Isogeny.zsmul_apply`.
- **How**: Calls `degree_quadratic_closed` via `refine`; discharges both `hβ_hom` and `hβ_dual_hom` cases with `simp [addIsog_toAddMonoidHom, …]` + `rw [neg_smul, sub_eq_add_neg]`.
- **Hypotheses**: `AddNonInversePair` witnesses for both `β` and `β_dual`, plus the standard III.6 inputs.
- **Uses from project**: `addIsog`, `addIsog_toAddMonoidHom`, `addCoordAlgHomPair`, `AddNonInversePair`, `Isogeny.zsmul_apply`, `mulByInt_apply`, `degree_quadratic_closed`, `isogTrace`
- **Used by**: Not called by any other declaration in this file.
- **Visibility**: public
- **Lines**: 617–655 (proof body ~39 lines)
- **Notes**: Proof is 39 lines (over 30-line threshold). References `hxy_β`, `hinj_β`, `addIsog`, `addCoordAlgHomPair` from `AdditionPullback`.

---

## Summary

| Name | Kind | Lines | Proof length | Used by (in file) |
|------|------|-------|-------------|-------------------|
| `quadratic_expansion` | private theorem | 55–79 | 25 | nobody (dead) |
| `comp_toAddMonoidHom_eq_mulByInt_of_quadratic` | theorem | 100–132 | 33 | `degree_quadratic_closed` |
| `degree_quadratic_nonneg_of_witness` | theorem | 162–169 | 8 | nobody |
| `signed_degree_of_isDualOf_and_comp_eq` | theorem | 202–215 | 14 | `signed_degree_of_genuine_dual_pair` |
| `signed_degree_of_genuine_dual_pair` | theorem | 233–240 | 8 | nobody |
| `sq_degree_eq_sq_of_dual_comp_witness` | theorem | 249–266 | 18 | `degree_eq_abs_of_dual_comp_witness` |
| `degree_eq_abs_of_dual_comp_witness` | theorem | 270–289 | 20 | `degree_quadratic_of_dualChain_witnesses` |
| `degree_quadratic_of_dualChain_witnesses` | theorem | 307–323 | 17 | nobody |
| `sq_degree_eq_sq_of_dual_deg_prod_witness` | theorem | 351–363 | 13 | `sq_degree_eq_sq_of_comp_deg_witness`, `degree_eq_abs_of_dual_deg_prod_witness` |
| `sq_degree_eq_sq_of_comp_deg_witness` | theorem | 369–375 | 7 | nobody |
| `degree_eq_abs_of_dual_deg_prod_witness` | theorem | 382–401 | 20 | `degree_quadratic_of_dualChain_deg_witnesses` |
| `degree_quadratic_of_dualChain_deg_witnesses` | theorem | 411–425 | 15 | `degree_quadratic_closed` |
| `degree_quadratic_closed` | theorem | 457–488 | 32 | `degree_quadratic_genuine_addIsog` |
| `trace_identity_of_dual_chain` | theorem | 559–592 | 34 | nobody |
| `degree_quadratic_genuine_addIsog` | theorem | 617–655 | 39 | nobody |

**Total declarations**: 15 (14 public + 1 private)
**Defs**: 0 | **Lemmas/Theorems**: 15 | **Instances**: 0 | **Sorries**: none

**keyApi** (used by 3+ others): `sq_degree_eq_sq_of_dual_deg_prod_witness` is used by 2 others; no declaration is used by 3 or more.

**Long proofs** (>30 lines): `comp_toAddMonoidHom_eq_mulByInt_of_quadratic` (33 lines), `degree_quadratic_closed` (32 lines), `trace_identity_of_dual_chain` (34 lines), `degree_quadratic_genuine_addIsog` (39 lines).

**Dead-code candidates** (unused in file): `quadratic_expansion` (private, superseded), `degree_quadratic_nonneg_of_witness`, `signed_degree_of_genuine_dual_pair`, `degree_quadratic_of_dualChain_witnesses`, `sq_degree_eq_sq_of_comp_deg_witness`, `trace_identity_of_dual_chain`, `degree_quadratic_genuine_addIsog`.

**No `set_option maxHeartbeats`** in file.

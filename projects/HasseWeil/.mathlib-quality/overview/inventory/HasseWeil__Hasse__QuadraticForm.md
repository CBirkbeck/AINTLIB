# Inventory: ./HasseWeil/Hasse/QuadraticForm.lean

**File**: `HasseWeil/Hasse/QuadraticForm.lean`
**Lines**: 591
**Imports**: `HasseWeil.HasseBound`, `HasseWeil.Hasse.PointFix`, `HasseWeil.DegreeQuadraticForm`, `HasseWeil.AdditionPullback.Frobenius`
**Total declarations**: 13 theorems (no defs, no instances)

---

## Summary

This file ships the "non-negativity form" of the Hasse bound argument: instead of
carrying a specific isogeny family with a degree-equality witness, the main results
accept a bare `∀ r s : ℤ, 0 ≤ q·r² − t·r·s + s²` hypothesis. The file also
contains the structural decomposition of `qf_nonneg` — edge cases, the
polarisation-witness form, and the single isolated `sorry` isolating the irreducible
geometric pivot (Silverman III.6.2).

---

### `theorem traceOfFrobenius_sq_le_of_qf_nonneg`
- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] (t : ℤ) (h_qf_nonneg : ∀ r s : ℤ, 0 ≤ (Fintype.card K : ℤ) * r ^ 2 - t * r * s + s ^ 2) : t ^ 2 ≤ 4 * (Fintype.card K : ℤ)`
- **What**: Proves the discriminant bound t² ≤ 4q given non-negativity of the integer quadratic form q·r² − t·r·s + s², with no isogeny family parameter.
- **How**: Direct one-liner delegating to `trace_sq_le_four_mul_deg` from `HasseBound.lean`, passing `Fintype.card_pos` for the positivity side-condition.
- **Hypotheses**: Elliptic curve over a finite field K; QF non-negativity for all integer r, s.
- **Uses from project**: `trace_sq_le_four_mul_deg` (HasseBound.lean)
- **Used by**: `hasse_bound_of_qf_nonneg_witnesses`, `hasse_bound_sq_of_qf_nonneg_witnesses` (both in this file)
- **Visibility**: public
- **Lines**: 50–56, proof = 1 line
- **Notes**: None

---

### `theorem hasse_bound_of_qf_nonneg_witnesses`
- **Type**: `(W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point] (t : ℤ) (h_pc : (pointCount W.toAffine : ℤ) = Fintype.card K + 1 - t) (h_qf_nonneg : ∀ r s : ℤ, 0 ≤ q·r² − t·r·s + s²) : |#E − q − 1| ≤ 2√q`
- **What**: Full Hasse bound |#E(F_q) − q − 1| ≤ 2√q, taking point-count formula and QF non-negativity as explicit hypotheses.
- **How**: Converts the integer identity `#E − q − 1 = −t` to reals via `exact_mod_cast`, rewrites the absolute value of −t, then applies `abs_le_two_sqrt_of_sq_le` fed by `traceOfFrobenius_sq_le_of_qf_nonneg`.
- **Hypotheses**: Elliptic curve over finite K with finitely many points; point-count formula `#E = q + 1 − t`; QF non-negativity.
- **Uses from project**: `traceOfFrobenius_sq_le_of_qf_nonneg` (this file), `abs_le_two_sqrt_of_sq_le` (HasseBound.lean), `pointCount` (HasseBound.lean)
- **Used by**: `hasse_bound_of_full_qf_nonneg_witnesses` (this file)
- **Visibility**: public
- **Lines**: 61–74, proof = 7 lines
- **Notes**: None

---

### `theorem hasse_bound_sq_of_qf_nonneg_witnesses`
- **Type**: `... : ((pointCount W.toAffine : ℤ) - Fintype.card K - 1) ^ 2 ≤ 4 * (Fintype.card K : ℤ)`
- **What**: Squared form of the Hasse bound, i.e. (#E − q − 1)² ≤ 4q.
- **How**: Rewrites `#E − q − 1 = −t` by `linarith`, then `neg_sq` removes the sign, finally applies `traceOfFrobenius_sq_le_of_qf_nonneg`.
- **Hypotheses**: Same as `hasse_bound_of_qf_nonneg_witnesses`.
- **Uses from project**: `traceOfFrobenius_sq_le_of_qf_nonneg` (this file)
- **Used by**: `hasse_bound_sq_of_all_qf_nonneg_witnesses` (this file)
- **Visibility**: public
- **Lines**: 77–87, proof = 5 lines
- **Notes**: None

---

### `theorem hasse_bound_of_full_qf_nonneg_witnesses`
- **Type**: Takes `β_pc : Isogeny`, `h_pc_hom`, `h_pc_ker_deg`, `h_qf_nonneg` (with t = `isogTrace π β_pc`) and concludes `|#E − q − 1| ≤ 2√q`
- **What**: Chains the point-count derivation from the (1−π) isogeny `β_pc` into the non-negativity form; replaces the QF isogeny-family + degree-equality witness by a bare non-negativity hypothesis with t computed as `isogTrace`.
- **How**: Calls `pointCount_eq_of_hom_kernel_witness` to produce the `h_pc` hypothesis, then delegates to `hasse_bound_of_qf_nonneg_witnesses`.
- **Hypotheses**: `β_pc` an isogeny with hom = id − π, kernel cardinality = degree; QF non-negativity with trace t = isogTrace(π, β_pc).
- **Uses from project**: `hasse_bound_of_qf_nonneg_witnesses` (this file), `pointCount_eq_of_hom_kernel_witness` (PointFix.lean), `isogTrace` (DegreeQuadraticForm or HasseBound), `frobeniusIsog` (Frobenius)
- **Used by**: `hasse_bound_of_all_qf_nonneg_witnesses` (this file)
- **Visibility**: public
- **Lines**: 93–106, proof = 3 lines (term-mode)
- **Notes**: None

---

### `theorem hasse_bound_of_all_qf_nonneg_witnesses`
- **Type**: Takes `β_pc`, separability + finite-dimensionality + fibre-witness data, plus QF non-negativity; concludes `|#E − q − 1| ≤ 2√q`
- **What**: Consolidated Hasse bound matching the hypothesis list of `hasse_bound_of_all_witnesses` but replacing the QF isogeny family by the bare QF non-negativity.
- **How**: Calls `Isogeny.card_kernel_eq_degree_of_separable_witness` to produce `h_pc_ker_deg` from separability data, then delegates to `hasse_bound_of_full_qf_nonneg_witnesses`.
- **Hypotheses**: Elliptic curve over finite K; `β_pc` separable isogeny with hom = id − π, finite-dimensional function field extension, fibre-card witness, finite kernel; QF non-negativity.
- **Uses from project**: `hasse_bound_of_full_qf_nonneg_witnesses` (this file), `Isogeny.card_kernel_eq_degree_of_separable_witness` (IsogenyKernel or similar), `pointCount_eq_of_hom_kernel_witness` (transitively)
- **Used by**: `HoleE.lean` (external consumer via `hasse_bound_of_all_qf_nonneg_witnesses`)
- **Visibility**: public
- **Lines**: 113–134, proof = 4 lines (term-mode)
- **Notes**: None

---

### `theorem qf_nonneg_of_genuine_chain`
- **Type**: Takes `β_pc`, a family `β : ℤ → ℤ → Isogeny` with `h_β_deg : ∀ r s, (β r s).degree = q·r² − t·r·s + s²`; concludes `∀ r s, 0 ≤ q·r² − t·r·s + s²`
- **What**: Discharges QF non-negativity from a family of isogenies `β r s` whose degree equals the quadratic-form value, using the fact that `Isogeny.degree : ℕ` is non-negative.
- **How**: Rewrites by `h_β_deg r s`, then applies `Int.natCast_nonneg`.
- **Hypotheses**: A family β of isogenies parametrised by (r, s : ℤ) with degree matching the QF expression.
- **Uses from project**: None (aside from `isogTrace`, `frobeniusIsog` in type)
- **Used by**: `qf_nonneg_via_frobenius_polarisation` (this file)
- **Visibility**: public
- **Lines**: 155–166, proof = 4 lines
- **Notes**: Extremely short; the key content is delegated to the caller who must supply the degree identity.

---

### `theorem qf_nonneg_via_frobenius_polarisation`
- **Type**: Takes Worker B's `addIsog` injectivity witnesses for the `r·π − s` and `r·V − s` families, Worker C's dual chain data (`h_dual_comp`, `h_sum_trace`, `h_deg_bridge`, `h_dual_deg`, `h_nonneg_N`); concludes `∀ r s, 0 ≤ q·r² − t·r·s + s²`
- **What**: Discharges `qf_nonneg` from the full Frobenius polarisation chain: the degree of `r·π − s` equals the QF value by Silverman III.6.3, so non-negativity is immediate.
- **How**: Rewrites `(frobeniusIsog W).degree = Fintype.card K` via `frobeniusIsog_degree`, then calls `qf_nonneg_of_genuine_chain` with the `addIsog (hxy_β r s) (hinj_β r s)` family, using `degree_quadratic_genuine_addIsog` to produce the degree hypothesis.
- **Hypotheses**: Worker B injectivity witnesses for both π-side and V-side isogenies; V ∘ π = [q] pointwise (`h_dual_comp`); trace sum identity (`h_sum_trace`); hom→degree implication (`h_deg_bridge`); V-side equals π-side degree (`h_dual_deg`); V-side non-negativity hypothesis (`h_nonneg_N`).
- **Uses from project**: `qf_nonneg_of_genuine_chain` (this file), `degree_quadratic_genuine_addIsog` (DegreeQuadraticForm.lean), `frobeniusIsog_degree` (FrobeniusIsogeny or AdditionPullback.Frobenius), `addIsog` (AdditionPullback.lean)
- **Used by**: Unused within this file (designed as the canonical discharger for external consumers)
- **Visibility**: public
- **Lines**: 190–235, proof = 11 lines
- **Notes**: Carries several universally-quantified witness hypotheses that are the responsibility of Workers B and C; the wrapper skeleton mentioned in comments (T9+T4 unconditional) is absent from this file.

---

### `theorem genuineIsogSmulSub_degree_eq_quadratic_form`
- **Type**: Takes `V : Isogeny`, `hV : IsDualOf V π`, `h_sum_trace`, `(r s : ℤ)` nonzero in K and ℤ, plus V-side `addIsog` witnesses; concludes `(genuineIsogSmulSub W r s …).degree = q·r² − t·r·s + s²`
- **What**: For a specific (r, s) pair with r, s ≠ 0 in both ℤ and K, proves the III.6.3 degree identity for `r·π − s` (the `genuineIsogSmulSub` isogeny) given the Verschiebung dual V and trace sum.
- **How**: Three-step proof: (1) derives `h_dual_comp` (V∘π = [q]) from `hV.1` via `congrArg Isogeny.toAddMonoidHom` + `DFunLike.congr_fun` + `Isogeny.comp_apply` + `mulByInt_apply`; (2) unfolds `genuineIsogSmulSub = addIsog hxy_β hinj_β` using `AddNonInversePair_zsmul_frobenius_mulByInt_neg` and `addCoordAlgHomPair_injective_zsmul_frobenius_mulByInt_neg_of_pole` with the pole bound from `ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg`; (3) applies `degree_quadratic_genuine_addIsog` with conversion via `frobeniusIsog_degree`.
- **Hypotheses**: |K| ≥ 2; Verschiebung V with IsDualOf; trace sum identity; r, s nonzero in ℤ and K; V-side AddNonInversePair + injectivity; h_deg_bridge + h_dual_deg + h_nonneg_N witnesses.
- **Uses from project**: `degree_quadratic_genuine_addIsog` (DegreeQuadraticForm.lean), `frobeniusIsog_degree`, `genuineIsogSmulSub` (AdditionPullback.Frobenius), `addIsog`, `AddNonInversePair_zsmul_frobenius_mulByInt_neg`, `addCoordAlgHomPair_injective_zsmul_frobenius_mulByInt_neg_of_pole`, `ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg`, `isogOneSub_negFrobenius`, `mulByInt_apply`, `Isogeny.comp_apply`
- **Used by**: `genuineIsogSmulSub_degree_eq_quadratic_form_minimal` (this file)
- **Visibility**: public
- **Lines**: 254–338, proof = 50 lines (289–338)
- **Notes**: **Long proof (50 lines).** The `set` tactic is used to name `hxy_β` and `hinj_β` from their construction lemmas; the `rfl` step unfolding `genuineIsogSmulSub` is load-bearing. The proof must thread `frobeniusIsog_degree` rewrites through the h_deg_bridge and h_nonneg_N hypotheses in both directions.

---

### `theorem genuineIsogSmulSub_pivot_witness`
- **Type**: `(W, hq, r, s, hr, hs, hrK, hsK) → ∃ β_dual : Isogeny, IsDualOf β_dual (genuineIsogSmulSub …) ∧ β_dual.comp (genuineIsogSmulSub …) = mulByInt W N ∧ 0 < (genuineIsogSmulSub …).degree ∧ N ≠ 0`  where `N = q·r² − t·r·s + s²`
- **What**: Asserts existence of a genuine dual isogeny β_dual of `r·π − s` with the full-isogeny composition `β_dual ∘ (r·π − s) = [N]`, plus positivity of the degree and nonzero N. This packages the irreducible Silverman III.6.2(b/c) geometric content.
- **How**: **`sorry`** — this is the single open irreducible residual in the file. The docstring explains why: the degree identity for `genuineIsogSmulSub` cannot be derived from point-map / Pic⁰ data alone because the isogeny is generically inseparable.
- **Hypotheses**: |K| ≥ 2; r, s nonzero in ℤ and K.
- **Uses from project**: `genuineIsogSmulSub` (AdditionPullback.Frobenius), `isogOneSub_negFrobenius`, `isogTrace`, `frobeniusIsog`, `IsDualOf`, `mulByInt`
- **Used by**: `genuineIsogSmulSub_degree_eq_quadratic_form_minimal` (this file)
- **Visibility**: public
- **Lines**: 437–451, proof = 1 line (sorry)
- **Notes**: **Contains `sorry`.** Thoroughly documented as the irreducible Wall A/B content (V-side pole bound + double-Vieta pullback match). The same residual gates `genuineIsogSmulSub_degree_eq_signed` in `GapSpines.lean`. Tracked as `[T-QF-PIVOT-FULL]`.

---

### `theorem genuineIsogSmulSub_degree_eq_quadratic_form_minimal`
- **Type**: `(W, hq, r, s, hr, hs, hrK, hsK) → ((genuineIsogSmulSub W r s …).degree : ℤ) = q·r² − t·r·s + s²`
- **What**: Minimal-signature form of the III.6.3 degree identity for `r·π − s`, taking only nonzero-in-K hypotheses and no additional witness arguments.
- **How**: Calls `genuineIsogSmulSub_pivot_witness` to obtain `(β_dual, h_isDual, h_comp_eq, h_beta_pos, h_N_ne)`, then applies the shipped `signed_degree_of_genuine_dual_pair` (Wall C, mulByInt injectivity on the pullback).
- **Hypotheses**: |K| ≥ 2; r, s nonzero in ℤ and K. (But inherits sorry from `genuineIsogSmulSub_pivot_witness`.)
- **Uses from project**: `genuineIsogSmulSub_pivot_witness` (this file), `signed_degree_of_genuine_dual_pair` (DegreeQuadraticForm.lean), `genuineIsogSmulSub`
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 463–479, proof = 9 lines
- **Notes**: **Transitively contains `sorry`** via `genuineIsogSmulSub_pivot_witness`. This is the T14 minimal-signature target.

---

### `theorem hasse_bound_sq_of_all_qf_nonneg_witnesses`
- **Type**: Same hypotheses as `hasse_bound_of_all_qf_nonneg_witnesses`; concludes squared form `((#E : ℤ) − q − 1)² ≤ 4q`
- **What**: Squared variant of the consolidated Hasse bound.
- **How**: Calls `Isogeny.card_kernel_eq_degree_of_separable_witness` then `hasse_bound_sq_of_qf_nonneg_witnesses` and `pointCount_eq_of_hom_kernel_witness` in term-mode.
- **Hypotheses**: Same as `hasse_bound_of_all_qf_nonneg_witnesses`.
- **Uses from project**: `hasse_bound_sq_of_qf_nonneg_witnesses` (this file), `Isogeny.card_kernel_eq_degree_of_separable_witness`, `pointCount_eq_of_hom_kernel_witness`
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 482–504, proof = 4 lines (term-mode)
- **Notes**: None

---

### `theorem qf_nonneg_universal_edge_r_zero`
- **Type**: `(W, {hq}, s : ℤ) → 0 ≤ q·0² − t·0·s + s²`
- **What**: Edge case: when r = 0, the QF collapses to s², which is non-negative.
- **How**: `ring_nf` simplifies the expression to `s^2`, then `sq_nonneg s`.
- **Hypotheses**: |K| ≥ 2 (implicit, needed for `isogOneSub_negFrobenius`).
- **Uses from project**: `isogOneSub_negFrobenius`, `isogTrace`, `frobeniusIsog` (in type only)
- **Used by**: `qf_nonneg_universal_of_polarisation_witness` (this file)
- **Visibility**: public
- **Lines**: 533–541, proof = 3 lines
- **Notes**: None

---

### `theorem qf_nonneg_universal_edge_s_zero`
- **Type**: `(W, {hq}, r : ℤ) → 0 ≤ q·r² − t·r·0 + 0²`
- **What**: Edge case: when s = 0, the QF collapses to q·r², which is non-negative since q = #K : ℕ.
- **How**: `ring_nf` simplifies to `q·r²`, then `mul_nonneg (Int.natCast_nonneg _) (sq_nonneg r)`.
- **Hypotheses**: |K| ≥ 2 (implicit).
- **Uses from project**: `isogOneSub_negFrobenius`, `isogTrace`, `frobeniusIsog` (in type only)
- **Used by**: `qf_nonneg_universal_of_polarisation_witness` (this file)
- **Visibility**: public
- **Lines**: 546–554, proof = 3 lines
- **Notes**: None

---

### `theorem qf_nonneg_universal_of_polarisation_witness`
- **Type**: Takes `h_polarisation : ∀ r s : ℤ, r ≠ 0 → s ≠ 0 → ∃ α : Isogeny, Q(r,s) = (α.degree : ℤ)`; concludes `∀ r s : ℤ, 0 ≤ Q(r, s)`
- **What**: Universal QF non-negativity by case-splitting on r = 0 / s = 0 / (r ≠ 0 ∧ s ≠ 0), using edge-case discharges for the degenerate cases and `Int.natCast_nonneg` for the substantive case via the polarisation witness.
- **How**: `by_cases` on `r = 0` and `s = 0`; subst for the zero cases, delegate to `qf_nonneg_universal_edge_r_zero` and `qf_nonneg_universal_edge_s_zero`; for the inner case, `obtain ⟨α, hα⟩ := h_polarisation r s hr hs`, rewrite by `hα`, and conclude by `Int.natCast_nonneg`.
- **Hypotheses**: |K| ≥ 2; a polarisation-witness function supplying a genuine isogeny for each nonzero (r, s) whose degree equals Q(r, s).
- **Uses from project**: `qf_nonneg_universal_edge_r_zero` (this file), `qf_nonneg_universal_edge_s_zero` (this file)
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 567–590, proof = 14 lines
- **Notes**: This is the R29 T28 structural decomposition; the substantive `h_polarisation` witness (from T27/T26-MAIN) is taken as a hypothesis.

---

## Cross-reference summary

| Declaration | Used by (in this file) |
|---|---|
| `traceOfFrobenius_sq_le_of_qf_nonneg` | `hasse_bound_of_qf_nonneg_witnesses`, `hasse_bound_sq_of_qf_nonneg_witnesses` (2 callers) |
| `hasse_bound_of_qf_nonneg_witnesses` | `hasse_bound_of_full_qf_nonneg_witnesses` (1 caller) |
| `hasse_bound_sq_of_qf_nonneg_witnesses` | `hasse_bound_sq_of_all_qf_nonneg_witnesses` (1 caller) |
| `hasse_bound_of_full_qf_nonneg_witnesses` | `hasse_bound_of_all_qf_nonneg_witnesses` (1 caller) |
| `qf_nonneg_of_genuine_chain` | `qf_nonneg_via_frobenius_polarisation` (1 caller) |
| `genuineIsogSmulSub_pivot_witness` | `genuineIsogSmulSub_degree_eq_quadratic_form_minimal` (1 caller) |
| `qf_nonneg_universal_edge_r_zero` | `qf_nonneg_universal_of_polarisation_witness` (1 caller) |
| `qf_nonneg_universal_edge_s_zero` | `qf_nonneg_universal_of_polarisation_witness` (1 caller) |

No declaration in this file is used by 3+ other declarations within the file.

**Declarations unused within this file** (dead-code candidates; may be used externally):
- `qf_nonneg_via_frobenius_polarisation`
- `genuineIsogSmulSub_degree_eq_quadratic_form`
- `genuineIsogSmulSub_degree_eq_quadratic_form_minimal`
- `hasse_bound_sq_of_all_qf_nonneg_witnesses`
- `qf_nonneg_universal_of_polarisation_witness`
- `hasse_bound_of_all_qf_nonneg_witnesses` (used externally in `HoleE.lean`)

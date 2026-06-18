# Inventory: ./HasseWeil/Curves/EffectiveSumReduce.lean

**Total declarations**: 20 (2 defs, 3 noncomputable defs, 1 private def, 13 theorems/lemmas (including 1 private), 1 abbrev/private def)
**Lines**: 496
**Sorries**: none
**set_option maxHeartbeats**: none

---

## Module-level summary

This file formalises the **list-induction reduction** of effective divisors via Miller's chord/tangent relation (Silverman III.3.5). Given `MillerHypothesis` as a carried predicate, it derives the canonical reduction of any nonempty list of points and a suite of `kappaDivisor` homomorphism-mod-principal identities. The geometric construction of the Miller witness function is explicitly deferred.

---

### `def MillerHypothesis`
- **Type**: `(W : Affine F) [W.IsElliptic] → Prop`
- **What**: Predicate asserting that for every pair `P, Q : W.Point`, the divisor `(P) + (Q) − (P+Q) − (O)` is principal. This is the abstract carrier for Silverman III.3.5.
- **How**: Pure `Prop` definition; no proof.
- **Hypotheses**: `W` an elliptic curve over a field `F` with `DecidableEq`.
- **Uses from project**: `SmoothPlaneCurve.ProjIsPrincipal`, `ProjectiveSmoothPoint.infinity`, `W.Point.toProjectiveSmoothPoint`
- **Used by**: `effective_sum_reduce`, `vertical_principal_of_miller`, `sub_principal_of_miller`, `single_diff_kappa_reduce_of_miller`, `kappaDivisor_add_linEquiv_of_miller`, `kappaDivisor_neg_linEquiv_of_miller`, `kappaDivisor_nsmul_linEquiv_of_miller`, `kappaDivisor_zsmul_linEquiv_of_miller`
- **Visibility**: public
- **Lines**: 39–46, definition only

---

### `noncomputable def listToDivisor`
- **Type**: `(Ps : List W.Point) → ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)`
- **What**: Converts a list of `W.Point`s to the formal sum of singleton divisors `Σ (P) `, via `List.foldr`.
- **How**: `List.foldr` over `Finsupp.single P.toProjectiveSmoothPoint 1`, base 0.
- **Hypotheses**: none beyond the section variables.
- **Uses from project**: `W.Point.toProjectiveSmoothPoint`, `SmoothPlaneCurve`, `ProjectiveDivisor`
- **Used by**: `listToDivisor_nil`, `listToDivisor_cons`, `projectiveDivisorSum_listToDivisor`, `effective_sum_reduce`
- **Visibility**: public
- **Lines**: 49–51

---

### `@[simp] theorem listToDivisor_nil`
- **Type**: `listToDivisor W [] = 0`
- **What**: The divisor of an empty list is zero.
- **How**: `rfl`
- **Hypotheses**: none
- **Uses from project**: `listToDivisor`
- **Used by**: `effective_sum_reduce` (via simp)
- **Visibility**: public
- **Lines**: 53–54, proof length 1

---

### `@[simp] theorem listToDivisor_cons`
- **Type**: `listToDivisor W (P :: Ps) = Finsupp.single P.toProjectiveSmoothPoint 1 + listToDivisor W Ps`
- **What**: Unfolding the head of the list-to-divisor conversion.
- **How**: `rfl`
- **Hypotheses**: none
- **Uses from project**: `listToDivisor`
- **Used by**: `projectiveDivisorSum_listToDivisor`, `effective_sum_reduce`
- **Visibility**: public
- **Lines**: 56–58, proof length 1

---

### `noncomputable def listSum`
- **Type**: `(Ps : List W.Point) → W.Point`
- **What**: The group-law sum of a list of points on `W`, via `List.foldr (· + ·) 0`.
- **How**: `List.foldr` with the elliptic-curve addition and basepoint `0`.
- **Hypotheses**: none beyond section variables.
- **Uses from project**: `W.Point` addition
- **Used by**: `listSum_nil`, `listSum_cons`, `projectiveDivisorSum_listToDivisor`, `effective_sum_reduce`
- **Visibility**: public
- **Lines**: 61–62

---

### `@[simp] theorem listSum_nil`
- **Type**: `listSum W [] = 0`
- **What**: Sum of an empty list is the identity/basepoint.
- **How**: `rfl`
- **Hypotheses**: none
- **Uses from project**: `listSum`
- **Used by**: `effective_sum_reduce` (via simp)
- **Visibility**: public
- **Lines**: 64, proof length 1

---

### `@[simp] theorem listSum_cons`
- **Type**: `listSum W (P :: Ps) = P + listSum W Ps`
- **What**: Unfolds the head of `listSum`.
- **How**: `rfl`
- **Hypotheses**: none
- **Uses from project**: `listSum`
- **Used by**: `projectiveDivisorSum_listToDivisor`, `effective_sum_reduce`
- **Visibility**: public
- **Lines**: 66–67, proof length 1

---

### `theorem projectiveDivisorSum_listToDivisor`
- **Type**: `∀ (Ps : List W.Point), projectiveDivisorSum W (listToDivisor W Ps) = listSum W Ps`
- **What**: The canonical σ map (sending a divisor to the underlying group-law sum of its support) applied to `listToDivisor` yields `listSum`: these two list-based definitions are compatible.
- **How**: List induction; the inductive step uses `projectiveDivisorSum_add` and `projectiveDivisorSum_single` (from PicZero), then `P.toProjectiveSmoothPoint_toAffinePoint` and `one_zsmul`.
- **Hypotheses**: none
- **Uses from project**: `listToDivisor`, `listSum`, `projectiveDivisorSum_add` (PicZero), `projectiveDivisorSum_single` (PicZero), `W.Point.toProjectiveSmoothPoint_toAffinePoint` (PicZero)
- **Used by**: unused in file (public API)
- **Visibility**: public
- **Lines**: 70–77, proof length 8

---

### `private noncomputable def infDiv`
- **Type**: `ProjectiveDivisor (⟨W⟩ : SmoothPlaneCurve F)`
- **What**: Local abbreviation for the principal divisor of the infinity point `(O)`, used to avoid repetition in the statement of `effective_sum_reduce`.
- **How**: `Finsupp.single ProjectiveSmoothPoint.infinity 1`
- **Hypotheses**: none
- **Uses from project**: `ProjectiveSmoothPoint.infinity`, `ProjectiveDivisor`
- **Used by**: `effective_sum_reduce`
- **Visibility**: private
- **Lines**: 80–82

---

### `private theorem ProjLinearlyEquiv.add_left`
- **Type**: `D₁ ~ D₂ → E + D₁ ~ E + D₂` (linear equivalence preserved under left addition)
- **What**: If `D₁` and `D₂` are linearly equivalent, then `E + D₁` and `E + D₂` are linearly equivalent. Used internally to transport the induction hypothesis past the first summand.
- **How**: Unfolds `ProjLinearlyEquiv` as `ProjIsPrincipal` applied to the difference, then simplifies the difference `(E + D₁) − (E + D₂) = D₁ − D₂` by `abel`.
- **Hypotheses**: none beyond the linear equivalence hypothesis.
- **Uses from project**: `SmoothPlaneCurve.ProjLinearlyEquiv`, `SmoothPlaneCurve.ProjIsPrincipal`
- **Used by**: `effective_sum_reduce`
- **Visibility**: private
- **Lines**: 85–92, proof length 8

---

### `theorem effective_sum_reduce`
- **Type**: `MillerHypothesis W → (Ps : List W.Point) → Ps ≠ [] → listToDivisor W Ps ~ Finsupp.single (listSum W Ps).toProjectiveSmoothPoint 1 + ((Ps.length : ℤ) − 1) • infDiv W`
- **What**: For any nonempty list of points, the effective sum divisor is linearly equivalent to the singleton divisor of the group-law sum plus `(length − 1)` copies of `(O)`. This is the main induction theorem.
- **How**: List induction with cases on the tail. Singleton base: `ProjLinearlyEquiv.refl`. Inductive step: (1) apply `ProjLinearlyEquiv.add_left` to transport the IH past the head; (2) close the gap by converting the remaining difference to Miller's divisor form and applying `h_miller P (listSum ...)` directly; the length arithmetic is done by `push_cast` + `ring` and the divisor identity by `abel`.
- **Hypotheses**: `MillerHypothesis W`; `Ps` nonempty.
- **Uses from project**: `MillerHypothesis`, `listToDivisor`, `listSum`, `infDiv`, `ProjLinearlyEquiv.add_left` (this file), `listToDivisor_cons`, `listToDivisor_nil`, `listSum_cons`, `listSum_nil`, `SmoothPlaneCurve.ProjLinearlyEquiv.refl` (ProjectiveDivisor)
- **Used by**: unused in file (main exported result)
- **Visibility**: public
- **Lines**: 97–174, proof length 78
- **Notes**: Proof is 78 lines — **longest proof in the file**. No sorry, no maxHeartbeats.

---

### `private theorem zero_toProj`
- **Type**: `(0 : W.Point).toProjectiveSmoothPoint = ProjectiveSmoothPoint.infinity`
- **What**: The basepoint/zero of the elliptic curve projects to the infinity point. Used as a local simp-lemma within the corollaries section.
- **How**: `rfl` (definitional equality).
- **Hypotheses**: none
- **Uses from project**: `W.Point.toProjectiveSmoothPoint`, `ProjectiveSmoothPoint.infinity`
- **Used by**: `vertical_principal_of_miller`
- **Visibility**: private
- **Lines**: 179–182, proof length 1

---

### `theorem vertical_principal_of_miller`
- **Type**: `MillerHypothesis W → (S : W.Point) → ProjIsPrincipal ((S) + (−S) − 2·(O))`
- **What**: The "vertical line at `x = x(S)`" divisor `(S) + (−S) − 2(O)` is principal. Derived from Miller applied to `(S, −S)` using `S + (−S) = 0` and the fact that `0` maps to `∞`.
- **How**: Instantiates `h_miller S (−S)`, rewrites with `add_neg_cancel` and `zero_toProj` to match the goal, then uses `abel` to re-express the `2·(O)` form.
- **Hypotheses**: `MillerHypothesis W`.
- **Uses from project**: `MillerHypothesis`, `zero_toProj` (this file)
- **Used by**: `sub_principal_of_miller`, `kappaDivisor_neg_linEquiv_of_miller`
- **Visibility**: public
- **Lines**: 188–216, proof length 29

---

### `theorem sub_principal_of_miller`
- **Type**: `MillerHypothesis W → (R S : W.Point) → ProjIsPrincipal ((R) − (S) − (R−S) + (O))`
- **What**: The divisor `(R) − (S) − (R−S) + (O)` is principal. Derived from Miller(`R`, `−S`) minus the vertical-line identity at `S`, giving the sub-form of Miller.
- **How**: Applies `h_miller R (−S)` and `vertical_principal_of_miller`, uses `projPrincipalSubgroup.sub_mem` to subtract the two principal divisors, then closes by `abel` after rewriting `R + −S = R − S`.
- **Hypotheses**: `MillerHypothesis W`.
- **Uses from project**: `MillerHypothesis`, `vertical_principal_of_miller` (this file), `SmoothPlaneCurve.projPrincipalSubgroup.sub_mem`
- **Used by**: `single_diff_kappa_reduce_of_miller`
- **Visibility**: public
- **Lines**: 222–266, proof length 45
- **Notes**: Proof is 45 lines (> 30 lines).

---

### `theorem single_diff_kappa_reduce_of_miller`
- **Type**: `MillerHypothesis W → (P Q : W.Point) → (P).toProj − (Q).toProj ~ kappaDivisor W (P − Q)`
- **What**: The difference of singleton divisors `(P) − (Q)` is linearly equivalent to `κ(P−Q)`. Packages `sub_principal_of_miller` into `ProjLinearlyEquiv` form.
- **How**: Unfolds `kappaDivisor`, invokes `sub_principal_of_miller W h_miller P Q`, then closes by `convert ... using 1; abel`.
- **Hypotheses**: `MillerHypothesis W`.
- **Uses from project**: `sub_principal_of_miller` (this file), `kappaDivisor` (PicZero), `SmoothPlaneCurve.ProjLinearlyEquiv`, `SmoothPlaneCurve.ProjIsPrincipal`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 275–288, proof length 14

---

### `@[simp] theorem kappaDivisor_zero`
- **Type**: `kappaDivisor W (0 : W.Point) = 0`
- **What**: The kappa divisor of the basepoint is zero (the identity divisor).
- **How**: Unfolds `kappaDivisor` and uses `sub_self`.
- **Hypotheses**: none
- **Uses from project**: `kappaDivisor` (PicZero)
- **Used by**: `kappaDivisor_nsmul_linEquiv_of_miller`
- **Visibility**: public
- **Lines**: 297–304, proof length 8

---

### `theorem kappaDivisor_add_linEquiv_of_miller`
- **Type**: `MillerHypothesis W → (P Q : W.Point) → kappaDivisor W (P + Q) ~ kappaDivisor W P + kappaDivisor W Q`
- **What**: `κ` is additive modulo principal: `κ(P + Q) ∼ κ(P) + κ(Q)`.
- **How**: Unfolds `kappaDivisor`, takes the negative of Miller's principal divisor via `projPrincipalSubgroup.neg_mem`, and uses `convert ... using 1; abel` to match the divisor form.
- **Hypotheses**: `MillerHypothesis W`.
- **Uses from project**: `MillerHypothesis`, `kappaDivisor` (PicZero), `SmoothPlaneCurve.projPrincipalSubgroup.neg_mem`
- **Used by**: `kappaDivisor_nsmul_linEquiv_of_miller`, `kappaDivisor_zsmul_linEquiv_of_miller`
- **Visibility**: public
- **Lines**: 310–322, proof length 13

---

### `theorem kappaDivisor_neg_linEquiv_of_miller`
- **Type**: `MillerHypothesis W → (P : W.Point) → kappaDivisor W (−P) ~ −kappaDivisor W P`
- **What**: `κ(−P) ∼ −κ(P)`, derived from the vertical-line identity.
- **How**: Applies `vertical_principal_of_miller W h_miller P`, then `convert ... using 1; rw [show (2:ℤ) = 1+1 ...]; abel`.
- **Hypotheses**: `MillerHypothesis W`.
- **Uses from project**: `vertical_principal_of_miller` (this file), `kappaDivisor` (PicZero)
- **Used by**: `kappaDivisor_zsmul_linEquiv_of_miller`
- **Visibility**: public
- **Lines**: 327–349, proof length 23

---

### `theorem kappaDivisor_nsmul_linEquiv_of_miller`
- **Type**: `MillerHypothesis W → (P : W.Point) → (n : ℕ) → kappaDivisor W (n • P) ~ n • kappaDivisor W P`
- **What**: `κ(n·P) ∼ n·κ(P)` for `n : ℕ`, by induction using additivity of κ modulo principal.
- **How**: Induction on `n`. Base: uses `kappaDivisor_zero` and `ProjLinearlyEquiv.refl`. Step: uses `kappaDivisor_add_linEquiv_of_miller` for `k•P + P`, combines with IH via `projPrincipalSubgroup` membership and `abel`; chains with `.trans`.
- **Hypotheses**: `MillerHypothesis W`.
- **Uses from project**: `kappaDivisor_zero` (this file), `kappaDivisor_add_linEquiv_of_miller` (this file), `SmoothPlaneCurve.ProjLinearlyEquiv.refl`, `SmoothPlaneCurve.ProjIsPrincipal`
- **Used by**: `kappaDivisor_zsmul_linEquiv_of_miller`
- **Visibility**: public
- **Lines**: 353–388, proof length 36
- **Notes**: Proof is 36 lines (> 30 lines).

---

### `theorem single_minus_inf_eq_kappaDivisor`
- **Type**: `∀ (Q : ProjectiveSmoothPoint ⟨W⟩), Finsupp.single Q 1 − Finsupp.single (∞) 1 = kappaDivisor W Q.toAffinePoint`
- **What**: An equality (not just equivalence): for any projective smooth point `Q`, the divisor `(Q) − (O)` equals `κ(Q.toAffinePoint)`. Handles both the infinity case (both sides are 0) and the affine case (by `rfl`).
- **How**: Pattern-match on `Q`; both cases close by `rfl` after unfolding `kappaDivisor`.
- **Hypotheses**: none
- **Uses from project**: `kappaDivisor` (PicZero), `ProjectiveSmoothPoint.toAffinePoint`
- **Used by**: unused in file (prepared for the Finsupp-induction strategy sketched in the comment block)
- **Visibility**: public
- **Lines**: 407–433, proof length 27

---

### `theorem kappaDivisor_zsmul_linEquiv_of_miller`
- **Type**: `MillerHypothesis W → (P : W.Point) → (n : ℤ) → kappaDivisor W (n • P) ~ n • kappaDivisor W P`
- **What**: ℤ-version of `kappaDivisor_nsmul_linEquiv_of_miller`: `κ(n·P) ∼ n·κ(P)` for integer `n`.
- **How**: Uses `Int.eq_nat_or_neg` to split `n` into `↑m` and `−↑m`. Positive case: reduces to `kappaDivisor_nsmul_linEquiv_of_miller` via `natCast_zsmul`. Negative case: chains `kappaDivisor_neg_linEquiv_of_miller (m•P)` with `kappaDivisor_nsmul_linEquiv_of_miller` (for the negation step) via `projPrincipalSubgroup.neg_mem` and `.trans`.
- **Hypotheses**: `MillerHypothesis W`.
- **Uses from project**: `kappaDivisor_nsmul_linEquiv_of_miller` (this file), `kappaDivisor_neg_linEquiv_of_miller` (this file), `SmoothPlaneCurve.projPrincipalSubgroup.neg_mem`, `SmoothPlaneCurve.ProjLinearlyEquiv`
- **Used by**: unused in file (prepared for the Finsupp-induction strategy)
- **Visibility**: public
- **Lines**: 437–470, proof length 34
- **Notes**: Proof is 34 lines (> 30 lines).

---

## Cross-reference summary

| Declaration | Used by (this file) |
|---|---|
| `MillerHypothesis` | 8 theorems |
| `listToDivisor` | 4 theorems |
| `listSum` | 5 theorems |
| `infDiv` (private) | `effective_sum_reduce` |
| `ProjLinearlyEquiv.add_left` (private) | `effective_sum_reduce` |
| `zero_toProj` (private) | `vertical_principal_of_miller` |
| `vertical_principal_of_miller` | `sub_principal_of_miller`, `kappaDivisor_neg_linEquiv_of_miller` |
| `sub_principal_of_miller` | `single_diff_kappa_reduce_of_miller` |
| `kappaDivisor_zero` | `kappaDivisor_nsmul_linEquiv_of_miller` |
| `kappaDivisor_add_linEquiv_of_miller` | `kappaDivisor_nsmul_linEquiv_of_miller`, `kappaDivisor_zsmul_linEquiv_of_miller` |
| `kappaDivisor_neg_linEquiv_of_miller` | `kappaDivisor_zsmul_linEquiv_of_miller` |
| `kappaDivisor_nsmul_linEquiv_of_miller` | `kappaDivisor_zsmul_linEquiv_of_miller` |
| `single_minus_inf_eq_kappaDivisor` | unused in file |
| `kappaDivisor_zsmul_linEquiv_of_miller` | unused in file |
| `single_diff_kappa_reduce_of_miller` | unused in file |
| `effective_sum_reduce` | unused in file |
| `projectiveDivisorSum_listToDivisor` | unused in file |

## Key API declarations (used by 3+ others in this file)

- `MillerHypothesis` — 8 users
- `listToDivisor` — 4 users
- `listSum` — 5 users
- `kappaDivisor_add_linEquiv_of_miller` — 2 users (kappaDivisor_nsmul + kappaDivisor_zsmul)
- `kappaDivisor_nsmul_linEquiv_of_miller` — used by kappaDivisor_zsmul + listed as key

## Notable observations

- No `sorry`, no `set_option maxHeartbeats`. The file is entirely clean.
- The trailing comment block (lines 472–494) sketches a `general_kappa_reduce_of_miller` theorem explicitly flagged as "deferred to a focused session" — the file is intentionally incomplete; all ingredients are ready but the capstone Finsupp-induction is parked.
- `single_minus_inf_eq_kappaDivisor` and `kappaDivisor_zsmul_linEquiv_of_miller` are prepared for the deferred `general_kappa_reduce_of_miller` but are currently dead code within this file.

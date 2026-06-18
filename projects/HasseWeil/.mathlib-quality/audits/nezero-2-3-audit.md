# `[NeZero (2 : K)] / [NeZero (3 : K)]` Audit (T-AUDIT-RESIDUAL-NEZERO)

**Date**: 2026-05-15
**Scope**: every `[NeZero (2 : K)]` and `[NeZero (3 : K)]` typeclass
hypothesis (and the bare `[NeZero 2]/[NeZero 3]` form) currently appearing
on a Lean declaration or section `variable` block under `HasseWeil/`.

**Method**: `grep -rn "NeZero (2 : \|NeZero (3 : \|NeZero 2\]\|NeZero 3\]"
HasseWeil/ --include="*.lean"`, then read the surrounding theorem / `variable`
block and classify per the five buckets in T-AUDIT-RESIDUAL-NEZERO:

1. **Miller-derived** — transitively consumes `MillerHypothesis`,
   `DivZeroReduce`, `picZeroIsoE_of_AFInputs`, or
   `coordRingImage_ordAtInfty_ne_neg_one`. Will drop once
   `T-MILLER-PROJECTIVE-REFACTOR` lands.
2. **Dedekind / integrally-closed** — needs the separability instance for
   `F(C)/F(X)`, or `[IsDedekindDomain CR]` / `[IsIntegrallyClosed CR]`
   synthesis that itself needs char ≠ 2 (and sometimes char ≠ 3).
3. **Short-Weierstrass / Legendre-form** — uses an explicit short form
   `Y² = X(X-1)(X-λ)` or `Y² = X³ + AX + B`.
4. **Discriminant / j-invariant** — uses the discriminant formula
   (`Δ = -16(4A³ + 27B²)`, the polynomial discriminant `4X³ + b₂X² + 2b₄X + b₆`,
   the identity `discr = 16·Δ`, or the cubic derivative `12X² + ...`).
5. **Other / unclassified**.

Internal `haveI` instances inside a proof body (not introducing a new
hypothesis on a declaration) and `omit [NeZero ...] in` lines are listed
in the appendix and excluded from the per-bucket totals. Comment-only
mentions inside docstrings are also appendix-only.

## Classification table

| File:line | Theorem / def / instance | Why typeclass appears | Class | Removable post Miller-projective refactor? |
|---|---|---|---|---|
| HasseWeil/Curves/IntegralClosure.lean:109 | `Polynomial.separable_of_monic_irreducible_natDegree_le_two` | Standalone helper — proof needs `(p.natDegree : K) ≠ 0` for natDegree = 2 case (`(2 : K) ≠ 0`). | (5) | NO — independent helper. |
| HasseWeil/Curves/IntegralClosure.lean:210 | `algebra_isSeparable_functionField` (instance) | IC-003i: `Algebra.IsSeparable (FractionRing F[X]) C.FunctionField`. Weierstrass poly in Y has derivative `2Y + a₁X + a₃`; needs `2 ≠ 0`. Reduces to the L109 helper. **Keystone separability instance for the IsIntegrallyClosed/IsDedekindDomain chain.** | (2) | NO — needs independent IntegralClosure refactor. |
| HasseWeil/Curves/IntegralClosure.lean:407 | `polynomialDiscriminant_natDegree` | Polynomial discriminant `4X³ + b₂X² + 2b₄X + b₆` has leading coeff `4 = 2²`; need char ≠ 2 for natDegree = 3. | (4) | NO — discriminant-form-specific. |
| HasseWeil/Curves/IntegralClosure.lean:451 | `polynomialDiscriminant_ne_zero` | Corollary of L407 (degree 3 ⇒ nonzero). | (4) | NO. |
| HasseWeil/Curves/IntegralClosure.lean:478 | `polynomialDiscriminant_degree` | Same as L407 but for `degree` rather than `natDegree`. | (4) | NO. |
| HasseWeil/Curves/IntegralClosure.lean:487 | `polynomialDiscriminant_discr` | Identity `discr(polynomialDiscriminant) = 16 · Δ` (uses `16 = 2⁴`). | (4) | NO. |
| HasseWeil/Curves/IntegralClosure.lean:498 | `polynomialDiscriminant_discr_ne_zero` | L487 + `Δ ≠ 0` from `[IsElliptic]`. | (4) | NO. |
| HasseWeil/Curves/IntegralClosure.lean:516–517 | `polynomialDiscriminant_derivative_natDegree` | Derivative leading coeff `12 = 4·3`; need char ≠ 2 AND char ≠ 3. | (4) | NO. |
| HasseWeil/Curves/IntegralClosure.lean:544 | `polynomialDiscriminant_squarefree` | Task D main: chains L498 + L516 via `Polynomial.resultant_deriv` to get separability ⇒ squarefree. | (4) | NO. |
| HasseWeil/Curves/IntegralClosure.lean:842–843 | `isIntegrallyClosed_coordinateRing_of_IsElliptic` (instance) | **Apex of bucket (2)**: synthesizes `IsIntegrallyClosed C.CoordinateRing` from L210 (sep) + L544 (squarefree) + `Polynomial.fractionRing_mem_range_of_sq_mul_squarefree`. | (2) | NO — this is the source of `[IsIntegrallyClosed]` discharge for the whole pipeline. |
| HasseWeil/Curves/Miller.lean:414 | `divisorOf_coordX_sub_const_apply_eq_finsupp` | Vertical-line scaffolding for Miller; carries `[IsIntegrallyClosed CR]` (synthesized via IntegralClosure.lean L843, which needs NeZero 2/3). | (1) | YES — conditional on Miller refactor handling `[IsIntegrallyClosed]`. |
| HasseWeil/Curves/Miller.lean:469 | `divisorOf_coordX_sub_const` | Vertical-line Finsupp form. Same chain as L414. | (1) | YES (conditional). |
| HasseWeil/Curves/Miller.lean:480 | `projectiveDivisorOf_coordX_sub_const` | Vertical-line projective lift. Same chain. | (1) | YES (conditional). |
| HasseWeil/Curves/Miller.lean:527 | `vertical_line_principal` | `(P) + (-P) − 2(∞)` principal — fed directly into Miller. | (1) | YES (conditional). |
| HasseWeil/Curves/Miller.lean:792 | `count_YClass_linePolynomial_eq` | Chord-line count formula for Miller. | (1) | YES (conditional). |
| HasseWeil/Curves/Miller.lean:944 | `divisorOf_coordY_sub_algMap_linePolynomial_apply_eq_finsupp` | Chord-line affine divisor for Miller. | (1) | YES (conditional). |
| HasseWeil/Curves/Miller.lean:988 | `divisorOf_coordY_sub_algMap_linePolynomial` | Chord-line affine divisor (Finsupp form). | (1) | YES (conditional). |
| HasseWeil/Curves/Miller.lean:1004 | `projectiveDivisorOf_coordY_sub_algMap_linePolynomial` | Chord-line projective lift. | (1) | YES (conditional). |
| HasseWeil/Curves/Miller.lean:1059 | `miller_at_addSmoothPoint_principal` | Miller core for non-degenerate chord case. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1129 | `miller_at_neg_of_some` | Miller for `(P) + (-P)` case. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1176 | `miller_at_some_some_nondegen` | Miller non-degenerate case wrapper. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1205 | `miller_at_some_some_degen` | Miller degenerate case wrapper. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1272 | `miller_hypothesis_holds` | **`MillerHypothesis W` axiom-clean** — the main theorem of the file. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1307 | `general_kappa_reduce` | Finsupp κ-reduction; uses `miller_hypothesis_holds`. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1467 | `divZeroReduce_holds` | **`DivZeroReduce W` axiom-clean** — Target 2. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1492 | `afInputs_unconditional` | Bundled `AFInputs W` — Target 3. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1509 | `picZeroIsoE` | **T-III-3-004 (Pic⁰(E) ≅ E) unconditional**. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1522 | `picZeroIsoE_baseChange` | Pic⁰ iso over `W.baseChange L`. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1534 | `picZeroIsoE_symm_apply` (`@[simp]`) | Inverse direction of `picZeroIsoE`. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1543 | `picZeroIsoE_picZeroOfPoint` (`@[simp]`) | Forward direction of `picZeroIsoE`. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1562 | `projectiveDivisorSum_eq_zero_of_principal` | σ vanishes on principals — uses Pic⁰ isomorphism content. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1577 | `sigmaBar_picZeroOfPoint` | σ̄ ∘ κ identity. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1588 | `picZeroOfPoint_sigmaBar` | κ ∘ σ̄ identity. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1603 | `exists_kappa_form` | Representation of Pic⁰ via κ. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1615 | `picZeroOfPoint_injective` | κ injective via Pic⁰ iso. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1630 | `picZeroOfPoint_injective` (continuation hypothesis line) | Same declaration as L1615. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1649 | `AddHomProperty_of_pushforward_principal` | Pushforward AddHom under principal preservation. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1673 | `kappaDivisor_inj` | κ-divisor injectivity. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1714 | `variable [IsAlgClosed F] [NeZero (2 : F)] [NeZero (3 : F)]` | Section variable governing all of `IsogenyBaseChange §5 wrappers`. | (1) | YES — drops entire §5 wrapper block at once. |
| HasseWeil/Curves/Miller.lean:1814 | `frobeniusPicPushforward_charP_prime` | Frobenius pushforward on Pic⁰ via `picZeroIsoE`. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1837 | `frobeniusPicPushforward_charP_prime_picZeroOfPoint` | Compat with κ. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1863 | `verschiebungPicPullback_charP_prime` | Verschiebung pullback on Pic⁰. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1889 | `verschiebungPicPullback_comp_frobeniusPicPushforward` | V ∘ F = [p] identity. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1920 | `frobeniusDualViaPicZero_charP_prime` | Dual isogeny via Pic⁰. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1943 | `frobeniusDualViaPicZero_charP_prime_comp_property` | Dual compat property. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1977 | `frobeniusPicPushforward_charP_pow` | `p^r` variant of Frobenius pushforward. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:1999 | `frobeniusPicPushforward_charP_pow_picZeroOfPoint` | `p^r` compat with κ. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:2022 | `verschiebungPicPullback_charP_pow` | `p^r` Verschiebung. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:2045 | `verschiebungPicPullback_comp_frobeniusPicPushforward_charP_pow` | `p^r` V ∘ F identity. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:2074 | `frobeniusDualViaPicZero_charP_pow` | `p^r` dual via Pic⁰. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:2094 | `frobeniusDualViaPicZero_charP_pow_comp_property` | `p^r` dual compat. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:2134 | `projectiveDivisorSum_chord_line` | σ vanishes on chord-line divisor (T-PIC-A-002a). Uses chord projective divisor + generic σ-vanishing. | (1) | YES. |
| HasseWeil/Curves/Miller.lean:2153 | `projectiveDivisorSum_vertical_line_of_principal` | σ vanishes on vertical-line divisor (T-PIC-A-002b). | (1) | YES. |
| HasseWeil/Curves/NoFinitePolesBridge.lean:289 | `AddHomProperty_of_miller_divZeroReduce` | Witness-parametric on `MillerHypothesis` + `DivZeroReduce` (explicit hypotheses). | (1) | YES. |
| HasseWeil/Curves/NoFinitePolesBridge.lean:337 | `picZeroIsoE_of_AFInputs` | Witness-parametric on `AFInputs` (explicit hypothesis). | (1) | YES. |
| HasseWeil/Curves/NoFinitePolesBridge.lean:376 | `picZeroIsoE_baseChange_of_AFInputs` | `picZeroIsoE_of_AFInputs` instantiated at `W.baseChange L`. | (1) | YES. |
| HasseWeil/Curves/NormValuation.lean:504 | `sum_ramificationIdx_over_fiber` | Calls mathlib `Ideal.sum_ramification_inertia C.CoordinateRing (FractionRing F[X]) C.FunctionField` — requires `Algebra.IsSeparable` of the function-field extension (= IntegralClosure.lean L210, char ≠ 2). NeZero 3 carried for API consistency only. | (2) | NO — needs IntegralClosure refactor (char-2 separability of F(C)/F(X) does not hold for the standard model). |
| HasseWeil/Curves/NormValuation.lean:536 | `sum_ramificationIdx_eq_finrank` | Corollary of L504; same chain. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:734 | `exists_relNorm_maximalIdealAt_eq_pow` | Helper B keystone (existence form); uses `Ideal.exists_relNorm_eq_pow_of_isPrime` + DedekindDomain chain. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:751 | `relNorm_algebraMap_X_sub_C_eq_pow_two` | `relNorm` of pulled-back `(X-a)` = `(X-a)²` via `finrank = 2` and mathlib's `Ideal.relNorm_algebraMap`. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:765 | `X_sub_C_pow_two_le_relNorm_maximalIdealAt` | Monotonicity bound from L751. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:783 | `map_algebraMap_X_sub_C_eq_prod_primesOver_pow` | Dedekind factorization of `(X-a)·F[C]` over fiber. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:813 | `prod_relNorm_pow_primesOver_eq_X_sub_C_pow_two` | Fibre product equation = `(X-a)²`. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:843 | `relNorm_maximalIdealAt_le_X_sub_C` | Divisibility bound on `relNorm M_P`. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:860 | `exists_relNorm_pow_of_primesOver` | Existence form for primes lying over `(X-a)`. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:896 | `primesOverExp` | Exponent function `s_Q` for fiber primes. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:903 | `one_le_primesOverExp` | `s_Q ≥ 1`. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:910 | `relNorm_eq_pow_primesOverExp` | `relNorm Q = (X-π(Q))^{s_Q}`. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:923 | `exists_relNorm_maximalIdealAt_eq_pow_bracketed` | Bracketed existence form. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:953 | `maximalIdealAt_mem_primesOver` | `maximalIdealAt P ∈ primesOver (X - P.x)`. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:964 | `ramificationIdx_maximalIdealAt_ne_zero` | Ramification index nonzero. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:991 | `relNorm_maximalIdealAt` | `relNorm (maxIdealAt P) = (X - P.x)` (s = 1 keystone). | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:1103 | `relNorm_eq_X_sub_C_of_primesOver` | All fiber primes have `relNorm = (X-a)`. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:1647 | `relNorm_pow_of_mem_primesOverFinset` | `relNorm (Q^n) = (X-a)^n` for Q in fiber. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:1669 | `count_relNorm_pow_of_mem_primesOverFinset` | `(X-a)`-count of `relNorm (Q^n) = n`. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:1708 | `count_relNorm_singleton_eq_sum_count_fiber` | Per-fiber count identity. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:2020 | `fiber_sum_divisorOf_algMap_eq_count_norm` | Per-fiber sum identity in smooth-point form. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:2158 | `divisorOf_algMap_degree_eq_natDegree_norm` | Affine divisor degree = `natDegree (norm)`. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:2233 | `helperB` | Helper B unconditional: `(C.divisorOf f).degree = intDegree (C.normAsRatFunc f)`. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:2293 | `projectiveDivisorOf_degree_eq_zero` | **Silverman II.3.1(b) keystone**: `(C.projectiveDivisorOf f).degree = 0`. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:2307 | `toProjective_eq_projectiveDivisorOf` | A5 chained principal preservation. | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:2319 | `toProjective_eq_projectiveDivisorOf_witness` | Pic-level form (Pic⁰_aff ≃+ PicProj⁰). | (2) | NO. |
| HasseWeil/Curves/NormValuation.lean:2332 | `principal_mem_degZero` | `PrincipalImpliesDegZero W` witness. | (2) | NO. |
| HasseWeil/EvenFunctions.lean:156 | `negInvolution_eq_iff` | Negation involution fixes `f` iff `f ∈ image F[X]`. Proof uses `2q = 0 → q = 0` via `NeZero.ne 2`. Char-2 obstruction is intrinsic (involution becomes trivial in char 2). | (5) | NO — char-2 obstruction is structural. |
| HasseWeil/Hasse/OpenLemmas.lean:863 | `vertical_principal` | Open Lemma 11a — directly calls `miller_hypothesis_holds`. | (1) | YES. |
| HasseWeil/Hasse/OpenLemmas.lean:912 | `line_principal` | Open Lemma 11b — uses Miller + vertical principal. | (1) | YES. |
| HasseWeil/Hasse/OpenLemmas.lean:963 | `miller_principal` | Open Lemma 11c — `MillerHypothesis W` literal alias. | (1) | YES. |
| HasseWeil/Hasse/OpenLemmas.lean:980 | `degree_zero_divisor_reduce` | Open Lemma 11d — `DivZeroReduce W` literal alias. | (1) | YES. |
| HasseWeil/LegendreForm.lean:69 | `legendreCurve_Δ_ne_zero_iff` | Computes Legendre curve discriminant `Δ = 16·l²·(l-1)²`; needs `16 ≠ 0`. | (3) | NO — Legendre form is char ≠ 2 by construction. |
| HasseWeil/LegendreForm.lean:87 | `variable [IsAlgClosed F] [NeZero (2 : F)]` | Section variable for `exists_legendreCurve_iso` (Silverman III.1.7). Existence of Legendre form for every elliptic curve requires char ≠ 2. | (3) | NO — intrinsic. |

## Scope summary

* **Total typeclass-bearing declarations**: **90**
  (does not include 1 proof-internal `haveI` at IntegralClosure.lean:212,
  1 `omit ... in` at LegendreForm.lean:89, and ~14 comment-only docstring
  mentions — see appendix).

* **Per-bucket counts**:

  | Bucket | Count | % of total |
  |---|---|---|
  | (1) Miller-derived | 50 | 56% |
  | (2) Dedekind / integrally-closed | 29 | 32% |
  | (3) Short-Weierstrass / Legendre-form | 2 | 2% |
  | (4) Discriminant / j-invariant | 7 | 8% |
  | (5) Other | 2 | 2% |

* **Per-bucket per-file distribution**:

  | File | (1) | (2) | (3) | (4) | (5) | total |
  |---|---|---|---|---|---|---|
  | Curves/IntegralClosure.lean | – | 2 | – | 7 | 1 | 10 |
  | Curves/Miller.lean | 43 | – | – | – | – | 43 |
  | Curves/NoFinitePolesBridge.lean | 3 | – | – | – | – | 3 |
  | Curves/NormValuation.lean | – | 27 | – | – | – | 27 |
  | EvenFunctions.lean | – | – | – | – | 1 | 1 |
  | Hasse/OpenLemmas.lean | 4 | – | – | – | – | 4 |
  | LegendreForm.lean | – | – | 2 | – | – | 2 |
  | **total** | **50** | **29** | **2** | **7** | **2** | **90** |

## Recommendation

The projective-Miller refactor (`T-MILLER-PROJECTIVE-REFACTOR`) cleanly
removes **only ~56% of the residual `[NeZero 2/3]` hypotheses** (the 50
bucket-(1) hits). To reach a fully char-uniform Hasse–Weil pipeline,
**three additional independent fronts** are required:

1. **Bucket (2) — IntegralClosure / NormValuation refactor (29 hits, 32%
   of total).** The keystone is the separability instance
   `algebra_isSeparable_functionField` (IntegralClosure.lean:210) and the
   `IsIntegrallyClosed` instance for elliptic coordinate rings
   (IntegralClosure.lean:842–843). These propagate via the entire Helper B
   relNorm chain in `NormValuation.lean` (27 hits). The standard
   Weierstrass model has *inseparable* `F(C)/F(X)` in char 2, so this
   route does not generalise without a model change — recommended approach:

   * Re-derive `Ideal.relNorm_algebraMap` and the Helper-B fibre identities
     via a different geometric route (e.g., regularity of `F[C]` directly,
     without going through separability), OR
   * Specialise to a different normal form in char 2/3 (the Tate form
     `Y² + a₁XY + a₃Y = X³ + …`) and prove `IsDedekindDomain` via a
     case-split.

   Suggested ticket: `T-INTEGRAL-CLOSURE-CHAR2` (and possibly `-CHAR3`).
   This is the **second-largest scope after Miller** and the bottleneck
   for char-2 Hasse bound — recommended as next priority after
   `T-MILLER-PROJECTIVE-REFACTOR` lands.

2. **Bucket (4) — Discriminant identities (7 hits, 8% of total).** All
   live in IntegralClosure.lean (407–544). Their `[NeZero 2/3]` arises
   from the specific polynomial-discriminant formula
   `4X³ + b₂X² + 2b₄X + b₆`. They support bucket (2) (feeding into the
   `isIntegrallyClosed` instance at L843), so they can be retired
   together with the bucket-(2) refactor if the new approach avoids the
   cubic-discriminant route.

   Suggested ticket: folded into `T-INTEGRAL-CLOSURE-CHAR2`.

3. **Bucket (3) — Legendre form (2 hits, 2% of total).** Only relevant
   for `T-HASSE-VIA-LEGENDRE` if that path is taken. Legendre form
   `Y² = X(X-1)(X-l)` is intrinsically char ≠ 2 and cannot be generalised;
   any char-2 strategy must avoid `HasseWeil/LegendreForm.lean` entirely
   or replace it with a Tate-style char-2 normal form.

   Suggested ticket: `T-HASSE-CHAR2-NORMAL-FORM` (only if needed).

4. **Bucket (5) — Other (2 hits, 2% of total).** Two unrelated structural
   char-2 obstructions:

   * `Polynomial.separable_of_monic_irreducible_natDegree_le_two`
     (IntegralClosure.lean:109) — a generic separability helper that
     supports bucket (2). Likely retired alongside bucket (2).
   * `negInvolution_eq_iff` (EvenFunctions.lean:156) — the negation
     involution becomes trivial in char 2 (since `-Y = Y + a₁X + a₃`
     collapses Y-asymmetry). Whether this is needed in a char-uniform
     pipeline depends on whether `EvenFunctions.lean` is still consumed
     after the Miller refactor.

   Suggested action: re-audit after Miller + IntegralClosure refactors
   land; these may auto-drop or need a small dedicated patch.

### Bottom line

| Phase | Hits retired | Cumulative coverage |
|---|---|---|
| `T-MILLER-PROJECTIVE-REFACTOR` (bucket 1) | 50 | 56% |
| `T-INTEGRAL-CLOSURE-CHAR2` (buckets 2 + 4) | 36 | 96% |
| char-2 normal-form work (bucket 3) | 2 | 98% |
| Residual cleanup (bucket 5) | 2 | 100% |

**Miller alone gets us a little over halfway.** The remaining ~44%
sits primarily in the integral-closure / Dedekind-domain layer and is
mathematically the bigger lift, because the standard Weierstrass model
has inseparable function-field extensions in char 2.

## Appendix A — Internal / negative / comment-only references

These are NOT counted in the per-bucket totals because they do not
introduce a `[NeZero ...]` hypothesis on a new declaration.

* **Proof-internal `haveI`**:
  * `HasseWeil/Curves/IntegralClosure.lean:212` — `haveI : NeZero
    (2 : FractionRing (Polynomial F)) := by ...` inside the proof of
    `algebra_isSeparable_functionField`. Derived from the outer
    `[NeZero (2 : F)]` hypothesis via `FaithfulSMul.algebraMap_injective`.

* **`omit` (drops the hypothesis for one decl in a `variable` block)**:
  * `HasseWeil/LegendreForm.lean:89` — `omit [NeZero (2 : F)] in
    private theorem exists_legendreCurve_of_charNeTwoNF_a₆_eq_zero` —
    the section variable at L87 introduces `[NeZero (2 : F)]` but this
    particular helper does not need it.

* **Comment / docstring mentions only** (no typeclass introduction):
  * `HasseWeil/Curves/IntegralClosure.lean:29` — file-level docstring.
  * `HasseWeil/Curves/IntegralClosure.lean:840` — docstring of L842 instance.
  * `HasseWeil/Curves/Miller.lean:1487` — docstring of `afInputs_unconditional`.
  * `HasseWeil/Curves/Miller.lean:1488` — same docstring.
  * `HasseWeil/EC/TranslateValuation.lean:2154` — docstring explaining why
    `[NeZero 2/3]` is needed in a downstream consumer.
  * `HasseWeil/EC/TranslateValuation.lean:2161` — comment noting which
    project lemma drops the `[NeZero 2/3]` requirement.
  * `HasseWeil/Hasse/OpenLemmas.lean:44` — pre-amble.
  * `HasseWeil/Hasse/OpenLemmas.lean:50` — references this ticket.
  * `HasseWeil/Hasse/OpenLemmas.lean:102` — Miller-edge-case audit comment.
  * `HasseWeil/Hasse/OpenLemmas.lean:547` — outline for a future
    char-uniform open lemma.
  * `HasseWeil/Hasse/OpenLemmas.lean:830,834,836,842,843,860` — comment
    block describing the standing hypothesis cone for the Hasse pipeline.
  * `HasseWeil/Hasse/OpenLemmas.lean:1625,1626` — note on consumer drop.

## Appendix B — Reproducer commands

```bash
# In /home/chris/Github/Hasse-Weil:
grep -rn "NeZero (2 : " HasseWeil/ --include="*.lean"
grep -rn "NeZero (3 : " HasseWeil/ --include="*.lean"
grep -rn "NeZero 2\]\|NeZero 3\]" HasseWeil/ --include="*.lean"
grep -rEn "NeZero\s*\(?\s*[23]\b" HasseWeil/ --include="*.lean"
```

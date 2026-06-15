# Inventory: ./HasseWeil/OmegaPullbackCoeff.lean

**Total declarations**: 37 (3 defs, 34 lemmas/theorems, 0 instances)
**Imports**: `HasseWeil.Auxiliary.DiffQuotientRule`, `HasseWeil.FormalGroupCorrespondence`, `HasseWeil.WronskianAux`, `Mathlib.Algebra.Polynomial.Derivation`
**Lines**: 977

---

## Summary

This file defines the omega-based pullback coefficient `a_α` for endomorphisms α of an elliptic curve E (Silverman III.5), and proves `a_{[n]} = n` (Silverman III.5.3). The main bottleneck is the division-polynomial Wronskian identity (Silverman Exercise III.3.7), which is proved for small base cases and by sorry for n ≥ 5 (EDS addition formula missing). An axiom-clean alternative route is documented pointing to `RouteBInduction.lean`.

---

## Declarations

### `noncomputable def u_gen`
- **Type**: `u_gen W : KE` (where `KE = W.toAffine.FunctionField`)
- **What**: The element `u = 2y + a₁x + a₃` in K(E), which is the denominator of the invariant differential ω = u⁻¹ · D(x).
- **How**: Direct algebraic expression: `2 * algebraMap R KE root + a₁ * algebraMap F KE * x_poly + a₃`.
- **Hypotheses**: W is an elliptic curve over a field F with DecidableEq.
- **Uses from project**: none (just `algebraMap` and section variables)
- **Used by**: `u_gen_ne_zero`, `alpha_star_u_eq`, `mk_polynomialY_eq_u_gen`, `preΨ_two_mul_u_eq_ΨSq_sq_mul_alpha_star_u`, `divPoly_wronskian_identity_of_poly`, `divPoly_wronskian_identity_of_omega`, `omegaPullbackCoeff_mulByInt_of_poly`, `omegaPullbackCoeff`, `omegaPullbackCoeff_spec`
- **Visibility**: public
- **Lines**: 48–51, 4 lines (definition)
- **Notes**: None.

### `theorem u_gen_ne_zero`
- **Type**: `u_gen W ≠ 0`
- **What**: The denominator element u of the invariant differential is nonzero in K(E).
- **How**: Direct one-liner via `denom_ne_zero W.toAffine` from project infrastructure.
- **Hypotheses**: W is an elliptic curve.
- **Uses from project**: `denom_ne_zero` (from `FormalGroupCorrespondence` or `InvariantDifferential`)
- **Used by**: `omegaPullbackCoeff_mulByInt_of_poly`, `divPoly_wronskian_identity_of_omega`
- **Visibility**: public
- **Lines**: 53, 1 line (proof)
- **Notes**: None.

### `noncomputable def alpha_star_u`
- **Type**: `alpha_star_u W α : KE` for `α : Isogeny W.toAffine W.toAffine`
- **What**: The element `α*(u) = 2·α*(y) + a₁·α*(x) + a₃` in K(E), i.e. the pullback of u under isogeny α.
- **How**: Direct algebraic expression using `α.pullback` applied to the generators.
- **Hypotheses**: α is an endomorphism of the elliptic curve.
- **Uses from project**: none directly (uses `Isogeny.pullback` from the project)
- **Used by**: `alpha_star_u_eq`, `alpha_star_u_mulByInt`, `omegaPullbackCoeff`, `omegaPullbackCoeff_spec`, `preΨ_two_mul_u_eq_ΨSq_sq_mul_alpha_star_u`, `divPoly_wronskian_identity_of_poly`, `divPoly_wronskian_identity`, `divPoly_wronskian_identity_of_omega`, `omegaPullbackCoeff_mulByInt_of_poly`
- **Visibility**: public
- **Lines**: 57–61, 5 lines (definition)
- **Notes**: None.

### `theorem alpha_star_u_eq`
- **Type**: `alpha_star_u W α = α.pullback (u_gen W)`
- **What**: The pullback of u under α equals the abstract pullback algebra homomorphism applied to u_gen.
- **How**: By `simp` using `u_gen`'s definition and the fact that `α.pullback` is an F-algebra hom (`AlgHom.commutes`).
- **Hypotheses**: α is an endomorphism.
- **Uses from project**: `alpha_star_u`, `u_gen`
- **Used by**: `omegaPullbackCoeff_mulByInt_of_poly`, `divPoly_wronskian_identity_of_omega`
- **Visibility**: public
- **Lines**: 64–66, 3 lines (proof)
- **Notes**: None.

### `noncomputable def omegaPullbackCoeff`
- **Type**: `omegaPullbackCoeff W α : KE` for `α : Isogeny W.toAffine W.toAffine`
- **What**: The unique scalar c ∈ K(E) such that `c • ω = α*(u)⁻¹ • D(α*(x))` in the 1-dimensional Kähler module Ω[K(E)/F].
- **How**: Extracted via `.choose` from `exists_smul_eq_of_finrank_eq_one`, using `kaehler_rank_one` and `invariantDifferential_ne_zero`.
- **Hypotheses**: The Kähler module is 1-dimensional (from `kaehler_rank_one`) and the invariant differential is nonzero.
- **Uses from project**: `exists_smul_eq_of_finrank_eq_one`, `kaehler_rank_one`, `invariantDifferential_ne_zero`, `invariantDifferential`, `alpha_star_u`, `u_gen`
- **Used by**: `omegaPullbackCoeff_spec`, `omegaPullbackCoeff_mulByInt_of_poly`, `divPoly_wronskian_identity_of_omega`, `omegaPullbackCoeff_mulByInt`, `omegaPullbackCoeff_mulByInt_two`
- **Visibility**: public
- **Lines**: 70–78, 9 lines (definition, `set_option maxHeartbeats 400000`)
- **Notes**: `set_option maxHeartbeats 400000` at line 70, NO-COMMENT (no justifying explanation beyond the approach).

### `theorem omegaPullbackCoeff_spec`
- **Type**: `omegaPullbackCoeff W α • invariantDifferential W.toAffine = (alpha_star_u W α)⁻¹ • KaehlerDifferential.D F KE (α.pullback x_gen)`
- **What**: The defining property: omegaPullbackCoeff is the scalar relating ω to α*(u)⁻¹ · D(α*(x)).
- **How**: Direct `.choose_spec` from the same `exists_smul_eq_of_finrank_eq_one` call as the definition.
- **Hypotheses**: Same as `omegaPullbackCoeff`.
- **Uses from project**: `exists_smul_eq_of_finrank_eq_one`, `kaehler_rank_one`, `invariantDifferential_ne_zero`, `invariantDifferential`, `alpha_star_u`
- **Used by**: `omegaPullbackCoeff_mulByInt_of_poly`, `divPoly_wronskian_identity_of_omega`
- **Visibility**: public
- **Lines**: 82–94, 13 lines (proof)
- **Notes**: None.

### `theorem omegaPullbackCoeff_unique`
- **Type**: `c₁ • invariantDifferential W.toAffine = c₂ • invariantDifferential W.toAffine → c₁ = c₂`
- **What**: Uniqueness of the pullback coefficient: in the 1-dimensional Kähler module, scaling ω by two scalars yields equal results iff the scalars are equal (since ω ≠ 0).
- **How**: Uses `sub_smul` to reduce to `(c₁ - c₂) • ω = 0`, then `smul_eq_zero` to case-split on zero scalar vs zero ω, and `invariantDifferential_ne_zero` to eliminate the latter.
- **Hypotheses**: invariantDifferential is nonzero (which holds for elliptic curves).
- **Uses from project**: `invariantDifferential_ne_zero`, `invariantDifferential`
- **Used by**: `omegaPullbackCoeff_mulByInt_of_poly`
- **Visibility**: public
- **Lines**: 113–121, 9 lines (proof)
- **Notes**: None.

### `theorem mulByInt_pullback_x`
- **Type**: `(mulByInt W.toAffine n).pullback (algebraMap R KE (algebraMap (Polynomial F) R Polynomial.X)) = mulByInt_x W n` for `n ≠ 0`
- **What**: The pullback of x_gen under [n] equals the division polynomial expression `Φ_n / ΨSq_n = mulByInt_x W n`.
- **How**: Unfolds `mulByInt.pullback = mulByInt_pullbackAlgHom` (via `dif_neg hn`), then uses `mulByInt_pullbackRingHom`, `IsLocalization.lift_eq`, `mulByInt_coordHom`, `AdjoinRoot.lift_mk`, and `mulByInt_xHom` / `mulByInt_x`.
- **Hypotheses**: n ≠ 0.
- **Uses from project**: `mulByInt_pullbackAlgHom`, `mulByInt_pullbackRingHom`, `mulByInt_coordHom`, `mulByInt_xHom`, `mulByInt_x`
- **Used by**: `alpha_star_u_mulByInt`, `preΨ_two_mul_u_eq_ΨSq_sq_mul_alpha_star_u`, `divPoly_wronskian_identity_of_poly`, `divPoly_wronskian_identity_of_omega`, `omegaPullbackCoeff_mulByInt_of_poly`
- **Visibility**: public
- **Lines**: 130–143, 14 lines (proof)
- **Notes**: None.

### `theorem mulByInt_pullback_y`
- **Type**: `(mulByInt W.toAffine n).pullback (algebraMap R KE (AdjoinRoot.root W.toAffine.polynomial)) = mulByInt_y W n` for `n ≠ 0`
- **What**: The pullback of y_gen under [n] equals `ω_n / ψ_n³ = mulByInt_y W n`.
- **How**: Same unfolding strategy as `mulByInt_pullback_x`: `dif_neg hn`, then `mulByInt_pullbackRingHom`, `IsLocalization.lift_eq`, `mulByInt_coordHom`, `AdjoinRoot.lift_root`.
- **Hypotheses**: n ≠ 0.
- **Uses from project**: `mulByInt_pullbackAlgHom`, `mulByInt_pullbackRingHom`, `mulByInt_coordHom`, `mulByInt_y`
- **Used by**: `alpha_star_u_mulByInt`
- **Visibility**: public
- **Lines**: 146–156, 11 lines (proof)
- **Notes**: None.

### `theorem alpha_star_u_mulByInt`
- **Type**: `alpha_star_u W (mulByInt W.toAffine n) = 2 * mulByInt_y W n + a₁ * mulByInt_x W n + a₃` for `n ≠ 0`
- **What**: Evaluates `α*(u)` for α = [n] in terms of the division polynomial functions mulByInt_y and mulByInt_x.
- **How**: Direct `simp` using `mulByInt_pullback_x` and `mulByInt_pullback_y` applied to the definition of `alpha_star_u`.
- **Hypotheses**: n ≠ 0.
- **Uses from project**: `alpha_star_u`, `mulByInt_pullback_x`, `mulByInt_pullback_y`, `mulByInt_x`, `mulByInt_y`
- **Used by**: `preΨ_two_mul_u_eq_ΨSq_sq_mul_alpha_star_u`, `divPoly_wronskian_identity_of_poly`, `divPoly_wronskian_identity_of_omega`
- **Visibility**: public
- **Lines**: 164–169, 6 lines (proof)
- **Notes**: None.

### `private lemma ψ_ff_sq_eq`
- **Type**: `(algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ψ n))) ^ 2 = ΨSq_ff W n`
- **What**: In K(E), the square of ψ_n equals ΨSq_ff W n.
- **How**: Unfolds `ΨSq_ff`, uses `map_pow` and `Affine.CoordinateRing.mk_Ψ_sq`.
- **Hypotheses**: None beyond section variables.
- **Uses from project**: `ΨSq_ff`, `Affine.CoordinateRing.mk_ψ`, `Affine.CoordinateRing.mk_Ψ_sq`
- **Used by**: `ΨSq_ff_ne_zero'`, `preΨ_two_mul_u_eq_ΨSq_sq_mul_alpha_star_u`, `divPoly_wronskian_identity_of_poly`
- **Visibility**: private
- **Lines**: 193–198, 6 lines (proof)
- **Notes**: None.

### `private lemma ΨSq_ff_ne_zero'`
- **Type**: `{n : ℤ} → n ≠ 0 → ΨSq_ff W n ≠ 0`
- **What**: ΨSq_ff is nonzero for n ≠ 0, by injectivity of algebraMap and `ΨSq_poly_ne_zero`.
- **How**: Injectivity of the composition `(IsFractionRing.injective R KE).comp Affine.CoordinateRing.algebraMap_poly_injective` transports nonzero from polynomials.
- **Hypotheses**: n ≠ 0.
- **Uses from project**: `ΨSq_ff`, `ΨSq_poly_ne_zero`, `Affine.CoordinateRing.algebraMap_poly_injective`
- **Used by**: `preΨ_two_mul_u_eq_ΨSq_sq_mul_alpha_star_u`, `divPoly_wronskian_identity_of_poly`, `divPoly_wronskian_identity_of_omega`, `omegaPullbackCoeff_mulByInt_of_poly`
- **Visibility**: private
- **Lines**: 201–206, 6 lines (proof)
- **Notes**: None.

### `private lemma φ_ff_eq`
- **Type**: `algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.φ n)) = Φ_ff W n`
- **What**: The image of φ_n in K(E) equals `Φ_ff W n`.
- **How**: Uses `Affine.CoordinateRing.mk_φ` and unfolds `Φ_ff`.
- **Hypotheses**: None.
- **Uses from project**: `Φ_ff`, `Affine.CoordinateRing.mk_φ`
- **Used by**: `ω_spec_ff`
- **Visibility**: private
- **Lines**: 209–213, 5 lines (proof)
- **Notes**: None.

### `private lemma CC_eq_algebraMap`
- **Type**: `algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (Polynomial.C (Polynomial.C a))) = algebraMap F KE a`
- **What**: Double-constant polynomials map to field elements via the scalar tower.
- **How**: Uses `IsScalarTower.algebraMap_apply`.
- **Hypotheses**: `a : F`.
- **Uses from project**: None (uses `IsScalarTower.algebraMap_apply`)
- **Used by**: `ω_spec_ff`
- **Visibility**: private
- **Lines**: 216–221, 6 lines (proof)
- **Notes**: None.

### `private lemma ω_spec_ff`
- **Type**: `2 * ω_n + a₁ * Φ_ff W n * ψ_n + a₃ * ψ_n³ = ψc_n` in K(E)
- **What**: The division polynomial identity `2ω_n + a₁Φ_nψ_n + a₃ψ_n³ = ψc_n`, lifted to K(E) via algebraMap.
- **How**: Takes `W.ω_spec n` (a polynomial identity), applies `algebraMap R KE ∘ mk`, then uses `φ_ff_eq` and `CC_eq_algebraMap` to convert constants.
- **Hypotheses**: None.
- **Uses from project**: `Φ_ff`, `φ_ff_eq`, `CC_eq_algebraMap`
- **Used by**: `preΨ_two_mul_u_eq_ΨSq_sq_mul_alpha_star_u`, `divPoly_wronskian_identity_of_poly`, `divPoly_wronskian_identity_of_omega`
- **Visibility**: private
- **Lines**: 225–235, 11 lines (proof)
- **Notes**: None.

### `private lemma ψc_spec_ff`
- **Type**: `ψ_n * ψc_n = ψ_{2n}` in K(E) (i.e., `algebraMap (mk ψ n) * algebraMap (mk ψc n) = algebraMap (mk ψ (2n))`)
- **What**: The factorization identity for ψc in K(E): ψ_n · ψc_n = ψ_{2n}.
- **How**: Lifts `W.ψc_spec n` to K(E) via algebraMap and simp.
- **Hypotheses**: None.
- **Uses from project**: None (uses `W.ψc_spec`)
- **Used by**: `preΨ_two_mul_u_eq_ΨSq_sq_mul_alpha_star_u`, `divPoly_wronskian_identity_of_poly`, `divPoly_wronskian_identity_of_omega`
- **Visibility**: private
- **Lines**: 238–243, 6 lines (proof)
- **Notes**: None.

### `private lemma mk_polynomialY_eq_u_gen`
- **Type**: `algebraMap R KE (Affine.CoordinateRing.mk W.toAffine W.toAffine.polynomialY) = u_gen W`
- **What**: The image of polynomialY (= ψ₂) in K(E) equals u_gen = 2y + a₁x + a₃.
- **How**: Unfolds `polynomialY`, uses `AdjoinRoot.mk_X`, and simplifies via scalar tower `IsScalarTower.algebraMap_apply` to identify the constants; closes with `ring`.
- **Hypotheses**: None.
- **Uses from project**: `u_gen`
- **Used by**: `preΨ_two_mul_u_eq_ΨSq_sq_mul_alpha_star_u`, `divPoly_wronskian_identity_of_poly`
- **Visibility**: private
- **Lines**: 246–277, 32 lines (proof)
- **Notes**: Proof is 32 lines.

### `private lemma wronskian_Φ_ΨSq_zero`
- **Type**: `Φ_0' * ΨSq_0 - Φ_0 * ΨSq_0' = C(0 : F) * preΨ(0)` as polynomials
- **What**: Base case n=0 of the Wronskian identity.
- **How**: Direct `simp` using `Φ_zero`, `ΨSq_zero`, `preΨ_zero`.
- **Hypotheses**: None.
- **Uses from project**: None (uses `WeierstrassCurve.Φ_zero`, `ΨSq_zero`, `preΨ_zero`)
- **Used by**: `wronskian_Φ_ΨSq_nat`
- **Visibility**: private
- **Lines**: 280–284, 5 lines (proof)
- **Notes**: None.

### `private lemma wronskian_Φ_ΨSq_one`
- **Type**: `Φ_1' * ΨSq_1 - Φ_1 * ΨSq_1' = C(1:F) * preΨ(2)` as polynomials
- **What**: Base case n=1 of the Wronskian identity.
- **How**: Rewrites via `Φ_one`, `ΨSq_one`, `preΨ_two`, then `derivative_X`, `derivative_one`.
- **Hypotheses**: None.
- **Uses from project**: None (uses `WeierstrassCurve.*`)
- **Used by**: `wronskian_Φ_ΨSq_neg_one`, `wronskian_Φ_ΨSq_nat`
- **Visibility**: private
- **Lines**: 287–292, 6 lines (proof)
- **Notes**: None.

### `private lemma wronskian_Φ_ΨSq_neg_one`
- **Type**: `Φ_{-1}' * ΨSq_{-1} - Φ_{-1} * ΨSq_{-1}' = C(-1:F) * preΨ(-2)` as polynomials
- **What**: Base case n=-1 of the Wronskian identity, derived from n=1 by negation symmetry.
- **How**: Uses `Φ_neg`, `ΨSq_neg`, `preΨ_neg` together with `wronskian_Φ_ΨSq_one` and sign manipulation via `exact_mod_cast`.
- **Hypotheses**: None.
- **Uses from project**: None (uses `WeierstrassCurve.*`), calls `wronskian_Φ_ΨSq_one`
- **Used by**: not used (superseded by `wronskian_Φ_ΨSq_neg_of` applied to `wronskian_Φ_ΨSq_nat`)
- **Visibility**: private
- **Lines**: 295–308, 14 lines (proof)
- **Notes**: Likely dead code — `wronskian_Φ_ΨSq_nat` handles n=-1 via `wronskian_Φ_ΨSq_neg_of`.

### `private lemma wronskian_Φ_ΨSq_two`
- **Type**: `Φ_2' * ΨSq_2 - Φ_2 * ΨSq_2' = C(2:F) * preΨ(4)` as polynomials
- **What**: Base case n=2 of the Wronskian identity, verified by direct ring computation.
- **How**: Expands `Φ_two`, `ΨSq_two`, `preΨ_four`, computes derivatives via `simp`, expands `C` operations, closes with `ring1`. Only uses `b₂, b₄, b₆, b₈` (not individual `a_i`).
- **Hypotheses**: None.
- **Uses from project**: None (uses `WeierstrassCurve.*`)
- **Used by**: `wronskian_Φ_ΨSq_nat`, `omegaPullbackCoeff_mulByInt_two`
- **Visibility**: private
- **Lines**: 314–336, 23 lines (proof)
- **Notes**: Axiom-clean (no sorry). Used by both the general induction and the axiom-clean base case for [2].

### `private lemma wronskian_Φ_ΨSq_neg_of`
- **Type**: If the Wronskian identity holds at n, it holds at -n.
- **What**: Negation symmetry for the Wronskian: `wronskian(-n) ← wronskian(n)`.
- **How**: Uses `Φ_neg`, `ΨSq_neg`, `preΨ_neg`, then sign cancellation via `Polynomial.C_neg` and `push_cast`.
- **Hypotheses**: The Wronskian identity at n.
- **Uses from project**: None (uses `WeierstrassCurve.*`)
- **Used by**: `wronskian_Φ_ΨSq`
- **Visibility**: private
- **Lines**: 339–349, 11 lines (proof)
- **Notes**: None.

### `private lemma wronskian_X_mul_sub`
- **Type**: For polynomials f q: `(X*f - q)' * f - (X*f - q) * f' = f² - (q' * f - q * f')`
- **What**: A pure polynomial identity reducing the Wronskian of (X*f - q) with f to f² minus the Wronskian of q with f.
- **How**: `simp` + `ring` after expanding the Leibniz rule.
- **Hypotheses**: None (omits `DecidableEq` and `IsElliptic`).
- **Uses from project**: None
- **Used by**: `wronskian_Φ_ΨSq_four`
- **Visibility**: private
- **Lines**: 352–358, 7 lines (proof)
- **Notes**: `omit [DecidableEq F] [W.toAffine.IsElliptic]` — instances not needed.

### `private lemma wronskian_Φ_ΨSq_three`
- **Type**: `Φ_3' * ΨSq_3 - Φ_3 * ΨSq_3' = C(3:F) * preΨ(6)` as polynomials
- **What**: Base case n=3 of the Wronskian identity.
- **How**: Expands all division polynomials down to `Ψ₃, preΨ₄, Ψ₂Sq`, then uses `wronskian_aux_three` (from `WronskianAux.lean`) via `linear_combination W.Ψ₃ * haux`.
- **Hypotheses**: None (omits `DecidableEq` and `IsElliptic`).
- **Uses from project**: `wronskian_aux_three` (from `WronskianAux`)
- **Used by**: `wronskian_Φ_ΨSq_nat`
- **Visibility**: private
- **Lines**: 369–401, 33 lines (proof)
- **Notes**: `set_option maxHeartbeats 6400000` at line 367, NO-COMMENT. Proof is 33 lines. `omit [DecidableEq F] [W.toAffine.IsElliptic]`. The comment explains the ring computation was factored out to `WronskianAux.lean`.

### `private lemma wronskian_Φ_ΨSq_four`
- **Type**: `Φ_4' * ΨSq_4 - Φ_4 * ΨSq_4' = C(4:F) * preΨ(8)` as polynomials
- **What**: Base case n=4 of the Wronskian identity.
- **How**: Uses `wronskian_X_mul_sub` to restructure the Wronskian, expands `preΨ(8)` via the even/odd recursions, then applies `wronskian_aux_four` from `WronskianAux.lean` via `linear_combination haux`.
- **Hypotheses**: None (omits `DecidableEq` and `IsElliptic`).
- **Uses from project**: `wronskian_X_mul_sub`, `wronskian_aux_four` (from `WronskianAux`)
- **Used by**: `wronskian_Φ_ΨSq_nat`
- **Visibility**: private
- **Lines**: 414–453, 40 lines (proof)
- **Notes**: `set_option maxHeartbeats 6400000` at line 412, NO-COMMENT (comment nearby says ~57 GB ring elaboration in WronskianAux). Proof is 40 lines.

### `private lemma wronskian_Φ_ΨSq_nat`
- **Type**: For `m : ℕ`, `Φ_m' * ΨSq_m - Φ_m * ΨSq_m' = C(m:F) * preΨ(2m)` as polynomials
- **What**: The Wronskian identity for all natural numbers, by strong induction. Base cases m=0..4 are handled; m ≥ 5 is **sorry**.
- **How**: `Nat.strong_induction_on` with pattern match on m. Cases 0–4 use the base case lemmas; case `n+5` is `sorry` (EDS addition formula not yet in mathlib).
- **Hypotheses**: None.
- **Uses from project**: `wronskian_Φ_ΨSq_zero`, `wronskian_Φ_ΨSq_one`, `wronskian_Φ_ΨSq_two`, `wronskian_Φ_ΨSq_three`, `wronskian_Φ_ΨSq_four`
- **Used by**: `wronskian_Φ_ΨSq`
- **Visibility**: private
- **Lines**: 495–514, 20 lines (proof, including sorry)
- **Notes**: **Contains `sorry` at line 514** for the m ≥ 5 inductive step. Extensive docstring documents that the EDS addition formula (Ward's relation) is required but missing from mathlib. An axiom-clean alternative exists downstream via `RouteBInduction.lean`.

### `theorem wronskian_Φ_ΨSq`
- **Type**: `∀ n : ℤ, Φ_n' * ΨSq_n - Φ_n * ΨSq_n' = C(n:F) * preΨ(2n)` as polynomials
- **What**: The division polynomial Wronskian identity (Silverman Exercise III.3.7) for all integers n.
- **How**: Case split on sign of n; for n < 0 uses `wronskian_Φ_ΨSq_neg_of` + `wronskian_Φ_ΨSq_nat`; for n ≥ 0 uses `wronskian_Φ_ΨSq_nat` directly.
- **Hypotheses**: None. (Inherits sorry from `wronskian_Φ_ΨSq_nat` for n ≥ 5.)
- **Uses from project**: `wronskian_Φ_ΨSq_neg_of`, `wronskian_Φ_ΨSq_nat`
- **Used by**: `divPoly_wronskian_identity`, `omegaPullbackCoeff_mulByInt`
- **Visibility**: public
- **Lines**: 523–536, 14 lines (proof)
- **Notes**: Inherits sorry-taint from `wronskian_Φ_ΨSq_nat` for |n| ≥ 5.

### `private lemma Φ_ff_eq_algebraMap_poly`
- **Type**: `Φ_ff W n = algebraMap (Polynomial F) KE (W.Φ n)`
- **What**: `Φ_ff W n` factors through `algebraMap (Polynomial F) KE` via the scalar tower.
- **How**: One-liner via `IsScalarTower.algebraMap_apply`.
- **Hypotheses**: None.
- **Uses from project**: `Φ_ff`
- **Used by**: `divPoly_wronskian_identity_of_poly`
- **Visibility**: private
- **Lines**: 539–541, 3 lines (proof)
- **Notes**: None.

### `private lemma ΨSq_ff_eq_algebraMap_poly`
- **Type**: `ΨSq_ff W n = algebraMap (Polynomial F) KE (W.ΨSq n)`
- **What**: `ΨSq_ff W n` factors through `algebraMap (Polynomial F) KE` via the scalar tower.
- **How**: One-liner via `IsScalarTower.algebraMap_apply`.
- **Hypotheses**: None.
- **Uses from project**: `ΨSq_ff`
- **Used by**: `divPoly_wronskian_identity_of_poly`
- **Visibility**: private
- **Lines**: 543–545, 3 lines (proof)
- **Notes**: None.

### `theorem preΨ_two_mul_u_eq_ΨSq_sq_mul_alpha_star_u`
- **Type**: `algebraMap (Polynomial F) KE (W.preΨ (2*n)) * u_gen W = ΨSq_ff W n ^ 2 * alpha_star_u W (mulByInt W.toAffine n)` for `n ≠ 0`
- **What**: The ω_n/preΨ bridge identity: `preΨ(2n) · u = ΨSq_n² · α*(u)` for the [n]-pullback. This is axiom-clean (does not use the Wronskian) and provides the key link between polynomial and K(E) level.
- **How**: Sets `ψn = mk(ψ n)`, `ψcn = mk(ψc n)` in K(E). Uses `ψc_spec_ff` (preΨ(2n)·u = ψn·ψcn), then `ω_spec_ff` and `ψ_ff_sq_eq` to evaluate α*(u) = ψcn/ψn³, giving ΨSq² · α*(u) = ψn⁴ · ψcn/ψn³ = ψn·ψcn; closes with `field_simp`.
- **Hypotheses**: n ≠ 0.
- **Uses from project**: `u_gen`, `ΨSq_ff`, `alpha_star_u`, `ψ_ff_sq_eq`, `ΨSq_ff_ne_zero'`, `ψc_spec_ff`, `ω_spec_ff`, `alpha_star_u_mulByInt`, `mulByInt_y`, `mulByInt_x`, `mk_polynomialY_eq_u_gen`, `Φ_ff`
- **Used by**: (documented as used by `RouteBInduction.lean` to recover the polynomial Wronskian; not used in this file)
- **Visibility**: public
- **Lines**: 556–593, 38 lines (proof)
- **Notes**: Proof is 38 lines. Axiom-clean and notable: the comment explicitly says "does NOT use the division-polynomial Wronskian". Key axiom-clean bridge for the Route-B approach.

### `theorem divPoly_wronskian_identity_of_poly`
- **Type**: Given `hpoly : Φ_n' ΨSq_n - Φ_n ΨSq_n' = C(n:F) * preΨ(2n)`, proves the K(E)-level identity `(Φ_n' ΨSq_n - Φ_n ΨSq_n') * u = (n : F) * ΨSq_n² * α*(u)` in K(E).
- **What**: Lifts the polynomial Wronskian identity to K(E), parametrized by the polynomial-level hypothesis `hpoly`. This lets specific n (e.g. n=2) be discharged axiom-cleanly.
- **How**: Lifts `hpoly` to K(E) via `Φ_ff_eq_algebraMap_poly` and `ΨSq_ff_eq_algebraMap_poly`, then `push_cast`, uses `ψc_spec_ff`, `ω_spec_ff`, `ψ_ff_sq_eq` to reduce both sides to `n * ψn * ψcn` in K(E), then closes with `field_simp`.
- **Hypotheses**: n ≠ 0; the polynomial Wronskian identity at n.
- **Uses from project**: `Φ_ff_eq_algebraMap_poly`, `ΨSq_ff_eq_algebraMap_poly`, `u_gen`, `alpha_star_u`, `ΨSq_ff`, `ΨSq_ff_ne_zero'`, `ψ_ff_sq_eq`, `ψc_spec_ff`, `ω_spec_ff`, `alpha_star_u_mulByInt`, `mulByInt_y`, `mulByInt_x`, `mk_polynomialY_eq_u_gen`, `Φ_ff`
- **Used by**: `divPoly_wronskian_identity`, `omegaPullbackCoeff_mulByInt_of_poly`
- **Visibility**: public
- **Lines**: 609–719, 111 lines (proof)
- **Notes**: `set_option maxHeartbeats 3200000` at line 595, NO-COMMENT. Proof is 111 lines — very long. The comment explains the purpose of the parametrization by `hpoly`.

### `theorem divPoly_wronskian_identity`
- **Type**: `∀ n ≠ 0, (Φ_n' ΨSq_n - Φ_n ΨSq_n') * u = n * ΨSq_n² * α*(u)` in K(E)
- **What**: The general K(E)-level Wronskian identity, applying the general polynomial Wronskian `wronskian_Φ_ΨSq`.
- **How**: One-liner: `divPoly_wronskian_identity_of_poly W n hn (wronskian_Φ_ΨSq W n)`.
- **Hypotheses**: n ≠ 0. (Inherits sorry-taint from `wronskian_Φ_ΨSq`.)
- **Uses from project**: `divPoly_wronskian_identity_of_poly`, `wronskian_Φ_ΨSq`
- **Used by**: (not used in this file; available for external consumption)
- **Visibility**: public
- **Lines**: 724–733, 10 lines (proof)
- **Notes**: Inherits sorry-taint. Not used in this file.

### `theorem D_poly_eval`
- **Type**: For `p : Polynomial F`, `KaehlerDifferential.D F KE (algebraMap (Polynomial F) KE p) = algebraMap (Polynomial F) KE (Polynomial.derivative p) • KaehlerDifferential.D F KE (algebraMap (Polynomial F) KE Polynomial.X)`
- **What**: The chain rule for the universal derivation D: D(p(x)) = p'(x) · D(x) for any polynomial p evaluated at the generic point x ∈ K(E).
- **How**: Shows `algebraMap (Polynomial F) KE q = Polynomial.aeval x_ff q` by induction, then applies `Derivation.comp_aeval_eq` from mathlib.
- **Hypotheses**: None (has `set_option linter.unusedSectionVars false`).
- **Uses from project**: `D_x_ne_zero` (only in later uses, not here directly)
- **Used by**: `omegaPullbackCoeff_mulByInt_of_poly` (via `hDΦ`, `hDΨ`), `divPoly_wronskian_identity_of_omega`
- **Visibility**: public
- **Lines**: 744–762, 19 lines (proof)
- **Notes**: Uses `Derivation.comp_aeval_eq` from mathlib. Has `set_option linter.unusedSectionVars false`.

### `theorem omegaPullbackCoeff_mulByInt_of_poly`
- **Type**: Given `hpoly : Φ_n' ΨSq_n - Φ_n ΨSq_n' = C(n:F) * preΨ(2n)`, proves `omegaPullbackCoeff W (mulByInt W.toAffine n) = algebraMap F KE n`.
- **What**: The key result `a_{[n]} = n`, parametrized by the polynomial-level Wronskian hypothesis. This lets the n=2 case be discharged axiom-cleanly.
- **How**: Uses `omegaPullbackCoeff_unique` to reduce to showing `algebraMap F KE n` satisfies the spec. Expands `omegaPullbackCoeff_spec`, then: writes `α*(x) = Φ * Ψ⁻¹` via `mulByInt_pullback_x`; applies Leibniz rule `Derivation.leibniz` and `D_inv_smul`; chain rule `D_poly_eval` for `D(Φ)` and `D(Ψ)`; simp/smul arithmetic; `divPoly_wronskian_identity_of_poly` to match the Wronskian scalar; clears denominators via `field_simp`.
- **Hypotheses**: n ≠ 0; polynomial Wronskian identity at n.
- **Uses from project**: `omegaPullbackCoeff_unique`, `omegaPullbackCoeff_spec`, `u_gen`, `u_gen_ne_zero`, `alpha_star_u`, `alpha_star_u_eq`, `ΨSq_ff`, `ΨSq_ff_ne_zero'`, `mulByInt_pullback_x`, `mulByInt_x`, `D_poly_eval`, `D_x_ne_zero`, `D_inv_smul`, `divPoly_wronskian_identity_of_poly`
- **Used by**: `omegaPullbackCoeff_mulByInt`, `omegaPullbackCoeff_mulByInt_two`
- **Visibility**: public
- **Lines**: 775–864, 90 lines (proof)
- **Notes**: Proof is 90 lines. Core computational proof of `a_{[n]} = n`.

### `theorem divPoly_wronskian_identity_of_omega`
- **Type**: Given `homega : omegaPullbackCoeff W (mulByInt W.toAffine n) = algebraMap F KE n`, proves the K(E)-level Wronskian identity `(Φ_n' ΨSq_n - Φ_n ΨSq_n') * u = n * ΨSq_n² * α*(u)`.
- **What**: The **reverse direction**: derives the K(E) Wronskian from `a_{[n]} = n`. Together with `preΨ_two_mul_u_eq_ΨSq_sq_mul_alpha_star_u` and injectivity of `algebraMap (Polynomial F) KE`, this recovers the polynomial Wronskian — without using the EDS addition formula.
- **How**: Takes `omegaPullbackCoeff_spec`, substitutes `homega`, then runs exactly the same Leibniz + chain-rule + smul-arithmetic as `omegaPullbackCoeff_mulByInt_of_poly` in reverse; extracts the scalar equation via `smul_eq_zero` and `D_x_ne_zero`; clears denominators via `field_simp` and `linear_combination`.
- **Hypotheses**: n ≠ 0; `omegaPullbackCoeff W (mulByInt W.toAffine n) = n`.
- **Uses from project**: `omegaPullbackCoeff_spec`, `u_gen`, `u_gen_ne_zero`, `alpha_star_u`, `alpha_star_u_eq`, `ΨSq_ff`, `ΨSq_ff_ne_zero'`, `mulByInt_pullback_x`, `mulByInt_x`, `D_poly_eval`, `D_x_ne_zero`, `D_inv_smul`, `Φ_ff`
- **Used by**: (not used in this file; designed for `RouteBInduction.lean`)
- **Visibility**: public
- **Lines**: 868–947, 80 lines (proof)
- **Notes**: `set_option maxHeartbeats 3200000` at line 868, with comment: "The Kähler-module Leibniz/chain-rule unfolding plus the two `field_simp` denominator clearings push the default heartbeat budget". Proof is 80 lines. Not used in this file — designed as an axiom-clean recovery tool via Route-B.

### `theorem omegaPullbackCoeff_mulByInt`
- **Type**: `∀ n ≠ 0, omegaPullbackCoeff W (mulByInt W.toAffine n) = algebraMap F KE n`
- **What**: `a_{[n]} = n` (Silverman III.5.3, IV.2.3) for all n ≠ 0, via the general Wronskian.
- **How**: One-liner: `omegaPullbackCoeff_mulByInt_of_poly W n hn (wronskian_Φ_ΨSq W n)`.
- **Hypotheses**: n ≠ 0. (Inherits sorry-taint from `wronskian_Φ_ΨSq` for |n| ≥ 5.)
- **Uses from project**: `omegaPullbackCoeff_mulByInt_of_poly`, `wronskian_Φ_ΨSq`
- **Used by**: (not used in this file; primary export for downstream)
- **Visibility**: public
- **Lines**: 961–963, 3 lines (proof)
- **Notes**: Has a note in the docstring that the axiom-clean version is `omegaPullbackCoeff_mulByInt_routeB` in `RouteBInduction.lean`.

### `theorem omegaPullbackCoeff_mulByInt_two`
- **Type**: `omegaPullbackCoeff W (mulByInt W.toAffine 2) = algebraMap F KE (2 : ℤ)`
- **What**: Axiom-clean base case: `a_{[2]} = 2`, using only the ring-verified `wronskian_Φ_ΨSq_two` (no sorry).
- **How**: `omegaPullbackCoeff_mulByInt_of_poly W 2 (by norm_num) (by simpa using wronskian_Φ_ΨSq_two W)`.
- **Hypotheses**: None (no sorry-taint).
- **Uses from project**: `omegaPullbackCoeff_mulByInt_of_poly`, `wronskian_Φ_ΨSq_two`
- **Used by**: (not used in this file; seeds Route-B induction in `RouteBInduction.lean`)
- **Visibility**: public
- **Lines**: 972–975, 4 lines (proof)
- **Notes**: Axiom-clean. Explicitly designed to seed the Route-B chord induction.

---

## Key API Summary

**Definitions**: `u_gen`, `alpha_star_u`, `omegaPullbackCoeff`

**Main theorems**: `wronskian_Φ_ΨSq` (polynomial Wronskian, sorry for n≥5), `omegaPullbackCoeff_mulByInt` (a_{[n]} = n, inherits sorry), `omegaPullbackCoeff_mulByInt_two` (axiom-clean base case), `preΨ_two_mul_u_eq_ΨSq_sq_mul_alpha_star_u` (axiom-clean bridge), `divPoly_wronskian_identity_of_omega` (reverse direction for Route-B)

**Dead code candidates**: `wronskian_Φ_ΨSq_neg_one` (not referenced; n=-1 handled by `wronskian_Φ_ΨSq_neg_of`), `divPoly_wronskian_identity` (not referenced in file), `omegaPullbackCoeff_mulByInt` (not referenced in file), `divPoly_wronskian_identity_of_omega` (not referenced in file)

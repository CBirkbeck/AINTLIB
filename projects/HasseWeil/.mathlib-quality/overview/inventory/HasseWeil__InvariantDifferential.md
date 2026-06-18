# Inventory: ./HasseWeil/InvariantDifferential.lean

**Total declarations**: 8 (4 private lemmas + 2 public lemmas + 1 noncomputable def + 1 theorem)

Imports: `HasseWeil.Basic`, `Mathlib.RingTheory.Kaehler.Basic`, `Mathlib.RingTheory.Kaehler.Polynomial`, `Mathlib.RingTheory.Unramified.Field`

---

### `private lemma polynomialY_ne_zero`

- **Type**: `(E : Affine F) [E.IsElliptic] : E.polynomialY ≠ 0`
- **What**: The partial derivative `2Y + a₁X + a₃` of the Weierstrass polynomial with respect to `Y` is nonzero as an element of `F[X][Y]`. In characteristic 2 this relies on `Δ ≠ 0`.
- **How**: Assumes `polynomialY = 0`, extracts coefficients to derive `a₁ = 0` and `a₃ = 0`, then uses `b₂ = b₄ = b₆ = 0` to show `Δ = 0`, contradicting `E.isUnit_Δ`.
- **Hypotheses**: `E` is an affine Weierstrass curve with the `IsElliptic` property (which asserts `Δ` is a unit in `F`).
- **Uses from project**: `Affine.polynomialY`, `WeierstrassCurve.Δ`, `WeierstrassCurve.b₂`, `WeierstrassCurve.b₄`, `WeierstrassCurve.b₆`, `E.isUnit_Δ`
- **Used by**: `D_x_ne_zero` (line 154), `denom_ne_zero` (line 268)
- **Visibility**: private
- **Lines**: 27–43, proof body ~16 lines
- **Notes**: None

---

### `private lemma algebraMap_polynomial_injective`

- **Type**: `(E : Affine F) [E.IsElliptic] : Function.Injective (algebraMap (Polynomial F) E.FunctionField)`
- **What**: The canonical ring map `F[X] → K(E)` (the function field of `E`) is injective, i.e., `x` is transcendental over `F`.
- **How**: Uses the scalar-tower `F[X] → E.CoordinateRing → K(E)` (IsFractionRing injective on the second leg) and injectivity of `F[X] → CoordinateRing` via `AdjoinRoot.mk_eq_zero` + `Polynomial.natDegree_le_of_dvd` + `Affine.natDegree_polynomial` to get a degree contradiction.
- **Hypotheses**: `E` is an elliptic curve over `F`.
- **Uses from project**: `Affine.natDegree_polynomial`, `E.FunctionField`, `E.CoordinateRing`
- **Used by**: `not_isAlgebraic_x` (line 77)
- **Visibility**: private
- **Lines**: 46–58, proof body ~13 lines
- **Notes**: None

---

### `private lemma aeval_x_eq_algebraMap'`

- **Type**: `(E : Affine F) (p : Polynomial F) : Polynomial.aeval (algebraMap (Polynomial F) E.FunctionField Polynomial.X) p = algebraMap (Polynomial F) E.FunctionField p`
- **What**: Evaluating a polynomial `p : F[X]` at the image of `X` in `K(E)` equals applying the algebra map directly. Concretely, `p(x) = algebraMap p` in `K(E)`.
- **How**: Induction on `p` via `Polynomial.induction_on'`; monomial case uses `map_pow`, `map_mul`, `Polynomial.C_mul_X_pow_eq_monomial`.
- **Hypotheses**: None beyond `E : Affine F` (no `IsElliptic` needed).
- **Uses from project**: `E.FunctionField`
- **Used by**: `not_isAlgebraic_x` (line 78, via `.symm.trans`)
- **Visibility**: private
- **Lines**: 61–71, proof body ~10 lines
- **Notes**: Duplicates a local `haeval` block also proved inline inside `D_x_ne_zero` (lines 104–113). This standalone version is used only by `not_isAlgebraic_x`.

---

### `private lemma not_isAlgebraic_x`

- **Type**: `(E : Affine F) [E.IsElliptic] : ¬ IsAlgebraic F (algebraMap (Polynomial F) E.FunctionField Polynomial.X)`
- **What**: The coordinate `x ∈ K(E)` is transcendental over `F`.
- **How**: An algebraic witness `p` with `p(x) = 0` would give `algebraMap p = 0` via `aeval_x_eq_algebraMap'`, then `p = 0` by `algebraMap_polynomial_injective`, contradicting `p ≠ 0`.
- **Hypotheses**: `E` is an elliptic curve over `F`.
- **Uses from project**: `algebraMap_polynomial_injective`, `aeval_x_eq_algebraMap'`
- **Used by**: `D_x_ne_zero` (line 224)
- **Visibility**: private
- **Lines**: 74–78, proof body ~5 lines
- **Notes**: None

---

### `lemma D_x_ne_zero`

- **Type**: `(E : Affine F) [E.IsElliptic] : KaehlerDifferential.D F E.FunctionField (algebraMap E.CoordinateRing E.FunctionField (algebraMap (Polynomial F) E.CoordinateRing Polynomial.X)) ≠ 0`
- **What**: The universal derivation `D(x)` is nonzero in the Kähler differential module `Ω[K(E)/F]`. This is the key analytic fact underlying the existence of the invariant differential.
- **How**: By contradiction: assume `D(x) = 0`. First prove `D` kills all of `F[X]` (by induction on monomials, using `Derivation.leibniz` and `D(x^n) = 0`). Then use the Weierstrass relation `y² + cy = RHS(x)` (established via `AdjoinRoot.mk_eq_mk`) to derive `(2y + c)·D(y) = 0`, and since `2y + c ≠ 0` (using `polynomialY_ne_zero` + `AdjoinRoot.mk_ne_zero_of_natDegree_lt` + `IsFractionRing.injective`), get `D(y) = 0`. Then `D` kills all of `CoordinateRing` by `Affine.CoordinateRing.exists_smul_basis_eq` decomposition, hence kills all of `K(E)` via `IsFractionRing.div_surjective` and the quotient rule. Then `Ω = 0` by `KaehlerDifferential.span_range_derivation`, so `K(E)/F` is formally unramified, hence separable algebraic (via `Algebra.FormallyUnramified.iff_isSeparable`), contradicting `not_isAlgebraic_x`.
- **Hypotheses**: `E` is an elliptic curve over `F`; the field `F` is `DecidableEq`.
- **Uses from project**: `polynomialY_ne_zero`, `not_isAlgebraic_x`, `Affine.polynomial`, `Affine.polynomialY`, `Affine.natDegree_polynomial`, `Affine.monic_polynomial`, `Affine.CoordinateRing.mk`, `E.FunctionField`, `E.CoordinateRing`
- **Used by**: `invariantDifferential_ne_zero` (line 315); also exported to `OmegaPullbackCoeff.lean` (line 822, 920), `PullbackCoeff.lean` (line 68), `GapQfKernel.lean` (line 852)
- **Visibility**: public
- **Lines**: 80–225 (with `set_option maxHeartbeats 3200000` at line 80), proof body ~140 lines
- **Notes**: `set_option maxHeartbeats 3200000` — NO inline justifying comment (just a docstring on the overall proof strategy). Proof is 140 lines — well over 30. The internal `haeval` block at lines 104–113 duplicates `aeval_x_eq_algebraMap'`. The proof strategy (derive `D = 0` on generators → formally unramified → algebraic → contradiction) is the standard route for function fields of curves.

---

### `lemma denom_ne_zero`

- **Type**: `(2 : E.FunctionField) * y + algebraMap F E.FunctionField E.a₁ * x + algebraMap F E.FunctionField E.a₃ ≠ 0` (where `x, y` are the standard coordinates in `K(E)`)
- **What**: The denominator `2y + a₁x + a₃` of the invariant differential is nonzero in `K(E)`. This is the image of `polynomialY` under the canonical map.
- **How**: Rewrites the goal in terms of a polynomial variable `c`, identifies `2y + c` as `algebraMap(CoordinateRing.mk E polynomialY)`, shows `polynomialY` has lower degree than `E.polynomial` via `polynomialY_ne_zero` + `AdjoinRoot.mk_ne_zero_of_natDegree_lt`, then injectivity of `IsFractionRing.injective` gives the result.
- **Hypotheses**: `E : Affine F` with `[E.IsElliptic]`.
- **Uses from project**: `polynomialY_ne_zero`, `Affine.polynomialY`, `Affine.monic_polynomial`, `Affine.natDegree_polynomial`, `Affine.CoordinateRing.mk`, `E.FunctionField`, `E.CoordinateRing`
- **Used by**: `invariantDifferential_ne_zero` (line 315); also used by `OmegaPullbackCoeff.lean:53` (`u_gen_ne_zero`), `FormalGroupCorrespondence.lean:89,177`
- **Visibility**: public
- **Lines**: 237–295, proof body ~59 lines
- **Notes**: Proof over 30 lines (59 lines). The proof largely duplicates the inner `hne` subproof of `D_x_ne_zero` (lines 151–181); these two could be unified. The proof has a `set_option linter.unusedDecidableInType false` wrapper on `invariantDifferential_ne_zero` which precedes (line 309), not on this lemma directly.

---

### `noncomputable def invariantDifferential`

- **Type**: `(E : Affine F) [E.IsElliptic] : KaehlerDifferential F E.FunctionField`
- **What**: The invariant differential `ω = dx / (2y + a₁x + a₃)` on the elliptic curve `E`, constructed concretely as `(2y + a₁x + a₃)⁻¹ • D(x)` in the Kähler differential module `Ω[K(E)/F]`.
- **How**: Direct definition: scalar multiplication of `D(x)` by the inverse of the denominator in the `E.FunctionField`-module structure of `Ω[K(E)/F]`.
- **Hypotheses**: `E : Affine F` with `[E.IsElliptic]`.
- **Uses from project**: `E.FunctionField`, `E.CoordinateRing`, `E.polynomial`, `E.a₁`, `E.a₃`
- **Used by**: `invariantDifferential_ne_zero` (line 313); widely used across the project (OmegaPullbackCoeff, InvariantDifferentialPullback, FormalGroupCorrespondence, Differentials, etc.)
- **Visibility**: public
- **Lines**: 299–307, definition body ~9 lines
- **Notes**: This is the primary API object exported from this file.

---

### `theorem invariantDifferential_ne_zero`

- **Type**: `(E : Affine F) [E.IsElliptic] : invariantDifferential E ≠ 0`
- **What**: The invariant differential `ω` is nonzero. Corresponds to Silverman Proposition III.1.5.
- **How**: Unfolds the definition and applies `smul_ne_zero` with `inv_ne_zero (denom_ne_zero E)` (denominator nonzero) and `D_x_ne_zero E` (derivation of `x` nonzero).
- **Hypotheses**: `E : Affine F` with `[E.IsElliptic]`.
- **Uses from project**: `invariantDifferential`, `denom_ne_zero`, `D_x_ne_zero`
- **Used by**: Widely used throughout the project (OmegaPullbackCoeff, EC/DifferentialOrd, Curves/Differentials, FormalGroupCorrespondence); unused within this file after line 315.
- **Visibility**: public
- **Lines**: 309–315 (with `set_option linter.unusedDecidableInType false` at line 309), proof body ~3 lines
- **Notes**: `set_option linter.unusedDecidableInType false` is applied; no heartbeat override needed. This is the key public theorem exported by the file.

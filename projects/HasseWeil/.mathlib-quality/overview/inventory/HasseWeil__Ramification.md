# Inventory: ./HasseWeil/Ramification.lean

> **File status (from module docstring):** Orphaned file (status 2026-04-20). Proves Silverman II.1.1 (local ring at smooth point is DVR) via Dedekind-domain approach through `IsIntegralClosure.isDedekindDomain`. The ticket T-II-1-001 is proved sorry-free elsewhere; this file is not imported from `HasseWeil.lean`. No `sorry` tactic appears in any proof body (all `sorry` occurrences are in comments or docstrings).

---

### `private theorem polynomial_mem_nonZeroDivisors`
- **Type**: `(E : Affine F) [E.IsElliptic] : E.polynomial ∈ (F[X][Y])⁰`
- **What**: The Weierstrass polynomial is a non-zero-divisor in the bivariate polynomial ring `F[X][Y]`, since `F[X][Y]` is a domain and the polynomial is irreducible (hence nonzero).
- **How**: Uses `mem_nonZeroDivisors_of_ne_zero` and `Irreducible.ne_zero Affine.irreducible_polynomial`.
- **Hypotheses**: `E` is an elliptic curve (`IsElliptic`).
- **Uses from project**: `Affine.irreducible_polynomial`
- **Used by**: `coordinateRing_krullDimLE_one`
- **Visibility**: private
- **Lines**: 123–125, proof length 1 line
- **Notes**: None

---

### `private theorem coordinateRing_krullDimLE_one`
- **Type**: `(E : Affine F) [E.IsElliptic] : Ring.KrullDimLE 1 E.CoordinateRing`
- **What**: The coordinate ring of an elliptic curve has Krull dimension at most 1, obtained by the principal ideal theorem applied to the quotient by the (non-zero-divisor) Weierstrass polynomial.
- **How**: Rewrites via `Ring.krullDimLE_iff`, applies `ringKrullDim_quotient_succ_le_of_nonZeroDivisor (polynomial_mem_nonZeroDivisors E)`, and computes `ringKrullDim (F[X][Y]) = 2` via `Polynomial.ringKrullDim_of_isNoetherianRing`.
- **Hypotheses**: `E.IsElliptic`.
- **Uses from project**: `polynomial_mem_nonZeroDivisors`
- **Used by**: `coordinateRing_dimensionLEOne`
- **Visibility**: private
- **Lines**: 130–142, proof length ~12 lines
- **Notes**: None

---

### `instance coordinateRing_dimensionLEOne`
- **Type**: `(E : Affine F) [E.IsElliptic] : Ring.DimensionLEOne E.CoordinateRing`
- **What**: Every nonzero prime ideal of the coordinate ring is maximal, i.e., the ring has dimension ≤ 1.
- **How**: Derives from `coordinateRing_krullDimLE_one` via `Ring.krullDimLE_one_iff_of_noZeroDivisors`.
- **Hypotheses**: `E.IsElliptic`.
- **Uses from project**: `coordinateRing_krullDimLE_one`
- **Used by**: `maximalIdeal_isPrincipal_of_nonsingular`, `coordinateRing_isIntegrallyClosed`
- **Visibility**: public
- **Lines**: 146–150, proof length 3 lines
- **Notes**: This is one of the two headline results called out in the module docstring.

---

### `private lemma quotient_comp_of_eq`
- **Type**: `{E : Affine F} (P : Ideal E.CoordinateRing) : π.comp (AdjoinRoot.of E.polynomial) = (Polynomial.evalRingHom x₀).comp (Polynomial.mapRingHom φ)` where `π = Ideal.Quotient.mk P`, `φ` is the `F`-algebra map, `x₀` is the residue image of `mk(C X)`.
- **What**: The composite `π ∘ AdjoinRoot.of` (embedding `F[X]` into `R/P`) equals evaluation at the X-residue after base change.
- **How**: Polynomial induction (`Polynomial.induction_on'`), `Polynomial.eval_map`, and `Polynomial.eval₂_monomial`.
- **Hypotheses**: None beyond `E : Affine F`.
- **Uses from project**: (none — all mathlib)
- **Used by**: `quotient_mk_eq_base_evalEval`
- **Visibility**: private
- **Lines**: 165–181, proof length ~16 lines
- **Notes**: None

---

### `private lemma quotient_mk_eq_base_evalEval`
- **Type**: `{E : Affine F} (P : Ideal E.CoordinateRing) (g : F[X][Y]) : π (AdjoinRoot.mk E.polynomial g) = (g.map (Polynomial.mapRingHom φ)).evalEval x₀ y₀`
- **What**: The image in `R/P` of `mk(g)` equals the evaluation of the base-changed bivariate polynomial at the residue coordinates `(x₀, y₀)`.
- **How**: Uses `AdjoinRoot.aeval_eq` to rewrite `mk g = g.eval₂ (of E.polynomial) (root E.polynomial)`, applies `Polynomial.hom_eval₂`, then `Polynomial.eval₂_map` and `quotient_comp_of_eq`.
- **Hypotheses**: None beyond `E : Affine F`.
- **Uses from project**: `quotient_comp_of_eq`
- **Used by**: `nonsingular_at_maximal`
- **Visibility**: private
- **Lines**: 184–204, proof length ~20 lines
- **Notes**: None

---

### `private lemma nonsingular_at_maximal`
- **Type**: `(E : Affine F) [E.IsElliptic] (P : Ideal E.CoordinateRing) (hPmax : P.IsMaximal) : AdjoinRoot.mk E.polynomial E.polynomialX ∉ P ∨ AdjoinRoot.mk E.polynomial E.polynomialY ∉ P`
- **What**: At every maximal ideal of the coordinate ring, at least one of the partial derivatives `∂W/∂X`, `∂W/∂Y` is not in the ideal; this is the abstract algebraic form of nonsingularity at every point.
- **How**: Sets up the residue field `k = R/P` (a field since P is maximal), evaluates the curve equation at `(x₀, y₀)` in `k` using `quotient_mk_eq_base_evalEval`, applies `Affine.equation_iff_nonsingular_of_Δ_ne_zero` to the base-changed curve (using `E.isUnit_Δ`), then translates back via the quotient map.
- **Hypotheses**: `E.IsElliptic`.
- **Uses from project**: `quotient_mk_eq_base_evalEval`
- **Used by**: `maximalIdeal_isPrincipal_of_nonsingular`
- **Visibility**: private
- **Lines**: 210–232, proof length ~22 lines
- **Notes**: None

---

### `noncomputable instance instModulePolynomialCoordinateRing`
- **Type**: `(E : Affine F) : Module (Polynomial F) E.CoordinateRing`
- **What**: Explicit module instance for `E.CoordinateRing` as a `F[X]`-module, bypassing noncomputable depth limits in typeclass synthesis.
- **How**: Direct `@Algebra.toModule` from `Affine.CoordinateRing.instAlgebraPolynomial`.
- **Hypotheses**: None.
- **Uses from project**: (none — uses `instAlgebraPolynomial` from mathlib/project boundary)
- **Used by**: `instModuleFinitePolynomialCoordinateRing`, `instIsTorsionFreePolynomialCoordinateRing`, downstream instances
- **Visibility**: public
- **Lines**: 242–244, proof length 1 line
- **Notes**: Workaround for `maxSynthPendingDepth = 3` limit.

---

### `noncomputable instance instModuleFinitePolynomialCoordinateRing`
- **Type**: `(E : Affine F) : Module.Finite (Polynomial F) E.CoordinateRing`
- **What**: The coordinate ring is a finitely generated `F[X]`-module (degree-2 monic Weierstrass polynomial gives a rank-2 basis).
- **How**: `Affine.monic_polynomial.finite_adjoinRoot`.
- **Hypotheses**: None.
- **Uses from project**: `Affine.monic_polynomial`
- **Used by**: `instIsTorsionFreePolynomialCoordinateRing`, `coordinateRing_algebraMap_injective`, downstream instances
- **Visibility**: public
- **Lines**: 246–248, proof length 1 line
- **Notes**: None

---

### `noncomputable instance instIsTorsionFreePolynomialCoordinateRing`
- **Type**: `(E : Affine F) [E.IsElliptic] : Module.IsTorsionFree (Polynomial F) E.CoordinateRing`
- **What**: The coordinate ring has no `F[X]`-torsion (equivalently, the algebra map `F[X] → R` has trivial annihilators).
- **How**: `AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero` applied to `Irreducible.prime Affine.irreducible_polynomial` and `Affine.degree_polynomial` (= 2 ≠ 0).
- **Hypotheses**: `E.IsElliptic`.
- **Uses from project**: `Affine.irreducible_polynomial`, `Affine.degree_polynomial`
- **Used by**: `functionField_finiteDimensional` (implicit via torsion-free + finite → FiniteDimensional over fraction ring)
- **Visibility**: public
- **Lines**: 250–254, proof length ~4 lines
- **Notes**: None

---

### `theorem coordinateRing_algebraMap_injective`
- **Type**: `(E : Affine F) : Function.Injective (algebraMap (Polynomial F) E.CoordinateRing)`
- **What**: The embedding `F[X] ↪ R` is injective because the Weierstrass polynomial has positive degree.
- **How**: `AdjoinRoot.of.injective_of_degree_ne_zero` with `Affine.degree_polynomial` = 2 ≠ 0.
- **Hypotheses**: None (no `IsElliptic` needed).
- **Uses from project**: `Affine.degree_polynomial`
- **Used by**: `coordinateRing_faithfulSMul`, `maximalIdeal_isPrincipal_of_nonsingular` (step 0 in both branches)
- **Visibility**: public
- **Lines**: 260–263, proof length 2 lines
- **Notes**: None

---

### `noncomputable instance coordinateRing_faithfulSMul`
- **Type**: `(E : Affine F) [E.IsElliptic] : FaithfulSMul (Polynomial F) E.CoordinateRing`
- **What**: `F[X]` acts faithfully on the coordinate ring.
- **How**: `faithfulSMul_iff_algebraMap_injective` + `coordinateRing_algebraMap_injective`.
- **Hypotheses**: `E.IsElliptic`.
- **Uses from project**: `coordinateRing_algebraMap_injective`
- **Used by**: `functionField_faithfulSMul`, `functionField_algebra_fractionRing`, `functionField_isScalarTower`
- **Visibility**: public
- **Lines**: 268–271, proof length 3 lines
- **Notes**: None

---

### `noncomputable instance functionField_faithfulSMul`
- **Type**: `(E : Affine F) [E.IsElliptic] : FaithfulSMul (Polynomial F) E.FunctionField`
- **What**: `F[X]` acts faithfully on `E.FunctionField` (lifted from faithful action on `CoordinateRing`).
- **How**: `FractionRing.instFaithfulSMul`.
- **Hypotheses**: `E.IsElliptic`.
- **Uses from project**: `coordinateRing_faithfulSMul` (implicit via instance resolution)
- **Used by**: `functionField_algebra_fractionRing`, `functionField_isScalarTower`
- **Visibility**: public
- **Lines**: 274–276, proof length 1 line
- **Notes**: None

---

### `noncomputable instance functionField_algebra_fractionRing`
- **Type**: `(E : Affine F) [E.IsElliptic] : Algebra (FractionRing (Polynomial F)) E.FunctionField`
- **What**: The rational function field `F(X)` acts as a `FractionRing(F[X])`-algebra on the function field of `E`.
- **How**: `FractionRing.liftAlgebra` via `functionField_faithfulSMul E`.
- **Hypotheses**: `E.IsElliptic`.
- **Uses from project**: `functionField_faithfulSMul`
- **Used by**: `functionField_isScalarTower`, `functionField_finiteDimensional`, `functionField_isSeparable`
- **Visibility**: public
- **Lines**: 292–294, proof length 1 line
- **Notes**: None

---

### `noncomputable instance functionField_isScalarTower`
- **Type**: `(E : Affine F) [E.IsElliptic] : IsScalarTower (Polynomial F) (FractionRing (Polynomial F)) E.FunctionField`
- **What**: Establishes the scalar tower `F[X] → FractionRing(F[X]) → FunctionField`.
- **How**: `FractionRing.isScalarTower_liftAlgebra` via `functionField_faithfulSMul E`.
- **Hypotheses**: `E.IsElliptic`.
- **Uses from project**: `functionField_faithfulSMul`
- **Used by**: `coordinateRing_isIntegralClosure`, `functionField_isSeparable`
- **Visibility**: public
- **Lines**: 297–300, proof length 1 line
- **Notes**: None

---

### `noncomputable instance functionField_finiteDimensional`
- **Type**: `(E : Affine F) [E.IsElliptic] : FiniteDimensional (FractionRing (Polynomial F)) E.FunctionField`
- **What**: The function field is a finite-dimensional extension of the rational function field `F(X)`, of degree 2.
- **How**: `inferInstance` — synthesized automatically from `instIsTorsionFreePolynomialCoordinateRing`, `instModuleFinitePolynomialCoordinateRing`, and the tower instance.
- **Hypotheses**: `E.IsElliptic`.
- **Uses from project**: (instances implicitly used)
- **Used by**: `functionField_isSeparable`
- **Visibility**: public
- **Lines**: 318–320, proof length 1 line
- **Notes**: `set_option maxHeartbeats 800000` with comment "Typeclass synthesis for FiniteDimensional over the tower FractionRing F[X] → K(E) needs extra heartbeats."

---

### `private theorem derivative_polynomial_eq_polynomialY`
- **Type**: `(E : Affine F) : Polynomial.derivative E.polynomial = E.polynomialY`
- **What**: The formal Y-derivative of the Weierstrass polynomial equals `polynomialY = 2Y + a₁X + a₃`.
- **How**: `simp` with derivative lemmas; concludes by `congr 1`.
- **Hypotheses**: None.
- **Uses from project**: `Affine.polynomial`, `Affine.polynomialY`
- **Used by**: `mk_polynomialY_sq` (via `polynomialY_sq_eq_disc`), `maximalIdeal_isPrincipal_of_nonsingular` (char-≠-2 branch derivative computation), `polynomialY_ne_zero`, `root_aeval_polynomial_map` (used in `functionField_isSeparable`)
- **Visibility**: private
- **Lines**: 343–348, proof length ~5 lines
- **Notes**: None

---

### `private lemma polynomialY_sq_eq_disc`
- **Type**: `(E : Affine F) : E.polynomialY * E.polynomialY - C ((C E.a₁ * X + C E.a₃) ^ 2 + C 4 * (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆)) = E.polynomial * C (C 4)`
- **What**: The discriminant identity in `F[X][Y]`: `polynomialY² - d = W · C(C 4)` where `d` is the Y-discriminant polynomial.
- **How**: `simp` with map lemmas, then `ring` over `F[X][Y]`.
- **Hypotheses**: None.
- **Uses from project**: `Affine.polynomialY`, `Affine.polynomial`
- **Used by**: `mk_polynomialY_sq`, `maximalIdeal_isPrincipal_of_nonsingular` (char-≠-2 branch, mapped identity)
- **Visibility**: private
- **Lines**: 352–356, proof length ~4 lines
- **Notes**: `set_option maxHeartbeats 3200000` with comment "Large `ring` over F[X][Y] needs extra heartbeats."

---

### `private lemma mk_polynomialY_sq`
- **Type**: `(E : Affine F) : (AdjoinRoot.mk E.polynomial E.polynomialY) ^ 2 = AdjoinRoot.mk E.polynomial (C d)` where `d = (a₁X + a₃)² + 4(X³ + a₂X² + a₄X + a₆) ∈ F[X]`
- **What**: In the coordinate ring `R`, the square of `mk(polynomialY)` lands in `F[X]` (i.e., equals `mk(C d)`).
- **How**: Rewrites `sq` as `mul`, applies `AdjoinRoot.mk_eq_mk`, and uses `polynomialY_sq_eq_disc`.
- **Hypotheses**: None.
- **Uses from project**: `polynomialY_sq_eq_disc`
- **Used by**: `disc_not_in_P`, `maximalIdeal_isPrincipal_of_nonsingular` (both branches)
- **Visibility**: private
- **Lines**: 360–366, proof length ~6 lines
- **Notes**: `set_option maxHeartbeats 800000` with comment "AdjoinRoot rewriting over the bivariate polynomial ring needs extra heartbeats."

---

### `private lemma disc_not_in_P`
- **Type**: `(E : Affine F) (P : Ideal E.CoordinateRing) [P.IsPrime] (hY : AdjoinRoot.mk E.polynomial E.polynomialY ∉ P) : AdjoinRoot.mk E.polynomial (C d) ∉ P`
- **What**: If `mk(polynomialY) ∉ P`, then the Y-discriminant `d` (as an element of `R`) is also not in `P` (since `mk(polynomialY)² = mk(C d)` and `P` is prime).
- **How**: Uses `mk_polynomialY_sq`, membership in `P`, and `IsPrime.mem_of_pow_mem`.
- **Hypotheses**: `P` is prime; `mk(polynomialY) ∉ P`.
- **Uses from project**: `mk_polynomialY_sq`
- **Used by**: `maximalIdeal_isPrincipal_of_nonsingular`
- **Visibility**: private
- **Lines**: 370–378, proof length ~8 lines
- **Notes**: None

---

### `private lemma four_polynomialX_eq_jacobi`
- **Type**: `(E : Affine F) : C (C (4 : F)) * E.polynomialX = C (C (2 * E.a₁)) * E.polynomialY - C (C 2 * C E.a₁ * (C E.a₁ * X + C E.a₃) + C 4 * (C 3 * X ^ 2 + C (2 * E.a₂) * X + C E.a₄))`
- **What**: The Jacobian identity in `F[X][Y]`: `4 · ∂W/∂X = 2a₁ · ∂W/∂Y - d'` where `d'` is the X-derivative of the Y-discriminant `d`.
- **How**: `simp` with map lemmas, then `ring` over `F[X][Y]`.
- **Hypotheses**: None.
- **Uses from project**: `Affine.polynomialX`, `Affine.polynomialY`
- **Used by**: `dprime_not_in_p`
- **Visibility**: private
- **Lines**: 388–394, proof length ~6 lines
- **Notes**: `set_option maxHeartbeats 3200000` with comment "Large `ring` over F[X][Y] needs extra heartbeats."

---

### `private lemma dprime_not_in_p`
- **Type**: `(E : Affine F) (P : Ideal E.CoordinateRing) [P.IsPrime] (hY : mk(polynomialY) ∈ P) (hX : mk(polynomialX) ∉ P) (h4 : (4 : F) ≠ 0) : d' ∉ P.comap (algebraMap (Polynomial F) E.CoordinateRing)` where `d'` is the X-derivative of the Y-discriminant
- **What**: Under char ≠ 2 and with `∂W/∂Y ∈ P` but `∂W/∂X ∉ P`, the X-derivative of the Y-discriminant is not in the contraction `p = P ∩ F[X]`. This is the "smoothness at a vertical tangent" consequence.
- **How**: Uses `four_polynomialX_eq_jacobi` mapped through `AdjoinRoot.mk`, combines primality of `P` with the fact that `4 ∈ F` is a unit (char ≠ 2), to obtain a contradiction.
- **Hypotheses**: `P` prime; `mk(polynomialY) ∈ P`; `mk(polynomialX) ∉ P`; `(4 : F) ≠ 0` (char ≠ 2).
- **Uses from project**: `four_polynomialX_eq_jacobi`
- **Used by**: `maximalIdeal_isPrincipal_of_nonsingular`
- **Visibility**: private
- **Lines**: 400–438, proof length ~38 lines
- **Notes**: Proof > 30 lines.

---

### `private lemma maximalIdeal_le_of_isField_quotient`
- **Type**: `{R : Type*} [CommRing R] [IsLocalRing R] (J : Ideal R) (hField : IsField (R ⧸ J)) : IsLocalRing.maximalIdeal R ≤ J`
- **What**: In a local ring, if `R/J` is a field then `J` contains the maximal ideal (so `J` equals or contains the maximal ideal).
- **How**: `IsLocalRing.eq_maximalIdeal` applied to `Ideal.Quotient.maximal_of_isField`.
- **Hypotheses**: `R` is a local commutative ring; `R/J` is a field.
- **Uses from project**: (none)
- **Used by**: `maximalIdeal_isPrincipal_of_nonsingular`
- **Visibility**: private
- **Lines**: 441–444, proof length ~3 lines
- **Notes**: None

---

### `private lemma exists_coeffs_via_polynomialY`
- **Type**: `(E : Affine F) (h2 : (2 : F) ≠ 0) (x : E.CoordinateRing) : ∃ a' b' : F[X], x = AdjoinRoot.mk E.polynomial (C a') + AdjoinRoot.mk E.polynomial (C b') * AdjoinRoot.mk E.polynomial E.polynomialY`
- **What**: In char ≠ 2, every element of the coordinate ring can be written as `mk(C a') + mk(C b') · mk(polynomialY)`, providing a basis decomposition replacing `{1, Y}` by `{1, polynomialY}`.
- **How**: Uses `Affine.CoordinateRing.exists_smul_basis_eq` to get the `{1, Y}` decomposition, then performs a change of basis via `Y = (polynomialY - C(a₁X+a₃))/2` (using `inv2 = (1/2 : F)`), carrying out a careful polynomial identity with `calc`.
- **Hypotheses**: `(2 : F) ≠ 0` (char ≠ 2).
- **Uses from project**: `Affine.CoordinateRing.exists_smul_basis_eq`, `Affine.CoordinateRing.smul`, `Affine.polynomialY`
- **Used by**: `maximalIdeal_isPrincipal_of_nonsingular` (char ≠ 2 branch, step 6)
- **Visibility**: private
- **Lines**: 452–516, proof length ~64 lines
- **Notes**: `set_option maxHeartbeats 1600000` with comment "Large polynomial manipulations plus AdjoinRoot pushes need extra heartbeats." Proof > 30 lines.

---

### `private theorem maximalIdeal_isPrincipal_of_nonsingular`
- **Type**: `(E : Affine F) [E.IsElliptic] (P : Ideal E.CoordinateRing) (_ : P ≠ ⊥) (hPmax : P.IsMaximal) : (IsLocalRing.maximalIdeal (Localization.AtPrime P)).IsPrincipal`
- **What**: For any nonzero maximal ideal `P`, the maximal ideal of the localization `R_P` is principal. This is the key principality step for the Dedekind-domain proof, equivalent to each local ring being a DVR.
- **How**: Massive case split: (case 1) `mk(polynomialY) ∉ P` — uses the discriminant identity + squarefreeness of `Wbar` over `k = F[X]/p` to establish `R_P/J ≅ (k[Y]/(Wbar))_P` is reduced and then a field (dimension 0 local ring), so `J = maximalIdeal`, hence `P.map f` is principal. (case 2) `mk(polynomialY) ∈ P`, char 2 supersingular subcase: vacuous (unit in `P` contradiction). (case 2) char 2 ordinary (a₁ ≠ 0): `P = span{mk(C c)}` by reducing to `localRing_isDVR` at the concrete affine point `(x₀, α)` when `δ` is a square, or by explicit ring map `proj : R → AdjoinRoot(f_quad)` when `δ` is not a square. (case 2) char ≠ 2: uses `dprime_not_in_p` + `polynomialY_sq_eq_disc` to show `π ∥ d` (valuation exactly 1), then `exists_coeffs_via_polynomialY` to show `P.map f = span{f(mk(polynomialY))}`. Key references: `maximalIdeal_le_of_isField_quotient`, `nonsingular_at_maximal`, `disc_not_in_P`, `mk_polynomialY_sq`, `dprime_not_in_p`, `exists_coeffs_via_polynomialY`, `coordinateRing_algebraMap_injective`, `HasseWeil.localRing_isDVR`, `pointIdeal_isMaximal`.
- **Hypotheses**: `E.IsElliptic`; `P ≠ ⊥`; `P.IsMaximal`.
- **Uses from project**: `coordinateRing_algebraMap_injective`, `nonsingular_at_maximal`, `disc_not_in_P`, `mk_polynomialY_sq`, `polynomialY_sq_eq_disc`, `dprime_not_in_p`, `exists_coeffs_via_polynomialY`, `maximalIdeal_le_of_isField_quotient`, `derivative_polynomial_eq_polynomialY`, `HasseWeil.localRing_isDVR`, `pointIdeal_isMaximal`, `Affine.CoordinateRing.exists_smul_basis_eq`, `Affine.CoordinateRing.smul`
- **Used by**: `coordinateRing_isIntegrallyClosed`
- **Visibility**: private
- **Lines**: 522–1517, proof length ~995 lines
- **Notes**: `set_option maxHeartbeats 6400000` with comment "Very large case analysis over char = 2 vs char ≠ 2 branches, plus nested AdjoinRoot arguments." Proof > 30 lines (by far the longest in the file). The bulk of the file. Contains an extended outline comment at lines 682–741 explaining the char=2 strategy.

---

### `instance coordinateRing_isIntegrallyClosed`
- **Type**: `(E : Affine F) [E.IsElliptic] : IsIntegrallyClosed E.CoordinateRing`
- **What**: The coordinate ring of an elliptic curve is integrally closed in its fraction field (the function field).
- **How**: `IsIntegrallyClosed.of_localization_maximal`: at each nonzero maximal `P`, `R_P` has principal maximal ideal (from `maximalIdeal_isPrincipal_of_nonsingular`), plus `Ring.DimensionLEOne` (from `coordinateRing_dimensionLEOne`), hence is a DVR via `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain`, hence integrally closed via `UniqueFactorizationMonoid.instIsIntegrallyClosed`.
- **Hypotheses**: `E.IsElliptic`.
- **Uses from project**: `maximalIdeal_isPrincipal_of_nonsingular`; `coordinateRing_dimensionLEOne` (implicit via `Ring.DimensionLEOne.localization`)
- **Used by**: `coordinateRing_isIntegralClosure`; `isIntegrallyClosed_coordinateRing`
- **Visibility**: public
- **Lines**: 1533–1564, proof length ~31 lines
- **Notes**: Proof > 30 lines.

---

### `noncomputable instance coordinateRing_isIntegralClosure`
- **Type**: `(E : Affine F) [E.IsElliptic] : IsIntegralClosure E.CoordinateRing (Polynomial F) E.FunctionField`
- **What**: The coordinate ring is the integral closure of `F[X]` in the function field.
- **How**: Injectivity from `IsFractionRing.injective`. For the integrality characterization: forward direction uses `IsIntegral.tower_top` + `coordinateRing_isIntegrallyClosed`; backward direction uses `IsIntegral.of_finite` + `IsScalarTower.toAlgHom`.
- **Hypotheses**: `E.IsElliptic`.
- **Uses from project**: `coordinateRing_isIntegrallyClosed`
- **Used by**: `coordinateRing_isDedekindDomain`
- **Visibility**: public
- **Lines**: 1568–1584, proof length ~15 lines
- **Notes**: `set_option maxHeartbeats 800000` with comment "Typeclass synthesis over the tower F[X] → CoordinateRing → FunctionField needs more budget."

---

### `private theorem polynomialY_ne_zero`
- **Type**: `(E : Affine F) [E.IsElliptic] : E.polynomialY ≠ 0`
- **What**: The Y-partial-derivative of the Weierstrass polynomial is nonzero, derived from the nonzero discriminant `Δ ≠ 0`.
- **How**: If `polynomialY = 0`, extracts `a₁ = 0`, `a₃ = 0` by coefficient extraction, then shows `Δ = 0` (by explicit `simp` computation), contradicting `E.isUnit_Δ`.
- **Hypotheses**: `E.IsElliptic`.
- **Uses from project**: `Affine.polynomialY`
- **Used by**: `functionField_isSeparable`
- **Visibility**: private
- **Lines**: 1597–1613, proof length ~16 lines
- **Notes**: Opens `Classical` locally.

---

### `private theorem root_aeval_polynomial_map`
- **Type**: `(E : Affine F) [E.IsElliptic] : Polynomial.aeval (algebraMap E.CoordinateRing E.FunctionField (AdjoinRoot.root E.polynomial)) (E.polynomial.map (algebraMap (Polynomial F) (FractionRing (Polynomial F)))) = 0`
- **What**: The image of `AdjoinRoot.root E.polynomial` in `E.FunctionField` is a root of the Weierstrass polynomial (base-changed to `FractionRing(F[X])[X]`).
- **How**: `Polynomial.aeval_map_algebraMap` + `AdjoinRoot.aeval_algHom_eq_zero` + commuting of algebra maps via `IsScalarTower.algebraMap_apply`.
- **Hypotheses**: `E.IsElliptic`.
- **Uses from project**: (none beyond imports)
- **Used by**: `functionField_isSeparable`
- **Visibility**: private
- **Lines**: 1618–1625, proof length ~7 lines
- **Notes**: `set_option maxHeartbeats 1600000` with comment "The image of AdjoinRoot.root in the function field is a root of W.map(algebraMap). Polynomial.aeval_map_algebraMap rewriting needs extra heartbeats."

---

### `noncomputable instance functionField_isSeparable`
- **Type**: `(E : Affine F) [E.IsElliptic] : Algebra.IsSeparable (FractionRing (Polynomial F)) E.FunctionField`
- **What**: The function field extension over the rational function field is separable (of degree 2, generated by a root of the separable Weierstrass polynomial).
- **How**: Uses `Field.finSepDegree_dvd_finrank` and computes `finrank = 2` via `Algebra.IsAlgebraic.finrank_of_isFractionRing` and `Affine.CoordinateRing.basis`. Shows `finSepDegree ≠ 1` by a contradiction argument: purely inseparable + `y` separable (proven via `minpoly K y = W'` using `polynomialY_ne_zero`) forces `y ∈ K`, contradicting degree 2. Concludes `finSepDegree = 2 = finrank` via `finSepDegree_eq_finrank_iff`.
- **Hypotheses**: `E.IsElliptic`.
- **Uses from project**: `functionField_finiteDimensional`, `root_aeval_polynomial_map`, `derivative_polynomial_eq_polynomialY`, `polynomialY_ne_zero`, `Affine.monic_polynomial`, `Affine.irreducible_polynomial`, `Affine.natDegree_polynomial`, `Affine.CoordinateRing.basis`
- **Used by**: `coordinateRing_isDedekindDomain` (implicit via `IsIntegralClosure.isDedekindDomain`)
- **Visibility**: public
- **Lines**: 1630–1690, proof length ~60 lines
- **Notes**: `set_option maxHeartbeats 800000` with comment "The separability proof reasons over two cases via finSepDegree; typeclass synthesis for the tower through FractionRing F[X] needs more budget." Proof > 30 lines.

---

### `instance coordinateRing_isDedekindDomain`
- **Type**: `(E : Affine F) [E.IsElliptic] : IsDedekindDomain E.CoordinateRing`
- **What**: The coordinate ring of an elliptic curve is a Dedekind domain. This is one of the two headline results.
- **How**: `IsIntegralClosure.isDedekindDomain (Polynomial F) (FractionRing (Polynomial F)) E.FunctionField E.CoordinateRing` — assembles `IsIntegralClosure`, `FiniteDimensional`, `IsSeparable`, `IsDedekindDomain (Polynomial F)` (PID), and `IsNoetherianRing`.
- **Hypotheses**: `E.IsElliptic`.
- **Uses from project**: `coordinateRing_isIntegralClosure`, `functionField_isSeparable`, `functionField_finiteDimensional` (all implicit via instance search)
- **Used by**: `isIntegrallyClosed_coordinateRing` (implicitly)
- **Visibility**: public
- **Lines**: 1715–1718, proof length ~3 lines
- **Notes**: `set_option maxHeartbeats 4000000` with comment "Assembling the Dedekind domain conclusion from integral closure + separability + Noetherian via mathlib's `IsIntegralClosure.isDedekindDomain` requires a heavy typeclass search."

---

### `instance isIntegrallyClosed_coordinateRing`
- **Type**: `(E : Affine F) [E.IsElliptic] : IsIntegrallyClosed E.CoordinateRing`
- **What**: Restatement of integral closure as a consequence of being a Dedekind domain.
- **How**: `inferInstance` — follows automatically from `coordinateRing_isDedekindDomain`.
- **Hypotheses**: `E.IsElliptic`.
- **Uses from project**: `coordinateRing_isDedekindDomain` (implicit)
- **Used by**: unused in file (redundant with `coordinateRing_isIntegrallyClosed`)
- **Visibility**: public
- **Lines**: 1722–1724, proof length 1 line
- **Notes**: Redundant: `coordinateRing_isIntegrallyClosed` was already proved directly; this is a second proof of the same thing via the Dedekind-domain route. Dead code candidate within this file.

---

## Summary statistics

| Metric | Value |
|--------|-------|
| Total declarations | 28 |
| Defs | 0 |
| Lemmas/theorems | 14 |
| Instances | 14 |
| Sorries in proof bodies | 0 |
| `set_option maxHeartbeats` occurrences | 10 |
| Proofs > 30 lines | 5 |

## Key API declarations (used by 3+ others in this file)

- `coordinateRing_algebraMap_injective` — used by `coordinateRing_faithfulSMul`, `maximalIdeal_isPrincipal_of_nonsingular` (twice, both branches)
- `mk_polynomialY_sq` — used by `disc_not_in_P`, `maximalIdeal_isPrincipal_of_nonsingular` (twice)
- `polynomialY_sq_eq_disc` — used by `mk_polynomialY_sq`, `maximalIdeal_isPrincipal_of_nonsingular`
- `nonsingular_at_maximal` — used by `maximalIdeal_isPrincipal_of_nonsingular`; relies on `quotient_mk_eq_base_evalEval` (which relies on `quotient_comp_of_eq`)
- `functionField_faithfulSMul` — used by `functionField_algebra_fractionRing`, `functionField_isScalarTower`
- `derivative_polynomial_eq_polynomialY` — used by `maximalIdeal_isPrincipal_of_nonsingular`, `polynomialY_ne_zero` (indirectly via `functionField_isSeparable`)

## Notes

- File is **orphaned and not imported** by `HasseWeil.lean`; T-II-1-001 is proved elsewhere. No `sorry` tactic appears in any proof body (all `sorry` mentions are in comments).
- The dominant declaration is `maximalIdeal_isPrincipal_of_nonsingular` at ~995 proof lines, containing a complete char-2/char-≠-2 case analysis for principality of the maximal ideal in the localization.
- `isIntegrallyClosed_coordinateRing` at the end is redundant with `coordinateRing_isIntegrallyClosed` (proved earlier directly via the DVR route).

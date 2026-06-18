# Inventory: ./HasseWeil/LocalExpansion.lean

**File**: `HasseWeil/LocalExpansion.lean`
**Lines**: 1–868
**Imports**: `HasseWeil.MulByIntPullback`, `HasseWeil.FormalGroup`, `Mathlib.RingTheory.LaurentSeries`, `Mathlib.RingTheory.PowerSeries.Inverse`

**Summary**: Constructs the *local expansion* ring homomorphism `localExpand : K(E) →+* LaurentSeries F` for an elliptic curve `W` over a field `F`. The strategy follows Silverman IV.1: define the unit series `u(z) = w(z)/z³`, form `formalX = t⁻²·u⁻¹` and `formalY = -t⁻³·u⁻¹`, prove they satisfy the Weierstrass equation, then extend the substitution to the fraction field via `IsFractionRing.lift`. No `sorry` appears in any proof body; the file comment warning that "hard parts are sorry-marked" is stale/inaccurate.

---

## Declarations

### `noncomputable def formalU`
- **Type**: `PowerSeries F`
- **What**: The "unit part" `u(z) = w(z)/z³`, defined by shifting the coefficient sequence of `formalW` down by 3 indices.
- **How**: Direct `PowerSeries.mk` of `fun n ↦ formalW_coeff W (n + 3)`.
- **Hypotheses**: `W : WeierstrassCurve F`, `[Field F]`, `[W.toAffine.IsElliptic]`
- **Uses from project**: `formalW_coeff` (FormalGroup.lean)
- **Used by**: `formalU_constantCoeff`, `formalU_isUnit`, `formalU_inv` (definition), `formalU_mul_inv`, `formalU_inv_mul`, `formalW_eq_X3_mul_U`, `formalY_mul_formalW`, `formalX_mul_formalW`
- **Visibility**: public
- **Lines**: 70–72 (2 lines, term-mode def)
- **Notes**: none

---

### `@[simp] theorem formalU_constantCoeff`
- **Type**: `@PowerSeries.constantCoeff F _ (formalU W) = 1`
- **What**: The constant (degree-0) coefficient of `formalU` is 1; follows from `formalW_coeff_three`.
- **How**: `rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, formalU, PowerSeries.coeff_mk, formalW_coeff_three]`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `formalW_coeff_three` (FormalGroup.lean)
- **Used by**: `formalU_isUnit`, `formalU_mul_inv`, `formalU_inv_mul`, `formalU_inv_constantCoeff`
- **Visibility**: public (simp)
- **Lines**: 74–78 (5 lines)
- **Notes**: none

---

### `theorem formalU_isUnit`
- **Type**: `IsUnit (formalU W)`
- **What**: `formalU W` is a unit in the power series ring, because its constant coefficient is 1.
- **How**: `PowerSeries.isUnit_iff_constantCoeff` reduces to `formalU_constantCoeff`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `formalU_constantCoeff`
- **Used by**: `formalW_ps_order`
- **Visibility**: public
- **Lines**: 80–83 (4 lines)
- **Notes**: none

---

### `noncomputable def formalU_inv`
- **Type**: `PowerSeries F`
- **What**: The multiplicative inverse of `formalU` in `F⟦X⟧`, constructed via `PowerSeries.invOfUnit`.
- **How**: `PowerSeries.invOfUnit (formalU W) 1`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `formalU` (this file)
- **Used by**: `formalU_mul_inv`, `formalU_inv_mul`, `formalU_inv_constantCoeff`, `formalY` (def), `formalX` (def)
- **Visibility**: public
- **Lines**: 87–88 (2 lines, term-mode def)
- **Notes**: none

---

### `@[simp] theorem formalU_mul_inv`
- **Type**: `formalU W * formalU_inv W = 1`
- **What**: Multiplication identity confirming `formalU_inv` is a right inverse.
- **How**: `PowerSeries.mul_invOfUnit` with `formalU_constantCoeff`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `formalU_constantCoeff`
- **Used by**: unused within this file (exposed as API)
- **Visibility**: public (simp)
- **Lines**: 91–93 (3 lines, term-mode proof)
- **Notes**: none

---

### `@[simp] theorem formalU_inv_mul`
- **Type**: `formalU_inv W * formalU W = 1`
- **What**: Left-inverse identity (commutativity of the inverse relation).
- **How**: `PowerSeries.invOfUnit_mul` with `formalU_constantCoeff`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `formalU_constantCoeff`
- **Used by**: `formalY_mul_formalW`, `formalX_mul_formalW`
- **Visibility**: public (simp)
- **Lines**: 96–98 (3 lines, term-mode proof)
- **Notes**: none

---

### `@[simp] theorem formalU_inv_constantCoeff`
- **Type**: `@PowerSeries.constantCoeff F _ (formalU_inv W) = 1`
- **What**: The constant coefficient of `formalU_inv` is 1, following from the `invOfUnit` formula.
- **How**: `PowerSeries.constantCoeff_invOfUnit` plus `rfl`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: none (uses `formalU_inv`, a local def)
- **Used by**: `ofPowerSeries_formalU_inv_ne_zero`, `ofPowerSeries_formalU_inv_orderTop`, `ofPowerSeries_formalU_inv_leadingCoeff`
- **Visibility**: public (simp)
- **Lines**: 101–104 (4 lines)
- **Notes**: none

---

### `noncomputable def formalY`
- **Type**: `LaurentSeries F`
- **What**: The formal Laurent series `y(t) = -t⁻³·u(t)⁻¹` for the y-coordinate in terms of the local parameter `t`.
- **How**: Direct `-(HahnSeries.single (-3 : ℤ) 1) * HahnSeries.ofPowerSeries ℤ F (formalU_inv W)`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `formalU_inv`
- **Used by**: `formalY_ne_zero`, `formalY_orderTop`, `formalY_leadingCoeff`, `formalY_mul_formalW`, `formalY_eq_div`, `formalXY_weierstrass`, `localExpand_weierstrass_eval`, `localExpand_coordHom_injective`, `localExpand_y_gen`
- **Visibility**: public
- **Lines**: 114–116 (3 lines, term-mode def)
- **Notes**: none

---

### `noncomputable def formalX`
- **Type**: `LaurentSeries F`
- **What**: The formal Laurent series `x(t) = t⁻²·u(t)⁻¹` for the x-coordinate in terms of `t`.
- **How**: Direct `HahnSeries.single (-2 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ F (formalU_inv W)`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `formalU_inv`
- **Used by**: `formalX_ne_zero`, `formalX_orderTop`, `formalX_leadingCoeff`, `formalX_mul_formalW`, `formalX_eq_div`, `formalXY_weierstrass`, `localExpand_inner` (def), `formalX_pow_orderTop`, `formalX_pow_leadingCoeff`
- **Visibility**: public
- **Lines**: 119–121 (3 lines, term-mode def)
- **Notes**: none

---

### `theorem ofPowerSeries_formalU_inv_ne_zero`
- **Type**: `(HahnSeries.ofPowerSeries ℤ F (formalU_inv W) : LaurentSeries F) ≠ 0`
- **What**: The lift of `formalU_inv` to `LaurentSeries F` is nonzero, because its coefficient at 0 equals 1.
- **How**: Extract the coefficient at 0 via `HahnSeries.ofPowerSeries_apply_coeff` and `formalU_inv_constantCoeff`, then derive contradiction with `h : ... = 0`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `formalU_inv_constantCoeff`
- **Used by**: `formalX_ne_zero`, `formalY_ne_zero`, `ofPowerSeries_formalU_inv_orderTop`, `ofPowerSeries_formalU_inv_leadingCoeff`
- **Visibility**: public
- **Lines**: 130–140 (11 lines)
- **Notes**: none

---

### `theorem formalX_ne_zero`
- **Type**: `formalX W ≠ 0`
- **What**: `formalX W` is nonzero; follows from `formalX = single(-2,1) * (nonzero)`.
- **How**: `mul_ne_zero` with `HahnSeries.single_ne_zero` and `ofPowerSeries_formalU_inv_ne_zero`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `ofPowerSeries_formalU_inv_ne_zero`
- **Used by**: `localParam_ne_zero`
- **Visibility**: public
- **Lines**: 143–147 (5 lines)
- **Notes**: none

---

### `theorem formalY_ne_zero`
- **Type**: `formalY W ≠ 0`
- **What**: `formalY W` is nonzero.
- **How**: `mul_ne_zero` with `neg_eq_zero` and `ofPowerSeries_formalU_inv_ne_zero`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `ofPowerSeries_formalU_inv_ne_zero`
- **Used by**: `localExpand_coordHom_injective`
- **Visibility**: public
- **Lines**: 149–153 (5 lines)
- **Notes**: none

---

### `theorem ofPowerSeries_formalU_inv_orderTop`
- **Type**: `(HahnSeries.ofPowerSeries ℤ F (formalU_inv W) : LaurentSeries F).orderTop = (0 : ℤ)`
- **What**: The order of the lifted `formalU_inv` is 0: the series lives in non-negative degrees (from `ofPowerSeries`) and the coefficient at 0 is 1 (from `formalU_inv_constantCoeff`).
- **How**: `orderTop_le_of_coeff_ne_zero` for upper bound; `le_orderTop_iff_forall` + `PowerSeries.coeff_coe` for lower bound; `le_antisymm`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `ofPowerSeries_formalU_inv_ne_zero`, `formalU_inv_constantCoeff`
- **Used by**: `formalX_orderTop`, `formalY_orderTop`, `ofPowerSeries_formalU_inv_leadingCoeff`
- **Visibility**: public
- **Lines**: 159–177 (19 lines)
- **Notes**: none

---

### `theorem formalX_orderTop`
- **Type**: `(formalX W).orderTop = ((-2 : ℤ) : WithTop ℤ)`
- **What**: The order of `formalX` in `LaurentSeries F` is −2.
- **How**: Unfold `formalX`, apply `orderTop_mul`, `orderTop_single`, `ofPowerSeries_formalU_inv_orderTop`, `rfl`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `ofPowerSeries_formalU_inv_orderTop`
- **Used by**: `formalX_pow_orderTop`
- **Visibility**: public
- **Lines**: 180–184 (5 lines)
- **Notes**: none

---

### `theorem formalY_orderTop`
- **Type**: `(formalY W).orderTop = ((-3 : ℤ) : WithTop ℤ)`
- **What**: The order of `formalY` in `LaurentSeries F` is −3.
- **How**: `orderTop_mul`, `orderTop_neg`, `orderTop_single`, `ofPowerSeries_formalU_inv_orderTop`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `ofPowerSeries_formalU_inv_orderTop`
- **Used by**: `localExpand_inner_mul_formalY_orderTop`
- **Visibility**: public
- **Lines**: 187–193 (7 lines)
- **Notes**: none

---

### `theorem ofPowerSeries_formalU_inv_leadingCoeff`
- **Type**: `(HahnSeries.ofPowerSeries ℤ F (formalU_inv W) : LaurentSeries F).leadingCoeff = 1`
- **What**: The leading coefficient of the lifted `formalU_inv` is 1, which amounts to `S.coeff 0 = 1`.
- **How**: `leadingCoeff_of_ne_zero`, extract `orderTop` via `ofPowerSeries_formalU_inv_orderTop`, `WithTop.coe_untop`, then `ofPowerSeries_apply_coeff` and `formalU_inv_constantCoeff`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `ofPowerSeries_formalU_inv_ne_zero`, `ofPowerSeries_formalU_inv_orderTop`, `formalU_inv_constantCoeff`
- **Used by**: `formalX_leadingCoeff`, `formalY_leadingCoeff`
- **Visibility**: public
- **Lines**: 204–218 (15 lines)
- **Notes**: none

---

### `theorem formalX_leadingCoeff`
- **Type**: `(formalX W).leadingCoeff = 1`
- **What**: The leading coefficient of `formalX` is 1.
- **How**: `leadingCoeff_mul`, `leadingCoeff_of_single`, `ofPowerSeries_formalU_inv_leadingCoeff`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `ofPowerSeries_formalU_inv_leadingCoeff`
- **Used by**: `formalX_pow_leadingCoeff`
- **Visibility**: public
- **Lines**: 221–224 (4 lines)
- **Notes**: none

---

### `theorem formalY_leadingCoeff`
- **Type**: `(formalY W).leadingCoeff = -1`
- **What**: The leading coefficient of `formalY` is −1.
- **How**: `leadingCoeff_mul`, `leadingCoeff_neg`, `leadingCoeff_of_single`, `ofPowerSeries_formalU_inv_leadingCoeff`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `ofPowerSeries_formalU_inv_leadingCoeff`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 227–230 (4 lines)
- **Notes**: Potentially dead code within this file; may be used by `IsogenyLocalExpansion.lean` or similar downstream files.

---

### `theorem formalW_ne_zero`
- **Type**: `formalW W ≠ 0`
- **What**: The formal group series `formalW` is nonzero, because its coefficient at index 3 is 1.
- **How**: Contradiction: if `formalW = 0` then `coeff 3 = 0`, but `formalW_coeff_three` gives `coeff 3 = 1`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `formalW_coeff_three` (FormalGroup.lean)
- **Used by**: `lifted_formalW_ne_zero`
- **Visibility**: public
- **Lines**: 246–254 (9 lines)
- **Notes**: none

---

### `theorem lifted_formalW_ne_zero`
- **Type**: `HahnSeries.ofPowerSeries ℤ F (formalW W) ≠ 0`
- **What**: The lift of `formalW` to `LaurentSeries F` is nonzero.
- **How**: `HahnSeries.ofPowerSeries_injective` transports the contradiction to `formalW_ne_zero`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `formalW_ne_zero`
- **Used by**: `formalY_mul_formalW`, `formalX_mul_formalW`, `formalY_eq_div`, `formalX_eq_div`, `formalXY_weierstrass`, `localExpand_localParam`
- **Visibility**: public
- **Lines**: 257–261 (5 lines)
- **Notes**: none

---

### `theorem formalW_eq_X3_mul_U`
- **Type**: `formalW W = PowerSeries.X ^ 3 * formalU W`
- **What**: The factorization of `formalW` as `X³ · u(z)`, proved by checking coefficients.
- **How**: `ext n`; for `n < 3` use `formalW_coeff_zero/one/two` and `coeff_X_pow_mul'`; for `n = m+3` use `coeff_X_pow_mul` and unfold `formalU`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `formalW_coeff_zero`, `formalW_coeff_one`, `formalW_coeff_two`, `formalW_coeff_three` (all FormalGroup.lean); `formalU` (this file)
- **Used by**: `formalW_ps_order`, `formalY_mul_formalW`, `formalX_mul_formalW`
- **Visibility**: public
- **Lines**: 264–287 (24 lines)
- **Notes**: none

---

### `theorem formalW_ps_order`
- **Type**: `(formalW W).order = 3`
- **What**: The `PowerSeries.order` of `formalW` is 3 (its lowest nonzero coefficient index).
- **How**: `formalW_eq_X3_mul_U`, `order_mul`, `order_X_pow`, `order_zero_of_unit` (with `formalU_isUnit`).
- **Hypotheses**: same as `formalU`
- **Uses from project**: `formalW_eq_X3_mul_U`, `formalU_isUnit`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 290–293 (4 lines)
- **Notes**: Unused within this file; may be API for other files.

---

### `private theorem hC_single'`
- **Type**: `∀ (a : F) (n : ℤ), (HahnSeries.C a : LaurentSeries F) * HahnSeries.single n 1 = HahnSeries.single n a`
- **What**: Helper: `C a · single(n,1) = single(n,a)`.
- **How**: Rewrite `C a = single 0 a`, apply `single_mul_single`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: none
- **Used by**: unused in this file (private, not referenced anywhere)
- **Visibility**: private
- **Lines**: 297–301 (5 lines)
- **Notes**: Appears to be dead code — never called in the file. Possibly left from an earlier proof attempt.

---

### `private theorem single_one_pow'`
- **Type**: `∀ (k : ℕ), (HahnSeries.single (1 : ℤ) (1 : F)) ^ k = HahnSeries.single (k : ℤ) (1 : F)`
- **What**: Helper: powers of `single(1,1)` equal `single(k,1)`.
- **How**: `HahnSeries.single_pow`, `one_pow`, `nsmul_eq_mul`, `mul_one`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: none
- **Used by**: unused in this file (private, not referenced anywhere)
- **Visibility**: private
- **Lines**: 305–307 (3 lines)
- **Notes**: Dead code — never called in the file. Likely from an earlier proof approach.

---

### `private theorem formalW_recurrence_lift`
- **Type**: Equation: `HahnSeries.ofPowerSeries ℤ F (formalW W) = z³ + C a₁·z·w + C a₂·z²·w + C a₃·w² + C a₄·z·w² + C a₆·w³` (where `z = single(1,1)`, `w = ofPowerSeries(formalW)`)
- **What**: The Silverman IV.1.1 recurrence for `formalW`, lifted to `LaurentSeries F`.
- **How**: Apply `congrArg (HahnSeries.ofPowerSeries ℤ F)` to `formalW_recurrence`, then `simp` with `ofPowerSeries_C`, `ofPowerSeries_X`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `formalW_recurrence` (FormalGroup.lean)
- **Used by**: `formalXY_weierstrass`
- **Visibility**: private
- **Lines**: 312–328 (17 lines)
- **Notes**: none

---

### `private theorem formalY_mul_formalW`
- **Type**: `formalY W * HahnSeries.ofPowerSeries ℤ F (formalW W) = -1`
- **What**: The product `y(t) · w(t) = -1` as formal series, implementing the relation `y = -1/w`.
- **How**: Expand using `formalW_eq_X3_mul_U`; cancel `single(-3,1)·single(3,1) = 1` and `u_inv·u = 1` (via `formalU_inv_mul`); conclude by `ring`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `formalW_eq_X3_mul_U`, `formalU_inv_mul`
- **Used by**: `formalY_eq_div`
- **Visibility**: private
- **Lines**: 331–348 (18 lines)
- **Notes**: none

---

### `private theorem formalX_mul_formalW`
- **Type**: `formalX W * HahnSeries.ofPowerSeries ℤ F (formalW W) = HahnSeries.single (1 : ℤ) (1 : F)`
- **What**: The product `x(t) · w(t) = t`, implementing `x = t/w`.
- **How**: Same pattern as `formalY_mul_formalW`: expand, cancel `single(-2,1)·single(3,1) = single(1,1)` and `u_inv·u = 1`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `formalW_eq_X3_mul_U`, `formalU_inv_mul`
- **Used by**: `formalX_eq_div`
- **Visibility**: private
- **Lines**: 351–370 (20 lines)
- **Notes**: none

---

### `theorem formalY_eq_div`
- **Type**: `formalY W = -1 / HahnSeries.ofPowerSeries ℤ F (formalW W)`
- **What**: Expresses `formalY` as a division identity, i.e. `y(t) = -1/w(t)`.
- **How**: `eq_div_iff (lifted_formalW_ne_zero W)` reduces to `formalY_mul_formalW`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `lifted_formalW_ne_zero`, `formalY_mul_formalW`
- **Used by**: `formalXY_weierstrass`, `localExpand_localParam`
- **Visibility**: public
- **Lines**: 373–376 (4 lines)
- **Notes**: none

---

### `theorem formalX_eq_div`
- **Type**: `formalX W = HahnSeries.single (1 : ℤ) 1 / HahnSeries.ofPowerSeries ℤ F (formalW W)`
- **What**: Expresses `formalX` as a division identity, i.e. `x(t) = t/w(t)`.
- **How**: `eq_div_iff (lifted_formalW_ne_zero W)` reduces to `formalX_mul_formalW`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `lifted_formalW_ne_zero`, `formalX_mul_formalW`
- **Used by**: `formalXY_weierstrass`, `localExpand_localParam`
- **Visibility**: public
- **Lines**: 379–383 (5 lines)
- **Notes**: none

---

### `theorem formalXY_weierstrass`
- **Type**: `(formalY W)² + C a₁ · formalX W · formalY W + C a₃ · formalY W - (formalX W)³ - C a₂ · (formalX W)² - C a₄ · formalX W - C a₆ = 0`
- **What**: `(formalX W, formalY W)` satisfies the Weierstrass equation of `W` over `LaurentSeries F`.
- **How**: Substitute `x = z/w`, `y = -1/w` via `formalX_eq_div`, `formalY_eq_div`; clear denominators with `field_simp`; the residual algebraic identity equals `formalW_recurrence_lift` up to rearrangement, closed by `linear_combination`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `formalX_eq_div`, `formalY_eq_div`, `lifted_formalW_ne_zero`, `formalW_recurrence_lift`
- **Used by**: `localExpand_weierstrass_eval`
- **Visibility**: public
- **Lines**: 391–421 (31 lines)
- **Notes**: Proof is just over 30 lines. The key insight is that the Weierstrass equation is identical to the recurrence after clearing denominators — no independent calculation required.

---

### `theorem y_gen_ne_zero`
- **Type**: `y_gen W ≠ 0`
- **What**: The generator `y_gen` of the function field `K(E)` is nonzero.
- **How**: The element `y_gen = algebraMap R KE (AdjoinRoot.root W.polynomial)`. Its preimage in `R` is nonzero by `AdjoinRoot.mk_ne_zero_of_natDegree_lt` (since `Polynomial.X` has natDegree 1 < 2 = `natDegree_polynomial`), and `algebraMap R KE` is injective by `IsFractionRing.injective`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `y_gen` (Basic.lean or FunctionField), `Affine.monic_polynomial`, `Affine.natDegree_polynomial`
- **Used by**: `localParam_ne_zero`, `x_gen_ne_zero` (uses `y_gen_ne_zero` only for the second component)
- **Visibility**: public
- **Lines**: 442–460 (19 lines)
- **Notes**: none

---

### `noncomputable def localParam`
- **Type**: `W.toAffine.FunctionField` (i.e. `KE`)
- **What**: The local parameter `t = -x_gen / y_gen` at the identity O of the elliptic curve.
- **How**: `-(x_gen W) / y_gen W`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `x_gen`, `y_gen` (project's function-field generators)
- **Used by**: `localParam_ne_zero`, `localExpand_localParam`
- **Visibility**: public
- **Lines**: 464–465 (2 lines, term-mode def)
- **Notes**: none

---

### `theorem x_gen_ne_zero`
- **Type**: `x_gen W ≠ 0`
- **What**: The generator `x_gen` of the function field is nonzero.
- **How**: Same argument as `y_gen_ne_zero`: `algebraMap (Polynomial F) R (Polynomial.X)` is nonzero by `AdjoinRoot.mk_ne_zero_of_natDegree_lt` (natDegree 0 < 2), and `IsFractionRing.injective` propagates.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `x_gen`, `Affine.monic_polynomial`, `Affine.natDegree_polynomial`
- **Used by**: `localParam_ne_zero`
- **Visibility**: public
- **Lines**: 472–490 (19 lines)
- **Notes**: none

---

### `theorem localParam_ne_zero`
- **Type**: `localParam W ≠ 0`
- **What**: The local parameter `t = -x/y` is nonzero.
- **How**: `div_eq_zero_iff`, `neg_eq_zero`, `x_gen_ne_zero`, `y_gen_ne_zero`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `localParam`, `x_gen_ne_zero`, `y_gen_ne_zero`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 493–496 (4 lines)
- **Notes**: Unused within this file; likely API for downstream files.

---

### `noncomputable def localExpand_inner`
- **Type**: `Polynomial F →+* LaurentSeries F`
- **What**: The polynomial evaluation ring hom `F[X] → LaurentSeries F` sending `X ↦ formalX W`.
- **How**: `Polynomial.eval₂RingHom (algebraMap F (LaurentSeries F)) (formalX W)`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `formalX` (this file)
- **Used by**: `localExpand_inner_X`, `localExpand_inner_C`, `localExpand_weierstrass_eval`, `localExpand_coordHom` (def), `localExpand_inner_orderTop_eq`, `localExpand_inner_ne_zero_of_ne_zero`, `localExpand_inner_leadingCoeff`, `localExpand_inner_mul_formalY_orderTop`, `localExpand_coordHom_injective`, `localExpand_x_gen`, `localExpand_algebraMap`, `localExpand_algebraMap_polynomial`
- **Visibility**: public
- **Lines**: 514–515 (2 lines, term-mode def)
- **Notes**: Key internal building block; referenced in 12+ places in the file.

---

### `@[simp] theorem localExpand_inner_X`
- **Type**: `localExpand_inner W Polynomial.X = formalX W`
- **What**: The inner hom sends `X` to `formalX W`.
- **How**: `simp [localExpand_inner]`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `localExpand_inner`
- **Used by**: `localExpand_inner_orderTop_eq`, `localExpand_inner_leadingCoeff` (both via `map_pow` + `localExpand_inner_X` simp-step)
- **Visibility**: public (simp)
- **Lines**: 518–520 (3 lines)
- **Notes**: none

---

### `@[simp] theorem localExpand_inner_C`
- **Type**: `∀ (a : F), localExpand_inner W (Polynomial.C a) = algebraMap F (LaurentSeries F) a`
- **What**: The inner hom sends constants to their image under `algebraMap`.
- **How**: `simp [localExpand_inner]`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `localExpand_inner`
- **Used by**: `localExpand_inner_orderTop_eq`, `localExpand_inner_leadingCoeff`
- **Visibility**: public (simp)
- **Lines**: 523–525 (3 lines)
- **Notes**: none

---

### `private theorem localExpand_weierstrass_eval`
- **Type**: `Polynomial.eval₂ (localExpand_inner W) (formalY W) W.toAffine.polynomial = 0`
- **What**: The Weierstrass polynomial evaluates to 0 when `X ↦ formalX W`, `Y ↦ formalY W`, confirming the lift condition for `AdjoinRoot.lift`.
- **How**: `eval₂_eval₂RingHom_apply`, `Affine.map_polynomial`, `Affine.evalEval_polynomial`; then `linear_combination formalXY_weierstrass W`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `formalXY_weierstrass`, `localExpand_inner`
- **Used by**: `localExpand_coordHom` (def)
- **Visibility**: private
- **Lines**: 529–545 (17 lines)
- **Notes**: none

---

### `private noncomputable def localExpand_coordHom`
- **Type**: `W.toAffine.CoordinateRing →+* LaurentSeries F`
- **What**: The ring hom from the coordinate ring `R = F[X][Y]/(W)` to `LaurentSeries F`, built by lifting the inner hom via `AdjoinRoot.lift`.
- **How**: `AdjoinRoot.lift (localExpand_inner W) (formalY W) (localExpand_weierstrass_eval W)`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `localExpand_inner`, `localExpand_weierstrass_eval`, `formalY`
- **Used by**: `localExpand_coordHom_root`, `localExpand_coordHom_injective`, `localExpand` (def), `localExpand_x_gen`, `localExpand_algebraMap`, `localExpand_algebraMap_polynomial`
- **Visibility**: private
- **Lines**: 548–550 (3 lines, term-mode def)
- **Notes**: none

---

### `@[simp] private theorem localExpand_coordHom_root`
- **Type**: `localExpand_coordHom W (AdjoinRoot.root W.toAffine.polynomial) = formalY W`
- **What**: The coordinate ring lift sends the root (= `y_gen` in `R`) to `formalY W`.
- **How**: `simp [localExpand_coordHom, AdjoinRoot.lift_root]`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `localExpand_coordHom`, `formalY`
- **Used by**: `localExpand_coordHom_injective`, `localExpand_y_gen`
- **Visibility**: private (simp)
- **Lines**: 553–555 (3 lines)
- **Notes**: none

---

### `theorem formalX_pow_orderTop`
- **Type**: `∀ (n : ℕ), ((formalX W) ^ n).orderTop = ((-2 * n : ℤ) : WithTop ℤ)`
- **What**: The order of the n-th power of `formalX` is `−2n`.
- **How**: Induction on `n`; base `orderTop_one = 0`; step uses `orderTop_mul`, inductive hypothesis, and `formalX_orderTop`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `formalX_orderTop`
- **Used by**: `localExpand_inner_orderTop_eq`, `localExpand_inner_leadingCoeff`
- **Visibility**: public
- **Lines**: 558–571 (14 lines)
- **Notes**: none

---

### `theorem formalX_pow_leadingCoeff`
- **Type**: `∀ (n : ℕ), ((formalX W) ^ n).leadingCoeff = 1`
- **What**: The leading coefficient of `formalX^n` is 1, by induction.
- **How**: Induction; base `leadingCoeff_one`; step uses `leadingCoeff_mul`, inductive hypothesis, `formalX_leadingCoeff`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `formalX_leadingCoeff`
- **Used by**: `localExpand_inner_leadingCoeff`
- **Visibility**: public
- **Lines**: 574–581 (8 lines)
- **Notes**: none

---

### `theorem localExpand_inner_orderTop_eq`
- **Type**: `{p : Polynomial F} → (hp : p ≠ 0) → (localExpand_inner W p).orderTop = ((-2 * p.natDegree : ℤ) : WithTop ℤ)`
- **What**: For any nonzero polynomial `p`, the image under the inner hom has order `−2 · deg(p)`.
- **How**: Strong induction on `natDegree`. Base: `p = C a`, image is `single(0,a)`, order 0. Step: decompose `p = eraseLead p + C(lc)·X^n`; leading term maps to `single(0,lc)·formalX^n` with order `−2n`; `eraseLead` maps to something with strictly larger order (inductive hypothesis + `natDegree_eraseLead_le`); conclude by `orderTop_add_eq_right`.
- **Hypotheses**: `p : Polynomial F`, `p ≠ 0`; plus standard curve hypotheses
- **Uses from project**: `localExpand_inner_C`, `localExpand_inner_X`, `formalX_pow_orderTop`
- **Used by**: `localExpand_inner_ne_zero_of_ne_zero`, `localExpand_inner_leadingCoeff`, `localExpand_inner_mul_formalY_orderTop`, `localExpand_coordHom_injective`, `orderTop_localExpand_algebraMap_polynomial`
- **Visibility**: public
- **Lines**: 591–634 (44 lines)
- **Notes**: Proof >30 lines. Uses `Nat.strong_induction_on` + `Polynomial.eraseLead_add_C_mul_X_pow` decomposition.

---

### `theorem localExpand_inner_ne_zero_of_ne_zero`
- **Type**: `{p : Polynomial F} → (hp : p ≠ 0) → localExpand_inner W p ≠ 0`
- **What**: The inner hom sends nonzero polynomials to nonzero Laurent series.
- **How**: If `localExpand_inner W p = 0` then `orderTop = ⊤` but `localExpand_inner_orderTop_eq` gives a finite value; contradiction.
- **Hypotheses**: `p ≠ 0`
- **Uses from project**: `localExpand_inner_orderTop_eq`
- **Used by**: `localExpand_coordHom_injective`
- **Visibility**: public
- **Lines**: 637–642 (6 lines)
- **Notes**: none

---

### `theorem localExpand_inner_leadingCoeff`
- **Type**: `{p : Polynomial F} → (hp : p ≠ 0) → (localExpand_inner W p).leadingCoeff = p.leadingCoeff`
- **What**: The inner hom preserves leading coefficients.
- **How**: Same strong induction as `localExpand_inner_orderTop_eq`; leading coefficient of the leading term is `lc·1 = lc`; `eraseLead` contributes with strictly larger order, so `leadingCoeff_add_eq_right` gives the result.
- **Hypotheses**: `p ≠ 0`
- **Uses from project**: `localExpand_inner_C`, `localExpand_inner_X`, `formalX_pow_orderTop`, `formalX_pow_leadingCoeff`, `localExpand_inner_orderTop_eq`
- **Used by**: unused in this file (public API for downstream)
- **Visibility**: public
- **Lines**: 653–700 (48 lines)
- **Notes**: Proof >30 lines. Structurally identical to `localExpand_inner_orderTop_eq`; could potentially be combined. Unused within this file.

---

### `theorem localExpand_inner_mul_formalY_orderTop`
- **Type**: `{q : Polynomial F} → (hq : q ≠ 0) → ((localExpand_inner W q) * formalY W).orderTop = ((-2 * q.natDegree - 3 : ℤ) : WithTop ℤ)`
- **What**: For nonzero `q`, the order of `(eval_inner q) · formalY` is `−2·deg(q) − 3` (always odd and negative).
- **How**: `orderTop_mul`, `localExpand_inner_orderTop_eq`, `formalY_orderTop`.
- **Hypotheses**: `q ≠ 0`
- **Uses from project**: `localExpand_inner_orderTop_eq`, `formalY_orderTop`
- **Used by**: `localExpand_coordHom_injective`
- **Visibility**: public
- **Lines**: 704–710 (7 lines)
- **Notes**: none

---

### `private theorem localExpand_coordHom_injective`
- **Type**: `Function.Injective (localExpand_coordHom W)`
- **What**: The coordinate ring hom is injective; this is used to invoke `IsFractionRing.lift` for the fraction field extension.
- **How**: Write any `r ∈ R` as `p · 1 + q · (mk Y)` via `Affine.CoordinateRing.exists_smul_basis_eq`; the image is `eval_inner(p) + eval_inner(q)·formalY`. A parity argument shows the image is 0 iff both `p = 0` and `q = 0`: `eval_inner(p)` has even order `−2·deg(p)` while `eval_inner(q)·formalY` has odd order `−2·deg(q)−3`; different parities force different orders, so the sum is nonzero when either summand is nonzero.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `Affine.CoordinateRing.exists_smul_basis_eq`, `Affine.CoordinateRing.smul`, `localExpand_coordHom`, `localExpand_coordHom_root`, `localExpand_inner`, `localExpand_inner_orderTop_eq`, `localExpand_inner_ne_zero_of_ne_zero`, `localExpand_inner_mul_formalY_orderTop`, `formalY_ne_zero`
- **Used by**: `localExpand` (def)
- **Visibility**: private
- **Lines**: 724–785 (62 lines)
- **Notes**: Proof >30 lines (62 lines). The parity argument is the core mathematical content. Uses `HahnSeries.orderTop_add_eq_left/right`.

---

### `noncomputable def localExpand`
- **Type**: `W.toAffine.FunctionField →+* LaurentSeries F`
- **What**: The local expansion ring homomorphism `K(E) → LaurentSeries F`, sending `x_gen ↦ formalX W` and `y_gen ↦ formalY W`.
- **How**: `IsFractionRing.lift (localExpand_coordHom_injective W)` — the universal property of the fraction field, using injectivity of the coordinate ring hom.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `localExpand_coordHom_injective`
- **Used by**: `localExpand_x_gen`, `localExpand_y_gen`, `localExpand_algebraMap`, `localExpand_algebraMap_polynomial`, `orderTop_localExpand_algebraMap_polynomial`, `localExpand_localParam`
- **Visibility**: public
- **Lines**: 798–799 (2 lines, term-mode def)
- **Notes**: The main deliverable of the file.

---

### `@[simp] theorem localExpand_x_gen`
- **Type**: `localExpand W (x_gen W) = formalX W`
- **What**: The local expansion sends `x_gen` to `formalX W`.
- **How**: `IsFractionRing.lift_algebraMap`; reduce to `localExpand_coordHom (AdjoinRoot.of _ X) = formalX`; `simp [localExpand_coordHom, AdjoinRoot.lift_of, localExpand_inner]`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `localExpand`, `localExpand_coordHom`, `localExpand_inner`
- **Used by**: `localExpand_localParam`
- **Visibility**: public (simp)
- **Lines**: 802–808 (7 lines)
- **Notes**: none

---

### `@[simp] theorem localExpand_y_gen`
- **Type**: `localExpand W (y_gen W) = formalY W`
- **What**: The local expansion sends `y_gen` to `formalY W`.
- **How**: `IsFractionRing.lift_algebraMap`, `localExpand_coordHom_root`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `localExpand`, `localExpand_coordHom_root`
- **Used by**: `localExpand_localParam`
- **Visibility**: public (simp)
- **Lines**: 811–813 (3 lines)
- **Notes**: none

---

### `theorem localExpand_algebraMap`
- **Type**: `∀ (a : F), localExpand W (algebraMap F KE a) = HahnSeries.ofPowerSeries ℤ F (PowerSeries.C a)`
- **What**: The local expansion acts on constants (field elements embedded in `K(E)`) as `C a ↦ ofPowerSeries(C a)`.
- **How**: Factor `algebraMap F KE` through `CoordinateRing` and `Polynomial F`; reduce via `IsFractionRing.lift_algebraMap`, `AdjoinRoot.lift_of`; `simp` with `localExpand_inner`, `LaurentSeries.algebraMap_apply`, `ofPowerSeries_C`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `localExpand`, `localExpand_coordHom`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 816–828 (13 lines)
- **Notes**: Unused within this file; public API for downstream consumers.

---

### `theorem localExpand_algebraMap_polynomial`
- **Type**: `∀ (p : Polynomial F), localExpand W (algebraMap (Polynomial F) KE p) = localExpand_inner W p`
- **What**: The local expansion of a polynomial element of `K(E)` equals the inner polynomial evaluation.
- **How**: Factor through `CoordinateRing` via `IsScalarTower.algebraMap_apply`; reduce via `IsFractionRing.lift_algebraMap`, `AdjoinRoot.lift_of`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `localExpand`, `localExpand_inner`, `localExpand_coordHom`
- **Used by**: `orderTop_localExpand_algebraMap_polynomial`
- **Visibility**: public
- **Lines**: 836–842 (7 lines)
- **Notes**: none

---

### `theorem orderTop_localExpand_algebraMap_polynomial`
- **Type**: `{p : Polynomial F} → (hp : p ≠ 0) → (localExpand W (algebraMap (Polynomial F) KE p)).orderTop = ((-2 * p.natDegree : ℤ) : WithTop ℤ)`
- **What**: Transports `localExpand_inner_orderTop_eq` through `localExpand_algebraMap_polynomial`.
- **How**: One-line rewrite via `localExpand_algebraMap_polynomial` + `localExpand_inner_orderTop_eq`.
- **Hypotheses**: `p ≠ 0`
- **Uses from project**: `localExpand_algebraMap_polynomial`, `localExpand_inner_orderTop_eq`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 847–851 (5 lines)
- **Notes**: Unused within this file; public API for downstream.

---

### `theorem localExpand_localParam`
- **Type**: `localExpand W (localParam W) = HahnSeries.single (1 : ℤ) 1`
- **What**: The key compatibility: the local parameter `t = -x/y` expands to the formal variable `t = single(1,1)` in `LaurentSeries F`.
- **How**: Apply `localExpand_x_gen`, `localExpand_y_gen`; then expand `formalX_eq_div`, `formalY_eq_div`; `field_simp` with `lifted_formalW_ne_zero`.
- **Hypotheses**: same as `formalU`
- **Uses from project**: `localParam`, `localExpand_x_gen`, `localExpand_y_gen`, `formalX_eq_div`, `formalY_eq_div`, `lifted_formalW_ne_zero`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 855–867 (13 lines)
- **Notes**: Key API theorem connecting the algebraic local parameter to the formal variable; likely used by `IsogenyLocalExpansion.lean`. Unused within this file.

---

## Cross-reference summary

### Key API (used by 3+ other declarations in this file)

| Declaration | Users within file |
|---|---|
| `ofPowerSeries_formalU_inv_ne_zero` | `formalX_ne_zero`, `formalY_ne_zero`, `ofPowerSeries_formalU_inv_orderTop`, `ofPowerSeries_formalU_inv_leadingCoeff` (4) |
| `formalU_inv_constantCoeff` | `ofPowerSeries_formalU_inv_ne_zero`, `ofPowerSeries_formalU_inv_orderTop`, `ofPowerSeries_formalU_inv_leadingCoeff` (3) |
| `ofPowerSeries_formalU_inv_orderTop` | `formalX_orderTop`, `formalY_orderTop`, `ofPowerSeries_formalU_inv_leadingCoeff` (3) |
| `lifted_formalW_ne_zero` | `formalY_eq_div`, `formalX_eq_div`, `formalXY_weierstrass`, `localExpand_localParam` (4) |
| `formalW_eq_X3_mul_U` | `formalW_ps_order`, `formalY_mul_formalW`, `formalX_mul_formalW` (3) |
| `localExpand_inner` | `localExpand_inner_X`, `localExpand_inner_C`, and 10+ other declarations |
| `localExpand_inner_orderTop_eq` | `localExpand_inner_ne_zero_of_ne_zero`, `localExpand_inner_leadingCoeff`, `localExpand_inner_mul_formalY_orderTop`, `localExpand_coordHom_injective`, `orderTop_localExpand_algebraMap_polynomial` (5) |
| `localExpand_coordHom` | `localExpand_coordHom_root`, `localExpand_coordHom_injective`, `localExpand_x_gen`, `localExpand_algebraMap`, `localExpand_algebraMap_polynomial` (5) |

### Unused within this file (dead-code candidates)

- `hC_single'` (private, never called)
- `single_one_pow'` (private, never called)
- `formalW_ps_order` (public, no internal callers)
- `formalY_leadingCoeff` (public, no internal callers)
- `localExpand_inner_leadingCoeff` (public, no internal callers)
- `localParam_ne_zero` (public, no internal callers)
- `localExpand_algebraMap` (public, no internal callers)
- `orderTop_localExpand_algebraMap_polynomial` (public, no internal callers)
- `localExpand_localParam` (public, no internal callers — but likely the primary output used by Phase 2)

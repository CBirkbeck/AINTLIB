# T-III-4-020b: Final closure via `zsmul_genericPoint_eq`

**Status**: OPEN (follow-up after T-III-4-020b-2 closed 2026-04-20)
**Estimated**: ~200 lines, single session

## Context

T-III-4-020b-2 (`zsmul_genericPoint_eq`) closed via the Jacobian approach.
This unblocks the full composition law via `mulByInt_comp_eq_mul_of_generator_witness`
(already in `MulByIntComp.lean`). All that remains is discharging the two
witnesses:

```
h_x : (mulByInt W n).pullback ((mulByInt W m).pullback (x_gen)) = mulByInt_x W (m·n)
h_y : (mulByInt W n).pullback ((mulByInt W m).pullback (y_gen)) = mulByInt_y W (m·n)
```

## Proof strategy

### Step 1: Generalize `zsmul_genericPoint_eq` to arbitrary curve points

Add to `HasseWeil/EC/GenericPointZsmul.lean`:

```lean
theorem zsmul_affine_point_eq (m : ℤ) {x₀ y₀ : KE}
    (h_ns : (W_KE W).toAffine.Nonsingular x₀ y₀)
    (h_ψ_ne : ((W_KE W).ψ m).evalEval x₀ y₀ ≠ 0) :
    ∃ h_ns' : (W_KE W).toAffine.Nonsingular
        (((W_KE W).φ m).evalEval x₀ y₀ / ((W_KE W).ψ m).evalEval x₀ y₀ ^ 2)
        (((W_KE W).ω m).evalEval x₀ y₀ / ((W_KE W).ψ m).evalEval x₀ y₀ ^ 3),
      m • Affine.Point.some x₀ y₀ h_ns =
        Affine.Point.some _ _ h_ns'
```

Proof: same pattern as `zsmul_genericPoint_eq` but with general `(x₀, y₀)`.

### Step 2: Derive nonvanishing of ψ at `(mulByInt_x W n, mulByInt_y W n)`

```lean
lemma ψ_m_evalEval_mulByInt_ne_zero (m n : ℤ) (hn : n ≠ 0) (hmn : m * n ≠ 0) :
    ((W_KE W).ψ m).evalEval (mulByInt_x W n) (mulByInt_y W n) ≠ 0
```

From `(m*n) • gen ≠ 0` (via `zsmul_genericPoint_eq (m*n) hmn` giving `.some _ _ _`
which is not 0) + Jacobian Z ≠ 0 fact.

### Step 3: Translate bivariate evalEval to univariate eval₂

```lean
lemma evalEval_φ_on_curve_eq_eval₂_Φ (m : ℤ) {x y : KE}
    (h_eq : (W_KE W).toAffine.Equation x y) :
    ((W_KE W).φ m).evalEval x y =
      Polynomial.eval₂ (algebraMap F KE) x (W.Φ m)
```

Via `Affine.CoordinateRing.mk_φ` (mathlib): `mk(φ_m) = mk(C(Φ_m))` in CoordinateRing.
At any point on the curve, the evaluation factors through the quotient, so
equal elements in CoordinateRing give equal values.

Similarly for ψ² → ΨSq (via `mk_Ψ_sq`).

### Step 4: Apply at `(mulByInt_x W n, mulByInt_y W n)` + combine with `mulByInt_pullback_mulByInt_x`

```lean
theorem mulByInt_pullback_mulByInt_x_eq (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m * n ≠ 0) :
    (mulByInt W.toAffine n).pullback (mulByInt_x W m) = mulByInt_x W (m * n) := by
  rw [mulByInt_pullback_mulByInt_x W n m hn]
  -- Now LHS = eval₂ at mulByInt_x W n of W.Φ m / W.ΨSq m
  -- Show this = mulByInt_x W (m*n) using zsmul_affine_point_eq + Step 3
  ...
```

### Step 5: Assemble h_x and h_y, conclude `mulByInt_comp_eq_mul`

```lean
theorem mulByInt_comp_eq_mul (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m * n ≠ 0) :
    (mulByInt W.toAffine m).comp (mulByInt W.toAffine n) =
      mulByInt W.toAffine (m * n) :=
  mulByInt_comp_eq_mul_of_generator_witness W m n hm hn hmn
    (h_x := ...)  -- by mulByInt_pullback_mulByInt_x_eq + mulByInt_pullback_x
    (h_y := ...)  -- analogous
```

## Line budget

| Piece | Lines |
|-------|------|
| `zsmul_affine_point_eq` (generalization) | ~50 |
| `ψ_m_evalEval_mulByInt_ne_zero` | ~20 |
| `evalEval_on_curve_eq_eval₂` (φ + ψ²) | ~40 |
| `mulByInt_pullback_mulByInt_x_eq` + y-version | ~50 |
| `mulByInt_comp_eq_mul` | ~10 |
| **Total** | **~170 lines** |

## Impact

Closes T-III-4-020b (Silverman III.4.2). Unblocks:
- T-III-6-006 (`[m]̂ = [m]`) via `isogDual_mulByInt_of_comp`
- T-III-6-003, T-III-6-007, T-III-6-008 (Hasse bound chain)
- Dual isogeny composition identities

## References

* `mulByInt_comp_eq_mul_of_generator_witness` (in `MulByIntComp.lean:134`)
* `mulByInt_pullback_mulByInt_x` (in `MulByIntBaseCase.lean:254`)
* `zsmul_genericPoint_eq` (in `GenericPointZsmul.lean` — closed 2026-04-20)
* `zsmul_eq_smulEval` (mathlib `Auxiliary/DivisionPolynomial.lean:678`)

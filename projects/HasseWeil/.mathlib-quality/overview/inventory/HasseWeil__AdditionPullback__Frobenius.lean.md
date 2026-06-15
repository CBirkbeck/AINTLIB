# Inventory: ./HasseWeil/AdditionPullback/Frobenius.lean

**File**: `HasseWeil/AdditionPullback/Frobenius.lean`  
**Lines**: 4564  
**Namespace**: `HasseWeil`  
**Imports**: `HasseWeil.AdditionPullback`, `HasseWeil.Curves.WithTopArith`, `HasseWeil.Frobenius`, `HasseWeil.EC.GenericPointZsmul`, `HasseWeil.EC.MulByIntBaseCase`

---

## Overview

This file computes `ord_∞` of addition-pullback coordinates for the Frobenius isogeny `π = frobeniusIsog W` and its negation `−π = negFrobeniusIsog W`, then bootstraps axiom-clean closures of "Sorry 1" (the pole bound `addPullback_x ∉ K`) for these isogenies and for the general pencil family `rπ − s`. It also develops σ-invariance machinery and the D3b–D4 tower that constructs the genuine `rπ − s` isogeny unconditionally.

---

## Declarations

### `theorem x_gen_ne_frobeniusIsog_pullback_x_gen`
- **Type**: `x_gen W ≠ (frobeniusIsog W).pullback (x_gen W)`
- **What**: The x-coordinate generator and its Frobenius pullback are distinct elements of K(E).
- **How**: Their `ord_∞` values are `-2` and `-2q` respectively; injectivity of `WithTop.coe` plus `q > 1` yields the contradiction.
- **Hypotheses**: `W` elliptic over finite field `K`
- **Uses from project**: `ordAtInfty_x_gen`, `ordAtInfty_frobeniusIsog_pullback_x_gen`
- **Used by**: `addSlope_frobenius_eq`, `x_gen_sub_frobeniusIsog_pullback_x_gen_ne_zero`, `AddNonInversePair_zsmul_one_frobenius_mulByInt_neg_one`, `AddNonInversePair_zsmul_frobenius_mulByInt_neg`, `negFrobeniusIsog_addNonInverse`, `x_gen_ne_negFrobeniusIsog_pullback_x_gen`, `negFrobeniusIsog_addNonInverse_for_y_ord`
- **Visibility**: public
- **Lines**: 44–55, proof 12 lines

---

### `theorem addSlope_frobenius_eq`
- **Type**: `addSlope W (frobeniusIsog W) = (y_gen W - (frobeniusIsog W).pullback (y_gen W)) / (x_gen W - (frobeniusIsog W).pullback (x_gen W))`
- **What**: Expresses the addition slope for the Frobenius isogeny as the explicit difference quotient.
- **How**: Unfolds `addSlope`, applies `Affine.slope_of_X_ne` using `x_gen_ne_frobeniusIsog_pullback_x_gen`.
- **Hypotheses**: `W` elliptic over finite field `K`
- **Uses from project**: `x_gen_ne_frobeniusIsog_pullback_x_gen`
- **Used by**: `addPullbackNumerator_frobenius_eq`
- **Visibility**: public
- **Lines**: 60–65, proof 6 lines

---

### `theorem ordAtInfty_x_gen_sub_frobeniusIsog_pullback_x_gen`
- **Type**: `(W_smooth W).ordAtInfty (x_gen W - (frobeniusIsog W).pullback (x_gen W)) = ((-2 * #K : ℤ) : WithTop ℤ)`
- **What**: `ord_∞(x − π·x) = -2q`.
- **How**: Sign-flip via `ordAtInfty_neg` and `ordAtInfty_frobeniusIsog_pullback_x_gen_sub_x_gen`.
- **Hypotheses**: `W` elliptic over finite field
- **Uses from project**: `ordAtInfty_frobeniusIsog_pullback_x_gen_sub_x_gen`
- **Used by**: `x_gen_sub_frobeniusIsog_pullback_x_gen_ne_zero`, `ordAtInfty_addSlope_frobenius`, `ordAtInfty_T3_frobenius`, `ord_addPullback_x_frobenius`, `ordAtInfty_x_gen_sub_negFrobeniusIsog_pullback_x_gen`
- **Visibility**: public
- **Lines**: 69–78, proof 10 lines

---

### `theorem ordAtInfty_y_gen_sub_frobeniusIsog_pullback_y_gen`
- **Type**: `(W_smooth W).ordAtInfty (y_gen W - (frobeniusIsog W).pullback (y_gen W)) = ((-3 * #K : ℤ) : WithTop ℤ)`
- **What**: `ord_∞(y − π·y) = -3q`.
- **How**: Sign-flip via `ordAtInfty_neg` and `ordAtInfty_frobeniusIsog_pullback_y_gen_sub_y_gen`.
- **Hypotheses**: `W` elliptic over finite field
- **Uses from project**: `ordAtInfty_frobeniusIsog_pullback_y_gen_sub_y_gen`
- **Used by**: `y_gen_sub_frobeniusIsog_pullback_y_gen_ne_zero`, `ordAtInfty_addSlope_frobenius`, `ordAtInfty_T1_frobenius`, `ordAtInfty_T2_frobenius`
- **Visibility**: public
- **Lines**: 80–88, proof 9 lines

---

### `theorem x_gen_sub_frobeniusIsog_pullback_x_gen_ne_zero`
- **Type**: `x_gen W - (frobeniusIsog W).pullback (x_gen W) ≠ 0`
- **What**: The denominator `x − π·x` is nonzero.
- **How**: Contradiction from `ordAtInfty_x_gen_sub_frobeniusIsog_pullback_x_gen` giving finite ord vs `ordAtInfty_zero = ⊤`.
- **Hypotheses**: `W` elliptic over finite field
- **Uses from project**: `ordAtInfty_x_gen_sub_frobeniusIsog_pullback_x_gen`
- **Used by**: `ordAtInfty_addSlope_frobenius`, `addPullbackNumerator_frobenius_eq`, `ord_addPullback_x_frobenius`
- **Visibility**: public
- **Lines**: 91–98, proof 8 lines

---

### `theorem ordAtInfty_addSlope_frobenius`
- **Type**: `(W_smooth W).ordAtInfty (addSlope W (frobeniusIsog W)) = ((-#K : ℤ) : WithTop ℤ)`
- **What**: **Main result**: `ord_∞(L) = -q` where `L` is the addition slope.
- **How**: Applies `ordAtInfty_div_of_ord_eq` to the numerator (ord `-3q`) and denominator (ord `-2q`), yielding `-3q − (-2q) = -q`.
- **Hypotheses**: `W` elliptic over finite field
- **Uses from project**: `addSlope_frobenius_eq`, `x_gen_sub_frobeniusIsog_pullback_x_gen_ne_zero`, `ordAtInfty_y_gen_sub_frobeniusIsog_pullback_y_gen`, `ordAtInfty_x_gen_sub_frobeniusIsog_pullback_x_gen`
- **Used by**: `addSlope_frobenius_ne_zero`, `ordAtInfty_addSlope_sq_frobenius`, `ordAtInfty_a1L_minus_a2_minus_xgen_frobenius`
- **Visibility**: public
- **Lines**: 102–113, proof 12 lines

---

### `theorem addSlope_frobenius_ne_zero`
- **Type**: `addSlope W (frobeniusIsog W) ≠ 0`
- **What**: The slope `L` is nonzero.
- **How**: Finite ord (`-q`) contradicts `ordAtInfty_zero = ⊤`.
- **Hypotheses**: `W` elliptic over finite field
- **Uses from project**: `ordAtInfty_addSlope_frobenius`
- **Used by**: `ordAtInfty_addSlope_sq_frobenius`, `ordAtInfty_a1L_minus_a2_minus_xgen_frobenius`
- **Visibility**: public
- **Lines**: 116–122, proof 7 lines

---

### `theorem ordAtInfty_addSlope_sq_frobenius`
- **Type**: `(W_smooth W).ordAtInfty (addSlope W (frobeniusIsog W) ^ 2) = ((-2 * #K : ℤ) : WithTop ℤ)`
- **What**: `ord_∞(L²) = -2q`.
- **How**: `ordAtInfty_pow_of_ord_eq` applied at `ord = -q`, exponent 2.
- **Hypotheses**: `W` elliptic over finite field
- **Uses from project**: `addSlope_frobenius_ne_zero`, `ordAtInfty_addSlope_frobenius`
- **Used by**: (unused in file, downstream consumers)
- **Visibility**: public
- **Lines**: 125–132, proof 8 lines

---

### `theorem addPullback_x_ne_const_frobenius_of_pole`
- **Type**: Given `hxy : AddNonInverse`, `h_pole : ord < 0`, `hc : addPullback_x = algebraMap c`, derives `False`.
- **What**: Thin wrapper calling `addPullback_x_ne_const_of_pole`.
- **How**: Direct delegation to `addPullback_x_ne_const_of_pole`.
- **Hypotheses**: `AddNonInverse`, pole, constant-value hypothesis
- **Uses from project**: `addPullback_x_ne_const_of_pole`
- **Used by**: (unused in file — superseded path)
- **Visibility**: public
- **Lines**: 137–143, proof 1 line
- **Notes**: Documentation says this path is superseded.

---

### `theorem ordAtInfty_a1L_minus_a2_minus_xgen_frobenius`
- **Type**: `ord_∞(a₁L − a₂ − x_gen) = -q` for `q ≥ 3`, `a₁ ≠ 0`, `a₂ ≠ 0`.
- **What**: The "rest" group in the regrouped `addPullback_x` formula has order `-q`.
- **How**: Two-step strict non-archimedean: first `ord(a₁L − a₂) = -q` (since `-q < 0`), then `ord(... − x_gen) = -q` (since `-q < -2` for `q ≥ 3`), using `ord_sub_lt_concrete`.
- **Hypotheses**: `q ≥ 3`, `a₁ ≠ 0`, `a₂ ≠ 0`
- **Uses from project**: `ordAtInfty_algebraMap_F_nonzero`, `ordAtInfty_addSlope_frobenius`, `addSlope_frobenius_ne_zero`, `ordAtInfty_x_gen`
- **Used by**: `addPullback_x_pole_frobenius_of_lc_witness`
- **Visibility**: public
- **Lines**: 159–202, proof 44 lines
- **Notes**: Long proof (44 lines).

---

### `theorem addPullback_x_pole_frobenius_of_lc_witness`
- **Type**: Given `q ≥ 3`, `a₁ ≠ 0`, `a₂ ≠ 0`, and a witness `ord(L² − π·x) ≠ -q`, proves `ord(addPullback_x) ≤ -2`.
- **What**: **SUPERSEDED**: Pole bound via lc-witness case split.
- **How**: Splits on whether `ord(A) < -q` or `> -q` (strict non-arch), in both cases getting `ord(A+B) ≤ -q ≤ -2`.
- **Hypotheses**: `q ≥ 3`, `a₁ ≠ 0`, `a₂ ≠ 0`, witness
- **Uses from project**: `ordAtInfty_a1L_minus_a2_minus_xgen_frobenius`
- **Used by**: `addPullback_x_ne_const_frobenius_q_ge_3_of_witness`
- **Visibility**: public
- **Lines**: 224–280, proof 57 lines
- **Notes**: Superseded; the witness premise is false for `a₁ ≠ 0`. Long proof (57 lines).

---

### `theorem addPullback_x_ne_const_frobenius_q_ge_3_of_witness`
- **Type**: Under `q ≥ 3`, `a₁ ≠ 0`, `a₂ ≠ 0`, witness `ord(L² − π·x) ≠ -q`, `AddNonInverse`, and `hc`: False.
- **What**: Composes the superseded pole bound with `addPullback_x_ne_const_of_pole`.
- **How**: `addPullback_x_pole_frobenius_of_lc_witness` gives `ord ≤ -2 < 0`, then `addPullback_x_ne_const_frobenius_of_pole`.
- **Hypotheses**: As above
- **Uses from project**: `addPullback_x_pole_frobenius_of_lc_witness`, `addPullback_x_ne_const_frobenius_of_pole`
- **Used by**: (unused in file — superseded path)
- **Visibility**: public
- **Lines**: 284–299, proof 15 lines
- **Notes**: Superseded.

---

### `theorem y_gen_sub_frobeniusIsog_pullback_y_gen_ne_zero`
- **Type**: `y_gen W - (frobeniusIsog W).pullback (y_gen W) ≠ 0`
- **What**: The numerator `y − π·y` is nonzero.
- **How**: Finite ord contradiction.
- **Hypotheses**: `W` elliptic over finite field
- **Uses from project**: `ordAtInfty_y_gen_sub_frobeniusIsog_pullback_y_gen`
- **Used by**: `ordAtInfty_T1_frobenius`, `ordAtInfty_T2_frobenius`
- **Visibility**: public
- **Lines**: 333–341, proof 9 lines

---

### `noncomputable def addPullbackNumerator_frobenius`
- **Type**: `KE` — the element `(y − π·y)² + a₁(x − π·x)(y − π·y) − (x − π·x)²(a₂ + x + π·x)`
- **What**: The numerator obtained by clearing `(x − π·x)²` from `addPullback_x W (frobeniusIsog W)`.
- **How**: Direct definition.
- **Uses from project**: `y_gen`, `x_gen`, `frobeniusIsog`
- **Used by**: `addPullbackNumerator_frobenius_eq`, `addPullbackNumerator_frobenius_eq_reduced`, `ord_addPullback_x_frobenius`
- **Visibility**: public
- **Lines**: 349–356, definition

---

### `theorem addPullbackNumerator_frobenius_eq`
- **Type**: `addPullbackNumerator_frobenius W = (x − π·x)² · addPullback_x W (frobeniusIsog W)`
- **What**: Algebraic identity: the numerator clears the denominator.
- **How**: Uses `addSlope_frobenius_eq` (slope = `n/d`), then `field_simp; ring`.
- **Hypotheses**: `W` elliptic over finite field
- **Uses from project**: `addSlope_frobenius_eq`, `x_gen_sub_frobeniusIsog_pullback_x_gen_ne_zero`
- **Used by**: `ord_addPullback_x_frobenius`
- **Visibility**: public
- **Lines**: 364–389, proof 26 lines

---

### `theorem ordAtInfty_T1_frobenius`
- **Type**: `ord_∞((y − π·y)²) = -6q`
- **What**: `T₁` has order `-6q`.
- **How**: `ord_pow_concrete` at `ord(y − π·y) = -3q`, exponent 2.
- **Hypotheses**: `W` elliptic over finite field
- **Uses from project**: `y_gen_sub_frobeniusIsog_pullback_y_gen_ne_zero`, `ordAtInfty_y_gen_sub_frobeniusIsog_pullback_y_gen`
- **Used by**: (used indirectly via the numerator analysis)
- **Visibility**: public
- **Lines**: 394–404, proof 11 lines

---

### `theorem ordAtInfty_T2_frobenius`
- **Type**: `ord_∞(a₁ · (x − π·x) · (y − π·y)) = -5q` for `a₁ ≠ 0`
- **What**: `T₂` has order `-5q`.
- **How**: Multiplicativity of `ord_∞`: `-2q + (-3q) = -5q`.
- **Hypotheses**: `a₁ ≠ 0`
- **Uses from project**: `x_gen_sub_frobeniusIsog_pullback_x_gen_ne_zero`, `y_gen_sub_frobeniusIsog_pullback_y_gen_ne_zero`, `ordAtInfty_algebraMap_F_nonzero`, `ordAtInfty_x_gen_sub_frobeniusIsog_pullback_x_gen`, `ordAtInfty_y_gen_sub_frobeniusIsog_pullback_y_gen`
- **Used by**: (term-ord documentation)
- **Visibility**: public
- **Lines**: 408–441, proof 34 lines
- **Notes**: Long proof (34 lines).

---

### `theorem ordAtInfty_a2_plus_x_gen_plus_pi_x_frobenius`
- **Type**: `ord_∞(a₂ + x + π·x) = -2q` for `q ≥ 2`
- **What**: The sum `a₂ + x_gen + π·x` has order `-2q`.
- **How**: Case split on `a₂ = 0`; in each case `π·x` dominates via `ord_add_lt_concrete`.
- **Hypotheses**: `q ≥ 2`
- **Uses from project**: `ordAtInfty_frobeniusIsog_pullback_x_gen`, `ordAtInfty_x_gen`, `ordAtInfty_algebraMap_F_nonzero`
- **Used by**: `ordAtInfty_T3_frobenius`
- **Visibility**: public
- **Lines**: 446–492, proof 47 lines
- **Notes**: Long proof (47 lines).

---

### `theorem ordAtInfty_T3_frobenius`
- **Type**: `ord_∞((x − π·x)² · (a₂ + x + π·x)) = -6q` for `q ≥ 2`
- **What**: `T₃` has order `-6q`.
- **How**: Multiplicativity: `ord((x−π·x)²) = -4q` plus `ord(a₂+x+π·x) = -2q`.
- **Hypotheses**: `q ≥ 2`
- **Uses from project**: `x_gen_sub_frobeniusIsog_pullback_x_gen_ne_zero`, `ordAtInfty_x_gen_sub_frobeniusIsog_pullback_x_gen`, `ordAtInfty_a2_plus_x_gen_plus_pi_x_frobenius`
- **Used by**: (term-ord documentation)
- **Visibility**: public
- **Lines**: 496–530, proof 35 lines
- **Notes**: Long proof (35 lines).

---

### `noncomputable def addPullbackNumerator_reduced_frobenius`
- **Type**: `KE` — the Weierstrass-reduced 8-term form
- **What**: The expression `a₄(x+π·x) + 2a₆ − a₃(y+π·y) − 2yπ·y − a₁(xπ·y+π·xy) + x²π·x + x(π·x)² + 2a₂xπ·x`.
- **How**: Direct definition; the `x(π·x)²` term is the dominant term.
- **Uses from project**: `y_gen`, `x_gen`, `frobeniusIsog`
- **Used by**: `addPullbackNumerator_frobenius_eq_reduced`, `ordAtInfty_addPullbackNumerator_reduced_frobenius_eq`
- **Visibility**: public
- **Lines**: 558–571, definition

---

### `theorem addPullbackNumerator_frobenius_eq_reduced`
- **Type**: `addPullbackNumerator_frobenius W = addPullbackNumerator_reduced_frobenius W`
- **What**: The Weierstrass reduction identity: naive numerator equals reduced form.
- **How**: Uses Weierstrass equations for `(x_gen, y_gen)` (via `generic_equation`) and `(π·x, π·y)` (via `pullback_equation`), then `linear_combination h_y_sq + h_Y_sq`.
- **Hypotheses**: `W` elliptic over finite field
- **Uses from project**: `generic_equation`, `pullback_equation`
- **Used by**: `ord_addPullback_x_frobenius`
- **Visibility**: public
- **Lines**: 584–627, proof 44 lines
- **Notes**: Long proof (44 lines). Key certificate is `linear_combination`.

---

### `private lemma ord_algebraMap_mul_ge`
- **Type**: For `c : K`, `n ≤ ord f → n ≤ ord(algebraMap c · f)`
- **What**: Multiplying by a scalar from K never decreases the `ord_∞`.
- **How**: Case split on `c = 0` (product vanishes, ord = ⊤) and `f = 0`; otherwise `ord(algebraMap c) = 0` via `ordAtInfty_algebraMap_F_nonzero`.
- **Hypotheses**: `n ≤ ord f`
- **Uses from project**: `ordAtInfty_algebraMap_F_nonzero`
- **Used by**: `ordAtInfty_addPullbackNumerator_reduced_frobenius_eq`, many terms
- **Visibility**: private
- **Lines**: 639–654, proof 15 lines

---

### `private lemma ord_two_mul_ge`
- **Type**: `n ≤ ord f → n ≤ ord(2 · f)`
- **What**: Multiplying by 2 never decreases `ord_∞` (works in char 2 via `f + f`).
- **How**: Rewrites `2f = f + f` and uses `ordAtInfty_add_ge_min`.
- **Uses from project**: (none from project; uses `ordAtInfty_add_ge_min`)
- **Used by**: `ordAtInfty_addPullbackNumerator_reduced_frobenius_eq`, `ordAtInfty_addPullbackNumerator_reduced_negFrobenius_eq`, `ordAtInfty_addPullbackNumerator_reduced_pair_zsmul_frobenius_mulByInt_neg_eq`
- **Visibility**: private
- **Lines**: 658–664, proof 7 lines

---

### `private lemma ord_x_gen_add_pi_x_eq`
- **Type**: `ord(x_gen + π·x) = -2q` for `q ≥ 2`
- **What**: The sum of x-coordinates has order `-2q`.
- **How**: `π·x` dominates via `ord_add_lt_concrete` since `-2q < -2`.
- **Uses from project**: `ordAtInfty_frobeniusIsog_pullback_x_gen`, `ordAtInfty_x_gen`
- **Used by**: `ordAtInfty_addPullbackNumerator_reduced_frobenius_eq`
- **Visibility**: private
- **Lines**: 668–678, proof 11 lines

---

### `private lemma ord_y_gen_add_pi_y_eq`
- **Type**: `ord(y_gen + π·y) = -3q` for `q ≥ 2`
- **What**: Sum of y-coordinates has order `-3q`.
- **How**: `π·y` dominates via `ord_add_lt_concrete` since `-3q < -3`.
- **Uses from project**: `ordAtInfty_frobeniusIsog_pullback_y_gen`, `ordAtInfty_y_gen`
- **Used by**: `ordAtInfty_addPullbackNumerator_reduced_frobenius_eq`
- **Visibility**: private
- **Lines**: 681–691, proof 11 lines

---

### `private lemma pi_x_gen_ne_zero`
- **Type**: `(frobeniusIsog W).pullback (x_gen W) ≠ 0`
- **What**: Frobenius pullback of `x_gen` is nonzero.
- **How**: Finite ord (`-2q`) contradicts `ordAtInfty_zero = ⊤`.
- **Uses from project**: `ordAtInfty_frobeniusIsog_pullback_x_gen`
- **Used by**: `ord_x_gen_mul_pi_x_eq`, `ord_x_gen_sq_mul_pi_x_eq`, `ord_x_gen_mul_pi_x_sq_eq`, `ord_x_pi_y_plus_pi_x_y_ge`
- **Visibility**: private
- **Lines**: 694–700, proof 7 lines

---

### `private lemma pi_y_gen_ne_zero`
- **Type**: `(frobeniusIsog W).pullback (y_gen W) ≠ 0`
- **What**: Frobenius pullback of `y_gen` is nonzero.
- **How**: Finite ord (`-3q`) contradicts `ordAtInfty_zero = ⊤`.
- **Uses from project**: `ordAtInfty_frobeniusIsog_pullback_y_gen`
- **Used by**: `ord_y_gen_mul_pi_y_eq`, `ord_x_pi_y_plus_pi_x_y_ge`
- **Visibility**: private
- **Lines**: 703–709, proof 7 lines

---

### `private lemma ord_x_gen_mul_pi_x_eq`
- **Type**: `ord(x_gen · π·x) = -2 - 2q`
- **What**: Computes the order of the product.
- **How**: `ordAtInfty_mul` then `congrArg₂`.
- **Uses from project**: `x_gen_ne_zero`, `pi_x_gen_ne_zero`, `ordAtInfty_x_gen`, `ordAtInfty_frobeniusIsog_pullback_x_gen`
- **Used by**: `ordAtInfty_addPullbackNumerator_reduced_frobenius_eq`
- **Visibility**: private
- **Lines**: 712–719, proof 8 lines

---

### `private lemma ord_x_gen_sq_mul_pi_x_eq`
- **Type**: `ord(x_gen² · π·x) = -4 - 2q`
- **What**: Order of `x²·π·x`.
- **How**: `ord_pow_concrete` for `x²`, then `ordAtInfty_mul`.
- **Uses from project**: `x_gen_ne_zero`, `pi_x_gen_ne_zero`, `ordAtInfty_x_gen`, `ordAtInfty_frobeniusIsog_pullback_x_gen`
- **Used by**: `ordAtInfty_addPullbackNumerator_reduced_frobenius_eq`
- **Visibility**: private
- **Lines**: 722–735, proof 14 lines

---

### `private lemma ord_x_gen_mul_pi_x_sq_eq`
- **Type**: `ord(x_gen · (π·x)²) = -2 - 4q`
- **What**: Order of the dominant term.
- **How**: `ord_pow_concrete` for `(π·x)²`, then `ordAtInfty_mul`.
- **Uses from project**: `pi_x_gen_ne_zero`, `x_gen_ne_zero`, `ordAtInfty_x_gen`, `ordAtInfty_frobeniusIsog_pullback_x_gen`
- **Used by**: `ordAtInfty_addPullbackNumerator_reduced_frobenius_eq`
- **Visibility**: private
- **Lines**: 738–755, proof 18 lines

---

### `private lemma ord_y_gen_mul_pi_y_eq`
- **Type**: `ord(y_gen · π·y) = -3 - 3q`
- **What**: Order of product of y-coordinates.
- **How**: `ordAtInfty_mul` then `congrArg₂`.
- **Uses from project**: `y_gen_ne_zero`, `pi_y_gen_ne_zero`, `ordAtInfty_y_gen`, `ordAtInfty_frobeniusIsog_pullback_y_gen`
- **Used by**: `ordAtInfty_addPullbackNumerator_reduced_frobenius_eq`
- **Visibility**: private
- **Lines**: 758–765, proof 8 lines

---

### `private lemma ord_x_pi_y_plus_pi_x_y_ge`
- **Type**: `(-2 - 3q : ℤ) ≤ ord(x·π·y + π·x·y)` for `q ≥ 2`
- **What**: Lower bound for the cross term.
- **How**: Computes individual orders, applies `ordAtInfty_add_ge_min`, uses `le_min`.
- **Uses from project**: `x_gen_ne_zero`, `pi_y_gen_ne_zero`, `y_gen_ne_zero`, `pi_x_gen_ne_zero`, `ordAtInfty_x_gen`, `ordAtInfty_y_gen`, `ordAtInfty_frobeniusIsog_pullback_y_gen`, `ordAtInfty_frobeniusIsog_pullback_x_gen`
- **Used by**: `ordAtInfty_addPullbackNumerator_reduced_frobenius_eq`
- **Visibility**: private
- **Lines**: 770–806, proof 37 lines
- **Notes**: Long proof (37 lines).

---

### `private lemma ord_add_ge_of_both_ge`
- **Type**: `n ≤ ord f → n ≤ ord g → n ≤ ord(f + g)`
- **What**: Sum preserves a lower ord bound.
- **How**: `le_min` plus `ordAtInfty_add_ge_min`.
- **Used by**: Throughout the file wherever term-bounds are chained
- **Visibility**: private
- **Lines**: 810–813, proof 2 lines

---

### `private lemma ord_neg_ge`
- **Type**: `n ≤ ord f → n ≤ ord(-f)`
- **What**: Negation preserves a lower ord bound.
- **How**: Rewrites via `ordAtInfty_neg`.
- **Used by**: `ord_sub_ge_of_both_ge`
- **Visibility**: private
- **Lines**: 816–819, proof 2 lines

---

### `private lemma ord_sub_ge_of_both_ge`
- **Type**: `n ≤ ord f → n ≤ ord g → n ≤ ord(f − g)`
- **What**: Subtraction preserves a lower ord bound.
- **How**: Rewrites `f − g = f + (−g)` and applies `ord_add_ge_of_both_ge` with `ord_neg_ge`.
- **Used by**: Throughout the file for chaining term bounds
- **Visibility**: private
- **Lines**: 822–826, proof 5 lines

---

### `theorem ordAtInfty_addPullbackNumerator_reduced_frobenius_eq`
- **Type**: `ord(addPullbackNumerator_reduced_frobenius W) = -2 - 4q` for `q ≥ 2`
- **What**: **Key computation**: the dominant term `x·(π·x)²` (order `-2-4q`) strictly beats all 7 "rest" terms (order `≥ -3-3q`), giving `ord(reduced) = -2-4q`.
- **How**: Establishes 7 term-bounds via `ord_algebraMap_mul_ge`, `ord_two_mul_ge`, and the private lemmas; chains them via `ord_add_ge_of_both_ge`/`ord_sub_ge_of_both_ge`; then splits the algebraic identity and applies `ordAtInfty_add_eq_of_lt`.
- **Hypotheses**: `q ≥ 2`
- **Uses from project**: `ord_algebraMap_mul_ge`, `ord_two_mul_ge`, `ord_x_gen_add_pi_x_eq`, `ord_y_gen_add_pi_y_eq`, `ord_y_gen_mul_pi_y_eq`, `ord_x_pi_y_plus_pi_x_y_ge`, `ord_x_gen_sq_mul_pi_x_eq`, `ord_x_gen_mul_pi_x_eq`, `ord_x_gen_mul_pi_x_sq_eq`, `ord_add_ge_of_both_ge`, `ord_sub_ge_of_both_ge`, `ordAtInfty_algebraMap_F_nonzero`
- **Used by**: `ord_addPullback_x_frobenius`
- **Visibility**: public
- **Lines**: 835–975, proof ~140 lines
- **Notes**: **Longest proof in file** (~140 lines). No `set_option maxHeartbeats`.

---

### `theorem ord_addPullback_x_frobenius`
- **Type**: `ord(addPullback_x W (frobeniusIsog W)) = -2` for `q ≥ 2`
- **What**: **Main theorem**: the addition-pullback x-coordinate has a simple pole at ∞ of order exactly `-2`.
- **How**: Uses Weierstrass reduction identity (`addPullbackNumerator_frobenius_eq_reduced`) to get `ord(numerator) = -2-4q`; numerator equals `(x−π·x)² · addPullback_x` (ord of denominator `= -4q`); division gives `-2-4q − (-4q) = -2`.
- **Hypotheses**: `q ≥ 2`
- **Uses from project**: `x_gen_sub_frobeniusIsog_pullback_x_gen_ne_zero`, `ordAtInfty_x_gen_sub_frobeniusIsog_pullback_x_gen`, `addPullbackNumerator_frobenius_eq_reduced`, `ordAtInfty_addPullbackNumerator_reduced_frobenius_eq`, `addPullbackNumerator_frobenius_eq`
- **Used by**: `addPullback_x_ne_const_frobenius`, `ordAtInfty_addPullback_x_frobenius_le_neg_two`
- **Visibility**: public
- **Lines**: 985–1016, proof 32 lines
- **Notes**: Long proof (32 lines).

---

### `theorem addPullback_x_ne_const_frobenius`
- **Type**: For `q ≥ 2`, `AddNonInverse`, `hc`: `addPullback_x = algebraMap c` → False
- **What**: **Sorry 1 closure for the Frobenius case**: the addition x-coordinate is not a constant.
- **How**: `ord = -2 < 0` via `ord_addPullback_x_frobenius`, then `addPullback_x_ne_const_of_pole`.
- **Uses from project**: `ord_addPullback_x_frobenius`, `addPullback_x_ne_const_of_pole`
- **Used by**: `addPullback_x_transcendental_negFrobenius` (indirectly)
- **Visibility**: public
- **Lines**: 1023–1029, proof 7 lines

---

### `theorem ordAtInfty_addPullback_x_frobenius_le_neg_two`
- **Type**: `ord(addPullback_x W (frobeniusIsog W)) ≤ -2` for `q ≥ 2`
- **What**: Inequality corollary for downstream consumers.
- **How**: `.le` from the equality.
- **Uses from project**: `ord_addPullback_x_frobenius`
- **Used by**: (unused in file)
- **Visibility**: public
- **Lines**: 1035–1039, proof 1 line

---

### `noncomputable def negFrobeniusIsog`
- **Type**: `Isogeny W.toAffine W.toAffine`
- **What**: The `−π` isogeny, defined as `[-1] ∘ π = mulByInt(-1) ∘ frobeniusIsog`.
- **How**: `Isogeny.comp`.
- **Uses from project**: `mulByInt`, `frobeniusIsog`
- **Used by**: Throughout the file for the `−π` analysis
- **Visibility**: public
- **Lines**: 1072–1073, definition

---

### `theorem negFrobeniusIsog_toAddMonoidHom_apply`
- **Type**: `(negFrobeniusIsog W).toAddMonoidHom P = -((frobeniusIsog W).toAddMonoidHom P)`
- **What**: Pointwise: `(−π)(P) = −π(P)`.
- **How**: `Isogeny.comp_toAddMonoidHom`, `mulByInt_apply`, `neg_one_zsmul`.
- **Uses from project**: `mulByInt_apply`
- **Used by**: (unused in file)
- **Visibility**: public
- **Lines**: 1079–1086, proof 8 lines

---

### `theorem mulByInt_pullback_y_neg_one`
- **Type**: `(mulByInt W (-1)).pullback (y_gen W) = -y_gen W - a₁·x_gen - a₃`
- **What**: The `[-1]`-pullback sends `y_gen` to the curve-negation formula.
- **How**: Reduces to `mulByInt_y_neg` → `mulByInt_y_neg_one` → `rfl` via definitional equality.
- **Uses from project**: `mulByInt_pullback_y`, `mulByInt_y_neg`, `mulByInt_x_one`, `mulByInt_y_one`
- **Used by**: `negFrobeniusIsog_pullback_y_gen`, `mulByInt_neg_one_pullback_y_gen_ne_y_gen_char_two`, `mulByInt_neg_one_pullback_y_gen_ne_y_gen_char_ne_two`, `mulByInt_neg_one_pullback_y_gen_eq`, `sigma_frobenius_pullback_y_eq_negFrobenius_pullback_y`
- **Visibility**: public
- **Lines**: 1094–1111, proof 18 lines

---

### `theorem negFrobeniusIsog_pullback_x_gen`
- **Type**: `(negFrobeniusIsog W).pullback (x_gen W) = (frobeniusIsog W).pullback (x_gen W)`
- **What**: The `−π` isogeny fixes the x-generator (since `[-1]` fixes `x_gen`).
- **How**: `Isogeny.comp_algebraMap_eq`, `mulByInt_pullback_x_neg_one`.
- **Uses from project**: `mulByInt_pullback_x_neg_one`
- **Used by**: Many lemmas in the negFrobenius and pair sections
- **Visibility**: public
- **Lines**: 1119–1123, proof 5 lines

---

### `theorem negFrobeniusIsog_pullback_y_gen`
- **Type**: `(negFrobeniusIsog W).pullback (y_gen W) = -π·y − a₁·π·x − a₃`
- **What**: The `−π` pullback of `y_gen` is the negation formula applied to Frobenius pullback.
- **How**: `Isogeny.comp_algebraMap_eq`, `mulByInt_pullback_y_neg_one`, then `simp` with `map_*` and `AlgHom.commutes`.
- **Uses from project**: `mulByInt_pullback_y_neg_one`
- **Used by**: `ordAtInfty_negFrobeniusIsog_pullback_y_gen`, `sigma_frobenius_pullback_y_eq_negFrobenius_pullback_y`, `sigma_negFrobenius_pullback_y_eq_frobenius_pullback_y`, `addPullback_x_negFrobenius_sigma_invariant`
- **Visibility**: public
- **Lines**: 1132–1143, proof 12 lines

---

### `theorem ordAtInfty_negFrobeniusIsog_pullback_x_gen`
- **Type**: `ord(negFrob.pb x_gen) = -2q`
- **What**: The `−π` pullback of `x_gen` has the same order as Frobenius.
- **How**: Rewrites via `negFrobeniusIsog_pullback_x_gen` then uses the Frobenius lemma.
- **Uses from project**: `negFrobeniusIsog_pullback_x_gen`, `ordAtInfty_frobeniusIsog_pullback_x_gen`
- **Used by**: `negFrob_pi_x_gen_ne_zero`, `ord_x_gen_add_negFrob_pi_x_eq`, `ordAtInfty_negFrobeniusIsog_pullback_y_gen`, `ordAtInfty_x_gen_sub_negFrobeniusIsog_pullback_x_gen`
- **Visibility**: public
- **Lines**: 1156–1160, proof 5 lines

---

### `theorem ordAtInfty_negFrobeniusIsog_pullback_y_gen`
- **Type**: `ord(negFrob.pb y_gen) = -3q` for `q ≥ 2`
- **What**: The `−π` pullback of `y_gen` has order `-3q`.
- **How**: Regroups as `-π·y − (a₁·π·x + a₃)`: the `-π·y` term (ord `-3q`) strictly beats the correction (ord `≥ -2q`), so `ordAtInfty_sub_eq_of_lt` gives `-3q`.
- **Hypotheses**: `q ≥ 2`
- **Uses from project**: `negFrobeniusIsog_pullback_y_gen`, `ordAtInfty_frobeniusIsog_pullback_y_gen`, `ord_algebraMap_mul_ge`, `ordAtInfty_frobeniusIsog_pullback_x_gen`, `ord_add_ge_of_both_ge`, `ordAtInfty_algebraMap_F_nonzero`
- **Used by**: `negFrob_pi_y_gen_ne_zero`, `ord_y_gen_add_negFrob_pi_y_eq`, `ord_y_gen_mul_negFrob_pi_y_eq`, `ord_x_negFrob_pi_y_plus_negFrob_pi_x_y_ge`
- **Visibility**: public
- **Lines**: 1170–1216, proof 47 lines
- **Notes**: Long proof (47 lines).

---

### `noncomputable def addPullbackNumerator_negFrobenius`
- **Type**: `KE` — same shape as `addPullbackNumerator_frobenius` with `negFrobeniusIsog`
- **What**: Numerator for clearing `(x − negFrob.pb x)²` from `addPullback_x W (negFrobeniusIsog W)`.
- **Used by**: `addPullbackNumerator_negFrobenius_eq_reduced`, `addPullbackNumerator_negFrobenius_eq`, `ord_addPullback_x_negFrobenius`
- **Visibility**: public
- **Lines**: 1229–1236, definition

---

### `noncomputable def addPullbackNumerator_reduced_negFrobenius`
- **Type**: `KE` — Weierstrass-reduced 8-term form for the negFrobenius case
- **What**: Same shape as `addPullbackNumerator_reduced_frobenius` with `negFrobeniusIsog`.
- **Used by**: `addPullbackNumerator_negFrobenius_eq_reduced`, `ordAtInfty_addPullbackNumerator_reduced_negFrobenius_eq`
- **Visibility**: public
- **Lines**: 1244–1257, definition

---

### `theorem addPullbackNumerator_negFrobenius_eq_reduced`
- **Type**: `addPullbackNumerator_negFrobenius W = addPullbackNumerator_reduced_negFrobenius W`
- **What**: Weierstrass reduction for the `−π` numerator.
- **How**: Uses `generic_equation` and `pullback_equation W (negFrobeniusIsog W)`, then `linear_combination h_xy + h_uv`.
- **Uses from project**: `generic_equation`, `pullback_equation`
- **Used by**: `ord_addPullback_x_negFrobenius`
- **Visibility**: public
- **Lines**: 1270–1315, proof 46 lines
- **Notes**: Long proof (46 lines). Mirror of `addPullbackNumerator_frobenius_eq_reduced`.

---

*(Private lemmas `negFrob_pi_x_gen_ne_zero`, `negFrob_pi_y_gen_ne_zero`, `ord_x_gen_add_negFrob_pi_x_eq`, `ord_y_gen_add_negFrob_pi_y_eq`, `ord_x_gen_mul_negFrob_pi_x_eq`, `ord_x_gen_sq_mul_negFrob_pi_x_eq`, `ord_x_gen_mul_negFrob_pi_x_sq_eq`, `ord_y_gen_mul_negFrob_pi_y_eq`, `ord_x_negFrob_pi_y_plus_negFrob_pi_x_y_ge` at lines 1321–1433 are mirrors of the Frobenius private helpers, each routing through the pullback equality `negFrobeniusIsog_pullback_x_gen` or directly computing with `negFrobeniusIsog_pullback_y_gen`.)*

---

### `theorem ordAtInfty_addPullbackNumerator_reduced_negFrobenius_eq`
- **Type**: `ord(addPullbackNumerator_reduced_negFrobenius W) = -2 - 4q` for `q ≥ 2`
- **What**: Mirror of `ordAtInfty_addPullbackNumerator_reduced_frobenius_eq` for `−π`.
- **How**: Same 7-term chaining proof structure; dominant term `x·(negFrob.pb x)² = x·(π·x)²` (same ord since pullback x is same).
- **Hypotheses**: `q ≥ 2`
- **Uses from project**: negFrob private helpers, `ord_algebraMap_mul_ge`, `ord_two_mul_ge`, `ord_add_ge_of_both_ge`, `ord_sub_ge_of_both_ge`, `ordAtInfty_algebraMap_F_nonzero`, `ord_x_gen_mul_negFrob_pi_x_sq_eq`
- **Used by**: `ord_addPullback_x_negFrobenius`
- **Visibility**: public
- **Lines**: 1443–1579, proof ~136 lines
- **Notes**: **Very long proof** (~136 lines). Mirror of Frobenius version.

---

### `private lemma x_gen_ne_negFrobeniusIsog_pullback_x_gen`
- **Type**: `x_gen W ≠ (negFrobeniusIsog W).pullback (x_gen W)`
- **How**: Rewrites via `negFrobeniusIsog_pullback_x_gen` and uses `x_gen_ne_frobeniusIsog_pullback_x_gen`.
- **Lines**: 1590–1593

---

### `lemma x_gen_sub_negFrobeniusIsog_pullback_x_gen_ne_zero`
- **Type**: `x_gen W - (negFrobeniusIsog W).pullback (x_gen W) ≠ 0`
- **How**: Via `negFrobeniusIsog_pullback_x_gen` + `x_gen_sub_frobeniusIsog_pullback_x_gen_ne_zero`.
- **Visibility**: public
- **Lines**: 1596–1599

---

### `private lemma ordAtInfty_x_gen_sub_negFrobeniusIsog_pullback_x_gen`
- **Type**: `ord(x_gen − negFrob.pb x_gen) = -2q`
- **Lines**: 1602–1607

---

### `theorem addSlope_negFrobeniusIsog_eq`
- **Type**: `addSlope W (negFrobeniusIsog W) = (y − negFrob.pb y) / (x − negFrob.pb x)`
- **Lines**: 1610–1615

---

### `theorem addPullbackNumerator_negFrobenius_eq`
- **Type**: `addPullbackNumerator_negFrobenius W = (x − negFrob.pb x)² · addPullback_x W (negFrobeniusIsog W)`
- **How**: Slope formula + field_simp; ring. Mirror of `addPullbackNumerator_frobenius_eq`.
- **Lines**: 1620–1645, proof 26 lines

---

### `theorem ord_addPullback_x_negFrobenius`
- **Type**: `ord(addPullback_x W (negFrobeniusIsog W)) = -2` for `q ≥ 2`
- **What**: **Main theorem for `−π`**: the addition pullback x-coordinate has a simple pole of order `-2`.
- **How**: Weierstrass reduction + numerator ord + denominator ord, then `ord_div_concrete`.
- **Uses from project**: `x_gen_sub_negFrobeniusIsog_pullback_x_gen_ne_zero`, `ordAtInfty_x_gen_sub_negFrobeniusIsog_pullback_x_gen`, `addPullbackNumerator_negFrobenius_eq_reduced`, `ordAtInfty_addPullbackNumerator_reduced_negFrobenius_eq`, `addPullbackNumerator_negFrobenius_eq`
- **Used by**: `addPullback_x_ne_const_negFrobenius`, `ordAtInfty_addPullback_x_negFrobenius_le_neg_two`, `addPullback_x_negFrobenius_ne_zero`, `ord_addPullback_x_negFrobenius` (called in y-ord proof)
- **Visibility**: public
- **Lines**: 1652–1679, proof 28 lines

---

### `theorem addPullback_x_ne_const_negFrobenius`
- **Type**: For `q ≥ 2`, `AddNonInverse W (negFrobeniusIsog W)`, `hc`: False
- **What**: **Sorry 1 closure for the `−π` case**.
- **Uses from project**: `ord_addPullback_x_negFrobenius`, `addPullback_x_ne_const_of_pole`
- **Visibility**: public
- **Lines**: 1687–1693, proof 7 lines

---

### `theorem ordAtInfty_addPullback_x_negFrobenius_le_neg_two`
- **Type**: `ord ≤ -2` corollary
- **Lines**: 1700–1704, proof 1 line

---

### `private theorem addPullback_x_negFrobenius_ne_zero`
- **Type**: `addPullback_x W (negFrobeniusIsog W) ≠ 0` for `q ≥ 2`
- **Lines**: 1723–1730

---

### `private theorem ord_addPullback_x_sq_negFrobenius`
- **Type**: `ord(X²) = -4` for the `−π` case
- **Lines**: 1733–1738

---

### `private theorem ord_addPullback_x_cube_negFrobenius`
- **Type**: `ord(X³) = -6` for the `−π` case
- **Lines**: 1741–1746

---

### `private theorem ord_RHS_lower_ge_neg_four_negFrobenius`
- **Type**: `(-4 : ℤ) ≤ ord(a₂·X² + a₄·X + a₆)` for the `−π` case
- **Lines**: 1749–1777

---

### `private theorem ord_a₆_ge_zero`
- **Type**: `0 ≤ ord(a₆)` (as an element of KE)
- **Lines**: 1780–1786

---

### `private theorem ord_RHS_negFrobenius`
- **Type**: `ord(X³ + a₂X² + a₄X + a₆) = -6` for the `−π` case
- **How**: Three-step strict non-arch on the sum.
- **Lines**: 1790–1843, proof 54 lines
- **Notes**: Long proof (54 lines). Used by `ord_addPullback_y_negFrobenius`.

---

### `private theorem negFrobeniusIsog_addNonInverse_for_y_ord`
- **Type**: `AddNonInverse W (negFrobeniusIsog W)` (inline, avoids forward reference)
- **Lines**: 1847–1851

---

### `theorem ord_addPullback_y_negFrobenius`
- **Type**: `ord(addPullback_y W (negFrobeniusIsog W)) = -3` for `q ≥ 2`
- **What**: The y-coordinate of the addition pullback for `−π` has a pole of order `-3` at `∞`.
- **How**: Uses the Weierstrass equation `addPullback_equation`; the RHS has `ord = -6`; case analysis on `ord(Y) = m`: rules out `m ≥ -2` (LHS ord ≥ -4, contradiction) and uses `Y²` strict dominance when `m ≤ -3` to get `2m = -6`, hence `m = -3`.
- **Hypotheses**: `q ≥ 2`
- **Uses from project**: `ord_addPullback_x_negFrobenius`, `addPullback_x_negFrobenius_ne_zero`, `addPullback_equation`, `ord_RHS_negFrobenius`, `negFrobeniusIsog_addNonInverse_for_y_ord`, `ord_algebraMap_mul_ge`, `ord_add_ge_of_both_ge`
- **Used by**: (unused in file; consumed by downstream pencil-comap work)
- **Visibility**: public
- **Lines**: 1861–2028, proof ~168 lines
- **Notes**: **Longest proof in file** (~168 lines). No `set_option maxHeartbeats`.

---

### `noncomputable def addPullbackAlgHom_negFrobenius_of_inj`
- **Type**: `KE →ₐ[K] KE`, witness-parametric on injectivity of `addCoordAlgHom hxy`
- **What**: The algebra hom encoding `id + (−π)` pullback, parametric on the injectivity proof.
- **Uses from project**: `addPullbackAlgHom`
- **Used by**: `addPullbackAlgHom_negFrobenius`
- **Visibility**: public
- **Lines**: 2084–2087, definition

---

### `theorem sigma_frobenius_pullback_y_eq_negFrobenius_pullback_y`
- **Type**: `σ(π·y_gen) = negFrob.pb(y_gen)` where `σ = mulByInt(-1).pullback`
- **What**: σ-invariance step 1: σ sends `π·y` to the `−π` pullback of `y`.
- **How**: Rewrites via `frobeniusIsog_pullback_apply`, `map_pow`, `mulByInt_pullback_y_neg_one`, then uses `← frobeniusIsog_pullback_apply` and distributes via `simp`.
- **Uses from project**: `frobeniusIsog_pullback_apply`, `mulByInt_pullback_y_neg_one`, `negFrobeniusIsog_pullback_y_gen`
- **Used by**: `sigma_negFrobenius_pullback_y_eq_frobenius_pullback_y`, `addSlope_negFrobenius_sigma_sum_eq_neg_a1`
- **Visibility**: public
- **Lines**: 2101–2113, proof 13 lines

---

### `theorem sigma_frobenius_pullback_x_eq`
- **Type**: `σ(π·x_gen) = π·x_gen`
- **What**: σ fixes `π·x_gen` (since σ fixes `x_gen` and Frobenius preserves powers).
- **Uses from project**: `frobeniusIsog_pullback_apply`, `mulByInt_pullback_x_neg_one`
- **Used by**: `sigma_negFrobenius_pullback_y_eq_frobenius_pullback_y`, `addSlope_negFrobenius_sigma_sum_eq_neg_a1`, `addPullback_x_negFrobenius_sigma_invariant`
- **Visibility**: public
- **Lines**: 2118–2122, proof 5 lines

---

### `theorem sigma_negFrobenius_pullback_y_eq_frobenius_pullback_y`
- **Type**: `σ(negFrob.pb y_gen) = frob.pb(y_gen)`
- **What**: σ swaps the two y-pullbacks.
- **How**: Distributes σ over the explicit form of `negFrob.pb y`, uses Step 1 and x-helper, then `ring`.
- **Uses from project**: `negFrobeniusIsog_pullback_y_gen`, `sigma_frobenius_pullback_y_eq_negFrobenius_pullback_y`, `sigma_frobenius_pullback_x_eq`
- **Used by**: `addSlope_negFrobenius_sigma_sum_eq_neg_a1`
- **Visibility**: public
- **Lines**: 2131–2139, proof 9 lines

---

### `theorem addSlope_negFrobenius_sigma_sum_eq_neg_a1`
- **Type**: `σ(L_neg) + L_neg = -a₁` where `L_neg = addSlope W (negFrobeniusIsog W)`
- **What**: The curve-arithmetic identity driving σ-invariance of `addPullback_x`.
- **How**: Applies `map_div₀` to the slope formula; distributes σ via `simp` using the σ-pair lemmas; then `field_simp; ring`.
- **Uses from project**: `x_gen_sub_frobeniusIsog_pullback_x_gen_ne_zero`, `addSlope_negFrobeniusIsog_eq`, `sigma_frobenius_pullback_y_eq_negFrobenius_pullback_y`, `sigma_frobenius_pullback_x_eq`, `negFrobeniusIsog_pullback_x_gen`, `negFrobeniusIsog_pullback_y_gen`, `sigma_negFrobenius_pullback_y_eq_frobenius_pullback_y`
- **Used by**: `addPullback_x_negFrobenius_sigma_invariant`
- **Visibility**: public
- **Lines**: 2152–2172, proof 21 lines

---

### `theorem addPullback_x_negFrobenius_sigma_invariant`
- **Type**: `σ(addPullback_x W (negFrobeniusIsog W)) = addPullback_x W (negFrobeniusIsog W)`
- **What**: **σ-invariance step 3**: the `−π` addition-pullback x-coordinate is fixed by σ.
- **How**: Unfolds `addPullback_x`/`addX`; uses `simp` with σ-lemmas; then `linear_combination` with `addSlope_negFrobenius_sigma_sum_eq_neg_a1`.
- **Uses from project**: `negFrobeniusIsog_pullback_x_gen`, `sigma_frobenius_pullback_x_eq`, `addSlope_negFrobenius_sigma_sum_eq_neg_a1`
- **Used by**: `addPullback_x_negFrobenius_in_KX_image`
- **Visibility**: public
- **Lines**: 2186–2205, proof 20 lines

---

### `theorem mulByInt_neg_one_pullback_comp_self`
- **Type**: `σ.comp σ = AlgHom.id K KE`
- **What**: σ has order 2 (involution).
- **How**: `mulByInt_comp_eq_mul W (-1) (-1)` gives `[-1]∘[-1]=[1]`, then take pullbacks; `mulByInt_one_pullback_eq_id`.
- **Uses from project**: `mulByInt_comp_eq_mul`, `mulByInt_one_pullback_eq_id`
- **Used by**: `mulByInt_neg_one_pullback_pow_two_apply`
- **Visibility**: public
- **Lines**: 2223–2242, proof 20 lines

---

### `theorem mulByInt_neg_one_pullback_pow_two_apply`
- **Type**: `σ(σ(z)) = z` for all `z : KE`
- **What**: Pointwise involution statement.
- **Uses from project**: `mulByInt_neg_one_pullback_comp_self`
- **Used by**: (unused in file)
- **Visibility**: public
- **Lines**: 2246–2250, proof 5 lines

---

### `theorem mulByInt_neg_one_pullback_y_gen_ne_y_gen_char_two`
- **Type**: `σ(y_gen W) ≠ y_gen W` in char 2
- **What**: σ is nontrivial in char 2 (uses `[IsElliptic]` discriminant).
- **How**: If `σ(y) = y`, then `a₁·x + a₃ = 0` in char 2; transcendence of `x_gen` forces `a₁ = a₃ = 0`; then `Δ_of_char_two` gives `Δ = 0`, contradicting `IsElliptic`.
- **Uses from project**: `mulByInt_pullback_y_neg_one`, `x_gen_transcendental`, `transcendental_iff`
- **Used by**: `mulByInt_neg_one_pullback_y_gen_ne_y_gen`
- **Visibility**: public
- **Lines**: 2269–2304, proof 36 lines
- **Notes**: Long proof (36 lines).

---

### `theorem mulByInt_neg_one_pullback_y_gen_ne_y_gen_char_ne_two`
- **Type**: `σ(y_gen W) ≠ y_gen W` for `(2 : K) ≠ 0`
- **What**: σ is nontrivial in char ≠ 2.
- **How**: If `σ(y) = y`, view `2y + a₁x + a₃ = 0` as a `{1, y_gen}` basis decomposition via `decomp_zero_iff`; the `y_gen`-coefficient is `2`, so `(2 : Frac(K[X])) = 0`, but injectivity `K → Frac(K[X])` contradicts `(2 : K) ≠ 0`.
- **Uses from project**: `mulByInt_pullback_y_neg_one`, `decomp_zero_iff`, `coordY_eq_coordYInFunctionField`, `coordY_W_smooth_eq_y_gen`
- **Used by**: `mulByInt_neg_one_pullback_y_gen_ne_y_gen`
- **Visibility**: public
- **Lines**: 2314–2366, proof 53 lines
- **Notes**: Long proof (53 lines).

---

### `theorem mulByInt_neg_one_pullback_y_gen_ne_y_gen`
- **Type**: `σ(y_gen W) ≠ y_gen W` (any characteristic)
- **What**: Unified: σ is nontrivial.
- **How**: Case split on `(2 : K) = 0`; uses char-2 and char-≠2 variants.
- **Uses from project**: `mulByInt_neg_one_pullback_y_gen_ne_y_gen_char_two`, `mulByInt_neg_one_pullback_y_gen_ne_y_gen_char_ne_two`
- **Used by**: (unused in file directly; key ingredient for Galois theory)
- **Visibility**: public
- **Lines**: 2374–2381, proof 8 lines

---

### `@[simp] theorem mulByInt_neg_one_pullback_algebraMap_K`
- **Type**: `σ(algebraMap c) = algebraMap c` for any `c : K`
- **What**: σ fixes K-constants.
- **How**: `AlgHom.commutes`.
- **Used by**: (referenced in σ-fixed analysis)
- **Visibility**: public (simp)
- **Lines**: 2390–2393, proof 1 line

---

### `theorem mulByInt_neg_one_pullback_algebraMap_polyK`
- **Type**: `σ(algebraMap p) = algebraMap p` for any `p : Polynomial K`
- **What**: σ fixes images of K[X].
- **How**: Uses uniqueness of K-algebra homs via `Polynomial.algHom_ext` (both sides agree on X since σ fixes `x_gen`), then `← Polynomial.aeval_algHom_apply`.
- **Uses from project**: (none from project)
- **Used by**: `mulByInt_neg_one_pullback_algebraMap_kx`
- **Visibility**: public
- **Lines**: 2398–2417, proof 20 lines

---

### `theorem mulByInt_neg_one_pullback_algebraMap_kx`
- **Type**: `σ(algebraMap r) = algebraMap r` for any `r : FractionRing (Polynomial K)`
- **What**: σ fixes images of `K(x) = Frac(K[X])`.
- **How**: Lifts from `mulByInt_neg_one_pullback_algebraMap_polyK` via `IsLocalization.surj` denominator clearing.
- **Uses from project**: `mulByInt_neg_one_pullback_algebraMap_polyK`
- **Used by**: `sigma_fixed_implies_in_KX_image`
- **Visibility**: public
- **Lines**: 2422–2447, proof 26 lines

---

### `theorem mulByInt_neg_one_pullback_y_gen_eq`
- **Type**: Restates `mulByInt_pullback_y_neg_one`
- **What**: Re-statement for use with basis machinery.
- **Lines**: 2453–2457, proof 1 line (delegation)

---

### `theorem a₁X_plus_a₃_ne_zero_char_two`
- **Type**: `C(a₁)·X + C(a₃) ≠ 0` as polynomial, in char 2
- **What**: The polynomial `a₁X + a₃` is nonzero for an elliptic curve in char 2.
- **How**: If zero, then `a₁ = a₃ = 0`, and `Δ_of_char_two` gives `Δ = 0`, contradicting `IsElliptic`.
- **Used by**: `sigma_fixed_implies_in_KX_image`
- **Visibility**: public
- **Lines**: 2464–2476, proof 13 lines

---

### `theorem algebraMap_a₁X_plus_a₃`
- **Type**: `algebraMap (K[X]) KE (C(a₁)·X + C(a₃)) = a₁·x_gen + a₃`
- **What**: Identifies the polynomial's image in KE.
- **Used by**: `sigma_fixed_implies_in_KX_image`
- **Visibility**: public
- **Lines**: 2480–2493, proof 14 lines

---

### `theorem sigma_fixed_implies_in_KX_image`
- **Type**: For `f : KE`, `σ(f) = f` → `∃ a : Frac(K[X]), f = algebraMap a`
- **What**: **σ-fixed implies in K(x)**: the core Galois-theory consequence.
- **How**: Writes `f = a·1 + b·Y` via `exists_decomp`; applies σ, collects via `decomp_zero_iff`; char-splits to deduce `b = 0`; in char 2 uses `a₁X+a₃ ≠ 0`; in char ≠ 2 uses `2 ≠ 0`.
- **Uses from project**: `exists_decomp`, `mulByInt_neg_one_pullback_algebraMap_kx`, `mulByInt_neg_one_pullback_y_gen_eq`, `decomp_zero_iff`, `algebraMap_a₁X_plus_a₃`, `a₁X_plus_a₃_ne_zero_char_two`
- **Used by**: `addPullback_x_negFrobenius_in_KX_image`, `addPullback_x_pair_zsmul_frobenius_mulByInt_neg_in_KX_image`
- **Visibility**: public
- **Lines**: 2511–2586, proof 75 lines
- **Notes**: Long proof (75 lines). Key structural lemma.

---

### `theorem addPullback_x_negFrobenius_in_KX_image`
- **Type**: `∃ a, addPullback_x W (negFrobeniusIsog W) = algebraMap a`
- **What**: The `−π` addition x-coord lies in the image of `K(x)`.
- **How**: One-line: `sigma_fixed_implies_in_KX_image` applied to `addPullback_x_negFrobenius_sigma_invariant`.
- **Uses from project**: `sigma_fixed_implies_in_KX_image`, `addPullback_x_negFrobenius_sigma_invariant`
- **Used by**: `addPullback_x_transcendental_negFrobenius`
- **Visibility**: public
- **Lines**: 2594–2599, proof 2 lines

---

### `theorem addPullback_x_transcendental_negFrobenius`
- **Type**: For `q ≥ 2`, `AddNonInverse W (negFrobeniusIsog W)`: `Transcendental K (addPullback_x W (negFrobeniusIsog W))`
- **What**: **Sorry 2 closure for `α = −π`**: the `−π` addition x-coord is transcendental over K.
- **How**: If algebraic, the K(x)-representative `r` is also algebraic; `algebraic_in_fracRing_eq_const` gives `r = algebraMap c`; then `addPullback_x_ne_const_negFrobenius` gives contradiction.
- **Uses from project**: `addPullback_x_negFrobenius_in_KX_image`, `algebraic_in_fracRing_eq_const`, `addPullback_x_ne_const_negFrobenius`
- **Used by**: `addBaseHom_injective_negFrobenius`
- **Visibility**: public
- **Lines**: 2622–2639, proof 18 lines

---

### `theorem addBaseHom_injective_negFrobenius`
- **Type**: For `q ≥ 2`, `AddNonInverse`: `Function.Injective (addBaseHom W (negFrobeniusIsog W))`
- **What**: Base-hom injectivity for the `−π` case.
- **How**: `addBaseHom_eq_aeval` + `transcendental_iff_injective` + transcendence.
- **Uses from project**: `addBaseHom_eq_aeval`, `transcendental_iff_injective`, `addPullback_x_transcendental_negFrobenius`
- **Used by**: `addCoordAlgHom_injective_negFrobenius`
- **Visibility**: public
- **Lines**: 2653–2659, proof 7 lines

---

### `theorem addCoordAlgHom_injective_negFrobenius`
- **Type**: For `q ≥ 2`, `AddNonInverse`: `Function.Injective (addCoordAlgHom hxy)`
- **What**: Full `addCoordAlgHom` injectivity for `−π`.
- **How**: `addCoordAlgHom_injective_of_baseHom_inj` + `addBaseHom_injective_negFrobenius`.
- **Uses from project**: `addCoordAlgHom_injective_of_baseHom_inj`, `addBaseHom_injective_negFrobenius`
- **Used by**: `addPullbackAlgHom_negFrobenius`
- **Visibility**: public
- **Lines**: 2670–2675, proof 6 lines

---

### `theorem negFrobeniusIsog_addNonInverse`
- **Type**: `AddNonInverse W (negFrobeniusIsog W)`
- **What**: The `−π` isogeny satisfies the non-inverse condition.
- **How**: The would-be first conjunct `x_gen = π·x_gen` contradicts `x_gen_ne_frobeniusIsog_pullback_x_gen`.
- **Uses from project**: `negFrobeniusIsog_pullback_x_gen`, `x_gen_ne_frobeniusIsog_pullback_x_gen`
- **Used by**: `addPullbackAlgHom_negFrobenius`, `isogOneSub_negFrobenius`
- **Visibility**: public
- **Lines**: 2689–2693, proof 5 lines

---

### `noncomputable def addPullbackAlgHom_negFrobenius`
- **Type**: `KE →ₐ[K] KE`, unconditional algebra hom for `id + (−π)`
- **What**: The unconditional `1−π` algebra hom, discharging both `AddNonInverse` and injectivity axiom-clean.
- **Uses from project**: `addPullbackAlgHom_negFrobenius_of_inj`, `negFrobeniusIsog_addNonInverse`, `addCoordAlgHom_injective_negFrobenius`
- **Used by**: `isogOneSub_negFrobenius`, `isogOneSub_negFrobenius_pullback`
- **Visibility**: public
- **Lines**: 2700–2705, definition

---

### `noncomputable def isogOneSub_negFrobenius`
- **Type**: `Isogeny W.toAffine W.toAffine`, the genuine `1−π` isogeny
- **What**: The mathematically correct `1−π` isogeny, replacing the placeholder.
- **Uses from project**: `addPullbackAlgHom_negFrobenius`, `frobeniusIsog`
- **Used by**: `isogOneSub_negFrobenius_pullback`, `isogOneSub_negFrobenius_toAddMonoidHom`
- **Visibility**: public
- **Lines**: 2723–2726, definition

---

### `@[simp] theorem isogOneSub_negFrobenius_pullback`
- **Type**: `(isogOneSub_negFrobenius W hq).pullback = addPullbackAlgHom_negFrobenius W hq`
- **Lines**: 2728–2730, proof `rfl`

---

### `@[simp] theorem isogOneSub_negFrobenius_toAddMonoidHom`
- **Type**: `(isogOneSub_negFrobenius W hq).toAddMonoidHom = AddMonoidHom.id _ - (frobeniusIsog W).toAddMonoidHom`
- **Lines**: 2732–2735, proof `rfl`

---

### `theorem AddNonInversePair_zsmul_one_frobenius_mulByInt_neg_one`
- **Type**: `AddNonInversePair ((frobeniusIsog W).zsmul 1) (mulByInt W (-1))`
- **What**: The `(r,s)=(1,1)` base case: the pair `(π, [-1])` is non-inverse.
- **How**: Reduces to `x_gen^q ≠ x_gen` via `x_gen_ne_frobeniusIsog_pullback_x_gen`.
- **Uses from project**: `AddNonInversePair_of_x_ne`, `mulByInt_x_one`, `mulByInt_x_neg`, `frobeniusIsog_pullback_apply`, `x_gen_ne_frobeniusIsog_pullback_x_gen`
- **Used by**: (unused in file directly)
- **Visibility**: public
- **Lines**: 2758–2780, proof 23 lines

---

### `theorem AddNonInversePair_zsmul_frobenius_mulByInt_neg`
- **Type**: For `r, s ≠ 0` with `(r:K) ≠ 0`, `(s:K) ≠ 0`: `AddNonInversePair ((frobeniusIsog W).zsmul r) (mulByInt W (-s))`
- **What**: General non-inverse condition for the pencil family via ord mismatch.
- **How**: The LHS `x`-pullback has order `-2q` vs RHS `-2`; they differ since `q ≥ 2`.
- **Uses from project**: `AddNonInversePair_of_x_ne`, `ordAtInfty_mulByInt_x`, `mulByInt_x_ne_zero`, `frobeniusIsog_pullback_apply`
- **Used by**: `ord_addPullback_y_pair_zsmul_frobenius_mulByInt_neg`
- **Visibility**: public
- **Lines**: 2794–2839, proof 46 lines
- **Notes**: Long proof (46 lines).

---

### `private theorem mulByInt_comp_mulByInt_neg_one`
- **Type**: `(mulByInt W n).comp (mulByInt W (-1)) = mulByInt W (-n)` for `n ≠ 0`
- **Lines**: 2853–2859

---

### `theorem sigma_mulByInt_pullback_x_eq`
- **Type**: `σ(([n].pb x_gen)) = [n].pb x_gen` for `n ≠ 0`
- **What**: σ fixes the x-pullback of any nonzero `[n]`.
- **How**: Composition path: `σ.pb([n].pb x_gen) = ([n]∘σ).pb x_gen = [-n].pb x_gen = mulByInt_x(-n) = mulByInt_x n` (via `mulByInt_x_neg`).
- **Uses from project**: `mulByInt_comp_mulByInt_neg_one`, `mulByInt_pullback_x`, `mulByInt_x_neg`
- **Used by**: `sigma_zsmul_frobenius_pullback_x_eq`, `addPullback_x_pair_zsmul_frobenius_mulByInt_neg_sigma_invariant`
- **Visibility**: public
- **Lines**: 2865–2875, proof 11 lines

---

### `theorem sigma_mulByInt_pullback_y_eq`
- **Type**: `σ(([n].pb y_gen)) = -[n].pb y_gen - a₁·[n].pb x_gen - a₃` for `n ≠ 0`
- **What**: σ sends `[n].pb y` to the curve-negation of itself.
- **How**: Same composition path for y; uses `mulByInt_y_neg` and unfolds `negY`.
- **Uses from project**: `mulByInt_comp_mulByInt_neg_one`, `mulByInt_pullback_y`, `mulByInt_x_neg`, `mulByInt_y_neg`
- **Used by**: `sigma_zsmul_frobenius_pullback_y_eq`, `addPullback_x_pair_zsmul_frobenius_mulByInt_neg_sigma_invariant`
- **Visibility**: public
- **Lines**: 2880–2912, proof 33 lines
- **Notes**: Long proof (33 lines).

---

### `theorem sigma_zsmul_frobenius_pullback_x_eq`
- **Type**: `σ(((zsmul r π).pb x_gen)) = (zsmul r π).pb x_gen` for `r ≠ 0`
- **What**: σ fixes the x-pullback of `rπ`.
- **How**: Uses `frobeniusIsog_pullback_universal_commute` to commute σ through π, then `sigma_mulByInt_pullback_x_eq`.
- **Uses from project**: `frobeniusIsog_pullback_universal_commute`, `sigma_mulByInt_pullback_x_eq`
- **Used by**: `addPullback_x_pair_zsmul_frobenius_mulByInt_neg_sigma_invariant`
- **Visibility**: public
- **Lines**: 2924–2941, proof 18 lines

---

### `theorem sigma_zsmul_frobenius_pullback_y_eq`
- **Type**: `σ((zsmul r π).pb y_gen) = -(zsmul r π).pb y_gen - a₁·(zsmul r π).pb x_gen - a₃` for `r ≠ 0`
- **What**: σ sends `rπ`'s y-pullback to the curve-negation.
- **How**: Same commutation via `frobeniusIsog_pullback_universal_commute`, then `sigma_mulByInt_pullback_y_eq`, distributing π.pb via `simp`.
- **Uses from project**: `frobeniusIsog_pullback_universal_commute`, `sigma_mulByInt_pullback_y_eq`
- **Used by**: `addPullback_x_pair_zsmul_frobenius_mulByInt_neg_sigma_invariant`
- **Visibility**: public
- **Lines**: 2947–2971, proof 25 lines

---

### `theorem zsmul_frobenius_pullback_x_ne_mulByInt_neg_pullback_x`
- **Type**: `(zsmul r π).pb x_gen ≠ (mulByInt -s).pb x_gen` for `r, s ≠ 0` with K-nonzero
- **What**: The x-coord mismatch witness: orders `-2q` vs `-2` differ.
- **How**: Same ord-mismatch argument as `AddNonInversePair_zsmul_frobenius_mulByInt_neg` but extracted as a standalone lemma.
- **Uses from project**: `ordAtInfty_mulByInt_x`, `mulByInt_x_ne_zero`, `frobeniusIsog_pullback_apply`
- **Used by**: `addPullback_x_pair_zsmul_frobenius_mulByInt_neg_sigma_invariant`
- **Visibility**: public
- **Lines**: 2983–3026, proof 44 lines
- **Notes**: Long proof (44 lines). Duplicates the core of `AddNonInversePair_zsmul_frobenius_mulByInt_neg`.

---

### `theorem addPullback_x_pair_zsmul_frobenius_mulByInt_neg_sigma_invariant`
- **Type**: `σ(addPullback_x_pair (zsmul r π) (mulByInt -s)) = addPullback_x_pair (zsmul r π) (mulByInt -s)`
- **What**: σ-invariance of the pair's x-pullback.
- **How**: Applies `addPullback_x_pair_sigma_invariant` with the four σ-symmetry lemmas.
- **Uses from project**: `addPullback_x_pair_sigma_invariant`, `zsmul_frobenius_pullback_x_ne_mulByInt_neg_pullback_x`, `sigma_zsmul_frobenius_pullback_x_eq`, `sigma_mulByInt_pullback_x_eq`, `sigma_zsmul_frobenius_pullback_y_eq`, `sigma_mulByInt_pullback_y_eq`
- **Used by**: `addPullback_x_pair_zsmul_frobenius_mulByInt_neg_in_KX_image`
- **Visibility**: public
- **Lines**: 3038–3050, proof 13 lines

---

### `theorem addPullback_x_pair_zsmul_frobenius_mulByInt_neg_in_KX_image`
- **Type**: `∃ a, addPullback_x_pair (zsmul r π) (mulByInt -s) = algebraMap a`
- **What**: The pair's x-pullback lies in K(x).
- **How**: `sigma_fixed_implies_in_KX_image` + σ-invariance.
- **Uses from project**: `sigma_fixed_implies_in_KX_image`, `addPullback_x_pair_zsmul_frobenius_mulByInt_neg_sigma_invariant`
- **Used by**: `addBaseHomPair_injective_zsmul_frobenius_mulByInt_neg_of_pole`
- **Visibility**: public
- **Lines**: 3055–3064, proof 4 lines

---

### `theorem ordAtInfty_zsmul_frobenius_pullback_x_gen`
- **Type**: `ord((zsmul r π).pb x_gen) = -2q` for `r ≠ 0`, `(r:K) ≠ 0`
- **What**: The x-pullback of `rπ` has order `-2q`.
- **How**: Identifies pullback as `(mulByInt_x r)^q`, applies `ordAtInfty_pow` and `ordAtInfty_mulByInt_x`.
- **Uses from project**: `frobeniusIsog_pullback_apply`, `ordAtInfty_pow`, `ordAtInfty_mulByInt_x`, `mulByInt_x_ne_zero`
- **Used by**: `ordAtInfty_zsmul_frobenius_sub_mulByInt_neg_x`, `ordAtInfty_addPullbackNumerator_reduced_pair_zsmul_frobenius_mulByInt_neg_eq`, `zsmul_frobenius_pullback_x_gen_ne_zero`
- **Visibility**: public
- **Lines**: 3076–3104, proof 29 lines

---

### `theorem ordAtInfty_mulByInt_neg_pullback_x_gen`
- **Type**: `ord((mulByInt -s).pb x_gen) = -2` for `s ≠ 0`, `(s:K) ≠ 0`
- **What**: The `[-s]` pullback of `x_gen` has order `-2`.
- **How**: Identifies pullback as `mulByInt_x(-s)` then `ordAtInfty_mulByInt_x`.
- **Uses from project**: `mulByInt_pullback_x`, `ordAtInfty_mulByInt_x`
- **Used by**: `ordAtInfty_zsmul_frobenius_sub_mulByInt_neg_x`, `ordAtInfty_addPullbackNumerator_reduced_pair_zsmul_frobenius_mulByInt_neg_eq`
- **Visibility**: public
- **Lines**: 3109–3120, proof 12 lines

---

### `theorem ordAtInfty_mulByInt_y_eq_of_x`
- **Type**: `ord(mulByInt_y W r) = (3M/2 : ℤ)` for `r ≠ 0`, `M = ord(mulByInt_x r) ≤ -2` even
- **What**: Generalised y-order for the inseparable case: `3M/2` from the Weierstrass equation.
- **How**: Curve equation for `(mulByInt_x, mulByInt_y)`; RHS has order `3M`; case analysis `m ≤ 3M/2` and `Y²` dominance force `2m = 3M`.
- **Hypotheses**: `r ≠ 0`, `M ≤ -2`, `M` even
- **Uses from project**: `pullback_equation`, `mulByInt_pullback_x`, `mulByInt_pullback_y`, `ord_add_ge_of_both_ge`, `ord_algebraMap_mul_ge`
- **Used by**: `ordAtInfty_zsmul_frobenius_pullback_y_gen_of_x`
- **Visibility**: public
- **Lines**: 3135–3306, proof ~171 lines
- **Notes**: **Longest proof in file** (~171 lines). Inseparable generalisation.

---

### `theorem ordAtInfty_mulByInt_y_eq_neg_three`
- **Type**: `ord(mulByInt_y W r) = -3` for `r ≠ 0`, `(r:K) ≠ 0`
- **What**: The y-coordinate of `[r]` has order `-3` (the separable case `M = -2`).
- **How**: Weierstrass equation argument: `ord(X) = -2` forces `ord(Y) = -3` via `2·ord(Y) = 3·ord(X)`.
- **Uses from project**: `ordAtInfty_mulByInt_x`, `mulByInt_x_ne_zero`, `pullback_equation`, `mulByInt_pullback_x`, `mulByInt_pullback_y`, `ord_add_ge_of_both_ge`, `ord_algebraMap_mul_ge`
- **Used by**: `ordAtInfty_zsmul_frobenius_pullback_y_gen`, `ordAtInfty_mulByInt_neg_pullback_y_gen`
- **Visibility**: public
- **Lines**: 3319–3506, proof ~187 lines
- **Notes**: **Very long proof** (~187 lines). Structurally similar to `ord_addPullback_y_negFrobenius`.

---

### `theorem ordAtInfty_zsmul_frobenius_pullback_y_gen`
- **Type**: `ord((zsmul r π).pb y_gen) = -3q` for `r ≠ 0`, `(r:K) ≠ 0`
- **How**: Identifies pullback as `(mulByInt_y r)^q`, then `ordAtInfty_pow` + `ordAtInfty_mulByInt_y_eq_neg_three`.
- **Uses from project**: `frobeniusIsog_pullback_apply`, `ordAtInfty_mulByInt_y_eq_neg_three`
- **Used by**: `ordAtInfty_zsmul_frobenius_sub_mulByInt_neg_y`, `ordAtInfty_addPullbackNumerator_reduced_pair_zsmul_frobenius_mulByInt_neg_eq`, `zsmul_frobenius_pullback_y_gen_ne_zero`
- **Visibility**: public
- **Lines**: 3510–3542, proof 33 lines

---

### `theorem ordAtInfty_mulByInt_neg_pullback_y_gen`
- **Type**: `ord((mulByInt -s).pb y_gen) = -3` for `s ≠ 0`, `(s:K) ≠ 0`
- **How**: Identifies as `mulByInt_y(-s)` then `ordAtInfty_mulByInt_y_eq_neg_three`.
- **Uses from project**: `mulByInt_pullback_y`, `ordAtInfty_mulByInt_y_eq_neg_three`
- **Used by**: `ordAtInfty_zsmul_frobenius_sub_mulByInt_neg_y`, `ordAtInfty_addPullbackNumerator_reduced_pair_zsmul_frobenius_mulByInt_neg_eq`
- **Visibility**: public
- **Lines**: 3547–3558, proof 12 lines

---

### `theorem ordAtInfty_zsmul_frobenius_pullback_x_gen_of_x`
- **Type**: `ord((zsmul r π).pb x_gen) = q·M` for `r ≠ 0`, `M = ord(mulByInt_x r)` (no K-nonzero)
- **What**: Inseparable x-pullback order.
- **Uses from project**: `frobeniusIsog_pullback_apply`, `ord_pow_concrete`, `mulByInt_x_ne_zero`
- **Used by**: `ordAtInfty_zsmul_frobenius_sub_mulByInt_neg_x_of_x`
- **Visibility**: public
- **Lines**: 3571–3588, proof 18 lines

---

### `theorem ordAtInfty_zsmul_frobenius_pullback_y_gen_of_x`
- **Type**: `ord((zsmul r π).pb y_gen) = q·(3M/2)` for `r ≠ 0`, `M ≤ -2` even (no K-nonzero)
- **What**: Inseparable y-pullback order.
- **Uses from project**: `frobeniusIsog_pullback_apply`, `ordAtInfty_mulByInt_y_eq_of_x`, `ord_pow_concrete`, `mulByInt_pullback_y`
- **Used by**: (unused in file currently; available for D4 inseparable)
- **Visibility**: public
- **Lines**: 3593–3618, proof 26 lines

---

### `theorem ordAtInfty_zsmul_frobenius_sub_mulByInt_neg_x`
- **Type**: `ord((zsmul r π).pb x − (mulByInt -s).pb x) = -2q` for separable `r, s`
- **How**: α₁ (ord `-2q`) dominates α₂ (ord `-2`) via `ord_sub_lt_concrete`.
- **Uses from project**: `ordAtInfty_zsmul_frobenius_pullback_x_gen`, `ordAtInfty_mulByInt_neg_pullback_x_gen`
- **Used by**: `zsmul_frobenius_sub_mulByInt_neg_x_ne_zero`, `ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg`
- **Visibility**: public
- **Lines**: 3628–3640, proof 13 lines

---

### `theorem ordAtInfty_zsmul_frobenius_sub_mulByInt_neg_y`
- **Type**: `ord((zsmul r π).pb y − (mulByInt -s).pb y) = -3q` for separable `r, s`
- **How**: α₁ (ord `-3q`) dominates α₂ (ord `-3`) via `ord_sub_lt_concrete`.
- **Uses from project**: `ordAtInfty_zsmul_frobenius_pullback_y_gen`, `ordAtInfty_mulByInt_neg_pullback_y_gen`
- **Used by**: (unused in file; available for pair numerator)
- **Visibility**: public
- **Lines**: 3644–3656, proof 13 lines

---

### `theorem zsmul_frobenius_sub_mulByInt_neg_x_ne_zero`
- **Type**: `(zsmul r π).pb x − (mulByInt -s).pb x ≠ 0` for separable
- **Uses from project**: `ordAtInfty_zsmul_frobenius_sub_mulByInt_neg_x`
- **Used by**: `addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg_eq`
- **Visibility**: public
- **Lines**: 3660–3671, proof 12 lines

---

### `noncomputable def addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg`
- **Type**: `KE` — numerator for the pair `(zsmul r π, mulByInt -s)`
- **Used by**: `addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg_eq_reduced`, `addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg_eq`, `ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg`
- **Visibility**: public
- **Lines**: 3682–3695, definition

---

### `noncomputable def addPullbackNumerator_reduced_pair_zsmul_frobenius_mulByInt_neg`
- **Type**: `KE` — Weierstrass-reduced 8-term form for the pair
- **Used by**: `addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg_eq_reduced`, `ordAtInfty_addPullbackNumerator_reduced_pair_zsmul_frobenius_mulByInt_neg_eq`, `ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg`
- **Visibility**: public
- **Lines**: 3700–3722, definition

---

### `theorem addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg_eq_reduced`
- **Type**: Weierstrass reduction identity for the pair numerator
- **How**: `pullback_equation` for both `zsmul r π` and `mulByInt -s`, then `linear_combination h_α₁ + h_α₂`.
- **Uses from project**: `pullback_equation`
- **Used by**: `ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg`
- **Visibility**: public
- **Lines**: 3728–3778, proof 51 lines
- **Notes**: Long proof (51 lines).

---

### `theorem addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg_eq`
- **Type**: `addPullbackNumerator_pair = d² · addPullback_x_pair`
- **How**: Slope formula + `field_simp; ring`. Mirror of prior numerator-eq lemmas.
- **Uses from project**: `zsmul_frobenius_sub_mulByInt_neg_x_ne_zero`
- **Used by**: `ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg`
- **Visibility**: public
- **Lines**: 3784–3824, proof 41 lines
- **Notes**: Long proof (41 lines).

---

*(Private lemmas `zsmul_frobenius_pullback_y_gen_ne_zero`, `zsmul_frobenius_pullback_x_gen_ne_zero`, `mulByInt_neg_pullback_y_gen_ne_zero`, `mulByInt_neg_pullback_x_gen_ne_zero` at lines 3834–3875 are nonzero witnesses derived from finite-ord arguments.)*

---

### `theorem ordAtInfty_addPullbackNumerator_reduced_pair_zsmul_frobenius_mulByInt_neg_eq`
- **Type**: `ord(reduced_pair) = -4q - 2` for separable `r, s`, `q ≥ 2`
- **What**: Dominant term `α₁(x)²·α₂(x)` (order `-4q-2`) beats all 7 rest terms (order `≥ -3q-3`).
- **How**: Seven term-bound proofs + algebraic identity + `ordAtInfty_add_eq_of_lt`.
- **Uses from project**: `ord_algebraMap_mul_ge`, `ord_two_mul_ge`, `ord_add_ge_of_both_ge`, `ord_sub_ge_of_both_ge`, `ordAtInfty_zsmul_frobenius_pullback_x_gen`, `ordAtInfty_mulByInt_neg_pullback_x_gen`, `ordAtInfty_zsmul_frobenius_pullback_y_gen`, `ordAtInfty_mulByInt_neg_pullback_y_gen`
- **Visibility**: public
- **Lines**: 3881–4081, proof ~200 lines
- **Notes**: **Longest proof in file** (~200 lines).

---

### `theorem ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg`
- **Type**: `ord(addPullback_x_pair (zsmul r π) (mulByInt -s)) = -2` for separable `r, s`, `q ≥ 2`
- **What**: **Key theorem**: the pair's x-pullback has a simple pole of order `-2`.
- **How**: Numerator eq + reduced ord `-4q-2`; denominator ord `-4q`; division gives `-2`.
- **Uses from project**: `zsmul_frobenius_sub_mulByInt_neg_x_ne_zero`, `ordAtInfty_zsmul_frobenius_sub_mulByInt_neg_x`, `addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg_eq_reduced`, `ordAtInfty_addPullbackNumerator_reduced_pair_zsmul_frobenius_mulByInt_neg_eq`, `addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg_eq`
- **Used by**: `h_pole_discharge`, `ord_addPullback_y_pair_zsmul_frobenius_mulByInt_neg`
- **Visibility**: public
- **Lines**: 4091–4124, proof 34 lines
- **Notes**: Long proof (34 lines).

---

*(Private helpers `ord_addPullback_x_sq_pair_...`, `ord_addPullback_x_cube_pair_...`, `ord_RHS_pair_...` at lines 4136–4211 compute `ord(X²) = -4`, `ord(X³) = -6`, and `ord(RHS) = -6` for the pair.)*

---

### `theorem ord_addPullback_y_pair_zsmul_frobenius_mulByInt_neg`
- **Type**: `ord(addPullback_y_pair (zsmul r π) (mulByInt -s)) = -3` for separable `r, s`, `q ≥ 2`
- **What**: The y-coordinate of the pair addition-pullback has order `-3`.
- **How**: Same Weierstrass equation case analysis as `ord_addPullback_y_negFrobenius`.
- **Uses from project**: `ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg`, `addPullback_pair_equation`, `AddNonInversePair_zsmul_frobenius_mulByInt_neg`, `ord_RHS_pair_zsmul_frobenius_mulByInt_neg`, `ord_algebraMap_mul_ge`, `ord_add_ge_of_both_ge`
- **Used by**: (unused in file; available for downstream)
- **Visibility**: public
- **Lines**: 4218–4311, proof ~93 lines
- **Notes**: Long proof (~93 lines).

---

### `theorem addBaseHomPair_injective_zsmul_frobenius_mulByInt_neg_of_pole`
- **Type**: Given pole bound `ord < 0`: `Function.Injective (addBaseHomPair (zsmul r π) (mulByInt -s))`
- **What**: Witness-parametric base-hom injectivity for the pair.
- **How**: Transcendence argument via K(x)-image + `algebraic_in_fracRing_eq_const`; the pole rules out the constant case.
- **Uses from project**: `addBaseHomPair_eq_aeval`, `transcendental_iff_injective`, `addPullback_x_pair_zsmul_frobenius_mulByInt_neg_in_KX_image`, `algebraic_in_fracRing_eq_const`, `ordAtInfty_algebraMap_F_nonzero`
- **Used by**: `addCoordAlgHomPair_injective_zsmul_frobenius_mulByInt_neg_of_pole`
- **Visibility**: public
- **Lines**: 4333–4375, proof 43 lines
- **Notes**: Long proof (43 lines).

---

### `theorem addCoordAlgHomPair_injective_zsmul_frobenius_mulByInt_neg_of_pole`
- **Type**: Given pole bound: `Function.Injective (addCoordAlgHomPair hxy)`
- **How**: `addCoordAlgHomPair_injective_of_baseHom_inj` + base-hom injectivity.
- **Uses from project**: `addCoordAlgHomPair_injective_of_baseHom_inj`, `addBaseHomPair_injective_zsmul_frobenius_mulByInt_neg_of_pole`, `AddNonInversePair_zsmul_frobenius_mulByInt_neg`
- **Used by**: `genuineIsogSmulSub_of_pole`
- **Visibility**: public
- **Lines**: 4380–4391, proof 12 lines

---

### `noncomputable def genuineIsogSmulSub_of_pole`
- **Type**: `Isogeny W.toAffine W.toAffine`, the genuine `rπ − s·id` isogeny (pole-bound-parametric)
- **What**: The genuine `rπ − s` isogeny with the real function-field pullback.
- **Uses from project**: `addIsog`, `AddNonInversePair_zsmul_frobenius_mulByInt_neg`, `addCoordAlgHomPair_injective_zsmul_frobenius_mulByInt_neg_of_pole`
- **Used by**: `genuineIsogSmulSub`
- **Visibility**: public
- **Lines**: 4404–4414, definition

---

### `@[simp] theorem genuineIsogSmulSub_of_pole_toAddMonoidHom`
- **Type**: The toAddMonoidHom of `genuineIsogSmulSub_of_pole` equals the sum
- **Lines**: 4416–4425, proof `rfl`

---

### `private theorem h_pole_discharge`
- **Type**: For separable `r, s`: `ord(addPullback_x_pair ...) < 0`
- **How**: `ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg` gives `-2 < 0`.
- **Lines**: 4436–4443

---

### `noncomputable def genuineIsogSmulSub`
- **Type**: `Isogeny W.toAffine W.toAffine`, unconditional `rπ − s·id`
- **What**: **D4 unconditional**: the genuine `rπ − s` isogeny, axiom-clean.
- **Uses from project**: `genuineIsogSmulSub_of_pole`, `h_pole_discharge`
- **Used by**: `genuineIsogSmulSub_toAddMonoidHom`
- **Visibility**: public
- **Lines**: 4450–4455, definition

---

### `@[simp] theorem genuineIsogSmulSub_toAddMonoidHom`
- **Type**: `(genuineIsogSmulSub W r s hr hs hrK hsK).toAddMonoidHom = (zsmul r π).toAddMonoidHom + (mulByInt -s).toAddMonoidHom`
- **Lines**: 4457–4463, proof `rfl`

---

### `theorem ordAtInfty_zsmul_frobenius_sub_mulByInt_neg_x_of_x`
- **Type**: `ord(α₁.pb x − α₂.pb x) = q·M` for inseparable `r` with `M = ord(mulByInt_x r) ≤ -2`
- **What**: The inseparable x-difference order.
- **How**: `α₁.pb x` (order `q·M ≤ -4`) dominates `α₂.pb x` (order `-2`).
- **Uses from project**: `ordAtInfty_zsmul_frobenius_pullback_x_gen_of_x`, `ordAtInfty_mulByInt_neg_pullback_x_gen`
- **Used by**: `zsmul_frobenius_sub_mulByInt_neg_x_ne_zero_of_x`
- **Visibility**: public
- **Lines**: 4480–4492, proof 13 lines

---

### `theorem zsmul_frobenius_sub_mulByInt_neg_x_ne_zero_of_x`
- **Type**: `(zsmul r π).pb x − (mulByInt -s).pb x ≠ 0` for inseparable
- **Uses from project**: `ordAtInfty_zsmul_frobenius_sub_mulByInt_neg_x_of_x`
- **Visibility**: public
- **Lines**: 4495–4506, proof 12 lines

---

### `theorem AddNonInversePair_zsmul_frobenius_mulByInt_neg_of_x`
- **Type**: `AddNonInversePair (zsmul r π) (mulByInt -s)` for inseparable
- **How**: `AddNonInversePair_of_x_ne` + `zsmul_frobenius_sub_mulByInt_neg_x_ne_zero_of_x`.
- **Visibility**: public
- **Lines**: 4511–4516, proof 3 lines

---

### `theorem addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg_eq_of_hd_ne`
- **Type**: `addPullbackNumerator_pair = d² · addPullback_x_pair` (parametric on `hd_ne`)
- **What**: Numerator-clearing identity for the inseparable case, body-identical to the separable version but taking `hd_ne` directly.
- **Uses from project**: `addSlopePair`, `addPullback_x_pair`
- **Visibility**: public
- **Lines**: 4522–4561, proof 40 lines
- **Notes**: Long proof (40 lines). Slight duplication of `addPullbackNumerator_pair_zsmul_frobenius_mulByInt_neg_eq`.

---

## Summary

| Category | Count |
|----------|-------|
| `theorem` / `lemma` | ~110 |
| `noncomputable def` | ~12 |
| `instance` | 0 |
| `abbrev` | 0 |
| Total | ~122 |

No `set_option maxHeartbeats` directives appear in the file. No `sorry` terms appear. No instances defined.

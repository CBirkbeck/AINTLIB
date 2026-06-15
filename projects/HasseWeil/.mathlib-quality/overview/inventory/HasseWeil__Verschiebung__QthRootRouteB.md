# Inventory: ./HasseWeil/Verschiebung/QthRootRouteB.lean

**Total declarations**: 22 (all theorems, no defs/instances)
**Sorries**: none
**set_option maxHeartbeats**: none

## Summary

This file discharges the universal q-th-root witness
`∀ z : K(E), ∃ g, g^q = [q]*z`
and from it derives `verschiebung_isDualOf_frobenius_general`, the GAP-QF keystone
(Verschiebung is the dual of Frobenius over any finite field). The strategy is
characteristic-uniform: it uses Kähler differentials + separability of `K(E)/K(x_gen)`,
not per-prime polynomial witnesses.

Imports: `HasseWeil.Verschiebung.Cascade`, `HasseWeil.Verschiebung.Route2Universal`,
`HasseWeil.GapQfKernel`.

---

### `theorem mem_fractionRing_range_of_pow_mem`

- **Type**: `(p : ℕ) [Fact p.Prime] [CharP K p] (g : K(E)) → g^p ∈ (algebraMap Mff K(E)).range → g ∈ (algebraMap Mff K(E)).range`  
  where `Mff = FractionRing (Polynomial K)`.
- **What**: Separable-root descent: if a `p`-th power lies in the image of `FractionRing K[X] → K(E)`, so does its `p`-th root.
- **How**: Uses `functionField_isSeparable` to get `IsSeparable Mff g`; then `minpoly.natSepDegree_eq_one_iff_pow_mem p` gives `natSepDegree = 1`; `Polynomial.Separable.natSepDegree_eq_natDegree` upgrades to `natDegree = 1`; `minpoly.mem_range_of_degree_eq_one` concludes.
- **Hypotheses**: `p` prime, `K` has characteristic `p`.
- **Uses from project**: `functionField_isSeparable`
- **Used by**: `mulByInt_p_pullback_x_gen_mem_adjoin_pow_routeB`
- **Visibility**: public
- **Lines**: 82–102; proof ~21 lines
- **Notes**: None

---

### `theorem algebraMap_polynomial_eq_fractionRing`

- **Type**: `(q : Polynomial K) → algebraMap (Polynomial K) K(E) q = algebraMap Mff K(E) (algebraMap (Polynomial K) Mff q)`
- **What**: Scalar-tower factoring: the structure map `K[X] → K(E)` factors through `Mff = FractionRing K[X]`.
- **How**: Uses `functionField_isScalarTower` and `IsScalarTower.algebraMap_apply`.
- **Hypotheses**: None beyond the ambient hypotheses on `W`.
- **Uses from project**: `functionField_isScalarTower`
- **Used by**: `x_gen_mem_fractionRing_range`, `mem_adjoin_x_gen_of_mem_fractionRing_range`, `mulByInt_x_mem_fractionRing_range`
- **Visibility**: public
- **Lines**: 108–112; proof ~5 lines
- **Notes**: key API (used by 3 other declarations)

---

### `theorem x_gen_mem_fractionRing_range`

- **Type**: `x_gen W ∈ (algebraMap Mff K(E)).range`
- **What**: The x-coordinate generator lies in the image of `FractionRing K[X] → K(E)` (it is the image of `X`).
- **How**: Exhibits the preimage `algebraMap K[X] Mff Polynomial.X` and rewrites via `algebraMap_polynomial_eq_fractionRing`.
- **Hypotheses**: None beyond ambient.
- **Uses from project**: `algebraMap_polynomial_eq_fractionRing`, `x_gen`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 115–119; proof ~5 lines
- **Notes**: Declared but not called anywhere else in this file; may be used by external callers.

---

### `theorem algebraMap_polynomial_mem_adjoin_x_gen`

- **Type**: `(q : Polynomial K) → algebraMap (Polynomial K) K(E) q ∈ IntermediateField.adjoin K {x_gen W}`
- **What**: Every polynomial in `K[X]`, mapped to `K(E)` via the structure map, lands in `K⟮x_gen⟯`.
- **How**: Polynomial induction via `Polynomial.induction_on`; the base cases use `IntermediateField.algebraMap_mem` and `IntermediateField.subset_adjoin`; the monomial case uses `map_mul`, `map_pow`, and `hXgen : algebraMap K[X] K(E) X = x_gen W`.
- **Hypotheses**: None beyond ambient.
- **Uses from project**: `x_gen`
- **Used by**: `mem_adjoin_x_gen_of_mem_fractionRing_range`
- **Visibility**: public
- **Lines**: 123–139; proof ~17 lines
- **Notes**: None

---

### `theorem mem_adjoin_x_gen_of_mem_fractionRing_range`

- **Type**: `{g : K(E)} → g ∈ (algebraMap Mff K(E)).range → g ∈ IntermediateField.adjoin K {x_gen W}`
- **What**: Image of `FractionRing K[X] → K(E)` is contained in `K⟮x_gen⟯`.
- **How**: Unfolds the image using `IsFractionRing.div_surjective`; rewrites via `algebraMap_polynomial_eq_fractionRing`; applies `algebraMap_polynomial_mem_adjoin_x_gen` to numerator and denominator.
- **Hypotheses**: None beyond ambient.
- **Uses from project**: `algebraMap_polynomial_eq_fractionRing`, `algebraMap_polynomial_mem_adjoin_x_gen`
- **Used by**: `mulByInt_p_pullback_x_gen_mem_adjoin_pow_routeB`
- **Visibility**: public
- **Lines**: 143–150; proof ~8 lines
- **Notes**: None

---

### `theorem mulByInt_x_mem_fractionRing_range`

- **Type**: `(n : ℤ) → mulByInt_x W n ∈ (algebraMap Mff K(E)).range`
- **What**: The x-coordinate `[n]* x_gen = Φ_ff W n / ΨSq_ff W n` lies in `Im(Mff → K(E))`.
- **How**: Exhibits `Φ_ff W n` and `ΨSq_ff W n` each in the image via `algebraMap_polynomial_eq_fractionRing`; constructs the quotient preimage.
- **Hypotheses**: None beyond ambient.
- **Uses from project**: `Φ_ff`, `ΨSq_ff`, `mulByInt_x`, `algebraMap_polynomial_eq_fractionRing`
- **Used by**: `mulByInt_p_pullback_x_gen_mem_adjoin_pow_routeB`
- **Visibility**: public
- **Lines**: 156–166; proof ~11 lines
- **Notes**: None

---

### `theorem mulByInt_p_pullback_x_gen_mem_adjoin_pow_routeB`

- **Type**: `(p : ℕ) [Fact p.Prime] [CharP K p] → (mulByInt W.toAffine (p : ℤ)).pullback (x_gen W) ∈ IntermediateField.adjoin K {x_gen W ^ p}`
- **What**: x-side base (general characteristic): `[p]* x_gen ∈ K⟮x_gen^p⟯`.
- **How**: Uses `D_mulByInt_p_pullback_x_gen_eq_zero` to get `D([p]*x_gen) = 0`; then `kaehlerD_eq_zero_iff_mem_pth_powers` yields a `p`-th root `g`; `mulByInt_pullback_x` identifies `[p]*x_gen` with `mulByInt_x W p`; `mulByInt_x_mem_fractionRing_range` places `[p]*x_gen` in `Im(Mff)`; `mem_fractionRing_range_of_pow_mem` gives `g ∈ Im(Mff) ⊆ K⟮x_gen⟯` (via `mem_adjoin_x_gen_of_mem_fractionRing_range`); finally `adjoin_simple_pow_le_adjoin_simple_pow` concludes `g^p ∈ K⟮x_gen^p⟯`.
- **Hypotheses**: `p` prime, `K` has characteristic `p`.
- **Uses from project**: `D_mulByInt_p_pullback_x_gen_eq_zero`, `kaehlerD_eq_zero_iff_mem_pth_powers`, `mulByInt_pullback_x`, `mulByInt_x_mem_fractionRing_range`, `mem_fractionRing_range_of_pow_mem`, `mem_adjoin_x_gen_of_mem_fractionRing_range`, `adjoin_simple_pow_le_adjoin_simple_pow`, `x_gen`
- **Used by**: `mulByInt_pow_pullback_x_gen_mem_adjoin_pow_routeB`, `mulByInt_pow_pullback_y_gen_mem_adjoin_pair_pow`
- **Visibility**: public
- **Lines**: 173–195; proof ~23 lines
- **Notes**: None

---

### `theorem mulByInt_pow_pullback_x_gen_mem_adjoin_pow_routeB`

- **Type**: `(p : ℕ) [Fact p.Prime] [CharP K p] → ∀ k, (mulByInt W.toAffine ((p^k : ℕ) : ℤ)).pullback (x_gen W) ∈ IntermediateField.adjoin K {x_gen W ^ (p^k : ℕ)}`
- **What**: x-side for all powers: `[p^k]* x_gen ∈ K⟮x_gen^(p^k)⟯` for every `k`.
- **How**: Induction on `k`. Base case via `mulByInt_pow_zero_pullback_x_gen_mem_adjoin_pow`. Inductive step: decomposes `[p^(k+1)] = [p^k] ∘ [p]` using `mulByInt_comp_eq_mul`; pushes the IH through `[p]*` via `IntermediateField.adjoin_map`; applies `mulByInt_p_pullback_x_gen_mem_adjoin_pow_routeB` for the base, then `adjoin_simple_pow_pow_le_adjoin_simple_pow_pow` for iterated powering; closes with `IntermediateField.adjoin_le_iff`.
- **Hypotheses**: `p` prime, `K` has characteristic `p`.
- **Uses from project**: `mulByInt_pow_zero_pullback_x_gen_mem_adjoin_pow`, `mulByInt_comp_eq_mul`, `mulByInt_p_pullback_x_gen_mem_adjoin_pow_routeB`, `adjoin_simple_pow_pow_le_adjoin_simple_pow_pow`, `x_gen`
- **Used by**: `mulByInt_card_pullback_x_gen_mem_adjoin_pow_card_routeB`
- **Visibility**: public
- **Lines**: 202–244; proof ~40 lines
- **Notes**: Proof > 30 lines.

---

### `theorem mulByInt_card_pullback_x_gen_mem_adjoin_pow_card_routeB`

- **Type**: `(p : ℕ) [Fact p.Prime] [CharP K p] → (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (x_gen W) ∈ IntermediateField.adjoin K {x_gen W ^ (Fintype.card K : ℕ)}`
- **What**: x-side at `q = #K`: `[q]* x_gen ∈ K⟮x_gen^q⟯`. Specialises `mulByInt_pow_pullback_x_gen_mem_adjoin_pow_routeB` at the exponent `k = n` where `#K = p^n`.
- **How**: Uses `FiniteField.card K p` to get `#K = p^n`; rewrites; applies `mulByInt_pow_pullback_x_gen_mem_adjoin_pow_routeB W p n`.
- **Hypotheses**: `p` prime, `K` has characteristic `p`.
- **Uses from project**: `mulByInt_pow_pullback_x_gen_mem_adjoin_pow_routeB`, `x_gen`
- **Used by**: `mulByInt_card_pullback_x_gen_mem_frobenius`
- **Visibility**: public
- **Lines**: 249–255; proof ~7 lines
- **Notes**: None

---

### `theorem adjoin_pow_card_x_gen_le_frobenius`

- **Type**: `IntermediateField.adjoin K {x_gen W ^ (Fintype.card K : ℕ)} ≤ frobeniusIsog_intermediateField W`
- **What**: The simple adjoin `K⟮x_gen^q⟯` is contained in the Frobenius intermediate field `K(E)^q = Im(π*)`.
- **How**: `IntermediateField.adjoin_le_iff` + `pow_card_mem_frobeniusIsog_intermediateField`.
- **Hypotheses**: None beyond ambient.
- **Uses from project**: `frobeniusIsog_intermediateField`, `pow_card_mem_frobeniusIsog_intermediateField`, `x_gen`
- **Used by**: `mulByInt_card_pullback_x_gen_mem_frobenius`
- **Visibility**: public
- **Lines**: 260–264; proof ~5 lines (term-mode)
- **Notes**: None

---

### `theorem mulByInt_card_pullback_x_gen_mem_frobenius`

- **Type**: `(p : ℕ) [Fact p.Prime] [CharP K p] → (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (x_gen W) ∈ frobeniusIsog_intermediateField W`
- **What**: x-side conclusion: `[q]* x_gen ∈ Im(π*) = K(E)^q`.
- **How**: Composes `adjoin_pow_card_x_gen_le_frobenius` with `mulByInt_card_pullback_x_gen_mem_adjoin_pow_card_routeB`.
- **Hypotheses**: `p` prime, `K` has characteristic `p`.
- **Uses from project**: `adjoin_pow_card_x_gen_le_frobenius`, `mulByInt_card_pullback_x_gen_mem_adjoin_pow_card_routeB`
- **Used by**: `qth_root_witness_of_charP`
- **Visibility**: public
- **Lines**: 267–272; proof ~6 lines
- **Notes**: None

---

### `theorem mulByInt_pullback_y_gen_weierstrass`

- **Type**: `(n : ℤ) → ([n]* y_gen)^2 + (a₁·[n]* x_gen + a₃)·[n]* y_gen = ([n]* x_gen)^3 + a₂·([n]* x_gen)^2 + a₄·[n]* x_gen + a₆`
- **What**: The Weierstrass quadratic equation for `y_gen` holds after applying the K-algebra hom `[n]*`.
- **How**: Applies `generic_equation W` (the generic Weierstrass equation), rewrites the a-coefficients, then uses `congrArg (mulByInt …).pullback` + `simp [AlgHom.commutes]` + `linear_combination`.
- **Hypotheses**: None beyond ambient.
- **Uses from project**: `generic_equation`, `y_gen`, `x_gen`
- **Used by**: `D_mulByInt_p_pullback_y_gen_eq_zero`
- **Visibility**: public
- **Lines**: 285–305; proof ~21 lines
- **Notes**: None

---

### `theorem kaehlerD_eq_zero_of_weierstrass_quadratic`

- **Type**: `(X Y : K(E)) → D X = 0 → Y² + (a₁X+a₃)Y = X³+a₂X²+a₄X+a₆ → 2Y + a₁X+a₃ ≠ 0 → D Y = 0`
- **What**: If `D(X) = 0` and `Y` is a root of the Weierstrass quadratic with non-zero discriminant `2Y+a₁X+a₃`, then `D(Y) = 0`. This is the Leibniz/derivation core for the y-side differential vanishing.
- **How**: Computes `D(Y²+βY)` by Leibniz rule (`Derivation.leibniz`, `Derivation.leibniz_pow`, `Derivation.map_algebraMap`) to get `(2Y+β)·D(Y)`; uses the Weierstrass equation + `D(X)=0` to show the LHS is 0; divides by `2Y+β ≠ 0` via `smul_eq_zero.mp`.
- **Hypotheses**: `D X = 0`, `Y` satisfies the Weierstrass quadratic, `2Y + a₁X + a₃ ≠ 0`.
- **Uses from project**: none (purely abstract)
- **Used by**: `D_mulByInt_p_pullback_y_gen_eq_zero`
- **Visibility**: public
- **Lines**: 310–333; proof ~24 lines
- **Notes**: Abstract utility lemma with no project-specific dependencies; could potentially be extracted to a general-purpose file.

---

### `theorem D_mulByInt_p_pullback_y_gen_eq_zero`

- **Type**: `(p : ℕ) [Fact p.Prime] [CharP K p] → KaehlerDifferential.D K K(E) ([p]* y_gen) = 0`
- **What**: The Kähler differential of `[p]* y_gen` vanishes.
- **How**: Applies `kaehlerD_eq_zero_of_weierstrass_quadratic` with `X := [p]*x_gen` (whose differential is zero by `D_mulByInt_p_pullback_x_gen_eq_zero`) and the Weierstrass equation from `mulByInt_pullback_y_gen_weierstrass`; the non-vanishing condition `2Y+β ≠ 0` is established by identifying `2Y+β = [p]* u_gen` via `alpha_star_u_eq` and using `u_gen_ne_zero` + injectivity of `[p]*`.
- **Hypotheses**: `p` prime, `K` has characteristic `p`.
- **Uses from project**: `kaehlerD_eq_zero_of_weierstrass_quadratic`, `D_mulByInt_p_pullback_x_gen_eq_zero`, `mulByInt_pullback_y_gen_weierstrass`, `alpha_star_u`, `alpha_star_u_eq`, `u_gen_ne_zero`
- **Used by**: `mulByInt_p_pullback_y_gen_mem_adjoin_pair_pow`
- **Visibility**: public
- **Lines**: 335–349; proof ~15 lines
- **Notes**: None

---

### `theorem adjoin_pair_pow_le_adjoin_pair_pow`

- **Type**: `{L : Type*} [Field L] [Algebra K L] (p : ℕ) [Fact p.Prime] [CharP L p] (a b z : L) → z ∈ adjoin K {a, b} → z^p ∈ adjoin K {a^p, b^p}`
- **What**: In characteristic `p`, `z ∈ K⟮a, b⟯` implies `z^p ∈ K⟮a^p, b^p⟯`. Two-generator analogue of `adjoin_simple_pow_le_adjoin_simple_pow`.
- **How**: Induction via `IntermediateField.adjoin_induction`; generator cases use `subset_adjoin`; field operations use `add_pow_expChar` (Frobenius endomorphism), `mul_pow`, `inv_pow`, `map_pow`.
- **Hypotheses**: `L/K` a field extension in characteristic `p` (prime).
- **Uses from project**: none (generic intermediate-field lemma)
- **Used by**: `adjoin_pair_pow_pow_le_adjoin_pair_pow_pow`, `mulByInt_p_pullback_y_gen_mem_adjoin_pair_pow`
- **Visibility**: public
- **Lines**: 361–373; proof ~13 lines
- **Notes**: Generic utility; no project-specific imports; potential mathlib candidate.

---

### `theorem adjoin_pair_pow_pow_le_adjoin_pair_pow_pow`

- **Type**: `{L : Type*} [Field L] [Algebra K L] (p : ℕ) [Fact p.Prime] [CharP L p] (a b : L) (n : ℕ) (z : L) → z ∈ adjoin K {a, b} → z^(p^n) ∈ adjoin K {a^(p^n), b^(p^n)}`
- **What**: Iterated version: `z ∈ K⟮a, b⟯ → z^(p^n) ∈ K⟮a^(p^n), b^(p^n)⟯`.
- **How**: Induction on `n`; base is trivial; inductive step applies `adjoin_pair_pow_le_adjoin_pair_pow`.
- **Hypotheses**: Same as `adjoin_pair_pow_le_adjoin_pair_pow`.
- **Uses from project**: `adjoin_pair_pow_le_adjoin_pair_pow`
- **Used by**: `mulByInt_pow_pullback_y_gen_mem_adjoin_pair_pow`
- **Visibility**: public
- **Lines**: 377–385; proof ~9 lines
- **Notes**: None

---

### `theorem mulByInt_p_pullback_y_gen_mem_adjoin_pair_pow`

- **Type**: `(p : ℕ) [Fact p.Prime] [CharP K p] → (mulByInt W.toAffine (p : ℤ)).pullback (y_gen W) ∈ adjoin K {x_gen W ^ p, y_gen W ^ p}`
- **What**: y-side base: `[p]* y_gen ∈ K⟮x_gen^p, y_gen^p⟯`.
- **How**: Uses `D_mulByInt_p_pullback_y_gen_eq_zero` + `kaehlerD_eq_zero_iff_mem_pth_powers` to get a `p`-th root `h`; uses `functionField_eq_intermediateField_adjoin_xy` to see `h ∈ K⟮x_gen, y_gen⟯`; then applies `adjoin_pair_pow_le_adjoin_pair_pow`.
- **Hypotheses**: `p` prime, `K` has characteristic `p`.
- **Uses from project**: `D_mulByInt_p_pullback_y_gen_eq_zero`, `kaehlerD_eq_zero_iff_mem_pth_powers`, `functionField_eq_intermediateField_adjoin_xy`, `adjoin_pair_pow_le_adjoin_pair_pow`, `x_gen`, `y_gen`
- **Used by**: `mulByInt_pow_pullback_y_gen_mem_adjoin_pair_pow`
- **Visibility**: public
- **Lines**: 390–400; proof ~11 lines
- **Notes**: None

---

### `theorem mulByInt_pow_pullback_y_gen_mem_adjoin_pair_pow`

- **Type**: `(p : ℕ) [Fact p.Prime] [CharP K p] → ∀ k, (mulByInt W.toAffine ((p^k : ℕ) : ℤ)).pullback (y_gen W) ∈ adjoin K {x_gen W ^ (p^k : ℕ), y_gen W ^ (p^k : ℕ)}`
- **What**: y-side for all powers: `[p^k]* y_gen ∈ K⟮x_gen^(p^k), y_gen^(p^k)⟯` for every `k`.
- **How**: Induction on `k`. Base: `[1]*y_gen = y_gen ∈ K⟮x_gen^1, y_gen^1⟯`. Inductive step: decomposes `[p^(k+1)] = [p^k] ∘ [p]` using `mulByInt_comp_eq_mul`; pushes the IH through `[p]*` via `IntermediateField.adjoin_map`; for the x-generator case uses `mulByInt_p_pullback_x_gen_mem_adjoin_pow_routeB` + `adjoin_pair_pow_pow_le_adjoin_pair_pow_pow`; for the y-generator case uses `mulByInt_p_pullback_y_gen_mem_adjoin_pair_pow` + `adjoin_pair_pow_pow_le_adjoin_pair_pow_pow`; finishes with `IntermediateField.adjoin_le_iff`.
- **Hypotheses**: `p` prime, `K` has characteristic `p`.
- **Uses from project**: `mulByInt_comp_eq_mul`, `mulByInt_p_pullback_x_gen_mem_adjoin_pow_routeB`, `mulByInt_p_pullback_y_gen_mem_adjoin_pair_pow`, `adjoin_pair_pow_pow_le_adjoin_pair_pow_pow`, `mulByInt_one_pullback_eq_id`, `x_gen`, `y_gen`
- **Used by**: `mulByInt_card_pullback_y_gen_mem_frobenius`
- **Visibility**: public
- **Lines**: 407–467; proof ~58 lines
- **Notes**: Proof > 30 lines. The longest proof in the file; mirrors the x-side induction but requires two generator cases.

---

### `theorem mulByInt_card_pullback_y_gen_mem_frobenius`

- **Type**: `(p : ℕ) [Fact p.Prime] [CharP K p] → (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (y_gen W) ∈ frobeniusIsog_intermediateField W`
- **What**: y-side conclusion: `[q]* y_gen ∈ Im(π*) = K(E)^q`.
- **How**: Specialises `mulByInt_pow_pullback_y_gen_mem_adjoin_pair_pow` at `k = n` (`#K = p^n`); uses `pow_card_mem_frobeniusIsog_intermediateField` for both `x_gen` and `y_gen` to verify the adjoin bounds.
- **Hypotheses**: `p` prime, `K` has characteristic `p`.
- **Uses from project**: `mulByInt_pow_pullback_y_gen_mem_adjoin_pair_pow`, `pow_card_mem_frobeniusIsog_intermediateField`, `frobeniusIsog_intermediateField`, `x_gen`, `y_gen`
- **Used by**: `qth_root_witness_of_charP`
- **Visibility**: public
- **Lines**: 471–483; proof ~13 lines
- **Notes**: None

---

### `theorem qth_root_witness_of_charP`

- **Type**: `(p : ℕ) [Fact p.Prime] [CharP K p] → ∀ z : K(E), ∃ g : K(E), g ^ Fintype.card K = (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z`
- **What**: Universal q-th-root witness in characteristic `p`: every `[q]*z` is a `q`-th power in `K(E)`.
- **How**: Converts the generator memberships `[q]* x_gen, [q]* y_gen ∈ Im(π*)` to `fieldRange` form via `frobeniusIsog_intermediateField_eq_fieldRange`; invokes `mulByInt_q_pullback_fieldRange_subset_frobenius_of_xy_witness` (uses `functionField_eq_intermediateField_adjoin_xy`) to extend to all `z`; then uses `mem_frobenius_range_iff` to extract the `q`-th root.
- **Hypotheses**: `p` prime, `K` has characteristic `p`.
- **Uses from project**: `mulByInt_card_pullback_x_gen_mem_frobenius`, `mulByInt_card_pullback_y_gen_mem_frobenius`, `frobeniusIsog_intermediateField_eq_fieldRange`, `mulByInt_q_pullback_fieldRange_subset_frobenius_of_xy_witness`, `functionField_eq_intermediateField_adjoin_xy`, `mem_frobenius_range_iff`, `frobeniusIsog`
- **Used by**: `qth_root_witness_general`
- **Visibility**: public
- **Lines**: 491–509; proof ~19 lines
- **Notes**: None

---

### `theorem qth_root_witness_general`

- **Type**: `∀ z : K(E), ∃ g : K(E), g ^ Fintype.card K = (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z`
- **What**: Universal q-th-root witness without any characteristic hypothesis: works over any finite field by internally extracting the characteristic via `FiniteField.card'`.
- **How**: Uses `FiniteField.card' K` to obtain `p` and install `Fact p.Prime` + `CharP K p` instances; then calls `qth_root_witness_of_charP W p`.
- **Hypotheses**: `K` finite field (no explicit characteristic hypothesis needed).
- **Uses from project**: `qth_root_witness_of_charP`
- **Used by**: `verschiebung_isDualOf_frobenius_general`
- **Visibility**: public
- **Lines**: 514–521; proof ~8 lines
- **Notes**: None

---

### `theorem verschiebung_isDualOf_frobenius_general`

- **Type**: `IsDualOf W.toAffine (verschiebungIsog_of_witness W (mulByInt_q_pullback_image_subset_frobenius_of_element_witness W (qth_root_witness_general W))) (frobeniusIsog W)`
- **What**: The GAP-QF keystone: the Verschiebung isogeny is the dual of Frobenius, for any elliptic curve over any finite field. No per-prime computation, no new axioms.
- **How**: Feeds `qth_root_witness_general W` through `mulByInt_q_pullback_image_subset_frobenius_of_element_witness` to produce the subset-witness, then directly applies `verschiebungIsog_isDualOf_frobenius_of_qth_root_witness`.
- **Hypotheses**: `W` an elliptic curve over a finite field `K`.
- **Uses from project**: `qth_root_witness_general`, `mulByInt_q_pullback_image_subset_frobenius_of_element_witness`, `verschiebungIsog_of_witness`, `verschiebungIsog_isDualOf_frobenius_of_qth_root_witness`, `frobeniusIsog`
- **Used by**: unused in file (exported result; used by downstream files)
- **Visibility**: public
- **Lines**: 530–536; proof ~7 lines (term-mode)
- **Notes**: Final exported keystone theorem; not called within this file.

---

## Cross-reference: Key API (used by 3+ declarations in this file)

- **`algebraMap_polynomial_eq_fractionRing`**: used by `x_gen_mem_fractionRing_range` (line 118), `mem_adjoin_x_gen_of_mem_fractionRing_range` (line 148), `mulByInt_x_mem_fractionRing_range` (lines 160, 163).

## Unused in file

- `x_gen_mem_fractionRing_range` (line 115): declared but never called in this file.
- `verschiebung_isDualOf_frobenius_general` (line 530): the final exported theorem, not called within this file.

## Long proofs (> 30 lines)

- `mulByInt_pow_pullback_x_gen_mem_adjoin_pow_routeB`: ~40 lines (induction with decomposition and intermediate-field manipulation)
- `mulByInt_pow_pullback_y_gen_mem_adjoin_pair_pow`: ~58 lines (two-generator induction with both x and y generator cases)

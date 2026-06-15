# Inventory: ./HasseWeil/Verschiebung/DivPolyExpand.lean

**Total declarations**: 6 (all theorems, no defs/instances)
**Sorries**: none
**File length**: 167 lines

---

## Imports

- `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`
- `Mathlib.Algebra.Polynomial.Expand`

## Context

`variable {R : Type*} [CommRing R]` — all theorems are in `namespace HasseWeil`.

---

## Declaration inventory

### `theorem Φ_two_mem_expand_two_charP`

- **Type**: `[CharP R 2] (W : WeierstrassCurve R) : W.Φ 2 ∈ Set.range (⇑(Polynomial.expand R 2))`
- **What**: Proves that the division polynomial Φ₂ lies in the image of the `p`-expansion map `Polynomial.expand R 2`, i.e., Φ₂ is a polynomial in X². This is the base case q = 2 of Silverman III.6.2.
- **How**: Provides explicit witness `X² - b₄·X - b₈`, rewrites via `W.Φ_two` and the ring homomorphism properties of `expand` (`expand_C`, `expand_X`, `map_pow`), then uses `CharP.cast_eq_zero R 2` to kill the `2·b₆·X` term and closes with `ring`.
- **Hypotheses**: `R` is a commutative ring with `CharP R 2`; `W` is a Weierstrass curve over `R`.
- **Uses from project**: none (only mathlib)
- **Used by**: unused within this file (used by `QthRoots.lean` and `Route2Universal.lean`)
- **Visibility**: public
- **Lines**: 48–57; proof lines 49–57 (≈ 9 lines)
- **Notes**: none

---

### `theorem ΨSq_two_mem_expand_two_charP`

- **Type**: `[CharP R 2] (W : WeierstrassCurve R) : W.ΨSq 2 ∈ Set.range (⇑(Polynomial.expand R 2))`
- **What**: Proves that the squared division polynomial ΨSq₂ lies in the image of `Polynomial.expand R 2`, i.e., ΨSq₂ is a polynomial in X². Base case q = 2 companion to `Φ_two_mem_expand_two_charP`.
- **How**: Provides explicit witness `b₂·X + b₆`, rewrites via `W.ΨSq_two`, `WeierstrassCurve.Ψ₂Sq`, and expand ring hom properties; uses `CharP.cast_eq_zero R 2` to show 4 = 0 and 2·b₄ = 0, killing the `4X³` and `2b₄X` terms; closes with `ring`.
- **Hypotheses**: `R` commutative ring with `CharP R 2`; `W` Weierstrass curve over `R`.
- **Uses from project**: none
- **Used by**: unused within this file (used by `QthRoots.lean` and `Route2Universal.lean`)
- **Visibility**: public
- **Lines**: 64–74; proof lines 65–74 (≈ 10 lines)
- **Notes**: none

---

### `theorem b_relation_of_charP_three`

- **Type**: `[CharP R 3] (W : WeierstrassCurve R) : W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2`
- **What**: In characteristic 3, the b-relation simplifies to `b₈ = b₂·b₆ - b₄²`. This is a specialisation of the mathlib identity `4·b₈ = b₂·b₆ - b₄²` (`WeierstrassCurve.b_relation`) using `4 = 1` in char 3.
- **How**: Invokes `W.b_relation` from mathlib, shows `(4 : R) = 1` via `CharP.cast_eq_zero R 3` (since 3 = 0 so 4 = 3+1 = 1), rewrites with `one_mul`.
- **Hypotheses**: `R` commutative ring with `CharP R 3`; `W` Weierstrass curve over `R`.
- **Uses from project**: none
- **Used by**: `Φ_three_mem_expand_three_charP` (line 140); also used by `QthRoots.lean`
- **Visibility**: public
- **Lines**: 81–88; proof lines 82–88 (≈ 7 lines)
- **Notes**: none

---

### `theorem Ψ₃_mem_expand_three_charP`

- **Type**: `[CharP R 3] (W : WeierstrassCurve R) : W.Ψ₃ ∈ Set.range (⇑(Polynomial.expand R 3))`
- **What**: Proves that the division polynomial Ψ₃ lies in the image of `Polynomial.expand R 3`, i.e., Ψ₃ is a polynomial in X³. Base case q = 3 of Silverman III.6.2.
- **How**: Provides explicit witness `b₂·X + b₈`, rewrites via `WeierstrassCurve.Ψ₃` and expand ring hom properties; constructs `(3 : Polynomial R) = 0` from `CharP.cast_eq_zero R 3` via `Nat.cast_ofNat` and `Polynomial.C_0`; closes the polynomial identity using `linear_combination` with the explicit char-3 multiplier `-(X⁴ + b₄·X² + b₆·X) * h_3P`.
- **Hypotheses**: `R` commutative ring with `CharP R 3`; `W` Weierstrass curve over `R`.
- **Uses from project**: none
- **Used by**: `ΨSq_three_mem_expand_three_charP` (line 113); also used by `QthRoots.lean` and `Route2Universal.lean`
- **Visibility**: public
- **Lines**: 94–106; proof lines 95–106 (≈ 12 lines)
- **Notes**: none

---

### `theorem ΨSq_three_mem_expand_three_charP`

- **Type**: `[CharP R 3] (W : WeierstrassCurve R) : W.ΨSq 3 ∈ Set.range (⇑(Polynomial.expand R 3))`
- **What**: Proves that ΨSq₃ lies in the image of `Polynomial.expand R 3`, i.e., ΨSq₃ = Ψ₃² is a polynomial in X³. Derived directly from `Ψ₃_mem_expand_three_charP` via `W.ΨSq_three : W.ΨSq 3 = W.Ψ₃²`.
- **How**: Destructs the range witness for `Ψ₃` from `Ψ₃_mem_expand_three_charP W`, squares it, uses `map_pow` on the expand ring hom.
- **Hypotheses**: `R` commutative ring with `CharP R 3`; `W` Weierstrass curve over `R`.
- **Uses from project**: `Ψ₃_mem_expand_three_charP`
- **Used by**: unused within this file (used by `QthRoots.lean` and `Route2Universal.lean`)
- **Visibility**: public
- **Lines**: 111–115; proof lines 112–115 (≈ 4 lines)
- **Notes**: none

---

### `theorem Φ_three_mem_expand_three_charP`

- **Type**: `[CharP R 3] (W : WeierstrassCurve R) : W.Φ 3 ∈ Set.range (⇑(Polynomial.expand R 3))`
- **What**: Proves that Φ₃ lies in the image of `Polynomial.expand R 3`, i.e., Φ₃ is a polynomial in X³. Base case q = 3, the most involved of the three, requiring a sympy-verified explicit witness polynomial of degree 3 in X with coefficients in terms of b₂, b₄, b₆.
- **How**: Provides the explicit degree-3 witness polynomial with coefficients `2·b₂·b₄`, `2·b₂³·b₆ + b₂²·b₄² + b₂·b₄·b₆`, `2·b₂·b₄·b₆² + b₄³·b₆ + b₆³` (sympy-verified). Rewrites via `W.Φ_three`, `WeierstrassCurve.Ψ₃`, `WeierstrassCurve.preΨ₄`, `WeierstrassCurve.Ψ₂Sq`, and `b_relation_of_charP_three W` (to substitute `b₈ = b₂·b₆ - b₄²`), then `push_cast` and `simp` for expand ring hom rewrites; closes via `linear_combination` with a large explicit char-3 multiplier (a degree-8 polynomial in X times `h_3P`). Needs `set_option maxHeartbeats 1000000` for the `linear_combination` tactic.
- **Hypotheses**: `R` commutative ring with `CharP R 3`; `W` Weierstrass curve over `R`.
- **Uses from project**: `b_relation_of_charP_three`
- **Used by**: unused within this file (used by `QthRoots.lean` and `Route2Universal.lean`)
- **Visibility**: public
- **Lines**: 117–165 (`set_option` at 117, theorem 125–165); proof lines 126–165 (≈ 40 lines)
- **Notes**: `set_option maxHeartbeats 1000000` at line 117 — no justifying comment present in the `set_option` line itself, though the doc-comment references "sympy-verified" witness. Proof is 40 lines, strictly > 30.

---

## Summary statistics

| Metric | Value |
|--------|-------|
| Total declarations | 6 |
| Theorems | 6 |
| Defs | 0 |
| Instances | 0 |
| Sorries | 0 |
| `set_option maxHeartbeats` | 1 (line 117: 1000000) |
| Long proofs (> 30 lines) | 1 (`Φ_three_mem_expand_three_charP`, 40 lines) |
| Unused within file | 4 (`Φ_two_mem_expand_two_charP`, `ΨSq_two_mem_expand_two_charP`, `ΨSq_three_mem_expand_three_charP`, `Φ_three_mem_expand_three_charP`) |
| Key API (used by 3+ in file) | none |

## Notes

This file is a leaf providing the base cases (q = 2 and q = 3) of Silverman III.6.2 for generic `[CommRing R]` with `[CharP R p]`; all six theorems are consumed by `QthRoots.lean` and/or `Route2Universal.lean` as one-line specialisations. The only non-trivial proof is `Φ_three_mem_expand_three_charP`, which uses a sympy-verified degree-9 `linear_combination` witness and requires a heartbeats bump; the char-3 b-relation simplification (`b_relation_of_charP_three`) is an auxiliary lemma for this proof. No sorries, no duplication suspected beyond what mathlib's `b_relation` already provides.

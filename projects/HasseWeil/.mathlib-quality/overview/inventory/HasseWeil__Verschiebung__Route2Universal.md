# Inventory: ./HasseWeil/Verschiebung/Route2Universal.lean

**File**: `HasseWeil/Verschiebung/Route2Universal.lean`
**Total declarations**: 70 (22 defs/types, 48 theorems, 0 instances)
**Sorries**: none
**`set_option maxHeartbeats`**: none

---

## Overview

This file implements the "Route 2 universal certificate" strategy for discharging Verschiebung polynomial identities (squaring, cubing, etc.) across all `(q, char)` pairs from a single `MvPolynomial AVar (ZMod p)` source. It defines the universal variable enum `AVar`, the universal coefficient ring `URing p`, universal Weierstrass b-coefficients and polynomial expressions, proves per-prime vanishing of binomial cross-terms via Freshman's dream (`(p : ZMod p) = 0`), provides K-level specialisations, and develops the full inductive infrastructure (`Φ_{p^k}, Ψ_{p^k}² ∈ R[X^{p^k}]`) as a pipeline of function-field and polynomial lemmas.

---

## Declarations

### `inductive AVar`
- **Type**: `Type` with constructors `a1 | a2 | a3 | a4 | a6 | X | Y`, deriving `DecidableEq`
- **What**: The variable index type for `MvPolynomial AVar (ZMod p)`, representing the five Weierstrass coefficients plus polynomial indeterminates X and Y.
- **How**: Pure inductive definition; `DecidableEq` derived automatically.
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `URing`, `Ua1`, `Ua2`, `Ua3`, `Ua4`, `Ua6`, `UX`, `UY` (via `MvPolynomial.X AVar.*`)
- **Visibility**: public
- **Lines**: 95–103
- **Notes**: keyApi (used by 8 other declarations)

---

### `abbrev URing`
- **Type**: `(p : ℕ) → [Fact p.Prime] → Type := MvPolynomial AVar (ZMod p)`
- **What**: The universal coefficient ring, i.e. `MvPolynomial AVar (ZMod p)`, used throughout the file as the ambient ring for universal polynomial identities.
- **How**: Abbreviation; no proof.
- **Hypotheses**: `p` prime
- **Uses from project**: [`AVar`]
- **Used by**: All universal def/theorem declarations in the file
- **Visibility**: public
- **Lines**: 106–107
- **Notes**: keyApi (used in the type of virtually every universal declaration)

---

### `noncomputable def Ua1`
- **Type**: `(p : ℕ) → [Fact p.Prime] → URing p := MvPolynomial.X AVar.a1`
- **What**: The universal variable for the Weierstrass coefficient a₁.
- **How**: Direct term.
- **Hypotheses**: `p` prime
- **Uses from project**: [`AVar`, `URing`]
- **Used by**: `Ub2`, `Ub4`, `UB`, `universalCurve`
- **Visibility**: public
- **Lines**: 112
- **Notes**: keyApi (used by ≥3 other declarations)

---

### `noncomputable def Ua2`
- **Type**: `(p : ℕ) → [Fact p.Prime] → URing p := MvPolynomial.X AVar.a2`
- **What**: Universal variable for a₂.
- **How**: Direct term.
- **Hypotheses**: `p` prime
- **Uses from project**: [`AVar`, `URing`]
- **Used by**: `Ub2`, `Ub8`, `Ucubic`, `universalCurve`
- **Visibility**: public
- **Lines**: 115
- **Notes**: keyApi (used by 4 declarations)

---

### `noncomputable def Ua3`
- **Type**: `(p : ℕ) → [Fact p.Prime] → URing p := MvPolynomial.X AVar.a3`
- **What**: Universal variable for a₃.
- **How**: Direct term.
- **Hypotheses**: `p` prime
- **Uses from project**: [`AVar`, `URing`]
- **Used by**: `Ub4`, `Ub6`, `Ub8`, `UB`, `universalCurve`
- **Visibility**: public
- **Lines**: 118
- **Notes**: keyApi (used by 5 declarations)

---

### `noncomputable def Ua4`
- **Type**: `(p : ℕ) → [Fact p.Prime] → URing p := MvPolynomial.X AVar.a4`
- **What**: Universal variable for a₄.
- **How**: Direct term.
- **Hypotheses**: `p` prime
- **Uses from project**: [`AVar`, `URing`]
- **Used by**: `Ub4`, `Ub8`, `Ucubic`, `universalCurve`
- **Visibility**: public
- **Lines**: 121
- **Notes**: keyApi (used by 4 declarations)

---

### `noncomputable def Ua6`
- **Type**: `(p : ℕ) → [Fact p.Prime] → URing p := MvPolynomial.X AVar.a6`
- **What**: Universal variable for a₆.
- **How**: Direct term.
- **Hypotheses**: `p` prime
- **Uses from project**: [`AVar`, `URing`]
- **Used by**: `Ub6`, `Ub8`, `Ucubic`, `universalCurve`
- **Visibility**: public
- **Lines**: 124
- **Notes**: keyApi (used by 4 declarations)

---

### `noncomputable def UX`
- **Type**: `(p : ℕ) → [Fact p.Prime] → URing p := MvPolynomial.X AVar.X`
- **What**: Universal polynomial indeterminate X.
- **How**: Direct term.
- **Hypotheses**: `p` prime
- **Uses from project**: [`AVar`, `URing`]
- **Used by**: `UB`, `Ucubic`
- **Visibility**: public
- **Lines**: 127

---

### `noncomputable def UY`
- **Type**: `(p : ℕ) → [Fact p.Prime] → URing p := MvPolynomial.X AVar.Y`
- **What**: Universal bivariate indeterminate Y (for the squaring identity over the curve).
- **How**: Direct term.
- **Hypotheses**: `p` prime
- **Uses from project**: [`AVar`, `URing`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 131
- **Notes**: Not referenced by any other declaration within this file.

---

### `noncomputable def Ub2`
- **Type**: `(p : ℕ) → [Fact p.Prime] → URing p := Ua1 p ^ 2 + 4 * Ua2 p`
- **What**: Universal Weierstrass b₂ coefficient.
- **How**: Direct polynomial expression.
- **Hypotheses**: `p` prime
- **Uses from project**: [`URing`, `Ua1`, `Ua2`]
- **Used by**: `UB`
- **Visibility**: public
- **Lines**: 150–152

---

### `noncomputable def Ub4`
- **Type**: `(p : ℕ) → [Fact p.Prime] → URing p := 2 * Ua4 p + Ua1 p * Ua3 p`
- **What**: Universal b₄.
- **How**: Direct polynomial expression.
- **Hypotheses**: `p` prime
- **Uses from project**: [`URing`, `Ua1`, `Ua3`, `Ua4`]
- **Used by**: `UB`
- **Visibility**: public
- **Lines**: 154–155

---

### `noncomputable def Ub6`
- **Type**: `(p : ℕ) → [Fact p.Prime] → URing p := Ua3 p ^ 2 + 4 * Ua6 p`
- **What**: Universal b₆.
- **How**: Direct polynomial expression.
- **Hypotheses**: `p` prime
- **Uses from project**: [`URing`, `Ua3`, `Ua6`]
- **Used by**: `UB`
- **Visibility**: public
- **Lines**: 158–159

---

### `noncomputable def Ub8`
- **Type**: `(p : ℕ) → [Fact p.Prime] → URing p`; `a₁²a₆ + 4a₂a₆ - a₁a₃a₄ + a₂a₃² - a₄²`
- **What**: Universal b₈.
- **How**: Direct polynomial expression.
- **Hypotheses**: `p` prime
- **Uses from project**: [`URing`, `Ua1`, `Ua2`, `Ua3`, `Ua4`, `Ua6`]
- **Used by**: `UB`
- **Visibility**: public
- **Lines**: 163–165

---

### `noncomputable def universalSquaringMultiplier`
- **Type**: `(p : ℕ) → [Fact p.Prime] → URing p := 0`
- **What**: Placeholder for the sympy-verified multiplier polynomial M(X,Y) in the universal squaring identity; currently 0 (for p=2 no multiplier is needed).
- **How**: Constant 0.
- **Hypotheses**: `p` prime
- **Uses from project**: [`URing`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 187–192
- **Notes**: Stub/placeholder; not referenced anywhere else in the file.

---

### `noncomputable def UB`
- **Type**: `(p : ℕ) → [Fact p.Prime] → URing p`; the Y-component coefficient of ω₂
- **What**: Universal B polynomial: `a₁ · Ψ₃(X) + (a₁X + a₃)³`, where Ψ₃ is expressed via b-coefficients.
- **How**: Direct polynomial expression in `URing p`.
- **Hypotheses**: `p` prime
- **Uses from project**: [`URing`, `Ua1`, `Ua3`, `UX`, `Ub2`, `Ub4`, `Ub6`, `Ub8`]
- **Used by**: `universalSquaringIdentity`, `universalCubingIdentity`, `universalQuinticIdentity`, `universalSepticIdentity`, `universalCharIdentity`
- **Visibility**: public
- **Lines**: 212–215
- **Notes**: keyApi (used by 5 declarations)

---

### `noncomputable def Ucubic`
- **Type**: `(p : ℕ) → [Fact p.Prime] → URing p := UX p ^ 3 + Ua2 p * UX p ^ 2 + Ua4 p * UX p + Ua6 p`
- **What**: Universal cubic polynomial X³ + a₂X² + a₄X + a₆ (the Weierstrass cubic in X).
- **How**: Direct polynomial expression.
- **Hypotheses**: `p` prime
- **Uses from project**: [`URing`, `UX`, `Ua2`, `Ua4`, `Ua6`]
- **Used by**: `universalSquaringIdentity`, `universalCubingIdentity`, `universalQuinticIdentity`, `universalSepticIdentity`, `universalCharIdentity`
- **Visibility**: public
- **Lines**: 219–220
- **Notes**: keyApi (used by 5 declarations)

---

### `def universalSquaringIdentity`
- **Type**: `(p : ℕ) → [Fact p.Prime] → Prop := (2 : URing p) * UB p * Ucubic p = 0`
- **What**: The universal squaring identity Prop: the residual `2 · B · cubic_x` vanishes in `URing p`.
- **How**: Prop-valued def.
- **Hypotheses**: `p` prime
- **Uses from project**: [`URing`, `UB`, `Ucubic`]
- **Used by**: `universalSquaringIdentity_holds_two`
- **Visibility**: public
- **Lines**: 225–226

---

### `theorem universalSquaringIdentity_holds_two`
- **Type**: `universalSquaringIdentity 2`
- **What**: Proves the universal squaring identity for p=2: `(2 : URing 2) = 0` since `(2 : ZMod 2) = 0`, hence the product vanishes.
- **How**: Unfolds definition, uses `(2 : ZMod 2) = 0` by `rfl`, applies `MvPolynomial.C_0`, then `zero_mul`.
- **Hypotheses**: none (p=2 is prime by `Nat.prime_two`)
- **Uses from project**: [`universalSquaringIdentity`, `URing`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 230–238, proof ~8 lines

---

### `def universalCubingIdentity`
- **Type**: `(p : ℕ) → [Fact p.Prime] → Prop := (3 : URing p) * UB p * Ucubic p = 0`
- **What**: q=3 analog of `universalSquaringIdentity`: residual `3 · UB · Ucubic = 0` in `URing p`.
- **How**: Prop-valued def.
- **Hypotheses**: `p` prime
- **Uses from project**: [`URing`, `UB`, `Ucubic`]
- **Used by**: `universalCubingIdentity_holds_three`
- **Visibility**: public
- **Lines**: 258–259

---

### `theorem universalCubingIdentity_holds_three`
- **Type**: `universalCubingIdentity 3`
- **What**: Proves the universal cubing identity for p=3 via `(3 : ZMod 3) = 0`.
- **How**: Same pattern as the squaring case: `(3 : ZMod 3) = 0` by `rfl`, `MvPolynomial.C_0`, `zero_mul`.
- **Hypotheses**: none
- **Uses from project**: [`universalCubingIdentity`, `URing`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 264–272, proof ~8 lines

---

### `def universalQuinticIdentity`
- **Type**: `(p : ℕ) → [Fact p.Prime] → Prop := (5 : URing p) * UB p * Ucubic p = 0`
- **What**: q=5 analog of the squaring/cubing universal identity.
- **How**: Prop-valued def.
- **Hypotheses**: `p` prime
- **Uses from project**: [`URing`, `UB`, `Ucubic`]
- **Used by**: `universalQuinticIdentity_holds_five`
- **Visibility**: public
- **Lines**: 292–293

---

### `theorem universalQuinticIdentity_holds_five`
- **Type**: `universalQuinticIdentity 5` (with local `Fact (Nat.Prime 5)` instance)
- **What**: Proves the universal quintic identity for p=5 via `(5 : ZMod 5) = 0`.
- **How**: Same pattern; `decide` used to establish `Fact (Nat.Prime 5)`.
- **Hypotheses**: none
- **Uses from project**: [`universalQuinticIdentity`, `URing`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 297–307, proof ~10 lines

---

### `def universalSepticIdentity`
- **Type**: `(p : ℕ) → [Fact p.Prime] → Prop := (7 : URing p) * UB p * Ucubic p = 0`
- **What**: q=7 analog.
- **How**: Prop-valued def.
- **Hypotheses**: `p` prime
- **Uses from project**: [`URing`, `UB`, `Ucubic`]
- **Used by**: `universalSepticIdentity_holds_seven`
- **Visibility**: public
- **Lines**: 316–317

---

### `theorem universalSepticIdentity_holds_seven`
- **Type**: `universalSepticIdentity 7` (with local `Fact (Nat.Prime 7)`)
- **What**: Proves the universal septic identity for p=7.
- **How**: Same pattern as quintic.
- **Hypotheses**: none
- **Uses from project**: [`universalSepticIdentity`, `URing`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 320–330, proof ~10 lines

---

### `def universalCharIdentity`
- **Type**: `(p : ℕ) → [Fact p.Prime] → Prop := (p : URing p) * UB p * Ucubic p = 0`
- **What**: Uniform-in-p generalization: residual `p · UB · Ucubic = 0` in `URing p` for any prime p. Subsumes the four per-prime variants.
- **How**: Prop-valued def.
- **Hypotheses**: `p` prime
- **Uses from project**: [`URing`, `UB`, `Ucubic`]
- **Used by**: `universalCharIdentity_holds`
- **Visibility**: public
- **Lines**: 349–350

---

### `theorem universalCharIdentity_holds`
- **Type**: `(p : ℕ) → [Fact p.Prime] → universalCharIdentity p`
- **What**: Proves the uniform-in-p universal identity: uses `CharP.cast_eq_zero (URing p) p` (which holds because `MvPolynomial` auto-derives `CharP _ p` from `CharP (ZMod p) p`) to reduce `(p : URing p)` to 0, then multiplies.
- **How**: One-liner: `rw [CharP.cast_eq_zero (URing p) p, zero_mul, zero_mul]`.
- **Hypotheses**: `p` prime
- **Uses from project**: [`universalCharIdentity`, `URing`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 355–358, proof 2 lines

---

### `theorem squaringIdentity_specialized_char_two`
- **Type**: For any `[Field K] [Fintype K] [DecidableEq K] (W : WeierstrassCurve K) [CharP K 2]`, an explicit K-level polynomial identity `(2 : Polynomial K) * B_K * cubic_x_K = 0`.
- **What**: K-level specialisation of the universal squaring identity: for any char-2 curve, the explicit binomial residual vanishes in `Polynomial K`.
- **How**: `CharP.cast_eq_zero K 2` gives `(2 : K) = 0`; lifts via `Polynomial.C_0` and `zero_mul`.
- **Hypotheses**: K field, char 2
- **Uses from project**: []
- **Used by**: unused in file (doc-referenced only)
- **Visibility**: public
- **Lines**: 368–384, proof ~16 lines

---

### `theorem cubingIdentity_specialized_char_three`
- **Type**: Analogous K-level identity for `[CharP K 3]`.
- **What**: `(3 : Polynomial K) * B_K * cubic_x_K = 0` for char-3 curves.
- **How**: Same pattern as `squaringIdentity_specialized_char_two`.
- **Hypotheses**: K field, char 3
- **Uses from project**: []
- **Used by**: unused in file (doc-referenced only)
- **Visibility**: public
- **Lines**: 394–410, proof ~16 lines

---

### `theorem quinticIdentity_specialized_char_five`
- **Type**: Analogous K-level identity for `[CharP K 5]`.
- **What**: `(5 : Polynomial K) * B_K * cubic_x_K = 0` for char-5 curves.
- **How**: Same pattern.
- **Hypotheses**: K field, char 5
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 420–436, proof ~16 lines

---

### `theorem septicIdentity_specialized_char_seven`
- **Type**: Analogous K-level identity for `[CharP K 7]`.
- **What**: `(7 : Polynomial K) * B_K * cubic_x_K = 0` for char-7 curves.
- **How**: Same pattern.
- **Hypotheses**: K field, char 7
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 440–456, proof ~16 lines

---

### `theorem charIdentity_specialized`
- **Type**: `(W : WeierstrassCurve K) (p : ℕ) [Fact p.Prime] [CharP K p] → (p : Polynomial K) * B_K * cubic_x_K = 0`
- **What**: Uniform-in-p K-level identity: one theorem replacing all four per-char variants.
- **How**: Single line: `rw [CharP.cast_eq_zero (Polynomial K) p, zero_mul, zero_mul]`.
- **Hypotheses**: K field, char p
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 471–481, proof 1 line

---

### `theorem h_polyRoot_sq_alpha_0_holds_char_two`
- **Type**: For `[CharP K 2]` and `h_card : Fintype.card K = 2`, proves `(polyExpandRoot ...) ^ 2 = aeval (x_gen W) (omega2_coupled_residual_char_two W)`.
- **What**: The polyExpandRoot squaring identity for the α₀ component of the char-2 squaring witness, avoiding the `Fintype.card K = 2 ↔ ^ 2` rewrite wall via `set` abstraction.
- **How**: Uses `set` to bind the polyExpandRoot value, then `polyExpandRoot_aeval_pow_eq` + `polyPowCardEq_of_finite`, rewriting the exponent `2` as `Fintype.card K`.
- **Hypotheses**: K finite field, char 2, `Fintype.card K = 2`, curve IsElliptic
- **Uses from project**: [`polyExpandRoot`, `omega2_coupled_residual_char_two`, `omega2_coupled_residual_mem_expand_two_char_two`, `polyExpandRoot_aeval_pow_eq`, `polyPowCardEq_of_finite`, `x_gen`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 492–508, proof ~16 lines

---

### `theorem h_polyRoot_sq_alpha_1_holds_char_two`
- **Type**: Analogous for `omega2_Y_coeff_char_two` (the α₁ component).
- **What**: polyExpandRoot squaring identity for the Y-coefficient component in the char-2 squaring witness.
- **How**: Same structure as `h_polyRoot_sq_alpha_0_holds_char_two`.
- **Hypotheses**: K finite field, char 2, `Fintype.card K = 2`, curve IsElliptic
- **Uses from project**: [`polyExpandRoot`, `omega2_Y_coeff_char_two`, `omega2_Y_coeff_mem_expand_two_char_two`, `polyExpandRoot_aeval_pow_eq`, `polyPowCardEq_of_finite`, `x_gen`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 512–528, proof ~16 lines

---

### `theorem h_polyRoot_cube_Ψ₃_holds_char_three`
- **Type**: For `[CharP K 3]` and `h_card : Fintype.card K = 3`, proves `(polyExpandRoot W.Ψ₃ ...) ^ 3 = aeval (x_gen W) W.Ψ₃`.
- **What**: q=3 analog of the alpha-0 squaring witness: polyExpandRoot cubing identity for Ψ₃.
- **How**: Same `set`-abstraction pattern with `polyExpandRoot_aeval_pow_eq` + `polyPowCardEq_of_finite`, exponent rewritten as `Fintype.card K`.
- **Hypotheses**: K finite field, char 3, `Fintype.card K = 3`, curve IsElliptic
- **Uses from project**: [`polyExpandRoot`, `Ψ₃_mem_expand_three_char_three`, `polyExpandRoot_aeval_pow_eq`, `polyPowCardEq_of_finite`, `x_gen`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 541–557, proof ~16 lines

---

### `theorem h_polyRoot_cube_ΨSq_three_holds_char_three`
- **Type**: Analogous for `W.ΨSq 3` (q=3 analog of alpha-1).
- **What**: polyExpandRoot cubing identity for ΨSq 3 in char 3.
- **How**: Same pattern.
- **Hypotheses**: K finite field, char 3, `Fintype.card K = 3`, curve IsElliptic
- **Uses from project**: [`polyExpandRoot`, `ΨSq_three_mem_expand_three_char_three`, `polyExpandRoot_aeval_pow_eq`, `polyPowCardEq_of_finite`, `x_gen`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 562–578, proof ~16 lines

---

### `theorem h_polyRoot_cube_omega3_coupled_residual_full_char_three`
- **Type**: Same pattern but carries `h_mem : omega3_coupled_residual_full_char_three W ∈ Set.range (Polynomial.expand K 3)` as a parameter.
- **What**: Witness-parametric polyExpandRoot cubing for the corrected ω₃ coupled residual; unblocks downstream K(E)-level work pending the substantive sympy-verified Lean transcription.
- **How**: Same `set`-abstraction + `polyExpandRoot_aeval_pow_eq` + `polyPowCardEq_of_finite`.
- **Hypotheses**: K finite field, char 3, `Fintype.card K = 3`, IsElliptic, `h_mem` (expand-3 membership passed as hypothesis)
- **Uses from project**: [`polyExpandRoot`, `omega3_coupled_residual_full_char_three`, `polyExpandRoot_aeval_pow_eq`, `polyPowCardEq_of_finite`, `x_gen`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 589–608, proof ~19 lines
- **Notes**: Substantive proof (sympy-verified identity) is carried as hypothesis `h_mem`, not discharged here.

---

### `theorem pow_mem_expand_charP`
- **Type**: `[CommRing R] [CharP R p] (f : Polynomial R) → f ^ p ∈ Set.range (Polynomial.expand R p)`
- **What**: In char p, every p-th power of a polynomial is in the expand-p range; explicit witness is `f.map (frobenius R p)`.
- **How**: Induction on `f` via `Polynomial.induction_on'`: for sums uses `add_pow_expChar`; for monomials uses `frobenius_def` and `ring`.
- **Hypotheses**: CommRing with char p
- **Uses from project**: []
- **Used by**: `pow_pow_mem_expand_pow_charP`
- **Visibility**: public (inside `section GenericExpand`)
- **Lines**: 655–664, proof ~9 lines

---

### `theorem expand_pow_map_iterateFrobenius`
- **Type**: `[CommRing R] [CharP R p] (n : ℕ) (f : Polynomial R) → Polynomial.expand R (p^n) (f.map (iterateFrobenius R p n)) = f ^ (p^n)`
- **What**: Equational form of the expand-iterate Frobenius identity: expanding a Frobenius-mapped polynomial equals the p^n-th power.
- **How**: Induction on `f` via `Polynomial.induction_on'`: sums use `add_pow_expChar_pow`; monomials use `iterateFrobenius_def` and `ring`.
- **Hypotheses**: CommRing with char p
- **Uses from project**: []
- **Used by**: `pow_pow_mem_expand_pow_charP`, `pow_pow_mem_expand_pow_succ_of_expand_charP`
- **Visibility**: public
- **Lines**: 668–677, proof ~9 lines

---

### `theorem pow_pow_mem_expand_pow_charP`
- **Type**: `[CommRing R] [CharP R p] (n : ℕ) (f : Polynomial R) → f ^ (p^n) ∈ Set.range (Polynomial.expand R (p^n))`
- **What**: Iterated version of `pow_mem_expand_charP`: f^{p^n} lies in the expand(p^n)-range.
- **How**: One-liner: `⟨f.map (iterateFrobenius R p n), expand_pow_map_iterateFrobenius p n f⟩`.
- **Hypotheses**: CommRing with char p
- **Uses from project**: [`expand_pow_map_iterateFrobenius`]
- **Used by**: `Φ_p_pow_mem_expand_p_of_base`
- **Visibility**: public
- **Lines**: 682–685, proof 1 line

---

### `theorem mul_mem_expand_range`
- **Type**: `(p : ℕ) (f g : Polynomial R) → f ∈ range(expand p) → g ∈ range(expand p) → f * g ∈ range(expand p)`
- **What**: The image of `Polynomial.expand R p` is closed under multiplication (it is a ring-hom image, hence a subring).
- **How**: Obtain witnesses via `obtain ⟨f', hf⟩ := hf`; explicit witness `f' * g'` with `map_mul`.
- **Hypotheses**: CommRing R
- **Uses from project**: []
- **Used by**: `mem_expand_range_of_isCoprime_witness`
- **Visibility**: public
- **Lines**: 690–696, proof ~6 lines

---

### `theorem pow_mem_expand_range`
- **Type**: `(p : ℕ) (f : Polynomial R) (n : ℕ) → f ∈ range(expand p) → f^n ∈ range(expand p)`
- **What**: The expand-p range is closed under powers.
- **How**: Obtain witness; `map_pow` gives explicit witness `f'^n`.
- **Hypotheses**: CommRing R
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 700–704, proof ~4 lines

---

### `theorem expand_pow_eq_expand_iterate`
- **Type**: `(p k : ℕ) (f : Polynomial R) → (Polynomial.expand R p)^[k] f = Polynomial.expand R (p^k) f`
- **What**: Iterating `expand p` k times equals `expand (p^k)`.
- **How**: Induction on k; base `simp`; step uses `Function.iterate_succ'`, `Polynomial.expand_expand`, `pow_succ'`.
- **Hypotheses**: CommRing R
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 709–715, proof ~6 lines

---

### `theorem Φ_p_pow_mem_expand_p_of_base`
- **Type**: `[CommRing R] [CharP R p] (n : ℕ) (W : WeierstrassCurve R) (h_base : W.Φ p ∈ range(expand p)) → (W.Φ p)^(p^n) ∈ range(expand (p^n))`
- **What**: If Φ_p ∈ expand-p range, then (Φ_p)^{p^n} ∈ expand(p^n) range. Inductive building block.
- **How**: Immediate from `pow_pow_mem_expand_pow_charP`; does NOT use `h_base` (the hypothesis is vacuously held, the result comes purely from char-p Frobenius structure).
- **Hypotheses**: CommRing with char p, Φ_p ∈ expand-p range (not actually needed!)
- **Uses from project**: [`pow_pow_mem_expand_pow_charP`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 728–732, proof 1 line
- **Notes**: The hypothesis `h_base` is unused in the proof body — the result follows from `pow_pow_mem_expand_pow_charP` alone.

---

### `theorem pow_pow_mem_expand_pow_succ_of_expand_charP`
- **Type**: `[CommRing R] [CharP R p] (k : ℕ) (f : Polynomial R) → f ∈ range(expand p) → f^(p^k) ∈ range(expand (p^(k+1)))`
- **What**: If f ∈ expand-p range, then f^{p^k} ∈ expand(p^{k+1}) range. Key inductive step.
- **How**: Obtains witness A with `f = expand p A`; then `expand(p^(k+1)) (A.map iterateFrobenius) = (expand p A)^(p^k)` via `expand_pow_map_iterateFrobenius`, `Polynomial.map_expand`, `Polynomial.expand_expand`.
- **Hypotheses**: CommRing with char p
- **Uses from project**: [`expand_pow_map_iterateFrobenius`]
- **Used by**: (in the comment for `mulByInt_pow_pullback_x_gen_mem_adjoin_pow_of_base`, but not directly called by any proof in file)
- **Visibility**: public
- **Lines**: 745–757, proof ~12 lines

---

### `theorem expand_aeval_mem_adjoin_pow`
- **Type**: `[Field K] [Field L] [Algebra K L] (p : ℕ) (A : Polynomial K) (z : L) → aeval z (expand K p A) ∈ adjoin K {z^p}`
- **What**: Evaluating an expand-p polynomial at z gives an element of K(z^p).
- **How**: `Polynomial.expand_aeval` rewrites `aeval z (expand p A) = aeval (z^p) A`; then `Polynomial.aeval_mem_adjoin_singleton` + `IntermediateField.algebra_adjoin_le_adjoin`.
- **Hypotheses**: Fields K ⊆ L
- **Uses from project**: []
- **Used by**: `mulByInt_p_pullback_x_gen_mem_adjoin_pow_of_base`
- **Visibility**: public
- **Lines**: 764–770, proof ~6 lines

---

### `theorem Φ_ff_eq_aeval_x_gen`
- **Type**: `[Field K] (W : WeierstrassCurve K) [IsElliptic] (n : ℤ) → Φ_ff W n = aeval (x_gen W) (W.Φ n)`
- **What**: Identifies Φ_ff (the function-field version of the division polynomial Φ) with `aeval x_gen` applied to the polynomial Φ.
- **How**: Symmetry + explicit chain `aeval (algebraMap CR FF ∘ algebraMap K[X] CR) = ...` using `Polynomial.aeval_algebraMap_apply` twice + `Polynomial.aeval_X_left_apply` + `rfl`.
- **Hypotheses**: Elliptic curve over K
- **Uses from project**: [`Φ_ff`, `x_gen`]
- **Used by**: `mulByInt_p_pullback_x_gen_mem_adjoin_pow_of_base`, `function_field_rational_to_K_X_eq`
- **Visibility**: public
- **Lines**: 775–788, proof ~13 lines

---

### `theorem ΨSq_ff_eq_aeval_x_gen`
- **Type**: `[Field K] (W : WeierstrassCurve K) [IsElliptic] (n : ℤ) → ΨSq_ff W n = aeval (x_gen W) (W.ΨSq n)`
- **What**: Companion of `Φ_ff_eq_aeval_x_gen` for ΨSq_ff.
- **How**: Same proof structure.
- **Hypotheses**: Elliptic curve over K
- **Uses from project**: [`ΨSq_ff`, `x_gen`]
- **Used by**: `mulByInt_p_pullback_x_gen_mem_adjoin_pow_of_base`, `function_field_rational_to_K_X_eq`
- **Visibility**: public
- **Lines**: 791–804, proof ~13 lines

---

### `theorem mulByInt_p_pullback_x_gen_mem_adjoin_pow_of_base`
- **Type**: `[Field K] [DecidableEq K] [IsElliptic] [CharP K p] (h_phi : W.Φ p ∈ range(expand K p)) (h_psi : W.ΨSq p ∈ range(expand K p)) → (mulByInt W.toAffine p).pullback (x_gen W) ∈ adjoin K {x_gen W ^ p}`
- **What**: The [p]-pullback of x_gen lies in K(x_gen^p), given Φ_p, ΨSq_p in expand-p range.
- **How**: Rewrites `mulByInt_pullback_x` to get `Φ_ff/ΨSq_ff`; applies `Φ_ff_eq_aeval_x_gen`/`ΨSq_ff_eq_aeval_x_gen`; uses `expand_aeval_mem_adjoin_pow` for each numerator/denominator; closes with `div_mem`.
- **Hypotheses**: K field with char p; Φ_p and ΨSq_p in expand-p range; IsElliptic
- **Uses from project**: [`Φ_ff_eq_aeval_x_gen`, `ΨSq_ff_eq_aeval_x_gen`, `expand_aeval_mem_adjoin_pow`, `mulByInt_pullback_x`, `Φ_ff`, `ΨSq_ff`, `x_gen`]
- **Used by**: `mulByInt_pow_pullback_x_gen_mem_adjoin_pow_of_base`
- **Visibility**: public
- **Lines**: 809–829, proof ~20 lines

---

### `theorem mulByInt_pow_zero_pullback_x_gen_mem_adjoin_pow`
- **Type**: `[Field K] [DecidableEq K] [IsElliptic] (p : ℕ) → (mulByInt W.toAffine (p^0 : ℕ)).pullback (x_gen W) ∈ adjoin K {x_gen W ^ (p^0 : ℕ)}`
- **What**: Trivial base case k=0: [1]-pullback of x_gen is x_gen itself, which is in adjoin K {x_gen}.
- **How**: `pow_zero` simplifies, `mulByInt_one_pullback_eq_id` gives the identity, `IntermediateField.subset_adjoin`.
- **Hypotheses**: Elliptic curve
- **Uses from project**: [`mulByInt_one_pullback_eq_id`, `x_gen`]
- **Used by**: `mulByInt_pow_pullback_x_gen_mem_adjoin_pow_of_base`
- **Visibility**: public
- **Lines**: 834–844, proof ~10 lines

---

### `theorem adjoin_simple_pow_le_adjoin_simple_pow`
- **Type**: `[Field K] [Field L] [Algebra K L] [CharP L p] (y z : L) → z ∈ adjoin K {y} → z^p ∈ adjoin K {y^p}`
- **What**: In char p, the p-th power map sends adjoin K {y} into adjoin K {y^p}.
- **How**: `IntermediateField.adjoin_induction` with cases: `mem` uses `hx` + `subset_adjoin`; `algebraMap` uses `map_pow`; `add` uses `add_pow_expChar`; `inv` uses `inv_pow`; `mul` uses `mul_pow`.
- **Hypotheses**: Fields K ⊆ L, char p on L
- **Uses from project**: []
- **Used by**: `adjoin_simple_pow_pow_le_adjoin_simple_pow_pow`
- **Visibility**: public
- **Lines**: 852–873, proof ~21 lines

---

### `theorem adjoin_simple_pow_pow_le_adjoin_simple_pow_pow`
- **Type**: `[Field K] [Field L] [Algebra K L] [CharP L p] (y : L) (n : ℕ) (z : L) → z ∈ adjoin K {y} → z^(p^n) ∈ adjoin K {y^(p^n)}`
- **What**: Iterated version: z ∈ adjoin K {y} implies z^{p^n} ∈ adjoin K {y^{p^n}}.
- **How**: Induction on n; base `simpa`; step uses `adjoin_simple_pow_le_adjoin_simple_pow` at `(y^{p^n}, z^{p^n})`.
- **Hypotheses**: Fields K ⊆ L, char p on L
- **Uses from project**: [`adjoin_simple_pow_le_adjoin_simple_pow`]
- **Used by**: `mulByInt_pow_pullback_x_gen_mem_adjoin_pow_of_base`
- **Visibility**: public
- **Lines**: 877–886, proof ~9 lines

---

### `theorem mulByInt_pow_pullback_x_gen_mem_adjoin_pow_of_base`
- **Type**: `[Field K] [DecidableEq K] [IsElliptic] [CharP K p] (h_phi : W.Φ p ∈ range(expand K p)) (h_psi : W.ΨSq p ∈ range(expand K p)) → ∀ k, (mulByInt W.toAffine (p^k : ℕ)).pullback (x_gen W) ∈ adjoin K {x_gen W ^ (p^k : ℕ)}`
- **What**: The main inductive theorem: [p^k]-pullback of x_gen ∈ adjoin K {x_gen^{p^k}} for all k, given base-case expand-p membership for Φ_p and ΨSq_p.
- **How**: Induction on k. Base: `mulByInt_pow_zero_pullback_x_gen_mem_adjoin_pow`. Step: decomposes `[p^{k+1}] = [p^k].comp [p]` via `mulByInt_comp_eq_mul`; uses pullback contravariance; pushes IH through `[p].pullback` via `IntermediateField.adjoin_map`; then `adjoin_simple_pow_pow_le_adjoin_simple_pow_pow` + `mulByInt_p_pullback_x_gen_mem_adjoin_pow_of_base`; derives `CharP FunctionField p` from `charP_of_injective_algebraMap`.
- **Hypotheses**: K field with char p; Φ_p, ΨSq_p ∈ expand-p range; IsElliptic
- **Uses from project**: [`mulByInt_pow_zero_pullback_x_gen_mem_adjoin_pow`, `mulByInt_p_pullback_x_gen_mem_adjoin_pow_of_base`, `adjoin_simple_pow_pow_le_adjoin_simple_pow_pow`, `mulByInt_comp_eq_mul`, `x_gen`]
- **Used by**: `function_field_rational_to_K_X_eq`, `mulByInt_card_pullback_x_gen_mem_adjoin_pow_card_of_base`
- **Visibility**: public
- **Lines**: 905–965, proof **61 lines**
- **Notes**: proof >30 lines

---

### `theorem isCoprime_eq_mul_factor_of_eq_mul`
- **Type**: `[CommRing R] [IsDomain R] {a b f g : R} → b ≠ 0 → IsCoprime a b → a * g = b * f → ∃ h, f = a * h ∧ g = b * h`
- **What**: In an integral domain, coprimality + cross-multiplication equation implies divisibility decomposition.
- **How**: Uses `IsCoprime.dvd_of_dvd_mul_left` to extract `b ∣ g`; obtains `h`; then `mul_left_cancel₀` to identify `f = a * h`.
- **Hypotheses**: integral domain, coprimality, equation
- **Uses from project**: []
- **Used by**: `h_witness_in_expand_range`
- **Visibility**: public
- **Lines**: 978–990, proof ~12 lines

---

### `theorem mem_expand_range_iff_coeff_zero`
- **Type**: `[CommSemiring R] (n : ℕ) (hn : 0 < n) (f : Polynomial R) → f ∈ range(expand R n) ↔ ∀ i, ¬(n ∣ i) → f.coeff i = 0`
- **What**: Characterises expand-n range membership: a polynomial is in R[X^n] iff all coefficients at non-multiple-of-n indices vanish.
- **How**: Forward: `Polynomial.coeff_expand hn` + `if_neg`. Backward: construct witness `Polynomial.contract n f` using `Polynomial.coeff_contract`.
- **Hypotheses**: CommSemiring, n > 0
- **Uses from project**: []
- **Used by**: `mem_expand_range_of_mul_mem_of_const_ne_zero`, `mem_expand_range_of_mul_mem_expand_range`
- **Visibility**: public
- **Lines**: 996–1009, proof ~13 lines

---

### `theorem mem_expand_range_of_mul_mem_of_const_ne_zero`
- **Type**: `[CommRing R] [IsDomain R] (n : ℕ) (hn : 0 < n) {b c} → b ∈ range(expand n) → b.coeff 0 ≠ 0 → b * c ∈ range(expand n) → c ∈ range(expand n)`
- **What**: If b ∈ R[X^n] has nonzero constant term and b*c ∈ R[X^n], then c ∈ R[X^n].
- **How**: Strong induction on coefficient index i using `Nat.strong_induction_on`. For each i not divisible by n, decomposes `(b*c).coeff i = 0` via `Polynomial.coeff_mul`; pairs with j1 ≠ 0 use `hb_mem` or IH for j2 < i; the (0,i) pair gives `b.coeff 0 * c.coeff i = 0`, resolved by `hb_zero_ne`.
- **Hypotheses**: integral domain, n > 0, b ∈ expand-n range, b.coeff 0 ≠ 0
- **Uses from project**: [`mem_expand_range_iff_coeff_zero`]
- **Used by**: `mem_expand_range_of_mul_mem_expand_range`
- **Visibility**: public
- **Lines**: 1014–1055, proof **42 lines**
- **Notes**: proof >30 lines

---

### `theorem mem_expand_range_of_mul_mem_expand_range`
- **Type**: `[CommRing R] [IsDomain R] (n : ℕ) (hn : 0 < n) {b c} → b ∈ range(expand n) → b ≠ 0 → b * c ∈ range(expand n) → c ∈ range(expand n)`
- **What**: Generalisation: if b ∈ R[X^n], b ≠ 0, and b*c ∈ R[X^n], then c ∈ R[X^n]. Handles the case where b's lowest nonzero coefficient is at index n*m₀ > 0 by shifting the induction by m₀.
- **How**: Uses `Polynomial.natTrailingDegree` to find m₀ = lowest index of nonzero coeff; strong induction on i via coefficient analysis; `Polynomial.coeff_eq_zero_of_lt_natTrailingDegree` for j1 < m₀; integral-domain cancellation at (m₀, i).
- **Hypotheses**: integral domain, n > 0, b ∈ expand-n range, b ≠ 0
- **Uses from project**: [`mem_expand_range_iff_coeff_zero`]
- **Used by**: `mem_expand_range_of_isCoprime_witness`
- **Visibility**: public
- **Lines**: 1064–1124, proof **61 lines**
- **Notes**: proof >30 lines

---

### `theorem aeval_x_gen_injective`
- **Type**: `[Field K] [DecidableEq K] [IsElliptic] → Function.Injective (Polynomial.aeval (x_gen W) : Polynomial K →ₐ[K] FunctionField W)`
- **What**: `aeval x_gen` is injective on K[X], a consequence of the transcendence of x_gen over K.
- **How**: One-liner: `transcendental_iff_injective.mp (x_gen_transcendental W)`.
- **Hypotheses**: IsElliptic
- **Uses from project**: [`x_gen_transcendental`, `x_gen`]
- **Used by**: `function_field_rational_to_K_X_eq`
- **Visibility**: public
- **Lines**: 1129–1134, proof 1 line

---

### `theorem function_field_rational_to_K_X_eq`
- **Type**: `[Field K] [DecidableEq K] [IsElliptic] [CharP K p] (k : ℕ) (h_phi ...) (h_psi ...) → ∃ f s : Polynomial K, expand K (p^k) s ≠ 0 ∧ W.Φ (p^k) * (expand K (p^k) s) = W.ΨSq (p^k) * (expand K (p^k) f)`
- **What**: Lifts the function-field adjoin-membership result to a K[X]-level polynomial equation: the ratio Φ_{p^k}/ΨSq_{p^k} = (expand r)/(expand s) implies cross-multiplication identity in K[X].
- **How**: Uses `mulByInt_pow_pullback_x_gen_mem_adjoin_pow_of_base` + `IntermediateField.mem_adjoin_simple_iff`; rewrites via `Φ_ff_eq_aeval_x_gen`, `ΨSq_ff_eq_aeval_x_gen`, `Polynomial.expand_aeval`; cross-multiplies with `div_eq_div_iff`; lifts to K[X] via `aeval_x_gen_injective`; handles s=0 contradiction via `mulByInt_x_ne_zero`.
- **Hypotheses**: K field with char p, IsElliptic, Φ_p/ΨSq_p in expand-p range
- **Uses from project**: [`mulByInt_pow_pullback_x_gen_mem_adjoin_pow_of_base`, `Φ_ff_eq_aeval_x_gen`, `ΨSq_ff_eq_aeval_x_gen`, `aeval_x_gen_injective`, `mulByInt_pullback_x`, `Φ_ff`, `ΨSq_ff`, `mulByInt_x_ne_zero`, `ΨSq_ff_ne_zero`, `x_gen`]
- **Used by**: `Φ_pow_mem_expand_pow_charP`
- **Visibility**: public
- **Lines**: 1150–1219, proof **70 lines**
- **Notes**: proof >30 lines

---

### `theorem mem_expand_range_of_isCoprime_witness`
- **Type**: `[CommRing R] [IsDomain R] (n : ℕ) (hn : 0 < n) {Φ Ψ} → Ψ ≠ 0 → IsCoprime Φ Ψ → {f g} → Φ * (expand n g) = Ψ * (expand n f) → (∃ h, h ≠ 0 ∧ h ∈ range(expand n) ∧ expand n f = Φ * h ∧ expand n g = Ψ * h) → Φ ∈ range(expand n) ∧ Ψ ∈ range(expand n)`
- **What**: The bridge lemma (Pieces 5+6): given coprime Φ, Ψ and a divisibility witness h ∈ expand-n range, both Φ and Ψ lie in the expand-n range.
- **How**: Extracts h; applies `mem_expand_range_of_mul_mem_expand_range` twice (once for `h * Φ = expand n f`, once for `h * Ψ = expand n g`).
- **Hypotheses**: integral domain, coprimality, divisibility witness in expand-n range
- **Uses from project**: [`mem_expand_range_of_mul_mem_expand_range`]
- **Used by**: `Φ_pow_mem_expand_pow_charP`
- **Visibility**: public
- **Lines**: 1254–1276, proof ~22 lines

---

### `theorem expand_gcd_associated`
- **Type**: `[Field K] [DecidableEq K] (n : ℕ) (a b : Polynomial K) → Associated (expand K n (gcd a b)) (gcd (expand K n a) (expand K n b))`
- **What**: `expand n` commutes with gcd up to associates: gcd of expanded polynomials is associated to the expanded gcd.
- **How**: `associated_of_dvd_dvd`: expand n (gcd a b) divides gcd (expand a, expand b) via `map_dvd`; converse via Bézout `gcd_eq_gcd_ab` and `map_add`/`map_mul`.
- **Hypotheses**: Field K (so K[X] is Euclidean domain)
- **Uses from project**: []
- **Used by**: `h_witness_in_expand_range`
- **Visibility**: public
- **Lines**: 1285–1308, proof ~23 lines

---

### `theorem mem_expand_range_of_associated`
- **Type**: `[Field K] (n : ℕ) {a b : Polynomial K} → Associated a b → b ∈ range(expand K n) → a ∈ range(expand K n)`
- **What**: The expand-n range of K[X] is closed under associates (units of K[X] are nonzero constants, which are in range(expand n) via `Polynomial.expand_C`).
- **How**: From `h_assoc.symm` gets `b * v = a`; decomposes unit v as nonzero constant via `Polynomial.isUnit_iff`; constructs witness `b' * C c`.
- **Hypotheses**: Field K
- **Uses from project**: []
- **Used by**: `h_witness_in_expand_range`
- **Visibility**: public
- **Lines**: 1314–1325, proof ~11 lines

---

### `theorem h_witness_in_expand_range`
- **Type**: `[Field K] [DecidableEq K] {n} {Φ Ψ} → Ψ ≠ 0 → IsCoprime Φ Ψ → {f s} → expand K n s ≠ 0 → Φ * (expand n s) = Ψ * (expand n f) → ∃ h, h ≠ 0 ∧ h ∈ range(expand n) ∧ expand n f = Φ * h ∧ expand n s = Ψ * h`
- **What**: The gcd argument: given coprimality and cross-multiplication equation, the divisibility witness h lies in the expand-n range. The witness h is the GCD of Φ*h and Ψ*h, which by Bézout equals h; while gcd(expand n f, expand n s) ∼ expand n (gcd f s) via `expand_gcd_associated`.
- **How**: Uses `isCoprime_eq_mul_factor_of_eq_mul` to extract h; builds Bézout-derived `gcd(Φh,Ψh) ∼ h`; uses `expand_gcd_associated` + `mem_expand_range_of_associated`.
- **Hypotheses**: Field K, coprimality, nonzero denominator
- **Uses from project**: [`isCoprime_eq_mul_factor_of_eq_mul`, `expand_gcd_associated`, `mem_expand_range_of_associated`]
- **Used by**: `Φ_pow_mem_expand_pow_charP`
- **Visibility**: public
- **Lines**: 1333–1378, proof **46 lines**
- **Notes**: proof >30 lines

---

### `theorem Φ_pow_mem_expand_pow_charP`
- **Type**: `[Field K] [DecidableEq K] [IsElliptic] [CharP K p] (k : ℕ) (h_phi ...) (h_psi ...) → W.Φ (p^k) ∈ range(expand K (p^k)) ∧ W.ΨSq (p^k) ∈ range(expand K (p^k))`
- **What**: The main universal-in-p deliverable (Silverman III.6.2 polynomial form): if Φ_p, ΨSq_p ∈ R[X^p], then Φ_{p^k}, ΨSq_{p^k} ∈ R[X^{p^k}] for all k.
- **How**: Chains: `function_field_rational_to_K_X_eq` (extract K[X] witnesses); `W.isCoprime_Φ_ΨSq` (coprimality); `W.natDegree_Φ_pos` (deduce ΨSq ≠ 0); `h_witness_in_expand_range` (gcd argument); `mem_expand_range_of_isCoprime_witness` (final conclusion).
- **Hypotheses**: K field with char p, IsElliptic, Φ_p/ΨSq_p ∈ expand-p range
- **Uses from project**: [`function_field_rational_to_K_X_eq`, `h_witness_in_expand_range`, `mem_expand_range_of_isCoprime_witness`, `isCoprime_Φ_ΨSq`, `natDegree_Φ_pos`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1394–1425, proof **32 lines**
- **Notes**: proof >30 lines (32 lines)

---

### `theorem mulByInt_card_pullback_x_gen_mem_adjoin_pow_card_of_base`
- **Type**: `[Field K] [Fintype K] [DecidableEq K] [IsElliptic] [CharP K p] (h_phi ...) (h_psi ...) → (mulByInt W.toAffine (Fintype.card K : ℕ)).pullback (x_gen W) ∈ adjoin K {x_gen W ^ (Fintype.card K : ℕ)}`
- **What**: K-level corollary: for a finite field K with `Fintype.card K = p^n`, the [card K]-pullback of x_gen lies in K(x_gen^{card K}).
- **How**: Uses `FiniteField.card K p` to get `n` with `Fintype.card K = p^n`; specialises `mulByInt_pow_pullback_x_gen_mem_adjoin_pow_of_base` at `k = n`.
- **Hypotheses**: K finite field with char p; Φ_p, ΨSq_p ∈ expand-p range; IsElliptic
- **Uses from project**: [`mulByInt_pow_pullback_x_gen_mem_adjoin_pow_of_base`, `x_gen`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1431–1442, proof ~11 lines

---

### `noncomputable def universalCurve`
- **Type**: `(p : ℕ) → [Fact p.Prime] → WeierstrassCurve (URing p)` with `aᵢ := Uaᵢ p`
- **What**: The universal Weierstrass curve over `URing p = MvPolynomial AVar (ZMod p)` with coefficients equal to the universal variables. The universal Φ_q, ΨSq_q are obtained by applying mathlib's division polynomial constructions to this curve.
- **How**: Structure construction.
- **Hypotheses**: `p` prime
- **Uses from project**: [`URing`, `Ua1`, `Ua2`, `Ua3`, `Ua4`, `Ua6`]
- **Used by**: `universalCurve_Φ_two_mem_expand_two`, `universalCurve_ΨSq_two_mem_expand_two`, `universalCurve_Ψ₃_mem_expand_three`, `universalCurve_ΨSq_three_mem_expand_three`, `universalCurve_Φ_three_mem_expand_three`
- **Visibility**: public
- **Lines**: 1520–1525

---

### `theorem universalCurve_Φ_two_mem_expand_two`
- **Type**: `(universalCurve 2).Φ 2 ∈ Set.range (Polynomial.expand (URing 2) 2)` (with local `Fact (Nat.Prime 2)`)
- **What**: Universal Φ_2 ∈ expand 2 range over URing 2, as direct corollary of `Φ_two_mem_expand_two_charP`.
- **How**: Direct application of `Φ_two_mem_expand_two_charP` to `universalCurve 2`.
- **Hypotheses**: none
- **Uses from project**: [`universalCurve`, `Φ_two_mem_expand_two_charP`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1530–1534, proof 1 line

---

### `theorem universalCurve_ΨSq_two_mem_expand_two`
- **Type**: `(universalCurve 2).ΨSq 2 ∈ Set.range (Polynomial.expand (URing 2) 2)` (with local `Fact (Nat.Prime 2)`)
- **What**: Universal ΨSq_2 ∈ expand 2 range over URing 2.
- **How**: Direct application of `ΨSq_two_mem_expand_two_charP`.
- **Hypotheses**: none
- **Uses from project**: [`universalCurve`, `ΨSq_two_mem_expand_two_charP`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1538–1542, proof 1 line

---

### `theorem universalCurve_Ψ₃_mem_expand_three`
- **Type**: `(universalCurve 3).Ψ₃ ∈ Set.range (Polynomial.expand (URing 3) 3)` (with local `Fact (Nat.Prime 3)`)
- **What**: Universal Ψ₃ ∈ expand 3 range over URing 3.
- **How**: Direct application of `Ψ₃_mem_expand_three_charP`.
- **Hypotheses**: none
- **Uses from project**: [`universalCurve`, `Ψ₃_mem_expand_three_charP`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1546–1550, proof 1 line

---

### `theorem universalCurve_ΨSq_three_mem_expand_three`
- **Type**: `(universalCurve 3).ΨSq 3 ∈ Set.range (Polynomial.expand (URing 3) 3)` (with local `Fact (Nat.Prime 3)`)
- **What**: Universal ΨSq_3 ∈ expand 3 range over URing 3.
- **How**: Direct application of `ΨSq_three_mem_expand_three_charP`.
- **Hypotheses**: none
- **Uses from project**: [`universalCurve`, `ΨSq_three_mem_expand_three_charP`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1554–1558, proof 1 line

---

### `theorem universalCurve_Φ_three_mem_expand_three`
- **Type**: `(universalCurve 3).Φ 3 ∈ Set.range (Polynomial.expand (URing 3) 3)` (with local `Fact (Nat.Prime 3)`)
- **What**: Universal Φ_3 ∈ expand 3 range over URing 3.
- **How**: Direct application of `Φ_three_mem_expand_three_charP`.
- **Hypotheses**: none
- **Uses from project**: [`universalCurve`, `Φ_three_mem_expand_three_charP`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1562–1566, proof 1 line

---

## Summary statistics

| Category | Count |
|---|---|
| Total declarations | 70 |
| Defs (inductive/abbrev/def/noncomputable def) | 22 |
| Theorems | 48 |
| Instances | 0 |
| Sorries | 0 |
| set_option maxHeartbeats | 0 |
| Proofs > 30 lines | 6 |
| Unused in file (dead-code candidates) | 28 |

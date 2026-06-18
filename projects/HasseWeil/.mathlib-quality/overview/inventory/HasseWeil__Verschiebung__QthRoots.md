# Inventory: ./HasseWeil/Verschiebung/QthRoots.lean

**File overview**: Constructs polynomial-level q-th-root extractors and uses them to show that the [q]-multiplication pullbacks of `x_gen` and `y_gen` lie in the Frobenius pullback range (`Im(π*)`), for small q = p^k in characteristic p. This is a key step toward the Verschiebung construction (III.6.2 inclusion `Im([q]*) ⊆ Im(π*)`). The file fully closes the q=2 char=2 case and develops significant scaffolding for q=3 char=3.

---

## Declarations

---

### `noncomputable def polyExpandRoot`
- **Type**: `(f : Polynomial K) → f ∈ Set.range (⇑(Polynomial.expand K (Fintype.card K))) → Polynomial K`
- **What**: Given a polynomial `f` in the range of `expand K q`, extracts a "q-th root polynomial" `f'` with `expand q f' = f`, i.e., `f'(X^q) = f(X)`.
- **How**: Pure `Classical.choose` on the `Set.range` membership hypothesis.
- **Hypotheses**: `K` is a finite field.
- **Uses from project**: none
- **Used by**: `polyExpandRoot_spec`, `polyExpandRoot_aeval_pow_eq`, `alpha_1_y_qth_root_char_two`, `alpha_0_y_qth_root_char_two`, `alpha_1_y_qth_root_pow_card_eq`, `alpha_0_y_qth_root_pow_card_eq`
- **Visibility**: public
- **Lines**: 82–85; proof length: 1
- **Notes**: none

---

### `theorem polyExpandRoot_spec`
- **Type**: `(f : Polynomial K) → (hf : f ∈ Set.range (⇑(Polynomial.expand K (Fintype.card K)))) → Polynomial.expand K (Fintype.card K) (polyExpandRoot f hf) = f`
- **What**: States the defining equation of `polyExpandRoot`: applying expand gives back `f`.
- **How**: `hf.choose_spec` directly.
- **Hypotheses**: Same as `polyExpandRoot`.
- **Uses from project**: `polyExpandRoot`
- **Used by**: `polyExpandRoot_aeval_pow_eq`
- **Visibility**: public
- **Lines**: 88–91; proof length: 1
- **Notes**: none

---

### `def PolyPowCardEq`
- **Type**: `(K : Type*) → [Field K] → [Fintype K] → Prop`
- **What**: The statement `∀ f : K[X], f^q = expand q f` (polynomial Frobenius identity).
- **How**: Pure `Prop` definition, no proof.
- **Hypotheses**: none (just a Prop)
- **Uses from project**: none
- **Used by**: `polyPowCardEq_of_finite`, `polyExpandRoot_aeval_pow_eq`, `mulByInt_q_pullback_x_gen_qth_root_of_expand_witness`
- **Visibility**: public
- **Lines**: 102–103
- **Notes**: This is essentially `Polynomial.expand_eq_pow_card` or similar in mathlib; the file provides its own unconditional proof via `polyPowCardEq_of_finite`.

---

### `theorem polyPowCardEq_of_finite`
- **Type**: `PolyPowCardEq K`
- **What**: Proves the polynomial Frobenius identity `f^q = expand q f` for all `f ∈ K[X]` over a finite field K of cardinality q = p^n.
- **How**: Extracts `(p, n)` via `FiniteField.card'`, uses `add_pow_expChar_pow` for the sum case, and `FiniteField.pow_card` + `expand_C/X` for the monomial case via polynomial induction.
- **Hypotheses**: `K` finite field.
- **Uses from project**: none (pure mathlib)
- **Used by**: `mulByInt_q_pullback_x_gen_qth_root_of_expand_witness`, `mulByInt_two_pullback_y_gen_sq_root_unconditional`; also called inside `polyExpandRoot_aeval_pow_eq`, `alpha_1_y_qth_root_pow_card_eq`, `alpha_0_y_qth_root_pow_card_eq`
- **Visibility**: public
- **Lines**: 113–130; proof length: 18
- **Notes**: none

---

### `theorem polyExpandRoot_aeval_pow_eq`
- **Type**: `(f : Polynomial K) → (hf : ...) → (h_pow : PolyPowCardEq K) → (z : W.toAffine.FunctionField) → (Polynomial.aeval z (polyExpandRoot f hf))^q = Polynomial.aeval z f`
- **What**: Transports the polynomial identity to the function field: the q-th power of `aeval z f'` equals `aeval z f`.
- **How**: Rewrites via `map_pow`, `h_pow`, and `polyExpandRoot_spec`.
- **Hypotheses**: Finite field, a polynomial Frobenius identity witness.
- **Uses from project**: `polyExpandRoot`, `polyExpandRoot_spec`
- **Used by**: `mulByInt_q_pullback_x_gen_qth_root_of_expand_witness`, `alpha_1_y_qth_root_pow_card_eq`, `alpha_0_y_qth_root_pow_card_eq`
- **Visibility**: public
- **Lines**: 141–149; proof length: 4

---

### `theorem Φ_two_mem_expand_two_char_two`
- **Type**: `(W : WeierstrassCurve K) → [CharP K 2] → W.Φ 2 ∈ Set.range (⇑(Polynomial.expand K 2))`
- **What**: K-level (char 2) specialisation that `Φ_2 ∈ K[X^2]`.
- **How**: Delegates to `Φ_two_mem_expand_two_charP` from `DivPolyExpand`.
- **Hypotheses**: char 2.
- **Uses from project**: `Φ_two_mem_expand_two_charP` (DivPolyExpand)
- **Used by**: `mulByInt_two_pullback_x_gen_sq_root_unconditional`
- **Visibility**: public
- **Lines**: 160–163; proof length: 1

---

### `theorem Ψ₃_mem_expand_three_char_three`
- **Type**: `(W : WeierstrassCurve K) → [CharP K 3] → W.Ψ₃ ∈ Set.range (⇑(Polynomial.expand K 3))`
- **What**: K-level char-3 fact that `Ψ₃ ∈ K[X^3]`.
- **How**: Delegates to `Ψ₃_mem_expand_three_charP` from `DivPolyExpand`.
- **Hypotheses**: char 3.
- **Uses from project**: `Ψ₃_mem_expand_three_charP` (DivPolyExpand)
- **Used by**: unused in this file (exported for use elsewhere)
- **Visibility**: public
- **Lines**: 176–179; proof length: 1

---

### `theorem ΨSq_three_mem_expand_three_char_three`
- **Type**: `(W : WeierstrassCurve K) → [CharP K 3] → W.ΨSq 3 ∈ Set.range (⇑(Polynomial.expand K 3))`
- **What**: K-level char-3 fact that `ΨSq_3 ∈ K[X^3]`.
- **How**: Delegates to `ΨSq_three_mem_expand_three_charP` from `DivPolyExpand`.
- **Hypotheses**: char 3.
- **Uses from project**: `ΨSq_three_mem_expand_three_charP` (DivPolyExpand)
- **Used by**: `mulByInt_three_pullback_x_gen_cube_root_unconditional`
- **Visibility**: public
- **Lines**: 183–186; proof length: 1

---

### `theorem b_relation_of_char_three`
- **Type**: `(W : WeierstrassCurve K) → [CharP K 3] → W.b₈ = W.b₂ * W.b₆ - W.b₄^2`
- **What**: Char-3 b-relation identity.
- **How**: Delegates to `b_relation_of_charP_three` from `DivPolyExpand`.
- **Hypotheses**: char 3.
- **Uses from project**: `b_relation_of_charP_three` (DivPolyExpand)
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 190–193; proof length: 1

---

### `theorem Φ_three_mem_expand_three_char_three`
- **Type**: `(W : WeierstrassCurve K) → [CharP K 3] → W.Φ 3 ∈ Set.range (⇑(Polynomial.expand K 3))`
- **What**: K-level char-3 fact that `Φ_3 ∈ K[X^3]`.
- **How**: Delegates to `Φ_three_mem_expand_three_charP` from `DivPolyExpand`.
- **Hypotheses**: char 3.
- **Uses from project**: `Φ_three_mem_expand_three_charP` (DivPolyExpand)
- **Used by**: `mulByInt_three_pullback_x_gen_cube_root_unconditional`
- **Visibility**: public
- **Lines**: 199–202; proof length: 1

---

### `theorem mulByInt_q_pullback_x_gen_qth_root_of_expand_witness`
- **Type**: Given `h_Φ`, `h_ΨSq` (expand-range memberships) and `hn : q ≠ 0`, produces `∃ g, g^q = (mulByInt W q).pullback (x_gen W)`.
- **What**: From polynomial-level expand-range witnesses for `Φ_q` and `ΨSq_q`, constructs an explicit q-th root of `[q]^* x_gen` in `K(E)`.
- **How**: Sets `g = aeval x_gen Φ' / aeval x_gen ΨSq'`, applies `polyExpandRoot_aeval_pow_eq` twice, identifies `aeval x_gen` with `Φ_ff`/`ΨSq_ff` via `Polynomial.aeval_algebraMap_apply`, then uses `mulByInt_pullback_x`.
- **Hypotheses**: `Φ_q` and `ΨSq_q` in expand-range; `q ≠ 0 : ℤ`; finite field.
- **Uses from project**: `polyExpandRoot`, `polyPowCardEq_of_finite`, `polyExpandRoot_aeval_pow_eq`, `Φ_ff`, `ΨSq_ff`, `mulByInt_pullback_x`, `x_gen`
- **Used by**: `mulByInt_three_pullback_x_gen_cube_root_unconditional`, `mulByInt_two_pullback_x_gen_sq_root_unconditional`
- **Visibility**: public
- **Lines**: 211–265; proof length: 55
- **Notes**: proof >30 lines

---

### `theorem mulByInt_q_pullback_y_gen_qth_root_of_witness`
- **Type**: Given `h_y : ∃ g, g^q = mulByInt_y W q` and `hn`, produces `∃ g, g^q = (mulByInt W q).pullback (y_gen W)`.
- **What**: Transports a q-th root of `mulByInt_y W q` through `mulByInt_pullback_y` to a q-th root of `[q]^* y_gen`.
- **How**: `obtain ⟨g, hg⟩`, refine, rewrite via `mulByInt_pullback_y`.
- **Hypotheses**: A q-th root of `mulByInt_y W q` exists; `q ≠ 0 : ℤ`.
- **Uses from project**: `mulByInt_y`, `mulByInt_pullback_y`, `y_gen`
- **Used by**: `mulByInt_q_pullback_y_gen_mem_range_of_sqrid_witness`, `mulByInt_two_pullback_y_gen_sq_root_unconditional`
- **Visibility**: public
- **Lines**: 279–292; proof length: 9

---

### `theorem ΨSq_two_mem_expand_two_char_two`
- **Type**: `(W : WeierstrassCurve K) → [CharP K 2] → W.ΨSq 2 ∈ Set.range (⇑(Polynomial.expand K 2))`
- **What**: K-level char-2 specialisation that `ΨSq_2 ∈ K[X^2]`.
- **How**: Delegates to `ΨSq_two_mem_expand_two_charP` from `DivPolyExpand`.
- **Hypotheses**: char 2.
- **Uses from project**: `ΨSq_two_mem_expand_two_charP` (DivPolyExpand)
- **Used by**: `mulByInt_two_pullback_x_gen_sq_root_unconditional`
- **Visibility**: public
- **Lines**: 296–299; proof length: 1

---

### `noncomputable def omega2_Y_coeff_char_two`
- **Type**: `(W : WeierstrassCurve K) → Polynomial K`
- **What**: Defines the Y-coefficient of `ω 2` in the `{1, Y}` basis in char 2: `a₁·Ψ₃ + (a₁X + a₃)^3`.
- **How**: Explicit formula.
- **Hypotheses**: none
- **Uses from project**: none (uses `WeierstrassCurve.Ψ₃` implicitly via `W.Ψ₃`)
- **Used by**: `omega2_Y_coeff_mem_expand_two_char_two`, `omega2_coupled_residual_char_two`, `omegaTwoBasisHolds_char_two`, `OmegaTwoBasisHolds`, `alpha_1_y_qth_root_char_two`, `alpha_1_y_qth_root_pow_card_eq`, `alpha_1_sq_psi_eq_B_div_psi_cubed_of_witness`, `alpha_0_sq_polynomial_match_char_two`, `y_qth_root_squared_eq_mulByInt_y_two_of_witnesses`, `mulByInt_two_pullback_y_gen_sq_root_unconditional`
- **Visibility**: public
- **Lines**: 317–320
- **Notes**: keyApi candidate (used by 10+ others)

---

### `theorem omega2_Y_coeff_mem_expand_two_char_two`
- **Type**: `(W : WeierstrassCurve K) → [CharP K 2] → omega2_Y_coeff_char_two W ∈ Set.range (⇑(Polynomial.expand K 2))`
- **What**: Proves the Y-coefficient of `ω₂` lies in `K[X^2]` in char 2, by exhibiting an explicit witness and showing the difference is a multiple of 2 via `linear_combination`.
- **How**: Provides an explicit polynomial witness; uses char-2 reductions `b₂ = a₁²`, `b₆ = a₃²` (from `WeierstrassCurve.Ψ₃`) and `linear_combination` with explicit 2-multiples.
- **Hypotheses**: char 2.
- **Uses from project**: `omega2_Y_coeff_char_two`
- **Used by**: `alpha_1_y_qth_root_char_two`, `alpha_1_y_qth_root_pow_card_eq`, `alpha_1_sq_psi_eq_B_div_psi_cubed_of_witness`, `alpha_0_sq_polynomial_match_char_two`, `y_qth_root_squared_eq_mulByInt_y_two_of_witnesses`, `mulByInt_two_pullback_y_gen_sq_root_unconditional`
- **Visibility**: public
- **Lines**: 327–357; proof length: 31
- **Notes**: proof >30 lines

---

### `noncomputable def omega2_X_coeff_char_two`
- **Type**: `(W : WeierstrassCurve K) → Polynomial K`
- **What**: Defines the 1-coefficient (constant-in-Y term) of `ω 2` in the `{1, Y}` basis in char 2.
- **How**: Explicit formula: `(X² + a₁²X + a₁a₃ + a₄)·Ψ₃ + (a₁X + a₃)^4`.
- **Hypotheses**: none
- **Uses from project**: none directly
- **Used by**: `omega2_coupled_residual_char_two`, `omegaTwoBasisHolds_char_two`, `OmegaTwoBasisHolds`, `alpha_0_sq_polynomial_match_char_two`, `y_qth_root_squared_eq_mulByInt_y_two_of_witnesses`
- **Visibility**: public
- **Lines**: 386–390

---

### `noncomputable def cubic_x`
- **Type**: `(W : WeierstrassCurve K) → Polynomial K`
- **What**: Defines `X³ + a₂X² + a₄X + a₆`, the "cubic part" of the Weierstrass equation.
- **How**: Explicit formula.
- **Hypotheses**: none
- **Uses from project**: none
- **Used by**: `omega2_coupled_residual_char_two`, `omega3_coupled_residual_char_three`, `omega3_coupled_residual_full_char_three`, `omega_3_X_coeff_reduced_char_three`, `omega_3_Y_coeff_reduced_char_three`, `omega2_coupled_residual_derivative_eq_zero`, `y_gen_sq_mul_basis_form_char_three`, `y_gen_cubed_mul_basis_form_char_three`, `y_gen_quartic_mul_basis_form_char_three`, `y_gen_quintic_mul_basis_form_char_three`, `alpha_cubed_basis_form_char_three`, `psi_2_sq_plus_cubic_x_form_char_three`
- **Visibility**: public
- **Lines**: 394–396
- **Notes**: keyApi candidate (used by many)

---

### `noncomputable def omega2_coupled_residual_char_two`
- **Type**: `(W : WeierstrassCurve K) → Polynomial K`
- **What**: Defines `A·ψ₂ + B·cubic_x` (the "coupled residual"), which must lie in `K[X^2]` for the y-side square root construction.
- **How**: Explicit formula combining `omega2_X_coeff_char_two`, `omega2_Y_coeff_char_two`, and `cubic_x`.
- **Hypotheses**: none
- **Uses from project**: `omega2_X_coeff_char_two`, `omega2_Y_coeff_char_two`, `cubic_x`
- **Used by**: `omega2_coupled_residual_mem_expand_two_char_two_witness`, `omega2_coupled_residual_derivative_eq_zero`, `omega2_coupled_residual_mem_expand_two_char_two`, `alpha_0_y_qth_root_char_two`, `alpha_0_y_qth_root_pow_card_eq`, `alpha_0_sq_polynomial_match_char_two`, `y_qth_root_squared_eq_mulByInt_y_two_of_witnesses`, `mulByInt_two_pullback_y_gen_sq_root_unconditional`
- **Visibility**: public
- **Lines**: 401–405

---

### `noncomputable def omega2_coupled_witness_char_two`
- **Type**: `(W : WeierstrassCurve K) → Polynomial K`
- **What**: Explicit sympy-derived witness polynomial `g` such that `expand 2 g = omega2_coupled_residual_char_two W` in char 2.
- **How**: Explicit coefficient formula (sympy-extracted).
- **Hypotheses**: none
- **Uses from project**: none
- **Used by**: `omega2_coupled_residual_mem_expand_two_char_two_witness` (ONLY)
- **Visibility**: public
- **Lines**: 412–426
- **Notes**: This approach was superseded by the derivative-vanishes route; this def is only used by the witness-parametric theorem.

---

### `noncomputable def omega2_coupled_multiplier_char_two`
- **Type**: `(W : WeierstrassCurve K) → Polynomial K`
- **What**: The sympy-derived multiplier polynomial M(X) with `omega2_coupled_residual - expand 2 witness = 2·M(X)`.
- **How**: Explicit coefficient formula (sympy-extracted, degree 7).
- **Hypotheses**: none
- **Uses from project**: none
- **Used by**: unused in file (parked/experimental)
- **Visibility**: public
- **Lines**: 432–462
- **Notes**: Dead code in this file — referenced only in comments. Likely parked.

---

### `theorem omega2_coupled_residual_mem_expand_two_char_two_witness`
- **Type**: `(W : WeierstrassCurve K) → [CharP K 2] → (h_witness : expand 2 (omega2_coupled_witness_char_two W) = omega2_coupled_residual_char_two W) → omega2_coupled_residual_char_two W ∈ Set.range (⇑(Polynomial.expand K 2))`
- **What**: Deduces the coupled residual lies in expand-range from a witness equality; witness-parametric version.
- **How**: Trivial: `⟨omega2_coupled_witness_char_two W, h_witness⟩`.
- **Hypotheses**: char 2 + witness hypothesis.
- **Uses from project**: `omega2_coupled_residual_char_two`, `omega2_coupled_witness_char_two`
- **Used by**: unused in this file (superseded by unconditional version)
- **Visibility**: public
- **Lines**: 476–481; proof length: 1
- **Notes**: Superseded by `omega2_coupled_residual_mem_expand_two_char_two`.

---

### `theorem omega2_coupled_residual_derivative_eq_zero` (set_option maxHeartbeats 1000000)
- **Type**: `(W : WeierstrassCurve K) → [CharP K 2] → Polynomial.derivative (omega2_coupled_residual_char_two W) = 0`
- **What**: Proves the derivative of the coupled residual vanishes in char 2 (every nonzero coefficient is at even degree).
- **How**: Substitutes char-2 b-relation simplifications (`b₂_of_char_two`, `b₄_of_char_two`, `b₆_of_char_two`), unfolds the polynomial, applies `simp` for derivatives and `reduce_mod_char!`, then `ring_nf` + second `reduce_mod_char!`.
- **Hypotheses**: char 2.
- **Uses from project**: `omega2_coupled_residual_char_two`, `omega2_X_coeff_char_two`, `omega2_Y_coeff_char_two`, `cubic_x`; `WeierstrassCurve.b₂_of_char_two`, `b₄_of_char_two`, `b₆_of_char_two` (project lemmas)
- **Used by**: `omega2_coupled_residual_mem_expand_two_char_two`
- **Visibility**: public
- **Lines**: 490–518; proof length: 29
- **Notes**: `set_option maxHeartbeats 1000000` (NO justifying comment); uses `reduce_mod_char!` twice.

---

### `theorem omega2_coupled_residual_mem_expand_two_char_two`
- **Type**: `(W : WeierstrassCurve K) → [CharP K 2] → omega2_coupled_residual_char_two W ∈ Set.range (⇑(Polynomial.expand K 2))`
- **What**: Unconditionally proves the coupled residual lies in `K[X^2]` in char 2, via the Frobenius criterion `f ∈ expand-range ↔ f' = 0`.
- **How**: Uses `Polynomial.expand_contract 2 (derivative = 0)`, appealing to `omega2_coupled_residual_derivative_eq_zero`.
- **Hypotheses**: char 2.
- **Uses from project**: `omega2_coupled_residual_char_two`, `omega2_coupled_residual_derivative_eq_zero`
- **Used by**: `alpha_0_y_qth_root_char_two`, `alpha_0_y_qth_root_pow_card_eq`, `alpha_0_sq_polynomial_match_char_two`, `y_qth_root_q_eq_2_char_2`, `y_qth_root_squared_eq_mulByInt_y_two_of_witnesses`, `mulByInt_two_pullback_y_gen_sq_root_unconditional`
- **Visibility**: public
- **Lines**: 522–527; proof length: 4

---

### `noncomputable def alpha_1_y_qth_root_char_two`
- **Type**: `(W : WeierstrassCurve K) → [W.toAffine.IsElliptic] → (h_card : Fintype.card K = 2) → (h_B : omega2_Y_coeff_char_two W ∈ Set.range (⇑(Polynomial.expand K 2))) → W.toAffine.FunctionField`
- **What**: Defines the coefficient α₁ of the y-side square root: `aeval x_gen (polyExpandRoot B h_B') / ψ₂(x_gen)²`.
- **How**: Transports the membership via `h_card ▸ h_B`, then divides the extracted polynomial root by the squared ψ₂-evaluation.
- **Hypotheses**: IsElliptic, char 2 (implicit via h_B), `Fintype.card K = 2`.
- **Uses from project**: `polyExpandRoot`, `omega2_Y_coeff_char_two`, `x_gen`
- **Used by**: `alpha_1_y_qth_root_pow_card_eq`, `alpha_1_sq_psi_eq_B_div_psi_cubed_of_witness`, `alpha_0_sq_polynomial_match_char_two`, `y_qth_root_q_eq_2_char_2_of_witnesses`, `y_qth_root_squared_eq_mulByInt_y_two_of_witnesses`
- **Visibility**: public
- **Lines**: 541–550

---

### `noncomputable def alpha_0_y_qth_root_char_two`
- **Type**: similar to `alpha_1_y_qth_root_char_two` but for `omega2_coupled_residual_char_two`
- **What**: Defines α₀ of the y-side square root: `aeval x_gen (polyExpandRoot AB h_AB') / ψ₂(x_gen)²`.
- **How**: Same pattern as `alpha_1_y_qth_root_char_two`.
- **Hypotheses**: IsElliptic, `Fintype.card K = 2`, coupled-residual in expand-range.
- **Uses from project**: `polyExpandRoot`, `omega2_coupled_residual_char_two`, `x_gen`
- **Used by**: `y_qth_root_q_eq_2_char_2_of_witnesses`, `alpha_0_sq_polynomial_match_char_two`, `y_qth_root_squared_eq_mulByInt_y_two_of_witnesses`
- **Visibility**: public
- **Lines**: 554–564

---

### `noncomputable def y_qth_root_q_eq_2_char_2_of_witnesses`
- **Type**: `(W : WeierstrassCurve K) → [IsElliptic] → (h_card : card K = 2) → (h_B h_AB : ...) → W.toAffine.FunctionField`
- **What**: Defines `α = α₀ + α₁·y_gen ∈ K(E)`, parametric on the two expand-range witnesses.
- **How**: `alpha_0_y_qth_root_char_two W h_card h_AB + alpha_1_y_qth_root_char_two W h_card h_B * y_gen W`
- **Hypotheses**: IsElliptic, card K = 2, both expand-range witnesses.
- **Uses from project**: `alpha_0_y_qth_root_char_two`, `alpha_1_y_qth_root_char_two`, `y_gen`
- **Used by**: `y_qth_root_q_eq_2_char_2`; also `y_qth_root_squared_eq_mulByInt_y_two_of_witnesses` (via `y_qth_root_q_eq_2_char_2`)
- **Visibility**: public
- **Lines**: 568–575

---

### `noncomputable def y_qth_root_q_eq_2_char_2`
- **Type**: `(W : WeierstrassCurve K) → [IsElliptic] → [CharP K 2] → (h_card : card K = 2) → W.toAffine.FunctionField`
- **What**: Unconditional (char-2-specific) definition of α = α₀ + α₁·y_gen.
- **How**: Calls `y_qth_root_q_eq_2_char_2_of_witnesses` with the now-unconditional witnesses.
- **Hypotheses**: IsElliptic, char 2, card K = 2.
- **Uses from project**: `y_qth_root_q_eq_2_char_2_of_witnesses`, `omega2_Y_coeff_mem_expand_two_char_two`, `omega2_coupled_residual_mem_expand_two_char_two`
- **Used by**: `mulByInt_q_pullback_y_gen_mem_range_of_sqrid_witness`, `y_qth_root_squared_eq_mulByInt_y_two_of_witnesses`, `mulByInt_two_pullback_y_gen_sq_root_unconditional`
- **Visibility**: public
- **Lines**: 581–587

---

### `theorem frobeniusIsog_pullback_range_inv_mem`
- **Type**: `(f : W.toAffine.FunctionField) → f ∈ (frobeniusIsog W).pullback.range → f⁻¹ ∈ (frobeniusIsog W).pullback.range`
- **What**: The Frobenius pullback range is closed under inverses.
- **How**: Uses `mem_frobenius_range_iff`, then `inv_pow` and the inverse of the q-th-power witness.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `frobeniusIsog`, `mem_frobenius_range_iff` (PurelyInsep)
- **Used by**: `mulByInt_q_pullback_range_subset_frobenius_of_xy_subfield_witness`
- **Visibility**: public
- **Lines**: 598–604; proof length: 5

---

### `theorem mulByInt_q_pullback_range_subset_frobenius_of_xy_subfield_witness`
- **Type**: Given `h_x`, `h_y` (x_gen and y_gen pullbacks in Frobenius range) and `h_subfield` (every z's pullback is in range or is (a+b)/c with a,b,c in range, c≠0), proves every pullback is in range.
- **What**: A structural generator-reduction step: if x_gen and y_gen pullbacks are q-th powers, and K(E) decomposes as a field-fraction of the span, then all pullbacks are q-th powers.
- **How**: Case splits on `h_subfield z`, uses `Subalgebra.add_mem`, `frobeniusIsog_pullback_range_inv_mem`, `Subalgebra.mul_mem`, and `div_eq_mul_inv`.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `frobeniusIsog`, `frobeniusIsog_pullback_range_inv_mem`, `mulByInt`, `x_gen`, `y_gen`
- **Used by**: unused in this file (exported)
- **Visibility**: public
- **Lines**: 619–645; proof length: 27

---

### `theorem mulByInt_q_pullback_y_gen_mem_range_of_sqrid_witness`
- **Type**: Given the squaring identity for the explicit α, produces `∃ g, g^q = (mulByInt W q).pullback (y_gen W)`.
- **What**: Specializes `mulByInt_q_pullback_y_gen_qth_root_of_witness` with `y_qth_root_q_eq_2_char_2` and the squaring identity hypothesis.
- **How**: Direct application.
- **Hypotheses**: IsElliptic, char 2, card K = 2, squaring identity witness, q ≠ 0.
- **Uses from project**: `y_qth_root_q_eq_2_char_2`, `mulByInt_q_pullback_y_gen_qth_root_of_witness`, `mulByInt_y`, `y_gen`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 657–667; proof length: 3

---

### `theorem mulByInt_q_pullback_fieldRange_subset_frobenius_of_xy_witness`
- **Type**: Given `h_top : (⊤ : IntermediateField K K(E)) = adjoin K {x_gen, y_gen}`, plus x and y pullbacks in Frobenius fieldRange, every z's pullback is in Frobenius fieldRange.
- **What**: The IntermediateField-level generator reduction: fullness of K(E) adjoin + x,y in range implies all are in range.
- **How**: Uses `IntermediateField.adjoin_map`, `IntermediateField.adjoin_le_iff`, `Set.image_pair`.
- **Hypotheses**: IsElliptic, `h_top` (IntermediateField equality).
- **Uses from project**: `frobeniusIsog`, `mulByInt`, `x_gen`, `y_gen`
- **Used by**: `mulByInt_two_pullback_fieldRange_subset_frobenius_unconditional`
- **Visibility**: public
- **Lines**: 685–719; proof length: 35
- **Notes**: proof >30 lines

---

### `theorem functionField_eq_intermediateField_adjoin_xy_of_witness`
- **Type**: Given `h_alg_top : ∀ r, algebraMap CR KE r ∈ Algebra.adjoin K {x_gen, y_gen}`, proves `(⊤ : IntermediateField K KE) = IntermediateField.adjoin K {x_gen, y_gen}`.
- **What**: K(E) equals the IntermediateField generated by x_gen and y_gen, parametric on a coordinate-ring witness.
- **How**: Uses `IsLocalization.mk'_surjective` to reduce to fraction quotients, then `IsFractionRing.mk'_eq_div` and `div_mem`.
- **Hypotheses**: IsElliptic, `h_alg_top`.
- **Uses from project**: `x_gen`, `y_gen`
- **Used by**: `functionField_eq_intermediateField_adjoin_xy`
- **Visibility**: public
- **Lines**: 738–758; proof length: 21

---

### `theorem coordinateRing_algebraMap_mem_adjoin_xy`
- **Type**: `(W : WeierstrassCurve K) → [IsElliptic] → (r : W.toAffine.CoordinateRing) → algebraMap CR KE r ∈ Algebra.adjoin K {x_gen W, y_gen W}`
- **What**: Every element of the coordinate ring, mapped to K(E), lies in the subalgebra generated by x_gen and y_gen.
- **How**: Double induction via `AdjoinRoot.induction_on` and `Polynomial.induction_on'`; monomial case uses `AdjoinRoot.mk_X`, `AdjoinRoot.mk_C`, `IsScalarTower.algebraMap_apply`, and `Algebra.subset_adjoin`.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `x_gen`, `y_gen`
- **Used by**: `functionField_eq_intermediateField_adjoin_xy`
- **Visibility**: public
- **Lines**: 779–835; proof length: 57
- **Notes**: proof >30 lines

---

### `theorem functionField_eq_intermediateField_adjoin_xy`
- **Type**: `(W : WeierstrassCurve K) → [IsElliptic] → (⊤ : IntermediateField K W.toAffine.FunctionField) = IntermediateField.adjoin K {x_gen W, y_gen W}`
- **What**: Unconditional version of K(E) = adjoin K {x_gen, y_gen}.
- **How**: Composes `functionField_eq_intermediateField_adjoin_xy_of_witness` with `coordinateRing_algebraMap_mem_adjoin_xy`.
- **Hypotheses**: IsElliptic.
- **Uses from project**: `functionField_eq_intermediateField_adjoin_xy_of_witness`, `coordinateRing_algebraMap_mem_adjoin_xy`, `x_gen`, `y_gen`
- **Used by**: `mulByInt_two_pullback_fieldRange_subset_frobenius_unconditional`
- **Visibility**: public
- **Lines**: 839–844; proof length: 2

---

### `theorem char_two_sq_basis_form`
- **Type**: `(W : WeierstrassCurve K) → [IsElliptic] → [CharP K 2] → (a b : K(E)) → (a + b * y_gen W)^2 = a^2 + b^2 * (y_gen W)^2`
- **What**: Freshman's dream for `a + b·y` in char 2.
- **How**: Uses `charP_of_injective_algebraMap` to lift char 2 to K(E), then `linear_combination ... * h_2`.
- **Hypotheses**: IsElliptic, char 2.
- **Uses from project**: `y_gen`, `charP_of_injective_algebraMap` (implied)
- **Used by**: `alpha_squared_basis_form`, `y_qth_root_squared_eq_mulByInt_y_two_of_witnesses`
- **Visibility**: public
- **Lines**: 863–871; proof length: 9

---

### `theorem y_gen_sq_weierstrass_char_two`
- **Type**: Proves `(y_gen W)^2 = a₁·x·y + a₃·y + cubic_x(x)` in char 2 K(E).
- **What**: Weierstrass equation at the generic point specialized to char 2.
- **How**: Uses `generic_equation W`, `Affine.equation_iff'`, char-2 sign collapse, and `linear_combination`.
- **Hypotheses**: IsElliptic, char 2.
- **Uses from project**: `y_gen`, `x_gen`, `generic_equation`, `W_KE`
- **Used by**: `alpha_squared_basis_form`
- **Visibility**: public
- **Lines**: 877–906; proof length: 30

---

### `theorem alpha_squared_basis_form`
- **Type**: Proves `(a + b * y_gen W)^2 = a^2 + b^2 * (a₁·x·y + a₃·y + cubic_x)` in char 2 K(E).
- **What**: Combined char-2 squaring + Weierstrass substitution.
- **How**: Chains `char_two_sq_basis_form` and `y_gen_sq_weierstrass_char_two`.
- **Hypotheses**: IsElliptic, char 2.
- **Uses from project**: `char_two_sq_basis_form`, `y_gen_sq_weierstrass_char_two`, `y_gen`, `x_gen`
- **Used by**: `y_qth_root_squared_eq_mulByInt_y_two_of_witnesses`
- **Visibility**: public
- **Lines**: 910–918; proof length: 2

---

### `theorem alpha_1_y_qth_root_pow_card_eq`
- **Type**: States `(aeval x_gen (polyExpandRoot B h_B'))^q = aeval x_gen B` in simplified form using `Fintype.card K`.
- **What**: Specialization of `polyExpandRoot_aeval_pow_eq` for α₁.
- **How**: Direct application of `polyExpandRoot_aeval_pow_eq` with `polyPowCardEq_of_finite`.
- **Hypotheses**: IsElliptic, char 2, card K = 2, B in expand range.
- **Uses from project**: `polyExpandRoot`, `omega2_Y_coeff_char_two`, `x_gen`, `polyExpandRoot_aeval_pow_eq`, `polyPowCardEq_of_finite`
- **Used by**: unused in file (exported)
- **Visibility**: public
- **Lines**: 928–935; proof length: 1

---

### `theorem alpha_0_y_qth_root_pow_card_eq`
- **Type**: Same as `alpha_1_y_qth_root_pow_card_eq` but for α₀ and the coupled residual.
- **What**: Specialization of `polyExpandRoot_aeval_pow_eq` for α₀.
- **How**: Same.
- **Hypotheses**: IsElliptic, char 2, card K = 2, AB in expand range.
- **Uses from project**: `polyExpandRoot`, `omega2_coupled_residual_char_two`, `x_gen`, `polyExpandRoot_aeval_pow_eq`, `polyPowCardEq_of_finite`
- **Used by**: unused in file (exported)
- **Visibility**: public
- **Lines**: 939–946; proof length: 1

---

### `def OmegaTwoBasisHolds`
- **Type**: `(W : WeierstrassCurve K) → Prop`
- **What**: The statement that `W.ω 2 = C(A) + C(B) · X` in `K[X][Y]` (bivariate polynomial).
- **How**: Prop definition.
- **Hypotheses**: none
- **Uses from project**: `omega2_X_coeff_char_two`, `omega2_Y_coeff_char_two`
- **Used by**: `omegaTwoBasisHolds_char_two`, `omega_ff_two_basis_decomp_char_two`
- **Visibility**: public
- **Lines**: 967–969

---

### `theorem omegaTwoBasisHolds_char_two` (set_option maxHeartbeats 1000000)
- **Type**: `(W : WeierstrassCurve K) → [CharP K 2] → OmegaTwoBasisHolds W`
- **What**: Proves the bivariate polynomial identity `W.ω 2 = C(A) + C(B)·Y` in char 2 via mathlib's `redInvarDenom_two` and `complEDSAux₂_two`.
- **How**: Unfolds definition, rewrites via `WeierstrassCurve.ω`, `redInvarDenom_two`, `complEDSAux₂_two`, char-2 b-relations, `reduce_mod_char!`, `simp`, and `ring_nf`.
- **Hypotheses**: char 2.
- **Uses from project**: `omega2_X_coeff_char_two`, `omega2_Y_coeff_char_two`, `OmegaTwoBasisHolds`; mathlib `redInvarDenom_two`, `complEDSAux₂_two`
- **Used by**: `omega_ff_two_basis_decomp_char_two`
- **Visibility**: public
- **Lines**: 976–992; proof length: 17
- **Notes**: `set_option maxHeartbeats 1000000` (NO justifying comment)

---

### `theorem omega_ff_two_basis_decomp_char_two`
- **Type**: `(W : WeierstrassCurve K) → [IsElliptic] → [CharP K 2] → ω_ff W 2 = aeval x_gen A + aeval x_gen B * y_gen W`
- **What**: Bridges the bivariate polynomial identity to the K(E)-level basis decomposition.
- **How**: Unfolds `ω_ff`, rewrites via `omegaTwoBasisHolds_char_two`, applies `map_add/map_mul`, establishes the aeval-algebraMap equality chain, identifies `mk W (C p) = aeval x_gen p` and `mk W X = y_gen W`.
- **Hypotheses**: IsElliptic, char 2.
- **Uses from project**: `omega2_X_coeff_char_two`, `omega2_Y_coeff_char_two`, `OmegaTwoBasisHolds`, `omegaTwoBasisHolds_char_two`, `ω_ff`, `x_gen`, `y_gen`
- **Used by**: `y_qth_root_squared_eq_mulByInt_y_two_of_witnesses`
- **Visibility**: public
- **Lines**: 1003–1056; proof length: 54
- **Notes**: proof >30 lines

---

### `theorem psi_ff_two_eq_aeval_char_two`
- **Type**: `(W : WeierstrassCurve K) → [IsElliptic] → [CharP K 2] → ψ_ff W 2 = Polynomial.aeval (x_gen W) (C a₁ * X + C a₃)`
- **What**: The ψ_ff evaluation at q=2 in char 2 equals the aeval of the char-2-simplified ψ₂.
- **How**: Unfolds `ψ_ff`, uses `WeierstrassCurve.ψ_two`, `WeierstrassCurve.Affine.polynomialY`, `reduce_mod_char!`, algebraMap chain rewrites.
- **Hypotheses**: IsElliptic, char 2.
- **Uses from project**: `ψ_ff`, `x_gen`
- **Used by**: `y_qth_root_squared_eq_mulByInt_y_two_of_witnesses`
- **Visibility**: public
- **Lines**: 1060–1087; proof length: 28

---

### `theorem alpha_1_sq_psi_eq_B_div_psi_cubed_of_witness`
- **Type**: Witness-parametric statement that `α₁² * ψ₂(x) = aeval x_gen B / ψ₂(x)^3`.
- **What**: Y-coefficient matching identity for the squaring identity.
- **How**: Unfolds `alpha_1_y_qth_root_char_two`, rewrites `div_pow`, `h_polyRoot_sq`, `field_simp`.
- **Hypotheses**: IsElliptic, char 2, card K = 2, ψ₂(x_gen) ≠ 0, `polyExpandRoot` squaring identity.
- **Uses from project**: `alpha_1_y_qth_root_char_two`, `omega2_Y_coeff_char_two`, `x_gen`, `omega2_Y_coeff_mem_expand_two_char_two`
- **Used by**: `y_qth_root_squared_eq_mulByInt_y_two_of_witnesses`
- **Visibility**: public
- **Lines**: 1099–1118; proof length: 20

---

### `theorem alpha_0_sq_polynomial_match_char_two`
- **Type**: Witness-parametric constant-coefficient matching identity `(α₀² + α₁²·cubic_x) * ψ₂^4 = A * ψ₂`.
- **What**: 1-coefficient matching for the squaring identity, multiplied through to clear denominators.
- **How**: Unfolds both α defs, rewrites via div_pow and the two polyExpandRoot squaring hypotheses, unfolds `omega2_coupled_residual_char_two`, `field_simp`, and `linear_combination` with char-2 cancellation.
- **Hypotheses**: IsElliptic, char 2, card K = 2, ψ₂(x_gen) ≠ 0, two polyExpandRoot squaring identity hypotheses.
- **Uses from project**: `alpha_0_y_qth_root_char_two`, `alpha_1_y_qth_root_char_two`, `omega2_coupled_residual_char_two`, `omega2_X_coeff_char_two`, `omega2_Y_coeff_char_two`, `cubic_x`, `x_gen`, `omega2_coupled_residual_mem_expand_two_char_two`, `omega2_Y_coeff_mem_expand_two_char_two`
- **Used by**: `y_qth_root_squared_eq_mulByInt_y_two_of_witnesses`
- **Visibility**: public
- **Lines**: 1125–1171; proof length: 47
- **Notes**: proof >30 lines

---

### `theorem y_qth_root_squared_eq_mulByInt_y_two_of_witnesses`
- **Type**: Witness-parametric: `(y_qth_root_q_eq_2_char_2 W h_card)^2 = mulByInt_y W 2`
- **What**: The squaring identity: the explicit α squares to `mulByInt_y W 2`.
- **How**: Unfolds α defs, applies `char_two_sq_basis_form`, `y_gen_sq_weierstrass_char_two`, then uses `alpha_1_sq_psi_eq_B_div_psi_cubed_of_witness`, `alpha_0_sq_polynomial_match_char_two`, `omega_ff_two_basis_decomp_char_two`, `psi_ff_two_eq_aeval_char_two`, a `set`-algebra block for abbreviations, and `linear_combination`.
- **Hypotheses**: IsElliptic, char 2, card K = 2, ψ₂(x_gen) ≠ 0, two polyExpandRoot squaring witnesses.
- **Uses from project**: `y_qth_root_q_eq_2_char_2`, `y_qth_root_q_eq_2_char_2_of_witnesses`, `char_two_sq_basis_form`, `y_gen_sq_weierstrass_char_two`, `alpha_1_sq_psi_eq_B_div_psi_cubed_of_witness`, `alpha_0_sq_polynomial_match_char_two`, `omega_ff_two_basis_decomp_char_two`, `psi_ff_two_eq_aeval_char_two`, `alpha_0_y_qth_root_char_two`, `alpha_1_y_qth_root_char_two`, `mulByInt_y`, `cubic_x`, `omega2_X_coeff_char_two`, `omega2_Y_coeff_char_two`
- **Used by**: `mulByInt_two_pullback_y_gen_sq_root_unconditional`
- **Visibility**: public
- **Lines**: 1175–1248; proof length: 74
- **Notes**: proof >30 lines

---

### `theorem char_three_cube_basis_form`
- **Type**: `(a b : K(E)) → (a + b * y_gen W)^3 = a^3 + b^3 * (y_gen W)^3` in char 3.
- **What**: Freshman's dream for `a + b·y` in char 3 (cross terms vanish).
- **How**: `charP_of_injective_algebraMap` for char 3 in K(E), `ring_nf`, `linear_combination`.
- **Hypotheses**: IsElliptic, char 3.
- **Uses from project**: `y_gen`
- **Used by**: `alpha_cubed_basis_form_char_three`
- **Visibility**: public
- **Lines**: 1277–1285; proof length: 9

---

### `theorem char_five_quintic_basis_form`
- **Type**: `(a b : K(E)) → (a + b * y_gen W)^5 = a^5 + b^5 * (y_gen W)^5` in char 5.
- **What**: Freshman's dream in char 5.
- **How**: Same pattern as char 3.
- **Hypotheses**: IsElliptic, char 5.
- **Uses from project**: `y_gen`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1290–1300; proof length: 11
- **Notes**: No char-5 application in this file yet; parked/scaffolding.

---

### `theorem y_gen_sq_weierstrass_char_three`
- **Type**: `(y_gen W)^2 = -a₁·x·y - a₃·y + cubic_x(x)` in char-3 K(E).
- **What**: Weierstrass equation at generic point for char 3.
- **How**: `generic_equation W`, `Affine.equation_iff'`, `linear_combination`.
- **Hypotheses**: IsElliptic, char 3.
- **Uses from project**: `y_gen`, `x_gen`, `generic_equation`, `W_KE`
- **Used by**: `y_gen_cubed_weierstrass_char_three`, `y_gen_sq_mul_basis_form_char_three`, `y_gen_quartic_weierstrass_char_three`, `y_gen_quintic_weierstrass_char_five` (via char-3 analogy)
- **Visibility**: public
- **Lines**: 1307–1323; proof length: 17

---

### `theorem y_gen_sq_weierstrass_char_five`
- **Type**: Same as `y_gen_sq_weierstrass_char_three` but for char 5.
- **What**: Weierstrass equation at generic point for char 5.
- **How**: Identical proof pattern.
- **Hypotheses**: IsElliptic, char 5.
- **Uses from project**: `y_gen`, `x_gen`, `generic_equation`, `W_KE`
- **Used by**: `y_gen_cubed_weierstrass_char_five`, `y_gen_quartic_weierstrass_char_five`, `y_gen_quintic_weierstrass_char_five`
- **Visibility**: public
- **Lines**: 1328–1344; proof length: 17

---

### `theorem y_gen_cubed_weierstrass_char_five`
- **Type**: `(y_gen W)^3 = (ψ₂² + cubic_x)·y - ψ₂·cubic_x` in char-5 K(E).
- **What**: y_gen³ in the {1, y_gen} basis for char 5.
- **How**: `linear_combination (y_gen W - ψ₂) * y_gen_sq_weierstrass_char_five`.
- **Hypotheses**: IsElliptic, char 5.
- **Uses from project**: `y_gen_sq_weierstrass_char_five`, `y_gen`, `x_gen`
- **Used by**: `y_gen_quartic_weierstrass_char_five`, `y_gen_quintic_weierstrass_char_five`
- **Visibility**: public
- **Lines**: 1349–1366; proof length: 18

---

### `theorem y_gen_cubed_weierstrass_char_three`
- **Type**: `(y_gen W)^3 = (ψ₂² + cubic_x)·y - ψ₂·cubic_x` in char-3 K(E).
- **What**: y_gen³ in the {1, y_gen} basis for char 3.
- **How**: `linear_combination (y_gen W - ψ₂) * y_gen_sq_weierstrass_char_three`.
- **Hypotheses**: IsElliptic, char 3.
- **Uses from project**: `y_gen_sq_weierstrass_char_three`, `y_gen`, `x_gen`
- **Used by**: `y_gen_quartic_weierstrass_char_three`, `y_gen_cubed_mul_basis_form_char_three`, `alpha_cubed_basis_form_char_three`
- **Visibility**: public
- **Lines**: 1375–1396; proof length: 22

---

### `noncomputable def omega_3_X_coeff_char_three`
- **Type**: `(W : WeierstrassCurve K) → Polynomial K`
- **What**: Raw Y⁰ coefficient of `W.ω 3` in `K[X][Y]`: `Polynomial.coeff (W.ω 3) 0`.
- **How**: Trivial extraction.
- **Hypotheses**: none
- **Uses from project**: none
- **Used by**: `omega3_coupled_residual_char_three`, `OmegaThreeBasisHolds`, `omega_3_X_coeff_reduced_char_three` (indirectly)
- **Visibility**: public
- **Lines**: 1421–1423
- **Notes**: This is the RAW coefficient before Weierstrass reduction; `OmegaThreeBasisHolds` using this is noted as structurally wrong in docstring.

---

### `noncomputable def omega_3_Y_coeff_char_three`
- **Type**: `(W : WeierstrassCurve K) → Polynomial K`
- **What**: Raw Y¹ coefficient of `W.ω 3`: `Polynomial.coeff (W.ω 3) 1`.
- **How**: Trivial extraction.
- **Hypotheses**: none
- **Uses from project**: none
- **Used by**: `omega3_coupled_residual_char_three`, `OmegaThreeBasisHolds`
- **Visibility**: public
- **Lines**: 1430–1432
- **Notes**: RAW form (before Weierstrass reduction).

---

### `noncomputable def omega_3_X_coeff_reduced_char_three`
- **Type**: `(W : WeierstrassCurve K) → Polynomial K`
- **What**: Weierstrass-reduced Y⁰ coefficient of ω_3 (sums contributions from Y-degrees 0..5 via iterated substitution).
- **How**: Explicit structured sum using `Polynomial.coeff (W.ω 3) k` for k=0..5 with ψ₂ and cubic_x factors.
- **Hypotheses**: none
- **Uses from project**: `cubic_x`
- **Used by**: `OmegaThreeBasisHoldsReduced`, `omega_ff_three_basis_decomp_via_witness_char_three`
- **Visibility**: public
- **Lines**: 1452–1460

---

### `noncomputable def omega_3_Y_coeff_reduced_char_three`
- **Type**: `(W : WeierstrassCurve K) → Polynomial K`
- **What**: Weierstrass-reduced Y¹ coefficient of ω_3.
- **How**: Same pattern as the X case but Y¹ contributions.
- **Hypotheses**: none
- **Uses from project**: `cubic_x`
- **Used by**: `OmegaThreeBasisHoldsReduced`, `omega_ff_three_basis_decomp_via_witness_char_three`
- **Visibility**: public
- **Lines**: 1464–1472

---

### `def OmegaThreeBasisHoldsReduced`
- **Type**: `(W : WeierstrassCurve K) → [IsElliptic] → Prop`
- **What**: States that `ω_ff W 3 = aeval x_gen A_reduced + aeval x_gen B_reduced · y_gen` using the Weierstrass-reduced coefficients.
- **How**: Prop definition.
- **Hypotheses**: none
- **Uses from project**: `ω_ff`, `x_gen`, `y_gen`, `omega_3_X_coeff_reduced_char_three`, `omega_3_Y_coeff_reduced_char_three`
- **Used by**: `omega_ff_three_basis_decomp_via_witness_char_three`, `omegaThreeBasisHoldsReduced_via_nat_degree_bound`, `omegaThreeBasisHoldsReduced_unconditional`
- **Visibility**: public
- **Lines**: 1480–1484

---

### `def OmegaThreeBasisHolds`
- **Type**: `(W : WeierstrassCurve K) → [IsElliptic] → Prop`
- **What**: States the bivariate identity using RAW (not reduced) coefficients; noted as structurally wrong.
- **How**: Prop definition.
- **Hypotheses**: none
- **Uses from project**: `ω_ff`, `x_gen`, `y_gen`, `omega_3_X_coeff_char_three`, `omega_3_Y_coeff_char_three`
- **Used by**: unused in file (parked — docstring says "structurally wrong")
- **Visibility**: public
- **Lines**: 1499–1503
- **Notes**: Parked/experimental; superseded by `OmegaThreeBasisHoldsReduced`.

---

### `noncomputable def omega3_coupled_residual_char_three`
- **Type**: `(W : WeierstrassCurve K) → Polynomial K`
- **What**: Raw coupled residual for q=3: `A_3·(ψ₂²+cubic_x) + B_3·ψ₂·cubic_x`.
- **How**: Explicit formula.
- **Hypotheses**: none
- **Uses from project**: `omega_3_X_coeff_char_three`, `omega_3_Y_coeff_char_three`, `cubic_x`
- **Used by**: `omega3_coupled_residual_full_char_three`
- **Visibility**: public
- **Lines**: 1517–1522
- **Notes**: Docstring warns this is NOT in expand-range generically; only used as building block.

---

### `noncomputable def omega3_coupled_residual_full_char_three`
- **Type**: `(W : WeierstrassCurve K) → Polynomial K`
- **What**: Corrected full coupled residual `omega3_coupled_residual_char_three W * (ψ₂²+cubic_x)²` for the q=3 cube-root construction.
- **How**: Explicit formula.
- **Hypotheses**: none
- **Uses from project**: `omega3_coupled_residual_char_three`, `cubic_x`
- **Used by**: `omega3_coupled_residual_full_mem_expand_three_char_three_via_witness`
- **Visibility**: public
- **Lines**: 1534–1537

---

### `noncomputable def omega3_witness_coeff_X7`
- **Type**: `(W : WeierstrassCurve K) → K`
- **What**: Witness polynomial coefficient at degree X⁷ for the q=3 expand-range membership.
- **How**: `W.a₁ * W.a₂`.
- **Hypotheses**: none
- **Uses from project**: none
- **Used by**: `omega3_witness_polynomial_char_three`
- **Visibility**: public
- **Lines**: 1553–1554

---

### `noncomputable def omega3_witness_coeff_X6`
- **Type**: `(W : WeierstrassCurve K) → K`
- **What**: Witness polynomial coefficient at degree X⁶ (14-term sympy-extracted formula).
- **How**: Explicit.
- **Uses from project**: none
- **Used by**: `omega3_witness_polynomial_char_three`
- **Visibility**: public
- **Lines**: 1557–1563

---

### `noncomputable def omega3_witness_coeff_X0` (set_option maxHeartbeats 2000000, maxRecDepth 4096)
- **Type**: `(W : WeierstrassCurve K) → K`
- **What**: Witness polynomial coefficient at degree X⁰ (~70-term sympy-extracted formula).
- **How**: Explicit large formula.
- **Uses from project**: none
- **Used by**: `omega3_witness_polynomial_char_three`
- **Visibility**: public
- **Lines**: 1569–1602
- **Notes**: `set_option maxHeartbeats 2000000` and `set_option maxRecDepth 4096` (NO justifying comments)

---

### `noncomputable def omega3_witness_coeff_X1` (set_option maxHeartbeats 2500000, maxRecDepth 4096)
- **Type**: `(W : WeierstrassCurve K) → K`
- **What**: Witness polynomial coefficient at degree X¹ (~85-term sympy-extracted formula).
- **How**: Explicit large formula.
- **Uses from project**: none
- **Used by**: `omega3_witness_polynomial_char_three`
- **Visibility**: public
- **Lines**: 1607–1663
- **Notes**: `set_option maxHeartbeats 2500000` and `set_option maxRecDepth 4096` (NO justifying comments); largest single coefficient def.

---

### `noncomputable def omega3_witness_coeff_X2` (set_option maxHeartbeats 1500000, maxRecDepth 4096)
- **Type**: `(W : WeierstrassCurve K) → K`
- **What**: Witness polynomial coefficient at degree X² (~70-term sympy-extracted formula).
- **How**: Explicit large formula.
- **Uses from project**: none
- **Used by**: `omega3_witness_polynomial_char_three`
- **Visibility**: public
- **Lines**: 1668–1712
- **Notes**: `set_option maxHeartbeats 1500000` and `set_option maxRecDepth 4096` (NO justifying comments)

---

### `noncomputable def omega3_witness_coeff_X3` (set_option maxHeartbeats 2000000, maxRecDepth 4096)
- **Type**: `(W : WeierstrassCurve K) → K`
- **What**: Witness polynomial coefficient at degree X³ (~100-term sympy-extracted formula).
- **How**: Explicit large formula.
- **Uses from project**: none
- **Used by**: `omega3_witness_polynomial_char_three`
- **Visibility**: public
- **Lines**: 1717–1777
- **Notes**: `set_option maxHeartbeats 2000000` and `set_option maxRecDepth 4096` (NO justifying comments)

---

### `noncomputable def omega3_witness_coeff_X4` (set_option maxHeartbeats 800000)
- **Type**: `(W : WeierstrassCurve K) → K`
- **What**: Witness polynomial coefficient at degree X⁴ (~70-term formula).
- **How**: Explicit large formula.
- **Uses from project**: none
- **Used by**: `omega3_witness_polynomial_char_three`
- **Visibility**: public
- **Lines**: 1781–1817
- **Notes**: `set_option maxHeartbeats 800000` (NO justifying comment)

---

### `noncomputable def omega3_witness_coeff_X5`
- **Type**: `(W : WeierstrassCurve K) → K`
- **What**: Witness polynomial coefficient at degree X⁵ (30-term formula).
- **How**: Explicit.
- **Uses from project**: none
- **Used by**: `omega3_witness_polynomial_char_three`
- **Visibility**: public
- **Lines**: 1820–1831

---

### `noncomputable def omega3_witness_polynomial_char_three`
- **Type**: `(W : WeierstrassCurve K) → Polynomial K`
- **What**: Assembles the full witness polynomial from coefficient-by-coefficient defs.
- **How**: Sums `C(coeff_Xi) * X^i` for i=0..7.
- **Hypotheses**: none
- **Uses from project**: `omega3_witness_coeff_X0`, `omega3_witness_coeff_X1`, `omega3_witness_coeff_X2`, `omega3_witness_coeff_X3`, `omega3_witness_coeff_X4`, `omega3_witness_coeff_X5`, `omega3_witness_coeff_X6`, `omega3_witness_coeff_X7`
- **Used by**: unused in file (supporting `omega3_coupled_residual_full_mem_expand_three_char_three_via_witness` via `h_eq`)
- **Visibility**: public
- **Lines**: 1837–1846

---

### `noncomputable def omega3_witness_leading_partial_char_three`
- **Type**: `(W : WeierstrassCurve K) → Polynomial K`
- **What**: OBSOLETE scaffold: partial witness with only X⁵-X⁷ terms, superseded by `omega3_witness_polynomial_char_three`.
- **How**: Explicit.
- **Hypotheses**: none
- **Uses from project**: none
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1850–1874
- **Notes**: Marked OBSOLETE in docstring; dead code candidate.

---

### `theorem omega3_coupled_residual_full_mem_expand_three_char_three_via_witness`
- **Type**: `{g : Polynomial K} → (h_eq : expand K 3 g = omega3_coupled_residual_full_char_three W) → omega3_coupled_residual_full_char_three W ∈ Set.range (⇑(Polynomial.expand K 3))`
- **What**: Witness-parametric existential: from any `g` with `expand 3 g = ...`, deduce the membership. Trivially `⟨g, h_eq⟩`.
- **How**: Trivial existential intro.
- **Hypotheses**: char 3, witness equality.
- **Uses from project**: `omega3_coupled_residual_full_char_three`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1883–1889; proof length: 1

---

### `theorem psi_2_sq_plus_cubic_x_form_char_three`
- **Type**: `(C a₁ * X + C a₃)^2 + cubic_x W = X³ + C b₂ * X² + C (2*b₄) * X + C b₆` in char 3.
- **What**: Explicit polynomial form of ψ₂² + cubic_x in char 3 using b-invariants.
- **How**: Unfolds `cubic_x`, uses char-3 reductions, `push_cast`, `simp`, `linear_combination` with 3-multiple.
- **Hypotheses**: char 3.
- **Uses from project**: `cubic_x`
- **Used by**: `psi_2_sq_plus_cubic_x_neg_b4_form_char_three`
- **Visibility**: public
- **Lines**: 1898–1916; proof length: 19

---

### `theorem psi_2_sq_plus_cubic_x_neg_b4_form_char_three`
- **Type**: Same as above but `C (2*b₄) = -C b₄` in char 3.
- **What**: Alternate form: ψ₂² + cubic_x = X³ + b₂X² - b₄X + b₆ in char 3.
- **How**: Applies `psi_2_sq_plus_cubic_x_form_char_three` and rewrites `2*b₄ = -b₄` via `linear_combination b₄ * h_3`.
- **Hypotheses**: char 3.
- **Uses from project**: `cubic_x`, `psi_2_sq_plus_cubic_x_form_char_three`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1921–1930; proof length: 10

---

### `theorem y_gen_quartic_weierstrass_char_three`
- **Type**: `(y_gen W)^4 = -ψ₂·(ψ₂²+2·cubic_x)·y + cubic_x·(ψ₂²+cubic_x)` in char-3 K(E).
- **What**: y_gen⁴ in {1, y_gen} basis by iterated Weierstrass substitution in char 3.
- **How**: Uses `y_gen_sq_weierstrass_char_three`, `y_gen_cubed_weierstrass_char_three`, `linear_combination`.
- **Hypotheses**: IsElliptic, char 3.
- **Uses from project**: `y_gen_sq_weierstrass_char_three`, `y_gen_cubed_weierstrass_char_three`, `y_gen`, `x_gen`
- **Used by**: `y_gen_quartic_mul_basis_form_char_three`, `y_gen_quintic_weierstrass_char_three`
- **Visibility**: public
- **Lines**: 1939–1969; proof length: 31
- **Notes**: proof >30 lines

---

### `theorem y_gen_quintic_weierstrass_char_three`
- **Type**: `(y_gen W)^5 = (ψ₂⁴+3ψ₂²·cubic_x+cubic_x²)·y - ψ₂·cubic_x·(ψ₂²+2·cubic_x)` in char-3 K(E).
- **What**: y_gen⁵ in {1, y_gen} basis by iterated Weierstrass substitution in char 3.
- **How**: Uses `y_gen_sq_weierstrass_char_three`, `y_gen_quartic_weierstrass_char_three`, `linear_combination`.
- **Hypotheses**: IsElliptic, char 3.
- **Uses from project**: `y_gen_sq_weierstrass_char_three`, `y_gen_quartic_weierstrass_char_three`, `y_gen`, `x_gen`
- **Used by**: `y_gen_quintic_mul_basis_form_char_three`
- **Visibility**: public
- **Lines**: 1982–2020; proof length: 39
- **Notes**: proof >30 lines

---

### `theorem y_gen_quartic_weierstrass_char_five`
- **Type**: Same form as `y_gen_quartic_weierstrass_char_three` but for char 5.
- **What**: y_gen⁴ in {1, y_gen} basis for char 5.
- **How**: Same pattern; uses `y_gen_sq_weierstrass_char_five`, `y_gen_cubed_weierstrass_char_five`.
- **Hypotheses**: IsElliptic, char 5.
- **Uses from project**: `y_gen_sq_weierstrass_char_five`, `y_gen_cubed_weierstrass_char_five`, `y_gen`, `x_gen`
- **Used by**: `y_gen_quintic_weierstrass_char_five`
- **Visibility**: public
- **Lines**: 2024–2054; proof length: 31
- **Notes**: proof >30 lines

---

### `theorem y_gen_quintic_weierstrass_char_five`
- **Type**: Same form as `y_gen_quintic_weierstrass_char_three` but for char 5.
- **What**: y_gen⁵ in {1, y_gen} basis for char 5.
- **How**: Uses `y_gen_sq_weierstrass_char_five`, `y_gen_quartic_weierstrass_char_five`.
- **Hypotheses**: IsElliptic, char 5.
- **Uses from project**: `y_gen_sq_weierstrass_char_five`, `y_gen_quartic_weierstrass_char_five`, `y_gen`, `x_gen`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 2057–2095; proof length: 39
- **Notes**: proof >30 lines; no char-5 application shipped yet.

---

### `theorem y_gen_sq_mul_basis_form_char_three`
- **Type**: `(p : K(E)) → p * (y_gen W)^2 = -p·ψ₂·y + p·cubic_x` in char-3 K(E).
- **What**: Scalar-multiplied Y² contribution helper.
- **How**: `linear_combination p * y_gen_sq_weierstrass_char_three`.
- **Hypotheses**: IsElliptic, char 3.
- **Uses from project**: `y_gen_sq_weierstrass_char_three`, `y_gen`, `x_gen`
- **Used by**: `omega_ff_three_basis_decomp_via_witness_char_three`
- **Visibility**: public
- **Lines**: 2109–2119; proof length: 2

---

### `theorem y_gen_cubed_mul_basis_form_char_three`
- **Type**: `(p : K(E)) → p * (y_gen W)^3 = p·(ψ₂²+cubic_x)·y - p·ψ₂·cubic_x` in char-3.
- **What**: Y³ contribution helper.
- **How**: `linear_combination p * y_gen_cubed_weierstrass_char_three`.
- **Hypotheses**: IsElliptic, char 3.
- **Uses from project**: `y_gen_cubed_weierstrass_char_three`, `y_gen`, `x_gen`
- **Used by**: `omega_ff_three_basis_decomp_via_witness_char_three`
- **Visibility**: public
- **Lines**: 2123–2139; proof length: 2

---

### `theorem y_gen_quartic_mul_basis_form_char_three`
- **Type**: `(p : K(E)) → p * (y_gen W)^4 = -p·ψ₂·(ψ₂²+2·cubic_x)·y + p·cubic_x·(ψ₂²+cubic_x)`.
- **What**: Y⁴ contribution helper.
- **How**: `linear_combination p * y_gen_quartic_weierstrass_char_three`.
- **Hypotheses**: IsElliptic, char 3.
- **Uses from project**: `y_gen_quartic_weierstrass_char_three`, `y_gen`, `x_gen`
- **Used by**: `omega_ff_three_basis_decomp_via_witness_char_three`
- **Visibility**: public
- **Lines**: 2143–2165; proof length: 2

---

### `theorem y_gen_quintic_mul_basis_form_char_three`
- **Type**: `(p : K(E)) → p * (y_gen W)^5 = p·(ψ₂⁴+3ψ₂²·cubic_x+cubic_x²)·y - p·ψ₂·cubic_x·(ψ₂²+2·cubic_x)`.
- **What**: Y⁵ contribution helper.
- **How**: `linear_combination p * y_gen_quintic_weierstrass_char_three`.
- **Hypotheses**: IsElliptic, char 3.
- **Uses from project**: `y_gen_quintic_weierstrass_char_three`, `y_gen`, `x_gen`
- **Used by**: `omega_ff_three_basis_decomp_via_witness_char_three`
- **Visibility**: public
- **Lines**: 2169–2197; proof length: 2

---

### `theorem alpha_cubed_basis_form_char_three`
- **Type**: `(a b : K(E)) → (a + b*y_gen W)^3 = (a^3 - b^3·ψ₂·cubic_x) + b^3·(ψ₂²+cubic_x)·y_gen W` in char 3.
- **What**: Combined char-3 cubing + Weierstrass substitution.
- **How**: `rw [char_three_cube_basis_form, y_gen_cubed_weierstrass_char_three]; ring`.
- **Hypotheses**: IsElliptic, char 3.
- **Uses from project**: `char_three_cube_basis_form`, `y_gen_cubed_weierstrass_char_three`, `y_gen`, `x_gen`
- **Used by**: unused in file (exported)
- **Visibility**: public
- **Lines**: 2208–2224; proof length: 17

---

### `theorem omega_ff_three_decomp_via_nat_degree_bound` (set_option maxHeartbeats 800000)
- **Type**: `(W : WeierstrassCurve K) → [IsElliptic] → (h_deg : (W.ω 3).natDegree ≤ 5) → ω_ff W 3 = sum over Y-degrees 0..5 of aeval x_gen (coeff k) * (y_gen W)^k`
- **What**: Expresses `ω_ff W 3` as an explicit sum over Y-degrees 0..5, given a natDegree bound.
- **How**: Uses `Polynomial.as_sum_range_C_mul_X_pow'`, the algebraMap-aeval bridge, `h_C_aeval`, `h_X_y`, `simp`, and `ring`.
- **Hypotheses**: IsElliptic, `(W.ω 3).natDegree ≤ 5`.
- **Uses from project**: `ω_ff`, `x_gen`, `y_gen`
- **Used by**: `omegaThreeBasisHoldsReduced_via_nat_degree_bound`
- **Visibility**: public
- **Lines**: 2233–2278; proof length: 46
- **Notes**: `set_option maxHeartbeats 800000` (NO justifying comment); proof >30 lines

---

### `theorem omega_ff_three_basis_decomp_via_witness_char_three` (set_option maxHeartbeats 1000000)
- **Type**: Given `h_decomp` (the Y-degree sum decomposition at K(E) level), proves `OmegaThreeBasisHoldsReduced W`.
- **What**: The substantive Weierstrass-reduction step: converts the Y-degree-sum form into the {1, y_gen} basis form using the four Y-degree contribution helpers.
- **How**: Uses `y_gen_sq/cubed/quartic/quintic_mul_basis_form_char_three`, `simp`, unfolds `cubic_x`, and `ring`.
- **Hypotheses**: IsElliptic, char 3, `h_decomp`.
- **Uses from project**: `OmegaThreeBasisHoldsReduced`, `omega_3_X_coeff_reduced_char_three`, `omega_3_Y_coeff_reduced_char_three`, `y_gen_sq_mul_basis_form_char_three`, `y_gen_cubed_mul_basis_form_char_three`, `y_gen_quartic_mul_basis_form_char_three`, `y_gen_quintic_mul_basis_form_char_three`, `cubic_x`, `x_gen`, `y_gen`
- **Used by**: `omegaThreeBasisHoldsReduced_via_nat_degree_bound`
- **Visibility**: public
- **Lines**: 2291–2320; proof length: 30
- **Notes**: `set_option maxHeartbeats 1000000` (NO justifying comment)

---

### `theorem natDegree_polynomialY_le`
- **Type**: `{R : Type*} → [CommRing R] → [Nontrivial R] → (W : WeierstrassCurve R) → W.toAffine.polynomialY.natDegree ≤ 1`
- **What**: Y-natDegree of `polynomialY` is ≤ 1.
- **How**: `natDegree_add_le`, `natDegree_mul_le`, `natDegree_C`, `natDegree_X`.
- **Hypotheses**: CommRing, Nontrivial.
- **Uses from project**: none
- **Used by**: `natDegree_ψ_2_le`, `natDegree_negPolynomial_le`, `natDegree_CC_a1_mul_polynomialY_le`
- **Visibility**: public
- **Lines**: 2328–2336; proof length: 9

---

### `theorem natDegree_polynomialX_le`
- **Type**: `W.toAffine.polynomialX.natDegree ≤ 1`
- **What**: Y-natDegree of `polynomialX` is ≤ 1.
- **How**: Identical pattern.
- **Uses from project**: none
- **Used by**: `natDegree_INNER_first_term_le`
- **Visibility**: public
- **Lines**: 2339–2347; proof length: 9

---

### `theorem natDegree_negPolynomial_le`
- **Type**: `W.toAffine.negPolynomial.natDegree ≤ 1`
- **What**: Y-natDegree of `negPolynomial` is ≤ 1.
- **How**: Similar pattern.
- **Uses from project**: none (uses `natDegree_polynomialY_le` indirectly via reference to `polynomialY`)
- **Used by**: `natDegree_negPolynomial_mul_psi_three_cubed_le`
- **Visibility**: public
- **Lines**: 2350–2357; proof length: 8

---

### `theorem natDegree_ψ_2_le`
- **Type**: `W.ψ₂.natDegree ≤ 1`
- **What**: Y-natDegree of ψ₂ = polynomialY is ≤ 1.
- **How**: Reduces to `natDegree_polynomialY_le`.
- **Uses from project**: `natDegree_polynomialY_le`
- **Used by**: `natDegree_negPolynomial_mul_psi_three_cubed_le` (via `natDegree_negPolynomial_le`), `natDegree_ω_three_le_via_component_witnesses` (via chain), `natDegree_complEDSAux₂_three_le_of_char_three`
- **Visibility**: public
- **Lines**: 2360–2364; proof length: 4

---

### `theorem natDegree_ψ_three_eq_zero`
- **Type**: `(W.ψ 3).natDegree = 0`
- **What**: ψ₃ = C Ψ₃ is constant in Y.
- **How**: `WeierstrassCurve.ψ_three` + `Polynomial.natDegree_C`.
- **Uses from project**: none
- **Used by**: `natDegree_negPolynomial_mul_psi_three_cubed_le`
- **Visibility**: public
- **Lines**: 2367–2371; proof length: 3

---

### `theorem natDegree_ψ_four_le`
- **Type**: `(W.ψ 4).natDegree ≤ 1`
- **What**: ψ₄ = C preΨ₄ · ψ₂ has Y-natDegree ≤ 1.
- **How**: `WeierstrassCurve.ψ_four`, `natDegree_mul_le`, `natDegree_C`, `natDegree_ψ_2_le`.
- **Uses from project**: `natDegree_ψ_2_le`
- **Used by**: `natDegree_redInvarDenom_three_le`
- **Visibility**: public
- **Lines**: 2374–2380; proof length: 7

---

### `theorem natDegree_polynomial_sq_le`
- **Type**: `(W.toAffine.polynomial ^ 2).natDegree ≤ 4`
- **What**: The squared Weierstrass polynomial has Y-natDegree ≤ 4.
- **How**: `natDegree_pow_le` + `natDegree_polynomial`.
- **Uses from project**: none
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 2383–2387; proof length: 5
- **Notes**: Not referenced in the proof chain; dead code candidate.

---

### `theorem natDegree_C_Ψ₂Sq_eq_zero`
- **Type**: `(Polynomial.C W.Ψ₂Sq).natDegree = 0`
- **What**: C·Ψ₂Sq is constant in Y.
- **How**: `natDegree_C`.
- **Uses from project**: none
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 2390–2392; proof length: 1
- **Notes**: Dead code candidate (no caller in file).

---

### `theorem natDegree_C_Ψ_3_eq_zero`
- **Type**: `(Polynomial.C W.Ψ₃).natDegree = 0`
- **What**: C·Ψ₃ is constant in Y.
- **How**: `natDegree_C`.
- **Uses from project**: none
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 2395–2397; proof length: 1
- **Notes**: Dead code candidate.

---

### `theorem natDegree_CC_a1_mul_polynomialY_le`
- **Type**: `(C (C W.a₁) * W.toAffine.polynomialY).natDegree ≤ 1`
- **What**: natDegree of `C(C a₁) · polynomialY` is ≤ 1.
- **How**: `natDegree_mul_le` + `natDegree_C` + `natDegree_polynomialY_le`.
- **Uses from project**: `natDegree_polynomialY_le`
- **Used by**: `natDegree_INNER_first_term_le`
- **Visibility**: public
- **Lines**: 2401–2406; proof length: 6

---

### `theorem natDegree_negPolynomial_mul_psi_three_cubed_le`
- **Type**: `(W.toAffine.negPolynomial * (W.ψ 3)^3).natDegree ≤ 1`
- **What**: The product of negPolynomial and ψ₃³ has Y-natDegree ≤ 1.
- **How**: Combines `natDegree_ψ_three_eq_zero`, `natDegree_negPolynomial_le`, `natDegree_pow_le`, `natDegree_mul_le`.
- **Uses from project**: `natDegree_ψ_three_eq_zero`, `natDegree_negPolynomial_le`
- **Used by**: `natDegree_ω_three_le_via_component_witnesses`
- **Visibility**: public
- **Lines**: 2410–2417; proof length: 8

---

### `theorem natDegree_INNER_first_term_le`
- **Type**: `((C (C a₁) * polynomialY - polynomialX) * C Ψ₃).natDegree ≤ 1`
- **What**: First summand of the INNER bracket has natDegree ≤ 1.
- **How**: `natDegree_sub_le`, `natDegree_CC_a1_mul_polynomialY_le`, `natDegree_polynomialX_le`, `natDegree_C`, `natDegree_mul_le`.
- **Uses from project**: `natDegree_CC_a1_mul_polynomialY_le`, `natDegree_polynomialX_le`
- **Used by**: `natDegree_INNER_le`
- **Visibility**: public
- **Lines**: 2421–2431; proof length: 11

---

### `theorem natDegree_polynomial_mul_two_polynomial_plus_C_Ψ₂Sq_le`
- **Type**: `(W.toAffine.polynomial * (2 * W.toAffine.polynomial + C W.Ψ₂Sq)).natDegree ≤ 4`
- **What**: Second summand helper for INNER: natDegree ≤ 4.
- **How**: Uses `natDegree_mul_le`, `natDegree_add_le`, `natDegree_polynomial`, `natDegree_C`.
- **Uses from project**: none
- **Used by**: `natDegree_INNER_second_term_le`
- **Visibility**: public
- **Lines**: 2435–2448; proof length: 14

---

### `theorem natDegree_INNER_second_term_le`
- **Type**: `(4 * W.toAffine.polynomial * (2 * W.toAffine.polynomial + C W.Ψ₂Sq)).natDegree ≤ 4`
- **What**: Second summand of INNER has Y-natDegree ≤ 4.
- **How**: Rearranges multiplication, uses `natDegree_mul_le`, `natDegree_polynomial`, various constant-natDegree calculations.
- **Uses from project**: `natDegree_polynomial_mul_two_polynomial_plus_C_Ψ₂Sq_le`
- **Used by**: `natDegree_INNER_le`
- **Visibility**: public
- **Lines**: 2453–2477; proof length: 25

---

### `theorem natDegree_INNER_le`
- **Type**: natDegree of the INNER bracket ≤ 4.
- **What**: Combines the two INNER summand bounds.
- **How**: `natDegree_add_le`, `natDegree_INNER_first_term_le`, `natDegree_INNER_second_term_le`.
- **Uses from project**: `natDegree_INNER_first_term_le`, `natDegree_INNER_second_term_le`
- **Used by**: `natDegree_ω_three_le_via_component_witnesses`
- **Visibility**: public
- **Lines**: 2480–2489; proof length: 10

---

### `theorem natDegree_redInvarDenom_three_le`
- **Type**: `(redInvarDenom W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) 3).natDegree ≤ 1`
- **What**: The m=3 branch of redInvarDenom has natDegree ≤ 1.
- **How**: Identifies `redInvarDenom ... 3 = W.ψ 4` via `simp [redInvarDenom, complEDS_one]`, then uses `natDegree_ψ_four_le`.
- **Uses from project**: `natDegree_ψ_four_le`
- **Used by**: `natDegree_ω_three_le_via_component_witnesses`, `natDegree_ω_three_le_of_char_three`
- **Visibility**: public
- **Lines**: 2495–2503; proof length: 9

---

### `theorem natDegree_ω_three_le_via_component_witnesses`
- **Type**: `{R : Type*} → [CommRing R] → [Nontrivial R] → (W : WeierstrassCurve R) → (h_redInvar : ... ≤ 1) → (h_complEDSAux₂ : ... ≤ 1) → (W.ω 3).natDegree ≤ 5`
- **What**: `(W.ω 3).natDegree ≤ 5` from two parametric natDegree witnesses for `redInvarDenom_3` and `complEDSAux₂_3`.
- **How**: Rewrites `W.ω 3` as explicit formula, applies `natDegree_add_le`, `natDegree_sub_le`, `natDegree_mul_le`, `natDegree_INNER_le`, `natDegree_negPolynomial_mul_psi_three_cubed_le`.
- **Hypotheses**: CommRing, Nontrivial, two natDegree witnesses.
- **Uses from project**: `natDegree_INNER_le`, `natDegree_negPolynomial_mul_psi_three_cubed_le`
- **Used by**: `natDegree_ω_three_le_of_char_three`
- **Visibility**: public
- **Lines**: 2512–2535; proof length: 24

---

### `theorem two_ne_zero_of_char_three`
- **Type**: `{K' : Type*} → [CommRing K'] → [Nontrivial K'] → [CharP K' 3] → (2 : K') ≠ 0`
- **What**: 2 ≠ 0 in characteristic 3.
- **How**: Derives `1 = 0` from `2 = 0` and `3 = 0` using `linear_combination`, contradicting `one_ne_zero`.
- **Hypotheses**: CommRing, Nontrivial, char 3.
- **Uses from project**: none
- **Used by**: `preΨ_4_ne_zero_of_char_three`, `ψ_2_ne_zero_of_char_three`
- **Visibility**: public
- **Lines**: 2556–2561; proof length: 6

---

### `theorem preΨ_4_ne_zero_of_char_three`
- **Type**: `(W : WeierstrassCurve K') → [Nontrivial K'] → [CharP K' 3] → W.preΨ₄ ≠ 0`
- **What**: preΨ₄ ≠ 0 in char 3 (uses mathlib's `preΨ₄_ne_zero` with 2 ≠ 0).
- **How**: `W.preΨ₄_ne_zero two_ne_zero_of_char_three`.
- **Uses from project**: `two_ne_zero_of_char_three`
- **Used by**: `ψ_four_ne_zero_of_char_three`
- **Visibility**: public
- **Lines**: 2564–2566; proof length: 1

---

### `theorem ψ_2_ne_zero_of_char_three`
- **Type**: `(W : WeierstrassCurve K') → [Nontrivial K'] → [CharP K' 3] → W.ψ₂ ≠ 0`
- **What**: ψ₂ = polynomialY ≠ 0 in char 3 (the leading coefficient C(C 2) ≠ 0).
- **How**: Takes coeff at degree 1, extracts `C(2 : K') = 0` → `2 = 0` contradiction with `two_ne_zero_of_char_three`.
- **Uses from project**: `two_ne_zero_of_char_three`
- **Used by**: `ψ_four_ne_zero_of_char_three`, `complEDSAux₂_three_eq_of_char_three`
- **Visibility**: public
- **Lines**: 2569–2581; proof length: 13

---

### `theorem ψ_four_ne_zero_of_char_three`
- **Type**: `(W : WeierstrassCurve K') → [Nontrivial K'] → [IsDomain K'] → [CharP K' 3] → (W.ψ 4 : ...) ≠ 0`
- **What**: ψ₄ = C preΨ₄ · ψ₂ ≠ 0 in char 3 (both factors nonzero in a domain).
- **How**: `WeierstrassCurve.ψ_four`, `mul_eq_zero.mp`, uses `preΨ_4_ne_zero_of_char_three` and `ψ_2_ne_zero_of_char_three`.
- **Hypotheses**: IsDomain, char 3.
- **Uses from project**: `preΨ_4_ne_zero_of_char_three`, `ψ_2_ne_zero_of_char_three`
- **Used by**: `ψ_four_sq_ne_zero_of_char_three`
- **Visibility**: public
- **Lines**: 2584–2592; proof length: 9

---

### `theorem ψ_four_sq_ne_zero_of_char_three`
- **Type**: `(W.ψ 4)^2 ≠ 0` in char 3.
- **What**: ψ₄² ≠ 0.
- **How**: `pow_ne_zero 2 (ψ_four_ne_zero_of_char_three W)`.
- **Uses from project**: `ψ_four_ne_zero_of_char_three`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 2595–2598; proof length: 1

---

### `theorem complEDSAux₂_three_eq_of_char_three`
- **Type**: `complEDSAux₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) 3 = (C W.preΨ₄)^2 * W.ψ₂` in char 3.
- **What**: Explicit form of `complEDSAux₂` at m=3 in char 3.
- **How**: Uses `complEDSAux₂_mul_b`, identifies `normEDS ... 4 = C preΨ₄ · ψ₂` via `WeierstrassCurve.ψ_four`, then cancels ψ₂ using `ψ_2_ne_zero_of_char_three` and `mul_right_cancel₀`.
- **Hypotheses**: IsDomain, char 3.
- **Uses from project**: `ψ_2_ne_zero_of_char_three`; mathlib `complEDSAux₂_mul_b`, `normEDS_one`
- **Used by**: `natDegree_complEDSAux₂_three_le_of_char_three`
- **Visibility**: public
- **Lines**: 2602–2620; proof length: 19

---

### `theorem natDegree_complEDSAux₂_three_le_of_char_three`
- **Type**: `(complEDSAux₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) 3).natDegree ≤ 1` unconditionally in char 3.
- **What**: The natDegree bound for `complEDSAux₂_3` in char 3.
- **How**: Uses `complEDSAux₂_three_eq_of_char_three`, `natDegree_mul_le`, `natDegree_pow_le`, `natDegree_C`, `natDegree_ψ_2_le`.
- **Hypotheses**: IsDomain, char 3.
- **Uses from project**: `complEDSAux₂_three_eq_of_char_three`, `natDegree_ψ_2_le`
- **Used by**: `natDegree_ω_three_le_of_char_three`
- **Visibility**: public
- **Lines**: 2626–2637; proof length: 12

---

### `theorem natDegree_ω_three_le_of_char_three`
- **Type**: `(W.ω 3).natDegree ≤ 5` unconditionally in IsDomain + char 3.
- **What**: Unconditional natDegree bound for `ω 3` in char 3.
- **How**: Composes `natDegree_ω_three_le_via_component_witnesses` with `natDegree_redInvarDenom_three_le` and `natDegree_complEDSAux₂_three_le_of_char_three`.
- **Hypotheses**: IsDomain, char 3.
- **Uses from project**: `natDegree_ω_three_le_via_component_witnesses`, `natDegree_redInvarDenom_three_le`, `natDegree_complEDSAux₂_three_le_of_char_three`
- **Used by**: `omegaThreeBasisHoldsReduced_unconditional`
- **Visibility**: public
- **Lines**: 2640–2645; proof length: 3

---

### `theorem omegaThreeBasisHoldsReduced_via_nat_degree_bound`
- **Type**: `[IsElliptic] → [CharP K 3] → (h_deg : (W.ω 3).natDegree ≤ 5) → OmegaThreeBasisHoldsReduced W`
- **What**: From the natDegree bound, derives the basis decomposition.
- **How**: Composes `omega_ff_three_basis_decomp_via_witness_char_three` with `omega_ff_three_decomp_via_nat_degree_bound`.
- **Uses from project**: `omega_ff_three_basis_decomp_via_witness_char_three`, `omega_ff_three_decomp_via_nat_degree_bound`, `OmegaThreeBasisHoldsReduced`
- **Used by**: `omegaThreeBasisHoldsReduced_unconditional`
- **Visibility**: public
- **Lines**: 2546–2551; proof length: 2

---

### `theorem omegaThreeBasisHoldsReduced_unconditional`
- **Type**: `(W : WeierstrassCurve K) → [IsElliptic] → [CharP K 3] → OmegaThreeBasisHoldsReduced W`
- **What**: Unconditional (axiom-clean) basis decomposition of ω₃ in char 3.
- **How**: Composes `omegaThreeBasisHoldsReduced_via_nat_degree_bound` with `natDegree_ω_three_le_of_char_three`.
- **Hypotheses**: IsDomain (implicit via char 3 finite field), char 3.
- **Uses from project**: `omegaThreeBasisHoldsReduced_via_nat_degree_bound`, `natDegree_ω_three_le_of_char_three`, `OmegaThreeBasisHoldsReduced`
- **Used by**: unused in file (exported)
- **Visibility**: public
- **Lines**: 2652–2656; proof length: 2

---

### `theorem mulByInt_three_pullback_x_gen_cube_root_unconditional`
- **Type**: `[IsElliptic] → [CharP K 3] → (h_card : Fintype.card K = 3) → ∃ g, g^(Fintype.card K) = (mulByInt W.toAffine q).pullback (x_gen W)`
- **What**: Unconditional q=3 char=3 x-side cube root: `[3]^* x_gen` has a cube root in K(E).
- **How**: Calls `mulByInt_q_pullback_x_gen_qth_root_of_expand_witness` with `Φ_three_mem_expand_three_char_three`, `ΨSq_three_mem_expand_three_char_three`, and `h_card` rewrites.
- **Hypotheses**: IsElliptic, char 3, card K = 3.
- **Uses from project**: `mulByInt_q_pullback_x_gen_qth_root_of_expand_witness`, `Φ_three_mem_expand_three_char_three`, `ΨSq_three_mem_expand_three_char_three`
- **Used by**: unused in file (exported)
- **Visibility**: public
- **Lines**: 2665–2680; proof length: 16

---

### `theorem mulByInt_two_pullback_x_gen_sq_root_unconditional`
- **Type**: `[IsElliptic] → [CharP K 2] → (h_card : Fintype.card K = 2) → ∃ g, g^q = (mulByInt W.toAffine q).pullback (x_gen W)`
- **What**: Unconditional q=2 char=2 x-side square root: `[2]^* x_gen` has a square root in K(E).
- **How**: Same pattern as q=3, using `Φ_two_mem_expand_two_char_two` and `ΨSq_two_mem_expand_two_char_two`.
- **Hypotheses**: IsElliptic, char 2, card K = 2.
- **Uses from project**: `mulByInt_q_pullback_x_gen_qth_root_of_expand_witness`, `Φ_two_mem_expand_two_char_two`, `ΨSq_two_mem_expand_two_char_two`
- **Used by**: `mulByInt_two_pullback_fieldRange_subset_frobenius_unconditional`
- **Visibility**: public
- **Lines**: 2693–2706; proof length: 14

---

### `private theorem a₁X_plus_a₃_polynomial_ne_zero_char_two`
- **Type**: `(Polynomial.C W.toAffine.a₁ * Polynomial.X + Polynomial.C W.toAffine.a₃ : Polynomial K) ≠ 0` in char 2 IsElliptic.
- **What**: The polynomial a₁X + a₃ is nonzero in char 2 when W is elliptic (otherwise Δ = 0).
- **How**: Derives a₁ = 0 and a₃ = 0 from the polynomial being 0 (via coefficient extraction), then shows Δ = 0 via `WeierstrassCurve.Δ_of_char_two` and contradicts `isUnit_Δ.ne_zero`.
- **Hypotheses**: IsElliptic, char 2.
- **Uses from project**: none (uses mathlib `WeierstrassCurve.Δ_of_char_two`, `W.toAffine.isUnit_Δ`)
- **Used by**: `aeval_x_gen_a₁X_plus_a₃_ne_zero_char_two`
- **Visibility**: private
- **Lines**: 2717–2730; proof length: 14

---

### `private theorem aeval_x_gen_a₁X_plus_a₃_ne_zero_char_two`
- **Type**: `Polynomial.aeval (x_gen W) (C a₁ * X + C a₃) ≠ (0 : W.toAffine.FunctionField)` in char 2 IsElliptic.
- **What**: The function-field evaluation ψ₂(x_gen) ≠ 0 (the `h_psi_ne` discharge).
- **How**: Converts `aeval x_gen p = algebraMap K[X] K(E) p`, uses injectivity of the `K[X] → CoordinateRing → K(E)` chain (via `IsFractionRing.injective`, `Affine.CoordinateRing.algebraMap_poly_injective`), then applies `a₁X_plus_a₃_polynomial_ne_zero_char_two`.
- **Hypotheses**: IsElliptic, char 2.
- **Uses from project**: `a₁X_plus_a₃_polynomial_ne_zero_char_two`, `x_gen`; `Affine.CoordinateRing.algebraMap_poly_injective`
- **Used by**: `mulByInt_two_pullback_y_gen_sq_root_unconditional`
- **Visibility**: private
- **Lines**: 2735–2763; proof length: 29

---

### `theorem mulByInt_two_pullback_y_gen_sq_root_unconditional`
- **Type**: `[IsElliptic] → [CharP K 2] → (h_card : Fintype.card K = 2) → ∃ g, g^q = (mulByInt W.toAffine q).pullback (y_gen W)`
- **What**: Unconditional q=2 char=2 y-side square root: `[2]^* y_gen` has a square root in K(E).
- **How**: Calls `mulByInt_q_pullback_y_gen_qth_root_of_witness` with `y_qth_root_q_eq_2_char_2`, the squaring identity from `y_qth_root_squared_eq_mulByInt_y_two_of_witnesses`, and the two polyExpandRoot squared equalities (using `polyExpandRoot_aeval_pow_eq` + `polyPowCardEq_of_finite` with `simpa [h_card]` to bridge `^card K` to `^2`).
- **Hypotheses**: IsElliptic, char 2, card K = 2.
- **Uses from project**: `mulByInt_q_pullback_y_gen_qth_root_of_witness`, `y_qth_root_q_eq_2_char_2`, `y_qth_root_squared_eq_mulByInt_y_two_of_witnesses`, `polyExpandRoot_aeval_pow_eq`, `polyPowCardEq_of_finite`, `omega2_coupled_residual_mem_expand_two_char_two`, `omega2_Y_coeff_mem_expand_two_char_two`, `aeval_x_gen_a₁X_plus_a₃_ne_zero_char_two`, `x_gen`
- **Used by**: `mulByInt_two_pullback_fieldRange_subset_frobenius_unconditional`
- **Visibility**: public
- **Lines**: 2772–2811; proof length: 40
- **Notes**: proof >30 lines

---

### `theorem mulByInt_two_pullback_fieldRange_subset_frobenius_unconditional`
- **Type**: `[IsElliptic] → [CharP K 2] → (h_card : Fintype.card K = 2) → ∀ z, (mulByInt W.toAffine q).pullback z ∈ (frobeniusIsog W).pullback.fieldRange`
- **What**: Final theorem for q=2 char=2: `Im([2]*) ⊆ Im(π*)` unconditionally. Closes the Silverman III.6.2 inclusion for `GF(2)`.
- **How**: Composes `mulByInt_q_pullback_fieldRange_subset_frobenius_of_xy_witness` with `functionField_eq_intermediateField_adjoin_xy`, `frobeniusIsog_pullback_mem_iff`, `mulByInt_two_pullback_x_gen_sq_root_unconditional`, `mulByInt_two_pullback_y_gen_sq_root_unconditional`.
- **Hypotheses**: IsElliptic, char 2, card K = 2.
- **Uses from project**: `mulByInt_q_pullback_fieldRange_subset_frobenius_of_xy_witness`, `functionField_eq_intermediateField_adjoin_xy`, `frobeniusIsog_pullback_mem_iff` (PurelyInsep), `mulByInt_two_pullback_x_gen_sq_root_unconditional`, `mulByInt_two_pullback_y_gen_sq_root_unconditional`, `frobeniusIsog`
- **Used by**: unused in file (capstone, exported)
- **Visibility**: public
- **Lines**: 2833–2844; proof length: 12

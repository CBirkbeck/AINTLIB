# Inventory: LutzNagell/ZSMul.lean

File: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/NagellLutz/LutzNagell/ZSMul.lean`

Proves `WeierstrassCurve.zsmul_eq_smulEval`: `n • P = ⟦(φₙ, ωₙ, ψₙ)⟧` in Jacobian coordinates for any integer `n` and nonsingular affine rational point `P = (x,y)` on a Weierstrass curve over a field. Strategy: even-odd induction reduces to doubling/addition formulas, which (via ring homs to the universal ring/field) reduce to universal polynomial identities, proved in the universal field via the affine multiplication formula and elliptic divisibility sequence identities.

---

### lemma evalEval_ψ₂
- Type: `W.ψ₂.evalEval x y = polyEval W x y curve.ψ₂`
- What: The second division polynomial ψ₂ specialized to `W` and evaluated at `(x,y)` equals the universal `curve.ψ₂` evaluated via `polyEval`.
- How: Unfolds `polyEval`, rewrites with `← map_ψ₂` (ψ₂ commutes with the specialization map) and `map_specialize`.
- Hypotheses: `W : WeierstrassCurve R`, `x y : R`.
- Uses from project: []
- Used by: `polyEval_cusp_ψ`, `polyEval_cusp_ψc`
- Visibility: public
- Lines: 88-89 (proof 1 line)
- Notes: none

### lemma evalEval_Ψ₃
- Type: `(C W.Ψ₃).evalEval x y = polyEval W x y (C curve.Ψ₃)`
- What: The (constant-embedded) third division polynomial Ψ₃ specialized to `W` and evaluated at `(x,y)` equals the universal `curve.Ψ₃` via `polyEval`.
- How: Unfolds `polyEval`, rewrites `map_C`, `coe_mapRingHom`, `← map_Ψ₃`, `map_specialize`.
- Hypotheses: `W : WeierstrassCurve R`, `x y : R`.
- Uses from project: []
- Used by: `polyEval_cusp_ψ`, `polyEval_cusp_ψc`
- Visibility: public
- Lines: 91-92 (proof 1 line)
- Notes: none

### lemma evalEval_preΨ₄
- Type: `(C W.preΨ₄).evalEval x y = polyEval W x y (C curve.preΨ₄)`
- What: The (constant-embedded) `preΨ₄` polynomial specialized to `W` and evaluated at `(x,y)` equals the universal `curve.preΨ₄` via `polyEval`.
- How: Unfolds `polyEval`, rewrites `map_C`, `coe_mapRingHom`, `← map_preΨ₄`, `map_specialize`.
- Hypotheses: `W : WeierstrassCurve R`, `x y : R`.
- Uses from project: []
- Used by: `polyEval_cusp_ψ`, `polyEval_cusp_ψc`
- Visibility: public
- Lines: 94-95 (proof 1 line)
- Notes: none

### lemma evalEval_ψ
- Type: `(W.ψ n).evalEval x y = polyEval W x y (curve.ψ n)`
- What: The n-th division polynomial ψₙ specialized to `W` and evaluated at `(x,y)` equals the universal `curve.ψ n` via `polyEval`.
- How: Unfolds `polyEval`, rewrites `← map_ψ` and `map_specialize`.
- Hypotheses: `W : WeierstrassCurve R`, `x y : R`, `n : ℤ`.
- Uses from project: []
- Used by: unused in file
- Visibility: public
- Lines: 99-100 (proof 1 line)
- Notes: none

### lemma evalEval_φ
- Type: `(W.φ n).evalEval x y = polyEval W x y (curve.φ n)`
- What: The n-th division polynomial φₙ specialized to `W` and evaluated at `(x,y)` equals the universal `curve.φ n` via `polyEval`.
- How: Unfolds `polyEval`, rewrites `← map_φ` and `map_specialize`.
- Hypotheses: `W : WeierstrassCurve R`, `x y : R`, `n : ℤ`.
- Uses from project: []
- Used by: unused in file
- Visibility: public
- Lines: 102-103 (proof 1 line)
- Notes: none

### lemma evalEval_ω
- Type: `(W.ω n).evalEval x y = polyEval W x y (curve.ω n)`
- What: The n-th division polynomial ωₙ specialized to `W` and evaluated at `(x,y)` equals the universal `curve.ω n` via `polyEval`.
- How: Unfolds `polyEval`, rewrites `← map_ω` and `map_specialize`.
- Hypotheses: `W : WeierstrassCurve R`, `x y : R`, `n : ℤ`.
- Uses from project: []
- Used by: unused in file
- Visibility: public
- Lines: 105-106 (proof 1 line)
- Notes: none

### lemma cusp_ψ₂
- Type: `cusp.ψ₂ = 2 * Y`
- What: For the universal cuspidal curve, ψ₂ equals `2 * Y`.
- How: `simp` unfolding `cusp`, `ψ₂`, `Affine.polynomialY`, `C_ofNat`.
- Hypotheses: none (universal `cusp`).
- Uses from project: []
- Used by: `polyEval_cusp_ψ`, `polyEval_cusp_ψc`
- Visibility: public
- Lines: 110 (proof 1 line)
- Notes: none

### lemma cusp_Ψ₃
- Type: `cusp.Ψ₃ = 3 * X ^ 4`
- What: For the universal cuspidal curve, Ψ₃ equals `3 * X^4`.
- How: `simp` unfolding `cusp`, `Ψ₃`, and the b-invariants `b₂, b₄, b₆, b₈`.
- Hypotheses: none.
- Uses from project: []
- Used by: `polyEval_cusp_ψ`, `polyEval_cusp_ψc`
- Visibility: public
- Lines: 111 (proof 1 line)
- Notes: none

### lemma cusp_preΨ₄
- Type: `cusp.preΨ₄ = 2 * X ^ 6`
- What: For the universal cuspidal curve, `preΨ₄` equals `2 * X^6`.
- How: `simp` unfolding `cusp`, `preΨ₄`, and the b-invariants.
- Hypotheses: none.
- Uses from project: []
- Used by: `polyEval_cusp_ψ`, `polyEval_cusp_ψc`
- Visibility: public
- Lines: 112 (proof 1 line)
- Notes: none

### lemma polyEval_cusp_ψ
- Type: `polyEval cusp 1 1 (curve.ψ n) = n`
- What: Evaluating the universal ψₙ on the cuspidal curve at `(1,1)` gives the integer `n` (the cusp realizes ψ as the identity EDS).
- How: Rewrites `ψ = normEDS …` via `map_normEDS`, replaces the three seed polynomials with their cusp values (`cusp_ψ₂`, `cusp_Ψ₃`, `cusp_preΨ₄`), then `normEDS_two_three_two` (the normalized EDS with seeds 2,3,2 is `n`).
- Hypotheses: `n : ℤ`.
- Uses from project: `evalEval_ψ₂`, `evalEval_Ψ₃`, `evalEval_preΨ₄`, `cusp_ψ₂`, `cusp_Ψ₃`, `cusp_preΨ₄`
- Used by: `polyEval_cusp_φ`, `ψᵤ_ne_zero`
- Visibility: public
- Lines: 114-116 (proof 3 lines)
- Notes: none

### lemma polyEval_cusp_φ
- Type: `polyEval cusp 1 1 (curve.φ n) = 1`
- What: Evaluating the universal φₙ on the cuspidal curve at `(1,1)` gives `1`.
- How: Unfolds `φ` (defined as `X·ψₙ² − ψₙ₊₁·ψₙ₋₁`), uses `polyEval_cusp_ψ` to replace each ψ-factor by an integer, then `ring`.
- Hypotheses: `n : ℤ`.
- Uses from project: `polyEval_cusp_ψ`
- Used by: `polyToField_φ_ne_zero`
- Visibility: public
- Lines: 118-120 (proof 2 lines)
- Notes: none

### lemma polyEval_cusp_ψc
- Type: `polyEval cusp 1 1 (curve.ψc n) = 2`
- What: Evaluating the universal companion `ψc n` on the cuspidal curve at `(1,1)` gives `2`.
- How: Rewrites `ψc = compl₂EDS …` via `map_compl₂EDS`, substitutes cusp seed values, then `compl₂EDS_two_three_two`.
- Hypotheses: `n : ℤ`.
- Uses from project: `evalEval_ψ₂`, `evalEval_Ψ₃`, `evalEval_preΨ₄`, `cusp_ψ₂`, `cusp_Ψ₃`, `cusp_preΨ₄`
- Used by: `polyEval_cusp_ω`
- Visibility: public
- Lines: 122-124 (proof 3 lines)
- Notes: none

### lemma polyEval_cusp_ω
- Type: `polyEval cusp 1 1 (curve.ω n) = 1`
- What: Evaluating the universal ωₙ on the cuspidal curve at `(1,1)` gives `1`.
- How: Applies `polyEval cusp 1 1` to the identity `curve.two_mul_ω n` (which expresses `2·ωₙ`), rewrites using `polyEval_cusp_ψc`, then `simpa` with `cusp`/`specialize`/`curve` unfolded.
- Hypotheses: `n : ℤ`.
- Uses from project: `polyEval_cusp_ψc`
- Used by: unused in file
- Visibility: public
- Lines: 126-129 (proof 4 lines)
- Notes: none

### abbrev ψᵤ
- Type: `ψᵤ (n : ℤ) : Universal.Field := polyToField (curve.ψ n)`
- What: The ψ-family of division polynomials viewed as elements of the universal field (image of `curve.ψ n` under `polyToField`).
- How: definitional (abbreviation).
- Hypotheses: `n : ℤ`.
- Uses from project: []
- Used by: `ψᵤ_eq_normEDS`, `isEllSequence_ψᵤ`, `net_ψᵤ`, `ψᵤ_ne_zero`, `polyToField_ψ₂Sq`, `smulX`, `smulY`, and many Affine/Jacobian lemmas.
- Visibility: public
- Lines: 131-132
- Notes: none

### lemma ψᵤ_eq_normEDS
- Type: `ψᵤ = normEDS (polyToField curve.ψ₂) (polyToField (C curve.Ψ₃)) (polyToField (C curve.preΨ₄))`
- What: As a function of `n`, `ψᵤ` is the normalized elliptic divisibility sequence with the three universal seed polynomials mapped into the universal field.
- How: `ext`, then `← map_normEDS` (normEDS commutes with the ring hom `polyToField`), then `rfl`.
- Hypotheses: none.
- Uses from project: `ψᵤ`
- Used by: `isEllSequence_ψᵤ`, `net_ψᵤ`
- Visibility: public
- Lines: 134-137 (proof 2 lines)
- Notes: none

### lemma isEllSequence_ψᵤ
- Type: `IsEllSequence ψᵤ`
- What: `ψᵤ` is an elliptic sequence (satisfies the EDS recurrence) in the universal field.
- How: Rewrites with `ψᵤ_eq_normEDS`, then `IsEllSequence.normEDS`.
- Hypotheses: none.
- Uses from project: `ψᵤ_eq_normEDS`
- Used by: `smulX_sub_smulX`
- Visibility: public
- Lines: 139 (proof 1 line)
- Notes: none

### lemma net_ψᵤ
- Type: `EllSequence.net ψᵤ p q r s = 0`
- What: The four-argument EDS "net" (Somos/elliptic net relation) of `ψᵤ` vanishes for all `p q r s`.
- How: Rewrites with `ψᵤ_eq_normEDS`, then applies `net_normEDS`.
- Hypotheses: `p q r s` (field-indexing integers).
- Uses from project: `ψᵤ_eq_normEDS`
- Used by: `smulY_add_sub_negY`
- Visibility: public
- Lines: 140 (proof 1 line)
- Notes: none

### lemma ψᵤ_ne_zero
- Type: `(h0 : n ≠ 0) : ψᵤ n ≠ 0`
- What: For nonzero `n`, the universal `ψᵤ n` is nonzero in the universal field.
- How: Contradiction: if `ψᵤ n = 0` then (injectivity of `IsFractionRing`) the ring element is 0; applying `ringEval cusp_equation_one_one` and `polyEval_cusp_ψ` forces `n = 0`.
- Hypotheses: `n ≠ 0`.
- Uses from project: `ψᵤ`, `polyEval_cusp_ψ`
- Used by: pervasive — `smulX_eq`, `smulX_sub_smulX`, `smulX_ne_smulX`, `smulY_sub_negY`, `smulY_one_sub_negY`, `slopeOne_eq_neg_div`, `addX_smul_one_smul_one`, `addY_smul_one_smul_one`, `smulY_neg`, `smulX_add`, `smulY_add_sub_negY`, `zsmul_point_eq_smulField`, `dblXYZ_smulField`, `addXYZ_smulField`.
- Visibility: public
- Lines: 142-146 (proof 4 lines)
- Notes: none

### lemma polyToField_φ_ne_zero
- Type: `polyToField (curve.φ n) ≠ 0`
- What: The universal φₙ is nonzero in the universal field (for every `n`).
- How: Contradiction via `IsFractionRing` injectivity, applying `ringEval cusp_equation_one_one` and `polyEval_cusp_φ` to force `1 = 0`.
- Hypotheses: `n : ℤ` (implicit).
- Uses from project: `polyEval_cusp_φ`
- Used by: `smulX_ne_zero`
- Visibility: public
- Lines: 148-152 (proof 4 lines)
- Notes: none

### lemma polyToField_ψ₂Sq
- Type: `polyToField (C curve.Ψ₂Sq) = ψᵤ 2 ^ 2`
- What: The image of the constant polynomial `Ψ₂Sq` in the universal field equals `(ψᵤ 2)²`.
- How: Rewrites `ψ_two`, `ψ₂_sq` (ψ₂² = Ψ₂Sq + (polynomial)·…), `polyToField_polynomial` killing the Weierstrass-polynomial term, then `mul_zero`/`add_zero`.
- Hypotheses: none.
- Uses from project: `ψᵤ`
- Used by: `addX_smul_one_smul_one`
- Visibility: public
- Lines: 154-155 (proof 1 line)
- Notes: none

### def Affine.smulX
- Type: `smulX (n) : Universal.Field := polyToField (curve.φ n) / (ψᵤ n) ^ 2`
- What: The rational function φₙ/ψₙ², the candidate X-coordinate of `n • (X,Y)` on the universal curve.
- How: definitional.
- Hypotheses: `n : ℤ`.
- Uses from project: `ψᵤ`
- Used by: `smulX_zero`, `smulX_one`, `smulX_eq`, `smulX_sub_smulX`, `smulX_neg`, `smulX_ne_zero`, `smulX_ne_smulX`, `smulY_sub_negY`, `slopeOne`, `addX_smul_one_smul_one`, `smulX_add`, `smulY_add_sub_negY`, `smulY_neg`, `zsmul_point_eq_smulX_smulY`, `nonsingular_smulX_smulY`, `zsmul_point_eq_smulField`.
- Visibility: public
- Lines: 162-164
- Notes: `attribute [local instance] Classical.propDecidable` in scope (line 159).

### def Affine.smulY
- Type: `smulY (n) : Universal.Field := polyToField (curve.ω n) / (ψᵤ n) ^ 3`
- What: The rational function ωₙ/ψₙ³, the candidate Y-coordinate of `n • (X,Y)` on the universal curve.
- How: definitional.
- Hypotheses: `n : ℤ`.
- Uses from project: `ψᵤ`
- Used by: `smulY_zero`, `smulY_one`, `smulY_sub_negY`, `slopeOne`, `addY_smul_one_smul_one`, `smulY_neg`, `smulX_add`, `smulY_add_sub_negY`, `zsmul_point_eq_smulX_smulY`, `nonsingular_smulX_smulY`, `zsmul_point_eq_smulField`.
- Visibility: public
- Lines: 166-168
- Notes: none

### lemma Affine.smulX_zero
- Type: `smulX 0 = 0`
- What: `smulX 0 = 0`.
- How: `simp [smulX, ψᵤ]` (φ₀ = 0 / ψ₀ = 0 handling).
- Hypotheses: none.
- Uses from project: `smulX`, `ψᵤ`
- Used by: `smulX_ne_smulX`
- Visibility: public (`@[simp]`)
- Lines: 171 (proof 1 line)
- Notes: none

### lemma Affine.smulY_zero
- Type: `smulY 0 = 0`
- What: `smulY 0 = 0`.
- How: `simp [smulY, ψᵤ]`.
- Hypotheses: none.
- Uses from project: `smulY`, `ψᵤ`
- Used by: unused in file
- Visibility: public (`@[simp]`)
- Lines: 172 (proof 1 line)
- Notes: none

### lemma Affine.smulX_one
- Type: `smulX 1 = polyToField (C X)`
- What: `smulX 1` equals the image of the universal coordinate `X` (so `1•(X,Y)` has X-coordinate `X`).
- How: `simp [smulX, ψᵤ]` (ψ₁ = 1, φ₁ = X).
- Hypotheses: none.
- Uses from project: `smulX`, `ψᵤ`
- Used by: `smulX_eq`, `smulX_one` callers — `addX_smul_one_smul_one`, `addY_smul_one_smul_one`, `slopeOne_eq_neg_div`.
- Visibility: public (`@[simp]`)
- Lines: 173 (proof 1 line)
- Notes: none

### lemma Affine.smulY_one
- Type: `smulY 1 = polyToField Y`
- What: `smulY 1` equals the image of the universal coordinate `Y`.
- How: `simp [smulY, ψᵤ]`.
- Hypotheses: none.
- Uses from project: `smulY`, `ψᵤ`
- Used by: `smulY_one_sub_negY`, `slopeOne_eq_neg_div`, `addX_smul_one_smul_one`, `addY_smul_one_smul_one`.
- Visibility: public (`@[simp]`)
- Lines: 174 (proof 1 line)
- Notes: none

### lemma Affine.smulX_eq
- Type: `(hn : n ≠ 0) : smulX n = smulX 1 - ψᵤ (n + 1) * ψᵤ (n - 1) / (ψᵤ n) ^ 2`
- What: Expresses `smulX n` via the standard EDS formula `X − ψₙ₊₁ψₙ₋₁/ψₙ²`.
- How: Unfolds `smulX`, `φ` (`= X·ψₙ² − ψₙ₊₁ψₙ₋₁`), clears denominators with `div_eq_iff` (using `ψᵤ_ne_zero`), substitutes `smulX_one`, then `abel`.
- Hypotheses: `n ≠ 0`.
- Uses from project: `smulX`, `ψᵤ`, `ψᵤ_ne_zero`, `smulX_one`
- Used by: `smulX_two`, `smulX_sub_smulX`
- Visibility: public
- Lines: 176-181 (proof 5 lines)
- Notes: none

### lemma Affine.smulX_two
- Type: `smulX 2 = smulX 1 - ψᵤ 3 / (ψᵤ 2) ^ 2`
- What: The X-coordinate of `2•(X,Y)`, specializing `smulX_eq` at `n=2` (`ψᵤ 3 / ψᵤ 2²`).
- How: `simp [smulX_eq two_ne_zero, ψᵤ]`.
- Hypotheses: none.
- Uses from project: `smulX_eq`, `ψᵤ`
- Used by: `addX_smul_one_smul_one`, `addY_smul_one_smul_one`
- Visibility: public
- Lines: 183-184 (proof 1 line)
- Notes: none

### lemma Affine.smulX_sub_smulX
- Type: `(hm : m ≠ 0) (hn : n ≠ 0) : smulX m - smulX n = (ψᵤ (n + m) * ψᵤ (n - m)) / (ψᵤ n * ψᵤ m) ^ 2`
- What: The difference of two X-coordinates equals ψₙ₊ₘ·ψₙ₋ₘ / (ψₙψₘ)² — a key EDS identity.
- How: Rewrites both via `smulX_eq`, an inline `ring` lemma rearranging `(c−a)−(c−b)`, `div_sub_div`, then converts the numerator using the elliptic sequence relation `isEllSequence_ψᵤ n m 1`; side goals discharged by `pow_ne_zero (ψᵤ_ne_zero …)`.
- Hypotheses: `m ≠ 0`, `n ≠ 0`.
- Uses from project: `smulX_eq`, `isEllSequence_ψᵤ`, `ψᵤ`, `ψᵤ_ne_zero`
- Used by: `smulX_sub_sub_smulX_add`, `smulX_ne_smulX`, `smulX_add`, `smulY_add_sub_negY`
- Visibility: public
- Lines: 186-194 (proof 8 lines)
- Notes: none

### lemma Affine.smulX_sub_sub_smulX_add
- Type: `(add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) : smulX (n - m) - smulX (n + m) = (ψᵤ (2 * n) * ψᵤ (2 * m)) / (ψᵤ (n + m) * ψᵤ (n - m)) ^ 2`
- What: A doubled-index difference identity `smulX(n−m) − smulX(n+m) = ψ₂ₙψ₂ₘ/(ψₙ₊ₘψₙ₋ₘ)²`.
- How: Applies `smulX_sub_smulX sub_ne add_ne`, then `simp` with the arithmetic rewrites `(n+m)+(n−m)=2n` and `(n+m)−(n−m)=2m`.
- Hypotheses: `n + m ≠ 0`, `n - m ≠ 0`.
- Uses from project: `smulX_sub_smulX`, `ψᵤ`
- Used by: `smulX_add`
- Visibility: public
- Lines: 196-199 (proof 4 lines)
- Notes: none

### lemma Affine.smulX_neg
- Type: `smulX (-n) = smulX n`
- What: `smulX` is even in `n` (the X-coordinate of `−P` equals that of `P`).
- How: `simp_rw` unfolding `smulX`, `φ_neg`, `ψ_neg`, `← map_pow`, `neg_sq` (ψ₋ₙ = −ψₙ but squared, φ₋ₙ = φₙ).
- Hypotheses: none.
- Uses from project: `smulX`, `ψᵤ`
- Used by: `smulX_eq_smulX_iff`, `zsmul_point_eq_smulX_smulY`
- Visibility: public
- Lines: 201 (proof 1 line)
- Notes: none

### lemma Affine.smulX_ne_zero
- Type: `(h0 : n ≠ 0) : smulX n ≠ 0`
- What: For nonzero `n`, `smulX n ≠ 0`.
- How: `div_ne_zero` from `polyToField_φ_ne_zero` (numerator) and `pow_ne_zero (ψᵤ_ne_zero h0)` (denominator).
- Hypotheses: `n ≠ 0`.
- Uses from project: `smulX`, `polyToField_φ_ne_zero`, `ψᵤ_ne_zero`
- Used by: `smulX_ne_smulX`
- Visibility: public
- Lines: 203-204 (proof 2 lines)
- Notes: none

### lemma Affine.smulX_ne_smulX
- Type: `(ne : m ≠ n) (ne_neg : m ≠ -n) : smulX m ≠ smulX n`
- What: Distinct indices `m ≠ ±n` give distinct X-coordinates (injectivity up to sign).
- How: Case-splits `m=0`/`n=0` (using `smulX_zero`, `smulX_ne_zero`); otherwise rewrites `← sub_ne_zero`, `smulX_sub_smulX`, and shows the ψ-factors are all nonzero via `ψᵤ_ne_zero` (after recasting `m ≠ n` and `m ≠ -n` as `n−m ≠ 0` and `n+m ≠ 0`).
- Hypotheses: `m ≠ n`, `m ≠ -n`.
- Uses from project: `smulX_zero`, `smulX_ne_zero`, `smulX_sub_smulX`, `ψᵤ_ne_zero`
- Used by: `smulX_eq_smulX_iff`, `zsmul_point_eq_smulX_smulY`
- Visibility: public
- Lines: 206-215 (proof 9 lines)
- Notes: none

### lemma Affine.smulX_eq_smulX_iff
- Type: `smulX m = smulX n ↔ m = n ∨ m = -n`
- What: Two X-coordinates coincide iff the indices are equal or negatives.
- How: Forward by `contrapose!` + `smulX_ne_smulX`; backward by `rintro` with `rfl`/`rfl` and `smulX_neg`.
- Hypotheses: `m n : ℤ`.
- Uses from project: `smulX_ne_smulX`, `smulX_neg`
- Used by: unused in file
- Visibility: public
- Lines: 217-220 (proof 4 lines)
- Notes: none

### lemma Affine.smulY_sub_negY_aux
- Type: `{F} [Field F] {a₁ a₃ x y z : F} (h0 : z ≠ 0) : y/z³ − (−(y/z³) − a₁(x/z²) − a₃) = z(2y + a₁xz + a₃z³)/z⁴`
- What: A pure field-algebra identity supporting `smulY_sub_negY` (the `y − negY` computation cleared of denominators).
- How: `field_simp; ring`.
- Hypotheses: `z ≠ 0`.
- Uses from project: []
- Used by: `smulY_sub_negY`
- Visibility: private
- Lines: 222-225 (proof 1 line)
- Notes: none

### lemma Affine.smulY_sub_negY
- Type: `(h0 : n ≠ 0) : smulY n - pointedCurve.toAffine.negY (smulX n) (smulY n) = ψᵤ (2 * n) / (ψᵤ n) ^ 4`
- What: `y − (−y)` at the n-th multiple equals ψ₂ₙ/ψₙ⁴ — a fundamental "doubled ψ" identity.
- How: Unfolds `negY`, `smulX`, `smulY`, uses `← ψc_spec` and `← ω_spec` (relating ψc/ω to the EDS), maps everything into the field, then closes with `smulY_sub_negY_aux (ψᵤ_ne_zero h0)`.
- Hypotheses: `n ≠ 0`.
- Uses from project: `smulX`, `smulY`, `ψᵤ`, `smulY_sub_negY_aux`, `ψᵤ_ne_zero`
- Used by: `smulY_one_sub_negY`, `smulX_add`, `smulY_add_sub_negY`
- Visibility: public
- Lines: 227-231 (proof 4 lines)
- Notes: none

### lemma Affine.smulY_one_sub_negY
- Type: `smulY 1 - pointedCurve.toAffine.negY (smulX 1) (smulY 1) = ψᵤ 2`
- What: At `n=1`, `y − negY = ψᵤ 2` (the value ψ₂ at the base point).
- How: `smulY_sub_negY one_ne_zero`, then `mul_one`, `ψ_one`, `map_one`, `one_pow`, `div_one`.
- Hypotheses: none.
- Uses from project: `smulY_sub_negY`, `ψᵤ`
- Used by: `smulY_one_ne_negY`, `slopeOne_eq_neg_div`
- Visibility: public
- Lines: 233-235 (proof 2 lines)
- Notes: none

### lemma Affine.smulY_one_ne_negY
- Type: `smulY 1 ≠ pointedCurve.toAffine.negY (smulX 1) (smulY 1)`
- What: At the base point, `y ≠ negY` (so doubling uses the tangent/slope formula, not the vertical case).
- How: `← sub_ne_zero`, `smulY_one_sub_negY`, then `ψᵤ_ne_zero two_ne_zero`.
- Hypotheses: none.
- Uses from project: `smulY_one_sub_negY`, `ψᵤ_ne_zero`
- Used by: `slopeOne_eq_neg_div`, `zsmul_point_eq_smulX_smulY`
- Visibility: public
- Lines: 237-238 (proof 2 lines)
- Notes: none

### def Affine.slopeOne
- Type: `slopeOne : Universal.Field := pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)`
- What: The slope of the tangent line to the universal curve at the base point `(X,Y)` (slope for doubling).
- How: definitional.
- Hypotheses: none.
- Uses from project: `smulX`, `smulY`
- Used by: `slopeOne_eq_neg_div`, `addX_smul_one_smul_one`, `addY_smul_one_smul_one`
- Visibility: public
- Lines: 240-242
- Notes: none

### lemma Affine.slopeOne_eq_neg_div
- Type: `slopeOne = -polyToField curve.polynomialX / ψᵤ 2`
- What: The tangent slope at the base point equals `−polynomialX / ψ₂`.
- How: Unfolds `slopeOne`, uses `Affine.slope_of_Y_ne` (the `Y ≠ negY` slope branch, justified by `smulY_one_ne_negY`), `smulY_one_sub_negY`, `Affine.polynomialX`, then `field_simp; norm_num` (needs `ψᵤ 2 ≠ 0`).
- Hypotheses: none.
- Uses from project: `slopeOne`, `ψᵤ_ne_zero`, `smulY_one_ne_negY`, `smulY_one_sub_negY`, `smulX_one`, `smulY_one`, `ψᵤ`
- Used by: `addX_smul_one_smul_one`, `addY_smul_one_smul_one`
- Visibility: public
- Lines: 244-250 (proof 6 lines)
- Notes: none

### lemma Affine.addX_smul_one_smul_one_aux
- Type: `{F} [Field F] {a₁ a₂ x dx dy : F} (h0 : dy ≠ 0) : (−dx/dy)² + a₁(−dx/dy) − a₂ − x − x − x = (dx² − a₁dx dy − (3x+a₂)dy²)/dy²`
- What: A field-algebra identity underlying the doubling-X formula (slope² + a₁·slope − a₂ − 3x).
- How: `field_simp; ring`.
- Hypotheses: `dy ≠ 0`.
- Uses from project: []
- Used by: unused in file
- Visibility: private
- Lines: 252-255 (proof 1 line)
- Notes: none. (Declared but not referenced; see File Summary.)

### lemma Affine.addX_smul_ring_identity
- Type: `{F} [Field F] {X' ψ a₁ a₂ cx : F} : X'(X' + −(ψa₁)) − ψ²a₂ − ψ²cx − ψ²cx = ψ²cx − (ψ²(cx·3 + a₂) − X'² + X'ψa₁ − a₁²·0)`
- What: A pure ring identity used to finish `addX_smul_one_smul_one` after clearing denominators.
- How: `ring`.
- Hypotheses: none.
- Uses from project: []
- Used by: `addX_smul_one_smul_one`
- Visibility: private
- Lines: 257-259 (proof 1 line)
- Notes: none

### lemma Affine.addX_smul_one_smul_one
- Type: `pointedCurve.toAffine.addX (smulX 1) (smulX 1) slopeOne = smulX 2`
- What: The affine doubling X-formula at the base point yields `smulX 2` (consistency of the doubling formula with `smulX`).
- How: Unfolds `Affine.addX`, substitutes `slopeOne_eq_neg_div`, `smulX_two`, `smulX_one`, rewrites ψ-values (`ψ_two`, `ψ_three`, `C_Ψ₃_eq`, `polyToField_ψ₂Sq`, `polyToField_polynomial`), clears denominators with `field_simp [hψ₂]`, then closes by `addX_smul_ring_identity`.
- Hypotheses: none (`ψᵤ 2 ≠ 0` derived inline).
- Uses from project: `ψᵤ_ne_zero`, `slopeOne_eq_neg_div`, `smulX_two`, `smulX_one`, `ψᵤ`, `polyToField_ψ₂Sq`, `addX_smul_ring_identity`, `slopeOne`
- Used by: `addY_smul_one_smul_one`, `zsmul_point_eq_smulX_smulY`
- Visibility: public
- Lines: 261-269 (proof 9 lines)
- Notes: none

### lemma Affine.addY_smul_one_smul_one_aux
- Type: `{F} [Field F] {a₁ a₃ dx dy x y ψ₃ t : F} (h0 : dy ≠ 0) : ((a₁dy − dx)ψ₃ + 0·t + (−y − (a₁x+a₃))dy³)/dy³ = −(−dx/dy·(x − ψ₃/dy² − x) + y) − a₁(x − ψ₃/dy²) − a₃`
- What: A field-algebra identity underlying the doubling-Y formula.
- How: `field_simp; ring`.
- Hypotheses: `dy ≠ 0`.
- Uses from project: []
- Used by: `addY_smul_one_smul_one`
- Visibility: private
- Lines: 271-274 (proof 1 line)
- Notes: none

### lemma Affine.addY_smul_one_smul_one
- Type: `pointedCurve.toAffine.addY (smulX 1) (smulX 1) (smulY 1) slopeOne = smulY 2`
- What: The affine doubling Y-formula at the base point yields `smulY 2`.
- How: Proven as `.symm` of: unfold `smulY`, `ω`, use `redInvarDenom_two`, `compl₂EDSAux_two`, `Affine.addY`/`negAddY`, substitute `addX_smul_one_smul_one`, `smulX_two`, `negY`, `negPolynomial`, `slopeOne_eq_neg_div`, ψ-rewrites, then close by `addY_smul_one_smul_one_aux (ψᵤ_ne_zero two_ne_zero)`.
- Hypotheses: none.
- Uses from project: `addX_smul_one_smul_one`, `smulX_two`, `slopeOne_eq_neg_div`, `smulX_one`, `smulY_one`, `ψᵤ`, `addY_smul_one_smul_one_aux`, `ψᵤ_ne_zero`, `slopeOne`, `smulY`
- Used by: `zsmul_point_eq_smulX_smulY`
- Visibility: public
- Lines: 276-284 (proof 7 lines)
- Notes: `open EllSequence in` modifier.

### lemma Affine.smulY_neg_aux
- Type: `{F} [Field F] {a₁ a₃ x y z : F} (hz : z ≠ 0) : (y + a₁xz + a₃z³)/(−z)³ = −(y/z³) − a₁(x/z²) − a₃`
- What: A field-algebra identity underlying `smulY_neg`.
- How: `rw [neg_pow]; field_simp; ring`.
- Hypotheses: `z ≠ 0`.
- Uses from project: []
- Used by: `smulY_neg`
- Visibility: private
- Lines: 286-288 (proof 1 line)
- Notes: none

### lemma Affine.smulY_neg
- Type: `(h0 : n ≠ 0) : smulY (-n) = pointedCurve.toAffine.negY (smulX n) (smulY n)`
- What: The Y-coordinate of `−P` (i.e. `smulY (−n)`) equals `negY` of the n-th coordinates.
- How: Unfolds `negY`, `smulX`, `smulY`, `ψ_neg`, `ω_neg`, maps into the field, then `smulY_neg_aux (ψᵤ_ne_zero h0)`.
- Hypotheses: `n ≠ 0`.
- Uses from project: `smulX`, `smulY`, `ψᵤ`, `smulY_neg_aux`, `ψᵤ_ne_zero`
- Used by: `zsmul_point_eq_smulX_smulY`
- Visibility: public
- Lines: 290-293 (proof 4 lines)
- Notes: none

### lemma Affine.smulX_add_aux
- Type: `{F} [Field F] {m n m₂ n₂ a s : F} (hm hn ha hs : ≠0) : n₂/n⁴ · (m₂/m⁴) / (a·s/(n·m)²)² = n₂·m₂/(a·s)²`
- What: A field-algebra identity (denominator bookkeeping) supporting the addition-X formula `smulX_add`.
- How: `field_simp`.
- Hypotheses: `m ≠ 0`, `n ≠ 0`, `a ≠ 0`, `s ≠ 0`.
- Uses from project: []
- Used by: `smulX_add`
- Visibility: private
- Lines: 295-298 (proof 1 line)
- Notes: none

### lemma Affine.smulX_add
- Type: `(hm : m ≠ 0) (hn : n ≠ 0) (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) : let ψ₂ x y := y − negY x y; smulX (n + m) = smulX (n - m) − ψ₂(smulX n)(smulY n)·ψ₂(smulX m)(smulY m)/(smulX m − smulX n)²`
- What: The affine addition formula for the X-coordinate of `(n+m)•P` in terms of the n-th and m-th coordinates (group-law addition-X).
- How: `change`s the `let`-bound ψ₂ to explicit `y − negY`, rewrites to `eq_sub_iff_add_eq`, then a `calc`: substitute `smulY_sub_negY` and `smulX_sub_smulX`, apply `smulX_add_aux` (4× `ψᵤ_ne_zero`), then `smulX_sub_sub_smulX_add.symm`.
- Hypotheses: `m ≠ 0`, `n ≠ 0`, `n + m ≠ 0`, `n - m ≠ 0`.
- Uses from project: `smulX`, `smulY`, `smulY_sub_negY`, `smulX_sub_smulX`, `smulX_add_aux`, `ψᵤ`, `ψᵤ_ne_zero`, `smulX_sub_sub_smulX_add`
- Used by: `zsmul_point_eq_smulX_smulY`
- Visibility: public
- Lines: 300-315 (proof 12 lines)
- Notes: hinges on EDS identities `smulY_sub_negY`, `smulX_sub_smulX`, `smulX_sub_sub_smulX_add`.

### lemma Affine.smulY_add_sub_negY_aux
- Type: `{F} [Field F] {m n m₂ n₂ a s am an : F} (hm hn ha hs : ≠0) : (m₂/m⁴·(an·m/(a·n)²) − n₂/n⁴·(am·n/(a·m)²))/(a·s/(n·m)²) = (an·m₂·n − am·n₂·m)·a/(s·n·m)/a⁴`
- What: A field-algebra identity (denominator bookkeeping) supporting the addition-Y formula `smulY_add_sub_negY`.
- How: `field_simp`.
- Hypotheses: `m ≠ 0`, `n ≠ 0`, `a ≠ 0`, `s ≠ 0`.
- Uses from project: []
- Used by: `smulY_add_sub_negY`
- Visibility: private
- Lines: 317-322 (proof 1 line)
- Notes: none

### lemma Affine.smulY_add_sub_negY
- Type: `(hm : m ≠ 0) (hn : n ≠ 0) (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) : let ψ₂ x y := y − negY x y; ψ₂(smulX(n+m))(smulY(n+m)) = (ψ₂(smulX m)(smulY m)·(smulX n − smulX(n+m)) − ψ₂(smulX n)(smulY n)·(smulX m − smulX(n+m)))/(smulX m − smulX n)`
- What: An addition formula for the `y − negY` quantity at `(n+m)•P` — the Y-side companion to `smulX_add`.
- How: `simp_rw` substitutes `smulY_sub_negY` (3×) and `smulX_sub_smulX` (3×), applies `smulY_add_sub_negY_aux` (4× `ψᵤ_ne_zero`), then a `congr` + `eq_div_iff` whose numerator identity comes from the EDS "net" relation `EllSequence.net_add_sub_iff` applied to `net_ψᵤ`, closed by `linear_combination (norm := ring_nf)`.
- Hypotheses: `m ≠ 0`, `n ≠ 0`, `n + m ≠ 0`, `n - m ≠ 0`.
- Uses from project: `smulY_sub_negY`, `smulX_sub_smulX`, `smulY_add_sub_negY_aux`, `ψᵤ_ne_zero`, `net_ψᵤ`, `smulX`, `smulY`, `ψᵤ`
- Used by: `zsmul_point_eq_smulX_smulY`
- Visibility: public
- Lines: 324-336 (proof 13 lines)
- Notes: hinges on `EllSequence.net_add_sub_iff` (mathlib/project EDS net relation) + `net_ψᵤ`.

### instance Affine (AddGroup …)
- Type: `instance : AddGroup ((curve.baseChange Universal.Field).toAffine.Point) := inferInstance`
- What: Registers the affine point group structure on the universal curve base-changed to the universal field (re-exposing the inferred instance).
- How: `inferInstance` (under `open WeierstrassCurve.Affine in`).
- Hypotheses: none.
- Uses from project: []
- Used by: (instance — used implicitly by `zsmul_point_eq_smulX_smulY` etc.)
- Visibility: public (instance)
- Lines: 340-341
- Notes: none

### theorem Affine.zsmul_point_eq_smulX_smulY
- Type: `n ≠ 0 → ∃ h : Affine.Nonsingular _ (smulX n) (smulY n), n • Affine.point = .some _ _ h`
- What: For nonzero `n`, the affine point `n • (X,Y)` on the universal curve is the nonsingular point with coordinates `(smulX n, smulY n)`. This is the central universal affine multiplication formula.
- How: `Int.negInduction`; the `nat` case is strong induction with base cases `n=0,1,2` (using `equation_point`, `addX/addY_smul_one_smul_one`, `add_self_of_Y_ne`); the induction step builds `(n2+1)` from `n2` and `1` via `add_of_X_ne`, with X-coordinate identity from `smulX_add` + `Affine.addX_eq_addX_negY_sub` and Y-coordinate from `smulY_add_sub_negY` + `Affine.addY_sub_negY_addY`; the `neg` case uses `smulX_neg`, `smulY_neg`, `Affine.nonsingular_neg`.
- Hypotheses: `n ≠ 0`.
- Uses from project: `smulX`, `smulY`, `smulX_one`, `smulY_one`, `addX_smul_one_smul_one`, `addY_smul_one_smul_one`, `smulY_one_ne_negY`, `smulX_ne_smulX`, `smulX_add`, `smulY_add_sub_negY`, `smulX_neg`, `smulY_neg`
- Used by: `nonsingular_smulX_smulY`, `zsmul_point_ne_zero` (Affine), `zsmul_point_eq_smulField`
- Visibility: public
- Lines: 343-383 (proof ~38 lines)
- Notes: long(30-50) — proof ~38 lines; uses `erw`. Candidate for `/decompose-proof`.

### lemma Affine.nonsingular_smulX_smulY
- Type: `(hn : n ≠ 0) : Affine.Nonsingular curveField (smulX n) (smulY n)`
- What: For nonzero `n`, `(smulX n, smulY n)` is a nonsingular point of the universal curve over the universal field.
- How: Extracts the existential witness `.1` from `zsmul_point_eq_smulX_smulY hn`.
- Hypotheses: `n ≠ 0`.
- Uses from project: `zsmul_point_eq_smulX_smulY`, `smulX`, `smulY`
- Used by: `nonsingular_smulField` (via `zsmul_point_eq_smulField` chain — actually used by Jacobian.`nonsingular_smulField`? see below), `addXYZ_smulField` indirectly. Direct in-file: `Jacobian.nonsingular_smulField`.
- Visibility: public
- Lines: 385-386 (proof 1 line)
- Notes: none

### lemma Affine.zsmul_point_ne_zero
- Type: `(h0 : n ≠ 0) : n • Affine.point ≠ 0`
- What: The base point `(X,Y)` is non-torsion: `n • (X,Y) ≠ O` for all nonzero `n`.
- How: From `zsmul_point_eq_smulX_smulY h0`, rewrite and apply `Affine.Point.some_ne_zero`.
- Hypotheses: `n ≠ 0`.
- Uses from project: `zsmul_point_eq_smulX_smulY`
- Used by: `Jacobian.zsmul_point_ne_zero`
- Visibility: public
- Lines: 388-391 (proof 3 lines)
- Notes: none

### lemma Jacobian.zsmul_point_ne_zero
- Type: `(h0 : n ≠ 0) : n • Jacobian.point ≠ 0`
- What: The base point in Jacobian coordinates is non-torsion: `n • point ≠ O`.
- How: Transports the affine result `Affine.zsmul_point_ne_zero` across the additive equivalence `toAffineAddEquiv` (uses `map_zsmul`, `map_eq_zero_iff` with its injectivity).
- Hypotheses: `n ≠ 0`.
- Uses from project: `Affine.zsmul_point_ne_zero`
- Used by: `zsmul_point_ne`
- Visibility: public
- Lines: 402-405 (proof 3 lines)
- Notes: `open Point in` modifier.

### lemma Jacobian.zsmul_point_ne
- Type: `(h : m ≠ n) : m • Jacobian.point ≠ n • Jacobian.point`
- What: Distinct integer multiples of the Jacobian base point are distinct.
- How: `← sub_ne_zero`, `sub_eq_add_neg`, `← sub_zsmul`, then `zsmul_point_ne_zero (sub_ne_zero.mpr h)`.
- Hypotheses: `m ≠ n`.
- Uses from project: `Jacobian.zsmul_point_ne_zero`
- Used by: `addXYZ_smulField`
- Visibility: public
- Lines: 407-409 (proof 2 lines)
- Notes: none

### lemma Jacobian.point_point
- Type: `Jacobian.point.point = ⟦![polyToField (C X), polyToField Y, 1]⟧`
- What: The Jacobian base point's underlying coordinate class is `⟦(X, Y, 1)⟧`.
- How: `rfl`.
- Hypotheses: none.
- Uses from project: []
- Used by: unused in file
- Visibility: public
- Lines: 411 (proof rfl)
- Notes: none

### abbrev Jacobian.smulPoly
- Type: `smulPoly (n : ℤ) : Fin 3 → Poly := ![curve.φ n, curve.ω n, curve.ψ n]`
- What: The three universal division-polynomial families bundled as a 3-tuple `(φₙ, ωₙ, ψₙ)` of polynomials.
- How: definitional (vector literal).
- Hypotheses: `n : ℤ`.
- Uses from project: []
- Used by: `smulRing`, `smulField`, `dblZ_smulPoly`, `dblXYZ_smulField`, `zsmul_point_eq_smulField`, `ω_neg_eq_neg_negY`, `smulPoly_neg`, `smulPoly_zero`, `addZ_smulPoly`
- Visibility: public
- Lines: 413-414
- Notes: none

### abbrev Jacobian.smulRing
- Type: `smulRing (n : ℤ) : Fin 3 → Universal.Ring := AdjoinRoot.mk _ ∘ smulPoly n`
- What: The 3-tuple of division polynomials as elements of the universal ring (quotient by the Weierstrass polynomial).
- How: definitional (post-compose with `AdjoinRoot.mk`).
- Hypotheses: `n : ℤ`.
- Uses from project: `smulPoly`
- Used by: `algebraMap_comp_smulRing`, `dblXYZ_smulRing`, `smulRing_neg`, `addXYZ_smulRing`, `addXYZ_smulRing₁`, and (top-level) `ringEval_comp_smulRing`, `ringEval_ψ`, etc.
- Visibility: public
- Lines: 415-416
- Notes: none

### abbrev Jacobian.smulField
- Type: `smulField (n : ℤ) : Fin 3 → Universal.Field := polyToField ∘ smulPoly n`
- What: The 3-tuple of division polynomials as elements of the universal field.
- How: definitional (post-compose with `polyToField`).
- Hypotheses: `n : ℤ`.
- Uses from project: `smulPoly`
- Used by: `algebraMap_comp_smulRing`, `zsmul_point_eq_smulField`, `nonsingular_smulField`, `dblXYZ_smulField`, `dblXYZ_smulRing`, `smulField_neg`, `smulField_zero`, `addXYZ_smulField`, `addXYZ_smulRing`, `addXYZ_smulField₁`.
- Visibility: public
- Lines: 417-418
- Notes: none

### lemma Jacobian.algebraMap_comp_smulRing
- Type: `(n : ℤ) : algebraMap _ _ ∘ smulRing n = smulField n`
- What: Applying the structure map `Universal.Ring → Universal.Field` componentwise to `smulRing n` recovers `smulField n`.
- How: `ext i; fin_cases i <;> rfl`.
- Hypotheses: `n : ℤ`.
- Uses from project: `smulRing`, `smulField`
- Used by: unused in file
- Visibility: public
- Lines: 420-421 (proof 1 line)
- Notes: none

### theorem Jacobian.zsmul_point_eq_smulField
- Type: `(n • Jacobian.point).point = ⟦smulField n⟧`
- What: The Jacobian coordinates of `n • (X,Y)` on the universal curve are exactly `⟦(φₙ, ωₙ, ψₙ)⟧` (universal multiplication formula in Jacobian coords).
- How: Reduces to the affine result: `n=0` case directly (`φ₀,ω₀,ψ₀`); for `n ≠ 0`, transports `Affine.zsmul_point_eq_smulX_smulY` through `toAffineAddEquiv`, then `Quotient.sound` with the unit scaling `inv (ψᵤ n)` matching Jacobian smul to `(smulX, smulY)` (uses `Jacobian.smul_fin3`, `inv_mul_eq_div`).
- Hypotheses: `n : ℤ`.
- Uses from project: `smulField`, `smulPoly`, `Affine.zsmul_point_eq_smulX_smulY`, `ψᵤ_ne_zero`, `Affine.smulX`, `Affine.smulY`
- Used by: `dblXYZ_smulField`, `nonsingular_smulField`, `addXYZ_smulField`
- Visibility: public
- Lines: 423-435 (proof ~12 lines)
- Notes: none (just over 10 lines — main hinge is `Affine.zsmul_point_eq_smulX_smulY`).

### lemma Jacobian.dblZ_smulPoly
- Type: `dblZ curvePoly (smulPoly n) = curve.ψ (2 * n)`
- What: The Z-coordinate of the Jacobian doubling formula applied to `(φₙ,ωₙ,ψₙ)` equals `ψ₂ₙ` (computed in the polynomial ring, no quotient needed).
- How: Unfolds `dblZ`, `smulPoly`, `negY`, `curvePoly`, base-change machinery; rewrites `← ψc_spec`, converts via `curve.ω_spec n`, then `norm_num; ring`.
- Hypotheses: `n : ℤ` (implicit).
- Uses from project: `smulPoly`
- Used by: `dblXYZ_smulField`, `addXYZ_smulField`
- Visibility: public
- Lines: 437-443 (proof 6 lines)
- Notes: none

### lemma Jacobian.nonsingular_smulField
- Type: `Nonsingular curveField (smulField n)`
- What: `smulField n` represents a nonsingular Jacobian point of the universal curve.
- How: `← nonsingularLift_iff`, then `simpa` with `zsmul_point_eq_smulField` and the lifted nonsingularity of `(n • point)`.
- Hypotheses: `n : ℤ` (implicit).
- Uses from project: `zsmul_point_eq_smulField`, `smulField`
- Used by: `addXYZ_smulField`
- Visibility: public
- Lines: 445-447 (proof 2 lines)
- Notes: none

### lemma Jacobian.two_zsmul_point_eq_dblXYZ
- Type: `{P : Point …} {v : Fin 3 → Universal.Field} (hv : P.point = ⟦v⟧) : ((2:ℤ) • P).point = ⟦dblXYZ curveField v⟧`
- What: Doubling a Jacobian point whose coordinates are `⟦v⟧` is computed by the doubling formula `dblXYZ`.
- How: `two_zsmul`, `Point.add_point`, `addMap_eq`, `add_self`.
- Hypotheses: `P.point = ⟦v⟧`.
- Uses from project: []
- Used by: `dblXYZ_smulField`
- Visibility: private
- Lines: 449-452 (proof 1 line)
- Notes: none

### lemma Jacobian.add_point_of_ne_eq_addXYZ
- Type: `{P Q : Point …} {v w} (hv : P.point = ⟦v⟧) (hw : Q.point = ⟦w⟧) (hne : P ≠ Q) : (P + Q).point = ⟦addXYZ curveField v w⟧`
- What: Adding two distinct Jacobian points with coordinates `⟦v⟧`, `⟦w⟧` is computed by `addXYZ`.
- How: `Point.add_point`, `addMap_eq`, `add_of_not_equiv`; the non-equivalence is derived from `P ≠ Q` via `Point.ext_iff`/`Quotient.eq`.
- Hypotheses: `P.point = ⟦v⟧`, `Q.point = ⟦w⟧`, `P ≠ Q`.
- Uses from project: []
- Used by: `addXYZ_smulField`
- Visibility: private
- Lines: 454-458 (proof 3 lines)
- Notes: none

### lemma Jacobian.dblXYZ_smulField
- Type: `dblXYZ curveField (smulField n) = smulField (2 * n)`
- What: The Jacobian doubling formula applied to `smulField n` yields `smulField (2n)` — the universal-field doubling identity.
- How: `n=0` case by direct `simp`/`norm_num` unfolding `dblXYZ`/`dblX`/`dblY`/`dblZ`; for `n ≠ 0`, applies `equiv_iff_eq_of_Z_eq` (Z-coords equal via `dblZ_smulPoly`/`map_dblZ`; nonzero via `ψᵤ_ne_zero`) and `Quotient.exact`, then identifies via `two_zsmul_point_eq_dblXYZ`, `mul_zsmul`, and `zsmul_point_eq_smulField`.
- Hypotheses: `n : ℤ` (implicit).
- Uses from project: `smulField`, `smulPoly`, `ψᵤ_ne_zero`, `dblZ_smulPoly`, `two_zsmul_point_eq_dblXYZ`, `zsmul_point_eq_smulField`
- Used by: `dblXYZ_smulRing`
- Visibility: public
- Lines: 460-473 (proof ~13 lines)
- Notes: `set_option maxRecDepth 2048 in`. Hinges on `equiv_iff_eq_of_Z_eq`.

### lemma Jacobian.dblXYZ_smulRing
- Type: `dblXYZ curveRing (smulRing n) = smulRing (2 * n)`
- What: The Jacobian doubling identity, transported to the universal ring.
- How: Uses injectivity `IsFractionRing.injective`'s `comp_left`, `← map_dblXYZ`, then `dblXYZ_smulField`.
- Hypotheses: `n : ℤ` (implicit).
- Uses from project: `dblXYZ_smulField`, `smulRing`
- Used by: (top-level) `dblXYZ_smulEval`
- Visibility: public
- Lines: 475-477 (proof 2 lines)
- Notes: none

### lemma Jacobian.addZ_smulPoly
- Type: `addZ (smulPoly m) (smulPoly n) = curve.ψ (n + m) * curve.ψ (n - m)`
- What: The Z-coordinate of the Jacobian addition formula on `(φₘ,…)` and `(φₙ,…)` equals `ψₙ₊ₘ·ψₙ₋ₘ` (polynomial ring).
- How: Unfolds `addZ`, `smulPoly`, `φ`; converts via the elliptic-sequence relation `curve.isEllSequence_ψ n m 1`, `ψ_one`, then `ring`.
- Hypotheses: `m n : ℤ` (implicit).
- Uses from project: `smulPoly`
- Used by: `addXYZ_smulField`
- Visibility: public
- Lines: 479-482 (proof 3 lines)
- Notes: none

### lemma Jacobian.ω_neg_eq_neg_negY
- Type: `curve.ω (-n) = -negY curvePoly (smulPoly n)`
- What: The negated-index ω polynomial equals minus the Jacobian `negY` of `(φₙ,ωₙ,ψₙ)`.
- How: Unfolds `smulPoly`, `negY`, `curvePoly`, base-change machinery; `ω_neg`, identifies the base-change map with `algebraMap`, then `norm_num; ring`.
- Hypotheses: `n : ℤ` (implicit).
- Uses from project: `smulPoly`
- Used by: `smulPoly_neg`
- Visibility: public
- Lines: 484-489 (proof 5 lines)
- Notes: none

### lemma Jacobian.smulPoly_neg
- Type: `smulPoly (-n) = (-1 : Poly) • neg curvePoly (smulPoly n)`
- What: `smulPoly (−n)` is the Jacobian negation of `smulPoly n`, scaled by `−1` (so it represents `−P`).
- How: `simp` with `ω_neg_eq_neg_negY`, `neg`, `smul_fin3`, `(Odd 3).neg_pow` (odd power flips sign on Z³).
- Hypotheses: `n : ℤ` (implicit).
- Uses from project: `smulPoly`, `ω_neg_eq_neg_negY`
- Used by: `smulRing_neg`, `smulField_neg`
- Visibility: public
- Lines: 491-492 (proof 1 line)
- Notes: none

### lemma Jacobian.smulRing_neg
- Type: `smulRing (-n) = (-1 : Universal.Ring) • neg curveRing (smulRing n)`
- What: The universal-ring analogue: `smulRing (−n)` is `−1` times the Jacobian negation of `smulRing n`.
- How: `simp_rw` with `smulPoly_neg`, `comp_smul`, `← map_neg`, `map_neg`, `map_one`; `rfl`.
- Hypotheses: `n : ℤ` (implicit).
- Uses from project: `smulRing`, `smulPoly_neg`
- Used by: (top-level) `zsmul_eq_smulEval`
- Visibility: public
- Lines: 494-495 (proof 1 line)
- Notes: none

### lemma Jacobian.smulField_neg
- Type: `smulField (-n) = (-1 : Universal.Field) • neg curveField (smulField n)`
- What: The universal-field analogue of `smulPoly_neg`.
- How: `simp_rw` with `smulPoly_neg`, `comp_smul`, `← map_neg`, `map_neg`, `map_one`; `rfl`.
- Hypotheses: `n : ℤ` (implicit).
- Uses from project: `smulField`, `smulPoly_neg`
- Used by: `addXYZ_smulField`
- Visibility: public
- Lines: 497-498 (proof 1 line)
- Notes: none

### lemma Jacobian.smulPoly_zero
- Type: `smulPoly 0 = ![1, 1, 0]`
- What: At `n=0`, `smulPoly` is `(1,1,0)` (the point at infinity's Jacobian coordinates).
- How: `simp [smulPoly]` (φ₀=1, ω₀=1, ψ₀=0).
- Hypotheses: none.
- Uses from project: `smulPoly`
- Used by: `smulField_zero`
- Visibility: public
- Lines: 500 (proof 1 line)
- Notes: none

### lemma Jacobian.smulField_zero
- Type: `smulField 0 = ![1, 1, 0]`
- What: At `n=0`, `smulField` is `(1,1,0)`.
- How: `simp [smulField, smulPoly_zero, comp_fin3]`.
- Hypotheses: none.
- Uses from project: `smulField`, `smulPoly_zero`
- Used by: `addXYZ_smulField`
- Visibility: public
- Lines: 501 (proof 1 line)
- Notes: none

### lemma Jacobian.addXYZ_smulField
- Type: `addXYZ curveField (smulField m) (smulField n) = polyToField (curve.ψ (n - m)) • smulField (n + m)`
- What: The Jacobian addition formula on `smulField m` and `smulField n` yields `ψₙ₋ₘ`-scaled `smulField (n+m)` — the universal-field addition identity (valid even when `m=n` or `n=-m`).
- How: Case `m=n`: `addXYZ_self` gives `(…,0,0)` matching `ψ₀=0` scaling. Case `n=-m`: rewrites via `smulField_neg`, `addXYZ_smul`, `addXYZ_neg`, `dblZ_smulPoly`, `smulField_zero`. Generic case: `equiv_iff_eq_of_Z_eq` (Z via `addZ_smulPoly`/`map_addZ`; nonzero via `ψᵤ_ne_zero`) + `Quotient.exact`, then identifies through `zsmul_point_eq_smulField`, `add_zsmul`, and `add_point_of_ne_eq_addXYZ` (using `zsmul_point_ne`).
- Hypotheses: `m n : ℤ` (implicit).
- Uses from project: `smulField`, `nonsingular_smulField`, `smulField_neg`, `dblZ_smulPoly`, `smulField_zero`, `addZ_smulPoly`, `ψᵤ_ne_zero`, `zsmul_point_eq_smulField`, `add_point_of_ne_eq_addXYZ`, `zsmul_point_ne`
- Used by: `addXYZ_smulRing`, `addXYZ_smulField₁`
- Visibility: public
- Lines: 503-527 (proof ~24 lines)
- Notes: `set_option maxHeartbeats 400000 in`. Hinges on `equiv_iff_eq_of_Z_eq`, `addXYZ_self`, `addXYZ_neg`.

### lemma Jacobian.addXYZ_smulRing
- Type: `addXYZ curveRing (smulRing m) (smulRing n) = AdjoinRoot.mk curve.polynomial (curve.ψ (n - m)) • smulRing (n + m)`
- What: The Jacobian addition identity transported to the universal ring.
- How: `IsFractionRing.injective`'s `comp_left`, `← map_addXYZ`, `comp_smul`, then `addXYZ_smulField`.
- Hypotheses: `m n : ℤ` (implicit).
- Uses from project: `addXYZ_smulField`, `smulRing`
- Used by: `addXYZ_smulRing₁`, (top-level) `addXYZ_smulEval`
- Visibility: public
- Lines: 529-533 (proof 3 lines)
- Notes: none

### lemma Jacobian.addXYZ_smulField₁
- Type: `addXYZ curveField (smulField n) (smulField (n + 1)) = smulField (2 * n + 1)`
- What: The special case of `addXYZ_smulField` for consecutive indices `n` and `n+1`, giving `smulField (2n+1)` (the odd-step of the even-odd induction).
- How: `addXYZ_smulField` with `add_sub_cancel_left`, `ψ_one`, `map_one`, the `1 • _ = _` simplification, then `congr; omega`.
- Hypotheses: `n : ℤ` (implicit).
- Uses from project: `addXYZ_smulField`, `smulField`
- Used by: unused in file (the Ring variant `addXYZ_smulRing₁` is the one used downstream)
- Visibility: public
- Lines: 535-540 (proof 5 lines)
- Notes: none

### lemma Jacobian.addXYZ_smulRing₁
- Type: `addXYZ curveRing (smulRing n) (smulRing (n + 1)) = smulRing (2 * n + 1)`
- What: The universal-ring consecutive-index addition identity, giving `smulRing (2n+1)`.
- How: `addXYZ_smulRing` with `add_sub_cancel_left`, `ψ_one`, `map_one`, the `1 • _ = _` simplification, then `congr; omega`.
- Hypotheses: `n : ℤ` (implicit).
- Uses from project: `addXYZ_smulRing`, `smulRing`
- Used by: (top-level) `addXYZ_smulEval₁`
- Visibility: public
- Lines: 542-547 (proof 5 lines)
- Notes: none

### abbrev smulEval
- Type: `smulEval (n : ℤ) : Fin 3 → R := evalEval x y ∘ ![W.φ n, W.ω n, W.ψ n]`
- What: The evaluation of the (specialized) division polynomials `(φₙ,ωₙ,ψₙ)` at a point `(x,y)`, the candidate Jacobian coordinates of `n • (x,y)`.
- How: definitional (compose `evalEval x y` with the polynomial 3-tuple).
- Hypotheses: `W : WeierstrassCurve R`, `x y : R` (via `variable`), `n : ℤ`.
- Uses from project: []
- Used by: `ringEval_comp_smulRing`, `ringEval_ψ`, `dblXYZ_smulEval`, `addXYZ_smulEval`, `addXYZ_smulEval₁`, `zsmul_eq_smulEval`
- Visibility: public
- Lines: 553-556
- Notes: none

### lemma ringEval_comp_smulRing
- Type: `(n : ℤ) : ringEval eqn ∘ smulRing n = smulEval W x y n`
- What: The universal evaluation map `ringEval eqn` (specializing the universal ring to `(x,y)` on `W`) sends `smulRing n` to `smulEval W x y n`. This is the bridge from universal identities to concrete evaluations.
- How: Rewrites `smulEval` via `map_specialize`, `map_φ/ω/ψ`, and ring-hom composition lemmas (`coe_evalEvalRingHom`, `eval₂RingHom_eval₂RingHom`), then `ringEval_comp_mk` and `polyEval`.
- Hypotheses: `eqn : W.toAffine.Equation x y`.
- Uses from project: `smulRing`, `smulEval`
- Used by: `ringEval_ψ`, `dblXYZ_smulEval`, `addXYZ_smulEval`, `addXYZ_smulEval₁`, `zsmul_eq_smulEval`
- Visibility: public
- Lines: 562-566 (proof 5 lines)
- Notes: none

### lemma ringEval_ψ
- Type: `(n : ℤ) : ringEval eqn (AdjoinRoot.mk _ (curve.ψ n)) = evalEval x y (W.ψ n)`
- What: `ringEval eqn` sends the universal ψₙ (as a ring element) to the specialized ψₙ evaluated at `(x,y)`.
- How: `congr_fun (ringEval_comp_smulRing eqn n) 2` (the third component of the previous lemma).
- Hypotheses: `eqn : W.toAffine.Equation x y`.
- Uses from project: `ringEval_comp_smulRing`
- Used by: `addXYZ_smulEval`
- Visibility: public
- Lines: 568-570 (proof 1 line)
- Notes: none

### lemma dblXYZ_smulEval
- Type: `(n : ℤ) : dblXYZ W (smulEval W x y n) = smulEval W x y (2 * n)`
- What: The concrete Jacobian doubling identity for `smulEval` on `W` at `(x,y)`.
- How: `simp_rw` rewriting `← ringEval_comp_smulRing`, `← dblXYZ_smulRing`, `← map_dblXYZ`, `curveRing_map_ringEval` (transports the universal-ring identity through `ringEval`).
- Hypotheses: `eqn : W.toAffine.Equation x y` (via `include eqn`).
- Uses from project: `ringEval_comp_smulRing`, `dblXYZ_smulRing`, `smulEval`
- Used by: `zsmul_eq_smulEval`
- Visibility: public
- Lines: 572-574 (proof 1 line)
- Notes: `include eqn in` modifier.

### lemma addXYZ_smulEval
- Type: `(m n : ℤ) : addXYZ W (smulEval W x y m) (smulEval W x y n) = evalEval x y (W.ψ (n - m)) • smulEval W x y (n + m)`
- What: The concrete Jacobian addition identity for `smulEval` (with ψₙ₋ₘ scaling).
- How: `simp_rw` rewriting `← ringEval_comp_smulRing`, `← ringEval_ψ`, then `← comp_smul`, `← addXYZ_smulRing`, `← map_addXYZ`, `curveRing_map_ringEval`.
- Hypotheses: `eqn : W.toAffine.Equation x y` (via `include eqn`).
- Uses from project: `ringEval_comp_smulRing`, `ringEval_ψ`, `addXYZ_smulRing`, `smulEval`
- Used by: unused in file
- Visibility: public
- Lines: 576-582 (proof 3 lines)
- Notes: `include eqn in` modifier.

### lemma addXYZ_smulEval₁
- Type: `(n : ℤ) : addXYZ W (smulEval W x y n) (smulEval W x y (n + 1)) = smulEval W x y (2 * n + 1)`
- What: The concrete consecutive-index Jacobian addition identity for `smulEval`.
- How: `simp_rw` rewriting `← ringEval_comp_smulRing`, `← addXYZ_smulRing₁`, `← map_addXYZ`, `curveRing_map_ringEval`.
- Hypotheses: `eqn : W.toAffine.Equation x y` (via `include eqn`).
- Uses from project: `ringEval_comp_smulRing`, `addXYZ_smulRing₁`, `smulEval`
- Used by: `zsmul_eq_smulEval`
- Visibility: public
- Lines: 584-587 (proof 1 line)
- Notes: `include eqn in` modifier.

### theorem zsmul_eq_smulEval
- Type: `{x y : F} (h : Affine.Nonsingular W x y) (n : ℤ) : (n • Point.fromAffine (Affine.Point.some _ _ h)).point = ⟦smulEval W x y n⟧`
- What: The MAIN theorem: for a field `F`, nonsingular affine rational point `(x,y)` on `W`, and any integer `n`, the Jacobian coordinates of `n • (x,y)` are `⟦(φₙ(x,y), ωₙ(x,y), ψₙ(x,y))⟧`.
- How: `Int.negInduction`; `nat` case is strong induction with base cases `n=0` (`⟦1,1,0⟧`) and `n=1`, then even/odd split via `n.even_or_odd'`: even case `2(n+1)` uses doubling (`dblXYZ_smulEval`, `add_self`); odd case uses addition `(n+1)+(n+1+1)` via `addXYZ_smulEval₁`, `add_of_not_equiv` (distinctness from `Point.fromAffine_some_ne_zero`). `neg` case scales by `−1` via `smulRing_neg` and `curveRing_map_ringEval` under `Quotient.sound`.
- Hypotheses: `F` a field, `W : WeierstrassCurve F`, `h : Affine.Nonsingular W x y`, `n : ℤ`.
- Uses from project: `smulEval`, `dblXYZ_smulEval`, `addXYZ_smulEval₁`, `ringEval_comp_smulRing`, `smulRing_neg`
- Used by: unused in file (this is the file's top-level deliverable)
- Visibility: public
- Lines: 593-628 (proof ~33 lines)
- Notes: long(30-50) — proof ~33 lines. Candidate for `/decompose-proof`.

---

## File Summary

- Total declarations documented: 64
  - defs: 3 (`Affine.smulX`, `Affine.smulY`, `Affine.slopeOne`)
  - abbrevs: 5 (`ψᵤ`, `Jacobian.smulPoly`, `Jacobian.smulRing`, `Jacobian.smulField`, `smulEval`)
  - lemmas + theorems: 55 (3 theorems: `Affine.zsmul_point_eq_smulX_smulY`, `Jacobian.zsmul_point_eq_smulField`, `zsmul_eq_smulEval`)
  - instances: 1 (`Affine` AddGroup on the base-changed point group)

- Key API (used by ≥3 in-file declarations):
  - `ψᵤ` — universal ψ in the field; backbone of the whole development (used by ~20 decls)
  - `ψᵤ_ne_zero` — nonvanishing of ψᵤ; cited in ~15 proofs
  - `Affine.smulX`, `Affine.smulY` — the candidate affine coordinates (each used by ~12–16 decls)
  - `Jacobian.smulPoly`, `Jacobian.smulRing`, `Jacobian.smulField` — the 3-tuple families (each used ≥5×)
  - `Affine.smulX_sub_smulX` — central EDS difference identity (used by 4 decls)
  - `Affine.smulY_sub_negY` — doubled-ψ identity (used by 3 decls)
  - `Affine.zsmul_point_eq_smulX_smulY` — universal affine mult formula (used by 3 decls)
  - `Jacobian.zsmul_point_eq_smulField` — universal Jacobian mult formula (used by 3 decls)
  - `Jacobian.dblZ_smulPoly`, `Jacobian.addZ_smulPoly`, `Jacobian.smulField_neg/zero` — Jacobian Z/negation building blocks
  - `Jacobian.addXYZ_smulField` — universal-field addition identity (used by 2; central)
  - `smulEval` — concrete evaluation tuple (used by 6 decls)
  - `ringEval_comp_smulRing` — universal→concrete bridge (used by 5 decls)

- Unused declarations (no in-file consumer; many are public API exported for downstream files):
  `evalEval_ψ`, `evalEval_φ`, `evalEval_ω`, `polyEval_cusp_ω`, `Affine.smulY_zero`, `Affine.smulX_eq_smulX_iff`, `Affine.addX_smul_one_smul_one_aux` (private — genuinely dead), `Jacobian.point_point`, `Jacobian.algebraMap_comp_smulRing`, `Jacobian.addXYZ_smulField₁`, `addXYZ_smulEval`, and the top-level deliverable `zsmul_eq_smulEval` (final export).
  Note: `Affine.addX_smul_one_smul_one_aux` is private and unreferenced — a likely dead-code candidate for cleanup.

- Declarations with `sorry`: none.

- Declarations with `set_option`:
  - `Jacobian.dblXYZ_smulField` — `set_option maxRecDepth 2048 in`
  - `Jacobian.addXYZ_smulField` — `set_option maxHeartbeats 400000 in`

- Proofs > 50 lines (OVER-50): none.

- Proofs 30–50 lines (long(30-50)): 2
  - `Affine.zsmul_point_eq_smulX_smulY` (~38 lines, lines 343-383)
  - `zsmul_eq_smulEval` (~33 lines, lines 593-628)

- Near-threshold note: `Jacobian.addXYZ_smulField` (~24 lines, lines 503-527) and `Jacobian.dblXYZ_smulField` (~13 lines) are the next-largest; both carry `set_option` and are reasonable secondary `/decompose-proof` candidates if the two long(30-50) proofs are split first.

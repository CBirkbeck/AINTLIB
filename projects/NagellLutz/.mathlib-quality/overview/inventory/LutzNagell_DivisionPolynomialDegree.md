# Inventory: LutzNagell/DivisionPolynomialDegree.lean

Path: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean`

All declarations live in `namespace WeierstrassCurve`, with `variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)`. The file computes leading terms (degree bound, leading coefficient, top coefficient, nonvanishing) of the division-polynomial pieces `Ψ₂Sq`, `Ψ₃`, `preΨ₄`, `preΨ'`, `preΨ`, `ΨSq`, `Φ`. The pieces themselves come from the project copy `LutzNagell/DivisionPolynomial.lean`.

---

### lemma natDegree_Ψ₂Sq_le
- Type: `W.Ψ₂Sq.natDegree ≤ 3`
- What: The polynomial `Ψ₂Sq` (square of the 2-division polynomial) has degree at most 3.
- How: Unfolds the definition `Ψ₂Sq` and discharges the bound by the `compute_degree` tactic.
- Hypotheses: none beyond `[CommRing R]`.
- Uses from project: `Ψ₂Sq`
- Used by: `natDegree_Ψ₂Sq`, `coeff_Ψ₂Sq_ne_zero` (indirectly via `natDegree_Ψ₂Sq`), `natDegree_coeff_preΨ'`, `natDegree_coeff_ΨSq_ofNat`, `natDegree_coeff_Φ_ofNat`
- Visibility: public
- Lines: 61-63 (proof 2 lines)
- Notes: none

### lemma coeff_Ψ₂Sq
- Type: `W.Ψ₂Sq.coeff 3 = 4`
- What: The degree-3 coefficient of `Ψ₂Sq` equals 4.
- How: Unfolds `Ψ₂Sq` and computes the coefficient with `compute_degree!`.
- Hypotheses: none.
- Uses from project: `Ψ₂Sq`
- Used by: `coeff_Ψ₂Sq_ne_zero`, `leadingCoeff_Ψ₂Sq`, `natDegree_coeff_preΨ'`, `natDegree_coeff_ΨSq_ofNat`, `natDegree_coeff_Φ_ofNat`
- Visibility: public (`@[simp]`)
- Lines: 65-68 (proof 2 lines)
- Notes: none

### lemma coeff_Ψ₂Sq_ne_zero
- Type: `(h : (4 : R) ≠ 0) : W.Ψ₂Sq.coeff 3 ≠ 0`
- What: If 4 is nonzero in `R`, the degree-3 coefficient of `Ψ₂Sq` is nonzero.
- How: Rewrites the coefficient via `coeff_Ψ₂Sq` to reduce to the hypothesis `(4 : R) ≠ 0`.
- Hypotheses: `4 ≠ 0` in `R`.
- Uses from project: `coeff_Ψ₂Sq`
- Used by: `natDegree_Ψ₂Sq`
- Visibility: public
- Lines: 70-71 (proof 1 line)
- Notes: none

### lemma natDegree_Ψ₂Sq
- Type: `(h : (4 : R) ≠ 0) : W.Ψ₂Sq.natDegree = 3`
- What: When 4 is nonzero, `Ψ₂Sq` has degree exactly 3.
- How: Combines the upper bound `natDegree_Ψ₂Sq_le` with nonvanishing of the leading coefficient `coeff_Ψ₂Sq_ne_zero` via mathlib's `natDegree_eq_of_le_of_coeff_ne_zero`.
- Hypotheses: `4 ≠ 0` in `R`.
- Uses from project: `natDegree_Ψ₂Sq_le`, `coeff_Ψ₂Sq_ne_zero`
- Used by: `natDegree_Ψ₂Sq_pos`, `leadingCoeff_Ψ₂Sq`
- Visibility: public (`@[simp]`)
- Lines: 73-75 (proof 1 line, term-mode)
- Notes: none

### lemma natDegree_Ψ₂Sq_pos
- Type: `(h : (4 : R) ≠ 0) : 0 < W.Ψ₂Sq.natDegree`
- What: When 4 is nonzero, `Ψ₂Sq` has positive degree.
- How: Rewrites the degree to 3 via `natDegree_Ψ₂Sq` and uses `three_pos`.
- Hypotheses: `4 ≠ 0` in `R`.
- Uses from project: `natDegree_Ψ₂Sq`
- Used by: `Ψ₂Sq_ne_zero`
- Visibility: public
- Lines: 77-78 (proof 1 line, term-mode rewrite)
- Notes: none

### lemma leadingCoeff_Ψ₂Sq
- Type: `(h : (4 : R) ≠ 0) : W.Ψ₂Sq.leadingCoeff = 4`
- What: When 4 is nonzero, the leading coefficient of `Ψ₂Sq` is 4.
- How: Unfolds `leadingCoeff`, rewrites the degree with `natDegree_Ψ₂Sq`, then the coefficient with `coeff_Ψ₂Sq`.
- Hypotheses: `4 ≠ 0` in `R`.
- Uses from project: `natDegree_Ψ₂Sq`, `coeff_Ψ₂Sq`
- Used by: unused in file
- Visibility: public (`@[simp]`)
- Lines: 80-82 (proof 1 line)
- Notes: none

### lemma Ψ₂Sq_ne_zero
- Type: `(h : (4 : R) ≠ 0) : W.Ψ₂Sq ≠ 0`
- What: When 4 is nonzero, `Ψ₂Sq` is a nonzero polynomial.
- How: Uses `ne_zero_of_natDegree_gt` applied to the positivity result `natDegree_Ψ₂Sq_pos`.
- Hypotheses: `4 ≠ 0` in `R`.
- Uses from project: `natDegree_Ψ₂Sq_pos`
- Used by: unused in file
- Visibility: public
- Lines: 84-85 (proof 1 line, term-mode)
- Notes: none

### lemma natDegree_Ψ₃_le
- Type: `W.Ψ₃.natDegree ≤ 4`
- What: The 3-division polynomial `Ψ₃` has degree at most 4.
- How: Unfolds `Ψ₃` and discharges via `compute_degree`.
- Hypotheses: none.
- Uses from project: `Ψ₃`
- Used by: `natDegree_Ψ₃`, `natDegree_coeff_preΨ'` (case `three`)
- Visibility: public
- Lines: 91-93 (proof 2 lines)
- Notes: none

### lemma coeff_Ψ₃
- Type: `W.Ψ₃.coeff 4 = 3`
- What: The degree-4 coefficient of `Ψ₃` equals 3.
- How: Unfolds `Ψ₃` and computes via `compute_degree!`.
- Hypotheses: none.
- Uses from project: `Ψ₃`
- Used by: `coeff_Ψ₃_ne_zero`, `leadingCoeff_Ψ₃`, `natDegree_coeff_preΨ'` (case `three`)
- Visibility: public (`@[simp]`)
- Lines: 95-98 (proof 2 lines)
- Notes: none

### lemma coeff_Ψ₃_ne_zero
- Type: `(h : (3 : R) ≠ 0) : W.Ψ₃.coeff 4 ≠ 0`
- What: If 3 is nonzero in `R`, the degree-4 coefficient of `Ψ₃` is nonzero.
- How: Rewrites via `coeff_Ψ₃` to reduce to the hypothesis.
- Hypotheses: `3 ≠ 0` in `R`.
- Uses from project: `coeff_Ψ₃`
- Used by: `natDegree_Ψ₃`
- Visibility: public
- Lines: 100-101 (proof 1 line)
- Notes: none

### lemma natDegree_Ψ₃
- Type: `(h : (3 : R) ≠ 0) : W.Ψ₃.natDegree = 4`
- What: When 3 is nonzero, `Ψ₃` has degree exactly 4.
- How: Combines bound `natDegree_Ψ₃_le` and nonvanishing `coeff_Ψ₃_ne_zero` via `natDegree_eq_of_le_of_coeff_ne_zero`.
- Hypotheses: `3 ≠ 0` in `R`.
- Uses from project: `natDegree_Ψ₃_le`, `coeff_Ψ₃_ne_zero`
- Used by: `natDegree_Ψ₃_pos`, `leadingCoeff_Ψ₃`
- Visibility: public (`@[simp]`)
- Lines: 103-105 (proof 1 line, term-mode)
- Notes: none

### lemma natDegree_Ψ₃_pos
- Type: `(h : (3 : R) ≠ 0) : 0 < W.Ψ₃.natDegree`
- What: When 3 is nonzero, `Ψ₃` has positive degree.
- How: Rewrites the degree to 4 via `natDegree_Ψ₃` and uses `four_pos`.
- Hypotheses: `3 ≠ 0` in `R`.
- Uses from project: `natDegree_Ψ₃`
- Used by: `Ψ₃_ne_zero`
- Visibility: public
- Lines: 107-108 (proof 1 line, term-mode rewrite)
- Notes: none

### lemma leadingCoeff_Ψ₃
- Type: `(h : (3 : R) ≠ 0) : W.Ψ₃.leadingCoeff = 3`
- What: When 3 is nonzero, the leading coefficient of `Ψ₃` is 3.
- How: Unfolds `leadingCoeff`, rewrites degree via `natDegree_Ψ₃` then coefficient via `coeff_Ψ₃`.
- Hypotheses: `3 ≠ 0` in `R`.
- Uses from project: `natDegree_Ψ₃`, `coeff_Ψ₃`
- Used by: unused in file
- Visibility: public (`@[simp]`)
- Lines: 110-112 (proof 1 line)
- Notes: none

### lemma Ψ₃_ne_zero
- Type: `(h : (3 : R) ≠ 0) : W.Ψ₃ ≠ 0`
- What: When 3 is nonzero, `Ψ₃` is a nonzero polynomial.
- How: Uses `ne_zero_of_natDegree_gt` on `natDegree_Ψ₃_pos`.
- Hypotheses: `3 ≠ 0` in `R`.
- Uses from project: `natDegree_Ψ₃_pos`
- Used by: unused in file
- Visibility: public
- Lines: 114-115 (proof 1 line, term-mode)
- Notes: none

### lemma natDegree_preΨ₄_le
- Type: `W.preΨ₄.natDegree ≤ 6`
- What: The pre-4-division polynomial `preΨ₄` has degree at most 6.
- How: Unfolds `preΨ₄` and discharges via `compute_degree`.
- Hypotheses: none.
- Uses from project: `preΨ₄`
- Used by: `natDegree_preΨ₄`, `natDegree_coeff_preΨ'` (case `four`)
- Visibility: public
- Lines: 121-123 (proof 2 lines)
- Notes: none

### lemma coeff_preΨ₄
- Type: `W.preΨ₄.coeff 6 = 2`
- What: The degree-6 coefficient of `preΨ₄` equals 2.
- How: Unfolds `preΨ₄` and computes via `compute_degree!`.
- Hypotheses: none.
- Uses from project: `preΨ₄`
- Used by: `coeff_preΨ₄_ne_zero`, `leadingCoeff_preΨ₄`, `natDegree_coeff_preΨ'` (case `four`)
- Visibility: public (`@[simp]`)
- Lines: 125-128 (proof 2 lines)
- Notes: none

### lemma coeff_preΨ₄_ne_zero
- Type: `(h : (2 : R) ≠ 0) : W.preΨ₄.coeff 6 ≠ 0`
- What: If 2 is nonzero in `R`, the degree-6 coefficient of `preΨ₄` is nonzero.
- How: Rewrites via `coeff_preΨ₄` to reduce to the hypothesis.
- Hypotheses: `2 ≠ 0` in `R`.
- Uses from project: `coeff_preΨ₄`
- Used by: `natDegree_preΨ₄`
- Visibility: public
- Lines: 130-131 (proof 1 line)
- Notes: none

### lemma natDegree_preΨ₄
- Type: `(h : (2 : R) ≠ 0) : W.preΨ₄.natDegree = 6`
- What: When 2 is nonzero, `preΨ₄` has degree exactly 6.
- How: Combines bound `natDegree_preΨ₄_le` and nonvanishing `coeff_preΨ₄_ne_zero` via `natDegree_eq_of_le_of_coeff_ne_zero`.
- Hypotheses: `2 ≠ 0` in `R`.
- Uses from project: `natDegree_preΨ₄_le`, `coeff_preΨ₄_ne_zero`
- Used by: `natDegree_preΨ₄_pos`, `leadingCoeff_preΨ₄`
- Visibility: public (`@[simp]`)
- Lines: 133-135 (proof 1 line, term-mode)
- Notes: none

### lemma natDegree_preΨ₄_pos
- Type: `(h : (2 : R) ≠ 0) : 0 < W.preΨ₄.natDegree`
- What: When 2 is nonzero, `preΨ₄` has positive degree.
- How: `linarith` from the degree value supplied by `natDegree_preΨ₄`.
- Hypotheses: `2 ≠ 0` in `R`.
- Uses from project: `natDegree_preΨ₄`
- Used by: `preΨ₄_ne_zero`
- Visibility: public
- Lines: 137-138 (proof 1 line)
- Notes: none

### lemma leadingCoeff_preΨ₄
- Type: `(h : (2 : R) ≠ 0) : W.preΨ₄.leadingCoeff = 2`
- What: When 2 is nonzero, the leading coefficient of `preΨ₄` is 2.
- How: Unfolds `leadingCoeff`, rewrites degree via `natDegree_preΨ₄` then coefficient via `coeff_preΨ₄`.
- Hypotheses: `2 ≠ 0` in `R`.
- Uses from project: `natDegree_preΨ₄`, `coeff_preΨ₄`
- Used by: unused in file
- Visibility: public (`@[simp]`)
- Lines: 140-142 (proof 1 line)
- Notes: none

### lemma preΨ₄_ne_zero
- Type: `(h : (2 : R) ≠ 0) : W.preΨ₄ ≠ 0`
- What: When 2 is nonzero, `preΨ₄` is a nonzero polynomial.
- How: Uses `ne_zero_of_natDegree_gt` on `natDegree_preΨ₄_pos`.
- Hypotheses: `2 ≠ 0` in `R`.
- Uses from project: `natDegree_preΨ₄_pos`
- Used by: unused in file
- Visibility: public
- Lines: 144-145 (proof 1 line, term-mode)
- Notes: none

### def expDegree
- Type: `expDegree (n : ℕ) : ℕ := (n ^ 2 - if Even n then 4 else 1) / 2`
- What: The expected degree of `preΨ'ₙ`: `(n²−4)/2` for even `n`, `(n²−1)/2` for odd `n`.
- How: Direct natural-number arithmetic definition.
- Hypotheses: none.
- Uses from project: []
- Used by: `expDegree_cast`, `expDegree_rec`, `natDegree_coeff_preΨ'`, `coeff_preΨ'`, `natDegree_coeff_ΨSq_ofNat`, `natDegree_coeff_Φ_ofNat`
- Visibility: private
- Lines: 151-152 (def, no proof)
- Notes: none

### lemma expDegree_cast
- Type: `{n : ℕ} (hn : n ≠ 0) : 2 * (expDegree n : ℤ) = n ^ 2 - if Even n then 4 else 1`
- What: Over `ℤ`, `2 * expDegree n` equals `n² − 4` (even) or `n² − 1` (odd), removing the truncated `Nat` subtraction/division.
- How: Case split on even/odd via `n.even_or_odd'`; in each branch rewrites the square as `2 * (...) + (4 or 1)` so that `Nat.add_sub_cancel` and `Nat.mul_div_cancel_left` make the division exact, then closes with `ring1`. Hinges on `Nat.mul_div_cancel_left` and `Nat.add_sub_cancel`.
- Hypotheses: `n ≠ 0`.
- Uses from project: `expDegree`
- Used by: `expDegree_rec`, `natDegree_coeff_ΨSq_ofNat`, `natDegree_coeff_Φ_ofNat`
- Visibility: private
- Lines: 154-164 (proof 10 lines)
- Notes: none

### lemma expDegree_rec
- Type: see source (4-way conjunction of recursion identities for `expDegree (2*(m+3))` and `expDegree (2*(m+2)+1)`)
- What: The four additivity/recurrence identities the expected degree must satisfy along the EDS recursion (the even-index and odd-index degree splits, two forms each).
- How: Casts everything to `ℤ` and cancels the factor 2 (via `mul_left_cancel_iff_of_pos`), repeatedly rewrites with `expDegree_cast` to clear truncated arithmetic, normalises parity with `Nat.even_add_one`/`even_two_mul`/`ite_not`, then `split_ifs <;> ring1`. Hinges on `expDegree_cast` and `mul_left_cancel_iff_of_pos`.
- Hypotheses: none beyond `m : ℕ`.
- Uses from project: `expDegree`, `expDegree_cast`
- Used by: `natDegree_coeff_preΨ'`
- Visibility: private
- Lines: 166-177 (proof ~5 lines)
- Notes: uses `lia` tactic (in `by lia`); none otherwise

### def expCoeff
- Type: `expCoeff (n : ℕ) : ℤ := if Even n then n / 2 else n`
- What: The expected leading coefficient of `preΨ'ₙ`: `n/2` for even `n`, `n` for odd `n` (as an integer).
- How: Direct integer definition.
- Hypotheses: none.
- Uses from project: []
- Used by: `expCoeff_cast`, `expCoeff_rec`, `natDegree_coeff_preΨ'`, `coeff_preΨ'`, `natDegree_coeff_ΨSq_ofNat`, `natDegree_coeff_Φ_ofNat`
- Visibility: private
- Lines: 179-180 (def, no proof)
- Notes: none

### lemma expCoeff_cast
- Type: `(n : ℕ) : (expCoeff n : ℚ) = if Even n then (n / 2 : ℚ) else n`
- What: Casts `expCoeff n` to `ℚ`, where the even-case division `n/2` is genuine rational division.
- How: Case split via `n.even_or_odd'`, then `simp` with `expCoeff` and `n.not_even_two_mul_add_one`.
- Hypotheses: none.
- Uses from project: `expCoeff`
- Used by: `expCoeff_rec`, `natDegree_coeff_ΨSq_ofNat`, `natDegree_coeff_Φ_ofNat`
- Visibility: private
- Lines: 182-183 (proof 1 line)
- Notes: none

### lemma expCoeff_rec
- Type: see source (conjunction of even-index and odd-index leading-coefficient recurrences for `expCoeff`)
- What: The two leading-coefficient recurrence identities (even and odd index) that `expCoeff` satisfies along the EDS recursion, including the `Ψ₂Sq`-coefficient factors `4²`.
- How: Casts to `ℚ` via `Int.cast_inj`, rewrites coefficients with `expCoeff_cast`, normalises parity (`even_two_mul`, `not_even_two_mul_add_one`, `Nat.even_add_one`, `ite_not`), then `split_ifs <;> ring1`. Hinges on `expCoeff_cast`.
- Hypotheses: none beyond `m : ℕ`.
- Uses from project: `expCoeff`, `expCoeff_cast`
- Used by: `natDegree_coeff_preΨ'`
- Visibility: private
- Lines: 185-194 (proof ~3 lines)
- Notes: none

### lemma natDegree_coeff_preΨ'
- Type: `(n : ℕ) : (W.preΨ' n).natDegree ≤ expDegree n ∧ (W.preΨ' n).coeff (expDegree n) = expCoeff n`
- What: Simultaneously, `preΨ'ₙ` has degree bounded by `expDegree n` and its `expDegree n`-th coefficient equals `expCoeff n`; this is the core strong-induction result of the file.
- How: Strong induction via the EDS recursor `normEDSRec`, handling base cases `zero/one/two/three/four` (using `preΨ'_zero/one/two/three/four`, `natDegree_Ψ₃_le`, `coeff_Ψ₃`, `natDegree_preΨ₄_le`, `coeff_preΨ₄`) and the `even`/`odd` recursion steps. The even/odd steps unfold `preΨ'_even`/`preΨ'_odd`, bound degrees with the local abbreviations `dm`/`dp` (built from `natDegree_mul_le_of_le`, `natDegree_pow_le_of_le`) and extract top coefficients with `cm`/`cp` (from `coeff_mul_add_eq_of_natDegree_le`, `coeff_pow_of_natDegree_le`), then transport the degree splits via `expDegree_rec` and the coefficient recurrences via `expCoeff_rec`, closing with `norm_cast`. Hinges on `normEDSRec`, `expDegree_rec`, `expCoeff_rec`, `coeff_mul_add_eq_of_natDegree_le`, `natDegree_sub_le_of_le`.
- Hypotheses: none beyond `[CommRing R]`.
- Uses from project: `expDegree`, `expCoeff`, `expDegree_rec`, `expCoeff_rec`, `preΨ'` (via constructors), `preΨ'_zero`, `preΨ'_one`, `preΨ'_two`, `preΨ'_three`, `preΨ'_four`, `preΨ'_even`, `preΨ'_odd`, `natDegree_Ψ₃_le`, `coeff_Ψ₃`, `natDegree_preΨ₄_le`, `coeff_preΨ₄`, `natDegree_Ψ₂Sq_le`, `coeff_Ψ₂Sq`
- Used by: `natDegree_preΨ'_le`, `coeff_preΨ'`, `natDegree_coeff_ΨSq_ofNat`, `natDegree_coeff_Φ_ofNat`
- Visibility: private
- Lines: 196-227 (proof 31 lines)
- Notes: long(30-50); central engine of the file — candidate for /decompose-proof

### lemma natDegree_preΨ'_le
- Type: `(n : ℕ) : (W.preΨ' n).natDegree ≤ (n ^ 2 - if Even n then 4 else 1) / 2`
- What: Degree bound for `preΨ'ₙ` (natural argument), stated with the explicit formula rather than `expDegree`.
- How: Projects the left conjunct of `natDegree_coeff_preΨ'`.
- Hypotheses: none.
- Uses from project: `natDegree_coeff_preΨ'`
- Used by: `coeff_preΨ'_ne_zero` (indirectly), `natDegree_preΨ'`, `natDegree_preΨ_le`
- Visibility: public
- Lines: 229-230 (proof 1 line, term-mode)
- Notes: none

### lemma coeff_preΨ'
- Type: `(n : ℕ) : (W.preΨ' n).coeff ((n ^ 2 - if Even n then 4 else 1) / 2) = if Even n then n / 2 else n`
- What: The top coefficient of `preΨ'ₙ` (at the expected degree) equals `n/2` (even) or `n` (odd).
- How: Converts to the right conjunct of `natDegree_coeff_preΨ'`, then in each parity branch (`n.even_or_odd'`) `simp`s the `expDegree`/`expCoeff` formulas using `n.not_even_two_mul_add_one`.
- Hypotheses: none.
- Uses from project: `natDegree_coeff_preΨ'`, `expDegree`, `expCoeff`
- Used by: `coeff_preΨ'_ne_zero`, `leadingCoeff_preΨ'`, `coeff_preΨ`
- Visibility: public (`@[simp]`)
- Lines: 232-237 (proof ~3 lines)
- Notes: none

### lemma coeff_preΨ'_ne_zero
- Type: `{n : ℕ} (h : (n : R) ≠ 0) : (W.preΨ' n).coeff ((n ^ 2 - if Even n then 4 else 1) / 2) ≠ 0`
- What: If `n ≠ 0` in `R`, the top coefficient of `preΨ'ₙ` is nonzero.
- How: Case split on even/odd via `n.even_or_odd'`; rewrites the coefficient with `coeff_preΨ'`, in the even case simplifies `n/2` via `Nat.mul_div_cancel_left` and uses `right_ne_zero_of_mul` against `(n : R) ≠ 0`, in the odd case reduces directly to `h`.
- Hypotheses: `n ≠ 0` in `R`.
- Uses from project: `coeff_preΨ'`
- Used by: `natDegree_preΨ'`, `coeff_preΨ_ne_zero` (via the `nat` branch path)
- Visibility: public
- Lines: 239-244 (proof ~5 lines)
- Notes: none

### lemma natDegree_preΨ'
- Type: `{n : ℕ} (h : (n : R) ≠ 0) : (W.preΨ' n).natDegree = (n ^ 2 - if Even n then 4 else 1) / 2`
- What: When `n ≠ 0` in `R`, the degree of `preΨ'ₙ` equals the expected formula.
- How: Combines bound `natDegree_preΨ'_le` and nonvanishing `coeff_preΨ'_ne_zero` via `natDegree_eq_of_le_of_coeff_ne_zero`.
- Hypotheses: `n ≠ 0` in `R`.
- Uses from project: `natDegree_preΨ'_le`, `coeff_preΨ'_ne_zero`
- Used by: `natDegree_preΨ'_pos`, `leadingCoeff_preΨ'`, `natDegree_preΨ_pos` (via the `nat` branch)
- Visibility: public (`@[simp]`)
- Lines: 246-249 (proof 1 line, term-mode)
- Notes: none

### lemma natDegree_preΨ'_pos
- Type: `{n : ℕ} (hn : 2 < n) (h : (n : R) ≠ 0) : 0 < (W.preΨ' n).natDegree`
- What: For `n > 2` and `n ≠ 0` in `R`, `preΨ'ₙ` has positive degree.
- How: Rewrites the degree via `natDegree_preΨ'` and reduces to `Nat.div_pos_iff`; after `split_ifs` bounds `n² − {4,1} ≥ 2` using `Nat.pow_le_pow_left hn 2` and `Nat.sub_le_sub_right` with `Nat.AtLeastTwo.prop`.
- Hypotheses: `2 < n`; `n ≠ 0` in `R`.
- Uses from project: `natDegree_preΨ'`
- Used by: `preΨ'_ne_zero`, `natDegree_preΨ_pos` (via the `nat` branch)
- Visibility: public
- Lines: 251-253 (proof ~3 lines)
- Notes: none

### lemma leadingCoeff_preΨ'
- Type: `{n : ℕ} (h : (n : R) ≠ 0) : (W.preΨ' n).leadingCoeff = if Even n then n / 2 else n`
- What: When `n ≠ 0` in `R`, the leading coefficient of `preΨ'ₙ` is `n/2` (even) or `n` (odd).
- How: Unfolds `leadingCoeff`, rewrites degree via `natDegree_preΨ'` then coefficient via `coeff_preΨ'`.
- Hypotheses: `n ≠ 0` in `R`.
- Uses from project: `natDegree_preΨ'`, `coeff_preΨ'`
- Used by: unused in file
- Visibility: public (`@[simp]`)
- Lines: 255-258 (proof 1 line)
- Notes: none

### lemma preΨ'_ne_zero
- Type: `[Nontrivial R] {n : ℕ} (h : (n : R) ≠ 0) : W.preΨ' n ≠ 0`
- What: Over a nontrivial ring, if `n ≠ 0` in `R` then `preΨ'ₙ` is a nonzero polynomial.
- How: Splits on `2 < n`: for large `n` uses `ne_zero_of_natDegree_gt` with `natDegree_preΨ'_pos`; for small `n` (`n = 0,1,2`) finishes by `aesop` on the explicit values.
- Hypotheses: `[Nontrivial R]`; `n ≠ 0` in `R`.
- Uses from project: `natDegree_preΨ'_pos`
- Used by: `preΨ_ne_zero` (via the `nat` branch)
- Visibility: public
- Lines: 260-263 (proof ~3 lines)
- Notes: none

### lemma natDegree_preΨ_le
- Type: `(n : ℤ) : (W.preΨ n).natDegree ≤ (n.natAbs ^ 2 - if Even n then 4 else 1) / 2`
- What: Degree bound for `preΨₙ` with integer argument `n`, using `|n|`.
- How: Integer sign induction `Int.negInduction`: the `nat` case casts to `natDegree_preΨ'_le` via `preΨ_ofNat`; the `neg` case rewrites `preΨ_neg`, `natDegree_neg`, `Int.natAbs_neg`, `even_neg` and reuses the inductive hypothesis.
- Hypotheses: none.
- Uses from project: `natDegree_preΨ'_le`, `preΨ` (via `preΨ_ofNat`, `preΨ_neg`)
- Used by: `natDegree_preΨ`
- Visibility: public
- Lines: 269-273 (proof ~4 lines)
- Notes: none

### lemma coeff_preΨ
- Type: `(n : ℤ) : (W.preΨ n).coeff ((n.natAbs ^ 2 - if Even n then 4 else 1) / 2) = if Even n then n / 2 else n`
- What: The top coefficient of `preΨₙ` (integer argument) equals `n/2` (even) or `n` (odd).
- How: `Int.negInduction`: `nat` case casts to `coeff_preΨ'` via `preΨ_ofNat`; `neg` case rewrites `preΨ_neg`, `coeff_neg`, then case-splits parity (`n.even_or_odd'`) and uses `Int.neg_ediv_of_dvd` to push the negation through the integer division before rewriting with the hypothesis.
- Hypotheses: none.
- Uses from project: `coeff_preΨ'`, `preΨ` (via `preΨ_ofNat`, `preΨ_neg`)
- Used by: `coeff_preΨ_ne_zero` (indirectly), `natDegree_preΨ`, `leadingCoeff_preΨ`
- Visibility: public (`@[simp]`)
- Lines: 275-284 (proof ~6 lines)
- Notes: none

### lemma coeff_preΨ_ne_zero
- Type: `{n : ℤ} (h : (n : R) ≠ 0) : (W.preΨ n).coeff ((n.natAbs ^ 2 - if Even n then 4 else 1) / 2) ≠ 0`
- What: If `n ≠ 0` in `R`, the top coefficient of `preΨₙ` (integer argument) is nonzero.
- How: `Int.negInduction`: `nat` case reduces to `coeff_preΨ'_ne_zero` (via `preΨ_ofNat`, `Int.even_coe_nat`, `Int.natAbs_natCast`); `neg` case rewrites `preΨ_neg`/`coeff_neg`/`neg_ne_zero` and applies the IH after `neg_ne_zero.mp`.
- Hypotheses: `n ≠ 0` in `R`.
- Uses from project: `coeff_preΨ'_ne_zero`, `preΨ` (via `preΨ_ofNat`, `preΨ_neg`)
- Used by: `natDegree_preΨ`
- Visibility: public
- Lines: 286-292 (proof ~6 lines)
- Notes: none

### lemma natDegree_preΨ
- Type: `{n : ℤ} (h : (n : R) ≠ 0) : (W.preΨ n).natDegree = (n.natAbs ^ 2 - if Even n then 4 else 1) / 2`
- What: When `n ≠ 0` in `R`, the degree of `preΨₙ` (integer argument) equals the expected formula. (Listed as a Main statement.)
- How: Combines bound `natDegree_preΨ_le` and nonvanishing `coeff_preΨ_ne_zero` via `natDegree_eq_of_le_of_coeff_ne_zero`.
- Hypotheses: `n ≠ 0` in `R`.
- Uses from project: `natDegree_preΨ_le`, `coeff_preΨ_ne_zero`
- Used by: `leadingCoeff_preΨ`
- Visibility: public (`@[simp]`)
- Lines: 294-297 (proof 1 line, term-mode)
- Notes: none

### lemma natDegree_preΨ_pos
- Type: `{n : ℤ} (hn : 2 < n.natAbs) (h : (n : R) ≠ 0) : 0 < (W.preΨ n).natDegree`
- What: For `|n| > 2` and `n ≠ 0` in `R`, `preΨₙ` (integer argument) has positive degree.
- How: `Int.negInduction`: `nat` case reduces to `natDegree_preΨ'_pos`; `neg` case rewrites `preΨ_neg`/`natDegree_neg` and applies the IH after adjusting `natAbs` and `neg_ne_zero`.
- Hypotheses: `|n| > 2`; `n ≠ 0` in `R`.
- Uses from project: `natDegree_preΨ'_pos`, `preΨ` (via `preΨ_ofNat`, `preΨ_neg`)
- Used by: unused in file
- Visibility: public
- Lines: 299-305 (proof ~5 lines)
- Notes: none

### lemma leadingCoeff_preΨ
- Type: `{n : ℤ} (h : (n : R) ≠ 0) : (W.preΨ n).leadingCoeff = if Even n then n / 2 else n`
- What: When `n ≠ 0` in `R`, the leading coefficient of `preΨₙ` (integer argument) is `n/2` (even) or `n` (odd). (Listed as a Main statement.)
- How: Unfolds `leadingCoeff`, rewrites degree via `natDegree_preΨ` then coefficient via `coeff_preΨ`.
- Hypotheses: `n ≠ 0` in `R`.
- Uses from project: `natDegree_preΨ`, `coeff_preΨ`
- Used by: unused in file
- Visibility: public (`@[simp]`)
- Lines: 307-310 (proof 1 line)
- Notes: none

### lemma preΨ_ne_zero
- Type: `[Nontrivial R] {n : ℤ} (h : (n : R) ≠ 0) : W.preΨ n ≠ 0`
- What: Over a nontrivial ring, if `n ≠ 0` in `R` then `preΨₙ` (integer argument) is a nonzero polynomial.
- How: `Int.negInduction`: `nat` case reduces to `preΨ'_ne_zero` via `preΨ_ofNat`; `neg` case rewrites `preΨ_neg`/`neg_ne_zero` and applies the IH after `neg_ne_zero.mp`.
- Hypotheses: `[Nontrivial R]`; `n ≠ 0` in `R`.
- Uses from project: `preΨ'_ne_zero`, `preΨ` (via `preΨ_ofNat`, `preΨ_neg`)
- Used by: unused in file
- Visibility: public
- Lines: 312-316 (proof ~4 lines)
- Notes: none

### lemma natDegree_coeff_ΨSq_ofNat
- Type: `(n : ℕ) : (W.ΨSq n).natDegree ≤ n ^ 2 - 1 ∧ (W.ΨSq n).coeff (n ^ 2 - 1) = (n ^ 2 : ℤ)`
- What: Simultaneously, `ΨSqₙ` (natural argument) has degree bounded by `n² − 1` and its `(n²−1)`-th coefficient equals `n²`.
- How: After the `n = 0` base case, derives two arithmetic identities `hd` (degree split `n²−1 = 2·expDegree(n+1) + {3,0}`) and `hc` (coefficient `n² = expCoeff(n+1)² · {4,1}`) by casting and `split_ifs <;> ring1`, then unfolds `ΨSq_ofNat`, bounds degree with `natDegree_pow_le_of_le` and `natDegree_Ψ₂Sq_le`, and computes the top coefficient via `coeff_mul_add_eq_of_natDegree_le`, `coeff_pow_of_natDegree_le`, `natDegree_coeff_preΨ'`, `coeff_Ψ₂Sq`. Hinges on `natDegree_coeff_preΨ'`, `expDegree_cast`, `expCoeff_cast`, `coeff_mul_add_eq_of_natDegree_le`.
- Hypotheses: none beyond `[CommRing R]`.
- Uses from project: `ΨSq` (via `ΨSq_ofNat`), `expDegree`, `expCoeff`, `expDegree_cast`, `expCoeff_cast`, `natDegree_coeff_preΨ'`, `natDegree_Ψ₂Sq_le`, `coeff_Ψ₂Sq`
- Used by: `natDegree_ΨSq_le`, `coeff_ΨSq`
- Visibility: private
- Lines: 322-341 (proof 19 lines)
- Notes: none

### lemma natDegree_ΨSq_le
- Type: `(n : ℤ) : (W.ΨSq n).natDegree ≤ n.natAbs ^ 2 - 1`
- What: Degree bound for `ΨSqₙ` (integer argument), using `|n|`. (Listed as a Main statement.)
- How: `Int.negInduction`: `nat` case projects `natDegree_coeff_ΨSq_ofNat`; `neg` case rewrites `ΨSq_neg`, `Int.natAbs_neg` and reuses the IH.
- Hypotheses: none.
- Uses from project: `natDegree_coeff_ΨSq_ofNat`, `ΨSq` (via `ΨSq_neg`)
- Used by: `natDegree_ΨSq`
- Visibility: public
- Lines: 343-346 (proof ~3 lines)
- Notes: none

### lemma coeff_ΨSq
- Type: `(n : ℤ) : (W.ΨSq n).coeff (n.natAbs ^ 2 - 1) = n ^ 2`
- What: The top coefficient of `ΨSqₙ` (integer argument) at degree `|n|²−1` equals `n²`. (Listed as a Main statement.)
- How: `Int.negInduction`: `nat` case casts `natDegree_coeff_ΨSq_ofNat`; `neg` case rewrites `ΨSq_neg`, `Int.natAbs_neg`, and uses `neg_sq` (via `Int.cast_pow`) to absorb the sign before applying the IH.
- Hypotheses: none.
- Uses from project: `natDegree_coeff_ΨSq_ofNat`, `ΨSq` (via `ΨSq_neg`)
- Used by: `coeff_ΨSq_ne_zero` (indirectly via `simpa`), `natDegree_ΨSq`, `leadingCoeff_ΨSq`
- Visibility: public (`@[simp]`)
- Lines: 348-352 (proof ~3 lines)
- Notes: none

### lemma coeff_ΨSq_ne_zero
- Type: `[NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) : (W.ΨSq n).coeff (n.natAbs ^ 2 - 1) ≠ 0`
- What: Over a ring with no zero divisors, if `n ≠ 0` in `R` then the top coefficient `n²` of `ΨSqₙ` is nonzero.
- How: `simpa` — discharges using the `@[simp]` lemma `coeff_ΨSq` together with `h` (no zero divisors forces `n² ≠ 0`).
- Hypotheses: `[NoZeroDivisors R]`; `n ≠ 0` in `R`.
- Uses from project: `coeff_ΨSq` (via simp set)
- Used by: `natDegree_ΨSq`
- Visibility: public
- Lines: 354-356 (proof 1 line)
- Notes: none

### lemma natDegree_ΨSq
- Type: `[NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) : (W.ΨSq n).natDegree = n.natAbs ^ 2 - 1`
- What: Over a ring with no zero divisors, when `n ≠ 0` in `R` the degree of `ΨSqₙ` equals `|n|²−1`. (Listed as a Main statement.)
- How: Combines bound `natDegree_ΨSq_le` and nonvanishing `coeff_ΨSq_ne_zero` via `natDegree_eq_of_le_of_coeff_ne_zero`.
- Hypotheses: `[NoZeroDivisors R]`; `n ≠ 0` in `R`.
- Uses from project: `natDegree_ΨSq_le`, `coeff_ΨSq_ne_zero`
- Used by: `natDegree_ΨSq_pos`, `leadingCoeff_ΨSq`
- Visibility: public (`@[simp]`)
- Lines: 358-361 (proof 1 line, term-mode)
- Notes: none

### lemma natDegree_ΨSq_pos
- Type: `[NoZeroDivisors R] {n : ℤ} (hn : 1 < n.natAbs) (h : (n : R) ≠ 0) : 0 < (W.ΨSq n).natDegree`
- What: Over a ring with no zero divisors, for `|n| > 1` and `n ≠ 0` in `R`, `ΨSqₙ` has positive degree.
- How: `simpa [W.natDegree_ΨSq h]` — rewrites the degree to `|n|²−1` and closes the positivity arithmetic from `1 < |n|`.
- Hypotheses: `[NoZeroDivisors R]`; `|n| > 1`; `n ≠ 0` in `R`.
- Uses from project: `natDegree_ΨSq`
- Used by: `ΨSq_ne_zero`
- Visibility: public
- Lines: 363-365 (proof 1 line)
- Notes: none

### lemma leadingCoeff_ΨSq
- Type: `[NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) : (W.ΨSq n).leadingCoeff = n ^ 2`
- What: Over a ring with no zero divisors, when `n ≠ 0` in `R` the leading coefficient of `ΨSqₙ` is `n²`. (Listed as a Main statement.)
- How: Unfolds `leadingCoeff`, rewrites degree via `natDegree_ΨSq` then coefficient via `coeff_ΨSq`.
- Hypotheses: `[NoZeroDivisors R]`; `n ≠ 0` in `R`.
- Uses from project: `natDegree_ΨSq`, `coeff_ΨSq`
- Used by: unused in file
- Visibility: public (`@[simp]`)
- Lines: 367-370 (proof 1 line)
- Notes: none

### lemma ΨSq_ne_zero
- Type: `[NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) : W.ΨSq n ≠ 0`
- What: Over a ring with no zero divisors, if `n ≠ 0` in `R` then `ΨSqₙ` is a nonzero polynomial.
- How: Splits on `1 < |n|`: for large `|n|` uses `ne_zero_of_natDegree_gt` with `natDegree_ΨSq_pos`; for `|n| ∈ {0,1}` handles `0` by contradiction with `h` and `±1` via `ΨSq_one`/`ΨSq_neg`, finishing with `C_injective` on the constant polynomial. Hinges on `natDegree_ΨSq_pos`, `Int.natAbs_eq_iff`, `C_injective`.
- Hypotheses: `[NoZeroDivisors R]`; `n ≠ 0` in `R`.
- Uses from project: `natDegree_ΨSq_pos`, `ΨSq` (via `ΨSq_neg`, `ΨSq_one`)
- Used by: unused in file
- Visibility: public
- Lines: 372-380 (proof ~8 lines)
- Notes: none

### lemma natDegree_coeff_Φ_ofNat
- Type: `(n : ℕ) : (W.Φ n).natDegree ≤ n ^ 2 ∧ (W.Φ n).coeff (n ^ 2) = 1`
- What: Simultaneously, `Φₙ` (natural argument) has degree bounded by `n²` and its `n²`-th coefficient equals 1.
- How: After base cases `n = 0,1` (`simp [natDegree_X_le]`), derives three arithmetic identities `hd`, `hd'` (two forms of the degree split for `n²` in terms of `expDegree`) and `hc` (the coefficient `1` as a difference of `expCoeff` products with `Ψ₂Sq` factors) by casting and `split_ifs <;> ring1`, then unfolds `Φ_ofNat`, bounds the degree of the difference with `natDegree_sub_le_of_le` using the local `dm`/`dp` abbreviations (`natDegree_mul_le_of_le`, `natDegree_pow_le_of_le`), and extracts the top coefficient via `coeff_sub`, `cm` (`coeff_mul_add_eq_of_natDegree_le`), `coeff_pow_of_natDegree_le`, `coeff_X_one`, `natDegree_coeff_preΨ'`, `coeff_Ψ₂Sq`, closing with `norm_cast`. Hinges on `natDegree_coeff_preΨ'`, `expDegree_cast`, `expCoeff_cast`, `natDegree_sub_le_of_le`, `coeff_mul_add_eq_of_natDegree_le`.
- Hypotheses: none beyond `[CommRing R]`.
- Uses from project: `Φ` (via `Φ_ofNat`), `expDegree`, `expCoeff`, `expDegree_cast`, `expCoeff_cast`, `natDegree_coeff_preΨ'`, `natDegree_Ψ₂Sq_le`, `coeff_Ψ₂Sq`
- Used by: `natDegree_Φ_le`, `coeff_Φ`
- Visibility: private
- Lines: 386-416 (proof 30 lines)
- Notes: long(30-50); candidate for /decompose-proof

### lemma natDegree_Φ_le
- Type: `(n : ℤ) : (W.Φ n).natDegree ≤ n.natAbs ^ 2`
- What: Degree bound for `Φₙ` (integer argument), using `|n|`. (Listed as a Main statement.)
- How: `Int.negInduction`: `nat` case projects `natDegree_coeff_Φ_ofNat`; `neg` case rewrites `Φ_neg`, `Int.natAbs_neg` and reuses the IH.
- Hypotheses: none.
- Uses from project: `natDegree_coeff_Φ_ofNat`, `Φ` (via `Φ_neg`)
- Used by: `natDegree_Φ`
- Visibility: public
- Lines: 418-421 (proof ~3 lines)
- Notes: none

### lemma coeff_Φ
- Type: `(n : ℤ) : (W.Φ n).coeff (n.natAbs ^ 2) = 1`
- What: The top coefficient of `Φₙ` (integer argument) at degree `|n|²` equals 1. (Listed as a Main statement.)
- How: `Int.negInduction`: `nat` case projects `natDegree_coeff_Φ_ofNat`; `neg` case rewrites `Φ_neg`, `Int.natAbs_neg` and reuses the IH.
- Hypotheses: none.
- Uses from project: `natDegree_coeff_Φ_ofNat`, `Φ` (via `Φ_neg`)
- Used by: `coeff_Φ_ne_zero`, `natDegree_Φ`, `leadingCoeff_Φ`
- Visibility: public (`@[simp]`)
- Lines: 423-427 (proof ~3 lines)
- Notes: none

### lemma coeff_Φ_ne_zero
- Type: `[Nontrivial R] (n : ℤ) : (W.Φ n).coeff (n.natAbs ^ 2) ≠ 0`
- What: Over a nontrivial ring, the top coefficient `1` of `Φₙ` is nonzero.
- How: Rewrites the coefficient to `1` via `coeff_Φ` and uses `one_ne_zero`.
- Hypotheses: `[Nontrivial R]`.
- Uses from project: `coeff_Φ`
- Used by: `natDegree_Φ`
- Visibility: public
- Lines: 429-430 (proof 1 line, term-mode)
- Notes: none

### lemma natDegree_Φ
- Type: `[Nontrivial R] (n : ℤ) : (W.Φ n).natDegree = n.natAbs ^ 2`
- What: Over a nontrivial ring, the degree of `Φₙ` (integer argument) equals `|n|²`. (Listed as a Main statement.)
- How: Combines bound `natDegree_Φ_le` and nonvanishing `coeff_Φ_ne_zero` via `natDegree_eq_of_le_of_coeff_ne_zero`.
- Hypotheses: `[Nontrivial R]`.
- Uses from project: `natDegree_Φ_le`, `coeff_Φ_ne_zero`
- Used by: `natDegree_Φ_pos`, `leadingCoeff_Φ`
- Visibility: public (`@[simp]`)
- Lines: 432-434 (proof 1 line, term-mode)
- Notes: none

### lemma natDegree_Φ_pos
- Type: `[Nontrivial R] {n : ℤ} (hn : n ≠ 0) : 0 < (W.Φ n).natDegree`
- What: Over a nontrivial ring, for `n ≠ 0`, `Φₙ` has positive degree.
- How: `simpa [sq_pos_iff]` — rewrites the degree to `|n|²` (via the `@[simp]` `natDegree_Φ`) and closes positivity from `n ≠ 0`.
- Hypotheses: `[Nontrivial R]`; `n ≠ 0`.
- Uses from project: `natDegree_Φ` (via simp set)
- Used by: `Φ_ne_zero`
- Visibility: public
- Lines: 436-437 (proof 1 line)
- Notes: none

### lemma leadingCoeff_Φ
- Type: `[Nontrivial R] (n : ℤ) : (W.Φ n).leadingCoeff = 1`
- What: Over a nontrivial ring, the leading coefficient of `Φₙ` (integer argument) is 1, i.e. `Φₙ` is monic. (Listed as a Main statement.)
- How: Unfolds `leadingCoeff`, rewrites degree via `natDegree_Φ` then coefficient via `coeff_Φ`.
- Hypotheses: `[Nontrivial R]`.
- Uses from project: `natDegree_Φ`, `coeff_Φ`
- Used by: unused in file
- Visibility: public (`@[simp]`)
- Lines: 439-441 (proof 1 line)
- Notes: none

### lemma Φ_ne_zero
- Type: `[Nontrivial R] (n : ℤ) : W.Φ n ≠ 0`
- What: Over a nontrivial ring, `Φₙ` is always a nonzero polynomial (for any integer `n`).
- How: Splits on `n = 0`: the zero case rewrites `Φ_zero` to `1` and uses `one_ne_zero`; otherwise uses `ne_zero_of_natDegree_gt` with `natDegree_Φ_pos`.
- Hypotheses: `[Nontrivial R]`.
- Uses from project: `natDegree_Φ_pos`, `Φ` (via `Φ_zero`)
- Used by: unused in file
- Visibility: public
- Lines: 443-446 (proof ~3 lines)
- Notes: none

---

## File Summary

- **Total declarations: 46** — 2 defs (`expDegree`, `expCoeff`) / 44 lemmas+theorems / 0 instances. (No structures, classes, abbrevs, or inductives.)
- **Key API (used by ≥3 in-file):**
  - `natDegree_coeff_preΨ'` (used by 4: `natDegree_preΨ'_le`, `coeff_preΨ'`, `natDegree_coeff_ΨSq_ofNat`, `natDegree_coeff_Φ_ofNat`) — the central strong-induction engine.
  - `expDegree` (used by 6), `expCoeff` (used by 6) — the private "expected degree / coefficient" definitions threaded through every recursion.
  - `natDegree_Ψ₂Sq_le` (used by ~5), `coeff_Ψ₂Sq` (used by ~5) — base building blocks for the odd-index / ΨSq / Φ recursions.
  - `coeff_Ψ₃`, `coeff_preΨ₄`, `coeff_preΨ'`, `natDegree_preΨ'_le` are each used by 3.
- **Unused decls (in-file leaf API; exported for downstream use):** `leadingCoeff_Ψ₂Sq`, `Ψ₂Sq_ne_zero`, `leadingCoeff_Ψ₃`, `Ψ₃_ne_zero`, `leadingCoeff_preΨ₄`, `preΨ₄_ne_zero`, `leadingCoeff_preΨ'`, `leadingCoeff_preΨ`, `natDegree_preΨ_pos`, `preΨ_ne_zero`, `leadingCoeff_ΨSq`, `ΨSq_ne_zero`, `leadingCoeff_Φ`, `Φ_ne_zero`. (All `leadingCoeff_*`, all `*_ne_zero` final results, and `natDegree_preΨ_pos` are terminal API consumed outside this file.)
- **Decls with `sorry`: none.**
- **Decls with `set_option`: none.**
- **Proofs >50 lines (OVER-50): none (0).**
- **Proofs 30-50 lines: 2** — `natDegree_coeff_preΨ'` (31 lines, 196-227) and `natDegree_coeff_Φ_ofNat` (30 lines, 386-416). Both are candidates for `/decompose-proof`. (`natDegree_coeff_ΨSq_ofNat` at 19 lines is the next largest, below the threshold.)

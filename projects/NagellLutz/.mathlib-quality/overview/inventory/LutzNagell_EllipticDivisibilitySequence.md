# Inventory: LutzNagell/EllipticDivisibilitySequence.lean

File defines elliptic divisibility sequences (EDS), the auxiliary/normalised sequences (`preNormEDS`, `normEDS`), their complement (division-witness) sequences, and proves `normEDS` is an EDS via a four-index relation `rel₄` machinery (Stange nets) reduced to single-index odd/even recurrences.

---

### def EllSequence.addMulSub
- Type: `(W : ℤ → R) (m n : ℤ) : R := W ((m + n).tdiv 2) * W ((m - n).tdiv 2)`
- What: The basic building block `W((m+n)/2) * W((m-n)/2)` of elliptic relations, for `m,n` of the same parity; uses `Int.tdiv` so sign-flips behave unconditionally.
- How: Plain definition (no proof).
- Hypotheses: none.
- Uses from project: []
- Used by: rel₄, net_eq_rel₄, addMulSub_two_zero, addMulSub_three_one, addMulSub_even, addMulSub_odd, addMulSub_same, addMulSub_neg₀, addMulSub_neg₁, addMulSub_abs₀, addMulSub_abs₁, addMulSub_swap, addMulSub₄_mul_addMulSub₄, addMulSub_transf, addMulSub_mem_nonZeroDivisors, rel₆, map_addMulSub
- Visibility: public
- Lines: 92-98 (def body 1 line)
- Notes: none

### def EllSequence.rel₄
- Type: `(W) (a b c d : ℤ) : R := addMulSub W a b * addMulSub W c d - addMulSub W a c * addMulSub W b d + addMulSub W a d * addMulSub W b c`
- What: The four-index elliptic relation as a signed sum over the three pairings of four same-parity indices.
- How: Plain definition in terms of `addMulSub`.
- Hypotheses: none.
- Uses from project: [addMulSub]
- Used by: net_eq_rel₄, rel₄_eq_net, rel₄_transf, rel₃_iff₄, rel₆, rel₃_iff_oddRec(indirect), rel₄_iff_evenRec, rel₆_eq₃, rel₆_eq₃', rel₆_eq₁₀, addMulSub_sq_mul_rel₄_eq₉, Rel₄OfValid, rel₄_abs, rel₄_swap₀₁/₁₂/₂₃, relFin4, rel₄_same₀₁/₁₂/₂₃, map_rel₄
- Visibility: public
- Lines: 100-105 (def body 2 lines)
- Notes: none

### def EllSequence.net
- Type: `(W) (p q r s : ℤ) : R := W (p+q+s)*W (p-q)*W (r+s)*W r - W (p+r+s)*W (p-r)*W (q+s)*W q + W (q+r+s)*W (q-r)*W (p+s)*W p`
- What: Stange's elliptic-net defining expression, sign/order-adjusted so equivalence with `rel₄` is unconditional and char-3-safe.
- How: Plain definition.
- Hypotheses: none.
- Uses from project: []
- Used by: net_eq_rel₄, invar_of_net, net_add_sub_iff, rel₄_eq_net, IsEllSequence.net, map_net, net_normEDS
- Visibility: public
- Lines: 107-118 (def body 3 lines)
- Notes: none

### lemma EllSequence.net_eq_rel₄
- Type: `{p q r s : ℤ} : net W p q r s = rel₄ W (2*p+s) (2*q+s) (2*r+s) s`
- What: Expresses a `net` as a `rel₄` whose indices are `2·(each)+s`.
- How: `simp_rw` unfolding both sides with `add_add_add_comm`, `Int.mul_tdiv_cancel_left`, then `ring`.
- Hypotheses: none.
- Uses from project: [net, rel₄, addMulSub]
- Used by: rel₄_eq_net
- Visibility: public
- Lines: 120-126 (proof 5 lines)
- Notes: none

### def EllSequence.Rel₃
- Type: `(W) (m n r : ℤ) : Prop := W (m+n)*W (m-n)*W r^2 = W (m+r)*W (m-r)*W n^2 - W (n+r)*W (n-r)*W m^2`
- What: The three-index elliptic relation (specialisation `d=0` of the four-index relation).
- How: Plain definition.
- Hypotheses: none.
- Uses from project: []
- Used by: IsEllSequence, invarNum(conceptually), rel₃_iff₄, rel₃_iff_oddRec, rel₃_iff_evenRec, isEllSequence_id, IsEllSequence.smul, IsEllSequence.map
- Visibility: public
- Lines: 128-132 (def body 2 lines)
- Notes: none

### def IsEllSequence
- Type: `(W : ℤ → R) : Prop := ∀ m n r : ℤ, Rel₃ W m n r` (root namespace)
- What: A sequence is elliptic iff it satisfies `Rel₃` for all index triples.
- How: Plain definition.
- Hypotheses: none.
- Uses from project: [Rel₃]
- Used by: IsEllDivSequence, isEllSequence_id, IsEllSequence.smul/map/of_oddRec_evenRec/normEDS/ext/eq_normEDS_of_dvd, and the whole `IsEllSequence` namespace
- Visibility: public
- Lines: 134-136 (def body 1 line)
- Notes: none

### def EllSequence.invarNum
- Type: `(s n : ℤ) : R := (W (n+2*s)*W (n-s)^2 + W (n+s)^2*W (n-2*s))*W s^2 + W n^3*W (2*s)^2`
- What: Numerator of an invariant of an elliptic sequence (the ratio `invarNum/invarDenom` is `n`-independent).
- How: Plain definition.
- Hypotheses: none.
- Uses from project: []
- Used by: invar_of_net, IsEllSequence.invar, invarNum_normEDS, invarNum_normEDS_two, invar_normEDS, invar₂_normEDS, invarNum_eq_redInvarNum_mul, map_invarNum
- Visibility: public
- Lines: 138-142 (def body 2 lines)
- Notes: none

### def EllSequence.invarDenom
- Type: `(s n : ℤ) : R := W (n+s)*W n*W (n-s)`
- What: Denominator of the invariant of an elliptic sequence.
- How: Plain definition.
- Hypotheses: none.
- Uses from project: []
- Used by: invar_of_net, IsEllSequence.invar, invarDenom_normEDS_two, invar_normEDS, invar₂_normEDS, invarDenom_eq_redInvarDenom_mul, map_invarDenom
- Visibility: public
- Lines: 144-145 (def body 1 line)
- Notes: none

### theorem EllSequence.invar_of_net
- Type: `(net_eq_zero : ∀ p q r s, net W p q r s = 0) (s m n : ℤ) : invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m`
- What: If all `net` values vanish, the invariant numerator/denominator cross-products agree (invariance of `invarNum/invarDenom` across `m,n`).
- How: `simp_rw` invarNum/invarDenom then a `linear_combination` over six specific `net_eq_zero` instances with explicit `W`-factor coefficients, normalised by `simp_rw [net]; ring_nf`.
- Hypotheses: all `net` values are zero.
- Uses from project: [net, invarNum, invarDenom]
- Used by: IsEllSequence.invar, invar_normEDS
- Visibility: public
- Lines: 147-156 (proof 6 lines; plus local set_option/attribute prelude)
- Notes: `set_option allowUnsafeReducibility true` + `attribute [local reducible] Nat.rawCast Mathlib.Meta.NormNum.instAddMonoidWithOne`.

### lemma EllSequence.net_add_sub_iff
- Type: `(m n : ℤ) : net W (m+n) m (m-n) n = 0 ↔ W (2*(m+n))*W (m-n)*W m*W n = (W (2*m+n)*W (2*n)*W m - W (m+2*n)*W (2*m)*W n)*W (m+n)`
- What: Rewrites the vanishing of a specific `net` instance as the standard EDS addition formula.
- How: `simp_rw [net, ...]` rewriting index arithmetic via `show ... from by ring`, then `constructor <;> intro h <;> linear_combination h`.
- Hypotheses: none.
- Uses from project: [net]
- Used by: unused in file
- Visibility: public
- Lines: 158-168 (proof 10 lines)
- Notes: none

### lemma EllSequence.addMulSub_two_zero
- Type: `addMulSub W 2 0 = W 1 ^ 2`
- What: Value of `addMulSub` at `(2,0)` is `W 1` squared.
- How: `(sq _).symm`.
- Hypotheses: none.
- Uses from project: [addMulSub]
- Used by: unused in file
- Visibility: public
- Lines: 170 (proof <1 line)
- Notes: none

### lemma EllSequence.addMulSub_three_one
- Type: `addMulSub W 3 1 = W 2 * W 1`
- What: Value of `addMulSub` at `(3,1)` is `W 2 * W 1`.
- How: `rfl`.
- Hypotheses: none.
- Uses from project: [addMulSub]
- Used by: unused in file
- Visibility: public
- Lines: 171 (proof <1 line)
- Notes: none

### lemma EllSequence.addMulSub_even
- Type: `(m n : ℤ) : addMulSub W (2*m) (2*n) = W (m+n) * W (m-n)`
- What: `addMulSub` on two even indices collapses to `W(m+n)·W(m-n)`.
- How: `simp_rw` with `Int.mul_tdiv_cancel_left`.
- Hypotheses: none.
- Uses from project: [addMulSub]
- Used by: rel₃_iff₄
- Visibility: public
- Lines: 173-174 (proof 1 line)
- Notes: none

### lemma EllSequence.addMulSub_odd
- Type: `(m n : ℤ) : addMulSub W (2*m+1) (2*n+1) = W (m+n+1) * W (m-n)`
- What: `addMulSub` on two odd indices collapses to `W(m+n+1)·W(m-n)`.
- How: introduce `Int.mul_tdiv_cancel_left`, rewrite, then `congr <;> ring`.
- Hypotheses: none.
- Uses from project: [addMulSub]
- Used by: rel₄_iff_evenRec
- Visibility: public
- Lines: 176-179 (proof 2 lines)
- Notes: none

### lemma EllSequence.addMulSub_same
- Type: `(zero : W 0 = 0) (m : ℤ) : addMulSub W m m = 0`
- What: `addMulSub W m m = 0` when `W 0 = 0`.
- How: `sub_self`, `Int.zero_tdiv`, hypothesis, `mul_zero`.
- Hypotheses: `W 0 = 0`.
- Uses from project: [addMulSub]
- Used by: rel₄_same₀₁, rel₄_same₁₂, rel₄_same₂₃
- Visibility: public
- Lines: 181-182 (proof 1 line)
- Notes: none

### lemma EllSequence.addMulSub_neg₀
- Type: `(neg : ∀ k, W (-k) = -W k) (m n : ℤ) : addMulSub W (-m) n = addMulSub W m n`
- What: Negating the first index leaves `addMulSub` unchanged when `W` is odd.
- How: `simp_rw` with `Int.neg_tdiv`, `neg`, then `ring`.
- Hypotheses: `W` is an odd function.
- Uses from project: [addMulSub]
- Used by: addMulSub_abs₀
- Visibility: public
- Lines: 184-186 (proof 1 line)
- Notes: none

### lemma EllSequence.addMulSub_neg₁
- Type: `(m n : ℤ) : addMulSub W m (-n) = addMulSub W m n`
- What: Negating the second index leaves `addMulSub` unchanged (unconditionally).
- How: `rw [addMulSub, addMulSub, mul_comm]; abel_nf`.
- Hypotheses: none.
- Uses from project: [addMulSub]
- Used by: addMulSub_abs₁
- Visibility: public
- Lines: 188-189 (proof 1 line)
- Notes: none

### lemma EllSequence.addMulSub_abs₀
- Type: `(neg : ∀ k, W (-k) = -W k) (m n : ℤ) : addMulSub W |m| n = addMulSub W m n`
- What: Taking absolute value of the first index leaves `addMulSub` unchanged (odd `W`).
- How: `abs_choice m`, then `addMulSub_neg₀`.
- Hypotheses: `W` odd.
- Uses from project: [addMulSub, addMulSub_neg₀]
- Used by: rel₄_abs
- Visibility: public
- Lines: 191-193 (proof 1 line)
- Notes: none

### lemma EllSequence.addMulSub_abs₁
- Type: `(m n : ℤ) : addMulSub W m |n| = addMulSub W m n`
- What: Taking absolute value of the second index leaves `addMulSub` unchanged (unconditionally).
- How: `abs_choice n`, then `addMulSub_neg₁`.
- Hypotheses: none.
- Uses from project: [addMulSub, addMulSub_neg₁]
- Used by: rel₄_abs, addMulSub_transf
- Visibility: public
- Lines: 195-196 (proof 1 line)
- Notes: none

### lemma EllSequence.addMulSub_swap
- Type: `(neg : ∀ k, W (-k) = -W k) (m n : ℤ) : addMulSub W m n = - addMulSub W n m`
- What: Swapping the two indices of `addMulSub` negates it (odd `W`).
- How: `rw` with `neg_sub`, `Int.neg_tdiv`, `neg`, then `ring`.
- Hypotheses: `W` odd.
- Uses from project: [addMulSub]
- Used by: rel₄_swap₀₁, rel₄_swap₁₂, rel₄_swap₂₃
- Visibility: public
- Lines: 198-200 (proof 1 line)
- Notes: none

### def EllSequence.StrictAnti₄
- Type: `(a b c d : ℤ) : Prop := 0 ≤ d ∧ d < c ∧ c < b ∧ b < a`
- What: The four indices are nonnegative and strictly decreasing.
- How: Plain definition.
- Hypotheses: none.
- Uses from project: []
- Used by: Rel₄OfValid, six_le_of_strictAnti₄, strictAnti₄_transf, rel₄_of_anti_oddRec_evenRec
- Visibility: public
- Lines: 206-207 (def body 1 line)
- Notes: none

### def EllSequence.HaveSameParity₄
- Type: `(a b c d : ℤ) : Prop := a.negOnePow = b.negOnePow ∧ b.negOnePow = c.negOnePow ∧ c.negOnePow = d.negOnePow`
- What: The four indices share the same parity (equal `negOnePow`).
- How: Plain definition.
- Hypotheses: none.
- Uses from project: []
- Used by: Rel₄OfValid, rel₄_eq_net, even_sum, same₀₃, .abs, .perm, six_le_of_strictAnti₄, addMulSub_transf, rel₄_transf, transf, strictAnti₄_transf, rel₄_fix₁_of_fix₂, rel₄_of_fix₂, rel₄_of_min₂, IsEllSequence.rel₄/net, rel₄_of_oddRec_evenRec, rel₄_normEDS
- Visibility: public
- Lines: 209-211 (def body 2 lines)
- Notes: none

### def EllSequence.avg₄
- Type: `(a b c d : ℤ) : ℤ := (a + b + c + d) / 2`
- What: Half the sum of the four indices (integer division).
- How: Plain definition.
- Hypotheses: none.
- Uses from project: []
- Used by: avg₄_add_avg₄, addMulSub_transf, rel₄_transf, transf, strictAnti₄_transf, rel₄_of_anti_oddRec_evenRec
- Visibility: public
- Lines: 213-214 (def body 1 line)
- Notes: none

### lemma EllSequence.HaveSameParity₄.rel₄_eq_net
- Type: `(same) : rel₄ W a b c d = net W ((a-d)/2) ((b-d)/2) ((c-d)/2) d`
- What: A same-parity `rel₄` equals a `net` with halved index differences.
- How: `net_eq_rel₄` plus `Int.two_mul_ediv_two_of_even` (three times) discharged via `negOnePow_eq_iff` and the `same` conjuncts.
- Hypotheses: indices same parity.
- Uses from project: [rel₄, net, net_eq_rel₄, HaveSameParity₄]
- Used by: rel₄_normEDS
- Visibility: public
- Lines: 222-226 (proof 4 lines)
- Notes: none

### lemma EllSequence.HaveSameParity₄.even_sum
- Type: `(same) : Even (a + b + c + d)`
- What: The sum of four same-parity integers is even.
- How: `simp_rw` with `negOnePow_add`, `units_mul_self` using the `same` equalities.
- Hypotheses: indices same parity.
- Uses from project: [HaveSameParity₄]
- Used by: avg₄_add_avg₄
- Visibility: public
- Lines: 228-230 (proof 2 lines)
- Notes: none

### lemma EllSequence.HaveSameParity₄.avg₄_add_avg₄
- Type: `(same) : avg₄ a b c d + avg₄ a b c d = a + b + c + d`
- What: Doubling `avg₄` recovers the index sum (valid since the sum is even).
- How: `← two_mul`, `Int.mul_ediv_cancel'` of `same.even_sum.two_dvd`.
- Hypotheses: indices same parity.
- Uses from project: [avg₄, HaveSameParity₄, even_sum]
- Used by: addMulSub_transf, strictAnti₄_transf
- Visibility: public
- Lines: 232-233 (proof 1 line)
- Notes: none

### lemma EllSequence.HaveSameParity₄.same₀₃
- Type: `(same) : a.negOnePow = d.negOnePow`
- What: First and last indices share parity (transitivity of the conjuncts).
- How: `rw` chaining `same.1`, `same.2.1`, `same.2.2`.
- Hypotheses: indices same parity.
- Uses from project: [HaveSameParity₄]
- Used by: rel₄_of_min₂
- Visibility: public
- Lines: 235 (proof <1 line)
- Notes: none

### lemma EllSequence.HaveSameParity₄.abs (protected)
- Type: `(same) : HaveSameParity₄ |a| |b| |c| |d|`
- What: Same-parity is preserved under taking absolute values.
- How: `simpa [negOnePow_abs]`.
- Hypotheses: indices same parity.
- Uses from project: [HaveSameParity₄]
- Used by: rel₄_of_oddRec_evenRec
- Visibility: public (protected)
- Lines: 237-238 (proof 1 line)
- Notes: none

### lemma EllSequence.HaveSameParity₄.perm
- Type: `(same) (σ : Perm (Fin 4)) : ∀ t : Fin 4 → ℤ, HaveSameParity₄ (t 0)..(t 3) → HaveSameParity₄ (t (σ 0))..(t (σ 3))`
- What: Same-parity of a 4-tuple is invariant under any permutation of its entries.
- How: reduce `σ` to generators via `Perm.mclosure_swap_castSucc_succ` and `Submonoid.closure_induction`, handle adjacent transpositions by `fin_cases`.
- Hypotheses: indices same parity (and `σ` arbitrary).
- Uses from project: [HaveSameParity₄]
- Used by: rel₄_of_oddRec_evenRec
- Visibility: public
- Lines: 240-250 (proof 10 lines)
- Notes: none

### lemma EllSequence.HaveSameParity₄.six_le_of_strictAnti₄
- Type: `(same) (anti : StrictAnti₄ a b c d) : 6 ≤ a`
- What: A strictly decreasing nonnegative same-parity 4-tuple forces `a ≥ 6` (gaps of ≥2 each).
- How: `negOnePow_eq_iff` + `add_two_le_iff_lt_of_even_sub` on each strict inequality, then `linarith`.
- Hypotheses: same parity and strictly decreasing nonnegative.
- Uses from project: [HaveSameParity₄, StrictAnti₄]
- Used by: rel₄_of_anti_oddRec_evenRec
- Visibility: public
- Lines: 252-257 (proof 5 lines)
- Notes: none

### def EllSequence.HaveSameParity₄.addMulSub₄
- Type: `(W) (a b c d : ℤ) : R := W ((a+b).tdiv 2) * W ((c-d).tdiv 2)`
- What: A hybrid product mixing one factor from each of two `addMulSub`s.
- How: Plain definition.
- Hypotheses: none.
- Uses from project: []
- Used by: addMulSub₄_mul_addMulSub₄, addMulSub_transf, rel₄_transf
- Visibility: public
- Lines: 259-261 (def body 1 line)
- Notes: none

### lemma EllSequence.HaveSameParity₄.addMulSub₄_mul_addMulSub₄
- Type: `: addMulSub₄ W a b c d * addMulSub₄ W c d a b = addMulSub W a b * addMulSub W c d`
- What: Product of a paired `addMulSub₄` and its mirror recovers the product of two `addMulSub`s.
- How: `simp_rw [addMulSub₄, addMulSub]; ring`.
- Hypotheses: none (`omit same`).
- Uses from project: [addMulSub₄, addMulSub]
- Used by: rel₄_transf
- Visibility: public
- Lines: 263-266 (proof 1 line)
- Notes: none

### lemma EllSequence.HaveSameParity₄.addMulSub_transf
- Type: 6-way conjunction equating `addMulSub W (avg₄ − x) (...)` to various `addMulSub₄`s
- What: Under same parity, the six `addMulSub`s built from `avg₄`-shifted indices coincide with the six `addMulSub₄` hybrids — the algebraic core of the transformation symmetry.
- How: `simp_rw` with `addMulSub_abs₁`, `sub_add_sub_comm`, `same.avg₄_add_avg₄`, then `refine ⟨...⟩ <;> ring_nf`.
- Hypotheses: indices same parity.
- Uses from project: [addMulSub, addMulSub₄, avg₄, HaveSameParity₄, addMulSub_abs₁, avg₄_add_avg₄]
- Used by: rel₄_transf
- Visibility: public
- Lines: 268-278 (proof 2 lines; plus set_option/attribute prelude)
- Notes: `set_option allowUnsafeReducibility true` + `attribute [local reducible] Nat.rawCast Mathlib.Meta.NormNum.instAddMonoidWithOne`.

### theorem EllSequence.HaveSameParity₄.rel₄_transf
- Type: `: rel₄ W (avg₄−d) (avg₄−c) (avg₄−b) |avg₄−a| = rel₄ W a b c d`
- What: `rel₄` is invariant under the `avg₄`-reflection transformation of its indices (same parity).
- How: destructure `addMulSub_transf`, `simp_rw` the six equalities and `addMulSub₄_mul_addMulSub₄`, `ring`.
- Hypotheses: indices same parity.
- Uses from project: [rel₄, avg₄, addMulSub_transf, addMulSub₄_mul_addMulSub₄, HaveSameParity₄]
- Used by: rel₄_of_anti_oddRec_evenRec
- Visibility: public
- Lines: 280-284 (proof 2 lines)
- Notes: none

### theorem EllSequence.HaveSameParity₄.transf
- Type: `: HaveSameParity₄ (avg₄−d) (avg₄−c) (avg₄−b) |avg₄−a|`
- What: The transformed indices remain same-parity.
- How: `simp_rw` with `negOnePow_abs`, `negOnePow_sub`, the `same` conjuncts.
- Hypotheses: indices same parity.
- Uses from project: [HaveSameParity₄, avg₄]
- Used by: rel₄_of_anti_oddRec_evenRec
- Visibility: public
- Lines: 286-288 (proof 1 line)
- Notes: none

### theorem EllSequence.HaveSameParity₄.strictAnti₄_transf
- Type: `(anti : StrictAnti₄ a b c d) : StrictAnti₄ (avg₄−d) (avg₄−c) (avg₄−b) |avg₄−a|`
- What: The transformed indices remain strictly-decreasing nonnegative.
- How: destructure `anti`, `abs_nonneg`/`abs_lt`, `← sub_pos`, then `linarith` using `avg₄_add_avg₄`.
- Hypotheses: same parity and strictly decreasing nonnegative.
- Uses from project: [StrictAnti₄, avg₄, HaveSameParity₄, avg₄_add_avg₄]
- Used by: rel₄_of_anti_oddRec_evenRec
- Visibility: public
- Lines: 290-295 (proof 5 lines)
- Notes: none

### abbrev EllSequence.rel₆
- Type: `(k l a b c d : ℤ) : R := addMulSub W k l * rel₄ W a b c d`
- What: A `rel₄` multiplied by an `addMulSub` "coefficient".
- How: Plain abbreviation.
- Hypotheses: none.
- Uses from project: [addMulSub, rel₄]
- Used by: rel₆_eq, rel₆_eq₃, rel₆_eq₃', rel₆_eq₁₀, addMulSub_sq_mul_rel₄_eq₉, rel₄_fix₁_of_fix₂, rel₄_of_fix₂
- Visibility: public
- Lines: 301-302 (abbrev body 1 line)
- Notes: none

### lemma EllSequence.rel₆_eq (@[simp])
- Type: `(k l a b c d : ℤ) : rel₆ W k l a b c d = addMulSub W k l * rel₄ W a b c d`
- What: Definitional unfolding of `rel₆` as a simp lemma.
- How: `rfl`.
- Hypotheses: none.
- Uses from project: [rel₆, addMulSub, rel₄]
- Used by: rel₄_fix₁_of_fix₂, rel₄_of_fix₂
- Visibility: public
- Lines: 304-305 (proof <1 line)
- Notes: none

### lemma EllSequence.rel₃_iff₄
- Type: `(m n r : ℤ) : Rel₃ W m n r ↔ rel₄ W (2*m) (2*n) (2*r) 0 = 0`
- What: The three-index relation is exactly the four-index relation at doubled indices with last index 0.
- How: unfold both, `simp_rw [addMulSub_even, ...]`, `convert sub_eq_zero.symm; ring`.
- Hypotheses: none.
- Uses from project: [Rel₃, rel₄, addMulSub_even]
- Used by: rel₄_of_anti_oddRec_evenRec, IsEllSequence.of_oddRec_evenRec
- Visibility: public
- Lines: 307-311 (proof 4 lines)
- Notes: none

### lemma EllSequence.rel₆_eq₃
- Type: `(c d m n r : ℤ) : rel₆ W c d m n r c = rel₆ W m c n r c d - rel₆ W n c m r c d + rel₆ W r c m n c d`
- What: Expands a `rel₆` with fixed last index `c` into three `rel₆`s sharing the larger fixed index.
- How: `simp_rw [rel₆, rel₄]; ring`.
- Hypotheses: none.
- Uses from project: [rel₆, rel₄]
- Used by: rel₄_fix₁_of_fix₂
- Visibility: public
- Lines: 320-322 (proof 1 line)
- Notes: none

### lemma EllSequence.rel₆_eq₃'
- Type: `(c d m n r : ℤ) : rel₆ W c d m n r d = rel₆ W m d n r c d - rel₆ W n d m r c d + rel₆ W r d m n c d`
- What: Same expansion as `rel₆_eq₃` but with fixed last index `d` (smaller fixed index).
- How: `simp_rw [rel₆, rel₄]; ring`.
- Hypotheses: none.
- Uses from project: [rel₆, rel₄]
- Used by: rel₄_fix₁_of_fix₂
- Visibility: public
- Lines: 324-330 (proof 1 line)
- Notes: none

### theorem EllSequence.rel₆_eq₁₀
- Type: `(c d m n r s : ℤ) : rel₆ W c d m n r s = (9 rel₆ terms) - 2 * rel₆ W m d n r s c`
- What: Expands a fully-free `rel₆` into a signed sum of ten `rel₆`s each touching a fixed index.
- How: `simp_rw [rel₆, rel₄]; ring`.
- Hypotheses: none.
- Uses from project: [rel₆, rel₄]
- Used by: rel₄_of_fix₂
- Visibility: public
- Lines: 336-342 (proof 1 line)
- Notes: none

### theorem EllSequence.addMulSub_sq_mul_rel₄_eq₉
- Type: `(c d m n r s : ℤ) : (addMulSub W c d)^2 * rel₄ W m n r s = (3 grouped addMulSub·(rel₆ sum) terms)`
- What: Expresses `(addMulSub c d)² · rel₄` as a combination of nine `rel₆`s grouped by three `addMulSub` coefficients.
- How: `simp_rw [rel₆, rel₄]; ring`.
- Hypotheses: none.
- Uses from project: [addMulSub, rel₄, rel₆]
- Used by: unused in file
- Visibility: public
- Lines: 344-351 (proof 1 line)
- Notes: none

### def EllSequence.OddRec
- Type: `(m : ℤ) : Prop := W (2*m+1)*W 1^3 = W (m+2)*W m^3 - W (m-1)*W (m+1)^3`
- What: The recurrence defining odd terms of an elliptic sequence.
- How: Plain definition.
- Hypotheses: none.
- Uses from project: []
- Used by: rel₃_iff_oddRec, rel₄_of_anti_oddRec_evenRec, rel₄_of_oddRec_evenRec, IsEllSequence.oddRec
- Visibility: public
- Lines: 353-356 (def body 2 lines)
- Notes: none

### def EllSequence.EvenRec
- Type: `(m : ℤ) : Prop := W (2*m)*W 2*W 1^2 = W m*(W (m-1)^2*W (m+2) - W (m-2)*W (m+1)^2)`
- What: The recurrence defining even terms of an elliptic sequence.
- How: Plain definition.
- Hypotheses: none.
- Uses from project: []
- Used by: rel₃_iff_evenRec, rel₄_iff_evenRec, rel₄_of_anti_oddRec_evenRec, rel₄_of_oddRec_evenRec, IsEllSequence.evenRec
- Visibility: public
- Lines: 358-361 (def body 2 lines)
- Notes: none

### lemma EllSequence.rel₃_iff_oddRec
- Type: `(m : ℤ) : Rel₃ W (m+1) m 1 ↔ OddRec W m`
- What: The odd recurrence is the three-index relation specialised to `(m+1, m, 1)`.
- How: `rw [Rel₃, OddRec]; ring`.
- Hypotheses: none.
- Uses from project: [Rel₃, OddRec]
- Used by: rel₄_of_anti_oddRec_evenRec, IsEllSequence.oddRec
- Visibility: public
- Lines: 363-364 (proof 1 line)
- Notes: none

### lemma EllSequence.rel₃_iff_evenRec
- Type: `(m : ℤ) : Rel₃ W (m+1) (m-1) 1 ↔ EvenRec W m`
- What: The even recurrence is the three-index relation specialised to `(m+1, m-1, 1)`.
- How: `rw [Rel₃, EvenRec]; ring_nf`.
- Hypotheses: none.
- Uses from project: [Rel₃, EvenRec]
- Used by: IsEllSequence.evenRec
- Visibility: public
- Lines: 366-369 (proof 1 line; plus set_option/attribute prelude)
- Notes: `set_option allowUnsafeReducibility true` + `attribute [local reducible] Nat.rawCast Mathlib.Meta.NormNum.instAddMonoidWithOne`.

### lemma EllSequence.rel₄_iff_evenRec
- Type: `(m : ℤ) : rel₄ W (2*m+1) (2*m-1) 3 1 = 0 ↔ EvenRec W m`
- What: The even recurrence is equivalent to vanishing of a specific odd-index `rel₄`.
- How: rewrite the `rel₄` to all-odd-index form via `congr 1 <;> ring`, then six `addMulSub_odd` rewrites and `ring_nf`.
- Hypotheses: none.
- Uses from project: [rel₄, EvenRec, addMulSub_odd]
- Used by: rel₄_of_anti_oddRec_evenRec
- Visibility: public
- Lines: 371-379 (proof 6 lines; plus set_option/attribute prelude)
- Notes: `set_option allowUnsafeReducibility true` + `attribute [local reducible] Nat.rawCast Mathlib.Meta.NormNum.instAddMonoidWithOne`.

### def EllSequence.dMin
- Type: `(a : ℤ) : ℤ := if Even a then 0 else 1`
- What: Minimal admissible fourth index (0 if `a` even, 1 if odd).
- How: Plain definition.
- Hypotheses: none.
- Uses from project: []
- Used by: cMin, dMin_nonneg, dMin_lt_cMin, negOnePow_cMin_eq_dMin, negOnePow_dMin, addMulSub_mem_nonZeroDivisors, dMin_le, rel₄_of_min₂, rel₄_of_anti_oddRec_evenRec
- Visibility: public
- Lines: 381-382 (def body 1 line)
- Notes: none

### def EllSequence.cMin
- Type: `(a : ℤ) : ℤ := dMin a + 2`
- What: Minimal admissible third index (`dMin a + 2`).
- How: Plain definition.
- Hypotheses: none.
- Uses from project: [dMin]
- Used by: dMin_lt_cMin, negOnePow_cMin_eq_dMin, negOnePow_cMin, addMulSub_mem_nonZeroDivisors, rel₄_of_min₂, rel₄_of_anti_oddRec_evenRec
- Visibility: public
- Lines: 383-384 (def body 1 line)
- Notes: none

### lemma EllSequence.dMin_nonneg
- Type: `(a : ℤ) : 0 ≤ dMin a`
- What: `dMin` is nonnegative.
- How: `rw [dMin]; split_ifs <;> decide`.
- Hypotheses: none.
- Uses from project: [dMin]
- Used by: rel₄_of_min₂
- Visibility: public
- Lines: 386 (proof <1 line)
- Notes: none

### lemma EllSequence.dMin_lt_cMin
- Type: `(a : ℤ) : dMin a < cMin a`
- What: `dMin a < cMin a`.
- How: `lt_add_of_pos_right _ zero_lt_two`.
- Hypotheses: none.
- Uses from project: [dMin, cMin]
- Used by: rel₄_of_min₂
- Visibility: public
- Lines: 388 (proof <1 line)
- Notes: none

### lemma EllSequence.negOnePow_cMin_eq_dMin
- Type: `(a : ℤ) : (cMin a).negOnePow = (dMin a).negOnePow`
- What: `cMin` and `dMin` have the same parity.
- How: `rw [cMin, Int.negOnePow_add]; exact mul_one _`.
- Hypotheses: none.
- Uses from project: [cMin, dMin]
- Used by: negOnePow_cMin, rel₄_of_min₂
- Visibility: public
- Lines: 390-391 (proof 1 line)
- Notes: none

### lemma EllSequence.negOnePow_dMin
- Type: `(a : ℤ) : (dMin a).negOnePow = a.negOnePow`
- What: `dMin a` has the same parity as `a`.
- How: `split_ifs`, then `Int.negOnePow_even` / `Int.negOnePow_odd`.
- Hypotheses: none.
- Uses from project: [dMin]
- Used by: negOnePow_cMin, rel₄_of_min₂, rel₄_of_fix₂(via callers)
- Visibility: public
- Lines: 393-396 (proof 3 lines)
- Notes: none

### lemma EllSequence.negOnePow_cMin
- Type: `(a : ℤ) : (cMin a).negOnePow = a.negOnePow`
- What: `cMin a` has the same parity as `a`.
- How: `rw [negOnePow_cMin_eq_dMin, negOnePow_dMin]`.
- Hypotheses: none.
- Uses from project: [cMin, negOnePow_cMin_eq_dMin, negOnePow_dMin]
- Used by: rel₄_of_min₂
- Visibility: public
- Lines: 398-399 (proof 1 line)
- Notes: none

### lemma EllSequence.addMulSub_mem_nonZeroDivisors
- Type: `(one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰) (a : ℤ) : addMulSub W (cMin a) (dMin a) ∈ R⁰`
- What: With `W 1, W 2` non-zero-divisors, `addMulSub` at the minimal indices is a non-zero-divisor.
- How: `rw [cMin, dMin]; split_ifs`, then `mul_mem`.
- Hypotheses: `W 1, W 2` are non-zero-divisors.
- Uses from project: [addMulSub, cMin, dMin]
- Used by: rel₄_of_min₂
- Visibility: public
- Lines: 402-404 (proof 1 line)
- Notes: none

### lemma EllSequence.dMin_le
- Type: `(same : a.negOnePow = b.negOnePow) (h : 0 ≤ b) : dMin a ≤ b`
- What: `dMin a` is the least nonnegative integer of `a`'s parity, so `dMin a ≤ b` for any same-parity `b ≥ 0`.
- How: `split_ifs`, using `negOnePow_eq_one_iff` to rule out `b = 0` in the odd case.
- Hypotheses: `a, b` same parity and `b ≥ 0`.
- Uses from project: [dMin]
- Used by: rel₄_of_min₂
- Visibility: public
- Lines: 406-408 (proof 2 lines)
- Notes: none

### def EllSequence.Rel₄OfValid
- Type: `(W) (a b c d : ℤ) : Prop := HaveSameParity₄ a b c d → StrictAnti₄ a b c d → rel₄ W a b c d = 0`
- What: The four-index relation restricted to valid (same-parity, strictly-decreasing, nonnegative) quadruples.
- How: Plain definition.
- Hypotheses: none.
- Uses from project: [HaveSameParity₄, StrictAnti₄, rel₄]
- Used by: rel₄_fix₁_of_fix₂, rel₄_of_fix₂, rel₄_of_min₂, rel₄_of_anti_oddRec_evenRec
- Visibility: public
- Lines: 414-418 (def body 2 lines)
- Notes: none

### lemma EllSequence.rel₄_fix₁_of_fix₂
- Type: `(par)(le)(lt)(rel)(mem) (b c : ℤ) : Rel₄OfValid W a b c c₀ ∧ (c₀ < c → Rel₄OfValid W a b c d₀)`
- What: From `rel₄` holding for all `(a', b, c₀, d₀)` with `a' < a`, derive it for `(a,b,c,c₀)` and `(a,b,c,d₀)`.
- How: uses `mem.2` (non-zero-divisor cancellation), `rel₆_eq₃`/`rel₆_eq₃'`, three applications of the hypothesis `rel`, parity bookkeeping via `HaveSameParity₄` and `linarith`.
- Hypotheses: `c₀,d₀` same parity, `0 ≤ d₀`, `d₀ < c₀`, the inductive `rel`, `addMulSub c₀ d₀` non-zero-divisor.
- Uses from project: [Rel₄OfValid, rel₆_eq, rel₆_eq₃, rel₆_eq₃', HaveSameParity₄, addMulSub]
- Used by: rel₄_of_fix₂, rel₄_of_min₂
- Visibility: public
- Lines: 427-437 (proof 9 lines)
- Notes: none

### lemma EllSequence.rel₄_of_fix₂
- Type: `(par)(le)(lt)(rel)(mem) (b c d : ℤ) (hc : c₀ < d) (par' : d.negOnePow = d₀.negOnePow) : Rel₄OfValid W a b c d`
- What: From the same inductive hypothesis, derive `rel₄` for fully-free `(a,b,c,d)` (subject to ordering/parity side-conditions).
- How: `rel₆_eq₁₀` ten-term expansion, repeated `rel₄_fix₁_of_fix₂` (both halves) and `rel`, with ten parity/order side goals closed by `linarith`.
- Hypotheses: as `rel₄_fix₁_of_fix₂` plus `c₀ < d` and `d` parity-matched to `d₀`.
- Uses from project: [Rel₄OfValid, rel₆_eq, rel₆_eq₁₀, rel₄_fix₁_of_fix₂, HaveSameParity₄]
- Used by: rel₄_of_min₂
- Visibility: public
- Lines: 442-452 (proof 9 lines)
- Notes: none

### theorem EllSequence.rel₄_of_min₂
- Type: `(one)(two)(rel : ∀ {a' b}, a' ≤ a → Rel₄OfValid W a' b (cMin a) (dMin a)) (b c d : ℤ) : Rel₄OfValid W a b c d`
- What: Specialises the previous lemmas to `c₀ = cMin a`, `d₀ = dMin a` and removes the ordering side-conditions, giving validity for arbitrary `b,c,d`.
- How: case split `lt_or_ge (cMin a) d`; applies `rel₄_of_fix₂` or `rel₄_fix₁_of_fix₂`; pins `dMin a = d`, `cMin a = c` via `dMin_le`, `add_two_le_iff_lt_of_even_sub`, `negOnePow_cMin`/`negOnePow_dMin`.
- Hypotheses: `W 1, W 2` non-zero-divisors; the minimal-index inductive `rel`.
- Uses from project: [Rel₄OfValid, cMin, dMin, rel₄_of_fix₂, rel₄_fix₁_of_fix₂, negOnePow_cMin_eq_dMin, negOnePow_cMin, negOnePow_dMin, dMin_nonneg, dMin_lt_cMin, dMin_le, addMulSub_mem_nonZeroDivisors, HaveSameParity₄.same₀₃, StrictAnti₄]
- Used by: rel₄_of_anti_oddRec_evenRec
- Visibility: public
- Lines: 457-473 (proof 17 lines)
- Notes: none

### theorem EllSequence.rel₄_of_anti_oddRec_evenRec
- Type: `(one)(two)(oddRec : ∀ m ≥ 2, OddRec W m)(evenRec : ∀ m ≥ 3, EvenRec W m) : ∀ ⦃a b c d⦄, Rel₄OfValid W a b c d`
- What: The main induction: the four-index relation holds for all valid quadruples given the single-index odd/even recurrences and non-zero-divisor first terms.
- How: `Int.strongRec` from base `6` (smaller `a` vacuous via `six_le_of_strictAnti₄`); inductive step via `rel₄_of_min₂`, with cases handled by the inductive hypothesis, `rel₄_transf`, or `rel₃_iff₄ ∘ rel₃_iff_oddRec` / `rel₄_iff_evenRec` depending on parity.
- Hypotheses: `W 1, W 2` non-zero-divisors; `OddRec` for `m ≥ 2`; `EvenRec` for `m ≥ 3`.
- Uses from project: [Rel₄OfValid, rel₄_of_min₂, OddRec, EvenRec, HaveSameParity₄ (six_le_of_strictAnti₄, rel₄_transf, transf, strictAnti₄_transf), StrictAnti₄, avg₄, cMin, dMin, rel₃_iff₄, rel₃_iff_oddRec, rel₄_iff_evenRec]
- Used by: rel₄_of_oddRec_evenRec
- Visibility: public
- Lines: 477-505 (proof 25 lines)
- Notes: none

### lemma EllSequence.rel₄_abs
- Type: `(neg) {m n r s : ℤ} : rel₄ W |m| |n| |r| |s| = rel₄ W m n r s`
- What: `rel₄` is invariant under taking absolute values of all four indices (odd `W`).
- How: `simp_rw [rel₄, addMulSub_abs₀ W neg, addMulSub_abs₁]`.
- Hypotheses: `W` odd.
- Uses from project: [rel₄, addMulSub_abs₀, addMulSub_abs₁]
- Used by: rel₄_of_oddRec_evenRec
- Visibility: public
- Lines: 514-515 (proof 1 line)
- Notes: none

### lemma EllSequence.rel₄_swap₀₁
- Type: `(neg) {m n r s} : rel₄ W m n r s = - rel₄ W n m r s`
- What: Swapping indices 0 and 1 negates `rel₄` (odd `W`).
- How: `simp_rw [rel₄, addMulSub_swap W neg n m]; ring`.
- Hypotheses: `W` odd.
- Uses from project: [rel₄, addMulSub_swap]
- Used by: relFin4_perm
- Visibility: public
- Lines: 517-518 (proof 1 line)
- Notes: none

### lemma EllSequence.rel₄_swap₁₂
- Type: `(neg) {m n r s} : rel₄ W m n r s = - rel₄ W m r n s`
- What: Swapping indices 1 and 2 negates `rel₄` (odd `W`).
- How: `simp_rw [rel₄, addMulSub_swap W neg r n]; ring`.
- Hypotheses: `W` odd.
- Uses from project: [rel₄, addMulSub_swap]
- Used by: relFin4_perm
- Visibility: public
- Lines: 520-521 (proof 1 line)
- Notes: none

### lemma EllSequence.rel₄_swap₂₃
- Type: `(neg) {m n r s} : rel₄ W m n r s = - rel₄ W m n s r`
- What: Swapping indices 2 and 3 negates `rel₄` (odd `W`).
- How: `simp_rw [rel₄, addMulSub_swap W neg s r]; ring`.
- Hypotheses: `W` odd.
- Uses from project: [rel₄, addMulSub_swap]
- Used by: relFin4_perm
- Visibility: public
- Lines: 523-524 (proof 1 line)
- Notes: none

### def EllSequence.relFin4
- Type: `(W) (t : Fin 4 → ℤ) : R := rel₄ W (t 0) (t 1) (t 2) (t 3)`
- What: `rel₄` packaged with a `Fin 4`-tuple of indices.
- How: Plain definition.
- Hypotheses: none.
- Uses from project: [rel₄]
- Used by: relFin4_perm, relFin4_perm', rel₄_of_oddRec_evenRec
- Visibility: public
- Lines: 528-530 (def body 1 line)
- Notes: none

### theorem EllSequence.relFin4_perm
- Type: `(neg) (σ : Perm (Fin 4)) : ∀ t, relFin4 W (t ∘ σ) = Perm.sign σ • relFin4 W t`
- What: `rel₄` (as `relFin4`) is permutation-equivariant up to sign of the permutation.
- How: reduce `σ` to adjacent transpositions via `Perm.mclosure_swap_castSucc_succ` + `Submonoid.closure_induction`, base cases use `rel₄_swap₀₁/₁₂/₂₃` with `Perm.sign_swap`.
- Hypotheses: `W` odd.
- Uses from project: [relFin4, rel₄_swap₀₁, rel₄_swap₁₂, rel₄_swap₂₃]
- Used by: relFin4_perm'
- Visibility: public
- Lines: 533-542 (proof 9 lines)
- Notes: none

### lemma EllSequence.relFin4_perm'
- Type: `(neg) (σ : Perm (Fin 4)) (t) : Perm.sign σ • relFin4 W (t ∘ σ) = relFin4 W t`
- What: Inverted form of `relFin4_perm` recovering the original `relFin4`.
- How: `rw [relFin4_perm neg, ← mul_smul, Int.units_mul_self, one_smul]`.
- Hypotheses: `W` odd.
- Uses from project: [relFin4_perm, relFin4]
- Used by: rel₄_of_oddRec_evenRec
- Visibility: public
- Lines: 544-545 (proof 1 line)
- Notes: none

### lemma EllSequence.rel₄_same₀₁
- Type: `(zero : W 0 = 0) (m r s : ℤ) : rel₄ W m m r s = 0`
- What: `rel₄` vanishes when its first two indices coincide (needs `W 0 = 0`).
- How: `simp_rw [rel₄, addMulSub_same W zero]; ring`.
- Hypotheses: `W 0 = 0`.
- Uses from project: [rel₄, addMulSub_same]
- Used by: rel₄_of_oddRec_evenRec
- Visibility: public
- Lines: 552-554 (proof 1 line)
- Notes: none

### lemma EllSequence.rel₄_same₁₂
- Type: `(zero : W 0 = 0) (m n s : ℤ) : rel₄ W m n n s = 0`
- What: `rel₄` vanishes when indices 1 and 2 coincide.
- How: `simp_rw [rel₄, addMulSub_same W zero]; ring`.
- Hypotheses: `W 0 = 0`.
- Uses from project: [rel₄, addMulSub_same]
- Used by: rel₄_of_oddRec_evenRec
- Visibility: public
- Lines: 556-558 (proof 1 line)
- Notes: none

### lemma EllSequence.rel₄_same₂₃
- Type: `(zero : W 0 = 0) (m n r : ℤ) : rel₄ W m n r r = 0`
- What: `rel₄` vanishes when its last two indices coincide.
- How: `simp_rw [rel₄, addMulSub_same W zero]; ring`.
- Hypotheses: `W 0 = 0`.
- Uses from project: [rel₄, addMulSub_same]
- Used by: rel₄_of_oddRec_evenRec
- Visibility: public
- Lines: 560-562 (proof 1 line)
- Notes: none

### theorem EllSequence.rel₄_of_oddRec_evenRec
- Type: `(neg)(zero)(one)(two)(oddRec)(evenRec) {a b c d : ℤ} (same : HaveSameParity₄ a b c d) : rel₄ W a b c d = 0`
- What: The full four-index relation (for any same-parity quadruple) follows from the single-index recurrences, for an odd `W` with non-zero-divisor first terms.
- How: sort `|a|,|b|,|c|,|d|` descending via `Tuple.sort`/`Fin.revPerm`, dispatch coincident-index cases with `rel₄_same₂₃/₁₂/₀₁`, then apply `rel₄_of_anti_oddRec_evenRec` and pull back through `relFin4_perm'` + `rel₄_abs`.
- Hypotheses: `W` odd, `W 0 = 0`, `W 1, W 2` non-zero-divisors, `OddRec (m≥2)`, `EvenRec (m≥3)`, indices same parity.
- Uses from project: [rel₄, HaveSameParity₄ (abs, perm), rel₄_abs, relFin4, relFin4_perm', rel₄_same₀₁, rel₄_same₁₂, rel₄_same₂₃, rel₄_of_anti_oddRec_evenRec]
- Used by: IsEllSequence.of_oddRec_evenRec, IsEllSequence.rel₄
- Visibility: public
- Lines: 570-586 (proof 15 lines)
- Notes: none

### theorem IsEllSequence.of_oddRec_evenRec
- Type: `(neg)(zero)(one)(two)(oddRec)(evenRec) : IsEllSequence W` (root namespace)
- What: A sequence satisfying the even/odd recurrences (extended oddly to ℤ) with non-zero-divisor first terms is elliptic.
- How: `rw [rel₃_iff₄, rel₄_of_oddRec_evenRec ...]` then parity side goals via `negOnePow_two_mul`/`negOnePow_zero`.
- Hypotheses: `W` odd, `W 0 = 0`, `W 1, W 2` non-zero-divisors, `OddRec (m≥2)`, `EvenRec (m≥3)`.
- Uses from project: [IsEllSequence, rel₃_iff₄, rel₄_of_oddRec_evenRec]
- Used by: IsEllSequence.normEDS_of_mem_nonZeroDivisors
- Visibility: public
- Lines: 591-593 (proof 2 lines)
- Notes: none

### def IsDivSequence
- Type: `(W : ℤ → R) : Prop := ∀ m n : ℤ, m ∣ n → W m ∣ W n`
- What: A sequence is a divisibility sequence iff `m ∣ n ⟹ W m ∣ W n`.
- How: Plain definition.
- Hypotheses: none.
- Uses from project: []
- Used by: IsEllDivSequence, isDivSequence_id, IsDivSequence.smul/map/normEDS, IsEllSequence.isDivSequence_of_dvd
- Visibility: public
- Lines: 601-603 (def body 1 line)
- Notes: none

### def IsEllDivSequence
- Type: `(W : ℤ → R) : Prop := IsEllSequence W ∧ IsDivSequence W`
- What: An EDS is a sequence that is both elliptic and a divisibility sequence.
- How: Plain definition.
- Hypotheses: none.
- Uses from project: [IsEllSequence, IsDivSequence]
- Used by: isEllDivSequence_id, IsEllDivSequence.smul/map/eq_normEDS/normEDS, IsEllSequence.isEllDivSequence_of_dvd
- Visibility: public
- Lines: 605-607 (def body 1 line)
- Notes: none

### lemma isEllSequence_id
- Type: `: IsEllSequence id`
- What: The identity sequence `n ↦ n` is elliptic.
- How: unfold `Rel₃`, `id_eq`, then `ring1`.
- Hypotheses: none.
- Uses from project: [IsEllSequence, Rel₃]
- Used by: isEllDivSequence_id, normEDS_two_three_two
- Visibility: public
- Lines: 609-610 (proof 1 line)
- Notes: none

### lemma isDivSequence_id
- Type: `: IsDivSequence id`
- What: The identity sequence is a divisibility sequence.
- How: `fun _ _ ↦ id`.
- Hypotheses: none.
- Uses from project: [IsDivSequence]
- Used by: isEllDivSequence_id
- Visibility: public
- Lines: 612-613 (proof <1 line)
- Notes: none

### theorem isEllDivSequence_id
- Type: `: IsEllDivSequence id`
- What: The identity sequence is an EDS.
- How: `⟨isEllSequence_id, isDivSequence_id⟩`.
- Hypotheses: none.
- Uses from project: [IsEllDivSequence, isEllSequence_id, isDivSequence_id]
- Used by: unused in file
- Visibility: public
- Lines: 615-617 (proof <1 line)
- Notes: none

### lemma IsEllSequence.smul
- Type: `(h : IsEllSequence W) (x : R) : IsEllSequence (x • W)`
- What: Scaling an elliptic sequence by a ring element is again elliptic.
- How: `linear_combination (norm := ring) x ^ 4 * key` on the `Rel₃` of `W`.
- Hypotheses: `W` elliptic.
- Uses from project: [IsEllSequence, Rel₃]
- Used by: IsEllDivSequence.smul, IsEllSequence.eq_normEDS_of_dvd
- Visibility: public
- Lines: 621-626 (proof 5 lines)
- Notes: none

### lemma IsDivSequence.smul
- Type: `(h : IsDivSequence W) (x : R) : IsDivSequence (x • W)`
- What: Scaling a divisibility sequence is again a divisibility sequence.
- How: `mul_dvd_mul_left x (h · · ·)`.
- Hypotheses: `W` a divisibility sequence.
- Uses from project: [IsDivSequence]
- Used by: IsEllDivSequence.smul
- Visibility: public
- Lines: 628-629 (proof 1 line)
- Notes: none

### lemma IsEllDivSequence.smul
- Type: `(h : IsEllDivSequence W) (x : R) : IsEllDivSequence (x • W)`
- What: Scaling an EDS gives an EDS.
- How: `⟨h.left.smul x, h.right.smul x⟩`.
- Hypotheses: `W` an EDS.
- Uses from project: [IsEllDivSequence, IsEllSequence.smul, IsDivSequence.smul]
- Used by: unused in file
- Visibility: public
- Lines: 631-632 (proof <1 line)
- Notes: none

### lemma IsEllSequence.map
- Type: `(h : IsEllSequence W) : IsEllSequence (f ∘ W)`
- What: A ring-hom image of an elliptic sequence is elliptic.
- How: `simpa [Rel₃, ..., map_mul, map_pow, map_sub] using congr_arg f (h m n r)`.
- Hypotheses: `W` elliptic; `f` a ring hom.
- Uses from project: [IsEllSequence, Rel₃]
- Used by: IsEllDivSequence.map, IsEllSequence.normEDS
- Visibility: public
- Lines: 634-635 (proof 1 line)
- Notes: none

### lemma IsDivSequence.map
- Type: `(h : IsDivSequence W) : IsDivSequence (f ∘ W)`
- What: A ring-hom image of a divisibility sequence is a divisibility sequence.
- How: `map_dvd f (h · · ·)`.
- Hypotheses: `W` a divisibility sequence; `f` a ring hom.
- Uses from project: [IsDivSequence]
- Used by: IsEllDivSequence.map
- Visibility: public
- Lines: 637-638 (proof 1 line)
- Notes: none

### lemma IsEllDivSequence.map
- Type: `(h : IsEllDivSequence W) : IsEllDivSequence (f ∘ W)`
- What: A ring-hom image of an EDS is an EDS.
- How: `⟨h.1.map f, h.2.map f⟩`.
- Hypotheses: `W` an EDS; `f` a ring hom.
- Uses from project: [IsEllDivSequence, IsEllSequence.map, IsDivSequence.map]
- Used by: unused in file
- Visibility: public
- Lines: 640-641 (proof <1 line)
- Notes: none

### lemma IsEllSequence.oddRec
- Type: `(ell : IsEllSequence W) (m : ℤ) : OddRec W m`
- What: An elliptic sequence satisfies the odd recurrence at every `m`.
- How: `(rel₃_iff_oddRec W m).mp (ell _ _ _)`.
- Hypotheses: `W` elliptic.
- Uses from project: [IsEllSequence, OddRec, rel₃_iff_oddRec]
- Used by: IsEllSequence.rel₄, IsEllSequence.ext
- Visibility: public
- Lines: 650 (proof <1 line)
- Notes: none

### lemma IsEllSequence.evenRec
- Type: `(ell : IsEllSequence W) (m : ℤ) : EvenRec W m`
- What: An elliptic sequence satisfies the even recurrence at every `m`.
- How: `(rel₃_iff_evenRec W m).mp (ell _ _ _)`.
- Hypotheses: `W` elliptic.
- Uses from project: [IsEllSequence, EvenRec, rel₃_iff_evenRec]
- Used by: IsEllSequence.rel₄, IsEllSequence.ext
- Visibility: public
- Lines: 651 (proof <1 line)
- Notes: none

### lemma IsEllSequence.zero'
- Type: `[IsReduced R] (ell : IsEllSequence W) : W 0 = 0`
- What: In a reduced ring, the zeroth term of an elliptic sequence is zero.
- How: from `ell 0 0 0`, `simp_rw` to `W 0 ^ something`, then `IsReduced.eq_zero`.
- Hypotheses: `R` reduced; `W` elliptic.
- Uses from project: [IsEllSequence, Rel₃]
- Used by: unused in file
- Visibility: public
- Lines: 653-656 (proof 3 lines)
- Notes: none

### lemma IsEllSequence.zero
- Type: `(ell) (m : ℤ) (mem : W (2*m) ∈ R⁰) : W 0 = 0`
- What: If some even term is a non-zero-divisor, the zeroth term is zero.
- How: from `ell m m (2*m)`, `rw [Rel₃, ...]`, cancel via `mem.2` and `pow_mem`.
- Hypotheses: `W (2m)` a non-zero-divisor; `W` elliptic.
- Uses from project: [IsEllSequence, Rel₃]
- Used by: IsEllSequence.rel₄, IsEllSequence.ext
- Visibility: public
- Lines: 658-663 (proof 4 lines)
- Notes: none

### lemma IsEllSequence.sub_add_neg_sub_mul_eq_zero
- Type: `(ell) (m n r : ℤ) : (W (m-n) + W (-(m-n))) * W (m+n) * W r^2 = 0`
- What: A symmetrised consequence of ellipticity capturing that `W` is "almost odd".
- How: add `ell m n r` and `ell n m r`, regroup via distributivity, `convert ... using 1; ring`.
- Hypotheses: `W` elliptic.
- Uses from project: [IsEllSequence]
- Used by: IsEllSequence.neg
- Visibility: public
- Lines: 665-670 (proof 5 lines)
- Notes: none

### lemma IsEllSequence.neg
- Type: `(ell)(one)(two) (m : ℤ) : W (-m) = - W m`
- What: An elliptic sequence is an odd function, given non-zero-divisor first two terms.
- How: `eq_neg_iff_add_eq_zero`, split `m` even/odd via `even_or_odd'`, cancel `W 1`/`W 2` factors using `sub_add_neg_sub_mul_eq_zero` + `pow_mem`.
- Hypotheses: `W 1, W 2` non-zero-divisors; `W` elliptic.
- Uses from project: [IsEllSequence, sub_add_neg_sub_mul_eq_zero]
- Used by: IsEllSequence.rel₄, IsEllSequence.ext
- Visibility: public
- Lines: 676-688 (proof 13 lines)
- Notes: long(30-50)? No — 13 lines.

### lemma IsEllSequence.rel₄ (protected)
- Type: `(ell)(one)(two) {a b c d : ℤ} (same : HaveSameParity₄ a b c d) : rel₄ W a b c d = 0`
- What: An elliptic sequence satisfies the four-index relation on same-parity quadruples.
- How: `rel₄_of_oddRec_evenRec` fed `ell.neg`, `ell.zero`, `ell.oddRec`, `ell.evenRec`.
- Hypotheses: `W 1, W 2` non-zero-divisors; `W` elliptic; same-parity indices.
- Uses from project: [rel₄, HaveSameParity₄, rel₄_of_oddRec_evenRec, IsEllSequence.neg, IsEllSequence.zero, IsEllSequence.oddRec, IsEllSequence.evenRec]
- Used by: IsEllSequence.net
- Visibility: public (protected)
- Lines: 690-692 (proof 2 lines)
- Notes: none

### lemma IsEllSequence.net (protected)
- Type: `(ell)(one)(two) (p q r s : ℤ) : net W p q r s = 0`
- What: An elliptic sequence (non-zero-divisor first terms) satisfies the net relation everywhere.
- How: `net_eq_rel₄` then `ell.rel₄` with parity discharged by `negOnePow_add`/`negOnePow_two_mul`.
- Hypotheses: `W 1, W 2` non-zero-divisors; `W` elliptic.
- Uses from project: [net, net_eq_rel₄, HaveSameParity₄, IsEllSequence.rel₄]
- Used by: IsEllSequence.invar
- Visibility: public (protected)
- Lines: 694-697 (proof 3 lines)
- Notes: none

### lemma IsEllSequence.invar
- Type: `(ell)(one)(two) (s m n : ℤ) : invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m`
- What: The invariant cross-product identity for an elliptic sequence with non-zero-divisor first terms.
- How: `invar_of_net _ (ell.net one two) _ _ _`.
- Hypotheses: `W 1, W 2` non-zero-divisors; `W` elliptic.
- Uses from project: [invarNum, invarDenom, invar_of_net, IsEllSequence.net]
- Used by: unused in file
- Visibility: public
- Lines: 699-700 (proof 1 line)
- Notes: none

### def preNormEDS'
- Type: `(b c d : R) : ℕ → R` with base cases `0↦0,1↦1,2↦1,3↦c,4↦d` and even/odd well-founded recursion on `n+5`
- What: Auxiliary ℕ-indexed normalised EDS with seeds `0,1,1,c,d`; the recursive step splits on the parity of `n` and of `m = n/2`, inserting factors of `b`.
- How: well-founded recursion (decreasing-index obligations discharged by `omega`).
- Hypotheses: none.
- Uses from project: []
- Used by: preNormEDS'_zero..four, preNormEDS'_even, preNormEDS'_odd, preNormEDS_ofNat, normEDS_ofNat, map_preNormEDS'
- Visibility: public
- Lines: 710-736 (def body ~27 lines, recursion)
- Notes: none (no proof per se; well-founded recursion with `omega` obligations).

### lemma preNormEDS'_zero (@[simp])
- Type: `: preNormEDS' b c d 0 = 0`
- What: Seed value 0.
- How: `rw [preNormEDS']`.
- Hypotheses: none.
- Uses from project: [preNormEDS']
- Used by: map_preNormEDS'
- Visibility: public
- Lines: 738-740 (proof 1 line)
- Notes: none

### lemma preNormEDS'_one (@[simp])
- Type: `: preNormEDS' b c d 1 = 1`
- What: Seed value 1.
- How: `rw [preNormEDS']`.
- Hypotheses: none.
- Uses from project: [preNormEDS']
- Used by: map_preNormEDS'
- Visibility: public
- Lines: 742-744 (proof 1 line)
- Notes: none

### lemma preNormEDS'_two (@[simp])
- Type: `: preNormEDS' b c d 2 = 1`
- What: Seed value 1 at index 2.
- How: `rw [preNormEDS']`.
- Hypotheses: none.
- Uses from project: [preNormEDS']
- Used by: map_preNormEDS'
- Visibility: public
- Lines: 746-748 (proof 1 line)
- Notes: none

### lemma preNormEDS'_three (@[simp])
- Type: `: preNormEDS' b c d 3 = c`
- What: Seed value `c` at index 3.
- How: `rw [preNormEDS']`.
- Hypotheses: none.
- Uses from project: [preNormEDS']
- Used by: map_preNormEDS'
- Visibility: public
- Lines: 750-752 (proof 1 line)
- Notes: none

### lemma preNormEDS'_four (@[simp])
- Type: `: preNormEDS' b c d 4 = d`
- What: Seed value `d` at index 4.
- How: `rw [preNormEDS']`.
- Hypotheses: none.
- Uses from project: [preNormEDS']
- Used by: map_preNormEDS'
- Visibility: public
- Lines: 754-756 (proof 1 line)
- Notes: none

### lemma preNormEDS'_even
- Type: `(m : ℕ) : preNormEDS' b c d (2*(m+3)) = p(m+2)^2*p(m+3)*p(m+5) - p(m+1)*p(m+3)*p(m+4)^2`
- What: Closed even-step recurrence for `preNormEDS'`.
- How: rewrite `2*(m+3)=2*m+1+5`, unfold `preNormEDS'` with `dif_neg (not_even_two_mul_add_one)`, `Nat.mul_add_div`.
- Hypotheses: none.
- Uses from project: [preNormEDS']
- Used by: preNormEDS_even, map_preNormEDS'
- Visibility: public
- Lines: 758-762 (proof 2 lines)
- Notes: none

### lemma preNormEDS'_odd
- Type: `(m : ℕ) : preNormEDS' b c d (2*(m+2)+1) = p(m+4)*p(m+2)^3*(if Even m then b else 1) - p(m+1)*p(m+3)^3*(if Even m then 1 else b)`
- What: Closed odd-step recurrence for `preNormEDS'`.
- How: rewrite `2*(m+2)+1=2*m+5`, unfold with `dif_pos (even_two_mul)`, `Nat.mul_div_cancel_left`.
- Hypotheses: none.
- Uses from project: [preNormEDS']
- Used by: preNormEDS_odd, map_preNormEDS'
- Visibility: public
- Lines: 764-768 (proof 2 lines)
- Notes: none

### def preNormEDS
- Type: `(b c d : R) (n : ℤ) : R := n.sign * preNormEDS' b c d n.natAbs`
- What: The ℤ-indexed auxiliary sequence extending `preNormEDS'` oddly to negatives via `sign`·(value at `natAbs`).
- How: Plain definition.
- Hypotheses: none.
- Uses from project: [preNormEDS']
- Used by: preNormEDS_ofNat..four, preNormEDS_neg, preNormEDS_even, preNormEDS_odd, complEDS₂, complEDS₂_*, preNormEDS_mul_complEDS₂, normEDS, compl₂EDSAux, compl₂EDS, map_preNormEDS
- Visibility: public
- Lines: 770-775 (def body 1 line)
- Notes: none

### lemma preNormEDS_ofNat (@[simp])
- Type: `(n : ℕ) : preNormEDS b c d n = preNormEDS' b c d n`
- What: On naturals `preNormEDS` agrees with `preNormEDS'`.
- How: case `n=0` by `simp`; else `Int.sign_natCast_of_ne_zero`.
- Hypotheses: none.
- Uses from project: [preNormEDS, preNormEDS']
- Used by: preNormEDS_even, preNormEDS_odd
- Visibility: public
- Lines: 777-781 (proof 3 lines)
- Notes: none

### lemma preNormEDS_zero (@[simp])
- Type: `: preNormEDS b c d 0 = 0`
- What: Value 0 at 0.
- How: `simp [preNormEDS]`.
- Hypotheses: none.
- Uses from project: [preNormEDS]
- Used by: unused in file
- Visibility: public
- Lines: 783-785 (proof 1 line)
- Notes: none

### lemma preNormEDS_one (@[simp])
- Type: `: preNormEDS b c d 1 = 1`
- What: Value 1 at 1.
- How: `simp [preNormEDS]`.
- Hypotheses: none.
- Uses from project: [preNormEDS]
- Used by: normEDS_six_eq_mul
- Visibility: public
- Lines: 787-789 (proof 1 line)
- Notes: none

### lemma preNormEDS_two (@[simp])
- Type: `: preNormEDS b c d 2 = 1`
- What: Value 1 at 2.
- How: `simp [preNormEDS, Int.sign_eq_one_of_pos]`.
- Hypotheses: none.
- Uses from project: [preNormEDS]
- Used by: normEDS_six_eq_mul
- Visibility: public
- Lines: 791-793 (proof 1 line)
- Notes: none

### lemma preNormEDS_three (@[simp])
- Type: `: preNormEDS b c d 3 = c`
- What: Value `c` at 3.
- How: `simp [preNormEDS, Int.sign_eq_one_of_pos]`.
- Hypotheses: none.
- Uses from project: [preNormEDS]
- Used by: unused in file
- Visibility: public
- Lines: 795-797 (proof 1 line)
- Notes: none

### lemma preNormEDS_four (@[simp])
- Type: `: preNormEDS b c d 4 = d`
- What: Value `d` at 4.
- How: `simp [preNormEDS, Int.sign_eq_one_of_pos]`.
- Hypotheses: none.
- Uses from project: [preNormEDS]
- Used by: normEDS_six_eq_mul
- Visibility: public
- Lines: 799-801 (proof 1 line)
- Notes: none

### lemma preNormEDS_neg (@[simp])
- Type: `(n : ℤ) : preNormEDS b c d (-n) = -preNormEDS b c d n`
- What: `preNormEDS` is an odd function.
- How: `simp [preNormEDS]`.
- Hypotheses: none.
- Uses from project: [preNormEDS]
- Used by: preNormEDS_even, preNormEDS_odd, complEDS₂_neg, compl₂EDSAux_neg, compl₂EDS_neg, normEDS_neg, map_preNormEDS(indirect)
- Visibility: public
- Lines: 803-805 (proof 1 line)
- Notes: none

### lemma preNormEDS_even
- Type: `(m : ℤ) : preNormEDS b c d (2*m) = p(m-1)^2*p m*p(m+2) - p(m-2)*p m*p(m+1)^2`
- What: ℤ-indexed even-step recurrence for `preNormEDS`.
- How: `Int.negInduction`; `nat` case reduces to `preNormEDS'_even` after small-`m` `simp` and `norm_cast`; `neg` case uses `preNormEDS_neg` and `ring1`.
- Hypotheses: none.
- Uses from project: [preNormEDS, preNormEDS_ofNat, preNormEDS'_even, preNormEDS_neg]
- Used by: preNormEDS_mul_complEDS₂, compl₂EDS(via normEDS_mul_compl₂EDS)
- Visibility: public
- Lines: 807-820 (proof 11 lines)
- Notes: none

### lemma preNormEDS_odd
- Type: `(m : ℤ) : preNormEDS b c d (2*m+1) = p(m+2)*p m^3*(if Even m then b else 1) - p(m-1)*p(m+1)^3*(if Even m then 1 else b)`
- What: ℤ-indexed odd-step recurrence for `preNormEDS`.
- How: `Int.negInduction`; `nat` case via `preNormEDS'_odd` after `norm_cast`; `neg` case rewrites the negated arguments and uses `preNormEDS_neg`, `ite_not`, `ring1`.
- Hypotheses: none.
- Uses from project: [preNormEDS, preNormEDS_ofNat, preNormEDS'_odd, preNormEDS_neg]
- Used by: normEDS_odd
- Visibility: public
- Lines: 822-838 (proof 16 lines)
- Notes: none

### def complEDS₂
- Type: `(b c d : R) (k : ℤ) : R := (p(k-1)^2*p(k+2) - p(k-2)*p(k+1)^2)*(if Even k then 1 else b)` where `p = preNormEDS (b^4) c d`
- What: The 2-complement sequence witnessing `W(k) ∣ W(2k)`, i.e. `W(k)·Wᶜ₂(k) = W(2k)`, defined from `preNormEDS (b^4)`.
- How: Plain definition.
- Hypotheses: none.
- Uses from project: [preNormEDS]
- Used by: complEDS₂_zero..four, complEDS₂_neg, preNormEDS_mul_complEDS₂, normEDS_mul_complEDS₂(via), complEDS₂_mul_b, complEDS'_even, complEDS_even, complEDS₂_two_three_two, map_complEDS₂
- Visibility: public
- Lines: 844-846 (def body 2 lines)
- Notes: none

### lemma complEDS₂_zero (@[simp])
- Type: `: complEDS₂ b c d 0 = 2`
- What: Value `2` at 0.
- How: `simp [complEDS₂, one_add_one_eq_two]`.
- Hypotheses: none.
- Uses from project: [complEDS₂]
- Used by: complEDS_even, complEDS₂_two_three_two
- Visibility: public
- Lines: 848-850 (proof 1 line)
- Notes: none

### lemma complEDS₂_one (@[simp])
- Type: `: complEDS₂ b c d 1 = b`
- What: Value `b` at 1.
- How: `simp [complEDS₂]`.
- Hypotheses: none.
- Uses from project: [complEDS₂]
- Used by: unused in file
- Visibility: public
- Lines: 852-854 (proof 1 line)
- Notes: none

### lemma complEDS₂_two (@[simp])
- Type: `: complEDS₂ b c d 2 = d`
- What: Value `d` at 2.
- How: `simp [complEDS₂]`.
- Hypotheses: none.
- Uses from project: [complEDS₂]
- Used by: unused in file
- Visibility: public
- Lines: 856-858 (proof 1 line)
- Notes: none

### lemma complEDS₂_three (@[simp])
- Type: `: complEDS₂ b c d 3 = preNormEDS (b^4) c d 5 * b - d^2 * b`
- What: Value at 3.
- How: `simp [complEDS₂, if_neg (¬Even 3), sub_mul]`.
- Hypotheses: none.
- Uses from project: [complEDS₂, preNormEDS]
- Used by: unused in file
- Visibility: public
- Lines: 860-862 (proof 1 line)
- Notes: none

### lemma complEDS₂_four (@[simp])
- Type: `: complEDS₂ b c d 4 = c^2 * preNormEDS (b^4) c d 6 - preNormEDS (b^4) c d 5 ^ 2`
- What: Value at 4.
- How: `simp [complEDS₂, if_pos (Even 4)]`.
- Hypotheses: none.
- Uses from project: [complEDS₂, preNormEDS]
- Used by: unused in file
- Visibility: public
- Lines: 864-867 (proof 1 line)
- Notes: none

### lemma complEDS₂_neg (@[simp])
- Type: `(k : ℤ) : complEDS₂ b c d (-k) = complEDS₂ b c d k`
- What: `complEDS₂` is even in `k`.
- How: `simp_rw [complEDS₂, ..., preNormEDS_neg, even_neg]; ring1`.
- Hypotheses: none.
- Uses from project: [complEDS₂, preNormEDS_neg]
- Used by: complEDS₂_mul_b, complEDS_even
- Visibility: public
- Lines: 869-872 (proof 2 lines)
- Notes: none

### lemma preNormEDS_mul_complEDS₂
- Type: `(k : ℤ) : preNormEDS (b^4) c d k * complEDS₂ b c d k = preNormEDS (b^4) c d (2*k) * if Even k then 1 else b`
- What: Defining property: `preNormEDS·complEDS₂` recovers the doubled-index `preNormEDS` (up to the parity factor).
- How: `rw [complEDS₂, preNormEDS_even]; ring1`.
- Hypotheses: none.
- Uses from project: [preNormEDS, complEDS₂, preNormEDS_even]
- Used by: normEDS_mul_complEDS₂
- Visibility: public
- Lines: 874-877 (proof 2 lines)
- Notes: none

### def normEDS
- Type: `(b c d : R) (n : ℤ) : R := preNormEDS (b^4) c d n * if Even n then b else 1`
- What: The canonical normalised EDS with seeds `W0=0,W1=1,W2=b,W3=c,W4=db`; even terms get an extra factor `b`.
- How: Plain definition.
- Hypotheses: none.
- Uses from project: [preNormEDS]
- Used by: a very large fraction of the rest of the file (normEDS_*, complEDS₂_mul_b, compl₂EDS*, complEDS', complEDS, universalNormEDS, all `IsEll*.normEDS`, invar*_normEDS, redInvar*, net/rel₄_normEDS, map_normEDS, etc.)
- Visibility: public
- Lines: 886-891 (def body 1 line)
- Notes: none

### lemma normEDS_def
- Type: `(n : ℤ) : normEDS b c d n = preNormEDS (b^4) c d n * if Even n then b else 1`
- What: Definitional restatement of `normEDS`.
- How: `rfl`.
- Hypotheses: none.
- Uses from project: [normEDS, preNormEDS]
- Used by: unused in file
- Visibility: public
- Lines: 893-894 (proof <1 line)
- Notes: none

### lemma normEDS_ofNat (@[simp])
- Type: `(n : ℕ) : normEDS b c d n = preNormEDS' (b^4) c d n * if Even n then b else 1`
- What: `normEDS` on naturals in terms of `preNormEDS'`.
- How: `simp_rw [normEDS, preNormEDS_ofNat, Int.even_coe_nat]`.
- Hypotheses: none.
- Uses from project: [normEDS, preNormEDS_ofNat]
- Used by: unused in file
- Visibility: public
- Lines: 896-899 (proof 1 line)
- Notes: none

### lemma normEDS_zero (@[simp])
- Type: `: normEDS b c d 0 = 0`
- What: `W 0 = 0`.
- How: `simp [normEDS]`.
- Hypotheses: none.
- Uses from project: [normEDS]
- Used by: normEDS_mul_complEDS, IsDivSequence.normEDS(indirect)
- Visibility: public
- Lines: 901-903 (proof 1 line)
- Notes: none

### lemma normEDS_one (@[simp])
- Type: `: normEDS b c d 1 = 1`
- What: `W 1 = 1`.
- How: `simp [normEDS]`.
- Hypotheses: none.
- Uses from project: [normEDS]
- Used by: normEDS_of_mem_nonZeroDivisors, normEDS_two_three_two, normEDS_mul_complEDS_of_mem, net_normEDS, ...
- Visibility: public
- Lines: 905-907 (proof 1 line)
- Notes: none

### lemma normEDS_two (@[simp])
- Type: `: normEDS b c d 2 = b`
- What: `W 2 = b`.
- How: `simp [normEDS]`.
- Hypotheses: none.
- Uses from project: [normEDS]
- Used by: normEDS_of_mem_nonZeroDivisors, normEDS_two_three_two, normEDS_mul_complEDS_of_mem, invarDenom_eq_redInvarDenom_mul, net_normEDS, ...
- Visibility: public
- Lines: 909-911 (proof 1 line)
- Notes: none

### lemma normEDS_three (@[simp])
- Type: `: normEDS b c d 3 = c`
- What: `W 3 = c`.
- How: `simp [normEDS, show ¬Even (3:ℤ)]`.
- Hypotheses: none.
- Uses from project: [normEDS]
- Used by: normEDS_six_eq_mul, normEDS_two_three_two, invarDenom_eq_redInvarDenom_mul
- Visibility: public
- Lines: 913-915 (proof 1 line)
- Notes: none

### lemma normEDS_four (@[simp])
- Type: `: normEDS b c d 4 = d * b`
- What: `W 4 = d·b`.
- How: `simp [normEDS, show ¬Odd (4:ℤ)]`.
- Hypotheses: none.
- Uses from project: [normEDS]
- Used by: normEDS_two_three_two, IsEllSequence.eq_normEDS_of_dvd
- Visibility: public
- Lines: 917-919 (proof 1 line)
- Notes: none

### lemma normEDS_neg (@[simp])
- Type: `(n : ℤ) : normEDS b c d (-n) = -normEDS b c d n`
- What: `normEDS` is an odd function.
- How: `simp_rw [normEDS, preNormEDS_neg, neg_mul, even_neg]`.
- Hypotheses: none.
- Uses from project: [normEDS, preNormEDS_neg]
- Used by: normEDS_of_mem_nonZeroDivisors, complEDS₂_mul_b, compl₂EDS_mul_b, normEDS_mul_compl₂EDS, complEDS_odd
- Visibility: public
- Lines: 921-923 (proof 1 line)
- Notes: none

### lemma normEDS_mul_complEDS₂
- Type: `(k : ℤ) : normEDS b c d k * complEDS₂ b c d k = normEDS b c d (2*k)`
- What: `complEDS₂` witnesses `W(k) ∣ W(2k)` for `normEDS`.
- How: `simp_rw [normEDS, mul_right_comm, preNormEDS_mul_complEDS₂, apply_ite₂, ...]` resolving the parity factor.
- Hypotheses: none.
- Uses from project: [normEDS, complEDS₂, preNormEDS_mul_complEDS₂]
- Used by: normEDS_dvd_normEDS_two_mul, normEDS_even, complEDS₂_two_three_two
- Visibility: public
- Lines: 925-928 (proof 2 lines)
- Notes: none

### lemma normEDS_dvd_normEDS_two_mul
- Type: `(k : ℤ) : normEDS b c d k ∣ normEDS b c d (2*k)`
- What: `W(k) ∣ W(2k)` for `normEDS`.
- How: `⟨complEDS₂ .., (normEDS_mul_complEDS₂ ..).symm⟩`.
- Hypotheses: none.
- Uses from project: [normEDS, complEDS₂, normEDS_mul_complEDS₂]
- Used by: unused in file
- Visibility: public
- Lines: 930-931 (proof <1 line)
- Notes: none

### lemma complEDS₂_mul_b
- Type: `(k : ℤ) : complEDS₂ b c d k * b = W(k-1)^2*W(k+2) - W(k-2)*W(k+1)^2` (`W = normEDS`)
- What: `complEDS₂·b` equals the standard two-term `normEDS` expression.
- How: `Int.negInduction`; `nat` case `simp_rw` parity lemmas + `split_ifs <;> ring1`; `neg` case via `normEDS_neg` and the IH.
- Hypotheses: none.
- Uses from project: [complEDS₂, normEDS, complEDS₂_neg, normEDS_neg]
- Used by: normEDS_even
- Visibility: public
- Lines: 933-943 (proof 8 lines)
- Notes: none

### lemma normEDS_even
- Type: `(m : ℤ) : normEDS b c d (2*m) * b = W(m-1)^2*W m*W(m+2) - W(m-2)*W m*W(m+1)^2`
- What: The even-step recurrence for `normEDS` (with the factor `b`).
- How: `← normEDS_mul_complEDS₂`, `complEDS₂_mul_b`, `ring1`.
- Hypotheses: none.
- Uses from project: [normEDS, normEDS_mul_complEDS₂, complEDS₂_mul_b]
- Used by: normEDS_of_mem_nonZeroDivisors
- Visibility: public
- Lines: 945-949 (proof 2 lines)
- Notes: none

### lemma normEDS_odd
- Type: `(m : ℤ) : normEDS b c d (2*m+1) = W(m+2)*W m^3 - W(m-1)*W(m+1)^3`
- What: The odd-step recurrence for `normEDS`.
- How: `simp_rw [normEDS, preNormEDS_odd, if_neg ..., parity lemmas]; split_ifs <;> ring1`.
- Hypotheses: none.
- Uses from project: [normEDS, preNormEDS_odd]
- Used by: normEDS_of_mem_nonZeroDivisors
- Visibility: public
- Lines: 951-956 (proof 2 lines)
- Notes: none

### theorem IsEllSequence.normEDS_of_mem_nonZeroDivisors (private)
- Type: `(hb : b ∈ R⁰) : IsEllSequence (normEDS b c d)`
- What: For `b` a non-zero-divisor, `normEDS` is an elliptic sequence (superseded by the unconditional `IsEllSequence.normEDS`).
- How: `IsEllSequence.of_oddRec_evenRec` fed `normEDS_neg/zero/one/two` and the recurrences via `normEDS_odd`/`normEDS_even` with `lift ... to ℕ`.
- Hypotheses: `b` a non-zero-divisor.
- Uses from project: [IsEllSequence, normEDS, IsEllSequence.of_oddRec_evenRec, normEDS_neg, normEDS_zero, normEDS_one, normEDS_two, OddRec, EvenRec, normEDS_odd, normEDS_even]
- Used by: IsEllSequence.normEDS
- Visibility: private
- Lines: 959-971 (proof 11 lines)
- Notes: none

### lemma invarNum_normEDS
- Type: `(n : ℤ) : invarNum (normEDS b c d) 1 n = W(n+2)*W(n-1)^2 + W(n+1)^2*W(n-2) + W n^3*b^2` (`W = normEDS`)
- What: Specialises `invarNum` at `s=1` for `normEDS`, using `W 2 = b`.
- How: `simp [invarNum]`.
- Hypotheses: none.
- Uses from project: [invarNum, normEDS]
- Used by: invarNum_eq_redInvarNum_mul
- Visibility: public
- Lines: 973-975 (proof 1 line)
- Notes: none

### lemma invarNum_normEDS_two
- Type: `: invarNum (normEDS b c d) 1 2 = (d + b^4) * b`
- What: Value of `invarNum` at `s=1, n=2`.
- How: `simp [invarNum, right_distrib, ← pow_succ, ← pow_add]`.
- Hypotheses: none.
- Uses from project: [invarNum, normEDS]
- Used by: invar₂_normEDS_of_mem_nonZeroDivisors
- Visibility: public
- Lines: 977-978 (proof 1 line)
- Notes: none

### lemma invarDenom_normEDS_two
- Type: `: invarDenom (normEDS b c d) 1 2 = c * b`
- What: Value of `invarDenom` at `s=1, n=2`.
- How: `simp [invarDenom]`.
- Hypotheses: none.
- Uses from project: [invarDenom, normEDS]
- Used by: invar₂_normEDS_of_mem_nonZeroDivisors
- Visibility: public
- Lines: 980 (proof <1 line)
- Notes: none

### def normEDSRec' (@[elab_as_elim], noncomputable)
- Type: strong even/odd recursion principle for ℕ-indexed normalised EDS
- What: `P n` for all `n` given base cases `P 0..4` and even/odd strong-recursion steps.
- How: built on `Nat.evenOddStrongRec`.
- Hypotheses: base cases and strong even/odd steps.
- Uses from project: []
- Used by: normEDSRec, map_preNormEDS'
- Visibility: public (noncomputable)
- Lines: 982-993 (body 2 lines)
- Notes: none

### def normEDSRec (@[elab_as_elim], noncomputable)
- Type: (non-strong) even/odd recursion principle for ℕ-indexed normalised EDS
- What: `P n` for all `n` given base cases and even/odd steps depending only on `P(m+1)..P(m+5)`.
- How: reduces to `normEDSRec'` with `linarith` bounds.
- Hypotheses: base cases and finite-lookback even/odd steps.
- Uses from project: [normEDSRec']
- Used by: IsEllSequence.ext
- Visibility: public (noncomputable)
- Lines: 995-1009 (body 2 lines)
- Notes: none

### def compl₂EDSAux
- Type: `(b c d : R) (m : ℤ) : R := p(m-2)*p(m+1)^2*(if Even m then 1 else b)` where `p = preNormEDS (b^4)`
- What: Auxiliary expression appearing in the reduced-invariant numerator and the `ω` division polynomials.
- How: Plain definition.
- Hypotheses: none.
- Uses from project: [preNormEDS]
- Used by: compl₂EDSAux_zero..neg_two, compl₂EDSAux_mul_b, compl₂EDSAux_neg, redInvarNum, compl₂EDS_eq_redInvarNum_sub, invarNum_eq_redInvarNum_mul, map_compl₂EDSAux, map_redInvarNum
- Visibility: public
- Lines: 1015-1018 (def body 1 line)
- Notes: none

### lemma compl₂EDSAux_zero (@[simp])
- Type: `: compl₂EDSAux b c d 0 = -1`
- How: `simp [compl₂EDSAux]`.
- What: Value `-1` at 0.
- Hypotheses: none.
- Uses from project: [compl₂EDSAux]
- Used by: unused in file
- Visibility: public
- Lines: 1020 (proof <1 line)
- Notes: none

### lemma compl₂EDSAux_one (@[simp])
- Type: `: compl₂EDSAux b c d 1 = -b`
- What: Value `-b` at 1.
- How: `simp [compl₂EDSAux]`.
- Hypotheses: none.
- Uses from project: [compl₂EDSAux]
- Used by: unused in file
- Visibility: public
- Lines: 1021 (proof <1 line)
- Notes: none

### lemma compl₂EDSAux_neg_one (@[simp])
- Type: `: compl₂EDSAux b c d (-1) = 0`
- What: Value 0 at -1.
- How: `simp [compl₂EDSAux]`.
- Hypotheses: none.
- Uses from project: [compl₂EDSAux]
- Used by: unused in file
- Visibility: public
- Lines: 1022 (proof <1 line)
- Notes: none

### lemma compl₂EDSAux_two (@[simp])
- Type: `: compl₂EDSAux b c d 2 = 0`
- What: Value 0 at 2.
- How: `simp [compl₂EDSAux]`.
- Hypotheses: none.
- Uses from project: [compl₂EDSAux]
- Used by: unused in file
- Visibility: public
- Lines: 1023 (proof <1 line)
- Notes: none

### lemma compl₂EDSAux_neg_two (@[simp])
- Type: `: compl₂EDSAux b c d (-2) = -d`
- What: Value `-d` at -2.
- How: `simp [compl₂EDSAux]`.
- Hypotheses: none.
- Uses from project: [compl₂EDSAux]
- Used by: unused in file
- Visibility: public
- Lines: 1024 (proof <1 line)
- Notes: none

### lemma compl₂EDSAux_mul_b
- Type: `(m : ℤ) : compl₂EDSAux b c d m * b = normEDS b c d (m-2) * normEDS b c d (m+1)^2`
- What: `compl₂EDSAux·b` equals the corresponding two-term `normEDS` product.
- How: `simp_rw [compl₂EDSAux, normEDS, parity lemmas]; split_ifs <;> ring`.
- Hypotheses: none.
- Uses from project: [compl₂EDSAux, normEDS]
- Used by: invarNum_eq_redInvarNum_mul
- Visibility: public
- Lines: 1026-1029 (proof 2 lines)
- Notes: none

### def compl₂EDS
- Type: `(b c d : R) (m : ℤ) : R := (p(m-1)^2*p(m+2) - p(m-2)*p(m+1)^2)*(if Even m then 1 else b)` where `p = preNormEDS (b^4)`
- What: The "complement" of `W(m)` in `W(2m)`: the witness of `W(m) ∣ W(2m)` for `normEDS`.
- How: Plain definition.
- Hypotheses: none.
- Uses from project: [preNormEDS]
- Used by: compl₂EDSAux_neg, compl₂EDS_zero..neg, normEDS_mul_compl₂EDS, normEDS_dvd_two_mul, compl₂EDS_mul_b, normEDS_six_eq_mul, complEDS(via), map_compl₂EDS, redInvarNum, compl₂EDS_eq_redInvarNum_sub, compl₂EDS_eq_aeval, compl₂EDS_two_three_two
- Visibility: public
- Lines: 1031-1034 (def body 2 lines)
- Notes: none

### lemma compl₂EDSAux_neg
- Type: `(m : ℤ) : compl₂EDSAux b c d (-m) = -compl₂EDS b c d m - compl₂EDSAux b c d m`
- What: Reflection identity tying `compl₂EDSAux` at `-m` to `compl₂EDS` and `compl₂EDSAux` at `m`.
- How: `simp_rw [compl₂EDSAux, compl₂EDS, neg lemmas, preNormEDS_neg, even_neg]; ring`.
- Hypotheses: none.
- Uses from project: [compl₂EDSAux, compl₂EDS, preNormEDS_neg]
- Used by: unused in file
- Visibility: public
- Lines: 1036-1038 (proof 2 lines)
- Notes: none

### lemma compl₂EDS_zero (@[simp])
- Type: `: compl₂EDS b c d 0 = 2`
- What: Value `2` at 0.
- How: `simp [compl₂EDS, one_add_one_eq_two]`.
- Hypotheses: none.
- Uses from project: [compl₂EDS]
- Used by: unused in file
- Visibility: public
- Lines: 1040 (proof <1 line)
- Notes: none

### lemma compl₂EDS_one (@[simp])
- Type: `: compl₂EDS b c d 1 = b`
- What: Value `b` at 1.
- How: `simp [compl₂EDS]`.
- Hypotheses: none.
- Uses from project: [compl₂EDS]
- Used by: unused in file
- Visibility: public
- Lines: 1041 (proof <1 line)
- Notes: none

### lemma compl₂EDS_two (@[simp])
- Type: `: compl₂EDS b c d 2 = d`
- What: Value `d` at 2.
- How: `simp [compl₂EDS]`.
- Hypotheses: none.
- Uses from project: [compl₂EDS]
- Used by: unused in file
- Visibility: public
- Lines: 1042 (proof <1 line)
- Notes: none

### lemma compl₂EDS_neg (@[simp])
- Type: `(m : ℤ) : compl₂EDS b c d (-m) = compl₂EDS b c d m`
- What: `compl₂EDS` is even in `m`.
- How: `simp_rw [compl₂EDS, neg lemmas, preNormEDS_neg, even_neg]; ring`.
- Hypotheses: none.
- Uses from project: [compl₂EDS, preNormEDS_neg]
- Used by: normEDS_mul_compl₂EDS, compl₂EDS_mul_b
- Visibility: public
- Lines: 1044-1045 (proof 1 line)
- Notes: none

### lemma normEDS_mul_compl₂EDS
- Type: `(m : ℤ) : normEDS b c d m * compl₂EDS b c d m = normEDS b c d (2*m)`
- What: `compl₂EDS` witnesses `W(m) ∣ W(2m)` for `normEDS`.
- How: `Int.negInduction`; `nat` case unfolds `normEDS`/`compl₂EDS` with `preNormEDS_even`, `mul_mul_mul_comm`, `push_cast; ring`; `neg` case via `normEDS_neg`, `compl₂EDS_neg` and IH.
- Hypotheses: none.
- Uses from project: [normEDS, compl₂EDS, preNormEDS_even, normEDS_neg, compl₂EDS_neg]
- Used by: normEDS_dvd_two_mul, normEDS_six_eq_mul, compl₂EDS_two_three_two, normEDS_mul_complEDS_of_mem(via)
- Visibility: public
- Lines: 1047-1058 (proof 10 lines)
- Notes: none

### lemma normEDS_dvd_two_mul
- Type: `(m : ℤ) : normEDS b c d m ∣ normEDS b c d (2*m)`
- What: `W(m) ∣ W(2m)` for `normEDS` (via `compl₂EDS`).
- How: `⟨_, (normEDS_mul_compl₂EDS b c d m).symm⟩`.
- Hypotheses: none.
- Uses from project: [normEDS, normEDS_mul_compl₂EDS]
- Used by: unused in file
- Visibility: public
- Lines: 1060-1061 (proof <1 line)
- Notes: none

### lemma compl₂EDS_mul_b
- Type: `(m : ℤ) : compl₂EDS b c d m * b = W(m-1)^2*W(m+2) - W(m-2)*W(m+1)^2` (`W = normEDS`)
- What: `compl₂EDS·b` equals the standard two-term `normEDS` expression.
- How: `Int.negInduction`; `nat` case via parity lemmas and `split_ifs <;> ring`; `neg` case via `normEDS_neg`, `compl₂EDS_neg`, `convert hm; ring`.
- Hypotheses: none.
- Uses from project: [compl₂EDS, normEDS, normEDS_neg, compl₂EDS_neg]
- Used by: invarNum_eq_redInvarNum_mul
- Visibility: public
- Lines: 1063-1072 (proof 9 lines)
- Notes: none

### lemma normEDS_six_eq_mul
- Type: `: normEDS b c d 6 = (normEDS b c d 5 - d^2) * b * c`
- What: Closed form for `W 6` in terms of `W 5`, `b`, `c`.
- How: write `6 = 2*3`, `← normEDS_mul_compl₂EDS`, unfold `compl₂EDS`/`normEDS`/`preNormEDS` at small values, `ring`.
- Hypotheses: none.
- Uses from project: [normEDS, normEDS_mul_compl₂EDS, compl₂EDS, normEDS_three, preNormEDS_one, preNormEDS_two, preNormEDS_four]
- Used by: invarDenom_eq_redInvarDenom_mul
- Visibility: public
- Lines: 1074-1078 (proof 4 lines)
- Notes: none

### def EllSequence.compl'
- Type: `(W₁ compl₂ : ℤ → R) (m : ℤ) : ℕ → R` with `0↦0, 1↦1`, and a parity-split well-founded recursion on `n+2`
- What: From sequences representing `W(m)/W(1)` and `W(2m)/W(m)`, builds `W(n·m)/W(m)` division-freely for `n : ℕ`.
- How: well-founded recursion with `omega`-discharged decreasing obligations.
- Hypotheses: none.
- Uses from project: []
- Used by: compl, compl_ofNat, map_compl', complEDS(via compl), redInvarDenom_*(via complEDS)
- Visibility: public
- Lines: 1086-1097 (def body ~12 lines)
- Notes: none

### def EllSequence.compl
- Type: `(W₁ compl₂ : ℤ → R) (m : ℤ) (n : ℤ) : R := n.sign * compl' W₁ compl₂ m n.natAbs`
- What: `W(n·m)/W(m)` for `n : ℤ`, extending `compl'` oddly to negatives.
- How: Plain definition.
- Hypotheses: none.
- Uses from project: [compl']
- Used by: compl_ofNat, compl_neg, complEDS, map_compl, mul_compl_eq_apply_mul_of_mem_nonZeroDivisors, normEDS_mul_complEDS_of_mem(via)
- Visibility: public
- Lines: 1099-1100 (def body 1 line)
- Notes: none

### lemma EllSequence.compl_ofNat
- Type: `(n : ℕ) : compl W₁ compl₂ m n = compl' W₁ compl₂ m n`
- What: On naturals `compl` agrees with `compl'`.
- How: case `n=0` by `simp`; else `Int.sign_natCast_of_ne_zero`, `Int.natAbs_natCast`.
- Hypotheses: none.
- Uses from project: [compl, compl']
- Used by: mul_compl_eq_apply_mul_of_mem_nonZeroDivisors
- Visibility: public
- Lines: 1102-1106 (proof 3 lines)
- Notes: none

### lemma EllSequence.compl_neg
- Type: `(n : ℤ) : compl W₁ compl₂ m (-n) = -compl W₁ compl₂ m n`
- What: `compl` is odd in `n`.
- How: `simp [compl, Int.sign_neg, Int.natAbs_neg, neg_mul]`.
- Hypotheses: none.
- Uses from project: [compl]
- Used by: mul_compl_eq_apply_mul_of_mem_nonZeroDivisors
- Visibility: public
- Lines: 1107-1108 (proof 1 line)
- Notes: none

### def EllSequence.complEDS
- Type: `(b c d : R) (m : ℤ) := compl (normEDS b c d) (compl₂EDS b c d) m`
- What: `W(n·m)/W(m)` for `W = normEDS`, instantiating `compl` with `normEDS` and `compl₂EDS`.
- How: Plain definition.
- Hypotheses: none.
- Uses from project: [compl, normEDS, compl₂EDS]
- Used by: map_complEDS, complEDS_eq_aeval, redInvarDenom, redInvarDenom_*, normEDS_mul_complEDS*, normEDS_mul_complEDS_of_mem
- Visibility: public
- Lines: 1110-1111 (def body 1 line)
- Notes: This is the `EllSequence.complEDS` (distinct from the root-level `complEDS` defined later in §ComplEDS).

### lemma map_preNormEDS'
- Type: `(n : ℕ) : f (preNormEDS' b c d n) = preNormEDS' (f b) (f c) (f d) n`
- What: Ring homs commute with `preNormEDS'`.
- How: `normEDSRec'` induction; recursive case `simp` with `preNormEDS'_odd/even`, `apply_ite f`, then re-apply IH.
- Hypotheses: `f` a ring hom.
- Uses from project: [preNormEDS', preNormEDS'_zero..four, preNormEDS'_odd, preNormEDS'_even, normEDSRec']
- Used by: map_preNormEDS
- Visibility: public
- Lines: 1121-1130 (proof 9 lines)
- Notes: none

### lemma map_preNormEDS
- Type: `(n : ℤ) : f (preNormEDS b c d n) = preNormEDS (f b) (f c) (f d) n`
- What: Ring homs commute with `preNormEDS`.
- How: `rw [preNormEDS, map_mul, map_intCast, map_preNormEDS', preNormEDS]`.
- Hypotheses: `f` a ring hom.
- Uses from project: [preNormEDS, map_preNormEDS']
- Used by: map_normEDS, map_compl₂EDS, map_compl₂EDSAux, map_complEDS₂
- Visibility: public
- Lines: 1132-1133 (proof 1 line)
- Notes: none

### lemma map_normEDS
- Type: `(n : ℤ) : f (normEDS b c d n) = normEDS (f b) (f c) (f d) n`
- What: Ring homs commute with `normEDS`.
- How: `rw [normEDS, map_mul, map_preNormEDS, map_pow, apply_ite f, map_one, normEDS]`.
- Hypotheses: `f` a ring hom.
- Uses from project: [normEDS, map_preNormEDS]
- Used by: map_complEDS(via), normEDS_eq_aeval, universalNormEDS_ne_zero, normEDS_mul_complEDS, net_normEDS, invar₂_normEDS, map_redInvarNum, map_redInvarDenom, map_complEDS_root(via)
- Visibility: public
- Lines: 1135-1136 (proof 1 line)
- Notes: none

### lemma map_compl₂EDS
- Type: `(n : ℤ) : f (compl₂EDS b c d n) = compl₂EDS (f b) (f c) (f d) n`
- What: Ring homs commute with `compl₂EDS`.
- How: `simp only [compl₂EDS, map_sub, map_mul, map_pow, map_preNormEDS, apply_ite f, map_one]`.
- Hypotheses: `f` a ring hom.
- Uses from project: [compl₂EDS, map_preNormEDS]
- Used by: map_complEDS, compl₂EDS_eq_aeval
- Visibility: public
- Lines: 1138-1139 (proof 1 line)
- Notes: none

### lemma EllSequence.map_compl'
- Type: `(W₁ compl₂ : ℤ → R) (m : ℤ) (n : ℕ) : f (compl' W₁ compl₂ m n) = compl' (f ∘ W₁) (f ∘ compl₂) m n`
- What: Ring homs commute with `compl'` (pushed into the two component sequences).
- How: `n.strong_induction_on`; unfold `compl'`, `split_ifs`, re-apply IH with `omega` bounds.
- Hypotheses: `f` a ring hom.
- Uses from project: [compl']
- Used by: map_compl
- Visibility: public
- Lines: 1141-1151 (proof 9 lines)
- Notes: none

### lemma EllSequence.map_compl
- Type: `(W₁ compl₂ : ℤ → R) (m n : ℤ) : f (compl W₁ compl₂ m n) = compl (f ∘ W₁) (f ∘ compl₂) m n`
- What: Ring homs commute with `compl`.
- How: `simp [compl, map_compl']`.
- Hypotheses: `f` a ring hom.
- Uses from project: [compl, map_compl']
- Used by: map_complEDS
- Visibility: public
- Lines: 1153-1155 (proof 1 line)
- Notes: none

### lemma map_complEDS
- Type: `(m n : ℤ) : f (complEDS b c d m n) = complEDS (f b) (f c) (f d) m n`
- What: Ring homs commute with `EllSequence.complEDS`.
- How: `simp [complEDS, EllSequence.map_compl]`, then `congr 1` and `ext`/`Function.comp` rewrites via `map_normEDS`, `map_compl₂EDS`.
- Hypotheses: `f` a ring hom.
- Uses from project: [complEDS(EllSequence), EllSequence.map_compl, map_normEDS, map_compl₂EDS]
- Used by: complEDS_eq_aeval, normEDS_mul_complEDS(via)
- Visibility: public
- Lines: 1157-1161 (proof 5 lines)
- Notes: none

### lemma map_addMulSub
- Type: `(m n : ℤ) : f (addMulSub W m n) = addMulSub (f ∘ W) m n`
- What: Ring homs commute with `addMulSub`.
- How: `simp_rw [addMulSub, map_mul, Function.comp]`.
- Hypotheses: `f` a ring hom.
- Uses from project: [addMulSub]
- Used by: map_rel₄
- Visibility: public
- Lines: 1163-1164 (proof 1 line)
- Notes: none

### lemma map_rel₄
- Type: `(p q r s : ℤ) : f (rel₄ W p q r s) = rel₄ (f ∘ W) p q r s`
- What: Ring homs commute with `rel₄`.
- How: `simp_rw [rel₄, map_add, map_sub, map_mul, map_addMulSub]`.
- Hypotheses: `f` a ring hom.
- Uses from project: [rel₄, map_addMulSub]
- Used by: map_net
- Visibility: public
- Lines: 1166-1167 (proof 1 line)
- Notes: none

### lemma map_net
- Type: `(p q r s : ℤ) : f (net W p q r s) = net (f ∘ W) p q r s`
- What: Ring homs commute with `net`.
- How: `simp_rw [net_eq_rel₄, map_rel₄]`.
- Hypotheses: `f` a ring hom.
- Uses from project: [net, net_eq_rel₄, map_rel₄]
- Used by: net_normEDS
- Visibility: public
- Lines: 1169-1170 (proof 1 line)
- Notes: none

### lemma map_invarNum
- Type: `(s m : ℤ) : f (invarNum W s m) = invarNum (f ∘ W) s m`
- What: Ring homs commute with `invarNum`.
- How: `simp only [invarNum, map_add, map_mul, map_pow, Function.comp]`.
- Hypotheses: `f` a ring hom.
- Uses from project: [invarNum]
- Used by: invar₂_normEDS
- Visibility: public
- Lines: 1172-1173 (proof 1 line)
- Notes: none

### lemma map_invarDenom
- Type: `(s m : ℤ) : f (invarDenom W s m) = invarDenom (f ∘ W) s m`
- What: Ring homs commute with `invarDenom`.
- How: `simp_rw [invarDenom, map_mul, Function.comp]`.
- Hypotheses: `f` a ring hom.
- Uses from project: [invarDenom]
- Used by: invar₂_normEDS
- Visibility: public
- Lines: 1175-1176 (proof 1 line)
- Notes: none

### inductive Param
- Type: `Type | B | C | D`
- What: A three-element type indexing the three parameters `b, c, d` of a normalised EDS.
- How: Plain inductive.
- Hypotheses: none.
- Uses from project: []
- Used by: universalNormEDS, normEDS_eq_aeval, compl₂EDS_eq_aeval, complEDS_eq_aeval, universalNormEDS_ne_zero, invar₂_normEDS, redInvar_normEDS, net_normEDS, and the `Param.rec` evaluation points throughout
- Visibility: public
- Lines: 1178-1179 (def body 1 line)
- Notes: none

### def universalNormEDS (noncomputable)
- Type: `: ℤ → MvPolynomial Param ℤ := normEDS (X B) (X C) (X D)`
- What: The universal normalised EDS over `ℤ[X_B, X_C, X_D]`; every `normEDS` is its `aeval`-image, and its nonzero terms are non-zero-divisors.
- How: Plain definition.
- Hypotheses: none.
- Uses from project: [normEDS]
- Used by: normEDS_eq_aeval, universalNormEDS_ne_zero, universalNormEDS_mem_nonZeroDivisors, net_normEDS, invar₂_normEDS
- Visibility: public (noncomputable)
- Lines: 1182-1187 (def body 1 line)
- Notes: none

### lemma normEDS_eq_aeval
- Type: `: normEDS b c d = (aeval (Param.rec b c d) <| universalNormEDS ·)`
- What: Every `normEDS b c d` is the `aeval`-specialisation of `universalNormEDS`.
- How: `simp_rw [universalNormEDS, map_normEDS, aeval_X]`.
- Hypotheses: none.
- Uses from project: [normEDS, universalNormEDS, map_normEDS]
- Used by: IsEllSequence.normEDS, net_normEDS
- Visibility: public
- Lines: 1189-1190 (proof 1 line)
- Notes: none

### lemma compl₂EDS_eq_aeval
- Type: `: compl₂EDS b c d = (aeval (Param.rec b c d) <| compl₂EDS (X B) (X C) (X D) ·)`
- What: `compl₂EDS b c d` is the `aeval`-specialisation of the universal `compl₂EDS`.
- How: `simp_rw [map_compl₂EDS, aeval_X]`.
- Hypotheses: none.
- Uses from project: [compl₂EDS, map_compl₂EDS]
- Used by: unused in file
- Visibility: public
- Lines: 1192-1195 (proof 1 line)
- Notes: none

### lemma complEDS_eq_aeval
- Type: `: complEDS b c d = (aeval (Param.rec b c d) <| complEDS (X B) (X C) (X D) · ·)`
- What: `EllSequence.complEDS b c d` is the `aeval`-specialisation of the universal `complEDS`.
- How: `simp_rw [map_complEDS, aeval_X]`.
- Hypotheses: none.
- Uses from project: [complEDS(EllSequence), map_complEDS]
- Used by: unused in file
- Visibility: public
- Lines: 1197-1200 (proof 1 line)
- Notes: none

### lemma IsEllSequence.normEDS (protected)
- Type: `: IsEllSequence (normEDS b c d)`
- What: A normalised EDS is unconditionally an elliptic sequence (no `b ∈ R⁰` needed).
- How: `rw [normEDS_eq_aeval]`, then `map` of the universal `normEDS_of_mem_nonZeroDivisors` (using `X_ne_zero`).
- Hypotheses: none.
- Uses from project: [IsEllSequence, normEDS, normEDS_eq_aeval, IsEllSequence.map, normEDS_of_mem_nonZeroDivisors]
- Used by: normEDS_two_three_two, IsEllSequence.eq_normEDS_of_dvd, normEDS_mul_complEDS_of_mem, net_normEDS, IsEllDivSequence.normEDS
- Visibility: public (protected)
- Lines: 1210-1214 (proof 2 lines)
- Notes: none

### theorem IsEllSequence.ext (protected)
- Type: `(ellW)(ellU)(one)(two)(h1..h4 : W i = U i for i=1..4) : W = U`
- What: Two elliptic sequences agreeing on their first four terms (with non-zero-divisor first two) are equal.
- How: `funext` + `Int.negInduction`; `nat` case `normEDSRec` with even/odd steps cancelling `W 2·W 1²`/`W 1³` via `mul_cancel_right_mem_nonZeroDivisors`, `ellW.evenRec`/`oddRec`; `neg` case via `ellW.neg`, `ellU.neg`.
- Hypotheses: `W, U` elliptic; `W 1, W 2` non-zero-divisors; agreement on first four terms.
- Uses from project: [IsEllSequence, normEDSRec, IsEllSequence.zero, IsEllSequence.evenRec, IsEllSequence.oddRec, IsEllSequence.neg]
- Used by: normEDS_two_three_two, IsEllSequence.eq_normEDS_of_dvd
- Visibility: public (protected)
- Lines: 1218-1232 (proof 14 lines)
- Notes: uses `erw`.

### lemma normEDS_two_three_two
- Type: `: normEDS (2 : ℤ) 3 2 = id`
- What: With parameters `b=2, c=3, d=2`, the normalised EDS is the identity sequence `n ↦ n`.
- How: `IsEllSequence.ext` between `normEDS` and `id` using non-zero-divisor `1, 2` and matching the four seeds.
- Hypotheses: none.
- Uses from project: [normEDS, IsEllSequence.ext, IsEllSequence.normEDS, isEllSequence_id, normEDS_one, normEDS_two, normEDS_three, normEDS_four]
- Used by: compl₂EDS_two_three_two, universalNormEDS_ne_zero
- Visibility: public
- Lines: 1235-1239 (proof 4 lines)
- Notes: none

### lemma compl₂EDS_two_three_two
- Type: `(n : ℤ) : compl₂EDS (2 : ℤ) 3 2 n = 2`
- What: At parameters `2,3,2`, the complement `compl₂EDS` is constantly `2`.
- How: case `n=0` by `compl₂EDS_zero`; else from `normEDS_mul_compl₂EDS` with `normEDS_two_three_two` and `mul_right_cancel₀`.
- Hypotheses: none.
- Uses from project: [compl₂EDS, normEDS_mul_compl₂EDS, normEDS_two_three_two, compl₂EDS_zero]
- Used by: unused in file
- Visibility: public
- Lines: 1241-1248 (proof 7 lines)
- Notes: none

### lemma universalNormEDS_ne_zero
- Type: `{n : ℤ} (hn : n ≠ 0) : universalNormEDS n ≠ 0`
- What: Every nonzero-index term of the universal normalised EDS is nonzero in the polynomial ring.
- How: `apply_fun aeval (Param.rec 2 3 2)`, reduce to `normEDS_two_three_two` (the identity), then `n ≠ 0`.
- Hypotheses: `n ≠ 0`.
- Uses from project: [universalNormEDS, map_normEDS, normEDS_two_three_two]
- Used by: universalNormEDS_mem_nonZeroDivisors
- Visibility: public
- Lines: 1250-1255 (proof 5 lines)
- Notes: none

### lemma universalNormEDS_mem_nonZeroDivisors
- Type: `{n : ℤ} (hn : n ≠ 0) : universalNormEDS n ∈ (MvPolynomial Param ℤ)⁰`
- What: Nonzero-index universal terms are non-zero-divisors (a domain, so nonzero ⟹ non-zero-divisor).
- How: `mem_nonZeroDivisors_of_ne_zero (universalNormEDS_ne_zero hn)`.
- Hypotheses: `n ≠ 0`.
- Uses from project: [universalNormEDS_ne_zero]
- Used by: normEDS_mul_complEDS
- Visibility: public
- Lines: 1257-1260 (proof 1 line)
- Notes: none

### theorem IsEllSequence.eq_normEDS_of_dvd
- Type: `(ellW)(one)(two)(dvd₁₂)(dvd₁₃)(dvd₂₄) : ∃ b c d, W = (W 1 * normEDS b c d ·)`
- What: An elliptic sequence with non-zero-divisor first terms and the three base divisibilities is `W 1` times a normalised EDS.
- How: take `b,c,d` from the divisibility witnesses, then `IsEllSequence.ext` against `W 1 • normEDS`.
- Hypotheses: `W` elliptic; `W 1, W 2` non-zero-divisors; `W1∣W2`, `W1∣W3`, `W2∣W4`.
- Uses from project: [IsEllSequence, normEDS, IsEllSequence.ext, IsEllSequence.smul, IsEllSequence.normEDS, normEDS_four]
- Used by: IsEllDivSequence.eq_normEDS, IsEllSequence.isDivSequence_of_dvd
- Visibility: public
- Lines: 1268-1272 (proof 4 lines)
- Notes: none

### theorem IsEllDivSequence.eq_normEDS
- Type: `(one)(two) (h : IsEllDivSequence W) : ∃ b c d, W = (W 1 * normEDS b c d ·)`
- What: An EDS with non-zero-divisor first two terms is a constant multiple of a normalised EDS.
- How: `h.1.eq_normEDS_of_dvd` fed the three base divisibilities from `h.2`.
- Hypotheses: `W 1, W 2` non-zero-divisors; `W` an EDS.
- Uses from project: [IsEllDivSequence, normEDS, IsEllSequence.eq_normEDS_of_dvd]
- Used by: unused in file
- Visibility: public
- Lines: 1274-1279 (proof 1 line)
- Notes: none

### lemma IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors
- Type: `(ellW)(one)(two)(W₁)(compl₂)(h₁ : ∀ m, W 1*W₁ m = W m)(h₂ : ∀ m, W m*compl₂ m = W(2m))(m n)(mem : W m ∈ R⁰) : W m * compl W₁ compl₂ m n = W (n*m)`
- What: The `compl` construction multiplied by `W m` recovers `W(n·m)`, for an elliptic `W` with non-zero-divisor first terms and `W m` a non-zero-divisor.
- How: `Int.negInduction` + strong induction on `n`; even step uses `h₂` and IH; odd step cancels `W m·W 1²` via `mul_cancel_right_mem_nonZeroDivisors`, the addition formula `ellW (...) (...) 1`, `h₁`, and two IH calls; `neg` step via `ellW.neg`, `compl_neg`.
- Hypotheses: `W` elliptic; `W 1, W 2` non-zero-divisors; `W m` a non-zero-divisor; the recursion `h₁, h₂`.
- Uses from project: [IsEllSequence, compl, compl', compl_ofNat, compl_neg, IsEllSequence.zero, IsEllSequence.neg]
- Used by: normEDS_mul_complEDS_of_mem
- Visibility: public
- Lines: 1293-1317 (proof 23 lines)
- Notes: none

### lemma normEDS_mul_complEDS_of_mem (private)
- Type: `(hb : b ∈ R⁰) {m : ℤ} (hm : normEDS b c d m ∈ R⁰) (n : ℤ) : normEDS b c d m * complEDS b c d m n = normEDS b c d (n*m)`
- What: For `b` and `W m` non-zero-divisors, `EllSequence.complEDS` witnesses `W(m) ∣ W(n·m)`.
- How: unfold `complEDS` to `compl ...`, then apply `mul_compl_eq_apply_mul_of_mem_nonZeroDivisors` with `IsEllSequence.normEDS`, `normEDS_one`/`normEDS_two`, and `normEDS_mul_compl₂EDS`.
- Hypotheses: `b ∈ R⁰`, `normEDS b c d m ∈ R⁰`.
- Uses from project: [normEDS, complEDS(EllSequence), IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors, IsEllSequence.normEDS, normEDS_one, normEDS_two, normEDS_mul_compl₂EDS]
- Used by: normEDS_mul_complEDS
- Visibility: private
- Lines: 1319-1331 (proof 7 lines)
- Notes: none

### lemma normEDS_mul_complEDS
- Type: `(m n : ℤ) : normEDS b c d m * complEDS b c d m n = normEDS b c d (n*m)`
- What: Unconditional version: `EllSequence.complEDS` witnesses `W(m) ∣ W(n·m)` for any `normEDS`.
- How: case `m=0` by `simp`; else `aeval`-transfer of the universal `normEDS_mul_complEDS_of_mem` using `universalNormEDS_mem_nonZeroDivisors` and `X_ne_zero`.
- Hypotheses: none.
- Uses from project: [normEDS, complEDS(EllSequence), normEDS_mul_complEDS_of_mem, map_normEDS, map_complEDS, universalNormEDS_mem_nonZeroDivisors, normEDS_zero]
- Used by: normEDS_mul_complEDS_div, IsDivSequence.normEDS
- Visibility: public
- Lines: 1333-1343 (proof 7 lines)
- Notes: none

### lemma normEDS_mul_complEDS_div
- Type: `{m : ℤ} (hm : m ≠ 0) (n : ℤ) (dvd : m ∣ n) : normEDS b c d m * complEDS b c d m (n/m) = normEDS b c d n`
- What: Division-form of `normEDS_mul_complEDS`: recovers `W(n)` from `W(m)` and the complement at `n/m` when `m ∣ n`.
- How: obtain witness from `dvd`, `Int.mul_ediv_cancel_left`, `normEDS_mul_complEDS`, `mul_comm`.
- Hypotheses: `m ≠ 0`, `m ∣ n`.
- Uses from project: [normEDS, complEDS(EllSequence), normEDS_mul_complEDS]
- Used by: invarDenom_eq_redInvarDenom_mul
- Visibility: public
- Lines: 1345-1349 (proof 2 lines)
- Notes: none

### def EllSequence.redInvarNum
- Type: `(b c d : R) (m : ℤ) : R := compl₂EDS b c d m + normEDS b c d m^3*b + 2*compl₂EDSAux b c d m`
- What: Numerator of the reduced invariant `(W(m-1)²W(m+2)+W(m-2)W(m+1)²+W₂²W(m)³)/W₂`, with `W₃W₂ = b·c` cancelled from `invarNum`.
- How: Plain definition.
- Hypotheses: none.
- Uses from project: [compl₂EDS, normEDS, compl₂EDSAux]
- Used by: compl₂EDS_eq_redInvarNum_sub, invarNum_eq_redInvarNum_mul, map_redInvarNum, redInvar_normEDS
- Visibility: public
- Lines: 1357-1360 (def body 1 line)
- Notes: none

### lemma EllSequence.compl₂EDS_eq_redInvarNum_sub
- Type: `: compl₂EDS b c d m = redInvarNum b c d m - normEDS b c d m^3*b - 2*compl₂EDSAux b c d m`
- What: Inverts the definition of `redInvarNum` to express `compl₂EDS`.
- How: `rw [redInvarNum]; ring`.
- Hypotheses: none.
- Uses from project: [compl₂EDS, redInvarNum, normEDS, compl₂EDSAux]
- Used by: unused in file
- Visibility: public
- Lines: 1362-1365 (proof 1 line)
- Notes: none

### lemma EllSequence.invarNum_eq_redInvarNum_mul
- Type: `: invarNum (normEDS b c d) 1 m = redInvarNum b c d m * b`
- What: `invarNum` (at `s=1`) factors as `redInvarNum · b`.
- How: `simp_rw [redInvarNum, right_distrib, compl₂EDS_mul_b, compl₂EDSAux_mul_b, invarNum_normEDS]; ring`.
- Hypotheses: none.
- Uses from project: [invarNum, normEDS, redInvarNum, compl₂EDS_mul_b, compl₂EDSAux_mul_b, invarNum_normEDS]
- Used by: redInvar_normEDS_of_mem_nonZeroDivisors
- Visibility: public
- Lines: 1367-1369 (proof 1 line)
- Notes: none

### def EllSequence.redInvarDenom
- Type: `(b c d : R) (m : ℤ) : R` — a 6-way `if m % 6 = …` case split over `complEDS`/`normEDS` products
- What: The expression `W(m+1)W(m)W(m-1)/W₃W₂` for a normalised EDS, as a division-free piecewise formula in `m mod 6`.
- How: Plain definition (six-branch `if`).
- Hypotheses: none.
- Uses from project: [complEDS(EllSequence), normEDS]
- Used by: invarDenom_eq_redInvarDenom_mul, redInvarDenom_zero/one/two, map_redInvarDenom, redInvar_normEDS
- Visibility: public
- Lines: 1371-1381 (def body ~9 lines)
- Notes: none

### lemma EllSequence.invarDenom_eq_redInvarDenom_mul
- Type: `: invarDenom (normEDS b c d) 1 m = redInvarDenom b c d m * b * c`
- What: `invarDenom` (at `s=1`) factors as `redInvarDenom · b · c`.
- How: `split_ifs` on `m % 6`, in each branch rewriting via `normEDS_mul_complEDS_div` (with `Int.dvd_*_emod_*` divisibility facts) and `normEDS_six_eq_mul`/`normEDS_three`/`normEDS_two`, then `ring`; impossible residue closed by `interval_cases`.
- Hypotheses: none.
- Uses from project: [invarDenom, normEDS, redInvarDenom, normEDS_mul_complEDS_div, normEDS_six_eq_mul, normEDS_three, normEDS_two]
- Used by: redInvar_normEDS_of_mem_nonZeroDivisors
- Visibility: public
- Lines: 1383-1405 (proof 21 lines)
- Notes: comment "-- slow"; uses `interval_cases`.

### lemma EllSequence.redInvarDenom_zero (@[simp])
- Type: `: redInvarDenom b c d 0 = 0`
- What: Value 0 at 0.
- How: `simp [redInvarDenom, complEDS, compl', compl]`.
- Hypotheses: none.
- Uses from project: [redInvarDenom, complEDS(EllSequence), compl', compl]
- Used by: unused in file
- Visibility: public
- Lines: 1407-1408 (proof 1 line)
- Notes: none

### lemma EllSequence.redInvarDenom_one (@[simp])
- Type: `: redInvarDenom b c d 1 = 0`
- What: Value 0 at 1.
- How: `simp [redInvarDenom, complEDS, compl', compl]`.
- Hypotheses: none.
- Uses from project: [redInvarDenom, complEDS(EllSequence), compl', compl]
- Used by: unused in file
- Visibility: public
- Lines: 1410-1411 (proof 1 line)
- Notes: none

### lemma EllSequence.redInvarDenom_two (@[simp])
- Type: `: redInvarDenom b c d 2 = 1`
- What: Value 1 at 2.
- How: `simp [redInvarDenom, complEDS, compl', compl]`.
- Hypotheses: none.
- Uses from project: [redInvarDenom, complEDS(EllSequence), compl', compl]
- Used by: unused in file
- Visibility: public
- Lines: 1413-1414 (proof 1 line)
- Notes: none

### lemma EllSequence.map_compl₂EDSAux
- Type: `: f (compl₂EDSAux b c d m) = compl₂EDSAux (f b) (f c) (f d) m`
- What: Ring homs commute with `compl₂EDSAux`.
- How: `simp [compl₂EDSAux, apply_ite f, map_preNormEDS]`.
- Hypotheses: `f` a ring hom.
- Uses from project: [compl₂EDSAux, map_preNormEDS]
- Used by: map_redInvarNum
- Visibility: public
- Lines: 1416-1417 (proof 1 line)
- Notes: none

### lemma EllSequence.map_redInvarNum
- Type: `: f (redInvarNum b c d m) = redInvarNum (f b) (f c) (f d) m`
- What: Ring homs commute with `redInvarNum`.
- How: `simp only [redInvarNum, map_add, map_mul, map_pow, map_compl₂EDS, map_normEDS, map_compl₂EDSAux, map_ofNat]`.
- Hypotheses: `f` a ring hom.
- Uses from project: [redInvarNum, map_compl₂EDS, map_normEDS, map_compl₂EDSAux]
- Used by: redInvar_normEDS
- Visibility: public
- Lines: 1419-1421 (proof 1 line)
- Notes: none

### lemma EllSequence.map_redInvarDenom
- Type: `: f (redInvarDenom b c d m) = redInvarDenom (f b) (f c) (f d) m`
- What: Ring homs commute with `redInvarDenom`.
- How: `simp [redInvarDenom, apply_ite f, map_normEDS, map_complEDS]`.
- Hypotheses: `f` a ring hom.
- Uses from project: [redInvarDenom, map_normEDS, map_complEDS]
- Used by: redInvar_normEDS
- Visibility: public
- Lines: 1423-1424 (proof 1 line)
- Notes: none

### theorem IsDivSequence.normEDS (protected)
- Type: `: IsDivSequence (normEDS b c d)`
- What: A normalised EDS is a divisibility sequence.
- How: from `m ∣ n` get witness `k`, `rw [hk, mul_comm]`, use `normEDS_mul_complEDS` as the divisibility witness.
- Hypotheses: none.
- Uses from project: [IsDivSequence, normEDS, normEDS_mul_complEDS]
- Used by: IsEllDivSequence.normEDS, IsEllSequence.isDivSequence_of_dvd
- Visibility: public (protected)
- Lines: 1430-1435 (proof 3 lines)
- Notes: none

### theorem IsEllDivSequence.normEDS (protected)
- Type: `: IsEllDivSequence (normEDS b c d)`
- What: A normalised EDS is an EDS (the headline result `isEllDivSequence_normEDS`).
- How: `⟨IsEllSequence.normEDS, IsDivSequence.normEDS⟩`.
- Hypotheses: none.
- Uses from project: [IsEllDivSequence, normEDS, IsEllSequence.normEDS, IsDivSequence.normEDS]
- Used by: unused in file
- Visibility: public (protected)
- Lines: 1437-1440 (proof 1 line)
- Notes: none

### lemma IsEllSequence.isDivSequence_of_dvd
- Type: `(ellW)(one)(two)(dvd₁₂)(dvd₁₃)(dvd₂₄) : IsDivSequence W`
- What: An elliptic sequence satisfying the three base divisibilities (non-zero-divisor first terms) is a divisibility sequence.
- How: write `W = W 1 • normEDS` via `eq_normEDS_of_dvd`, then `mul_dvd_mul_left` of `IsDivSequence.normEDS`.
- Hypotheses: `W` elliptic; `W 1, W 2` non-zero-divisors; `W1∣W2`, `W1∣W3`, `W2∣W4`.
- Uses from project: [IsDivSequence, IsEllSequence.eq_normEDS_of_dvd, IsDivSequence.normEDS]
- Used by: IsEllSequence.isEllDivSequence_of_dvd
- Visibility: public
- Lines: 1442-1449 (proof 5 lines)
- Notes: none

### lemma IsEllSequence.isEllDivSequence_of_dvd
- Type: `(ellW)(one)(two)(dvd₁₂)(dvd₁₃)(dvd₂₄) : IsEllDivSequence W`
- What: Such an elliptic sequence is in fact an EDS.
- How: `⟨ellW, ellW.isDivSequence_of_dvd ...⟩`.
- Hypotheses: as `isDivSequence_of_dvd`.
- Uses from project: [IsEllDivSequence, IsEllSequence.isDivSequence_of_dvd]
- Used by: unused in file
- Visibility: public
- Lines: 1451-1453 (proof 1 line)
- Notes: none

### lemma net_normEDS
- Type: `(p q r s : ℤ) : net (normEDS b c d) p q r s = 0`
- What: A normalised EDS satisfies the net relation everywhere.
- How: `normEDS_eq_aeval`, push `aeval` through `← map_net`, then `IsEllSequence.normEDS.net` at the universal level with `X_ne_zero`.
- Hypotheses: none.
- Uses from project: [net, normEDS, normEDS_eq_aeval, map_net, universalNormEDS, IsEllSequence.net, IsEllSequence.normEDS, normEDS_one, normEDS_two]
- Used by: rel₄_normEDS, invar_normEDS
- Visibility: public
- Lines: 1459-1465 (proof 5 lines)
- Notes: none

### lemma rel₄_normEDS
- Type: `(p q r s : ℤ) (same : HaveSameParity₄ p q r s) : rel₄ (normEDS b c d) p q r s = 0`
- What: A normalised EDS satisfies the four-index relation on same-parity quadruples.
- How: `rw [same.rel₄_eq_net, net_normEDS]`.
- Hypotheses: indices same parity.
- Uses from project: [rel₄, normEDS, HaveSameParity₄.rel₄_eq_net, net_normEDS]
- Used by: unused in file
- Visibility: public
- Lines: 1467-1470 (proof 1 line)
- Notes: none

### lemma invar_normEDS
- Type: `(s m n : ℤ) : invarNum (normEDS b c d) s m * invarDenom (normEDS b c d) s n = invarNum (normEDS b c d) s n * invarDenom (normEDS b c d) s m`
- What: The invariant cross-product identity for `normEDS`.
- How: `invar_of_net _ net_normEDS _ _ _`.
- Hypotheses: none.
- Uses from project: [invarNum, invarDenom, normEDS, invar_of_net, net_normEDS]
- Used by: invar₂_normEDS_of_mem_nonZeroDivisors
- Visibility: public
- Lines: 1472-1476 (proof 1 line)
- Notes: none

### lemma invar₂_normEDS_of_mem_nonZeroDivisors (private)
- Type: `(hb : b ∈ R⁰) (m : ℤ) : invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b^4)`
- What: The reduced invariant identity at `s=1`, assuming `b` a non-zero-divisor.
- How: cancel `b` via `mul_cancel_right_mem_nonZeroDivisors`, `convert invar_normEDS 1 m 2` then `invarNum_normEDS_two`/`invarDenom_normEDS_two`.
- Hypotheses: `b ∈ R⁰`.
- Uses from project: [invarNum, invarDenom, normEDS, invar_normEDS, invarNum_normEDS_two, invarDenom_normEDS_two]
- Used by: invar₂_normEDS
- Visibility: private
- Lines: 1478-1482 (proof 3 lines)
- Notes: none

### lemma invar₂_normEDS
- Type: `{m : ℤ} : invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b^4)`
- What: Unconditional reduced-invariant identity at `s=1`.
- How: `aeval`-transfer of `invar₂_normEDS_of_mem_nonZeroDivisors` at universal parameters with `X_ne_zero`, then rewrite the composite back to `normEDS b c d`.
- Hypotheses: none.
- Uses from project: [invarNum, invarDenom, normEDS, invar₂_normEDS_of_mem_nonZeroDivisors, universalNormEDS, map_invarNum, map_invarDenom, map_normEDS]
- Used by: redInvar_normEDS_of_mem_nonZeroDivisors
- Visibility: public
- Lines: 1484-1493 (proof 7 lines)
- Notes: none

### lemma redInvar_normEDS_of_mem_nonZeroDivisors (private)
- Type: `(hb : b ∈ R⁰) (hc : c ∈ R⁰) (m : ℤ) : redInvarNum b c d m = redInvarDenom b c d m * (d + b^4)`
- What: Reduced-invariant identity (numerator/denominator form), assuming `b, c` non-zero-divisors.
- How: cancel `b` and `c` via `mul_cancel_right_mem_nonZeroDivisors`, rewrite by `invarNum_eq_redInvarNum_mul`, `invar₂_normEDS`, `invarDenom_eq_redInvarDenom_mul`, `ring`.
- Hypotheses: `b ∈ R⁰`, `c ∈ R⁰`.
- Uses from project: [redInvarNum, redInvarDenom, invarNum_eq_redInvarNum_mul, invar₂_normEDS, invarDenom_eq_redInvarDenom_mul]
- Used by: redInvar_normEDS
- Visibility: private
- Lines: 1495-1500 (proof 4 lines)
- Notes: none

### lemma redInvar_normEDS
- Type: `(m : ℤ) : redInvarNum b c d m = redInvarDenom b c d m * (d + b^4)`
- What: Unconditional reduced-invariant identity.
- How: `aeval`-transfer of `redInvar_normEDS_of_mem_nonZeroDivisors` at universal parameters with `X_ne_zero`.
- Hypotheses: none.
- Uses from project: [redInvarNum, redInvarDenom, redInvar_normEDS_of_mem_nonZeroDivisors, map_redInvarNum, map_redInvarDenom]
- Used by: unused in file
- Visibility: public
- Lines: 1502-1509 (proof 6 lines)
- Notes: none

### def complEDS' (root-level, §ComplEDS)
- Type: `(b c d : R) (k : ℤ) : ℕ → R` with `0↦0, 1↦1` and a parity-split well-founded recursion on `n+2`
- What: The complement sequence `Wᶜ : ℤ×ℕ → R` witnessing `W(k) ∣ W(n·k)` for `normEDS`; agrees with `complEDS₂` at `n=2`. Built directly from `normEDS`/`complEDS₂` (not via `EllSequence.compl`).
- How: well-founded recursion with `Nat.div_lt_self` decreasing obligation.
- Hypotheses: none.
- Uses from project: [normEDS, complEDS₂]
- Used by: complEDS'_zero, complEDS'_one, complEDS'_even, complEDS'_odd, complEDS(root), map_complEDS'
- Visibility: public
- Lines: 1528-1536 (def body ~9 lines)
- Notes: Distinct from `EllSequence.compl'`. This is the root-level `complEDS'` (the file's `## Main definitions` `complEDS'`).

### lemma complEDS'_zero (@[simp], root-level)
- Type: `: complEDS' b c d k 0 = 0`
- What: Value 0 at 0.
- How: `simp [complEDS'.eq_def]`.
- Hypotheses: none.
- Uses from project: [complEDS'(root)]
- Used by: map_complEDS'(root)
- Visibility: public
- Lines: 1538-1540 (proof 1 line)
- Notes: none

### lemma complEDS'_one (@[simp], root-level)
- Type: `: complEDS' b c d k 1 = 1`
- What: Value 1 at 1.
- How: `simp [complEDS'.eq_def]`.
- Hypotheses: none.
- Uses from project: [complEDS'(root)]
- Used by: map_complEDS'(root)
- Visibility: public
- Lines: 1542-1544 (proof 1 line)
- Notes: none

### lemma complEDS'_even (root-level)
- Type: `(m : ℕ) : complEDS' b c d k (2*(m+1)) = complEDS' b c d k (m+1) * complEDS₂ b c d ((m+1)*k)`
- What: Even-step recurrence for the root-level `complEDS'`.
- How: rewrite `2*(m+1)=2*m+2`, unfold with `dif_pos (even_two_mul)`, `mul_div_cancel_left`, `Nat.cast_succ`.
- Hypotheses: none.
- Uses from project: [complEDS'(root), complEDS₂]
- Used by: complEDS_even, map_complEDS'(root)
- Visibility: public
- Lines: 1546-1549 (proof 2 lines)
- Notes: none

### lemma complEDS'_odd (root-level)
- Type: `(m : ℕ) : complEDS' b c d k (2*(m+1)+1) = (two-term expression in complEDS' and normEDS at ((m+2)k±1), ((m+1)k±1))`
- What: Odd-step recurrence for the root-level `complEDS'`.
- How: rewrite `2*(m+1)+1=2*m+3`, unfold with `dif_neg (not_even_two_mul_add_one)`, `Nat.mul_add_div`.
- Hypotheses: none.
- Uses from project: [complEDS'(root), normEDS]
- Used by: complEDS_odd, map_complEDS'(root)
- Visibility: public
- Lines: 1551-1557 (proof 2 lines)
- Notes: none

### def complEDS (root-level, §ComplEDS)
- Type: `(b c d : R) (k : ℤ) (n : ℤ) : R := n.sign * complEDS' b c d k n.natAbs`
- What: The ℤ-indexed complement sequence `Wᶜ : ℤ×ℤ → R` witnessing `W(k) ∣ W(n·k)`, extending root-level `complEDS'` to negatives.
- How: Plain definition.
- Hypotheses: none.
- Uses from project: [complEDS'(root)]
- Used by: complEDS_ofNat, complEDS_zero, complEDS_one, complEDS_neg, complEDS_even, complEDS_odd, map_complEDS_root
- Visibility: public
- Lines: 1559-1564 (def body 1 line)
- Notes: Distinct from `EllSequence.complEDS`; the two share the spelling but live in different namespaces (`section … end` closes the `@[expose] public` block before this one to avoid ambiguity, per the comment at line 1517).

### lemma complEDS_ofNat (@[simp], root-level)
- Type: `(n : ℕ) : complEDS b c d k n = complEDS' b c d k n`
- What: On naturals root-level `complEDS` agrees with `complEDS'`.
- How: case `n=0` by `simp`; else `Int.sign_natCast_of_ne_zero`, `Int.natAbs_natCast`.
- Hypotheses: none.
- Uses from project: [complEDS(root), complEDS'(root)]
- Used by: complEDS_even, complEDS_odd
- Visibility: public
- Lines: 1566-1570 (proof 3 lines)
- Notes: none

### lemma complEDS_zero (@[simp], root-level)
- Type: `: complEDS b c d k 0 = 0`
- What: Value 0 at 0.
- How: `simp only [complEDS, Int.sign_zero, ...]`.
- Hypotheses: none.
- Uses from project: [complEDS(root)]
- Used by: complEDS_even, complEDS_odd
- Visibility: public
- Lines: 1572-1574 (proof 1 line)
- Notes: none

### lemma complEDS_one (@[simp], root-level)
- Type: `: complEDS b c d k 1 = 1`
- What: Value 1 at 1.
- How: `simp only [complEDS, Int.sign_one, ..., complEDS'_one]`.
- Hypotheses: none.
- Uses from project: [complEDS(root), complEDS'_one]
- Used by: complEDS_odd
- Visibility: public
- Lines: 1576-1578 (proof 1 line)
- Notes: none

### lemma complEDS_neg (@[simp], root-level)
- Type: `(n : ℤ) : complEDS b c d k (-n) = -complEDS b c d k n`
- What: Root-level `complEDS` is odd in `n`.
- How: `simp only [complEDS, Int.sign_neg, Int.natAbs_neg, ...]`.
- Hypotheses: none.
- Uses from project: [complEDS(root)]
- Used by: complEDS_even, complEDS_odd
- Visibility: public
- Lines: 1580-1582 (proof 1 line)
- Notes: none

### lemma complEDS_even (root-level)
- Type: `(m : ℤ) : complEDS b c d k (2*m) = complEDS b c d k m * complEDS₂ b c d (m*k)`
- What: Even-step recurrence for root-level `complEDS`.
- How: `Int.negInduction`; `nat` case via `complEDS'_even` after `norm_cast`; `neg` case via `complEDS_neg`, `complEDS₂_neg`.
- Hypotheses: none.
- Uses from project: [complEDS(root), complEDS₂, complEDS'_even, complEDS_neg, complEDS_zero, complEDS₂_zero, complEDS₂_neg, complEDS_ofNat]
- Used by: unused in file
- Visibility: public
- Lines: 1584-1592 (proof 6 lines)
- Notes: none

### lemma complEDS_odd (root-level)
- Type: `(m : ℤ) : complEDS b c d k (2*m+1) = (two-term expression in complEDS at m, m+1 and normEDS at ((m+1)k±1), (mk±1))`
- What: Odd-step recurrence for root-level `complEDS`.
- How: `Int.negInduction`; `nat` case via `complEDS'_odd` after `norm_cast`; `neg` case rewrites negated arguments and uses `complEDS_neg`, `normEDS_neg`, IH, `ring`.
- Hypotheses: none.
- Uses from project: [complEDS(root), normEDS, complEDS'_odd, complEDS_neg, complEDS_zero, complEDS_one, normEDS_neg, complEDS_ofNat]
- Used by: unused in file
- Visibility: public
- Lines: 1594-1611 (proof 16 lines)
- Notes: none

### def complEDSRec' (@[elab_as_elim], noncomputable)
- Type: strong even/odd recursion principle for the root-level complement sequence
- What: `P n` for all `n` given `P 0`, `P 1`, and even/odd strong-recursion steps (lookback `2*(m+1)`, `2*(m+1)+1`).
- How: built on `Nat.evenOddStrongRec`.
- Hypotheses: base cases and strong even/odd steps.
- Uses from project: []
- Used by: complEDSRec, map_complEDS'(root)
- Visibility: public (noncomputable)
- Lines: 1613-1623 (body 2 lines)
- Notes: none

### def complEDSRec (@[elab_as_elim], noncomputable)
- Type: (non-strong) even/odd recursion principle for the root-level complement sequence
- What: `P n` for all `n` given base cases and finite-lookback even/odd steps.
- How: reduces to `complEDSRec'` with `linarith` bounds.
- Hypotheses: base cases and finite-lookback even/odd steps.
- Uses from project: [complEDSRec']
- Used by: map_complEDS'(root)
- Visibility: public (noncomputable)
- Lines: 1625-1637 (body 2 lines)
- Notes: none

### lemma map_complEDS₂ (@[simp], §Map, root-level)
- Type: `(n : ℤ) : f (complEDS₂ b c d n) = complEDS₂ (f b) (f c) (f d) n`
- What: Ring homs commute with `complEDS₂` (here `f : R →+* S`).
- How: `simp [complEDS₂, apply_ite f, map_preNormEDS, map_pow]`.
- Hypotheses: `f` a ring hom.
- Uses from project: [complEDS₂, map_preNormEDS]
- Used by: map_complEDS'(root)
- Visibility: public
- Lines: 1646-1649 (proof 1 line)
- Notes: This duplicates the commutation logic of the earlier `EllSequence`-namespace map lemmas but for the root-level `complEDS₂`; restated after the `@[expose]` block closes.

### lemma map_complEDS' (@[simp], §Map, root-level)
- Type: `(k : ℤ) (n : ℕ) : f (complEDS' b c d k n) = complEDS' (f b) (f c) (f d) k n`
- What: Ring homs commute with root-level `complEDS'`.
- How: `complEDSRec'` induction; recursive case `simp` with `complEDS'_even/odd`, `map_*`, re-apply IH.
- Hypotheses: `f` a ring hom.
- Uses from project: [complEDS'(root), complEDS'_zero, complEDS'_one, complEDS'_even, complEDS'_odd, complEDSRec', map_normEDS, map_complEDS₂]
- Used by: map_complEDS_root
- Visibility: public
- Lines: 1651-1660 (proof 9 lines)
- Notes: none

### lemma map_complEDS_root (@[simp], §Map, root-level)
- Type: `(k n : ℤ) : f (complEDS b c d k n) = complEDS (f b) (f c) (f d) k n`
- What: Ring homs commute with root-level `complEDS`.
- How: `simp [complEDS]` (reducing to `map_complEDS'`).
- Hypotheses: `f` a ring hom.
- Uses from project: [complEDS(root), map_complEDS'(root)]
- Used by: unused in file
- Visibility: public
- Lines: 1662-1665 (proof 1 line)
- Notes: none

---

## File Summary

**Total declarations: 161**
- **defs / recursion principles / inductive: 33** — `addMulSub`, `rel₄`, `net`, `Rel₃`, `IsEllSequence`, `invarNum`, `invarDenom`, `StrictAnti₄`, `HaveSameParity₄`, `avg₄`, `addMulSub₄`, `rel₆` (abbrev), `Rel₄OfValid`, `OddRec`, `EvenRec`, `dMin`, `cMin`, `relFin4`, `IsDivSequence`, `IsEllDivSequence`, `preNormEDS'`, `preNormEDS`, `complEDS₂`, `normEDS`, `normEDSRec'`, `normEDSRec`, `compl₂EDSAux`, `compl₂EDS`, `EllSequence.compl'`, `EllSequence.compl`, `EllSequence.complEDS`, `redInvarNum`, `redInvarDenom`, `universalNormEDS`, `Param` (inductive), `complEDS'`(root), `complEDS`(root), `complEDSRec'`, `complEDSRec`. (Count above folds `rel₆` abbrev + `Param` inductive into the 33; recursion principles are `noncomputable def`s.)
- **lemmas + theorems: ~128**
- **instances: 0** (no `instance` declarations; the universe/`variable` setup uses existing instances).

**Key API (used by ≥3 in-file decls):**
- `addMulSub` (def) — ubiquitous building block.
- `rel₄` (def) — central four-index relation.
- `net` (def) — Stange-net form.
- `Rel₃`, `IsEllSequence`, `IsDivSequence`, `IsEllDivSequence` (defs).
- `HaveSameParity₄`, `StrictAnti₄`, `avg₄`, `Rel₄OfValid`, `OddRec`, `EvenRec`, `dMin`, `cMin` (the `rel₄` induction scaffold).
- `rel₆` (abbrev).
- `preNormEDS'`, `preNormEDS`, `preNormEDS_neg`, `normEDS`, and seed lemmas `normEDS_one/two/three/four`.
- `complEDS₂`, `compl₂EDS`, `compl₂EDSAux`, `EllSequence.complEDS`, `complEDS'`(root), `complEDS`(root).
- `IsEllSequence.normEDS`, `normEDS_mul_complEDS`, `normEDS_mul_compl₂EDS`, `normEDS_six_eq_mul`.
- `universalNormEDS`, `Param`, `map_normEDS`, `map_preNormEDS`, `map_compl₂EDS`.
- `IsEllSequence.neg`, `IsEllSequence.zero`, `IsEllSequence.oddRec`, `IsEllSequence.evenRec`, `IsEllSequence.ext`, `rel₄_of_oddRec_evenRec`, `rel₄_of_anti_oddRec_evenRec`, `rel₄_of_min₂`.

**Unused-in-file declarations (no in-file consumer; many are public API or terminal results):**
`net_add_sub_iff`, `addMulSub_two_zero`, `addMulSub_three_one`, `addMulSub_sq_mul_rel₄_eq₉`, `isEllDivSequence_id`, `IsEllDivSequence.smul`, `IsEllDivSequence.map`, `IsEllSequence.zero'`, `IsEllSequence.invar`, `preNormEDS_zero`, `preNormEDS_three`, `normEDS_def`, `normEDS_ofNat`, `normEDS_dvd_normEDS_two_mul`, `complEDS₂_one`, `complEDS₂_two`, `complEDS₂_three`, `complEDS₂_four`, all five `compl₂EDSAux_{zero,one,neg_one,two,neg_two}`, `compl₂EDSAux_neg`, `compl₂EDS_zero`, `compl₂EDS_one`, `compl₂EDS_two`, `normEDS_dvd_two_mul`, `compl₂EDS_eq_aeval`, `complEDS_eq_aeval`, `IsEllDivSequence.eq_normEDS`, `compl₂EDS_eq_redInvarNum_sub`, `redInvarDenom_zero`, `redInvarDenom_one`, `redInvarDenom_two`, `IsEllDivSequence.normEDS`, `IsEllSequence.isEllDivSequence_of_dvd`, `rel₄_normEDS`, `redInvar_normEDS`, `compl₂EDS_two_three_two`, `complEDS_even`(root), `complEDS_odd`(root), `map_complEDS_root`. (These are exported for downstream Nagell-Lutz / division-polynomial files; "unused in file" ≠ dead.)

**Declarations with `sorry`: none.**

**Declarations with `set_option` (`allowUnsafeReducibility true` + local `attribute [local reducible] Nat.rawCast Mathlib.Meta.NormNum.instAddMonoidWithOne`):**
`invar_of_net`, `HaveSameParity₄.addMulSub_transf`, `rel₃_iff_evenRec`, `rel₄_iff_evenRec`. (4 declarations.)

**Proofs > 50 lines (OVER-50): 0.**

**Proofs 30-50 lines: 0.**
(Longest proof bodies: `rel₄_of_anti_oddRec_evenRec` ~25 lines, `mul_compl_eq_apply_mul_of_mem_nonZeroDivisors` ~23 lines, `invarDenom_eq_redInvarDenom_mul` ~21 lines, `rel₄_of_min₂` ~17 lines, `preNormEDS_odd` / `complEDS_odd`(root) ~16 lines, `rel₄_of_oddRec_evenRec` ~15 lines, `IsEllSequence.ext` ~14 lines, `IsEllSequence.neg` ~13 lines — all under 30.)

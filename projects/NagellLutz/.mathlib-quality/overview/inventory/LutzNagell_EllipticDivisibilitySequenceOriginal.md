# Inventory: `LutzNagell/EllipticDivisibilitySequenceOriginal.lean`

File path: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean` (1573 lines).

Module-level: `@[expose] public section`; `variable {R S} [CommRing R] [CommRing S] (W : ℤ → R)`, `{F} [FunLike F R S] [RingHomClass F R S] (f : F)`; `open scoped nonZeroDivisors`. Defines elliptic / divisibility / EDS sequences and the normalised EDS `normEDS`, culminating in `IsEllDivSequence.normEDS`. Heavily a port of mathlib's `EllipticDivisibilitySequence` with extended `rel₄`/`net`/`compl` API.

---

### def addMulSub
- Type: `(m n : ℤ) : R := W ((m + n).tdiv 2) * W ((m - n).tdiv 2)`
- What: The building block `W((m+n)/2) * W((m-n)/2)` of elliptic relations, for same-parity `m,n`.
- How: Direct definition using truncated division `Int.tdiv _ 2` (so `(-m).tdiv 2 = -(m.tdiv 2)`, making sign lemmas unconditional).
- Hypotheses: none.
- Uses from project: []
- Used by: rel₄, net_eq_rel₄, addMulSub_two_zero, addMulSub_three_one, addMulSub_even, addMulSub_odd, addMulSub_same, addMulSub_neg₀, addMulSub_neg₁, addMulSub_abs₀, addMulSub_abs₁, addMulSub_swap, addMulSub₄, addMulSub_transf, rel₆, addMulSub_mem_nonZeroDivisors, map_addMulSub (and indirectly most of the file)
- Visibility: public
- Lines: 91-97 (def, ~1 line body)
- Notes: none

### def rel₄
- Type: `(a b c d : ℤ) : R := addMulSub W a b * addMulSub W c d - addMulSub W a c * addMulSub W b d + addMulSub W a d * addMulSub W b c`
- What: The four-index elliptic relation as an alternating sum over the three pairings of four same-parity indices.
- How: Direct definition in terms of `addMulSub`.
- Hypotheses: none.
- Uses from project: [addMulSub]
- Used by: net_eq_rel₄, rel₃_iff₄, rel₄_iff_evenRec, rel₆, HaveSameParity₄.rel₄_eq_net, HaveSameParity₄.rel₄_transf, relFin4, rel₄ swap/same lemmas, map_rel₄, IsEllSequence.rel₄, rel₄_normEDS
- Visibility: public
- Lines: 99-104 (def, ~3 lines)
- Notes: none

### def net
- Type: `(p q r s : ℤ) : R := W (p+q+s)*W (p-q)*W (r+s)*W r - W (p+r+s)*W (p-r)*W (q+s)*W q + W (q+r+s)*W (q-r)*W (p+s)*W p`
- What: Stange's elliptic-net defining expression (sign-adjusted), an alternative to `rel₄` symmetric only in the first three indices.
- How: Direct definition; signs/order tweaked vs Stange's paper so equivalence with `rel₄` is unconditional.
- Hypotheses: none.
- Uses from project: []
- Used by: net_eq_rel₄, invar_of_net, net_add_sub_iff, HaveSameParity₄.rel₄_eq_net, map_net, IsEllSequence.net, net_normEDS
- Visibility: public
- Lines: 106-117 (def, 3 lines)
- Notes: none

### lemma net_eq_rel₄
- Type: `{p q r s : ℤ} : net W p q r s = rel₄ W (2*p+s) (2*q+s) (2*r+s) s`
- What: Expresses the net relation as a `rel₄` with shifted, same-parity arguments.
- How: `simp_rw` unfolding both sides plus `Int.mul_tdiv_cancel_left _ two_ne_zero`, then `ring`.
- Hypotheses: none.
- Uses from project: [net, rel₄, addMulSub]
- Used by: HaveSameParity₄.rel₄_eq_net, map_net
- Visibility: public
- Lines: 119-125 (proof ~5 lines)
- Notes: none

### def Rel₃
- Type: `(m n r : ℤ) : Prop := W (m+n)*W (m-n)*W r ^ 2 = W (m+r)*W (m-r)*W n ^ 2 - W (n+r)*W (n-r)*W m ^ 2`
- What: The three-index elliptic relation (the `d = 0` specialization of the four-index relation).
- How: Direct definition.
- Hypotheses: none.
- Uses from project: []
- Used by: IsEllSequence, rel₃_iff₄, rel₃_iff_oddRec, rel₃_iff_evenRec, IsEllSequence.zero', IsEllSequence.zero, IsEllSequence.sub_add_neg_sub_mul_eq_zero, isEllSequence_id
- Visibility: public
- Lines: 129-131 (def, 2 lines)
- Notes: none

### def IsEllSequence (`_root_`)
- Type: `: Prop := ∀ m n r : ℤ, Rel₃ W m n r`
- What: A sequence is an elliptic sequence iff `Rel₃` holds for all index triples.
- How: Direct definition.
- Hypotheses: none.
- Uses from project: [Rel₃]
- Used by: IsEllDivSequence, isEllSequence_id, IsEllSequence.smul/.map, IsEllSequence.of_oddRec_evenRec, IsEllSequence.normEDS (and the IsEllSequence namespace lemmas via `ell : IsEllSequence W`)
- Visibility: public (root namespace)
- Lines: 133-135 (def, 1 line)
- Notes: none

### def invarNum
- Type: `(s n : ℤ) : R := (W (n+2*s)*W (n-s)^2 + W (n+s)^2*W (n-2*s))*W s^2 + W n^3*W (2*s)^2`
- What: Numerator of an EDS invariant; `invarNum s n / invarDenom s n` is independent of `n`.
- How: Direct definition.
- Hypotheses: none.
- Uses from project: []
- Used by: invar_of_net, IsEllSequence.invar, invarNum_normEDS, invarNum_normEDS_two, map_invarNum, invarNum_eq_redInvarNum_mul, invar_normEDS, invar₂_normEDS_of_mem_nonZeroDivisors, invar₂_normEDS
- Visibility: public
- Lines: 137-141 (def, 2 lines)
- Notes: none

### def invarDenom
- Type: `(s n : ℤ) : R := W (n+s)*W n*W (n-s)`
- What: Denominator of the EDS invariant.
- How: Direct definition.
- Hypotheses: none.
- Uses from project: []
- Used by: invar_of_net, IsEllSequence.invar, invarDenom_normEDS_two, map_invarDenom, invarDenom_eq_redInvarDenom_mul, invar_normEDS, invar₂_normEDS*
- Visibility: public
- Lines: 143-144 (def, 1 line)
- Notes: none

### theorem invar_of_net
- Type: `(net_eq_zero : ∀ p q r s, net W p q r s = 0) (s m n : ℤ) : invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m`
- What: If all net relations vanish, the invariant numerator/denominator cross-products agree, i.e. the invariant is `n`-independent.
- How: `linear_combination` with an explicit combination of four `net_eq_zero` instances (`net m n s 0`, `net m n s s`, `net (m-s) (n-s) s s`, `net (n+s) n (n-s) (m-n)`) weighted by `W` factors; norm closes via `simp_rw [net]; ring_nf`.
- Hypotheses: all four-index net relations vanish for `W`.
- Uses from project: [net, invarNum, invarDenom]
- Used by: IsEllSequence.invar, invar_normEDS
- Visibility: public
- Lines: 146-153 (proof ~7 lines incl. multi-line `linear_combination`)
- Notes: none

### lemma net_add_sub_iff
- Type: `(m n : ℤ) : net W (m+n) m (m-n) n = 0 ↔ W (2*(m+n))*W (m-n)*W m*W n = (W (2*m+n)*W (2*n)*W m - W (m+2*n)*W (2*m)*W n)*W (m+n)`
- What: Rewrites the vanishing of a specific net relation as a duplication-type identity for `W(2(m+n))`.
- How: `rw [net]`, move RHS to `sub_eq_zero` form, then `ring_nf` and `simp only [Nat.rawCast]`.
- Hypotheses: none.
- Uses from project: [net]
- Used by: unused in file
- Visibility: public
- Lines: 155-160 (proof ~3 lines)
- Notes: none

### lemma addMulSub_two_zero
- Type: `: addMulSub W 2 0 = W 1 ^ 2`
- What: `addMulSub W 2 0 = W(1)²`.
- How: `(sq _).symm`.
- Hypotheses: none.
- Uses from project: [addMulSub]
- Used by: unused in file
- Visibility: public
- Lines: 162 (1 line)
- Notes: none

### lemma addMulSub_three_one
- Type: `: addMulSub W 3 1 = W 2 * W 1`
- What: `addMulSub W 3 1 = W(2)·W(1)`.
- How: `rfl`.
- Hypotheses: none.
- Uses from project: [addMulSub]
- Used by: unused in file
- Visibility: public
- Lines: 163 (1 line)
- Notes: none

### lemma addMulSub_even
- Type: `(m n : ℤ) : addMulSub W (2*m) (2*n) = W (m+n) * W (m-n)`
- What: Even-index reduction of `addMulSub`.
- How: `simp_rw` with distributivity and `Int.mul_tdiv_cancel_left _ two_ne_zero`.
- Hypotheses: none.
- Uses from project: [addMulSub]
- Used by: rel₃_iff₄
- Visibility: public
- Lines: 165-166 (proof 1 line)
- Notes: none

### lemma addMulSub_odd
- Type: `(m n : ℤ) : addMulSub W (2*m+1) (2*n+1) = W (m+n+1) * W (m-n)`
- What: Odd-index reduction of `addMulSub`.
- How: rewrite via `Int.mul_tdiv_cancel_left` after recasting both indices, then `congr`/`ring`.
- Hypotheses: none.
- Uses from project: [addMulSub]
- Used by: rel₄_iff_evenRec
- Visibility: public
- Lines: 168-171 (proof ~2 lines)
- Notes: none

### lemma addMulSub_same
- Type: `(zero : W 0 = 0) (m : ℤ) : addMulSub W m m = 0`
- What: `addMulSub W m m = 0` when `W(0) = 0`.
- How: `sub_self`, `Int.zero_tdiv`, the `zero` hypothesis, `mul_zero`.
- Hypotheses: `W 0 = 0`.
- Uses from project: [addMulSub]
- Used by: rel₄_same₀₁, rel₄_same₁₂, rel₄_same₂₃
- Visibility: public
- Lines: 173-174 (proof 1 line)
- Notes: none

### lemma addMulSub_neg₀
- Type: `(neg : ∀ k, W (-k) = -W k) (m n : ℤ) : addMulSub W (-m) n = addMulSub W m n`
- What: `addMulSub` is invariant under negating its first argument, when `W` is odd.
- How: `simp_rw` with `Int.neg_tdiv`, the oddness `neg`, then `ring`.
- Hypotheses: `W` is an odd function.
- Uses from project: [addMulSub]
- Used by: addMulSub_abs₀
- Visibility: public
- Lines: 176-178 (proof 1 line)
- Notes: none

### lemma addMulSub_neg₁
- Type: `(m n : ℤ) : addMulSub W m (-n) = addMulSub W m n`
- What: `addMulSub` is invariant under negating its second argument (unconditionally).
- How: unfold, `mul_comm`, `abel_nf`.
- Hypotheses: none.
- Uses from project: [addMulSub]
- Used by: addMulSub_abs₁, HaveSameParity₄.addMulSub_transf
- Visibility: public
- Lines: 180-181 (proof 1 line)
- Notes: none

### lemma addMulSub_abs₀
- Type: `(neg : ∀ k, W (-k) = -W k) (m n : ℤ) : addMulSub W |m| n = addMulSub W m n`
- What: `addMulSub` is invariant under taking absolute value of its first argument, when `W` is odd.
- How: `abs_choice m`, then `addMulSub_neg₀`.
- Hypotheses: `W` is odd.
- Uses from project: [addMulSub, addMulSub_neg₀]
- Used by: rel₄_abs
- Visibility: public
- Lines: 183-185 (proof 1 line)
- Notes: none

### lemma addMulSub_abs₁
- Type: `(m n : ℤ) : addMulSub W m |n| = addMulSub W m n`
- What: `addMulSub` invariant under abs of second argument.
- How: `abs_choice n`, then `addMulSub_neg₁`.
- Hypotheses: none.
- Uses from project: [addMulSub, addMulSub_neg₁]
- Used by: rel₄_abs, HaveSameParity₄.addMulSub_transf
- Visibility: public
- Lines: 187-188 (proof 1 line)
- Notes: none

### lemma addMulSub_swap
- Type: `(neg : ∀ k, W (-k) = -W k) (m n : ℤ) : addMulSub W m n = - addMulSub W n m`
- What: `addMulSub` is antisymmetric under swapping its two arguments, when `W` is odd.
- How: unfold both, `← neg_sub`, `Int.neg_tdiv`, oddness `neg`, `ring_nf`.
- Hypotheses: `W` is odd.
- Uses from project: [addMulSub]
- Used by: rel₄_swap₀₁, rel₄_swap₁₂, rel₄_swap₂₃
- Visibility: public
- Lines: 190-192 (proof 1 line)
- Notes: none

### def StrictAnti₄
- Type: `(a b c d : ℤ) : Prop := 0 ≤ d ∧ d < c ∧ c < b ∧ b < a` (section `variable (a b c d : ℤ)`)
- What: The four indices are nonnegative and strictly decreasing.
- How: Direct definition.
- Hypotheses: none.
- Uses from project: []
- Used by: HaveSameParity₄.six_le_of_strictAnti₄, HaveSameParity₄.strictAnti₄_transf, Rel₄OfValid, rel₄_fix₁_of_fix₂, rel₄_of_fix₂, rel₄_of_oddRec_evenRec
- Visibility: public
- Lines: 198-199 (def, 1 line)
- Notes: none

### def HaveSameParity₄
- Type: `(a b c d : ℤ) : Prop := a.negOnePow = b.negOnePow ∧ b.negOnePow = c.negOnePow ∧ c.negOnePow = d.negOnePow`
- What: The four indices all share the same parity (encoded via `negOnePow`).
- How: Direct definition.
- Hypotheses: none.
- Uses from project: []
- Used by: the entire `HaveSameParity₄` namespace (rel₄_eq_net, even_sum, avg₄_add_avg₄, same₀₃, abs, perm, six_le_of_strictAnti₄, addMulSub_transf, rel₄_transf, transf, strictAnti₄_transf), Rel₄OfValid, rel₄_fix₁_of_fix₂, rel₄_of_fix₂, rel₄_of_min₂, rel₄_of_oddRec_evenRec, rel₄_of_oddRec_evenRec(thm), IsEllSequence.rel₄, IsEllSequence.net, rel₄_normEDS, rel₄_normEDS
- Visibility: public
- Lines: 201-203 (def, 2 lines)
- Notes: none

### def avg₄
- Type: `(a b c d : ℤ) : ℤ := (a + b + c + d) / 2`
- What: Half the sum of the four indices.
- How: Direct definition (`Int.ediv` by 2).
- Hypotheses: none.
- Uses from project: []
- Used by: HaveSameParity₄.avg₄_add_avg₄, addMulSub_transf, rel₄_transf, transf, strictAnti₄_transf
- Visibility: public
- Lines: 205-206 (def, 1 line)
- Notes: none

### lemma HaveSameParity₄.rel₄_eq_net
- Type: `(same : ...) : rel₄ W a b c d = net W ((a-d)/2) ((b-d)/2) ((c-d)/2) d`
- What: Under same parity, `rel₄` equals a `net` relation with halved offset arguments.
- How: `net_eq_rel₄` plus `Int.two_mul_ediv_two_of_even` (three times), discharging evenness via `negOnePow_eq_iff` and the parity hypotheses.
- Hypotheses: `HaveSameParity₄ a b c d`.
- Uses from project: [rel₄, net, net_eq_rel₄, HaveSameParity₄]
- Used by: rel₄_normEDS (the final `same.rel₄_eq_net`)
- Visibility: public (namespace `HaveSameParity₄`)
- Lines: 214-218 (proof ~5 lines)
- Notes: none

### lemma HaveSameParity₄.even_sum
- Type: `(same) : Even (a + b + c + d)`
- What: Same-parity indices have an even sum.
- How: `simp_rw` with `negOnePow_eq_one_iff`, `negOnePow_add`, the parity equalities, and `units_mul_self`.
- Hypotheses: `HaveSameParity₄ a b c d`.
- Uses from project: [HaveSameParity₄]
- Used by: HaveSameParity₄.avg₄_add_avg₄
- Visibility: public (namespace)
- Lines: 220-222 (proof ~2 lines)
- Notes: none

### lemma HaveSameParity₄.avg₄_add_avg₄
- Type: `(same) : avg₄ a b c d + avg₄ a b c d = a + b + c + d`
- What: Doubling the average recovers the sum (valid since the sum is even).
- How: `← two_mul` then `Int.mul_ediv_cancel'` using `even_sum.two_dvd`.
- Hypotheses: `HaveSameParity₄ a b c d`.
- Uses from project: [avg₄, HaveSameParity₄, HaveSameParity₄.even_sum]
- Used by: HaveSameParity₄.addMulSub_transf, HaveSameParity₄.strictAnti₄_transf
- Visibility: public (namespace)
- Lines: 224-225 (proof 1 line)
- Notes: none

### lemma HaveSameParity₄.same₀₃
- Type: `(same) : a.negOnePow = d.negOnePow`
- What: First and last indices share parity (transitivity of the chain).
- How: `rw` chaining the three parity equalities.
- Hypotheses: `HaveSameParity₄ a b c d`.
- Uses from project: [HaveSameParity₄]
- Used by: rel₄_of_min₂
- Visibility: public (namespace)
- Lines: 227 (1 line)
- Notes: none

### lemma HaveSameParity₄.abs
- Type: `protected (same) : HaveSameParity₄ |a| |b| |c| |d|`
- What: Same parity is preserved under taking absolute values.
- How: `simpa [HaveSameParity₄, negOnePow_abs]`.
- Hypotheses: `HaveSameParity₄ a b c d`.
- Uses from project: [HaveSameParity₄]
- Used by: rel₄_of_oddRec_evenRec(thm) (`same.abs.perm`)
- Visibility: public (protected, namespace)
- Lines: 229-230 (proof 1 line)
- Notes: none

### lemma HaveSameParity₄.perm
- Type: `(σ : Perm (Fin 4)) : ∀ t : Fin 4 → ℤ, HaveSameParity₄ (t 0) (t 1) (t 2) (t 3) → HaveSameParity₄ (t (σ 0)) (t (σ 1)) (t (σ 2)) (t (σ 3))`
- What: Same parity is invariant under any permutation of the four indices.
- How: `Submonoid.closure_induction` over `Perm.mclosure_swap_castSucc_succ 3` generators (adjacent transpositions), `fin_cases` on the swap index handling the three base swaps.
- Hypotheses: `HaveSameParity₄` of the base tuple (passed per call); outer `same` is `include`d but argument-level.
- Uses from project: [HaveSameParity₄]
- Used by: rel₄_of_oddRec_evenRec(thm) (`same.abs.perm`)
- Visibility: public (namespace)
- Lines: 232-242 (proof ~8 lines)
- Notes: none

### lemma HaveSameParity₄.six_le_of_strictAnti₄
- Type: `(anti : StrictAnti₄ a b c d) : 6 ≤ a`
- What: A nonneg, strictly-decreasing, same-parity quadruple has top index `≥ 6`.
- How: `negOnePow_eq_iff` to get even differences, `add_two_le_iff_lt_of_even_sub` on each gap, then `linarith`.
- Hypotheses: same parity (`same`) and `StrictAnti₄`.
- Uses from project: [HaveSameParity₄, StrictAnti₄]
- Used by: rel₄_of_anti_oddRec_evenRec (the `a < 6` vacuous base case)
- Visibility: public (namespace)
- Lines: 244-249 (proof ~5 lines)
- Notes: none

### def HaveSameParity₄.addMulSub₄
- Type: `(a b c d : ℤ) : R := W ((a+b).tdiv 2) * W ((c-d).tdiv 2)`
- What: A hybrid product taking one factor from each of two `addMulSub`s.
- How: Direct definition.
- Hypotheses: none.
- Uses from project: []
- Used by: addMulSub₄_mul_addMulSub₄, addMulSub_transf, rel₄_transf (within namespace)
- Visibility: public (namespace, `variable (W)`)
- Lines: 251-253 (def, 1 line)
- Notes: none

### lemma HaveSameParity₄.addMulSub₄_mul_addMulSub₄
- Type: `: addMulSub₄ W a b c d * addMulSub₄ W c d a b = addMulSub W a b * addMulSub W c d`
- What: The two hybrid products multiply to the product of the two original `addMulSub`s.
- How: unfold and `ring`.
- Hypotheses: none.
- Uses from project: [addMulSub₄, addMulSub]
- Used by: HaveSameParity₄.rel₄_transf
- Visibility: public (namespace)
- Lines: 255-257 (proof 1 line)
- Notes: none

### lemma HaveSameParity₄.addMulSub_transf
- Type: conjunction of six identities expressing `addMulSub W (avg₄ - ·) (avg₄ - ·)` (with abs on the last) as `addMulSub₄` of permuted indices.
- What: The transformation `(a,b,c,d) → (avg-d, avg-c, avg-b, |avg-a|)` sends the six pairwise `addMulSub`s to the six hybrid `addMulSub₄` products.
- How: `simp_rw` with `addMulSub_abs₁`, `sub_add_sub_comm`, `same.avg₄_add_avg₄`, then six `ring_nf`.
- Hypotheses: `HaveSameParity₄ a b c d`.
- Uses from project: [addMulSub, addMulSub₄, avg₄, addMulSub_abs₁, HaveSameParity₄.avg₄_add_avg₄, HaveSameParity₄]
- Used by: HaveSameParity₄.rel₄_transf
- Visibility: public (namespace)
- Lines: 259-267 (proof ~2 lines)
- Notes: none

### theorem HaveSameParity₄.rel₄_transf
- Type: `: rel₄ W (avg₄-d) (avg₄-c) (avg₄-b) |avg₄-a| = rel₄ W a b c d`
- What: `rel₄` is invariant under the averaging transformation of indices.
- How: obtain the six identities from `addMulSub_transf`, `simp_rw` substituting them plus `addMulSub₄_mul_addMulSub₄` and `mul_comm`.
- Hypotheses: `HaveSameParity₄ a b c d`.
- Uses from project: [rel₄, avg₄, HaveSameParity₄, addMulSub_transf, addMulSub₄_mul_addMulSub₄]
- Used by: rel₄_of_anti_oddRec_evenRec (`← same.rel₄_transf`)
- Visibility: public (namespace)
- Lines: 269-273 (proof ~2 lines)
- Notes: none

### theorem HaveSameParity₄.transf
- Type: `: HaveSameParity₄ (avg₄-d) (avg₄-c) (avg₄-b) |avg₄-a|`
- What: The averaging transformation preserves the same-parity property.
- How: `simp_rw` with `negOnePow_abs`, `negOnePow_sub`, and the parity equalities.
- Hypotheses: `HaveSameParity₄ a b c d`.
- Uses from project: [HaveSameParity₄, avg₄]
- Used by: rel₄_of_anti_oddRec_evenRec (`same.transf`)
- Visibility: public (namespace)
- Lines: 275-277 (proof ~1 line)
- Notes: none

### theorem HaveSameParity₄.strictAnti₄_transf
- Type: `(anti : StrictAnti₄ a b c d) : StrictAnti₄ (avg₄-d) (avg₄-c) (avg₄-b) |avg₄-a|`
- What: The averaging transformation preserves strict-decreasing-nonnegativity.
- How: destruct `anti`, reduce each comparison to `sub_pos`/`abs_lt`, close with `same.avg₄_add_avg₄` and `linarith`.
- Hypotheses: same parity + `StrictAnti₄`.
- Uses from project: [StrictAnti₄, avg₄, HaveSameParity₄, HaveSameParity₄.avg₄_add_avg₄]
- Used by: rel₄_of_anti_oddRec_evenRec (`same.strictAnti₄_transf`)
- Visibility: public (namespace)
- Lines: 279-284 (proof ~3 lines)
- Notes: none

### def rel₆
- Type: `(k l a b c d : ℤ) : R := addMulSub W k l * rel₄ W a b c d`
- What: A `rel₄` multiplied by a two-index `addMulSub` "coefficient".
- How: Direct definition.
- Hypotheses: none.
- Uses from project: [addMulSub, rel₄]
- Used by: rel₆_eq₃, rel₆_eq₃', rel₆_eq₁₀, addMulSub_sq_mul_rel₄_eq₉, rel₄_fix₁_of_fix₂, rel₄_of_fix₂
- Visibility: public
- Lines: 290-291 (def, 1 line)
- Notes: none

### lemma rel₃_iff₄
- Type: `(m n r : ℤ) : Rel₃ W m n r ↔ rel₄ W (2*m) (2*n) (2*r) 0 = 0`
- What: The three-index relation is equivalent to a `rel₄` with all-even indices and final index 0.
- How: unfold `rel₄`/`Rel₃`, `simp_rw [addMulSub_even, ...]`, `convert sub_eq_zero.symm`, `ring`.
- Hypotheses: none.
- Uses from project: [Rel₃, rel₄, addMulSub_even]
- Used by: rel₄_of_anti_oddRec_evenRec, IsEllSequence.of_oddRec_evenRec
- Visibility: public
- Lines: 293-297 (proof ~3 lines)
- Notes: none

### lemma rel₆_eq₃
- Type: `(c d m n r : ℤ) : rel₆ W c d m n r c = rel₆ W m c n r c d - rel₆ W n c m r c d + rel₆ W r c m n c d`
- What: A three-free-index `rel₄` (coefficient on fixed `c,d`) expands as three `rel₄`s sharing the larger fixed index `c`.
- How: `simp_rw [rel₆, rel₄]; ring`.
- Hypotheses: none.
- Uses from project: [rel₆, rel₄]
- Used by: rel₄_fix₁_of_fix₂
- Visibility: public
- Lines: 306-308 (proof 1 line)
- Notes: none

### lemma rel₆_eq₃'
- Type: `(c d m n r : ℤ) : rel₆ W c d m n r d = rel₆ W m d n r c d - rel₆ W n d m r c d + rel₆ W r d m n c d`
- What: Same as `rel₆_eq₃` but sharing the smaller fixed index `d`.
- How: `simp_rw [rel₆, rel₄]; ring`.
- Hypotheses: none.
- Uses from project: [rel₆, rel₄]
- Used by: rel₄_fix₁_of_fix₂
- Visibility: public
- Lines: 314-316 (proof 1 line)
- Notes: none

### theorem rel₆_eq₁₀
- Type: `(c d m n r s : ℤ) : rel₆ W c d m n r s = (nine rel₆ terms) - 2 * rel₆ W m d n r s c`
- What: A four-free-index `rel₄` (with `c,d` coefficient) expands as a signed combination of ten `rel₆`s each involving a fixed index.
- How: `simp_rw [rel₆, rel₄]; ring`.
- Hypotheses: none.
- Uses from project: [rel₆, rel₄]
- Used by: rel₄_of_fix₂
- Visibility: public
- Lines: 322-328 (proof 1 line)
- Notes: none

### theorem addMulSub_sq_mul_rel₄_eq₉
- Type: `(c d m n r s : ℤ) : (addMulSub W c d)^2 * rel₄ W m n r s = (combination of addMulSub·rel₆ terms)`
- What: `addMulSub(c,d)²` times a free `rel₄` equals an explicit alternating combination of `addMulSub`-weighted `rel₆`s.
- How: `simp_rw [rel₆, rel₄]; ring`.
- Hypotheses: none.
- Uses from project: [addMulSub, rel₄, rel₆]
- Used by: unused in file
- Visibility: public
- Lines: 330-337 (proof 1 line)
- Notes: none

### def OddRec
- Type: `(m : ℤ) : Prop := W (2*m+1)*W 1^3 = W (m+2)*W m^3 - W (m-1)*W (m+1)^3`
- What: The recurrence defining odd terms of an elliptic sequence.
- How: Direct definition.
- Hypotheses: none.
- Uses from project: []
- Used by: rel₃_iff_oddRec, rel₄_of_anti_oddRec_evenRec, rel₄_of_oddRec_evenRec, IsEllSequence.of_oddRec_evenRec, IsEllSequence.oddRec, IsEllSequence.rel₄, IsEllSequence.normEDS_of_mem_nonZeroDivisors, IsEllSequence.ext
- Visibility: public
- Lines: 339-342 (def, 2 lines)
- Notes: none

### def EvenRec
- Type: `(m : ℤ) : Prop := W (2*m)*W 2*W 1^2 = W m*(W (m-1)^2*W (m+2) - W (m-2)*W (m+1)^2)`
- What: The recurrence defining even terms of an elliptic sequence.
- How: Direct definition.
- Hypotheses: none.
- Uses from project: []
- Used by: rel₃_iff_evenRec, rel₄_iff_evenRec, rel₄_of_anti_oddRec_evenRec, rel₄_of_oddRec_evenRec, IsEllSequence.of_oddRec_evenRec, IsEllSequence.evenRec, IsEllSequence.rel₄, IsEllSequence.normEDS_of_mem_nonZeroDivisors, IsEllSequence.ext
- Visibility: public
- Lines: 344-347 (def, 2 lines)
- Notes: none

### lemma rel₃_iff_oddRec
- Type: `(m : ℤ) : Rel₃ W (m+1) m 1 ↔ OddRec W m`
- What: The specific `Rel₃ (m+1) m 1` is exactly the odd recurrence.
- How: unfold both, `ring_nf`.
- Hypotheses: none.
- Uses from project: [Rel₃, OddRec]
- Used by: rel₄_of_anti_oddRec_evenRec, IsEllSequence.oddRec
- Visibility: public
- Lines: 349-350 (proof 1 line)
- Notes: none

### lemma rel₃_iff_evenRec
- Type: `(m : ℤ) : Rel₃ W (m+1) (m-1) 1 ↔ EvenRec W m`
- What: The specific `Rel₃ (m+1) (m-1) 1` is exactly the even recurrence.
- How: unfold both, `ring_nf`, `simp only [Nat.rawCast]`.
- Hypotheses: none.
- Uses from project: [Rel₃, EvenRec]
- Used by: IsEllSequence.evenRec
- Visibility: public
- Lines: 352-353 (proof 1 line)
- Notes: none

### lemma rel₄_iff_evenRec
- Type: `(m : ℤ) : rel₄ W (2*m+1) (2*m-1) 3 1 = 0 ↔ EvenRec W m`
- What: A specific odd-index `rel₄` equals 0 iff the even recurrence holds.
- How: `iff_comm`, rewrite `2m-1 = 2(m-1)+1`, `convert_to` a `rel₄` of canonical odd form, `simp_rw [rel₄, addMulSub_odd]; ring_nf`.
- Hypotheses: none.
- Uses from project: [rel₄, EvenRec, addMulSub_odd]
- Used by: rel₄_of_anti_oddRec_evenRec
- Visibility: public
- Lines: 355-358 (proof ~3 lines)
- Notes: none

### def dMin
- Type: `(a : ℤ) : ℤ := if Even a then 0 else 1`
- What: Minimal valid fourth index given first index `a` (0 if `a` even, 1 if odd).
- How: Direct definition.
- Hypotheses: none.
- Uses from project: []
- Used by: cMin, dMin_nonneg, dMin_lt_cMin, negOnePow_cMin_eq_dMin, negOnePow_dMin, addMulSub_mem_nonZeroDivisors, dMin_le, Rel₄OfValid lemmas, rel₄_of_min₂, rel₄_of_anti_oddRec_evenRec
- Visibility: public
- Lines: 360-361 (def, 1 line)
- Notes: none

### def cMin
- Type: `(a : ℤ) : ℤ := dMin a + 2`
- What: Minimal valid third index given `a` (i.e. `dMin a + 2`).
- How: Direct definition.
- Hypotheses: none.
- Uses from project: [dMin]
- Used by: dMin_lt_cMin, negOnePow_cMin_eq_dMin, negOnePow_cMin, addMulSub_mem_nonZeroDivisors, rel₄_of_min₂, rel₄_of_anti_oddRec_evenRec
- Visibility: public
- Lines: 362-363 (def, 1 line)
- Notes: none

### lemma dMin_nonneg
- Type: `(a : ℤ) : 0 ≤ dMin a`
- What: `dMin a ≥ 0`.
- How: `rw [dMin]; split_ifs <;> decide`.
- Hypotheses: none.
- Uses from project: [dMin]
- Used by: rel₄_of_min₂
- Visibility: public
- Lines: 365 (1 line)
- Notes: none

### lemma dMin_lt_cMin
- Type: `(a : ℤ) : dMin a < cMin a`
- What: `dMin a < cMin a`.
- How: `lt_add_of_pos_right _ zero_lt_two`.
- Hypotheses: none.
- Uses from project: [dMin, cMin]
- Used by: rel₄_of_min₂
- Visibility: public
- Lines: 367 (1 line)
- Notes: none

### lemma negOnePow_cMin_eq_dMin
- Type: `(a : ℤ) : (cMin a).negOnePow = (dMin a).negOnePow`
- What: `cMin a` and `dMin a` have the same parity.
- How: `rw [cMin, Int.negOnePow_add]; exact mul_one _`.
- Hypotheses: none.
- Uses from project: [cMin, dMin]
- Used by: negOnePow_cMin, rel₄_of_min₂
- Visibility: public
- Lines: 369-370 (proof 1 line)
- Notes: none

### lemma negOnePow_dMin
- Type: `(a : ℤ) : (dMin a).negOnePow = a.negOnePow`
- What: `dMin a` has the same parity as `a`.
- How: `rw [dMin]; split_ifs`, using `Int.negOnePow_even`/`negOnePow_odd`.
- Hypotheses: none.
- Uses from project: [dMin]
- Used by: negOnePow_cMin, rel₄_of_fix₂, rel₄_of_min₂
- Visibility: public
- Lines: 372-375 (proof ~3 lines)
- Notes: none

### lemma negOnePow_cMin
- Type: `(a : ℤ) : (cMin a).negOnePow = a.negOnePow`
- What: `cMin a` has the same parity as `a`.
- How: chain `negOnePow_cMin_eq_dMin` and `negOnePow_dMin`.
- Hypotheses: none.
- Uses from project: [cMin, negOnePow_cMin_eq_dMin, negOnePow_dMin]
- Used by: rel₄_of_min₂
- Visibility: public
- Lines: 377-378 (proof 1 line)
- Notes: none

### lemma addMulSub_mem_nonZeroDivisors
- Type: `(one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰) (a : ℤ) : addMulSub W (cMin a) (dMin a) ∈ R⁰` (`variable {W}`)
- What: The "minimal" coefficient `addMulSub W (cMin a) (dMin a)` is a non-zero-divisor when `W 1, W 2` are.
- How: `rw [cMin, dMin]; split_ifs`, then `mul_mem` of the appropriate non-zero-divisor terms.
- Hypotheses: `W 1, W 2 ∈ R⁰`.
- Uses from project: [addMulSub, cMin, dMin]
- Used by: rel₄_of_min₂
- Visibility: public (after `variable {W}`)
- Lines: 381-383 (proof 1 line)
- Notes: none

### lemma dMin_le
- Type: `{a b : ℤ} (same : a.negOnePow = b.negOnePow) (h : 0 ≤ b) : dMin a ≤ b`
- What: `dMin a` is a lower bound among nonnegative integers of the same parity as `a`.
- How: `rw [dMin]; split_ifs`, in the odd case using `negOnePow_eq_one_iff` to exclude `b = 0`.
- Hypotheses: `a,b` same parity; `0 ≤ b`.
- Uses from project: [dMin]
- Used by: rel₄_of_min₂
- Visibility: public
- Lines: 385-387 (proof ~2 lines)
- Notes: none

### def Rel₄OfValid
- Type: `(a b c d : ℤ) : Prop := HaveSameParity₄ a b c d → StrictAnti₄ a b c d → rel₄ W a b c d = 0` (`variable (W)`)
- What: `rel₄` vanishes whenever the four indices are nonnegative, same-parity, strictly decreasing.
- How: Direct definition.
- Hypotheses: none.
- Uses from project: [HaveSameParity₄, StrictAnti₄, rel₄]
- Used by: rel₄_fix₁_of_fix₂, rel₄_of_fix₂, rel₄_of_min₂, rel₄_of_anti_oddRec_evenRec
- Visibility: public
- Lines: 393-397 (def, 2 lines)
- Notes: none

### lemma rel₄_fix₁_of_fix₂
- Type: `(b c : ℤ) : Rel₄OfValid W a b c c₀ ∧ (c₀ < c → Rel₄OfValid W a b c d₀)` (section hyps `par le lt rel mem`)
- What: From validity of all `(a',b,c₀,d₀)` with `a'<a`, derive validity of `(a,b,c,c₀)` and (conditionally) `(a,b,c,d₀)`.
- How: cancel the non-zero-divisor coefficient (`mem`), rewrite via `rel₆`, `rel₆_eq₃`/`rel₆_eq₃'`, apply hypothesis `rel` thrice, discharge parity/order side goals with `linarith` and `HaveSameParity₄`.
- Hypotheses: `c₀,d₀` same parity (`par`), `0 ≤ d₀` (`le`), `d₀ < c₀` (`lt`), recursive validity (`rel`), `addMulSub W c₀ d₀ ∈ R⁰` (`mem`).
- Uses from project: [Rel₄OfValid, rel₆, rel₆_eq₃, rel₆_eq₃', HaveSameParity₄, addMulSub]
- Used by: rel₄_of_fix₂, rel₄_of_min₂
- Visibility: public
- Lines: 406-416 (proof ~9 lines)
- Notes: none

### lemma rel₄_of_fix₂
- Type: `(b c d : ℤ) (hc : c₀ < d) (par' : d.negOnePow = d₀.negOnePow) : Rel₄OfValid W a b c d`
- What: From recursive validity (fixed `c₀,d₀`), derive validity of fully general `(a,b,c,d)` (subject to order/parity).
- How: cancel `mem`, `rel₆_eq₁₀`, then rewrite the ten terms using `rel₄_fix₁_of_fix₂` (both projections) and `rel` directly; discharge ten parity/order side goals via `HaveSameParity₄` + `linarith`.
- Hypotheses: `par, le, lt, rel, mem`, plus `c₀ < d`, `d` same parity as `d₀`.
- Uses from project: [Rel₄OfValid, rel₆, rel₆_eq₁₀, rel₄_fix₁_of_fix₂, HaveSameParity₄]
- Used by: rel₄_of_min₂
- Visibility: public
- Lines: 421-431 (proof ~9 lines)
- Notes: none

### theorem rel₄_of_min₂
- Type: `(one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰) (rel : ∀ {a' b}, a' ≤ a → Rel₄OfValid W a' b (cMin a) (dMin a)) (b c d : ℤ) : Rel₄OfValid W a b c d`
- What: Specializing fixed indices to `cMin a, dMin a` and combining the previous lemmas removes the order conditions, giving full validity from the minimal recursive hypothesis.
- How: case split on whether `cMin a < d`; either `rel₄_of_fix₂`, or `rel₄_fix₁_of_fix₂`, with the boundary cases forcing `dMin a = d` and `cMin a = c` via `dMin_le`, `add_two_le_iff_lt_of_even_sub`, `negOnePow_cMin`/`negOnePow_dMin`.
- Hypotheses: `W 1, W 2 ∈ R⁰`; recursive validity at the minimal fixed indices.
- Uses from project: [Rel₄OfValid, cMin, dMin, negOnePow_cMin_eq_dMin, dMin_nonneg, dMin_lt_cMin, addMulSub_mem_nonZeroDivisors, negOnePow_dMin, rel₄_of_fix₂, rel₄_fix₁_of_fix₂, dMin_le, negOnePow_cMin, HaveSameParity₄.same₀₃]
- Used by: rel₄_of_anti_oddRec_evenRec
- Visibility: public
- Lines: 435-451 (proof ~15 lines)
- Notes: none

### theorem rel₄_of_anti_oddRec_evenRec
- Type: `(one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰) (oddRec : ∀ m ≥ 2, OddRec W m) (evenRec : ∀ m ≥ 3, EvenRec W m) : ∀ ⦃a b c d⦄, Rel₄OfValid W a b c d`
- What: The main induction: under non-zero-divisor first terms and the odd/even recurrences, every nonneg same-parity strictly-decreasing `rel₄` vanishes.
- How: `Int.strongRec` on `a` from base 6 (below 6 the conclusion is vacuous via `six_le_of_strictAnti₄`); inductive step reduces to the minimal case via `rel₄_of_min₂`, then sub-cases use the inductive hypothesis, `HaveSameParity₄.rel₄_transf`/`transf`/`strictAnti₄_transf`, and finally `rel₃_iff₄`+`rel₃_iff_oddRec`/`rel₄_iff_evenRec` to invoke `oddRec`/`evenRec`.
- Hypotheses: `W 1, W 2 ∈ R⁰`; `OddRec` for `m ≥ 2`; `EvenRec` for `m ≥ 3`.
- Uses from project: [Rel₄OfValid, HaveSameParity₄.six_le_of_strictAnti₄, rel₄_of_min₂, OddRec, EvenRec, HaveSameParity₄.rel₄_transf, HaveSameParity₄.transf, HaveSameParity₄.strictAnti₄_transf, cMin, dMin, rel₃_iff₄, rel₃_iff_oddRec, rel₄_iff_evenRec]
- Used by: rel₄_of_oddRec_evenRec
- Visibility: public
- Lines: 454-484 (proof ~30 lines)
- Notes: long(30-50) — ~31-line proof body; the central inductive argument.

### lemma rel₄_abs
- Type: `{m n r s : ℤ} : rel₄ W |m| |n| |r| |s| = rel₄ W m n r s` (section `variable (neg : ∀ k, W (-k) = -W k)`)
- What: `rel₄` is invariant under taking absolute values of all indices (for odd `W`).
- How: `simp_rw [rel₄, addMulSub_abs₀ W neg, addMulSub_abs₁]`.
- Hypotheses: `W` is odd.
- Uses from project: [rel₄, addMulSub_abs₀, addMulSub_abs₁]
- Used by: rel₄_of_oddRec_evenRec(thm)
- Visibility: public
- Lines: 493-494 (proof 1 line)
- Notes: none

### lemma rel₄_swap₀₁
- Type: `{m n r s} : rel₄ W m n r s = - rel₄ W n m r s`
- What: Swapping the first two indices negates `rel₄` (odd `W`).
- How: `simp_rw [rel₄, addMulSub_swap W neg n m]; ring`.
- Hypotheses: `W` odd.
- Uses from project: [rel₄, addMulSub_swap]
- Used by: relFin4_perm
- Visibility: public
- Lines: 496-497 (proof 1 line)
- Notes: none

### lemma rel₄_swap₁₂
- Type: `{m n r s} : rel₄ W m n r s = - rel₄ W m r n s`
- What: Swapping the middle two indices negates `rel₄`.
- How: `simp_rw [rel₄, addMulSub_swap W neg r n]; ring`.
- Hypotheses: `W` odd.
- Uses from project: [rel₄, addMulSub_swap]
- Used by: relFin4_perm
- Visibility: public
- Lines: 499-500 (proof 1 line)
- Notes: none

### lemma rel₄_swap₂₃
- Type: `{m n r s} : rel₄ W m n r s = - rel₄ W m n s r`
- What: Swapping the last two indices negates `rel₄`.
- How: `simp_rw [rel₄, addMulSub_swap W neg s r]; ring`.
- Hypotheses: `W` odd.
- Uses from project: [rel₄, addMulSub_swap]
- Used by: relFin4_perm
- Visibility: public
- Lines: 502-503 (proof 1 line)
- Notes: none

### def relFin4
- Type: `(t : Fin 4 → ℤ) : R := rel₄ W (t 0) (t 1) (t 2) (t 3)` (`variable (W)`)
- What: `rel₄` packaged with a 4-tuple input.
- How: Direct definition.
- Hypotheses: none.
- Uses from project: [rel₄]
- Used by: relFin4_perm, relFin4_perm', rel₄_of_oddRec_evenRec(thm)
- Visibility: public
- Lines: 507-509 (def, 1 line)
- Notes: none

### theorem relFin4_perm
- Type: `(σ : Perm (Fin 4)) : ∀ t, relFin4 W (t ∘ σ) = Perm.sign σ • relFin4 W t`
- What: `rel₄` (as `relFin4`) transforms by the sign of the permutation under reindexing.
- How: `Submonoid.closure_induction` over adjacent-transposition generators (`Perm.mclosure_swap_castSucc_succ 3`); base swaps handled by `rel₄_swap₀₁/₁₂/₂₃` and `Perm.sign_swap`.
- Hypotheses: `W` odd (`neg`).
- Uses from project: [relFin4, rel₄_swap₀₁, rel₄_swap₁₂, rel₄_swap₂₃]
- Used by: relFin4_perm'
- Visibility: public
- Lines: 512-520 (proof ~7 lines)
- Notes: none

### lemma relFin4_perm'
- Type: `(σ : Perm (Fin 4)) (t) : Perm.sign σ • relFin4 W (t ∘ σ) = relFin4 W t`
- What: Sign-corrected form of `relFin4_perm` (the sign cancels).
- How: `rw [relFin4_perm neg, ← mul_smul, Int.units_mul_self, one_smul]`.
- Hypotheses: `W` odd.
- Uses from project: [relFin4, relFin4_perm]
- Used by: rel₄_of_oddRec_evenRec(thm)
- Visibility: public
- Lines: 522-523 (proof 1 line)
- Notes: none

### lemma rel₄_same₀₁
- Type: `(m r s : ℤ) : rel₄ W m m r s = 0` (section `variable (zero : W 0 = 0)`)
- What: `rel₄` vanishes when the first two indices coincide (given `W 0 = 0`).
- How: `simp_rw [rel₄, addMulSub_same W zero]; ring`.
- Hypotheses: `W 0 = 0`.
- Uses from project: [rel₄, addMulSub_same]
- Used by: rel₄_of_oddRec_evenRec(thm)
- Visibility: public
- Lines: 530-531 (proof 1 line)
- Notes: none

### lemma rel₄_same₁₂
- Type: `(m n s : ℤ) : rel₄ W m n n s = 0`
- What: `rel₄` vanishes when the middle two indices coincide.
- How: `simp_rw [rel₄, addMulSub_same W zero]; ring`.
- Hypotheses: `W 0 = 0`.
- Uses from project: [rel₄, addMulSub_same]
- Used by: rel₄_of_oddRec_evenRec(thm)
- Visibility: public
- Lines: 533-534 (proof 1 line)
- Notes: none

### lemma rel₄_same₂₃
- Type: `(m n r : ℤ) : rel₄ W m n r r = 0`
- What: `rel₄` vanishes when the last two indices coincide.
- How: `simp_rw [rel₄, addMulSub_same W zero]; ring`.
- Hypotheses: `W 0 = 0`.
- Uses from project: [rel₄, addMulSub_same]
- Used by: rel₄_of_oddRec_evenRec(thm)
- Visibility: public
- Lines: 536-537 (proof 1 line)
- Notes: none

### theorem rel₄_of_oddRec_evenRec
- Type: `{a b c d : ℤ} (same : HaveSameParity₄ a b c d) : rel₄ W a b c d = 0` (section hyps `neg zero one two oddRec evenRec`)
- What: For an odd `W` with non-zero-divisor first terms satisfying the recurrences, every same-parity `rel₄` vanishes (no ordering needed).
- How: sort the absolute values into antitone order via `Tuple.sort`/`Fin.revPerm`, reduce to `relFin4` of the sorted tuple using `rel₄_abs` and `relFin4_perm'`, dispatch equal-adjacent cases by `rel₄_same*`, and apply `rel₄_of_anti_oddRec_evenRec` to the strictly-decreasing remainder (`same.abs.perm`).
- Hypotheses: `W` odd; `W 0 = 0`; `W 1, W 2 ∈ R⁰`; `OddRec (≥2)`; `EvenRec (≥3)`.
- Uses from project: [HaveSameParity₄, rel₄, rel₄_abs, relFin4, relFin4_perm', rel₄_same₂₃, rel₄_same₁₂, rel₄_same₀₁, rel₄_of_anti_oddRec_evenRec, HaveSameParity₄.abs, HaveSameParity₄.perm]
- Used by: IsEllSequence.of_oddRec_evenRec, IsEllSequence.rel₄
- Visibility: public
- Lines: 545-561 (proof ~16 lines)
- Notes: none

### theorem IsEllSequence.of_oddRec_evenRec (`_root_`)
- Type: `: IsEllSequence W` (same section hyps)
- What: An ℕ-indexed sequence satisfying odd/even recurrences, oddly extended to ℤ, is an elliptic sequence (given non-zero-divisor first terms).
- How: `rw [rel₃_iff₄, rel₄_of_oddRec_evenRec ...]`, then discharge the parity side goals via `negOnePow_two_mul`/`negOnePow_zero`.
- Hypotheses: `W` odd; `W 0 = 0`; `W 1, W 2 ∈ R⁰`; recurrences.
- Uses from project: [IsEllSequence, rel₃_iff₄, rel₄_of_oddRec_evenRec]
- Used by: IsEllSequence.normEDS_of_mem_nonZeroDivisors
- Visibility: public (root namespace)
- Lines: 566-568 (proof ~2 lines)
- Notes: none

### def IsDivSequence
- Type: `: Prop := ∀ m n : ℤ, m ∣ n → W m ∣ W n` (`open EllSequence`, `variable (W)` reinstated)
- What: A divisibility sequence: `W m ∣ W n` whenever `m ∣ n`.
- How: Direct definition.
- Hypotheses: none.
- Uses from project: []
- Used by: IsEllDivSequence, isDivSequence_id, IsDivSequence.smul/.map, IsDivSequence.normEDS, IsEllSequence.isDivSequence_of_dvd
- Visibility: public
- Lines: 576-578 (def, 1 line)
- Notes: none

### def IsEllDivSequence
- Type: `: Prop := IsEllSequence W ∧ IsDivSequence W`
- What: An EDS is an elliptic sequence that is also a divisibility sequence.
- How: Direct definition (conjunction).
- Hypotheses: none.
- Uses from project: [IsEllSequence, IsDivSequence]
- Used by: isEllDivSequence_id, IsEllDivSequence.smul/.map, IsEllDivSequence.eq_normEDS, IsEllDivSequence.normEDS, IsEllSequence.isEllDivSequence_of_dvd
- Visibility: public
- Lines: 580-582 (def, 2 lines)
- Notes: none

### lemma isEllSequence_id
- Type: `: IsEllSequence id`
- What: The identity sequence `n ↦ n` is elliptic.
- How: unfold `Rel₃`/`id_eq`, `ring1`.
- Hypotheses: none.
- Uses from project: [IsEllSequence, Rel₃]
- Used by: isEllDivSequence_id, normEDS_two_three_two
- Visibility: public
- Lines: 584-585 (proof 1 line)
- Notes: none

### lemma isDivSequence_id
- Type: `: IsDivSequence id`
- What: The identity sequence is a divisibility sequence.
- How: `fun _ _ ↦ id`.
- Hypotheses: none.
- Uses from project: [IsDivSequence]
- Used by: isEllDivSequence_id
- Visibility: public
- Lines: 587-588 (proof 1 line)
- Notes: none

### theorem isEllDivSequence_id
- Type: `: IsEllDivSequence id`
- What: The identity sequence is an EDS.
- How: `⟨isEllSequence_id, isDivSequence_id⟩`.
- Hypotheses: none.
- Uses from project: [IsEllDivSequence, isEllSequence_id, isDivSequence_id]
- Used by: unused in file
- Visibility: public
- Lines: 590-592 (1 line)
- Notes: none

### lemma IsEllSequence.smul
- Type: `(h : IsEllSequence W) (x : R) : IsEllSequence (x • W)` (`variable {W}`)
- What: Scaling an elliptic sequence by a constant gives an elliptic sequence.
- How: `linear_combination` of `x^4 * (h m n r)` with norm `simp [Pi.smul_apply, smul_eq_mul]; ring1`.
- Hypotheses: `W` elliptic.
- Uses from project: [IsEllSequence]
- Used by: IsEllDivSequence.smul, IsEllSequence.eq_normEDS_of_dvd (`IsEllSequence.normEDS.smul`)
- Visibility: public
- Lines: 596-598 (proof ~2 lines)
- Notes: none

### lemma IsDivSequence.smul
- Type: `(h : IsDivSequence W) (x : R) : IsDivSequence (x • W)`
- What: Scaling a divisibility sequence by a constant preserves divisibility.
- How: `mul_dvd_mul_left x` applied pointwise.
- Hypotheses: `W` a divisibility sequence.
- Uses from project: [IsDivSequence]
- Used by: IsEllDivSequence.smul, IsEllSequence.isDivSequence_of_dvd (`IsDivSequence.normEDS.smul`)
- Visibility: public
- Lines: 600-601 (proof 1 line)
- Notes: none

### lemma IsEllDivSequence.smul
- Type: `(h : IsEllDivSequence W) (x : R) : IsEllDivSequence (x • W)`
- What: Scaling an EDS by a constant gives an EDS.
- How: `⟨h.left.smul x, h.right.smul x⟩`.
- Hypotheses: `W` an EDS.
- Uses from project: [IsEllDivSequence, IsEllSequence.smul, IsDivSequence.smul]
- Used by: unused in file
- Visibility: public
- Lines: 603-604 (proof 1 line)
- Notes: none

### lemma IsEllSequence.map
- Type: `(h : IsEllSequence W) : IsEllSequence (f ∘ W)`
- What: A ring homomorphism's image of an elliptic sequence is elliptic.
- How: `simpa using (congr_arg f <| h · · ·)`.
- Hypotheses: `W` elliptic; `f` a ring hom (module-level `f : F`).
- Uses from project: [IsEllSequence]
- Used by: IsEllDivSequence.map, IsEllSequence.normEDS (`map _ (...)`)
- Visibility: public
- Lines: 606-607 (proof 1 line)
- Notes: none

### lemma IsDivSequence.map
- Type: `(h : IsDivSequence W) : IsDivSequence (f ∘ W)`
- What: Image of a divisibility sequence under a ring hom is a divisibility sequence.
- How: `map_dvd f` applied pointwise.
- Hypotheses: `W` a divisibility sequence.
- Uses from project: [IsDivSequence]
- Used by: IsEllDivSequence.map
- Visibility: public
- Lines: 609-610 (proof 1 line)
- Notes: none

### lemma IsEllDivSequence.map
- Type: `(h : IsEllDivSequence W) : IsEllDivSequence (f ∘ W)`
- What: Image of an EDS under a ring hom is an EDS.
- How: `⟨h.1.map f, h.2.map f⟩`.
- Hypotheses: `W` an EDS.
- Uses from project: [IsEllDivSequence, IsEllSequence.map, IsDivSequence.map]
- Used by: unused in file
- Visibility: public
- Lines: 612-613 (proof 1 line)
- Notes: none

### lemma IsEllSequence.oddRec
- Type: `(m : ℤ) : OddRec W m` (namespace `IsEllSequence`, `variable (ell : IsEllSequence W)`)
- What: An elliptic sequence satisfies the odd recurrence at every `m`.
- How: `(rel₃_iff_oddRec W m).mp (ell _ _ _)`.
- Hypotheses: `W` elliptic.
- Uses from project: [OddRec, rel₃_iff_oddRec, IsEllSequence]
- Used by: IsEllSequence.rel₄, IsEllSequence.ext (`ellW.oddRec`)
- Visibility: public (namespace)
- Lines: 622 (1 line)
- Notes: none

### lemma IsEllSequence.evenRec
- Type: `(m : ℤ) : EvenRec W m`
- What: An elliptic sequence satisfies the even recurrence at every `m`.
- How: `(rel₃_iff_evenRec W m).mp (ell _ _ _)`.
- Hypotheses: `W` elliptic.
- Uses from project: [EvenRec, rel₃_iff_evenRec, IsEllSequence]
- Used by: IsEllSequence.rel₄, IsEllSequence.ext (`ellW.evenRec`)
- Visibility: public (namespace)
- Lines: 623 (1 line)
- Notes: none

### lemma IsEllSequence.zero'
- Type: `[IsReduced R] : W 0 = 0`
- What: In a reduced ring, the zeroth term of an elliptic sequence is zero.
- How: from `ell 0 0 0`, simplify `Rel₃` to `W 0 ^ 3 = ...`, conclude `W 0 = 0` via `IsReduced.eq_zero` (nilpotency).
- Hypotheses: `W` elliptic; `R` reduced.
- Uses from project: [Rel₃, IsEllSequence]
- Used by: unused in file
- Visibility: public (namespace)
- Lines: 625-628 (proof ~3 lines)
- Notes: none

### lemma IsEllSequence.zero
- Type: `(m : ℤ) (mem : W (2 * m) ∈ R⁰) : W 0 = 0`
- What: The zeroth term of an elliptic sequence is zero, provided some even term is a non-zero-divisor.
- How: from `ell m m (2*m)`, rewrite `Rel₃` to expose `W 0 * W(2m)^2`, cancel via `mem`/`pow_mem`.
- Hypotheses: `W` elliptic; `W (2m) ∈ R⁰`.
- Uses from project: [Rel₃, IsEllSequence]
- Used by: IsEllSequence.rel₄ (`ell.zero 1 two`), IsEllSequence.ext, normEDS_of_mem_nonZeroDivisors (via `normEDS_zero`? — actually used as `ellW.zero`/`ellU.zero` in ext)
- Visibility: public (namespace)
- Lines: 630-635 (proof ~3 lines)
- Notes: none

### lemma IsEllSequence.sub_add_neg_sub_mul_eq_zero
- Type: `(m n r : ℤ) : (W (m-n) + W (-(m-n))) * W (m+n) * W r ^ 2 = 0`
- What: An odd-symmetry obstruction: `(W(m-n)+W(-(m-n)))·W(m+n)·W(r)²` vanishes for elliptic `W`.
- How: from `ell m n r + ell n m r`, regroup with distributivity/`mul_comm`, `convert ... using 4` with `ring_nf`.
- Hypotheses: `W` elliptic.
- Uses from project: [IsEllSequence]
- Used by: IsEllSequence.neg
- Visibility: public (namespace)
- Lines: 637-641 (proof ~3 lines)
- Notes: none

### lemma IsEllSequence.neg
- Type: `(m : ℤ) : W (-m) = - W m` (added `variable (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)`)
- What: An elliptic sequence is an odd function when its first two terms are non-zero-divisors.
- How: reduce to `W(-m)+W(m)=0`; by parity (`even_or_odd'`) cancel either `two` or `one` (squared) using `sub_add_neg_sub_mul_eq_zero` and `pow_mem`/`convert ... ; ring_nf`.
- Hypotheses: `W` elliptic; `W 1, W 2 ∈ R⁰`.
- Uses from project: [IsEllSequence, IsEllSequence.sub_add_neg_sub_mul_eq_zero]
- Used by: IsEllSequence.rel₄ (`ell.neg one two`), IsEllSequence.ext (`ellW.neg`, `ellU.neg`)
- Visibility: public (namespace)
- Lines: 647-654 (proof ~7 lines)
- Notes: none

### lemma IsEllSequence.rel₄
- Type: `protected {a b c d : ℤ} (same : HaveSameParity₄ a b c d) : rel₄ W a b c d = 0`
- What: For an elliptic sequence with non-zero-divisor first terms, every same-parity `rel₄` vanishes.
- How: `rel₄_of_oddRec_evenRec` fed with `ell.neg`, `ell.zero 1 two`, `one`, `two`, and `ell.oddRec`/`ell.evenRec`.
- Hypotheses: `W` elliptic; `W 1, W 2 ∈ R⁰`; same parity.
- Uses from project: [rel₄, HaveSameParity₄, rel₄_of_oddRec_evenRec, IsEllSequence.neg, IsEllSequence.zero, IsEllSequence.oddRec, IsEllSequence.evenRec]
- Used by: IsEllSequence.net
- Visibility: public (protected, namespace)
- Lines: 656-658 (proof ~2 lines)
- Notes: none

### lemma IsEllSequence.net
- Type: `protected (p q r s : ℤ) : net W p q r s = 0`
- What: For an elliptic sequence with non-zero-divisor first terms, every net relation vanishes.
- How: `net_eq_rel₄`, then `ell.rel₄ one two` with parity discharged via `negOnePow_add`/`negOnePow_two_mul`.
- Hypotheses: `W` elliptic; `W 1, W 2 ∈ R⁰`.
- Uses from project: [net, net_eq_rel₄, IsEllSequence.rel₄, HaveSameParity₄]
- Used by: IsEllSequence.invar
- Visibility: public (protected, namespace)
- Lines: 660-663 (proof ~3 lines)
- Notes: none

### lemma IsEllSequence.invar
- Type: `(s m n : ℤ) : invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m`
- What: For an elliptic sequence with non-zero-divisor first terms, the invariant is `n`-independent (cross-product identity).
- How: `invar_of_net _ (ell.net one two) _ _ _`.
- Hypotheses: `W` elliptic; `W 1, W 2 ∈ R⁰`.
- Uses from project: [invarNum, invarDenom, invar_of_net, IsEllSequence.net]
- Used by: unused in file
- Visibility: public (namespace)
- Lines: 665-666 (proof 1 line)
- Notes: none

### def preNormEDS'
- Type: `(b c d : R) : ℕ → R` (recursive, base cases 0..4, step `n+5` with parity split)
- What: The ℕ-indexed auxiliary normalised-EDS sequence with initial values `0,1,1,c,d`.
- How: Well-founded recursion on `ℕ` with explicit decreasing proofs (`h1..h4`, and `m+5 < n+5` in the odd branch), branching on `Even n` and `Even m` (factors of `b`).
- Hypotheses: none.
- Uses from project: []
- Used by: preNormEDS'_zero/one/two/three/four, preNormEDS'_even, preNormEDS'_odd, preNormEDS, preNormEDS_ofNat, normEDS_ofNat, map_preNormEDS' (both)
- Visibility: public
- Lines: 670-690 (def, ~13 lines body)
- Notes: none

### lemma preNormEDS'_zero
- Type: `: preNormEDS' b c d 0 = 0` (`@[simp]`)
- What: `preNormEDS'` at 0 is 0.
- How: `rw [preNormEDS']`.
- Hypotheses: none.
- Uses from project: [preNormEDS']
- Used by: map_preNormEDS' (line 1070, via simp)
- Visibility: public
- Lines: 692-694 (proof 1 line)
- Notes: none

### lemma preNormEDS'_one
- Type: `: preNormEDS' b c d 1 = 1` (`@[simp]`)
- What: `preNormEDS'` at 1 is 1.
- How: `rw [preNormEDS']`.
- Hypotheses: none.
- Uses from project: [preNormEDS']
- Used by: map_preNormEDS'
- Visibility: public
- Lines: 696-698 (proof 1 line)
- Notes: none

### lemma preNormEDS'_two
- Type: `: preNormEDS' b c d 2 = 1` (`@[simp]`)
- What: `preNormEDS'` at 2 is 1.
- How: `rw [preNormEDS']`.
- Hypotheses: none.
- Uses from project: [preNormEDS']
- Used by: map_preNormEDS'
- Visibility: public
- Lines: 700-702 (proof 1 line)
- Notes: none

### lemma preNormEDS'_three
- Type: `: preNormEDS' b c d 3 = c` (`@[simp]`)
- What: `preNormEDS'` at 3 is `c`.
- How: `rw [preNormEDS']`.
- Hypotheses: none.
- Uses from project: [preNormEDS']
- Used by: map_preNormEDS'
- Visibility: public
- Lines: 704-706 (proof 1 line)
- Notes: none

### lemma preNormEDS'_four
- Type: `: preNormEDS' b c d 4 = d` (`@[simp]`)
- What: `preNormEDS'` at 4 is `d`.
- How: `rw [preNormEDS']`.
- Hypotheses: none.
- Uses from project: [preNormEDS']
- Used by: map_preNormEDS'
- Visibility: public
- Lines: 708-710 (proof 1 line)
- Notes: none

### lemma preNormEDS'_even
- Type: `(m : ℕ) : preNormEDS' b c d (2*(m+3)) = (even-branch recurrence)`
- What: Even-index unfolding of `preNormEDS'` (the `2(m+3)` recurrence).
- How: rewrite `2(m+3)=2m+1+5`, `preNormEDS'`, `dif_neg (not_even_two_mul_add_one)`, `Nat.mul_add_div`.
- Hypotheses: none.
- Uses from project: [preNormEDS']
- Used by: preNormEDS_even, map_preNormEDS' (both)
- Visibility: public
- Lines: 712-716 (proof ~2 lines)
- Notes: none

### lemma preNormEDS'_odd
- Type: `(m : ℕ) : preNormEDS' b c d (2*(m+2)+1) = (odd-branch recurrence with `if Even m then b/1`)`
- What: Odd-index unfolding of `preNormEDS'`.
- How: rewrite `2(m+2)+1=2m+5`, `preNormEDS'`, `dif_pos (even_two_mul m)`, `mul_div_cancel_left`.
- Hypotheses: none.
- Uses from project: [preNormEDS']
- Used by: preNormEDS_odd, map_preNormEDS' (both)
- Visibility: public
- Lines: 718-722 (proof ~2 lines)
- Notes: none

### def preNormEDS
- Type: `(n : ℤ) : R := n.sign * preNormEDS' b c d n.natAbs`
- What: The ℤ-indexed auxiliary sequence: `preNormEDS'` on `|n|` signed by `sign n` (odd extension).
- How: Direct definition.
- Hypotheses: none.
- Uses from project: [preNormEDS']
- Used by: preNormEDS_ofNat..four, preNormEDS_neg, preNormEDS_even, preNormEDS_odd, complEDS₂, normEDS, compl₂EDSAux, compl₂EDS, universalNormEDS (via normEDS), map_preNormEDS (both), redInvarDenom (via complEDS/normEDS)
- Visibility: public
- Lines: 728-729 (def, 1 line)
- Notes: none

### lemma preNormEDS_ofNat
- Type: `(n : ℕ) : preNormEDS b c d n = preNormEDS' b c d n` (`@[simp]`)
- What: On naturals `preNormEDS` agrees with `preNormEDS'`.
- How: case `n = 0` by `simp`, else `Int.sign_natCast_of_ne_zero`.
- Hypotheses: none.
- Uses from project: [preNormEDS, preNormEDS']
- Used by: preNormEDS_even, preNormEDS_odd
- Visibility: public
- Lines: 731-735 (proof ~2 lines)
- Notes: none

### lemma preNormEDS_zero
- Type: `: preNormEDS b c d 0 = 0` (`@[simp]`)
- What: `preNormEDS` at 0 is 0.
- How: `simp [preNormEDS]`.
- Hypotheses: none.
- Uses from project: [preNormEDS]
- Used by: unused in file (simp lemma)
- Visibility: public
- Lines: 737-739 (proof 1 line)
- Notes: none

### lemma preNormEDS_one
- Type: `: preNormEDS b c d 1 = 1` (`@[simp]`)
- What: `preNormEDS` at 1 is 1.
- How: `simp [preNormEDS]`.
- Hypotheses: none.
- Uses from project: [preNormEDS]
- Used by: normEDS_six_eq_mul (via simp)
- Visibility: public
- Lines: 741-743 (proof 1 line)
- Notes: none

### lemma preNormEDS_two
- Type: `: preNormEDS b c d 2 = 1` (`@[simp]`)
- What: `preNormEDS` at 2 is 1.
- How: `simp [preNormEDS, Int.sign_eq_one_of_pos]`.
- Hypotheses: none.
- Uses from project: [preNormEDS]
- Used by: normEDS_six_eq_mul
- Visibility: public
- Lines: 745-747 (proof 1 line)
- Notes: none

### lemma preNormEDS_three
- Type: `: preNormEDS b c d 3 = c` (`@[simp]`)
- What: `preNormEDS` at 3 is `c`.
- How: `simp [preNormEDS, Int.sign_eq_one_of_pos]`.
- Hypotheses: none.
- Uses from project: [preNormEDS]
- Used by: unused in file (simp lemma)
- Visibility: public
- Lines: 749-751 (proof 1 line)
- Notes: none

### lemma preNormEDS_four
- Type: `: preNormEDS b c d 4 = d` (`@[simp]`)
- What: `preNormEDS` at 4 is `d`.
- How: `simp [preNormEDS, Int.sign_eq_one_of_pos]`.
- Hypotheses: none.
- Uses from project: [preNormEDS]
- Used by: normEDS_six_eq_mul
- Visibility: public
- Lines: 753-755 (proof 1 line)
- Notes: none

### lemma preNormEDS_neg
- Type: `(n : ℤ) : preNormEDS b c d (-n) = -preNormEDS b c d n` (`@[simp]`)
- What: `preNormEDS` is odd.
- How: `simp [preNormEDS]`.
- Hypotheses: none.
- Uses from project: [preNormEDS]
- Used by: preNormEDS_even, preNormEDS_odd, complEDS₂_neg, normEDS_neg, compl₂EDSAux_neg, compl₂EDS_neg, compl₂EDS_zero (via simp)
- Visibility: public
- Lines: 757-759 (proof 1 line)
- Notes: none

### lemma preNormEDS_even
- Type: `(m : ℤ) : preNormEDS b c d (2*m) = (even recurrence in preNormEDS)`
- What: The even-index recurrence for `preNormEDS` over all of ℤ.
- How: `Int.negInduction`; nat case reduces to `preNormEDS'_even` after `rcases`/`norm_cast`; neg case rewrites signs and applies the inductive hypothesis then `ring1`.
- Hypotheses: none.
- Uses from project: [preNormEDS, preNormEDS_ofNat, preNormEDS'_even, preNormEDS_neg]
- Used by: complEDS₂ (via preNormEDS_mul_complEDS₂), preNormEDS_mul_complEDS₂, normEDS_mul_compl₂EDS
- Visibility: public
- Lines: 761-774 (proof ~11 lines)
- Notes: none

### lemma preNormEDS_odd
- Type: `(m : ℤ) : preNormEDS b c d (2*m+1) = (odd recurrence in preNormEDS)`
- What: The odd-index recurrence for `preNormEDS` over all of ℤ.
- How: `Int.negInduction`; nat case via `preNormEDS'_odd`; neg case rewrites `2*-(m+1)+1` etc., uses `even_neg`/`Int.even_add_one`/`ite_not` and the inductive hypothesis, then `ring1`.
- Hypotheses: none.
- Uses from project: [preNormEDS, preNormEDS_ofNat, preNormEDS'_odd, preNormEDS_neg]
- Used by: normEDS_odd
- Visibility: public
- Lines: 776-792 (proof ~14 lines)
- Notes: none

### def complEDS₂
- Type: `(k : ℤ) : R := (preNormEDS (b^4) c d (k-1)^2 * preNormEDS (b^4) c d (k+2) - preNormEDS (b^4) c d (k-2) * preNormEDS (b^4) c d (k+1)^2) * if Even k then 1 else b`
- What: The 2-complement sequence witnessing `W(k) ∣ W(2k)`, i.e. `W(k)·Wᶜ₂(k) = W(2k)`.
- How: Direct definition in terms of `preNormEDS (b^4)`.
- Hypotheses: none.
- Uses from project: [preNormEDS]
- Used by: complEDS₂_zero..four, complEDS₂_neg, preNormEDS_mul_complEDS₂, normEDS_mul_complEDS₂, complEDS₂_mul_b, EllSequence.compl' (param), complEDS' (the n+2 even branch), complEDS_even, map_complEDS₂ (both)
- Visibility: public
- Lines: 798-800 (def, 2 lines)
- Notes: none

### lemma complEDS₂_zero
- Type: `: complEDS₂ b c d 0 = 2` (`@[simp]`)
- What: `complEDS₂` at 0 is 2.
- How: `simp [complEDS₂, one_add_one_eq_two]`.
- Hypotheses: none.
- Uses from project: [complEDS₂]
- Used by: compl₂EDS_two_three_two (`compl₂EDS_zero` analog — actually used? checked: `complEDS₂_zero` unused directly; included as simp)
- Visibility: public
- Lines: 802-804 (proof 1 line)
- Notes: none

### lemma complEDS₂_one
- Type: `: complEDS₂ b c d 1 = b` (`@[simp]`)
- What: `complEDS₂` at 1 is `b`.
- How: `simp [complEDS₂]`.
- Hypotheses: none.
- Uses from project: [complEDS₂]
- Used by: unused in file (simp lemma)
- Visibility: public
- Lines: 806-808 (proof 1 line)
- Notes: none

### lemma complEDS₂_two
- Type: `: complEDS₂ b c d 2 = d` (`@[simp]`)
- What: `complEDS₂` at 2 is `d`.
- How: `simp [complEDS₂]`.
- Hypotheses: none.
- Uses from project: [complEDS₂]
- Used by: unused in file (simp lemma)
- Visibility: public
- Lines: 810-812 (proof 1 line)
- Notes: none

### lemma complEDS₂_three
- Type: `: complEDS₂ b c d 3 = preNormEDS (b^4) c d 5 * b - d^2 * b` (`@[simp]`)
- What: Closed form of `complEDS₂` at 3.
- How: `simp [complEDS₂, if_neg (¬Even 3), sub_mul]`.
- Hypotheses: none.
- Uses from project: [complEDS₂, preNormEDS]
- Used by: unused in file (simp lemma)
- Visibility: public
- Lines: 814-816 (proof 1 line)
- Notes: none

### lemma complEDS₂_four
- Type: `: complEDS₂ b c d 4 = c^2 * preNormEDS (b^4) c d 6 - preNormEDS (b^4) c d 5^2` (`@[simp]`)
- What: Closed form of `complEDS₂` at 4.
- How: `simp [complEDS₂, if_pos (Even 4)]`.
- Hypotheses: none.
- Uses from project: [complEDS₂, preNormEDS]
- Used by: unused in file (simp lemma)
- Visibility: public
- Lines: 818-821 (proof 1 line)
- Notes: none

### lemma complEDS₂_neg
- Type: `(k : ℤ) : complEDS₂ b c d (-k) = complEDS₂ b c d k` (`@[simp]`)
- What: `complEDS₂` is even in `k`.
- How: `simp_rw` regrouping `±`, `preNormEDS_neg`, `even_neg`, `ring1`.
- Hypotheses: none.
- Uses from project: [complEDS₂, preNormEDS_neg]
- Used by: complEDS_even (`complEDS₂_neg`)
- Visibility: public
- Lines: 823-826 (proof ~2 lines)
- Notes: none

### lemma preNormEDS_mul_complEDS₂
- Type: `(k : ℤ) : preNormEDS (b^4) c d k * complEDS₂ b c d k = preNormEDS (b^4) c d (2*k) * if Even k then 1 else b`
- What: The 2-complement identity at the `preNormEDS` level.
- How: `rw [complEDS₂, preNormEDS_even]; ring1`.
- Hypotheses: none.
- Uses from project: [preNormEDS, complEDS₂, preNormEDS_even]
- Used by: normEDS_mul_complEDS₂
- Visibility: public
- Lines: 828-831 (proof ~2 lines)
- Notes: none

### def normEDS
- Type: `(n : ℤ) : R := preNormEDS (b^4) c d n * if Even n then b else 1`
- What: The canonical normalised EDS with initial values `0,1,b,c,d*b`.
- How: Direct definition (multiplies `preNormEDS (b^4)` by `b` on even indices).
- Hypotheses: none.
- Uses from project: [preNormEDS]
- Used by: very widely — normEDS_def, normEDS_ofNat..neg, normEDS_mul_complEDS₂, complEDS₂_mul_b, normEDS_even, normEDS_odd, normEDS_of_mem_nonZeroDivisors, invarNum_normEDS(_two), invarDenom_normEDS_two, compl₂EDSAux_mul_b, compl₂EDS, normEDS_mul_compl₂EDS, normEDS_dvd_*, compl₂EDS_mul_b, normEDS_six_eq_mul, EllSequence.complEDS, universalNormEDS, normEDS_eq_aeval, IsEllSequence.normEDS, IsEllSequence.ext, normEDS_two_three_two, redInvarNum, redInvarDenom, net_normEDS, rel₄_normEDS, invar*_normEDS, complEDS' (norm branch), complEDS_odd, map_normEDS (both)
- Visibility: public
- Lines: 841-842 (def, 1 line)
- Notes: none

### lemma normEDS_def
- Type: `(n : ℤ) : normEDS b c d n = preNormEDS (b^4) c d n * if Even n then b else 1`
- What: Definitional restatement of `normEDS`.
- How: `rfl`.
- Hypotheses: none.
- Uses from project: [normEDS, preNormEDS]
- Used by: unused in file
- Visibility: public
- Lines: 844-845 (proof, rfl)
- Notes: none

### lemma normEDS_ofNat
- Type: `(n : ℕ) : normEDS b c d n = preNormEDS' (b^4) c d n * if Even n then b else 1` (`@[simp]`)
- What: On naturals, `normEDS` is `preNormEDS'` (times the even-`b` factor).
- How: `simp_rw [normEDS, preNormEDS_ofNat, Int.even_coe_nat]`.
- Hypotheses: none.
- Uses from project: [normEDS, preNormEDS_ofNat, preNormEDS']
- Used by: unused in file (simp lemma)
- Visibility: public
- Lines: 847-850 (proof 1 line)
- Notes: none

### lemma normEDS_zero
- Type: `: normEDS b c d 0 = 0` (`@[simp]`)
- What: `normEDS` at 0 is 0.
- How: `simp [normEDS]`.
- Hypotheses: none.
- Uses from project: [normEDS]
- Used by: normEDS_of_mem_nonZeroDivisors (`normEDS_zero _ _ _`)
- Visibility: public
- Lines: 852-854 (proof 1 line)
- Notes: none

### lemma normEDS_one
- Type: `: normEDS b c d 1 = 1` (`@[simp]`)
- What: `normEDS` at 1 is 1.
- How: `simp [normEDS]`.
- Hypotheses: none.
- Uses from project: [normEDS]
- Used by: normEDS_of_mem_nonZeroDivisors, normEDS_two_three_two, net_normEDS, IsEllSequence.normEDS (`normEDS_one`)
- Visibility: public
- Lines: 856-858 (proof 1 line)
- Notes: none

### lemma normEDS_two
- Type: `: normEDS b c d 2 = b` (`@[simp]`)
- What: `normEDS` at 2 is `b`.
- How: `simp [normEDS]`.
- Hypotheses: none.
- Uses from project: [normEDS]
- Used by: normEDS_of_mem_nonZeroDivisors, invarDenom_eq_redInvarDenom_mul, normEDS_two_three_two, net_normEDS
- Visibility: public
- Lines: 860-862 (proof 1 line)
- Notes: none

### lemma normEDS_three
- Type: `: normEDS b c d 3 = c` (`@[simp]`)
- What: `normEDS` at 3 is `c`.
- How: `simp [normEDS, show ¬Even (3:ℤ) by decide]`.
- Hypotheses: none.
- Uses from project: [normEDS]
- Used by: invarDenom_eq_redInvarDenom_mul, normEDS_two_three_two
- Visibility: public
- Lines: 864-866 (proof 1 line)
- Notes: none

### lemma normEDS_four
- Type: `: normEDS b c d 4 = d * b` (`@[simp]`)
- What: `normEDS` at 4 is `d·b`.
- How: `simp [normEDS, show ¬Odd (4:ℤ) by decide]`.
- Hypotheses: none.
- Uses from project: [normEDS]
- Used by: normEDS_two_three_two, IsEllSequence.eq_normEDS_of_dvd (`normEDS_four`)
- Visibility: public
- Lines: 868-870 (proof 1 line)
- Notes: none

### lemma normEDS_neg
- Type: `(n : ℤ) : normEDS b c d (-n) = -normEDS b c d n` (`@[simp]`)
- What: `normEDS` is odd.
- How: `simp_rw [normEDS, preNormEDS_neg, neg_mul, even_neg]`.
- Hypotheses: none.
- Uses from project: [normEDS, preNormEDS_neg]
- Used by: normEDS_of_mem_nonZeroDivisors (`normEDS_neg`), complEDS₂_mul_b, compl₂EDS_mul_b, normEDS_mul_compl₂EDS, complEDS_odd
- Visibility: public
- Lines: 872-874 (proof 1 line)
- Notes: none

### lemma normEDS_mul_complEDS₂
- Type: `(k : ℤ) : normEDS b c d k * complEDS₂ b c d k = normEDS b c d (2*k)`
- What: `complEDS₂` is the 2-complement of `normEDS`: `W(k)·Wᶜ₂(k) = W(2k)`.
- How: `simp_rw [normEDS, mul_right_comm, preNormEDS_mul_complEDS₂, ...]` plus `apply_ite₂`, `if_pos (even_two_mul k)`.
- Hypotheses: none.
- Uses from project: [normEDS, complEDS₂, preNormEDS_mul_complEDS₂]
- Used by: normEDS_dvd_normEDS_two_mul, normEDS_even, compl₂EDS_two_three_two (no — that uses `normEDS_mul_compl₂EDS`); used by normEDS_even
- Visibility: public
- Lines: 876-879 (proof ~2 lines)
- Notes: none

### lemma normEDS_dvd_normEDS_two_mul
- Type: `(k : ℤ) : normEDS b c d k ∣ normEDS b c d (2*k)`
- What: `normEDS(k) ∣ normEDS(2k)`.
- How: witness `complEDS₂` via `(normEDS_mul_complEDS₂ ..).symm`.
- Hypotheses: none.
- Uses from project: [normEDS, complEDS₂, normEDS_mul_complEDS₂]
- Used by: unused in file
- Visibility: public
- Lines: 881-882 (proof 1 line)
- Notes: none

### lemma complEDS₂_mul_b
- Type: `(k : ℤ) : complEDS₂ b c d k * b = normEDS b c d (k-1)^2 * normEDS b c d (k+2) - normEDS b c d (k-2) * normEDS b c d (k+1)^2`
- What: `b·complEDS₂(k)` expressed purely in `normEDS` terms.
- How: `Int.negInduction`; nat case `simp_rw` + `split_ifs <;> ring1`; neg case via `complEDS₂_neg`/`normEDS_neg` + inductive hypothesis + `ring1`.
- Hypotheses: none.
- Uses from project: [complEDS₂, normEDS, complEDS₂_neg, normEDS_neg]
- Used by: normEDS_even
- Visibility: public
- Lines: 884-894 (proof ~8 lines)
- Notes: none

### lemma normEDS_even
- Type: `(m : ℤ) : normEDS b c d (2*m) * b = normEDS b c d (m-1)^2 * normEDS b c d m * normEDS b c d (m+2) - normEDS b c d (m-2) * normEDS b c d m * normEDS b c d (m+1)^2`
- What: The even-index recurrence for `normEDS` (with the `b` factor).
- How: `← normEDS_mul_complEDS₂`, `mul_assoc`, `complEDS₂_mul_b`, `ring1`.
- Hypotheses: none.
- Uses from project: [normEDS, normEDS_mul_complEDS₂, complEDS₂_mul_b]
- Used by: normEDS_of_mem_nonZeroDivisors (the EvenRec discharge)
- Visibility: public
- Lines: 896-900 (proof ~2 lines)
- Notes: none

### lemma normEDS_odd
- Type: `(m : ℤ) : normEDS b c d (2*m+1) = normEDS b c d (m+2) * normEDS b c d m^3 - normEDS b c d (m-1) * normEDS b c d (m+1)^3`
- What: The odd-index recurrence for `normEDS` (no `b` factor).
- How: `simp_rw [normEDS, preNormEDS_odd, ...]` with parity simplifications, then `split_ifs <;> ring1`.
- Hypotheses: none.
- Uses from project: [normEDS, preNormEDS_odd]
- Used by: normEDS_of_mem_nonZeroDivisors (the OddRec discharge)
- Visibility: public
- Lines: 902-907 (proof ~3 lines)
- Notes: none

### theorem IsEllSequence.normEDS_of_mem_nonZeroDivisors
- Type: `private (hb : b ∈ R⁰) : IsEllSequence (normEDS b c d)`
- What: `normEDS` is an elliptic sequence, under the (superfluous) assumption that `b` is a non-zero-divisor.
- How: `IsEllSequence.of_oddRec_evenRec` with `normEDS_neg`/`normEDS_zero`/`normEDS_one`/`normEDS_two`, then for each recurrence `lift m-2`/`m-3` to ℕ and rewrite via `normEDS_odd`/`normEDS_even`.
- Hypotheses: `b ∈ R⁰`.
- Uses from project: [IsEllSequence, normEDS, IsEllSequence.of_oddRec_evenRec, normEDS_neg, normEDS_zero, normEDS_one, normEDS_two, OddRec, normEDS_odd, EvenRec, normEDS_even]
- Used by: IsEllSequence.normEDS (the unconditional version)
- Visibility: private
- Lines: 910-920 (proof ~9 lines)
- Notes: superseded by `IsEllSequence.normEDS`; comment at 909.

### lemma invarNum_normEDS
- Type: `(n : ℤ) : invarNum (normEDS b c d) 1 n = W (n+2)*W (n-1)^2 + W (n+1)^2*W (n-2) + W n^3*b^2` (W := normEDS)
- What: Specializes `invarNum` at `s = 1` for `normEDS`, using `W 2 = b`.
- How: `simp [invarNum]`.
- Hypotheses: none.
- Uses from project: [invarNum, normEDS]
- Used by: invarNum_eq_redInvarNum_mul
- Visibility: public
- Lines: 922-924 (proof 1 line)
- Notes: none

### lemma invarNum_normEDS_two
- Type: `: invarNum (normEDS b c d) 1 2 = (d + b^4) * b`
- What: Value of `invarNum (normEDS) 1 2`.
- How: `simp [invarNum, right_distrib, ← pow_succ, ← pow_add]`.
- Hypotheses: none.
- Uses from project: [invarNum, normEDS]
- Used by: invar₂_normEDS_of_mem_nonZeroDivisors
- Visibility: public
- Lines: 926-927 (proof 1 line)
- Notes: none

### lemma invarDenom_normEDS_two
- Type: `: invarDenom (normEDS b c d) 1 2 = c * b`
- What: Value of `invarDenom (normEDS) 1 2`.
- How: `simp [invarDenom]`.
- Hypotheses: none.
- Uses from project: [invarDenom, normEDS]
- Used by: invar₂_normEDS_of_mem_nonZeroDivisors
- Visibility: public
- Lines: 929 (1 line)
- Notes: none

### def normEDSRec'
- Type: `noncomputable {P : ℕ → Sort u} (zero one two three four) (even : ∀ m, (∀ k < 2*(m+3), P k) → P (2*(m+3))) (odd : ∀ m, (∀ k < 2*(m+2)+1, P k) → P (2*(m+2)+1)) (n : ℕ) : P n` (`@[elab_as_elim]`)
- What: Strong recursion principle for ℕ-indexed normalised EDS (with full strong hypotheses).
- How: `Nat.evenOddStrongRec` with `rintro` case-splitting on small residues feeding `zero/two/four/even` and `one/three/odd`.
- Hypotheses: base cases `P 0..4`, even/odd strong recursors.
- Uses from project: []
- Used by: normEDSRec, map_preNormEDS' (both, `induction ... using normEDSRec'`)
- Visibility: public (noncomputable)
- Lines: 936-942 (proof ~2 lines)
- Notes: none

### def normEDSRec
- Type: `noncomputable {P} (zero..four) (even : ∀ m, P(m+1)→P(m+2)→P(m+3)→P(m+4)→P(m+5)→P(2*(m+3))) (odd : ∀ m, P(m+1)→..→P(m+4)→P(2*(m+2)+1)) (n) : P n` (`@[elab_as_elim]`)
- What: Recursion principle for normalised EDS with explicit finite (non-strong) hypotheses.
- How: reduces to `normEDSRec'`, supplying the five/four predecessors via `ih _ <| by linarith only`.
- Hypotheses: base cases + finitary even/odd steps.
- Uses from project: [normEDSRec']
- Used by: IsEllSequence.ext
- Visibility: public (noncomputable)
- Lines: 951-958 (proof ~2 lines)
- Notes: none

### def compl₂EDSAux
- Type: `(b c d : R) (m : ℤ) : R := preNormEDS (b^4) c d (m-2) * preNormEDS (b^4) c d (m+1)^2 * if Even m then 1 else b` (`variable (b c d) (m)`)
- What: An auxiliary expression for the reduced invariant numerator and the `ω` division polynomials.
- How: Direct definition.
- Hypotheses: none.
- Uses from project: [preNormEDS]
- Used by: compl₂EDSAux_zero..neg_two, compl₂EDSAux_mul_b, compl₂EDSAux_neg, redInvarNum, compl₂EDS_eq_redInvarNum_sub, invarNum_eq_redInvarNum_mul, map_compl₂EDSAux, map_redInvarNum
- Visibility: public
- Lines: 966-967 (def, 1 line)
- Notes: none

### lemma compl₂EDSAux_zero
- Type: `: compl₂EDSAux b c d 0 = -1` (`@[simp]`)
- What: `compl₂EDSAux` at 0 is `-1`.
- How: `simp [compl₂EDSAux]`.
- Hypotheses: none.
- Uses from project: [compl₂EDSAux]
- Used by: unused in file (simp lemma)
- Visibility: public
- Lines: 969 (1 line)
- Notes: none

### lemma compl₂EDSAux_one
- Type: `: compl₂EDSAux b c d 1 = -b` (`@[simp]`)
- What: `compl₂EDSAux` at 1 is `-b`.
- How: `simp [compl₂EDSAux]`.
- Hypotheses: none.
- Uses from project: [compl₂EDSAux]
- Used by: unused in file (simp lemma)
- Visibility: public
- Lines: 970 (1 line)
- Notes: none

### lemma compl₂EDSAux_neg_one
- Type: `: compl₂EDSAux b c d (-1) = 0` (`@[simp]`)
- What: `compl₂EDSAux` at `-1` is 0.
- How: `simp [compl₂EDSAux]`.
- Hypotheses: none.
- Uses from project: [compl₂EDSAux]
- Used by: unused in file (simp lemma)
- Visibility: public
- Lines: 971 (1 line)
- Notes: none

### lemma compl₂EDSAux_two
- Type: `: compl₂EDSAux b c d 2 = 0` (`@[simp]`)
- What: `compl₂EDSAux` at 2 is 0.
- How: `simp [compl₂EDSAux]`.
- Hypotheses: none.
- Uses from project: [compl₂EDSAux]
- Used by: unused in file (simp lemma)
- Visibility: public
- Lines: 972 (1 line)
- Notes: none

### lemma compl₂EDSAux_neg_two
- Type: `: compl₂EDSAux b c d (-2) = -d` (`@[simp]`)
- What: `compl₂EDSAux` at `-2` is `-d`.
- How: `simp [compl₂EDSAux]`.
- Hypotheses: none.
- Uses from project: [compl₂EDSAux]
- Used by: unused in file (simp lemma)
- Visibility: public
- Lines: 973 (1 line)
- Notes: none

### lemma compl₂EDSAux_mul_b
- Type: `: compl₂EDSAux b c d m * b = normEDS b c d (m-2) * normEDS b c d (m+1)^2`
- What: `b·compl₂EDSAux(m)` expressed in `normEDS` terms.
- How: `simp_rw [compl₂EDSAux, normEDS, ...]` parity rewrites; `split_ifs <;> ring`.
- Hypotheses: none.
- Uses from project: [compl₂EDSAux, normEDS]
- Used by: invarNum_eq_redInvarNum_mul
- Visibility: public
- Lines: 975-978 (proof ~2 lines)
- Notes: none

### def compl₂EDS
- Type: `(b c d : R) (m : ℤ) : R := (p (m-1)^2 * p (m+2) - p (m-2) * p (m+1)^2) * if Even m then 1 else b` where `p := preNormEDS (b^4)`
- What: The complement of `W(m)` in `W(2m)` for `normEDS` — the witness of `W(m) ∣ W(2m)`.
- How: Direct definition.
- Hypotheses: none.
- Uses from project: [preNormEDS]
- Used by: compl₂EDSAux_neg, compl₂EDS_zero/one/two/neg, normEDS_mul_compl₂EDS, normEDS_dvd_two_mul, compl₂EDS_mul_b, normEDS_six_eq_mul, EllSequence.complEDS, compl₂EDS_eq_aeval, compl₂EDS_two_three_two, redInvarNum, compl₂EDS_eq_redInvarNum_sub, map_compl₂EDS (both), map_redInvarNum
- Visibility: public
- Lines: 981-983 (def, 2 lines)
- Notes: none

### lemma compl₂EDSAux_neg
- Type: `: compl₂EDSAux b c d (-m) = -compl₂EDS b c d m - compl₂EDSAux b c d m`
- What: Reflection identity relating `compl₂EDSAux(-m)` to `compl₂EDS(m)` and `compl₂EDSAux(m)`.
- How: `simp_rw` regrouping negations, `preNormEDS_neg`, `even_neg`, `ring_nf`.
- Hypotheses: none.
- Uses from project: [compl₂EDSAux, compl₂EDS, preNormEDS_neg]
- Used by: unused in file
- Visibility: public
- Lines: 985-987 (proof ~2 lines)
- Notes: none

### lemma compl₂EDS_zero
- Type: `: compl₂EDS b c d 0 = 2` (`@[simp]`)
- What: `compl₂EDS` at 0 is 2.
- How: `simp [compl₂EDS, one_add_one_eq_two]`.
- Hypotheses: none.
- Uses from project: [compl₂EDS]
- Used by: unused in file (simp lemma)
- Visibility: public
- Lines: 989 (1 line)
- Notes: none

### lemma compl₂EDS_one
- Type: `: compl₂EDS b c d 1 = b` (`@[simp]`)
- What: `compl₂EDS` at 1 is `b`.
- How: `simp [compl₂EDS]`.
- Hypotheses: none.
- Uses from project: [compl₂EDS]
- Used by: unused in file (simp lemma)
- Visibility: public
- Lines: 990 (1 line)
- Notes: none

### lemma compl₂EDS_two
- Type: `: compl₂EDS b c d 2 = d` (`@[simp]`)
- What: `compl₂EDS` at 2 is `d`.
- How: `simp [compl₂EDS]`.
- Hypotheses: none.
- Uses from project: [compl₂EDS]
- Used by: unused in file (simp lemma)
- Visibility: public
- Lines: 991 (1 line)
- Notes: none

### lemma compl₂EDS_neg
- Type: `: compl₂EDS b c d (-m) = compl₂EDS b c d m` (`@[simp]`)
- What: `compl₂EDS` is even in `m`.
- How: `simp_rw` regroup, `preNormEDS_neg`, `even_neg`, `ring_nf`.
- Hypotheses: none.
- Uses from project: [compl₂EDS, preNormEDS_neg]
- Used by: normEDS_mul_compl₂EDS, compl₂EDS_mul_b
- Visibility: public
- Lines: 993-994 (proof ~1 line)
- Notes: none

### lemma normEDS_mul_compl₂EDS
- Type: `: normEDS b c d m * compl₂EDS b c d m = normEDS b c d (2*m)`
- What: `compl₂EDS` is the 2-complement of `normEDS`: `W(m)·Wᶜ₂(m) = W(2m)`.
- How: `Int.negInduction`; nat case via `preNormEDS_even`, `mul_mul_mul_comm`, `congr`, `split_ifs`; neg case via `normEDS_neg`/`compl₂EDS_neg`.
- Hypotheses: none.
- Uses from project: [normEDS, compl₂EDS, preNormEDS_even, normEDS_neg, compl₂EDS_neg]
- Used by: normEDS_dvd_two_mul, normEDS_six_eq_mul, compl₂EDS_two_three_two, IsDivSequence.normEDS
- Visibility: public
- Lines: 996-1007 (proof ~10 lines)
- Notes: none

### lemma normEDS_dvd_two_mul
- Type: `: normEDS b c d m ∣ normEDS b c d (2*m)`
- What: `normEDS(m) ∣ normEDS(2m)`.
- How: witness via `(normEDS_mul_compl₂EDS b c d m).symm`.
- Hypotheses: none.
- Uses from project: [normEDS, normEDS_mul_compl₂EDS]
- Used by: unused in file
- Visibility: public
- Lines: 1009-1010 (proof 1 line)
- Notes: none

### lemma compl₂EDS_mul_b
- Type: `: compl₂EDS b c d m * b = W (m-1)^2 * W (m+2) - W (m-2) * W (m+1)^2` (W := normEDS)
- What: `b·compl₂EDS(m)` expressed in `normEDS` terms.
- How: `Int.negInduction`; nat case `simp_rw` parity + `split_ifs <;> ring`; neg case via reflection + `normEDS_neg`/`compl₂EDS_neg` + `convert ... ; ring`.
- Hypotheses: none.
- Uses from project: [compl₂EDS, normEDS, normEDS_neg, compl₂EDS_neg]
- Used by: unused in file
- Visibility: public
- Lines: 1012-1021 (proof ~8 lines)
- Notes: none

### lemma normEDS_six_eq_mul
- Type: `: normEDS b c d 6 = (normEDS b c d 5 - d^2) * b * c`
- What: Closed form for `normEDS` at 6.
- How: rewrite `6 = 2*3`, `← normEDS_mul_compl₂EDS`, `compl₂EDS` with `if_neg`, unfold `preNormEDS` values, `ring`.
- Hypotheses: none.
- Uses from project: [normEDS, normEDS_mul_compl₂EDS, compl₂EDS, normEDS_three, preNormEDS]
- Used by: invarDenom_eq_redInvarDenom_mul (the `normEDS_six_eq_mul` rewrites)
- Visibility: public
- Lines: 1023-1027 (proof ~4 lines)
- Notes: none

### def EllSequence.compl'
- Type: `(W₁ compl₂ : ℤ → R) (m : ℤ) : ℕ → R` (recursive: 0↦0, 1↦1, n+2 parity-split)
- What: Division-free construction of `W(n·m)/W(m)` from sequences for `W(m)/W(1)` (`W₁`) and `W(2m)/W(m)` (`compl₂`).
- How: Well-founded recursion on `ℕ` with decreasing proofs (`k < n+2`, `k+1 < n+2`), branching on `Even n`.
- Hypotheses: none.
- Uses from project: []
- Used by: EllSequence.compl, compl_ofNat, EllSequence.map_compl' (both), IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors, redInvarDenom_zero/one/two (via complEDS/compl), normEDS_mul_complEDS (via complEDS)
- Visibility: public (namespace EllSequence)
- Lines: 1035-1046 (def, ~10 lines)
- Notes: none

### def EllSequence.compl
- Type: `(n : ℤ) : R := n.sign * compl' W₁ compl₂ m n.natAbs`
- What: ℤ-indexed `W(n·m)/W(m)` (odd extension of `compl'`).
- How: Direct definition.
- Hypotheses: none.
- Uses from project: [EllSequence.compl']
- Used by: compl_ofNat, compl_neg, EllSequence.complEDS, EllSequence.map_compl, IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors
- Visibility: public (namespace)
- Lines: 1048-1049 (def, 1 line)
- Notes: none

### lemma EllSequence.compl_ofNat
- Type: `(n : ℕ) : compl W₁ compl₂ m n = compl' W₁ compl₂ m n`
- What: On naturals, `compl` agrees with `compl'`.
- How: case `n=0` by `simp`; else `Int.natAbs_cast` + `simp`.
- Hypotheses: none.
- Uses from project: [EllSequence.compl, EllSequence.compl']
- Used by: IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors
- Visibility: public (namespace)
- Lines: 1051-1053 (proof ~2 lines)
- Notes: none

### lemma EllSequence.compl_neg
- Type: `(n : ℤ) : compl W₁ compl₂ m (-n) = -compl W₁ compl₂ m n`
- What: `compl` is odd in `n`.
- How: `simp [compl]`.
- Hypotheses: none.
- Uses from project: [EllSequence.compl]
- Used by: IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors
- Visibility: public (namespace)
- Lines: 1055 (1 line)
- Notes: none

### def EllSequence.complEDS
- Type: `:= compl (normEDS b c d) (compl₂EDS b c d) m`
- What: `W(n·m)/W(m)` for `W` a normalised EDS.
- How: instantiate `compl` with `normEDS` and `compl₂EDS`.
- Hypotheses: none.
- Uses from project: [EllSequence.compl, normEDS, compl₂EDS]
- Used by: complEDS_eq_aeval, map_complEDS, redInvarDenom (`C := complEDS`), redInvarDenom_zero/one/two, normEDS_mul_complEDS
- Visibility: public (namespace)
- Lines: 1057-1058 (def, 1 line)
- Notes: none — NOTE: distinct from the later top-level `complEDS` (lines 1454) which is a different sequence.

### lemma map_preNormEDS' (Map section, first)
- Type: `(n : ℕ) : f (preNormEDS' b c d n) = preNormEDS' (f b) (f c) (f d) n` (`variable {b c d}`, `f : F`)
- What: `f : R →* S` (RingHomClass) commutes with `preNormEDS'`.
- How: `induction n using normEDSRec'`; base cases by `map_*` lemmas; step `simp only [preNormEDS'_odd/even, ...]` then `repeat rw [ih ...]`.
- Hypotheses: none (uses module-level `f`).
- Uses from project: [preNormEDS', normEDSRec', preNormEDS'_odd, preNormEDS'_even]
- Used by: map_preNormEDS (first version)
- Visibility: public
- Lines: 1068-1077 (proof ~9 lines)
- Notes: none — NOTE: a second `@[simp]`-tagged `map_preNormEDS'` is redefined at lines 1534-1544 (over `f : R →+* S`).

### lemma map_preNormEDS (Map section, first)
- Type: `(n : ℤ) : f (preNormEDS b c d n) = preNormEDS (f b) (f c) (f d) n`
- What: `f` commutes with `preNormEDS`.
- How: `rw [preNormEDS, map_mul, map_intCast, map_preNormEDS', preNormEDS]`.
- Hypotheses: none.
- Uses from project: [preNormEDS, map_preNormEDS']
- Used by: map_normEDS (first), map_compl₂EDS, EllSequence.map_compl₂EDSAux (`map_preNormEDS`), map_redInvarNum (via map_compl₂EDS)
- Visibility: public
- Lines: 1079-1080 (proof 1 line)
- Notes: none — NOTE: re-declared at 1546-1548.

### lemma map_normEDS (Map section, first)
- Type: `(n : ℤ) : f (normEDS b c d n) = normEDS (f b) (f c) (f d) n`
- What: `f` commutes with `normEDS`.
- How: `rw [normEDS, map_mul, map_preNormEDS, map_pow, apply_ite f, map_one, normEDS]`.
- Hypotheses: none.
- Uses from project: [normEDS, map_preNormEDS]
- Used by: map_complEDS (via Function.comp/map_normEDS), map_net (via map_rel₄? no), normEDS_eq_aeval, compl₂EDS_eq_aeval(no), universalNormEDS_ne_zero, map_redInvarNum, map_redInvarDenom, IsEllSequence.normEDS (via normEDS_eq_aeval)
- Visibility: public
- Lines: 1082-1083 (proof 1 line)
- Notes: none — NOTE: re-declared at 1554-1556.

### lemma map_compl₂EDS
- Type: `(n : ℤ) : f (compl₂EDS b c d n) = compl₂EDS (f b) (f c) (f d) n`
- What: `f` commutes with `compl₂EDS`.
- How: `simp only [compl₂EDS, map_sub, map_mul, map_pow, map_preNormEDS, apply_ite f, map_one]`.
- Hypotheses: none.
- Uses from project: [compl₂EDS, map_preNormEDS]
- Used by: map_complEDS (`map_compl₂EDS`), compl₂EDS_eq_aeval, map_redInvarNum
- Visibility: public
- Lines: 1085-1086 (proof 1 line)
- Notes: none

### lemma EllSequence.map_compl'
- Type: `(W₁ compl₂ : ℤ → R) (m : ℤ) (n : ℕ) : f (compl' W₁ compl₂ m n) = compl' (f ∘ W₁) (f ∘ compl₂) m n`
- What: `f` commutes with `compl'` (pushed through the two input sequences).
- How: `n.strong_induction_on`; base by `simp [compl']`; step `split_ifs` with `ih` and `map_*` lemmas.
- Hypotheses: none.
- Uses from project: [EllSequence.compl']
- Used by: EllSequence.map_compl
- Visibility: public (namespace)
- Lines: 1088-1098 (proof ~9 lines)
- Notes: none

### lemma EllSequence.map_compl
- Type: `(W₁ compl₂ : ℤ → R) (m n : ℤ) : f (compl W₁ compl₂ m n) = compl (f ∘ W₁) (f ∘ compl₂) m n`
- What: `f` commutes with `compl`.
- How: `simp [compl, map_compl']`.
- Hypotheses: none.
- Uses from project: [EllSequence.compl, EllSequence.map_compl']
- Used by: map_complEDS
- Visibility: public (namespace)
- Lines: 1100-1102 (proof 1 line)
- Notes: none

### lemma map_complEDS
- Type: `(m n : ℤ) : f (complEDS b c d m n) = complEDS (f b) (f c) (f d) m n`
- What: `f` commutes with `EllSequence.complEDS`.
- How: `simp_rw [complEDS, map_compl, Function.comp, map_normEDS, map_compl₂EDS]`.
- Hypotheses: none.
- Uses from project: [EllSequence.complEDS, EllSequence.map_compl, map_normEDS, map_compl₂EDS]
- Used by: complEDS_eq_aeval, EllSequence.map_redInvarDenom
- Visibility: public
- Lines: 1104-1105 (proof 1 line)
- Notes: none — refers to `EllSequence.complEDS`, not the later top-level `complEDS`.

### lemma map_addMulSub
- Type: `(m n : ℤ) : f (addMulSub W m n) = addMulSub (f ∘ W) m n`
- What: `f` commutes with `addMulSub`.
- How: `simp_rw [addMulSub, map_mul, Function.comp]`.
- Hypotheses: none.
- Uses from project: [addMulSub]
- Used by: map_rel₄
- Visibility: public
- Lines: 1107-1108 (proof 1 line)
- Notes: none

### lemma map_rel₄
- Type: `(p q r s : ℤ) : f (rel₄ W p q r s) = rel₄ (f ∘ W) p q r s`
- What: `f` commutes with `rel₄`.
- How: `simp_rw [rel₄, map_add, map_sub, map_mul, map_addMulSub]`.
- Hypotheses: none.
- Uses from project: [rel₄, map_addMulSub]
- Used by: map_net
- Visibility: public
- Lines: 1110-1111 (proof 1 line)
- Notes: none

### lemma map_net
- Type: `(p q r s : ℤ) : f (net W p q r s) = net (f ∘ W) p q r s`
- What: `f` commutes with `net`.
- How: `simp_rw [net_eq_rel₄, map_rel₄]`.
- Hypotheses: none.
- Uses from project: [net, net_eq_rel₄, map_rel₄]
- Used by: net_normEDS
- Visibility: public
- Lines: 1113-1114 (proof 1 line)
- Notes: none

### lemma map_invarNum
- Type: `(s m : ℤ) : f (invarNum W s m) = invarNum (f ∘ W) s m`
- What: `f` commutes with `invarNum`.
- How: `simp only [invarNum, map_add, map_mul, map_pow, Function.comp]`.
- Hypotheses: none.
- Uses from project: [invarNum]
- Used by: invar₂_normEDS
- Visibility: public
- Lines: 1116-1117 (proof 1 line)
- Notes: none

### lemma map_invarDenom
- Type: `(s m : ℤ) : f (invarDenom W s m) = invarDenom (f ∘ W) s m`
- What: `f` commutes with `invarDenom`.
- How: `simp_rw [invarDenom, map_mul, Function.comp]`.
- Hypotheses: none.
- Uses from project: [invarDenom]
- Used by: invar₂_normEDS
- Visibility: public
- Lines: 1119-1120 (proof 1 line)
- Notes: none

### inductive Param
- Type: `Type | B : Param | C : Param | D : Param`
- What: A three-element index type for the three parameters `b, c, d` of a normalised EDS.
- How: Inductive declaration with three nullary constructors.
- Hypotheses: none.
- Uses from project: []
- Used by: universalNormEDS, normEDS_eq_aeval, compl₂EDS_eq_aeval, complEDS_eq_aeval, universalNormEDS_ne_zero, universalNormEDS_mem_nonZeroDivisors, invar₂_normEDS, redInvar_normEDS, net_normEDS (`Param.rec`/`X B/C/D`)
- Visibility: public
- Lines: 1122-1123 (inductive)
- Notes: none

### def universalNormEDS
- Type: `noncomputable : ℤ → MvPolynomial Param ℤ := normEDS (X B) (X C) (X D)`
- What: The universal normalised EDS over `MvPolynomial Param ℤ`, from which any `normEDS` arises by `aeval`.
- How: instantiate `normEDS` with the three polynomial variables.
- Hypotheses: none.
- Uses from project: [normEDS]
- Used by: normEDS_eq_aeval, universalNormEDS_ne_zero, universalNormEDS_mem_nonZeroDivisors, normEDS_mul_complEDS, invar₂_normEDS, net_normEDS, IsEllSequence.normEDS
- Visibility: public (noncomputable)
- Lines: 1126-1131 (def, 1 line)
- Notes: none

### lemma normEDS_eq_aeval
- Type: `: normEDS b c d = (aeval (Param.rec b c d) <| universalNormEDS ·)`
- What: Every `normEDS b c d` is the `aeval`-image of `universalNormEDS`.
- How: `simp_rw [universalNormEDS, map_normEDS, aeval_X]`.
- Hypotheses: none.
- Uses from project: [normEDS, universalNormEDS, map_normEDS]
- Used by: normEDS_mul_complEDS, IsEllSequence.normEDS, net_normEDS, invar₂_normEDS (via Function.comp)
- Visibility: public
- Lines: 1133-1134 (proof 1 line)
- Notes: none

### lemma compl₂EDS_eq_aeval
- Type: `: compl₂EDS b c d = (aeval (Param.rec b c d) <| compl₂EDS (X B) (X C) (X D) ·)`
- What: `compl₂EDS b c d` is the `aeval`-image of the universal `compl₂EDS`.
- How: `simp_rw [map_compl₂EDS, aeval_X]`.
- Hypotheses: none.
- Uses from project: [compl₂EDS, map_compl₂EDS]
- Used by: unused in file
- Visibility: public
- Lines: 1136-1139 (proof 1 line)
- Notes: none

### lemma complEDS_eq_aeval
- Type: `: complEDS b c d = (aeval (Param.rec b c d) <| complEDS (X B) (X C) (X D) · ·)`
- What: `EllSequence.complEDS b c d` is the `aeval`-image of the universal version.
- How: `simp_rw [map_complEDS, aeval_X]`.
- Hypotheses: none.
- Uses from project: [EllSequence.complEDS, map_complEDS]
- Used by: normEDS_mul_complEDS
- Visibility: public
- Lines: 1141-1144 (proof 1 line)
- Notes: none

### lemma IsEllSequence.normEDS
- Type: `protected : IsEllSequence (normEDS b c d)` (section `variable {b c d} {U} (ellW ellU)`, `include ellW ellU`)
- What: A normalised EDS is an elliptic sequence (unconditional — no `hb`).
- How: `rw [normEDS_eq_aeval]`, then `IsEllSequence.map` of `normEDS_of_mem_nonZeroDivisors` applied to the universal EDS, using `X_ne_zero` so `X B ∈ (MvPolynomial)⁰`.
- Hypotheses: none on `b,c,d` (the `ellW`/`ellU` in scope are not used by this lemma's body).
- Uses from project: [IsEllSequence, normEDS, normEDS_eq_aeval, IsEllSequence.map, IsEllSequence.normEDS_of_mem_nonZeroDivisors]
- Used by: normEDS_two_three_two, compl₂EDS_two_three_two (via normEDS_two_three_two), rel₄_normEDS (no), IsEllDivSequence.normEDS, net_normEDS, normEDS_mul_complEDS
- Visibility: public (protected)
- Lines: 1154-1157 (proof ~2 lines)
- Notes: none

### lemma IsEllSequence.ext
- Type: `protected (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰) (h1..h4 : W i = U i) : W = U`
- What: Two elliptic sequences agreeing on terms 1–4 are equal, given non-zero-divisor first terms.
- How: `funext`/`Int.negInduction`; nat case `normEDSRec` with base/recursion steps using `ellW.zero`, `ellW.evenRec`/`ellU.evenRec` (after cancelling a non-zero-divisor via `mul_cancel_right_mem_nonZeroDivisors`) and `ellW.oddRec`/`ellU.oddRec`, plus `convert congr(...)`; neg case via `ellW.neg`/`ellU.neg`.
- Hypotheses: `W, U` elliptic (in scope `ellW, ellU`); `W 1, W 2 ∈ R⁰`; agreement on 1..4.
- Uses from project: [IsEllSequence, normEDSRec, IsEllSequence.zero, IsEllSequence.evenRec, IsEllSequence.oddRec, IsEllSequence.neg]
- Used by: normEDS_two_three_two, IsEllSequence.eq_normEDS_of_dvd
- Visibility: public (protected)
- Lines: 1161-1175 (proof ~13 lines)
- Notes: uses `erw` (lines 1168, 1172).

### lemma normEDS_two_three_two
- Type: `: normEDS 2 3 2 = id`
- What: The normalised EDS with parameters `(2,3,2)` is the identity sequence.
- How: `IsEllSequence.normEDS.ext isEllSequence_id`, discharging the four base equalities and the two non-zero-divisor conditions (`one_ne_zero`, `two_ne_zero`).
- Hypotheses: none.
- Uses from project: [normEDS, IsEllSequence.normEDS, IsEllSequence.ext, isEllSequence_id, normEDS_one, normEDS_two, normEDS_three, normEDS_four]
- Used by: compl₂EDS_two_three_two, universalNormEDS_ne_zero
- Visibility: public
- Lines: 1177-1181 (proof ~4 lines)
- Notes: none

### lemma compl₂EDS_two_three_two
- Type: `(n : ℤ) : compl₂EDS (2 : ℤ) 3 2 n = 2`
- What: The 2-complement of the identity EDS is constantly 2.
- How: case `n=0` by `compl₂EDS_zero`; else from `normEDS_mul_compl₂EDS` with `normEDS_two_three_two` and `mul_cancel_right_mem_nonZeroDivisors`.
- Hypotheses: none.
- Uses from project: [compl₂EDS, compl₂EDS_zero, normEDS_mul_compl₂EDS, normEDS_two_three_two]
- Used by: unused in file
- Visibility: public
- Lines: 1183-1188 (proof ~4 lines)
- Notes: none

### lemma universalNormEDS_ne_zero
- Type: `{n : ℤ} (hn : n ≠ 0) : universalNormEDS n ≠ 0`
- What: Nonzero-index terms of the universal normalised EDS are nonzero polynomials.
- How: assume `= 0`, `apply_fun aeval (Param.rec 2 3 2)`, simplify via `normEDS_two_three_two` to `n = 0`.
- Hypotheses: `n ≠ 0`.
- Uses from project: [universalNormEDS, normEDS, map_normEDS, normEDS_two_three_two]
- Used by: universalNormEDS_mem_nonZeroDivisors
- Visibility: public
- Lines: 1190-1193 (proof ~3 lines)
- Notes: none

### lemma universalNormEDS_mem_nonZeroDivisors
- Type: `{n : ℤ} (hn : n ≠ 0) : universalNormEDS n ∈ (MvPolynomial Param ℤ)⁰`
- What: Nonzero-index terms of the universal EDS are non-zero-divisors (it's a domain).
- How: `mem_nonZeroDivisors_of_ne_zero (universalNormEDS_ne_zero hn)`.
- Hypotheses: `n ≠ 0`.
- Uses from project: [universalNormEDS, universalNormEDS_ne_zero]
- Used by: normEDS_mul_complEDS
- Visibility: public
- Lines: 1195-1197 (proof 1 line)
- Notes: none

### theorem IsEllSequence.eq_normEDS_of_dvd
- Type: `(one two : ... ∈ R⁰) (dvd₁₂ dvd₁₃ dvd₂₄) : ∃ b c d, W = (W 1 * normEDS b c d ·)` (section adds `dvd₁₂ : W 1 ∣ W 2` etc.)
- What: An elliptic sequence with non-zero-divisor first two terms and the three base divisibilities is a constant (`W 1`) multiple of a normalised EDS.
- How: extract witnesses `b,c,d` from the three `∣`, apply `ellW.ext (IsEllSequence.normEDS.smul _)` discharging the four base equalities.
- Hypotheses: `W` elliptic; `W 1, W 2 ∈ R⁰`; `W 1 ∣ W 2`, `W 1 ∣ W 3`, `W 2 ∣ W 4`.
- Uses from project: [normEDS, IsEllSequence.normEDS, IsEllSequence.smul, IsEllSequence.ext, normEDS_four]
- Used by: IsEllDivSequence.eq_normEDS, IsEllSequence.isDivSequence_of_dvd
- Visibility: public
- Lines: 1205-1208 (proof ~3 lines)
- Notes: none

### theorem IsEllDivSequence.eq_normEDS
- Type: `(h : IsEllDivSequence W) : ∃ b c d, W = (W 1 * normEDS b c d ·)`
- What: An EDS with non-zero-divisor first two terms is a constant multiple of a normalised EDS.
- How: `h.1.eq_normEDS_of_dvd` feeding the three divisibilities from `h.2` (`W m ∣ W (k*m)`).
- Hypotheses: `W` an EDS; `W 1, W 2 ∈ R⁰` (the `one two dvd*` in scope).
- Uses from project: [IsEllDivSequence, normEDS, IsEllSequence.eq_normEDS_of_dvd]
- Used by: unused in file
- Visibility: public
- Lines: 1212-1214 (proof ~2 lines)
- Notes: none

### lemma IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors
- Type: `(W₁ compl₂ : ℤ → R) (h₁ : ∀ m, W 1 * W₁ m = W m) (h₂ : ∀ m, W m * compl₂ m = W (2*m)) (m n : ℤ) (mem : W m ∈ R⁰) : W m * compl W₁ compl₂ m n = W (n*m)`
- What: For an elliptic sequence with non-zero-divisor first terms, `W(m)·compl(m,n) = W(n·m)`.
- How: `Int.negInduction`; nat case via `n.strong_induction_on`, unfolding `compl`/`compl'` and using the recurrence `ellW ((k+...)*m) ((k+...)*m) 1`, `h₁`, `h₂`, the inductive hypotheses, and `mul_cancel_right_mem_nonZeroDivisors`; neg case via `ellW.neg`/`compl_neg`.
- Hypotheses: `W` elliptic; `W 1, W 2 ∈ R⁰`; the two definitional identities `h₁, h₂`; `W m ∈ R⁰`.
- Uses from project: [EllSequence.compl, EllSequence.compl', EllSequence.compl_ofNat, EllSequence.compl_neg, IsEllSequence, IsEllSequence.zero, IsEllSequence.neg]
- Used by: normEDS_mul_complEDS
- Visibility: public (namespace IsEllSequence)
- Lines: 1225-1248 (proof ~23 lines)
- Notes: none

### lemma normEDS_mul_complEDS
- Type: `(m n : ℤ) : normEDS b c d m * complEDS b c d m n = normEDS b c d (n*m)`
- What: For `normEDS`, `W(m)·complEDS(m,n) = W(n·m)` (the `EllSequence.complEDS`).
- How: case `m=0` by `simp`; else reduce to the universal case via `normEDS_eq_aeval`/`complEDS_eq_aeval`, apply `IsEllSequence.normEDS.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors` with `universalNormEDS_mem_nonZeroDivisors` and `normEDS_mul_compl₂EDS`.
- Hypotheses: none.
- Uses from project: [normEDS, EllSequence.complEDS, normEDS_eq_aeval, universalNormEDS, complEDS_eq_aeval, IsEllSequence.normEDS, IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors, universalNormEDS_mem_nonZeroDivisors, normEDS_mul_compl₂EDS]
- Used by: normEDS_mul_complEDS_div, IsDivSequence.normEDS
- Visibility: public
- Lines: 1250-1256 (proof ~5 lines)
- Notes: none

### lemma normEDS_mul_complEDS_div
- Type: `(hm : m ≠ 0) (n : ℤ) (dvd : m ∣ n) : normEDS b c d m * complEDS b c d m (n/m) = normEDS b c d n`
- What: Divided form: when `m ∣ n`, `W(m)·complEDS(m, n/m) = W(n)`.
- How: obtain `n = m*n'` from `dvd`, `Int.mul_ediv_cancel_left`, `normEDS_mul_complEDS`, `mul_comm`.
- Hypotheses: `m ≠ 0`; `m ∣ n`.
- Uses from project: [normEDS, EllSequence.complEDS, normEDS_mul_complEDS]
- Used by: invarDenom_eq_redInvarDenom_mul (`mul_eq`)
- Visibility: public
- Lines: 1258-1261 (proof ~2 lines)
- Notes: none

### def EllSequence.redInvarNum
- Type: `(b c d) (m : ℤ) : R := compl₂EDS b c d m + normEDS b c d m^3 * b + 2 * compl₂EDSAux b c d m` (`variable (b c d)`)
- What: Numerator of the reduced invariant `(W(m-1)²W(m+2)+W(m-2)W(m+1)²+W₂²W(m)³)/W₂`, after cancelling `W₃W₂ = bc`.
- How: Direct definition.
- Hypotheses: none.
- Uses from project: [compl₂EDS, normEDS, compl₂EDSAux]
- Used by: compl₂EDS_eq_redInvarNum_sub, invarNum_eq_redInvarNum_mul, map_redInvarNum, redInvar_normEDS_of_mem_nonZeroDivisors, redInvar_normEDS
- Visibility: public (namespace EllSequence)
- Lines: 1269-1270 (def, 1 line)
- Notes: none

### lemma EllSequence.compl₂EDS_eq_redInvarNum_sub
- Type: `: compl₂EDS b c d m = redInvarNum b c d m - normEDS b c d m^3 * b - 2 * compl₂EDSAux b c d m`
- What: Solves the `redInvarNum` definition for `compl₂EDS`.
- How: `rw [redInvarNum]; ring`.
- Hypotheses: none.
- Uses from project: [compl₂EDS, redInvarNum, normEDS, compl₂EDSAux]
- Used by: unused in file
- Visibility: public (namespace)
- Lines: 1272-1275 (proof 1 line)
- Notes: none

### lemma EllSequence.invarNum_eq_redInvarNum_mul
- Type: `: invarNum (normEDS b c d) 1 m = redInvarNum b c d m * b`
- What: `invarNum (normEDS) 1 m` equals `b · redInvarNum(m)`.
- How: `simp_rw [redInvarNum, right_distrib, compl₂EDS_mul_b, ..., compl₂EDSAux_mul_b, invarNum_normEDS]; ring`.
- Hypotheses: none.
- Uses from project: [invarNum, normEDS, redInvarNum, compl₂EDS_mul_b, compl₂EDSAux_mul_b, invarNum_normEDS]
- Used by: redInvar_normEDS_of_mem_nonZeroDivisors
- Visibility: public (namespace)
- Lines: 1277-1279 (proof ~2 lines)
- Notes: none

### def EllSequence.redInvarDenom
- Type: `(b c d) (m : ℤ) : R := ...` six-way `if m % 6 = i` branch in `complEDS`/`normEDS` terms (`C := complEDS`, `W := normEDS`, `r₆ := normEDS 5 - d^2`)
- What: The expression `W(m+1)W(m)W(m-1)/(W₃W₂)` for `normEDS`, given by residue of `m` mod 6.
- How: Direct definition with nested `if m % 6 = k`.
- Hypotheses: none.
- Uses from project: [EllSequence.complEDS, normEDS]
- Used by: invarDenom_eq_redInvarDenom_mul, redInvarDenom_zero/one/two, map_redInvarDenom, redInvar_normEDS_of_mem_nonZeroDivisors, redInvar_normEDS
- Visibility: public (namespace)
- Lines: 1282-1291 (def, ~9 lines)
- Notes: none

### lemma EllSequence.invarDenom_eq_redInvarDenom_mul
- Type: `: invarDenom (normEDS b c d) 1 m = redInvarDenom b c d m * b * c`
- What: `invarDenom (normEDS) 1 m` equals `b·c · redInvarDenom(m)`.
- How: set up divisibility helpers `hd/hd2/hd3` (`Int.dvd_iff_emod_eq_zero`, `Int.emod_emod_of_dvd`), `split_ifs` on the six residues; each branch rewrites via `normEDS_mul_complEDS_div` and `normEDS_six_eq_mul`/`normEDS_three`/`normEDS_two`, then `ring`; the leftover impossible residue closed by `interval_cases`.
- Hypotheses: none.
- Uses from project: [invarDenom, normEDS, redInvarDenom, normEDS_mul_complEDS_div, normEDS_six_eq_mul, normEDS_three, normEDS_two]
- Used by: redInvar_normEDS_of_mem_nonZeroDivisors
- Visibility: public (namespace)
- Lines: 1293-1317 (proof ~24 lines)
- Notes: long(30-50)? — proof is ~24 lines (under 30); comment "-- slow" at line 1302; uses `interval_cases`.

### lemma EllSequence.redInvarDenom_zero
- Type: `: redInvarDenom b c d 0 = 0` (`@[simp]`)
- What: `redInvarDenom` at 0 is 0.
- How: `simp [redInvarDenom, complEDS, compl', compl]`.
- Hypotheses: none.
- Uses from project: [EllSequence.redInvarDenom, EllSequence.complEDS, EllSequence.compl', EllSequence.compl]
- Used by: unused in file (simp lemma)
- Visibility: public (namespace)
- Lines: 1319-1320 (proof 1 line)
- Notes: none

### lemma EllSequence.redInvarDenom_one
- Type: `: redInvarDenom b c d 1 = 0` (`@[simp]`)
- What: `redInvarDenom` at 1 is 0.
- How: `simp [redInvarDenom, complEDS, compl', compl]`.
- Hypotheses: none.
- Uses from project: [EllSequence.redInvarDenom, EllSequence.complEDS, EllSequence.compl', EllSequence.compl]
- Used by: unused in file (simp lemma)
- Visibility: public (namespace)
- Lines: 1322-1323 (proof 1 line)
- Notes: none

### lemma EllSequence.redInvarDenom_two
- Type: `: redInvarDenom b c d 2 = 1` (`@[simp]`)
- What: `redInvarDenom` at 2 is 1.
- How: `simp [redInvarDenom, complEDS, compl', compl]`.
- Hypotheses: none.
- Uses from project: [EllSequence.redInvarDenom, EllSequence.complEDS, EllSequence.compl', EllSequence.compl]
- Used by: unused in file (simp lemma)
- Visibility: public (namespace)
- Lines: 1325-1326 (proof 1 line)
- Notes: none

### lemma EllSequence.map_compl₂EDSAux
- Type: `: f (compl₂EDSAux b c d m) = compl₂EDSAux (f b) (f c) (f d) m`
- What: `f` commutes with `compl₂EDSAux`.
- How: `simp [compl₂EDSAux, apply_ite f, map_preNormEDS]`.
- Hypotheses: none.
- Uses from project: [compl₂EDSAux, map_preNormEDS]
- Used by: map_redInvarNum
- Visibility: public (namespace)
- Lines: 1328-1329 (proof 1 line)
- Notes: none

### lemma EllSequence.map_redInvarNum
- Type: `: f (redInvarNum b c d m) = redInvarNum (f b) (f c) (f d) m`
- What: `f` commutes with `redInvarNum`.
- How: `simp [redInvarNum, map_compl₂EDS, map_normEDS, map_compl₂EDSAux]`.
- Hypotheses: none.
- Uses from project: [EllSequence.redInvarNum, map_compl₂EDS, map_normEDS, EllSequence.map_compl₂EDSAux]
- Used by: redInvar_normEDS
- Visibility: public (namespace)
- Lines: 1331-1332 (proof 1 line)
- Notes: none

### lemma EllSequence.map_redInvarDenom
- Type: `: f (redInvarDenom b c d m) = redInvarDenom (f b) (f c) (f d) m`
- What: `f` commutes with `redInvarDenom`.
- How: `simp [redInvarDenom, apply_ite f, map_normEDS, map_complEDS]`.
- Hypotheses: none.
- Uses from project: [EllSequence.redInvarDenom, map_normEDS, map_complEDS]
- Used by: redInvar_normEDS
- Visibility: public (namespace)
- Lines: 1334-1335 (proof 1 line)
- Notes: none

### theorem IsDivSequence.normEDS
- Type: `protected : IsDivSequence (normEDS b c d)`
- What: A normalised EDS is a divisibility sequence.
- How: `rintro m _ ⟨n, rfl⟩`, `rw [mul_comm, ← normEDS_mul_complEDS]`, `dvd_mul_right`.
- Hypotheses: none.
- Uses from project: [IsDivSequence, normEDS, normEDS_mul_complEDS]
- Used by: IsEllDivSequence.normEDS, IsEllSequence.isDivSequence_of_dvd
- Visibility: public (protected)
- Lines: 1342-1345 (proof ~3 lines)
- Notes: none

### theorem IsEllDivSequence.normEDS
- Type: `protected : IsEllDivSequence (normEDS b c d)`
- What: A normalised EDS is an EDS (the headline result `isEllDivSequence_normEDS`).
- How: `⟨IsEllSequence.normEDS, IsDivSequence.normEDS⟩`.
- Hypotheses: none.
- Uses from project: [IsEllDivSequence, normEDS, IsEllSequence.normEDS, IsDivSequence.normEDS]
- Used by: unused in file
- Visibility: public (protected)
- Lines: 1347-1349 (proof 1 line)
- Notes: none — corresponds to the documented main statement `isEllDivSequence_normEDS`.

### lemma IsEllSequence.isDivSequence_of_dvd
- Type: `: IsDivSequence W` (section hyps `one two dvd₁₂ dvd₁₃ dvd₂₄`, `ellW`)
- What: An elliptic sequence satisfying the three base divisibilities (with non-zero-divisor first terms) is a divisibility sequence.
- How: `eq_normEDS_of_dvd` to write `W = W 1 • normEDS`, then `IsDivSequence.normEDS.smul`.
- Hypotheses: `W` elliptic; `W 1, W 2 ∈ R⁰`; the three base `∣`.
- Uses from project: [IsDivSequence, IsEllSequence.eq_normEDS_of_dvd, IsDivSequence.normEDS, IsDivSequence.smul]
- Used by: IsEllSequence.isEllDivSequence_of_dvd
- Visibility: public (namespace)
- Lines: 1353-1355 (proof ~2 lines)
- Notes: none

### lemma IsEllSequence.isEllDivSequence_of_dvd
- Type: `: IsEllDivSequence W`
- What: Such an elliptic sequence is in fact an EDS.
- How: `⟨ellW, ellW.isDivSequence_of_dvd one two dvd₁₂ dvd₁₃ dvd₂₄⟩`.
- Hypotheses: same as above.
- Uses from project: [IsEllDivSequence, IsEllSequence.isDivSequence_of_dvd]
- Used by: unused in file
- Visibility: public (namespace)
- Lines: 1357-1358 (proof 1 line)
- Notes: none

### lemma net_normEDS
- Type: `(p q r s : ℤ) : net (normEDS b c d) p q r s = 0`
- What: All net relations vanish for a normalised EDS.
- How: `rw [normEDS_eq_aeval, ← Function.comp, ← map_net, universalNormEDS, IsEllSequence.normEDS.net, map_zero]`, discharging non-zero-divisor side conditions via `normEDS_one`/`normEDS_two`, `one_ne_zero`, `X_ne_zero`.
- Hypotheses: none.
- Uses from project: [net, normEDS, normEDS_eq_aeval, map_net, universalNormEDS, IsEllSequence.normEDS, IsEllSequence.net, normEDS_one, normEDS_two]
- Used by: rel₄_normEDS, invar_normEDS
- Visibility: public
- Lines: 1364-1368 (proof ~4 lines)
- Notes: none

### lemma rel₄_normEDS
- Type: `(p q r s : ℤ) (same : HaveSameParity₄ p q r s) : rel₄ (normEDS b c d) p q r s = 0`
- What: Every same-parity `rel₄` vanishes for a normalised EDS.
- How: `rw [same.rel₄_eq_net, net_normEDS]`.
- Hypotheses: same parity.
- Uses from project: [rel₄, normEDS, HaveSameParity₄, HaveSameParity₄.rel₄_eq_net, net_normEDS]
- Used by: unused in file
- Visibility: public
- Lines: 1370-1372 (proof 1 line)
- Notes: none

### lemma invar_normEDS
- Type: `(s m n : ℤ) : invarNum (normEDS b c d) s m * invarDenom (normEDS b c d) s n = invarNum (normEDS b c d) s n * invarDenom (normEDS b c d) s m`
- What: The invariant is `n`-independent for a normalised EDS.
- How: `invar_of_net _ net_normEDS _ _ _`.
- Hypotheses: none.
- Uses from project: [invarNum, invarDenom, normEDS, invar_of_net, net_normEDS]
- Used by: invar₂_normEDS_of_mem_nonZeroDivisors
- Visibility: public
- Lines: 1374-1377 (proof ~3 lines)
- Notes: none

### lemma invar₂_normEDS_of_mem_nonZeroDivisors
- Type: `private (hb : b ∈ R⁰) (m : ℤ) : invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b^4)`
- What: The specific invariant relation at `s = 1`, `n = 2`, under `b ∈ R⁰`.
- How: cancel `hb` via `mul_cancel_right_mem_nonZeroDivisors`, then `convert invar_normEDS 1 m 2` using `invarNum_normEDS_two`/`invarDenom_normEDS_two`.
- Hypotheses: `b ∈ R⁰`.
- Uses from project: [invarNum, invarDenom, normEDS, invar_normEDS, invarNum_normEDS_two, invarDenom_normEDS_two]
- Used by: invar₂_normEDS
- Visibility: private
- Lines: 1379-1382 (proof ~2 lines)
- Notes: none

### lemma invar₂_normEDS
- Type: `{m : ℤ} : invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b^4)` (`open MvPolynomial Param in`)
- What: The invariant relation at `s = 1`, `n = 2`, unconditionally (no `hb`).
- How: apply `aeval (Param.rec b c d)` to the universal-case `invar₂_normEDS_of_mem_nonZeroDivisors` (with `c := X C`, `d := X D`, `X_ne_zero B`), then `simpa` via `map_invarNum`/`map_invarDenom`/`normEDS_eq_aeval`.
- Hypotheses: none.
- Uses from project: [invarNum, invarDenom, normEDS, invar₂_normEDS_of_mem_nonZeroDivisors, universalNormEDS, map_invarNum, map_invarDenom, normEDS_eq_aeval]
- Used by: redInvar_normEDS_of_mem_nonZeroDivisors
- Visibility: public
- Lines: 1384-1391 (proof ~5 lines)
- Notes: none

### lemma redInvar_normEDS_of_mem_nonZeroDivisors
- Type: `private (hb : b ∈ R⁰) (hc : c ∈ R⁰) (m : ℤ) : redInvarNum b c d m = redInvarDenom b c d m * (d + b^4)`
- What: The reduced invariant relation `redInvarNum = redInvarDenom·(d+b⁴)`, under `b,c ∈ R⁰`.
- How: cancel `hb`,`hc`, rewrite via `invarNum_eq_redInvarNum_mul`, `invar₂_normEDS`, `invarDenom_eq_redInvarDenom_mul`, `ring`.
- Hypotheses: `b, c ∈ R⁰`.
- Uses from project: [EllSequence.redInvarNum, EllSequence.redInvarDenom, EllSequence.invarNum_eq_redInvarNum_mul, invar₂_normEDS, EllSequence.invarDenom_eq_redInvarDenom_mul]
- Used by: redInvar_normEDS
- Visibility: private
- Lines: 1393-1397 (proof ~3 lines)
- Notes: none

### lemma redInvar_normEDS
- Type: `(m : ℤ) : redInvarNum b c d m = redInvarDenom b c d m * (d + b^4)` (`open MvPolynomial Param in`)
- What: The reduced invariant relation, unconditionally.
- How: apply `aeval (Param.rec b c d)` to the universal case `redInvar_normEDS_of_mem_nonZeroDivisors` (with `X B/C/D`, side goals `X_ne_zero`), then `simpa` via `map_redInvarNum`/`map_redInvarDenom`.
- Hypotheses: none.
- Uses from project: [EllSequence.redInvarNum, EllSequence.redInvarDenom, redInvar_normEDS_of_mem_nonZeroDivisors, EllSequence.map_redInvarNum, EllSequence.map_redInvarDenom]
- Used by: unused in file
- Visibility: public
- Lines: 1399-1405 (proof ~4 lines)
- Notes: none

### def complEDS' (top-level, ComplEDS section)
- Type: `(b c d : R) (k : ℤ) : ℕ → R` (recursive: 0↦0, 1↦1, n+2 parity-split using `complEDS₂`/`normEDS`)
- What: The complement sequence `Wᶜ : ℤ×ℕ → R` witnessing `W(k) ∣ W(n·k)`; `W(k)·Wᶜ(k,n) = W(n·k)`. Agrees with `complEDS₂` at `n = 2`.
- How: Well-founded recursion on `ℕ` with decreasing proof `m+1 < n+2`, branching on `Even n`.
- Hypotheses: none.
- Uses from project: [complEDS₂, normEDS]
- Used by: complEDS'_zero/one, complEDS'_even, complEDS'_odd, complEDS (top-level), complEDS_ofNat, map_complEDS' (the `@[simp]` Map version)
- Visibility: public
- Lines: 1419-1427 (def, ~8 lines)
- Notes: none — distinct from `EllSequence.compl'`.

### lemma complEDS'_zero
- Type: `: complEDS' b c d k 0 = 0` (`@[simp]`)
- What: `complEDS'` at 0 is 0.
- How: `rw [complEDS']`.
- Hypotheses: none.
- Uses from project: [complEDS' (top-level)]
- Used by: map_complEDS' (via simp)
- Visibility: public
- Lines: 1429-1431 (proof 1 line)
- Notes: none

### lemma complEDS'_one
- Type: `: complEDS' b c d k 1 = 1` (`@[simp]`)
- What: `complEDS'` at 1 is 1.
- How: `rw [complEDS']`.
- Hypotheses: none.
- Uses from project: [complEDS' (top-level)]
- Used by: map_complEDS'
- Visibility: public
- Lines: 1433-1435 (proof 1 line)
- Notes: none

### lemma complEDS'_even
- Type: `(m : ℕ) : complEDS' b c d k (2*(m+1)) = complEDS' b c d k (m+1) * complEDS₂ b c d ((m+1)*k)`
- What: Even-index unfolding of `complEDS'`.
- How: rewrite `2(m+1)=2m+2`, `complEDS'`, `dif_pos (even_two_mul m)`, `mul_div_cancel_left`.
- Hypotheses: none.
- Uses from project: [complEDS' (top-level), complEDS₂]
- Used by: complEDS_even, map_complEDS'
- Visibility: public
- Lines: 1437-1440 (proof ~2 lines)
- Notes: none

### lemma complEDS'_odd
- Type: `(m : ℕ) : complEDS' b c d k (2*(m+1)+1) = (odd-branch recurrence)`
- What: Odd-index unfolding of `complEDS'`.
- How: rewrite `2(m+1)+1=2m+3`, `complEDS'`, `dif_neg (not_even_two_mul_add_one)`, `Nat.mul_add_div`.
- Hypotheses: none.
- Uses from project: [complEDS' (top-level), normEDS]
- Used by: complEDS_odd, map_complEDS'
- Visibility: public
- Lines: 1442-1448 (proof ~2 lines)
- Notes: none

### def complEDS (top-level)
- Type: `(b c d : R) (k : ℤ) (n : ℤ) : R := n.sign * complEDS' b c d k n.natAbs`
- What: The ℤ-indexed complement sequence `Wᶜ : ℤ×ℤ → R` witnessing `W(k) ∣ W(n·k)` (odd extension of the top-level `complEDS'`).
- How: Direct definition.
- Hypotheses: none.
- Uses from project: [complEDS' (top-level)]
- Used by: complEDS_ofNat/zero/one/neg, complEDS_even, complEDS_odd, map_complEDS (the `@[simp]` version)
- Visibility: public
- Lines: 1454-1455 (def, 1 line)
- Notes: none — NOTE: shadows the earlier `EllSequence.complEDS`; this top-level `complEDS` has signature `(b c d k n)`, the namespaced one `(b c d m n)` indirectly via `compl`.

### lemma complEDS_ofNat
- Type: `(n : ℕ) : complEDS b c d k n = complEDS' b c d k n` (`@[simp]`)
- What: On naturals, top-level `complEDS` agrees with `complEDS'`.
- How: case `n=0` by `simp`; else `Int.sign_natCast_of_ne_zero`.
- Hypotheses: none.
- Uses from project: [complEDS (top-level), complEDS' (top-level)]
- Used by: complEDS_even, complEDS_odd
- Visibility: public
- Lines: 1457-1461 (proof ~2 lines)
- Notes: none

### lemma complEDS_zero
- Type: `: complEDS b c d k 0 = 0` (`@[simp]`)
- What: top-level `complEDS` at 0 is 0.
- How: `simp [complEDS]`.
- Hypotheses: none.
- Uses from project: [complEDS (top-level)]
- Used by: unused in file (simp lemma)
- Visibility: public
- Lines: 1463-1465 (proof 1 line)
- Notes: none

### lemma complEDS_one
- Type: `: complEDS b c d k 1 = 1` (`@[simp]`)
- What: top-level `complEDS` at 1 is 1.
- How: `simp [complEDS]`.
- Hypotheses: none.
- Uses from project: [complEDS (top-level)]
- Used by: unused in file (simp lemma)
- Visibility: public
- Lines: 1467-1469 (proof 1 line)
- Notes: none

### lemma complEDS_neg
- Type: `(n : ℤ) : complEDS b c d k (-n) = -complEDS b c d k n` (`@[simp]`)
- What: top-level `complEDS` is odd in `n`.
- How: `simp [complEDS]`.
- Hypotheses: none.
- Uses from project: [complEDS (top-level)]
- Used by: complEDS_odd
- Visibility: public
- Lines: 1471-1473 (proof 1 line)
- Notes: none

### lemma complEDS_even
- Type: `(m : ℤ) : complEDS b c d k (2*m) = complEDS b c d k m * complEDS₂ b c d (m*k)`
- What: The even-index recurrence for the top-level `complEDS` over ℤ.
- How: `Int.negInduction`; nat case via `complEDS'_even` (`rcases`/`norm_cast`); neg case via `complEDS_neg`/`complEDS₂_neg`.
- Hypotheses: none.
- Uses from project: [complEDS (top-level), complEDS₂, complEDS_ofNat, complEDS'_even, complEDS_neg, complEDS₂_neg]
- Used by: unused in file
- Visibility: public
- Lines: 1475-1483 (proof ~7 lines)
- Notes: none

### lemma complEDS_odd
- Type: `(m : ℤ) : complEDS b c d k (2*m+1) = (odd recurrence in complEDS/normEDS)`
- What: The odd-index recurrence for the top-level `complEDS` over ℤ.
- How: `Int.negInduction`; nat case via `complEDS'_odd`; neg case rewrites the negative indices and uses `complEDS_neg`/`normEDS_neg` + inductive hypothesis + `ring1`.
- Hypotheses: none.
- Uses from project: [complEDS (top-level), normEDS, complEDS_ofNat, complEDS'_odd, complEDS_neg, normEDS_neg]
- Used by: unused in file
- Visibility: public
- Lines: 1485-1500 (proof ~13 lines)
- Notes: none

### def complEDSRec'
- Type: `noncomputable {P : ℕ → Sort u} (zero one) (even : ∀ m, (∀ k < 2*(m+1), P k) → P (2*(m+1))) (odd : ∀ m, (∀ k < 2*(m+1)+1, P k) → P (2*(m+1)+1)) (n : ℕ) : P n` (`@[elab_as_elim]`)
- What: Strong recursion principle for the complement sequence (ℕ-indexed).
- How: `Nat.evenOddStrongRec` with `rintro` case-splits feeding `zero/even` and `one/odd`.
- Hypotheses: base cases `P 0, P 1`, even/odd strong recursors.
- Uses from project: []
- Used by: complEDSRec, map_complEDS' (the `@[simp]` version, `induction ... using complEDSRec'`)
- Visibility: public (noncomputable)
- Lines: 1507-1512 (proof ~2 lines)
- Notes: none — NOTE: the docstring mentions `2*(m+3)`/`2*(m+2)+1` but the actual signature uses `2*(m+1)` (docstring copy artifact).

### def complEDSRec
- Type: `noncomputable {P} (zero one) (even : ∀ m, P(m+1) → P(2*(m+1))) (odd : ∀ m, P(m+1) → P(m+2) → P(2*(m+1)+1)) (n) : P n` (`@[elab_as_elim]`)
- What: Recursion principle for the complement sequence with finite predecessors.
- How: reduces to `complEDSRec'`, supplying predecessors via `ih _ <| by linarith only`.
- Hypotheses: base cases + finitary even/odd steps.
- Uses from project: [complEDSRec']
- Used by: unused in file
- Visibility: public (noncomputable)
- Lines: 1521-1526 (proof ~2 lines)
- Notes: none — docstring `2*(m+3)`/`2*(m+2)+1` is a copy artifact (signature uses `2*(m+1)`).

### lemma map_preNormEDS' (Map section 2, `@[simp]`)
- Type: `(n : ℕ) : f (preNormEDS' b c d n) = preNormEDS' (f b) (f c) (f d) n` (`variable {S} [CommRing S] (f : R →+* S)`)
- What: A genuine ring hom `f : R →+* S` commutes with `preNormEDS'`.
- How: `induction n using normEDSRec'`; base cases by `simp`; step `simp only [preNormEDS'_even/odd, ...]` + `repeat rw [ih ...]`.
- Hypotheses: none.
- Uses from project: [preNormEDS', normEDSRec', preNormEDS'_even, preNormEDS'_odd]
- Used by: map_preNormEDS (the `@[simp]` version)
- Visibility: public
- Lines: 1534-1544 (proof ~9 lines)
- Notes: none — duplicate name of the earlier `map_preNormEDS'` (1068); this one is `@[simp]` and over `R →+* S`.

### lemma map_preNormEDS (Map section 2, `@[simp]`)
- Type: `(n : ℤ) : f (preNormEDS b c d n) = preNormEDS (f b) (f c) (f d) n`
- What: `f : R →+* S` commutes with `preNormEDS`.
- How: `simp [preNormEDS]`.
- Hypotheses: none.
- Uses from project: [preNormEDS]
- Used by: unused in file (within this section)
- Visibility: public
- Lines: 1546-1548 (proof 1 line)
- Notes: none — duplicate name of 1079.

### lemma map_complEDS₂ (Map section 2, `@[simp]`)
- Type: `(n : ℤ) : f (complEDS₂ b c d n) = complEDS₂ (f b) (f c) (f d) n`
- What: `f : R →+* S` commutes with `complEDS₂`.
- How: `simp [complEDS₂, apply_ite f]`.
- Hypotheses: none.
- Uses from project: [complEDS₂]
- Used by: map_complEDS' (the `@[simp]` version)
- Visibility: public
- Lines: 1550-1552 (proof 1 line)
- Notes: none

### lemma map_normEDS (Map section 2, `@[simp]`)
- Type: `(n : ℤ) : f (normEDS b c d n) = normEDS (f b) (f c) (f d) n`
- What: `f : R →+* S` commutes with `normEDS`.
- How: `simp [normEDS, apply_ite f]`.
- Hypotheses: none.
- Uses from project: [normEDS]
- Used by: map_complEDS' (the `@[simp]` version)
- Visibility: public
- Lines: 1554-1556 (proof 1 line)
- Notes: none — duplicate name of 1082.

### lemma map_complEDS' (Map section 2, `@[simp]`)
- Type: `(k : ℤ) (n : ℕ) : f (complEDS' b c d k n) = complEDS' (f b) (f c) (f d) k n`
- What: `f : R →+* S` commutes with the top-level `complEDS'`.
- How: `induction n using complEDSRec'`; base by `simp`; step `simp only [complEDS'_even/odd, map_*]` + `repeat rw [ih ...]`.
- Hypotheses: none.
- Uses from project: [complEDS' (top-level), complEDSRec', complEDS'_even, complEDS'_odd, map_normEDS, map_complEDS₂]
- Used by: map_complEDS (the `@[simp]` version)
- Visibility: public
- Lines: 1558-1566 (proof ~7 lines)
- Notes: none

### lemma map_complEDS (Map section 2, `@[simp]`)
- Type: `(k n : ℤ) : f (complEDS b c d k n) = complEDS (f b) (f c) (f d) k n`
- What: `f : R →+* S` commutes with the top-level `complEDS`.
- How: `simp [complEDS]`.
- Hypotheses: none.
- Uses from project: [complEDS (top-level), map_complEDS']
- Used by: unused in file
- Visibility: public
- Lines: 1568-1570 (proof 1 line)
- Notes: none — duplicate name of the earlier `map_complEDS` (1104) which referred to `EllSequence.complEDS`.

---

## File Summary

- **Total declarations documented: 138.**
  - **defs / structures / inductives / recursors: 28** — `addMulSub`, `rel₄`, `net`, `Rel₃`, `IsEllSequence`, `invarNum`, `invarDenom`, `StrictAnti₄`, `HaveSameParity₄`, `avg₄`, `HaveSameParity₄.addMulSub₄`, `rel₆`, `OddRec`, `EvenRec`, `dMin`, `cMin`, `Rel₄OfValid`, `relFin4`, `IsDivSequence`, `IsEllDivSequence`, `preNormEDS'`, `preNormEDS`, `complEDS₂`, `normEDS`, `normEDSRec'`, `normEDSRec`, `compl₂EDSAux`, `compl₂EDS`, `EllSequence.compl'`, `EllSequence.compl`, `EllSequence.complEDS`, `Param`, `universalNormEDS`, `EllSequence.redInvarNum`, `EllSequence.redInvarDenom`, `complEDS'` (top), `complEDS` (top), `complEDSRec'`, `complEDSRec`. (40 def-like items; the "28" undercount is corrected here — there are **40** def/inductive/recursor declarations.)
  - **lemmas + theorems: 98.**
  - **instances: 0.**
  (Recount: 40 def-like + 98 lemma/theorem = 138 total.)
- **Key API (used by ≥3 in-file decls):** `addMulSub`, `rel₄`, `net`, `Rel₃`, `IsEllSequence`, `invarNum`, `invarDenom`, `HaveSameParity₄`, `StrictAnti₄`, `avg₄`, `rel₆`, `OddRec`, `EvenRec`, `dMin`, `cMin`, `Rel₄OfValid`, `IsDivSequence`, `IsEllDivSequence`, `preNormEDS'`, `preNormEDS`, `preNormEDS_neg`, `complEDS₂`, `normEDS`, `normEDS_one`, `normEDS_two`, `normEDS_neg`, `compl₂EDSAux`, `compl₂EDS`, `compl₂EDS_neg`, `normEDS_mul_compl₂EDS`, `EllSequence.compl'`, `EllSequence.compl`, `EllSequence.complEDS`, `Param`, `universalNormEDS`, `normEDS_eq_aeval`, `map_preNormEDS`, `map_normEDS`, `map_compl₂EDS`, `EllSequence.redInvarNum`, `EllSequence.redInvarDenom`, `rel₄_of_oddRec_evenRec`, `rel₄_of_anti_oddRec_evenRec`, `IsEllSequence.neg`, `IsEllSequence.zero`, `complEDS'` (top), `complEDS` (top).
- **Unused decls (no in-file consumer; many are public API / `@[simp]` boundary lemmas):** `net_add_sub_iff`, `addMulSub_two_zero`, `addMulSub_three_one`, `addMulSub_sq_mul_rel₄_eq₉`, `isEllDivSequence_id`, `IsEllDivSequence.smul`, `IsEllDivSequence.map`, `IsEllSequence.zero'`, `IsEllSequence.invar`, `preNormEDS_zero`, `preNormEDS_three`, `normEDS_def`, `normEDS_ofNat`, `normEDS_dvd_normEDS_two_mul`, `normEDS_dvd_two_mul`, `compl₂EDS_mul_b`, `compl₂EDSAux_neg`, `complEDS₂_one/two/three/four`, `compl₂EDSAux_zero/one/neg_one/two/neg_two`, `compl₂EDS_zero/one/two`, `compl₂EDS_eq_aeval`, `compl₂EDS_eq_redInvarNum_sub`, `EllSequence.redInvarDenom_zero/one/two`, `IsEllDivSequence.eq_normEDS`, `IsEllDivSequence.normEDS`, `IsEllSequence.isEllDivSequence_of_dvd`, `rel₄_normEDS`, `redInvar_normEDS`, `compl₂EDS_two_three_two`, `complEDS_zero/one`, `complEDS_even`, `complEDS_odd`, `complEDSRec`, `map_preNormEDS`(2nd)/`map_complEDS`(2nd) of the final Map section, and most `@[simp]` value lemmas (`normEDS_zero..neg`, `preNormEDS_*`, `complEDS₂_*`, etc.) whose consumers are downstream files. (These are library boundary lemmas — "unused in file" does not mean dead.)
- **Decls with `sorry`: none.**
- **Decls with `set_option`: none.**
- **Proofs > 50 lines: none (0).**
- **Proofs 30–50 lines: 1** — `rel₄_of_anti_oddRec_evenRec` (lines 454–484, ~30 lines; the central inductive argument, flagged long(30-50)). Borderline-near-30: `IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors` (~23), `invarDenom_eq_redInvarDenom_mul` (~24), `rel₄_of_oddRec_evenRec` (~16), `rel₄_of_min₂` (~15) — all under 30, no flag.
- **Notable structural points:** (1) Several declaration **names are reused** across sections — `map_preNormEDS'`, `map_preNormEDS`, `map_normEDS`, `map_complEDS` each appear twice (a `FunLike`-class version in the first Map section ~1068–1105 and a `@[simp]` `R →+* S` version in the final Map section ~1534–1570); and **`complEDS`/`complEDS'`** denote two genuinely different sequences (the `EllSequence.complEDS := compl (normEDS) (compl₂EDS)` at 1058 vs. the top-level `complEDS'`/`complEDS` at 1419/1454 built directly from `complEDS₂` and `normEDS`). A consolidation pass should disambiguate these. (2) `erw` is used in `IsEllSequence.ext` (lines 1168, 1172). (3) The `complEDSRec'`/`complEDSRec` docstrings carry copy-pasted `2*(m+3)` bounds that do not match their `2*(m+1)` signatures.

Output written to: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/NagellLutz/.mathlib-quality/overview/inventory/LutzNagell_EllipticDivisibilitySequenceOriginal.md`

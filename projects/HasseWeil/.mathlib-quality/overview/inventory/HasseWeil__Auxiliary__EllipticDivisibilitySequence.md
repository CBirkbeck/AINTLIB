# Inventory: ./HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean

**File**: `HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean`
**Lines**: 1063
**Authors**: Junyan Xu, David Kurniadi Angdinata (ported from LutzNagell project)
**Purpose**: Additional lemmas for normalised elliptic divisibility sequences (EDS) needed for division polynomial / ZSMul development.

---

## Namespace `EllSequence`

### `def addMulSub`
- **Type**: `(W : ℤ → R) → (m n : ℤ) → R`
- **What**: Defines the building block `W((m+n)/2) * W((m-n)/2)` used in elliptic relations; uses integer truncated division `tdiv`.
- **How**: Direct definition; no proof.
- **Hypotheses**: `R` a commutative ring.
- **Uses from project**: []
- **Used by**: `rel₄`, `net`, `addMulSub_even`, `addMulSub_odd`, `addMulSub_same`, `addMulSub_neg₀`, `addMulSub_neg₁`, `addMulSub_abs₀`, `addMulSub_abs₁`, `addMulSub_swap`, `map_addMulSub`, `rel₃_iff₄`, `addMulSub_mem_nonZeroDivisors`, `addMulSub₄_mul_addMulSub₄`, `addMulSub_transf`, `rel₄_abs`, `rel₄_swap₀₁`, `rel₄_swap₁₂`, `rel₄_swap₂₃`
- **Visibility**: public
- **Lines**: 40–40 (definition only)
- **Notes**: Core algebraic building block; used throughout the file.

---

### `def rel₄`
- **Type**: `(W : ℤ → R) → (a b c d : ℤ) → R`
- **What**: The four-index elliptic relation: `addMulSub W a b * addMulSub W c d - addMulSub W a c * addMulSub W b d + addMulSub W a d * addMulSub W b c`, encoding the three partitions of four same-parity indices into pairs.
- **How**: Direct definition using `addMulSub`.
- **Hypotheses**: `R` a commutative ring.
- **Uses from project**: [`addMulSub`]
- **Used by**: `net_eq_rel₄`, `rel₃_iff₄`, `rel₄_eq_net`, `rel₄_transf`, `rel₄_abs`, `rel₄_swap₀₁`, `rel₄_swap₁₂`, `rel₄_swap₂₃`, `rel₆`, `rel₄_same₀₁`, `rel₄_same₁₂`, `rel₄_same₂₃`, `rel₄_of_oddRec_evenRec`, `rel₄_iff_evenRec`, `IsEllSequence.rel₄`, `map_rel₄`, `Rel₄OfValid`, `relFin4`, `rel₄_fix₁_of_fix₂`, `rel₄_of_fix₂`
- **Visibility**: public
- **Lines**: 45–47 (definition only)
- **Notes**: Central algebraic object; used by nearly every subsequent lemma.

---

### `def net`
- **Type**: `(W : ℤ → R) → (p q r s : ℤ) → R`
- **What**: Stange's elliptic net relation: `W(p+q+s)*W(p-q)*W(r+s)*W(r) - W(p+r+s)*W(p-r)*W(q+s)*W(q) + W(q+r+s)*W(q-r)*W(p+s)*W(p)`.
- **How**: Direct definition.
- **Hypotheses**: `R` a commutative ring.
- **Uses from project**: []
- **Used by**: `net_eq_rel₄`, `net_add_sub_iff`, `map_net`, `invar_of_net`, `IsEllSequence.net`, `net_normEDS`
- **Visibility**: public
- **Lines**: 51–55 (definition only)

---

### `lemma net_eq_rel₄`
- **Type**: `net W p q r s = rel₄ W (2*p+s) (2*q+s) (2*r+s) s`
- **What**: Expresses the net relation as a four-index elliptic relation at doubled shifted indices.
- **How**: `simp_rw` with `net`, `rel₄`, `addMulSub` definitions + `ring`.
- **Hypotheses**: none beyond ring context.
- **Uses from project**: [`net`, `rel₄`, `addMulSub`]
- **Used by**: `map_net`, `rel₄_eq_net`, `IsEllSequence.net`
- **Visibility**: public
- **Lines**: 57–62 (5 lines)

---

### `lemma net_add_sub_iff`
- **Type**: `net W (m+n) m (m-n) n = 0 ↔ W(2*(m+n))*W(m-n)*W(m)*W(n) = (W(2*m+n)*W(2*n)*W(m) - W(m+2*n)*W(2*m)*W(n)) * W(m+n)`
- **What**: Rewrites the specialised net vanishing at `(m+n, m, m-n, n)` as a polynomial identity.
- **How**: `simp_rw` arithmetic + `linear_combination`.
- **Hypotheses**: none.
- **Uses from project**: [`net`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 64–74 (10 lines)

---

### `def Rel₃`
- **Type**: `(W : ℤ → R) → (m n r : ℤ) → Prop`
- **What**: Three-index elliptic relation: `W(m+n)*W(m-n)*W(r)^2 = W(m+r)*W(m-r)*W(n)^2 - W(n+r)*W(n-r)*W(m)^2`.
- **How**: Direct definition.
- **Hypotheses**: `R` a commutative ring.
- **Uses from project**: []
- **Used by**: `isEllSequence_iff_rel₃`, `rel₃_iff_oddRec`, `rel₃_iff_evenRec`, `rel₃_iff₄`, `IsEllSequence.of_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 77–79 (definition only)

---

### `lemma isEllSequence_iff_rel₃`
- **Type**: `IsEllSequence W ↔ ∀ m n r, Rel₃ W m n r`
- **What**: `IsEllSequence` unfolds to the universal `Rel₃` property.
- **How**: `Iff.rfl` (definitional equality).
- **Hypotheses**: none.
- **Uses from project**: [`Rel₃`]
- **Used by**: unused in file (documentation lemma)
- **Visibility**: public
- **Lines**: 82–82 (1 line)

---

### `def invarNum`
- **Type**: `(W : ℤ → R) → (s n : ℤ) → R`
- **What**: Numerator of an invariant of an elliptic sequence: `(W(n+2s)*W(n-s)^2 + W(n+s)^2*W(n-2s))*W(s)^2 + W(n)^3*W(2s)^2`.
- **How**: Direct definition.
- **Hypotheses**: `R` a commutative ring.
- **Uses from project**: []
- **Used by**: `map_invarNum`, `invar_of_net`, `invarNum_normEDS`, `invarNum_normEDS_two`, `invarNum_eq_redInvarNum_mul`, `invar_normEDS`, `invar₂_normEDS`, `invar₂_normEDS_of_mem_nonZeroDivisors`, `IsEllSequence.invar`
- **Visibility**: public
- **Lines**: 86–88 (definition only)

---

### `def invarDenom`
- **Type**: `(W : ℤ → R) → (s n : ℤ) → R`
- **What**: Denominator of the same invariant: `W(n+s) * W(n) * W(n-s)`.
- **How**: Direct definition.
- **Hypotheses**: `R` a commutative ring.
- **Uses from project**: []
- **Used by**: `map_invarDenom`, `invar_of_net`, `invarDenom_normEDS_two`, `invarDenom_normEDS_eq_redInvarDenom_mul`, `invar_normEDS`, `invar₂_normEDS`, `invar₂_normEDS_of_mem_nonZeroDivisors`, `IsEllSequence.invar`
- **Visibility**: public
- **Lines**: 91–91 (definition only)

---

### `theorem invar_of_net`
- **Type**: `(net_eq_zero : ∀ p q r s, net W p q r s = 0) → (s m n : ℤ) → invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m`
- **What**: Cross-multiplication invariant: given that the net vanishes universally, `invarNum(s,m)/invarDenom(s,m)` is independent of `m`.
- **How**: `simp_rw` unfolding + `linear_combination` from four instantiations of `net_eq_zero`. Uses `set_option allowUnsafeReducibility`.
- **Hypotheses**: Net vanishes universally.
- **Uses from project**: [`invarNum`, `invarDenom`, `net`]
- **Used by**: `IsEllSequence.invar`, `invar_normEDS`
- **Visibility**: public
- **Lines**: 95–102 (7 lines)
- **Notes**: Uses `allowUnsafeReducibility` attribute for `Nat.rawCast`.

---

### `lemma addMulSub_even`
- **Type**: `addMulSub W (2*m) (2*n) = W(m+n) * W(m-n)`
- **What**: Simplification of `addMulSub` at even indices.
- **How**: `simp_rw` with `Int.mul_tdiv_cancel_left`.
- **Uses from project**: [`addMulSub`]
- **Used by**: `rel₃_iff₄`
- **Visibility**: public
- **Lines**: 104–106

---

### `lemma addMulSub_odd`
- **Type**: `addMulSub W (2*m+1) (2*n+1) = W(m+n+1) * W(m-n)`
- **What**: Simplification of `addMulSub` at odd indices.
- **How**: Arithmetic rewrites using `Int.mul_tdiv_cancel_left`.
- **Uses from project**: [`addMulSub`]
- **Used by**: `rel₄_iff_evenRec`
- **Visibility**: public
- **Lines**: 108–111

---

### `lemma addMulSub_same`
- **Type**: `(zero : W 0 = 0) → addMulSub W m m = 0`
- **What**: `addMulSub W m m = 0` when `W 0 = 0` (since `m - m = 0`).
- **How**: Unfold, `sub_self`, apply zero hypothesis.
- **Uses from project**: [`addMulSub`]
- **Used by**: `rel₄_same₀₁`, `rel₄_same₁₂`, `rel₄_same₂₃`
- **Visibility**: public
- **Lines**: 113–115

---

### `lemma addMulSub_neg₀`
- **Type**: `(neg : ∀ k, W(-k) = -W k) → addMulSub W (-m) n = addMulSub W m n`
- **What**: `addMulSub` is even in its first argument given oddness of `W`.
- **Uses from project**: [`addMulSub`]
- **Used by**: `addMulSub_abs₀`, `addMulSub_swap`
- **Visibility**: public
- **Lines**: 116–118

---

### `lemma addMulSub_neg₁`
- **Type**: `addMulSub W m (-n) = addMulSub W m n`
- **What**: `addMulSub` is even in its second argument unconditionally (the two factors just swap).
- **Uses from project**: [`addMulSub`]
- **Used by**: `addMulSub_abs₁`
- **Visibility**: public
- **Lines**: 120–121

---

### `lemma addMulSub_abs₀`
- **Type**: `(neg : ...) → addMulSub W |m| n = addMulSub W m n`
- **What**: Replace first argument by its absolute value.
- **Uses from project**: [`addMulSub`, `addMulSub_neg₀`]
- **Used by**: `rel₄_abs`, `addMulSub_transf`
- **Visibility**: public
- **Lines**: 123–125

---

### `lemma addMulSub_abs₁`
- **Type**: `addMulSub W m |n| = addMulSub W m n`
- **What**: Replace second argument by its absolute value.
- **Uses from project**: [`addMulSub`, `addMulSub_neg₁`]
- **Used by**: `addMulSub_transf`
- **Visibility**: public
- **Lines**: 127–128

---

### `lemma addMulSub_swap`
- **Type**: `(neg : ...) → addMulSub W m n = -addMulSub W n m`
- **What**: Swapping arguments negates `addMulSub`.
- **Uses from project**: [`addMulSub`, `addMulSub_neg₀`]
- **Used by**: `rel₄_swap₀₁`, `rel₄_swap₁₂`, `rel₄_swap₂₃`
- **Visibility**: public
- **Lines**: 130–132

---

### `lemma map_addMulSub`
- **Type**: `f (addMulSub W m n) = addMulSub (f ∘ W) m n`
- **What**: Ring homomorphism naturality for `addMulSub`.
- **Uses from project**: [`addMulSub`]
- **Used by**: `map_rel₄`
- **Visibility**: public
- **Lines**: 138–139

---

### `lemma map_rel₄`
- **Type**: `f (rel₄ W p q r s) = rel₄ (f ∘ W) p q r s`
- **What**: Ring homomorphism naturality for `rel₄`.
- **Uses from project**: [`rel₄`, `map_addMulSub`]
- **Used by**: `map_net`
- **Visibility**: public
- **Lines**: 141–142

---

### `lemma map_net`
- **Type**: `f (net W p q r s) = net (f ∘ W) p q r s`
- **What**: Ring homomorphism naturality for `net`.
- **Uses from project**: [`net_eq_rel₄`, `map_rel₄`]
- **Used by**: `net_normEDS`
- **Visibility**: public
- **Lines**: 144–145

---

### `lemma map_invarNum`
- **Type**: `f (invarNum W s m) = invarNum (f ∘ W) s m`
- **What**: Ring homomorphism naturality for `invarNum`.
- **Uses from project**: [`invarNum`]
- **Used by**: `invar₂_normEDS`
- **Visibility**: public
- **Lines**: 147–148

---

### `lemma map_invarDenom`
- **Type**: `f (invarDenom W s m) = invarDenom (f ∘ W) s m`
- **What**: Ring homomorphism naturality for `invarDenom`.
- **Uses from project**: [`invarDenom`]
- **Used by**: `invar₂_normEDS`
- **Visibility**: public
- **Lines**: 150–151

---

### `lemma rel₃_iff₄`
- **Type**: `Rel₃ W m n r ↔ rel₄ W (2*m) (2*n) (2*r) 0 = 0`
- **What**: Converts the three-index relation to the four-index relation at doubled indices.
- **How**: Unfold using `addMulSub_even`; algebraic manipulation.
- **Uses from project**: [`Rel₃`, `rel₄`, `addMulSub_even`]
- **Used by**: `IsEllSequence.of_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 155–159

---

### `def StrictAnti₄`
- **Type**: `(a b c d : ℤ) → Prop`
- **What**: Predicate saying the four indices are nonneg and strictly decreasing: `0 ≤ d < c < b < a`.
- **Uses from project**: []
- **Used by**: `six_le_of_strictAnti₄`, `strictAnti₄_transf`, `rel₄_of_anti_oddRec_evenRec`, `rel₄_of_min₂`, `rel₄_of_oddRec_evenRec`, `Rel₄OfValid`
- **Visibility**: public
- **Lines**: 166–166

---

### `def HaveSameParity₄`
- **Type**: `(a b c d : ℤ) → Prop`
- **What**: Predicate saying the four indices have the same parity (equal `negOnePow` values).
- **Uses from project**: []
- **Used by**: Most lemmas in the `transf` section, `rel₄_eq_net`, `even_sum`, `avg₄_add_avg₄`, `same₀₃`, `HaveSameParity₄.abs`, `perm`, `six_le_of_strictAnti₄`, `addMulSub_transf`, `rel₄_transf`, `transf`, `strictAnti₄_transf`, `rel₄_of_anti_oddRec_evenRec`, `rel₄_of_min₂`, `rel₄_of_oddRec_evenRec`, `Rel₄OfValid`, `IsEllSequence.rel₄`, `IsEllSequence.net`
- **Visibility**: public
- **Lines**: 169–170

---

### `def avg₄`
- **Type**: `(a b c d : ℤ) → ℤ`
- **What**: Average of four integers: `(a + b + c + d) / 2`.
- **Uses from project**: []
- **Used by**: `avg₄_add_avg₄`, `addMulSub_transf`, `rel₄_transf`, `transf`, `strictAnti₄_transf`, `rel₄_of_anti_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 173–173

---

### `lemma HaveSameParity₄.rel₄_eq_net` (within namespace)
- **Type**: `HaveSameParity₄ a b c d → rel₄ W a b c d = net W ((a-d)/2) ((b-d)/2) ((c-d)/2) d`
- **What**: Same-parity four-index relation equals the net at half-shifted indices.
- **How**: Uses `net_eq_rel₄` and `Int.two_mul_ediv_two_of_even` for the parity conditions.
- **Uses from project**: [`rel₄`, `net`, `net_eq_rel₄`, `HaveSameParity₄`]
- **Used by**: (within `HaveSameParity₄` namespace)
- **Visibility**: public
- **Lines**: 181–185

---

### `lemma HaveSameParity₄.even_sum`
- **Type**: `HaveSameParity₄ a b c d → Even (a + b + c + d)`
- **What**: Sum of four same-parity integers is even.
- **How**: Negation-power arithmetic + `units_mul_self`.
- **Uses from project**: [`HaveSameParity₄`]
- **Used by**: `avg₄_add_avg₄`
- **Visibility**: public
- **Lines**: 187–189

---

### `lemma HaveSameParity₄.avg₄_add_avg₄`
- **Type**: `HaveSameParity₄ a b c d → avg₄ a b c d + avg₄ a b c d = a + b + c + d`
- **What**: `2 * avg₄ = a + b + c + d` (exact, not just up to rounding).
- **Uses from project**: [`avg₄`, `HaveSameParity₄`, `even_sum`]
- **Used by**: `addMulSub_transf`, `strictAnti₄_transf`
- **Visibility**: public
- **Lines**: 191–192

---

### `lemma HaveSameParity₄.same₀₃`
- **Type**: `HaveSameParity₄ a b c d → a.negOnePow = d.negOnePow`
- **What**: First and fourth elements have the same parity.
- **Uses from project**: [`HaveSameParity₄`]
- **Used by**: `rel₄_of_min₂`
- **Visibility**: public
- **Lines**: 194–194

---

### `lemma HaveSameParity₄.abs`
- **Type**: `HaveSameParity₄ a b c d → HaveSameParity₄ |a| |b| |c| |d|`
- **What**: Same-parity is preserved under absolute value.
- **Uses from project**: [`HaveSameParity₄`]
- **Used by**: `rel₄_of_oddRec_evenRec`
- **Visibility**: public (protected)
- **Lines**: 196–197

---

### `lemma HaveSameParity₄.perm`
- **Type**: `∀ (σ : Perm (Fin 4)) (t : Fin 4 → ℤ), HaveSameParity₄ (t 0) (t 1) (t 2) (t 3) → HaveSameParity₄ (t (σ 0)) (t (σ 1)) (t (σ 2)) (t (σ 3))`
- **What**: Same-parity is invariant under permutation of the four indices.
- **How**: Induction on `Perm.mclosure_swap_castSucc_succ 3` via `Submonoid.closure_induction`; case analysis on adjacent transpositions.
- **Uses from project**: [`HaveSameParity₄`]
- **Used by**: `rel₄_of_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 200–211 (11 lines)

---

### `lemma HaveSameParity₄.six_le_of_strictAnti₄`
- **Type**: `HaveSameParity₄ a b c d → StrictAnti₄ a b c d → 6 ≤ a`
- **What**: A strictly decreasing same-parity nonneg quadruple must have its largest element at least 6.
- **How**: Parity conditions convert strict inequalities to `+2` steps; `linarith`.
- **Uses from project**: [`HaveSameParity₄`, `StrictAnti₄`]
- **Used by**: `rel₄_of_anti_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 213–218

---

### `def HaveSameParity₄.addMulSub₄` (within namespace, with `W`)
- **Type**: `(W : ℤ → R) → (a b c d : ℤ) → R`
- **What**: Hybrid product: `W((a+b)/2) * W((c-d)/2)`, combining one factor from each of two `addMulSub` expressions.
- **Uses from project**: []
- **Used by**: `addMulSub₄_mul_addMulSub₄`, `addMulSub_transf`, `rel₄_transf`
- **Visibility**: public
- **Lines**: 222–222

---

### `lemma addMulSub₄_mul_addMulSub₄`
- **Type**: `addMulSub₄ W a b c d * addMulSub₄ W c d a b = addMulSub W a b * addMulSub W c d`
- **What**: Product of the two hybrid factors recovers the original `addMulSub` product.
- **Uses from project**: [`addMulSub₄`, `addMulSub`]
- **Used by**: `rel₄_transf`
- **Visibility**: public
- **Lines**: 225–227

---

### `lemma addMulSub_transf`
- **Type**: Six-part conjunction expressing `addMulSub W (avg₄ - x) (avg₄ - y)` in terms of `addMulSub₄`.
- **What**: The six pairwise `addMulSub` values after the averaging transformation equal the six `addMulSub₄` values of the original indices.
- **How**: `simp_rw` with `addMulSub_abs₁`, `addMulSub`, `addMulSub₄`, `avg₄_add_avg₄`, then `ring_nf`. Uses `allowUnsafeReducibility`.
- **Uses from project**: [`addMulSub`, `addMulSub₄`, `avg₄`, `addMulSub_abs₁`, `HaveSameParity₄.avg₄_add_avg₄`]
- **Used by**: `rel₄_transf`
- **Visibility**: public
- **Lines**: 231–239 (8 lines)

---

### `theorem HaveSameParity₄.rel₄_transf`
- **Type**: `HaveSameParity₄ a b c d → rel₄ W (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| = rel₄ W a b c d`
- **What**: The four-index relation is invariant under the averaging transformation (shifting by `avg₄`).
- **How**: Uses `addMulSub_transf` to express both sides via `addMulSub₄`; applies `addMulSub₄_mul_addMulSub₄`; `ring`.
- **Uses from project**: [`rel₄`, `avg₄`, `HaveSameParity₄`, `addMulSub_transf`, `addMulSub₄_mul_addMulSub₄`]
- **Used by**: `rel₄_of_anti_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 241–245

---

### `theorem HaveSameParity₄.transf`
- **Type**: `HaveSameParity₄ a b c d → HaveSameParity₄ (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a|`
- **What**: The averaging transformation preserves the same-parity property.
- **Uses from project**: [`HaveSameParity₄`, `avg₄`]
- **Used by**: `rel₄_of_anti_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 247–249

---

### `theorem HaveSameParity₄.strictAnti₄_transf`
- **Type**: `HaveSameParity₄ a b c d → StrictAnti₄ a b c d → StrictAnti₄ (avg₄ - d) (avg₄ - c) (avg₄ - b) |avg₄ - a|`
- **What**: The averaging transformation preserves the strict antitonicity property.
- **How**: `abs_nonneg`, `abs_lt`, arithmetic inequalities via `linarith`.
- **Uses from project**: [`HaveSameParity₄`, `StrictAnti₄`, `avg₄`, `avg₄_add_avg₄`]
- **Used by**: `rel₄_of_anti_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 251–257

---

### `abbrev rel₆`
- **Type**: `(W : ℤ → R) → (k l a b c d : ℤ) → R`
- **What**: Six-index auxiliary: `addMulSub W k l * rel₄ W a b c d`. Used internally in the inductive reduction proofs.
- **Uses from project**: [`addMulSub`, `rel₄`]
- **Used by**: `rel₆_eq`, `rel₆_eq₃`, `rel₆_eq₃'`, `rel₆_eq₁₀`, `rel₄_fix₁_of_fix₂`, `rel₄_of_fix₂`
- **Visibility**: public
- **Lines**: 264–264

---

### `@[simp] lemma rel₆_eq`
- **Type**: `rel₆ W k l a b c d = addMulSub W k l * rel₄ W a b c d`
- **What**: Unfolds the abbreviation `rel₆`.
- **Uses from project**: [`rel₆`]
- **Used by**: `rel₄_fix₁_of_fix₂`, `rel₄_of_fix₂`
- **Visibility**: public
- **Lines**: 266–267

---

### `lemma rel₆_eq₃`
- **Type**: `rel₆ W c d m n r c = rel₆ W m c n r c d - rel₆ W n c m r c d + rel₆ W r c m n c d`
- **What**: Three-term identity for `rel₆` fixing the last index to `c`.
- **How**: `ring`.
- **Uses from project**: [`rel₆`]
- **Used by**: `rel₄_fix₁_of_fix₂`
- **Visibility**: public
- **Lines**: 269–271

---

### `lemma rel₆_eq₃'`
- **Type**: `rel₆ W c d m n r d = rel₆ W m d n r c d - rel₆ W n d m r c d + rel₆ W r d m n c d`
- **What**: Three-term identity for `rel₆` fixing the last index to `d`.
- **Uses from project**: [`rel₆`]
- **Used by**: `rel₄_fix₁_of_fix₂`
- **Visibility**: public
- **Lines**: 273–275

---

### `theorem rel₆_eq₁₀`
- **Type**: `rel₆ W c d m n r s = (nine-term linear combination of rel₆ values)`
- **What**: Ten-term identity expressing `rel₆ W c d m n r s` in terms of other `rel₆` values; key inductive step in the proof of the four-index relation from recurrences.
- **How**: `ring`.
- **Uses from project**: [`rel₆`]
- **Used by**: `rel₄_of_fix₂`
- **Visibility**: public
- **Lines**: 277–283

---

### `def OddRec`
- **Type**: `(W : ℤ → R) → (m : ℤ) → Prop`
- **What**: The recurrence relation for odd terms of a normalised EDS: `W(2m+1)*W(1)^3 = W(m+2)*W(m)^3 - W(m-1)*W(m+1)^3`.
- **Uses from project**: []
- **Used by**: `rel₃_iff_oddRec`, `IsEllSequence.oddRec`, `rel₄_of_anti_oddRec_evenRec`, `normEDS_of_mem_nonZeroDivisors`, `IsEllSequence.of_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 286–287

---

### `def EvenRec`
- **Type**: `(W : ℤ → R) → (m : ℤ) → Prop`
- **What**: The recurrence relation for even terms: `W(2m)*W(2)*W(1)^2 = W(m)*(W(m-1)^2*W(m+2) - W(m-2)*W(m+1)^2)`.
- **Uses from project**: []
- **Used by**: `rel₃_iff_evenRec`, `IsEllSequence.evenRec`, `rel₄_of_anti_oddRec_evenRec`, `normEDS_of_mem_nonZeroDivisors`, `IsEllSequence.of_oddRec_evenRec`, `rel₄_iff_evenRec`
- **Visibility**: public
- **Lines**: 290–291

---

### `lemma rel₃_iff_oddRec`
- **Type**: `Rel₃ W (m+1) m 1 ↔ OddRec W m`
- **What**: Specialisation of `Rel₃` at `(m+1, m, 1)` is the odd recurrence.
- **How**: `ring`.
- **Uses from project**: [`Rel₃`, `OddRec`]
- **Used by**: `IsEllSequence.oddRec`, `rel₄_of_anti_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 293–294

---

### `lemma rel₃_iff_evenRec`
- **Type**: `Rel₃ W (m+1) (m-1) 1 ↔ EvenRec W m`
- **What**: Specialisation of `Rel₃` at `(m+1, m-1, 1)` is the even recurrence.
- **How**: `ring_nf` with `allowUnsafeReducibility`.
- **Uses from project**: [`Rel₃`, `EvenRec`]
- **Used by**: `IsEllSequence.evenRec`, `rel₄_of_anti_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 298–299
- **Notes**: Uses `allowUnsafeReducibility`.

---

### `lemma rel₄_iff_evenRec`
- **Type**: `rel₄ W (2*m+1) (2*m-1) 3 1 = 0 ↔ EvenRec W m`
- **What**: The four-index relation at `(2m+1, 2m-1, 3, 1)` is equivalent to the even recurrence.
- **How**: `convert_to` + `addMulSub_odd` + `ring_nf`. Uses `allowUnsafeReducibility`.
- **Uses from project**: [`rel₄`, `EvenRec`, `addMulSub_odd`]
- **Used by**: `rel₄_of_anti_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 303–306
- **Notes**: Uses `allowUnsafeReducibility`.

---

### `def dMin`
- **Type**: `(a : ℤ) → ℤ`
- **What**: Minimal same-parity nonneg index for `a`: `0` if `a` is even, `1` if odd.
- **Uses from project**: []
- **Used by**: `dMin_nonneg`, `dMin_lt_cMin`, `negOnePow_cMin_eq_dMin`, `negOnePow_dMin`, `addMulSub_mem_nonZeroDivisors`, `dMin_le`, `rel₄_of_min₂`, `rel₄_of_anti_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 309–309

---

### `def cMin`
- **Type**: `(a : ℤ) → ℤ`
- **What**: Minimal third index: `dMin a + 2`.
- **Uses from project**: [`dMin`]
- **Used by**: `dMin_lt_cMin`, `negOnePow_cMin_eq_dMin`, `negOnePow_cMin`, `addMulSub_mem_nonZeroDivisors`, `rel₄_of_min₂`, `rel₄_of_anti_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 311–311

---

### `lemma dMin_nonneg`
- **Type**: `0 ≤ dMin a`
- **Uses from project**: [`dMin`]
- **Used by**: `rel₄_of_min₂`
- **Visibility**: public
- **Lines**: 313–313

---

### `lemma dMin_lt_cMin`
- **Type**: `dMin a < cMin a`
- **Uses from project**: [`dMin`, `cMin`]
- **Used by**: `rel₄_of_min₂`
- **Visibility**: public
- **Lines**: 315–315

---

### `lemma negOnePow_cMin_eq_dMin`
- **Type**: `(cMin a).negOnePow = (dMin a).negOnePow`
- **What**: `cMin` and `dMin` have the same parity.
- **Uses from project**: [`cMin`, `dMin`]
- **Used by**: `rel₄_of_min₂`
- **Visibility**: public
- **Lines**: 317–318

---

### `lemma negOnePow_dMin`
- **Type**: `(dMin a).negOnePow = a.negOnePow`
- **What**: `dMin a` has the same parity as `a`.
- **Uses from project**: [`dMin`]
- **Used by**: `negOnePow_cMin`, `rel₄_of_anti_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 320–322

---

### `lemma negOnePow_cMin`
- **Type**: `(cMin a).negOnePow = a.negOnePow`
- **Uses from project**: [`cMin`, `negOnePow_cMin_eq_dMin`, `negOnePow_dMin`]
- **Used by**: `rel₄_of_anti_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 325–326

---

### `lemma addMulSub_mem_nonZeroDivisors`
- **Type**: `(one : W 1 ∈ R⁰) → (two : W 2 ∈ R⁰) → (a : ℤ) → addMulSub W (cMin a) (dMin a) ∈ R⁰`
- **What**: The `addMulSub` at `(cMin a, dMin a)` is a nonzerodivisor, since it equals `W(1)*W(1)` or `W(2)*W(1)`.
- **Uses from project**: [`addMulSub`, `cMin`, `dMin`]
- **Used by**: `rel₄_of_min₂`
- **Visibility**: public
- **Lines**: 329–331

---

### `lemma dMin_le`
- **Type**: `(same : a.negOnePow = b.negOnePow) → (h : 0 ≤ b) → dMin a ≤ b`
- **What**: `dMin a` is the smallest nonneg integer with the same parity as `a`.
- **Uses from project**: [`dMin`]
- **Used by**: `rel₄_of_min₂`
- **Visibility**: public
- **Lines**: 333–335

---

### `def Rel₄OfValid`
- **Type**: `(W : ℤ → R) → (a b c d : ℤ) → Prop`
- **What**: `Rel₄OfValid W a b c d` is the statement that `rel₄ W a b c d = 0` holds whenever `a b c d` have the same parity and are strictly decreasing nonneg.
- **Uses from project**: [`HaveSameParity₄`, `StrictAnti₄`, `rel₄`]
- **Used by**: `rel₄_fix₁_of_fix₂`, `rel₄_of_fix₂`, `rel₄_of_min₂`, `rel₄_of_anti_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 344–345

---

### `lemma rel₄_fix₁_of_fix₂`
- **Type**: Given fixed lower bounds `c₀, d₀` and validity for all `a' ≤ a` with those bounds, derives validity for `a b c c₀` and (if `c₀ < c`) for `a b c d₀`.
- **What**: Inductive step: extends validity one index level.
- **How**: Cancels `addMulSub W c₀ d₀` (a nonzerodivisor) using the three-term identity `rel₆_eq₃`, `rel₆_eq₃'`.
- **Uses from project**: [`Rel₄OfValid`, `rel₄_fix₁_of_fix₂` (itself), `rel₆_eq`, `rel₆_eq₃`, `rel₆_eq₃'`]
- **Used by**: `rel₄_of_fix₂`, `rel₄_of_min₂`
- **Visibility**: public
- **Lines**: 351–363 (12 lines)

---

### `lemma rel₄_of_fix₂`
- **Type**: Given validity for `a' ≤ a` with fixed `c₀, d₀` bounds, derives `Rel₄OfValid W a b c d` for any `c₀ < d` with same parity as `d₀`.
- **What**: Extends induction to arbitrary upper index using the ten-term identity.
- **How**: `rel₆_eq₁₀` + cancellation via `addMulSub W c₀ d₀ ∈ R⁰`.
- **Uses from project**: [`Rel₄OfValid`, `rel₄_fix₁_of_fix₂`, `rel₆_eq`, `rel₆_eq₁₀`]
- **Used by**: `rel₄_of_min₂`
- **Visibility**: public
- **Lines**: 364–374 (10 lines)

---

### `theorem rel₄_of_min₂`
- **Type**: Given `W 1, W 2 ∈ R⁰` and `Rel₄OfValid W a b (cMin a) (dMin a)` for all `a' ≤ a, b`, derives `Rel₄OfValid W a b c d` for all `b c d`.
- **What**: Bootstraps validity from minimal indices to all valid quadruples.
- **How**: Combines `rel₄_fix₁_of_fix₂`, `rel₄_of_fix₂`, `dMin_le`, `negOnePow_cMin_eq_dMin`.
- **Uses from project**: [`Rel₄OfValid`, `rel₄_fix₁_of_fix₂`, `rel₄_of_fix₂`, `dMin_le`, `dMin_nonneg`, `dMin_lt_cMin`, `negOnePow_cMin_eq_dMin`, `addMulSub_mem_nonZeroDivisors`, `HaveSameParity₄.same₀₃`]
- **Used by**: `rel₄_of_anti_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 377–393 (16 lines)

---

### `theorem rel₄_of_anti_oddRec_evenRec`
- **Type**: Given `W 1, W 2 ∈ R⁰` and the odd/even recurrences for `m ≥ 2` / `m ≥ 3`, derives `∀ a b c d, Rel₄OfValid W a b c d`.
- **What**: From the recurrences, the four-index relation holds universally on valid quadruples.
- **How**: Strong induction via `Int.strongRec` with base case at 6, using `rel₄_transf`, `rel₄_of_min₂`, `rel₃_iff₄`, and the `*Rec` lemmas.
- **Uses from project**: [`Rel₄OfValid`, `rel₄_of_min₂`, `rel₄_transf`, `six_le_of_strictAnti₄`, `HaveSameParity₄.transf`, `HaveSameParity₄.strictAnti₄_transf`, `negOnePow_dMin`, `negOnePow_cMin`, `rel₃_iff_oddRec`, `rel₃_iff_evenRec`, `rel₄_iff_evenRec`, `rel₃_iff₄`]
- **Used by**: `rel₄_of_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 396–421 (25 lines)

---

### `lemma rel₄_abs`
- **Type**: `(neg : ∀ k, W(-k) = -W k) → rel₄ W |m| |n| |r| |s| = rel₄ W m n r s`
- **What**: Absolute values can be removed from a `rel₄` when `W` is odd.
- **Uses from project**: [`rel₄`, `addMulSub_abs₀`, `addMulSub_abs₁`]
- **Used by**: `rel₄_of_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 430–431

---

### `lemma rel₄_swap₀₁`, `rel₄_swap₁₂`, `rel₄_swap₂₃`
- **Type**: `(neg : ...) → rel₄ W m n r s = -rel₄ W n m r s` (and similar for positions 1,2 and 2,3)
- **What**: Swapping adjacent arguments of `rel₄` negates the result (anti-symmetry from `addMulSub_swap`).
- **Uses from project**: [`rel₄`, `addMulSub_swap`]
- **Used by**: `relFin4_perm`
- **Visibility**: public
- **Lines**: 433–440

---

### `def relFin4`
- **Type**: `(W : ℤ → R) → (t : Fin 4 → ℤ) → R`
- **What**: Four-index elliptic relation with tuple input: `rel₄ W (t 0) (t 1) (t 2) (t 3)`.
- **Uses from project**: [`rel₄`]
- **Used by**: `relFin4_perm`, `relFin4_perm'`, `rel₄_of_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 446–446

---

### `theorem relFin4_perm`
- **Type**: `(neg : ...) → ∀ (σ : Perm (Fin 4)) t, relFin4 W (t ∘ σ) = Perm.sign σ • relFin4 W t`
- **What**: `rel₄` is anti-symmetric under permutations of the four indices, with sign given by the sign of the permutation.
- **How**: Induction on the symmetric group via `Submonoid.closure_induction` on `Perm.mclosure_swap_castSucc_succ`; base cases use `rel₄_swap₀₁/₁₂/₂₃`.
- **Uses from project**: [`relFin4`, `rel₄_swap₀₁`, `rel₄_swap₁₂`, `rel₄_swap₂₃`]
- **Used by**: `relFin4_perm'`, `rel₄_of_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 449–460 (11 lines)

---

### `lemma relFin4_perm'`
- **Type**: `(neg : ...) → Perm.sign σ • relFin4 W (t ∘ σ) = relFin4 W t`
- **What**: Signed permutation of `relFin4` recovers the original.
- **Uses from project**: [`relFin4_perm`, `relFin4`]
- **Used by**: `rel₄_of_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 462–464

---

### `lemma rel₄_same₀₁`, `rel₄_same₁₂`, `rel₄_same₂₃`
- **Type**: `(zero : W 0 = 0) → rel₄ W m m r s = 0` (and similar)
- **What**: `rel₄` vanishes when two adjacent indices coincide.
- **Uses from project**: [`rel₄`, `addMulSub_same`]
- **Used by**: `rel₄_of_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 470–479

---

### `theorem rel₄_of_oddRec_evenRec`
- **Type**: `(neg : ...) (zero : W 0 = 0) (one two : ...) (oddRec : ...) (evenRec : ...) (same : HaveSameParity₄ a b c d) → rel₄ W a b c d = 0`
- **What**: Full result: from the recurrences, `rel₄` vanishes on same-parity quadruples.
- **How**: Sorts the absolute values via `Tuple.sort` + `Fin.revPerm`, reduces to the valid case via `relFin4_perm'`, handles equal-index degenerate cases, then invokes `rel₄_of_anti_oddRec_evenRec`.
- **Uses from project**: [`rel₄`, `rel₄_abs`, `relFin4`, `relFin4_perm'`, `rel₄_same₀₁`, `rel₄_same₁₂`, `rel₄_same₂₃`, `rel₄_of_anti_oddRec_evenRec`, `HaveSameParity₄.abs`, `HaveSameParity₄.perm`]
- **Used by**: `IsEllSequence.of_oddRec_evenRec`
- **Visibility**: public
- **Lines**: 485–506 (21 lines)

---

### `theorem _root_.IsEllSequence.of_oddRec_evenRec`
- **Type**: `(neg : ...) (zero : W 0 = 0) (one two : ...) (oddRec : ...) (evenRec : ...) → IsEllSequence W`
- **What**: If `W` satisfies oddness, zero condition, non-zerodivisor conditions, and the odd/even recurrences, then `W` is an elliptic sequence.
- **How**: Reduce `Rel₃` to `rel₄` via `rel₃_iff₄` and apply `rel₄_of_oddRec_evenRec`.
- **Uses from project**: [`rel₃_iff₄`, `rel₄_of_oddRec_evenRec`]
- **Used by**: `normEDS_of_mem_nonZeroDivisors`
- **Visibility**: public (at root namespace)
- **Lines**: 511–514

---

## Namespace `IsEllSequence`

### `lemma IsEllSequence.oddRec`
- **Type**: `IsEllSequence W → (m : ℤ) → OddRec W m`
- **What**: An elliptic sequence satisfies the odd recurrence at every index.
- **Uses from project**: [`OddRec`, `rel₃_iff_oddRec`]
- **Used by**: `IsEllSequence.rel₄`
- **Visibility**: public
- **Lines**: 529–529

---

### `lemma IsEllSequence.evenRec`
- **Type**: `IsEllSequence W → (m : ℤ) → EvenRec W m`
- **What**: An elliptic sequence satisfies the even recurrence at every index.
- **Uses from project**: [`EvenRec`, `rel₃_iff_evenRec`]
- **Used by**: `IsEllSequence.ext`
- **Visibility**: public
- **Lines**: 530–530

---

### `lemma IsEllSequence.zero`
- **Type**: `IsEllSequence W → (m : ℤ) → (mem : W(2m) ∈ R⁰) → W 0 = 0`
- **What**: The zeroth term of an elliptic sequence is zero, given a nonzerodivisor even term.
- **How**: Uses the elliptic relation at `(m, m, 2m)`: `W(2m)*W(0)*W(2m)^2 = 0`, then cancels the nonzerodivisor.
- **Uses from project**: []
- **Used by**: `IsEllSequence.rel₄`, `IsEllSequence.ext`
- **Visibility**: public
- **Lines**: 534–545 (11 lines)

---

### `lemma IsEllSequence.sub_add_neg_sub_mul_eq_zero`
- **Type**: `IsEllSequence W → (m n r : ℤ) → (W(m-n) + W(-(m-n))) * W(m+n) * W(r)^2 = 0`
- **What**: Auxiliary identity showing `W(k) + W(-k)` kills certain elliptic combinations.
- **How**: Adds two elliptic relations at `(m,n,r)` and `(n,m,r)` using `congr`.
- **Uses from project**: []
- **Used by**: `IsEllSequence.neg`
- **Visibility**: public
- **Lines**: 547–552

---

### `lemma IsEllSequence.neg`
- **Type**: `IsEllSequence W → (one : W 1 ∈ R⁰) → (two : W 2 ∈ R⁰) → (m : ℤ) → W(-m) = -W m`
- **What**: An elliptic sequence with first two terms nonzerodivisors is an odd function.
- **How**: Case splits on parity of `m`; cancels `W(2)^{} * W(1)^2` (or `W(1)^3`) using `sub_add_neg_sub_mul_eq_zero`.
- **Uses from project**: [`sub_add_neg_sub_mul_eq_zero`]
- **Used by**: `IsEllSequence.rel₄`, `IsEllSequence.ext`
- **Visibility**: public
- **Lines**: 558–570 (12 lines)

---

### `protected lemma IsEllSequence.rel₄`
- **Type**: `IsEllSequence W → (one : W 1 ∈ R⁰) → (two : W 2 ∈ R⁰) → (same : HaveSameParity₄ a b c d) → rel₄ W a b c d = 0`
- **What**: An elliptic sequence satisfies `rel₄` on same-parity quadruples.
- **How**: Applies `rel₄_of_oddRec_evenRec` using the derived `neg`, `zero`, `oddRec`, `evenRec`.
- **Uses from project**: [`rel₄_of_oddRec_evenRec`, `IsEllSequence.neg`, `IsEllSequence.zero`, `IsEllSequence.oddRec`, `IsEllSequence.evenRec`]
- **Used by**: `IsEllSequence.net`
- **Visibility**: public
- **Lines**: 572–575

---

### `protected lemma IsEllSequence.net`
- **Type**: `IsEllSequence W → (one : W 1 ∈ R⁰) → (two : W 2 ∈ R⁰) → (p q r s : ℤ) → net W p q r s = 0`
- **What**: The elliptic net relation vanishes for any elliptic sequence.
- **How**: `net_eq_rel₄` + `IsEllSequence.rel₄` with the same-parity check.
- **Uses from project**: [`net_eq_rel₄`, `IsEllSequence.rel₄`]
- **Used by**: `IsEllSequence.invar`, `net_normEDS`
- **Visibility**: public
- **Lines**: 577–580

---

### `lemma IsEllSequence.invar`
- **Type**: `IsEllSequence W → (one : W 1 ∈ R⁰) → (two : W 2 ∈ R⁰) → (s m n : ℤ) → invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m`
- **What**: The invariant cross-multiplication property for any elliptic sequence.
- **Uses from project**: [`invar_of_net`, `IsEllSequence.net`]
- **Used by**: (exported; used by callers of the project)
- **Visibility**: public
- **Lines**: 582–584

---

### `private theorem normEDS_of_mem_nonZeroDivisors`
- **Type**: `(hb : b ∈ R⁰) → IsEllSequence (normEDS b c d)`
- **What**: A normalised EDS is an elliptic sequence, given `b` is a nonzerodivisor.
- **How**: Applies `IsEllSequence.of_oddRec_evenRec` using the mathlib lemmas `normEDS_neg`, `normEDS_zero`, `normEDS_one`, `normEDS_two`, `normEDS_odd`, `normEDS_even`.
- **Uses from project**: [`IsEllSequence.of_oddRec_evenRec`]
- **Used by**: `IsEllSequence.normEDS`
- **Visibility**: private
- **Lines**: 594–608 (14 lines)

---

### `lemma invarNum_normEDS`
- **Type**: `invarNum (normEDS b c d) 1 n = W(n+2)*W(n-1)^2 + W(n+1)^2*W(n-2) + W(n)^3*b^2`
- **What**: Computes `invarNum` for a normalised EDS at `s = 1`.
- **Uses from project**: [`invarNum`]
- **Used by**: `invarNum_eq_redInvarNum_mul`, `invarNum_normEDS_two`, `invar₂_normEDS`
- **Visibility**: public
- **Lines**: 617–620

---

### `lemma invarNum_normEDS_two`
- **Type**: `invarNum (normEDS b c d) 1 2 = (d + b^4) * b`
- **What**: Evaluates `invarNum` at `n = 2` for normalised EDS.
- **Uses from project**: [`invarNum`, `invarNum_normEDS`]
- **Used by**: `invar₂_normEDS_of_mem_nonZeroDivisors`
- **Visibility**: public
- **Lines**: 622–624

---

### `lemma invarDenom_normEDS_two`
- **Type**: `invarDenom (normEDS b c d) 1 2 = c * b`
- **What**: Evaluates `invarDenom` at `n = 2` for normalised EDS.
- **Uses from project**: [`invarDenom`]
- **Used by**: `invar₂_normEDS_of_mem_nonZeroDivisors`
- **Visibility**: public
- **Lines**: 626–628

---

### `lemma normEDS_six_eq_mul`
- **Type**: `normEDS b c d 6 = (normEDS b c d 5 - d^2) * b * c`
- **What**: Evaluates `normEDS` at index 6 in terms of index 5 and the parameters.
- **How**: Direct computation using `normEDS_mul_complEDS₂`, `complEDS₂`, `normEDS_three`, `normEDS`, `preNormEDS_*`.
- **Uses from project**: []
- **Used by**: `invarDenom_normEDS_eq_redInvarDenom_mul`
- **Visibility**: public
- **Lines**: 630–634

---

### `inductive Param`
- **Type**: `Type`
- **What**: Three-element type `{B, C, D}` indexing the three parameters of a normalised EDS.
- **Uses from project**: []
- **Used by**: `universalNormEDS`, `normEDS_eq_aeval`, `complEDS₂_eq_aeval`, `complEDS_eq_aeval`, `IsEllSequence.normEDS`, `universalNormEDS_ne_zero`, `universalNormEDS_mem_nonZeroDivisors`, `normEDS_mul_complEDS`, `net_normEDS`, `invar₂_normEDS`, `redInvar_normEDS`
- **Visibility**: public
- **Lines**: 645–645

---

### `noncomputable def universalNormEDS`
- **Type**: `ℤ → MvPolynomial Param ℤ`
- **What**: The universal normalised EDS with polynomial coefficients `X B, X C, X D` in `ℤ[B, C, D]`, from which every normalised EDS is obtained by specialisation.
- **Uses from project**: [`Param`]
- **Used by**: `normEDS_eq_aeval`, `universalNormEDS_ne_zero`, `universalNormEDS_mem_nonZeroDivisors`, `normEDS_mul_complEDS`, `net_normEDS`, `invar₂_normEDS`
- **Visibility**: public
- **Lines**: 651–651

---

### `lemma normEDS_eq_aeval`
- **Type**: `normEDS b c d = (MvPolynomial.aeval (Param.rec b c d) ∘ universalNormEDS)`
- **What**: Every specialised normalised EDS is obtained from the universal one by applying `aeval`.
- **Uses from project**: [`universalNormEDS`, `Param`]
- **Used by**: `IsEllSequence.normEDS`, `universalNormEDS_ne_zero`, `normEDS_mul_complEDS`, `net_normEDS`, `invar₂_normEDS`, `redInvar_normEDS`
- **Visibility**: public
- **Lines**: 653–657

---

### `lemma complEDS₂_eq_aeval`
- **Type**: `complEDS₂ b c d = (MvPolynomial.aeval (Param.rec b c d) ∘ complEDS₂ (X B) (X C) (X D))`
- **What**: `complEDS₂` also specialises from its universal version.
- **Uses from project**: [`Param`]
- **Used by**: (not used within file; exported)
- **Visibility**: public
- **Lines**: 659–663

---

### `lemma complEDS_eq_aeval`
- **Type**: `complEDS b c d = (MvPolynomial.aeval (Param.rec b c d) ∘ complEDS (X B) (X C) (X D))`
- **What**: `complEDS` also specialises from its universal version.
- **Uses from project**: [`Param`]
- **Used by**: `normEDS_mul_complEDS`
- **Visibility**: public
- **Lines**: 665–669

---

### `private lemma IsEllSequence.map'`
- **Type**: `IsEllSequence W → (f : R →+* S) → IsEllSequence (f ∘ W)`
- **What**: Ring homomorphisms preserve the elliptic sequence property.
- **How**: Applies `congr_arg f` to the three-index relation.
- **Uses from project**: []
- **Used by**: `IsEllSequence.normEDS`
- **Visibility**: private
- **Lines**: 680–682

---

### `protected theorem IsEllSequence.normEDS`
- **Type**: `IsEllSequence (normEDS b c d)`
- **What**: A normalised EDS over any commutative ring is an elliptic sequence (no nonzerodivisor hypothesis).
- **How**: Universalises to the polynomial ring (where `X B ∈ R⁰` trivially) via `normEDS_eq_aeval` and `IsEllSequence.map'` applied to `normEDS_of_mem_nonZeroDivisors`.
- **Uses from project**: [`normEDS_eq_aeval`, `normEDS_of_mem_nonZeroDivisors`, `IsEllSequence.map'`]
- **Used by**: `IsEllDivSequence.normEDS`, `IsEllSequence.ext`, `normEDS_two_three_two`, `invar_normEDS`, `net_normEDS`, `invar₂_normEDS`, `redInvar_normEDS`
- **Visibility**: public
- **Lines**: 685–688

---

### `protected theorem IsEllSequence.ext`
- **Type**: `IsEllSequence W → IsEllSequence U → (one : W 1 ∈ R⁰) → (two : W 2 ∈ R⁰) → W 1 = U 1 → W 2 = U 2 → W 3 = U 3 → W 4 = U 4 → W = U`
- **What**: Two elliptic sequences with the same first four terms are equal everywhere, provided the first two terms are nonzerodivisors.
- **How**: Induction using `normEDSRec` (reduces to the recurrence); the negative case uses `IsEllSequence.neg`; the positive cases use `evenRec` / `oddRec` plus cancellation.
- **Uses from project**: [`IsEllSequence.zero`, `IsEllSequence.neg`, `IsEllSequence.evenRec`, `IsEllSequence.oddRec`]
- **Used by**: `normEDS_two_three_two`
- **Visibility**: public
- **Lines**: 700–715 (15 lines)

---

### `lemma normEDS_two_three_two`
- **Type**: `normEDS (2 : ℤ) 3 2 = id`
- **What**: The normalised EDS with parameters `(2, 3, 2)` is the identity sequence `n ↦ n`.
- **How**: `IsEllSequence.ext` with `isEllSequence_id` plus explicit evaluation at 1, 2, 3, 4.
- **Uses from project**: [`IsEllSequence.ext`, `IsEllSequence.normEDS`]
- **Used by**: `complEDS₂_two_three_two`, `universalNormEDS_ne_zero`
- **Visibility**: public
- **Lines**: 722–726

---

### `lemma complEDS₂_two_three_two`
- **Type**: `complEDS₂ (2 : ℤ) 3 2 n = 2`
- **What**: The 2-complement EDS with parameters `(2, 3, 2)` is constantly 2.
- **How**: `normEDS_mul_complEDS₂` + `normEDS_two_three_two` + cancellation.
- **Uses from project**: [`normEDS_two_three_two`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 729–735

---

### `private lemma universalNormEDS_ne_zero`
- **Type**: `(hn : n ≠ 0) → universalNormEDS n ≠ 0`
- **What**: The universal normalised EDS is nonzero at every nonzero index.
- **How**: Specialises to `(2, 3, 2)` via `aeval` and uses `normEDS_two_three_two` + `id` = `n ≠ 0`.
- **Uses from project**: [`universalNormEDS`, `normEDS_eq_aeval`, `normEDS_two_three_two`]
- **Used by**: `universalNormEDS_mem_nonZeroDivisors`
- **Visibility**: private
- **Lines**: 738–745

---

### `private lemma universalNormEDS_mem_nonZeroDivisors`
- **Type**: `(hn : n ≠ 0) → universalNormEDS n ∈ (MvPolynomial Param ℤ)⁰`
- **What**: The universal normalised EDS at any nonzero index is a nonzerodivisor (since `MvPolynomial Param ℤ` is a domain).
- **Uses from project**: [`universalNormEDS`, `universalNormEDS_ne_zero`]
- **Used by**: `normEDS_mul_complEDS`
- **Visibility**: private
- **Lines**: 747–749

---

### `private lemma normEDS_mul_complEDS_of_mem`
- **Type**: `(hb : b ∈ R⁰) → (hm : normEDS b c d m ∈ R⁰) → (n : ℤ) → normEDS b c d m * complEDS b c d m n = normEDS b c d (n * m)`
- **What**: Multiplication formula: `normEDS(m) * complEDS(m, n) = normEDS(n*m)`, proved under nonzerodivisor hypotheses.
- **How**: Induction on `n` via `Int.negInduction` + `n.strong_induction_on`; even case uses `complEDS₂` via `normEDS_mul_complEDS₂`; odd case applies `IsEllSequence.normEDS` relation; negative case uses `normEDS_neg`/`complEDS_neg`.
- **Uses from project**: [`IsEllSequence.normEDS`]
- **Used by**: `normEDS_mul_complEDS`
- **Visibility**: private
- **Lines**: 759–809 (50 lines)
- **Notes**: Longest proof in the file (50 lines).

---

### `lemma normEDS_mul_complEDS`
- **Type**: `normEDS b c d m * complEDS b c d m n = normEDS b c d (n * m)`
- **What**: Multiplication formula without nonzerodivisor hypothesis; proved by universalising to `MvPolynomial Param ℤ` and applying `aeval`.
- **How**: Cases on `m = 0`; for `m ≠ 0`, uses `universalNormEDS_mem_nonZeroDivisors` + `normEDS_mul_complEDS_of_mem` in the universal ring, then applies `aeval` via `normEDS_eq_aeval` and `complEDS_eq_aeval`.
- **Uses from project**: [`normEDS_mul_complEDS_of_mem`, `universalNormEDS_mem_nonZeroDivisors`, `normEDS_eq_aeval`, `complEDS_eq_aeval`, `Param`]
- **Used by**: `normEDS_mul_complEDS_div`, `IsDivSequence.normEDS`, `normEDS_mul_complEDS_of_mem` (via induction), `invarDenom_normEDS_eq_redInvarDenom_mul`
- **Visibility**: public
- **Lines**: 812–830 (18 lines)

---

### `lemma normEDS_mul_complEDS_div`
- **Type**: `(hm : m ≠ 0) → (n : ℤ) → (dvd : m ∣ n) → normEDS b c d m * complEDS b c d m (n / m) = normEDS b c d n`
- **What**: Division form of the multiplication formula.
- **Uses from project**: [`normEDS_mul_complEDS`]
- **Used by**: `invarDenom_normEDS_eq_redInvarDenom_mul`
- **Visibility**: public
- **Lines**: 832–835

---

### `def complEDSAux₂`
- **Type**: `(b c d : R) → (m : ℤ) → R`
- **What**: Auxiliary complement used in the `ω` definition: `preNormEDS(b^4, c, d)(m-2) * preNormEDS(b^4, c, d)(m+1)^2 * (if Even m then 1 else b)`.
- **Uses from project**: []
- **Used by**: `complEDSAux₂_zero`, `complEDSAux₂_one`, `complEDSAux₂_neg_one`, `complEDSAux₂_two`, `complEDSAux₂_neg_two`, `complEDSAux₂_mul_b`, `complEDSAux₂_neg`, `map_complEDSAux₂`, `redInvarNum`, `redInvar_normEDS_of_mem_nonZeroDivisors`, `map_redInvarNum`
- **Visibility**: public
- **Lines**: 846–847

---

### `@[simp] lemma complEDSAux₂_zero`, `_one`, `_neg_one`, `_two`, `_neg_two`
- **Type**: Base cases of `complEDSAux₂`.
- **What**: Evaluates `complEDSAux₂` at small indices: `0 ↦ -1`, `1 ↦ -b`, `-1 ↦ 0`, `2 ↦ 0`, `-2 ↦ -d`.
- **Uses from project**: [`complEDSAux₂`]
- **Used by**: (simp lemmas; internal to section)
- **Visibility**: public
- **Lines**: 849–853

---

### `lemma complEDSAux₂_mul_b`
- **Type**: `complEDSAux₂ b c d m * b = normEDS b c d (m-2) * normEDS b c d (m+1)^2`
- **What**: Clearing the denominators: `complEDSAux₂` times `b` equals a product of two `normEDS` values.
- **Uses from project**: [`complEDSAux₂`]
- **Used by**: `invarNum_eq_redInvarNum_mul`
- **Visibility**: public
- **Lines**: 855–858

---

### `lemma complEDSAux₂_neg`
- **Type**: `complEDSAux₂ b c d (-m) = -complEDS₂ b c d m - complEDSAux₂ b c d m`
- **What**: Reflection formula for `complEDSAux₂`.
- **Uses from project**: [`complEDSAux₂`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 860–863

---

### `lemma map_complEDSAux₂`
- **Type**: `complEDSAux₂ (f b) (f c) (f d) m = f (complEDSAux₂ b c d m)`
- **What**: Ring homomorphism naturality for `complEDSAux₂`.
- **Uses from project**: [`complEDSAux₂`]
- **Used by**: `map_redInvarNum`
- **Visibility**: public
- **Lines**: 867–868

---

### `def redInvarNum`
- **Type**: `(b c d : R) → (m : ℤ) → R`
- **What**: Reduced invariant numerator: `complEDS₂ b c d m + normEDS b c d m^3 * b + 2 * complEDSAux₂ b c d m`.
- **Uses from project**: [`complEDSAux₂`]
- **Used by**: `complEDS₂_eq_redInvarNum_sub`, `invarNum_eq_redInvarNum_mul`, `redInvar_normEDS_of_mem_nonZeroDivisors`, `redInvar_normEDS`, `map_redInvarNum`
- **Visibility**: public
- **Lines**: 879–880

---

### `lemma complEDS₂_eq_redInvarNum_sub`
- **Type**: `complEDS₂ b c d m = redInvarNum b c d m - normEDS b c d m^3 * b - 2 * complEDSAux₂ b c d m`
- **What**: Expresses `complEDS₂` in terms of `redInvarNum`.
- **Uses from project**: [`redInvarNum`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 882–887

---

### `lemma invarNum_eq_redInvarNum_mul`
- **Type**: `invarNum (normEDS b c d) 1 m = redInvarNum b c d m * b`
- **What**: `invarNum` at `s = 1` equals `redInvarNum * b`.
- **Uses from project**: [`redInvarNum`, `invarNum`, `complEDSAux₂_mul_b`, `invarNum_normEDS`]
- **Used by**: `redInvar_normEDS_of_mem_nonZeroDivisors`
- **Visibility**: public
- **Lines**: 889–892

---

### `def redInvarDenom`
- **Type**: `(b c d : R) → (m : ℤ) → R`
- **What**: Reduced invariant denominator: a case split on `m mod 6` giving `complEDS`/`normEDS` products.
- **Uses from project**: []
- **Used by**: `invarDenom_normEDS_eq_redInvarDenom_mul`, `redInvarDenom_zero`, `redInvarDenom_one`, `redInvarDenom_two`, `redInvar_normEDS_of_mem_nonZeroDivisors`, `redInvar_normEDS`, `map_redInvarDenom`
- **Visibility**: public
- **Lines**: 895–904

---

### `lemma invarDenom_normEDS_eq_redInvarDenom_mul`
- **Type**: `invarDenom (normEDS b c d) 1 m = redInvarDenom b c d m * b * c`
- **What**: `invarDenom` at `s = 1` equals `redInvarDenom * b * c`.
- **How**: Case split on `m mod 6`; uses `normEDS_mul_complEDS_div` to factorise `normEDS(n*6)` etc.; uses `normEDS_six_eq_mul`; `ring` in each case.
- **Uses from project**: [`invarDenom`, `redInvarDenom`, `normEDS_mul_complEDS_div`, `normEDS_six_eq_mul`]
- **Used by**: `redInvar_normEDS_of_mem_nonZeroDivisors`
- **Visibility**: public
- **Lines**: 906–947 (41 lines)
- **Notes**: Proof is 41 lines — long proof. Uses `interval_cases m % 6` for the contradiction branch.

---

### `@[simp] lemma redInvarDenom_zero`, `_one`, `_two`
- **Type**: Base evaluations of `redInvarDenom` at 0, 1, 2.
- **What**: `redInvarDenom b c d 0 = 0`, `... 1 = 0`, `... 2 = 1`.
- **Uses from project**: [`redInvarDenom`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 949–956

---

### `lemma map_redInvarNum`
- **Type**: `redInvarNum (f b) (f c) (f d) m = f (redInvarNum b c d m)`
- **What**: Ring homomorphism naturality for `redInvarNum`.
- **Uses from project**: [`redInvarNum`, `map_complEDSAux₂`]
- **Used by**: `redInvar_normEDS`
- **Visibility**: public
- **Lines**: 960–962

---

### `lemma map_redInvarDenom`
- **Type**: `redInvarDenom (f b) (f c) (f d) m = f (redInvarDenom b c d m)`
- **What**: Ring homomorphism naturality for `redInvarDenom`.
- **Uses from project**: [`redInvarDenom`]
- **Used by**: `redInvar_normEDS`
- **Visibility**: public
- **Lines**: 964–966

---

### `lemma net_normEDS`
- **Type**: `EllSequence.net (normEDS b c d) p q r s = 0`
- **What**: The net relation vanishes for any normalised EDS (without hypothesis on parameters).
- **How**: Universalises to the polynomial ring, applies `IsEllSequence.net` there, then transports via `map_net`.
- **Uses from project**: [`IsEllSequence.normEDS`, `IsEllSequence.net`, `map_net`, `normEDS_eq_aeval`, `Param`]
- **Used by**: `invar_normEDS`
- **Visibility**: public
- **Lines**: 978–989 (11 lines)

---

### `lemma invar_normEDS`
- **Type**: `invarNum (normEDS b c d) s m * invarDenom (normEDS b c d) s n = invarNum (normEDS b c d) s n * invarDenom (normEDS b c d) s m`
- **What**: Cross-multiplication invariant for normalised EDS.
- **Uses from project**: [`invar_of_net`, `net_normEDS`]
- **Used by**: `invar₂_normEDS_of_mem_nonZeroDivisors`
- **Visibility**: public
- **Lines**: 991–994

---

### `private lemma invar₂_normEDS_of_mem_nonZeroDivisors`
- **Type**: `(hb : b ∈ R⁰) → (m : ℤ) → invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b^4)`
- **What**: Specialised invariant identity at `s = 1, n = 2`: the ratio `invarNum/invarDenom = (d + b^4)/c`.
- **Uses from project**: [`invarNum_normEDS_two`, `invarDenom_normEDS_two`, `invar_normEDS`]
- **Used by**: `invar₂_normEDS`
- **Visibility**: private
- **Lines**: 996–1002

---

### `lemma invar₂_normEDS`
- **Type**: `invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b^4)`
- **What**: Removes the nonzerodivisor hypothesis from `invar₂_normEDS_of_mem_nonZeroDivisors` via universalisation.
- **How**: Universalises to polynomial ring, applies `invar₂_normEDS_of_mem_nonZeroDivisors`, maps via `aeval`, uses `map_invarNum`, `map_invarDenom`.
- **Uses from project**: [`invar₂_normEDS_of_mem_nonZeroDivisors`, `normEDS_eq_aeval`, `map_invarNum`, `map_invarDenom`]
- **Used by**: `redInvar_normEDS_of_mem_nonZeroDivisors`
- **Visibility**: public
- **Lines**: 1004–1021 (17 lines)

---

### `private lemma redInvar_normEDS_of_mem_nonZeroDivisors`
- **Type**: `(hb : b ∈ R⁰) → (hc : c ∈ R⁰) → (m : ℤ) → redInvarNum b c d m = redInvarDenom b c d m * (d + b^4)`
- **What**: Key identity: the reduced invariant decomposition `redInvarNum = redInvarDenom * (d + b^4)`, under nonzerodivisor hypotheses.
- **How**: Cancels `b` and `c` successively using `invarNum_eq_redInvarNum_mul`, `invar₂_normEDS`, `invarDenom_normEDS_eq_redInvarDenom_mul`.
- **Uses from project**: [`redInvarNum`, `redInvarDenom`, `invarNum_eq_redInvarNum_mul`, `invar₂_normEDS`, `invarDenom_normEDS_eq_redInvarDenom_mul`]
- **Used by**: `redInvar_normEDS`
- **Visibility**: private
- **Lines**: 1023–1027

---

### `lemma redInvar_normEDS`
- **Type**: `redInvarNum b c d m = redInvarDenom b c d m * (d + b^4)`
- **What**: Key reduced-invariant identity without nonzerodivisor hypothesis; key for the `ω` definition.
- **How**: Universalises to polynomial ring, applies `redInvar_normEDS_of_mem_nonZeroDivisors`, transports via `map_redInvarNum`, `map_redInvarDenom`, `aeval`.
- **Uses from project**: [`redInvar_normEDS_of_mem_nonZeroDivisors`, `map_redInvarNum`, `map_redInvarDenom`, `normEDS_eq_aeval`, `Param`]
- **Used by**: (exported; key API for division polynomial / zsmul dev)
- **Visibility**: public
- **Lines**: 1030–1043 (13 lines)

---

### `protected theorem IsDivSequence.normEDS`
- **Type**: `IsDivSequence (normEDS b c d)`
- **What**: A normalised EDS is a divisibility sequence: if `m ∣ n` then `normEDS(m) ∣ normEDS(n)`.
- **How**: Directly from `normEDS_mul_complEDS`.
- **Uses from project**: [`normEDS_mul_complEDS`]
- **Used by**: `IsEllDivSequence.normEDS`
- **Visibility**: public
- **Lines**: 1054–1057

---

### `protected theorem IsEllDivSequence.normEDS`
- **Type**: `IsEllDivSequence (normEDS b c d)`
- **What**: A normalised EDS is both an elliptic sequence and a divisibility sequence.
- **Uses from project**: [`IsEllSequence.normEDS`, `IsDivSequence.normEDS`]
- **Used by**: (exported)
- **Visibility**: public
- **Lines**: 1060–1061

---

## Summary Statistics

- **Total declarations**: 99
- **defs**: 21 (`addMulSub`, `rel₄`, `net`, `Rel₃`, `invarNum`, `invarDenom`, `StrictAnti₄`, `HaveSameParity₄`, `avg₄`, `addMulSub₄`, `Rel₄OfValid`, `OddRec`, `EvenRec`, `dMin`, `cMin`, `relFin4`, `Param` (inductive), `universalNormEDS`, `complEDSAux₂`, `redInvarNum`, `redInvarDenom`)
- **lemmas/theorems**: 77
- **instances**: 0
- **sorries**: none
- **maxHeartbeats**: none set
- **Long proofs** (>30 lines): `normEDS_mul_complEDS_of_mem` (50 lines, 759–809), `invarDenom_normEDS_eq_redInvarDenom_mul` (41 lines, 906–947)
- **Key API**: `normEDS_mul_complEDS`, `redInvar_normEDS`, `IsEllSequence.normEDS`, `IsEllSequence.ext`

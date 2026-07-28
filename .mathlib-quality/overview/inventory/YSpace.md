# Inventory — `projects/AdicSpaces/Adic spaces/FarguesFontaine/YSpace.lean`

963 lines. Namespace `FarguesFontaine`, inside `noncomputable section`, `universe u`.
Imports: `«Adic spaces».FarguesFontaine.FrobeniusAction`, `«Adic spaces».RationalSubsets`.
Open: `TopologicalRing ValuationSpectrum WittVector Pointwise`.

Ambient variables (lines 45–48): `(p : ℕ) [Fact p.Prime]`, `(F : Type u)` a perfectoid field of
characteristic `p` (topological/uniform/nonarchimedean), `(ϖ : PseudoUniformizer F)`.

---

### `def vlt`
- **Type**: `vlt (p : ℕ) [Fact p.Prime] (F : Type u) [...] (v : Spv (Ainf p F)) (a b : Ainf p F) : Prop`
- **What**: Strict comparison of valuations, `v(a) < v(b)`, phrased purely in terms of the valuative relation as `v.vle a b ∧ ¬ v.vle b a`.
- **How**: Definition — the standard "`≤` and not `≥`" rendering of `<` in a linear preorder, avoiding any choice of value group.
- **Hypotheses**: None beyond the ambient perfectoid-field setup; `v` an arbitrary point of the valuation spectrum of `A_inf`.
- **Uses from project**: `Ainf`, `Spv.vle`
- **Used by**: `exists_pow_succ_vlt`, `vlt_one_of_not_vle_pow`, `vlt_p_one`, `vlt_teichPi_one`, `exists_pow_p_vlt`, `exists_pow_teichPi_vlt`
- **Visibility**: public
- **Lines**: 50–52 (definition, 2 lines)
- **Notes**: none

### `def Y`
- **Type**: `Y (p : ℕ) [Fact p.Prime] (F : Type u) [...] (ϖ : PseudoUniformizer F) : Set (Spv (Ainf p F))`
- **What**: **The space 𝒴** — the subset of the adic spectrum `Spa(A_inf, A_inf)` consisting of the valuations `v` for which `v(p·[ϖ]) ≠ 0`; i.e. `Spa(A_inf, A_inf)` punctured along `V(p[ϖ])`.
- **How**: Direct set-builder definition: intersect `Spa (Ainf p F) (ringPlus (Ainf p F))` with `{v | ¬ v.vle (p * teichPi p F ϖ) 0}` (non-vanishing expressed as "not `≤ 0`").
- **Hypotheses**: `F` a perfectoid field of char `p`; `ϖ` a pseudo-uniformizer.
- **Uses from project**: `Ainf`, `Spa`, `ringPlus`, `teichPi`, `Spv.vle`
- **Used by**: `Y_subset_spa`, `Y_eq_spa_inter_basicOpen`, `isOpen_Y`, `v_p_ne_zero`, `v_teichPi_ne_zero`, `vlt_p_one`, `vlt_teichPi_one`, `exists_pow_p_vlt`, `exists_pow_teichPi_vlt`, `Y_indep`, `smul_mem_Y`, `KGE_iff`, `KLE_iff`, `KGE_or_KLE`, `not_KGE_of_KLE_of_lt`, `KGE_mono`, `KLE_mono`, `windowU`, `windowV`, `Y_eq_iUnion_windows`, `KGE_smul_iff`, `KLE_smul_iff`, `KGE_cFF_smul_iff`, `KLE_zpow_smul_iff`, `zsmul_windowU`, `zsmul_windowV`, `not_vle_pow_p_zero`, `not_vle_pow_teichPi_zero`, `isOpen_windowU`, `isOpen_windowV`
- **Visibility**: public
- **Lines**: 54–61 (definition, 3 lines)
- **Notes**: docstring cites [BFHHLWY, Def 2.1.1] and [Kedlaya-AWS, Rem. 3.1.9]

### `theorem Y_subset_spa`
- **Type**: `Y p F ϖ ⊆ Spa (Ainf p F) (ringPlus (Ainf p F))`
- **What**: 𝒴 is a subset of the adic spectrum — the puncturing condition is imposed on top of membership in `Spa`.
- **How**: Immediate projection: membership in `Y` is a conjunction, take its first component.
- **Hypotheses**: none.
- **Uses from project**: `Y`, `Spa`, `Ainf`, `ringPlus`
- **Used by**: unused in file (the `.1` projection is used inline instead)
- **Visibility**: public
- **Lines**: 63–64 (1-line proof)
- **Notes**: none

### `theorem Y_eq_spa_inter_basicOpen`
- **Type**: `Y p F ϖ = Spa (Ainf p F) (ringPlus (Ainf p F)) ∩ basicOpen (p * teichPi p F ϖ) (p * teichPi p F ϖ)`
- **What**: Identifies 𝒴 as the trace on `Spa` of the rational/basic open subset `{v : v(f) ≠ 0}` attached to `f = p·[ϖ]`.
- **How**: `basicOpen_self` rewrites the basic open `{v : v(f) ≤ v(f), v(f) ≠ 0}` to the non-vanishing locus of `f`, after which the two sets are definitionally equal (`rfl`).
- **Hypotheses**: none.
- **Uses from project**: `Y`, `Spa`, `Ainf`, `ringPlus`, `teichPi`, `basicOpen`, `basicOpen_self`
- **Used by**: unused in file (`isOpen_Y` re-derives the same identification inline)
- **Visibility**: public
- **Lines**: 66–72 (2-line proof)
- **Notes**: none

### `theorem isOpen_Y`
- **Type**: `IsOpen (Subtype.val ⁻¹' Y p F ϖ : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))`
- **What**: 𝒴 is open in `Spa(A_inf, A_inf)` for the subspace topology on the adic spectrum.
- **How**: Transports openness of the basic open set: `isOpen_basicOpen (p·[ϖ]) (p·[ϖ])` pulled back along `continuous_subtype_val`, then `basicOpen_self` plus the subtype's own `Spa`-membership `v.2` identify the two preimages pointwise.
- **Hypotheses**: none.
- **Uses from project**: `Y`, `Spa`, `Ainf`, `ringPlus`, `teichPi`, `basicOpen`, `basicOpen_self`, `isOpen_basicOpen`
- **Used by**: `isOpen_windowU`, `isOpen_windowV`
- **Visibility**: public
- **Lines**: 74–82 (5-line proof)
- **Notes**: none

### `private theorem p_mem_Iinf`
- **Type**: `(p : Ainf p F) ∈ Iinf p F ϖ`
- **What**: The prime `p` lies in the ideal of definition `I_inf = (p, [ϖ])` of `A_inf`.
- **How**: Unfold `Iinf` as a span and apply `Ideal.subset_span` to the first element of the generating pair.
- **Hypotheses**: none.
- **Uses from project**: `Ainf`, `Iinf`
- **Used by**: `vlt_p_one`, `exists_pow_p_vlt`
- **Visibility**: private
- **Lines**: 84–86 (2-line proof)
- **Notes**: none

### `private theorem teichPi_mem_Iinf`
- **Type**: `teichPi p F ϖ ∈ Iinf p F ϖ`
- **What**: The Teichmüller lift `[ϖ]` lies in the ideal of definition `I_inf = (p, [ϖ])`.
- **How**: Same as `p_mem_Iinf`, via `Ideal.subset_span` on the second generator (`Set.mem_insert_of_mem`).
- **Hypotheses**: none.
- **Uses from project**: `Ainf`, `Iinf`, `teichPi`
- **Used by**: `vlt_teichPi_one`, `exists_pow_teichPi_vlt`
- **Visibility**: private
- **Lines**: 88–90 (2-line proof)
- **Notes**: none

### `private theorem exists_pow_succ_vlt`
- **Type**: `(hv : v ∈ Spa (Ainf p F) (ringPlus (Ainf p F))) (ha : a ∈ Iinf p F ϖ) (hb : ¬ v.vle b 0) : ∃ n : ℕ, vlt p F v (a ^ (n + 1)) b`
- **What**: Continuity engine of the file: if `a` lies in the ideal of definition and `v(b) ≠ 0`, then some positive power `a^(n+1)` has strictly smaller value than `b`.
- **How**: The set `{x | v(x) < v(b)}` is open (it is the preimage of a `<`-set under `ValuativeRel.valuation`, using the continuity clause `hv.1` of `Spa`-membership and `Valuation.vle_iff_le`), and contains `0`; adicness of `I_inf` (`isAdic_iff.mp (isAdic_Iinf …)`) then supplies `N` with `I^N` inside it, and `Ideal.pow_mem_pow` puts `a^(N+1)` in `I^N`.
- **Hypotheses**: `v` continuous (i.e. in `Spa`), `a ∈ I_inf`, `v(b) ≠ 0`.
- **Uses from project**: `vlt`, `Ainf`, `Spa`, `ringPlus`, `Iinf`, `isAdic_Iinf`, `Spv.toValuativeRel`, `Spv.vle`, `Spv.zero_vle`
- **Used by**: `vlt_p_one`, `vlt_teichPi_one`, `exists_pow_p_vlt`, `exists_pow_teichPi_vlt`
- **Visibility**: private
- **Lines**: 92–115 (21-line proof)
- **Notes**: none

### `private theorem vlt_one_of_not_vle_pow`
- **Type**: `(h2 : ¬ v.vle a (a ^ (n + 1))) : vlt p F v a 1`
- **What**: If `v(a) ≤ v(a^(n+1))` fails for some `n`, then `v(a) < 1` strictly.
- **How**: Contrapositive: assuming `v(1) ≤ v(a)`, an induction on `k` using `Spv.mul_vle_mul_left` (multiplying the hypothesis by `a^(m+1)` and rewriting `pow_succ'`) gives `v(a) ≤ v(a^(k+1))` for every `k`, contradicting `h2`; totality `Spv.vle_total` then yields the strict inequality.
- **Hypotheses**: `¬ v.vle a (a^(n+1))` for some `n`.
- **Uses from project**: `vlt`, `Ainf`, `Spv.vle`, `Spv.vle_total`, `Spv.vle_trans`, `Spv.mul_vle_mul_left`
- **Used by**: `vlt_p_one`, `vlt_teichPi_one`
- **Visibility**: private
- **Lines**: 117–129 (12-line proof)
- **Notes**: none

## section ElementFacts (lines 131–180) — `{p F ϖ}` and `{v : Spv (Ainf p F)}` implicit

### `theorem v_p_ne_zero`
- **Type**: `(hv : v ∈ Y p F ϖ) : ¬ v.vle (p : Ainf p F) 0`
- **What**: On 𝒴 the valuation of `p` is nonzero.
- **How**: If `v(p) = 0` then multiplying by `[ϖ]` via `Spv.mul_vle_mul_left` gives `v(p[ϖ]) ≤ 0`, contradicting the defining condition `hv.2` of 𝒴.
- **Hypotheses**: `v ∈ Y p F ϖ`.
- **Uses from project**: `Y`, `Ainf`, `teichPi`, `Spv.vle`, `Spv.mul_vle_mul_left`
- **Used by**: `vlt_p_one`, `Y_indep`, `smul_mem_Y`, `not_KGE_of_KLE_of_lt`, `KGE_mono`, `KLE_mono`, `Y_eq_iUnion_windows`, `not_vle_pow_p_zero`
- **Visibility**: public
- **Lines**: 136–138 (2-line proof)
- **Notes**: none

### `theorem v_teichPi_ne_zero`
- **Type**: `(hv : v ∈ Y p F ϖ) : ¬ v.vle (teichPi p F ϖ) 0`
- **What**: On 𝒴 the valuation of the Teichmüller lift `[ϖ]` is nonzero.
- **How**: Mirror of `v_p_ne_zero` — multiply the hypothesised vanishing by `p` (`Spv.mul_vle_mul_left`), commute, and contradict `hv.2`.
- **Hypotheses**: `v ∈ Y p F ϖ`.
- **Uses from project**: `Y`, `Ainf`, `teichPi`, `Spv.vle`, `Spv.mul_vle_mul_left`
- **Used by**: `vlt_teichPi_one`, `Y_indep`, `smul_mem_Y`, `Y_eq_iUnion_windows`, `not_vle_pow_teichPi_zero`
- **Visibility**: public
- **Lines**: 140–144 (4-line proof)
- **Notes**: none

### `theorem vlt_p_one`
- **Type**: `(hv : v ∈ Y p F ϖ) : vlt p F v (p : Ainf p F) 1`
- **What**: On 𝒴 one has `v(p) < 1` strictly — the standard fact that on the analytic locus the ideal of definition has value `< 1`.
- **How**: Feed `p_mem_Iinf` and `v_p_ne_zero` into `exists_pow_succ_vlt` to get `v(p^(n+1)) < v(p)`, then apply `vlt_one_of_not_vle_pow`.
- **Hypotheses**: `v ∈ Y p F ϖ`.
- **Uses from project**: `Y`, `vlt`, `Ainf`, `exists_pow_succ_vlt`, `p_mem_Iinf`, `v_p_ne_zero`, `vlt_one_of_not_vle_pow`
- **Used by**: `not_KGE_of_KLE_of_lt`, `KGE_mono`, `KLE_mono`, `Y_eq_iUnion_windows` (all four need `v(p) < 1` to flip exponent inequalities)
- **Visibility**: public
- **Lines**: 146–155 (3-line proof)
- **Notes**: docstring cites [SW, §12.2] and Wedhorn §7-style continuity

### `theorem vlt_teichPi_one`
- **Type**: `(hv : v ∈ Y p F ϖ) : vlt p F v (teichPi p F ϖ) 1`
- **What**: On 𝒴 one has `v([ϖ]) < 1` strictly.
- **How**: Identical to `vlt_p_one` with `teichPi_mem_Iinf` and `v_teichPi_ne_zero` fed into `exists_pow_succ_vlt`, then `vlt_one_of_not_vle_pow`.
- **Hypotheses**: `v ∈ Y p F ϖ`.
- **Uses from project**: `Y`, `vlt`, `Ainf`, `teichPi`, `exists_pow_succ_vlt`, `teichPi_mem_Iinf`, `v_teichPi_ne_zero`, `vlt_one_of_not_vle_pow`
- **Used by**: `Y_eq_iUnion_windows`
- **Visibility**: public
- **Lines**: 157–161 (3-line proof)
- **Notes**: none

### `theorem exists_pow_p_vlt`
- **Type**: `(hv : v ∈ Y p F ϖ) {g : Ainf p F} (hg : ¬ v.vle g 0) : ∃ n : ℕ, vlt p F v ((p : Ainf p F) ^ n) g`
- **What**: Cofinality of `p`-powers: for any `g` with `v(g) ≠ 0` there is `n` with `v(p^n) < v(g)`.
- **How**: `exists_pow_succ_vlt` applied with `a := p` (using `p_mem_Iinf`) produces the exponent `n+1`, repackaged as a bare `n`.
- **Hypotheses**: `v ∈ Y p F ϖ`, `v(g) ≠ 0`.
- **Uses from project**: `Y`, `vlt`, `Ainf`, `exists_pow_succ_vlt`, `p_mem_Iinf`
- **Used by**: `Y_eq_iUnion_windows` (supplies the upper bound on κ)
- **Visibility**: public
- **Lines**: 163–172 (2-line proof)
- **Notes**: none

### `theorem exists_pow_teichPi_vlt`
- **Type**: `(hv : v ∈ Y p F ϖ) {g : Ainf p F} (hg : ¬ v.vle g 0) : ∃ n : ℕ, vlt p F v (teichPi p F ϖ ^ n) g`
- **What**: Cofinality of `[ϖ]`-powers, the `teichPi` analogue of `exists_pow_p_vlt`.
- **How**: `exists_pow_succ_vlt` with `a := teichPi p F ϖ` (using `teichPi_mem_Iinf`).
- **Hypotheses**: `v ∈ Y p F ϖ`, `v(g) ≠ 0`.
- **Uses from project**: `Y`, `vlt`, `Ainf`, `teichPi`, `exists_pow_succ_vlt`, `teichPi_mem_Iinf`
- **Used by**: `Y_eq_iUnion_windows` (supplies the lower bound on κ)
- **Visibility**: public
- **Lines**: 174–178 (2-line proof)
- **Notes**: none

## (end section ElementFacts)

### `theorem Y_indep`
- **Type**: `(ϖ' : PseudoUniformizer F) : Y p F ϖ = Y p F ϖ'`
- **What**: 𝒴 is independent of the choice of pseudo-uniformizer.
- **How**: A symmetric `key` claim: if `v ∈ Y p F α` and `v(p[β]) = 0` then, since `v.supp` is prime, either `p ∈ supp` (contradicting `v_p_ne_zero`) or `[β] ∈ supp`; in the latter case `exists_teichPi_pow_mem_span_teichPi` gives `[α]^k ∈ ([β])`, so `[α]^k ∈ supp`, and `Ideal.IsPrime.mem_of_pow_mem` contradicts `v_teichPi_ne_zero`.
- **Hypotheses**: `ϖ, ϖ'` both pseudo-uniformizers of `F`.
- **Uses from project**: `Y`, `Ainf`, `teichPi`, `v_p_ne_zero`, `v_teichPi_ne_zero`, `exists_teichPi_pow_mem_span_teichPi`, `Spv.supp`, `Spv.mem_supp_iff`, `Spv.vle`
- **Used by**: unused in file (exported invariance statement)
- **Visibility**: public
- **Lines**: 182–200 (13-line proof)
- **Notes**: docstring cites [Kedlaya-AWS §11.2]-style divisibility argument

### `private theorem frob_teichmuller`
- **Type**: `(x : OF F) : frob p F (WittVector.teichmuller p x) = WittVector.teichmuller p (x ^ p)`
- **What**: Frobenius on `A_inf` sends `[x]` to `[x^p]`.
- **How**: Unfold `frob` to `WittVector.frobenius`, then chain `frobenius_eq_map_frobenius`, `WittVector.map_teichmuller` and `frobenius_def` (using `CharP F p`).
- **Hypotheses**: `F` of characteristic `p` (so ring Frobenius is `x ↦ x^p`).
- **Uses from project**: `frob`, `OF`, `Ainf`
- **Used by**: `frob_zpow_teichmuller`
- **Visibility**: private
- **Lines**: 202–205 (3-line proof)
- **Notes**: none

### `private theorem frobeniusEquiv_pow_apply`
- **Type**: `(m : ℕ) (x : OF F) : ((frobeniusEquiv (OF F) p) ^ m : RingAut (OF F)) x = x ^ p ^ m`
- **What**: The `m`-th power of the Frobenius automorphism of `O_F` is `x ↦ x^{p^m}`.
- **How**: Induction on `m`, generalising `x`; the step rewrites `pow_succ'`, `RingAut.mul_apply`, the induction hypothesis, and then `← pow_mul`/`← pow_succ` to combine exponents.
- **Hypotheses**: `O_F` perfect of characteristic `p` (so `frobeniusEquiv` exists).
- **Uses from project**: `OF`
- **Used by**: `smul_mem_Y`
- **Visibility**: private
- **Lines**: 207–214 (7-line proof)
- **Notes**: none

### `private theorem frob_zpow_teichmuller`
- **Type**: `(j : ℤ) (x : OF F) : (frob p F ^ j : RingAut (Ainf p F)) (teichmuller p x) = teichmuller p ((frobeniusEquiv (OF F) p ^ j : RingAut (OF F)) x)`
- **What**: Teichmüller lifting intertwines the integer powers of Frobenius on `A_inf` with those on `O_F`.
- **How**: `Int.induction_on` in `j` generalising `x`: the successor step rewrites `zpow_add_one` and applies `frob_teichmuller`; the predecessor step first proves the inverse form `(frob p F).symm [x] = [(frobeniusEquiv).symm x]` by injectivity of `frob p F` plus `frob_teichmuller`, then rewrites `zpow_sub_one`.
- **Hypotheses**: `char F = p`, `O_F` perfect.
- **Uses from project**: `frob`, `OF`, `Ainf`, `frob_teichmuller`
- **Used by**: `smul_mem_Y`
- **Visibility**: private
- **Lines**: 216–241 (22-line proof)
- **Notes**: none

### `theorem smul_mem_Y`
- **Type**: `(g : Multiplicative ℤ) {v : Spv (Ainf p F)} (hv : v ∈ Y p F ϖ) : g • v ∈ Y p F ϖ`
- **What**: 𝒴 is stable under the `φ^ℤ`-action of Frobenius on `Spa(A_inf, A_inf)`.
- **How**: `smul_mem_spa_Ainf` handles the `Spa` component; for the puncture, `(g • v).vle a b ↔ v.vle (g⁻¹ • a) (g⁻¹ • b)` (via `comap_vle`) reduces to `v(φ^j(p)·φ^j([ϖ])) = 0`; primality of `v.supp` splits into the `p` case (`map_natCast`, contradicting `v_p_ne_zero`) and the `[ϖ]` case, where `frob_zpow_teichmuller` and `frobeniusEquiv_pow_apply` convert `φ^j([ϖ])^{p^{(-j).toNat}}` into `[ϖ]^{p^{j.toNat}}`, contradicting `v_teichPi_ne_zero`.
- **Hypotheses**: `v ∈ Y p F ϖ`; `g` an integer power of Frobenius.
- **Uses from project**: `Y`, `Ainf`, `frob`, `OF`, `teichPi`, `PseudoUniformizer.toOF`, `smul_mem_spa_Ainf`, `frob_zpow_teichmuller`, `frobeniusEquiv_pow_apply`, `v_p_ne_zero`, `v_teichPi_ne_zero`, `Spv.supp`, `Spv.mem_supp_iff`, `Spv.vle`, `comap`, `comap_vle`
- **Used by**: `KGE_smul_iff`, `KLE_smul_iff`, `KGE_cFF_smul_iff`, `KLE_zpow_smul_iff`, `zsmul_windowU`, `zsmul_windowV`
- **Visibility**: public
- **Lines**: 243–276 (29-line proof)
- **Notes**: proof close to 30 lines; docstring cites [SW, §12.2]

## §  The rank-free κ-comparison predicates (from line 278)

### `def KGE`
- **Type**: `KGE (p F ϖ) (q : ℚ) (v : Spv (Ainf p F)) : Prop`
- **What**: Rank-free rendering of "`κ(v) ≥ q`": for `q = a/b` in lowest terms, the inequality `v([ϖ])^b ≤ v(p)^a`, stated on ring elements as `v.vle (teichPi ^ q.den) (p ^ q.num.toNat)`.
- **How**: Definition — denominators are cleared so no real-valued radius function `κ` (nor any rank-1 hypothesis) is needed; for `q ≤ 0` the numerator truncates to `0`, so all lemmas assume `0 < q`.
- **Hypotheses**: none in the definition; downstream lemmas require `0 < q` and `v ∈ Y`.
- **Uses from project**: `Ainf`, `teichPi`, `Spv.vle`
- **Used by**: `KGE_iff`, `KGE_or_KLE`, `not_KGE_of_KLE_of_lt`, `KGE_mono`, `windowU`, `windowV`, `KGE_smul_iff`, `KGE_cFF_smul_iff`, `isOpen_windowU`, `isOpen_windowV`
- **Visibility**: public
- **Lines**: 280–289 (2-line definition)
- **Notes**: docstring cites [SW, §12.2] and [Kedlaya-AWS, Rem. 3.1.9]

### `def KLE`
- **Type**: `KLE (p F ϖ) (q : ℚ) (v : Spv (Ainf p F)) : Prop`
- **What**: Rank-free rendering of "`κ(v) ≤ q`": `v(p)^a ≤ v([ϖ])^b` for `q = a/b` in lowest terms.
- **How**: Definition, dual to `KGE` with the two sides of `vle` exchanged.
- **Hypotheses**: none in the definition; downstream lemmas require `0 < q` and `v ∈ Y`.
- **Uses from project**: `Ainf`, `teichPi`, `Spv.vle`
- **Used by**: `KLE_iff`, `KGE_or_KLE`, `not_KGE_of_KLE_of_lt`, `KLE_mono`, `windowU`, `windowV`, `KLE_smul_iff`, `KLE_zpow_smul_iff`, `isOpen_windowU`, `isOpen_windowV`
- **Visibility**: public
- **Lines**: 291–293 (2-line definition)
- **Notes**: none

### `private theorem pow_le_pow_iff_cross`
- **Type**: `{Γ₀} [LinearOrderedCommGroupWithZero Γ₀] {x y : Γ₀} {a b c d : ℕ} (hcross : a * d = c * b) (hb : b ≠ 0) (hd : d ≠ 0) : x ^ d ≤ y ^ c ↔ x ^ b ≤ y ^ a`
- **What**: Cross-multiplication in a linearly-ordered commutative group with zero: two power-inequalities agree when the exponents cross-multiply equally.
- **How**: Raise both sides of each inequality to the opposite denominator using `pow_le_pow_iff_left₀` (valid since `Γ₀` is linearly ordered with `zero_le'`), collapse with `← pow_mul`, and match exponents through the cross relation `hcross`.
- **Hypotheses**: `a*d = c*b`, `b ≠ 0`, `d ≠ 0`.
- **Uses from project**: `[]`
- **Used by**: `KGE_iff`, `KLE_iff`, `vle_pow_iff_cross`
- **Visibility**: private
- **Lines**: 297–302 (3-line proof)
- **Notes**: fully general — no `A_inf` or `Spv` involved

### `private theorem cross_eq`
- **Type**: `{q : ℚ} (hq : 0 < q) {a b : ℕ} (hb : 0 < b) (hab : q = (a : ℚ) / b) : a * q.den = q.num.toNat * b`
- **What**: The cross-multiplication identity behind representation-independence: any presentation `q = a/b` cross-multiplies against the reduced form `q.num/q.den`.
- **How**: From `a/b = q.num/q.den` (via `Rat.num_div_den`) and `div_eq_div_iff` (both denominators nonzero by `hb` and `q.den_pos`), obtain the `ℚ`-identity, then push down to `ℕ` using `Int.toNat_of_nonneg (Rat.num_pos.mpr hq).le` and `exact_mod_cast`.
- **Hypotheses**: `0 < q` (so `q.num.toNat` is faithful), `0 < b`, `q = a/b`.
- **Uses from project**: `[]`
- **Used by**: `KGE_iff`, `KLE_iff`, `vle_pow_iff_cross`
- **Visibility**: private
- **Lines**: 304–313 (6-line proof)
- **Notes**: none

### `theorem KGE_iff`
- **Type**: `(hv : v ∈ Y p F ϖ) {q : ℚ} (hq : 0 < q) {a b : ℕ} (hb : 0 < b) (hab : q = (a : ℚ) / b) : KGE p F ϖ q v ↔ v.vle (teichPi p F ϖ ^ b) ((p : Ainf p F) ^ a)`
- **What**: Representation-independence of `KGE`: the predicate may be tested with *any* fraction `a/b` representing `q`, not just the reduced one. The denominator-clearing workhorse of the file.
- **How**: Install `v.toValuativeRel`, transport both `vle`s to `≤` of `ValuativeRel.valuation` via `Valuation.vle_iff_le`, distribute `map_pow`, and conclude by `pow_le_pow_iff_cross` fed with `cross_eq hq hb hab`.
- **Hypotheses**: `v ∈ Y`, `0 < q`, `0 < b`, `q = a/b`.
- **Uses from project**: `KGE`, `Y`, `Ainf`, `teichPi`, `pow_le_pow_iff_cross`, `cross_eq`, `Spv.vle`, `Spv.toValuativeRel`
- **Used by**: `Y_eq_iUnion_windows`, `KGE_smul_iff`, `KGE_cFF_smul_iff`
- **Visibility**: public
- **Lines**: 315–326 (7-line proof)
- **Notes**: `hv` is present for uniformity but the proof does not consume it

### `theorem KLE_iff`
- **Type**: `(hv : v ∈ Y p F ϖ) {q : ℚ} (hq : 0 < q) {a b : ℕ} (hb : 0 < b) (hab : q = (a : ℚ) / b) : KLE p F ϖ q v ↔ v.vle ((p : Ainf p F) ^ a) (teichPi p F ϖ ^ b)`
- **What**: Representation-independence of `KLE`: it may be tested with any fraction `a/b` representing `q`.
- **How**: As in `KGE_iff` — bridge `vle` to `≤` via `Valuation.vle_iff_le`, `map_pow`, then `pow_le_pow_iff_cross` with the *transposed* cross relation `b * q.num.toNat = q.den * a`; extra care establishes `q.num.toNat ≠ 0` (from `Rat.num_pos.mpr hq`) and `a ≠ 0` (else `cross_eq` forces `q.num.toNat * b = 0`, killed by `omega`).
- **Hypotheses**: `v ∈ Y`, `0 < q`, `0 < b`, `q = a/b`.
- **Uses from project**: `KLE`, `Y`, `Ainf`, `teichPi`, `pow_le_pow_iff_cross`, `cross_eq`, `Spv.vle`, `Spv.toValuativeRel`
- **Used by**: `Y_eq_iUnion_windows`, `KLE_smul_iff`, `KLE_zpow_smul_iff`
- **Visibility**: public
- **Lines**: 328–347 (16-line proof)
- **Notes**: `hv` unused in the proof body (kept for API symmetry with `KGE_iff`)

### `theorem KGE_or_KLE`
- **Type**: `(hv : v ∈ Y p F ϖ) {q : ℚ} (hq : 0 < q) : KGE p F ϖ q v ∨ KLE p F ϖ q v`
- **What**: Totality: at each positive rational `q`, either `κ(v) ≥ q` or `κ(v) ≤ q`.
- **How**: Immediate from linearity of the valuative order, `Spv.vle_total` applied to the two ring elements `[ϖ]^q.den` and `p^q.num.toNat`.
- **Hypotheses**: `v ∈ Y`, `0 < q` (both nominally; the proof is `vle_total` alone).
- **Uses from project**: `KGE`, `KLE`, `Y`, `Ainf`, `Spv.vle_total`
- **Used by**: `Y_eq_iUnion_windows` (used twice: to pick `KLE (p^{n₀+1})` from maximality, and to split into `U_{n₀}` vs `V_{n₀}`)
- **Visibility**: public
- **Lines**: 349–353 (1-line proof)
- **Notes**: `hv` and `hq` unused in the body

### `theorem not_KGE_of_KLE_of_lt`
- **Type**: `(hv : v ∈ Y p F ϖ) {q q' : ℚ} (hq' : 0 < q') (hlt : q' < q) (hle : KLE p F ϖ q' v) : ¬ KGE p F ϖ q v`
- **What**: Order-incompatibility on 𝒴: `κ(v) ≤ q'` and `κ(v) ≥ q` cannot both hold when `q' < q`. **This single lemma drives all window disjointness.**
- **How**: Set `X = v([ϖ])`, `Ypv = v(p)`; on 𝒴 one has `0 < Ypv < 1` (`v_p_ne_zero`, `vlt_p_one`). Chaining the two hypotheses with `pow_le_pow_left'` and `pow_mul` gives `Ypv^(q'.num·q.den) ≤ Ypv^(q.num·q'.den)`; since `Ypv < 1`, `pow_le_pow_iff_right_of_lt_one₀` *flips* this to `q.num·q'.den ≤ q'.num·q.den`, contradicting the cross-multiplied form of `q' < q` (`div_lt_div_iff₀`), closed by `omega`.
- **Hypotheses**: `v ∈ Y` (needed for `0 < v(p) < 1`), `0 < q'`, `q' < q`, `KLE q' v`.
- **Uses from project**: `KGE`, `KLE`, `Y`, `Ainf`, `teichPi`, `v_p_ne_zero`, `vlt_p_one`, `Spv.vle`, `Spv.toValuativeRel`
- **Used by**: `Y_eq_iUnion_windows`, `windowU_disjoint`, `windowV_disjoint`
- **Visibility**: public
- **Lines**: 355–407 (45-line proof)
- **Notes**: **proof >30 lines**; the exponent-flip `pow_le_pow_iff_right_of_lt_one₀` is the crux

## §  The windows U_n, V_n (Kedlaya, AWS Remark 3.1.9) (from line 409)

### `def cFF`
- **Type**: `cFF (p : ℕ) : ℚ := ((p : ℚ) + 1) / 2`
- **What**: The auxiliary constant `c = (p+1)/2 ∈ (1, p) ∩ ℚ` of [Kedlaya-AWS, Rem. 3.1.9], which separates the `U_n` from the `V_n`.
- **How**: Explicit choice of a rational strictly between `1` and `p`; the midpoint works for every prime including `p = 2` (giving `c = 3/2`).
- **Hypotheses**: none in the definition; `1 < p` is needed for the interval property.
- **Uses from project**: `[]`
- **Used by**: `one_lt_cFF`, `cFF_lt_p`, `windowU`, `windowV`, `cFF_mul_zpow_eq`, `KLE_smul_iff`, `KGE_cFF_smul_iff`, `windowU_disjoint`, `windowV_disjoint`, `isOpen_windowU`, `isOpen_windowV`
- **Visibility**: public
- **Lines**: 411–415 (1-line definition)
- **Notes**: takes its own explicit `(p : ℕ)` binder, independent of the section variables

### `theorem one_lt_cFF`
- **Type**: `{p : ℕ} (hp : 1 < p) : 1 < cFF p`
- **What**: `c > 1`.
- **How**: Unfold `cFF` and clear the denominator with `lt_div_iff₀`, then `linarith` from `(1 : ℚ) < p`.
- **Hypotheses**: `1 < p`.
- **Uses from project**: `cFF`
- **Used by**: `Y_eq_iUnion_windows`, `KLE_smul_iff`, `KGE_cFF_smul_iff`, `windowU_disjoint`, `windowV_disjoint`
- **Visibility**: public
- **Lines**: 417–420 (3-line proof)
- **Notes**: none

### `theorem cFF_lt_p`
- **Type**: `{p : ℕ} (hp : 1 < p) : cFF p < (p : ℚ)`
- **What**: `c < p`.
- **How**: Unfold `cFF`, clear the denominator with `div_lt_iff₀`, then `linarith`.
- **Hypotheses**: `1 < p`.
- **Uses from project**: `cFF`
- **Used by**: `windowU_disjoint` (the only consumer; `c < p` is what separates consecutive `U`-windows)
- **Visibility**: public
- **Lines**: 422–425 (3-line proof)
- **Notes**: none

### `def windowU`
- **Type**: `windowU (p F ϖ) (n : ℤ) : Set (Spv (Ainf p F))`
- **What**: Kedlaya's window `U_n = {v ∈ 𝒴 : v(p)^{c·p^n} ≤ v([ϖ]) ≤ v(p)^{p^n}}`, i.e. `κ(v) ∈ [p^n, c·p^n]`, expressed as `KGE (p^n) ∧ KLE (c·p^n)`.
- **How**: Set-builder over `Y p F ϖ` conjoining the two rank-free comparisons.
- **Hypotheses**: none in the definition; `n : ℤ` ranges over all integers.
- **Uses from project**: `Y`, `KGE`, `KLE`, `cFF`, `Ainf`
- **Used by**: `Y_eq_iUnion_windows`, `zsmul_windowU`, `windowU_disjoint`, `isOpen_windowU`
- **Visibility**: public
- **Lines**: 429–434 (2-line definition)
- **Notes**: none

### `def windowV`
- **Type**: `windowV (p F ϖ) (n : ℤ) : Set (Spv (Ainf p F))`
- **What**: Kedlaya's window `V_n = {v ∈ 𝒴 : v(p)^{p^{n+1}} ≤ v([ϖ]) ≤ v(p)^{c·p^n}}`, i.e. `κ(v) ∈ [c·p^n, p^{n+1}]`.
- **How**: Set-builder over `Y p F ϖ` with `KGE (c·p^n) ∧ KLE (p^{n+1})` — the complementary half of the interval covered by `windowU`.
- **Hypotheses**: none in the definition.
- **Uses from project**: `Y`, `KGE`, `KLE`, `cFF`, `Ainf`
- **Used by**: `Y_eq_iUnion_windows`, `zsmul_windowV`, `windowV_disjoint`, `isOpen_windowV`
- **Visibility**: public
- **Lines**: 436–441 (2-line definition)
- **Notes**: none

### `theorem KGE_mono`
- **Type**: `(hv : v ∈ Y p F ϖ) {q q' : ℚ} (hq' : 0 < q') (hle : q' ≤ q) (h : KGE p F ϖ q v) : KGE p F ϖ q' v`
- **What**: Antitone monotonicity of `KGE` in the rational parameter: `κ(v) ≥ q` and `q' ≤ q` imply `κ(v) ≥ q'`.
- **How**: On 𝒴, `0 < v(p) < 1` (`v_p_ne_zero`, `vlt_p_one`). Cross-multiplying `q' ≤ q` (`div_le_div_iff₀`) yields `q'.num·q.den ≤ q.num·q'.den`; a `calc` chain then raises the hypothesis to the `q'.den`-th power (`pow_le_pow_left'`), applies the reverse-monotone `pow_le_pow_iff_right_of_lt_one₀` for `v(p) < 1`, and `pow_le_pow_iff_left₀` cancels the extra `q.den`-th power.
- **Hypotheses**: `v ∈ Y`, `0 < q'`, `q' ≤ q`, `KGE q v`.
- **Uses from project**: `KGE`, `Y`, `Ainf`, `teichPi`, `v_p_ne_zero`, `vlt_p_one`, `Spv.vle`, `Spv.toValuativeRel`
- **Used by**: `Y_eq_iUnion_windows` (to push the lower κ-bound `1/(m₂+1)` down to `p^{-N}`)
- **Visibility**: public
- **Lines**: 451–491 (41-line proof)
- **Notes**: **proof >30 lines**. The `/-- The covering ... -/` docstring at lines 443–450 sits immediately above this declaration but actually describes `Y_eq_iUnion_windows` — a **misplaced docstring**.

### `theorem KLE_mono`
- **Type**: `(hv : v ∈ Y p F ϖ) {q q' : ℚ} (hq : 0 < q) (hle : q ≤ q') (h : KLE p F ϖ q v) : KLE p F ϖ q' v`
- **What**: Monotonicity of `KLE`: `κ(v) ≤ q` and `q ≤ q'` imply `κ(v) ≤ q'`.
- **How**: Mirror of `KGE_mono` — `0 < v(p) < 1` from `v_p_ne_zero`/`vlt_p_one`, cross-multiplication of `q ≤ q'` via `div_le_div_iff₀`, then a `calc` chain using `pow_le_pow_iff_right_of_lt_one₀` (exponent flip) and `pow_le_pow_left'`, with `pow_le_pow_iff_left₀` cancelling the auxiliary power.
- **Hypotheses**: `v ∈ Y`, `0 < q`, `q ≤ q'`, `KLE q v`.
- **Uses from project**: `KLE`, `Y`, `Ainf`, `teichPi`, `v_p_ne_zero`, `vlt_p_one`, `Spv.vle`, `Spv.toValuativeRel`
- **Used by**: unused in file — it is the unused dual of `KGE_mono` (exported API only)
- **Visibility**: public
- **Lines**: 493–533 (41-line proof)
- **Notes**: **proof >30 lines**; no docstring

### `theorem Y_eq_iUnion_windows`
- **Type**: `Y p F ϖ = (⋃ n : ℤ, windowU p F ϖ n) ∪ ⋃ n : ℤ, windowV p F ϖ n`
- **What**: **The covering** — 𝒴 is the union of Kedlaya's windows `U_n` and `V_n` over all `n ∈ ℤ`.
- **How**: `⊇` is projection to the `Y`-component of each window. For `⊆`: cofinality (`exists_pow_p_vlt` with `v_teichPi_ne_zero`, and `exists_pow_teichPi_vlt` with `v_p_ne_zero`) plus `vlt_p_one`/`vlt_teichPi_one` gives `KLE (m₁+1)` and `KGE (1/(m₂+1))` (translated via `KLE_iff`/`KGE_iff`); `KGE_mono` pushes the lower bound to `p^{-N}` for `N = max (m₁+2) (m₂+1)`, and `not_KGE_of_KLE_of_lt` bounds the set `{z | KGE (p^z) v}` above by `N`, so `Int.exists_greatest_of_bdd` supplies a maximal `n₀`; maximality plus `KGE_or_KLE` gives `KLE (p^{n₀+1})`, and a final `KGE_or_KLE` at `c·p^{n₀}` (positive by `one_lt_cFF`) places `v` in `V_{n₀}` or `U_{n₀}`.
- **Hypotheses**: `p` prime (used as `1 < p` via `Fact.out`).
- **Uses from project**: `Y`, `windowU`, `windowV`, `KGE`, `KLE`, `KGE_iff`, `KLE_iff`, `KGE_mono`, `KGE_or_KLE`, `not_KGE_of_KLE_of_lt`, `exists_pow_p_vlt`, `exists_pow_teichPi_vlt`, `v_p_ne_zero`, `v_teichPi_ne_zero`, `vlt_p_one`, `vlt_teichPi_one`, `cFF`, `one_lt_cFF`, `Ainf`, `teichPi`, `Spv.vle`, `Spv.vle_trans`, `Spv.mul_vle_mul_left`
- **Used by**: unused in file (headline theorem)
- **Visibility**: public
- **Lines**: 535–601 (66-line proof)
- **Notes**: **proof >30 lines**; the theorem's intended docstring is stranded at lines 443–450 above `KGE_mono`, so this declaration carries none

### `private theorem vle_pow_iff_cross`
- **Type**: `{v : Spv (Ainf p F)} {x y : Ainf p F} {a b c d : ℕ} (h : a * d = c * b) (hb : b ≠ 0) (hd : d ≠ 0) : v.vle (x ^ d) (y ^ c) ↔ v.vle (x ^ b) (y ^ a)`
- **What**: `Spv`-level version of cross-multiplication: two `vle` power-comparisons agree when their exponents cross-multiply equally.
- **How**: Install `v.toValuativeRel`, transport both sides through `Valuation.vle_iff_le` and `map_pow`, then apply the abstract `pow_le_pow_iff_cross`.
- **Hypotheses**: `a*d = c*b`, `b ≠ 0`, `d ≠ 0`.
- **Uses from project**: `Ainf`, `pow_le_pow_iff_cross`, `Spv.vle`, `Spv.toValuativeRel`
- **Used by**: `vle_theta_iff_ge`, `vle_theta_iff_le`
- **Visibility**: private
- **Lines**: 609–617 (6-line proof)
- **Notes**: The `/-- **Translation** ... -/` docstring at lines 603–608 sits above this private helper but describes the `φ^k(U_n) = U_{n-k}` translation theorem — a second **misplaced docstring**.

### `private theorem teichmuller_frobeniusEquiv_zpow_pow`
- **Type**: `(j : ℤ) (x : OF F) : teichmuller p ((frobeniusEquiv (OF F) p ^ j) x) ^ p ^ (-j).toNat = teichmuller p x ^ p ^ j.toNat`
- **What**: Collapsing identity: raising the `φ^j`-twisted Teichmüller lift to the `p^{(-j)⁺}`-th power equals the plain lift raised to the `p^{j⁺}`-th power — the "clear the negative part of `j`" trick.
- **How**: Prove the `O_F`-level identity first by rewriting `frobeniusEquiv_pow_apply` backwards, merging the two `zpow`s with `← zpow_add` and the arithmetic fact `((-j).toNat : ℤ) + j = j.toNat` (`omega`); then transport along `map_pow` for the multiplicative `teichmuller`.
- **Hypotheses**: `O_F` perfect of characteristic `p`.
- **Uses from project**: `OF`, `frobeniusEquiv_pow_apply`
- **Used by**: `vle_theta_iff_ge`, `vle_theta_iff_le`
- **Visibility**: private
- **Lines**: 619–629 (9-line proof)
- **Notes**: none

### `private theorem smul_vle_iff`
- **Type**: `(g : Multiplicative ℤ) (w : Spv (Ainf p F)) (a b : Ainf p F) : (g • w).vle a b ↔ w.vle (g⁻¹ • a) (g⁻¹ • b)`
- **What**: The `φ^ℤ`-action on valuations translates comparisons: comparing `a, b` under `g • w` is comparing `g⁻¹ • a, g⁻¹ • b` under `w`.
- **How**: Unfold the action as `comap (MulSemiringAction.toRingHom _ _ g⁻¹)` and apply `comap_vle`, closing by `rfl`.
- **Hypotheses**: none.
- **Uses from project**: `Ainf`, `Spv.vle`, `comap`, `comap_vle`
- **Used by**: `KGE_smul_iff`, `KLE_smul_iff`, `KGE_cFF_smul_iff`, `KLE_zpow_smul_iff`
- **Visibility**: private
- **Lines**: 631–635 (3-line proof)
- **Notes**: extracts the local `hsmul_vle` `have` that appears inline in `smul_mem_Y`

### `private theorem smul_teichPi`
- **Type**: `(g : Multiplicative ℤ) : g • teichPi p F ϖ = teichmuller p ((frobeniusEquiv (OF F) p ^ (toAdd g)) (PseudoUniformizer.toOF F ϖ))`
- **What**: The action of `φ^g` on the Teichmüller lift `[ϖ]` is the Teichmüller lift of `φ^g(ϖ)`.
- **How**: Rewrite `g` as `ofAdd (toAdd g)`, unfold the `zsmul` action via `ofAdd_zsmul_def`, then apply `frob_zpow_teichmuller`.
- **Hypotheses**: none.
- **Uses from project**: `teichPi`, `OF`, `PseudoUniformizer.toOF`, `frob_zpow_teichmuller`
- **Used by**: `KGE_smul_iff`, `KLE_smul_iff`, `KGE_cFF_smul_iff`, `KLE_zpow_smul_iff`
- **Visibility**: private
- **Lines**: 637–641 (1-line proof)
- **Notes**: none

### `private theorem smul_natCast_p`
- **Type**: `(g : Multiplicative ℤ) : g • ((p : ℕ) : Ainf p F) = ((p : ℕ) : Ainf p F)`
- **What**: Frobenius fixes the image of `p` in `A_inf` (ring maps preserve natural-number casts).
- **How**: Rewrite the action via `ofAdd_zsmul_def` and apply `map_natCast` for the ring automorphism.
- **Hypotheses**: none.
- **Uses from project**: `Ainf`
- **Used by**: `KGE_smul_iff`, `KLE_smul_iff`, `KGE_cFF_smul_iff`, `KLE_zpow_smul_iff`
- **Visibility**: private
- **Lines**: 643–646 (2-line proof)
- **Notes**: none

### `private theorem zpow_eq_natCast_div`
- **Type**: `(n : ℤ) : ((p : ℚ)) ^ n = ((p ^ n.toNat : ℕ) : ℚ) / ((p ^ (-n).toNat : ℕ) : ℚ)`
- **What**: Writes the integer power `p^n ∈ ℚ` as an explicit quotient of two natural numbers — the fraction presentation needed to invoke `KGE_iff` / `KLE_iff`.
- **How**: Split `n` by `Int.eq_nat_or_neg`; the nonnegative case is `zpow_natCast` after `simp`, the negative case rewrites the two `toNat`s (by `omega`) and uses `zpow_neg`/`zpow_natCast`.
- **Hypotheses**: none.
- **Uses from project**: `[]`
- **Used by**: `KGE_smul_iff`, `KLE_zpow_smul_iff`, `cFF_mul_zpow_eq`
- **Visibility**: private
- **Lines**: 648–656 (7-line proof)
- **Notes**: none

### `private theorem cFF_mul_zpow_eq`
- **Type**: `(n : ℤ) : cFF p * (p : ℚ) ^ n = (((p + 1) * p ^ n.toNat : ℕ) : ℚ) / ((2 * p ^ (-n).toNat : ℕ) : ℚ)`
- **What**: The `ℕ/ℕ` fraction presentation of the window endpoint `c·p^n`, with numerator `(p+1)·p^{n⁺}` and denominator `2·p^{(-n)⁺}`.
- **How**: Unfold `cFF = (p+1)/2` and substitute `zpow_eq_natCast_div`, then combine the two quotients with `div_mul_div_comm`.
- **Hypotheses**: none.
- **Uses from project**: `cFF`, `zpow_eq_natCast_div`
- **Used by**: `KLE_smul_iff`, `KGE_cFF_smul_iff`
- **Visibility**: private
- **Lines**: 658–663 (3-line proof)
- **Notes**: none

### `private theorem vle_theta_iff_ge`
- **Type**: `{w : Spv (Ainf p F)} (k : ℤ) {α β α' β' : ℕ} (hβ : β ≠ 0) (hβ' : β' ≠ 0) (hcross : α' * (p^k.toNat * β) = (α * p^(-k).toNat) * β') : w.vle (teichmuller p ((frobeniusEquiv (OF F) p ^ k) ϖ) ^ β) (p ^ α) ↔ w.vle (teichPi p F ϖ ^ β') (p ^ α')`
- **What**: Core `KGE`-shape transport: comparing against the `φ^k`-twisted Teichmüller lift equals comparing against the plain lift, with exponents shifted by `p^{±k}`.
- **How**: Raise the twisted lift to the `p^{(-k)⁺}` power so that `teichmuller_frobeniusEquiv_zpow_pow` collapses it into `teichPi ^ (p^{k⁺}·β)`; both directions are then two applications of `vle_pow_iff_cross`, one with the trivial cross relation `α·(β·p^{(-k)⁺}) = (α·p^{(-k)⁺})·β` and one with the hypothesis `hcross`.
- **Hypotheses**: `β ≠ 0`, `β' ≠ 0`, and the cross relation `hcross` linking `(α, β)` to `(α', β')` through `p^{±k}`.
- **Uses from project**: `Ainf`, `OF`, `teichPi`, `PseudoUniformizer.toOF`, `vle_pow_iff_cross`, `teichmuller_frobeniusEquiv_zpow_pow`, `Spv.vle`
- **Used by**: `KGE_smul_iff`, `KGE_cFF_smul_iff`
- **Visibility**: private
- **Lines**: 665–699 (26-line proof)
- **Notes**: none

### `private theorem vle_theta_iff_le`
- **Type**: `{w : Spv (Ainf p F)} (k : ℤ) {α β α' β' : ℕ} (hα : α ≠ 0) (hα' : α' ≠ 0) (hβ : β ≠ 0) (hcross : α' * (p^k.toNat * β) = (α * p^(-k).toNat) * β') : w.vle (p ^ α) (teichmuller p ((frobeniusEquiv (OF F) p ^ k) ϖ) ^ β) ↔ w.vle (p ^ α') (teichPi p F ϖ ^ β')`
- **What**: Core `KLE`-shape transport, mirror of `vle_theta_iff_ge` with the two sides of `vle` exchanged.
- **How**: Same collapsing identity `teichmuller_frobeniusEquiv_zpow_pow` (giving `Tθ^(β·p^{(-k)⁺}) = teichPi^(p^{k⁺}·β)`), then two `vle_pow_iff_cross` steps per direction, with `hcross` transposed via `mul_comm` to match the `KLE` orientation.
- **Hypotheses**: `α ≠ 0`, `α' ≠ 0`, `β ≠ 0`, and the same cross relation `hcross`.
- **Uses from project**: `Ainf`, `OF`, `teichPi`, `PseudoUniformizer.toOF`, `vle_pow_iff_cross`, `teichmuller_frobeniusEquiv_zpow_pow`, `Spv.vle`
- **Used by**: `KLE_smul_iff`, `KLE_zpow_smul_iff`
- **Visibility**: private
- **Lines**: 701–740 (32-line proof)
- **Notes**: **proof >30 lines**

### `private theorem KGE_smul_iff`
- **Type**: `{w : Spv (Ainf p F)} (hw : w ∈ Y p F ϖ) (k n : ℤ) : KGE p F ϖ ((p:ℚ)^n) ((ofAdd k)⁻¹ • w) ↔ KGE p F ϖ ((p:ℚ)^(n-k)) w`
- **What**: The `κ ≥ p^n` condition transports along the Frobenius action with an index shift by `k`: `κ(φ^{-k}·w) ≥ p^n ⟺ κ(w) ≥ p^{n-k}`.
- **How**: `smul_mem_Y` keeps the translated point in 𝒴; rewrite both sides with `KGE_iff` using the fraction presentation `zpow_eq_natCast_div`, push the action through with `smul_vle_iff`, `smul_pow'`, `smul_teichPi`, `smul_natCast_p`, and finish with `vle_theta_iff_ge`, whose cross relation reduces (after `← pow_add`) to an exponent identity discharged by `omega`.
- **Hypotheses**: `w ∈ Y p F ϖ`; `p` prime.
- **Uses from project**: `KGE`, `Y`, `Ainf`, `KGE_iff`, `smul_mem_Y`, `smul_vle_iff`, `smul_teichPi`, `smul_natCast_p`, `zpow_eq_natCast_div`, `vle_theta_iff_ge`
- **Used by**: `zsmul_windowU`
- **Visibility**: private
- **Lines**: 742–754 (10-line proof)
- **Notes**: none

### `private theorem KLE_smul_iff`
- **Type**: `{w : Spv (Ainf p F)} (hw : w ∈ Y p F ϖ) (k n : ℤ) : KLE p F ϖ (cFF p * (p:ℚ)^n) ((ofAdd k)⁻¹ • w) ↔ KLE p F ϖ (cFF p * (p:ℚ)^(n-k)) w`
- **What**: Transport of the *upper* window endpoint `κ ≤ c·p^n` along the Frobenius action, with index shift `k`.
- **How**: As in `KGE_smul_iff` but with the `cFF_mul_zpow_eq` fraction presentation: `KLE_iff` on both sides, action pushed through by `smul_vle_iff`/`smul_teichPi`/`smul_natCast_p`, then `vle_theta_iff_le`; the cross relation is normalised by two ad-hoc `hnorm` identities `((p+1)·p^x)·(p^y·(2·p^z)) = ((p+1)·2)·p^{x+y+z}` and closed by `omega`.
- **Hypotheses**: `w ∈ Y p F ϖ`; `p` prime (`1 < p` for `one_lt_cFF`).
- **Uses from project**: `KLE`, `Y`, `cFF`, `one_lt_cFF`, `Ainf`, `KLE_iff`, `smul_mem_Y`, `smul_vle_iff`, `smul_teichPi`, `smul_natCast_p`, `cFF_mul_zpow_eq`, `vle_theta_iff_le`
- **Used by**: `zsmul_windowU`
- **Visibility**: private
- **Lines**: 756–785 (27-line proof)
- **Notes**: the two `hnorm` helpers duplicate those in `KGE_cFF_smul_iff` (lines 823–832) — dedup candidate

### `theorem zsmul_windowU`
- **Type**: `(k n : ℤ) : (Multiplicative.ofAdd k) • windowU p F ϖ n = windowU p F ϖ (n - k)`
- **What**: **Translation for the `U`-family**: the Frobenius action shifts Kedlaya's windows, `φ^k(U_n) = U_{n-k}` (convention `g • v = v ∘ φ^{-g}`, so `κ(g • v) = κ(v)/p^g`).
- **How**: Reduce membership in the translated set with `Set.mem_smul_set_iff_inv_smul_mem`, use `smul_mem_Y` (and `smul_inv_smul`) for the 𝒴-component, then apply `KGE_smul_iff` and `KLE_smul_iff` to the two endpoint conditions in each direction.
- **Hypotheses**: none beyond the ambient setup.
- **Uses from project**: `windowU`, `Y`, `KGE_smul_iff`, `KLE_smul_iff`, `smul_mem_Y`
- **Used by**: unused in file (headline translation theorem)
- **Visibility**: public
- **Lines**: 787–805 (11-line proof)
- **Notes**: docstring cites [Kedlaya-AWS, Rem. 3.1.9] and [SW, §12.2] ("κ∘φ = pκ")

### `private theorem KGE_cFF_smul_iff`
- **Type**: `{w : Spv (Ainf p F)} (hw : w ∈ Y p F ϖ) (k n : ℤ) : KGE p F ϖ (cFF p * (p:ℚ)^n) ((ofAdd k)⁻¹ • w) ↔ KGE p F ϖ (cFF p * (p:ℚ)^(n-k)) w`
- **What**: Transport of the *lower* endpoint of a `V`-window, `κ ≥ c·p^n`, along the Frobenius action with index shift `k`.
- **How**: Identical shape to `KLE_smul_iff` but on the `KGE` side: `KGE_iff` with the `cFF_mul_zpow_eq` presentation, action pushed by `smul_vle_iff`/`smul_teichPi`/`smul_natCast_p`, then `vle_theta_iff_ge` with the same two `hnorm` exponent-normalisation identities and `omega`.
- **Hypotheses**: `w ∈ Y p F ϖ`; `p` prime.
- **Uses from project**: `KGE`, `Y`, `cFF`, `one_lt_cFF`, `Ainf`, `KGE_iff`, `smul_mem_Y`, `smul_vle_iff`, `smul_teichPi`, `smul_natCast_p`, `cFF_mul_zpow_eq`, `vle_theta_iff_ge`
- **Used by**: `zsmul_windowV`
- **Visibility**: private
- **Lines**: 807–834 (26-line proof)
- **Notes**: `hnorm1`/`hnorm2` duplicated from `KLE_smul_iff` — dedup candidate

### `private theorem KLE_zpow_smul_iff`
- **Type**: `{w : Spv (Ainf p F)} (hw : w ∈ Y p F ϖ) (k n : ℤ) : KLE p F ϖ ((p:ℚ)^n) ((ofAdd k)⁻¹ • w) ↔ KLE p F ϖ ((p:ℚ)^(n-k)) w`
- **What**: Transport of the *upper* endpoint of a `V`-window, `κ ≤ p^n`, along the Frobenius action with index shift `k`.
- **How**: Dual of `KGE_smul_iff`: `KLE_iff` on both sides with the `zpow_eq_natCast_div` presentation, action pushed through by `smul_vle_iff`/`smul_teichPi`/`smul_natCast_p`, closed by `vle_theta_iff_le` whose cross relation becomes an exponent identity after `← pow_add`, discharged by `omega`.
- **Hypotheses**: `w ∈ Y p F ϖ`; `p` prime.
- **Uses from project**: `KLE`, `Y`, `Ainf`, `KLE_iff`, `smul_mem_Y`, `smul_vle_iff`, `smul_teichPi`, `smul_natCast_p`, `zpow_eq_natCast_div`, `vle_theta_iff_le`
- **Used by**: `zsmul_windowV`
- **Visibility**: private
- **Lines**: 836–848 (10-line proof)
- **Notes**: line 846 is 101 characters — over the 100-column mathlib limit

### `theorem zsmul_windowV`
- **Type**: `(k n : ℤ) : (Multiplicative.ofAdd k) • windowV p F ϖ n = windowV p F ϖ (n - k)`
- **What**: **Translation for the `V`-family**: `φ^k(V_n) = V_{n-k}`, so the Frobenius action permutes the `V`-windows among themselves.
- **How**: As for `zsmul_windowU` — `Set.mem_smul_set_iff_inv_smul_mem` plus `smul_mem_Y`/`smul_inv_smul` for the 𝒴-component — then `KGE_cFF_smul_iff` on the lower endpoint and `KLE_zpow_smul_iff` (at index `n+1`) on the upper, with the index bookkeeping `(n+1) - k = (n-k) + 1` supplied by `harith` and transported by `▸`.
- **Hypotheses**: none beyond the ambient setup.
- **Uses from project**: `windowV`, `Y`, `KGE_cFF_smul_iff`, `KLE_zpow_smul_iff`, `smul_mem_Y`
- **Used by**: unused in file (headline translation theorem)
- **Visibility**: public
- **Lines**: 850–865 (13-line proof)
- **Notes**: none

### `theorem windowU_disjoint`
- **Type**: `{n m : ℤ} (h : n ≠ m) : Disjoint (windowU p F ϖ n) (windowU p F ϖ m)`
- **What**: **Within-family disjointness** for the `U`-family: distinct `U`-windows are disjoint, because the κ-intervals `[p^n, c·p^n]` are pairwise disjoint when `c < p`.
- **How**: WLOG `n < m` (the statement is symmetric, `Disjoint.symm`); then `Set.disjoint_left` reduces to showing that `KLE (c·p^n)` and `KGE (p^m)` cannot coexist, which is exactly `not_KGE_of_KLE_of_lt` applied to the strict chain `c·p^n < p·p^n = p^{n+1} ≤ p^m` (using `cFF_lt_p`, `zpow_add_one₀`, `zpow_le_zpow_right₀`); positivity of `c·p^n` comes from `one_lt_cFF`.
- **Hypotheses**: `n ≠ m`; `p` prime (so `1 < c < p`).
- **Uses from project**: `windowU`, `cFF`, `one_lt_cFF`, `cFF_lt_p`, `not_KGE_of_KLE_of_lt`
- **Used by**: unused in file (headline disjointness theorem)
- **Visibility**: public
- **Lines**: 867–886 (13-line proof)
- **Notes**: docstring cites [Kedlaya-AWS, Rem. 3.1.9] ("hence is properly discontinuous"); `c < p` strictly is the load-bearing inequality

### `theorem windowV_disjoint`
- **Type**: `{n m : ℤ} (h : n ≠ m) : Disjoint (windowV p F ϖ n) (windowV p F ϖ m)`
- **What**: Within-family disjointness for the `V`-family: the κ-intervals `[c·p^n, p^{n+1}]` are pairwise disjoint because `1 < c`.
- **How**: WLOG `n < m`, `Set.disjoint_left`, then `not_KGE_of_KLE_of_lt` on the chain `p^{n+1} ≤ p^m = 1·p^m < c·p^m` (`zpow_le_zpow_right₀` then `mul_lt_mul_of_pos_right (one_lt_cFF hp1)`).
- **Hypotheses**: `n ≠ m`; `p` prime (so `1 < c`).
- **Uses from project**: `windowV`, `cFF`, `one_lt_cFF`, `not_KGE_of_KLE_of_lt`
- **Used by**: unused in file (headline disjointness theorem)
- **Visibility**: public
- **Lines**: 888–903 (12-line proof)
- **Notes**: here `1 < c` (rather than `c < p`) is the load-bearing inequality

### `private theorem not_vle_pow_p_zero`
- **Type**: `{v : Spv (Ainf p F)} (hv : v ∈ Y p F ϖ) (k : ℕ) : ¬ v.vle ((p : Ainf p F) ^ k) 0`
- **What**: On 𝒴, no power of `p` has zero valuation.
- **How**: If `v(p^k) = 0` then `p^k ∈ v.supp`, and primality of the support (`Ideal.IsPrime.mem_of_pow_mem` via `Spv.mem_supp_iff`) puts `p` itself in the support, contradicting `v_p_ne_zero`.
- **Hypotheses**: `v ∈ Y p F ϖ`.
- **Uses from project**: `Y`, `Ainf`, `v_p_ne_zero`, `Spv.supp`, `Spv.mem_supp_iff`, `Spv.vle`
- **Used by**: `isOpen_windowU`, `isOpen_windowV`
- **Visibility**: private
- **Lines**: 905–908 (3-line term proof)
- **Notes**: none

### `private theorem not_vle_pow_teichPi_zero`
- **Type**: `{v : Spv (Ainf p F)} (hv : v ∈ Y p F ϖ) (k : ℕ) : ¬ v.vle (teichPi p F ϖ ^ k) 0`
- **What**: On 𝒴, no power of `[ϖ]` has zero valuation.
- **How**: Mirror of `not_vle_pow_p_zero` — `Ideal.IsPrime.mem_of_pow_mem` on `v.supp` reduces to `v_teichPi_ne_zero`.
- **Hypotheses**: `v ∈ Y p F ϖ`.
- **Uses from project**: `Y`, `Ainf`, `teichPi`, `v_teichPi_ne_zero`, `Spv.supp`, `Spv.mem_supp_iff`, `Spv.vle`
- **Used by**: `isOpen_windowU`, `isOpen_windowV`
- **Visibility**: private
- **Lines**: 910–913 (3-line term proof)
- **Notes**: none

### `theorem isOpen_windowU`
- **Type**: `(n : ℤ) : IsOpen (Subtype.val ⁻¹' windowU p F ϖ n : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))`
- **What**: Each `U`-window is open in `Spa(A_inf, A_inf)`.
- **How**: Exhibit `U_n` as `𝒴 ∩ basicOpen([ϖ]^{den}, p^{num}) ∩ basicOpen(p^{num'}, [ϖ]^{den'})` — the two `KGE`/`KLE` inequalities *plus* the nonvanishing clauses supplied free of charge by `not_vle_pow_p_zero` / `not_vle_pow_teichPi_zero` on 𝒴 — then combine `isOpen_Y` with two `isOpen_basicOpen` preimages along `continuous_subtype_val` using `IsOpen.inter`.
- **Hypotheses**: none beyond the ambient setup.
- **Uses from project**: `windowU`, `Y`, `KGE`, `KLE`, `cFF`, `Ainf`, `Spa`, `ringPlus`, `teichPi`, `basicOpen`, `isOpen_basicOpen`, `isOpen_Y`, `not_vle_pow_p_zero`, `not_vle_pow_teichPi_zero`
- **Used by**: unused in file (headline openness theorem)
- **Visibility**: public
- **Lines**: 915–937 (20-line proof)
- **Notes**: the point of the proof is that `basicOpen f g` bundles `v(f) ≤ v(g)` *with* `v(g) ≠ 0`, and the second clause is automatic on 𝒴

### `theorem isOpen_windowV`
- **Type**: `(n : ℤ) : IsOpen (Subtype.val ⁻¹' windowV p F ϖ n : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))`
- **What**: Each `V`-window is open in `Spa(A_inf, A_inf)`.
- **How**: Verbatim the `isOpen_windowU` argument with the endpoints `c·p^n` and `p^{n+1}`: rewrite `V_n` as `𝒴` intersected with two `basicOpen`s (nonvanishing from `not_vle_pow_p_zero` / `not_vle_pow_teichPi_zero`), then `isOpen_Y` and `isOpen_basicOpen` under `continuous_subtype_val`.
- **Hypotheses**: none beyond the ambient setup.
- **Uses from project**: `windowV`, `Y`, `KGE`, `KLE`, `cFF`, `Ainf`, `Spa`, `ringPlus`, `teichPi`, `basicOpen`, `isOpen_basicOpen`, `isOpen_Y`, `not_vle_pow_p_zero`, `not_vle_pow_teichPi_zero`
- **Used by**: unused in file (headline openness theorem)
- **Visibility**: public
- **Lines**: 939–959 (18-line proof)
- **Notes**: near-verbatim duplicate of `isOpen_windowU` — decompose/dedup candidate (a shared `isOpen_of_KGE_KLE` helper parameterised by the two endpoints would cover both)

---

### File Summary

- **Total declarations: 57** (7 defs, 50 lemmas/theorems, 0 instances/structures/classes)
  - defs (all public): `vlt`, `Y`, `KGE`, `KLE`, `cFF`, `windowU`, `windowV`
  - 24 of the 50 theorems are `private` helpers; 26 are public API
- **Key API (used by 3+ others in this file)**:
  - `Y` (used by essentially every declaration), `vlt` (6), `KGE` (10), `KLE` (10), `cFF` (11), `windowU` (4), `windowV` (4)
  - `v_p_ne_zero` (8), `v_teichPi_ne_zero` (5), `vlt_p_one` (4), `smul_mem_Y` (6), `one_lt_cFF` (5)
  - `exists_pow_succ_vlt` (4), `pow_le_pow_iff_cross` (3), `KGE_iff` (3), `KLE_iff` (3), `not_KGE_of_KLE_of_lt` (3), `zpow_eq_natCast_div` (3)
  - `smul_vle_iff` (4), `smul_teichPi` (4), `smul_natCast_p` (4)
- **Unused declarations (in this file — these are the exported headline results plus a few strays)**:
  - Headline API, expected to be consumed downstream: `Y_eq_iUnion_windows`, `zsmul_windowU`, `zsmul_windowV`, `windowU_disjoint`, `windowV_disjoint`, `isOpen_windowU`, `isOpen_windowV`, `Y_indep`, `vlt_teichPi_one`
  - Genuinely unused strays worth flagging: `Y_subset_spa` (callers use `.1` inline), `Y_eq_spa_inter_basicOpen` (`isOpen_Y` re-derives it inline), `KLE_mono` (the `KGE_mono` dual — only `KGE_mono` is used, by `Y_eq_iUnion_windows`), `cFF_lt_p` (used only by `windowU_disjoint`, i.e. exactly once)
- **Declarations with `sorry`**: none — the file is sorry-free
- **Declarations with `set_option`**: none — no `maxHeartbeats` / `maxRecDepth` bumps anywhere in the file
- **Proofs >30 lines**:
  - `Y_eq_iUnion_windows` — 66 lines (535–601)
  - `not_KGE_of_KLE_of_lt` — 45 lines (355–407)
  - `KGE_mono` — 40 lines (451–491)
  - `KLE_mono` — 40 lines (493–533)
  - `vle_theta_iff_le` — 32 lines (701–740)
  - (just under: `smul_mem_Y` 29, `KLE_smul_iff` 27, `vle_theta_iff_ge` 26, `KGE_cFF_smul_iff` 25)

#### Cleanup observations
1. **Two misplaced docstrings.** The `/-- **The covering** ... -/` block (lines 443–450) sits above `KGE_mono` but describes `Y_eq_iUnion_windows`; the `/-- **Translation** ... -/` block (lines 603–608) sits above the private `vle_pow_iff_cross` but describes `zsmul_windowU` (whose own copy at 787–792 is correct). Consequently `KGE_mono`, `KLE_mono` and `Y_eq_iUnion_windows` are effectively undocumented.
2. **Repeated `hbridge` idiom.** The four-line `have hbridge : ∀ s t, v.vle s t ↔ valuation s ≤ valuation t := fun s t => (…).vle_iff_le` block is copy-pasted in eight proofs (`exists_pow_succ_vlt`, `KGE_iff`, `KLE_iff`, `not_KGE_of_KLE_of_lt`, `KGE_mono`, `KLE_mono`, `vle_pow_iff_cross`, …) — a one-line private lemma would remove ~30 lines.
3. **Repeated `hy0`/`hy1` blocks** (`0 < v(p)` and `v(p) < 1` on 𝒴, from `v_p_ne_zero` + `vlt_p_one`) appear verbatim in `not_KGE_of_KLE_of_lt`, `KGE_mono` and `KLE_mono` — another extractable private lemma pair.
4. **`hnorm1`/`hnorm2`** are duplicated verbatim between `KLE_smul_iff` (774–783) and `KGE_cFF_smul_iff` (823–832).
5. **`isOpen_windowU` / `isOpen_windowV`** are near-verbatim duplicates differing only in the two rational endpoints.
6. **Line 846 exceeds 100 columns** (101 chars).
7. **Unused hypotheses**: `hv` in `KGE_iff` and `KLE_iff`; `hv` and `hq` in `KGE_or_KLE`. Kept for API uniformity, but they may trigger linter warnings.

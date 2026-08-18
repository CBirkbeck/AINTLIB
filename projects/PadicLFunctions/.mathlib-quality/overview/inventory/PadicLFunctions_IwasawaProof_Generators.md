# Inventory: `PadicLFunctions/IwasawaProof/Generators.lean`

Generators for the cyclotomic units (RJW §12.3–12.4, TeX 3450–3578) — E12.4. The conjugation-fixed units `γ_{n,a} = ξ^{(1−a)/2} c_n(a) ∈ 𝒟_n^+`; the global generator lemmas; the closure lemma (p-adic closure of a `ℤ`-span = `ℤ_p`-span); and the Λ(𝒢^+)-cyclicity of `𝒞_{∞,1}^+`. All in `namespace PadicLFunctions.Coleman`, `variable (p : ℕ) [hp : Fact p.Prime]`, `noncomputable section`.

---

### def zhp
- Type: `def zhp {n : ℕ} (c : ZMod (p ^ n)) : ℂ_[p] := zetaSys p n ^ c.val`
- What: The root of unity `ξ_{p^n}` raised to the exponent given by a `ZMod (p^n)` element `c` (a total realisation of `ξ^c`).
- How: Direct definition as `zetaSys p n ^ c.val`.
- Hypotheses: Level `n`; exponent `c ∈ ZMod (p^n)`.
- Uses from project: [zetaSys]
- Used by: zhp_natCast, zhp_add, zhp_zero, zhp_mul_neg, zhp_ne_zero, norm_zhp, gammaUnit, gammaUnit_eq_sum, zhp_neg, gammaUnit_mem_FglobalPlus, norm_zhp_sub_one_lt
- Visibility: public
- Lines: 37–39 (def, 1 line)
- Notes: none

### theorem zhp_natCast
- Type: `theorem zhp_natCast {n : ℕ} (k : ℕ) : zhp p (k : ZMod (p ^ n)) = zetaSys p n ^ k`
- What: `zhp` on a natural-number cast equals the plain power `ξ^k`.
- How: Applies `zetaSys_pow_eq_pow_of_modEq` (exponents differ by a multiple of `p^n`); the modEq is discharged via `ZMod.natCast_eq_natCast_iff` and `ZMod.cast_id`.
- Hypotheses: Level `n`; natural `k`.
- Uses from project: [zhp, zetaSys, zetaSys_pow_eq_pow_of_modEq]
- Used by: zhp_zero, gammaUnit_eq_sum, norm_zetaSys_eq_one
- Visibility: public
- Lines: 41–45 (proof 3 lines)
- Notes: none

### theorem zhp_add
- Type: `theorem zhp_add {n : ℕ} (c d : ZMod (p ^ n)) : zhp p (c + d) = zhp p c * zhp p d`
- What: `zhp` is multiplicative/additive in the exponent: `zhp (c+d) = zhp c · zhp d`.
- How: Unfolds `zhp`, uses `← pow_add`, then `zetaSys_pow_eq_pow_of_modEq` to reconcile `(c+d).val` with `c.val + d.val` mod `p^n`.
- Hypotheses: Level `n`; exponents `c, d ∈ ZMod (p^n)`.
- Uses from project: [zhp, zetaSys_pow_eq_pow_of_modEq]
- Used by: zhp_zero, zhp_mul_neg, gammaUnit_eq_sum
- Visibility: public
- Lines: 47–52 (proof 5 lines)
- Notes: none

### theorem zhp_zero
- Type: `@[simp] theorem zhp_zero {n : ℕ} : zhp p (0 : ZMod (p ^ n)) = 1`
- What: `zhp 0 = 1`.
- How: Rewrites `0` as a natural cast, applies `zhp_natCast` and `pow_zero`.
- Hypotheses: Level `n`.
- Uses from project: [zhp, zhp_natCast]
- Used by: zhp_mul_neg
- Visibility: public (simp)
- Lines: 54–56 (proof 1 line)
- Notes: none

### theorem zhp_mul_neg
- Type: `theorem zhp_mul_neg {n : ℕ} (c : ZMod (p ^ n)) : zhp p c * zhp p (-c) = 1`
- What: `zhp c · zhp (−c) = 1`.
- How: `← zhp_add`, `add_neg_cancel`, `zhp_zero`.
- Hypotheses: Level `n`; exponent `c`.
- Uses from project: [zhp, zhp_add, zhp_zero]
- Used by: zhp_ne_zero, zhp_neg
- Visibility: public
- Lines: 58–60 (proof 1 line)
- Notes: none

### theorem zhp_ne_zero
- Type: `theorem zhp_ne_zero {n : ℕ} (c : ZMod (p ^ n)) : zhp p c ≠ 0`
- What: `zhp c ≠ 0` (a power of the nonzero `ξ`).
- How: From `zhp_mul_neg`, if `zhp c = 0` then `0 = 1` via `zero_mul`, contradiction with `one_ne_zero`.
- Hypotheses: Level `n`; exponent `c`.
- Uses from project: [zhp, zhp_mul_neg]
- Used by: gammaUnit_mem_cycloUnitsPlus, zetaSys_pow_sub_one_mem_aug_coprime, norm_zhp_sub_one_lt (indirectly via gammaUnit), gammaUnit_mem_cycloUnitsPlus
- Visibility: public
- Lines: 62–66 (proof 3 lines)
- Notes: none

### theorem norm_zhp
- Type: `theorem norm_zhp {n : ℕ} (c : ZMod (p ^ n)) : ‖zhp p c‖ = 1`
- What: `‖zhp c‖ = 1` (`ξ` has norm 1).
- How: Shows `‖ξ‖ = 1` by `le_antisymm`: `‖ξ‖^(p^n) = 1` via `(zetaSys_primitiveRoot p n).pow_eq_one`, then excludes `>1` and `<1` using `one_lt_pow₀` / `pow_lt_one₀`.
- Hypotheses: Level `n`; exponent `c`.
- Uses from project: [zhp, zetaSys, zetaSys_primitiveRoot]
- Used by: norm_zetaSys_eq_one, valHom_eq_one_of_mem_closure_gammaGenSet
- Visibility: public
- Lines: 68–78 (proof 9 lines)
- Notes: none

### def halfExp
- Type: `def halfExp (a n : ℕ) : ZMod (p ^ n) := (1 - (a : ZMod (p ^ n))) * (2 : ZMod (p ^ n))⁻¹`
- What: The half-power exponent `(1−a)/2 ∈ ZMod (p^n)` of `γ_{n,a}` (RJW TeX 3458).
- How: Direct definition via `(2 : ZMod (p^n))⁻¹` (valid since `p` odd).
- Hypotheses: Integers `a, n`.
- Uses from project: []
- Used by: gammaUnit, gammaUnit_eq_sum, halfExp_add_symm, gammaUnit_mem_FglobalPlus, gammaUnit_mem_cycloUnitsPlus, zetaSys_pow_sub_one_mem_aug_coprime, norm_cycloUnit_sub_natCast_lt (via gammaUnit), gammaUnit_congr_natCast
- Visibility: public
- Lines: 80–81 (def, 1 line)
- Notes: none

### def gammaUnit
- Type: `def gammaUnit (a n : ℕ) : ℂ_[p] := zhp p (halfExp p a n) * cycloUnit p a n`
- What: The conjugation-fixed cyclotomic unit `γ_{n,a} = ξ_{p^n}^{(1−a)/2} c_n(a)` (RJW TeX 3458).
- How: Direct product of the half-power `zhp(halfExp)` and the cyclotomic unit `cycloUnit`.
- Hypotheses: Integers `a, n`.
- Uses from project: [zhp, halfExp, cycloUnit]
- Used by: gammaUnit_eq_sum, gammaUnit_mem_FglobalPlus, gammaUnit_mem_cycloUnitsPlus, gammaGenSet, coe_mem_FglobalPlus_of_mem_closure_gammaGenSet, valHom_eq_one_of_mem_closure_gammaGenSet, zetaSys_pow_sub_one_mem_aug_coprime, cycloUnitsPlus_eq_closure_gammas, gammaUnit_congr_natCast, gammaUnit_congr_natCast_tower
- Visibility: public
- Lines: 83–85 (def, 1 line)
- Notes: none

### theorem zetaSys_add_inv_mem_FglobalPlus
- Type: `private theorem zetaSys_add_inv_mem_FglobalPlus (n : ℕ) : zetaSys p n + (zetaSys p n)⁻¹ ∈ FglobalPlus p n`
- What: `ξ_{p^n} + ξ_{p^n}⁻¹` lies in `F_n⁺` (the chosen generator).
- How: `IntermediateField.mem_adjoin_simple_self` (the generator of the simple adjunction).
- Hypotheses: Level `n`.
- Uses from project: [zetaSys, FglobalPlus]
- Used by: cosPow_mem_FglobalPlus
- Visibility: private
- Lines: 96–98 (proof 1 line)
- Notes: none

### theorem cosPow_mem_FglobalPlus
- Type: `private theorem cosPow_mem_FglobalPlus (n : ℕ) (m : ℕ) : zetaSys p n ^ m + (zetaSys p n ^ m)⁻¹ ∈ FglobalPlus p n`
- What: Every "cosine power" `ξ^m + (ξ^m)⁻¹` lies in `F_n⁺`.
- How: `Nat.twoStepInduction` using the Chebyshev recurrence `c_{m+2} = c_1·c_{m+1} − c_m`; the recurrence identity is proved by `field_simp; ring`, then `sub_mem (mul_mem … ih2) ih1`.
- Hypotheses: Level `n`; exponent `m`.
- Uses from project: [zetaSys, FglobalPlus, zetaSys_primitiveRoot, zetaSys_add_inv_mem_FglobalPlus]
- Used by: gammaUnit_mem_FglobalPlus
- Visibility: private
- Lines: 100–118 (proof 16 lines)
- Notes: none

### theorem cycloUnit_eq_geomSum
- Type: `private theorem cycloUnit_eq_geomSum {a : ℕ} {n : ℕ} (hn : 1 ≤ n) : cycloUnit p a n = ∑ i ∈ Finset.range a, zetaSys p n ^ i`
- What: `c_n(a)` as a geometric sum `∑_{i<a} ξ^i`.
- How: Unfolds `cycloUnit` as `(ξ^a−1)/(ξ−1)`; `div_eq_iff hne` with `geom_sum_mul`, using `ξ−1 ≠ 0` from `zetaSys_primitiveRoot.ne_one`.
- Hypotheses: `n ≥ 1`; integer `a`.
- Uses from project: [cycloUnit, zetaSys, zetaSys_primitiveRoot]
- Used by: gammaUnit_eq_sum, gammaUnit_mem_cycloUnitsPlus, norm_cycloUnit_sub_natCast_lt
- Visibility: private
- Lines: 122–126 (proof 3 lines)
- Notes: none

### theorem gammaUnit_eq_sum
- Type: `private theorem gammaUnit_eq_sum (a : ℕ) {n : ℕ} (hn : 1 ≤ n) : gammaUnit p a n = ∑ i ∈ Finset.range a, zhp p (halfExp p a n + (i : ZMod (p ^ n)))`
- What: `γ_{n,a}` as a geometric sum of half-power roots `∑_{i<a} ξ^{(1−a)/2+i}`.
- How: Rewrites `gammaUnit` via `cycloUnit_eq_geomSum` and `Finset.mul_sum`; each summand handled by `zhp_add` and `zhp_natCast`.
- Hypotheses: `n ≥ 1`; integer `a`.
- Uses from project: [gammaUnit, zhp, halfExp, cycloUnit_eq_geomSum, zhp_add, zhp_natCast]
- Used by: gammaUnit_mem_FglobalPlus
- Visibility: private
- Lines: 128–131 (proof 2 lines)
- Notes: none

### theorem isUnit_two_zmod
- Type: `private theorem isUnit_two_zmod (hp2 : p ≠ 2) (n : ℕ) : IsUnit (2 : ZMod (p ^ n))`
- What: `2` is a unit of `ZMod (p^n)` for `p` odd.
- How: Rewrites `2` as a natural cast and `ZMod.isUnit_iff_coprime`; coprimality from `Nat.Coprime.pow_right` and `Nat.coprime_primes`.
- Hypotheses: `p ≠ 2`; level `n`.
- Uses from project: []
- Used by: two_mul_inv_two, halfExp_add_symm
- Visibility: private
- Lines: 133–136 (proof 2 lines)
- Notes: none

### theorem two_mul_inv_two
- Type: `private theorem two_mul_inv_two (hp2 : p ≠ 2) (n : ℕ) : (2 : ZMod (p ^ n)) * (2 : ZMod (p ^ n))⁻¹ = 1`
- What: `2 · 2⁻¹ = 1` in `ZMod (p^n)` for `p` odd.
- How: `ZMod.mul_inv_of_unit` applied to `isUnit_two_zmod`.
- Hypotheses: `p ≠ 2`; level `n`.
- Uses from project: [isUnit_two_zmod]
- Used by: halfExp_add_symm
- Visibility: private
- Lines: 138–141 (proof 1 line)
- Notes: none

### theorem halfExp_add_symm
- Type: `private theorem halfExp_add_symm (hp2 : p ≠ 2) {a : ℕ} (n : ℕ) {i : ℕ} (hi : i < a) : halfExp p a n + ((a - 1 - i : ℕ) : ZMod (p ^ n)) = -(halfExp p a n + (i : ZMod (p ^ n)))`
- What: The reindexing symmetry of the half-exponents: `halfExp a n + (a−1−i) = −(halfExp a n + i)`.
- How: Casts `(a−1−i)` via `Nat.cast_sub`; computes `2·halfExp = 1−a` (cancel `two_mul_inv_two`); reduces to a pure `ZMod` equation, cleared by `(isUnit_two_zmod).mul_left_cancel` then `ring`.
- Hypotheses: `p ≠ 2`; `i < a`; level `n`.
- Uses from project: [halfExp, isUnit_two_zmod, two_mul_inv_two]
- Used by: gammaUnit_mem_FglobalPlus
- Visibility: private
- Lines: 143–163 (proof 18 lines)
- Notes: none

### theorem zhp_neg
- Type: `private theorem zhp_neg {n : ℕ} (c : ZMod (p ^ n)) : zhp p (-c) = (zhp p c)⁻¹`
- What: `zhp (−c) = (zhp c)⁻¹` (the inverse half-power).
- How: `eq_inv_of_mul_eq_one_left` using `zhp_mul_neg` (after `mul_comm`).
- Hypotheses: Level `n`; exponent `c`.
- Uses from project: [zhp, zhp_mul_neg]
- Used by: gammaUnit_mem_FglobalPlus, gammaUnit_mem_cycloUnitsPlus, zetaSys_pow_sub_one_mem_aug_coprime
- Visibility: private
- Lines: 165–167 (proof 1 line)
- Notes: none

### theorem gammaUnit_mem_FglobalPlus
- Type: `private theorem gammaUnit_mem_FglobalPlus {a : ℕ} (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) : gammaUnit p a n ∈ FglobalPlus p n`
- What: Conjugation-fixedness `γ_{n,a} ∈ F_n⁺` (RJW TeX 3459): `γ` is a symmetric geometric sum, expressible (after averaging the reflection `i ↦ a−1−i`) as a sum of `cosPow` terms.
- How: Sets `S = ∑ zhp(halfExp+i)`; the reflected sum equals `S` via `Finset.sum_range_reflect` + `halfExp_add_symm`; then `2S = ∑(zhp c + (zhp c)⁻¹)` each in `F_n⁺` by `cosPow_mem_FglobalPlus`; finally `γ = 2⁻¹·(2S)` with `2⁻¹ ∈ ℚ ⊆ F_n⁺` (`SubfieldClass.ratCast_mem`).
- Hypotheses: `p ≠ 2`; `n ≥ 1`; integer `a`.
- Uses from project: [gammaUnit, zhp, halfExp, FglobalPlus, gammaUnit_eq_sum, halfExp_add_symm, zhp_neg, zetaSys, cosPow_mem_FglobalPlus]
- Used by: gammaUnit_mem_cycloUnitsPlus, coe_mem_FglobalPlus_of_mem_closure_gammaGenSet
- Visibility: private
- Lines: 169–203 (proof 32 lines)
- Notes: long(30-50)

### theorem gammaUnit_mem_cycloUnitsPlus
- Type: `theorem gammaUnit_mem_cycloUnitsPlus {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) : ∃ g : ℂ_[p]ˣ, (g : ℂ_[p]) = gammaUnit p a n ∧ g ∈ cycloUnitsPlus p n`
- What: `γ_{n,a} ∈ 𝒟_n^+` (conjugation-fixed, RJW TeX 3458–3459) — packaged as a unit lying in `cycloUnitsPlus`.
- How: Builds `Units.mk0 (gammaUnit) hγ0`; proves `𝒟_n = closure(cycloGenSet) ⊓ globalUnits` membership using the milestone `cyclo_elems_mem_cycloUnits` for the `c_n(a)`-factor, the `ξ`-power half-factor as `ζu^(halfExp.val)` in the closure, plus `Fglobal` membership and integrality (`isIntegral_cycloUnit`, `isIntegral_inv_cycloUnit`, `monic_X_pow_sub_C`); `F_n⁺` membership from `gammaUnit_mem_FglobalPlus`.
- Hypotheses: `p ∤ a`; `p ≠ 2`; `n ≥ 1`.
- Uses from project: [gammaUnit, zhp, zhp_ne_zero, cycloUnit_ne_zero, cycloUnitsPlus, cycloUnits, cyclo_elems_mem_cycloUnits, cyclo, cycloUnit, cycloGenSet, zetaSys, zetaSys_primitiveRoot, halfExp, Fglobal, cycloUnit_eq_geomSum, isIntegral_cycloUnit, isIntegral_inv_cycloUnit, zhp_neg, gammaUnit_mem_FglobalPlus]
- Used by: cycloUnitsPlus_eq_closure_gammas
- Visibility: public
- Lines: 205–261 (proof 55 lines)
- Notes: OVER-50 (needs /decompose-proof)

### theorem neg_one_mem_cycloUnitsPlus
- Type: `private theorem neg_one_mem_cycloUnitsPlus {n : ℕ} : (-1 : ℂ_[p]ˣ) ∈ cycloUnitsPlus p n`
- What: `−1` (as a unit) lies in `𝒟_n^+`: it is `(−ξ)·ξ⁻¹`, a global unit, and rational hence in `F_n⁺`.
- How: Shows `−1 = negζu * ζu⁻¹` in `closure(cycloGenSet)` (via `Subgroup.subset_closure` on the `±ξ` generators); rational-and-integral `𝒱_n` membership (`isIntegral_one.neg`); rational `F_n⁺` membership.
- Hypotheses: Level `n`.
- Uses from project: [cycloUnitsPlus, cycloUnits, zetaSys, zetaSys_primitiveRoot, cycloGenSet]
- Used by: cycloUnitsPlus_eq_closure_gammas
- Visibility: private
- Lines: 263–294 (proof 28 lines)
- Notes: none

### theorem norm_zetaSys_eq_one
- Type: `private theorem norm_zetaSys_eq_one (n : ℕ) : ‖zetaSys p n‖ = 1`
- What: `‖ξ_{p^n}‖ = 1` (a primitive `p^n`-th root of unity).
- How: `‖ξ‖ = ‖ξ^1‖ = ‖zhp 1‖ = 1` via `← zhp_natCast` and `norm_zhp`.
- Hypotheses: Level `n`.
- Uses from project: [zetaSys, zhp_natCast, norm_zhp]
- Used by: zetaSys_ne_zero, norm_zetaSys_pow_sub_one_lt, cycloUnitsPlus_eq_closure_gammas, norm_cycloUnit_sub_natCast_lt
- Visibility: private
- Lines: 308–310 (proof 1 line)
- Notes: none

### theorem zetaSys_ne_zero
- Type: `private theorem zetaSys_ne_zero (n : ℕ) : zetaSys p n ≠ 0`
- What: `ξ_{p^n} ≠ 0`.
- How: `norm_ne_zero_iff.mp` from `norm_zetaSys_eq_one`.
- Hypotheses: Level `n`.
- Uses from project: [zetaSys, norm_zetaSys_eq_one]
- Used by: zetaSysUnit
- Visibility: private
- Lines: 312–314 (proof 1 line)
- Notes: none

### def valHom
- Type: `private def valHom : ℂ_[p]ˣ →* Multiplicative ℝ` (toFun `u ↦ ofAdd(−log‖u‖)`)
- What: The additive valuation `V u = −log‖u‖` as a `MonoidHom` into `Multiplicative ℝ`.
- How: `map_one'` by `simp`; `map_mul'` via `Real.log_mul` of the multiplicative norm, then `ring`.
- Hypotheses: None beyond the section variables.
- Uses from project: []
- Used by: valHom_eq_one_of_norm_one, valHom_eq_one_of_mem_closure_gammaGenSet, valHom_deltaUnit_ne_one, cycloUnitsPlus_eq_closure_gammas
- Visibility: private
- Lines: 316–328 (def with proofs, ~10 lines)
- Notes: none

### theorem valHom_eq_one_of_norm_one
- Type: `private theorem valHom_eq_one_of_norm_one {u : ℂ_[p]ˣ} (h : ‖(u : ℂ_[p])‖ = 1) : valHom p u = 1`
- What: `V` vanishes on norm-1 units.
- How: Unfolds `valHom`; `Real.log_one`, `neg_zero` give `ofAdd 0 = 1`.
- Hypotheses: `‖u‖ = 1`.
- Uses from project: [valHom]
- Used by: valHom_eq_one_of_mem_closure_gammaGenSet, cycloUnitsPlus_eq_closure_gammas
- Visibility: private
- Lines: 330–334 (proof 2 lines)
- Notes: none

### theorem galAutNegOne_zetaSys
- Type: `private theorem galAutNegOne_zetaSys {n : ℕ} (hn : 1 ≤ n) : (galAut p (-1) n ⟨zetaSys p n, zetaSys_mem_K p n⟩ : ℂ_[p]) = (zetaSys p n)⁻¹`
- What: Conjugation `σ_{−1}` sends `ξ_{p^n} ↦ ξ_{p^n}⁻¹` (cyclotomic-character value `−1`).
- How: `galAut_zetaSys`; shows `unitsToZModPow p n (−1) = −1` via `Units.ext`/`unitsToZModPow_coe`; then `ξ^{(−1).val} = ξ⁻¹` via `eq_inv_of_mul_eq_one_left` and `zetaSys_pow_eq_pow_of_modEq`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [galAut, zetaSys, zetaSys_mem_K, galAut_zetaSys, PadicMeasure.unitsToZModPow, PadicMeasure.unitsToZModPow_coe, zetaSys_pow_eq_pow_of_modEq]
- Used by: galAutNegOne_gen, zetaSysUnit_zpow_eq_one_of_mem_FglobalPlus
- Visibility: private
- Lines: 336–349 (proof 9 lines)
- Notes: none

### theorem galAutNegOne_gen
- Type: `private theorem galAutNegOne_gen {n : ℕ} (hn : 1 ≤ n) (hzK : zetaSys p n + (zetaSys p n)⁻¹ ∈ K p n) : (galAut p (-1) n ⟨zetaSys p n + (zetaSys p n)⁻¹, hzK⟩ : ℂ_[p]) = zetaSys p n + (zetaSys p n)⁻¹`
- What: Conjugation `σ_{−1}` fixes the generator `ξ + ξ⁻¹` of `F_n⁺`.
- How: Decomposes the subtype element as `⟨ξ⟩ + ⟨ξ⟩⁻¹`; pushes `galAut` through `map_add`/`map_inv₀`; applies `galAutNegOne_zetaSys`, `inv_inv`, `add_comm`.
- Hypotheses: `n ≥ 1`; `ξ+ξ⁻¹ ∈ K_n`.
- Uses from project: [galAut, zetaSys, zetaSys_mem_K, K, galAutNegOne_zetaSys]
- Used by: galAutNegOne_fixes_FglobalPlus
- Visibility: private
- Lines: 351–364 (proof 9 lines)
- Notes: none

### theorem galAutNegOne_fixes_FglobalPlus
- Type: `private theorem galAutNegOne_fixes_FglobalPlus {n : ℕ} (hn : 1 ≤ n) {x : ℂ_[p]} (hx : x ∈ FglobalPlus p n) (hxK : x ∈ K p n) : (galAut p (-1) n ⟨x, hxK⟩ : ℂ_[p]) = x`
- What: Reality of `F_n⁺`: conjugation `σ_{−1}` fixes every element of `F_n⁺` pointwise.
- How: `IntermediateField.adjoin_induction` over `F_n⁺ = ℚ(ξ+ξ⁻¹)`: base case `galAutNegOne_gen`; `algebraMap`/`ℚ` fixed via `map_ratCast`; `add`/`inv`/`mul` cases push `galAut` through `map_add`/`map_inv₀`/`map_mul`; auxiliary `toK` lifts `FglobalPlus` membership to `K`.
- Hypotheses: `n ≥ 1`; `x ∈ F_n⁺` and `x ∈ K_n`.
- Uses from project: [galAut, FglobalPlus, K, Fglobal_le_K, FglobalPlus_le_Fglobal, galAutNegOne_gen]
- Used by: zetaSysUnit_zpow_eq_one_of_mem_FglobalPlus
- Visibility: private
- Lines: 366–404 (proof 36 lines)
- Notes: long(30-50)

### theorem zpow_eq_one_of_two_mul
- Type: `private theorem zpow_eq_one_of_two_mul {n : ℕ} (hp2 : p ≠ 2) (ζu : ℂ_[p]ˣ) (hord : orderOf ζu = p ^ n) (m : ℤ) (h2m : ζu ^ (2 * m) = 1) : ζu ^ m = 1`
- What: For `p` odd, a `ξ`-power that is real (`ξ^{2m}=1`) is trivial (`ξ^m=1`).
- How: `← orderOf_dvd_iff_zpow_eq_one`; coprimality `IsCoprime (p^n) 2` from `Nat.Coprime.pow_left` + `coprime_primes`; concludes via `hcop.dvd_of_dvd_mul_left`.
- Hypotheses: `p ≠ 2`; `orderOf ζu = p^n`; `ζu^{2m} = 1`.
- Uses from project: []
- Used by: zetaSysUnit_zpow_eq_one_of_mem_FglobalPlus
- Visibility: private
- Lines: 406–415 (proof 6 lines)
- Notes: none

### def zetaSysUnit
- Type: `private def zetaSysUnit (n : ℕ) : ℂ_[p]ˣ := Units.mk0 (zetaSys p n) (zetaSys_ne_zero p n)`
- What: `ξ_{p^n}` packaged as a unit of `ℂ_[p]ˣ`.
- How: `Units.mk0` with the nonzero witness `zetaSys_ne_zero`.
- Hypotheses: Level `n`.
- Uses from project: [zetaSys, zetaSys_ne_zero]
- Used by: zetaSysUnit_val, orderOf_zetaSysUnit, zetaSysUnit_zpow_val, zetaSysUnit_zpow_eq_one_of_mem_FglobalPlus, gammaGenSet (no), augGenSet, zetaSysUnit_mem_aug, zetaSys_pow_sub_one_mem_aug_coprime, mem_aug_normal_form, closure_cycloGenSet_le_aug, cycloUnitsPlus_eq_closure_gammas
- Visibility: private
- Lines: 417–418 (def, 1 line)
- Notes: none

### theorem zetaSysUnit_val
- Type: `private theorem zetaSysUnit_val (n : ℕ) : (zetaSysUnit p n : ℂ_[p]) = zetaSys p n`
- What: `zetaSysUnit` coerces to `ξ`.
- How: `Units.val_mk0`.
- Hypotheses: Level `n`.
- Uses from project: [zetaSysUnit, zetaSys]
- Used by: orderOf_zetaSysUnit, zetaSysUnit_zpow_val, zetaSys_pow_sub_one_mem_aug_coprime, closure_cycloGenSet_le_aug, cycloUnitsPlus_eq_closure_gammas
- Visibility: private
- Lines: 420–421 (proof 1 line)
- Notes: none

### theorem orderOf_zetaSysUnit
- Type: `private theorem orderOf_zetaSysUnit (n : ℕ) : orderOf (zetaSysUnit p n) = p ^ n`
- What: `orderOf (ξ_{p^n} : ℂ_[p]ˣ) = p^n`.
- How: Shows `IsPrimitiveRoot (zetaSysUnit) (p^n)` via `← IsPrimitiveRoot.coe_units_iff` and `zetaSys_primitiveRoot`, then `.eq_orderOf.symm`.
- Hypotheses: Level `n`.
- Uses from project: [zetaSysUnit, zetaSysUnit_val, zetaSys_primitiveRoot]
- Used by: zetaSysUnit_zpow_eq_one_of_mem_FglobalPlus
- Visibility: private
- Lines: 423–428 (proof 4 lines)
- Notes: none

### theorem zetaSysUnit_zpow_val
- Type: `private theorem zetaSysUnit_zpow_val (n : ℕ) (m : ℤ) : ((zetaSysUnit p n ^ m : ℂ_[p]ˣ) : ℂ_[p]) = (zetaSys p n) ^ m`
- What: `(ξ^m : ℂ_[p]ˣ)` coerces to `ξ^m` in `ℂ_[p]`.
- How: `Units.val_zpow_eq_zpow_val` then `zetaSysUnit_val`.
- Hypotheses: Level `n`; integer `m`.
- Uses from project: [zetaSysUnit, zetaSysUnit_val, zetaSys]
- Used by: zetaSysUnit_zpow_eq_one_of_mem_FglobalPlus
- Visibility: private
- Lines: 430–433 (proof 1 line)
- Notes: none

### theorem zetaSysUnit_zpow_eq_one_of_mem_FglobalPlus
- Type: `private theorem zetaSysUnit_zpow_eq_one_of_mem_FglobalPlus {n : ℕ} (hp2 : p ≠ 2) (hn : 1 ≤ n) (m : ℤ) (hmem : ((zetaSysUnit p n ^ m : ℂ_[p]ˣ) : ℂ_[p]) ∈ FglobalPlus p n) : zetaSysUnit p n ^ m = 1`
- What: Reality kills the `ξ`-power (RJW TeX 3478–3482): if `ξ^m ∈ F_n⁺` then `ξ^m = 1`.
- How: `galAutNegOne_fixes_FglobalPlus` gives reality; `galAutNegOne_zetaSys`/`map_zpow₀` give `σ_{−1}(ξ^m) = ξ^{−m}`, so `ξ^{−m} = ξ^m`; lift to units, derive `ξ^{2m} = 1`, conclude via `zpow_eq_one_of_two_mul` with `orderOf_zetaSysUnit`.
- Hypotheses: `p ≠ 2`; `n ≥ 1`; integer `m`; `ξ^m ∈ F_n⁺`.
- Uses from project: [zetaSysUnit, FglobalPlus, K, Fglobal_le_K, FglobalPlus_le_Fglobal, galAutNegOne_fixes_FglobalPlus, galAut, zetaSys, zetaSys_mem_K, zetaSysUnit_zpow_val, galAutNegOne_zetaSys, zpow_eq_one_of_two_mul, orderOf_zetaSysUnit]
- Used by: cycloUnitsPlus_eq_closure_gammas
- Visibility: private
- Lines: 435–470 (proof 30 lines)
- Notes: long(30-50)

### theorem norm_zetaSys_pow_sub_one_lt
- Type: `private theorem norm_zetaSys_pow_sub_one_lt {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : ‖zetaSys p n ^ k - 1‖ < 1`
- What: `‖ξ^k − 1‖ < 1` for every `k` (a conjugate uniformiser, dominated by `‖π_n‖ < 1`).
- How: Bound `‖ξ^k − 1‖ ≤ ‖ξ − 1‖` via `geom_sum_mul` + `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` and `nlinarith`; then `‖ξ−1‖ < 1` from `norm_pi_lt_one` (rewriting `pi`).
- Hypotheses: `n ≥ 1`; exponent `k`.
- Uses from project: [zetaSys, norm_zetaSys_eq_one, norm_pi_lt_one, pi]
- Used by: valHom_deltaUnit_ne_one, norm_zhp_sub_one_lt
- Visibility: private
- Lines: 472–487 (proof 13 lines)
- Notes: none

### theorem zetaSys_pow_isPrimitiveRoot_p
- Type: `private theorem zetaSys_pow_isPrimitiveRoot_p {n : ℕ} (hn : 1 ≤ n) : IsPrimitiveRoot (zetaSys p n ^ (p ^ (n - 1))) p`
- What: `ω = ξ_{p^n}^{p^{n−1}}` is a primitive `p`-th root of unity.
- How: `(zetaSys_primitiveRoot p n).pow` with the divisibility/quotient condition discharged by `← pow_succ`, `congr`, `omega`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [zetaSys, zetaSys_primitiveRoot]
- Used by: zetaSys_pow_mul_sub_one_prod
- Visibility: private
- Lines: 489–495 (proof 4 lines)
- Notes: none

### theorem zetaSys_pow_mul_sub_one_prod
- Type: `private theorem zetaSys_pow_mul_sub_one_prod (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : zetaSys p n ^ (k * p) - 1 = ∏ i ∈ Finset.range p, (zetaSys p n ^ (k + i * p ^ (n - 1)) - 1)`
- What: The `p`-fold reduction identity (RJW TeX 3471): `ξ^{kp}−1 = ∏_{i<p}(ξ^{k+i·p^{n−1}}−1)`.
- How: Factors `X^p − ξ^{kp}` over the `p`-th roots `ω^i` via `X_pow_sub_C_eq_prod`, evaluates at `X=1` (`Polynomial.eval_prod` etc.), uses `Odd.neg_one_pow` for the `(−1)^p = −1` sign, and reassembles the factors via `Finset.prod_mul_distrib`/`prod_const` + `ring`.
- Hypotheses: `p ≠ 2`; `n ≥ 1`; integer `k`.
- Uses from project: [zetaSys, zetaSys_pow_isPrimitiveRoot_p]
- Used by: zetaSys_pow_sub_one_mem_aug
- Visibility: private
- Lines: 497–518 (proof 18 lines)
- Notes: none

### def gammaGenSet
- Type: `private def gammaGenSet (n : ℕ) : Set ℂ_[p]ˣ := {g | ∃ b, ¬ p ∣ b ∧ (g : ℂ_[p]) = gammaUnit p b n} ∪ {g | (g : ℂ_[p]) = -1}`
- What: The target generating set `{γ_{n,b} : (b,p)=1} ∪ {−1}`.
- How: Direct union of two set-builder predicates.
- Hypotheses: Level `n`.
- Uses from project: [gammaUnit]
- Used by: coe_mem_FglobalPlus_of_mem_closure_gammaGenSet, valHom_eq_one_of_mem_closure_gammaGenSet, augGenSet, gammaGenSet_le_aug, zetaSys_pow_sub_one_mem_aug_coprime, mem_aug_normal_form, closure_cycloGenSet_le_aug
- Visibility: private
- Lines: 528–530 (def, 2 lines)
- Notes: none

### theorem coe_mem_FglobalPlus_of_mem_closure_gammaGenSet
- Type: `private theorem coe_mem_FglobalPlus_of_mem_closure_gammaGenSet (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) {u : ℂ_[p]ˣ} (hu : u ∈ Subgroup.closure (gammaGenSet p n)) : (u : ℂ_[p]) ∈ FglobalPlus p n`
- What: Every element of `closure(gammaGenSet)` is real (lies in `F_n⁺`).
- How: `Subgroup.closure_induction`: generators `γ` via `gammaUnit_mem_FglobalPlus`, `−1` via `neg_mem (one_mem)`; `one`/`mul`/`inv` cases close under field operations.
- Hypotheses: `p ≠ 2`; `n ≥ 1`.
- Uses from project: [gammaGenSet, FglobalPlus, gammaUnit_mem_FglobalPlus]
- Used by: cycloUnitsPlus_eq_closure_gammas
- Visibility: private
- Lines: 532–543 (proof 8 lines)
- Notes: none

### theorem valHom_eq_one_of_mem_closure_gammaGenSet
- Type: `private theorem valHom_eq_one_of_mem_closure_gammaGenSet {n : ℕ} (hn : 1 ≤ n) {u : ℂ_[p]ˣ} (hu : u ∈ Subgroup.closure (gammaGenSet p n)) : valHom p u = 1`
- What: `valHom` vanishes on every generator of `gammaGenSet`, hence on the whole closure.
- How: `Subgroup.closure_induction`: `γ_b` has norm 1 (`norm_zhp`, `norm_cycloUnit`) so `valHom_eq_one_of_norm_one`; `−1` has norm 1; `map_one`/`map_mul`/`map_inv` close the steps.
- Hypotheses: `n ≥ 1`.
- Uses from project: [gammaGenSet, valHom, valHom_eq_one_of_norm_one, gammaUnit, norm_zhp, norm_cycloUnit]
- Used by: cycloUnitsPlus_eq_closure_gammas
- Visibility: private
- Lines: 545–558 (proof 10 lines)
- Notes: none

### def deltaUnit
- Type: `private def deltaUnit {n : ℕ} (hn : 1 ≤ n) : ℂ_[p]ˣ := Units.mk0 (zetaSys p n - 1) (…)`
- What: `δ = ξ_{p^n} − 1` packaged as a unit of `ℂ_[p]ˣ` (`n ≥ 1`, so `ξ ≠ 1`).
- How: `Units.mk0` with nonzero witness from `zetaSys_primitiveRoot.ne_one` and `one_lt_pow₀`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [zetaSys, zetaSys_primitiveRoot]
- Used by: deltaUnit_val, valHom_deltaUnit_ne_one, augGenSet, deltaUnit_mem_aug, zetaSys_pow_sub_one_mem_aug_coprime, mem_aug_normal_form, cycloUnitsPlus_eq_closure_gammas
- Visibility: private
- Lines: 567–570 (def, 3 lines)
- Notes: none

### theorem deltaUnit_val
- Type: `private theorem deltaUnit_val {n : ℕ} (hn : 1 ≤ n) : (deltaUnit p hn : ℂ_[p]) = zetaSys p n - 1`
- What: `deltaUnit` coerces to `ξ − 1`.
- How: `Units.val_mk0`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [deltaUnit, zetaSys]
- Used by: valHom_deltaUnit_ne_one, zetaSys_pow_sub_one_mem_aug_coprime
- Visibility: private
- Lines: 572–574 (proof 1 line)
- Notes: none

### theorem valHom_deltaUnit_ne_one
- Type: `private theorem valHom_deltaUnit_ne_one {n : ℕ} (hn : 1 ≤ n) : valHom p (deltaUnit p hn) ≠ 1`
- What: `0 < −log‖δ‖`, i.e. `valHom δ ≠ 1` (the uniformiser has norm < 1).
- How: `‖δ‖ < 1` from `norm_zetaSys_pow_sub_one_lt` (k=1); `Real.log_neg` gives `log‖δ‖ < 0`; if `valHom δ = 1` then `ofAdd_eq_one` forces `−log‖δ‖ = 0`, `linarith` contradiction.
- Hypotheses: `n ≥ 1`.
- Uses from project: [valHom, deltaUnit, deltaUnit_val, zetaSys, norm_zetaSys_pow_sub_one_lt]
- Used by: cycloUnitsPlus_eq_closure_gammas
- Visibility: private
- Lines: 576–587 (proof 9 lines)
- Notes: none

### def augGenSet
- Type: `private def augGenSet {n : ℕ} (hn : 1 ≤ n) : Set ℂ_[p]ˣ := ({zetaSysUnit p n} ∪ {deltaUnit p hn}) ∪ gammaGenSet p n`
- What: The augmented generating set `{ξ} ∪ {δ} ∪ gammaGenSet`.
- How: Direct union of singletons and `gammaGenSet`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [zetaSysUnit, deltaUnit, gammaGenSet]
- Used by: zetaSysUnit_mem_aug, deltaUnit_mem_aug, gammaGenSet_le_aug, zetaSys_pow_sub_one_mem_aug_coprime, zetaSys_pow_sub_one_mem_aug, mem_aug_normal_form, closure_cycloGenSet_le_aug, cycloUnitsPlus_eq_closure_gammas
- Visibility: private
- Lines: 597–599 (def, 1 line)
- Notes: none

### theorem zetaSysUnit_mem_aug
- Type: `private theorem zetaSysUnit_mem_aug {n : ℕ} (hn : 1 ≤ n) : zetaSysUnit p n ∈ Subgroup.closure (augGenSet p hn)`
- What: `ξ ∈ closure(augGenSet)`.
- How: `Subgroup.subset_closure (Or.inl (Or.inl rfl))`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [zetaSysUnit, augGenSet]
- Used by: zetaSys_pow_sub_one_mem_aug_coprime, closure_cycloGenSet_le_aug
- Visibility: private
- Lines: 601–603 (proof 1 line)
- Notes: none

### theorem deltaUnit_mem_aug
- Type: `private theorem deltaUnit_mem_aug {n : ℕ} (hn : 1 ≤ n) : deltaUnit p hn ∈ Subgroup.closure (augGenSet p hn)`
- What: `δ ∈ closure(augGenSet)`.
- How: `Subgroup.subset_closure (Or.inl (Or.inr rfl))`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [deltaUnit, augGenSet]
- Used by: zetaSys_pow_sub_one_mem_aug_coprime
- Visibility: private
- Lines: 605–607 (proof 1 line)
- Notes: none

### theorem gammaGenSet_le_aug
- Type: `private theorem gammaGenSet_le_aug {n : ℕ} (hn : 1 ≤ n) {g : ℂ_[p]ˣ} (hg : g ∈ gammaGenSet p n) : g ∈ Subgroup.closure (augGenSet p hn)`
- What: Every `gammaGenSet` element lies in `closure(augGenSet)`.
- How: `Subgroup.subset_closure (Or.inr hg)`.
- Hypotheses: `n ≥ 1`; `g ∈ gammaGenSet`.
- Uses from project: [gammaGenSet, augGenSet]
- Used by: zetaSys_pow_sub_one_mem_aug_coprime, closure_cycloGenSet_le_aug
- Visibility: private
- Lines: 609–611 (proof 1 line)
- Notes: none

### theorem zetaSys_pow_sub_one_ne_zero
- Type: `private theorem zetaSys_pow_sub_one_ne_zero {n a : ℕ} (ha1 : 1 ≤ a) (ha2 : a < p ^ n) : zetaSys p n ^ a - 1 ≠ 0`
- What: `ξ^a − 1 ≠ 0` for `1 ≤ a < p^n` (since `ξ` has order `p^n`).
- How: `sub_ne_zero_of_ne`; if `ξ^a = 1` then `p^n ∣ a` (`pow_eq_one_iff_dvd`), contradicting `a < p^n` via `Nat.le_of_dvd`/`omega`.
- Hypotheses: `1 ≤ a < p^n`.
- Uses from project: [zetaSys, zetaSys_primitiveRoot]
- Used by: zetaSys_pow_sub_one_mem_aug
- Visibility: private
- Lines: 613–618 (proof 4 lines)
- Notes: none

### theorem zetaSys_pow_sub_one_mem_aug_coprime
- Type: `private theorem zetaSys_pow_sub_one_mem_aug_coprime (_hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) {a : ℕ} (ha : ¬ p ∣ a) (_ha1 : 1 ≤ a) (_ha2 : a < p ^ n) {g : ℂ_[p]ˣ} (hgv : (g : ℂ_[p]) = zetaSys p n ^ a - 1) : g ∈ Subgroup.closure (augGenSet p hn)`
- What: Base case `(a,p)=1`: `ξ^a − 1 = ↑(δ · ξ^{(−halfExp).val} · γ_{n,a})`, so the generator unit lies in `M`.
- How: Builds `γu = Units.mk0(gammaUnit)`; proves the word `g = δ · ξ^{(−halfExp).val} · γu` via `Units.ext` + `field_simp` using `cycloUnit`'s definition and `zhp_neg`; then `mul_mem`/`pow_mem` of the augGenSet memberships.
- Hypotheses: `p ≠ 2` (unused); `n ≥ 1`; `p ∤ a`; `1 ≤ a < p^n` (unused); `g`'s value is `ξ^a−1`.
- Uses from project: [zetaSys, gammaUnit, zhp_ne_zero, cycloUnit_ne_zero, gammaGenSet, deltaUnit, deltaUnit_val, zetaSysUnit, zetaSysUnit_val, halfExp, zhp, zhp_neg, cycloUnit, zetaSys_primitiveRoot, deltaUnit_mem_aug, zetaSysUnit_mem_aug, gammaGenSet_le_aug]
- Used by: zetaSys_pow_sub_one_mem_aug
- Visibility: private
- Lines: 620–644 (proof 23 lines)
- Notes: none

### theorem zetaSys_pow_sub_one_mem_aug
- Type: `private theorem zetaSys_pow_sub_one_mem_aug (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) : ∀ m a : ℕ, padicValNat p a = m → 1 ≤ a → a < p ^ n → ∀ g : ℂ_[p]ˣ, (g : ℂ_[p]) = zetaSys p n ^ a - 1 → g ∈ Subgroup.closure (augGenSet p hn)`
- What: The full `ξ^a − 1` case (RJW TeX 3471–3472): for every `1 ≤ a < p^n` the generator unit lies in `M`.
- How: Strong induction on `m = v_p(a)` (`Nat.strong_induction_on`); base `(a,p)=1` is `zetaSys_pow_sub_one_mem_aug_coprime`; for `p∣a`, sets `k = a/p`, uses `zetaSys_pow_mul_sub_one_prod` to write `ξ^a−1` as a product of factors `ξ^{k+i·p^{n−1}}−1` each with strictly smaller `v_p` (bound proofs via `padicValNat_dvd_iff_le`, `omega`), then `prod_mem` + the IH.
- Hypotheses: `p ≠ 2`; `n ≥ 1`; the full quantified statement.
- Uses from project: [zetaSys, augGenSet, zetaSys_pow_sub_one_ne_zero, zetaSys_pow_mul_sub_one_prod, zetaSys_primitiveRoot, zetaSys_pow_sub_one_mem_aug_coprime]
- Used by: closure_cycloGenSet_le_aug
- Visibility: private
- Lines: 646–717 (proof 64 lines)
- Notes: OVER-50 (needs /decompose-proof)

### theorem mem_aug_normal_form
- Type: `private theorem mem_aug_normal_form {n : ℕ} (hn : 1 ≤ n) {w : ℂ_[p]ˣ} (hw : w ∈ Subgroup.closure (augGenSet p hn)) : ∃ (D E : ℤ) (h : ℂ_[p]ˣ), h ∈ Subgroup.closure (gammaGenSet p n) ∧ w = zetaSysUnit p n ^ D * deltaUnit p hn ^ E * h`
- What: The normal form (RJW TeX 3476): every `w ∈ M` has shape `w = ξ^D · δ^E · h` with `D,E ∈ ℤ` and `h ∈ closure(gammaGenSet)`.
- How: `Subgroup.closure_induction`: generators map to the three base cases; `mul` adds exponents (`zpow_add`, `ac_rfl`); `inv` negates them (`mul_inv`, `zpow_neg`). Commutativity of `ℂ_[p]ˣ` lets `ξ`/`δ`-powers collect.
- Hypotheses: `n ≥ 1`; `w ∈ closure(augGenSet)`.
- Uses from project: [augGenSet, gammaGenSet, zetaSysUnit, deltaUnit]
- Used by: cycloUnitsPlus_eq_closure_gammas
- Visibility: private
- Lines: 719–743 (proof 17 lines)
- Notes: none

### theorem closure_cycloGenSet_le_aug
- Type: `private theorem closure_cycloGenSet_le_aug (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) : Subgroup.closure (cycloGenSet p n) ≤ Subgroup.closure (augGenSet p hn)`
- What: `closure(cycloGenSet) ≤ M`: the three generator types `ξ, −ξ, ξ^a−1` of `𝒟_n` all lie in `M`.
- How: `Subgroup.closure_le` + `rintro` on the three generator cases: `ξ` via `zetaSysUnit_mem_aug`; `−ξ = (−1)·ξ` via `gammaGenSet_le_aug`; `ξ^a−1` via `zetaSys_pow_sub_one_mem_aug`.
- Hypotheses: `p ≠ 2`; `n ≥ 1`.
- Uses from project: [cycloGenSet, augGenSet, zetaSysUnit, zetaSysUnit_val, zetaSysUnit_mem_aug, gammaGenSet_le_aug, zetaSys_pow_sub_one_mem_aug]
- Used by: cycloUnitsPlus_eq_closure_gammas
- Visibility: private
- Lines: 745–765 (proof 17 lines)
- Notes: none

### theorem cycloUnitsPlus_eq_closure_gammas
- Type: `theorem cycloUnitsPlus_eq_closure_gammas (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) : cycloUnitsPlus p n = Subgroup.closure ({g | ∃ b, ¬ p ∣ b ∧ (g : ℂ_[p]) = gammaUnit p b n} ∪ {g | (g : ℂ_[p]) = -1})`
- What: RJW lem:cyc units gen (i) (TeX 3461–3482): `𝒟_n^+` is generated by `−1` and the `γ_{n,a}` with `(a,p)=1`.
- How: `le_antisymm`. `⊆`: extract the normal form `u = ξ^D·δ^E·h` (`mem_aug_normal_form` via `closure_cycloGenSet_le_aug`); kill `E` via `valHom_deltaUnit_ne_one` (a global unit has norm 1, `norm_le_one_of_isIntegral_int`); kill `D` via reality (`zetaSysUnit_zpow_eq_one_of_mem_FglobalPlus`); conclude `u = h`. `⊇`: each generator is in `𝒟_n^+` via `gammaUnit_mem_cycloUnitsPlus`/`neg_one_mem_cycloUnitsPlus`.
- Hypotheses: `p ≠ 2`; `n ≥ 1`.
- Uses from project: [cycloUnitsPlus, gammaUnit, cycloUnits, closure_cycloGenSet_le_aug, augGenSet, mem_aug_normal_form, gammaGenSet, coe_mem_FglobalPlus_of_mem_closure_gammaGenSet, valHom_eq_one_of_mem_closure_gammaGenSet, FglobalPlus, valHom, valHom_eq_one_of_norm_one, norm_le_one_of_isIntegral_int, zetaSysUnit, zetaSysUnit_val, norm_zetaSys_eq_one, valHom_deltaUnit_ne_one, deltaUnit, zetaSysUnit_zpow_eq_one_of_mem_FglobalPlus, gammaUnit_mem_cycloUnitsPlus, neg_one_mem_cycloUnitsPlus]
- Used by: unused in file
- Visibility: public
- Lines: 767–838 (proof 64 lines)
- Notes: OVER-50 (needs /decompose-proof)

### theorem zpPow_zero'
- Type: `private theorem zpPow_zero' {y : ℂ_[p]} (hy : ‖y - 1‖ < 1) : zpPow p y 0 = 1`
- What: `zpPow y 0 = 1` (the `n = 0` natural power).
- How: Rewrites `0` as natural cast, `zpPow_natCast`, `pow_zero`.
- Hypotheses: `‖y−1‖ < 1`.
- Uses from project: [zpPow, zpPow_natCast]
- Used by: zpPow_neg'
- Visibility: private
- Lines: 840–842 (proof 1 line)
- Notes: none

### theorem zpPow_neg'
- Type: `private theorem zpPow_neg' {y : ℂ_[p]} (hy : ‖y - 1‖ < 1) (a : ℤ_[p]) : zpPow p y (-a) = (zpPow p y a)⁻¹`
- What: `zpPow y (−a) = (zpPow y a)⁻¹`.
- How: `eq_inv_of_mul_eq_one_left` using `← zpPow_add`, `neg_add_cancel`, `zpPow_zero'`.
- Hypotheses: `‖y−1‖ < 1`; `a ∈ ℤ_[p]`.
- Uses from project: [zpPow, zpPow_add, zpPow_zero']
- Used by: zpPow_intCast
- Visibility: private
- Lines: 844–847 (proof 1 line)
- Notes: none

### theorem zpPow_intCast
- Type: `private theorem zpPow_intCast {y : ℂ_[p]} (hy : ‖y - 1‖ < 1) (k : ℤ) : zpPow p y ((k : ℤ_[p])) = y ^ k`
- What: `zpPow y (k : ℤ_[p]) = y^k` for integer `k`.
- How: Case-splits `k` into `±m` (`Int.eq_nat_or_neg`); each case via `zpPow_natCast`, `zpPow_neg'`, `zpow_natCast`/`zpow_neg`.
- Hypotheses: `‖y−1‖ < 1`; integer `k`.
- Uses from project: [zpPow, zpPow_natCast, zpPow_neg']
- Used by: closure_zspan_eq_zpspan
- Visibility: private
- Lines: 849–856 (proof 4 lines)
- Notes: none

### theorem closure_zspan_eq_zpspan
- Type: `theorem closure_zspan_eq_zpspan {n : ℕ} (hn : 1 ≤ n) {g : ℂ_[p]ˣ} (hg : g ∈ localUnitsOne p n) (x : ℂ_[p]ˣ) (hx : x ∈ (Subgroup.zpowers g).topologicalClosure) : ∃ a : ℤ_[p], (x : ℂ_[p]) = zpPow p (g : ℂ_[p]) a`
- What: RJW lem:closure (TeX 3503–3505): the p-adic closure of the multiplicative `ℤ`-span `⟨g⟩` is the `ℤ_p`-span (stated for a single generator).
- How: The set `T = {y | ↑y ∈ range(zpPow ↑g)}` is closed (range of `zpPow` is the continuous image of compact `ℤ_p`, via `PadicInt.continuous_addChar_of_value_at_one` and `isCompact_range`) and contains `⟨g⟩_ℤ` (`zpPow_intCast`); so `closure(⟨g⟩) ⊆ T`.
- Hypotheses: `n ≥ 1`; `g ∈ localUnitsOne` (principal); `x` in the topological closure of `zpowers g`.
- Uses from project: [localUnitsOne, mem_localUnitsOne_iff, zpPow, zpPow_intCast]
- Used by: unused in file
- Visibility: public
- Lines: 858–894 (proof 27 lines)
- Notes: none

### theorem norm_zhp_sub_one_lt
- Type: `private theorem norm_zhp_sub_one_lt {n : ℕ} (hn : 1 ≤ n) (c : ZMod (p ^ n)) : ‖zhp p c - 1‖ < 1`
- What: `‖zhp c − 1‖ < 1` (a half-power root of unity is a principal unit).
- How: Unfolds `zhp`, applies `norm_zetaSys_pow_sub_one_lt` at `k = c.val`.
- Hypotheses: `n ≥ 1`; exponent `c`.
- Uses from project: [zhp, norm_zetaSys_pow_sub_one_lt]
- Used by: gammaUnit_congr_natCast
- Visibility: private
- Lines: 896–899 (proof 1 line)
- Notes: none

### theorem norm_cycloUnit_sub_natCast_lt
- Type: `private theorem norm_cycloUnit_sub_natCast_lt {a : ℕ} {n : ℕ} (hn : 1 ≤ n) : ‖cycloUnit p a n - (a : ℂ_[p])‖ < 1`
- What: `‖c_n(a) − a‖ < 1`: `c_n(a) − a = ∑_{i<a}(ξ^i − 1)`, an ultrametric sum of principal terms (unconditional in `a`).
- How: Writes `c_n(a) − a` as the geometric difference sum (`cycloUnit_eq_geomSum`, `Finset.sum_sub_distrib`); `a=0` trivial; else `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` with each term `≤ ‖ξ−1‖ < 1` (via `geom_sum_mul`, `norm_zetaSys_eq_one`, `nlinarith`, `norm_pi_lt_one`).
- Hypotheses: `n ≥ 1`; integer `a`.
- Uses from project: [cycloUnit, zetaSys, cycloUnit_eq_geomSum, pi, norm_pi_lt_one, norm_zetaSys_eq_one, norm_zetaSys_pow_sub_one_lt]
- Used by: gammaUnit_congr_natCast
- Visibility: private
- Lines: 901–925 (proof 21 lines)
- Notes: none

### theorem gammaUnit_congr_natCast
- Type: `theorem gammaUnit_congr_natCast {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) {n : ℕ} (hn : 1 ≤ n) : ‖gammaUnit p a n - (a : ℂ_[p])‖ < 1`
- What: The §11 b2-note resolved (RJW TeX 3567): `γ_{n,a} ≡ a (mod 𝔭_n)`, i.e. `‖γ_{n,a} − a‖ < 1`.
- How: `c_n(a)` has norm 1 (`norm_cycloUnit`); splits `γ − a = (zhp(halfExp)−1)·c_n(a) + (c_n(a)−a)` (`ring`); each term has norm < 1 by `norm_zhp_sub_one_lt` / `norm_cycloUnit_sub_natCast_lt`, combined via `IsUltrametricDist.norm_add_le_max` + `max_lt`.
- Hypotheses: `p ∤ a`; `n ≥ 1`.
- Uses from project: [gammaUnit, cycloUnit, norm_cycloUnit, zhp, halfExp, norm_zhp_sub_one_lt, norm_cycloUnit_sub_natCast_lt]
- Used by: gammaUnit_congr_natCast_tower
- Visibility: public
- Lines: 927–945 (proof 12 lines)
- Notes: none

### theorem gammaUnit_congr_natCast_tower
- Type: `theorem gammaUnit_congr_natCast_tower {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) : ∀ n : ℕ, 1 ≤ n → ‖gammaUnit p a n - (a : ℂ_[p])‖ < 1`
- What: The Teichmüller-correction congruence (RJW LemmaGeneratorCinfty1, TeX 3553–3567): `γ_{n,a} ≡ a (mod 𝔭_n)` at every level `n ≥ 1`.
- How: Pointwise wrapper: `fun _ hn => gammaUnit_congr_natCast p ha hn`.
- Hypotheses: `p ∤ a`.
- Uses from project: [gammaUnit, gammaUnit_congr_natCast]
- Used by: unused in file
- Visibility: public
- Lines: 947–961 (proof 1 line)
- Notes: none

### theorem galNCU_mul
- Type: `theorem galNCU_mul (a : ℤ_[p]ˣ) (u v : NormCompatUnits p) : galNCU p a (u * v) = galNCU p a u * galNCU p a v`
- What: `σ_a` is a group homomorphism of `𝒰_∞`: `σ_a(u·v) = σ_a(u)·σ_a(v)`.
- How: `NormCompatUnits.ext` + levelwise `Units.ext`; reduces to `map_mul` of `galAut p a n`, decomposing the multiplied `K_n`-element subtype via `Subtype.ext`.
- Hypotheses: `a ∈ ℤ_[p]ˣ`; `u, v ∈ NormCompatUnits`.
- Uses from project: [galNCU, NormCompatUnits, galAut, K]
- Used by: galNCU_one (no), galNCU_pow, galNCU_inv
- Visibility: public
- Lines: 975–991 (proof 13 lines)
- Notes: none

### theorem galNCU_one
- Type: `theorem galNCU_one (a : ℤ_[p]ˣ) : galNCU p a (1 : NormCompatUnits p) = 1`
- What: `σ_a(1) = 1`.
- How: `NormCompatUnits.ext` + levelwise `Units.ext`; the level value is `σ_a(⟨1⟩) = σ_a(1) = 1` via `map_one` (subtype `⟨1⟩ = 1` by `Subtype.ext`).
- Hypotheses: `a ∈ ℤ_[p]ˣ`.
- Uses from project: [galNCU, NormCompatUnits, galAut, K]
- Used by: galNCU_pow, galNCU_inv
- Visibility: public
- Lines: 993–1003 (proof 8 lines)
- Notes: none

### theorem galNCU_elems_val
- Type: `theorem galNCU_elems_val (a : ℤ_[p]ˣ) (u : NormCompatUnits p) (n : ℕ) : (((galNCU p a u).elems n : ℂ_[p]ˣ) : ℂ_[p]) = (galAut p a n ⟨(u.elems n : ℂ_[p]), (Subring.mem_inf.1 (u.mem n)).1⟩ : ℂ_[p])`
- What: The level value of `σ_a u`: `(σ_a u)_n = σ_a(⟨u_n,_⟩)` in `ℂ_[p]`.
- How: Definitional (`rfl`).
- Hypotheses: `a ∈ ℤ_[p]ˣ`; `u`; level `n`.
- Uses from project: [galNCU, NormCompatUnits, galAut]
- Used by: galNCU_elems_eq_galAutValU
- Visibility: public
- Lines: 1005–1010 (proof 1 line, `rfl`)
- Notes: none

### theorem galNCU_mem_unitsTower1
- Type: `theorem galNCU_mem_unitsTower1 (a : ℤ_[p]ˣ) {u : NormCompatUnits p} (hu : u ∈ unitsTower1 p) : galNCU p a u ∈ unitsTower1 p`
- What: `σ_a` preserves the principal-unit tower `𝒰_{∞,1}`.
- How: Levelwise: value and inverse-value stay in `O_n` (the `NormCompatUnits` integrality of `σ_a u`); `σ_a` is an isometry fixing 1 (`norm_galAut`, `map_one`, `map_sub`), so `‖σ_a u_n − 1‖ = ‖u_n − 1‖ < 1`; via `mem_localUnitsOne_iff`.
- Hypotheses: `a ∈ ℤ_[p]ˣ`; `u ∈ unitsTower1` (principal).
- Uses from project: [galNCU, NormCompatUnits, unitsTower1, mem_localUnitsOne_iff, K, galAut, mem_localUnits_iff, norm_galAut]
- Used by: galNCU_wGamma_mem_cycloTower1
- Visibility: public
- Lines: 1012–1033 (proof 18 lines)
- Notes: none

### theorem dirac_mul_eq_pushforward
- Type: `theorem dirac_mul_eq_pushforward (a : ℤ_[p]ˣ) (μ : PadicMeasure p ℤ_[p]ˣ) : (PadicMeasure.dirac p a) * μ = PadicMeasure.pushforward p (unitsMulLeftCM p a) μ`
- What: Convolution form of the `Λ(𝒢)`-equivariance of `Col` (RJW cor:G-eq): `dirac a * μ = pushforward (a·) μ`.
- How: `LinearMap.ext`; unfolds `pushforward_apply`, `dirac_apply`, `innerInt_apply`, with the inner-integration `change` and `congr 1`.
- Hypotheses: `a ∈ ℤ_[p]ˣ`; measure `μ`.
- Uses from project: [PadicMeasure.dirac, PadicMeasure.pushforward, unitsMulLeftCM, PadicMeasure.innerInt, PadicMeasure.mulCM₂, PadicMeasure.pushforward_apply, PadicMeasure.dirac_apply, PadicMeasure.innerInt_apply]
- Used by: Col_galNCU_eq_dirac_mul
- Visibility: public
- Lines: 1035–1048 (proof 6 lines)
- Notes: none

### theorem Col_galNCU_eq_dirac_mul
- Type: `theorem Col_galNCU_eq_dirac_mul (a : ℤ_[p]ˣ) (u : NormCompatUnits p) : Col p (galNCU p a u) = (PadicMeasure.dirac p a) * Col p u`
- What: `Col(σ_a u) = [a]·Col u` (RJW cor:G-eq, convolution form).
- How: `Col_galNCU` (pushforward form) then `dirac_mul_eq_pushforward`.
- Hypotheses: `a ∈ ℤ_[p]ˣ`; `u`.
- Uses from project: [Col, galNCU, PadicMeasure.dirac, Col_galNCU, dirac_mul_eq_pushforward]
- Used by: unused in file
- Visibility: public
- Lines: 1050–1057 (proof 1 line)
- Notes: none

### theorem galAut_mem_Fglobal
- Type: `private theorem galAut_mem_Fglobal (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n) {x : ℂ_[p]} (hx : x ∈ Fglobal p n) (hxK : x ∈ K p n) : (galAut p a n ⟨x, hxK⟩ : ℂ_[p]) ∈ Fglobal p n`
- What: `σ_a` preserves `F_n = ℚ(ξ_n)`.
- How: `IntermediateField.adjoin_induction` (same shape as the reality lemma): generator `σ_a ξ_n = ξ_n^t ∈ F_n` (`galAut_zetaSys`, `pow_mem`); `ℚ` fixed (`map_ratCast`); `add`/`inv`/`mul` cases close.
- Hypotheses: `a ∈ ℤ_[p]ˣ`; `n ≥ 1`; `x ∈ F_n` and `x ∈ K_n`.
- Uses from project: [galAut, Fglobal, K, Fglobal_le_K, zetaSys, galAut_zetaSys]
- Used by: galAutValU_mem_cycloUnits
- Visibility: private
- Lines: 1068–1108 (proof 37 lines)
- Notes: long(30-50)

### theorem galAut_isIntegral
- Type: `private theorem galAut_isIntegral (a : ℤ_[p]ˣ) {n : ℕ} {x : ℂ_[p]} (hxK : x ∈ K p n) (hx : IsIntegral ℤ x) : IsIntegral ℤ (galAut p a n ⟨x, hxK⟩ : ℂ_[p])`
- What: `σ_a` preserves `ℤ`-integrality of `K_n`-elements.
- How: Lifts `x` to integrality as a `K_n`-element via `RingHom.IsIntegralElem.map_iff` (injective `K_n ↪ ℂ_p`), then transports through the `ℤ`-algebra ring hom `(K_n).val ∘ σ_a` using `IsIntegral.map_of_comp_eq` (`φ = id_ℤ`).
- Hypotheses: `a ∈ ℤ_[p]ˣ`; `x ∈ K_n` integral over `ℤ`.
- Uses from project: [galAut, K]
- Used by: galAutValU_mem_cycloUnits
- Visibility: private
- Lines: 1110–1131 (proof 16 lines)
- Notes: none

### theorem galAut_zetaSys_pow
- Type: `private theorem galAut_zetaSys_pow (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (hk : zetaSys p n ^ k ∈ K p n) : (galAut p a n ⟨zetaSys p n ^ k, hk⟩ : ℂ_[p]) = zetaSys p n ^ (((unitsToZModPow p n a : (ZMod (p^n))ˣ) : ZMod (p^n)).val * k)`
- What: `σ_a(ξ_n^k) = ξ_n^{t·k}` with `t = (a mod p^n).val`.
- How: Rewrites `⟨ξ^k⟩ = ⟨ξ⟩^k` (`Subtype.ext`), `map_pow`, `galAut_zetaSys`, `← pow_mul`.
- Hypotheses: `a ∈ ℤ_[p]ˣ`; `n ≥ 1`; `ξ^k ∈ K_n`.
- Uses from project: [galAut, zetaSys, zetaSys_mem_K, galAut_zetaSys, PadicMeasure.unitsToZModPow, K]
- Used by: galAutVal_zetaSys_pow, galAut_mem_closure_cycloGenSet
- Visibility: private
- Lines: 1133–1142 (proof 4 lines)
- Notes: none

### theorem neg_one_mem_closure_cycloGenSet
- Type: `private theorem neg_one_mem_closure_cycloGenSet {n : ℕ} (hn : 1 ≤ n) : ∀ x : ℂ_[p]ˣ, (x : ℂ_[p]) = -1 → x ∈ Subgroup.closure (cycloGenSet p n)`
- What: `−1 ∈ closure(cycloGenSet n)`: `−1 = (−ξ_n)·ξ_n⁻¹`, both factors generated.
- How: Builds the units `ξ = mk0(ξ)`, `nξ = mk0(−ξ)`, both in `cycloGenSet`; word `x = nξ·ξ⁻¹` via `Units.ext`/`mul_inv_cancel₀`; `mul_mem`/`inv_mem` of `subset_closure`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [cycloGenSet, zetaSys, zetaSys_primitiveRoot]
- Used by: galAut_mem_closure_cycloGenSet
- Visibility: private
- Lines: 1144–1160 (proof 14 lines)
- Notes: none

### theorem zetaSys_pow_sub_one_mem_closure_cycloGenSet
- Type: `private theorem zetaSys_pow_sub_one_mem_closure_cycloGenSet {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (hk : ¬ p ^ n ∣ k) : ∀ x : ℂ_[p]ˣ, (x : ℂ_[p]) = zetaSys p n ^ k - 1 → x ∈ Subgroup.closure (cycloGenSet p n)`
- What: `ξ_n^k − 1 ∈ closure(cycloGenSet n)` for any `k` with `p^n ∤ k`.
- How: Reduces `k mod p^n` (`zetaSys_pow_eq_pow_of_modEq`, `Nat.mod_modEq`), shows `1 ≤ k%p^n < p^n` and `ξ^{k%p^n}−1 ≠ 0`, exhibits `x ∈ cycloGenSet` via the third disjunct, then `subset_closure`.
- Hypotheses: `n ≥ 1`; `p^n ∤ k`.
- Uses from project: [cycloGenSet, zetaSys, zetaSys_primitiveRoot, zetaSys_pow_eq_pow_of_modEq]
- Used by: galAut_mem_closure_cycloGenSet
- Visibility: private
- Lines: 1162–1183 (proof 16 lines)
- Notes: none

### theorem zetaSys_pow_mem_closure_cycloGenSet
- Type: `private theorem zetaSys_pow_mem_closure_cycloGenSet {n : ℕ} (k : ℕ) : ∃ w : ℂ_[p]ˣ, w ∈ Subgroup.closure (cycloGenSet p n) ∧ (w : ℂ_[p]) = zetaSys p n ^ k`
- What: Any power `ξ_n^k` is the value of an element of `closure(cycloGenSet n)`.
- How: `ξ = mk0(ξ)` is a generator (first disjunct); `ξ^k` is in the closure (`pow_mem`) with value `ξ^k`.
- Hypotheses: Level `n`; exponent `k`.
- Uses from project: [cycloGenSet, zetaSys, zetaSys_primitiveRoot]
- Used by: galAut_mem_closure_cycloGenSet
- Visibility: private
- Lines: 1185–1194 (proof 6 lines)
- Notes: none

### theorem mem_K_of_mem_closure_cycloGenSet
- Type: `private theorem mem_K_of_mem_closure_cycloGenSet {n : ℕ} {v : ℂ_[p]ˣ} (hv : v ∈ Subgroup.closure (cycloGenSet p n)) : (v : ℂ_[p]) ∈ K p n`
- What: Every unit in `closure(cycloGenSet n)` has value in `K_n`.
- How: `Subgroup.closure_induction`: generators `±ξ_n, ξ_n^b−1` lie in `K_n` (`zetaSys_mem_K`, `sub_mem`, `pow_mem`); closed under products/inverses.
- Hypotheses: Level `n`; `v ∈ closure(cycloGenSet)`.
- Uses from project: [cycloGenSet, K, zetaSys_mem_K]
- Used by: galAut_mem_closure_cycloGenSet, galAutValU_mem_cycloUnits, prod_galAutValU_cycloUnit_telescope (no — uses cycloUnit_mem_K)
- Visibility: private
- Lines: 1196–1208 (proof 8 lines)
- Notes: none

### def galAutVal
- Type: `private noncomputable def galAutVal (a : ℤ_[p]ˣ) (n : ℕ) (x : ℂ_[p]) : ℂ_[p] := if h : x ∈ K p n then (galAut p a n ⟨x, h⟩ : ℂ_[p]) else x` (`open scoped Classical`)
- What: The total `σ_a`-on-values map: `galAut a n` on `K_n`, identity elsewhere (decouples the `K_n`-membership proof from the induction variable).
- How: Dependent `if` on `K_n`-membership.
- Hypotheses: `a ∈ ℤ_[p]ˣ`; level `n`; `x ∈ ℂ_[p]`.
- Uses from project: [galAut, K]
- Used by: galAutVal_mem, galAutVal_mul, galAutVal_inv, galAutVal_zetaSys_pow, galAutVal_neg_one, galAutVal_add, galAutVal_cycloUnit, prod_galAutVal_cycloUnit_telescope, galAut_mem_closure_cycloGenSet, galAutValU (val), galAutValU_val_mem
- Visibility: private (scoped Classical)
- Lines: 1210–1215 (def, 2 lines)
- Notes: none

### theorem galAutVal_mem
- Type: `private theorem galAutVal_mem (a : ℤ_[p]ˣ) {n : ℕ} {x : ℂ_[p]} (h : x ∈ K p n) : galAutVal p a n x = (galAut p a n ⟨x, h⟩ : ℂ_[p])`
- What: On `K_n`, `galAutVal` agrees with `galAut`.
- How: `galAutVal`, `dif_pos h`.
- Hypotheses: `x ∈ K_n`.
- Uses from project: [galAutVal, galAut, K]
- Used by: galAutVal_mul, galAutVal_inv, galAutVal_zetaSys_pow, galAutVal_neg_one, galAutVal_add, galAutVal_cycloUnit, galAut_mem_closure_cycloGenSet, galAutValU_val_mem, galAutValU_mem_cycloUnits, galNCU_elems_eq_galAutValU, galAutValU_zero, galNCU_neg_one_involutive, galNCU_neg_one_fixed_mem_unitsTower1Plus
- Visibility: private
- Lines: 1217–1219 (proof 1 line)
- Notes: none

### theorem galAutVal_mul
- Type: `private theorem galAutVal_mul (a : ℤ_[p]ˣ) {n : ℕ} {x y : ℂ_[p]} (hx : x ∈ K p n) (hy : y ∈ K p n) : galAutVal p a n (x * y) = galAutVal p a n x * galAutVal p a n y`
- What: `galAutVal` is multiplicative on `K_n`.
- How: `galAutVal_mem` on all three products; subtype `⟨xy⟩ = ⟨x⟩·⟨y⟩` (`Subtype.ext`), `map_mul`, `IntermediateField.coe_mul`.
- Hypotheses: `x, y ∈ K_n`.
- Uses from project: [galAutVal, galAutVal_mem, K]
- Used by: galAutVal_cycloUnit, galAut_mem_closure_cycloGenSet, galAutValU_mem_cycloUnits (via inv)
- Visibility: private
- Lines: 1221–1226 (proof 4 lines)
- Notes: none

### theorem galAutVal_inv
- Type: `private theorem galAutVal_inv (a : ℤ_[p]ˣ) {n : ℕ} {x : ℂ_[p]} (hx : x ∈ K p n) : galAutVal p a n x⁻¹ = (galAutVal p a n x)⁻¹`
- What: `galAutVal` of an inverse: `σ_a(x⁻¹) = (σ_a x)⁻¹`.
- How: `galAutVal_mem`; subtype `⟨x⁻¹⟩ = ⟨x⟩⁻¹` (`Subtype.ext`/`IntermediateField.coe_inv`), `map_inv₀`.
- Hypotheses: `x ∈ K_n`.
- Uses from project: [galAutVal, galAutVal_mem, K]
- Used by: galAutVal_cycloUnit, galAut_mem_closure_cycloGenSet, galAutValU_mem_cycloUnits
- Visibility: private
- Lines: 1228–1233 (proof 3 lines)
- Notes: none

### theorem galAutVal_zetaSys_pow
- Type: `private theorem galAutVal_zetaSys_pow (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : galAutVal p a n (zetaSys p n ^ k) = zetaSys p n ^ (((unitsToZModPow p n a) : ZMod (p^n)).val * k)`
- What: `galAutVal(ξ_n^k) = ξ_n^{t·k}` with `t = (a mod p^n).val`.
- How: `galAutVal_mem` (using `pow_mem zetaSys_mem_K`), then `galAut_zetaSys_pow`.
- Hypotheses: `a ∈ ℤ_[p]ˣ`; `n ≥ 1`; exponent `k`.
- Uses from project: [galAutVal, galAutVal_mem, zetaSys, zetaSys_mem_K, galAut_zetaSys_pow, PadicMeasure.unitsToZModPow]
- Used by: galAutVal_cycloUnit, galAut_mem_closure_cycloGenSet
- Visibility: private
- Lines: 1235–1240 (proof 1 line)
- Notes: none

### theorem galAutVal_neg_one
- Type: `private theorem galAutVal_neg_one (a : ℤ_[p]ˣ) {n : ℕ} : galAutVal p a n (-1) = -1`
- What: `galAutVal(−1) = −1` (`σ_a` fixes `ℚ`).
- How: `galAutVal_mem` (neg_mem one_mem); subtype `⟨−1⟩ = −1` (`Subtype.ext`), `map_neg`/`map_one`, `IntermediateField.coe_neg`/`coe_one`.
- Hypotheses: `a ∈ ℤ_[p]ˣ`; level `n`.
- Uses from project: [galAutVal, galAutVal_mem, K]
- Used by: galAutVal_cycloUnit, galAut_mem_closure_cycloGenSet
- Visibility: private
- Lines: 1242–1248 (proof 4 lines)
- Notes: none

### theorem galAutVal_add
- Type: `private theorem galAutVal_add (a : ℤ_[p]ˣ) {n : ℕ} {x y : ℂ_[p]} (hx : x ∈ K p n) (hy : y ∈ K p n) : galAutVal p a n (x + y) = galAutVal p a n x + galAutVal p a n y`
- What: `galAutVal` is additive on `K_n`.
- How: `galAutVal_mem` on all three; subtype `⟨x+y⟩ = ⟨x⟩+⟨y⟩` (`Subtype.ext`), `map_add`, `IntermediateField.coe_add`.
- Hypotheses: `x, y ∈ K_n`.
- Uses from project: [galAutVal, galAutVal_mem, K]
- Used by: galAutVal_cycloUnit
- Visibility: private
- Lines: 1250–1255 (proof 4 lines)
- Notes: none

### theorem galAutVal_cycloUnit
- Type: `private theorem galAutVal_cycloUnit (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n) (b : ℕ) : galAutVal p a n (cycloUnit p b n) = (ξ^{t·b} − 1)/(ξ^t − 1)` (with `t = (a mod p^n).val`)
- What: The closed-form `σ_a`-action on the cyclotomic units (RJW §12.4, sub-step of cor:cyc units gen 2): `σ_a(c_n(b)) = (ξ^{t·b}−1)/(ξ^t−1)`.
- How: Unfolds `cycloUnit = (ξ^b−1)/(ξ−1)`, distributes via `galAutVal_mul`/`galAutVal_inv`/`galAutVal_add`, applies `galAutVal_zetaSys_pow` and `galAutVal_neg_one` to numerator/denominator, `ring`.
- Hypotheses: `a ∈ ℤ_[p]ˣ`; `n ≥ 1`; integer `b`.
- Uses from project: [galAutVal, cycloUnit, zetaSys, zetaSys_mem_K, K, galAutVal_mul, galAutVal_inv, galAutVal_add, galAutVal_zetaSys_pow, galAutVal_neg_one, PadicMeasure.unitsToZModPow]
- Used by: prod_galAutVal_cycloUnit_telescope
- Visibility: private
- Lines: 1257–1280 (proof 18 lines)
- Notes: none

### theorem prod_range_div_telescope
- Type: `private theorem prod_range_div_telescope {F : Type*} [Field F] (e : ℕ → F) (he : ∀ i, e i ≠ 0) (r : ℕ) : ∏ i ∈ Finset.range r, (e (i + 1) / e i) = e r / e 0`
- What: A telescoping product over a field: `∏_{i<r} e(i+1)/e(i) = e r / e 0`.
- How: Induction on `r`; `succ` case via `Finset.prod_range_succ`, `div_mul_div_comm`, `mul_div_mul_right`.
- Hypotheses: Field `F`; all `e i ≠ 0`.
- Uses from project: []
- Used by: prod_galAutVal_cycloUnit_telescope
- Visibility: private
- Lines: 1282–1290 (proof 6 lines)
- Notes: none

### def charExp
- Type: `private def charExp (a : ℤ_[p]ˣ) (n i : ℕ) : ℕ := ((unitsToZModPow p n (a ^ i) : (ZMod (p^n))ˣ) : ZMod (p^n)).val`
- What: The `σ_{a^i}`-character exponent `t_i = (a^i mod p^n).val` (a power of `t = (a mod p^n)`).
- How: Direct definition as the `.val` of `unitsToZModPow (a^i)`.
- Hypotheses: `a ∈ ℤ_[p]ˣ`; levels `n, i`.
- Uses from project: [PadicMeasure.unitsToZModPow]
- Used by: charExp_cast, zetaSys_pow_charExp_sub_one_ne_zero, prod_galAutVal_cycloUnit_telescope
- Visibility: private
- Lines: 1292–1295 (def, 1 line)
- Notes: none

### theorem charExp_cast
- Type: `private theorem charExp_cast (a : ℤ_[p]ˣ) {n : ℕ} (i : ℕ) : ((charExp p a n i : ℕ) : ZMod (p ^ n)) = ((unitsToZModPow p n a) : ZMod (p^n)) ^ i`
- What: `(charExp i : ZMod (p^n)) = (a mod p^n)^i`.
- How: `unitsToZModPow` a `MonoidHom`: `ZMod.natCast_val`, `ZMod.cast_id`, `← Units.val_pow_eq_pow_val`, `← map_pow`.
- Hypotheses: `a ∈ ℤ_[p]ˣ`; levels `n, i`.
- Uses from project: [charExp, PadicMeasure.unitsToZModPow]
- Used by: prod_galAutVal_cycloUnit_telescope
- Visibility: private
- Lines: 1297–1301 (proof 1 line)
- Notes: none

### theorem zetaSys_pow_charExp_sub_one_ne_zero
- Type: `private theorem zetaSys_pow_charExp_sub_one_ne_zero (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n) (i : ℕ) : zetaSys p n ^ charExp p a n i - 1 ≠ 0`
- What: `ξ^{charExp(i)} − 1 ≠ 0` (`a^i mod p^n` is a unit, so `≢ 0`).
- How: `sub_ne_zero_of_ne`; if `ξ^{charExp i} = 1` then `(charExp i : ZMod) = 0` (`pow_eq_one_iff_dvd`, `natCast_eq_zero_iff`), contradicting that it is the value of a unit (`unitsToZModPow.ne_zero`).
- Hypotheses: `a ∈ ℤ_[p]ˣ`; `n ≥ 1`; level `i`.
- Uses from project: [zetaSys, charExp, zetaSys_primitiveRoot, PadicMeasure.unitsToZModPow]
- Used by: prod_galAutVal_cycloUnit_telescope
- Visibility: private
- Lines: 1303–1312 (proof 6 lines)
- Notes: none

### theorem prod_galAutVal_cycloUnit_telescope
- Type: `private theorem prod_galAutVal_cycloUnit_telescope (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n) {b : ℕ} (hb : (b : ZMod (p^n)) = (unitsToZModPow p n a)) (r : ℕ) : ∏ i ∈ Finset.range r, galAutVal p (a ^ i) n (cycloUnit p b n) = (zetaSys p n ^ ((b^r).val) - 1) / (zetaSys p n - 1)`
- What: The telescoping generation (RJW cor:cyc units gen 2, sub-step (b)): `∏_{i<r} σ_{a^i}(c_n(b)) = (ξ^{b^r mod p^n}−1)/(ξ−1)`.
- How: Per-factor `σ_{a^i}(c_n(b)) = (ξ^{charExp(i+1)}−1)/(ξ^{charExp i}−1)` (`galAutVal_cycloUnit` + `hb` gives `t_i·b ≡ t_{i+1}` via `zetaSys_pow_eq_pow_of_modEq`/`charExp_cast`); then `prod_range_div_telescope` with `e i = ξ^{charExp i}−1`; finally `ξ^{charExp r} = ξ^{(b^r).val}`, `ξ^{charExp 0} = ξ`.
- Hypotheses: `a ∈ ℤ_[p]ˣ`; `n ≥ 1`; `b ≡ a (mod p^n)`; level `r`.
- Uses from project: [galAutVal, cycloUnit, zetaSys, charExp, charExp_cast, galAutVal_cycloUnit, zetaSys_pow_charExp_sub_one_ne_zero, prod_range_div_telescope, zetaSys_pow_eq_pow_of_modEq, PadicMeasure.unitsToZModPow]
- Used by: prod_galAutValU_cycloUnit_telescope
- Visibility: private
- Lines: 1314–1350 (proof 29 lines)
- Notes: none

### theorem galAut_mem_closure_cycloGenSet
- Type: `private theorem galAut_mem_closure_cycloGenSet (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n) {v : ℂ_[p]ˣ} (hv : v ∈ Subgroup.closure (cycloGenSet p n)) : ∃ w : ℂ_[p]ˣ, w ∈ Subgroup.closure (cycloGenSet p n) ∧ (w : ℂ_[p]) = galAutVal p a n (v : ℂ_[p])`
- What: `σ_a` maps `closure(cycloGenSet n)` into itself.
- How: Auxiliary `ht_dvd` (`t·b ≢ 0 mod p^n` for `1 ≤ b ≤ p^n−1`); `Subgroup.closure_induction`: `σ_a(ξ_n) = ξ_n^t` (`zetaSys_pow_mem_closure_cycloGenSet`), `σ_a(−ξ_n) = −(ξ_n^t)` (`neg_one_mem_closure_cycloGenSet`), `σ_a(ξ_n^b−1) = ξ_n^{tb}−1` (`zetaSys_pow_sub_one_mem_closure_cycloGenSet`, `galAut_zetaSys_pow`); `mul`/`inv` close via `galAutVal_mul`/`galAutVal_inv` (using `mem_K_of_mem_closure_cycloGenSet`).
- Hypotheses: `a ∈ ℤ_[p]ˣ`; `n ≥ 1`; `v ∈ closure(cycloGenSet)`.
- Uses from project: [cycloGenSet, galAutVal, zetaSys, zetaSys_mem_K, zetaSys_primitiveRoot, galAut_zetaSys_pow, galAutVal_zetaSys_pow, galAutVal_neg_one, galAutVal_mul, galAutVal_inv, galAutVal_mem, zetaSys_pow_mem_closure_cycloGenSet, neg_one_mem_closure_cycloGenSet, zetaSys_pow_sub_one_mem_closure_cycloGenSet, mem_K_of_mem_closure_cycloGenSet, PadicMeasure.unitsToZModPow]
- Used by: galAutValU_mem_cycloUnits
- Visibility: private
- Lines: 1352–1433 (proof 76 lines)
- Notes: OVER-50 (needs /decompose-proof)

### def galAutValU
- Type: `noncomputable def galAutValU (a : ℤ_[p]ˣ) (n : ℕ) (v : ℂ_[p]ˣ) : ℂ_[p]ˣ := if h : (v : ℂ_[p]) ∈ K p n then galAutUnit p a v h else v` (`open scoped Classical`)
- What: The units-level total `σ_a` map: `galAutUnit a` on `K_n`-valued units, identity elsewhere (the unit version of `galAutVal`).
- How: Dependent `if` on `K_n`-membership of `(v : ℂ_[p])`.
- Hypotheses: `a ∈ ℤ_[p]ˣ`; level `n`; unit `v`.
- Uses from project: [K, galAutUnit]
- Used by: galAutValU_val_mem, prod_galAutValU_cycloUnit_telescope, galAutValU_mem_cycloUnits, cycloTranslateSubgroup, galNCU_elems_eq_galAutValU, galAutValU_zero, galNCU_neg_one_involutive, galNCU_neg_one_fixed_mem_unitsTower1Plus, galNCU_wGamma_mem_cycloTower1
- Visibility: public (scoped Classical)
- Lines: 1435–1439 (def, 2 lines)
- Notes: none

### theorem galAutValU_val_mem
- Type: `private theorem galAutValU_val_mem (a : ℤ_[p]ˣ) {n : ℕ} {v : ℂ_[p]ˣ} (h : (v : ℂ_[p]) ∈ K p n) : (galAutValU p a n v : ℂ_[p]) = galAutVal p a n (v : ℂ_[p])`
- What: On `K_n`-valued units, `galAutValU`'s value agrees with `galAutVal`.
- How: `galAutValU`, `dif_pos h`, `galAutUnit_val`, `galAutVal_mem`.
- Hypotheses: `(v : ℂ_[p]) ∈ K_n`.
- Uses from project: [galAutValU, galAutVal, K, galAutUnit, galAutVal_mem]
- Used by: prod_galAutValU_cycloUnit_telescope, galAutValU_mem_cycloUnits, galNCU_elems_eq_galAutValU, galAutValU_zero, galNCU_neg_one_involutive, galNCU_neg_one_fixed_mem_unitsTower1Plus
- Visibility: private
- Lines: 1441–1444 (proof 1 line)
- Notes: none

### def cycloUnitU
- Type: `private noncomputable def cycloUnitU {b : ℕ} (hb : ¬ p ∣ b) {n : ℕ} (hn : 1 ≤ n) : ℂ_[p]ˣ := Units.mk0 (cycloUnit p b n) (cycloUnit_ne_zero p hb hn)`
- What: The cyclotomic unit `c_n(b)` packaged as a unit of `ℂ_[p]ˣ` (`n ≥ 1`, `p ∤ b`).
- How: `Units.mk0` with nonzero witness `cycloUnit_ne_zero`.
- Hypotheses: `p ∤ b`; `n ≥ 1`.
- Uses from project: [cycloUnit, cycloUnit_ne_zero]
- Used by: cycloUnitU_val, prod_galAutValU_cycloUnit_telescope, cycloUnit_mem_cycloTranslateSubgroup, cycloUnitU_a0_generates
- Visibility: private
- Lines: 1446–1450 (def, 2 lines)
- Notes: none

### theorem cycloUnitU_val
- Type: `private theorem cycloUnitU_val {b : ℕ} (hb : ¬ p ∣ b) {n : ℕ} (hn : 1 ≤ n) : (cycloUnitU p hb hn : ℂ_[p]) = cycloUnit p b n`
- What: `cycloUnitU` coerces to `c_n(b)`.
- How: `Units.val_mk0`.
- Hypotheses: `p ∤ b`; `n ≥ 1`.
- Uses from project: [cycloUnitU, cycloUnit]
- Used by: prod_galAutValU_cycloUnit_telescope
- Visibility: private
- Lines: 1452–1453 (proof 1 line)
- Notes: none

### theorem prod_galAutValU_cycloUnit_telescope
- Type: `private theorem prod_galAutValU_cycloUnit_telescope (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n) {b : ℕ} (hb0 : ¬ p ∣ b) (hb : (b : ZMod (p^n)) = unitsToZModPow p n a) (r : ℕ) {b' : ℕ} (hb' : ¬ p ∣ b') (hbb' : (b' : ZMod (p^n)) = (b : ZMod (p^n))^r) : ∏ i ∈ Finset.range r, galAutValU p (a ^ i) n (cycloUnitU p hb0 hn) = cycloUnitU p hb' hn`
- What: cor:cyc units gen 2 — the units-level telescoping (RJW TeX 3484–3486): `∏_{i<r} galAutValU(a^i)(c_n(b)) = c_n(b')` for `b' ≡ b^r (mod p^n)`.
- How: `Units.ext` + `cycloUnitU_val`; the unit-product coerces to the value-product (`Units.coe_prod`, `galAutValU_val_mem` using `cycloUnit_mem_K`), then `prod_galAutVal_cycloUnit_telescope`, finally `ξ^{(b^r).val} = ξ^{b'}` via `zetaSys_pow_eq_pow_of_modEq`.
- Hypotheses: `a ∈ ℤ_[p]ˣ`; `n ≥ 1`; `p ∤ b`; `b ≡ a (mod p^n)`; `p ∤ b'`; `b' ≡ b^r (mod p^n)`.
- Uses from project: [galAutValU, cycloUnitU, cycloUnitU_val, cycloUnit, cycloUnit_mem_K, zetaSys, galAutValU_val_mem, prod_galAutVal_cycloUnit_telescope, zetaSys_pow_eq_pow_of_modEq, PadicMeasure.unitsToZModPow]
- Used by: cycloUnit_mem_cycloTranslateSubgroup
- Visibility: private
- Lines: 1455–1481 (proof 14 lines)
- Notes: none

### theorem galAutValU_mem_cycloUnits
- Type: `private theorem galAutValU_mem_cycloUnits (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n) {v : ℂ_[p]ˣ} (hv : v ∈ cycloUnits p n) : galAutValU p a n v ∈ cycloUnits p n`
- What: `galAutValU a` maps `cycloUnits n` into itself.
- How: Unfolds `cycloUnits = closure(cycloGenSet) ⊓ globalUnits` (`Subgroup.mem_inf`); closure preserved by `galAut_mem_closure_cycloGenSet`; `Fglobal` by `galAut_mem_Fglobal`; integrality of value and inverse-value by `galAut_isIntegral`.
- Hypotheses: `a ∈ ℤ_[p]ˣ`; `n ≥ 1`; `v ∈ cycloUnits`.
- Uses from project: [galAutValU, cycloUnits, mem_K_of_mem_closure_cycloGenSet, galAut_mem_closure_cycloGenSet, galAutValU_val_mem, galAutVal_mem, galAut_mem_Fglobal, galAut_isIntegral, galAutVal_inv, K]
- Used by: galNCU_wGamma_mem_cycloTower1
- Visibility: private
- Lines: 1483–1506 (proof 21 lines)
- Notes: none

### def cycloTranslateSubgroup
- Type: `def cycloTranslateSubgroup (n : ℕ) (g : ℂ_[p]ˣ) : Subgroup ℂ_[p]ˣ := Subgroup.closure {h | ∃ c : ℤ_[p]ˣ, h = galAutValU p c n g}`
- What: The `ℤ[𝒢_n]`-translate subgroup of a single cyclotomic generator `g`: the subgroup generated by all Galois translates `{σ_c(g)}`.
- How: `Subgroup.closure` of the translate set.
- Hypotheses: Level `n`; generator `g`.
- Uses from project: [galAutValU]
- Used by: cycloUnit_mem_cycloTranslateSubgroup, cycloUnitU_a0_generates, cycloClosureOnePlus_le_closure_wGammaTranslate
- Visibility: public
- Lines: 1508–1513 (def, 1 line)
- Notes: none

### theorem cycloUnit_mem_cycloTranslateSubgroup
- Type: `theorem cycloUnit_mem_cycloTranslateSubgroup (a : ℤ_[p]ˣ) {n : ℕ} (hn : 1 ≤ n) {b : ℕ} (hb0 : ¬ p ∣ b) (hb : (b : ZMod (p^n)) = unitsToZModPow p n a) {b' : ℕ} (hb' : ¬ p ∣ b') {r : ℕ} (hbb' : (b' : ZMod (p^n)) = (b : ZMod (p^n))^r) : cycloUnitU p hb' hn ∈ cycloTranslateSubgroup p n (cycloUnitU p hb0 hn)`
- What: cor:cyc units gen 2 (RJW TeX 3484–3486): the level-`n` single-generator cyclicity — the single `c_n(b)` `ℤ[𝒢_n]`-generates every cyclotomic unit `c_n(b')`.
- How: Rewrites `c_n(b')` as the telescoping product (`prod_galAutValU_cycloUnit_telescope`), then `prod_mem`, each factor a translate `subset_closure ⟨a^i, rfl⟩`.
- Hypotheses: `a ∈ ℤ_[p]ˣ`; `n ≥ 1`; `p ∤ b`; `b ≡ a (mod p^n)`; `p ∤ b'`; `b' ≡ b^r (mod p^n)`.
- Uses from project: [cycloUnitU, cycloTranslateSubgroup, prod_galAutValU_cycloUnit_telescope, PadicMeasure.unitsToZModPow]
- Used by: cycloUnitU_a0_generates
- Visibility: public
- Lines: 1515–1535 (proof 5 lines)
- Notes: none

### theorem galNCU_elems_eq_galAutValU
- Type: `theorem galNCU_elems_eq_galAutValU (a : ℤ_[p]ˣ) (u : NormCompatUnits p) (n : ℕ) : (galNCU p a u).elems n = galAutValU p a n (u.elems n)`
- What: The level value of `galNCU a u`: `(galNCU a u).elems n = galAutValU a n (u.elems n)`.
- How: `Units.ext`; `galNCU_elems_val`, `galAutValU_val_mem`, `galAutVal_mem` (all on the `K_n`-membership of `u.elems n`).
- Hypotheses: `a ∈ ℤ_[p]ˣ`; `u`; level `n`.
- Uses from project: [galNCU, NormCompatUnits, galAutValU, galNCU_elems_val, galAutValU_val_mem, galAutVal_mem]
- Used by: galNCU_neg_one_involutive, galNCU_neg_one_fixed_mem_unitsTower1Plus, galNCU_wGamma_mem_cycloTower1
- Visibility: public
- Lines: 1537–1543 (proof 3 lines)
- Notes: none

### theorem galNCU_pow
- Type: `private theorem galNCU_pow (a : ℤ_[p]ˣ) (u : NormCompatUnits p) (k : ℕ) : galNCU p a (u ^ k) = (galNCU p a u) ^ k`
- What: `galNCU a` commutes with powers.
- How: Induction on `k`; `zero` via `galNCU_one`, `succ` via `pow_succ` + `galNCU_mul`.
- Hypotheses: `a ∈ ℤ_[p]ˣ`; `u`; exponent `k`.
- Uses from project: [galNCU, NormCompatUnits, galNCU_one, galNCU_mul]
- Used by: galNCU_wGamma_mem_cycloTower1
- Visibility: private
- Lines: 1545–1551 (proof 3 lines)
- Notes: none

### theorem galNCU_inv
- Type: `theorem galNCU_inv (a : ℤ_[p]ˣ) (u : NormCompatUnits p) : galNCU p a u⁻¹ = (galNCU p a u)⁻¹`
- What: `galNCU a` commutes with inverses.
- How: `eq_inv_of_mul_eq_one_left` via `← galNCU_mul`, `inv_mul_cancel`, `galNCU_one`.
- Hypotheses: `a ∈ ℤ_[p]ˣ`; `u`.
- Uses from project: [galNCU, NormCompatUnits, galNCU_mul, galNCU_one]
- Used by: unused in file
- Visibility: public
- Lines: 1553–1557 (proof 1 line)
- Notes: none

### theorem galAutValU_zero
- Type: `private theorem galAutValU_zero (a : ℤ_[p]ˣ) (v : ℂ_[p]ˣ) : galAutValU p a 0 v = v`
- What: At level 0 the Galois action is trivial (`K_0 = ℚ_p`, `σ_a 0 = refl`): `galAutValU a 0 = id`.
- How: Case-split on `(v : ℂ_[p]) ∈ K_0`; in-`K` case uses `galAut p a 0 = AlgEquiv.refl` (via `dif_neg`); else `galAutValU`, `dif_neg`.
- Hypotheses: `a ∈ ℤ_[p]ˣ`; unit `v`.
- Uses from project: [galAutValU, galAutVal_mem, galAut, K, galAutValU_val_mem]
- Used by: galNCU_neg_one_involutive
- Visibility: private
- Lines: 1559–1566 (proof 6 lines)
- Notes: none

### theorem galNCU_neg_one_involutive
- Type: `theorem galNCU_neg_one_involutive (hp2 : p ≠ 2) (u : NormCompatUnits p) : galNCU p (-1) (galNCU p (-1) u) = u`
- What: (H2) `σ_{−1}` is an involution on `𝒰_∞` (complex conjugation has order 2, `p` odd).
- How: `NormCompatUnits.ext` + levelwise `Units.ext` via `galNCU_elems_eq_galAutValU`; level 0 via `galAutValU_zero`; level `≥1` uses `galAut(−1) n` has order 2 (`orderOf_galAut_neg_one`, `pow_orderOf_eq_one`, `sq`), then `← AlgEquiv.mul_apply`, `h2`, `AlgEquiv.one_apply`.
- Hypotheses: `p ≠ 2`; `u`.
- Uses from project: [galNCU, NormCompatUnits, galNCU_elems_eq_galAutValU, galAutValU_zero, K, galAutValU_val_mem, galAutVal_mem, galAut, orderOf_galAut_neg_one]
- Used by: unused in file
- Visibility: public
- Lines: 1568–1587 (proof 16 lines)
- Notes: none

### theorem galNCU_neg_one_fixed_mem_unitsTower1Plus
- Type: `theorem galNCU_neg_one_fixed_mem_unitsTower1Plus (hp2 : p ≠ 2) {w : NormCompatUnits p} (hw : w ∈ unitsTower1 p) (hfix : galNCU p (-1) w = w) : w ∈ unitsTower1Plus p`
- What: (H3) `σ_{−1}`-fixed principal units are totally real: a fixed `w ∈ 𝒰_{∞,1}` lies in `𝒰⁺_{∞,1}`.
- How: Levelwise `mem_localUnitsOnePlus_iff_galAut_fixed`; the fixedness `galAutValU(−1)(w_n) = w_n` is extracted from `hfix` via `galNCU_elems_eq_galAutValU`, then transported to values via `galAutValU_val_mem`/`galAutVal_mem`.
- Hypotheses: `p ≠ 2`; `w ∈ unitsTower1`; `σ_{−1}(w) = w`.
- Uses from project: [galNCU, NormCompatUnits, unitsTower1, unitsTower1Plus, localUnitsOne, K, mem_localUnitsOnePlus_iff_galAut_fixed, galAutValU, galNCU_elems_eq_galAutValU, galAutValU_val_mem, galAutVal_mem]
- Used by: unused in file
- Visibility: public
- Lines: 1589–1601 (proof 11 lines)
- Notes: none

### theorem galNCU_neg_one_mem_cycloTower1
- Type: `theorem galNCU_neg_one_mem_cycloTower1 {u : NormCompatUnits p} (hu : u ∈ cycloTower1 p) : galNCU p (-1) u ∈ cycloTower1 p`
- What: (H1) `σ_{−1}` preserves the cyclotomic tower `𝒞_{∞,1}`.
- How: `sorry`.
- Hypotheses: `u ∈ cycloTower1`.
- Uses from project: [galNCU, NormCompatUnits, cycloTower1]
- Used by: unused in file
- Visibility: public
- Lines: 1603–1609 (proof: `sorry`)
- Notes: sorry

### def a0
- Type: `private def a0 (hp2 : p ≠ 2) : ℕ := (PadicMeasure.exists_nat_topological_generator p hp2).choose`
- What: The canonical integer topological generator `a₀` of `ℤ_p^×` (a primitive root mod `p²`), as a `ℕ`.
- How: `.choose` of `exists_nat_topological_generator`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [PadicMeasure.exists_nat_topological_generator]
- Used by: a0_not_dvd, splitCyclo, Col_wGamma, wGamma_elems_pow_eq_cycloUnit_pow, cycloUnitU_a0_generates
- Visibility: private
- Lines: 1624–1626 (def, 1 line)
- Notes: none

### theorem a0_not_dvd
- Type: `private theorem a0_not_dvd (hp2 : p ≠ 2) : ¬ (p : ℕ) ∣ a0 p hp2`
- What: `p ∤ a₀`.
- How: `.choose_spec.choose_spec.1` of `exists_nat_topological_generator`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [a0, PadicMeasure.exists_nat_topological_generator]
- Used by: splitCyclo, cyclo_eq_split, Col_wGamma, wGamma_pow_eq_cyclo_pow, wGamma_pow_mem_cycloTower1, wGamma_mem_cycloTower1, galNCU_wGamma_mem_cycloTower1, wGamma_elems_pow_eq_cycloUnit_pow, cycloUnitU_a0_generates
- Visibility: private
- Lines: 1628–1629 (proof 1 line)
- Notes: none

### def splitCyclo
- Type: `private def splitCyclo (hp2 : p ≠ 2) : {vw : NormCompatUnits p × NormCompatUnits p // vw.2 ∈ unitsTower1 p ∧ (∀ n, (vw.1.elems n) ^ (p - 1) = 1) ∧ cyclo p (a0_not_dvd p hp2) hp2 = vw.1 * vw.2}`
- What: The Teichmüller split of `cyclo a₀` (RJW §12.1): `cyclo a₀ = v·w` with `v` `(p−1)`-torsion (residue Teichmüller part) and `w` principal.
- How: `choose v w hw hv heq` from `normCompat_eq_teichmuller_mul_principal`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [NormCompatUnits, unitsTower1, cyclo, a0_not_dvd, normCompat_eq_teichmuller_mul_principal]
- Used by: wGamma, wGammaTeich, wGamma_mem_unitsTower1, wGammaTeich_torsion, cyclo_eq_split
- Visibility: private
- Lines: 1631–1639 (def with `by choose`, ~3 lines)
- Notes: none

### def wGamma
- Type: `def wGamma (hp2 : p ≠ 2) : NormCompatUnits p := (splitCyclo p hp2).1.2`
- What: The Teichmüller-corrected cyclotomic generator `wγ(a₀)` (RJW LemmaGeneratorCinfty1, TeX 3553): the principal part of the split, levelwise `ω(b)⁻¹·c_n(a₀)`.
- How: Second component of `splitCyclo`'s witness.
- Hypotheses: `p ≠ 2`.
- Uses from project: [NormCompatUnits, splitCyclo]
- Used by: wGamma_mem_unitsTower1, cyclo_eq_split, Col_wGamma, Col_wGamma_choose, wGamma_pow_eq_cyclo_pow, wGamma_pow_mem_cycloTower1, wGamma_mem_cycloTower1, galNCU_wGamma_mem_cycloTower1, wGamma_elems_pow_eq_cycloUnit_pow, cycloClosureOnePlus_le_closure_wGammaTranslate
- Visibility: public
- Lines: 1641–1644 (def, 1 line)
- Notes: none

### def wGammaTeich
- Type: `private def wGammaTeich (hp2 : p ≠ 2) : NormCompatUnits p := (splitCyclo p hp2).1.1`
- What: The `(p−1)`-torsion (Teichmüller) part `v` of the split, `cyclo a₀ = v·wγ(a₀)`.
- How: First component of `splitCyclo`'s witness.
- Hypotheses: `p ≠ 2`.
- Uses from project: [NormCompatUnits, splitCyclo]
- Used by: wGammaTeich_torsion, cyclo_eq_split, Col_wGamma, wGamma_pow_eq_cyclo_pow
- Visibility: private
- Lines: 1646–1647 (def, 1 line)
- Notes: none

### theorem wGamma_mem_unitsTower1
- Type: `theorem wGamma_mem_unitsTower1 (hp2 : p ≠ 2) : wGamma p hp2 ∈ unitsTower1 p`
- What: `wγ(a₀) ∈ 𝒰_{∞,1}` (principal); the §11 b2-note `w·γ_{n,a₀} ≡ 1 mod 𝔭_n` resolved.
- How: `(splitCyclo p hp2).2.1`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [wGamma, unitsTower1, splitCyclo]
- Used by: wGamma_pow_mem_cycloTower1, wGamma_mem_cycloTower1, galNCU_wGamma_mem_cycloTower1
- Visibility: public
- Lines: 1649–1652 (proof 1 line)
- Notes: none

### theorem wGammaTeich_torsion
- Type: `private theorem wGammaTeich_torsion (hp2 : p ≠ 2) : ∀ n, (wGammaTeich p hp2).elems n ^ (p - 1) = 1`
- What: `v.elems n ^ (p−1) = 1` (the Teichmüller part is `(p−1)`-torsion).
- How: `(splitCyclo p hp2).2.2.1`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [wGammaTeich, splitCyclo]
- Used by: Col_wGamma, wGamma_pow_eq_cyclo_pow
- Visibility: private
- Lines: 1654–1655 (proof 1 line)
- Notes: none

### theorem cyclo_eq_split
- Type: `private theorem cyclo_eq_split (hp2 : p ≠ 2) : cyclo p (a0_not_dvd p hp2) hp2 = wGammaTeich p hp2 * wGamma p hp2`
- What: The split identity `cyclo a₀ = v · wγ(a₀)`.
- How: `(splitCyclo p hp2).2.2.2`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [cyclo, a0_not_dvd, wGammaTeich, wGamma, splitCyclo]
- Used by: Col_wGamma, wGamma_pow_eq_cyclo_pow
- Visibility: private
- Lines: 1657–1659 (proof 1 line)
- Notes: none

### theorem Col_wGamma
- Type: `theorem Col_wGamma (hp2 : p ≠ 2) : Col p (wGamma p hp2) = -PadicMeasure.zetaNum p (a0 p hp2)`
- What: `Col(wγ(a₀)) = −zetaNum a₀`: the Teichmüller part is killed by `Col`, so `Col(wγ) = Col(cyclo a₀) = −zetaNum a₀`.
- How: `Col_eq_zero_of_torsion` (torsion part) + `Col_add` on the split + `Col_cyclo`, then `zero_add`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [Col, wGamma, PadicMeasure.zetaNum, a0, wGammaTeich, Col_eq_zero_of_torsion, wGammaTeich_torsion, cyclo, a0_not_dvd, cyclo_eq_split, Col_add, Col_cyclo]
- Used by: Col_wGamma_choose
- Visibility: public
- Lines: 1661–1673 (proof 7 lines)
- Notes: none

### theorem Col_wGamma_choose
- Type: `theorem Col_wGamma_choose (hp2 : p ≠ 2) : Col p (wGamma p hp2) = -PadicMeasure.zetaNum p (PadicMeasure.exists_nat_topological_generator p hp2).choose`
- What: `Col(wγ(a₀)) = −zetaNum a₀` with `a₀` named as the canonical `.choose` (the form used downstream).
- How: `a0 p hp2` is by definition that `.choose`, so this is `Col_wGamma`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [Col, wGamma, PadicMeasure.zetaNum, PadicMeasure.exists_nat_topological_generator, Col_wGamma]
- Used by: unused in file
- Visibility: public
- Lines: 1675–1681 (proof 1 line)
- Notes: none

### theorem elems_pow'
- Type: `private theorem elems_pow' (u : NormCompatUnits p) (k n : ℕ) : (u ^ k).elems n = (u.elems n) ^ k`
- What: The level units of a power: `(uᵏ).elems n = (u.elems n)ᵏ`.
- How: Induction on `k`; `zero`/`succ` via `pow_zero`/`pow_succ` and `rfl`.
- Hypotheses: `u`; exponents `k, n`.
- Uses from project: [NormCompatUnits]
- Used by: wGamma_pow_eq_cyclo_pow, wGamma_pow_mem_cycloTower1, wGamma_mem_cycloTower1, galNCU_wGamma_mem_cycloTower1, wGamma_elems_pow_eq_cycloUnit_pow
- Visibility: private
- Lines: 1683–1688 (proof 3 lines)
- Notes: none

### theorem wGamma_pow_eq_cyclo_pow
- Type: `private theorem wGamma_pow_eq_cyclo_pow (hp2 : p ≠ 2) : wGamma p hp2 ^ (p - 1) = cyclo p (a0_not_dvd p hp2) hp2 ^ (p - 1)`
- What: `wγ(a₀)^{p−1} = (cyclo a₀)^{p−1}` (the Teichmüller part `v` is `(p−1)`-torsion).
- How: `cyclo_eq_split`, `mul_pow`; the torsion factor `v^{p−1} = 1` (`elems_pow'`, `wGammaTeich_torsion`), then `one_mul`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [wGamma, cyclo, a0_not_dvd, cyclo_eq_split, wGammaTeich, NormCompatUnits, elems_pow', wGammaTeich_torsion]
- Used by: wGamma_pow_mem_cycloTower1, galNCU_wGamma_mem_cycloTower1, wGamma_elems_pow_eq_cycloUnit_pow
- Visibility: private
- Lines: 1690–1697 (proof 6 lines)
- Notes: none

### theorem wGamma_pow_mem_cycloTower1
- Type: `theorem wGamma_pow_mem_cycloTower1 (hp2 : p ≠ 2) : wGamma p hp2 ^ (p - 1) ∈ cycloTower1 p`
- What: The honest cyclotomic content: `wγ(a₀)^{p−1} ∈ 𝒞_{∞,1}` — it equals `(cyclo a₀)^{p−1}`, cyclotomic and principal.
- How: Levelwise; principal via `pow_mem (wGamma_mem_unitsTower1)`; unfolds `cycloClosureOne`/`cycloClosure` (`Subgroup.mem_inf`); cyclotomic via `wGamma_pow_eq_cyclo_pow`, `elems_pow'`, `pow_mem` of `cyclo_elems_mem_cycloUnits` lifted by `Subgroup.le_topologicalClosure`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [wGamma, cycloTower1, unitsTower1, wGamma_mem_unitsTower1, cycloClosureOne, cycloClosure, mem_localUnitsOne_iff, wGamma_pow_eq_cyclo_pow, elems_pow', cyclo_elems_mem_cycloUnits, a0_not_dvd]
- Used by: wGamma_mem_cycloTower1
- Visibility: public
- Lines: 1699–1715 (proof 12 lines)
- Notes: none

### theorem wGamma_mem_cycloTower1
- Type: `theorem wGamma_mem_cycloTower1 (hp2 : p ≠ 2) : wGamma p hp2 ∈ cycloTower1 p`
- What: `wγ(a₀) ∈ 𝒞_{∞,1}` (RJW LemmaGeneratorCinfty1, TeX 3553); input (I) of `col_image_cycloTower1_eq_zetaIdeal`.
- How: Levelwise; `g = wγ.elems n` is principal (`wGamma_mem_unitsTower1`) and `g^{p−1} ∈ 𝒞_{n,1}` (`wGamma_pow_mem_cycloTower1`, `elems_pow'`); the §13 `(p−1)`-rootedness `mem_cycloClosureOne_of_pow_mem` concludes.
- Hypotheses: `p ≠ 2`.
- Uses from project: [wGamma, cycloTower1, localUnitsOne, wGamma_mem_unitsTower1, cycloClosureOne, elems_pow', wGamma_pow_mem_cycloTower1, mem_cycloClosureOne_of_pow_mem]
- Used by: unused in file
- Visibility: public
- Lines: 1717–1734 (proof 8 lines)
- Notes: none

### theorem galNCU_wGamma_mem_cycloTower1
- Type: `theorem galNCU_wGamma_mem_cycloTower1 (a : ℤ_[p]ˣ) (hp2 : p ≠ 2) : galNCU p a (wGamma p hp2) ∈ cycloTower1 p`
- What: `σ_a` stabilises `𝒞_{∞,1}` on the cyclotomic generator `wγ(a₀)`: `σ_a(wγ(a₀)) ∈ 𝒞_{∞,1}`.
- How: Levelwise; `g = σ_a(wγ).elems n` principal (`galNCU_mem_unitsTower1`); `g^{p−1} = galAutValU a n ((c_n(a₀))^{p−1})` (`galNCU_pow`, `galNCU_elems_eq_galAutValU`, `wGamma_pow_eq_cyclo_pow`, `elems_pow'`); `(c_n(a₀))^{p−1} ∈ 𝒟_n` (`cyclo_elems_mem_cycloUnits`), mapped into `𝒟_n` by `galAutValU_mem_cycloUnits`, lifted by `Subgroup.le_topologicalClosure`; concluded via `mem_cycloClosureOne_of_pow_mem`.
- Hypotheses: `a ∈ ℤ_[p]ˣ`; `p ≠ 2`.
- Uses from project: [galNCU, wGamma, cycloTower1, localUnitsOne, galNCU_mem_unitsTower1, wGamma_mem_unitsTower1, mem_cycloClosureOne_of_pow_mem, elems_pow', galNCU_pow, galNCU_elems_eq_galAutValU, wGamma_pow_eq_cyclo_pow, galAutValU, cyclo, a0_not_dvd, cyclo_elems_mem_cycloUnits, cycloUnits, galAutValU_mem_cycloUnits, cycloClosureOne, cycloClosure, mem_localUnitsOne_iff]
- Used by: unused in file
- Visibility: public
- Lines: 1736–1767 (proof 22 lines)
- Notes: none

### theorem wGamma_elems_pow_eq_cycloUnit_pow
- Type: `theorem wGamma_elems_pow_eq_cycloUnit_pow (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) : ((wGamma p hp2).elems n : ℂ_[p]) ^ (p - 1) = cycloUnit p (a0 p hp2) n ^ (p - 1)`
- What: (A) The `wγ(a₀)`↔`c_n(a₀)` level bridge: the `(p−1)`-power of `wγ(a₀)`'s level-`n` coordinate equals `c_n(a₀)^{p−1}`.
- How: Applies the coercion of `wGamma_pow_eq_cyclo_pow` (`elems_pow'`, `Units.val_pow_eq_pow_val`); identifies `(cyclo a₀).elems n = c_n(a₀)` for `n ≥ 1` via the `dif_pos hn` unfolding of `cyclo` and `Units.val_mk0`.
- Hypotheses: `p ≠ 2`; `n ≥ 1`.
- Uses from project: [wGamma, cycloUnit, a0, NormCompatUnits, elems_pow', wGamma_pow_eq_cyclo_pow, cyclo, a0_not_dvd, cycloUnit_ne_zero]
- Used by: unused in file
- Visibility: public
- Lines: 1779–1795 (proof 10 lines)
- Notes: none

### theorem cycloUnitU_a0_generates
- Type: `theorem cycloUnitU_a0_generates (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) {b' : ℕ} (hb' : ¬ p ∣ b') : cycloUnitU p hb' hn ∈ cycloTranslateSubgroup p n (cycloUnitU p (a0_not_dvd p hp2) hn)`
- What: (B) Level-`n` single-generator cyclicity at `a₀` (RJW cor:cyc units gen 2, specialised to `a₀`): every `c_n(b')` lies in the `𝒢_n`-translate subgroup of `c_n(a₀)`.
- How: The canonical `u₀` (from `exists_nat_topological_generator`) generates `(ℤ/p^nℤ)^×` at every `n` (`hu₀spec.2.2`); `b'` coprime to `p` is a unit mod `p^n` (`ZMod.isUnit_iff_coprime`, `coprime_pow_of_not_dvd`), so its residue is a `ℕ`-power `(a₀)^{r'}` (`mem_powers_iff_mem_zpowers`); concludes via `cycloUnit_mem_cycloTranslateSubgroup`.
- Hypotheses: `p ≠ 2`; `n ≥ 1`; `p ∤ b'`.
- Uses from project: [cycloUnitU, cycloTranslateSubgroup, a0_not_dvd, a0, PadicMeasure.exists_nat_topological_generator, PadicMeasure.unitsToZModPow, PadicMeasure.unitsToZModPow_coe, cycloUnit_mem_cycloTranslateSubgroup]
- Used by: unused in file
- Visibility: public
- Lines: 1797–1838 (proof 32 lines)
- Notes: long(30-50)

### theorem cycloClosureOnePlus_le_closure_wGammaTranslate
- Type: `theorem cycloClosureOnePlus_le_closure_wGammaTranslate (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) : (cycloClosureOnePlus p n : Set ℂ_[p]ˣ) ⊆ _root_.closure (cycloTranslateSubgroup p n ((wGamma p hp2).elems n) : Set ℂ_[p]ˣ)`
- What: T1222 — level-`n` PLUS density (RJW LemmaGeneratorCinfty1(i), TeX 3553–3572): `𝒞⁺_{n,1}` lies in the topological closure of the `𝒢_n`-translate subgroup of `wγ(a₀)` at level `n`.
- How: `sorry`.
- Hypotheses: `p ≠ 2`; `n ≥ 1`.
- Uses from project: [cycloClosureOnePlus, cycloTranslateSubgroup, wGamma, NormCompatUnits]
- Used by: unused in file
- Visibility: public
- Lines: 1840–1850 (proof: `sorry`)
- Notes: sorry

---

## File Summary

**Total declarations: 84** — 18 defs / 64 lemmas+theorems / 0 instances. (Defs: zhp, halfExp, gammaUnit, valHom, zetaSysUnit, gammaGenSet, deltaUnit, augGenSet, galAutVal, galAutValU, cycloUnitU, charExp, cycloTranslateSubgroup, a0, splitCyclo, wGamma, wGammaTeich, prod_range_div_telescope is a theorem — count = 17 defs… recount: zhp, halfExp, gammaUnit, valHom, zetaSysUnit, gammaGenSet, deltaUnit, augGenSet, galAutVal, galAutValU, cycloUnitU, cycloTranslateSubgroup, charExp, a0, splitCyclo, wGamma, wGammaTeich = **17 defs**; remaining **67 lemmas/theorems**; 0 instances/structures/classes.)

**Key API (referenced by ≥3 decls in this file):**
- `zhp` (def) — used by ~11
- `gammaUnit` (def) — used by ~10
- `halfExp` (def) — used by ~8
- `zetaSys` / `zetaSys_primitiveRoot` / `zetaSys_mem_K` (project imports, pervasive)
- `zetaSysUnit` (def) + `zetaSysUnit_val` — used by ~10 / ~5
- `deltaUnit` (def) — used by ~7
- `augGenSet` (def) — used by ~8
- `gammaGenSet` (def) — used by ~7
- `galAutVal` (def) + `galAutVal_mem` — used by ~11 / ~13
- `galAutValU` (def) + `galAutValU_val_mem` — used by ~10 / ~6
- `cycloUnit_eq_geomSum` — used by 3
- `zhp_neg` — used by 3
- `norm_zetaSys_eq_one` — used by 4
- `norm_zetaSys_pow_sub_one_lt` — used by 3
- `cycloUnitU` (def) — used by 4
- `cycloTranslateSubgroup` (def) — used by 3
- `a0` / `a0_not_dvd` — used by ~6 / ~9
- `splitCyclo` (def) — used by 5
- `wGamma` (def) — used by ~10
- `elems_pow'` — used by 5
- `galNCU_elems_eq_galAutValU` — used by 3
- `wGamma_pow_eq_cyclo_pow` — used by 3
- `wGamma_mem_unitsTower1` — used by 3

**Unused in file (terminal/downstream-facing public API):** cycloUnitsPlus_eq_closure_gammas, closure_zspan_eq_zpspan, gammaUnit_congr_natCast_tower, Col_galNCU_eq_dirac_mul, galNCU_inv, galNCU_neg_one_involutive, galNCU_neg_one_fixed_mem_unitsTower1Plus, galNCU_neg_one_mem_cycloTower1, Col_wGamma_choose, wGamma_mem_cycloTower1, galNCU_wGamma_mem_cycloTower1, wGamma_elems_pow_eq_cycloUnit_pow, cycloUnitU_a0_generates, cycloClosureOnePlus_le_closure_wGammaTranslate. (These are the file's exports, consumed by Main.lean / other IwasawaProof modules.)

**Declarations with `sorry` (2):**
- `galNCU_neg_one_mem_cycloTower1` (lines 1603–1609) — (H1) `σ_{−1}` preserves `𝒞_{∞,1}`.
- `cycloClosureOnePlus_le_closure_wGammaTranslate` (lines 1840–1850) — T1222 level-`n` PLUS density.

**`set_option`:** none. **TODO comments:** none (two `sorry`s carry inline mathematical commentary on the deferred §13 module layer).

**Proofs > 50 lines (5) — need /decompose-proof:**
- `gammaUnit_mem_cycloUnitsPlus` (~55 lines, 205–261)
- `zetaSys_pow_sub_one_mem_aug` (~64 lines, 646–717)
- `cycloUnitsPlus_eq_closure_gammas` (~64 lines, 767–838)
- `galAut_mem_closure_cycloGenSet` (~76 lines, 1352–1433)

(Note: `valHom` def carries an inline ~10-line `map_mul'` proof but is a def, not a long theorem.)

**Proofs 30–50 lines (5):**
- `gammaUnit_mem_FglobalPlus` (~32 lines, 169–203)
- `galAutNegOne_fixes_FglobalPlus` (~36 lines, 366–404)
- `zetaSysUnit_zpow_eq_one_of_mem_FglobalPlus` (~30 lines, 435–470)
- `galAut_mem_Fglobal` (~37 lines, 1068–1108)
- `cycloUnitU_a0_generates` (~32 lines, 1797–1838)

# Inventory: PadicLFunctions/Coleman/Tower.lean

The cyclotomic tower over ℚ_p (RJW §9, TeX 2466–2511): fixed compatible system `ξ_{p^n}`, fields `K_n = ℚ_p(μ_{p^n}) ⊂ ℂ_p`, uniformisers `π_n = ξ_{p^n} − 1`, integer rings `O_n`, level norms `N_{n+1,n}`, and the norm-inverse-limit `𝒰_∞`.

`namespace PadicLFunctions.Coleman`; `variable (p : ℕ) [hp : Fact p.Prime]`.

---

### theorem primitiveRoot_pow_succ
- Type: `∀ {n : ℕ} {z : ℂ_[p]}, IsPrimitiveRoot z (p ^ n) → ∃ w : ℂ_[p], IsPrimitiveRoot w (p ^ (n + 1)) ∧ w ^ p = z`
- What: The single tower step — from a primitive `p^n`-th root `z` extract a primitive `p^{n+1}`-th root `w` with `w^p = z`.
- How: Case split on `n`. For `n = 0` use `HasEnoughRootsOfUnity.exists_primitiveRoot` (a genuine primitive `p`-th root in the algebraically closed char-0 `ℂ_p`). For `n ≥ 1` take any `p`-th root via `IsAlgClosed.exists_pow_nat_eq`, then pin `orderOf w = p^{n+1}` by `Nat.dvd_prime_pow` and `IsPrimitiveRoot.pow_ne_one_of_pos_of_lt`.
- Hypotheses: `z` is a primitive `p^n`-th root of unity in `ℂ_p`.
- Uses from project: []
- Used by: exists_compatible_primitiveRoot
- Visibility: private
- Lines: 46–70 (proof ~25 lines)
- Notes: none

### theorem exists_compatible_primitiveRoot
- Type: `∃ ξ : ℕ → ℂ_[p], (∀ n, IsPrimitiveRoot (ξ n) (p ^ n)) ∧ ∀ n, ξ (n + 1) ^ p = ξ n`
- What: R9 — a compatible system of primitive `p^n`-th roots of unity in `ℂ_p` exists (`ξ_0 = 1`, each `ξ_{n+1}^p = ξ_n`).
- How: ℕ-recursion building a dependent chain `{z // IsPrimitiveRoot z (p^n)}` using `primitiveRoot_pow_succ` at each step via `.choose`/`.choose_spec`.
- Hypotheses: none beyond `[Fact p.Prime]`.
- Uses from project: primitiveRoot_pow_succ
- Used by: zetaSys, zetaSys_primitiveRoot, zetaSys_pow_p
- Visibility: public
- Lines: 76–83 (proof ~8 lines)
- Notes: none

### def zetaSys
- Type: `noncomputable def zetaSys : ℕ → ℂ_[p]`
- What: The fixed compatible system `n ↦ ξ_{p^n}` (RJW TeX 2507).
- How: `.choose` of `exists_compatible_primitiveRoot`.
- Hypotheses: none.
- Uses from project: exists_compatible_primitiveRoot
- Used by: zetaSys_primitiveRoot, zetaSys_pow_p, K, pi, zetaSys_mem_K, and pervasively throughout the file
- Visibility: public
- Lines: 86–87 (no proof)
- Notes: none

### theorem zetaSys_primitiveRoot
- Type: `(n : ℕ) : IsPrimitiveRoot (zetaSys p n) (p ^ n)`
- What: `ξ_{p^n}` is a primitive `p^n`-th root of unity.
- How: Projects the first component of `exists_compatible_primitiveRoot.choose_spec`.
- Hypotheses: none.
- Uses from project: exists_compatible_primitiveRoot
- Used by: isCyclotomicExtension_K, finrank_K, norm_root_sub_one_eq, norm_pi_lt_one, pi_ne_zero, finiteDimensional_K, levelNorm_zetaSys_pow_sub_one, zetaSys_extendScalars_generator, exists_pi_repr
- Visibility: public
- Lines: 89–91 (proof 1 line)
- Notes: none

### theorem zetaSys_pow_p
- Type: `(n : ℕ) : zetaSys p (n + 1) ^ p = zetaSys p n`
- What: Compatibility relation `ξ_{p^{n+1}}^p = ξ_{p^n}`.
- How: Projects the second component of `exists_compatible_primitiveRoot.choose_spec`.
- Hypotheses: none.
- Uses from project: exists_compatible_primitiveRoot
- Used by: K_le_succ, levelNorm_zetaSys_pow_sub_one, zetaSys_extendScalars_generator
- Visibility: public
- Lines: 93–94 (proof 1 line)
- Notes: none

### def K
- Type: `noncomputable def K (n : ℕ) : IntermediateField ℚ_[p] ℂ_[p]`
- What: R9 — the local cyclotomic field `K_n = ℚ_p(ξ_{p^n})` realised inside `ℂ_p`.
- How: `IntermediateField.adjoin ℚ_[p] {zetaSys p n}`.
- Hypotheses: none.
- Uses from project: zetaSys
- Used by: pi (no), zetaSys_mem_K, pi_mem_K, K_le_succ, isCyclotomicExtension_K, finrank_K, O, levelNorm, and pervasively
- Visibility: public
- Lines: 98–99 (no proof)
- Notes: none

### def pi
- Type: `noncomputable def pi (n : ℕ) : ℂ_[p]`
- What: R9 — the uniformiser `π_n = ξ_{p^n} − 1` of `K_n`.
- How: `zetaSys p n - 1`.
- Hypotheses: none.
- Uses from project: zetaSys
- Used by: pi_mem_K, norm_root_sub_one_eq, norm_pi_pow_totient, norm_pi_lt_one, pi_ne_zero, pi_mem_O, levelNorm_pi, forall_norm_le_one_of_norm_sum_pi_pow_le_one, exists_pi_repr, pi_pow_mem_span, O_succ_exists_digits
- Visibility: public
- Lines: 102 (no proof)
- Notes: none

### theorem zetaSys_mem_K
- Type: `(n : ℕ) : zetaSys p n ∈ K p n`
- What: `ξ_{p^n}` belongs to `K_n`.
- How: `IntermediateField.subset_adjoin` on the singleton.
- Hypotheses: none.
- Uses from project: zetaSys, K
- Used by: pi_mem_K, K_le_succ, levelNorm_zetaSys_pow_sub_one, zetaSys_extendScalars_generator
- Visibility: public
- Lines: 104–105 (proof 1 line)
- Notes: none

### theorem pi_mem_K
- Type: `(n : ℕ) : pi p n ∈ K p n`
- What: The uniformiser `π_n` belongs to `K_n`.
- How: `sub_mem` of `zetaSys_mem_K` and `one_mem`.
- Hypotheses: none.
- Uses from project: pi, K, zetaSys_mem_K
- Used by: pi_mem_O
- Visibility: public
- Lines: 107–108 (proof 1 line)
- Notes: none

### theorem K_le_succ
- Type: `(n : ℕ) : K p n ≤ K p (n + 1)`
- What: The tower is increasing: `K_n ⊆ K_{n+1}`.
- How: `IntermediateField.adjoin_le_iff`; rewrite `ξ_{p^n} = ξ_{p^{n+1}}^p` (`zetaSys_pow_p`) and use `pow_mem`.
- Hypotheses: none.
- Uses from project: K, zetaSys_pow_p, zetaSys_mem_K
- Used by: finrank_K_succ, levelNorm, levelNorm_apply, levelNorm_mem, levelNorm_mul, levelNorm_one, levelNorm_const_eq_pow, extendScalars_adjoin_eq_top, norm_extendScalars_translated, minpoly_extendScalars_of_pow, levelNorm_zetaSys_pow_sub_one, extendScalars_exists_repr, zetaSys_extendScalars_generator, exists_pi_repr, zetaSys_pow_sum_eq_zero_imp
- Visibility: public
- Lines: 110–113 (proof ~4 lines)
- Notes: none

### theorem cyclotomic_irreducible_Zp
- Type: `(n : ℕ) : Irreducible (cyclotomic (p ^ (n + 1)) ℤ_[p])`
- What: `Φ_{p^{n+1}}` is irreducible over `ℤ_p`.
- How: The translate `Φ_{p^{n+1}}(T+1)` over `ℤ_p` is Eisenstein at `(p)` — transported from ℤ via `cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt`, with leading/lower/constant coefficient checks (constant term `Φ_{p^{n+1}}(1) = p` via `eval_one_cyclotomic_prime_pow`); `IsEisensteinAt.irreducible` gives irreducibility of the composite, and `algEquivAevalXAddC` (the `T ↦ T+1` automorphism) plus `MulEquiv.irreducible_iff` carries it back. Hinges on `PadicInt.irreducible_p`.
- Hypotheses: none beyond `[Fact p.Prime]`.
- Uses from project: []
- Used by: cyclotomic_irreducible_Qp
- Visibility: private
- Lines: 120–182 (proof ~63 lines)
- Notes: OVER-50 (needs /decompose-proof)

### theorem cyclotomic_irreducible_Qp
- Type: `{n : ℕ} (hn : 1 ≤ n) : Irreducible (cyclotomic (p ^ n) ℚ_[p])`
- What: `Φ_{p^n}` is irreducible over `ℚ_p` for `n ≥ 1`.
- How: Reduce `n = m+1`; Gauss's lemma `Monic.irreducible_iff_irreducible_map_fraction_map` transfers `ℤ_p`-irreducibility (`cyclotomic_irreducible_Zp`) to `ℚ_p` (fraction field).
- Hypotheses: `n ≥ 1`.
- Uses from project: cyclotomic_irreducible_Zp
- Used by: isCyclotomicExtension_K, finrank_K, finrank_adjoin_primitiveRoot
- Visibility: public
- Lines: 188–193 (proof ~5 lines)
- Notes: none

### instance isCyclotomicExtension_K
- Type: `{n : ℕ} [NeZero (p ^ n)] : IsCyclotomicExtension {p ^ n} ℚ_[p] (K p n)`
- What: `K_n = ℚ_p(ξ_{p^n})` is a cyclotomic extension of `ℚ_p`.
- How: `ξ_{p^n}` is integral over `ℚ_p` (root of `X^{p^n} − 1`); rewrite the adjoin via `adjoin_simple_toSubalgebra_of_isAlgebraic` and apply `IsPrimitiveRoot.adjoin_isCyclotomicExtension`.
- Hypotheses: `NeZero (p^n)`.
- Uses from project: zetaSys_primitiveRoot, K
- Used by: finrank_K (via IsCyclotomicExtension.finrank), levelNorm_const_eq_pow (finiteDimensional)
- Visibility: public (instance)
- Lines: 198–207 (proof ~10 lines)
- Notes: none

### theorem finrank_K
- Type: `(n : ℕ) : Module.finrank ℚ_[p] (K p n) = Nat.totient (p ^ n)`
- What: R10.2 degree ladder — `[K_n : ℚ_p] = φ(p^n)`.
- How: Case `n = 0`: `K_0 = ⊥`, `finrank_bot`. Case `n ≥ 1`: `IsCyclotomicExtension.finrank` with `cyclotomic_irreducible_Qp`.
- Hypotheses: none.
- Uses from project: zetaSys_primitiveRoot, K, cyclotomic_irreducible_Qp
- Used by: finrank_K_succ, primitiveRoot_notMem_K, norm_pow_totient_mem_zpow
- Visibility: public
- Lines: 212–221 (proof ~10 lines)
- Notes: none

### theorem norm_primitiveRoot_eq_one
- Type: `{n : ℕ} {ξ : ℂ_[p]} (hξ : IsPrimitiveRoot ξ (p ^ n)) : ‖ξ‖ = 1`
- What: A primitive `p^n`-th root of unity in `ℂ_p` has norm 1.
- How: `‖ξ‖^{p^n} = 1` (from `pow_eq_one`); antisymmetry rules out `‖ξ‖ > 1` (`one_lt_pow₀`) and `‖ξ‖ < 1` (`pow_lt_one₀`).
- Hypotheses: `ξ` a primitive `p^n`-th root.
- Uses from project: []
- Used by: norm_sub_one_eq
- Visibility: private
- Lines: 225–231 (proof ~6 lines)
- Notes: none

### theorem norm_pow_sub_one_le
- Type: `{ξ : ℂ_[p]} (hξ1 : ‖ξ‖ = 1) (c : ℕ) : ‖ξ ^ c - 1‖ ≤ ‖ξ - 1‖`
- What: For norm-one `ξ`, `‖ξ^c − 1‖ ≤ ‖ξ − 1‖`.
- How: Factor `ξ^c − 1 = (∑_{i<c} ξ^i)(ξ − 1)` (`geom_sum_mul`); bound the geometric factor by 1 via ultrametric `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`; `nlinarith`.
- Hypotheses: `‖ξ‖ = 1`.
- Uses from project: []
- Used by: norm_sub_one_eq
- Visibility: private
- Lines: 236–243 (proof ~8 lines)
- Notes: none

### theorem norm_sub_one_eq
- Type: `{n : ℕ} {ξ η : ℂ_[p]} (hξ : IsPrimitiveRoot ξ (p ^ n)) (hη : IsPrimitiveRoot η (p ^ n)) : ‖ξ - 1‖ = ‖η - 1‖`
- What: Any two primitive `p^n`-th roots `ξ, η` satisfy `‖ξ − 1‖ = ‖η − 1‖`.
- How: Each is a power of the other (`IsPrimitiveRoot.eq_pow_of_pow_eq_one`, same cyclic group); `norm_pow_sub_one_le` + `norm_primitiveRoot_eq_one` give both inequalities; antisymmetry.
- Hypotheses: `ξ, η` both primitive `p^n`-th roots.
- Uses from project: norm_primitiveRoot_eq_one, norm_pow_sub_one_le
- Used by: norm_root_sub_one_eq
- Visibility: private
- Lines: 249–257 (proof ~9 lines)
- Notes: none

### theorem norm_root_sub_one_eq
- Type: `{n : ℕ} (r : ℂ_[p]) (hr : r ∈ (cyclotomic (p ^ n) ℂ_[p]).roots) : ‖r - 1‖ = ‖pi p n‖`
- What: Every root `r` of `Φ_{p^n}` in `ℂ_p` is a primitive `p^n`-th root, so `‖r − 1‖ = ‖π_n‖`.
- How: `mem_roots` + `isRoot_cyclotomic_iff` makes `r` primitive; `norm_sub_one_eq` against `zetaSys_primitiveRoot`.
- Hypotheses: `r` a root of `cyclotomic (p^n) ℂ_[p]`.
- Uses from project: pi, norm_sub_one_eq, zetaSys_primitiveRoot
- Used by: norm_pi_pow_totient
- Visibility: private
- Lines: 261–267 (proof ~6 lines)
- Notes: none

### theorem norm_pi_pow_totient
- Type: `{n : ℕ} (hn : 1 ≤ n) : ‖pi p n‖ ^ Nat.totient (p ^ n) = (p : ℝ)⁻¹`
- What: R10.2 — the uniformiser norm in rpow-free form: `‖π_n‖^{φ(p^n)} = p⁻¹` for `n ≥ 1`.
- How: Work in `ℂ_p` with `g = Φ_{p^n}(T+1)`, monic and split (`IsAlgClosed.splits`); its roots are `{η − 1}` each of norm `‖π_n‖` (`norm_root_sub_one_eq`, `map_multiset_prod` of `normHom`); constant term `Φ_{p^n}(1) = p` (`eval_one_cyclotomic_prime_pow`); Vieta `coeff_zero_eq_prod_roots_of_monic` gives `p = ±∏ roots`, so `‖π_n‖^{φ(p^n)} = ‖p‖ = p⁻¹` via `Padic.norm_p`. Hinges on `roots_comp_C_mul_X_add_C`, `splits_iff_card_roots`.
- Hypotheses: `n ≥ 1`.
- Uses from project: pi, norm_root_sub_one_eq
- Used by: forall_norm_le_one_of_norm_sum_pi_pow_le_one (via hqpM)
- Visibility: public
- Lines: 278–319 (proof ~42 lines)
- Notes: long(30-50)

### theorem norm_pi_lt_one
- Type: `{n : ℕ} (hn : 1 ≤ n) : ‖pi p n‖ < 1`
- What: The uniformiser has norm `< 1`.
- How: `IsPrimitiveRoot.norm_sub_one_lt` on `zetaSys_primitiveRoot`.
- Hypotheses: `n ≥ 1`.
- Uses from project: pi, zetaSys_primitiveRoot
- Used by: pi_mem_O
- Visibility: public
- Lines: 321–322 (proof 1 line)
- Notes: none

### theorem pi_ne_zero
- Type: `{n : ℕ} (hn : 1 ≤ n) : pi p n ≠ 0`
- What: The uniformiser is nonzero for `n ≥ 1`.
- How: `sub_ne_zero`; `ξ_{p^n} ≠ 1` since order `p^n > 1` (`IsPrimitiveRoot.ne_one`, `one_lt_pow₀`).
- Hypotheses: `n ≥ 1`.
- Uses from project: pi, zetaSys_primitiveRoot
- Used by: unused in file
- Visibility: public
- Lines: 324–326 (proof ~3 lines)
- Notes: none

### def O
- Type: `noncomputable def O (n : ℕ) : Subring ℂ_[p]`
- What: R9 — the integer ring `O_n = O_{K_n}` as the norm-unit-ball of `K_n`.
- How: `(K p n).toSubring ⊓ integerRing ℂ_[p]`.
- Hypotheses: none.
- Uses from project: K
- Used by: pi_mem_O, NormCompatUnits (mem/inv_mem), pi_pow_mem_span, O_succ_exists_digits, and the digit theorems
- Visibility: public
- Lines: 331–332 (no proof)
- Notes: none

### theorem pi_mem_O
- Type: `{n : ℕ} (hn : 1 ≤ n) : pi p n ∈ O p n`
- What: The uniformiser lies in the integer ring `O_n`.
- How: `Subring.mem_inf`; membership in `K_n` (`pi_mem_K`) and norm `≤ 1` (`norm_pi_lt_one`).
- Hypotheses: `n ≥ 1`.
- Uses from project: pi, O, pi_mem_K, norm_pi_lt_one
- Used by: unused in file
- Visibility: public
- Lines: 334–336 (proof ~3 lines)
- Notes: none

### theorem finrank_K_succ
- Type: `{n : ℕ} (hn : 1 ≤ n) : Module.finrank (K p n) (IntermediateField.extendScalars (K_le_succ p n)) = p`
- What: R10.2 tower step — `[K_{n+1} : K_n] = p` for `n ≥ 1`.
- How: Multiplicativity of finrank in the tower `ℚ_p ⊆ K_n ⊆ K_{n+1}` (`Module.finrank_mul_finrank`), with `finrank_K` at both levels and `φ(p^{n+1}) = p·φ(p^n)` (`Nat.totient_prime_pow`); cancel via `Nat.eq_of_mul_eq_mul_left`.
- Hypotheses: `n ≥ 1`.
- Uses from project: K, K_le_succ, finrank_K
- Used by: levelNorm_const_eq_pow, extendScalars_adjoin_eq_top, minpoly_extendScalars_of_pow, forall_norm_le_one_of_norm_sum_pi_pow_le_one (via hM1; actually uses totient identity), extendScalars_exists_repr, zetaSys_pow_sum_eq_zero_imp
- Visibility: public
- Lines: 349–366 (proof ~18 lines)
- Notes: set_option synthInstance.maxHeartbeats 400000

### def levelNorm
- Type: `noncomputable def levelNorm (n : ℕ) : ℂ_[p] → ℂ_[p]` (junk-extended `Algebra.norm (K p n)` of the extendScalars element)
- What: The relative field norm `N_{K_{n+1}/K_n} : K_{n+1} → K_n` viewed as `ℂ_p → ℂ_p`, `0` off `K_{n+1}` (RJW TeX 2503).
- How: `if h : x ∈ K p (n + 1)` then `Algebra.norm (K p n)` of `⟨x,…⟩ : extendScalars (K_le_succ p n)` coerced back into `ℂ_p`, else `0` (Classical decidability).
- Hypotheses: none.
- Uses from project: K, K_le_succ
- Used by: levelNorm_apply, levelNorm_mem, levelNorm_mul, levelNorm_one, levelNorm_const_eq_pow, levelNorm_zetaSys_pow_sub_one, levelNorm_pi, NormCompatUnits.compat
- Visibility: public
- Lines: 374–380 (no proof body; definitional `if`)
- Notes: none

### theorem levelNorm_apply
- Type: `(n : ℕ) {x : ℂ_[p]} (hx : x ∈ K p (n + 1)) : levelNorm p n x = (Algebra.norm (K p n) ⟨x,…⟩ : K p n)`
- What: For `x ∈ K_{n+1}`, `levelNorm` unfolds to the `Algebra.norm` value (no junk branch).
- How: `rw [levelNorm, dif_pos hx]`.
- Hypotheses: `x ∈ K_{n+1}`.
- Uses from project: levelNorm, K, K_le_succ
- Used by: levelNorm_mem, levelNorm_mul, levelNorm_one, levelNorm_const_eq_pow, levelNorm_zetaSys_pow_sub_one
- Visibility: public
- Lines: 384–389 (proof 1 line)
- Notes: none

### theorem levelNorm_mem
- Type: `(n : ℕ) {x : ℂ_[p]} (hx : x ∈ K p (n + 1)) : levelNorm p n x ∈ K p n`
- What: The level norm lands in the base field `K_n`.
- How: `levelNorm_apply`; the `Algebra.norm` value is a `K_n`-subtype element.
- Hypotheses: `x ∈ K_{n+1}`.
- Uses from project: levelNorm, K, levelNorm_apply
- Used by: unused in file
- Visibility: public
- Lines: 393–395 (proof 1 line)
- Notes: none

### theorem levelNorm_mul
- Type: `(n : ℕ) {x y : ℂ_[p]} (hx : x ∈ K p (n + 1)) (hy : y ∈ K p (n + 1)) : levelNorm p n (x * y) = levelNorm p n x * levelNorm p n y`
- What: The level norm is multiplicative on `K_{n+1}`.
- How: `levelNorm_apply` on all three; `Algebra.norm` is a `MonoidHom` (`map_mul`) plus `IntermediateField.coe_mul`/`mul_mem` plumbing.
- Hypotheses: `x, y ∈ K_{n+1}`.
- Uses from project: levelNorm, K, levelNorm_apply
- Used by: NormCompatUnits.mul
- Visibility: public
- Lines: 399–404 (proof ~5 lines)
- Notes: none

### theorem levelNorm_one
- Type: `(n : ℕ) : levelNorm p n 1 = 1`
- What: `N_{n+1,n}(1) = 1`.
- How: `levelNorm_apply` at `1`; the subtype `1` maps to `1`, `map_one`.
- Hypotheses: none.
- Uses from project: levelNorm, K_le_succ, levelNorm_apply
- Used by: NormCompatUnits.one
- Visibility: public
- Lines: 407–411 (proof ~4 lines)
- Notes: none

### theorem levelNorm_const_eq_pow
- Type: `{n : ℕ} (hn : 1 ≤ n) {c : ℂ_[p]} (hc : c ∈ K p n) : levelNorm p n c = c ^ p`
- What: The level norm of a base constant `c ∈ K_n` is `c^p` (norm-compatibility for §12.1/§12.5 Teichmüller systems).
- How: `c ∈ K_{n+1}` via `K_le_succ`; the extendScalars element is `algebraMap (K_n) … ⟨c,hc⟩`; `Algebra.norm_algebraMap` gives `c^{[K_{n+1}:K_n]}` and `finrank_K_succ` gives the exponent `p`. Needs `FiniteDimensional` instances via `IsCyclotomicExtension.finiteDimensional` and `FiniteDimensional.right`.
- Hypotheses: `n ≥ 1`, `c ∈ K_n`.
- Uses from project: levelNorm, K, K_le_succ, levelNorm_apply, finrank_K_succ
- Used by: unused in file
- Visibility: public
- Lines: 425–440 (proof ~16 lines)
- Notes: set_option synthInstance.maxHeartbeats 1000000

### theorem finrank_adjoin_primitiveRoot
- Type: `{n : ℕ} {w : ℂ_[p]} (hw : IsPrimitiveRoot w (p ^ (n + 1))) : Module.finrank ℚ_[p] (IntermediateField.adjoin ℚ_[p] {w}) = Nat.totient (p ^ (n + 1))`
- What: For any primitive `p^{n+1}`-th root `w`, `[ℚ_p(w):ℚ_p] = φ(p^{n+1})`.
- How: `w` integral (root of `X^{p^{n+1}} − 1`); `ℚ_p(w)` is a cyclotomic extension (`adjoin_simple_toSubalgebra_of_isAlgebraic`, `IsPrimitiveRoot.adjoin_isCyclotomicExtension`); `IsCyclotomicExtension.finrank` with `cyclotomic_irreducible_Qp`.
- Hypotheses: `w` a primitive `p^{n+1}`-th root.
- Uses from project: cyclotomic_irreducible_Qp
- Used by: primitiveRoot_notMem_K
- Visibility: private
- Lines: 445–459 (proof ~15 lines)
- Notes: none

### theorem finiteDimensional_K
- Type: `(n : ℕ) : FiniteDimensional ℚ_[p] (K p n)`
- What: `K_n` is finite-dimensional over `ℚ_p`.
- How: Case `n = 0`: `K_0 = ⊥` (adjoin of `1`). Case `n ≥ 1`: `IsCyclotomicExtension.finite_of_singleton`.
- Hypotheses: none.
- Uses from project: zetaSys_primitiveRoot, K
- Used by: primitiveRoot_notMem_K, extendScalars_adjoin_eq_top, norm_pow_totient_mem_zpow
- Visibility: private
- Lines: 463–469 (proof ~7 lines)
- Notes: none

### theorem primitiveRoot_notMem_K
- Type: `{n : ℕ} (hn : 1 ≤ n) {w : ℂ_[p]} (hw : IsPrimitiveRoot w (p ^ (n + 1))) : w ∉ K p n`
- What: A primitive `p^{n+1}`-th root `w` is not in `K_n`.
- How: If it were, `IntermediateField.finrank_le_of_le_right` would give `φ(p^{n+1}) ≤ φ(p^n)` (via `finrank_adjoin_primitiveRoot`, `finrank_K`), contradicting `φ(p^n) < φ(p^{n+1})` (`Nat.totient_prime_pow`, `Nat.pow_lt_pow_right`); `omega`.
- Hypotheses: `n ≥ 1`, `w` primitive `p^{n+1}`-th root.
- Uses from project: finiteDimensional_K, finrank_adjoin_primitiveRoot, finrank_K, K
- Used by: levelNorm_zetaSys_pow_sub_one, zetaSys_extendScalars_generator, exists_pi_repr
- Visibility: public
- Lines: 473–486 (proof ~14 lines)
- Notes: none

### theorem extendScalars_adjoin_eq_top
- Type: `{n : ℕ} (hn : 1 ≤ n) {V : IntermediateField.extendScalars (K_le_succ p n)} (hbot : (V : ℂ_[p]) ∉ K p n) : (K p n)⟮V⟯ = ⊤`
- What: If the `ℂ_p`-value of `V` is not in `K_n`, then `V` generates `K_{n+1}` over `K_n`.
- How: `IntermediateField.eq_of_le_of_finrank_eq`; `[K_{n+1}:K_n] = p` prime (`finrank_K_succ`), so `[K_n(V):K_n]` divides `p` (`finrank_dvd_of_le_right`) and is `1` or `p`; rule out `1` (`finrank_adjoin_simple_eq_one_iff` + `mem_bot` contradicts `hbot`).
- Hypotheses: `n ≥ 1`, `(V : ℂ_p) ∉ K_n`.
- Uses from project: K, K_le_succ, finiteDimensional_K, finrank_K_succ
- Used by: norm_extendScalars_translated, levelNorm_zetaSys_pow_sub_one, zetaSys_extendScalars_generator, exists_pi_repr
- Visibility: public
- Lines: 494–515 (proof ~22 lines)
- Notes: set_option synthInstance.maxHeartbeats 1000000

### theorem norm_extendScalars_translated
- Type: `{n : ℕ} (hn : 1 ≤ n) (hp2 : p ≠ 2) {V : …extendScalars…} {c : K p n} (hbot : (V : ℂ_[p]) ∉ K p n) (hmp : minpoly (K p n) V = (X + 1) ^ p - C c) : Algebra.norm (K p n) V = c - 1`
- What: The norm of a generator `V` with minimal polynomial `(X+1)^p − C c` is `c − 1` (using `p` odd).
- How: `V` integral with `(K_n)⟮V⟯ = ⊤` (`extendScalars_adjoin_eq_top`); `Algebra.norm = (−1)^{deg}·coeff₀(minpoly)` via `Algebra.norm_eq_norm_adjoin` + `PowerBasis.norm_gen_eq_coeff_zero_minpoly`; deg `= p`, constant term `= (X+1)^p − C c` evaluated at 0 `= 1 − c`, and `(−1)^p = −1` (`Nat.Prime.odd_of_ne_two`); `ring`.
- Hypotheses: `n ≥ 1`, `p ≠ 2`, `(V : ℂ_p) ∉ K_n`, `minpoly V = (X+1)^p − C c`.
- Uses from project: K, K_le_succ, extendScalars_adjoin_eq_top
- Used by: levelNorm_zetaSys_pow_sub_one
- Visibility: private
- Lines: 522–563 (proof ~42 lines)
- Notes: long(30-50); set_option synthInstance.maxHeartbeats 1000000

### theorem minpoly_extendScalars_of_pow
- Type: `{n : ℕ} (hn : 1 ≤ n) {W : …extendScalars…} {c : K p n} (hWc : W ^ p = algebraMap … c) (htop : (K p n)⟮W⟯ = ⊤) : minpoly (K p n) W = X ^ p - C c`
- What: The minimal polynomial over `K_n` of an extendScalars element `W` with `W^p = c ∈ K_n` and `K_n(W) = ⊤` is `X^p − C c` (RJW TeX 2685).
- How: `W` is a root of `X^p − C c` (monic), so `minpoly ∣ X^p − C c`; degrees agree (`deg minpoly = [K_{n+1}:K_n] = p` via `IntermediateField.adjoin.finrank` + `finrank_K_succ`, `deg(X^p − C c) = p`); `Polynomial.eq_of_monic_of_dvd_of_natDegree_le`.
- Hypotheses: `n ≥ 1`, `W^p = algebraMap c`, `(K_n)⟮W⟯ = ⊤`.
- Uses from project: K, K_le_succ, finiteDimensional_K, finrank_K_succ
- Used by: levelNorm_zetaSys_pow_sub_one
- Visibility: public
- Lines: 570–589 (proof ~20 lines)
- Notes: set_option synthInstance.maxHeartbeats 1000000

### theorem levelNorm_zetaSys_pow_sub_one
- Type: `{n : ℕ} (hn : 1 ≤ n) (hp2 : p ≠ 2) {b : ℕ} (hb : ¬ p ∣ b) : levelNorm p n (zetaSys p (n + 1) ^ b - 1) = zetaSys p n ^ b - 1`
- What: The norm collapse (RJW TeX 2581–2585): for `b` coprime to `p`, `N_{n+1,n}(ξ^b_{p^{n+1}} − 1) = ξ^b_{p^n} − 1`.
- How: `ξ^b_{p^{n+1}}` is primitive `p^{n+1}`-th (`pow_of_coprime`), with `(ξ^b_{p^{n+1}})^p = ξ^b_{p^n}` (`zetaSys_pow_p`); set `W = ξ^b_{p^{n+1}}`, `V = W − 1`, both ∉ `K_n` (`primitiveRoot_notMem_K`), generating `K_{n+1}` (`extendScalars_adjoin_eq_top`); minpoly of `V` is `(X+1)^p − C c` (`minpoly.sub_algebraMap` + `minpoly_extendScalars_of_pow`); norm `= c − 1` (`norm_extendScalars_translated`).
- Hypotheses: `n ≥ 1`, `p ≠ 2`, `¬ p ∣ b`.
- Uses from project: levelNorm, K, K_le_succ, zetaSys, zetaSys_primitiveRoot, zetaSys_mem_K, zetaSys_pow_p, primitiveRoot_notMem_K, extendScalars_adjoin_eq_top, minpoly_extendScalars_of_pow, norm_extendScalars_translated, levelNorm_apply
- Used by: levelNorm_pi
- Visibility: public
- Lines: 599–637 (proof ~39 lines)
- Notes: long(30-50)

### theorem levelNorm_pi
- Type: `{n : ℕ} (hn : 1 ≤ n) (hp2 : p ≠ 2) : levelNorm p n (pi p (n + 1)) = pi p n`
- What: The uniformiser is norm-compatible: `N_{n+1,n}(π_{n+1}) = π_n`.
- How: `b = 1` case of `levelNorm_zetaSys_pow_sub_one` (`¬ p ∣ 1`); `π = ξ − 1` and `pow_one`.
- Hypotheses: `n ≥ 1`, `p ≠ 2`.
- Uses from project: levelNorm, pi, levelNorm_zetaSys_pow_sub_one
- Used by: unused in file
- Visibility: public
- Lines: 641–644 (proof ~3 lines)
- Notes: none

### structure NormCompatUnits
- Type: `structure NormCompatUnits` (fields `elems : ℕ → ℂ_[p]ˣ`, `mem`, `inv_mem`, `compat`)
- What: `𝒰_∞` — the norm-inverse-limit of local unit groups (RJW TeX 2503): a compatible system of units, each with inverse in its integer ring, matched by level norms for `n ≥ 1`.
- How: Record with four fields; `compat : ∀ n, 1 ≤ n → levelNorm p n (elems (n+1)) = elems n`.
- Hypotheses: none (data).
- Uses from project: O, levelNorm
- Used by: NormCompatUnits.one, NormCompatUnits.mul, the `One`/`Mul` instances
- Visibility: public
- Lines: 650–658 (structure)
- Notes: none

### def NormCompatUnits.one
- Type: `noncomputable def one : NormCompatUnits p` (in `namespace NormCompatUnits`, `variable {p}`)
- What: The trivial compatible system `u_n = 1`.
- How: `elems _ := 1`; memberships `one_mem`; compat from `levelNorm_one`.
- Hypotheses: none.
- Uses from project: O, levelNorm_one
- Used by: instance `One (NormCompatUnits p)`
- Visibility: public
- Lines: 666–670 (proof ~5 lines)
- Notes: none

### instance NormCompatUnits.instOne
- Type: `noncomputable instance : One (NormCompatUnits p)`
- What: `One` instance for `NormCompatUnits`, via `one`.
- How: `⟨one⟩`.
- Hypotheses: none.
- Uses from project: NormCompatUnits.one
- Used by: unused in file
- Visibility: public (instance)
- Lines: 672 (no proof)
- Notes: none

### def NormCompatUnits.mul
- Type: `noncomputable def mul (u v : NormCompatUnits p) : NormCompatUnits p`
- What: Pointwise product of two compatible systems.
- How: `elems n := u.elems n * v.elems n`; memberships via `mul_mem`/`mul_inv_rev`; compat via `levelNorm_mul` (factors in `K_{n+1}` by `Subring.mem_inf`) + `u.compat`, `v.compat`.
- Hypotheses: none.
- Uses from project: O (no), K, levelNorm_mul
- Used by: instance `Mul (NormCompatUnits p)`
- Visibility: public
- Lines: 677–686 (proof ~10 lines)
- Notes: none

### instance NormCompatUnits.instMul
- Type: `noncomputable instance : Mul (NormCompatUnits p)`
- What: `Mul` instance for `NormCompatUnits`, via `mul`.
- How: `⟨mul⟩`.
- Hypotheses: none.
- Uses from project: NormCompatUnits.mul
- Used by: unused in file
- Visibility: public (instance)
- Lines: 688 (no proof)
- Notes: none

### def restrictAbs
- Type: `private noncomputable def restrictAbs (F : IntermediateField ℚ_[p] ℂ_[p]) : AbsoluteValue F ℝ`
- What: The ambient `ℂ_p`-norm restricted to a finite extension `F`, packaged as an `AbsoluteValue F ℝ`.
- How: `toFun x := ‖(x : ℂ_[p])‖`; field laws (`map_mul'`, `nonneg'`, `eq_zero'`, `add_le'`) from `norm_mul`, `norm_nonneg`, `norm_eq_zero`, `norm_add_le`.
- Hypotheses: `F` an intermediate field.
- Uses from project: []
- Used by: norm_eq_spectralNorm
- Visibility: private
- Lines: 694–702 (structure-def, ~9 lines)
- Notes: none

### theorem norm_eq_spectralNorm
- Type: `{F : IntermediateField ℚ_[p] ℂ_[p]} [FiniteDimensional ℚ_[p] F] (x : F) : ‖(x : ℂ_[p])‖ = spectralNorm ℚ_[p] F x`
- What: For `x` in a finite extension `F`, the ambient `ℂ_p`-norm equals the spectral norm.
- How: `spectralNorm_unique_field_norm_ext` — the `ℂ_p`-norm (`restrictAbs`) is a multiplicative `ℚ_p`-algebra norm extending the `p`-adic norm (checked on `algebraMap`), hence equals the spectral norm (`ℚ_p` complete).
- Hypotheses: `F` finite-dimensional over `ℚ_p`.
- Uses from project: restrictAbs
- Used by: norm_pow_totient_mem_zpow
- Visibility: private
- Lines: 708–715 (proof ~8 lines)
- Notes: none

### theorem norm_pow_totient_mem_zpow
- Type: `{n : ℕ} {c : ℂ_[p]} (hc : c ∈ K p n) (hc0 : c ≠ 0) : ∃ k : ℤ, ‖c‖ ^ Nat.totient (p ^ n) = (p : ℝ) ^ k`
- What: Value-group fact for `K_n`: for nonzero `c ∈ K_n`, `‖c‖^{φ(p^n)} ∈ p^ℤ`.
- How: Bridge `‖c‖ = spectralNorm` (`norm_eq_spectralNorm`) and `spectralNorm = ‖coeff₀ minpoly‖^{1/deg}` (`spectralNorm_eq_norm_coeff_zero_rpow`); raise to `deg`, so `‖c‖^{deg} = ‖coeff₀‖`; `deg ∣ φ(p^n)` (`minpoly.degree_dvd` + `finrank_K`); `‖coeff₀‖ = p^j` (`Padic.norm_eq_zpow_neg_valuation`); combine exponents.
- Hypotheses: `c ∈ K_n`, `c ≠ 0`.
- Uses from project: finiteDimensional_K, K, norm_eq_spectralNorm, finrank_K
- Used by: forall_norm_le_one_of_norm_sum_pi_pow_le_one
- Visibility: private
- Lines: 721–749 (proof ~29 lines)
- Notes: none

### theorem forall_norm_le_one_of_norm_sum_pi_pow_le_one
- Type: `{n : ℕ} (hn : 1 ≤ n) (d : Fin p → ℂ_[p]) (hdK : ∀ j, d j ∈ K p n) (hsum : ‖∑ j : Fin p, d j * pi p (n + 1) ^ (j : ℕ)‖ ≤ 1) : ∀ j, ‖d j‖ ≤ 1`
- What: Orthogonality + integrality collapse: if all `d_j ∈ K_n` and `‖∑ d_j π_{n+1}^j‖ ≤ 1`, then every `‖d_j‖ ≤ 1`.
- How: Nonzero terms `d_j π_{n+1}^j` have pairwise distinct norms — their `(pφ(p^n))`-th powers are `p^{k_j p − j}` with `j` pinned mod `p` (`norm_pow_totient_mem_zpow` + `norm_pi_pow_totient`, `zpow_right_injective₀`); ultrametric orthogonality `IsUltrametricDist.norm_sum_eq_sup'_of_pairwise_ne` gives `‖d_j π^j‖ ≤ ‖∑‖ ≤ 1`; `j < p` forces the exponent `k_j ≥ 0`, i.e. `‖d_j‖ ≤ 1`. Hinges on `Finset.sum_filter_of_ne`, `le_of_pow_le_pow_left₀`.
- Hypotheses: `n ≥ 1`, all `d j ∈ K_n`, sum has norm `≤ 1`.
- Uses from project: K, pi, norm_pi_pow_totient, norm_pow_totient_mem_zpow
- Used by: O_succ_exists_digits
- Visibility: private
- Lines: 759–860 (proof ~102 lines)
- Notes: OVER-50 (needs /decompose-proof)

### theorem extendScalars_exists_repr
- Type: `{n : ℕ} (hn : 1 ≤ n) {W : …extendScalars…} (hint : IsIntegral (K p n) W) (htop : (K p n)⟮W⟯ = ⊤) (x : …extendScalars…) : ∃ c : Fin p → K p n, x = ∑ i : Fin p, c i • W ^ (i : ℕ)`
- What: `K_n`-coordinate expansion: for an integral generator `W` of `K_{n+1}/K_n`, every element is `∑_{i<p} c_i W^i` with `c_i ∈ K_n`.
- How: `W` carries a power basis of dim `p` (`IntermediateField.adjoin.powerBasis` + `finrank_K_succ`); map it to `extendScalars` via `equivOfEq htop ≫ topEquiv`; `pb.basis.sum_repr` + `Fintype.sum_equiv (finCongr …)`.
- Hypotheses: `n ≥ 1`, `W` integral over `K_n`, `(K_n)⟮W⟯ = ⊤`.
- Uses from project: K, K_le_succ, finrank_K_succ
- Used by: exists_pi_repr
- Visibility: private
- Lines: 870–893 (proof ~24 lines)
- Notes: set_option synthInstance.maxHeartbeats 1000000; set_option maxHeartbeats 1000000

### theorem zetaSys_extendScalars_generator
- Type: `{n : ℕ} (hn : 1 ≤ n) : ∃ W : …extendScalars…, (W : ℂ_[p]) = zetaSys p (n + 1) ∧ IsIntegral (K p n) W ∧ (K p n)⟮W⟯ = ⊤`
- What: `⟨ξ_{n+1}, _⟩` is an integral generator of `K_{n+1}/K_n`.
- How: Take `W = ⟨ξ_{n+1},…⟩`; integral via `W^p = ξ_n ∈ K_n` (`zetaSys_pow_p`, root of `X^p − C ξ_n`, monic); generates by `extendScalars_adjoin_eq_top` with `ξ_{n+1} ∉ K_n` (`primitiveRoot_notMem_K`).
- Hypotheses: `n ≥ 1`.
- Uses from project: zetaSys, K, K_le_succ, zetaSys_mem_K, zetaSys_pow_p, extendScalars_adjoin_eq_top, primitiveRoot_notMem_K, zetaSys_primitiveRoot
- Used by: exists_pi_repr, zetaSys_pow_sum_eq_zero_imp
- Visibility: private
- Lines: 898–914 (proof ~17 lines)
- Notes: none

### theorem exists_pi_repr
- Type: `{n : ℕ} (hn : 1 ≤ n) {x : ℂ_[p]} (hx : x ∈ K p (n + 1)) : ∃ d : Fin p → ℂ_[p], (∀ k, d k ∈ K p n) ∧ x = ∑ k : Fin p, d k * pi p (n + 1) ^ (k : ℕ)`
- What: Uniformiser-power coordinate expansion: every `x ∈ K_{n+1}` is `∑_{k<p} d_k π_{n+1}^k` with `d_k ∈ K_n`.
- How: Get the generator `W = ξ_{n+1}` (`zetaSys_extendScalars_generator`); translate to `V = W − 1 = π_{n+1}`, which is integral, ∉ `K_n`, generating; expand `x` in `V`-powers (`extendScalars_exists_repr`) and coerce coefficients back to `ℂ_p`.
- Hypotheses: `n ≥ 1`, `x ∈ K_{n+1}`.
- Uses from project: K, K_le_succ, pi, zetaSys_extendScalars_generator, primitiveRoot_notMem_K, zetaSys_primitiveRoot, extendScalars_adjoin_eq_top, extendScalars_exists_repr
- Used by: O_succ_exists_digits
- Visibility: private
- Lines: 919–942 (proof ~24 lines)
- Notes: none

### theorem pi_pow_mem_span
- Type: `{n : ℕ} {k : ℕ} (hk : k < p) : pi p (n + 1) ^ k ∈ Submodule.span (O p n) (Set.range (fun i : Fin p => zetaSys p (n + 1) ^ (i : ℕ)))`
- What: Each uniformiser power `π_{n+1}^k` (`k < p`) lies in the `O_n`-span of `{ξ_{n+1}^i : i < p}`.
- How: Binomial expand `π_{n+1}^k = (ξ_{n+1} − 1)^k` (`add_pow`); coefficients `(−1)^{k−i}·C(k,i)` are integers, hence in `O_n` (`intCast_mem`, `norm_intCast_le_one`); exponents `i ≤ k < p` so each `ξ^i` is in the range; `Submodule.smul_mem`/`subset_span`.
- Hypotheses: `k < p`.
- Uses from project: pi, O, zetaSys, K
- Used by: O_succ_exists_digits
- Visibility: private
- Lines: 948–969 (proof ~22 lines)
- Notes: none

### theorem O_succ_exists_digits
- Type: `{n : ℕ} (hn : 1 ≤ n) {x : ℂ_[p]} (hx : x ∈ O p (n + 1)) : ∃ c : Fin p → ℂ_[p], (∀ i, c i ∈ O p n) ∧ x = ∑ i : Fin p, c i * zetaSys p (n + 1) ^ (i : ℕ)`
- What: R10.2 / RJW TeX 2685 — every `x ∈ O_{n+1}` is `∑_{i<p} c_i ξ_{n+1}^i` with all `c_i ∈ O_n` (existence half of `O_{n+1} = ⊕ O_n·ξ_{n+1}^i`).
- How: Expand `x = ∑ d_k π_{n+1}^k` (`exists_pi_repr`); `‖x‖ ≤ 1` + total ramification force all `d_k ∈ O_n` (`forall_norm_le_one_of_norm_sum_pi_pow_le_one`); each `π_{n+1}^k` is integral in the `ξ`-powers (`pi_pow_mem_span`), so `x` is in the `O_n`-span; extract coordinates via `Submodule.mem_span_range_iff_exists_fun`.
- Hypotheses: `n ≥ 1`, `x ∈ O_{n+1}`.
- Uses from project: O, zetaSys, pi, exists_pi_repr, forall_norm_le_one_of_norm_sum_pi_pow_le_one, pi_pow_mem_span
- Used by: unused in file
- Visibility: public
- Lines: 980–1002 (proof ~23 lines)
- Notes: none

### theorem zetaSys_pow_sum_eq_zero_imp
- Type: `{n : ℕ} (hn : 1 ≤ n) {e : Fin p → ℂ_[p]} (heK : ∀ i, e i ∈ K p n) (he0 : ∑ i : Fin p, e i * zetaSys p (n + 1) ^ (i : ℕ) = 0) : ∀ i, e i = 0`
- What: The `ξ_{n+1}`-powers `{ξ_{n+1}^i : i < p}` are `K_n`-linearly independent in `ℂ_p`.
- How: Lift the combination to `extendScalars` against the generator `W = ξ_{n+1}` (`zetaSys_extendScalars_generator`); `deg minpoly W = p` (`adjoin.finrank` + `finrank_K_succ`); apply `linearIndependent_pow` of the power basis through `Fintype.linearIndependent_iff` + `Fintype.sum_equiv (finCongr …)`.
- Hypotheses: `n ≥ 1`, all `e i ∈ K_n`, the combination is `0`.
- Uses from project: K, K_le_succ, zetaSys, zetaSys_extendScalars_generator, finrank_K_succ
- Used by: O_succ_digits_unique
- Visibility: private
- Lines: 1009–1038 (proof ~30 lines)
- Notes: long(30-50)

### theorem O_succ_digits_unique
- Type: `{n : ℕ} (hn : 1 ≤ n) {c c' : Fin p → ℂ_[p]} (hc : ∀ i, c i ∈ K p n) (hc' : ∀ i, c' i ∈ K p n) (heq : ∑ … c i … = ∑ … c' i …) : c = c'`
- What: R10.2 / RJW TeX 2685 — uniqueness of the `Fin p` `ξ_{n+1}`-power expansion with `K_n`-coefficients (uniqueness half of `O_{n+1} = ⊕ O_n·ξ_{n+1}^i`).
- How: Difference `∑ (c_i − c'_i) ξ^i = 0`; `zetaSys_pow_sum_eq_zero_imp` forces each `c_i − c'_i = 0`; `funext` + `sub_eq_zero`.
- Hypotheses: `n ≥ 1`, all `c i, c' i ∈ K_n`, equal expansions.
- Uses from project: K, zetaSys, zetaSys_pow_sum_eq_zero_imp
- Used by: unused in file
- Visibility: public
- Lines: 1044–1057 (proof ~14 lines)
- Notes: none

---

## File Summary

**Total declarations: 39** — defs: 8 (`zetaSys`, `K`, `pi`, `O`, `levelNorm`, `restrictAbs`, `NormCompatUnits.one`, `NormCompatUnits.mul`) / lemmas+theorems: 27 / instances: 3 (`isCyclotomicExtension_K`, `NormCompatUnits.instOne`, `NormCompatUnits.instMul`) / structures: 1 (`NormCompatUnits`).

**Key API (used by ≥3 in-file):**
- `zetaSys` — the fixed compatible root system (used pervasively).
- `K` — the cyclotomic field tower (used pervasively).
- `pi` — the uniformiser (≥11 in-file consumers).
- `K_le_succ` — tower inclusion (≥15 in-file consumers).
- `zetaSys_primitiveRoot` — primitivity (≥9 consumers).
- `O` — integer ring (≥5 consumers).
- `finrank_K_succ` — degree-`p` tower step (≥6 consumers).
- `finrank_K`, `levelNorm`, `levelNorm_apply`, `finiteDimensional_K`, `extendScalars_adjoin_eq_top`, `primitiveRoot_notMem_K`, `zetaSys_extendScalars_generator` — each used by ≥3.

**Unused in file (terminal/exported API):** `pi_ne_zero`, `pi_mem_O`, `levelNorm_mem`, `levelNorm_const_eq_pow`, `levelNorm_pi`, `NormCompatUnits.instOne`, `NormCompatUnits.instMul`, `O_succ_exists_digits`, `O_succ_digits_unique`. (Also `levelNorm_mul`, `levelNorm_one` are used only inside the `NormCompatUnits` namespace defs.)

**Declarations with sorry: NONE.**

**set_option present (7 decls):**
- `finrank_K_succ` — `synthInstance.maxHeartbeats 400000`
- `levelNorm_const_eq_pow`, `extendScalars_adjoin_eq_top`, `norm_extendScalars_translated`, `minpoly_extendScalars_of_pow`, `zetaSys_pow_sum_eq_zero_imp` — `synthInstance.maxHeartbeats 1000000`
- `extendScalars_exists_repr` — `synthInstance.maxHeartbeats 1000000` AND `maxHeartbeats 1000000`

**Proofs >50 lines (2) — need /decompose-proof:**
1. `cyclotomic_irreducible_Zp` (~63 lines, 120–182)
2. `forall_norm_le_one_of_norm_sum_pi_pow_le_one` (~102 lines, 759–860)

**Proofs 30–50 lines (4):**
1. `norm_pi_pow_totient` (~42 lines, 278–319)
2. `norm_extendScalars_translated` (~42 lines, 522–563)
3. `levelNorm_zetaSys_pow_sub_one` (~39 lines, 599–637)
4. `zetaSys_pow_sum_eq_zero_imp` (~30 lines, 1009–1038)

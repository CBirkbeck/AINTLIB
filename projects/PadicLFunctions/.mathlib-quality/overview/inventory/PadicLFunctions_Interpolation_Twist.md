# Inventory: PadicLFunctions/Interpolation/Twist.lean

Twisting measures by Dirichlet characters (RJW §5.1): the twist `μ_χ`, the
`z`-twist by a continuous additive character, the Mahler transform of the
twist, and the cleared restriction formula. Namespace `PadicLFunctions.MeasureR`.

---

### def twist
- Type: `(g : C(ℤ_[p], integerRing K)) (μ : MeasureR K ℤ_[p]) : MeasureR K ℤ_[p]`
- What: The twist of a measure `μ` by a continuous integer-valued function `g`, defined so that `(twist g μ)(f) = μ(g·f)`; specialised to Dirichlet characters this is RJW's `μ_χ`.
- How: Defined directly as `cmul p K g μ` (multiplication of a measure by a continuous function from the base-change/measure layer).
- Hypotheses: `g` a continuous map `ℤ_[p] → integerRing K`; `μ` a `MeasureR`.
- Uses from project: [`cmul`]
- Used by: `twist_apply`, `twist_powCM`, `twist_res_units`, `mahlerTransform_charTwist`, `res_class_eq_sum_twists`, `mahler_twist_formula`, `mahlerTransform_charTwist_eq_substAffine`
- Visibility: public
- Lines: 38–39 (defn, no proof)
- Notes: none

### lemma twist_apply
- Type: `(g f : C(ℤ_[p], integerRing K)) (μ : MeasureR K ℤ_[p]) : twist p K g μ f = μ (g * f)`
- What: Evaluation/unfolding lemma: the twisted measure applied to `f` equals `μ` applied to the product `g * f`.
- How: `rfl` — definitional, since `twist` is `cmul` and `cmul` evaluates by left-multiplication.
- Hypotheses: `g, f` continuous maps; `μ` a measure. `omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K]`.
- Uses from project: [`twist`]
- Used by: `mahlerTransform_charTwist`, `res_class_eq_sum_twists`, `mahler_twist_formula`
- Visibility: public; `@[simp]`
- Lines: 43–46 (proof 1 line)
- Notes: none

### lemma twist_powCM
- Type: `(g : C(ℤ_[p], integerRing K)) (μ : MeasureR K ℤ_[p]) (k : ℕ) : twist p K g μ (powCM p K k) = μ (g * powCM p K k)`
- What: Twisted moments: the `k`-th moment of `twist g μ` equals `μ` of `g` times the `k`-th power monomial map.
- How: `rfl` — definitional unfolding of `twist`/`cmul` at the monomial `powCM`.
- Hypotheses: `g` continuous; `μ` a measure; `k` a natural number. `omit [CompleteSpace K]`.
- Uses from project: [`twist`, `powCM`]
- Used by: unused in file
- Visibility: public
- Lines: 48–51 (proof 1 line)
- Notes: none

### def charCM
- Type: `(r : integerRing K) (hr : Filter.Tendsto (r ^ ·) Filter.atTop (nhds 0)) : C(ℤ_[p], integerRing K)`
- What: The continuous additive character `κ_r` of `ℤ_[p]` valued in `integerRing K`, sending `1 ↦ 1+r` (mathlib's `addChar_of_value_at_one`), as a continuous map.
- How: Bundles `PadicInt.addChar_of_value_at_one r hr` with its continuity proof `PadicInt.continuous_addChar_of_value_at_one hr` into a `ContinuousMap`.
- Hypotheses: `r` topologically nilpotent (`r^k → 0`).
- Uses from project: []
- Used by: `charCM_natCast`, `mahlerTransform_charTwist`, `res_class_eq_sum_twists`, `mahler_twist_formula`, `mahlerTransform_charTwist_eq_substAffine`
- Visibility: public
- Lines: 55–58 (defn, no proof)
- Notes: none

### lemma charCM_natCast
- Type: `(r : integerRing K) (hr : ...) (k : ℕ) : charCM r hr ((k : ℕ) : ℤ_[p]) = (1 + r) ^ k`
- What: The character `κ_r` evaluated at a natural number `k` (cast into `ℤ_[p]`) equals `(1+r)^k`.
- How: Rewrites `k` as `k • 1`, applies `AddChar.map_nsmul_eq_pow` and the defining value `addChar_of_value_at_one_def`.
- Hypotheses: `r` topologically nilpotent; `k : ℕ`.
- Uses from project: [`charCM`]
- Used by: `mahlerTransform_charTwist`, `res_class_eq_sum_twists`, `mahler_twist_formula`
- Visibility: public; `@[simp]`
- Lines: 62–67 (proof 3 lines)
- Notes: none

### lemma isClopen_toZModPow_fiber
- Type: `(n : ℕ) (b : ZMod (p ^ n)) : IsClopen {x : ℤ_[p] | PadicInt.toZModPow n x = b}`
- What: The fibre of reduction mod `p^n` over a residue `b` is clopen in `ℤ_[p]`.
- How: Direct delegation to `PadicMeasure.isClopen_toZModPow_fiber p n b`.
- Hypotheses: `n : ℕ`, `b : ZMod (p^n)`.
- Uses from project: [`PadicMeasure.isClopen_toZModPow_fiber`]
- Used by: `res_class_eq_sum_twists`
- Visibility: public
- Lines: 72–74 (proof 1 line)
- Notes: none

### theorem twist_res_units
- Type: `{n : ℕ} (hn : 1 ≤ n) (χ : DirichletCharacter (integerRing K) (p ^ n)) (μ : MeasureR K ℤ_[p]) : res p K (PadicMeasure.isClopen_units p) (twist p K χ.toContinuousMapZp μ) = twist p K χ.toContinuousMapZp μ`
- What: Restricting the `χ`-twisted measure to the units `ℤ_[p]^×` does not change it, because `χ` is supported on the units, so `μ_χ` is automatically supported there too (RJW L5.1.3).
- How: Reduces (via `LinearMap.ext`) to a pointwise identity of continuous maps; on units the unit-indicator is `1` so `1·χ·f` matches; off units `χ.toContinuousMapZp` vanishes via `DirichletCharacter.toContinuousMapZp_eq_zero` (needs `hn`), killing both sides.
- Hypotheses: `n ≥ 1`; `χ` a Dirichlet character mod `p^n` valued in `integerRing K`; `μ` a measure. `omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K]`.
- Uses from project: [`res`, `twist`, `PadicMeasure.isClopen_units`, `charFnCM`, `DirichletCharacter.toContinuousMapZp`, `DirichletCharacter.toContinuousMapZp_eq_zero`]
- Used by: unused in file
- Visibility: public
- Lines: 82–95 (proof ~10 lines)
- Notes: none

### theorem mahlerTransform_charTwist
- Type: `(r : integerRing K) (hr : ...) (μ : MeasureR K ℤ_[p]) (n : ℕ) : PowerSeries.coeff n (mahlerTransform p K (twist p K (charCM r hr) μ)) = ∑' m, PowerSeries.coeff n (((1 + X) * C (1 + r) - 1) ^ m) * μ (mahlerCM p K m)`
- What: Coefficientwise `z`-twist transform formula: the `n`-th Mahler coefficient of the transform of `twist κ_r μ` is the tsum over `m` of the `n`-th coefficient of `((1+T)(1+r)−1)^m` times the `m`-th Mahler moment of `μ` — i.e. `𝓐(κ_r·μ)(T) = 𝓐_μ((1+T)(1+r)−1)` (RJW §3.5, TeX 1084–1090).
- How: Rewrites via `coeff_mahlerTransform`, `twist_apply`, `apply_eq_tsum`; reduces summand-by-summand to a finite-sum identity, expanding `((1+X)C(1+r)−1)^m` by `Commute.add_pow`, identifying `coeff n ((1+X)^i)` with the binomial `i.choose n` via `Polynomial.coeff_one_add_X_pow`, then matching the forward-difference expansion `fwdDiff_iter_eq_sum_shift` of the Mahler moment with `charCM_natCast`/`mahlerCM_apply`; finishes with `push_cast; ring`.
- Hypotheses: `r` topologically nilpotent; `μ` a measure; `n : ℕ`.
- Uses from project: [`mahlerTransform`, `twist`, `charCM`, `mahlerCM`, `coeff_mahlerTransform`, `twist_apply`, `apply_eq_tsum`, `charCM_natCast`, `mahlerCM_apply`]
- Used by: `mahlerTransform_charTwist_eq_substAffine`
- Visibility: public
- Lines: 109–144 (proof ~30 lines)
- Notes: long(30-50) — proof body ~30 lines; uses `fwdDiff` scoped notation

### lemma norm_pow_sub_one_lt_one
- Type: `{ζ : integerRing K} {n : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ n)) (c : ℕ) : ‖ζ ^ c - 1‖ < 1`
- What: Any power `ζ^c` of a primitive `p^n`-th root of unity satisfies `‖ζ^c − 1‖ < 1` (extending the primitive-root norm bound to all of `μ_{p^∞}`).
- How: If `ζ^c = 1` the bound is trivial; otherwise `orderOf (ζ^c) = p^j` for some `1 ≤ j` (via `Nat.dvd_prime_pow`), `ζ^c` is then a primitive `p^j`-th root of unity (mapped into `K` by `IsPrimitiveRoot.map_of_injective` along the subring inclusion), and `IsPrimitiveRoot.norm_sub_one_lt` gives the strict bound.
- Hypotheses: `ζ` a primitive `p^n`-th root of unity in `integerRing K`; `c : ℕ`. `omit [CompleteSpace K]`.
- Uses from project: []
- Used by: `tendsto_pow_pow_sub_one`
- Visibility: public
- Lines: 149–162 (proof ~12 lines)
- Notes: none

### lemma tendsto_pow_pow_sub_one
- Type: `{ζ : integerRing K} {n : ℕ} (hζ : IsPrimitiveRoot ζ (p ^ n)) (c : ℕ) : Filter.Tendsto ((ζ ^ c - 1) ^ ·) Filter.atTop (nhds 0)`
- What: For `ζ ∈ μ_{p^n}`, the element `ζ^c − 1` is topologically nilpotent (its powers tend to `0`).
- How: Immediate from `tendsto_pow_atTop_nhds_zero_of_norm_lt_one` applied to the norm bound `norm_pow_sub_one_lt_one`.
- Hypotheses: `ζ` a primitive `p^n`-th root of unity; `c : ℕ`. `omit [CompleteSpace K]`.
- Uses from project: [`norm_pow_sub_one_lt_one`]
- Used by: `res_class_eq_sum_twists`, `mahler_twist_formula` (as the `hr` argument to `charCM`)
- Visibility: public
- Lines: 166–169 (proof 1 line)
- Notes: none

### theorem res_class_eq_sum_twists
- Type: `{n : ℕ} (_hn : 1 ≤ n) {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ (p ^ n)) (b : ZMod (p ^ n)) (μ : MeasureR K ℤ_[p]) : ((p : ℕ) ^ n : integerRing K) • res p K (isClopen_toZModPow_fiber p n b) μ = ∑ c ∈ Finset.range (p ^ n), ζ ^ (c * (p ^ n - (b.val % p ^ n))) • twist p K (charCM (ζ ^ c - 1) ...) μ`
- What: Cleared restriction formula (RJW `EqRestrictionFormula`, ×`p^n`): `p^n` times the restriction of `μ` to the residue class `b + p^nℤ_[p]` equals a sum over `c` of `ζ^{-bc}` (realised as `ζ^{c(p^n−b.val)}`) times the `κ_{ζ^c−1}`-twist of `μ`.
- How: Establishes the pointwise orthogonality identity of the indicator `charFnCM` of the fibre as a sum of characters: by `Continuous.ext_on` over the dense natural numbers, each summand becomes `(ζ^{s+m})^c`, and `ζ^{s+m}=1` iff `m` reduces to `b` (via `hζ.pow_eq_one_iff_dvd`); in the membership case the sum is `p^n` (constant), in the non-membership case `geom_sum_mul` with `sub_ne_zero` forces it to `0`. Then integrate the pointwise identity through `μ` via `LinearMap.ext`, `map_smul`, `map_sum`, `twist_apply`.
- Hypotheses: `n ≥ 1` (hypothesis present but used only via name); `ζ` a primitive `p^n`-th root of unity; `b : ZMod (p^n)`; `μ` a measure.
- Uses from project: [`res`, `isClopen_toZModPow_fiber`, `twist`, `charCM`, `tendsto_pow_pow_sub_one`, `charFnCM`, `charCM_natCast`, `twist_apply`]
- Used by: unused in file
- Visibility: public
- Lines: 178–235 (proof ~57 lines)
- Notes: OVER-50 — proof body ~57 lines (needs /decompose-proof); `_hn` argument unused in body

### theorem mahler_twist_formula
- Type: `{n : ℕ} {χ : DirichletCharacter (integerRing K) (p ^ n)} (hχ : χ.IsPrimitive) {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ (p ^ n)) (μ : MeasureR K ℤ_[p]) : gaussSum χ⁻¹ (AddChar.zmodChar (p ^ n) hζ.pow_eq_one) • twist p K χ.toContinuousMapZp μ = ∑ c ∈ Finset.range (p ^ n), χ⁻¹ (c : ZMod (p ^ n)) • twist p K (charCM (ζ ^ c - 1) ...) μ`
- What: Cleared Mahler transform of the twist (RJW Lem 5.4, ×Gauss sum): for `χ` primitive mod `p^n` and `ζ` a primitive `p^n`-th root, `G(χ⁻¹)·𝓐(μ_χ) = ∑_c χ⁻¹(c)·𝓐(κ_{ζ^c−1}·μ)`.
- How: Establishes the pointwise Gauss–Fourier expansion `G(χ⁻¹)·χ̃ = ∑_c χ⁻¹(c)·κ_{ζ^c−1}` by `Continuous.ext_on` over dense naturals: each term rewrites as `χ⁻¹(c)·e.mulShift m (c)`, the sum is reindexed onto `ZMod (p^n)` by `Finset.sum_nbij'` to a Gauss sum `gaussSum χ⁻¹ (e.mulShift m)`, evaluated by `gaussSum_mulShift_of_isPrimitive` (using `hχinv` from `DirichletCharacter.conductor_inv`). Then integrate via `LinearMap.ext`, `map_smul`, `map_sum`, `twist_apply`.
- Hypotheses: `χ` primitive Dirichlet character mod `p^n` valued in `integerRing K`; `ζ` a primitive `p^n`-th root of unity; `μ` a measure.
- Uses from project: [`twist`, `charCM`, `tendsto_pow_pow_sub_one`, `DirichletCharacter.toContinuousMapZp`, `charCM_natCast`, `twist_apply`]
- Used by: unused in file
- Visibility: public
- Lines: 245–303 (proof ~58 lines)
- Notes: OVER-50 — proof body ~58 lines (needs /decompose-proof)

### instance (IsLinearTopology …)
- Type: `instance : IsLinearTopology (integerRing K)ᵐᵒᵖ (integerRing K)`
- What: Provides the linear-topology instance on the opposite ring acting on `integerRing K`, needed for the power-series product-topology evaluation machinery.
- How: `(IsCentralScalar.isLinearTopology_iff _).mpr inferInstance` — transfers the left/central linear-topology instance to the opposite-module side.
- Hypotheses: ambient `K` instances (in `substAffine` section, `open scoped PowerSeries.WithPiTopology`).
- Uses from project: []
- Used by: (instance — resolved implicitly by `hasEval_affine`, `substAffine`, `coeff_substAffine`)
- Visibility: public (instance)
- Lines: 309–310 (proof 1 line)
- Notes: none

### lemma hasEval_affine
- Type: `(r : integerRing K) (hr : ...) : PowerSeries.HasEval ((1 + X) * C (1 + r) - 1 : PowerSeries (integerRing K))`
- What: The affine substitution point `(1+X)(1+r)−1 = C r + C(1+r)·X` is topologically nilpotent (admits power-series evaluation) in the product topology whenever `r` is.
- How: Rewrites the point as `C r + C(1+r)·X`, then combines `HasEval.map continuous_C hr` (for the constant part) with `HasEval.X.mul_left` (for the `X` part) via `HasEval.add`.
- Hypotheses: `r` topologically nilpotent. `omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K]`.
- Uses from project: []
- Used by: `substAffine`, `substAffine_X`, `substAffine_C`, `coeff_substAffine`
- Visibility: public
- Lines: 315–328 (proof ~8 lines)
- Notes: none

### def substAffine
- Type: `(r : integerRing K) (hr : ...) : PowerSeries (integerRing K) →+* PowerSeries (integerRing K)`
- What: The substitution ring homomorphism `F(T) ↦ F((1+T)(1+r)−1)` (the eval₂ form of the `z`-twist transform), realised via mathlib's topological `PowerSeries.eval₂Hom` at the nilpotent affine point.
- How: `PowerSeries.eval₂Hom continuous_C (hasEval_affine r hr)`.
- Hypotheses: `r` topologically nilpotent.
- Uses from project: [`hasEval_affine`]
- Used by: `substAffine_X`, `substAffine_C`, `substAffine_one_add_X`, `coeff_substAffine`, `mahlerTransform_charTwist_eq_substAffine`
- Visibility: public (noncomputable)
- Lines: 333–337 (defn, no proof)
- Notes: none

### lemma substAffine_X
- Type: `(r : integerRing K) (hr : ...) : substAffine r hr PowerSeries.X = (1 + X) * C (1 + r) - 1`
- What: The substitution sends `X` to the affine point `(1+X)(1+r)−1`.
- How: Unfolds `substAffine`, `coe_eval₂Hom`, `eval₂_X`.
- Hypotheses: `r` topologically nilpotent.
- Uses from project: [`substAffine`]
- Used by: `substAffine_one_add_X`
- Visibility: public; `@[simp]`
- Lines: 340–344 (proof 1 line)
- Notes: none

### lemma substAffine_C
- Type: `(r : integerRing K) (hr : ...) (b : integerRing K) : substAffine r hr (PowerSeries.C b) = PowerSeries.C b`
- What: The substitution fixes constant power series `C b`.
- How: Unfolds `substAffine`, `coe_eval₂Hom`, `eval₂_C`.
- Hypotheses: `r` topologically nilpotent; `b : integerRing K`.
- Uses from project: [`substAffine`]
- Used by: unused in file
- Visibility: public; `@[simp]`
- Lines: 347–350 (proof 1 line)
- Notes: none

### lemma substAffine_one_add_X
- Type: `(r : integerRing K) (hr : ...) : substAffine r hr (1 + PowerSeries.X) = PowerSeries.C (1 + r) * (1 + PowerSeries.X)`
- What: The substitution sends `1 + X` to `C(1+r)·(1+X)`.
- How: `map_add`, `map_one`, `substAffine_X`, then `ring`.
- Hypotheses: `r` topologically nilpotent.
- Uses from project: [`substAffine`, `substAffine_X`]
- Used by: unused in file
- Visibility: public
- Lines: 353–357 (proof 2 lines)
- Notes: none

### lemma coeff_substAffine
- Type: `(r : integerRing K) (hr : ...) (F : PowerSeries (integerRing K)) (n : ℕ) : PowerSeries.coeff n (substAffine r hr F) = ∑' m, PowerSeries.coeff n (((1 + X) * C (1 + r) - 1) ^ m) * PowerSeries.coeff m F`
- What: The `n`-th coefficient of `substAffine r hr F` is the tsum over `m` of `coeff n (affine^m)` times `coeff m F` (the §5.1 tsum form of the substitution).
- How: From `PowerSeries.hasSum_eval₂`, maps through the continuous coefficient functional (`WithPiTopology.continuous_coeff`) via `HasSum.map`, rewrites `substAffine` to `coe_eval₂Hom` and uses `HasSum.tsum_eq`; summand-wise `coeff_C_mul` plus `ring`.
- Hypotheses: `r` topologically nilpotent; `F` a power series; `n : ℕ`.
- Uses from project: [`substAffine`, `hasEval_affine`]
- Used by: `mahlerTransform_charTwist_eq_substAffine`
- Visibility: public
- Lines: 361–376 (proof ~9 lines)
- Notes: none

### theorem mahlerTransform_charTwist_eq_substAffine
- Type: `(r : integerRing K) (hr : ...) (μ : MeasureR K ℤ_[p]) : mahlerTransform p K (twist p K (charCM r hr) μ) = substAffine r hr (mahlerTransform p K μ)`
- What: The §3.5 statement in the source's own form: the Mahler transform of the `z`-twist of `μ` equals the affine substitution applied to the Mahler transform of `μ`, i.e. `𝓐(κ_r·μ)(T) = 𝓐_μ((1+T)(1+r)−1)` (TeX 1084–1090).
- How: `PowerSeries.ext` reduces to coefficients; rewrites via `coeff_substAffine` and `mahlerTransform_charTwist`, then matches summands via `coeff_mahlerTransform` (tsum_congr).
- Hypotheses: `r` topologically nilpotent; `μ` a measure.
- Uses from project: [`mahlerTransform`, `twist`, `charCM`, `substAffine`, `coeff_substAffine`, `mahlerTransform_charTwist`, `coeff_mahlerTransform`]
- Used by: unused in file
- Visibility: public
- Lines: 381–387 (proof ~5 lines)
- Notes: none

---

## File Summary

- **Total declarations: 19** — defs: 3 (`twist`, `charCM`, `substAffine`); lemmas+theorems: 15 (`twist_apply`, `twist_powCM`, `charCM_natCast`, `isClopen_toZModPow_fiber`, `twist_res_units`, `mahlerTransform_charTwist`, `norm_pow_sub_one_lt_one`, `tendsto_pow_pow_sub_one`, `res_class_eq_sum_twists`, `mahler_twist_formula`, `hasEval_affine`, `substAffine_X`, `substAffine_C`, `substAffine_one_add_X`, `coeff_substAffine`, `mahlerTransform_charTwist_eq_substAffine`); instances: 1 (anonymous `IsLinearTopology` on `(integerRing K)ᵐᵒᵖ`).
- **Key API (used by ≥3 in this file):** `twist` (7 uses), `charCM` (5), `substAffine` (5), `charCM_natCast` (3), `twist_apply` (3). Cross-project consumers not assessed here.
- **Unused in file (no in-file consumer):** `twist_powCM`, `twist_res_units`, `res_class_eq_sum_twists`, `mahler_twist_formula`, `substAffine_C`, `substAffine_one_add_X`, `mahlerTransform_charTwist_eq_substAffine` (these are §5.1 export results / simp lemmas consumed elsewhere in the project).
- **Decls with `sorry`: none.**
- **`set_option`: none.**
- **Proofs >50 lines: 2** — `res_class_eq_sum_twists` (~57 lines), `mahler_twist_formula` (~58 lines). Both flagged OVER-50; candidates for /decompose-proof.
- **Proofs 30–50 lines: 1** — `mahlerTransform_charTwist` (~30 lines), flagged long(30-50).

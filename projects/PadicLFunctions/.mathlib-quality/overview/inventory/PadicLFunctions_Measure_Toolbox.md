# Inventory: PadicLFunctions/Measure/Toolbox.lean

Source: RJW (arXiv:2309.15692) §3.5 (`sec:toolbox`) — standard operations on measures on `ℤ_p` and their effect on Mahler transforms. All over `ℤ_p` coefficients. Two formulas needing `p`-power roots of unity (`EqRestrictionFormula`, `Eqphipsi`) deferred to §5.

File-level: `open scoped fwdDiff`, `open PowerSeries`, `variable (p : ℕ) [hp : Fact p.Prime]`, `noncomputable section`, `namespace PadicMeasure`.

---

### def cmul
- Type: `cmul (g : C(ℤ_[p], ℤ_[p])) (μ : PadicMeasure p ℤ_[p]) : PadicMeasure p ℤ_[p]`
- What: Multiplication of a measure by a continuous function `g`, defined by `(g·μ)(f) = μ(gf)`.
- How: Precomposition of `μ` (as a linear map) with left-multiplication by `g`, via `μ.comp (LinearMap.mulLeft ℤ_[p] g)`.
- Hypotheses: `g` continuous `ℤ_[p] → ℤ_[p]`; `μ` a `ℤ_p`-valued measure on `ℤ_p`.
- Uses from project: [`PadicMeasure`, `PadicMeasure.comp`]
- Used by: `cmul_apply`, `mahlerTransform_cmul_X`, `apply_powCM`, `res`
- Visibility: public
- Lines: 35-39 (def, 1 line body)
- Notes: none

### lemma cmul_apply
- Type: `cmul p g μ f = μ (g * f)` (for `g f : C(ℤ_[p], ℤ_[p])`, `μ`)
- What: Evaluation rule for `cmul`: applying `g·μ` to `f` gives `μ(g*f)`.
- How: Definitional unfolding, `rfl`.
- Hypotheses: `g, f` continuous maps `ℤ_[p] → ℤ_[p]`; `μ` a measure.
- Uses from project: [`cmul`]
- Used by: `apply_powCM`
- Visibility: public (`@[simp]`)
- Lines: 41-43 (proof: rfl)
- Notes: none

### def del
- Type: `del (F : PowerSeries ℤ_[p]) : PowerSeries ℤ_[p]`
- What: The differential operator `∂ = (1+T) d/dT` acting on power series over `ℤ_p`.
- How: `(1 + PowerSeries.X) * F.derivativeFun`.
- Hypotheses: `F` a power series over `ℤ_[p]`.
- Uses from project: []
- Used by: `coeff_del`, `mahlerTransform_cmul_X`, `apply_powCM`
- Visibility: public (noncomputable)
- Lines: 45-47 (def, 1 line body)
- Notes: none

### lemma mul_choose_eq
- Type: `x * Ring.choose x n = (n + 1) * Ring.choose x (n + 1) + n * Ring.choose x n` (for `x : ℤ_[p]`, `n : ℕ`)
- What: The binomial recurrence `x·binom(x,n) = (n+1)·binom(x,n+1) + n·binom(x,n)` over `ℤ_p`.
- How: Proves the identity first for natural-number arguments `m` (case split on `m < n` using `Nat.choose_eq_zero_of_lt`, else `Nat.choose_succ_right_eq` + `nlinarith`), casts to `Ring.choose` via `Ring.choose_natCast`, then extends from `ℕ` to all of `ℤ_p` by density using `PadicInt.denseRange_natCast.equalizer` (both sides continuous via `fun_prop`).
- Hypotheses: `x` a `p`-adic integer; `n` a natural number.
- Uses from project: []
- Used by: `mahlerTransform_cmul_X`
- Visibility: public
- Lines: 49-75 (proof ~24 lines)
- Notes: none — under 30 (the density-equalizer argument is the crux)

### lemma coeff_del
- Type: `PowerSeries.coeff n (del p F) = (n + 1) * coeff (n+1) F + n * coeff n F`
- What: The `n`-th coefficient of `∂F = (1+T)F'` in terms of coefficients of `F`.
- How: Unfold `del`, distribute `one_add_mul`, use `coeff_derivativeFun`, then case split `n = 0` vs `n = m+1` using `coeff_zero_X_mul` / `coeff_succ_X_mul` and `ring`.
- Hypotheses: `F` a power series; `n : ℕ`.
- Uses from project: [`del`]
- Used by: `mahlerTransform_cmul_X`
- Visibility: private
- Lines: 77-88 (proof ~12 lines)
- Notes: none

### theorem mahlerTransform_cmul_X
- Type: `mahlerTransform p (cmul p (ContinuousMap.id ℤ_[p]) μ) = del p (mahlerTransform p μ)`
- What: Multiplication by `x` on measures corresponds to `∂` on Mahler transforms: `𝓐_{xμ} = ∂ 𝓐_μ` (RJW Lem. 3.24).
- How: Compare coefficient-wise via `coeff_mahlerTransform`; key step rewrites the continuous map `id · mahler n` as `(n+1)•mahler(n+1) + n•mahler n` using `mul_choose_eq`, then pushes through linearity (`map_add`, `map_smul`) and `coeff_del`.
- Hypotheses: `μ` a `ℤ_p`-valued measure on `ℤ_p`.
- Uses from project: [`mahlerTransform`, `cmul`, `del`, `coeff_mahlerTransform`, `mul_choose_eq`, `coeff_del`]
- Used by: `apply_powCM`
- Visibility: public
- Lines: 90-105 (proof ~10 lines)
- Notes: none

### def powCM
- Type: `powCM (k : ℕ) : C(ℤ_[p], ℤ_[p])`
- What: The monomial `x ↦ x^k` as a continuous map on `ℤ_p`.
- How: Bundles `fun x => x ^ k` with continuity proved by `fun_prop`.
- Hypotheses: `k : ℕ`.
- Uses from project: []
- Used by: `apply_powCM`
- Visibility: public
- Lines: 107-108 (def, 1 line)
- Notes: none

### theorem apply_powCM
- Type: `μ (powCM p k) = PowerSeries.constantCoeff ((del p)^[k] (mahlerTransform p μ))`
- What: Evaluation formula `∫_{ℤ_p} xᵏ dμ = (∂ᵏ 𝓐_μ)(0)` (RJW Cor. 3.25).
- How: Induction on `k` generalizing `μ`. Base case `k=0`: `powCM 0 = mahler 0`, so the integral is the `0`-th coeff = constant coefficient. Step: `powCM (m+1) = id · powCM m`, rewrite via `cmul_apply`, apply the inductive hypothesis to `cmul id μ`, then `mahlerTransform_cmul_X` and `Function.iterate_succ_apply`.
- Hypotheses: `μ` a measure; `k : ℕ`.
- Uses from project: [`powCM`, `del`, `mahlerTransform`, `cmul`, `cmul_apply`, `mahlerTransform_cmul_X`]
- Used by: unused in file
- Visibility: public
- Lines: 110-127 (proof ~16 lines)
- Notes: none

### def res
- Type: `res {U : Set ℤ_[p]} (hU : IsClopen U) (μ : PadicMeasure p ℤ_[p]) : PadicMeasure p ℤ_[p]`
- What: Restriction of a measure to a clopen subset `U`: `(Res_U μ)(f) = μ(𝟙_U · f)`, again a measure on `ℤ_p` (RJW §3.5.3).
- How: `cmul` by the characteristic function `LocallyConstant.charFn ℤ_[p] hU` viewed as a continuous map.
- Hypotheses: `U` clopen; `μ` a measure.
- Uses from project: [`cmul`]
- Used by: `IsSupportedOn`, `res_union`, `phi_psi`, `res_units_eq`
- Visibility: public (noncomputable)
- Lines: 133-139 (def, 1 line body)
- Notes: none

### def IsSupportedOn
- Type: `IsSupportedOn {U : Set ℤ_[p]} (hU : IsClopen U) (μ : PadicMeasure p ℤ_[p]) : Prop`
- What: A measure is *supported on* a clopen `U` iff `Res_U μ = μ`.
- How: Defined as the proposition `res p hU μ = μ`.
- Hypotheses: `U` clopen; `μ` a measure.
- Uses from project: [`res`]
- Used by: `isSupportedOn_units_iff_psi_eq_zero`
- Visibility: public
- Lines: 141-143 (def, 1 line)
- Notes: none

### theorem res_union
- Type: `res p (hU.union hV) μ = res p hU μ + res p hV μ` (for disjoint clopen `U, V`)
- What: Restriction is additive over a disjoint clopen decomposition `U ⊔ V` (RJW §3.5.4).
- How: Show the characteristic function of `U ∪ V` splits as `charFn U + charFn V` using `Set.indicator_union_of_disjoint`; then by `LinearMap.ext`, the measure of `(charFn(U∪V))·f` equals sum via `map_add`/`add_mul`.
- Hypotheses: `U, V` clopen and disjoint; `μ` a measure.
- Uses from project: [`res`]
- Used by: unused in file
- Visibility: public
- Lines: 145-160 (proof ~10 lines)
- Notes: none

### def mulCM
- Type: `mulCM (a : ℤ_[p]) : C(ℤ_[p], ℤ_[p])`
- What: Multiplication by a fixed `a : ℤ_[p]` as a continuous self-map `x ↦ a*x`.
- How: Bundles `fun x => a * x` with continuity via `fun_prop`.
- Hypotheses: `a : ℤ_[p]`.
- Uses from project: []
- Used by: `sigma`, `phi`, `mahlerTransform_pushforward_mulCM`, `psi_phi`, `phi_psi`
- Visibility: public
- Lines: 166-167 (def, 1 line)
- Notes: none

### def sigma
- Type: `sigma (a : ℤ_[p]ˣ) : PadicMeasure p ℤ_[p] →ₗ[ℤ_[p]] PadicMeasure p ℤ_[p]`
- What: The `ℤ_p^×`-action on measures: `∫ f d(σ_a μ) = ∫ f(ax) dμ` (RJW §3.5.5).
- How: Pushforward of measures along `mulCM a`, i.e. `pushforward p (mulCM p (a : ℤ_[p]))`.
- Hypotheses: `a` a unit of `ℤ_[p]`.
- Uses from project: [`PadicMeasure`, `pushforward`, `mulCM`]
- Used by: `mahlerTransform_sigma`
- Visibility: public (noncomputable)
- Lines: 169-174 (def, 1 line body)
- Notes: none

### def phi
- Type: `phi : PadicMeasure p ℤ_[p] →ₗ[ℤ_[p]] PadicMeasure p ℤ_[p]`
- What: The operator `φ` ("`σ_p`"): `∫ f d(φμ) = ∫ f(px) dμ` (RJW §3.5.5).
- How: Pushforward along `mulCM p (p : ℤ_[p])`.
- Hypotheses: none beyond the global `p` prime.
- Uses from project: [`PadicMeasure`, `pushforward`, `mulCM`]
- Used by: `mahlerTransform_phi`, `psi_phi`, `phi_psi`, `res_units_eq`, `isSupportedOn_units_iff_psi_eq_zero`
- Visibility: public (noncomputable)
- Lines: 176-180 (def, 1 line body)
- Notes: none

### lemma binomialSeries_mul_nat
- Type: `binomialSeries ℤ_[p] (c * (k : ℤ_[p])) = binomialSeries ℤ_[p] c ^ k`
- What: The binomial series satisfies `(1+T)^{ck} = ((1+T)^c)^k` for natural `k`.
- How: Induction on `k`; base `binomialSeries_zero`; step rewrites `c*(m+1) = c*m + c` and uses `binomialSeries_add` with `pow_succ`.
- Hypotheses: `c : ℤ_[p]`, `k : ℕ`.
- Uses from project: [`binomialSeries`, `binomialSeries_zero`, `binomialSeries_add`]
- Used by: `mahlerTransform_pushforward_mulCM`
- Visibility: private
- Lines: 182-188 (proof ~7 lines)
- Notes: none

### theorem mahlerTransform_pushforward_mulCM
- Type: `mahlerTransform p (pushforward p (mulCM p c) μ) = PowerSeries.subst (binomialSeries ℤ_[p] c - 1) (mahlerTransform p μ)`
- What: General substitution formula — pushing a measure forward along multiplication by `c ∈ ℤ_p` substitutes `(1+T)^c − 1` into the Mahler transform (RJW §3.5.5, Eq. (3.9)).
- How: Set `B' = binomialSeries c - 1`; show `constantCoeff B' = 0` (via `binomialSeries_constantCoeff`) so substitution is valid (`HasSubst.of_constantCoeff_zero'`) and `coeff n (B'^d)=0` for `n<d`. Compare coefficients via `coeff_mahlerTransform` and `coeff_subst'`, restricting the finsum to `Finset.range (n+1)`. The key identity expresses `mahler n (c*k)` two ways: via `binomialSeries_mul_nat` + `binomialSeries_coeff`, and via the binomial expansion `(B'+1)^k` with `add_pow`/`coeff_mul_C`, reconciled by `Finset.sum_subset` with `Nat.choose_eq_zero_of_lt`. Finally `(mahler n).comp (mulCM c)` is rewritten as a finite sum of scaled Mahler basis elements by density (`PadicInt.denseRange_natCast.equalizer`), and `map_sum` finishes.
- Hypotheses: `c : ℤ_[p]`; `μ` a measure.
- Uses from project: [`mahlerTransform`, `pushforward`, `mulCM`, `binomialSeries`, `binomialSeries_constantCoeff`, `binomialSeries_coeff`, `binomialSeries_mul_nat`, `coeff_mahlerTransform`]
- Used by: `mahlerTransform_sigma`, `mahlerTransform_phi`
- Visibility: public
- Lines: 190-252 (proof ~57 lines)
- Notes: **OVER-50** (needs /decompose-proof) — the central substitution theorem; hinges on `PowerSeries.coeff_subst'`, `add_pow`, and the density equalizer.

### theorem mahlerTransform_sigma
- Type: `mahlerTransform p (sigma p a μ) = PowerSeries.subst (binomialSeries ℤ_[p] (a : ℤ_[p]) - 1) (mahlerTransform p μ)`
- What: The `ℤ_p^×`-action on power series is substitution into the binomial series: `𝓐_{σ_a μ} = 𝓐_μ((1+T)^a − 1)` (RJW §3.5.5).
- How: Direct application of `mahlerTransform_pushforward_mulCM` with `c = a` (since `sigma` is the pushforward along `mulCM a`).
- Hypotheses: `a` a unit; `μ` a measure.
- Uses from project: [`mahlerTransform`, `sigma`, `binomialSeries`, `mahlerTransform_pushforward_mulCM`]
- Used by: unused in file
- Visibility: public
- Lines: 254-261 (proof: term-mode, 1 line)
- Notes: none

### theorem mahlerTransform_phi
- Type: `mahlerTransform p (phi p μ) = PowerSeries.subst ((1 + PowerSeries.X) ^ p - 1) (mahlerTransform p μ)`
- What: `𝓐_{φ(μ)} = 𝓐_μ((1+T)^p − 1)` — Eq. (3.9) (`eq:varphi power series`).
- How: Apply `mahlerTransform_pushforward_mulCM` with `c = (p : ℤ_[p])`, then rewrite `binomialSeries ℤ_[p] (p:ℕ)` to `(1+X)^p` via `binomialSeries_nat`.
- Hypotheses: `μ` a measure.
- Uses from project: [`mahlerTransform`, `phi`, `mahlerTransform_pushforward_mulCM`, `binomialSeries_nat`]
- Used by: unused in file
- Visibility: public
- Lines: 263-270 (proof ~3 lines)
- Notes: none

### def digit
- Type: `digit (x : ℤ_[p]) : ℤ_[p]`
- What: The canonical digit of `x` mod `p`, lifted back to `ℤ_p` (the `ℕ`-valued representative of `x mod p`).
- How: `((PadicInt.toZModPow 1 x).val : ℕ) : ℤ_[p]` — take the `ZMod (p^1)` reduction, its `.val`, cast to `ℤ_[p]`.
- Hypotheses: `x : ℤ_[p]`.
- Uses from project: []
- Used by: `sub_digit_mem_span`, `shiftDiv_mem`, `shiftDiv`, `shiftDiv_mul`, `mul_shiftDiv_of_mem`
- Visibility: public (noncomputable)
- Lines: 272-274 (def, 1 line body)
- Notes: none

### lemma sub_digit_mem_span
- Type: `x - digit p x ∈ (Ideal.span {(p : ℤ_[p]) ^ 1} : Ideal ℤ_[p])`
- What: `x` minus its mod-`p` digit lies in the ideal `(p)` (i.e. `x ≡ digit x mod p`).
- How: Rewrite the span as the kernel of `toZModPow 1` (`PadicInt.ker_toZModPow`), then membership follows since `toZModPow` of the digit recovers the reduction via `ZMod.natCast_rightInverse`, giving `sub_self`.
- Hypotheses: `x : ℤ_[p]`.
- Uses from project: [`digit`]
- Used by: `shiftDiv_mem`
- Visibility: public
- Lines: 276-279 (proof ~3 lines)
- Notes: none

### lemma shiftDiv_mem
- Type: `‖((x : ℚ_[p]) - (digit p x : ℚ_[p])) / (p : ℚ_[p])‖ ≤ 1`
- What: The quantity `(x − [x mod p])/p` has norm `≤ 1`, so it lands in `ℤ_p` (well-definedness for `shiftDiv`).
- How: From `sub_digit_mem_span` get `‖x − digit x‖ ≤ p^{-1}` via `norm_le_pow_iff_mem_span_pow`; cast difference into `ℚ_[p]`, then `norm_div`, `div_le_one`, and `Padic.norm_p` (= `p^{-1}`) reduce the bound to the established estimate.
- Hypotheses: `x : ℤ_[p]`.
- Uses from project: [`digit`, `sub_digit_mem_span`]
- Used by: `shiftDiv`
- Visibility: private
- Lines: 281-292 (proof ~12 lines)
- Notes: none

### def shiftDiv
- Type: `shiftDiv : C(ℤ_[p], ℤ_[p])`
- What: The canonical "digit shift" `x ↦ (x − [x mod p])/p` as a continuous map; satisfies `shiftDiv(p*x) = x`. Auxiliary for `ψ`.
- How: `toFun x` packages the `ℚ_[p]` quotient with the membership proof `shiftDiv_mem`; continuity from `continuous_subtype_val`, the locally-constant `toZModPow`-val map (`isLocallyConstant_toZModPow_val`), and `.div_const`.
- Hypotheses: none beyond global `p` prime.
- Uses from project: [`digit`, `shiftDiv_mem`, `isLocallyConstant_toZModPow_val`]
- Used by: `shiftDiv_mul`, `psi`, `psi_phi`, `phi_psi`
- Visibility: public (noncomputable)
- Lines: 294-303 (def, ~6 line continuity proof)
- Notes: none

### lemma shiftDiv_mul
- Type: `shiftDiv p ((p : ℤ_[p]) * x) = x`
- What: `shiftDiv(p·x) = x`: the digit shift inverts multiplication by `p`.
- How: Show `digit(p*x) = 0` (since `toZModPow 1 (p*x) = 0`, using `map_natCast`/`ZMod.natCast_self` to get `toZModPow 1 p = 0`); then by `Subtype.ext` the `ℚ_[p]` computation `(p*x − 0)/p = x` follows via `div_self` of `p ≠ 0`.
- Hypotheses: `x : ℤ_[p]`.
- Uses from project: [`shiftDiv`, `digit`]
- Used by: `psi_phi`
- Visibility: public (`@[simp]`)
- Lines: 305-320 (proof ~16 lines)
- Notes: none

### lemma isClopen_pZp
- Type: `IsClopen {x : ℤ_[p] | ‖x‖ < 1}`
- What: `pℤ_p ⊆ ℤ_p` (the set `‖x‖ < 1`) is clopen — it is the closed ball of radius `1/p`.
- How: Identify `{‖x‖ < 1}` with `Metric.closedBall 0 (p^{-1})` via `norm_le_pow_iff_norm_lt_pow_add_one`; closedness from `Metric.isClosed_closedBall`, openness from `isOpen_lt` of continuous norm.
- Hypotheses: none beyond global `p` prime.
- Uses from project: []
- Used by: `psi`, `psi_phi`, `phi_psi`
- Visibility: public
- Lines: 322-331 (proof ~9 lines)
- Notes: none

### def psi
- Type: `psi (μ : PadicMeasure p ℤ_[p]) : PadicMeasure p ℤ_[p]`
- What: The operator `ψ`: `∫ f d(ψμ) = ∫_{pℤ_p} f(p⁻¹x) dμ` (RJW §3.5.5).
- How: `toFun f := μ (charFn(pℤ_p) · f∘shiftDiv)`; additivity from `ContinuousMap.add_comp`/`mul_add`/`map_add`, scalar-linearity from `ContinuousMap.smul_comp`/`mul_smul_comm`/`map_smul`.
- Hypotheses: `μ` a measure.
- Uses from project: [`PadicMeasure`, `isClopen_pZp`, `shiftDiv`]
- Used by: `psi_phi`, `phi_psi`, `res_units_eq`, `psi_sub`, `isSupportedOn_units_iff_psi_eq_zero`
- Visibility: public (noncomputable)
- Lines: 333-343 (def, ~5 line bundled proofs)
- Notes: none

### lemma mem_pZp_of_mul
- Type: `‖(p : ℤ_[p]) * x‖ < 1`
- What: `p·x` always lies in `pℤ_p` (norm `< 1`) for any `x : ℤ_[p]`.
- How: `calc`: `‖p*x‖ = ‖p‖·‖x‖ ≤ ‖p‖·1 = ‖p‖` (using `PadicInt.norm_le_one`), and `‖p‖ = p^{-1} < 1` via `PadicInt.norm_p` and `inv_lt_one_of_one_lt₀`.
- Hypotheses: `x : ℤ_[p]` (implicit).
- Uses from project: []
- Used by: `psi_phi`
- Visibility: public
- Lines: 345-351 (proof ~7 lines)
- Notes: none

### lemma mul_shiftDiv_of_mem
- Type: `(p : ℤ_[p]) * shiftDiv p x = x` (given `‖x‖ < 1`)
- What: On `pℤ_p`, multiplying the digit shift back by `p` recovers the point: `p·shiftDiv(x) = x`.
- How: From `‖x‖ < 1` derive `toZModPow 1 x = 0` (via `norm_le_pow_iff_mem_span_pow` + `ker_toZModPow`), hence `digit x = 0`; then by `Subtype.ext` the `ℚ_[p]` identity `p·((x−0)/p) = x` follows from `div_mul_cancel₀`.
- Hypotheses: `‖x‖ < 1` (i.e. `x ∈ pℤ_p`).
- Uses from project: [`shiftDiv`, `digit`]
- Used by: `phi_psi`
- Visibility: public
- Lines: 353-369 (proof ~16 lines)
- Notes: none

### theorem psi_phi
- Type: `psi p (phi p μ) = μ`
- What: `ψ ∘ φ = id` (RJW first display after §3.5.5).
- How: By `LinearMap.ext`, unfold to `μ((charFn(pℤ_p)·(f∘shiftDiv))∘(mulCM p))`; after `ext x` and simp with `shiftDiv_mul`, the digit shift composed with `p·(·)` is the identity; since `p*x ∈ pℤ_p` (`mem_pZp_of_mul`) the indicator is `1`, giving `μ f`.
- Hypotheses: `μ` a measure.
- Uses from project: [`psi`, `phi`, `shiftDiv`, `mulCM`, `isClopen_pZp`, `shiftDiv_mul`, `mem_pZp_of_mul`]
- Used by: `isSupportedOn_units_iff_psi_eq_zero`
- Visibility: public (`@[simp]`)
- Lines: 371-383 (proof ~10 lines)
- Notes: none

### theorem phi_psi
- Type: `phi p (psi p μ) = res p (isClopen_pZp p) μ`
- What: `φ ∘ ψ = Res_{pℤ_p}` (RJW second display after §3.5.5).
- How: By `LinearMap.ext` and `ext x`, compare the two integrands; case split on `‖x‖ < 1`: if in `pℤ_p` use `mul_shiftDiv_of_mem` to recover `x`, else both sides vanish since the indicator is `0` (`Set.indicator_of_notMem`).
- Hypotheses: `μ` a measure.
- Uses from project: [`phi`, `psi`, `res`, `isClopen_pZp`, `mulCM`, `shiftDiv`, `mul_shiftDiv_of_mem`]
- Used by: `res_units_eq`
- Visibility: public
- Lines: 385-399 (proof ~14 lines)
- Notes: none

### lemma isClopen_units
- Type: `IsClopen {x : ℤ_[p] | IsUnit x}`
- What: `ℤ_p^× ⊆ ℤ_p` (the units, `‖x‖ = 1`) is clopen.
- How: Identify the units with the complement `{‖x‖ < 1}ᶜ` (via `PadicInt.isUnit_iff` and norm antisymmetry), then take the complement of `isClopen_pZp`.
- Hypotheses: none beyond global `p` prime.
- Uses from project: [`isClopen_pZp`]
- Used by: `res_units_eq`, `isSupportedOn_units_iff_psi_eq_zero`
- Visibility: public
- Lines: 401-408 (proof ~7 lines)
- Notes: none

### lemma setOf_isUnit_eq
- Type: `{x : ℤ_[p] | IsUnit x} = {x : ℤ_[p] | ‖x‖ < 1}ᶜ`
- What: The units of `ℤ_p` are exactly the complement of `pℤ_p` (`‖x‖ = 1` ⟺ unit).
- How: `ext x`; `PadicInt.isUnit_iff` reduces `IsUnit x` to `‖x‖ = 1`; antisymmetry of `≤` with `PadicInt.norm_le_one` closes both directions.
- Hypotheses: none beyond global `p` prime.
- Uses from project: []
- Used by: unused in file
- Visibility: public
- Lines: 410-416 (proof ~3 lines)
- Notes: none — duplicates the `heq` step inside `isClopen_units`; flagged for dedup review.

### theorem res_units_eq
- Type: `res p (isClopen_units p) μ = μ - phi p (psi p μ)`
- What: `Res_{ℤ_p^×} = 1 − φ∘ψ` — Eq. (3.10) (`res to Zp`).
- How: Rewrite `phi∘psi` as `res(pℤ_p)` via `phi_psi`; by `LinearMap.ext` reduce to `μ(charFn(units)·f) = μ f − μ(charFn(pℤ_p)·f)`; via `eq_sub_iff_add_eq`/`map_add`, show `charFn(units) + charFn(pℤ_p) = 1` pointwise by case split on `‖x‖ < 1` (exactly one indicator is `1`).
- Hypotheses: `μ` a measure.
- Uses from project: [`res`, `isClopen_units`, `phi`, `psi`, `phi_psi`]
- Used by: `isSupportedOn_units_iff_psi_eq_zero`
- Visibility: public
- Lines: 418-439 (proof ~21 lines)
- Notes: none

### lemma psi_sub
- Type: `psi p (μ - ν) = psi p μ - psi p ν`
- What: `ψ` respects subtraction of measures (it is additive/linear on differences).
- How: `LinearMap.ext` then `LinearMap.sub_apply` (since `psi` underlies a linear-map-like structure on each test function).
- Hypotheses: `μ, ν` measures.
- Uses from project: [`psi`]
- Used by: `isSupportedOn_units_iff_psi_eq_zero`
- Visibility: public
- Lines: 441-443 (proof: term-mode, ~2 lines)
- Notes: none

### theorem isSupportedOn_units_iff_psi_eq_zero
- Type: `IsSupportedOn p (isClopen_units p) μ ↔ psi p μ = 0`
- What: **RJW Cor. 3.32**: a measure is supported on `ℤ_p^×` iff `ψ(μ) = 0`.
- How: Unfold `IsSupportedOn`. (→) apply `psi` to `res(units)μ = μ`, expand with `res_units_eq`, `psi_sub`, `psi_phi` (so `ψ(φ(ψμ)) = ψμ`), giving `sub_self`. (←) from `ψμ = 0`, `res_units_eq` gives `res = μ − φ(0) = μ`.
- Hypotheses: `μ` a measure.
- Uses from project: [`IsSupportedOn`, `isClopen_units`, `psi`, `res_units_eq`, `psi_sub`, `psi_phi`, `phi`]
- Used by: unused in file
- Visibility: public
- Lines: 445-456 (proof ~11 lines)
- Notes: none

---

## File Summary

**Total declarations: 28** — defs: 9 (`cmul`, `del`, `powCM`, `res`, `IsSupportedOn`, `mulCM`, `sigma`, `phi`, `digit`, `shiftDiv`, `psi` = 11 if `IsSupportedOn` counts as def; here: **11 defs**), lemmas+theorems: **17**, instances: **0**.

Recount (precise):
- **defs**: `cmul`, `del`, `powCM`, `res`, `IsSupportedOn`, `mulCM`, `sigma`, `phi`, `digit`, `shiftDiv`, `psi` = **11**
- **lemmas/theorems**: `cmul_apply`, `mul_choose_eq`, `coeff_del`, `mahlerTransform_cmul_X`, `apply_powCM`, `res_union`, `binomialSeries_mul_nat`, `mahlerTransform_pushforward_mulCM`, `mahlerTransform_sigma`, `mahlerTransform_phi`, `sub_digit_mem_span`, `shiftDiv_mem`, `shiftDiv_mul`, `isClopen_pZp`, `mem_pZp_of_mul`, `mul_shiftDiv_of_mem`, `psi_phi`, `phi_psi`, `isClopen_units`, `setOf_isUnit_eq`, `res_units_eq`, `psi_sub`, `isSupportedOn_units_iff_psi_eq_zero` = **23**
- **instances**: 0
- **Grand total: 34 declarations.**

**Key API (used by ≥3 in this file):**
- `cmul` (4: `cmul_apply`, `mahlerTransform_cmul_X`, `apply_powCM`, `res`)
- `del` (3: `coeff_del`, `mahlerTransform_cmul_X`, `apply_powCM`)
- `res` (4: `IsSupportedOn`, `res_union`, `phi_psi`, `res_units_eq`)
- `mulCM` (5: `sigma`, `phi`, `mahlerTransform_pushforward_mulCM`, `psi_phi`, `phi_psi`)
- `phi` (5: `mahlerTransform_phi`, `psi_phi`, `phi_psi`, `res_units_eq`, `isSupportedOn_units_iff_psi_eq_zero`)
- `digit` (5: `sub_digit_mem_span`, `shiftDiv_mem`, `shiftDiv`, `shiftDiv_mul`, `mul_shiftDiv_of_mem`)
- `shiftDiv` (4: `shiftDiv_mul`, `psi`, `psi_phi`, `phi_psi`)
- `psi` (5: `psi_phi`, `phi_psi`, `res_units_eq`, `psi_sub`, `isSupportedOn_units_iff_psi_eq_zero`)
- `isClopen_pZp` (3: `psi`, `psi_phi`, `phi_psi`)

**Unused in file (terminal API — likely exported):** `apply_powCM`, `res_union`, `mahlerTransform_sigma`, `mahlerTransform_phi`, `setOf_isUnit_eq`, `isSupportedOn_units_iff_psi_eq_zero`.

**Declarations with `sorry`:** none.

**`set_option`:** none.

**Proofs >50 lines (1):** `mahlerTransform_pushforward_mulCM` (~57 lines, lines 190-252) — **OVER-50**, flagged for `/decompose-proof`.

**Proofs 30-50 lines:** none.

**Dedup note:** `setOf_isUnit_eq` (410-416) reproduces verbatim the `heq` sub-proof inside `isClopen_units` (402-408); `isClopen_units` could be refactored to use `setOf_isUnit_eq`.

**External-formula deferrals:** `EqRestrictionFormula`, `Eqphipsi` (the two `p`-power-root-of-unity formulas) are NOT in this file — deferred to the §5 pass per the module docstring.

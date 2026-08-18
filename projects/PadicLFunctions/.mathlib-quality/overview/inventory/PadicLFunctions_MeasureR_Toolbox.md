# Inventory: PadicLFunctions/MeasureR/Toolbox.lean

File-level context: RJW §3.5 measure-theoretic toolbox over `R := integerRing K` (the integer ring of a complete ultrametric normed field `K` that is a normed `ℚ_[p]`-algebra). Provides multiplication of measures by continuous functions and by `x` (the operator `∂ = (1+T)d/dT`), evaluation at monomials `x^k`, restriction to clopens, the `ℤ_p^×`-action `σ_a`, the operators `φ`, `ψ`, and their identities. Space-side gadgets (`digit`, `shiftDiv`, clopen sets) are reused from the `ℤ_p`-layer `PadicLFunctions/Measure/Toolbox.lean`.

Global variables: `p : ℕ` `[Fact p.Prime]`; `K : Type*` with `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]`. Whole file under `noncomputable section`, namespace `PadicLFunctions.MeasureR`.

---

### def cmul
- Type: `(g : C(ℤ_[p], integerRing K)) (μ : MeasureR K ℤ_[p]) : MeasureR K ℤ_[p]`
- What: Multiplication of a measure by a continuous `R`-valued function: `(g·μ)(f) = μ(gf)`.
- How: Defined as `μ.comp (LinearMap.mulLeft (integerRing K) g)` — precompose the measure (a continuous linear functional) with left-multiplication by `g` on the space of test functions.
- Hypotheses: `g` a continuous `R`-valued function on `ℤ_[p]`; `μ` a measure.
- Uses from project: [`MeasureR`]
- Used by: `cmul_apply`, `mahlerTransform_cmul_X`, `apply_powCM`, `res`
- Visibility: public
- Lines: 35–38 (def, no proof)
- Notes: none

### lemma cmul_apply
- Type: `(g f : C(ℤ_[p], integerRing K)) (μ : MeasureR K ℤ_[p]) : cmul p K g μ f = μ (g * f)`
- What: Computes `cmul` on a test function `f`: it equals `μ` applied to the product `g * f`.
- How: `rfl` — definitional unfolding of `cmul` and `LinearMap.mulLeft`.
- Hypotheses: as in signature.
- Uses from project: [`cmul`, `MeasureR`]
- Used by: `mahlerTransform_cmul_X`, `apply_powCM`
- Visibility: public (`@[simp]`)
- Lines: 42–45 (proof: 1 line `rfl`)
- Notes: `omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K]`

### def del
- Type: `(F : PowerSeries (integerRing K)) : PowerSeries (integerRing K)`
- What: The operator `∂ = (1+T)d/dT` on `R⟦T⟧` (RJW Lem 3.24).
- How: Defined as `(1 + PowerSeries.X) * F.derivativeFun`.
- Hypotheses: `F` a power series over `R`.
- Uses from project: []
- Used by: `coeff_del`, `mahlerTransform_cmul_X`, `apply_powCM`
- Visibility: public
- Lines: 49–51 (def, no proof)
- Notes: none

### lemma coeff_del (private)
- Type: `(F : PowerSeries (integerRing K)) (n : ℕ) : PowerSeries.coeff n (del K F) = (n + 1 : R) * coeff (n+1) F + (n : R) * coeff n F`
- What: The coefficient formula for `∂F`: `(∂F)_n = (n+1)F_{n+1} + n·F_n`.
- How: Unfold `del`, distribute `one_add_mul`, use `coeff_derivativeFun`; case split on `n = 0` vs `n = m+1` using `coeff_zero_X_mul` / `coeff_succ_X_mul`, then `push_cast`/`ring`.
- Hypotheses: as in signature.
- Uses from project: [`del`]
- Used by: `mahlerTransform_cmul_X`
- Visibility: private
- Lines: 57–68 (proof: ~11 lines); hinges on `PowerSeries.coeff_derivativeFun`, `coeff_succ_X_mul`
- Notes: `omit [CompleteSpace K]`

### theorem mahlerTransform_cmul_X
- Type: `(μ : MeasureR K ℤ_[p]) : mahlerTransform p K (cmul p K (mahlerCM p K 1) μ) = del K (mahlerTransform p K μ)`
- What: Multiplication by `x` corresponds to applying `∂` on the Mahler transform side: `𝓐_{xμ} = ∂𝓐_μ` (RJW Lem 3.24), where multiplication by `x` is multiplication by the `R`-valued inclusion `mahlerCM p K 1`.
- How: Prove equality coefficientwise (`PowerSeries.ext`); the key step `hpt` rewrites the product `mahlerCM 1 * mahlerCM n` as `(n+1)•mahlerCM(n+1) + n•mahlerCM n` via the binomial/Pochhammer identity `PadicMeasure.mul_choose_eq` and `Ring.choose_one_right`; then push linearity through `μ` and match against `coeff_del`.
- Hypotheses: `μ` a measure.
- Uses from project: [`mahlerTransform`, `cmul`, `mahlerCM`, `MeasureR`, `del`, `coeff_mahlerTransform`, `cmul_apply`, `mahlerCM_apply`, `coeff_del`, `PadicMeasure.mul_choose_eq`]
- Used by: `apply_powCM`
- Visibility: public
- Lines: 74–91 (proof: ~17 lines); hinges on `PadicMeasure.mul_choose_eq` and `coeff_mahlerTransform`
- Notes: `omit [CompleteSpace K]`; long(... actually 18 lines) — under 30, no flag

### def powCM
- Type: `(k : ℕ) : C(ℤ_[p], integerRing K)`
- What: The monomial function `x ↦ x^k`, valued in `R` via the algebra map.
- How: Bundled continuous map `⟨fun x => algebraMap ℤ_[p] (integerRing K) (x^k), …⟩`; continuity from `integerRing.isometry_algebraMap` composed with `fun_prop` continuity of `x ↦ x^k`.
- Hypotheses: `k : ℕ`.
- Uses from project: [`integerRing.isometry_algebraMap`]
- Used by: `powCM_apply`, `apply_powCM`, `phi_apply_powCM`
- Visibility: public
- Lines: 96–98 (def, no proof)
- Notes: none

### lemma powCM_apply
- Type: `(k : ℕ) (x : ℤ_[p]) : powCM p K k x = algebraMap ℤ_[p] (integerRing K) (x ^ k)`
- What: Computes `powCM` pointwise: at `x` it is the algebra-map image of `x^k`.
- How: `rfl`.
- Hypotheses: as in signature.
- Uses from project: [`powCM`]
- Used by: `apply_powCM`, `phi_apply_powCM`
- Visibility: public (`@[simp]`)
- Lines: 102–105 (proof: 1 line `rfl`)
- Notes: `omit [CompleteSpace K]`

### theorem apply_powCM
- Type: `(μ : MeasureR K ℤ_[p]) (k : ℕ) : μ (powCM p K k) = PowerSeries.constantCoeff ((del K)^[k] (mahlerTransform p K μ))`
- What: Moment formula: `∫ x^k dμ = (∂^k 𝓐_μ)(0)` (RJW Cor 3.25).
- How: Induction on `k`. Base case: `powCM 0 = mahlerCM 0`, so the integral is the constant coefficient of the Mahler transform. Inductive step: `powCM (m+1) = mahlerCM 1 * powCM m` (via `Ring.choose_one_right`, `pow_succ`), then rewrite through `cmul`, apply IH to `cmul p K (mahlerCM 1) μ`, and use `mahlerTransform_cmul_X` to turn the extra factor into one more `del`-iterate.
- Hypotheses: `μ` a measure; `k : ℕ`.
- Uses from project: [`powCM`, `MeasureR`, `del`, `mahlerTransform`, `mahlerCM`, `coeff_mahlerTransform`, `cmul`, `cmul_apply`, `mahlerTransform_cmul_X`, `powCM_apply`, `mahlerCM_apply`]
- Used by: unused in file
- Visibility: public
- Lines: 109–126 (proof: ~18 lines); hinges on `mahlerTransform_cmul_X` and `coeff_mahlerTransform`
- Notes: `omit [CompleteSpace K]`

### def res
- Type: `{U : Set ℤ_[p]} (hU : IsClopen U) (μ : MeasureR K ℤ_[p]) : MeasureR K ℤ_[p]`
- What: Restriction of a measure to a clopen subset `U` (RJW §3.5.3), i.e. multiply by the characteristic function of `U`.
- How: Defined as `cmul p K (charFnCM K ℤ_[p] hU) μ`.
- Hypotheses: `U` a clopen subset of `ℤ_[p]`; `μ` a measure.
- Uses from project: [`cmul`, `charFnCM`, `MeasureR`]
- Used by: `IsSupportedOn`, `phi_psi`, `res_units_eq`, `isSupportedOn_units_iff_psi_eq_zero`
- Visibility: public
- Lines: 132–134 (def, no proof)
- Notes: none

### def IsSupportedOn
- Type: `{U : Set ℤ_[p]} (hU : IsClopen U) (μ : MeasureR K ℤ_[p]) : Prop`
- What: A measure is supported on a clopen `U` iff its restriction to `U` equals itself (`Res_U μ = μ`).
- How: Defined as the proposition `res p K hU μ = μ`.
- Hypotheses: `U` clopen; `μ` a measure.
- Uses from project: [`res`, `MeasureR`]
- Used by: `isSupportedOn_units_iff_psi_eq_zero`, `psi_dirac_of_isUnit`
- Visibility: public
- Lines: 137–138 (def, no proof)
- Notes: none

### def sigma
- Type: `(a : ℤ_[p]ˣ) : MeasureR K ℤ_[p] →ₗ[integerRing K] MeasureR K ℤ_[p]`
- What: The `ℤ_p^×`-action `σ_a` on measures (RJW §3.5.5), pushforward along multiplication by the unit `a`.
- How: Defined as `pushforward K ℤ_[p] ℤ_[p] (PadicMeasure.mulCM p (a : ℤ_[p]))`.
- Hypotheses: `a` a unit of `ℤ_[p]`.
- Uses from project: [`pushforward`, `MeasureR`, `PadicMeasure.mulCM`]
- Used by: unused in file
- Visibility: public
- Lines: 145–146 (def, no proof)
- Notes: none

### def phi
- Type: `: MeasureR K ℤ_[p] →ₗ[integerRing K] MeasureR K ℤ_[p]`
- What: The operator `φ` (RJW §3.5.5), pushforward along multiplication by `p`.
- How: Defined as `pushforward K ℤ_[p] ℤ_[p] (PadicMeasure.mulCM p (p : ℤ_[p]))`.
- Hypotheses: none beyond globals.
- Uses from project: [`pushforward`, `MeasureR`, `PadicMeasure.mulCM`]
- Used by: `psi_phi`, `phi_psi`, `res_units_eq`, `phi_apply_powCM`, `isSupportedOn_units_iff_psi_eq_zero`, `psi_phi_mul`
- Visibility: public
- Lines: 149–150 (def, no proof)
- Notes: none

### def psi
- Type: `(μ : MeasureR K ℤ_[p]) : MeasureR K ℤ_[p]` (a bundled measure / continuous linear functional)
- What: The operator `ψ` (RJW §3.5.5): `(ψμ)(f) = μ(1_{pℤ_p} · (f ∘ shiftDiv))`, using the coefficient-free digit shift `PadicMeasure.shiftDiv` of the `ℤ_p`-layer.
- How: Provides `toFun` plus additivity (`map_add'` via `ContinuousMap.add_comp`, `mul_add`) and `R`-linearity (`map_smul'` via `ContinuousMap.smul_comp`, `mul_smul_comm`).
- Hypotheses: `μ` a measure.
- Uses from project: [`MeasureR`, `charFnCM`, `PadicMeasure.isClopen_pZp`, `PadicMeasure.shiftDiv`]
- Used by: `psi_phi`, `phi_psi`, `res_units_eq`, `psi_sub`, `psi_add`, `psi_smul`, `psi_zero`, `psi_sum`, `psi_dirac_zero`, `isSupportedOn_units_iff_psi_eq_zero`, `psi_dirac_of_isUnit`, `psi_phi_mul`
- Visibility: public
- Lines: 154–160 (def with field proofs, ~7 lines total)
- Notes: none

### theorem psi_phi
- Type: `(μ : MeasureR K ℤ_[p]) : psi p K (phi p K μ) = μ`
- What: `ψ ∘ φ = id` (RJW TeX 1149–1150).
- How: `LinearMap.ext` on test functions; unfold definitionally to `μ` of a composed map; reduce to a `ContinuousMap.ext` pointwise statement using `PadicMeasure.shiftDiv_mul` and the membership `PadicMeasure.mem_pZp_of_mul` (so `p·x ∈ pℤ_p` makes the indicator `1`).
- Hypotheses: `μ` a measure.
- Uses from project: [`psi`, `phi`, `MeasureR`, `PadicMeasure.shiftDiv`, `PadicMeasure.mulCM`, `charFnCM`, `PadicMeasure.shiftDiv_mul`, `PadicMeasure.mem_pZp_of_mul`]
- Used by: `isSupportedOn_units_iff_psi_eq_zero`
- Visibility: public (`@[simp]`)
- Lines: 167–177 (proof: ~11 lines); hinges on `PadicMeasure.mem_pZp_of_mul`, `PadicMeasure.shiftDiv_mul`
- Notes: `omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K]`

### theorem phi_psi
- Type: `(μ : MeasureR K ℤ_[p]) : phi p K (psi p K μ) = res p K (PadicMeasure.isClopen_pZp p) μ`
- What: `φ ∘ ψ = Res_{pℤ_p}` (RJW TeX 1149–1151).
- How: `LinearMap.ext` on test functions; unfold both sides to `μ`-applications; reduce to pointwise `ContinuousMap.ext`, split on `‖x‖ < 1`: on `pℤ_p` use `PadicMeasure.mul_shiftDiv_of_mem`, off it the indicator is `0`.
- Hypotheses: `μ` a measure.
- Uses from project: [`phi`, `psi`, `res`, `MeasureR`, `PadicMeasure.isClopen_pZp`, `PadicMeasure.mulCM`, `charFnCM`, `PadicMeasure.mul_shiftDiv_of_mem`]
- Used by: `res_units_eq`, `isSupportedOn_units_iff_psi_eq_zero` (indirectly via `res_units_eq`)
- Visibility: public
- Lines: 181–193 (proof: ~13 lines); hinges on `PadicMeasure.mul_shiftDiv_of_mem`
- Notes: `omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K]`

### theorem res_units_eq
- Type: `(μ : MeasureR K ℤ_[p]) : res p K (PadicMeasure.isClopen_units p) μ = μ - phi p K (psi p K μ)`
- What: `Res_{ℤ_p^×} = 1 − φ∘ψ` (RJW Eq 3.10).
- How: Rewrite RHS via `phi_psi` (so the subtracted term is `Res_{pℤ_p}`); `LinearMap.ext`, reduce to `μ(1_{ℤ_p^×}·f) = μ(f) − μ(1_{pℤ_p}·f)`; combine the two indicators via `add_mul` and case split on `‖x‖ < 1`, using `PadicInt.isUnit_iff` to identify units with `‖x‖ = 1` and the complementary indicator memberships.
- Hypotheses: `μ` a measure.
- Uses from project: [`res`, `phi`, `psi`, `MeasureR`, `PadicMeasure.isClopen_units`, `phi_psi`, `charFnCM`]
- Used by: `isSupportedOn_units_iff_psi_eq_zero`
- Visibility: public
- Lines: 197–218 (proof: ~22 lines); hinges on `phi_psi`, `PadicInt.isUnit_iff`
- Notes: `omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K]`

### lemma phi_apply_powCM
- Type: `(μ : MeasureR K ℤ_[p]) (k : ℕ) : phi p K μ (powCM p K k) = algebraMap ℤ_[p] (integerRing K) ((p:ℤ_[p])^k) * μ (powCM p K k)`
- What: The `φ`-scaling of moments: `∫ x^k d(φμ) = p^k · ∫ x^k dμ` (the `R`-widening of the §4 `phi_apply_powCM`).
- How: Unfold `φμ` as pushforward, so `phi μ (powCM k) = μ((powCM k) ∘ mulCM p)`; show pointwise `(powCM k) ∘ (mul by p) = algebraMap(p^k) • powCM k` (via `mul_pow`), then `map_smul` / `smul_eq_mul`.
- Hypotheses: `μ` a measure; `k : ℕ`.
- Uses from project: [`phi`, `MeasureR`, `powCM`, `PadicMeasure.mulCM`]
- Used by: unused in file
- Visibility: public
- Lines: 223–232 (proof: ~10 lines)
- Notes: `omit [CompleteSpace K]`

### lemma psi_sub
- Type: `(μ ν : MeasureR K ℤ_[p]) : psi p K (μ - ν) = psi p K μ - psi p K ν`
- What: `ψ` commutes with subtraction of measures.
- How: `LinearMap.ext` + `LinearMap.sub_apply` (each measure is a linear map, and `psi` of a difference applied to `f` is the difference of applications).
- Hypotheses: `μ`, `ν` measures.
- Uses from project: [`psi`, `MeasureR`]
- Used by: `isSupportedOn_units_iff_psi_eq_zero`
- Visibility: public
- Lines: 235–237 (proof: 1-line term)
- Notes: `omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K]`

### lemma psi_add
- Type: `(μ ν : MeasureR K ℤ_[p]) : psi p K (μ + ν) = psi p K μ + psi p K ν`
- What: `ψ` commutes with addition of measures.
- How: `LinearMap.ext` + `LinearMap.add_apply`.
- Hypotheses: `μ`, `ν` measures.
- Uses from project: [`psi`, `MeasureR`]
- Used by: `psi_sum`
- Visibility: public
- Lines: 240–242 (proof: 1-line term)
- Notes: `omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K]`

### lemma psi_smul
- Type: `(r : integerRing K) (μ : MeasureR K ℤ_[p]) : psi p K (r • μ) = r • psi p K μ`
- What: `ψ` is `R`-homogeneous (commutes with scalar multiplication).
- How: `LinearMap.ext` + `LinearMap.smul_apply`.
- Hypotheses: `r ∈ R`; `μ` a measure.
- Uses from project: [`psi`, `MeasureR`]
- Used by: unused in file
- Visibility: public
- Lines: 245–247 (proof: 1-line term)
- Notes: `omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K]`

### lemma psi_zero
- Type: `: psi p K (0 : MeasureR K ℤ_[p]) = 0`
- What: `ψ` sends the zero measure to zero.
- How: `LinearMap.ext` with `rfl` on each test function.
- Hypotheses: none beyond globals.
- Uses from project: [`psi`, `MeasureR`]
- Used by: `psi_sum`
- Visibility: public
- Lines: 250–251 (proof: 1-line term)
- Notes: `omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K]`

### lemma psi_sum
- Type: `{ι : Type*} (s : Finset ι) (μ : ι → MeasureR K ℤ_[p]) : psi p K (∑ i ∈ s, μ i) = ∑ i ∈ s, psi p K (μ i)`
- What: `ψ` commutes with finite sums of measures.
- How: `Finset.induction_on`: empty case via `psi_zero`; insert case via `Finset.sum_insert` and `psi_add`.
- Hypotheses: `s` a finite index set; `μ` a family of measures.
- Uses from project: [`psi`, `MeasureR`, `psi_zero`, `psi_add`]
- Used by: unused in file
- Visibility: public
- Lines: 254–259 (proof: ~4 lines)
- Notes: `omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K]`; `classical`

### lemma psi_dirac_zero
- Type: `: psi p K (dirac K ℤ_[p] 0) = dirac K ℤ_[p] 0`
- What: `ψ(δ_0) = δ_0` — the Dirac measure at `0` is fixed by `ψ`.
- How: `LinearMap.ext`; unfold both Diracs via `dirac_apply`; use `0 ∈ pℤ_p` so the indicator is `1`, and `shiftDiv p 0 = 0` (from `PadicMeasure.shiftDiv_mul`) so `f` is evaluated at `0`.
- Hypotheses: none beyond globals.
- Uses from project: [`psi`, `dirac`, `charFnCM`, `PadicMeasure.isClopen_pZp`, `PadicMeasure.shiftDiv`, `dirac_apply`, `PadicMeasure.shiftDiv_mul`]
- Used by: unused in file
- Visibility: public
- Lines: 263–272 (proof: ~10 lines)
- Notes: `omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K]`

### theorem isSupportedOn_units_iff_psi_eq_zero
- Type: `(μ : MeasureR K ℤ_[p]) : IsSupportedOn p K (PadicMeasure.isClopen_units p) μ ↔ psi p K μ = 0`
- What: **RJW Cor 3.32** over `R`: `μ` is supported on `ℤ_p^×` iff `ψμ = 0`.
- How: Unfold `IsSupportedOn`. Forward: apply `psi` to `Res_{ℤ_p^×} μ = μ`, rewrite with `res_units_eq`, `psi_sub`, `psi_phi`, `sub_self`. Backward: from `ψμ = 0`, `res_units_eq` gives `μ − φ(ψμ) = μ − 0`, hence `Res_{ℤ_p^×}μ = μ`.
- Hypotheses: `μ` a measure.
- Uses from project: [`IsSupportedOn`, `PadicMeasure.isClopen_units`, `psi`, `MeasureR`, `res_units_eq`, `psi_sub`, `psi_phi`, `phi`]
- Used by: `psi_dirac_of_isUnit`
- Visibility: public
- Lines: 276–285 (proof: ~10 lines); hinges on `res_units_eq`, `psi_phi`
- Notes: none

### lemma psi_dirac_of_isUnit
- Type: `{u : ℤ_[p]} (hu : IsUnit u) : psi p K (dirac K ℤ_[p] u) = 0`
- What: `ψ(δ_u) = 0` for a unit `u` — a Dirac at a unit is supported on `ℤ_p^×` (instance of Cor 3.32).
- How: Rewrite goal via `← isSupportedOn_units_iff_psi_eq_zero` and unfold `IsSupportedOn`; on test functions reduce both sides through `dirac_apply`, using `Set.indicator_of_mem` since `u` is a unit makes the `ℤ_p^×`-indicator `1`.
- Hypotheses: `u` a unit of `ℤ_[p]`.
- Uses from project: [`psi`, `dirac`, `isSupportedOn_units_iff_psi_eq_zero`, `IsSupportedOn`, `charFnCM`, `PadicMeasure.isClopen_units`, `dirac_apply`]
- Used by: unused in file
- Visibility: public
- Lines: 289–297 (proof: ~9 lines)
- Notes: none

### theorem psi_phi_mul
- Type: `(ν μ : MeasureR K ℤ_[p]) : psi p K (phi p K ν * μ) = ν * psi p K μ`
- What: **The projection formula** `ψ(φ(ν)·μ) = ν·ψ(μ)` (cleared form of RJW's trace identity Eq. (3.12); used in §5.2's ξ-free route for `ψ(μ_η) = η(p)μ_η`, decomposition L5.2.4).
- How: Test-function proof routed through the convolution formula. After unfolding `psi` and the product (`mul_apply`), the goal becomes equality of two `ν`-applications of `convInner`; reduce by `congr 1` + `ContinuousMap.ext` (in inner variable `x`, then `y`) so both sides integrate `y ↦ 1_{pℤ_p}(y)·f(x + y/p)` against `μ`. Case split on `‖y‖ < 1`: when small, use ultrametric `norm_add_le_max` to show `p·x + y ∈ pℤ_p`, then `mul_shiftDiv_of_mem` and `shiftDiv_mul` to rewrite the argument as `p·(x + shiftDiv y)`; when large, both indicators vanish (using `norm_add_eq_max_of_norm_ne_norm`).
- Hypotheses: `ν`, `μ` measures.
- Uses from project: [`psi`, `phi`, `MeasureR`, `mul_apply`, `convInner`, `convInner_apply`, `charFnCM`, `PadicMeasure.isClopen_pZp`, `PadicMeasure.shiftDiv`, `PadicMeasure.mulCM`, `PadicMeasure.mem_pZp_of_mul`, `PadicMeasure.mul_shiftDiv_of_mem`, `PadicMeasure.shiftDiv_mul`]
- Used by: unused in file
- Visibility: public
- Lines: 304–342 (proof: ~38 lines); hinges on `convInner_apply`, `PadicMeasure.mul_shiftDiv_of_mem`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`
- Notes: **long(30-50)**; `omit` not present (full instance set in scope)

---

## File Summary

- **Total declarations: 23** — defs: 8 (`cmul`, `del`, `powCM`, `res`, `IsSupportedOn`, `sigma`, `phi`, `psi`); lemmas+theorems: 15 (`cmul_apply`, `coeff_del`, `mahlerTransform_cmul_X`, `powCM_apply`, `apply_powCM`, `psi_phi`, `phi_psi`, `res_units_eq`, `phi_apply_powCM`, `psi_sub`, `psi_add`, `psi_smul`, `psi_zero`, `psi_sum`, `psi_dirac_zero`, `isSupportedOn_units_iff_psi_eq_zero`, `psi_dirac_of_isUnit`, `psi_phi_mul` — note 18 theorem/lemma items counted, see below); instances: 0; structures/classes: 0.
  - (Recount: 8 defs + 15 lemmas/theorems = 23 declarations. The 15 lemmas/theorems are: `cmul_apply`, `coeff_del`, `mahlerTransform_cmul_X`, `powCM_apply`, `apply_powCM`, `psi_phi`, `phi_psi`, `res_units_eq`, `phi_apply_powCM`, `psi_sub`, `psi_add`, `psi_smul`, `psi_zero`, `psi_sum`, `psi_dirac_zero`, `isSupportedOn_units_iff_psi_eq_zero`, `psi_dirac_of_isUnit`, `psi_phi_mul`. That is 18 — total declarations = 8 + 18 = **26**.)
- **Total declarations (final): 26** — defs: 8; lemmas+theorems: 18; instances: 0.
- **Key API (used by ≥3 in this file):**
  - `cmul` — used by `cmul_apply`, `mahlerTransform_cmul_X`, `apply_powCM`, `res` (4).
  - `del` — used by `coeff_del`, `mahlerTransform_cmul_X`, `apply_powCM` (3).
  - `powCM` — used by `powCM_apply`, `apply_powCM`, `phi_apply_powCM` (3).
  - `res` — used by `IsSupportedOn`, `phi_psi`, `res_units_eq`, `isSupportedOn_units_iff_psi_eq_zero` (4).
  - `phi` — used by `psi_phi`, `phi_psi`, `res_units_eq`, `phi_apply_powCM`, `isSupportedOn_units_iff_psi_eq_zero`, `psi_phi_mul` (6).
  - `psi` — used by 12 downstream decls (the central operator of the file).
- **Unused in file (leaf API, likely consumed elsewhere in project):** `apply_powCM`, `sigma`, `phi_apply_powCM`, `psi_smul`, `psi_sum`, `psi_dirac_zero`, `psi_dirac_of_isUnit`, `psi_phi_mul`.
- **Declarations with `sorry`: none.**
- **`set_option`: none.**
- **TODO / admit: none.**
- **Proofs >50 lines: none (0).**
- **Proofs 30–50 lines (long): 1** — `psi_phi_mul` (~38 lines, lines 304–342).
- **Other notable proofs (20–30 lines):** `res_units_eq` (~22 lines).
- **`omit` usage:** most lemmas drop `[CompleteSpace K]` and several also drop `[NormedAlgebra ℚ_[p] K]` to widen applicability; `psi_phi_mul` keeps the full instance set.
- **1 private declaration:** `coeff_del`.

# Inventory: PadicLFunctions/MeasureR/UnitsRing.lean

File-level context: The Iwasawa algebra `Λ_R(ℤ_p^×)` of the units over the integer ring `R := integerRing K` of an ultrametric complete normed field `K` over `ℚ_[p]`. RJW Eq 3.11 / Rem 3.33: convolution ring (commutativity via Fubini, associativity by triple-integral), Dirac multiplicativity `[u]·[v] = [uv]`, and the degree/augmentation map. Whole file is in `noncomputable section`.

Module-wide variables: `(p : ℕ) [hp : Fact p.Prime]`; `(K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]`.

---

### def unitsConv
- Type: `unitsConv (μ ν : MeasureR K ℤ_[p]ˣ) : MeasureR K ℤ_[p]ˣ`
- What: The convolution of two `R`-valued measures on `ℤ_p^×`, defined on a test function `f` by `∫ f d(μ⋆ν) = ∫∫ f(xy) dν(y) dμ(x)` (RJW Eq 3.11, TeX 1173–1175); the resulting object is again a `MeasureR` (a continuous-linear functional on `C(ℤ_p^×, R)`).
- How: Builds the `MeasureR` bundled linear map directly: `toFun f := μ (innerInt K ν (f.comp (PadicMeasure.unitsMulCM₂ p)))`, composing `f` with the two-variable multiplication map `unitsMulCM₂` and taking the inner integral over `ν` before integrating over `μ`. Additivity uses `ContinuousMap.add_comp` + `innerInt_add` + `map_add`; smul-compatibility uses `ContinuousMap.smul_comp` + `innerInt_smul` + `map_smul`.
- Hypotheses: `μ, ν` measures (continuous linear functionals) on `C(ℤ_p^×, R)`; ambient `K` ultrametric complete normed `ℚ_p`-algebra.
- Uses from project: `MeasureR`, `innerInt`, `PadicMeasure.unitsMulCM₂`, `innerInt_add`, `innerInt_smul`
- Used by: `Mul` instance, `units_mul_def`, `units_mul_apply` (indirectly via the `Mul` instance), `CommRing` instance (`mul_assoc`)
- Visibility: public
- Lines: 31–36; proof length: ~2 lines (two field-proof tactics)
- Notes: none

### instance Mul (MeasureR K ℤ_[p]ˣ)
- Type: `instance : Mul (MeasureR K ℤ_[p]ˣ)`
- What: Equips `MeasureR K ℤ_[p]ˣ` with multiplication given by convolution.
- How: `⟨unitsConv p K⟩`.
- Hypotheses: ambient module variables.
- Uses from project: `unitsConv`, `MeasureR`
- Used by: `One` instance context, `units_mul_def`, `units_mul_apply`, `CommRing` instance, `units_dirac_mul_dirac`, `deg`
- Visibility: public
- Lines: 38; proof length: 0 (term)
- Notes: none

### instance One (MeasureR K ℤ_[p]ˣ)
- Type: `instance : One (MeasureR K ℤ_[p]ˣ)`
- What: The multiplicative identity of the convolution ring is the Dirac measure at `1 ∈ ℤ_p^×`.
- How: `⟨dirac K ℤ_[p]ˣ 1⟩`.
- Hypotheses: ambient module variables.
- Uses from project: `MeasureR`, `dirac`
- Used by: `units_one_def`, `CommRing` instance (`one_mul`, `mul_one`)
- Visibility: public
- Lines: 40; proof length: 0 (term)
- Notes: none

### lemma units_mul_def
- Type: `units_mul_def (μ ν : MeasureR K ℤ_[p]ˣ) : μ * ν = unitsConv p K μ ν`
- What: Unfolds the multiplication on `MeasureR K ℤ_[p]ˣ` to the convolution definition `unitsConv`.
- How: `rfl` (definitional, since `Mul` is `⟨unitsConv p K⟩`).
- Hypotheses: two measures `μ, ν`. `omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K]`.
- Uses from project: `MeasureR`, `unitsConv`
- Used by: unused in file
- Visibility: public
- Lines: 44–45; proof length: 0 (rfl)
- Notes: none

### lemma units_mul_apply
- Type: `units_mul_apply (μ ν : MeasureR K ℤ_[p]ˣ) (f : C(ℤ_[p]ˣ, integerRing K)) : (μ * ν) f = μ (innerInt K ν (f.comp (PadicMeasure.unitsMulCM₂ p)))`
- What: Computes the value of the convolution product `μ * ν` on a test function `f` as the iterated integral `μ (innerInt K ν (f ∘ mul))`.
- How: `rfl` (definitional unfolding of the `Mul`/`unitsConv`). `@[simp]`.
- Hypotheses: measures `μ, ν` and a continuous function `f : C(ℤ_p^×, R)`. `omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K]`.
- Uses from project: `MeasureR`, `integerRing`, `innerInt`, `PadicMeasure.unitsMulCM₂`
- Used by: unused in file
- Visibility: public (simp)
- Lines: 47–50; proof length: 0 (rfl)
- Notes: none

### lemma units_one_def
- Type: `units_one_def : (1 : MeasureR K ℤ_[p]ˣ) = dirac K ℤ_[p]ˣ 1`
- What: Identifies the ring identity `1` of `MeasureR K ℤ_[p]ˣ` with the Dirac measure at the unit `1`.
- How: `rfl` (definitional).
- Hypotheses: ambient module variables. `omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K]`.
- Uses from project: `MeasureR`, `dirac`
- Used by: unused in file
- Visibility: public
- Lines: 52–53; proof length: 0 (rfl)
- Notes: none

### instance CommRing (MeasureR K ℤ_[p]ˣ)
- Type: `instance : CommRing (MeasureR K ℤ_[p]ˣ)`
- What: The Iwasawa algebra `Λ_R(ℤ_p^×)` is a commutative ring under convolution (RJW Rem 3.11 + Rem 3.33), supplying all ring axioms (assoc, unit, distributivity, zero, commutativity) on top of the existing additive/`Mul`/`One` structure.
- How: Each field is proved by reducing to equality of `MeasureR` linear maps via `LinearMap.ext fun f`, then `change`-ing to an explicit iterated-integral form and pushing the algebraic identity inward through `congrArg Subtype.val` / `congrArg f`. `mul_assoc` peels three integral layers and ends with `mul_assoc x y z`; `mul_comm` is the Fubini swap via `integral_swap` then `mul_comm x y`; `one_mul`/`mul_one` use `ContinuousMap.curry`/`dirac` with `one_mul`/`mul_one`; distributivity uses `innerInt_measure_add`; `zero_mul`/`mul_zero` use `innerInt_measure_zero`. Hinges crucially on `integral_swap` (Fubini) and on `innerInt_measure_add`/`innerInt_measure_zero` for additivity in the measure slot.
- Hypotheses: ambient ultrametric complete normed `ℚ_p`-algebra `K`; relies on the supplied `Mul`/`One`/additive structure of `MeasureR`.
- Uses from project: `MeasureR`, `innerInt`, `PadicMeasure.unitsMulCM₂`, `unitsConv`, `dirac`, `innerInt_measure_add`, `innerInt_measure_zero`, `integral_swap`
- Used by: `units_dirac_mul_dirac` (ring `*`), `deg` (ring hom out of it)
- Visibility: public
- Lines: 60–116; proof length: ~56 lines
- Notes: OVER-50 (needs /decompose-proof) — the whole instance body spans ~56 lines covering all ten ring-axiom fields; the individual fields are short but bundled. No `sorry`, no `set_option`, no TODO.

### theorem units_dirac_mul_dirac
- Type: `units_dirac_mul_dirac (u v : ℤ_[p]ˣ) : (dirac K ℤ_[p]ˣ u : MeasureR K ℤ_[p]ˣ) * dirac K ℤ_[p]ˣ v = dirac K ℤ_[p]ˣ (u * v)`
- What: Dirac multiplicativity in the convolution ring: the product of point-mass measures at `u` and `v` is the point mass at `u * v` (RJW; `[u]·[v] = [uv]`).
- How: `LinearMap.ext fun _f => rfl` — definitional, because convolving two Diracs evaluates `f` at the product point. `@[simp]`.
- Hypotheses: two units `u, v : ℤ_p^×`. `omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K]`.
- Uses from project: `dirac`, `MeasureR`
- Used by: unused in file
- Visibility: public (simp)
- Lines: 119–125; proof length: 0 (single-line term via ext)
- Notes: none

### def deg
- Type: `deg : MeasureR K ℤ_[p]ˣ →+* integerRing K`
- What: The degree/augmentation ring homomorphism `Λ_R(ℤ_p^×) → R`, `μ ↦ ∫ 1 dμ = μ 1` (RJW Def 3.37, TeX 1245–1253).
- How: Bundles the map `μ ↦ μ 1` as a `RingHom`. `map_one'`, `map_zero'`, `map_add'` are `rfl`. `map_mul'` `change`s the product to the iterated integral, proves the auxiliary identity `innerInt K ν ((1).comp unitsMulCM₂) = ν 1 • 1` by `ext`/`congrArg Subtype.val` + `simp [smul_eq_mul]`, then finishes with `map_smul`, `smul_eq_mul`, `mul_comm`.
- Hypotheses: ambient module variables; measures evaluated at the constant function `1`.
- Uses from project: `MeasureR`, `integerRing`, `innerInt`, `PadicMeasure.unitsMulCM₂`
- Used by: unused in file
- Visibility: public
- Lines: 129–145; proof length: ~11 lines (`map_mul'` field is ~10 lines; rest rfl)
- Notes: none (just under flag thresholds; `map_mul'` hinges on the `ν 1 • 1` rewrite)

---

## File Summary

- Total declarations: 9 — defs: 2 (`unitsConv`, `deg`); lemmas+theorems: 4 (`units_mul_def`, `units_mul_apply`, `units_one_def`, `units_dirac_mul_dirac`); instances: 3 (`Mul`, `One`, `CommRing`).
- Key API (used by ≥3 decls in file): `MeasureR` (used by all 9); `PadicMeasure.unitsMulCM₂` (unitsConv, units_mul_apply, CommRing, deg); `innerInt` (unitsConv, units_mul_apply, CommRing, deg); `dirac` (One, units_one_def, CommRing, units_dirac_mul_dirac); `unitsConv` (Mul, units_mul_def, CommRing). The `Mul` instance is consumed by 5 later decls.
- Unused in file: `units_mul_def`, `units_mul_apply`, `units_one_def`, `units_dirac_mul_dirac`, `deg` (all are exported public API for downstream §5 use, not consumed internally).
- Decls with `sorry`: none.
- `set_option`: none.
- Proofs >50 lines: 1 — `CommRing` instance (~56 lines, bundled ten-field ring-axiom proof; flagged OVER-50 for /decompose-proof).
- Proofs 30–50 lines: 0.

Output path: /Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/.mathlib-quality/overview/inventory/PadicLFunctions_MeasureR_UnitsRing.md

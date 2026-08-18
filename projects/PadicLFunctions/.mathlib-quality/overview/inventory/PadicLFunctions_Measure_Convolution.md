# Inventory: PadicLFunctions/Measure/Convolution.lean

File-level: defines the convolution (Iwasawa-algebra) ring structure on `PadicMeasure p ℤ_[p] = ℳ(ℤ_p, ℤ_p)`, transported from `ℤ_p[[T]]` along the Mahler transform. Implements RJW (arXiv:2309.15692) §3.3, Rem. 3.11, Thm. 3.20, Exx. 3.12/3.16.

Namespace: `PadicMeasure`. All declarations live under `noncomputable section`. Imports `PadicLFunctions.Measure.MahlerTransform`.

---

### instance Mul (PadicMeasure p ℤ_[p])
- Type: `noncomputable instance : Mul (PadicMeasure p ℤ_[p])` (anonymous)
- What: Defines multiplication of two measures on `ℤ_p` by pulling back the power-series product `ℤ_p[[T]]` under the Mahler linear equivalence, i.e. `μ * ν := (mahlerLinearEquiv p).symm (mahlerLinearEquiv p μ * mahlerLinearEquiv p ν)`.
- How: Transport of structure: applies the inverse of `mahlerLinearEquiv` to the product of the two transformed measures. Direct definitional construction (anonymous constructor `⟨…⟩`).
- Hypotheses: `p : ℕ`, `[Fact p.Prime]` (file-level variables).
- Uses from project: `mahlerLinearEquiv`, `PadicMeasure`
- Used by: `mul_def`, `mahlerTransform_mul` (via `mul_def`)
- Visibility: public (scoped instance in namespace `PadicMeasure`)
- Lines: 39–40 (proof: definitional, 1 line)
- Notes: none

### instance One (PadicMeasure p ℤ_[p])
- Type: `noncomputable instance : One (PadicMeasure p ℤ_[p])` = `⟨dirac p 0⟩`
- What: Designates the unit measure to be the Dirac measure `δ_0` at `0`, whose Mahler transform is `(1+T)^0 = 1`.
- How: Anonymous constructor wrapping `dirac p 0`. Definitional.
- Hypotheses: `p : ℕ`, `[Fact p.Prime]`.
- Uses from project: `dirac`, `PadicMeasure`
- Used by: `one_def`, `mahlerTransform_one` (via `one_def`)
- Visibility: public
- Lines: 42–43 (proof: definitional, 1 line)
- Notes: none

### lemma mul_def
- Type: `(μ ν : PadicMeasure p ℤ_[p]) : μ * ν = (mahlerLinearEquiv p).symm (mahlerLinearEquiv p μ * mahlerLinearEquiv p ν)`
- What: Unfolds the definition of measure multiplication to its transport-of-structure formula.
- How: `rfl` — holds by definition of the `Mul` instance.
- Hypotheses: two measures `μ, ν`; `p` prime.
- Uses from project: `mahlerLinearEquiv`, `PadicMeasure` (and the `Mul` instance)
- Used by: `mahlerTransform_mul`
- Visibility: public
- Lines: 45–47 (proof: 1 line, `rfl`)
- Notes: none

### lemma one_def
- Type: `(1 : PadicMeasure p ℤ_[p]) = dirac p 0`
- What: Identifies the ring unit `1` as the Dirac measure at `0`.
- How: `rfl` — definitional from the `One` instance.
- Hypotheses: `p` prime.
- Uses from project: `dirac`, `PadicMeasure`
- Used by: `mahlerTransform_one`
- Visibility: public
- Lines: 49 (proof: 1 line, `rfl`)
- Notes: none

### theorem mahlerTransform_mul
- Type: `@[simp] (μ ν : PadicMeasure p ℤ_[p]) : mahlerTransform p (μ * ν) = mahlerTransform p μ * mahlerTransform p ν`
- What: The Mahler transform is multiplicative: it carries the convolution product of measures to the ordinary product of power series (`𝓐_{μ·ν} = 𝓐_μ · 𝓐_ν`).
- How: Rewrites `mul_def`, then converts `mahlerTransform` to `mahlerLinearEquiv` (`mahlerLinearEquiv_apply`), cancels via `LinearEquiv.apply_symm_apply`, and re-expresses both factors. Pure rewrite chain.
- Hypotheses: two measures; `p` prime.
- Uses from project: `mahlerTransform`, `mul_def`, `mahlerLinearEquiv_apply` (from MahlerTransform), `mahlerLinearEquiv`, `PadicMeasure`
- Used by: `mahlerRingEquiv` (as `map_mul'`), `CommRing` instance, `mul_apply`, `dirac_mul_dirac`
- Visibility: public; `@[simp]`
- Lines: 51–56 (proof: 2 lines)
- Notes: none. Key API (used ≥3 times).

### theorem mahlerTransform_one
- Type: `@[simp] : mahlerTransform p (1 : PadicMeasure p ℤ_[p]) = 1`
- What: The Mahler transform of the ring unit `δ_0` is the power-series `1`.
- How: Rewrites `one_def`, then `mahlerTransform_dirac` to get the binomial series `(1+T)^0`, then `binomialSeries_zero` to collapse it to `1`.
- Hypotheses: `p` prime.
- Uses from project: `mahlerTransform`, `one_def`, `mahlerTransform_dirac` (from MahlerTransform)
- Used by: unused in file (likely used downstream / by simp set)
- Visibility: public; `@[simp]`
- Lines: 58–61 (proof: 1 line)
- Notes: `binomialSeries_zero` is a mathlib lemma, not project.

### theorem mahlerTransform_add
- Type: `@[simp] (μ ν : PadicMeasure p ℤ_[p]) : mahlerTransform p (μ + ν) = mahlerTransform p μ + mahlerTransform p ν`
- What: The Mahler transform is additive over measure addition.
- How: Extensionality on coefficients (`ext n`) followed by `simp` (relies on `mahlerTransform`/coeff simp lemmas from MahlerTransform).
- Hypotheses: two measures; `p` prime.
- Uses from project: `mahlerTransform`, `PadicMeasure`
- Used by: unused in file (simp lemma)
- Visibility: public; `@[simp]`
- Lines: 63–66 (proof: 2 lines)
- Notes: none

### theorem mahlerTransform_zero
- Type: `@[simp] : mahlerTransform p (0 : PadicMeasure p ℤ_[p]) = 0`
- What: The Mahler transform of the zero measure is the zero power series.
- How: `ext n; simp` — coefficientwise, both sides vanish.
- Hypotheses: `p` prime.
- Uses from project: `mahlerTransform`, `PadicMeasure`
- Used by: unused in file (simp lemma)
- Visibility: public; `@[simp]`
- Lines: 68–70 (proof: 2 lines)
- Notes: none

### instance CommRing (PadicMeasure p ℤ_[p])
- Type: `noncomputable instance : CommRing (PadicMeasure p ℤ_[p])` (anonymous, structure with 8 explicit ring-axiom fields)
- What: Equips `PadicMeasure p ℤ_[p]` with the commutative ring structure of the Iwasawa algebra `Λ(ℤ_p) = ℳ(ℤ_p, ℤ_p)`, with all ring laws inherited from `ℤ_p[[T]]` via the Mahler bijection.
- How: Each field (`mul_assoc`, `one_mul`, `mul_one`, `left_distrib`, `right_distrib`, `zero_mul`, `mul_zero`, `mul_comm`) is discharged by `mahlerTransform_injective p (by simp [...])` — the Mahler transform is injective and is a `simp`-driven ring homomorphism (using `mahlerTransform_mul`, `mahlerTransform_add`, `mahlerTransform_one`, etc.), so the corresponding law in `ℤ_p[[T]]` transports back. Hinges on `mahlerTransform_injective` and `mahlerTransform_mul`.
- Hypotheses: `p` prime; relies on `PadicMeasure` already being an additive comm group (from MahlerTransform / Measure base) so only the multiplicative + distributive axioms are supplied.
- Uses from project: `mahlerTransform_injective` (from MahlerTransform), `mahlerTransform_mul`, `mahlerTransform_add`/`_one`/`_zero` (via simp), `PadicMeasure`
- Used by: `mahlerRingEquiv` (needs `≃+*`), `mul_apply`, `dirac_mul_dirac`, and the whole downstream Iwasawa-algebra API
- Visibility: public
- Lines: 72–84 (proof: 8 one-line field proofs, ~9 lines total)
- Notes: none

### def mahlerRingEquiv
- Type: `noncomputable def mahlerRingEquiv : PadicMeasure p ℤ_[p] ≃+* PowerSeries ℤ_[p]`
- What: Upgrades the Mahler linear equivalence to a ring isomorphism `ℳ(ℤ_p, ℤ_p) ≅ ℤ_p[[T]]` (RJW Thm. 3.20), exhibiting the Iwasawa algebra as a power-series ring.
- How: Extends `mahlerLinearEquiv p` (an additive/`ℤ_p`-linear equiv) with `map_mul' := mahlerTransform_mul p`, using record-update syntax `{ mahlerLinearEquiv p with map_mul' := … }`.
- Hypotheses: `p` prime.
- Uses from project: `mahlerLinearEquiv`, `mahlerTransform_mul`, `PadicMeasure`
- Used by: unused in file (headline API for downstream)
- Visibility: public
- Lines: 86–90 (proof: structure literal, ~2 lines)
- Notes: none. Headline result (RJW Thm. 3.20).

### def convInner
- Type: `noncomputable def convInner (ν : PadicMeasure p ℤ_[p]) (f : C(ℤ_[p], ℤ_[p])) : C(ℤ_[p], ℤ_[p])` with `toFun x := ν (f.comp ⟨fun y => x + y, _⟩)`
- What: The inner-convolution integrand `x ↦ ∫ f(x+y) dν(y)`, packaged as a continuous map `ℤ_p → ℤ_p`; this is the function integrated against `μ` in the convolution formula.
- How: `toFun` sends `x` to `ν` applied to the translate `f(x+·)`. Continuity (`continuous_toFun`) is proved by rewriting the family of translates as the curry of the jointly-continuous map `(x,y) ↦ f(x+y)` (`ContinuousMap.curry`), then composing the measure's continuity (`continuous p ν`) with `map_continuous` of the curried map. Hinges on `continuous p ν` and `ContinuousMap.curry`.
- Hypotheses: a measure `ν`; a continuous `f : C(ℤ_p, ℤ_p)`; `p` prime.
- Uses from project: `PadicMeasure`, `continuous` (the continuity-of-measure lemma from the Measure base, used as `continuous p ν`)
- Used by: `convInner_apply`, `mul_apply`
- Visibility: public
- Lines: 92–102 (proof of continuity: ~6 lines)
- Notes: none

### lemma convInner_apply
- Type: `@[simp] (ν : PadicMeasure p ℤ_[p]) (f : C(ℤ_[p], ℤ_[p])) (x : ℤ_[p]) : convInner p ν f x = ν (f.comp ⟨fun y => x + y, _⟩)`
- What: Computes the value of `convInner p ν f` at a point `x` as `ν` applied to the translated function `f(x+·)`.
- How: `rfl` — definitional unfolding of `convInner`.
- Hypotheses: measure `ν`, continuous `f`, point `x`; `p` prime.
- Uses from project: `convInner`, `PadicMeasure`
- Used by: `mul_apply` (in the `key` step)
- Visibility: public; `@[simp]`
- Lines: 104–106 (proof: 1 line, `rfl`)
- Notes: none

### theorem mul_apply
- Type: `(μ ν : PadicMeasure p ℤ_[p]) (f : C(ℤ_[p], ℤ_[p])) : (μ * ν) f = μ (convInner p ν f)`
- What: **The convolution formula** (RJW Rem. 3.11): `∫ φ d(μ*ν) = ∫ (∫ φ(x+y) dν(y)) dμ(x)`; i.e. integrating `f` against the product measure equals integrating, against `μ`, the inner convolution `convInner p ν f`.
- How: Defines the candidate measure `ρ` whose action is `f ↦ μ (convInner p ν f)` (with `map_add'` / `map_smul'` proved via `ContinuousMap.add_comp` / `ContinuousMap.smul_comp` and `congrArg μ`), reduces to `μ * ν = ρ` and then to equality of Mahler transforms via `mahlerTransform_injective`. After `ext n` and `coeff_mul`, the proof checks the identity on the Mahler basis `mahler n`: the key combinatorial input is the Chu–Vandermonde identity `Ring.add_choose_eq` giving `binom(x+y,n) = ∑_{i+j=n} binom(x,i)·binom(y,j)` (lemma `hcomp`), which expands the translate of `mahler n` as a finite sum of scaled Mahler functions; `key` then evaluates `convInner` on this sum, and the coefficients are matched with `coeff_mahlerTransform`. Hinges on `mahlerTransform_injective`, `mahlerTransform_mul`, `coeff_mahlerTransform`, and `Ring.add_choose_eq`.
- Hypotheses: two measures `μ, ν`; a continuous `f`; `p` prime.
- Uses from project: `PadicMeasure`, `convInner`, `convInner_apply`, `mahlerTransform_injective` (from MahlerTransform), `mahlerTransform_mul`, `coeff_mahlerTransform` (from MahlerTransform), `mahler` (Mahler basis; `mahler_apply`)
- Used by: unused in file (headline convolution formula for downstream)
- Visibility: public
- Lines: 108–149 (proof: ~36 lines)
- Notes: long(30-50) — proof body ~36 lines; candidate for /decompose-proof. No sorry / set_option / TODO. Relies on mathlib `Ring.add_choose_eq`, `PowerSeries.coeff_mul`, `ContinuousMap.add_comp`/`smul_comp`.

### theorem dirac_mul_dirac
- Type: `@[simp] (a b : ℤ_[p]) : dirac p a * dirac p b = dirac p (a + b)`
- What: Dirac measures multiply by adding their points: `δ_a * δ_b = δ_{a+b}`, i.e. in Iwasawa-algebra notation `[a]·[b] = [a+b]`.
- How: Applies `mahlerTransform_injective`; then `mahlerTransform_mul` reduces to a product of binomial series, three `mahlerTransform_dirac` rewrites give `(1+T)^a · (1+T)^b`, and `binomialSeries_add` collapses it to `(1+T)^{a+b}`. Hinges on `mahlerTransform_mul` and `binomialSeries_add`.
- Hypotheses: two points `a, b : ℤ_p`; `p` prime.
- Uses from project: `dirac`, `mahlerTransform_injective` (from MahlerTransform), `mahlerTransform_mul`, `mahlerTransform_dirac` (from MahlerTransform)
- Used by: unused in file (simp lemma; group-like API for downstream)
- Visibility: public; `@[simp]`
- Lines: 151–160 (proof: 3 lines)
- Notes: `binomialSeries_add` is a mathlib lemma, not project.

---

## File Summary

**Total declarations: 13** — 2 defs (`mahlerRingEquiv`, `convInner`) / 9 lemmas+theorems (`mul_def`, `one_def`, `mahlerTransform_mul`, `mahlerTransform_one`, `mahlerTransform_add`, `mahlerTransform_zero`, `convInner_apply`, `mul_apply`, `dirac_mul_dirac`) / 3 instances (`Mul`, `One`, `CommRing`). (2 / 9 / 3 = 14 named slots; counting `mul_def`+`one_def` lemmas, the 11 non-instance + reasoning gives 10 def/lemma/thm + 3 instances; canonical count = 13 declarations as listed above.)

**Key API (used by ≥3 in file):**
- `mahlerTransform_mul` — used by `CommRing` instance, `mahlerRingEquiv`, `mul_apply`, `dirac_mul_dirac` (≥4). The central multiplicativity lemma.
- `mahlerTransform_injective` (imported from MahlerTransform, not defined here) — used by `CommRing` (8×), `mul_apply`, `dirac_mul_dirac`.

**Unused in file (downstream/headline API):** `mahlerTransform_one`, `mahlerTransform_add`, `mahlerTransform_zero` (simp lemmas), `mahlerRingEquiv` (RJW Thm. 3.20), `mul_apply` (convolution formula), `dirac_mul_dirac` (simp lemma).

**Declarations with `sorry`: none.**

**set_option: none.** **TODO/admit: none.**

**Proofs > 50 lines (OVER-50): 0.**

**Proofs 30–50 lines: 1** — `mul_apply` (lines 108–149, ~36-line body). Candidate for /decompose-proof (Chu–Vandermonde / Mahler-basis expansion is the natural helper to extract).

**Output path:** `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/.mathlib-quality/overview/inventory/PadicLFunctions_Measure_Convolution.md`

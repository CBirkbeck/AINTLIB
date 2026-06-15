# Inventory: ./HasseWeil/FormalGroupAssoc.lean

**File**: `HasseWeil/FormalGroupAssoc.lean`
**Module**: `HasseWeil` namespace
**Imports**: `HasseWeil.FormalGroup`, `Mathlib.RingTheory.PowerSeries.Basic`
**Topic**: Silverman IV.3 — formal group operations and pullback coefficient properties
**Total declarations**: 21 (7 private, 14 public; 8 defs, 13 lemmas/theorems, 0 instances)

---

## Declarations

### `noncomputable def formalGroupEval`
- **Type**: `(a b : R) (N : ℕ) : R`
- **What**: Truncated evaluation of the formal group law `F(a,b)` to degree `N`, computed as `Σ_{i+j≤N} F_{ij} · aⁱ · bʲ`.
- **How**: Straightforward double finite sum over `Finset.range`; uses `formalGroupLaw_coeff` from `FormalGroup.lean`.
- **Hypotheses**: `R` a commutative ring; no completeness assumption (truncated, not convergent).
- **Uses from project**: `formalGroupLaw_coeff` (from `HasseWeil.FormalGroup`)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 43–45, proof length: definition body (3 lines)
- **Notes**: Not referenced within this file; likely imported by `FormalGroupBridge.lean` or `FormalGroupCorrespondence.lean` (those files import this module).

---

### `noncomputable def formalInverseEval`
- **Type**: `(a : R) (N : ℕ) : R`
- **What**: Truncated evaluation of the formal inverse `i(a)` to degree `N`, as `Σ_{n=0}^{N} c_n · aⁿ`.
- **How**: Single finite sum using `formalInverse_coeff` from `FormalGroup.lean`.
- **Hypotheses**: `R` a commutative ring.
- **Uses from project**: `formalInverse_coeff` (from `HasseWeil.FormalGroup`)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 48–49, definition body (2 lines)
- **Notes**: Not referenced within this file; dead-code candidate at file level.

---

### `private def uconv`
- **Type**: `(f g : ℕ → R) (n : ℕ) : R`
- **What**: Convolution of two coefficient sequences: `(f * g)_n = Σ_{i=0}^{n} f(i) · g(n−i)`.
- **How**: Plain `Finset.range (n+1)` sum.
- **Hypotheses**: None beyond `R` commutative ring.
- **Uses from project**: none
- **Used by**: `univPow` (line 68), `uconv_zero` (line 134), `uconv_one` (line 137), `univPow_zero_eq` (line 146)
- **Visibility**: private
- **Lines**: 61–63, definition body (2 lines)
- **Notes**: Standard discrete convolution; no mathlib duplication check needed (it's private scaffolding).

---

### `private def univPow`
- **Type**: `(s : ℕ → R) : ℕ → ℕ → R`  
  (first arg = power index `i`, second arg = coefficient index `n`)
- **What**: Coefficient sequence of the `i`-th power of the power series with coefficient sequence `s`: `(s^0)_n = [n=0]`, `(s^1)_n = s n`, `(s^{i+2})_n = (s * s^{i+1})_n` by convolution.
- **How**: Structural recursion with `uconv` for the inductive step.
- **Hypotheses**: None.
- **Uses from project**: `uconv`
- **Used by**: `compFGL` (line 76), `univPow_zero_eq` (line 141–147), `univPow_one_eq_zero` (line 150–156), `bivarComp` (line 167), `comp_coeff_one` (line 214)
- **Visibility**: private
- **Lines**: 65–68, definition body (4 lines)
- **Notes**: Key internal helper; referenced by 5 other declarations (the most-used private def).

---

### `private noncomputable def compFGL`
- **Type**: `(s : ℕ → R) (n : ℕ) : R`
- **What**: Coefficient of `T^n` in the composition `F(s(T), T)` where `s` is a power series with `s(0)=0`; used to define `[m+1] = F([m], T)` recursively.
- **How**: Double sum over formal group law coefficients `F_{i,j}` weighted by `univPow s i` evaluated at degree `n−j`.
- **Hypotheses**: `s 0 = 0` assumed implicitly (needed for convergence of the composition at finite degree).
- **Uses from project**: `formalGroupLaw_coeff` (from `HasseWeil.FormalGroup`), `univPow`
- **Used by**: `formalMulByNat_coeff` (line 84)
- **Visibility**: private
- **Lines**: 71–77, definition body (7 lines)
- **Notes**: Implements the recursion step `[m+1] = F([m], \mathrm{id})` at the coefficient level.

---

### `private noncomputable def formalMulByNat_coeff`
- **Type**: `: ℕ → ℕ → R`  
  (first arg = multiplier `m : ℕ`, second = coefficient index `n : ℕ`)
- **What**: Coefficients of the multiplication-by-`m` formal group series `[m](T)`, defined by well-founded recursion: `[0]=0`, `[1]=T`, `[m+1]=F([m],T)`.
- **How**: Uses `WellFoundedRelation.wf.fix` for the recursion, delegating to `compFGL` for the inductive step.
- **Hypotheses**: None beyond `R` commutative ring.
- **Uses from project**: `compFGL`
- **Used by**: `formalMulByInt_coeff` (line 90)
- **Visibility**: private
- **Lines**: 80–85, definition body (6 lines)
- **Notes**: The sign correction for negative `m` is handled separately in `formalMulByInt_coeff`; comment in body acknowledges the simplification that `formalInverse_coeff` composition is skipped for `n ≥ 2`.

---

### `noncomputable def formalMulByInt_coeff`
- **Type**: `(m : ℤ) (n : ℕ) : R`
- **What**: Coefficients of the multiplication-by-`m` formal group endomorphism `[m](T)`: constant term 0, linear term `m`, higher terms via `formalMulByNat_coeff W m.natAbs`.
- **How**: Case split on `n = 0`, `n = 1`, and `n ≥ 2`; uses `formalMulByNat_coeff`.
- **Hypotheses**: None.
- **Uses from project**: `formalMulByNat_coeff`
- **Used by**: `formalMulByInt` (line 99), `pullbackCoeff_mulByInt` (line 110)
- **Visibility**: public
- **Lines**: 87–96, definition body (10 lines, including comment)
- **Notes**: The comment explicitly flags the simplification that `formalInverse_coeff` is not composed for `n ≥ 2, m < 0`; this is mathematically incorrect for higher coefficients when `m < 0`. Potential correctness gap for the `n ≥ 2, m < 0` case.

---

### `noncomputable def formalMulByInt`
- **Type**: `(m : ℤ) : PowerSeries R`
- **What**: The multiplication-by-`m` power series `[m](T) ∈ R[[T]]`, packaged as a `PowerSeries`.
- **How**: `PowerSeries.mk` applied to `formalMulByInt_coeff W m`.
- **Hypotheses**: None.
- **Uses from project**: `formalMulByInt_coeff`
- **Used by**: `pullbackCoeff_mulByInt` (line 108)
- **Visibility**: public
- **Lines**: 98–99, definition body (2 lines)
- **Notes**: Referenced by `FormalGroupCorrespondence.lean`.

---

### `theorem pullbackCoeff_mulByInt`
- **Type**: `(m : ℤ) : PowerSeries.coeff 1 (formalMulByInt W m) = (m : R)`
- **What**: The linear coefficient of `[m](T)` equals `m` in `R`.
- **How**: `simp` unfolds `formalMulByInt` via `PowerSeries.coeff_mk`, then unfolds `formalMulByInt_coeff` which returns `m` by definition at `n = 1`.
- **Hypotheses**: None.
- **Uses from project**: `formalMulByInt`, `formalMulByInt_coeff`
- **Used by**: unused in file (exported for downstream use)
- **Visibility**: public
- **Lines**: 107–111, proof length: 5 lines
- **Notes**: Corresponds to Silverman Prop. IV.2.3a. No sorry. Clean.

---

### `theorem formalGroupLaw_coeff_right_unit`
- **Type**: `(n : ℕ) : formalGroupLaw_coeff W (Finsupp.single 0 n) = if n = 1 then 1 else 0`
- **What**: Proves `F(X, 0) = X` at the coefficient level: the coefficient indexed by `(n, 0)` is `[n=1]`.
- **How**: Unfolds `formalGroupLaw_coeff` and uses `simp` with `Finsupp.single_apply` and `Fin` decidability, then `split_ifs`.
- **Hypotheses**: None.
- **Uses from project**: `formalGroupLaw_coeff` (from `HasseWeil.FormalGroup`)
- **Used by**: `pullbackCoeff_add` (line 186) via `fgl_coeff`
- **Visibility**: public
- **Lines**: 114–122, proof length: 9 lines
- **Notes**: Establishes the right-unit law for the formal group law coefficients.

---

### `theorem formalGroupLaw_coeff_left_unit`
- **Type**: `(n : ℕ) : formalGroupLaw_coeff W (Finsupp.single 1 n) = if n = 1 then 1 else 0`
- **What**: Proves `F(0, Y) = Y` at the coefficient level: the coefficient indexed by `(0, n)` is `[n=1]`.
- **How**: Same `unfold` + `simp` approach as `formalGroupLaw_coeff_right_unit`.
- **Hypotheses**: None.
- **Uses from project**: `formalGroupLaw_coeff` (from `HasseWeil.FormalGroup`)
- **Used by**: `pullbackCoeff_add` (line 189) via `fgl_coeff`
- **Visibility**: public
- **Lines**: 125–131, proof length: 7 lines
- **Notes**: Proof appears incomplete — the proof block ends without a closing `<;> simp_all` or similar (the `formalGroupLaw_coeff_right_unit` proof needed `split_ifs <;> simp_all`; this one stops after `simp only`). May be missing a tactic or intentionally closed by `simp only` achieving `rfl`.

---

### `private theorem uconv_zero`
- **Type**: `(f g : ℕ → R) : uconv f g 0 = f 0 * g 0`
- **What**: The zero-index convolution is just the product of the zeroth coefficients.
- **How**: `simp [uconv]` unfolds and simplifies the single-term sum.
- **Hypotheses**: None.
- **Uses from project**: `uconv`
- **Used by**: `univPow_zero_eq` (line 147)
- **Visibility**: private
- **Lines**: 134–135, proof length: 2 lines
- **Notes**: trivial helper.

---

### `private theorem uconv_one`
- **Type**: `(f g : ℕ → R) : uconv f g 1 = f 0 * g 1 + f 1 * g 0`
- **What**: The index-1 convolution equals `f(0)g(1) + f(1)g(0)`.
- **How**: `simp [uconv, Finset.sum_range_succ]` unpacks the two-term sum.
- **Hypotheses**: None.
- **Uses from project**: `uconv`
- **Used by**: `univPow_one_eq_zero` (line 155)
- **Visibility**: private
- **Lines**: 137–139, proof length: 3 lines
- **Notes**: trivial helper.

---

### `private theorem univPow_zero_eq`
- **Type**: `(s : ℕ → R) (hs0 : s 0 = 0) (i : ℕ) (hi : 1 ≤ i) : univPow s i 0 = 0`
- **What**: If `s(0) = 0`, then every power `s^i` (for `i ≥ 1`) has zero constant term.
- **How**: Induction via `match i` with base `i=1` and step `i+2`; step uses `uconv_zero` and `hs0` to push the zero through convolution.
- **Hypotheses**: `s 0 = 0`, `i ≥ 1`.
- **Uses from project**: `uconv_zero`, `univPow`
- **Used by**: `univPow_one_eq_zero` (line 156)
- **Visibility**: private
- **Lines**: 141–147, proof length: 7 lines
- **Notes**: Helper for the linear-coefficient computation.

---

### `theorem univPow_one_eq_zero`
- **Type**: `(s : ℕ → R) (hs0 : s 0 = 0) (i : ℕ) (hi : 2 ≤ i) : univPow s i 1 = 0`
- **What**: If `s(0) = 0`, then for powers `i ≥ 2`, the linear coefficient of `s^i` is zero; this captures that `O(T)^i = O(T^i)` vanishes at degree 1 for `i ≥ 2`.
- **How**: `match` on `i+2`; unfolds to `uconv s (univPow s (i+1)) 1`, applies `uconv_one`, uses `hs0` and `univPow_zero_eq` to kill both terms.
- **Hypotheses**: `s 0 = 0`, `i ≥ 2`.
- **Uses from project**: `uconv_one`, `univPow_zero_eq`, `univPow`
- **Used by**: unused in file (but referenced in comment of `pullbackCoeff_comp`)
- **Visibility**: public
- **Lines**: 150–156, proof length: 7 lines
- **Notes**: Key lemma supporting the chain-rule argument; exported publicly.

---

### `private noncomputable def bivarComp`
- **Type**: `(F : ℕ → ℕ → R) (f g : ℕ → R) (n : ℕ) : R`
- **What**: The `n`-th coefficient of the bivariate composition `F(f(T), g(T))` for coefficient sequences `F`, `f`, `g`.
- **How**: Triple sum `Σ_{k,i,j}` with a guard `i + j ≤ n`, using `univPow`.
- **Hypotheses**: None explicitly; intended for `f 0 = g 0 = 0`.
- **Uses from project**: `univPow`
- **Used by**: unused in file (defined but never used internally)
- **Visibility**: private
- **Lines**: 161–168, definition body (8 lines)
- **Notes**: Dead-code candidate within this file; appears to be scaffolding for a planned `pullbackCoeff_add` proof that was ultimately proved more directly.

---

### `private noncomputable def fgl_coeff`
- **Type**: `(i j : ℕ) : R`
- **What**: The `(i,j)` coefficient of the formal group law, as a function of two natural number arguments (unwrapping the `Finsupp` representation).
- **How**: `formalGroupLaw_coeff W (Finsupp.single 0 i + Finsupp.single 1 j)`.
- **Hypotheses**: None.
- **Uses from project**: `formalGroupLaw_coeff` (from `HasseWeil.FormalGroup`)
- **Used by**: `pullbackCoeff_add` (lines 184, 185, 188)
- **Visibility**: private
- **Lines**: 171–172, definition body (2 lines)
- **Notes**: Thin notational alias; used 3 times in `pullbackCoeff_add`.

---

### `theorem pullbackCoeff_add`
- **Type**: `(f g : ℕ → R) (hf0 : f 0 = 0) (hg0 : g 0 = 0) : fgl_coeff W 1 0 * f 1 + fgl_coeff W 0 1 * g 1 = f 1 + g 1`
- **What**: The linear coefficient of `F(f(T), g(T))` is `f₁ + g₁`; equivalently, `F_{1,0} = F_{0,1} = 1`, so the sum of linear coefficients is additive (Silverman III.5.6, additivity of the pullback coefficient).
- **How**: Two `rw` steps reduce `fgl_coeff W 1 0` and `fgl_coeff W 0 1` to `1` using `formalGroupLaw_coeff_right_unit` and `formalGroupLaw_coeff_left_unit` respectively; then `ring`.
- **Hypotheses**: `f 0 = 0`, `g 0 = 0` (hypotheses present but not used in the proof, since the result is purely about the formal group law coefficients).
- **Uses from project**: `fgl_coeff`, `formalGroupLaw_coeff_right_unit`, `formalGroupLaw_coeff_left_unit`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 180–191, proof length: 12 lines
- **Notes**: The stated conclusion is somewhat weaker than described — it proves the coefficient identity rather than the full composition statement; `hf0`/`hg0` are not used in the proof body (dead hypotheses).

---

### `theorem pullbackCoeff_comp`
- **Type**: `(f g : ℕ → R) (hf0 : f 0 = 0) (hg0 : g 0 = 0) : f 1 * g 1 = f 1 * g 1`
- **What**: States that the linear coefficient of `f(g(T))` equals `f₁ · g₁`; the proof is `rfl`.
- **How**: The conclusion is literally `rfl` — the statement is a tautology as stated.
- **Hypotheses**: `f 0 = 0`, `g 0 = 0` (unused).
- **Uses from project**: none
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 202–209, proof length: 8 lines (including multi-line comment)
- **Notes**: This is a stub/placeholder — the proof is `rfl` on `f 1 * g 1 = f 1 * g 1`. The actual content (that composition has this linear coefficient) is in the comments, not proven. Dead-code / parked declaration.

---

### `theorem comp_coeff_one`
- **Type**: `(f g : ℕ → R) (hf0 : f 0 = 0) (hg0 : g 0 = 0) : (Finset.range 2).sum (fun n => f n * univPow g n 1) = f 1 * g 1`
- **What**: The degree-1 coefficient of the formal composition `Σ_n f_n · g^n` equals `f₁ · g₁`, since `(g^0)_1 = 0` and `(g^n)_1 = 0` for `n ≥ 2` (uses `hg0`).
- **How**: `simp [Finset.sum_range_succ, hf0, univPow]` unfolds the two-term sum and simplifies.
- **Hypotheses**: `f 0 = 0`, `g 0 = 0`.
- **Uses from project**: `univPow`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 212–215, proof length: 4 lines
- **Notes**: Packaged version of the chain-rule linear-coefficient argument.

---

### `theorem dual_additivity_algebraic`
- **Type**: `{K : Type*} [Field K] (a b d_a d_b d_ab : K) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) (hquad : d_ab * a * b = (d_a + d_b) * a * b + a ^ 2 * d_b + b ^ 2 * d_a) : d_ab * a * b = (a + b) * (d_a * b + d_b * a)`
- **What**: A pure field-algebra identity: given the quadratic form relation `d_{a+b} · ab = (d_a + d_b)·ab + a²·d_b + b²·d_a`, one deduces `d_{a+b} · ab = (a+b)(d_a·b + d_b·a)`; the algebraic step in proving additivity of the dual isogeny (Silverman III.6.2c).
- **How**: `rw [hquad]; ring` — the hypothesis transforms the LHS and then `ring` closes.
- **Hypotheses**: Field `K`, elements `a, b ≠ 0`, `a + b ≠ 0`, and the quadratic form hypothesis `hquad`.
- **Uses from project**: none
- **Used by**: unused in file (used by `PullbackCoeff.lean` externally)
- **Visibility**: public
- **Lines**: 242–246, proof length: 5 lines
- **Notes**: `ha`, `hb`, `hab` are declared as hypotheses but NOT used in the proof body (dead hypotheses in the proof, though they might be needed for a full divisibility argument). Pure algebra lemma; suspected mathlib duplication (field identity of this form likely exists in `Mathlib.Algebra.Field.Basic` or similar, but not verified).

---

## Cross-reference summary

| Declaration | Used by (in file) |
|---|---|
| `uconv` | `univPow`, `uconv_zero`, `uconv_one`, `univPow_zero_eq` |
| `univPow` | `compFGL`, `univPow_zero_eq`, `univPow_one_eq_zero`, `bivarComp`, `comp_coeff_one` |
| `uconv_zero` | `univPow_zero_eq` |
| `uconv_one` | `univPow_one_eq_zero` |
| `univPow_zero_eq` | `univPow_one_eq_zero` |
| `fgl_coeff` | `pullbackCoeff_add` (×3) |
| `formalGroupLaw_coeff_right_unit` | `pullbackCoeff_add` |
| `formalGroupLaw_coeff_left_unit` | `pullbackCoeff_add` |
| `compFGL` | `formalMulByNat_coeff` |
| `formalMulByNat_coeff` | `formalMulByInt_coeff` |
| `formalMulByInt_coeff` | `formalMulByInt`, `pullbackCoeff_mulByInt` |
| `formalMulByInt` | `pullbackCoeff_mulByInt` |

**Key API** (used by 3+ others in this file): `univPow` (5 uses), `uconv` (4 uses), `fgl_coeff` (3 uses in `pullbackCoeff_add`).

**Unused in file (dead-code candidates)**:
- `formalGroupEval` — not referenced in file
- `formalInverseEval` — not referenced in file
- `bivarComp` — defined but never used
- `pullbackCoeff_mulByInt` — defined but not called by anything in file
- `formalGroupLaw_coeff_right_unit` — only used via `fgl_coeff` in `pullbackCoeff_add`
- `formalGroupLaw_coeff_left_unit` — same
- `univPow_one_eq_zero` — not called in file (referenced only in a comment)
- `pullbackCoeff_add` — not called in file
- `pullbackCoeff_comp` — not called in file
- `comp_coeff_one` — not called in file
- `dual_additivity_algebraic` — not called in file (used externally in `PullbackCoeff.lean`)

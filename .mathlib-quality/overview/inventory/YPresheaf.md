# Inventory — `projects/AdicSpaces/Adic spaces/FarguesFontaine/YPresheaf.lean`

798 lines. Namespace `FarguesFontaine` (with an inner `DyadicIdx` namespace).
File-level `set_option linter.overlappingInstances false` (line 25) and a
file-wide `noncomputable section` (line 27).

Ambient variables: `(p : ℕ) [Fact p.Prime]`, `(F : Type*)` a perfectoid field of
characteristic `p` (`[Field F] [TopologicalSpace F] [IsTopologicalRing F]
[UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]`),
and `(ϖ : PseudoUniformizer F)`. These are re-declared at line 243–245 after the
`DyadicIdx` namespace closes.

Imports: `FarguesFontaine.BigWindows`, `.ChartSpa`, `.FrobeniusGauss`,
`.IntervalSplitting`.

---

## Section 1 — interval traces (lines 36–146)

### `def intervalTrace`
- **Type**: `intervalTrace (p : ℕ) [Fact p.Prime] (F : Type*) [...] (ϖ : PseudoUniformizer F) (q₁ q₂ : ℚ) : Set (Spv (Ainf p F))`
- **What**: The trace on `Y` of the radius-exponent interval `[q₂, q₁]`: the set of valuations `v ∈ Y p F ϖ` whose radius `κ(v)` lies between `1/q₁` and `1/q₂`.
- **How**: Direct set-builder definition: `{v ∈ Y p F ϖ | KGE p F ϖ (1/q₁) v ∧ KLE p F ϖ (1/q₂) v}` — the conjunction of the two one-sided radius conditions cutting out the annulus.
- **Hypotheses**: None beyond the ambient perfectoid-field variables; `q₁ q₂` are arbitrary rationals (the intended convention is `q₂ < q₁`, both positive).
- **Uses from project**: `Y`, `KGE`, `KLE`, `Ainf`
- **Used by**: `bigWindow_eq_intervalTrace`, `intervalTrace_mono`, `intervalTrace_dyadic_eq_rationalOpen`, `isOpen_intervalTrace_dyadic`, `dyadicTrace`
- **Visibility**: public
- **Lines**: 36–40 (definition, 2 lines of body)
- **Notes**: none

### `theorem bigWindow_eq_intervalTrace`
- **Type**: `∀ (n : ℤ), bigWindow p F ϖ n = intervalTrace p F ϖ (1 / (p:ℚ)^n) (1 / (p:ℚ)^(n+1))`
- **What**: Identifies the "Big windows" of the Fargues–Fontaine construction with interval traces: the window at level `n` is the trace at exponents `(1/p^n, 1/p^{n+1})`.
- **How**: Unfolds both sides to the same `Y ∧ KGE ∧ KLE` conjunction via `show`, then closes with `one_div_one_div` (mathlib) twice, since `1/(1/p^n) = p^n`.
- **Hypotheses**: `n : ℤ` arbitrary; ambient perfectoid hypotheses.
- **Uses from project**: `bigWindow`, `intervalTrace`, `Y`, `KGE`, `KLE`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 42–50 (proof 5 lines)
- **Notes**: none

### `theorem intervalTrace_mono`
- **Type**: `{q₁ q₂ r₁ r₂ : ℚ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (h₁ : r₁ ≤ q₁) (h₂ : q₂ ≤ r₂) : intervalTrace p F ϖ r₁ r₂ ⊆ intervalTrace p F ϖ q₁ q₂`
- **What**: Interval traces are monotone in the exponent interval: shrinking the exponent range `[r₂, r₁] ⊆ [q₂, q₁]` shrinks the trace.
- **How**: Pointwise: destructure membership into `⟨hY, hge, hle⟩` and transport the two radius bounds along `KGE_mono` / `KLE_mono`, converting `r₁ ≤ q₁` into `1/q₁ ≤ 1/r₁` by mathlib's `one_div_le_one_div_of_le`.
- **Hypotheses**: all four exponents positive; the interval inclusion `r₁ ≤ q₁` and `q₂ ≤ r₂`.
- **Uses from project**: `intervalTrace`, `KGE_mono`, `KLE_mono`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 52–65 (proof 8 lines)
- **Notes**: none

### `theorem intervalTrace_dyadic_eq_rationalOpen`
- **Type**: `(s j₁ j₂ : ℕ) (hj₁ : 0 < j₁) (hj₂ : 0 < j₂) : intervalTrace p F ϖ ((j₁:ℚ)/(p:ℚ)^s) ((j₂:ℚ)/(p:ℚ)^s) = rationalOpen (chartT p F (PseudoUniformizer.frobRoot p F ϖ s) 1 (j₁ + j₂ - 1)) (chartS p F (PseudoUniformizer.frobRoot p F ϖ s) 1 j₂)`
- **What**: The key comparison theorem: a *dyadic* interval trace (exponents with denominator `p^s`) is exactly a rational subset of `Spa (A_inf, A_inf)`, namely the `κ' ∈ [1/j₁, 1/j₂]` chart for the `p^s`-th Frobenius-root uniformizer `ϖ' = frobRoot p F ϖ s`.
- **How**: Replaces `ϖ` by `ϖ' = PseudoUniformizer.frobRoot p F ϖ s`, using `teichPi_frobRoot_pow` (so `[ϖ']^{p^s} = [ϖ]`) and `Y_eq_of_teichPi_pow` (so the ambient `Y` is unchanged); then rewrites membership in the chart with `mem_rationalOpen_chartData_iff` and matches each side against `KGE_iff` / `KLE_iff` after clearing the `p^s`-th powers with `vle_pow_iff` and the collapse identities `(([ϖ']^{j})^{p^s} = [ϖ]^j`, `(p^1)^{p^s} = p^{p^s})`.
- **Hypotheses**: `0 < j₁`, `0 < j₂`; `p` prime (used for `p^s > 0`); ambient perfectoid field.
- **Uses from project**: `intervalTrace`, `rationalOpen`, `chartT`, `chartS`, `PseudoUniformizer.frobRoot`, `teichPi`, `teichPi_frobRoot_pow`, `Y`, `Y_eq_of_teichPi_pow`, `mem_rationalOpen_chartData_iff`, `KGE_iff`, `KLE_iff`, `vle_pow_iff`, `Ainf`
- **Used by**: `isOpen_intervalTrace_dyadic`
- **Visibility**: public
- **Lines**: 67–129 (proof 54 lines)
- **Notes**: proof > 30 lines; the `1 + 1 - 1 = 1` `omega` rewrite at line 87 patches the `chartT` numerator normalisation.

### `theorem isOpen_intervalTrace_dyadic`
- **Type**: `(s j₁ j₂ : ℕ) (hj₁ : 0 < j₁) (hj₂ : 0 < j₂) : IsOpen {x : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))) | (x : Spv (Ainf p F)) ∈ intervalTrace p F ϖ ((j₁:ℚ)/(p:ℚ)^s) ((j₂:ℚ)/(p:ℚ)^s)}`
- **What**: Dyadic interval traces are open in the adic spectrum `Spa (A_inf, A_inf)` — this is what makes them a legitimate basis for the structure presheaf.
- **How**: Rewrites the trace as a rational subset via `intervalTrace_dyadic_eq_rationalOpen`, then applies `isOpen_rationalOpen_trace` with the nonemptiness witness `chartT_nonempty`.
- **Hypotheses**: `0 < j₁`, `0 < j₂`; ambient perfectoid field.
- **Uses from project**: `intervalTrace`, `intervalTrace_dyadic_eq_rationalOpen`, `rationalOpen`, `isOpen_rationalOpen_trace`, `chartT`, `chartT_nonempty`, `chartS`, `PseudoUniformizer.frobRoot`, `Spa`, `Ainf`, `ringPlus`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 132–146 (proof 9 lines)
- **Notes**: none

---

## Section 2 — `DyadicIdx` (lines 148–240)

### `structure DyadicIdx`
- **Type**: `structure DyadicIdx where s : ℕ; j₁ : ℕ; j₂ : ℕ; hj₂ : 0 < j₂; hlt : j₂ < j₁`
- **What**: A dyadic interval index: the exponent pair `(j₁/p^s, j₂/p^s)` with the exponents strictly decreasing and the smaller one positive.
- **How**: Plain structure carrying the denominator exponent `s`, the two numerators, and the two positivity/ordering side conditions; no proof content.
- **Hypotheses**: fields `hj₂ : 0 < j₂` and `hlt : j₂ < j₁` are the structural constraints.
- **Uses from project**: `[]`
- **Used by**: `DyadicIdx.q₁`, `DyadicIdx.q₂`, `DyadicIdx.hj₁`, `DyadicIdx.q₁_pos`, `DyadicIdx.q₂_pos`, `DyadicIdx.q₂_lt_q₁`, `DyadicIdx.Nested`, `DyadicIdx.splitL`, `DyadicIdx.splitR`, `dyadicVal`, `dyadicRes`, `dyadicTrace`, `limitSectionsY`, `limitEvalTop`, and essentially every later declaration
- **Visibility**: public
- **Lines**: 148–159
- **Notes**: every field carries a doc-comment.

### `def DyadicIdx.q₁`
- **Type**: `q₁ (p : ℕ) (i : DyadicIdx) : ℚ`
- **What**: The larger rational exponent `j₁ / p^s` of a dyadic index.
- **How**: Direct definition `(i.j₁ : ℚ) / ((p : ℚ) ^ i.s)`.
- **Hypotheses**: none (`p` need not be prime here).
- **Uses from project**: `DyadicIdx`
- **Used by**: `DyadicIdx.q₁_pos`, `DyadicIdx.q₂_lt_q₁`, `DyadicIdx.Nested`, `DyadicIdx.splitL_nested`, `DyadicIdx.splitR_nested`, `dyadicVal`, `dyadicRes`, `dyadicTrace`
- **Visibility**: public
- **Lines**: 163–164
- **Notes**: none

### `def DyadicIdx.q₂`
- **Type**: `q₂ (p : ℕ) (i : DyadicIdx) : ℚ`
- **What**: The smaller rational exponent `j₂ / p^s` of a dyadic index.
- **How**: Direct definition `(i.j₂ : ℚ) / ((p : ℚ) ^ i.s)`.
- **Hypotheses**: none.
- **Uses from project**: `DyadicIdx`
- **Used by**: `DyadicIdx.q₂_pos`, `DyadicIdx.q₂_lt_q₁`, `DyadicIdx.Nested`, `DyadicIdx.splitL_nested`, `DyadicIdx.splitR_nested`, `dyadicVal`, `dyadicRes`, `dyadicTrace`
- **Visibility**: public
- **Lines**: 166–167
- **Notes**: none

### `theorem DyadicIdx.hj₁`
- **Type**: `(i : DyadicIdx) : 0 < i.j₁`
- **What**: The larger numerator of a dyadic index is positive.
- **How**: Transitivity `0 < j₂ < j₁`, i.e. `lt_trans i.hj₂ i.hlt`.
- **Hypotheses**: the structure fields `hj₂` and `hlt`.
- **Uses from project**: `DyadicIdx`
- **Used by**: `DyadicIdx.q₁_pos`
- **Visibility**: public
- **Lines**: 169 (term proof, 1 line)
- **Notes**: none

### `theorem DyadicIdx.q₁_pos`
- **Type**: `[Fact p.Prime] (i : DyadicIdx) : 0 < i.q₁ p`
- **What**: The larger rational exponent is positive.
- **How**: `p > 0` from primality (`Nat.Prime.pos` on `Fact.out`), `j₁ > 0` from `DyadicIdx.hj₁`, then `positivity` on the quotient after unfolding `q₁`.
- **Hypotheses**: `Fact p.Prime`.
- **Uses from project**: `DyadicIdx.q₁`, `DyadicIdx.hj₁`
- **Used by**: `dyadicVal`, `dyadicRes`
- **Visibility**: public
- **Lines**: 171–176 (proof 5 lines)
- **Notes**: none

### `theorem DyadicIdx.q₂_pos`
- **Type**: `[Fact p.Prime] (i : DyadicIdx) : 0 < i.q₂ p`
- **What**: The smaller rational exponent is positive.
- **How**: Same shape as `q₁_pos`: `p > 0` via `Nat.Prime.pos`, `j₂ > 0` from the structure field `hj₂`, then `positivity`.
- **Hypotheses**: `Fact p.Prime`; the field `hj₂`.
- **Uses from project**: `DyadicIdx.q₂`, `DyadicIdx`
- **Used by**: `dyadicVal`, `dyadicRes`
- **Visibility**: public
- **Lines**: 178–183 (proof 5 lines)
- **Notes**: none

### `theorem DyadicIdx.q₂_lt_q₁`
- **Type**: `[Fact p.Prime] (i : DyadicIdx) : i.q₂ p < i.q₁ p`
- **What**: The two rational exponents of a dyadic index are strictly ordered.
- **How**: Both sides have the same positive denominator `p^s`, so `gcongr` reduces to `j₂ < j₁`, which is the structure field `hlt` after `exact_mod_cast`.
- **Hypotheses**: `Fact p.Prime` (for the positive denominator); the field `hlt`.
- **Uses from project**: `DyadicIdx.q₁`, `DyadicIdx.q₂`, `DyadicIdx`
- **Used by**: `DyadicIdx.Nested.mem₁`, `DyadicIdx.Nested.mem₂`, `dyadicRes`
- **Visibility**: public
- **Lines**: 185–192 (proof 7 lines)
- **Notes**: none

### `def DyadicIdx.Nested`
- **Type**: `Nested (p : ℕ) (i' i : DyadicIdx) : Prop`
- **What**: The nesting relation on dyadic indices: `i'`'s exponent interval is contained in `i`'s, i.e. `i.q₂ ≤ i'.q₂` and `i'.q₁ ≤ i.q₁`.
- **How**: A conjunction of the two endpoint inequalities.
- **Hypotheses**: none.
- **Uses from project**: `DyadicIdx.q₁`, `DyadicIdx.q₂`, `DyadicIdx`
- **Used by**: `DyadicIdx.Nested.mem₁`, `DyadicIdx.Nested.mem₂`, `DyadicIdx.splitL_nested`, `DyadicIdx.splitR_nested`, `dyadicRes`, `limitSectionsY`, `limitEvalTop_spec`, `dyadicTrace_subset_nested`, `DyadicIdx.Nested.trans`, `dyadicRes_id`, `dyadicRes_comp`, and the gluing theorems
- **Visibility**: public
- **Lines**: 194–196
- **Notes**: none

### `theorem DyadicIdx.Nested.mem₁`
- **Type**: `[Fact p.Prime] {i' i : DyadicIdx} (h : Nested p i' i) : i.q₂ p ≤ i'.q₁ p ∧ i'.q₁ p ≤ i.q₁ p`
- **What**: Under nesting, `i'`'s *upper* endpoint lies inside `i`'s interval — the membership package the interval-ring restriction map needs.
- **How**: Chain `i.q₂ ≤ i'.q₂ ≤ i'.q₁` using `h.1` and `DyadicIdx.q₂_lt_q₁`, and take `h.2` for the second component.
- **Hypotheses**: `Fact p.Prime`; `Nested p i' i`.
- **Uses from project**: `DyadicIdx.Nested`, `DyadicIdx.q₂_lt_q₁`, `DyadicIdx.q₁`, `DyadicIdx.q₂`
- **Used by**: `dyadicRes`
- **Visibility**: public
- **Lines**: 198–200 (term proof, 1 line)
- **Notes**: none

### `theorem DyadicIdx.Nested.mem₂`
- **Type**: `[Fact p.Prime] {i' i : DyadicIdx} (h : Nested p i' i) : i.q₂ p ≤ i'.q₂ p ∧ i'.q₂ p ≤ i.q₁ p`
- **What**: Under nesting, `i'`'s *lower* endpoint lies inside `i`'s interval.
- **How**: `h.1` gives the left inequality; `i'.q₂ ≤ i'.q₁ ≤ i.q₁` via `DyadicIdx.q₂_lt_q₁` and `h.2` gives the right.
- **Hypotheses**: `Fact p.Prime`; `Nested p i' i`.
- **Uses from project**: `DyadicIdx.Nested`, `DyadicIdx.q₂_lt_q₁`, `DyadicIdx.q₁`, `DyadicIdx.q₂`
- **Used by**: `dyadicRes`
- **Visibility**: public
- **Lines**: 202–204 (term proof, 1 line)
- **Notes**: none

### `def DyadicIdx.splitL`
- **Type**: `(i : DyadicIdx) (j : ℕ) (hj : i.j₂ < j) (hj' : j < i.j₁) : DyadicIdx`
- **What**: The left (upper-radius) piece `(j₁, j)` obtained by splitting `i`'s interval at an interior numerator `j`.
- **How**: Anonymous-constructor record `⟨i.s, i.j₁, j, lt_trans i.hj₂ hj, hj'⟩`, reusing `i`'s denominator exponent.
- **Hypotheses**: `j` strictly interior: `i.j₂ < j < i.j₁`.
- **Uses from project**: `DyadicIdx`
- **Used by**: `DyadicIdx.splitL_nested`, and the split-gluing theorems later in the file
- **Visibility**: public
- **Lines**: 206–209
- **Notes**: none

### `def DyadicIdx.splitR`
- **Type**: `(i : DyadicIdx) (j : ℕ) (hj : i.j₂ < j) (hj' : j < i.j₁) : DyadicIdx`
- **What**: The right (lower-radius) piece `(j, j₂)` of a middle split of `i` at `j`.
- **How**: Record `⟨i.s, j, i.j₂, i.hj₂, hj⟩`.
- **Hypotheses**: `i.j₂ < j < i.j₁`.
- **Uses from project**: `DyadicIdx`
- **Used by**: `DyadicIdx.splitR_nested`, and the split-gluing theorems later in the file
- **Visibility**: public
- **Lines**: 211–214
- **Notes**: none

### `theorem DyadicIdx.splitL_nested`
- **Type**: `[Fact p.Prime] (i : DyadicIdx) (j : ℕ) (hj : i.j₂ < j) (hj' : j < i.j₁) : Nested p (splitL i j hj hj') i`
- **What**: The left split piece is nested inside the original index.
- **How**: Upper endpoints agree (`le_rfl`); for the lower one, both sides share denominator `p^s > 0`, so `gcongr` reduces to `i.j₂ ≤ j`, given by `hj`.
- **Hypotheses**: `Fact p.Prime`; `i.j₂ < j < i.j₁`.
- **Uses from project**: `DyadicIdx.Nested`, `DyadicIdx.splitL`
- **Used by**: the split-gluing theorems later in the file
- **Visibility**: public
- **Lines**: 216–226 (proof 9 lines)
- **Notes**: none

### `theorem DyadicIdx.splitR_nested`
- **Type**: `[Fact p.Prime] (i : DyadicIdx) (j : ℕ) (hj : i.j₂ < j) (hj' : j < i.j₁) : Nested p (splitR i j hj hj') i`
- **What**: The right split piece is nested inside the original index.
- **How**: Mirror of `splitL_nested`: lower endpoints agree (`le_rfl`); the upper one reduces by `gcongr` over the common positive denominator to `j ≤ i.j₁`, given by `hj'`.
- **Hypotheses**: `Fact p.Prime`; `i.j₂ < j < i.j₁`.
- **Uses from project**: `DyadicIdx.Nested`, `DyadicIdx.splitR`
- **Used by**: the split-gluing theorems later in the file
- **Visibility**: public
- **Lines**: 228–238 (proof 9 lines)
- **Notes**: none

---

## Section 3 — dyadic interval rings and limit sections (lines 247–336)

### `def dyadicVal`
- **Type**: `dyadicVal (p F ϖ) (i : DyadicIdx) : Type _`
- **What**: The interval ring `B_{[q₂,q₁]}` attached to a dyadic index — the coefficient ring of the presheaf at index `i`.
- **How**: Unfolds to the coercion `↥(BIQ p F ϖ (i.q₁ p) (i.q₂ p) _ _)`, supplying positivity from `DyadicIdx.q₁_pos` / `q₂_pos`.
- **Hypotheses**: ambient perfectoid field; `Fact p.Prime` (needed for the positivity arguments).
- **Uses from project**: `BIQ`, `DyadicIdx.q₁`, `DyadicIdx.q₂`, `DyadicIdx.q₁_pos`, `DyadicIdx.q₂_pos`
- **Used by**: the `CommRing` instance, `dyadicRes`, `limitSectionsY`, `limitEvalTop`, and all topological/uniform instances later
- **Visibility**: public, `noncomputable`
- **Lines**: 247–249
- **Notes**: a `Type _`-valued `def` (not `abbrev`), so instances must be transported explicitly — this is why the `CommRing` instance below is proved by `rw [dyadicVal]`.

### `instance : CommRing (dyadicVal p F ϖ i)`
- **Type**: `noncomputable instance (i : DyadicIdx) : CommRing (dyadicVal p F ϖ i)`
- **What**: Transports the commutative-ring structure of `BIQ` across the definitional unfolding of `dyadicVal`.
- **How**: `rw [dyadicVal]` turns the goal into `CommRing ↥(BIQ …)`, then `infer_instance`.
- **Hypotheses**: ambient perfectoid field.
- **Uses from project**: `dyadicVal`, `BIQ`
- **Used by**: `dyadicRes`, `limitSectionsY`, and every ring-theoretic statement about `dyadicVal`
- **Visibility**: public instance (anonymous), `noncomputable`
- **Lines**: 251–253 (proof 2 lines)
- **Notes**: none

### `def dyadicRes`
- **Type**: `dyadicRes {i' i : DyadicIdx} (h : DyadicIdx.Nested p i' i) : dyadicVal p F ϖ i →+* dyadicVal p F ϖ i'`
- **What**: The restriction ring homomorphism between interval rings along a nesting of dyadic indices — the transition map of the presheaf.
- **How**: Instantiates the general interval-ring restriction `biResQ'` at the four endpoints, feeding it positivity (`q₁_pos`/`q₂_pos`), strictness (`q₂_lt_q₁`) and the two containment packages `h.mem₁`, `h.mem₂`.
- **Hypotheses**: `DyadicIdx.Nested p i' i`; ambient perfectoid field.
- **Uses from project**: `biResQ'`, `dyadicVal`, `DyadicIdx.Nested`, `DyadicIdx.q₁`, `DyadicIdx.q₂`, `DyadicIdx.q₁_pos`, `DyadicIdx.q₂_pos`, `DyadicIdx.q₂_lt_q₁`, `DyadicIdx.Nested.mem₁`, `DyadicIdx.Nested.mem₂`
- **Used by**: `limitSectionsY`, `limitEvalTop_spec`, `dyadicRes_id`, `dyadicRes_comp`, `valuesOnBasisEquiv`-style gluing statements, and the continuity instances later
- **Visibility**: public, `noncomputable`
- **Lines**: 255–260
- **Notes**: none

### `def dyadicTrace`
- **Type**: `dyadicTrace (p F ϖ) (i : DyadicIdx) : Set (Spv (Ainf p F))`
- **What**: The trace of a dyadic index on `Y`: the interval trace at `i`'s two rational exponents.
- **How**: `intervalTrace p F ϖ (i.q₁ p) (i.q₂ p)`.
- **Hypotheses**: ambient perfectoid field.
- **Uses from project**: `intervalTrace`, `DyadicIdx.q₁`, `DyadicIdx.q₂`, `Ainf`
- **Used by**: `limitSectionsY`, `limitRestrictY`, `limitEvalTop`, `limitEvalTop_spec`, `dyadicTrace_subset_nested`, `limitEvalTop_bijective`, and the gluing theorems
- **Visibility**: public
- **Lines**: 262–264
- **Notes**: none

### `def limitSectionsY`
- **Type**: `limitSectionsY (p F ϖ) (W : Set (Spv (Ainf p F))) : Subring (Π i : {i : DyadicIdx // dyadicTrace p F ϖ i ⊆ W}, dyadicVal p F ϖ i.1)`
- **What**: The sections of the structure presheaf over an arbitrary subset `W`: the subring of the product of interval rings, over all dyadic traces contained in `W`, cut out by compatibility with all restriction maps.
- **How**: A `Subring` bundled by hand — carrier is the compatibility locus `{f | ∀ i' i h, dyadicRes h (f i) = f i'}`; the five closure fields follow because `dyadicRes` is a ring hom (`map_zero`, `map_one`, `map_add`, `map_mul`, `map_neg`).
- **Hypotheses**: ambient perfectoid field; `W` arbitrary.
- **Uses from project**: `dyadicTrace`, `dyadicVal`, `dyadicRes`, `DyadicIdx`, `DyadicIdx.Nested`, `Ainf`
- **Used by**: `limitRestrictY`, `limitRestrictY_id`, `limitRestrictY_comp`, `limitEvalTop`, `limitEvalTop_spec`, the completeness/separation/topological-ring instances, and `yPresheaf`
- **Visibility**: public, `noncomputable`
- **Lines**: 266–292 (definition 22 lines)
- **Notes**: none

### `def limitRestrictY`
- **Type**: `limitRestrictY {W' W : Set (Spv (Ainf p F))} (hW : W' ⊆ W) : ↥(limitSectionsY p F ϖ W) →+* ↥(limitSectionsY p F ϖ W')`
- **What**: The presheaf restriction map: a compatible family indexed by traces inside `W` restricts, by re-indexing, to one indexed by traces inside `W' ⊆ W`.
- **How**: `toFun f i := f.1 ⟨i.1, Set.Subset.trans i.2 hW⟩` — pure re-indexing along `Set.Subset.trans`; all four ring-hom laws hold by `rfl` since nothing is computed.
- **Hypotheses**: `W' ⊆ W`.
- **Uses from project**: `limitSectionsY`, `Ainf`
- **Used by**: `limitRestrictY_id`, `limitRestrictY_comp`, the continuity instance, `yPresheaf`
- **Visibility**: public, `noncomputable`
- **Lines**: 295–305
- **Notes**: none

### `theorem limitRestrictY_id`
- **Type**: `{W : Set (Spv (Ainf p F))} : limitRestrictY p F ϖ (le_refl W) = RingHom.id ↥(limitSectionsY p F ϖ W)`
- **What**: Restricting a section to the same set is the identity — the first presheaf functoriality law.
- **How**: `rfl`: re-indexing along `Set.Subset.trans i.2 (le_refl W)` is definitionally the original index.
- **Hypotheses**: none.
- **Uses from project**: `limitRestrictY`, `limitSectionsY`, `Ainf`
- **Used by**: unused in file (consumed by `yPresheaf`'s presheaf laws conceptually)
- **Visibility**: public
- **Lines**: 307–311 (term proof, `rfl`)
- **Notes**: none

### `theorem limitRestrictY_comp`
- **Type**: `{W'' W' W : Set (Spv (Ainf p F))} (h₁ : W'' ⊆ W') (h₂ : W' ⊆ W) : (limitRestrictY p F ϖ h₁).comp (limitRestrictY p F ϖ h₂) = limitRestrictY p F ϖ (Set.Subset.trans h₁ h₂)`
- **What**: Restrictions compose — the second presheaf functoriality law.
- **How**: `rfl`, since composing two re-indexings is the re-indexing along the composite subset proof (proof irrelevance in `Prop`).
- **Hypotheses**: `W'' ⊆ W' ⊆ W`.
- **Uses from project**: `limitRestrictY`, `limitSectionsY`, `Ainf`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 313–318 (term proof, `rfl`)
- **Notes**: none

### `def limitEvalTop`
- **Type**: `limitEvalTop (i₀ : DyadicIdx) : ↥(limitSectionsY p F ϖ (dyadicTrace p F ϖ i₀)) →+* dyadicVal p F ϖ i₀`
- **What**: Evaluation of a limit section over `dyadicTrace i₀` at the *top* index `i₀` itself — the candidate inverse of the comparison map from the interval ring to limit sections.
- **How**: `f ↦ f.1 ⟨i₀, Set.Subset.refl _⟩`; the ring-hom laws are `rfl` because the subring's operations are pointwise.
- **Hypotheses**: none beyond ambient.
- **Uses from project**: `limitSectionsY`, `dyadicTrace`, `dyadicVal`, `DyadicIdx`
- **Used by**: `limitEvalTop_spec`, and the bijectivity/gluing theorems later in the file
- **Visibility**: public, `noncomputable`
- **Lines**: 320–327
- **Notes**: none

### `theorem limitEvalTop_spec`
- **Type**: `(i₀ : DyadicIdx) (f : ↥(limitSectionsY p F ϖ (dyadicTrace p F ϖ i₀))) (i : {i // dyadicTrace p F ϖ i ⊆ dyadicTrace p F ϖ i₀}) (h : DyadicIdx.Nested p i.1 i₀) : f.1 i = dyadicRes p F ϖ h (limitEvalTop p F ϖ i₀ f)`
- **What**: Every component of a limit section is determined by its top value: `f i = res_{i₀→i}(f i₀)`.
- **How**: Directly the compatibility property `f.2` of the section, instantiated at `(i, i₀)` and symmetrised.
- **Hypotheses**: `DyadicIdx.Nested p i.1 i₀` — `i` nested in the top index.
- **Uses from project**: `limitSectionsY`, `dyadicTrace`, `dyadicRes`, `limitEvalTop`, `DyadicIdx.Nested`, `DyadicIdx`
- **Used by**: the bijectivity theorem for the comparison map
- **Visibility**: public
- **Lines**: 329–336 (term proof, 1 line)
- **Notes**: none

### `theorem vpiQ_pow`
- **Type**: `(q : ℚ) (a : ℕ) : vpiQ p F ϖ q ^ a = vpiQ p F ϖ (q * a)` — with `omit [CharP F p]`
- **What**: Raising the rational-radius value `|ϖ|^q` to a natural power `a` multiplies the exponent: `(v_ϖ^q)^a = v_ϖ^{qa}`.
- **How**: Unfold `vpiQ` twice, convert the natural power to an `rpow` via mathlib's `NNReal.rpow_natCast`, merge with `NNReal.rpow_mul`, and close the exponent identity `q * a` with `push_cast; ring`.
- **Hypotheses**: none (`CharP F p` explicitly omitted).
- **Uses from project**: `vpiQ`
- **Used by**: the Gauss-valuation lemmas later in the file
- **Visibility**: public
- **Lines**: 338–345 (proof 4 lines)
- **Notes**: `omit [CharP F p] in` attribute at line 338.

### `theorem vpiQ_le_vpiQ_iff`
- **Type**: `{x y : ℚ} : vpiQ p F ϖ x ≤ vpiQ p F ϖ y ↔ y ≤ x`
- **What**: The rational-radius values `|ϖ|^x` compare *antitonically* in the exponent, and this is an iff (both directions).
- **How**: Establishes `0 < |ϖ| < 1` — nonvanishing from `PseudoUniformizer.toOF_ne_zero` via `Valuation.ne_zero_iff`, and `< 1` from `perfectoidValuation_toOF_lt_one` — then unfolds `vpiQ` to `NNReal.rpow` and applies mathlib's `Real.rpow_le_rpow_left_iff_of_base_lt_one`, which reverses the inequality for a base below 1.
- **Hypotheses**: none explicit; uses that `ϖ` is a pseudo-uniformizer (so its perfectoid valuation is in `(0,1)`).
- **Uses from project**: `vpiQ`, `perfectoidValuation`, `perfectoidValuation_toOF_lt_one`, `PseudoUniformizer.toOF`, `PseudoUniformizer.toOF_ne_zero`, `OF`
- **Used by**: `gaussPoint_mem_intervalTrace_iff`
- **Visibility**: public
- **Lines**: 347–362 (proof 13 lines)
- **Notes**: none

---

## Section 4 — Gauss points detect the interval (lines 365–466)

### `theorem gaussVal_p_pow`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (a : ℕ) : gaussVal p F hρ0 hρ1 ((p : Ainf p F) ^ a) = ρ ^ a`
- **What**: The Gauss valuation at radius `ρ` sends `p^a` to `ρ^a` — i.e. `|p| = ρ` for the Gauss point.
- **How**: `Valuation.map_pow` reduces to the case `a = 1`; then `gaussVal_apply` plus `gaussValue_p_mul p F hρ1.le 1` combined with `gaussValue_one` gives `gaussValue p = ρ`.
- **Hypotheses**: `0 < ρ < 1` (the Gauss radius is in the open unit interval).
- **Uses from project**: `gaussVal`, `gaussVal_apply`, `gaussValue_p_mul`, `gaussValue_one`, `Ainf`
- **Used by**: `gaussPoint_mem_intervalTrace_iff`
- **Visibility**: public
- **Lines**: 365–372 (proof 5 lines)
- **Notes**: none

### `theorem gaussVal_teichPi_pow`
- **Type**: `{ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (b : ℕ) : gaussVal p F hρ0 hρ1 (teichPi p F ϖ ^ b) = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b`
- **What**: The Gauss valuation of a power of the Teichmüller lift `[ϖ]` is the corresponding power of the perfectoid valuation of `ϖ` — the Gauss point is "the identity" on Teichmüller elements.
- **How**: `Valuation.map_pow`, then `gaussVal_apply` and `gaussValue_teichmuller` (which computes the Gauss value of a Teichmüller lift as the tilted valuation), after unfolding `teichPi`.
- **Hypotheses**: `0 < ρ < 1`.
- **Uses from project**: `gaussVal`, `gaussVal_apply`, `teichPi`, `gaussValue_teichmuller`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`
- **Used by**: `gaussPoint_mem_intervalTrace_iff`
- **Visibility**: public
- **Lines**: 374–379 (proof 2 lines)
- **Notes**: none

### `theorem gaussPoint_mem_intervalTrace_iff`
- **Type**: `{q q₁ q₂ : ℚ} (hq : 0 < q) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) : ofValuation (gaussVal p F (vpiQ_pos p F ϖ q) (vpiQ_lt_one p F ϖ hq)) ∈ intervalTrace p F ϖ q₁ q₂ ↔ q₂ ≤ q ∧ q ≤ q₁`
- **What**: **The geometric separation statement**: the Gauss point of radius `|ϖ|^q` lies in the `(q₁, q₂)`-interval trace precisely when the exponent `q` lies in `[q₂, q₁]`. Gauss points therefore "see" the interval exactly.
- **How**: Writes `1/q₁` and `1/q₂` as ratios of naturals `den/num.toNat` (via `Rat.num_div_den` and `Int.toNat_of_nonneg`), so the trace conditions become `KGE_iff` / `KLE_iff` statements about `vle ([ϖ]^num) (p^den)`; each is then computed by `gaussVal_teichPi_pow`, `gaussVal_p_pow`, `vpiQ_natCast`, `vpiQ_pow` and turned into the scalar inequality `q * den ≤ num ↔ q ≤ q₁` by `le_div_iff₀` / `div_le_iff₀` plus the antitone comparison `vpiQ_le_vpiQ_iff`. Membership in `Y` comes from `gaussPoint_mem_Y`.
- **Hypotheses**: all three exponents positive.
- **Uses from project**: `ofValuation`, `gaussVal`, `vpiQ_pos`, `vpiQ_lt_one`, `intervalTrace`, `gaussPoint_mem_Y`, `KGE_iff`, `KLE_iff`, `gaussVal_teichPi_pow`, `gaussVal_p_pow`, `vpiQ`, `vpiQ_natCast`, `vpiQ_pow`, `vpiQ_le_vpiQ_iff`, `teichPi`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`, `Ainf`
- **Used by**: `dyadicTrace_subset_nested`
- **Visibility**: public
- **Lines**: 381–446 (proof 59 lines)
- **Notes**: proof > 30 lines; contains two large `have hcompute₁/₂` blocks that each do a `show`-then-`rw` valuation computation.

### `theorem dyadicTrace_subset_nested`
- **Type**: `{i' i : DyadicIdx} (h : dyadicTrace p F ϖ i' ⊆ dyadicTrace p F ϖ i) : DyadicIdx.Nested p i' i`
- **What**: **The geometric bridge**: containment of dyadic *traces* on `Y` forces containment of the underlying exponent *intervals*. This converts a topological hypothesis into the combinatorial `Nested` relation the algebra needs.
- **How**: Evaluates the inclusion at the two endpoint Gauss points of `i'`: `gaussPoint_mem_intervalTrace_iff` puts the radius-`q₁'` and radius-`q₂'` Gauss points in `dyadicTrace i'` (using `q₂_lt_q₁`), pushes them into `dyadicTrace i` along `h`, and reads off `i.q₂ ≤ i'.q₂` and `i'.q₁ ≤ i.q₁` from the same iff.
- **Hypotheses**: the trace inclusion `dyadicTrace i' ⊆ dyadicTrace i`; ambient perfectoid field.
- **Uses from project**: `dyadicTrace`, `DyadicIdx.Nested`, `gaussPoint_mem_intervalTrace_iff`, `ofValuation`, `gaussVal`, `vpiQ_pos`, `vpiQ_lt_one`, `DyadicIdx.q₁`, `DyadicIdx.q₂`, `DyadicIdx.q₁_pos`, `DyadicIdx.q₂_pos`, `DyadicIdx.q₂_lt_q₁`
- **Used by**: `limitEvalTop_bijective`
- **Visibility**: public
- **Lines**: 448–466 (proof 13 lines)
- **Notes**: this is the only place the Gauss-point machinery is consumed; without it the presheaf comparison would be unprovable.

---

## Section 5 — presheaf laws and gluing (lines 468–665)

### `theorem DyadicIdx.Nested.trans`
- **Type**: `{i'' i' i : DyadicIdx} (h₁ : Nested p i'' i') (h₂ : Nested p i' i) : Nested p i'' i`
- **What**: Nesting of dyadic indices is transitive.
- **How**: Componentwise `le_trans` on the two endpoint inequalities (note the order flip on the lower endpoint).
- **Hypotheses**: two nestings.
- **Uses from project**: `DyadicIdx.Nested`
- **Used by**: `dyadicRes_comp`
- **Visibility**: public
- **Lines**: 468–472 (term proof, 1 line)
- **Notes**: declared *outside* the `DyadicIdx` namespace block using the fully qualified name.

### `theorem dyadicRes_id`
- **Type**: `(i : DyadicIdx) (h : DyadicIdx.Nested p i i) : dyadicRes p F ϖ h = RingHom.id (dyadicVal p F ϖ i)`
- **What**: Restriction along a self-nesting is the identity — the first presheaf law at the level of dyadic index restrictions.
- **How**: Term-mode instantiation of the interval-ring identity law `biResQ'_id` at `i`'s endpoints.
- **Hypotheses**: `Nested p i i` (always true, but taken as an argument so any proof works — proof irrelevance).
- **Uses from project**: `dyadicRes`, `dyadicVal`, `biResQ'_id`, `DyadicIdx.Nested`, `DyadicIdx.q₁`, `DyadicIdx.q₂`, `DyadicIdx.q₁_pos`, `DyadicIdx.q₂_pos`, `DyadicIdx.q₂_lt_q₁`
- **Used by**: `limitEvalTop_bijective`
- **Visibility**: public
- **Lines**: 474–478 (term proof, 1 line)
- **Notes**: none

### `theorem dyadicRes_comp`
- **Type**: `{i'' i' i : DyadicIdx} (h₁ : Nested p i'' i') (h₂ : Nested p i' i) : (dyadicRes p F ϖ h₁).comp (dyadicRes p F ϖ h₂) = dyadicRes p F ϖ (h₁.trans p h₂)`
- **What**: Dyadic restrictions compose — the second presheaf law.
- **How**: Term-mode instantiation of `biResQ'_comp` at the six endpoints of `i, i', i''`, feeding positivity, strictness and the four `mem₁`/`mem₂` containment packages.
- **Hypotheses**: two nestings `i'' ⊆ i' ⊆ i`.
- **Uses from project**: `dyadicRes`, `biResQ'_comp`, `DyadicIdx.Nested`, `DyadicIdx.Nested.trans`, `DyadicIdx.Nested.mem₁`, `DyadicIdx.Nested.mem₂`, `DyadicIdx.q₁`, `DyadicIdx.q₂`, `DyadicIdx.q₁_pos`, `DyadicIdx.q₂_pos`, `DyadicIdx.q₂_lt_q₁`
- **Used by**: `limitEvalTop_bijective`
- **Visibility**: public
- **Lines**: 480–488 (term proof, 4 lines)
- **Notes**: none

### `theorem limitEvalTop_bijective`
- **Type**: `(i₀ : DyadicIdx) : Function.Bijective (limitEvalTop p F ϖ i₀)`
- **What**: **The values-on-basis comparison theorem**: evaluation at the top index is a bijection between the limit sections over `dyadicTrace i₀` and the single interval ring `dyadicVal i₀`. In other words, the inverse-limit presheaf is already computed by the interval ring on each basis element.
- **How**: *Injectivity*: every component of a section is `dyadicRes` of the top value by `limitEvalTop_spec`, where the required nesting is produced from the subtype's subset proof by the geometric bridge `dyadicTrace_subset_nested`. *Surjectivity*: given `x`, the family `i ↦ dyadicRes (dyadicTrace_subset_nested i.2) x` is compatible by `dyadicRes_comp`, and evaluating it at the top index returns `x` by `dyadicRes_id`.
- **Hypotheses**: none beyond ambient perfectoid field.
- **Uses from project**: `limitEvalTop`, `limitEvalTop_spec`, `dyadicTrace_subset_nested`, `dyadicTrace`, `dyadicRes`, `dyadicRes_comp`, `dyadicRes_id`, `limitSectionsY`, `DyadicIdx.Nested`, `DyadicIdx`
- **Used by**: unused in file (the headline export of the presheaf comparison)
- **Visibility**: public
- **Lines**: 490–518 (proof 22 lines)
- **Notes**: none

### `theorem biResQ'_split_existsUnique`
- **Type**: `(q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂) (hr : 0 < r) (hlt : q₂ < q₁) (hrm : q₂ ≤ r ∧ r ≤ q₁) (g₁ : ↥(BIQ p F ϖ q₁ r h₁ hr)) (g₂ : ↥(BIQ p F ϖ r q₂ hr h₂)) (hmatch : biSndQ … g₁ = biFstQ … g₂) : ∃! f : ↥(BIQ p F ϖ q₁ q₂ h₁ h₂), (restriction to [r,q₁]) f = g₁ ∧ (restriction to [q₂,r]) f = g₂`
- **What**: The `∃!` repackaging of the two-piece gluing theorem for interval rings: a matching pair over `[r,q₁]` and `[q₂,r]` glues to a *unique* section over `[q₂,q₁]`.
- **How**: Existence from `biResQ'_split_surjective` applied to the matching pair; uniqueness from `biResQ'_split_injective` applied to the difference of any competing `f'` with the produced `f`.
- **Hypotheses**: all three exponents positive; `q₂ < q₁`; the split point `r ∈ [q₂, q₁]`; the matching condition `biSndQ g₁ = biFstQ g₂` on the overlap.
- **Uses from project**: `BIQ`, `biResQ'`, `biSndQ`, `biFstQ`, `biResQ'_split_surjective`, `biResQ'_split_injective`
- **Used by**: `biResQ'_chain_glue`
- **Visibility**: public
- **Lines**: 520–533 (proof 5 lines)
- **Notes**: none

### `theorem exists_unique_dyadicRes_glue`
- **Type**: `(i : DyadicIdx) (j : ℕ) (hj : i.j₂ < j) (hj' : j < i.j₁) (gL : dyadicVal p F ϖ (splitL i j hj hj')) (gR : dyadicVal p F ϖ (splitR i j hj hj')) (hmatch : biSndQ … gL = biFstQ … gR) : ∃! f : dyadicVal p F ϖ i, dyadicRes (splitL_nested …) f = gL ∧ dyadicRes (splitR_nested …) f = gR`
- **What**: **The two-piece sheaf axiom for the dyadic interval presheaf**: a matching pair of sections over the left and right pieces of a middle split of `i` is the pair of restrictions of a unique section over `i`.
- **How**: Assembles the split-point membership `hrm` from `splitL_nested.1` and `splitR_nested.2`, then existence via `biResQ'_split_surjective` and uniqueness via `biResQ'_split_injective`, both at the split exponent `(splitL i j).q₂ = j/p^s`.
- **Hypotheses**: `i.j₂ < j < i.j₁` (an interior split point); the overlap matching condition on `gL, gR`.
- **Uses from project**: `DyadicIdx.splitL`, `DyadicIdx.splitR`, `DyadicIdx.splitL_nested`, `DyadicIdx.splitR_nested`, `dyadicVal`, `dyadicRes`, `biSndQ`, `biFstQ`, `biResQ'_split_surjective`, `biResQ'_split_injective`, `DyadicIdx.q₁`, `DyadicIdx.q₂`, `DyadicIdx.q₁_pos`, `DyadicIdx.q₂_pos`, `DyadicIdx.q₂_lt_q₁`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 535–565 (proof 12 lines)
- **Notes**: none

### `theorem biResQ'_chain_glue`
- **Type**: `(q : ℕ → ℚ) (hq : ∀ t, 0 < q t) (hlt : ∀ t, q t < q (t+1)) (g : ∀ t, ↥(BIQ p F ϖ (q (t+1)) (q t) …)) (hmatch : ∀ t, biSndQ … (g (t+1)) = biFstQ … (g t)) : ∀ m : ℕ, ∃! f : ↥(BIQ p F ϖ (q (m+1)) (q 0) …), ∀ t ≤ m, biResQ' … f = g t`
- **What**: **The finite-chain sheaf axiom**: matching sections over the `N` consecutive pieces `[q t, q (t+1)]` of a strictly increasing exponent chain glue to a unique section over the whole interval `[q 0, q (m+1)]`.
- **How**: Induction on `m`. Base case `m = 0`: the single piece *is* the whole interval, so `biResQ'_id` finishes both existence and uniqueness. Inductive step: the glue `fm` over `[q 0, q (m+1)]` has top endpoint matching `g m` — proved with `biFstQ_biResQ'_left` — hence matches `g (m+1)` by `hmatch`; `biResQ'_split_existsUnique` then glues `g (m+1)` and `fm` into `f` over `[q 0, q (m+2)]`, and `biResQ'_comp` transports the inductive restriction identities through the two-step restriction to conclude for all `t ≤ m`, with uniqueness inherited from `hfu` and the inductive `hfmu`.
- **Hypotheses**: `q` strictly increasing (via `strictMono_nat_of_lt_succ hlt`) and pointwise positive; consecutive overlap matching conditions.
- **Uses from project**: `BIQ`, `biResQ'`, `biSndQ`, `biFstQ`, `biResQ'_id`, `biResQ'_comp`, `biFstQ_biResQ'_left`, `biResQ'_split_existsUnique`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 567–665 (proof 77 lines)
- **Notes**: proof > 30 lines; the statement itself is ~20 lines because the `biResQ'` call needs six endpoint/monotonicity arguments produced from `strictMono_nat_of_lt_succ hlt`; contains an inline comment at line 602.

---

## Section 6 — topology, uniformity, completeness (lines 667–765)

### `instance : UniformSpace (dyadicVal p F ϖ i)`
- **Type**: `noncomputable instance (i : DyadicIdx) : UniformSpace (dyadicVal p F ϖ i)`
- **What**: Equips each dyadic interval ring with the subspace uniformity it inherits from `BIQ`.
- **How**: `inferInstanceAs` transports the `UniformSpace ↥(BIQ …)` instance across the definitional unfolding of `dyadicVal`.
- **Hypotheses**: ambient perfectoid field.
- **Uses from project**: `dyadicVal`, `BIQ`, `DyadicIdx.q₁`, `DyadicIdx.q₂`, `DyadicIdx.q₁_pos`, `DyadicIdx.q₂_pos`
- **Used by**: consumed by typeclass inference in every later topological statement about `dyadicVal` and in `limitSectionsY`'s product topology
- **Visibility**: public instance (anonymous), `noncomputable`
- **Lines**: 667–672
- **Notes**: none

### `instance : IsTopologicalRing (dyadicVal p F ϖ i)`
- **Type**: `instance (i : DyadicIdx) : IsTopologicalRing (dyadicVal p F ϖ i)`
- **What**: The dyadic interval rings are topological rings.
- **How**: `inferInstanceAs` from the corresponding `BIQ` instance.
- **Hypotheses**: ambient perfectoid field.
- **Uses from project**: `dyadicVal`, `BIQ`, `DyadicIdx.q₁`, `DyadicIdx.q₂`, `DyadicIdx.q₁_pos`, `DyadicIdx.q₂_pos`
- **Used by**: typeclass inference for the `IsTopologicalRing ↥(limitSectionsY …)` instance
- **Visibility**: public instance (anonymous)
- **Lines**: 674–677
- **Notes**: none

### `instance : T2Space (dyadicVal p F ϖ i)`
- **Type**: `instance (i : DyadicIdx) : T2Space (dyadicVal p F ϖ i)`
- **What**: The dyadic interval rings are Hausdorff (separated).
- **How**: `inferInstanceAs` from the `BIQ` instance.
- **Hypotheses**: ambient perfectoid field.
- **Uses from project**: `dyadicVal`, `BIQ`, `DyadicIdx.q₁`, `DyadicIdx.q₂`, `DyadicIdx.q₁_pos`, `DyadicIdx.q₂_pos`
- **Used by**: typeclass inference for `T2Space ↥(limitSectionsY …)`
- **Visibility**: public instance (anonymous)
- **Lines**: 679–682
- **Notes**: none

### `instance : CompleteSpace (dyadicVal p F ϖ i)`
- **Type**: `instance (i : DyadicIdx) : CompleteSpace (dyadicVal p F ϖ i)`
- **What**: The dyadic interval rings are complete — they are closed subrings of complete products.
- **How**: `isClosed_BISub` (closedness of the interval subring inside the ambient complete object, instantiated at the two radii `vpiQ (i.q₁ p)`, `vpiQ (i.q₂ p)`) followed by mathlib's `IsClosed.completeSpace_coe`.
- **Hypotheses**: the radii are in `(0,1)`, supplied by `vpiQ_pos` and `vpiQ_lt_one` at `q₁_pos` / `q₂_pos`.
- **Uses from project**: `dyadicVal`, `isClosed_BISub`, `vpiQ_pos`, `vpiQ_lt_one`, `DyadicIdx.q₁`, `DyadicIdx.q₂`, `DyadicIdx.q₁_pos`, `DyadicIdx.q₂_pos`
- **Used by**: typeclass inference for `CompleteSpace ↥(limitSectionsY …)` (via `isClosed_limitSectionsY`)
- **Visibility**: public instance (anonymous)
- **Lines**: 684–689 (term proof, 4 lines)
- **Notes**: named-argument style (`hρ₁0 := …`) is used to pin the four radius hypotheses.

### `theorem dyadicRes_continuous`
- **Type**: `{i' i : DyadicIdx} (h : DyadicIdx.Nested p i' i) : Continuous (dyadicRes p F ϖ h)`
- **What**: The restriction map between nested dyadic interval rings is continuous.
- **How**: Term-mode instantiation of `biResQ'_continuous` at the four endpoints, with the same positivity / strictness / `mem₁` / `mem₂` package used by `dyadicRes` itself.
- **Hypotheses**: `Nested p i' i`.
- **Uses from project**: `dyadicRes`, `biResQ'_continuous`, `DyadicIdx.Nested`, `DyadicIdx.Nested.mem₁`, `DyadicIdx.Nested.mem₂`, `DyadicIdx.q₁`, `DyadicIdx.q₂`, `DyadicIdx.q₁_pos`, `DyadicIdx.q₂_pos`, `DyadicIdx.q₂_lt_q₁`
- **Used by**: `isClosed_limitSectionsY`
- **Visibility**: public
- **Lines**: 691–697 (term proof, 3 lines)
- **Notes**: none

### `theorem isClosed_limitSectionsY`
- **Type**: `(W : Set (Spv (Ainf p F))) : IsClosed (limitSectionsY p F ϖ W : Set (Π i : {i // dyadicTrace p F ϖ i ⊆ W}, dyadicVal p F ϖ i.1))`
- **What**: The compatibility locus defining the limit sections is closed inside the product of the dyadic interval rings — the topological input to completeness of the presheaf sections.
- **How**: Rewrites the carrier as a triple intersection `⋂ i' ⋂ i ⋂ h, {f | dyadicRes h (f i) = f i'}` (an `ext`/`simp only [Set.mem_iInter]` identity), then applies `isClosed_iInter` three times and closes each equaliser with `isClosed_eq`, whose two continuous maps are `dyadicRes_continuous h ∘ continuous_apply i` and `continuous_apply i'`.
- **Hypotheses**: `W` arbitrary; the Hausdorff instance on `dyadicVal` (needed by `isClosed_eq`).
- **Uses from project**: `limitSectionsY`, `dyadicTrace`, `dyadicVal`, `dyadicRes`, `dyadicRes_continuous`, `DyadicIdx`, `DyadicIdx.Nested`, `Ainf`
- **Used by**: the `CompleteSpace ↥(limitSectionsY …)` instance
- **Visibility**: public
- **Lines**: 699–720 (proof 16 lines)
- **Notes**: none

### `instance : CompleteSpace ↥(limitSectionsY p F ϖ W)`
- **Type**: `instance (W : Set (Spv (Ainf p F))) : CompleteSpace ↥(limitSectionsY p F ϖ W)`
- **What**: The presheaf sections over any `W` form a complete uniform space.
- **How**: `isClosed_limitSectionsY` plus mathlib's `IsClosed.completeSpace_coe` — a closed subspace of a complete space (the product of complete `dyadicVal`s) is complete.
- **Hypotheses**: `W` arbitrary; the per-index `CompleteSpace (dyadicVal …)` instance.
- **Uses from project**: `limitSectionsY`, `isClosed_limitSectionsY`, `Ainf`
- **Used by**: typeclass inference in `yPresheaf` (the `CompleteTopCommRingCat.of` bundling)
- **Visibility**: public instance (anonymous)
- **Lines**: 722–725 (term proof, 1 line)
- **Notes**: none

### `instance : T2Space ↥(limitSectionsY p F ϖ W)`
- **Type**: `instance (W : Set (Spv (Ainf p F))) : T2Space ↥(limitSectionsY p F ϖ W)`
- **What**: The presheaf sections are Hausdorff.
- **How**: `inferInstance` — a subspace of a product of Hausdorff spaces (the `T2Space (dyadicVal …)` instance above) is Hausdorff.
- **Hypotheses**: `W` arbitrary.
- **Uses from project**: `limitSectionsY`, `Ainf`
- **Used by**: typeclass inference in `yPresheaf`
- **Visibility**: public instance (anonymous)
- **Lines**: 727–730 (1 line)
- **Notes**: none

### `instance : IsTopologicalRing ↥(limitSectionsY p F ϖ W)`
- **Type**: `instance (W : Set (Spv (Ainf p F))) : IsTopologicalRing ↥(limitSectionsY p F ϖ W)`
- **What**: The presheaf sections form a topological ring.
- **How**: `inferInstance` — a subring of a product of topological rings inherits the structure from the `IsTopologicalRing (dyadicVal …)` instance.
- **Hypotheses**: `W` arbitrary.
- **Uses from project**: `limitSectionsY`, `Ainf`
- **Used by**: typeclass inference in `yPresheaf`
- **Visibility**: public instance (anonymous)
- **Lines**: 732–735 (1 line)
- **Notes**: none

### `theorem limitRestrictY_continuous`
- **Type**: `{W' W : Set (Spv (Ainf p F))} (hW : W' ⊆ W) : Continuous (limitRestrictY p F ϖ hW)`
- **What**: The presheaf restriction map is continuous, so it is a morphism of topological rings.
- **How**: `Continuous.subtype_mk` reduces to continuity into the product; `continuous_pi` then reduces to each component, which is `continuous_apply _ ∘ continuous_subtype_val` — restriction is just a re-indexed product projection.
- **Hypotheses**: `W' ⊆ W`.
- **Uses from project**: `limitRestrictY`, `limitSectionsY`, `Ainf`
- **Used by**: `yPresheaf`, `yPresheaf_map`
- **Visibility**: public
- **Lines**: 737–744 (proof 3 lines)
- **Notes**: none

### `instance : IsUniformAddGroup ↥(BIQ p F ϖ q₁ q₂ h₁ h₂)`
- **Type**: `instance (q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂) : IsUniformAddGroup ↥(BIQ p F ϖ q₁ q₂ h₁ h₂)`
- **What**: Every interval subring is a uniform additive group, i.e. subtraction is uniformly continuous for the subspace uniformity.
- **How**: `IsUniformInducing.isUniformAddGroup` applied to the subring inclusion `(BIQ …).subtype`, whose uniform-inducing property comes from `isUniformEmbedding_subtype_val.isUniformInducing`.
- **Hypotheses**: `0 < q₁`, `0 < q₂`; the ambient uniform-add-group structure on `B`.
- **Uses from project**: `BIQ`
- **Used by**: the `IsUniformAddGroup (dyadicVal …)` instance below (via `inferInstanceAs`)
- **Visibility**: public instance (anonymous)
- **Lines**: 746–750 (term proof, 2 lines)
- **Notes**: stated for arbitrary rational exponents, not just dyadic ones.

### `instance : IsUniformAddGroup (dyadicVal p F ϖ i)`
- **Type**: `instance (i : DyadicIdx) : IsUniformAddGroup (dyadicVal p F ϖ i)`
- **What**: The dyadic interval rings are uniform additive groups.
- **How**: `inferInstanceAs` transport of the previous `BIQ` instance across `dyadicVal`'s unfolding.
- **Hypotheses**: ambient perfectoid field.
- **Uses from project**: `dyadicVal`, `BIQ`, `DyadicIdx.q₁`, `DyadicIdx.q₂`, `DyadicIdx.q₁_pos`, `DyadicIdx.q₂_pos`
- **Used by**: typeclass inference for the product uniformity on limit sections
- **Visibility**: public instance (anonymous)
- **Lines**: 752–755
- **Notes**: none

### `instance limitSectionsY.isUniformAddGroup`
- **Type**: `instance limitSectionsY.isUniformAddGroup (W : Set (Spv (Ainf p F))) : IsUniformAddGroup ↥(limitSectionsY p F ϖ W)`
- **What**: The presheaf sections are a uniform additive group under the subspace uniformity from the product.
- **How**: Same pattern as the `BIQ` case: `IsUniformInducing.isUniformAddGroup` on the subring inclusion `(limitSectionsY p F ϖ W).subtype`, uniform-inducing via `isUniformEmbedding_subtype_val`.
- **Hypotheses**: `W` arbitrary; the `IsUniformAddGroup (dyadicVal …)` instance for the ambient product.
- **Uses from project**: `limitSectionsY`, `Ainf`
- **Used by**: `limitSectionsY.t0Space` (uniform-group separation), and inference in `yPresheaf`
- **Visibility**: public, named instance
- **Lines**: 757–761 (term proof, 2 lines)
- **Notes**: one of only two *named* instances in the file.

### `instance limitSectionsY.t0Space`
- **Type**: `instance limitSectionsY.t0Space (W : Set (Spv (Ainf p F))) : T0Space ↥(limitSectionsY p F ϖ W)`
- **What**: The presheaf sections are T0 (hence, being a uniform group, Hausdorff).
- **How**: `inferInstance` — derived from the ambient product of `T2Space` dyadic values via the subspace topology.
- **Hypotheses**: `W` arbitrary.
- **Uses from project**: `limitSectionsY`, `Ainf`
- **Used by**: typeclass inference in `yPresheaf`
- **Visibility**: public, named instance
- **Lines**: 763–765 (1 line)
- **Notes**: has no doc-comment (the only declaration in the file without one).

---

## Section 7 — the bundled Y-structure presheaf (lines 767–794)

### `def yPresheaf`
- **Type**: `yPresheaf (p F ϖ) : TopCat.Presheaf CompleteTopCommRingCat (TopCat.of ↥(Y p F ϖ))`
- **What**: **The headline object of the file**: the structure presheaf of `𝒴`, valued in complete topological commutative rings. Over an open `U ⊆ 𝒴` it is the complete topological ring of compatible dyadic families supported inside `U`.
- **How**: `obj V := CompleteTopCommRingCat.of ↥(limitSectionsY p F ϖ (Subtype.val '' V.unop))` — pushing the open forward into `Spv (Ainf p F)` along the subtype inclusion — and `map i := ⟨limitRestrictY (Set.image_mono (leOfHom i.unop)), limitRestrictY_continuous …⟩`. Functoriality (`map_id`, `map_comp`) reduces to `rfl` after `Subtype.ext`/`RingHom.ext`/`funext`, because `limitRestrictY` is pure re-indexing.
- **Hypotheses**: ambient perfectoid field; the complete/Hausdorff/topological-ring instances on `limitSectionsY` supply the `CompleteTopCommRingCat` bundling.
- **Uses from project**: `limitSectionsY`, `limitRestrictY`, `limitRestrictY_continuous`, `Y`, `CompleteTopCommRingCat`
- **Used by**: `yPresheaf_obj`, `yPresheaf_map`
- **Visibility**: public (`noncomputable` by the ambient section)
- **Lines**: 767–781 (definition 11 lines)
- **Notes**: none

### `theorem yPresheaf_obj`
- **Type**: `@[simp] (V : (TopologicalSpace.Opens ↥(TopCat.of ↥(Y p F ϖ)))ᵒᵖ) : (yPresheaf p F ϖ).obj V = CompleteTopCommRingCat.of ↥(limitSectionsY p F ϖ (Subtype.val '' (V.unop.1 : Set ↥(Y p F ϖ))))`
- **What**: Simp-normal-form unfolding of the presheaf's value on an open set.
- **How**: `rfl` — the equation is definitional, packaged as a `@[simp]` lemma so downstream proofs never unfold `yPresheaf` by hand.
- **Hypotheses**: none.
- **Uses from project**: `yPresheaf`, `limitSectionsY`, `Y`, `CompleteTopCommRingCat`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 783–787 (term proof, `rfl`)
- **Notes**: `@[simp]` attribute; the only attribute in the file.

### `theorem yPresheaf_map`
- **Type**: `{V W : (TopologicalSpace.Opens ↥(TopCat.of ↥(Y p F ϖ)))ᵒᵖ} (i : V ⟶ W) (x : ↥(limitSectionsY p F ϖ (Subtype.val '' V.unop))) : ((yPresheaf p F ϖ).map i).1 x = limitRestrictY p F ϖ (Set.image_mono (CategoryTheory.leOfHom i.unop)) x`
- **What**: Unfolding of the presheaf's restriction morphism on elements: it is `limitRestrictY` along the image of the open inclusion.
- **How**: `rfl` — definitional by construction of `yPresheaf.map`.
- **Hypotheses**: `i : V ⟶ W` a morphism of opens (i.e. `W ≤ V` in the opposite category).
- **Uses from project**: `yPresheaf`, `limitRestrictY`, `limitSectionsY`, `Y`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 789–794 (term proof, `rfl`)
- **Notes**: not marked `@[simp]` (asymmetric with `yPresheaf_obj`).

---

### File Summary

- **Total declarations**: 59 (13 defs + 1 structure, 33 lemmas/theorems, 12 instances)
  - defs: `intervalTrace`, `DyadicIdx.q₁`, `DyadicIdx.q₂`, `DyadicIdx.Nested`, `DyadicIdx.splitL`, `DyadicIdx.splitR`, `dyadicVal`, `dyadicRes`, `dyadicTrace`, `limitSectionsY`, `limitRestrictY`, `limitEvalTop`, `yPresheaf`
  - structure: `DyadicIdx`
  - instances: `CommRing (dyadicVal)`, `UniformSpace (dyadicVal)`, `IsTopologicalRing (dyadicVal)`, `T2Space (dyadicVal)`, `CompleteSpace (dyadicVal)`, `IsUniformAddGroup (dyadicVal)`, `IsUniformAddGroup (BIQ)`, `CompleteSpace (limitSectionsY)`, `T2Space (limitSectionsY)`, `IsTopologicalRing (limitSectionsY)`, `limitSectionsY.isUniformAddGroup`, `limitSectionsY.t0Space` (only the last two are named)

- **Key API (used by 3+ others in this file)**:
  `DyadicIdx` (structure — the index type of everything after line 148);
  `DyadicIdx.q₁`, `DyadicIdx.q₂` (the two exponents; each feeds 7+ declarations);
  `DyadicIdx.q₁_pos`, `DyadicIdx.q₂_pos` (positivity side conditions demanded by every `BIQ`/`biResQ'` call);
  `DyadicIdx.q₂_lt_q₁` (strictness, 8 consumers);
  `DyadicIdx.Nested` (the restriction-index relation, 12+ consumers);
  `DyadicIdx.Nested.mem₁` / `mem₂` (3 consumers each: `dyadicRes`, `dyadicRes_comp`, `dyadicRes_continuous`);
  `dyadicVal` (the coefficient ring; every instance and every section statement);
  `dyadicRes` (8 consumers);
  `dyadicTrace` (6 consumers);
  `intervalTrace` (5 consumers);
  `limitSectionsY` (10+ consumers, including all instances and `yPresheaf`);
  `limitRestrictY` (5 consumers).

- **Unused declarations** (no in-file consumer — these are the file's exports):
  `bigWindow_eq_intervalTrace`, `intervalTrace_mono`, `isOpen_intervalTrace_dyadic`,
  `limitRestrictY_id`, `limitRestrictY_comp`, `limitEvalTop_bijective`,
  `exists_unique_dyadicRes_glue`, `biResQ'_chain_glue`, `yPresheaf_obj`, `yPresheaf_map`.
  All 12 instances are "unused" in the literal sense but are consumed by typeclass inference
  (the `dyadicVal` instances feed the product structure on `limitSectionsY`, and the
  `limitSectionsY` instances feed the `CompleteTopCommRingCat.of` bundling in `yPresheaf`).

- **Declarations with `sorry`**: none — the file is sorry-free.

- **Declarations with `set_option`**: none per-declaration. One file-level
  `set_option linter.overlappingInstances false` at line 25 (needed because the ambient
  variable block declares both `[TopologicalSpace F]`/`[UniformSpace F]` and
  `[IsTopologicalRing F]`/`[NonarchimedeanRing F]`). No `maxHeartbeats` bumps anywhere.

- **Proofs > 30 lines**:
  - `biResQ'_chain_glue` — lines 567–665, proof body 77 lines (induction on the chain length)
  - `gaussPoint_mem_intervalTrace_iff` — lines 381–446, proof body 59 lines
  - `intervalTrace_dyadic_eq_rationalOpen` — lines 67–129, proof body 54 lines
  (next longest are `limitEvalTop_bijective` at 22 lines and the `limitSectionsY` subring
  definition at 22 lines, both under the threshold.)


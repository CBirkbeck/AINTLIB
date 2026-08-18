# Inventory — `ForMathlib/CharacterOrthogonality.lean`

Path: `projects/Chebotarev/CebotarevDensity/ForMathlib/CharacterOrthogonality.lean`
Module is `@[expose] public section` + `noncomputable section`. Imports: `Mathlib.GroupTheory.FiniteAbelian.Duality`, `Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`, `Mathlib.Analysis.Complex.Polynomial.Basic`. **This is a `ForMathlib/` file — decls are earmarked for upstreaming, intentionally kept in the root namespace.**

---

### `private theorem sum_eq_zero_of_mulLeft_mul_const_aux`
- **Type**: `{H : Type*} [Group H] [Fintype H] {M₀ : Type*} [Semiring M₀] [IsRightCancelMulZero M₀] (f : H → M₀) (h₀ : H) {c : M₀} (hc : c ≠ 1) (hf : ∀ h, f (h₀ * h) = c * f h) : ∑ h : H, f h = 0`
- **What**: If a function `f` on a finite group `H` valued in a right-cancellative semiring satisfies `f(h₀·h) = c·f(h)` for some fixed `h₀` and scalar `c ≠ 1`, then the total sum `∑ f` is zero.
- **How**: The "translation trick": left-multiplication by `h₀` is a bijection of `H`, so re-indexing the sum gives `∑ f = c·(∑ f)`; then `eq_zero_of_mul_eq_self_left hc` cancels to force the sum to `0`. Hinges on `Group.mulLeft_bijective` and `Fintype.sum_bijective`.
- **Hypotheses**: `H` a finite group; `M₀` a semiring with right cancellation of products by nonzero (`IsRightCancelMulZero`); a fixed element `h₀`; a scalar `c ≠ 1`; the scaling identity `f(h₀·h) = c·f(h)` for all `h`.
- **Uses from project**: `[]`
- **Used by**: `sum_char_apply_eq_zero_of_ne_one`, `sum_char_self_eq_zero_of_ne_one`
- **Visibility**: private
- **Lines**: 37–42 (proof ~3 lines)
- **Notes**: none

### `theorem sum_char_apply_eq_zero_of_ne_one`
- **Type**: `{G : Type*} [CommGroup G] [Finite G] [Fintype (G →* ℂˣ)] {g : G} (hg : g ≠ 1) : ∑ χ : G →* ℂˣ, ((χ g : ℂˣ) : ℂ) = 0`
- **What**: Character-column orthogonality: for a fixed group element `g ≠ 1`, summing the complex value `χ(g)` over all complex characters `χ : G →* ℂˣ` of a finite commutative group gives `0`.
- **How**: Obtains a separating character `χ₀` with `χ₀ g ≠ 1` from `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity` (valid since `ℂ` is algebraically closed ⇒ `HasEnoughRootsOfUnity ℂ`), then applies the aux lemma with `h₀ = χ₀` and `c = χ₀ g`, the scaling coming from `MonoidHom.mul_apply`/`Units.val_mul`.
- **Hypotheses**: `G` a finite commutative group; the character group `G →* ℂˣ` is a `Fintype`; `g ≠ 1`.
- **Uses from project**: `sum_eq_zero_of_mulLeft_mul_const_aux`
- **Used by**: `card_mul_eq_sum_of_sum_char_mul_eq_zero`
- **Visibility**: public
- **Lines**: 44–50 (proof ~3 lines)
- **Notes**: none

### `theorem sum_char_self_eq_zero_of_ne_one`
- **Type**: `{G : Type*} [CommGroup G] [Fintype G] {χ : G →* ℂˣ} (hχ : χ ≠ 1) : ∑ g : G, ((χ g : ℂˣ) : ℂ) = 0`
- **What**: Character-row orthogonality: for a nontrivial complex character `χ ≠ 1` of a finite commutative group, summing `χ(g)` over all group elements `g` gives `0`.
- **How**: Extracts a separating element `g₀` with `χ g₀ ≠ 1` via `DFunLike.ne_iff` (after rewriting `MonoidHom.one_apply`), then applies the aux lemma with `h₀ = g₀` and `c = χ g₀`, the scaling identity coming from `map_mul`/`Units.val_mul`.
- **Hypotheses**: `G` a finite commutative group (`Fintype G`); `χ` a nontrivial character.
- **Uses from project**: `sum_eq_zero_of_mulLeft_mul_const_aux`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 52–59 (proof ~3 lines)
- **Notes**: none

### `theorem card_mul_eq_sum_of_sum_char_mul_eq_zero`
- **Type**: `{G : Type*} [CommGroup G] [Fintype G] [Fintype (G →* ℂˣ)] (f : G → ℂ) (hf : ∀ χ : G →* ℂˣ, χ ≠ 1 → ∑ s : G, ((χ s : ℂˣ) : ℂ) * f s = 0) (u : G) : (Fintype.card (G →* ℂˣ) : ℂ) * f u = ∑ s : G, f s`
- **What**: Finite-abelian Fourier inversion: if every nontrivial character moment `∑ s, χ(s)·f(s)` of `f : G → ℂ` vanishes, then `(#dual)·f(u) = ∑ s f(s)` for every `u` — i.e. `f(u)` equals the average of `f`.
- **How**: Establishes `horth` — the inner character sum `∑_χ χ(u⁻¹·s)` equals `#dual` if `s = u` and `0` otherwise — using `sum_char_apply_eq_zero_of_ne_one`. Then a `calc` chain rewrites the LHS via this indicator, swaps the order of summation (`Finset.sum_comm`), factors `χ(u⁻¹)` out, and collapses the character sum to its `χ = 1` term via `Finset.sum_eq_single_of_mem` together with the hypothesis `hf`.
- **Hypotheses**: `G` finite commutative; dual `G →* ℂˣ` a `Fintype`; `f : G → ℂ` with all nontrivial character moments zero; a point `u`.
- **Uses from project**: `sum_char_apply_eq_zero_of_ne_one`
- **Used by**: `eq_of_sum_char_mul_eq_zero`
- **Visibility**: public
- **Lines**: 61–94 (proof ~25 lines, incl. calc)
- **Notes**: none (proof 30–50? — no, ~25 lines, under 30)

### `theorem eq_of_sum_char_mul_eq_zero`
- **Type**: `{G : Type*} [CommGroup G] [Fintype G] (f : G → ℂ) (hf : ∀ χ : G →* ℂˣ, χ ≠ 1 → ∑ s : G, ((χ s : ℂˣ) : ℂ) * f s = 0) (u u' : G) : f u = f u'`
- **What**: If every nontrivial character moment of `f : G → ℂ` vanishes, then `f` is constant: `f u = f u'` for any two points.
- **How**: Both `f u` and `f u'` equal the common average via `card_mul_eq_sum_of_sum_char_mul_eq_zero`; cancelling the nonzero dual cardinality (`Fintype.card_ne_zero`) by `mul_left_cancel₀` yields equality. Supplies `Fintype (G →* ℂˣ)` locally via `Fintype.ofFinite`.
- **Hypotheses**: `G` finite commutative; `f : G → ℂ` with all nontrivial character moments zero; two points `u, u'`.
- **Uses from project**: `card_mul_eq_sum_of_sum_char_mul_eq_zero`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 96–107 (proof ~5 lines)
- **Notes**: none

---

## File Summary

- **Total decls**: 5 — defs: 0 / lemmas+theorems: 5 / instances: 0. (1 private aux + 4 public theorems.)
- **Key API (used by ≥3 in-file)**: none. Most-used is `sum_eq_zero_of_mulLeft_mul_const_aux` (the private engine, 2 callers).
- **Dependency spine**: `sum_eq_zero_of_mulLeft_mul_const_aux` → {`sum_char_apply_eq_zero_of_ne_one`, `sum_char_self_eq_zero_of_ne_one`}; `sum_char_apply_eq_zero_of_ne_one` → `card_mul_eq_sum_of_sum_char_mul_eq_zero` → `eq_of_sum_char_mul_eq_zero`.
- **Unused in file (leaf decls — public API surface)**: `sum_char_self_eq_zero_of_ne_one`, `eq_of_sum_char_mul_eq_zero`. (Both are intended external/upstream entry points, not dead code.)
- **Decls with `sorry`**: none.
- **Decls with `set_option`**: none.
- **Proofs >50 lines (decompose-needed)**: none.
- **Proofs 30–50 lines**: none. (Longest is `card_mul_eq_sum_of_sum_char_mul_eq_zero` at ~25 lines.)
- **Mathlib-overlap flags (ForMathlib audit)**: The four public theorems are textbook finite-abelian character orthogonality / Fourier inversion and are prime upstream candidates — check before/at PR time:
  - `sum_char_apply_eq_zero_of_ne_one` & `sum_char_self_eq_zero_of_ne_one` — the two standard orthogonality relations for `G →* ℂˣ`. Mathlib has related results for `MonoidHom.toHomUnits`/`AddChar` and `∑ orthogonality` over roots of unity (e.g. `AddChar.sum_eq_zero_of_ne_one`-style lemmas, `MonoidHom.sum_apply_eq_zero`-type results); the complex-character specialisation may already exist or be a thin specialisation. **Verify against mathlib's `AddChar`/character-sum API before upstreaming.**
  - `card_mul_eq_sum_of_sum_char_mul_eq_zero` / `eq_of_sum_char_mul_eq_zero` — Fourier-inversion consequences; less likely to exist verbatim but overlap with `AddChar.inv_apply`/Fourier-inversion machinery is possible.
  - The private aux `sum_eq_zero_of_mulLeft_mul_const_aux` is a clean general "scaling-by-a-non-unit-root forces sum 0" statement over any `IsRightCancelMulZero` semiring — itself plausibly mathlib-worthy and worth checking for an existing analogue.
- **Generality notes (ForMathlib)**: aux lemma is already maximally general (any `Group` + `IsRightCancelMulZero Semiring`). The four public results are hard-wired to `ℂ`; for mathlib they may warrant generalisation to a target field with `HasEnoughRootsOfUnity` / `IsAlgClosed` rather than `ℂ` specifically (the column proof already only uses `HasEnoughRootsOfUnity ℂ`).

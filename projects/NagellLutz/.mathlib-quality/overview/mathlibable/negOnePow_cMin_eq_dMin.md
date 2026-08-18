# Mathlibability assessment: `EllSequence.negOnePow_cMin_eq_dMin`

**Verdict: NO-composable-from-mathlib**

## Declaration

- **Qualified name:** `EllSequence.negOnePow_cMin_eq_dMin`
  (namespace `EllSequence`, opened at line 90 and closed at line 597; the lemma at line 390 lies inside it — *not* inside the later `Rel₄OfValid` section, which only opens at line 412).
- **Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:390`
- **Statement & proof (verbatim):**

```lean
lemma negOnePow_cMin_eq_dMin (a : ℤ) : (cMin a).negOnePow = (dMin a).negOnePow := by
  rw [cMin, Int.negOnePow_add]; exact mul_one _
```

- **Supporting local definitions** (same file):

```lean
/-- The minimal possible fourth index in the four-index elliptic relation given the first index. -/
def dMin (a : ℤ) : ℤ := if Even a then 0 else 1
/-- The minimal possible third index in the four-index elliptic relation given the first index. -/
def cMin (a : ℤ) : ℤ := dMin a + 2
```

## What it says

For the project-local pair `dMin`/`cMin` (which pick the minimal valid fourth/third index of the
four-index elliptic relation `rel₄`, with `cMin a = dMin a + 2`), the lemma records that
`cMin a` and `dMin a` have the *same parity*, phrased via `Int.negOnePow`:
`(cMin a).negOnePow = (dMin a).negOnePow`.

It is internal plumbing: used only at lines 461 and 464 to feed `rel₄_of_fix₂` /
`rel₄_fix₁_of_fix₂` inside `rel₄_of_min₂` (the specialization of the elliptic relation to the
minimal-index case).

## (1) Literature search

`negOnePow` is mathlib's notation `(-1)^n` for `n : ℤ` (the Koszul-sign / parity function from
homological algebra). The proposition "`n+2` and `n` have the same `(-1)`-power" is not a named
result anywhere in the literature — it is the elementary 2-periodicity of `(-1)^n`. WebSearch on
EDS sources (Silverman/Ward/Everest et al.) surfaces parity discussions of EDS *terms*
(`sign(W_n) = (-1)^{parity}`) but nothing resembling this index-bookkeeping identity, which is an
artefact of *this* formalization's `cMin`/`dMin` definitions, not of the mathematics of EDS.
Conclusion: no literature-standard form to match against.

## (2) Mathlib search — is it there, or more general?

The statement mentions `EllSequence.cMin` and `EllSequence.dMin`, which are **project-local
definitions** with no mathlib counterpart. Hence the lemma cannot appear in mathlib verbatim, and
would be meaningless there.

The relevant *general* API is `Mathlib/Algebra/Ring/NegOnePow.lean` (present in this repo at
`.lake/packages/mathlib/Mathlib/Algebra/Ring/NegOnePow.lean`). It already contains everything
needed and more:

- `Int.negOnePow_add (n₁ n₂) : (n₁ + n₂).negOnePow = n₁.negOnePow * n₂.negOnePow` (line 34) — used by the proof.
- `Int.negOnePow_succ`, `negOnePow_even`, `negOnePow_odd`, `negOnePow_two_mul`,
  `negOnePow_two_mul_add_one`, `negOnePow_eq_one_iff`, `negOnePow_eq_neg_one_iff`,
  `negOnePow_neg`, `negOnePow_sub`,
  `negOnePow_eq_iff (n₁ n₂) : n₁.negOnePow = n₂.negOnePow ↔ Even (n₁ - n₂)` (line 98).

Note the project itself already leans on this mathlib API throughout the same file (`negOnePow_add`,
`negOnePow_eq_iff`, `negOnePow_two_mul`, `negOnePow_even`, `negOnePow_odd`, …). There is **no
general "`(n+2).negOnePow = n.negOnePow`" lemma** in mathlib, but it is not worth one: see (4).

## (3) Generality analysis

The lemma is stated for the bespoke functions `cMin a`/`dMin a`. The only mathematical content is
`cMin a = dMin a + 2`, i.e. a statement of the shape `(x + 2).negOnePow = x.negOnePow`. The wrapper
adds nothing reusable beyond unfolding `cMin`; it is strictly less general than the underlying
`Int.negOnePow_add` it is built from. There is no maximally-general form to lift to mathlib that
isn't already there.

## (4) Composition check (≤ 3 mathlib calls)

The in-repo proof is literally a **2-step composition** of existing mathlib primitives:

```lean
rw [cMin, Int.negOnePow_add]   -- (dMin a + 2).negOnePow → (dMin a).negOnePow * (2 : ℤ).negOnePow
exact mul_one _                -- (2 : ℤ).negOnePow reduces to 1, closing the goal
```

Equivalently it is one application of `Int.negOnePow_eq_iff` with `Even ((dMin a + 2) - dMin a)`
discharged by `decide`/`even_two`-style facts. Either way ≤ 3 mathlib calls suffice — in fact 2 do.
The general fact "`negOnePow` is 2-periodic" is an immediate corollary of `negOnePow_add` +
`negOnePow_two_mul` (or `negOnePow_even`), all already in mathlib.

## Verdict

**NO-composable-from-mathlib.** This is a one-line glue lemma about the project-private definitions
`cMin`/`dMin`; it cannot live in mathlib (its statement references local defs) and its content is a
trivial ≤2-call consequence of mathlib's existing `Int.negOnePow` API (`negOnePow_add` + `mul_one`).
Mathlib's `Mathlib/Algebra/Ring/NegOnePow.lean` already provides the full general parity-of-`(-1)^n`
toolkit. Keep it local. (If anything, a tiny general helper `Int.negOnePow_add_two` could be added
upstream, but it is not needed — `negOnePow_add` covers it — and is not what this declaration is.)

### Note
This file is duplicated across the consolidation monorepo (identical lemma at
`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:317` and
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:370`). That is a
within-AINTLIB dedup matter (cleanup-lane), orthogonal to mathlibability.

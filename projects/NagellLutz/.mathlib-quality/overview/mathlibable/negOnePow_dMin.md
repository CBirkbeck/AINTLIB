# Mathlibable assessment — `EllSequence.negOnePow_dMin`

**Verdict: NO-composable-from-mathlib**

**Qualified name:** `EllSequence.negOnePow_dMin`
**Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:393`
**Assessed:** 2026-06-18

---

## 1. The declaration

```lean
namespace EllSequence
-- ...
/-- The minimal possible fourth index in the four-index elliptic relation given the first index. -/
def dMin (a : ℤ) : ℤ := if Even a then 0 else 1

lemma negOnePow_dMin (a : ℤ) : (dMin a).negOnePow = a.negOnePow := by
  rw [dMin]; split_ifs with h
  · simp [Int.negOnePow_even, h]
  · simp [Int.negOnePow_odd, Int.not_even_iff_odd.mp h]
```

### What it says mathematically

`dMin a` is the parity-collapsed representative of `a`: it returns `0` when `a` is even and `1`
when `a` is odd. The lemma states that this representative carries the same sign-character as `a`
under mathlib's `Int.negOnePow` map (`n ↦ (-1)^n ∈ ℤˣ`):

> `(-1)^(dMin a) = (-1)^a`.

This holds trivially: `Int.negOnePow` depends only on the parity of its argument, and `dMin a` is
defined to have the same parity as `a`. The proof is a two-branch case split: even branch reduces
both sides to `1` via `negOnePow_even`; odd branch reduces both to `-1` via `negOnePow_odd`.

### Role in the project

`dMin` (with siblings `cMin = dMin + 2`, `dMin_nonneg`, `dMin_lt_cMin`, `negOnePow_cMin_eq_dMin`,
`negOnePow_cMin`, `dMin_le`) is internal bookkeeping for the **four-index elliptic relation**
`rel₄`: `dMin`/`cMin` pin down the minimal valid third/fourth indices of a strictly-decreasing,
same-parity quadruple. `negOnePow_dMin` is used to discharge the "same parity" side-condition when
descending the recursion (e.g. `dMin_le` and the `Rel₄OfValid` induction). It is plumbing, not a
headline result — it does not even appear in the file's `## Main statements`.

---

## 2. Literature search

- **arXiv math/0402415, "The sign of an elliptic divisibility sequence"** (Silverman–Stephens);
  **arXiv 1702.08102, "The Signs in Elliptic Nets"**; **Wikipedia, "Elliptic divisibility
  sequence."** The genuine sign/parity literature on EDS studies the *sign of the term* `W_n`,
  given by `Sign(W_n) = (-1)^⌊n·b⌋` for an irrational `b` — a deep equidistribution result. This is
  unrelated to the lemma here, which is a one-line parity fact about an `if`-expression.
- There is **no named theorem** in the mathematical literature for "the parity-collapse of `n` has
  the same sign-character as `n`." It is an internal `simp`-style identity, not a citable statement.
- `negOnePow` is not standard mathematical notation; it is mathlib's own device for the
  sign-character `(-1)^n` valued in `ℤˣ` (introduced for the sign rule in homological algebra /
  `CochainComplex`). The "interesting" content lives entirely in mathlib's `negOnePow` API, not in
  this glue lemma.

Conclusion: nothing in the literature corresponds to `negOnePow_dMin` as a standalone result.

---

## 3. Mathlib search (five methods)

Searched mathlib (`.lake/packages/mathlib`, commit pinned by the workspace) by name, by statement
shape, by the API it consumes, and within the fork-source file.

| Method | Result |
|---|---|
| Name (`dMin`, `negOnePow_dMin`, `cMin`) | **Absent** from all of mathlib. `grep` over `.lake/packages/mathlib/Mathlib/` finds zero hits; in particular **zero** hits in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (the file this project forked). `dMin` is defined **only** in the three forked project copies (NagellLutz, NagellLutz/…Original, HasseWeil). |
| Statement shape (`(if Even _ then 0 else 1).negOnePow = _.negOnePow`) | No such lemma; mathlib has no `dMin`-like collapse function to state it about. |
| `Int.negOnePow` API it relies on | **All present** in `Mathlib/Algebra/Ring/NegOnePow.lean`: `negOnePow` (def), `negOnePow_even`, `negOnePow_odd`, `negOnePow_eq_one_iff`, `negOnePow_eq_neg_one_iff`, `negOnePow_add`, `negOnePow_succ`, `negOnePow_two_mul`, etc. |
| Parity helpers it relies on | `Int.not_even_iff_odd` present (`Mathlib/Algebra/Group/Int/Even.lean`, imported by the file). |
| Fork check (project forks `Mathlib.NumberTheory.EllipticDivisibilitySequence`) | The mathlib source file exists and is the fork basis, but it does **not** contain `dMin`/`cMin`/`negOnePow_dMin` — these are additions made in the fork. So this decl is genuinely project-new, **not** a duplicate of an existing mathlib decl. |

So mathlib does **not** already contain this exact lemma (rules out NO-mathlib-has-it), but it
contains every primitive needed to state and prove it in two lines.

---

## 4. Generality analysis

The statement is already as general as it can be *for `dMin`* (universally quantified over `a : ℤ`).
The only generalisation would be to drop `dMin` and state the underlying fact directly — but the
underlying fact *is* the standard `Int.negOnePow` parity API, which mathlib already has in maximally
general form. There is no more-general, literature-standard statement that this is a special case of:
`dMin` is a bespoke index-selector for the `rel₄` machinery with no independent mathematical life.

A mathlib-shaped restatement ("for any function picking a same-parity representative, `negOnePow`
agrees") would be artificial generalisation of plumbing — not warranted.

---

## 5. Composition check (≤ 3 mathlib calls?)

**Yes — the lemma *is* the composition.** Modulo the `split_ifs` on the `if` in `dMin`'s own
definition (which only exists because `dMin` is project-local), each branch is a single mathlib
rewrite:

- even branch: `Int.negOnePow_even` (twice — applied to `dMin a = 0` and to `a`), parity supplied
  by hypothesis `h`;
- odd branch: `Int.negOnePow_odd` (twice), parity supplied by `Int.not_even_iff_odd.mp h`.

That is exactly the existing 2-line proof: 2–3 mathlib lemma applications per branch and a case
split. Any downstream consumer in mathlib (were `dMin` ever upstreamed) could inline this with
`by rw [dMin]; split_ifs <;> simp [Int.negOnePow_even, Int.negOnePow_odd, Int.not_even_iff_odd.*]`.
No new API is required.

---

## 6. Five-bucket verdict

**NO-composable-from-mathlib.**

Two independent reasons, either sufficient:

1. **Statement is not mathlib-bound.** `negOnePow_dMin` mentions the project-private definition
   `dMin`, which has no place in mathlib (it is index bookkeeping for one project's `rel₄` proof).
   A lemma whose *statement* references a symbol mathlib lacks cannot be contributed as-is.
2. **Content is a trivial composition of existing mathlib API.** Stripped of `dMin`, the
   mathematical content is "`negOnePow` depends only on parity," already covered exhaustively by
   `Int.negOnePow_even` / `negOnePow_odd` / `negOnePow_eq_one_iff` in
   `Mathlib/Algebra/Ring/NegOnePow.lean`. The proof composes ≤3 of these per branch.

Not **NO-mathlib-has-it**: the *exact* lemma is absent from mathlib (it is a fork addition).
Not **YES-***: nothing here is a missing general fact; it is project glue.
Not **BORDERLINE**: the call is unambiguous.

**Recommendation:** keep `negOnePow_dMin` local to the project (alongside `dMin`/`cMin`). No mathlib
PR. If anything is ever upstreamed from this neighbourhood it would be the `dMin`/`cMin`/`rel₄`
framework as a whole (a separate, much larger question), at which point this lemma rides along as a
trivial private helper — not as an independent contribution.

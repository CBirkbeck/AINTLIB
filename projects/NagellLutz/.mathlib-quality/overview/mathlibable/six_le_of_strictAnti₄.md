# Mathlibable assessment — `EllSequence.HaveSameParity₄.six_le_of_strictAnti₄`

**Verdict: NO-composable-from-mathlib**

## 0. Declaration under assessment

- **Parsed/verified qualified name:** `EllSequence.HaveSameParity₄.six_le_of_strictAnti₄`
  - `namespace EllSequence` (line 90) → `namespace HaveSameParity₄` (line 216), inside `section transf` (line 202).
- **Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:252`
- **Statement (verbatim):**
  ```lean
  variable {W a b c d} (same : HaveSameParity₄ a b c d)
  include same

  lemma six_le_of_strictAnti₄ (anti : StrictAnti₄ a b c d) : 6 ≤ a := by
    simp_rw [HaveSameParity₄, negOnePow_eq_iff] at same
    obtain ⟨hd, hdc, hcb, hba⟩ := anti
    rw [← add_two_le_iff_lt_of_even_sub] at hdc hcb hba
    · linarith
    exacts [same.1, same.2.1, same.2.2]
  ```
- **Supporting project-local definitions (same file):**
  - `StrictAnti₄ a b c d : Prop := 0 ≤ d ∧ d < c ∧ c < b ∧ b < a`  (line 207)
  - `HaveSameParity₄ a b c d : Prop := a.negOnePow = b.negOnePow ∧ b.negOnePow = c.negOnePow ∧ c.negOnePow = d.negOnePow`  (line 210)

## 1. What the statement says (mathematics)

Given four integers `a > b > c > d ≥ 0` (`StrictAnti₄`) that are **all of the same parity**
(`HaveSameParity₄` — encoded as equal `Int.negOnePow`), the largest, `a`, is at least `6`.

Reasoning: same parity ⇒ each consecutive difference is even; a strict inequality `x < y` with
`Even (y − x)` upgrades to `x + 2 ≤ y`. So `d ≥ 0`, `c ≥ d+2 ≥ 2`, `b ≥ c+2 ≥ 4`, `a ≥ b+2 ≥ 6`.

This is the **base case of the strong induction** in the file's main recurrence proof: in
`rel₄_of_anti_oddRec_evenRec` (line 477) the conclusion `Rel₄OfValid W a b c d` is established by
`Int.strongRec (m := 6)`, and `six_le_of_strictAnti₄` is exactly what makes the `a < 6` range
**vacuous** (line 482: `absurd ha (not_lt.mpr (same.six_le_of_strictAnti₄ anti))`).

## 2. Literature search

This is not a named theorem. It is an elementary "spacing" counting fact: `n` strictly decreasing,
same-parity, nonnegative integers force the maximum to be `≥ 2(n−1)` (here `n = 4` ⇒ `6`). No
textbook or paper states it as a citable result; it is bespoke arithmetic bookkeeping internal to
the Ward-recurrence induction set-up (cf. M. Ward, *Memoir on Elliptic Divisibility Sequences*,
the file's cited reference, which does not isolate such a lemma).

- WebSearch ("mathlib strictly decreasing integers same parity lower bound spacing two lemma") —
  no matching named result; only generic `Int.parity` docs and unrelated analytic-number-theory
  gap papers. Confirms there is nothing to cite and nothing standard to generalise *to*.

## 3. Mathlib search (five methods)

Target the **residual** content (the local predicates dissolve to mathlib atoms).

| # | Method | Query | Result |
|---|--------|-------|--------|
| A | Exact name | `six_le_of_strictAnti₄`, `strictAnti`, `HaveSameParity` | no hit in mathlib; names exist only in this project + the HasseWeil sibling copy |
| B | mathlib EDS file | grep `rel₄ / addMulSub / HaveSameParity₄ / StrictAnti₄ / six_le_of_strictAnti` in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` | **0 hits** — upstream EDS file (547 lines) is the small `IsEllSequence`/`normEDS`/`preNormEDS` version; the entire `rel₄`/`net`/`HaveSameParity₄`/transformation apparatus (project file: 1667 lines) is **not upstreamed** |
| C | Whole-mathlib grep | `six_le_of_strictAnti`, `HaveSameParity₄`, `StrictAnti₄` over `.lake/packages/mathlib/Mathlib/` | **0 hits** |
| D | Atom search | the one nontrivial ingredient | **`Int.add_two_le_iff_lt_of_even_sub` IS in mathlib** — `Mathlib/Algebra/Order/Ring/Int.lean:56`; the project *imports and reuses* it (does not re-prove). Also `Int.negOnePow_eq_iff` — `Mathlib/Algebra/Ring/NegOnePow.lean:98` |
| E | Name-pattern / loogle | a packaged "`n` decreasing same-parity nonneg ⇒ max ≥ 2(n−1)" lemma | none; the atoms above plus `linarith` are all that exist, and that is the right granularity |

**Conclusion of search:** the lemma itself is absent from mathlib, but it is *not* a missing
primitive — its only nontrivial step already lives in mathlib.

## 4. Generality analysis

- The statement is **maximally specialised by design**: arity exactly 4, bound exactly `6`, phrased
  over two project-local `Prop`s (`StrictAnti₄`, `HaveSameParity₄`) tailored to the `strongRec`
  base index `m := 6`.
- A mathlib-shaped generalisation ("`n` strictly decreasing same-parity nonnegatives ⇒ max
  `≥ 2(n−1)`") is *possible* but is a synthetic exercise with **no consumer** and no literature
  demand — generalising would be speculative, not value-adding. (Sibling reports reach the same
  conclusion for `StrictAnti₄`/`HaveSameParity₄`: they are project glue, not upstream-bound.)

## 5. Composition check (can ≤ 3 mathlib calls give it?)

Once the project-local predicates are unfolded (they are pure conjunctions; `HaveSameParity₄`
unfolds via `Int.negOnePow_eq_iff` to three `Even (· − ·)`), the proof **is** a ≤3-call mathlib
composition — exactly as written:

```text
1. Int.negOnePow_eq_iff           -- same parity ⇒ Even (b−a), Even (c−b), Even (d−c)
2. Int.add_two_le_iff_lt_of_even_sub  ×3  -- each strict gap ⇒ +2 jump   (Mathlib/Algebra/Order/Ring/Int.lean:56)
3. linarith                       -- 0 ≤ d, d+2 ≤ c, c+2 ≤ b, b+2 ≤ a ⊢ 6 ≤ a
```

No new mathlib API is required; the mathematically load-bearing inequality
(`add_two_le_iff_lt_of_even_sub`) is **already a mathlib lemma**. The wrapper exists only to bundle
this 5-line composition against the file's bespoke predicates so the `Int.strongRec (m := 6)` base
case reads cleanly. That is the definition of **composable-from-mathlib**.

## 6. Consumers (project-internal only)

- `EllipticDivisibilitySequence.lean:482` — base case of `rel₄_of_anti_oddRec_evenRec`'s
  `Int.strongRec (m := 6)`.
- A verbatim sibling copy exists in `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:210`
  (same dup track) used at its line 400 — same role.
- No external/library-facing use; it is a private stepping-stone bound to `StrictAnti₄` /
  `HaveSameParity₄`.

## 7. Verdict

**NO-composable-from-mathlib.**

Evidence:
- (M5) Mathlib's primitives compose to it in ≤3 calls — the exact in-file proof is
  `negOnePow_eq_iff` → `add_two_le_iff_lt_of_even_sub ×3` → `linarith`, all mathlib.
- The single nontrivial arithmetic ingredient, `Int.add_two_le_iff_lt_of_even_sub`, **already exists
  in mathlib** (`Mathlib/Algebra/Order/Ring/Int.lean:56`) and is reused, not re-proved.
- The lemma is bespoke glue: a degree-4, bound-6 counting fact phrased over project-local predicates,
  serving only as the vacuous base case of a `strongRec`. No literature names it; mathlib does not
  contain it and does not need it.

If `EllSequence`'s whole Ward-recurrence development (`rel₄`/`net`/`addMulSub`/`HaveSameParity₄`/…)
were ever upstreamed wholesale, this lemma would ride along as a one-liner private helper — but on
its own it is **not** a mathlib contribution.

### Mathlib decls relied upon
- `Int.add_two_le_iff_lt_of_even_sub` — `Mathlib/Algebra/Order/Ring/Int.lean:56`
- `Int.negOnePow_eq_iff` — `Mathlib/Algebra/Ring/NegOnePow.lean:98`
- `linarith`

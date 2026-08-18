# Mathlibable assessment: `EllSequence.HaveSameParity₄.avg₄_add_avg₄`

- **Project:** NagellLutz (Nagell–Lutz; elliptic curves; division polynomials; EDS)
- **File:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:232`
- **Date:** 2026-06-18
- **Verdict:** **NO-composable-from-mathlib** (borderline with NO-mathlib-has-it)

---

## 1. The declaration (verified from source)

True qualified name (file opens `namespace EllSequence`, then inside it `namespace HaveSameParity₄`):

```
EllSequence.HaveSameParity₄.avg₄_add_avg₄
```

Statement and proof (lines 232–233), in scope of `variable {W a b c d} (same : HaveSameParity₄ a b c d)` with `include same`:

```lean
lemma avg₄_add_avg₄ : avg₄ a b c d + avg₄ a b c d = a + b + c + d := by
  rw [← two_mul]; exact Int.mul_ediv_cancel' same.even_sum.two_dvd
```

Supporting local definitions:

```lean
/-- The average of four indices. -/
def avg₄ : ℤ := (a + b + c + d) / 2          -- integer ediv

/-- The proposition that the four indices are of the same parity. -/
def HaveSameParity₄ : Prop :=
  a.negOnePow = b.negOnePow ∧ b.negOnePow = c.negOnePow ∧ c.negOnePow = d.negOnePow

lemma even_sum : Even (a + b + c + d) := by ...   -- line 228
```

So the lemma asserts: when the four integer indices share a parity (hence their sum is even),
`(a+b+c+d)/2 + (a+b+c+d)/2 = a+b+c+d`. It is a one-line convenience wrapper used to discharge
the `addMulSub_transf` / `strictAnti₄_transf` index manipulations downstream.

This is part of David Kurniadi Angdinata's division-polynomial *transformation* machinery
(`avg₄`, `HaveSameParity₄`, `addMulSub`, `net`, `rel₄`, `transf`) — the same code that backs
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`, here forked into the project.

## 2. Literature search

WebSearch over "elliptic divisibility sequence / division polynomial / average of four indices of
same parity": the EDS/division-polynomial literature (Ward; Stange, *Elliptic nets*; Silverman;
Stange 2025 *Division polynomials for arbitrary isogenies*) contains **no named result** of this
shape. The four-index *average* `avg₄` and the `HaveSameParity₄` predicate are bespoke
formalisation scaffolding for re-indexing the EDS quartic relation; the arithmetic fact
"twice the average of an even sum equals the sum" is too trivial to be named anywhere.

Sources:
- Elliptic divisibility sequence — Wikipedia: https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence
- Mathlib.NumberTheory.EllipticDivisibilitySequence docs: https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html
- K. Stange, Division polynomials for arbitrary isogenies: https://eprint.iacr.org/2025/521.pdf

## 3. Mathlib search (five methods)

Searched the forked-and-original mathlib files and core:

- **Forked files** `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` and
  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean`: **no**
  `avg₄`, `avg4`, `HaveSameParity`, `StrictAnti₄`, or `avg₄_add_avg₄`. This transformation layer
  is *not* upstreamed — it lives only in the NagellLutz (and HasseWeil) forks. So the **specific
  wrapper is not in mathlib**.
- **The mathematical core, however, IS in mathlib**, essentially verbatim:

  ```
  Mathlib/Algebra/Group/Int/Even.lean:76
  lemma Int.two_mul_ediv_two_of_even : Even n → 2 * (n / 2) = n := by grind
  ```

  After `rw [← two_mul]` the goal is `2 * ((a+b+c+d)/2) = a+b+c+d`, which is exactly
  `Int.two_mul_ediv_two_of_even (n := a+b+c+d) same.even_sum`. The project file *already imports
  and uses this lemma directly* — see line 223, `have h := @Int.two_mul_ediv_two_of_even` inside
  `rel₄_eq_net`.
- The proof as written instead routes through `Int.mul_ediv_cancel'`
  (`a ∣ b → a * (b / a) = b`), a long-standing mathlib lemma used throughout mathlib
  (e.g. `NumberTheory/PythagoreanTriples.lean:187`, `NumberTheory/SumFourSquares.lean:52,179`,
  `Data/Int/ModEq.lean:222`). Either lemma closes the goal in one call.

Conclusion: mathlib has the content (two equivalent primitives), but **not** this exact
statement, because the statement is phrased on the project-local `avg₄` and is gated by the
project-local `HaveSameParity₄`.

## 4. Generality analysis

The lemma is **strictly less general** than what mathlib already provides:

- It hardcodes the project definition `avg₄ a b c d = (a+b+c+d)/2`. Unfold `avg₄` and it is just
  `Int.two_mul_ediv_two_of_even` on `a+b+c+d`.
- It carries a *redundant, stronger* hypothesis: `HaveSameParity₄ a b c d` (all four `negOnePow`s
  equal). The only fact consumed is `Even (a+b+c+d)` (via `same.even_sum`). The mathlib primitive
  asks for exactly `Even n` — nothing more.
- The `x + x` left-hand side (vs `2 * x`) is cosmetic; the proof's first step is literally
  `rw [← two_mul]`.

There is no generalisation that would make this mathlib-worthy: the maximally-general form is
already in mathlib (`Int.two_mul_ediv_two_of_even`), and the only thing this adds is the bespoke
`avg₄` wrapper — which is project-specific and not independently meaningful.

## 5. Composition check (≤ 3 mathlib calls?)

**Yes — 1 call.** The proof itself is the witness:

```lean
rw [← two_mul]; exact Int.two_mul_ediv_two_of_even same.even_sum
-- or, as written upstream:
rw [← two_mul]; exact Int.mul_ediv_cancel' same.even_sum.two_dvd
```

A single mathlib lemma after one cosmetic rewrite. Every downstream caller
(`addMulSub_transf`, `strictAnti₄_transf`) could inline this just as cheaply, and the file
already uses the same primitive directly elsewhere.

## 6. Verdict

**NO-composable-from-mathlib.**

The lemma is a one-line private convenience wrapper: unfold the project-local `avg₄` and it is
`Int.two_mul_ediv_two_of_even` / `Int.mul_ediv_cancel'` (mathlib) applied to `same.even_sum`,
behind a redundant `HaveSameParity₄` hypothesis. Nothing here belongs in mathlib on its own —
`avg₄` and `HaveSameParity₄` are bespoke division-polynomial re-indexing scaffolding, and the
arithmetic kernel is already upstream.

It sits on the **NO-mathlib-has-it / NO-composable-from-mathlib** boundary: the *content* is in
mathlib (`two_mul_ediv_two_of_even`), so "mathlib has it" is morally true; but because the
declaration as stated is a project-local wrapper around `avg₄` rather than the bare mathlib
lemma, **composable-from-mathlib** is the precise call. Either way the action is the same:
**keep it project-local; do not PR**. If anything, downstream uses could call
`Int.two_mul_ediv_two_of_even same.even_sum` directly and drop the wrapper (a `/cleanup`-grade
golf, not a mathlib contribution).

### Recommended action
- Do **not** submit to mathlib.
- Optional local cleanup: inline `Int.two_mul_ediv_two_of_even same.even_sum` at the two call
  sites, or keep the wrapper for readability — purely a project style choice.

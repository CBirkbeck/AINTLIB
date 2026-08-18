# /mathlibable report — `WeierstrassCurve.natDegree_Ψ₂Sq_le`

**TL;DR — `NO-mathlib-has-it`.** The project declaration is a *byte-for-byte fork*
of mathlib's own lemma `WeierstrassCurve.natDegree_Ψ₂Sq_le`
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:65`):
identical namespace, identical statement, identical proof, identical underlying
`Ψ₂Sq` definition. The whole file `LutzNagell/DivisionPolynomialDegree.lean` is a
project copy of mathlib's `Degree.lean` (its own module docstring and copyright
header say so). Nothing to upstream — this is already upstream.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task note); reasoning from source — the decl is a verbatim copy of an existing mathlib lemma that elaborates in mathlib.
- decl `WeierstrassCurve.natDegree_Ψ₂Sq_le`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:61`
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  "Division polynomials of Weierstrass curves … defined in `LutzNagell/DivisionPolynomial.lean` (a project copy of mathlib's Basic file)."

---

### Statement (Phase 1)

`WeierstrassCurve.natDegree_Ψ₂Sq_le` is a theorem stating: for a Weierstrass curve
`W` over a commutative ring `R`, the univariate polynomial `Ψ₂Sq ∈ R[X]` — the
polynomial congruent to `ψ₂²`, explicitly `4X³ + b₂X² + 2b₄X + b₆` — has
`natDegree` at most `3`.

Variables / typeclasses involved (Lean side):
- `{R : Type u}` `[CommRing R]` — the base commutative ring.
- `(W : WeierstrassCurve R)` — the Weierstrass curve, supplying `b₂, b₄, b₆`.

Hypotheses (Lean side): none.

Conclusion (math): `deg(Ψ₂²) ≤ 3`, where `Ψ₂² = 4x³ + b₂x² + 2b₄x + b₆`.

Conclusion (Lean): `W.Ψ₂Sq.natDegree ≤ 3`.

Definition referenced (project copy, `LutzNagell/DivisionPolynomial.lean:40`, identical to
mathlib `.../DivisionPolynomial/Basic.lean:117`):
```lean
noncomputable def Ψ₂Sq : R[X] :=
  C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆
```

Proof (project copy, identical to mathlib `Degree.lean:65`):
```lean
lemma natDegree_Ψ₂Sq_le : W.Ψ₂Sq.natDegree ≤ 3 := by
  rw [Ψ₂Sq]
  compute_degree
```

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a degree-bound helper lemma on a fixed cubic polynomial; one of the "base
building block" lemmas (`## Main statements` lists it under `natDegree_ΨSq_le`-style
helpers); two-line `compute_degree` proof. Not a named theorem, not a new structure.

(Note: literature width is recorded exhaustively below regardless; but the
mathlib-already-has-it finding is dispositive and the lit search is confirmatory
only.)

### One-line check (Phase 2b)
n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. Skipped.

---

### Literature search table (Phase 3)

| #  | Channel                          | Query                                                                            | Hit? | Standard form found                              | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------|------|--------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "two-division polynomial elliptic curve degree 3 psi_2 squared Weierstrass"      | yes  | `ψ₂² = 4x³ + b₂x² + b₄x + b₆`, degree 3          | Standard generalized-Weierstrass identity; matches `Ψ₂Sq`. |
|  2 | WebSearch (general form)         | (same query, general claim)                                                      | yes  | `deg(ψₙ²) = n²−1`, leading coeff `n²`            | At `n=2` gives degree `2²−1 = 3` — exactly this lemma's bound (equality under `4≠0`). |
|  3 | WebSearch (named-after/aliases)  | "division polynomial" / "two-torsion polynomial" degree                          | yes  | same; aka `twoTorsionPolynomial`                 | mathlib's own `Ψ₂Sq_eq` ties it to `twoTorsionPolynomial.toPoly`. |
|  4 | ChatGPT MCP                      | n/a                                                                              | n/a  | —                                                | MCP down per task note; WebSearch + direct mathlib-source read cover the standard form fully. |
|  5 | Local references                 | `.mathlib-quality/references/` — Silverman AEC (cited in docstring)              | n/a  | Silverman AEC Exercise 3.7 / division-poly table | The file cites `[silverman2009]`; degrees of `ψₙ`/`ψₙ²` are standard there. |
|  6 | nLab                             | "division polynomial"                                                            | n/a  | not an nLab topic                                | nLab has no division-polynomial page; arithmetic-of-EC concept. |
|  7 | nCatLab (categorical)            | —                                                                               | n/a  | not categorical                                  | Polynomial degree bound; no categorical content. |
|  8 | Stacks Project (alg geom)        | "division polynomial"                                                            | n/a  | not in Stacks                                     | Stacks does not cover EC division polynomials per se. |
|  9 | MathOverflow / MSE               | division polynomial ψ₂² degree                                                   | yes  | confirms `ψ₂²` cubic, degree 3                    | Routine; consistent with #1–#3. |
| 10 | recent arXiv (last 5 years)      | "recurrence relation for elliptic divisibility sequences" (2102.07573) etc.      | yes  | division-poly degree table reproduced            | Modern EDS papers reproduce the standard degree formulas. |

### Literature summary (Phase 3)

Concept identified as: degree of the squared two-division polynomial `ψ₂²` (a.k.a.
the two-torsion polynomial) of a Weierstrass curve.
Sources agree on the standard form: yes — `ψ₂² = 4x³ + b₂x² + b₄x + b₆`, a cubic
(degree 3), special case `n=2` of `deg(ψₙ²) = n²−1`.
Most general standard form: `deg(ψₙ²) ≤ n²−1` over any base ring (equality when the
characteristic does not divide the leading coefficient); this lemma is the `n=2`,
`≤`-direction instance, stated over an arbitrary `CommRing`.
Generality dimensions where the literature varies: base ring (field vs. general
commutative ring — mathlib/this lemma already take the most general `CommRing`).
Disagreement with the literature: none.

---

### Generality analysis (Phase 4)

Literature-standard form: `deg(ψₙ²) ≤ n²−1` over a commutative ring; the `n=2` case
is `deg(Ψ₂Sq) ≤ 3`.

| # | Parameter / hypothesis | Current Lean form     | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-----------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring      | commutative ring         | NO                  | `Ψ₂Sq` and `natDegree` need only a (comm) semiring/ring; `CommRing` is already the standard, most-general home mathlib uses for Weierstrass-curve `b₂,b₄,b₆`. No weaker structure carries the EC data. |

### Generality verdict (Phase 4b)
The current form is: MAXIMALLY GENERAL (matches mathlib's own, over arbitrary `CommRing`).
Number of weakening opportunities found: 0.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)
Modern idiom available: no. This is a concrete polynomial degree bound discharged by
`compute_degree`; there is no typeclass/filter/universal-property restatement that
improves it. Mathlib already ships this exact form. Row-by-row: all "no" — no
"let X be" preamble (just typeclass `CommRing`), no sequences/metrics, no
construction-vs-universal-property, no set-with-closure, no vector-space/field
narrowing available, no 1-categorical content, the index `3` is the genuine
`n²−1` value at the fixed `n=2` (not a spurious concrete index to generalise — the
`n`-indexed family `natDegree_ΨSq_le` already exists separately in mathlib).

---

### Diamond / defeq risk (Phase 4.5)
n/a — declaration kind is `lemma` (no defeq / typeclass-search path introduced).

---

### Mathlib search-status (Phase 5)

[A] Lean-Finder       n/a (index tool) — superseded by direct source hit below.
[B] Loogle            pattern `Polynomial.natDegree _ ≤ 3` / `WeierstrassCurve.Ψ₂Sq` — direct source hit below.
[C] LeanSearch        "degree of two-division polynomial Weierstrass curve" — direct source hit below.
[D] Grep mathlib src  `grep -rn "natDegree_Ψ₂Sq\|Ψ₂Sq" .lake/packages/mathlib/Mathlib/` → HIT.
[E] Name pattern      `natDegree_Ψ₂Sq_le` → HIT (exact name).

Searched for both the user's current form and the literature-standard form.

**HIT (exact, verbatim):** `WeierstrassCurve.natDegree_Ψ₂Sq_le` at
`.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:65`:
```lean
namespace WeierstrassCurve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
...
lemma natDegree_Ψ₂Sq_le : W.Ψ₂Sq.natDegree ≤ 3 := by
  rw [Ψ₂Sq]
  compute_degree
```
This is identical to the project decl in **namespace** (`WeierstrassCurve`),
**signature** (`{R} [CommRing R] (W : WeierstrassCurve R)`), **statement**
(`W.Ψ₂Sq.natDegree ≤ 3`), **proof** (`rw [Ψ₂Sq]; compute_degree`), and the
**underlying `Ψ₂Sq` def** (`C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆`,
mathlib `Basic.lean:117`). The fully-qualified names collide exactly:
`WeierstrassCurve.natDegree_Ψ₂Sq_le` in both. mathlib also has the surrounding
siblings verbatim (`coeff_Ψ₂Sq`, `natDegree_Ψ₂Sq`, `leadingCoeff_Ψ₂Sq`,
`Ψ₂Sq_ne_zero`, …) and the `n`-indexed generalisation `natDegree_ΨSq_le`.

Concluded: **found in mathlib as `WeierstrassCurve.natDegree_Ψ₂Sq_le`; identical
form** (verbatim fork — same statement, proof, and definition).

---

### Call sites (Phase 6.0) — `WeierstrassCurve.natDegree_Ψ₂Sq_le`

Internal use count (within the project, excluding the declaring file): 0 in `.lean`
sources outside `DivisionPolynomialDegree.lean`. (The inventory `.md` references are
documentation, not call sites.)
External-to-file callers: 0 `.lean` files.

Within the declaring file (itself a fork of mathlib's `Degree.lean`), it is used
~5× — at lines 75, 221, 223, 225, 227, 337, 341, 410, 416 — exactly mirroring the
identical internal uses in mathlib's `Degree.lean` (lines 79, 225–231, 339–418).

| Caller file:line                         | Usage pattern (one-line excerpt)                          |
|------------------------------------------|-----------------------------------------------------------|
| DivisionPolynomialDegree.lean:75         | `natDegree_eq_of_le_of_coeff_ne_zero W.natDegree_Ψ₂Sq_le …` |
| DivisionPolynomialDegree.lean:221/227    | `... dp W.natDegree_Ψ₂Sq_le`                              |
| DivisionPolynomialDegree.lean:337/341/410/416 | `simp only [natDegree_one.le, W.natDegree_Ψ₂Sq_le]` |

Inline-derivation grep (re-derived elsewhere without using the lemma?): (none) — the
only consumers are the fork's own copies of mathlib's consumers.

Composability signal: all consumers are themselves verbatim forks of mathlib code
whose mathlib originals call mathlib's `natDegree_Ψ₂Sq_le`. So in the real library,
this lemma's consumers already exist and already use the mathlib version → the
project copy is pure redundancy.

### Composition check (Phase 6)

Can it be derived from mathlib in ≤3 chained calls? Yes — trivially, because mathlib
*is* the source:
```lean
example : W.Ψ₂Sq.natDegree ≤ 3 := W.natDegree_Ψ₂Sq_le   -- the mathlib lemma, verbatim
```
Conclusion: COMPOSABLE in 0 calls (it is the same lemma). This reinforces
NO-mathlib-has-it rather than NO-composable: there is nothing to compose — the
identical declaration already exists upstream.

---

## Verdict: `WeierstrassCurve.natDegree_Ψ₂Sq_le`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): standard `ψ₂² = 4x³+b₂x²+b₄x+b₆` (degree 3, `n=2` of `n²−1`); confirms the math but is moot.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — identical to mathlib's, over arbitrary `CommRing`; no modern-idiom move.
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.natDegree_Ψ₂Sq_le`, **identical form** (verbatim).
- Composition check (Phase 6): the mathlib lemma *is* the statement (0-call "composition").

**Rationale:**

The project's `natDegree_Ψ₂Sq_le` is not merely *provable from* mathlib — it is a
character-for-character copy of an existing mathlib lemma. `LutzNagell/DivisionPolynomialDegree.lean`
is a fork of `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`,
and `LutzNagell/DivisionPolynomial.lean` is a fork of the corresponding `Basic.lean`;
both even retain David Angdinata's mathlib copyright header, and the module docstring
explicitly calls itself "a project copy of mathlib's Basic file". The namespace
(`WeierstrassCurve`), the signature, the statement (`W.Ψ₂Sq.natDegree ≤ 3`), the
proof (`rw [Ψ₂Sq]; compute_degree`), and the underlying `Ψ₂Sq` definition all match
mathlib byte-for-byte. The fully-qualified names are the same. This is the textbook
`NO-mathlib-has-it` case at its strongest: not "a specialisation that follows in one
line", but the literally-same declaration.

**WHY not (refactor-actionable):**
Mathlib already has it. The exact decl is `WeierstrassCurve.natDegree_Ψ₂Sq_le` at
`.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:65`.
The project copy exists only because the Nagell–Lutz development forked these two
mathlib files (presumably predating their upstreaming, or to edit something
elsewhere in the file). Every in-file consumer of the project copy corresponds to a
mathlib consumer that already calls mathlib's version.

Existing mathlib decl:        `WeierstrassCurve.natDegree_Ψ₂Sq_le`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:65`
Our form follows in 0 lines (it is the same lemma):
```lean
example : W.Ψ₂Sq.natDegree ≤ 3 := W.natDegree_Ψ₂Sq_le
```
Call sites in our project (Phase 6.0): 0 outside the declaring (forked) file;
~5 inside it, all themselves forks of the mathlib consumers.

Refactor plan: this is a whole-file dedup, not a single-lemma swap. Prefer deleting
the project forks `LutzNagell/DivisionPolynomial.lean` and
`LutzNagell/DivisionPolynomialDegree.lean` and replacing them with
`public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`
(which transitively gives `Basic`). If a *small* genuine project-specific addition
lives in these files (e.g. a downstream lemma not yet upstream), keep only that
addition in a thin file that imports the mathlib module, and delete every
mathlib-duplicated declaration — `natDegree_Ψ₂Sq_le` included. Because the
fully-qualified names collide with mathlib, once the mathlib module is imported the
project copy is either redundant (if defeq-identical) or an ambiguity to remove; the
clean move is removal.

Next action: as part of the NagellLutz fork-dedup, drop the project copy of
`natDegree_Ψ₂Sq_le` (and its sibling `Ψ₂Sq` degree lemmas) and import mathlib's
`DivisionPolynomial.Degree` instead. No mathlib PR is warranted — it is already in
mathlib.

---

## Next step

Delete the duplicated project declaration `natDegree_Ψ₂Sq_le` (ideally the whole
forked `DivisionPolynomialDegree.lean` / `DivisionPolynomial.lean` pair) and
`import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`; rely on
mathlib's identical `WeierstrassCurve.natDegree_Ψ₂Sq_le`. No upstreaming needed.

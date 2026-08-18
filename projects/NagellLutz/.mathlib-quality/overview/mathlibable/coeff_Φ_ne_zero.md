# /mathlibable report — `WeierstrassCurve.coeff_Φ_ne_zero`

**TL;DR verdict: `NO-mathlib-has-it`.** The declaration is a **byte-for-byte copy**
of `WeierstrassCurve.coeff_Φ_ne_zero`, which already exists in mathlib at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:431`.
Same namespace, same signature, same `[Nontrivial R]` hypothesis, same proof term.
The project file is a fork of that mathlib file.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); decl read directly from source
- decl `WeierstrassCurve.coeff_Φ_ne_zero`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:429`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Degrees / leading coefficients of the division polynomials (Ψ₂Sq, Ψ₃, preΨ', preΨ, ΨSq, Φ) of a Weierstrass curve — a fork of mathlib's `DivisionPolynomial/Degree.lean`.

Qualified name VERIFIED from source: the file opens `namespace WeierstrassCurve`
(line 55) with `variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)`
(line 57), and the lemma sits inside `section Φ … end Φ` (lines 384–448) before
`end WeierstrassCurve` (line 450). Hence `WeierstrassCurve.coeff_Φ_ne_zero`.

---

### Statement (Phase 1)

`WeierstrassCurve.coeff_Φ_ne_zero` states: for a Weierstrass curve `W` over a
commutative ring `R` that is nontrivial, and any integer `n`, the coefficient of
the division polynomial `Φₙ` at degree `|n|²` is nonzero.

This is the immediate "nonzero" corollary of `coeff_Φ` (the same coefficient
equals `1`); it is the bridge lemma used to pin down `natDegree (Φ n) = |n|²`
(via `natDegree_eq_of_le_of_coeff_ne_zero`).

Variables / typeclasses involved (Lean side):
- `{R : Type u}`, `[CommRing R]` — the base commutative ring.
- `[Nontrivial R]` — needed so that `(1 : R) ≠ 0`, i.e. so a coefficient equal to 1 is nonzero.
- `(W : WeierstrassCurve R)` — the Weierstrass curve.
- `(n : ℤ)` — the index of the division polynomial.

Hypotheses (Lean side): none beyond the typeclasses (`[Nontrivial R]` carries the content).

Conclusion (math): `[Φₙ]_{|n|²} ≠ 0`.

Conclusion (Lean): `(W.Φ n).coeff (n.natAbs ^ 2) ≠ 0`.

Exact source:
```lean
lemma coeff_Φ_ne_zero [Nontrivial R] (n : ℤ) : (W.Φ n).coeff (n.natAbs ^ 2) ≠ 0 :=
  W.coeff_Φ n ▸ one_ne_zero
```

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: A one-line corollary (`coeff = 1`  ⟹  `coeff ≠ 0`) of the sibling
`coeff_Φ`; not a named theorem, not a new structure, not a project main result.

(Note: literature width is normally EXHAUSTIVE regardless. Here the verdict is
fixed by direct file-level evidence — the decl is an identical copy of an
existing mathlib lemma — so the standard-form question is moot: mathlib's own
form *is* the standard form, and we are it. The channels below are recorded at
the depth needed to document that, not expanded, because no literature finding
could change "mathlib already contains this exact declaration".)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`W.coeff_Φ n ▸ one_ne_zero`).
One-liner verdict: n/a — kind is `lemma`, not a `def`/`abbrev`/`structure`. The
one-line-def negative signal does not apply to lemmas (lemmas are proof-irrelevant;
there is no defeq/diamond/unfolding concern). Recorded for completeness only.

---

### Literature search — resolved by mathlib hit (Phase 3)

| #  | Channel                          | Query / action                                                                 | Hit? | Finding |
|----|----------------------------------|--------------------------------------------------------------------------------|------|---------|
|  1 | mathlib source (decisive)        | grep `coeff_Φ_ne_zero` in mathlib `DivisionPolynomial/`                         | yes  | **Exact decl present** at `Degree.lean:431`, identical statement + proof |
|  2 | WebSearch (concept)              | "division polynomial elliptic curve leading coefficient degree n^2"            | yes  | Standard: the n-division polynomial ψₙ (and the φₙ = x·ψₙ² − ψ_{n+1}ψ_{n−1} numerator) has degree n²−1 / n² and is monic up to a known constant — Silverman, *AEC*, Ch. III Exercise 3.7 / §III.4 |
|  3 | WebSearch (named / aliases)      | "Φ division polynomial monic coefficient" / "Weierstrass division polynomial degree" | yes | Confirms φₙ has x-degree n² with leading coefficient 1; the "nonzero top coefficient" is the routine monicity fact |
|  4 | ChatGPT MCP                      | (MCP down per task note — substituted by #2/#3 WebSearch + Silverman reference) | n/a  | Standard form is well-established and matches mathlib's; no historical-evolution subtlety affecting this corollary |
|  5 | Local references                 | `.mathlib-quality/references/` — Silverman AEC is the project's source text     | n/a  | Division-polynomial degree facts are textbook (Silverman III §4 / Ex 3.7); consistent with mathlib's statement |
|  6 | nLab                             | "division polynomial"                                                           | n/a  | Not an nLab-style categorical concept; no entry adds anything beyond the textbook degree fact |
|  7 | nCatLab                          | —                                                                              | n/a  | Not a categorical concept |
|  8 | Stacks Project                   | "division polynomial"                                                           | n/a  | Stacks does not develop elliptic-curve division polynomials at this granularity |
|  9 | MathOverflow / MSE               | "degree of division polynomial phi_n elliptic curve"                           | yes  | Routine: φₙ has degree n², monic; the nonzero-leading-coefficient statement is folklore |
| 10 | recent arXiv                     | —                                                                              | n/a  | A monicity corollary of a classical 19th-century construction; no recent-arXiv standard-form revision |

### Literature summary (Phase 3)

Concept identified as: the **n-th division polynomial** `Φₙ` (the x-coordinate
numerator `φₙ`) of a Weierstrass curve; this lemma is its **top-coefficient
non-vanishing** at degree `|n|²` (equivalently, `Φₙ` is monic of degree `|n|²`).
Sources agree on the standard form: yes — Silverman *AEC* and the standard
references all give φₙ degree `n²`, leading coefficient `1`.
Most general standard form: over any nontrivial commutative ring (which is
exactly mathlib's / the project's `[CommRing R] [Nontrivial R]`).
Generality dimensions where the literature varies: essentially none for this
corollary — the only hypothesis that matters is `(1 : R) ≠ 0`, captured by
`[Nontrivial R]`. Mathlib already states it at this generality.
Disagreement with the literature: none.

---

### Generality analysis (Phase 4)

Literature-standard form (from Phase 3): over a nontrivial commutative ring,
`Φₙ` has nonzero coefficient at degree `|n|²`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`        | commutative ring  | commutative ring         | NO                  | `Φ` is defined over `CommRing`; this is mathlib's base and the natural setting |
| 2 | `[Nontrivial R]`     | nontrivial        | `(1 : R) ≠ 0`            | NO                  | Strictly necessary: in the trivial ring every coefficient is 0, so the conclusion fails. This is the minimal hypothesis. |
| 3 | `(n : ℤ)`            | integer index     | integer index            | NO                  | Already fully general over ℤ (mathlib handles `n < 0` via `Int.negInduction`). |

### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL (and identical to mathlib's own form).
Number of weakening opportunities found: 0.
Cost of restatement: n/a — no restatement warranted.

### Modern-idiom check (Phase 4c)

Modern idiom available: no. This is a concrete polynomial-coefficient
non-vanishing statement over a commutative ring; there is no typeclass-ification,
filter/topology, universal-property, bundled-substructure, or categorification
move that applies. Mathlib's own formulation is already the idiom. Every row of
the Phase-4c table is `no` for the same reason: a finite algebraic identity over
`CommRing`, no structure to abstract.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (proof-irrelevant; introduces no definitional
equalities, instances, coercions, or typeclass-search paths).

---

### Mathlib search-status: `WeierstrassCurve.coeff_Φ_ne_zero` (Phase 5)

[A] Lean-Finder       "division polynomial Phi coefficient nonzero"   → mathlib `coeff_Φ_ne_zero` (consistent with grep)
[B] Loogle            `(WeierstrassCurve.Φ _ _).coeff _ ≠ 0`            → matches mathlib `WeierstrassCurve.coeff_Φ_ne_zero`
[C] LeanSearch        "coefficient of division polynomial Phi_n is nonzero" → returns the mathlib lemma
[D] Grep mathlib src  grep `coeff_Φ_ne_zero` / `coeff_Φ` / `natDegree_Φ` in `.lake/packages/mathlib/.../DivisionPolynomial/Degree.lean` → **HIT, exact** (lines 431, 426, 435)
[E] Name pattern      `WeierstrassCurve.coeff_Φ_ne_zero`               → present verbatim in mathlib

Searched for both:
  - the user's current form — found verbatim.
  - the literature-standard form — same statement; also found.

Concluded: **found in mathlib as `WeierstrassCurve.coeff_Φ_ne_zero`; identical
form** (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:431`).

Direct evidence (mathlib vs. project, both lines 431–432 / 429–430):
```lean
-- mathlib  Degree.lean:431
lemma coeff_Φ_ne_zero [Nontrivial R] (n : ℤ) : (W.Φ n).coeff (n.natAbs ^ 2) ≠ 0 :=
  W.coeff_Φ n ▸ one_ne_zero
-- project  DivisionPolynomialDegree.lean:429
lemma coeff_Φ_ne_zero [Nontrivial R] (n : ℤ) : (W.Φ n).coeff (n.natAbs ^ 2) ≠ 0 :=
  W.coeff_Φ n ▸ one_ne_zero
```
A `diff` of the surrounding `section Φ` block (project lines 418–450 vs. mathlib
415–448) shows the two are identical up to the trailing `end WeierstrassCurve` —
confirming the project file is a fork of mathlib's `DivisionPolynomial/Degree.lean`.
Mathlib's module docstring even lists the sibling `WeierstrassCurve.coeff_Φ` as a
documented main result of that file.

Note on `Φ`'s provenance: the project imports its own `LutzNagell.DivisionPolynomial`
(a fork of mathlib's `DivisionPolynomial/Basic.lean` defining `WeierstrassCurve.Φ`),
not mathlib's. But that forked `Φ` is itself a copy of mathlib's `Φ`, so the
statement is mathlib-equivalent; nothing about the fork makes this lemma novel.

---

### Composition check (Phase 6)

### Call sites — `WeierstrassCurve.coeff_Φ_ne_zero`

Internal use count: 1 (within the project, excluding the declaring lemma itself).
External-to-file callers: 0 distinct *other* files (the single use is in the same file).

| Caller file:line                                   | Usage pattern |
|----------------------------------------------------|---------------|
| DivisionPolynomialDegree.lean:434 (`natDegree_Φ`)  | `natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_Φ_le n) <| W.coeff_Φ_ne_zero n` |

Inline-derivation grep: (none) — no other site re-derives this nonzero fact.
This usage pattern mirrors mathlib's own internal use of `coeff_Φ_ne_zero`
inside `natDegree_Φ`, reinforcing that the project's whole Φ block tracks mathlib.

### Composition check (Phase 6)

Can `coeff_Φ_ne_zero` be derived from mathlib in ≤3 chained calls? — Moot for the
verdict (mathlib has the lemma verbatim), but yes, trivially:

Attempt 1: `W.coeff_Φ n ▸ one_ne_zero`
  - Mathlib decls used: `WeierstrassCurve.coeff_Φ` (the sibling, `coeff = 1`), `one_ne_zero`.
  - Result: succeeds — it is exactly the existing proof term (1 rewrite + `one_ne_zero`).

Conclusion: COMPOSABLE in ≤2 calls from mathlib primitives — *and* the fully
assembled lemma is already in mathlib under the same name. The operative bucket
is therefore NO-mathlib-has-it (mathlib has the finished lemma), with
NO-composable-from-mathlib as a strict secondary (even absent the named lemma,
the form is a 2-call composition off `coeff_Φ`).

---

## Verdict: `WeierstrassCurve.coeff_Φ_ne_zero`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): standard textbook fact (Silverman *AEC* III); φₙ monic of x-degree n². Resolved decisively by a direct mathlib-source hit.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — identical to mathlib; `[Nontrivial R]` is the minimal hypothesis; no modern-idiom move.
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.coeff_Φ_ne_zero`; **identical form** (statement + proof term).
- Composition check (Phase 6): COMPOSABLE (2 calls) — but irrelevant; the finished lemma already exists.

**Rationale:**

The project lemma is a verbatim copy of `WeierstrassCurve.coeff_Φ_ne_zero` in
mathlib's `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`
(line 431) — same `WeierstrassCurve` namespace, same `[CommRing R] [Nontrivial R]
(n : ℤ)` signature, same conclusion `(W.Φ n).coeff (n.natAbs ^ 2) ≠ 0`, and the
same proof term `W.coeff_Φ n ▸ one_ne_zero`. A `diff` of the enclosing `section Φ`
block against mathlib's confirms the project's `DivisionPolynomialDegree.lean` is
a fork of mathlib's `Degree.lean`; the sibling lemmas (`coeff_Φ`, `natDegree_Φ_le`,
`natDegree_Φ`, `leadingCoeff_Φ`, `Φ_ne_zero`) all match line-for-line too. There is
no generalisation gap and no modernisation gap: mathlib's form already sits at the
maximal natural generality (any nontrivial commutative ring), and `[Nontrivial R]`
is genuinely required (in the zero ring the conclusion is false). Hence this is a
duplicate of an existing mathlib lemma, not a contribution.

**WHY not (refactor-actionable):** Mathlib already has this exact lemma. The
project's `Φ` is its own forked copy of mathlib's `WeierstrassCurve.Φ`
(`LutzNagell.DivisionPolynomial`), so the project's lemma is stated about the
forked `Φ`. The clean refactor is to **drop the entire forked `Φ`/division-
polynomial track and depend on mathlib's** `DivisionPolynomial/Basic.lean` +
`Degree.lean` directly, at which point `coeff_Φ_ne_zero` (and every sibling here)
is provided by mathlib for free.

Existing mathlib decl:        `WeierstrassCurve.coeff_Φ_ne_zero`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:431`
Our form follows in ≤1 line (in fact it *is* mathlib's line):
```lean
example [Nontrivial R] (n : ℤ) : (W.Φ n).coeff (n.natAbs ^ 2) ≠ 0 :=
  WeierstrassCurve.coeff_Φ_ne_zero n   -- mathlib's, on mathlib's `W.Φ`
```
Call sites in our project (from Phase 6.0):  K = 1 (the sibling `natDegree_Φ` at
DivisionPolynomialDegree.lean:434).

Refactor plan:
1. This is one leaf of a whole forked module. The forked `WeierstrassCurve.Φ`
   (in `LutzNagell.DivisionPolynomial`) is a copy of mathlib's `WeierstrassCurve.Φ`,
   so prefer **deleting the fork** (`DivisionPolynomial.lean` +
   `DivisionPolynomialDegree.lean`) and `import`-ing mathlib's
   `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` instead.
2. After that, the single internal call site (line 434, `natDegree_Φ`) is also
   served by mathlib's `WeierstrassCurve.natDegree_Φ`, so it disappears with the
   fork — no per-call-site rewrite needed beyond fixing imports.
3. The one *downstream* consumer of the Φ-degree API in the project,
   `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDIntegralMultiple.lean:35`
   (`_ = (W.Φ n).natDegree := (natDegree_Φ _ n).symm`), should then resolve
   `natDegree_Φ` to mathlib's lemma — verify it still typechecks against mathlib's
   `W.Φ` (it should: same statement) and adjust the import line only.
4. If, for project reasons, the fork must stay (e.g. it is intentionally pinned to
   an older mathlib `Φ`), then this specific duplicate lemma is still redundant
   *given the fork* and could at minimum be re-exported/aliased rather than
   re-proved — but the structural fix is removing the fork.

Next action: do not upstream. Treat as a fork-dedup task: delete (or re-point to
mathlib) the forked `Φ` division-polynomial track in `projects/NagellLutz/`, then
let `WeierstrassCurve.coeff_Φ_ne_zero` and its siblings come from mathlib.

---

## Next step

Treat as a fork-deduplication item, not a mathlib contribution. The cleanest move
is to drop the project's forked `WeierstrassCurve.Φ` division-polynomial files
(`LutzNagell/DivisionPolynomial.lean`, `LutzNagell/DivisionPolynomialDegree.lean`)
and import mathlib's `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`
directly; `coeff_Φ_ne_zero` (and `coeff_Φ`, `natDegree_Φ`, `leadingCoeff_Φ`,
`Φ_ne_zero`, …) are then provided by mathlib. Update the one downstream consumer
(`PIDIntegralMultiple.lean:35`) to use mathlib's `natDegree_Φ`.

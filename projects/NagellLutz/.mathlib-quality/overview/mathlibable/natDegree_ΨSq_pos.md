# /mathlibable report — `WeierstrassCurve.natDegree_ΨSq_pos`

> **Headline:** This declaration is a **verbatim fork of an existing mathlib lemma**. Mathlib
> already has `WeierstrassCurve.natDegree_ΨSq_pos`, character-for-character identical (same
> namespace, same signature, same one-line proof), in
> `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:365`.
> **Verdict: `NO-mathlib-has-it`.**

---

### Baseline (Phase 0)
- lake build:               ⚠ not re-run (local build stale per task brief). Reasoned from source +
                            vendored mathlib oleans/source under `.lake/packages/mathlib`. The decl
                            elaborates in mathlib (it *is* mathlib's lemma), so its type is known exactly.
- decl `WeierstrassCurve.natDegree_ΨSq_pos`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:363`
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  "Division polynomials of Weierstrass curves" — computes leading terms
                             (degree + leading coeff) of `preΨ`, `ΨSq`, `Φ`. The file header states
                             verbatim: *"a project copy of mathlib's Basic file"* (line 14).

The parsed/guessed qualified name `WeierstrassCurve.natDegree_ΨSq_pos` is **VERIFIED**: the file opens
`namespace WeierstrassCurve` at line 55 and never closes it before line 363; base name `natDegree_ΨSq_pos`.

---

### Statement (Phase 1)

`WeierstrassCurve.natDegree_ΨSq_pos` is a theorem stating:

> Let `W` be a Weierstrass curve over a commutative ring `R` with no zero divisors, and let `n` be an
> integer with `|n| > 1` (`1 < n.natAbs`) whose image in `R` is nonzero. Then the squared `n`-division
> polynomial `W.ΨSq n` (a univariate polynomial over `R`) has **strictly positive degree**.

Mathematically this is immediate from the exact-degree formula `deg(ΨSqₙ) = n² − 1`: once `|n| > 1`
we have `n² − 1 ≥ 3 > 0`. It is a throwaway positivity corollary of `natDegree_ΨSq`, used only to
prove that `ΨSqₙ` is a nonzero polynomial.

Variables / typeclasses (Lean side):
- `{R : Type u}`, `[CommRing R]` — the base ring.
- `[NoZeroDivisors R]` — needed so that the *exact* degree (not just the upper bound) is available
  (`coeff_ΨSq_ne_zero` requires the leading coeff `n²` to be nonzero, which uses no-zero-divisors).
- `(W : WeierstrassCurve R)` — the curve (the `ΨSq` family is defined relative to it).

Hypotheses (Lean side):
- `(hn : 1 < n.natAbs)` — `|n| > 1`, i.e. `n ∉ {−1, 0, 1}`.
- `(h : (n : R) ≠ 0)` — the characteristic does not divide `n`.

Conclusion (math): `deg(W.ΨSq n) > 0`.
Conclusion (Lean): `0 < (W.ΨSq n).natDegree`.

Proof body (both project and mathlib): `by simpa [W.natDegree_ΨSq h]` — rewrite the degree to
`n.natAbs ^ 2 - 1` via `natDegree_ΨSq`, then `simpa` closes `0 < n.natAbs ^ 2 - 1` from `1 < n.natAbs`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A one-line positivity corollary of `natDegree_ΨSq`; not a new structure, not a named theorem,
not a `## Main results` entry (it is not even listed in the file's own Main-statements block).

(Literature width was still run. BIG/SMALL is narrative only.)

### One-line check (Phase 2b)

Kind is `lemma`/`theorem`, not a `def` — Phase 2b one-liner gate is **n/a**. (Recorded for the form:
the *proof* is one line, but the one-liner exemption machinery is about one-line `def` bodies, which
this is not.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                   | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------|------|-------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic curve division polynomial psi_n degree n^2 - 1 Silverman"                     | yes  | `deg ψₙ² = n² − 1` (so `> 0` for `n>1`)               | **Top hit is the mathlib doc page for `…DivisionPolynomial.Degree`** — independent confirmation it is in mathlib. Also MIT 18.783 Lec #6, Sutherland. |
|  2 | WebSearch (general form)         | (folded into #1 — Sutherland notes `deg gₙ = deg ψₙ² ≤ n²−1`, exact under char ∤ n)      | yes  | exact degree `n²−1` over a field / no-zero-divisor ring | The positivity is a trivial arithmetic consequence; nobody states "degree is positive" as its own named result in the literature — it is a one-line corollary. |
|  3 | WebSearch (named-after/aliases)  | division polynomials are not named after a person; "ψ_n squared" / "g_n" aliases checked in #1 | n/a | —                                                     | No eponymous name; standard textbook object (Silverman III.§). |
|  4 | ChatGPT MCP                      | —                                                                                       | n/a  | —                                                     | MCP down per task brief; substituted by WebSearch ×2 + the decisive mathlib-source grep. Not load-bearing: the verdict rests on an exact byte-level source match, not on taste. |
|  5 | Local references                 | `find refs/NagellLutz`, `.mathlib-quality/**/references`                                 | n/a  | —                                                     | No references dir present (`refs/` absent; gitignored local store not populated on this machine). |
|  6 | nLab                             | "division polynomial"                                                                    | n/a  | —                                                     | Not a category-theoretic concept; nLab has no division-polynomial page. The object and its degree are elementary commutative algebra. |
|  7 | nCatLab                          | —                                                                                       | n/a  | —                                                     | Not categorical. |
|  8 | Stacks Project                   | "division polynomial"                                                                    | n/a  | —                                                     | Stacks is scheme-theoretic algebraic geometry; division polynomials of a Weierstrass model are not a Stacks topic. |
|  9 | MathOverflow / Math.SE           | (covered by #1's arXiv/lecture-note hits)                                                | n/a  | —                                                     | Degree of ψₙ is undergraduate-standard; no MO controversy to resolve. |
| 10 | recent arXiv (last 5 yrs)        | surfaced by #1: eprint 2010/630, arXiv 1801.02664 (Division-Polynomial PIT), 2008.00433 | yes  | all use `deg ψₙ ~ (n²−1)/2`, `deg ψₙ² = n²−1`         | Confirms the degree formula is the universally-used standard; positivity never gets a separate name. |

### Literature summary (Phase 3)

Concept identified as: the **`n`-th division polynomial** `ψₙ` of a Weierstrass / elliptic curve, and
its square `ψₙ²` (mathlib's `ΨSq n`). Standard reference: Silverman, *The Arithmetic of Elliptic
Curves*, Ch. III (Exercise 3.7) — exactly the reference cited in the file header.
Sources agree on the standard form: **yes** — `deg ψₙ² = n² − 1` (equivalently `deg ψₙ = (n²−1)/2` for
odd `n`, `n(n²−4)/2`-style for even after removing the `2y+a₁x+a₃` factor). Over a field of
characteristic ∤ n the degree is exact.
Most general standard form: the exact degree `n² − 1` of `ψₙ²`; positivity for `|n|>1` is the trivial
`n²−1 ≥ 3 > 0` consequence. **No source states "the degree is positive" as a standalone result** — it
is a one-line corollary used to deduce `ψₙ ≠ 0`, which is precisely how this lemma is used here.
Disagreement with the literature: none. The Lean statement is the standard object at standard generality.

---

### Generality analysis — `WeierstrassCurve.natDegree_ΨSq_pos`

Literature-standard form: `deg(ψₙ²) = n² − 1`, exact over a no-zero-divisor ring with `(n:R) ≠ 0`.

| # | Parameter / hypothesis      | Current Lean form                | Literature-standard form                 | Weaker form exists? | Reason |
|---|------------------------------|----------------------------------|------------------------------------------|---------------------|--------|
| 1 | `[CommRing R]`              | commutative ring                 | usually a field; mathlib already does CommRing | NO            | Already the general mathlib form (matches mathlib's own lemma). |
| 2 | `[NoZeroDivisors R]`        | no zero divisors                 | integral domain / field                  | NO                  | Needed for the *exact* degree (leading coeff `n²` must be nonzero); this is already weaker than "field". |
| 3 | `(hn : 1 < n.natAbs)`       | `|n| > 1`                        | `|n| > 1` (else degree is `0`, not `>0`) | NO                  | Sharp: at `|n|=1`, `deg = 0`; the hypothesis is exactly the threshold for positivity. |
| 4 | `(h : (n:R) ≠ 0)`           | char ∤ n                         | char ∤ n                                 | NO                  | Required for the exact-degree input. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it is, verbatim, mathlib's own already-curated form).
Number of weakening opportunities found: **0**.
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Reformulation | Downstream |
|----|--------------------------------------------------------------------------|----------|---------------|------------|
| 1 | Bundled hyps → typeclasses?                                              | no       | — | `NoZeroDivisors` is already a typeclass; `hn`,`h` are genuine per-`n` propositions. |
| 2 | Sequences/metric → filters/topology?                                     | no       | — | Pure polynomial-degree statement; no analysis. |
| 3 | Construction → universal property?                                       | no       | — | A degree inequality, nothing to characterise. |
| 4 | Set+closure-pred → bundled substructure?                                  | no       | — | n/a. |
| 5 | Vector-space/field-specific → weaken typeclass?                           | no       | — | Already at `CommRing + NoZeroDivisors`. |
| 6 | 1-categorical → higher-categorical?                                       | no       | — | n/a. |
| 7 | Concrete index → general additive structure?                             | no       | — | Index is `n : ℤ`, intrinsic to the `ΨSq : ℤ → R[X]` family; cannot abstract. |

Modern idiom available: **no**. Reason: this is a finite arithmetic positivity corollary of an
exact-degree formula; there is no organisational lever to pull, and mathlib already ships this exact
statement.

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `lemma`** (no definitional equalities, no typeclass-search paths introduced).

---

### Mathlib search-status: `WeierstrassCurve.natDegree_ΨSq_pos`

[A] Lean-Finder       — (mathlib index)            n/a — superseded by exact source match below.
[B] Loogle            `WeierstrassCurve.ΨSq, 0 < natDegree`  → hit: mathlib's lemma (same name).
[C] LeanSearch        "degree of division polynomial squared is positive" → mathlib `…ΨSq` family.
[D] **Grep mathlib src** `grep -n "ΨSq" …/DivisionPolynomial/Degree.lean` → **DIRECT HIT** (below).
[E] Name pattern      `natDegree_ΨSq_pos` in `.lake/packages/mathlib` → found, exactly one decl.

Searched for both the user's current form and the literature-standard exact-degree form — both are in
mathlib (`natDegree_ΨSq` is the exact-degree lemma; `natDegree_ΨSq_pos` is this positivity corollary).

**Decisive evidence (Grep [D], byte-level):**

Mathlib `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:365–367`:
```lean
lemma natDegree_ΨSq_pos [NoZeroDivisors R] {n : ℤ} (hn : 1 < n.natAbs) (h : (n : R) ≠ 0) :
    0 < (W.ΨSq n).natDegree := by
  simpa [W.natDegree_ΨSq h]
```
Project `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:363–365`:
```lean
lemma natDegree_ΨSq_pos [NoZeroDivisors R] {n : ℤ} (hn : 1 < n.natAbs) (h : (n : R) ≠ 0) :
    0 < (W.ΨSq n).natDegree := by
  simpa [W.natDegree_ΨSq h]
```
Same `namespace WeierstrassCurve`, same `variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)`,
same hypotheses, same conclusion, same proof term. A `diff` of the surrounding ΨSq section confirms
the only divergences are in *adjacent* lemmas (`natDegree_coeff_ΨSq_ofNat`, `ΨSq_ne_zero`), **not** in
`natDegree_ΨSq_pos` itself, which is byte-identical. The mathlib pin is rev `69aaaa313f44`
(`lakefile.toml`), and WebSearch hit #1 is the live mathlib doc page for this very file — so the lemma
is in mathlib at the pinned version, not merely a local artifact.

**Concluded:** *found in mathlib as `WeierstrassCurve.natDegree_ΨSq_pos`; identical form.*

---

### Call sites — `WeierstrassCurve.natDegree_ΨSq_pos`

Internal use count: **1** (and it is *inside the declaring file*, so external-to-file count = **0**).
External-to-file callers: **0** distinct files.

| Caller file:line                                         | Usage pattern (one-line excerpt)                          |
|----------------------------------------------------------|-----------------------------------------------------------|
| LutzNagell/DivisionPolynomialDegree.lean:374 (`ΨSq_ne_zero`) | `· exact ne_zero_of_natDegree_gt <| W.natDegree_ΨSq_pos hn h` |

Inline-derivation grep (re-derived elsewhere without using the lemma?): (none).

Call-sites reading: this is mathlib's own internal helper for `ΨSq_ne_zero` (which is *also* in mathlib
right below it, lines 374–384). The project inherited the whole micro-API verbatim. No project code
outside the forked file depends on it.

---

### Composition check (Phase 6)

Can `natDegree_ΨSq_pos` be derived from mathlib in ≤3 chained calls? **Moot — mathlib has the exact
lemma**, so there is nothing to compose; you just call it. (For completeness: it is also a 1-call
corollary of mathlib's `WeierstrassCurve.natDegree_ΨSq`, via `by simpa [W.natDegree_ΨSq h]` — the very
proof both copies use. But that is irrelevant given the identical lemma already exists.)

Conclusion: **N/A — identical decl already in mathlib** (dominates any composition argument).

---

## Verdict: `WeierstrassCurve.natDegree_ΨSq_pos`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): standard Silverman degree formula `deg ψₙ² = n²−1`; positivity is a
  trivial corollary, never separately named. Top WebSearch hit is the mathlib doc page for the file.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — it *is* mathlib's curated form; 0 weakenings;
  no modern-idiom lever.
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.natDegree_ΨSq_pos`; byte-identical**
  at `…/DivisionPolynomial/Degree.lean:365`.
- Composition check (Phase 6): N/A — the identical declaration already exists.

**Rationale:**

This file is, by its own admission (line 14), a project copy of mathlib's elliptic-curve
division-polynomial files, and `natDegree_ΨSq_pos` is the most clear-cut instance of that: it is
character-for-character identical to the mathlib lemma of the same fully-qualified name —
`WeierstrassCurve.natDegree_ΨSq_pos` — same namespace, same `[NoZeroDivisors R]` typeclass, same
hypotheses `1 < n.natAbs` and `(n : R) ≠ 0`, same conclusion `0 < (W.ΨSq n).natDegree`, and the same
one-line proof `by simpa [W.natDegree_ΨSq h]`. Mathlib carries it at the pinned revision (rev
`69aaaa313f44`); the live mathlib documentation page for
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` was in fact the first WebSearch
result. Nothing about the project's copy is more general or more modern than mathlib's — they are the
same lemma. There is therefore no contribution to make: mathlib already has it.

**WHY not (refactor-actionable detail):**

Mathlib already has the result, verbatim, as part of the curated division-polynomial degree API. The
gap that motivated copying it is purely structural: the NagellLutz project forked
`DivisionPolynomial/{Basic,Degree}.lean` wholesale (presumably to extend the API for the Nagell–Lutz
torsion argument) and the fork brought the entire ΨSq micro-section along, including this corollary and
its sole consumer `ΨSq_ne_zero` (which mathlib *also* already has, two lemmas down). The right
disposition is to **drop the fork in favour of importing mathlib**, not to upstream anything.

Existing mathlib decl:        `WeierstrassCurve.natDegree_ΨSq_pos`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:365`
Our form follows in ≤1 line:  it *is* the same statement — no bridging needed:
```lean
example [NoZeroDivisors R] {n : ℤ} (hn : 1 < n.natAbs) (h : (n : R) ≠ 0) :
    0 < (W.ΨSq n).natDegree :=
  W.natDegree_ΨSq_pos hn h   -- the mathlib lemma, identical signature
```
Call sites in our project (from Phase 6.0):  **1** (only `ΨSq_ne_zero` at line 374, in the same file).

Refactor plan (whole-fork scope, of which this lemma is one line):
1. The single in-project consumer is line 374 inside the forked file itself; once the file imports
   mathlib's `…DivisionPolynomial.Degree` instead of redefining the section, that call resolves to the
   mathlib lemma unchanged (identical name + argument order `W.natDegree_ΨSq_pos hn h`) — **zero
   edits** at the call site.
2. This decl is not a standalone deletion target: it is one lemma in a verbatim-copied block. The
   actionable move is at the **file level** — replace the project's `DivisionPolynomialDegree.lean`
   ΨSq/preΨ/Φ sections with `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`
   (and likewise the `Basic` copy in `DivisionPolynomial.lean`), keeping only whatever genuinely-new
   lemmas the project added on top. Verify the project's `ΨSq`/`natDegree_ΨSq`/`ΨSq_ne_zero` all
   resolve to the mathlib versions afterward.
3. Before doing so, diff the *whole* forked file against mathlib to confirm which lemmas (if any) are
   genuinely new — those are the only candidates for a separate `/mathlibable` pass; everything that
   diffs clean (like this lemma) is pure duplication to delete.

Next action: do not upstream. De-duplicate against mathlib — drop the forked ΨSq section (this lemma
included) and import `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`; the lone
call site needs no change. File this under the project's dedup/cleanup work, not a mathlib PR.

---

## Next step

De-duplicate against mathlib: delete the forked copy of `natDegree_ΨSq_pos` (as part of dropping the
verbatim-copied ΨSq section) and import mathlib's `…DivisionPolynomial.Degree`. The single in-file call
site (`ΨSq_ne_zero`, line 374) resolves to the identical mathlib lemma with no edit. No mathlib PR — the
lemma is already there.

# /mathlibable report — `normEDS_three`

**TL;DR — `NO-mathlib-has-it`.** This declaration is a verbatim fork of mathlib's
own `normEDS_three` (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:310`):
same `@[simp]` attribute, same statement `normEDS b c d 3 = c`, same proof
`by simp [normEDS, show ¬Even (3 : ℤ) by decide]`, same top-level namespace, same
2024 D. K. Angdinata copyright header. The NagellLutz project copied
`Mathlib.NumberTheory.EllipticDivisibilitySequence` into its tree to work on it;
`normEDS_three` is unchanged from upstream. Nothing to upstream — it is already
upstream.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); reasoning from source — the decl elaborates in mathlib, which the project forks verbatim.
- decl `normEDS_three`:     ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:914`
- kind:                     lemma (`@[simp]`)
- has sorry:                no
- module docstring summary: Defines elliptic divisibility sequences (EDS) and constructs the canonical normalised EDS `normEDS` from initial terms; a verbatim fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence` (identical `Authors: David Kurniadi Angdinata` header).

---

### Statement (Phase 1)

`normEDS_three` is a theorem stating that the canonical normalised elliptic
divisibility sequence `normEDS b c d`, evaluated at the index `n = 3`, returns its
third initial value `c`.

`normEDS b c d : ℤ → R` is the canonical normalised EDS over a commutative ring `R`
with initial data `W(0)=0, W(1)=1, W(2)=b, W(3)=c, W(4)=d·b`, built from the
auxiliary sequence `preNormEDS (b^4) c d` (odd terms agree; even terms carry an
extra factor of `b`). The lemma is one of the five "initial value" evaluation
lemmas (`normEDS_zero/one/two/three/four`) that pin down those seed terms, and it
is tagged `@[simp]` so the simplifier rewrites `normEDS b c d 3` to `c`
automatically.

Variables / typeclasses involved (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring (set at file scope).
- `(b c d : R)` — the EDS initial data (`section NormEDS` `variable`s).

Hypotheses (Lean side): none.

Conclusion (math): the 3rd term of the canonical normalised EDS equals `c`.

Conclusion (Lean): `normEDS b c d 3 = c`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: A `@[simp]` evaluation lemma fixing one initial value of a defined
sequence; not a new structure, not a `## Main statements` result (the file's main
statement is `isEllDivSequence_normEDS`), not named after a person/place.

(Note: literature width is EXHAUSTIVE regardless. Here the question collapses
immediately at Phase 5 — mathlib has the byte-identical lemma — so the literature
sweep is recorded for completeness but does not change the verdict.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`simp [normEDS, show ¬Even (3 : ℤ) by decide]`).
One-liner verdict: n/a — kind is `lemma` (a proof, not a `def`). The one-liner
exemption table applies to `def`/`abbrev`/`structure` bodies; a one-line proof of
a lemma carries no defeq/diamond/API-anchor concern. Skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                 | Hit? | Standard form found                              | Notes |
|----|----------------------------------|-----------------------------------------------------------------------|------|--------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence" normalised initial values W3 = c     | yes  | Normalised EDS seeded by `1, b, c, d` (Ward)     | Ward's *Memoir on EDS* (1948); the seeds `W1=1, W2=b, W3=c, W4=db` are the standard normalisation cited in mathlib's own References. |
|  2 | WebSearch (general form)         | division polynomial psi_3 elliptic curve formula                      | yes  | `ψ₃ = 3x⁴ + b₂x³ + 3b₄x² + 3b₆x + b₈`            | The n=3 division polynomial is the concrete instance of `normEDS …3` for the EC-coefficient specialisation; the *abstract* seed value is `c`. |
|  3 | WebSearch (named-after / aliases)| Ward elliptic divisibility sequence; Somos sequence initial terms     | yes  | Same normalisation; "EDS" ≡ Ward sequence        | Aliases: EDS / Ward sequence / (special) Somos-4; all use the same seed convention. |
|  4 | ChatGPT MCP                      | (MCP down per task note — fallback to WebSearch #1–3 + mathlib docstring) | n/a  | covered by #1, #2 and the in-source References   | The mathlib module docstring already cites Ward and fixes the seed convention `W0=0,W1=1,W2=b,W3=c,W4=db`; no historical-evolution ambiguity. |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` for "EDS"     | n/a  | directory not consulted; in-source docstring authoritative | The decl's own docstring + mathlib's References (Ward) settle the standard form. |
|  6 | nLab                             | elliptic divisibility sequence                                        | no   | no dedicated page                                | nLab has no EDS entry; concept is number-theoretic, not categorical. |
|  7 | nCatLab (if categorical)         | —                                                                     | n/a  | not a categorical concept                        | n/a. |
|  8 | Stacks Project (if alg geom)     | division polynomial / elliptic divisibility                           | n/a  | not in Stacks                                    | Stacks does not cover division polynomials / EDS recursions. |
|  9 | MathOverflow / Math.StackExchange| elliptic divisibility sequence initial conditions normalisation       | yes  | seeds `1, b, c, d` standard                      | Confirms the `W3 = c` seed is the universally used normalisation. |
| 10 | recent arXiv (last 5 years)      | elliptic divisibility sequences Somos arithmetic                      | yes  | same normalisation (Ward seeds)                  | Modern EDS papers (
ward-sequence / Somos literature) all reuse the `1,b,c,d` seeding; nothing more general at the *seed-value* level. |

### Literature summary (Phase 3)

Concept identified as: the third initial value of the **canonical normalised
elliptic divisibility sequence** (Ward normalisation `W0=0, W1=1, W2=b, W3=c,
W4=d·b`).
Sources agree on the standard form: yes — Ward's memoir, the division-polynomial
literature, and modern EDS/Somos papers all use the seed convention in which
`W(3) = c`. Mathlib's own module docstring cites Ward and fixes exactly this
convention.
Most general standard form: there is no "more general" seed value — `normEDS_three`
is a definitional evaluation of a *specific* sequence at a *specific* index; its
content is exactly "the n=3 seed of the canonical normalisation is `c`."
Generality dimensions where the literature varies: none at the seed-value level;
the only variation in the literature is which concrete ring/curve one specialises
`b,c,d` to (e.g. EC division polynomials), which is downstream of this lemma, not a
generalisation of it.
Disagreement with the literature: none.

---

### Generality analysis — `normEDS_three`

Literature-standard form (from Phase 3): `normEDS b c d 3 = c` over an arbitrary
commutative ring `R`, for arbitrary seeds `b c d : R`.

| # | Parameter / hypothesis | Current Lean form        | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|--------------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`         | commutative ring         | commutative ring         | NO                  | `normEDS`/`preNormEDS` are defined only over `CommRing` (the recursion uses subtraction and the `b^4` factor); the seed lemma inherits that and matches mathlib exactly. |
| 2 | `(b c d : R)`          | three free ring elements | three free ring elements | NO                  | Already fully general (universally quantified seeds); no hypothesis to weaken. |
| 3 | index `3`              | the literal `(3 : ℤ)`    | the literal `3`          | NO                  | The whole point of the lemma is the specific value at `n = 3`; "generalising the index" would just be the family `normEDS_zero/one/two/three/four`, all of which mathlib already has. |

### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL (it is identical to mathlib's, over an
arbitrary `CommRing` with free seeds).
Number of weakening opportunities found: 0.
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                            | Applies? | Proposed reformulation | Mathlib downstream |
|----|--------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses?                          | no       | —                      | already typeclass-driven (`CommRing`) |
|  2 | sequences/metric → filters/topological?                           | no       | —                      | discrete evaluation; no limit notion |
|  3 | construction → universal-property class?                          | no       | —                      | it is an `=`-evaluation lemma |
|  4 | set-with-closure-predicate → bundled substructure?                | no       | —                      | n/a |
|  5 | vector-space/metric/field-specific → weaken typeclass?            | no       | —                      | already at `CommRing`, the natural floor |
|  6 | 1-categorical → higher-categorical?                               | no       | —                      | n/a |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary additive structure?             | no       | —                      | the index is fixed at `3` deliberately |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: no.
Reason: This is a finite definitional evaluation of a fixed sequence at a fixed
index over the most natural typeclass (`CommRing`). There is no preamble to
typeclass-ify, no limit to filter-ise, no construction to characterise by a
universal property. Mathlib's own form is already exactly this.

---

### Diamond / defeq risk — `normEDS_three`

n/a — declaration kind is `lemma`. (Phase 4.5 runs only for
`def`/`abbrev`/`structure`/`inductive`/`class`/`instance`.)

---

### Mathlib search-status: `normEDS_three`

[A] Lean-Finder       "normEDS at 3 equals c" / "third term normalised EDS"     hit: `normEDS_three`
[B] Loogle            `normEDS _ _ _ 3 = _`                                      hit: `normEDS_three` (mathlib)
[C] LeanSearch        "value of normalised EDS at 3 is c"                        hit: `normEDS_three`
[D] Grep mathlib src  `grep -n "normEDS_three" .lake/packages/mathlib/.../EllipticDivisibilitySequence.lean` hit: line 310
[E] Name pattern      `normEDS_three` / `normEDS_*`                              hit: full `normEDS_zero/one/two/three/four` family present

Searched for both:
  - the user's current form (`normEDS b c d 3 = c`) — found.
  - the literature-standard form — identical to the user's form — found.

Concluded: **found in mathlib as `normEDS_three`
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:310`); IDENTICAL form** —
same `@[simp]`, same statement `normEDS b c d 3 = c`, same proof
`by simp [normEDS, show ¬Even (3 : ℤ) by decide]`, same top-level namespace. A
byte-level diff of the surrounding `normEDS` region shows the project file added a
`normEDS_def` lemma and tweaked the proofs of `normEDS_ofNat` (and others), but the
`normEDS_three` lemma itself is unchanged from upstream. The shared
`Copyright (c) 2024 David Kurniadi Angdinata` header confirms the project file is a
fork of the mathlib module.

---

### Call sites — `normEDS_three`

Internal use count: 7 (across the repo; NOT counting the declaring file's own line 914)
External-to-file callers (within NagellLutz, outside the declaring file): the
declaring file re-uses it at lines 1075 / 1236 / 1410; `DivisionPolynomial.lean`
uses it once. The HasseWeil project (which forks the *same* mathlib module) uses
its own copy 3×.

| Caller file:line                                                             | Usage pattern (one-line excerpt)                          |
|------------------------------------------------------------------------------|-----------------------------------------------------------|
| NagellLutz/.../EllipticDivisibilitySequence.lean:1075                        | `simp_rw [Int.reduceAdd, Int.reduceSub, normEDS_three, normEDS]` |
| NagellLutz/.../EllipticDivisibilitySequence.lean:1236                        | `simp only [normEDS_one, normEDS_two, normEDS_three, normEDS_four]` |
| NagellLutz/.../EllipticDivisibilitySequence.lean:1410                        | `all_goals rw [normEDS_three, normEDS_two]; ring`         |
| NagellLutz/LutzNagell/DivisionPolynomial.lean:343                            | `normEDS_three ..` (term-mode application)                |
| HasseWeil/.../Auxiliary/EllipticDivisibilitySequence.lean:622/711/918        | (separate fork of the same mathlib file; own copy)        |

Inline-derivation grep: (none) — every consumer calls the lemma by name; no site
re-derives `normEDS b c d 3 = c` by hand. This is expected, because the lemma is a
`@[simp]` initial-value lemma that the existing mathlib lemma already provides.

Signal: the call sites confirm the lemma is *real API* (used as a `simp` rewrite in
several proofs) — but it is API that **mathlib already supplies**. The consumers
depend on the *name* `normEDS_three`, which is identical in mathlib; switching the
import from the forked module to `Mathlib.NumberTheory.EllipticDivisibilitySequence`
keeps every call site working verbatim.

---

### Composition check (Phase 6)

Can `normEDS_three` be derived from mathlib in ≤3 chained calls?

Attempt 1: `Mathlib.NumberTheory.EllipticDivisibilitySequence.normEDS_three`
  - Mathlib decls used: `normEDS_three` (the identical lemma).
  - Result: succeeds — it *is* the mathlib lemma; no derivation needed.

Conclusion: NOT-COMPOSABLE in the "build from primitives" sense, because no
composition is needed at all — mathlib already states this exact lemma. (The
relevant verdict is therefore NO-mathlib-has-it, not NO-composable-from-mathlib.)

---

## Verdict: `normEDS_three`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): the Ward-normalised EDS seed `W(3)=c` is the
  universal convention; mathlib's docstring cites Ward and fixes it. No more-general
  seed-value form exists.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — identical to mathlib's form
  over arbitrary `CommRing` with free seeds; 0 weakenings; no modern-idiom move.
- Mathlib search (Phase 5): found in mathlib as `normEDS_three`
  (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:310`); IDENTICAL form
  and proof.
- Composition check (Phase 6): no composition needed — it is the mathlib lemma.

**Rationale:**

The NagellLutz project forked `Mathlib.NumberTheory.EllipticDivisibilitySequence`
into `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` (same
`Authors: David Kurniadi Angdinata` header). Within that fork, `normEDS_three` is
**byte-identical** to upstream: the `@[simp]` attribute, the statement
`normEDS b c d 3 = c`, the proof `by simp [normEDS, show ¬Even (3 : ℤ) by decide]`,
and the top-level (un-namespaced, inside `section NormEDS`) placement all match
mathlib exactly. It is not a generalisation, not a re-statement, not a new initial
value — it is the same lemma. So mathlib unambiguously already has it; there is
nothing to add or generalise.

**WHY not (refactor-actionable detail):**
Mathlib already has this exact lemma — `normEDS_three` at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:310`. The project's copy is
a verbatim fork (identical statement, proof, attribute, and namespace). The user's
form does not merely *follow from* the mathlib decl in ≤1 line — it **is** the
mathlib decl. The only reason a local copy exists is that the project forked the
whole module (alongside the `DivisionPolynomial.*` files) to develop the
Nagell–Lutz material on top of it.

Existing mathlib decl:        `normEDS_three`
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:310`
Our form follows in ≤1 line:
```lean
-- it is literally the same lemma:
example (b c d : R) : normEDS b c d 3 = c := normEDS_three
```
Call sites in our project (from Phase 6.0):  4 within NagellLutz
  (EllipticDivisibilitySequence.lean:1075, :1236, :1410; DivisionPolynomial.lean:343).

Refactor plan: this is part of a *whole-file fork*, so the right unit of action is
the file, not this single lemma. Treat as a fork-reconciliation item:
1. Diff `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` against
   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` to enumerate what the
   fork genuinely *adds* (e.g. `normEDS_def`, the `complEDS`/`HaveSameParity₄`/
   `Rel₄OfValid` machinery, the `Map`/`Divisibility` sections) versus what is a
   verbatim copy of upstream (the `IsEllSequence` / `preNormEDS` / `normEDS_*` seed
   lemmas, including `normEDS_three`).
2. For the verbatim-copy part — `normEDS_three` included — delete it from the fork
   and `import Mathlib.NumberTheory.EllipticDivisibilitySequence`. Because the name
   and signature are identical and the lemma sits at top level in both, the 4
   in-project call sites (and the term-mode use in `DivisionPolynomial.lean:343`)
   continue to resolve unchanged.
3. Any genuinely-new lemmas the fork adds are separate `/mathlibable` questions and
   should be assessed on their own (several look like real new EDS API:
   `complEDS`, the divisibility/complement lemmas, etc.).

Next action: do not upstream `normEDS_three` (it is already upstream). Fold it into
a fork-reconciliation cleanup ticket for the forked
`EllipticDivisibilitySequence.lean` module: drop the verbatim upstream copies
(this lemma among them) and import them from
`Mathlib.NumberTheory.EllipticDivisibilitySequence`, keeping only the project's
genuine additions in the project tree.

---

## Next step

Do not upstream `normEDS_three` — mathlib already has the identical lemma at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:310`. File a
fork-reconciliation cleanup ticket for the forked module: delete the verbatim
upstream copies (including this lemma) and `import` them from mathlib, retaining
only the project's genuine new EDS API. Re-run `/mathlibable` per *new* lemma the
fork adds.

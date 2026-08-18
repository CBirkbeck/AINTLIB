# /mathlibable report — `preNormEDS'_two`

**TL;DR verdict: `NO-mathlib-has-it`.** This declaration is a *byte-for-byte
fork* of an existing mathlib lemma. The NagellLutz project file
`LutzNagell/EllipticDivisibilitySequence.lean` is an explicit, deliberate copy
of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (same author, same
section structure, same proofs), re-namespaced locally only to dodge a
`normEDS` / `complEDS` name clash. `preNormEDS'_two` exists in mathlib verbatim,
with the same statement, same proof, and same `@[simp]` attribute.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoning from source — task-sanctioned)
- decl `preNormEDS'_two`:   ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:747`
- kind:                     lemma (`@[simp]`)
- has sorry:                no
- module docstring summary: "Elliptic divisibility sequences (EDS) and the construction of normalised EDSs from initial terms." (This file is a fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence`.)

**Qualified name.** The file declares no top-level `namespace` around
`section PreNormEDS` (the preceding `end IsEllSequence` at line 702 closes the
last namespace). So the Lean qualified name is exactly **`preNormEDS'_two`** —
identical in both the project and mathlib. (The leanprover4 doc site displays it
as `Mathlib.NumberTheory.EllipticDivisibilitySequence.preNormEDS'_two`, but that
prefix is the *module path* the doc generator prepends for root-namespace decls,
not a Lean `namespace`.)

---

### Statement (Phase 1)

`preNormEDS'_two` states the base-case evaluation of the auxiliary
elliptic-divisibility-sequence function at index 2:

> For a commutative ring `R` and parameters `b c d : R`, the auxiliary normalised
> EDS satisfies `W(2) = 1`, i.e. `preNormEDS' b c d 2 = 1`.

`preNormEDS'` is the `ℕ`-indexed auxiliary sequence with hard-coded initial values
`W(0)=0, W(1)=1, W(2)=1, W(3)=c, W(4)=d` and a degree-2 Ward recurrence for
`n ≥ 5`. This lemma is one of five trivial "read off the base case" lemmas
(`_zero`, `_one`, `_two`, `_three`, `_four`); it is definitional bookkeeping, not
a mathematical result in its own right. The proof is a single
`rw [preNormEDS']` that unfolds the pattern-matching definition to its `2 => 1`
arm.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring.
- `(b c d : R)` — the three EDS parameters (`b` from the recurrence, `c = W(3)`, `d = W(4)`).

Hypotheses: none.

Conclusion (math): `W(2) = 1`.
Conclusion (Lean): `preNormEDS' b c d 2 = 1`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A trivial `@[simp]` evaluation lemma reading off a base case of a
recursive definition; one of five siblings; not a named theorem and not a
project main result.

(Literature width run EXHAUSTIVE regardless; recorded for framing only.)

### One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. (For completeness: the
*proof* is one line, `rw [preNormEDS']`, which underscores how trivial the
content is, but the one-liner gate applies to definitions, not lemmas.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence normalised initial values W(0)=0 W(1)=1 W(2)=1 W(3) W(4) division polynomial Ward recurrence" | yes | EDS determined by W(2),W(3),W(4); normalised means W(0)=0,W(1)=1 | Top hit is literally the **mathlib doc page** for this file; Wikipedia "Elliptic divisibility sequence"; Ward (1948) |
|  2 | WebSearch (general form)         | (same query, general angle) — "a divisibility sequence is normalized if D₀=0 and D₁=1"                  | yes  | W(2)=1 is part of the canonical EDS normalisation (Ward's normalisation) | The value `W(2)=1` is a *definitional choice* in the standard normalisation, not a theorem to generalise |
|  3 | WebSearch (named-after / aliases)| "Ward recurrence" / "division polynomial ψₙ(P)" elliptic divisibility | yes  | Ward: Wₙ = ψₙ(P) for a curve E and point P | Confirms the concept is classical (Morgan Ward, 1948); ψ₂ = 1 normalisation standard |
|  4 | ChatGPT MCP                      | (MCP down per task env; substituted by WebSearch #1–#3 + Wikipedia + arXiv survey reads) | n/a  | — | MCP unavailable; fallback channels covered the standard-form + historical-evolution question |
|  5 | Local references                 | check `projects/NagellLutz/.mathlib-quality/references/`                                                | n/a  | (forked-from-mathlib source is itself the reference) | The decl is a verbatim mathlib copy; the canonical "reference" is the mathlib source, already read |
|  6 | nLab                             | "elliptic divisibility sequence"                                                                        | n/a  | not an nLab topic                | Concrete number-theory / recurrence object, not a categorical concept; nLab has no entry |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | not categorical                  | No categorical content in a base-case `= 1` evaluation |
|  8 | Stacks Project (if alg geom)     | "division polynomial" / "elliptic divisibility"                                                        | n/a  | not a Stacks topic               | Stacks covers scheme-theoretic AG; EDS recurrences / division-polynomial base values are not in scope |
|  9 | MathOverflow / Math.StackExchange| "elliptic divisibility sequence W2 = 1 normalisation"                                                  | yes  | confirms W(2)=1 is the standard normalisation convention | Background only; nothing beyond #1–#3 |
| 10 | recent arXiv (last 5 years)      | "elliptic divisibility sequence" (Silverman, Stange, et al.); arXiv math/0402415, 1101.3839, 1001.5303 | yes  | EDS theory active; base normalisation unchanged since Ward | The `W(2)=1` base value is settled classical convention, not a research-frontier object |

### Literature summary (Phase 3)

Concept identified as: **Elliptic divisibility sequence (EDS)** — specifically the
*auxiliary normalised* sequence `preNormEDS'` underlying the division polynomials
`ψₙ`. Classical, due to Morgan Ward (1948); modern treatments by Silverman, Stange,
Shipsey.
Sources agree on the standard form: **yes** — a normalised EDS has `W(0)=0`,
`W(1)=1`, and the canonical normalisation fixes `W(2)=1`. The value at index 2
being `1` is part of the *definition* of the normalised/auxiliary sequence, not a
derived theorem.
Most general standard form: there is no "more general" form of `W(2)=1` — it is a
single base-case value read off a fixed definition. The generality lives entirely
in the ambient ring (`CommRing R`), which the lemma already states at full
generality.
Generality dimensions where the literature varies: none relevant. The interesting
generality in EDS theory (working over arbitrary commutative rings, over function
fields, etc.) concerns the *sequence* and its *divisibility/recurrence* properties
— not the trivial evaluation `W(2)=1`.
Disagreement with the literature: none. The Lean statement is exactly the standard
normalisation value.

**Decisive literature finding:** WebSearch result #1 is the **mathlib documentation
page for this very file**, and the official docs (fetched) confirm a lemma
`preNormEDS'_two : preNormEDS' b c d 2 = 1`, `@[simp]`, already in mathlib. The
literature search therefore doubles as a mathlib hit.

---

### Generality analysis — `preNormEDS'_two`

Literature-standard form (from Phase 3): `W(2) = 1` over any commutative ring;
i.e. `preNormEDS' b c d 2 = 1` for `[CommRing R]`, `b c d : R`.

| # | Parameter / hypothesis | Current Lean form        | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|--------------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`         | commutative ring         | commutative ring         | NO                  | `preNormEDS'` is *defined* with `CommRing` (uses subtraction in the recurrence); the base value `1` needs a `One`, and the function's whole API lives at `CommRing`. Weakening the typeclass would mean redefining `preNormEDS'` itself — out of scope for a base-case lemma, and mathlib already fixes this signature. |
| 2 | `(b c d : R)`          | three ring elements      | three ring elements      | NO                  | These are the defining parameters of the sequence; they are inert in this lemma (the value at 2 ignores them). Cannot be removed — they are part of `preNormEDS'`'s signature. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it matches mathlib's exactly and is
stated at the full generality of `preNormEDS'`'s own definition).
Number of weakening opportunities found: 0.
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Mathlib downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preamble → typeclass/instance?                          | no       | — | Already typeclass-based (`[CommRing R]`); nothing to bundle. |
|  2 | sequences/metric → filters/topology?                                    | no       | — | A finite base-case evaluation; no limiting/topological content. |
|  3 | construction → universal-property class?                                | no       | — | `= 1` value; no object being constructed. |
|  4 | set-with-closure-predicate → bundled substructure?                      | no       | — | No substructure. |
|  5 | vector-space/field-specific → weakened typeclass?                       | no       | — | Already at `CommRing`, the natural floor for this definition. |
|  6 | 1-categorical → higher-categorical?                                     | no       | — | No categorical content. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group?                        | no       | — | The "index" here is the literal natural number `2` naming a specific base case of a `ℕ`-recursion; it is intrinsically concrete (you cannot generalise "the value at 2" to "the value at an arbitrary monoid element" — there is no such value). |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. This is a base-case evaluation of a fixed
recursive definition; there is no contemporary mathlib reformulation that
improves its organisation. (And in any case mathlib already ships the lemma in
exactly this form, so mathlib's own taste has already ruled.)

---

### Diamond / defeq risk — `preNormEDS'_two`

n/a — declaration kind is **lemma** (Phase 4.5 runs only for
`def`/`class`/`instance`).

---

### Mathlib search-status: `preNormEDS'_two`

[A] Lean-Finder       "preNormEDS two equals one"            → resolves to mathlib decl (concept index)
[B] Loogle            `preNormEDS' _ _ _ 2 = 1` (type pattern)→ would match `Mathlib...preNormEDS'_two` (index has it)
[C] LeanSearch        "auxiliary EDS value at 2 is 1"        → resolves to mathlib `preNormEDS'_two`
[D] Grep mathlib src  `preNormEDS'_two` in `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` → **HIT, lines 148–150**
[E] Name pattern      `preNormEDS'_two` (exact)              → **HIT** in mathlib (same name, root namespace)

**Direct source evidence (the load-bearing check):**
`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`,
mathlib pin `d90090f647cae4f4ad4da99c0ac8bab2ca8c34ab`:

```lean
@[simp]
lemma preNormEDS'_two : preNormEDS' b c d 2 = 1 := by
  rw [preNormEDS']
```

This is **character-for-character identical** to the project declaration at
`EllipticDivisibilitySequence.lean:747` (same `@[simp]`, same statement, same
`rw [preNormEDS']` proof, same root namespace, same surrounding
`section PreNormEDS` with `variable (b c d : R)`). Official mathlib4 docs (fetched)
confirm the public lemma and its four siblings `preNormEDS'_{zero,one,three,four}`,
all `@[simp]`.

Searched for both:
- the user's current form `preNormEDS' b c d 2 = 1` — found.
- the literature-standard form (`W(2)=1` normalisation) — found (same lemma).

Concluded: **found in mathlib as `preNormEDS'_two` (module
`Mathlib.NumberTheory.EllipticDivisibilitySequence`); identical form.**

---

### Call sites — `preNormEDS'_two`

Internal use count: **2** (within NagellLutz, excluding the declaring file and the
`...Original.lean` backup copy).
External-to-file callers: 2 distinct files.

| Caller file:line                                              | Usage pattern (one-line excerpt)                          |
|--------------------------------------------------------------|-----------------------------------------------------------|
| `LutzNagell/DivisionPolynomial.lean:89`                      | `preNormEDS'_two ..` (proving `WeierstrassCurve.preΨ'_two : W.preΨ' 2 = 1`) |
| `LutzNagell/EllipticDivisibilitySequence.lean:1125`          | `| two => rw [preNormEDS'_two, map_one, preNormEDS'_two]` (inside a `map_preNormEDS'`-style proof) |

Also present (NOT counted — these are the fork's own duplicate backup file):
- `LutzNagell/EllipticDivisibilitySequenceOriginal.lean:701` — the lemma's own
  re-declaration in the backup copy.
- `LutzNagell/EllipticDivisibilitySequenceOriginal.lean:1072` — backup-copy call site.

Inline-derivation grep (was `W(2)=1` re-derived elsewhere without the lemma?):
(none) — every site uses the named lemma; both consumers are themselves verbatim
forks of mathlib's `DivisionPolynomial.Basic` / `EllipticDivisibilitySequence`
`map_*` proofs.

Composability signal: K = 2 internal uses, no inline re-derivation → the lemma is a
real (if trivial) API leaf *within the fork*. But since the entire fork mirrors
mathlib, those two consumers correspond exactly to mathlib's own
`preNormEDS'_two` call sites — they exist because the fork copied mathlib's
proofs wholesale, not because the project needs a *new* lemma.

---

### Composition check (Phase 6)

Can `preNormEDS'_two` be derived from mathlib in ≤3 chained calls?

Not applicable in the usual sense — **mathlib already has the exact lemma**, so
this is `NO-mathlib-has-it`, not `NO-composable`. For completeness: the proof is
itself a one-call composition, `by rw [preNormEDS']` (unfold the definition to its
`2 => 1` arm), so even absent the named lemma the content is a trivial
definitional unfolding. But the right action is to *use the mathlib lemma*, not to
inline an unfolding.

Conclusion: **n/a (NO-mathlib-has-it dominates)** — the identical decl exists
upstream; no composition needed.

---

## Verdict: `preNormEDS'_two`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the concept is classical (Ward 1948); the top web
  hit is the *mathlib doc page for this file*; `W(2)=1` is the standard
  normalisation value — not a generalisable theorem.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL**; 0 weakenings; no modern-idiom
  reformulation (Phase 4c all `no`).
- Mathlib search (Phase 5): **found in mathlib as `preNormEDS'_two`**
  (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:148–150`,
  pin `d90090f`); character-for-character identical, including `@[simp]`.
- Composition check (Phase 6): n/a — mathlib has the exact decl.

**Rationale:**

The NagellLutz file `LutzNagell/EllipticDivisibilitySequence.lean` is, by its own
header and by direct comparison, a **fork** of
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (same author David
Kurniadi Angdinata, same `section PreNormEDS`, same `variable (b c d : R)`, same
five base-case lemmas with identical proofs). `DivisionPolynomial.lean:13`
documents the reason explicitly: the fork "imports
`LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid
name conflicts (both define `normEDS`, `complEDS`, etc.)." So this is a
*consolidation/name-clash workaround*, not new mathematics. `preNormEDS'_two`
reads off the base value `W(2) = 1` from the recursive definition; mathlib carries
the byte-identical lemma. There is nothing to upstream — mathlib already has it.

**WHY not (refactor-actionable):**
Mathlib already contains this exact lemma. The project's copy exists only because
the surrounding file was forked to sidestep `normEDS`/`complEDS` name collisions
during consolidation. The correct disposition is not a per-lemma deletion but a
*file-level* deduplication: re-base the fork onto mathlib (or namespace the
fork so it can `import Mathlib.NumberTheory.EllipticDivisibilitySequence` and use
mathlib's `preNormEDS'`/`preNormEDS'_two` directly). `preNormEDS'_two` should not be
considered individually — it is collateral of the whole-file duplication and will
disappear when the fork is reconciled with upstream.

Existing mathlib decl:        `preNormEDS'_two`
                              (display name
                              `Mathlib.NumberTheory.EllipticDivisibilitySequence.preNormEDS'_two`)
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:148–150`
                              (mathlib pin `d90090f647cae4f4ad4da99c0ac8bab2ca8c34ab`)
Our form follows in ≤1 line:  it is *literally the same statement* — no derivation
needed:
```lean
example (b c d : R) : preNormEDS' b c d 2 = 1 := preNormEDS'_two ..   -- the mathlib lemma
```

Call sites in our project (from Phase 6.0):  K = 2
(`DivisionPolynomial.lean:89`, `EllipticDivisibilitySequence.lean:1125`), plus 2 in
the `...Original.lean` backup copy.

Refactor plan:
1. **Do not** treat this as a standalone delete. The fork re-defines `preNormEDS'`
   itself locally; the local `preNormEDS'_two` is *about the local `preNormEDS'`*,
   so it cannot simply be swapped for mathlib's lemma while the local `preNormEDS'`
   coexists (the two `preNormEDS'` are distinct constants even though defeq).
2. The real fix is whole-file: reconcile `LutzNagell.EllipticDivisibilitySequence`
   with `Mathlib.NumberTheory.EllipticDivisibilitySequence` — either
   (a) drop the local copy of the `preNormEDS'`/`normEDS` track and import mathlib's,
   resolving the `normEDS`/`complEDS` clash by *renaming the project-specific
   additions* rather than re-forking the whole upstream file; or
   (b) if the fork must persist for now, leave `preNormEDS'_two` exactly as-is
   (it correctly mirrors mathlib) and tag the file as a known upstream duplicate.
3. Once the local `preNormEDS'` is gone (option a), the 2 in-project call sites and
   their `...Original.lean` twins automatically resolve to mathlib's
   `preNormEDS'_two`; no per-site edits to the *lemma name* are needed (the name is
   identical), only the removal of the local re-declaration.

Next action: handle at the file/consolidation level — this is a fork-dedup task,
not a single-lemma upstream. Flag `LutzNagell/EllipticDivisibilitySequence.lean`
(and its `...Original.lean` sibling) as a verbatim mathlib fork in the overview's
dedup track; `preNormEDS'_two` carries `NO-mathlib-has-it` purely as a consequence.

---

## Next step

Treat `LutzNagell/EllipticDivisibilitySequence.lean` as a known fork of
`Mathlib.NumberTheory.EllipticDivisibilitySequence`; resolve the duplication at the
file level (reconcile-with-upstream / rename the genuinely-new `normEDS`/`complEDS`
extensions), at which point `preNormEDS'_two` and its four sibling base-case lemmas
vanish as upstream duplicates. No mathlib PR — mathlib already has this lemma.

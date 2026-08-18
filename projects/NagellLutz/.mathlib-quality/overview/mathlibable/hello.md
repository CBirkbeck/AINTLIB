# /mathlibable report — `hello`

> Step-9 mathlibable assessment, NagellLutz project. Single declaration.
> Source: `projects/NagellLutz/LutzNagell/Basic.lean:1`.

## TL;DR

`def hello := "world"` is the **verbatim Lake project template stub** (`lake new` /
`lake init` scaffolding), not mathematics. It has no mathematical content, no namespace,
no imports, and **zero call sites** anywhere in the repository. The project's own
`/overview` analysis already classified it as dead template to REMOVE.

**Verdict: `NO-composable-from-mathlib`** — degenerate. There is nothing to add to
mathlib; the correct action is to delete the line. (NO-composable is the closest of the
five buckets: the "content", a string literal `"world"`, is trivially producible inline
and is in no sense a mathematical result mathlib would host. It is recorded as NO-* rather
than YES-* / BORDERLINE because there is unambiguously no contribution here.)

---

## Baseline (Phase 0)
- lake build:               not run (local build stale per task; irrelevant — the decl is a
                            zero-dependency string literal that needs no mathlib to elaborate)
- decl `hello`:             ✓ resolved at `projects/NagellLutz/LutzNagell/Basic.lean:1`
- qualified name:           `hello` (VERIFIED — no `namespace` and no `open` in `Basic.lean`;
                            file is a single line)
- kind:                     `def`
- has sorry:                no
- module docstring summary: none — file is a one-line placeholder; `.mathlib-quality`
                            inventory notes "`Basic.lean` is currently a one-line placeholder
                            (`def hello := "world"`) with no Nagell-Lutz / EDS content."

## Statement (Phase 1)

`hello` is a definition binding the identifier `hello` to the string literal `"world"`.

There is **no mathematical statement**. The value is `("world" : String)`. This is the
standard Lean 4 library scaffolding produced by `lake new`/`lake init`: the generated
`Basic.lean` holds a single trivial definition, consumed by the generated `Main.lean` via
`IO.println s!"Hello, {hello}!"`.

Variables / typeclasses: none.
Hypotheses: none.
Conclusion (math): n/a — not a mathematical object.
Conclusion (Lean): `hello : String`.

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: not a new structure, not a project main result, not named after a person/place — a
template placeholder with no mathematical role.

## One-line check (Phase 2b)

Body line count: 1 substantive line (`"world"`).
One-liner verdict: **ONE-LINER** (kind is `def`).

Exemption check:
| Exemption                        | Applies? | Evidence                                                            |
|----------------------------------|----------|--------------------------------------------------------------------|
| Avoid defeq abuse                | no       | No downstream proof exists; body is a literal — nothing to seal.   |
| Avoid typeclass diamonds         | no       | No instances involved; `String` literal, no `Mul`/`Zero`/etc.     |
| Mark semantic intent / API name  | no       | No consumer; the name `hello` carries no domain meaning.          |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION** — strongest possible negative signal for
mathlib inclusion. Combined with K = 0 call sites (Phase 6), the case for NO is overwhelming.

## Literature search table (Phase 3)

EXHAUSTIVE protocol is run, but the "concept" is a string literal `"world"` — there is no
mathematical concept to locate. Channels are recorded honestly as n/a, with the one
substantive query (identifying the line as Lake boilerplate) reported.

| #  | Channel                          | Query                                                              | Hit? | Standard form found                  | Notes |
|----|----------------------------------|-------------------------------------------------------------------|------|--------------------------------------|-------|
| 1  | WebSearch (specific form)        | lake new lean4 default template `def hello := "world"`            | yes  | Lake `lake new` library scaffolding   | Lean4 Lake README + FP-in-Lean confirm generated `Basic.lean` has a single trivial `hello` def used by `Main.lean`'s `s!"Hello, {hello}!"` |
| 2  | WebSearch (general form)         | n/a — no mathematical "general form" of a `String` literal        | n/a  | n/a                                   | Not a mathematical statement. |
| 3  | WebSearch (named-after/aliases)  | n/a — not a named theorem/concept                                 | n/a  | n/a                                   | Placeholder identifier, no aliases. |
| 4  | ChatGPT MCP                      | n/a — MCP down per task; no math question to ask of a literal     | n/a  | n/a                                   | No mathematical content to second-opinion; fallback not needed. |
| 5  | Local references                 | grep `.mathlib-quality/references/` for "hello"                   | n/a  | n/a                                   | Concept-free; refs are about Nagell-Lutz/EDS, not template stubs. |
| 6  | nLab                             | n/a — not a categorical/mathematical concept                      | n/a  | n/a                                   | A string literal has no nLab entry. |
| 7  | nCatLab                          | n/a — not categorical                                             | n/a  | n/a                                   | — |
| 8  | Stacks Project                   | n/a — not an algebraic-geometry concept                           | n/a  | n/a                                   | — |
| 9  | MathOverflow / Math.SE           | n/a — no mathematical question                                    | n/a  | n/a                                   | — |
| 10 | recent arXiv                     | n/a — no research concept                                         | n/a  | n/a                                   | — |

### Literature summary (Phase 3)

Concept identified as: **none (Lake project template boilerplate)** — not a mathematical
concept. The only positive identification is that `def hello := "world"` is the standard
Lean 4 / Lake `lake new` library scaffolding.
Sources agree on the standard form: yes — it is universally the throwaway placeholder in the
generated `Basic.lean`/`<Lib>/Basic.lean`.
Most general standard form: n/a.
Disagreement with the literature: n/a — there is no mathematical literature in play.

The literature search returning no mathematical concept is itself the signal: this
declaration is not a candidate for mathlib at all.

## Generality analysis (Phase 4)

Literature-standard form: n/a — no mathematical statement to generalise.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| — | (none)                 | `def hello := "world"` | n/a                   | n/a                 | No parameters, hypotheses, or typeclasses. |

### Generality verdict (Phase 4b)
The current form is: **n/a** (no parameters to weaken). Weakening opportunities: 0.

### Modern-idiom check (Phase 4c)
All seven rows answer **no**: there is no "let X be a foo" preamble, no sequence/metric to
filterise, no construction to characterise universally, no closure-predicate to bundle, no
field/vector-space typeclass to weaken, no 1-categorical statement to lift, and no concrete
index to generalise. The body is a `String` literal.
Modern idiom available: **no** — there is no mathematics to reformulate.

## Diamond / defeq risk (Phase 4.5)

Kind is `def`, so this phase runs.

| # | Risk                         | Verdict | Evidence / rationale                                                        |
|---|------------------------------|---------|-----------------------------------------------------------------------------|
| 1 | Typeclass diamond           | none    | No typeclasses; `hello : String` participates in no instance search.        |
| 2 | Reducibility leak           | none    | Not `@[reducible]`; body is a literal — defeq-checking it is trivial/harmless.|
| 3 | Non-canonical unfolding     | none    | `simp`/`rfl` unfolding `hello` to `"world"` surprises no one; no consumers.  |
| 4 | Instance priority collision | none    | Not an `instance`.                                                          |
| 5 | Universe-polymorphism       | none    | `String : Type`, monomorphic; no universe variables.                       |
| 6 | Coercion ambiguity          | none    | No `CoeFun`/`CoeSort`; a plain `String`.                                    |

### Risk verdict (Phase 4.5)
Overall risk: **NONE**. (Risk is nil precisely because the def is content-free — which is
also why it is not a mathlib contribution.)

## Mathlib search-status (Phase 5)

| Method | Query | Result |
|--------|-------|--------|
| [A] Lean-Finder       | n/a — no mathematical statement to phrase                 | n/a |
| [B] Loogle            | n/a — `String`-valued nullary def; no informative type pattern (a `Loogle` for `: String` returns thousands of unrelated literals) | n/a |
| [C] LeanSearch        | n/a — no natural-language math statement                  | n/a |
| [D] Grep mathlib src  | `def hello` / `:= "world"` over `Mathlib/`                | no hits — mathlib does not contain template stubs |
| [E] Name pattern      | bare name `hello` in mathlib                              | no hit as a mathlib def of this form; mathlib has no `hello` placeholder |

Searched for both the current form and the (nonexistent) literature-standard form.

Concluded: **not in mathlib** — and correctly so; mathlib contains no `lake new` template
placeholders. There is nothing here mathlib has or should have.

## Composition check (Phase 6)

### Call sites — `hello`
Internal use count: **0** (within NagellLutz, excluding the declaring file).
External-to-file callers: **0 files**.

Repo-wide grep for `\bhello\b` in `*.lean` (excluding `.lake`) returns exactly two lines,
both being the template stub itself:
- `projects/NagellLutz/LutzNagell/Basic.lean:1` — the declaration under assessment.
- `projects/AdicSpaces/Adic spaces/Basic.lean:1` — the *identical* stub in a sibling
  project, confirming this is the unmodified Lake template default (not bespoke code).

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | no caller anywhere in the repo |

Inline-derivation grep: (none) — nothing re-derives `"world"`; it is simply unused.

Per the Phase 6.0.1 table: **K = 0 internal uses, no inline re-derivation → dead code /
template stub.** This matches the project `/overview` Step-8 finding exactly.

### Composition check (Phase 6a)
Can `hello` be "derived" from mathlib in ≤3 calls? Trivially: the value is the literal
`"world" : String`, reproducible inline with zero mathlib calls (`("world" : String)`).
Conclusion: **COMPOSABLE** (degenerate — it is a literal, not a derivation).

---

## Verdict: `hello`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): no mathematical concept; positively identified as Lake
  `lake new` template boilerplate.
- Generality analysis (Phase 4): n/a — no parameters; modern-idiom check all `no`.
- Mathlib search (Phase 5): not in mathlib, and mathlib correctly hosts no template stubs.
- Composition check (Phase 6): COMPOSABLE — value is the literal `"world"`; K = 0 call sites.

**Rationale:**

`def hello := "world"` is not mathematics. It is the unmodified Lean 4 / Lake project
template scaffolding — the same line appears verbatim in `AdicSpaces/Adic spaces/Basic.lean`,
which is the tell that no one ever replaced the generated placeholder. It has no namespace,
no imports, no hypotheses, no mathematical statement, and **zero consumers** anywhere in the
repository. The project's own `/overview` already flagged it ("template stub
`def hello := "world"`. REMOVE — genuine dead template", `07-api-and-junk.md:203`).

Of the five buckets, this is recorded as **NO-composable-from-mathlib**: the trivial
"content" (a `String` literal) is producible inline with zero mathlib calls, so under no
reading is a new mathlib lemma warranted. It is firmly a NO (not BORDERLINE) because there
is no judgment call to make — there is simply nothing to contribute. The actionable outcome
is **deletion**, not refactoring to a mathlib call.

**Refactor / action plan (REQUIRED):**
- Mathlib building blocks: none needed — the value is `("world" : String)`.
- Call sites in the project: **K = 0**. Nothing imports or uses `hello`.
- Action: **delete `projects/NagellLutz/LutzNagell/Basic.lean` entirely** (it is a
  one-line placeholder with no other content), and drop `import LutzNagell.Basic` from
  `projects/NagellLutz/LutzNagell.lean:1`. No call sites to update; no behaviour change.
  (Outside the scope of this read-only mathlibable assessment — recorded as the
  recommended cleanup follow-up. This duplicates the existing `/overview` Step-8 REMOVE
  recommendation; it is not a mathlib-upstreaming action.)

**Next action:** delete the dead template stub `hello` (and its now-empty `Basic.lean` +
the `import LutzNagell.Basic` line). Nothing to upstream to mathlib.

---

### Note on the project's "forks mathlib" context

The task flagged that NagellLutz forks `Mathlib.AlgebraicGeometry.EllipticCurve.Division\
Polynomial.*` and `Mathlib.NumberTheory.EllipticDivisibilitySequence`, so a decl might
already be in mathlib. That caveat is relevant for the project's *mathematical* declarations
(in `DivisionPolynomial.lean`, `EllipticDivisibilitySequence.lean`, etc.) — but it does not
apply to `hello`, which is template boilerplate with no relationship to division polynomials
or EDS. No mathlib fork comparison is meaningful here.

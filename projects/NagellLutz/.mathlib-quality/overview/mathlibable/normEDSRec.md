# /mathlibable report — `normEDSRec`

> **Headline:** `normEDSRec` is a **verbatim fork of an existing mathlib declaration**.
> Mathlib ships it identically at
> `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:374` (same `@[elab_as_elim]`,
> same `noncomputable def normEDSRec`, same signature, same proof body, same bare
> qualified name). **Verdict: NO-mathlib-has-it.**

> Step-9 (overview) mathlibable assessment, single declaration.
> Project: `NagellLutz` (Nagell–Lutz theorem; elliptic curves; division polynomials; EDS).
> The file forks `Mathlib.NumberTheory.EllipticDivisibilitySequence` (plus parts of
> `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`) to host the project's
> `General*` / `PID*` / `Complement` / `ComplEDS` tracks — so the decl is expected to
> already be upstream. It is.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task brief; reasoning from source — the decl is a verbatim copy of a mathlib decl that elaborates upstream)
- decl `normEDSRec`:        ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1001–1008` (signature head on line 1002; base name `normEDSRec` on line 1003)
- qualified name:           **`normEDSRec`** (bare — declared inside `section NormEDS` opened at line 881, within the `@[expose] public section` at line 81; there is **no enclosing `namespace`** at that point: `namespace EllSequence` (90) closed at 597, `namespace IsEllSequence` (643) closed at 702, `section PreNormEDS` (704) closed at `end PreNormEDS` (879) — all before line 1003)
- kind:                     `def` (`noncomputable def`, attribute `@[elab_as_elim]`)
- has sorry:                no (the whole file has 0 `sorry`)
- module docstring summary: "Elliptic divisibility sequences — defines EDS and constructs normalised EDSs from initial terms." Near-verbatim fork of mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (same copyright header: "Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.").

---

### Statement (Phase 1)

`normEDSRec` is a **custom recursion / induction principle** (a `Sort u`-valued
eliminator, hence `@[elab_as_elim]`) for proving a family `P : ℕ → Sort u` of
every natural number, tailored to the recurrence shape of a **normalised elliptic
divisibility sequence** (`normEDS`).

To conclude `P n` for all `n`, the user supplies:
- base cases `P 0`, `P 1`, `P 2`, `P 3`, `P 4`;
- an **even step**: for every `m`, from `P (m+1), P (m+2), P (m+3), P (m+4), P (m+5)` conclude `P (2*(m+3))`;
- an **odd step**: for every `m`, from `P (m+1), P (m+2), P (m+3), P (m+4)` conclude `P (2*(m+2)+1)`.

It is the **fixed-window specialisation of the strong recursor `normEDSRec'`**
(project lines 987–992 / mathlib 358–363): the body is literally
`normEDSRec' zero one two three four (fun _ ih ↦ by apply even <;> exact ih _ <| by linarith only) (fun _ ih ↦ by apply odd <;> exact ih _ <| by linarith only) n`,
i.e. it feeds the bounded strong-recursion hypotheses the finitely many
predecessors they need. The five-/four-predecessor windows mirror the arithmetic
of `normEDS_even` / `normEDS_odd`, letting one run `induction n using normEDSRec`
and discharge each EDS term from exactly the earlier terms in its defining
recurrence.

Variables / typeclasses (Lean side):
- `{P : ℕ → Sort u}` — a `Sort`-valued motive on `ℕ`. **No algebraic typeclasses, no
  ring `R`, no mention of `normEDS` in the type.** It is *named after* the EDS
  use-case but is pure `ℕ`-recursion infrastructure.

Hypotheses (Lean side):
- `zero..four : P 0 .. P 4`; `even`, `odd` as above; `(n : ℕ)` the index to eliminate at.

Conclusion (math): an induction scheme valid for all `n : ℕ` whose step windows match the normalised-EDS doubling recurrences.
Conclusion (Lean): `P n`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (recursion-principle helper).
Reason: introduces no new mathematical *structure*, is not a named theorem; it is
recursion-scheme infrastructure derived in two lines from `normEDSRec'`.
(Literature width is normally EXHAUSTIVE regardless; here it is moot — the decl is
a verbatim mathlib fork, see Phase 3 / Phase 5.)

### One-line check (Phase 2b)

Body line count: 2 substantive lines (`normEDSRec' … <even glue>` / `<odd glue> n`).
One-liner verdict: **borderline ONE-LINER** (a thin 2-line wrapper over `normEDSRec'`).
Exemption analysis is **moot**: the decl is identical to an existing mathlib decl
(Phase 5), so the bucket is decided by NO-mathlib-has-it, not by the one-liner gate.

---

### Literature search (Phase 3)

**Moot for the verdict**: `normEDSRec` is a verbatim fork of an existing mathlib
declaration (Phase 5), authored by the same person (David Kurniadi Angdinata) who
wrote the mathlib file. "Is this the standard form at the right generality" is not
what decides the bucket. For completeness:

| #  | Channel                          | Query / status                                                         | Hit? | Notes |
|----|----------------------------------|-------------------------------------------------------------------------|------|-------|
|  1 | WebSearch (specific form)        | n/a — not run; decl is a known mathlib fork (Phase 5 decisive)         | n/a  | "Elliptic divisibility sequence" recursion traces to Ward (1948); a Lean `@[elab_as_elim]` recursor is a formalisation artefact, not a literature object |
|  2 | WebSearch (general form)         | n/a — same reason                                                      | n/a  | The general object is the strong recursor `normEDSRec'` (built on `Nat.evenOddStrongRec`), itself forked here |
|  3 | WebSearch (named-after/aliases)  | n/a — same reason                                                      | n/a  | "EDS" = Ward elliptic divisibility sequence; the recursor itself has no literature name |
|  4 | ChatGPT MCP                      | n/a — MCP down in task env; decl is a fork so a second opinion adds nothing | n/a  | — |
|  5 | Local references                 | `projects/NagellLutz/.mathlib-quality/references/` and `refs/` checked  | n/a  | **Both absent on this checkout** — recorded n/a (refs are local-only per CLAUDE.md) |
|  6 | nLab                             | n/a                                                                    | n/a  | a Lean recursor is not an nLab concept |
|  7 | nCatLab                          | n/a                                                                    | n/a  | not categorical |
|  8 | Stacks Project                   | n/a                                                                    | n/a  | not an algebraic-geometry concept (it is `ℕ`-recursion infra) |
|  9 | MathOverflow / MSE               | n/a                                                                    | n/a  | recursor-formalisation detail, not a math question |
| 10 | recent arXiv                     | n/a                                                                    | n/a  | — |

### Literature summary (Phase 3)

Concept identified as: a **specialised ℕ-induction principle matching the
normalised-EDS odd/even doubling recurrence** — a formalisation convenience, not a
named theorem. Underlying mathematics (EDS) is due to **Morgan Ward, "Memoir on
elliptic divisibility sequences", Amer. J. Math. 70 (1948)**; the recursor is an
artefact of the Lean development of `normEDS`.
Sources agree on the standard form: n/a (no literature form for a Lean recursor).
Disagreement with the literature: none — not a literature object.

---

### Generality analysis (Phase 4)

Literature-standard form (from Phase 3): n/a (formalisation artefact).

| # | Parameter / hypothesis | Current Lean form | Weaker form exists? | Reason |
|---|------------------------|-------------------|---------------------|--------|
| 1 | `{P : ℕ → Sort u}`     | universe-poly `Sort`-valued motive on `ℕ` | NO | Already maximally general for a `ℕ`-eliminator: `Sort u` covers `Prop` and all data; index is `ℕ` because EDS terms recurse over `ℕ`. |
| 2 | base/step windows      | exact windows matching `normEDS_even`/`normEDS_odd` | NO (by design) | Narrowing breaks the intended `induction … using normEDSRec` use-pattern. The *strong* companion `normEDSRec'` already supplies maximally-permissive (full `< n`) hypotheses, and `normEDSRec` is the deliberately-convenient specialisation. **Both already coexist in mathlib.** |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (`Sort u`, universe polymorphic; it sits
alongside the strong recursor `normEDSRec'` exactly as in mathlib).
Number of weakening opportunities: 0. Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

Modern idiom available: **no**. This *is* the modern mathlib idiom — it is literally
the current mathlib declaration (same author, `@[elab_as_elim]`, `Sort u`,
delegating to `Nat.evenOddStrongRec` via `normEDSRec'`). Nothing to modernise.

---

### Diamond / defeq risk (Phase 4.5) — kind is `def`

`normEDSRec` is a `noncomputable def` (an eliminator), not a `class`/`instance`,
carries no typeclass data, defines no new typeclass-search path and no coercion.

| # | Risk                         | Verdict | Rationale |
|---|------------------------------|---------|-----------|
| 1 | Typeclass diamond            | none    | No instances introduced; motive `P` is an argument, not resolved by typeclass search. |
| 2 | Reducibility leak            | none    | Not `@[reducible]`; `@[elab_as_elim]` affects only elaboration of `induction … using`, not defeq. |
| 3 | Non-canonical unfolding      | low     | Body unfolds to `normEDSRec'`; relevant only under explicit `induction using`, the intended use. |
| 4 | Instance priority collision  | n/a     | not an instance. |
| 5 | Universe-polymorphism issues | none    | `Sort u` is the correct fully-polymorphic choice; mathlib ships it identically. |
| 6 | Coercion ambiguity           | none    | no `CoeFun`/`CoeSort`. |

### Risk verdict (Phase 4.5): **NONE** — and moot, since the identical def is already in mathlib.

---

### Mathlib search-status: `normEDSRec` (Phase 5 — DECISIVE)

[A] Lean-Finder       n/a — a direct source match is stronger and unambiguous here
[B] Loogle            n/a — same
[C] LeanSearch        n/a — same
[D] Grep mathlib src  `grep -nE "normEDSRec" .lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
                      → **HIT**: line 374 `noncomputable def normEDSRec {P : ℕ → Sort u}` (strong variant `normEDSRec'` at line 358; internal use at 511)
[E] Name pattern      grep `normEDSRec` across mathlib → only `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`

Searched for both:
  - the user's current form — **exact match**.
  - the more-general form — the strong recursor `normEDSRec'`, **also present in
    mathlib** (line 358) and **also forked verbatim** here (line 987).

**Side-by-side (project 1001–1008 vs mathlib 373–380):**

```
project 1002:  noncomputable def normEDSRec {P : ℕ → Sort u}
mathlib 374:   noncomputable def normEDSRec {P : ℕ → Sort u}
project 1003:  (zero : P 0) (one : P 1) (two : P 2) (three : P 3) (four : P 4)
mathlib 375:   (zero : P 0) (one : P 1) (two : P 2) (three : P 3) (four : P 4)
project 1004:  (even : ∀ m : ℕ, P (m + 1) → P (m + 2) → P (m + 3) → P (m + 4) → P (m + 5) → P (2 * (m + 3)))
mathlib 376:   (even : ∀ m : ℕ, P (m + 1) → P (m + 2) → P (m + 3) → P (m + 4) → P (m + 5) → P (2 * (m + 3)))
project 1005:  (odd : ∀ m : ℕ, P (m + 1) → P (m + 2) → P (m + 3) → P (m + 4) → P (2 * (m + 2) + 1)) (n : ℕ) :
mathlib 377:   (odd : ∀ m : ℕ, P (m + 1) → P (m + 2) → P (m + 3) → P (m + 4) → P (2 * (m + 2) + 1)) (n : ℕ) :
project 1006:  P n :=
mathlib 378:   P n :=
project 1007:  normEDSRec' zero one two three four (fun _ ih ↦ by apply even <;> exact ih _ <| by linarith only)
mathlib 379:   normEDSRec' zero one two three four (fun _ ih => by apply even <;> exact ih _ <| by linarith only)
project 1008:  (fun _ ih ↦ by apply odd <;> exact ih _ <| by linarith only) n
mathlib 380:   (fun _ ih => by apply odd <;> exact ih _ <| by linarith only) n
```

The **only** difference is the lambda-arrow glyph `↦` (project) vs `=>` (mathlib) —
identical surface syntax for the same `fun`. Same `@[elab_as_elim]` attribute, same
docstring, same signature, same body, same top-level (un-namespaced) name.

Concluded: **found in mathlib as `normEDSRec`; identical form**
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:374`). The strong variant
`normEDSRec'` is likewise present (`…:358`) and likewise forked.

---

### Composition check (Phase 6)

#### Call sites — `normEDSRec`

Internal use count (within `NagellLutz`, excluding the declaring file): **1**.
External-to-file callers: **1 distinct file**.

| Caller file:line                                                    | Usage pattern |
|---------------------------------------------------------------------|----------------|
| `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:202`  | `induction n using normEDSRec with` |

(Also 1 use of the *strong* variant `normEDSRec'` inside the declaring file at line
1121, `induction n using normEDSRec'`, which is a separate decl.)

Inline-derivation grep: (none) — the eliminator is used via `induction … using`, not re-derived.

#### Composition attempt

Not a "compose from primitives" kind of statement. But note: the project also forks
`normEDSRec'`, and `normEDSRec`'s body is `normEDSRec' … <2-line glue>`. Within
mathlib the decl *already exists outright*; no composition is needed.
Conclusion: **NOT-COMPOSABLE** (and irrelevant — mathlib has the decl verbatim).

---

## Verdict: `normEDSRec`

**Category:** **NO-mathlib-has-it**

**Evidence:**
- Literature search (Phase 3): moot — formalisation artefact, not a literature object; underlying EDS theory is Ward (1948).
- Generality analysis (Phase 4): MAXIMALLY GENERAL (`Sort u`, universe-poly); modern idiom = the mathlib decl itself; nothing to change.
- Mathlib search (Phase 5): **found in mathlib as `normEDSRec` — identical form**, `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:374`. Strong variant `normEDSRec'` also present (`…:358`).
- Composition check (Phase 6): NOT-COMPOSABLE (and moot — mathlib has the decl verbatim). 1 internal call site (`DivisionPolynomialDegree.lean:202`).

**Rationale:**

The project's `EllipticDivisibilitySequence.lean` is a near-verbatim fork of
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (identical copyright
header, same author David Kurniadi Angdinata), and `normEDSRec` is one of the
forked declarations. The project copy (lines 1001–1008) and the mathlib copy
(lines 373–380) are **character-for-character identical** apart from the
lambda-arrow glyph (`↦` vs `=>`), which is the same syntax. Both are top-level (no
namespace), so the qualified name is `normEDSRec` in each. Mathlib already has this
exact declaration — there is nothing to add and nothing to generalise (its strong
companion `normEDSRec'`, the maximally-general version, is *also* already in mathlib
and also forked here). The mathlib pin in `lakefile.toml` (`09b373db6e24`) is the
mathlib that ships this file.

**WHY not (refactor-actionable):**
Mathlib already has `normEDSRec`, identically. The project copy exists only because
the whole file was forked to host the project's `General*` / `PID*` / `Complement` /
`ComplEDS` extensions (e.g. `compl₂EDS`, `complEDS`, and the parallel `complEDSRec`
/ `complEDSRec'` recursors). The single consumer (`induction n using normEDSRec` at
`DivisionPolynomialDegree.lean:202`) resolves identically against the mathlib
declaration — same bare name, same `@[elab_as_elim]` signature — so dropping the
local copy needs no call-site edit beyond importing the mathlib module.

  Existing mathlib decl:        `normEDSRec`
  Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:374`
  Our form follows in ≤1 line:  it *is* the mathlib form (identical signature + body); no derivation needed.
  Call sites in our project (Phase 6.0):  K = 1  (`DivisionPolynomialDegree.lean:202`)
  Refactor plan — this is a **whole-file de-fork**, not a one-decl deletion:
    1. If the fork carries NO local divergence from mathlib beyond the
       `General*`/`PID*`/`Complement`/`ComplEDS` additions, delete the duplicated
       mathlib-origin declarations (`preNormEDS`, `normEDS`, `normEDSRec'`,
       `normEDSRec`, the `normEDS_*` lemmas, etc.) and add
       `import Mathlib.NumberTheory.EllipticDivisibilitySequence`, keeping only the
       genuinely-new project material.
    2. The lone `normEDSRec` consumer at `DivisionPolynomialDegree.lean:202`
       (`induction n using normEDSRec with`) then binds to the mathlib declaration
       unchanged — no argument-order or dot-notation difference (same un-namespaced
       name, same signature).
    Caveat: do this as a coordinated de-dup of the forked file (the project's
    `lane:cleanup` / dedup track), NOT as an isolated edit — many sibling
    declarations in the same file have the same status and must be removed together
    to avoid a half-forked module. (Mind the file's `@[expose] public section` /
    module-system wrapper when splitting.)

  Next action: route into the project's mathlib-fork dedup pass (remove the forked
  mathlib-origin decls and import the mathlib module) rather than a standalone
  `normEDSRec` deletion. **No mathlib PR — mathlib already has it.**

---

## Next step

Do not open a mathlib PR — `normEDSRec` is already in mathlib
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:374`), identically. Route
this into the project's whole-file de-fork / dedup of
`EllipticDivisibilitySequence.lean` against the upstream module: drop the duplicated
mathlib-origin declarations and `import Mathlib.NumberTheory.EllipticDivisibilitySequence`,
keeping only the project's genuinely-new `General*` / `PID*` / `Complement` /
`ComplEDS` material; the single consumer at `DivisionPolynomialDegree.lean:202` then
binds to the mathlib `normEDSRec` with no change.

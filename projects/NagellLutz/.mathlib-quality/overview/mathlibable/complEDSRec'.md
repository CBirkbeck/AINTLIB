# /mathlibable report — `complEDSRec'`

> **Headline:** This declaration is **already in mathlib**, byte-for-byte identical (attribute +
> signature + proof term), under the *same qualified name* (`complEDSRec'`, top-level, no namespace).
> The project file `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a **standalone
> fork** of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` and re-defines the entire EDS API,
> including this recursor. Verdict: **NO-mathlib-has-it**.

---

### Baseline (Phase 0)
- lake build:               not run (env note: local build stale). Assessment reasons from source + the
                            vendored mathlib copy under `.lake/packages/mathlib/`, which is authoritative for
                            "is it in mathlib".
- decl `complEDSRec'`:      ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1624`
                            (docstring opens at :1618; `noncomputable def` line is :1624)
- kind:                     `noncomputable def` (a recursor / eliminator; `@[elab_as_elim]`)
- has sorry:                no
- module docstring summary: "Elliptic divisibility sequences" — defines EDS and constructs normalised EDSs
                            from initial terms (a verbatim fork of the mathlib EDS file).

**Qualified name (VERIFIED).** The `def` sits inside `section ComplEDS` (opened :1524, closed `end ComplEDS`
:1644). The nearest `namespace EllSequence` (:1356) was already closed at `end EllSequence` (:1431). A
`section` does **not** introduce a namespace prefix. Therefore the true qualified name is **`complEDSRec'`**
(top-level, no namespace) — matching the parsed guess in the prompt.

---

### Statement (Phase 1)

`complEDSRec'` is a **strong (course-of-values) recursion / elimination principle on `ℕ`,
split by even/odd parity with an offset that skips the small base cases**. It is a piece of
recursion *infrastructure* specialised to the shape of the `complEDS'` recurrence — not a
mathematical theorem about elliptic divisibility sequences.

To define a family `P : ℕ → Sort u`, it suffices to provide:
- `P 0` and `P 1` (base cases);
- for every `m`, a way to build `P (2*(m+1))` from `P k` for *all* `k < 2*(m+1)` (even step, strong IH);
- for every `m`, a way to build `P (2*(m+1)+1)` from `P k` for *all* `k < 2*(m+1)+1` (odd step, strong IH).

From these one obtains `P n` for every `n : ℕ`. It is implemented by deferring to
`Nat.evenOddStrongRec`, dispatching the `0`/`1` base cases by a `rintro (_ | _)` on the parity index.

Variables / typeclasses (Lean side):
- `{P : ℕ → Sort u}` — the motive (no algebraic typeclasses; pure `ℕ`-recursion, universe-polymorphic).

Hypotheses (Lean side): `zero`, `one`, `even`, `odd` — as above (the four "minor premises" of the eliminator).

Conclusion (math): every `n : ℕ` is reached by a parity-offset strong induction.
Conclusion (Lean): `(n : ℕ) : P n`.

Exact body (project :1624–1628):
```lean
@[elab_as_elim]
noncomputable def complEDSRec' {P : ℕ → Sort u} (zero : P 0) (one : P 1)
    (even : ∀ m : ℕ, (∀ k < 2 * (m + 1), P k) → P (2 * (m + 1)))
    (odd : ∀ m : ℕ, (∀ k < 2 * (m + 1) + 1, P k) → P (2 * (m + 1) + 1)) (n : ℕ) : P n :=
  n.evenOddStrongRec (by rintro (_ | _) h; exacts [zero, even _ h])
    (by rintro (_ | _) h; exacts [one, odd _ h])
```

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a bespoke recursion principle (helper eliminator) tailored to the `complEDS'` recurrence;
it is not a named theorem, not a new mathematical structure, and not a `## Main results` entry. It is
support scaffolding for the `complEDS'` definition/lemmas. (Literature width is exhaustive regardless;
recorded here only for framing — and in this case the mathlib search short-circuits everything anyway.)

### One-line check (Phase 2b)

Body line count: 2 substantive lines (the `n.evenOddStrongRec (...) (...)` application).
One-liner verdict: **MULTI-LINE-ish / n/a** — it is a `def`, but the body is a single
`evenOddStrongRec` application with two `by`-tactic minor premises; not a one-liner alias. The Phase-2b
exemption table is moot because the decl is identical to an existing mathlib decl (Phase 5), so the
verdict is fixed independent of the one-liner analysis. Recorded as **n/a**.

---

### Literature search (Phase 3)

This is **recursion-scheme infrastructure**, not a mathematical statement with a "standard form" in the
literature. The relevant "literature" is mathlib's own recursor conventions. The exhaustive channel sweep
is therefore largely `n/a` by *kind*, and — decisively — the mathlib search (Phase 5) found the decl
already present and identical, which renders the literature-standard-form question irrelevant to the
verdict (you cannot be "more general than the literature" than a decl that is literally already upstream).

| #  | Channel                           | Query                                                                 | Hit? | Standard form found | Notes |
|----|-----------------------------------|-----------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)         | "even odd strong recursion natural numbers Lean"                      | n/a  | —                   | This is a Lean/mathlib recursor idiom, not a board-level math concept; the canonical reference IS mathlib `Nat.evenOddStrongRec`. |
|  2 | WebSearch (general form)          | "course-of-values induction parity ℕ recursion principle"             | n/a  | strong (well-founded) induction on `ℕ` | The general primitive is well-founded/strong induction on `ℕ` — already `Nat.strongRecOn` / `Nat.evenOddStrongRec` in mathlib. |
|  3 | WebSearch (named-after / aliases) | "elliptic divisibility sequence recursion principle complEDS"          | yes  | mathlib decl        | The only hits are mathlib's own `NumberTheory/EllipticDivisibilitySequence` and downstream forks (Angdinata's EDS development). Confirms provenance, not an external standard. |
|  4 | ChatGPT MCP                       | (env: ChatGPT MCP down — fallback to reasoning from source)            | n/a  | —                   | Skipped per environment note; not load-bearing because Phase 5 is dispositive. |
|  5 | Local references                  | grep `.mathlib-quality/references/` for "complEDS"/"recursion"          | n/a  | —                   | No project-specific source paper defines a recursor; recursors are an implementation artifact, authored by D. K. Angdinata for the mathlib EDS file. |
|  6 | nLab                              | "elliptic divisibility sequence" / "strong induction"                  | n/a  | —                   | nLab has no page on this Lean recursor; "strong induction" there is the generic well-founded principle. |
|  7 | nCatLab                           | —                                                                     | n/a  | —                   | Not a categorical concept. |
|  8 | Stacks Project                    | —                                                                     | n/a  | —                   | Not an algebraic-geometry concept (it is `ℕ`-recursion plumbing). |
|  9 | MathOverflow / MSE                | "parity strong induction recursor"                                    | n/a  | —                   | Generic strong-induction discussions only; nothing bespoke to this offset scheme. |
| 10 | recent arXiv (≤5y)                | "elliptic divisibility sequence" formalization                        | yes  | —                   | Hits concern EDS *mathematics* (Ward sequences, division polynomials), not a recursion principle; irrelevant to this helper. |

### Literature summary (Phase 3)

Concept identified as: a **parity-split strong-recursion eliminator on `ℕ`** (an offset variant of
`Nat.evenOddStrongRec`), authored as infrastructure for the `complEDS'` recurrence.
Sources agree on the standard form: **n/a** — there is no external "literature standard" for a Lean recursor;
the governing convention is mathlib's, and mathlib already *contains this exact declaration*.
Most general standard form: the underlying primitive (`Nat.evenOddStrongRec` / strong induction on `ℕ`) is
already in mathlib; `complEDSRec'` is the EDS-shaped specialisation of it that mathlib also already ships.
Disagreement with the literature: none.

---

### Generality analysis (Phase 4)

Literature-standard form (from Phase 3): the general primitive is `Nat.evenOddStrongRec`; `complEDSRec'`
is the deliberate EDS-shaped specialisation (base cases at `0,1`, even/odd steps offset by `+1`).

| # | Parameter / hypothesis | Current Lean form | Literature/mathlib form | Weaker form exists? | Reason |
|---|---|---|---|---|---|
| 1 | `{P : ℕ → Sort u}` | universe-poly motive over `ℕ` | identical in mathlib | NO | already maximally general for a `ℕ`-recursor (`Sort u`, no typeclass constraints). |
| 2 | `zero/one/even/odd` minor premises | parity-offset strong-IH steps | identical in mathlib | NO | the offsets (`2*(m+1)`, `2*(m+1)+1`) are dictated by the `complEDS'` recurrence; weakening them would defeat the purpose. The maximally-general underlying recursor (`Nat.evenOddStrongRec`) already exists separately. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** for its purpose (it *is* the mathlib form — see Phase 5).
Number of weakening opportunities found: 0.
There is no "generalise first" target: the more-general primitive (`Nat.evenOddStrongRec`) is *already*
in mathlib and is what `complEDSRec'` is built on. The decl is the intended specialisation, and that
specialisation is itself already upstream.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Reformulation | Downstream |
|---|---|---|---|---|
| 1 | bundled hyps → typeclasses? | no | — | minor premises of an eliminator; not typeclass-shaped. |
| 2 | sequences/metric → filters/topology? | no | — | pure `ℕ`-recursion; no topology. |
| 3 | construction → universal property? | no | — | a recursor is the universal property here; it's already in eliminator form. |
| 4 | set+closure → bundled substructure? | no | — | not a substructure. |
| 5 | field/metric-specific → weaker typeclass? | no | — | no typeclasses at all. |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index → general algebra? | no | — | the index `ℕ` is intrinsic; the recurrence is defined on `ℕ`. |

Modern idiom available: **no**. The decl is already in idiomatic mathlib form — indeed it *is* a verbatim
mathlib declaration. One-line reason: it is a standard `@[elab_as_elim] noncomputable def` recursor
delegating to `Nat.evenOddStrongRec`, exactly the contemporary mathlib pattern (cf. `normEDSRec'`).

---

### Diamond / defeq risk — `complEDSRec'` (Phase 4.5)

The decl is a `def`, so the phase runs. But the risk question is moot for the *verdict* (it is identical to
an existing mathlib def, so mathlib has already accepted whatever risk profile it carries). Recorded for
completeness:

| # | Risk | Verdict | Rationale |
|---|---|---|---|
| 1 | Typeclass diamond | none | No instances declared; no typeclass arguments. Cannot create a diamond. |
| 2 | Reducibility leak | none | Not `@[reducible]`; sealed `noncomputable def`. `@[elab_as_elim]` only affects elaboration as an eliminator, not defeq. |
| 3 | Non-canonical unfolding | low | A recursor; `simp` won't unfold it spuriously (it's used via `induction … using complEDSRec'`). |
| 4 | Instance priority collision | none | Not an `instance`. |
| 5 | Universe-polymorphism issues | none | `Sort u` motive is the maximally-flexible choice; no forced annotation. |
| 6 | Coercion ambiguity | none | No `CoeFun`/`CoeSort`. |

### Risk verdict (Phase 4.5)
Overall risk: **NONE**. (And moot: mathlib already ships this exact def.)

---

### Mathlib search-status: `complEDSRec'` (Phase 5)

**This is the dispositive phase.** The project FORKS `Mathlib.NumberTheory.EllipticDivisibilitySequence`,
so the first thing checked was that mathlib file directly — and the decl is there.

- [A] Lean-Finder      "even odd strong recursion EDS"          n/a (mathlib index stale locally) — superseded by [D] direct grep.
- [B] Loogle           `?P : ℕ → Sort u, (P 0) → (P 1) → …`     n/a — recursor signatures are awkward to Loogle; [D] is authoritative.
- [C] LeanSearch       "strong recursion principle complement EDS" n/a (index stale) — superseded by [D].
- [D] Grep mathlib src `complEDSRec'` in `.lake/packages/mathlib/` **HIT**: `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:482`.
- [E] Name pattern     `complEDSRec'` qualified                  **HIT** — same file, same (empty) namespace, same name.

**Direct evidence (grep over the vendored mathlib):**
```
.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:482:
  noncomputable def complEDSRec' {P : ℕ → Sort u} (zero : P 0) (one : P 1)
```
Surrounding mathlib context: line 481 `@[elab_as_elim]`, lines 483–486 the identical `even`/`odd`
premises and the identical `n.evenOddStrongRec (by rintro (_ | _) h; exacts [zero, even _ h]) (by rintro
(_ | _) h; exacts [one, odd _ h])` body. It sits in `section ComplEDS` (mathlib :384–:503), **no namespace**
— so the mathlib qualified name is also `complEDSRec'`.

**Byte-level comparison (re-run this assessment).** `diff` of the project decl block (project :1623–:1628)
vs the mathlib decl block (mathlib :481–:486) reported **IDENTICAL** — the attribute, the full signature
(motive, all four minor premises, the `(n : ℕ) : P n` conclusion), and the two-line `evenOddStrongRec`
proof term all match character-for-character. The *only* difference anywhere in the surrounding text is a
single blank line inside the **docstring** (mathlib :479, inserted by PR "avoid lazy continuation lines");
the declaration proper is unchanged.

`Nat.evenOddStrongRec`, the primitive both bodies delegate to, is itself in mathlib at
`Mathlib/Data/Nat/EvenOddRec.lean:51` (`noncomputable def evenOddStrongRec {P : ℕ → Sort*} …`, built on
`Nat.strongRecOn` + `Nat.even_or_odd'`). It is **not** forked by the project (grep over `projects/`:
no local `def evenOddStrongRec`).

Mathlib provenance: the file was authored by David Kurniadi Angdinata (the same Author header as the
project fork). The whole `complEDS*` API (`complEDS₂`, `complEDS'`, `complEDS`, `complEDSRec'`,
`complEDSRec`, `normEDSRec'`, `normEDSRec`, the `map_*` lemmas) is present in mathlib — the project file
is a wholesale copy.

Concluded: **found in mathlib as `complEDSRec'`** (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:482`);
**identical form** (modulo one cosmetic blank line in the docstring). Our form does not merely *follow*
from the mathlib decl — it *is* the mathlib decl.

---

### Composition check (Phase 6)

#### Call sites — `complEDSRec'`
Internal use count: **2** (both inside the declaring file `EllipticDivisibilitySequence.lean`):
- line 1641 — `complEDSRec` is built on top of it (`complEDSRec' zero one (fun _ ih => …) …`);
- line 1659 — `induction n using complEDSRec'` inside `map_complEDS'`.

External-to-file callers: **0** (no project file outside the forked EDS file references it directly; the
active file is imported by `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean`, which does not name
`complEDSRec'`). The sibling `EllipticDivisibilitySequenceOriginal.lean` is an *unused* second fork.

| Caller file:line | Usage pattern |
|---|---|
| EllipticDivisibilitySequence.lean:1641 | `complEDSRec' zero one (fun _ ih => even _ <| ih _ <| by linarith only) …` (builds `complEDSRec`) |
| EllipticDivisibilitySequence.lean:1659 | `induction n using complEDSRec' with …` (proves `map_complEDS'`) |

Inline-derivation grep: (none) — the recursor is used as-is, never re-derived inline.

Composability reading: the call-site count is low and entirely *internal to the forked file*. Because the
identical decl is already in mathlib, the "composition from mathlib primitives" question is subsumed:
mathlib's `complEDSRec'` IS the building block, and mathlib additionally exposes the more-general
`Nat.evenOddStrongRec` it is built from.

#### Composition check
Can `complEDSRec'` be obtained from mathlib in ≤3 calls? **Trivially yes — it is `mathlib.complEDSRec'`.**
- Attempt 1: `exact complEDSRec' zero one even odd n` using mathlib's decl. Result: **succeeds** (0-step;
  it is the same declaration). Were the project file to instead `import
  Mathlib.NumberTheory.EllipticDivisibilitySequence`, every reference resolves unchanged.

Conclusion: the decl is redundant with mathlib. (Formally this is **NO-mathlib-has-it**, the stronger
of the two NO buckets — mathlib has the *identical* decl, not merely composable building blocks.)

---

## Verdict: `complEDSRec'`

**Category:** **NO-mathlib-has-it**

**Evidence:**
- Literature search (Phase 3): recursion-scheme infrastructure; no external "standard form"; the only hits
  are mathlib itself and downstream forks of Angdinata's EDS development.
- Generality analysis (Phase 4): MAXIMALLY GENERAL for its purpose; the more-general primitive
  (`Nat.evenOddStrongRec`) is also already in mathlib. No modern-idiom move (Phase 4c: all `no`).
- Mathlib search (Phase 5): **found in mathlib as `complEDSRec'`,
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:482` — identical form** (a `diff` of the two decl
  blocks is IDENTICAL; one cosmetic docstring blank line aside). Same name, same (empty) namespace.
- Composition check (Phase 6): redundant; mathlib's `complEDSRec'` is the decl itself. Only 2 internal call
  sites (project :1641, :1659), 0 external.

**Rationale.**
The project's `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a **verbatim fork** of
mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (same copyright/author header, same API
surface). `complEDSRec'` is one of the declarations copied across; it is **byte-for-byte identical** to the
upstream `complEDSRec'` save a single blank line that mathlib later inserted in the docstring for the
lazy-continuation-line lint. There is therefore nothing to upstream: mathlib already has exactly this
declaration, under exactly this qualified name. This is precisely the situation the project context flagged
("this project FORKS parts of mathlib … so this decl may ALREADY be in mathlib"). The correct disposition
is **dedup against mathlib**, not a PR.

**WHY not (refactor-actionable).**
Mathlib already has the identical declaration. The project carries it only because the *entire* EDS file was
vendored as a standalone fork that does **not** `import Mathlib.NumberTheory.EllipticDivisibilitySequence`
(confirmed: no such import in the file). The right fix is at the *file* level, not this one decl:
- **Existing mathlib decl:** `complEDSRec'`
- **Located at:** `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:482`
- **Our form follows in 0 lines:** it is the same declaration —
  ```lean
  -- after `import Mathlib.NumberTheory.EllipticDivisibilitySequence`
  example {P : ℕ → Sort u} (zero : P 0) (one : P 1)
      (even : ∀ m : ℕ, (∀ k < 2 * (m + 1), P k) → P (2 * (m + 1)))
      (odd  : ∀ m : ℕ, (∀ k < 2 * (m + 1) + 1, P k) → P (2 * (m + 1) + 1)) (n : ℕ) : P n :=
    complEDSRec' zero one even odd n        -- mathlib's `complEDSRec'`, unchanged
  ```
- **Call sites in our project (Phase 6.0):** 2 — both internal to the forked file (lines 1641, 1659), 0 external.

**Refactor plan.** This decl should not be deduped in isolation, because the *whole* `complEDS*`/`normEDS*`
block of this file duplicates mathlib. Recommended (a project-level dedup ticket, not a per-decl edit):
1. Have `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` (and the dependent
   `DivisionPolynomial.lean`) `import Mathlib.NumberTheory.EllipticDivisibilitySequence` and delete the
   duplicated definitions/lemmas that mathlib already provides verbatim — including `complEDSRec'`,
   `complEDSRec`, `complEDS₂`, `complEDS'`, `complEDS`, `normEDSRec'`, `normEDSRec`, and the `map_*` lemmas.
   The 2 internal references to `complEDSRec'` (1641, 1659) then resolve against mathlib unchanged.
2. Retire the unused second fork `EllipticDivisibilitySequenceOriginal.lean` (no importers).
3. Keep in the project *only* the genuinely-new material that is **not** in mathlib (e.g. anything the
   Nagell–Lutz development adds on top of the upstream EDS API). Re-run `/overview` Step 8 to identify what,
   if anything, is net-new versus the mathlib file before deleting.

**Caveat for the human deduper.** Confirm the *vendored* mathlib pin actually contains this decl on the
project's current toolchain (it does in `.lake/packages/mathlib/` here). If a future bump ever *removed*
`complEDSRec'` from mathlib, the fork would need to retain it — but as of this pin, mathlib has it. The
single docstring blank-line difference is cosmetic and not a reason to keep the fork.

---

## Next step

Do **not** open a mathlib PR — mathlib already has `complEDSRec'`
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:482`), identical. File a project-level **dedup
ticket** to make the forked `EllipticDivisibilitySequence.lean` import the mathlib EDS file and delete the
duplicated `complEDS*`/`normEDS*` API (this decl among them), keeping only Nagell–Lutz-specific additions.
The 2 internal call sites (lines 1641, 1659) resolve against mathlib's `complEDSRec'` unchanged.

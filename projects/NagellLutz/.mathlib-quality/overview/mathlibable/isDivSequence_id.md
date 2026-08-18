# /mathlibable report — `isDivSequence_id`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz; elliptic curves;
> division polynomials; elliptic divisibility sequences).
> Declaration at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:612`.

## TL;DR

**Verdict: `NO-mathlib-has-it`.** Mathlib already contains a lemma named
`isDivSequence_id` with the same statement (the identity sequence is a
divisibility sequence) at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:97`. This project file
is a **fork** of that exact mathlib file (its unmodified twin is
`EllipticDivisibilitySequenceOriginal.lean`). The only difference is that the
project has generalised the *definition* `IsDivSequence` from a ℕ-index to a
ℤ-index — but mathlib still has the corresponding lemma about its own
definition, so this lemma is redundant under fork reconciliation, not a new
contribution.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task brief); decl read directly from source
- decl `isDivSequence_id`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:612`
- kind:                     lemma
- has sorry:                no
- module docstring summary: "Elliptic divisibility sequences (EDS) — defines EDS and constructs normalised EDSs from initial terms." (a fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence`)

**Qualified name.** The base name is `isDivSequence_id`. Namespace check:
`namespace EllSequence` opens at line 90 and closes (`end EllSequence`) at line
597; line 599 is `open EllSequence` (an *open*, not a namespace). Line 612 is
therefore at the **top level** — the file-level `@[expose] public section` (line
81) introduces no namespace. **Fully-qualified name = `isDivSequence_id`.**

---

### Statement (Phase 1)

`isDivSequence_id` asserts that the identity sequence `id : ℤ → ℤ`, `n ↦ n`, is a
**divisibility sequence**: whenever `m ∣ n`, the corresponding terms satisfy
`id m ∣ id n`, i.e. `m ∣ n`. This is immediate — for the identity sequence the
divisibility-sequence condition is the tautology `m ∣ n → m ∣ n`.

In the EDS literature this is the trivial observation that `W n = n` is the
simplest example of a divisibility (indeed elliptic divisibility) sequence.

Variables / typeclasses involved (Lean side):
- The ambient `variable {R : Type u} [CommRing R]` and `(W : ℤ → R)` are in
  scope, but **this lemma instantiates `R = ℤ` and `W = id`** — no free
  parameters remain in the statement.

Hypotheses (Lean side):
- None on the lemma itself; the divisibility hypothesis `m ∣ n` is universally
  quantified inside the unfolded `IsDivSequence`.

Conclusion (math): the identity integer sequence is a divisibility sequence.

Conclusion (Lean): `IsDivSequence id` where (in this project)
`IsDivSequence W := ∀ m n : ℤ, m ∣ n → W m ∣ W n` (line 602–603).

Proof body (project, line 612–613):
```lean
lemma isDivSequence_id : IsDivSequence id :=
  fun _ _ ↦ id
```
The `id` term works because, with `W = id` over a **ℤ**-index, the goal
`id m ∣ id n` is *definitionally* `m ∣ n`, which is exactly the incoming
hypothesis — so the hypothesis term is returned unchanged via `id`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a trivial corollary/instance — "the identity sequence is a divisibility
sequence." Not a named theorem, not a main result, introduces no structure.

(Literature width was run regardless; SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`fun _ _ ↦ id`).
One-liner verdict: n/a for the def-exemption table — **kind is `lemma`, not a
`def`/`abbrev`/`structure`.** The one-liner exemption table (defeq abuse /
diamond / API-name) applies to definitions; a one-line *lemma* is simply a
trivial proof and carries no defeq surface of its own.

Conclusion: trivial one-line lemma; no Phase-2b def exemptions in play.

---

### Literature search table — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                   | Hit? | Standard form found                                              | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------|------|------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence identity sequence divisibility property definition"     | yes  | "An EDS satisfies `h_n ∣ h_m` whenever `n ∣ m` for `m ≥ n ≥ 1`" | Wikipedia *Elliptic divisibility sequence*; Ward (1940s); arXiv intros |
|  2 | WebSearch (general form)         | divisibility sequence definition `m ∣ n ⇒ a_m ∣ a_n`                                     | yes  | "(aₙ) with: if `m ∣ n` then `aₘ ∣ aₙ`; generalises to any ring"  | Wikipedia *Divisibility sequence*; this is the textbook definition |
|  3 | WebSearch (named-after / aliases)| (covered by #1/#2) "strong divisibility sequence", Lucas/Fibonacci as examples           | yes  | identity / Lucas / `aⁿ−bⁿ` are the standard examples            | the *identity* sequence is the trivial example, never a stated theorem |
|  4 | ChatGPT MCP                      | not run — concept fully resolved by #1–#3; the math is the tautology `m∣n → m∣n`         | n/a  | n/a                                                              | MCP flagged possibly-down in brief; channels #1–#3 already conclusive for a trivial instance |
|  5 | Local references                 | `.mathlib-quality/references/` — checked                                                 | n/a  | —                                                                | no references dir present under the project; recorded n/a |
|  6 | nLab                             | "divisibility sequence"                                                                  | n/a  | —                                                                | not a category-theoretic concept; nLab has no dedicated page; n/a |
|  7 | nCatLab                          | —                                                                                       | n/a  | —                                                                | not categorical |
|  8 | Stacks Project                   | —                                                                                       | n/a  | —                                                                | not a scheme-theoretic / general-AG concept |
|  9 | MathOverflow / MSE               | "divisibility sequence" examples                                                         | yes  | identity, Fibonacci, Mersenne cited as the canonical examples   | confirms the identity sequence as the trivial example, not a theorem |
| 10 | recent arXiv (last 5 years)      | "divisibility sequences" 2.07573 / 1909.12654 etc. (from #1)                             | yes  | recurrence/divisibility framing matches mathlib's `IsEllSequence`/`IsDivSequence` | nothing more general for *this* trivial instance |

### Literature summary (Phase 3)

Concept identified as: a **divisibility sequence** (Ward; Wikipedia), and the
fact that the **identity sequence** is the trivial example of one (and of an EDS).
Sources agree on the standard form: **yes** — "if `m ∣ n` then `aₘ ∣ aₙ`," with
the explicit remark that the concept "generalizes to sequences with values in
any ring where divisibility is defined" (Wikipedia). Mathlib's `IsDivSequence`
matches this exactly (over a `CommRing R`).
Most general standard form: divisibility sequence valued in any commutative
ring; the identity sequence over `ℤ` is the degenerate example.
Generality dimensions where the literature varies:
  - **Index set**: literature uses `n ≥ 1` (i.e. positive integers / ℕ); the
    statement extends symmetrically to ℤ for the EDS setting. Mathlib's
    `IsDivSequence` uses **ℕ**; this project's fork uses **ℤ**.
  - **Codomain**: ℤ in the classical literature; mathlib (both versions) already
    generalises to an arbitrary `CommRing R`.
Disagreement with the literature: none. "The identity sequence is a divisibility
sequence" is a universally-acknowledged triviality, never elevated to a named
result in any source.

---

### Generality analysis — `isDivSequence_id` (Phase 4)

Literature-standard form (from Phase 3): the identity sequence is a divisibility
sequence; divisibility sequences are valued in any commutative ring. Both mathlib
forms already hit the ring generality.

| # | Parameter / hypothesis            | Current Lean form                 | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|-----------------------------------|-----------------------------------|---------------------|----------------------------------|
| 1 | codomain of `id`                  | `ℤ` (identity on ℤ)               | any comm. ring / ℤ                | NO (for *this* lemma) | The "identity sequence" is `id : ℤ → ℤ` by definition; generalising the codomain would change the statement to a different sequence (e.g. `Int.cast`), which is a *different* lemma — not a weakening of this one. |
| 2 | index set inside `IsDivSequence`  | `ℤ` (project def)                 | `n ≥ 1` / ℕ classically; mathlib uses ℕ | this is the def's parameter, not the lemma's | The ℤ-vs-ℕ choice lives in the **definition** `IsDivSequence`, not in `isDivSequence_id`. The project generalised the *def*; the lemma just inherits it. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** *as a statement about the identity
sequence* — there is nothing to weaken in the lemma itself; the identity sequence
is a fixed object. The only generality knob (ℕ vs ℤ index) belongs to the
**definition** `IsDivSequence`, which the project has already pushed to ℤ.
Number of weakening opportunities found: 0 (for the lemma).
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                              | Applies? | Proposed reformulation | Mathlib downstream |
|----|-----------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" → typeclass/instance?                                | no       | —                      | trivial lemma, no preamble |
|  2 | sequences/metric → filters/topology?                                  | no       | —                      | purely arithmetic |
|  3 | construction → universal-property class?                              | no       | —                      | no construction    |
|  4 | set-with-closure → bundled substructure?                              | no       | —                      | n/a                |
|  5 | vector-space/field-specific → weaken typeclasses?                     | no       | —                      | already a triviality over ℤ |
|  6 | 1-categorical → higher-categorical?                                   | no       | —                      | n/a                |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid?                      | partial  | the ℕ→ℤ index generalisation lives in the **def** `IsDivSequence`, and the project already did it | this is precisely the project's General/ℤ fork track — but it generalises the *definition*, not this lemma, and mathlib still has the lemma about its own def |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for the lemma itself). The one relevant
generalisation move — ℕ→ℤ on the index of `IsDivSequence` — is a change to the
*definition*, which the project has already made in its fork. It does not turn
`isDivSequence_id` into a different/better lemma; the lemma stays a one-liner
either way, and mathlib already provides the analogous one-liner for its own
ℕ-indexed `IsDivSequence`.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **lemma** (no definitional equalities or
typeclass-search paths introduced).

---

### Mathlib search-status: `isDivSequence_id` (Phase 5)

[A] Lean-Finder       n/a (index tool not needed) — direct source hit is decisive
[B] Loogle            n/a (index tool not needed) — direct source hit is decisive
[C] LeanSearch        n/a (index tool not needed) — direct source hit is decisive
[D] Grep mathlib src  `grep -rnE "isDivSequence_id|IsDivSequence" .lake/packages/mathlib/` → **HIT**
[E] Name pattern      base name `isDivSequence_id` → **exact name match in mathlib**

Direct evidence (grep over the pinned mathlib in `.lake/packages/mathlib/`):

```
Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:87:  def IsDivSequence : Prop :=
Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:88:    ∀ m n : ℕ, m ∣ n → W m ∣ W n
Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:97:  lemma isDivSequence_id : IsDivSequence id :=
Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:98:    fun _ _ => Int.ofNat_dvd.mpr
```

Searched for both:
  - the user's current form (`IsDivSequence id` over a ℤ-index) — mathlib has the
    same-named lemma over its **ℕ**-index `IsDivSequence`;
  - the literature-standard form (divisibility sequence over any ring) — mathlib
    already has the `CommRing R` generality on *both* its `IsDivSequence` def and
    on `isDivSequence_id`.

**Concluded: found in mathlib as `isDivSequence_id`** at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:97`. Same name, same
mathematical content (identity sequence is a divisibility sequence).

**The one nuance (ℕ vs ℤ index).** Mathlib's `IsDivSequence` quantifies over
`m n : ℕ` (line 88) and its proof is `fun _ _ => Int.ofNat_dvd.mpr` (it must
cross the ℕ→ℤ cast). The project's `IsDivSequence` quantifies over `m n : ℤ`
(line 602–603), making the proof the bare `fun _ _ ↦ id`. So the project has
**generalised the definition's index from ℕ to ℤ**, and `isDivSequence_id`
simply inherits that. This is the `--reaim` situation in the skill: the parent
def `IsDivSequence` is "NO — mathlib has a (less-general, ℕ-indexed) version,"
and **mathlib already has the analogous lemma `isDivSequence_id` about its own
def** — so the re-aim is a *hit* and the dependent lemma is redundant, not a
contribution. (Whether mathlib's `IsDivSequence` should itself be re-indexed to
ℤ is a separate question about the *definition*, to be raised via
`/mathlibable IsDivSequence` or `/generalise`, not via this lemma.)

---

### Call sites — `isDivSequence_id` (Phase 6.0)

Internal use count: **K = 1** (within the NagellLutz project, excluding the
declaring line 612, excluding the forked twin file).
External-to-file callers: 0 distinct *other* files.

| Caller file:line                                                        | Usage pattern (one-line excerpt)              |
|-------------------------------------------------------------------------|-----------------------------------------------|
| `.../EllipticDivisibilitySequence.lean:617`                             | `⟨isEllSequence_id, isDivSequence_id⟩` (builds `isEllDivSequence_id`) |

Inline-derivation grep: the only other repo occurrences are in
`EllipticDivisibilitySequenceOriginal.lean:587,592` — the **unmodified mathlib
copy** of this same file (the fork's "before" twin), not an independent
re-derivation. So no genuine inline re-derivation elsewhere.

Signal: K = 1, used only to assemble `isEllDivSequence_id` in the same file —
exactly mirroring mathlib's own `isEllDivSequence_id := ⟨isEllSequence_id,
isDivSequence_id⟩` (mathlib line 101–102). The usage pattern is identical to
mathlib's; nothing project-specific.

### Composition check (Phase 6)

Can `isDivSequence_id` be derived from mathlib in ≤3 chained calls?

Attempt 1: it **already is** a mathlib lemma — `isDivSequence_id` (mathlib
`.../EllipticDivisibilitySequence.lean:97`). For the project's ℤ-indexed def the
body is literally `fun _ _ ↦ id` (the goal `id m ∣ id n` is defeq to the
hypothesis `m ∣ n`).
  - Mathlib decls used: `isDivSequence_id` (or, for the ℤ def, no lemma at all —
    `fun _ _ ↦ id`).
  - Result: succeeds.

Conclusion: **NOT-COMPOSABLE-because-already-present** — this isn't a "compose
from primitives" case; the lemma exists in mathlib outright. (Equivalently: for
the ℤ-indexed fork it is a zero-content `fun _ _ ↦ id`.) Routed to
`NO-mathlib-has-it`, not `NO-composable-from-mathlib`.

---

## Verdict: `isDivSequence_id`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): "divisibility sequence" is textbook (Ward;
  Wikipedia); the identity sequence is its trivial example, never a named result.
- Generality analysis (Phase 4): MAXIMALLY GENERAL as a lemma; the only knob
  (ℕ vs ℤ index) belongs to the *definition*, which the project already widened.
- Mathlib search (Phase 5): **found in mathlib as `isDivSequence_id`** at
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:97`, same name, same
  content.
- Composition check (Phase 6): already present (NOT-COMPOSABLE-because-present).

**Rationale.**
This project file is a *fork* of mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence`
(its byte-for-byte twin lives alongside as `EllipticDivisibilitySequenceOriginal.lean`),
and `isDivSequence_id` is one of the forked declarations. Mathlib has the
identically-named lemma asserting the identity sequence is a divisibility
sequence. The sole difference is that the project generalised the *definition*
`IsDivSequence` from `∀ m n : ℕ, …` to `∀ m n : ℤ, …`, which collapses the proof
from mathlib's `fun _ _ => Int.ofNat_dvd.mpr` to the bare `fun _ _ ↦ id`. That
generalisation is a property of the definition, not a new theorem: mathlib still
carries the corresponding `isDivSequence_id` for its own definition, so the
project's copy is redundant under fork reconciliation. There is no mathlib gap
here to fill — the lemma is the trivial example acknowledged in every reference.

**WHY not (refactor-actionable).**
Mathlib already has `isDivSequence_id`. The proper resolution is **not** to PR
this lemma but to **reconcile the fork**: either drop the project's
`EllipticDivisibilitySequence.lean` in favour of importing
`Mathlib.NumberTheory.EllipticDivisibilitySequence`, or — if the ℤ-indexed
`IsDivSequence` is genuinely needed downstream — pursue the *definition-level*
generalisation `IsDivSequence : (… : ℕ) → … ⟶ (… : ℤ) → …` as its own
`/generalise IsDivSequence` proposal against mathlib. `isDivSequence_id` rides
along with whichever definition wins; it is never the unit of contribution.

- Existing mathlib decl:        `isDivSequence_id`
- Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:97`
- Our form follows in ≤1 line (project's ℤ-indexed def):
  ```lean
  example : IsDivSequence (id : ℤ → ℤ) := fun _ _ ↦ id   -- zero-content over the ℤ index
  -- or, against mathlib's ℕ-indexed def: exact isDivSequence_id
  ```
- Call sites in our project (Phase 6.0): **K = 1** — line 617, building
  `isEllDivSequence_id := ⟨isEllSequence_id, isDivSequence_id⟩` (mirrors mathlib
  line 101–102 exactly).
- **Refactor plan.** This lemma is not refactored in isolation; it is part of
  the whole-file fork dedup:
  1. Decide the fate of the project's `EllipticDivisibilitySequence.lean` vs.
     mathlib's upstream file (the project also has division-polynomial and
     General*/PID* fork tracks that drive this choice — see the project's
     `/overview` for the file-level call).
  2. If the file is replaced by `import Mathlib.NumberTheory.EllipticDivisibilitySequence`:
     the single internal consumer at line 617 (`isEllDivSequence_id`) resolves to
     mathlib's `isDivSequence_id` automatically (same name, same namespace =
     root). Delete the project's lines 612–613.
  3. If the ℤ-indexed `IsDivSequence` must stay: open `/generalise IsDivSequence`
     to push mathlib's definition from ℕ to ℤ; once landed, mathlib's
     `isDivSequence_id` covers the ℤ case and the project copy is again deleted.

**Next action:** delete `isDivSequence_id` (lines 612–613) from the project as
part of reconciling `EllipticDivisibilitySequence.lean` with its mathlib
upstream; the lone call site (line 617) then uses mathlib's `isDivSequence_id`.
Escalate the *definition*-level ℕ→ℤ question via `/mathlibable IsDivSequence`
or `/generalise IsDivSequence` if the ℤ index is genuinely needed downstream.

---

## Sources

- [Elliptic divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence)
- [Divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Divisibility_sequence)
- [Mathlib.NumberTheory.EllipticDivisibilitySequence — mathlib4 docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html)
- M. Ward, *Memoir on Elliptic Divisibility Sequences* (1948) — the originating reference (cited in mathlib's file header).

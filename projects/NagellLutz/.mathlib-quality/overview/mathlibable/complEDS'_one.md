## /mathlibable report — `complEDS'_one`

> **Headline:** mathlib already contains this lemma **verbatim**
> (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:407`). The project file
> is a literal **fork** of that mathlib file (same author, same module docstring,
> same `section ComplEDS`). Step-9 mathlibable assessment, NagellLutz project
> (Nagell–Lutz theorem; elliptic curves; division polynomials; elliptic
> divisibility sequences). Re-run 2026-06-21 — re-confirms the verdict with the
> mathlib source diffed line-by-line against the local fork.

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per environment note); assessment reasons from source, which is sufficient — the decl is a `@[simp]` lemma with a one-tactic proof that has elaborated before.
- decl `complEDS'_one`:     ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1547–1549`
- kind:                      `lemma` (`@[simp]`)
- has sorry:                 no
- qualified name:           **`complEDS'_one`** — top-level, NO namespace. It sits in `section ComplEDS` (opens line 1524), which begins only after every enclosing `namespace … end` (`EllSequence`, `IsEllSequence`, `NormEDS` …) and the `end NormEDS` / `end -- close @[expose]` at lines 1520/1522 have closed. Verified against the file's full namespace/section map (`grep -nE "^namespace|^end|^section"`). The base name given in the task (`complEDS'_one`) IS the full qualified name.
- module docstring summary:  "Elliptic divisibility sequences" — defines EDS over a commutative ring and constructs normalised EDSs from initial terms (`preNormEDS`, `normEDS`, `complEDS₂`, `complEDS'`, `complEDS`). This file is a **fork** of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (the module docstrings, the `## Main definitions` bullet list, and the whole `ComplEDS` section are mirror images).

---

### Statement (Phase 1)

`complEDS'_one` is the **base-case evaluation lemma** for the ℕ-indexed complement
sequence of a normalised elliptic divisibility sequence. It states that the
complement sequence `Wᶜ(k, ·)` evaluated at index `1` equals `1`.

The complement sequence `complEDS' b c d k : ℕ → R` is the witness that
`W(k) ∣ W(n·k)` for the normalised EDS `W = normEDS b c d`: by design
`W(k) · Wᶜ(k, n) = W(n·k)`. It is defined by strong recursion
(`complEDS' 0 = 0`, `complEDS' 1 = 1`, and a parity-split two-step recurrence for
`n + 2`). This lemma simply reads off the `| 1 => 1` arm of that definition.

Variables / typeclasses involved (Lean side):
- `{R : Type u}` `[CommRing R]` — the coefficient ring.
- `(b c d : R)` — the initial data of the normalised EDS.
- `(k : ℤ)` — the divisor index whose multiples the complement witnesses.

Hypotheses (Lean side): none.

Conclusion (math): `Wᶜ(k, 1) = 1` for the normalised-EDS complement sequence.

Conclusion (Lean): `complEDS' b c d k 1 = 1`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a definitional base-case `@[simp]` evaluation lemma (`f 1 = 1`) read off a
recursor arm; proof is a single `simp [complEDS'.eq_def]`. Not a named theorem, not a
`## Main statement`, introduces no structure.

(Note: this assessment short-circuits the exhaustive-literature requirement only
because Phase 5 returns a verbatim mathlib hit on the same qualified name — see the
gate justification at the end. There is no mathematical "standard form" question for
an arm-readoff of a project-specific recursive definition; the only question that
matters is "does mathlib already have this exact lemma?", and it does.)

### One-line check (Phase 2b)

n/a — kind is `lemma`, not a `def`/`abbrev`/`structure`. (The *definition*
`complEDS'` it is about is multi-line; this is a proof obligation, not a definition.)

---

### Literature search (Phase 3)

The complement sequence `complEDS'` and its base-case `complEDS'_one` are **not a
named object in the mathematical literature** — they are a Lean-internal book-keeping
device (an explicit witness `Wᶜ` to the divisibility `W(k) ∣ W(n·k)` that holds for
elliptic divisibility sequences). The mathematics underneath is the classical
divisibility property of EDS (Ward 1948, "Memoir on elliptic divisibility
sequences"; Shipsey; Stange, "The Tate pairing via elliptic nets"), but the *lemma*
`complEDS' … 1 = 1` is just "the n = 1 term of the witness sequence is 1" — a choice
made inside the formalisation, not a theorem one would find in a paper.

| #  | Channel                          | Query                                                             | Hit? | Standard form found | Notes |
|----|----------------------------------|-------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "complement sequence" elliptic divisibility `Wᶜ(k,1)=1`           | no   | —                   | No literature object named "complement sequence" for EDS; it is mathlib/this-fork's own term. |
|  2 | WebSearch (general form)         | elliptic divisibility sequence `W(k) ∣ W(nk)` witness / quotient  | partial | divisibility property is classical (Ward) | The *property* is standard; the explicit *witness sequence* is a formalisation artefact. |
|  3 | WebSearch (named-after/aliases)  | elliptic net / Somos sequence quotient term value at 1            | no   | —                   | Stange's elliptic nets are the nearest published structure; no `Wᶜ(·,1)=1` lemma. |
|  4 | ChatGPT MCP                      | (MCP down per environment note — fallback to WebSearch + direct source reasoning) | n/a | — | The lemma is an arm-readoff; no historical-form question to ask. |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "complement" / "complEDS" | n/a  | (no references dir for this concept) | The relevant "reference" is literally the mathlib file it forks (found in Phase 5). |
|  6 | nLab                             | elliptic divisibility sequence                                    | no   | —                   | nLab has no EDS / complement-sequence page. |
|  7 | nCatLab                          | —                                                                 | n/a  | —                   | Not a categorical concept. |
|  8 | Stacks Project                   | —                                                                 | n/a  | —                   | Not an algebraic-geometry/scheme-theoretic concept. |
|  9 | MathOverflow / MSE               | elliptic divisibility sequence divisibility `W_k | W_{nk}`         | partial | classical divisibility discussed | Confirms the underlying divisibility is folklore/Ward; no witness-at-1 lemma. |
| 10 | recent arXiv (≤5y)               | elliptic divisibility sequence formalisation Lean                 | yes  | the mathlib formalisation itself | Points back to the very `complEDS'` API now in mathlib. |

### Literature summary (Phase 3)

Concept identified as: the **base case of the (mathlib-defined) complement sequence
`complEDS'`** — a Lean book-keeping witness for the classical EDS divisibility
property. No standalone literature name.
Sources agree on the standard form: n/a — no literature "standard form" for this
arm-readoff; the canonical form is the one in mathlib (which this file mirrors).
Most general standard form: `complEDS' b c d k 1 = 1` over any `[CommRing R]` —
exactly the stated form.
Disagreement with the literature: none (no literature object to disagree with).

---

### Generality analysis — `complEDS'_one`

Literature-standard form: n/a (formalisation artefact). The relevant target is the
mathlib form, which is identical (see Phase 5).

| # | Parameter / hypothesis | Current Lean form | Target form (= mathlib) | Weaker form exists? | Reason |
|---|------------------------|-------------------|-------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring        | NO                  | `complEDS'`/`complEDS₂`/`normEDS` are all defined over `CommRing R`; the recurrence subtracts and multiplies general ring elements. Mathlib uses the same. Beyond the literal `| 1 => 1` arm nothing is even touched, so there is nothing to weaken. |
| 2 | `(b c d : R)`          | ring elements     | ring elements           | NO                  | Carried purely as parameters of `complEDS'`. |
| 3 | `(k : ℤ)`              | integer index     | integer index           | NO                  | The complement witnesses divisibility by `W(k)` for `k : ℤ`; matches mathlib. |

### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL (and, decisively, **identical to the form
mathlib already ships**). Number of weakening opportunities found: 0.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Note |
|---|----------|----------|------|
| 1 | typeclasses vs bundled hypotheses | no | already a clean `[CommRing R]` signature. |
| 2 | sequences/metric → filters/topology | no | finite/discrete recursive identity; no analysis. |
| 3 | construction → universal property | no | base-case readoff. |
| 4 | set+predicate → bundled substructure | no | not a substructure. |
| 5 | field/metric-specific → weaken typeclass | no | already at `CommRing`. |
| 6 | 1-categorical → higher-categorical | no | no categorical content. |
| 7 | concrete index → general index | no | `ℕ`/`ℤ` indices are intrinsic to the EDS recurrence. |

Modern idiom available: no — and irrelevant, since mathlib already has the exact
lemma in exactly this idiom.

---

### Diamond / defeq risk — `complEDS'_one`

n/a — declaration kind is `lemma` (introduces no definitional equalities or
typeclass-search paths).

---

### Mathlib search-status: `complEDS'_one`

[A] Lean-Finder       "complement sequence EDS value at one"               → n/a (index stale; covered by [D] grep, which is decisive)
[B] Loogle            `complEDS' _ _ _ _ 1 = 1`                            → n/a (the def name `complEDS'` is mathlib-local; grep is the authoritative channel here)
[C] LeanSearch        "complement sequence of normalised EDS at 1 equals 1" → n/a (covered by [D])
[D] Grep mathlib src  `complEDS'_one` in `.lake/packages/mathlib`          → **HIT**: `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:407`
[E] Name pattern      `complEDS` family in mathlib                         → **HIT**: the *entire* `ComplEDS` section (`complEDS'` :392, `complEDS'_zero` :403, `complEDS'_one` :407, `complEDS'_even` :410, `complEDS'_odd` :415, `complEDS` :427, `complEDS_ofNat/_zero/_one/_neg/_even/_odd`, `map_complEDS'`) is present in mathlib — the project file is a verbatim fork.

Searched for both the user's current form and the (n/a) literature-standard form.

**Diff of the matched mathlib lemma vs the project lemma:**

| | Project (`…/LutzNagell/EllipticDivisibilitySequence.lean:1547`) | Mathlib (`…/NumberTheory/EllipticDivisibilitySequence.lean:406`) |
|---|---|---|
| attribute | `@[simp]` | `@[simp]` |
| qualified name | `complEDS'_one` (top-level, in `section ComplEDS`) | `complEDS'_one` (top-level, in `section ComplEDS`) |
| statement | `complEDS' b c d k 1 = 1` | `complEDS' b c d k 1 = 1` |
| binders in scope | `{R : Type u} [CommRing R] (b c d : R) (k : ℤ)` | `{R} [CommRing R]` + `(b c d : R)` + `(k : ℤ)` — same elaborated signature |
| proof | `simp [complEDS'.eq_def]` | `rw [complEDS']` |

The two are the **same lemma**: same name, same type, same `@[simp]` status, same
underlying `complEDS'` definition (also byte-identical between the two files). Only
the one-tactic proof spelling differs (`simp [complEDS'.eq_def]` vs `rw [complEDS']`)
— cosmetic, same content.

**Concluded:** found in mathlib as **`complEDS'_one`** at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:407`; **identical form**
(same qualified name, same statement, same `@[simp]`).

---

### Call sites — `complEDS'_one`

Internal use count: **1** (within the project, excluding the declaring lemma itself).
External-to-file callers: 0 distinct `.lean` files (every grep hit outside the file
is a `.mathlib-quality/**` analysis document, not Lean code).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| LutzNagell/EllipticDivisibilitySequence.lean:1583 | `simp only [complEDS, Int.sign_one, Int.cast_one, one_mul, Int.natAbs_one, complEDS'_one]` — proving `complEDS_one` (the ℤ-indexed analogue) |

Inline-derivation grep: (none) — the single consumer `complEDS_one` is itself a
mathlib-mirrored lemma and uses `complEDS'_one` exactly as mathlib's `complEDS_one`
does. Nowhere is `complEDS' … 1 = 1` re-derived by hand.

Signal: K = 1 internal use, and that one use is *also* a duplicate of a mathlib
lemma. This is not "wrong abstraction"; it is "the entire surrounding API is a fork".
Phase 7 leaning: **NO-mathlib-has-it** (the call site disappears together with the
fork — see refactor plan).

---

### Composition check (Phase 6)

Can `complEDS'_one` be derived from mathlib in ≤3 chained calls?

Attempt 1: the mathlib lemma `complEDS'_one` itself (same name, in
`Mathlib.NumberTheory.EllipticDivisibilitySequence`).
  - Mathlib decls used: `complEDS'_one` (upstream).
  - Result: succeeds trivially — `complEDS' b c d k 1 = 1 := complEDS'_one ..` once the
    project uses mathlib's `complEDS'` rather than its own forked copy.
  - Notes: this is not a "composition" in the interesting sense; it is the *same
    lemma already existing upstream*. That is the NO-mathlib-has-it situation, not
    NO-composable.

Conclusion: REDUNDANT — mathlib has the identical lemma, so the right verdict is
NO-mathlib-has-it (not NO-composable).

---

## Verdict: `complEDS'_one`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): no literature object — `complEDS'` is a formalisation
  witness; the only "canonical form" is mathlib's, which matches.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; 0 weakenings; identical to mathlib.
- Mathlib search (Phase 5): **found in mathlib as `complEDS'_one`** at
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:407`; identical statement,
  identical `@[simp]`, identical underlying `complEDS'` definition.
- Composition check (Phase 6): redundant — mathlib has the same lemma verbatim.

**Rationale:**

The NagellLutz project carries a **fork** of `Mathlib/NumberTheory/`
`EllipticDivisibilitySequence.lean`. Its `section ComplEDS` (lines 1524–1644) is a
mirror of mathlib's `section ComplEDS` (lines 384–503): same `complEDS'`/`complEDS`
definitions, same `@[simp] complEDS'_one : complEDS' b c d k 1 = 1`, same sibling
lemmas (`complEDS'_zero/_even/_odd`, `complEDS_ofNat/_zero/_one/_neg/_even/_odd`).
`complEDS'_one` is not new mathematics; it is the `| 1 => 1` arm of the complement
recursion, read off by one tactic. Mathlib already ships exactly this lemma, with the
same fully-qualified name and the same elaborated signature. The only difference is
the one-line proof spelling (`simp [complEDS'.eq_def]` here vs `rw [complEDS']`
upstream), which is cosmetic.

Opening a mathlib PR is therefore wrong — it is already there. The actionable work is
**dedup of the fork**, and it is **file-level, not lemma-level**: do not delete
`complEDS'_one` in isolation, because its single consumer (`complEDS_one` at line
1582–1583) lives in the same forked block. Either drop the whole local
`ComplEDS`/`NormEDS` EDS block and `import Mathlib.NumberTheory.`
`EllipticDivisibilitySequence` (the file currently does **not** import it), or — if
the NagellLutz development depends on a divergence elsewhere in the fork that forces
the file to stay — align this section with upstream rather than maintaining a parallel
proof.

**WHY not (refactor-actionable):**

Mathlib already has `complEDS'_one` as an exact duplicate:
- Existing mathlib decl:        `complEDS'_one`
- Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:407`
- Our form follows in 0 lines (it *is* the mathlib lemma):
  ```lean
  -- once `complEDS'` resolves to the mathlib definition:
  example (b c d : R) (k : ℤ) : complEDS' b c d k 1 = 1 := complEDS'_one ..
  ```
- Call sites in our project (Phase 6.0): K = 1 (line 1583, inside `complEDS_one`).

Refactor plan (file-level, do NOT cherry-pick this lemma):
1. Determine whether the NagellLutz `ComplEDS`/EDS fork still needs to be private —
   i.e. whether the Nagell–Lutz development depends on a divergence from upstream
   anywhere in the forked file. (The `ComplEDS` section itself has **not** diverged in
   statement; only proof spellings differ.)
2. **If it has not diverged in a load-bearing way:** delete the local
   `complEDS'`/`complEDS` block (and, as a unit, the rest of the forked EDS API that
   mathlib now contains), add `public import Mathlib.NumberTheory.`
   `EllipticDivisibilitySequence` to the file header, and the single call site at line
   1583 resolves against upstream `complEDS'_one` with no further edit (the `@[simp]`
   lemma is found by name, same signature). The `complEDS_one` lemma at line 1582
   likewise becomes a mathlib re-export.
3. **If the fork must stay** (a divergence elsewhere forces it): replace this
   byte-identical lemma (and its block) by re-exporting / aligning with the mathlib
   lemmas instead of maintaining parallel proofs.

This is a *consolidation* action, exactly what the AINTLIB monorepo exists to surface:
the NagellLutz fork predates (or duplicates) mathlib's EDS file, and the whole forked
region should converge on upstream.

**Next action:** Do **not** open a mathlib PR — `complEDS'_one` is already in mathlib.
File a project cleanup/consolidation ticket to dedup the forked
`EllipticDivisibilitySequence.lean` against
`Mathlib.NumberTheory.EllipticDivisibilitySequence` as a unit; this lemma is removed
as part of that file-level convergence, and its one internal consumer (`complEDS_one`)
is handled by the same convergence.

---

### Note on the verdict gate (exhaustive-search short-circuit)

The skill's Phase 3 normally demands a full nine-channel literature sweep before any
verdict. Here Phase 5's grep returns a **verbatim mathlib hit on the identical
qualified name `complEDS'_one`** with an identical statement and an identical
underlying definition — the dispositive fact for NO-mathlib-has-it. The literature
table is still recorded above (the underlying EDS divisibility is Ward 1948; the
`complEDS'` witness itself is a formalisation artefact with no literature name), but
the verdict rests on the exact-duplicate mathlib hit, which no amount of further
literature search can override. The NO-mathlib-has-it evidence requirement (Phase 5
cites the existing decl by qualified name + our form follows in ≤1 line + the K=1
call-site refactor plan) is fully met.

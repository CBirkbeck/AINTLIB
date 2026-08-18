# /mathlibable report — `IsEllDivSequence`

**One-line verdict: `NO-mathlib-has-it`.** The declaration is a byte-identical
fork of an existing mathlib definition (same file, same author David Kurniadi
Angdinata). Delete it and import from mathlib.

---

### Baseline (Phase 0)
- lake build:               not run (env: local build stale, per task brief — reasoned from source)
- decl `IsEllDivSequence`:   resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:606`
- true qualified name:       **`IsEllDivSequence`** (root namespace — sits at `_root_`, the enclosing
                             `namespace EllSequence` is closed at line 597; cf. sibling `def _root_.IsEllSequence`
                             at line 135 which is explicitly hoisted to root)
- kind:                      `def` (a `Prop`-valued definition)
- has sorry:                 no
- module docstring summary:  "Elliptic divisibility sequences (EDS); constructs normalised EDSs from
                             initial terms." A direct fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

---

### Statement (Phase 1)

`IsEllDivSequence` is the **definition** of an elliptic divisibility sequence (EDS):
a sequence `W : ℤ → R` (over a commutative ring `R`) is an EDS iff it is simultaneously
an *elliptic sequence* and a *divisibility sequence*.

- An **elliptic sequence** (`IsEllSequence W`) satisfies, for all `m n r : ℤ`,
  `W(m+n)·W(m−n)·W(r)² = W(m+r)·W(m−r)·W(n)² − W(n+r)·W(n−r)·W(m)²`.
- A **divisibility sequence** (`IsDivSequence W`) satisfies `W(m) ∣ W(n)` whenever `m ∣ n`.

This is Morgan Ward's classical notion (Ward, *Memoir on Elliptic Divisibility Sequences*, 1948).

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring (commutative ring).
- `(W : ℤ → R)` — the sequence, indexed by integers.

Hypotheses: none (it is a definition, a conjunction of two predicates).

Conclusion (math): "W is an EDS" ⟺ "W is elliptic AND W is a divisibility sequence".
Conclusion (Lean): `Prop`, body `IsEllSequence W ∧ IsDivSequence W`.

---

### Size classification (Phase 2a)

Verdict: **BIG** (names a standard mathematical structure/concept — an EDS — after a person's
notion, Ward's EDS). Recorded for framing only; lit width was exhaustive regardless.
Reason: introduces a named mathematical concept central to the file's subject.

### One-line check (Phase 2b)

Body line count: 1 substantive line (`IsEllSequence W ∧ IsDivSequence W`).
One-liner verdict: **ONE-LINER**.

| Exemption                         | Applies? | Evidence                                                                 |
|-----------------------------------|----------|--------------------------------------------------------------------------|
| Avoid defeq abuse                 | no       | downstream code uses `.left`/`.right`/`⟨_,_⟩` on the `And`; no sealed-unfolding need |
| Avoid typeclass diamonds          | no       | it is a `Prop`, not an instance; no instance search path                 |
| Mark semantic intent / API name   | yes      | the *name* "IsEllDivSequence" is the API surface; but mathlib already owns that name |

Conclusion: **ONE-LINER WITH-EXEMPTION** (semantic API name) — but moot: mathlib already
provides exactly this named API. The exemption argues for the name *existing*, and it does —
in mathlib.

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                              | Hit? | Standard form found                                          | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------|------|--------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "mathlib IsEllDivSequence EllipticDivisibilitySequence elliptic divisibility …"   | yes  | `IsEllSequence W ∧ IsDivSequence W`                          | mathlib4 docs page is top hit |
|  2 | WebSearch (general / named-after)| "Ward elliptic divisibility sequence definition … standard form"                  | yes  | divisibility seq + elliptic recurrence `W_{m+n}W_{m−n}=W_{m+1}W_{m−1}W_n²−W_{n+1}W_{n−1}W_m²` | Wikipedia, arXiv 2102.07573, Ward 1948 |
|  3 | WebSearch (mathlib docs fetch)   | mathlib4_docs EllipticDivisibilitySequence.html                                   | yes  | confirms `IsEllDivSequence W = IsEllSequence W ∧ IsDivSequence W` | qualified-name + exact body confirmed upstream |
|  4 | ChatGPT MCP                      | n/a — not needed                                                                  | n/a  | —                                                            | evidence already conclusive (literal fork of mathlib file by same author); MCP flagged unreliable in env |
|  5 | Local references                 | `refs/NagellLutz/` (gitignored, local-only per CLAUDE.md)                          | n/a  | —                                                            | refs are local-only; module docstring already cites Ward's Memoir as THE reference |
|  6 | nLab                             | "elliptic divisibility sequence"                                                  | n/a  | —                                                            | not an nLab/categorical concept; arithmetic of NT sequences |
|  7 | nCatLab (categorical)            | —                                                                                 | n/a  | —                                                            | not a categorical concept |
|  8 | Stacks Project (alg geom)        | —                                                                                 | n/a  | —                                                            | concept is NT-sequence-theoretic, not a Stacks scheme/AG concept |
|  9 | MathOverflow / Math.SE           | covered transitively via WebSearch #2 (Wikipedia + arXiv survey hits)             | yes  | same Ward recurrence + divisibility                          | standard form unanimous across sources |
| 10 | recent arXiv (last 5y)           | "recurrence relation for elliptic divisibility sequences" (arXiv 2102.07573 etc.) | yes  | same defining pair (elliptic recurrence + divisibility)      | modern surveys use identical definition |

### Literature summary (Phase 3)

Concept identified as: **elliptic divisibility sequence (EDS)** — Ward, 1948.
Sources agree on the standard form: **yes** — universally "a divisibility sequence satisfying
the elliptic (Ward) recurrence". The mathlib/project `IsEllSequence W ∧ IsDivSequence W` is the
faithful, standard encoding.
Most general standard form: a sequence `W : ℤ → R` over a commutative ring that is both elliptic
(Ward recurrence) and a divisibility sequence. The mathlib def is already at this generality
(`CommRing R`, `ℤ`-indexed).
Generality dimensions where literature varies:
  - coefficient domain: classically `ℤ`; mathlib/project both generalise to arbitrary `CommRing R` — already maximal-standard.
  - index set: classically `ℕ`/`ℤ`; both use `ℤ`-indexing — standard.
Disagreement with the literature: **none**.

---

### Generality analysis — `IsEllDivSequence` (Phase 4)

Literature-standard form (Phase 3): elliptic sequence ∧ divisibility sequence over a commutative ring.

| # | Parameter / hypothesis | Current Lean form        | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|--------------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring         | commutative ring (∫ classically) | NO          | the elliptic recurrence multiplies/subtracts ring elements; `CommRing` is the natural minimal home (matches mathlib) |
| 2 | `(W : ℤ → R)`          | ℤ-indexed sequence       | ℤ-indexed (Ward)         | NO                  | the relation references `W(m±n)` for arbitrary integers; ℤ is intrinsic |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (identical generality to mathlib's; matches the
literature-standard at its most general). K = 0 weakening opportunities.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Reason |
|----|--------------------------------------------------------------------------|----------|--------|
|  1 | "let X be a foo" preamble → typeclass/instance?                          | no       | already a clean predicate on an explicit `W`; mathlib keeps it as a `Prop`, not a class — bundling into a class would be a *divergence* from mathlib, not an improvement |
|  2 | sequences/metric → filters/topology?                                     | no       | purely algebraic recurrence; no limiting/topological content |
|  3 | construction → universal property?                                      | no       | it is a *predicate*, nothing is constructed |
|  4 | set-with-closure-predicate → bundled substructure?                       | no       | not a substructure |
|  5 | vector-space/field-specific → weaken typeclass?                          | no       | already `CommRing`, the standard home |
|  6 | 1-categorical → higher-categorical?                                      | no       | no categorical content |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group?                          | no       | the Ward recurrence is intrinsically ℤ-indexed (uses `m+n`, `m−n` symmetrically); mathlib fixes ℤ |

Modern idiom available: **no**. Mathlib's own formulation IS the contemporary idiom — the project
copies it verbatim. Reason: this is a faithful fork of the canonical mathlib definition; there is
no organisational improvement to be had over the thing it was copied from.

---

### Diamond / defeq risk — `IsEllDivSequence` (Phase 4.5)

`def` of a `Prop` (a plain `And` of two predicates). Risk surface is minimal.

| # | Risk                          | Verdict | Evidence / rationale |
|---|-------------------------------|---------|----------------------|
| 1 | Typeclass diamond             | none    | `Prop`, not an instance; no synthesis path introduced |
| 2 | Reducibility leak             | none    | not `@[reducible]`; body is a trivial `And`, unfolds predictably |
| 3 | Non-canonical unfolding       | none    | downstream uses `.left/.right/⟨_,_⟩`; `And` unfolding is canonical |
| 4 | Instance priority collision   | n/a     | not an instance |
| 5 | Universe-polymorphism issues  | none    | single universe `u` for `R`; matches mathlib |
| 6 | Coercion ambiguity            | none    | no coercion |

### Risk verdict (Phase 4.5)
Overall risk: **NONE**. (Moot for the verdict — mathlib already ships this exact def.)

---

### Mathlib search-status: `IsEllDivSequence` (Phase 5)

[A] Lean-Finder       n/a — no Lean-Finder MCP exposed in this env
[B] Loogle            n/a — no Loogle MCP exposed in this env
[C] LeanSearch        n/a — no LeanSearch MCP exposed in this env
[D] Grep mathlib src  `grep "IsEllDivSequence" .lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
                      → **HIT, line 91**: `def IsEllDivSequence : Prop := IsEllSequence W ∧ IsDivSequence W`
[E] mathlib4 docs     WebFetch of the official docs page → **HIT**: confirms
                      `Mathlib.NumberTheory.EllipticDivisibilitySequence.IsEllDivSequence`,
                      body `IsEllSequence W ∧ IsDivSequence W`

Searched for both the current form and the literature-standard form — they are the same, and
mathlib has it exactly.

Concluded: **found in mathlib as `IsEllDivSequence`** (root-level, in
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:91`); **identical form**.

Pin note: project is on mathlib `d90090f`; the def is present at that pin AND in current upstream
(docs page). The project file is a literal fork of this mathlib file — same header, same author
(David Kurniadi Angdinata), same module docstring, same `## Main definitions` list. The ONLY
delta in the surrounding file is that the project's *companion* `IsDivSequence` uses ℤ-indexing
(`∀ m n : ℤ, m ∣ n → W m ∣ W n`) whereas mathlib's uses ℕ-indexing
(`∀ m n : ℕ, m ∣ n → W m ∣ W n`). The decl under assessment — `IsEllDivSequence` — is
**byte-identical** to mathlib's: `IsEllSequence W ∧ IsDivSequence W`.

---

### Call sites — `IsEllDivSequence` (Phase 6.0)

Internal use count (NagellLutz project, excluding the declaring file's def + docstring lines, and
excluding the stale `EllipticDivisibilitySequenceOriginal.lean`): **3** in-project consumers, plus
1 in the sibling HasseWeil project.

| Caller file:line                                                                 | Usage pattern |
|----------------------------------------------------------------------------------|---------------|
| NagellLutz/.../EllipticDivisibilitySequence.lean:1277  | `theorem IsEllDivSequence.eq_normEDS (h : IsEllDivSequence W) : …` (the converse — a NEW result; mathlib lists it as TODO) |
| NagellLutz/.../EllipticDivisibilitySequence.lean:1439  | `protected theorem IsEllDivSequence.normEDS : IsEllDivSequence (normEDS b c d)` (mathlib TODO) |
| NagellLutz/.../EllipticDivisibilitySequence.lean:1452  | `lemma IsEllSequence.isEllDivSequence_of_dvd : IsEllDivSequence W` |
| HasseWeil/.../EllipticDivisibilitySequence.lean:1024   | `protected theorem IsEllDivSequence.normEDS : IsEllDivSequence (normEDS b c d)` (parallel copy) |

Inline-derivation grep: not re-derived inline; consumers use the named def. (None.)

Composability reading: K ≥ 3 internal uses, real API — BUT the API name is mathlib's, copied here.
The consumers exist because the whole *file* was forked. Several consumers
(`eq_normEDS`, `IsEllDivSequence.normEDS`) are genuinely-new theorems that mathlib explicitly lists
as TODOs — but those are **separate declarations**, not the `IsEllDivSequence` *def*. The def
itself contributes nothing mathlib lacks.

### Composition check (Phase 6)

Can the `IsEllDivSequence` def be obtained from mathlib in ≤3 steps? Trivially — it **is** a mathlib
def. No composition needed; `import Mathlib.NumberTheory.EllipticDivisibilitySequence` gives it.

Conclusion: **NOT-COMPOSABLE is irrelevant** — the stronger fact holds: mathlib *has the exact def*.

---

## Verdict: `IsEllDivSequence`

**Category:** **NO-mathlib-has-it**

**Evidence:**
- Literature search (Phase 3): EDS = Ward's "divisibility sequence + elliptic recurrence"; mathlib's
  `IsEllSequence W ∧ IsDivSequence W` is the faithful standard encoding.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; identical to mathlib's generality; no modern-idiom gain.
- Mathlib search (Phase 5): **found in mathlib as `IsEllDivSequence`**, identical form,
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:91`.
- Composition check (Phase 6): irrelevant — exact def already in mathlib.

**Rationale:**

The project's `IsEllDivSequence` is not merely *equivalent* to a mathlib declaration — it is a
verbatim fork of one. The file `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`
shares its copyright header, author (David Kurniadi Angdinata), module docstring, and
`## Main definitions` list with `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, and the
def body `IsEllSequence W ∧ IsDivSequence W` is character-for-character identical to mathlib's at
line 91. The literature (Ward 1948, Wikipedia, modern arXiv surveys) unanimously fixes this as the
standard definition of an EDS, and mathlib already encodes it at the right generality (`CommRing R`,
ℤ-indexed). There is no generalisation, no modernisation, and no new mathematical content in the
*def*: it is the canonical mathlib definition, re-declared inside the project because the project
forked the whole file (to extend it with results mathlib lists as TODO — e.g. `eq_normEDS`).

**WHY not (refactor-actionable):**
Mathlib already has it, byte-identical. The named gap mathlib *does* have is downstream of this def
— `IsEllDivSequence.normEDS` and the converse `eq_normEDS` are explicit mathlib TODOs (lines 44-45
of the mathlib file) — but those are **theorems built on** `IsEllDivSequence`, not the def itself.
Re-declaring the def locally forces every project lemma to be about the *project's* `IsEllDivSequence`
rather than mathlib's, which is exactly what blocks those TODO-discharging theorems from being
upstreamed cleanly.

Existing mathlib decl:        `IsEllDivSequence`
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:91`
Our form follows in 0 lines (it is the same def):
```lean
-- mathlib (line 91):
def IsEllDivSequence : Prop := IsEllSequence W ∧ IsDivSequence W
-- project (line 606): identical body
```
Call sites in our project (Phase 6.0): 3 (NagellLutz) + 1 (HasseWeil parallel copy).

**Refactor plan:**
1. Delete the project's `IsEllSequence` / `IsDivSequence` / `IsEllDivSequence` re-declarations
   (lines 135, 602, 606 and their `_root_` hoists) and replace
   `import` of the local file's defs with
   `public import Mathlib.NumberTheory.EllipticDivisibilitySequence`.
2. **Watch one mismatch:** mathlib's companion `IsDivSequence` is ℕ-indexed
   (`∀ m n : ℕ, m ∣ n → W m ∣ W n`) while the project's is ℤ-indexed
   (`∀ m n : ℤ, m ∣ n → W m ∣ W n`). `IsEllDivSequence` itself is identical, but if any project
   proof relies on the ℤ-indexed divisibility, that companion def must be reconciled first (it is a
   **separate** mathlibable question — assess `IsDivSequence` on its own; the ℤ-vs-ℕ choice may even
   be a generalisation worth upstreaming there). The `IsEllDivSequence` *def* needs no such care.
3. After the swap, the project's genuinely-new theorems (`IsEllDivSequence.eq_normEDS`,
   `IsEllDivSequence.normEDS`) become statements about mathlib's `IsEllDivSequence` — which is the
   correct precondition for upstreaming them to discharge mathlib's TODOs.

**Next action:** delete `IsEllDivSequence` (and its siblings) from the project; import from
`Mathlib.NumberTheory.EllipticDivisibilitySequence`; reconcile the ℤ-vs-ℕ `IsDivSequence` companion
separately. Consider a follow-up mathlib PR upstreaming the project's `eq_normEDS` /
`IsEllDivSequence.normEDS` to close the mathlib TODOs (those are the real contributions in this file).

---

## Next step

Delete `IsEllDivSequence` from the project and import it from
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (root-level name `IsEllDivSequence`,
file `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:91`). Reconcile the companion
`IsDivSequence` (ℤ-indexed locally vs. ℕ-indexed in mathlib) as a separate item.

# /mathlibable report — `EllSequence.rel₆_eq`

## Verdict: **NO-composable-from-mathlib**

One-line: a `@[simp]`, `:= rfl` definitional-unfolding glue lemma for the
project-local `abbrev EllSequence.rel₆`. No standalone mathematical content;
recoverable from the abbreviation by `rfl`/`unfold`/`simp only [rel₆]` in ≤1 step.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task note; reasoned from source)
- decl `EllSequence.rel₆_eq`: ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:304`
- qualified name:           `EllSequence.rel₆_eq` (file opens `namespace EllSequence` at L90; decl is inside it, before `end EllSequence` at L597). **VERIFIED.**
- kind:                     `lemma` (with `@[simp]`)
- has sorry:                no (body is `rfl`)
- module docstring summary: Elliptic divisibility sequences / Stange's elliptic nets; defines the `addMulSub`/`rel₃`/`rel₄`/`net`/`rel₆` relation apparatus used to prove the EDS recurrences (forks + extends `Mathlib.NumberTheory.EllipticDivisibilitySequence`).

---

### Statement (Phase 1)

```lean
abbrev rel₆ (k l a b c d : ℤ) : R := addMulSub W k l * rel₄ W a b c d   -- L302

@[simp] lemma rel₆_eq (k l a b c d : ℤ) :
    rel₆ W k l a b c d = addMulSub W k l * rel₄ W a b c d := rfl          -- L304
```

`rel₆_eq` states that the abbreviation `rel₆` (defined one line above as
`addMulSub W k l * rel₄ W a b c d`) is *equal to its own definition*. It is a
`rfl` lemma: pure definitional unfolding, tagged `@[simp]` so the unfolding can
be triggered/controlled in tactic blocks.

- `R` : a commutative ring; `W : ℤ → R` is the sequence (section variables).
- `addMulSub W m n := W ((m+n).tdiv 2) * W ((m-n).tdiv 2)` (L94) — the basic building block of elliptic relations.
- `rel₄ W a b c d := addMulSub W a b * addMulSub W c d − addMulSub W a c * addMulSub W b d + addMulSub W a d * addMulSub W b c` (L103) — the four-index Ward/Stange elliptic-net relation.
- `rel₆ W k l a b c d` — "the four-index relation `rel₄` multiplied by the two-index coefficient `addMulSub W k l`" (docstring L301).

Conclusion (math): trivial identity `rel₆ = (its definition)`.
Conclusion (Lean): `rel₆ W k l a b c d = addMulSub W k l * rel₄ W a b c d`, proved by `rfl`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a `:= rfl` helper lemma unfolding a one-line abbreviation; not a named
theorem, not a `## Main results` entry, not a new structure. (Lit width run
exhaustively regardless.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`rfl`). The *subject* `abbrev rel₆` is also a one-liner.
One-liner verdict: this is a **lemma**, so the def one-liner table is n/a — but the lemma is itself a trivial `rfl`, the strongest possible negative signal: it has no content beyond definitional equality of an `abbrev`.

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | no       | The opposite: `rel₆` is an `abbrev` (reducible), so the equation already holds by `rfl` everywhere; the lemma does not *seal* anything. It exists only to give `simp`/`rw` a named handle to fold/unfold (`← rel₆_eq` then `simp only [rel₆_eq]`). |
| Avoid typeclass diamonds          | no       | No instances involved; `rel₆` is a plain ring-valued function. |
| Mark semantic intent / API name   | no (for the *lemma*) | The *abbrev* `rel₆` carries the semantic name + docstring; the equation lemma adds nothing a consumer depends on beyond `rel₆` itself unfolding. |

Conclusion: definitional-unfolding lemma; strong NO signal. Mathlibability is inherited from the parent `abbrev rel₆` (skill's glue-lemma inheritance rule).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence four-term Ward addition relation division polynomial net Stange"       | yes  | Ward's relation `W(n+m)W(n−m)W(r)² + W(m+r)W(m−r)W(n)² + W(r+n)W(r−n)W(m)² = 0` | Wikipedia EDS; Ward Memoir. The *relation* is standard; `rel₆` is not. |
|  2 | WebSearch (general form)         | "elliptic net" Stange "addMulSub" OR "three-term recurrence" … quadratic relation                      | partial | Stange net recurrence `W(p+q+s)W(p−q)W(r+s)W(r)+…=0` | Stange "Elliptic nets and elliptic curves" (arXiv:0710.1316). Explicitly: **"addMulSub terminology not found"**. |
|  3 | WebSearch (named-after / aliases)| (covered by #1/#2 hits) "Ward addition relation", "elliptic net recurrence"                             | yes  | as #1/#2            | Concept = Ward/Stange relation; the names `addMulSub`/`rel₄`/`rel₆` are this project's. |
|  4 | ChatGPT MCP                      | "is rel₆ a named concept; does `abbrev = its-definition := rfl` carry content?"                        | n/a  | —                   | **MCP down** (Codex exec failed — matches task note "ChatGPT MCP may be down"). Fallback channels used. |
|  5 | Local references                 | `.mathlib-quality/references/` for "rel₆"/"addMulSub"/"net"                                            | n/a  | —                   | No references dir for this concept located; recorded n/a. Source docstrings (L16–24, L301) cite Stange's paper directly and state the names are project-chosen ("changed compared to Stange's paper"). |
|  6 | nLab                             | "elliptic divisibility sequence" / "elliptic net"                                                       | n/a  | —                   | Not an nLab concept (no categorical content); the relation is elementary number theory. |
|  7 | nCatLab                          | —                                                                                                      | n/a  | —                   | Not categorical. |
|  8 | Stacks Project                   | —                                                                                                      | n/a  | —                   | EDS recurrences are not in Stacks (not a scheme-theoretic statement); `rel₆` certainly not. |
|  9 | MathOverflow / MSE               | "elliptic divisibility sequence Ward relation" generality                                              | yes  | as #1               | Confirms Ward relation is the standard object; no "rel₆" coefficient-times-relation named device. |
| 10 | recent arXiv (5y)                | Stange elliptic nets; arXiv:2512.09601 "Explicit valuation of elliptic nets …"                         | yes  | net recurrence as #2 | Modern work still uses the *net recurrence*; nobody names a "relation × addMulSub coefficient" object. |

Sources: Wikipedia "Elliptic divisibility sequence"; Stange, *Elliptic nets and elliptic curves* (arXiv:0710.1316); Stange's MSR/Tate-pairing talks (math.colorado.edu/~kstange); arXiv:2512.09601.

### Literature summary (Phase 3)

Concept identified as: **Ward's addition relation / Stange's elliptic-net recurrence** (the underlying math of `rel₄`/`net`). The specific object `rel₆` = "`rel₄` scaled by an `addMulSub` coefficient" is **project-specific proof scaffolding**, not a named literature concept.
Sources agree on the standard form: yes (Ward/Stange relation). On `rel₆`: there is nothing to agree on — it has no literature name.
Most general standard form: the net recurrence (Stange), of which Ward's 3-term relation is the rank-1 case. The project's `rel₄`/`net` already encode this; `rel₆` is a derived bookkeeping product internal to the project's induction (`rel₆_eq₃`/`rel₆_eq₁₀` are the real identities).
Disagreement with the literature: none. The docstrings themselves flag that the formulation deviates from Stange's paper deliberately ("two signs swapped … to make the equivalence unconditional", L21–23) — i.e. these are bespoke project definitions.

---

### Generality analysis — `EllSequence.rel₆_eq`

Literature-standard form (Phase 3): n/a — `rel₆_eq` is not a mathematical statement with a literature analogue; it is `abbrev = its-own-definition`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form? | Reason |
|---|------------------------|-------------------|----------------------|--------------|--------|
| 1 | `[CommRing R]` (section) | commutative ring | — | n/a | Already maximally general for the ring; `rel₆`/`rel₄` are defined over any `CommRing`. The lemma is `rfl` regardless. |
| 2 | `k l a b c d : ℤ` | integer indices | — | n/a | Inherent to EDS indexing; not a weakening axis for a `rfl` lemma. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (vacuously — a `rfl` unfolding lemma has no hypotheses to weaken).
Number of weakening opportunities: 0.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Reformulation | Downstream |
|---|----------|----------|---------------|------------|
| 1 | bundled hyps → typeclasses? | no | — | no hypotheses |
| 2 | sequences/metric → filters/topology? | no | — | finite ring identity, no topology |
| 3 | construct → universal-property class? | no | — | `rel₆` is a product of two ring expressions |
| 4 | set+closure-pred → bundled substructure? | no | — | n/a |
| 5 | vector-space/field → modules/(semi)ring? | no | already over `CommRing` | n/a |
| 6 | 1-categorical → higher-categorical? | no | — | n/a |
| 7 | concrete index → general additive structure? | no | indices are `ℤ` by definition of EDS | n/a |

Modern idiom available: **no**. A `rfl` unfolding of an `abbrev` has no idiomatic alternative to modernise toward.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equality or typeclass-search path introduced). (The *parent* `abbrev rel₆` is reducible by construction; that is the reason the lemma is content-free, not a separate risk.)

---

### Mathlib search-status: `EllSequence.rel₆_eq`

[A] Lean-Finder       n/a (mathlib index for `rel₆`/`addMulSub`)  no hits — not loadable offline; covered by [D]
[B] Loogle            `rel₆`, `addMulSub`, pattern `_ * (_ - _ + _)` over `ℤ → R`  no hits for the named objects
[C] LeanSearch        "elliptic relation times coefficient", "rel₆ abbrev equals definition"  no hits
[D] Grep mathlib src  `grep -rnE "(rel₆|addMulSub)" .lake/packages/mathlib/Mathlib/`  **zero matches** — none of `rel₆`, `rel₄`, `addMulSub`, `net`, or the `EllSequence` namespace exist in mathlib
[E] Name pattern      `EllSequence.rel₆_eq`, `rel₆_eq` in mathlib tree  no hits

Searched for both:
  - user's form (`rel₆_eq` / `rel₆`): absent from mathlib.
  - the literature-standard form (Ward/Stange relation): mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (547 lines) takes a **completely different route** — it defines `IsEllSequence` as a `Prop` (the recurrence as a predicate, L82), `IsDivSequence`, `IsEllDivSequence`, and the `preNormEDS`/`normEDS`/`complEDS` *construction* (a recursively-defined sequence). It has **no** `addMulSub`/`rel₄`/`rel₆`/`net` factored-relation apparatus. So the project's entire `EllSequence.*` relation track — including `rel₆` and this lemma — is new, project-local code (a fork/extension), not present upstream.

Concluded: **not in mathlib** (all methods exhausted; the literature-standard EDS API in mathlib uses an unrelated formulation). The *parent abbreviation* `rel₆` is also not in mathlib.

---

### Call sites — `EllSequence.rel₆_eq`

Internal use count (this NagellLutz file, excl. declaring line): **3** — L429 (`← rel₆_eq`), L432 (`simp only [rel₆_eq]`), L444 (`← rel₆_eq` … `simp only [rel₆_eq]`).
External-to-file callers: it is **duplicated verbatim**, not imported, in two other places:
  - `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:261` (independent copy; used at L354/357/366 there).
  - `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:` (a `…Original` snapshot copy in the same project).

| Caller file:line | Usage pattern |
|------------------|---------------|
| EllipticDivisibilitySequence.lean:429 | `… <;> rw [mul_comm, ← rel₆_eq]` (fold `addMulSub*rel₄` → `rel₆`) |
| EllipticDivisibilitySequence.lean:432 | `all_goals simp only [rel₆_eq]; rw [rel le_rfl, …]` (unfold back) |
| EllipticDivisibilitySequence.lean:444 | `rw [mul_comm, ← rel₆_eq, rel₆_eq₁₀]; simp only [rel₆_eq]` |

Inline-derivation grep: the `…Original.lean` copy at L423 does the *same* manoeuvre using `rw [mul_comm, ← rel₆, rel₆_eq₁₀]; simp_rw [rel₆]` — i.e. it folds/unfolds via the **abbrev `rel₆` directly** (`← rel₆` / `simp_rw [rel₆]`) instead of the lemma. This is direct evidence the lemma is redundant: the identical job is done by unfolding the abbreviation, with no `rel₆_eq` lemma needed.

Signal: K=3 internal uses, but **every use is fold-then-unfold of a reducible `abbrev`** — a `simp`-plumbing convenience, not a mathematical dependency. The `…Original` copy proves the same proofs go through using the bare `abbrev`. This is the "wrapper consumers can bypass" pattern → NO-composable.

---

### Composition check (Phase 6)

Can `EllSequence.rel₆_eq` be derived from mathlib in ≤3 chained calls? — Wrong framing (it is not a mathlib statement), so the right question is: *given the parent `abbrev rel₆`, is the lemma a trivial composition?*

Attempt 1: `rfl`.
  - Decls used: the definitional equality of `abbrev rel₆` itself.
  - Result: **succeeds** — the lemma body *is* `rfl`. Because `rel₆` is an `abbrev` (semireducible/reducible), `rel₆ W k l a b c d = addMulSub W k l * rel₄ W a b c d` holds by `rfl`, and `simp [rel₆]` / `unfold rel₆` reproduce the rewrite at any call site without the named lemma.

Conclusion: **COMPOSABLE** (0–1 step). The lemma is recoverable from its own definition; no new lemma is needed in mathlib.

---

## Verdict: `EllSequence.rel₆_eq`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the math is Ward/Stange's relation; `rel₆` is *project scaffolding* with no literature name ("addMulSub terminology not found"). No standard object `rel₆_eq` exists to upstream.
- Generality analysis (Phase 4): vacuously maximally general; a `rfl` unfolding lemma, no idiom to modernise.
- Mathlib search (Phase 5): not in mathlib; moreover the *whole* `addMulSub`/`rel₄`/`rel₆`/`net` track is absent upstream — mathlib's EDS uses the unrelated `IsEllSequence`/`normEDS` formulation. The parent `abbrev rel₆` is also not in mathlib.
- Composition check (Phase 6): COMPOSABLE — body is `rfl`; recoverable via `unfold rel₆` / `simp [rel₆]`.

**Rationale:**

`rel₆_eq` is a `@[simp]`, `:= rfl` lemma asserting that the one-line abbreviation
`abbrev rel₆ … := addMulSub W k l * rel₄ W a b c d` equals its own right-hand
side. It carries **zero mathematical content** independent of the abbreviation:
since `rel₆` is reducible, the equation holds definitionally and every call site
can fold/unfold with `← rel₆ … ; simp_rw [rel₆]` — which is exactly what the
sibling `…Original.lean` copy does (L423), with no `rel₆_eq` lemma in sight. The
genuine mathematics lives in the *other* `rel₆_*` results (`rel₆_eq₃`,
`rel₆_eq₃'`, `rel₆_eq₁₀`, `addMulSub_sq_mul_rel₄_eq₉` — the ring identities that
re-express a `rel₄`), not here.

It is therefore not a mathlib candidate in its own right. Mathlib does not ship
`foo_eq : foo args = (rhs) := rfl` companions for reducible `abbrev`s — the
abbreviation already unfolds. And the parent object it unfolds (`rel₆`, and the
entire `addMulSub`/`rel₄`/`net` apparatus) is itself project-local proof
infrastructure that mathlib's EDS file does not use (mathlib formalises EDS via
`IsEllSequence` + the `normEDS` construction, a different formulation). So even
the strongest pro-upstreaming move — "ship it alongside its parent def" — does
not apply: the parent isn't in mathlib, and if the `rel₄`/`rel₆` machinery were
ever upstreamed, this `rfl` lemma would not travel with it as a separate
declaration.

**WHY not (refactor-actionable):**
Mathlib has the building block in the most literal sense: it *is* the
abbreviation `rel₆`, which lives in the project. The lemma is a ≤1-call
composition (`rfl`). No mathlib lemma is needed; nothing to inline *from*
mathlib — the equation is just `rel₆`'s own definition.

Mathlib building blocks: none required — `EllSequence.rel₆` (the `abbrev` at L302) reduces to the RHS by `rfl`.
Composition sketch (≤1 line):
```lean
example (k l a b c d : ℤ) :
    rel₆ W k l a b c d = addMulSub W k l * rel₄ W a b c d := rfl
```
Call sites in this project (Phase 6.0): K = 3 (all fold/unfold plumbing).
Refactor plan (project-internal cleanup, NOT a mathlib action):
  - This lemma may legitimately stay as a *local* `simp`/`rw` convenience — that
    is a project style choice, not a mathlib contribution. If a cleaner wishes to
    remove it: at L429/L432/L444 replace `← rel₆_eq` / `simp only [rel₆_eq]` with
    `← (rel₆ W …)`-style `show`/`unfold rel₆` / `simp only [rel₆]` (the
    `…Original.lean` copy at L423 already demonstrates the bare-abbrev form works).
  - Separately, the verbatim duplication across NagellLutz, `…Original`, and
    HasseWeil (`Auxiliary/EllipticDivisibilitySequence.lean:261`) is a
    cross-project dedup item for `/cleanup` (consolidate into one shared module),
    independent of mathlibability.
Next action (mathlib): **none** — do not propose `rel₆_eq` for mathlib. It is
local proof glue for a reducible abbreviation.

---

## Next step

Do not upstream `EllSequence.rel₆_eq`. It is a `:= rfl` unfolding lemma for the
project-local reducible `abbrev rel₆`, recoverable by `unfold`/`simp [rel₆]` and
already bypassed via the bare abbrev in a sibling copy. The mathlib-relevant
question, if any, is whether the *underlying `rel₄`/`net` (Ward–Stange relation)
apparatus* should be upstreamed — a separate, much larger assessment on those
defs/theorems, not on this glue lemma. For the AINTLIB fleet, the actionable
follow-up is dedup of the triplicated copies via `/cleanup`.

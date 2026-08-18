# /mathlibable report — `EllSequence.rel₄_same₂₃`

_Project: NagellLutz · file:_ `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:561`
_Run: /overview Step-9 mathlibable assessment (single declaration)._

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief; reasoned from source — decl elaborates in committed file, green per repo status)
- decl `EllSequence.rel₄_same₂₃`: ✓ resolved at `EllipticDivisibilitySequence.lean:561` (namespace `EllSequence`, opened at line 90)
- kind:                      `lemma`
- has sorry:                 no
- module docstring summary:  Defines elliptic divisibility sequences (EDS) and constructs normalised EDSs from initial terms; ports Angdinata's mathlib EDS file plus a new `EllSequence` apparatus (`addMulSub`/`rel₄`/`net`/`relFin4`) for proving a sequence is elliptic from the even-odd recurrence.

**Qualified name (VERIFIED):** `EllSequence.rel₄_same₂₃` — confirmed: `namespace EllSequence` opens at line 90 and is not closed (`end EllSequence` at line 597) before line 561. Base name `rel₄_same₂₃`.

---

### Statement (Phase 1)

`EllSequence.rel₄_same₂₃` states that the four-index elliptic-relation expression `rel₄ W m n r s` vanishes when its **last two indices coincide** (`s = r`):

> For a sequence `W : ℤ → R` over a commutative ring `R` with `W 0 = 0`, and any `m n r : ℤ`,
> `rel₄ W m n r r = 0`.

Here `rel₄` is a **project-local definition** (line 103):
```
rel₄ W a b c d  :=  addMulSub W a b * addMulSub W c d
                  − addMulSub W a c * addMulSub W b d
                  + addMulSub W a d * addMulSub W b c
```
and `addMulSub W m n := W ((m+n).tdiv 2) * W ((m−n).tdiv 2)` (line 94). The lemma is the third of three sibling "diagonal-vanishing" facts:
- `rel₄_same₀₁ : rel₄ W m m r s = 0` (first two indices equal),
- `rel₄_same₁₂ : rel₄ W m n n s = 0` (middle two equal),
- `rel₄_same₂₃ : rel₄ W m n r r = 0` (last two equal) ← **this decl**.

Mathematically these say: the Plücker-like 3-term sum that defines the four-index elliptic relation is an *alternating* function of its index pairs, so it dies on any diagonal. The single fact powering all three is `addMulSub_same` (`addMulSub W m m = 0`, because `W ((m−m).tdiv 2) = W 0 = 0`).

Variables / typeclasses involved (Lean side):
- `R : Type u` with `[CommRing R]` — the value ring.
- `W : ℤ → R` — the sequence (section variable).
- `m n r : ℤ` — explicit indices.

Hypotheses (Lean side):
- `zero : W 0 = 0` — a section hypothesis (`variable (zero : W 0 = 0)` at line 547, `include zero`), provided by the `omit neg in` lemma so only `zero` (not `neg`) is used.

Conclusion (math): the four-index elliptic relation vanishes on the `c = d` diagonal.
Conclusion (Lean): `rel₄ W m n r r = 0`.

Proof body (one line): `simp_rw [rel₄, addMulSub_same W zero]; ring`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A helper glue lemma — one of three identical "diagonal vanishing" facts about a project-local `def` (`rel₄`); not a named theorem, not a `## Main statement`, not a new structure. Pure scaffolding for the permutation-reduction step inside `rel₄_of_oddRec_evenRec`.

(Literature width was run EXHAUSTIVE regardless; SMALL is recorded for framing.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → the one-liner def-exemption machinery does not apply. Note only: the *proof* is a one-liner (`simp_rw […]; ring`), which is itself a strong "this is composable glue" signal carried into Phases 6–7.

Conclusion: n/a (lemma).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                   | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "Stange elliptic net relation four indices vanishes when two indices equal antisymmetry"                | partial | Stange's net relation $W(p{+}q{+}s)W(p{-}q)W(r{+}s)W(r) + \dots = 0$; vanishing-on-diagonal is implicit in the $W(0)=0$ / antisymmetry structure | arXiv 0710.1316 (Stange, "Elliptic nets and elliptic curves"), 1408.6623 (symmetries of elliptic nets), 1702.08102 (signs). No source names a standalone "diagonal vanishing" lemma. |
|  2 | WebSearch (general form)         | "elliptic divisibility sequence W(m+n)W(m-n) relation diagonal vanishing two arguments equal"           | partial | The EDS recurrence $W_{n+m}W_{n-m}W_r^2 + W_{m+r}W_{m-r}W_n^2 + W_{r+n}W_{r-n}W_m^2 = 0$; diagonal-vanishing not isolated | Wikipedia EDS; arXiv math/0402415, 2102.07573. Confirms the relation but the "two args equal ⇒ 0" specialization is treated as a triviality, never a named result. |
|  3 | WebSearch (named-after / aliases / project source) | "mathlib EllSequence addMulSub rel₄ relFin4 of_oddRec_evenRec"                          | yes  | Source paper identified: arXiv **2604.05280**, "On Elliptic Sequences over Commutative Rings" | This is the paper the `EllSequence` apparatus formalizes (commutative-ring EDS via even-odd recurrence). `rel₄_same₂₃` is internal to its proof apparatus, not a stated result. |
|  4 | ChatGPT MCP                      | (planned) "standard form + generality + history of the four-index elliptic relation vanishing on a diagonal" | n/a — MCP down per task brief | — | Fallback: WebSearch ×3 + arXiv source paper + nLab + first-principles reasoning from the source statement (below). The math content is elementary algebra (alternating 3-term sum), so the standard-form question is fully resolved without MCP. |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`                                                  | n/a  | (directory absent)                                   | `references/` does not exist for NagellLutz; recorded n/a. |
|  6 | nLab                             | "elliptic divisibility sequence" / "elliptic net"                                                        | n/a  | nLab has no EDS / elliptic-net entry                 | Not a category-theoretic concept; nLab does not cover it. |
|  7 | nCatLab (categorical)            | —                                                                                                       | n/a  | —                                                    | Not a categorical concept. |
|  8 | Stacks Project (alg geom)        | "elliptic divisibility sequence" / "division polynomial"                                                 | n/a  | Stacks has no EDS / division-polynomial section      | Stacks covers schemes/stacks foundations, not the arithmetic of EDS recurrences. |
|  9 | MathOverflow / Math.StackExchange| "elliptic net relation two indices equal" (covered via WebSearch general crawl)                          | no   | No isolated statement found                          | Discussions treat diagonal-vanishing as obvious from $W(0)=0$. |
| 10 | recent arXiv (last 5 years)      | (covered by #1–#3) 1408.6623 (2014), 2102.07573 (2021), 2604.05280 (2026)                                | yes  | Confirms the apparatus is current research; no named diagonal lemma | 2604.05280 is the direct source; even it does not name this sub-fact. |

### Literature summary (Phase 3)

Concept identified as: the **four-index elliptic relation** `rel₄` (a same-parity reformulation of Stange's elliptic-net relation / the Ward EDS recurrence), and specifically its **vanishing on a coincident-index diagonal**.
Sources agree on the standard form: **yes** for the *relation itself* (Stange's net relation and the Ward recurrence are standard and equivalent); **the diagonal-vanishing specialization is not a named result** in any source — it is treated as an immediate triviality of the structure (a paired factor becomes `W(0) = 0`).
Most general standard form: the elliptic-net / Ward relation `W(m+n)W(m−n)W(r)² = W(m+r)W(m−r)W(n)² − W(n+r)W(n−r)W(m)²` (mathlib already encodes this as `IsEllSequence`). `rel₄` is the project's `addMulSub`-factored, all-four-indices-permutable repackaging; `rel₄_same₂₃` is the trivial corollary "vanishes when last two indices agree."
Generality dimensions where the literature varies:
  - value structure: integral domain (classical Ward/Stange) → **commutative ring** (arXiv 2604.05280 and this formalization — the *more general* setting, already adopted here). No further weakening available (`addMulSub` and `W 0 = 0` need only `CommRing`).
  - which diagonal: the three siblings `_same₀₁/₁₂/₂₃` cover all adjacent diagonals; full permutation symmetry is `relFin4_perm`.
Disagreement with the literature: **none.** The Lean form is, if anything, *more* general than the classical literature (commutative ring vs. integral domain) and the diagonal fact is below the granularity any source bothers to name.

---

### Generality analysis — `EllSequence.rel₄_same₂₃`

Literature-standard form (from Phase 3): there is **no** literature-standard standalone form of this fact; the ambient relation `rel₄` is already at maximal generality (`CommRing`, all-four-index-permutable).

| # | Parameter / hypothesis | Current Lean form        | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|--------------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`         | commutative ring         | (literature: integral domain) | NO — already weaker | The proof uses only `CommRing` ops + `ring`; this is *more* general than the classical integral-domain setting. Cannot weaken to a non-commutative or non-associative structure (`rel₄` and `ring` need `CommRing`). |
| 2 | `zero : W 0 = 0`       | `W 0 = 0` hypothesis     | same                     | NO                  | Essential: the whole content is `addMulSub W r r = W(0)·W(…) = 0`. Without `W 0 = 0` the lemma is false. |
| 3 | `m n r : ℤ` (indices)  | integer indices          | integer indices          | NO                  | `rel₄`/`addMulSub` are defined on `ℤ` via `Int.tdiv 2`; the index type is intrinsic to the EDS setup, not a generalizable knob. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it is already strictly more general than the classical integral-domain literature form, and every hypothesis is load-bearing).
Number of weakening opportunities found: 0.
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "Let X be a foo" → typeclass/instance? | no | — | The only hypothesis is the bare equation `W 0 = 0`; there is no "structure" to bundle. |
| 2 | sequences/metric → filters/topology? | no | — | Purely algebraic finite identity; no limits/topology. |
| 3 | construction → universal property? | no | — | It is a vanishing equation, not a construction. |
| 4 | set+closure-predicate → bundled substructure? | no | — | No substructure here. |
| 5 | vector-space/field-specific → weaken typeclass? | no | — | Already `CommRing`; nothing field-specific. |
| 6 | 1-categorical → higher-categorical? | no | — | Not categorical. |
| 7 | concrete index (ℕ/ℤ/ℝ) → general monoid/group? | no | — | Indices live on `ℤ` intrinsically (`Int.tdiv 2` in `addMulSub`); generalizing the index type would require redefining `rel₄` itself, out of scope for a one-line corollary. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**.
One-line reason: a finite algebraic identity with a single bare-equation hypothesis over `CommRing` — there is no abstraction (typeclass, filter, universal property, substructure) to modernize toward; it is already in the contemporary form.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `EllSequence.rel₄_same₂₃`

[A] Lean-Finder       (mathlib index unavailable for live query; reasoned via grep over the vendored mathlib tree) — n/a
[B] Loogle            type pattern `rel₄ _ _ _ _ _ = 0` / `addMulSub`-shaped — n/a: the symbols `rel₄`, `addMulSub`, `relFin4`, `HaveSameParity₄` **do not exist in mathlib**, so no type pattern can match. (See [D].)
[C] LeanSearch        NL: "four-index elliptic relation vanishes when two indices equal" — no hit (the concept's apparatus is not in mathlib).
[D] Grep mathlib src  `grep -rE "addMulSub|relFin4|HaveSameParity₄|\brel₄\b" .lake/packages/mathlib/Mathlib/` → **empty (confirmed absent)**. Also `grep -rE "rel₄_same|namespace EllSequence|def addMulSub|def rel₄" .lake/packages/mathlib/` → empty. Mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (547 lines) contains only `IsEllSequence`/`IsDivSequence`/`normEDS`/`preNormEDS`/`complEDS` machinery — **no `EllSequence` namespace, no `rel₄` apparatus**.
[E] Name pattern      grep for `rel₄_same₂₃` across mathlib → no match.

Searched for both:
  - the user's current form (`rel₄ W m n r r = 0`) — not in mathlib (subject `rel₄` absent).
  - the literature-standard form (the Ward/Stange relation `IsEllSequence`) — mathlib **does** have `IsEllSequence` (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:82`), but it has **no** `rel₄`-factored four-index repackaging and **no** diagonal-vanishing lemma about it. The "diagonal vanishing" fact has no mathlib analog because the `rel₄` object it concerns is not in mathlib.

Concluded: **not in mathlib** (all methods exhausted; both the user's form and the closest mathlib concept `IsEllSequence` checked — mathlib lacks the entire `rel₄`/`addMulSub` apparatus this lemma lives in).

---

### Call sites — `EllSequence.rel₄_same₂₃`

Internal use count (within NagellLutz, excluding the declaring file's own line 561): **1**
External-to-file callers (genuine consumers, not forks): **0**

| Caller file:line                                                                 | Usage pattern (one-line excerpt)                                  |
|----------------------------------------------------------------------------------|-------------------------------------------------------------------|
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:581`           | `by_cases h₃₂ : t (σ 3) = t (σ 2); · rw [h₃₂, rel₄_same₂₃ zero, smul_zero]` |

Fork copies (same code duplicated across the repo's parallel tracks — **not** independent consumers):
- `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:536` (declaration) + `:556` (use) — the "Original" track.
- `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:476` (declaration) + `:498` (use) — HasseWeil's vendored copy of the same apparatus.

Inline-derivation grep (was the equivalent re-derived elsewhere without using `rel₄_same₂₃`?):
  - (none) — every use of the fact goes through this lemma; its two siblings `rel₄_same₀₁`/`rel₄_same₁₂` are used at the adjacent lines 583/582 of the same proof.

Signal: **K = 1 internal use, used exactly once, inside a single proof** (`rel₄_of_oddRec_evenRec`), alongside two identical siblings. This is "private proof glue," not reusable API. Per the call-sites table (Phase 6.0.1), K = 1 leans toward NO-composable (could be inlined).

---

### Composition check (Phase 6)

Can `rel₄_same₂₃` be derived in ≤3 chained mathlib + project-primitive calls?

Attempt 1: unfold + rewrite the building block, then ring.
```lean
example (zero : W 0 = 0) (m n r : ℤ) : rel₄ W m n r r = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring
```
  - Primitives used: `rel₄` (project def, unfolded), `EllSequence.addMulSub_same` (project lemma: `addMulSub W m m = 0`, line 181), `ring`.
  - Result: **succeeds** — this is verbatim the actual proof body. Two `simp_rw` rewrites + `ring` (≤3 steps).
  - Notes: the only non-mathlib primitive is `addMulSub_same`, which is itself a 4-step unfold (`addMulSub, sub_self, Int.zero_tdiv, zero, mul_zero`) over the project-local `addMulSub`. The "composition" is entirely over **project-local** definitions; mathlib supplies only `ring`/`sub_self`/`Int.zero_tdiv`/`mul_zero`.

Conclusion: **COMPOSABLE** — a ≤3-step composition (`simp_rw [rel₄, addMulSub_same]; ring`). No new idea; it is mechanical unfolding once `addMulSub_same` is in hand.

Composition heuristic check: the body is `simp_rw […]; ring` closing the goal — this is the "trivial simp/ring composition" row, i.e. genuinely inlinable, not a disguised proof (no intermediate `have`s, no reasoning between steps).

---

## Verdict: `EllSequence.rel₄_same₂₃`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the four-index relation `rel₄` is a standard object (Stange nets / Ward recurrence; source paper arXiv 2604.05280), but the diagonal-vanishing fact is **never named** in the literature — treated as a `W(0)=0` triviality.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** already (`CommRing`, stronger than classical integral-domain); no weakening, no modern-idiom move.
- Mathlib search (Phase 5): **not in mathlib** — the entire `rel₄`/`addMulSub` apparatus is absent; closest concept `IsEllSequence` has no four-index repackaging.
- Composition check (Phase 6): **COMPOSABLE** — `simp_rw [rel₄, addMulSub_same W zero]; ring` (≤3 steps over project-local primitives).

**Rationale:**

`rel₄_same₂₃` is not a mathlib candidate in its own right, for two compounding reasons. First, its subject `rel₄` is a **project-local definition** that does not exist in mathlib (confirmed: `grep` for `addMulSub`/`rel₄`/`relFin4`/`HaveSameParity₄` over the entire vendored mathlib tree returns empty; mathlib's EDS file stops at `IsEllSequence`/`normEDS`). A lemma about a project-local object cannot be upstreamed without first upstreaming that object — and the `rel₄` apparatus is itself an in-progress formalization of a 2026 research paper (arXiv 2604.05280, "On Elliptic Sequences over Commutative Rings"), squarely producer-WIP, not cleaned library. Second, even granting the apparatus, the lemma is a **one-line, ≤3-step composition** (`simp_rw [rel₄, addMulSub_same]; ring`) — one of three identical sibling "diagonal vanishing" facts (`_same₀₁`/`_same₁₂`/`_same₂₃`), each used exactly once, all inside the single proof `rel₄_of_oddRec_evenRec`. The content is purely "a paired `addMulSub W r r` factor is `W(0)·… = 0`," which the literature does not even bother to name. With K = 1 internal call site and no external consumers (the HasseWeil / `…Original` copies are duplicate forks, not independent users), there is no reusable-API case.

This is NO-composable rather than NO-mathlib-has-it because mathlib does **not** have the result (it lacks the `rel₄` object entirely) — but mathlib *does* supply the only non-project pieces of the proof (`ring`, `sub_self`, `Int.zero_tdiv`, `mul_zero`), and the project supplies the rest (`addMulSub_same`). The fact is a mechanical composition that should remain inlined/local, not promoted.

**WHY not (refactor-actionable detail).**
Mathlib has the *generic* building blocks (`ring`, `sub_self`, `Int.zero_tdiv`, `mul_zero`); the **project** supplies the domain-specific block `EllSequence.addMulSub_same` (line 181). The user's form is the ≤3-step composition below over those blocks. No new mathlib lemma is warranted: the lemma's entire job is to package "`rel₄` dies when its last two indices coincide," which unfolds in one `simp_rw` once `addMulSub_same` is available.

Mathlib building blocks: `ring` (tactic), `sub_self` (`Mathlib/Algebra/Group/Basic.lean`), `Int.zero_tdiv` (`Mathlib`/core `Int` API), `mul_zero` (`Mathlib/Algebra/GroupWithZero/Basic.lean`) — these are the mathlib pieces *inside* `addMulSub_same`; the four-index lemma itself needs only `ring` from mathlib.
Project building block: `EllSequence.addMulSub_same` (`EllipticDivisibilitySequence.lean:181`, `addMulSub W m m = 0`).

Composition sketch (≤3 lines — verbatim the current proof, i.e. the lemma *is* its own inline expansion):
```lean
-- at the single call site, in place of `rel₄_same₂₃ zero`:
example (zero : W 0 = 0) (m n r : ℤ) : rel₄ W m n r r = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring
```

Call sites in our project (from Phase 6.0): **K = 1** (line 581).
Refactor plan:
- **Recommended (do nothing for mathlib; keep local):** this lemma is correct, well-named project scaffolding for `rel₄_of_oddRec_evenRec`. It should **stay in the project**, not be sent to mathlib. The three `_same` siblings + the single proof that consumes them are a coherent local unit; naming them aids readability of the permutation-reduction (`by_cases` on which adjacent indices coincide at lines 581–583). No action needed beyond noting it is *out of mathlib scope*.
- **If ever minimizing surface:** at line 581 one *could* inline `rw [h₃₂]; simp_rw [rel₄, addMulSub_same zero]; ring; rw [smul_zero]`, deleting the named lemma — but this is **not** recommended, because the three named siblings document the symmetry and keep the `by_cases` arms parallel. The composability finding is what disqualifies it from mathlib, not a directive to inline locally.

**Next action:** No mathlib PR. Treat `rel₄_same₂₃` (and its siblings `rel₄_same₀₁`, `rel₄_same₁₂`) as **project-internal glue** that travels with the `rel₄` apparatus. If/when the entire `EllSequence` apparatus (the arXiv 2604.05280 formalization: `addMulSub`, `rel₄`, `relFin4`, `IsEllSequence.of_oddRec_evenRec`) is proposed for mathlib as a unit, these vanishing lemmas ride along as supporting API of that PR — they are never a standalone contribution. (Separately, the cleanup fleet should note the **triplicated** copies across `EllipticDivisibilitySequenceOriginal.lean` and `HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean` as a cross-project dedup target, but that is a `/cleanup` dedup ticket, not a mathlibable verdict.)

---

## Next step

No mathlib PR. Keep `EllSequence.rel₄_same₂₃` as project-internal scaffolding of the `rel₄` apparatus (formalizing arXiv 2604.05280); it is a ≤3-step composition (`simp_rw [rel₄, addMulSub_same W zero]; ring`) over a project-local `def` that does not exist in mathlib, with a single internal call site. It is out of standalone-mathlib scope; if the whole apparatus is ever upstreamed, it rides along as supporting API.

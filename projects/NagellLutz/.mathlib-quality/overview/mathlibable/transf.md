# /mathlibable report — `EllSequence.HaveSameParity₄.transf`

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief; reasoning from source). Mathlib package present at `.lake/packages/mathlib`.
- decl `EllSequence.HaveSameParity₄.transf`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:286`
- kind:                      theorem (theorem-class — no defeq / typeclass surface; Phase 4.5 skipped)
- has sorry:                 no
- module docstring summary:  Elliptic divisibility sequences (EDS); defines `IsEllSequence`/`normEDS`/`complEDS`, proves `normEDS` is an EDS. This file is a **project fork+extension** of `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

**Qualified name VERIFIED:** namespace `EllSequence` (line 90) → `namespace HaveSameParity₄` (line 216) → `theorem transf` (line 286). Full name = `EllSequence.HaveSameParity₄.transf`. Confirmed against the parsed name in the brief — correct. (Sibling `protected lemma abs` above is `protected`; `transf` is **not** protected.)

Exact source (lines 286–288):
```lean
theorem transf : HaveSameParity₄
    (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| := by
  simp_rw [HaveSameParity₄, negOnePow_abs, negOnePow_sub, same.1, same.2.1, same.2.2, true_and]
```
With section context: `variable {W a b c d} (same : HaveSameParity₄ a b c d)` + `include same` (line 219–220), and `a b c d : ℤ`.

---

### Statement (Phase 1)

`EllSequence.HaveSameParity₄.transf` states: if four integers `a, b, c, d` all share a parity (`HaveSameParity₄ a b c d`, i.e. equal `Int.negOnePow`), then the **transformed quadruple**
`(avg₄ a b c d − d,  avg₄ a b c d − c,  avg₄ a b c d − b,  |avg₄ a b c d − a|)`
*also* has all four entries of one common parity.

Here `avg₄ a b c d := (a + b + c + d) / 2` (bespoke `def`, line 214) and `HaveSameParity₄` (bespoke `def`, line 210) is the chain `a.negOnePow = b.negOnePow ∧ b.negOnePow = c.negOnePow ∧ c.negOnePow = d.negOnePow`.

Mathematically: this is the parity-bookkeeping half of the **descent step** in the proof that the four-index elliptic relation `rel₄ W a b c d` vanishes for same-parity, strictly-decreasing indices. The transformation `xᵢ ↦ avg₄ − (index)` is a reflection of the four indices about their common average; the theorem records that this reflection preserves "all four indices share a parity". Its order-counterpart `strictAnti₄_transf` (line 290) records that the reflection lands inside the strictly-decreasing region, and `rel₄_transf` (line 280) records that it preserves the value of `rel₄`. Together they feed the induction `ih` at line 492.

Variables / typeclasses (Lean side):
- `a b c d : ℤ` — the four indices (section `variable`, line 204). No ring/`W`/typeclass parameters are used by `transf`: it is purely a statement about `ℤ` parities (`W : ℤ → R` is in scope via `include same` but does not appear in the conclusion).

Hypotheses (Lean side):
- `same : HaveSameParity₄ a b c d` — the four indices share a parity (supplied as a section `include`).

Conclusion (math): the average-reflection map `x ↦ avg₄ − x` (with `|·|` on the last slot) sends a same-parity quadruple to a same-parity quadruple.
Conclusion (Lean): `HaveSameParity₄ (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a|`.

Proof (1 line): `simp_rw [HaveSameParity₄, negOnePow_abs, negOnePow_sub, same.1, same.2.1, same.2.2, true_and]`. Unfold the predicate to three `negOnePow` equalities; `negOnePow_abs` strips the `|·|`; `negOnePow_sub` turns each `negOnePow (avg₄ − xᵢ)` into `negOnePow avg₄ * negOnePow xᵢ` (as units); the three `same.*` rewrites collapse the `negOnePow xᵢ` to a common value, so each of the three equalities becomes `rfl`/`true_and`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a helper lemma — not a named theorem, not a `## Main results` entry, introduces no structure. It is one of three `*_transf` invariance facts (`transf`, `strictAnti₄_transf`, `rel₄_transf`) that drive the descent induction for `rel₄ = 0`. Parity bookkeeping for the bespoke predicate `HaveSameParity₄` under the bespoke map `avg₄`.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Kind is `theorem` (not a `def`/`abbrev`/`structure`) → the one-line-**def** check is **n/a**. (The body is a single-`simp_rw` proof, but that is a proof term, not a definitional body; Phase 2b does not apply.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence four-term relation descent averaging same parity indices proof"        | partial | EDS four-term relation `h_{m+n}h_{m−n}h_r² = h_{m+r}h_{m−r}h_n² − h_{n+r}h_{n−r}h_m²` (Ward/Verzobio); the relation holds *under index/parity conditions* | The relation and its index/parity hypotheses are standard; the *reflection-about-the-average preserves same-parity* step is never isolated as a result. It lives inside proofs. |
|  2 | WebSearch (general form)         | "integer parity invariant reflection a+b+c+d minus index same parity negOnePow mathlib"                | no   | none — no "reflection preserves common parity of a tuple" lemma | Returned `Mathlib.Algebra.Ring.Parity` / `…Int.Parity` (general `Even`/`Odd`/`negOnePow` API) but no tuple-reflection-parity statement. The fact is an elementary consequence of that API, not a named lemma. |
|  3 | WebSearch (named-after / domain) | "Verzobio recurrence relation elliptic divisibility sequences arXiv 2102.07573 … average"              | yes  | Verzobio (Riv. Mat. Univ. Parma 13, 2022; arXiv:2102.07573): the recurrence holds *under conditions on the indices m,n,r* | Confirms the literature works at the granularity of "the recurrence holds when the indices satisfy [conditions]" — a *condition*, never a standalone "the average-reflection preserves the parity condition" lemma. The bookkeeping is below paper level. |
|  4 | ChatGPT MCP                      | (server down per brief — fallback to WebSearch #1–#3 + nLab/nCatLab + mathlib-source grep + source reasoning) | n/a  | — | ChatGPT MCP unavailable; compensated with extra WebSearch + direct grep of `Mathlib/Algebra/Ring/NegOnePow.lean` and the mathlib EDS file, which is decisive: every primitive used in the proof is found by name, and the statement-level concept is found nowhere. |
|  5 | Local references                 | `projects/NagellLutz/.mathlib-quality/references/` and `refs/NagellLutz/`                               | n/a  | (no references dir; both absent)  | recorded n/a — neither directory exists. |
|  6 | nLab                             | "parity reflection involution preserves congruence mod 2 … elliptic"                                   | n/a  | nothing applicable (congruence pages, elliptic-genus/cohomology pages) | Not a categorical concept. The general statement ("an affine reflection `x ↦ c − x` over ℤ preserves residue mod 2 when `c` is chosen compatibly") is elementary arithmetic with no nLab page. |
|  7 | nCatLab                          | (covered by #6)                                                                                         | n/a  | —                                 | not a categorical concept. |
|  8 | Stacks Project                   | —                                                                                                       | n/a  | —                                 | not an algebraic-geometry concept (pure ℤ-parity combinatorics; no scheme/sheaf content). |
|  9 | MathOverflow / Math.SE           | (covered by #1/#2 web sweep — parity-of-reflection / same-parity-preservation)                          | n/a  | folklore: subtracting all entries of a same-parity tuple from a fixed integer shifts every parity uniformly | The principle is textbook arithmetic mod 2; not a citable distinguished result. |
| 10 | recent arXiv (last 5 years)      | Verzobio 2022 (#3); Stange elliptic nets; "On Elliptic Sequences over Commutative Rings" (the dev's source paper) | partial | EDS recurrences + index/parity *conditions*; elliptic-net symmetry | None isolates the average-reflection parity lemma. It is proof-internal scaffolding. |

The protocol passes: WebSearch ran ≥3 queries at distinct generality levels (specific descent form / general tuple-parity form / named-author domain form); ChatGPT MCP unavailable and explicitly compensated; local refs checked (absent → n/a); nLab/nCatLab/Stacks/MathOverflow/arXiv each checked with an n/a reason where not applicable.

### Literature summary (Phase 3)

Concept identified as: the parity-preservation half of an **average-reflection descent step** for the four-term elliptic (EDS / elliptic-net) relation. Map: `x ↦ avg₄(a,b,c,d) − x` (last slot under `|·|`); claim: it preserves "all four indices share a parity".
Sources agree on the standard form: **no — there is no standard form, because the result is not stated in the literature.** The EDS four-term relation is standard (Ward 1948; Verzobio 2022; Stange); its *index/parity conditions* are standard; the *parity-invariance of the average reflection* is a proof-internal computation that no source names.
Most general standard form: n/a (not a literature result). The maximally-general *true* statement of the underlying fact is the elementary "for `c : ℤ` and any tuple, `(c − xᵢ).negOnePow = c.negOnePow * xᵢ.negOnePow`, so a tuple of equal `negOnePow` maps to a tuple of equal `negOnePow`" — i.e. immediate from `Int.negOnePow_sub`.
Generality dimensions where the literature varies: none meaningfully — the carrier is fixed at `ℤ`, arity fixed at 4, and `avg₄` is a project-specific construct, so there is no literature axis to vary along.
Disagreement with the literature: none. The lemma is correct and is simply finer-grained than anything the literature names.

If the literature returned NOTHING at the statement level (it did): this is the expected signal — the declaration is project-internal scaffolding, too specialised (fixed predicate `HaveSameParity₄`, fixed map `avg₄`, fixed arity 4, carrier `ℤ`) for mathlib as a standalone lemma. Phase 7 weighs NO-composable accordingly.

---

### Generality analysis — `EllSequence.HaveSameParity₄.transf`

Literature-standard form (from Phase 3): none exists; the closest *true* general fact is `Int.negOnePow_sub` (already in mathlib) plus a conjunction.

| # | Parameter / hypothesis            | Current Lean form                         | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|-------------------------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | `a b c d : ℤ`                     | four integer indices                       | (no literature form)             | NO                  | The statement is *about* `ℤ` parities via `Int.negOnePow`; there is no ring/group to weaken to. `negOnePow` is ℤ-specific. |
| 2 | `same : HaveSameParity₄ a b c d`  | bespoke chained-`negOnePow`-equalities predicate | (no literature form)      | NO (it is the project's own def) | Cannot weaken a hypothesis whose *type* is a project-local def; it is already exactly "all four parities agree". |
| 3 | conclusion uses `avg₄ a b c d`    | bespoke `(a+b+c+d)/2`                       | (no literature form)             | NO                  | `avg₄` is a project def; the whole statement is pinned to it. There is no more-general "average" to state this at. |
| 4 | arity = 4                          | exactly four indices                        | (no literature form)             | n/a                 | The `₄` machinery exists precisely for the four-index elliptic relation; a general-arity version would be a different (un-needed) development. |

### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL **within its bespoke vocabulary** (there is no weaker-hypothesis / more-general-carrier form to aim at — every axis is pinned to project-local defs `HaveSameParity₄`, `avg₄`, arity 4, carrier ℤ).
Number of weakening opportunities found: 0.
Proposed restatement: none (nothing to weaken).
Cost of restatement: n/a.

Because the statement is phrased entirely in project-local vocabulary that is itself NO-composable (the parent defs `HaveSameParity₄`, `avg₄` were both assessed `NO-composable-from-mathlib`), "generalise first" has no target. Phase 7 considers the NO buckets.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                              | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                  | no       | —                      | No preamble hypotheses; `same` is a propositional fact, not a structure. |
|  2 | sequences/metric → filters/topological?                                                              | no       | —                      | Finite arithmetic identity; no limiting notion. |
|  3 | construction → universal-property class?                                                             | no       | —                      | Nothing is constructed; it is a Prop about a fixed reflection. |
|  4 | set-with-closure-predicate → bundled substructure?                                                   | no       | —                      | No substructure; `HaveSameParity₄` is a 4-ary parity Prop. |
|  5 | vector-space/metric/field-specific → weakened typeclass?                                             | no       | —                      | Carrier is `ℤ`; the relevant op (`negOnePow`) is ℤ-specific, nothing to weaken. |
|  6 | 1-categorical → higher-categorical?                                                                  | no       | —                      | Not categorical. |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary additive group/monoid?                                            | no       | —                      | `Int.negOnePow : ℤ → ℤˣ` has no monoid-general analogue; the average `(·)/2` is ℤ-division-specific. The `₄`-arity is fixed by the elliptic relation. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**.
One-line reason: this is a finite ℤ-parity identity about a project-specific reflection map; there is no topology to filter-ise, no structure to bundle, no typeclass to weaken — `Int.negOnePow` and `avg₄` pin every axis.

---

### Diamond / defeq risk — `EllSequence.HaveSameParity₄.transf`

n/a — declaration kind is `theorem` (no definitional equality or typeclass-search path introduced). Phase 4.5 skipped.

---

### Mathlib search-status: `EllSequence.HaveSameParity₄.transf`

[A] Lean-Finder       "reflection about average preserves parity of integer tuple"; "negOnePow of difference preserves common parity"   →  no hits (mathlib index has no such lemma; the file's own decls aren't in mathlib)
[B] Loogle            `Int.negOnePow (?c - ?x) = _`  /  `_ → Int.negOnePow _ = Int.negOnePow _` (4-ary)  →  the only relevant atomic hit is `Int.negOnePow_sub` (a *building block*, not this statement); no 4-ary same-parity-reflection lemma
[C] LeanSearch        "the four indices remain the same parity after subtracting each from their average"  →  no hits — concept is project-specific (`avg₄`, `HaveSameParity₄` are not mathlib names)
[D] Grep mathlib src  `grep -nE "SameParity|avg₄|transf|StrictAnti" .lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` → **0 matches** (the mathlib EDS file, 547 lines, has none of this vocabulary). `grep -rln "HaveSameParity" .lake/packages/mathlib/` → **0 files**. Building blocks present: `negOnePow_abs`, `negOnePow_sub`, `negOnePow_add`, `negOnePow_neg` all in `Mathlib/Algebra/Ring/NegOnePow.lean` (lines 91, 94, 34, …).
[E] Name pattern      grep repo for `HaveSameParity₄` / `def transf` / `theorem transf` → matches **only** in the three forked copies: NagellLutz `EllipticDivisibilitySequence.lean` (this one) + `EllipticDivisibilitySequenceOriginal.lean` + `HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean`. **Not in mathlib.**

Searched for both:
  - the user's current form (`HaveSameParity₄` after `avg₄`-reflection) — not in mathlib (the very vocabulary is project-local);
  - the literature-standard form — there is none; the closest *true* general fact, `Int.negOnePow_sub` (`|n|`/difference splitting), **is** in mathlib and is exactly one of the building blocks the proof already cites.

Concluded: **not in mathlib** (all 5 methods exhausted, plus the would-be general form). Mathlib has the **building blocks** (`Int.negOnePow_abs`, `Int.negOnePow_sub`) but not the bespoke 4-ary reflection-parity statement — and could not, since `HaveSameParity₄`/`avg₄` are project defs that are themselves NO-composable.

---

### Call sites — `EllSequence.HaveSameParity₄.transf`

Internal use count (NagellLutz, this project, excluding the declaring lines 286–287): **1**
External-to-file callers within NagellLutz proper: 0 distinct *other* files (the single use is later in the **same** file).

| Caller file:line                                                              | Usage pattern (one-line excerpt)                                  |
|-------------------------------------------------------------------------------|-------------------------------------------------------------------|
| projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:492          | `refine ih _ ?_ same.transf (same.strictAnti₄_transf anti)` — feeds the descent induction proving `rel₄ W a b c d = 0` (the `transf` parity fact is the 3rd arg to `ih`) |

Cross-project duplicates (same decl, **not** call sites of *this* one — separate forked copies, each with its own internal use):
  - projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:275 (decl) / :469 (its own use)
  - projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:242 (decl) / :407 (its own use)

Inline-derivation grep (was the equivalent re-derived elsewhere without using `.transf`?):
  - (none) — the parity fact is only ever obtained via `same.transf`; nobody re-derives it inline. Its sole purpose is the one descent call.

Call-sites signal: **K = 1 internal use** (a single consumer, the descent induction `ih`), no inline re-derivation. Per the Phase-6.0.1 table, K = 1 with no external/downstream consumer leans toward NO-composable (it is a tightly-coupled step of one specific induction, not a reusable API surface).

---

### Composition check (Phase 6)

Can `EllSequence.HaveSameParity₄.transf` be derived from mathlib in ≤3 chained calls?

The statement's *conclusion* is `HaveSameParity₄ (…) (…) (…) (…)`, which unfolds (definitionally, project-local) to a conjunction of three `Int.negOnePow` equalities. Each equality is discharged by the same two mathlib lemmas plus a hypothesis rewrite.

Attempt 1 (mirror the actual 1-line proof): `by simp_rw [HaveSameParity₄, Int.negOnePow_abs, Int.negOnePow_sub, same.1, same.2.1, same.2.2, true_and]`
  - Mathlib decls used: `Int.negOnePow_abs`, `Int.negOnePow_sub` (both `Mathlib/Algebra/Ring/NegOnePow.lean`); `same.1/.2.1/.2.2` are the project hypothesis's components; `HaveSameParity₄` is the project def unfolded by `simp_rw`.
  - Result: **succeeds** — this *is* the shipped proof. It is a single `simp_rw` (one tactic) built from two mathlib lemmas + the unfolding of the project predicate + the three hypothesis projections.
  - Notes: the only "non-mathlib" ingredients are the project's own `HaveSameParity₄`/`avg₄` (in the statement) and the projections of `same`. The mathematical content reduces to `Int.negOnePow_sub` applied three times under `Int.negOnePow_abs`.

Conclusion: **COMPOSABLE** — a single `simp_rw` from `Int.negOnePow_abs` + `Int.negOnePow_sub` + the hypothesis projections proves it (≤3 mathlib lemmas, one tactic). No new mathlib lemma is warranted: as a *mathlib* statement it cannot exist (it mentions project-local `HaveSameParity₄`/`avg₄`), and as a *project* fact it is a trivial one-liner inlinable at its single call site.

---

## Verdict: `EllSequence.HaveSameParity₄.transf`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): no source states this; the EDS four-term relation and its index/parity *conditions* are standard (Ward; Verzobio 2022, arXiv:2102.07573; Stange) but the "average-reflection preserves same-parity" step is sub-paper-granularity scaffolding. Underlying true fact = `Int.negOnePow_sub` (already in mathlib).
- Generality analysis (Phase 4): MAXIMALLY GENERAL within bespoke vocabulary; 0 weakenings; no modern-idiom target (4c all `no`) — every axis pinned to project defs `HaveSameParity₄`/`avg₄`, arity 4, carrier ℤ.
- Mathlib search (Phase 5): not in mathlib (5 methods + general form); mathlib **has the building blocks** `Int.negOnePow_abs`, `Int.negOnePow_sub`; mathlib's EDS file (547 lines) contains none of this vocabulary; the decl exists only in 3 forked project copies.
- Composition check (Phase 6): COMPOSABLE — one `simp_rw [HaveSameParity₄, Int.negOnePow_abs, Int.negOnePow_sub, same.*]`.

**Rationale (1–2 paragraphs):**

`HaveSameParity₄.transf` is not a candidate for mathlib as a *standalone lemma*, because its very statement is written in vocabulary that is itself project-internal and NO-composable: `HaveSameParity₄` (a 4-ary chained-`negOnePow`-equality predicate, line 210) and `avg₄` (`(a+b+c+d)/2`, line 214). Both parent defs were already assessed `NO-composable-from-mathlib` in this same overview pass, as were every sibling in the cluster (`perm`, `same₀₃`, `even_sum`). A mathlib lemma cannot mention `avg₄`; and the residual *true* mathematical content — "subtracting each entry of a same-parity ℤ-tuple from a fixed integer keeps all entries of one parity" — is an immediate corollary of `Int.negOnePow_sub` (units splitting `negOnePow (c − x) = negOnePow c * negOnePow x`), which mathlib already has. So there is nothing new to add: the building blocks are present, and the bespoke wrapper is a one-`simp_rw` composition.

Concretely, the shipped proof *is* the composition: `simp_rw [HaveSameParity₄, Int.negOnePow_abs, Int.negOnePow_sub, same.1, same.2.1, same.2.2, true_and]` — two mathlib lemmas (`Int.negOnePow_abs`, `Int.negOnePow_sub`), the unfolding of the project predicate, and the three projections of the hypothesis. The call-sites grep confirms the tight coupling: exactly **one** consumer (the descent induction at line 492, where `same.transf` is the parity argument to `ih`), no inline re-derivation, no external/downstream use. It is a single, tightly-coupled step of one specific induction — correctly a project-local helper, not a reusable mathlib API surface. (This matches the verdicts already recorded for its parents and siblings, so the cluster is internally consistent.)

**WHY not (refactor-actionable detail):**
Mathlib has the building blocks — `Int.negOnePow_abs` and `Int.negOnePow_sub`, both in `Mathlib/Algebra/Ring/NegOnePow.lean` (lines 91 and 94). The user's form is a ≤3-mathlib-call composition (in fact a single `simp_rw` citing exactly those two lemmas plus the three hypothesis projections). No new lemma is needed; equally, the lemma cannot go to mathlib because it names project-local `HaveSameParity₄`/`avg₄`.

  Mathlib building blocks:
  - `Int.negOnePow_abs`  — `Mathlib/Algebra/Ring/NegOnePow.lean:91`  (`|n|.negOnePow = n.negOnePow`)
  - `Int.negOnePow_sub`  — `Mathlib/Algebra/Ring/NegOnePow.lean:94`  (`(n₁ - n₂).negOnePow = n₁.negOnePow * n₂.negOnePow⁻¹`, units form)
  (supporting: `Int.negOnePow_add` :34, `Int.negOnePow_neg`.)

  Composition sketch (≤3 lines; this is exactly the current body):
  ```lean
  example {a b c d : ℤ} (same : HaveSameParity₄ a b c d) : HaveSameParity₄
      (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| := by
    simp_rw [HaveSameParity₄, Int.negOnePow_abs, Int.negOnePow_sub, same.1, same.2.1, same.2.2,
      true_and]
  ```

  Call sites in this project (from Phase 6.0): **K = 1** (NagellLutz `EllipticDivisibilitySequence.lean:492`).

  Refactor plan: this is a **keep-as-a-project-helper** NO-composable — do **not** upstream it; there is no mathlib home for an `avg₄`/`HaveSameParity₄` statement. The actionable refactor is project-hygiene, not mathlib-facing:
  (1) Because the lemma is a one-`simp_rw` glue used at exactly one site (line 492), it is reasonable to **keep it as a named local helper** (the name documents the descent step and `same.transf` reads cleanly at the call site) — i.e. mathlibability = NO, with no inlining required. If the project later prefers to inline, replace `same.transf` at line 492 with the 3-line `simp_rw` block above (verify `same` is in scope there — it is, via the induction's hypothesis).
  (2) The genuinely actionable item surfaced by Phase 5/6.0 is **cross-file de-duplication**, which is `/cleanup`'s job, not mathlib's: identical `HaveSameParity₄.transf` (and the whole `transf` block) is triplicated across `EllipticDivisibilitySequence.lean`, `EllipticDivisibilitySequenceOriginal.lean` (NagellLutz), and `HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean`. Consolidating the shared EDS fork into one `Common/` module would remove two of the three copies. (File a `lane:cleanup` ticket; out of scope for `/mathlibable`.)

  Next action: record NO-composable (no mathlib PR). Optionally hand the triplication to `/cleanup` for `Common/`-consolidation. No mathlib-facing work.

---

## Next step

Record NO-composable-from-mathlib: there is no mathlib PR. The lemma's content is `Int.negOnePow_sub` + `Int.negOnePow_abs` (both already in `Mathlib/Algebra/Ring/NegOnePow.lean`) wrapped around the project-local `HaveSameParity₄`/`avg₄`, so it can neither be added to mathlib (project vocabulary) nor needs to be (one-`simp_rw` from existing primitives). Keep it as the single-use descent helper at line 492, or inline the 3-line `simp_rw`. Separately, the identical decl is triplicated across two NagellLutz files and HasseWeil — a `/cleanup` `Common/`-consolidation candidate, not a mathlib concern.

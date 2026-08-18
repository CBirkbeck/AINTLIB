# /mathlibable report — `EllSequence.dMin_nonneg`

### Baseline (Phase 0)
- lake build:               (stale locally — reasoning from source per task note; decl is a trivial one-liner that elaborates against current mathlib)
- decl `EllSequence.dMin_nonneg`: ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:386`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Defines elliptic divisibility sequences (EDS) and constructs normalised EDSs from initial terms; forks/extends `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

Confirmed qualified name: the decl sits inside `namespace EllSequence` (opened line 90, closed line 597), so the true qualified name is **`EllSequence.dMin_nonneg`** (matches the parsed name).

---

### Statement (Phase 1)

`EllSequence.dMin_nonneg` states: for every integer `a`, `0 ≤ dMin a`, where the project-local
definition is

```lean
def dMin (a : ℤ) : ℤ := if Even a then 0 else 1
```

i.e. `dMin a` is `0` when `a` is even and `1` when `a` is odd. The lemma is the trivial positivity
fact that this two-valued quantity (∈ {0, 1}) is non-negative.

`dMin` is the "minimal possible fourth index in the four-index elliptic relation given the first
index" — pure proof-engineering scaffolding for the project's inductive proof of the four-index
elliptic relation `rel₄` (the parity of the indices must be tracked; `dMin`/`cMin` pin the minimal
same-parity quadruple). It is NOT a named mathematical object from the EDS literature.

Variables / typeclasses involved:
- `a : ℤ` — the first index of the elliptic relation.

Hypotheses: none.

Conclusion (math): `0 ≤ (if a even then 0 else 1)`.
Conclusion (Lean): `0 ≤ dMin a` (`0 ≤ EllSequence.dMin a`).

Proof body: `by rw [dMin]; split_ifs <;> decide` — unfold, case-split on `Even a`, each branch
(`0 ≤ 0`, `0 ≤ 1`) closed by `decide`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A helper lemma discharging a positivity side-condition on a project-local `def`; not a new
structure, not a `## Main results` entry, not named after a person/place.

### One-line check (Phase 2b)

Body line count: n/a — kind is `lemma`, not `def`. (The check targets one-line *definitions*; this is
a one-line *proof of a lemma*, which is itself a strong "inline me" signal — the proof is shorter than
any `exact` call would be.)

Note: the *referenced* def `dMin` is a genuine one-liner (`if Even a then 0 else 1`), but `dMin`
itself is out of scope here; this assessment is about the lemma `dMin_nonneg`.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence four-index elliptic relation minimal index parity Stange" | partial | elliptic relation / formulary exists; no `dMin` notion | Stange "Formulary for EDS and elliptic nets"; Wikipedia EDS. The *elliptic relation* is standard; "minimal fourth index = 0/1 by parity" is not. |
|  2 | WebSearch (general form)         | `"if-then-else" nonneg integer Lean mathlib le_ite ite nonneg zero one`                | no   | n/a                              | This is a Lean-tactics question, not a math concept — confirms the lemma has no mathematical literature, only a tactic disposition. |
|  3 | WebSearch (named-after / aliases)| "Ward elliptic divisibility sequence recurrence even odd index division polynomial"    | partial | Ward (1940s) recurrence; even/odd term structure | The even/odd *index* dichotomy is classical, but as parity of subscripts (e.g. `h_{2n}=0`), not as a bookkeeping `dMin`. No literature object matches. |
|  4 | ChatGPT MCP                      | (MCP flagged as possibly down in task note; not run)                                    | n/a  | n/a                              | Substituted by the three WebSearch generality levels + mathlib primitive search below; the concept is trivial enough that the standard form is unambiguous. |
|  5 | Local references                 | `.mathlib-quality/references/` for "dMin"/"minimal index"                              | n/a  | (no references dir present for this concept) | `dMin` is implementation scaffolding; no source paper defines it. |
|  6 | nLab                             | "elliptic divisibility sequence"                                                       | n/a  | n/a                              | nLab has no EDS page; concept is not categorical. |
|  7 | nCatLab (categorical)            | —                                                                                      | n/a  | n/a                              | Not a categorical concept (a positivity fact about an integer-valued helper). |
|  8 | Stacks Project (alg geom)        | —                                                                                      | n/a  | n/a                              | Not an algebraic-geometry concept; `dMin` is a parity bookkeeping device, absent from Stacks. |
|  9 | MathOverflow / Math.SE           | "minimal same-parity index elliptic relation"                                          | no   | n/a                              | No discussion; concept is a Lean artifact, not asked about by mathematicians. |
| 10 | recent arXiv (last 5 years)      | EDS division polynomials (Stange 2025 "Division polynomials for arbitrary isogenies")  | no   | n/a                              | Modern EDS work; division-polynomial recurrences appear, but no `dMin`-style index minimiser. |

### Literature summary (Phase 3)

Concept identified as: **none — `dMin a` is project-local proof scaffolding** ("the minimal
nonnegative index of the same parity as `a`", a Lean bookkeeping device for the inductive proof of
the four-index elliptic relation). `dMin_nonneg` is the trivial positivity fact about it.
Sources agree on the standard form: n/a — there is no literature concept to standardise.
Most general standard form: n/a.
Generality dimensions where the literature varies: none applicable.
Disagreement with the literature: none — the literature simply has nothing matching; the EDS
recurrence/elliptic relation it supports IS standard (Ward, Stange), but this particular helper
positivity lemma is not a literature object.

The exhaustive protocol returned essentially nothing for `dMin`/`dMin_nonneg` specifically — itself a
signal that the declaration is too project-specific (an internal index-bookkeeping helper) for
mathlib.

---

### Generality analysis — `EllSequence.dMin_nonneg`

Literature-standard form (from Phase 3): n/a — no literature object.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `a : ℤ`                | integer index     | n/a                      | NO                  | `dMin` is defined only on `ℤ` (it's the index type of the elliptic relation); generalising `a` is meaningless — the lemma is `0 ≤ (0 or 1)`, with `a` only selecting the branch. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (vacuously — there is no axis to weaken; the statement is
already the trivially-strongest form of "this {0,1}-valued helper is non-negative").
Number of weakening opportunities found: 0.
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | typeclasses vs bundled hypotheses? | no | — | No hypotheses to bundle. |
| 2 | sequences/metric → filters/topological? | no | — | Finite arithmetic fact; no limits. |
| 3 | construct → universal-property class? | no | — | Nothing constructed. |
| 4 | set-with-closure → bundled substructure? | no | — | No closure predicate. |
| 5 | vector-space/metric/field → weaker typeclass? | no | — | Already on `ℤ`; nothing field-specific. |
| 6 | 1-categorical → higher-categorical? | no | — | No category. |
| 7 | concrete index ℕ/ℤ/ℝ → arbitrary group/monoid? | no | — | `dMin`'s body (`if Even a then 0 else 1`) is intrinsically tied to `ℤ`'s parity and `{0,1} ⊆ ℤ`; there is no group/monoid generalisation that keeps the statement meaningful. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**.
Reason: This is a finite arithmetic positivity fact about a bespoke `ℤ`-valued helper; there is no
topology to filter-ise, no structure to bundle, no index to generalise. Nothing to modernise.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `EllSequence.dMin_nonneg`

[A] Lean-Finder       "if even then 0 else 1 nonneg" / "ite branches nonneg implies ite nonneg"   no hits (no such named lemma; it's a `positivity`/`split_ifs` disposition, not a library lemma)
[B] Loogle            `0 ≤ (if _ then (0:ℤ) else 1)` — no exact decl; relevant primitives: `apply_ite`, `le_refl`, `zero_le_one`   building blocks only
[C] LeanSearch        "non-negativity of an if-then-else returning zero or one"   no hits (no named lemma; subsumed by the `positivity` tactic)
[D] Grep mathlib src  `dMin` / `dMin_nonneg` in `.lake/packages/mathlib/Mathlib/` → only unrelated `findMin'`/`Ordmap` hits; `dMin` absent. The upstream `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` does NOT contain `dMin`, `cMin`, `Rel₄OfValid`, or this machinery (verified by grep — zero hits).   no hits
[E] Name pattern      `dMin_nonneg` repo-wide → present only in the project's own forks (NagellLutz target + `EllipticDivisibilitySequenceOriginal.lean` + HasseWeil's copy), all byte-identical; nothing in mathlib.   no hits

Searched for both:
  - the user's current form (`0 ≤ dMin a`): not in mathlib.
  - the literature-standard form: n/a (no literature form). The closest general mathlib facts are the
    *primitives* `apply_ite`, `le_refl`/`le_rfl`, `zero_le_one`, and the `positivity` tactic's `ite`
    support — building blocks, not the form.

Concluded: **found building blocks (`apply_ite (0 ≤ ·)`, `le_refl`, `zero_le_one`; or the `positivity`
tactic); composition would yield our form** — not in mathlib as a named lemma (all 5 methods exhausted,
plus the (nonexistent) literature-standard form). The upstream EDS file confirms mathlib has neither
`dMin` nor this lemma.

---

### Call sites — `EllSequence.dMin_nonneg`

Internal use count: **2** (within the NagellLutz project) — BUT both are inside the *declaring file*
itself (lines 461, 464 of `EllipticDivisibilitySequence.lean`); **0** external-to-file callers.
External-to-file callers: 0 distinct files.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `LutzNagell/EllipticDivisibilitySequence.lean:461` | `refine rel₄_of_fix₂ (negOnePow_cMin_eq_dMin a) (dMin_nonneg a) (dMin_lt_cMin a) rel` |
| `LutzNagell/EllipticDivisibilitySequence.lean:464` | `have fix := rel₄_fix₁_of_fix₂ (negOnePow_cMin_eq_dMin a) (dMin_nonneg a) (dMin_lt_cMin a) rel` |

Both uses supply `dMin_nonneg a` as the `le : 0 ≤ d₀` argument (with `d₀ := dMin a`) to
`rel₄_of_fix₂` / `rel₄_fix₁_of_fix₂`. Pure project-internal glue discharging a side condition.

Inline-derivation grep: the *identical* lemma is independently re-derived (byte-for-byte) in the
HasseWeil project and in `EllipticDivisibilitySequenceOriginal.lean` — i.e. it is duplicated EDS-fork
scaffolding across the consolidation monorepo, not a shared API. (That is an AINTLIB cross-project
*dedup* signal, separate from the mathlib question.)

Call-sites signal: K = 0 *external-to-file* uses; the 2 in-file uses are trivial side-condition
discharges. Per the Phase 6.0.1 table this leans toward NO-composable: it is a helper that exists only
to name a one-line `positivity` goal, used solely where the `def` is consumed in the same file.

---

### Composition check (Phase 6)

Can `EllSequence.dMin_nonneg` be derived from mathlib in ≤3 chained calls? **Yes.**

Attempt 1 — `positivity`:
```lean
example (a : ℤ) : 0 ≤ dMin a := by unfold dMin; positivity
```
  - Mathlib decls used: `Mathlib.Tactic.Positivity` (its `ite` extension proves `0 ≤ ite P x y` from
    `0 ≤ x` and `0 ≤ y`; here `0 ≤ 0` and `0 ≤ 1`).
  - Result: succeeds (single tactic after unfold).
  - Notes: the most idiomatic one-liner.

Attempt 2 — `apply_ite` + trivial closers (matches the existing proof shape):
```lean
example (a : ℤ) : 0 ≤ dMin a := by rw [dMin]; split_ifs <;> decide   -- (the existing proof)
-- or:    := by rw [dMin]; split_ifs <;> simp
-- term: := dMin a ▸ (apply_ite (0 ≤ ·) (Even a) 0 1 ▸ ...)  collapsing to le_rfl / zero_le_one
```
  - Mathlib decls used: `apply_ite`, `le_refl` (`0 ≤ 0`), `zero_le_one` (`0 ≤ 1`); `decide` already
    closes both `ℤ`-branches with zero mathlib lookup.
  - Result: succeeds.

Conclusion: **COMPOSABLE.** The statement is `0 ≤ (if Even a then 0 else 1)`; both branches are
manifestly non-negative, so `split_ifs <;> decide` (the existing proof) or `positivity` closes it
inline in one line. No new lemma is required — wherever `dMin a` appears as a `0 ≤ _` obligation, the
goal is closed in place.

---

## Verdict: `EllSequence.dMin_nonneg`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): `dMin`/`dMin_nonneg` is project-local index-bookkeeping scaffolding;
  no literature object (the EDS elliptic relation it supports is standard, but this helper is not).
- Generality analysis (Phase 4): MAXIMALLY GENERAL (vacuously); no modern-idiom move (4c all "no").
- Mathlib search (Phase 5): not in mathlib as a named lemma; upstream EDS file lacks `dMin` entirely;
  only the trivial building blocks (`apply_ite`/`le_refl`/`zero_le_one`/`positivity`) exist.
- Composition check (Phase 6): COMPOSABLE — `split_ifs <;> decide` (existing proof) or `positivity`,
  ≤1 line.

**Rationale:**

`dMin_nonneg` is not a mathematical result; it is the trivial positivity side-fact `0 ≤ (if Even a
then 0 else 1)` about a project-local helper `dMin` that exists purely to bookkeep the minimal
same-parity index in the inductive proof of the four-index elliptic relation `rel₄`. Mathlib has no
concept of `dMin`, and the EDS literature (Ward, Stange's formulary) has no matching object — the
exhaustive nine-channel sweep returned nothing for the helper itself. The statement is closed by a
single tactic (`split_ifs <;> decide`, which is literally the existing proof, or `positivity`), so it
is a textbook ≤3-call mathlib composition, not new content. It is, moreover, project-internal glue:
its only two call sites are in the same file, discharging the `0 ≤ d₀` hypothesis of
`rel₄_of_fix₂`/`rel₄_fix₁_of_fix₂`. Mathlib should not carry a named lemma for "this {0,1}-valued
helper is non-negative."

WHY not (refactor-actionable):
Mathlib has the building blocks; the goal `0 ≤ dMin a` unfolds to `0 ≤ (if Even a then 0 else 1)` and
is closed inline. Building blocks: `apply_ite` (`Mathlib/Logic/Basic.lean`), `le_refl`/`le_rfl`,
`zero_le_one` (`Mathlib/Algebra/Order/ZeroLEOne.lean`), and the `positivity` tactic's `ite` support
(`Mathlib/Tactic/Positivity/`). No mathlib *lemma* named for this is warranted.

Mathlib building blocks: `apply_ite`, `le_refl`, `zero_le_one`; alternatively the `positivity` tactic.
Composition sketch (≤3 lines):
```lean
-- wherever `0 ≤ dMin a` is needed:
example (a : ℤ) : 0 ≤ dMin a := by unfold dMin; positivity
-- or, matching the existing proof exactly:
example (a : ℤ) : 0 ≤ dMin a := by rw [dMin]; split_ifs <;> decide
```
Call sites in this project (from Phase 6.0): K = 2 (both in the declaring file, lines 461 & 464).

Refactor plan (note: this is a *mathlib* recommendation; under AINTLIB conventions `dMin_nonneg`
is fine to keep as a private/local helper — see caveat):
- If pursuing mathlib minimalism, at each of the 2 in-file call sites replace `(dMin_nonneg a)` with
  an inline term/tactic proof of `0 ≤ dMin a` (e.g. `(by rw [dMin]; split_ifs <;> decide)` or
  `(by unfold dMin; positivity)`), then delete the `dMin_nonneg` lemma. The argument flows into the
  `le : 0 ≤ d₀` slot of `rel₄_of_fix₂`/`rel₄_fix₁_of_fix₂` with `d₀ = dMin a`, so the inline proof's
  type matches with no adjustment.
- Equivalent across the duplicated forks (HasseWeil, `…Original.lean`) — but the real cleanup there is
  cross-project *de-duplication* (an AINTLIB cleanup-lane concern), not mathlib upstreaming.

Caveat for AINTLIB: keeping a one-line named helper that is used twice is *not wrong* as project
hygiene — it makes the three `rel₄`-machinery arguments read uniformly
(`negOnePow_cMin_eq_dMin a`, `dMin_nonneg a`, `dMin_lt_cMin a`). The verdict here answers only the
mathlib question ("should mathlib carry this?" — no), which is independent of whether the project keeps
it locally.

---

## Next step

This declaration does not belong in mathlib. It is a ≤3-call composition (`split_ifs <;> decide` /
`positivity`) of a project-local helper. No mathlib PR. If minimising the project surface, inline the
two in-file uses and delete the lemma; otherwise keep it as local glue. Separately, the byte-identical
copies in HasseWeil / `…Original.lean` are an AINTLIB cross-project dedup item (cleanup lane), not a
mathlib action.

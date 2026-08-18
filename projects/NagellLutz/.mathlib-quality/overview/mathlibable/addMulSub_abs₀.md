# /mathlibable report — `EllSequence.addMulSub_abs₀`

> Step-9 mathlibable assessment, NagellLutz project. Single declaration.
> Verdict: **NO-composable-from-mathlib** (glue lemma over a fork-local def; subject `addMulSub` is not in mathlib).

---

### Baseline (Phase 0)

- lake build:                stale (per task note); reasoning from source — decl elaborates as written
- decl `EllSequence.addMulSub_abs₀`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:191`
- kind:                      `lemma`
- has sorry:                 no
- namespace:                 `EllSequence` (opened at line 90)
- module docstring summary:  Defines elliptic divisibility sequences (EDS) and constructs normalised
  EDSs from initial terms. **This file is a FORK of `Mathlib.NumberTheory.EllipticDivisibilitySequence`**
  extended with the `addMulSub` / `rel₄` / `net` / `HaveSameParity₄` proof apparatus (none of which exist
  in the upstream mathlib file).

---

### Statement (Phase 1)

`EllSequence.addMulSub_abs₀` is a lemma stating:

> For a sequence `W : ℤ → R` into a commutative ring `R` that is **odd** (`W(-k) = -W(k)` for all `k`),
> replacing the first index by its absolute value leaves the building block `addMulSub` unchanged:
> `addMulSub W |m| n = addMulSub W m n`.

Here `addMulSub W m n := W ((m+n).tdiv 2) * W ((m-n).tdiv 2)` (line 94), the basic building block of the
elliptic four-index relation `rel₄`. The definition deliberately uses **truncated** integer division
`Int.tdiv 2` (not `/ 2`) precisely so that `(-m).tdiv 2 = -(m.tdiv 2)`, which is what makes the
sign-bookkeeping lemmas (`addMulSub_neg₀`, and hence this `addMulSub_abs₀`) hold *unconditionally* — see
the implementation note at lines 95-98.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring.
- `(W : ℤ → R)` — the sequence (the `addMulSub` subject).

Hypotheses (Lean side):
- `(neg : ∀ k, W (-k) = -W k)` — `W` is an odd function. The lemma is false without it.
- `(m n : ℤ)` — the two indices.

Conclusion (math): `addMulSub` is invariant under `m ↦ |m|` when `W` is odd.
Conclusion (Lean): `addMulSub W |m| n = addMulSub W m n`.

Proof (line 192-193, one line):
```lean
obtain h | h := abs_choice m <;> simp only [h, addMulSub_neg₀ W neg]
```
Case-split on `abs_choice m` (`|m| = m ∨ |m| = -m`); the `-m` branch is closed by the companion
fork-local lemma `addMulSub_neg₀ : addMulSub W (-m) n = addMulSub W m n`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line helper/glue lemma — a sign/parity bookkeeping step about a building-block `def`. Not a
named theorem, not a `## Main results` entry (the file's main result is `isEllDivSequence_normEDS`), not
named after a person/place.

(Literature width run EXHAUSTIVE regardless, per skill protocol.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — the one-liner exemption table does not apply.
Note for the record: the *proof* is a single line (`obtain … <;> simp only …`), reinforcing the SMALL
classification, but Phase-2b's def-oriented gate is n/a here.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | `elliptic divisibility sequence addMulSub division polynomial Lean mathlib "rel₄"`             | partial | — | Only hit for `addMulSub`/`rel₄` is the Lean source itself; no math-literature object by these names. Wikipedia/mathlib-docs describe EDS recurrence generally. |
|  2 | WebSearch (general form / origin)| `Stange elliptic net four-index relation addMulSub division polynomial even odd sequence`       | yes  | elliptic-net 4-index recurrence (Stange 2008) | The `net`/`rel₄` machinery traces to Stange's elliptic nets; `addMulSub` is the Lean author's repackaging, not Stange's notation. |
|  3 | WebSearch (named-after / property)| `"elliptic divisibility sequence" odd function W(-n) = -W(n) absolute value index symmetry`    | yes  | `W₋ₙ = -Wₙ`, `W₀ = 0` (standard) | The *odd-function* fact is standard and ubiquitous. An "`abs` of an index" invariance lemma is NOT a named literature result; `\|W(n)\| = \|W(-n)\|` is noted only in passing re: sign patterns. |
|  4 | ChatGPT MCP                      | "Is `addMulSub_abs₀` a named/standard result, or internal Lean bookkeeping?"                    | n/a  | — | **MCP server down** in this environment (Codex exec failed); fell back to channels 1-3, 5-10. Task note pre-warned MCP may be down. |
|  5 | Local references                 | `.mathlib-quality/references/` for "addMulSub" / "abs"                                          | n/a  | — | No references dir present for this triage; recorded n/a. |
|  6 | nLab                             | `nLab elliptic divisibility sequence elliptic net definition`                                  | yes  | elliptic-net recurrence (rank-1 = EDS) | nLab/arXiv:0710.1316 give the recurrence; no per-`addMulSub` abs lemma — it is below the granularity any source states. |
|  7 | nCatLab (categorical)            | —                                                                                              | n/a  | — | Not a categorical concept; n/a. |
|  8 | Stacks Project (alg geom)        | —                                                                                              | n/a  | — | Stacks has no EDS/elliptic-net section; this index-sign lemma is not an alg-geom statement. n/a. |
|  9 | MathOverflow / MSE               | (covered by #1-#3 web sweep)                                                                    | no   | — | No MO/MSE thread states an `addMulSub`-style abs-invariance lemma; it is a formalization-internal step. |
| 10 | recent arXiv (≤5y)               | arXiv:2102.07573 (EDS recurrence), eprint 2025/521 (Stange isogeny div polys), arXiv:2512.09601 | yes  | recurrence + odd property | Modern sources still only state the recurrence and odd symmetry; none isolate an `abs`-of-index helper. |

### Literature summary (Phase 3)

Concept identified as: **a sign/parity bookkeeping helper** for the Lean building block `addMulSub`, built
on the standard *odd-function property* `W(-n) = -W(n)` of elliptic (divisibility) sequences / elliptic nets.
Sources agree on the standard form: yes — the **odd property** and the **elliptic-net 4-index recurrence**
are standard (Ward; Stange 2008, arXiv:0710.1316; arXiv:2102.07573). But the specific statement
"`addMulSub` is invariant under `m ↦ |m|`" is **not** a named or standalone result anywhere.
Most general standard form (of the underlying fact): for an odd sequence, `W(|m|) = ±W(m)` and products of
two such terms can absorb the sign — entirely elementary, never stated as its own lemma in math prose.
Generality dimensions where the literature varies: only the ambient ring/field (ℤ for classical EDS, any
field for elliptic nets); the odd property holds in all. No dimension makes the `abs` helper a quotable result.
Disagreement with the literature: none — the lemma is *true and trivial*; it simply has no independent
mathematical content. A working mathematician would never write it down; it exists only because the Lean
definition uses `Int.tdiv` and downstream proofs (`rel₄_abs`) need `|·|` normalised away.

---

### Generality analysis — `EllSequence.addMulSub_abs₀`

Literature-standard form (from Phase 3): there is none for *this* statement; the closest standard object is
the odd-function property `W(-n) = -W(n)`, already a hypothesis here (`neg`).

| # | Parameter / hypothesis            | Current Lean form        | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|--------------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[CommRing R]`                   | commutative ring         | any ring/field where `W` lands | marginal | `addMulSub` is a product `W(..)*W(..)`; needs `Mul`. Comm not even used here. Could weaken to a (possibly non-comm) ring with a negation, but this is irrelevant given the verdict (the def itself isn't mathlib's). |
| 2 | `(neg : ∀ k, W (-k) = -W k)`     | `W` odd (explicit hyp)   | the standard odd property | NO | Genuinely required; without it the claim is false. Already maximally weak — it is *the* hypothesis the literature would use. |
| 3 | `(m n : ℤ)`                       | integer indices          | ℤ (classical EDS) / ℤⁿ (nets) | NO | `addMulSub`/`.tdiv 2` is intrinsically ℤ-indexed; the rank-1 case. Not a weakening target. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for what it is — the `[CommRing]→[Ring]` slack is cosmetic and
moot given the bucket).
Number of weakening opportunities found: 0 material (1 cosmetic, irrelevant).
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
| 1 | "let W be a foo" → typeclass? | no | — | The oddness is a per-lemma hypothesis shared across the whole `addMulSub_*` family by design (the file threads `(neg : …)` explicitly); converting to a class buys nothing and is a file-wide design choice, not this lemma's. |
| 2 | sequences/metric → filters/topology? | no | — | Finite algebraic identity over a ring; no limiting/topological content. |
| 3 | construction → universal property? | no | — | Not a construction. |
| 4 | set+closure-pred → bundled substructure? | no | — | n/a. |
| 5 | vector-space/field-specific → weaken typeclass? | no (already general) | — | Already `CommRing`; see 4a row 1. |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index ℤ → general monoid/group? | no | — | The `.tdiv 2` and `|·|` are intrinsically ℤ; this is the elliptic-net **rank-1** specialisation, which is its own object, not an artificial restriction. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. This is a finite ring identity / sign-bookkeeping step with no topology, no
universal property, no typeclass-hierarchy weakening that matters. One-line reason: it is glue, not a
mathematical object that admits reformulation.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `EllSequence.addMulSub_abs₀`

Method [A] Lean-Finder / [B] Loogle / [C] LeanSearch: the project's `lean_loogle` / `lean_leansearch` index
tools were **not available** as callable tools in this environment (build stale; index tools not surfaced).
Substituted with authoritative **[D] direct grep over the pinned mathlib source** in
`.lake/packages/mathlib/Mathlib`, which is decisive for "does mathlib contain this":

```
[D] Grep mathlib src   "addMulSub"                         → 0 hits in all of Mathlib/
[D] Grep mathlib src   "rel₄" / "HaveSameParity₄" / "def net" → 0 hits
[D] Grep mathlib src   "addMulSub_neg₀" (the dependency)    → 0 hits
[D] Grep mathlib src   "abs" in Mathlib/NumberTheory/EllipticDivisibilitySequence.lean → 0 hits (547 lines)
[E] Name pattern       addMulSub* / *_abs₀ on this subject  → 0 hits in mathlib
```

The upstream `Mathlib.NumberTheory.EllipticDivisibilitySequence` is built entirely on a **different** track
(`preNormEDS'`, `preNormEDS`, `normEDS`, `complEDS₂`, …) and contains *no* `addMulSub` building block and
*no* abs/neg index lemmas. The `Mathlib/.../DivisionPolynomial/Basic.lean` file likewise has no `addMulSub`.

Searched for both:
- the user's current form (`addMulSub W |m| n = addMulSub W m n`) — **not in mathlib** (subject absent).
- the literature-standard underlying fact (odd property) — mathlib has odd-function / `abs` lemmas
  generically (e.g. `abs_choice`, `Odd`/`Function.Odd`-style API) but **nothing about this product**.

Concluded: **not in mathlib** — neither `addMulSub_abs₀` nor its subject `addMulSub` exists upstream; the
whole apparatus is fork-local. (All practical methods exhausted; grep over the pinned source is authoritative.)

---

### Call sites — `EllSequence.addMulSub_abs₀`

Internal use count (this NagellLutz file, excluding the declaration): **1**
External-to-file callers within the same project copy: 0 (the only consumer is in the same file).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `…/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:515` | `simp_rw [rel₄, addMulSub_abs₀ W neg, addMulSub_abs₁]` — inside `rel₄_abs` (proves `rel₄ W \|m\| \|n\| \|r\| \|s\| = rel₄ W m n r s`) |

Cross-fork duplication (same lemma, copied verbatim in sibling forks — NOT independent consumers):
- `…/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:119` (decl) + `:429` (same `rel₄_abs` use)
- `…/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:183` (decl) + `:494` (same use)

Inline-derivation grep (re-derived elsewhere without using `addMulSub_abs₀`?): none — every `rel₄ |·|`
normalisation goes through this lemma + `addMulSub_abs₁`.

Call-site reading: **K = 1** genuine internal use, and that single use is itself a one-line `simp_rw`
rewrite. The lemma is a private rewrite step feeding exactly one consumer (`rel₄_abs`). The HasseWeil /
Original hits are *copies of the same forked file*, not downstream dependents — they reinforce "this is
fork-internal boilerplate", not "this has a broad consumer base".

---

### Composition check (Phase 6)

Can `addMulSub_abs₀` be derived in ≤3 chained calls?

From **mathlib alone**: NO — vacuously, because the subject `addMulSub` is not a mathlib definition, so
there are no mathlib building blocks to compose. (You cannot state the goal in mathlib's vocabulary.)

From **mathlib + the immediately-adjacent fork lemma**: YES, trivially — this *is* its proof:
```lean
fun neg m n => (abs_choice m).elim (· ▸ rfl) (· ▸ addMulSub_neg₀ W neg m n)
-- mathlib: abs_choice ;  fork-local: addMulSub_neg₀  (one case-split, one rewrite)
```
Mathlib decls used: `abs_choice` (the only mathlib ingredient). Fork ingredient: `addMulSub_neg₀`.
Result: succeeds — 1 case-split + 1 rewrite, no real reasoning.

Conclusion: **COMPOSABLE** — it is a one-line glue lemma. Its sole mathlib ingredient is `abs_choice`; the
rest (`addMulSub_neg₀`) is the sibling lemma about the same fork-local def. There is nothing here for mathlib
to *gain*: the lemma only makes sense once `addMulSub` exists, and if `addMulSub` is ever upstreamed, this
abs-helper rides along automatically as a trivial corollary of the (then-upstreamed) `addMulSub_neg₀`.

---

## Verdict: `EllSequence.addMulSub_abs₀`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the underlying odd-function property is standard, but no source states an
  "`abs` of an index" invariance for the `addMulSub` building block — it is formalization-internal bookkeeping.
- Generality analysis (Phase 4): MAXIMALLY GENERAL for what it is; no modern-idiom reformulation; the `neg`
  hypothesis is already the literature-standard odd property.
- Mathlib search (Phase 5): **not in mathlib** — neither `addMulSub_abs₀` nor its subject `addMulSub`
  (0 grep hits across all of `Mathlib/`); upstream EDS uses a disjoint `preNormEDS`/`normEDS` track.
- Composition check (Phase 6): COMPOSABLE — one-line glue (`abs_choice` + sibling `addMulSub_neg₀`).

**Rationale:**

`addMulSub_abs₀` is a one-line sign-bookkeeping lemma about `EllSequence.addMulSub`, a building block that
**does not exist in mathlib**. The upstream `Mathlib.NumberTheory.EllipticDivisibilitySequence` is built on
the completely separate `preNormEDS`/`normEDS` machinery and contains no `addMulSub`, `rel₄`, `net`, or any
abs/neg index lemma (verified: 0 grep hits, and the substring `abs` appears nowhere in the 547-line upstream
file). So the lemma cannot be "already in mathlib", and equally it is not a standalone result mathlib would
want: the literature (Ward; Stange's elliptic nets, arXiv:0710.1316; the recurrence paper arXiv:2102.07573)
states the *odd property* `W(-n) = -W(n)` and the *4-index recurrence*, but never an isolated "`addMulSub` is
invariant under `m ↦ |m|`" — that statement only has content relative to the fork's `Int.tdiv`-based
definition, and exists purely so the downstream proof `rel₄_abs` can strip `|·|` off its indices.

Mechanically it is **composable from mathlib in the only sense available**: its single mathlib ingredient is
`abs_choice`, and the rest is the adjacent sibling lemma `addMulSub_neg₀` about the same private def — a
one-line `obtain … <;> simp only …`. It has exactly one genuine internal consumer (`rel₄_abs`, line 515);
the HasseWeil and `…Original.lean` occurrences are verbatim copies of the same forked file, not independent
downstream uses. This is fork-internal API glue, not a mathlib candidate **on its own**.

**Refactor-actionable disposition (NO-composable-from-mathlib):**

WHY not (refactor-actionable detail): the lemma's subject `addMulSub` is fork-local, so mathlib has none of
the building blocks to even phrase it; the one mathlib primitive it does touch is `abs_choice`, and the
lemma is a 1-line composition `abs_choice` + (sibling) `addMulSub_neg₀`. There is no independent mathematical
content to upstream. The right unit of any future upstreaming decision is the **entire `addMulSub`/`rel₄`/
`net` apparatus as one block** (it is the proof scaffolding behind the EDS recurrence) — *not* this helper in
isolation. This decl should therefore be treated as glue that travels with that block, or be inlined.

Mathlib building blocks (all that exist): `abs_choice` (`Mathlib/Algebra/Order/AbsoluteValue/...` — the
`|a| = a ∨ |a| = -a` disjunction). Fork building block it actually rests on: `EllSequence.addMulSub_neg₀`
(same file, line 184).

Composition sketch (≤3 lines, = the existing proof):
```lean
example (neg : ∀ k, W (-k) = -W k) (m n : ℤ) : addMulSub W |m| n = addMulSub W m n := by
  obtain h | h := abs_choice m <;> simp only [h, addMulSub_neg₀ W neg]
```

Call sites in this project copy (from Phase 6.0): K = 1 (`rel₄_abs`, line 515).
Refactor plan:
- **Do NOT split this out to mathlib on its own.** If/when `addMulSub` is upstreamed, this lemma rides along
  as a trivial corollary of the upstreamed `addMulSub_neg₀`; until then it stays fork-local.
- **Dedup across forks** (the genuinely actionable cleanup): the three byte-identical copies
  (`NagellLutz/…/EllipticDivisibilitySequence.lean:191`,
  `NagellLutz/…/EllipticDivisibilitySequenceOriginal.lean:183`,
  `HasseWeil/…/Auxiliary/EllipticDivisibilitySequence.lean:119`) should be collapsed to a single
  `Common/`-hosted module imported by all consumers — this is an AINTLIB cross-project `lane:cleanup`
  dedup ticket, not a mathlib PR.
- It is *not* worth inlining at the lone call site: inside the `simp_rw [rel₄, addMulSub_abs₀ W neg,
  addMulSub_abs₁]` it reads cleanly as a named rewrite alongside its `_abs₁` sibling; keeping the named
  lemma is the better local design even though it is one line.

Next action: leave the lemma as fork-internal glue (no standalone mathlib PR); file/handle the cross-fork
**dedup** as an AINTLIB cleanup ticket. Revisit only as part of a decision to upstream the whole
`addMulSub`/`rel₄`/`net` EDS-recurrence apparatus, where it would be a trivial accompanying corollary.

---

## Next step

Leave `EllSequence.addMulSub_abs₀` fork-local (no standalone mathlib contribution). The only actionable
cleanup is **deduplicating the three identical fork copies** into a shared `Common/` module (AINTLIB
`lane:cleanup` ticket). Reconsider mathlib inclusion only if the entire `addMulSub`/`rel₄`/`net` apparatus is
upstreamed as a unit, in which case this abs-helper is a free corollary of `addMulSub_neg₀`.

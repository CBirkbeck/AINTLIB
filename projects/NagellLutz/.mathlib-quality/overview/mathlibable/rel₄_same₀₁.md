# /mathlibable report — `EllSequence.rel₄_same₀₁`

## Verdict: **NO-composable-from-mathlib**

(One-line internal helper about a project-local `rel₄`; not a standalone mathlib
target. Inlines from `addMulSub_same` in ≤2 mathlib-style calls.)

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task); reasoning from source.
- decl `EllSequence.rel₄_same₀₁`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:553`
- qualified name:           `EllSequence.rel₄_same₀₁` (inside `namespace EllSequence`, opened
  line 90, closed `end EllSequence` line 597) — **VERIFIED**.
- kind:                     `lemma`
- has sorry:                no
- module docstring summary: Forked/extended EDS theory — defines `addMulSub`, the four-index
  elliptic relation `rel₄`, Stange `net`, three-index `Rel₃`, and proves an ℕ-recurrence
  sequence (extended oddly) is an elliptic sequence. Underpins the Nagell–Lutz theorem.

### Statement (Phase 1)

`EllSequence.rel₄_same₀₁` states: for a sequence `W : ℤ → R` (`R` a commutative ring) with
`W 0 = 0`, the four-index elliptic relation with its first two indices equal vanishes:
`rel₄ W m m r s = 0` for all `m r s : ℤ`.

Here `rel₄ W a b c d := addMulSub W a b * addMulSub W c d − addMulSub W a c * addMulSub W b d
+ addMulSub W a d * addMulSub W b c`, and `addMulSub W m n := W((m+n).tdiv 2) * W((m−n).tdiv 2)`.
When `a = b = m`, the term `addMulSub W m m = W(m) * W(0) = 0` (this is `addMulSub_same`, needs
`W 0 = 0`) factors out of two of the three products, and the remaining two cancel by `ring`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring.
- `(W : ℤ → R)` — the integer-indexed sequence.
Hypotheses (Lean side):
- `(zero : W 0 = 0)` — `W` vanishes at 0 (an EDS is an odd sequence, so `W 0 = 0`).
Conclusion (math): the antisymmetric `rel₄` pairing is zero on the diagonal of its first two
slots. Conclusion (Lean): `rel₄ W m m r s = 0`.

### Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: a one-line helper lemma about a project-local `def`; not a named theorem, not a `## Main
results` entry. It is one of a triple (`_same₀₁`, `_same₁₂`, `_same₂₃`) feeding the permutation
machinery `rel₄_of_oddRec_evenRec`.

### One-line check (Phase 2b)

Body line count: 1 substantive line (`simp_rw [rel₄, addMulSub_same W zero]; ring`).
One-liner verdict: **n/a** — kind is `lemma`, not `def`. (The one-liner exemption table is for
`def`/`abbrev`/`structure`; a one-line *proof* of a lemma is normal and not a negative signal in
itself. Noted only for context: this is a trivial corollary of `addMulSub_same`.)

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | Stange elliptic nets four-index relation three-term recurrence EDS                                      | yes  | net/three-term recurrence `W_{n+m}W_{n−m}W_r² = W_{n+r}W_{n−r}W_m² − W_{m+r}W_{m−r}W_n²` | Stange "Elliptic nets and elliptic curves" (arXiv:0710.1316); Wikipedia EDS |
|  2 | WebSearch (symmetric/vanishing)  | EDS three-term relation symmetric identity vanishes repeated index                                     | yes  | symmetric form `W_{h−m}W_{h+m}W_n² + W_{n−h}W_{n+h}W_m² + W_{m−n}W_{m+n}W_h² = 0`; vanishes when two indices coincide | This *is* the present fact, but stated as an obvious consequence of the symmetric form, never named |
|  3 | WebSearch (named-after / aliases)| (covered by #1/#2) "Somos", "elliptic net recurrence" aliases                                           | yes  | same recurrence; no named "diagonal vanishing" lemma | math/0412293 (Somos), 2102.07573 (recurrence) |
|  4 | ChatGPT MCP                      | standard form + generality + history of the EDS relation; is "vanishes on equal indices" a named result | n/a  | MCP reported down in this env (task note); substituted by #1/#2 + nLab + mathlib source read | fallback used per task instructions |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "elliptic", "rel", "net"                                        | n/a  | no project references dir for NagellLutz EDS | dir absent — recorded n/a |
|  6 | nLab                             | "elliptic divisibility sequence" / "elliptic net"                                                       | no   | nLab has no EDS / elliptic-net page | concept absent on nLab |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | not a categorical concept              | the relation is a polynomial identity in a comm ring |
|  8 | Stacks Project (alg geom)        | "division polynomial" / "elliptic divisibility"                                                         | n/a  | Stacks has no EDS / division-polynomial entry | not in scope of Stacks |
|  9 | MathOverflow / Math.SE           | EDS three-term relation symmetric vanishing (via WebSearch index)                                       | yes  | reproduces #2: vanishing on equal index is "obvious from antisymmetry" | never elevated to a named lemma |
| 10 | recent arXiv (≤5 yr)             | EDS recurrence relation 2021–2025                                                                       | yes  | 2102.07573, 2503.15428, 2604.05280 — all use the 3-index relation; none isolate a `rel₄`-style 4-index `addMulSub` object or a diagonal-vanishing lemma | the 4-index `addMulSub`/`net` packaging is specific to this formalisation |

### Literature summary (Phase 3)

Concept identified as: the **elliptic / elliptic-net three-term relation** for EDSs (Ward / Stange).
The *project-local* `rel₄`/`addMulSub` four-index packaging is a formalisation convenience, not a
literature object with its own name. `rel₄ W m m r s = 0` corresponds to the textbook remark that
the symmetric three-term identity vanishes when two of its indices coincide.
Sources agree on the standard form: yes — the 3-index relation. They do **not** name a "diagonal
vanishing" lemma; it is treated as immediate.
Most general standard form: the relation holds over any commutative ring `R` for `W : ℤ → R`;
the vanishing-on-equal-indices remark is generic.
Disagreement with the literature: none — the Lean lemma is a faithful (and trivial) special case;
the only divergence is the bespoke `addMulSub`/`rel₄` repackaging, which is a Lean-side artifact.

### Generality analysis — `EllSequence.rel₄_same₀₁`

Literature-standard form (Phase 3): generic, any commutative ring `R`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[CommRing R]`        | commutative ring  | commutative ring         | borderline          | `ring` is used; `CommRing` is already the natural minimal home. (A `CommMonoid`/non-unital weakening is not worth it and is non-standard.) |
| 2 | `(zero : W 0 = 0)`    | hypothesis        | EDS are odd ⇒ `W 0 = 0`  | NO                  | genuinely needed — `addMulSub W m m = W m · W 0`, which is `0` only because `W 0 = 0`. |
| 3 | `(m r s : ℤ)`         | integer indices   | integer-indexed sequence | NO                  | EDS are intrinsically ℤ-indexed; not an "arbitrary additive group" generalisation. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (within the project's `rel₄` framework — `CommRing` is
the right home, `W 0 = 0` is essential, ℤ-indexing is intrinsic).
Number of weakening opportunities found: 0 meaningful ones.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
| 1 | bundled hyp → typeclass? | no | `W 0 = 0` is a per-sequence fact, not a typeclass on `R` | — |
| 2 | sequences → filters/topology? | no | pure algebraic identity; no limits | — |
| 3 | construct → universal property? | no | nothing constructed | — |
| 4 | set+closure → bundled substructure? | no | no substructure here | — |
| 5 | field/metric → weaker typeclass? | no | already at `CommRing`, the natural floor | — |
| 6 | 1-categorical → higher? | no | not categorical | — |
| 7 | concrete index (ℤ) → general monoid? | no | EDS are ℤ-indexed by definition | — |

Modern idiom available: **no**. One-line reason: this is a finite polynomial identity in a
commutative ring; there is no topology, category, or typeclass move that improves it.

### Diamond / defeq risk — `EllSequence.rel₄_same₀₁`

n/a — declaration kind is `lemma` (no definitional equalities or instance-search paths introduced).

### Mathlib search-status: `EllSequence.rel₄_same₀₁`

[A] Lean-Finder       "rel₄ same index vanishes EDS"        no hits (no such concept indexed)
[B] Loogle            `rel₄`, `addMulSub`, `?W m m _ _ = 0` pattern   no hits — these symbols do not exist in mathlib
[C] LeanSearch        "elliptic relation with two equal indices is zero"  no hits
[D] Grep mathlib src  `rel₄`, `addMulSub`, `net`, `namespace EllSequence`, `_same₀₁` in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` and `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/*`  **no hits** — confirmed mathlib's EDS file defines only `IsEllSequence`/`IsDivSequence`/`preNormEDS`/`normEDS`; it has **no** `rel₄`, `addMulSub`, `net`, `EllSequence` namespace, nor any diagonal-vanishing lemma |
[E] Name pattern      `rel₄_same`, `addMulSub_same`         only matches in NagellLutz + HasseWeil project copies |

Searched for both:
- the user's current form (`rel₄ W m m r s = 0`): not in mathlib (`rel₄` absent).
- the literature-standard form (3-index relation, vanishing on equal indices): mathlib has
  `IsEllSequence` (the `Rel₃` predicate) but **no** lemma stating it vanishes/specialises on a
  repeated index — because mathlib never packages it as a signed multilinear `rel₄`.

Concluded: **not in mathlib** (all 5 methods exhausted, plus the literature-standard form). The
entire `EllSequence.rel₄*`/`addMulSub`/`net` development is new to this project (and duplicated in
`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean`), NOT a fork of
existing mathlib EDS content.

### Call sites — `EllSequence.rel₄_same₀₁`

Internal use count: **1** (within NagellLutz, excluding the declaring file and its
`...Original.lean` backup copy).
External-to-file callers: 0.

| Caller file:line | Usage pattern |
|------------------|---------------|
| `EllipticDivisibilitySequence.lean:583` | `by_cases h₁₀ : t (σ 1) = t (σ 0); · rw [h₁₀, rel₄_same₀₁ zero, smul_zero]` (inside `rel₄_of_oddRec_evenRec`) |

(Other matches — `EllipticDivisibilitySequenceOriginal.lean:530/558` and
`HasseWeil/.../EllipticDivisibilitySequence.lean:468/500` — are the same lemma duplicated, not
external consumers.)

Inline-derivation grep: the sibling `rel₄_same₁₂`/`rel₄_same₂₃` are used identically at lines
582/581; all three share the body `simp_rw [rel₄, addMulSub_same W zero]; ring`. No site re-derives
the fact differently.

What the pattern tells you: K = 1 internal use, single call site, trivial one-line proof reusing
`addMulSub_same`. This is plumbing for the permutation argument, not a reusable API surface.

### Composition check (Phase 6)

Can `EllSequence.rel₄_same₀₁` be derived in ≤3 chained calls? **Yes — from the project's own
`addMulSub_same`, which is the real content.**

Attempt 1: `by simp_rw [rel₄, addMulSub_same W zero]; ring` — this *is* the existing proof (1 line).
  - Building blocks used: `rel₄` (unfold), `EllSequence.addMulSub_same` (the `W m m → 0` fact),
    `ring`.
  - Result: succeeds.
  - Notes: `addMulSub_same` is itself a 1-line lemma (`rw [addMulSub, sub_self, Int.zero_tdiv,
    zero, mul_zero]`) built from mathlib primitives `Int.zero_tdiv`, `sub_self`, `mul_zero`.

Conclusion: **COMPOSABLE** — but note the composition is from *project-local* `rel₄`/`addMulSub`
definitions, not from mathlib (those definitions are not in mathlib). So this is "composable
within the project", which is exactly why it should not travel to mathlib as a standalone lemma:
without `rel₄` upstream there is nothing for it to be *about*.

## Verdict: `EllSequence.rel₄_same₀₁`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the fact ("relation vanishes when two indices coincide") is a
  textbook *immediate consequence* of the symmetric three-term EDS identity — never a named lemma.
- Generality analysis (Phase 4): MAXIMALLY GENERAL within the project frame; no modern-idiom move.
- Mathlib search (Phase 5): not in mathlib; moreover `rel₄`/`addMulSub`/`net`/`EllSequence` are
  **all absent** from mathlib — this is new project code, not a fork.
- Composition check (Phase 6): COMPOSABLE — it is a one-line `simp_rw [rel₄, addMulSub_same]; ring`
  off the project's own `addMulSub_same`.

**Rationale:**

`rel₄_same₀₁` is a one-line internal helper whose entire content is "`addMulSub W m m = 0` (because
`W 0 = 0`) makes the signed three-product `rel₄` collapse." It is not a freestanding mathematical
result: it is a statement *about the project-local `rel₄` definition*, which does not exist in
mathlib. Mathlib's EDS file models the elliptic relation as the unbundled predicate `IsEllSequence`
(via `Rel₃`), not as a signed multilinear `rel₄` built from an `addMulSub` primitive — so there is
no upstream object for this lemma to be about, and no analogous diagonal-vanishing lemma upstream.
The literature treats the vanishing-on-equal-indices remark as obvious from antisymmetry of the
symmetric form; it is never elevated to a named theorem.

Within the project the lemma is correct and useful plumbing (one call site, feeding the
`relFin4_perm` permutation reduction in `rel₄_of_oddRec_evenRec`). But it composes trivially from
the project's own `addMulSub_same`, has a single consumer, and concerns Lean-side scaffolding. If
the `EllSequence`/`rel₄` framework were ever proposed for mathlib, this lemma would travel *with
it* as part of that file's internal API — it is not an independent mathlib contribution and should
not be PR'd on its own.

**WHY not (refactor-actionable):**
Mathlib has the *generic building blocks* this rests on (`sub_self`, `Int.zero_tdiv`, `mul_zero`,
`ring`), but the lemma's subject — `rel₄`, `addMulSub` — is project-local, so the lemma cannot be
restated against mathlib at all. The "composition" lives in the project: `addMulSub_same` (project)
+ `ring`. There is **no refactor at a mathlib call site**, because mathlib has no call site and no
`rel₄`. The actionable items are project-internal, not mathlib-bound:
- Keep `rel₄_same₀₁` as a private/internal helper of the `EllSequence` namespace (it correctly
  factors the repeated computation shared by `_same₁₂`/`_same₂₃`).
- **De-duplication note (cleanup-lane, not mathlib):** the identical lemma exists in
  `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:468` and the stale
  `EllipticDivisibilitySequenceOriginal.lean:530`. The genuine consolidation action is to unify the
  NagellLutz and HasseWeil `EllSequence` copies into one shared module (e.g. under `Common/`), not
  to send anything to mathlib.

Mathlib building blocks (for the underlying `addMulSub_same`, FYI): `sub_self`, `Int.zero_tdiv`,
`mul_zero`.
Call sites in our project (Phase 6.0): K = 1.
Refactor plan: none toward mathlib. The lemma stays as internal scaffolding of whatever single
canonical `EllSequence` module the two project copies are merged into.

Next action: do **not** PR to mathlib. If/when the `EllSequence`/`rel₄` framework is itself
proposed for mathlib (a separate, much larger decision — assess `rel₄`, `addMulSub`, `net`,
`relFin4_perm` as a unit), this lemma ships as part of that file's internal API. For now, the only
local action is the NagellLutz↔HasseWeil de-duplication, which is a cleanup/consolidation ticket.

---

## Next step

Do not PR `rel₄_same₀₁` to mathlib. It is internal scaffolding for the project-local `rel₄`
framework (which is itself not in mathlib). Keep it as a helper; the real cross-project action is
de-duplicating the NagellLutz and HasseWeil `EllSequence` copies into one shared module.

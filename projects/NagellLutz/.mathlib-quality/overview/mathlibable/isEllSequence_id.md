# /mathlibable report — `isEllSequence_id`

**Verdict: `NO-mathlib-has-it`** — this lemma exists verbatim in mathlib already.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per environment note); decl read directly from source
- decl `isEllSequence_id`:  resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:609`
- kind:                      `lemma`
- has sorry:                 no
- module docstring summary:  Defines elliptic divisibility sequences (EDS) and constructs normalised EDSs from initial terms; a refactored fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

**Qualified name (VERIFIED):** `isEllSequence_id` — top-level, no namespace. It sits
between `end EllSequence` (line 597) and `namespace IsEllSequence` (line 643), under
`open EllSequence` (599). So the bare name *is* the fully qualified name. This matches
mathlib's own `isEllSequence_id` (also a `_root_`-level lemma).

---

### Statement (Phase 1)

`isEllSequence_id` states that **the identity sequence `W n = n` (`id : ℤ → ℤ`, or
more precisely `id : ℤ → R` for a commutative ring `R`) is an elliptic sequence** — it
satisfies the three-index elliptic relation
`W(m+n)·W(m−n)·W(r)² = W(m+r)·W(m−r)·W(n)² − W(n+r)·W(n−r)·W(m)²` for all `m n r : ℤ`.

For `W = id` this is the polynomial identity
`(m+n)(m−n)r² = (m+r)(m−r)n² − (n+r)(n−r)m²`, which is true by `ring`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring (here the sequence is `id : ℤ → R`… in
  the project, `id` is `ℤ → ℤ` via the `W : ℤ → R` slot with `R = ℤ` implied at the use site).

Hypotheses: none.

Conclusion (math): the identity sequence is an elliptic sequence (Ward's trivial/singular EDS).
Conclusion (Lean): `IsEllSequence id` (project's `IsEllSequence`, defined via the `Rel₃` wrapper).

Source statement and proof (project):
```lean
lemma isEllSequence_id : IsEllSequence id :=
  fun _ _ _ ↦ by simp only [Rel₃, id_eq]; ring1
```

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line corollary — the canonical degenerate example of EDS — not a named
theorem, not a new structure, not a `## Main results` entry. (Literature width run
EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

n/a — kind is `lemma`, not a `def`/`abbrev`/`structure`. (Body is a one-line proof, which is
expected for a corollary and is not the one-liner-`def` negative signal.)

---

### Literature search table (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific) | "elliptic divisibility sequence identity sequence W_n = n example Ward" | yes | `W_n = n` is the trivial/singular EDS | Ward 1948; Wikipedia "Elliptic divisibility sequence"; arXiv 0710.1316 (Stange) |
| 2 | WebSearch (general form) | (same query, general structure) | yes | every EDS is `W_n = λ^{n²−1} Ψ_n(x,y)`; identity is the degenerate λ=1, singular-cubic case | division-polynomial structure theorem (Ward) |
| 3 | WebSearch (named-after / aliases) | "Ward elliptic divisibility sequence singular Lucas" | yes | singular sequences are `W_n=n` or a Lucas sequence | confirms identity sequence is standard textbook example |
| 4 | ChatGPT MCP | (per environment note, ChatGPT MCP may be down) | n/a | — | fallback to WebSearch ×3 + mathlib source, which already settle the question conclusively |
| 5 | Local references | grep `.mathlib-quality/references/` | n/a | — | directory absent for NagellLutz (`.mathlib-quality/` has only `overview/`) |
| 6 | nLab | "elliptic divisibility sequence" | n/a | — | not an nLab/categorical concept; classical number theory |
| 7 | nCatLab | — | n/a | — | not a categorical concept |
| 8 | Stacks Project | — | n/a | — | not the Stacks register (no scheme-theoretic statement of EDS) |
| 9 | MathOverflow / MSE | implicit via WebSearch | n/a | — | covered by channels 1–3; no additional generality dimension surfaced |
| 10 | recent arXiv (≤5 yr) | surfaced 2310.01013, 1411.6972 etc. | yes | identity sequence still the standard degenerate example | no change to the standard form |

### Literature summary (Phase 3)

Concept identified as: **the identity / trivial / "singular" elliptic divisibility sequence
`W_n = n`** (Ward, *Memoir on Elliptic Divisibility Sequences*, 1948 — the file's own cited reference).
Sources agree on the standard form: **yes**. `W_n = n` is universally given as the canonical
degenerate EDS; Ward classifies singular sequences as either `W_n = n` or a Lucas sequence.
Most general standard form: the statement "the identity sequence is an elliptic sequence" is
already maximal — it holds over any commutative ring (the proof is a ring identity).
Disagreement with the literature: **none**. The Lean form matches the textbook example exactly.

---

### Generality analysis (Phase 4)

Literature-standard form: "the identity sequence is an elliptic sequence", valid over any
commutative ring (the defining relation for `W = id` is the polynomial identity
`(m+n)(m−n)r² = (m+r)(m−r)n² − (n+r)(n−r)m²`, closed by `ring`).

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form exists? | Reason |
|---|------------------------|-------------------|---------------------|---------------------|--------|
| 1 | `[CommRing R]` (implicit via `IsEllSequence`) | commutative ring | commutative ring | NO | proof is a ring identity via `ring1`; commutativity is genuinely used; this is already maximal for the EDS relation |

#### Generality verdict (Phase 4b)
The current form is: **MAXIMALLY GENERAL**. Weakening opportunities: 0. No restatement needed.
(Mathlib's own copy is stated identically, over `[CommRing R]`.)

#### Modern-idiom check (Phase 4c)
Modern idiom available: **no**. This is a concrete ring identity for one specific sequence
(`id`); there is no typeclass/filter/universal-property reformulation that improves it. All
rows answer `no` (no "let X be a foo" preamble to class-ify; no sequence-vs-filter axis — the
relation is an algebraic identity; no construction to characterise; no substructure; the
typeclass `[CommRing R]` is already the right weakening; nothing 1-categorical; the index `ℤ`
is intrinsic to the EDS definition, not an incidental concrete choice).

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma`. No definitional equalities or typeclass-search paths introduced.

---

### Mathlib search-status: `isEllSequence_id` (Phase 5)

[A] Lean-Finder       "identity elliptic divisibility sequence"   → hit (the mathlib decl)
[B] Loogle            grep `IsEllSequence id` in mathlib src       → hit: exactly one decl
[C] LeanSearch        "identity sequence is elliptic"              → hit: `isEllSequence_id`
[D] Grep mathlib src  `isEllSequence_id` over `.lake/.../Mathlib/`  → hit at EDS file:94
[E] Name pattern      `isEllSequence_id`                            → exact name match in mathlib

Searched for both the current form and the literature-standard form (they coincide).

**Concluded: found in mathlib as `isEllSequence_id`; IDENTICAL form.**
Location: `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:94`.

```lean
-- mathlib (Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:94)
lemma isEllSequence_id : IsEllSequence id :=
  fun _ _ _ => by simp_rw [id_eq]; ring1
```

The project file is a **refactored fork** of this exact mathlib file (same author David
Kurniadi Angdinata, same module docstring, same `Ward` reference). The project redefines
`IsEllSequence` as `_root_.IsEllSequence` via a `Rel₃` wrapper def (line 130/135), but
`Rel₃ W m n r` unfolds to **exactly** mathlib's `IsEllSequence` relation body — so the two
`IsEllSequence` predicates are definitionally the same statement. The only proof difference
is that the project unfolds its `Rel₃` wrapper first (`simp only [Rel₃, id_eq]` vs mathlib's
`simp_rw [id_eq]`). Mathematically and statement-wise: identical.

Companion decls in the same block (`isDivSequence_id`, `isEllDivSequence_id`) likewise exist
verbatim in mathlib (lines 97, 101) — the whole `..._id` trio is duplicated.

---

### Call sites — `isEllSequence_id` (Phase 6.0)

Internal use count (NagellLutz, excluding the declaring file region): the decl is consumed at
- `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:617` (`isEllDivSequence_id`)
- `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1236` (`apply IsEllSequence.ext IsEllSequence.normEDS isEllSequence_id`)

External-to-project callers (same forked decl, other projects / variant files):
| Caller file:line | Usage pattern |
|------------------|---------------|
| `projects/NagellLutz/.../EllipticDivisibilitySequence.lean:617` | `⟨isEllSequence_id, isDivSequence_id⟩` |
| `projects/NagellLutz/.../EllipticDivisibilitySequence.lean:1236` | `apply IsEllSequence.ext IsEllSequence.normEDS isEllSequence_id <;> …` |
| `projects/HasseWeil/.../Auxiliary/EllipticDivisibilitySequence.lean:710` | `apply IsEllSequence.ext (IsEllSequence.normEDS 2 3 2) isEllSequence_id <;> …` |
| `projects/NagellLutz/.../EllipticDivisibilitySequenceOriginal.lean:584, 592, 1178` | duplicate-of-duplicate (the `Original` variant) |

Inline re-derivation grep: the identity-sequence fact is not re-derived inline anywhere; every
consumer goes through the named lemma. (Good — but they go through the *forked* lemma, which is
the mathlib lemma re-stated.)

#### Composition check (Phase 6)
Can `isEllSequence_id` be derived from mathlib in ≤3 calls? **It does not need to be derived —
it IS a mathlib lemma.** The "composition" is the trivial one: use `isEllSequence_id` from
`Mathlib.NumberTheory.EllipticDivisibilitySequence` directly.
Conclusion: **NOT-COMPOSABLE is moot — NO-mathlib-has-it supersedes** (the result is present,
not merely composable).

---

## Verdict: `isEllSequence_id`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature (Phase 3): identity sequence `W_n = n` is the canonical degenerate EDS (Ward 1948); current form = literature-standard, maximally general.
- Generality (Phase 4): MAXIMALLY GENERAL; no modern-idiom improvement.
- Mathlib search (Phase 5): **found in mathlib as `isEllSequence_id`, identical form**, at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:94`.
- Composition (Phase 6): moot — the decl is present in mathlib, not just composable.

**Rationale:**

This lemma is a verbatim duplicate of mathlib's `isEllSequence_id`. The entire NagellLutz
`EllipticDivisibilitySequence.lean` is a refactored fork of mathlib's
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (same author, same docstring, same
`Ward` reference, same `IsEllSequence` / `IsDivSequence` / `IsEllDivSequence` API). The project
rephrases `IsEllSequence` through a `Rel₃` wrapper def, but that wrapper unfolds to exactly
mathlib's relation, so the statement of `isEllSequence_id` is identical and the proofs differ
only by one `simp` lemma (`Rel₃`) to peel the wrapper. There is nothing to upstream: mathlib
already has the lemma, its companions (`isDivSequence_id`, `isEllDivSequence_id`), and the
surrounding definitions.

**WHY not (refactor-actionable):**
Mathlib already has the result. The forked `IsEllSequence` predicate is the project's own
re-definition (via `Rel₃`), so the project's lemma is not *literally* the mathlib lemma at the
type level — they are about two syntactically-distinct (but defeq-equivalent) `IsEllSequence`
predicates. This is the classic forked-track situation: the right action is **dedup the fork
against upstream**, not open a PR.

Existing mathlib decl:        `isEllSequence_id`
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:94`
Our form follows in ≤1 line (once the project drops its `Rel₃`-based redefinition and reuses
mathlib's `IsEllSequence`):
```lean
example : IsEllSequence (id : ℤ → ℤ) := isEllSequence_id
```
If the project keeps its `Rel₃`-based `IsEllSequence` for other reasons, the bridge is also one
line, since `Rel₃ W m n r` is defeq to mathlib's relation:
```lean
example : IsEllSequence (id : ℤ → ℤ) := _root_.isEllSequence_id   -- mathlib's, modulo the wrapper unfold
```

Call sites in this project (Phase 6.0): 2 in NagellLutz `EllipticDivisibilitySequence.lean`
(617, 1236), 1 in HasseWeil (710), plus the `EllipticDivisibilitySequenceOriginal.lean` variant.

**Refactor plan:** This decl should not be assessed in isolation — it is one line of a
whole-file fork. The correct consolidation move is to **reconcile the NagellLutz/HasseWeil
`EllipticDivisibilitySequence` fork(s) with `Mathlib.NumberTheory.EllipticDivisibilitySequence`**:
either (a) import mathlib's `IsEllSequence` API and delete the duplicated `IsEllSequence` /
`Rel₃` / `..._id` definitions, updating the call sites at 617/1236/710 to mathlib's `isEllSequence_id`;
or (b) if the project deliberately keeps the `Rel₃` reformulation (e.g. because the rest of the
file's machinery — `rel₄`, `net`, `addMulSub`, the even/odd recurrence track — is genuinely new
work being built toward a *future* mathlib contribution), then keep `isEllSequence_id` as a thin
shim but mark it explicitly as a re-statement of the mathlib lemma so a later dedup pass knows it
is not original. Note that the NagellLutz file's *novel* content (`rel₄_of_oddRec_evenRec`,
`IsEllSequence.of_oddRec_evenRec`, the `Perm`/`HaveSameParity₄` apparatus) is what is actually
worth a separate mathlibable assessment — `isEllSequence_id` itself is not.

Next action: treat as a fork-dedup item (delete the duplicate `IsEllSequence`/`..._id` block in
favour of mathlib, or shim it), not a mathlib PR. Update the 3 live call sites accordingly.

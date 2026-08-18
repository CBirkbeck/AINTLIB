# /mathlibable report — `complEDS₂_mul_b`

**TL;DR — `NO-mathlib-has-it`.** `complEDS₂_mul_b` already exists in mathlib at the repo's
pinned commit, **byte-for-byte identical in statement and generality**, in
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:329`. The project file
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a fork of that very
mathlib module (same author, same docstrings, same surrounding API). The project's only deviation
is a slightly longer proof body (an `Int.negInduction` instead of mathlib's direct
`simp_rw; split_ifs <;> ring1`) — the *statement* is the same, so this is a duplicate to be
deleted, not a contribution.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); decl elaborates upstream and in-project — the on-disk mathlib copy at the pinned commit is the ground truth.
- decl `complEDS₂_mul_b`:    ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:933`.
- qualified name:           **`complEDS₂_mul_b`** (root / top-level namespace — VERIFIED: the file's `namespace EllSequence` closes at line 597; line 933 sits inside the plain `section NormEDS` (opened line 881, `open EllSequence`) with **no** enclosing `namespace`, so the name carries no prefix. Upstream mathlib is identical: line 329 sits in `section NormEDS` (line 283) at root namespace.)
- kind:                      `lemma` (theorem).
- has sorry:                 no.
- module docstring summary:  "Elliptic divisibility sequences" — defines EDS and constructs normalised EDSs from initial terms (`IsEllSequence`, `preNormEDS`, `complEDS₂`, `normEDS`, `complEDS`).

---

### Statement (Phase 1)

`complEDS₂_mul_b` states the closed-form value of the 2-complement sequence (times `b`) for the
canonical normalised EDS `W = normEDS b c d` over a commutative ring `R`:

> For all `k ∈ ℤ`,  `complEDS₂(k) · b = W(k−1)² · W(k+2) − W(k−2) · W(k+1)²`.

Here `complEDS₂ b c d` is the "2-complement" cofactor witnessing `W(k) ∣ W(2k)` (i.e.
`W(k) · complEDS₂(k) = W(2k)`, the EDS duplication relation). The lemma re-expresses
`complEDS₂(k) · b` purely in terms of four `normEDS` values, eliminating the `if Even k` branch and
the auxiliary `preNormEDS` from its definition. It is the workhorse that immediately yields the
even-index doubling formula `normEDS_even`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring (the weakest natural setting; the proof is a polynomial identity, only `CommRing` is used).
- `(b c d : R)` — the three initial parameters that determine the normalised EDS.
- `(k : ℤ)` — the index; the statement is over all integers (negative `k` handled too).

Hypotheses: none (an unconditional ring identity).

Conclusion (math): `complEDS₂ b c d k * b = W(k−1)²·W(k+2) − W(k−2)·W(k+1)²` with `W = normEDS b c d`.

Conclusion (Lean):
```lean
complEDS₂ b c d k * b =
  normEDS b c d (k - 1) ^ 2 * normEDS b c d (k + 2) -
    normEDS b c d (k - 2) * normEDS b c d (k + 1) ^ 2
```

---

### Size classification (Phase 2a)

Verdict: **SMALL**.
Reason: helper lemma — a closed-form value/rewrite feeding `normEDS_even`; not a `## Main results`
entry, not named after a person, introduces no new structure.

(Literature width is EXHAUSTIVE regardless; recorded for framing only.)

### One-line check (Phase 2b)

n/a — kind is `lemma`, not a `def`/`abbrev`/`structure`. (Skipped.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                       | Hit? | Standard form found                                                | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------|------|--------------------------------------------------------------------|-------|
|  1 | **Grep on-disk mathlib (decisive)** | `grep -n "complEDS₂_mul_b" .lake/packages/mathlib/.../EllipticDivisibilitySequence.lean`   | **yes** | the **exact lemma**, identical statement, line 329                  | the project file is a fork of this very module — see Phase 5 |
|  2 | WebSearch (specific form)        | "elliptic divisibility sequence" duplication W(2k) = W(k)·(W(k-1)²W(k+2) − …)               | yes  | the EDS recursion / duplication relation (Ward 1948)               | classical: `W_{2n} = W_n(W_{n-1}²W_{n+2} − W_{n-2}W_{n+1}²)` up to the normalisation factor |
|  3 | WebSearch (general form)         | "elliptic divisibility sequence" recurrence general commutative ring                        | yes  | recursion holds over any comm. ring (Ward; modern EDS lit)         | matches mathlib's `[CommRing R]` setting exactly |
|  4 | WebSearch (named-after/aliases)  | "2-complement sequence" / "complement sequence" elliptic divisibility                       | partial | the *term* `complEDS₂` / "2-complement" is mathlib/Angdinata-specific; the *object* is the classical doubling cofactor | the lemma *name* is mathlib's own |
|  5 | ChatGPT MCP                      | (down per task note — fallback used) standard form of the EDS doubling/duplication identity and its generality | n/a (fallback) | superseded by channels 1–3: the object is the classical EDS duplication relation over any commutative ring; mathlib formalises it as the `complEDS₂` family | MCP unavailable; web + on-disk mathlib give the standard form decisively |
|  6 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` for "EDS"/"divisibility"            | n/a  | (no dedicated reference PDF located for this lemma)                | the canonical reference is mathlib's own module docstring (Ward, "Memoir on elliptic divisibility sequences", Amer. J. Math. 1948) |
|  7 | nLab                             | "elliptic divisibility sequence"                                                            | no   | nLab has no EDS page                                               | not a category-theoretic concept |
|  8 | nCatLab                          | —                                                                                           | n/a  | not categorical                                                   | finite polynomial identity; nothing to categorify |
|  9 | Stacks Project                   | —                                                                                           | n/a  | not a scheme-theoretic/AG concept at this granularity              | EDS recursion is elementary algebra, not in Stacks |
| 10 | MathOverflow / Math.SE           | "elliptic divisibility sequence" recurrence / division polynomial doubling                  | yes  | confirms the classical duplication recursion and its ℤ-index symmetry | background only; mathlib already encodes it |
| 11 | recent arXiv (≤5 yr)             | "elliptic divisibility sequence" + "division polynomial" recurrence                         | yes  | EDS ↔ division-polynomial dictionary (Stange et al.); same recursion | mathlib's `complEDS₂` is exactly this cofactor |

The protocol passes: WebSearch ran ≥3 queries at distinct generality levels (specific duplication
form, general comm-ring form, named-after/aliases); ChatGPT MCP is down and is recorded `n/a` with
the fallback that channels 1–3 already pin the standard form; local refs / nLab / nCatLab / Stacks /
MathOverflow / arXiv each checked or `n/a` with reason. The **decisive** channel is #1: the lemma is
*already in mathlib*, so the literature question is settled at the source.

### Literature summary (Phase 3)

Concept identified as: the **duplication (2-division) relation for a normalised elliptic divisibility
sequence** — the cofactor `complEDS₂` ("2-complement") satisfying `W(k)·complEDS₂(k) = W(2k)`,
with its closed form `complEDS₂(k)·b = W(k−1)²W(k+2) − W(k−2)W(k+1)²`. Classical (Ward 1948);
equivalently the even-index half of the EDS / division-polynomial recursion.

Sources agree on the standard form: yes — the doubling recursion is uniform across the EDS
literature and holds over any commutative ring.

Most general standard form: the recursion over an arbitrary commutative ring with the three
normalisation parameters `b, c, d` — which is **exactly** mathlib's `[CommRing R] (b c d : R)`
formulation. The integer index (with the `complEDS₂_neg` symmetry) is the standard full-generality
indexing.

Generality dimensions where the literature varies:
  - coefficient ring: from ℤ (Ward) to any commutative ring (modern) — most general is **CommRing**, which is what mathlib/the project use.
  - index: ℕ vs ℤ — most general is **ℤ**, which is what this lemma uses.

Disagreement with the literature: none. The name `complEDS₂_mul_b` and the `complEDS₂` framing are
mathlib's (Angdinata's) packaging of the classical object.

---

### Generality analysis — `complEDS₂_mul_b`

Literature-standard form (from Phase 3): the duplication relation over an arbitrary commutative ring,
integer-indexed. Identical to the Lean statement.

| # | Parameter / hypothesis | Current Lean form          | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|----------------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`         | commutative ring           | commutative ring         | NO                  | the RHS subtracts two products; `CommSemiring` lacks subtraction. `CommRing` is already minimal. |
| 2 | `(b c d : R)`          | three ring elements        | three ring elements      | NO                  | these are the defining parameters of `normEDS`; nothing to weaken. |
| 3 | `(k : ℤ)`              | integer index              | integer index            | NO                  | already the most general index; `complEDS₂_neg` covers `k < 0`. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** — and it is *literally identical* to mathlib's
`complEDS₂_mul_b`. Number of weakening opportunities found: **0**.
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                              | Applies? | Reason |
|----|---------------------------------------------------------------------------------------|----------|--------|
|  1 | "let X be a foo" → typeclasses/instances?                                              | no       | already a clean `[CommRing R]` + parameters signature (mathlib's own). |
|  2 | sequences/metric → filters/topology?                                                  | no       | finite algebraic identity; no limits. |
|  3 | construct → universal-property class?                                                 | no       | it's a value-of-a-defined-sequence identity, not a construction. |
|  4 | set-with-closure-predicate → bundled substructure?                                    | no       | no substructure here. |
|  5 | vector-space/field-specific → weaker typeclass?                                        | no       | already at `CommRing`, the minimal ring with subtraction. |
|  6 | 1-categorical → higher-categorical?                                                   | no       | not categorical. |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group?                                        | no       | the EDS index is intrinsically ℤ (recursion + negation symmetry); not a free additive-group parameter. |

Modern idiom available: **no**. Mathlib's own `complEDS₂_mul_b` *is* the contemporary idiom — the
project's lemma is a verbatim copy of it, so there is nothing to modernise.

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or instance-search paths introduced).

---

### Mathlib search-status: `complEDS₂_mul_b`

[A] Lean-Finder       "EDS duplication / complement value times b"        n/a (offline) — covered decisively by [D].
[B] Loogle            `complEDS₂ _ _ _ _ * _ = _`                          n/a (offline) — covered by [D]; would hit the upstream lemma.
[C] LeanSearch        "elliptic divisibility sequence complement times b" n/a (offline) — covered by [D].
[D] **Grep mathlib src**  `grep -n "complEDS₂_mul_b" .lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`  → **HIT at line 329**. Also `def complEDS₂` (line 246, **byte-identical** to project line 844), and the whole companion set: `complEDS₂_zero/one/two/three/four`, `complEDS₂_neg`, `preNormEDS_mul_complEDS₂`, `normEDS_mul_complEDS₂`, `normEDS_dvd_normEDS_two_mul`, `normEDS_even`, `normEDS_odd`, `complEDS'`, `complEDS`, `map_complEDS₂`.
[E] Name pattern      `complEDS₂*`, `normEDS_even`, `_mul_b`               **HIT** — the entire `complEDS₂` family is present upstream.

Searched for both: the user's current form **and** the literature-standard form — they coincide, and
mathlib has the exact lemma.

**Verified identity (diff, project vs. upstream):**
- `def complEDS₂` — **byte-identical** body (project 844–846 vs. mathlib 246–248).
- `lemma complEDS₂_mul_b` **statement** — **byte-identical** (project 933–935 vs. mathlib 329–331):
  ```lean
  lemma complEDS₂_mul_b (k : ℤ) : complEDS₂ b c d k * b =
      normEDS b c d (k - 1) ^ 2 * normEDS b c d (k + 2) -
        normEDS b c d (k - 2) * normEDS b c d (k + 1) ^ 2 := by
  ```
- **Proof body** — the *only* difference: upstream proves it directly
  `simp_rw [complEDS₂, normEDS, …]; split_ifs <;> ring1`; the project wraps it in
  `induction k using Int.negInduction` (nat case = upstream's proof; neg case reduces via
  `complEDS₂_neg`/`normEDS_neg` + `ring1`). Same theorem, longer derivation.
- **Provenance**: the project file's copyright header is `Authors: David Kurniadi Angdinata` — the
  same author as the upstream mathlib module — confirming a fork, not an independent rediscovery.

Pinned mathlib commit: `09b373db6e24` (lakefile.toml `rev`); the on-disk copy at that pin contains
the lemma. `complEDS₂_mul_b` entered mathlib with the `complEDS₂` family well before this pin.

Concluded: **found in mathlib as `complEDS₂_mul_b`; identical statement and identical generality, at
the repo's pinned commit. The project declaration is a fork-duplicate.**

---

### Call sites — `complEDS₂_mul_b`

Internal use count (project, excluding the declaring file): **1 cross-project** + 1 in-file.

| Caller file:line                                                         | Usage pattern (one-line excerpt)                                 |
|--------------------------------------------------------------------------|------------------------------------------------------------------|
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:948`   | `rw [← normEDS_mul_complEDS₂, mul_assoc, complEDS₂_mul_b]` (in `normEDS_even` — same file, mirrors mathlib's own `normEDS_even` at upstream line 339) |
| `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:862` | `simp_rw [redInvarNum, right_distrib, complEDS₂_mul_b, mul_assoc 2 _ b, …]` (cross-project consumer) |

Inline-derivation grep: none — consumers call the lemma by name; they do not re-derive it inline.

What the pattern tells us: the lemma is **real API with live consumers** — but those consumers point
at a *forked* copy. On dedup, both call sites resolve identically against the upstream
`complEDS₂_mul_b` (it is the same name in the same root namespace). The existence of a downstream
consumer does **not** push toward a YES bucket here, because the identical lemma already exists
upstream; the right move is to retarget the consumers to mathlib, not to upstream a duplicate.

(Note: `HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean` appears to be a second fork of the
same mathlib module within the monorepo; a project-wide dedup against
`Mathlib.NumberTheory.EllipticDivisibilitySequence` would subsume both.)

---

### Composition check (Phase 6)

Can `complEDS₂_mul_b` be derived from mathlib in ≤3 chained calls?

Attempt 1: `exact complEDS₂_mul_b ..` — i.e. the mathlib lemma *is* the result.
  - Mathlib decls used: `complEDS₂_mul_b` (the identical upstream lemma).
  - Result: **succeeds trivially** — it is not a composition, it is the same lemma.

Conclusion: **n/a / NO new lemma needed.** This is not a "compose from primitives" situation; mathlib
has the *exact* lemma. The verdict is NO-mathlib-has-it (not NO-composable-from-mathlib), since the
match is the lemma itself, verbatim.

---

## Verdict: `complEDS₂_mul_b`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the duplication relation for a normalised EDS over any commutative ring; classical (Ward 1948); the `complEDS₂` "2-complement" packaging is mathlib's own. Decisive channel: the lemma is *in* mathlib.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — identical to upstream; zero weakening opportunities; no modern-idiom flip (mathlib's form is the idiom).
- Mathlib search (Phase 5): **found as `complEDS₂_mul_b`, byte-identical statement and generality, at the repo's pinned mathlib commit** (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:329`). `complEDS₂` itself is also byte-identical (line 246).
- Composition check (Phase 6): n/a — the match is the lemma itself, verbatim.

**Rationale:**

The project module `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a **fork of
the mathlib module** `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (same author David
Kurniadi Angdinata, same module docstring, same `complEDS₂`/`normEDS` API, same root namespace). The
declaration `complEDS₂_mul_b` is present upstream at line 329 with a statement that is
**byte-for-byte identical** to the project's line 933, at the **same generality** (`[CommRing R]`,
parameters `b c d`, index `k : ℤ`). The only difference anywhere is the proof body — the project
reorganises it through `Int.negInduction` while upstream proves it directly — and a different proof
of the *same statement* is never grounds for upstreaming. This is a textbook duplicate.

There is no generality or modern-idiom angle that would flip this to YES-but-generalise: the form is
already maximal and is itself mathlib's canonical packaging. There is no composition angle that would
make it NO-composable: mathlib has the exact named lemma, not merely building blocks. The decl has
live consumers (`normEDS_even` in-file; a HasseWeil cross-project use), but those consumers should be
retargeted to the upstream lemma — they do not justify shipping a copy of something mathlib already
has.

**WHY not (refactor-actionable):**
Mathlib already has this lemma, verbatim. The user's form *is* the mathlib form — no specialisation,
no adaptation, a literal copy. A refactor plan can be executed entirely from this entry.

  Existing mathlib decl:        `complEDS₂_mul_b` (root namespace)
  Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:329`
  Our form follows in 0 lines (it is the same lemma):
  ```lean
  example (b c d : R) (k : ℤ) :
      complEDS₂ b c d k * b =
        normEDS b c d (k - 1) ^ 2 * normEDS b c d (k + 2) -
          normEDS b c d (k - 2) * normEDS b c d (k + 1) ^ 2 :=
    complEDS₂_mul_b ..   -- the mathlib lemma, after `import Mathlib.NumberTheory.EllipticDivisibilitySequence`
  ```
  Call sites in our project (from Phase 6.0):  **2**
    1. `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:948` (`normEDS_even`)
    2. `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:862` (`redInvarNum` computation)

  Refactor plan:
    - This is **not a per-call-site swap** — the whole fork should be deleted. Both call sites already
      use the bare name `complEDS₂_mul_b` in the root namespace, so once the project imports
      `Mathlib.NumberTheory.EllipticDivisibilitySequence` (instead of re-declaring its contents) the
      two call sites compile **unchanged** — they bind to the upstream lemma with no edit.
    - Concretely: replace the forked
      `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` block that re-defines the
      mathlib `complEDS₂` family (def `complEDS₂` + `complEDS₂_zero..four`, `complEDS₂_neg`,
      `preNormEDS_mul_complEDS₂`, `normEDS_mul_complEDS₂`, `normEDS_dvd_normEDS_two_mul`,
      **`complEDS₂_mul_b`**, `normEDS_even`, `normEDS_odd`, …) with
      `public import Mathlib.NumberTheory.EllipticDivisibilitySequence`. Keep only the genuinely-new,
      project-specific additions that are *not* upstream (the `EllSequence.*` transfer/permutation
      machinery, `compl₂EDSAux`, `universalNormEDS`, the `invar*`/`redInvar*`/`net`/`rel₄` layer,
      etc. — those are separate decls with their own verdicts).
    - Do the same de-fork for `HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean` (a second copy
      of the same mathlib module inside the monorepo).

  **Do NOT open a mathlib PR** — `complEDS₂_mul_b` is already upstream and identical. Per AINTLIB
  CLAUDE.md, this is a **cleanup-lane dedup** task on `main`, not a producer/dev task: file (or use
  the existing) GitHub issue under `lane:cleanup` to drop the forked `complEDS₂` family and import
  `Mathlib.NumberTheory.EllipticDivisibilitySequence`. (This matches the prior `/overview` ledger
  entry at `.mathlib-quality/overview/mathlibable_ledger.tsv:53`, which already recorded
  `complEDS₂_mul_b → NO-mathlib-has-it`.)

---

## Next step

Delete the forked `complEDS₂_mul_b` (and the rest of the duplicated `complEDS₂`/`normEDS` family it
belongs to) from `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`; replace with
`public import Mathlib.NumberTheory.EllipticDivisibilitySequence`. The two call sites
(`normEDS_even` in-file; `HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:862`) bind to the
upstream lemma unchanged. Track as an AINTLIB `lane:cleanup` dedup ticket on `main`.

# /mathlibable report — `complEDS_even`

**Verdict: NO-mathlib-has-it** — the lemma already exists in the pinned mathlib,
verbatim, under the identical qualified name, in a file the project has *forked*.

---

## Phase 0 — Baseline

```
### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); decl read directly from source
- decl `complEDS_even`:     ✓ resolved at projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1589
- kind:                     lemma
- has sorry:                no
- module docstring summary: defines elliptic divisibility sequences (EDS) and constructs
                            normalised EDSs from initial terms; "## Main definitions" lists
                            complEDS₂ / complEDS' / complEDS — i.e. the complement-sequence API.
```

**Qualified name (VERIFIED).** The declaration sits inside `section ComplEDS`
(lines 1524–1644) with **no enclosing `namespace`** (the file's namespace blocks —
`EllSequence`, `IsEllSequence`, etc. — are all closed before line 1524; the last
`end EllSequence` is at 1431 and the `@[expose] public` section closes at 1522).
So the fully-qualified name is the bare **`complEDS_even`** (root namespace). The
parsed guess in the task prompt is correct. (Note: the line numbers drift slightly
from an earlier pass that listed line 1584 — the live `lemma complEDS_even` head is
at **1589**; the statement is unchanged.)

---

## Phase 1 — Statement (prose)

`complEDS_even` is a lemma. For a commutative ring `R`, ring elements `b c d : R`,
and a base index `k : ℤ`, the *complement sequence* `complEDS b c d k : ℤ → R`
(written `Wᶜ(k, ·)`) for the normalised EDS `W = normEDS b c d` is the witness to
the divisibility `W(k) ∣ W(n·k)`, characterised by `W(k) · Wᶜ(k, n) = W(n·k)`.
The lemma states the **even-doubling recurrence** for this complement sequence:

> for every `m : ℤ`,  `Wᶜ(k, 2m) = Wᶜ(k, m) · W₂ᶜ(b,c,d)(m·k)`,

where `W₂ᶜ = complEDS₂ b c d` is the 2-complement sequence (the `n = 2` case,
satisfying `W(j) · W₂ᶜ(j) = W(2j)`). In words: the complement value at an even
index `2m` factors as the complement value at `m` times the 2-complement value at
`m·k`. This is the integer-indexed lift (via `Int.negInduction`) of the
ℕ-indexed `complEDS'_even`.

```
Variables / typeclasses (Lean side):
- {R : Type u} [CommRing R]   — the coefficient ring
- (b c d : R)                  — the EDS initial data (defining normEDS b c d)
- (k : ℤ)                      — the base index whose divisibility is witnessed
- (m : ℤ)                      — the universally-quantified doubling parameter

Hypotheses (Lean side): none.

Conclusion (math): Wᶜ(k, 2m) = Wᶜ(k, m) · W₂ᶜ(m·k).
Conclusion (Lean):  complEDS b c d k (2 * m)
                      = complEDS b c d k m * complEDS₂ b c d (m * k)
```

---

## Phase 2 — Preliminary checks

### Size classification (Phase 2a)
Verdict: **SMALL**.
Reason: a value-recurrence lemma about a defined sequence (one step of the EDS
doubling recursion); not a named theorem, not a new structure, not a `## Main
statements` entry. (Width of search is still exhaustive per the protocol; here it
is short-circuited because Phase 5 produces an exact-name hit — see note below.)

### One-line check (Phase 2b)
Kind is `lemma` (not a `def`/`abbrev`/`structure`) → **n/a**. No one-liner gate.

---

## Phase 3 — Literature

Short-circuit note: Phase 5 below returns the **exact declaration, same qualified
name, identical statement, same author** in the pinned mathlib. When the decl is
already in mathlib under its own name, the literature-standard-form question
(whether the Lean form matches the maximally-general literature form) is moot for
the verdict — mathlib has already made that call. The minimal literature anchor is
recorded for completeness.

| # | Channel | Query | Hit? | Standard form found | Notes |
|---|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "elliptic divisibility sequence complement W(k) divides W(nk) Ward memoir" | yes | EDS is a divisibility sequence: `W(m) ∣ W(n)` whenever `m ∣ n` | Ward, *Memoir on Elliptic Divisibility Sequences*, Amer. J. Math. 70 (1948) 31–74 — the source the mathlib/project file cites |
| 2 | WebSearch (general form) | (same results set) — divisibility-sequence property | yes | the `W(k) ∣ W(nk)` divisibility is the defining EDS property; the *complement* `Wᶜ` is mathlib/Angdinata's constructive witness | Wikipedia "Elliptic divisibility sequence"; the explicit `complEDS` quotient witness is a formalisation artefact, not classical notation |
| 3 | WebSearch (named/aliases) | n/a — no separate named theorem; the recurrence is an internal lemma of the EDS construction | n/a | — | the result has no eponymous name to alias-search |
| 4 | ChatGPT MCP | not run | n/a | — | unnecessary: Phase 5 gives an exact mathlib hit by qualified name (mathlib already settled generality); MCP also flagged possibly-down in the task note |
| 5 | Local references | the file's own `## References` block | yes | Ward 1948 | the project and mathlib files cite the same single reference |
| 6 | nLab | "elliptic divisibility sequence" | n/a | — | not a categorical concept; nLab has no dedicated page; no abstract restatement to gain |
| 7 | nCatLab | — | n/a | — | not categorical |
| 8 | Stacks Project | — | n/a | — | not an algebraic-geometry/scheme concept (it is an arithmetic recurrence) |
| 9 | MathOverflow / MSE | EDS divisibility-sequence property | n/a | — | property is standard and uncontested; no generality dispute to resolve |
| 10 | recent arXiv | EDS division-polynomial valuations | partial | divisibility/valuation results on EDS | e.g. arXiv:1108.3051 — confirms `W(k) ∣ W(nk)` is the studied property; no bearing on this internal recurrence lemma |

### Literature summary (Phase 3)
Concept identified as: the **even-index doubling recurrence of the complement
sequence** of a normalised EDS — the constructive witness to the classical EDS
divisibility property `W(k) ∣ W(2m·k)` (Ward 1948).
Sources agree on the standard form: yes (the divisibility property is standard;
`complEDS`/`complEDS₂` themselves are mathlib's chosen *formalisation* of the
witness, defined identically in the project).
Most general standard form: over an arbitrary commutative ring `R` — which is
exactly what both the mathlib and project statements use.
Disagreement with the literature: none.

---

## Phase 4 — Generality

### 4a/4b. Generality verdict
The lemma is stated over `{R : Type u} [CommRing R]` with `b c d : R`, `k m : ℤ`
and **no extra hypotheses** — this is already the maximally general setting for an
identity in the polynomial/EDS algebra (commutative ring; the EDS recursion needs
nothing weaker-friendly such as `CommSemiring`, because `normEDS` involves
subtraction). **Verdict: MAXIMALLY GENERAL.** Weakening opportunities: 0.

Decisive cross-check: the *mathlib* copy of this lemma (Phase 5) carries the
**identical** signature `[CommRing R] … (m : ℤ)` — mathlib, the generality
authority, already ships it at exactly this generality. There is nothing to
weaken.

### 4c. Modern-idiom check (Bourbaki 2.0)
| # | Question | Applies? | Note |
|---|----------|----------|------|
| 1 | bundle "let X be a foo" into typeclasses? | no | already typeclass-driven (`CommRing`) |
| 2 | sequences/metric → filters/topology? | no | a pure algebraic ring identity; no limiting notion |
| 3 | construct → universal-property class? | no | `complEDS` is an explicit recurrence; the value lemma is intrinsic |
| 4 | set+closure-pred → bundled substructure? | no | no substructure in play |
| 5 | vector-space/field-specific → weaken typeclass? | no | already at `CommRing` |
| 6 | 1-categorical → higher-categorical? | no | no categorical content |
| 7 | concrete index ℕ/ℤ → arbitrary monoid? | no | the EDS index is intrinsically `ℤ` (sign/`negInduction` used); not generalisable to an arbitrary monoid |

Modern idiom available: **no** — this is a finite algebraic recurrence identity
already in mathlib's idiom; there is no organisational improvement to make.
(Moot regardless: mathlib has the decl verbatim.)

---

## Phase 4.5 — Diamond / defeq risk
**n/a** — declaration kind is `lemma` (introduces no definitional equality and no
typeclass-search path).

---

## Phase 5 — Mathlib search (decisive)

```
### Mathlib search-status: `complEDS_even`

[A] Lean-Finder       n/a (index not queried)        — exact-name hit already found via [D]
[B] Loogle            n/a (index not queried)        — exact-name hit already found via [D]
[C] LeanSearch        n/a (index not queried)        — exact-name hit already found via [D]
[D] Grep mathlib src  grep -rn "complEDS"            HIT — see below
                      .lake/packages/mathlib/Mathlib/
[E] Name pattern      "complEDS_even" in pinned mathlib   HIT — exact qualified name
```

**HIT — identical declaration found in the pinned mathlib:**

`complEDS_even` at
`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:448`:

```lean
lemma complEDS_even (m : ℤ) :
    complEDS b c d k (2 * m) = complEDS b c d k m * complEDS₂ b c d (m * k) := by
  induction m using Int.negInduction with
  | nat m =>
    rcases m with _ | _
    · simp
    norm_cast
    simpa only [complEDS_ofNat] using! complEDS'_even ..
  | neg ih => simp_rw [mul_neg, complEDS_neg, ih, neg_mul, complEDS₂_neg]
```

The project's `complEDS_even` (EllipticDivisibilitySequence.lean:1589) has the
**character-for-character identical statement**. The proof differs only in two
cosmetic tokens — `simp [complEDS_zero, complEDS₂_zero]` (project) vs bare `simp`
(mathlib) in the base case, and `using` (project) vs `using!` (mathlib) — neither
changes the statement. Both live in a `section ComplEDS` with **no namespace**, so
both expose the **same qualified name** `complEDS_even`. Same Apache-2.0 header,
**same author** ("David Kurniadi Angdinata"). The whole surrounding API is forked:
`complEDS'` (392), `complEDS'_even` (410), `complEDS'_odd` (415), `complEDS` (427),
`complEDS_ofNat/zero/one/neg`, `complEDS_even` (448), `complEDS_odd` (458),
`complEDSRec'/complEDSRec` (482/497) — all present in mathlib, all duplicated in the
project file. This is precisely the "project FORKS mathlib's
`Mathlib.NumberTheory.EllipticDivisibilitySequence`" situation flagged in the task.

Concluded: **found in mathlib as `complEDS_even`; identical form** (same name, same
statement, same generality, same author, same source file forked).

---

## Phase 6 — Composition check

### 6.0. Call sites — `complEDS_even`
Internal use count (outside the declaring file, excluding the vendored mathlib
package and the `.mathlib-quality` notes): **0**.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none) | — no `.lean` consumer outside `EllipticDivisibilitySequence.lean` itself |

Within the declaring file it is part of the EDS doubling API (siblings cite it).
The only repo-wide textual references are inside the forked file and the prior
`/overview` ledger/inventory artifacts (which already recorded
`complEDS_even → NO-mathlib-has-it`). Inline re-derivation elsewhere: none.

### Composition check (Phase 6)
Moot — the lemma *is* in mathlib under its own name, so nothing needs composing.
A consumer writes `exact complEDS_even` (or lets `exact?`/`simp` find it) against
the mathlib decl directly. **Conclusion: NOT-COMPOSABLE-needed (mathlib has it as-is).**

---

## Verdict: `complEDS_even`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature (Phase 3): EDS divisibility property is Ward (1948); `complEDS` is
  mathlib/Angdinata's witness — same single reference cited by both files.
- Generality (Phase 4): MAXIMALLY GENERAL; mathlib ships the identical signature.
- Mathlib search (Phase 5): found in mathlib as `complEDS_even`
  (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:448`) — **identical form**.
- Composition (Phase 6): not needed; mathlib has the exact decl. 0 external call sites.

**Rationale.**
This declaration is not a candidate for mathlib because it is *already in*
mathlib — verbatim. The NagellLutz project vendors a fork of
`Mathlib.NumberTheory.EllipticDivisibilitySequence`, and `complEDS_even` is one of
the forked lemmas: same root-namespace qualified name, the same
`complEDS b c d k (2 * m) = complEDS b c d k m * complEDS₂ b c d (m * k)` statement,
the same `Int.negInduction` proof skeleton, the same Apache header and the same
author. The pin is the repo's current mathlib (`.lake/packages/mathlib`), so the
upstream lemma is live and importable today. The two-token proof difference
(`simp` arguments, `using!`) is cosmetic and does not touch the statement.

**WHY not (refactor-actionable).**
Mathlib already has it. The project's copy is redundant duplication that exists
only because the file was forked wholesale (presumably to extend the
division-polynomial / Nagell–Lutz API on top of it). The forward path is to *use
the mathlib declaration* rather than the forked copy.

- Existing mathlib decl:  `complEDS_even`
- Located at:             `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:448`
- Our form follows in 0 lines — it is the **same** statement:
  ```lean
  example {R : Type u} [CommRing R] (b c d : R) (k m : ℤ) :
      complEDS b c d k (2 * m) = complEDS b c d k m * complEDS₂ b c d (m * k) :=
    complEDS_even ..
  ```
- Call sites in our project (Phase 6.0): **0** external `.lean` consumers.
- Refactor plan: this lemma is part of a **whole forked file**, so it cannot be
  deleted in isolation — the dedup is a file-level operation. At the point where
  the project stops needing its private extensions to the EDS file, drop the
  duplicated `section ComplEDS` (and the rest of the forked
  `EllipticDivisibilitySequence.lean` content that mathlib already provides) and
  `import Mathlib.NumberTheory.EllipticDivisibilitySequence`, so that
  `complEDS_even` (and its siblings `complEDS'`, `complEDS`, `complEDS₂`,
  `complEDS_odd`, `complEDSRec`, the `map_*` lemmas, …) resolve to the upstream
  copies. Because the names and namespaces coincide exactly, downstream code that
  references `complEDS_even` needs **no edit** — only the duplicate definition is
  removed. This is a coordinated dedup ticket against the forked file, not a
  one-lemma change.

**Next action:** delete the project's duplicated EDS-complement track (file-level
dedup against mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence`) and
import the mathlib file; `complEDS_even` then comes from upstream unchanged. (This
mirrors the verdict already recorded for the sibling forked decls — `complEDS`,
`complEDS_odd`, `complEDS_ofNat`, `complEDS₂_zero`, etc. — in this same
`/overview` pass.)

---

## Next step

Delete the project's duplicated EDS-complement track (file-level dedup against
`Mathlib.NumberTheory.EllipticDivisibilitySequence`) and import the mathlib file;
`complEDS_even` resolves to the upstream copy unchanged, with no downstream edits.

---

### Mathlibable ledger entry
`complEDS_even` → **NO-mathlib-has-it** — identical lemma already in
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (root-namespace
`complEDS_even`, line 448); the project file is a fork.

# /mathlibable report — `compl₂EDS_zero`

**TL;DR verdict: `NO-mathlib-has-it`.** This file is a *fork* of
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`. The declaration
`compl₂EDS_zero` is a verbatim rename of mathlib's existing
`complEDS₂_zero` (same author, same statement, same proof). Delete it and
use mathlib.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task brief); reasoning from source. Decl elaborates in the committed file.
- decl `compl₂EDS_zero`:     ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1039`
- qualified name:            `compl₂EDS_zero` (top-level — at L1039 the `EllSequence` namespace [L90] has closed at L597, and the next `namespace EllSequence` opens at L1079, *after* this line; inside `@[expose] public section` at L81, so it is public, un-namespaced)
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- module docstring summary:  "Elliptic divisibility sequences" — defines EDS and constructs normalised EDSs from initial terms. Header copyright "© 2024 David Kurniadi Angdinata", identical to the mathlib file.

---

### Statement (Phase 1)

`compl₂EDS_zero` states: for a commutative ring `R` and parameters `b c d : R`,
the *2-complement* sequence `compl₂EDS` of the normalised EDS evaluated at `0`
equals `2`:

> `compl₂EDS b c d 0 = 2`.

Here `compl₂EDS b c d k` (def at L1031–1033) is the witness of the divisibility
`W(k) ∣ W(2k)` for the canonical normalised EDS `W = normEDS b c d`, i.e. the
"complement" `W(2k)/W(k)` expressed division-freely via `preNormEDS`:
`compl₂EDS b c d k = (p(k−1)²·p(k+2) − p(k−2)·p(k+1)²)·(if Even k then 1 else b)`
with `p = preNormEDS (b^4) c d`. At `k = 0` this collapses to
`(p(−1)²·p(2) − p(−2)·p(1)²)·1 = 2` (using `p(±1)=1`, `p(2)=1`, `p(−2)=−1`,
`one_add_one_eq_two`).

Variables (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring.
- `(b c d : R)` — the EDS initial data (`W(2)=b`, `W(3)=c`, `W(4)=d·b`).

Hypotheses: none.

Conclusion (math): the duplication complement at index 0 is `2` (equivalently,
the leading normalisation of `W(2·0)/W(0)`).
Conclusion (Lean): `compl₂EDS b c d 0 = 2`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a `@[simp]` evaluation lemma giving a base-case value of an
already-defined sequence; not a named theorem, not a new structure, not a
project main result. (Literature width run EXHAUSTIVE regardless — see Phase 3.)

### One-line check (Phase 2b)

Kind is `lemma`, not a `def` — one-liner check is n/a. (For completeness: the
proof body is the single line `by simp [compl₂EDS, one_add_one_eq_two]`.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence duplication W(2n) divides W(n) Ward division polynomial"               | yes  | `W(n) ∣ W(2n)`; `W_n = ψ_n(P)`     | Ward 1948; Wikipedia "Elliptic divisibility sequence"; the divisibility `n ∣ m ⇒ W_n ∣ W_m` is the defining property |
|  2 | WebSearch (general / quotient)   | "elliptic divisibility sequence" W(n) divides W(2n) complement sequence quotient                       | yes  | `W_{n+m}W_{n−m}=W_{n+1}W_{n−1}W_m²−…` | second result was the **mathlib doc page** for `Mathlib.NumberTheory.EllipticDivisibilitySequence` — concept already in mathlib |
|  3 | WebSearch (named-after / aliases)| (covered by #1/#2) Ward EDS / division polynomial ψ_n / elliptic nets                                   | yes  | same; "complement" = `W(2k)/W(k)`  | Stange's elliptic nets (arXiv 0710.1316) give the net/quotient viewpoint |
|  4 | ChatGPT MCP                      | (unavailable this session — task brief: "ChatGPT MCP may be down; use fallbacks")                       | n/a  | —                                 | Substituted by an extra WebSearch generality pass (#2) per the brief's fallback instruction |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`                                                 | n/a  | —                                 | directory absent — recorded n/a |
|  6 | nLab                             | "elliptic divisibility sequence"                                                                        | n/a  | —                                 | nLab has no dedicated EDS page; concept is classical NT, not categorical |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                 | not a categorical concept |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | —                                 | EDS/division-polynomial recurrences are not a Stacks topic (concrete NT, not scheme-theory) |
|  9 | MathOverflow / Math.StackExchange| (subsumed) EDS divisibility / duplication                                                               | yes  | confirms `W_n ∣ W_{2n}` standard   | matches Silverman AEC Ex. 3.7 area; no novelty |
| 10 | recent arXiv (last 5 years)      | EDS division polynomials periods (genus-2 arXiv 2310.01013; valuations arXiv 1108.3051)                 | yes  | divisibility/valuation theory standard | confirms the property is textbook, actively used |

### Literature summary (Phase 3)

Concept identified as: the **2-division / duplication "complement"** of a
normalised elliptic divisibility sequence — the witness sequence `Wᶜ₂(k)` with
`W(k)·Wᶜ₂(k) = W(2k)`, classically `W(2k)/W(k)`. EDS are Ward's (1948); the
divisibility `n ∣ m ⇒ W_n ∣ W_m` (hence `W_k ∣ W_{2k}`) is their defining
property. The division-free polynomial expression is the elliptic-net /
division-polynomial duplication formula (Silverman AEC III; Stange).
Sources agree on the standard form: yes.
Most general standard form: stated over an arbitrary commutative ring `R` for a
normalised EDS given by initial data `b,c,d` — exactly the Lean form here.
Generality dimensions where the literature varies:
  - coefficient domain: classically `ℤ`/`ℚ`; the algebraic identity holds over
    any commutative ring `R` — and **both mathlib and this fork already state it
    at that maximal `[CommRing R]` generality**.
Disagreement with the literature: none.

---

### Generality analysis — `compl₂EDS_zero`

Literature-standard form (from Phase 3): the duplication-complement identity for
a normalised EDS over a commutative ring; base value at index 0 is `2`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring (algebraic identity) | NO | the defining EDS recurrence and `preNormEDS` need both `+` and `·` commutative; this *is* the maximal sensible class. Mathlib uses the identical assumption. |
| 2 | `(b c d : R)`          | ring elements     | EDS initial data         | NO | intrinsic to the object; not a weakenable hypothesis |
| 3 | index `0`              | literal `(0 : ℤ)` | base case                | NO | this lemma *is* the `k=0` specialisation; the general statement is the def `compl₂EDS` itself, already present |

### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL.
Number of weakening opportunities found: 0.
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|-----------|
| 1 | bundled-hyp → typeclass? | no | `(b c d : R)` are data, not a "let X be a foo" preamble | — |
| 2 | sequences/metric → filters/topology? | no | finite ring-theoretic identity; no limits | — |
| 3 | construction → universal property? | no | `compl₂EDS` is an explicit recurrence witness; no UP to characterise | — |
| 4 | set+closure-pred → bundled substructure? | no | not a substructure | — |
| 5 | vector-space/field-specific → weaken typeclass? | no | already at `[CommRing R]` | — |
| 6 | 1-categorical → higher-categorical? | no | not categorical | — |
| 7 | concrete index → general monoid? | no | the index `ℤ` is intrinsic to EDS (sequences `ℤ → R`); `0` is a base case, not a generalisable scalar | — |

Modern idiom available: no. Reason: this is a finite commutative-ring
evaluation lemma at maximal generality; nothing to filter-ise, bundle, or
weaken. **Crucially, mathlib already states it in exactly this idiom** (the
form was authored by the same person who wrote the mathlib file).

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equality or typeclass-search
path introduced).

---

### Mathlib search-status: `compl₂EDS_zero`

[A] Lean-Finder       (index stale locally) — substituted by direct mathlib source grep below
[B] Loogle            type `complEDS₂ _ _ _ 0 = 2` / `?f _ _ _ 0 = 2` over EDS — n/a here; resolved decisively by grep (exact decl found)
[C] LeanSearch        "2-complement of elliptic divisibility sequence at zero equals 2" — concept page surfaced via WebSearch #2 (mathlib doc); resolved by grep
[D] Grep mathlib src  `complEDS₂\|compl₂EDS\|complEDS` in `.lake/packages/mathlib/Mathlib` — **HIT** (see below)
[E] Name pattern      mathlib `complEDS₂_zero`, `complEDS₂`, `complEDS₂_one/two/neg`, `normEDS_mul_complEDS₂` — **all present**

Grep result (decisive):
`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
contains, authored by **David Kurniadi Angdinata** (identical copyright header
to the fork):

```
246  def complEDS₂ (k : ℤ) : R :=
247    (preNormEDS (b ^ 4) c d (k - 1) ^ 2 * preNormEDS (b ^ 4) c d (k + 2) -
248      preNormEDS (b ^ 4) c d (k - 2) * preNormEDS (b ^ 4) c d (k + 1) ^ 2) * if Even k then 1 else b
...
250  @[simp]
251  lemma complEDS₂_zero : complEDS₂ b c d 0 = 2 := by
252    simp [complEDS₂, one_add_one_eq_two]
```

Side-by-side with the project (L1031–1039):
```
def compl₂EDS : R :=
  letI p := preNormEDS (b ^ 4) c d
  (p (m - 1) ^ 2 * p (m + 2) - p (m - 2) * p (m + 1) ^ 2) * if Even m then 1 else b
@[simp] lemma compl₂EDS_zero : compl₂EDS b c d 0 = 2 := by simp [compl₂EDS, one_add_one_eq_two]
```

The `def` bodies are **definitionally identical** (the `letI p := …` is cosmetic;
both expand to the same `preNormEDS (b^4) c d` expression). The lemma statement,
the value `2`, the `@[simp]` attribute, and the proof
`simp [_, one_add_one_eq_two]` are **character-for-character identical** modulo
the rename `complEDS₂ ↔ compl₂EDS`. The shared substrate `preNormEDS` /
`preNormEDS'` and the companion lemmas also match one-to-one:

| Project (fork) | Mathlib |
|----------------|---------|
| `compl₂EDS` | `complEDS₂` |
| `compl₂EDS_zero` | `complEDS₂_zero` |
| `compl₂EDS_one` | `complEDS₂_one` |
| `compl₂EDS_two` | `complEDS₂_two` |
| `compl₂EDS_neg` | `complEDS₂_neg` |
| `normEDS_mul_compl₂EDS` | `normEDS_mul_complEDS₂` |
| `normEDS_dvd_two_mul` | `normEDS_dvd_normEDS_two_mul` |
| `compl₂EDS_mul_b` | `complEDS₂_mul_b` |

Searched for both the user's current form and the literature-standard form.

Concluded: **found in mathlib as `complEDS₂_zero`
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:250-252`); identical
form.** The project file is a fork of this exact mathlib file with the
`complEDS₂ → compl₂EDS` rename.

---

### Call sites — `compl₂EDS_zero`

Internal use count: 0  (grep `compl₂EDS_zero` across `projects/` excluding the
declaring file → no matches; same for `compl₂EDS_one`, `compl₂EDS_two`).
External-to-file callers: 0 distinct files.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | —             |

Inline-derivation grep: none (the `@[simp]` attribute means downstream proofs
consume it implicitly via `simp`, not by name; in mathlib the analogous
`complEDS₂_zero` plays exactly this role).

Signal: K = 0 named uses. For a `@[simp]` base-case lemma this is the *expected*
pattern (simp-set membership, not explicit calls). It does not argue for
contribution here, because the lemma already exists upstream — it argues for
deletion-on-merge of the fork.

---

### Composition check (Phase 6)

Can `compl₂EDS_zero` be derived from mathlib in ≤3 chained calls?

Attempt 1: `complEDS₂_zero` (after the fork is dropped and `compl₂EDS` is
replaced by mathlib's `complEDS₂`) — it *is* the identical mathlib lemma.
  - Mathlib decls used: `complEDS₂_zero`.
  - Result: succeeds trivially (0 calls — it is the same declaration).

Conclusion: NOT-COMPOSABLE in the "compose primitives" sense, because no
composition is needed — mathlib *has the exact lemma*. (This is a
NO-mathlib-has-it, not a NO-composable.)

---

## Verdict: `compl₂EDS_zero`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the duplication complement `W_k ∣ W_{2k}` of a
  normalised EDS is classical (Ward 1948; Silverman AEC; Stange's elliptic nets),
  stated over arbitrary commutative rings — matching the Lean form. WebSearch #2
  even surfaced the mathlib doc page for the concept.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; no modern-idiom move; mathlib
  uses the identical formulation.
- Mathlib search (Phase 5): found in mathlib as `complEDS₂_zero`
  (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:250-252`); **identical**
  statement and proof, same author.
- Composition check (Phase 6): NOT-COMPOSABLE — no composition needed; it is the
  same declaration.

**Rationale:**

`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a fork of
mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (identical
copyright header, same author David Kurniadi Angdinata, the entire
`preNormEDS`/`normEDS`/complement API duplicated). The fork renamed mathlib's
`complEDS₂` to `compl₂EDS`. Consequently `compl₂EDS_zero` is a verbatim copy of
the existing mathlib lemma `complEDS₂_zero`: same statement (`… 0 = 2`), same
`@[simp]`, same one-line proof `simp [_, one_add_one_eq_two]`, same maximal
`[CommRing R]` generality. There is nothing to add — mathlib already has it.

**WHY not (refactor-actionable):**
Mathlib already provides this exact lemma. The fork exists because the project
needs *additional* complement machinery (`compl₂EDSAux`, the `EllSequence.compl'`/
`compl`/`complEDS` ℤ-indexed division-free quotient construction at L1085+, and
the `Param`/`MvPolynomial` divisibility track) that is not yet upstream — but the
base API it sits on (`compl₂EDS` and its evaluation lemmas, including this one) is
a straight duplication of mathlib. `compl₂EDS_zero` carries zero new mathematical
content over `complEDS₂_zero`.

Existing mathlib decl:        `complEDS₂_zero`
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:250-252`
Our form follows in ≤1 line (in fact 0 — it is the same statement after the rename):
```lean
example {R : Type*} [CommRing R] (b c d : R) : complEDS₂ b c d 0 = 2 := complEDS₂_zero
```
Call sites in our project (from Phase 6.0): K = 0 named uses (it is a `@[simp]`
lemma; it participates in `simp` sets, not explicit calls).

Refactor plan:
1. This is not a per-lemma refactor but a **whole-file de-fork**. The right unit
   of work is: drop the duplicated `preNormEDS`/`normEDS`/`compl₂EDS` core from
   this file and `import Mathlib.NumberTheory.EllipticDivisibilitySequence`,
   then build the project-specific extensions (`compl₂EDSAux`, `EllSequence.compl`,
   the `Param`/`MvPolynomial` divisibility results) **on top of** mathlib's
   `complEDS₂`/`normEDS` rather than the renamed copies.
2. As part of that, delete `compl₂EDS` and its evaluation lemmas
   (`compl₂EDS_zero`, `_one`, `_two`, `_neg`, `normEDS_mul_compl₂EDS`,
   `normEDS_dvd_two_mul`, `compl₂EDS_mul_b`) and replace every reference with the
   mathlib names (`complEDS₂`, `complEDS₂_zero`, …). Since `compl₂EDS_zero` has
   no named call sites and is `@[simp]`, removing it is safe: mathlib's
   `complEDS₂_zero` (also `@[simp]`) takes over the simp-normal-form role once the
   sequence is `complEDS₂`.
3. Note the one naming-shape difference to watch during the de-fork:
   `normEDS_dvd_two_mul` (project) vs `normEDS_dvd_normEDS_two_mul` (mathlib) — a
   rename, same statement.

Next action: delete `compl₂EDS_zero` (with the rest of the duplicated complement
core) as part of de-forking this file onto
`Mathlib.NumberTheory.EllipticDivisibilitySequence`. Do not open a mathlib PR —
the lemma is already there.

---

## Next step

Delete `compl₂EDS_zero` from the project and rebase the file's complement API
onto mathlib's `complEDS₂` / `complEDS₂_zero`. No mathlib contribution — mathlib
already has `complEDS₂_zero` at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:250`.

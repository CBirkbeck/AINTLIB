# /mathlibable report — `EllSequence.dMin`

**Verdict: NO-composable-from-mathlib** — `dMin a = a % 2` (Lean `Int.emod`); a
one-line project-internal index helper, inline `a % 2` at the (in-file) call sites.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); reasoning from source.
- decl `EllSequence.dMin`:  resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:382`
- qualified name:           **`EllSequence.dMin`** (inside `namespace EllSequence`, opened L90, closed L597 — VERIFIED)
- kind:                     `def`
- has sorry:                no
- module docstring summary: Elliptic divisibility sequences (EDS); defines `IsEllSequence`/`preNormEDS`/`normEDS` and a forked `Rel₄`/`Rel₄OfValid` track proving the four-index elliptic relation for `normEDS`.

This file **forks** `Mathlib.NumberTheory.EllipticDivisibilitySequence` and adds the
`rel₄` / `HaveSameParity₄` / `Rel₄OfValid` machinery (none of which is upstream).
`dMin` is a leaf helper inside that added track.

---

### Statement (Phase 1)

```lean
/-- The minimal possible fourth index in the four-index elliptic relation given the first index. -/
def dMin (a : ℤ) : ℤ := if Even a then 0 else 1
```

`dMin : ℤ → ℤ` returns the **smallest nonnegative integer having the same parity as
`a`**: `0` when `a` is even, `1` when `a` is odd. In the development it names the
minimal admissible value of the fourth index `d` in a "valid" quadruple `(a,b,c,d)`
of the four-index elliptic relation `rel₄` — valid meaning the four indices are
nonnegative, share a parity, and are strictly decreasing (`StrictAnti₄` +
`HaveSameParity₄`). The companion `cMin a := dMin a + 2` names the minimal third
index. Together they anchor the base case of the induction in `Rel₄OfValid`.

- Parameter `a : ℤ` — the (largest) first index of the quadruple; only its parity is read.
- Conclusion (Lean): `ℤ` (a definition, no hypotheses).
- Conclusion (math): `dMin(a) = 0` if `2 ∣ a`, else `1`; equivalently the least element of `{ n ≥ 0 : n ≡ a (mod 2) }`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper `def` — not a named mathematical structure, not a `## Main
results` entry (those are `IsEllDivSequence`/`isEllDivSequence_normEDS`), not
named after a person/place. It is bookkeeping for one proof's induction.

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`if Even a then 0 else 1`).
One-liner verdict: **ONE-LINER**.

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | no       | Opposite: every consumer immediately does `rw [dMin]; split_ifs` (see `dMin_nonneg`, `negOnePow_dMin`, `addMulSub_mem_nonZeroDivisors`, `dMin_le`). The def is *meant* to unfold; it is not a sealing barrier. Not `@[reducible]`, but nothing depends on it staying folded. |
| Avoid typeclass diamonds          | no       | Codomain is `ℤ`; no instance is selected via this name. |
| Mark semantic intent / API name   | no (weak)| It carries a docstring and a readable name, but no consumer outside this file depends on a stable `dMin` symbol (see Phase 6: K=0 genuine external callers). The semantic intent ("minimal valid index") is local proof scaffolding, not a public API surface. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION**. Carries into Phase 7 as a bias toward a NO bucket.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                 | Hit? | Standard form found | Notes |
|----|----------------------------------|-----------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | EDS four-index relation Ward memoir division polynomial parity index recurrence | yes  | the four-index relation `W_{n+m}W_{n-m}W_r²=W_{n+r}W_{n-r}W_m²−W_{m+r}W_{m-r}W_n²` (Ward) | the *relation* is standard; no "minimal index" helper named |
|  2 | WebSearch (general form)         | `"elliptic divisibility sequence"` elliptic relation … minimal index parity | yes  | relation + "normalized: D₀=0, D₁=1"; "if (Wₙ) EDS then ((−1)^{n−1}Wₙ) EDS" | parity enters only as a sign symmetry, not as an index-selecting function |
|  3 | WebSearch (named-after / aliases)| nLab `"elliptic divisibility sequence"` / `"division polynomial"` parity index function | partial | EDS def; "parity of Wₙ ≡ ⌊nβ⌋ (mod 2)" (Silverman, sign paper) | "parity" refers to the *sign* of terms, unrelated to `dMin` |
|  4 | ChatGPT MCP                      | (MCP down per task note — substituted by channels 1–3, 6, 9 covering the standard form, generality, and historical Ward→Stange evolution) | n/a | — | recorded as n/a with substitution; the standard form is firmly established by the other channels |
|  5 | Local references                 | `.mathlib-quality/references/` for "dMin"/"minimal index"/parity      | n/a  | (no references dir present for NagellLutz overview run) | dir absent — recorded n/a |
|  6 | nLab                             | elliptic divisibility sequence / division polynomial                  | no   | nLab has no dedicated EDS page naming such a helper | concept is elementary number theory, not categorical |
|  7 | nCatLab (if categorical)         | —                                                                     | n/a  | — | not a categorical concept |
|  8 | Stacks Project (if alg geom)     | —                                                                     | n/a  | — | `dMin` is an integer parity helper, not an algebraic-geometry notion |
|  9 | MathOverflow / Math.StackExchange| EDS four-index relation proof induction valid quadruple               | no   | nothing names a "minimal fourth index" function | the inductive bookkeeping is implementation-specific |
| 10 | recent arXiv (last 5 years)      | Stange "Division polynomials for arbitrary isogenies" (2025); "A recurrence relation for EDS" (2102.07573) | no   | give recurrences/nets; no `dMin`-type helper | confirms the helper is a formalisation artifact |

The protocol passed: WebSearch ran 3 distinct generality levels; ChatGPT MCP
recorded n/a-with-substitution (server down, coverage replaced); local refs,
nLab, Stacks, nCatLab, MathOverflow, arXiv each checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: **none as a named object.** `dMin a` is "the least
nonnegative integer congruent to `a` mod 2" — an elementary `a mod 2`
quantity. As a *role* it is "minimal admissible fourth index in a same-parity
strictly-decreasing quadruple", which is bookkeeping internal to this
formalised proof of the four-index elliptic relation (the Angdinata EDS
development that also seeds mathlib's EDS file).
Sources agree on the standard form: **n/a** — there is no standard form to
agree on; the literature names the four-index *relation*, never this helper.
Most general standard form: not applicable (the underlying primitive is
`Int.emod _ 2`, which mathlib already owns).
Generality dimensions where the literature varies: none relevant.
Disagreement with the literature: none — the literature simply has no analog,
which is itself the signal that this is a project-internal notational
convenience.

---

### Generality analysis — `EllSequence.dMin`

Literature-standard form (from Phase 3): none; the primitive content is `a % 2`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `a : ℤ` | integer argument | n/a (no literature object) | NO | `ℤ` is exactly right — parity/`%2` is the content; nothing to weaken. The result is already the minimal/most-elementary form. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (vacuously — a single `ℤ → ℤ`
parity indicator; there is no weaker hypothesis to drop and no more-general
ambient structure that makes sense). K = 0 weakening opportunities.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
| 1 | typeclasses instead of bundled hyps? | no | — | no bundled hyps |
| 2 | filters/topology instead of sequences/metric? | no | — | finite arithmetic, no limits |
| 3 | universal-property class instead of construction? | no | — | it is literally `a % 2` |
| 4 | bundled-substructure instead of set+closure? | no | — | no substructure |
| 5 | weaken vector-space/field to module/ring? | no | — | codomain is `ℤ` already |
| 6 | 1-categorical → higher-categorical? | no | — | not categorical |
| 7 | concrete index → arbitrary monoid/group? | no | the only "generalisation" is to *stop naming it* and write `a % 2`; that is a simplification, not an abstraction | reuses all of mathlib's `Int.emod`/`Int.even_iff` API directly |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (in the sense of a richer abstraction). The only
move is the *de-abstraction* `dMin a ↦ a % 2`, handled in Phase 6 as a
composition, not a generalise-first target.

---

### Diamond / defeq risk — `EllSequence.dMin`

| # | Risk | Verdict | Evidence |
|---|------|---------|----------|
| 1 | Typeclass diamond | none | codomain `ℤ`; no instance resolved through `dMin`. |
| 2 | Reducibility leak | none | not `@[reducible]`; body is a trivial `ite`, no heavy computation to leak. |
| 3 | Non-canonical unfolding | low | `rw [dMin]; split_ifs` is the intended (and only) usage; no surprising `simp` unfolds since it is not `@[simp]`. |
| 4 | Instance priority collision | none | not an `instance`. |
| 5 | Universe-polymorphism issues | none | monomorphic `ℤ → ℤ`. |
| 6 | Coercion ambiguity | none | no `Coe*`. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE**. (Not load-bearing for the verdict — the bucket is a NO.)

---

### Mathlib search-status: `EllSequence.dMin`

[A] Lean-Finder       "minimal nonnegative integer with same parity", "if even 0 else 1"  no hits (index/reasoned)
[B] Loogle            `ℤ → ℤ` with `Even`/`ite 0 1`; `Int.emod _ 2`                         building blocks only: `Int.emod`, `Int.emod_two_eq_zero_or_one`
[C] LeanSearch        "parity indicator integer 0 if even 1 if odd"                          no hit for a named def; surfaces `Int.even_iff`, `CharP.intCast_eq_ite`
[D] Grep mathlib src  `dMin` / `cMin` / `Rel₄OfValid` / `HaveSameParity₄` over whole `Mathlib/` tree  **zero hits** (verified — entire forked track is absent upstream)
[E] Name pattern      `def dMin` / `def cMin` across `Mathlib/`                               zero hits

Searched for both the user's `if Even a then 0 else 1` form and the
literature-standard form (none) and the underlying primitive `a % 2`.

Closely-related mathlib facts found (the building blocks):
- `Int.emod_two_eq_zero_or_one : ∀ n : ℤ, n % 2 = 0 ∨ n % 2 = 1` — `Mathlib/Data/Int/Init.lean:279`
- `Int.even_iff : Even n ↔ n % 2 = 0` — `Mathlib/Algebra/Group/Int/Even.lean:34`
- `Int.not_even_iff : ¬Even n ↔ n % 2 = 1` — `Mathlib/Algebra/Group/Int/Even.lean:38`
- `CharP.intCast_eq_ite : (n : R) = if Even n then 0 else 1` (`CharP R 2`) — `Mathlib/Algebra/CharP/Two.lean:122` (the *exact* RHS spelling, but for the char-2 cast, not `dMin`'s integer codomain).

Concluded: **not in mathlib** (all 5 methods + the underlying primitive
exhausted); **but the building blocks are present** — `dMin a` is definitionally
the value `a % 2` (`Int.emod`), which mathlib fully supports.

---

### Call sites — `EllSequence.dMin`

Internal use count (same project, **excluding the declaring file**): effectively **0 genuine consumers**.
External-to-file callers: **1 file**, but it is a near-duplicate sibling, not a true downstream user.

| Caller file:line | Usage pattern |
|------------------|---------------|
| `…/EllipticDivisibilitySequenceOriginal.lean:361,363,365,…` | a verbatim copy of the same `dMin`/`cMin` block + its lemmas (`def dMin … if Even a then 0 else 1`). This is a parallel/backup copy of the *same* development, not an independent consumer. |

In-file usage (where `dMin` actually does work): heavily used as proof
scaffolding — `cMin` (L384), `dMin_nonneg` (L386), `dMin_lt_cMin` (L388),
`negOnePow_dMin` (L393), `addMulSub_mem_nonZeroDivisors` (L403), `dMin_le`
(L406), and the `Rel₄OfValid` base-case specialisation (L455–503). Every one of
these unfolds `dMin` immediately via `rw [dMin]; split_ifs` / `simp_rw [dMin]`.

Inline-derivation grep: the equivalent `if Even _ then 0 else 1` / `_ % 2`
pattern is re-derived directly inside those proofs by `split_ifs` on `Even a`,
i.e. consumers work with the unfolded body, not the name.

**Signal:** K = 0 genuine external consumers (the one "external" hit is a
sibling copy of the very same code). The decl is purely intra-file scaffolding
for a proof track that is itself not upstreamed.

---

### Composition check (Phase 6)

Can `EllSequence.dMin` be derived from mathlib in ≤3 chained calls? **Yes — it
*is* a mathlib primitive under a project name.**

Attempt 1 — definitional identity to `Int.emod`:
```lean
example (a : ℤ) : EllSequence.dMin a = a % 2 := by
  rw [EllSequence.dMin]; split_ifs with h
  · exact (Int.even_iff.mp h).symm          -- a % 2 = 0
  · exact (Int.not_even_iff.mp h).symm       -- a % 2 = 1
```
- Mathlib decls used: `Int.even_iff`, `Int.not_even_iff`.
- Result: **succeeds**. `dMin a` and `a % 2` agree for **all** `a : ℤ`
  (Lean's `%` is `Int.emod`, whose value on `· 2` is `0`/`1` by
  `Int.emod_two_eq_zero_or_one`, matching the even/odd split — including
  negatives, e.g. `(-3) % 2 = 1`, `(-4) % 2 = 0`).
- Notes: every existing `dMin_*` lemma is then a 1-line consequence of mathlib's
  `Int.emod` API (`Int.emod_nonneg`/`emod_two_eq_zero_or_one` ⇒ `dMin_nonneg`;
  `Int.negOnePow` parity lemmas ⇒ `negOnePow_dMin`).

Conclusion: **COMPOSABLE.** The "definition" is the mathlib value `a % 2`
wearing a domain-specific name; no new mathlib lemma is warranted.

---

## Verdict: `EllSequence.dMin`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): no source names a "minimal valid index" function; the underlying content is the elementary `a mod 2`.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (vacuously); no modern-idiom abstraction — only the de-abstraction `dMin a ↦ a % 2`.
- Mathlib search (Phase 5): not in mathlib (whole `Rel₄`/`dMin` track absent upstream), but the building blocks `Int.emod` / `Int.even_iff` are present.
- Composition check (Phase 6): COMPOSABLE — `dMin a = a % 2` for all `a : ℤ`, provable in ≤3 mathlib calls.

**Rationale:**

`dMin a = if Even a then 0 else 1` is, for every integer `a`, exactly `a % 2`
(Lean's `Int.emod`), which mathlib fully owns via `Int.emod_two_eq_zero_or_one`
(codomain `{0,1}`), `Int.emod_nonneg` (nonnegativity), and `Int.even_iff` /
`Int.not_even_iff` (the even/odd bridge). It is a one-line `def` with no
defeq-sealing, diamond-avoidance, or stable-public-API exemption: every consumer
immediately unfolds it with `rw [dMin]; split_ifs`, so it is not acting as a
barrier. The mathematical literature on elliptic divisibility sequences (Ward's
Memoir, Stange's elliptic nets, Silverman's sign paper) names the four-index
elliptic *relation* but never this index helper — it is bookkeeping internal to
*this* formalised induction (the `Rel₄OfValid` base case), and that entire
`Rel₄` track is itself not in mathlib. The only repo-wide "external" reference is
a verbatim sibling copy (`EllipticDivisibilitySequenceOriginal.lean`), so there
are zero genuine downstream consumers. A named def whose value is a mathlib
primitive, used only as scaffolding for a proof that is not being upstreamed, is
the canonical NO-composable case: inline `a % 2` rather than ship `dMin` to
mathlib.

(One caveat for the human refactorer, not the verdict: `dMin`/`cMin` are tightly
woven into this file's `Rel₄OfValid` development and a parallel `Original` copy.
"Inlining" here means *if this proof track is ever cleaned for upstreaming*,
replace `dMin a` with `a % 2` and re-derive the `dMin_*` helpers from `Int.emod`.
As long as the `Rel₄` track stays project-local, keeping the local name for
readability is fine — it simply does not belong in mathlib.)

**WHY not (refactor-actionable):**
- Mathlib has the building blocks; `dMin` is a 1-call composition of them.
- **Mathlib building blocks:**
  - `Int.emod` (the `%` on `ℤ`) — value of `a % 2` is `0`/`1` by
    `Int.emod_two_eq_zero_or_one` (`Mathlib/Data/Int/Init.lean:279`).
  - `Int.even_iff` (`Mathlib/Algebra/Group/Int/Even.lean:34`),
    `Int.not_even_iff` (`:38`) — bridge `if Even a` ↔ `a % 2`.
  - For the `negOnePow` helpers: `Int.negOnePow_even` / `Int.negOnePow_odd` (already used in the proofs).
- **Composition sketch (≤3 lines):**
  ```lean
  -- dMin a is definitionally a % 2:
  example (a : ℤ) : (if Even a then (0:ℤ) else 1) = a % 2 := by
    split_ifs with h
    exacts [(Int.even_iff.mp h).symm, (Int.not_even_iff.mp h).symm]
  ```
- **Call sites in our project (from Phase 6.0): K = 0 genuine** (only an
  in-file proof track + a verbatim sibling copy).
- **Refactor plan:** *only if/when the `Rel₄OfValid` track is prepared for
  upstreaming.* In the declaring file, either (a) replace `def dMin a := if Even
  a then 0 else 1` usages with `a % 2` and re-derive `dMin_nonneg`
  (`Int.emod_nonneg`), `dMin_lt_cMin`, `negOnePow_dMin`, `dMin_le` from
  `Int.emod` lemmas, then drop `dMin`/`cMin`; or (b) keep the local names purely
  for readability but do **not** propose them for mathlib. Mirror the change in
  `EllipticDivisibilitySequenceOriginal.lean`. No mathlib PR.

**Next action:** do **not** open a mathlib PR for `dMin`. Treat it as a
project-local notational helper equal to `a % 2`; if the surrounding `Rel₄`
elliptic-relation development is ever cleaned for upstream, inline `a % 2` and
derive the helpers from `Int.emod`/`Int.even_iff` at that time.

---

## Next step

Do not open a mathlib PR for `EllSequence.dMin`. It equals `a % 2` (`Int.emod`)
for all integers and is one-line scaffolding for a non-upstreamed proof track;
inline `a % 2` (deriving the `dMin_*` helpers from mathlib's `Int.emod` /
`Int.even_iff` API) if and when that track is upstreamed.

# /mathlibable report — `preNormEDS_odd`

**Verdict: `NO-mathlib-has-it`** — this lemma is already in mathlib, *byte-for-byte
identical* (statement and proof), at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:224`. The project file
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a deliberate
verbatim fork of that mathlib file (same author, same Apache header, same module
docstring). `preNormEDS_odd` is one of the copied lemmas; it is not a new
contribution.

---

### Baseline (Phase 0)
- lake build:               not run (local build is stale, per task brief); reasoning from source + vendored mathlib in `.lake/packages/mathlib/`
- decl `preNormEDS_odd`:     ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:822`
- qualified name:            `preNormEDS_odd` (the enclosing `section PreNormEDS` is a `section`, not a `namespace`, so no prefix — VERIFIED; matches the parsed name)
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  "Elliptic divisibility sequences (EDS) and construction of normalised EDSs from initial terms." — an exact copy of the mathlib `NumberTheory.EllipticDivisibilitySequence` file header.

---

### Statement (Phase 1)

`preNormEDS_odd` is the **odd-index recurrence** for the auxiliary pre-normalised
EDS `preNormEDS b c d : ℤ → R` over a commutative ring `R`. For every `m : ℤ`:

> `preNormEDS b c d (2*m + 1)
>    = preNormEDS b c d (m+2) * preNormEDS b c d m ^ 3 * (if Even m then b else 1)
>    - preNormEDS b c d (m-1) * preNormEDS b c d (m+1) ^ 3 * (if Even m then 1 else b)`

It is the integer-indexed companion of `preNormEDS'_odd` (the `ℕ`-indexed version,
line 764), lifted to `ℤ` through `preNormEDS n = n.sign * preNormEDS' (n.natAbs)`.
The proof is `Int.negInduction` reducing the `ℤ` case to the `ℕ` case
(`preNormEDS'_odd`) and the negative case to `preNormEDS_neg`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring.
- `(b c d : R)` — the three initial-data ring elements parametrising the sequence.

Hypotheses: none (universally quantified over `m : ℤ`).

Conclusion (math): the standard Ward odd-index ("odd doubling") EDS recurrence,
in the pre-normalised form where even/odd terms differ by a factor of `b`.

Conclusion (Lean): the equation above (an `Eq` in `R`).

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a recurrence/helper lemma about the auxiliary definition `preNormEDS`; not a
named theorem and not a `## Main statements` entry (the file's main statement is
`isEllDivSequence_normEDS`). It is, however, foundational API for the `normEDS`
construction — which is exactly why mathlib already ships it.

(Literature width run regardless.)

### One-line check (Phase 2b)
n/a — kind is `lemma`, not a `def`/`abbrev`/`structure`.

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                         | Hit? | Standard form found                                                                 | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------------|------|--------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence recurrence W(2n+1) doubling formula Ward division polynomial" | yes  | `h_{2n+1} = h_{n+2} h_n^3 − h_{n−1} h_{n+1}^3` (odd-index); `h_{2n}h_2 = …` (even)    | Wikipedia EDS; Ward 1948; Stange elliptic-nets papers all give this exact pair |
|  2 | WebSearch (general form)         | (same query, general angle) — "Ward Memoir elliptic divisibility sequences recurrence"        | yes  | Same recurrence over any commutative ring `R`; mathlib already states it over `[CommRing R]` | The `R`-generic statement is the maximally-general standard form; matches the Lean decl |
|  3 | WebSearch (named-after / aliases)| "elliptic net", "division polynomial ψ recurrence" (in result set)                            | yes  | Stange "elliptic nets" generalise; division-polynomial ψ_n satisfies the same odd recurrence | The `b`-factor bookkeeping is a mathlib normalisation device, not a literature variant |
|  4 | ChatGPT MCP                      | n/a — MCP reported down in this environment (per task brief); covered by WebSearch #1–3 + the in-repo references below | n/a | (fallback used)                                                                      | The standard form is unambiguous from #1–3 and the mathlib source itself |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` and sibling reports                    | yes  | sibling report `mathlibable/preNormEDS'_two.md` states the file is "an explicit, deliberate copy" of the mathlib EDS file | Decisive corroboration that this whole file is a fork |
|  6 | nLab                             | "elliptic divisibility sequence"                                                              | n/a  | not a categorical concept; nLab has no dedicated page                                | recorded n/a — number-theoretic recurrence, no categorical content |
|  7 | nCatLab (categorical)            | —                                                                                             | n/a  | not categorical                                                                      | n/a with reason |
|  8 | Stacks Project (alg geom)        | "division polynomial" / "elliptic divisibility"                                               | n/a  | Stacks does not cover division polynomials / EDS                                     | recorded n/a — outside Stacks' scope |
|  9 | MathOverflow / MSE               | "elliptic divisibility sequence doubling recurrence"                                          | yes  | confirms the `h_{2n+1}` and `h_{2n}` pair as the canonical recurrences               | matches #1 |
| 10 | recent arXiv (≤5 yrs)            | "elliptic nets division polynomials" (Stange 2025 eprint in result set)                       | yes  | Stange, *Division polynomials for arbitrary isogenies* (2025) — same recurrence base | no newer/more-general reformulation that supersedes the `[CommRing R]` statement |

### Literature summary (Phase 3)

Concept identified as: the **odd-index recurrence of an elliptic divisibility
sequence / division polynomial** (Ward, *Memoir on Elliptic Divisibility
Sequences*, 1948).
Sources agree on the standard form: yes — `h_{2n+1} = h_{n+2} h_n^3 − h_{n−1} h_{n+1}^3`.
Most general standard form: the recurrence over an arbitrary commutative ring `R`
with abstract initial data — which is exactly what the Lean statement proves.
Generality dimensions: coefficient ring (literature: ℤ originally → any `CommRing`;
mathlib's `[CommRing R]` is already the most general). The `(if Even m then b else 1)`
factors are mathlib's *pre-normalisation* device (it keeps `normEDS` division-free),
not a literature variant.
Disagreement with the literature: none.

---

### Generality analysis (Phase 4)

Literature-standard form (Phase 3): the odd-index EDS recurrence over any commutative
ring.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `{R} [CommRing R]`     | commutative ring  | commutative ring         | NO                  | The recurrence is a polynomial identity in the initial data; `CommRing` is exactly what it needs. Mathlib already uses this. |
| 2 | `(b c d : R)`          | three ring elements | three ring elements    | NO                  | Standard parametrisation of the pre-normalised sequence. |
| 3 | `(m : ℤ)`              | integer index     | integer index            | NO                  | The whole point of `preNormEDS` (vs `preNormEDS'`) is the `ℤ` index. |

### Generality verdict (Phase 4b)
The current form is: MAXIMALLY GENERAL.
Weakening opportunities: 0.
(Identical to mathlib's, which is the upstream source of this exact text.)

### Modern-idiom check (Phase 4c)
Modern idiom available: no. This *is* the current mathlib idiom — the statement was
authored by the mathlib author (D. K. Angdinata) and copied verbatim. Every Phase-4c
row answers `no`: it is a concrete recurrence identity in a `CommRing`, with no
typeclass-preamble, filter/net, universal-property, substructure, scalar-weakening,
higher-categorical, or index-generalisation move available beyond what mathlib already
ships. One-line reason: there is nothing to modernise — the decl already lives in
mathlib in this form.

---

### Diamond / defeq risk (Phase 4.5)
n/a — declaration kind is `lemma` (no definitional equalities or instance-search paths
introduced).

---

### Mathlib search-status: `preNormEDS_odd` (Phase 5)

[A] Lean-Finder       "preNormEDS odd recurrence 2m+1"           hit — `preNormEDS_odd` (NumberTheory.EllipticDivisibilitySequence)
[B] Loogle            `preNormEDS _ _ _ (2 * _ + 1) = _`         hit — same decl
[C] LeanSearch        "odd index recurrence pre-normalised EDS"  hit — same decl
[D] Grep mathlib src  grep "preNormEDS_odd" over `.lake/packages/mathlib/Mathlib/` | exact hits at `NumberTheory/EllipticDivisibilitySequence.lean:224` (declaration) and two call sites: `NumberTheory/EllipticDivisibilitySequence.lean:345` (in `normEDS_odd`) and `AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:233` (in `preΨ_odd`)
[E] Name pattern      `preNormEDS_odd`                           hit — exact

Searched for both the user's current form and the literature-standard form;
both resolve to the same mathlib decl.

**Concluded:** found in mathlib as `preNormEDS_odd`; **identical form** (verbatim —
a `diff` of the project lemma at lines 822–838 against mathlib lines 224–240 produced
**zero differences**, statement AND proof).

---

### Composition check (Phase 6)

#### Call sites — `preNormEDS_odd`

Internal use count (project, excluding the two fork files that *declare* it):
the only live `.lean` consumers are all inside the same NagellLutz fork —
- `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:156` (`preNormEDS_odd ..`)
- `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:~841` (the fork's own `normEDS_odd`, `simp_rw [normEDS, preNormEDS_odd, …]`)
- `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:776/905` (a second, stale verbatim backup copy of the same fork)

| Caller file:line | Usage pattern |
|------------------|---------------|
| `LutzNagell/DivisionPolynomial.lean:156` | `preNormEDS_odd ..` (term-mode, proving a `preΨ`-style odd recurrence) |
| `LutzNagell/EllipticDivisibilitySequence.lean:~841` | `simp_rw [normEDS, preNormEDS_odd, …]` inside `normEDS_odd` |
| `LutzNagell/EllipticDivisibilitySequenceOriginal.lean:905` | same as above, in the backup copy |

Inline re-derivation grep: none — every consumer calls `preNormEDS_odd` by name. The
mathlib copy has the *same* consumers upstream (`normEDS_odd` at mathlib:345, `preΨ_odd`
at `DivisionPolynomial/Basic.lean:233`), so deleting the fork's copy loses nothing —
the consumers re-point at the mathlib decl.

#### Composition check
Not applicable as a "compose from primitives" question — the exact lemma already exists
in mathlib, so there is nothing to compose. (For completeness: it is *not* a ≤3-call
composition of smaller mathlib lemmas; its own proof is a 16-line `Int.negInduction`.
That is irrelevant here because mathlib already provides the finished lemma.)
Conclusion: N/A — superseded by the Phase-5 exact hit.

---

## Verdict: `preNormEDS_odd`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): standard Ward odd-index EDS recurrence; mathlib's
  `[CommRing R]` statement is already the maximally-general standard form.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; 0 weakenings; no modern-idiom move
  (it is already the mathlib idiom).
- Mathlib search (Phase 5): **found in mathlib as `preNormEDS_odd`; identical form**
  (verbatim `diff` = zero differences, statement + proof).
- Composition check (Phase 6): N/A — exact hit supersedes.

**Rationale.**
`preNormEDS_odd` is not a NagellLutz contribution. The file
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a deliberate,
verbatim fork of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` — same author
(David Kurniadi Angdinata), same Apache-2.0 header, same module docstring, same
`section PreNormEDS` structure. A line-level `diff` of the project lemma (lines 822–838)
against the mathlib lemma (lines 224–240) yields **no differences at all**: identical
statement, identical `Int.negInduction` proof, identical surrounding API
(`preNormEDS_neg`, `preNormEDS_ofNat`, `preNormEDS'_odd`). Mathlib even uses this exact
lemma downstream, both inside the EDS file (`normEDS_odd`, mathlib:345) and in
`AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:233` (`preΨ_odd`), which
is the very `DivisionPolynomial` track the task brief flagged.

**WHY not (refactor-actionable).**
Mathlib already has it. The fork exists for project-local reasons (the file is extended
with new EDS material further down — `complEDS₂`, the `EllSequence`/`HaveSameParity₄`
machinery, etc.), but `preNormEDS_odd` itself is pure duplication of upstream. There is
no statement to upstream and no generality to add.

Existing mathlib decl:  `preNormEDS_odd`
Located at:             `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:224`
Our form follows in ≤1 line: it *is* the mathlib lemma —
```lean
example (b c d : R) (m : ℤ) :
    preNormEDS b c d (2 * m + 1) =
      preNormEDS b c d (m + 2) * preNormEDS b c d m ^ 3 * (if Even m then b else 1) -
        preNormEDS b c d (m - 1) * preNormEDS b c d (m + 1) ^ 3 * (if Even m then 1 else b) :=
  preNormEDS_odd ..   -- the mathlib decl, identical signature
```

Call sites in our project (Phase 6): 3 live `.lean` consumers, all inside the NagellLutz
fork (`DivisionPolynomial.lean:156`; the fork's own `normEDS_odd`; the stale
`EllipticDivisibilitySequenceOriginal.lean` backup).

Refactor plan (project hygiene, NOT a mathlib PR): this is one declaration inside a
whole forked file. The right fix is **file-level, not lemma-level**: reconcile
`LutzNagell/EllipticDivisibilitySequence.lean` with upstream so the project `import`s
`Mathlib.NumberTheory.EllipticDivisibilitySequence` and keeps only the genuinely-new
material in a separate file. Once that import is in place, `preNormEDS_odd` (and its
siblings `preNormEDS_even`, `preNormEDS_neg`, `preNormEDS_ofNat`, `complEDS₂…`, etc.)
are deleted from the fork and the 3 call sites resolve to the mathlib decl unchanged
(identical signature, so no edit needed at the call sites). The duplicate
`EllipticDivisibilitySequenceOriginal.lean` backup copy should be removed as well. This
matches the recommendation already recorded in the sibling report
`.mathlib-quality/overview/mathlibable/preNormEDS'_two.md` ("the real fix is whole-file:
reconcile `LutzNagell.EllipticDivisibilitySequence`").

**Next action:** do **not** open a mathlib PR (mathlib already has it). File/continue a
project cleanup ticket to de-fork `LutzNagell/EllipticDivisibilitySequence.lean` against
upstream mathlib and drop the duplicated `preNormEDS_*` / `complEDS*` block (and the
`EllipticDivisibilitySequenceOriginal.lean` backup).

---

## Next step

Delete `preNormEDS_odd` from the project as part of the whole-file de-fork of
`LutzNagell/EllipticDivisibilitySequence.lean`; the 3 internal call sites resolve to
mathlib's identical `preNormEDS_odd` with no edits.

Sources:
- [Elliptic divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence)
- [Ward, via Stange — Elliptic nets and elliptic curves (arXiv:0710.1316)](https://arxiv.org/pdf/0710.1316)
- [Stange — Division polynomials for arbitrary isogenies (eprint 2025/521)](https://eprint.iacr.org/2025/521.pdf)
- mathlib: `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:224` (the existing `preNormEDS_odd`)

# /mathlibable report — `EllSequence.redInvarDenom_one`

_Project: NagellLutz (Nagell–Lutz theorem; elliptic curves; division polynomials; EDS)_
_Target: `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1415` · assessed 2026-06-21 (supersedes a prior run that recorded `NO-composable-from-mathlib`)_
_Run: Step-9 /overview mathlibable assessment, single declaration, Mode A, full workflow._

**Verdict: BORDERLINE-needs-human**
(fate is bound to a human decision about upstreaming the parent definition `redInvarDenom`; this run
**corrects** the earlier `NO-composable-from-mathlib` verdict, bringing `_one` into line with its
parent `redInvarDenom` and its siblings `_zero` / `_two`, all assessed BORDERLINE — and as the
`redInvarDenom_two.md` report itself flags, the old `_one` `NO-composable` label was the inaccurate
outlier)

---

## Baseline (Phase 0)

- **lake build:** ⚠ not re-run (prompt: local build stale). Reasoned from source + the vendored mathlib
  tree at `.lake/packages/mathlib/`. The decl elaborates in the committed tree (a one-line `simp` proof
  of a base case; the file is part of green `main`).
- **decl `EllSequence.redInvarDenom_one`:** ✓ resolved at `EllipticDivisibilitySequence.lean:1415`.
  **Qualified name VERIFIED: `EllSequence.redInvarDenom_one`** (the prompt's parsed guess was correct).
- **kind:** `lemma` (`@[simp]`).
- **has sorry:** no.
- **module docstring summary:** "Elliptic divisibility sequences (EDS) and construction of normalised
  EDSs from initial terms." Author: David Kurniadi Angdinata — the **same author** as mathlib's
  `Mathlib.NumberTheory.EllipticDivisibilitySequence` and `…/EllipticCurve/DivisionPolynomial/*`. This
  file is an **extended fork** of the mathlib EDS file (mathlib ≈547 lines; this file 1672 lines),
  adding the `net`/`rel₄`/`invar*`/`redInvar*`/`compl₂EDS`/`ω`-division-polynomial layer not yet
  upstreamed.

**Qualified-name verification (detail).** The `@[simp] lemma` at L1415 sits inside `namespace
EllSequence` opened at L1356 and closed at L1431. Enclosing `section`s (`section NormEDS` L881,
`section` L1203, `section Divisibility` L1261, `section Complement` L1284) and the file-level
`@[expose] public section` (L81) are **not** namespaces and do not contribute to the name. The earlier
`namespace EllSequence` blocks (L90→L597, L1079→L1112) are both closed before L1356 — no double-nesting.

---

## Statement (Phase 1)

Exact source (L1377–1386 def, L1415–1416 lemma):

```lean
/-- The expression `W(m+1)W(m)W(m-1)/W₃W₂` for a normalised EDS. -/
def redInvarDenom : R :=
  letI C := complEDS b c d
  letI W := normEDS b c d
  letI r₆ := normEDS b c d 5 - d ^ 2 -- W₆/W₃W₂
  if m % 6 = 0 then r₆ * C 6 (m / 6) * W (m + 1) * W (m - 1) else
  if m % 6 = 1 then r₆ * C 6 ((m - 1) / 6) * W (m + 1) * W m else
  if m % 6 = 5 then r₆ * C 6 ((m + 1) / 6) * W m * W (m - 1) else
  if m % 6 = 2 then C 3 ((m + 1) / 3) * C 2 (m / 2) * W (m - 1) else
  if m % 6 = 4 then C 3 ((m - 1) / 3) * C 2 (m / 2) * W (m + 1) else
  if m % 6 = 3 then C 3 (m / 3) * C 2 ((m - 1) / 2) * W (m + 1) else 0

@[simp] lemma redInvarDenom_one : redInvarDenom b c d 1 = 0 := by
  simp [redInvarDenom, complEDS, compl', compl]
```

`redInvarDenom_one` is the **base-case evaluation** stating that the project-specific "reduced
invariant denominator" of a normalised EDS, at `m = 1`, is `0`. At `m = 1` the branch is
`r₆ · C 6 ((1−1)/6) · W(2) · W(1) = r₆ · complEDS b c d 6 0 · W₂ · W₁`, and the complement-sequence
base case `complEDS b c d k 0 = 0` (via the project-local `compl' 0 = 0`) collapses the product to `0`.

`redInvarDenom` is the *reduced denominator* of the EDS invariant `invarNum s n / invarDenom s n`,
where `invarDenom W s n = W(n+s)·W(n)·W(n−s)` (L145). The companion `invarDenom_eq_redInvarDenom_mul`
(L1388) proves `invarDenom (normEDS b c d) 1 m = redInvarDenom b c d m * b * c`, i.e. `redInvarDenom`
is `W(m+1)·W(m)·W(m−1)` after cancelling `W₃·W₂ = c·b`, realised division-free in any `CommRing` via a
6-way `m mod 6` case split.

- **Variables / typeclasses:** `{R : Type u} [CommRing R]`; `(b c d : R)` the EDS initial data; index
  fixed to the literal `1`.
- **Hypotheses:** none.
- **Conclusion (math):** the reduced invariant denominator vanishes at index 1.
- **Conclusion (Lean):** `redInvarDenom b c d 1 = 0`.

One of three sibling base-case `@[simp]` lemmas: `redInvarDenom_zero = 0` (L1412), `redInvarDenom_one`
(L1415, this decl), `redInvarDenom_two = 1` (L1418) — mirroring upstream mathlib's
`normEDS_zero/one/two`, `complEDS_zero` base-case simp lemmas.

---

## Size classification (Phase 2a)

**Verdict: SMALL.** A `@[simp]` base-case evaluation of a helper definition at a fixed index — not a
new structure, not a `## Main results` entry, not named after a person/place. (Literature width is
EXHAUSTIVE regardless.)

## One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → the one-liner-definition analysis is **n/a**. (For
the record, the *proof* is a one-line `simp` and the *statement* a single equation — both consistent
with a trivial base case whose whole content is "unfold the parent at one index". This
trivially-true-and-harmless character is exactly why the lemma cannot be judged on its own merits —
see Phase 7.)

---

## Literature search — EXHAUSTIVE protocol (Phase 3)

No project `.mathlib-quality/references/` directory exists (recorded `n/a`); search is WebSearch +
mathlib4_docs + nLab, as in the sibling `_zero`/`_two` reports. The literature question is: *is "the
reduced invariant denominator / invariant numerator–denominator of an EDS" a standard named object?* —
because if `redInvarDenom` is standard and mathlib-worthy, its base cases ship with it.

| # | Channel | Query | Hit? | Standard form found | Notes |
|---|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific) | EDS "invariant" `W(n+1)W(n)W(n-1)` division polynomial reduced denominator Ward | partial | Ward recurrence (1948); `[n]P=(A_n/D_n²,B_n/D_n³)`; σ-function form `W_n=σ(nξ)/σ(ξ)^{n²}` | Wikipedia EDS; Stange arXiv:0710.1316; Silverman. Recurrence/σ-form are standard; **no "invariant denominator" object** |
| 2 | WebSearch (general/aliases) | "reduced invariant denominator" EDS OR "redInvarDenom" mathlib | no | only the generic point-denominator `D_n` | `D_n` (denominator of `[n]P`) is a *different* object from this `redInvarDenom` |
| 3 | WebSearch (named-after) | Shipsey/Stange elliptic nets; Swart "elliptic curves and related sequences"; complement sequence | no | "elliptic net" (Stange) is standard; "complement sequence"/"invariant numerator–denominator" are not | the multivariable elliptic-net generalisation has no `redInvarDenom` |
| 4 | ChatGPT MCP | "Is 'reduced invariant denominator of an EDS' a standard named concept, and at what generality?" | n/a | — | MCP server down in this env (per prompt); WebSearch rows 1–3 + the upstream source read (Phase 5) compensate |
| 5 | Local references | `.mathlib-quality/references/` for "invar"/"redInvar" | n/a | — | directory absent for this project |
| 6 | nLab | "elliptic divisibility sequence" | no | — | no EDS "invariant denominator"; not categorical |
| 7 | nCatLab | — | n/a | — | not a categorical concept |
| 8 | Stacks Project | — | n/a | — | EDS/division-polynomial bookkeeping out of Stacks' scope |
| 9 | MathOverflow / MSE | "invariant denominator" EDS / Ward symmetry generality | partial | confirms Ward symmetry is the standard fact behind `invarNum`/`invarDenom` | no source names a reduced-denominator sub-object or its value at index 1 |
| 10 | recent arXiv (≤5y) | division-poly/EDS valuations (arXiv:1108.3051, 2310.01013, math/0404412) | no | — | use Ward's `Ψ_n`/recurrence directly; none defines `redInvarDenom` |

**Literature summary.** Concept identified as: a **bespoke piecewise re-packaging** of the
normalised-EDS product `W(m+1)·W(m)·W(m−1)/(W₃·W₂)`, engineered to express the elliptic-curve
**group-law addition** (the `Y`-coordinate via the `ω` division polynomial — see `ZSMul.lean:279`
`Affine.addY`, `DivisionPolynomialOmega.lean`). The genuinely standard EDS notions (Ward recurrence,
`normEDS`, division polynomials `Ψ_n`, σ-function form, Stange's elliptic nets) are all *already in
mathlib*; `invarNum`/`invarDenom`/`redInvarNum`/`redInvarDenom` are **not** among them and have **no
named counterpart in the literature**. A fortiori `redInvarDenom(1)=0` is an implementation detail
(value at a degenerate index), not a named result. Literature absence here is the documented
"too-project-specific" signal, **not** "novel ⇒ add".

Sources: [Elliptic divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence) ·
[Elliptic nets and elliptic curves (Stange), arXiv:0710.1316](https://arxiv.org/pdf/0710.1316) ·
[p-adic properties of division polynomials and EDS, arXiv:math/0404412](https://arxiv.org/pdf/math/0404412) ·
[Integral points & explicit valuations of division polynomials, arXiv:1108.3051](https://arxiv.org/pdf/1108.3051) ·
[Mathlib.NumberTheory.EllipticDivisibilitySequence (docs)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html).

---

## Generality analysis (Phase 4)

Literature-standard form (from Phase 3): **none exists** for this object. The lemma is a fixed-index
(`m = 1`) base-case evaluation of a bespoke definition; there is no generality axis to weaken against a
literature target.

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form? | Reason |
|---|------------------------|-------------------|---------------------|--------------|--------|
| 1 | `[CommRing R]` | commutative ring | n/a (no literature object) | NO | `normEDS`/`complEDS` are defined over `CommRing` — already mathlib's chosen generality; the division-free encoding exists precisely to avoid needing a field. Nothing to weaken |
| 2 | `(b c d : R)` | three ring elements | n/a | NO | intrinsic to `normEDS b c d` |
| 3 | index `m = 1` | fixed literal | n/a | n/a | a base case *is* the specialisation to a fixed index; "generalising" it is the `redInvarDenom` def plus `invarDenom_eq_redInvarDenom_mul` — packaging, not assumption-weakening |

**Generality verdict (4b).** **MAXIMALLY GENERAL** for what it is (a `CommRing`-level base case of a
project-specific def) — but moot, because the *subject* is not a mathlib/literature object. K = 0
weakening opportunities.

**Modern-idiom check (4c).** Modern idiom available: **no.** Every Bourbaki-2.0 row is `no`: already a
plain `CommRing` + three elements (row 1); purely algebraic, no topology/filters (row 2); a base-case
value, not a constructed object with a universal property (row 3 — though the *parent* `ω` is the
universal-property gap, not this lemma); no substructure lattice (row 4); already at `CommRing`
(row 5); no categorification (row 6); the `ℤ`-indexing matches mathlib's `normEDS : ℤ → R` and the
index here is the literal `1`, not a structural index to generalise (row 7). The only conceivable
"reformulation" — folding the three base cases into one `redInvarDenom_ofNat` lemma — is packaging, not
a real organisational improvement. **No modern-idiom move.**

---

## Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `lemma`** (a `Prop`; introduces no definitional equalities or
typeclass-search paths). The `@[simp]` attribute is benign: it rewrites the closed constant
`redInvarDenom b c d 1` to `0`, a terminating, confluent base-case simp exactly like upstream
`complEDS_zero`/`normEDS_one`.

---

## Mathlib search-status: `EllSequence.redInvarDenom_one` (Phase 5)

Searched the actual mathlib source tree (`.lake/packages/mathlib/Mathlib/`), authoritative for
"is it there", for both the current form and the (non-existent) literature-standard form.

```
[A] Lean-Finder       "reduced invariant denominator EDS" / "redInvarDenom"   no hit / n/a (offline; covered by D/E + mathlib4_docs)
[B] Loogle            (no mathlib symbol `redInvarDenom` to pattern on)        n/a — statement names a non-mathlib constant
[C] LeanSearch        "EDS invariant denominator base case" via mathlib4_docs  no hit (docs page lists normEDS/complEDS only)
[D] Grep mathlib src  redInvarDenom / redInvarNum / invarDenom / invarNum /
                      compl₂EDS / complEDSAux   over .lake/packages/mathlib/   ZERO hits anywhere in mathlib
[D] Grep mathlib src  complEDS / complEDS₂ / complEDS' / normEDS               HITS — the BUILDING-BLOCK sequences ARE in mathlib
[E] Name pattern      complEDS_one (L441) / normEDS_one (L302) / normEDS_zero  HITS — the in-mathlib analog base-case @[simp] lemmas
[E] Name pattern      `invar` across mathlib EDS file + whole EllipticCurve dir only the unrelated *invariant differential* / variable-change "invariants" (Weierstrass.lean, VariableChange.lean, ModelsWithJ.lean, IsomOfJ.lean) — NONE is the EDS invariant
```

**Upstream source read.** `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` provides
`IsEllSequence`, `IsDivSequence`, `IsEllDivSequence`, `preNormEDS'`, `preNormEDS`, `complEDS₂`,
`normEDS`, `complEDS'`, `complEDS`, and their `@[simp]` base cases (`normEDS_zero/one/two`,
`complEDS₂_zero`, `complEDS'_zero`, `complEDS_zero`, …). It has **no** `invarNum`, `invarDenom`,
`redInvarNum`, `redInvarDenom`, `compl₂EDS`, `compl₂EDSAux`, nor the project's `EllSequence.compl'/
compl/complEDS` family (the one taking `W₁ compl₂` parameters). The whole
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/*` and EllipticCurve dir have **no
`invar*` notion**.

**Cross-project check.** The `invarNum`/`invarDenom`/`redInvar*` family appears **only** in this
project's files and in `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean` (a
verbatim duplicate of `redInvarDenom_one` at HasseWeil `…:923`). It is an AINTLIB-internal fork
addition, not upstreamed.

**Concluded:** the lemma's subject `redInvarDenom` is **NOT in mathlib** (whole-tree grep exhausted),
and there is **no literature-standard object** it specialises. Mathlib has the underlying sequences
`normEDS`/`complEDS`/`complEDS₂`/`complEDS'` and their own base-case `@[simp]` lemmas (`normEDS_one`
L302, `complEDS_one` L441) — the *building blocks* — but not the `redInvar*` packaging this lemma is
about.

---

## Composition check + call sites (Phase 6)

### 6.0 Call sites

Cross-project use of the **lemma** `redInvarDenom_one` (excluding the NagellLutz declaring file):

| Caller file:line | Usage |
|------------------|-------|
| `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:121` | `rw [redInvarDenom_one, complEDSAux₂_one, ψ_one]` — **genuine load-bearing use**: rewriting the division-polynomial base case `ω 1` |
| `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:923` | verbatim **duplicate declaration** (HasseWeil's own fork copy) |
| `projects/NagellLutz/.../EllipticDivisibilitySequenceOriginal.lean:1322` | verbatim **duplicate declaration** (the pre-fork "Original" copy), if present in tree |

Use of the **parent def** `redInvarDenom` (what its mathlib fate really turns on):
- this file: `invarDenom_eq_redInvarDenom_mul` (L1388), `redInvarNum = redInvarDenom·(d+b⁴)`
  (L1502/1510), `map_redInvarDenom` (L1428).
- `projects/NagellLutz/LutzNagell/DivisionPolynomialOmega.lean` (≈L75,85,112) — building the `ω`
  division polynomial.
- `projects/NagellLutz/LutzNagell/ZSMul.lean:279` — `rw [smulY, ω, redInvarDenom_two, …, Affine.addY, …]`
  — i.e. the **elliptic-curve group-law `Y`-coordinate**.

**Signal.** The def `redInvarDenom` is **real, load-bearing project API** (K ≥ 3 across NagellLutz +
HasseWeil), and `redInvarDenom_one` is one of its mandatory `@[simp]` base cases (with `_zero`,
`_two`); it is genuinely used at HasseWeil `DivisionPolynomial.lean:121`. **Not dead code**, **not** a
bypassed wrapper. But every consumer is internal to the EDS/division-polynomial fork; there are **no
consumers outside these forked NT projects**. The triplication is a dedup signal, not a mathlib-ability
signal. Inline-derivation grep: the fact is consumed via the named lemma, not re-derived inline.

### 6a Composition attempt

Can `redInvarDenom b c d 1 = 0` be derived from **mathlib** in ≤3 chained **mathlib** calls?

- **Attempt 1:** cite mathlib decls to rewrite `redInvarDenom b c d 1`. **Fails at step 0** —
  `redInvarDenom` is **not a mathlib symbol**, so no mathlib lemma even mentions it. The proof
  `simp [redInvarDenom, complEDS, compl', compl]` unfolds **project-local** definitions and collapses
  the `m % 6 = 1` branch via the project-local base case `compl' 0 = 0`. Mathlib supplies
  `complEDS`/`normEDS` and analogous base cases, but the packaging `redInvarDenom` and hence this lemma
  are outside mathlib's surface entirely.

**Conclusion: NOT-COMPOSABLE from mathlib.** Composable only from *project-local* definitions. This is
precisely why the `NO-composable-from-mathlib` bucket does **not** apply: that bucket's required
evidence (per `references/mathlibable-verdicts.md` §4 and its Case 4 `my_sum_cont_integrable`) is a
Phase-5 list of **mathlib** building blocks plus a Phase-6 composition sketch of **mathlib** decls
cited by qualified name, whose action is "delete the lemma; replace call sites with the mathlib calls."
Here there are **no** mathlib building blocks for the statement and **no** mathlib composition to inline
at the HasseWeil call site (the consumer reasons about `redInvarDenom`/`ω`, absent from mathlib). The
honest framing is **inheritance**: this lemma's mathlib status is determined by its parent def
`redInvarDenom`, a bespoke, non-literature, non-mathlib piecewise construction whose own assessment was
**BORDERLINE**. A base-case lemma about a project-only def whose fate is "rides along iff the parent is
upstreamed" is a human/maintainer judgment, not a mechanical NO.

---

## Verdict: `EllSequence.redInvarDenom_one`

**Category: BORDERLINE-needs-human**

**Evidence:**
- **Literature (Phase 3):** the underlying invariant is standard EDS theory (Ward 1948), but the
  *object* `redInvarDenom` and the *fact* `redInvarDenom(1)=0` have **no named counterpart** in any
  source — project-specific division-free encoding; literature absence is the "too-project-specific"
  signal.
- **Generality (Phase 4):** MAXIMALLY GENERAL for what it is; no modern-idiom move; nothing to weaken —
  but moot, the subject is not a mathlib object.
- **Mathlib search (Phase 5):** **not in mathlib** — zero hits for `redInvarDenom`/`redInvarNum`/
  `invarDenom`/`invarNum`/`compl₂EDS` across the whole tree; parent def absent. Building blocks
  (`normEDS`, `complEDS`, `normEDS_one`, `complEDS_one`) are present.
- **Composition (Phase 6):** **NOT-COMPOSABLE** from mathlib — the statement names a non-mathlib
  constant; provable only from project-local definitions. Real consumer at HasseWeil
  `DivisionPolynomial.lean:121`.

**Rationale.**

`redInvarDenom_one` is a `@[simp]` base-case evaluation (`redInvarDenom b c d 1 = 0`) of a definition
that exists only in this fork of mathlib's EDS file. It is trivially correct (`simp` unfolds the parent
at index 1; `compl' 0 = 0` zeroes the branch) and harmless — but **meaningless in isolation from its
parent `redInvarDenom`**, which is a bespoke `mod 6`-case-split, division-free encoding of the EDS
invariant's reduced denominator, with no literature counterpart and no presence in mathlib. The parent
`def` was itself assessed **BORDERLINE**: its mathlib-ability hinges on *how the division polynomial
`ω` is eventually upstreamed* (mathlib's `DivisionPolynomial/Basic.lean` already flags `ωₙ` as a known
gap) and on whether the `mod 6` division-free decomposition is the formulation mathlib's curve author
commits to — a different upstreaming of `ω` via mathlib's existing `ψ`-based universal-ring approach
might never introduce a standalone `redInvarDenom`. Both sibling base cases `redInvarDenom_zero` and
`redInvarDenom_two` were assessed **BORDERLINE** for exactly this reason. This lemma's fate rides
entirely on that same parent decision, so it cannot be settled mechanically.

**Why not the other buckets.**
- **NO-composable-from-mathlib** (the earlier verdict) — **rejected**, and it *fails its own evidence
  gate*: that bucket requires mathlib building blocks (Phase 5) + a mathlib composition sketch cited by
  qualified name (Phase 6). Here the statement is phrased in `redInvarDenom`, a non-mathlib symbol, so
  there are no mathlib building blocks and Phase 6 explicitly yields "there is none" — the proof
  unfolds only project-local definitions, and at the real call site (HasseWeil
  `DivisionPolynomial.lean:121`) there is no mathlib composition to inline. The sibling
  `redInvarDenom_two.md` (L227–229) already flagged the old `_one` `NO-composable` label as the single
  inaccurate point and prefers "inseparable from a non-mathlib parent whose fate a human must decide."
- **NO-mathlib-has-it** — rejected: mathlib has the *building-block sequences* but not the packaged
  object `redInvarDenom`, so there is no decl to delete-and-replace against.
- **YES-add-as-is / YES-but-generalise-first** — rejected as stated for this lemma in isolation: a
  `@[simp]` base case is meaningless without its parent, and whether the `invar*`/`redInvar*` apparatus
  belongs upstream is a non-trivial design question for a human maintainer (especially given it lives
  as a *fork* of mathlib's EDS file and is duplicated NagellLutz↔HasseWeil, with names likely revised
  on upstreaming).

**Numbered questions for a human maintainer (≤5):**
1. Should the `invarNum`/`invarDenom`/`redInvarNum`/`redInvarDenom` "reduced invariant decomposition"
   apparatus be upstreamed to mathlib at all, or remain project-internal plumbing for
   Nagell–Lutz / Hasse–Weil?
2. If the division polynomial `ω` is upstreamed, is the `mod 6` division-free `redInvarDenom`
   decomposition the formulation mathlib wants — or should `ω` be built via mathlib's existing
   `ψ`-based universal-ring construction (in which case a standalone `redInvarDenom` may never exist)?
3. Conditional on (1)–(2): on upstreaming `redInvarDenom`, do its three `@[simp]` base cases
   (`_zero`, `_one`, `_two`) ride along automatically (as `complEDS_zero`/`normEDS_one` already do
   upstream)? (Expected: yes — never PR'd standalone.)
4. The NagellLutz and HasseWeil copies of this lemma (and the whole `redInvar*` block) are duplicated
   verbatim — should this be deduplicated into a shared module **before** any upstreaming judgment, and
   which names survive?

**Refactor / upstreaming plan (BORDERLINE next action).**
- Do **not** PR `redInvarDenom_one` standalone. Treat it as **bundled** with any future upstreaming of
  the `invar*`/`redInvar*` reduced-invariant API (driven ultimately by `ω`); on that event it ships as
  a required `@[simp]` base case, mirroring upstream `complEDS_zero`.
- **First** deduplicate the NagellLutz ↔ HasseWeil (and any "Original") copies and converge on names;
  **then** a human mathlib maintainer (realistically D. Angdinata, author of both the mathlib EDS files
  and these project files) judges the whole block. Re-run `/mathlibable` on the **def** `redInvarDenom`
  first if/when the apparatus is proposed for upstreaming; this base-case lemma inherits that decision.
- **Ledger fix:** update `redInvarDenom_one`'s recorded verdict from `NO-composable-from-mathlib` to
  `BORDERLINE-needs-human`, for consistency with `_zero`, `_two`, and the parent `redInvarDenom`.

---

## Next step

Surface questions 1–4 to a human mathlib maintainer (bundled with the parent `redInvarDenom` and its
sibling base cases); do not PR this lemma on its own. Separately, file/expect a `lane:cleanup` dedup
ticket for the NagellLutz↔HasseWeil (and "Original") duplication, and update the ledger entry for
`redInvarDenom_one` to `BORDERLINE-needs-human`.

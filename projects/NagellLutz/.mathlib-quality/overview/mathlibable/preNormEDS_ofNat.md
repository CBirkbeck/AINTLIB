# /mathlibable report — `preNormEDS_ofNat`

**TL;DR verdict: `NO-mathlib-has-it`.** This declaration is a *verbatim copy* of a
lemma that already exists in mathlib at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:180` — same name, same
signature, same proof body, same `@[simp]` attribute. The NagellLutz project
deliberately forks the mathlib EDS file (`Mathlib.NumberTheory.EllipticDivisibilitySequence`)
to avoid a `normEDS`/`complEDS` name clash; this lemma rode along in the fork.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task brief); decl read directly from source
- decl `preNormEDS_ofNat`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:778`
- kind:                     `lemma`
- has sorry:                no
- module docstring summary: "Elliptic divisibility sequences (EDS) and the construction of normalised EDSs from initial terms" — a fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

Qualified name: **`preNormEDS_ofNat`** (the declaration sits in `section PreNormEDS`
with **no enclosing `namespace`**, so the base name *is* the fully-qualified name).
The task's parsed name is confirmed correct.

---

### Statement (Phase 1)

`preNormEDS_ofNat` states that the integer-indexed auxiliary EDS sequence
`preNormEDS b c d : ℤ → R`, when evaluated at a *natural-number* argument
`(n : ℕ)` (coerced into `ℤ`), agrees with the natural-indexed auxiliary sequence
`preNormEDS' b c d : ℕ → R`:

> For every `n ∈ ℕ`,  `preNormEDS b c d (↑n) = preNormEDS' b c d n`.

Mathematically this is the compatibility/"restriction" identity between the
ℤ-extension `preNormEDS` and its underlying ℕ-sequence `preNormEDS'`. The
ℤ-version is defined by `preNormEDS n = (Int.sign n) • preNormEDS' …|n|`, so on
non-negative inputs the sign factor is `1` and the two coincide. It is a pure
bookkeeping bridge lemma, tagged `@[simp]` so the simplifier can always push a
ℤ-indexed term at a nat literal down to the ℕ-sequence.

Variables / typeclasses (Lean side):
- `{R : Type u}` with `[CommRing R]` — the coefficient ring.
- `(b c d : R)` — the EDS initial-data parameters (section-level `variable (b c d : R)`).
- `(n : ℕ)` — the index.

Hypotheses: none.

Conclusion (math): `preNormEDS b c d n = preNormEDS' b c d n` for `n : ℕ`.
Conclusion (Lean): `preNormEDS b c d ↑n = preNormEDS' b c d n`.

Proof body (identical in project and mathlib):
```lean
by_cases hn : n = 0
· simp [hn, preNormEDS]
· simp [preNormEDS, Int.sign_natCast_of_ne_zero hn]
```

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a glue/bridge lemma connecting a ℤ-indexed definition to its ℕ-indexed
core; not a named theorem, not a new structure, not a project main result.

### One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. (For completeness: it is a
two-branch `by_cases` proof, not a one-liner def. The one-liner exemption table
does not apply to lemmas.)

---

### Literature search (Phase 3)

This is a **library-internal bookkeeping lemma** about a mathlib-specific
construction (`preNormEDS` / `preNormEDS'`, an implementation device for building
normalised EDSs from initial terms, due to D. Angdinata). There is no external
mathematical "standard form" for a ℤ↔ℕ index-compatibility lemma of a particular
recursive sequence — the relevant authority is mathlib itself, where the
construction was introduced. The search nonetheless ran across channels to
confirm there is no broader literature object this specialises.

| #  | Channel                          | Query                                                                 | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "preNormEDS" / "normalised elliptic divisibility sequence" auxiliary   | n/a  | —                   | `preNormEDS`/`preNormEDS'` are mathlib-coined names for an implementation device; no external "preNormEDS_ofNat" object exists in the literature |
|  2 | WebSearch (general form)         | elliptic divisibility sequence definition ℤ vs ℕ indexing             | partial | EDS defined on ℤ (Ward 1948; Shipsey; Stange) | the math literature defines EDS on **ℤ** directly; the ℕ-core + sign-extension split is a *formalisation* artifact, not a literature notion |
|  3 | WebSearch (named-after/aliases)  | Ward recurrence / Somos / division-polynomial sequence indexing       | n/a  | —                   | named theory (Ward's elliptic sequences) concerns the recurrence + divisibility, not an index-coercion lemma |
|  4 | ChatGPT MCP                      | (per task: MCP may be down; used WebSearch fallback)                   | n/a  | —                   | substituted by channels 1–3, 6, plus the decisive mathlib-source comparison in Phase 5 |
|  5 | Local references                 | grep `.mathlib-quality/references/` (NagellLutz)                       | n/a  | —                   | no references dir present for this project subtree; recorded n/a |
|  6 | nLab                             | "elliptic divisibility sequence"                                      | partial | EDS concept page | nLab/encyclopedic coverage treats EDS abstractly on ℤ; no ℤ↔ℕ bridge lemma of a specific recursion |
|  7 | nCatLab (categorical)            | —                                                                      | n/a  | —                   | not a categorical concept |
|  8 | Stacks Project (alg geom)        | —                                                                      | n/a  | —                   | not a Stacks-style algebraic-geometry statement; it is a recursion-bookkeeping lemma |
|  9 | MathOverflow / MSE               | EDS extension to negative indices                                     | partial | sign/oddness symmetry `W(-n) = -W(n)` is standard | confirms the ℤ-extension exists in literature via the antisymmetry, but the **ℕ-core split** is a mathlib implementation choice |
| 10 | arXiv (last 5 yrs)               | elliptic divisibility sequences formalization Lean                    | partial | Angdinata–Xu EllipticCurve formalisation | the *source* of this construction is the mathlib formalisation itself |

### Literature summary (Phase 3)

Concept identified as: an **index-compatibility (`ofNat`) lemma** for mathlib's
`preNormEDS` auxiliary construction — i.e. "the ℤ-indexed sequence restricts to
the ℕ-indexed sequence on naturals."
Sources agree on the standard form: n/a — there is no external literature object;
the literature defines EDS directly on ℤ and the ℕ-core + sign-extension is a
mathlib *implementation* decomposition. The canonical authority is mathlib, which
already contains exactly this lemma.
Most general standard form: the lemma is already stated over an arbitrary
`CommRing R` with arbitrary parameters `b c d : R` — maximal for the construction.
Disagreement with the literature: none (no literature object to disagree with).

---

### Generality analysis (Phase 4)

Literature-standard form: n/a (library-internal lemma). Compare instead against
the mathlib original — which is identical.

| # | Parameter / hypothesis | Current Lean form | mathlib form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring (mathlib `variable {R} [CommRing R]`) | NO | `preNormEDS` is defined via `Int.sign • …`; needs at least a ring with the EDS recurrence; mathlib already settled on `CommRing` |
| 2 | `(b c d : R)`          | ring elements     | ring elements | NO | the EDS initial data; cannot be weakened |
| 3 | `(n : ℕ)`              | nat index         | nat index     | NO | the lemma's entire content is the ℕ→ℤ coercion case |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it is byte-identical to mathlib's, which
is the canonical maximal form for this construction).
Number of weakening opportunities found: 0.
Cost of restatement: n/a — no restatement applicable.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Notes |
|----|----------|----------|-------|
|  1 | bundled-hyps → typeclasses? | no | already minimal: a `CommRing` instance + ring-element parameters |
|  2 | sequences/metric → filters/topology? | no | finite algebraic recursion; no limit notion |
|  3 | construction → universal property? | no | it is a compatibility lemma about an existing recursive def, not a construction |
|  4 | set+closure-pred → bundled substructure? | no | not a substructure statement |
|  5 | vector-space/field-specific → weaken typeclass? | no | already `CommRing`, the natural home |
|  6 | 1-categorical → higher-categorical? | no | not categorical |
|  7 | concrete index → general additive structure? | no | the index *is* the point (ℕ vs ℤ); generalising it away deletes the lemma |

Modern idiom available: **no.** The lemma is the canonical mathlib formulation;
there is no cleaner contemporary idiom — indeed mathlib *chose* this exact form.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no new definitional equalities or
typeclass-search paths introduced).

---

### Mathlib search-status: `preNormEDS_ofNat`

[A] Lean-Finder       "preNormEDS ofNat" / "preNormEDS nat coercion"  → hit (mathlib EDS file)
[B] Loogle            `preNormEDS _ _ _ (Nat.cast _) = preNormEDS' _ _ _ _`  → hit (the lemma itself)
[C] LeanSearch        "auxiliary EDS sequence on naturals equals integer version"  → hit (mathlib)
[D] Grep mathlib src  `grep -rn "preNormEDS_ofNat" .lake/packages/mathlib/`  → **direct hit, declaration body identical**
[E] Name pattern      `preNormEDS_ofNat` exact name  → hit at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:180`

Searched for both the current form and the (n/a) literature-standard form.

**Decisive grep result:**
```
.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:180:
  lemma preNormEDS_ofNat (n : ℕ) : preNormEDS b c d n = preNormEDS' b c d n := by
```
The mathlib declaration (lines 179–183) is **character-for-character identical** to
the project's (lines 777–781): same `@[simp]`, same name, same signature, same
`by_cases hn : n = 0` / `simp [...]` proof. Same surrounding context: both sit in
`section PreNormEDS` over `variable {R} [CommRing R]` + `variable (b c d : R)`, no
namespace. It is additionally *used* inside mathlib at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:199`.

Concluded: **found in mathlib as `preNormEDS_ofNat` (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:180`); identical form.**

---

### Call sites — `preNormEDS_ofNat` (Phase 6.0)

Internal use count (NagellLutz project, excluding the declaring file
`EllipticDivisibilitySequence.lean` and the parallel duplicate
`EllipticDivisibilitySequenceOriginal.lean`): **1 distinct external file.**

| Caller file:line | Usage pattern |
|------------------|---------------|
| `LutzNagell/DivisionPolynomial.lean:122` | `preNormEDS_ofNat ..` (rewriting/closing a div-poly EDS step) |

Same-file uses (within the fork itself): `EllipticDivisibilitySequence.lean:817`,
`:831` (`simpa only [preNormEDS_ofNat] using preNormEDS'_even/_odd ..`), `:899`
(`simp_rw [normEDS, preNormEDS_ofNat, …]`).
Parallel copy `EllipticDivisibilitySequenceOriginal.lean` re-declares + uses the
same lemma at `:732`, `:771`, `:785`, `:850` — a second forked copy in the same
project.

Inline-derivation grep: none re-derive the identity inline; they all call
`preNormEDS_ofNat`. This is exactly how mathlib uses its own copy — confirming
the lemma is a genuine, used bridge, but one that **already exists upstream**.

### Composition check (Phase 6)

Can `preNormEDS_ofNat` be derived from mathlib in ≤3 chained calls?

Attempt 1 (the decisive one): `exact preNormEDS_ofNat` — i.e. the *literal mathlib
lemma of the same name*. The project would not need to *compose* anything; it would
simply use mathlib's `preNormEDS_ofNat` directly, were it importing the mathlib EDS
file instead of the local fork.
  - Mathlib decls used: `preNormEDS_ofNat` (and, if one re-proved it, `Int.sign_natCast_of_ne_zero`).
  - Result: succeeds (0-step — it *is* the mathlib lemma).

Conclusion: **NOT-COMPOSABLE in the "build it from primitives" sense — because it
does not need to be built at all. Mathlib already has the finished lemma.** This
routes the verdict to `NO-mathlib-has-it`, not `NO-composable-from-mathlib`.

---

## Verdict: `preNormEDS_ofNat`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): no external object; the construction `preNormEDS` originates in mathlib, which is the authority. No broader form to chase.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — identical to mathlib's, over arbitrary `CommRing`.
- Mathlib search (Phase 5): **found in mathlib as `preNormEDS_ofNat` at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:180`; identical form** (same name, signature, proof, `@[simp]`).
- Composition check (Phase 6): NOT-COMPOSABLE — no need to compose; the finished lemma is upstream and is even used inside mathlib (`DivisionPolynomial/Basic.lean:199`).

**Rationale:**

This project (`NagellLutz`) intentionally **forks** mathlib's
`Mathlib.NumberTheory.EllipticDivisibilitySequence` into
`LutzNagell/EllipticDivisibilitySequence.lean`. The header of the sibling
`LutzNagell/DivisionPolynomial.lean` states the reason verbatim: it "imports
`LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid
name conflicts (both define `normEDS`, `complEDS`, etc.)." `preNormEDS_ofNat` is
one of the many lemmas carried along in that copy. The copy is exact: the
project's lines 777–781 match mathlib's lines 179–183 to the character, the
surrounding `section PreNormEDS` / `variable {R} [CommRing R]` / `variable (b c d :
R)` context matches, and mathlib already *consumes* the lemma internally
(`DivisionPolynomial/Basic.lean:199`).

Therefore the answer to "should mathlib have this?" is "mathlib already does, and
this is a duplicate of it." There is nothing to upstream. This is the canonical
`NO-mathlib-has-it` situation — the strongest possible form of it, since it is not
merely subsumed by a more general mathlib result but is the *identical declaration*.

**WHY not (refactor-actionable):**
Mathlib already has `preNormEDS_ofNat` with the identical statement and proof.
Our form does not "follow in ≤1 line" — it *is* the same line.

- Existing mathlib decl:   `preNormEDS_ofNat`
- Located at:              `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:180`
- Our form is identical:
  ```lean
  -- mathlib (line 180) and project (line 778) are byte-identical:
  @[simp] lemma preNormEDS_ofNat (n : ℕ) : preNormEDS b c d n = preNormEDS' b c d n := by
    by_cases hn : n = 0
    · simp [hn, preNormEDS]
    · simp [preNormEDS, Int.sign_natCast_of_ne_zero hn]
  ```
- Call sites in our project (Phase 6.0): **1 external** (`DivisionPolynomial.lean:122`),
  plus 3 in-fork uses and a second forked copy in
  `EllipticDivisibilitySequenceOriginal.lean`.

**Refactor plan (note: this is a deliberate fork — see caveat below).**
The orthodox `NO-mathlib-has-it` action would be: delete the local
`preNormEDS_ofNat` and have every call site use mathlib's `preNormEDS_ofNat` by
importing `Mathlib.NumberTheory.EllipticDivisibilitySequence`. **However**, the
project header documents that the *entire* EDS file was forked precisely to dodge a
`normEDS`/`complEDS` namespace clash with mathlib. So `preNormEDS_ofNat` cannot be
deleted in isolation — it is structurally tied to the whole forked module. The
real refactor is the **file-level one**: reconcile the `NagellLutz` EDS/division-
polynomial fork with upstream mathlib (e.g. open the mathlib EDS namespace under an
alias, or upstream whatever genuinely-new NagellLutz lemmas exist and drop the
copy), at which point this lemma and its siblings disappear automatically. That is
a consolidation decision for the maintainers, not a one-lemma edit.

**Next action:** do **not** PR `preNormEDS_ofNat` to mathlib (it is already there).
Treat it as part of the NagellLutz↔mathlib EDS de-duplication: file/track a
consolidation ticket to retire the forked `EllipticDivisibilitySequence` (and the
duplicate `…Original`) copy against upstream mathlib, rather than touching this
lemma alone.

---

## Next step

Do not PR to mathlib — `preNormEDS_ofNat` already exists upstream verbatim at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:180`. Fold this into the
project-level decision to retire the deliberate `NagellLutz` EDS fork against
mathlib (the fork exists to avoid a `normEDS`/`complEDS` name clash, so the lemma
is removed as part of reconciling the whole module, not in isolation).

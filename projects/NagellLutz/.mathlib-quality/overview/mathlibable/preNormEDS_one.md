# /mathlibable report — `preNormEDS_one`

## Verdict: **NO-mathlib-has-it**

> **One-line:** This is a verbatim fork of an existing mathlib lemma. Mathlib already
> has `preNormEDS_one` (same statement, same proof, same author) at
> `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:190`.

---

### Baseline (Phase 0)
- lake build:               stale locally (read elaborated form from source; statement is a
                            trivial `simp` evaluation, no ambiguity)
- decl `preNormEDS_one`:    resolved at
                            `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:788`
- kind:                     lemma (`@[simp]`)
- has sorry:                no
- module docstring summary: Elliptic divisibility sequences (EDS); defines `preNormEDS'`,
                            `preNormEDS`, `normEDS`, `complEDS` from initial terms. The file
                            header explicitly carries the **mathlib copyright**
                            (David Kurniadi Angdinata, 2024) — i.e. this file *is* a fork of
                            `Mathlib.NumberTheory.EllipticDivisibilitySequence`, extended with
                            the project's own `EllSequence` / `complEDS` material.

### Qualified name (verified)
The prompt's guessed `preNormEDS_one` is **correct**. Tracing every `namespace`/`end`
before line 788 in the project file:
`namespace EllSequence` (90) … `end EllSequence` (597); `namespace IsEllSequence` (643) …
`end IsEllSequence` (702). The declaration then sits inside `section PreNormEDS` (opened
line 704) — a **`section`, not a `namespace`** — so it carries **no namespace prefix**.
Fully-qualified name: **`preNormEDS_one`**.

---

### Statement (Phase 1)

`preNormEDS_one` states that the auxiliary pre-normalised elliptic divisibility sequence
`preNormEDS b c d : ℤ → R` evaluates to `1` at the index `1`:
$$ \mathrm{preNormEDS}\,(b,c,d)\,(1) = 1. $$
It is one of the five base-case evaluation lemmas (`_zero, _one, _two, _three, _four`) that
pin down the initial values `W(0)=0, W(1)=1, W(2)=1, W(3)=c, W(4)=d` of Ward's normalised
EDS, lifted from the `ℕ`-indexed `preNormEDS'` to the `ℤ`-indexed `preNormEDS` via
`preNormEDS n = sign(n) · preNormEDS'(|n|)`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring (maximal sensible generality for EDS).
- `(b c d : R)` — the three parameters defining the sequence's initial data.

Hypotheses: none.

Conclusion (math): `preNormEDS(b,c,d)(1) = 1`.
Conclusion (Lean): `preNormEDS b c d 1 = 1`.

Exact source text (project, lines 787–789):
```lean
@[simp]
lemma preNormEDS_one : preNormEDS b c d 1 = 1 := by
  simp [preNormEDS]
```

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line base-case `@[simp]` evaluation lemma; not a named theorem, not a new
structure, not a `## Main results` entry.

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-liner exemption table is **n/a**.
(The body is the single tactic `simp [preNormEDS]`.)

---

### Mathlib search (Phase 5) — DECISIVE

This phase resolves the verdict on its own; the remaining phases are recorded for
completeness but cannot change a direct exact-name, exact-statement hit.

```
### Mathlib search-status: `preNormEDS_one`

[A] Lean-Finder       "preNormEDS one base value 1"        local index stale; superseded by [D]
[B] Loogle            preNormEDS, (preNormEDS _ _ _ 1 = 1) superseded by exact-name hit [D]
[C] LeanSearch        "pre-normalised EDS value at one"    superseded by exact-name hit [D]
[D] Grep mathlib src  "preNormEDS_one" in
                      .lake/packages/mathlib/Mathlib/      HIT — exact name + identical body
[E] Name pattern      lemma preNormEDS_one                 HIT — single match, mathlib EDS file
```

**HIT.** `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:189–191`:
```lean
@[simp]
lemma preNormEDS_one : preNormEDS b c d 1 = 1 := by
  simp [preNormEDS]
```
`diff` of the project lines 787–789 against mathlib lines 189–191 reports **IDENTICAL**
(verified via shell `diff`). The supporting `def preNormEDS` (mathlib line 176) is likewise
identical to the project's (line 774), so the definition this lemma is *about* is also
already in mathlib, at the same `[CommRing R]` generality. Same `@[simp]` attribute, same
namespace situation (bare `section PreNormEDS`, no prefix), same author/copyright header.

Concluded: **found in mathlib as `preNormEDS_one`; identical form** (not merely a more
general form — the *same* lemma, byte-for-byte).

---

### Literature search (Phase 3) — for completeness

The decl is a base-case evaluation of a definition that mathlib already owns, so the
literature question reduces to "is Ward's normalised EDS the right object?" — which mathlib
already answered when it accepted this file. Recorded briefly:

| # | Channel              | Query                                             | Hit | Standard form                         | Notes |
|---|----------------------|---------------------------------------------------|-----|---------------------------------------|-------|
| 1 | WebSearch (specific) | "elliptic divisibility sequence initial values W(1)=1" | yes | `W_0=0, W_1=1, W_2, W_3, W_4` standard normalisation | Ward 1948 (Memoir on EDS); the file's cited reference |
| 2 | WebSearch (general)  | "normalised elliptic divisibility sequence definition commutative ring" | yes | defined over any comm. ring | matches the `[CommRing R]` of both copies |
| 3 | WebSearch (aliases)  | "division polynomial recurrence base case psi_1 = 1" | yes | `ψ₁ = 1` is the universal convention | `preNormEDS` underlies the n-division polynomials |
| 4 | ChatGPT MCP          | (MCP down in this env — fallback to refs/WebSearch) | n/a | — | superseded by mathlib exact hit; not load-bearing |
| 5 | Local references     | `.mathlib-quality/references/` for NagellLutz     | n/a | dir absent | no references dir in this project |
| 6 | nLab                 | "elliptic divisibility sequence"                  | yes | normalisation `W₁=1` standard | confirms convention |
| 7 | nCatLab              | —                                                 | n/a | not a categorical concept | — |
| 8 | Stacks Project       | —                                                 | n/a | not the right register (classical NT, not scheme-theoretic AG) | — |
| 9 | MathOverflow         | "elliptic divisibility sequence normalisation"    | yes | `W₁=1` universal | — |

### Literature summary (Phase 3)
Concept identified as: **(pre-)normalised elliptic divisibility sequence** (Ward); the
initial value `W(1) = 1` is the universal normalisation convention.
Sources agree on the standard form: yes — `W₁ = 1` is conventional everywhere.
Most general standard form: `preNormEDS b c d 1 = 1` over an arbitrary commutative ring —
exactly the Lean statement. No generality is lost.

---

### Generality analysis (Phase 4)

| # | Parameter / hyp | Current Lean form | Literature-standard | Weaker form? | Reason |
|---|-----------------|-------------------|---------------------|--------------|--------|
| 1 | `[CommRing R]`  | commutative ring  | commutative ring    | NO           | EDS recurrences need both `+` and `*` with full ring structure; `CommRing` is the standard and maximal home. mathlib uses exactly this. |
| 2 | `(b c d : R)`   | three ring params | three ring params   | NO           | intrinsic to the definition. |
| 3 | index `1`       | the literal `1 : ℤ` | the literal `1`   | NO           | this is a base-case evaluation *at a fixed index*; there is nothing to generalise. |

**Generality verdict (Phase 4b):** MAXIMALLY GENERAL. K = 0 weakening opportunities.
The form is identical to mathlib's, which is already at `CommRing` — the literature-standard
and maximal setting.

**Modern-idiom check (Phase 4c):** Modern idiom available: **no**. This is a concrete
finite evaluation of a recursively-defined sequence at a fixed index; there is no
typeclass/filter/universal-property/bundling reformulation to make (and mathlib, which sets
the idiom here, already chose this exact statement). Rows 1–7 all `no`.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (introduces no definitional equality or instance-search
path).

---

### Composition check (Phase 6)

#### Call sites (Phase 6.0)
Internal use count (project, excluding the declaring `EllipticDivisibilitySequence.lean:788`): **3**
| Caller file:line | Usage |
|------------------|-------|
| `LutzNagell/DivisionPolynomial.lean:130` | `preNormEDS_one ..` |
| `LutzNagell/EllipticDivisibilitySequence.lean:1077` | `rw [preNormEDS_one, preNormEDS_two, preNormEDS_four, …]` |
| `LutzNagell/EllipticDivisibilitySequenceOriginal.lean:1026` | `rw [preNormEDS_one, …]` (the project's own second copy of the file) |

Inline re-derivation grep: the lemma is re-declared verbatim in
`EllipticDivisibilitySequenceOriginal.lean:742` — i.e. the project keeps **two forked copies**
of the same mathlib file. This *strengthens* NO-mathlib-has-it: the local copies are
redundant with mathlib, not novel.

The call sites confirm the lemma is genuinely used — but every one of those uses would be
satisfied identically by the mathlib lemma of the same name once the fork drops its private
copy. The K = 3 internal-use signal does **not** push toward YES here, because the
*identical lemma already lives in mathlib*; the uses are evidence the lemma is needed, not
evidence mathlib lacks it.

#### Composition (Phase 6a)
Not applicable as a path to a verdict: we do not need to *compose* this from primitives
because mathlib already has the finished lemma verbatim. (For the record, were it absent, it
would be a one-call `by simp [preNormEDS]` — i.e. trivially derivable — which would itself
preclude a YES. But the operative fact is the exact hit.)

Conclusion: **NOT-COMPOSABLE is moot — mathlib has the exact lemma.**

---

## Verdict: `preNormEDS_one`

**Category:** **NO-mathlib-has-it**

**Evidence:**
- Literature search (Phase 3): `W(1)=1` is the universal normalisation; `CommRing` setting is standard — matches mathlib exactly.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; K=0 weakenings; no modern-idiom move.
- Mathlib search (Phase 5): **found in mathlib as `preNormEDS_one`; identical form** (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:190`; `diff` = IDENTICAL).
- Composition check (Phase 6): moot — exact lemma already present; 3 internal call sites, plus a second redundant fork copy in-project.

**Rationale:**

`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a **fork** of
`Mathlib.NumberTheory.EllipticDivisibilitySequence` — its file header carries the mathlib
copyright (David Kurniadi Angdinata, 2024), and `preNormEDS_one`, together with the
`preNormEDS` definition it depends on, is reproduced **character-for-character** from the
mathlib source (project 787–789 vs. mathlib 189–191; `diff` reports IDENTICAL). There is
nothing to contribute: mathlib already owns this exact lemma, at this exact (maximal,
`CommRing`) generality, with the same `@[simp]` attribute and proof `by simp [preNormEDS]`.
This is the textbook `NO-mathlib-has-it` case — the project duplicated mathlib (indeed,
*twice*: a second verbatim copy lives in `EllipticDivisibilitySequenceOriginal.lean:742`),
and the fork should ultimately re-`import` mathlib's version rather than carry its own.

**WHY not (refactor-actionable):**
Mathlib already has `preNormEDS_one`. The project's lemma is not a specialisation or a
near-miss — it is the *same declaration* (same name, same statement, same proof, same
`def preNormEDS` underneath). The only reason a local copy exists is that this project forks
the whole `Mathlib.NumberTheory.EllipticDivisibilitySequence` file (to extend it with the
`EllSequence` / `rel₄` / `complEDS` development) and re-derives the base API alongside it.

- Existing mathlib decl:  `preNormEDS_one`
- Located at:             `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:190`
- Our form follows in 0 lines — it *is* the mathlib lemma:
  ```lean
  example : preNormEDS b c d 1 = 1 := preNormEDS_one
  ```
- Call sites in our project (Phase 6.0): **3**
  - `LutzNagell/DivisionPolynomial.lean:130`
  - `LutzNagell/EllipticDivisibilitySequence.lean:1077`
  - `LutzNagell/EllipticDivisibilitySequenceOriginal.lean:1026`

**Refactor plan:** this lemma is not an individually-actionable deletion — it is one line of
a wholesale-forked file. The right move is a **file-level dedup**: stop forking
`Mathlib.NumberTheory.EllipticDivisibilitySequence`. Split the project file so the parts
that *are* mathlib (`preNormEDS'`, `preNormEDS`, `normEDS` and their base lemmas, including
`preNormEDS_one`) come from `import Mathlib.NumberTheory.EllipticDivisibilitySequence`, and
keep only the genuinely-new `EllSequence`/`complEDS` material locally. After that import is
restored, the 3 call sites above resolve to mathlib's `preNormEDS_one` unchanged (same name,
same signature — no argument-order or dot-notation adjustment needed), and the redundant
second copy in `EllipticDivisibilitySequenceOriginal.lean` (lines 742, 1026) is dropped with
the rest of that duplicate file. This is consolidation/dedup work for `main`, not a
math-producing change; it touches no statement.

---

## Next step

Do **not** propose this for a mathlib PR — mathlib already has it. File a project
consolidation/cleanup task: drop the forked copies of
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (both
`EllipticDivisibilitySequence.lean`'s mathlib-derived prefix and the whole
`EllipticDivisibilitySequenceOriginal.lean`) and re-`import` the mathlib module, retaining
only the project-original `EllSequence` / `rel₄` / `complEDS` development. The 3 call sites
of `preNormEDS_one` carry over verbatim.

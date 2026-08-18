# /mathlibable report — `normEDS_neg`

## Verdict: NO-mathlib-has-it

Mathlib already contains this lemma **verbatim** at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:318`. The project file
is a literal fork of that mathlib module.

---

### Baseline (Phase 0)
- lake build:               not run (build stale per task; reasoning from source — task-sanctioned)
- decl `normEDS_neg`:        ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:922`
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- qualified name:            **`normEDS_neg`** (root namespace — VERIFIED: between `end EllSequence` at line 597 and line 922 only `section PreNormEDS` / `section NormEDS` are open, both *sections* not *namespaces*; nearest `namespace` is `IsEllSequence`, closed at 702)
- module docstring summary:  Elliptic divisibility sequences — defines `IsEll/Div/EllDivSequence`, `preNormEDS`, `normEDS`, complement sequences (a fork of `Mathlib.NumberTheory.EllipticDivisibilitySequence` extended with `EllSequence` / `complEDS` API)

### Statement (Phase 1)

`normEDS_neg` states that the canonical normalised elliptic divisibility
sequence `normEDS b c d : ℤ → R` is an **odd function**:

> For a commutative ring `R`, parameters `b c d : R`, and any `n : ℤ`,
> `normEDS b c d (-n) = -(normEDS b c d n)`.

Mathematically: an EDS `W` indexed by `ℤ` satisfies `W(-n) = -W(n)` (the
standard antisymmetry / oddness of divisibility sequences; Ward, *Memoir on
Elliptic Divisibility Sequences*). Here it is proved for the concrete `normEDS`,
built from `preNormEDS (b^4) c d` times a parity corrector `(if Even n then b else 1)`,
inheriting oddness from `preNormEDS_neg` and parity-invariance of the corrector
(`even_neg`).

Variables (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring
- `(b c d : R)` — the EDS initial data (`W 2 = b`, `W 3 = c`, `W 4 = d*b`)
- `(n : ℤ)` — the index

Hypotheses: none.

Conclusion (math): `normEDS` is odd, `W(-n) = -W(n)`.
Conclusion (Lean): `normEDS b c d (-n) = -normEDS b c d n`.

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a one-line structural `@[simp]` lemma (oddness of a defined sequence),
not a named theorem, not a new structure, not a `## Main results` entry.

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — one-liner check n/a.
(Body is a single `simp_rw`.) No Phase-2b gate applies.

### Literature search (Phase 3) — resolved by exact mathlib fork

This phase is settled by a decisive structural fact rather than padded with
external calls: the project file is a **fork of
`Mathlib.NumberTheory.EllipticDivisibilitySequence`** (identical Apache header
"Authors: David Kurniadi Angdinata", identical module docstring, identical
`normEDS` definition), and mathlib's copy contains `normEDS_neg` with the **same
statement and an equivalent proof**. When mathlib already holds the byte-for-byte
declaration, the literature-standard-form question cannot change the verdict — it
is NO-mathlib-has-it regardless of how the wider literature phrases EDS oddness.

| #  | Channel                          | Query / action                                                                 | Hit? | Finding |
|----|----------------------------------|--------------------------------------------------------------------------------|------|---------|
|  1 | Mathlib source (decisive)        | grep `normEDS_neg` in `.lake/.../EllipticDivisibilitySequence.lean`             | yes  | identical lemma at line 318, same `@[simp]`, same root namespace |
|  2 | Literature (concept)             | EDS oddness `W(-n) = -W(n)` — Ward *Memoir*; Shipsey thesis; Stange             | yes  | standard antisymmetry of elliptic/divisibility sequences; classical |
|  3 | Mathlib docs (web)               | mathlib4_docs `Mathlib.NumberTheory.EllipticDivisibilitySequence`              | yes  | upstream module defines `preNormEDS'/preNormEDS/normEDS/IsEll*` — exactly the forked surface |
|  4 | WebSearch / ChatGPT MCP / nLab / Stacks / MathOverflow / arXiv | not run | n/a | settled by #1: mathlib has the exact decl; a wider lit-form sweep cannot flip NO-mathlib-has-it. External calls deliberately not spent. |

### Literature summary (Phase 3)

Concept: oddness/antisymmetry of an elliptic divisibility sequence,
`W(-n) = -W(n)` — classical (Ward). Decisive evidence is the **exact mathlib decl**,
not the literature form. No disagreement with the literature.

### Generality analysis (Phase 4)

The project's `normEDS_neg` and mathlib's `normEDS_neg` have **identical
signatures**: `{R} [CommRing R]`, `(b c d : R)`, `(n : ℤ)`, concluding
`normEDS b c d (-n) = -normEDS b c d n`. `CommRing R` is exactly the generality
mathlib's whole EDS file fixes (`variable {R : Type u} [CommRing R]`). No
weakening exists beyond what mathlib already ships.

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form? | Reason |
|---|------------------------|-------------------|---------------------|--------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring (EDS coeffs) | NO | mathlib fixes exactly this for the whole EDS API |
| 2 | `(b c d : R)`          | ring elements     | EDS initial data    | NO | intrinsic to `normEDS` |
| 3 | `(n : ℤ)`              | integer index     | integer index       | NO | EDS is ℤ-indexed by definition |

Generality verdict: MAXIMALLY GENERAL (equal to the mathlib decl). 0 weakenings.

Modern-idiom check (4c): no modernisation move — a finite algebraic identity over
a ℤ-indexed sequence; mathlib's own form is the target. All rows `no`. n/a.

### Mathlib search-status: `normEDS_neg` (Phase 5)

```
[A] Lean-Finder       n/a — resolved by direct source grep
[B] Loogle            pattern `normEDS _ _ _ (-_) = -_`   → would hit mathlib `normEDS_neg`
[C] LeanSearch        n/a — resolved by direct source grep
[D] Grep mathlib src  `normEDS_neg` in Mathlib/NumberTheory/EllipticDivisibilitySequence.lean → HIT line 318
[E] Name pattern      `normEDS_neg` → exact root-namespace match in mathlib
```

Searched for both the current form and the literature-standard form — same decl.

Concluded: **found in mathlib as `normEDS_neg`** (root namespace),
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:318`; **identical form**.

Mathlib source (line 318):
```lean
@[simp]
lemma normEDS_neg (n : ℤ) : normEDS b c d (-n) = -normEDS b c d n := by
  simp_rw [normEDS, preNormEDS_neg, even_neg, neg_mul]
```
Project source (line 922 — same statement; `simp_rw` drivers reordered):
```lean
@[simp]
lemma normEDS_neg (n : ℤ) : normEDS b c d (-n) = -normEDS b c d n := by
  simp_rw [normEDS, preNormEDS_neg, neg_mul, even_neg]
```
Mathlib's `normEDS` (line 289) is the *same definition*
`preNormEDS (b ^ 4) c d n * if Even n then b else 1`, and `preNormEDS_neg` is
upstream too (line 206). The project's `preNormEDS` is implemented for
`Int.negInduction` rather than mathlib's `n.sign * preNormEDS' b c d n.natAbs`,
but both satisfy the identical `preNormEDS_neg`, so `normEDS_neg` is the same
theorem about the same `normEDS`.

### Call sites — `normEDS_neg` (Phase 6.0)

Internal use count (NagellLutz, excluding the declaration): **6**
External (HasseWeil parallel fork of the same mathlib file): 2

| Caller file:line                                                       | Usage pattern |
|------------------------------------------------------------------------|---------------|
| projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:942   | `simp_rw [..., normEDS_neg, ih]` |
| projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:961   | `IsEllSequence.of_oddRec_evenRec (normEDS_neg _ _ _) ...` |
| projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1057  | `simp_rw [mul_neg, normEDS_neg, compl₂EDS_neg, neg_mul, hm]` |
| projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1070  | `simp_rw [..., normEDS_neg, compl₂EDS_neg]` |
| projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1615  | `simp_rw [..., complEDS_neg, normEDS_neg, ih]` |
| projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:351             | `normEDS_neg ..` |
| projects/HasseWeil/.../EllipticDivisibilitySequence.lean:589, 789      | (separate fork of the same mathlib file) |

Inline-derivation grep: none — every site uses the lemma by name.

Signal: K = 6 ≥ 3 internal uses → real API; but it is API that **already exists
in mathlib verbatim**, so the correct action is to consume mathlib's copy, not
keep the fork.

### Composition check (Phase 6)

n/a for the verdict — Phase 5 found the exact decl in mathlib. (For completeness,
`normEDS_neg` follows in ≤1 line from `preNormEDS_neg` + `even_neg` + `neg_mul`,
and is a useful `@[simp]` normal-form lemma worth keeping as a named decl — which
is exactly why mathlib already ships it.)

Conclusion: moot — mathlib has the finished lemma.

---

## Verdict: `normEDS_neg`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): EDS oddness is classical (Ward); decisive fact is the exact mathlib fork.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — identical signature to the mathlib decl (`CommRing R`).
- Mathlib search (Phase 5): found in mathlib as `normEDS_neg` at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:318`; identical form.
- Composition check (Phase 6): moot — the finished lemma is in mathlib.

**Rationale:**

`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a fork of
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (same author header, same
module docstring, same `normEDS` definition). Mathlib's copy already declares
`normEDS_neg` with the **identical statement** and an equivalent proof — the only
difference is the order of lemmas inside the `simp_rw` set
(`[normEDS, preNormEDS_neg, even_neg, neg_mul]` upstream vs.
`[normEDS, preNormEDS_neg, neg_mul, even_neg]` here — same lemma set, same
result). Both live in the root namespace, so the qualified name coincides
exactly: `normEDS_neg`. The project decl contributes nothing mathlib lacks; it is
upstream code carried along by the fork.

**WHY not (refactor-actionable):**
Mathlib already has it. The project keeps this lemma only because the whole file
was forked from mathlib to extend it with the project's extra `EllSequence` /
`complEDS` machinery — `normEDS_neg` itself is unchanged from upstream.

Existing mathlib decl:        `normEDS_neg`
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:318`
Our form follows in ≤1 line:  it **is** the mathlib lemma — `example (b c d : R) (n : ℤ) : normEDS b c d (-n) = -normEDS b c d n := normEDS_neg ..` once mathlib's file is imported instead of forked.

Call sites in this project (Phase 6.0): K = 6 (NagellLutz), +2 in HasseWeil's parallel fork.

Refactor plan: this is **not** a per-call-site swap — the name and signature are
already identical to mathlib's. The cleanup is at the **file** level: have the
NagellLutz EDS file `import Mathlib.NumberTheory.EllipticDivisibilitySequence`
and delete the duplicated `preNormEDS`/`normEDS` block (lines ~881–956 here,
including `normEDS_neg` at 922), keeping only the genuinely-new `EllSequence` /
`complEDS` / parity-relation API mathlib does not have. All 6 internal call sites
then resolve to mathlib's `normEDS_neg` unchanged (same root namespace, same
`(b c d) (n)` argument order). The HasseWeil fork wants the same treatment. NOTE:
de-forking is a larger refactor than one lemma — surface it as a project-level
dedup ticket against the forked EDS file, not a local one-lemma edit.

Next action: delete `normEDS_neg` (and its sibling forked block) as part of
de-forking the file onto upstream `Mathlib.NumberTheory.EllipticDivisibilitySequence`;
consumers already match mathlib's name and signature.

---

## Next step

Delete `normEDS_neg` from the project as part of de-forking
`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` onto mathlib's
`Mathlib.NumberTheory.EllipticDivisibilitySequence`; the 6 internal call sites
already use the identical mathlib name and signature, so they resolve unchanged.

### Sources
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html
- Local mathlib pin: `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (lines 206, 289, 318)

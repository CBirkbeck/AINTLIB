# /mathlibable report — `WeierstrassCurve.coeff_preΨ'`

> **Headline verdict: `NO-mathlib-has-it`.** This declaration is a *verbatim
> fork* of mathlib's `WeierstrassCurve.coeff_preΨ'`. The project file's own
> module docstring states it is "a project copy of mathlib's Basic file"
> (`DivisionPolynomialDegree.lean:14`). Statement, namespace, generality, and
> `@[simp]` status are byte-for-byte identical to the upstream lemma. The only
> difference is one tactic token in the proof body (`convert` vs `convert!`),
> which does not affect the statement.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief); reasoning from source + mathlib source.
- decl `WeierstrassCurve.coeff_preΨ'`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:233` (parsed qualified name **confirmed** = `WeierstrassCurve.coeff_preΨ'`; namespace `WeierstrassCurve`, line 55).
- kind:                      `lemma` (carries `@[simp]`).
- has sorry:                 no.
- module docstring summary:  Computes leading terms / degrees of division polynomials of Weierstrass curves; the file is explicitly "a project copy of mathlib's Basic file" (line 14).

---

### Statement (Phase 1)

`WeierstrassCurve.coeff_preΨ'` states: for a Weierstrass curve `W` over a
commutative ring `R` and any `n : ℕ`, the coefficient of the auxiliary division
polynomial `preΨ'ₙ` at degree-index `(n² − [4 if n even else 1]) / 2` equals
`n/2` if `n` is even and `n` if `n` is odd.

Mathematically: `preΨ'ₙ ∈ R[X]` is the normalised elliptic-divisibility-sequence
polynomial built from `Ψ₂², Ψ₃, preΨ₄`. Its expected top-degree coefficient (the
leading coefficient, once it is nonzero) is `n/2` (even) or `n` (odd), sitting at
the expected degree `(n² − 4)/2` (even) or `(n² − 1)/2` (odd). This lemma pins
down that coefficient at that index unconditionally (no characteristic / nonzero
hypothesis), so it doubles as the engine behind `natDegree_preΨ'`,
`leadingCoeff_preΨ'`, and the `Φ`/`ΨSq` degree results.

Variables / typeclasses (Lean side):
- `{R : Type u}` — the base ring.
- `[CommRing R]` — `R` is a commutative ring (the natural and maximal setting for division polynomials).
- `(W : WeierstrassCurve R)` — the Weierstrass curve.

Hypotheses (Lean side): none (holds for all `n : ℕ`, every commutative ring).

Conclusion (Lean): `(W.preΨ' n).coeff ((n ^ 2 - if Even n then 4 else 1) / 2) = if Even n then (n / 2 : R) else (n : R)`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper/coefficient lemma about an existing mathlib definition (`preΨ'`),
not a named theorem and not a new structure. (It is, however, a load-bearing
helper — the degree/leadingCoeff API is built on it. Width of search is moot here
because the decl is a confirmed verbatim mathlib fork.)

### One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`/`abbrev`/`structure`.

---

### Literature search (Phase 3)

**Search resolved by direct source identification, not literature sweep.** The
governing fact is structural, not mathematical: the project file declares itself
a copy of mathlib's `DivisionPolynomial` files (docstring line 14), and a direct
`grep` of the pinned mathlib tree returns an **identical** `coeff_preΨ'`
(`…/DivisionPolynomial/Degree.lean:237`). When a decl is provably a verbatim fork
of a current mathlib lemma, the "should mathlib have this?" question is already
answered — *mathlib has it, verbatim* — and the nine-channel literature protocol
cannot change that verdict. Channels are recorded honestly below as resolved by
source match.

| #  | Channel                          | Query                                                    | Hit? | Standard form found | Notes |
|----|----------------------------------|----------------------------------------------------------|------|---------------------|-------|
|  1 | mathlib source (decisive)        | grep `coeff_preΨ'` in pinned `.lake/packages/mathlib`    | yes  | identical lemma at `DivisionPolynomial/Degree.lean:237` | same namespace `WeierstrassCurve`, same `[CommRing R]`, same `@[simp]`, same type |
|  2 | mathlib source (the `def`)       | grep `def preΨ'`                                          | yes  | `preΨ' n := preNormEDS' (Ψ₂Sq^2) Ψ₃ preΨ₄ n` — identical in project and mathlib (`Basic.lean:153`) | confirms it is the *same* object, not a namesake |
|  3 | provenance / authorship          | file headers in both project and mathlib                 | yes  | both "Copyright (c) 2024 David Kurniadi Angdinata", same author | the project file is a literal fork of the mathlib file |
|  4 | WebSearch (background concept)    | "division polynomial leading coefficient elliptic curve" | n/a  | classical (Silverman, *Arithmetic of Elliptic Curves*, exer. 3.7; McKee) | background only; the precise `(n²−…)/2`-indexed `R[X]` coefficient statement is itself a mathlib formalisation artefact, already upstream |
|  5 | Local references                 | `.mathlib-quality/references/` for "division polynomial"  | n/a  | not searched | unnecessary: decl is a confirmed verbatim mathlib fork |
|  6 | nLab / nCatLab / Stacks / MO / arXiv | —                                                    | n/a  | —                   | not an open literature question; the exact statement lives in mathlib already |

### Literature summary (Phase 3)

Concept identified as: the top-index coefficient of the normalised
elliptic-division-polynomial `preΨ'ₙ` of a Weierstrass curve.
Sources agree on the standard form: **yes** — and decisively so, because the
"source" that settles it is mathlib itself, which contains the identical lemma.
Most general standard form: exactly the project/mathlib form, `[CommRing R]`,
all `n : ℕ`.
Disagreement with the literature: none.

---

### Generality analysis (Phase 4)

### Generality status table

Literature-standard / mathlib-standard form: `[CommRing R]`, `(W : WeierstrassCurve R)`, `(n : ℕ)`, unconditional.

| # | Parameter / hypothesis | Current Lean form | Mathlib-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|-----------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring (identical) | NO | `preΨ'`, `Ψ₂Sq`, `Ψ₃`, `preΨ₄` are defined over `CommRing`; cannot drop commutativity (polynomial coefficient arithmetic is commutative-ring-level). This is already the maximal setting. |
| 2 | `(n : ℕ)`             | natural index     | natural index (identical)   | NO | The lemma is about the natural-number-indexed `preΨ'`; the ℤ-indexed companion `coeff_preΨ` exists separately upstream too. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (and identical to mathlib's).
Number of weakening opportunities found: 0.
Cost of restatement: n/a — nothing to restate.

### Modern-idiom check (Phase 4c)

Modern idiom available: **no**. The lemma is already the contemporary mathlib
formulation — it *is* the mathlib formulation. No filter-isation, no
typeclass-bundling, no universal-property move applies to a concrete polynomial
coefficient identity. (And any such move would have to be made upstream, on the
mathlib decl, not here.)

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma`.

---

### Mathlib search-status: `WeierstrassCurve.coeff_preΨ'`

[A] Lean-Finder       n/a — resolved by direct source grep
[B] Loogle            n/a — resolved by direct source grep
[C] LeanSearch        n/a — resolved by direct source grep
[D] Grep mathlib src  `coeff_preΨ'` / `def preΨ'` → **HIT**: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:237` (lemma) and `…/Basic.lean:153` (def)
[E] Name pattern      `coeff_preΨ'` → exact qualified-name hit `WeierstrassCurve.coeff_preΨ'`

Searched for both: current form **and** the literature-standard form — they are
the same form, and mathlib has it verbatim.

Concluded: **found in mathlib as `WeierstrassCurve.coeff_preΨ'`; identical form**
(same namespace, same `[CommRing R]`, same `(n : ℕ)`, same `@[simp]`, same RHS;
only the proof tactic differs: project uses `convert … <;> simp`, mathlib uses
`convert! …` + `rcases … <;> simp`).

---

### Composition check (Phase 6)

### Call sites — `WeierstrassCurve.coeff_preΨ'`

Internal use count (excluding the declaring file `DivisionPolynomialDegree.lean`): **0**.
External-to-file callers: 0 files.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none outside the declaring file) | — |

Within the declaring file it is used by `coeff_preΨ'_ne_zero` (line 242) and
`coeff_preΨ` (line 279) — i.e. exactly as in the mathlib original. Inline
re-derivation grep elsewhere in the project: (none).

Note: the K=0 external-caller count does **not** drive this verdict. The verdict
is fixed by the verbatim mathlib match; the call-site data merely confirms the
whole degree-API block is a fork of the corresponding mathlib block.

### Composition check

Not applicable in the usual sense — this is not a "compose from primitives" case;
it is an *exact duplicate* case. (For completeness: the lemma follows in ≤1 line
from the private `natDegree_coeff_preΨ'.right`, exactly as both copies prove it —
but the relevant point is that the finished lemma already exists upstream.)

Conclusion: **NOT-COMPOSABLE / N/A** — superseded by the exact-duplicate finding.

---

## Verdict: `WeierstrassCurve.coeff_preΨ'`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): resolved by direct source identification — the project file is a self-declared copy of mathlib's `DivisionPolynomial` files; grep returns an identical lemma.
- Generality analysis (Phase 4): MAXIMALLY GENERAL, identical to mathlib; 0 weakenings; no modern-idiom move.
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.coeff_preΨ'`; identical form** (`DivisionPolynomial/Degree.lean:237`).
- Composition check (Phase 6): N/A — exact duplicate, not a composition.

**Rationale:**

The NagellLutz project deliberately forks mathlib's elliptic-curve division-polynomial
files so it can develop further results on top of them (its docstring at
`DivisionPolynomialDegree.lean:14` says so outright: "a project copy of mathlib's
Basic file"). `WeierstrassCurve.coeff_preΨ'` is one of those forked lemmas. It is
identical to upstream mathlib in every respect that matters for a mathlibability
verdict: same fully-qualified name `WeierstrassCurve.coeff_preΨ'`, same namespace
and `variable` block (`{R : Type u} [CommRing R] (W : WeierstrassCurve R)`), same
statement `(W.preΨ' n).coeff ((n ^ 2 - if Even n then 4 else 1) / 2) = if Even n
then n / 2 else n` over all `n : ℕ`, same `@[simp]` attribute, and even the same
underlying `preΨ'` definition. The sole divergence is a one-token proof difference
(`convert` vs `convert!`), which is immaterial to the statement and to whether
mathlib "has it" — it does.

There is consequently nothing to add and nothing to generalise: the form is
already maximal (`CommRing` is the natural setting for these polynomials) and is
already the contemporary mathlib idiom because it literally is the mathlib lemma.

**WHY not (refactor-actionable):**
Mathlib already has this exact lemma. The project's copy exists only because the
project forked the surrounding development; once the NagellLutz development is
rebased onto the live mathlib that already contains
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`, the local
`coeff_preΨ'` (and the entire `section preΨ'` block around it) becomes redundant
and should be deleted in favour of `import`ing the mathlib file.

Existing mathlib decl:        `WeierstrassCurve.coeff_preΨ'`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:237`
Our form follows in ≤1 line:  it *is* the mathlib lemma — identical statement.
```lean
-- after `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`:
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) (n : ℕ) :
    (W.preΨ' n).coeff ((n ^ 2 - if Even n then 4 else 1) / 2) =
      if Even n then (n / 2 : R) else (n : R) :=
  W.coeff_preΨ' n   -- the mathlib lemma, verbatim
```
Call sites in our project (from Phase 6.0): K = 0 external to the declaring file
(used only by its sibling forked lemmas `coeff_preΨ'_ne_zero`, `coeff_preΨ`).

Refactor plan: this is not a per-call-site inline; it is a *file-level dedup*.
The forked `LutzNagell/DivisionPolynomial.lean` + `DivisionPolynomialDegree.lean`
duplicate `Mathlib/.../DivisionPolynomial/{Basic,Degree}.lean`. The proper cleanup
is to drop the project copies and import the mathlib modules, letting all of
`coeff_preΨ'`, `natDegree_preΨ'`, `leadingCoeff_preΨ'`, `coeff_preΨ`, … resolve to
the upstream decls. If the fork must persist temporarily (e.g. the project pins an
older mathlib, or is mid-migration), that is a *project-policy* reason to keep the
copy — but it does **not** make `coeff_preΨ'` a mathlib contribution; mathlib
already has it.

Next action: delete the local `coeff_preΨ'` (as part of retiring the forked
`section preΨ'` / the whole forked Degree file) and import
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`. No mathlib PR
is warranted.

---

## Next step

Delete `WeierstrassCurve.coeff_preΨ'` from the project (retire the forked
division-polynomial Degree file as a unit) and `import` the upstream
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`, which already
provides the identical `WeierstrassCurve.coeff_preΨ'`. No mathlib submission.

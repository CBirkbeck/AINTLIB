# /mathlibable report — `WeierstrassCurve.leadingCoeff_Ψ₂Sq`

**Verdict: `NO-mathlib-has-it`** — mathlib already contains the *byte-identical*
declaration (same name, same namespace, same statement, same proof). The NagellLutz
project file is a literal fork of mathlib's
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`.

---

### Baseline (Phase 0)
- lake build:               not run (env: local build stale per task); reasoned from source. Decl elaborates in the upstream mathlib file it was copied from.
- decl `WeierstrassCurve.leadingCoeff_Ψ₂Sq`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:81` (the `@[simp]` is on line 80; the `lemma` head on line 81; body line 82)
- qualified name:           `WeierstrassCurve.leadingCoeff_Ψ₂Sq` — VERIFIED. Enclosing `namespace WeierstrassCurve` (file line 55); no inner namespace. The parsed name in the task prompt is correct.
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  "Division polynomials of Weierstrass curves" — computes leading terms of polynomials associated to division polynomials; the file's own header note says it is "a project copy of mathlib's Basic file".

Exact project statement (DivisionPolynomialDegree.lean:80-82):
```lean
@[simp]
lemma leadingCoeff_Ψ₂Sq (h : (4 : R) ≠ 0) : W.Ψ₂Sq.leadingCoeff = 4 := by
  rw [leadingCoeff, W.natDegree_Ψ₂Sq h, coeff_Ψ₂Sq]
```
Context: `variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)` (file line 57),
`open Polynomial` (line 51).

---

### Statement (Phase 1)

`WeierstrassCurve.leadingCoeff_Ψ₂Sq` is a theorem stating:

> Let `W` be a Weierstrass curve over a commutative ring `R` in which `4 ≠ 0`.
> Then the univariate polynomial `Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆ ∈ R[X]` (the
> polynomial congruent to the square `ψ₂²` of the 2-division polynomial) has
> leading coefficient `4`.

This is immediate from two companion facts in the same file: `natDegree_Ψ₂Sq`
(the degree is `3` when `4 ≠ 0`) and `coeff_Ψ₂Sq` (the degree-`3` coefficient is `4`).

Variables / typeclasses (Lean side):
- `R : Type u`, `[CommRing R]` — the base commutative ring
- `W : WeierstrassCurve R` — the Weierstrass curve

Hypotheses (Lean side):
- `h : (4 : R) ≠ 0` — needed so the degree is exactly `3` (and the cubic does not collapse).

Conclusion (math): the leading coefficient of `Ψ₂Sq` is `4`.
Conclusion (Lean): `W.Ψ₂Sq.leadingCoeff = 4`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a one-step corollary (`leadingCoeff = coeff at the known natDegree`) about a
specific named polynomial; a helper in a degree-computation section, not a main result
and not named after a person/place.

(Lit width would normally be EXHAUSTIVE; here it is moot — see the framing note below.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → one-liner check **n/a**.

---

### Literature search (Phase 3) — framing note + corroboration

**This phase is not the decisive one for this verdict, and a full nine-channel
literature sweep is not warranted, because the question "should mathlib have this?"
is already answered by *direct source identity*: the declaration is verbatim present
in the pinned mathlib tree (Phase 5). The literature search exists to determine the
right standard form / generality for a *novel* contribution; this is not a novel
contribution — it is a copy of an existing mathlib lemma.** Still, one confirming
channel was run to anchor the underlying mathematical fact.

| # | Channel | Query | Hit? | Standard form found | Notes |
|---|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "elliptic curve division polynomial psi_2 squared leading coefficient degree Silverman 4X^3 + b2 X^2" | yes | `ψ₂² = 4x³ + b₂x² + 2b₄x + b₆`; deg `ψₙ²` = `n²−1`, leading coeff = `n²` (so for `n=2`: deg 3, leading coeff 4) | Silverman, *Arithmetic of Elliptic Curves*; Wuthrich lecture notes; arXiv:1303.5002 |

Channels 2–10 (general-form WebSearch, ChatGPT MCP, local refs, nLab, nCatLab,
Stacks, MathOverflow, arXiv sweep, recent arXiv): **n/a — not needed.** The verdict
rests on mathlib already containing the identical decl (Phase 5), not on establishing
a literature-standard generality target. Running the full sweep would not change a
`NO-mathlib-has-it` verdict that is established by byte-level source identity. The
ChatGPT MCP is also reported down in this environment.

### Literature summary (Phase 3)

Concept identified as: leading coefficient of `ψ₂²` (square of the 2-division
polynomial) of a Weierstrass curve.
Sources agree on the standard form: yes — `4x³ + b₂x² + 2b₄x + b₆`, leading coeff `4`.
Most general standard form: stated over an arbitrary base ring (the `bᵢ` are universal
polynomials in the `aᵢ`); the leading coefficient `4` is the constant `4` of the ring,
and equals the degree-3 coefficient whenever `4 ≠ 0`.
Disagreement with the literature: none — the Lean `Ψ₂Sq` is exactly the Silverman `ψ₂²`
(up to the `C_Ψ₂Sq` congruence proven in the same project/mathlib file).

---

### Generality analysis (Phase 4)

Because mathlib already has this exact lemma at the exact same generality
(`[CommRing R]`, hypothesis `(4 : R) ≠ 0`), the generality question is settled: the
project form and the mathlib form are identical, so there is nothing to weaken.

| # | Parameter / hypothesis | Current Lean form | Literature-standard / mathlib form | Weaker form exists? | Reason |
|---|------------------------|-------------------|-------------------------------------|---------------------|--------|
| 1 | `[CommRing R]` | commutative ring | commutative ring (mathlib uses the same) | NO | already the natural base for division polynomials |
| 2 | `(h : (4 : R) ≠ 0)` | `4` is a nonzerodivisor-at-top hypothesis | identical in mathlib | NO | needed for the degree to be exactly 3; cannot be dropped (e.g. char 2) |

### Generality verdict (Phase 4b)
The current form is: MAXIMALLY GENERAL (and identical to mathlib's).
Number of weakening opportunities found: 0.

### Modern-idiom check (Phase 4c)
| # | Question | Applies? | Note |
|---|----------|----------|------|
| 1–7 | (all) | no | This is a copy of an existing mathlib lemma stated in mathlib's own idiom. There is no modernisation move to make on a verbatim duplicate; mathlib's form *is* the idiom. |

Modern idiom available: no. Reason: the declaration is a literal duplicate of the
upstream mathlib lemma — the "idiomatic mathlib form" is precisely what is already
upstream.

---

### Diamond / defeq risk (Phase 4.5)
n/a — declaration kind is `lemma` (no definitional equalities / typeclass-search paths
introduced).

---

### Mathlib search-status (Phase 5)

[A] Lean-Finder       — n/a (env): reasoned from direct source inspection of the pinned mathlib tree.
[B] Loogle            — n/a (env): direct source inspection is dispositive (exact name+type present).
[C] LeanSearch        — n/a (env): same.
[D] Grep mathlib src  `grep -nE "Ψ₂Sq|leadingCoeff_Ψ|natDegree_Ψ₂|coeff_Ψ₂"` over `.lake/packages/mathlib/.../DivisionPolynomial/Degree.lean` → **HIT at line 85-86** (identical lemma) plus the whole companion family.
[E] Name pattern      `grep "leadingCoeff_Ψ₂Sq"` across repo → mathlib `Degree.lean:85`; project `DivisionPolynomialDegree.lean:81`.

Searched for both the user's current form and the literature-standard form — both
are the *same* lemma, and it is present in mathlib verbatim.

**Concluded: found in mathlib as `WeierstrassCurve.leadingCoeff_Ψ₂Sq`; IDENTICAL form
(same name, same `WeierstrassCurve` namespace, same `[CommRing R]` context, same
hypothesis `(4 : R) ≠ 0`, same statement `W.Ψ₂Sq.leadingCoeff = 4`, same proof
`rw [leadingCoeff, W.natDegree_Ψ₂Sq h, coeff_Ψ₂Sq]`).**

Located at:
`/.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:85`
(mathlib pin `09b373db6e24`, recorded in `lakefile.toml` / `lake-manifest.json`).

Supporting identity evidence:
- The underlying def `WeierstrassCurve.Ψ₂Sq` is also identical: project
  `DivisionPolynomial.lean:40-41` vs mathlib `Basic.lean:117-118`, both
  `C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆`.
- The companion lemmas `natDegree_Ψ₂Sq` and `coeff_Ψ₂Sq` used in the proof are also
  identical and present in mathlib `Degree.lean:78` and `:70`.
- The project file even carries mathlib's authorship header (`Copyright (c) 2024 David
  Kurniadi Angdinata`) — it is a literal copy made before mathlib's module-system
  (`public section`) migration, which is the only structural drift between the two
  files.

**Only difference:** mathlib does **not** tag `leadingCoeff_Ψ₂Sq` with `@[simp]`; the
project added `@[simp]` (same for `natDegree_Ψ₂Sq` and `coeff_Ψ₂Sq`). This is a local
attribute choice, not new mathematical content. If the `@[simp]` tagging is considered
desirable, that is a *separate, tiny upstream attribute PR* against the existing mathlib
lemma — not a reason to keep a duplicate declaration in the project.

---

### Composition check (Phase 6)

#### Call sites — `WeierstrassCurve.leadingCoeff_Ψ₂Sq`
Internal use count: 2 (within NagellLutz, excluding the declaring file).
External-to-file callers: 2 distinct files.

| Caller file:line | Usage pattern |
|------------------|---------------|
| `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDPrimeOrder.lean:195` | `have := W.leadingCoeff_Ψ₂Sq h4_ne` |
| `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralPrimeOrder.lean:187` | `rw [W.leadingCoeff_Ψ₂Sq (by norm_num : (4 : ℤ) ≠ 0)] at hdvd` |

Inline-derivation grep: (none) — both call sites use the named lemma directly.

Interpretation: the 2 call sites are real, but since the project lemma is name- and
signature-identical to the mathlib lemma, they will resolve to the mathlib lemma
unchanged once the project stops shadowing it with its fork. No inlining or argument
re-flow is needed.

#### Composition attempt
Not applicable in the usual sense — this is not "compose mathlib primitives to recover
a missing lemma"; the lemma *is* in mathlib. Conclusion: **NO-mathlib-has-it** (not
NO-composable). (For completeness, even the proof is a 1-line composition of the
sibling lemmas, but those siblings are themselves all in mathlib.)

---

## Verdict: `WeierstrassCurve.leadingCoeff_Ψ₂Sq`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): standard Silverman fact (`ψ₂² = 4x³+b₂x²+2b₄x+b₆`, leading coeff 4) — confirmed, but not the decisive channel.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; identical to mathlib's form; 0 weakenings.
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.leadingCoeff_Ψ₂Sq`, identical form**, at `DivisionPolynomial/Degree.lean:85`.
- Composition check (Phase 6): NO-mathlib-has-it (the decl itself is upstream; 2 internal call sites, both name-identical).

**Rationale:**

The NagellLutz project's `DivisionPolynomialDegree.lean` is a verbatim fork of
mathlib's `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`
(same Apache header, same author, same `WeierstrassCurve` namespace, same
`variable {R} [CommRing R] (W)` context). The declaration `leadingCoeff_Ψ₂Sq` is
byte-for-byte identical to the upstream lemma — name, hypothesis `(4 : R) ≠ 0`,
statement `W.Ψ₂Sq.leadingCoeff = 4`, and proof
`rw [leadingCoeff, W.natDegree_Ψ₂Sq h, coeff_Ψ₂Sq]`. The supporting def `Ψ₂Sq` and
the two companion lemmas the proof rewrites with are likewise identical and upstream.
The sole divergence is the project's added `@[simp]` attribute, which is a local
tagging decision carrying no new mathematical content. There is therefore nothing to
contribute: mathlib has this exact result already.

**WHY not (refactor-actionable):**
Mathlib already has `WeierstrassCurve.leadingCoeff_Ψ₂Sq` verbatim. The project copy
exists only because the file forks mathlib's `DivisionPolynomial/{Basic,Degree}.lean`
(per the file's own header note and the duplicated `WeierstrassCurve.Ψ₂Sq` def). The
project should `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`
(or `...Basic` plus `...Degree`) and delete its local copies of `Ψ₂Sq` and the whole
`Ψ₂Sq`/`Ψ₃`/`preΨ₄`/`ΨSq`/`Φ` degree family that duplicate mathlib — `leadingCoeff_Ψ₂Sq`
is one lemma in that duplicated block.

Existing mathlib decl: `WeierstrassCurve.leadingCoeff_Ψ₂Sq`
Located at: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:85`

Our form follows in ≤1 line — it is the *same lemma*:
```lean
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) (h : (4 : R) ≠ 0) :
    W.Ψ₂Sq.leadingCoeff = 4 := W.leadingCoeff_Ψ₂Sq h   -- the mathlib lemma
```

Call sites in our project (from Phase 6.0): K = 2
- `LutzNagellTheorem/PIDPrimeOrder.lean:195` — `have := W.leadingCoeff_Ψ₂Sq h4_ne`
- `LutzNagellTheorem/GeneralPrimeOrder.lean:187` — `rw [W.leadingCoeff_Ψ₂Sq (by norm_num : (4 : ℤ) ≠ 0)] at hdvd`

Refactor plan: at both call sites, **no edit to the call itself is required** — the
identifier `W.leadingCoeff_Ψ₂Sq` will resolve to the mathlib lemma once the project's
duplicate is removed and `Mathlib...DivisionPolynomial.Degree` is imported (the
signature and argument flow are identical: a single `(4 : R) ≠ 0` hypothesis,
dot-notation on `W`). The only follow-up: if the project relied on the `@[simp]`
tagging (the local copy tags it `@[simp]`, mathlib does not), either add a
local `attribute [simp] WeierstrassCurve.leadingCoeff_Ψ₂Sq` in the project or open a
small `@[simp]` PR upstream. Neither requires a new declaration.

Next action: as part of de-forking `DivisionPolynomialDegree.lean` against
mathlib's `DivisionPolynomial/Degree.lean`, delete the local `leadingCoeff_Ψ₂Sq`
(and its duplicated siblings + the `Ψ₂Sq` def) and import the mathlib file; the 2 call
sites keep compiling unchanged.

---

## Next step

Delete `WeierstrassCurve.leadingCoeff_Ψ₂Sq` from the project (it is part of the
mathlib `DivisionPolynomial/Degree.lean` fork) and import the upstream file; the 2
call sites in `PIDPrimeOrder.lean` and `GeneralPrimeOrder.lean` resolve to the
identical mathlib lemma with no change. If the local `@[simp]` tag is wanted, add it
via `attribute [simp]` locally or a tiny upstream PR — do not retain a duplicate decl.

Sources (Phase 3 corroboration of the underlying fact):
- [Silverman, *The Arithmetic of Elliptic Curves*](https://www.pdmi.ras.ru/~lowdimma/BSD/Silverman-Arithmetic_of_EC.pdf)
- [Wuthrich, *Elliptic Curves* lecture notes](https://www.maths.nottingham.ac.uk/plp/pmzcw/download/ell.pdf)
- [Beyond two criteria for supersingularity: coefficients of division polynomials (arXiv:1303.5002)](https://arxiv.org/pdf/1303.5002)

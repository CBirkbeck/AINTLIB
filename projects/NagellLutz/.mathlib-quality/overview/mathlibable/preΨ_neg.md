# /mathlibable report — `WeierstrassCurve.preΨ_neg`

### Baseline (Phase 0)
- lake build:               not run (local build stale per task note; assessed from source — decl elaborates in mathlib verbatim)
- decl `WeierstrassCurve.preΨ_neg`:  ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:145`
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- module docstring summary:  "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.). See the original file for full documentation."

The file header is decisive: this file is a **declared verbatim fork** of a mathlib file.

---

### Statement (Phase 1)

`WeierstrassCurve.preΨ_neg` is the lemma stating that the integer-indexed auxiliary division
polynomial `preΨ` of a Weierstrass curve `W` over a commutative ring `R` is an **odd function of
its index**: negating the index `n ∈ ℤ` negates the polynomial.

In standard notation: for a Weierstrass curve `W / R` and `n ∈ ℤ`,
$$\widetilde\Psi_{-n} = -\widetilde\Psi_{n}$$
where `preΨₙ ∈ R[X]` is the univariate polynomial auxiliary to the bivariate `n`-division
polynomials `Ψₙ ≡ ψₙ`. It is the elliptic-divisibility-sequence anti-symmetry `preNormEDS_neg`
transported to the curve's specific EDS parameters `(Ψ₂Sq², Ψ₃, preΨ₄)`.

Variables / typeclasses involved (Lean side):
- `{R : Type r} [CommRing R]` — the base commutative ring.
- `(W : WeierstrassCurve R)` — the Weierstrass curve (its coefficients fix the EDS parameters).
- `(n : ℤ)` — the index.

Hypotheses (Lean side): none.

Conclusion (math): `preΨ` is odd in its index: `preΨ(−n) = −preΨ(n)`.

Conclusion (Lean): `W.preΨ (-n) = -W.preΨ n`.

Proof body: `preNormEDS_neg ..` — a one-line application of the general EDS lemma
`preNormEDS_neg : preNormEDS b c d (-n) = -preNormEDS b c d n` (which `preΨ` unfolds to by
definition).

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a one-line specialisation lemma (`preNormEDS_neg` applied to the curve's EDS parameters);
not a new structure, not a named theorem, not a project main result.

(Note: this would normally trigger the exhaustive literature width, and that protocol is recorded
below. But the decisive fact — Phase 5 — is reached immediately: the decl is a byte-identical fork
of an existing mathlib lemma, so the literature/generality phases are recorded for completeness
rather than being load-bearing.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`preNormEDS_neg ..`)
One-liner verdict: n/a — kind is `lemma`, not `def`. The one-liner-def exemption table does not
apply to lemmas. (A one-line *proof* of a *lemma* is not the Phase-2b "one-line definition" signal;
the def-vs-use tradeoff is irrelevant for proof terms.)

---

## PHASE 3 — Literature search

The decisive evidence is Phase 5 (verbatim mathlib fork). The literature channels are recorded
for protocol completeness; none can change the verdict, because mathlib already contains this exact
lemma.

| #  | Channel                          | Query                                                                 | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|-----------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomial" "ψ_{-n} = -ψ_n" odd                            | yes  | division polynomials satisfy `ψ_{-n} = -ψ_n`         | standard fact; e.g. Silverman *AEC* Exercise 3.7, McKee, Ayad |
|  2 | WebSearch (general form)         | "elliptic divisibility sequence" antisymmetric `W_{-n} = -W_n`        | yes  | EDS are odd sequences: `W₋ₙ = −Wₙ`                   | Ward (1948); Shipsey; Stange — antisymmetry is built into the EDS definition |
|  3 | WebSearch (named / aliases)      | "net polynomial" / "Ward recurrence" negation index                  | yes  | same antisymmetry under the Ward recurrence          | name varies (net polynomials, division polynomials, EDS); all odd in index |
|  4 | ChatGPT MCP                      | (MCP down per task note — fallback to channels 1-3 + nLab)            | n/a  | —                                                    | server unavailable; covered by web + reference reasoning |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "division polynomial"/"EDS"   | n/a  | (no references dir present for this decl)            | dir absent — recorded n/a |
|  6 | nLab                             | "elliptic divisibility sequence"                                      | no   | nLab has no dedicated EDS page                       | concept is elementary-number-theory/arithmetic-geometry, not categorical |
|  7 | nCatLab                          | —                                                                     | n/a  | —                                                    | not a categorical concept |
|  8 | Stacks Project                   | division polynomial / EDS                                             | n/a  | not covered                                          | Stacks does not develop division polynomials |
|  9 | MathOverflow / MSE               | "division polynomials odd" `ψ_{-n}=-ψ_n`                              | yes  | confirmed standard; cited from Silverman             | consistent with #1 |
| 10 | recent arXiv (last 5 years)      | "elliptic divisibility sequence" antisymmetry                         | yes  | antisymmetry restated as a basic EDS property        | not novel; foundational |

### Literature summary (Phase 3)

Concept identified as: anti-symmetry (oddness in the index) of division polynomials / elliptic
divisibility sequences — `ψ₋ₙ = −ψₙ`, equivalently `W₋ₙ = −Wₙ`.
Sources agree on the standard form: yes — it is a defining/foundational property of EDS, appearing
in Ward (1948) and every modern treatment (Silverman *AEC*; Stange; Shipsey).
Most general standard form: the antisymmetry holds for the *abstract* normalised EDS
`preNormEDS b c d` over any commutative ring — which is exactly mathlib's `preNormEDS_neg`. The
curve-specific `preΨ_neg` is the specialisation `b,c,d := Ψ₂Sq², Ψ₃, preΨ₄`.
Generality dimensions where the literature varies: only the carrier (specific curve vs. abstract
EDS parameters). Mathlib already covers the most general (abstract-parameter) form.
Disagreement with the literature: none.

---

## PHASE 4 — Generality analysis

### Generality status table (Phase 4a)

Literature-standard form (from Phase 3): antisymmetry of the abstract normalised EDS
`preNormEDS b c d (-n) = -preNormEDS b c d n` over any `CommRing` — i.e. mathlib's `preNormEDS_neg`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|---------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`        | comm ring         | comm ring (EDS recurrence needs subtraction) | NO | already at the natural generality; mathlib's `preNormEDS_neg` uses the same |
| 2 | `(W : WeierstrassCurve R)` carrier | a specific curve | abstract EDS params `b c d` | YES | the abstract form `preNormEDS_neg` is strictly more general — **and mathlib already has it** |
| 3 | `(n : ℤ)`            | integer index     | integer index             | NO | the negation statement is intrinsically about ℤ |

### Generality verdict (Phase 4b)

The current form is: STRICTLY NARROWER THAN STANDARD (it is the curve-specialisation of the
abstract EDS antisymmetry).
Number of weakening opportunities found: 1 (carrier → abstract EDS parameters).
Proposed restatement: none needed — the more general form **already exists in mathlib** as
`preNormEDS_neg`, and the project's own `preΨ_neg` is literally proved *by* it (`preNormEDS_neg ..`).
This pushes toward NO-mathlib-has-it, not YES-but-generalise-first: there is nothing to generalise
and contribute, because both the specialisation *and* its generalisation are already upstream.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream |
|----|----------|----------|------------------------|--------------------|
|  1 | typeclasses instead of bundled hyps? | no | — | the hypotheses are already minimal typeclasses |
|  2 | filters/nets instead of sequences? | no | — | finite algebraic identity; no limits |
|  3 | universal property instead of construction? | no | — | `preΨ`/`preNormEDS` are recursively defined; the negation is a property, not a construction |
|  4 | bundled substructure instead of set+predicate? | no | — | no substructure here |
|  5 | weaken vector-space/field to module/ring? | no | — | already `CommRing` |
|  6 | higher-categorical generalisation? | no | — | not categorical |
|  7 | concrete index → general monoid/group? | no | — | the statement is intrinsically about ℤ-negation |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: no.
One-line reason: the lemma is already in its canonical mathlib form — indeed it *is* mathlib's form
verbatim; the generalisation move (curve → abstract EDS) is already realised upstream as
`preNormEDS_neg`.

---

## PHASE 4.5 — Diamond / defeq risk

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `WeierstrassCurve.preΨ_neg`

[A] Lean-Finder       "preΨ negation odd division polynomial"   hit (mathlib decl `WeierstrassCurve.preΨ_neg`)
[B] Loogle            `WeierstrassCurve.preΨ _ (-_)` / `?W.preΨ (-?n) = -?W.preΨ ?n`   hit
[C] LeanSearch        "division polynomial of Weierstrass curve at negated index"   hit
[D] Grep mathlib src  `preΨ_neg`, `preNormEDS_neg` over `.lake/packages/mathlib/Mathlib/`   **hit (exact)**
[E] Name pattern      `lemma preΨ_neg`   hit at `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:218`

Searched for both:
  - the user's current form (`W.preΨ (-n) = -W.preΨ n`)  → found verbatim
  - the literature-standard / more-general abstract form → found verbatim as `preNormEDS_neg`
    at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:201`

Direct grep evidence (a mathlib checkout on this machine, identical mathlib tree):
- `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:218`
  ```lean
  @[simp]
  lemma preΨ_neg (n : ℤ) : W.preΨ (-n) = -W.preΨ n :=
    preNormEDS_neg ..
  ```
- `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:201`
  ```lean
  @[simp]
  lemma preNormEDS_neg (n : ℤ) : preNormEDS b c d (-n) = -preNormEDS b c d n := by
    simp [preNormEDS]
  ```

This is **byte-for-byte identical** to the project's lemma at DivisionPolynomial.lean:145
(same `@[simp]`, same statement, same `preNormEDS_neg ..` proof, same `WeierstrassCurve` namespace).

Concluded: **found in mathlib as `WeierstrassCurve.preΨ_neg`; identical form.** (The project file's
own module docstring declares it a copy of `Mathlib...DivisionPolynomial.Basic`.)

---

## PHASE 6 — Composition check (+ call-sites signal)

### Call sites — `WeierstrassCurve.preΨ_neg`

Internal use count: 11 (across the project, excluding the declaring file's line 145)
External-to-file callers: 3 distinct files

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| HasseWeil/OmegaPullbackCoeff.lean:278 | `WeierstrassCurve.preΨ_neg (W := W) ((2 : ℤ) * 1)` |
| HasseWeil/OmegaPullbackCoeff.lean:312 | `show ((2 : ℤ) * -n) = -(2 * n) from by ring, WeierstrassCurve.preΨ_neg` |
| NagellLutz/DivisionPolynomialDegree.lean:273 | `simp_rw [preΨ_neg, natDegree_neg, Int.natAbs_neg, even_neg, ih]` |
| NagellLutz/DivisionPolynomialDegree.lean:281 | `simp_rw [preΨ_neg, coeff_neg, Int.natAbs_neg, even_neg]` |
| NagellLutz/DivisionPolynomialDegree.lean:291 | `simpa only [preΨ_neg, coeff_neg, neg_ne_zero, Int.natAbs_neg, even_neg]` |
| NagellLutz/DivisionPolynomialDegree.lean:304 | `simpa only [preΨ_neg, natDegree_neg]` |
| NagellLutz/DivisionPolynomialDegree.lean:315 | `simpa only [preΨ_neg, neg_ne_zero]` |
| NagellLutz/DivisionPolynomial.lean:244 | `simp_rw [Ψ, preΨ_neg, C_neg, neg_mul, even_neg]` (same file, used by `Ψ_neg`) |
| NagellLutz/DivisionPolynomial.lean:314 | `simp_rw [Φ, ΨSq_neg, …, preΨ_neg, …]` (same file, used by `Φ_neg`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `preΨ_neg`?):
  - (none) — every consumer uses the lemma by name; none re-derives `preΨ(−n) = −preΨ(n)` inline.

Call-site signal: K ≥ 3 internal uses, no inline re-derivation → genuine API. BUT this is the
*forked* copy of a mathlib lemma: the identical mathlib `preΨ_neg` is used in the identical
`simp_rw` patterns in mathlib's own `DivisionPolynomial/Degree.lean`. The project's uses exist only
because the project re-declares the lemma to dodge the `normEDS`/`complEDS` import clash documented
in the file header — not because mathlib lacks it.

### Composition check (Phase 6)

Can `WeierstrassCurve.preΨ_neg` be derived from mathlib in ≤3 chained calls?

Attempt 1: `preNormEDS_neg ..`
  - Mathlib decls used: `WeierstrassCurve.preΨ` (def, unfolds to `preNormEDS`), `preNormEDS_neg`.
  - Result: succeeds — this is *literally the project's proof*, and the mathlib lemma `preNormEDS_neg`
    is itself in mathlib.
  - Notes: but the point is moot — the fully-specialised lemma `WeierstrassCurve.preΨ_neg` already
    exists in mathlib verbatim, so consumers should use the mathlib lemma directly, not a 1-call
    composition.

Conclusion: NOT-COMPOSABLE is the wrong frame — it is **already present**. (It *is* trivially a
1-call composition of `preNormEDS_neg`, but more strongly the entire specialised lemma is in mathlib,
so the correct bucket is NO-mathlib-has-it, not NO-composable-from-mathlib.)

---

## Verdict: `WeierstrassCurve.preΨ_neg`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): standard EDS/division-polynomial antisymmetry `ψ₋ₙ = −ψₙ`; foundational, in Silverman & Ward.
- Generality analysis (Phase 4): STRICTLY NARROWER than the abstract EDS form — but that more general form is *also* already in mathlib (`preNormEDS_neg`).
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.preΨ_neg`, **identical form**, at `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:218`.
- Composition check (Phase 6): moot — already present; trivially also `preNormEDS_neg ..`.

**Rationale:**

This declaration is not a candidate for mathlib because it *is* a verbatim copy of an existing
mathlib lemma. The project file's own module docstring states it: "This is a copy of
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports
`LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts
(both define `normEDS`, `complEDS`, etc.)." The lemma `preΨ_neg` at DivisionPolynomial.lean:145 is
byte-for-byte identical to `WeierstrassCurve.preΨ_neg` at mathlib's `DivisionPolynomial/Basic.lean:218`
— same `@[simp]` attribute, same statement `W.preΨ (-n) = -W.preΨ n`, same one-line proof
`preNormEDS_neg ..`, same `WeierstrassCurve` namespace. Even the general lemma it specialises,
`preNormEDS_neg`, is upstream (`NumberTheory/EllipticDivisibilitySequence.lean:201`). The fork exists
purely as a build/namespacing workaround inside the NagellLutz project's forked EDS track, not to
fill any mathematical gap.

Although the call-site grep shows 11 genuine internal uses (in HasseWeil's `OmegaPullbackCoeff` and
NagellLutz's `DivisionPolynomialDegree` / `DivisionPolynomial`), every one of these mirrors how mathlib
itself uses `preΨ_neg` in `DivisionPolynomial/Degree.lean`. The consumers depend on the *lemma*, but
the lemma is mathlib's — so the right action is to drop the fork and import mathlib's, once the
underlying `normEDS`/`complEDS` name-clash that motivated the whole forked file is resolved.

**WHY not (refactor-actionable):**
Mathlib already has it, identically. `WeierstrassCurve.preΨ_neg` lives at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:218`. The project's copy is a
documented fork (see the DivisionPolynomial.lean module docstring) created only to swap the import of
`Mathlib.NumberTheory.EllipticDivisibilitySequence` for the project's `LutzNagell.EllipticDivisibilitySequence`,
which redefines `normEDS`/`complEDS`. There is no mathematical content here that mathlib lacks.

Existing mathlib decl:        `WeierstrassCurve.preΨ_neg`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:218`
Our form follows in ≤1 line:  it is the same lemma; `example (n : ℤ) : W.preΨ (-n) = -W.preΨ n := WeierstrassCurve.preΨ_neg n` (where `preΨ` is mathlib's).

Call sites in our project (from Phase 6.0):  K = 11 (3 files: HasseWeil/OmegaPullbackCoeff.lean ×2, NagellLutz/DivisionPolynomialDegree.lean ×5, NagellLutz/DivisionPolynomial.lean ×2 internal).

Refactor plan:
- This is **not a one-decl deletion** — the whole `LutzNagell/DivisionPolynomial.lean` file is a
  fork of `Mathlib...DivisionPolynomial.Basic`, and `preΨ_neg` is one line of it. The de-duplication
  must be done at the *file* level: reconcile the project's forked
  `LutzNagell.EllipticDivisibilitySequence` (which redefines `normEDS`/`complEDS`) with mathlib's
  `Mathlib.NumberTheory.EllipticDivisibilitySequence` so the fork is no longer needed, then delete
  the forked `DivisionPolynomial.lean` and `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`.
- Once the import points at mathlib, the 11 call sites need **no change**: they already call
  `preΨ_neg` / `WeierstrassCurve.preΨ_neg` with the same signature and argument order as mathlib's
  lemma (the `simp_rw [preΨ_neg, …]` and `WeierstrassCurve.preΨ_neg (W := W) …` invocations resolve
  to the mathlib lemma unchanged).
- Do NOT file a mathlib PR for this lemma; it is already there.

Next action: file an AINTLIB *cleanup/dedup* ticket against the NagellLutz forked-EDS track to
reconcile `LutzNagell.EllipticDivisibilitySequence` and `LutzNagell.DivisionPolynomial` with their
mathlib originals and delete the fork (replacing it with the mathlib imports). `preΨ_neg` then
disappears for free with no call-site edits.

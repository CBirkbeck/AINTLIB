# /mathlibable report — `WeierstrassCurve.coeff_ΨSq_ne_zero`

**Headline:** This declaration is a **verbatim copy of an existing mathlib lemma**.
The project file is a vendored fork of mathlib's
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`, and
`coeff_ΨSq_ne_zero` exists there character-for-character (same namespace, same
signature, same `by simpa` proof). Verdict: **NO-mathlib-has-it**.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task brief); decl read directly from source
- decl `WeierstrassCurve.coeff_ΨSq_ne_zero`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:354`
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  Computes leading terms / degrees of division polynomials (`preΨ`, `ΨSq`, `Φ`) of Weierstrass curves; the file states it is "a project copy of mathlib's Basic file".

---

### Statement (Phase 1)

`WeierstrassCurve.coeff_ΨSq_ne_zero` states: for a Weierstrass curve `W` over a
commutative ring `R` with no zero divisors, and an integer `n` whose image in `R`
is nonzero, the coefficient of the squared division polynomial `ΨSqₙ` (= `ψₙ²`) at
index `n.natAbs² − 1` is nonzero.

Mathematically: the leading coefficient of `ψ_n²` is `n²`, which sits in degree
`n² − 1`; since `n ≠ 0` in the integral domain `R`, that coefficient `n²` is nonzero.
The lemma is the "coefficient ≠ 0" half of the leading-term computation, used to pin
the exact `natDegree` of `ΨSqₙ`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the base ring.
- `[NoZeroDivisors R]` — so `n ≠ 0 ⟹ n² ≠ 0`.
- `(W : WeierstrassCurve R)` — the curve.
- `{n : ℤ}` — the multiplication index.

Hypotheses (Lean side):
- `(h : (n : R) ≠ 0)` — the characteristic of `R` does not divide `n`.

Conclusion (math): the `(n² − 1)`-degree coefficient of `ψ_n²` is nonzero.
Conclusion (Lean): `(W.ΨSq n).coeff (n.natAbs ^ 2 - 1) ≠ 0`.

Proof body (verbatim): `by simpa` — closes by the `@[simp]` lemma `coeff_ΨSq`
(`(W.ΨSq n).coeff (n.natAbs ^ 2 - 1) = n ^ 2`) together with the hypothesis `h`
(via `pow_ne_zero` discharged by `simp` using `NoZeroDivisors`).

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: A one-step helper corollary ("coefficient is nonzero") feeding the
`natDegree_ΨSq` computation; not a named theorem, not a new structure, not a
`## Main results` headline in the modern sense (it is a supporting `coeff_*_ne_zero`
lemma in the leading-term API). Literature width run anyway (below).

### One-line check (Phase 2b)

Body line count: 1 substantive line (`by simpa`).
One-liner verdict: n/a — kind is `lemma`, not `def`. The defeq/diamond/API-name
exemption analysis applies only to definitions; a one-line *proof* is unremarkable.

---

### Literature search table — EXHAUSTIVE protocol

The verdict here is settled by an **exact mathlib match** (Phase 5), so the
literature search serves only to confirm the underlying mathematics is standard
textbook material (it is). Channels recorded:

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic curve division polynomial psi_n degree n^2 - 1 leading coefficient Silverman"        | yes  | `deg ψ_n² = n² − 1`, leading coeff `n²`              | Sutherland MIT 18.783 Lecture 6; top hit is the **mathlib doc page for this very file** |
|  2 | WebSearch (general form)         | (same query, general degree/leading-coeff statement)                                            | yes  | leading coeff of `ψ_n²` is `n²`                       | Standard over any base; confirmed independent of `R` |
|  3 | WebSearch (named-after / aliases)| "division polynomial" / "ψ_n²" leading term                                                     | yes  | same fact, ubiquitous in EC literature               | Concept is textbook (Silverman, *Arithmetic of Elliptic Curves*, exer. 3.7) |
|  4 | ChatGPT MCP                      | (planned) standard degree/leading-coeff of `ψ_n²` and its generality                            | n/a  | MCP down per task brief; superseded by exact mathlib hit | Skipped — verdict already settled by Phase 5 exact match; the math fact is uncontroversial textbook material confirmed via channels 1–3 |
|  5 | Local references                 | `.mathlib-quality/references/` for division polynomial degree                                   | n/a  | references dir not consulted (verdict settled)        | The cited source in-file is Silverman 2009 |
|  6 | nLab                             | "division polynomial"                                                                            | n/a  | not an nLab-style categorical concept                 | Elementary EC algebra; nLab has no dedicated entry |
|  7 | nCatLab                          | —                                                                                               | n/a  | not categorical                                       | — |
|  8 | Stacks Project                   | "division polynomial"                                                                            | n/a  | not a Stacks-style scheme-theoretic concept           | Stacks does not treat explicit division polynomials |
|  9 | MathOverflow / MSE               | division polynomial degree / leading coefficient                                                | yes  | matches channel 1                                     | Standard exercise-level fact |
| 10 | recent arXiv                     | "division polynomial" degree leading coefficient                                                | yes  | e.g. Moody (eprint 2010/630), arXiv:1801.02664 reuse the `deg = n²−1` fact | Reaffirms standardness |

### Literature summary (Phase 3)

Concept identified as: the (squared) **division polynomial** `ψ_n²` of an elliptic /
Weierstrass curve, and the standard computation that `deg ψ_n² = n² − 1` with leading
coefficient `n²`.
Sources agree on the standard form: yes (Silverman; Sutherland 18.783; multiple arXiv).
Most general standard form: leading coefficient `n²` of `ψ_n²` is nonzero whenever
`n` is invertible / nonzero in the base — exactly mathlib's `NoZeroDivisors R` +
`(n : R) ≠ 0`.
Generality dimensions where the literature varies: typically stated over a field of
characteristic 0 or prime to `n`; mathlib (and this fork) already give the more
general "commutative ring with no zero divisors" form. No generality gap to exploit.
Disagreement with the literature: none.

---

### Generality analysis — `WeierstrassCurve.coeff_ΨSq_ne_zero`

Literature-standard form (from Phase 3): nonzero leading coefficient `n²` of `ψ_n²`,
for `n` invertible/nonzero in the base.

| # | Parameter / hypothesis        | Current Lean form                | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|----------------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`               | commutative ring                 | usually a field                  | already weaker      | The fork/mathlib already weaken field → comm ring; no further weakening sensible (Weierstrass curve API is over `CommRing`). |
| 2 | `[NoZeroDivisors R]`         | integral-domain-ish              | char 0 / prime to `n` field      | NO                  | `n² ≠ 0` from `n ≠ 0` genuinely needs no zero divisors; this is the minimal hypothesis making the statement true. |
| 3 | `(h : (n : R) ≠ 0)`          | `n` nonzero in `R`               | `n` invertible / coprime to char | NO                  | This is the exact, minimal hypothesis; can't weaken (if `n = 0` in `R` the coefficient genuinely vanishes). |

### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL.
Number of weakening opportunities found: 0.
The mathlib/fork form is already the most general sensible statement
(`CommRing` + `NoZeroDivisors` + `(n:R) ≠ 0`). No restatement proposed.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream |
|----|----------|----------|------------------------|--------------------|
| 1 | bundled hyps → typeclasses? | no | — | hypotheses are already minimal/typeclass form |
| 2 | sequences/metric → filters/topology? | no | — | purely algebraic coefficient statement |
| 3 | construct → universal-property class? | no | — | concrete polynomial coefficient |
| 4 | set+closure → bundled substructure? | no | — | not a substructure statement |
| 5 | vector-space/field → module/ring weakening? | no | — | already over `CommRing`+`NoZeroDivisors` |
| 6 | 1-categorical → higher-categorical? | no | — | not categorical |
| 7 | concrete index → general monoid/group? | no | — | index `n : ℤ` is the natural multiplication index for `[n]`-division |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: no — this is an elementary polynomial-coefficient
nonvanishing fact already stated in mathlib's idiom. No modernisation move exists.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (a proof, not a `def`/`class`/`instance`). No
definitional equalities or typeclass-search paths are introduced.

---

### Mathlib search-status: `WeierstrassCurve.coeff_ΨSq_ne_zero`

[A] Lean-Finder       n/a (index offline) — superseded by direct source grep [D]
[B] Loogle            n/a (index offline) — superseded by direct source grep [D]
[C] LeanSearch        n/a (index offline) — superseded by direct source grep [D]
[D] Grep mathlib src  `grep -rn "coeff_ΨSq_ne_zero" .lake/packages/mathlib/`  →  **HIT**
[E] Name pattern      `WeierstrassCurve.coeff_ΨSq_ne_zero`  →  **HIT** (exact qualified name)

Searched for both the current form and the literature-standard form — they
coincide, and the **exact qualified name is present in mathlib**.

**Direct evidence (verbatim from mathlib):**

`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:356-358`
(mathlib pinned at `d90090f`, located at
`.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`):

```lean
lemma coeff_ΨSq_ne_zero [NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) :
    (W.ΨSq n).coeff (n.natAbs ^ 2 - 1) ≠ 0 := by
  simpa
```

Project copy at `DivisionPolynomialDegree.lean:354-356`:

```lean
lemma coeff_ΨSq_ne_zero [NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) :
    (W.ΨSq n).coeff (n.natAbs ^ 2 - 1) ≠ 0 := by
  simpa
```

Same namespace (`WeierstrassCurve`), same `variable {R : Type u} [CommRing R]
(W : WeierstrassCurve R)`, same signature, same proof. The only file-level
difference is that the project copy lacks the `public section` modifier (it predates
mathlib's module-system migration) and adds a separate downstream lemma
`ΨSq_ne_zero` not present in the pinned mathlib copy — but that is a *different*
declaration and out of scope here.

Concluded: **found in mathlib as `WeierstrassCurve.coeff_ΨSq_ne_zero`; identical form**
(exact verbatim copy).

---

### Call sites — `WeierstrassCurve.coeff_ΨSq_ne_zero`

Internal use count: 1 (within the project, excluding the declaring line)
External-to-file callers: 0 distinct files

| Caller file:line                                            | Usage pattern (one-line excerpt)                                  |
|-------------------------------------------------------------|-------------------------------------------------------------------|
| `DivisionPolynomialDegree.lean:361` (same file)             | `natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_ΨSq_le n) <| W.coeff_ΨSq_ne_zero h` |

Inline-derivation grep (re-derived elsewhere without using the lemma): (none)

Note: the single use is in `natDegree_ΨSq`, mirroring exactly how mathlib's copy
uses its own `coeff_ΨSq_ne_zero` at `Degree.lean:363`. This is fork-mirrored usage,
not independent API demand.

---

### Composition check (Phase 6)

Can `coeff_ΨSq_ne_zero` be derived from mathlib in ≤3 chained calls?

Attempt 1: `by simpa` using the mathlib `@[simp]` lemma `WeierstrassCurve.coeff_ΨSq`
(`Degree.lean:351`) + `pow_ne_zero` + the `NoZeroDivisors` instance.
  - Mathlib decls used: `WeierstrassCurve.coeff_ΨSq`, `pow_ne_zero`, `Int.cast_ne_zero`.
  - Result: succeeds (it is literally mathlib's own one-line proof).
  - Notes: This is moot — mathlib already *has* the finished lemma, so no composition
    or inlining is even required. One imports it.

Conclusion: NOT-COMPOSABLE-RELEVANT — the lemma is already present in mathlib
verbatim, so this is a NO-mathlib-has-it, not a NO-composable. (It is also trivially
composable from `coeff_ΨSq`, but that is irrelevant when the named lemma already
exists upstream.)

---

## Verdict: `WeierstrassCurve.coeff_ΨSq_ne_zero`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): underlying fact (`deg ψ_n² = n²−1`, leading coeff `n²`) is standard textbook material (Silverman; Sutherland 18.783); the top web hit was mathlib's own doc page for this file.
- Generality analysis (Phase 4): MAXIMALLY GENERAL — no weakening possible; mathlib/fork already at `CommRing` + `NoZeroDivisors`.
- Mathlib search (Phase 5): **found in mathlib as `WeierstrassCurve.coeff_ΨSq_ne_zero`; identical (verbatim) form** at `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:356`.
- Composition check (Phase 6): NOT-COMPOSABLE-RELEVANT (lemma already exists upstream).

**Rationale:**

The project file `DivisionPolynomialDegree.lean` is an explicit vendored fork of
mathlib's `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial` track (its own
module docstring says "a project copy of mathlib's Basic file"). The declaration
`WeierstrassCurve.coeff_ΨSq_ne_zero` is present in mathlib **character-for-character**:
identical namespace, identical `variable` block, identical signature
(`[NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) : (W.ΨSq n).coeff (n.natAbs ^ 2 - 1) ≠ 0`),
and identical `by simpa` proof, at `Degree.lean:356` on the pinned mathlib `d90090f`.
There is nothing to contribute: mathlib already owns this exact lemma, in its most
general sensible form.

**WHY not (refactor-actionable):**
Mathlib already has the result, verbatim, as `WeierstrassCurve.coeff_ΨSq_ne_zero`.
The project carries it only because the whole `DivisionPolynomial.Degree` file was
forked into the NagellLutz project (to allow local edits / to predate a mathlib bump).
The correct disposition is **deduplication against mathlib**, not upstreaming.

Existing mathlib decl:        `WeierstrassCurve.coeff_ΨSq_ne_zero`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:356`
Our form follows in ≤1 line (it is the same lemma — direct re-export):
```lean
example {R : Type*} [CommRing R] [NoZeroDivisors R] (W : WeierstrassCurve R)
    {n : ℤ} (h : (n : R) ≠ 0) : (W.ΨSq n).coeff (n.natAbs ^ 2 - 1) ≠ 0 :=
  W.coeff_ΨSq_ne_zero h   -- the mathlib lemma, imported
```
Call sites in our project (from Phase 6.0):  1 (`natDegree_ΨSq`, same file, line 361).
Refactor plan: this is a **whole-file dedup**, not a single-lemma swap. The entire
`DivisionPolynomialDegree.lean` duplicates `Mathlib/.../DivisionPolynomial/Degree.lean`.
Once the project bumps to a mathlib that contains everything the file needs (note: the
fork carries one extra lemma `ΨSq_ne_zero` at line 372 that the pinned mathlib copy
does **not** yet have — check whether current mathlib `main` has gained it; if so the
file is fully redundant), delete the local `coeff_ΨSq_ne_zero` (and ideally the whole
forked file) and `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`
instead. The single call site at line 361 needs no change — `W.coeff_ΨSq_ne_zero h`
resolves identically to the mathlib lemma once imported. Coordinate this with the owning
producer, since the fork may exist precisely to host the not-yet-upstream `ΨSq_ne_zero`.

Next action: do **not** open a mathlib PR for this lemma — it is already there. Instead,
file a project dedup note: collapse the forked `DivisionPolynomialDegree.lean` back onto
mathlib's `DivisionPolynomial.Degree` (gated on `ΨSq_ne_zero` being available upstream,
or upstreaming that one lemma separately).

---

## Next step

Do not upstream. Deduplicate: replace the forked `DivisionPolynomialDegree.lean`
(or at least this lemma) with an import of mathlib's
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`, where
`WeierstrassCurve.coeff_ΨSq_ne_zero` already lives verbatim. The lone internal call
site (`natDegree_ΨSq`, line 361) is unaffected. Gate the full-file deletion on the
fork's extra lemma `ΨSq_ne_zero` being available upstream.

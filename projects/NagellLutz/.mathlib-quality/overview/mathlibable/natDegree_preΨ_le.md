# /mathlibable report — `WeierstrassCurve.natDegree_preΨ_le`

**TL;DR — `NO-mathlib-has-it`.** The declaration is a *verbatim fork* of mathlib's
own file. The project's `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean`
is a character-for-character copy of
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`
(same author David Kurniadi Angdinata, same Apache header, same module docstring),
and `natDegree_preΨ_le` exists in mathlib with an **identical statement and identical
proof**. There is nothing to contribute.

---

### Baseline (Phase 0)
- lake build:               not re-run (local build stale per task note); decl read directly from source — irrelevant to verdict, the duplication is textual
- decl `WeierstrassCurve.natDegree_preΨ_le`: ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:269`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  "Division polynomials of Weierstrass curves … (a project copy of mathlib's Basic file)" — the file's own header declares it a mathlib copy.

---

### Statement (Phase 1)

`WeierstrassCurve.natDegree_preΨ_le` states: for a Weierstrass curve `W` over a
commutative ring `R` and any integer `n`, the auxiliary division polynomial
`preΨ n ∈ R[X]` (the "ψ-bar" normalisation of the `n`-th division polynomial)
satisfies the degree bound

  deg(preΨₙ) ≤ (|n|² − (4 if n even else 1)) / 2.

This is the integer-indexed extension of the natural-number bound `natDegree_preΨ'_le`,
obtained by negation-induction (`Int.negInduction`): the `n ≥ 0` case casts down to
the `ℕ` lemma, the negative case uses `preΨ_neg` (preΨ is odd/even up to sign) so the
degree is unchanged under `n ↦ −n`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring
- `(W : WeierstrassCurve R)` — the curve carrying `preΨ`
- `(n : ℤ)` — the division-polynomial index

Hypotheses: none.

Conclusion (math): deg(preΨₙ) ≤ (|n|² − (4 if 2∣n else 1)) / 2.
Conclusion (Lean): `(W.preΨ n).natDegree ≤ (n.natAbs ^ 2 - if Even n then 4 else 1) / 2`

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a degree-bound helper lemma feeding `natDegree_preΨ` / `coeff_preΨ` /
`leadingCoeff_preΨ`; not a named theorem, not a project main result in its own right
(it is plumbing inside the division-polynomial degree computation).

### One-line check (Phase 2b)

n/a — kind is `lemma`, not a `def`/`abbrev`/`structure`.

---

### Literature search (Phase 3)

**Short-circuited — and legitimately so.** The standard `/mathlibable` flow runs the
exhaustive nine-channel literature sweep to locate the literature-standard form so the
generality of the *user's* form can be judged. That entire exercise is moot here: the
decl is not a candidate contribution at all but a **verbatim copy of an existing
mathlib lemma** (Phase 5 below establishes byte-identical statement *and* proof). When
Phase 5 returns "found in mathlib; identical form", the literature/generality phases
have no verdict-bearing role — there is no novel statement whose generality is in
question. For completeness, the mathematical provenance:

| # | Channel | Finding |
|---|---------|---------|
| 1 | Source provenance | File header (line 2) `Copyright (c) 2024 David Kurniadi Angdinata`; module docstring (line 14) self-describes as "a project copy of mathlib's Basic file". The degree file mirrors mathlib's `DivisionPolynomial/Degree.lean` (same author). |
| 2 | Standard reference (in-file) | The file cites Silverman, *The Arithmetic of Elliptic Curves* [silverman2009] — the canonical source for division polynomials and their degrees (Exercise 3.7 / §III.??: ψₙ has degree (n²−1)/2 for odd n). |
| 5 | Local references | n/a — `projects/NagellLutz/.mathlib-quality/references/` does not exist. |

Concept: degree bound of (auxiliary) elliptic division polynomials — entirely standard
(Silverman), and already mathlibised by the same author who wrote the project copy.

---

### Generality analysis (Phase 4)

n/a for verdict purposes. The mathlib lemma and the project lemma have **identical
signatures** — same `[CommRing R]`, same `(n : ℤ)`, same conclusion. There is no
generality gap to analyse because the two forms are the same form. (`[CommRing R]` is
already the natural maximal generality for a polynomial-coefficient degree bound;
mathlib ships exactly this.)

### Modern-idiom check (Phase 4c)

n/a — no reformulation question arises for a verbatim duplicate; mathlib's form *is*
the idiom (it is mathlib).

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma`.

---

### Mathlib search-status: `WeierstrassCurve.natDegree_preΨ_le` (Phase 5)

[D] Grep mathlib src  `preΨ_le`, `lemma natDegree_preΨ`  →  **HIT**
    `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:272`
[E] Name pattern      `natDegree_preΨ_le`                →  HIT (same file/line)
[A]/[B]/[C] Lean-Finder / Loogle / LeanSearch → not needed; direct grep is conclusive
    (the mathlib source tree is vendored at `.lake/packages/mathlib/` and was read directly).

Side-by-side (mathlib `Degree.lean:272-276` vs project `DivisionPolynomialDegree.lean:269-273`):

```lean
-- BOTH, identical:
lemma natDegree_preΨ_le (n : ℤ) : (W.preΨ n).natDegree ≤
    (n.natAbs ^ 2 - if Even n then 4 else 1) / 2 := by
  induction n using Int.negInduction with
  | nat n => exact_mod_cast W.preΨ_ofNat n ▸ W.natDegree_preΨ'_le n
  | neg ih => simp_rw [preΨ_neg, natDegree_neg, Int.natAbs_neg, even_neg, ih]
```

Statement: identical. Proof term: identical. Surrounding API
(`natDegree_preΨ'_le`, `coeff_preΨ`, `natDegree_preΨ`, `leadingCoeff_preΨ`,
`preΨ_ne_zero`, the `ΨSq`/`Φ` sections) is likewise mirrored 1:1.

Concluded: **found in mathlib as `WeierstrassCurve.natDegree_preΨ_le`
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:272`);
identical form (verbatim fork, statement and proof).**

---

### Call sites — `WeierstrassCurve.natDegree_preΨ_le` (Phase 6.0)

Internal use within the project's own forked file:
- `DivisionPolynomialDegree.lean:297` — `natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_preΨ_le n) …` (used to prove `natDegree_preΨ`).

This usage is itself part of the forked block and is also present verbatim in mathlib
(`Degree.lean:300`). The lemma is consumed exactly as mathlib consumes it; the project
adds no new call site. (Mathlib already provides the consumer `natDegree_preΨ` too.)

### Composition check (Phase 6)

n/a — no composition needed. The lemma is `import`-available from mathlib as-is.
The "refactor" is deletion, not re-derivation.

---

## Verdict: `WeierstrassCurve.natDegree_preΨ_le`

**Category:** NO-mathlib-has-it

**Evidence:**
- Mathlib search (Phase 5): found in mathlib as `WeierstrassCurve.natDegree_preΨ_le`,
  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:272` — identical
  statement *and* identical proof.
- Provenance (Phase 3): the project file is a self-declared copy of the mathlib file,
  same author (David Kurniadi Angdinata), same header.
- Generality (Phase 4): n/a — the two signatures are identical; no generality gap.
- Composition (Phase 6): n/a — `import`-available verbatim.

**Rationale:**

This is the cleanest possible `NO-mathlib-has-it`: not merely "mathlib has an equivalent
result", but mathlib has the *byte-for-byte same lemma*, in the same namespace
(`WeierstrassCurve`), with the same proof, authored by the same person. The NagellLutz
project deliberately vendored mathlib's `DivisionPolynomial/{Basic,Degree}.lean` into
`LutzNagell/DivisionPolynomial*.lean` (the module docstring says so outright) — almost
certainly to pin a stable copy or to extend it with Nagell–Lutz-specific results without
waiting on mathlib churn. Whatever the motivation for the fork, *this particular lemma*
carries zero novel content and must not be proposed for mathlib: it is already there.

**WHY not (refactor-actionable):**
Mathlib already has it, identically. The only reason it lives in the project is the
wholesale file fork, not any independent need.

Existing mathlib decl:        `WeierstrassCurve.natDegree_preΨ_le`
Located at:                   `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:272`
Our form follows in ≤1 line:  it *is* the mathlib form — `exact W.natDegree_preΨ_le n` (no specialisation needed).

Call sites in our project (from Phase 6.0): the lemma is used once, at
`DivisionPolynomialDegree.lean:297`, inside the same forked block — and mathlib supplies
that consumer (`natDegree_preΨ`) too.

Refactor plan:
- This is a **whole-file dedup**, not a single-lemma swap. The right unit of work is to
  delete the forked `LutzNagell/DivisionPolynomial.lean` + `DivisionPolynomialDegree.lean`
  (and the analogous `EllipticDivisibilitySequence` fork) and replace every
  `import LutzNagell.DivisionPolynomial*` with the mathlib imports
  `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` and
  `…DivisionPolynomial.Degree`. Then `WeierstrassCurve.natDegree_preΨ_le` (and all its
  siblings) resolve to the mathlib decls unchanged — downstream NagellLutz code that
  references `W.natDegree_preΨ_le`/`coeff_preΨ`/`natDegree_preΨ`/etc. keeps compiling
  verbatim, because the names and signatures are identical.
- If the fork is being kept *intentionally* (e.g. the project genuinely needs to modify
  these files for Nagell–Lutz and can't yet upstream), then this decl is simply not a
  mathlibable candidate and the entry is closed as "intentional vendored copy — exclude
  from upstreaming".

**Next action:** delete the forked declaration (as part of removing the vendored
`DivisionPolynomial*` files) and re-point imports at
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`; the mathlib
`WeierstrassCurve.natDegree_preΨ_le` covers every use unchanged. If the vendoring is
deliberate, mark this decl out-of-scope for mathlib (it is already in mathlib).

---

## Next step

Delete `WeierstrassCurve.natDegree_preΨ_le` from the project together with the rest of the
vendored `LutzNagell/DivisionPolynomial*.lean` fork, and import
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` instead — the mathlib
lemma is identical (same name, statement, and proof) and covers all call sites verbatim.

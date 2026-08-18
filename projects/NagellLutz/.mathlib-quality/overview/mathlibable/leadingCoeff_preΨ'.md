# Mathlibable assessment — `WeierstrassCurve.leadingCoeff_preΨ'`

**Verdict: NO-mathlib-has-it**

The declaration is a verbatim copy of an existing mathlib lemma. Do not add it.

---

## 1. Declaration under review

- **Parsed/verified qualified name:** `WeierstrassCurve.leadingCoeff_preΨ'`
  (file is `namespace WeierstrassCurve`; base name `leadingCoeff_preΨ'`).
- **Location:** `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:256`
- **Statement (project copy):**

  ```lean
  @[simp]
  lemma leadingCoeff_preΨ' {n : ℕ} (h : (n : R) ≠ 0) :
      (W.preΨ' n).leadingCoeff = if Even n then n / 2 else n := by
    rw [leadingCoeff, W.natDegree_preΨ' h, coeff_preΨ']
  ```

  Context: `variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)`.

Mathematical content: for a Weierstrass curve `W` over a commutative ring `R`, the univariate
"pre-ψ" division polynomial `preΨ' n` (the polynomial part of the normalised EDS) has leading
coefficient `n/2` when `n` is even and `n` when `n` is odd, provided `(n : R) ≠ 0`. This is the
leading-term computation underlying Silverman's division-polynomial degree facts
(*The Arithmetic of Elliptic Curves*, division polynomials), used in the Nagell–Lutz development.

---

## 2. Mathlib search — IT IS ALREADY THERE (exact duplicate)

Mathlib contains this lemma **verbatim**:

- **`WeierstrassCurve.leadingCoeff_preΨ'`** in
  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:259`
  (cached at `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`):

  ```lean
  @[simp]
  lemma leadingCoeff_preΨ' {n : ℕ} (h : (n : R) ≠ 0) :
      (W.preΨ' n).leadingCoeff = if Even n then n / 2 else n := by
    rw [leadingCoeff, W.natDegree_preΨ' h, coeff_preΨ']
  ```

A direct `diff` of the project lemma (lines 255–258) against the mathlib lemma (lines 258–261)
reports **IDENTICAL** — same name, same namespace, same binders, same statement, same `@[simp]`
attribute, same one-line proof `rw [leadingCoeff, W.natDegree_preΨ' h, coeff_preΨ']`.

### Why the duplicate exists (project context)

This is a deliberate, documented **fork**, not independent work:

- The project's `LutzNagell/DivisionPolynomial.lean` header states: *"This is a copy of
  `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports
  `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts
  (both define `normEDS`, `complEDS`, etc.)."*
- `LutzNagell/DivisionPolynomialDegree.lean` header states: *"a project copy of mathlib's Basic
  file."* Its `## Main statements` list is identical to mathlib's `Degree.lean` main-statements
  list.
- The underlying `preΨ'` is itself the mathlib definition: mathlib defines
  `noncomputable def preΨ'` at `…/DivisionPolynomial/Basic.lean:153`; the project re-defines the same
  `preΨ'` at `LutzNagell/DivisionPolynomial.lean:76` only so it can be built on the project's local
  `EllipticDivisibilitySequence` (forked to dodge the `normEDS` name clash). The mathematical object
  is the same.

So the only reason the project carries its own `leadingCoeff_preΨ'` is the `normEDS`/`complEDS`
naming collision in the forked EDS layer — a packaging artifact, not a mathematical gap.

### Five-method search summary

1. **Exact name** — `leadingCoeff_preΨ'` found in mathlib `Degree.lean:259`. Hit.
2. **Namespace / dot** — `WeierstrassCurve.leadingCoeff_preΨ'`. Hit (same).
3. **Statement / `leadingCoeff (preΨ' …)`** — `grep` for `leadingCoeff_preΨ` across mathlib also
   surfaces the integer-indexed companion `leadingCoeff_preΨ` (`Degree.lean:310`), plus
   `leadingCoeff_preΨ₄` (`:145`) — the surrounding API is fully present.
4. **Forked-file check** (per task instructions: look at mathlib's DivisionPolynomial files first) —
   `Mathlib/.../DivisionPolynomial/{Basic,Degree}.lean` both exist and the project files are copies
   of them. Confirmed.
5. **Companion lemmas** — `natDegree_preΨ'_le`, `coeff_preΨ'`, `coeff_preΨ'_ne_zero`,
   `natDegree_preΨ'`, `natDegree_preΨ'_pos`, `preΨ'_ne_zero` all appear identically in both the
   project file and mathlib `Degree.lean`. The whole block is a fork.

---

## 3. Generality analysis

Not applicable for the verdict: mathlib already has the lemma in **exactly** this generality
(`R` a `CommRing`, hypothesis `(n : R) ≠ 0`, `n : ℕ`). The project statement matches it character for
character, so there is no weaker/stronger form to reconcile. Mathlib's own form is the standard one
(it is literally the same declaration authored by D. K. Angdinata in both places).

---

## 4. Composition check

Not needed for the verdict — the lemma is not merely *composable* from mathlib, it **is** a mathlib
lemma already. (For the record, its own proof is a 3-rewrite composition
`leadingCoeff` + `natDegree_preΨ'` + `coeff_preΨ'`, all of which are likewise present in mathlib.)

---

## 5. Literature note

The result is the leading-coefficient half of the classical division-polynomial degree computation
(Silverman, *The Arithmetic of Elliptic Curves*, Exercise 3.7 / division-polynomial recursion). It is
genuine textbook content and rightly lives in mathlib — where it already does. No external literature
sweep changes the verdict.

---

## 6. Decision

| Criterion | Finding |
|---|---|
| Already in mathlib? | **Yes — `WeierstrassCurve.leadingCoeff_preΨ'`, `…/DivisionPolynomial/Degree.lean:259`** |
| Same name & namespace? | Yes |
| Same statement? | Yes — `diff` reports IDENTICAL |
| Same `@[simp]` attr & proof? | Yes |
| Why the project has a copy | Documented fork of mathlib `Basic`/`Degree` to swap the local `EllipticDivisibilitySequence` (avoids `normEDS`/`complEDS` clash) |

**Bucket: `NO-mathlib-has-it`.**

**Recommendation:** Nothing to upstream. The project copy exists only to support the forked EDS
layer. Cleanup-side, this duplication is resolved if/when the project drops its EDS fork and depends
on `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` directly — but that is a
de-duplication/refactor concern for the project, **not** a mathlib contribution.

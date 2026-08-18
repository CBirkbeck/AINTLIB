# Mathlibable assessment — `WeierstrassCurve.natDegree_Ψ₃_le`

**Verdict: NO-mathlib-has-it**

> One-line: This is a verbatim fork of an existing mathlib declaration — same name, same
> statement, same proof, same author — in the file the project explicitly copied.

---

## 0. Declaration under assessment

- **Qualified name (verified from source):** `WeierstrassCurve.natDegree_Ψ₃_le`
  - Namespace `WeierstrassCurve` (file line 55: `namespace WeierstrassCurve`).
  - `variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)`.
- **Location:** `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:91`
- **Statement + proof (project copy):**

  ```lean
  lemma natDegree_Ψ₃_le : W.Ψ₃.natDegree ≤ 4 := by
    rw [Ψ₃]
    compute_degree
  ```

  where (`LutzNagell/DivisionPolynomial.lean:65`)

  ```lean
  /-- The `3`-division polynomial `ψ₃ = Ψ₃`. -/
  noncomputable def Ψ₃ : R[X] :=
    3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈
  ```

**Meaning.** Over any commutative ring `R`, the univariate 3-division polynomial `Ψ₃` of a
Weierstrass curve `W` has natural degree at most `4`. (Companion lemmas in the same section give
`coeff_Ψ₃ : W.Ψ₃.coeff 4 = 3`, and hence `natDegree_Ψ₃ = 4` and `leadingCoeff_Ψ₃ = 3` once
`(3 : R) ≠ 0`.)

---

## 1. Literature search

The degree/leading-coefficient facts for division polynomials are completely standard, textbook
material:

- **J. H. Silverman, *The Arithmetic of Elliptic Curves* (GTM 106), Exercise 3.7** — the file's own
  `## References` cites `[silverman2009]`. For odd `m`, `ψ_m` has degree `(m² − 1)/2` with leading
  coefficient `m`; for `m = 3` this is degree `4`, leading coefficient `3`. The `≤ 4` bound here is
  exactly the "degree at most" half of that statement.
- Web search corroboration: multiple references (e.g. arXiv:1303.5002 "coefficients of division
  polynomials", arXiv:1303.4327 "Homogeneous division polynomials for Weierstrass elliptic curves")
  restate "if `m` is odd then `ψ_m` has degree `(m²−1)/2` and the leading coefficient is `m`",
  citing Silverman as the classical source.

The numbers (degree `4`, leading coefficient `3`) match the Lean statement precisely. There is no
literature-standard form *more general* than "for general `n`" — and mathlib already has that
general version too (see §3).

## 2. Mathlib search — IT IS ALREADY THERE (verbatim)

`natDegree_Ψ₃_le` exists in current mathlib, **identical down to the byte**:

- **File:** `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`
  (inspected at a live checkout, `…/cheb-stackB/.lake/packages/mathlib/…`, mathlib commit
  `66748b489336`, 2026-06-02; the file is long-stable and authored 2024).
- **Line 95:**

  ```lean
  lemma natDegree_Ψ₃_le : W.Ψ₃.natDegree ≤ 4 := by
    rw [Ψ₃]
    compute_degree
  ```

- Same namespace (`WeierstrassCurve`, line 59), same `variable {R : Type u} [CommRing R]
  (W : WeierstrassCurve R)` (line 61), same `open Polynomial`.

**Mechanical confirmation of identity.** `diff` of the project's Ψ₃ section
(`DivisionPolynomialDegree.lean:91–116`) against mathlib's Ψ₃ section
(`Degree.lean:95–120`) returns **empty** — the two blocks (`natDegree_Ψ₃_le`, `coeff_Ψ₃`,
`coeff_Ψ₃_ne_zero`, `natDegree_Ψ₃`, `natDegree_Ψ₃_pos`, `leadingCoeff_Ψ₃`, `Ψ₃_ne_zero`) are
character-for-character identical. The underlying `def Ψ₃` is also identical to mathlib's.

**This is a documented fork, not an independent re-derivation.**
- The defining file's header (`LutzNagell/DivisionPolynomial.lean:12–13`) states verbatim:
  *"This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that
  imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid …"*.
- The degree file's header (`DivisionPolynomialDegree.lean:13–14`) calls itself *"a project copy of
  mathlib's Basic file"*.
- Both carry the original mathlib copyright: *"Copyright (c) 2024 David Kurniadi Angdinata …
  Authors: David Kurniadi Angdinata"* — the same person who wrote the mathlib originals.

The fork exists **only** so the project can swap in its local copy of
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (the `preNormEDS'` machinery that `Ψ₃` and the
degree induction build on). It is not new mathematics, not a strengthening, and not a different
proof.

## 3. Generality analysis

No generalisation is available or warranted:

- The hypotheses are already maximal: `[CommRing R]` (no domain, no characteristic assumption) and
  the bound is the unconditional `≤ 4`. The conditional sharpenings (`natDegree_Ψ₃ = 4`,
  `leadingCoeff_Ψ₃ = 3` under `(3 : R) ≠ 0`) are the separate companion lemmas, also already in
  mathlib.
- The general-`n` statement is *also* already in mathlib in the same file. `Degree.lean:210`:
  ```lean
  | three => simpa only [preΨ'_three] using ⟨W.natDegree_Ψ₃_le, W.coeff_Ψ₃ ▸ Int.cast_three.symm⟩
  ```
  i.e. `natDegree_Ψ₃_le` is consumed as the `n = 3` base case of mathlib's general
  `natDegree_preΨ'_le` / `natDegree_preΨ_le` induction. So mathlib covers both the specific lemma
  and its `∀ n` generalisation.

There is nothing to weaken or widen.

## 4. Composition check

Not applicable as a reason to add: the declaration is **literally present** in mathlib, so the
question "can ≤ 3 mathlib calls reconstruct it?" is moot. (For the record it is also a one-liner
— `rw [Ψ₃]; compute_degree` — but that is irrelevant given the verbatim hit.)

## 5. Five-bucket verdict

**NO-mathlib-has-it.**

Required evidence (the exact mathlib declaration):
- **Name:** `WeierstrassCurve.natDegree_Ψ₃_le`
- **Mathlib path:** `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:95`
- **Match quality:** identical name, identical signature, identical proof (`diff` of the whole Ψ₃
  block is empty); identical underlying `def Ψ₃`; same author and copyright; the project file's own
  docstring states it is a copy of the mathlib file.

**Recommendation.** Do not contribute. This declaration is the mathlib original. The project should
ideally `import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` and delete the
local copy; the fork is justified only by the parallel `EllipticDivisibilitySequence` copy, and if
that local copy is ever reconciled back to mathlib the entire `DivisionPolynomialDegree.lean` file
(this lemma included) becomes dead duplication. Within mathlib-quality terms this is a
cross-project **dedup-against-mathlib** item, not a mathlib-submission candidate.

---

### Sources
- [Beyond two criteria for supersingularity: coefficients of division polynomials (arXiv:1303.5002)](https://arxiv.org/pdf/1303.5002)
- [Homogeneous division polynomials for Weierstrass elliptic curves (arXiv:1303.4327)](https://arxiv.org/pdf/1303.4327)
- J. H. Silverman, *The Arithmetic of Elliptic Curves*, GTM 106 (cited in-file as `[silverman2009]`), Exercise 3.7.
- Mathlib source: `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean` (lemma `natDegree_Ψ₃_le`).

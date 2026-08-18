# Mathlibable assessment: `WeierstrassCurve.coeff_preΨ₄_ne_zero`

**Verdict: NO-mathlib-has-it**

**One-line rationale:** This declaration is a verbatim copy of a lemma that already exists in
mathlib (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`), confirmed
character-for-character against current mathlib `master`.

---

## 1. The declaration under review

Source: `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:130`

```lean
namespace WeierstrassCurve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

lemma coeff_preΨ₄_ne_zero (h : (2 : R) ≠ 0) : W.preΨ₄.coeff 6 ≠ 0 := by
  rwa [coeff_preΨ₄]
```

Parsed/verified qualified name: **`WeierstrassCurve.coeff_preΨ₄_ne_zero`** (the prompt's guess was
correct — confirmed from `namespace WeierstrassCurve` at line 55 of the source file).

**Mathematical content.** For a Weierstrass curve `W` over a commutative ring `R`, `preΨ₄` is the
fixed degree-6 univariate polynomial auxiliary to the 4-division polynomial
`ψ₄ = Ψ₄ = preΨ₄ · ψ₂`:

```
preΨ₄ = 2·X⁶ + b₂·X⁵ + 5·b₄·X⁴ + 10·b₆·X³ + 10·b₈·X² + (b₂b₈ − b₄b₆)·X + (b₄b₈ − b₆²).
```

Its `X⁶`-coefficient is the constant `2`, so the lemma is the trivial statement "if `2 ≠ 0` in `R`
then `(2 : R) ≠ 0`", routed through the already-proved `@[simp]` lemma `coeff_preΨ₄ : coeff 6 = 2`.
It is a one-line micro-lemma whose only role is to feed `natDegree_preΨ₄` (degree `= 6` when
`2 ≠ 0`) via `natDegree_eq_of_le_of_coeff_ne_zero`.

## 2. Why this file is a fork of mathlib (project context)

The project header is explicit. `LutzNagell/DivisionPolynomial.lean` lines 12–14 state:

> This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that
> imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid
> name conflicts (both define `normEDS`, `complEDS`, etc.).

`DivisionPolynomialDegree.lean` is the corresponding copy of mathlib's
`.../DivisionPolynomial/Degree.lean`. The header, `namespace`, `variable` line, section structure,
docstrings, statements and proofs are all reproduced. The fork exists purely so the Nagell–Lutz
development can swap in its local `EllipticDivisibilitySequence` copy — **not** because any new
mathematics was added here. This is exactly the "duplicated fork of mathlib" case the prompt warned
about.

## 3. Mathlib search (five methods)

- **Exact-name / source read.** `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`
  contains, in `namespace WeierstrassCurve` with `variable {R : Type u} [CommRing R]
  (W : WeierstrassCurve R)`:
  ```lean
  lemma coeff_preΨ₄_ne_zero (h : (2 : R) ≠ 0) : W.preΨ₄.coeff 6 ≠ 0 := by
    rwa [coeff_preΨ₄]
  ```
  This is **byte-identical** to the project declaration (same name, signature, proof, namespace).
- **Local mathlib caches.** Found in *two* independent vendored mathlib trees on this machine:
  - project pin `09b373db…` (`.lake/packages/mathlib`), and
  - the loogle-index mathlib `3ea6690c…` dated 2025-12-15 (which is on the *newer* `module` /
    `public import` system) — so the lemma is stable across mathlib versions, not an artifact of one
    stale checkout.
- **Live mathlib `master` (GitHub).** Fetched
  `raw.githubusercontent.com/leanprover-community/mathlib4/master/.../DivisionPolynomial/Degree.lean`
  → the lemma `coeff_preΨ₄_ne_zero` is present today, identical statement and proof, namespace
  `WeierstrassCurve`. ✅ definitive.
- **Sibling lemmas confirm the whole block was copied.** `natDegree_preΨ₄_le`, `coeff_preΨ₄`,
  `natDegree_preΨ₄`, `natDegree_preΨ₄_pos`, `leadingCoeff_preΨ₄`, `preΨ₄_ne_zero` all match mathlib's
  `Degree.lean` line-for-line (project lines 121–145 vs mathlib lines 125–149).

## 4. Generality / composition analysis

Not applicable in the usual sense — there is no "more general form to prefer" and no "compose from
primitives" question, because the *identical* declaration already exists upstream. (For completeness:
the lemma is already at the natural generality — `CommRing R` with the single side hypothesis
`(2 : R) ≠ 0`, which is exactly what `natDegree_preΨ₄` needs. The `2`-specific shape is intrinsic to
`preΨ₄`'s fixed leading coefficient and is correct as stated.)

## 5. Literature

The construction is standard: Silverman, *The Arithmetic of Elliptic Curves* (cited in both the
project file and mathlib's `Degree.lean`), division-polynomial leading-term computations. The
mathlib originals are due to David Kurniadi Angdinata (2024), the same author named in the project
file's copyright header — further confirming this is a transplanted mathlib file, not new work.

## 6. Verdict

**NO-mathlib-has-it.**

The declaration `WeierstrassCurve.coeff_preΨ₄_ne_zero` is already in mathlib, verbatim, in
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`. There is nothing to add or
generalise. The project copy is a deliberate fork to dodge `normEDS`/`complEDS` name clashes with the
project's local `EllipticDivisibilitySequence`; when the consolidation/dedup pass reconciles the
local `EllipticDivisibilitySequence` copy against mathlib's, this lemma (and its entire `preΨ₄`
section) should drop out in favour of the upstream version.

**Evidence pointer (mathlib):** `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`,
`lemma coeff_preΨ₄_ne_zero` — confirmed on mathlib `master` and in two local vendored mathlib trees.

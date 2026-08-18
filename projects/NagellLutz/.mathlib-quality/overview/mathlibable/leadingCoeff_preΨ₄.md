# Mathlibable assessment: `WeierstrassCurve.leadingCoeff_preΨ₄`

**Verdict: NO-mathlib-has-it**

**One-line rationale:** Byte-identical copy of an existing mathlib lemma — the project file is a self-declared fork of mathlib's `DivisionPolynomial/Degree.lean`.

---

## 1. Declaration under assessment

- **Qualified name (VERIFIED):** `WeierstrassCurve.leadingCoeff_preΨ₄`
  (namespace `WeierstrassCurve`, opened at line 55 of the project file; base name `leadingCoeff_preΨ₄`)
- **Location:** `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:140-142`
- **Statement (project):**
  ```lean
  @[simp]
  lemma leadingCoeff_preΨ₄ (h : (2 : R) ≠ 0) : W.preΨ₄.leadingCoeff = 2 := by
    rw [leadingCoeff, W.natDegree_preΨ₄ h, coeff_preΨ₄]
  ```
  with `variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)`.

Mathematical content: for a Weierstrass curve `W` over a commutative ring `R` in which `2 ≠ 0`,
the fourth pre-division polynomial `preΨ₄` (a univariate polynomial in `R[X]`) has leading
coefficient `2`. (Companion facts in the same section give `natDegree preΨ₄ = 6` and `coeff … 6 = 2`.)

## 2. Literature search

The relevant "literature" here is mathlib's own division-polynomial development, authored by
David Kurniadi Angdinata (the very same author named in this project file's copyright header),
following [Silverman, *The Arithmetic of Elliptic Curves*]. Division polynomials `ψₙ` and their
leading coefficients are classical (Silverman Ch. III, Ex. 3.7); the `n = 4` value `leadingCoeff = 2`
matches the general formula `n/2` for even `n` (`4/2 = 2`).

WebSearch for `mathlib WeierstrassCurve leadingCoeff_preΨ₄ division polynomial` returns, as the
**top hit**, the official mathlib4 documentation page
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.html`, which documents exactly
`WeierstrassCurve.leadingCoeff_preΨ₄` (leading coefficient of `preΨ₄` is `2`). So the name is the
*upstream* mathlib name, not a project coinage.

## 3. Mathlib search — IT IS ALREADY THERE (verbatim)

Direct source inspection of a local mathlib checkout
(`…/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`, rev
`718d4e20c09a`, dated 2026-04-16 — newer than AINTLIB's pin `09b373db6e24`, so the lemma is
current upstream, not removed) shows at **line 144-146**:

```lean
@[simp]
lemma leadingCoeff_preΨ₄ (h : (2 : R) ≠ 0) : W.preΨ₄.leadingCoeff = 2 := by
  rw [leadingCoeff, W.natDegree_preΨ₄ h, coeff_preΨ₄]
```

This is **byte-for-byte identical** to the project declaration: same `@[simp]` attribute, same
hypothesis `(h : (2 : R) ≠ 0)`, same statement `W.preΨ₄.leadingCoeff = 2`, same one-line proof
`rw [leadingCoeff, W.natDegree_preΨ₄ h, coeff_preΨ₄]`, same `WeierstrassCurve` namespace, same
`[CommRing R]` typeclass context. The surrounding `section preΨ₄` (and indeed the whole file,
including the module docstring and Main-statements list) is identical to the project's
`DivisionPolynomialDegree.lean`.

This is not a coincidence; it is an **explicit, self-declared fork**:
- `DivisionPolynomialDegree.lean:12-14` — "This file computes the leading terms of certain
  polynomials … defined in `LutzNagell/DivisionPolynomial.lean` (a project copy of mathlib's Basic
  file)."
- `DivisionPolynomial.lean:10-14` — "This is a copy of
  `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports
  `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts
  (both define `normEDS`, `complEDS`, etc.). See the original file for full documentation."

The fork exists purely to swap the underlying `EllipticDivisibilitySequence` import (the project
vendors its own copy to avoid `normEDS`/`complEDS` clashes); it does **not** strengthen, generalise,
or otherwise change this lemma.

## 4. Generality analysis

No generalisation is on the table: the project statement and the mathlib statement are identical
over the same `[CommRing R]`. The natural "more general" companion is also already in mathlib in the
same file — `WeierstrassCurve.leadingCoeff_preΨ` (line 310 upstream): for `{n : ℤ}` with `(n : R) ≠ 0`,
`(W.preΨ n).leadingCoeff = if Even n then n / 2 else n`. The `…₄` lemma is the convenience
specialisation at `n = 4`, and mathlib already ships **both** the general and the specialised form.
(The project's own consumers use both: `GeneralPrimeOrder.lean:132` and `PIDPrimeOrder.lean:166`
rewrite with `W.leadingCoeff_preΨ₄`, while lines 98/129 use the general `W.leadingCoeff_preΨ`.)

## 5. Composition check

Not applicable / trivially satisfied: the lemma is literally present in mathlib, so it requires
**zero** new declarations upstream. (For completeness, its own proof is a 1-line composition of the
already-upstream `leadingCoeff` unfold + `natDegree_preΨ₄` + `coeff_preΨ₄`, all of which are also in
the same mathlib file.)

## 6. Verdict

**NO-mathlib-has-it.** `WeierstrassCurve.leadingCoeff_preΨ₄` already exists in mathlib at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean` (confirmed by direct source
inspection and by the official mathlib4 docs), with an identical statement and proof. The project
copy is a deliberate fork created only to retarget the `EllipticDivisibilitySequence` import; it
carries no new mathematical content. There is nothing to upstream.

Consolidation note for AINTLIB: this whole `DivisionPolynomialDegree.lean` file is a verbatim copy
of upstream `DivisionPolynomial/Degree.lean`. The right long-term move is to drop the fork and
import mathlib's file directly once the `normEDS`/`complEDS` naming conflict that motivated the
vendored `EllipticDivisibilitySequence` is resolved (e.g. by upstreaming the project's EDS additions
or namespacing them) — not to PR this lemma.

### Sources
- mathlib4 docs — [`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.html)
- mathlib4 docs — [`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.html)
- Local mathlib source: `…/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:144-146` (rev `718d4e20c09a`)
- Silverman, *The Arithmetic of Elliptic Curves*, Ch. III (division polynomials)

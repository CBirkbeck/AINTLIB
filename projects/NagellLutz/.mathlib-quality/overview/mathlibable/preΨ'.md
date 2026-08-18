# Mathlibable assessment — `WeierstrassCurve.preΨ'`

**Verdict:** `NO-mathlib-has-it`
**Qualified name:** `WeierstrassCurve.preΨ'`
**Date:** 2026-06-22
**Project:** NagellLutz (Nagell–Lutz theorem; division polynomials; elliptic divisibility sequences)

---

## 1. The declaration under assessment

`projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:76`

```lean
namespace WeierstrassCurve
variable {R : Type r} [CommRing R] (W : WeierstrassCurve R)

/-- The univariate polynomials `preΨₙ` for `n ∈ ℕ`, which are auxiliary to the bivariate
polynomials `Ψₙ` congruent to the bivariate `n`-division polynomials `ψₙ`. -/
noncomputable def preΨ' (n : ℕ) : R[X] :=
  preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n
```

The parsed qualified name is **`WeierstrassCurve.preΨ'`** (the file opens `namespace WeierstrassCurve`
at line 27 and never leaves it before line 76). VERIFIED from source.

It is the auxiliary univariate (`R[X]`) sequence `preΨₙ` for `n ∈ ℕ`: the `R[X]`-valued normalised
EDS auxiliary sequence with extra parameter `Ψ₂Sq²` and initial values `preΨ₀ = 0`, `preΨ₁ = 1`,
`preΨ₂ = 1`, `preΨ₃ = Ψ₃`, `preΨ₄ = preΨ₄`. It is a thin specialisation of the generic
`preNormEDS'` recurrence to the division-polynomial data of a Weierstrass curve.

## 2. Mathlib search — it is already there, verbatim

This project's own file header states the situation outright (lines 12–14):

> This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports
> `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts
> (both define `normEDS`, `complEDS`, etc.).

Confirmed by reading the live mathlib checkout at
`/Users/mcu22seu/Documents/GitHub/aintlib-adic-spaces/.lake/packages/mathlib`:

`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:153–154`

```lean
namespace WeierstrassCurve
variable {R : Type r} [CommRing R] (W : WeierstrassCurve R)

/-- The univariate polynomials `preΨₙ` for `n ∈ ℕ`, which are auxiliary to the bivariate
polynomials `Ψₙ` congruent to the bivariate `n`-division polynomials `ψₙ`. -/
noncomputable def preΨ' (n : ℕ) : R[X] :=
  preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n
```

The match is exact on every axis:

| axis | project | mathlib |
|---|---|---|
| namespace | `WeierstrassCurve` | `WeierstrassCurve` |
| base name | `preΨ'` | `preΨ'` |
| signature | `(n : ℕ) : R[X]` over `(W : WeierstrassCurve R)` | identical |
| body | `preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n` | identical |
| docstring | identical | identical |
| copyright / author | David Kurniadi Angdinata, 2024 | identical |

The supporting API is duplicated too (`preΨ'_zero/one/two/three/four/even/odd`, `map_preΨ'`,
`baseChange_preΨ'` — all present in both, byte-for-byte). The primitive `preΨ'` depends on,
`preNormEDS'`, also exists in mathlib at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:124` (the project's
`LutzNagell.EllipticDivisibilitySequence.preNormEDS'` is the same definition with explicit `(b c d)`
binders and a couple of extra termination `have`s — mathematically identical).

### Five-method mathlib search

1. **Exact-name / source grep** — `grep "preΨ'"` in mathlib's `DivisionPolynomial/Basic.lean`
   returns the identical `def` plus its whole lemma family. Decisive.
2. **leansearch / loogle (mathlib index)** — not needed; the source grep is already conclusive for a
   same-name, same-namespace, same-body declaration. (`preΨ'` / `preNormEDS'` are indexed mathlib
   names.)
3. **Dependency primitive** — `preNormEDS'` located in mathlib `EllipticDivisibilitySequence.lean`.
4. **Consumers** — `Ψ_ofNat`, `ΨSq_ofNat`, `Φ_ofNat`, `map_preΨ'`, `baseChange_preΨ'` all present in
   mathlib, confirming `preΨ'` is a fully integrated mathlib API surface, not a fragment.
5. **Provenance** — the project header and identical copyright header confirm it was *copied from*
   mathlib, not independently invented.

## 3. Generality analysis

Not applicable to the verdict: the mathlib form is identical (same `[CommRing R]`, same universe,
same `WeierstrassCurve R`). There is no weaker hypothesis set to reach — the project copy is not
more general than mathlib's (it is the same definition). Mathlib's version is the canonical,
maximally-integrated form.

## 4. Composition check

Trivially yes — `preΨ'` *is* a one-line composition: `preNormEDS'` applied to `Ψ₂Sq ^ 2`, `Ψ₃`,
`preΨ₄`. But this is moot, because the fully-assembled definition (and its name) already lives in
mathlib. There is nothing to add.

## 5. Why the fork exists (and why it is not a mathlib candidate)

The NagellLutz project forks `Mathlib.NumberTheory.EllipticDivisibilitySequence` and
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` (the `General*`/`PID*` tracks) so it
can extend/modify the EDS development locally without colliding with the imported mathlib names.
`preΨ'` rides along in that copy purely as a mechanical consequence — it is not new mathematics and
was never intended to be upstreamed; it already *is* upstream.

The correct disposition is **deduplication**: downstream NagellLutz code should ultimately use
`WeierstrassCurve.preΨ'` from `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`
directly, and the local copy should be removed once the fork's divergent parts (if any) are isolated
or upstreamed. That is a cleanup/dedup ticket on `main`, not a mathlib contribution.

## 6. Verdict

**`NO-mathlib-has-it`.** `WeierstrassCurve.preΨ'` exists in mathlib verbatim — identical namespace,
name, signature, body, docstring, and author — at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:153`. The project's copy is an
explicit fork made only to dodge a name clash with the project's own forked EDS file. No
literature/generalisation work is warranted; the action item is dedup against mathlib, not addition.

**Evidence (required for this bucket):** mathlib declaration `WeierstrassCurve.preΨ'` at
`.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:153–154`,
body `preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n` — byte-for-byte identical to the project declaration.

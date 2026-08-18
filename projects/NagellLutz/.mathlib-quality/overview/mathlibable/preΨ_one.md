# Mathlibable assessment: `WeierstrassCurve.preΨ_one`

**Verdict: `NO-mathlib-has-it`**

## Declaration under review

- **Parsed qualified name:** `WeierstrassCurve.preΨ_one` (VERIFIED — `namespace WeierstrassCurve`
  is open at line 27; the lemma base name is `preΨ_one`).
- **Location:** `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:129`
- **Statement + proof (exact):**

```lean
@[simp]
lemma preΨ_one : W.preΨ 1 = 1 :=
  preNormEDS_one ..
```

Here `W : WeierstrassCurve R` with `[CommRing R]`, and `W.preΨ (n : ℤ) : R[X]` is defined
(line 117) as `preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n`. So the lemma says: the univariate
"pre-division polynomial" of a Weierstrass curve, evaluated at index `1`, equals the constant
polynomial `1`. It is the trivial base case of the division-polynomial / elliptic-divisibility
recursion, and is a one-line specialisation of the underlying EDS lemma `preNormEDS_one`.

## 1. Literature search

The notion is the well-known base case of the **division polynomials** of an elliptic curve,
equivalently the normalisation of an **elliptic divisibility sequence (EDS)**: ψ₁ = 1 (and the
auxiliary preψ₁ = 1). This is utterly standard — Silverman, *The Arithmetic of Elliptic Curves*
(Exercise 3.7 / division-polynomial recursion); Ward's original EDS papers; the Wikipedia EDS page.
There is no research novelty whatsoever: it is a definitional initial condition.

Sources:
- [Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic (mathlib4 docs)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.html)
- [Mathlib.NumberTheory.EllipticDivisibilitySequence (mathlib4 docs)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html)
- [Elliptic divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence)

## 2. Mathlib search — IS IT THERE?

**Yes — verbatim, character-for-character identical, including the `@[simp]` attribute, the
statement, and the proof term.**

The NagellLutz project is an explicit, acknowledged fork. The file's own module docstring
(`DivisionPolynomial.lean:12-14`) states:

> "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that
> imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid
> name conflicts (both define `normEDS`, `complEDS`, etc.)."

Direct evidence from the pinned mathlib in `.lake/packages/mathlib` (mathlib `d90090f`):

- `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:205-207`

  ```lean
  @[simp]
  lemma preΨ_one : W.preΨ 1 = 1 :=
    preNormEDS_one ..
  ```

  This is in `namespace WeierstrassCurve` exactly as in the project file ⇒ the mathlib name is
  also `WeierstrassCurve.preΨ_one`. **Identical name, statement, attribute, and proof.**

- The underlying EDS lemma it delegates to is likewise already in mathlib:
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:189-191`

  ```lean
  @[simp]
  lemma preNormEDS_one : preNormEDS b c d 1 = 1 := by
    simp [preNormEDS]
  ```

The five mathlib search methods all collapse to the same answer here: exact-name match
(`WeierstrassCurve.preΨ_one`), exact-statement match, the dependency (`preNormEDS_one`) is also
present, the surrounding API block (`preΨ_zero/one/two/three/four`, `preΨ_neg`, `preΨ_even/odd`)
is present line-for-line, and a web/docs search returns the mathlib4 docs page hosting it as the
top hit. There is nothing to disambiguate.

## 3. Generality analysis

The project statement and the mathlib statement are the same general form (`[CommRing R]`, any
Weierstrass curve `W`). The mathlib lemma is not *less* general, so there is no
"generalise-first" angle. (One could in principle phrase it purely at the EDS level — which
mathlib already does as `preNormEDS_one` — but the curve-specialised `preΨ_one` is a deliberate,
useful API wrapper that mathlib also chose to keep.)

## 4. Composition check

Trivially composable — it is literally one mathlib call: `preNormEDS_one ..`. But this is moot:
the *exact* lemma already exists in mathlib under the *exact same name*, so there is nothing to
re-derive.

## 5. Verdict

**`NO-mathlib-has-it`.** `WeierstrassCurve.preΨ_one` is present in mathlib verbatim at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:206` (same name, same
`@[simp]` statement, same proof). The project copy exists only because NagellLutz forks
`DivisionPolynomial.*` + `EllipticDivisibilitySequence` to dodge name collisions while it develops
the Nagell–Lutz theorem; it is not a candidate for upstreaming. The consolidation action is to
**drop the fork and depend on mathlib** once the EDS-fork name-conflict issue is resolved — not to
add anything.

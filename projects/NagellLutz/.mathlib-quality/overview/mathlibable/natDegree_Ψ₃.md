# Mathlibable assessment — `WeierstrassCurve.natDegree_Ψ₃`

**Verdict: NO-mathlib-has-it** (exact, byte-identical duplicate of an existing mathlib lemma).

---

## 1. Declaration under review

- **Qualified name:** `WeierstrassCurve.natDegree_Ψ₃`
- **Location:** `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:104`
- **Statement (verified from source):**

  ```lean
  namespace WeierstrassCurve
  variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

  @[simp]
  lemma natDegree_Ψ₃ (h : (3 : R) ≠ 0) : W.Ψ₃.natDegree = 4 :=
    natDegree_eq_of_le_of_coeff_ne_zero W.natDegree_Ψ₃_le <| W.coeff_Ψ₃_ne_zero h
  ```

  Mathematically: for a Weierstrass curve `W` over a commutative ring `R` in which `3 ≠ 0`, the
  3-division polynomial `Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈` has degree exactly `4`. (Combines
  the degree bound `≤ 4` with non-vanishing of the leading coefficient `3`.)

---

## 2. Project context

The `NagellLutz` project **forks** mathlib's elliptic-curve division-polynomial files:

- `LutzNagell/DivisionPolynomial.lean`  ← copy of `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`
- `LutzNagell/DivisionPolynomialDegree.lean`  ← copy of `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`

Same author (David Kurniadi Angdinata), same copyright header, same docstring, same `## Main
statements` list. The only deltas are the local `import LutzNagell.DivisionPolynomial` (instead of
mathlib's `…/DivisionPolynomial/Basic`) and the absence of mathlib's `module` / `public section`
wrapper. The project fork is a near-verbatim vendored copy.

---

## 3. Literature search

The claim "the n-division polynomial ψₙ of an elliptic curve in Weierstrass form has degree
(n²−1)/2 (n odd), with ψ₃ of degree 4 and leading coefficient 3" is **completely standard**:

- J. Silverman, *The Arithmetic of Elliptic Curves* (2009), Exercise 3.7 — division polynomials and
  their degrees. (Cited in both the project file and the mathlib file headers as `[silverman2009]`.)
- Washington, *Elliptic Curves: Number Theory and Cryptography* — §3.2, division polynomials.

This is not novel mathematics; it is a textbook degree computation. No literature gap.

---

## 4. Mathlib search (five methods)

Mathlib already contains this lemma **verbatim**.

- **File:** `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:108`
- **Mathlib statement (identical):**

  ```lean
  @[simp]
  lemma natDegree_Ψ₃ (h : (3 : R) ≠ 0) : W.Ψ₃.natDegree = 4 :=
    natDegree_eq_of_le_of_coeff_ne_zero W.natDegree_Ψ₃_le <| W.coeff_Ψ₃_ne_zero h
  ```

  → same name, same namespace (`WeierstrassCurve`), same hypothesis, same conclusion, same
  `@[simp]` attribute, **same proof term**.

Supporting chain also fully present in mathlib:
- `WeierstrassCurve.natDegree_Ψ₃_le`         — `Degree.lean:95`
- `WeierstrassCurve.coeff_Ψ₃` / `coeff_Ψ₃_ne_zero` — `Degree.lean:100,104`
- `Polynomial.natDegree_eq_of_le_of_coeff_ne_zero` — `Mathlib/Algebra/Polynomial/Degree/Operations.lean:69`
- `WeierstrassCurve.Ψ₃` (def, byte-identical: `3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈`) — `Basic.lean:142`

Mathlib pin for this checkout: `09b373db6e24` (toolchain v4.32.0-rc1).

(`lean_loogle` / `lean_leansearch` not needed — the decl was located directly in the vendored
mathlib source; a name/statement search would return this same lemma.)

---

## 5. Generality analysis

The hypothesis `(3 : R) ≠ 0` over a general `CommRing R` is already the maximally-general natural
form (no integral-domain / field / characteristic assumption needed for the degree-4 claim — only
that the leading coefficient `3` is nonzero). The project version and the mathlib version are
generality-identical. Nothing to weaken.

---

## 6. Composition check

Not merely composable from primitives — it is **literally the same lemma already in mathlib**, with
the same one-line proof. ≤ 3 mathlib calls is trivially satisfied because mathlib *is* the source.

---

## 7. Verdict

**NO-mathlib-has-it.**

`WeierstrassCurve.natDegree_Ψ₃` is a byte-for-byte duplicate of the existing mathlib lemma
`WeierstrassCurve.natDegree_Ψ₃` (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`).
The `NagellLutz` project vendored mathlib's `Degree.lean` (and its `Basic.lean` dependency) verbatim.
There is nothing to upstream: identical name, statement, proof, attribute, and namespace already
live in mathlib. The right cleanup action is to **drop the fork and import the mathlib file**
(`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`) once the project no longer
needs a divergent local copy.

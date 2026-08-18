# Mathlibable assessment — `WeierstrassCurve.coeff_Φ`

**Verdict: NO-mathlib-has-it**

**Qualified name:** `WeierstrassCurve.coeff_Φ`

---

## 1. The declaration under assessment

Source: `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:424`

```lean
@[simp]
lemma coeff_Φ (n : ℤ) : (W.Φ n).coeff (n.natAbs ^ 2) = 1 := by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_Φ_ofNat n).right
  | neg ih => rw [Φ_neg, Int.natAbs_neg, ih]
```

Context: `namespace WeierstrassCurve`, `variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)`,
`open Polynomial`.

Mathematical content: for a Weierstrass curve `W` over a commutative ring `R`, the univariate
polynomial `Φₙ ∈ R[X]` (the numerator of the `x`-coordinate of `[n]P`, congruent to `φₙ`) has its
coefficient in degree `n²` (= `|n|²`) equal to `1`. Equivalently: `Φₙ` is monic of degree `n²`.
This is the `coeff` half of the leading-term computation for the division-polynomial family
(`preΨₙ`, `ΨSqₙ`, `Φₙ`); it feeds `natDegree_Φ`, `leadingCoeff_Φ`, and `Φ_ne_zero`.

Reference for the mathematics: J. Silverman, *The Arithmetic of Elliptic Curves*, exercise 3.7
(division polynomials).

---

## 2. Mathlib search — IT IS ALREADY THERE (verbatim)

This project explicitly **forks** mathlib's elliptic-curve division-polynomial files. The project
file header (`DivisionPolynomialDegree.lean:14`) states it is *"a project copy of mathlib's Basic
file"*, and the underlying `LutzNagell/DivisionPolynomial.lean` copies
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`.

The decl exists in mathlib at:

`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:426`

```lean
@[simp]
lemma coeff_Φ (n : ℤ) : (W.Φ n).coeff (n.natAbs ^ 2) = 1 := by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_Φ_ofNat n).right
  | neg ih => rw [Φ_neg, Int.natAbs_neg, ih]
```

This is a **character-for-character identical** statement *and proof*, in the **same namespace**
(`WeierstrassCurve`), with the same `@[simp]` attribute.

Supporting evidence that this is the same declaration, not a coincidental restatement:

| Item | Project | Mathlib |
|---|---|---|
| Statement of `coeff_Φ` | `DivisionPolynomialDegree.lean:424` | `DivisionPolynomial/Degree.lean:426` |
| Proof body | identical | identical |
| Underlying `def Φ` | `DivisionPolynomial.lean:272`: `X * W.ΨSq n - W.preΨ (n + 1) * W.preΨ (n - 1) * if Even n then 1 else W.Ψ₂Sq` | `DivisionPolynomial/Basic.lean:349`: identical |
| Private helper `natDegree_coeff_Φ_ofNat` | `:386` | `Degree.lean:388` (identical) |
| File copyright | "Copyright (c) 2024 David Kurniadi Angdinata" | same |
| Module docstring / `## Main statements` list | identical (lists `WeierstrassCurve.coeff_Φ`) | identical |
| Author | David Kurniadi Angdinata | David Kurniadi Angdinata |

The whole `section Φ` (`coeff_Φ`, `coeff_Φ_ne_zero`, `natDegree_Φ`, `natDegree_Φ_pos`,
`leadingCoeff_Φ`, `Φ_ne_zero`) matches mathlib's `Degree.lean` line-for-line.

Mathlib's five-method search is moot here: a direct name + namespace match (`WeierstrassCurve.coeff_Φ`)
in the upstream source the project copied is the strongest possible "mathlib has it" evidence. (For
completeness: name search `coeff_Φ`, `exact?`-shaped lookup against `Polynomial.coeff`, and the
explicit `## Main statements` cross-reference all point at the same upstream lemma.)

---

## 3. Generality analysis

No generality gap. The mathlib decl already has the most general hypotheses for this statement:
`[CommRing R]` (no domain / nontriviality / characteristic assumption — `coeff = 1` is an honest
identity that holds over any commutative ring). The project copy carries the *same* `[CommRing R]`
signature. There is nothing to weaken; mathlib's form is already maximal.

---

## 4. Composition check

Not applicable / does not rescue it from duplication. The lemma is not a ≤3-call corollary of other
mathlib primitives — its proof is a dedicated `Int.negInduction` reducing to the private
`natDegree_coeff_Φ_ofNat` (a substantial `compute_degree`/`coeff`-bookkeeping induction over the
division-polynomial recurrence). But mathlib already *contains that whole development*, so the point
is academic: the result is present verbatim, not merely re-derivable.

---

## 5. Verdict

**NO-mathlib-has-it.**

`WeierstrassCurve.coeff_Φ` is a verbatim fork of the mathlib lemma of the same fully-qualified name in
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean` (same statement, same proof,
same `@[simp]`, same author, over the same definition `WeierstrassCurve.Φ`). It must not be
re-contributed. Cleanup action for the NagellLutz project: where possible, drop the local fork and
`import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`, using the upstream
`WeierstrassCurve.coeff_Φ` directly. (The project presumably forked the file only because it needed to
patch a *sibling* result; the forked copy of `coeff_Φ` itself is pure duplication.)

**Mathlib location:** `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:426`
(`WeierstrassCurve.coeff_Φ`).

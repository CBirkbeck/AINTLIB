# Mathlibable assessment — `WeierstrassCurve.natDegree_preΨ'_le`

- **Verdict:** `NO-mathlib-has-it`
- **Qualified name:** `WeierstrassCurve.natDegree_preΨ'_le`
- **Source:** `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:229`
- **Date:** 2026-06-22

## Statement (from project source)

```lean
namespace WeierstrassCurve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
open Polynomial
-- section preΨ'

lemma natDegree_preΨ'_le (n : ℕ) :
    (W.preΨ' n).natDegree ≤ (n ^ 2 - if Even n then 4 else 1) / 2 :=
  (W.natDegree_coeff_preΨ' n).left
```

The degree bound for the auxiliary division polynomial `preΨ'ₙ` of a Weierstrass curve `W` over
a commutative ring: `deg ≤ (n² − 4)/2` for even `n`, `(n² − 1)/2` for odd `n`. It is one half of
the strong-induction lemma `natDegree_coeff_preΨ'` (degree bound + leading coefficient).

## Search — is this already in mathlib?

**Yes. Verbatim.** The whole project file `DivisionPolynomialDegree.lean` is a forked copy of
mathlib's `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`.

Mathlib pin in this repo: `09b373db6e24` (2026-06-21), file present at
`.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`.

| Aspect | Project (`:229`) | Mathlib `Degree.lean:233` |
|---|---|---|
| Name | `natDegree_preΨ'_le` | `natDegree_preΨ'_le` |
| Namespace | `WeierstrassCurve` | `WeierstrassCurve` |
| Section | `preΨ'` | `preΨ'` |
| Variables | `{R : Type u} [CommRing R] (W : WeierstrassCurve R)` | identical |
| Statement | `(W.preΨ' n).natDegree ≤ (n ^ 2 - if Even n then 4 else 1) / 2` | **identical** |
| Proof term | `(W.natDegree_coeff_preΨ' n).left` | **identical** |

Supporting context is identical too: same module docstring, same `Authors: David Kurniadi
Angdinata`, same private helpers `expDegree` / `expCoeff` / `natDegree_coeff_preΨ'`, same section
layout (`Ψ₂Sq`, `Ψ₃`, `preΨ₄`, `preΨ'`, `preΨ`, `ΨSq`, `Φ`). Mathlib's copy is in fact marginally
newer (adjacent lemmas `coeff_preΨ'` / `natDegree_preΨ` are golfed with `convert!` / `using!`),
i.e. the project is a snapshot fork that upstream has since lightly polished.

Search methods applied:
1. Repo grep `natDegree_preΨ'` → the only definitions are the project copy and the mathlib copy.
2. Mathlib file read (`Degree.lean:200-254`) → exact match, same proof.
3. Name/namespace/section/variable/statement/proof-term cross-check → all identical (table above).

## Literature

Not required for this bucket. The literature-standard result (degree of division polynomials,
Silverman, *The Arithmetic of Elliptic Curves*, Exercise 3.7 / `[silverman2009]`, cited in both the
project and mathlib module docstrings) is already the content of the upstream mathlib lemma of the
same name. No more-general published form would change the verdict.

## Generality / composition

N/a — the declaration is upstream verbatim, at full generality (`[CommRing R]`, all `n : ℕ`). There
is no weaker/stronger or more-composable variant to consider; it simply already exists.

## Conclusion

`NO-mathlib-has-it`. `WeierstrassCurve.natDegree_preΨ'_le` is a byte-for-byte duplicate of
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`'s lemma of the same fully
qualified name. This is exactly the "forked mathlib DivisionPolynomial track" flagged in the project
context. Action for consolidation: drop the project fork and `import` the mathlib file instead (or,
on `main`, delete the duplicate once downstream NagellLutz code points at the mathlib lemma).

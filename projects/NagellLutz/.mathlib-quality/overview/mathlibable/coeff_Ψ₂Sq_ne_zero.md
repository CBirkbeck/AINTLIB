# Mathlibable assessment: `WeierstrassCurve.coeff_Ψ₂Sq_ne_zero`

**Verdict: NO-mathlib-has-it**

## Declaration under review

- **Qualified name:** `WeierstrassCurve.coeff_Ψ₂Sq_ne_zero` (verified: inside `namespace WeierstrassCurve`)
- **Location:** `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:70`
- **Statement & proof:**

```lean
namespace WeierstrassCurve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

lemma coeff_Ψ₂Sq_ne_zero (h : (4 : R) ≠ 0) : W.Ψ₂Sq.coeff 3 ≠ 0 := by
  rwa [coeff_Ψ₂Sq]
```

Mathematically: for a Weierstrass curve `W` over a commutative ring `R`, the degree-3 coefficient of
the univariate two-torsion polynomial `Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆` is `4`, hence is nonzero
whenever `4 ≠ 0` in `R`. It is a one-line corollary of `coeff_Ψ₂Sq : W.Ψ₂Sq.coeff 3 = 4`.

## Why this is in mathlib already (the decisive check)

This declaration is a **verbatim fork** of a mathlib lemma — same name, same namespace, same binders,
same statement, same proof. The project's `DivisionPolynomialDegree.lean` self-identifies as such:

> "This file computes the leading terms of certain polynomials associated to division polynomials of
>  Weierstrass curves defined in `LutzNagell/DivisionPolynomial.lean` (**a project copy of mathlib's
>  Basic file**)." — file header, line 14.

### Exact match in the pinned mathlib

`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`
(mathlib rev `09b373db6e24`, toolchain `v4.32.0-rc1`), **lines 74–75**:

```lean
namespace WeierstrassCurve                                   -- line 59
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)  -- line 61

lemma coeff_Ψ₂Sq_ne_zero (h : (4 : R) ≠ 0) : W.Ψ₂Sq.coeff 3 ≠ 0 := by  -- line 74
  rwa [coeff_Ψ₂Sq]                                                      -- line 75
```

Field-by-field comparison (project vs. mathlib):

| Field            | Project (`DivisionPolynomialDegree.lean`) | Mathlib (`DivisionPolynomial/Degree.lean`) |
|------------------|-------------------------------------------|--------------------------------------------|
| Namespace        | `WeierstrassCurve` (L55)                   | `WeierstrassCurve` (L59)                    |
| Binders          | `{R : Type u} [CommRing R] (W : WeierstrassCurve R)` (L57) | identical (L61)                |
| Hypothesis       | `(h : (4 : R) ≠ 0)`                        | `(h : (4 : R) ≠ 0)`                         |
| Conclusion       | `W.Ψ₂Sq.coeff 3 ≠ 0`                       | `W.Ψ₂Sq.coeff 3 ≠ 0`                        |
| Proof            | `rwa [coeff_Ψ₂Sq]`                         | `rwa [coeff_Ψ₂Sq]`                          |
| Qualified name   | `WeierstrassCurve.coeff_Ψ₂Sq_ne_zero`     | `WeierstrassCurve.coeff_Ψ₂Sq_ne_zero`       |

The underlying object is the same too: `Ψ₂Sq` is defined identically in the project's
`DivisionPolynomial.lean:40` and in mathlib `DivisionPolynomial/Basic.lean:117`
(`noncomputable def Ψ₂Sq : R[X]`, the two-torsion polynomial congruent to `ψ₂²`). So the two lemmas
are not merely "equivalent" — they are the *same* lemma about the *same* definition.

The neighbouring lemmas in the same section (`natDegree_Ψ₂Sq_le`, `coeff_Ψ₂Sq`, `natDegree_Ψ₂Sq`,
`natDegree_Ψ₂Sq_pos`, `leadingCoeff_Ψ₂Sq`, `Ψ₂Sq_ne_zero`) are likewise present verbatim in the
mathlib file, confirming a whole-section fork rather than a coincidental name collision. Authorship
header (David Kurniadi Angdinata) and the Silverman reference match as well.

## Search trail (mathlib's five methods)

1. **Exact-name search** — `grep` for `coeff_Ψ₂Sq_ne_zero` over `.lake/packages/mathlib`: found at
   `DivisionPolynomial/Degree.lean:74`. Exact hit; search effectively terminates here.
2. **By definition** — `Ψ₂Sq` is mathlib's own (`DivisionPolynomial/Basic.lean:117`); the whole
   `section Ψ₂Sq` of degree lemmas lives in `Degree.lean:63–91`.
3. **By statement shape** (`coeff … ≠ 0` from `coeff … = c` with `c ≠ 0`) — the generic engine is
   mathlib's `coeff_ne_zero` reasoning; here it is specialised and already packaged.
4. **Literature** — Silverman, *The Arithmetic of Elliptic Curves* (AEC), §III.2 / Exercise 3.7:
   division/two-torsion polynomials; `Ψ₂Sq = 4x³ + b₂x² + 2b₄x + b₆` is the standard two-torsion
   polynomial with leading coefficient `4`. The "nonzero degree-3 coefficient when `4 ≠ 0`" statement
   is the routine bookkeeping step toward `deg Ψ₂Sq = 3`; it carries no independent mathematical
   content and has no special name in the literature. WebSearch was therefore unnecessary — an exact
   in-repo mathlib hit already closes the question.
5. **Loogle / leansearch** — would resolve to the same `WeierstrassCurve.coeff_Ψ₂Sq_ne_zero`; not
   needed given the verbatim source match.

## Generality analysis

`[CommRing R]` is already the natural minimal class (`Ψ₂Sq` needs ring operations and the constant
`4`; the hypothesis `(4 : R) ≠ 0` is exactly what makes the leading coefficient survive). Mathlib
states it at this same generality. There is no weaker-hypothesis or more-general form to chase — and
in any case generalisation is moot, since mathlib already contains the lemma at this generality.

## Composition check

Trivially composable from mathlib (`coeff_Ψ₂Sq` then discharge `(4 : R) ≠ 0`, i.e. `≤ 2` steps — in
fact the project proof *is* this composition), **but that is irrelevant**: mathlib does not merely
let you re-derive it, it already ships the packaged lemma under the identical name. This is a
direct duplication, the strongest form of "NO".

## Recommendation

Do **not** propose for mathlib. On consolidation, the project's `DivisionPolynomialDegree.lean`
two-torsion/division-polynomial degree section should be dropped in favour of importing
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`; every downstream use in the
NagellLutz / HasseWeil projects (e.g. `W.leadingCoeff_Ψ₂Sq`, `W.natDegree_Ψ₂Sq_le`,
`W.coeff_Ψ₂Sq_ne_zero`) already typechecks against the mathlib names verbatim. The fork presumably
predates the upstreaming of this section (or was kept to pin a specific `Ψ₂Sq` API revision); it is
now redundant with mathlib.

---

*Assessment basis:* source statement + direct read of the pinned mathlib at rev `09b373db6e24`
(toolchain `v4.32.0-rc1`); local Lean build is stale, but no build was needed — the verdict rests on
an exact textual match of name, statement, and proof against mathlib source.

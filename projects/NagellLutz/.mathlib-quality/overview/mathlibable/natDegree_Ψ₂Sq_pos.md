# Mathlibable assessment: `WeierstrassCurve.natDegree_Ψ₂Sq_pos`

**Verdict: NO-mathlib-has-it**

**One-line rationale:** Character-identical to mathlib's
`WeierstrassCurve.natDegree_Ψ₂Sq_pos` (`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`,
lines 81–82); the project file is a verbatim fork.

---

## 1. The declaration under assessment

Source: `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:77`

```lean
namespace WeierstrassCurve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

lemma natDegree_Ψ₂Sq_pos (h : (4 : R) ≠ 0) : 0 < W.Ψ₂Sq.natDegree :=
  W.natDegree_Ψ₂Sq h ▸ three_pos
```

Qualified name (verified from source): **`WeierstrassCurve.natDegree_Ψ₂Sq_pos`**.

`Ψ₂Sq` is the univariate polynomial congruent to `ψ₂²` (the square of the
2-division polynomial of the Weierstrass curve `W`), defined in the project's
`DivisionPolynomial.lean:40` as

```lean
noncomputable def Ψ₂Sq : R[X] := C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆
```

Mathematically the lemma says: over a commutative ring `R` in which `4 ≠ 0`,
`Ψ₂Sq` has positive natural degree (it is in fact degree 3, since its leading
coefficient `4` is nonzero). This is the degree-positivity fact used downstream
to show `Ψ₂Sq ≠ 0` (`Ψ₂Sq_ne_zero`), feeding the division-polynomial machinery
for the Nagell–Lutz theorem.

## 2. Project context

The file's own module docstring (`DivisionPolynomialDegree.lean:14`) states it is
"a project copy of mathlib's Basic file." The NagellLutz project forks
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` and
`Mathlib.NumberTheory.EllipticDivisibilitySequence` to develop a PID/torsion
track. This declaration sits squarely inside that fork.

## 3. Mathlib search (five methods)

The decisive method here is **direct source-file inspection of the target
namespace** — and it is dispositive, so the other index-based methods are
redundant.

Mathlib pin in this checkout: `09b373db6e24` (toolchain `v4.32.0-rc1`), at
`.lake/packages/mathlib/`.

`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`,
lines 81–82:

```lean
lemma natDegree_Ψ₂Sq_pos (h : (4 : R) ≠ 0) : 0 < W.Ψ₂Sq.natDegree :=
  W.natDegree_Ψ₂Sq h ▸ three_pos
```

This is **byte-for-byte identical** to the project declaration:
- same namespace `WeierstrassCurve`;
- same section `variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)`;
- same hypothesis `(h : (4 : R) ≠ 0)`;
- same statement `0 < W.Ψ₂Sq.natDegree`;
- same proof term `W.natDegree_Ψ₂Sq h ▸ three_pos`.

The underlying `Ψ₂Sq` definition also matches mathlib's
`DivisionPolynomial/Basic.lean:117` exactly
(`C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆`), so this is the same
statement over the same object — not merely a same-named lemma over a divergent
definition. The entire surrounding block (`natDegree_Ψ₂Sq_le`, `coeff_Ψ₂Sq`,
`coeff_Ψ₂Sq_ne_zero`, `natDegree_Ψ₂Sq`, `leadingCoeff_Ψ₂Sq`, `Ψ₂Sq_ne_zero`) is
duplicated verbatim as well.

Authorship corroborates this: both the mathlib file and the project file carry
the header "Copyright (c) 2024 David Kurniadi Angdinata … Authors: David
Kurniadi Angdinata" — the project file is a direct copy of his upstream mathlib
contribution.

(Index searches via loogle/leansearch were not needed: the literal declaration is
present in the pinned mathlib source under its exact qualified name. No
literature search is warranted for a degree-positivity micro-lemma whose
upstream home is already established.)

## 4. Generality / composition analysis

Not applicable to the verdict: when mathlib already contains the *literal,
character-identical* declaration under the *same qualified name*, no
generalisation or composition argument can move the bucket. (For completeness:
the mathlib version is already at the natural generality — `CommRing R` with the
sharp hypothesis `4 ≠ 0` — and is itself a one-liner built from the neighbouring
`natDegree_Ψ₂Sq`.)

## 5. Conclusion

`WeierstrassCurve.natDegree_Ψ₂Sq_pos` is **already in mathlib**, identically, at
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` (lines
81–82). The project copy is a verbatim fork.

**Bucket: NO-mathlib-has-it.**

Recommended action for the consolidation: this is duplicated mathlib content. It
should not be re-contributed. When the NagellLutz project is consolidated, the
forked `DivisionPolynomial.lean` / `DivisionPolynomialDegree.lean` blocks that
exist verbatim upstream should be deleted in favour of importing
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` directly
(retaining only the genuinely new project-specific material, e.g. the
`DivisionPolynomialOmega` additions).

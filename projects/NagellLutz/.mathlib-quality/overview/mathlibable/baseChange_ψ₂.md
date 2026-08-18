# Mathlibable assessment — `WeierstrassCurve.baseChange_ψ₂`

**Verdict: NO-mathlib-has-it**

## Declaration under assessment

- **Qualified name:** `WeierstrassCurve.baseChange_ψ₂`
- **Location:** `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:476`
  (the prompt cited line 483, which is actually `baseChange_Ψ₃`; the `baseChange_ψ₂`
  lemma is at line 476.)
- **Namespace / section:** `WeierstrassCurve` → `section BaseChange`

```lean
variable [Algebra R S] {A : Type u} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
  {B : Type v} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B] (f : A →ₐ[S] B)

lemma baseChange_ψ₂ : (W.baseChange B).ψ₂ = (W.baseChange A).ψ₂.map (mapRingHom f) := by
  rw [← map_ψ₂, map_baseChange]
```

**Meaning.** For a Weierstrass curve `W` over `R`, with an `R`-algebra tower `R → S → A → B`
and an `S`-algebra hom `f : A →ₐ[S] B`, the `2`-division polynomial `ψ₂` of the base change
of `W` to `B` equals the coefficient-wise image under `f` (via `Polynomial.mapRingHom` on the
bivariate ring `R[X][Y]`) of the `ψ₂` of the base change to `A`. It is the naturality of `ψ₂`
under base change, an immediate corollary of `map_ψ₂` (naturality of `ψ₂` under ring-map
push-forward) composed with `map_baseChange` (compatibility of `map` and `baseChange`).

## Why this is a fork, not new math

The file's own module docstring states it outright:

> This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`
> that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version,
> to avoid name conflicts (both define `normEDS`, `complEDS`, etc.).
> See the original file for full documentation.

So the NagellLutz `DivisionPolynomial.lean` is a deliberate verbatim fork of the mathlib file,
duplicated only so it can sit on a forked `EllipticDivisibilitySequence` (to dodge `normEDS` /
`complEDS` name clashes). Nothing in this section is original to the project.

## Mathlib search (method: read the forked source directly)

The decisive search is reading the very file this is copied from. In the repo's pinned mathlib
(`.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`),
the `section BaseChange` block is character-for-character the same, including the lemma:

```lean
-- mathlib Basic.lean:553
lemma baseChange_ψ₂ : (W⁄B).ψ₂ = (W⁄A).ψ₂.map (mapRingHom f) := by
  rw [← map_ψ₂, map_baseChange]
```

Here `W⁄B` is mathlib's notation for `W.baseChange B`, so the statement is **identical** to the
project's (the fork merely spells the notation out). Same:

- **name** — `WeierstrassCurve.baseChange_ψ₂`
- **variable block** — the `R → S → A → B` tower with `f : A →ₐ[S] B` (mathlib line 550–551,
  project line 473–474, identical)
- **statement** — `(W.baseChange B).ψ₂ = (W.baseChange A).ψ₂.map (mapRingHom f)`
- **proof** — `rw [← map_ψ₂, map_baseChange]`

The entire surrounding family matches one-to-one as well (`baseChange_Ψ₂Sq`, `baseChange_Ψ₃`,
`baseChange_preΨ₄`, `baseChange_preΨ'`, `baseChange_preΨ`, `baseChange_ΨSq`, `baseChange_Ψ`,
`baseChange_Φ`, `baseChange_ψ`, `baseChange_φ`), confirming this is a wholesale copy of mathlib's
`section BaseChange`, not an independent rediscovery.

Mathlib's five search methods all collapse to the same answer here: exact-name lookup
(`WeierstrassCurve.baseChange_ψ₂`) hits in mathlib's own `DivisionPolynomial/Basic.lean`.

## Literature / generality / composition

Not load-bearing for the verdict, but for completeness:

- **Literature.** Division polynomials and their base-change naturality are standard (Silverman,
  *The Arithmetic of Elliptic Curves*, Exercise 3.7; the EDS framing follows Ward). This is
  bookkeeping naturality, not a named theorem.
- **Generality.** The statement is already at mathlib's chosen generality (arbitrary commutative
  `R`-algebra tower, `S`-algebra hom). No weakening is on the table — and irrelevant, since the
  identical lemma is upstream.
- **Composition.** It is literally a two-rewrite composition of `map_ψ₂` and `map_baseChange`
  (both already in mathlib). But it does not even need recomposing: the assembled lemma is
  already a named declaration in mathlib.

## Conclusion

`WeierstrassCurve.baseChange_ψ₂` is a verbatim duplicate of an existing mathlib lemma of the same
name, brought in only as part of a fork that swaps an import. It must not be re-added to mathlib.

When the NagellLutz fork is eventually reconciled, this whole copied `DivisionPolynomial.lean`
(and its `baseChange_*` family) should be dropped in favour of mathlib's
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`; the only reason for the fork
is the local `EllipticDivisibilitySequence` redefinition, which is the thing to deduplicate
upstream-ward, not these consequences of it.

**Bucket: NO-mathlib-has-it.**

# Mathlibable assessment — `WeierstrassCurve.map_preΨ₄`

**Verdict: NO-mathlib-has-it** — verbatim duplicate of an existing mathlib lemma.

## Declaration under review

- **Project**: NagellLutz (Nagell–Lutz theorem; elliptic curves; division polynomials; EDS).
- **File**: `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:433`
- **Qualified name**: `WeierstrassCurve.map_preΨ₄` (namespace `WeierstrassCurve`, opened at line 27).
- **Statement** (with `variable {R S} [CommRing R] [CommRing S] (W : WeierstrassCurve R)` and `(f : R →+* S)`):

```lean
@[simp]
lemma map_preΨ₄ : (W.map f).preΨ₄ = W.preΨ₄.map f := by
  simp [preΨ₄]
```

It asserts that the auxiliary univariate division polynomial `preΨ₄` (where
`preΨ₄ = 2·X⁶ + b₂·X⁵ + 5·b₄·X⁴ + 10·b₆·X³ + 10·b₈·X² + (b₂·b₈ − b₄·b₆)·X + (b₄·b₈ − b₆²)`,
the cofactor `ψ₄ / ψ₂` of the 4-division polynomial) commutes with the coefficient-wise pushforward
of a Weierstrass curve along a ring homomorphism `f : R →+* S`. A naturality/`map`-compatibility lemma.

## Provenance — this file is an explicit mathlib fork

The file header (lines 1–17) is unambiguous:

> Copyright (c) 2024 David Kurniadi Angdinata. … Authors: David Kurniadi Angdinata
> "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that
> imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid
> name conflicts (both define `normEDS`, `complEDS`, etc.)."

The fork exists **only** to swap one import (the local EDS file) so `normEDS`/`complEDS` do not clash;
it is not new mathematics. The author of this file is the same person who authored the mathlib original.

## Mathlib search (the file is present in the pinned toolchain)

Mathlib pin: `rev = 09b373db6e24` (toolchain v4.32.0-rc1), vendored at
`.lake/packages/mathlib/`. Searched the live source directly (no index needed — exact text match found).

`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:509–511`:

```lean
@[simp]
lemma map_preΨ₄ : (W.map f).preΨ₄ = W.preΨ₄.map f := by
  simp [preΨ₄]
```

**Byte-for-byte identical** to the project copy. Surrounding context matches exactly:

| Element | Mathlib `Basic.lean` | Project `DivisionPolynomial.lean` |
|---|---|---|
| Namespace | `WeierstrassCurve` (L104) | `WeierstrassCurve` (L27) |
| Section vars | `{R S} [CommRing R] [CommRing S] (W)` (L106) | same (L29) |
| Local hyp | `variable (f : R →+* S)` (L495) | same (L418) |
| `preΨ₄` def | `2·X⁶ + … + C (b₄·b₈ − b₆²)` (L147) | identical (L70) |
| Lemma + attr + proof | L509–511 | L433–434 (identical) |

Search methods applied:
1. Direct `grep` of the pinned mathlib tree → hit at `…/DivisionPolynomial/Basic.lean:510` (qualified
   name `WeierstrassCurve.map_preΨ₄`). Also referenced internally by `baseChange_preΨ₄` (L563), exactly
   as in the project copy (L486).
2. Repo-wide `grep -r "map_preΨ₄" Mathlib/` → the definition + its one downstream use; no rename, no
   deprecation alias. The decl is live in mathlib under this exact name.

The fork's sibling `map_*` lemmas (`map_ψ₂`, `map_Ψ₂Sq`, `map_Ψ₃`, `map_preΨ'`, `map_preΨ`, `map_Ψ`,
`map_Φ`, `map_ψ`, `map_φ`) are likewise verbatim copies of the same mathlib section — confirming a
wholesale file copy, not an independent reinvention.

## Generality / composition analysis

Not applicable. Both the lemma **and** the `preΨ₄` definition it is stated about are already in mathlib
in identical form, over the same `CommRing → CommRing` generality. There is no weaker hypothesis to
target and nothing to compose: mathlib already exposes this exact `@[simp]` lemma. Re-adding it would
be a duplicate.

## Literature note (for completeness)

`preΨ₄ = ψ₄/ψ₂` is a standard object in the theory of elliptic division polynomials (e.g.
Silverman, *The Arithmetic of Elliptic Curves*, Exercise 3.7; division polynomials `ψₙ` and their
recursion). Compatibility of division polynomials with base change / ring maps is folklore naturality.
No external citation is decisive here: the mathlib hit alone settles the verdict.

## Conclusion

`WeierstrassCurve.map_preΨ₄` is a copied-from-mathlib lemma that already lives in
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`, verbatim, same namespace, same
signature, same proof. **Bucket: NO-mathlib-has-it.** Consolidation action: this and its sibling fork
`map_*`/`baseChange_*`/`Ψ`/`Φ` lemmas should be dropped in favour of the mathlib originals once the
local-`EDS`-import naming clash that motivated the fork is resolved (the project forked the whole file
solely to redirect one import).

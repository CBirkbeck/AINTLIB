# Mathlibable assessment — `WeierstrassCurve.natDegree_preΨ₄_le`

**Verdict: NO-mathlib-has-it**
**Qualified name:** `WeierstrassCurve.natDegree_preΨ₄_le`

## Statement (project source)

`/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:121`

```lean
namespace WeierstrassCurve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

lemma natDegree_preΨ₄_le : W.preΨ₄.natDegree ≤ 6 := by
  rw [preΨ₄]
  compute_degree
```

Here `preΨ₄` is the auxiliary univariate polynomial for the 4-division polynomial of a Weierstrass
curve `W` over a commutative ring `R`:

```lean
noncomputable def preΨ₄ : R[X] :=
  2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 + 10 * C W.b₆ * X ^ 3 + 10 * C W.b₈ * X ^ 2 +
    C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X + C (W.b₄ * W.b₈ - W.b₆ ^ 2)
```

The lemma states the (purely formal, no nonzero-characteristic hypothesis) degree bound
`natDegree (preΨ₄) ≤ 6`.

## Why this is a known-fork case

The project explicitly forks two mathlib files to avoid `normEDS`/`complEDS` name clashes with its
own copy of `Mathlib.NumberTheory.EllipticDivisibilitySequence`:

- `LutzNagell/DivisionPolynomial.lean` header (lines 12–14): *"This is a copy of
  `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports
  `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts
  (both define `normEDS`, `complEDS`, etc.)."*
- `LutzNagell/DivisionPolynomialDegree.lean` header (lines 12–14): *"This file computes the leading
  terms of certain polynomials … defined in `LutzNagell/DivisionPolynomial.lean` (a project copy of
  mathlib's Basic file)."*

`DivisionPolynomialDegree.lean` is therefore a project copy of
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`.

## Mathlib search — it is already there (verbatim)

Mathlib file (pinned rev `09b373db6e24`):
`.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:125`

```lean
namespace WeierstrassCurve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section preΨ₄

lemma natDegree_preΨ₄_le : W.preΨ₄.natDegree ≤ 6 := by
  rw [preΨ₄]
  compute_degree
```

Comparison:

| | Project | Mathlib |
|---|---|---|
| Qualified name | `WeierstrassCurve.natDegree_preΨ₄_le` | `WeierstrassCurve.natDegree_preΨ₄_le` |
| Namespace / variables | `WeierstrassCurve`, `{R} [CommRing R] (W : WeierstrassCurve R)` | identical |
| Statement | `W.preΨ₄.natDegree ≤ 6` | identical |
| Proof | `rw [preΨ₄]; compute_degree` | identical (byte-for-byte) |
| `preΨ₄` def | `Basic`-copy line 70 | `Basic.lean:147` (same def) |

This is a **byte-identical** declaration — same name, same signature, same proof — living in the very
mathlib file that the project copied. The surrounding siblings (`coeff_preΨ₄`, `coeff_preΨ₄_ne_zero`,
`natDegree_preΨ₄`, `natDegree_preΨ₄_pos`, `leadingCoeff_preΨ₄`, `preΨ₄_ne_zero`, and likewise for
`Ψ₂Sq`, `Ψ₃`, `preΨ'`, `preΨ`, `ΨSq`, `Φ`) are all present and identical in mathlib's `Degree.lean`,
confirming a wholesale fork rather than coincidence.

Mathlib's five-method search is moot here: an exact-name + exact-statement match in the upstream file
is the strongest possible "mathlib has it" evidence, so `exact?`/`leansearch`/`loogle`/`rw?`/`simp?`
would each trivially close on `WeierstrassCurve.natDegree_preΨ₄_le` itself.

## Generality / composition (not needed, recorded for completeness)

- The lemma is already at full generality: any `CommRing R`, no domain or characteristic hypothesis
  (the bound `≤ 6` is the unconditional degree bound; the *exact* degree `= 6` is the separate
  `natDegree_preΨ₄` under `(2 : R) ≠ 0`). There is nothing to weaken.
- It is the base case feeding `natDegree_preΨ'_le` / `natDegree_preΨ_le` (the general division-
  polynomial degree bounds, mathlib `Degree.lean:233`/`272`), so it is not "just a one-liner to
  inline" — but that role is *already* served by the mathlib copy.
- Literature: the degree pattern `deg preΨₙ = (n² − {4,1})/2` is standard (Silverman, *The Arithmetic
  of Elliptic Curves*, division-polynomial recursion; this is the `n = 4` instance, `preΨ₄`). The
  project's own module docstring cites `[silverman2009]`. No literature gap.

## Action

Do not add to mathlib. In AINTLIB, this fork exists only to dodge the `normEDS`/`complEDS` name
collision between the project's `EllipticDivisibilitySequence` copy and mathlib's. If/when that
collision is resolved (e.g. the project drops its EDS copy or namespaces it), `DivisionPolynomial.lean`
and `DivisionPolynomialDegree.lean` should be deleted in favour of importing
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` directly. That is a
de-duplication/cleanup task on the consolidation side, not a mathlib contribution.

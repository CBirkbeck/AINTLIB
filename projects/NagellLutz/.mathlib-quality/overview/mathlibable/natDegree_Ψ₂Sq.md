# Mathlibable assessment — `WeierstrassCurve.natDegree_Ψ₂Sq`

**Verdict: NO-mathlib-has-it**

**Qualified name:** `WeierstrassCurve.natDegree_Ψ₂Sq`

---

## 1. The declaration under assessment

Source: `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:74`

```lean
namespace WeierstrassCurve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

@[simp]
lemma natDegree_Ψ₂Sq (h : (4 : R) ≠ 0) : W.Ψ₂Sq.natDegree = 3 :=
  natDegree_eq_of_le_of_coeff_ne_zero W.natDegree_Ψ₂Sq_le <| W.coeff_Ψ₂Sq_ne_zero h
```

where `Ψ₂Sq := C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆` (the univariate
polynomial congruent to `ψ₂²`, i.e. `W.twoTorsionPolynomial.toPoly`).

Mathematical content: the `natDegree` of the `2`-torsion polynomial square `Ψ₂Sq` equals `3`,
under the hypothesis that the leading coefficient `4` is nonzero in `R`.

## 2. Provenance — this file is a verbatim fork of mathlib

The project's own module docstring says so explicitly:

> "This file computes the leading terms of certain polynomials associated to division polynomials
> of Weierstrass curves defined in `LutzNagell/DivisionPolynomial.lean` (a project copy of mathlib's
> Basic file)."

`DivisionPolynomialDegree.lean` is a copy of mathlib's
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`, and
`LutzNagell/DivisionPolynomial.lean` is a copy of that directory's `Basic.lean`. Both originate from
the same author (David Kurniadi Angdinata) and carry the identical Apache-2.0 header and references
(`silverman2009`).

## 3. Mathlib search — exact match found

Mathlib pin for this project (`aintlib-main/lakefile.toml`): mathlib rev `09b373db6e24`
(toolchain `v4.32.0-rc1`). I read mathlib's source at that exact pin via a sibling worktree
(`aintlib-decompose`, same `inputRev 09b373db6e24`).

Mathlib file:
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:78`

```lean
namespace WeierstrassCurve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

@[simp]
lemma natDegree_Ψ₂Sq (h : (4 : R) ≠ 0) : W.Ψ₂Sq.natDegree = 3 :=
  natDegree_eq_of_le_of_coeff_ne_zero W.natDegree_Ψ₂Sq_le <| W.coeff_Ψ₂Sq_ne_zero h
```

A byte-level `diff` of the project declaration (lines 73–75) against the mathlib declaration
(lines 77–79) is **empty** — name, signature, `@[simp]` attribute, and proof term are all
**byte-identical**. The surrounding helpers (`natDegree_Ψ₂Sq_le`, `coeff_Ψ₂Sq`,
`coeff_Ψ₂Sq_ne_zero`, `natDegree_Ψ₂Sq_pos`, `leadingCoeff_Ψ₂Sq`, `Ψ₂Sq_ne_zero`) are likewise
present verbatim in the same `section Ψ₂Sq` of mathlib's `Degree.lean`.

Provenance of the mathlib file confirmed upstream: `git log` on
`mathlib/.../DivisionPolynomial/Degree.lean` shows only standard upstream commits
(`chore: bump toolchain …`, `feat(Tactic): …`) — no local AINTLIB modification. It is genuine
upstream mathlib, not a locally-patched copy.

## 4. Independent confirmation (literature / index)

The public mathlib4 docs corroborate the exact statement:

- `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` —
  `WeierstrassCurve.natDegree_Ψ₂Sq`: for a Weierstrass curve `W` over a commutative ring `R`, if
  `4 ≠ 0` then `W.Ψ₂Sq.natDegree = 3`. Companion lemmas `natDegree_Ψ₂Sq_le` (`≤ 3`) and
  `leadingCoeff_Ψ₂Sq` (`= 4`) are documented in the same module.
  <https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.html>

The underlying mathematics (the degree of the `2`-division polynomial / `b`-invariant cubic
`4x³ + b₂x² + 2b₄x + b₆`) is standard elliptic-curve theory — Silverman, *The Arithmetic of Elliptic
Curves*, Ch. III (division polynomials); cf. the cited `silverman2009`. There is nothing novel here
beyond mathlib's existing formalisation.

## 5. Generality / composition checks (for completeness)

Not material to the verdict — the result is in mathlib at the **same generality** (any `CommRing R`,
hypothesis `(4 : R) ≠ 0`), so there is no stronger form to target and no need to compose primitives.
The two-line proof itself already *is* a composition of mathlib primitives
(`natDegree_eq_of_le_of_coeff_ne_zero` applied to the local `…_le` and `coeff…_ne_zero` lemmas),
but since the whole package already ships in mathlib, the operative bucket is **NO-mathlib-has-it**,
not NO-composable-from-mathlib.

## 6. Verdict

**NO-mathlib-has-it.** `WeierstrassCurve.natDegree_Ψ₂Sq` exists in upstream mathlib
(`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`) **byte-for-byte identical** —
same name, namespace, statement, `@[simp]` attribute, and proof — at the exact revision
(`09b373db6e24`) this project pins. This is a forked copy, by the original mathlib author, of a file
that is already in mathlib. No upstreaming action; if anything the project copy is a candidate for
deletion-in-favour-of-mathlib during consolidation.

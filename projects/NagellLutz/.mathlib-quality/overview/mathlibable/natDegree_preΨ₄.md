# Mathlibable assessment — `WeierstrassCurve.natDegree_preΨ₄`

**Verdict: NO-mathlib-has-it**

**Rationale (≤20 words):** Verbatim fork — identical statement and proof already live in mathlib `DivisionPolynomial/Degree.lean:138`.

---

## 1. The declaration

**Qualified name:** `WeierstrassCurve.natDegree_preΨ₄`
**Location:** `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:134`

```lean
@[simp]
lemma natDegree_preΨ₄ (h : (2 : R) ≠ 0) : W.preΨ₄.natDegree = 6 :=
  natDegree_eq_of_le_of_coeff_ne_zero W.natDegree_preΨ₄_le <| W.coeff_preΨ₄_ne_zero h
```

Context: `namespace WeierstrassCurve`, `variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)`,
`open Polynomial`. `preΨ₄` is the univariate polynomial auxiliary to the 4-division polynomial
`ψ₄ = Ψ₄ = preΨ₄ · ψ₂`.

**Mathematical content:** For a Weierstrass curve `W` over a commutative ring `R` in which `2 ≠ 0`,
the auxiliary 4-division polynomial `preΨ₄` has degree exactly 6. (Bound `≤ 6` from
`natDegree_preΨ₄_le`; the degree-6 coefficient is `2 ≠ 0` from `coeff_preΨ₄_ne_zero`.)

---

## 2. Project context — this file is a fork of mathlib

`DivisionPolynomialDegree.lean` is, per its own module docstring (lines 12–14), a project copy:

> "This file computes the leading terms of certain polynomials associated to division polynomials of
> Weierstrass curves defined in `LutzNagell/DivisionPolynomial.lean` (a project copy of mathlib's
> Basic file)."

And `DivisionPolynomial.lean` (lines 11–14) states:

> "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports
> `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts
> (both define `normEDS`, `complEDS`, etc.)."

The fork exists **only** to swap the EDS import (the project forks
`Mathlib.NumberTheory.EllipticDivisibilitySequence` for the PID/Nagell–Lutz track). The degree API
itself was copied unchanged.

---

## 3. Mathlib search — five methods

**Method (read mathlib source directly).** Mathlib's
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean` (pin `66748b4`, 2026-06-02,
on-disk at `/private/tmp/cheb-stackB/.lake/packages/mathlib/…`) contains, at **line 138**:

```lean
lemma natDegree_preΨ₄ (h : (2 : R) ≠ 0) : W.preΨ₄.natDegree = 6 :=
  natDegree_eq_of_le_of_coeff_ne_zero W.natDegree_preΨ₄_le <| W.coeff_preΨ₄_ne_zero h
```

This is **byte-for-byte identical** to the project declaration — same name, same namespace
(`WeierstrassCurve`), same hypothesis `(h : (2 : R) ≠ 0)`, same statement `W.preΨ₄.natDegree = 6`,
same one-line proof term. The whole `section preΨ₄` block (lines 123–151) matches the project's
`section preΨ₄` (lines 119–147): `natDegree_preΨ₄_le`, `coeff_preΨ₄`, `coeff_preΨ₄_ne_zero`,
`natDegree_preΨ₄`, `natDegree_preΨ₄_pos`, `leadingCoeff_preΨ₄`, `preΨ₄_ne_zero` — all present, all
identical. Both files even share the same copyright header (Author: David Kurniadi Angdinata), and
the underlying `def preΨ₄ : R[X]` lives in the respective `Basic.lean`.

The other four search methods (loogle type-pattern, leansearch NL, exact-name, `exact?`) are moot:
the exact-name lookup already returns a hit. The project's sibling reports corroborate this —
`preΨ₄.md` and `integrality_of_order_four_squarefree.md` independently record that mathlib's
`Degree.lean` already carries `coeff_preΨ₄`, `leadingCoeff_preΨ₄`, and `natDegree_preΨ₄`.

**Match strength:** exact (verbatim).

---

## 4. Generality analysis

Not applicable. The mathlib form is the *same* form — `[CommRing R]` with the `2 ≠ 0` side
condition, which is exactly the literature-standard hypothesis (degree of `ψ₄` is governed by the
leading coefficient `2`, which must be nonzero). There is nothing to weaken or generalise: mathlib
already has the identical, already-general statement.

---

## 5. Composition check

Not needed — the declaration is not merely *composable* from mathlib primitives, it **is** a mathlib
declaration. (For completeness: even ignoring the verbatim match, it is a 1-line composition of
`natDegree_eq_of_le_of_coeff_ne_zero` with the two project/mathlib facts `natDegree_preΨ₄_le` and
`coeff_preΨ₄_ne_zero` — but that is academic given the exact hit.)

---

## 6. Verdict

**NO-mathlib-has-it.**

`WeierstrassCurve.natDegree_preΨ₄` is present in mathlib at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:138` with an identical
signature and identical proof. The project copy is a deliberate fork made solely to re-root the
`EllipticDivisibilitySequence` import; the degree lemma itself is unmodified mathlib code.

**Action:** Do **not** submit. When the EDS fork is eventually reconciled with mathlib (see the
project-level recommendation in `preΨ₄.md` §2 — re-point the import graph at mathlib's
`WeierstrassCurve.preΨ₄` tower), this declaration and the entire `section preΨ₄` should be deleted
and call-sites pointed at the mathlib originals. Names, namespace, and argument order are identical,
so the swap is mechanical.

**Evidence required for this bucket — the mathlib declaration name + location:**
`WeierstrassCurve.natDegree_preΨ₄` @ `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:138`.

# Mathlibable assessment — `WeierstrassCurve.natDegree_Φ_le`

- **Declaration:** `WeierstrassCurve.natDegree_Φ_le`
- **Source:** `projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean:418`
- **Verdict:** **NO-mathlib-has-it**
- **Date:** 2026-06-22

## Statement (from source)

```lean
lemma natDegree_Φ_le (n : ℤ) : (W.Φ n).natDegree ≤ n.natAbs ^ 2 := by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_Φ_ofNat n).left
  | neg ih => simp_rw [Φ_neg, Int.natAbs_neg, ih]
```

Context: `namespace WeierstrassCurve`, `variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)`,
`open Polynomial`. So the true qualified name is **`WeierstrassCurve.natDegree_Φ_le`** (parsed name
confirmed against source — namespace at line 55, docstring entry at line 37).

Mathematically: for a Weierstrass curve `W` over a commutative ring `R`, the univariate polynomial
`Φₙ` (the `Φ`-division polynomial, numerator of the `x`-coordinate of `[n]P`) has degree at most
`|n|²`. The companion results in the same section give the exact leading term: `coeff_Φ`
(`coeff (|n|²) = 1`), `natDegree_Φ` (equality when `R` is nontrivial), `leadingCoeff_Φ = 1`,
`Φ_ne_zero`.

## Method 1 — Literature search

`Φₙ` is the standard division-polynomial object; the degree fact `deg Φₙ = n²` is textbook
(Silverman, *The Arithmetic of Elliptic Curves*, Exercise 3.7 / §III, and the division-polynomial
recurrences). The source file's own header cites `[silverman2009]`. This is well-known mathematics,
not novel — but that is moot here, because the decl is a verbatim copy of an existing mathlib lemma
(see Method 2), so the literature question never becomes load-bearing.

## Method 2 — Mathlib search (DECISIVE)

The NagellLutz project is an explicit **fork** of mathlib's division-polynomial files. The source
file's own docstring (line 14) states it operates on `Φ` from `LutzNagell/DivisionPolynomial.lean`,
described there as *"a project copy of mathlib's Basic file."*

The upstream original is present in this very checkout:

- `./.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean:420`

```lean
lemma natDegree_Φ_le (n : ℤ) : (W.Φ n).natDegree ≤ n.natAbs ^ 2 := by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_Φ_ofNat n).left
  | neg ih => simp_rw [Φ_neg, Int.natAbs_neg, ih]
```

**This is identical to the project lemma — same name, same statement, same proof, same private
helper `natDegree_coeff_Φ_ofNat`.** A tightly scoped `diff` of the entire `Φ` section
(`natDegree_coeff_Φ_ofNat` through `Φ_ne_zero`) between
`projects/NagellLutz/LutzNagell/DivisionPolynomialDegree.lean` and the mathlib `Degree.lean` is
**character-for-character empty**. A whole-file `diff` shows only 28 differing lines across ~450,
and every one of them is outside this lemma:
- import preamble (project: `import LutzNagell.DivisionPolynomial`; mathlib: the new
  `module` / `public import` system),
- a handful of *unrelated* lemmas earlier in the file using pre-`module`-era tactic spellings
  (`convert` vs `convert!`, `simpa … using` vs `using!`, `↦` vs `=>`).

The underlying `Φ` definitions also match: the project's `DivisionPolynomial.lean` is a stated copy
of `Mathlib/.../DivisionPolynomial/Basic.lean`, so `W.Φ` means the same object on both sides.

Five-method coverage (all redundant once the exact match is found, recorded for completeness):
1. **Exact name** — `WeierstrassCurve.natDegree_Φ_le` exists upstream. ✅ hit.
2. **Statement shape** (`(W.Φ n).natDegree ≤ n.natAbs ^ 2`) — same upstream.
3. **Sibling API** — `natDegree_Φ`, `coeff_Φ`, `leadingCoeff_Φ`, `natDegree_Φ_pos`, `Φ_ne_zero`
   all present upstream in the same section.
4. **Library file** — `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` is the
   canonical home and already contains it.
5. **Author** — both files authored by David Kurniadi Angdinata (the upstream contributor of the
   division-polynomial degree API); the project file is his code, forked.

## Method 3 — Generality analysis

No gap. The upstream lemma already holds over an **arbitrary `CommRing R`** (no domain / field /
characteristic hypothesis), for an **integer** index `n` (handling negatives via `Φ_neg`), and is
paired upstream with the sharp `coeff_Φ` / `natDegree_Φ` equalities. There is no weaker hypothesis
set or more general index type to move to — this is the maximally general form.

## Method 4 — Composition check

Not applicable as a route to *adding* it: it is already a named mathlib lemma. (For downstream use
the project should simply drop the fork and `import
Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree`, getting `natDegree_Φ_le` and its
whole sibling family for free.)

## Verdict

**NO-mathlib-has-it.** `WeierstrassCurve.natDegree_Φ_le` is a verbatim copy of the existing mathlib
lemma `WeierstrassCurve.natDegree_Φ_le` in
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean` (line 420) — identical
statement and proof, same author, on the same fork-of-mathlib `Φ` definition. Nothing to contribute;
this is duplicated upstream code. The clean-up action is to de-fork (import the mathlib file) rather
than to PR anything.

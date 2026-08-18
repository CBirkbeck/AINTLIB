# Mathlibable assessment — `WeierstrassCurve.Universal.Affine.smulX_one`

- **Declaration (verified qualified name):** `WeierstrassCurve.Universal.Affine.smulX_one`
- **Location:** `projects/NagellLutz/LutzNagell/ZSMul.lean:173`
- **Fork copy:** identical decl at `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:248`
- **Verdict:** `YES-add-as-is` (gated — see "Gating" below)
- **Date:** 2026-06-22

## Statement & proof (from source)

```lean
namespace WeierstrassCurve
namespace Universal      -- the universal Weierstrass curve over MvPolynomial Coeff ℤ
namespace Affine

/-- The rational function φₙ/ψₙ², which we will show to be the `X`-coordinate
of the point `n • (X, Y)` on the universal curve. -/
def smulX : Universal.Field := polyToField (curve.φ n) / (ψᵤ n) ^ 2

@[simp] lemma smulX_one : smulX 1 = polyToField (C X) := by simp [smulX, ψᵤ]
```

Supporting project-local definitions:
- `curve : Affine (MvPolynomial Coeff ℤ)` — the **universal Weierstrass curve** (`Universal.lean:84`),
  `{a₁ := X A₁, …, a₆ := X A₆}`, the generic curve carrying the five indeterminate coefficients.
- `Universal.Ring := curve.CoordinateRing`; `Universal.Field := FractionRing Universal.Ring`
  (`Universal.lean:96,99`).
- `polyToField : Poly →+* Universal.Field` (`Universal.lean:108`) — project-local ring hom
  `(algebraMap Universal.Ring _).comp (AdjoinRoot.mk _)`.
- `ψᵤ (n : ℤ) : Universal.Field := polyToField (curve.ψ n)` (`ZSMul.lean:132`).

So `smulX 1 = polyToField (curve.φ 1) / (ψᵤ 1)^2`. The proof `simp [smulX, ψᵤ]` discharges it via
mathlib's own simp lemmas: `φ_one : W.φ 1 = C X`, `ψ_one : W.ψ 1 = 1` (hence `ψᵤ 1 = 1`), giving
`polyToField (C X) / 1^2 = polyToField (C X)`.

**Mathematical content.** This is the **n = 1 base case** of the multiplication-by-n formula
`n • (X, Y) = (φₙ/ψₙ², ωₙ/ψₙ³)` for the universal curve: `1 • P = P`, whose `X`-coordinate is `X`.

## 1. Literature search

The multiplication-by-n formula via division polynomials is classical (Silverman, *Arithmetic of
Elliptic Curves*, Exercise 3.7; standard in every treatment of division polynomials). The
`X`-coordinate of `nP` is `φₙ(x)/ψₙ(x)²` with `φₙ = x·ψₙ² − ψₙ₊₁ψₙ₋₁`. The **n = 1 base case** is the
universal sanity check: `ψ₁ = 1`, `ψ₀ = 0`, so `φ₁ = x·1 − ψ₀ψ₂ = x`, i.e. `1·P = P`. WebSearch
(arXiv 1710.05264, 2102.07573, 1108.3051, et al.) confirms exactly this normalization and base case.

There is no separate "literature theorem" named for `smulX_one` — it is the trivial initial value of a
classical recursion. Its mathlib-worthiness rides entirely on the surrounding development (the
multiplication-by-n coordinate formula), not on the one-line base case in isolation.

## 2. Mathlib search (five methods)

The project **forks** `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` and
`Mathlib.NumberTheory.EllipticDivisibilitySequence`. Checked the mathlib copies directly.

- **By name / grep `smulX`, `smulY`, `smulEval`, `zsmul_eq_smulEval`:** no hits in mathlib (the only
  `smulX` grep hits are unrelated `smul`/`X` tokens in `NoncommRing.lean`, `OreLocalization`, etc.).
- **`Universal` namespace under EllipticCurve / AlgebraicGeometry:** none related — only
  `Morphisms/UniversallyOpen.lean`. Mathlib has **no universal-Weierstrass-curve framework**
  (`curve`, `Universal.Ring`, `Universal.Field`, `polyToField` are all project-local in
  `Universal.lean`).
- **Multiplication-by-n coordinate formula (`n • P = (φₙ/ψₙ², …)`):** **absent from mathlib.** Mathlib
  has the division polynomials and their values/recurrences but not the theorem connecting them to
  `n • P` in `W.Point`. That theorem (`zsmul_eq_smulEval`, `zsmul_point_eq_smulX_smulY`) is the
  headline result of this very NagellLutz file.
- **Underlying building blocks that mathlib DOES have:**
  `WeierstrassCurve.φ_one : W.φ 1 = C X` (`DivisionPolynomial/Basic.lean:458`);
  `ψ_one : W.ψ 1 = 1` (`:411`, `= normEDS_one`); `normEDS_one`, `preNormEDS_one`
  (`EllipticDivisibilitySequence.lean:302,190`). These are precisely the simp lemmas that prove
  `smulX_one`.

**Conclusion of search:** `smulX_one` is **not** in mathlib, and no more-general mathlib lemma
subsumes it, because its subject `smulX` (and the universal-field framework it lives in) does not
exist in mathlib.

## 3. Generality analysis

`smulX_one` is already at **maximal generality**: it is stated over the *universal* curve, i.e.
simultaneously over every Weierstrass curve (the indeterminate coefficients `A₁,…,A₆` specialize to
any base ring via `ringEval`/`map_*`). There is nothing to weaken — base ring, coefficients, and the
point are all generic. The only "specialization" is `n = 1`, which is the point of the lemma (it is
the base case, not a special case worth generalizing away). So **no generalisation is needed**.

## 4. Composition check (≤ 3 mathlib calls?)

Can mathlib's primitives give `smulX_one` directly? **No** — not because the *math* is hard (the
proof is `simp [smulX, ψᵤ]`, two unfoldings + `φ_one`/`ψ_one`/`normEDS_one`), but because the
**statement does not typecheck against mathlib alone**: `smulX`, `ψᵤ`, `polyToField`, `curve`,
`Universal.Field` are all project-local. The composition `polyToField (curve.φ 1) / (ψᵤ 1)^2 =
polyToField (C X)` is trivially derivable *once those definitions exist*, but they exist only in this
project. So this is "composable from mathlib's lemmas, but only on top of not-yet-upstreamed
definitions" — which is materially different from `NO-composable-from-mathlib` (where the *result*
itself is reachable from mathlib as written).

## 5. Verdict — `YES-add-as-is`

`smulX_one` is correct, at full generality, with a clean one-line proof, and is **not** present in
mathlib in any form. It is a genuine, heavily-reused piece of a development that mathlib is **missing**
(the division-polynomial multiplication-by-n coordinate formula on `WeierstrassCurve.Point`). As a
declaration it needs no change: it should be added **as-is**.

It is **not** `YES-but-generalise-first` (already maximally general — universal curve), **not**
`NO-mathlib-has-it` (mathlib lacks `smulX` and the whole framework), and **not**
`NO-composable-from-mathlib` (the statement is not even expressible in mathlib without first adding
`smulX` and the universal-field scaffold).

### Gating (why this is not a standalone PR)

`smulX_one` cannot be PR'd in isolation. Its admission is **gated** on first upstreaming its
dependency stack as a coherent contribution:
1. the universal-Weierstrass-curve framework (`Universal.curve`, `Universal.Ring`, `Universal.Field`,
   `polyToField`, `ψᵤ`) from `Universal.lean` / `ZSMul.lean`;
2. the affine multiplication-by-n rational functions `smulX`/`smulY` and the formula
   `n • (X,Y) = (φₙ/ψₙ², ωₙ/ψₙ³)` (`zsmul_point_eq_smulX_smulY`) — the actual missing-from-mathlib
   theorem this whole file proves.

Within that PR, `smulX_one` (and its siblings `smulX_zero`, `smulY_zero`, `smulY_one`,
`smulX_two`, …) go in unchanged as the `@[simp]` base-case lemmas. So: **YES, add as-is — as part of
the upstream of the division-polynomial multiplication formula, not alone.**

### Consumers (evidence of load-bearing internal use)

`smulX_one` is used 7× in `ZSMul.lean` (lines 180, 248, 265, 281, 351) and 7× in the HasseWeil fork
copy (`Auxiliary/DivisionPolynomial.lean` 255, 319, 336, 352, 423), feeding `smulX_eq`,
`addX_smul_one_smul_one`, `slopeOne_eq_neg_div`, and ultimately `zsmul_point_eq_smulX_smulY`.

## Evidence index (paths)

- Decl: `projects/NagellLutz/LutzNagell/ZSMul.lean:173`
- Defs: `projects/NagellLutz/LutzNagell/Universal.lean:84,96,99,108`;
  `projects/NagellLutz/LutzNagell/ZSMul.lean:132,164`
- Mathlib building blocks (present):
  `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:411,458`;
  `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:190,302`
- Mathlib gaps (absent): no `smulX`/`smulY`, no `Universal` curve framework, no `n • P` division-poly
  coordinate formula anywhere under `.lake/packages/mathlib/Mathlib/AlgebraicGeometry/EllipticCurve/`.

# Mathlibable assessment: `WeierstrassCurve.C_Ψ₃_eq`

**Verdict: NO-composable-from-mathlib**

- **Qualified name:** `WeierstrassCurve.C_Ψ₃_eq`
- **Location:** `projects/NagellLutz/LutzNagell/DivisionPolynomialOmega.lean:55`
- **Duplicate:** byte-identical statement + proof at
  `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:73`
- **Date:** 2026-06-18

## Statement (verified from source)

```lean
namespace WeierstrassCurve
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

lemma C_Ψ₃_eq :
    C W.Ψ₃ = (3 * C X + CC W.a₂) * C W.Ψ₂Sq - polynomialX W ^ 2
      + CC W.a₁ * W.ψ₂ * polynomialX W - CC W.a₁ ^ 2 * polynomial W := by
  simp_rw [Ψ₃, Ψ₂Sq, polynomial, polynomialX, ψ₂, polynomialY, b₂, b₄, b₆, b₈, CC]; C_simp; ring
```

Here everything lives in the bivariate ring `R[X][Y]`:
- `Ψ₃ : R[X]` is the 3-division polynomial `3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈`;
- `Ψ₂Sq : R[X]` is `4X³ + b₂X² + 2b₄X + b₆` (congruent to `ψ₂²`);
- `ψ₂ = polynomialY`, `polynomialX`, `polynomial` are the affine Weierstrass polynomial and its
  partial derivatives (mathlib `WeierstrassCurve.Affine`);
- `CC r = C (C r)` is mathlib's bivariate double-constant embedding (`Polynomial.Bivariate.CC`).

It is a pure **polynomial identity** in `R[X][Y]` over an arbitrary `CommRing R`, expressing
`C Ψ₃` through the affine curve polynomial, its X-derivative `polynomialX`, and `ψ₂`. It is glue
that feeds the `ω`-polynomial / `ψc` construction (used in `ω_spec`, and downstream in the
`ZSMul` / Nagell–Lutz development; cf. its single use sites `ZSMul.lean:266` and the HasseWeil
`pointedCurve` simp set).

## 1. Literature search

- WebSearch: the 3-division polynomial `ψ₃` is entirely standard (e.g. short-Weierstrass
  `ψ₃ = 3x⁴ + 6ax² + 12bx − a²`; general `b`-form `3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈`). Sources:
  Homogeneous division polynomials (arXiv:1303.4327), explicit valuations of division polynomials
  (arXiv:1108.3051), Holm-curve torsion (arXiv:2002.00295).
- The specific rewriting of `C ψ₃` in terms of `(3X + a₂)·Ψ₂Sq`, `polynomialX²`, `a₁·ψ₂·polynomialX`
  and `a₁²·polynomial` is **not** a named theorem in the literature. It is the kind of
  expand-and-collect bookkeeping identity one writes to connect the (univariate) division
  polynomials with the (bivariate) affine geometry. No standard name; no independent citation.

## 2. Mathlib search (five methods)

- **Forked files checked first** (per project context): this project copies
  `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` into
  `LutzNagell/DivisionPolynomial.lean`. `Ψ₃`, `Ψ₂Sq`, `ψ₂` are defined identically in both the fork
  and upstream `…/DivisionPolynomial/Basic.lean`. `polynomialX`, `polynomialY`, `polynomial`, `CC`
  are upstream mathlib (`Affine/Basic.lean`, `Algebra/Polynomial/Bivariate.lean`).
- `grep -rn "C_Ψ₃\|Ψ₃_eq\|C_Ψ3"` across **all** of `.lake/packages/mathlib/Mathlib/` → **no hits**.
- Mathlib's `DivisionPolynomial/Basic.lean` and `Degree.lean` contain `Ψ_three`, `ψ_three`,
  `Φ_three`, `C_Ψ₂Sq`, `ψ₂_sq`, … but **no** lemma rewriting `C Ψ₃` via `polynomialX`/`polynomial`.
- loogle/leansearch (mathlib index) consistent: no decl of this shape exists upstream.

**Conclusion:** the lemma is genuinely absent from mathlib, but every ingredient it mentions is
already a mathlib definition.

## 3. Generality analysis

Already maximally general for mathlib's `WeierstrassCurve` framework: arbitrary `CommRing R`, general
Weierstrass coefficients `a₁..a₆` (not short form). No hypotheses to weaken; the statement is an
unconditional ring identity. Nothing to generalise.

## 4. Composition check (the deciding gate)

The proof is a single normalisation: unfold the seven defining equations (`Ψ₃, Ψ₂Sq, polynomial,
polynomialX, ψ₂, polynomialY` plus `b₂,b₄,b₆,b₈, CC`), push `C` through (`C_simp`), then `ring`.

Anyone in mathlib who wanted this fact would obtain it in **one `ring` call** after
`simp only [unfolding lemmas]` — i.e. it is mechanically composable from existing mathlib
primitives, far inside the ≤3-call bar. It carries no reusable API: it is not a structural fact,
not a recurrence, not a degree/coefficient statement of independent interest — it is a private
bridge identity whose only purpose is to rewrite `C Ψ₃` into the exact shape needed by the
`ω`/`ψc` machinery in this project. Both AINTLIB copies use it solely inside that machinery.

## 5. Verdict

**NO-composable-from-mathlib.** It is absent from mathlib, but it is a `ring`-after-unfold polynomial
identity between definitions that ALL already exist upstream, with no standalone mathematical content
or reusable API — exactly the kind of glue mathlib expects a user to discharge inline rather than
host as a named lemma.

### Notes for the AINTLIB consolidation pass
- Cross-project **duplication** (NagellLutz ↔ HasseWeil, byte-identical) is a separate dedup concern
  for the `main` fleet — but the canonical home is a *project* `Common/` (or the local
  DivisionPolynomial fork), **not** mathlib.
- If the broader `ω`/`ψc`/`compl₂EDS` division-polynomial extension that this lemma serves is itself
  upstreamed to mathlib someday, this identity would naturally ride along as a `private`/auxiliary
  step there — still not as a standalone public lemma.

## Sources
- https://arxiv.org/pdf/1303.4327 — Homogeneous division polynomials for Weierstrass elliptic curves
- https://arxiv.org/pdf/1108.3051 — Integral points on elliptic curves and explicit valuations of division polynomials
- https://arxiv.org/pdf/2002.00295 — The group of rational points on the Holm curve is torsion-free

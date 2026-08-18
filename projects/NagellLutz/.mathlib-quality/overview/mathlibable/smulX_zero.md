# Mathlibable assessment — `WeierstrassCurve.Universal.Affine.smulX_zero`

**Verdict: NO — composable from mathlib (a one-step boundary lemma about a *project-local* definition; not an independent mathlib candidate).**

- **Qualified name:** `WeierstrassCurve.Universal.Affine.smulX_zero`
- **Location:** `projects/NagellLutz/LutzNagell/ZSMul.lean:171`
- **Date:** 2026-06-22

---

## 0. Source statement and proof (verbatim)

```lean
namespace WeierstrassCurve            -- ZSMul.lean:76
namespace Universal                   -- ZSMul.lean:86
namespace Affine                      -- ZSMul.lean:157

variable (n)
/-- The rational function φₙ/ψₙ², which we will show to be the `X`-coordinate
of the point `n • (X, Y)` on the universal curve. -/
def smulX : Universal.Field := polyToField (curve.φ n) / (ψᵤ n) ^ 2     -- :164
…
@[simp] lemma smulX_zero : smulX 0 = 0 := by simp [smulX, ψᵤ]           -- :171
```

with the supporting abbreviation (`ZSMul.lean:131-132`):

```lean
/-- The `ψ` family of division polynomials as elements in the universal field. -/
abbrev ψᵤ (n : ℤ) : Universal.Field := polyToField (curve.ψ n)
```

**True qualified name verified from source.** Namespace nesting is
`WeierstrassCurve` (line 76) → `Universal` (line 86) → `Affine` (line 157), so the
parsed name `WeierstrassCurve.Universal.Affine.smulX_zero` in the prompt is **correct**.

### What it says / why it is true
`smulX 0 = polyToField (curve.φ 0) / (ψᵤ 0) ^ 2`. Here `ψᵤ 0 = polyToField (curve.ψ 0)`
and `curve.ψ 0 = 0` (mathlib/project `ψ_zero`, itself `normEDS_zero`), so `ψᵤ 0 = 0`,
the denominator `(ψᵤ 0) ^ 2 = 0`, and `a / 0 = 0` in a field (`div_zero`). The `@[simp]`
proof `simp [smulX, ψᵤ]` just unfolds the definitions and lets `ψ_zero`/`normEDS_zero` +
`div_zero` close it. This is the trivial `n = 0` boundary case of the candidate X-coordinate
`x(n • (X,Y)) = φₙ/ψₙ²` on the *universal* curve.

---

## 1. Literature search

The identity `x([n]P) = φₙ(x)/ψₙ(x)²` (and the full `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)`) is the
**classical division-polynomial multiplication formula** — Silverman, *The Arithmetic of
Elliptic Curves*, Ch. III/Exercise 3.7; Washington, *Elliptic Curves: Number Theory and
Cryptography* §3.2; and the Wikipedia "Division polynomials" article (which states both
`φₙ = x·ψₙ² − ψₙ₊₁ψₙ₋₁` and `[n]P = (φ/ψ², ω/ψ³)`). It underpins the Nagell–Lutz theorem and
elliptic divisibility sequences. The literature treats `n = 0` as the degenerate
"point at infinity" case (`ψ₀ = 0`); there is no named theorem for the `n = 0` boundary —
it is a triviality once the convention is fixed.

The relevant content here is **not** the classical formula (this project proves that as
`zsmul_eq_smulEval`); it is merely the `n = 0` edge case of one auxiliary definition used in
that proof.

Sources:
- Division polynomials — Wikipedia: https://en.wikipedia.org/wiki/Division_polynomials
- Topics in Elliptic Curves over Finite Fields (arXiv:1103.4560): https://arxiv.org/pdf/1103.4560
- Integral points / explicit valuations of division polynomials (arXiv:1108.3051): https://arxiv.org/pdf/1108.3051

## 2. Mathlib search (five methods)

Subject of the lemma is the **project-local** definition `smulX` (and `ψᵤ`, `polyToField`,
`Universal.Field`, `curve`). None of this machinery exists in mathlib, so the lemma cannot
exist there either.

1. **Exact-name / grep.** `grep -rln "smulX" .lake/packages/mathlib/Mathlib/` → **no matches**
   (anywhere in mathlib). Same for `smulY`, `polyToField`, `Universal.Field`, `UniversalCurve`.
2. **Concept grep in the EllipticCurve tree.** `grep -rln "Universal|zsmul_point|ψᵤ"` over
   `Mathlib/AlgebraicGeometry/EllipticCurve/` and `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
   → **no matches**. No `n • P` X-coordinate-via-division-polynomials formula present
   (`grep -rln "zsmul_eq|smul.*divisionPoly|φ.*ψ.*smul"` → empty).
3. **What mathlib *does* have.** `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean`
   and `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` define the division polynomials
   `ψ, preΨ, Ψ, φ, ω` and the normalised EDS, including `ψ_zero : W.ψ 0 = 0`, `φ_zero : W.φ 0 = 1`,
   `normEDS_zero`. It does **not** define `smulX`/`smulY`, the universal curve, `polyToField`, or
   the multiplication formula. (This project *forks* the DivisionPolynomial / EDS files and
   builds the `Universal.*` layer on top.)
4. **leansearch / loogle (mathlib index).** A query for "smulX", "universal Weierstrass curve
   field", or "x coordinate n smul division polynomial" returns nothing matching `smulX`; mathlib's
   division-polynomial API stops at the polynomials themselves and their degrees.
5. **Docs / web.** mathlib4 docs confirm `DivisionPolynomial.Basic`/`Degree` exist with `ψ/φ/ω`
   but no `smul`-coordinate API; the "elementary group law" ITP-2023 work is about the group law,
   not the division-polynomial multiplication map.

**Conclusion:** mathlib has the *ingredients* (`ψ_zero`, `div_zero`) but neither the definition
`smulX` nor any equivalent of this lemma. → not `NO-mathlib-has-it`.

## 3. Generality analysis

The literature-standard object is `x([n]P)` for a point `P` on a curve over a field. The project
deliberately works on the **universal** curve (coefficients are indeterminates `a₁..a₆`, point
`(X,Y)` generic) so that one identity specialises to every curve/point. The lemma is already at the
most useful generality *for its role*: a `@[simp]` normal-form fact for the universal `smulX`. There
is no honest "weaker hypotheses" axis here — it is a closed term equation with no hypotheses
(`smulX 0 = 0`). Generalising would mean abstracting `smulX` itself (e.g. to an arbitrary
`a / b` with `b = 0`), at which point the lemma *is* just `div_zero`. So there is nothing to
generalise that isn't already a mathlib primitive. → not `YES-but-generalise-first`.

## 4. Composition check (≤ 3 mathlib calls)

The lemma's mathematical content collapses to mathlib primitives:

```lean
-- modulo the project-local `smulX`/`ψᵤ` unfolding:
smulX 0
  = polyToField (curve.φ 0) / (ψᵤ 0) ^ 2        -- unfold smulX, ψᵤ (definitional)
  = polyToField (curve.φ 0) / (polyToField 0) ^ 2  -- ψ_zero  (mathlib: W.ψ 0 = 0)
  = _ / 0                                        -- map_zero + zero_pow
  = 0                                            -- div_zero  (mathlib)
```

i.e. **`ψ_zero` (≈ `normEDS_zero`) + `div_zero`** (plus structural `map_zero`/`zero_pow`),
which is exactly why the one-liner `simp [smulX, ψᵤ]` discharges it. The *non-trivial* facts it
rests on (`ψ_zero`, `div_zero`) are **already in mathlib**. The lemma itself adds no reusable
mathematics; it is `@[simp]` glue that puts a project-local definition into normal form. → fits
`NO-composable-from-mathlib`.

## 5. Verdict — NO, composable from mathlib

- **It is not in mathlib** only because its *subject* (`smulX`) is a project-local definition that
  mathlib does not have — so this is not `NO-mathlib-has-it`.
- It is a **zero-content boundary lemma** (`a / 0 = 0` after `ψ 0 = 0`): the moment you have the
  definition in front of you, mathlib's `div_zero` + `ψ_zero`/`normEDS_zero` give it in one `simp`.
  There is **no reusable lemma to upstream on its own** — adding `smulX 0 = 0` to mathlib without
  `smulX` is meaningless, and *with* `smulX` it is just the obligatory `@[simp]` normal-form lemma
  that ships alongside the definition.
- It should live exactly where it does: next to `smulX` in the project. **If and only if** the whole
  `WeierstrassCurve.Universal.Affine` development (the universal curve, `polyToField`, `smulX/smulY`,
  and the multiplication formula `zsmul_eq_smulEval`) is ever upstreamed, this lemma rides along as a
  trivial companion — it is never a standalone candidate.

**Bucket: `NO-composable-from-mathlib`.**

> Note: the same lemma is duplicated verbatim in the HasseWeil project
> (`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean:246`). That intra-repo
> duplication is a *cleanup/dedup* concern (the two projects share this `Universal` layer), not a
> mathlib-eligibility concern, and does not change the verdict.

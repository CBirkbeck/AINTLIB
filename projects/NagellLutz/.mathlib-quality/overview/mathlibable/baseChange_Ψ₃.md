# Mathlibable assessment: `WeierstrassCurve.baseChange_Ψ₃`

**Verdict: NO-mathlib-has-it**

> The declaration is a byte-for-byte copy of an existing mathlib lemma. It exists in the
> project only as a side effect of the project's deliberate fork of mathlib's division-polynomial
> files, not because it is new mathematics.

---

## 1. The declaration under assessment

- **Qualified name:** `WeierstrassCurve.baseChange_Ψ₃`
  (namespace is the single `namespace WeierstrassCurve` opened at line 27; no nested namespace in
  the `BaseChange` section.)
- **Location:** `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:482`
  (NOTE: the dispatch prompt cited line 489 with this base name, but line 489 is actually
  `baseChange_preΨ'`; `baseChange_Ψ₃` is at **line 482**. Statement verified directly from source.)

Statement and proof (project copy):

```lean
section BaseChange
variable [Algebra R S] {A : Type u} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
  {B : Type v} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B] (f : A →ₐ[S] B)

lemma baseChange_Ψ₃ : (W.baseChange B).Ψ₃ = (W.baseChange A).Ψ₃.map f := by
  rw [← map_Ψ₃, map_baseChange]
```

Mathematical content: the univariate 3-division polynomial `Ψ₃ = 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈`
of a Weierstrass curve is natural in the base ring, i.e. it commutes with base change along an
`S`-algebra homomorphism `f : A →ₐ[S] B` (push the coefficients forward via `Polynomial.map f`).
It is a one-line corollary of the ring-hom naturality lemma `map_Ψ₃` plus the bookkeeping lemma
`map_baseChange` (which rewrites `baseChange` as `map` of the algebra-map ring hom).

## 2. Project context

The file's own header (lines 12–16) states:

> "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that
> imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid
> name conflicts (both define `normEDS`, `complEDS`, etc.)."

So `DivisionPolynomial.lean` is a verbatim fork of the mathlib module, re-pointed at the project's
local EDS file. Every lemma in it — including `baseChange_Ψ₃` — is expected to already be in mathlib.

## 3. Mathlib search (the decisive step)

The pinned mathlib (`.lake/packages/mathlib`, rev `09b373db6e24`) contains the **identical**
declaration:

- **File:** `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:559`
- **Mathlib source:**

```lean
namespace WeierstrassCurve   -- line 104
...
section BaseChange           -- line 546
variable [Algebra R S] {A : Type u} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
  {B : Type v} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B] (f : A →ₐ[S] B)

lemma baseChange_Ψ₃ : (W⁄B).Ψ₃ = (W⁄A).Ψ₃.map f := by   -- line 559
  rw [← map_Ψ₃, map_baseChange]
```

**Equivalence check.** Same qualified name (`WeierstrassCurve.baseChange_Ψ₃`), same section
variables (identical `Algebra`/`IsScalarTower` context, same `f : A →ₐ[S] B`), same statement,
same proof term. The only textual difference is notation: mathlib writes `W⁄B`, the project writes
`W.baseChange B`. These are the *same expression* — `⁄` is `scoped notation:max ... W "⁄" A =>
baseChange W A`, defined in `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:240`. So the
two declarations are syntactically equal after notation expansion.

Mathlib's five search methods all collapse to this one exact hit:
- **Exact name** — `WeierstrassCurve.baseChange_Ψ₃` exists verbatim in mathlib.
- **Statement / `exact?`-style** — would close instantly with the mathlib lemma (same type).
- **Loogle / leansearch (`WeierstrassCurve.Ψ₃`, `baseChange`, `Polynomial.map`)** — moot; an
  exact-name match in the pinned source already settles it. The whole `baseChange_*` family
  (`ψ₂, Ψ₂Sq, Ψ₃, preΨ₄, preΨ', preΨ, ΨSq, Ψ, Φ, ψ, φ`) is present in mathlib lines 553–584.

## 4. Generality / composition / literature

Not applicable for the verdict — the lemma is *already in mathlib in this exact form*, so there is
nothing to generalise toward and nothing to compose. (For completeness: the statement is already at
the natural level of generality — an arbitrary commutative-ring base-change tower along an algebra
hom — matching the standard "division polynomials are natural in the base ring" fact, e.g. Silverman,
*Arithmetic of Elliptic Curves*, Exercise 3.7 / §III.) No literature search is needed to reach the
verdict because the duplication is exact and internal to the pinned dependency.

## 5. Verdict

**NO-mathlib-has-it.** `WeierstrassCurve.baseChange_Ψ₃` is a verbatim duplicate of the mathlib lemma
of the same name at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:559`. It exists in the project
purely because `DivisionPolynomial.lean` is a deliberate fork of that mathlib module (re-pointed at
the project's local `EllipticDivisibilitySequence` to dodge `normEDS`/`complEDS` name clashes). No
contribution is warranted. The consolidation action, if the project ever stops needing the fork, is
to drop the copy and `import` the mathlib lemma directly.

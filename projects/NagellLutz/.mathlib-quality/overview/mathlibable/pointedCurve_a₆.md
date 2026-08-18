# Mathlibable assessment — `WeierstrassCurve.Universal.pointedCurve_a₆`

**Verdict: NO-mathlib-has-it**

- **Qualified name:** `WeierstrassCurve.Universal.pointedCurve_a₆`
- **Source:** `projects/NagellLutz/LutzNagell/Universal.lean:164`
- **Project:** NagellLutz (Nagell–Lutz; division polynomials / elliptic divisibility sequences)
- **Date:** 2026-06-22

## 1. Exact statement (verified from source)

```lean
namespace WeierstrassCurve
namespace Universal
open Polynomial (CC)

-- pointedCurve := baseChange curve Universal.Field   (Universal.lean:130)
-- curve : Affine (MvPolynomial Coeff ℤ)              (Universal.lean:84) with a₆ = MvPolynomial.X A₆
-- polyToField : Poly →+* Universal.Field             (Universal.lean:108)

@[simp] lemma pointedCurve_a₆ : pointedCurve.a₆ = polyToField (CC curve.a₆) := rfl
```

Here `CC r = C (C r)` is the bivariate constant embedding `R → R[X][Y]` (mathlib
`Mathlib/Algebra/Polynomial/Bivariate.lean:47`), `Poly = (MvPolynomial Coeff ℤ)[X][Y]`,
`Universal.Field = FractionRing (curve.CoordinateRing)`, and
`pointedCurve = curve.baseChange Universal.Field`.

It is one of a family of five sibling lemmas `pointedCurve_a₁ … pointedCurve_a₆`
(Universal.lean:160–164), each proved by `rfl`, each `@[simp]`.

## 2. Mathematical content

There is essentially none. The lemma asserts that the `a₆`-coefficient of the curve obtained
by base-changing the *universal* Weierstrass curve to its universal fraction field equals the
canonical ring-homomorphism image of the universal `a₆`. This is pure bookkeeping: it puts
`pointedCurve.a₆` into the project's chosen simp-normal-form (`polyToField (CC ·)`), so that
downstream `simp` calls in `ZSMul.lean` and the division-polynomial development can rewrite the
coefficients of the base-changed curve. It is true **by `rfl`** — definitional.

A literature search is not meaningful here: "the a₆ of a base-changed Weierstrass curve is the
image of a₆ under the structure map" is not a named result in Silverman, Washington, or any
paper — it is an immediate unfolding of the definition of base change of a Weierstrass curve.
(Silverman, *The Arithmetic of Elliptic Curves*, Ch. III gives base change of Weierstrass
equations; coefficients transform by the ring map, tautologically.)

## 3. mathlib search — the general form is already there

mathlib defines the map of a Weierstrass curve **with `@[simps]`**, in
`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`:

```lean
variable {A : Type v} [CommRing A] (f : R →+* A)

/-- The Weierstrass curve mapped over a ring homomorphism `f : R →+* A`. -/
@[simps]                                   -- line 230
def map : WeierstrassCurve A :=
  ⟨f W.a₁, f W.a₂, f W.a₃, f W.a₄, f W.a₆⟩

variable (A) in
def baseChange [Algebra R A] : WeierstrassCurve A :=
  W.map <| algebraMap R A                  -- line 236
```

The `@[simps]` attribute auto-generates the five projection simp lemmas
`WeierstrassCurve.map_a₁ … map_a₆`, in particular:

```lean
@[simp] theorem WeierstrassCurve.map_a₆ : (W.map f).a₆ = f W.a₆
```

(Used internally by mathlib itself, e.g. Weierstrass.lean:254 and 259 inside `map_b₆` / `map_b₈`.)

Search methods applied:
- **grep mathlib source** for `map_a₆ / baseChange_a₆ / @[simps] … map` — found the `@[simps]` def
  and its generated `map_a₆` (the general statement of our lemma).
- **`coe_algebraMap_eq_CC`** (`Mathlib/Algebra/Polynomial/Bivariate.lean:148`):
  `algebraMap R R[X][Y] = CC`, i.e. `CC = algebraMap _ Poly`.

## 4. Generality / specialisation analysis

Our lemma is the mathlib lemma `map_a₆` (general `f : R →+* A`), specialised to
`f = algebraMap (MvPolynomial Coeff ℤ) Universal.Field` and reglued through the project's
`polyToField` normal form. The chain:

```
pointedCurve.a₆
  = (curve.baseChange Universal.Field).a₆
  = (curve.map (algebraMap _ Universal.Field)).a₆
  = algebraMap _ Universal.Field curve.a₆           -- mathlib `map_a₆` (general)
  = polyToField (algebraMap _ Poly curve.a₆)        -- `algebraMap_field_eq_comp` (Universal.lean:113)
  = polyToField (CC curve.a₆)                        -- `coe_algebraMap_eq_CC` (mathlib Bivariate:148)
```

So our lemma is **strictly less general** than the mathlib lemma (which holds for any base ring,
any target, any ring hom). The project version exists only to express the result in terms of the
project-specific `polyToField`/`CC` so that one `simp` discharges it. The `polyToField (CC ·)`
normal-form choice is project glue, with no mathematical generality to recover.

## 5. Composition check (≤ 3 mathlib calls)

Yes — trivially. From existing mathlib + the two adjacent project lemmas this is at most:
`map_a₆` (or `baseChange` unfold) → `algebraMap_field_eq_comp` → `coe_algebraMap_eq_CC`.
In fact it is `rfl`, so even composition is unnecessary. The general lemma plus the bivariate
constant-embedding bridge already cover every use site; the bespoke lemma adds only a
simp-normal-form convenience, not new content.

## 6. Cross-project note (cleanup, not mathlib)

This exact lemma (and its four siblings) is **duplicated verbatim** in HasseWeil:
`projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:163–167`. The whole `Universal` glue file
appears to be a shared fork. That is an **AINTLIB dedup / `Common/` refactor** matter (a cleanup
ticket), independent of the mathlib-contribution decision below.

## 7. Verdict

**NO-mathlib-has-it.**

mathlib's `@[simps] def WeierstrassCurve.map` already provides the general projection lemma
`WeierstrassCurve.map_a₆ : (W.map f).a₆ = f W.a₆`, of which `pointedCurve_a₆` is a `rfl`-level
specialisation reglued into this project's `polyToField`/`CC` simp-normal-form. There is no
general mathematical statement here to upstream — it is project-local definitional glue. Keep it
in the project as a local `@[simp]` convenience; do not add to mathlib.

Evidence:
- mathlib general lemma: `WeierstrassCurve.map_a₆` (generated by `@[simps]` at
  `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:230`).
- bridge to project normal form: `coe_algebraMap_eq_CC`
  (`Mathlib/Algebra/Polynomial/Bivariate.lean:148`) + `algebraMap_field_eq_comp`
  (Universal.lean:113).

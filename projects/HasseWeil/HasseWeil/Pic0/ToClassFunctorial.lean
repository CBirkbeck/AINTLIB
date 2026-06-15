import HasseWeil.Curves.PointFunctor
import HasseWeil.Curves.IntegralClosure
import HasseWeil.Pic0.ToClassSurjective

/-!
# Functoriality of `E ≅ Pic⁰(E)` on the point map (Silverman III.3.4) — ideal-level core

For an elliptic curve `E` over a field `F`, mathlib's
`toClass : W.Point →+ Additive (ClassGroup R)` (with `R := E.CoordinateRing`) and the
surjectivity packaged in `WeierstrassCurve.Affine.Point.toClassEquiv'` realise the
isomorphism `E ≃+ Pic⁰(E)`.

This file isolates the **functoriality content** of Silverman III.3.4 at the level the
`toClass`/`XYIdeal'` API actually exposes: how the geometric point map of an endomorphism
corresponds to an *ideal* map of `Pic⁰(E)`. The headline difficulty (and the reason the
naive `toClass_isogeny_compat` is *not* directly provable from the shipped infrastructure)
is a **variance mismatch** which this file makes precise and unavoidable; see below.

## The point-map ↔ ideal-map link (the exact identity)

mathlib sends a finite point `P = (x, y)` to the class of the fractional ideal
`XYIdeal' h = ⟨X - x, Y - y⟩`, whose underlying integral ideal `XYIdeal W x (C y)` is
*exactly* the project's `maximalIdealAt P` (the maximal ideal at `P`). Hence
(`toClass_toAffinePoint`)

```
toClass (P.toAffinePoint) = Additive.ofMul (ClassGroup.mk0 ⟨maximalIdealAt P, _⟩).
```

For a `Curves.CurveMap φ` with a coordinate-ring witness `coordHom` (the comorphism
`α* : R → R`), the project's `Curves.CurveMap.maximalIdealAt_toPointMap` gives the
scheme-theoretic identity

```
maximalIdealAt (φ.toPointMap coordHom P)
  = Ideal.comap coordHom.toAlgHom.toRingHom (maximalIdealAt P).
```

i.e. the maximal ideal **at the image point** `φ(P)` is the **contraction / `comap`** of
the maximal ideal at `P` along the comorphism. This is the morphism-from-comorphism
direction of Silverman II.2.4 (specialised; III.3.4 is the `Pic⁰` packaging). Composing the
two displays gives the functoriality identity proved here (`toClass_toPointMap`):

```
toClass ((φ.toPointMap coordHom P).toAffinePoint)
  = Additive.ofMul
      (ClassGroup.mk0 ⟨Ideal.comap coordHom.toAlgHom.toRingHom (maximalIdealAt P), _⟩).
```

**The variance is `comap` (contraction / transpose), not `Ideal.map` (extension).**

## Why this is *not* `classMap`, and why naive `toClass_isogeny_compat` is unprovable here

`HasseWeil.Isogeny.classMap` is built from `Ideal.map (algebraMap …)` (the *extension*
`α_*`) and `HasseWeil.Isogeny.classNorm` from `Ideal.relNorm` (the *norm* `α^*` direction).
The genuinely-true point-map functoriality above is the **`comap`** of an ideal, a *third*
operation, equal to neither `Ideal.map` nor `Ideal.relNorm` on a single prime: `comap` and
`map` are adjoint, not equal, and `relNorm P = p^f ≠ comap P` in general. Therefore

```
toClass (α P) = (additive-wrap of α.classMap ch) (toClass P)     -- classMap = Ideal.map
```

is **false as stated** for the shipped `classMap`: it would force
`class (comap m_P) = class (map m_P)` on every prime, which fails. What *is* true at the
ideal level is the `comap` identity here; turning it into `classNorm`/`classMap` requires
the genuine Riemann–Roch/divisor functoriality `relNorm (comap …) = (·)^?`, i.e. the
inertia/ramification bookkeeping (`relNorm_eq_pow_of_isMaximal`, which needs
`PerfectField (FractionRing R)` — *not* available for a general base, and in any case the
exponent is the inertia degree, not a clean power of the class). This is exactly the III.3.4
content the `Isogeny` carries as *independent data* (`pullback` and `toAddMonoidHom` are
unlinked beyond `CoordHom.compat` on the function field); the comorphism-to-point-map
compatibility is an **extra unproven theorem**, not derivable from `compat` alone.

## What is shipped (all `#print axioms`-clean)

* `WeierstrassCurve.Affine.Point.toClass_toAffinePoint` — `toClass` of a smooth point is the
  `mk0` class of its maximal ideal (the `mk`/`mk0` bridge, via `mk0_eq_mk_XYIdeal'`).
  Unconditional.
* `HasseWeil.Curves.CurveMap.toClass_toPointMap` — the **III.3.4 ideal-level functoriality**:
  the class of `φ(P)` is the `mk0` class of `comap(α*)(maximalIdealAt P)`. The
  `comap`-is-nonzero side condition is carried as a hypothesis `hne` (it holds whenever the
  comorphism is module-finite / integral, e.g. for a genuine isogeny — *not* universally,
  since `comap` of a nonzero prime along a non-integral inclusion can be `⊥`).
* `HasseWeil.Curves.CurveMap.toClass_toPointMap_id` — the identity-isogeny base case, fully
  unconditional (comap along `AlgHom.id` is the identity, so it collapses to `toClass P`).

The `comap`-level identity is the **correct** and reachable form of III.3.4 functoriality in this
codebase. The signed `deg(rπ − s) = N` does **not** follow from it (see the report / the project
tickets): that needs the dual relation at the *pullback / inseparable-degree* level, which the
point-level `Pic⁰` infrastructure cannot supply.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.4 (morphism ↔ comorphism), III.3.4
  (functoriality of `E ≅ Pic⁰(E)`).
-/

open WeierstrassCurve Polynomial
open scoped nonZeroDivisors

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] [DecidableEq F]

/-- **`toClass` of a smooth point is the `mk0` class of its maximal ideal.**

mathlib's `toClass` sends `P = (x, y)` to the class of the fractional ideal `XYIdeal' h`;
its underlying integral ideal `XYIdeal W x (C y)` is the project's `maximalIdealAt P`. The
`mk`/`mk0` bridge `mk0_eq_mk_XYIdeal'` identifies the two class constructors, so `toClass(P)`
is the additive wrap of `ClassGroup.mk0` of the maximal ideal at `P`.

This is the affine-coordinate-ring incarnation of `κ : E → Pic⁰(E)`, `P ↦ [(P) - (O)]`, at
the level of mathlib's ideal class group. -/
theorem toClass_toAffinePoint {C : HasseWeil.Curves.SmoothPlaneCurve F}
    [C.toAffine.IsElliptic] (P : C.SmoothPoint) :
    toClass (P.toAffinePoint) =
      Additive.ofMul (ClassGroup.mk0 ⟨C.maximalIdealAt P,
        mem_nonZeroDivisors_iff_ne_zero.mpr (C.maximalIdealAt_ne_bot P)⟩) := by
  rw [HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint_def, toClass_some,
    ← mk0_eq_mk_XYIdeal' P.nonsingular
      (mem_nonZeroDivisors_iff_ne_zero.mpr (C.maximalIdealAt_ne_bot P))]
  rfl

end WeierstrassCurve.Affine.Point

namespace HasseWeil.Curves.CurveMap

open WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] [DecidableEq F]
variable {C₁ C₂ : HasseWeil.Curves.SmoothPlaneCurve F}
  [C₁.toAffine.IsElliptic] [C₂.toAffine.IsElliptic]

omit [C₁.toAffine.IsElliptic] in
/-- **Silverman III.3.4 functoriality, ideal-level core (`comap` form).**

For a `CurveMap φ : C₁ → C₂` with comorphism witness `coordHom` (the algebra hom
`α* : R₂ → R₁` on coordinate rings) and a smooth point `P` of `C₁`, the class of the image
point `φ(P)` in `Pic⁰(C₂)` is the `mk0` class of the **contraction**
`comap(α*)(maximalIdealAt P)`:

```
toClass ((φ.toPointMap coordHom P).toAffinePoint)
  = Additive.ofMul
      (ClassGroup.mk0 ⟨comap coordHom.toAlgHom.toRingHom (maximalIdealAt P), _⟩).
```

This is the exact, true point-map ↔ ideal-map link. The variance is `comap` (transpose),
**not** `Ideal.map` (the `classMap` extension) and **not** `Ideal.relNorm` (the `classNorm`
norm); see the module note for why this blocks naive `toClass_isogeny_compat` vs `classMap`.

The hypothesis `hne` (`comap(α*)(maximalIdealAt P) ≠ ⊥`) is the only side condition; it holds
for any module-finite / integral comorphism (e.g. a genuine isogeny), but is *not* automatic
— a non-integral inclusion can contract a nonzero prime to `⊥`. Supplied by the caller. -/
theorem toClass_toPointMap {φ : CurveMap C₁ C₂} (coordHom : φ.CoordHom)
    (P : C₁.SmoothPoint)
    (hne : Ideal.comap coordHom.toAlgHom.toRingHom (C₁.maximalIdealAt P) ≠ ⊥) :
    toClass ((toPointMap coordHom P).toAffinePoint) =
      Additive.ofMul (ClassGroup.mk0
        ⟨Ideal.comap coordHom.toAlgHom.toRingHom (C₁.maximalIdealAt P),
          mem_nonZeroDivisors_iff_ne_zero.mpr hne⟩) := by
  rw [toClass_toAffinePoint (toPointMap coordHom P)]
  -- `maximalIdealAt (φ P) = comap α* (maximalIdealAt P)` is the scheme-theoretic shadow.
  have hmax := maximalIdealAt_toPointMap coordHom P
  -- Rewrite the underlying ideal of the `mk0` argument.
  congr 1
  exact congrArg ClassGroup.mk0 (Subtype.ext hmax)

/-- **Identity-isogeny base case (unconditional).** For the identity curve map with the
identity coordinate-ring witness, `toClass` of `φ(P)` is just `toClass P`: the point map is
the identity (`toPointMap_id`), so the `comap` collapses. This is the `α = id` instance of
III.3.4 functoriality, and it needs no side condition. -/
theorem toClass_toPointMap_id {C : HasseWeil.Curves.SmoothPlaneCurve F}
    [C.toAffine.IsElliptic] (P : C.SmoothPoint) :
    toClass ((toPointMap (CoordHom.id C) P).toAffinePoint) =
      toClass (P.toAffinePoint) := by
  rw [toPointMap_id]

end HasseWeil.Curves.CurveMap

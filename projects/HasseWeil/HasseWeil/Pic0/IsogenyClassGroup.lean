import HasseWeil.Basic
import HasseWeil.Ramification
import HasseWeil.Pic0.ClassGroupNorm

/-!
# The isogeny ↔ class-group bridge (reusable Pic⁰ infrastructure)

This file packages, for an endomorphism `α : Isogeny E E` of an elliptic curve `E`, the data and
lemmas needed to push `α` down to the ideal class group `ClassGroup E.CoordinateRing` and recover
the dual relation `α̂ ∘ α = [deg α]` at the level of `ClassGroup`.

The function-field pullback `α.pullback : E.FunctionField →ₐ[F] E.FunctionField` does **not** in
general restrict to the coordinate ring `R := E.CoordinateRing` (this is the
integrality-preservation content of Silverman III.3.4, deliberately *not* discharged here).  We
therefore carry the restriction as **data**, an `Isogeny.CoordHom`, mirroring
`Curves.CurveMap.CoordHom`.

The deep obligations are carried as **hypotheses** (witness-parametric), not discharged universally:

* injectivity of the coordinate-ring restriction (`hinj`), giving `FaithfulSMul`/`IsTorsionFree`;
* finiteness of `R` over itself through the restriction (`Module.Finite`), giving the `ClassGroup`
  norm/extension maps and matching `α.degree` to the coordinate-ring `finrank`.

These are instantiable per isogeny (e.g. Frobenius, multiplication-by-`n`); the universal versions
are separate, flagged-deep tickets.

## Main definitions

* `HasseWeil.Isogeny.CoordHom`: the coordinate-ring restriction witness for `α : Isogeny E E`.
* `HasseWeil.Isogeny.CoordHom.toAlgebra`: the induced `R`-algebra structure on `R`.
* `HasseWeil.Isogeny.classNorm` / `Isogeny.classMap`: the relative norm / extension maps on
  `ClassGroup R` induced by a `CoordHom`.

## Main results

* `HasseWeil.Isogeny.degree_eq_finrank_coordinateRing_of_tower_eq`: `α.degree` equals the
  coordinate-ring `finrank` of `ch.toAlgebra`, given a fraction-field tower witness for the
  `ch`-twisted coordinate ring (witness-parametric, to sidestep a same-type instance diamond — see
  the lemma's docstring).
* `HasseWeil.Isogeny.classNorm_comp_classMap`: `classNorm (classMap c) = c ^ (finrank R R)` — the
  class-group shadow of `α̂ ∘ α = [deg α]`, exponent as the coordinate-ring degree.
* `HasseWeil.Isogeny.classNorm_comp_classMap_degree`: the same with exponent `α.degree` (combines
  the previous two; carries the tower witness as hypotheses).

## Design note

The function-field pullback restricted to coordinate rings and lifted back to the fraction field
gives, on the *same* carriers `R` and `FF`, a *non-identity* algebra structure.  Several would-be
"auto-derived" scalar towers (`R → R → FF`, `R → FF → FF`) are therefore **false** as stated with
the canonical base action, and `finrank_of_isFractionRing` cannot be applied with `S = R`,
`S' = FF` literally (the `IsFractionRing` typeclass cannot distinguish the canonical inclusion from
the twisted map).  The deep obligations (injectivity `hinj`, finiteness `Module.Finite`, and the
fraction-field tower witness for the degree bridge) are consequently carried as **hypotheses**;
they are instantiable per isogeny (Frobenius, multiplication-by-`n`).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.3.4, III.4, III.6.
-/

open WeierstrassCurve Polynomial
open scoped nonZeroDivisors

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable {E : Affine F} [E.IsElliptic]

/-- **Coordinate-ring restriction witness** for an endomorphism `α : Isogeny E E`.

A ring hom `R →ₐ[F] R` on the coordinate ring `R := E.CoordinateRing`, compatible with the
function-field pullback `α.pullback`.  Not every function-field pullback restricts to the coordinate
ring, hence this is data rather than automatic (mirrors `Curves.CurveMap.CoordHom`). -/
structure Isogeny.CoordHom (α : Isogeny E E) where
  /-- The `F`-algebra hom on the coordinate ring `R := E.CoordinateRing`. -/
  toAlgHom : E.CoordinateRing →ₐ[F] E.CoordinateRing
  /-- Compatibility with the function-field pullback: the square
      `R → R → E.FunctionField` (restriction then inclusion) commutes with
      `R → E.FunctionField → E.FunctionField` (inclusion then pullback). -/
  compat : ∀ u : E.CoordinateRing,
    α.pullback (algebraMap E.CoordinateRing E.FunctionField u) =
      algebraMap E.CoordinateRing E.FunctionField (toAlgHom u)

namespace Isogeny.CoordHom

variable {α : Isogeny E E}

/-- The `R`-algebra structure on `R := E.CoordinateRing` induced by a `CoordHom` witness. -/
@[reducible]
noncomputable def toAlgebra (ch : α.CoordHom) :
    Algebra E.CoordinateRing E.CoordinateRing :=
  ch.toAlgHom.toRingHom.toAlgebra

/-- From injectivity of the coordinate-ring restriction, `R` acts faithfully on `R` through `ch`.

Built by hand (rather than `FaithfulSMul.of_injective`) to avoid the `R → R` instance diamond
between the canonical `Algebra.id` and `ch.toAlgebra`: from `r₁ • x = r₂ • x` for all `x`, take
`x = 1` and use `Algebra.smul_def` to get `toAlgHom r₁ = toAlgHom r₂`, then `hinj`. -/
theorem faithfulSMul (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom) :
    @FaithfulSMul E.CoordinateRing E.CoordinateRing ch.toAlgebra.toSMul := by
  refine @FaithfulSMul.mk _ _ ch.toAlgebra.toSMul fun {r₁ r₂} h => hinj ?_
  have h1 := h (1 : E.CoordinateRing)
  rwa [@Algebra.smul_def _ _ _ _ ch.toAlgebra, @Algebra.smul_def _ _ _ _ ch.toAlgebra,
    mul_one, mul_one] at h1

/-- From injectivity of the coordinate-ring restriction, `R` is torsion-free over `R` through `ch`.

Built by hand (rather than `trans_faithfulSMul`, which would re-trigger the `R → R` diamond): for
`r` regular (hence `r ≠ 0`) the scalar action `x ↦ toAlgHom r * x` is injective because
`toAlgHom r ≠ 0` (by `hinj` and `map_zero`) in the domain `R`. -/
theorem isTorsionFree (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom) :
    @Module.IsTorsionFree E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule := by
  refine @Module.IsTorsionFree.mk _ _ _ _ ch.toAlgebra.toModule fun {r} hr => ?_
  have hrne : r ≠ 0 := isRegular_iff_ne_zero.mp hr
  have hfr : ch.toAlgHom r ≠ 0 := fun h => hrne (hinj (by rw [h, map_zero]))
  intro x y hxy
  simp only at hxy
  rw [@Algebra.smul_def _ _ _ _ ch.toAlgebra, @Algebra.smul_def _ _ _ _ ch.toAlgebra] at hxy
  have heq : @algebraMap E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra r =
      ch.toAlgHom r := rfl
  rw [heq] at hxy
  exact mul_left_cancel₀ hfr hxy

end Isogeny.CoordHom

namespace Isogeny

variable {α : Isogeny E E}

/-- The **relative norm on the class group** induced by an endomorphism `α : Isogeny E E` and a
coordinate-ring restriction witness `ch`, with the finiteness obligation carried as a hypothesis.

This is `ClassGroup.relNorm` for the extension `R → R` given by `ch.toAlgebra`; it is the
class-group shadow of the dual isogeny `α̂`.  The torsion-free hypothesis is discharged from
injectivity of `ch.toAlgHom`; `Module.Finite` is supplied by the caller (instantiable per
isogeny). -/
noncomputable def classNorm (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule) :
    ClassGroup E.CoordinateRing →* ClassGroup E.CoordinateRing :=
  letI := ch.toAlgebra
  haveI hfinI : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule := hfin
  haveI htfI : @Module.IsTorsionFree E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule :=
    ch.isTorsionFree hinj
  @ClassGroup.relNorm E.CoordinateRing E.CoordinateRing _ _ _ _ _ _ _ _ ch.toAlgebra hfinI htfI

/-- The **extension map on the class group** induced by `α : Isogeny E E` and a coordinate-ring
restriction witness `ch`, with the finiteness obligation carried as a hypothesis.

This is `ClassGroup.map` for the extension `R → R` given by `ch.toAlgebra`; it is the class-group
shadow of `α` itself (pull an ideal class up along the restriction). -/
noncomputable def classMap (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule) :
    ClassGroup E.CoordinateRing →* ClassGroup E.CoordinateRing :=
  letI := ch.toAlgebra
  haveI : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule := hfin
  haveI htfI : @Module.IsTorsionFree E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule :=
    ch.isTorsionFree hinj
  @ClassGroup.map E.CoordinateRing E.CoordinateRing _ _ _ _ _ _ ch.toAlgebra htfI

/-- **Function-field ↔ coordinate-ring degree bridge (witness-parametric `_of_tower_eq` form).**

The function-field degree `α.degree` equals the coordinate-ring degree
`Module.finrank R R` (with `R` carrying `ch.toAlgebra`), *given* a fraction-field tower witness for
the `ch`-twisted coordinate ring.

The deep obstruction (see the file-level note and the round report) is a genuine **same-type
instance diamond**: `Algebra.IsAlgebraic.finrank_of_isFractionRing` needs the source/target rings
`R, S` and their fraction fields `R', S'` to be *distinguishable type pairs* so that
`IsFractionRing R R'` and `IsFractionRing S S'` can coexist with the canonical inclusion (for `R'`)
and the `ch`-twisted map (for the `S → S'` tower) respectively.  With `S = R` and `S' = R' = FF`
*literally*, Lean's instance resolution cannot keep the two `Algebra R FF` structures apart, even
though the required equation `α.pullback (algebraMap R FF r) = algebraMap R FF (ch.toAlgHom r)` is
exactly `ch.compat`.

We therefore expose the bridge witness-parametrically: the caller supplies a *distinct nominal copy*
`S` of the `ch`-twisted coordinate ring together with its fraction field `S'` (a copy of
`E.FunctionField` carrying `α.toAlgebra`), the standard fraction-field tower instances, and the two
`Module.finrank`-transfer equalities `hSR`, `hS'FF` (each a `LinearEquiv.finrank_eq` away once the
copies are chosen).  These are dischargeable per isogeny (Frobenius, multiplication-by-`n`).

The conclusion is then a one-line application of `finrank_of_isFractionRing` between the four
distinct type slots `R, FF, S, S'`. -/
theorem degree_eq_finrank_coordinateRing_of_tower_eq (ch : α.CoordHom)
    (S : Type*) [CommRing S] [Algebra E.CoordinateRing S]
    [FaithfulSMul E.CoordinateRing S] [Algebra.IsAlgebraic E.CoordinateRing S] [NoZeroDivisors S]
    (S' : Type*) [CommRing S'] [Algebra E.CoordinateRing S'] [Algebra S S']
    [Module E.FunctionField S']
    [IsScalarTower E.CoordinateRing E.FunctionField S'] [IsScalarTower E.CoordinateRing S S']
    [IsFractionRing S S']
    (hSR : @Module.finrank E.CoordinateRing S _ _ _ =
      @Module.finrank E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hS'FF : @Module.finrank E.FunctionField S' _ _ _ = α.degree) :
    α.degree = @Module.finrank E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule := by
  rw [← hSR, ← hS'FF]
  exact Algebra.IsAlgebraic.finrank_of_isFractionRing E.CoordinateRing E.FunctionField S S'

/-- **The class-group dual relation (coordinate-ring `finrank` form).**

For an endomorphism `α : Isogeny E E` with coordinate-ring restriction `ch`, the composite of the
extension map with the relative norm is raising to the power `Module.finrank R R` (where `R` carries
the `ch.toAlgebra` structure):
`classNorm (classMap c) = c ^ (Module.finrank R R)` for every `c : ClassGroup R`.

This is the class-group shadow of `α̂ ∘ α = [deg α]`, with the exponent expressed as the
coordinate-ring degree.  To express the exponent as `α.degree` (the function-field degree), compose
with `degree_eq_finrank_coordinateRing_of_tower_eq` (the function-field ↔ coordinate-ring degree
bridge, separately flagged). -/
theorem classNorm_comp_classMap (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (c : ClassGroup E.CoordinateRing) :
    α.classNorm ch hinj hfin (α.classMap ch hinj hfin c) =
      c ^ (letI := ch.toAlgebra;
        @Module.finrank E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule) := by
  letI := ch.toAlgebra
  haveI hfinI : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule := hfin
  haveI htfI : @Module.IsTorsionFree E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule :=
    ch.isTorsionFree hinj
  exact @ClassGroup.relNorm_comp_map E.CoordinateRing E.CoordinateRing _ _ _ _ _ _ _ _
    ch.toAlgebra hfinI htfI c

/-- **The class-group dual relation (`α.degree` form).**

`classNorm (classMap c) = c ^ α.degree`, the class-group shadow of `α̂ ∘ α = [deg α]` with the
exponent expressed as the function-field degree `α.degree`.

Obtained from `classNorm_comp_classMap` (coordinate-ring `finrank` form) by rewriting the exponent
through the degree bridge `degree_eq_finrank_coordinateRing_of_tower_eq`, whose fraction-field tower
witness `(S, S', …)` is carried as hypotheses (dischargeable per isogeny). -/
theorem classNorm_comp_classMap_degree (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (S : Type*) [CommRing S] [Algebra E.CoordinateRing S]
    [FaithfulSMul E.CoordinateRing S] [Algebra.IsAlgebraic E.CoordinateRing S] [NoZeroDivisors S]
    (S' : Type*) [CommRing S'] [Algebra E.CoordinateRing S'] [Algebra S S']
    [Module E.FunctionField S']
    [IsScalarTower E.CoordinateRing E.FunctionField S'] [IsScalarTower E.CoordinateRing S S']
    [IsFractionRing S S']
    (hSR : @Module.finrank E.CoordinateRing S _ _ _ =
      @Module.finrank E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (hS'FF : @Module.finrank E.FunctionField S' _ _ _ = α.degree)
    (c : ClassGroup E.CoordinateRing) :
    α.classNorm ch hinj hfin (α.classMap ch hinj hfin c) = c ^ α.degree := by
  rw [α.degree_eq_finrank_coordinateRing_of_tower_eq ch S S' hSR hS'FF]
  exact α.classNorm_comp_classMap ch hinj hfin c

end Isogeny

end HasseWeil

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Foundation.Curves.Divisor.MillerAllChar
import HasseWeil.Foundation.Ramification
import HasseWeil.Pic0.PicDualClassMapMultiplicativity

/-!
# The theorem of the square in divisor form

This file gives a characteristic-free divisor formulation of the theorem of the square for an
elliptic curve. For `κ(P) = (P) - (O)` and the sum map `σ : Pic⁰ → E`, Miller's relation gives
`κ(P + Q) ∼ κ(P) + κ(Q)`. The identity `σ(κ(P)) = P` identifies vanishing divisor sums with
pointwise additivity.

The final results apply this formulation to the pullback dual of an isogeny. They isolate dual
additivity as the condition that the corresponding difference divisor has sum zero, and derive the
Frobenius-trace relation used by the Route C degree argument.

## Main results

* `kappaDivisor_add_linEquiv`: additivity of `κ` up to linear equivalence.
* `tos_divisor`: the divisor-form theorem of the square for additive point maps.
* `sigma_delta_eq_zero_iff`: vanishing of the divisor sum is equivalent to pointwise additivity.
* `tos_toClass`: the corresponding identity in the ideal class group.
* `picDual_add_iff_sigma_vanishes`: dual additivity as vanishing of a divisor sum.
* `htrace_dual_of_picDual_add`: the Route C trace identity obtained from dual additivity.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.3.4–3.5 and III.6.1–III.6.2.
-/

open WeierstrassCurve
open HasseWeil.Curves
open scoped nonZeroDivisors

namespace HasseWeil.Pic0.RouteCTheoremOfSquareDiv

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- The projective divisors `κ(A + B)` and `κ(A) + κ(B)` are linearly equivalent. -/
theorem kappaDivisor_add_linEquiv (A B : W.Point) :
    SmoothPlaneCurve.ProjLinearlyEquiv (⟨W⟩ : SmoothPlaneCurve F)
      (Curves.kappaDivisor W (A + B))
      (Curves.kappaDivisor W A + Curves.kappaDivisor W B) :=
  Curves.kappaDivisor_add_linEquiv_of_miller W (Curves.miller_hypothesis_holds_allChar W) A B

/-- If `f Q = g Q + h Q`, then `κ(f Q) - κ(g Q) - κ(h Q)` is principal. -/
theorem tos_divisor
    {f g h : W.Point →+ W.Point}
    (hsum : ∀ Q, f Q = g Q + h Q) (Q : W.Point) :
    SmoothPlaneCurve.ProjIsPrincipal (⟨W⟩ : SmoothPlaneCurve F)
      (Curves.kappaDivisor W (f Q) - Curves.kappaDivisor W (g Q) -
        Curves.kappaDivisor W (h Q)) := by
  rw [sub_sub, hsum Q]
  exact kappaDivisor_add_linEquiv W (g Q) (h Q)

/-- The sum of `κ(f Q) - κ(g Q) - κ(h Q)` is `f Q - g Q - h Q`. -/
theorem sigma_delta
    {f g h : W.Point →+ W.Point} (Q : W.Point) :
    Curves.projectiveDivisorSum W
        (Curves.kappaDivisor W (f Q) - Curves.kappaDivisor W (g Q) -
          Curves.kappaDivisor W (h Q)) =
      f Q - g Q - h Q := by
  rw [Curves.projectiveDivisorSum_sub, Curves.projectiveDivisorSum_sub,
    Curves.projectiveDivisorSum_kappaDivisor, Curves.projectiveDivisorSum_kappaDivisor,
    Curves.projectiveDivisorSum_kappaDivisor]

/-- The sum of `κ(f Q) - κ(g Q) - κ(h Q)` vanishes exactly when `f Q = g Q + h Q`. -/
theorem sigma_delta_eq_zero_iff
    {f g h : W.Point →+ W.Point} (Q : W.Point) :
    Curves.projectiveDivisorSum W
        (Curves.kappaDivisor W (f Q) - Curves.kappaDivisor W (g Q) -
          Curves.kappaDivisor W (h Q)) = 0 ↔
      f Q = g Q + h Q := by
  rw [sigma_delta, sub_sub, sub_eq_zero]

omit [W.IsElliptic] in
/-- Pointwise additivity gives the corresponding identity under `Point.toClass`. -/
theorem tos_toClass
    {f g h : W.Point →+ W.Point}
    (hsum : ∀ Q, f Q = g Q + h Q) (Q : W.Point) :
    WeierstrassCurve.Affine.Point.toClass (f Q) =
      WeierstrassCurve.Affine.Point.toClass (g Q) +
        WeierstrassCurve.Affine.Point.toClass (h Q) := by
  rw [hsum Q, map_add]

/-- The image of `f Q` under `toClassEquiv'` is additive exactly when `f Q = g Q + h Q`. -/
theorem toClassEquiv'_add_iff
    {f g h : W.Point →+ W.Point} (Q : W.Point) :
    WeierstrassCurve.Affine.Point.toClassEquiv' (W := W) (f Q) =
        WeierstrassCurve.Affine.Point.toClassEquiv' (W := W) (g Q) +
          WeierstrassCurve.Affine.Point.toClassEquiv' (W := W) (h Q) ↔
      f Q = g Q + h Q := by
  rw [← map_add]
  exact (WeierstrassCurve.Affine.Point.toClassEquiv' (W := W)).injective.eq_iff

end HasseWeil.Pic0.RouteCTheoremOfSquareDiv

namespace HasseWeil.Pic0.RouteCTheoremOfSquareDiv

open HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable {E : WeierstrassCurve.Affine F} [E.IsElliptic]

/-- Dual additivity is equivalent to its pointwise formulation. -/
theorem picDual_add_iff_pointwise
    {α α₁ α₂ : Isogeny E E}
    (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (ch₁ : α₁.CoordHom) (hinj₁ : Function.Injective ch₁.toAlgHom)
    (hfin₁ : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch₁.toAlgebra.toModule)
    (ch₂ : α₂.CoordHom) (hinj₂ : Function.Injective ch₂.toAlgHom)
    (hfin₂ : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch₂.toAlgebra.toModule) :
    (α.picDual ch hinj hfin =
      α₁.picDual ch₁ hinj₁ hfin₁ + α₂.picDual ch₂ hinj₂ hfin₂) ↔
      (∀ Q : E.Point, α.picDual ch hinj hfin Q =
        α₁.picDual ch₁ hinj₁ hfin₁ Q + α₂.picDual ch₂ hinj₂ hfin₂ Q) := by
  simp only [DFunLike.ext_iff, AddMonoidHom.add_apply]

/-- Dual additivity holds exactly when the associated difference divisor has sum zero at every
point. -/
theorem picDual_add_iff_sigma_vanishes
    {α α₁ α₂ : Isogeny E E}
    (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (ch₁ : α₁.CoordHom) (hinj₁ : Function.Injective ch₁.toAlgHom)
    (hfin₁ : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch₁.toAlgebra.toModule)
    (ch₂ : α₂.CoordHom) (hinj₂ : Function.Injective ch₂.toAlgHom)
    (hfin₂ : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch₂.toAlgebra.toModule) :
    (α.picDual ch hinj hfin =
      α₁.picDual ch₁ hinj₁ hfin₁ + α₂.picDual ch₂ hinj₂ hfin₂) ↔
      (∀ Q : E.Point,
        Curves.projectiveDivisorSum E
            (Curves.kappaDivisor E (α.picDual ch hinj hfin Q) -
              Curves.kappaDivisor E (α₁.picDual ch₁ hinj₁ hfin₁ Q) -
              Curves.kappaDivisor E (α₂.picDual ch₂ hinj₂ hfin₂ Q)) = 0) := by
  rw [picDual_add_iff_pointwise]
  exact forall_congr' fun Q ↦ (sigma_delta_eq_zero_iff E
    (f := α.picDual ch hinj hfin) (g := α₁.picDual ch₁ hinj₁ hfin₁)
    (h := α₂.picDual ch₂ hinj₂ hfin₂) Q).symm

/-- The Route C Frobenius-trace identity obtained from dual additivity and its two summand
identities. -/
theorem htrace_dual_of_picDual_add
    {α α₁ α₂ : Isogeny E E}
    (ch : α.CoordHom) (hinj : Function.Injective ch.toAlgHom)
    (hfin : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch.toAlgebra.toModule)
    (ch₁ : α₁.CoordHom) (hinj₁ : Function.Injective ch₁.toAlgHom)
    (hfin₁ : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch₁.toAlgebra.toModule)
    (ch₂ : α₂.CoordHom) (hinj₂ : Function.Injective ch₂.toAlgHom)
    (hfin₂ : @Module.Finite E.CoordinateRing E.CoordinateRing _ _ ch₂.toAlgebra.toModule)
    {π V : E.Point →+ E.Point} (r s t : ℤ)
    (hbeta : α.toAddMonoidHom = r • π - s • (AddMonoidHom.id _))
    (hsum : π + V = (mulByInt E t).toAddMonoidHom)
    (hdual₁ : α₁.picDual ch₁ hinj₁ hfin₁ = r • V)
    (hdual₂ : α₂.picDual ch₂ hinj₂ hfin₂ = -(s • (AddMonoidHom.id _)))
    (hadd : α.picDual ch hinj hfin =
      α₁.picDual ch₁ hinj₁ hfin₁ + α₂.picDual ch₂ hinj₂ hfin₂) :
    α.toAddMonoidHom + α.picDual ch hinj hfin =
      (mulByInt E (r * t - 2 * s)).toAddMonoidHom :=
  RouteCAdditivity.htrace_dual_of_picDual_additive ch hinj hfin ch₁ hinj₁ hfin₁ ch₂ hinj₂
    hfin₂ r s t hbeta hsum hdual₁ hdual₂ hadd

end HasseWeil.Pic0.RouteCTheoremOfSquareDiv

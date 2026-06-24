module

public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Formal logarithm identities for the finite logarithm

This file isolates the formal-power-series identity behind finite-log
additivity.  The identity is proved with a dummy variable `T`; substituting
`T * x` and `T * y` makes coefficients of `T^d` record total degree `d` in the
two principal-unit coordinates.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace Furtwaengler

namespace FiniteLogFormal

open PowerSeries

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The derivative of `log(1+X)` is inverse to `1+X` as a formal series. -/
theorem deriv_log_mul_one_add_X :
    (d⁄dX A (PowerSeries.log A)) * (1 + PowerSeries.X) = 1 := by
  have h :=
    congrArg (PowerSeries.rescale (-1 : A))
      (PowerSeries.mk_one_mul_one_sub_eq_one A)
  rw [map_mul, map_one] at h
  simpa [PowerSeries.deriv_log, PowerSeries.rescale_mk, PowerSeries.rescale_X] using h

theorem subst_deriv_log_mul_one_add {a : PowerSeries A} (ha : PowerSeries.HasSubst a) :
    (PowerSeries.subst a (d⁄dX A (PowerSeries.log A))) * (1 + a) = 1 := by
  have h := congrArg (PowerSeries.subst a) (deriv_log_mul_one_add_X (A := A))
  rw [PowerSeries.subst_mul ha] at h
  have h_one : PowerSeries.subst a (1 : PowerSeries A) = 1 := by
    rw [show (1 : PowerSeries A) = PowerSeries.C (1 : A) by rfl]
    rw [PowerSeries.subst_C]
    rfl
  have h_one_add : PowerSeries.subst a (1 + PowerSeries.X : PowerSeries A) = 1 + a := by
    rw [PowerSeries.subst_add ha, PowerSeries.subst_X ha, h_one]
  simpa [h_one_add, h_one] using h

/-- `log((1+T*x)*(1+T*y)) = log(1+T*x) + log(1+T*y)`.

The dummy variable `T` is the `PowerSeries.X`; in later quotient arguments,
the coefficient of `T^d` is the total-degree-`d` part of the two-variable
identity. -/
theorem log_subst_mul_one_add_scaled [IsAddTorsionFree A] (x y : A) :
    PowerSeries.subst
        ((1 + PowerSeries.X * PowerSeries.C x) *
            (1 + PowerSeries.X * PowerSeries.C y) - 1)
        (PowerSeries.log A) =
      PowerSeries.subst (PowerSeries.X * PowerSeries.C x) (PowerSeries.log A) +
        PowerSeries.subst (PowerSeries.X * PowerSeries.C y) (PowerSeries.log A) := by
  let a : PowerSeries A := PowerSeries.X * PowerSeries.C x
  let b : PowerSeries A := PowerSeries.X * PowerSeries.C y
  let z : PowerSeries A := (1 + a) * (1 + b) - 1
  have ha0 : PowerSeries.constantCoeff a = 0 := by simp [a]
  have hb0 : PowerSeries.constantCoeff b = 0 := by simp [b]
  have hz0 : PowerSeries.constantCoeff z = 0 := by simp [z, a, b]
  have ha : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero' ha0
  have hb : PowerSeries.HasSubst b := PowerSeries.HasSubst.of_constantCoeff_zero' hb0
  have hz : PowerSeries.HasSubst z := PowerSeries.HasSubst.of_constantCoeff_zero' hz0
  have hone_z : 1 + z = (1 + a) * (1 + b) := by
    simp [z]
  have hgeom_z :
      PowerSeries.subst z (d⁄dX A (PowerSeries.log A)) * ((1 + a) * (1 + b)) = 1 := by
    simpa [hone_z] using subst_deriv_log_mul_one_add (A := A) hz
  have hgeom_a :
      PowerSeries.subst a (d⁄dX A (PowerSeries.log A)) * (1 + a) = 1 :=
    subst_deriv_log_mul_one_add (A := A) ha
  have hgeom_b :
      PowerSeries.subst b (d⁄dX A (PowerSeries.log A)) * (1 + b) = 1 :=
    subst_deriv_log_mul_one_add (A := A) hb
  have hunit_a : IsUnit (1 + a) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp [a]
  have hunit_b : IsUnit (1 + b) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp [b]
  have hunit_ab : IsUnit ((1 + a) * (1 + b)) := hunit_a.mul hunit_b
  refine PowerSeries.derivative.ext ?_ ?_
  · rw [PowerSeries.derivative_subst A hz, map_add,
      PowerSeries.derivative_subst A ha, PowerSeries.derivative_subst A hb]
    have hda : d⁄dX A a = PowerSeries.C x := by
      simp [a]
    have hdb : d⁄dX A b = PowerSeries.C y := by
      simp [b]
    have hdz : d⁄dX A z = PowerSeries.C x * (1 + b) + (1 + a) * PowerSeries.C y := by
      simp [z, hda, hdb, map_sub, map_add]
      ring
    rw [hdz, hda, hdb]
    apply hunit_ab.mul_right_injective
    have hleft :
        ((1 + a) * (1 + b)) *
            (PowerSeries.subst z (d⁄dX A (PowerSeries.log A)) *
              (PowerSeries.C x * (1 + b) + (1 + a) * PowerSeries.C y)) =
          PowerSeries.C x * (1 + b) + (1 + a) * PowerSeries.C y := by
      calc
        ((1 + a) * (1 + b)) *
            (PowerSeries.subst z (d⁄dX A (PowerSeries.log A)) *
              (PowerSeries.C x * (1 + b) + (1 + a) * PowerSeries.C y))
            =
          (PowerSeries.subst z (d⁄dX A (PowerSeries.log A)) * ((1 + a) * (1 + b))) *
            (PowerSeries.C x * (1 + b) + (1 + a) * PowerSeries.C y) := by
            ring
        _ = PowerSeries.C x * (1 + b) + (1 + a) * PowerSeries.C y := by
            rw [hgeom_z, one_mul]
    have hright :
        ((1 + a) * (1 + b)) *
            (PowerSeries.subst a (d⁄dX A (PowerSeries.log A)) * PowerSeries.C x +
              PowerSeries.subst b (d⁄dX A (PowerSeries.log A)) * PowerSeries.C y) =
          PowerSeries.C x * (1 + b) + (1 + a) * PowerSeries.C y := by
      calc
        ((1 + a) * (1 + b)) *
            (PowerSeries.subst a (d⁄dX A (PowerSeries.log A)) * PowerSeries.C x +
              PowerSeries.subst b (d⁄dX A (PowerSeries.log A)) * PowerSeries.C y)
            =
          (PowerSeries.subst a (d⁄dX A (PowerSeries.log A)) * (1 + a)) *
              (PowerSeries.C x * (1 + b)) +
            (PowerSeries.subst b (d⁄dX A (PowerSeries.log A)) * (1 + b)) *
              ((1 + a) * PowerSeries.C y) := by
            ring
        _ = PowerSeries.C x * (1 + b) + (1 + a) * PowerSeries.C y := by
            rw [hgeom_a, hgeom_b]
            ring
    exact hleft.trans hright.symm
  · have hz0 :
        PowerSeries.constantCoeff
            (PowerSeries.subst z (PowerSeries.log A)) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero hz0 _ PowerSeries.constantCoeff_log
    have ha0 :
        PowerSeries.constantCoeff
            (PowerSeries.subst a (PowerSeries.log A)) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero ha0 _ PowerSeries.constantCoeff_log
    have hb0 :
        PowerSeries.constantCoeff
            (PowerSeries.subst b (PowerSeries.log A)) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero hb0 _ PowerSeries.constantCoeff_log
    simp [z, a, b, hz0, ha0, hb0]

/-- Expanded form of `log_subst_mul_one_add_scaled`.

The argument of the left logarithm is `T*x + T*y + T^2*x*y`, the principal-unit
coordinate of `(1+T*x)*(1+T*y)`. -/
theorem log_subst_add_add_mul_scaled [IsAddTorsionFree A] (x y : A) :
    PowerSeries.subst
        (PowerSeries.X * PowerSeries.C x + PowerSeries.X * PowerSeries.C y +
          PowerSeries.X ^ 2 * PowerSeries.C (x * y))
        (PowerSeries.log A) =
      PowerSeries.subst (PowerSeries.X * PowerSeries.C x) (PowerSeries.log A) +
        PowerSeries.subst (PowerSeries.X * PowerSeries.C y) (PowerSeries.log A) := by
  have harg :
      (1 + PowerSeries.X * PowerSeries.C x) *
            (1 + PowerSeries.X * PowerSeries.C y) - 1 =
        PowerSeries.X * PowerSeries.C x + PowerSeries.X * PowerSeries.C y +
          PowerSeries.X ^ 2 * PowerSeries.C (x * y) := by
    rw [pow_two, map_mul]
    ring
  rw [← harg]
  exact log_subst_mul_one_add_scaled (A := A) x y

/-- Coefficient extraction from the scaled two-variable formal logarithm
identity.  The coefficient of `T^n` is the homogeneous total-degree `n` part
of the identity in `x` and `y`. -/
theorem coeff_log_subst_add_add_mul_scaled [IsAddTorsionFree A] (x y : A) (n : ℕ) :
    PowerSeries.coeff n
        (PowerSeries.subst
          (PowerSeries.X * PowerSeries.C x + PowerSeries.X * PowerSeries.C y +
            PowerSeries.X ^ 2 * PowerSeries.C (x * y))
          (PowerSeries.log A)) =
      PowerSeries.coeff n
          (PowerSeries.subst (PowerSeries.X * PowerSeries.C x) (PowerSeries.log A)) +
        PowerSeries.coeff n
          (PowerSeries.subst (PowerSeries.X * PowerSeries.C y) (PowerSeries.log A)) := by
  rw [log_subst_add_add_mul_scaled (A := A) x y]
  simp

end FiniteLogFormal

end Furtwaengler

end BernoulliRegular

end
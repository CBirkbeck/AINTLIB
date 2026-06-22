import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# The operator `∂ = (1+T)·d/dT` on power series

RJW (arXiv:2309.15692) Lem. 3.24: on `R⟦T⟧` (for any commutative ring `R`) the operator
`∂ = (1+T) d/dT` underlies the action of "multiplication by `x`" on Mahler transforms.

`PowerSeries.derivativeFun` (`Mathlib.RingTheory.PowerSeries.Derivative`) is defined for any
`[CommRing R]`, so the operator itself is generic. This file holds the single shared definition
and its basic coefficient / functoriality API; every `p`-adic specialisation in the project
routes through it.
-/

open PowerSeries

namespace PadicLFunctions

variable {R : Type*} [CommRing R]

/-- The operator `∂ = (1+T)·d/dT` on `R⟦T⟧` (RJW Lem. 3.24). -/
noncomputable def del (F : PowerSeries R) : PowerSeries R :=
  (1 + PowerSeries.X) * F.derivativeFun

lemma del_def (F : PowerSeries R) : del F = (1 + PowerSeries.X) * F.derivativeFun := rfl

/-- The coefficients of `∂F`: `(∂F)_n = (n+1)·F_{n+1} + n·F_n` (RJW TeX 1066–1075). -/
lemma coeff_del (F : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (del F)
      = (n + 1 : R) * PowerSeries.coeff (n + 1) F + (n : R) * PowerSeries.coeff n F := by
  rw [del, one_add_mul, map_add, coeff_derivativeFun]
  rcases n with - | m
  · rw [coeff_zero_X_mul]
    push_cast
    ring
  · rw [coeff_succ_X_mul, coeff_derivativeFun]
    push_cast
    ring

/-- `PowerSeries.map` commutes with `derivativeFun` (coefficient-wise). -/
lemma map_derivativeFun {S : Type*} [CommRing S] (f : R →+* S) (F : PowerSeries R) :
    PowerSeries.map f F.derivativeFun = (PowerSeries.map f F).derivativeFun := by
  ext n
  simp [coeff_derivativeFun]

/-- A ring map intertwines `∂`. -/
lemma map_del {S : Type*} [CommRing S] (f : R →+* S) (F : PowerSeries R) :
    PowerSeries.map f (del F) = del (PowerSeries.map f F) := by
  rw [del, del, map_mul, map_add, map_one, PowerSeries.map_X, map_derivativeFun]

/-- `∂` commutes with iteration through a ring map. -/
lemma map_del_iterate {S : Type*} [CommRing S] (f : R →+* S) (k : ℕ) (F : PowerSeries R) :
    PowerSeries.map f (del^[k] F) = del^[k] (PowerSeries.map f F) := by
  induction k generalizing F with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_del, ih]

end PadicLFunctions

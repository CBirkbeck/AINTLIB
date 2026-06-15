module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerArtinHasseTeichmuller
public import BernoulliRegular.Reflection.SingularKummer.LocalizationKernel.Part1

/-!
# Global lambda decomposition for the Kummer--Artin--Hasse correction

The full explicit local correction is only consumed by the global product
formula on elements of `Kˣ`.  This file gives the decomposition API for those
global field units at the distinguished cyclotomic prime:

* normalize by the explicit uniformizer `pi = zeta_p - 1`;
* convert the resulting lambda-local unit into the localized ring and then
  into the completed local unit group;
* split the completed unit into its Teichmuller residue factor and a
  principal-unit factor.

This avoids assuming that the adic completed integer ring is already known to
Lean as a DVR.
-/

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors WithZero
open NumberField IsCyclotomicExtension IsDedekindDomain

namespace BernoulliRegular

open Reflection.SingularKummer.SingularPair

namespace Furtwaengler
namespace KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The global integral cyclotomic uniformizer `pi = zeta_p - 1`. -/
def lambdaPiIntegral
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    𝓞 K :=
  (zeta_spec p ℚ K).toInteger - 1

@[simp]
theorem lambdaPiIntegral_ne_zero
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    lambdaPiIntegral p K ≠ 0 := by
  change (zeta_spec p ℚ K).toInteger - 1 ≠ 0
  exact (zeta_spec p ℚ K).zeta_sub_one_prime'.ne_zero

/-- The explicit cyclotomic uniformizer as a global field unit. -/
def lambdaPiFieldUnit
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    Kˣ :=
  Units.mk0 (algebraMap (𝓞 K) K (lambdaPiIntegral p K))
    ((FaithfulSMul.algebraMap_injective (𝓞 K) K).ne
      (lambdaPiIntegral_ne_zero (p := p) (K := K)))

@[simp]
theorem lambdaPiFieldUnit_val
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    (lambdaPiFieldUnit p K : K) =
      algebraMap (𝓞 K) K (lambdaPiIntegral p K) :=
  rfl

/-- The distinguished lambda prime as a height-one prime. -/
abbrev lambdaHeightOne
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    HeightOneSpectrum (𝓞 K) :=
  Reflection.SingularKummer.SingularPair.cyclotomicLambdaHeightOne (p := p) K

/-- The explicit cyclotomic uniformizer has normalized lambda valuation
`exp (-1)`. -/
theorem lambdaPiFieldUnit_valuation
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    (lambdaHeightOne p K).valuation K (lambdaPiFieldUnit p K : K) =
      WithZero.exp (-1 : ℤ) := by
  rw [lambdaPiFieldUnit_val]
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  have hspan :
      (lambdaHeightOne p K).asIdeal =
        Ideal.span ({lambdaPiIntegral p K} : Set (𝓞 K)) := rfl
  exact (lambdaHeightOne p K).intValuation_singleton
    (lambdaPiIntegral_ne_zero (p := p) (K := K)) hspan

/-- The lambda valuation exponent of a global field unit, normalized so that
dividing by `pi^exponent` leaves a lambda-local unit. -/
def lambdaGlobalExponent
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (x : Kˣ) : ℤ :=
  -(((lambdaHeightOne p K).valuation K (x : K)).log)

theorem lambdaPiFieldUnit_zpow_valuation_eq
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (x : Kˣ) :
    (lambdaHeightOne p K).valuation K
        ((lambdaPiFieldUnit p K ^ lambdaGlobalExponent p K x : Kˣ) : K) =
      (lambdaHeightOne p K).valuation K (x : K) := by
  have hxv : (lambdaHeightOne p K).valuation K (x : K) ≠ 0 :=
    (Valuation.ne_zero_iff ((lambdaHeightOne p K).valuation K)).2 x.ne_zero
  have hden_ne :
      (lambdaHeightOne p K).valuation K
          ((lambdaPiFieldUnit p K ^ lambdaGlobalExponent p K x : Kˣ) : K) ≠ 0 :=
    (Valuation.ne_zero_iff ((lambdaHeightOne p K).valuation K)).2
      (Units.ne_zero (lambdaPiFieldUnit p K ^ lambdaGlobalExponent p K x))
  rw [← WithZero.exp_log hden_ne, ← WithZero.exp_log hxv]
  apply congrArg WithZero.exp
  rw [Units.val_zpow_eq_zpow_val]
  rw [map_zpow₀]
  rw [lambdaPiFieldUnit_valuation]
  rw [WithZero.log_zpow, WithZero.log_exp]
  unfold lambdaGlobalExponent
  ring

/-- Normalize a global field unit to a lambda-local unit using the explicit
uniformizer `zeta_p - 1`. -/
def lambdaGlobalNormalizedUnit
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (x : Kˣ) :
    Reflection.SingularKummer.SingularPair.cyclotomicLocalUnitSubgroup
      (p := p) K :=
  ⟨x / (lambdaPiFieldUnit p K) ^ lambdaGlobalExponent p K x, by
    rw [Reflection.SingularKummer.SingularPair.mem_localUnitSubgroupAt_iff]
    have hxv : (lambdaHeightOne p K).valuation K (x : K) ≠ 0 :=
      (Valuation.ne_zero_iff ((lambdaHeightOne p K).valuation K)).2 x.ne_zero
    rw [Units.val_div_eq_div_val, map_div₀,
      lambdaPiFieldUnit_zpow_valuation_eq (p := p) (K := K) x]
    exact div_self hxv⟩

/-- Global unit decomposition into the explicit lambda-uniformizer part and
the normalized lambda-local unit. -/
theorem lambdaPi_zpow_mul_normalizedUnit
    (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (x : Kˣ) :
    lambdaPiFieldUnit p K ^ lambdaGlobalExponent p K x *
      (lambdaGlobalNormalizedUnit p K x : Kˣ) = x := by
  change lambdaPiFieldUnit p K ^ lambdaGlobalExponent p K x *
      (x / lambdaPiFieldUnit p K ^ lambdaGlobalExponent p K x) = x
  rw [div_eq_mul_inv, ← mul_assoc,
    mul_comm (lambdaPiFieldUnit p K ^ lambdaGlobalExponent p K x) x,
    mul_assoc, mul_inv_cancel, mul_one]

/-- The normalized global unit represented as an actual localized-ring unit. -/
def lambdaGlobalLocalCyclotomicUnit
    (x : Kˣ) : Reflection.Local.localCyclotomicUnitGroup p K :=
  Reflection.SingularKummer.SingularPair.cyclotomicLocalUnitSubgroupToLocalCyclotomicUnitHom
    (p := p) (K := K) (lambdaGlobalNormalizedUnit p K x)

@[simp]
theorem localCyclotomicRingToField_lambdaGlobalLocalCyclotomicUnit
    (x : Kˣ) :
    Reflection.SingularKummer.SingularPair.localCyclotomicRingToField p K
        (lambdaGlobalLocalCyclotomicUnit p K x :
          Reflection.Local.localCyclotomicRing p K) =
      ((lambdaGlobalNormalizedUnit p K x : Kˣ) : K) := by
  let h :=
    localCyclotomicRingToField_cyclotomicLocalUnitSubgroupToLocalCyclotomicUnit
      (p := p) (K := K) (lambdaGlobalNormalizedUnit p K x)
  exact h

/-- The completed local unit attached to a global field unit after removing
its explicit lambda-uniformizer part. -/
def lambdaGlobalCompletedUnit
    (x : Kˣ) : LambdaUnitGroup p K :=
  Reflection.Local.completedLocalCyclotomicUnitMap p K
    (lambdaGlobalLocalCyclotomicUnit p K x)

/-- Principal-unit part after splitting off the Teichmuller residue lift. -/
def lambdaTeichmullerPrincipalUnitPart
    (u : LambdaUnitGroup p K) : LambdaPrincipalUnitSubgroup p K 1 :=
  ⟨u * (lambdaTeichmullerUnitLift p K (lambdaCompletedUnitResidue p K u))⁻¹, by
    refine (mem_principalUnits_one_iff_completedResidue_eq_one (p := p) (K := K) _).2 ?_
    rw [map_mul, map_inv, lambdaTeichmullerUnitLift_residue]
    simp⟩

@[simp]
theorem lambdaTeichmullerPrincipalUnitPart_val
    (u : LambdaUnitGroup p K) :
    (lambdaTeichmullerPrincipalUnitPart p K u : LambdaUnitGroup p K) =
      u * (lambdaTeichmullerUnitLift p K (lambdaCompletedUnitResidue p K u))⁻¹ :=
  rfl

/-- Completed-unit decomposition using the Teichmuller residue lift. -/
theorem lambdaTeichmullerLift_mul_principalUnitPart
    (u : LambdaUnitGroup p K) :
    lambdaTeichmullerUnitLift p K (lambdaCompletedUnitResidue p K u) *
        (lambdaTeichmullerPrincipalUnitPart p K u : LambdaUnitGroup p K) = u := by
  rw [lambdaTeichmullerPrincipalUnitPart_val]
  rw [mul_comm u (lambdaTeichmullerUnitLift p K (lambdaCompletedUnitResidue p K u))⁻¹,
    ← mul_assoc, mul_inv_cancel, one_mul]

/-- The Teichmuller factor attached to a global field unit. -/
def lambdaGlobalTeichmullerFactor
    (x : Kˣ) : LambdaUnitGroup p K :=
  lambdaTeichmullerUnitLift p K
    (lambdaCompletedUnitResidue p K (lambdaGlobalCompletedUnit p K x))

/-- The principal-unit factor attached to a global field unit. -/
def lambdaGlobalPrincipalUnitPart
    (x : Kˣ) : LambdaPrincipalUnitSubgroup p K 1 :=
  lambdaTeichmullerPrincipalUnitPart p K (lambdaGlobalCompletedUnit p K x)

/-- Completed decomposition of the local unit attached to a global field unit:
Teichmuller residue factor times principal-unit factor. -/
theorem lambdaGlobalTeichmuller_mul_principalUnitPart
    (x : Kˣ) :
    lambdaGlobalTeichmullerFactor p K x *
        (lambdaGlobalPrincipalUnitPart p K x : LambdaUnitGroup p K) =
      lambdaGlobalCompletedUnit p K x := by
  simp [lambdaGlobalTeichmullerFactor, lambdaGlobalPrincipalUnitPart]

/-- The global Teichmuller residue factor is invisible modulo `p`-th powers. -/
theorem lambdaGlobalTeichmullerFactor_mem_powMonoidHom_range
    (x : Kˣ) :
    lambdaGlobalTeichmullerFactor p K x ∈
      (powMonoidHom p : LambdaUnitGroup p K →* LambdaUnitGroup p K).range :=
  lambdaTeichmullerUnitLift_mem_powMonoidHom_range (p := p) (K := K)
    (lambdaCompletedUnitResidue p K (lambdaGlobalCompletedUnit p K x))

end KummerArtinHasse
end Furtwaengler
end BernoulliRegular

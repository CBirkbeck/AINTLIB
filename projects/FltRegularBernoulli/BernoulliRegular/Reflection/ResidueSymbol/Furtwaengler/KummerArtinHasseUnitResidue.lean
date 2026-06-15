module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerArtinHasseLocalModel

/-!
# Residue splitting for completed local units

This file proves the first, purely algebraic, part of the local decomposition
needed by the Kummer--Artin--Hasse formula.  A completed local unit has a
residue in the residue field at `lambda`; after choosing a lift of that
residue from the uncompleted local unit group and mapping it into the
completion, the quotient is a completed principal unit.

This is not yet the Teichmuller finite-order lift.  It is only the residue
splitting that the later Teichmuller construction must refine.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace Furtwaengler
namespace KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The residue ring of the local cyclotomic ring at `lambda`.

This is definitionally the residue field of the uncompleted local ring.  We
use the uncompleted residue ring as target because the completed ring maps to
it through `AdicCompletion.evalOneₐ`. -/
abbrev LambdaResidueRing : Type _ :=
  Reflection.Local.localCyclotomicRing p K ⧸
    Reflection.Local.localCyclotomicMaximalIdeal p K

/-- The nonzero residue classes, written as units of the residue ring. -/
abbrev LambdaResidueUnitGroup : Type _ :=
  (LambdaResidueRing p K)ˣ

/-- Residue map on uncompleted local units. -/
noncomputable def lambdaLocalUnitResidue :
    Reflection.Local.localCyclotomicUnitGroup p K →*
      LambdaResidueUnitGroup p K :=
  Units.map (Ideal.Quotient.mk (Reflection.Local.localCyclotomicMaximalIdeal p K)).toMonoidHom

/-- Residue map on completed local units, via the first quotient of the adic
completion. -/
noncomputable def lambdaCompletedUnitResidue :
    LambdaUnitGroup p K →* LambdaResidueUnitGroup p K :=
  Units.map
    (AdicCompletion.evalOneₐ
      (Reflection.Local.localCyclotomicMaximalIdeal p K)).toMonoidHom

theorem lambdaLocalUnitResidue_surjective :
    Function.Surjective (lambdaLocalUnitResidue p K) := by
  let R := Reflection.Local.localCyclotomicRing p K
  let M := Reflection.Local.localCyclotomicMaximalIdeal p K
  have hsurj :
      Function.Surjective
        (Units.map (IsLocalRing.residue R).toMonoidHom :
          Rˣ →* (IsLocalRing.ResidueField R)ˣ) :=
    IsLocalRing.surjective_units_map_of_local_ringHom
      (IsLocalRing.residue R) IsLocalRing.residue_surjective inferInstance
  exact hsurj

@[simp]
theorem lambdaCompletedUnitResidue_completedLocalCyclotomicUnitMap
    (u : Reflection.Local.localCyclotomicUnitGroup p K) :
    lambdaCompletedUnitResidue p K
        (Reflection.Local.completedLocalCyclotomicUnitMap p K u) =
      lambdaLocalUnitResidue p K u := by
  ext
  simp [lambdaCompletedUnitResidue, lambdaLocalUnitResidue,
    Reflection.Local.completedLocalCyclotomicUnitMap]

theorem mem_principalUnits_one_iff_completedResidue_eq_one
    (u : LambdaUnitGroup p K) :
    u ∈ LambdaPrincipalUnitSubgroup p K 1 ↔
      lambdaCompletedUnitResidue p K u = 1 := by
  let R := Reflection.Local.localCyclotomicRing p K
  let S := LambdaLocalIntegerRing p K
  let M := Reflection.Local.localCyclotomicMaximalIdeal p K
  let Mhat := LambdaMaximalIdeal p K
  constructor
  · intro hu
    apply Units.ext
    rw [Reflection.Local.mem_completedPrincipalUnitSubgroup_iff] at hu
    rw [pow_one] at hu
    have hzero :
        AdicCompletion.evalOneₐ M ((u : S) - 1) = 0 := by
      have hker : (u : S) - 1 ∈
          RingHom.ker (AdicCompletion.evalOneₐ M).toRingHom := by
        rw [← Reflection.Local.completedLocalCyclotomicMaximalIdeal_eq_ker_evalOne
          (p := p) (K := K)]
        simpa [S, Mhat] using hu
      exact hker
    change AdicCompletion.evalOneₐ M (u : S) = 1
    rw [map_sub, map_one] at hzero
    exact sub_eq_zero.mp hzero
  · intro h
    rw [Reflection.Local.mem_completedPrincipalUnitSubgroup_iff]
    rw [pow_one]
    have hval : AdicCompletion.evalOneₐ M (u : S) = 1 :=
      congrArg Units.val h
    have hzero :
        AdicCompletion.evalOneₐ M ((u : S) - 1) = 0 := by
      rw [map_sub, hval, map_one, sub_self]
    have hker : (u : S) - 1 ∈
        RingHom.ker (AdicCompletion.evalOneₐ M).toRingHom := hzero
    rw [Reflection.Local.completedLocalCyclotomicMaximalIdeal_eq_ker_evalOne
      (p := p) (K := K)]
    simpa [S, Mhat] using hker

/-- A chosen uncompleted local-unit lift of a nonzero residue class. -/
noncomputable def lambdaResidueUnitLocalLift
    (a : LambdaResidueUnitGroup p K) :
    Reflection.Local.localCyclotomicUnitGroup p K :=
  Classical.choose (lambdaLocalUnitResidue_surjective p K a)

@[simp]
theorem lambdaResidueUnitLocalLift_residue
    (a : LambdaResidueUnitGroup p K) :
    lambdaLocalUnitResidue p K (lambdaResidueUnitLocalLift p K a) = a :=
  Classical.choose_spec (lambdaLocalUnitResidue_surjective p K a)

/-- The chosen completed unit lift of a nonzero residue class. -/
noncomputable def lambdaResidueUnitLift
    (a : LambdaResidueUnitGroup p K) : LambdaUnitGroup p K :=
  Reflection.Local.completedLocalCyclotomicUnitMap p K
    (lambdaResidueUnitLocalLift p K a)

@[simp]
theorem lambdaResidueUnitLift_residue
    (a : LambdaResidueUnitGroup p K) :
    lambdaCompletedUnitResidue p K (lambdaResidueUnitLift p K a) = a := by
  simp [lambdaResidueUnitLift]

/-- The principal-unit part of a completed unit after splitting off a chosen
residue-unit lift. -/
noncomputable def lambdaPrincipalUnitPart
    (u : LambdaUnitGroup p K) : LambdaPrincipalUnitSubgroup p K 1 :=
  ⟨u * (lambdaResidueUnitLift p K (lambdaCompletedUnitResidue p K u))⁻¹, by
    refine (mem_principalUnits_one_iff_completedResidue_eq_one (p := p) (K := K) _).2 ?_
    rw [map_mul, map_inv, lambdaResidueUnitLift_residue]
    simp⟩

@[simp]
theorem lambdaPrincipalUnitPart_val
    (u : LambdaUnitGroup p K) :
    (lambdaPrincipalUnitPart p K u : LambdaUnitGroup p K) =
      u * (lambdaResidueUnitLift p K (lambdaCompletedUnitResidue p K u))⁻¹ :=
  rfl

/-- Completed-unit residue splitting: a unit is the chosen residue lift times
its principal-unit part. -/
theorem lambdaResidueLift_mul_principalUnitPart
    (u : LambdaUnitGroup p K) :
    lambdaResidueUnitLift p K (lambdaCompletedUnitResidue p K u) *
        (lambdaPrincipalUnitPart p K u : LambdaUnitGroup p K) = u := by
  rw [lambdaPrincipalUnitPart_val]
  rw [mul_comm u (lambdaResidueUnitLift p K (lambdaCompletedUnitResidue p K u))⁻¹,
    ← mul_assoc, mul_inv_cancel, one_mul]

end KummerArtinHasse
end Furtwaengler
end BernoulliRegular

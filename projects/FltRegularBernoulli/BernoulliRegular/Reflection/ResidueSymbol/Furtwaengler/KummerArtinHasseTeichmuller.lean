module

public import Mathlib.RingTheory.Teichmuller
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.KummerArtinHasseUnitResidue

/-!
# Teichmüller residue-unit lifts at `lambda`

This file replaces the arbitrary residue lifts from
`KummerArtinHasseUnitResidue` by adic Teichmüller lifts in the completed
local integer ring.  This is the second piece of the explicit local
decomposition used by the Kummer--Artin--Hasse correction:

* identify the completed first residue quotient with the uncompleted residue
  quotient already used by the unit-residue map;
* construct the Teichmüller lift of each nonzero residue class;
* prove its residue and finite-order equations.

The construction uses `Perfection.teichmuller₀` and stays in the explicit
local model.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace Furtwaengler
namespace KummerArtinHasse

-- The completed residue quotient instances expand through adic completion.
-- The explicit Teichmüller construction below repeatedly asks typeclass search
-- for the quotient ring structure, so this file raises the local budget.
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

theorem pow_prime_eq_self_of_pow_sub_one_eq_one
    {G : Type*} [Monoid G] (u : G) {p : ℕ}
    (hp_one : 1 ≤ p) (h : u ^ (p - 1) = 1) :
    u ^ p = u := by
  calc
    u ^ p = u ^ ((p - 1) + 1) := by rw [Nat.sub_add_cancel hp_one]
    _ = u ^ (p - 1) * u := by rw [pow_succ]
    _ = u := by rw [h, one_mul]

/-- The residue quotient of the completed local integer ring. -/
abbrev LambdaCompletedResidueRing : Type _ :=
  LambdaLocalIntegerRing p K ⧸ LambdaMaximalIdeal p K

/-- The completed first residue quotient is canonically the same as the
uncompleted residue quotient, via `AdicCompletion.evalOneₐ`. -/
noncomputable def lambdaCompletedResidueEquivLocal :
    LambdaCompletedResidueRing p K ≃+* LambdaResidueRing p K :=
  (Ideal.quotEquivOfEq
      (Reflection.Local.completedLocalCyclotomicMaximalIdeal_eq_ker_evalOne
        (p := p) (K := K))).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := (AdicCompletion.evalOneₐ
        (Reflection.Local.localCyclotomicMaximalIdeal p K)).toRingHom)
      (AdicCompletion.evalOneₐ_surjective
        (Reflection.Local.localCyclotomicMaximalIdeal p K)))

@[simp]
theorem lambdaCompletedResidueEquivLocal_mk
    (x : LambdaLocalIntegerRing p K) :
    lambdaCompletedResidueEquivLocal p K
        (Ideal.Quotient.mk (LambdaMaximalIdeal p K) x) =
      AdicCompletion.evalOneₐ
        (Reflection.Local.localCyclotomicMaximalIdeal p K) x := by
  rw [lambdaCompletedResidueEquivLocal, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

theorem lambdaCompletedResidueRing_natCard :
    Nat.card (LambdaCompletedResidueRing p K) = p :=
  (Nat.card_congr (lambdaCompletedResidueEquivLocal p K).toEquiv).trans
    (Reflection.Local.localCyclotomicResidueCard (p := p) (K := K))

instance lambdaCompletedResidueRing_finite :
    Finite (LambdaCompletedResidueRing p K) :=
  Nat.finite_of_card_ne_zero <| by
    rw [lambdaCompletedResidueRing_natCard (p := p) (K := K)]
    exact (Fact.out : Nat.Prime p).ne_zero

noncomputable instance lambdaCompletedResidueRing_fintype :
    Fintype (LambdaCompletedResidueRing p K) :=
  Fintype.ofFinite (LambdaCompletedResidueRing p K)

theorem lambdaCompletedResidueRing_card :
    Fintype.card (LambdaCompletedResidueRing p K) = p := by
  rw [← Nat.card_eq_fintype_card]
  exact lambdaCompletedResidueRing_natCard (p := p) (K := K)

instance lambdaCompletedResidueRing_charP :
    CharP (LambdaCompletedResidueRing p K) p :=
  charP_of_card_eq_prime (lambdaCompletedResidueRing_card (p := p) (K := K))

theorem lambdaCompletedResidueRing_pow_prime
    (x : LambdaCompletedResidueRing p K) :
    x ^ p = x := by
  let e : ZMod p ≃+* LambdaCompletedResidueRing p K :=
    ZMod.ringEquivOfPrime (LambdaCompletedResidueRing p K)
      (Fact.out : Nat.Prime p)
      (lambdaCompletedResidueRing_card (p := p) (K := K))
  calc
    x ^ p = e ((e.symm x) ^ p) := by
      rw [map_pow, RingEquiv.apply_symm_apply]
    _ = e (e.symm x) := by rw [ZMod.pow_card]
    _ = x := by simp

theorem lambdaCompletedResidueRing_symm_residueUnit_ne_zero
    (a : LambdaResidueUnitGroup p K) :
    (lambdaCompletedResidueEquivLocal p K).symm (a : LambdaResidueRing p K) ≠ 0 := by
  intro h
  have ha0 : (a : LambdaResidueRing p K) = 0 := by
    rw [← (lambdaCompletedResidueEquivLocal p K).apply_symm_apply
      (a : LambdaResidueRing p K), h, map_zero]
  exact a.ne_zero ha0

theorem lambdaCompletedResidueRing_symm_residueUnit_pow_sub_one
    (a : LambdaResidueUnitGroup p K) :
    ((lambdaCompletedResidueEquivLocal p K).symm (a : LambdaResidueRing p K)) ^
        (p - 1) = 1 := by
  let e : ZMod p ≃+* LambdaCompletedResidueRing p K :=
    ZMod.ringEquivOfPrime (LambdaCompletedResidueRing p K)
      (Fact.out : Nat.Prime p)
      (lambdaCompletedResidueRing_card (p := p) (K := K))
  have hc_ne :
      e.symm ((lambdaCompletedResidueEquivLocal p K).symm
        (a : LambdaResidueRing p K)) ≠ 0 := fun h =>
    lambdaCompletedResidueRing_symm_residueUnit_ne_zero (p := p) (K := K) a
      (by
        rw [← e.apply_symm_apply
          ((lambdaCompletedResidueEquivLocal p K).symm (a : LambdaResidueRing p K)),
          h, map_zero])
  calc
    ((lambdaCompletedResidueEquivLocal p K).symm (a : LambdaResidueRing p K)) ^
        (p - 1) =
      e ((e.symm ((lambdaCompletedResidueEquivLocal p K).symm
        (a : LambdaResidueRing p K))) ^ (p - 1)) := by
        rw [map_pow, RingEquiv.apply_symm_apply]
    _ = e 1 := by rw [ZMod.pow_card_sub_one_eq_one hc_ne]
    _ = 1 := by simp

/-- The constant perfection element attached to a nonzero residue class. -/
noncomputable def lambdaTeichmullerInput
    (a : LambdaResidueUnitGroup p K) :
    Perfection (LambdaCompletedResidueRing p K) p :=
  ⟨fun _ => (lambdaCompletedResidueEquivLocal p K).symm a,
    fun _ => lambdaCompletedResidueRing_pow_prime (p := p) (K := K) _⟩

theorem lambdaTeichmullerInput_pow_sub_one
    (a : LambdaResidueUnitGroup p K) :
    lambdaTeichmullerInput p K a ^ (p - 1) = 1 := by
  ext n
  exact lambdaCompletedResidueRing_symm_residueUnit_pow_sub_one (p := p) (K := K) a

/-- The Teichmüller lift in the completed local integer ring. -/
noncomputable def lambdaTeichmullerRingLift
    (a : LambdaResidueUnitGroup p K) : LambdaLocalIntegerRing p K :=
  Perfection.teichmuller₀ p (LambdaMaximalIdeal p K)
    (lambdaTeichmullerInput p K a)

@[simp]
theorem lambdaTeichmullerRingLift_residue
    (a : LambdaResidueUnitGroup p K) :
    AdicCompletion.evalOneₐ
        (Reflection.Local.localCyclotomicMaximalIdeal p K)
        (lambdaTeichmullerRingLift p K a) = a := by
  rw [← lambdaCompletedResidueEquivLocal_mk (p := p) (K := K)]
  rw [lambdaTeichmullerRingLift, Perfection.mk_teichmuller₀]
  simp [lambdaTeichmullerInput]

theorem lambdaTeichmullerRingLift_pow_sub_one
    (a : LambdaResidueUnitGroup p K) :
    lambdaTeichmullerRingLift p K a ^ (p - 1) = 1 := by
  rw [lambdaTeichmullerRingLift, ← map_pow,
    lambdaTeichmullerInput_pow_sub_one, map_one]

/-- The Teichmüller lift is a unit, as its residue is nonzero. -/
noncomputable def lambdaTeichmullerUnitLift
    (a : LambdaResidueUnitGroup p K) : LambdaUnitGroup p K :=
  (IsUnit.of_pow_eq_one
    (lambdaTeichmullerRingLift_pow_sub_one (p := p) (K := K) a)
    (by
      have hp_gt_one : 1 < p := (Fact.out : Nat.Prime p).one_lt
      omega)).unit

@[simp]
theorem lambdaTeichmullerUnitLift_val
    (a : LambdaResidueUnitGroup p K) :
    (lambdaTeichmullerUnitLift p K a : LambdaLocalIntegerRing p K) =
      lambdaTeichmullerRingLift p K a :=
  IsUnit.unit_spec _

@[simp]
theorem lambdaTeichmullerUnitLift_residue
    (a : LambdaResidueUnitGroup p K) :
    lambdaCompletedUnitResidue p K (lambdaTeichmullerUnitLift p K a) = a := by
  ext
  simp [lambdaCompletedUnitResidue]

theorem lambdaTeichmullerUnitLift_pow_sub_one
    (a : LambdaResidueUnitGroup p K) :
    lambdaTeichmullerUnitLift p K a ^ (p - 1) = 1 := by
  apply Units.ext
  change ((lambdaTeichmullerUnitLift p K a : LambdaLocalIntegerRing p K) ^ (p - 1)) = 1
  rw [lambdaTeichmullerUnitLift_val, lambdaTeichmullerRingLift_pow_sub_one]

theorem lambdaTeichmullerUnitLift_pow_prime
    (a : LambdaResidueUnitGroup p K) :
    lambdaTeichmullerUnitLift p K a ^ p = lambdaTeichmullerUnitLift p K a :=
  pow_prime_eq_self_of_pow_sub_one_eq_one
    (lambdaTeichmullerUnitLift p K a)
    (Nat.Prime.one_le (Fact.out : Nat.Prime p))
    (lambdaTeichmullerUnitLift_pow_sub_one (p := p) (K := K) a)

/-- The Teichmüller factor is a `p`-th power in the completed local unit group;
it is its own `p`-th root. -/
theorem lambdaTeichmullerUnitLift_mem_powMonoidHom_range
    (a : LambdaResidueUnitGroup p K) :
    lambdaTeichmullerUnitLift p K a ∈
      (powMonoidHom p : LambdaUnitGroup p K →* LambdaUnitGroup p K).range :=
  ⟨lambdaTeichmullerUnitLift p K a,
    lambdaTeichmullerUnitLift_pow_prime (p := p) (K := K) a⟩

/-- The Teichmüller factor has order dividing `p - 1`. -/
theorem orderOf_lambdaTeichmullerUnitLift_dvd
    (a : LambdaResidueUnitGroup p K) :
    orderOf (lambdaTeichmullerUnitLift p K a) ∣ p - 1 :=
  orderOf_dvd_of_pow_eq_one (lambdaTeichmullerUnitLift_pow_sub_one (p := p) (K := K) a)

end KummerArtinHasse
end Furtwaengler
end BernoulliRegular

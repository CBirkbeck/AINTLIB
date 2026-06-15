module

public import Mathlib.Algebra.Module.ZMod
public import BernoulliRegular.Reflection.Local.Completion

/-!
# Local principal-unit quotients

This file starts the REF-11 local unit component calculation.  It packages the
completed principal-unit quotient `completed U_1 / completed U_1^p` and its
additive `ZMod p`-module structure, using the REF-10 endpoint equality
`completed U_1^p = completed U_{p+1}`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular
namespace Reflection
namespace Local

section CyclotomicSetup

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The subgroup `completed U_1^p`, viewed inside `completed U_1`. -/
abbrev completedPrincipalUnitModPSubgroup :
    Subgroup (completedPrincipalUnitSubgroup p K 1) :=
  (completedPrincipalUnitPowerSubgroup p K p 1).subgroupOf
    (completedPrincipalUnitSubgroup p K 1)

@[simp]
theorem mem_completedPrincipalUnitModPSubgroup_iff
    {u : completedPrincipalUnitSubgroup p K 1} :
    u ∈ completedPrincipalUnitModPSubgroup p K ↔
      (u : completedLocalCyclotomicUnitGroup p K) ∈
        completedPrincipalUnitPowerSubgroup p K p 1 :=
  Iff.rfl

/-- The subgroup `completed U_{p+1}`, viewed inside `completed U_1`. -/
abbrev completedPrincipalUnitPAddOneSubgroup :
    Subgroup (completedPrincipalUnitSubgroup p K 1) :=
  (completedPrincipalUnitSubgroup p K (p + 1)).subgroupOf
    (completedPrincipalUnitSubgroup p K 1)

@[simp]
theorem mem_completedPrincipalUnitPAddOneSubgroup_iff
    {u : completedPrincipalUnitSubgroup p K 1} :
    u ∈ completedPrincipalUnitPAddOneSubgroup p K ↔
      (u : completedLocalCyclotomicUnitGroup p K) ∈
        completedPrincipalUnitSubgroup p K (p + 1) :=
  Iff.rfl

theorem completedPrincipalUnitModPSubgroup_eq_p_add_one :
    completedPrincipalUnitModPSubgroup p K =
      completedPrincipalUnitPAddOneSubgroup p K := by
  ext u
  rw [mem_completedPrincipalUnitModPSubgroup_iff,
    mem_completedPrincipalUnitPAddOneSubgroup_iff]
  rw [completedPrincipalUnitPowerSubgroup_one_eq_p_add_one (p := p) (K := K)]

/-- The completed local principal-unit mod-`p` quotient
`completed U_1 / completed U_1^p`. -/
abbrev completedPrincipalUnitModPQuotient : Type _ :=
  completedPrincipalUnitSubgroup p K 1 ⧸ completedPrincipalUnitModPSubgroup p K

/-- The quotient map `completed U_1 -> completed U_1 / completed U_1^p`. -/
def completedPrincipalUnitModPClass :
    completedPrincipalUnitSubgroup p K 1 →*
      completedPrincipalUnitModPQuotient p K :=
  QuotientGroup.mk' (completedPrincipalUnitModPSubgroup p K)

@[simp]
theorem completedPrincipalUnitModPClass_apply
    (u : completedPrincipalUnitSubgroup p K 1) :
    completedPrincipalUnitModPClass p K u = QuotientGroup.mk u :=
  rfl

/-- The completed local principal-unit quotient can equivalently be written
as `completed U_1 / completed U_{p+1}`. -/
noncomputable def completedPrincipalUnitModPQuotientEquivPAddOne :
    completedPrincipalUnitModPQuotient p K ≃*
      completedPrincipalUnitSubgroup p K 1 ⧸
        completedPrincipalUnitPAddOneSubgroup p K :=
  QuotientGroup.quotientMulEquivOfEq
    (completedPrincipalUnitModPSubgroup_eq_p_add_one (p := p) (K := K))

@[simp]
theorem completedPrincipalUnitModPQuotientEquivPAddOne_mk
    (u : completedPrincipalUnitSubgroup p K 1) :
    completedPrincipalUnitModPQuotientEquivPAddOne p K (QuotientGroup.mk u) =
      QuotientGroup.mk u :=
  rfl

/-- The quotient map kills completed `p`-th powers from `completed U_1`. -/
theorem completedPrincipalUnitModPClass_pow_eq_one
    (u : completedPrincipalUnitSubgroup p K 1) :
    completedPrincipalUnitModPClass p K (u ^ p) = 1 :=
  (QuotientGroup.eq_one_iff
    (N := completedPrincipalUnitModPSubgroup p K) (u ^ p)).2 (by
      rw [mem_completedPrincipalUnitModPSubgroup_iff]
      rw [mem_completedPrincipalUnitPowerSubgroup_iff]
      exact ⟨(u : completedLocalCyclotomicUnitGroup p K), u.2, rfl⟩)

/-- Every element of `completed U_1 / completed U_1^p` is killed by `p`. -/
theorem completedPrincipalUnitModPQuotient_pow_eq_one
    (x : completedPrincipalUnitModPQuotient p K) :
    x ^ p = 1 := by
  refine QuotientGroup.induction_on x fun u => ?_
  rw [← QuotientGroup.mk_pow]
  exact completedPrincipalUnitModPClass_pow_eq_one (p := p) (K := K) u

/-- Additive `ZMod p`-module structure on the completed local principal-unit
mod-`p` quotient. -/
instance completedPrincipalUnitModPQuotientModuleZMod :
    Module (ZMod p) (Additive (completedPrincipalUnitModPQuotient p K)) :=
  AddCommGroup.zmodModule (n := p) fun x => by
    apply Additive.ext
    rw [toMul_nsmul, toMul_zero]
    simpa using completedPrincipalUnitModPQuotient_pow_eq_one (p := p) (K := K) x.toMul

end CyclotomicSetup

end Local
end Reflection
end BernoulliRegular

end

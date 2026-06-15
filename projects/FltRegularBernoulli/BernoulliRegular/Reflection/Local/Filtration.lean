module

public import BernoulliRegular.Reflection.Local.Basic

/-!
# Principal-unit filtration API

This file proves the formal subgroup facts about the local principal-unit
filtration

```text
U_n = 1 + lambda^n O_F.
```

It is the REF-10a layer: no cyclotomic ramification calculation is used here.
The lemmas only use the local notation from `Local.Basic` and general facts
about powers of ideals and subgroups.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Ideal

section OneUnits

variable {R : Type*} [CommRing R]

/-- Congruence-one subgroups are monotone in the defining ideal. -/
theorem oneUnitsSubgroup_mono {I J : Ideal R} (hIJ : I ≤ J) :
    oneUnitsSubgroup I ≤ oneUnitsSubgroup J := by
  intro u hu
  exact hIJ hu

@[simp]
theorem oneUnitsSubgroup_top : oneUnitsSubgroup (⊤ : Ideal R) = ⊤ := by
  ext u
  simp [oneUnitsSubgroup]

end OneUnits

end Ideal

namespace Reflection
namespace Local

section CyclotomicSetup

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

@[simp]
theorem principalUnitSubgroup_zero : principalUnitSubgroup p K 0 = ⊤ := by
  simp [principalUnitSubgroup]

/-- The principal-unit filtration is antitone in the index. -/
theorem principalUnitSubgroup_mono {m n : ℕ} (h : n ≤ m) :
    principalUnitSubgroup p K m ≤ principalUnitSubgroup p K n := by
  intro u hu
  rw [mem_principalUnitSubgroup_iff] at hu ⊢
  exact Ideal.pow_le_pow_right h hu

/-- Bundled antitonicity of the principal-unit filtration. -/
theorem principalUnitSubgroup_antitone :
    Antitone (principalUnitSubgroup p K) := by
  intro n m h
  exact principalUnitSubgroup_mono (p := p) (K := K) h

/-- Successive filtration steps are nested. -/
theorem principalUnitSubgroup_succ_le (n : ℕ) :
    principalUnitSubgroup p K (n + 1) ≤ principalUnitSubgroup p K n :=
  principalUnitSubgroup_mono (p := p) (K := K) (Nat.le_succ n)

theorem mem_principalUnitSubgroup_of_le {m n : ℕ} (h : n ≤ m)
    {u : localCyclotomicUnitGroup p K}
    (hu : u ∈ principalUnitSubgroup p K m) :
    u ∈ principalUnitSubgroup p K n :=
  principalUnitSubgroup_mono (p := p) (K := K) h hu

theorem mem_principalUnitSubgroup_succ {n : ℕ}
    {u : localCyclotomicUnitGroup p K}
    (hu : u ∈ principalUnitSubgroup p K (n + 1)) :
    u ∈ principalUnitSubgroup p K n :=
  mem_principalUnitSubgroup_of_le (p := p) (K := K) (Nat.le_succ n) hu

@[simp]
theorem one_mem_principalUnitSubgroup (n : ℕ) :
    (1 : localCyclotomicUnitGroup p K) ∈ principalUnitSubgroup p K n :=
  (principalUnitSubgroup p K n).one_mem

theorem mul_mem_principalUnitSubgroup {n : ℕ}
    {u v : localCyclotomicUnitGroup p K}
    (hu : u ∈ principalUnitSubgroup p K n)
    (hv : v ∈ principalUnitSubgroup p K n) :
    u * v ∈ principalUnitSubgroup p K n :=
  (principalUnitSubgroup p K n).mul_mem hu hv

theorem inv_mem_principalUnitSubgroup {n : ℕ}
    {u : localCyclotomicUnitGroup p K}
    (hu : u ∈ principalUnitSubgroup p K n) :
    u⁻¹ ∈ principalUnitSubgroup p K n :=
  (principalUnitSubgroup p K n).inv_mem hu

theorem div_mem_principalUnitSubgroup {n : ℕ}
    {u v : localCyclotomicUnitGroup p K}
    (hu : u ∈ principalUnitSubgroup p K n)
    (hv : v ∈ principalUnitSubgroup p K n) :
    u / v ∈ principalUnitSubgroup p K n := by
  simpa [div_eq_mul_inv] using
    mul_mem_principalUnitSubgroup (p := p) (K := K) hu
      (inv_mem_principalUnitSubgroup (p := p) (K := K) hv)

theorem pow_mem_principalUnitSubgroup {n q : ℕ}
    {u : localCyclotomicUnitGroup p K}
    (hu : u ∈ principalUnitSubgroup p K n) :
    u ^ q ∈ principalUnitSubgroup p K n :=
  (principalUnitSubgroup p K n).pow_mem hu q

theorem zpow_mem_principalUnitSubgroup {n : ℕ} (q : ℤ)
    {u : localCyclotomicUnitGroup p K}
    (hu : u ∈ principalUnitSubgroup p K n) :
    u ^ q ∈ principalUnitSubgroup p K n :=
  (principalUnitSubgroup p K n).zpow_mem hu q

/-- The subgroup of `q`-th powers of `U_n`. -/
def principalUnitPowerSubgroup (q n : ℕ) :
    Subgroup (localCyclotomicUnitGroup p K) :=
  (principalUnitSubgroup p K n).map (powMonoidHom q)

@[simp]
theorem mem_principalUnitPowerSubgroup_iff {q n : ℕ}
    {u : localCyclotomicUnitGroup p K} :
    u ∈ principalUnitPowerSubgroup p K q n ↔
      ∃ v, v ∈ principalUnitSubgroup p K n ∧ v ^ q = u := by
  rfl

/-- Powers of elements of `U_n` still lie in `U_n`. -/
theorem principalUnitPowerSubgroup_le (q n : ℕ) :
    principalUnitPowerSubgroup p K q n ≤ principalUnitSubgroup p K n := by
  intro u hu
  rw [mem_principalUnitPowerSubgroup_iff] at hu
  rcases hu with ⟨v, hv, rfl⟩
  exact pow_mem_principalUnitSubgroup (p := p) (K := K) hv

/-- The `q`-th-power subgroups inherit the filtration nesting. -/
theorem principalUnitPowerSubgroup_mono {m n q : ℕ} (h : n ≤ m) :
    principalUnitPowerSubgroup p K q m ≤ principalUnitPowerSubgroup p K q n :=
  Subgroup.map_mono (principalUnitSubgroup_mono (p := p) (K := K) h)

end CyclotomicSetup

end Local
end Reflection

end BernoulliRegular

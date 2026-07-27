/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.SigmaPreservation
public import BernoulliRegular.FLT37.CyclotomicUnitsKplus
public import BernoulliRegular.HMinus.ClassNumberFormula
public import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Max-rank family of real cyclotomic units

The Sinnott / Washington Theorem 8.2 states `[(𝓞 K⁺)ˣ : C⁺] = h⁺(K)`,
where `C⁺ ⊆ (𝓞 K)ˣ` is the cyclotomic-units subgroup intersected with
real units.

To apply mathlib's `regOfFamily_div_regulator`, we need an explicit
family `u : Fin (rank K⁺) → (𝓞 K⁺)ˣ` of real cyclotomic units. The
classical choice (Washington 8.1):

  `ν_a := ζ^{1-a} · cyclotomicUnit(a)^2 = cyclotomicUnit(a) · σ(cyclotomicUnit(a))`

for `a ∈ {2, 3, ..., (p-1)/2}` (a set of cardinality `(p-3)/2 = rank K⁺`).

This file defines the family at the `(𝓞 K)ˣ` level, proves that it is σ-fixed
and belongs to `cyclotomicUnitsPlus`, and lifts it to `(𝓞 K⁺)ˣ`. The
max-rank generation claim is deferred to later steps.

This is **Step (B)** of the Sinnott / Cor 8.19 bridge construction.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

/-- The **real cyclotomic unit at index `a`**:

  `cyclotomicRealUnit a := cyclotomicUnitUnit p K a ·
    unitsComplexConj K (cyclotomicUnitUnit p K a)`

in `(𝓞 K)ˣ`. By construction, this is σ-fixed (= real). -/
def cyclotomicRealUnit {a : ℕ} (ha : a.Coprime p) (hp_two : 2 ≤ p) : (𝓞 K)ˣ :=
  cyclotomicUnitUnit p K a ha hp_two *
    unitsComplexConj K (cyclotomicUnitUnit p K a ha hp_two)

/-- σ² is the identity on units (since complex conjugation is an
involution). -/
theorem unitsComplexConj_unitsComplexConj (u : (𝓞 K)ˣ) :
    unitsComplexConj K (unitsComplexConj K u) = u := by
  apply Units.ext
  change ringOfIntegersComplexConj K
      (ringOfIntegersComplexConj K (u : 𝓞 K)) = (u : 𝓞 K)
  apply RingOfIntegers.ext
  rw [coe_ringOfIntegersComplexConj, coe_ringOfIntegersComplexConj]
  exact complexConj_apply_apply K _

/-- The real cyclotomic unit is σ-fixed: `σ(cyclotomicRealUnit a) = cyclotomicRealUnit a`. -/
theorem unitsComplexConj_cyclotomicRealUnit {a : ℕ} (ha : a.Coprime p) (hp_two : 2 ≤ p) :
    unitsComplexConj K (cyclotomicRealUnit p K ha hp_two) =
      cyclotomicRealUnit p K ha hp_two := by
  simp only [cyclotomicRealUnit]
  rw [map_mul, unitsComplexConj_unitsComplexConj, mul_comm]

/-- The real cyclotomic unit is in the cyclotomic-units subgroup. -/
theorem cyclotomicRealUnit_mem_cyclotomicUnitsSubgroup
    {a : ℕ} (ha : a.Coprime p) (ha_pos : 1 ≤ a) (ha_lt : a < p) (hp_two : 2 ≤ p) :
    cyclotomicRealUnit p K ha hp_two ∈ cyclotomicUnitsSubgroup p K hp_two := by
  simp only [cyclotomicRealUnit]
  apply Subgroup.mul_mem
  · exact cyclotomicUnitUnit_mem_cyclotomicUnitsSubgroup p K ha ha_pos ha_lt hp_two
  · exact unitsComplexConj_cyclotomicUnitUnit_mem (p := p) (K := K)
      ha ha_pos ha_lt hp_two

/-- The real cyclotomic unit is in the **real** cyclotomic-units subgroup. -/
theorem cyclotomicRealUnit_mem_cyclotomicUnitsPlus
    {a : ℕ} (ha : a.Coprime p) (ha_pos : 1 ≤ a) (ha_lt : a < p) (hp_two : 2 ≤ p) :
    cyclotomicRealUnit p K ha hp_two ∈ cyclotomicUnitsPlus p K hp_two := by
  refine ⟨cyclotomicRealUnit_mem_cyclotomicUnitsSubgroup (p := p) (K := K)
    ha ha_pos ha_lt hp_two, ?_⟩
  change cyclotomicRealUnit p K ha hp_two ∈ realUnits K
  rw [← unitsComplexConj_eq_self_iff]
  exact unitsComplexConj_cyclotomicRealUnit (p := p) (K := K) ha hp_two

/-- The set of "real cyclotomic-unit indices": `a ∈ Finset.Ico 2 ((p-1)/2 + 1)`.

Cardinality is `(p-1)/2 - 1 = (p-3)/2`, matching the unit rank of `K⁺`. -/
def cyclotomicRealUnitIndexSet : Finset ℕ := Finset.Ico 2 ((p - 1) / 2 + 1)

omit hp in
/-- For `a ∈ cyclotomicRealUnitIndexSet`, we have `1 ≤ a` and `a < p`
(needed for `cyclotomicUnitUnit p K a`). -/
theorem cyclotomicRealUnitIndexSet_bounds
    (hp_two : 2 < p) {a : ℕ} (ha : a ∈ cyclotomicRealUnitIndexSet p) :
    1 ≤ a ∧ a < p := by
  simp only [cyclotomicRealUnitIndexSet, Finset.mem_Ico] at ha
  lia

/-- For `a ∈ cyclotomicRealUnitIndexSet`, `a.Coprime p`. Since `1 ≤ a < p`
and `p` is prime, `p ∤ a`, so `a.Coprime p`. -/
theorem cyclotomicRealUnitIndexSet_coprime (hp_two : 2 < p)
    {a : ℕ} (ha : a ∈ cyclotomicRealUnitIndexSet p) :
    a.Coprime p := by
  obtain ⟨ha_pos, ha_lt⟩ := cyclotomicRealUnitIndexSet_bounds p hp_two ha
  exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr fun h ↦
    (Nat.not_le_of_lt ha_lt) (Nat.le_of_dvd ha_pos h)).symm

/-- `realCyclotomicUnitPlus p K a` is a unit in `𝓞 K⁺` when `a.Coprime p`
and `2 ≤ p`. The inverse exists in 𝓞 K and is real (σ-fixed), hence
descends to `𝓞 K⁺`. -/
theorem isUnit_realCyclotomicUnitPlus
    {a : ℕ} (ha : a.Coprime p) (_ha_lt : a < p) (hp_two : 2 ≤ p) :
    IsUnit (FLT37.realCyclotomicUnitPlus p K a) :=
  FLT37.isUnit_realCyclotomicUnitPlus p K a ha hp_two

/-- The K⁺-side real cyclotomic unit packaged as a unit. -/
noncomputable def realCyclotomicUnitPlusUnit
    {a : ℕ} (ha : a.Coprime p) (ha_lt : a < p) (hp_two : 2 ≤ p) :
    (𝓞 (NumberField.maximalRealSubfield K))ˣ :=
  (isUnit_realCyclotomicUnitPlus p K ha ha_lt hp_two).unit

/-- The value of `realCyclotomicUnitPlusUnit` is `realCyclotomicUnitPlus`. -/
@[simp]
theorem realCyclotomicUnitPlusUnit_val
    {a : ℕ} (ha : a.Coprime p) (ha_lt : a < p) (hp_two : 2 ≤ p) :
    (realCyclotomicUnitPlusUnit p K ha ha_lt hp_two :
      𝓞 (NumberField.maximalRealSubfield K)) =
    FLT37.realCyclotomicUnitPlus p K a :=
  FLT37.realCyclotomicUnitPlusUnit_val p K a ha hp_two

/-- For `i : Fin ((p-3)/2)`, the index `(i+2)` is coprime to `p` (and `< p`). -/
theorem cyclotomicUnitFamily_index_coprime (hp_three : 3 ≤ p)
    (i : Fin ((p - 3) / 2)) : ((i : ℕ) + 2).Coprime p := by
  apply cyclotomicRealUnitIndexSet_coprime p (by lia)
  simp only [cyclotomicRealUnitIndexSet, Finset.mem_Ico]
  lia

omit hp in
/-- For `i : Fin ((p-3)/2)`, the index `(i+2) < p`. -/
theorem cyclotomicUnitFamily_index_lt
    (hp_three : 3 ≤ p) (i : Fin ((p - 3) / 2)) :
    (i : ℕ) + 2 < p := by omega

/-- **The cyclotomic-unit family for K⁺**, indexed by `Fin ((p-3)/2)`.

For `i : Fin ((p-3)/2)`, returns `realCyclotomicUnitPlusUnit (i+2)`. -/
noncomputable def cyclotomicUnitFamilyKplus (hp_three : 3 ≤ p)
    (i : Fin ((p - 3) / 2)) : (𝓞 (NumberField.maximalRealSubfield K))ˣ :=
  realCyclotomicUnitPlusUnit p K
    (cyclotomicUnitFamily_index_coprime p hp_three i)
    (cyclotomicUnitFamily_index_lt p hp_three i)
    (Nat.Prime.two_le Fact.out)

/-- The cyclotomic-unit family at the `Fin (Units.rank K⁺)` index expected
by `regOfFamily_div_regulator`, via the rank identity
`Units.rank K⁺ = (p-3)/2`. -/
noncomputable def cyclotomicUnitFamilyKplusFinRank (_hp_odd : p ≠ 2)
    (hp_three : 3 ≤ p) :
    Fin (NumberField.Units.rank (NumberField.maximalRealSubfield K)) →
      (𝓞 (NumberField.maximalRealSubfield K))ˣ :=
  fun i ↦
    cyclotomicUnitFamilyKplus p K hp_three
      (i.cast ((NumberField.IsCMField.units_rank_eq_units_rank (K := K)).trans
        (BernoulliRegular.units_rank_eq_prime_sub_three_div_two (p := p) (K := K))))

/-- **Sinnott index identity (parametric)**: applying mathlib's
`regOfFamily_div_regulator` to the cyclotomic-unit family gives

  `regOfFamily(family) / regulator(K⁺) = [E⁺ : ⟨family⟩ ⊔ torsion]`.

The right-hand side is the index of the subgroup generated by the
family + torsion. To get the classical Sinnott formula
`[E⁺ : C⁺] = h⁺(K)`, one further shows that this subgroup equals
`C⁺ ⊓ realUnits K` (i.e., the family is a max-rank generating set —
Washington Theorem 8.2). -/
theorem regOfFamily_cyclotomicUnitFamilyKplus_div_regulator (hp_odd : p ≠ 2)
    (hp_three : 3 ≤ p) :
    NumberField.Units.regOfFamily
        (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) /
      NumberField.Units.regulator (NumberField.maximalRealSubfield K) =
    ((Subgroup.closure
        (Set.range (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ⊔
      NumberField.Units.torsion (NumberField.maximalRealSubfield K)).index
      : ℝ) :=
  NumberField.Units.regOfFamily_div_regulator
    (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)

end Sinnott

end FLT37

end BernoulliRegular

end

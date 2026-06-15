import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.SigmaPreservation
import BernoulliRegular.FLT37.CyclotomicUnitsKplus
import BernoulliRegular.HMinus.ClassNumberFormula
import Mathlib.NumberTheory.NumberField.Units.Regulator


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

This file defines the family at the `(𝓞 K)ˣ` level (σ-fixed, hence real)
and verifies its membership in `cyclotomicUnitsPlus`. The lift to
`(𝓞 K⁺)ˣ` and the max-rank claim are deferred to later steps.

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

set_option backward.isDefEq.respectTransparency false in
/-- The **real cyclotomic unit at index `a`**:

  `cyclotomicRealUnit a := cyclotomicUnitUnit p K a ·
    unitsComplexConj K (cyclotomicUnitUnit p K a)`

in `(𝓞 K)ˣ`. By construction, this is σ-fixed (= real). -/
def cyclotomicRealUnit {a : ℕ} (ha : a.Coprime p) (hp_two : 2 ≤ p) : (𝓞 K)ˣ :=
  cyclotomicUnitUnit p K a ha hp_two *
    unitsComplexConj K (cyclotomicUnitUnit p K a ha hp_two)

set_option backward.isDefEq.respectTransparency false in
/-- σ² is the identity on units (since complex conjugation is an
involution). -/
theorem unitsComplexConj_unitsComplexConj (u : (𝓞 K)ˣ) :
    unitsComplexConj K (unitsComplexConj K u) = u := by
  apply Units.ext
  change ringOfIntegersComplexConj K
      (ringOfIntegersComplexConj K (u : 𝓞 K)) = (u : 𝓞 K)
  apply RingOfIntegers.ext
  change ((ringOfIntegersComplexConj K
      (ringOfIntegersComplexConj K (u : 𝓞 K))) : K) = ((u : 𝓞 K) : K)
  rw [coe_ringOfIntegersComplexConj, coe_ringOfIntegersComplexConj]
  exact complexConj_apply_apply K _

set_option backward.isDefEq.respectTransparency false in
/-- The real cyclotomic unit is σ-fixed: `σ(cyclotomicRealUnit a) = cyclotomicRealUnit a`. -/
theorem unitsComplexConj_cyclotomicRealUnit {a : ℕ} (ha : a.Coprime p) (hp_two : 2 ≤ p) :
    unitsComplexConj K (cyclotomicRealUnit p K ha hp_two) =
      cyclotomicRealUnit p K ha hp_two := by
  unfold cyclotomicRealUnit
  rw [map_mul, unitsComplexConj_unitsComplexConj, mul_comm]

set_option backward.isDefEq.respectTransparency false in
/-- The real cyclotomic unit is in the cyclotomic-units subgroup. -/
theorem cyclotomicRealUnit_mem_cyclotomicUnitsSubgroup
    {a : ℕ} (ha : a.Coprime p) (ha_pos : 1 ≤ a) (ha_lt : a < p) (hp_two : 2 ≤ p) :
    cyclotomicRealUnit p K ha hp_two ∈ cyclotomicUnitsSubgroup p K hp_two := by
  unfold cyclotomicRealUnit
  apply Subgroup.mul_mem
  · exact cyclotomicUnitUnit_mem_cyclotomicUnitsSubgroup p K ha ha_pos ha_lt hp_two
  · exact unitsComplexConj_cyclotomicUnitUnit_mem (p := p) (K := K)
      ha ha_pos ha_lt hp_two

set_option backward.isDefEq.respectTransparency false in
/-- The real cyclotomic unit is in the **real** cyclotomic-units subgroup. -/
theorem cyclotomicRealUnit_mem_cyclotomicUnitsPlus
    {a : ℕ} (ha : a.Coprime p) (ha_pos : 1 ≤ a) (ha_lt : a < p) (hp_two : 2 ≤ p) :
    cyclotomicRealUnit p K ha hp_two ∈ cyclotomicUnitsPlus p K hp_two := by
  refine ⟨cyclotomicRealUnit_mem_cyclotomicUnitsSubgroup (p := p) (K := K)
    ha ha_pos ha_lt hp_two, ?_⟩
  change cyclotomicRealUnit p K ha hp_two ∈ realUnits K
  rw [← unitsComplexConj_eq_self_iff]
  exact unitsComplexConj_cyclotomicRealUnit (p := p) (K := K) ha hp_two

/-! ## Indexed family of real cyclotomic units

The standard family is indexed by `a ∈ {2, 3, ..., (p-1)/2}` (cardinality
`(p-3)/2 = rank K⁺`). Using a Fin-typed index lets us apply mathlib's
`regOfFamily_div_regulator`. -/

set_option backward.isDefEq.respectTransparency false in
/-- The set of "real cyclotomic-unit indices": `a ∈ Finset.Ico 2 ((p-1)/2 + 1)`.

Cardinality is `(p-1)/2 - 1 = (p-3)/2`, matching the unit rank of `K⁺`. -/
def cyclotomicRealUnitIndexSet : Finset ℕ := Finset.Ico 2 ((p - 1) / 2 + 1)

set_option backward.isDefEq.respectTransparency false in
omit hp in
/-- For `a ∈ cyclotomicRealUnitIndexSet`, we have `1 ≤ a` and `a < p`
(needed for `cyclotomicUnitUnit p K a`). -/
theorem cyclotomicRealUnitIndexSet_bounds
    (hp_two : 2 < p) {a : ℕ} (ha : a ∈ cyclotomicRealUnitIndexSet p) :
    1 ≤ a ∧ a < p := by
  unfold cyclotomicRealUnitIndexSet at ha
  rw [Finset.mem_Ico] at ha
  refine ⟨by omega, ?_⟩
  -- a ≤ (p-1)/2 < p for p ≥ 3.
  have h1 : a ≤ (p - 1) / 2 := by omega
  have h2 : (p - 1) / 2 < p := by omega
  omega

set_option backward.isDefEq.respectTransparency false in
/-- For `a ∈ cyclotomicRealUnitIndexSet`, `a.Coprime p`. Since `1 ≤ a < p`
and `p` is prime, `p ∤ a`, so `a.Coprime p`. -/
theorem cyclotomicRealUnitIndexSet_coprime (hp_two : 2 < p)
    {a : ℕ} (ha : a ∈ cyclotomicRealUnitIndexSet p) :
    a.Coprime p := by
  obtain ⟨ha_pos, ha_lt⟩ := cyclotomicRealUnitIndexSet_bounds p hp_two ha
  -- p prime + 1 ≤ a < p ⟹ ¬p ∣ a ⟹ p.Coprime a ⟹ a.Coprime p.
  have hp_prime : Nat.Prime p := Fact.out
  have h_not_dvd : ¬ p ∣ a := fun h => by
    have := Nat.le_of_dvd ha_pos h
    omega
  exact (hp_prime.coprime_iff_not_dvd.mpr h_not_dvd).symm

/-! ## Unit-form K⁺ cyclotomic units and Fin-indexed family -/

set_option backward.isDefEq.respectTransparency false in
/-- `realCyclotomicUnitPlus p K a` is a unit in `𝓞 K⁺` when `a.Coprime p`
and `2 ≤ p`. The inverse exists in 𝓞 K and is real (σ-fixed), hence
descends to `𝓞 K⁺`. -/
theorem isUnit_realCyclotomicUnitPlus
    {a : ℕ} (ha : a.Coprime p) (_ha_lt : a < p) (hp_two : 2 ≤ p) :
    IsUnit (FLT37.realCyclotomicUnitPlus p K a) := by
  -- The K-side unit form has σ-fixed inverse, descending to 𝓞 K⁺.
  have h_real_unit : ∃ inv_u : (𝓞 K)ˣ,
      unitsComplexConj K inv_u = inv_u ∧
      ((cyclotomicRealUnit p K ha hp_two : (𝓞 K)ˣ) *
        inv_u : (𝓞 K)ˣ) = 1 := by
    refine ⟨(cyclotomicRealUnit p K ha hp_two)⁻¹, ?_, mul_inv_cancel _⟩
    rw [map_inv]
    exact congrArg (·⁻¹)
      (unitsComplexConj_cyclotomicRealUnit (p := p) (K := K) ha hp_two)
  obtain ⟨inv_u, h_inv_real, h_mul⟩ := h_real_unit
  -- inv_u ∈ realUnits K → descends to 𝓞 K⁺ via mem_realUnits_iff.
  have h_inv_mem : inv_u ∈ realUnits K := by
    rw [← unitsComplexConj_eq_self_iff (K := K)]
    exact h_inv_real
  rw [mem_realUnits_iff (K := K)] at h_inv_mem
  obtain ⟨v_inv, hv_inv⟩ := h_inv_mem
  rw [isUnit_iff_exists]
  refine ⟨(v_inv : 𝓞 (NumberField.maximalRealSubfield K)), ?_, ?_⟩
  · apply FaithfulSMul.algebraMap_injective
      (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
    rw [map_mul, map_one, FLT37.algebraMap_realCyclotomicUnitPlus, hv_inv]
    have h_u_eq : FLT37.realCyclotomicUnit p K a =
        ((cyclotomicRealUnit p K ha hp_two : (𝓞 K)ˣ) : 𝓞 K) := by
      unfold cyclotomicRealUnit FLT37.realCyclotomicUnit
      rw [Units.val_mul, cyclotomicUnitUnit_val]
      rfl
    rw [h_u_eq, ← Units.val_mul, h_mul, Units.val_one]
  · apply FaithfulSMul.algebraMap_injective
      (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
    rw [map_mul, map_one, FLT37.algebraMap_realCyclotomicUnitPlus, hv_inv]
    have h_u_eq : FLT37.realCyclotomicUnit p K a =
        ((cyclotomicRealUnit p K ha hp_two : (𝓞 K)ˣ) : 𝓞 K) := by
      unfold cyclotomicRealUnit FLT37.realCyclotomicUnit
      rw [Units.val_mul, cyclotomicUnitUnit_val]
      rfl
    rw [h_u_eq, ← Units.val_mul]
    have h_comm : inv_u * cyclotomicRealUnit p K ha hp_two = 1 := by
      rw [mul_comm]; exact h_mul
    rw [h_comm, Units.val_one]

set_option backward.isDefEq.respectTransparency false in
/-- The K⁺-side real cyclotomic unit packaged as a unit. -/
noncomputable def realCyclotomicUnitPlusUnit
    {a : ℕ} (ha : a.Coprime p) (ha_lt : a < p) (hp_two : 2 ≤ p) :
    (𝓞 (NumberField.maximalRealSubfield K))ˣ :=
  (isUnit_realCyclotomicUnitPlus p K ha ha_lt hp_two).unit

set_option backward.isDefEq.respectTransparency false in
/-- The value of `realCyclotomicUnitPlusUnit` is `realCyclotomicUnitPlus`. -/
@[simp]
theorem realCyclotomicUnitPlusUnit_val
    {a : ℕ} (ha : a.Coprime p) (ha_lt : a < p) (hp_two : 2 ≤ p) :
    (realCyclotomicUnitPlusUnit p K ha ha_lt hp_two :
      𝓞 (NumberField.maximalRealSubfield K)) =
    FLT37.realCyclotomicUnitPlus p K a :=
  IsUnit.unit_spec _

/-! ## Fin-indexed family

The family `cyclotomicUnitFamilyKplus i := realCyclotomicUnitPlusUnit (i+2)`
for `i : Fin ((p-3)/2)`. Indexed by Fin to apply mathlib's
`regOfFamily_div_regulator`. -/

set_option backward.isDefEq.respectTransparency false in
/-- For `i : Fin ((p-3)/2)`, the index `(i+2)` is coprime to `p` (and `< p`). -/
theorem cyclotomicUnitFamily_index_coprime (hp_three : 3 ≤ p)
    (i : Fin ((p - 3) / 2)) : ((i : ℕ) + 2).Coprime p := by
  have hp_prime : Nat.Prime p := Fact.out
  have h_lt : (i : ℕ) + 2 < p := by
    have hi_lt : (i : ℕ) < (p - 3) / 2 := i.isLt
    have h_half : (p - 3) / 2 ≤ p - 3 := Nat.div_le_self _ _
    omega
  have h_pos : 1 ≤ (i : ℕ) + 2 := by omega
  -- p prime + 1 ≤ a < p ⟹ ¬p ∣ a ⟹ a.Coprime p.
  have h_not_dvd : ¬ p ∣ ((i : ℕ) + 2) := fun h => by
    have := Nat.le_of_dvd h_pos h
    omega
  exact (hp_prime.coprime_iff_not_dvd.mpr h_not_dvd).symm

set_option backward.isDefEq.respectTransparency false in
omit hp in
/-- For `i : Fin ((p-3)/2)`, the index `(i+2) < p`. -/
theorem cyclotomicUnitFamily_index_lt
    (hp_three : 3 ≤ p) (i : Fin ((p - 3) / 2)) :
    (i : ℕ) + 2 < p := by
  have hi_lt : (i : ℕ) < (p - 3) / 2 := i.isLt
  have h_half : (p - 3) / 2 ≤ p - 3 := Nat.div_le_self _ _
  omega

set_option backward.isDefEq.respectTransparency false in
/-- **The cyclotomic-unit family for K⁺**, indexed by `Fin ((p-3)/2)`.

For `i : Fin ((p-3)/2)`, returns `realCyclotomicUnitPlusUnit (i+2)`. -/
noncomputable def cyclotomicUnitFamilyKplus (hp_three : 3 ≤ p)
    (i : Fin ((p - 3) / 2)) : (𝓞 (NumberField.maximalRealSubfield K))ˣ :=
  realCyclotomicUnitPlusUnit p K
    (cyclotomicUnitFamily_index_coprime p hp_three i)
    (cyclotomicUnitFamily_index_lt p hp_three i)
    (Nat.Prime.two_le Fact.out)

/-! ## Connection to `regOfFamily_div_regulator`

The family `cyclotomicUnitFamilyKplus` lives in `Fin ((p-3)/2) → (𝓞 K⁺)ˣ`,
and the unit rank of K⁺ is `(p-3)/2` (`units_rank_eq_prime_sub_three_div_two`),
so we can package as `Fin (Units.rank K⁺) → (𝓞 K⁺)ˣ` after rewriting the
index. -/

set_option backward.isDefEq.respectTransparency false in
/-- The cyclotomic-unit family at the `Fin (Units.rank K⁺)` index expected
by `regOfFamily_div_regulator`, via the rank identity
`Units.rank K⁺ = (p-3)/2`. -/
noncomputable def cyclotomicUnitFamilyKplusFinRank (_hp_odd : p ≠ 2)
    (hp_three : 3 ≤ p) :
    Fin (NumberField.Units.rank (NumberField.maximalRealSubfield K)) →
      (𝓞 (NumberField.maximalRealSubfield K))ˣ :=
  fun i =>
    cyclotomicUnitFamilyKplus p K hp_three
      (i.cast ((NumberField.IsCMField.units_rank_eq_units_rank (K := K)).trans
        (BernoulliRegular.units_rank_eq_prime_sub_three_div_two (p := p) (K := K))))

set_option backward.isDefEq.respectTransparency false in
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

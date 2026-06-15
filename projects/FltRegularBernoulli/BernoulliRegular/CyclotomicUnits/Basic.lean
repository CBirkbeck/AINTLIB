module

public import BernoulliRegular.FLT37.PrimaryUnits

/-!
# Real cyclotomic units

This file gives the cyclotomic-unit route a stable, non-FLT37-facing name for
the standard real cyclotomic units in `K⁺`.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField

namespace BernoulliRegular

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Indices `2 ≤ a ≤ (p - 1) / 2` are automatically coprime to the prime
conductor `p`. -/
theorem realCyclotomicUnit_index_coprime {a : ℕ}
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) : a.Coprime p := by
  have hp_prime : Nat.Prime p := Fact.out
  have ha_pos : 0 < a := by omega
  have ha_lt : a < p := by
    have hhalf : (p - 1) / 2 < p := by omega
    omega
  have hnot : ¬ p ∣ a := fun hpa => by
    exact (not_le_of_gt ha_lt) (Nat.le_of_dvd ha_pos hpa)
  exact (hp_prime.coprime_iff_not_dvd.mpr hnot).symm

/-- The real cyclotomic unit in `𝓞 K⁺` attached to
`2 ≤ a ≤ (p - 1) / 2`.

This wraps the existing descended unit
`FLT37.realCyclotomicUnitPlusUnit p K a`, with the index coprimality proved
from the standard prime-conductor range. -/
noncomputable def realCyclotomicUnit (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) : (𝓞 K⁺)ˣ :=
  FLT37.realCyclotomicUnitPlusUnit p K a
    (realCyclotomicUnit_index_coprime (p := p) ha_two ha_le)
    (Fact.out : Nat.Prime p).two_le

@[simp]
theorem realCyclotomicUnit_val (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) :
    (realCyclotomicUnit (p := p) (K := K) a ha_two ha_le : 𝓞 K⁺) =
      FLT37.realCyclotomicUnitPlus p K a := by
  unfold realCyclotomicUnit
  rw [FLT37.realCyclotomicUnitPlusUnit_val]

/-- The route-level real cyclotomic unit is a unit. -/
theorem realCyclotomicUnit_isUnit (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) :
    IsUnit (FLT37.realCyclotomicUnitPlus p K a) :=
  FLT37.isUnit_realCyclotomicUnitPlus p K a
    (realCyclotomicUnit_index_coprime (p := p) ha_two ha_le)
    (Fact.out : Nat.Prime p).two_le

/-- The image of the real cyclotomic unit in `𝓞 K` is the σ-fixed product
`cyclotomicUnit a * σ(cyclotomicUnit a)`. -/
theorem algebraMap_realCyclotomicUnit (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) :
    algebraMap (𝓞 K⁺) (𝓞 K)
        (realCyclotomicUnit (p := p) (K := K) a ha_two ha_le : 𝓞 K⁺) =
      FLT37.realCyclotomicUnit p K a := by
  rw [realCyclotomicUnit_val, FLT37.algebraMap_realCyclotomicUnitPlus]

/-- The image of `realCyclotomicUnit` in `𝓞 K` is fixed by complex
conjugation. -/
theorem realCyclotomicUnit_conj_eq_self (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) :
    ringOfIntegersComplexConj K
        (algebraMap (𝓞 K⁺) (𝓞 K)
          (realCyclotomicUnit (p := p) (K := K) a ha_two ha_le : 𝓞 K⁺)) =
      algebraMap (𝓞 K⁺) (𝓞 K)
        (realCyclotomicUnit (p := p) (K := K) a ha_two ha_le : 𝓞 K⁺) := by
  rw [algebraMap_realCyclotomicUnit]
  exact FLT37.realCyclotomicUnit_complexConj p K a

/-- The image of `realCyclotomicUnit` is a real unit of `K`. -/
theorem realCyclotomicUnit_mem_real (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) :
    Units.map (algebraMap (𝓞 K⁺) (𝓞 K)).toMonoidHom
        (realCyclotomicUnit (p := p) (K := K) a ha_two ha_le) ∈
      realUnits K :=
  ⟨realCyclotomicUnit (p := p) (K := K) a ha_two ha_le, rfl⟩

end BernoulliRegular

end

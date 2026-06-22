module

public import BernoulliRegular.FLT37.PrimaryConj
public import BernoulliRegular.TotallyRealSubfield.ZetaPrime
public import BernoulliRegular.HMinus.KplusPrimeArithmetic
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import FltRegular.NumberTheory.Cyclotomic.MoreLemmas
public import BernoulliRegular.FLT37.PrimaryUnits.Part2

/-!
# Primary units of `𝓞 K⁺` (ticket FLT37c, scaffold)

For Vandiver Lemma 2 (primary unit decomposition), an element
`γ ∈ 𝓞 K⁺` is **primary** when it is congruent to a rational integer
modulo `𝔭⁺^p`, where `𝔭⁺` is the unique prime of `𝓞 K⁺` above `(p)`.
Equivalently (since `𝔭⁺·𝓞 K = 𝔭² = (ζ-1)^2`), this is
`γ ≡ a (mod (ζ-1)^{2p})` viewed in `𝓞 K`.

This file isolates the K⁺-side primary definition with basic API.

## References

* Washington, *Introduction to Cyclotomic Fields*, §6.4.
* Vandiver 1929, *Fermat's Last Theorem and the Second Factor in the
  Cyclotomic Class Number*.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

section PrimaryPlus

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

section RealCyclotomicUnits

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- The real cyclotomic combination descends to `𝓞 K⁺`: there exists
`y ∈ 𝓞 K⁺` with `algebraMap y = realCyclotomicUnit p K k`. -/
theorem exists_realCyclotomicUnit_descent [IsCMField K] (k : ℕ) :
    ∃ y : 𝓞 (NumberField.maximalRealSubfield K),
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) y =
      realCyclotomicUnit p K k :=
  (ringOfIntegersComplexConj_eq_self_iff K (realCyclotomicUnit p K k)).mp
    (realCyclotomicUnit_complexConj p K k)

/-- The K⁺-side real cyclotomic unit: a chosen lift of
`realCyclotomicUnit p K k` to `𝓞 K⁺`. -/
noncomputable def realCyclotomicUnitPlus [IsCMField K] (k : ℕ) :
    𝓞 (NumberField.maximalRealSubfield K) :=
  (exists_realCyclotomicUnit_descent p K k).choose

/-- `algebraMap (realCyclotomicUnitPlus p K k) = realCyclotomicUnit p K k`. -/
theorem algebraMap_realCyclotomicUnitPlus [IsCMField K] (k : ℕ) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (realCyclotomicUnitPlus p K k) =
      realCyclotomicUnit p K k :=
  (exists_realCyclotomicUnit_descent p K k).choose_spec


/-- `realCyclotomicUnitPlus p K 1 = 1` in `𝓞 K⁺`. -/
theorem realCyclotomicUnitPlus_one [IsCMField K] :
    realCyclotomicUnitPlus p K 1 = 1 := by
  apply FaithfulSMul.algebraMap_injective
    (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  rw [algebraMap_realCyclotomicUnitPlus, realCyclotomicUnit_one, map_one]

/-- `realCyclotomicUnitPlus p K (p - 1) = 1` in `𝓞 K⁺`. -/
theorem realCyclotomicUnitPlus_p_sub_one [IsCMField K] :
    realCyclotomicUnitPlus p K (p - 1) = 1 := by
  apply FaithfulSMul.algebraMap_injective
    (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  rw [algebraMap_realCyclotomicUnitPlus, realCyclotomicUnit_p_sub_one, map_one]

/-- `realCyclotomicUnitPlus p K p = 0` in `𝓞 K⁺`. -/
theorem realCyclotomicUnitPlus_p_eq_zero [IsCMField K] :
    realCyclotomicUnitPlus p K p = 0 := by
  apply FaithfulSMul.algebraMap_injective
    (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  rw [algebraMap_realCyclotomicUnitPlus, realCyclotomicUnit_p_eq_zero, map_zero]

/-- `realCyclotomicUnitPlus p K (p + 1) = 1` in `𝓞 K⁺`. -/
theorem realCyclotomicUnitPlus_p_add_one [IsCMField K] :
    realCyclotomicUnitPlus p K (p + 1) = 1 := by
  apply FaithfulSMul.algebraMap_injective
    (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  rw [algebraMap_realCyclotomicUnitPlus, realCyclotomicUnit_p_add_one, map_one]

/-- Iterated periodicity for the K⁺-side cyclotomic unit. -/
theorem realCyclotomicUnitPlus_add_mul_p [IsCMField K] (a m : ℕ) :
    realCyclotomicUnitPlus p K (a + m * p) = realCyclotomicUnitPlus p K a := by
  apply FaithfulSMul.algebraMap_injective
    (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  rw [algebraMap_realCyclotomicUnitPlus, algebraMap_realCyclotomicUnitPlus,
    realCyclotomicUnit_add_mul_p]

/-- `realCyclotomicUnitPlus p K k` only depends on `k mod p`. -/
theorem realCyclotomicUnitPlus_mod_p [IsCMField K] (k : ℕ) :
    realCyclotomicUnitPlus p K k = realCyclotomicUnitPlus p K (k % p) := by
  apply FaithfulSMul.algebraMap_injective
    (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  rw [algebraMap_realCyclotomicUnitPlus, algebraMap_realCyclotomicUnitPlus,
    realCyclotomicUnit_mod_p]

/-- ZMod-indexed wrapper for `realCyclotomicUnit`. -/
noncomputable def realCyclotomicUnitZMod [IsCMField K] (k : ZMod p) : 𝓞 K :=
  realCyclotomicUnit p K k.val

/-- The ZMod-indexed real cyclotomic combination is σ-fixed. -/
theorem realCyclotomicUnitZMod_complexConj [IsCMField K] (k : ZMod p) :
    ringOfIntegersComplexConj K (realCyclotomicUnitZMod p K k) =
      realCyclotomicUnitZMod p K k :=
  realCyclotomicUnit_complexConj p K k.val

/-- ZMod-indexed value at `k = 2` (for `p ≥ 3`). -/
theorem realCyclotomicUnitZMod_two [IsCMField K] (hp_three : 3 ≤ p) :
    realCyclotomicUnitZMod p K (2 : ZMod p) = realCyclotomicUnit p K 2 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  unfold realCyclotomicUnitZMod
  congr 1
  exact ZMod.val_two_eq_two_mod p |>.trans (Nat.mod_eq_of_lt (by omega))

/-- ZMod-indexed value at `k = 3` (for `p ≥ 5`). -/
theorem realCyclotomicUnitZMod_three [IsCMField K] (hp_five : 5 ≤ p) :
    realCyclotomicUnitZMod p K (3 : ZMod p) = realCyclotomicUnit p K 3 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  unfold realCyclotomicUnitZMod
  congr 1
  rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) from by push_cast; rfl,
    ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

/-- ZMod-indexed residue-field congruence: `realCyclotomicUnitZMod k ≡ k.val²
(mod ζ - 1)` in `𝓞 K`. -/
theorem zetaSubOne_dvd_realCyclotomicUnitZMod_sub_sq [IsCMField K] (k : ZMod p) :
    ((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1 ∣
      realCyclotomicUnitZMod p K k - (k.val : 𝓞 K) ^ 2 :=
  zetaSubOne_dvd_realCyclotomicUnit_sub_sq p K k.val

theorem realCyclotomicUnitZMod_natCast [IsCMField K] (k : ℕ) [NeZero p] :
    realCyclotomicUnitZMod p K (k : ZMod p) = realCyclotomicUnit p K k := by
  unfold realCyclotomicUnitZMod
  rw [ZMod.val_natCast, ← realCyclotomicUnit_mod_p]

theorem realCyclotomicUnitZMod_zero [IsCMField K] [NeZero p] :
    realCyclotomicUnitZMod p K (0 : ZMod p) = 0 := by
  unfold realCyclotomicUnitZMod
  rw [ZMod.val_zero, realCyclotomicUnit_zero]

theorem realCyclotomicUnitZMod_one [IsCMField K] :
    realCyclotomicUnitZMod p K (1 : ZMod p) = 1 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  unfold realCyclotomicUnitZMod
  rw [ZMod.val_one, realCyclotomicUnit_one]

/-- `realCyclotomicUnitZMod p K k = 0 ↔ k = 0`. -/
theorem realCyclotomicUnitZMod_eq_zero_iff [IsCMField K] (k : ZMod p) :
    realCyclotomicUnitZMod p K k = 0 ↔ k = 0 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  unfold realCyclotomicUnitZMod
  rw [realCyclotomicUnit_eq_zero_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [show (0 : ZMod p) = ((0 : ℕ) : ZMod p) from by push_cast; rfl,
      ← ZMod.natCast_zmod_val k, ZMod.natCast_eq_natCast_iff]
    exact (Nat.modEq_zero_iff_dvd).mpr h
  · subst h
    simp

/-- For `k : (ZMod p)ˣ`, `realCyclotomicUnitZMod p K (k : ZMod p)` is a unit. -/
theorem isUnit_realCyclotomicUnitZMod_of_units [IsCMField K] (k : (ZMod p)ˣ)
    (hp_two : 2 ≤ p) :
    IsUnit (realCyclotomicUnitZMod p K (k : ZMod p)) := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  unfold realCyclotomicUnitZMod
  exact isUnit_realCyclotomicUnit p K (k : ZMod p).val
    (ZMod.val_coe_unit_coprime k) hp_two

/-- `IsUnit (realCyclotomicUnitZMod p K k) ↔ k ≠ 0`. -/
theorem isUnit_realCyclotomicUnitZMod_iff [IsCMField K] (k : ZMod p) :
    IsUnit (realCyclotomicUnitZMod p K k) ↔ k ≠ 0 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  refine ⟨fun h hk ↦ ?_, fun h ↦ ?_⟩
  · subst hk
    rw [realCyclotomicUnitZMod_zero] at h
    exact not_isUnit_zero h
  · have h_unit : IsUnit k := isUnit_iff_ne_zero.mpr h
    obtain ⟨u, hu⟩ := h_unit
    rw [← hu]
    exact isUnit_realCyclotomicUnitZMod_of_units p K u hp.1.two_le

/-- The K-side cyclotomic unit `(0 : ZMod p)`-indexed equals `0`. -/
theorem cyclotomicUnitZMod_eq_iff_val_dvd (k : ZMod p) :
    cyclotomicUnitZMod p K k = 0 ↔ p ∣ k.val := by
  unfold cyclotomicUnitZMod
  rw [cyclotomicUnit_eq_zero_iff]

/-- For ZMod-indexed cyclotomic unit at unit-class element. -/
theorem cyclotomicUnitZMod_units_val (k : (ZMod p)ˣ) :
    cyclotomicUnitZMod p K (k : ZMod p) = cyclotomicUnit p K (k : ZMod p).val := rfl

/-- ZMod-indexed cyclotomic unit value at `k = 2` (for `p ≥ 3`). -/
theorem cyclotomicUnitZMod_two (hp_three : 3 ≤ p) :
    cyclotomicUnitZMod p K (2 : ZMod p) = cyclotomicUnit p K 2 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  unfold cyclotomicUnitZMod
  congr 1
  exact ZMod.val_two_eq_two_mod p |>.trans (Nat.mod_eq_of_lt (by omega))

/-- ZMod-indexed cyclotomic unit value at `k = 3` (for `p ≥ 5`). -/
theorem cyclotomicUnitZMod_three (hp_five : 5 ≤ p) :
    cyclotomicUnitZMod p K (3 : ZMod p) = cyclotomicUnit p K 3 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  unfold cyclotomicUnitZMod
  congr 1
  rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) from by push_cast; rfl,
    ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

/-- ZMod-indexed residue-field congruence: `cyclotomicUnitZMod k ≡ k.val
(mod ζ - 1)` in `𝓞 K`. -/
theorem zetaSubOne_dvd_cyclotomicUnitZMod_sub_natCast (k : ZMod p) :
    ((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1 ∣
      cyclotomicUnitZMod p K k - (k.val : 𝓞 K) :=
  zetaSubOne_dvd_cyclotomicUnit_sub_natCast p K k.val


/-- ZMod-indexed wrapper for the K⁺-side cyclotomic unit. -/
noncomputable def realCyclotomicUnitPlusZMod [IsCMField K] (k : ZMod p) :
    𝓞 (NumberField.maximalRealSubfield K) :=
  realCyclotomicUnitPlus p K k.val

theorem realCyclotomicUnitPlusZMod_natCast [IsCMField K] (k : ℕ) [NeZero p] :
    realCyclotomicUnitPlusZMod p K (k : ZMod p) = realCyclotomicUnitPlus p K k := by
  unfold realCyclotomicUnitPlusZMod
  rw [ZMod.val_natCast, ← realCyclotomicUnitPlus_mod_p]

theorem algebraMap_realCyclotomicUnitPlusZMod [IsCMField K] (k : ZMod p) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (realCyclotomicUnitPlusZMod p K k) =
      realCyclotomicUnitZMod p K k := by
  unfold realCyclotomicUnitPlusZMod realCyclotomicUnitZMod
  rw [algebraMap_realCyclotomicUnitPlus]

theorem realCyclotomicUnitPlusZMod_zero [IsCMField K] [NeZero p] :
    realCyclotomicUnitPlusZMod p K (0 : ZMod p) = 0 := by
  apply FaithfulSMul.algebraMap_injective
    (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  rw [algebraMap_realCyclotomicUnitPlusZMod, realCyclotomicUnitZMod_zero, map_zero]

theorem realCyclotomicUnitPlusZMod_one [IsCMField K] :
    realCyclotomicUnitPlusZMod p K (1 : ZMod p) = 1 := by
  apply FaithfulSMul.algebraMap_injective
    (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  rw [algebraMap_realCyclotomicUnitPlusZMod, realCyclotomicUnitZMod_one, map_one]

theorem realCyclotomicUnitPlusZMod_eq_zero_iff [IsCMField K] (k : ZMod p) :
    realCyclotomicUnitPlusZMod p K k = 0 ↔ k = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h_alg := congrArg
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) h
    rw [algebraMap_realCyclotomicUnitPlusZMod, map_zero] at h_alg
    exact (realCyclotomicUnitZMod_eq_zero_iff p K k).mp h_alg
  · subst h
    haveI : NeZero p := ⟨hp.1.ne_zero⟩
    exact realCyclotomicUnitPlusZMod_zero p K

/-- K⁺-side ZMod-indexed value at `k = 2` (for `p ≥ 3`). -/
theorem realCyclotomicUnitPlusZMod_two [IsCMField K] (hp_three : 3 ≤ p) :
    realCyclotomicUnitPlusZMod p K (2 : ZMod p) = realCyclotomicUnitPlus p K 2 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  unfold realCyclotomicUnitPlusZMod
  congr 1
  exact ZMod.val_two_eq_two_mod p |>.trans (Nat.mod_eq_of_lt (by omega))

/-- K⁺-side ZMod-indexed value at `k = 3` (for `p ≥ 5`). -/
theorem realCyclotomicUnitPlusZMod_three [IsCMField K] (hp_five : 5 ≤ p) :
    realCyclotomicUnitPlusZMod p K (3 : ZMod p) = realCyclotomicUnitPlus p K 3 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  unfold realCyclotomicUnitPlusZMod
  congr 1
  rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) from by push_cast; rfl,
    ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]

/-- The K⁺-side real cyclotomic unit is itself a unit when `k` is coprime
to `p`. Uses the norm characterization of units in `𝓞 K⁺`. -/
theorem isUnit_realCyclotomicUnitPlus [IsCMField K] (k : ℕ)
    (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    IsUnit (realCyclotomicUnitPlus p K k) := by
  have h_unit : IsUnit (realCyclotomicUnit p K k) :=
    isUnit_realCyclotomicUnit p K k hk hp_two
  rw [← algebraMap_realCyclotomicUnitPlus p K k] at h_unit
  -- norm of a unit is a unit; norm K⁺ (algebraMap y) = y^[K:K⁺] = y^2
  have h_norm_unit : IsUnit (RingOfIntegers.norm (NumberField.maximalRealSubfield K)
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (realCyclotomicUnitPlus p K k))) :=
    h_unit.map _
  rw [RingOfIntegers.norm_algebraMap] at h_norm_unit
  -- IsUnit (y ^ finrank) → IsUnit y when finrank > 0
  have hfin_ne : Module.finrank (NumberField.maximalRealSubfield K) K ≠ 0 := by
    rw [finrank_K_over_Kplus]
    decide
  exact (isUnit_pow_iff hfin_ne).mp h_norm_unit

/-- The K⁺-side real cyclotomic unit, packaged as an element of
`(𝓞 K⁺)ˣ` when `k` is coprime to `p`. -/
noncomputable def realCyclotomicUnitPlusUnit [IsCMField K] (k : ℕ)
    (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    (𝓞 (NumberField.maximalRealSubfield K))ˣ :=
  (isUnit_realCyclotomicUnitPlus p K k hk hp_two).unit

@[simp]
theorem realCyclotomicUnitPlusUnit_val [IsCMField K] (k : ℕ)
    (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    (realCyclotomicUnitPlusUnit p K k hk hp_two : 𝓞 (NumberField.maximalRealSubfield K)) =
      realCyclotomicUnitPlus p K k :=
  IsUnit.unit_spec _

/-- The K⁺-side cyclotomic unit lift, viewed in `(𝓞 K)ˣ` via the unit
map of `algebraMap`, equals `realCyclotomicUnitUnit`. -/
theorem algebraMap_realCyclotomicUnitPlusUnit_val [IsCMField K] (k : ℕ)
    (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (realCyclotomicUnitPlusUnit p K k hk hp_two) =
      realCyclotomicUnit p K k := by
  rw [realCyclotomicUnitPlusUnit_val, algebraMap_realCyclotomicUnitPlus]

/-- For `k : (ZMod p)ˣ`, `realCyclotomicUnitPlusZMod p K (k : ZMod p)` is a unit. -/
theorem isUnit_realCyclotomicUnitPlusZMod_of_units [IsCMField K] (k : (ZMod p)ˣ)
    (hp_two : 2 ≤ p) :
    IsUnit (realCyclotomicUnitPlusZMod p K (k : ZMod p)) := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  unfold realCyclotomicUnitPlusZMod
  exact isUnit_realCyclotomicUnitPlus p K (k : ZMod p).val
    (ZMod.val_coe_unit_coprime k) hp_two

/-- `IsUnit (realCyclotomicUnitPlusZMod p K k) ↔ k ≠ 0`. -/
theorem isUnit_realCyclotomicUnitPlusZMod_iff [IsCMField K] (k : ZMod p) :
    IsUnit (realCyclotomicUnitPlusZMod p K k) ↔ k ≠ 0 := by
  haveI : NeZero p := ⟨hp.1.ne_zero⟩
  refine ⟨fun h hk ↦ ?_, fun h ↦ ?_⟩
  · subst hk
    rw [realCyclotomicUnitPlusZMod_zero] at h
    exact not_isUnit_zero h
  · have h_unit : IsUnit k := isUnit_iff_ne_zero.mpr h
    obtain ⟨u, hu⟩ := h_unit
    rw [← hu]
    exact isUnit_realCyclotomicUnitPlusZMod_of_units p K u hp.1.two_le

/-- **Integer norm of K⁺-side cyclotomic unit is a unit in ℤ.** Since
`realCyclotomicUnitPlus p K k` is a unit (for `k` coprime to `p`,
`p ≥ 2`), its integer norm is a unit in `ℤ`, hence `±1`. -/
theorem realCyclotomicUnitPlus_norm_int_isUnit [IsCMField K]
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    IsUnit (Algebra.norm ℤ (realCyclotomicUnitPlus p K k)) :=
  (isUnit_realCyclotomicUnitPlus p K k hk hp_two).map _

/-- **Squared integer norm of K⁺-side cyclotomic unit is 1.** Direct
corollary of the unit property. -/
theorem realCyclotomicUnitPlus_norm_int_sq_eq_one [IsCMField K]
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    (Algebra.norm ℤ (realCyclotomicUnitPlus p K k)) ^ 2 = (1 : ℤ) := by
  rcases Int.isUnit_iff.mp (realCyclotomicUnitPlus_norm_int_isUnit p K k hk hp_two) with h | h
    <;> rw [h] <;> norm_num

end RealCyclotomicUnits

end PrimaryPlus

end FLT37

end BernoulliRegular

end

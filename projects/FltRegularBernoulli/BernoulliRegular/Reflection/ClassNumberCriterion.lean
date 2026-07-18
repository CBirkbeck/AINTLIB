module

public import Mathlib.NumberTheory.Bernoulli
public import BernoulliRegular.HMinusCriterion
public import BernoulliRegular.Reflection.Final
public import BernoulliRegular.Reflection.FinalReflection

/-!
# Reflection-route class-number criterion

This file contains the class-number consequence of the reflection route. It
deliberately stops before restating Kummer's criterion: the public endpoint is
`BernoulliRegular.kummer_criterion`, proved through cyclotomic units.
-/

@[expose] public section

open NumberField

namespace BernoulliRegular

/-- **T045a** — reduction of `p ∣ h` to `p ∣ h⁻`.

The reverse direction is automatic from `h = h⁺ · h⁻` (T019). The forward
direction is the reflection consequence `p ∣ h⁺ ⟹ p ∣ h⁻` (T044), which
in this project is packaged in a `ReflectionMinusNontrivialityBridge` —
an honest bridge encoding the reflection-mechanism output at the
class-number level. Consumers instantiate the bridge from `T042b`/`T043`
plus the class-group / reflection-component identification. -/
theorem dvd_h_iff_dvd_hMinus
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [IsCMField K] (B : ReflectionMinusNontrivialityBridge p K) :
    (p : ℕ) ∣ h K ↔ (p : ℕ) ∣ hMinus K := by
  constructor
  · -- `p ∣ h ⟹ p ∣ h⁻`: `p` prime + `h = h⁺ · h⁻`, so `p` divides one
    -- factor. Either it divides `h⁻` directly, or it divides `h⁺` and
    -- the reflection bridge transfers that to `h⁻`.
    intro hpH
    rw [h_eq_hPlus_mul_hMinus p hp_odd K] at hpH
    rcases (Nat.Prime.dvd_mul hp.out).mp hpH with hpl | hpr
    · exact B.dvd_hMinus_of_dvd_hPlus hpl
    · exact hpr
  · -- `p ∣ h⁻ ⟹ p ∣ h`: immediate from `h = h⁺ · h⁻`.
    intro hpMinus
    rw [h_eq_hPlus_mul_hMinus p hp_odd K]
    exact dvd_mul_of_dvd_right hpMinus _

/-- **T045b** — `p ∣ h ↔ ∃ k, 1 ≤ k ∧ 2k ≤ p-3 ∧ p ∣ (bernoulli (2k)).num`.

Chains T045a's `dvd_h_iff_dvd_hMinus` with the closed `h⁻`-Bernoulli
criterion from T017 (`p_dvd_hMinus_iff_p_dvd_some_bernoulli`). -/
theorem dvd_h_iff_exists_dvd_bernoulli
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [IsCMField K] (B : ReflectionMinusNontrivialityBridge p K) :
    (p : ℕ) ∣ h K ↔
      ∃ k, 1 ≤ k ∧ 2 * k ≤ p - 3 ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num := by
  rw [dvd_h_iff_dvd_hMinus hp_odd B,
    p_dvd_hMinus_iff_p_dvd_some_bernoulli (p := p) (K := K) hp_odd]

/-- **T045a/T045b via weak reflection.**

This is the class-number/Bernoulli bridge using the explicit weak-reflection
component theorem rather than a prebuilt `ReflectionMinusNontrivialityBridge`.
The only reflection input is `weakReflection_componentNontrivial`. -/
theorem dvd_h_iff_exists_dvd_bernoulli_of_weakReflection
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [IsCMField K] :
    (p : ℕ) ∣ h K ↔
      ∃ k, 1 ≤ k ∧ 2 * k ≤ p - 3 ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num := by
  constructor
  · intro hpH
    have h_hMinus :
        (p : ℕ) ∣ hMinus K ↔
          ∃ k, 1 ≤ k ∧ 2 * k ≤ p - 3 ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num :=
      p_dvd_hMinus_iff_p_dvd_some_bernoulli (p := p) (K := K) hp_odd
    rw [h_eq_hPlus_mul_hMinus p hp_odd K] at hpH
    rcases (Nat.Prime.dvd_mul hp.out).mp hpH with hplus | hminus
    · exact h_hMinus.mp <|
        weakReflection_dvd_hMinus_of_dvd_hPlus
          p hp_odd K hplus
    · exact h_hMinus.mp hminus
  · intro hBernoulli
    have h_hMinus :
        (p : ℕ) ∣ hMinus K ↔
          ∃ k, 1 ≤ k ∧ 2 * k ≤ p - 3 ∧ (p : ℤ) ∣ (bernoulli (2 * k)).num :=
      p_dvd_hMinus_iff_p_dvd_some_bernoulli (p := p) (K := K) hp_odd
    have hminus : (p : ℕ) ∣ hMinus K := h_hMinus.mpr hBernoulli
    rw [h_eq_hPlus_mul_hMinus p hp_odd K]
    exact dvd_mul_of_dvd_right hminus _

end BernoulliRegular

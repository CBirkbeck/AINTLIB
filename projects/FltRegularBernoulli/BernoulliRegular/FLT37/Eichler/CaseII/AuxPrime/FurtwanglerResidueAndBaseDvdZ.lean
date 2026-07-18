import BernoulliRegular.FLT37.Eichler.CaseII.Mirimanoff.Lemma98RealData
import BernoulliRegular.FLT37.Eichler.CaseII.RootClass.IntSolutionToRealDatum

/-!
# Furtwängler residue obstruction for `(37, 149)`

This file proves Washington's Lemma 9.7 at the integer base of the FLT37 Case II descent.
The residue calculation in `ZMod 149` forces the third Fermat variable to be divisible by `149`
and transports this divisibility to the corresponding real Case II datum.

## Main results

* `furtwangler_37_149`: a Fermat equation in `ZMod 149` has a zero variable.
* `caseII_int_dvd_z_of_lemma96`: the auxiliary prime `149` divides the third integer variable.
* `exists_realCaseIIData37_with_dvd_z_of_caseII_int_solution_z`: the base real datum inherits
  membership in `lv149`.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Theorem 9.5, Lemma 9.6
  and Lemma 9.7, pp. 176–178.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

/-- The `37`-th-power residues in `ZMod 149` are `0`, `1`, `44`, `105`, and `148`. -/
theorem caseII_pow37_values_149 (a : ZMod 149) :
    a ^ 37 = 0 ∨ a ^ 37 = 1 ∨ a ^ 37 = 44 ∨ a ^ 37 = 105 ∨ a ^ 37 = 148 := by
  have h44 : (44 : ZMod 149) ^ 2 = -1 := by decide
  have h105 : (105 : ZMod 149) = -44 := by decide
  have h148 : (148 : ZMod 149) = -1 := by decide
  haveI : Fact (Nat.Prime 149) := ⟨by decide⟩
  by_cases hzero : a ^ 37 = 0
  · exact Or.inl hzero
  right
  have ha : a ≠ 0 := by
    intro ha
    subst a
    exact hzero (zero_pow (by decide))
  have hpow : (a ^ 37) ^ 4 = 1 := by
    rw [← pow_mul]
    norm_num
    exact ZMod.pow_card_sub_one_eq_one ha
  have hfactor :
      (a ^ 37 - 1) * ((a ^ 37 - 44) * ((a ^ 37 + 44) * (a ^ 37 + 1))) = 0 := by
    calc
      _ = ((a ^ 37) ^ 2 - 1) * ((a ^ 37) ^ 2 - 44 ^ 2) := by ring
      _ = ((a ^ 37) ^ 2 - 1) * ((a ^ 37) ^ 2 + 1) := by rw [h44]; ring
      _ = (a ^ 37) ^ 4 - 1 := by ring
      _ = 0 := by rw [hpow, sub_self]
  have hor :
      a ^ 37 = 1 ∨ a ^ 37 = 44 ∨ a ^ 37 = -44 ∨ a ^ 37 = -1 := by
    simpa only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] using hfactor
  simpa only [← h105, ← h148] using hor

/-- A `37`-th power in `ZMod 149` is zero exactly when its base is zero. -/
theorem caseII_pow37_eq_zero_iff_149 (a : ZMod 149) : a ^ 37 = 0 ↔ a = 0 :=
  haveI : Fact (Nat.Prime 149) := ⟨by decide⟩
  pow_eq_zero_iff (by decide : 37 ≠ 0)

/-- A Fermat equation of exponent `37` in `ZMod 149` has a zero variable. -/
theorem furtwangler_37_149 (a b c : ZMod 149)
    (h : a ^ 37 + b ^ 37 = c ^ 37) : a = 0 ∨ b = 0 ∨ c = 0 := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨ha, hb, hc⟩ := hcon
  have ha' : a ^ 37 ≠ 0 := mt (caseII_pow37_eq_zero_iff_149 a).mp ha
  have hb' : b ^ 37 ≠ 0 := mt (caseII_pow37_eq_zero_iff_149 b).mp hb
  have hc' : c ^ 37 ≠ 0 := mt (caseII_pow37_eq_zero_iff_149 c).mp hc
  rcases caseII_pow37_values_149 a with h1 | h1 | h1 | h1 | h1 <;>
  rcases caseII_pow37_values_149 b with h2 | h2 | h2 | h2 | h2 <;>
  rcases caseII_pow37_values_149 c with h3 | h3 | h3 | h3 | h3 <;>
    first
      | exact ha' h1
      | exact hb' h2
      | exact hc' h3
      | (rw [h1, h2, h3] at h; revert h; decide)

/-- Membership of an integer cast in `lv149` is vanishing modulo `149`. -/
theorem caseII_intCast_mem_lv149_iff (n : ℤ) :
    (n : 𝓞 (CyclotomicField 37 ℚ)) ∈ lv149 ↔ (n : ZMod 149) = 0 := by
  simp only [lv149, lehmerVandiverPrime]
  rw [Ideal.mem_comap, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingHom.mem_ker,
    map_intCast, map_intCast]

/-- Builds the base real Case II datum and records its `(ζ - 1)`-multiplicity relation. -/
theorem exists_realCaseIIData37_zRel_of_Int_solution
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {x y z : ℤ} (hy_int : ¬ (37 : ℤ) ∣ y) (hz_int : (37 : ℤ) ∣ z) (hz_ne : z ≠ 0)
    (e : x ^ 37 + y ^ 37 = z ^ 37) :
    ∃ (m : ℕ) (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m),
      (D.x = (x : 𝓞 (CyclotomicField 37 ℚ))) ∧
        (D.y = (y : 𝓞 (CyclotomicField 37 ℚ))) ∧
          (z : 𝓞 (CyclotomicField 37 ℚ)) = (D.hζ.toInteger - 1) ^ (m + 1) * D.z := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI := CyclotomicField.isCyclotomicExtension 37 ℚ
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot
    ℚ (B := (CyclotomicField 37 ℚ)) (Set.mem_singleton 37)
    (by decide : (37 : ℕ) ≠ 0)
  have h_dvd_iff := fun n ↦
    zeta_sub_one_dvd_Int_iff (K := CyclotomicField 37 ℚ) hζ (n := n)
  have hy : ¬ (hζ.toInteger - 1) ∣ (y : 𝓞 (CyclotomicField 37 ℚ)) :=
    mt (h_dvd_iff y).mp hy_int
  have hz : (hζ.toInteger - 1) ∣ (z : 𝓞 (CyclotomicField 37 ℚ)) := (h_dvd_iff z).mpr hz_int
  have hz_ne_OK : (z : 𝓞 (CyclotomicField 37 ℚ)) ≠ 0 := by rwa [ne_eq, Int.cast_eq_zero]
  have eOK :
      (x : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 + (y : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 =
        (z : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 := by
    simp_rw [← Int.cast_pow, ← Int.cast_add, e]
  letI : WfDvdMonoid (𝓞 (CyclotomicField 37 ℚ)) := IsNoetherianRing.wfDvdMonoid
  obtain ⟨n, z', hn, hz_n, hz_eq⟩ :
      ∃ n z', 1 ≤ n ∧ ¬ ((hζ.toInteger - 1) ∣ z') ∧
        (z : 𝓞 (CyclotomicField 37 ℚ)) = (hζ.toInteger - 1) ^ n * z' := by
    classical
    have H : FiniteMultiplicity (hζ.toInteger - 1) (z : 𝓞 (CyclotomicField 37 ℚ)) :=
      FiniteMultiplicity.of_not_isUnit hζ.zeta_sub_one_prime'.not_unit hz_ne_OK
    obtain ⟨z', hfac⟩ :=
      pow_multiplicity_dvd (hζ.toInteger - 1) (z : 𝓞 (CyclotomicField 37 ℚ))
    refine ⟨_, _, ?_, ?_, hfac⟩
    · rwa [← Nat.cast_le (α := ENat), ← FiniteMultiplicity.emultiplicity_eq_multiplicity H,
        ← pow_dvd_iff_le_emultiplicity, pow_one]
    · intro h_dvd
      have hpowDvd := mul_dvd_mul_left
        ((hζ.toInteger - 1) ^
          multiplicity (hζ.toInteger - 1) (z : 𝓞 (CyclotomicField 37 ℚ))) h_dvd
      rw [← pow_succ, ← hfac] at hpowDvd
      refine not_pow_dvd_of_emultiplicity_lt ?_ hpowDvd
      rw [FiniteMultiplicity.emultiplicity_eq_multiplicity H, Nat.cast_lt]
      exact Nat.lt_succ_self _
  have hn_eq : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have heqn :
      (x : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 + (y : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 =
        (1 : (𝓞 (CyclotomicField 37 ℚ))ˣ) *
          ((hζ.toInteger - 1) ^ (n - 1 + 1) * z') ^ 37 := by
    rw [hz_eq] at eOK
    simpa [hn_eq] using eOK
  refine ⟨n - 1,
    { ζ := ζ
      hζ := hζ
      x := (x : 𝓞 (CyclotomicField 37 ℚ))
      y := (y : 𝓞 (CyclotomicField 37 ℚ))
      z := z'
      ε := 1
      equation := heqn
      hy := hy
      hz := hz_n
      x_real := ringOfIntegersComplexConj_intCast_eq (K := CyclotomicField 37 ℚ) x
      y_real := ringOfIntegersComplexConj_intCast_eq (K := CyclotomicField 37 ℚ) y },
    rfl, rfl, ?_⟩
  rw [hn_eq]
  exact hz_eq

/-- Washington's Lemma 9.7 for an integer Fermat equation of exponent `37`. -/
theorem caseII_int_dvd_z_of_lemma96 {x y z : ℤ}
    (e : x ^ 37 + y ^ 37 = z ^ 37)
    (hx_lv : ¬ (149 : ℤ) ∣ x) (hy_lv : ¬ (149 : ℤ) ∣ y) :
    (149 : ℤ) ∣ z := by
  have hx' : ¬ (x : ZMod 149) = 0 := mt (ZMod.intCast_zmod_eq_zero_iff_dvd x 149).mp hx_lv
  have hy' : ¬ (y : ZMod 149) = 0 := mt (ZMod.intCast_zmod_eq_zero_iff_dvd y 149).mp hy_lv
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd z 149).mp ?_
  have he : (x : ZMod 149) ^ 37 + (y : ZMod 149) ^ 37 = (z : ZMod 149) ^ 37 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod 149) e
  rcases furtwangler_37_149 (x : ZMod 149) (y : ZMod 149) (z : ZMod 149) he with h | h | h
  · exact absurd h hx'
  · exact absurd h hy'
  · exact h

/-- Builds a base real Case II datum whose descent integer lies in `lv149`. -/
theorem exists_realCaseIIData37_with_dvd_z_of_Int_solution
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {x y z : ℤ} (hy_int : ¬ (37 : ℤ) ∣ y) (hz_int : (37 : ℤ) ∣ z) (hz_ne : z ≠ 0)
    (e : x ^ 37 + y ^ 37 = z ^ 37)
    (hx_lv : ¬ (x : ZMod 149) = 0) (hy_lv : ¬ (y : ZMod 149) = 0) :
    ∃ m : ℕ, ∃ D : RealCaseIIData37 (CyclotomicField 37 ℚ) m, D.z ∈ lv149 := by
  haveI : lv149.IsPrime := lv149_isMaximal.isPrime
  obtain ⟨m, D, _hx, _hy, hz_eq⟩ :=
    exists_realCaseIIData37_zRel_of_Int_solution hy_int hz_int hz_ne e
  refine ⟨m, D, ?_⟩
  have hz_dvd : (149 : ℤ) ∣ z :=
    caseII_int_dvd_z_of_lemma96 e
      (mt (ZMod.intCast_zmod_eq_zero_iff_dvd x 149).mpr hx_lv)
      (mt (ZMod.intCast_zmod_eq_zero_iff_dvd y 149).mpr hy_lv)
  have hz_mem : (z : 𝓞 (CyclotomicField 37 ℚ)) ∈ lv149 :=
    (caseII_intCast_mem_lv149_iff z).mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd z 149).mpr hz_dvd)
  rw [hz_eq] at hz_mem
  rcases Ideal.IsPrime.mem_or_mem ‹lv149.IsPrime› hz_mem with hpow | hz'
  · exact absurd (Ideal.IsPrime.mem_of_pow_mem ‹lv149.IsPrime› (m + 1) hpow)
      (caseII_zeta_sub_one_notMem_lv149 D.hζ)
  · exact hz'

/-- Builds the base real Case II datum with `D.z ∈ lv149` when `37 ∣ c`. -/
theorem exists_realCaseIIData37_with_dvd_z_of_caseII_int_solution_z
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    {a b c : ℤ} (ha_int : ¬ (37 : ℤ) ∣ a) (hc_int : (37 : ℤ) ∣ c) (hc_ne : c ≠ 0)
    (e : a ^ 37 + b ^ 37 = c ^ 37)
    (ha_lv : ¬ (149 : ℤ) ∣ a) (hb_lv : ¬ (149 : ℤ) ∣ b) :
    ∃ m : ℕ, ∃ D : RealCaseIIData37 (CyclotomicField 37 ℚ) m, D.z ∈ lv149 := by
  have hb_int : ¬ (37 : ℤ) ∣ b := by
    intro hb
    have h_dvd : (37 : ℤ) ∣ a ^ 37 := by
      have hpow := dvd_sub (dvd_pow hc_int (by decide : (37 : ℕ) ≠ 0))
        (dvd_pow hb (by decide : (37 : ℕ) ≠ 0))
      rwa [← e, add_sub_cancel_right] at hpow
    exact ha_int <| (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 37)).dvd_of_dvd_pow h_dvd
  refine exists_realCaseIIData37_with_dvd_z_of_Int_solution hb_int hc_int hc_ne e
    (mt (ZMod.intCast_zmod_eq_zero_iff_dvd a 149).mp ha_lv)
    (mt (ZMod.intCast_zmod_eq_zero_iff_dvd b 149).mp hb_lv)

/-- The base Lemma 9.7 divisibility hypothesis implies the real-data conclusion of Lemma 9.8. -/
theorem caseII_real_base_x_add_y_mem
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (hSO : NoSecondOrderIrregularPair 37 32)
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hz : D.z ∈ lv149) (hxl : D.x ∉ lv149) (hyl : D.y ∉ lv149) :
    D.x + D.y ∈ lv149 :=
  caseII_real_x_add_y_mem_of_dvd_z hSO D hz hxl hyl

end BernoulliRegular.FLT37.Eichler

end

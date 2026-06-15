module

public import BernoulliRegular.TotallyRealSubfield.Conjugation

/-!
# Fixed-associate descent

This file removes the residual root-of-unity twist and produces
conjugation-fixed generators that descend to `𝒪_{K⁺}`.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField Algebra IsCyclotomicExtension
open scoped NumberField nonZeroDivisors

namespace BernoulliRegular

section CyclotomicSetup

variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

include hp_odd in
/-- If `u` is classified as a pure `ζ`-power, the possible `-1` factor is absent. -/
theorem generator_unit_eq_zeta_pow [IsCMField K]
    {hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (I : Ideal (𝓞 (NumberField.maximalRealSubfield K)))
    (a : 𝓞 K) (u : (𝓞 K)ˣ)
    (ha : a ≠ 0)
    (hIa : I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) = Ideal.span {a})
    (hu : ringOfIntegersComplexConj K a = u * a)
    (hclass : ∃ n k : ℕ, u = (-1 : (𝓞 K)ˣ) ^ k *
      (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit ^ n) :
    ∃ n : ℕ, u = (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit ^ n := by
  obtain ⟨n, k, huk⟩ := hclass
  set η : (𝓞 K)ˣ := (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit with hη_def
  have hηcoe : ((η : (𝓞 K)ˣ) : 𝓞 K) = hζ.toInteger := by
    rw [hη_def]; exact IsUnit.unit_spec _
  have hηpow : (η : (𝓞 K)ˣ) ^ p = 1 := by
    rw [hη_def]; exact (hζ.toInteger_isPrimitiveRoot.isUnit_unit (NeZero.ne p)).pow_eq_one
  clear_value η
  by_cases hk_even : Even k
  · rcases hk_even with ⟨m, rfl⟩
    have hneg_even : (-1 : (𝓞 K)ˣ) ^ (m + m) = 1 :=
      Even.neg_one_pow (show Even (m + m) from ⟨m, rfl⟩)
    refine ⟨n, ?_⟩
    calc
      u = (-1 : (𝓞 K)ˣ) ^ (m + m) * η ^ n := huk
      _ = η ^ n := by rw [hneg_even]; simp
  · have hk_odd : Odd k := Nat.not_even_iff_odd.mp hk_even
    let π : 𝓞 K := hζ.toInteger - 1
    let P : Ideal (𝓞 K) := zetaPrime p K
    let e := multiplicity π a
    have heven : Even e :=
      multiplicity_zetaPrime_even_of_map_eq_span (p := p) (hp_odd := hp_odd) (K := K) I a ha hIa
    have hπPrime : Prime π := by simpa [π] using hζ.zeta_sub_one_prime'
    have hπFin : FiniteMultiplicity π a := FiniteMultiplicity.of_prime_left hπPrime ha
    obtain ⟨b, hpow, hnotdvd⟩ := hπFin.exists_eq_pow_mul_and_not_dvd
    have hb_not_mem : b ∉ P := by
      simpa [P, π, zetaPrime, Ideal.mem_span_singleton] using hnotdvd
    have hu_odd : u = (-1 : (𝓞 K)ˣ) * η ^ n := by
      have hneg_odd : (-1 : (𝓞 K)ˣ) ^ k = -1 := Odd.neg_one_pow hk_odd
      calc
        u = (-1 : (𝓞 K)ˣ) ^ k * η ^ n := huk
        _ = (-1 : (𝓞 K)ˣ) * η ^ n := by rw [hneg_odd]
    let γ : (𝓞 K)ˣ := (-1 : (𝓞 K)ˣ) * η ^ (p - 1)
    have hc_pi : ringOfIntegersComplexConj K π = (γ : (𝓞 K)ˣ) * π := by
      have hc_pi' : ringOfIntegersComplexConj K π = -hζ.toInteger ^ (p - 1) * π := by
        rw [show π = hζ.toInteger - 1 by rfl, map_sub, map_one, complexConj_apply_zeta]
        linear_combination zeta_toInteger_pow_pred_mul p K
      simpa [γ, π, hηcoe, mul_assoc, mul_left_comm, mul_comm] using hc_pi'
    have hγ_mul : γ ^ e * η ^ e = 1 := by
      have hγhu : γ * η = (-1 : (𝓞 K)ˣ) := by
        dsimp [γ]
        rw [mul_assoc, ← pow_succ, Nat.sub_one_add_one hp.1.ne_zero, hηpow, mul_one]
      have hmulpow : γ ^ e * η ^ e = (γ * η) ^ e := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using (mul_pow γ η e).symm
      calc
        γ ^ e * η ^ e = (γ * η) ^ e := hmulpow
        _ = (-1 : (𝓞 K)ˣ) ^ e := by rw [hγhu]
        _ = 1 := by simpa using (Even.neg_one_pow heven : (-1 : (𝓞 K)ˣ) ^ e = 1)
    let u' : (𝓞 K)ˣ := η ^ e * u
    have hcb : ringOfIntegersComplexConj K b = u' * b := by
      have hcalc : ringOfIntegersComplexConj K (π ^ e * b) = u * (π ^ e * b) := by
        calc
          ringOfIntegersComplexConj K (π ^ e * b) = ringOfIntegersComplexConj K a := by rw [hpow]
          _ = u * a := hu
          _ = u * (π ^ e * b) := by rw [hpow]
      rw [map_mul, map_pow, hc_pi, mul_pow] at hcalc
      have hcancel : (((γ ^ e : (𝓞 K)ˣ) : 𝓞 K) * ringOfIntegersComplexConj K b) =
          ((u : (𝓞 K)ˣ) : 𝓞 K) * b := by
        have htmp : π ^ e * ((((γ ^ e : (𝓞 K)ˣ) : 𝓞 K) * ringOfIntegersComplexConj K b)) =
            π ^ e * ((((u : (𝓞 K)ˣ) : 𝓞 K) * b)) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hcalc
        exact mul_left_cancel₀ (pow_ne_zero _ hπPrime.ne_zero) htmp
      have hγ_mul' : η ^ e * γ ^ e = 1 := by simpa [mul_comm] using hγ_mul
      have hmult := congrArg (fun x : 𝓞 K => (((η ^ e : (𝓞 K)ˣ) : 𝓞 K) * x)) hcancel
      have hγ_mul_coe : ((((η ^ e : (𝓞 K)ˣ) * γ ^ e : (𝓞 K)ˣ) : 𝓞 K)) = 1 :=
        congrArg (fun x : (𝓞 K)ˣ => (x : 𝓞 K)) hγ_mul'
      have hmult'' : ((((η ^ e : (𝓞 K)ˣ) * γ ^ e : (𝓞 K)ˣ) : 𝓞 K) *
          ringOfIntegersComplexConj K b) =
          ((((η ^ e : (𝓞 K)ˣ) * u : (𝓞 K)ˣ) : 𝓞 K) * b) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmult
      have hmult' : ringOfIntegersComplexConj K b =
          ((((η ^ e : (𝓞 K)ˣ) * u : (𝓞 K)ˣ) : 𝓞 K) * b) := by
        calc
          ringOfIntegersComplexConj K b =
              ((((η ^ e : (𝓞 K)ˣ) * γ ^ e : (𝓞 K)ˣ) : 𝓞 K) *
                ringOfIntegersComplexConj K b) := by rw [hγ_mul_coe]; simp
          _ = ((((η ^ e : (𝓞 K)ˣ) * u : (𝓞 K)ˣ) : 𝓞 K) * b) := hmult''
      simpa [u', mul_assoc, mul_left_comm, mul_comm] using hmult'
    have hpow_sub : ∀ m : ℕ, (hζ.toInteger ^ m - 1 : 𝓞 K) ∈ P := by
      intro m
      dsimp [P]
      rw [zetaPrime, Ideal.mem_span_singleton]
      have hdiv := sub_dvd_pow_sub_pow hζ.toInteger (1 : 𝓞 K) m
      rwa [one_pow] at hdiv
    have hu'_class : u' = (-1 : (𝓞 K)ˣ) * η ^ (e + n) := by
      dsimp [u']
      calc
        η ^ e * u = η ^ e * ((-1 : (𝓞 K)ˣ) * η ^ n) := by rw [hu_odd]
        _ = (-1 : (𝓞 K)ˣ) * (η ^ e * η ^ n) := by simp [mul_left_comm, mul_comm]
        _ = (-1 : (𝓞 K)ˣ) * η ^ (e + n) := by rw [← pow_add]
    have hu'_plus_mem : ((((u' : (𝓞 K)ˣ) : 𝓞 K) + 1) : 𝓞 K) ∈ P := by
      have hu'_plus_eq : (((u' : (𝓞 K)ˣ) : 𝓞 K) + 1 : 𝓞 K) =
          (1 - hζ.toInteger ^ e * hζ.toInteger ^ n : 𝓞 K) := by
        rw [hu'_class]
        simp only [Units.val_mul, Units.val_neg]
        rw [show (((η ^ (e + n) : (𝓞 K)ˣ) : 𝓞 K)) = hζ.toInteger ^ (e + n) by
          rw [Units.val_pow_eq_pow_val, hηcoe]]
        rw [pow_add]
        simp [sub_eq_add_neg, add_comm]
      have hpow_sub' : (1 - hζ.toInteger ^ e * hζ.toInteger ^ n : 𝓞 K) ∈ P := by
        have : (1 - hζ.toInteger ^ e * hζ.toInteger ^ n : 𝓞 K) = -(hζ.toInteger ^ (e + n) - 1) := by
          rw [pow_add]
          ring
        rw [this]
        exact P.neg_mem (hpow_sub (e + n))
      rw [hu'_plus_eq]
      exact hpow_sub'
    have hu'_minus_not_mem : ((((u' : (𝓞 K)ˣ) : 𝓞 K) - 1) : 𝓞 K) ∉ P := by
      intro hminus
      have hp2 : 2 < p := lt_of_le_of_ne hp.1.two_le (Ne.symm hp_odd)
      have htwo : (2 : 𝓞 K) ∈ P := by
        have hsub := Ideal.sub_mem _ hu'_plus_mem hminus
        convert hsub using 1
        ring
      exact (zeta_spec p ℚ K).two_not_mem_one_sub_zeta hp2 htwo
    have hprod_mem : ((((u' : (𝓞 K)ˣ) : 𝓞 K) - 1) * b : 𝓞 K) ∈ P := by
      have hres : (ringOfIntegersComplexConj K b : 𝓞 K) - b ∈ P :=
        complexConj_sub_mem_zetaPrime p K b
      convert hres using 1
      rw [hcb]
      ring
    exfalso
    rcases (zetaPrime_isPrime p K).mem_or_mem hprod_mem with hunit_mem | hb_mem
    · exact hu'_minus_not_mem hunit_mem
    · exact hb_not_mem hb_mem

include hp_odd in
/-- Twisting by a suitable square root yields a conjugation-fixed associate. -/
theorem exists_conj_fixed_associate_of_zeta_pow [IsCMField K]
    {hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (a : 𝓞 K) (u : (𝓞 K)ˣ)
    (hu : ringOfIntegersComplexConj K a = u * a)
    (hclass : ∃ n : ℕ, u = (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit ^ n) :
    ∃ b : 𝓞 K, ringOfIntegersComplexConj K b = b ∧ Ideal.span {b} = Ideal.span {a} := by
  have hpo : Odd p := hp.1.odd_of_ne_two hp_odd
  obtain ⟨n, rfl⟩ := hclass
  obtain ⟨m, hm⟩ := zeta_runity_pow_even hζ hpo n
  set η : (𝓞 K)ˣ := (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit with hη_def
  let μ : (𝓞 K)ˣ := η ^ m
  have hμsq : (η ^ n : (𝓞 K)ˣ) = μ ^ 2 := by
    dsimp [μ]
    calc
      (η ^ n : (𝓞 K)ˣ) = η ^ (2 * m) := hm
      _ = (η ^ m) ^ 2 := by simp [pow_mul, mul_comm]
  let b : 𝓞 K := a * (μ : (𝓞 K)ˣ)
  refine ⟨b, ?_, ?_⟩
  · have hμconj : complexConj K μ = (μ⁻¹ : (𝓞 K)ˣ) := by
      dsimp [μ]
      simpa [hη_def] using conj_zeta_pow (p := p) (K := K) (hζ := hζ) m
    have hμcoe :
        ringOfIntegersComplexConj K ((μ : (𝓞 K)ˣ) : 𝓞 K) = (((μ⁻¹ : (𝓞 K)ˣ)) : 𝓞 K) := by
      apply RingOfIntegers.ext
      simpa [coe_ringOfIntegersComplexConj] using hμconj
    have huμinv : (η ^ n : (𝓞 K)ˣ) * μ⁻¹ = μ := by
      rw [hμsq]
      simp [pow_two, mul_assoc]
    calc
      ringOfIntegersComplexConj K b =
          ringOfIntegersComplexConj K a * ringOfIntegersComplexConj K ((μ : (𝓞 K)ˣ) : 𝓞 K) := by
            dsimp [b]
            simp
      _ = ((η ^ n : (𝓞 K)ˣ) : 𝓞 K) * a * (((μ⁻¹ : (𝓞 K)ˣ)) : 𝓞 K) := by
            dsimp [b]
            simpa [mul_assoc, hμcoe] using congrArg
              (fun x : 𝓞 K => x * ringOfIntegersComplexConj K (((μ : (𝓞 K)ˣ) : 𝓞 K))) hu
      _ = ((((η ^ n : (𝓞 K)ˣ) * μ⁻¹ : (𝓞 K)ˣ) : (𝓞 K)) * a) := by
            simp [mul_assoc, mul_comm]
      _ = (μ : (𝓞 K)ˣ) * a := by rw [huμinv]
      _ = b := by dsimp [b]; simp [mul_comm]
  · rw [Ideal.span_singleton_eq_span_singleton]
    dsimp [b]
    exact (associated_mul_unit_right a (μ : (𝓞 K)ˣ) μ.isUnit).symm

include hp_odd in
/-- The extra descent input removes the possible `-1` factor. -/
theorem exists_conj_fixed_associate_of_classification [IsCMField K]
    {hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (I : Ideal (𝓞 (NumberField.maximalRealSubfield K)))
    (a : 𝓞 K) (u : (𝓞 K)ˣ)
    (hIa : I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) = Ideal.span {a})
    (hu : ringOfIntegersComplexConj K a = u * a)
    (hclass : ∃ n k : ℕ, u = (-1 : (𝓞 K)ˣ) ^ k *
      (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit ^ n) :
    ∃ b : 𝓞 K, ringOfIntegersComplexConj K b = b ∧ Ideal.span {b} = Ideal.span {a} := by
  by_cases ha : a = 0
  · refine ⟨0, ?_, ?_⟩ <;> simp [ha]
  · obtain ⟨n, hn⟩ :=
      generator_unit_eq_zeta_pow (p := p) (hp_odd := hp_odd) (K := K) (hζ := hζ)
        I a u ha hIa hu hclass
    exact exists_conj_fixed_associate_of_zeta_pow
      (p := p) (hp_odd := hp_odd) (K := K) (hζ := hζ) a u hu ⟨n, hn⟩

/-- If `b` is fixed by conjugation, then it comes from `𝒪_{K⁺}`. -/
theorem mem_ringOfIntegers_of_conj_eq_self [IsCMField K]
    (b : 𝓞 K) (hb : ringOfIntegersComplexConj K b = b) :
    b ∈ Set.range (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :=
  (ringOfIntegersComplexConj_eq_self_iff K b).mp hb

end CyclotomicSetup

end BernoulliRegular

end

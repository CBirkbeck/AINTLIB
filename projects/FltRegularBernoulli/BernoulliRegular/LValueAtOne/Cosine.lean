module

public import BernoulliRegular.LValueAtOne.ComplexBounds
public import BernoulliRegular.LValueAtOne.DirichletBounds

/-!
# Cosine boundary values for `LValueAtOne`

This file contains the cosine-side Dirichlet bounds and the boundary-value
formula used in the even `L(1, χ)` evaluation.
-/

@[expose] public section

noncomputable section

open Filter
open scoped BigOperators Topology

namespace BernoulliRegular

section LValueAtOne

variable (p : ℕ) [hp : Fact p.Prime]

private lemma norm_one_sub_exp_two_pi_mul_I {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ =
      2 * Real.sin (Real.pi * x) := by
  have ht₀ : 0 < 2 * Real.pi * x := by nlinarith [hx₀, Real.pi_pos]
  have ht₂π : 2 * Real.pi * x < 2 * Real.pi := by nlinarith [hx₁, Real.pi_pos]
  simpa [mul_assoc] using norm_one_sub_exp_ofReal_mul_I ht₀ ht₂π

private lemma norm_one_sub_exp_two_pi_mul_I_pos {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    0 < ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
  rw [norm_one_sub_exp_two_pi_mul_I hx₀ hx₁]
  have hxπ : Real.pi * x ∈ Set.Ioo 0 Real.pi := by
    constructor <;> nlinarith [hx₀, hx₁, Real.pi_pos]
  exact mul_pos zero_lt_two (Real.sin_pos_of_mem_Ioo hxπ)

private lemma one_le_two_div_norm_one_sub_exp_two_pi_mul_I {x : ℝ}
    (hx₀ : 0 < x) (hx₁ : x < 1) :
    1 ≤ 2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
  apply (one_le_div (norm_one_sub_exp_two_pi_mul_I_pos hx₀ hx₁)).2
  calc
    ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖
        ≤ ‖(1 : ℂ)‖ + ‖Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := norm_sub_le _ _
    _ = 2 := by
      have hexp : ‖Complex.exp ((2 * Real.pi * x) * Complex.I)‖ = 1 := by
        simpa [mul_assoc] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
      rw [norm_one, hexp]
      norm_num

/-- Partial sums of the cosine kernel stay uniformly bounded away from the endpoints. -/
lemma norm_sum_range_cos_le {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i)‖ ≤
      2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
  let z : ℂ := Complex.exp ((2 * Real.pi * x) * Complex.I)
  have hz_ne_one : z ≠ 1 := by
    have hne := norm_pos_iff.mp (norm_one_sub_exp_two_pi_mul_I_pos hx₀ hx₁)
    simpa [z] using (sub_ne_zero.mp hne).symm
  have hre :
      ((∑ i ∈ Finset.range n, z ^ i).re : ℝ) =
        ∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [show z ^ i = Complex.exp (((2 * Real.pi * x * i : ℝ) : ℂ) * Complex.I) by
      rw [← Complex.exp_nat_mul]
      congr 1
      norm_num
      ring, Complex.exp_ofReal_mul_I_re]
  have hgeom :
      ‖∑ i ∈ Finset.range n, z ^ i‖ ≤ 2 / ‖z - 1‖ := by
    calc
      ‖∑ i ∈ Finset.range n, z ^ i‖ = ‖(z ^ n - 1) / (z - 1)‖ := by
        rw [geom_sum_eq hz_ne_one]
      _ = ‖z ^ n - 1‖ / ‖z - 1‖ := by rw [Complex.norm_div]
      _ ≤ 2 / ‖z - 1‖ := by
        have hden : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne_one)
        have hnum : ‖z ^ n - 1‖ ≤ 2 := by
          calc
            ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = 1 + 1 := by
              rw [norm_pow]
              have hz_norm : ‖z‖ = 1 := by
                simpa [z] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
              rw [hz_norm]
              norm_num
            _ = 2 := by norm_num
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hden.le)
  calc
    ‖∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i)‖
      = ‖((∑ i ∈ Finset.range n, z ^ i).re : ℝ)‖ := by rw [hre]
    _ ≤ ‖∑ i ∈ Finset.range n, z ^ i‖ := by
      simpa using (RCLike.norm_re_le_norm (∑ i ∈ Finset.range n, z ^ i))
    _ ≤ 2 / ‖z - 1‖ := hgeom
    _ = 2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
      simp only [z, norm_sub_rev]

/-- Continuity in the exponent of a single shifted cosine term. -/
lemma continuous_shiftedCosTerm (x : ℝ) (i : ℕ) :
    Continuous fun s : ℝ ↦
      Real.cos (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (s : ℂ)) := by
  refine Continuous.div continuous_const ?_ ?_
  · exact Continuous.const_cpow Complex.continuous_ofReal (Or.inl (Nat.cast_add_one_ne_zero i))
  · intro s h
    exact (Nat.cast_add_one_ne_zero i) ((Complex.cpow_eq_zero_iff _ _).mp h).1

/-- Repackage `hasSum_nat_cosZeta` with the harmless zero term removed. -/
lemma hasSum_shifted_cosZeta (x s : ℝ) (hs : 1 < s) :
    HasSum (fun n : ℕ ↦ Real.cos (2 * Real.pi * x * (n + 1)) / ((n + 1 : ℂ) ^ (s : ℂ)))
      (HurwitzZeta.cosZeta x s) := by
  let f : ℕ → ℂ := fun n ↦ Real.cos (2 * Real.pi * x * n) / ((n : ℂ) ^ (s : ℂ))
  have hfull : HasSum f (HurwitzZeta.cosZeta x s) := by
    simpa [f] using HurwitzZeta.hasSum_nat_cosZeta x (show 1 < ((s : ℂ)).re by simpa)
  have hshift : HasSum (fun n : ℕ ↦ f (n + 1)) (∑' n : ℕ, f (n + 1)) :=
    ((summable_nat_add_iff 1).2 hfull.summable).hasSum
  have hfull' : HasSum f (f 0 + ∑' n : ℕ, f (n + 1)) := hshift.zero_add
  have hvalue : (∑' n : ℕ, f (n + 1)) = HurwitzZeta.cosZeta x s := by
    have hs0 : ((s : ℂ)) ≠ 0 := by
      exact_mod_cast (show s ≠ 0 by linarith)
    have hf0 : f 0 = 0 := by
      norm_num [f, hs0]
    have := tendsto_nhds_unique hfull'.tendsto_sum_nat hfull.tendsto_sum_nat
    simpa [hf0] using this
  exact hvalue ▸ hshift.congr_fun (fun n ↦ by simp [f])

private lemma norm_sum_range_shifted_cos_le {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1)
    (n : ℕ) :
    ‖∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * (i + 1))‖ ≤
      4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
  let f : ℕ → ℝ := fun i ↦ Real.cos (2 * Real.pi * x * i)
  have hsum0 := Finset.sum_range_add f 1 n
  have hsum :
      ∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * (i + 1)) =
        ∑ i ∈ Finset.range (n + 1), Real.cos (2 * Real.pi * x * i) - 1 := by
    rw [Finset.sum_range_one] at hsum0
    calc
      ∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * (i + 1))
          = ∑ i ∈ Finset.range n, f (1 + i) := by simp [f, add_comm]
      _ = ∑ i ∈ Finset.range (n + 1), f i - f 0 :=
        eq_sub_iff_add_eq.mpr (by
          simpa [add_comm, add_left_comm, add_assoc, Nat.add_comm] using hsum0.symm)
      _ = ∑ i ∈ Finset.range (n + 1), Real.cos (2 * Real.pi * x * i) - 1 := by
        simp [f]
  rw [Real.norm_eq_abs, hsum]
  calc
    |∑ i ∈ Finset.range (n + 1), Real.cos (2 * Real.pi * x * i) - 1|
        ≤ |∑ i ∈ Finset.range (n + 1), Real.cos (2 * Real.pi * x * i) - 0| +
            |0 - (1 : ℝ)| := by
          simpa using
            abs_sub_le (∑ i ∈ Finset.range (n + 1), Real.cos (2 * Real.pi * x * i)) 0 1
    _ ≤ |∑ i ∈ Finset.range (n + 1), Real.cos (2 * Real.pi * x * i)| + 1 := by simp
    _ ≤ (2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖) + 1 := by
      have hcos :
          |∑ i ∈ Finset.range (n + 1), Real.cos (2 * Real.pi * x * i)| ≤
            2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
        simpa using norm_sum_range_cos_le hx₀ hx₁ (n + 1)
      exact add_le_add hcos le_rfl
    _ ≤ 2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ +
          2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
      have hdenom := one_le_two_div_norm_one_sub_exp_two_pi_mul_I hx₀ hx₁
      linarith
    _ = 4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by ring

/-- Uniform tail bound for the shifted cosine Dirichlet series on the half-line `s ≥ 1`. -/
lemma norm_sum_range_shifted_cos_term_le {x s : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) (hs : 1 ≤ s)
    (m n : ℕ) :
    ‖∑ i ∈ Finset.range n,
        Real.cos (2 * Real.pi * x * (m + i + 1)) / (((m + i + 1 : ℕ) : ℂ) ^ (s : ℂ))‖ ≤
      (8 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖) *
        (1 / (m + 1 : ℝ) ^ s) := by
  let a : ℕ → ℝ := fun k ↦ 1 / (k + 1 : ℝ) ^ s
  let z : ℕ → ℂ := fun k ↦ Real.cos (2 * Real.pi * x * (k + 1))
  have ha : Antitone a := by
    intro i j hij
    have hij' : (i + 1 : ℝ) ≤ j + 1 := by exact_mod_cast Nat.succ_le_succ hij
    have hi_pos : 0 < (i + 1 : ℝ) := by positivity
    have hs_nonneg : 0 ≤ s := le_trans zero_lt_one.le hs
    have hpow : (i + 1 : ℝ) ^ s ≤ (j + 1 : ℝ) ^ s :=
      Real.rpow_le_rpow hi_pos.le hij' hs_nonneg
    simpa [a, one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hi_pos _) hpow
  have ha_nonneg : ∀ k, 0 ≤ a k := by
    intro k
    positivity
  have hzbound :
      ∀ k, ‖∑ i ∈ Finset.range k, z i‖ ≤
        4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
    intro k
    rw [show (∑ i ∈ Finset.range k, z i) =
        ((∑ i ∈ Finset.range k, Real.cos (2 * Real.pi * x * (i + 1)) : ℝ) : ℂ) by
          simp [z, Complex.ofReal_sum]]
    rw [Complex.norm_real]
    simpa [Real.norm_eq_abs] using norm_sum_range_shifted_cos_le hx₀ hx₁ k
  calc
    ‖∑ i ∈ Finset.range n,
        Real.cos (2 * Real.pi * x * (m + i + 1)) / (((m + i + 1 : ℕ) : ℂ) ^ (s : ℂ))‖
        = ‖∑ i ∈ Finset.range n, a (m + i) • z (m + i)‖ := by
            congr 1
            refine Finset.sum_congr rfl fun i hi ↦ ?_
            have hcpow :
                (((m + i + 1 : ℕ) : ℂ) ^ (s : ℂ)) =
                  ((((m + i + 1 : ℕ) : ℝ) ^ s : ℝ) : ℂ) := by
              simpa using
                (Complex.ofReal_cpow (x := (m + i + 1 : ℝ)) (by positivity) (y := s)).symm
            rw [hcpow]
            simp [a, z, div_eq_mul_inv, mul_comm, mul_left_comm]
    _ ≤ (2 * (4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖)) * a m :=
          norm_sum_range_shift_smul_le_of_antitone_of_nonneg_of_bounded ha ha_nonneg hzbound m n
    _ = (8 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖) *
        (1 / (m + 1 : ℝ) ^ s) := by
          have hcoef :
              (2 * (4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖)) =
                8 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
            ring
          rw [hcoef]

/-- The partial sums of the cosine kernel with its constant (`i = 0`) term zeroed out stay
uniformly bounded away from the endpoints: on `(0, 1)` the sums
`∑ i ∈ range n, if i = 0 then 0 else cos (2 * π * x * i)` are bounded by
`4 / ‖1 - exp (2 * π * x * I)‖`. This is the coefficient sequence used in the Dirichlet-test
argument for the endpoint cosine series. -/
lemma norm_sum_range_ite_cos_le {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, if i = 0 then (0 : ℝ) else Real.cos (2 * Real.pi * x * i)‖ ≤
      4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  · have hsum := Finset.sum_range_add
      (fun i : ℕ ↦ if i = 0 then (0 : ℝ) else Real.cos (2 * Real.pi * x * i))
      1 (n - 1)
    have hn' : 1 + (n - 1) = n := by omega
    rw [hn', Finset.sum_range_one] at hsum
    rw [show (∑ i ∈ Finset.range n,
        if i = 0 then (0 : ℝ) else Real.cos (2 * Real.pi * x * i)) =
        ∑ i ∈ Finset.range (n - 1), Real.cos (2 * Real.pi * x * (i + 1)) by
      simpa [add_comm] using hsum]
    exact norm_sum_range_shifted_cos_le hx₀ hx₁ (n - 1)

/-- The endpoint cosine series converges on `(0, 1)` by Dirichlet's test. -/
lemma exists_tendsto_sum_range_cos_div_nat {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    ∃ l : ℝ,
      Tendsto
        (fun n ↦ ∑ i ∈ Finset.range n,
          if i = 0 then 0 else Real.cos (2 * Real.pi * x * i) / i)
        atTop (𝓝 l) := by
  let f : ℕ → ℝ := fun n ↦ if n = 0 then 1 else 1 / n
  let z : ℕ → ℝ := fun n ↦ if n = 0 then 0 else Real.cos (2 * Real.pi * x * n)
  have hf : Antitone f := by
    intro a b hab
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · simp [f]
      · simp [f, hb.ne']
        have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast Nat.succ_le_of_lt hb
        simpa [one_div] using one_div_le_one_div_of_le zero_lt_one hb1
    · have hb : 0 < b := lt_of_lt_of_le ha hab
      simp [f, ha.ne', (Nat.ne_of_gt hb)]
      have ha' : (0 : ℝ) < a := by exact_mod_cast ha
      have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
      simpa [one_div] using one_div_le_one_div_of_le ha' hab'
  have hf0 : Tendsto f atTop (𝓝 0) := by
    apply (tendsto_add_atTop_iff_nat 1).1
    simpa [f]
      using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ ↦ 1 / (n + 1 : ℝ)) atTop (𝓝 0))
  have hbound :
      ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤
        4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ :=
    fun n ↦ norm_sum_range_ite_cos_le hx₀ hx₁ n
  have hcauchy := hf.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 hbound
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨l, ?_⟩
  have hseries :
      (fun n ↦ ∑ i ∈ Finset.range n, f i • z i) =
        fun n ↦ ∑ i ∈ Finset.range n,
          if i = 0 then 0 else Real.cos (2 * Real.pi * x * i) / i := by
    funext n
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [f, z]
    · simp [f, z, hi.ne', smul_eq_mul, div_eq_mul_inv, mul_comm]
  exact hseries ▸ hl

/-- The endpoint cosine series converges to the classical boundary value
`-log (2 * sin (πx))` on `(0, 1)`. -/
lemma tendsto_sum_range_cos_div_nat {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n, if i = 0 then 0 else Real.cos (2 * Real.pi * x * i) / i)
      atTop (𝓝 (-Real.log (2 * Real.sin (Real.pi * x)))) := by
  obtain ⟨l, hl⟩ := exists_tendsto_sum_range_cos_div_nat hx₀ hx₁
  let coeff : ℕ → ℝ := fun n ↦
    if n = 0 then 0 else Real.cos (2 * Real.pi * x * n) / n
  have habel :
      Tendsto (fun r : ℝ ↦ ∑' n, coeff n * r ^ n) (𝓝[<] 1) (𝓝 l) :=
    Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  have hcoeff :
      Set.EqOn
        (fun r : ℝ ↦ ∑' n, coeff n * r ^ n)
        (fun r : ℝ ↦
          -Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖)
        (Set.Ioo 0 1) := by
    intro r hr
    have hr₀ : 0 ≤ r := hr.1.le
    have hr₁ : r < 1 := hr.2
    calc
      ∑' n : ℕ, coeff n * r ^ n
          = ∑' n : ℕ, (r ^ n / n) * Real.cos (2 * Real.pi * x * n) := by
              refine tsum_congr fun n : ℕ ↦ ?_
              rcases n.eq_zero_or_pos with rfl | hn
              · simp [coeff]
              · simp [coeff, hn.ne', div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = -Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖ :=
            (hasSum_mul_rpow_cos x r hr₀ hr₁).tsum_eq
  have habel' :
      Tendsto
        (fun r : ℝ ↦
          -Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖)
        (𝓝[<] 1) (𝓝 l) :=
    Tendsto.congr' (hcoeff.eventuallyEq_of_mem (Ioo_mem_nhdsLT zero_lt_one)) habel
  have hzero :
      (1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I) ≠ 0 := by
    exact norm_pos_iff.mp (norm_one_sub_exp_two_pi_mul_I_pos hx₀ hx₁)
  have hcont :
      Tendsto
        (fun r : ℝ ↦
          -Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖)
        (𝓝[<] 1)
        (𝓝 (-Real.log ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖)) := by
    have hinner :
        ContinuousAt
          (fun r : ℝ ↦ (1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)) 1 :=
      continuousAt_const.sub
        (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
    have hnorm :
        ContinuousAt
          (fun r : ℝ ↦
            ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖) 1 :=
      continuous_norm.continuousAt.comp hinner
    have hnorm_ne :
        ‖(1 : ℂ) - ((1 : ℝ) : ℂ) *
          Complex.exp ((2 * Real.pi * x) * Complex.I)‖ ≠ 0 := by
      simpa using (norm_ne_zero_iff.mpr hzero)
    have hlog :
        ContinuousAt
          (fun r : ℝ ↦
            Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖) 1 :=
      hnorm.log hnorm_ne
    convert tendsto_nhdsWithin_of_tendsto_nhds hlog.neg.tendsto using 2
    rw [Pi.neg_apply]
    simp
  have hnorm_value :
      ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ =
        2 * Real.sin (Real.pi * x) := by
    exact norm_one_sub_exp_two_pi_mul_I hx₀ hx₁
  have hl_eq : l = -Real.log (2 * Real.sin (Real.pi * x)) :=
    tendsto_nhds_unique habel' (by simpa [hnorm_value] using hcont)
  simpa [hl_eq] using hl

/-- The shifted endpoint cosine series converges to the same boundary value. -/
lemma tendsto_sum_range_shifted_cos_one {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    Tendsto
      (fun n : ℕ ↦ ∑ i ∈ Finset.range n,
        Real.cos (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (1 : ℂ)))
      atTop (nhds ((-Real.log (2 * Real.sin (Real.pi * x)) : ℝ) : ℂ)) := by
  let partialSums : ℕ → ℂ := fun n ↦
    ((∑ i ∈ Finset.range n,
      if i = 0 then 0 else Real.cos (2 * Real.pi * x * i) / i : ℝ) : ℂ)
  have hbase : Tendsto partialSums atTop
      (nhds (((-Real.log (2 * Real.sin (Real.pi * x)) : ℝ) : ℂ))) := by
    simpa [partialSums] using (tendsto_sum_range_cos_div_nat hx₀ hx₁).ofReal
  have hshifted : Tendsto (fun n : ℕ ↦ partialSums (n + 1)) atTop
      (nhds (((-Real.log (2 * Real.sin (Real.pi * x)) : ℝ) : ℂ))) :=
    (tendsto_add_atTop_iff_nat 1).2 hbase
  refine hshifted.congr' <| Filter.Eventually.of_forall fun n ↦ ?_
  have hsum :=
    Finset.sum_range_add
      (fun i : ℕ ↦
        (((if i = 0 then 0 else Real.cos (2 * Real.pi * x * i) / i : ℝ)) : ℂ))
      1 n
  simpa [partialSums, add_comm, add_left_comm, add_assoc] using hsum

/-- The shifted cosine Dirichlet partial sums are uniformly Cauchy on the half-line `s ≥ 1`. -/
lemma uniformCauchySeqOn_shiftedCosPartialSums {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    UniformCauchySeqOn
      (fun n (s : ℝ) ↦ ∑ i ∈ Finset.range n,
        Real.cos (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (s : ℂ)))
      atTop (Set.Ici 1) := by
  rw [Metric.uniformCauchySeqOn_iff]
  let bound : ℝ :=
    8 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖
  have hdenom_pos := norm_one_sub_exp_two_pi_mul_I_pos hx₀ hx₁
  have hbound_pos : 0 < bound := by
    positivity
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (div_pos hε hbound_pos)
  refine ⟨N, ?_⟩
  have htail_bound :
      ∀ ⦃m n : ℕ⦄, N ≤ m → m ≤ n → ∀ s ∈ Set.Ici (1 : ℝ),
        dist
            (∑ i ∈ Finset.range m,
              Real.cos (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (s : ℂ)))
            (∑ i ∈ Finset.range n,
              Real.cos (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (s : ℂ)))
          < ε := by
    intro m n hm hmn s hs
    let term : ℕ → ℂ := fun k ↦
      Real.cos (2 * Real.pi * x * (k + 1)) / ((k + 1 : ℂ) ^ (s : ℂ))
    have hsplit :
        ∑ i ∈ Finset.range n, term i =
          ∑ i ∈ Finset.range m, term i + ∑ i ∈ Finset.range (n - m), term (m + i) := by
      simpa [term, Nat.add_sub_of_le hmn] using Finset.sum_range_add term m (n - m)
    have hs' : 1 ≤ s := hs
    rw [dist_eq_norm, norm_sub_rev]
    calc
      ‖∑ i ∈ Finset.range n, term i - ∑ i ∈ Finset.range m, term i‖
          = ‖∑ i ∈ Finset.range (n - m), term (m + i)‖ := by
              rw [hsplit]
              ring_nf
      _ ≤ bound * (1 / (m + 1 : ℝ) ^ s) := by
            simpa [bound, term, add_assoc, add_comm, add_left_comm] using
              norm_sum_range_shifted_cos_term_le (x := x) hx₀ hx₁ hs' m (n - m)
      _ ≤ bound * (1 / (m + 1 : ℝ)) := by
            have hm1 : 1 ≤ (m + 1 : ℝ) := by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
            have hpow : (m + 1 : ℝ) ^ (1 : ℝ) ≤ (m + 1 : ℝ) ^ s := by
              simpa using Real.rpow_le_rpow_of_exponent_le hm1 hs'
            have hpow_inv : 1 / (m + 1 : ℝ) ^ s ≤ 1 / (m + 1 : ℝ) := by
              simpa [Real.rpow_one] using
                (one_div_le_one_div_of_le (show 0 < (m + 1 : ℝ) ^ (1 : ℝ) by positivity) hpow)
            exact mul_le_mul_of_nonneg_left hpow_inv hbound_pos.le
      _ ≤ bound * (1 / (N + 1 : ℝ)) := by
            have hm_inv : 1 / (m + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) :=
              one_div_le_one_div_of_le (show 0 < (N + 1 : ℝ) by positivity)
                (by exact_mod_cast Nat.succ_le_succ hm)
            exact mul_le_mul_of_nonneg_left hm_inv hbound_pos.le
      _ < bound * (ε / bound) :=
            mul_lt_mul_of_pos_left hN hbound_pos
      _ = ε := by
            field_simp [hbound_pos.ne']
  intro m hm n hn s hs
  rcases le_total m n with hmn | hnm
  · exact htail_bound hm hmn s hs
  · simpa [dist_comm] using htail_bound hn hnm s hs

/-- The cosine zeta function takes the classical boundary value at `s = 1` for `x ∈ (0, 1)`. -/
theorem cosZeta_one_eq_boundary {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    HurwitzZeta.cosZeta x 1 = (((-Real.log (2 * Real.sin (Real.pi * x)) : ℝ) : ℂ)) := by
  let boundary : ℂ := (((-Real.log (2 * Real.sin (Real.pi * x)) : ℝ) : ℂ))
  let partialSums : ℕ → ℝ → ℂ := fun n s ↦
    ∑ i ∈ Finset.range n,
      Real.cos (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (s : ℂ))
  let limit : ℝ → ℂ := fun s ↦ if hs : s = 1 then boundary else HurwitzZeta.cosZeta x s
  have hCauchy : UniformCauchySeqOn partialSums atTop (Set.Ici 1) := by
    simpa [partialSums] using uniformCauchySeqOn_shiftedCosPartialSums (x := x) hx₀ hx₁
  have hpoint : ∀ s ∈ Set.Ici (1 : ℝ),
      Tendsto (fun n ↦ partialSums n s) atTop (𝓝 (limit s)) := by
    intro s hs
    by_cases hs1 : s = 1
    · simpa [partialSums, limit, hs1, boundary] using
        tendsto_sum_range_shifted_cos_one (x := x) hx₀ hx₁
    · have hslt : 1 < s := lt_of_le_of_ne hs (by simpa [eq_comm] using hs1)
      simpa [partialSums, limit, hs1] using
        (hasSum_shifted_cosZeta (x := x) s hslt).tendsto_sum_nat
  have hunif : TendstoUniformlyOn partialSums limit atTop (Set.Ici 1) :=
    hCauchy.tendstoUniformlyOn_of_tendsto hpoint
  have hcont : ContinuousOn limit (Set.Ici (1 : ℝ)) := by
    apply hunif.continuousOn
    refine Frequently.of_forall fun n ↦ ?_
    classical
    dsimp [partialSums]
    exact Continuous.continuousOn <|
      continuous_finsetSum _ fun i _ ↦ continuous_shiftedCosTerm x i
  have hlimit_right : Tendsto limit (𝓝[Set.Ioi 1] 1) (𝓝 boundary) := by
    have hlimit_Ici : Tendsto limit (𝓝[Set.Ici 1] 1) (𝓝 boundary) := by
      simpa [limit, boundary] using (hcont 1 (by simp)).tendsto
    exact hlimit_Ici.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  have hlimit_eq : limit =ᶠ[𝓝[Set.Ioi 1] 1] fun s : ℝ ↦ HurwitzZeta.cosZeta x s := by
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    have hslt : 1 < s := by simpa using hs
    simp [limit, ne_of_gt hslt]
  have hcos_right : Tendsto (fun s : ℝ ↦ HurwitzZeta.cosZeta x s) (𝓝[Set.Ioi 1] 1)
      (𝓝 boundary) :=
    Tendsto.congr' hlimit_eq hlimit_right
  have hcos_cont : Tendsto (fun s : ℝ ↦ HurwitzZeta.cosZeta x s) (𝓝[Set.Ioi 1] 1)
      (𝓝 (HurwitzZeta.cosZeta x 1)) := by
    have hxadd : (x : UnitAddCircle) ≠ 0 := by
      intro hxzero
      rw [AddCircle.coe_eq_zero_iff] at hxzero
      rcases hxzero with ⟨n, hn⟩
      have hn' : (n : ℝ) = x := by simpa using hn
      have hn_pos : (0 : ℝ) < n := by nlinarith [hx₀, hn']
      have hn_lt_one : (n : ℝ) < 1 := by nlinarith [hx₁, hn']
      have hn_pos_int : 0 < n := by exact_mod_cast hn_pos
      have hn_lt_one_int : n < 1 := by exact_mod_cast hn_lt_one
      omega
    have hcomplex : Tendsto (fun z : ℂ ↦ HurwitzZeta.cosZeta x z) (𝓝 (1 : ℂ))
        (𝓝 (HurwitzZeta.cosZeta x 1)) :=
      (HurwitzZeta.differentiableAt_cosZeta (a := (x : UnitAddCircle)) (s := (1 : ℂ))
        (Or.inr hxadd)).continuousAt.tendsto
    have hreal : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝 (1 : ℝ)) (𝓝 (1 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto
    have hcomp : Tendsto (fun s : ℝ ↦ HurwitzZeta.cosZeta x (s : ℂ)) (𝓝 (1 : ℝ))
        (𝓝 (HurwitzZeta.cosZeta x 1)) := by
      simpa [Function.comp_def] using hcomplex.comp hreal
    exact hcomp.mono_left nhdsWithin_le_nhds
  simpa [boundary] using (tendsto_nhds_unique hcos_right hcos_cont).symm

/-- For a nonzero residue class, `cosZeta` at the corresponding point of `UnitAddCircle`
takes the classical boundary value used on the even side of the `L(1, χ)` formula. -/
theorem cosZeta_toAddCircle_one_eq_boundary {a : ZMod p} (ha : a ≠ 0) :
    HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 =
      (((-Real.log (2 * Real.sin (Real.pi * (a.val / p : ℝ))) : ℝ) : ℂ)) := by
  have hxIoo := zmod_val_div_prime_mem_Ioo (p := p) ha
  rw [ZMod.toAddCircle_apply]
  exact cosZeta_one_eq_boundary (x := (a.val / p : ℝ)) hxIoo.1 hxIoo.2

/-- The norm of `1 - ζ_p^a` matches the trigonometric boundary term. -/
lemma norm_one_sub_stdAddChar {a : ZMod p} (ha : a ≠ 0) :
    ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ =
      2 * Real.sin (Real.pi * (a.val / p : ℝ)) := by
  have hxIoo := zmod_val_div_prime_mem_Ioo (p := p) ha
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  have hexp :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a.val : ℂ) / (p : ℂ)) =
        Complex.exp ((((2 * Real.pi * (a.val / p : ℝ)) : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    ring
  rw [hexp]
  simpa [mul_assoc] using norm_one_sub_exp_two_pi_mul_I hxIoo.1 hxIoo.2

end LValueAtOne

end BernoulliRegular

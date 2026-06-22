module

public import BernoulliRegular.LValueAtOne.ComplexBounds
public import BernoulliRegular.LValueAtOne.DirichletBounds

/-!
# Sine boundary values for `LValueAtOne`

This file contains the sine-side Dirichlet bounds and the boundary-value
formula used in the odd `L(1, χ)` evaluation.
-/

@[expose] public section

noncomputable section

open Filter
open scoped BigOperators Topology

namespace BernoulliRegular

section LValueAtOne

variable (p : ℕ) [hp : Fact p.Prime]

/-- Partial sums of the sine kernel stay uniformly bounded away from the endpoints. -/
lemma norm_sum_range_sin_le {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, Real.sin (2 * Real.pi * x * i)‖ ≤
      2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
  let z : ℂ := Complex.exp ((2 * Real.pi * x) * Complex.I)
  have hz_ne_one : z ≠ 1 := by
    intro hz
    have hexp : Complex.exp ((2 * Real.pi * x) * Complex.I) = 1 := by simpa [z] using hz
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hexp
    have him : 2 * Real.pi * x = (m : ℝ) * (2 * Real.pi) := by
      simpa using congrArg Complex.im hm
    have hm_pos : (0 : ℝ) < m := by nlinarith [Real.pi_pos, hx₀, him]
    have hm_lt_one : (m : ℝ) < 1 := by nlinarith [Real.pi_pos, hx₁, him]
    have hm_pos_int : 0 < m := by exact_mod_cast hm_pos
    have hm_lt_one_int : m < 1 := by exact_mod_cast hm_lt_one
    omega
  have him :
      ((∑ i ∈ Finset.range n, z ^ i).im : ℝ) =
        ∑ i ∈ Finset.range n, Real.sin (2 * Real.pi * x * i) := by
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [show z ^ i = Complex.exp (((2 * Real.pi * x * i : ℝ) : ℂ) * Complex.I) by
      rw [← Complex.exp_nat_mul]
      congr 1
      norm_num
      ring, Complex.exp_ofReal_mul_I_im]
  have hgeom :
      ‖∑ i ∈ Finset.range n, z ^ i‖ ≤ 2 / ‖z - 1‖ := by
    calc
      ‖∑ i ∈ Finset.range n, z ^ i‖ = ‖(z ^ n - 1) / (z - 1)‖ := by rw [geom_sum_eq hz_ne_one]
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
              simp
            _ = 2 := by norm_num
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hden.le)
  calc
    ‖∑ i ∈ Finset.range n, Real.sin (2 * Real.pi * x * i)‖
      = ‖((∑ i ∈ Finset.range n, z ^ i).im : ℝ)‖ := by rw [him]
    _ ≤ ‖∑ i ∈ Finset.range n, z ^ i‖ := by
      simpa using (RCLike.norm_im_le_norm (∑ i ∈ Finset.range n, z ^ i))
    _ ≤ 2 / ‖z - 1‖ := hgeom
    _ = 2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
      simp [z, norm_sub_rev]

/-- Continuity in the exponent of a single shifted sine term. -/
lemma continuous_shiftedSinTerm (x : ℝ) (i : ℕ) :
    Continuous fun s : ℝ ↦
      Real.sin (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (s : ℂ)) := by
  refine Continuous.div continuous_const ?_ ?_
  · exact Continuous.const_cpow Complex.continuous_ofReal (Or.inl (Nat.cast_add_one_ne_zero i))
  · intro s h
    exact (Nat.cast_add_one_ne_zero i) ((Complex.cpow_eq_zero_iff _ _).mp h).1

/-- Repackage `hasSum_nat_sinZeta` with the harmless zero term removed. -/
lemma hasSum_shifted_sinZeta (x s : ℝ) (hs : 1 < s) :
    HasSum (fun n : ℕ ↦ Real.sin (2 * Real.pi * x * (n + 1)) / ((n + 1 : ℂ) ^ (s : ℂ)))
      (HurwitzZeta.sinZeta x s) := by
  let f : ℕ → ℂ := fun n ↦ Real.sin (2 * Real.pi * x * n) / ((n : ℂ) ^ (s : ℂ))
  have hfull : HasSum f (HurwitzZeta.sinZeta x s) := by
    simpa [f] using HurwitzZeta.hasSum_nat_sinZeta x (show 1 < ((s : ℂ)).re by simpa)
  have hshift : HasSum (fun n : ℕ ↦ f (n + 1)) (∑' n : ℕ, f (n + 1)) :=
    ((summable_nat_add_iff 1).2 hfull.summable).hasSum
  have hfull' : HasSum f (f 0 + ∑' n : ℕ, f (n + 1)) := hshift.zero_add
  have hvalue : (∑' n : ℕ, f (n + 1)) = HurwitzZeta.sinZeta x s := by
    have := tendsto_nhds_unique hfull'.tendsto_sum_nat hfull.tendsto_sum_nat
    simpa [f, hs.ne'] using this
  exact hvalue ▸ hshift.congr_fun (fun n ↦ by simp [f])

/-- Uniform tail bound for the shifted sine Dirichlet series on the half-line `s ≥ 1`. -/
lemma norm_sum_range_shifted_sin_term_le {x s : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) (hs : 1 ≤ s)
    (m n : ℕ) :
    ‖∑ i ∈ Finset.range n,
        Real.sin (2 * Real.pi * x * (m + i + 1)) / (((m + i + 1 : ℕ) : ℂ) ^ (s : ℂ))‖ ≤
      (4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖) *
        (1 / (m + 1 : ℝ) ^ s) := by
  let a : ℕ → ℝ := fun k ↦ 1 / (k + 1 : ℝ) ^ s
  let z : ℕ → ℂ := fun k ↦ Real.sin (2 * Real.pi * x * (k + 1))
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
        2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
    intro k
    have hsum :
        ∑ i ∈ Finset.range k, Real.sin (2 * Real.pi * x * (i + 1)) =
          ∑ i ∈ Finset.range (k + 1), Real.sin (2 * Real.pi * x * i) := by
      simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using
        (Finset.sum_range_add (fun i ↦ Real.sin (2 * Real.pi * x * i)) 1 k).symm
    rw [show (∑ i ∈ Finset.range k, z i) =
        ((∑ i ∈ Finset.range k, Real.sin (2 * Real.pi * x * (i + 1)) : ℝ) : ℂ) by
          simp [z, Complex.ofReal_sum]]
    rw [Complex.norm_real, hsum]
    exact norm_sum_range_sin_le hx₀ hx₁ (k + 1)
  calc
    ‖∑ i ∈ Finset.range n,
        Real.sin (2 * Real.pi * x * (m + i + 1)) / (((m + i + 1 : ℕ) : ℂ) ^ (s : ℂ))‖
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
    _ ≤ (2 * (2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖)) * a m :=
          norm_sum_range_shift_smul_le_of_antitone_of_nonneg_of_bounded ha ha_nonneg hzbound m n
    _ = (4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖) * (1 / (m + 1 : ℝ) ^ s) := by
          have hcoef :
              (2 * (2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖)) =
                4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
            ring
          rw [hcoef]

/-- The endpoint sine series converges on `(0, 1)` by Dirichlet's test. -/
lemma exists_tendsto_sum_range_sin_div_nat {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    ∃ l : ℝ,
      Tendsto
        (fun n ↦ ∑ i ∈ Finset.range n, if i = 0 then 0 else Real.sin (2 * Real.pi * x * i) / i)
        atTop (𝓝 l) := by
  let f : ℕ → ℝ := fun n ↦ if n = 0 then 1 else 1 / n
  let z : ℕ → ℝ := fun n ↦ if n = 0 then 0 else Real.sin (2 * Real.pi * x * n)
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
  have hpartial :
      ∀ n, ∑ i ∈ Finset.range n, z i = ∑ i ∈ Finset.range n, Real.sin (2 * Real.pi * x * i) := by
    intro n
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [z]
    · simp [z, hi.ne']
  have hbound :
      ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤
        2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
    intro n
    rw [hpartial]
    exact norm_sum_range_sin_le hx₀ hx₁ n
  have hcauchy := hf.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 hbound
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨l, ?_⟩
  have hseries :
      (fun n ↦ ∑ i ∈ Finset.range n, f i • z i) =
        fun n ↦ ∑ i ∈ Finset.range n, if i = 0 then 0 else Real.sin (2 * Real.pi * x * i) / i := by
    funext n
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [f, z]
    · simp [f, z, hi.ne', smul_eq_mul, div_eq_mul_inv, mul_comm]
  exact hseries ▸ hl

/-- The endpoint sine series converges to the classical boundary value
`π * (1 / 2 - x)` on `(0, 1)`. -/
lemma tendsto_sum_range_sin_div_nat {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n, if i = 0 then 0 else Real.sin (2 * Real.pi * x * i) / i)
      atTop (𝓝 (Real.pi * (1 / 2 - x))) := by
  obtain ⟨l, hl⟩ := exists_tendsto_sum_range_sin_div_nat hx₀ hx₁
  let coeff : ℕ → ℝ := fun n ↦
    if n = 0 then 0 else Real.sin (2 * Real.pi * x * n) / n
  have habel :
      Tendsto (fun r : ℝ ↦ ∑' n, coeff n * r ^ n) (𝓝[<] 1) (𝓝 l) :=
    Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  have hcoeff :
      Set.EqOn
        (fun r : ℝ ↦ ∑' n, coeff n * r ^ n)
        (fun r : ℝ ↦
          (-Complex.log ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im)
        (Set.Ioo 0 1) := by
    intro r hr
    have hr₀ : 0 ≤ r := hr.1.le
    have hr₁ : r < 1 := hr.2
    calc
      ∑' n : ℕ, coeff n * r ^ n
          = ∑' n : ℕ, (r ^ n / n) * Real.sin (2 * Real.pi * x * n) := by
              refine tsum_congr fun n : ℕ ↦ ?_
              rcases n.eq_zero_or_pos with rfl | hn
              · simp [coeff]
              · simp [coeff, hn.ne', div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = (-Complex.log ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im :=
            (hasSum_mul_rpow_sin x r hr₀ hr₁).tsum_eq
  have habel' :
      Tendsto
        (fun r : ℝ ↦
          (-Complex.log ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im)
        (𝓝[<] 1) (𝓝 l) :=
    Tendsto.congr' (hcoeff.eventuallyEq_of_mem (Ioo_mem_nhdsLT zero_lt_one)) habel
  have hslit :
      ((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    have hre :
        (((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)).re : ℝ) =
          2 * Real.sin (Real.pi * x) ^ 2 := by
      have hExp :
          (Complex.exp ((2 * Real.pi * x) * Complex.I)).re = Real.cos (2 * Real.pi * x) := by
        simpa using (Complex.exp_ofReal_mul_I_re (2 * Real.pi * x))
      rw [Complex.sub_re, Complex.one_re, hExp]
      have hsq : 1 - Real.cos (2 * Real.pi * x) = 2 * Real.sin (Real.pi * x) ^ 2 := by
        rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring, Real.cos_two_mul]
        nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x)]
      exact hsq
    rw [hre]
    have hxπ : Real.pi * x ∈ Set.Ioo 0 Real.pi := by
      constructor <;> nlinarith [hx₀, hx₁, Real.pi_pos]
    have hsin : 0 < Real.sin (Real.pi * x) := Real.sin_pos_of_mem_Ioo hxπ
    positivity
  have hcont :
      Tendsto
        (fun r : ℝ ↦
          (-Complex.log ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im)
        (𝓝[<] 1) (𝓝 (Real.pi * (1 / 2 - x))) := by
    have hz :
        Tendsto
          (fun r : ℝ ↦ (1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))
          (𝓝[<] 1)
          (𝓝 ((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I))) := by
      have hcont :
          Continuous fun r : ℝ ↦
            (1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I) := by
        continuity
      have hcont1 :
          ContinuousAt
            (fun r : ℝ ↦ (1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)) 1 :=
        hcont.continuousAt
      convert tendsto_nhdsWithin_of_tendsto_nhds hcont1.tendsto using 1
      · simp
    have hlog :
        Tendsto
          (fun r : ℝ ↦
            Complex.log ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)))
          (𝓝[<] 1)
          (𝓝 (Complex.log ((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)))) :=
      hz.clog hslit
    have him0 :
        Tendsto
          (fun r : ℝ ↦
            (Complex.log ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im)
          (𝓝[<] 1)
          (𝓝 ((Complex.log (((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)))).im)) :=
      Complex.continuous_im.continuousAt.tendsto.comp hlog
    have hnegim :
        Tendsto
          (fun r : ℝ ↦
            -((Complex.log ((1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I))).im))
          (𝓝[<] 1)
          (𝓝 (-((Complex.log (((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)))).im))) :=
      him0.neg
    have ht₀ : 0 < 2 * Real.pi * x := by nlinarith [hx₀, Real.pi_pos]
    have ht₂π : 2 * Real.pi * x < 2 * Real.pi := by nlinarith [hx₁, Real.pi_pos]
    have hvalue := neg_log_one_sub_exp_ofReal_mul_I_im ht₀ ht₂π
    have hvalue' :
        -((Complex.log (((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)))).im) =
          Real.pi * (1 / 2 - x) := by
      calc
        -((Complex.log (((1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)))).im) =
            Real.pi / 2 - (2 * Real.pi * x) / 2 := by
              simpa using hvalue
        _ = Real.pi * (1 / 2 - x) := by ring
    simpa [hvalue'] using hnegim
  have hl_eq : l = Real.pi * (1 / 2 - x) := tendsto_nhds_unique habel' hcont
  simpa [hl_eq] using hl

/-- The shifted endpoint sine series converges to the same boundary value. -/
lemma tendsto_sum_range_shifted_sin_one {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    Tendsto
      (fun n : ℕ ↦ ∑ i ∈ Finset.range n,
        Real.sin (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (1 : ℂ)))
      atTop (nhds (Real.pi * (1 / 2 - x) : ℂ)) := by
  let F : ℕ → ℂ := fun n ↦
    ((∑ i ∈ Finset.range n, if i = 0 then 0 else Real.sin (2 * Real.pi * x * i) / i : ℝ) : ℂ)
  have hbase : Tendsto F atTop (nhds (Real.pi * (1 / 2 - x) : ℂ)) := by
    simpa [F] using (tendsto_sum_range_sin_div_nat hx₀ hx₁).ofReal
  have hshifted : Tendsto (fun n : ℕ ↦ F (n + 1)) atTop (nhds (Real.pi * (1 / 2 - x) : ℂ)) :=
    (tendsto_add_atTop_iff_nat 1).2 hbase
  refine hshifted.congr' <| Filter.Eventually.of_forall fun n ↦ ?_
  have hsum :=
    Finset.sum_range_add
      (fun i : ℕ ↦ (((if i = 0 then 0 else Real.sin (2 * Real.pi * x * i) / i : ℝ)) : ℂ)) 1 n
  simpa [F, add_comm, add_left_comm, add_assoc] using hsum

/-- The shifted sine Dirichlet partial sums are uniformly Cauchy on the half-line `s ≥ 1`. -/
lemma uniformCauchySeqOn_shiftedSinPartialSums {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    UniformCauchySeqOn
      (fun n (s : ℝ) ↦ ∑ i ∈ Finset.range n,
        Real.sin (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (s : ℂ)))
      atTop (Set.Ici 1) := by
  rw [Metric.uniformCauchySeqOn_iff]
  let B : ℝ :=
    4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖
  have hxπ : Real.pi * x ∈ Set.Ioo 0 Real.pi := by
    constructor <;> nlinarith [hx₀, hx₁, Real.pi_pos]
  have hsin : 0 < Real.sin (Real.pi * x) := Real.sin_pos_of_mem_Ioo hxπ
  have hdenom : 0 < ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
    have htwo : 0 < 2 * Real.sin (Real.pi * x) := by positivity
    have hunit_ne :
        Real.cos (Real.pi * x - Real.pi / 2) +
            Real.sin (Real.pi * x - Real.pi / 2) * Complex.I ≠ 0 := by
      have hunit_pos :
          0 < ‖Real.cos (Real.pi * x - Real.pi / 2) +
              Real.sin (Real.pi * x - Real.pi / 2) * Complex.I‖ := by
        have hunit_pos' :
            0 < ‖Complex.cos ((Real.pi * x - Real.pi / 2 : ℝ) : ℂ) +
                Complex.sin ((Real.pi * x - Real.pi / 2 : ℝ) : ℂ) * Complex.I‖ := by
          rw [Complex.norm_cos_add_sin_mul_I]
          norm_num
        simpa [Complex.ofReal_cos, Complex.ofReal_sin] using hunit_pos'
      exact norm_pos_iff.mp hunit_pos
    have hfac_ne : ((2 * Real.sin (Real.pi * x) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast htwo.ne'
    have hzero : (1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I) ≠ 0 := by
      have hrewrite :
          (1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I) =
            (2 * Real.sin ((2 * Real.pi * x) / 2) : ℝ) *
              (Real.cos ((2 * Real.pi * x) / 2 - Real.pi / 2) +
                Real.sin ((2 * Real.pi * x) / 2 - Real.pi / 2) * Complex.I) := by
        simpa [mul_assoc] using one_sub_exp_ofReal_mul_I (2 * Real.pi * x)
      rw [hrewrite]
      simpa [show (2 * Real.pi * x) / 2 = Real.pi * x by ring] using mul_ne_zero hfac_ne hunit_ne
    exact norm_pos_iff.mpr hzero
  have hB_pos : 0 < B := by
    positivity
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (div_pos hε hB_pos)
  refine ⟨N, ?_⟩
  have htail_bound :
      ∀ ⦃m n : ℕ⦄, N ≤ m → m ≤ n → ∀ s ∈ Set.Ici (1 : ℝ),
        dist
            (∑ i ∈ Finset.range m,
              Real.sin (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (s : ℂ)))
            (∑ i ∈ Finset.range n,
              Real.sin (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (s : ℂ)))
          < ε := by
    intro m n hm hmn s hs
    let term : ℕ → ℂ := fun k ↦
      Real.sin (2 * Real.pi * x * (k + 1)) / ((k + 1 : ℂ) ^ (s : ℂ))
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
      _ ≤ B * (1 / (m + 1 : ℝ) ^ s) := by
            simpa [B, term, add_assoc, add_comm, add_left_comm] using
              norm_sum_range_shifted_sin_term_le (x := x) hx₀ hx₁ hs' m (n - m)
      _ ≤ B * (1 / (m + 1 : ℝ)) := by
            have hm1 : 1 ≤ (m + 1 : ℝ) := by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
            have hpow : (m + 1 : ℝ) ^ (1 : ℝ) ≤ (m + 1 : ℝ) ^ s := by
              simpa using Real.rpow_le_rpow_of_exponent_le hm1 hs'
            have hpow_inv : 1 / (m + 1 : ℝ) ^ s ≤ 1 / (m + 1 : ℝ) := by
              simpa [Real.rpow_one] using
                (one_div_le_one_div_of_le (show 0 < (m + 1 : ℝ) ^ (1 : ℝ) by positivity) hpow)
            exact mul_le_mul_of_nonneg_left hpow_inv hB_pos.le
      _ ≤ B * (1 / (N + 1 : ℝ)) := by
            have hm_inv : 1 / (m + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) :=
              one_div_le_one_div_of_le (show 0 < (N + 1 : ℝ) by positivity)
                (by exact_mod_cast Nat.succ_le_succ hm)
            exact mul_le_mul_of_nonneg_left hm_inv hB_pos.le
      _ < B * (ε / B) :=
            mul_lt_mul_of_pos_left hN hB_pos
      _ = ε := by
            field_simp [hB_pos.ne']
  intro m hm n hn s hs
  rcases le_total m n with hmn | hnm
  · exact htail_bound hm hmn s hs
  · simpa [dist_comm] using htail_bound hn hnm s hs

/-- The sine zeta function takes the classical boundary value at `s = 1` for `x ∈ (0, 1)`. -/
theorem sinZeta_one_eq_boundary {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    HurwitzZeta.sinZeta x 1 = (Real.pi * (1 / 2 - x) : ℂ) := by
  let boundary : ℂ := (Real.pi * (1 / 2 - x) : ℂ)
  let S : ℕ → ℝ → ℂ := fun n s ↦
    ∑ i ∈ Finset.range n,
      Real.sin (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (s : ℂ))
  let G : ℝ → ℂ := fun s ↦ if hs : s = 1 then boundary else HurwitzZeta.sinZeta x s
  have hCauchy : UniformCauchySeqOn S atTop (Set.Ici 1) := by
    simpa [S] using uniformCauchySeqOn_shiftedSinPartialSums (x := x) hx₀ hx₁
  have hpoint : ∀ s ∈ Set.Ici (1 : ℝ), Tendsto (fun n ↦ S n s) atTop (𝓝 (G s)) := by
    intro s hs
    by_cases hs1 : s = 1
    · simpa [S, G, hs1, boundary] using tendsto_sum_range_shifted_sin_one (x := x) hx₀ hx₁
    · have hslt : 1 < s := lt_of_le_of_ne hs (by simpa [eq_comm] using hs1)
      simpa [S, G, hs1] using (hasSum_shifted_sinZeta (x := x) s hslt).tendsto_sum_nat
  have hunif : TendstoUniformlyOn S G atTop (Set.Ici 1) :=
    hCauchy.tendstoUniformlyOn_of_tendsto hpoint
  have hcont : ContinuousOn G (Set.Ici (1 : ℝ)) := by
    apply hunif.continuousOn
    refine Frequently.of_forall fun n ↦ ?_
    classical
    dsimp [S]
    exact Continuous.continuousOn <|
      continuous_finsetSum _ fun i _ ↦ continuous_shiftedSinTerm x i
  have hG_right : Tendsto G (𝓝[Set.Ioi 1] 1) (𝓝 boundary) := by
    have hG_Ici : Tendsto G (𝓝[Set.Ici 1] 1) (𝓝 boundary) := by
      simpa [G, boundary] using (hcont 1 (by simp)).tendsto
    exact hG_Ici.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  have hG_eq : G =ᶠ[𝓝[Set.Ioi 1] 1] fun s : ℝ ↦ HurwitzZeta.sinZeta x s := by
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    have hslt : 1 < s := by simpa using hs
    simp [G, ne_of_gt hslt]
  have hsin_right : Tendsto (fun s : ℝ ↦ HurwitzZeta.sinZeta x s) (𝓝[Set.Ioi 1] 1)
      (𝓝 boundary) :=
    Tendsto.congr' hG_eq hG_right
  have hsin_cont : Tendsto (fun s : ℝ ↦ HurwitzZeta.sinZeta x s) (𝓝[Set.Ioi 1] 1)
      (𝓝 (HurwitzZeta.sinZeta x 1)) := by
    have hcomplex : Tendsto (fun z : ℂ ↦ HurwitzZeta.sinZeta x z) (𝓝 (1 : ℂ))
        (𝓝 (HurwitzZeta.sinZeta x 1)) :=
      ((HurwitzZeta.differentiableAt_sinZeta x) (1 : ℂ)).continuousAt.tendsto
    have hreal : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝 (1 : ℝ)) (𝓝 (1 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto
    have hcomp : Tendsto (fun s : ℝ ↦ HurwitzZeta.sinZeta x (s : ℂ)) (𝓝 (1 : ℝ))
        (𝓝 (HurwitzZeta.sinZeta x 1)) := by
      simpa [Function.comp_def] using hcomplex.comp hreal
    exact hcomp.mono_left nhdsWithin_le_nhds
  simpa [boundary] using (tendsto_nhds_unique hsin_right hsin_cont).symm

/-- For a nonzero residue class, `sinZeta` at the corresponding point of `UnitAddCircle`
takes the classical boundary value used on the odd side of the `L(1, χ)` formula. -/
theorem sinZeta_toAddCircle_one_eq_boundary {a : ZMod p} (ha : a ≠ 0) :
    HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 =
      (((Real.pi : ℝ) : ℂ) * ((1 / 2 : ℂ) - (a.val : ℂ) / (p : ℂ))) := by
  rw [sinZeta_toAddCircle_eq_val_div_prime]
  have hx : (a.val / p : ℝ) ∈ Set.Ioo 0 1 := zmod_val_div_prime_mem_Ioo (p := p) ha
  calc
    HurwitzZeta.sinZeta (a.val / p : ℝ) 1 =
        (Real.pi * (1 / 2 - (a.val / p : ℝ)) : ℂ) :=
          sinZeta_one_eq_boundary (x := (a.val / p : ℝ)) hx.1 hx.2
    _ = (((Real.pi : ℝ) : ℂ) * ((1 / 2 : ℂ) - (a.val : ℂ) / (p : ℂ))) := by
          have hcast : (((a.val / p : ℝ) : ℂ)) = (a.val : ℂ) / (p : ℂ) := by
            push_cast
            rfl
          simpa using congrArg
            (fun z : ℂ ↦ (((Real.pi : ℝ) : ℂ) * ((1 / 2 : ℂ) - z))) hcast

end LValueAtOne

end BernoulliRegular

module

public import Mathlib
public import DedekindResidue.CompletedZeta.Existence
public import DedekindResidue.CompletedZeta.GammaStrip

/-!
# Analytic control of the completed Dedekind zeta function  (SP1-AC leaf A2)

Uniform vertical-strip bounds for the Hecke pair's Mellin transforms, from the triangle
inequality applied to the strong pair's full-line Mellin representation:

* `norm_heckeΛ₀_le` — `‖Λ₀(s)‖` is at most the norm-integral at `Re s`;
* `integrable_heckeΛ₀_norm` — those norm-integrals converge at every real exponent;
* `exists_heckeΛ₀_strip_bound` — `‖Λ₀‖` is bounded on every vertical strip, uniformly
  in the imaginary direction (the `x^{σ-1} ≤ x^{a-1} + x^{b-1}` endpoint trick).

Downstream (per `.mathlib-quality/decomposition-sp1ac.md`): Λ- and
`H(s) = s(s-1)Λ_K(s)`-versions, the ζ_K convexity bounds (with `GammaStrip`), Jensen
zero-counting, and the Landau local partial fractions.
-/

namespace DedekindResidue

@[expose] public section

open Complex MeasureTheory NumberField NumberField.InfinitePlace
open scoped Real

variable (K : Type*) [Field K] [NumberField K]

/-- Pointwise Mellin triangle inequality for the entire completed theta transform:
`‖Λ₀(s)‖` is at most the norm-integral at the real part. -/
theorem norm_heckeΛ₀_le (s : ℂ) :
    ‖(heckeFEPair K).Λ₀ s‖
      ≤ ∫ x in Set.Ioi (0:ℝ), x ^ (s.re - 1) * ‖(heckeFEPair K).f_modif x‖ := by
  rw [WeakFEPair.Λ₀, mellin]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [Complex.sub_re]

/-- The norm-integrals converge at every real exponent (the strong pair has full-line
Mellin convergence). -/
theorem integrable_heckeΛ₀_norm (a : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ (a - 1) * ‖(heckeFEPair K).f_modif x‖)
      (Set.Ioi 0) := by
  have hconv : MellinConvergent ((heckeFEPair K).f_modif) (a : ℂ) :=
    ((heckeFEPair K).toStrongFEPair.hasMellin (a : ℂ)).1
  have hnn : IntegrableOn
      (fun x : ℝ => ‖((x:ℂ) ^ ((a:ℂ) - 1) • (heckeFEPair K).f_modif x)‖)
      (Set.Ioi 0) := hconv.norm
  refine hnn.congr_fun (fun x hx => ?_) measurableSet_Ioi
  show ‖((x:ℂ) ^ ((a:ℂ) - 1) • (heckeFEPair K).f_modif x)‖
    = x ^ (a - 1) * ‖(heckeFEPair K).f_modif x‖
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [Complex.sub_re]

/-- **AC-A2: uniform vertical-strip bound for `Λ₀`** — on any strip `a ≤ Re s ≤ b`,
`‖Λ₀(s)‖` is bounded by a constant depending only on the strip (and `K`), uniformly
in the imaginary direction. -/
theorem exists_heckeΛ₀_strip_bound (a b : ℝ) :
    ∃ B : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖(heckeFEPair K).Λ₀ s‖ ≤ B := by
  refine ⟨(∫ x in Set.Ioi (0:ℝ), x ^ (a - 1) * ‖(heckeFEPair K).f_modif x‖)
    + ∫ x in Set.Ioi (0:ℝ), x ^ (b - 1) * ‖(heckeFEPair K).f_modif x‖, ?_⟩
  intro s ha hb
  refine le_trans (norm_heckeΛ₀_le K s) ?_
  have hmono : ∀ x ∈ Set.Ioi (0:ℝ),
      x ^ (s.re - 1) * ‖(heckeFEPair K).f_modif x‖
        ≤ x ^ (a - 1) * ‖(heckeFEPair K).f_modif x‖
          + x ^ (b - 1) * ‖(heckeFEPair K).f_modif x‖ := by
    intro x hx
    have hx0 : (0:ℝ) < x := hx
    rcases le_or_gt x 1 with hx1 | hx1
    · have h1 : x ^ (s.re - 1) ≤ x ^ (a - 1) :=
        Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by linarith)
      have h2 : (0:ℝ) ≤ x ^ (b - 1) * ‖(heckeFEPair K).f_modif x‖ := by positivity
      nlinarith [norm_nonneg ((heckeFEPair K).f_modif x), Real.rpow_nonneg hx0.le (s.re - 1)]
    · have h1 : x ^ (s.re - 1) ≤ x ^ (b - 1) :=
        Real.rpow_le_rpow_of_exponent_le (le_of_lt hx1) (by linarith)
      have h2 : (0:ℝ) ≤ x ^ (a - 1) * ‖(heckeFEPair K).f_modif x‖ := by positivity
      nlinarith [norm_nonneg ((heckeFEPair K).f_modif x), Real.rpow_nonneg hx0.le (s.re - 1)]
  calc (∫ x in Set.Ioi (0:ℝ), x ^ (s.re - 1) * ‖(heckeFEPair K).f_modif x‖)
      ≤ ∫ x in Set.Ioi (0:ℝ),
          (x ^ (a - 1) * ‖(heckeFEPair K).f_modif x‖
            + x ^ (b - 1) * ‖(heckeFEPair K).f_modif x‖) :=
        setIntegral_mono_on (integrable_heckeΛ₀_norm K s.re)
          ((integrable_heckeΛ₀_norm K a).add (integrable_heckeΛ₀_norm K b))
          measurableSet_Ioi hmono
    _ = (∫ x in Set.Ioi (0:ℝ), x ^ (a - 1) * ‖(heckeFEPair K).f_modif x‖)
          + ∫ x in Set.Ioi (0:ℝ), x ^ (b - 1) * ‖(heckeFEPair K).f_modif x‖ :=
        integral_add (integrable_heckeΛ₀_norm K a) (integrable_heckeΛ₀_norm K b)

/-- **AC-A2-ii: polynomial strip bound for the entire completed zeta**
`H(s) = s(s-1)Λ_K(s)`: on every vertical strip, `‖H(s)‖ ≤ B·(1+‖s‖)²` uniformly in
the imaginary direction. This is the growth input for Jensen counting and the
contour estimates. -/
theorem exists_completedDedekindZetaEntire_strip_bound (a b : ℝ) (hab : a ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖completedDedekindZetaEntire K s‖ ≤ B * (1 + ‖s‖)^2 := by
  obtain ⟨B₀, hB₀⟩ := exists_heckeΛ₀_strip_bound K (a/2) (b/2)
  have hB₀0 : 0 ≤ B₀ := by
    refine le_trans (norm_nonneg ((heckeFEPair K).Λ₀ ((a/2 : ℝ) : ℂ))) (hB₀ _ ?_ ?_)
    · simp
    · simp
      linarith
  refine ⟨‖(((heckeAdjust K : ℝ) : ℂ))⁻¹‖
    * (B₀ + 2 * ‖(heckeFEPair K).f₀‖ + 2 * ‖(heckeFEPair K).g₀‖),
    by positivity, fun s ha hb => ?_⟩
  have hs2 : (s / 2).re = s.re / 2 := by
    rw [show s / 2 = ((1/2 : ℝ) : ℂ) * s by push_cast; ring, Complex.re_ofReal_mul]
    ring
  have hΛ : ‖(heckeFEPair K).Λ₀ (s / 2)‖ ≤ B₀ :=
    hB₀ (s/2) (by rw [hs2]; linarith) (by rw [hs2]; linarith)
  have h1s : ‖s‖ ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
  have h1s1 : ‖s - 1‖ ≤ 1 + ‖s‖ := by
    calc ‖s - 1‖ ≤ ‖s‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 1 + ‖s‖ := by rw [norm_one]; ring
  have hone : (1:ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
  have hmain : ‖s * (s - 1) * (heckeFEPair K).Λ₀ (s / 2)
      - 2 * (s - 1) * (heckeFEPair K).f₀ + 2 * s * (heckeFEPair K).g₀‖
      ≤ (1 + ‖s‖)^2 * (B₀ + 2 * ‖(heckeFEPair K).f₀‖ + 2 * ‖(heckeFEPair K).g₀‖) := by
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add_left (norm_sub_le _ _) _) ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_ofNat]
    have hsq : 1 + ‖s‖ ≤ (1 + ‖s‖)^2 := by nlinarith [norm_nonneg s]
    have e1 : ‖s‖ * ‖s - 1‖ * ‖(heckeFEPair K).Λ₀ (s / 2)‖ ≤ (1 + ‖s‖)^2 * B₀ := by
      have hss : ‖s‖ * ‖s - 1‖ ≤ (1 + ‖s‖)^2 := by
        nlinarith [norm_nonneg s, norm_nonneg (s - 1)]
      exact mul_le_mul hss hΛ (norm_nonneg _) (by positivity)
    have e2 : 2 * ‖s - 1‖ * ‖(heckeFEPair K).f₀‖
        ≤ (1 + ‖s‖)^2 * (2 * ‖(heckeFEPair K).f₀‖) := by
      calc 2 * ‖s - 1‖ * ‖(heckeFEPair K).f₀‖
          = ‖s - 1‖ * (2 * ‖(heckeFEPair K).f₀‖) := by ring
        _ ≤ (1 + ‖s‖)^2 * (2 * ‖(heckeFEPair K).f₀‖) :=
            mul_le_mul_of_nonneg_right (h1s1.trans hsq) (by positivity)
    have e3 : 2 * ‖s‖ * ‖(heckeFEPair K).g₀‖
        ≤ (1 + ‖s‖)^2 * (2 * ‖(heckeFEPair K).g₀‖) := by
      calc 2 * ‖s‖ * ‖(heckeFEPair K).g₀‖
          = ‖s‖ * (2 * ‖(heckeFEPair K).g₀‖) := by ring
        _ ≤ (1 + ‖s‖)^2 * (2 * ‖(heckeFEPair K).g₀‖) :=
            mul_le_mul_of_nonneg_right (h1s.trans hsq) (by positivity)
    have hdist : (1 + ‖s‖)^2 * (B₀ + 2 * ‖(heckeFEPair K).f₀‖ + 2 * ‖(heckeFEPair K).g₀‖)
        = (1 + ‖s‖)^2 * B₀ + (1 + ‖s‖)^2 * (2 * ‖(heckeFEPair K).f₀‖)
          + (1 + ‖s‖)^2 * (2 * ‖(heckeFEPair K).g₀‖) := by ring
    rw [hdist]
    linarith
  rw [completedDedekindZetaEntire, norm_mul]
  calc ‖(((heckeAdjust K : ℝ) : ℂ))⁻¹‖
      * ‖s * (s - 1) * (heckeFEPair K).Λ₀ (s / 2)
          - 2 * (s - 1) * (heckeFEPair K).f₀ + 2 * s * (heckeFEPair K).g₀‖
      ≤ ‖(((heckeAdjust K : ℝ) : ℂ))⁻¹‖
        * ((1 + ‖s‖)^2 * (B₀ + 2 * ‖(heckeFEPair K).f₀‖ + 2 * ‖(heckeFEPair K).g₀‖)) :=
        mul_le_mul_of_nonneg_left hmain (norm_nonneg _)
    _ = ‖(((heckeAdjust K : ℝ) : ℂ))⁻¹‖
        * (B₀ + 2 * ‖(heckeFEPair K).f₀‖ + 2 * ‖(heckeFEPair K).g₀‖) * (1 + ‖s‖)^2 := by
        ring

/-- There is exactly one ideal of norm 1. -/
theorem card_absNorm_eq_one :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 1} = 1 := by
  have he : {I : Ideal (𝓞 K) // Ideal.absNorm I = 1} ≃ {I : Ideal (𝓞 K) // I = ⊤} :=
    Equiv.subtypeEquivRight (fun I => Ideal.absNorm_eq_one_iff)
  rw [Nat.card_congr he]
  simp

/-- **AC-A4 center lower bound**: far enough right, the Dedekind zeta function is at
least `1/2` in modulus — the Dirichlet tail `∑_{n≥2} a_n n^{-σ}` decays like `2^{-σ}`
once it converges, so it is eventually below `1/2`. -/
theorem exists_re_norm_dedekindZeta_ge_half :
    ∃ A : ℝ, 2 ≤ A ∧ ∀ s : ℂ, A ≤ s.re → 1/2 ≤ ‖dedekindZeta K s‖ := by
  set f : ℕ → ℂ := fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)
    with hf
  have hsum2 : LSeriesSummable f 2 := by
    have h := count_LSeriesSummable K (by norm_num : (1:ℝ) < 2)
    have hfe : (fun n : ℕ =>
        ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) : ℂ)) = f := by
      funext n
      rw [hf]
      push_cast
      rfl
    rw [hfe] at h
    exact_mod_cast h
  set T : ℝ := ∑' n : ℕ, ‖LSeries.term f 2 n‖ with hT
  have hT0 : 0 ≤ T := tsum_nonneg (fun n => norm_nonneg _)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, T * (1/2)^m ≤ 1/2 := by
    rcases eq_or_lt_of_le hT0 with h0 | hpos
    · exact ⟨0, by rw [← h0]; norm_num⟩
    · obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
        (show (0:ℝ) < 1/(2*T) by positivity) (by norm_num : (1:ℝ)/2 < 1)
      refine ⟨m, ?_⟩
      have := mul_le_mul_of_nonneg_left hm.le hT0
      calc T * (1/2)^m ≤ T * (1/(2*T)) := this
        _ = 1/2 := by field_simp
  refine ⟨2 + m, by linarith [Nat.cast_nonneg (α := ℝ) m], fun s hs => ?_⟩
  have hσ2 : (2:ℝ) ≤ s.re := by
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hsummS : LSeriesSummable f s := hsum2.of_re_le_re (by simpa using hσ2)
  have hterm1 : LSeries.term f s 1 = 1 := by
    rw [LSeries.term_def]
    simp [hf]
  have hζ : dedekindZeta K s
      = 1 + ∑' n : ℕ, ite (n = 1) 0 (LSeries.term f s n) := by
    rw [dedekindZeta, LSeries]
    rw [show (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) = f
      from rfl]
    rw [hsummS.tsum_eq_add_tsum_ite 1, hterm1]
  -- pointwise tail comparison against the exponent-2 terms
  have hpoint : ∀ n : ℕ, ‖ite (n = 1) 0 (LSeries.term f s n)‖
      ≤ (1/2)^m * ‖LSeries.term f 2 n‖ := by
    intro n
    rcases eq_or_ne n 1 with rfl | hn1
    · simp
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    rw [if_neg hn1, LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hn0, if_neg hn0,
      show ((2:ℂ)).re = (2:ℝ) by norm_num]
    have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
    have hnpos : (0:ℝ) < n := by linarith
    have hkey : (n:ℝ)^(2:ℝ) * (2:ℝ)^(m:ℝ) ≤ (n:ℝ)^(s.re) := by
      have h1 : (2:ℝ)^(m:ℝ) ≤ (n:ℝ)^(s.re - 2) := by
        calc (2:ℝ)^(m:ℝ) ≤ (2:ℝ)^(s.re - 2) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ ≤ (n:ℝ)^(s.re - 2) := Real.rpow_le_rpow (by norm_num) hn2 (by linarith)
      calc (n:ℝ)^(2:ℝ) * (2:ℝ)^(m:ℝ)
          ≤ (n:ℝ)^(2:ℝ) * (n:ℝ)^(s.re - 2) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (n:ℝ)^(s.re) := by
            rw [← Real.rpow_add hnpos]
            ring_nf
    have hhalf : ((1:ℝ)/2)^m * ((2:ℝ)^(m:ℝ)) = 1 := by
      rw [← Real.rpow_natCast ((1:ℝ)/2) m,
        ← Real.mul_rpow (by norm_num) (by norm_num)]
      norm_num
    calc ‖f n‖ / (n:ℝ)^(s.re)
        ≤ ‖f n‖ / ((n:ℝ)^(2:ℝ) * (2:ℝ)^(m:ℝ)) := by
          gcongr
      _ = (1/2)^m * (‖f n‖ / (n:ℝ)^(2:ℝ)) := by
          rw [← div_div, div_eq_mul_inv (‖f n‖ / (n:ℝ)^(2:ℝ)), mul_comm]
          congr 1
          exact (eq_inv_of_mul_eq_one_left hhalf).symm
  -- summability of the pieces
  have hnormS : Summable (fun n : ℕ => ‖ite (n = 1) 0 (LSeries.term f s n)‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hsummS.norm
    rcases eq_or_ne n 1 with rfl | hn1
    · simp
    · rw [if_neg hn1]
  have hcompar : Summable (fun n : ℕ => (1/2:ℝ)^m * ‖LSeries.term f 2 n‖) :=
    (hsum2.norm).mul_left _
  have hRbound : ‖∑' n : ℕ, ite (n = 1) 0 (LSeries.term f s n)‖ ≤ T * (1/2)^m := by
    refine le_trans (norm_tsum_le_tsum_norm hnormS) ?_
    calc (∑' n : ℕ, ‖ite (n = 1) 0 (LSeries.term f s n)‖)
        ≤ ∑' n : ℕ, (1/2:ℝ)^m * ‖LSeries.term f 2 n‖ :=
          hnormS.tsum_le_tsum hpoint hcompar
      _ = (1/2)^m * T := by rw [tsum_mul_left]
      _ = T * (1/2)^m := by ring
  rw [hζ]
  set R : ℂ := ∑' n : ℕ, ite (n = 1) 0 (LSeries.term f s n) with hR
  have h1R : (1:ℝ) ≤ ‖(1:ℂ) + R‖ + ‖R‖ := by
    calc (1:ℝ) = ‖(1:ℂ)‖ := by norm_num
      _ = ‖((1:ℂ) + R) + (-R)‖ := by ring_nf
      _ ≤ ‖(1:ℂ) + R‖ + ‖-R‖ := norm_add_le _ _
      _ = ‖(1:ℂ) + R‖ + ‖R‖ := by rw [norm_neg]
  linarith [le_trans hRbound hm]

/-- Decaying upper bound for `Γℝ` on `1 ≤ σ ≤ 2`, `|t| ≥ 2`:
`‖Γℝ(σ+it)‖ ≤ √(12π)·(1+|t|)·e^{-π|t|/4}`. -/
theorem norm_Gammaℝ_le {σ t : ℝ} (h1 : 1 ≤ σ) (h2 : σ ≤ 2) (ht : 2 ≤ |t|) :
    ‖Complex.Gammaℝ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Real.sqrt (12 * π) * (1 + |t|) * Real.exp (-(π * |t|) / 4) := by
  rw [Complex.Gammaℝ_def, norm_mul]
  have hπ : ‖(π : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I) / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hre : (-((σ : ℂ) + (t : ℂ) * Complex.I) / 2).re = -σ/2 := by
      rw [show -((σ : ℂ) + (t : ℂ) * Complex.I) / 2
          = ((-σ/2 : ℝ) : ℂ) + ((-t/2 : ℝ) : ℂ) * Complex.I by push_cast; ring]
      simp
    rw [hre]
    calc π ^ (-σ/2 : ℝ) ≤ π ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
      _ = 1 := Real.rpow_zero π
  have harg : ((σ : ℂ) + (t : ℂ) * Complex.I) / 2
      = ((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have ht2 : 1 ≤ |t/2| := by
    rw [abs_div, show |(2:ℝ)| = 2 by norm_num]
    linarith
  have hΓ : ‖Complex.Gamma (((σ : ℂ) + (t : ℂ) * Complex.I) / 2)‖
      ≤ Real.sqrt (12 * π) * (1 + |t|) * Real.exp (-(π * |t|) / 4) := by
    rw [harg]
    refine le_trans (norm_Gamma_le_mul_exp (σ := σ/2) (t := t/2)
      (by linarith) (by linarith) ht2) ?_
    have hnorm : ‖((σ/2 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * Complex.I‖ ≤ 1 + |t| := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
      have hs2 : |σ/2| ≤ 1 := by
        rw [abs_div, show |(2:ℝ)| = 2 by norm_num,
          abs_of_pos (by linarith : (0:ℝ) < σ)]
        linarith
      have ht2' : |t/2| ≤ |t| := by
        rw [abs_div, show |(2:ℝ)| = 2 by norm_num]
        linarith [abs_nonneg t]
      linarith
    have hexp : Real.exp (-(π * |t/2|) / 2) = Real.exp (-(π * |t|) / 4) := by
      congr 1
      rw [abs_div, show |(2:ℝ)| = 2 by norm_num]
      ring
    rw [hexp]
    gcongr
  calc ‖(π : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I) / 2)‖
      * ‖Complex.Gamma (((σ : ℂ) + (t : ℂ) * Complex.I) / 2)‖
      ≤ 1 * (Real.sqrt (12 * π) * (1 + |t|) * Real.exp (-(π * |t|) / 4)) :=
        mul_le_mul hπ hΓ (norm_nonneg _) (by norm_num)
    _ = Real.sqrt (12 * π) * (1 + |t|) * Real.exp (-(π * |t|) / 4) := by ring

/-- Decaying upper bound for `Γℂ` on `1 ≤ σ ≤ 2`, `|t| ≥ 2`:
`‖Γℂ(σ+it)‖ ≤ 8√(12π)·(1+|t|)²·e^{-π|t|/2}`. -/
theorem norm_Gammaℂ_le {σ t : ℝ} (h1 : 1 ≤ σ) (h2 : σ ≤ 2) (ht : 2 ≤ |t|) :
    ‖Complex.Gammaℂ ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 8 * Real.sqrt (12 * π) * (1 + |t|)^2 * Real.exp (-(π * |t|) / 2) := by
  rw [Complex.Gammaℂ_def, norm_mul, norm_mul]
  have ht1 : 1 ≤ |t| := by linarith
  have h1t : (1:ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hsq : (0:ℝ) ≤ Real.sqrt (12*π) := Real.sqrt_nonneg _
  have he : (0:ℝ) < Real.exp (-(π * |t|)/2) := Real.exp_pos _
  have h2π : ‖((2:ℂ) * π) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ 1 := by
    rw [show ((2:ℂ) * π) = ((2 * π : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have hre : (-((σ : ℂ) + (t : ℂ) * Complex.I)).re = -σ := by simp
    rw [hre]
    calc (2*π) ^ (-σ : ℝ) ≤ (2*π) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
      _ = 1 := Real.rpow_zero _
  have h2n : ‖(2:ℂ)‖ = 2 := by norm_num
  have hznorm : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ 2 * (1 + |t|) := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < σ)]
    nlinarith [abs_nonneg t]
  have hΓ : ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 4 * Real.sqrt (12 * π) * (1 + |t|)^2 * Real.exp (-(π * |t|) / 2) := by
    rcases le_or_gt σ (3/2) with hσ | hσ
    · refine le_trans (norm_Gamma_le_mul_exp (σ := σ) (t := t) (by linarith) hσ ht1) ?_
      have hstep : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ 4 * (1 + |t|)^2 := by
        refine le_trans hznorm ?_
        nlinarith
      calc Real.sqrt (12*π) * ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ * Real.exp (-(π * |t|)/2)
          ≤ Real.sqrt (12*π) * (4 * (1 + |t|)^2) * Real.exp (-(π * |t|)/2) := by
            gcongr
        _ = 4 * Real.sqrt (12*π) * (1 + |t|)^2 * Real.exp (-(π * |t|)/2) := by ring
    · have hne : ((σ : ℂ) + (t : ℂ) * Complex.I) - 1 ≠ 0 := by
        intro h0
        have := congrArg Complex.im h0
        simp at this
        rw [this] at ht1
        norm_num at ht1
      have hrec : Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)
          = (((σ : ℂ) + (t : ℂ) * Complex.I) - 1)
            * Complex.Gamma (((σ - 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
        have h := Complex.Gamma_add_one (((σ : ℂ) + (t : ℂ) * Complex.I) - 1) hne
        rw [sub_add_cancel] at h
        rw [h]
        congr 2
        push_cast
        ring
      rw [hrec, norm_mul]
      have hfac : ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖ ≤ 3 * (1 + |t|) := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [norm_one]
        linarith [hznorm]
      have hbase := norm_Gamma_le_mul_exp (σ := σ - 1) (t := t)
        (by linarith) (by linarith) ht1
      have hn1 : ‖((σ - 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ ≤ 1 + |t| := by
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < σ - 1)]
        linarith
      calc ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖
          * ‖Complex.Gamma (((σ - 1 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ (3 * (1 + |t|))
            * (Real.sqrt (12 * π) * (1 + |t|) * Real.exp (-(π * |t|) / 2)) := by
            refine mul_le_mul hfac (le_trans hbase ?_) (norm_nonneg _) (by positivity)
            gcongr
        _ ≤ 4 * Real.sqrt (12 * π) * (1 + |t|)^2 * Real.exp (-(π * |t|) / 2) := by
            nlinarith [mul_nonneg (mul_nonneg hsq (by nlinarith : (0:ℝ) ≤ (1+|t|)^2)) he.le]
  calc ‖(2:ℂ)‖ * ‖((2:ℂ) * π) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
      * ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 2 * 1 * (4 * Real.sqrt (12 * π) * (1 + |t|)^2 * Real.exp (-(π * |t|) / 2)) := by
        rw [h2n]
        refine mul_le_mul (by nlinarith [norm_nonneg (((2:ℂ) * π)
          ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))]) hΓ (norm_nonneg _) (by norm_num)
    _ = 8 * Real.sqrt (12 * π) * (1 + |t|)^2 * Real.exp (-(π * |t|) / 2) := by ring

/-- **Decaying upper for the archimedean factor** on `1 ≤ σ ≤ 2`, `|t| ≥ 2`:
`‖γ_K(σ+it)‖ ≤ C_K·(1+|t|)^{n}·e^{-nπ|t|/4}` with `n = r₁ + 2r₂` — the envelope rate
matched by the lower bounds (`Γℝ` decays at `π|t|/4` per factor, `Γℂ` at `π|t|/2`). -/
theorem norm_gammaFactor_le {σ t : ℝ} (h1 : 1 ≤ σ) (h2 : σ ≤ 2) (ht : 2 ≤ |t|) :
    ‖gammaFactor K ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (Real.sqrt (12*π))^(nrRealPlaces K) * (8 * Real.sqrt (12*π))^(nrComplexPlaces K)
        * (1 + |t|)^(nrRealPlaces K + 2 * nrComplexPlaces K)
        * Real.exp (-(((nrRealPlaces K + 2 * nrComplexPlaces K : ℕ) : ℝ) * (π * |t|)) / 4)
      := by
  rw [gammaFactor, norm_mul, norm_pow, norm_pow]
  have hE2 : Real.exp (-(π * |t|) / 2) = (Real.exp (-(π * |t|) / 4))^2 := by
    rw [show -(π * |t|) / 2 = -(π * |t|) / 4 + -(π * |t|) / 4 by ring, Real.exp_add, sq]
  have hb1 := norm_Gammaℝ_le (h1 := h1) (h2 := h2) (ht := ht)
  have hb2 := norm_Gammaℂ_le (h1 := h1) (h2 := h2) (ht := ht)
  have hp1 : ‖Complex.Gammaℝ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ nrRealPlaces K
      ≤ (Real.sqrt (12*π) * (1 + |t|) * Real.exp (-(π * |t|) / 4)) ^ nrRealPlaces K :=
    pow_le_pow_left₀ (norm_nonneg _) hb1 _
  have hp2 : ‖Complex.Gammaℂ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ nrComplexPlaces K
      ≤ (8 * Real.sqrt (12*π) * (1 + |t|)^2 * Real.exp (-(π * |t|) / 2))
        ^ nrComplexPlaces K :=
    pow_le_pow_left₀ (norm_nonneg _) hb2 _
  refine le_trans (mul_le_mul hp1 hp2 (by positivity) (by positivity)) (le_of_eq ?_)
  rw [hE2]
  rw [show (Real.sqrt (12*π) * (1 + |t|) * Real.exp (-(π * |t|) / 4)) ^ nrRealPlaces K
      * (8 * Real.sqrt (12*π) * (1 + |t|)^2 * (Real.exp (-(π * |t|) / 4))^2)
        ^ nrComplexPlaces K
      = (Real.sqrt (12*π))^(nrRealPlaces K) * (8 * Real.sqrt (12*π))^(nrComplexPlaces K)
        * (1 + |t|)^(nrRealPlaces K + 2 * nrComplexPlaces K)
        * (Real.exp (-(π * |t|) / 4))^(nrRealPlaces K + 2 * nrComplexPlaces K) by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, pow_add, ← pow_mul, pow_add, ← pow_mul]
    ring]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

end

end DedekindResidue

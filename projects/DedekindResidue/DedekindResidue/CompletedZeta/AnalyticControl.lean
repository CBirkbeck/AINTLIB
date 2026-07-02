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

/-- On `Re s ≥ 2` the Dedekind zeta function is bounded by its norm-sum at `2`. -/
theorem norm_dedekindZeta_le_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖dedekindZeta K s‖
      ≤ ∑' n : ℕ, ‖LSeries.term
          (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) 2 n‖ := by
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
  have hsummS : LSeriesSummable f s := hsum2.of_re_le_re (by simpa using hs)
  have hterm : ∀ n : ℕ, ‖LSeries.term f s n‖ ≤ ‖LSeries.term f 2 n‖ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hn0, if_neg hn0,
      show ((2:ℂ)).re = (2:ℝ) by norm_num]
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
    gcongr
  calc ‖dedekindZeta K s‖ = ‖∑' n : ℕ, LSeries.term f s n‖ := by rw [dedekindZeta]; rfl
    _ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hsummS.norm
    _ ≤ ∑' n : ℕ, ‖LSeries.term f 2 n‖ :=
        (hsummS.norm).tsum_le_tsum hterm (hsum2.norm)

/-- **Decaying upper for `H` on the line `Re = 2`** (A3-c): the polynomial factors and
the prefactor are tame, the gamma factor supplies the `e^{-n_K π|t|/4}` envelope, and
the zeta factor is bounded. -/
theorem exists_H_two_line_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ |t| →
      ‖completedDedekindZetaEntire K (((2:ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * (1 + |t|)^(nrRealPlaces K + 2 * nrComplexPlaces K + 2)
          * Real.exp (-(((nrRealPlaces K + 2 * nrComplexPlaces K : ℕ) : ℝ) * (π * |t|))
            / 4) := by
  set T₂ : ℝ := ∑' n : ℕ, ‖LSeries.term
      (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) 2 n‖ with hT₂
  have hT₂0 : 0 ≤ T₂ := tsum_nonneg (fun n => norm_nonneg _)
  refine ⟨6 * (|((discr K : ℤ) : ℝ)| + 2)
    * ((Real.sqrt (12*π))^(nrRealPlaces K) * (8 * Real.sqrt (12*π))^(nrComplexPlaces K))
    * (T₂ + 1), by positivity, fun t ht => ?_⟩
  set s : ℂ := ((2:ℝ) : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = 2 := by simp [hs]
  have hs0 : s ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    rw [hsre] at this
    norm_num at this
  have hs1 : s ≠ 1 := by
    intro h0
    have := congrArg Complex.re h0
    rw [hsre] at this
    norm_num at this
  have hs2 : (1:ℝ) < s.re := by rw [hsre]; norm_num
  rw [completedDedekindZetaEntire_eq K hs0 hs1,
    completedDedekindZeta_eq_of_one_lt_re K hs2, completedZetaPrefactor]
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  have h1t : (1:ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hsn : ‖s‖ ≤ 2 * (1 + |t|) := by
    rw [hs]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, show |(2:ℝ)| = 2 by norm_num]
    linarith [abs_nonneg t]
  have hsn1 : ‖s - 1‖ ≤ 3 * (1 + |t|) := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_one]
    linarith [hsn]
  have hdne : ((discr K : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast NumberField.discr_ne_zero K
  have hdpos : (0:ℝ) < |((discr K : ℤ) : ℝ)| := abs_pos.mpr hdne
  have hΔ : ‖((|discr K| : ℝ) : ℂ) ^ (s / 2)‖ ≤ |((discr K : ℤ) : ℝ)| + 2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hdpos]
    have hre2 : (s / 2).re = 1 := by
      rw [show s / 2 = ((1:ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * Complex.I by
        rw [hs]; push_cast; ring]
      simp
    rw [hre2, Real.rpow_one]
    linarith
  have hγ := norm_gammaFactor_le K (σ := 2) (t := t) (by norm_num) (by norm_num) ht
  rw [show (((2:ℝ) : ℂ) + (t : ℂ) * Complex.I) = s from rfl] at hγ
  have hζ : ‖dedekindZeta K s‖ ≤ T₂ + 1 := by
    refine le_trans (norm_dedekindZeta_le_of_two_le_re K (s := s) (by rw [hsre])) ?_
    rw [← hT₂]
    linarith
  calc ‖s‖ * ‖s - 1‖ * (‖((|discr K| : ℝ) : ℂ) ^ (s / 2)‖ * ‖gammaFactor K s‖
        * ‖dedekindZeta K s‖)
      ≤ (2 * (1 + |t|)) * (3 * (1 + |t|)) * ((|((discr K : ℤ) : ℝ)| + 2)
          * ((Real.sqrt (12*π))^(nrRealPlaces K)
              * (8 * Real.sqrt (12*π))^(nrComplexPlaces K)
            * (1 + |t|)^(nrRealPlaces K + 2 * nrComplexPlaces K)
            * Real.exp (-(((nrRealPlaces K + 2 * nrComplexPlaces K : ℕ) : ℝ)
              * (π * |t|)) / 4))
          * (T₂ + 1)) := by
        gcongr
    _ = 6 * (|((discr K : ℤ) : ℝ)| + 2)
        * ((Real.sqrt (12*π))^(nrRealPlaces K) * (8 * Real.sqrt (12*π))^(nrComplexPlaces K))
        * (T₂ + 1)
        * ((1 + |t|)^2 * (1 + |t|)^(nrRealPlaces K + 2 * nrComplexPlaces K))
        * Real.exp (-(((nrRealPlaces K + 2 * nrComplexPlaces K : ℕ) : ℝ) * (π * |t|))
          / 4) := by ring
    _ = 6 * (|((discr K : ℤ) : ℝ)| + 2)
        * ((Real.sqrt (12*π))^(nrRealPlaces K) * (8 * Real.sqrt (12*π))^(nrComplexPlaces K))
        * (T₂ + 1)
        * (1 + |t|)^(nrRealPlaces K + 2 * nrComplexPlaces K + 2)
        * Real.exp (-(((nrRealPlaces K + 2 * nrComplexPlaces K : ℕ) : ℝ) * (π * |t|))
          / 4) := by
        rw [show nrRealPlaces K + 2 * nrComplexPlaces K + 2
            = 2 + (nrRealPlaces K + 2 * nrComplexPlaces K) by ring, pow_add]
        ring

/-- **The functional equation for the entire completed zeta** (A3-d):
`H(1-s) = H(s)`, since `s(s-1)` is symmetric under `s ↦ 1-s` and `Λ_K(1-s) = Λ_K(s)`;
the two exceptional points are absorbed by continuity. -/
theorem completedDedekindZetaEntire_one_sub (s : ℂ) :
    completedDedekindZetaEntire K (1 - s) = completedDedekindZetaEntire K s := by
  have hcont1 : Continuous (fun z : ℂ => completedDedekindZetaEntire K (1 - z)) :=
    ((differentiable_completedDedekindZetaEntire K).comp
      ((differentiable_const (1:ℂ)).sub differentiable_id)).continuous
  have hcont2 : Continuous (completedDedekindZetaEntire K) :=
    (differentiable_completedDedekindZetaEntire K).continuous
  have hdense : Dense ({(0:ℂ), 1}ᶜ : Set ℂ) :=
    Set.Countable.dense_compl ℝ
      ((Set.toFinite ({(0:ℂ), 1} : Set ℂ)).countable)
  refine congrFun (Continuous.ext_on hdense hcont1 hcont2 ?_) s
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
  obtain ⟨hz0, hz1⟩ := hz
  show completedDedekindZetaEntire K (1 - z) = completedDedekindZetaEntire K z
  have h1z0 : (1:ℂ) - z ≠ 0 := by
    intro h0
    apply hz1
    linear_combination -h0
  have h1z1 : (1:ℂ) - z ≠ 1 := by
    intro h0
    apply hz0
    linear_combination -h0
  rw [completedDedekindZetaEntire_eq K h1z0 h1z1, completedDedekindZetaEntire_eq K hz0 hz1,
    completedDedekindZeta_one_sub K z]
  ring

/-- On the strip `-1 ≤ Re z ≤ 2`, the normalizer `z - 4` dominates both the constant 2
and the height: `1 + |Im z| ≤ 2‖z - 4‖`. -/
theorem one_add_abs_im_le_two_norm_sub_four {z : ℂ} (_h1 : -1 ≤ z.re) (h2 : z.re ≤ 2) :
    1 + |z.im| ≤ 2 * ‖z - 4‖ := by
  have hre4 : (z - 4).re = z.re - 4 := by simp
  have hre : (2:ℝ) ≤ ‖z - 4‖ := by
    have habs : (2:ℝ) ≤ |(z - 4).re| := by
      rw [hre4, abs_sub_comm z.re 4, abs_of_pos (by linarith : (0:ℝ) < 4 - z.re)]
      linarith
    exact le_trans habs (Complex.abs_re_le_norm _)
  have him : |z.im| ≤ ‖z - 4‖ := by
    have h : |(z - 4).im| ≤ ‖z - 4‖ := Complex.abs_im_le_norm _
    simpa using h
  linarith

/-- The comparator sine-exponent: `n_K = r₁ + 2r₂`. -/
noncomputable def gammaExponent : ℕ := nrRealPlaces K + 2 * nrComplexPlaces K

/-- Right boundary bound for the comparator
`G = H⁴·sin(πz)^{n_K}/(z-4)^{4n_K+8}` on `Re z = 2`. -/
theorem comparator_bound_right :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ,
      ‖completedDedekindZetaEntire K (((2:ℝ) : ℂ) + (t : ℂ) * Complex.I)‖^4
        * ‖Complex.sin (π * (((2:ℝ) : ℂ) + (t : ℂ) * Complex.I))‖^(gammaExponent K)
        / ‖(((2:ℝ) : ℂ) + (t : ℂ) * Complex.I) - 4‖^(4 * gammaExponent K + 8)
      ≤ M := by
  obtain ⟨C, hC0, hC⟩ := exists_H_two_line_bound K
  obtain ⟨B, hB0, hB⟩ :=
    exists_completedDedekindZetaEntire_strip_bound K (-1) 2 (by norm_num)
  set n : ℕ := gammaExponent K with hn
  refine ⟨C^4 * 2^(4*n+8) + (B * 25)^4 * Real.exp ((n:ℝ) * (π * 2)) / 2^(4*n+8),
    by positivity, fun t => ?_⟩
  set z : ℂ := ((2:ℝ) : ℂ) + (t : ℂ) * Complex.I with hz
  have hzre : z.re = 2 := by simp [hz]
  have hzim : z.im = t := by simp [hz]
  have hnorm4 : (1:ℝ) + |t| ≤ 2 * ‖z - 4‖ := by
    have := one_add_abs_im_le_two_norm_sub_four (z := z) (by rw [hzre]; norm_num)
      (by rw [hzre])
    rwa [hzim] at this
  have h2z : (2:ℝ) ≤ ‖z - 4‖ := by
    have habs : (2:ℝ) ≤ |(z - 4).re| := by
      rw [show (z - 4).re = z.re - 4 by simp, hzre]
      norm_num
    exact le_trans habs (Complex.abs_re_le_norm _)
  have hz4pos : (0:ℝ) < ‖z - 4‖ := by linarith
  have hsin : ‖Complex.sin (π * z)‖ ≤ Real.exp (π * |t|) := by
    have := norm_sin_pi_mul_le z
    rwa [hzim] at this
  rcases le_or_gt 2 |t| with ht | ht
  · have hH := hC t ht
    rw [← hz] at hH
    have hHn : ‖completedDedekindZetaEntire K z‖^4
        ≤ C^4 * (1+|t|)^(4*n+8) * Real.exp (-((n:ℝ) * (π * |t|))) := by
      calc ‖completedDedekindZetaEntire K z‖^4
          ≤ (C * (1 + |t|)^(n + 2)
              * Real.exp (-(((n:ℕ) : ℝ) * (π * |t|)) / 4))^4 :=
            pow_le_pow_left₀ (norm_nonneg _) hH 4
        _ = C^4 * (1+|t|)^(4*n+8) * Real.exp (-((n:ℝ) * (π * |t|))) := by
            rw [mul_pow, mul_pow, ← pow_mul, ← Real.exp_nat_mul]
            rw [show (n + 2) * 4 = 4*n+8 by ring]
            congr 2
            push_cast
            ring
    have hsinn : ‖Complex.sin (π * z)‖^n ≤ Real.exp ((n:ℝ) * (π * |t|)) := by
      calc ‖Complex.sin (π * z)‖^n ≤ (Real.exp (π * |t|))^n :=
            pow_le_pow_left₀ (norm_nonneg _) hsin n
        _ = Real.exp ((n:ℝ) * (π * |t|)) := by rw [← Real.exp_nat_mul]
    have hnum : ‖completedDedekindZetaEntire K z‖^4 * ‖Complex.sin (π * z)‖^n
        ≤ C^4 * (1+|t|)^(4*n+8) := by
      calc ‖completedDedekindZetaEntire K z‖^4 * ‖Complex.sin (π * z)‖^n
          ≤ (C^4 * (1+|t|)^(4*n+8) * Real.exp (-((n:ℝ) * (π * |t|))))
            * Real.exp ((n:ℝ) * (π * |t|)) :=
            mul_le_mul hHn hsinn (by positivity) (by positivity)
        _ = C^4 * (1+|t|)^(4*n+8) * (Real.exp (-((n:ℝ) * (π * |t|)))
            * Real.exp ((n:ℝ) * (π * |t|))) := by ring
        _ = C^4 * (1+|t|)^(4*n+8) := by
            rw [← Real.exp_add]
            norm_num
    calc ‖completedDedekindZetaEntire K z‖^4 * ‖Complex.sin (π * z)‖^n
        / ‖z - 4‖^(4*n+8)
        ≤ C^4 * (1+|t|)^(4*n+8) / ‖z - 4‖^(4*n+8) := by gcongr
      _ ≤ C^4 * (2 * ‖z - 4‖)^(4*n+8) / ‖z - 4‖^(4*n+8) := by
          gcongr
      _ = C^4 * 2^(4*n+8) := by
          rw [mul_pow, mul_div_assoc, mul_div_assoc,
            div_self (pow_ne_zero _ hz4pos.ne'), mul_one]
      _ ≤ C^4 * 2^(4*n+8)
          + (B * 25)^4 * Real.exp ((n:ℝ) * (π * 2)) / 2^(4*n+8) :=
          le_add_of_nonneg_right (by positivity)
  · have hzn : ‖z‖ ≤ 4 := by
      rw [hz]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, show |(2:ℝ)| = 2 by norm_num]
      linarith
    have hH := hB z (by rw [hzre]; norm_num) (by rw [hzre])
    have hH4 : ‖completedDedekindZetaEntire K z‖^4 ≤ (B*25)^4 := by
      refine pow_le_pow_left₀ (norm_nonneg _) (le_trans hH ?_) 4
      have h25 : (1+‖z‖)^2 ≤ 25 := by nlinarith [norm_nonneg z, hzn]
      nlinarith [hB0]
    have hsinn : ‖Complex.sin (π * z)‖^n ≤ Real.exp ((n:ℝ) * (π * 2)) := by
      calc ‖Complex.sin (π * z)‖^n ≤ (Real.exp (π * |t|))^n :=
            pow_le_pow_left₀ (norm_nonneg _) hsin n
        _ = Real.exp ((n:ℝ) * (π * |t|)) := by rw [← Real.exp_nat_mul]
        _ ≤ Real.exp ((n:ℝ) * (π * 2)) := by
            rw [Real.exp_le_exp]
            have hπ0 : (0:ℝ) ≤ π := Real.pi_pos.le
            nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hπ0)
              (by linarith [ht.le] : (0:ℝ) ≤ 2 - |t|)]
    have hden : (2:ℝ)^(4*n+8) ≤ ‖z - 4‖^(4*n+8) :=
      pow_le_pow_left₀ (by norm_num) h2z _
    have hnum2 : ‖completedDedekindZetaEntire K z‖^4 * ‖Complex.sin (π * z)‖^n
        ≤ (B*25)^4 * Real.exp ((n:ℝ) * (π * 2)) :=
      mul_le_mul hH4 hsinn (pow_nonneg (norm_nonneg _) n)
        (pow_nonneg (by positivity) 4)
    calc ‖completedDedekindZetaEntire K z‖^4 * ‖Complex.sin (π * z)‖^n
        / ‖z - 4‖^(4*n+8)
        ≤ (‖completedDedekindZetaEntire K z‖^4 * ‖Complex.sin (π * z)‖^n)
          / 2^(4*n+8) :=
          div_le_div_of_nonneg_left
            (mul_nonneg (pow_nonneg (norm_nonneg _) 4) (pow_nonneg (norm_nonneg _) n))
            (by positivity) hden
      _ ≤ (B*25)^4 * Real.exp ((n:ℝ) * (π * 2)) / 2^(4*n+8) := by
          gcongr
      _ ≤ C^4 * 2^(4*n+8)
          + (B * 25)^4 * Real.exp ((n:ℝ) * (π * 2)) / 2^(4*n+8) :=
          le_add_of_nonneg_left (by positivity)

/-- Left boundary bound for the comparator on `Re z = -1`, by reflecting to the right
boundary through the functional equation. -/
theorem comparator_bound_left :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ,
      ‖completedDedekindZetaEntire K (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I)‖^4
        * ‖Complex.sin (π * (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I))‖^(gammaExponent K)
        / ‖(((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I) - 4‖^(4 * gammaExponent K + 8)
      ≤ M := by
  obtain ⟨M, hM0, hM⟩ := comparator_bound_right K
  refine ⟨M, hM0, fun t => ?_⟩
  set n : ℕ := gammaExponent K with hn
  -- the functional equation sends -1+it to 2-it
  have hH : completedDedekindZetaEntire K (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I)
      = completedDedekindZetaEntire K (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) := by
    have := completedDedekindZetaEntire_one_sub K (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I)
    rw [show (1:ℂ) - (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I)
        = ((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I by push_cast; ring] at this
    exact this.symm
  -- the sine moduli agree: both lines have vanishing real sine part
  have hsin : ‖Complex.sin (π * (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I))‖
      = ‖Complex.sin (π * (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))‖ := by
    have hd1 : (π : ℂ) * (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I)
        = ((π * (-1) : ℝ) : ℂ) + ((π * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have hd2 : (π : ℂ) * (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)
        = ((π * 2 : ℝ) : ℂ) + ((π * (-t) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have hsq1 := norm_sin_add_mul_I_sq (π * (-1)) (π * t)
    have hsq2 := norm_sin_add_mul_I_sq (π * 2) (π * (-t))
    rw [← hd1] at hsq1
    rw [← hd2] at hsq2
    have hv1 : Real.sin (π * (-1)) = 0 := by
      rw [show π * (-1) = -π by ring, Real.sin_neg, Real.sin_pi, neg_zero]
    have hv2 : Real.sin (π * 2) = 0 := by
      rw [show π * 2 = 2 * π by ring, Real.sin_two_pi]
    rw [hv1] at hsq1
    rw [hv2] at hsq2
    have hs1 : ‖Complex.sin ((π : ℂ) * (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I))‖^2
        = ‖Complex.sin ((π : ℂ) * (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))‖^2 := by
      rw [hsq1, hsq2]
      rw [show π * (-t) = -(π * t) by ring, Real.sinh_neg]
      ring
    calc ‖Complex.sin ((π : ℂ) * (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I))‖
        = Real.sqrt (‖Complex.sin ((π : ℂ) * (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I))‖^2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (‖Complex.sin ((π : ℂ)
            * (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))‖^2) := by rw [hs1]
      _ = ‖Complex.sin ((π : ℂ) * (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))‖ :=
          Real.sqrt_sq (norm_nonneg _)
  -- the left denominator dominates the right one
  have hden : ‖(((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) - 4‖
      ≤ ‖(((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I) - 4‖ := by
    have he1 : (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) - 4
        = ((-2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have he2 : (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I) - 4
        = ((-5 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [he1, he2, Complex.norm_add_mul_I, Complex.norm_add_mul_I]
    refine Real.sqrt_le_sqrt ?_
    nlinarith [sq_nonneg t]
  have hdenpos : (0:ℝ) < ‖(((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) - 4‖ := by
    have : (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) - 4 ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      norm_num at this
    exact norm_pos_iff.mpr this
  calc ‖completedDedekindZetaEntire K (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I)‖^4
      * ‖Complex.sin (π * (((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I))‖^n
      / ‖(((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I) - 4‖^(4*n+8)
      = ‖completedDedekindZetaEntire K (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖^4
        * ‖Complex.sin (π * (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))‖^n
        / ‖(((-1:ℝ) : ℂ) + (t : ℂ) * Complex.I) - 4‖^(4*n+8) := by
        rw [hH, hsin]
    _ ≤ ‖completedDedekindZetaEntire K (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)‖^4
        * ‖Complex.sin (π * (((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))‖^n
        / ‖(((2:ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) - 4‖^(4*n+8) :=
        div_le_div_of_nonneg_left
          (mul_nonneg (pow_nonneg (norm_nonneg _) 4) (pow_nonneg (norm_nonneg _) n))
          (by positivity) (pow_le_pow_left₀ (norm_nonneg _) hden _)
    _ ≤ M := hM (-t)

end

end DedekindResidue

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

open MeasureTheory NumberField
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

end

end DedekindResidue

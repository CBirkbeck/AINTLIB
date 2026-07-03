/-
DedekindResidue: Belabas–Friedman Lemma 4 — the two-cutoff difference estimates.

Applying Lemma 3 at the two cutoffs `X` and `X' = X/e^a` and subtracting kills the
`T`-independent terms (`Φ(0)+Φ(1)`, `log Δ_K`, the Γ-constant), and the paper's four
estimates bound what remains: the sine difference by the mean value theorem
(`|sin(Tγ) − sin(T'γ)| ≤ a|γ|`, losing no `log X`), the cosine terms trivially, the
tail integrals by the exact antiderivative of the kernel, and the archimedean
integrals by monotonicity and the mean value theorem (the `β`-bound). Everything is
carried at real `σ > 1` with `h = σ − 1/2` explicit; the `σ → 1⁺` limit is taken in
the final inequality (never by analytic continuation of the identity), which
reproduces the paper's Lemma 4 (`Mostways`, eq. (Explicit2)) at `k = ℚ`.

Source: B–F 1305.0035, §3 (TeX lines 409–519); route: decomposition-t011.md.
-/
module

public import Mathlib
public import DedekindResidue.Lemma3

@[expose] public section

namespace DedekindResidue

open Complex NumberField Filter Real

variable (K : Type*) [Field K] [NumberField K]

/-! ### The sine-difference estimate (paper lines 446–456)

The mean value theorem gives `|sin(γT) − sin(γT')| ≤ |γ|(T − T')`, so the difference
of the sine series at two cutoffs loses the `1/γ` and is bounded by
`(T−T')·2h²·Σ_ρ m_ρ/(h²+γ_ρ²)` — no `log X` loss. -/

/-- Pointwise: `‖zeroSinTerm at X − zeroSinTerm at X'‖ ≤ 2h²(T−T')/(h²+γ²)`. -/
theorem norm_zeroSinTerm_sub_le {σ : ℝ} (hσ : 1/2 < σ) {X X' : ℝ} (hX' : 1 < X')
    (hXX : X' ≤ X) (γ : ℝ) :
    ‖zeroSinTerm (σ:ℂ) X γ - zeroSinTerm (σ:ℂ) X' γ‖
      ≤ 2*(σ - 1/2)^2 * (Real.log X - Real.log X') / ((σ - 1/2)^2 + γ^2) := by
  have hh : (0:ℝ) < σ - 1/2 := by linarith
  have hh2 : (0:ℝ) < (σ - 1/2)^2 := pow_pos hh 2
  have hT'0 : 0 < Real.log X' := Real.log_pos hX'
  have hTT : Real.log X' ≤ Real.log X := Real.log_le_log (by linarith) hXX
  have hD : (0:ℝ) < (σ - 1/2)^2 + γ^2 := by positivity
  by_cases hγ : γ = 0
  · -- plateau: the difference of the plateau values is `2(T − T')`
    subst hγ
    rw [zeroSinTerm, zeroSinTerm, if_pos rfl, if_pos rfl]
    have h1 : (2 * (Real.log X : ℂ)) - 2 * (Real.log X' : ℂ)
        = ((2*(Real.log X - Real.log X') : ℝ) : ℂ) := by push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    rw [show (0:ℝ)^2 = 0 by norm_num, add_zero]
    rw [div_eq_mul_inv, show 2*(σ - 1/2)^2 * (Real.log X - Real.log X')
        * ((σ - 1/2)^2)⁻¹ = 2*(Real.log X - Real.log X')
          * ((σ - 1/2)^2 * ((σ - 1/2)^2)⁻¹) by ring,
      mul_inv_cancel₀ hh2.ne', mul_one]
  · -- `γ ≠ 0`: MVT via `LipschitzWith 1 sin`
    have h1 : zeroSinTerm (σ:ℂ) X γ - zeroSinTerm (σ:ℂ) X' γ
        = ((2*(σ - 1/2)^2 / (((σ - 1/2)^2 + γ^2)*γ)
            * (Real.sin (Real.log X * γ) - Real.sin (Real.log X' * γ)) : ℝ) : ℂ) := by
      rw [zeroSinTerm, zeroSinTerm, if_neg hγ, if_neg hγ]
      push_cast
      ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs]
    have hsin : |Real.sin (Real.log X * γ) - Real.sin (Real.log X' * γ)|
        ≤ (Real.log X - Real.log X') * |γ| := by
      have h2 := Real.lipschitzWith_sin.dist_le_mul (Real.log X * γ) (Real.log X' * γ)
      rw [Real.dist_eq, Real.dist_eq] at h2
      calc |Real.sin (Real.log X * γ) - Real.sin (Real.log X' * γ)|
          ≤ 1 * |Real.log X * γ - Real.log X' * γ| := by exact_mod_cast h2
        _ = |(Real.log X - Real.log X')| * |γ| := by
            rw [one_mul, show Real.log X * γ - Real.log X' * γ
              = (Real.log X - Real.log X') * γ by ring, abs_mul]
        _ = (Real.log X - Real.log X') * |γ| := by
            rw [abs_of_nonneg (by linarith)]
    have hγpos : (0:ℝ) < |γ| := abs_pos.mpr hγ
    calc |2*(σ - 1/2)^2 / (((σ - 1/2)^2 + γ^2)*γ)
          * (Real.sin (Real.log X * γ) - Real.sin (Real.log X' * γ))|
        = 2*(σ - 1/2)^2 / (((σ - 1/2)^2 + γ^2)*|γ|)
          * |Real.sin (Real.log X * γ) - Real.sin (Real.log X' * γ)| := by
          rw [abs_mul, abs_div, abs_mul, abs_two, abs_of_pos hh2, abs_mul,
            abs_of_pos hD]
      _ ≤ 2*(σ - 1/2)^2 / (((σ - 1/2)^2 + γ^2)*|γ|)
          * ((Real.log X - Real.log X') * |γ|) := by
          gcongr
      _ = 2*(σ - 1/2)^2 * (Real.log X - Real.log X') / ((σ - 1/2)^2 + γ^2) := by
          field_simp

/-- **The sine-difference estimate**: the two-cutoff difference of the sine series is
bounded by `2h²(T−T')·Σ_ρ m_ρ/(h²+γ_ρ²)`. -/
theorem norm_tsum_zeroSinTerm_sub_le {σ : ℝ} (hσ : 1/2 < σ) {X X' : ℝ} (hX' : 1 < X')
    (hXX : X' ≤ X) :
    ‖(∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X ρ.1.im)
      - ∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X' ρ.1.im‖
      ≤ 2*(σ - 1/2)^2 * (Real.log X - Real.log X')
          * ∑' ρ : ZetaZeros K,
              (zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2) := by
  have hX : 1 < X := lt_of_lt_of_le hX' hXX
  have hsum : Summable (fun ρ : ZetaZeros K =>
      (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X ρ.1.im) :=
    summable_zetaZeros_mul_of_norm_le K hσ (fun γ => norm_zeroSinTerm_le hσ hX γ)
  have hsum' : Summable (fun ρ : ZetaZeros K =>
      (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X' ρ.1.im) :=
    summable_zetaZeros_mul_of_norm_le K hσ (fun γ => norm_zeroSinTerm_le hσ hX' γ)
  rw [← Summable.tsum_sub hsum hsum']
  have hmaj : Summable (fun ρ : ZetaZeros K =>
      2*(σ - 1/2)^2 * (Real.log X - Real.log X')
        * ((zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2))) :=
    (summable_zetaZeros_inv_sq K (σ - 1/2) (by linarith)).mul_left _
  have hpt : ∀ ρ : ZetaZeros K,
      ‖(zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X ρ.1.im
        - (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X' ρ.1.im‖
      ≤ 2*(σ - 1/2)^2 * (Real.log X - Real.log X')
          * ((zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2)) := by
    intro ρ
    have hdnn : (0:ℝ) ≤ (zetaZeroDivisor K ρ.1 : ℝ) := by
      exact_mod_cast zetaZeroDivisor_nonneg K ρ.1
    rw [show (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X ρ.1.im
        - (zetaZeroDivisor K ρ.1 : ℂ) * zeroSinTerm (σ:ℂ) X' ρ.1.im
        = (zetaZeroDivisor K ρ.1 : ℂ)
          * (zeroSinTerm (σ:ℂ) X ρ.1.im - zeroSinTerm (σ:ℂ) X' ρ.1.im) by ring,
      norm_mul, Complex.norm_intCast, abs_of_nonneg hdnn]
    calc (zetaZeroDivisor K ρ.1 : ℝ)
          * ‖zeroSinTerm (σ:ℂ) X ρ.1.im - zeroSinTerm (σ:ℂ) X' ρ.1.im‖
        ≤ (zetaZeroDivisor K ρ.1 : ℝ)
          * (2*(σ - 1/2)^2 * (Real.log X - Real.log X')
              / ((σ - 1/2)^2 + ρ.1.im^2)) :=
          mul_le_mul_of_nonneg_left (norm_zeroSinTerm_sub_le hσ hX' hXX _) hdnn
      _ = 2*(σ - 1/2)^2 * (Real.log X - Real.log X')
            * ((zetaZeroDivisor K ρ.1 : ℝ) / ((σ - 1/2)^2 + ρ.1.im^2)) := by ring
  rw [← tsum_mul_left]
  refine (norm_tsum_le_tsum_norm ?_).trans
    (Summable.tsum_le_tsum (fun ρ => hpt ρ) ?_ hmaj)
  · exact hmaj.of_nonneg_of_le (fun ρ => norm_nonneg _) hpt
  · exact (hsum.sub hsum').norm

end DedekindResidue

end

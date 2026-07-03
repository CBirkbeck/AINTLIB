/-
DedekindResidue: Belabas–Friedman Lemma 3 — the explicit formula at `F_{s,X}` as an
absolutely convergent sum over the critical-line zeros.

Under GRH the window sums of `weil_explicit_formula_auxF` converge (b5,
`tendsto_finsum_window_zetaZeros`) to the absolutely summable series
`∑'_ρ m_ρ · Φ_{F_{s,X}}(ρ)` over the full zero index: absolute convergence comes from
the quadratic Fourier decay `‖F̂_{s,X}(γ)‖ = O(1/γ²)` (Lemma 2's closed form) glued to
the band bound on `|γ| ≤ γ₀`, against the Landau-type summability
`∑_ρ m_ρ/(1+γ_ρ²) < ∞`. Uniqueness of limits then upgrades the explicit formula from
a limit statement along good heights to the honest `∑'` identity — the shape of
Belabas–Friedman's Lemma 3 (eq. (13)) sums.
-/
module

public import Mathlib
public import DedekindResidue.ExplicitFormula.WeilAssembly
public import DedekindResidue.ExplicitFormula.GRHZeros

@[expose] public section

namespace DedekindResidue

open Complex NumberField Filter Real

variable (K : Type*) [Field K] [NumberField K]

/-- **Absolute convergence of the zero side at the auxiliary function** (`Re s > 1`):
under GRH every zero is `ρ = 1/2 + iγ_ρ`, where `Φ_{F_{s,X}}(ρ) = F̂_{s,X}(γ_ρ)` decays
like `1/γ_ρ²` (Lemma 2), so the divisor-weighted series over the zero index converges
absolutely by the Landau-type bound `∑_ρ m_ρ/(1+γ_ρ²) < ∞`. -/
theorem summable_zetaZeros_paperPhi_auxF (hGRH : GeneralizedRiemannHypothesis K)
    (s : ℂ) {X : ℝ} (hX : 1 < X) (hs : 1 < s.re) :
    Summable (fun ρ : ZetaZeros K =>
      (zetaZeroDivisor K ρ.1 : ℂ) * paperPhi (auxF s X) ρ.1) := by
  have hs2 : 1/2 < s.re := by linarith
  obtain ⟨C, γ₀, hC, hγ₀, hφ⟩ := exists_norm_fourier_auxF_le s hX hs2
  set a : ℝ := (s.re - 1)/2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have has : a < s.re - 1 := by rw [ha_def]; linarith
  obtain ⟨M, hM0, hMb⟩ := exists_band_bound_paperPhi_auxF s hX ha has
  set C' : ℝ := max (2*C) (M*(1+γ₀^2)) with hC'_def
  have hbound : ∀ ρ : ZetaZeros K,
      ‖(zetaZeroDivisor K ρ.1 : ℂ) * paperPhi (auxF s X) ρ.1‖
        ≤ C' * ((zetaZeroDivisor K ρ.1 : ℝ) / (1^2 + ρ.1.im^2)) := by
    intro ρ
    have hre := ZetaZeros_re_eq_half K hGRH ρ
    set γ : ℝ := ρ.1.im with hγ_def
    have hρ_eq : ρ.1 = ((1/2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I := by
      apply Complex.ext
      · simpa using hre
      · simp [hγ_def]
    have hden : (0:ℝ) < 1 + γ^2 := by positivity
    -- the uniform bound `‖Φ(1/2+iγ)‖ ≤ C'/(1+γ²)`
    have hΦbound : ‖paperPhi (auxF s X) ρ.1‖ ≤ C' / (1 + γ^2) := by
      by_cases hcase : γ₀ ≤ |γ|
      · -- tail regime: the quadratic Fourier decay
        have h12 : ((1/2 : ℝ) : ℂ) = (1/2 : ℂ) := by norm_num
        have hval : paperPhi (auxF s X) ρ.1 = paperFourierIntegral (auxF s X) γ := by
          rw [hρ_eq, h12, paperPhi_half_add_mul_I]
        rw [hval]
        refine (hφ γ hcase).trans ?_
        have hγ1 : (1:ℝ) ≤ |γ| := le_trans hγ₀ hcase
        have hγsq : (1:ℝ) ≤ γ^2 := by
          have := sq_abs γ
          nlinarith
        have h1 : C/γ^2 ≤ 2*C/(1+γ^2) := by
          rw [div_le_div_iff₀ (by positivity) hden]
          nlinarith
        refine h1.trans ?_
        gcongr
        exact le_max_left _ _
      · -- compact regime: the band bound at `σ = 1/2`
        have hcase' : |γ| < γ₀ := not_le.mp hcase
        have hb := hMb (1/2) γ (by linarith) (by linarith)
        rw [← hρ_eq] at hb
        refine hb.trans ?_
        have h1 : M / max |γ| 1 ≤ M := by
          refine div_le_self hM0 (le_max_right _ _)
        refine h1.trans ?_
        have hγsq : γ^2 ≤ γ₀^2 := by
          have h2 : |γ| ≤ γ₀ := le_of_lt hcase'
          have := sq_abs γ
          nlinarith [abs_nonneg γ]
        rw [le_div_iff₀ hden]
        have hMC : M * (1+γ₀^2) ≤ C' := le_max_right _ _
        nlinarith
    -- assemble the product bound
    have hdnn : (0:ℝ) ≤ (zetaZeroDivisor K ρ.1 : ℝ) := by
      exact_mod_cast zetaZeroDivisor_nonneg K ρ.1
    rw [norm_mul]
    have hnormd : ‖((zetaZeroDivisor K ρ.1 : ℤ) : ℂ)‖ = (zetaZeroDivisor K ρ.1 : ℝ) := by
      rw [Complex.norm_intCast, abs_of_nonneg]
      exact_mod_cast zetaZeroDivisor_nonneg K ρ.1
    rw [hnormd]
    calc (zetaZeroDivisor K ρ.1 : ℝ) * ‖paperPhi (auxF s X) ρ.1‖
        ≤ (zetaZeroDivisor K ρ.1 : ℝ) * (C' / (1 + γ^2)) :=
          mul_le_mul_of_nonneg_left hΦbound hdnn
      _ = C' * ((zetaZeroDivisor K ρ.1 : ℝ) / (1^2 + γ^2)) := by
          rw [one_pow]
          ring
  have hmaj : Summable (fun ρ : ZetaZeros K =>
      C' * ((zetaZeroDivisor K ρ.1 : ℝ) / (1^2 + ρ.1.im^2))) :=
    (summable_zetaZeros_inv_sq K 1 one_pos).mul_left C'
  exact Summable.of_norm_bounded hmaj hbound

/-- **The explicit formula as an absolutely convergent zero sum** (the b6 bridge to
Belabas–Friedman Lemma 3): under GRH, for `1 < X` and `0 < a ≤ 1/4` with
`a < Re s − 1`, the divisor-weighted sum of `Φ_{F_{s,X}}` over the full zero index
equals Poitou's right-hand side of the explicit formula at `F_{s,X}`. This removes
the `T → ∞` limit from `weil_explicit_formula_auxF` (uniqueness of limits against
`tendsto_finsum_window_zetaZeros`). -/
theorem tsum_zetaZeros_paperPhi_auxF_eq (hGRH : GeneralizedRiemannHypothesis K)
    (s : ℂ) {X : ℝ} (hX : 1 < X) {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1/4)
    (has : a < s.re - 1) :
    ∑' ρ : ZetaZeros K, (zetaZeroDivisor K ρ.1 : ℂ) * paperPhi (auxF s X) ρ.1
      = (paperPhi (auxF s X) 0 + paperPhi (auxF s X) 1)
          + ((Real.log |NumberField.discr K| : ℝ) : ℂ) * auxF s X 0
          + (((-(((NumberField.InfinitePlace.nrRealPlaces K : ℝ)
              + 2*(NumberField.InfinitePlace.nrComplexPlaces K : ℝ))
                * (Real.eulerMascheroniConstant + Real.log (8*π))
              + (NumberField.InfinitePlace.nrRealPlaces K : ℝ) * (π/2)) : ℝ)) : ℂ)
              * auxF s X 0
          + (((NumberField.InfinitePlace.nrRealPlaces K
              + 2*NumberField.InfinitePlace.nrComplexPlaces K : ℕ)) : ℂ)
              * (∫ y in Set.Ioi (0:ℝ),
                ((1/(2 * Real.sinh (y/2)) : ℝ) : ℂ) * (auxF s X 0 - auxF s X y))
          + ((NumberField.InfinitePlace.nrRealPlaces K : ℕ) : ℂ)
              * (∫ y in Set.Ioi (0:ℝ),
                ((1/(2 * Real.cosh (y/2)) : ℝ) : ℂ) * (auxF s X 0 - auxF s X y))
          - (primeSideH K a (auxF s X) 0 + primeSideH K a (auxF s X) 0) := by
  have hs : 1 < s.re := by linarith
  obtain ⟨T, hTtop, hTlim⟩ := weil_explicit_formula_auxF K s hX ha ha' has
  exact tendsto_nhds_unique
    (tendsto_finsum_window_zetaZeros K hGRH
      (summable_zetaZeros_paperPhi_auxF K hGRH s hX hs) ha hTtop)
    hTlim

end DedekindResidue

end

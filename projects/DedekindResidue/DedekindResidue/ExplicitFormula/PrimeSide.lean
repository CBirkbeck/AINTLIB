module

public import Mathlib
public import DedekindResidue.ExplicitFormula.ZeroCapture

/-!
# The prime side of the explicit formula  (SP2-vM)

Poitou's ultrametric side (p. 6-02) needs the Dirichlet series of the logarithmic
derivative: `−ζ_K'/ζ_K(s) = ∑_{𝔭,m} log(N𝔭)·N𝔭^{-ms}` on `Re s > 1`. This file
differentiates Chebotarev's prime-ideal Euler product through locally uniform
convergence (`logDeriv_tprod_eq_tsum`) to obtain the closed form
`−ζ_K'/ζ_K(s) = ∑_𝔭 log(N𝔭)·N𝔭^{-s}/(1 − N𝔭^{-s})`; the geometric `m`-expansion
is deferred to the Fubini step of Proposition 2.

## Main declarations
* `summable_primeIdeal_rpow`, `summable_primeIdeal_log_rpow` — prime-ideal Dirichlet
  convergence (with logarithmic weights, via exponent absorption);
* `logDeriv_euler_factor` — the single-factor computation;
* `euler_g_bound`, `euler_factor_ne_zero`, `euler_inv_norm_le_two` — uniform factor
  estimates on `Re ≥ σ₀ > 1`;
* `multipliableLocallyUniformlyOn_eulerFactors` — the Euler product converges locally
  uniformly on the half-plane;
* `neg_logDeriv_dedekindZeta_eq_tsum` — the prime-side series.

Route: `.mathlib-quality/decomposition-sp2.md`, leaf SP2-vM.
-/

@[expose] public section

namespace DedekindResidue

open MeasureTheory Complex NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- Prime-ideal norm sums converge for real exponent `σ > 1` (comparison with the full
ideal Dirichlet series). -/
theorem summable_primeIdeal_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ)) := by
  have hσsum : Summable (fun I : Chebotarev.NonzeroIdeal K =>
      (Ideal.absNorm I.1 : ℝ) ^ (-σ)) := by
    have h1 := (Chebotarev.hasSum_nonzeroIdeal_absNorm_cpow K
      (s := ((σ : ℝ) : ℂ)) (by simpa using hσ)).summable
    have h1' : Summable (fun I : Chebotarev.NonzeroIdeal K =>
        (((Ideal.absNorm I.1 : ℝ) ^ (-σ) : ℝ) : ℂ)) := by
      refine h1.congr (fun I => ?_)
      rw [show ((Ideal.absNorm I.1 : ℕ) : ℂ) = (((Ideal.absNorm I.1 : ℝ)) : ℂ) by
          push_cast; ring,
        show -(((σ : ℝ)) : ℂ) = (((-σ : ℝ)) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow (Nat.cast_nonneg _)]
    exact Complex.summable_ofReal.mp h1'
  have hinj : Function.Injective
      (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
        (⟨𝔭.1, 𝔭.2.2⟩ : Chebotarev.NonzeroIdeal K)) := by
    intro 𝔭 𝔮 h
    have h' : (⟨𝔭.1, 𝔭.2.2⟩ : Chebotarev.NonzeroIdeal K) = ⟨𝔮.1, 𝔮.2.2⟩ := h
    exact Subtype.ext (Subtype.mk_eq_mk.mp h')
  exact (hσsum.comp_injective hinj).congr (fun 𝔭 => rfl)

/-- Log-weighted prime-ideal norm sums converge for `σ > 1`: absorb the logarithm
into a slightly smaller exponent. -/
theorem summable_primeIdeal_log_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
      Real.log (Ideal.absNorm 𝔭.1) * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ)) := by
  set δ : ℝ := (σ - 1)/2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hexp : 1 < σ - δ := by rw [hδ]; linarith
  refine Summable.of_nonneg_of_le (fun 𝔭 => ?_) (fun 𝔭 => ?_)
    ((summable_primeIdeal_rpow K hexp).mul_left (1/δ))
  · have hN : (1:ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by
      have h0 : Ideal.absNorm 𝔭.1 ≠ 0 :=
        fun h => 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
    have := Real.log_nonneg hN
    positivity
  · have hN : (1:ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by
      have h0 : Ideal.absNorm 𝔭.1 ≠ 0 :=
        fun h => 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
    have hNpos : (0:ℝ) < (Ideal.absNorm 𝔭.1 : ℝ) := by linarith
    -- log N ≤ N^δ/δ
    have hlog : Real.log (Ideal.absNorm 𝔭.1) ≤ (Ideal.absNorm 𝔭.1 : ℝ)^δ / δ := by
      have h1 : Real.log ((Ideal.absNorm 𝔭.1 : ℝ)^δ)
          ≤ (Ideal.absNorm 𝔭.1 : ℝ)^δ - 1 :=
        Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hNpos δ)
      rw [Real.log_rpow hNpos] at h1
      refine (le_div_iff₀ hδpos).mpr ?_
      have h3 : (0:ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ)^δ := (Real.rpow_pos_of_pos hNpos δ).le
      nlinarith
    calc Real.log (Ideal.absNorm 𝔭.1) * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ)
        ≤ ((Ideal.absNorm 𝔭.1 : ℝ)^δ / δ) * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hNpos.le _)
      _ = (1/δ) * ((Ideal.absNorm 𝔭.1 : ℝ)^δ * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ)) := by
          ring
      _ = (1/δ) * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(σ - δ)) := by
          rw [← Real.rpow_add hNpos, show δ + -σ = -(σ - δ) by ring]

/-- Logarithmic derivative of a single Euler factor:
`(d/dz) log (1 - c^{-z})⁻¹ = -(log c)·c^{-z}/(1 - c^{-z})`. -/
theorem logDeriv_euler_factor {c : ℂ} (hc : c ≠ 0) (z : ℂ) :
    logDeriv (fun w => (1 - c ^ (-w))⁻¹) z
      = -(Complex.log c * c ^ (-z) / (1 - c ^ (-z))) := by
  have hinner_deriv : HasDerivAt (fun w : ℂ => 1 - c ^ (-w))
      (Complex.log c * c ^ (-z)) z := by
    have h1 : HasDerivAt (fun w : ℂ => -w) (-1 : ℂ) z := (hasDerivAt_id z).neg
    have h2 := h1.const_cpow (c := c) (Or.inl hc)
    have h3 := h2.const_sub 1
    rw [show -(c ^ (-z) * Complex.log c * (-1)) = Complex.log c * c ^ (-z) by ring] at h3
    exact h3
  have hinner_diff : DifferentiableAt ℂ (fun w : ℂ => 1 - c ^ (-w)) z :=
    hinner_deriv.differentiableAt
  have hfun : (fun w : ℂ => (1 - c ^ (-w))⁻¹)
      = fun w : ℂ => (fun v : ℂ => 1 - c ^ (-v)) w ^ (-1 : ℤ) := by
    funext w
    rw [zpow_neg_one]
  rw [hfun, logDeriv_fun_zpow hinner_diff]
  have hld : logDeriv (fun w : ℂ => 1 - c ^ (-w)) z
      = Complex.log c * c ^ (-z) / (1 - c ^ (-z)) := by
    rw [logDeriv_apply, hinner_deriv.deriv]
  rw [hld]
  push_cast
  ring

/-- On a compact subset of the half-plane `Re > 1`, the real part attains a minimum
`σ₀ > 1`. -/
theorem exists_min_re_of_isCompact {S : Set ℂ} (hS : IsCompact S) (hne : S.Nonempty)
    (hsub : S ⊆ {z : ℂ | 1 < z.re}) :
    ∃ σ₀ : ℝ, 1 < σ₀ ∧ ∀ x ∈ S, σ₀ ≤ x.re := by
  obtain ⟨z₀, hz₀S, hz₀min⟩ := hS.exists_isMinOn hne
    (Complex.continuous_re.continuousOn)
  exact ⟨z₀.re, hsub hz₀S, fun x hx => hz₀min hx⟩

/-- Norm bound for the Euler-factor correction on `Re ≥ σ₀ > 1`. -/
theorem euler_g_bound (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) {x : ℂ} {σ₀ : ℝ}
    (h1 : 1 < σ₀) (h2 : σ₀ ≤ x.re) :
    ‖(1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-x))⁻¹ - 1‖
      ≤ 2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ₀) := by
  have hne0 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h => 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
  have hne1 : Ideal.absNorm 𝔭.1 ≠ 1 := fun h => 𝔭.2.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hN2 : (2:ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by
    have : 2 ≤ Ideal.absNorm 𝔭.1 := by omega
    exact_mod_cast this
  have hnorm : ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-x)‖ = (Ideal.absNorm 𝔭.1 : ℝ) ^ (-x.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  have hle : ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-x)‖ ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ₀) := by
    rw [hnorm]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hhalf : ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-x)‖ ≤ 1/2 := by
    refine le_trans hle ?_
    have hstep1 : (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ₀) ≤ (2:ℝ) ^ (-σ₀) := by
      rw [Real.rpow_neg (by linarith), Real.rpow_neg (by norm_num)]
      refine (inv_le_inv₀ (Real.rpow_pos_of_pos (by linarith) _)
        (Real.rpow_pos_of_pos (by norm_num) _)).mpr ?_
      exact Real.rpow_le_rpow (by norm_num) hN2 (by linarith)
    have hstep2 : (2:ℝ) ^ (-σ₀) ≤ (2:ℝ) ^ (-(1:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hstep3 : (2:ℝ) ^ (-(1:ℝ)) = 1/2 := by
      rw [Real.rpow_neg_one]
      norm_num
    calc (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ₀) ≤ (2:ℝ) ^ (-σ₀) := hstep1
      _ ≤ (2:ℝ) ^ (-(1:ℝ)) := hstep2
      _ = 1/2 := hstep3
  set w : ℂ := (Ideal.absNorm 𝔭.1 : ℂ) ^ (-x) with hwdef
  have hfac_ne : (1 : ℂ) - w ≠ 0 := by
    intro h0
    have h1' : w = 1 := by linear_combination -h0
    rw [h1'] at hhalf
    norm_num at hhalf
  have hid : (1 - w)⁻¹ - 1 = w * (1 - w)⁻¹ := by
    field_simp
    ring
  rw [hid, norm_mul]
  have hlow : (1:ℝ)/2 ≤ ‖1 - w‖ := by
    have h1' : ‖(1:ℂ)‖ - ‖w‖ ≤ ‖1 - w‖ := norm_sub_norm_le _ _
    rw [norm_one] at h1'
    linarith
  have hinv : ‖(1 - w)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    rw [show (2:ℝ) = (1/2)⁻¹ by norm_num]
    refine (inv_le_inv₀ ?_ (by norm_num)).mpr hlow
    linarith
  calc ‖w‖ * ‖(1 - w)⁻¹‖ ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ₀) * 2 :=
        mul_le_mul hle hinv (norm_nonneg _) (Real.rpow_nonneg (by linarith) _)
    _ = 2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ₀) := by ring

/-- The Euler product over prime ideals is locally uniformly multipliable on the
half-plane `Re > 1`. -/
theorem multipliableLocallyUniformlyOn_eulerFactors :
    MultipliableLocallyUniformlyOn
      (fun (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (z : ℂ) =>
        (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-z))⁻¹)
      {z : ℂ | 1 < z.re} := by
  have hfun : (fun (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (z : ℂ) =>
      (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-z))⁻¹)
      = fun 𝔭 z => 1 + ((1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-z))⁻¹ - 1) := by
    funext 𝔭 z
    ring
  rw [hfun]
  refine ⟨fun z => ∏' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
    (1 + ((1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-z))⁻¹ - 1)), ?_⟩
  refine hasProdLocallyUniformlyOn_of_forall_compact
    (isOpen_lt continuous_const Complex.continuous_re) ?_
  intro S hsub hcS
  rcases S.eq_empty_or_nonempty with hN | hN
  · simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn, hN] using tendstoUniformlyOn_empty
  obtain ⟨σ₀, hσ₀, hσ₀min⟩ := exists_min_re_of_isCompact hcS hN hsub
  have hnonvan : ∀ (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}), ∀ x ∈ S,
      (1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-x) ≠ 0 := by
    intro 𝔭 x hx h0
    have hb := euler_g_bound K 𝔭 hσ₀ (hσ₀min x hx)
    rw [h0] at hb
    simp only [inv_zero, zero_sub, norm_neg, norm_one] at hb
    have hN2 : (2:ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by
      have hne0 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h => 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
      have hne1 : Ideal.absNorm 𝔭.1 ≠ 1 :=
        fun h => 𝔭.2.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
      have : 2 ≤ Ideal.absNorm 𝔭.1 := by omega
      exact_mod_cast this
    have hsmall : 2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ₀) ≤ 2 * (2:ℝ)^(-σ₀) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      rw [Real.rpow_neg (by linarith), Real.rpow_neg (by norm_num)]
      refine (inv_le_inv₀ (Real.rpow_pos_of_pos (by linarith) _)
        (Real.rpow_pos_of_pos (by norm_num) _)).mpr ?_
      exact Real.rpow_le_rpow (by norm_num) hN2 (by linarith)
    have h2s : (2:ℝ) * (2:ℝ)^(-σ₀) < 1 := by
      have hs2 : (2:ℝ)^(-σ₀) < (2:ℝ)^(-(1:ℝ)) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      rw [Real.rpow_neg_one] at hs2
      norm_num at hs2
      linarith
    linarith
  have hsum_u : Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
      2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-σ₀)) :=
    (summable_primeIdeal_rpow K hσ₀).mul_left 2
  refine hsum_u.hasProdUniformlyOn_one_add hcS ?_ ?_
  · refine Filter.Eventually.of_forall (fun 𝔭 x hx => ?_)
    exact euler_g_bound K 𝔭 hσ₀ (hσ₀min x hx)
  · intro 𝔭
    refine ContinuousOn.sub ?_ continuousOn_const
    refine ContinuousOn.inv₀ ?_ (fun x hx => hnonvan 𝔭 x hx)
    refine ContinuousOn.sub continuousOn_const ?_
    refine Continuous.continuousOn ?_
    refine Continuous.const_cpow continuous_neg ?_
    left
    intro h0
    have hne0 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h => 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
    rw [show ((Ideal.absNorm 𝔭.1 : ℕ) : ℂ) = 0 ↔ Ideal.absNorm 𝔭.1 = 0 from
      Nat.cast_eq_zero] at h0
    exact hne0 h0

/-- Euler factors do not vanish on `Re > 1`. -/
theorem euler_factor_ne_zero (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) {x : ℂ}
    (hx : 1 < x.re) :
    (1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-x) ≠ 0 := by
  intro h0
  have hb := euler_g_bound K 𝔭 hx (le_refl x.re)
  rw [h0] at hb
  simp only [inv_zero, zero_sub, norm_neg, norm_one] at hb
  have hne0 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h => 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
  have hne1 : Ideal.absNorm 𝔭.1 ≠ 1 := fun h => 𝔭.2.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hN2 : (2:ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by
    have : 2 ≤ Ideal.absNorm 𝔭.1 := by omega
    exact_mod_cast this
  have hsmall : 2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-x.re) ≤ 2 * (2:ℝ)^(-x.re) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [Real.rpow_neg (by linarith), Real.rpow_neg (by norm_num)]
    refine (inv_le_inv₀ (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_pos_of_pos (by norm_num) _)).mpr ?_
    exact Real.rpow_le_rpow (by norm_num) hN2 (by linarith)
  have h2s : (2:ℝ) * (2:ℝ)^(-x.re) < 1 := by
    have hs2 : (2:ℝ)^(-x.re) < (2:ℝ)^(-(1:ℝ)) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    rw [Real.rpow_neg_one] at hs2
    norm_num at hs2
    linarith
  linarith

/-- The inverse Euler factor has norm at most `2` on `Re > 1`. -/
theorem euler_inv_norm_le_two (𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) {x : ℂ}
    (hx : 1 < x.re) :
    ‖((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-x))⁻¹‖ ≤ 2 := by
  have hb := euler_g_bound K 𝔭 hx (le_refl x.re)
  have hne0 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h => 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
  have hne1 : Ideal.absNorm 𝔭.1 ≠ 1 := fun h => 𝔭.2.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hN2 : (2:ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by
    have : 2 ≤ Ideal.absNorm 𝔭.1 := by omega
    exact_mod_cast this
  have hsmall : 2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-x.re) ≤ 1 := by
    have h1 : 2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-x.re) ≤ 2 * (2:ℝ)^(-x.re) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      rw [Real.rpow_neg (by linarith), Real.rpow_neg (by norm_num)]
      refine (inv_le_inv₀ (Real.rpow_pos_of_pos (by linarith) _)
        (Real.rpow_pos_of_pos (by norm_num) _)).mpr ?_
      exact Real.rpow_le_rpow (by norm_num) hN2 (by linarith)
    have h2 : (2:ℝ) * (2:ℝ)^(-x.re) ≤ 1 := by
      have hs2 : (2:ℝ)^(-x.re) ≤ (2:ℝ)^(-(1:ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      rw [Real.rpow_neg_one] at hs2
      norm_num at hs2
      linarith
    linarith
  calc ‖((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-x))⁻¹‖
      ≤ ‖((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-x))⁻¹ - 1‖ + ‖(1:ℂ)‖ :=
        norm_le_norm_sub_add _ _
    _ ≤ 2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-x.re) + 1 := by
        rw [norm_one]
        linarith [hb]
    _ ≤ 2 := by linarith

/-- **SP2-vM: the prime-side series** (Poitou p. 6-02): for `Re s > 1`,
`−ζ_K'/ζ_K(s) = ∑_𝔭 log(N𝔭)·N𝔭^{-s}/(1 − N𝔭^{-s})`, differentiating the Euler
product through the locally uniform convergence. -/
theorem neg_logDeriv_dedekindZeta_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    -(logDeriv (NumberField.dedekindZeta K) s)
      = ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
          Complex.log (Ideal.absNorm 𝔭.1 : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)
            / (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)) := by
  have hUo : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ {z : ℂ | 1 < z.re} := hs
  have hNcast : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      ((Ideal.absNorm 𝔭.1 : ℕ) : ℂ) ≠ 0 := by
    intro 𝔭 h0
    have hne0 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h => 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
    exact hne0 (Nat.cast_eq_zero.mp h0)
  have hf_ne : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      ((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ ≠ 0 :=
    fun 𝔭 => inv_ne_zero (euler_factor_ne_zero K 𝔭 hs)
  have hd : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      DifferentiableOn ℂ (fun z => ((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-z))⁻¹)
        {z : ℂ | 1 < z.re} := by
    intro 𝔭 z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.inv ?_ (euler_factor_ne_zero K 𝔭 hz)
    refine DifferentiableAt.const_sub ?_ 1
    exact (differentiable_neg.differentiableAt).const_cpow (Or.inl (hNcast 𝔭))
  -- summability of the factor log-derivatives at s
  have hclosed_bound : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      ‖-(Complex.log (Ideal.absNorm 𝔭.1 : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)
        / (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)))‖
      ≤ 2 * (Real.log (Ideal.absNorm 𝔭.1) * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s.re)) := by
    intro 𝔭
    have hne0 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h => 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
    have hN1 : (1:ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne0
    have hlogeq : ‖Complex.log (Ideal.absNorm 𝔭.1 : ℂ)‖ = Real.log (Ideal.absNorm 𝔭.1) := by
      rw [show ((Ideal.absNorm 𝔭.1 : ℕ) : ℂ) = (((Ideal.absNorm 𝔭.1 : ℝ)) : ℂ) by
          push_cast; ring,
        ← Complex.ofReal_log (by linarith), Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg hN1)]
    have hweq : ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ = (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    rw [norm_neg, norm_div, norm_mul, hlogeq, hweq]
    rw [div_eq_mul_inv, ← norm_inv]
    calc Real.log (Ideal.absNorm 𝔭.1) * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s.re)
        * ‖((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹‖
        ≤ Real.log (Ideal.absNorm 𝔭.1) * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s.re) * 2 := by
          refine mul_le_mul_of_nonneg_left (euler_inv_norm_le_two K 𝔭 hs) ?_
          have := Real.log_nonneg hN1
          positivity
      _ = 2 * (Real.log (Ideal.absNorm 𝔭.1) * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s.re)) := by
          ring
  have hclosed_sum : Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
      -(Complex.log (Ideal.absNorm 𝔭.1 : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)
        / (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)))) := by
    refine Summable.of_norm_bounded ?_ hclosed_bound
    exact (summable_primeIdeal_log_rpow K hs).mul_left 2
  have hld_eq : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      logDeriv (fun z => ((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-z))⁻¹) s
        = -(Complex.log (Ideal.absNorm 𝔭.1 : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)
            / (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))) :=
    fun 𝔭 => logDeriv_euler_factor (hNcast 𝔭) s
  have hm : Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
      logDeriv (fun z => ((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-z))⁻¹) s) :=
    hclosed_sum.congr (fun 𝔭 => (hld_eq 𝔭).symm)
  have hnez : (∏' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      ((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹) ≠ 0 := by
    rw [← Chebotarev.dedekindZeta_eq_tprod_primeIdeal K hs]
    exact dedekindZeta_ne_zero_of_one_lt_re K hs
  have hkey := logDeriv_tprod_eq_tsum hUo hsU hf_ne hd hm
    (multipliableLocallyUniformlyOn_eulerFactors K) hnez
  have hev : NumberField.dedekindZeta K =ᶠ[nhds s]
      (fun z => ∏' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        ((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-z))⁻¹) := by
    filter_upwards [hUo.mem_nhds hsU] with z hz
    exact Chebotarev.dedekindZeta_eq_tprod_primeIdeal K hz
  have hζld : logDeriv (NumberField.dedekindZeta K) s
      = logDeriv (fun z => ∏' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
          ((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-z))⁻¹) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  calc -(logDeriv (NumberField.dedekindZeta K) s)
      = -(∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
          logDeriv (fun z => ((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-z))⁻¹) s) := by
        rw [hζld, hkey]
    _ = ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
          -(logDeriv (fun z => ((1 : ℂ) - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-z))⁻¹) s) :=
        tsum_neg.symm
    _ = ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
          Complex.log (Ideal.absNorm 𝔭.1 : ℂ) * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)
            / (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)) := by
        refine tsum_congr (fun 𝔭 => ?_)
        rw [hld_eq 𝔭, neg_neg]

end DedekindResidue

end

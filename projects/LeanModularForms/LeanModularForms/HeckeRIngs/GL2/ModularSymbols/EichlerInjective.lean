/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.PeriodInjective
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.PeriodHecke
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Eichler-integral proof of period-map injectivity (`k ≥ 2`)

The *Eichler-integral* route to `periodMap'_injective` (decomposition
`.mathlib-quality/decomposition-eichler.md`, tree §Step 2).  The top result
`periodMap'_injective_eichler` is now **fully PROVEN and axiom-clean**.  The last residual
`eichler_slashSL_bdd_finite` (sub-ticket EICH-3a-i) — the boundedness of the slashed Eichler
integral
at a *finite* cusp (`γ • ∞ ≠ ∞`, i.e. `γ₁₀ ≠ 0`) — is closed: after slashing by `γ ∈ SL(2,ℤ)`, the
function decomposes as `(E_f∘↑)∣[2-k]γ = E_g − C_k·cuspValueGen g ((·-τ)ⁿ)(γ⁻¹∞)`, where `E_g` is
the
`∞`-Eichler integral of the conjugate cusp form `g := f∣[k]γ`
(`eichler_slashSL_eq_eichlerIntegralGen_sub_cuspValueGen`, the honest general-`γ` form of
`eichler_defect_eq_cuspValueMoving` via the Möbius change of variables + the generic interior-ray
FTC
`rayGen_integral_eq_top_sub`).  The conjugate cusp value vanishes under `ι(f)=0`
(`cuspValueGen_translate_eq_zero`: `ι(f)=0 ⟹ ι(g)=0` via `rawPairingGen_actMat` since `γ` has det
`1`,
plus the generic base-point independence), so the slash *is* `C_k·E_g`, which is bounded at `i∞`
by the
dominated-integral cusp-decay bound `eichlerIntegralGen_isBoundedAtImInfty`.  The all-`γ`
cusp-boundedness `eichler_bdd_at_cusp` is therefore PROVEN by case split: the `γ • ∞ = ∞` (`γ₁₀ =
0`)
case via the cusp-`∞` bound transfer (`eichler_cusp_holo`), the finite-cusp case via the above.
`#print axioms periodMap'_injective_eichler` is `[propext, Classical.choice, Quot.sound]` — NO
`sorryAx`, NO `interior_edges_cancel_sum`; `HeckeAlgFiniteFinal.heckeAlgℤ_finite` (k≥2) consumes
this
route, so the whole `k≥2` integral-Hecke-ring-finiteness chain is axiom-clean.

The mathematical content (reply.md §1, transcribed in the decomposition):

* `G1` Eichler integral `E_f(z) = Σ_{m≥1} (a_m/m^{k-1}) q^m` with `D^{k-1} E_f = f`.  [PROVEN]
* `G2`/`L7` modularity defect: `ι(f)=0 ⟹ E_f|_{2-k}γ = E_f` for all `γ ∈ Γ₁(N)`.  [PROVEN]
* `G3` holomorphy / vanishing at every cusp of `E_f`.  [PROVEN: `∞`-cusp + every `γ • ∞ = ∞` cusp
  (`eichler_cusp_holo`, `eichler_isZeroAtImInfty`); the finite cusp `γ₁₀ ≠ 0` via
  `eichler_slashSL_bdd_finite` (EICH-3a-i, the `E_g + period-polynomial` decomposition)]
* `G4`/`L9` the weight-`(2-k)` packaging (`eichlerModularForm`) + negative/zero-weight vanishing
  ⟹ `E_f = 0` (`eichler_eq_zero`).  [PROVEN]
* `R`/`FINAL` then `f = D^{k-1} E_f = 0`, i.e. `periodMap'` is injective.  [PROVEN modulo EICH-3a-i]

## TYPE-LEVEL ARCHITECTURE NOTES (see per-declaration notes below)

The two flagged architecture gaps `G2` (slash of a `ℂ → ℂ` function at weight `2-k`) and `G4a`
(packaging `E_f` as a `ModularForm Γ (2-k)` with `k ≥ 2`, so `2-k ≤ 0`) are addressed by bridging a
`ℂ → ℂ` function to a `ℍ → ℂ` function by **precomposition with the coercion** `((↑) : ℍ → ℂ)`
(`UpperHalfPlane.coe`), i.e. `(eichlerIntegral f) ∘ ((↑) : ℍ → ℂ)` — the `ℍ → ℂ` carrier the mathlib
`SlashAction` and `ModularForm` structure both require.  (The project's `periodForm` is defined the
other way, on `ℂ`, via `f (UpperHalfPlane.ofComplex z)`; here we keep `eichlerIntegral` on `ℂ` and
restrict to `ℍ` for the slash/packaging.)  The mathlib weight-`k` `SlashAction` is on `ℍ → ℂ` and
accepts **any** `k : ℤ` (incl. negative), and `ModularForm Γ k` is defined for any `k : ℤ`, so the
negative-weight packaging type-checks.

## References

* reply.md (expert-review/2026-06-24) §1–§2; Shimura §8.2; Diamond–Shurman §5.x;
  arXiv:1701.00611 (Bol); Res. Math. Sci. doi 10.1007/s40687-018-0128-2.
-/

noncomputable section

namespace HeckeRing.GL2.ModularSymbols

open scoped MatrixGroups ModularForm Topology Pointwise TensorProduct Real
open UpperHalfPlane Complex MeasureTheory Filter CongruenceSubgroup
  Matrix.SpecialLinearGroup

variable {N : ℕ} [NeZero N] {k : ℤ}

/-! ## `G1` — the Eichler integral and `D^{k-1} E_f = f` -/

/-- The `m`-th coefficient of the Eichler integral `q`-series: `a_m / m^{k-1}` where `a_m` is the
`m`-th Fourier coefficient of `f` at `∞` (the `q`-expansion of `f` taken at the cusp width `1` of
`Γ₁(N)`).  For `m = 0` this is `a_0 / 0^{k-1} = 0` (and `a_0 = 0` since `f` is a cusp form), so the
constant term vanishes.  The power is taken as a natural-number power with exponent `(k-1).toNat`,
which equals `k-1` for `k ≥ 2`. -/
private def eichlerCoeff (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (m : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m / (m : ℂ) ^ (k - 1).toNat

/-- The `j`-fold formally differentiated Eichler `q`-series: `Σ_m (a_m/m^{k-1}) (2πi m)^j q^m`,
where `q = exp(2πi z)`.  For `j = 0` this is the Eichler integral itself; each application of
`d/dz` increases `j` by one (it brings down a factor `2πi m` per term). -/
private def eichlerQSeries (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (j : ℕ) (z : ℂ) : ℂ :=
  ∑' m : ℕ, eichlerCoeff f m * (2 * (π : ℂ) * Complex.I * m) ^ j *
    Complex.exp (2 * (π : ℂ) * Complex.I * m * z)

omit [NeZero N] in
/-- `1` is a strict period of `Γ₁(N)` (the cusp width at `∞` is `1`). -/
private lemma one_mem_strictPeriods_Gamma1 :
    (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
  rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
    CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples 1

omit [NeZero N] in
/-- The `q`-expansion of a cusp form sums to its value: `Σ_m a_m q^m = f τ`. -/
private lemma hasSum_qExpansion_eichler (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m •
      Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m) (f τ) :=
  haveI : Fact (IsCusp OnePoint.infty ((Gamma1 N).map (mapGL ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos one_mem_strictPeriods_Gamma1⟩
  UpperHalfPlane.hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_Gamma1)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ

/-- For any `r : ℝ≥0` with `r < 1`, the Fourier coefficients of `f` weighted by `r^m` are
absolutely summable: this is the statement that the `q`-expansion has radius of convergence `≥ 1`.
-/
private lemma summable_norm_coeff_mul_geom (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {r : NNReal} (hr : (r : ℝ) < 1) :
    Summable (fun m : ℕ ↦ ‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ * (r : ℝ) ^ m) := by
  have hrad : 1 ≤ (UpperHalfPlane.qExpansionFormalMultilinearSeries (1 : ℝ) f).radius :=
    UpperHalfPlane.qExpansionFormalMultilinearSeries_radius f one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_Gamma1)
      (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)
  have hr1 : (r : ENNReal) < (UpperHalfPlane.qExpansionFormalMultilinearSeries (1 : ℝ) f).radius :=
    lt_of_lt_of_le (by exact_mod_cast hr) hrad
  have := (UpperHalfPlane.qExpansionFormalMultilinearSeries (1 : ℝ) f).summable_norm_mul_pow hr1
  simpa only [UpperHalfPlane.qExpansionFormalMultilinearSeries_apply_norm] using this

/-- The summability bound powering the term-by-term differentiation: for any polynomial degree `j`
and any geometric ratio `ρ ∈ [0, 1)`, the dominating sequence `‖a_m‖ · m^j · ρ^m` is summable. -/
private lemma summable_norm_coeff_mul_pow_geom (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (j : ℕ) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable (fun m : ℕ ↦
      ‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ * (m : ℝ) ^ j * ρ ^ m) := by
  -- Choose an intermediate ratio `ρ < s < 1`.
  set s : ℝ := (ρ + 1) / 2 with hs
  have hsρ : ρ < s := by rw [hs]; linarith
  have hs0 : 0 < s := lt_of_le_of_lt h0 hsρ
  have hs1 : s < 1 := by rw [hs]; linarith
  -- The geometric series with ratio `s` weighted by the Fourier norms is summable.
  have hg : Summable (fun m : ℕ ↦ ‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ * s ^ m) := by
    have := summable_norm_coeff_mul_geom f (r := s.toNNReal)
      (by rwa [Real.coe_toNNReal s hs0.le])
    rwa [Real.coe_toNNReal s hs0.le] at this
  -- `m^j (ρ/s)^m` is summable, hence bounded (`= O(1)`).
  have hu : (fun m : ℕ ↦ (m : ℝ) ^ j * (ρ / s) ^ m) =O[atTop] (fun _ ↦ (1 : ℝ)) := by
    have hrs : ‖ρ / s‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg h0 hs0.le), div_lt_one hs0]; exact hsρ
    exact (summable_pow_mul_geometric_of_norm_lt_one j hrs).tendsto_atTop_zero.isBigO_one ℝ
  -- The target is `O` of the summable geometric series, hence summable.
  refine summable_of_isBigO_nat hg ?_
  have hmul := (Asymptotics.isBigO_refl
    (fun m : ℕ ↦ ‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ * s ^ m) atTop).mul hu
  refine hmul.congr' ?_ ?_
  · filter_upwards with m
    have hps : s ^ m * (ρ / s) ^ m = ρ ^ m := by
      rw [← mul_pow, mul_div_cancel₀ ρ hs0.ne']
    rw [show ‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ * s ^ m * ((m : ℝ) ^ j * (ρ / s) ^ m)
        = ‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ * (m : ℝ) ^ j * (s ^ m * (ρ / s) ^ m) by
      ring, hps]
  · filter_upwards with m; rw [mul_one]

/-- **Single derivative of the Eichler `q`-series.**  On the open upper half-plane,
`d/dz (eichlerQSeries f j) = eichlerQSeries f (j+1)` (and it `HasDerivAt` there): differentiating
term by term brings down one factor `2πi m`, which is exactly the passage `j ↦ j+1`. -/
private lemma hasDerivAt_eichlerQSeries (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (j : ℕ)
    {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (eichlerQSeries f j) (eichlerQSeries f (j + 1) z) z := by
  -- Work on the open half-plane `t = {Im > y₀}` with `0 < y₀ < z.im`.
  set y₀ : ℝ := z.im / 2 with hy₀def
  have hy₀pos : 0 < y₀ := by positivity
  have hzy₀ : y₀ < z.im := by rw [hy₀def]; linarith
  set t : Set ℂ := {w : ℂ | y₀ < w.im} with htdef
  have htopen : IsOpen t := isOpen_lt continuous_const Complex.continuous_im
  have htconn : IsPreconnected t := (convex_halfSpace_im_gt y₀).isPreconnected
  have hzt : z ∈ t := hzy₀
  -- The term functions and their derivatives.
  set g : ℕ → ℂ → ℂ := fun m w ↦
    eichlerCoeff f m * (2 * (π : ℂ) * Complex.I * m) ^ j *
      Complex.exp (2 * (π : ℂ) * Complex.I * m * w) with hgdef
  set g' : ℕ → ℂ → ℂ := fun m w ↦
    eichlerCoeff f m * (2 * (π : ℂ) * Complex.I * m) ^ (j + 1) *
      Complex.exp (2 * (π : ℂ) * Complex.I * m * w) with hg'def
  -- The geometric ratio and the dominating sequence.
  set ρ : ℝ := Real.exp (-(2 * π * y₀)) with hρdef
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := by
    rw [hρdef]; exact Real.exp_lt_one_iff.mpr (by have := Real.pi_pos; nlinarith [hy₀pos])
  set u : ℕ → ℝ := fun m ↦
    (2 * π) ^ (j + 1) *
      (‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ * (m : ℝ) ^ (j + 1) * ρ ^ m)
    with hudef
  -- (i) `u` is summable.
  have hu : Summable u := by
    rw [hudef]
    exact (summable_norm_coeff_mul_pow_geom f (j + 1) hρ0.le hρ1).mul_left _
  -- The norm of `exp(2πi m w)` is `exp(-2π m (w.im))`.
  have hnorm_exp : ∀ (m : ℕ) (w : ℂ),
      ‖Complex.exp (2 * (π : ℂ) * Complex.I * m * w)‖ = Real.exp (-(2 * π * m * w.im)) := by
    intro m w
    have h1 : Complex.exp (2 * (π : ℂ) * Complex.I * m * w)
        = Function.Periodic.qParam 1 w ^ m := by
      rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]; push_cast; ring_nf
    rw [h1, norm_pow, Function.Periodic.norm_qParam, ← Real.exp_nat_mul]
    congr 1; ring
  -- The norm of `2πi m` is `2π m`.
  have hnorm2pi : ∀ m : ℕ, ‖2 * (π : ℂ) * Complex.I * m‖ = 2 * π * m := by
    intro m
    rw [show (2 : ℂ) * (π : ℂ) * Complex.I * m = ((2 * π * m : ℝ) : ℂ) * Complex.I by
        push_cast; ring,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  -- `‖eichlerCoeff f m‖ ≤ ‖coeff m‖` (dividing by `m^n` only shrinks the norm).
  have hcoeff_bd : ∀ m : ℕ,
      ‖eichlerCoeff f m‖ ≤ ‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ := by
    intro m
    rw [eichlerCoeff, norm_div, norm_pow, Complex.norm_natCast]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rcases Nat.eq_zero_or_pos (k - 1).toNat with he | he
      · simp [he]
      · rw [Nat.cast_zero, zero_pow he.ne', div_zero]; exact norm_nonneg _
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg ((UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m),
        one_le_pow₀ (by exact_mod_cast hm : (1 : ℝ) ≤ (m : ℝ)) (n := (k - 1).toNat)]
  -- Uniform bound on the `i`-th derivative term over the half-plane `t`.
  have hbound : ∀ (i m : ℕ) (w : ℂ), y₀ < w.im →
      ‖eichlerCoeff f m * (2 * (π : ℂ) * Complex.I * m) ^ i *
          Complex.exp (2 * (π : ℂ) * Complex.I * m * w)‖
        ≤ (2 * π) ^ i *
            (‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ * (m : ℝ) ^ i * ρ ^ m) := by
    intro i m w hwim
    rw [norm_mul, norm_mul, norm_pow, hnorm2pi, hnorm_exp]
    have hexp_le : Real.exp (-(2 * π * m * w.im)) ≤ ρ ^ m := by
      rw [hρdef, ← Real.exp_nat_mul]
      refine Real.exp_le_exp.mpr ?_
      have hprod : (0 : ℝ) ≤ (2 * π * m) * (w.im - y₀) :=
        mul_nonneg (by positivity) (sub_nonneg.mpr hwim.le)
      nlinarith [hprod]
    rw [show (2 * π) ^ i * (‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ * (m : ℝ) ^ i * ρ ^ m)
        = ‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ * (2 * π * m) ^ i * ρ ^ m by
      rw [mul_pow]; ring]
    refine mul_le_mul ?_ hexp_le (Real.exp_nonneg _) (by positivity)
    gcongr
    exact hcoeff_bd m
  -- (ii) each term is differentiable with the expected derivative on `t`.
  have hg : ∀ (m : ℕ), ∀ w ∈ t, HasDerivAt (g m) (g' m w) w := by
    intro m w _
    have hlin : HasDerivAt (fun w : ℂ ↦ 2 * (π : ℂ) * Complex.I * m * w)
        (2 * (π : ℂ) * Complex.I * m) w := by
      simpa using (hasDerivAt_id w).const_mul (2 * (π : ℂ) * Complex.I * m)
    have hcm := (hlin.cexp).const_mul (eichlerCoeff f m * (2 * (π : ℂ) * Complex.I * m) ^ j)
    have hval : g' m w = eichlerCoeff f m * (2 * (π : ℂ) * Complex.I * m) ^ j *
        (Complex.exp (2 * (π : ℂ) * Complex.I * m * w) * (2 * (π : ℂ) * Complex.I * m)) := by
      rw [hg'def]; dsimp only; rw [pow_succ]; ring
    rw [hgdef, hval]
    exact hcm
  -- (iii) the derivative norms are dominated by `u` on `t`.
  have hg' : ∀ (m : ℕ), ∀ w ∈ t, ‖g' m w‖ ≤ u m := by
    intro m w hw
    simpa only [hg'def, hudef] using hbound (j + 1) m w hw
  -- (iv) the series at the base point `z` is summable (dominated at degree `j`).
  have hg0 : Summable (fun m ↦ g m z) := by
    have hu0 : Summable (fun m ↦ (2 * π) ^ j *
        (‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ * (m : ℝ) ^ j * ρ ^ m)) :=
      (summable_norm_coeff_mul_pow_geom f j hρ0.le hρ1).mul_left _
    refine Summable.of_norm (hu0.of_nonneg_of_le (fun m ↦ norm_nonneg _) (fun m ↦ ?_))
    rw [hgdef]; exact hbound j m z hzt
  -- Assemble: term-by-term differentiation of the `q`-series.
  have hres := hasDerivAt_tsum_of_isPreconnected hu htopen htconn hg hg' hzt hg0 hzt
  rw [hgdef, hg'def] at hres
  exact hres

/-- The `n`-fold iterated derivative of the Eichler `q`-series shifts the polynomial degree by `n`:
`(d/dz)^n (eichlerQSeries f j) = eichlerQSeries f (j+n)` on the upper half-plane. -/
private lemma iteratedDeriv_eichlerQSeries (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (j n : ℕ) {z : ℂ} (hz : 0 < z.im) :
    iteratedDeriv n (eichlerQSeries f j) z = eichlerQSeries f (j + n) z := by
  induction n generalizing j with
  | zero => simp [eichlerQSeries]
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hee : deriv (eichlerQSeries f j) =ᶠ[nhds z] eichlerQSeries f (j + 1) := by
      have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
      filter_upwards [hopen.mem_nhds hz] with w hw
      exact (hasDerivAt_eichlerQSeries f j hw).deriv
    rw [Filter.EventuallyEq.iteratedDeriv_eq n hee, ih (j + 1)]
    congr 1
    omega

/-- **G1a — the Eichler integral `E_f`.**  As a function `ℂ → ℂ` (extended off `ℍ` by the project's
`ofComplex` convention, so it can be slashed and packaged uniformly with `periodForm`).  Informally
`E_f(z) = Σ_{m≥1} (a_m / m^{k-1}) q^m = C_k ∫_z^{i∞} f(τ)(τ-z)^{k-2} dτ` (reply.md §1.1).

TYPE-LEVEL NOTE: stated as `ℂ → ℂ` (not `ℍ → ℂ`) to match `periodForm`'s convention and to make the
weight-`(2-k)` slash (`eichler_slash_invariant`) and the `ModularForm` packaging
(`eichlerModularForm`) go through the same `((↑) : ℍ → ℂ)` (`UpperHalfPlane.coe`) restriction.

IMPLEMENTATION: defined as the `q`-series `Σ_{m} (a_m/m^{k-1}) exp(2πi m z)` (the `m = 0` term is
`0`); off the upper half-plane the series is non-summable and the value is the junk default `0`,
which is irrelevant as all consumers carry a `0 < z.im` hypothesis. -/
def eichlerIntegral (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : ℂ → ℂ :=
  eichlerQSeries f 0

/-- **G1c — holomorphy of `E_f` on the open upper half-plane.**  From the absolutely convergent
`q`-series (or from the project primitive `isExactOn_upperHalf` on the integral side). -/
theorem differentiableOn_eichlerIntegral (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    DifferentiableOn ℂ (eichlerIntegral f) {z : ℂ | 0 < z.im} :=
  fun _z hz ↦ ((hasDerivAt_eichlerQSeries f 0 hz).differentiableAt).differentiableWithinAt

/-- **G1b — Bol's identity in `q`-series form: `D^{k-1} E_f = f`** (reply.md §1.1, with
`D = (1/2πi) d/dz`).  Here `D^{k-1}` is `(k-1).toNat` applications of `iteratedDeriv` scaled by
`((2πi)⁻¹)^{k-1}`, and the right-hand side is `f` (via `ofComplex`).

TYPE-LEVEL NOTE: `D` carries the scalar `(2πi)⁻¹` per application, so `D^{k-1} = ((2πi)⁻¹)^{k-1} ·
d^{k-1}/dz^{k-1}`.  We fold the scalar into the statement via
`((2 * π * Complex.I)⁻¹) ^ (k-1).toNat * iteratedDeriv (k-1).toNat (eichlerIntegral f) z`.  The
`k ≥ 2` hypothesis makes `(k-1).toNat = k-1 ≥ 1` an honest positive iterate. -/
theorem bol_iterated_eichler (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hk : 2 ≤ k) {z : ℂ}
    (hz : 0 < z.im) :
    ((2 * (π : ℂ) * Complex.I)⁻¹) ^ (k - 1).toNat *
        iteratedDeriv (k - 1).toNat (eichlerIntegral f) z
      = f (UpperHalfPlane.ofComplex z) := by
  set n := (k - 1).toNat with hn
  have hn1 : 1 ≤ n := by omega
  -- Step 1: the iterated derivative is the `n`-shifted Eichler series.
  rw [eichlerIntegral, iteratedDeriv_eichlerQSeries f 0 n hz, zero_add, eichlerQSeries]
  -- Step 2: pull the scalar `((2πi)⁻¹)^n` inside the sum.
  rw [← tsum_mul_left]
  -- Step 3: identify the point with the upper-half-plane element `⟨z, hz⟩`.
  rw [show UpperHalfPlane.ofComplex z = (⟨z, hz⟩ : ℍ) from
    UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  -- Step 4: the q-expansion of `f` sums to `f ⟨z, hz⟩`.
  rw [← (hasSum_qExpansion_eichler f ⟨z, hz⟩).tsum_eq]
  -- Step 5: match the two series term by term.
  refine tsum_congr (fun m ↦ ?_)
  have hI : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rcases eq_or_ne m 0 with rfl | hm0
  · -- `m = 0`: both sides are `0` (the constant term of a cusp form vanishes; `(2πi·0)^n = 0`).
    have hcoeff0 : (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff 0 = 0 :=
      CuspFormClass.qExpansion_coeff_zero f one_pos one_mem_strictPeriods_Gamma1
    simp [eichlerCoeff, hcoeff0, zero_pow (by omega : n ≠ 0)]
  · -- `m ≠ 0`: cancel `m^n` and `(2πi)^n`.
    have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
    have hqp : Function.Periodic.qParam (1 : ℝ) (z : ℂ) ^ m =
        Complex.exp (2 * (π : ℂ) * Complex.I * m * z) := by
      rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
      push_cast
      ring_nf
    have ha : (2 * (π : ℂ) * Complex.I)⁻¹ ^ n * (2 * (π : ℂ) * Complex.I) ^ n = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hI, one_pow]
    have hb : (m : ℂ) ^ n / (m : ℂ) ^ n = 1 := div_self (pow_ne_zero n hmC)
    rw [hqp, smul_eq_mul, eichlerCoeff, ← hn, mul_pow]
    rw [show (2 * (π : ℂ) * Complex.I)⁻¹ ^ n *
          ((UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m / (m : ℂ) ^ n *
            ((2 * (π : ℂ) * Complex.I) ^ n * (m : ℂ) ^ n) *
            Complex.exp (2 * (π : ℂ) * Complex.I * m * z)) =
        ((2 * (π : ℂ) * Complex.I)⁻¹ ^ n * (2 * (π : ℂ) * Complex.I) ^ n) *
          ((m : ℂ) ^ n / (m : ℂ) ^ n) *
          ((UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m *
            Complex.exp (2 * (π : ℂ) * Complex.I * m * z)) from by ring]
    rw [ha, hb, one_mul, one_mul]

/-! ## `G3` — holomorphy / vanishing at every cusp -/

/-- The `ℤ → ℂ` cast `castSymPow m : Sym^m(ℤ) → Sym^m(ℂ)` has `ℂ`-spanning range: every complex
homogeneous polynomial is a `ℂ`-linear combination of (integer) monomials, each of which lies in the
image of `castSymPow`.  (Used to extend integer-coefficient period identities to complex `P`.) -/
private lemma span_range_castSymPow_eq_top (m : ℕ) :
    Submodule.span ℂ (Set.range (castSymPow m)) = ⊤ := by
  -- It suffices to compare images under the injective subtype map into `MvPolynomial`.
  apply Submodule.map_injective_of_injective (SymPow ℂ m).injective_subtype
  rw [Submodule.map_subtype_top, Submodule.map_span, ← Set.range_comp]
  -- The image of `range castSymPow` under the subtype is `{map cast Q.val | Q homogeneous}`.
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨Q, rfl⟩
    exact (Q.2).map (Int.castRingHom ℂ)
  · -- Conversely `SymPow ℂ m` is spanned by degree-`m` monomials, each in the image.
    have heq : SymPow ℂ m
        = Submodule.span ℂ ((fun d => (MvPolynomial.monomial d 1 : MvPolynomial (Fin 2) ℂ)) ''
          {d | Finsupp.degree d = m}) := by
      rw [show SymPow ℂ m = MvPolynomial.homogeneousSubmodule (Fin 2) ℂ m from rfl,
        MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
        AddMonoidAlgebra.supported_eq_span_single]
      simp only [MvPolynomial.single_eq_monomial]
    conv_lhs => rw [heq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨d, (hd : Finsupp.degree d = m), rfl⟩
    refine Submodule.subset_span ⟨⟨MvPolynomial.monomial d 1, ?_⟩, ?_⟩
    · rw [MvPolynomial.mem_homogeneousSubmodule]
      exact MvPolynomial.isHomogeneous_monomial _ hd
    · simp [castSymPow, MvPolynomial.map_monomial]

/-- **G3a — base-point independence.**  The Eichler integral based at any cusp `α` equals `E_f`,
because their difference is a period of `f`, which vanishes once `ι(f)=0` (reply.md §1.3).

TYPE-LEVEL NOTE (WEAKENED — see report): "the Eichler integral based at the cusp `c`",
`eichlerIntegralAt c`, is itself an API gap (no project def yet), so the literal statement
`E_{f,c} = E_f` cannot be written.  Pending that def, we state the *driver* of base-point
independence that `ι(f)=0` actually supplies and that is genuinely true: for any two cusps
`c₁, c₂`, the **difference** of their cusp values vanishes (`cuspValue f P c₁ = cuspValue f P c₂`).
This is exactly the `Div⁰` content of `ι(f)=0` (cf. `rawPairing_eq_zero_of_periodMap'_zero`, which
forces every `((c₁)-(c₂)) ⊗ P` period to `0`); the individual `cuspValue f P c` need NOT vanish,
only
their differences do, so this is the faithful (non-vacuous, true) shadow.  It is **weaker** than the
literal G3a equality of two Eichler integrals; closing G3a properly needs the `eichlerIntegralAt c`
def first.  (`P` is taken in `SymPow ℂ (k-2).toNat`, matching `cuspValue`.) -/
theorem eichler_basepoint_indep (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hk : 2 ≤ k)
    (hf : periodMap' N k hk f = 0) (P : SymPow ℂ (k - 2).toNat)
    (c₁ c₂ : Projectivization ℚ (Fin 2 → ℚ)) :
    cuspValue f P c₁ = cuspValue f P c₂ := by
  -- The integer case: for integer-coefficient `Q`, the cusp-difference period vanishes by
  -- `rawPairing_eq_zero_of_periodMap'_zero` applied to `(c₁) - (c₂) ∈ Div⁰`.
  have hint : ∀ Q : SymPow ℤ (k - 2).toNat,
      cuspValue f (castSymPow (k - 2).toNat Q) c₁ =
        cuspValue f (castSymPow (k - 2).toNat Q) c₂ := by
    intro Q
    have hz := rawPairing_eq_zero_of_periodMap'_zero hk f hf (divDiff c₁ c₂ ⊗ₜ[ℤ] Q)
    rw [rawPairing_tmul, divDiff_val, map_sub, LinearMap.sub_apply,
      rawBilin_single, rawBilin_single] at hz
    simp only [Int.cast_one, one_mul] at hz
    exact eq_of_sub_eq_zero hz
  -- `cuspValue f` of `0` vanishes (scaling by `0`), so it is consistent across cusps.
  have hzero : ∀ c : Projectivization ℚ (Fin 2 → ℚ),
      cuspValue f (0 : SymPow ℂ (k - 2).toNat) c = 0 := by
    intro c
    rw [show (0 : SymPow ℂ (k - 2).toNat) = (0 : ℂ) • 0 by simp, cuspValue_smul_right, zero_smul]
  -- Extend to complex `P` by `ℂ`-linearity: the difference functional is `ℂ`-linear in `P`
  -- and vanishes on the `ℂ`-spanning set `Set.range (castSymPow (k-2).toNat)`.
  have hspan : P ∈ Submodule.span ℂ (Set.range (castSymPow (k - 2).toNat)) := by
    rw [span_range_castSymPow_eq_top]; exact Submodule.mem_top
  refine Submodule.span_induction
    (p := fun P (_ : P ∈ Submodule.span ℂ (Set.range (castSymPow (k - 2).toNat))) =>
      cuspValue f P c₁ = cuspValue f P c₂)
    (fun x hx => ?_) ?_ (fun x y _ _ hx hy => ?_) (fun a x _ hx => ?_) hspan
  · obtain ⟨Q, rfl⟩ := hx; exact hint Q
  · rw [hzero, hzero]
  · rw [cuspValue_add_right, cuspValue_add_right, hx, hy]
  · rw [cuspValue_smul_right, cuspValue_smul_right, hx]

set_option linter.unusedVariables false in
/-- **G3b — only positive Fourier powers at every cusp.**  After slashing `E_f` by `σ` at weight
`2-k`, the expansion `C_k' Σ_{m≥1} b_m/(m/h)^{k-1} e^{2πimz/h}` has only positive `q`-powers, so
`E_f`
is holomorphic and vanishing at every cusp (reply.md §1.3, (8)).

TYPE-LEVEL NOTE: "holomorphic and bounded/zero at every cusp" is the mathlib `IsBoundedAtImInfty` /
`OnePoint.IsBoundedAt` predicate applied to `(eichlerIntegral f) ∘ ofComplex` slashed by the
cusp-width data.  We state the bounded-at-`i∞` shadow on the `ℍ → ℂ` bridge; the full per-cusp
statement is folded into the `bdd_at_cusps'` field of `eichlerModularForm`.  Stated here as the
`IsBoundedAtImInfty` of the bridged function (the cusp-`∞` case), which is what the packaging
consumes.

The `ℍ → ℂ` carrier is `(eichlerIntegral f) ∘ ((↑) : ℍ → ℂ)`, i.e. `fun z : ℍ => eichlerIntegral f
z`
(the project bridges `ℂ → ℂ` integrands to `ℍ → ℂ` by the `UpperHalfPlane.coe` coercion).

NOTE: boundedness at `i∞` is *automatic* from `a₀ = 0` (the Eichler `q`-series starts at `m ≥ 1`),
so `hf` is **not** used here; it is kept in the signature only for uniformity with the other
`G3`/`G4`
lemmas (`eichler_basepoint_indep`, `eichler_slash_invariant`) where it is genuinely needed. -/
theorem eichler_cusp_holo (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hk : 2 ≤ k)
    (hf : periodMap' N k hk f = 0) :
    UpperHalfPlane.IsBoundedAtImInfty
      ((eichlerIntegral f) ∘ ((↑) : ℍ → ℂ)) := by
  -- The geometric ratio `ρ = exp(-2π) < 1` controls every term for `Im z ≥ 1`.
  set ρ : ℝ := Real.exp (-(2 * π)) with hρdef
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := by
    rw [hρdef]; exact Real.exp_lt_one_iff.mpr (by have := Real.pi_pos; nlinarith)
  -- The bounding constant `M = Σ_m ‖a_m‖ ρ^m` (absolutely summable since the radius is `≥ 1`).
  have hsum : Summable (fun m : ℕ ↦
      ‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ * ρ ^ m) := by
    simpa using summable_norm_coeff_mul_pow_geom f 0 hρ0.le hρ1
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨∑' m : ℕ, ‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ * ρ ^ m, 1, fun z hz ↦ ?_⟩
  -- `‖coeff m‖ ≤ ...` bound on each Eichler coefficient (dividing by `m^n` only shrinks the norm).
  have hcoeff_bd : ∀ m : ℕ,
      ‖eichlerCoeff f m‖ ≤ ‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ := by
    intro m
    rw [eichlerCoeff, norm_div, norm_pow, Complex.norm_natCast]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rcases Nat.eq_zero_or_pos (k - 1).toNat with he | he
      · simp [he]
      · rw [Nat.cast_zero, zero_pow he.ne', div_zero]; exact norm_nonneg _
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg ((UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m),
        one_le_pow₀ (by exact_mod_cast hm : (1 : ℝ) ≤ (m : ℝ)) (n := (k - 1).toNat)]
  -- The norm of `exp(2πi m z)` is `exp(-2π m (z.im)) ≤ ρ^m` for `z.im ≥ 1`.
  have hnorm_exp : ∀ m : ℕ,
      ‖Complex.exp (2 * (π : ℂ) * Complex.I * m * (z : ℂ))‖ ≤ ρ ^ m := by
    intro m
    have h1 : Complex.exp (2 * (π : ℂ) * Complex.I * m * (z : ℂ))
        = Function.Periodic.qParam 1 (z : ℂ) ^ m := by
      rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]; push_cast; ring_nf
    rw [h1, norm_pow, Function.Periodic.norm_qParam, ← Real.exp_nat_mul, hρdef, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have hzim : (1 : ℝ) ≤ (z : ℂ).im := by simpa using hz
    have : (0 : ℝ) ≤ (m : ℝ) * (2 * π) * ((z : ℂ).im - 1) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith [this]
  -- `E_f z` is the `q`-series at `j = 0`; bound `‖tsum‖ ≤ tsum ‖·‖ ≤ M`.
  have hsumm_term : Summable (fun m : ℕ ↦
      eichlerCoeff f m * (2 * (π : ℂ) * Complex.I * m) ^ 0 *
        Complex.exp (2 * (π : ℂ) * Complex.I * m * (z : ℂ))) := by
    refine Summable.of_norm (hsum.of_nonneg_of_le (fun m ↦ norm_nonneg _) (fun m ↦ ?_))
    rw [pow_zero, mul_one, norm_mul]
    exact mul_le_mul (hcoeff_bd m) (hnorm_exp m) (norm_nonneg _) (norm_nonneg _)
  rw [Function.comp_apply, eichlerIntegral, eichlerQSeries]
  refine le_trans (norm_tsum_le_tsum_norm hsumm_term.norm) ?_
  refine Summable.tsum_le_tsum (fun m ↦ ?_) hsumm_term.norm hsum
  rw [pow_zero, mul_one, norm_mul]
  exact mul_le_mul (hcoeff_bd m) (hnorm_exp m) (norm_nonneg _) (norm_nonneg _)

/-- **G3b′ — vanishing of `E_f` at the cusp `∞`** (the strengthening of `eichler_cusp_holo` from
*bounded* to *zero* at `i∞`).  The Eichler `q`-series has no constant term (`a₀ = 0` for a cusp
form), so every term `a_m·q^m` (`m ≥ 1`) decays exponentially and `E_f → 0` as `Im → ∞`.  Like
`eichler_cusp_holo`, this is `hf`-free (it holds for any cusp form).  Concretely we bound
`‖E_f z‖ ≤ exp(-π·Im z) · (exp π · Σ ‖a_m‖ exp(-2π m))` for `Im z ≥ 1`, and the prefactor `→ 0`. -/
theorem eichler_isZeroAtImInfty (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    UpperHalfPlane.IsZeroAtImInfty
      ((eichlerIntegral f) ∘ ((↑) : ℍ → ℂ)) := by
  -- `M = Σ_m ‖a_m‖ exp(-2π m)`, absolutely summable (radius of convergence `≥ 1`).
  set ρ : ℝ := Real.exp (-(2 * π)) with hρdef
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := by
    rw [hρdef]; exact Real.exp_lt_one_iff.mpr (by have := Real.pi_pos; nlinarith)
  have hsum : Summable (fun m : ℕ ↦
      ‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ * ρ ^ m) := by
    simpa using summable_norm_coeff_mul_pow_geom f 0 hρ0.le hρ1
  set M : ℝ := ∑' m : ℕ, ‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ * ρ ^ m with hMdef
  have hM0 : 0 ≤ M := tsum_nonneg (fun m ↦ by positivity)
  -- `‖coeff m‖ ≤ ‖a_m‖` bound on each Eichler coefficient.
  have hcoeff_bd : ∀ m : ℕ,
      ‖eichlerCoeff f m‖ ≤ ‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ := by
    intro m
    rw [eichlerCoeff, norm_div, norm_pow, Complex.norm_natCast]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rcases Nat.eq_zero_or_pos (k - 1).toNat with he | he
      · simp [he]
      · rw [Nat.cast_zero, zero_pow he.ne', div_zero]; exact norm_nonneg _
    · rw [div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg ((UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m),
        one_le_pow₀ (by exact_mod_cast hm : (1 : ℝ) ≤ (m : ℝ)) (n := (k - 1).toNat)]
  -- Pointwise bound: `‖E_f z‖ ≤ exp(-π·Im z) · (exp π · M)` for `Im z ≥ 1`.
  have hpoint : ∀ z : ℍ, (1 : ℝ) ≤ (z : ℂ).im →
      ‖(eichlerIntegral f ∘ ((↑) : ℍ → ℂ)) z‖ ≤
        Real.exp (-(π * (z : ℂ).im)) * (Real.exp π * M) := by
    intro z hz
    -- Per-term: `‖a_m q^m‖ ≤ exp(-π Im z) · exp π · (‖a_m‖ ρ^m)` for `Im z ≥ 1`.
    have hterm : ∀ m : ℕ,
        ‖eichlerCoeff f m * (2 * (π : ℂ) * Complex.I * m) ^ 0 *
          Complex.exp (2 * (π : ℂ) * Complex.I * m * (z : ℂ))‖
        ≤ Real.exp (-(π * (z : ℂ).im)) *
            (Real.exp π *
              (‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ * ρ ^ m)) := by
      intro m
      have hnexp : ‖Complex.exp (2 * (π : ℂ) * Complex.I * m * (z : ℂ))‖
          = Real.exp (-(2 * π * m * (z : ℂ).im)) := by
        have h1 : Complex.exp (2 * (π : ℂ) * Complex.I * m * (z : ℂ))
            = Function.Periodic.qParam 1 (z : ℂ) ^ m := by
          rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]; push_cast; ring_nf
        rw [h1, norm_pow, Function.Periodic.norm_qParam, ← Real.exp_nat_mul]
        congr 1; ring
      rw [pow_zero, mul_one, norm_mul, hnexp, hρdef, ← Real.exp_nat_mul]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · -- `m = 0`: the term vanishes (`eichlerCoeff f 0 = 0`).
        have hc0 : eichlerCoeff f 0 = 0 := by
          have h0 : (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff 0 = 0 :=
            CuspFormClass.qExpansion_coeff_zero f one_pos one_mem_strictPeriods_Gamma1
          simp only [eichlerCoeff, h0, Nat.cast_zero, zero_div]
        rw [hc0, norm_zero, zero_mul]
        positivity
      · -- `m ≥ 1`: the exponent comparison `exp(-2π m Im) ≤ exp(-π Im)·exp π·exp(-2π m)` holds.
        have hexp_le : Real.exp (-(2 * π * m * (z : ℂ).im))
            ≤ Real.exp (-(π * (z : ℂ).im)) * (Real.exp π * Real.exp (m * -(2 * π))) := by
          rw [← Real.exp_add, ← Real.exp_add]
          refine Real.exp_le_exp.mpr ?_
          have hpi : 0 < π := Real.pi_pos
          have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (m : ℝ) - 1) hpi.le)
            (sub_nonneg.mpr hz)]
        calc ‖eichlerCoeff f m‖ * Real.exp (-(2 * π * m * (z : ℂ).im))
            ≤ ‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ *
                (Real.exp (-(π * (z : ℂ).im)) * (Real.exp π * Real.exp (m * -(2 * π)))) :=
              mul_le_mul (hcoeff_bd m) hexp_le (Real.exp_nonneg _) (norm_nonneg _)
          _ = Real.exp (-(π * (z : ℂ).im)) * (Real.exp π *
                (‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ *
                  Real.exp (m * -(2 * π)))) := by ring
    -- Sum the per-term bound.
    have hsumm_term : Summable (fun m : ℕ ↦
        eichlerCoeff f m * (2 * (π : ℂ) * Complex.I * m) ^ 0 *
          Complex.exp (2 * (π : ℂ) * Complex.I * m * (z : ℂ))) := by
      refine Summable.of_norm (Summable.of_nonneg_of_le (fun m ↦ norm_nonneg _) hterm ?_)
      exact ((hsum.mul_left (Real.exp π)).mul_left (Real.exp (-(π * (z : ℂ).im))))
    rw [Function.comp_apply, eichlerIntegral, eichlerQSeries]
    refine le_trans (norm_tsum_le_tsum_norm hsumm_term.norm) ?_
    refine le_trans (Summable.tsum_le_tsum hterm hsumm_term.norm
      ((hsum.mul_left (Real.exp π)).mul_left (Real.exp (-(π * (z : ℂ).im))))) ?_
    rw [tsum_mul_left, tsum_mul_left]
  -- Conclude `IsZeroAtImInfty` from the pointwise bound and `exp(-π·Im z) → 0`.
  rw [UpperHalfPlane.isZeroAtImInfty_iff]
  intro ε hε
  -- pick `A ≥ 1` so that `exp(-π A) · (exp π · M) ≤ ε`.
  have hpi : 0 < π := Real.pi_pos
  obtain ⟨A, hA1, hAbd⟩ : ∃ A : ℝ, (1 : ℝ) ≤ A ∧ Real.exp (-(π * A)) * (Real.exp π * M) ≤ ε := by
    rcases eq_or_lt_of_le hM0 with hM_eq | hM_pos
    · exact ⟨1, le_refl _, by rw [← hM_eq]; simp; positivity⟩
    · set D : ℝ := Real.exp π * M with hDdef
      have hD0 : 0 < D := by positivity
      -- want `exp(-π A) ≤ ε / D`, i.e. `-π A ≤ log(ε/D)`, i.e. `A ≥ -log(ε/D)/π`.
      set A : ℝ := max 1 (-(Real.log (ε / D)) / π) with hAdef
      have hge : -(Real.log (ε / D)) / π ≤ A := le_max_right _ _
      rw [div_le_iff₀ hpi] at hge
      have hlog : -(π * A) ≤ Real.log (ε / D) := by nlinarith [hge]
      refine ⟨A, le_max_left _ _, ?_⟩
      rw [← le_div_iff₀ hD0]
      calc Real.exp (-(π * A)) ≤ Real.exp (Real.log (ε / D)) := Real.exp_le_exp.mpr hlog
        _ = ε / D := Real.exp_log (by positivity)
  refine ⟨A, fun z hz ↦ ?_⟩
  have hz1 : (1 : ℝ) ≤ (z : ℂ).im := le_trans hA1 (by simpa using hz)
  refine le_trans (hpoint z hz1) (le_trans ?_ hAbd)
  gcongr
  simpa using hz

/-- A shifted polynomial times a decaying exponential is integrable on `(0,∞)`: `(a+s)^D·e^{-c s}`
(`a ≥ 0`, `c > 0`).  The dominator for the interior vertical-ray integrability of `periodForm`. -/
private lemma integrableOn_shifted_pow_mul_exp_neg {a c : ℝ} (_ha : 0 ≤ a) (hc : 0 < c) (D : ℕ) :
    IntegrableOn (fun s : ℝ => (a + s) ^ D * Real.exp (-c * s)) (Set.Ioi 0) := by
  -- Expand `(a+s)^D = Σ_i C(D,i) a^{D-i} s^i` and bound each `s^i e^{-c s}` term.
  have hterm : ∀ i : ℕ, IntegrableOn (fun s : ℝ => s ^ i * Real.exp (-c * s)) (Set.Ioi 0) := by
    intro i
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (i : ℝ)) (b := c)
      (neg_one_lt_zero.trans_le (Nat.cast_nonneg i)) one_pos hc
    refine h.congr_fun (fun s hs => ?_) measurableSet_Ioi
    rw [Set.mem_Ioi] at hs
    simp only [Real.rpow_natCast, Real.rpow_one]
  have hsum : IntegrableOn
      (fun s : ℝ => ∑ i ∈ Finset.range (D + 1),
        ((D.choose i : ℝ) * a ^ i) * (s ^ (D - i) * Real.exp (-c * s))) (Set.Ioi 0) :=
    integrable_finsetSum _ (fun i _ => ((hterm (D - i)).const_mul _))
  refine hsum.congr_fun (fun s hs => ?_) measurableSet_Ioi
  rw [add_pow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ### Generic interior vertical-ray integral machinery (for the conjugate cusp form `g = f∣γ`)

The finite-cusp boundedness `eichler_slashSL_bdd_finite` (EICH-3a-i) is closed by the decomposition
`(E_f∘↑)∣[2-k]γ = E_g + P`, where `E_g` is the `∞`-Eichler integral of the conjugate cusp form
`g := f∣[k]γ` (a `CuspForm` for the arithmetic conjugate group `γ⁻¹•Γ`) and `P` is a degree-`≤k-2`
period polynomial that vanishes under `ι(f)=0`.  Both pieces need the *generic* (arbitrary
arithmetic
cusp form) versions of the interior-ray integrability/FTC already proven for `Γ₁(N)` cusp forms; we
transcribe them here with the polymorphic `[CuspFormClass F Γ k] [Γ.IsArithmetic]` hypotheses (the
underlying bounds `periodForm_norm_le`, `differentiableOn_periodForm`, `Complex.isExactOn_upperHalf`
are all already polymorphic). -/

/-- **Interior vertical-ray integrability of the period form (generic arithmetic cusp form).**
Generic version of `integrableOn_periodForm_ray_interior`: for any arithmetic cusp form `f0` and a
base point `w₀` in the open upper half-plane, `t ↦ periodForm f0 Q (w₀ + i·t)·i` is integrable on
`[0,∞)`.  (No cusp singularity at the bottom; cusp decay beats polynomial growth at the top.) -/
private lemma integrableOn_periodFormGen_ray_interior {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} [CuspFormClass F Γ k] [Γ.IsArithmetic] (f0 : F) {m : ℕ}
    (Q : SymPow ℂ m) {w₀ : ℂ} (hw₀ : 0 < w₀.im) :
    IntegrableOn (fun t : ℝ => periodForm (⇑f0) Q (w₀ + Complex.I * t) * Complex.I)
      (Set.Ici 0) := by
  obtain ⟨c, hc, C, A, hbound⟩ := periodForm_norm_le f0 Q
  set D := (Q : MvPolynomial (Fin 2) ℂ).totalDegree with hD
  set g0 : ℝ → ℂ := fun t : ℝ => periodForm (⇑f0) Q (w₀ + Complex.I * t) * Complex.I with hg0
  have hcoe : ∀ t : ℝ, w₀ + Complex.I * t = ((w₀.re : ℂ)) + ((w₀.im + t : ℝ) : ℂ) * Complex.I := by
    intro t
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one, zero_mul, one_mul,
        sub_zero, add_zero, zero_add]
  have him : ∀ t : ℝ, 0 ≤ t → 0 < (w₀ + Complex.I * t).im := by
    intro t ht; rw [hcoe t]; simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_im, Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
    linarith
  set M : ℝ := max 1 A with hM
  have h0M : (0 : ℝ) ≤ M := le_trans zero_le_one (le_max_left _ _)
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hcont : ∀ {a : ℝ}, 0 ≤ a → ContinuousOn g0 (Set.Ici a) := by
    intro a ha
    apply ContinuousOn.mul _ continuousOn_const
    apply ContinuousOn.comp (g := periodForm (⇑f0) Q) (f := fun t : ℝ => w₀ + Complex.I * t)
      (s := Set.Ici a) (t := {z : ℂ | 0 < z.im})
    · exact (differentiableOn_periodForm f0 Q).continuousOn
    · fun_prop
    · intro t ht; simp only [Set.mem_Ici] at ht
      exact him t (le_trans ha ht)
  have hcompact : IntegrableOn g0 (Set.Icc 0 M) :=
    ((hcont le_rfl).mono Set.Icc_subset_Ici_self).integrableOn_compact isCompact_Icc
  have htail : IntegrableOn g0 (Set.Ici M) := by
    set g : ℝ → ℝ := fun t => |C| * (1 + (|w₀.re| + w₀.im) + t) ^ D *
      Real.exp (-c * (w₀.im + t)) with hg
    have hgint : IntegrableOn g (Set.Ici M) := by
      have h0 : IntegrableOn
          (fun t : ℝ => (1 + (|w₀.re| + w₀.im) + t) ^ D * Real.exp (-c * t)) (Set.Ici M) :=
        (integrableOn_shifted_pow_mul_exp_neg (a := 1 + (|w₀.re| + w₀.im)) (by positivity) hc D
          ).mono_set (fun t ht => lt_of_lt_of_le hMpos ht)
      have h1 : IntegrableOn (fun t : ℝ =>
          (|C| * Real.exp (-c * w₀.im)) * ((1 + (|w₀.re| + w₀.im) + t) ^ D * Real.exp (-c * t)))
          (Set.Ici M) := h0.const_mul _
      refine h1.congr_fun (fun t _ => ?_) measurableSet_Ici
      simp only [hg, show -c * (w₀.im + t) = -c * w₀.im + -c * t by ring, Real.exp_add]
      ring
    refine MeasureTheory.Integrable.mono' hgint
      ((hcont h0M).aestronglyMeasurable measurableSet_Ici) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
    rw [Set.mem_Ici] at ht
    have htpos : 0 ≤ t := le_trans h0M ht
    have hyA : A ≤ w₀.im + t := by
      have : A ≤ t := le_trans (le_max_right 1 A) ht
      linarith [hw₀]
    simp only [hg0, norm_mul, Complex.norm_I, mul_one]
    rw [hcoe t]
    refine (hbound w₀.re (w₀.im + t) hyA).trans ?_
    simp only [hg]
    rw [← hcoe t]
    have hqs : ‖w₀ + Complex.I * t‖ ≤ 1 + (|w₀.re| + w₀.im) + t := by
      rw [hcoe t, Complex.norm_add_mul_I]
      have hssq : Real.sqrt (w₀.re ^ 2 + (w₀.im + t) ^ 2) ≤ |w₀.re| + (w₀.im + t) := by
        rw [show (|w₀.re| + (w₀.im + t)) = Real.sqrt ((|w₀.re| + (w₀.im + t)) ^ 2) from
          (Real.sqrt_sq (by positivity)).symm]
        apply Real.sqrt_le_sqrt
        nlinarith [abs_nonneg w₀.re, sq_abs w₀.re, hw₀, htpos,
          mul_nonneg (abs_nonneg w₀.re) (by linarith : (0:ℝ) ≤ w₀.im + t)]
      have : |w₀.re| + (w₀.im + t) ≤ 1 + (|w₀.re| + w₀.im) + t := by ring_nf; linarith
      linarith
    gcongr
    · exact le_abs_self C
    · exact max_le (by nlinarith [abs_nonneg w₀.re, hw₀.le, htpos]) (by linarith)
  have hunion : Set.Ici (0 : ℝ) = Set.Icc 0 M ∪ Set.Ici M := by
    rw [Set.Icc_union_Ici_eq_Ici h0M]
  rw [hunion]
  exact hcompact.union htail

/-- **Interior vertical-ray FTC (generic arithmetic cusp form).**  Generic version of
`ray_integral_eq_top_sub`: for `Φ` a primitive of `periodForm f0 Q` on the open upper half-plane
with
real-part-independent top boundary value `L`, the improper integral up the vertical ray from the
interior point `w₀` to `i∞` equals `L − Φ(w₀)`. -/
private lemma rayGen_integral_eq_top_sub {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} [CuspFormClass F Γ k] [Γ.IsArithmetic] (f0 : F) {m : ℕ}
    (Q : SymPow ℂ m) (Φ : ℂ → ℂ)
    (hΦ : ∀ z : ℂ, 0 < z.im → HasDerivAt Φ (periodForm (⇑f0) Q z) z) (L : ℂ)
    (hL : ∀ q : ℝ, Tendsto (fun Y : ℝ => Φ ((q : ℂ) + Y * Complex.I)) atTop (𝓝 L))
    {w₀ : ℂ} (hw₀ : 0 < w₀.im) :
    (∫ t in Set.Ioi (0 : ℝ), periodForm (⇑f0) Q (w₀ + Complex.I * t) * Complex.I)
      = L - Φ w₀ := by
  set g : ℝ → ℂ := fun t => periodForm (⇑f0) Q (w₀ + Complex.I * t) * Complex.I with hg
  have hint : IntegrableOn g (Set.Ici 0) := integrableOn_periodFormGen_ray_interior f0 Q hw₀
  have hintIoi : IntegrableOn g (Set.Ioi 0) := hint.mono_set Set.Ioi_subset_Ici_self
  have hTrunc : Tendsto (fun Y₁ : ℝ => ∫ t in (0 : ℝ)..Y₁, g t) atTop
      (𝓝 (∫ t in Set.Ioi (0 : ℝ), g t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 hintIoi tendsto_id
  have hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun s : ℝ => Φ (w₀ + Complex.I * s)) (g t) t := by
    intro t ht
    have him : 0 < (w₀ + Complex.I * (t : ℂ)).im := by
      simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.ofReal_im, Complex.I_im,
        Complex.ofReal_re, zero_mul, zero_add]; linarith
    have h1 := hΦ _ him
    have hpath : HasDerivAt (fun s : ℝ => w₀ + Complex.I * (s : ℂ)) Complex.I t := by
      have := ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul Complex.I).const_add w₀
      simpa [mul_comm] using this
    have h2 := h1.scomp t hpath
    rw [hg]; rw [smul_eq_mul, mul_comm] at h2; exact h2
  have hFTC : ∀ Y₁ : ℝ, 0 < Y₁ →
      (∫ t in (0 : ℝ)..Y₁, g t) = Φ (w₀ + Complex.I * Y₁) - Φ w₀ := by
    intro Y₁ hY₁
    have hii : IntervalIntegrable g MeasureTheory.volume 0 Y₁ :=
      (hint.mono_set (fun t ht => by
        rw [Set.uIcc_of_le hY₁.le, Set.mem_Icc] at ht
        rw [Set.mem_Ici]; linarith [ht.1])).intervalIntegrable
    have hd : ∀ t ∈ Set.uIcc (0:ℝ) Y₁,
        HasDerivAt (fun s : ℝ => Φ (w₀ + Complex.I * s)) (g t) t := by
      intro t ht
      rw [Set.uIcc_of_le hY₁.le, Set.mem_Icc] at ht
      exact hderiv t ht.1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hii]
    norm_num
  have htop : Tendsto (fun Y₁ : ℝ => Φ (w₀ + Complex.I * Y₁)) atTop (𝓝 L) := by
    have hbase : Tendsto (fun Y : ℝ => Φ ((w₀.re : ℂ) + (Y : ℂ) * Complex.I)) atTop (𝓝 L) :=
      hL w₀.re
    have hcomp := hbase.comp (tendsto_atTop_add_const_left atTop w₀.im tendsto_id)
    refine hcomp.congr (fun Y₁ => ?_)
    simp only [Function.comp_apply, id_eq]
    congr 1
    conv_rhs => rw [← Complex.re_add_im w₀]
    push_cast
    ring
  have hlim : Tendsto (fun Y₁ : ℝ => ∫ t in (0 : ℝ)..Y₁, g t) atTop (𝓝 (L - Φ w₀)) := by
    have heq : (fun Y₁ : ℝ => ∫ t in (0 : ℝ)..Y₁, g t) =ᶠ[atTop]
        (fun Y₁ : ℝ => Φ (w₀ + Complex.I * Y₁) - Φ w₀) := by
      filter_upwards [eventually_gt_atTop 0] with Y₁ hY₁
      exact hFTC Y₁ hY₁
    rw [tendsto_congr' heq]
    exact htop.sub_const _
  exact tendsto_nhds_unique hTrunc hlim

/-! ## `G2`/`L7` — the modularity defect and weight-`(2-k)` invariance

The heart (reply.md §1.2).  We route the weight-`(2-k)` slash invariance of `E_f` through the
**integral representation** of `E_f` (`eichlerIntegral_eq_vertical`, sub-ticket EICH-2a) and the
**modularity-defect formula** packaged as a finite `ℂ`-linear combination of cusp-value
*differences*
(`eichler_slash_sub_eq_cuspValue_diff`, sub-ticket EICH-2b).  Once the defect is in that shape, the
main lemma `eichler_slash_invariant` is **fully proven** here: every cusp-value difference
vanishes by
`eichler_basepoint_indep` (EICH-3a, the `Div⁰`-content of `ι(f)=0`), so the whole defect is `0`,
hence `E_f|_{2-k}γ = E_f`.  The two analytic ingredients (the term-by-term Gamma-integral and the
Möbius change of variables) are isolated as the two sub-tickets and do **not** block the gluing. -/

/-- The Eichler normalising constant `C_k = (2π)^{k-1}/(I^{k-1}·Γ(k-1))` of reply.md §1.1 (4), so
that `E_f(z) = C_k ∫_z^{i∞} f(τ)(τ-z)^{k-2} dτ`.  It is the **reciprocal** of the per-term Gamma
factor: the vertical-ray integral of the `q`-series term `a_m·exp(2πi m·)·(i·)^{k-2}·i` is, after
the
substitution `u = τ-z` and the Euler Gamma integral `∫_0^∞ e^{-2πm t} t^{k-2} dt =
Γ(k-1)/(2πm)^{k-1}`
(mathlib `Complex.integral_cpow_mul_exp_neg_mul_Ioi`), equal to `(I^{k-1}·Γ(k-1)/(2π)^{k-1}) ·
eichlerCoeff f m · exp(2πi m z)` (the `m^{k-1}` denominators are exactly the `eichlerCoeff` weights,
the `m`-dependence cancelling); so `E_f(z) = C_k · ∫ …` requires `C_k` to invert that factor. -/
private def eichlerConst (k : ℤ) : ℂ :=
  (2 * (π : ℂ)) ^ (k - 1).toNat / (Complex.I ^ (k - 1).toNat * Complex.Gamma ((k : ℂ) - 1))

/-- The per-`m` term function of the vertical-ray integrand: `a_m·exp(2πi m(z+i t))·(i t)^{k-2}·i`,
with `a_m = (qExpansion 1 f).coeff m` the `m`-th Fourier coefficient of `f` at `∞` (so that the sum
`∑' m, eichlerTerm f z m t = f(z + i t)·(i t)^{k-2}·i` by `hasSum_qExpansion_eichler`).  The
`1/m^{k-1}`
weight of `eichlerCoeff` is produced *by the Gamma integral*, not carried in the coefficient. -/
private def eichlerTerm (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (z : ℂ) (m : ℕ) (t : ℝ) : ℂ :=
  (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m *
      Complex.exp (2 * (π : ℂ) * Complex.I * m * (z + Complex.I * t)) *
    (Complex.I * (t : ℂ)) ^ (k - 2).toNat * Complex.I

/-- The reciprocal of `eichlerConst`: the common Gamma factor `I^{k-1}·Γ(k-1)/(2π)^{k-1}` produced
by
each per-term vertical-ray integral.  Nonzero (`Γ(k-1) ≠ 0` for `k ≥ 2`, `I^{k-1} ≠ 0`). -/
private def eichlerGammaFactor (k : ℤ) : ℂ :=
  Complex.I ^ (k - 1).toNat * Complex.Gamma ((k : ℂ) - 1) / (2 * (π : ℂ)) ^ (k - 1).toNat

omit [NeZero N] in
/-- `eichlerConst` inverts the per-term Gamma factor: `eichlerConst k · eichlerGammaFactor k = 1`.
-/
private lemma eichlerConst_mul_gammaFactor (hk : 2 ≤ k) :
    eichlerConst k * eichlerGammaFactor k = 1 := by
  have hπ : (2 * (π : ℂ)) ^ (k - 1).toNat ≠ 0 := by
    refine pow_ne_zero _ ?_
    simp [Real.pi_ne_zero]
  have hI : Complex.I ^ (k - 1).toNat ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  have hΓ : Complex.Gamma ((k : ℂ) - 1) ≠ 0 := by
    refine Complex.Gamma_ne_zero (fun n hn => ?_)
    -- `(k:ℂ)-1` has real part `≥ 1`, so it is never a non-positive integer `-n`.
    have hre : ((k : ℂ) - 1).re = (k : ℝ) - 1 := by simp
    rw [hn] at hre
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have : (1 : ℝ) ≤ (k : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  rw [eichlerConst, eichlerGammaFactor]
  field_simp

omit [NeZero N] in
/-- **Per-term vertical-ray integral** (the Euler Gamma integral, the analytic core of EICH-2a).
For each `m`, integrating the `q`-series term up the vertical ray gives the `eichlerCoeff` weight
times the common Gamma factor and `exp(2πi m z)`:
`∫_0^∞ a_m·exp(2πi m(z+i t))·(i t)^{k-2}·i dt = eichlerGammaFactor k · eichlerCoeff f m · exp(2πi
m z)`.
For `m = 0` both sides are `0` (`eichlerCoeff f 0 = 0`); for `m ≥ 1` it is
`Complex.integral_cpow_mul_exp_neg_mul_Ioi` with `a = k-1`, `r = 2π m`. -/
private lemma integral_eichlerTerm (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hk : 2 ≤ k)
    (z : ℂ) (m : ℕ) :
    ∫ t in Set.Ioi (0 : ℝ), eichlerTerm f z m t
      = eichlerGammaFactor k * eichlerCoeff f m *
          Complex.exp (2 * (π : ℂ) * Complex.I * m * z) := by
  set n₂ : ℕ := (k - 2).toNat with hn₂
  have hn12 : (k - 1).toNat = n₂ + 1 := by omega
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- `m = 0`: the constant Fourier coefficient `a₀ = 0` (cusp form), so both sides vanish.
    have h0 : (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff 0 = 0 :=
      CuspFormClass.qExpansion_coeff_zero f one_pos one_mem_strictPeriods_Gamma1
    have hc0 : eichlerCoeff f 0 = 0 := by
      simp only [eichlerCoeff, h0, Nat.cast_zero, zero_div]
    simp only [eichlerTerm, h0, zero_mul, MeasureTheory.integral_zero, hc0, mul_zero]
  · -- `m ≥ 1`: factor `a_m·exp(2πi m z)·i^{k-1}` out, leaving the Euler Gamma integral.
    have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    set r : ℝ := 2 * π * m with hr
    have hr0 : 0 < r := by rw [hr]; have := Real.pi_pos; positivity
    set a : ℂ := (k : ℂ) - 1 with ha
    have hare : 0 < a.re := by
      rw [ha]; simp only [Complex.sub_re, Complex.intCast_re, Complex.one_re]
      have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    -- The constant pulled out front.
    set C : ℂ := (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m *
      Complex.exp (2 * (π : ℂ) * Complex.I * m * z) * Complex.I ^ (n₂ + 1) with hC
    -- Pointwise: rewrite `eichlerTerm f z m t` into the Gamma-integrand shape `C·(t^(a-1)·e^{-r
    -- t})`.
    have hpoint : ∀ t ∈ Set.Ioi (0 : ℝ),
        eichlerTerm f z m t = C * ((t : ℂ) ^ (a - 1) * Complex.exp (-(r * t))) := by
      intro t ht
      have htpos : (0 : ℝ) < t := ht
      have hn2C : ((n₂ : ℕ) : ℂ) = (k : ℂ) - 2 := by
        rw [hn₂, ← Int.cast_natCast, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ k - 2)]
        push_cast; ring
      have hcpow : (t : ℂ) ^ (a - 1) = (t : ℂ) ^ n₂ := by
        rw [show a - 1 = ((n₂ : ℕ) : ℂ) by rw [hn2C, ha]; ring, Complex.cpow_natCast]
      have hexp_split : Complex.exp (2 * (π : ℂ) * Complex.I * m * (z + Complex.I * t))
          = Complex.exp (2 * (π : ℂ) * Complex.I * m * z) * Complex.exp (-(r * t)) := by
        rw [← Complex.exp_add]
        congr 1
        rw [hr]
        push_cast
        ring_nf
        rw [Complex.I_sq]
        ring
      rw [eichlerTerm, hexp_split, hcpow, mul_pow, hC]
      ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpoint]
    rw [MeasureTheory.integral_const_mul,
      Complex.integral_cpow_mul_exp_neg_mul_Ioi hare hr0]
    -- Match `C·((1/r)^a·Γ a)` with `eichlerGammaFactor k · eichlerCoeff f m · exp(2πi m z)`.
    have haC : a = ((n₂ + 1 : ℕ) : ℂ) := by
      rw [ha, hn₂]
      rw [show ((((k - 2).toNat + 1 : ℕ)) : ℂ) = (((k - 1).toNat : ℕ) : ℂ) by rw [hn12, hn₂]]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ k - 1)]
      push_cast; ring
    have hone_div : ((1 : ℂ) / (r : ℂ)) ^ a = (1 / (r : ℂ)) ^ (n₂ + 1) := by
      rw [haC, Complex.cpow_natCast]
    have hrC : (r : ℂ) = 2 * (π : ℂ) * (m : ℂ) := by rw [hr]; push_cast; ring
    rw [hC, ha, eichlerGammaFactor, eichlerCoeff, hn12, hone_div, hrC]
    rw [div_pow, one_pow, mul_pow]
    field_simp

omit [NeZero N] in
/-- The norm of the `m`-th term on `Ioi 0`: `‖a_m‖·e^{-2πm·Im z}·(t^{k-2}·e^{-2πm t})`.  Factors the
`t`-independent geometric weight `e^{-2πm·Im z}` from the `t`-dependent Gamma integrand. -/
private lemma norm_eichlerTerm (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (z : ℂ) (m : ℕ)
    {t : ℝ} (ht : 0 < t) :
    ‖eichlerTerm f z m t‖
      = ‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ * Real.exp (-(2 * π * m * z.im)) *
          ((t : ℝ) ^ (k - 2).toNat * Real.exp (-(2 * π * m * t))) := by
  rw [eichlerTerm, norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_I, mul_one,
    norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ht]
  have hre : (2 * (π : ℂ) * Complex.I * m * (z + Complex.I * t)).re
      = -(2 * π * m * (z.im + t)) := by
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im]
  rw [hre]
  rw [show -(2 * π * (m : ℝ) * (z.im + t)) = -(2 * π * m * z.im) + -(2 * π * m * t) by ring,
    Real.exp_add]
  ring

omit [NeZero N] in
/-- Each `m`-th term is integrable on `Ioi 0` (the Gamma integrand `t^{k-2}·e^{-2πm t}` is). -/
private lemma integrableOn_eichlerTerm (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (z : ℂ) (m : ℕ) :
    IntegrableOn (eichlerTerm f z m) (Set.Ioi (0 : ℝ)) := by
  set n₂ : ℕ := (k - 2).toNat with hn₂
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- `m = 0`: term is identically `0`.
    have h0 : (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff 0 = 0 :=
      CuspFormClass.qExpansion_coeff_zero f one_pos one_mem_strictPeriods_Gamma1
    have hfun : eichlerTerm f z 0 = 0 := by
      funext t; simp only [eichlerTerm, h0, zero_mul, Nat.cast_zero, Pi.zero_apply]
    rw [hfun]
    exact MeasureTheory.integrableOn_zero
  · -- `m ≥ 1`: bound the norm by the integrable real Gamma integrand and use measurability.
    have hr0 : (0 : ℝ) < 2 * π * m := by have := Real.pi_pos; positivity
    -- Measurability: `eichlerTerm` is continuous in `t`.
    have hmeas : AEStronglyMeasurable (eichlerTerm f z m) (volume.restrict (Set.Ioi (0 : ℝ))) := by
      apply Continuous.aestronglyMeasurable
      unfold eichlerTerm
      fun_prop
    -- Domination by `C · (t^{n₂} · exp(-(2πm) t))`, integrable on `Ioi 0`.
    have hn2nonneg : (-1 : ℝ) < (n₂ : ℝ) := by
      have : (0 : ℝ) ≤ (n₂ : ℝ) := Nat.cast_nonneg n₂
      linarith
    have hint : IntegrableOn
        (fun t : ℝ ↦ (t : ℝ) ^ (n₂ : ℝ) * Real.exp (-(2 * π * m) * t ^ (1 : ℝ))) (Set.Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow hn2nonneg one_pos hr0
    refine MeasureTheory.Integrable.mono'
      (g := fun t : ℝ ↦ ‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ *
        Real.exp (-(2 * π * m * z.im)) *
          ((t : ℝ) ^ (n₂ : ℝ) * Real.exp (-(2 * π * m) * t ^ (1 : ℝ))))
      ((hint.const_mul _)) hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_eichlerTerm f z m ht, ← hn₂]
    have htpos : (0 : ℝ) < t := ht
    rw [Real.rpow_natCast, Real.rpow_one, show -(2 * π * (m : ℝ)) * t = -(2 * π * m * t) by ring]

omit [NeZero N] in
/-- The integral of the `m`-th norm factors as `‖a_m‖·e^{-2πm·Im z}·∫ t^{k-2} e^{-2πm t} dt`. -/
private lemma integral_norm_eichlerTerm (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (z : ℂ)
    (m : ℕ) :
    ∫ t in Set.Ioi (0 : ℝ), ‖eichlerTerm f z m t‖
      = ‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ * Real.exp (-(2 * π * m * z.im)) *
          ∫ t in Set.Ioi (0 : ℝ), (t : ℝ) ^ (k - 2).toNat * Real.exp (-(2 * π * m * t)) := by
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [norm_eichlerTerm f z m ht]

/-- **Summability of the per-term integral-norms** (the dominated-convergence hypothesis of the
`∑'/∫` interchange).  Bounds `∫ ‖term_m‖ ≤ ‖a_m‖·ρ^m·K` with `ρ = e^{-2π·Im z} < 1` and `K` the
`m = 1` Gamma integral, then sums by the radius-of-convergence bound
`summable_norm_coeff_mul_geom`. -/
private lemma summable_integral_norm_eichlerTerm (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {z : ℂ} (hz : 0 < z.im) :
    Summable (fun m : ℕ ↦ ∫ t in Set.Ioi (0 : ℝ), ‖eichlerTerm f z m t‖) := by
  set n₂ : ℕ := (k - 2).toNat with hn₂
  -- The reference Gamma integral `K = ∫ t^{n₂} e^{-2π t} dt ≥ 0`.
  set K : ℝ := ∫ t in Set.Ioi (0 : ℝ), (t : ℝ) ^ n₂ * Real.exp (-(2 * π * t)) with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun t ht => ?_)
    have : (0 : ℝ) < t := ht
    positivity
  -- The geometric ratio `ρ = e^{-2π·Im z} ∈ (0,1)`.
  set ρ : ℝ := Real.exp (-(2 * π * z.im)) with hρdef
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := by
    rw [hρdef]; exact Real.exp_lt_one_iff.mpr (by have := Real.pi_pos; nlinarith)
  -- Reference integrability of `t^{n₂} e^{-2π·c·t}` for any `c ≥ 1`.
  have hint : ∀ c : ℝ, 0 < c →
      IntegrableOn (fun t : ℝ ↦ (t : ℝ) ^ n₂ * Real.exp (-(2 * π * c * t))) (Set.Ioi 0) := by
    intro c hc
    have hr0 : (0 : ℝ) < 2 * π * c := by have := Real.pi_pos; positivity
    have hn2nonneg : (-1 : ℝ) < (n₂ : ℝ) := by
      have : (0 : ℝ) ≤ (n₂ : ℝ) := Nat.cast_nonneg n₂; linarith
    have := integrableOn_rpow_mul_exp_neg_mul_rpow hn2nonneg one_pos hr0
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have htpos : (0 : ℝ) < t := ht
    simp only [Real.rpow_natCast, Real.rpow_one]
    rw [show -(2 * π * c) * t = -(2 * π * c * t) by ring]
  -- The summable dominating sequence `B m = ‖a_m‖ · ρ^m · K`.
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
    (((summable_norm_coeff_mul_geom f (r := ρ.toNNReal)
      (by rwa [Real.coe_toNNReal ρ hρ0.le])).mul_right K))
  · -- nonnegativity of `∫ ‖term_m‖`
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun t ht => norm_nonneg _)
  · -- the bound `∫ ‖term_m‖ ≤ ‖a_m‖ · ρ^m · K`
    rw [integral_norm_eichlerTerm f z m, ← hn₂, Real.coe_toNNReal ρ hρ0.le]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · -- `m = 0`: LHS has `‖a₀‖ = 0`.
      have h0 : (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff 0 = 0 :=
        CuspFormClass.qExpansion_coeff_zero f one_pos one_mem_strictPeriods_Gamma1
      simp [h0]
    · -- `m ≥ 1`: `e^{-2πm·Im z} = ρ^m` and `∫ t^{n₂} e^{-2πm t} ≤ K`.
      have hexpρ : Real.exp (-(2 * π * (m : ℝ) * z.im)) = ρ ^ m := by
        rw [hρdef, ← Real.exp_nat_mul]; congr 1; ring
      have hmono : (∫ t in Set.Ioi (0 : ℝ), (t : ℝ) ^ n₂ * Real.exp (-(2 * π * m * t))) ≤ K := by
        rw [hKdef]
        refine MeasureTheory.setIntegral_mono_on (hint m (by exact_mod_cast hm))
          (hint 1 one_pos |>.congr_fun (fun t _ => by rw [mul_one]) measurableSet_Ioi)
          measurableSet_Ioi (fun t ht => ?_)
        have htpos : (0 : ℝ) < t := ht
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Real.exp_le_exp]
        have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        nlinarith [Real.pi_pos, htpos,
          mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * π) htpos.le)
          (by linarith : (0:ℝ) ≤ (m : ℝ) - 1)]
      rw [hexpρ]
      exact mul_le_mul_of_nonneg_left hmono
        (mul_nonneg (norm_nonneg _) (pow_nonneg hρ0.le m))

omit [NeZero N] in
/-- **Pointwise term sum.**  On the open upper half-plane the vertical-ray integrand is the sum of
the per-`m` terms: `∑' m, eichlerTerm f z m t = f(z + i t)·(i t)^{k-2}·i` (the `q`-expansion of `f`
at `z + i t`, by `hasSum_qExpansion_eichler`, times the `m`-independent factor `(i t)^{k-2}·i`). -/
private lemma hasSum_eichlerTerm (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {z : ℂ}
    (hz : 0 < z.im) {t : ℝ} (ht : 0 < t) :
    HasSum (fun m : ℕ ↦ eichlerTerm f z m t)
      (f (UpperHalfPlane.ofComplex (z + Complex.I * t)) *
        (Complex.I * (t : ℂ)) ^ (k - 2).toNat * Complex.I) := by
  have him : 0 < (z + Complex.I * (t : ℂ)).im := by
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    simpa using add_pos hz ht
  -- `f` at `z + i t` is the sum of its `q`-expansion.
  have hf : HasSum (fun m : ℕ ↦ (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m *
      Complex.exp (2 * (π : ℂ) * Complex.I * m * (z + Complex.I * t)))
      (f (UpperHalfPlane.ofComplex (z + Complex.I * t))) := by
    have hofc : UpperHalfPlane.ofComplex (z + Complex.I * (t : ℂ)) = (⟨_, him⟩ : ℍ) :=
      UpperHalfPlane.ofComplex_apply_of_im_pos him
    rw [hofc]
    have hqp : ∀ m : ℕ, (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m *
          Complex.exp (2 * (π : ℂ) * Complex.I * m * (z + Complex.I * t))
        = (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m •
          Function.Periodic.qParam (1 : ℝ) ((⟨_, him⟩ : ℍ) : ℂ) ^ m := by
      intro m
      rw [smul_eq_mul]
      congr 1
      rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
      push_cast
      ring_nf
    exact (hasSum_qExpansion_eichler f ⟨_, him⟩).congr_fun hqp
  -- Multiply by the `m`-independent factor `(i t)^{k-2}·i`.
  have hfac := hf.mul_right ((Complex.I * (t : ℂ)) ^ (k - 2).toNat * Complex.I)
  rw [mul_assoc]
  refine hfac.congr_fun (fun m => ?_)
  rw [eichlerTerm]; ring

/-- **G2a / EICH-2a — the integral representation of `E_f`** (reply.md §1.1 (4)).  On the open upper
half-plane the Eichler `q`-series equals the contour integral up the vertical ray from `z` to `i∞`:
`E_f(z) = C_k ∫_0^∞ f(z + i t)·(i t)^{k-2}·i dt` (the parametrisation `τ = z + i t`, `dτ = i dt`),
where `C_k = eichlerConst k = (2π)^{k-1}/(I^{k-1}·Γ(k-1))`.

Proof: integrate the absolutely convergent `q`-series term by term.  The pointwise sum
`∑' m, eichlerTerm f z m t = f(z+i t)·(i t)^{k-2}·i` (`hasSum_eichlerTerm`); the `∑'/∫` interchange
is `MeasureTheory.integral_tsum_of_summable_integral_norm` with the integrability
(`integrableOn_eichlerTerm`) and summable integral-norms (`summable_integral_norm_eichlerTerm`);
each
term integrates to `eichlerGammaFactor k · eichlerCoeff f m · exp(2πi m z)` via the Euler Gamma
integral `Complex.integral_cpow_mul_exp_neg_mul_Ioi` (`integral_eichlerTerm`); and
`eichlerConst k · eichlerGammaFactor k = 1` (`eichlerConst_mul_gammaFactor`) leaves
`E_f(z) = ∑' m, eichlerCoeff f m · exp(2πi m z) = eichlerQSeries f 0 z`. -/
private theorem eichlerIntegral_eq_vertical (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hk : 2 ≤ k)
    {z : ℂ} (hz : 0 < z.im) :
    eichlerIntegral f z =
      eichlerConst k *
        ∫ t in Set.Ioi (0 : ℝ),
          f (UpperHalfPlane.ofComplex (z + Complex.I * t)) *
            (Complex.I * (t : ℂ)) ^ (k - 2).toNat * Complex.I := by
  -- Rewrite the integrand as the pointwise `∑'` of the per-term functions.
  have hpt : (∫ t in Set.Ioi (0 : ℝ),
        f (UpperHalfPlane.ofComplex (z + Complex.I * t)) *
          (Complex.I * (t : ℂ)) ^ (k - 2).toNat * Complex.I)
      = ∫ t in Set.Ioi (0 : ℝ), ∑' m : ℕ, eichlerTerm f z m t := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    exact (hasSum_eichlerTerm f hz ht).tsum_eq.symm
  rw [hpt]
  -- Interchange `∑'` and `∫`.
  rw [← MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun m => integrableOn_eichlerTerm f z m) (summable_integral_norm_eichlerTerm f hz)]
  -- Evaluate each term integral via the Gamma integral.
  rw [tsum_congr (fun m => integral_eichlerTerm f hk z m)]
  -- Pull the common Gamma factor out of the sum.
  rw [show (fun m : ℕ ↦ eichlerGammaFactor k * eichlerCoeff f m *
        Complex.exp (2 * (π : ℂ) * Complex.I * m * z))
      = (fun m : ℕ ↦ eichlerGammaFactor k *
          (eichlerCoeff f m * Complex.exp (2 * (π : ℂ) * Complex.I * m * z))) by
    funext m; ring]
  rw [tsum_mul_left, ← mul_assoc, mul_comm (eichlerConst k) (eichlerGammaFactor k)]
  -- `eichlerGammaFactor · eichlerConst = 1` ⟹ the prefactor is `1`.
  rw [show eichlerGammaFactor k * eichlerConst k = 1 by
    rw [mul_comm]; exact eichlerConst_mul_gammaFactor hk, one_mul]
  -- The remaining sum is `eichlerIntegral f z` (the `q`-series with `(2πi m)^0 = 1`).
  rw [eichlerIntegral, eichlerQSeries]
  refine tsum_congr (fun m => ?_)
  rw [pow_zero, mul_one]

/-- The **Eichler moving polynomial** `(X₀ - τ·X₁)^n ∈ Sym^n(ℂ²)` (`n = (k-2).toNat`), written in
the
monomial basis `Σ_{j≤n} C(n,j)·(-τ)^{n-j}·symMon n j`, so that `evalSym1 (eichlerMovingPoly τ) z =
(z - τ)^n` (`evalSym1_eichlerMovingPoly`).  This is the *fixed* `Sym^n` element (with `τ`-dependent
coefficients) whose period form is the moving-basepoint Eichler kernel `f(z)·(z-τ)^{k-2}`; making
it a
genuine `Sym^n` element lets the whole polynomial-agnostic period-form/primitive engine
(`periodForm`, `cuspValue_eq_top_sub_botVal`, `tendsto_F_pole`, …) apply to it directly. -/
private def eichlerMovingPoly (n : ℕ) (τ : ℍ) : SymPow ℂ n :=
  ∑ j ∈ Finset.range (n + 1),
    (((n.choose j : ℂ) * (-(τ : ℂ)) ^ (n - j))) • symMon n j

/-- `evalSym1 (eichlerMovingPoly n τ) z = (z - τ)^n`: the moving polynomial evaluates to the Eichler
kernel.  This is the binomial theorem `(z + (-τ))^n = Σ_{j≤n} C(n,j)·z^j·(-τ)^{n-j}` repackaged
through `evalSym1`-linearity and `evalSym1_symMon`. -/
private lemma evalSym1_eichlerMovingPoly (n : ℕ) (τ : ℍ) (z : ℂ) :
    evalSym1 n (eichlerMovingPoly n τ) z = (z - (τ : ℂ)) ^ n := by
  rw [eichlerMovingPoly, evalSym1, Submodule.coe_sum, map_sum]
  rw [show (z - (τ : ℂ)) = z + (-(τ : ℂ)) by ring, add_pow]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hj
  rw [SetLike.val_smul, MvPolynomial.smul_eval, ← evalSym1, evalSym1_symMon n j hj]
  ring

/-- The **homogeneous** evaluation of the moving polynomial: `eval ![u, v] (eichlerMovingPoly n τ) =
(u - τ·v)^n`.  (The degree-`n` homogenisation of `evalSym1_eichlerMovingPoly`; used for the Möbius
change of variables, where the evaluation point `(u,v)` is the linear image of `(σ,1)` under
`symMat`.) -/
private lemma eval_eichlerMovingPoly_hom (n : ℕ) (τ : ℍ) (u v : ℂ) :
    MvPolynomial.eval ![u, v] (eichlerMovingPoly n τ : MvPolynomial (Fin 2) ℂ)
      = (u - (τ : ℂ) * v) ^ n := by
  rw [eichlerMovingPoly, Submodule.coe_sum, map_sum]
  rw [show (u - (τ : ℂ) * v) = u + (-(τ : ℂ)) * v by ring, add_pow]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hj
  rw [SetLike.val_smul, MvPolynomial.smul_eval]
  -- `eval ![u,v] (symMon n j) = u^j · v^{n-j}` for `j ≤ n`.
  have hmon : MvPolynomial.eval ![u, v] (symMon n j : MvPolynomial (Fin 2) ℂ)
      = u ^ j * v ^ (n - j) := by
    show MvPolynomial.eval ![u, v]
      (MvPolynomial.monomial
        (Finsupp.single (0 : Fin 2) (min j n) + Finsupp.single (1 : Fin 2) (n - j)) (1 : ℂ))
      = u ^ j * v ^ (n - j)
    rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod_fintype]
    · rw [Fin.prod_univ_two]
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
        Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)]
      rw [Nat.min_eq_left hj]
      simp
    · intro i; simp
  rw [hmon]
  ring

/-- **Möbius covariance of the moving polynomial.**  `evalSym1 (symRep γ (eichlerMovingPoly n τ)) σ
= (cτ+d)^n · (σ − γ·τ)^n`, where `(c,d) = (γ₁₀, γ₁₁)` and `γ·τ = mob γ τ`.  This is the moving-poly
analogue of `evalSym1_symRep_smul`, but as an identity in the free variable `σ` (via the polynomial
substitution `evalSym1_substAlgHom` + the homogeneous evaluation `eval_eichlerMovingPoly_hom`),
which
is exactly what the under-the-integral change of variables on the `γτ`-ray needs. -/
private lemma evalSym1_symRep_eichlerMovingPoly (n : ℕ) (γ : SL(2, ℤ)) (τ : ℍ) (σ : ℂ) :
    evalSym1 n (symRep ℂ n γ (eichlerMovingPoly n τ)) σ
      = (((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) ^ n) * (σ - mob γ (τ : ℂ)) ^ n := by
  -- Unfold `symRep = substAlgHom (symMat γ)` and evaluate via the substitution lemma.
  have hrep : symRep ℂ n γ (eichlerMovingPoly n τ)
      = ⟨substAlgHom (symMat ℂ γ) ((eichlerMovingPoly n τ : SymPow ℂ n) : MvPolynomial (Fin 2) ℂ),
          substAlgHom_isHomogeneous (symMat ℂ γ) (eichlerMovingPoly n τ).2⟩ := by
    apply Subtype.ext; rw [symRep_apply]
  rw [hrep, evalSym1_substAlgHom, eval_eichlerMovingPoly_hom]
  -- The `symMat γ = (γ⁻¹).map` entries: `(γ⁻¹)₀₀=γ₁₁, (γ⁻¹)₀₁=-γ₀₁, (γ⁻¹)₁₀=-γ₁₀, (γ⁻¹)₁₁=γ₀₀`.
  have hM00 : (symMat ℂ γ) 0 0 = (γ 1 1 : ℂ) := by
    simp [symMat, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.map_apply]
  have hM01 : (symMat ℂ γ) 0 1 = -(γ 0 1 : ℂ) := by
    rw [symMat, Matrix.map_apply, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp
  have hM10 : (symMat ℂ γ) 1 0 = -(γ 1 0 : ℂ) := by
    rw [symMat, Matrix.map_apply, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp
  have hM11 : (symMat ℂ γ) 1 1 = (γ 0 0 : ℂ) := by
    rw [symMat, Matrix.map_apply, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp
  rw [hM00, hM01, hM10, hM11]
  -- `((γ₁₁σ - γ₀₁) - τ·(γ₀₀ - γ₁₀σ))^n = ((cτ+d)·(σ - γτ))^n`.
  rw [← mul_pow]
  congr 1
  rw [mob]
  have hden : ((γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ)) ≠ 0 := denom_mob_ne γ (τ).im_pos
  rw [mul_sub, mul_div_cancel₀ _ hden]
  ring
private lemma cuspValue_eichlerMovingPoly (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ)
    (τ : ℍ) (c : Projectivization ℚ (Fin 2 → ℚ)) :
    cuspValue f (eichlerMovingPoly n τ) c =
      ∑ j ∈ Finset.range (n + 1),
        ((n.choose j : ℂ) * (-(τ : ℂ)) ^ (n - j)) *
          cuspValue f (symMon n j) c := by
  rw [eichlerMovingPoly]
  refine Finset.cons_induction ?_ ?_ (Finset.range (n + 1))
  · simp only [Finset.sum_empty]
    rw [show (0 : SymPow ℂ n) = (0 : ℂ) • 0 by simp, cuspValue_smul_right, zero_smul]
  · intro j s hjs ih
    rw [Finset.sum_cons, Finset.sum_cons, cuspValue_add_right,
      cuspValue_smul_right, ih, smul_eq_mul]

/-- **Interior vertical-ray integrability of the period form (`ℂ`-base form).**  For an arithmetic
cusp form `f` and a base point `w₀` in the open upper half-plane, the integrand
`t ↦ periodForm f Q (w₀ + i·t)·i` is integrable on `[0,∞)` (no cusp singularity at the bottom — the
ray stays at height `≥ w₀.im > 0`; cusp decay `e^{-c·t}` beats polynomial growth at the top). -/
private lemma integrableOn_periodForm_ray_interior
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ} (Q : SymPow ℂ m) {w₀ : ℂ}
    (hw₀ : 0 < w₀.im) :
    IntegrableOn (fun t : ℝ => periodForm (⇑f) Q (w₀ + Complex.I * t) * Complex.I)
      (Set.Ici 0) := by
  obtain ⟨c, hc, C, A, hbound⟩ := periodForm_norm_le f Q
  set D := (Q : MvPolynomial (Fin 2) ℂ).totalDegree with hD
  set g0 : ℝ → ℂ := fun t : ℝ => periodForm (⇑f) Q (w₀ + Complex.I * t) * Complex.I with hg0
  -- `w₀ + i·t = w₀.re + (w₀.im + t)·i`.
  have hcoe : ∀ t : ℝ, w₀ + Complex.I * t = ((w₀.re : ℂ)) + ((w₀.im + t : ℝ) : ℂ) * Complex.I := by
    intro t
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one, zero_mul, one_mul,
        sub_zero, add_zero, zero_add]
  have him : ∀ t : ℝ, 0 ≤ t → 0 < (w₀ + Complex.I * t).im := by
    intro t ht; rw [hcoe t]; simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_im, Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
    linarith
  set M : ℝ := max 1 A with hM
  have h0M : (0 : ℝ) ≤ M := le_trans zero_le_one (le_max_left _ _)
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  -- Continuity of `g0` on any `Ici a` with `a ≥ 0`.
  have hcont : ∀ {a : ℝ}, 0 ≤ a → ContinuousOn g0 (Set.Ici a) := by
    intro a ha
    apply ContinuousOn.mul _ continuousOn_const
    apply ContinuousOn.comp (g := periodForm (⇑f) Q) (f := fun t : ℝ => w₀ + Complex.I * t)
      (s := Set.Ici a) (t := {z : ℂ | 0 < z.im})
    · exact (differentiableOn_periodForm f Q).continuousOn
    · fun_prop
    · intro t ht; simp only [Set.mem_Ici] at ht
      exact him t (le_trans ha ht)
  -- Piece 1: integrable on the compact `[0, M]` by continuity.
  have hcompact : IntegrableOn g0 (Set.Icc 0 M) :=
    ((hcont le_rfl).mono Set.Icc_subset_Ici_self).integrableOn_compact isCompact_Icc
  -- Piece 2: integrable on `[M, ∞)` by domination (where `periodForm_norm_le` applies, `w₀.im+t ≥
  -- A`).
  have htail : IntegrableOn g0 (Set.Ici M) := by
    set g : ℝ → ℝ := fun t => |C| * (1 + (|w₀.re| + w₀.im) + t) ^ D *
      Real.exp (-c * (w₀.im + t)) with hg
    have hgint : IntegrableOn g (Set.Ici M) := by
      -- `(a+t)^D · e^{-c(w₀.im+t)} = e^{-c·w₀.im}·(a+t)^D·e^{-c t}`, integrable.
      have h0 : IntegrableOn
          (fun t : ℝ => (1 + (|w₀.re| + w₀.im) + t) ^ D * Real.exp (-c * t)) (Set.Ici M) :=
        (integrableOn_shifted_pow_mul_exp_neg (a := 1 + (|w₀.re| + w₀.im)) (by positivity) hc D
          ).mono_set (fun t ht => lt_of_lt_of_le hMpos ht)
      have h1 : IntegrableOn (fun t : ℝ =>
          (|C| * Real.exp (-c * w₀.im)) * ((1 + (|w₀.re| + w₀.im) + t) ^ D * Real.exp (-c * t)))
          (Set.Ici M) := h0.const_mul _
      refine h1.congr_fun (fun t _ => ?_) measurableSet_Ici
      simp only [hg, show -c * (w₀.im + t) = -c * w₀.im + -c * t by ring, Real.exp_add]
      ring
    refine MeasureTheory.Integrable.mono' hgint
      ((hcont h0M).aestronglyMeasurable measurableSet_Ici) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
    rw [Set.mem_Ici] at ht
    have htpos : 0 ≤ t := le_trans h0M ht
    have hyA : A ≤ w₀.im + t := by
      have : A ≤ t := le_trans (le_max_right 1 A) ht
      linarith [hw₀]
    simp only [hg0, norm_mul, Complex.norm_I, mul_one]
    rw [hcoe t]
    refine (hbound w₀.re (w₀.im + t) hyA).trans ?_
    simp only [hg]
    rw [← hcoe t]
    have hqs : ‖w₀ + Complex.I * t‖ ≤ 1 + (|w₀.re| + w₀.im) + t := by
      rw [hcoe t, Complex.norm_add_mul_I]
      have hssq : Real.sqrt (w₀.re ^ 2 + (w₀.im + t) ^ 2) ≤ |w₀.re| + (w₀.im + t) := by
        rw [show (|w₀.re| + (w₀.im + t)) = Real.sqrt ((|w₀.re| + (w₀.im + t)) ^ 2) from
          (Real.sqrt_sq (by positivity)).symm]
        apply Real.sqrt_le_sqrt
        nlinarith [abs_nonneg w₀.re, sq_abs w₀.re, hw₀, htpos,
          mul_nonneg (abs_nonneg w₀.re) (by linarith : (0:ℝ) ≤ w₀.im + t)]
      have : |w₀.re| + (w₀.im + t) ≤ 1 + (|w₀.re| + w₀.im) + t := by ring_nf; linarith
      linarith
    gcongr
    · exact le_abs_self C
    · exact max_le (by nlinarith [abs_nonneg w₀.re, hw₀.le, htpos]) (by linarith)
  -- Glue over `Ici 0 = Icc 0 M ∪ Ici M`.
  have hunion : Set.Ici (0 : ℝ) = Set.Icc 0 M ∪ Set.Ici M := by
    rw [Set.Icc_union_Ici_eq_Ici h0M]
  rw [hunion]
  exact hcompact.union htail

/-- **Interior vertical-ray FTC (`ℂ`-base form).**  For `Φ` a primitive of `periodForm f Q` on the
open upper half-plane with real-part-independent top boundary value `L`, the improper integral up
the
vertical ray from the *interior* point `w₀` to `i∞` equals `L − Φ(w₀)`.  Unlike the cusp version
(`cuspToInftyIntegral_eq_top_sub_bot`) the bottom is a genuine point of `ℍ`, so the bottom value is
just `Φ(w₀)` with no `0⁺` limit.  (FTC `∫_0^{Y₁} = Φ(w₀+iY₁) − Φ(w₀)` plus `Φ(w₀+iY₁) → L` along the
vertical ray at real part `w₀.re`.) -/
private lemma ray_integral_eq_top_sub
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ} (Q : SymPow ℂ m) (Φ : ℂ → ℂ)
    (hΦ : ∀ z : ℂ, 0 < z.im → HasDerivAt Φ (periodForm (⇑f) Q z) z) (L : ℂ)
    (hL : ∀ q : ℝ, Tendsto (fun Y : ℝ => Φ ((q : ℂ) + Y * Complex.I)) atTop (𝓝 L))
    {w₀ : ℂ} (hw₀ : 0 < w₀.im) :
    (∫ t in Set.Ioi (0 : ℝ), periodForm (⇑f) Q (w₀ + Complex.I * t) * Complex.I)
      = L - Φ w₀ := by
  set g : ℝ → ℂ := fun t => periodForm (⇑f) Q (w₀ + Complex.I * t) * Complex.I with hg
  have hint : IntegrableOn g (Set.Ici 0) := integrableOn_periodForm_ray_interior f Q hw₀
  have hintIoi : IntegrableOn g (Set.Ioi 0) := hint.mono_set Set.Ioi_subset_Ici_self
  -- Truncated integrals converge to the improper one.
  have hTrunc : Tendsto (fun Y₁ : ℝ => ∫ t in (0 : ℝ)..Y₁, g t) atTop
      (𝓝 (∫ t in Set.Ioi (0 : ℝ), g t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 hintIoi tendsto_id
  -- The `HasDerivAt` of `t ↦ Φ(w₀ + i·t)` along the ray, for `t ≥ 0` (height stays `≥ w₀.im > 0`).
  have hderiv : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun s : ℝ => Φ (w₀ + Complex.I * s)) (g t) t := by
    intro t ht
    have him : 0 < (w₀ + Complex.I * (t : ℂ)).im := by
      simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.ofReal_im, Complex.I_im,
        Complex.ofReal_re, zero_mul, zero_add]; linarith
    have h1 := hΦ _ him
    have hpath : HasDerivAt (fun s : ℝ => w₀ + Complex.I * (s : ℂ)) Complex.I t := by
      have := ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul Complex.I).const_add w₀
      simpa [mul_comm] using this
    have h2 := h1.scomp t hpath
    rw [hg]; rw [smul_eq_mul, mul_comm] at h2; exact h2
  -- FTC on `[0, Y₁]`: `∫ = Φ(w₀+iY₁) − Φ(w₀)`.
  have hFTC : ∀ Y₁ : ℝ, 0 < Y₁ →
      (∫ t in (0 : ℝ)..Y₁, g t) = Φ (w₀ + Complex.I * Y₁) - Φ w₀ := by
    intro Y₁ hY₁
    have hii : IntervalIntegrable g MeasureTheory.volume 0 Y₁ :=
      (hint.mono_set (fun t ht => by
        rw [Set.uIcc_of_le hY₁.le, Set.mem_Icc] at ht
        rw [Set.mem_Ici]; linarith [ht.1])).intervalIntegrable
    have hd : ∀ t ∈ Set.uIcc (0:ℝ) Y₁,
        HasDerivAt (fun s : ℝ => Φ (w₀ + Complex.I * s)) (g t) t := by
      intro t ht
      rw [Set.uIcc_of_le hY₁.le, Set.mem_Icc] at ht
      exact hderiv t ht.1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hii]
    norm_num
  -- Limit `Y₁ → ∞`: `Φ(w₀+iY₁) → L`, so the truncated integrals tend to `L − Φ(w₀)`.
  have htop : Tendsto (fun Y₁ : ℝ => Φ (w₀ + Complex.I * Y₁)) atTop (𝓝 L) := by
    -- Pull back the vertical-ray top limit `hL w₀.re` along `Y ↦ w₀.im + Y`.
    have hbase : Tendsto (fun Y : ℝ => Φ ((w₀.re : ℂ) + (Y : ℂ) * Complex.I)) atTop (𝓝 L) :=
      hL w₀.re
    have hcomp := hbase.comp (tendsto_atTop_add_const_left atTop w₀.im tendsto_id)
    refine hcomp.congr (fun Y₁ => ?_)
    simp only [Function.comp_apply, id_eq]
    congr 1
    conv_rhs => rw [← Complex.re_add_im w₀]
    push_cast
    ring
  have hlim : Tendsto (fun Y₁ : ℝ => ∫ t in (0 : ℝ)..Y₁, g t) atTop (𝓝 (L - Φ w₀)) := by
    have heq : (fun Y₁ : ℝ => ∫ t in (0 : ℝ)..Y₁, g t) =ᶠ[atTop]
        (fun Y₁ : ℝ => Φ (w₀ + Complex.I * Y₁) - Φ w₀) := by
      filter_upwards [eventually_gt_atTop 0] with Y₁ hY₁
      exact hFTC Y₁ hY₁
    rw [tendsto_congr' heq]
    exact htop.sub_const _
  exact tendsto_nhds_unique hTrunc hlim

/-- **EICH-2b-i (analytic core, packaged form) — the moving-basepoint Eichler defect as a single
cusp value.**  For `γ ∈ Γ₁(N)`, the pointwise weight-`(2-k)` modularity defect of `E_f` equals
`-C_k` times the cusp value of `f` against the *moving polynomial* `(·-τ)^{k-2}`
(`eichlerMovingPoly τ`)
at the single cusp `γ⁻¹∞`:

`(E_f∘↑ ∣[2-k] γ) τ - (E_f∘↑) τ = -C_k · cuspValue f (eichlerMovingPoly τ) (γ⁻¹∞)`.

This is exactly the classical Eichler formula (reply.md §1.2 (5), in the orientation-honest sign
`∫_{i∞}^{γ⁻¹∞}` — see the note on `eichler_defect_cuspValue` for the sign): by
`eichlerIntegral_eq_vertical`
(EICH-2a) both `E_f(γτ)` and `E_f(τ)` are vertical-ray integrals of `periodForm f
(eichlerMovingPoly ·)`;
the Möbius change of variables `σ = γ·w` (using `f`'s weight-`k` automorphy + the slash factor
`(cτ+d)^{k-2}` + `evalSym1_symRep_smul`) turns `E_f(γτ)·(cτ+d)^{k-2}` into the integral of
`periodForm f (symRep γ (eichlerMovingPoly τ))` from the interior point `γτ` to `i∞`; the two
interior
endpoints cancel (`mob γ τ = γτ`), leaving the cusp boundary term, which the project's primitive/FTC
engine (`cuspValue_eq_top_sub_botVal`, `tendsto_F_pole`, `tendsto_F_upper`) identifies with
`cuspValue f (eichlerMovingPoly τ)(γ⁻¹∞)`.  The genuine moving-basepoint analytic content (NOT
reducible to the fixed-polynomial `cuspValue_symRep_gamma`) is isolated here. -/
private lemma eichler_defect_eq_cuspValueMoving
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hk : 2 ≤ k)
    (γ : CongruenceSubgroup.Gamma1 N) (τ : ℍ) :
    ((eichlerIntegral f ∘ ((↑) : ℍ → ℂ)) ∣[2 - k] (γ : SL(2, ℤ))) τ -
        (eichlerIntegral f ∘ ((↑) : ℍ → ℂ)) τ =
      -(eichlerConst k) * cuspValue f (eichlerMovingPoly (k - 2).toNat τ)
        (cuspAction γ⁻¹ (OnePoint.equivProjectivization ℚ (OnePoint.infty : OnePoint ℚ))) := by
  classical
  set n : ℕ := (k - 2).toNat with hn
  set g : SL(2, ℤ) := (γ : SL(2, ℤ)) with hgdef
  set Pτ : SymPow ℂ n := eichlerMovingPoly n τ with hPτ
  set Qγ : SymPow ℂ n := symRep ℂ n g Pτ with hQγ
  set C : ℂ := eichlerConst k with hC
  -- The slash denominator `D = (g₁₀τ + g₁₁) = denom(g,τ)`, nonzero.
  set Dn : ℂ := (g 1 0 : ℂ) * (τ : ℂ) + (g 1 1 : ℂ) with hDn
  have hDne : Dn ≠ 0 := denom_mob_ne g τ.im_pos
  -- `γ•τ` and `mob g τ = ↑(γ•τ)`, with positive imaginary part.
  have hmobτ : mob g (τ : ℂ) = ((g • τ : ℍ) : ℂ) := mob_eq_smul g τ
  have hgτpos : 0 < ((g • τ : ℍ) : ℂ).im := (g • τ).im_pos
  -- A primitive `F` of `periodForm f Qγ` on ℍ, and its real-part-independent top value `Finf`.
  obtain ⟨F, hF⟩ := Complex.isExactOn_upperHalf (differentiableOn_periodForm f Qγ)
  have hFz : ∀ z : ℂ, 0 < z.im → HasDerivAt F (periodForm (⇑f) Qγ z) z := hF
  obtain ⟨Finf, hFinf⟩ := exists_tendsto_primitive_vertical_atTop f Qγ F hFz
  -- `G := F ∘ mob g` is a primitive of `periodForm f Pτ` (since `f ∣ g = f` for `g ∈ Γ₁(N)`).
  have hslashg : ⇑f ∣[k] g = ⇑f := slash_Gamma1_eq f γ γ.2
  have hG : ∀ z : ℂ, 0 < z.im → HasDerivAt (fun w => F (mob g w)) (periodForm (⇑f) Pτ z) z := by
    intro z hz
    have hd := hasDerivAt_primitive_mob_general (⇑f) g Pτ hk F (by rwa [← hQγ]) hz
    rwa [hslashg] at hd
  obtain ⟨Ginf, hGinf⟩ := exists_tendsto_primitive_vertical_atTop f Pτ (fun w => F (mob g w)) hG
  -- Integrand identity: the EICH-2a kernel `f(ofComplex(w₀+i t))·(i t)ⁿ` is `periodForm f
  -- (eichlerMovingPoly n w₀)`.
  have hker : ∀ (P : SymPow ℂ n) (w₀ : ℂ) (t : ℝ),
      evalSym1 n P (w₀ + Complex.I * t) = (Complex.I * (t : ℂ)) ^ n →
      f (UpperHalfPlane.ofComplex (w₀ + Complex.I * t)) * (Complex.I * (t : ℂ)) ^ n * Complex.I
        = periodForm (⇑f) P (w₀ + Complex.I * t) * Complex.I := by
    intro P w₀ t hev
    rw [show periodForm (⇑f) P (w₀ + Complex.I * t)
        = f (UpperHalfPlane.ofComplex (w₀ + Complex.I * t)) * evalSym1 n P (w₀ + Complex.I * t)
        from rfl, hev]
  -- (1) `E_f(τ) = C·(Ginf − G(τ))` via EICH-2a at `τ` and the interior FTC for `G`.
  have hEτ : eichlerIntegral f (τ : ℂ) = C * (Ginf - F (mob g (τ : ℂ))) := by
    rw [eichlerIntegral_eq_vertical f hk τ.im_pos, ← hn, hC]
    congr 1
    rw [show F (mob g (τ : ℂ)) = (fun w => F (mob g w)) (τ : ℂ) from rfl,
      ← ray_integral_eq_top_sub f Pτ (fun w => F (mob g w)) hG Ginf hGinf τ.im_pos]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [hker Pτ (τ : ℂ) t]
    rw [hPτ, evalSym1_eichlerMovingPoly n τ ((τ : ℂ) + Complex.I * t)]
    ring_nf
  -- (2) `E_f(γτ)·Dⁿ = C·(Finf − F(γτ))` via EICH-2a at `γτ` and the interior FTC for `F`.
  have hEγτ : eichlerIntegral f ((g • τ : ℍ) : ℂ) * Dn ^ n = C * (Finf - F ((g • τ : ℍ) : ℂ)) := by
    rw [eichlerIntegral_eq_vertical f hk hgτpos, ← hn, hC,
      ← ray_integral_eq_top_sub f Qγ F hFz Finf hFinf hgτpos,
      show (C * ∫ t in Set.Ioi (0 : ℝ), f (UpperHalfPlane.ofComplex (((g • τ : ℍ) : ℂ) +
              Complex.I * t)) * (Complex.I * (t : ℂ)) ^ n * Complex.I) * Dn ^ n
          = C * (Dn ^ n * ∫ t in Set.Ioi (0 : ℝ), f (UpperHalfPlane.ofComplex (((g • τ : ℍ) : ℂ) +
              Complex.I * t)) * (Complex.I * (t : ℂ)) ^ n * Complex.I) by ring,
      ← MeasureTheory.integral_const_mul]
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    -- `Dⁿ · [f(ofComplex(γτ+is))·(is)ⁿ·i] = periodForm f Qγ (γτ+is)·i`.
    rw [show periodForm (⇑f) Qγ (((g • τ : ℍ) : ℂ) + Complex.I * s)
        = f (UpperHalfPlane.ofComplex (((g • τ : ℍ) : ℂ) + Complex.I * s)) *
          evalSym1 n Qγ (((g • τ : ℍ) : ℂ) + Complex.I * s) from rfl]
    -- `evalSym1 Qγ (γτ+is) = Dⁿ·(is)ⁿ` via the Möbius covariance of the moving poly.
    rw [hQγ, evalSym1_symRep_eichlerMovingPoly n g τ (((g • τ : ℍ) : ℂ) + Complex.I * s), hmobτ,
      show (((g • τ : ℍ) : ℂ) + Complex.I * (s : ℂ)) - ((g • τ : ℍ) : ℂ) = Complex.I * (s : ℂ)
        by ring, ← hDn]
    ring
  -- The defect: unfold the slash and combine (1),(2).  `G(τ) = F(mob g τ) = F(γτ)` cancels.
  have hdefect : ((eichlerIntegral f ∘ ((↑) : ℍ → ℂ)) ∣[2 - k] g) τ -
      (eichlerIntegral f ∘ ((↑) : ℍ → ℂ)) τ = C * (Finf - Ginf) := by
    -- Unfold the slash: `(E∘↑ ∣[2-k] g) τ = E(↑(g•τ)) · denom(g,τ)^(k-2)`.
    rw [ModularForm.SL_slash_apply]
    have hden : UpperHalfPlane.denom
        (toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) τ = Dn := by
      rw [UpperHalfPlane.denom, hDn]; norm_cast
    rw [hden]
    have hpow : Dn ^ (-(2 - k)) = Dn ^ n := by
      rw [show (-(2 - k) : ℤ) = (n : ℤ) by rw [hn]; omega, zpow_natCast]
    simp only [Function.comp_apply, hpow]
    rw [hEγτ, hEτ, hmobτ]
    ring
  -- The cusp value: `cuspValue f Pτ (γ⁻¹∞) = Ginf − Finf` (via the FTC top/bottom + pole geodesic).
  have hcusp : cuspValue f Pτ
      (cuspAction γ⁻¹ (OnePoint.equivProjectivization ℚ (OnePoint.infty : OnePoint ℚ)))
      = Ginf - Finf := by
    -- `cuspValue f Pτ c = Ginf − (cusp boundary of G at c)`; reduce that boundary to `Finf`.
    rw [cuspValue_eq_top_sub_botVal f Pτ (fun w => F (mob g w)) hG Ginf hGinf]
    -- The `OnePoint` representative of `c = γ⁻¹·∞` is `mapGL ℚ γ⁻¹ • ∞`.
    rw [equivProjectivization_symm_cuspAction, Equiv.symm_apply_apply]
    -- Reduce to: the cusp boundary of `G` at `γ⁻¹·∞` equals `Finf`.
    have hcoeinv : ((γ⁻¹ : CongruenceSubgroup.Gamma1 N) : SL(2, ℤ)) = g⁻¹ := by
      rw [hgdef]; rfl
    rw [hcoeinv]
    congr 1
    -- `γ⁻¹ • ∞` is finite iff `(γ⁻¹)₁₀ ≠ 0` iff `g₁₀ ≠ 0`.
    rw [OnePoint.smul_infty_eq_ite]
    by_cases hc : (Matrix.SpecialLinearGroup.mapGL ℚ g⁻¹) 1 0 = 0
    · -- `g⁻¹ • ∞ = ∞`: upper-triangular case, `Ginf = Finf` via `tendsto_F_upper`.
      rw [if_pos hc]
      -- `(g⁻¹)₁₀ = 0` over ℚ ⟹ over ℤ ⟹ `g₁₀ = 0` (`(g⁻¹)₁₀ = -g₁₀`).
      have hcZ : (g⁻¹ 1 0 : ℤ) = 0 := by
        have hent : (Matrix.SpecialLinearGroup.mapGL ℚ g⁻¹) 1 0 = ((g⁻¹ 1 0 : ℤ) : ℚ) := by
          rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
          rfl
        rw [hent] at hc; exact_mod_cast hc
      have hg0 : (g 1 0 : ℝ) = 0 := by
        have h1 := (inv_entries g).1
        have h2 : (g⁻¹ 1 0 : ℝ) = 0 := by exact_mod_cast hcZ
        rw [h2] at h1; linarith
      -- `Ginf = lim F(mob g (q+iY)) = Finf` by `tendsto_F_upper` (g upper-triangular).
      exact tendsto_nhds_unique (hGinf 0) (tendsto_F_upper f Qγ F hFz Finf hFinf g 0 hg0)
    · -- `g⁻¹ • ∞ = r := (g⁻¹)₀₀/(g⁻¹)₁₀` finite: `botVal G r = Finf` via the pole geodesic.
      rw [if_neg hc]
      set r : ℚ := (Matrix.SpecialLinearGroup.mapGL ℚ g⁻¹) 0 0 /
        (Matrix.SpecialLinearGroup.mapGL ℚ g⁻¹) 1 0 with hr
      -- `g` sends `r` to `∞`: `g • r = g • (g⁻¹ • ∞) = ∞`.
      have hgr : (Matrix.SpecialLinearGroup.mapGL ℚ g) • (r : OnePoint ℚ)
          = (OnePoint.infty : OnePoint ℚ) := by
        have hrinf : (Matrix.SpecialLinearGroup.mapGL ℚ g⁻¹) • (OnePoint.infty : OnePoint ℚ)
            = (r : OnePoint ℚ) := by
          rw [OnePoint.smul_infty_eq_ite, if_neg hc]
        rw [← hrinf, ← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
      obtain ⟨hcr, hpoler⟩ := pole_of_smul_infty g r hgr
      -- `botVal f Pτ (F∘mob g) r = lim_{Y→0⁺} F(mob g (r+iY)) = Finf` via `tendsto_F_pole` (σ=1).
      have hbot := tendsto_F_pole f hk Qγ F hFz 1 Finf
        (by intro q; simpa only [show ∀ z : ℂ, mob (1 : SL(2, ℤ)) z = z from fun z => by simp [mob]]
          using hFinf q) g (r : ℝ) (by simpa using hcr) (by simpa using hpoler)
      have hbotG : Tendsto (fun Y : ℝ => F (mob g ((r : ℂ) + Y * Complex.I))) (𝓝[>] 0)
          (𝓝 (botVal f Pτ (fun w => F (mob g w)) r)) :=
        tendsto_primitive_vertical_nhdsGT_zero f Pτ r (fun w => F (mob g w)) hG
      exact tendsto_nhds_unique hbotG hbot
  rw [hdefect, hcusp, hC]
  ring

/-- **EICH-2b-i — the analytic core of the modularity-defect formula** (reply.md §1.2 (5)–(6); the
isolated function-level Möbius change-of-variables under the integral, with a *moving* basepoint).

For `γ ∈ Γ₁(N)`, writing `n = (k-2).toNat`, the pointwise modularity defect of `E_f` at weight
`2-k` equals the explicit binomial combination of cusp values of `f` against the monomials
`symMon n j = X₀ʲ X₁^{n-j}` at the single cusp `γ⁻¹·∞` (`cuspAction γ⁻¹ cInf`):

`(E_f∘↑ ∣[2-k] γ) τ - (E_f∘↑) τ = Σ_{j=0}^{n} -(C_k · C(n,j) · (-τ)^{n-j}) · cuspValue f (symMon n
j) (γ⁻¹∞)`

where `C_k = eichlerConst k` and `cInf = OnePoint.equivProjectivization ℚ ∞`.

SIGN NOTE.  The overall `-` is **mathematically forced** (reply.md §1.2 (5) is written `∫_{γ⁻¹∞}^∞`,
but the honest derivation — slash, then Möbius CoV `σ = γ·w` — yields the *opposite* orientation
`C_k ∫_{i∞}^{γ⁻¹∞} f(σ)(σ-τ)^{k-2} dσ`, i.e. `-C_k ∫_{γ⁻¹∞}^{i∞}`; since `cuspValue` is the vertical
`∫_{q₀}^{i∞}` integral, the defect is `-C_k · (cusp-value combination)`, not `+`).  Equivalently,
the
`k=2`/`n=0` case computes directly to `C_2 ∫_{i∞}^{γ⁻¹∞} f = -C_2 · cuspValue f 1 (γ⁻¹∞)`.  This
sign
is invisible to the only consumer `eichler_slash_invariant` (every cusp-value difference vanishes
under `ι(f)=0`, so `±` is immaterial there), and is absorbed by the `coeff` witness in
`eichler_slash_sub_eq_cuspValue_diff`.

This is the irreducible analytic content of EICH-2b.  By the integral representation
`eichlerIntegral_eq_vertical` (EICH-2a) both `E_f(γτ)` and `E_f(τ)` are vertical-ray Eichler
integrals; substituting `τ' = γ·w` in `E_f(γτ)` (the **function-level Möbius change of variables**,
on the moving polynomial `(τ' - τ)^{k-2}`, using `f`'s weight-`k` automorphy together with the slash
factor `denom(γ,τ)^{k-2}`) collapses the defect to the geodesic period
`-C_k ∫_{[γ⁻¹∞ → i∞]} f(τ')(τ'-τ)^{k-2} dτ'`; expanding `(τ'-τ)^n = Σ_j C(n,j)(-τ)^{n-j} τ'^j`
(binomial) and **straightening the geodesic to the vertical line** (path-independence: the cusp
decay kills the connecting horizontal cap, exactly the project's `tendsto_horizontal_cap` mechanism)
identifies the `j`-th monomial period with `cuspToInftyIntegral f (symMon n j) q₀ =
cuspValue f (symMon n j) (γ⁻¹∞)` (`evalSym1 (symMon n j) τ' = τ'^j` by `evalSym1_symMon`;
`cuspValue`
at the finite cusp `γ⁻¹∞ = q₀` is the vertical-line integral, and `0` at `∞`).

Unlike the project's `cuspValue_symRep_gamma` (the Möbius covariance of the *fixed-polynomial*
modular-symbol periods), this is the Eichler integral's *moving*-polynomial change of variables
under
the integral and is a genuinely separate development; it is therefore isolated as sub-ticket
**EICH-2b-i** (Parent = EICH-2b).  The sign/normalisation is folded into the (existential) `coeff`
of
the consumer `eichler_slash_sub_eq_cuspValue_diff`, so it does not affect the gluing in
`eichler_slash_invariant`. -/
private theorem eichler_defect_cuspValue
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hk : 2 ≤ k)
    (γ : CongruenceSubgroup.Gamma1 N) (τ : ℍ) :
    ((eichlerIntegral f ∘ ((↑) : ℍ → ℂ)) ∣[2 - k] (γ : SL(2, ℤ))) τ -
        (eichlerIntegral f ∘ ((↑) : ℍ → ℂ)) τ =
      ∑ j ∈ Finset.range ((k - 2).toNat + 1),
        -(eichlerConst k * ((k - 2).toNat).choose j * (-(τ : ℂ)) ^ ((k - 2).toNat - j)) *
          cuspValue f (symMon (k - 2).toNat j)
            (cuspAction γ⁻¹ (OnePoint.equivProjectivization ℚ (OnePoint.infty : OnePoint ℚ))) := by
  -- The genuine analytic content (the moving-basepoint Möbius CoV producing the geodesic period,
  -- straightened to the vertical line at the cusp `γ⁻¹∞`) is `eichler_defect_eq_cuspValueMoving`,
  -- which packages the defect as `-C_k · cuspValue f (eichlerMovingPoly τ)(γ⁻¹∞)`.  Here we only
  -- expand that single moving-polynomial cusp value into the stated binomial combination of the
  -- `symMon` cusp values via `cuspValue_eichlerMovingPoly` (ℂ-linearity of `cuspValue`).
  rw [eichler_defect_eq_cuspValueMoving f hk γ τ, cuspValue_eichlerMovingPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring_nf

/-- **G2a+G2b / EICH-2b — the modularity-defect formula, packaged as cusp-value differences**
(reply.md §1.2 (5)).  For `γ ∈ Γ₁(N)` the pointwise modularity defect of `E_f` at weight `2-k` is a
finite `ℂ`-linear combination of cusp-value *differences* of `f` against the monomials
`symMon n j = X₀^j X₁^{n-j}` (`n = (k-2).toNat`), at a *fixed* pair of cusps `c₁, c₂`.

The two cusps are `c₁ = γ⁻¹·∞` and `c₂ = ∞`; `coeff τ j = -C_k·C(n,j)·(-τ)^{n-j}` are (the negatives
of) the binomial coefficients of `(τ - ·)^{n}` — the sign matches the orientation-honest defect
formula `eichler_defect_cuspValue` (see its note).  Because `c₂ = ∞` has `cuspValue f · ∞ = 0`
(the cusp value at `∞` is
`0` by definition of `cuspValue`/`cuspToInftyIntegral`), each difference reduces to the single cusp
value at `c₁ = γ⁻¹∞`, and the identity is exactly the analytic core `eichler_defect_cuspValue`
(EICH-2b-i).  This thin wrapper supplies the existential witnesses and discharges the
`c₂ = ∞ ⟹ cuspValue = 0` simplification; the gluing in `eichler_slash_invariant` consumes only this
statement. -/
private theorem eichler_slash_sub_eq_cuspValue_diff
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hk : 2 ≤ k)
    (γ : CongruenceSubgroup.Gamma1 N) :
    ∃ (c₁ c₂ : Projectivization ℚ (Fin 2 → ℚ)) (coeff : ℍ → ℕ → ℂ),
      ∀ τ : ℍ,
        ((eichlerIntegral f ∘ ((↑) : ℍ → ℂ)) ∣[2 - k] (γ : SL(2, ℤ))) τ -
            (eichlerIntegral f ∘ ((↑) : ℍ → ℂ)) τ =
          ∑ j ∈ Finset.range ((k - 2).toNat + 1),
            coeff τ j *
              (cuspValue f (symMon (k - 2).toNat j) c₁ -
                cuspValue f (symMon (k - 2).toNat j) c₂) := by
  -- Witnesses: `c₁ = γ⁻¹·∞`, `c₂ = ∞`, `coeff τ j = C_k · C(n,j) · (-τ)^{n-j}`.
  refine ⟨cuspAction γ⁻¹ (OnePoint.equivProjectivization ℚ (OnePoint.infty : OnePoint ℚ)),
    OnePoint.equivProjectivization ℚ (OnePoint.infty : OnePoint ℚ),
    fun τ j => -(eichlerConst k * ((k - 2).toNat).choose j * (-(τ : ℂ)) ^ ((k - 2).toNat - j)),
    fun τ => ?_⟩
  -- The cusp value at `∞` (the second cusp) is `0` by definition of `cuspValue`.
  have hcinf : ∀ j, cuspValue f (symMon (k - 2).toNat j)
      (OnePoint.equivProjectivization ℚ (OnePoint.infty : OnePoint ℚ)) = 0 := by
    intro j
    simp only [cuspValue, Equiv.symm_apply_apply]
  simp only [hcinf, sub_zero]
  exact eichler_defect_cuspValue f hk γ τ

/-- **L7 — `ι(f)=0 ⟹ E_f|_{2-k}γ = E_f` for every `γ ∈ Γ₁(N)`** (reply.md §1.2, the heart, via the
integral defect `G2a` + the binomial period bridge `G2b` + `L0`).  The slash is taken at weight
`2-k` (note `k ≥ 2 ⟹ 2-k ≤ 0`, a genuinely non-positive weight).

TYPE-LEVEL NOTE (flagged G2 architecture gap): the mathlib weight-`w` `SlashAction` lives on
`ℍ → ℂ`, while `eichlerIntegral f : ℂ → ℂ`.  We bridge by restricting along the coercion
`((↑) : ℍ → ℂ)`: the slash invariant is stated as
`((eichlerIntegral f) ∘ ((↑) : ℍ → ℂ)) ∣[2 - k] (γ : SL(2,ℤ)) = (eichlerIntegral f) ∘ ((↑) : ℍ →
ℂ)`.
This *does* state cleanly (the `SlashAction ℤ SL(2,ℤ) (ℍ → ℂ)` instance accepts the negative weight
`2-k`), at the cost of the `UpperHalfPlane.coe` round-trip — the same cost `periodForm` pays.  No
weakening of mathematical content; the bridge `(eichlerIntegral f) ∘ ((↑) : ℍ → ℂ)` is faithful. -/
theorem eichler_slash_invariant (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hk : 2 ≤ k)
    (hf : periodMap' N k hk f = 0) (γ : CongruenceSubgroup.Gamma1 N) :
    ((eichlerIntegral f) ∘ ((↑) : ℍ → ℂ)) ∣[2 - k] (γ : SL(2, ℤ))
      = (eichlerIntegral f) ∘ ((↑) : ℍ → ℂ) := by
  -- The modularity defect is a finite combination of cusp-value differences (EICH-2b)...
  obtain ⟨c₁, c₂, coeff, hsub⟩ := eichler_slash_sub_eq_cuspValue_diff f hk γ
  -- ...each of which vanishes because `ι(f)=0` (EICH-3a, `eichler_basepoint_indep`).
  -- Hence the defect is `0`, i.e. the slashed function agrees with `E_f` at every `τ`.
  refine funext fun τ => sub_eq_zero.mp ?_
  rw [hsub τ]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [eichler_basepoint_indep f hk hf (symMon (k - 2).toNat j) c₁ c₂, sub_self, mul_zero]

/-- **Boundedness at `i∞` of the `∞`-Eichler integral of a generic arithmetic cusp form.**  For any
arithmetic cusp form `g0` and `n = (k-2).toNat`, the function `E_{g0}(τ) = ∫_0^∞ g0(τ+it)·(it)ⁿ·i
dt`
(`g0` extended off `ℍ` by `ofComplex`) is bounded as `Im τ → ∞`.  This is the cleaner "dominated
integral" form of the cusp-holomorphy step (reply.md §1.3): `g0` is a cusp form ⟹ exponential decay
`‖g0(z)‖ ≤ C·exp(-c·Im z)`, so for `Im τ ≥ A` (uniformly in `Re τ`) the integral is bounded by
`C·exp(-c·Im τ)·∫_0^∞ tⁿ exp(-c t) dt → 0`; hence `IsBoundedAtImInfty` (in fact `→ 0`).  This is the
boundedness of the conjugate cusp form's Eichler integral `E_g` (`g = f∣[k]γ`), the analytic core of
the finite-cusp case.  No width-`h` `q`-series is needed — the dominated integral suffices. -/
private lemma eichlerIntegralGen_isBoundedAtImInfty {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} [CuspFormClass F Γ k] [Γ.IsArithmetic] (g0 : F) (n : ℕ)
    (_hn : n = (k - 2).toNat) :
    UpperHalfPlane.IsBoundedAtImInfty
      (fun τ : ℍ => ∫ t in Set.Ioi (0 : ℝ),
        g0 (UpperHalfPlane.ofComplex ((τ : ℂ) + Complex.I * t)) *
          (Complex.I * (t : ℂ)) ^ n * Complex.I) := by
  obtain ⟨c, hc, Cg, Ag, hbound⟩ := exists_exp_decay_bound g0
  -- The reference Gamma integral `K = ∫_0^∞ tⁿ exp(-c t) dt ≥ 0`.
  have hKint : IntegrableOn (fun t : ℝ => (t : ℝ) ^ n * Real.exp (-c * t)) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (n : ℝ)) (b := c)
      (neg_one_lt_zero.trans_le (Nat.cast_nonneg n)) one_pos hc
    refine h.congr_fun (fun s hs => ?_) measurableSet_Ioi
    simp only [Real.rpow_natCast, Real.rpow_one]
  set K : ℝ := ∫ t in Set.Ioi (0 : ℝ), (t : ℝ) ^ n * Real.exp (-c * t) with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]; exact MeasureTheory.setIntegral_nonneg measurableSet_Ioi
      (fun t ht => by have : (0:ℝ) < t := ht; positivity)
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨|Cg| * K, max Ag 1, fun τ hτ => ?_⟩
  have hτ1 : (1 : ℝ) ≤ (τ : ℂ).im := le_trans (le_max_right Ag 1) hτ
  have hτA : Ag ≤ (τ : ℂ).im := le_trans (le_max_left Ag 1) hτ
  have hτpos : 0 < (τ : ℂ).im := lt_of_lt_of_le one_pos hτ1
  -- The integrand is `periodForm g0 (eichlerMovingPoly n τ) (τ+it)·i`; integrable by the generic
  -- interior ray integrability.
  have hev : ∀ t : ℝ, g0 (UpperHalfPlane.ofComplex ((τ : ℂ) + Complex.I * t)) *
      (Complex.I * (t : ℂ)) ^ n * Complex.I
      = periodForm (⇑g0) (eichlerMovingPoly n τ) ((τ : ℂ) + Complex.I * t) * Complex.I := by
    intro t
    rw [show periodForm (⇑g0) (eichlerMovingPoly n τ) ((τ : ℂ) + Complex.I * t)
        = g0 (UpperHalfPlane.ofComplex ((τ : ℂ) + Complex.I * t)) *
          evalSym1 n (eichlerMovingPoly n τ) ((τ : ℂ) + Complex.I * t) from rfl,
      evalSym1_eichlerMovingPoly n τ ((τ : ℂ) + Complex.I * t),
      show ((τ : ℂ) + Complex.I * t) - (τ : ℂ) = Complex.I * (t : ℂ) by ring]
  have hintIci : IntegrableOn (fun t : ℝ =>
      g0 (UpperHalfPlane.ofComplex ((τ : ℂ) + Complex.I * t)) *
        (Complex.I * (t : ℂ)) ^ n * Complex.I) (Set.Ici 0) := by
    refine (integrableOn_periodFormGen_ray_interior g0 (eichlerMovingPoly n τ) hτpos).congr_fun
      (fun t _ => (hev t).symm) measurableSet_Ici
  have hintIoi : IntegrableOn (fun t : ℝ =>
      g0 (UpperHalfPlane.ofComplex ((τ : ℂ) + Complex.I * t)) *
        (Complex.I * (t : ℂ)) ^ n * Complex.I) (Set.Ioi 0) :=
    hintIci.mono_set Set.Ioi_subset_Ici_self
  -- Pointwise norm bound on `Ioi 0`: `‖g0(τ+it)·(it)ⁿ·i‖ ≤ Cg·exp(-c·Imτ)·(tⁿ·exp(-c t))`.
  have hpt : ∀ t : ℝ, 0 < t →
      ‖g0 (UpperHalfPlane.ofComplex ((τ : ℂ) + Complex.I * t)) *
          (Complex.I * (t : ℂ)) ^ n * Complex.I‖
        ≤ (Cg * Real.exp (-c * (τ : ℂ).im)) * ((t : ℝ) ^ n * Real.exp (-c * t)) := by
    intro t ht
    have himeq : ((τ : ℂ) + Complex.I * (t : ℂ)).im = (τ : ℂ).im + t := by
      simp [Complex.add_im, Complex.mul_im]
    have him : 0 < ((τ : ℂ) + Complex.I * (t : ℂ)).im := by rw [himeq]; linarith
    rw [show UpperHalfPlane.ofComplex ((τ : ℂ) + Complex.I * (t : ℂ)) = (⟨_, him⟩ : ℍ) from
      UpperHalfPlane.ofComplex_apply_of_im_pos him]
    have hzim : (⟨(τ : ℂ) + Complex.I * (t : ℂ), him⟩ : ℍ).im = (τ : ℂ).im + t := himeq
    have hgz : ‖g0 (⟨(τ : ℂ) + Complex.I * (t : ℂ), him⟩ : ℍ)‖
        ≤ Cg * Real.exp (-c * ((τ : ℂ).im + t)) := by
      have := hbound (⟨(τ : ℂ) + Complex.I * (t : ℂ), him⟩ : ℍ) (by rw [hzim]; linarith)
      rwa [hzim] at this
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_pow, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    calc ‖g0 (⟨(τ : ℂ) + Complex.I * (t : ℂ), him⟩ : ℍ)‖ * (t : ℝ) ^ n
        ≤ (Cg * Real.exp (-c * ((τ : ℂ).im + t))) * (t : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right hgz (by positivity)
      _ = (Cg * Real.exp (-c * (τ : ℂ).im)) * ((t : ℝ) ^ n * Real.exp (-c * t)) := by
          rw [show -c * ((τ : ℂ).im + t) = -c * (τ : ℂ).im + -c * t by ring, Real.exp_add]; ring
  -- Bound the integral norm.
  calc ‖∫ t in Set.Ioi (0 : ℝ),
          g0 (UpperHalfPlane.ofComplex ((τ : ℂ) + Complex.I * t)) *
            (Complex.I * (t : ℂ)) ^ n * Complex.I‖
      ≤ ∫ t in Set.Ioi (0 : ℝ),
          ‖g0 (UpperHalfPlane.ofComplex ((τ : ℂ) + Complex.I * t)) *
            (Complex.I * (t : ℂ)) ^ n * Complex.I‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioi (0 : ℝ),
          (Cg * Real.exp (-c * (τ : ℂ).im)) * ((t : ℝ) ^ n * Real.exp (-c * t)) := by
        refine MeasureTheory.setIntegral_mono_on hintIoi.norm
          ((hKint.const_mul _)) measurableSet_Ioi (fun t ht => hpt t ht)
    _ = (Cg * Real.exp (-c * (τ : ℂ).im)) * K := by rw [MeasureTheory.integral_const_mul, ← hKdef]
    _ ≤ |Cg| * K := by
        have hexp1 : Real.exp (-c * (τ : ℂ).im) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have : 0 ≤ c * (τ : ℂ).im := mul_nonneg hc.le hτpos.le
          linarith
        have hfac : Cg * Real.exp (-c * (τ : ℂ).im) ≤ |Cg| := by
          calc Cg * Real.exp (-c * (τ : ℂ).im)
              ≤ |Cg| * Real.exp (-c * (τ : ℂ).im) :=
                mul_le_mul_of_nonneg_right (le_abs_self Cg) (Real.exp_nonneg _)
            _ ≤ |Cg| * 1 := mul_le_mul_of_nonneg_left hexp1 (abs_nonneg _)
            _ = |Cg| := mul_one _
        exact mul_le_mul_of_nonneg_right hfac hKnn

/-- The conjugate arithmetic group `γ⁻¹•Γ` (`Γ = Γ₁(N)`) is arithmetic, for the `mapGL ℝ
γ`-translate
`g = f∣[k]γ` to be a `CuspForm` with the full cusp-value/decay API. -/
private instance instArithmetic_conj_mapGL (γ : SL(2, ℤ)) :
    (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ •
      ((Gamma1 N).map (mapGL ℝ))).IsArithmetic := by
  have h : (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹
      = ((Matrix.SpecialLinearGroup.mapGL ℚ γ)⁻¹).map (algebraMap ℚ ℝ) := by
    rw [map_inv, map_mapGL]
  rw [h]
  exact Subgroup.IsArithmetic.conj _ (Matrix.SpecialLinearGroup.mapGL ℚ γ)⁻¹

/-- **The general-`γ` Eichler slash decomposition** (`g := f∣[k]γ`, `n := (k-2).toNat`,
`C := eichlerConst k`).  For *every* `γ ∈ SL(2,ℤ)` the slashed Eichler integral is the `∞`-Eichler
integral of the conjugate cusp form `g` minus `C` times a single conjugate cusp value:

`(E_f∘↑ ∣[2-k] γ) τ = C·∫_0^∞ g(τ+is)·(is)ⁿ·i ds − C·cuspValueGen g ((·-τ)ⁿ)(γ⁻¹∞)`.

This is the honest general-`γ` form of `eichler_defect_eq_cuspValueMoving` (which only handled
`γ ∈ Γ₁(N)`, where `g = f`): the Möbius change of variables `σ = γ·w` turns `E_f(γτ)·denom(γ,τ)ⁿ`
into the integral of `periodForm f (symRep γ (·-τ)ⁿ)` from `γτ` to `i∞`
(`eichlerIntegral_eq_vertical`
+ `evalSym1_symRep_eichlerMovingPoly`, `rayGen_integral_eq_top_sub`); its primitive `F` pulled
back by
`mob γ` is, by `hasDerivAt_primitive_mob_general`, a primitive of `periodForm g (·-τ)ⁿ` — and that
integral is exactly `E_g`.  The constant gap `C·(F∞ − G∞)` between the two frames' top boundary
values
is `−C·cuspValueGen g (·-τ)ⁿ (γ⁻¹∞)` (the finite-cusp boundary of `G` at `γ⁻¹∞` is `F∞`, via
`tendsto_F_pole`/`tendsto_F_upper`), the *single* conjugate cusp value that — unlike the `Γ₁(N)`
case
— survives.  (Under `ι(f)=0` it vanishes too, by `cuspValueGen_eq_zero_of_periodMap'_zero`.) -/
private lemma eichler_slashSL_eq_eichlerIntegralGen_sub_cuspValueGen
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hk : 2 ≤ k) (γ : SL(2, ℤ)) (τ : ℍ) :
    ((eichlerIntegral f ∘ ((↑) : ℍ → ℂ)) ∣[2 - k] γ) τ =
      eichlerConst k * (∫ t in Set.Ioi (0 : ℝ),
          (CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ γ))
            (UpperHalfPlane.ofComplex ((τ : ℂ) + Complex.I * t)) *
            (Complex.I * (t : ℂ)) ^ (k - 2).toNat * Complex.I)
        - eichlerConst k * cuspValueGen (CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ γ))
            (eichlerMovingPoly (k - 2).toNat τ)
            ((OnePoint.equivProjectivization ℚ)
              ((Matrix.SpecialLinearGroup.mapGL ℚ γ⁻¹) • (OnePoint.infty : OnePoint ℚ))) := by
  classical
  set n : ℕ := (k - 2).toNat with hn
  set g : CuspForm (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ •
    ((Gamma1 N).map (mapGL ℝ))) k := CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ γ)
    with hgdef
  set Pτ : SymPow ℂ n := eichlerMovingPoly n τ with hPτ
  set Qγ : SymPow ℂ n := symRep ℂ n γ Pτ with hQγ
  set C : ℂ := eichlerConst k with hC
  -- `⇑g = ⇑f ∣[k] γ` (definitionally, via `SL_slash` and the `(γ : GL) = mapGL ℝ γ` coercion).
  have hgfn : ⇑g = ⇑f ∣[k] γ := rfl
  -- The slash denominator `D = (γ₁₀τ + γ₁₁) = denom(γ,τ)`, nonzero.
  set Dn : ℂ := (γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ) with hDn
  have hDne : Dn ≠ 0 := denom_mob_ne γ τ.im_pos
  -- `γ•τ` and `mob γ τ = ↑(γ•τ)`, with positive imaginary part.
  have hmobτ : mob γ (τ : ℂ) = ((γ • τ : ℍ) : ℂ) := mob_eq_smul γ τ
  have hgτpos : 0 < ((γ • τ : ℍ) : ℂ).im := (γ • τ).im_pos
  -- A primitive `F` of `periodForm f Qγ` on ℍ, and its real-part-independent top value `Finf`.
  obtain ⟨F, hF⟩ := Complex.isExactOn_upperHalf (differentiableOn_periodForm f Qγ)
  have hFz : ∀ z : ℂ, 0 < z.im → HasDerivAt F (periodForm (⇑f) Qγ z) z := hF
  obtain ⟨Finf, hFinf⟩ := exists_tendsto_primitive_vertical_atTop f Qγ F hFz
  -- `G := F ∘ mob γ` is a primitive of `periodForm g Pτ` (general `γ`: slash survives on `g`).
  have hG : ∀ z : ℂ, 0 < z.im → HasDerivAt (fun w => F (mob γ w)) (periodForm (⇑g) Pτ z) z := by
    intro z hz
    rw [hgfn]
    exact hasDerivAt_primitive_mob_general (⇑f) γ Pτ hk F (by rwa [← hQγ]) hz
  obtain ⟨Ginf, hGinf⟩ := exists_tendsto_primitive_vertical_atTop' g Pτ (fun w => F (mob γ w)) hG
  -- Integrand identity helper.
  have hker : ∀ (P : SymPow ℂ n) (h0 : ℍ → ℂ) (w₀ : ℂ) (t : ℝ),
      evalSym1 n P (w₀ + Complex.I * t) = (Complex.I * (t : ℂ)) ^ n →
      h0 (UpperHalfPlane.ofComplex (w₀ + Complex.I * t)) * (Complex.I * (t : ℂ)) ^ n * Complex.I
        = periodForm h0 P (w₀ + Complex.I * t) * Complex.I := by
    intro P h0 w₀ t hev
    rw [show periodForm h0 P (w₀ + Complex.I * t)
        = h0 (UpperHalfPlane.ofComplex (w₀ + Complex.I * t)) * evalSym1 n P (w₀ + Complex.I * t)
        from rfl, hev]
  -- (Eg) `E_g(τ) := C·∫ g(τ+is)·(is)ⁿ·i ds = C·(Ginf − G(τ))` via the generic interior FTC for `G`.
  have hEg : C * (∫ t in Set.Ioi (0 : ℝ),
        g (UpperHalfPlane.ofComplex ((τ : ℂ) + Complex.I * t)) *
          (Complex.I * (t : ℂ)) ^ n * Complex.I)
      = C * (Ginf - F (mob γ (τ : ℂ))) := by
    congr 1
    rw [show F (mob γ (τ : ℂ)) = (fun w => F (mob γ w)) (τ : ℂ) from rfl,
      ← rayGen_integral_eq_top_sub g Pτ (fun w => F (mob γ w)) hG Ginf hGinf τ.im_pos]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [hker Pτ (⇑g) (τ : ℂ) t]
    rw [hPτ, evalSym1_eichlerMovingPoly n τ ((τ : ℂ) + Complex.I * t)]
    ring_nf
  -- (Eγτ) `E_f(γτ)·Dⁿ = C·(Finf − F(γτ))` via EICH-2a at `γτ` and the interior FTC for `F`.
  have hEγτ : eichlerIntegral f ((γ • τ : ℍ) : ℂ) * Dn ^ n = C * (Finf - F ((γ • τ : ℍ) : ℂ)) := by
    rw [eichlerIntegral_eq_vertical f hk hgτpos, ← hn, hC,
      ← ray_integral_eq_top_sub f Qγ F hFz Finf hFinf hgτpos,
      show (C * ∫ t in Set.Ioi (0 : ℝ), f (UpperHalfPlane.ofComplex (((γ • τ : ℍ) : ℂ) +
              Complex.I * t)) * (Complex.I * (t : ℂ)) ^ n * Complex.I) * Dn ^ n
          = C * (Dn ^ n * ∫ t in Set.Ioi (0 : ℝ), f (UpperHalfPlane.ofComplex (((γ • τ : ℍ) : ℂ) +
              Complex.I * t)) * (Complex.I * (t : ℂ)) ^ n * Complex.I) by rw [hC]; ring,
      ← MeasureTheory.integral_const_mul]
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    rw [show periodForm (⇑f) Qγ (((γ • τ : ℍ) : ℂ) + Complex.I * s)
        = f (UpperHalfPlane.ofComplex (((γ • τ : ℍ) : ℂ) + Complex.I * s)) *
          evalSym1 n Qγ (((γ • τ : ℍ) : ℂ) + Complex.I * s) from rfl]
    rw [hQγ, evalSym1_symRep_eichlerMovingPoly n γ τ (((γ • τ : ℍ) : ℂ) + Complex.I * s), hmobτ,
      show (((γ • τ : ℍ) : ℂ) + Complex.I * (s : ℂ)) - ((γ • τ : ℍ) : ℂ) = Complex.I * (s : ℂ)
        by ring, ← hDn]
    ring
  -- The slash: `(E_f∘↑ ∣[2-k] γ) τ = E_f(↑(γ•τ))·Dⁿ = C·(Finf − F(γτ))`.
  have hslash : ((eichlerIntegral f ∘ ((↑) : ℍ → ℂ)) ∣[2 - k] γ) τ =
      C * (Finf - F ((γ • τ : ℍ) : ℂ)) := by
    rw [ModularForm.SL_slash_apply]
    have hden : UpperHalfPlane.denom
        (toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) τ = Dn := by
      rw [UpperHalfPlane.denom, hDn]; norm_cast
    rw [hden]
    have hpow : Dn ^ (-(2 - k)) = Dn ^ n := by
      rw [show (-(2 - k) : ℤ) = (n : ℤ) by rw [hn]; omega, zpow_natCast]
    simp only [Function.comp_apply, hpow]
    rw [hEγτ]
  -- The conjugate cusp value: `cuspValueGen g Pτ (γ⁻¹∞) = Ginf − Finf` (generic FTC + pole
  -- geodesic).
  have hcusp : cuspValueGen g Pτ
      ((OnePoint.equivProjectivization ℚ)
        ((Matrix.SpecialLinearGroup.mapGL ℚ γ⁻¹) • (OnePoint.infty : OnePoint ℚ)))
      = Ginf - Finf := by
    rw [cuspValueGen_eq_top_sub_botValGen g Pτ (fun w => F (mob γ w)) hG Ginf hGinf]
    rw [Equiv.symm_apply_apply]
    congr 1
    rw [OnePoint.smul_infty_eq_ite]
    by_cases hcc : (Matrix.SpecialLinearGroup.mapGL ℚ γ⁻¹) 1 0 = 0
    · -- `γ⁻¹ • ∞ = ∞` (γ upper-triangular): `Ginf = Finf` via `tendsto_F_upper`.
      rw [if_pos hcc]
      have hcZ : (γ⁻¹ 1 0 : ℤ) = 0 := by
        have hent : (Matrix.SpecialLinearGroup.mapGL ℚ γ⁻¹) 1 0 = ((γ⁻¹ 1 0 : ℤ) : ℚ) := by
          rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]; rfl
        rw [hent] at hcc; exact_mod_cast hcc
      have hg0 : (γ 1 0 : ℝ) = 0 := by
        have h1 := (inv_entries γ).1
        have h2 : (γ⁻¹ 1 0 : ℝ) = 0 := by exact_mod_cast hcZ
        rw [h2] at h1; linarith
      exact tendsto_nhds_unique (hGinf 0) (tendsto_F_upper f Qγ F hFz Finf hFinf γ 0 hg0)
    · rw [if_neg hcc]
      set r : ℚ := (Matrix.SpecialLinearGroup.mapGL ℚ γ⁻¹) 0 0 /
        (Matrix.SpecialLinearGroup.mapGL ℚ γ⁻¹) 1 0 with hr
      have hgr : (Matrix.SpecialLinearGroup.mapGL ℚ γ) • (r : OnePoint ℚ)
          = (OnePoint.infty : OnePoint ℚ) := by
        have hrinf : (Matrix.SpecialLinearGroup.mapGL ℚ γ⁻¹) • (OnePoint.infty : OnePoint ℚ)
            = (r : OnePoint ℚ) := by
          rw [OnePoint.smul_infty_eq_ite, if_neg hcc]
        rw [← hrinf, ← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
      obtain ⟨hcr, hpoler⟩ := pole_of_smul_infty γ r hgr
      have hbot := tendsto_F_pole f hk Qγ F hFz 1 Finf
        (by intro q; simpa only [show ∀ z : ℂ, mob (1 : SL(2, ℤ)) z = z from fun z => by simp [mob]]
          using hFinf q) γ (r : ℝ) (by simpa using hcr) (by simpa using hpoler)
      have hbotG : Tendsto (fun Y : ℝ => F (mob γ ((r : ℂ) + Y * Complex.I))) (𝓝[>] 0)
          (𝓝 (botValGen g Pτ (fun w => F (mob γ w)) r)) :=
        tendsto_primitive_vertical_nhdsGT_zeroGen g Pτ r (fun w => F (mob γ w)) hG
      exact tendsto_nhds_unique hbotG hbot
  -- Assemble: `slash = C·(Finf − F(γτ)) = E_g − C·cuspValueGen g Pτ (γ⁻¹∞)`.
  rw [hslash, hcusp, hEg, hmobτ]
  ring

/-- `cuspValueGen` depends only on the underlying function `⇑f0` (built from
`genPeriodIntegral`/`genIntegrand`, which take a raw `ℍ → ℂ`).  Lets us pass between two equal-as-
functions conjugate cusp forms living in different (heterogeneous) arithmetic groups. -/
private lemma cuspValueGen_congr {F F' : Type*} [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ]
    {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} [CuspFormClass F Γ k] [Γ.IsArithmetic]
    [CuspFormClass F' Γ' k] [Γ'.IsArithmetic] (f1 : F) (f2 : F') (hco : ⇑f1 = ⇑f2) {m : ℕ}
    (P : SymPow ℂ m) (c : Projectivization ℚ (Fin 2 → ℚ)) :
    cuspValueGen f1 P c = cuspValueGen f2 P c := by
  rw [cuspValueGen, cuspValueGen]
  cases (OnePoint.equivProjectivization ℚ).symm c with
  | infty => rfl
  | coe r =>
    haveI : (ConjAct.toConjAct (transMat r)⁻¹ • Γ).IsArithmetic := isArithmetic_conj_transMat r
    haveI : (ConjAct.toConjAct (transMat r)⁻¹ • Γ').IsArithmetic := isArithmetic_conj_transMat r
    simp only [cuspToInftyIntegralGen, genPeriodIntegral]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [coe_cuspForm_translate_transMat, coe_cuspForm_translate_transMat, hco]

/-- `rawBilinGen` against a single divisor (generic analogue of `rawBilin_single`). -/
private lemma rawBilinGen_single {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)}
    [CuspFormClass F Γ k] [Γ.IsArithmetic] (f0 : F) {m : ℕ}
    (c : Projectivization ℚ (Fin 2 → ℚ)) (j : ℤ) (P : SymPow ℤ m) :
    rawBilinGen f0 (Finsupp.single c j) P = (j : ℂ) * cuspValueGen f0 (castSymPow m P) c := by
  rw [rawBilinGen, Finsupp.linearCombination_single, LinearMap.smul_apply, cuspFunctionalGen]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, zsmul_eq_mul]

/-- **Base-point independence for the conjugate cusp form** (generic port of
`eichler_basepoint_indep`
to `cuspValueGen`).  Under `ι(f)=0`, every conjugate cusp value `cuspValueGen g P c` vanishes (`g =
f∣[k]γ`): the cusp-value *differences* vanish (the `Div⁰`-content of `ι(g)=0` via
`rawPairingGen_actMat`, since `γ` has determinant `1` so `glMap (heilbronnGL γ) = mapGL ℝ γ`), and
`cuspValueGen g P ∞ = 0` by definition, so all are `0`.  (The `rawPairingGen` content is carried
by the
`glMap (heilbronnGL γ)`-translate `g'`, which is equal as a *function* to `g`; the two are bridged
at
the `cuspValueGen` level by `cuspValueGen_congr`, sidestepping the heterogeneous group
dependence.) -/
private lemma cuspValueGen_translate_eq_zero (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hk : 2 ≤ k)
    (hf : periodMap' N k hk f = 0) (γ : SL(2, ℤ)) (P : SymPow ℂ (k - 2).toNat)
    (c : Projectivization ℚ (Fin 2 → ℚ)) :
    cuspValueGen (CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ γ)) P c = 0 := by
  set g := CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ γ) with hgdef
  have hdet : 0 < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by
    rw [Matrix.SpecialLinearGroup.det_coe]; norm_num
  -- The `glMap (heilbronnGL γ)`-translate `g'` carries the `rawPairingGen` (=
  -- `rawPairingGen_actMat`).
  set g' := CuspForm.translate f (glMap (heilbronnGL (γ : Matrix (Fin 2) (Fin 2) ℤ) hdet.ne'))
    with hg'def
  -- `g` and `g'` are equal as functions (`mapGL ℝ γ = glMap (heilbronnGL γ)`, both slashes agree).
  have hbridge : Matrix.SpecialLinearGroup.mapGL ℝ γ
      = glMap (heilbronnGL (γ : Matrix (Fin 2) (Fin 2) ℤ) hdet.ne') := by
    rw [heilbronnGL_sl, glMap_mapGL_eq]
  have hco : ⇑g = ⇑g' := by
    have e1 : (⇑g : ℍ → ℂ) = ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) := rfl
    have e2 : (⇑g' : ℍ → ℂ)
        = ⇑f ∣[k] (glMap (heilbronnGL (γ : Matrix (Fin 2) (Fin 2) ℤ) hdet.ne')) := rfl
    rw [e1, e2, hbridge]
  -- `cInf = ∞`: `cuspValueGen g · ∞ = 0` by definition (anchor for the differences).
  set cInf : Projectivization ℚ (Fin 2 → ℚ) :=
    OnePoint.equivProjectivization ℚ (OnePoint.infty : OnePoint ℚ) with hcInf
  have hinf : ∀ Q : SymPow ℂ (k - 2).toNat, cuspValueGen g Q cInf = 0 := by
    intro Q; rw [cuspValueGen, hcInf, Equiv.symm_apply_apply]
  -- Integer case: cusp-difference periods of `g` vanish (`ι(g)=0`), bridged `g' ↦ g`.
  have hint : ∀ Q : SymPow ℤ (k - 2).toNat,
      cuspValueGen g (castSymPow (k - 2).toNat Q) c =
        cuspValueGen g (castSymPow (k - 2).toNat Q) cInf := by
    intro Q
    have hz := rawPairingGen_actMat hk f (γ : Matrix (Fin 2) (Fin 2) ℤ) hdet
      (divDiff c cInf ⊗ₜ[ℤ] Q)
    rw [rawPairing_eq_zero_of_periodMap'_zero hk f hf, ← hg'def] at hz
    rw [rawPairingGen_tmul, divDiff_val, map_sub, LinearMap.sub_apply,
      rawBilinGen_single, rawBilinGen_single] at hz
    simp only [Int.cast_one, one_mul] at hz
    have heq := eq_of_sub_eq_zero hz
    rw [cuspValueGen_congr g g' hco, cuspValueGen_congr g g' hco]
    exact heq
  -- It suffices to show `cuspValueGen g P c = cuspValueGen g P cInf = 0` for complex `P`.
  suffices h : cuspValueGen g P c = cuspValueGen g P cInf by rw [h, hinf]
  -- Extend to complex `P` by `ℂ`-linearity over the spanning set `range castSymPow`.
  have hzero : ∀ d : Projectivization ℚ (Fin 2 → ℚ),
      cuspValueGen g (0 : SymPow ℂ (k - 2).toNat) d = 0 := by
    intro d
    rw [show (0 : SymPow ℂ (k - 2).toNat) = (0 : ℂ) • 0 by simp, cuspValueGen_smul_right, zero_smul]
  have hspan : P ∈ Submodule.span ℂ (Set.range (castSymPow (k - 2).toNat)) := by
    rw [span_range_castSymPow_eq_top]; exact Submodule.mem_top
  refine Submodule.span_induction
    (p := fun P (_ : P ∈ Submodule.span ℂ (Set.range (castSymPow (k - 2).toNat))) =>
      cuspValueGen g P c = cuspValueGen g P cInf)
    (fun x hx => ?_) ?_ (fun x y _ _ hx hy => ?_) (fun a x _ hx => ?_) hspan
  · obtain ⟨Q, rfl⟩ := hx; exact hint Q
  · rw [hzero, hzero]
  · rw [cuspValueGen_add_right, cuspValueGen_add_right, hx, hy]
  · rw [cuspValueGen_smul_right, cuspValueGen_smul_right, hx]

/-- **EICH-3a-i (PROVEN) — boundedness of the slashed Eichler integral at a *finite* cusp**
(`γ • ∞ ≠ ∞`, i.e. the lower-left entry `γ₁₀ ≠ 0`).  This is the genuine analytic content of
reply.md §1.3 (8) that survives after the `γ • ∞ = ∞` (`γ₁₀ = 0`) case is dispatched directly (in
`eichler_bdd_at_cusp`).

PROOF (the dominated-integral route, *not* a width-`h` `q`-series).  Write `g := f ∣[k] γ`
(`= CuspForm.translate f (mapGL ℝ γ)`, a `CuspForm` for the arithmetic conjugate group `γ⁻¹•Γ`),
`n := (k-2).toNat`, `C := eichlerConst k`.  By
`eichler_slashSL_eq_eichlerIntegralGen_sub_cuspValueGen`
(the honest general-`γ` form of `eichler_defect_eq_cuspValueMoving`: the Möbius change of variables
`σ = γ·w`, the generic interior-ray FTC `rayGen_integral_eq_top_sub`, the `tendsto_F_pole`/`_upper`
boundary engine):

`(E_f∘↑ ∣[2-k] γ) τ = C·∫₀^∞ g(τ+is)·(is)ⁿ·i ds − C·cuspValueGen g ((·-τ)ⁿ)(γ⁻¹∞)`.

The first term is the `∞`-Eichler integral `E_g(τ)` of `g`; the second is the degree-`≤n` period
polynomial `P(τ)`, the *single* conjugate cusp value that survives for general `γ` (it collapses to
`0` only for `γ ∈ Γ₁(N)`, where `g = f`).  Under `ι(f)=0` the polynomial vanishes
(`cuspValueGen_translate_eq_zero`: `ι(f)=0 ⟹ ι(g)=0` via `rawPairingGen_actMat` — `γ` has det `1`,
so
`glMap (heilbronnGL γ) = mapGL ℝ γ` — plus the generic base-point independence forcing every
conjugate cusp value to the vanishing value at `∞`).  So the slash *equals* `C·E_g`, and `E_g` is
bounded at `i∞` by the dominated-integral cusp-decay bound `eichlerIntegralGen_isBoundedAtImInfty`
(`g` is a cusp form ⟹ `‖g(z)‖ ≤ A·exp(-c·Im z)`, so `‖E_g(τ)‖ ≤ A'·exp(-c·Im τ)·∫₀^∞ tⁿe^{-ct}dt`).
No width-`h` `q`-expansion or slashed-Bol identity is needed.

NOTE: `hf` is genuinely needed here (the period polynomial `P` is nonzero in general and vanishes
only under `ι(f)=0`), unlike the `γ • ∞ = ∞` case where boundedness is automatic from `b₀ = 0`. -/
private theorem eichler_slashSL_bdd_finite (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hk : 2 ≤ k)
    (hf : periodMap' N k hk f = 0) (γ : SL(2, ℤ)) (_hc : ¬ ((γ 1 0 : ℝ) = 0)) :
    UpperHalfPlane.IsBoundedAtImInfty
      (((eichlerIntegral f) ∘ ((↑) : ℍ → ℂ)) ∣[2 - k] γ) := by
  set g := CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ γ) with hgdef
  -- Decomposition + `ι(g)=0` (`cuspValueGen g … = 0`): the slash IS `C·E_g` (period polynomial
  -- gone).
  have hdecomp : ((eichlerIntegral f ∘ ((↑) : ℍ → ℂ)) ∣[2 - k] γ)
      = eichlerConst k • (fun τ : ℍ => ∫ t in Set.Ioi (0 : ℝ),
          g (UpperHalfPlane.ofComplex ((τ : ℂ) + Complex.I * t)) *
            (Complex.I * (t : ℂ)) ^ (k - 2).toNat * Complex.I) := by
    funext τ
    rw [eichler_slashSL_eq_eichlerIntegralGen_sub_cuspValueGen f hk γ τ, ← hgdef,
      cuspValueGen_translate_eq_zero f hk hf γ _ _, mul_zero, sub_zero]
    rfl
  rw [hdecomp]
  -- `E_g` is bounded (dominated integral on the cusp form `g`); scale by the constant `C`.
  exact (eichlerIntegralGen_isBoundedAtImInfty g (k - 2).toNat rfl).smul (eichlerConst k)

/-- **G3b (all cusps) — boundedness of `E_f` at *every* cusp** (reply.md §1.3 (8)).
The `bdd_at_cusps'` field of `eichlerModularForm : ModularForm ((Gamma1 N).map (mapGL ℝ)) (2-k)`
requires `c.IsBoundedAt (E_f ∘ ↑) (2-k)` for **every** `c : OnePoint ℝ` that is a cusp of
`(Gamma1 N).map (mapGL ℝ)`.  Because that group is arithmetic, by
`Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z` + `OnePoint.isBoundedAt_iff_forall_SL2Z` this is
*equivalent* to the statement below: for every `γ ∈ SL(2,ℤ)`, the slash `(E_f ∘ ↑) ∣[2-k] γ` is
bounded at `i∞`.

This splits on whether `γ • ∞ = ∞` (the lower-left entry `γ₁₀`):
* **`γ₁₀ = 0` (`γ • ∞ = ∞`) — PROVEN here.**  Then `γ` is upper-triangular, `denom γ τ = γ₁₁ = ±1`
  (norm `1`) and `Im (γ • τ) = Im τ`, so `‖(E_f∘↑ ∣[2-k] γ) τ‖ = ‖E_f(γ•τ)‖`; the cusp-`∞` bound of
  `eichler_cusp_holo` (uniform in `Re`, for `Im ≥ B`) transfers verbatim.
* **`γ₁₀ ≠ 0` (`γ • ∞` a finite cusp) — the isolated residual** `eichler_slashSL_bdd_finite`
  (sub-ticket **EICH-3a-i**; see its docstring for the precise gap and why it is mathlib-absent).
  This is the genuine cusp-holomorphy content of reply.md §1.3 (8): the slash is the `∞`-Eichler
  integral of the *conjugate* cusp form `f ∣[k] γ` (cusp width `h ≠ 1`) plus a period polynomial,
  needing the width-`h` conjugate `q`-expansion machinery (or slashed Bol + a Laurent argument). -/
private theorem eichler_bdd_at_cusp (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hk : 2 ≤ k)
    (hf : periodMap' N k hk f = 0) (γ : SL(2, ℤ)) :
    UpperHalfPlane.IsBoundedAtImInfty
      (((eichlerIntegral f) ∘ ((↑) : ℍ → ℂ)) ∣[2 - k] γ) := by
  by_cases hc : (γ 1 0 : ℝ) = 0
  · -- **The `γ • ∞ = ∞` case (lower-left entry `c = 0`).**  Here `γ` is upper-triangular, so
    -- `denom γ τ = γ₁₁ = ±1` (norm `1`) and `Im (γ • τ) = Im τ` (the action is a real translation
    -- composed with `±1`), hence `‖(E_f∘↑ ∣[2-k] γ) τ‖ = ‖E_f(γ•τ)‖` and the bound from
    -- `eichler_cusp_holo` (uniform in `Re`, for `Im ≥ B`) transfers verbatim.
    obtain ⟨M, B, hMB⟩ := UpperHalfPlane.isBoundedAtImInfty_iff.mp (eichler_cusp_holo f hk hf)
    rw [UpperHalfPlane.isBoundedAtImInfty_iff]
    refine ⟨M, B, fun τ hτ => ?_⟩
    -- `det γ = 1` over `ℤ`, hence `γ₀₀·γ₁₁ = 1` (using `γ₁₀ = 0`), so `γ₁₁ = ±1` and `(γ₁₁)² = 1`.
    have hcZ : (γ 1 0 : ℤ) = 0 := by exact_mod_cast hc
    have hdetZ : (γ 0 0 : ℤ) * (γ 1 1) - (γ 0 1) * (γ 1 0) = 1 := by
      have := γ.2; rwa [Matrix.det_fin_two] at this
    have hd2 : (γ 1 1 : ℝ) ^ 2 = 1 := by
      have hprod : (γ 0 0 : ℤ) * (γ 1 1) = 1 := by
        rw [hcZ, mul_zero, sub_zero] at hdetZ; exact hdetZ
      have h11 : (γ 1 1 : ℤ) = 1 ∨ (γ 1 1 : ℤ) = -1 :=
        (Int.eq_one_or_neg_one_of_mul_eq_one' hprod).imp (·.2) (·.2)
      rcases h11 with h11 | h11 <;>
        · have hcast : (γ 1 1 : ℝ) = ((γ 1 1 : ℤ) : ℝ) := by norm_cast
          rw [hcast, h11]; norm_num
    have hd1 : ‖(γ 1 1 : ℝ)‖ = 1 := by
      rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs, hd2, Real.sqrt_one]
    -- The slash denominator is `denom (toGL (γ.map castℝ)) τ`, equal to `↑(γ₁₁)` (since `γ₁₀ = 0`).
    have hden : UpperHalfPlane.denom
        (toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) τ
        = ((γ 1 1 : ℝ) : ℂ) := by
      rw [UpperHalfPlane.denom]
      have h10 : ((toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) 1 0 : ℂ)
          = ((γ 1 0 : ℝ) : ℂ) := by norm_cast
      have h11 : ((toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) 1 1 : ℂ)
          = ((γ 1 1 : ℝ) : ℂ) := by norm_cast
      rw [h10, h11, hc]; push_cast; ring
    -- `Im (γ • τ) = Im τ` (the denominator has `normSq = 1`).
    have hnsq : Complex.normSq
        (UpperHalfPlane.denom
          (toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) τ) = 1 := by
      rw [hden, Complex.normSq_ofReal, ← pow_two, hd2]
    have himeq : ((γ : SL(2, ℤ)) • τ).im = τ.im := by
      rw [ModularGroup.im_smul_eq_div_normSq, hnsq, div_one]
    -- Unfold the slash and bound.
    rw [ModularForm.SL_slash_apply, Function.comp_apply, norm_mul]
    have hnden : ‖UpperHalfPlane.denom
        (toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) τ ^ (-(2 - k))‖ = 1 := by
      rw [norm_zpow, hden, Complex.norm_real, hd1, one_zpow]
    rw [hnden, mul_one]
    -- `‖E_f(γ•τ)‖ ≤ M` from `eichler_cusp_holo`, since `Im (γ•τ) = Im τ ≥ B`.
    have := hMB ((γ : SL(2, ℤ)) • τ) (by rw [himeq]; exact hτ)
    rwa [Function.comp_apply] at this
  · -- **The `γ • ∞ ≠ ∞` (finite-cusp, `c ≠ 0`) case** — the genuine residual EICH-3a-i.
    exact eichler_slashSL_bdd_finite f hk hf γ hc

/-! ## `G4` — weight-`(2-k)` packaging and the `Δ^n` weight-0 vanishing -/

/-- **G4a — package `E_f` as a `ModularForm Γ (2-k)`** (reply.md §1.4; the flagged architecture
gap).
Built from `eichler_slash_invariant` (L7, the `slash_action_eq'` field),
`differentiableOn_eichlerIntegral`
(G1c, the `holo'` field), and `eichler_bdd_at_cusp` (G3b/EICH-3a, the `bdd_at_cusps'` field,
reduced to
the all-`γ` `IsBoundedAtImInfty` shadow via `Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z` +
`OnePoint.isBoundedAt_iff_forall_SL2Z`).  The weight is `2-k`, which is `≤ 0` for `k ≥ 2` — a
genuine
negative-weight modular form, **not** a `CuspForm`.

TYPE-LEVEL NOTE (flagged G4a architecture gap — RESOLVED at the type level): `ModularForm Γ w` is
defined for **any** `w : ℤ`, so `ModularForm ((Gamma1 N).map (mapGL ℝ)) (2 - k)` type-checks for
`2-k ≤ 0`.  The `ℍ → ℂ` carrier is the restriction `(eichlerIntegral f) ∘ ((↑) : ℍ → ℂ)`, consistent
with `eichler_slash_invariant` / `differentiableOn_eichlerIntegral`.  This `def` is now fully
assembled
(no `sorry` in the `def` itself); its only deep input is the `bdd_at_cusps'` field, which
delegates to
the lone residual `eichler_bdd_at_cusp` (EICH-3a). -/
def eichlerModularForm (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hk : 2 ≤ k)
    (hf : periodMap' N k hk f = 0) : ModularForm ((Gamma1 N).map (mapGL ℝ)) (2 - k) where
  toFun := (eichlerIntegral f) ∘ ((↑) : ℍ → ℂ)
  slash_action_eq' g hg := by
    rw [Subgroup.mem_map] at hg
    obtain ⟨δ, hδ, rfl⟩ := hg
    rw [show (Matrix.SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ) = (δ : GL (Fin 2) ℝ) from rfl,
      ← ModularForm.SL_slash]
    exact eichler_slash_invariant f hk hf ⟨δ, hδ⟩
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine (differentiableOn_eichlerIntegral f).congr (fun z hz => ?_)
    simp only [SlashInvariantForm.coe_mk, Function.comp_apply,
      UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    exact eichler_bdd_at_cusp f hk hf γ

/-- **L9 — `E_f = 0`** (reply.md §1.4).  `E_f^{12} · Δ^n` (`n = k-2`) has weight `12(2-k)+12n = 0`,
is holomorphic on `ℍ`, and vanishes at a cusp (because `Δ` does), hence is a weight-0 form on the
compact modular curve ⟹ constant (mathlib `ModularForm.eq_const_of_weight_zero`) ⟹ `0`; since
`Δ ≠ 0` on `ℍ` (mathlib `ModularForm.discriminant_ne_zero`), `E_f = 0`. -/
theorem eichler_eq_zero (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hk : 2 ≤ k)
    (hf : periodMap' N k hk f = 0) :
    eichlerIntegral f = 0 := by
  -- The carrier of the packaged modular form is `E_f ∘ ↑`, definitionally.
  have hmf : (eichlerModularForm f hk hf : ℍ → ℂ) = (eichlerIntegral f) ∘ ((↑) : ℍ → ℂ) := rfl
  -- Step 1: the packaged weight-`(2-k)` modular form `E_f` is the zero form.
  have hg0 : (eichlerModularForm f hk hf : ℍ → ℂ) = 0 := by
    rcases lt_or_eq_of_le hk with hk2 | hk2
    · -- `k > 2`: weight `2 - k < 0`, so `E_f = 0` by `isZero_of_neg_weight`.
      have hzero : eichlerModularForm f hk hf = 0 :=
        ModularForm.isZero_of_neg_weight (by omega) _
      rw [hzero, ModularForm.coe_zero]
    · -- `k = 2`: weight `2 - k = 0`, so `E_f` is constant; vanishing at `∞` forces the
      -- constant `0`.
      have hw : 2 - k = 0 := by omega
      obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero
        (ModularForm.mcast hw (eichlerModularForm f hk hf))
      rw [ModularForm.coe_mcast] at hc
      -- `E_f → 0` at `i∞`, so the constant `c = 0`.
      have hzc : c = 0 := by
        have hz := eichler_isZeroAtImInfty f
        rw [← hmf, hc] at hz
        exact tendsto_nhds_unique tendsto_const_nhds hz
      rw [hc, hzc]; rfl
  -- Step 2: `hg0` says `E_f z = 0` for every `z ∈ ℍ`; package as a statement on `ℂ`.
  have hzero_upper : ∀ z : ℂ, 0 < z.im → eichlerIntegral f z = 0 := by
    intro z hz
    have hzz := congr_fun (hmf ▸ hg0) (⟨z, hz⟩ : ℍ)
    simpa only [Pi.zero_apply, Function.comp_apply, UpperHalfPlane.coe_mk] using hzz
  -- Step 3: extend to all of `ℂ` via vanishing of every Fourier coefficient.
  -- The `q`-expansion of `E_f` (as a modular form) has coefficients `eichlerCoeff f m` by
  -- uniqueness; since the form is `0`, every coefficient vanishes.
  have hHasSum : ∀ τ : ℍ, HasSum
      (fun m : ℕ ↦ eichlerCoeff f m • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m)
      ((eichlerModularForm f hk hf) τ) := by
    intro τ
    have hτ : 0 < (τ : ℂ).im := τ.2
    -- summability of the Eichler series at `τ` (radius of convergence `≥ 1`).
    set ρ : ℝ := Real.exp (-(2 * π * (τ : ℂ).im)) with hρdef
    have hρ0 : 0 < ρ := Real.exp_pos _
    have hρ1 : ρ < 1 := by
      rw [hρdef]; exact Real.exp_lt_one_iff.mpr (by have := Real.pi_pos; nlinarith)
    have hcoeff_bd : ∀ m : ℕ,
        ‖eichlerCoeff f m‖ ≤ ‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ := by
      intro m
      rw [eichlerCoeff, norm_div, norm_pow, Complex.norm_natCast]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rcases Nat.eq_zero_or_pos (k - 1).toNat with he | he
        · simp [he]
        · rw [Nat.cast_zero, zero_pow he.ne', div_zero]; exact norm_nonneg _
      · rw [div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg ((UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m),
          one_le_pow₀ (by exact_mod_cast hm : (1 : ℝ) ≤ (m : ℝ)) (n := (k - 1).toNat)]
    have hqnorm : ‖Function.Periodic.qParam (1 : ℝ) (τ : ℂ)‖ = ρ := by
      rw [Function.Periodic.norm_qParam, hρdef]; congr 1; ring
    have hsummable : Summable
        (fun m : ℕ ↦ eichlerCoeff f m • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m) := by
      have hbd : Summable
          (fun m : ℕ ↦ ‖(UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m‖ * ρ ^ m) := by
        have := summable_norm_coeff_mul_pow_geom f 0 hρ0.le hρ1
        simpa using this
      refine Summable.of_norm (hbd.of_nonneg_of_le (fun m ↦ norm_nonneg _) (fun m ↦ ?_))
      rw [smul_eq_mul, norm_mul, norm_pow, hqnorm]
      exact mul_le_mul (hcoeff_bd m) (le_refl _) (by positivity) (norm_nonneg _)
    -- the value: `E_f τ = Σ eichlerCoeff f m • q^m`.
    have hval : (eichlerModularForm f hk hf) τ =
        ∑' m : ℕ, eichlerCoeff f m • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ m := by
      show (eichlerIntegral f) (τ : ℂ) = _
      rw [eichlerIntegral, eichlerQSeries]
      refine tsum_congr (fun m ↦ ?_)
      rw [pow_zero, mul_one, smul_eq_mul]
      congr 1
      rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
      push_cast; ring_nf
    rw [hval]
    exact hsummable.hasSum
  -- Uniqueness of `q`-expansion coefficients: `eichlerCoeff f m = (qExpansion 1 E_f).coeff m`.
  have hcoeff_zero : ∀ m : ℕ, eichlerCoeff f m = 0 := by
    intro m
    rw [ModularFormClass.qExpansion_coeff_unique (Γ := (Gamma1 N).map (mapGL ℝ))
      (k := 2 - k) (f := eichlerModularForm f hk hf) one_pos one_mem_strictPeriods_Gamma1
      hHasSum m]
    -- the form is `0`, so its `cuspFunction`, hence its `q`-expansion, vanishes.
    have hcusp0 : UpperHalfPlane.cuspFunction (1 : ℝ) (eichlerModularForm f hk hf) = 0 := by
      have hcomp : (eichlerModularForm f hk hf : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex
          = (0 : ℂ → ℂ) := by rw [hg0]; rfl
      rw [UpperHalfPlane.cuspFunction, hcomp, Function.Periodic.cuspFunction]
      ext q
      rcases eq_or_ne q 0 with rfl | hq
      · simp only [Function.update_self, Pi.zero_apply]
        exact (tendsto_const_nhds (x := (0 : ℂ)) (f := 𝓝[≠] (0 : ℂ))).limUnder_eq
      · rw [Function.update_of_ne hq]; rfl
    rw [UpperHalfPlane.qExpansion_coeff, hcusp0]
    simp
  funext z
  simp only [Pi.zero_apply, eichlerIntegral, eichlerQSeries, hcoeff_zero, zero_mul, tsum_zero]

/-! ## `R`/`FINAL` — injectivity of the period map via the Eichler integral -/

/-- **R — Injectivity of `periodMap'` (`k ≥ 2`) via the Eichler integral** (reply.md §1, the top
result; the Eichler/`Δ^n`-route replacement for the Stokes route `periodMap'_injective`).  A
`ℂ`-linear map is injective iff `ker` is trivial: from `ι(f)=0` we get `E_f = 0` (`eichler_eq_zero`,
L9), and then `f = D^{k-1} E_f = 0` (`bol_iterated_eichler`, G1b/FINAL). -/
theorem periodMap'_injective_eichler (hk : 2 ≤ k) :
    Function.Injective (periodMap' (N := N) (k := k) hk) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  -- `ι(f)=0 ⟹ E_f = 0`, hence the iterated derivative of `E_f` vanishes, hence `f = D^{k-1} E_f =
  -- 0`.
  have hE : eichlerIntegral f = 0 := eichler_eq_zero f hk hf
  ext τ
  -- `f τ = ((2πi)⁻¹)^{k-1} · D^{k-1} E_f (τ) = ((2πi)⁻¹)^{k-1} · D^{k-1} 0 (τ) = 0`.
  have hbol := bol_iterated_eichler f hk (z := (τ : ℂ)) (by simpa using τ.2)
  rw [hE] at hbol
  simp only [Pi.zero_def, iteratedDeriv_fun_const_zero, mul_zero,
    UpperHalfPlane.ofComplex_apply] at hbol
  simpa using hbol.symm

end HeckeRing.GL2.ModularSymbols

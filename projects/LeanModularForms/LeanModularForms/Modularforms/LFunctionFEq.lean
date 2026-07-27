/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.Modularforms.LFunction
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Functional equation and analytic continuation of the L-function of a level-1 cusp form

For a weight-`k` cusp form `f` on `SL₂(ℤ)` (so `f ∣[k] S = f`, where `S = [[0,-1],[1,0]]`),
the **completed L-function** is
`Λ(s, f) = (2π)^{-s} · Γ(s) · L(s, f)`, where `L(s, f) = ModularForms.lSeries f s`.

This file proves Hecke's theorem for level `1`, via mathlib's abstract Mellin
functional-equation framework (`StrongFEPair`, in
`Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean`; template
`Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean`):

* `ModularForms.mellin_resToImagAxis_eq` (the **bridge**): on the half-plane
  `k/2 + 1 < Re s`, the Mellin transform of `t ↦ f(it)` equals the completed
  L-function `(2π)^{-s} · Γ(s) · L(s, f)`.
* `ModularForms.lcompletedSeries_functional_equation`: the **functional equation**
  `Λ(k - s, f) = i^k · Λ(s, f)`.
* `ModularForms.lSeries_hasEntireExtension`: **analytic continuation**: `L(·, f)` extends
  to an entire function on `ℂ`.

## Mathematical outline

The restriction `g(t) := f(it)` (`Function.resToImagAxis`, set to `0` for `t ≤ 0`) satisfies,
for a level-1 cusp form:

* `g(1/t) = (i^k · t^k) · g(t)` for `t > 0` — the **self-duality** functional equation, obtained
  from `ResToImagAxis.SlashActionS` together with `f ∣[k] S = f`.  In the language of
  `WeakFEPair`, this is `h_feq` with FE-weight `k` and root number `ε = i^k`.
* `g` decays faster than any power of `t` as `t → ∞` (and, by the functional equation, also as
  `t → 0⁺`): the `hf_top`/`hg_top` fields.  This uses the exponential decay
  `CuspFormClass.exp_decay_atImInfty`.

Hence `(g, g)` form a `StrongFEPair ℂ` with `f₀ = g₀ = 0`.  Its completed L-function
`Λ = mellin g` is entire (`StrongFEPair.differentiable_Λ`) and satisfies
`Λ(k - s) = i^k · Λ(s)` (`StrongFEPair.functional_equation`, using `symm.Λ = Λ` because
`f = g`).

The bridge `mellin g s = (2π)^{-s} · Γ(s) · L(s, f)` comes from `hasSum_mellin`
applied to `aₙ = lCoeff f n`, `pₙ = 2π·n`: the imaginary-axis `q`-expansion
`f(it) = Σ_n aₙ e^{-2π n t}` (from `UpperHalfPlane.hasSum_qExpansion` at `τ = i·t`, width `1`,
where `𝕢 1 (it) = e^{-2π t}`) is the `hF` hypothesis, and `a₀ = lCoeff f 0 = 0`
(cusp form) handles the `p₀ = 0` term.

Since `1/Γ` is entire, the continuation of `L(·, f)` is `s ↦ (2π)^s · Λ(s) / Γ(s)`, an entire
function agreeing with `L(s, f)` on the convergence half-plane.

## References

* Hecke, *Über die Bestimmung Dirichletscher Reihen durch ihre Funktionalgleichung*.
* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.10.
* [Miy] Miyake, *Modular Forms*, Thm 4.3.5.
-/

open Filter Topology Asymptotics Set MeasureTheory Complex UpperHalfPlane
open scoped Real ModularForm MatrixGroups

namespace ModularForms

variable {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)}
variable {F : Type*} [FunLike F ℍ ℂ]

/-- The point `i · t ∈ ℍ` for `t > 0`. -/
private def imLift {t : ℝ} (ht : 0 < t) : ℍ :=
  ⟨Complex.I * (t : ℂ), by simp [ht]⟩

private lemma imLift_im {t : ℝ} (ht : 0 < t) : (imLift ht).im = t := by
  simp [imLift, UpperHalfPlane.im]

/-- `f.resToImagAxis t = f (i·t)` for `t > 0`. -/
private lemma resToImagAxis_eq [ModularFormClass F Γ k] (f : F) {t : ℝ} (ht : 0 < t) :
    (f : ℍ → ℂ).resToImagAxis t = f (imLift ht) := by
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte, imLift]

/-- The local parameter at the cusp, evaluated on the imaginary axis with width `1`:
`𝕢 1 (i·t) = exp(-2π t)`. -/
private lemma qParam_one_imLift {t : ℝ} (ht : 0 < t) :
    Function.Periodic.qParam 1 (imLift ht) = Real.exp (-2 * π * t) := by
  rw [Function.Periodic.qParam]
  have hcoe : ((imLift ht : ℍ) : ℂ) = Complex.I * (t : ℂ) := rfl
  have : (2 * ↑π * Complex.I * ((imLift ht : ℍ) : ℂ) / ↑(1 : ℝ)) = ((-2 * π * t : ℝ) : ℂ) := by
    rw [hcoe]
    push_cast
    rw [show 2 * (↑π : ℂ) * Complex.I * (Complex.I * ↑t) =
        2 * ↑π * (Complex.I * Complex.I) * ↑t by ring, Complex.I_mul_I]
    ring
  rw [this, Complex.ofReal_exp]

/-- **Imaginary-axis `q`-expansion.**  For a weight-`k` modular form of strict width `1` at `∞`,
`f(it) = Σ_n aₙ · e^{-2π n t}` for `t > 0`, where `aₙ = lCoeff f n`.  Written in the shape
required by `hasSum_mellin` with `pₙ = 2π·n`. -/
private lemma hasSum_resToImagAxis [ModularFormClass F Γ k] (f : F)
    (hw : Γ.strictWidthInfty = 1) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ lCoeff f n * Real.exp (-(2 * π * n) * t))
      ((f : ℍ → ℂ).resToImagAxis t) := by
  have hΓ : Γ.strictWidthInfty ∈ Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  have hone : (1 : ℝ) ∈ Γ.strictPeriods := hw ▸ hΓ
  have _fact : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hone⟩
  have key := UpperHalfPlane.hasSum_qExpansion (f := (f : ℍ → ℂ)) (h := 1) one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f hone) (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f) (imLift ht)
  rw [resToImagAxis_eq f ht]
  refine key.congr_fun fun n ↦ ?_
  rw [lCoeff_apply, hw, qParam_one_imLift ht, smul_eq_mul, ← Complex.ofReal_pow,
    ← Real.exp_nat_mul, Complex.ofReal_exp, ← Complex.ofReal_exp,
    show (-(2 * π * (n : ℝ)) * t) = (n : ℝ) * (-2 * π * t) from by ring]

/-! ### The completed L-function and the Mellin bridge -/

/-- The **completed L-function** `Λ(s, f) = (2π)^{-s} · Γ(s) · L(s, f)` of a modular form. -/
noncomputable def lcompletedSeries [ModularFormClass F Γ k] (f : F) (s : ℂ) : ℂ :=
  (2 * ↑Real.pi) ^ (-s) * Complex.Gamma s * lSeries f s

@[simp]
lemma lcompletedSeries_apply [ModularFormClass F Γ k] (f : F) (s : ℂ) :
    lcompletedSeries f s = (2 * ↑Real.pi) ^ (-s) * Complex.Gamma s * lSeries f s := rfl

/-- The summability hypothesis of `hasSum_mellin` (with `pₙ = 2π·n`) follows from
`LSeriesSummable (lCoeff f) s`. -/
private lemma summable_norm_div_of_lSeriesSummable [ModularFormClass F Γ k] (f : F) {s : ℂ}
    (hs0 : s.re ≠ 0) (hsum : LSeriesSummable (lCoeff f) s) :
    Summable fun n : ℕ ↦ ‖lCoeff f n‖ / (2 * π * n) ^ s.re := by
  rw [LSeriesSummable, ← summable_norm_iff] at hsum
  -- `‖lCoeff f n‖ / (2π·n)^{s.re} = (2π)^{-s.re} · ‖term (lCoeff f) s n‖`
  have hpi : (0 : ℝ) < 2 * π := by positivity
  refine (hsum.mul_left ((2 * π) ^ (-s.re))).congr (fun n ↦ ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, norm_zero, mul_zero, Nat.cast_zero, mul_zero,
      Real.zero_rpow hs0, div_zero]
  · rw [LSeries.norm_term_eq, if_neg hn,
      show (2 * π * (n : ℝ)) = (2 * π) * (n : ℝ) from by ring,
      Real.mul_rpow hpi.le (Nat.cast_nonneg n), Real.rpow_neg hpi.le]
    field_simp

/-- Per-term identity: `Γ(s) · aₙ / (2πn)^s = (2π)^{-s} · Γ(s) · term(a) s n` (for `s ≠ 0`). -/
private lemma gamma_term_eq (a : ℕ → ℂ) {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    Complex.Gamma s * a n / (2 * ↑π * ↑n) ^ s
      = (2 * ↑π) ^ (-s) * Complex.Gamma s * LSeries.term a s n := by
  have h2pi : (0 : ℝ) ≤ 2 * π := by positivity
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, mul_zero, Nat.cast_zero, mul_zero,
      Complex.zero_cpow hs, div_zero]
  · rw [LSeries.term_of_ne_zero hn,
      show (2 * (↑π : ℂ) * (n : ℂ)) = ((2 * π : ℝ) : ℂ) * ((n : ℝ) : ℂ) from by push_cast; ring,
      Complex.mul_cpow_ofReal_nonneg h2pi (Nat.cast_nonneg n), Complex.cpow_neg,
      show (((2 * π : ℝ) : ℂ)) = 2 * (↑π : ℂ) from by push_cast; ring,
      show (((n : ℝ) : ℂ)) = (n : ℂ) from by push_cast; ring]
    rw [mul_comm (((2 : ℂ) * ↑π) ^ s), ← div_div, mul_div_assoc, mul_div_assoc,
      div_eq_mul_inv (a n / (n : ℂ) ^ s)]
    ring

/-- **The Mellin bridge.**  For a weight-`k` cusp form `f` of strict width `1` at `∞` on an
arithmetic subgroup, with `0 < k`, the Mellin transform of `t ↦ f(it)` on the half-plane
`k/2 + 1 < Re s` equals the completed L-function `(2π)^{-s} · Γ(s) · L(s, f)`. -/
theorem mellin_resToImagAxis_eq [Γ.IsArithmetic] [CuspFormClass F Γ k] (f : F)
    (hw : Γ.strictWidthInfty = 1) (hk : 0 < k) {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    mellin ((f : ℍ → ℂ).resToImagAxis) s = lcompletedSeries f s := by
  have hk2 : (0 : ℝ) < (k : ℝ) / 2 + 1 := by positivity
  have hs0re : 0 < s.re := hk2.trans hs
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs0re
  have hΓper : Γ.strictWidthInfty ∈ Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  -- Apply the Mellin–Dirichlet bridge with `aₙ = lCoeff f n`, `pₙ = 2π·n`.
  have hcusp_sum : LSeriesSummable (lCoeff f) s := lSeriesSummable_of_cuspForm f hs
  have hp : ∀ n : ℕ, lCoeff f n = 0 ∨ 0 < 2 * π * (n : ℝ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · exact Or.inl (by
        rw [lCoeff_apply, hw]
        exact CuspFormClass.qExpansion_coeff_zero f one_pos (hw ▸ hΓper))
    · exact Or.inr (by positivity)
  have key := hasSum_mellin (a := lCoeff f) (p := fun n ↦ 2 * π * (n : ℝ))
    (F := (f : ℍ → ℂ).resToImagAxis) hp hs0re
    (fun t ht ↦ hasSum_resToImagAxis f hw ht)
    (summable_norm_div_of_lSeriesSummable f hs0re.ne' hcusp_sum)
  -- Sum and rewrite each term.
  rw [← key.tsum_eq, lcompletedSeries_apply, lSeries_apply, LSeries, ← tsum_mul_left]
  refine tsum_congr (fun n ↦ ?_)
  rw [show ((2 * π * (n : ℝ) : ℝ) : ℂ) = 2 * (↑π : ℂ) * (n : ℂ) from by push_cast; ring]
  exact gamma_term_eq (lCoeff f) hs0 n

/-! ### Rapid decay of the imaginary-axis restriction -/

/-- The total lift `t ↦ ofComplex (i·t) : ℝ → ℍ`, which agrees with `imLift` for `t > 0`. -/
private noncomputable def imAxisLift (t : ℝ) : ℍ := UpperHalfPlane.ofComplex (Complex.I * (t : ℂ))

private lemma imAxisLift_coe {t : ℝ} (ht : 0 < t) :
    ((imAxisLift t : ℍ) : ℂ) = Complex.I * (t : ℂ) := by
  rw [imAxisLift,
    UpperHalfPlane.ofComplex_apply_of_im_pos (z := Complex.I * (t : ℂ)) (by simp [ht])]

private lemma imAxisLift_im_of_pos {t : ℝ} (ht : 0 < t) : (imAxisLift t).im = t := by
  rw [← UpperHalfPlane.coe_im, imAxisLift_coe ht, Complex.mul_im, Complex.I_im, Complex.I_re,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

private lemma resToImagAxis_eq_comp [ModularFormClass F Γ k] (f : F) {t : ℝ} (ht : 0 < t) :
    (f : ℍ → ℂ).resToImagAxis t = f (imAxisLift t) := by
  rw [resToImagAxis_eq f ht]
  congr 1
  apply UpperHalfPlane.ext
  rw [imAxisLift_coe ht]
  rfl

/-- The lift tends to `atImInfty` as `t → ∞`. -/
private lemma tendsto_imAxisLift : Tendsto imAxisLift atTop atImInfty := by
  refine UpperHalfPlane.tendsto_comap_im_ofComplex.comp ?_
  rw [tendsto_comap_iff]
  apply tendsto_id.congr
  intro t
  simp [Function.comp_apply, Complex.mul_im]

/-- **Exponential decay of `f(it)` on the imaginary axis.**  For a weight-`k` cusp form of strict
width `1` at `∞`, `resToImagAxis f =O[atTop] (fun t => exp(-2π t))`. -/
private lemma isBigO_resToImagAxis_exp [Γ.IsArithmetic] [CuspFormClass F Γ k] (f : F)
    (hw : Γ.strictWidthInfty = 1) :
    (fun t : ℝ ↦ (f : ℍ → ℂ).resToImagAxis t) =O[atTop] fun t : ℝ ↦ Real.exp (-2 * π * t) := by
  have hΓper : (1 : ℝ) ∈ Γ.strictPeriods := hw ▸ Γ.strictWidthInfty_mem_strictPeriods
  -- exp decay on ℍ, pulled back along the lift
  have hdecay : (⇑f) =O[atImInfty] fun τ : ℍ ↦ Real.exp (-2 * π * τ.im / 1) :=
    CuspFormClass.exp_decay_atImInfty (h := 1) f one_pos hΓper
  have hcomp := hdecay.comp_tendsto tendsto_imAxisLift
  -- the composite `(f ∘ imAxisLift)` agrees with `resToImagAxis f` for large `t`
  refine (hcomp.congr' ?_ ?_)
  · filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Function.comp_apply, ← resToImagAxis_eq_comp f ht]
  · filter_upwards [eventually_gt_atTop 0] with t ht
    rw [Function.comp_apply, imAxisLift_im_of_pos ht]
    norm_num

/-- **Rapid decay of the imaginary-axis restriction.**  For a weight-`k` cusp form of strict width
`1`, `resToImagAxis f =O[atTop] (·^r)` for every real exponent `r` (because `f(it)` decays
exponentially, faster than any power).  This is the `hf_top`/`hg_top` field of a `StrongFEPair`. -/
private lemma isBigO_resToImagAxis_rpow [Γ.IsArithmetic] [CuspFormClass F Γ k] (f : F)
    (hw : Γ.strictWidthInfty = 1) (r : ℝ) :
    (fun t : ℝ ↦ (f : ℍ → ℂ).resToImagAxis t) =O[atTop] fun t : ℝ ↦ t ^ r := by
  refine (isBigO_resToImagAxis_exp f hw).trans ?_
  have hlit : (fun t : ℝ ↦ Real.exp (-(2 * π) * t)) =o[atTop] fun t : ℝ ↦ t ^ r :=
    isLittleO_exp_neg_mul_rpow_atTop (by positivity) r
  refine (hlit.isBigO).congr_left (fun t ↦ ?_)
  congr 1
  ring

/-! ### The self-duality functional equation -/

open ModularForm in
/-- **Self-duality of the imaginary-axis restriction at level `1`.**  If `f ∣[k] S = f`
(`S = [[0,-1],[1,0]]`), then `f(i/t) = (i^k · t^k) · f(it)` for `t > 0`.  This is the `h_feq`
field of the `StrongFEPair`, with FE-weight `k` and root number `ε = i^k`. -/
private lemma resToImagAxis_feq (f : F) (hS : (f : ℍ → ℂ) ∣[k] ModularGroup.S = f)
    {t : ℝ} (ht : 0 < t) :
    (f : ℍ → ℂ).resToImagAxis (1 / t)
      = (Complex.I ^ k * ((t ^ (k : ℝ) : ℝ) : ℂ)) • (f : ℍ → ℂ).resToImagAxis t := by
  -- `SlashActionS`: `(f ∣ S)(it) = I^(-k) · (↑t)^(-k) · f(i/t)`; substitute `f ∣ S = f`.
  have hslash := ResToImagAxis.SlashActionS (f : ℍ → ℂ) k ht
  rw [hS] at hslash
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [smul_eq_mul,
    show ((t ^ (k : ℝ) : ℝ) : ℂ) = (t : ℂ) ^ k by rw [← Complex.ofReal_zpow, Real.rpow_intCast]]
  -- `f(it) = I^(-k) (↑t)^(-k) f(i/t)`  ⟹  `f(i/t) = (I^(-k) (↑t)^(-k))⁻¹ f(it) = I^k (↑t)^k f(it)`
  have key : (f : ℍ → ℂ).resToImagAxis (1 / t)
      = (Complex.I ^ (-k) * (t : ℂ) ^ (-k))⁻¹ * (f : ℍ → ℂ).resToImagAxis t := by
    rw [hslash, ← mul_assoc, inv_mul_cancel₀, one_mul]
    exact mul_ne_zero (zpow_ne_zero _ Complex.I_ne_zero) (zpow_ne_zero _ ht0)
  rw [key]
  simp only [mul_inv, ← zpow_neg, neg_neg]

/-! ### Local integrability -/

/-- `resToImagAxis f` is locally integrable on `Ioi 0` (it is continuous there, being
real-differentiable at each `t > 0`). -/
private lemma locallyIntegrableOn_resToImagAxis [ModularFormClass F Γ k] (f : F) :
    LocallyIntegrableOn ((f : ℍ → ℂ).resToImagAxis) (Ioi 0) := by
  refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
  refine fun t (ht : 0 < t) ↦ ?_
  exact (ResToImagAxis.Differentiable (f : ℍ → ℂ) (ModularFormClass.holo f) t ht)
    |>.continuousAt.continuousWithinAt

/-! ### The `StrongFEPair` -/

open ModularForm in
/-- The `StrongFEPair` attached to a level-`1` weight-`k` cusp form `f` (with `f ∣[k] S = f`,
`Γ.strictWidthInfty = 1`, `0 < k`).  Both functions are `t ↦ f(it)`, the FE-weight is `k`, and the
root number is `ε = i^k`. -/
noncomputable def feqPair [Γ.IsArithmetic] [CuspFormClass F Γ k] (f : F)
    (hw : Γ.strictWidthInfty = 1) (hk : 0 < k)
    (hS : (f : ℍ → ℂ) ∣[k] ModularGroup.S = f) : WeakFEPair ℂ where
  f := (f : ℍ → ℂ).resToImagAxis
  g := (f : ℍ → ℂ).resToImagAxis
  k := (k : ℝ)
  ε := Complex.I ^ k
  f₀ := 0
  g₀ := 0
  hf_int := locallyIntegrableOn_resToImagAxis f
  hg_int := locallyIntegrableOn_resToImagAxis f
  hk := by exact_mod_cast hk
  hε := zpow_ne_zero _ Complex.I_ne_zero
  h_feq := fun x hx ↦ resToImagAxis_feq f hS (mem_Ioi.mp hx)
  hf_top := fun r ↦ by simpa using isBigO_resToImagAxis_rpow f hw r
  hg_top := fun r ↦ by simpa using isBigO_resToImagAxis_rpow f hw r

open ModularForm in
/-- The `feqPair` of a cusp form is a strong FE-pair: its constant terms vanish. -/
theorem isStrongFEPair_feqPair [Γ.IsArithmetic] [CuspFormClass F Γ k] (f : F)
    (hw : Γ.strictWidthInfty = 1) (hk : 0 < k)
    (hS : (f : ℍ → ℂ) ∣[k] ModularGroup.S = f) :
    IsStrongFEPair (feqPair f hw hk hS) where
  hf₀ := rfl
  hg₀ := rfl

/-! ### The completed L-function, its functional equation and entirety

The **completed L-function** is the entire function `Λ(s, f) = mellin (t ↦ f(it)) s`.  On the
absolute-convergence half-plane it coincides with `(2π)^{-s} · Γ(s) · L(s, f)` (the bridge
`mellin_resToImagAxis_eq`), but unlike the naive Dirichlet product it is entire and satisfies the
functional equation everywhere. -/

variable [Γ.IsArithmetic] [CuspFormClass F Γ k]

/-- The **completed L-function** of a level-`1` weight-`k` cusp form: the entire function
`Λ(s, f) = mellin (t ↦ f(it)) s`. -/
noncomputable def lcompleted (f : F) (s : ℂ) : ℂ := mellin ((f : ℍ → ℂ).resToImagAxis) s

lemma lcompleted_apply (f : F) (s : ℂ) :
    lcompleted f s = mellin ((f : ℍ → ℂ).resToImagAxis) s := rfl

/-- On the half-plane `k/2 + 1 < Re s`, the completed L-function equals the naive completed
Dirichlet product `(2π)^{-s} · Γ(s) · L(s, f)`. -/
theorem lcompleted_eq_lcompletedSeries (f : F) (hw : Γ.strictWidthInfty = 1) (hk : 0 < k)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    lcompleted f s = lcompletedSeries f s :=
  mellin_resToImagAxis_eq f hw hk hs

/-- **The completed L-function is entire.** -/
theorem differentiable_lcompleted (f : F) (hw : Γ.strictWidthInfty = 1) (hk : 0 < k)
    (hS : (f : ℍ → ℂ) ∣[k] ModularGroup.S = f) :
    Differentiable ℂ (lcompleted f) := by
  have hP := isStrongFEPair_feqPair f hw hk hS
  have hΛ : lcompleted f = (feqPair f hw hk hS).Λ :=
    funext fun s ↦ (hP.hasMellin s).2
  rw [hΛ]
  exact hP.differentiable_Λ

open ModularForm in
/-- **The functional equation of the completed L-function.**  For a level-`1` weight-`k` cusp form
`f` (so `f ∣[k] S = f`), `Λ(k - s, f) = i^k · Λ(s, f)`. -/
theorem lcompleted_functional_equation (f : F) (hw : Γ.strictWidthInfty = 1) (hk : 0 < k)
    (hS : (f : ℍ → ℂ) ∣[k] ModularGroup.S = f) (s : ℂ) :
    lcompleted f ((k : ℂ) - s) = Complex.I ^ k * lcompleted f s := by
  have hP := isStrongFEPair_feqPair f hw hk hS
  set P := feqPair f hw hk hS with hP_def
  have hfe := P.functional_equation s
  -- `P.Λ (k - s) = ε • P.symm.Λ s`; here `P.symm.Λ = P.Λ = lcompleted f` (since `f = g`)
  -- and `ε = I^k`.
  rw [smul_eq_mul] at hfe
  have hΛ : ∀ t, lcompleted f t = P.Λ t := fun t ↦ (hP.hasMellin t).2
  have hΛsymm : ∀ t, lcompleted f t = P.symm.Λ t := fun t ↦ (hP.symm.hasMellin t).2
  have hPk : (P.k : ℂ) = (k : ℂ) := by
    have hk_eq : P.k = (k : ℝ) := by rw [hP_def]; rfl
    rw [hk_eq]; push_cast; ring
  have hcast : ((k : ℂ) - s) = (↑P.k - s) := by rw [hPk]
  rw [hΛ ((k : ℂ) - s), hcast, hfe, ← hΛsymm s]
  rfl

/-- **Hecke's functional equation, naive form.**  On the half-plane `k/2 + 1 < Re s`, the
completed Dirichlet product `(2π)^{-s} · Γ(s) · L(s, f)` at `s` equals (after multiplying by
`i^k`) the analytic continuation of the completed L-function at the reflected point `k - s`:
`i^k · lcompletedSeries f s = Λ(k - s, f)`.  (The naive product cannot satisfy the functional
equation at both `s` and `k - s` simultaneously, since their real parts sum to `k`; the genuine
statement is `lcompleted_functional_equation`, on the entire completed function.) -/
theorem lcompletedSeries_functional_equation (f : F) (hw : Γ.strictWidthInfty = 1) (hk : 0 < k)
    (hS : (f : ℍ → ℂ) ∣[k] ModularGroup.S = f) {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    Complex.I ^ k * lcompletedSeries f s = lcompleted f ((k : ℂ) - s) := by
  rw [lcompleted_functional_equation f hw hk hS s, lcompleted_eq_lcompletedSeries f hw hk hs]

/-! ### Analytic continuation of `L(·, f)` -/

/-- The half-plane `{s | x < Re s}` (with `x : EReal`) is preconnected.

Stated for `EReal` so it applies directly to `{s | abscissaOfAbsConv a < Re s}`, the natural domain
of an `LSeries`.  Not modular-form-specific: it is the identity-theorem input shared by every
analytic-continuation argument here, so it is public and reused at level `N`
(`LFunctionFEqN.lean`). -/
lemma isPreconnected_re_gt_EReal (x : EReal) :
    IsPreconnected {z : ℂ | x < (z.re : EReal)} := by
  induction x using EReal.rec with
  | bot =>
    have : {z : ℂ | (⊥ : EReal) < (z.re : EReal)} = Set.univ := by
      ext z; simp [bot_lt_iff_ne_bot]
    rw [this]; exact isPreconnected_univ
  | coe r =>
    have : {z : ℂ | (↑r : EReal) < (z.re : EReal)} = {z : ℂ | r < z.re} := by
      ext z; simp [EReal.coe_lt_coe_iff]
    rw [this]; exact (convex_halfSpace_re_gt r).isPreconnected
  | top =>
    have : {z : ℂ | (⊤ : EReal) < (z.re : EReal)} = (∅ : Set ℂ) := by
      ext z; simp
    rw [this]; exact isPreconnected_empty

/-- The entire witness for the continuation of `L(·, f)`:
`G(s) = (2π)^s · Λ(s, f) / Γ(s)`, where `Λ = lcompleted`. -/
private noncomputable def lSeriesExtension (f : F) (s : ℂ) : ℂ :=
  (2 * ↑π) ^ s * lcompleted f s * (Complex.Gamma s)⁻¹

/-- The witness is entire (`1/Γ` is entire, `(2π)^s` is entire, `Λ` is entire). -/
private lemma differentiable_lSeriesExtension (f : F) (hw : Γ.strictWidthInfty = 1) (hk : 0 < k)
    (hS : (f : ℍ → ℂ) ∣[k] ModularGroup.S = f) :
    Differentiable ℂ (lSeriesExtension f) := by
  have hpi : NeZero (2 * (↑π : ℂ)) := ⟨by simp [Real.pi_ne_zero]⟩
  exact (((differentiable_const_cpow_of_neZero (2 * (↑π : ℂ))).mul
    (differentiable_lcompleted f hw hk hS)).mul
    Complex.differentiable_one_div_Gamma)

/-- On the half-plane `k/2 + 1 < Re s`, the witness equals `L(s, f)`. -/
private lemma lSeriesExtension_eq_of_re_gt (f : F) (hw : Γ.strictWidthInfty = 1) (hk : 0 < k)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    lSeriesExtension f s = LSeries (lCoeff f) s := by
  have hs0re : 0 < s.re := lt_trans (by positivity) hs
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero (fun m ↦ by
    intro h; rw [h] at hs0re; simp at hs0re; nlinarith [hs0re, Nat.cast_nonneg (α := ℝ) m])
  have hpi : (2 * (↑π : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [lSeriesExtension, lcompleted_eq_lcompletedSeries f hw hk hs, lcompletedSeries_apply,
    lSeries_apply]
  rw [show (2 * (↑π : ℂ)) ^ s * ((2 * ↑π) ^ (-s) * Complex.Gamma s * LSeries (lCoeff f) s)
      * (Complex.Gamma s)⁻¹
      = ((2 * ↑π) ^ s * (2 * ↑π) ^ (-s)) * (Complex.Gamma s * (Complex.Gamma s)⁻¹)
        * LSeries (lCoeff f) s from by ring]
  rw [← Complex.cpow_add _ _ hpi, add_neg_cancel, Complex.cpow_zero, mul_inv_cancel₀ hΓ,
    one_mul, one_mul]

/-- **Analytic continuation of the L-function.**  For a level-`1` weight-`k` cusp form `f`
(so `f ∣[k] S = f`, `Γ.strictWidthInfty = 1`, `0 < k`), the L-function `L(·, f)` extends to an
entire function on `ℂ`, namely `s ↦ (2π)^s · Λ(s, f) / Γ(s)` (where `Λ = lcompleted`). -/
theorem lSeries_hasEntireExtension (f : F) (hw : Γ.strictWidthInfty = 1) (hk : 0 < k)
    (hS : (f : ℍ → ℂ) ∣[k] ModularGroup.S = f) :
    LSeries.HasEntireExtension (lCoeff f) := by
  refine ⟨lSeriesExtension f, differentiable_lSeriesExtension f hw hk hS, ?_⟩
  -- agreement on the convergence half-plane via the identity theorem
  set U : Set ℂ := {z : ℂ | LSeries.abscissaOfAbsConv (lCoeff f) < (z.re : EReal)} with hU
  -- the witness and `LSeries` are both analytic on `U`
  have hGan : AnalyticOnNhd ℂ (lSeriesExtension f) U :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (differentiable_lSeriesExtension f hw hk hS)).mono (Set.subset_univ _)
  have hLan : AnalyticOnNhd ℂ (LSeries (lCoeff f)) U := LSeries_analyticOnNhd (lCoeff f)
  -- a base point with large real part, lying in `U`
  set z₀ : ℂ := (((k : ℝ) / 2 + 2 : ℝ) : ℂ) with hz₀
  have habs : LSeries.abscissaOfAbsConv (lCoeff f) ≤ (((k : ℝ) / 2 : ℝ) : EReal) + 1 :=
    abscissaOfAbsConv_lCoeff_le_cuspForm f
  have hz₀U : z₀ ∈ U := by
    rw [hU, Set.mem_setOf_eq, hz₀, Complex.ofReal_re]
    refine lt_of_le_of_lt habs ?_
    rw [show (1 : EReal) = ((1 : ℝ) : EReal) from rfl, ← EReal.coe_add, EReal.coe_lt_coe_iff]
    linarith
  -- on the open set `{k/2+1 < re}` (a nbhd of `z₀`), the two functions agree
  have hnhd : lSeriesExtension f =ᶠ[𝓝 z₀] LSeries (lCoeff f) := by
    have hopen : IsOpen {z : ℂ | (k : ℝ) / 2 + 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hz₀mem : z₀ ∈ {z : ℂ | (k : ℝ) / 2 + 1 < z.re} := by
      rw [Set.mem_setOf_eq, hz₀, Complex.ofReal_re]; linarith
    filter_upwards [hopen.mem_nhds hz₀mem] with z hz
    exact lSeriesExtension_eq_of_re_gt f hw hk hz
  -- conclude via the identity principle on the preconnected half-plane `U`
  intro s hs
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hGan hLan
    (isPreconnected_re_gt_EReal _) hz₀U hnhd hs

/-! ### Specialisation to the concrete level-`1` carrier `SL₂(ℤ)`

The natural carrier of a level-`1` form is the image `Γ := (Γ₁(1)).map (mapGL ℝ)` of `SL₂(ℤ)` in
`GL₂(ℝ)`.  It has strict width `1` at `∞` (`strictWidthInfty_Gamma1_mapGL`) and is arithmetic, and
`S ∈ SL₂(ℤ)` so every modular form for `Γ` is automatically `S`-invariant.  Hence Hecke's theorem
applies unconditionally to any `CuspForm ((Γ₁(1)).map (mapGL ℝ)) k` of weight `k > 0`. -/

section Level1

open Matrix CongruenceSubgroup ModularGroup Matrix.SpecialLinearGroup
open scoped ModularForm

variable {k : ℤ}

/-- For a modular form on `Γ := (Γ₁(1)).map (mapGL ℝ)` (the image of `SL₂(ℤ)`), the slash by
`S = [[0,-1],[1,0]]` is the identity (since `S ∈ SL₂(ℤ)` maps into `Γ`). -/
theorem slash_S_eq_self_level1 {F : Type*} [FunLike F ℍ ℂ]
    [SlashInvariantFormClass F ((Gamma1 1).map (mapGL ℝ)) k] (f : F) :
    (f : ℍ → ℂ) ∣[k] ModularGroup.S = f := by
  have hSmem : (ModularGroup.S : SL(2, ℤ)) ∈ Gamma1 1 := by
    rw [CongruenceSubgroup.Gamma1_mem]; refine ⟨?_, ?_, ?_⟩ <;> exact Subsingleton.elim _ _
  have hmap : ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ (Gamma1 1).map (mapGL ℝ) :=
    Subgroup.mem_map_of_mem _ hSmem
  rw [ModularForm.SL_slash]
  exact SlashInvariantFormClass.slash_action_eq f _ hmap

variable {F : Type*} [FunLike F ℍ ℂ] [CuspFormClass F ((Gamma1 1).map (mapGL ℝ)) k]

/-- **Hecke functional equation, level `1`.**  For a weight-`k > 0` cusp form `f` on `SL₂(ℤ)`, the
completed L-function satisfies `Λ(k - s, f) = i^k · Λ(s, f)`. -/
theorem lcompleted_functional_equation_level1 (f : F) (hk : 0 < k) (s : ℂ) :
    lcompleted f ((k : ℂ) - s) = Complex.I ^ k * lcompleted f s :=
  lcompleted_functional_equation f (strictWidthInfty_Gamma1_mapGL 1) hk
    (slash_S_eq_self_level1 f) s

/-- **The completed L-function of a level-`1` cusp form is entire.** -/
theorem differentiable_lcompleted_level1 (f : F) (hk : 0 < k) :
    Differentiable ℂ (lcompleted f) :=
  differentiable_lcompleted f (strictWidthInfty_Gamma1_mapGL 1) hk (slash_S_eq_self_level1 f)

/-- **Analytic continuation, level `1`.**  The L-function of a weight-`k > 0` cusp form on
`SL₂(ℤ)` extends to an entire function on `ℂ`. -/
theorem lSeries_hasEntireExtension_level1 (f : F) (hk : 0 < k) :
    LSeries.HasEntireExtension (lCoeff f) :=
  lSeries_hasEntireExtension f (strictWidthInfty_Gamma1_mapGL 1) hk (slash_S_eq_self_level1 f)

end Level1

end ModularForms

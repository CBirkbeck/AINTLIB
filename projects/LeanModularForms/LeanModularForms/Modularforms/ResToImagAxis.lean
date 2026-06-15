/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.NumberTheory.ModularForms.QExpansion

public import LeanModularForms.Modularforms.AtImInfty
public import LeanModularForms.Modularforms.SlashActionAuxil

@[expose] public section

/-!
# Restriction of functions on the upper half-plane to the imaginary axis

For a function `F : ℍ → ℂ` we define its restriction `ResToImagAxis F : ℝ → ℂ` to the
positive imaginary axis by `t ↦ F (I * t)` for `t > 0` and `0` otherwise. We then study
the algebraic structure (realness, positivity, eventual positivity) of this restriction
under addition, multiplication and scaling, and establish polynomial-decay results that
apply in particular to cusp forms.

## Main definitions

* `ResToImagAxis F`: the restriction `t ↦ F (I * t)`.
* `ResToImagAxis.Real F`: `F` is real-valued on the positive imaginary axis.
* `ResToImagAxis.Pos F`: `F` is real-valued and positive on the positive imaginary axis.
* `ResToImagAxis.EventuallyPos F`: `F` is real-valued and positive for large enough `t > 0`.

## Main results

* `ResToImagAxis.Differentiable`: `F.resToImagAxis` is real-differentiable at `t > 0`
  whenever `F` is `MDiff`.
* `ResToImagAxis.SlashActionS`: behaviour of the restriction under the slash action of `S`.
* `cuspForm_rpow_mul_resToImagAxis_tendsto_zero`: any cusp form of level `Γ(n)` satisfies
  `t ^ s * f (it) → 0` as `t → ∞`.
* `isBigO_atImInfty_of_fourier_shift`: a Fourier expansion starting at index `n₀ > 0`
  gives an `O(exp(-2π n₀ · im z))` bound at `atImInfty`.
-/

open UpperHalfPlane hiding I

open Real Complex ContinuousMap Matrix CongruenceSubgroup ModularGroup Filter Asymptotics

open scoped Interval Real Topology Manifold ModularForm MatrixGroups

/--
Restrict a function `F : ℍ → ℂ` to the positive imaginary axis, i.e. `t ↦ F (I * t)`.
If $t \le 0$, then `F (I * t)` is not defined, and we return `0` in that case.
-/
noncomputable def ResToImagAxis (F : ℍ → ℂ) : ℝ → ℂ :=
  fun t ↦ if ht : 0 < t then F ⟨(I * t), by simp [ht]⟩ else 0

namespace Function

/-- Dot notation alias for `ResToImagAxis`. -/
noncomputable def resToImagAxis (F : ℍ → ℂ) : ℝ → ℂ := ResToImagAxis F

@[simp] lemma resToImagAxis_eq_resToImagAxis (F : ℍ → ℂ) :
    F.resToImagAxis = ResToImagAxis F := rfl

@[simp] lemma resToImagAxis_apply (F : ℍ → ℂ) (t : ℝ) :
    F.resToImagAxis t = ResToImagAxis F t := rfl

end Function

/--
Function $F : \mathbb{H} \to \mathbb{C}$ whose restriction to the imaginary axis is real-valued,
i.e. imaginary part is zero.
-/
@[fun_prop]
noncomputable def ResToImagAxis.Real (F : ℍ → ℂ) : Prop :=
  ∀ t : ℝ, 0 < t → (F.resToImagAxis t).im = 0

/--
Function $F : \mathbb{H} \to \mathbb{C}$ is real and positive on the imaginary axis.
-/
@[fun_prop]
noncomputable def ResToImagAxis.Pos (F : ℍ → ℂ) : Prop :=
  ResToImagAxis.Real F ∧ ∀ t : ℝ, 0 < t → 0 < (F.resToImagAxis t).re

/--
Function $F : \mathbb{H} \to \mathbb{C}$ whose restriction to the imaginary axis is eventually
positive, i.e. there exists $t_0 > 0$ such that for all $t \ge t_0$, $F(it)$ is real and positive.
-/
@[fun_prop]
noncomputable def ResToImagAxis.EventuallyPos (F : ℍ → ℂ) : Prop :=
  ResToImagAxis.Real F ∧ ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, t₀ ≤ t → 0 < (F.resToImagAxis t).re

/-- The restriction `F.resToImagAxis` is real-differentiable at every `t > 0` whenever `F`
is manifold-differentiable on `ℍ`. -/
@[fun_prop]
theorem ResToImagAxis.Differentiable (F : ℍ → ℂ) (hF : MDiff F) (t : ℝ)
    (ht : 0 < t) : DifferentiableAt ℝ F.resToImagAxis t := by
  rw [Function.resToImagAxis_eq_resToImagAxis]
  have hmdiff := hF ⟨Complex.I * t, by norm_num [Complex.I_re, ht]⟩
  rw [mdifferentiableAt_iff] at hmdiff
  have h_diff : DifferentiableAt ℝ (fun t : ℝ ↦ F (ofComplex (Complex.I * t))) t := by
    convert hmdiff.restrictScalars ℝ |> DifferentiableAt.comp t <|
      DifferentiableAt.const_mul ofRealCLM.differentiableAt _ using 1
    all_goals try rfl
  refine h_diff.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds ht] with t ht
  simp_all only [ResToImagAxis, ↓reduceDIte]
  rw [ofComplex_apply_of_im_pos]

/-- Restriction and slash action under `S`: `(F ∣[k] S) (it) = (it) ^ (-k) * F (it)`. -/
theorem ResToImagAxis.SlashActionS (F : ℍ → ℂ) (k : ℤ) {t : ℝ} (ht : 0 < t) :
    (F ∣[k] S).resToImagAxis t = Complex.I ^ (-k) * t ^ (-k) * F.resToImagAxis (1 / t) := by
  set z : ℍ := ⟨I * t, by simp [ht]⟩ with hzdef
  set z' : ℍ := ⟨I * (1 / t : ℝ), by simpa [one_div_pos.2 ht]⟩ with hz'def
  have h : mk (-z)⁻¹ z.im_inv_neg_coe_pos = z' :=
    UpperHalfPlane.ext (by simp [hzdef, hz'def, mul_comm])
  have hslash : (F ∣[k] S) z = I ^ (-k) * t ^ (-k) * F z' := by
    rw [modular_slash_S_apply, h]
    simp [hzdef, mul_zpow I (t : ℂ) (-k), mul_comm (F z')]
  simpa [ResToImagAxis, ht, hz'def] using hslash

/-- The constant function `t ↦ c` with `c : ℝ` is real-valued on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Real.const (c : ℝ) : ResToImagAxis.Real (fun _ ↦ c) := by
  intro t ht
  simp only [Function.resToImagAxis_apply, ResToImagAxis, ht, ↓reduceDIte, ofReal_im]

/-- The zero function is real-valued on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Real.zero : ResToImagAxis.Real (fun _ ↦ 0) := ResToImagAxis.Real.const 0

/-- The constant function `1` is real-valued on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Real.one : ResToImagAxis.Real (fun _ ↦ 1) := ResToImagAxis.Real.const 1

/-- Negation preserves realness on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Real.neg {F : ℍ → ℂ} (hF : ResToImagAxis.Real F) :
    ResToImagAxis.Real (-F) := by
  intro t ht
  have hFreal := hF t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal
  simp [ResToImagAxis, ht, hFreal]

/-- Addition preserves realness on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Real.add {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F + G) := by
  intro t ht
  have hFreal := hF t ht
  have hGreal := hG t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal hGreal
  simp [ResToImagAxis, ht, hFreal, hGreal]

/-- Subtraction preserves realness on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Real.sub {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F - G) := by
  simpa [sub_eq_add_neg] using ResToImagAxis.Real.add hF hG.neg

/-- Multiplication preserves realness on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Real.mul {F G : ℍ → ℂ} (hF : ResToImagAxis.Real F)
    (hG : ResToImagAxis.Real G) : ResToImagAxis.Real (F * G) := by
  intro t ht
  have hFreal := hF t ht
  have hGreal := hG t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal hGreal
  simp [ResToImagAxis, ht, hFreal, hGreal]

/-- Real scalar multiplication preserves realness on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Real.smul {F : ℍ → ℂ} {c : ℝ} (hF : ResToImagAxis.Real F) :
    ResToImagAxis.Real (c • F) := by
  intro t ht
  have hFreal := hF t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal
  simp [ResToImagAxis, ht, hFreal]

/-- Natural powers preserve realness on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Real.pow {F : ℍ → ℂ} (hF : ResToImagAxis.Real F) (n : ℕ) :
    ResToImagAxis.Real (F ^ n) := by
  induction n with
  | zero => exact ResToImagAxis.Real.one
  | succ n hn => exact hn.mul hF

/-- A positive real constant function is positive on the imaginary axis. -/
theorem ResToImagAxis.Pos.const (c : ℝ) (hc : 0 < c) : ResToImagAxis.Pos (fun _ ↦ c) :=
  ⟨ResToImagAxis.Real.const c, fun t ht ↦ by simp [ResToImagAxis, ht, hc]⟩

/-- The constant function `1` is positive on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Pos.one : ResToImagAxis.Pos (fun _ ↦ 1) :=
  ResToImagAxis.Pos.const 1 one_pos

/-- Addition preserves positivity on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Pos.add {F G : ℍ → ℂ} (hF : ResToImagAxis.Pos F)
    (hG : ResToImagAxis.Pos G) : ResToImagAxis.Pos (F + G) := by
  refine ⟨Real.add hF.1 hG.1, fun t ht ↦ ?_⟩
  have hFpos := hF.2 t ht
  have hGpos := hG.2 t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFpos hGpos
  simp [ResToImagAxis, ht, add_pos hFpos hGpos]

/-- Multiplication preserves positivity on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Pos.mul {F G : ℍ → ℂ} (hF : ResToImagAxis.Pos F)
    (hG : ResToImagAxis.Pos G) : ResToImagAxis.Pos (F * G) := by
  refine ⟨Real.mul hF.1 hG.1, fun t ht ↦ ?_⟩
  have hFreal := hF.1 t ht
  have hGreal := hG.1 t ht
  have hFpos := hF.2 t ht
  have hGpos := hG.2 t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFreal hGreal hFpos hGpos
  simp [ResToImagAxis, ht, hFreal, hGreal, mul_pos hFpos hGpos]

/-- Positive scalar multiplication preserves positivity on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Pos.smul {F : ℍ → ℂ} {c : ℝ} (hF : ResToImagAxis.Pos F)
    (hc : 0 < c) : ResToImagAxis.Pos (c • F) := by
  refine ⟨Real.smul hF.1, fun t ht ↦ ?_⟩
  have hFpos := hF.2 t ht
  simp only [Function.resToImagAxis, ResToImagAxis, ht, ↓reduceDIte] at hFpos
  simp [ResToImagAxis, ht, mul_pos hc hFpos]

/-- Natural powers preserve positivity on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.Pos.pow {F : ℍ → ℂ} (hF : ResToImagAxis.Pos F) (n : ℕ) :
    ResToImagAxis.Pos (F ^ n) := by
  induction n with
  | zero => exact ResToImagAxis.Pos.one
  | succ n hn => exact hn.mul hF

/-- Positivity on the imaginary axis implies eventual positivity (with threshold `1`). -/
@[fun_prop]
theorem ResToImagAxis.EventuallyPos.from_pos {F : ℍ → ℂ} (hF : ResToImagAxis.Pos F) :
    ResToImagAxis.EventuallyPos F :=
  ⟨hF.1, 1, by positivity, fun t ht ↦ hF.2 t (by linarith)⟩

/-- The constant function `1` is eventually positive on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.EventuallyPos.one :
    ResToImagAxis.EventuallyPos (fun _ ↦ 1) :=
  ResToImagAxis.EventuallyPos.from_pos ResToImagAxis.Pos.one

/-- A positive real constant function is eventually positive on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.EventuallyPos.const (c : ℝ) (hc : 0 < c) :
    ResToImagAxis.EventuallyPos (fun _ ↦ c) :=
  ResToImagAxis.EventuallyPos.from_pos (ResToImagAxis.Pos.const c hc)

/-- Addition preserves eventual positivity on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.EventuallyPos.add {F G : ℍ → ℂ}
    (hF : ResToImagAxis.EventuallyPos F) (hG : ResToImagAxis.EventuallyPos G) :
    ResToImagAxis.EventuallyPos (F + G) := by
  refine ⟨ResToImagAxis.Real.add hF.1 hG.1, ?_⟩
  obtain ⟨tF, hF0, hFpos⟩ := hF.2
  obtain ⟨tG, hG0, hGpos⟩ := hG.2
  refine ⟨max tF tG, by positivity, fun t ht ↦ ?_⟩
  have htpos : 0 < t := hF0.trans_le ((le_max_left tF tG).trans ht)
  have hFpos_t := hFpos t ((le_max_left tF tG).trans ht)
  have hGpos_t := hGpos t ((le_max_right tF tG).trans ht)
  simp only [Function.resToImagAxis_apply, ResToImagAxis, htpos] at hFpos_t hGpos_t
  simp only [Function.resToImagAxis_apply, ResToImagAxis, htpos]
  exact add_pos hFpos_t hGpos_t

/-- Multiplication preserves eventual positivity on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.EventuallyPos.mul {F G : ℍ → ℂ}
    (hF : ResToImagAxis.EventuallyPos F) (hG : ResToImagAxis.EventuallyPos G) :
    ResToImagAxis.EventuallyPos (F * G) := by
  refine ⟨ResToImagAxis.Real.mul hF.1 hG.1, ?_⟩
  obtain ⟨tF, hF0, hFpos⟩ := hF.2
  obtain ⟨tG, hG0, hGpos⟩ := hG.2
  refine ⟨max tF tG, by positivity, fun t ht ↦ ?_⟩
  have htpos : 0 < t := hF0.trans_le ((le_max_left tF tG).trans ht)
  have hFreal_t := hF.1 t htpos
  have hGreal_t := hG.1 t htpos
  have hFpos_t := hFpos t ((le_max_left tF tG).trans ht)
  have hGpos_t := hGpos t ((le_max_right tF tG).trans ht)
  simp only [Function.resToImagAxis, ResToImagAxis, htpos] at hFpos_t hGpos_t
  simp only [Function.resToImagAxis, ResToImagAxis, htpos, ↓reduceDIte] at hFreal_t hGreal_t
  simp only [Function.resToImagAxis_apply, ResToImagAxis, htpos, ↓reduceDIte, Pi.mul_apply, mul_re,
    hFreal_t, hGreal_t, mul_zero, sub_zero]
  exact mul_pos hFpos_t hGpos_t

/-- Natural powers preserve eventual positivity on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.EventuallyPos.pow {F : ℍ → ℂ}
    (hF : ResToImagAxis.EventuallyPos F) (n : ℕ) :
    ResToImagAxis.EventuallyPos (F ^ n) := by
  induction n with
  | zero => exact ResToImagAxis.EventuallyPos.one
  | succ n hn => exact hn.mul hF

/-- Positive scalar multiplication preserves eventual positivity on the imaginary axis. -/
@[fun_prop]
theorem ResToImagAxis.EventuallyPos.smul {F : ℍ → ℂ} {c : ℝ} (hF : ResToImagAxis.EventuallyPos F)
    (hc : 0 < c) : ResToImagAxis.EventuallyPos (c • F) := by
  refine ⟨ResToImagAxis.Real.smul hF.1, ?_⟩
  obtain ⟨t₀, hF0, hFpos⟩ := hF.2
  refine ⟨t₀, hF0, fun t ht ↦ ?_⟩
  have htpos : 0 < t := hF0.trans_le ht
  have hFpos_t := hFpos t ht
  simp only [Function.resToImagAxis, ResToImagAxis, htpos, ↓reduceDIte] at hFpos_t
  simp [ResToImagAxis, htpos, mul_pos hc hFpos_t]


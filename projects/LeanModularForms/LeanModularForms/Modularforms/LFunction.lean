/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Cusps

import LeanModularForms.Modularforms.ResToImagAxis

/-!
# L-functions of modular forms

For a weight-`k` modular form `f` with `q`-expansion `f(τ) = Σ_{n≥0} aₙ qⁿ`,
the **L-function** is the Dirichlet series `L(s, f) = Σ_{n ≥ 1} aₙ · n^{-s}`,
built on mathlib's `LSeries` / `LSeriesSummable` infrastructure.

All results are stated at full generality for a `ModularFormClass F Γ k` (resp. `CuspFormClass`)
with `Γ : Subgroup (GL (Fin 2) ℝ)` and `k : ℤ`; the convergence statements additionally assume
`Γ.IsArithmetic`, which is what mathlib's coefficient-growth bounds require.

## Main definitions

* `ModularForms.lCoeff f` — the `ℕ → ℂ` coefficient sequence built from the
  `q`-expansion of `f` at the strict width at `∞` of its level.
* `ModularForms.lSeries f` — the associated L-function `fun s ↦ LSeries (lCoeff f) s`.

## Main results

* `ModularForms.abscissaOfAbsConv_lCoeff_le` /
  `ModularForms.abscissaOfAbsConv_lCoeff_le_cuspForm` — Hecke's abscissa bounds
  `≤ k + 1` (modular forms, for `0 ≤ k`) and `≤ k / 2 + 1` (cusp forms), derived from
  `ModularFormClass.qExpansion_isBigO` and `CuspFormClass.qExpansion_isBigO`.
* `ModularForms.lSeriesSummable_of_modularForm` /
  `ModularForms.lSeriesSummable_of_cuspForm` — absolute convergence on the half-planes
  `Re s > k + 1` (modular forms) and `Re s > k / 2 + 1` (cusp forms).
* `ModularForms.lSeries_eq_iff_cuspForm` / `ModularForms.lSeries_eq_zero_iff_cuspForm`
  — injectivity (two cusp forms with equal L-functions are equal) and non-vanishing
  (the L-function vanishes iff the form does) for cusp forms.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.9.
* [Miy] Miyake, *Modular Forms*, Thm 4.5.16.
-/

open Filter LSeries UpperHalfPlane
open scoped UpperHalfPlane

namespace ModularForms

variable {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)}
variable {F : Type*} [FunLike F ℍ ℂ]

/-- The coefficient sequence `n ↦ (q-expansion of f).coeff n`, viewed as `ℕ → ℂ`,
the natural input to mathlib's `LSeries`. -/
noncomputable def lCoeff [ModularFormClass F Γ k] (f : F) : ℕ → ℂ :=
  fun n ↦ (qExpansion Γ.strictWidthInfty f).coeff n

@[simp]
lemma lCoeff_apply [ModularFormClass F Γ k] (f : F) (n : ℕ) :
    lCoeff f n = (qExpansion Γ.strictWidthInfty f).coeff n := rfl

/-- The **L-function** `L(s, f) = Σ_{n ≥ 1} aₙ · n^{-s}` of a modular form, as the Dirichlet
series of its `q`-expansion coefficients `lCoeff f`. -/
noncomputable def lSeries [ModularFormClass F Γ k] (f : F) (s : ℂ) : ℂ :=
  LSeries (lCoeff f) s

@[simp]
lemma lSeries_apply [ModularFormClass F Γ k] (f : F) (s : ℂ) :
    lSeries f s = LSeries (lCoeff f) s := rfl

open CongruenceSubgroup Matrix.SpecialLinearGroup in
/-- **Strict width at infinity of the GL₂(ℝ) image of Γ₁(N) is `1`.** -/
@[simp]
lemma strictWidthInfty_Gamma1_mapGL (N : ℕ) :
    ((Gamma1 N).map (mapGL ℝ)).strictWidthInfty = 1 :=
  CongruenceSubgroup.strictWidthInfty_Gamma1 N

/-- The point `i · t` lies in the upper half-plane when `0 < t`. -/
private lemma imAxis_mem {t : ℝ} (ht : 0 < t) : 0 < (Complex.I * (t : ℂ)).im := by
  rw [Complex.mul_im, Complex.I_im, Complex.I_re,
    Complex.ofReal_re, Complex.ofReal_im]
  simpa using ht

/-- **Modular form on the positive imaginary axis.**

Maps `t > 0` to `f` evaluated at `i · t ∈ ℍ`, and `t ≤ 0` to `0`. -/
noncomputable def imAxis [ModularFormClass F Γ k] (f : F) (t : ℝ) : ℂ :=
  if h : 0 < t then f ⟨Complex.I * (t : ℂ), imAxis_mem h⟩ else 0

@[simp]
lemma imAxis_apply_of_pos [ModularFormClass F Γ k] (f : F) {t : ℝ} (ht : 0 < t) :
    imAxis f t = f ⟨Complex.I * (t : ℂ), imAxis_mem ht⟩ := by
  rw [imAxis, dif_pos ht]

section Convergence

/-! ### Convergence of the L-function

The coefficient bounds of `Mathlib/NumberTheory/ModularForms/Bounds.lean`
(`ModularFormClass.qExpansion_isBigO` and `CuspFormClass.qExpansion_isBigO`) feed
mathlib's abscissa-of-absolute-convergence API to give half-planes of absolute
convergence for `L(s, f)`. -/

open Filter Asymptotics in
/-- **Hecke's abscissa bound.**  For a weight-`k` modular form on an arithmetic subgroup,
the L-series of its `q`-expansion coefficients converges absolutely for `Re s > k + 1`;
equivalently, its abscissa of absolute convergence is at most `k + 1`. -/
theorem abscissaOfAbsConv_lCoeff_le [Γ.IsArithmetic] [ModularFormClass F Γ k] (f : F)
    (hk : 0 ≤ k) :
    LSeries.abscissaOfAbsConv (lCoeff f) ≤ (k : ℝ) + 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_isBigO_rpow ?_
  refine (ModularFormClass.qExpansion_isBigO hk f).congr_right fun n ↦ ?_
  rw [Real.rpow_intCast]

open Filter Asymptotics in
/-- **Hecke's abscissa bound for cusp forms.**  For a weight-`k` cusp form on an arithmetic
subgroup, the L-series of its `q`-expansion coefficients converges absolutely for
`Re s > k / 2 + 1`; equivalently, its abscissa of absolute convergence is at most `k / 2 + 1`. -/
theorem abscissaOfAbsConv_lCoeff_le_cuspForm [Γ.IsArithmetic] [CuspFormClass F Γ k] (f : F) :
    LSeries.abscissaOfAbsConv (lCoeff f) ≤ (((k : ℝ) / 2 : ℝ) : EReal) + 1 :=
  LSeries.abscissaOfAbsConv_le_of_isBigO_rpow (CuspFormClass.qExpansion_isBigO f)

/-- **Absolute convergence of the L-function of a modular form.**  For a weight-`k` modular form
on an arithmetic subgroup, the Dirichlet series `lCoeff f` is `LSeriesSummable` at every `s`
with `k + 1 < Re s`. -/
theorem lSeriesSummable_of_modularForm [Γ.IsArithmetic] [ModularFormClass F Γ k] (f : F)
    (hk : 0 ≤ k) {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    LSeriesSummable (lCoeff f) s :=
  LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
    (abscissaOfAbsConv_lCoeff_le f hk).trans_lt (by exact_mod_cast hs)

/-- **Absolute convergence of the L-function of a cusp form.**  For a weight-`k` cusp form
on an arithmetic subgroup, the Dirichlet series `lCoeff f` is `LSeriesSummable` at every `s`
with `k / 2 + 1 < Re s`. -/
theorem lSeriesSummable_of_cuspForm [Γ.IsArithmetic] [CuspFormClass F Γ k] (f : F)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    LSeriesSummable (lCoeff f) s :=
  LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
    (abscissaOfAbsConv_lCoeff_le_cuspForm f).trans_lt (by exact_mod_cast hs)

/-- The L-series of a cusp form converges somewhere, i.e. its abscissa of absolute
convergence is finite. -/
theorem abscissaOfAbsConv_lCoeff_lt_top_cuspForm [Γ.IsArithmetic] [CuspFormClass F Γ k] (f : F) :
    LSeries.abscissaOfAbsConv (lCoeff f) < ⊤ := by
  refine (abscissaOfAbsConv_lCoeff_le_cuspForm f).trans_lt ?_
  rw [show (1 : EReal) = ((1 : ℝ) : EReal) from rfl, ← EReal.coe_add]
  exact EReal.coe_lt_top _

end Convergence

section Injectivity

/-! ### Injectivity and non-vanishing of cusp-form L-functions

Two cusp forms whose L-functions agree have the same `q`-expansion coefficients (mathlib's
`LSeries_eq_iff_of_abscissaOfAbsConv_lt_top`, using that a cusp-form L-series converges), and a
holomorphic function on `ℍ` is recovered from its `q`-expansion
(`UpperHalfPlane.hasSum_qExpansion`); hence equal L-functions force the forms to be equal. -/

open UpperHalfPlane in
/-- A modular form is recovered from its `q`-expansion coefficients: for an arithmetic subgroup,
if two weight-`k` modular forms have the same `lCoeff`, they are equal as functions on `ℍ`. -/
theorem coe_eq_of_lCoeff_eq [Γ.IsArithmetic] [ModularFormClass F Γ k] {f g : F}
    (hfg : lCoeff f = lCoeff g) : (f : ℍ → ℂ) = g := by
  have hh : 0 < Γ.strictWidthInfty := Γ.strictWidthInfty_pos
  have hΓ : Γ.strictWidthInfty ∈ Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  ext τ
  have hf := hasSum_qExpansion (f := (f : ℍ → ℂ)) hh
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f) τ
  have hg := hasSum_qExpansion (f := (g : ℍ → ℂ)) hh
    (SlashInvariantFormClass.periodic_comp_ofComplex g hΓ) (ModularFormClass.holo g)
    (ModularFormClass.bdd_at_infty g) τ
  exact hf.unique (by simpa only [← lCoeff_apply, hfg] using hg)

/-- **Injectivity of the cusp-form L-function.**  Two weight-`k` cusp forms on an arithmetic
subgroup are equal if and only if their L-functions agree. -/
theorem lSeries_eq_iff_cuspForm [Γ.IsArithmetic] [CuspFormClass F Γ k] (f g : F) :
    lSeries f = lSeries g ↔ f = g := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have hh : 0 < Γ.strictWidthInfty := Γ.strictWidthInfty_pos
  have hΓ : Γ.strictWidthInfty ∈ Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  -- equal L-series force equal coefficients at every `n ≠ 0`; the `n = 0` ones both vanish
  have hcoeff : ∀ n ≠ 0, lCoeff f n = lCoeff g n :=
    (LSeries_eq_iff_of_abscissaOfAbsConv_lt_top (abscissaOfAbsConv_lCoeff_lt_top_cuspForm f)
      (abscissaOfAbsConv_lCoeff_lt_top_cuspForm g)).mp h
  refine DFunLike.coe_injective (coe_eq_of_lCoeff_eq (funext fun n ↦ ?_))
  rcases eq_or_ne n 0 with rfl | hn
  · rw [lCoeff_apply, lCoeff_apply, CuspFormClass.qExpansion_coeff_zero f hh hΓ,
      CuspFormClass.qExpansion_coeff_zero g hh hΓ]
  · exact hcoeff n hn

open UpperHalfPlane in
/-- The `q`-expansion coefficient sequence of a cusp form vanishes identically if and only if the
form does. -/
theorem lCoeff_eq_zero_iff_cuspForm [Γ.IsArithmetic] [CuspFormClass F Γ k] (f : F) :
    lCoeff f = 0 ↔ (f : ℍ → ℂ) = 0 := by
  have hh : 0 < Γ.strictWidthInfty := Γ.strictWidthInfty_pos
  have hΓ : Γ.strictWidthInfty ∈ Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  rw [← UpperHalfPlane.qExpansion_eq_zero_iff hh
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f)]
  rw [PowerSeries.ext_iff]
  simp [funext_iff, lCoeff]

/-- **Non-vanishing of the cusp-form L-function.**  The L-function of a weight-`k` cusp form on
an arithmetic subgroup is identically zero if and only if the form itself is identically zero. -/
theorem lSeries_eq_zero_iff_cuspForm [Γ.IsArithmetic] [CuspFormClass F Γ k] (f : F) :
    lSeries f = 0 ↔ (f : ℍ → ℂ) = 0 := by
  have hh : 0 < Γ.strictWidthInfty := Γ.strictWidthInfty_pos
  have hΓ : Γ.strictWidthInfty ∈ Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  rw [← lCoeff_eq_zero_iff_cuspForm f]
  rw [show (lSeries f : ℂ → ℂ) = LSeries (lCoeff f) from rfl,
    LSeries_eq_zero_iff (by simp [CuspFormClass.qExpansion_coeff_zero f hh hΓ])]
  simp [(abscissaOfAbsConv_lCoeff_lt_top_cuspForm f).ne]

end Injectivity

end ModularForms

namespace LSeries

/-- **Hecke entire-continuation predicate.**  A coefficient sequence
`a : ℕ → ℂ` *has an entire extension* if there exists an entire
function `F : ℂ → ℂ` agreeing with `LSeries a` on the
absolute-convergence half-plane `abscissaOfAbsConv a < s.re`.

When it exists, the entire extension is unique on `ℂ`
(`HasEntireExtension.unique`). -/
def HasEntireExtension (a : ℕ → ℂ) : Prop :=
  ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
    ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → F s = LSeries a s

namespace HasEntireExtension

variable {a : ℕ → ℂ}

/-- **Uniqueness of entire extension.**  Two entire functions
`F, G : ℂ → ℂ` that both extend `LSeries a` on the absolute-
convergence half-plane are equal everywhere on `ℂ`. -/
theorem unique {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (h_finite : abscissaOfAbsConv a < ⊤)
    (hFa : ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → F s = LSeries a s)
    (hGa : ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → G s = LSeries a s) :
    F = G := by
  obtain ⟨σ, hσ_abs, _⟩ := EReal.exists_between_coe_real h_finite
  let U : Set ℂ := {s : ℂ | (σ : ℝ) < s.re}
  have hU_sub : ∀ s ∈ U, abscissaOfAbsConv a < (s.re : EReal) := fun s hs ↦
    lt_of_lt_of_le hσ_abs (by exact_mod_cast (hs : (σ : ℝ) < s.re).le)
  obtain ⟨z₀, hz₀⟩ : U.Nonempty := ⟨((σ + 1 : ℝ) : ℂ), by
    show (σ : ℝ) < ((σ + 1 : ℝ) : ℂ).re; rw [Complex.ofReal_re]; linarith⟩
  exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr hF).eq_of_eventuallyEq
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hG)
    (Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨U, (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀,
        fun s hs ↦ (hFa (hU_sub s hs)).trans (hGa (hU_sub s hs)).symm⟩)

end HasEntireExtension

/-- **Quotient pole sufficient condition.**

If `num, den : 𝕜 → 𝕜` are meromorphic at `x`, both with finite
(`≠ ⊤`) order, and `meromorphicOrderAt num x < meromorphicOrderAt den x`,
then `fun s ↦ num s / den s` has **negative** meromorphic order at `x`
— i.e., the quotient has a pole at `x`. -/
theorem _root_.meromorphicOrderAt_div_neg_of_orderAt_lt
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {num den : 𝕜 → 𝕜} {x : 𝕜}
    (h_num : MeromorphicAt num x) (h_den : MeromorphicAt den x)
    (h_num_finite : meromorphicOrderAt num x ≠ ⊤)
    (h_den_finite : meromorphicOrderAt den x ≠ ⊤)
    (h_lt : meromorphicOrderAt num x < meromorphicOrderAt den x) :
    meromorphicOrderAt (num / den) x < 0 := by
  rw [div_eq_mul_inv, meromorphicOrderAt_mul h_num h_den.inv, meromorphicOrderAt_inv]
  lift meromorphicOrderAt num x to ℤ using h_num_finite with n hn
  lift meromorphicOrderAt den x to ℤ using h_den_finite with m hm
  rw [WithTop.coe_lt_coe] at h_lt
  rw [show -((m : ℤ) : WithTop ℤ) = (((-m) : ℤ) : WithTop ℤ) from rfl,
      ← WithTop.coe_add, show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl,
      WithTop.coe_lt_coe]
  lia

/-- **Meromorphic extension with a pole — analytic obligation Prop.**

A coefficient sequence `a : ℕ → ℂ` *has a meromorphic extension with a pole*
if there exist a witness function `g : ℂ → ℂ` and a witness pole point
`s₀ : ℂ` such that:

* `g` is meromorphic at `s₀`;
* `g` has *negative* meromorphic order at `s₀` (a pole);
* every entire extension `F : ℂ → ℂ` of `LSeries a` coincides with
  `g` on a punctured neighbourhood of `s₀`. -/
def HasMeromorphicExtensionWithPole (a : ℕ → ℂ) : Prop :=
  ∃ (g : ℂ → ℂ) (s₀ : ℂ),
    MeromorphicAt g s₀ ∧
    meromorphicOrderAt g s₀ < 0 ∧
    ∀ F : ℂ → ℂ, Differentiable ℂ F →
      (∀ {s : ℂ}, abscissaOfAbsConv a < s.re → F s = LSeries a s) →
      F =ᶠ[nhdsWithin s₀ {s₀}ᶜ] g

/-- **Coprime-stripped coefficient sequence at a Finset of primes.**

The S-stripped version of `f : ℕ → ℂ`: zeroed at every positive
integer `n` divisible by some prime in `S`, equal to `f n` elsewhere. -/
def coprimeStrip (S : Finset Nat.Primes) (f : ℕ → ℂ) : ℕ → ℂ :=
  fun n ↦ if ∀ p ∈ S, ¬ (p : ℕ) ∣ n then f n else 0

/-- **`coprimeStrip S f 1 = f 1`** (since no prime divides `1`). -/
@[simp]
lemma coprimeStrip_one (S : Finset Nat.Primes) (f : ℕ → ℂ) :
    coprimeStrip S f 1 = f 1 := by
  simp only [coprimeStrip]
  rw [if_pos (fun p _ h_dvd ↦ p.prop.one_lt.ne' (Nat.dvd_one.mp h_dvd))]

end LSeries

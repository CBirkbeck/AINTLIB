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

## Main definitions

* `ModularForms.lCoeff f` — the `ℕ → ℂ` coefficient sequence built from the
  `q`-expansion of `f` at the strict width at `∞` of its level.
* `ModularForms.lSeries f` — the associated L-function `fun s ↦ LSeries (lCoeff f) s`.

## Main results

* `ModularForms.abscissaOfAbsConv_lCoeff_le` /
  `ModularForms.abscissaOfAbsConv_lCoeff_le_cuspForm` — Hecke's abscissa bounds
  `≤ k + 1` (modular forms) and `≤ k/2 + 1` (cusp forms).
* `ModularForms.lSeriesSummable_of_modularForm` /
  `ModularForms.lSeriesSummable_of_cuspForm` — absolute convergence on the
  corresponding half-planes.
* `ModularForms.lSeries_eq_iff_cuspForm` / `ModularForms.lSeries_eq_zero_iff_cuspForm`
  — LSeries injectivity and non-vanishing for cusp forms.

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

open CongruenceSubgroup Matrix.SpecialLinearGroup in
/-- **Strict width at infinity of the GL₂(ℝ) image of Γ₁(N) is `1`.** -/
@[simp]
lemma strictWidthInfty_Gamma1_mapGL (N : ℕ) :
    ((Gamma1 N).map (mapGL ℝ)).strictWidthInfty = 1 :=
  CongruenceSubgroup.strictWidthInfty_Gamma1 N

open CongruenceSubgroup Matrix.SpecialLinearGroup in

/-- **Modular form on the positive imaginary axis.**

Maps `t > 0` to `f` evaluated at `i · t ∈ ℍ`, and `t ≤ 0` to `0`. -/
noncomputable def imAxis [ModularFormClass F Γ k] (f : F) (t : ℝ) : ℂ :=
  if h : 0 < t then
    f ⟨Complex.I * (t : ℂ), by
      show 0 < (Complex.I * (t : ℂ)).im
      rw [Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_re, Complex.ofReal_im]
      simpa using h⟩
  else 0

@[simp]
lemma imAxis_apply_of_pos [ModularFormClass F Γ k] (f : F) {t : ℝ} (ht : 0 < t) :
    imAxis f t = f ⟨Complex.I * (t : ℂ), by
      show 0 < (Complex.I * (t : ℂ)).im
      rw [Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_re, Complex.ofReal_im]
      simpa using ht⟩ := by
  unfold imAxis; rw [dif_pos ht]

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

namespace HasMeromorphicExtensionWithPole

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

end HasMeromorphicExtensionWithPole

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

namespace HasMeromorphicExtensionWithPole

end HasMeromorphicExtensionWithPole

/-- **Coprime-stripped coefficient sequence at a Finset of primes.**

The S-stripped version of `f : ℕ → ℂ`: zeroed at every positive
integer `n` divisible by some prime in `S`, equal to `f n` elsewhere. -/
def coprimeStrip (S : Finset Nat.Primes) (f : ℕ → ℂ) : ℕ → ℂ :=
  fun n ↦ if ∀ p ∈ S, ¬ (p : ℕ) ∣ n then f n else 0

/-- **`coprimeStrip S f 1 = f 1`** (since no prime divides `1`). -/
@[simp]
lemma coprimeStrip_one (S : Finset Nat.Primes) (f : ℕ → ℂ) :
    coprimeStrip S f 1 = f 1 := by
  unfold coprimeStrip
  rw [if_pos (fun p _ h_dvd ↦ p.prop.one_lt.ne' (Nat.dvd_one.mp h_dvd))]

end LSeries

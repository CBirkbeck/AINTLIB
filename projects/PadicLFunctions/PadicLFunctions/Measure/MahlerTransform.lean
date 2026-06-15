import PadicLFunctions.Measure.Basic
import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# The Mahler (Amice) transform

Following RJW (arXiv:2309.15692) §3.4: to a measure `μ` on `ℤ_p` we attach the power
series `𝓐_μ(T) = ∫ (1+T)^x dμ(x) = ∑_n (∫ binom(x,n) dμ) Tⁿ ∈ ℤ_p[[T]]`, and
prove this
is a bijection — RJW Thm. 3.20 (`thm:mahler`), as a linear equivalence here; the ring
isomorphism is assembled in `PadicLFunctions.Measure.Convolution`.

The analytic input (RJW Thm. 3.13, Mahler's theorem) is entirely in mathlib:
`PadicInt.hasSum_mahler`, `PadicInt.fwdDiff_tendsto_zero`, `mahler`, `mahlerSeries`.

## Main definitions

* `PadicMeasure.mahlerCoeff μ n`: the `n`-th Mahler coefficient `∫ binom(x,n) dμ`.
* `PadicMeasure.mahlerTransform μ`: the Amice transform `𝓐_μ ∈ ℤ_p[[T]]`.
* `PadicMeasure.ofPowerSeries g`: the inverse, `φ ↦ ∑' n, Δⁿφ(0) * g_n`.
* `PadicMeasure.mahlerLinearEquiv`: RJW Thm. 3.20 as a `ℤ_[p]`-linear equivalence.
-/

open scoped fwdDiff
open PowerSeries

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

namespace PadicMeasure

/-- The `n`-th *Mahler coefficient* of a measure: `∫_{ℤ_p} binom(x,n) dμ(x)`.

Source: RJW Def. 3.15 (TeX lines 962–965), coefficient form. -/
noncomputable def mahlerCoeff (μ : PadicMeasure p ℤ_[p]) (n : ℕ) : ℤ_[p] :=
  μ (mahler n)

/-- The *Mahler transform* (or *Amice transform*) of a measure on `ℤ_p`:
`𝓐_μ(T) = ∑_{n ≥ 0} (∫ binom(x,n) dμ) Tⁿ ∈ ℤ_p[[T]]`.

Source: RJW Def. 3.15 (TeX lines 962–965). -/
noncomputable def mahlerTransform (μ : PadicMeasure p ℤ_[p]) : PowerSeries ℤ_[p] :=
  PowerSeries.mk (mahlerCoeff p μ)

@[simp]
lemma coeff_mahlerTransform (μ : PadicMeasure p ℤ_[p]) (n : ℕ) :
    PowerSeries.coeff n (mahlerTransform p μ) = μ (mahler n) := by
  simp [mahlerTransform, mahlerCoeff]

/-- The Mahler transform is `ℤ_[p]`-linear. -/
noncomputable def mahlerTransformₗ :
    PadicMeasure p ℤ_[p] →ₗ[ℤ_[p]] PowerSeries ℤ_[p] where
  toFun := mahlerTransform p
  map_add' _ _ := by ext n; simp [mahlerTransform, mahlerCoeff]
  map_smul' _ _ := by ext n; simp [mahlerTransform, mahlerCoeff]

/-- **Evaluation formula**: integrating `φ` against `μ` is pairing the Mahler
coefficients of `φ` with those of `μ`: `μ φ = ∑' n, Δⁿφ(0) * (∫ binom(x,n) dμ)`.
This is the content of "any measure is uniquely determined by the values
`∫ binom(x,n) dμ`" in the source's proof.

Source: RJW Thm. 3.20, proof, first display (TeX lines 995–998). -/
theorem apply_eq_tsum (μ : PadicMeasure p ℤ_[p]) (f : C(ℤ_[p], ℤ_[p])) :
    μ f = ∑' n, Δ_[1]^[n] (⇑f) 0 * mahlerCoeff p μ n := by
  have hterm : ∀ (a : ℤ_[p]) (n : ℕ),
      (PadicInt.mahlerTerm a n : C(ℤ_[p], ℤ_[p])) = a • mahler n := by
    intro a n
    ext x
    simp [PadicInt.mahlerTerm_apply, smul_eq_mul, mul_comm]
  have h2 : HasSum (fun n => μ (PadicInt.mahlerTerm (Δ_[1]^[n] (⇑f) 0) n)) (μ f) :=
    (PadicInt.hasSum_mahler f).map μ.toAddMonoidHom (continuous p μ)
  refine h2.tsum_eq.symm.trans (tsum_congr fun n => ?_)
  rw [hterm, map_smul, smul_eq_mul, mahlerCoeff]

/-- The Mahler transform of the Dirac measure `δ_a` is `(1+T)^a` (the binomial series).

Source: RJW Ex. 3.16 (TeX lines 968–973). -/
@[simp]
theorem mahlerTransform_dirac (a : ℤ_[p]) :
    mahlerTransform p (dirac p a) = binomialSeries ℤ_[p] a := by
  ext n
  simp [binomialSeries_coeff, mahler_apply, smul_eq_mul]

/-- The Mahler transform is injective: a measure killing every `binom(·,n)` is zero.

Source: RJW Thm. 3.20, proof ("uniquely determined", TeX lines 995–998). -/
theorem mahlerTransform_injective : Function.Injective (mahlerTransform p) := by
  intro μ ν h
  refine LinearMap.ext fun f => ?_
  rw [apply_eq_tsum p μ f, apply_eq_tsum p ν f]
  refine tsum_congr fun n => ?_
  have hn : μ (mahler n) = ν (mahler n) := by
    simpa using congrArg (PowerSeries.coeff n) h
  rw [mahlerCoeff, mahlerCoeff, hn]

/-- The summand `Δⁿf(0)·gₙ` of `ofPowerSeries` is summable: the Mahler coefficients
tend to zero and the power-series coefficients are bounded by 1. -/
private lemma summable_fwdDiff_mul (f : C(ℤ_[p], ℤ_[p])) (g : PowerSeries ℤ_[p]) :
    Summable fun n => Δ_[1]^[n] (⇑f) 0 * PowerSeries.coeff n g := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop]
  have h := PadicInt.fwdDiff_tendsto_zero f
  rw [tendsto_zero_iff_norm_tendsto_zero] at h ⊢
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h
  calc ‖Δ_[1]^[n] (⇑f) 0 * PowerSeries.coeff n g‖
      = ‖Δ_[1]^[n] (⇑f) 0‖ * ‖PowerSeries.coeff n g‖ := norm_mul _ _
    _ ≤ ‖Δ_[1]^[n] (⇑f) 0‖ * 1 :=
        mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
    _ = ‖Δ_[1]^[n] (⇑f) 0‖ := mul_one _

/-- The measure `μ_g` attached to a power series `g`: `φ ↦ ∑' n, Δⁿφ(0) * g_n`.
The series converges because `Δⁿφ(0) → 0` (mathlib's `PadicInt.fwdDiff_tendsto_zero`)
and `ℤ_p` is a complete nonarchimedean ring.

Source: RJW Thm. 3.20, proof, converse direction (TeX lines 1000–1004). -/
noncomputable def ofPowerSeries (g : PowerSeries ℤ_[p]) : PadicMeasure p ℤ_[p] where
  toFun f := ∑' n, Δ_[1]^[n] (⇑f) 0 * PowerSeries.coeff n g
  map_add' f₁ f₂ := by
    simp only [ContinuousMap.coe_add, fwdDiff_iter_add, Pi.add_apply, add_mul]
    exact (summable_fwdDiff_mul p f₁ g).tsum_add (summable_fwdDiff_mul p f₂ g)
  map_smul' c f := by
    simp only [ContinuousMap.coe_smul, fwdDiff_iter_const_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, mul_assoc]
    exact (summable_fwdDiff_mul p f g).tsum_mul_left c

/-- `Δⁿ(binom(·,k))(0) = δ_{nk}` over `ℤ_p`: transported from mathlib's
`fwdDiff_iter_choose_zero` (over `ℕ → ℤ`) along the finite-sum formula for iterated
forward differences. -/
lemma fwdDiff_iter_mahler_zero (n k : ℕ) :
    Δ_[1]^[n] (⇑(mahler k : C(ℤ_[p], ℤ_[p]))) 0 = if n = k then 1 else 0 := by
  have key : Δ_[1]^[n] (⇑(mahler k : C(ℤ_[p], ℤ_[p]))) 0
      = ((Δ_[1]^[n] (fun x => (x.choose k : ℤ)) 0 : ℤ) : ℤ_[p]) := by
    rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift, Int.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (0 : ℤ_[p]) + i • (1 : ℤ_[p]) = (i : ℤ_[p]) := by
      rw [zero_add, nsmul_eq_mul, mul_one]
    have h2 : 0 + i • 1 = i := by simp
    rw [h1, h2, mahler_natCast_eq]
    simp only [zsmul_eq_mul]
    push_cast
    ring
  rw [key, fwdDiff_iter_choose_zero]
  split <;> simp

/-- The Mahler coefficients of `ofPowerSeries g` recover `g`: `∫ binom(x,k) dμ_g = g_k`.

Source: RJW Thm. 3.20, proof: "Visibly we have 𝓐_{μ_g} = g" (TeX line 1004). -/
@[simp]
theorem mahlerTransform_ofPowerSeries (g : PowerSeries ℤ_[p]) :
    mahlerTransform p (ofPowerSeries p g) = g := by
  ext k
  rw [coeff_mahlerTransform]
  change ∑' n, Δ_[1]^[n] (⇑(mahler k : C(ℤ_[p], ℤ_[p]))) 0 * PowerSeries.coeff n g
      = PowerSeries.coeff k g
  simp_rw [fwdDiff_iter_mahler_zero, ite_mul, one_mul, zero_mul]
  exact tsum_ite_eq k _

/-- **RJW Theorem 3.20 (`thm:mahler`), linear part**: the Mahler transform is a
`ℤ_[p]`-linear equivalence `ℳ(ℤ_p, ℤ_p) ≃ ℤ_p[[T]]`. (Upgraded to a ring isomorphism
in `PadicLFunctions.Measure.Convolution`.) -/
noncomputable def mahlerLinearEquiv : PadicMeasure p ℤ_[p] ≃ₗ[ℤ_[p]] PowerSeries ℤ_[p] :=
  { mahlerTransformₗ p with
    invFun := ofPowerSeries p
    left_inv := fun μ => by
      refine LinearMap.ext fun f => ?_
      change ∑' n, Δ_[1]^[n] (⇑f) 0 * PowerSeries.coeff n (mahlerTransform p μ) = μ f
      simp_rw [coeff_mahlerTransform]
      exact (apply_eq_tsum p μ f).symm
    right_inv := mahlerTransform_ofPowerSeries p }

@[simp]
lemma mahlerLinearEquiv_apply (μ : PadicMeasure p ℤ_[p]) :
    mahlerLinearEquiv p μ = mahlerTransform p μ := rfl

@[simp]
lemma mahlerLinearEquiv_symm_apply (g : PowerSeries ℤ_[p]) :
    (mahlerLinearEquiv p).symm g = ofPowerSeries p g := rfl

end PadicMeasure

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.CoefficientSystem
import LeanModularForms.Modularforms.ResToImagAxis
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# Period integrals for modular symbols (ES-3a)

This file builds the analytic foundation of the modular-symbol period map: the *period integral*
of a cusp form against a homogeneous polynomial coefficient, taken along the geodesic from the
cusp `0` to the cusp `∞` (i.e. up the positive imaginary axis).

For a cusp form `f` of weight `k` for `Γ₁(N)` and a homogeneous polynomial `P ∈ Sym^{k-2}`, the
*period integral* is
$$\langle f, \{0, \infty\}\otimes P\rangle = \int_0^{\infty} f(it)\, P(it, 1)\, i\, dt.$$
This is the canonical generator (Shimura, *Introduction to the Arithmetic Theory of Automorphic
Functions*, §8.2; the differential `𝔡(f) = f(z) P(z,1)\,dz` of (8.2.12)).

The descent of this pairing to the modular-symbol module `𝕄 N k` (Γ-invariance) and the
Hecke-equivariance are handled in later leaves (ES-3b/c); here we build only the underlying
integral and prove that it converges (the integrand is integrable along the improper contour).

## Main definitions

* `evalSym1 m P z` : evaluation of the homogeneous polynomial `P` at `(X₀, X₁) = (z, 1)`.
* `periodIntegrand k f P` : the holomorphic integrand `τ ↦ f τ · P(τ, 1)` on `ℍ`.
* `imagAxisPeriodIntegrand k f P` : the parametrised integrand `t ↦ f(it) · P(it, 1) · i` on `ℝ`.
* `periodIntegral k f P` : the period integral `∫_{(0,∞)} f(it) · P(it, 1) · i \, dt`.

## Main results

* `integrableOn_imagAxisPeriodIntegrand` : the integrand is integrable on `(0, ∞)` — convergence
  of the (improper, cusp-to-cusp) period integral.  This is the analytic heart of the file: the
  exponential cusp decay `f =O(exp(-c·Im))` beats the polynomial growth of `P(it, 1)` at both
  cusps (`∞` directly, `0` via the slash action of `S = [[0,-1],[1,0]]`).
* `periodIntegral_add_left`, `periodIntegral_smul_left` : `ℂ`-linearity of the period in `f`.
* `periodIntegral_add_right`, `periodIntegral_smul_right` : `ℂ`-linearity of the period in `P`.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §8.2.
-/

noncomputable section

namespace HeckeRing.GL2.ModularSymbols

open scoped MatrixGroups ModularForm Topology Pointwise
open UpperHalfPlane Complex MeasureTheory Filter Asymptotics CongruenceSubgroup
  Matrix.SpecialLinearGroup MvPolynomial ConjAct

variable {N : ℕ} [NeZero N]

/-! ## `evalSym1` — evaluating a `Sym^m` element at `(z, 1)` -/

/-- Evaluate the homogeneous polynomial `P ∈ Sym^m(ℂ²)` at `(X₀, X₁) = (z, 1)`. -/
def evalSym1 (m : ℕ) (P : SymPow ℂ m) (z : ℂ) : ℂ :=
  MvPolynomial.eval ![z, 1] (P : MvPolynomial (Fin 2) ℂ)

@[simp]
theorem evalSym1_apply (m : ℕ) (P : SymPow ℂ m) (z : ℂ) :
    evalSym1 m P z = MvPolynomial.eval ![z, 1] (P : MvPolynomial (Fin 2) ℂ) :=
  rfl

/-- The point `(z, 1) ∈ ℂ²` as a function of `z`, used to evaluate `Sym^m` elements. -/
theorem continuous_vec_z_one : Continuous (fun z : ℂ => (![z, 1] : Fin 2 → ℂ)) := by
  apply continuous_pi
  intro i; fin_cases i <;> simp <;> fun_prop

/-- `evalSym1 m P` is continuous (it is a polynomial function of `z`). -/
@[fun_prop]
theorem continuous_evalSym1 (m : ℕ) (P : SymPow ℂ m) : Continuous (evalSym1 m P) :=
  (MvPolynomial.continuous_eval (P : MvPolynomial (Fin 2) ℂ)).comp continuous_vec_z_one

/-- `evalSym1` is additive in `P`. -/
@[simp]
theorem evalSym1_add (m : ℕ) (P Q : SymPow ℂ m) (z : ℂ) :
    evalSym1 m (P + Q) z = evalSym1 m P z + evalSym1 m Q z := by
  simp only [evalSym1, Submodule.coe_add, map_add]

/-- `evalSym1` is `ℂ`-homogeneous in `P`. -/
@[simp]
theorem evalSym1_smul (m : ℕ) (c : ℂ) (P : SymPow ℂ m) (z : ℂ) :
    evalSym1 m (c • P) z = c * evalSym1 m P z := by
  simp only [evalSym1, SetLike.val_smul, MvPolynomial.smul_eval]

@[simp]
theorem evalSym1_zero (m : ℕ) (z : ℂ) : evalSym1 m (0 : SymPow ℂ m) z = 0 := by
  simp [evalSym1]

/-! ## Polynomial growth bound for `evalSym1` along the imaginary axis

`evalSym1 m P` is a polynomial function, so it has polynomial growth.  We package the bound
`‖evalSym1 m P z‖ ≤ C · (max 1 ‖z‖) ^ D` where `D` is the total degree, which is all we need to
dominate it by `exp(ε·t)` along the imaginary axis. -/

/-- For a single monomial exponent `d : Fin 2 →₀ ℕ`, evaluating the monomial term at `![z, 1]`
gives `coeff · z ^ (d 0)`. -/
theorem eval_vec_z_one_eq (z : ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.eval ![z, 1] P = ∑ d ∈ P.support, P.coeff d * z ^ (d 0) := by
  rw [MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun d _ => ?_
  congr 1
  rw [Fin.prod_univ_two]
  simp

/-- Polynomial growth bound: `‖evalSym1 m P z‖` is bounded by a constant times
`(max 1 ‖z‖) ^ (totalDegree)`. -/
theorem norm_evalSym1_le (m : ℕ) (P : SymPow ℂ m) (z : ℂ) :
    ‖evalSym1 m P z‖ ≤
      (∑ d ∈ (P : MvPolynomial (Fin 2) ℂ).support, ‖(P : MvPolynomial (Fin 2) ℂ).coeff d‖) *
        (max 1 ‖z‖) ^ (P : MvPolynomial (Fin 2) ℂ).totalDegree := by
  rw [evalSym1, eval_vec_z_one_eq]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun d hd => ?_
  rw [norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖z‖ ^ (d 0) ≤ (max 1 ‖z‖) ^ (d 0) :=
        pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
    _ ≤ (max 1 ‖z‖) ^ (P : MvPolynomial (Fin 2) ℂ).totalDegree := by
        apply pow_le_pow_right₀ (le_max_left _ _)
        calc d 0 ≤ d 0 + d 1 := Nat.le_add_right _ _
          _ = ∑ i, d i := by rw [Fin.sum_univ_two]
          _ = (Finsupp.sum d fun _ e => e) := by
                rw [Finsupp.sum_fintype]; intro _; rfl
          _ ≤ (P : MvPolynomial (Fin 2) ℂ).totalDegree :=
                MvPolynomial.le_totalDegree hd

/-! ## The period integrand -/

/-- The holomorphic integrand of the period integral: `τ ↦ f(τ) · P(τ, 1)`. -/
def periodIntegrand (k : ℤ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (P : SymPow ℂ (k - 2).toNat) : ℍ → ℂ :=
  fun τ => f τ * evalSym1 (k - 2).toNat P (τ : ℂ)

omit [NeZero N] in
@[simp]
theorem periodIntegrand_apply (k : ℤ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (P : SymPow ℂ (k - 2).toNat) (τ : ℍ) :
    periodIntegrand k f P τ = f τ * evalSym1 (k - 2).toNat P (τ : ℂ) :=
  rfl

/-- `evalSym1 m P` is (complex-)differentiable: it is a polynomial in `z`.  (Holomorphy of the
integrand; not needed for the integrability route, recorded for completeness / later leaves.) -/
theorem differentiable_evalSym1 (m : ℕ) (P : SymPow ℂ m) :
    Differentiable ℂ (evalSym1 m P) := by
  have h : evalSym1 m P =
      fun z => ∑ d ∈ (P : MvPolynomial (Fin 2) ℂ).support,
        (P : MvPolynomial (Fin 2) ℂ).coeff d * z ^ (d 0) := by
    ext z; rw [evalSym1, eval_vec_z_one_eq]
  rw [h]
  apply Differentiable.fun_sum
  intro d _
  fun_prop

omit [NeZero N] in
/-- The period integrand is continuous on `ℍ`. -/
@[fun_prop]
theorem continuous_periodIntegrand (k : ℤ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (P : SymPow ℂ (k - 2).toNat) : Continuous (periodIntegrand k f P) :=
  (ModularFormClass.continuous f).mul
    ((continuous_evalSym1 _ P).comp continuous_coe)

/-! ## Shared analytic input: exponential cusp decay and the slash-`S` relation

These facts feed both the polymorphic integrand below and its `CuspForm`-specific
specialisation. -/

/-- **Exponential cusp decay, pointwise form.**  A cusp form (for any arithmetic group with `∞` a
cusp) has a bound `‖f z‖ ≤ C·exp(-c·Im z)` for all `z` with `Im z` above some threshold `A`, with
`c > 0`.  This is the pointwise repackaging of `CuspFormClass.exp_decay_atImInfty'`. -/
theorem exists_exp_decay_bound {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    [CuspFormClass F Γ k] [Γ.HasDetPlusMinusOne] [DiscreteTopology Γ]
    [Fact (IsCusp OnePoint.infty Γ)] (f : F) :
    ∃ c > 0, ∃ C A : ℝ, ∀ z : ℍ, A ≤ z.im → ‖f z‖ ≤ C * Real.exp (-c * z.im) := by
  obtain ⟨c, hc, hO⟩ := CuspFormClass.exp_decay_atImInfty' f
  rw [Asymptotics.isBigO_iff] at hO
  obtain ⟨C, hC⟩ := hO
  rw [atImInfty, Filter.eventually_comap, Filter.eventually_atTop] at hC
  obtain ⟨A, hA⟩ := hC
  exact ⟨c, hc, C, A, fun z hz => by simpa using hA z.im hz z rfl⟩

/-! ### Convergence at the cusp `0` (bottom end)

Near the cusp `0`, the form `f` does not decay in the `it`-coordinate directly; we use the slash
action of `S = [[0,-1],[1,0]]`, which sends `0 ↦ ∞`.  Writing `f(it) = i^k t^{-k} (f∣S)(i/t)` and
using that `f∣S` is again a cusp form (for the conjugate arithmetic group, hence decaying at `i∞`),
the product `t^{-k} · (f∣S)(i/t) · P(it,1)` tends to `0` as `t → 0⁺`. -/

/-- `s ↦ s^m · exp(-c·s) → 0` at `+∞` for `c > 0` and any integer `m`.  (Powers are beaten by
exponential decay.) -/
theorem tendsto_zpow_mul_exp_neg_atTop (c : ℝ) (hc : 0 < c) (m : ℤ) :
    Tendsto (fun s : ℝ => s ^ m * Real.exp (-c * s)) atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (m : ℝ) c hc
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  rw [Real.rpow_intCast]

omit [NeZero N] in
/-- The conjugate cusp form `f ∣ S` (a `CuspForm` for the `S`-conjugate of the level group). -/
theorem coe_translate_S (k : ℤ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(CuspForm.translate f (mapGL ℝ ModularGroup.S)) = ⇑f ∣[k] ModularGroup.S :=
  rfl

/-- The `S`-conjugate of an arithmetic group is arithmetic, so `f ∣ S` enjoys exponential decay
too. -/
theorem isArithmetic_conj_S' {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] :
    (ConjAct.toConjAct (mapGL ℝ ModularGroup.S)⁻¹ • Γ).IsArithmetic := by
  have h : (mapGL ℝ ModularGroup.S)⁻¹ = ((mapGL ℚ ModularGroup.S)⁻¹).map (algebraMap ℚ ℝ) := by
    rw [map_inv, map_mapGL]
  rw [h]
  exact Subgroup.IsArithmetic.conj Γ (mapGL ℚ ModularGroup.S)⁻¹

/-- The `S`-conjugate of the level group is arithmetic, so `f ∣ S` enjoys exponential decay too. -/
theorem isArithmetic_conj_S :
    (ConjAct.toConjAct (mapGL ℝ ModularGroup.S)⁻¹ • ((Gamma1 N).map (mapGL ℝ))).IsArithmetic :=
  isArithmetic_conj_S'

omit [NeZero N] in
/-- The relation `f(it) = i^k (1/t)^k (f∣S)(i/t)` along the imaginary axis (from the slash action
of `S`). -/
theorem resToImagAxis_eq_slash_S (k : ℤ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {t : ℝ} (ht : 0 < t) :
    ResToImagAxis (⇑f) t =
      Complex.I ^ k * ((1 / t : ℝ) : ℂ) ^ k * ResToImagAxis (⇑f ∣[k] ModularGroup.S) (1 / t) := by
  have h := ResToImagAxis.SlashActionS (⇑f) k (show (0 : ℝ) < 1 / t by positivity)
  rw [one_div_one_div] at h
  rw [Function.resToImagAxis_apply, Function.resToImagAxis_apply] at h
  rw [h]
  rw [← mul_assoc, ← mul_assoc]
  rw [show Complex.I ^ k * ((1 / t : ℝ) : ℂ) ^ k * Complex.I ^ (-k) * ((1 / t : ℝ) : ℂ) ^ (-k)
      = (Complex.I ^ k * Complex.I ^ (-k)) * (((1 / t : ℝ) : ℂ) ^ k * ((1 / t : ℝ) : ℂ) ^ (-k))
      by ring]
  have hne : ((1 / t : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; positivity
  rw [← zpow_add₀ Complex.I_ne_zero, ← zpow_add₀ hne]
  simp

/-! ## Polymorphic period integral for an arbitrary arithmetic cusp form

To handle the integral up a *vertical line* `{q + it}` from a finite cusp `q ∈ ℚ` to `i∞`, we reduce
to the imaginary axis by the horizontal translation `z ↦ z + q`.  This turns the cusp form `f` into
its translate `f ∣ T_q` — a cusp form for the conjugate (still arithmetic) group.  We therefore
generalise the ES-3a integrand and its integrability to **any** cusp form for an arithmetic group.
-/

section Generic

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

/-- The ES-3a period integrand for an arbitrary function `F : ℍ → ℂ` and polynomial `P`,
parametrised along the positive imaginary axis: `t ↦ F(it) · P(it, 1) · i`, extended by `0` for
`t ≤ 0`. -/
def genIntegrand (F : ℍ → ℂ) {m : ℕ} (P : SymPow ℂ m) : ℝ → ℂ :=
  fun t => ResToImagAxis (fun τ => F τ * evalSym1 m P (τ : ℂ)) t * Complex.I

theorem genIntegrand_apply_of_pos (F : ℍ → ℂ) {m : ℕ} (P : SymPow ℂ m) {t : ℝ} (ht : 0 < t) :
    genIntegrand F P t =
      F ⟨Complex.I * t, by simp [ht]⟩ *
        evalSym1 m P (⟨Complex.I * t, by simp [ht]⟩ : ℍ) * Complex.I := by
  simp only [genIntegrand, ResToImagAxis, ht, ↓reduceDIte]

@[simp]
theorem genIntegrand_zero (F : ℍ → ℂ) {m : ℕ} (P : SymPow ℂ m) :
    genIntegrand F P 0 = 0 := by
  simp [genIntegrand, ResToImagAxis]

/-- The polymorphic integrand is continuous on the open ray `(0, ∞)` when `F` is continuous. -/
theorem continuousOn_genIntegrand {F : ℍ → ℂ} (hF : Continuous F) {m : ℕ} (P : SymPow ℂ m) :
    ContinuousOn (genIntegrand F P) (Set.Ioi 0) := by
  intro t ht
  rw [Set.mem_Ioi] at ht
  apply ContinuousAt.continuousWithinAt
  have hofc : ContinuousAt UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)) :=
    (contMDiffAt_ofComplex (n := ⊤) (by simp [ht])).continuousAt
  have hg : ContinuousAt (fun s : ℝ => Complex.I * (s : ℂ)) t := by fun_prop
  have hcomp : ContinuousAt (fun s : ℝ => UpperHalfPlane.ofComplex (Complex.I * (s : ℂ))) t :=
    ContinuousAt.comp hofc hg
  have hfull : ContinuousAt (fun s : ℝ =>
      (fun τ => F τ * evalSym1 m P (τ : ℂ)) (UpperHalfPlane.ofComplex (Complex.I * (s : ℂ)))
        * Complex.I) t :=
    ((hF.mul ((continuous_evalSym1 m P).comp continuous_coe)).continuousAt.comp hcomp).mul
      continuousAt_const
  apply hfull.congr
  filter_upwards [lt_mem_nhds ht] with s hs
  simp only [genIntegrand, ResToImagAxis, hs, ↓reduceDIte]
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simp [hs])]

/-- **Decay at the cusp `∞`.**  For a cusp form `F` of an arithmetic group, the polymorphic
integrand decays exponentially at `t → +∞` (the cusp decay of `F` beats the polynomial growth of
`P`). -/
theorem genIntegrand_isBigO_atTop [CuspFormClass F Γ k] [Γ.IsArithmetic] (f : F) {m : ℕ}
    (P : SymPow ℂ m) :
    ∃ b > 0, genIntegrand (⇑f) P =O[atTop] fun t : ℝ => Real.exp (-b * t) := by
  obtain ⟨c, hc, C, A, hbound⟩ := exists_exp_decay_bound f
  set D := (P : MvPolynomial (Fin 2) ℂ).totalDegree with hD
  set K := ∑ d ∈ (P : MvPolynomial (Fin 2) ℂ).support,
    ‖(P : MvPolynomial (Fin 2) ℂ).coeff d‖ with hK
  refine ⟨c / 2, by positivity, ?_⟩
  have hstep1 : genIntegrand (⇑f) P =O[atTop]
      fun t : ℝ => (t ^ D) * Real.exp (-c * t) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨C * K, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop (max A 1)] with t ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le one_pos (le_trans (le_max_right A 1) ht)
    have htA : A ≤ t := le_trans (le_max_left A 1) ht
    have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_right A 1) ht
    rw [genIntegrand_apply_of_pos (⇑f) P htpos]
    set z : ℍ := ⟨Complex.I * t, by simp [htpos]⟩ with hz
    have hzim : z.im = t := by simp [hz, UpperHalfPlane.im]
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one]
    have hfb : ‖f z‖ ≤ C * Real.exp (-c * t) := by
      have := hbound z (by rw [hzim]; exact htA); rwa [hzim] at this
    have hKnn : 0 ≤ K := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hPb : ‖evalSym1 m P (z : ℂ)‖ ≤ K * t ^ D := by
      have h := norm_evalSym1_le m P (z : ℂ)
      rw [← hK, ← hD] at h
      have hzn : ‖(z : ℂ)‖ = t := by rw [hz]; simp [abs_of_pos htpos]
      rw [hzn, max_eq_right ht1] at h
      exact h
    have hCexp : 0 ≤ C * Real.exp (-c * t) := (norm_nonneg (f z)).trans hfb
    calc ‖f z‖ * ‖evalSym1 m P (z : ℂ)‖
        ≤ (C * Real.exp (-c * t)) * (K * t ^ D) :=
          mul_le_mul hfb hPb (norm_nonneg _) hCexp
      _ = C * K * (t ^ D * Real.exp (-c * t)) := by ring
      _ = C * K * ‖t ^ D * Real.exp (-c * t)‖ := by
          rw [Real.norm_of_nonneg (by positivity)]
  have hstep2 : (fun t : ℝ => (t ^ D) * Real.exp (-c * t)) =O[atTop]
      fun t : ℝ => Real.exp (-(c / 2) * t) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop D (show (0 : ℝ) < c / 2 by positivity)).mul_isBigO
      (Asymptotics.isBigO_refl (fun t : ℝ => Real.exp (-c * t)) atTop)
    refine h.isBigO.congr_right ?_
    intro t; rw [← Real.exp_add]; ring_nf
  exact hstep1.trans hstep2

/-- **Integrability at the cusp `∞`.**  The polymorphic integrand is integrable on `[1, ∞)`. -/
theorem genIntegrableOn_Ici_one [CuspFormClass F Γ k] [Γ.IsArithmetic] (f : F) {m : ℕ}
    (P : SymPow ℂ m) :
    IntegrableOn (genIntegrand (⇑f) P) (Set.Ici 1) := by
  obtain ⟨b, hb, hO⟩ := genIntegrand_isBigO_atTop f P
  have hloc : MeasureTheory.LocallyIntegrableOn (genIntegrand (⇑f) P) (Set.Ici 1) := by
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ici
    exact (continuousOn_genIntegrand (ModularFormClass.continuous f) P).mono
      (fun x hx => by simp only [Set.mem_Ici] at hx; simp only [Set.mem_Ioi]; linarith)
  exact hloc.integrableOn_of_isBigO_atTop hO
    ⟨Set.Ioi b, Ioi_mem_atTop b, exp_neg_integrableOn_Ioi b hb⟩

/-- **Convergence at the cusp `0`.**  For a cusp form `F` of an arithmetic group, the polymorphic
integrand tends to `0` as `t → 0⁺`: applying the slash action of `S`, the exponential decay of
`F ∣ S` at `i∞` beats the polynomial factors. -/
theorem tendsto_genIntegrand_nhdsGT_zero [CuspFormClass F Γ k] [Γ.IsArithmetic] (f : F) {m : ℕ}
    (P : SymPow ℂ m) :
    Tendsto (genIntegrand (⇑f) P) (𝓝[>] 0) (𝓝 0) := by
  haveI : (toConjAct (mapGL ℝ ModularGroup.S)⁻¹ • Γ).IsArithmetic := isArithmetic_conj_S'
  obtain ⟨c, hc, C, A, hbound⟩ :=
    exists_exp_decay_bound (CuspForm.translate f (mapGL ℝ ModularGroup.S))
  set A' := max A 1 with hA'
  have hA'1 : (1 : ℝ) ≤ A' := le_max_right _ _
  have hA'0 : (0 : ℝ) < A' := lt_of_lt_of_le one_pos hA'1
  set K := ∑ d ∈ (P : MvPolynomial (Fin 2) ℂ).support,
    ‖(P : MvPolynomial (Fin 2) ℂ).coeff d‖ with hK
  set D := (P : MvPolynomial (Fin 2) ℂ).totalDegree with hD
  have hKnn : 0 ≤ K := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set g : ℝ → ℝ := fun t => (max C 0 * K) * ((1 / t) ^ k * Real.exp (-c * (1 / t))) with hg
  have hg0 : Tendsto g (𝓝[>] 0) (𝓝 0) := by
    have hinv : Tendsto (fun t : ℝ => 1 / t) (𝓝[>] (0 : ℝ)) atTop :=
      tendsto_inv_nhdsGT_zero.congr fun t => (one_div t).symm
    have hcomp := (tendsto_zpow_mul_exp_neg_atTop c hc k).comp hinv
    have h2 : Tendsto (fun t : ℝ => (max C 0 * K) * ((1 / t) ^ k * Real.exp (-c * (1 / t))))
        (𝓝[>] 0) (𝓝 (max C 0 * K * 0)) := hcomp.const_mul (max C 0 * K)
    simpa [hg] using h2
  apply squeeze_zero_norm' _ hg0
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (show (0 : ℝ) < 1 / A' by positivity))]
    with t htpos htle
  rw [Set.mem_Ioi] at htpos
  rw [Set.mem_Iic] at htle
  have hst : A' ≤ 1 / t := by
    rw [le_div_iff₀ htpos]
    have := (le_div_iff₀ hA'0).mp htle
    linarith [this]
  rw [genIntegrand_apply_of_pos (⇑f) P htpos, norm_mul, norm_mul, Complex.norm_I, mul_one]
  set z : ℍ := ⟨Complex.I * t, by simp [htpos]⟩ with hz
  have hzc : (z : ℂ) = Complex.I * t := rfl
  have hzf : f z = ResToImagAxis (⇑f) t := by
    simp only [ResToImagAxis, htpos, ↓reduceDIte]; rfl
  have hslash : ResToImagAxis (⇑f) t =
      Complex.I ^ k * ((1 / t : ℝ) : ℂ) ^ k *
        ResToImagAxis (⇑f ∣[k] ModularGroup.S) (1 / t) := by
    have h := ResToImagAxis.SlashActionS (⇑f) k (show (0 : ℝ) < 1 / t by positivity)
    rw [one_div_one_div] at h
    rw [Function.resToImagAxis_apply, Function.resToImagAxis_apply] at h
    rw [h, ← mul_assoc, ← mul_assoc]
    rw [show Complex.I ^ k * ((1 / t : ℝ) : ℂ) ^ k * Complex.I ^ (-k) * ((1 / t : ℝ) : ℂ) ^ (-k)
        = (Complex.I ^ k * Complex.I ^ (-k)) *
          (((1 / t : ℝ) : ℂ) ^ k * ((1 / t : ℝ) : ℂ) ^ (-k)) by ring]
    have hne : ((1 / t : ℝ) : ℂ) ≠ 0 := by rw [Ne, Complex.ofReal_eq_zero]; positivity
    rw [← zpow_add₀ Complex.I_ne_zero, ← zpow_add₀ hne]
    simp
  set w : ℍ := ⟨Complex.I * (1 / t), by simp [htpos]⟩ with hw
  have hwim : w.im = 1 / t := by simp [hw, UpperHalfPlane.im]
  have hfSval : ResToImagAxis (⇑f ∣[k] ModularGroup.S) (1 / t) =
      (CuspForm.translate f (mapGL ℝ ModularGroup.S)) w := by
    rw [show (⇑f ∣[k] ModularGroup.S) = ⇑(CuspForm.translate f (mapGL ℝ ModularGroup.S)) from rfl,
      hw]
    simp only [ResToImagAxis, show (0 : ℝ) < 1 / t by positivity, ↓reduceDIte]
    congr 2
    push_cast; ring
  have hfSbound : ‖(CuspForm.translate f (mapGL ℝ ModularGroup.S)) w‖ ≤
      C * Real.exp (-c * (1 / t)) := by
    have := hbound w (by rw [hwim]; exact le_trans (le_max_left A 1) hst)
    rwa [hwim] at this
  have hfz : ‖f z‖ ≤ max C 0 * Real.exp (-c * (1 / t)) * (1 / t) ^ k := by
    rw [hzf, hslash, norm_mul, norm_mul, norm_zpow, Complex.norm_I, one_zpow, one_mul, hfSval]
    rw [show ‖((1 / t : ℝ) : ℂ) ^ k‖ = (1 / t) ^ k from by
      rw [norm_zpow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]]
    calc (1 / t) ^ k * ‖(CuspForm.translate f (mapGL ℝ ModularGroup.S)) w‖
        ≤ (1 / t) ^ k * (C * Real.exp (-c * (1 / t))) :=
          mul_le_mul_of_nonneg_left hfSbound (by positivity)
      _ ≤ (1 / t) ^ k * (max C 0 * Real.exp (-c * (1 / t))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le) (by positivity)
      _ = max C 0 * Real.exp (-c * (1 / t)) * (1 / t) ^ k := by ring
  have hzn : ‖(z : ℂ)‖ = t := by rw [hzc]; simp [abs_of_pos htpos]
  have ht1 : t ≤ 1 := le_trans htle (by rw [div_le_one hA'0]; linarith)
  have hPz : ‖evalSym1 m P (z : ℂ)‖ ≤ K := by
    have h := norm_evalSym1_le m P (z : ℂ)
    rw [← hK, ← hD, hzn, max_eq_left ht1, one_pow, mul_one] at h
    exact h
  calc ‖f z‖ * ‖evalSym1 m P (z : ℂ)‖
      ≤ (max C 0 * Real.exp (-c * (1 / t)) * (1 / t) ^ k) * K :=
        mul_le_mul hfz hPz (norm_nonneg _) (by positivity)
    _ = g t := by rw [hg]; ring

/-- The polymorphic integrand is continuous on `[0, 1]` (value `0` at the cusp `0`). -/
theorem continuousOn_genIntegrand_Icc [CuspFormClass F Γ k] [Γ.IsArithmetic] (f : F) {m : ℕ}
    (P : SymPow ℂ m) :
    ContinuousOn (genIntegrand (⇑f) P) (Set.Icc 0 1) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · subst hx0
    rw [ContinuousWithinAt, genIntegrand_zero]
    refine Tendsto.mono_left ?_ (nhdsWithin_mono _ Set.Icc_subset_Ici_self)
    rw [show (Set.Ici (0 : ℝ)) = {0} ∪ Set.Ioi 0 from by
        rw [Set.union_comm]; exact Set.Ioi_union_left.symm, nhdsWithin_union]
    refine Tendsto.sup ?_ (tendsto_genIntegrand_nhdsGT_zero f P)
    rw [nhdsWithin_singleton, tendsto_pure_left]
    intro s hs; rw [genIntegrand_zero]; exact mem_of_mem_nhds hs
  · exact ((continuousOn_genIntegrand (ModularFormClass.continuous f) P).continuousAt
      (Ioi_mem_nhds hx0)).continuousWithinAt

/-- **Integrability at the cusp `0`.**  The polymorphic integrand is integrable on `(0, 1]`. -/
theorem genIntegrableOn_Ioc_zero_one [CuspFormClass F Γ k] [Γ.IsArithmetic] (f : F) {m : ℕ}
    (P : SymPow ℂ m) :
    IntegrableOn (genIntegrand (⇑f) P) (Set.Ioc 0 1) :=
  ((continuousOn_genIntegrand_Icc f P).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self

/-- **Convergence of the polymorphic period integral** on the whole improper contour `(0, ∞)`. -/
theorem genIntegrableOn [CuspFormClass F Γ k] [Γ.IsArithmetic] (f : F) {m : ℕ} (P : SymPow ℂ m) :
    IntegrableOn (genIntegrand (⇑f) P) (Set.Ioi 0) := by
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ici 1 := by
    ext x; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc, Set.mem_Ici]
    constructor
    · intro hx; rcases le_or_gt x 1 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h.le
    · rintro (⟨hx, _⟩ | hx)
      · exact hx
      · linarith
  rw [hsplit]
  exact (genIntegrableOn_Ioc_zero_one f P).union (genIntegrableOn_Ici_one f P)

/-- The polymorphic period integral `∫₀^∞ F(it) · P(it,1) · i \, dt` of an arithmetic cusp form
`F` against `P`.  Finite by `genIntegrableOn`. -/
def genPeriodIntegral [CuspFormClass F Γ k] [Γ.IsArithmetic] (f : F) {m : ℕ} (P : SymPow ℂ m) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), genIntegrand (⇑f) P t

/-! ### Linearity of the polymorphic period integral in the polynomial slot

We record `ℂ`-linearity in `P`.  (Linearity in the cusp form is handled at the level of the cusp
integral below, where the form is directly evaluated as a function, avoiding any reliance on the
`ℂ`-module structure of `CuspForm Γ k` for the conjugate group.) -/

theorem genIntegrand_add_right (F : ℍ → ℂ) {m : ℕ} (P Q : SymPow ℂ m) (t : ℝ) :
    genIntegrand F (P + Q) t = genIntegrand F P t + genIntegrand F Q t := by
  simp only [genIntegrand, ResToImagAxis]
  split_ifs with h
  · simp only [evalSym1_add]; ring
  · ring

theorem genIntegrand_smul_right (c : ℂ) (F : ℍ → ℂ) {m : ℕ} (P : SymPow ℂ m) (t : ℝ) :
    genIntegrand F (c • P) t = c • genIntegrand F P t := by
  simp only [genIntegrand, ResToImagAxis]
  split_ifs with h
  · simp only [evalSym1_smul, smul_eq_mul]; ring
  · simp

theorem genPeriodIntegral_add_right [CuspFormClass F Γ k] [Γ.IsArithmetic] (f : F) {m : ℕ}
    (P Q : SymPow ℂ m) :
    genPeriodIntegral f (P + Q) = genPeriodIntegral f P + genPeriodIntegral f Q := by
  simp only [genPeriodIntegral]
  rw [← MeasureTheory.integral_add (genIntegrableOn f P) (genIntegrableOn f Q)]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  exact genIntegrand_add_right (⇑f) P Q t

theorem genPeriodIntegral_smul_right [CuspFormClass F Γ k] [Γ.IsArithmetic] (c : ℂ) (f : F)
    {m : ℕ} (P : SymPow ℂ m) :
    genPeriodIntegral f (c • P) = c • genPeriodIntegral f P := by
  simp only [genPeriodIntegral]
  rw [← MeasureTheory.integral_smul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  exact genIntegrand_smul_right c (⇑f) P t

end Generic

/-! ## The parametrised integrand on the imaginary axis

We integrate the geodesic from `0` to `∞`, i.e. the positive imaginary axis `z = it`, `t ∈ (0, ∞)`,
along which `dz = i\,dt`.  The parametrised integrand is `t ↦ (periodIntegrand)(it) · i`,
extended by `0` for `t ≤ 0` (via `ResToImagAxis`). -/

/-- The integrand of the period integral, parametrised along the positive imaginary axis:
`t ↦ f(it) · P(it, 1) · i`.  (The factor `i = dz/dt`.) -/
def imagAxisPeriodIntegrand (k : ℤ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (P : SymPow ℂ (k - 2).toNat) : ℝ → ℂ :=
  fun t => ResToImagAxis (periodIntegrand k f P) t * Complex.I

omit [NeZero N] in
/-- The `CuspForm`-specific integrand *is* the polymorphic one, applied to `⇑f` (`rfl`, since
`periodIntegrand k f P = fun τ ↦ f τ * evalSym1 _ P τ`). -/
theorem imagAxisPeriodIntegrand_eq_genIntegrand (k : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (P : SymPow ℂ (k - 2).toNat) :
    imagAxisPeriodIntegrand k f P = genIntegrand (⇑f) P :=
  rfl

omit [NeZero N] in
theorem imagAxisPeriodIntegrand_apply_of_pos (k : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (P : SymPow ℂ (k - 2).toNat)
    {t : ℝ} (ht : 0 < t) :
    imagAxisPeriodIntegrand k f P t =
      periodIntegrand k f P ⟨Complex.I * t, by simp [ht]⟩ * Complex.I :=
  genIntegrand_apply_of_pos (⇑f) P ht

/-- **The decay of the period integrand along the imaginary axis.**  The exponential cusp decay of
`f` dominates the polynomial growth of `P(it, 1)`, giving an exponential bound at `t → +∞`.  This is
the analytic crux of the convergence at the cusp `∞`. -/
theorem imagAxisPeriodIntegrand_isBigO_atTop (k : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (P : SymPow ℂ (k - 2).toNat) :
    ∃ b > 0, imagAxisPeriodIntegrand k f P =O[atTop] fun t : ℝ => Real.exp (-b * t) :=
  genIntegrand_isBigO_atTop f P

omit [NeZero N] in
/-- The parametrised integrand is continuous on the open ray `(0, ∞)`. -/
theorem continuousOn_imagAxisPeriodIntegrand (k : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (P : SymPow ℂ (k - 2).toNat) :
    ContinuousOn (imagAxisPeriodIntegrand k f P) (Set.Ioi 0) :=
  continuousOn_genIntegrand (ModularFormClass.continuous f) P

/-- **Integrability at the cusp `∞`.**  The period integrand is integrable on `[1, ∞)`: the
exponential cusp decay makes the improper integral converge at the upper cusp. -/
theorem integrableOn_imagAxisPeriodIntegrand_Ici_one (k : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (P : SymPow ℂ (k - 2).toNat) :
    IntegrableOn (imagAxisPeriodIntegrand k f P) (Set.Ici 1) :=
  genIntegrableOn_Ici_one f P

/-- **Convergence at the cusp `0`.**  The period integrand tends to `0` as `t → 0⁺`: applying the
slash action of `S`, the exponential decay of `f ∣ S` at `i∞` (translated to `t → 0`) beats the
polynomial factors `t^{-k}` and `P(it,1)`. -/
theorem tendsto_imagAxisPeriodIntegrand_nhdsGT_zero (k : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (P : SymPow ℂ (k - 2).toNat) :
    Tendsto (imagAxisPeriodIntegrand k f P) (𝓝[>] 0) (𝓝 0) :=
  tendsto_genIntegrand_nhdsGT_zero f P

/-- The period integrand is continuous on `[0, 1]` (taking the value `0` at the cusp `0`). -/
theorem continuousOn_imagAxisPeriodIntegrand_Icc (k : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (P : SymPow ℂ (k - 2).toNat) :
    ContinuousOn (imagAxisPeriodIntegrand k f P) (Set.Icc 0 1) :=
  continuousOn_genIntegrand_Icc f P

/-- **Integrability at the cusp `0`.**  The period integrand is integrable on `(0, 1]`. -/
theorem integrableOn_imagAxisPeriodIntegrand_Ioc_zero_one (k : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (P : SymPow ℂ (k - 2).toNat) :
    IntegrableOn (imagAxisPeriodIntegrand k f P) (Set.Ioc 0 1) :=
  genIntegrableOn_Ioc_zero_one f P

/-- **Convergence of the period integral.**  The integrand `t ↦ f(it)·P(it,1)·i` is integrable on
the whole improper contour `(0, ∞)` from the cusp `0` to the cusp `∞`.  This is the analytic heart
of the modular-symbol period: the exponential cusp decay of `f` dominates the polynomial growth of
`P(it,1)` at *both* cusps. -/
theorem integrableOn_imagAxisPeriodIntegrand (k : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (P : SymPow ℂ (k - 2).toNat) :
    IntegrableOn (imagAxisPeriodIntegrand k f P) (Set.Ioi 0) :=
  genIntegrableOn f P

/-- **The period integral** `⟨f, {0,∞}⊗P⟩ = ∫₀^∞ f(it)·P(it,1)·i\,dt`, the canonical generator of
the modular-symbol period pairing (Shimura §8.2).  It is a well-defined finite complex number by
`integrableOn_imagAxisPeriodIntegrand`. -/
def periodIntegral (k : ℤ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (P : SymPow ℂ (k - 2).toNat) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), imagAxisPeriodIntegrand k f P t

/-! ## Linearity of the period integral

The period is `ℂ`-linear in the cusp form `f` and in the polynomial `P`.  This is the algebraic
content needed to assemble the bilinear period pairing in the later leaves ES-3b/c. -/

omit [NeZero N] in
theorem imagAxisPeriodIntegrand_add_left (k : ℤ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (P : SymPow ℂ (k - 2).toNat) (t : ℝ) :
    imagAxisPeriodIntegrand k (f + g) P t =
      imagAxisPeriodIntegrand k f P t + imagAxisPeriodIntegrand k g P t := by
  simp only [imagAxisPeriodIntegrand, ResToImagAxis]
  split_ifs with h
  · simp only [periodIntegrand_apply, CuspForm.coe_add, Pi.add_apply]; ring
  · ring

omit [NeZero N] in
theorem imagAxisPeriodIntegrand_smul_left (k : ℤ) (c : ℂ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (P : SymPow ℂ (k - 2).toNat) (t : ℝ) :
    imagAxisPeriodIntegrand k (c • f) P t = c • imagAxisPeriodIntegrand k f P t := by
  simp only [imagAxisPeriodIntegrand, ResToImagAxis]
  split_ifs with h
  · have hcf : (c • f) (⟨Complex.I * t, by simp [h]⟩ : ℍ) =
        c * f ⟨Complex.I * t, by simp [h]⟩ := by simp
    rw [periodIntegrand_apply, periodIntegrand_apply, hcf, smul_eq_mul]; ring
  · simp

omit [NeZero N] in
theorem imagAxisPeriodIntegrand_add_right (k : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (P Q : SymPow ℂ (k - 2).toNat) (t : ℝ) :
    imagAxisPeriodIntegrand k f (P + Q) t =
      imagAxisPeriodIntegrand k f P t + imagAxisPeriodIntegrand k f Q t :=
  genIntegrand_add_right (⇑f) P Q t

omit [NeZero N] in
theorem imagAxisPeriodIntegrand_smul_right (k : ℤ) (c : ℂ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (P : SymPow ℂ (k - 2).toNat) (t : ℝ) :
    imagAxisPeriodIntegrand k f (c • P) t = c • imagAxisPeriodIntegrand k f P t :=
  genIntegrand_smul_right c (⇑f) P t

/-- The period integral is additive in the cusp form `f`. -/
theorem periodIntegral_add_left (k : ℤ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (P : SymPow ℂ (k - 2).toNat) :
    periodIntegral k (f + g) P = periodIntegral k f P + periodIntegral k g P := by
  simp only [periodIntegral]
  rw [← MeasureTheory.integral_add (integrableOn_imagAxisPeriodIntegrand k f P)
    (integrableOn_imagAxisPeriodIntegrand k g P)]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  exact imagAxisPeriodIntegrand_add_left k f g P t

omit [NeZero N] in
/-- The period integral is `ℂ`-homogeneous in the cusp form `f`. -/
theorem periodIntegral_smul_left (k : ℤ) (c : ℂ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (P : SymPow ℂ (k - 2).toNat) :
    periodIntegral k (c • f) P = c • periodIntegral k f P := by
  simp only [periodIntegral]
  rw [← MeasureTheory.integral_smul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  exact imagAxisPeriodIntegrand_smul_left k c f P t

/-- The period integral is additive in the polynomial `P`. -/
theorem periodIntegral_add_right (k : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (P Q : SymPow ℂ (k - 2).toNat) :
    periodIntegral k f (P + Q) = periodIntegral k f P + periodIntegral k f Q := by
  simp only [periodIntegral]
  rw [← MeasureTheory.integral_add (integrableOn_imagAxisPeriodIntegrand k f P)
    (integrableOn_imagAxisPeriodIntegrand k f Q)]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  exact imagAxisPeriodIntegrand_add_right k f P Q t

omit [NeZero N] in
/-- The period integral is `ℂ`-homogeneous in the polynomial `P`. -/
theorem periodIntegral_smul_right (k : ℤ) (c : ℂ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (P : SymPow ℂ (k - 2).toNat) :
    periodIntegral k f (c • P) = c • periodIntegral k f P := by
  simp only [periodIntegral]
  rw [← MeasureTheory.integral_smul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  exact imagAxisPeriodIntegrand_smul_right k c f P t

end HeckeRing.GL2.ModularSymbols

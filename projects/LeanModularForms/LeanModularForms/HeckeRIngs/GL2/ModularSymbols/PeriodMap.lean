/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.PeriodIntegral
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.ModuleM
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.FinitelyManyCusps
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The period map for modular symbols (ES-3b)

This file builds the *period map*

```
periodMap N k : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] (𝕄 N k →ₗ[ℤ] ℂ)
```

assembling the period integral of `PeriodIntegral.lean` (ES-3a) into a `ℤ`-linear functional on the
modular-symbol module `𝕄 N k`, `ℂ`-linear in the cusp form.  The pairing of `f` against the class of
`((α) - (β)) ⊗ P` is `∫_β^α f(z) · evalSym1 P z \, dz`, computed via cusp-to-`i∞` integrals along
vertical geodesics.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §8.2.
-/

noncomputable section

namespace HeckeRing.GL2.ModularSymbols

open scoped MatrixGroups ModularForm Topology Pointwise TensorProduct
open UpperHalfPlane Complex MeasureTheory Filter Asymptotics CongruenceSubgroup
  Matrix.SpecialLinearGroup MvPolynomial ConjAct

universe u

/-! ## `evalSym1` under linear substitutions

`evalSym1 m P z = eval ![z, 1] P`.  Pulling the evaluation point through `substAlgHom M` is the
algebraic heart of the change-of-variables: `evalSym1 m (substAlgHom M P) z` is `P` evaluated at the
linear image of `![z, 1]` under `Mᵀ`.  We record the two special substitutions we need:

* horizontal shift `M = [[1, q], [0, 1]]`: `evalSym1 m (substAlgHom M P) z = evalSym1 m P (z + q)`;
* the `symRep` action and its interaction with `evalSym1` at a Möbius-transformed point.
-/

/-- Evaluating `substAlgHom M P` at `![z, 1]` is `P` evaluated at `![M₀₀·z + M₀₁, M₁₀·z + M₁₁]`. -/
theorem evalSym1_substAlgHom (m : ℕ) (M : Matrix (Fin 2) (Fin 2) ℂ) (P : SymPow ℂ m) (z : ℂ) :
    evalSym1 m ⟨substAlgHom M (P : MvPolynomial (Fin 2) ℂ),
        substAlgHom_isHomogeneous M P.2⟩ z =
      MvPolynomial.eval ![M 0 0 * z + M 0 1, M 1 0 * z + M 1 1] (P : MvPolynomial (Fin 2) ℂ) := by
  show (MvPolynomial.eval ![z, 1]) (substAlgHom M (P : MvPolynomial (Fin 2) ℂ)) = _
  rw [substAlgHom]
  have key : ∀ p : MvPolynomial (Fin 2) ℂ,
      (eval ![z, 1]) ((aeval fun i ↦ ∑ j, M i j • X j) p) =
        (eval fun i ↦ (eval ![z, 1]) (∑ j, M i j • X j)) p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.eval_X, MvPolynomial.aeval_X]
  rw [key]
  have hv : (fun i ↦ (eval ![z, 1]) (∑ j, M i j • X j)) =
      ![M 0 0 * z + M 0 1, M 1 0 * z + M 1 1] := by
    ext i
    fin_cases i <;> simp [Fin.sum_univ_two]
  rw [hv]

/-! ## Polymorphic period integral for an arbitrary arithmetic cusp form

To handle the integral up a *vertical line* `{q + it}` from a finite cusp `q ∈ ℚ` to `i∞`, we reduce
to the imaginary axis by the horizontal translation `z ↦ z + q`.  This turns the cusp form `f` into
its translate `f ∣ T_q` — a cusp form for the conjugate (still arithmetic) group.  We therefore
generalise the ES-3a integrand and its integrability to **any** cusp form for an arithmetic group.
-/

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

/-- The `S`-conjugate of an arithmetic group is arithmetic, so `F ∣ S` enjoys exponential decay. -/
theorem isArithmetic_conj_S' [Γ.IsArithmetic] :
    (ConjAct.toConjAct (mapGL ℝ ModularGroup.S)⁻¹ • Γ).IsArithmetic := by
  have h : (mapGL ℝ ModularGroup.S)⁻¹ = ((mapGL ℚ ModularGroup.S)⁻¹).map (algebraMap ℚ ℝ) := by
    rw [map_inv, map_mapGL]
  rw [h]
  exact Subgroup.IsArithmetic.conj Γ (mapGL ℚ ModularGroup.S)⁻¹

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

/-! ## The cusp-to-`i∞` integral

For a finite cusp `q ∈ ℚ` we integrate up the vertical line `{q + it : t > 0}` to `i∞`.  The
translation matrix `transMat q = [[1, q], [0, 1]]` maps the imaginary axis to this line, so the
integrand coincides with the polymorphic integrand of the *translate* `f ∣ transMat q` against the
*shifted* polynomial — giving convergence for free.  We package this as `cuspToInftyIntegral`, with
value `0` at the cusp `∞`. -/

open scoped MatrixGroups

variable {N : ℕ} [NeZero N]

/-- The real translation matrix `[[1, q], [0, 1]] ∈ GL(2, ℝ)` attached to `q : ℚ`. -/
def transMat (q : ℚ) : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.upperRightHom (q : ℝ)

/-- `transMat q` is the image of the rational translation matrix `upperRightHom q` under `ℚ → ℝ`. -/
theorem transMat_eq_map (q : ℚ) :
    transMat q = (Matrix.GeneralLinearGroup.upperRightHom q).map (Rat.castHom ℝ) := by
  rw [transMat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.upperRightHom_apply, Matrix.GeneralLinearGroup.map,
      Matrix.map_apply]

/-- The `transMat q`-conjugate of an arithmetic group is arithmetic (`q ∈ ℚ`). -/
theorem isArithmetic_conj_transMat {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (q : ℚ) :
    (toConjAct (transMat q)⁻¹ • Γ).IsArithmetic := by
  have h : (transMat q)⁻¹ = ((Matrix.GeneralLinearGroup.upperRightHom q)⁻¹).map (Rat.castHom ℝ) := by
    rw [transMat_eq_map, ← map_inv]
  rw [h]
  exact Subgroup.IsArithmetic.conj Γ (Matrix.GeneralLinearGroup.upperRightHom q)⁻¹

/-- The determinant of `transMat q` is `1`. -/
theorem det_transMat (q : ℚ) : ((transMat q).det.val : ℝ) = 1 := by
  rw [transMat]
  simp [Matrix.GeneralLinearGroup.upperRightHom_apply, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.det_fin_two]

/-- `transMat q` has positive determinant. -/
theorem det_transMat_pos (q : ℚ) : 0 < (transMat q).det.val := by rw [det_transMat]; norm_num

/-- The automorphy factor `denom (transMat q) z = 1`. -/
theorem denom_transMat (q : ℚ) (z : ℂ) : UpperHalfPlane.denom (transMat q) z = 1 := by
  rw [transMat, UpperHalfPlane.denom]
  simp [Matrix.GeneralLinearGroup.upperRightHom_apply]

/-- The Möbius action of `transMat q` on `ℍ` is the horizontal shift `z ↦ z + q`. -/
theorem transMat_smul (q : ℚ) (z : ℍ) : ((transMat q • z : ℍ) : ℂ) = (z : ℂ) + q := by
  have h := UpperHalfPlane.coe_smul_of_det_pos (det_transMat_pos q) z
  rw [h, show UpperHalfPlane.denom (transMat q) (z : ℂ) = 1 from denom_transMat q z, div_one,
    UpperHalfPlane.num, transMat]
  simp [Matrix.GeneralLinearGroup.upperRightHom_apply]

/-- The slash of `f` by `transMat q` is the horizontal shift `z ↦ f(z + q)`. -/
theorem slash_transMat_apply (f : ℍ → ℂ) {k : ℤ} (q : ℚ) (z : ℍ) :
    (f ∣[k] (transMat q)) z = f (UpperHalfPlane.ofComplex ((z : ℂ) + q)) := by
  rw [ModularForm.slash_apply, det_transMat, denom_transMat]
  have hsmul : (transMat q • z) = UpperHalfPlane.ofComplex ((z : ℂ) + q) := by
    apply UpperHalfPlane.ext
    rw [transMat_smul, UpperHalfPlane.ofComplex_apply_of_im_pos (by simp [UpperHalfPlane.im_pos z])]
  rw [hsmul]
  have hσ : (UpperHalfPlane.σ (transMat q)) (f (UpperHalfPlane.ofComplex ((z : ℂ) + q))) =
      f (UpperHalfPlane.ofComplex ((z : ℂ) + q)) := by
    rw [UpperHalfPlane.σ, if_pos (det_transMat_pos q)]; rfl
  rw [hσ]
  simp

/-- The coercion of the `CuspForm` translate by `transMat q` is the slash. -/
theorem coe_cuspForm_translate_transMat {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {F : Type*}
    [FunLike F ℍ ℂ] [CuspFormClass F Γ k] (f : F) (q : ℚ) :
    ⇑(CuspForm.translate f (transMat q)) = ⇑f ∣[k] (transMat q) := rfl

/-- The complex shift matrix `[[1, q], [0, 1]]` used to shift the polynomial argument by `q`. -/
def shiftMat (q : ℚ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, (q : ℂ); 0, 1]

/-- The polynomial `P` with its argument shifted by `q`: `evalSym1 (shiftPoly q P) z = P(z + q, 1)`.
-/
def shiftPoly (q : ℚ) {m : ℕ} (P : SymPow ℂ m) : SymPow ℂ m :=
  ⟨substAlgHom (shiftMat q) (P : MvPolynomial (Fin 2) ℂ),
    substAlgHom_isHomogeneous (shiftMat q) P.2⟩

/-- `evalSym1 (shiftPoly q P) z = evalSym1 P (z + q)`. -/
theorem evalSym1_shiftPoly (q : ℚ) {m : ℕ} (P : SymPow ℂ m) (z : ℂ) :
    evalSym1 m (shiftPoly q P) z = evalSym1 m P (z + (q : ℂ)) := by
  rw [shiftPoly, evalSym1_substAlgHom]
  rw [evalSym1, shiftMat]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, mul_comm]

/-- The integral from the finite cusp `q ∈ ℚ` up the vertical line to `i∞`:
`∫₀^∞ f(q + it) · P(q + it, 1) · i \, dt`.  Defined as the polymorphic period integral of the
translate `f ∣ transMat q` against the shifted polynomial `shiftPoly q P`, which makes convergence
automatic and exhibits the value as a finite complex number. -/
def cuspToInftyIntegral (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ} (P : SymPow ℂ m)
    (q : ℚ) : ℂ :=
  haveI : (toConjAct (transMat q)⁻¹ • ((Gamma1 N).map (mapGL ℝ))).IsArithmetic :=
    isArithmetic_conj_transMat q
  genPeriodIntegral (CuspForm.translate f (transMat q)) (shiftPoly q P)

omit [NeZero N] in
/-- The integrand of `cuspToInftyIntegral`, expressed via `f` evaluated at the shifted point. -/
theorem cuspToInftyIntegral_integrand (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (P : SymPow ℂ m) (q : ℚ) {t : ℝ} (ht : 0 < t) :
    genIntegrand (⇑(CuspForm.translate f (transMat q))) (shiftPoly q P) t =
      f (UpperHalfPlane.ofComplex (Complex.I * t + (q : ℂ))) *
        evalSym1 m P (Complex.I * t + (q : ℂ)) * Complex.I := by
  rw [genIntegrand_apply_of_pos _ _ ht, coe_cuspForm_translate_transMat,
    slash_transMat_apply (⇑f) q ⟨Complex.I * t, by simp [ht]⟩, evalSym1_shiftPoly]

/-- Integrability of the cusp integrand. -/
theorem integrableOn_cuspToInftyIntegrand (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (P : SymPow ℂ m) (q : ℚ) :
    IntegrableOn (genIntegrand (⇑(CuspForm.translate f (transMat q))) (shiftPoly q P))
      (Set.Ioi 0) :=
  haveI : (toConjAct (transMat q)⁻¹ • ((Gamma1 N).map (mapGL ℝ))).IsArithmetic :=
    isArithmetic_conj_transMat q
  genIntegrableOn (CuspForm.translate f (transMat q)) (shiftPoly q P)

/-- `cuspToInftyIntegral` is additive in the cusp form `f`. -/
theorem cuspToInftyIntegral_add_left (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (P : SymPow ℂ m) (q : ℚ) :
    cuspToInftyIntegral (f + g) P q =
      cuspToInftyIntegral f P q + cuspToInftyIntegral g P q := by
  simp only [cuspToInftyIntegral, genPeriodIntegral]
  rw [← MeasureTheory.integral_add (integrableOn_cuspToInftyIntegrand f P q)
    (integrableOn_cuspToInftyIntegrand g P q)]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [Set.mem_Ioi] at ht
  rw [cuspToInftyIntegral_integrand _ P q ht, cuspToInftyIntegral_integrand _ P q ht,
    cuspToInftyIntegral_integrand _ P q ht]
  have hfg : (f + g) (UpperHalfPlane.ofComplex (Complex.I * t + (q : ℂ))) =
      f (UpperHalfPlane.ofComplex (Complex.I * t + (q : ℂ))) +
        g (UpperHalfPlane.ofComplex (Complex.I * t + (q : ℂ))) := by simp
  rw [hfg]
  ring

/-- `cuspToInftyIntegral` is `ℂ`-homogeneous in the cusp form `f`. -/
theorem cuspToInftyIntegral_smul_left (c : ℂ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (P : SymPow ℂ m) (q : ℚ) :
    cuspToInftyIntegral (c • f) P q = c • cuspToInftyIntegral f P q := by
  simp only [cuspToInftyIntegral, genPeriodIntegral]
  rw [← MeasureTheory.integral_smul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [Set.mem_Ioi] at ht
  rw [cuspToInftyIntegral_integrand _ P q ht, cuspToInftyIntegral_integrand _ P q ht]
  have hcf : (c • f) (UpperHalfPlane.ofComplex (Complex.I * t + (q : ℂ))) =
      c * f (UpperHalfPlane.ofComplex (Complex.I * t + (q : ℂ))) := by simp
  rw [hcf, smul_eq_mul]
  ring

/-- `cuspToInftyIntegral` is additive in the polynomial `P`. -/
theorem cuspToInftyIntegral_add_right (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (P Q : SymPow ℂ m) (q : ℚ) :
    cuspToInftyIntegral f (P + Q) q =
      cuspToInftyIntegral f P q + cuspToInftyIntegral f Q q := by
  simp only [cuspToInftyIntegral, genPeriodIntegral]
  rw [← MeasureTheory.integral_add (integrableOn_cuspToInftyIntegrand f P q)
    (integrableOn_cuspToInftyIntegrand f Q q)]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [Set.mem_Ioi] at ht
  rw [cuspToInftyIntegral_integrand _ _ q ht, cuspToInftyIntegral_integrand _ _ q ht,
    cuspToInftyIntegral_integrand _ _ q ht, evalSym1_add]
  ring

/-- `cuspToInftyIntegral` is `ℂ`-homogeneous in the polynomial `P`. -/
theorem cuspToInftyIntegral_smul_right (c : ℂ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (P : SymPow ℂ m) (q : ℚ) :
    cuspToInftyIntegral f (c • P) q = c • cuspToInftyIntegral f P q := by
  simp only [cuspToInftyIntegral, genPeriodIntegral]
  rw [← MeasureTheory.integral_smul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [Set.mem_Ioi] at ht
  rw [cuspToInftyIntegral_integrand _ _ q ht, cuspToInftyIntegral_integrand _ _ q ht,
    evalSym1_smul]
  simp only [smul_eq_mul]
  ring

/-! ## The cusp value indexed by a point of `ℙ¹(ℚ)`

We now index the cusp integral by a projective point `c : ℙ¹(ℚ)`, taking the value `0` at the cusp
`∞` and the vertical-line integral `cuspToInftyIntegral` at a finite cusp `q ∈ ℚ`.  The relevant
`q` is recovered from `c` via the equivalence `ℙ¹(ℚ) ≃ OnePoint ℚ`. -/

open scoped LinearAlgebra.Projectivization in
/-- The cusp value of `f` against `P` at a projective point `c : ℙ¹(ℚ)`: the integral up the
geodesic from the cusp `c` to `i∞` (`0` if `c = ∞`). -/
def cuspValue (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ} (P : SymPow ℂ m)
    (c : Projectivization ℚ (Fin 2 → ℚ)) : ℂ :=
  match (OnePoint.equivProjectivization ℚ).symm c with
  | (q : ℚ) => cuspToInftyIntegral f P q
  | .infty => 0

theorem cuspValue_add_left (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (P : SymPow ℂ m) (c : Projectivization ℚ (Fin 2 → ℚ)) :
    cuspValue (f + g) P c = cuspValue f P c + cuspValue g P c := by
  rw [cuspValue, cuspValue, cuspValue]
  cases (OnePoint.equivProjectivization ℚ).symm c with
  | infty => simp
  | coe q => exact cuspToInftyIntegral_add_left f g P q

theorem cuspValue_smul_left (a : ℂ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (P : SymPow ℂ m) (c : Projectivization ℚ (Fin 2 → ℚ)) :
    cuspValue (a • f) P c = a • cuspValue f P c := by
  rw [cuspValue, cuspValue]
  cases (OnePoint.equivProjectivization ℚ).symm c with
  | infty => simp
  | coe q => exact cuspToInftyIntegral_smul_left a f P q

theorem cuspValue_add_right (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (P Q : SymPow ℂ m) (c : Projectivization ℚ (Fin 2 → ℚ)) :
    cuspValue f (P + Q) c = cuspValue f P c + cuspValue f Q c := by
  rw [cuspValue, cuspValue, cuspValue]
  cases (OnePoint.equivProjectivization ℚ).symm c with
  | infty => simp
  | coe q => exact cuspToInftyIntegral_add_right f P Q q

theorem cuspValue_smul_right (a : ℂ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {m : ℕ}
    (P : SymPow ℂ m) (c : Projectivization ℚ (Fin 2 → ℚ)) :
    cuspValue f (a • P) c = a • cuspValue f P c := by
  rw [cuspValue, cuspValue]
  cases (OnePoint.equivProjectivization ℚ).symm c with
  | infty => simp
  | coe q => exact cuspToInftyIntegral_smul_right a f P q

/-! ## The raw pairing on `Div⁰ ⊗ Sym`

We assemble `cuspValue` into a `ℤ`-bilinear, `ℂ`-valued pairing on `(ℙ¹(ℚ) →₀ ℤ) × Sym^m(ℤ)`,
casting the integral `ℤ`-coefficients into `ℂ`.  Restricting to the augmentation subspace `Div⁰`
gives `rawPairing f : (Div0 ℤ ⊗[ℤ] SymPow ℤ m) →ₗ[ℤ] ℂ`, the pre-descent period functional. -/

/-- The `ℤ`-linear cast `Sym^m(ℤ) → Sym^m(ℂ)` induced by `ℤ → ℂ` on coefficients. -/
def castSymPow (m : ℕ) : SymPow ℤ m →ₗ[ℤ] SymPow ℂ m where
  toFun P := ⟨MvPolynomial.map (Int.castRingHom ℂ) (P : MvPolynomial (Fin 2) ℤ),
    (P.2).map (Int.castRingHom ℂ)⟩
  map_add' P Q := by ext1; simp [map_add]
  map_smul' a P := by
    ext1
    simp only [SetLike.val_smul, zsmul_eq_mul, map_mul, map_intCast, RingHom.id_apply,
      Submodule.coe_smul_of_tower]

theorem evalSym1_castSymPow (m : ℕ) (P : SymPow ℤ m) (z : ℂ) :
    evalSym1 m (castSymPow m P) z =
      MvPolynomial.eval ![z, 1] (MvPolynomial.map (Int.castRingHom ℂ)
        (P : MvPolynomial (Fin 2) ℤ)) := rfl

variable (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)

/-- The `ℤ`-linear, `ℂ`-valued functional `P ↦ cuspValue f (P : Sym ℂ) c` at a fixed cusp `c`. -/
def cuspFunctional {m : ℕ} (c : Projectivization ℚ (Fin 2 → ℚ)) : SymPow ℤ m →ₗ[ℤ] ℂ where
  toFun P := cuspValue f (castSymPow m P) c
  map_add' P Q := by rw [map_add, cuspValue_add_right]
  map_smul' a P := by
    rw [map_smul, RingHom.id_apply,
      ← Int.cast_smul_eq_zsmul ℂ a (castSymPow m P), cuspValue_smul_right,
      Int.cast_smul_eq_zsmul ℂ a (cuspValue f (castSymPow m P) c)]

/-- The `ℤ`-bilinear, `ℂ`-valued period pairing on `(ℙ¹(ℚ) →₀ ℤ) × Sym^m(ℤ)`:
`(D, P) ↦ Σ_c D(c) · cuspValue f (P : Sym ℂ) c`, as a `ℤ`-linear map in the divisor slot valued in
functionals on `Sym^m(ℤ)`. -/
def rawBilin {m : ℕ} :
    (Projectivization ℚ (Fin 2 → ℚ) →₀ ℤ) →ₗ[ℤ] SymPow ℤ m →ₗ[ℤ] ℂ :=
  Finsupp.linearCombination ℤ (fun c => cuspFunctional f c)

theorem rawBilin_single {m : ℕ} (c : Projectivization ℚ (Fin 2 → ℚ)) (n : ℤ) (P : SymPow ℤ m) :
    rawBilin f (Finsupp.single c n) P = (n : ℂ) * cuspValue f (castSymPow m P) c := by
  rw [rawBilin, Finsupp.linearCombination_single, LinearMap.smul_apply, cuspFunctional]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, zsmul_eq_mul]

/-- The raw period pairing on `Div⁰ ⊗ Sym^m`, the `ℤ`-bilinear `ℂ`-valued functional
`(D, P) ↦ Σ_c D(c) · cuspValue f (P : Sym ℂ) c`.  This is the pre-descent period functional that
descends to the modular-symbol module `𝕄`. -/
def rawPairing {m : ℕ} : (Div0 ℤ ⊗[ℤ] SymPow ℤ m) →ₗ[ℤ] ℂ :=
  TensorProduct.lift ((rawBilin f).comp (Div0 ℤ).subtype)

@[simp]
theorem rawPairing_tmul {m : ℕ} (D : Div0 ℤ) (P : SymPow ℤ m) :
    rawPairing f (D ⊗ₜ P) = rawBilin f (D : Projectivization ℚ (Fin 2 → ℚ) →₀ ℤ) P :=
  rfl

/-! ## The Möbius covariance of `evalSym1` under `symRep` (the change-of-variables crux)

The algebraic heart of the `Γ`-invariance is Shimura (8.2.15): with the `symRep` convention
`symRep γ = substAlgHom (γ⁻¹)` (the `g⁻¹`-substitution), one has
`evalSym1 m (symRep γ P) (γ • z) = (cz + d)^{-m} · evalSym1 m P z`, where `[[a,b],[c,d]] = γ` and
`cz + d` is the automorphy factor.  Combined with `f(γ • z) = (cz + d)^k f(z)` (slash invariance,
for `γ ∈ Γ₁(N)`) and `dz = (cz+d)^{-2} d(γz)`, the exponents combine as `(cz+d)^{k - (k-2) - 2} = 1`,
which is exactly the cancellation making the period pairing `Γ`-invariant.  We give the
self-contained verification that the `g⁻¹`-substitution convention of `symRep` aligns. -/

/-- Two-variable evaluation expansion: `eval ![u, v] P = Σ_d coeff_d · u^{d₀} · v^{d₁}`. -/
theorem eval_vec_pair_eq (u v : ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.eval ![u, v] P = ∑ d ∈ P.support, P.coeff d * (u ^ (d 0) * v ^ (d 1)) := by
  rw [MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun d _ => ?_
  congr 1
  rw [Fin.prod_univ_two]
  simp

/-- **Homogeneous scaling of `evalSym1`.**  For `P` homogeneous of degree `m` and `D ≠ 0`,
`evalSym1 m P (z / D) = D^{-m} · evalSym1 m P z` — scaling the (projective) point by `D⁻¹` pulls out
`D^{-m}`. -/
theorem evalSym1_div (m : ℕ) (P : SymPow ℂ m) (z D : ℂ) (_hD : D ≠ 0) :
    MvPolynomial.eval ![z / D, 1 / D] (P : MvPolynomial (Fin 2) ℂ) =
      (D ^ m)⁻¹ * evalSym1 m P z := by
  rw [evalSym1, eval_vec_pair_eq, eval_vec_z_one_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d 0 + d 1 = m := by
    have hdm : d.degree = m := by
      by_contra hne
      exact (MvPolynomial.mem_support_iff.mp hd) (MvPolynomial.IsHomogeneous.coeff_eq_zero P.2 hne)
    rw [Finsupp.degree_apply] at hdm
    rw [← hdm, Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => by
      simpa using hx), Fin.sum_univ_two]
  rw [div_pow, div_pow, one_pow, div_mul_div_comm, mul_one, ← pow_add, hdeg, div_eq_inv_mul]
  ring

/-- **Möbius covariance of `evalSym1` (Shimura 8.2.15).**  For `γ ∈ SL(2, ℤ)`, writing
`γ = [[a, b], [c, d]]`, the substitution convention of `symRep` gives
`evalSym1 m (symRep γ P) (γ • z) = (c·z + d)^{-m} · evalSym1 m P z`.  This is the change-of-variables
identity at the core of the modular-symbol `Γ`-invariance: the convention `symRep γ = substAlgHom γ⁻¹`
makes the automorphy factors cancel exactly. -/
theorem evalSym1_symRep_smul {m : ℕ} (γ : SL(2, ℤ)) (P : SymPow ℂ m) (z : ℍ) :
    evalSym1 m (symRep ℂ m γ P) ((γ • z : ℍ) : ℂ) =
      (((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ^ m)⁻¹ * evalSym1 m P (z : ℂ) := by
  have hden : ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ≠ 0 := by
    have hd := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) z
    have hval : ∀ i j, ((Matrix.SpecialLinearGroup.mapGL ℝ γ : Matrix (Fin 2) (Fin 2) ℝ) i j) =
        ((γ i j : ℝ)) := fun i j => by
      rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]; simp [Matrix.SpecialLinearGroup.map_apply_coe]
    rw [UpperHalfPlane.denom, hval, hval] at hd
    intro hc; apply hd
    push_cast at hc ⊢
    rw [← hc]
  -- Inverse-matrix entries of `symMat ℂ γ = (γ⁻¹).map`.
  have hinv00 : (symMat ℂ γ) 0 0 = (γ 1 1 : ℂ) := by
    simp [symMat, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.map_apply]
  have hinv01 : (symMat ℂ γ) 0 1 = -(γ 0 1 : ℂ) := by
    rw [symMat, Matrix.map_apply, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp
  have hinv10 : (symMat ℂ γ) 1 0 = -(γ 1 0 : ℂ) := by
    rw [symMat, Matrix.map_apply, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp
  have hinv11 : (symMat ℂ γ) 1 1 = (γ 0 0 : ℂ) := by
    simp [symMat, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.map_apply]
  -- The Möbius action point.
  have hw : ((γ • z : ℍ) : ℂ) =
      ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]; norm_cast
  -- The determinant relation `ad - bc = 1` over ℂ.
  have hdet : (γ 0 0 : ℂ) * (γ 1 1 : ℂ) - (γ 0 1 : ℂ) * (γ 1 0 : ℂ) = 1 := by
    have h : (γ 0 0) * (γ 1 1) - (γ 0 1) * (γ 1 0) = 1 := by
      have := γ.2; rwa [Matrix.det_fin_two] at this
    exact_mod_cast h
  -- Rewrite the substituted evaluation and reduce the two coordinates.
  rw [show symRep ℂ m γ P = ⟨substAlgHom (symMat ℂ γ) (P : MvPolynomial (Fin 2) ℂ),
      substAlgHom_isHomogeneous (symMat ℂ γ) P.2⟩ from Subtype.ext (by rw [symRep_apply]),
    evalSym1_substAlgHom, hinv00, hinv01, hinv10, hinv11, hw]
  -- `d·w - b = z/D` and `-c·w + a = 1/D` where `D = c·z + d`.
  have hc0 : (γ 1 1 : ℂ) * (((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)))
      + -(γ 0 1 : ℂ) = (z : ℂ) / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) := by
    rw [eq_div_iff hden, add_mul, mul_assoc, div_mul_cancel₀ _ hden]
    linear_combination (z : ℂ) * hdet
  have hc1 : -(γ 1 0 : ℂ) * (((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)))
      + (γ 0 0 : ℂ) = 1 / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) := by
    rw [eq_div_iff hden, add_mul, mul_assoc, div_mul_cancel₀ _ hden]
    linear_combination hdet
  rw [hc0, hc1]
  exact evalSym1_div m P z _ hden

/-! ## Descent to `𝕄` and the period map

The pre-descent functional `rawPairing f` descends to a functional on the modular-symbol module
`𝕄 N k = Coinvariants (modSymRep N (k-2).toNat)` precisely when it is `Γ₁(N)`-invariant, via
`Representation.Coinvariants.lift`.  The `Γ₁(N)`-invariance — Shimura (8.2.15)/(8.2.16), the cocycle
relation `𝔡(f)∘α = χ(α)𝔡(f)` — is the *modular-symbol invariance* of the period: it holds on the
augmentation subspace `Div⁰` and is exactly the statement that the period integral over the geodesic
`β → α` is unchanged under the simultaneous `γ`-action on the cusps and the `symRep`-action on the
coefficient.  Its algebraic core is `evalSym1_symRep_smul` (above); its analytic core is the
deformation/path-independence of the cusp-difference integral (Cauchy's theorem on the region between
the geodesics `β→α` and `γβ→γα`), which is the remaining analytic input.

We package the descent so that the period map is produced from any proof of this invariance. -/

/-- The `Γ₁(N)`-invariance hypothesis for the raw period pairing: for every `γ ∈ Γ₁(N)`,
precomposing `rawPairing f` with the diagonal action `modSymRep N (k-2).toNat γ` leaves it
unchanged.  This is Shimura (8.2.15)/(8.2.16); see the module docstring for its status. -/
def IsPeriodInvariant (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  ∀ γ : CongruenceSubgroup.Gamma1 N,
    (rawPairing f).comp (modSymRep N (k - 2).toNat γ) = rawPairing f

/-- **The period functional on `𝕄`, given the invariance.**  Descends `rawPairing f` to a
`ℤ`-linear functional on the modular-symbol module `𝕄 N k` via `Coinvariants.lift`.  This is the
period map evaluated at `f`, modulo the `Γ`-invariance input `hf`. -/
def periodMapOfInvariant (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : IsPeriodInvariant f) : 𝕄 N k →ₗ[ℤ] ℂ :=
  Representation.Coinvariants.lift (modSymRep N (k - 2).toNat) (rawPairing f) hf

@[simp]
theorem periodMapOfInvariant_mk (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : IsPeriodInvariant f) (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    periodMapOfInvariant f hf (𝕄.mk N k x) = rawPairing f x :=
  rfl

/-! ### `ℂ`-linearity of the raw pairing in the cusp form

The pairing is `ℂ`-linear in `f` (from `cuspToInftyIntegral_add_left`/`_smul_left`).  These are the
algebraic ingredients that make the assembled period map `ℂ`-linear in `f` — recorded so that the
final `periodMap : CuspForm ... →ₗ[ℂ] (𝕄 →ₗ[ℤ] ℂ)` is `ℂ`-linear (modulo the invariance input). -/

theorem rawBilin_add_left {m : ℕ} (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (D : Projectivization ℚ (Fin 2 → ℚ) →₀ ℤ) (P : SymPow ℤ m) :
    rawBilin (f + g) D P = rawBilin f D P + rawBilin g D P := by
  simp only [rawBilin, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.coe_sum,
    Finset.sum_apply, cuspFunctional, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [cuspValue_add_left, smul_add]

theorem rawBilin_smul_left {m : ℕ} (a : ℂ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (D : Projectivization ℚ (Fin 2 → ℚ) →₀ ℤ) (P : SymPow ℤ m) :
    rawBilin (a • f) D P = a • rawBilin f D P := by
  simp only [rawBilin, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.coe_sum,
    Finset.sum_apply, cuspFunctional, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [cuspValue_smul_left, smul_comm]

theorem rawPairing_add_left {m : ℕ} (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ m) :
    rawPairing (f + g) x = rawPairing f x + rawPairing g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul D P => simp only [rawPairing_tmul]; exact rawBilin_add_left f g _ P
  | add x y hx hy => simp only [map_add, hx, hy]; ring

theorem rawPairing_smul_left {m : ℕ} (a : ℂ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (x : Div0 ℤ ⊗[ℤ] SymPow ℤ m) :
    rawPairing (a • f) x = a • rawPairing f x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul D P => simp only [rawPairing_tmul]; exact rawBilin_smul_left a f _ P
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/-! ## The period map

Given the `Γ`-invariance for every cusp form (`hinv : ∀ f, IsPeriodInvariant f` — the one remaining
analytic input, Shimura (8.2.15)/(8.2.16)), we assemble the full period map

```
periodMap N k : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] (𝕄 N k →ₗ[ℤ] ℂ)
```

It is `ℂ`-linear in the cusp form `f` (`rawPairing_add_left`/`_smul_left`) and `ℤ`-linear on `𝕄`. -/

/-- **The period map** (Shimura §8.2), modulo the `Γ`-invariance input `hinv`: the `ℂ`-linear map
sending a cusp form `f` to the `ℤ`-linear functional `⟦((α)-(β)) ⊗ P⟧ ↦ ∫_β^α f(z)·P(z,1) dz` on the
modular-symbol module `𝕄 N k`.  Assembled from the cusp integrals via `Coinvariants.lift`. -/
def periodMap (hinv : ∀ f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k, IsPeriodInvariant f) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ] (𝕄 N k →ₗ[ℤ] ℂ) where
  toFun f := periodMapOfInvariant f (hinv f)
  map_add' f g := by
    apply Representation.Coinvariants.hom_ext
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, periodMapOfInvariant, Representation.Coinvariants.lift_mk]
    exact rawPairing_add_left f g x
  map_smul' a f := by
    apply Representation.Coinvariants.hom_ext
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, periodMapOfInvariant, Representation.Coinvariants.lift_mk,
      RingHom.id_apply]
    exact rawPairing_smul_left a f x

@[simp]
theorem periodMap_apply_mk
    (hinv : ∀ f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k, IsPeriodInvariant f)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (x : Div0 ℤ ⊗[ℤ] SymPow ℤ (k - 2).toNat) :
    periodMap hinv f (𝕄.mk N k x) = rawPairing f x :=
  rfl

end HeckeRing.GL2.ModularSymbols

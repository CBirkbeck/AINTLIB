/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p
import LeanModularForms.HeckeRIngs.GL2.HeckeT_n
import LeanModularForms.Modularforms.AtImInfty
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum

/-!
# Q-expansion coefficients under Hecke operators

Root-of-unity orthogonality and the Fourier coefficient formulas for
Hecke operators on modular forms, at the period-`N` (original) and
period-`1` (canonical Fourier) conventions.

## Main results

* `rootOfUnity_sum_eq` — `Σ_{b<n} ζ^{kb} = n` if `n ∣ k`, else `0`.
* `qParam_mul_nat`, `qParam_add` — q-parameter identities.
* `HeckeRing.GL2.fourierCoeff_heckeT_p` — for `f ∈ M_k(Γ₁(N), χ)` and prime
  `p ∤ N`, `a_m(T_p f) = a_{pm} + χ(p) · p^{k-1} · [p ∣ m] · a_{m/p}`.
* `HeckeRing.GL2.fourierCoeff_heckeT_p_period_one` — the same formula with
  every `coeff` evaluated at the canonical Fourier period `1`.
* `HeckeRing.GL2.qExpansion_one_heckeT_p_divN_coeff` —
  `a_m(T_p^{divN} f) = a_{pm}(f)` at period `1` (no-diamond case, `p ∣ M`).

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.2 Prop 5.2.2
* [Miy] Miyake, *Modular Forms*, §4.5 Thm 4.5.13 (period-1 Fourier
  convention)
-/

noncomputable section

open Complex Finset UpperHalfPlane

/-- Scaling the argument by `p`: `qParam h (p · z) = (qParam h z) ^ p`.
This is the key identity for computing q-expansions of `f(pτ)`. -/
theorem qParam_mul_nat (h : ℝ) (p : ℕ) (z : ℂ) :
    Function.Periodic.qParam h (↑p * z) = Function.Periodic.qParam h z ^ p := by
  simp only [Function.Periodic.qParam, ← exp_nat_mul]; congr 1; ring

/-- Shifting by `b` multiplies the q-parameter: `qParam h (z + b) = qParam h z · (qParam h b)`.
For integer `b`, this becomes multiplication by a root of unity when `h | b`. -/
theorem qParam_add (h : ℝ) (z w : ℂ) :
    Function.Periodic.qParam h (z + w) =
      Function.Periodic.qParam h z * Function.Periodic.qParam h w := by
  simp only [Function.Periodic.qParam, add_div, mul_add, exp_add]

namespace HeckeRing.GL2

open Matrix Subgroup.Commensurable Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
  ModularFormClass

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane Manifold

variable {N : ℕ}

/-- For a `ModularFormClass` form with strict period `h ∈ Γ.strictPeriods`, the q-expansion
sums to `f τ` for all `τ`. Wraps `UpperHalfPlane.hasSum_qExpansion`, deriving the periodicity,
holomorphy, and boundedness from the modular form structure. -/
private lemma hasSum_qExpansion_of_strictPeriod
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ k] {h : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (f : F)
    (τ : ℍ) : HasSum (fun m : ℕ ↦ (qExpansion h f).coeff m •
      Function.Periodic.qParam h ↑τ ^ m) (f τ) :=
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  UpperHalfPlane.hasSum_qExpansion hh (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ

private theorem coe_smul_T_p_upper (p : ℕ) (hp : 0 < p) (b : ℕ) (τ : ℍ) :
    (↑(glMap (T_p_upper p hp b) • τ) : ℂ) = ↑τ / ↑p + ↑b / ↑p := by
  simp only [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom]
  have hdet_pos : 0 < (glMap (T_p_upper p hp b)).det.val := by
    rw [show (glMap (T_p_upper p hp b)).det.val =
      algebraMap ℚ ℝ (T_p_upper p hp b).det.val from
      congr_arg Units.val (GeneralLinearGroup.map_det (algebraMap ℚ ℝ) _),
      GeneralLinearGroup.val_det_apply, T_p_upper_det]; simp; linarith [hp]
  simp only [UpperHalfPlane.σ, hdet_pos, ↓reduceIte, ContinuousAlgEquiv.refl_apply,
    show (↑(glMap (T_p_upper p hp b)) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1
      from by simp [glMap, T_p_upper],
    show (↑(glMap (T_p_upper p hp b)) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = b
      from by simp [glMap, T_p_upper],
    show (↑(glMap (T_p_upper p hp b)) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0
      from by simp [glMap, T_p_upper],
    show (↑(glMap (T_p_upper p hp b)) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = p
      from by simp [glMap, T_p_upper, Matrix.cons_val_one]]
  push_cast; ring

/-- Pointwise slash evaluation for `T_p_upper = [[1,b],[0,p]]`:
`(f ∣[k] T_p_upper b)(τ) = p⁻¹ * f((τ+b)/p)`.
Factor: `|det|^{k-1} * denom^{-k} = p^{k-1} * p^{-k} = p^{-1}`. -/
theorem slash_T_p_upper_eval (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (b : ℕ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) τ =
      (↑p : ℂ)⁻¹ * f (⟨(↑τ + ↑b) / ↑p, by
        simp; exact div_pos (by linarith [τ.im_pos])
          (Nat.cast_pos.mpr hp.pos)⟩ : ℍ) := by
  show ((f ∣[k] glMap (T_p_upper p hp.pos b)) τ) = _
  rw [ModularForm.slash_apply]
  have hdet_val : (glMap (T_p_upper p hp.pos b)).det.val = (p : ℝ) := by
    rw [show (glMap (T_p_upper p hp.pos b)).det.val =
      algebraMap ℚ ℝ (T_p_upper p hp.pos b).det.val from
      congr_arg Units.val (GeneralLinearGroup.map_det (algebraMap ℚ ℝ) _),
      GeneralLinearGroup.val_det_apply, T_p_upper_det]; simp
  have hdet_pos : 0 < (glMap (T_p_upper p hp.pos b)).det.val :=
    hdet_val ▸ Nat.cast_pos.mpr hp.pos
  have hσ : UpperHalfPlane.σ (glMap (T_p_upper p hp.pos b)) = ContinuousAlgEquiv.refl ℝ ℂ := by
    simp only [UpperHalfPlane.σ, hdet_pos, ↓reduceIte]
  have hdenom : UpperHalfPlane.denom (glMap (T_p_upper p hp.pos b)) ↑τ = ↑p := by
    simp [UpperHalfPlane.denom, glMap, T_p_upper, Matrix.cons_val_one]
  have hmob : (↑(glMap (T_p_upper p hp.pos b) • τ) : ℂ) = (↑τ + ↑b) / ↑p := by
    rw [coe_smul_T_p_upper p hp.pos b τ]; ring
  rw [hσ, ContinuousAlgEquiv.refl_apply, hdet_val, abs_of_pos (Nat.cast_pos.mpr hp.pos), hdenom]
  have hp_ne : (↑p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have halg (x : ℂ) : x * (↑p : ℂ) ^ (k - 1) * (↑p : ℂ) ^ (-k) = (↑p : ℂ)⁻¹ * x := by
    rw [mul_assoc, ← zpow_add₀ hp_ne]; simp [show (k - 1 + -k : ℤ) = -1 by omega]; ring
  have harg : (⟨(↑τ + ↑b) / ↑p, by
      simp; exact div_pos (by linarith [τ.im_pos])
        (Nat.cast_pos.mpr hp.pos)⟩ : ℍ) = glMap (T_p_upper p hp.pos b) • τ :=
    UpperHalfPlane.ext hmob.symm
  convert halg (f (glMap (T_p_upper p hp.pos b) • τ)) using 2 <;>
    first | exact congr_arg f harg | (push_cast; rfl)

private theorem qParam_smul_T_p_upper_pow (h : ℝ) (p : ℕ) (hp : 0 < p) (b : ℕ)
    (τ : ℍ) (n : ℕ) :
    Function.Periodic.qParam h ↑(glMap (T_p_upper p hp b) • τ) ^ n =
      Function.Periodic.qParam h ((↑τ : ℂ) / ↑p) ^ n *
        Function.Periodic.qParam h (1 / (↑p : ℂ)) ^ (n * b) := by
  conv_lhs => rw [show (↑(glMap (T_p_upper p hp b) • τ) : ℂ) = ↑τ / ↑p + ↑b / ↑p
    from coe_smul_T_p_upper p hp b τ]
  rw [qParam_add, show (↑b : ℂ) / ↑p = ↑b * (1 / ↑p) from by ring, qParam_mul_nat,
    mul_pow, ← pow_mul, mul_comm b n]

private theorem heckeT_p_ut_eq_inv_mul_sum (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (f : ℍ → ℂ) (τ : ℍ) :
    heckeT_p_ut k p hp.pos f τ =
      (↑p : ℂ)⁻¹ * ∑ b ∈ Finset.range p, f (⟨(↑τ + ↑b) / ↑p, by
        simp; exact div_pos (by linarith [τ.im_pos]) (Nat.cast_pos.mpr hp.pos)⟩ : ℍ) := by
  simp only [heckeT_p_ut, Finset.sum_apply, Finset.mul_sum]
  congr 1; ext b; exact slash_T_p_upper_eval k p hp b f τ

private theorem slash_T_p_lower_eval (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (g : ℍ → ℂ) (τ : ℍ) (pτ : ℍ) (hpτ : (↑pτ : ℂ) = ↑p * ↑τ) :
    (g ∣[k] (T_p_lower p hp.pos : GL (Fin 2) ℚ)) τ = (↑p : ℂ) ^ (k - 1) * g pτ := by
  show (g ∣[k] glMap (T_p_lower p hp.pos)) τ = (↑p : ℂ) ^ (k - 1) * g pτ
  rw [ModularForm.slash_apply]
  have hdet_val : (glMap (T_p_lower p hp.pos)).det.val = (p : ℝ) := by
    rw [show (glMap (T_p_lower p hp.pos)).det.val =
      algebraMap ℚ ℝ (T_p_lower p hp.pos).det.val from
      congr_arg Units.val (GeneralLinearGroup.map_det (algebraMap ℚ ℝ) _),
      GeneralLinearGroup.val_det_apply, T_p_lower_det]; simp
  have hdet_pos : 0 < (glMap (T_p_lower p hp.pos)).det.val := by
    rw [hdet_val]; exact Nat.cast_pos.mpr hp.pos
  have hσ : UpperHalfPlane.σ (glMap (T_p_lower p hp.pos)) = ContinuousAlgEquiv.refl ℝ ℂ := by
    simp only [UpperHalfPlane.σ, hdet_pos, ↓reduceIte]
  have hmob : glMap (T_p_lower p hp.pos) • τ = pτ := by
    ext : 1; rw [hpτ]; show (↑(glMap (T_p_lower p hp.pos) • τ) : ℂ) = ↑p * ↑τ
    simp only [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom,
      UpperHalfPlane.σ, hdet_pos, ↓reduceIte, ContinuousAlgEquiv.refl_apply,
      show (↑(glMap (T_p_lower p hp.pos)) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = p
        from by simp [glMap, T_p_lower],
      show (↑(glMap (T_p_lower p hp.pos)) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0
        from by simp [glMap, T_p_lower],
      show (↑(glMap (T_p_lower p hp.pos)) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0
        from by simp [glMap, T_p_lower],
      show (↑(glMap (T_p_lower p hp.pos)) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1
        from by simp [glMap, T_p_lower, Matrix.cons_val_one]]
    push_cast; ring
  have hdenom : UpperHalfPlane.denom (glMap (T_p_lower p hp.pos)) ↑τ = 1 := by
    simp [UpperHalfPlane.denom, glMap, T_p_lower, Matrix.cons_val_one]
  rw [hσ, ContinuousAlgEquiv.refl_apply, hmob, hdenom, one_zpow, mul_one,
    hdet_val, abs_of_pos (Nat.cast_pos.mpr hp.pos)]
  push_cast; ring

private theorem f_smul_T_p_upper_eq (p : ℕ) (hp : Nat.Prime p) (f : ℍ → ℂ)
    (b : ℕ) (τ : ℍ) :
    f (glMap (T_p_upper p hp.pos b) • τ) =
      f (⟨(↑τ + ↑b) / ↑p, by
        simp; exact div_pos (by linarith [τ.im_pos]) (Nat.cast_pos.mpr hp.pos)⟩ : ℍ) := by
  congr 1; ext : 1; rw [coe_smul_T_p_upper p hp.pos b τ]; push_cast; ring

private theorem sum_qParam_pow_period_one {p : ℕ} (hp : Nat.Prime p) (n : ℕ) :
    ∑ b ∈ Finset.range p, Function.Periodic.qParam (1 : ℝ) (1 / (↑p : ℂ)) ^ (n * b) =
      if p ∣ n then (↑p : ℂ) else 0 := by
  set ζ := Function.Periodic.qParam (1 : ℝ) (1 / (↑p : ℂ)) with hζ_def
  have hζ_prim : IsPrimitiveRoot ζ p := by
    rw [hζ_def, Function.Periodic.qParam]
    convert Complex.isPrimitiveRoot_exp p hp.ne_zero using 1; push_cast; ring
  split_ifs with hpn
  · simp_rw [pow_mul ζ n, (hζ_prim.pow_eq_one_iff_dvd n).mpr hpn, one_pow,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · have hζn_ne : ζ ^ n ≠ 1 := mt (hζ_prim.pow_eq_one_iff_dvd n).mp hpn
    simp_rw [pow_mul ζ n]
    rw [geom_sum_eq hζn_ne, show (ζ ^ n) ^ p = 1 from by
      rw [← pow_mul, mul_comm, pow_mul, hζ_prim.pow_eq_one, one_pow]]
    simp

private theorem hasSum_heckeT_p_ut_period_one (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (f : ℍ → ℂ) (a : ℕ → ℂ) (τ : ℍ)
    (hf_hs : ∀ σ : ℍ, HasSum
      (fun n ↦ a n • Function.Periodic.qParam (1 : ℝ) ↑σ ^ n) (f σ)) :
    HasSum (fun n ↦ a (p * n) • Function.Periodic.qParam (1 : ℝ) ↑τ ^ n)
      (heckeT_p_ut k p hp.pos f τ) := by
  set q := Function.Periodic.qParam (1 : ℝ) ↑τ
  rw [heckeT_p_ut_eq_inv_mul_sum k p hp f τ]
  have hinj : Function.Injective (p * · : ℕ → ℕ) := mul_right_injective₀ hp.ne_zero
  set w := Function.Periodic.qParam (1 : ℝ) ((↑τ : ℂ) / ↑p) with hw_def
  set ζ := Function.Periodic.qParam (1 : ℝ) (1 / (↑p : ℂ))
  have hp_ne : (↑p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hw_pow_p : w ^ p = q := by rw [hw_def, ← qParam_mul_nat]; congr 1; field_simp
  have h_rewritten : HasSum
      (fun n ↦ a n • w ^ n * ∑ b ∈ Finset.range p, ζ ^ (n * b))
      (∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ)) := by
    convert hasSum_sum (fun b _ ↦ hf_hs (glMap (T_p_upper p hp.pos b) • τ)) using 2 with n
    trans (∑ b ∈ Finset.range p, a n * (w ^ n * ζ ^ (n * b)))
    · rw [smul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum, mul_assoc]
    · exact Finset.sum_congr rfl fun b _ ↦ by
        rw [qParam_smul_T_p_upper_pow (1 : ℝ) p hp.pos b τ n, smul_eq_mul]
  have h_ind : HasSum (fun n' ↦ (if p ∣ n' then a n' • w ^ n' else 0))
      ((↑p : ℂ)⁻¹ * ∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ)) := by
    rw [show (↑p : ℂ)⁻¹ * ∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ) =
        (↑p : ℂ)⁻¹ • ∑ b ∈ Finset.range p, f (glMap (T_p_upper p hp.pos b) • τ) from by
      simp [smul_eq_mul]]
    have h_scaled := h_rewritten.const_smul (↑p : ℂ)⁻¹
    unfold HasSum at h_scaled ⊢
    refine h_scaled.congr fun s ↦ ?_
    congr 1; ext n
    simp only [smul_eq_mul]
    rw [sum_qParam_pow_period_one hp n]
    split_ifs with h
    · rw [mul_comm (a n * w ^ n), ← mul_assoc, inv_mul_cancel₀ hp_ne, one_mul]
    · ring
  rw [← hinj.hasSum_iff (fun x hx ↦ by
    simp only [Set.mem_range, not_exists] at hx
    simp [show ¬p ∣ x from fun ⟨k, hk⟩ ↦ hx k (by omega)])] at h_ind
  simp only [Function.comp_def, show ∀ m, p ∣ p * m from dvd_mul_right p, if_true] at h_ind
  convert h_ind using 2 with m
  · rw [smul_eq_mul, smul_eq_mul, pow_mul, hw_pow_p]
  · exact Finset.sum_congr rfl fun b _ ↦ (f_smul_T_p_upper_eq p hp f b τ).symm

private theorem hasSum_heckeT_p_of_ut {N : ℕ} [NeZero N] (k : ℤ) {p : ℕ}
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ)
    (h : ℝ) (a : ℕ → ℂ) (τ : ℍ)
    (hf_hs : ∀ σ : ℍ, HasSum (fun n ↦ a n • Function.Periodic.qParam h ↑σ ^ n) (f σ))
    (h_upper : HasSum (fun n ↦ a (p * n) • Function.Periodic.qParam h ↑τ ^ n)
      (heckeT_p_ut k p hp.pos (⇑f) τ)) :
    HasSum (fun n : ℕ ↦ ((a (p * n) + (↑p : ℂ) ^ (k - 1) *
        ↑(χ (ZMod.unitOfCoprime p hpN)) * if p ∣ n then a (n / p) else 0)) •
      Function.Periodic.qParam h ↑τ ^ n) ((heckeT_p k p hp hpN f) τ) := by
  set q := Function.Periodic.qParam h ↑τ
  set χp := (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ)
  set pk := (↑p : ℂ) ^ (k - 1)
  have hpτ_im : 0 < ((p : ℂ) * ↑τ).im := by
    simp [Complex.mul_im]; exact mul_pos (Nat.cast_pos.mpr hp.pos) τ.im_pos
  set pτ : ℍ := ⟨(p : ℂ) * ↑τ, hpτ_im⟩
  have hinj : Function.Injective (p * · : ℕ → ℕ) := mul_right_injective₀ hp.ne_zero
  have h_lower_ind : HasSum
      (fun m ↦ (if p ∣ m then a (m / p) else 0) • q ^ m) (f pτ) := by
    refine (hinj.hasSum_iff (fun x hx ↦ ?_)).mp ?_
    · simp only [Set.mem_range, not_exists] at hx
      simp [show ¬(p ∣ x) from fun ⟨k, hk⟩ ↦ hx k (by omega)]
    · show HasSum ((fun m ↦ (if p ∣ m then a (m / p) else 0) • q ^ m) ∘ (p * ·)) (f pτ)
      simp only [Function.comp_def, show ∀ n, p ∣ p * n from dvd_mul_right p,
        if_true, Nat.mul_div_cancel_left _ hp.pos]
      have := hf_hs pτ; simp only [pτ, qParam_mul_nat] at this
      convert this using 2 with n; rw [← pow_mul]
  have h_diamond : ∀ σ : ℍ, (diamondOp k (ZMod.unitOfCoprime p hpN) f) σ = χp • f σ := by
    intro σ
    have hd := (mem_modFormCharSpace_iff k χ f).mp hf (ZMod.unitOfCoprime p hpN)
    change (diamondOpHom k (ZMod.unitOfCoprime p hpN) f) σ = χp • f σ
    rw [hd]; rfl
  have h_slash_lower : (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      (T_p_lower p hp.pos : GL (Fin 2) ℚ)) τ = pk * χp * f pτ := by
    rw [slash_T_p_lower_eval k p hp _ τ pτ rfl, h_diamond pτ, smul_eq_mul]; ring
  have h_lower_scaled : HasSum
      (fun m ↦ (pk * χp * if p ∣ m then a (m / p) else 0) • q ^ m) (pk * χp * f pτ) := by
    have := h_lower_ind.const_smul (pk * χp)
    simp only [smul_eq_mul] at this ⊢
    convert this using 2 with m; split_ifs <;> ring
  convert h_upper.add h_lower_scaled using 1
  · ext n; simp only [smul_eq_mul]; split_ifs <;> ring
  · show heckeT_p_fun k p hp hpN f τ = heckeT_p_ut k p hp.pos (⇑f) τ + pk * χp * f pτ
    simp only [heckeT_p_fun, Pi.add_apply, h_slash_lower]

/-- **Fourier coefficient formula for `T_p` at period 1** (Diamond–Shurman
Prop 5.2.2, canonical period). The period-`1` sibling of `fourierCoeff_heckeT_p`:
since every `Γ₁(N)`-form is `1`-periodic, the canonical `q`-expansion uses
period `1`, and `a_m(T_p f) = a_{pm}(f) + p^{k-1} · χ(p) · a_{m/p}(f)` (the last
term present only when `p ∣ m`). -/
theorem fourierCoeff_heckeT_p_period_one [NeZero N] (k : ℤ) {p : ℕ}
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) (m : ℕ) :
    (qExpansion (1 : ℝ) (heckeT_p k p hp hpN f)).coeff m =
      (qExpansion (1 : ℝ) f).coeff (p * m) +
        (↑p : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime p hpN)) *
          (if p ∣ m then (qExpansion (1 : ℝ) f).coeff (m / p) else 0) := by
  have h1_pos : (0 : ℝ) < 1 := one_pos
  have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
      strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  set a := fun n ↦ (qExpansion (1 : ℝ) (⇑f)).coeff n
  have hf_hs : ∀ σ : ℍ, HasSum (fun n ↦ a n • (Function.Periodic.qParam (1 : ℝ) ↑σ) ^ n)
      (f σ) := hasSum_qExpansion_of_strictPeriod h1_pos h1_period f
  suffices key : ∀ τ : ℍ, HasSum
      (fun n : ℕ ↦ (a (p * n) + (↑p : ℂ) ^ (k - 1) *
          ↑(χ (ZMod.unitOfCoprime p hpN)) * if p ∣ n then a (n / p) else 0) •
        Function.Periodic.qParam (1 : ℝ) ↑τ ^ n) ((heckeT_p k p hp hpN f) τ) by
    exact (ModularFormClass.qExpansion_coeff_unique h1_pos h1_period key m).symm
  exact fun τ ↦ hasSum_heckeT_p_of_ut k hp hpN χ hf (1 : ℝ) a τ hf_hs
    (hasSum_heckeT_p_ut_period_one k hp (⇑f) a τ hf_hs)

/-- **Fourier coefficient formula for `T_p` on forms with `p ∣ M` at period 1**
(Diamond–Shurman §5.2, no-diamond case). For `f ∈ M_k(Γ₁(M))` and a prime `p ∣ M`,
the level-divisible operator `heckeT_p_divN` is the purely upper-triangular sum
(no diamond term, the Nebentypus being undefined at `p`), so at period `1` its
`m`-th Fourier coefficient is `a_{pm}(f)`. -/
theorem qExpansion_one_heckeT_p_divN_coeff
    {M : ℕ} [NeZero M] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hpM : ¬ Nat.Coprime p M)
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (m : ℕ) :
    (qExpansion (1 : ℝ) (heckeT_p_divN k p hp hpM f)).coeff m =
      (qExpansion (1 : ℝ) f).coeff (p * m) := by
  have h1_pos : (0 : ℝ) < 1 := one_pos
  have h1_period : (1 : ℝ) ∈ ((Gamma1 M).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 M).map (mapGL ℝ) = (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) from rfl,
      strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  set a := fun n ↦ (qExpansion (1 : ℝ) (⇑f)).coeff n
  have hf_hs : ∀ σ : ℍ, HasSum (fun n ↦ a n • (Function.Periodic.qParam (1 : ℝ) ↑σ) ^ n)
      (f σ) := hasSum_qExpansion_of_strictPeriod h1_pos h1_period f
  refine (ModularFormClass.qExpansion_coeff_unique (c := fun n ↦ a (p * n))
    h1_pos h1_period (fun τ ↦ ?_) m).symm
  exact hasSum_heckeT_p_ut_period_one k hp (⇑f) a τ hf_hs

end HeckeRing.GL2

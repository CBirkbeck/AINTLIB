/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.BigOperators.Finprod
import LeanModularForms.ForMathlib.CanonicalReps

/-!
# The Valence Formula for Modular Forms

The textbook orbit-sum form of the valence formula for weight-`k` modular forms on `SL₂(ℤ)`:

$$\operatorname{ord}_\infty(f) + \tfrac{1}{2}\operatorname{ord}_i(f)
  + \tfrac{1}{3}\operatorname{ord}_\rho(f)
  + \sum_{q\;\text{non-ell}} \operatorname{ord}_q(f) = \frac{k}{12}$$

## Main definitions

* `ordOrbitQ` — the order of vanishing on non-elliptic orbits, cast to `ℂ`

## Main results

* `fd_orbit_i_eq_i` — a point of `𝒟` in the `i`-orbit equals `i`
* `fd_orbit_rho_eq` — a point of `𝒟` in the `ρ`-orbit equals `ρ` or `ρ + 1`
* `orb_repCanon_nonEll` — `repCanon` representatives have non-elliptic orbits
* `finsum_nonell_eq_repCanon_sum` — the `∑ᶠ` over non-elliptic orbits equals the
  `repCanon` Finset sum
* `repCanon_sum_split` — the `repCanon` sum splits into strict interior, left vertical
  edge, and left arc
* `valence_formula_textbook_orbit_finsum` — the valence formula in literal orbit-sum form,
  conditional on the core identity (supplied as the hypothesis `h_core`)
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-- The order of vanishing on non-elliptic orbits, cast to `ℂ`. -/
def ordOrbitQ (q : NonEllOrbitFM) : ℂ := (ordOrbitFM f q.val : ℂ)

private lemma ellipticPointI'_coe : (ellipticPointI' : ℂ) = Complex.I := rfl
private lemma ellipticPointI'_im : (ellipticPointI' : ℍ).im = 1 := Complex.I_im

private lemma ellipticPointRho'_re : (ellipticPointRho' : ℍ).re = -1/2 := by
  change (-1/2 + (Real.sqrt 3 / 2) * I : ℂ).re = -1/2; simp

private lemma ellipticPointRho'_im : (ellipticPointRho' : ℍ).im = Real.sqrt 3 / 2 := by
  change (-1/2 + (Real.sqrt 3 / 2) * I : ℂ).im = Real.sqrt 3 / 2; simp

private lemma ellipticPointRhoPlusOne'_re : (ellipticPointRhoPlusOne' : ℍ).re = 1/2 := by
  change (1/2 + (Real.sqrt 3 / 2) * I : ℂ).re = 1/2; simp

private lemma ellipticPointRhoPlusOne'_im :
    (ellipticPointRhoPlusOne' : ℍ).im = Real.sqrt 3 / 2 := by
  change (1/2 + (Real.sqrt 3 / 2) * I : ℂ).im = Real.sqrt 3 / 2; simp

omit f hf in
private lemma sl2_det (g : SL(2, ℤ)) :
    (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
    (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 *
      (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
  rw [← Matrix.det_fin_two]; exact g.prop

omit f hf in
private lemma denom_at_I (g : SL(2, ℤ)) :
    UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (Complex.I) =
    ↑((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) * Complex.I +
    ↑((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) := by
  simp [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.toGL, Matrix.SpecialLinearGroup.map]

omit f hf in
private lemma normSq_denom_at_I (g : SL(2, ℤ)) :
    Complex.normSq (UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (Complex.I)) =
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 +
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ^ 2 := by
  simp [denom_at_I, Complex.normSq_apply]; ring

omit f hf in
private lemma normSq_denom_eq_one_of_smul_i_in_fd (g : SL(2, ℤ))
    (h_fd : g • ellipticPointI' ∈ 𝒟) :
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 +
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ^ 2 = 1 := by
  let c := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  let d := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have h_im := ModularGroup.im_smul_eq_div_normSq g ellipticPointI'
  rw [ellipticPointI'_im, ellipticPointI'_coe, normSq_denom_at_I] at h_im
  have h_gt : (1 : ℝ)/2 < 1 / ((c : ℝ) ^ 2 + (d : ℝ) ^ 2) := h_im ▸ fd_im_gt_halfFM _ h_fd
  have h_ge : c ^ 2 + d ^ 2 ≥ 1 := by
    by_contra! h
    have hc0 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by nlinarith [sq_nonneg c]
    have hd0 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 0 := by nlinarith [sq_nonneg d]
    simpa [hc0, hd0] using sl2_det g
  have h_pos : (c : ℝ) ^ 2 + (d : ℝ) ^ 2 > 0 := by
    exact_mod_cast show (0 : ℤ) < c ^ 2 + d ^ 2 by omega
  have h_lt2 : (c : ℝ) ^ 2 + (d : ℝ) ^ 2 < 2 := by
    nlinarith [mul_lt_mul_of_pos_right h_gt h_pos, div_mul_cancel₀ (1 : ℝ) h_pos.ne']
  have : c ^ 2 + d ^ 2 < 2 := by exact_mod_cast h_lt2
  exact_mod_cast show c ^ 2 + d ^ 2 = 1 by omega

omit f hf in
private lemma re_smul_ellipticPointI (g : SL(2, ℤ)) :
    (g • ellipticPointI').re =
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 +
     (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) /
    (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 +
     ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ^ 2) := by
  change (↑(g • ellipticPointI') : ℂ).re = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, ellipticPointI'_coe]
  simp only [algebraMap_int_eq, Int.coe_castRingHom]
  rw [Complex.div_re, Complex.normSq_apply]; simp; ring

omit f hf in
/-- If `p ∈ 𝒟` and `orbFM p = oiFM`, then `p = i`. -/
theorem fd_orbit_i_eq_i (p : ℍ) (hp : p ∈ 𝒟) (horb : orbFM p = oiFM) :
    p = ellipticPointI' := by
  obtain ⟨g, hg⟩ := (Quotient.exact' horb : ∃ g : SL(2, ℤ), g • ellipticPointI' = p)
  subst hg
  set c := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set d := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  set a := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set b := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  have h_cd1 := normSq_denom_eq_one_of_smul_i_in_fd g hp
  have h_im := ModularGroup.im_smul_eq_div_normSq g ellipticPointI'
  rw [ellipticPointI'_im, ellipticPointI'_coe, normSq_denom_at_I, h_cd1, div_one] at h_im
  have h_re := re_smul_ellipticPointI g
  rw [h_cd1, div_one] at h_re
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (g • ellipticPointI').re = (n : ℝ) :=
    ⟨a * c + b * d, by rw [h_re]; push_cast; ring⟩
  have h_n_zero : n = 0 := by
    by_contra h_ne
    have h2 := hp.2; rw [hn] at h2
    linarith [show (1 : ℝ) ≤ |(n : ℝ)| from mod_cast Int.one_le_abs h_ne]
  refine UpperHalfPlane.ext_re_im ?_ (by linarith [h_im, ellipticPointI'_im])
  rw [hn, h_n_zero, Int.cast_zero]
  exact Complex.I_re.symm

omit f hf in
private lemma denom_at_rho (g : SL(2, ℤ)) :
    UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (ellipticPointRho' : ℍ) =
    ↑((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) *
      (-1/2 + (Real.sqrt 3 / 2) * I) +
    ↑((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) := by
  simp [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.toGL,
    Matrix.SpecialLinearGroup.map, ellipticPointRho']

omit f hf in
private lemma normSq_denom_at_rho (g : SL(2, ℤ)) :
    Complex.normSq (UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (ellipticPointRho' : ℍ)) =
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 -
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) +
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ^ 2 := by
  simp [denom_at_rho, Complex.normSq_apply]
  ring_nf
  nlinarith [Real.mul_self_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]

omit f hf in
private lemma normSq_denom_eq_one_of_smul_rho_in_fd (g : SL(2, ℤ))
    (h_fd : g • ellipticPointRho' ∈ 𝒟) :
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 -
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) +
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ^ 2 = 1 := by
  let c := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  let d := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have h_im := ModularGroup.im_smul_eq_div_normSq g ellipticPointRho'
  rw [ellipticPointRho'_im, normSq_denom_at_rho] at h_im
  have h_gt : (1 : ℝ)/2 < (g • ellipticPointRho').im := fd_im_gt_halfFM _ h_fd
  rw [h_im] at h_gt
  have h_pos : (c : ℝ) ^ 2 - (c : ℝ) * (d : ℝ) + (d : ℝ) ^ 2 > 0 := by
    by_contra! h
    have : Real.sqrt 3 / 2 / ((c : ℝ) ^ 2 - (c : ℝ) * (d : ℝ) + (d : ℝ) ^ 2) ≤ 0 :=
      div_nonpos_iff.mpr (Or.inl ⟨by positivity, h⟩)
    linarith
  have h_lt2 : (c : ℝ) ^ 2 - (c : ℝ) * (d : ℝ) + (d : ℝ) ^ 2 < 2 := by
    nlinarith [Real.mul_self_sqrt (show (3 : ℝ) ≥ 0 by norm_num),
      mul_lt_mul_of_pos_right h_gt h_pos,
      div_mul_cancel₀ ((Real.sqrt 3 / 2 : ℝ)) h_pos.ne',
      sq_nonneg (Real.sqrt 3 - 2)]
  have : (0 : ℤ) < c ^ 2 - c * d + d ^ 2 := by exact_mod_cast h_pos
  have : c ^ 2 - c * d + d ^ 2 < (2 : ℤ) := by exact_mod_cast h_lt2
  exact_mod_cast show c ^ 2 - c * d + d ^ 2 = 1 by omega

omit f hf in
private lemma abs_re_eq_half_of_smul_rho_in_fd (g : SL(2, ℤ))
    (h_fd : g • ellipticPointRho' ∈ 𝒟)
    (h_cd1 : ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 -
      ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) *
        ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) +
      ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ^ 2 = 1) :
    |(g • ellipticPointRho').re| = 1/2 := by
  have h_im_eq : (g • ellipticPointRho').im = Real.sqrt 3 / 2 := by
    rw [ModularGroup.im_smul_eq_div_normSq, ellipticPointRho'_im, normSq_denom_at_rho,
      h_cd1, div_one]
  have h_im_sq : (g • ellipticPointRho').im ^ 2 = 3/4 := by
    rw [h_im_eq]; nlinarith [Real.mul_self_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
  have h_nsq : (g • ellipticPointRho').re ^ 2 +
      (g • ellipticPointRho').im ^ 2 ≥ 1 := by
    have h_apply := Complex.normSq_apply (↑(g • ellipticPointRho') : ℂ)
    rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h_apply
    nlinarith [h_fd.1, h_apply]
  refine le_antisymm h_fd.2 ?_
  by_contra! h_lt
  nlinarith [sq_abs (g • ellipticPointRho').re,
    abs_nonneg (g • ellipticPointRho').re, h_im_sq, h_nsq]

omit f hf in
/-- If `p ∈ 𝒟` and `orbFM p = orhoFM`, then `p = ρ` or `p = ρ+1`. -/
theorem fd_orbit_rho_eq (p : ℍ) (hp : p ∈ 𝒟) (horb : orbFM p = orhoFM) :
    p = ellipticPointRho' ∨ p = ellipticPointRhoPlusOne' := by
  obtain ⟨g, hg⟩ := (Quotient.exact' horb : ∃ g : SL(2, ℤ), g • ellipticPointRho' = p)
  rw [← hg] at hp ⊢
  have h_cd1 := normSq_denom_eq_one_of_smul_rho_in_fd g hp
  have h_im : (g • ellipticPointRho').im = Real.sqrt 3 / 2 := by
    rw [ModularGroup.im_smul_eq_div_normSq, ellipticPointRho'_im, normSq_denom_at_rho,
      h_cd1, div_one]
  have h_re_abs := abs_re_eq_half_of_smul_rho_in_fd g hp h_cd1
  rcases le_or_gt (g • ellipticPointRho').re 0 with h_neg | h_pos
  · exact .inl <| UpperHalfPlane.ext_re_im
      (by linarith [abs_of_nonpos h_neg, ellipticPointRho'_re])
      (by linarith [h_im, ellipticPointRho'_im])
  · exact .inr <| UpperHalfPlane.ext_re_im
      (by linarith [abs_of_pos h_pos, ellipticPointRhoPlusOne'_re])
      (by linarith [h_im, ellipticPointRhoPlusOne'_im])

/-- Elements of `repCanon` map to non-elliptic orbits. -/
theorem orb_repCanon_nonEll (p : ℍ) (hp : p ∈ repCanon f hf) :
    orbFM p ≠ oiFM ∧ orbFM p ≠ orhoFM := by
  have ⟨hne_i, hne_rho, hne_rho1⟩ := repCanon_ne_elliptic f hf p hp
  have hp_fd := repCanon_mem_fd f hf hp
  exact ⟨fun h ↦ hne_i (fd_orbit_i_eq_i p hp_fd h),
    fun h ↦ (fd_orbit_rho_eq p hp_fd h).elim hne_rho hne_rho1⟩

/-- The `∑ᶠ` over non-elliptic orbits equals the `repCanon` Finset sum. -/
theorem finsum_nonell_eq_repCanon_sum :
    ∑ᶠ (q : NonEllOrbitFM), ordOrbitQ f q =
    ∑ s ∈ repCanon f hf, (orderOfVanishingAt' (⇑f) s : ℂ) := by
  set S := (finite_support_ordOrbit_nonEllFM f hf).toFinset
  rw [finsum_eq_sum_of_support_subset _ (fun q hq ↦ by
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact Int.cast_ne_zero.mp (Function.mem_support.mp hq))]
  set R := repCanon f hf
  set φ : (p : ℍ) → p ∈ R → NonEllOrbitFM :=
    fun p hp ↦ ⟨orbFM p, orb_repCanon_nonEll f hf p hp⟩ with hφ_def
  have h_im : ∀ p (hp : p ∈ R), φ p hp ∈ S := fun p hp ↦ by
    rw [Set.Finite.mem_toFinset]
    change ordOrbitFM f (orbFM p) ≠ 0
    rw [ordOrbit_mkFM]
    have hp_s₀ := repCanon_mem_s₀ f hf hp
    rw [s₀FM, Set.Finite.mem_toFinset] at hp_s₀
    exact hp_s₀.2
  have h_surj : ∀ q ∈ S, ∃ p, ∃ hp : p ∈ R, φ p hp = q := fun q hq ↦ by
    obtain ⟨p, hp_mem, hp_orb⟩ := exists_repCanon_of_nonEllOrbit f hf q
      ((Set.Finite.mem_toFinset _).mp hq)
    exact ⟨p, hp_mem, Subtype.ext hp_orb⟩
  exact (Finset.sum_bij φ h_im
    (fun _ h₁ _ h₂ heq ↦ orb_injOn_repCanon f hf h₁ h₂ (congr_arg Subtype.val heq))
    h_surj (fun p hp ↦ by
      simp only [ordOrbitQ, hφ_def]
      exact_mod_cast (ordOrbit_mkFM f p).symm)).symm

/-- The `repCanon` sum splits into strict interior + left vertical + left arc. -/
theorem repCanon_sum_split :
    ∑ s ∈ repCanon f hf, (orderOfVanishingAt' (⇑f) s : ℂ) =
    ∑ s ∈ repStrict f hf, (orderOfVanishingAt' (⇑f) s : ℂ) +
    ∑ s ∈ repLeftVert f hf, (orderOfVanishingAt' (⇑f) s : ℂ) +
    ∑ s ∈ repLeftArc f hf, (orderOfVanishingAt' (⇑f) s : ℂ) := by
  rw [repCanon, Finset.sum_union (disjoint_union_repLeftArc f hf),
    Finset.sum_union (disjoint_repStrict_repLeftVert f hf)]

include hf in
/-- **The Valence Formula** for weight-`k` modular forms on `SL₂(ℤ)`, in textbook orbit-sum
form, conditional on the core identity (supplied as the hypothesis `h_core`).

The core identity states that for any finite set `S ⊆ 𝒟` capturing all zeros,
the explicit coefficient expansion holds. This is proved separately via contour
integration of the logarithmic derivative along the boundary of the fundamental domain. -/
theorem valence_formula_textbook_orbit_finsum
    (h_core : ∀ (S : Finset UpperHalfPlane),
      (∀ p ∈ S, p ∈ 𝒟) →
      (∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) →
      (orderAtCusp' f : ℂ) +
      (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
      (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
      ∑ s ∈ S.filter (fun p ↦
          p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne' ∧
          ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2),
        ↑(orderOfVanishingAt' (⇑f) s) +
      ∑ s ∈ sLeftVertFM S, ↑(orderOfVanishingAt' (⇑f) s) +
      ∑ s ∈ S.filter (fun p ↦
          p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
        ↑(orderOfVanishingAt' (⇑f) s) =
      (k : ℂ) / 12) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ᶠ (q : NonEllOrbitFM), ordOrbitQ f q =
    (k : ℂ) / 12 := by
  rw [finsum_nonell_eq_repCanon_sum f hf, repCanon_sum_split f hf]
  unfold repStrict repLeftVert repLeftArc
  linear_combination
    h_core (s₀FM f hf) (s₀FM_mem_fd f hf) (s₀FM_complete f hf)

end

/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.OrbitPairing

/-!
# Canonical Representatives for Non-Elliptic Orbits

Every non-elliptic orbit with nonzero order of vanishing has a representative in the canonical
finsets used by `valence_formula_orbit_sum_s₀`.

## Main Definitions

* `repStrict` — strict interior representatives (non-elliptic, ‖p‖ > 1, |re| < 1/2)
* `repLeftVert` — left vertical edge representatives (re = -1/2, ‖p‖ > 1)
* `repLeftArc` — left arc representatives (‖p‖ = 1, re < 0, not ρ)
* `repCanon` — union of the three canonical sets

## Main Results

* `repCanon_mem_s₀` — elements of `repCanon` lie in `s₀`
* `repCanon_mem_fd` — elements of `repCanon` lie in `𝒟`
* `repCanon_ne_elliptic` — elements are distinct from all three elliptic points
* `disjoint_repStrict_repLeftVert` — `repStrict` and `repLeftVert` are disjoint
* `disjoint_union_repLeftArc` — `repStrict ∪ repLeftVert` and `repLeftArc` are disjoint
* `exists_repCanon_of_nonEllOrbit` — every non-elliptic orbit with nonzero order has a
  representative in `repCanon`
* `orb_injOn_repCanon` — the orbit map is injective on `repCanon`
-/

open Complex Set CongruenceSubgroup
open scoped UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-! ### Canonical representative finsets -/

/-- Strict interior representatives: points in `s₀` with `‖p‖ > 1`, `|re| < 1/2`,
not elliptic. -/
noncomputable def repStrict : Finset ℍ :=
  (s₀FM f hf).filter (fun p ↦ p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧
    p ≠ ellipticPointRhoPlusOne' ∧ ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2)

/-- Left vertical edge representatives: points in `s₀` with `re = -1/2`, `‖p‖ > 1`. -/
noncomputable def repLeftVert : Finset ℍ := sLeftVertFM (s₀FM f hf)

/-- Left arc representatives: points in `s₀` with `‖p‖ = 1`, `re < 0`, not `ρ`. -/
noncomputable def repLeftArc : Finset ℍ :=
  (s₀FM f hf).filter (fun p ↦ p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)

/-- The canonical representative finset: union of strict interior, left vertical, and left arc. -/
noncomputable def repCanon : Finset ℍ :=
  repStrict f hf ∪ repLeftVert f hf ∪ repLeftArc f hf

/-! ### Membership in s₀FM -/

/-- Every element of `repCanon` lies in `s₀`. -/
theorem repCanon_mem_s₀ {p : ℍ} (hp : p ∈ repCanon f hf) :
    p ∈ s₀FM f hf := by
  simp only [repCanon, Finset.mem_union] at hp
  rcases hp with (h | h) | h <;> exact (Finset.mem_filter.mp h).1

/-- Every element of `repCanon` lies in the fundamental domain `𝒟`. -/
theorem repCanon_mem_fd {p : ℍ} (hp : p ∈ repCanon f hf) : p ∈ 𝒟 :=
  s₀FM_mem_fd f hf p (repCanon_mem_s₀ f hf hp)

/-! ### Distinctness from elliptic points -/

/-- Elements of `repCanon` are distinct from all three elliptic points. -/
theorem repCanon_ne_elliptic (p : ℍ) (hp : p ∈ repCanon f hf) :
    p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne' := by
  have hI : (ellipticPointI' : ℂ).re = 0 := Complex.I_re
  have hR1 : (ellipticPointRhoPlusOne' : ℂ).re = 1/2 := by simp [ellipticPointRhoPlusOne']
  simp only [repCanon, Finset.mem_union] at hp
  rcases hp with (h | h) | h
  · obtain ⟨_, h1, h2, h3, _⟩ := Finset.mem_filter.mp h
    exact ⟨h1, h2, h3⟩
  · have h2 := (Finset.mem_filter.mp h).2
    refine ⟨fun heq ↦ ?_, fun heq ↦ ?_, fun heq ↦ ?_⟩ <;> rw [heq] at h2
    · linarith [h2.1]
    · linarith [h2.2, ellipticPointRho_norm]
    · linarith [h2.1]
  · have h2 := (Finset.mem_filter.mp h).2
    refine ⟨fun heq ↦ ?_, h2.1, fun heq ↦ ?_⟩ <;> rw [heq] at h2
    · linarith [h2.2.2]
    · linarith [h2.2.2]

/-! ### Disjointness -/

/-- `repStrict` and `repLeftVert` are disjoint. -/
theorem disjoint_repStrict_repLeftVert :
    Disjoint (repStrict f hf) (repLeftVert f hf) := by
  refine Finset.disjoint_left.mpr fun p hp_s hp_lv ↦ ?_
  have h1 : |(p : ℂ).re| < 1/2 := (Finset.mem_filter.mp hp_s).2.2.2.2.2
  rw [(Finset.mem_filter.mp hp_lv).2.1] at h1
  norm_num at h1

/-- `repStrict ∪ repLeftVert` and `repLeftArc` are disjoint. -/
theorem disjoint_union_repLeftArc :
    Disjoint (repStrict f hf ∪ repLeftVert f hf) (repLeftArc f hf) := by
  refine Finset.disjoint_left.mpr fun p hp_u hp_a ↦ ?_
  have h_norm_eq : ‖(p : ℂ)‖ = 1 := (Finset.mem_filter.mp hp_a).2.2.1
  simp only [Finset.mem_union] at hp_u
  rcases hp_u with hp_s | hp_lv
  · linarith [show ‖(p : ℂ)‖ > 1 from (Finset.mem_filter.mp hp_s).2.2.2.2.1]
  · linarith [show ‖(p : ℂ)‖ > 1 from (Finset.mem_filter.mp hp_lv).2.2]

/-! ### Helper lemmas for norm = 1 characterizations -/

private lemma uhp_norm_one_re_zero_eq_i (p : ℍ)
    (hn : ‖(p : ℂ)‖ = 1) (hr : (p : ℂ).re = 0) :
    p = ellipticPointI' := by
  refine UpperHalfPlane.ext (Complex.ext (hr.trans Complex.I_re.symm) ?_)
  have h_nsq : Complex.normSq (p : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hn, one_pow]
  rw [Complex.normSq_apply, hr] at h_nsq
  have h_prod : ((p : ℂ).im - 1) * ((p : ℂ).im + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp h_prod with h | h
  · exact (by linarith : (p : ℂ).im = 1).trans Complex.I_im.symm
  · exact absurd h (add_pos p.2 one_pos).ne'

/-! ### Case lemmas for exists_repCanon_of_nonEllOrbit -/

private lemma case_right_vertical_via_tInv (q : NonEllOrbitFM) (p0 : ℍ)
    (hp0_fd : p0 ∈ 𝒟) (hp0_ord : orderOfVanishingAt' (⇑f) p0 ≠ 0)
    (h_half : (↑p0 : ℂ).re = 1/2) (h_gt : ‖(↑p0 : ℂ)‖ > 1)
    (hp0_orb : orbFM p0 = q.val) :
    ∃ p1 ∈ repCanon f hf, orbFM p1 = q.val := by
  set p1 := (-1 : ℝ) +ᵥ p0
  have hp1_s₀ : p1 ∈ s₀FM f hf :=
    s₀FM_complete f hf p1 (vAdd_neg_one_mem_fd_of_right_vertFM p0 hp0_fd h_half)
      ((ord_vAdd_neg_one_eqFM f p0).symm ▸ hp0_ord)
  have hp1_re : (↑p1 : ℂ).re = -1/2 := by
    rw [vAdd_neg_one_coeFM, sub_re, one_re]; linarith
  refine ⟨p1, ?_, orb_vAdd_neg_one_eq p0 ▸ hp0_orb⟩
  simp only [repCanon, Finset.mem_union]
  exact Or.inl (Or.inr (Finset.mem_filter.mpr
    ⟨hp1_s₀, hp1_re, (vAdd_neg_one_norm_eq_of_re_halfFM p0 h_half).symm ▸ h_gt⟩))

private lemma case_right_arc_via_S (q : NonEllOrbitFM) (p0 : ℍ)
    (hp0_fd : p0 ∈ 𝒟) (hp0_ord : orderOfVanishingAt' (⇑f) p0 ≠ 0)
    (h_norm_eq : ‖(↑p0 : ℂ)‖ = 1) (h_pos : (↑p0 : ℂ).re > 0)
    (hp0_orb : orbFM p0 = q.val) (hq_ne_rho : orbFM (ellipticPointRho' : ℍ) ≠ q.val) :
    ∃ p1 ∈ repCanon f hf, orbFM p1 = q.val := by
  set p1 := ModularGroup.S • p0
  have hp1_s₀ : p1 ∈ s₀FM f hf :=
    s₀FM_complete f hf p1 (S_smul_mem_fd_of_unitFM p0 hp0_fd h_norm_eq)
      ((ord_S_eq f p0).symm ▸ hp0_ord)
  have hp1_re_neg : (↑p1 : ℂ).re < 0 := by
    change (ModularGroup.S • p0 : ℍ).re < 0
    rw [S_smul_re_neg_of_unitFM p0 h_norm_eq]
    exact neg_neg_iff_pos.mpr h_pos
  have hp1_ne_rho : p1 ≠ ellipticPointRho' := fun h ↦ hq_ne_rho <| by
    rw [← h, show orbFM (ModularGroup.S • p0) = orbFM p0 from orb_S_smul_eq p0, hp0_orb]
  refine ⟨p1, ?_, orb_S_smul_eq p0 ▸ hp0_orb⟩
  simp only [repCanon, Finset.mem_union]
  exact Or.inr (Finset.mem_filter.mpr ⟨hp1_s₀, hp1_ne_rho,
    S_smul_norm_of_unitFM p0 h_norm_eq, hp1_re_neg⟩)

/-! ### The key existence theorem -/

/-- Every non-elliptic orbit with nonzero order has a representative in `repCanon`. -/
theorem exists_repCanon_of_nonEllOrbit :
    ∀ q : NonEllOrbitFM,
      ordOrbitFM f q.val ≠ 0 →
      ∃ p ∈ repCanon f hf, orbFM p = q.val := by
  intro q hord
  obtain ⟨hq_ne_i, hq_ne_rho⟩ := q.2
  obtain ⟨p0, hp0_orb, hp0_fd⟩ := orbit_has_fd_repFM q.val
  have hp0_ord : orderOfVanishingAt' (⇑f) p0 ≠ 0 := by
    rw [← ordOrbit_mkFM f p0, hp0_orb]; exact hord
  have hp0_s₀ : p0 ∈ s₀FM f hf := s₀FM_complete f hf p0 hp0_fd hp0_ord
  have hp0_ne_i : p0 ≠ ellipticPointI' := fun h ↦ hq_ne_i (h ▸ hp0_orb).symm
  have hp0_ne_rho : p0 ≠ ellipticPointRho' := fun h ↦ hq_ne_rho (h ▸ hp0_orb).symm
  have hp0_ne_rho1 : p0 ≠ ellipticPointRhoPlusOne' :=
    fun h ↦ hq_ne_rho ((h ▸ hp0_orb).symm.trans orb_rho_plus_one_eq_orb_rhoFM)
  have h_norm_ge_one : ‖(p0 : ℂ)‖ ≥ 1 := by
    nlinarith [Complex.normSq_eq_norm_sq (p0 : ℂ), norm_nonneg (p0 : ℂ),
      sq_nonneg (‖(p0 : ℂ)‖ - 1), hp0_fd.1]
  rcases h_norm_ge_one.lt_or_eq with h_gt | h_eq
  · rcases hp0_fd.2.lt_or_eq with h_re_lt | h_re_eq
    · refine ⟨p0, ?_, hp0_orb⟩
      simp only [repCanon, Finset.mem_union]
      exact Or.inl (Or.inl (Finset.mem_filter.mpr
        ⟨hp0_s₀, hp0_ne_i, hp0_ne_rho, hp0_ne_rho1, h_gt, h_re_lt⟩))
    · rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1/2)).mp h_re_eq with h_half | h_neg_half
      · exact case_right_vertical_via_tInv f hf q p0 hp0_fd hp0_ord h_half h_gt hp0_orb
      · refine ⟨p0, ?_, hp0_orb⟩
        simp only [repCanon, Finset.mem_union]
        refine Or.inl (Or.inr (Finset.mem_filter.mpr ⟨hp0_s₀, ?_, h_gt⟩))
        change p0.re = -1/2; linarith
  · have h_norm_eq : ‖(↑p0 : ℂ)‖ = 1 := h_eq.symm
    have h_re_ne_zero : (↑p0 : ℂ).re ≠ 0 :=
      fun h ↦ hp0_ne_i (uhp_norm_one_re_zero_eq_i p0 h_norm_eq h)
    rcases lt_or_gt_of_ne h_re_ne_zero with h_neg | h_pos
    · refine ⟨p0, ?_, hp0_orb⟩
      simp only [repCanon, Finset.mem_union]
      exact Or.inr (Finset.mem_filter.mpr ⟨hp0_s₀, hp0_ne_rho, h_norm_eq, h_neg⟩)
    · exact case_right_arc_via_S f hf q p0 hp0_fd hp0_ord h_norm_eq h_pos hp0_orb hq_ne_rho.symm

/-! ### Injectivity helpers -/

/-- Elements of `repCanon` have real part strictly less than `1/2`. -/
private lemma repCanon_re_lt_half (p : ℍ) (hp : p ∈ repCanon f hf) : p.re < 1/2 := by
  simp only [repCanon, Finset.mem_union] at hp
  have hpre : p.re = (↑p : ℂ).re := rfl
  rcases hp with (h | h) | h
  · exact lt_of_abs_lt (Finset.mem_filter.mp h).2.2.2.2.2
  · simp only [repLeftVert, sLeftVertFM, Finset.mem_filter] at h; linarith [h.2.1]
  · linarith [(Finset.mem_filter.mp h).2.2.2]

/-- Elements of `repCanon` on the unit circle have negative real part. -/
private lemma repCanon_norm_one_re_neg (p : ℍ) (hp : p ∈ repCanon f hf)
    (h_norm : ‖(p : ℂ)‖ = 1) : (p : ℂ).re < 0 := by
  simp only [repCanon, Finset.mem_union] at hp
  rcases hp with (h | h) | h
  · exact absurd h_norm (Finset.mem_filter.mp h).2.2.2.2.1.ne'
  · exact absurd h_norm (Finset.mem_filter.mp h).2.2.ne'
  · exact (Finset.mem_filter.mp h).2.2.2

private lemma normSq_denom_expand_general (h : SL(2, ℤ)) (p : ℍ) :
    Complex.normSq (UpperHalfPlane.denom h p) =
    ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 * Complex.normSq (↑p) +
    2 * ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) *
      ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) * (↑p : ℂ).re +
    ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ^ 2 := by
  have hd : UpperHalfPlane.denom h p = ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ↑p +
      ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ) := by
    simp only [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.toGL,
      Matrix.SpecialLinearGroup.map, RingHom.mapMatrix_apply]; rfl
  rw [hd, Complex.normSq_apply]
  simp only [add_re, mul_re, add_im, mul_im,
    Complex.intCast_re, Complex.intCast_im, Complex.normSq_apply]
  ring

private lemma abs_int_cast_eq_one_of_sq_one {c : ℤ}
    (h : (c : ℝ) ^ 2 = 1) : |(c : ℝ)| = 1 := by
  nlinarith [sq_abs (c : ℝ), abs_nonneg (c : ℝ), sq_nonneg (|(c : ℝ)| - 1)]

private lemma d_mul_linear_nonneg {c d : ℤ} {z : ℍ}
    (hz : z ∈ 𝒟) (h_c_abs : |(c : ℝ)| = 1) :
    (d : ℝ) * (2 * (c : ℝ) * (z : ℂ).re + (d : ℝ)) ≥ 0 := by
  have h_bound : |2 * (c : ℝ) * (z : ℂ).re| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (2:ℝ) > 0), h_c_abs, mul_one]
    linarith [show |(z : ℂ).re| ≤ 1/2 from hz.2]
  rcases le_or_gt (d : ℤ) 0 with hd | hd
  · rcases eq_or_lt_of_le hd with hd0 | hd_neg
    · simp [show (d : ℝ) = 0 by exact_mod_cast hd0]
    · have hd_le : (d : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hd_neg
      exact mul_nonneg_iff.mpr (Or.inr ⟨by linarith, by linarith [abs_le.mp h_bound]⟩)
  · have hd_ge : (d : ℝ) ≥ 1 := by exact_mod_cast hd
    exact mul_nonneg (by linarith) (by linarith [abs_le.mp h_bound])

private lemma normSq_denom_ge_one (h : SL(2, ℤ)) (z : ℍ) (hz : z ∈ 𝒟)
    (h_csq : ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0) ^ 2 = 1) :
    Complex.normSq (UpperHalfPlane.denom h z) ≥ 1 := by
  have h_csq_real : ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 = 1 := by exact_mod_cast h_csq
  rw [normSq_denom_expand_general, h_csq_real, one_mul]
  nlinarith [hz.1, d_mul_linear_nonneg (c := (h : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (d := (h : Matrix (Fin 2) (Fin 2) ℤ) 1 1) hz (abs_int_cast_eq_one_of_sq_one h_csq_real)]

private lemma normSq_eq_one_of_denom_one (g : SL(2, ℤ)) (z : ℍ) (hz : z ∈ 𝒟)
    (h_csq : ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0) ^ 2 = 1)
    (h_denom : Complex.normSq (UpperHalfPlane.denom g z) = 1) :
    Complex.normSq (z : ℂ) = 1 := by
  have h_csq_real : ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 = 1 := by exact_mod_cast h_csq
  have h_expand := normSq_denom_expand_general g z
  rw [h_denom, h_csq_real, one_mul] at h_expand
  nlinarith [hz.1, d_mul_linear_nonneg (c := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (d := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1) hz (abs_int_cast_eq_one_of_sq_one h_csq_real)]

private lemma inv_c_sq_eq (g : SL(2, ℤ)) :
    ((g⁻¹ : SL(2, ℤ)).1 1 0) ^ 2 = ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0) ^ 2 := by
  have h : (g⁻¹ : SL(2, ℤ)).1 1 0 = -((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0) := by
    rw [Matrix.SpecialLinearGroup.coe_inv g, Matrix.adjugate_fin_two]
    simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.cons_val_one]
  rw [h]; ring

private lemma c_abs_le_one_of_smul_fd (g : SL(2, ℤ)) (p₁ p₂ : ℍ)
    (hg : g • p₂ = p₁) (hp₁ : p₁ ∈ 𝒟) (hp₂ : p₂ ∈ 𝒟) :
    |(g : Matrix (Fin 2) (Fin 2) ℤ) 1 0| ≤ 1 := by
  set c := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  have h_nsq_eq : Complex.normSq (UpperHalfPlane.denom g p₂) = p₂.im / p₁.im := by
    rw [(hg ▸ ModularGroup.im_smul_eq_div_normSq g p₂ :
      p₁.im = p₂.im / Complex.normSq (UpperHalfPlane.denom g p₂))]; field_simp
  by_contra! h_gt
  have h_c2 : c ^ 2 ≥ 4 := by nlinarith [sq_abs c]
  have h1 : (↑c : ℝ) ^ 2 * p₂.im ^ 2 ≤ p₂.im / p₁.im := by
    rw [← h_nsq_eq]
    convert p₂.c_mul_im_sq_le_normSq_denom g using 1
    simp [c]; ring
  have h2 : (↑c : ℝ) ^ 2 * p₂.im ^ 2 * p₁.im ≤ p₂.im := by
    have := mul_le_mul_of_nonneg_right h1 p₁.im_pos.le
    rwa [div_mul_cancel₀ _ p₁.im_pos.ne'] at this
  have h_c2_real : (↑c : ℝ) ^ 2 ≥ 4 := by exact_mod_cast h_c2
  have im_gt : ∀ {p : ℍ}, p ∈ 𝒟 → (1 : ℝ) / 2 < p.im := fun {p} hp ↦ by
    rw [← UpperHalfPlane.coe_im]; exact fd_im_gt_halfFM _ hp
  have hp1_im := im_gt hp₁
  have hp2_im := im_gt hp₂
  nlinarith [mul_pos (by linarith : (0:ℝ) < p₁.im - 1/2)
    (by linarith : (0:ℝ) < p₂.im - 1/2),
    mul_nonneg (show (0 : ℝ) ≤ (↑c : ℝ) ^ 2 - 4 from by linarith)
      (mul_nonneg p₂.im_pos.le p₁.im_pos.le),
    sq_nonneg p₂.im, p₂.im_pos, p₁.im_pos]

private lemma normSq_denom_one_of_im_eq (g : SL(2, ℤ))
    (p₁ p₂ : ℍ) (h_smul : g • p₁ = p₂)
    (h_im : p₁.im = p₂.im) :
    Complex.normSq (UpperHalfPlane.denom g p₁) = 1 := by
  have h := ModularGroup.im_smul_eq_div_normSq g p₁
  rw [h_smul, h_im] at h
  have hne : Complex.normSq (UpperHalfPlane.denom g p₁) ≠ 0 :=
    fun h0 ↦ by simp [h0] at h; linarith [p₂.im_pos]
  rw [eq_div_iff hne] at h
  nlinarith [p₂.im_pos]

private lemma injOn_c_eq_zero (g : SL(2, ℤ)) (p₁ p₂ : ℍ)
    (hg : g • p₂ = p₁) (hp₁ : p₁ ∈ repCanon f hf) (hp₂ : p₂ ∈ repCanon f hf)
    (hc : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0) :
    p₁ = p₂ := by
  obtain ⟨n, hn⟩ := ModularGroup.exists_eq_T_zpow_of_c_eq_zero hc
  have hTn : p₁ = ModularGroup.T ^ n • p₂ := by rw [hn] at hg; exact hg.symm
  have h_re_shift : p₁.re = p₂.re + (n : ℝ) := hTn ▸ ModularGroup.re_T_zpow_smul p₂ n
  have h_n_zero : n = 0 := by
    have h1 := repCanon_re_lt_half f hf p₁ hp₁
    have h3 := repCanon_re_lt_half f hf p₂ hp₂
    have re_ge : ∀ {p : ℍ}, p ∈ repCanon f hf → -(1/2 : ℝ) ≤ p.re := fun hp ↦ by
      have := (repCanon_mem_fd f hf hp).2
      rw [← UpperHalfPlane.coe_re] at this; exact (abs_le.mp this).1
    have h4 := re_ge hp₂
    have h5 := re_ge hp₁
    have h_lt : n < 1 := by exact_mod_cast (show (↑n : ℝ) < 1 by linarith)
    have h_gt : -1 < n := by exact_mod_cast (show (-1 : ℝ) < (↑n : ℝ) by linarith)
    lia
  rw [hTn, h_n_zero, zpow_zero, one_smul]

private lemma injOn_c_ne_zero (g : SL(2, ℤ)) (p₁ p₂ : ℍ)
    (hg : g • p₂ = p₁) (hp₁ : p₁ ∈ repCanon f hf) (hp₂ : p₂ ∈ repCanon f hf)
    (hp₁_fd : p₁ ∈ 𝒟) (hp₂_fd : p₂ ∈ 𝒟)
    (h_c_ne : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ≠ 0)
    (h_abs_c : |(g : Matrix (Fin 2) (Fin 2) ℤ) 1 0| ≤ 1) :
    p₁ = p₂ := by
  have h_csq : ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0) ^ 2 = 1 := by
    nlinarith [sq_abs ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0), Int.one_le_abs h_c_ne]
  have h_nsq_eq : Complex.normSq (UpperHalfPlane.denom g p₂) = p₂.im / p₁.im := by
    have h := ModularGroup.im_smul_eq_div_normSq g p₂
    rw [hg] at h; rw [h]; field_simp
  have h_im_eq : p₁.im = p₂.im := by
    refine le_antisymm ?_ ?_
    · have h := normSq_denom_ge_one g p₂ hp₂_fd h_csq
      rw [h_nsq_eq] at h
      rwa [ge_iff_le, le_div_iff₀ p₁.im_pos, one_mul] at h
    · have h := ModularGroup.im_smul_eq_div_normSq g⁻¹ p₁
      rw [inv_smul_eq_iff.mpr hg.symm] at h; rw [h]
      exact div_le_self p₁.im_pos.le
        (normSq_denom_ge_one g⁻¹ p₁ hp₁_fd ((inv_c_sq_eq g).trans h_csq))
  have h_p2_nsq := normSq_eq_one_of_denom_one g p₂ hp₂_fd h_csq
    (by rw [h_nsq_eq, h_im_eq, div_self p₂.im_pos.ne'])
  have h_p1_nsq := normSq_eq_one_of_denom_one g⁻¹ p₁ hp₁_fd
    ((inv_c_sq_eq g).trans h_csq)
    (normSq_denom_one_of_im_eq g⁻¹ p₁ p₂ (inv_smul_eq_iff.mpr hg.symm) h_im_eq)
  have nsq_to_norm : ∀ {p : ℍ}, Complex.normSq (p : ℂ) = 1 → ‖(p : ℂ)‖ = 1 := fun {p} hp ↦ by
    nlinarith [Complex.normSq_eq_norm_sq (p : ℂ), norm_nonneg (p : ℂ),
      sq_nonneg (‖(p : ℂ)‖ - 1), hp]
  have h_p1_norm := nsq_to_norm h_p1_nsq
  have h_p2_norm := nsq_to_norm h_p2_nsq
  have h_re_eq : (p₁ : ℂ).re = (p₂ : ℂ).re := by
    rw [Complex.normSq_apply] at h_p1_nsq h_p2_nsq
    rw [show (↑p₁ : ℂ).im = (↑p₂ : ℂ).im from h_im_eq] at h_p1_nsq
    nlinarith [sq_nonneg ((p₁ : ℂ).re - (p₂ : ℂ).re),
      sq_nonneg ((p₁ : ℂ).re + (p₂ : ℂ).re),
      repCanon_norm_one_re_neg f hf p₁ hp₁ h_p1_norm,
      repCanon_norm_one_re_neg f hf p₂ hp₂ h_p2_norm]
  exact UpperHalfPlane.ext_re_im h_re_eq h_im_eq

/-! ### OrbitFM injectivity -/

/-- The orbit map is injective on `repCanon`. -/
theorem orb_injOn_repCanon :
    Set.InjOn orbFM ↑(repCanon f hf) := by
  intro p₁ hp₁ p₂ hp₂ h_eq
  simp only [orbFM] at h_eq
  obtain ⟨g, hg⟩ := Quotient.exact' h_eq
  have hp₁_fd := repCanon_mem_fd f hf hp₁
  have hp₂_fd := repCanon_mem_fd f hf hp₂
  rcases eq_or_ne ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0) 0 with hc | hc
  · exact injOn_c_eq_zero f hf g p₁ p₂ hg hp₁ hp₂ hc
  · exact injOn_c_ne_zero f hf g p₁ p₂ hg hp₁ hp₂ hp₁_fd hp₂_fd hc
      (c_abs_le_one_of_smul_fd g p₁ p₂ hg hp₁_fd hp₂_fd)

end

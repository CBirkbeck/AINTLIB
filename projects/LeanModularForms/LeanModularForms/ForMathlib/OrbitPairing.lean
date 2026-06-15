/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.Orbits

/-!
# OrbitFM Pairing Lemmas for the Valence Formula

Pure-algebra lemmas about orbit pairings under the modular group actions T (z ↦ z + 1) and
S (z ↦ -1/z). These collapse the explicit coefficient expansion of the valence formula,
pairing left/right vertical and arc contributions.

## Main results

* `vAdd_one_mem_fd_of_left_vertFM` — T-translation preserves 𝒟 for left-vertical points
* `vAdd_neg_one_mem_fd_of_right_vertFM` — T⁻¹-translation preserves 𝒟 for right-vertical points
* `sum_ord_rightVert_eq_sum_ord_leftVertFM` — orders on right vertical equal orders on left
* `sum_ord_rightArc_eq_sum_ord_leftArcFM` — orders on right arc equal orders on left arc
* `orb_vAdd_neg_one_eq` — T⁻¹-translation preserves orbits
* `orb_S_smul_eq` — S-action preserves orbits
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

private lemma normSq_add_one_eq_of_re_neg_halfFM (z : ℂ) (hre : z.re = -1/2) :
    Complex.normSq (z + 1) = Complex.normSq z := by
  simp only [normSq_apply, add_re, one_re, add_im, one_im, add_zero, hre]
  ring

private lemma normSq_sub_one_eq_of_re_halfFM (z : ℂ) (hre : z.re = 1/2) :
    Complex.normSq (z - 1) = Complex.normSq z := by
  simp only [normSq_apply, sub_re, one_re, sub_im, one_im, sub_zero, hre]
  ring

private lemma norm_eq_of_normSq_eqFM {z w : ℂ}
    (h : Complex.normSq z = Complex.normSq w) : ‖z‖ = ‖w‖ :=
  (sq_eq_sq₀ (norm_nonneg z) (norm_nonneg w)).mp <| by
    linarith [normSq_eq_norm_sq z, normSq_eq_norm_sq w]

private lemma normSq_eq_one_of_norm_eq_oneFM {z : ℂ} (h : ‖z‖ = 1) :
    Complex.normSq z = 1 := by
  simp [normSq_eq_norm_sq, h]

/-- Coercion identity for T-translation: `((1:ℝ) +ᵥ p : ℂ) = (p : ℂ) + 1`. -/
lemma vAdd_one_coeFM (p : ℍ) : ((1 : ℝ) +ᵥ p : ℂ) = (p : ℂ) + 1 := by
  simp [add_comm]

/-- T⁻¹-translation coercion: `((-1:ℝ) +ᵥ p : ℂ) = (p : ℂ) - 1`. -/
lemma vAdd_neg_one_coeFM (p : ℍ) : ((-1 : ℝ) +ᵥ p : ℂ) = (p : ℂ) - 1 := by
  simp [sub_eq_add_neg, add_comm]

/-- T-translation preserves norm for left-vertical points (`re = -1/2`). -/
lemma norm_add_one_eq_of_re_neg_halfFM (z : ℂ) (hre : z.re = -1/2) :
    ‖z + 1‖ = ‖z‖ :=
  norm_eq_of_normSq_eqFM (normSq_add_one_eq_of_re_neg_halfFM z hre)

/-- T⁻¹-translation preserves norm for right-vertical points (`re = 1/2`). -/
lemma norm_sub_one_eq_of_re_halfFM (z : ℂ) (hre : z.re = 1/2) :
    ‖z - 1‖ = ‖z‖ :=
  norm_eq_of_normSq_eqFM (normSq_sub_one_eq_of_re_halfFM z hre)

/-- T-translation preserves norm for UpperHalfPlane points with `re = -1/2`. -/
lemma vAdd_one_norm_eq_of_re_neg_halfFM (p : ℍ) (hre : (p : ℂ).re = -1/2) :
    ‖((1 : ℝ) +ᵥ p : ℂ)‖ = ‖(p : ℂ)‖ :=
  vAdd_one_coeFM p ▸ norm_add_one_eq_of_re_neg_halfFM _ hre

/-- T⁻¹-translation preserves norm for UpperHalfPlane points with `re = 1/2`. -/
lemma vAdd_neg_one_norm_eq_of_re_halfFM (p : ℍ) (hre : (p : ℂ).re = 1/2) :
    ‖((-1 : ℝ) +ᵥ p : ℂ)‖ = ‖(p : ℂ)‖ :=
  vAdd_neg_one_coeFM p ▸ norm_sub_one_eq_of_re_halfFM _ hre

/-- T-translation sends left-vertical FD points to 𝒟. -/
theorem vAdd_one_mem_fd_of_left_vertFM (p : ℍ) (hp_fd : p ∈ 𝒟) (hre : (p : ℂ).re = -1/2) :
    (1 : ℝ) +ᵥ p ∈ 𝒟 := by
  refine ⟨?_, ?_⟩
  · rw [vAdd_one_coeFM, normSq_add_one_eq_of_re_neg_halfFM _ hre]
    exact hp_fd.1
  · change |((1 : ℝ) +ᵥ p : ℂ).re| ≤ 1 / 2
    rw [vAdd_one_coeFM, add_re, one_re, hre]
    norm_num

/-- T⁻¹-translation sends right-vertical FD points to 𝒟. -/
theorem vAdd_neg_one_mem_fd_of_right_vertFM (p : ℍ) (hp_fd : p ∈ 𝒟) (hre : (p : ℂ).re = 1/2) :
    (-1 : ℝ) +ᵥ p ∈ 𝒟 := by
  refine ⟨?_, ?_⟩
  · rw [vAdd_neg_one_coeFM, normSq_sub_one_eq_of_re_halfFM _ hre]
    exact hp_fd.1
  · change |((-1 : ℝ) +ᵥ p : ℂ).re| ≤ 1 / 2
    rw [vAdd_neg_one_coeFM, sub_re, one_re, hre]
    norm_num

/-- `(1:ℝ) +ᵥ ρ' = ρ'+1` as UpperHalfPlane elements. -/
theorem vAdd_one_rho_eq_rho_plus_oneFM :
    (1 : ℝ) +ᵥ ellipticPointRho' = ellipticPointRhoPlusOne' :=
  UpperHalfPlane.ext <| vAdd_one_coeFM _ ▸ ellipticPointRho_add_one_eq

/-- ρ+1 is in the standard fundamental domain 𝒟. -/
theorem ellipticPointRhoPlusOne_mem_fdFM : ellipticPointRhoPlusOne' ∈ 𝒟 := by
  rw [← vAdd_one_rho_eq_rho_plus_oneFM]
  refine vAdd_one_mem_fd_of_left_vertFM ellipticPointRho' ellipticPointRho_mem_fd ?_
  simp only [ellipticPointRho']
  norm_num

variable {k : ℤ} (f : ModularForm (Gamma 1) k)

/-- `ord(f, ρ+1) = ord(f, ρ)` via the T-translation identity. -/
theorem ord_rho_plus_one_eq_ord_rho_via_vAddFM :
    orderOfVanishingAt' (⇑f) ellipticPointRhoPlusOne' =
    orderOfVanishingAt' (⇑f) ellipticPointRho' := by
  rw [← vAdd_one_rho_eq_rho_plus_oneFM]
  exact ord_add_one_eq f ellipticPointRho'

/-- S-action coe: `(S·z : ℂ) = (-z)⁻¹`. -/
lemma S_smul_coeFM (p : ℍ) : ((ModularGroup.S • p : ℍ) : ℂ) = (-(p : ℂ))⁻¹ := by
  rw [UpperHalfPlane.modular_S_smul]

/-- S-action preserves norm on the unit circle. -/
theorem S_smul_norm_of_unitFM (p : ℍ) (hp : ‖(p : ℂ)‖ = 1) :
    ‖((ModularGroup.S • p : ℍ) : ℂ)‖ = 1 := by
  rw [S_smul_coeFM, norm_inv, norm_neg, hp, inv_one]

/-- S-action negates real part on the unit circle. -/
theorem S_smul_re_neg_of_unitFM (p : ℍ) (hp : ‖(p : ℂ)‖ = 1) :
    (ModularGroup.S • p : ℍ).re = -p.re := by
  change ((ModularGroup.S • p : ℍ) : ℂ).re = -p.re
  rw [S_smul_coeFM]
  simp [normSq_eq_one_of_norm_eq_oneFM hp]

/-- S-action preserves 𝒟 for unit-circle points. -/
theorem S_smul_mem_fd_of_unitFM (p : ℍ) (hp_fd : p ∈ 𝒟) (hp_norm : ‖(p : ℂ)‖ = 1) :
    ModularGroup.S • p ∈ 𝒟 := by
  have hns : Complex.normSq (p : ℂ) = 1 := normSq_eq_one_of_norm_eq_oneFM hp_norm
  refine ⟨?_, ?_⟩
  · rw [S_smul_coeFM, map_inv₀, Complex.normSq_neg, hns, inv_one]
  · change |((ModularGroup.S • p : ℍ) : ℂ).re| ≤ 1 / 2
    simpa only [S_smul_coeFM, Complex.inv_re, Complex.neg_re,
      Complex.normSq_neg, hns, div_one, abs_neg, UpperHalfPlane.coe_re] using hp_fd.2

private lemma S_mul_SFM : ModularGroup.S * ModularGroup.S = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [ModularGroup.S] <;> decide

/-- S² acts as the identity on ℍ. -/
lemma S_smul_S_smulFM (p : ℍ) : ModularGroup.S • (ModularGroup.S • p) = p := by
  rw [← mul_smul, S_mul_SFM, ModularGroup.SL_neg_smul, one_smul]

/-- The S-action is injective on ℍ. -/
lemma S_smul_injectiveFM : Function.Injective (ModularGroup.S • · : ℍ → ℍ) :=
  Function.HasLeftInverse.injective ⟨(ModularGroup.S • ·), S_smul_S_smulFM⟩

/-- T⁻¹-translation preserves orbits: `orbFM((-1)+ᵥp) = orbFM(p)`. -/
lemma orb_vAdd_neg_one_eq (p : ℍ) :
    orbFM ((-1 : ℝ) +ᵥ p) = orbFM p := by
  change Quotient.mk'' ((-1 : ℝ) +ᵥ p) = Quotient.mk'' p
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨ModularGroup.T⁻¹, by simpa using UpperHalfPlane.modular_T_zpow_smul p (-1)⟩

/-- S-action preserves orbits: `orbFM(S • p) = orbFM(p)`. -/
lemma orb_S_smul_eq (p : ℍ) :
    orbFM (ModularGroup.S • p) = orbFM p := by
  change Quotient.mk'' (ModularGroup.S • p) = Quotient.mk'' p
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨ModularGroup.S, rfl⟩

/-- The left-vertical filter of S: points with `re = -1/2` and `‖p‖ > 1`. -/
def sLeftVertFM (S : Finset ℍ) : Finset ℍ :=
  S.filter (fun p => (p : ℂ).re = -1/2 ∧ ‖(p : ℂ)‖ > 1)

/-- The right-vertical filter of S: points with `re = 1/2` and `‖p‖ > 1`. -/
def sRightVertFM (S : Finset ℍ) : Finset ℍ :=
  S.filter (fun p => (p : ℂ).re = 1/2 ∧ ‖(p : ℂ)‖ > 1)

/-- The left-arc filter: points on the unit circle with negative real part. -/
def sLeftArcFM (S : Finset ℍ) : Finset ℍ :=
  S.filter (fun p => ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)

/-- The right-arc filter: points on the unit circle with positive real part. -/
def sRightArcFM (S : Finset ℍ) : Finset ℍ :=
  S.filter (fun p => ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re > 0)

/-- T⁻¹-invariance of vanishing order: `ord(f, (-1)+ᵥp) = ord(f, p)`. -/
lemma ord_vAdd_neg_one_eqFM (p : ℍ) :
    orderOfVanishingAt' (⇑f) ((-1 : ℝ) +ᵥ p) = orderOfVanishingAt' (⇑f) p := by
  simpa using (ord_add_one_eq f ((-1 : ℝ) +ᵥ p)).symm

private lemma ord_ne_zero_of_cast_ne_zeroFM {p : ℍ} {g : ℍ → ℂ}
    (h : (orderOfVanishingAt' g p : ℂ) ≠ 0) : orderOfVanishingAt' g p ≠ 0 :=
  mod_cast h

/-- Orders on right vertical edge equal orders on left vertical edge. -/
theorem sum_ord_rightVert_eq_sum_ord_leftVertFM (S : Finset ℍ)
    (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∑ p ∈ sRightVertFM S, (orderOfVanishingAt' (⇑f) p : ℂ) =
    ∑ p ∈ sLeftVertFM S, (orderOfVanishingAt' (⇑f) p : ℂ) := by
  rw [← Finset.sum_filter_ne_zero, ← Finset.sum_filter_ne_zero (s := sLeftVertFM S)]
  apply Finset.sum_nbij ((-1 : ℝ) +ᵥ ·)
  · intro p hp
    obtain ⟨⟨hp_S, hre, hnorm⟩, hord⟩ := Finset.mem_filter.mp hp
      |>.imp_left Finset.mem_filter.mp
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨
      hS_complete _ (vAdd_neg_one_mem_fd_of_right_vertFM p (hS p hp_S) hre)
        (ord_vAdd_neg_one_eqFM f p ▸ ord_ne_zero_of_cast_ne_zeroFM hord),
      ?_, ?_⟩, ?_⟩
    · change ((-1 : ℝ) +ᵥ p : ℂ).re = -1 / 2
      rw [vAdd_neg_one_coeFM, sub_re, one_re, hre]
      norm_num
    · rw [vAdd_neg_one_norm_eq_of_re_halfFM p hre]
      exact hnorm
    · exact ord_vAdd_neg_one_eqFM f p ▸ hord
  · exact fun _ _ _ _ => IsLeftCancelVAdd.left_cancel _ _ _
  · intro q hq
    obtain ⟨⟨hq_S, hre, hnorm⟩, hord⟩ := Finset.mem_filter.mp hq
      |>.imp_left Finset.mem_filter.mp
    refine ⟨(1 : ℝ) +ᵥ q, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨
      hS_complete _ (vAdd_one_mem_fd_of_left_vertFM q (hS q hq_S) hre)
        (ord_add_one_eq f q ▸ ord_ne_zero_of_cast_ne_zeroFM hord),
      ?_, ?_⟩, ?_⟩, ?_⟩
    · change ((1 : ℝ) +ᵥ q : ℂ).re = 1 / 2
      rw [vAdd_one_coeFM, add_re, one_re, hre]
      norm_num
    · rw [vAdd_one_norm_eq_of_re_neg_halfFM q hre]
      exact hnorm
    · exact ord_add_one_eq f q ▸ hord
    · change (-1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ q) = q
      simp [← add_vadd]
  · exact fun p _ => by rw [ord_vAdd_neg_one_eqFM f p]

/-- Orders on right arc equal orders on left arc (via S-action). -/
theorem sum_ord_rightArc_eq_sum_ord_leftArcFM (S : Finset ℍ) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∑ p ∈ sRightArcFM S, (orderOfVanishingAt' (⇑f) p : ℂ) =
    ∑ p ∈ sLeftArcFM S, (orderOfVanishingAt' (⇑f) p : ℂ) := by
  rw [← Finset.sum_filter_ne_zero, ← Finset.sum_filter_ne_zero (s := sLeftArcFM S)]
  apply Finset.sum_nbij (ModularGroup.S • ·)
  · intro p hp
    obtain ⟨⟨hp_S, hnorm, hre_pos⟩, hord⟩ := Finset.mem_filter.mp hp
      |>.imp_left Finset.mem_filter.mp
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨
      hS_complete _ (S_smul_mem_fd_of_unitFM p (hS p hp_S) hnorm)
        (ord_S_eq f p ▸ ord_ne_zero_of_cast_ne_zeroFM hord),
      S_smul_norm_of_unitFM p hnorm, ?_⟩, ?_⟩
    · change (ModularGroup.S • p : ℍ).re < 0
      rw [S_smul_re_neg_of_unitFM p hnorm, show p.re = (p : ℂ).re from rfl]
      linarith
    · exact ord_S_eq f p ▸ hord
  · exact S_smul_injectiveFM.injOn
  · intro q hq
    obtain ⟨⟨hq_S, hnorm, hre_neg⟩, hord⟩ := Finset.mem_filter.mp hq
      |>.imp_left Finset.mem_filter.mp
    refine ⟨ModularGroup.S • q, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨
      hS_complete _ (S_smul_mem_fd_of_unitFM q (hS q hq_S) hnorm)
        (ord_S_eq f q ▸ ord_ne_zero_of_cast_ne_zeroFM hord),
      S_smul_norm_of_unitFM q hnorm, ?_⟩, ?_⟩, S_smul_S_smulFM q⟩
    · change (ModularGroup.S • q : ℍ).re > 0
      rw [S_smul_re_neg_of_unitFM q hnorm, show q.re = (q : ℂ).re from rfl]
      linarith
    · exact ord_S_eq f q ▸ hord
  · exact fun p _ => by rw [ord_S_eq f p]

end

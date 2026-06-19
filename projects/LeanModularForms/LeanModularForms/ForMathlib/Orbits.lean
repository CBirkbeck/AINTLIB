/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import LeanModularForms.ForMathlib.ModularInvariance

/-!
# SL₂(ℤ) Orbits on the Upper Half-Plane

`orderOfVanishingAt'` is invariant under the full modular group SL(2, ℤ). We define `ordOrbitFM`
on orbits and establish finite support for the orbit sum.

## Main Definitions

* `OrbitFM` — the orbit quotient `MulAction.orbitRel.Quotient SL(2, ℤ) ℍ`
* `orbFM` — canonical quotient map `ℍ → OrbitFM`
* `ordOrbitFM` — order of vanishing lifted to orbits
* `oiFM`, `orhoFM` — orbits of the elliptic points `i` and `ρ`
* `NonEllOrbitFM` — non-elliptic orbits
* `s₀` — the finite set of zeros in the fundamental domain

## Main Results

* `ord_smul_eqFM` — `orderOfVanishingAt' f (g • p) = orderOfVanishingAt' f p`
* `finite_zeros_in_fdFM` — finiteness of zeros with nonzero order in `𝒟`
* `finite_support_ordOrbitFM` — finitely many orbits have nonzero `ordOrbitFM`
* `orbit_has_fd_repFM` — every orbit has a representative in `𝒟`
* `orb_rho_plus_one_eq_orb_rhoFM` — T-equivalence of elliptic orbits
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k)

/-- `orderOfVanishingAt'` is invariant under the action of any `g ∈ SL(2, ℤ)`. -/
theorem ord_smul_eqFM (g : SL(2, ℤ)) (p : ℍ) :
    orderOfVanishingAt' (⇑f) (g • p) = orderOfVanishingAt' (⇑f) p := by
  have hg_mem : g ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top g
  induction hg_mem using Subgroup.closure_induction generalizing p with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ord_S_eq f p
    · rw [UpperHalfPlane.modular_T_smul]; exact ord_add_one_eq f p
  | one => simp only [one_smul]
  | mul x y _ _ ihx ihy => rw [mul_smul, ihx]; exact ihy p
  | inv x _ ihx => rw [← ihx, smul_inv_smul]

/-- The type of orbits of `SL(2, ℤ)` acting on `ℍ`. -/
abbrev OrbitFM := MulAction.orbitRel.Quotient SL(2, ℤ) ℍ

/-- The canonical map from `ℍ` to its orbit. -/
def orbFM (p : ℍ) : OrbitFM := Quotient.mk'' p

/-- The order of vanishing lifted to orbits. Well-defined by `ord_smul_eqFM`. -/
def ordOrbitFM (q : OrbitFM) : ℤ :=
  Quotient.liftOn' q (orderOfVanishingAt' (⇑f)) fun _ b ⟨g, hg⟩ ↦ by
    rw [← hg]; exact ord_smul_eqFM f g b

@[simp]
theorem ordOrbit_mkFM (p : ℍ) : ordOrbitFM f (orbFM p) = orderOfVanishingAt' (⇑f) p := rfl

/-- The orbit of `i`. -/
def oiFM : OrbitFM := orbFM ellipticPointI'

/-- The orbit of `ρ`. -/
def orhoFM : OrbitFM := orbFM ellipticPointRho'

/-- A non-elliptic orbit is one distinct from both `oiFM` and `orhoFM`. -/
def NonEllOrbitFM := {q : OrbitFM // q ≠ oiFM ∧ q ≠ orhoFM}

/-- Every orbit has a representative in the fundamental domain `𝒟`. -/
theorem orbit_has_fd_repFM (q : OrbitFM) : ∃ p : ℍ, orbFM p = q ∧ p ∈ 𝒟 := by
  induction q using Quotient.inductionOn' with
  | h z =>
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
    exact ⟨g • z, Quotient.sound' ⟨g, rfl⟩, hg⟩

private theorem G_analyticAtFM (p : ℍ) :
    AnalyticAt ℂ (fun w : ℂ ↦ if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℂ) := by
  have h_diffOn : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {w | 0 < w.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp f.holo'
  apply analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds p.im_pos] with w hw
  have h_eq : ∀ᶠ u in 𝓝 w, (fun w : ℂ ↦ if h : 0 < w.im then f ⟨w, h⟩ else 0) u =
        (f ∘ UpperHalfPlane.ofComplex) u := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw] with u hu
    simp only [Function.comp_apply, dif_pos hu, UpperHalfPlane.ofComplex_apply_of_im_pos hu]
  exact ((h_diffOn w hw).differentiableAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw)).congr_of_eventuallyEq h_eq

private theorem G_eval_eq_fFM (p : ℍ) :
    (fun w : ℂ ↦ if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℂ) = f p :=
  dif_pos p.im_pos

/-- If `f p ≠ 0`, then `orderOfVanishingAt' f p = 0`. -/
theorem orderOfVanishingAt'_eq_zero_of_ne_zero' (p : ℍ) (hp : f p ≠ 0) :
    orderOfVanishingAt' f p = 0 := by
  unfold orderOfVanishingAt'
  have h_nf : MeromorphicNFAt _ (p : ℂ) := (G_analyticAtFM f p).meromorphicNFAt
  have hGp : (fun w : ℂ ↦ if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℂ) ≠ 0 := by
    rwa [G_eval_eq_fFM]
  rw [h_nf.meromorphicOrderAt_eq_zero_iff.mpr hGp]; rfl

/-- `orderOfVanishingAt' f p ≠ 0` implies `f p = 0`. -/
theorem eq_zero_of_orderOfVanishingAt'_ne_zero' (p : ℍ)
    (hp : orderOfVanishingAt' (⇑f) p ≠ 0) : f p = 0 :=
  not_imp_comm.mp (orderOfVanishingAt'_eq_zero_of_ne_zero' f p) hp

/-- `f ≠ 0` and `f p = 0` implies `orderOfVanishingAt' f p ≠ 0`. -/
theorem orderOfVanishingAt'_ne_zero_of_eq_zeroFM (hf : f ≠ 0) (p : ℍ) (hp : f p = 0) :
    orderOfVanishingAt' (⇑f) p ≠ 0 := by
  unfold orderOfVanishingAt'
  intro h_untop_eq
  have h_nf : MeromorphicNFAt _ (p : ℂ) := (G_analyticAtFM f p).meromorphicNFAt
  have h_ord_ne : meromorphicOrderAt
      (fun w : ℂ ↦ if h : 0 < w.im then f ⟨w, h⟩ else 0) (↑p) ≠ (0 : WithTop ℤ) := by
    intro h0
    apply h_nf.meromorphicOrderAt_eq_zero_iff.mp h0
    split_ifs with h
    · exact_mod_cast hp
    · exact absurd p.im_pos h
  have h_top := (WithTop.untop₀_eq_zero.mp h_untop_eq).resolve_left h_ord_ne
  rw [meromorphicOrderAt_eq_top_iff] at h_top
  have h_analOn : AnalyticOnNhd ℂ (fun w : ℂ ↦ if h : 0 < w.im then f ⟨w, h⟩ else 0)
      {w | 0 < w.im} := fun w hw ↦ G_analyticAtFM f ⟨w, hw⟩
  have h_preconn : IsPreconnected {w : ℂ | 0 < w.im} :=
    ((convex_halfSpace_im_gt 0).isConnected ⟨I, by simp [I_im]⟩).isPreconnected
  apply hf
  ext z
  exact (G_eval_eq_fFM f z).symm.trans
    (h_analOn.eqOn_zero_of_preconnected_of_frequently_eq_zero
      h_preconn p.im_pos h_top.frequently z.im_pos)

private theorem modularFormCompOfComplexFM_eq' (p : ℍ) :
    modularFormCompOfComplex f (p : ℂ) = f p := by
  simp [modularFormCompOfComplex, UpperHalfPlane.ofComplex_apply_of_im_pos p.im_pos]

/-- A point in the fundamental domain `𝒟` has imaginary part strictly above `1/2`. -/
theorem fd_im_gt_halfFM (p : ℍ) (hp : p ∈ 𝒟) : (1:ℝ)/2 < (p : ℂ).im := by
  by_contra! h_le
  obtain ⟨hnormSq, habs_re⟩ := hp
  have hre := abs_le.mp habs_re
  nlinarith [normSq_apply (↑p : ℂ), p.im_pos, mul_self_nonneg (p : ℂ).re,
    show UpperHalfPlane.re p = (↑p : ℂ).re from rfl, show p.im = (↑p : ℂ).im from rfl]

private theorem no_zeros_above_height' (hf : f ≠ 0) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ (p : ℍ), H₀ ≤ (p : ℂ).im → f p ≠ 0 := by
  obtain ⟨H₀, hH₀_gt, hH₀_nonvan⟩ := exists_height_cusp_nonvanishing f hf
  refine ⟨H₀, hH₀_gt, fun p hp hfp ↦ ?_⟩
  have h_one_mem : (1 : ℝ) ∈ (↑(Gamma 1) : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
    Gamma_one_coe_eq_SL.symm ▸ one_mem_strictPeriods_SL
  have h_eq := SlashInvariantFormClass.eq_cuspFunction f p h_one_mem one_ne_zero
  have h_qParam_mem : Function.Periodic.qParam (1 : ℝ) (↑p : ℂ) ∈
      Metric.closedBall (0 : ℂ) (Real.exp (-2 * Real.pi * H₀)) := by
    rw [Metric.mem_closedBall, dist_zero_right, Function.Periodic.norm_qParam, div_one]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  exact hH₀_nonvan _ h_qParam_mem (Complex.exp_ne_zero _) (h_eq ▸ hfp)

/-- The set of zeros (with nonzero order) in `𝒟` is finite. -/
theorem finite_zeros_in_fdFM (hf : f ≠ 0) :
    Set.Finite {p : ℍ | p ∈ 𝒟 ∧ orderOfVanishingAt' (⇑f) p ≠ 0} := by
  apply Set.Finite.subset (s := {p : ℍ | p ∈ 𝒟 ∧ f p = 0})
  swap
  · intro p ⟨hp_fd, hp_ord⟩
    exact ⟨hp_fd, eq_zero_of_orderOfVanishingAt'_ne_zero' f p hp_ord⟩
  obtain ⟨H₀, hH₀_gt, hH₀_no_zeros⟩ := no_zeros_above_height' f hf
  have hM_half : (1:ℝ)/2 < H₀ + 1 := by
    linarith [Real.sqrt_nonneg 3]
  have h_fin := modularForm_finitely_many_zeros_in_fdBox f hf hM_half
  apply (h_fin.preimage UpperHalfPlane.coe_injective.injOn).subset
  intro p ⟨hp_fd, hp_zero⟩
  change (p : ℂ) ∈ {z ∈ fdBox (H₀ + 1) | modularFormCompOfComplex f z = 0}
  have hre_bridge : UpperHalfPlane.re p = (↑p : ℂ).re := rfl
  have hre := abs_le.mp hp_fd.2
  refine ⟨⟨by linarith [hre_bridge], by linarith [hre_bridge],
    fd_im_gt_halfFM p hp_fd, ?_⟩, (modularFormCompOfComplexFM_eq' f p).symm ▸ hp_zero⟩
  by_contra! h_ge
  exact absurd hp_zero (hH₀_no_zeros p (by linarith))

/-- The set of orbits with nonzero `ordOrbitFM` is finite. -/
theorem finite_support_ordOrbitFM (hf : f ≠ 0) :
    Set.Finite {q : OrbitFM | ordOrbitFM f q ≠ 0} := by
  choose rep hrep using orbit_has_fd_repFM
  set S := {q : OrbitFM | ordOrbitFM f q ≠ 0}
  have h_image : rep '' S ⊆
      {p : ℍ | p ∈ 𝒟 ∧ orderOfVanishingAt' (⇑f) p ≠ 0} := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨(hrep q).2, by rwa [← ordOrbit_mkFM f (rep q), (hrep q).1]⟩
  have h_inj : Set.InjOn rep S := fun q₁ _ q₂ _ h ↦ by
    have := congrArg orbFM h
    rwa [(hrep q₁).1, (hrep q₂).1] at this
  exact (finite_zeros_in_fdFM f hf).subset h_image |>.of_finite_image h_inj

/-- The set of non-elliptic orbits with nonzero `ordOrbitFM` is finite. -/
theorem finite_support_ordOrbit_nonEllFM (hf : f ≠ 0) :
    Set.Finite {q : NonEllOrbitFM | ordOrbitFM f q.val ≠ 0} :=
  ((finite_support_ordOrbitFM f hf).preimage Subtype.val_injective.injOn).subset fun _ h ↦ h

/-- The canonical finite set of zeros (with nonzero order) in `𝒟`. -/
noncomputable def s₀FM (hf : f ≠ 0) : Finset ℍ := (finite_zeros_in_fdFM f hf).toFinset

/-- Every point in `s₀` lies in the fundamental domain `𝒟`. -/
theorem s₀FM_mem_fd (hf : f ≠ 0) : ∀ p ∈ s₀FM f hf, p ∈ 𝒟 :=
  fun _ hp ↦ ((finite_zeros_in_fdFM f hf).mem_toFinset.mp hp).1

/-- `s₀` captures all points in `𝒟` with nonzero order of vanishing. -/
theorem s₀FM_complete (hf : f ≠ 0) :
    ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ s₀FM f hf :=
  fun _ hp hord ↦ (finite_zeros_in_fdFM f hf).mem_toFinset.mpr ⟨hp, hord⟩

/-- The orbit of `ρ+1` equals the orbit of `ρ`. -/
theorem orb_rho_plus_one_eq_orb_rhoFM :
    orbFM ellipticPointRhoPlusOne' = (orhoFM : OrbitFM) := by
  change Quotient.mk'' ellipticPointRhoPlusOne' = Quotient.mk'' ellipticPointRho'
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨ModularGroup.T, ?_⟩
  rw [UpperHalfPlane.modular_T_smul]
  ext
  simp only [ellipticPointRho', ellipticPointRhoPlusOne', UpperHalfPlane.coe_vadd]
  push_cast; ring

end

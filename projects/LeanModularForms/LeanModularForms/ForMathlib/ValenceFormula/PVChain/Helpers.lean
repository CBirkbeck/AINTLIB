/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.EllipticPoints
import LeanModularForms.ForMathlib.FDBoundaryH
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue
import LeanModularForms.ForMathlib.ModularInvariance
import LeanModularForms.ForMathlib.Orbits
import LeanModularForms.ForMathlib.ValenceFormula.OnCurvePV.Main

/-!
# PV Chain Helpers

Auxiliary definitions and lemmas used in the proof of the valence formula:
the CPV integrand `pvIntegrand` and the singular sets `sArcOfS`, `sVertOfS`
together with closure, boundary and containment lemmas for them.

## Main definitions

* `pvIntegrand` — the ε-truncated integrand for the CPV of `f'/f`.
* `sArcOfS`, `sVertOfS` — arc and vertical singular sets of `S`.
* `onCurvePVProvider` — predicate witnessing CPV existence on the boundary.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-- The ε-truncated integrand for the PV integral of `f'/f` along `γ`,
with singular set `S₀`. Zero when `γ(t)` is within `ε` of any `s ∈ S₀`,
otherwise `logDeriv f (γ t) * γ'(t)`. -/
noncomputable def pvIntegrand {k : ℤ} (f : ModularForm (Gamma 1) k) (γ : ℝ → ℂ)
    (S₀ : Finset ℂ) (ε : ℝ) (t : ℝ) : ℂ :=
  cpvIntegrandOn S₀ (logDeriv (modularFormCompOfComplex f)) γ ε t

/-- Arc singular set: unit-circle zeros (and S-transforms) plus ρ, ρ+1. -/
noncomputable def sArcOfS (S : Finset UpperHalfPlane) : Finset ℂ :=
  (S.filter (fun (p : ℍ) => ‖(↑p : ℂ)‖ = 1)).image (↑· : ℍ → ℂ) ∪
  (S.filter (fun (p : ℍ) => ‖(↑p : ℂ)‖ = 1)).image (fun (p : ℍ) => -(1 : ℂ) / (↑p : ℂ)) ∪
  {ellipticPointRho, ellipticPointRhoPlusOne}

/-- Vertical singular set: re = ±1/2, ‖z‖ > 1 zeros, plus T-shifts. -/
noncomputable def sVertOfS (S : Finset UpperHalfPlane) : Finset ℂ :=
  (S.filter (fun p : ℍ => (↑p : ℂ).re = 1/2 ∧ ‖(↑p : ℂ)‖ > 1)).image
    (↑· : ℍ → ℂ) ∪
  (S.filter (fun p : ℍ => (↑p : ℂ).re = 1/2 ∧ ‖(↑p : ℂ)‖ > 1)).image
    (fun p : ℍ => (↑p : ℂ) - 1) ∪
  (S.filter (fun p : ℍ => (↑p : ℂ).re = -1/2 ∧ ‖(↑p : ℂ)‖ > 1)).image
    (↑· : ℍ → ℂ) ∪
  (S.filter (fun p : ℍ => (↑p : ℂ).re = -1/2 ∧ ‖(↑p : ℂ)‖ > 1)).image
    (fun p : ℍ => (↑p : ℂ) + 1)

lemma sArcOfS_rho_in (S : Finset UpperHalfPlane) :
    ellipticPointRho ∈ sArcOfS S := by
  simp [sArcOfS]

omit f hf in
lemma sArcOfS_rho_plus_one_in (S : Finset UpperHalfPlane) :
    ellipticPointRhoPlusOne ∈ sArcOfS S := by
  simp [sArcOfS]

omit f hf in
lemma sArcOfS_unit (S : Finset UpperHalfPlane) :
    ∀ s ∈ sArcOfS S, ‖s‖ = 1 := by
  intro s hs
  simp only [sArcOfS, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with ⟨⟨p, ⟨_, hp_norm⟩, rfl⟩ | ⟨p, ⟨_, hp_norm⟩, rfl⟩⟩ | hs
  · exact hp_norm
  · rw [norm_div, norm_neg, norm_one, hp_norm, div_one]
  · rcases hs with rfl | rfl
    · exact ellipticPointRho_norm
    · exact ellipticPointRhoPlusOne_norm

omit f hf in
private lemma neg_inv_rho_eq_rho_plus_one :
    -(1 : ℂ) / ellipticPointRho = ellipticPointRhoPlusOne := by
  have hre : (ellipticPointRho : ℂ).re = -1/2 := by
    simp [ellipticPointRho, ellipticPointRho']
  have him : (ellipticPointRho : ℂ).im = Real.sqrt 3 / 2 := by
    simp [ellipticPointRho, ellipticPointRho']
  have hre2 : (ellipticPointRhoPlusOne : ℂ).re = 1/2 := by
    simp [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne']
  have him2 : (ellipticPointRhoPlusOne : ℂ).im = Real.sqrt 3 / 2 := by
    simp [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne']
  have hnormSq :
      -(1/2 : ℝ) * -(1/2) + Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) = 1 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  apply Complex.ext
  · simp only [neg_div, Complex.neg_re, Complex.div_re,
      Complex.one_re, Complex.one_im, Complex.normSq_apply,
      hre, him, hre2, hnormSq]
    ring
  · simp only [neg_div, Complex.neg_im, Complex.div_im,
      Complex.one_re, Complex.one_im, Complex.normSq_apply,
      hre, him, him2, hnormSq]
    ring

omit f hf in
private lemma neg_inv_rho_plus_one_eq_rho :
    -(1 : ℂ) / ellipticPointRhoPlusOne = ellipticPointRho := by
  have hre : (ellipticPointRhoPlusOne : ℂ).re = 1/2 := by
    simp [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne']
  have him : (ellipticPointRhoPlusOne : ℂ).im = Real.sqrt 3 / 2 := by
    simp [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne']
  have hre2 : (ellipticPointRho : ℂ).re = -1/2 := by
    simp [ellipticPointRho, ellipticPointRho']
  have him2 : (ellipticPointRho : ℂ).im = Real.sqrt 3 / 2 := by
    simp [ellipticPointRho, ellipticPointRho']
  have hnormSq : (1/2 : ℝ) * (1/2) + Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) = 1 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  apply Complex.ext
  · simp only [neg_div, Complex.neg_re, Complex.div_re,
      Complex.one_re, Complex.one_im, Complex.normSq_apply,
      hre, him, hre2, hnormSq]
    ring
  · simp only [neg_div, Complex.neg_im, Complex.div_im,
      Complex.one_re, Complex.one_im, Complex.normSq_apply,
      hre, him, him2, hnormSq]
    ring

omit f hf in
lemma sArcOfS_closed (S : Finset UpperHalfPlane) :
    ∀ s ∈ sArcOfS S, -(1 : ℂ) / s ∈ sArcOfS S := by
  intro s hs
  simp only [sArcOfS, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hs ⊢
  rcases hs with ⟨⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩⟩ | hs
  · exact Or.inl (Or.inr ⟨p, hp, rfl⟩)
  · refine Or.inl (Or.inl ⟨p, hp, ?_⟩)
    have : (↑p : ℂ) ≠ 0 := norm_pos_iff.mp (by rw [hp.2]; norm_num)
    field_simp
  · rcases hs with rfl | rfl
    · exact Or.inr (Or.inr neg_inv_rho_eq_rho_plus_one)
    · exact Or.inr (Or.inl neg_inv_rho_plus_one_eq_rho)

omit f hf in
lemma sVertOfS_re (S : Finset UpperHalfPlane) :
    ∀ s ∈ sVertOfS S, s.re = 1/2 ∨ s.re = -1/2 := by
  intro s hs
  simp only [sVertOfS, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hs
  rcases hs with ⟨⟨⟨p, ⟨_, hp_re, _⟩, rfl⟩ | ⟨p, ⟨_, hp_re, _⟩, rfl⟩⟩ |
    ⟨p, ⟨_, hp_re, _⟩, rfl⟩⟩ | ⟨p, ⟨_, hp_re, _⟩, rfl⟩
  · exact Or.inl hp_re
  · right
    simp only [Complex.sub_re, Complex.one_re, hp_re]
    norm_num
  · exact Or.inr hp_re
  · left
    simp only [Complex.add_re, Complex.one_re, hp_re]
    norm_num

omit f hf in
lemma sVertOfS_pair_left (S : Finset UpperHalfPlane) :
    ∀ s ∈ sVertOfS S, s.re = 1/2 → s - 1 ∈ sVertOfS S := by
  intro s hs hre
  simp only [sVertOfS, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hs ⊢
  rcases hs with ⟨⟨⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩⟩ | ⟨p, hp, rfl⟩⟩ | ⟨p, hp, rfl⟩
  · exact Or.inl (Or.inl (Or.inr ⟨p, hp, rfl⟩))
  · exfalso
    simp only [Complex.sub_re, Complex.one_re, hp.2.1] at hre
    norm_num at hre
  · exfalso
    linarith [hp.2.1]
  · refine Or.inl (Or.inr ⟨p, hp, ?_⟩)
    ring

omit f hf in
lemma sVertOfS_pair_right (S : Finset UpperHalfPlane) :
    ∀ s ∈ sVertOfS S, s.re = -1/2 → s + 1 ∈ sVertOfS S := by
  intro s hs hre
  simp only [sVertOfS, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hs ⊢
  rcases hs with ⟨⟨⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩⟩ | ⟨p, hp, rfl⟩⟩ | ⟨p, hp, rfl⟩
  · exfalso
    linarith [hp.2.1]
  · refine Or.inl (Or.inl (Or.inl ⟨p, hp, ?_⟩))
    ring
  · exact Or.inr ⟨p, hp, rfl⟩
  · exfalso
    simp only [Complex.add_re, Complex.one_re, hp.2.1] at hre
    norm_num at hre

omit f hf in
/-- There exists a height above √3/2 exceeding all points in `S`. -/
theorem exists_height_bound_S (S : Finset UpperHalfPlane) :
    ∃ H₁ : ℝ, Real.sqrt 3 / 2 < H₁ ∧ 1 < H₁ ∧ ∀ s ∈ S, (s : ℂ).im < H₁ := by
  have hsqrt3 : Real.sqrt 3 / 2 < 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  rcases S.eq_empty_or_nonempty with h_empty | h_ne
  · exact ⟨2, hsqrt3, by norm_num, by simp [h_empty]⟩
  set M := S.sup' h_ne (fun s : ℍ => (s : ℂ).im)
  refine ⟨max 2 (M + 1), lt_of_lt_of_le hsqrt3 (le_max_left _ _),
      lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _), fun s hs => ?_⟩
  calc (s : ℂ).im ≤ M := Finset.le_sup' (fun s : ℍ => (↑s : ℂ).im) hs
    _ < M + 1 := by linarith
    _ ≤ max 2 (M + 1) := le_max_right _ _

omit f hf in
/-- All elements of `sVertOfS S` have im < H₁ when all elements of `S` have im < H₁. -/
lemma sVertOfS_im_lt_height_bound (S : Finset UpperHalfPlane) (s : ℂ)
    (hs : s ∈ sVertOfS S) (h_bound : ∀ p ∈ S, (p : ℂ).im < H₁) :
    s.im < H₁ := by
  simp only [sVertOfS, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hs
  rcases hs with ⟨⟨⟨p, ⟨hp_mem, _⟩, rfl⟩ | ⟨p, ⟨hp_mem, _⟩, rfl⟩⟩ |
    ⟨p, ⟨hp_mem, _⟩, rfl⟩⟩ | ⟨p, ⟨hp_mem, _⟩, rfl⟩ <;>
    first | exact h_bound p hp_mem | simpa using h_bound p hp_mem

omit hf in
/-- Summing `gWN · ord` over all of `S` equals summing over just zeros. -/
theorem sum_gWN_ord_eq_filter_zeros (S : Finset UpperHalfPlane) (g : ℂ → ℂ) :
    ∑ s ∈ S, g (↑s : ℂ) * (orderOfVanishingAt' (⇑f) s : ℂ) =
    ∑ s ∈ S.filter (fun p => f p = 0),
      g (↑s : ℂ) * (orderOfVanishingAt' (⇑f) s : ℂ) := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs with h
  · rfl
  · simp [orderOfVanishingAt'_eq_zero_of_ne_zero' f p h]

omit f hf in
/-- All elements of `sArcOfS S` have positive imaginary part. -/
lemma sArcOfS_im_pos (S : Finset UpperHalfPlane) (s : ℂ) (hs : s ∈ sArcOfS S) :
    0 < s.im := by
  simp only [sArcOfS, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with ⟨⟨p, ⟨_, _⟩, rfl⟩ | ⟨p, ⟨_, hp_norm⟩, rfl⟩⟩ | hs
  · exact p.2
  · have hz_ne : (↑p : ℂ) ≠ 0 := fun h => by simp [h] at hp_norm
    rw [show -(1 : ℂ) / (↑p : ℂ) = (-(↑p : ℂ))⁻¹ from by field_simp, Complex.inv_im]
    simp only [neg_im, neg_neg]
    exact div_pos p.2 (Complex.normSq_pos.mpr (neg_ne_zero.mpr hz_ne))
  · rcases hs with rfl | rfl <;>
      simp [ellipticPointRho, ellipticPointRhoPlusOne,
        ellipticPointRho', ellipticPointRhoPlusOne']

omit f hf in
/-- All elements of `sVertOfS S` have positive imaginary part. -/
lemma sVertOfS_im_pos (S : Finset UpperHalfPlane) (s : ℂ) (hs : s ∈ sVertOfS S) :
    0 < s.im := by
  simp only [sVertOfS, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hs
  rcases hs with ⟨⟨⟨p, _, rfl⟩ | ⟨p, _, rfl⟩⟩ | ⟨p, _, rfl⟩⟩ | ⟨p, _, rfl⟩ <;>
    first | exact p.2 | simpa using p.2

omit f hf in
private lemma sVertOfS_re_bound (S : Finset UpperHalfPlane) (s : ℂ)
    (hs : s ∈ sVertOfS S) : |s.re| ≤ 1/2 := by
  simp only [sVertOfS, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hs
  rcases hs with ⟨⟨⟨p, ⟨_, hp_re, _⟩, rfl⟩ | ⟨p, ⟨_, hp_re, _⟩, rfl⟩⟩ |
    ⟨p, ⟨_, hp_re, _⟩, rfl⟩⟩ | ⟨p, ⟨_, hp_re, _⟩, rfl⟩
  all_goals first
    | (rw [hp_re]; norm_num)
    | (simp only [Complex.sub_re, Complex.add_re, Complex.one_re, hp_re]; norm_num)

omit f hf in
private lemma im_gt_sqrt3_half_of_re_half_and_norm_gt_one (p : ℍ)
    (hre : (↑p : ℂ).re = 1/2 ∨ (↑p : ℂ).re = -1/2) (hnorm : ‖(↑p : ℂ)‖ > 1) :
    (↑p : ℂ).im > Real.sqrt 3 / 2 := by
  have h_eq : ‖(↑p : ℂ)‖ ^ 2 = (↑p : ℂ).re ^ 2 + (↑p : ℂ).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h_re_sq : (↑p : ℂ).re ^ 2 = 1/4 := by rcases hre with h | h <;> · rw [h]; ring
  have h_im_sq' : (Real.sqrt 3 / 2) ^ 2 < (↑p : ℂ).im ^ 2 := by
    rw [div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    nlinarith [sq_nonneg (‖(↑p : ℂ)‖ - 1)]
  have h_sqrt_ineq := Real.sqrt_lt_sqrt (sq_nonneg (Real.sqrt 3 / 2)) h_im_sq'
  rwa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Real.sqrt 3 / 2),
    Real.sqrt_sq p.2.le] at h_sqrt_ineq

omit f hf in
private lemma sVertOfS_im_gt_sqrt3_half (S : Finset UpperHalfPlane) (s : ℂ)
    (hs : s ∈ sVertOfS S) : s.im > Real.sqrt 3 / 2 := by
  simp only [sVertOfS, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hs
  rcases hs with ⟨⟨⟨p, ⟨_, hp_re, hp_norm⟩, rfl⟩ | ⟨p, ⟨_, hp_re, hp_norm⟩, rfl⟩⟩ |
    ⟨p, ⟨_, hp_re, hp_norm⟩, rfl⟩⟩ | ⟨p, ⟨_, hp_re, hp_norm⟩, rfl⟩
  · exact im_gt_sqrt3_half_of_re_half_and_norm_gt_one p (Or.inl hp_re) hp_norm
  · simpa using im_gt_sqrt3_half_of_re_half_and_norm_gt_one p (Or.inl hp_re) hp_norm
  · exact im_gt_sqrt3_half_of_re_half_and_norm_gt_one p (Or.inr hp_re) hp_norm
  · simpa using im_gt_sqrt3_half_of_re_half_and_norm_gt_one p (Or.inr hp_re) hp_norm

omit f hf in
private lemma im_ge_sqrt3_half_of_re_half_and_norm_eq_one (p : ℍ)
    (hre : |(↑p : ℂ).re| ≤ 1/2) (hnorm : ‖(↑p : ℂ)‖ = 1) :
    (↑p : ℂ).im ≥ Real.sqrt 3 / 2 := by
  have h_eq : ‖(↑p : ℂ)‖ ^ 2 = (↑p : ℂ).re ^ 2 + (↑p : ℂ).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h_im_sq' : (Real.sqrt 3 / 2) ^ 2 ≤ (↑p : ℂ).im ^ 2 := by
    rw [div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    nlinarith [abs_le.mp hre, hnorm]
  rw [ge_iff_le, ← Real.sqrt_sq p.2.le,
    ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Real.sqrt 3 / 2)]
  exact Real.sqrt_le_sqrt h_im_sq'

omit f hf in
private lemma sArcOfS_im_ge_sqrt3_half (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (s : ℂ) (h_arc : s ∈ sArcOfS S) : s.im ≥ Real.sqrt 3 / 2 := by
  simp only [sArcOfS, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at h_arc
  rcases h_arc with ⟨⟨p, ⟨hp_mem, hp_norm⟩, rfl⟩ | ⟨p, ⟨hp_mem, hp_norm⟩, rfl⟩⟩ | h_ell
  · exact im_ge_sqrt3_half_of_re_half_and_norm_eq_one p (hS p hp_mem).2 hp_norm
  · have hz_ne : (↑p : ℂ) ≠ 0 := fun h => by simp [h] at hp_norm
    have h_eq : (-(1 : ℂ) / (↑p : ℂ)).im = (↑p : ℂ).im := by
      rw [show -(1 : ℂ) / (↑p : ℂ) = (-(↑p : ℂ))⁻¹ from by field_simp,
        Complex.inv_im, Complex.normSq_neg]
      have h_nsq_val : Complex.normSq (↑p : ℂ) = 1 := by
        rw [← Complex.sq_norm, hp_norm]; norm_num
      rw [h_nsq_val, neg_im, neg_neg, div_one]
    rw [h_eq]
    exact im_ge_sqrt3_half_of_re_half_and_norm_eq_one p (hS p hp_mem).2 hp_norm
  · rcases h_ell with rfl | rfl <;>
      simp [ellipticPointRho, ellipticPointRhoPlusOne,
        ellipticPointRho', ellipticPointRhoPlusOne']

omit f hf in
/-- On-curve singular points lie inside `fdBox M` when `H < M`. -/
lemma fdBox_of_on_curve (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    {H M : ℝ} (_hH_sqrt3 : Real.sqrt 3 / 2 < H) (hH_lt_M : H < M) (hH_ge1 : 1 ≤ H)
    (hH_bound : ∀ s ∈ S, (s : ℂ).im < H)
    (s : ℂ) (hs : s ∈ sArcOfS S ∪ sVertOfS S) : s ∈ fdBox M := by
  have sqrt3_gt_one : (1 : ℝ) < Real.sqrt 3 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  rcases Finset.mem_union.mp hs with h_arc | h_vert
  · have h_unit := sArcOfS_unit S s h_arc
    have h_nsq : s.re ^ 2 + s.im ^ 2 = 1 := by
      have h_sq : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      nlinarith [h_unit, h_sq]
    have h_im_le : s.im ≤ 1 := by nlinarith
    have h_im_ge := sArcOfS_im_ge_sqrt3_half S hS s h_arc
    refine ⟨?_, ?_, by linarith, by linarith⟩ <;> nlinarith [sq_abs s.re]
  · have h_re := sVertOfS_re_bound S s h_vert
    have h_im_gt := sVertOfS_im_gt_sqrt3_half S s h_vert
    have h_im_lt := sVertOfS_im_lt_height_bound S s h_vert hH_bound
    exact ⟨by linarith [abs_le.mp h_re], by linarith [abs_le.mp h_re],
      by linarith, by linarith⟩

end

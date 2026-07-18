/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.NormTrace
import LeanModularForms.ForMathlib.ValenceFormulaFinal
import LeanModularForms.Modularforms.ForMathlib_Cusps

/-!
# The modular `j`-function

The `j`-function `j = E₄³ / Δ` is the fundamental weight-zero modular function for `SL₂(ℤ)`.
This file defines `j`, proves it is `SL₂(ℤ)`-invariant, holomorphic on `ℍ`, surjective, and
(via the valence formula) injective on a fundamental domain.
-/

open Filter ModularForm ModularFormClass MatrixGroups Function CongruenceSubgroup
open scoped Manifold
open UpperHalfPlane hiding I

local notation "𝕢" => Periodic.qParam

noncomputable section

private abbrev E4 : ModularForm 𝒮ℒ 4 := ModularForm.E₄

private abbrev Delta : CuspForm 𝒮ℒ 12 := CuspForm.discriminant

/-- This defines the `j` function as E4^3/Δ -/
def j : ℍ → ℂ := fun τ ↦ (E4 τ) ^ 3 / Delta τ

private lemma j_slashInvariant (γ : SL(2, ℤ)) : j ∣[(0 : ℤ)] γ = j := by
  ext z
  rw [slash_action_eq'_iff, j, j]
  have h1 : E4 (γ • z) = ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ^ (4 : ℤ) * E4 z :=
    SlashInvariantForm.slash_action_eqn' E4 (MonoidHom.mem_range.mpr ⟨γ, rfl⟩) z
  have h2 : Delta (γ • z) = ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ^ (12 : ℤ) * Delta z :=
    SlashInvariantForm.slash_action_eqn' Delta (MonoidHom.mem_range.mpr ⟨γ, rfl⟩) z
  rw [h1, h2]
  have hden : ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ≠ 0 := by
    simpa [ModularGroup.denom_apply] using denom_ne_zero γ z
  field_simp [hden, ModularForm.discriminant_ne_zero z]

def Deltaoverq : ℍ → ℂ := fun z ↦ ∏' (n : ℕ), (1 - ModularForm.eta_q n z) ^ 24

lemma Delta_eq_q_mul_Deltaoverq (z : ℍ) : Delta z = 𝕢 1 z * Deltaoverq z := by
  simpa [Delta, Deltaoverq] using ModularForm.discriminant_eq_q_prod z

lemma Deltaoverq_ne_zero (z : ℍ) : Deltaoverq z ≠ 0 := by
  intro h
  have hD : Delta z = 0 := by simp [Delta_eq_q_mul_Deltaoverq z, h]
  exact ModularForm.discriminant_ne_zero z (by simpa [Delta] using hD)

def qoverDelta : ℍ → ℂ := fun z ↦ 1 / Deltaoverq z

def qj : ℍ → ℂ := (fun z ↦ 𝕢 1 z : ℍ → ℂ) * j

lemma qjIdentity : (fun z : ℍ => (E4 z) ^ 3) * qoverDelta = qj := by
  ext z
  simp only [Pi.mul_apply, qj, j, qoverDelta]
  have hDnz : Delta z ≠ 0 := by simpa [Delta] using ModularForm.discriminant_ne_zero z
  field_simp [hDnz, Deltaoverq_ne_zero z]
  linear_combination E4 z ^ 3 * Delta_eq_q_mul_Deltaoverq z

lemma Deltaoverq_tendsto_atImInfty : Tendsto Deltaoverq atImInfty (nhds (1 : ℂ)) :=
  ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow

lemma qoverDelta_tendsto_atImInfty : Tendsto qoverDelta atImInfty (nhds (1 : ℂ)) := by
  have h : Tendsto (fun τ : ℍ => (Deltaoverq τ)⁻¹) atImInfty (nhds ((1 : ℂ)⁻¹)) :=
    Deltaoverq_tendsto_atImInfty.inv₀ (by norm_num)
  change Tendsto (fun τ : ℍ => (1 / Deltaoverq τ)) atImInfty (nhds (1 : ℂ))
  simpa [one_div] using h

lemma E4_tendsto_atImInfty : Tendsto (E4 : ℍ → ℂ) atImInfty (nhds (1 : ℂ)) := by
  have hper : Periodic ((E4 : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex E4 one_mem_strictPeriods_SL
  have h0 : cuspFunction 1 (E4 : ℍ → ℂ) 0 = 1 := by
    simpa [qExpansion_coeff, E4] using
      (EisensteinSeries.E_qExpansion_coeff_zero (by norm_num : 3 ≤ 4) ⟨2, rfl⟩)
  simpa only [Function.comp_def, UpperHalfPlane.eq_cuspFunction _ one_ne_zero hper, h0] using
    (ModularFormClass.analyticAt_cuspFunction_zero (h := (1 : ℝ)) E4 (by norm_num)
      one_mem_strictPeriods_SL).continuousAt.tendsto.comp
      (UpperHalfPlane.qParam_tendsto_atImInfty (h := 1) (by norm_num))

lemma j_MDifferentiable : MDiff j := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  have hE4 : DifferentiableAt ℂ (E4 ∘ UpperHalfPlane.ofComplex) z :=
    UpperHalfPlane.mdifferentiableAt_iff.mp (ModularFormClass.holo E4 ⟨z, hz⟩)
  have hDelta : DifferentiableAt ℂ (Delta ∘ UpperHalfPlane.ofComplex) z :=
    UpperHalfPlane.mdifferentiableAt_iff.mp (ModularFormClass.holo Delta ⟨z, hz⟩)
  have hDelta0 : (Delta ∘ UpperHalfPlane.ofComplex) z ≠ 0 := by
    simpa [comp, UpperHalfPlane.ofComplex_apply_of_im_pos hz, Delta] using
      ModularForm.discriminant_ne_zero (UpperHalfPlane.ofComplex z)
  have hj : DifferentiableAt ℂ (j ∘ UpperHalfPlane.ofComplex) z :=
    (hE4.pow 3).div hDelta hDelta0
  exact hj.differentiableWithinAt

theorem qj_tendsto_atImInfty : Tendsto qj atImInfty (nhds (1 : ℂ)) := by
  have hE4 : Tendsto (fun τ : ℍ => (E4 τ) ^ 3) atImInfty (nhds ((1 : ℂ) ^ 3)) :=
    E4_tendsto_atImInfty.pow 3
  have hqj : Tendsto ((fun τ : ℍ => (E4 τ) ^ 3) * qoverDelta) atImInfty
      (nhds ((1 : ℂ) ^ 3 * 1)) :=
    hE4.mul qoverDelta_tendsto_atImInfty
  have hEq : ((fun τ : ℍ => (E4 τ) ^ 3) * qoverDelta) = qj := by
    ext τ
    exact congrFun qjIdentity τ
  simpa [hEq] using hqj

def levelOneWeightZeroCuspForm {f : ℍ → ℂ} (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f)
    (hmdiff : MDiff f) (hzero : IsZeroAtImInfty f) : CuspForm (Gamma 1) 0 where
  toFun := f
  slash_action_eq' := fun γ hγ => by
    obtain ⟨γ', _, rfl⟩ := hγ
    exact hslash γ'
  holo' := hmdiff
  zero_at_cusps' := fun hc =>
    zero_at_cusps_of_zero_at_infty hc fun A hA => by
      obtain ⟨γ, rfl⟩ := hA
      have hγ : f ∣[(0 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ) = f := hslash γ
      simpa [hγ] using hzero

theorem weight_zero_cuspForm_eq_zero {f : ℍ → ℂ}
    (hslash : ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f) (hmdiff : MDiff f) (hzero : IsZeroAtImInfty f) :
    f = 0 := by
  let F : ModularForm (Gamma 1) 0 := levelOneWeightZeroCuspForm hslash hmdiff hzero
  obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero F
  have hc0 : c = 0 :=
    tendsto_nhds_unique tendsto_const_nhds (hc ▸ show IsZeroAtImInfty ⇑F from hzero)
  ext z
  show (F : ℍ → ℂ) z = 0
  simpa [hc0] using congrFun hc z

theorem f_slashInvariant (c : ℂ) : letI f : ℍ → ℂ := fun τ => (j τ - c)⁻¹
    ∀ γ : SL(2, ℤ), f ∣[(0 : ℤ)] γ = f := by
  intro γ
  ext τ
  have hj := congrFun (j_slashInvariant γ) τ
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one] at hj ⊢
  simpa [hj]

theorem f_MDiff (c : ℂ) (hc : ∀ τ : ℍ, j τ ≠ c) :
    MDiff (fun τ : ℍ => (j τ - c)⁻¹) := fun τ =>
  ((j_MDifferentiable τ).sub mdifferentiableAt_const).inv (sub_ne_zero.mpr (hc τ))

theorem f_IsZeroAtInfty (c : ℂ) : IsZeroAtImInfty (fun τ : ℍ => (j τ - c)⁻¹) := by
  let q : ℍ → ℂ := fun τ => 𝕢 1 τ
  have hq : Tendsto q atImInfty (nhds 0) := qParam_tendsto_atImInfty (by norm_num)
  have hden : Tendsto (fun τ : ℍ => qj τ - c * q τ) atImInfty (nhds 1) := by
    simpa using qj_tendsto_atImInfty.sub (tendsto_const_nhds.mul hq)
  have hratio : Tendsto (fun τ : ℍ => q τ / (qj τ - c * q τ)) atImInfty (nhds 0) := by
    simpa [div_eq_mul_inv] using hq.mul (hden.inv₀ (by norm_num : (1 : ℂ) ≠ 0))
  have hEq : (fun τ : ℍ => (j τ - c)⁻¹) =ᶠ[atImInfty] fun τ : ℍ => q τ / (qj τ - c * q τ) := by
    refine Eventually.of_forall fun τ => ?_
    simp only [show qj τ = q τ * j τ from by simp [q, qj, Periodic.qParam]]
    field_simp [show q τ ≠ 0 from by simp [q, Periodic.qParam]]
  exact hratio.congr' hEq.symm

/-- The modular `j`-function is surjective. -/
theorem j_surjective : Function.Surjective j := by
  intro c
  by_contra! hc
  let f : ℍ → ℂ := fun τ => (j τ - c)⁻¹
  have hf := weight_zero_cuspForm_eq_zero (f_slashInvariant c) (f_MDiff c hc) (f_IsZeroAtInfty c)
  have τ : ℍ := Classical.arbitrary ℍ
  exact inv_ne_zero (sub_ne_zero.mpr (hc τ)) (congrFun hf τ)

/-- The weight-12 modular form `g = E₄³ − a·Δ` on `Γ(1) = SL₂(ℤ)`, used to detect the
fiber `j⁻¹(a)`: we have `j τ = a ↔ gForm a τ = 0`. -/
def gForm (a : ℂ) : ModularForm (Gamma 1) 12 :=
  ModularForm.mcast (by norm_num) (E4.pow 3) Gamma_one_coe_eq_SL -
    ModularForm.mcast rfl (a • (Delta : ModularForm 𝒮ℒ 12)) Gamma_one_coe_eq_SL

lemma gForm_apply (a : ℂ) (τ : ℍ) : gForm a τ = (E4 τ) ^ 3 - a * Delta τ := by
  simp only [gForm, ModularForm.coe_sub, Pi.sub_apply, ModularForm.coe_mcast, ModularForm.coe_pow,
    Pi.pow_apply, ModularForm.IsGLPos.smul_apply, smul_eq_mul]
  rfl

/-- `j τ = a` iff the weight-12 form `gForm a` vanishes at `τ`. -/
lemma j_eq_iff_gForm_zero (a : ℂ) (τ : ℍ) : j τ = a ↔ gForm a τ = 0 := by
  have hΔ : Delta τ ≠ 0 := by simpa [Delta] using ModularForm.discriminant_ne_zero τ
  rw [gForm_apply, sub_eq_zero, j, div_eq_iff hΔ]

/-- The weight-12 form `gForm a` is nonzero: if it vanished identically, `j` would be the
constant `a`, contradicting surjectivity. -/
lemma gForm_ne_zero (a : ℂ) : gForm a ≠ 0 := by
  intro hg
  obtain ⟨τ, hτ⟩ := j_surjective (a + 1)
  have hτa : j τ = a := (j_eq_iff_gForm_zero a τ).mpr (by rw [hg]; rfl)
  rw [hτa] at hτ
  exact (by norm_num : a ≠ a + 1) hτ

/-- The cusp limit of `gForm a` is `1` (constant term of its `q`-expansion). -/
lemma gForm_tendsto_atImInfty (a : ℂ) :
    Tendsto (gForm a) atImInfty (nhds (1 : ℂ)) := by
  have hΔ : Tendsto (Delta : ℍ → ℂ) atImInfty (nhds (0 : ℂ)) :=
    ModularForm.discriminant_isZeroAtImInfty
  have h1 : Tendsto (fun τ : ℍ => (E4 τ) ^ 3 - a * Delta τ) atImInfty
      (nhds ((1 : ℂ) ^ 3 - a * 0)) :=
    (E4_tendsto_atImInfty.pow 3).sub (tendsto_const_nhds.mul hΔ)
  refine (h1.congr (fun τ => (gForm_apply a τ).symm)).mono_right ?_
  rw [show (1 : ℂ) ^ 3 - a * 0 = 1 by ring]

/-- The constant term of the `q`-expansion of `gForm a` is `1`. -/
lemma gForm_qExpansion_coeff_zero (a : ℂ) :
    (UpperHalfPlane.qExpansion 1 (gForm a)).coeff 0 = 1 := by
  have hsp : (1 : ℝ) ∈ (Gamma 1 : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
    Gamma_one_coe_eq_SL.symm ▸ one_mem_strictPeriods_SL
  have hper : Periodic ((gForm a : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex (gForm a) hsp
  have hanalytic : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (gForm a)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero (gForm a) (by norm_num) hsp
  rw [UpperHalfPlane.qExpansion_coeff_zero (by norm_num) hanalytic hper]
  exact (gForm_tendsto_atImInfty a).limUnder_eq

/-- The order of vanishing of `gForm a` at the cusp is `0`. -/
lemma orderAtCusp'_gForm (a : ℂ) : orderAtCusp' (gForm a) = 0 := by
  have hcoeff : (UpperHalfPlane.qExpansion 1 (gForm a)).coeff 0 ≠ 0 := by
    rw [gForm_qExpansion_coeff_zero a]; exact one_ne_zero
  have hord : (UpperHalfPlane.qExpansion 1 (gForm a)).order = 0 :=
    le_antisymm (by simpa using PowerSeries.order_le 0 hcoeff) bot_le
  rw [orderAtCusp', hord]; rfl

/-- The order of vanishing of `gForm a` at any point of `ℍ` is nonnegative (since `gForm a`
is holomorphic). -/
lemma orderOfVanishingAt'_gForm_nonneg (a : ℂ) (p : ℍ) :
    0 ≤ orderOfVanishingAt' (gForm a) p := by
  rw [orderOfVanishingAt', WithTop.untop₀_nonneg]
  exact (G_analyticAtFM (gForm a) p).meromorphicOrderAt_nonneg

/-- The non-elliptic orbit sum of `gForm a`, as an integer. -/
private def gFormOrbitSumℤ (a : ℂ) : ℤ :=
  ∑ᶠ (q : NonEllOrbitFM), ordOrbitFM (gForm a) q.val

/-- The cast of the integer orbit sum agrees with the complex orbit sum in the valence
formula. -/
private lemma gFormOrbitSum_cast (a : ℂ) :
    ((gFormOrbitSumℤ a : ℤ) : ℂ) = ∑ᶠ (q : NonEllOrbitFM), ordOrbitQ (gForm a) q := by
  have hsupp : (Function.support
      (fun q : NonEllOrbitFM => ordOrbitFM (gForm a) q.val)).Finite :=
    (finite_support_ordOrbit_nonEllFM (gForm a) (gForm_ne_zero a)).subset fun _ h => h
  have hmap := map_finsum (Int.castRingHom ℂ)
    (f := fun q : NonEllOrbitFM => ordOrbitFM (gForm a) q.val) hsupp
  simp only [Int.coe_castRingHom] at hmap
  rw [gFormOrbitSumℤ, hmap]
  rfl

/-- The integer Diophantine consequence of the valence formula for `gForm a`:
`3·A + 2·B + 6·S = 6`, where `A`, `B` are the orders at `i`, `ρ` and `S` is the non-elliptic
orbit sum (all `≥ 0`). -/
private lemma gForm_valence_diophantine (a : ℂ) :
    3 * orderOfVanishingAt' (gForm a) ellipticPointI' +
    2 * orderOfVanishingAt' (gForm a) ellipticPointRho' +
    6 * gFormOrbitSumℤ a = 6 := by
  have hvf := valence_formula_textbook (gForm a) (gForm_ne_zero a)
  rw [orderAtCusp'_gForm a] at hvf
  rw [← gFormOrbitSum_cast a] at hvf
  -- Now hvf : (0 : ℂ) + (1/2)*A + (1/3)*B + (S : ℂ) = 12/12
  have hcast : ((3 * orderOfVanishingAt' (gForm a) ellipticPointI' +
      2 * orderOfVanishingAt' (gForm a) ellipticPointRho' +
      6 * gFormOrbitSumℤ a : ℤ) : ℂ) = ((6 : ℤ) : ℂ) := by
    push_cast
    push_cast at hvf
    linear_combination 6 * hvf
  exact_mod_cast hcast

/-- All orbit orders of `gForm a` are nonnegative. -/
private lemma ordOrbitFM_gForm_nonneg (a : ℂ) (q : OrbitFM) :
    0 ≤ ordOrbitFM (gForm a) q := by
  induction q using Quotient.inductionOn' with
  | h p => exact orderOfVanishingAt'_gForm_nonneg a p

/-- The non-elliptic orbit sum of `gForm a` is nonnegative. -/
private lemma gFormOrbitSumℤ_nonneg (a : ℂ) : 0 ≤ gFormOrbitSumℤ a := by
  rw [gFormOrbitSumℤ]
  exact finsum_nonneg fun q => ordOrbitFM_gForm_nonneg a q.val

/-- At a zero `p` of `gForm a`, the order of vanishing is at least `1`. -/
private lemma one_le_orderOfVanishingAt'_gForm (a : ℂ) (p : ℍ) (hp : gForm a p = 0) :
    1 ≤ orderOfVanishingAt' (gForm a) p := by
  have hne := orderOfVanishingAt'_ne_zero_of_eq_zeroFM (gForm a) (gForm_ne_zero a) p hp
  have hge := orderOfVanishingAt'_gForm_nonneg a p
  omega

/-- A zero `p` of `gForm a` forces order `≥ 1` at every point of its orbit.  The order is an
orbit invariant (`ordOrbit_mkFM`), so it may be read off at any representative. -/
private lemma one_le_orderOfVanishingAt'_of_orb_eq (a : ℂ) {p x : ℍ} (hp : gForm a p = 0)
    (horb : orbFM p = orbFM x) : 1 ≤ orderOfVanishingAt' (gForm a) x := by
  have h := ordOrbit_mkFM (gForm a) p
  rw [horb, ordOrbit_mkFM] at h
  rw [h]; exact one_le_orderOfVanishingAt'_gForm a p hp

/-- If a zero `p` of `gForm a` lies in the orbit of `i`, then the order `A` at `i` is `≥ 1`. -/
private lemma slot_i (a : ℂ) (p : ℍ) (hp : gForm a p = 0) (horb : orbFM p = oiFM) :
    1 ≤ orderOfVanishingAt' (gForm a) ellipticPointI' :=
  one_le_orderOfVanishingAt'_of_orb_eq a hp horb

/-- If a zero `p` of `gForm a` lies in the orbit of `ρ`, then the order `B` at `ρ` is `≥ 1`. -/
private lemma slot_rho (a : ℂ) (p : ℍ) (hp : gForm a p = 0) (horb : orbFM p = orhoFM) :
    1 ≤ orderOfVanishingAt' (gForm a) ellipticPointRho' :=
  one_le_orderOfVanishingAt'_of_orb_eq a hp horb

/-- The orbit order of `gForm a` at the orbit of a zero `p` is at least `1`. -/
private lemma one_le_ordOrbitFM_gForm (a : ℂ) (p : ℍ) (hp : gForm a p = 0) :
    1 ≤ ordOrbitFM (gForm a) (orbFM p) := by
  rw [ordOrbit_mkFM]; exact one_le_orderOfVanishingAt'_gForm a p hp

/-- A single non-elliptic orbit with order `≥ 1` forces the orbit sum `S ≥ 1`. -/
private lemma slot_nonEll_one (a : ℂ) (q : NonEllOrbitFM)
    (hq : 1 ≤ ordOrbitFM (gForm a) q.val) : 1 ≤ gFormOrbitSumℤ a := by
  have hsupp : Function.HasFiniteSupport
      (fun q : NonEllOrbitFM => ordOrbitFM (gForm a) q.val) :=
    (finite_support_ordOrbit_nonEllFM (gForm a) (gForm_ne_zero a)).subset fun _ h => h
  have hle := single_le_finsum q hsupp (fun j => ordOrbitFM_gForm_nonneg a j.val)
  rw [gFormOrbitSumℤ]; omega

/-- Two distinct non-elliptic orbits, each with order `≥ 1`, force the orbit sum `S ≥ 2`. -/
private lemma slot_nonEll_two (a : ℂ) (q₁ q₂ : NonEllOrbitFM) (hne : q₁ ≠ q₂)
    (h1 : 1 ≤ ordOrbitFM (gForm a) q₁.val) (h2 : 1 ≤ ordOrbitFM (gForm a) q₂.val) :
    2 ≤ gFormOrbitSumℤ a := by
  classical
  have hfin : (Function.support
      (fun q : NonEllOrbitFM => ordOrbitFM (gForm a) q.val)).Finite :=
    (finite_support_ordOrbit_nonEllFM (gForm a) (gForm_ne_zero a)).subset fun _ h => h
  have hsum : gFormOrbitSumℤ a =
      ∑ q ∈ hfin.toFinset, ordOrbitFM (gForm a) q.val := by
    rw [gFormOrbitSumℤ]; exact finsum_eq_sum _ hfin
  have hmem₁ : q₁ ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset, Function.mem_support]; omega
  have hmem₂ : q₂ ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset, Function.mem_support]; omega
  have hsub : ({q₁, q₂} : Finset NonEllOrbitFM) ⊆ hfin.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hpair := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun q : NonEllOrbitFM => ordOrbitFM (gForm a) q.val)
    (fun i _ _ => ordOrbitFM_gForm_nonneg a i.val)
  rw [Finset.sum_pair hne] at hpair
  rw [hsum]; omega

/-- The slot classification of a zero `p` of `gForm a`: either it is in the orbit of `i`
(forcing `A ≥ 1`), the orbit of `ρ` (forcing `B ≥ 1`), or a non-elliptic orbit `q` whose
order `ordOrbitFM (gForm a) q.val ≥ 1`. -/
private lemma slot_classify (a : ℂ) (p : ℍ) (hp : gForm a p = 0) :
    orbFM p = oiFM ∨ orbFM p = orhoFM ∨
    ∃ q : NonEllOrbitFM, q.val = orbFM p ∧ 1 ≤ ordOrbitFM (gForm a) q.val := by
  by_cases hi : orbFM p = oiFM
  · exact Or.inl hi
  by_cases hr : orbFM p = orhoFM
  · exact Or.inr (Or.inl hr)
  refine Or.inr (Or.inr ⟨⟨orbFM p, ⟨hi, hr⟩⟩, rfl, ?_⟩)
  exact one_le_ordOrbitFM_gForm a p hp

/-- **Key uniqueness lemma.** Two zeros of `gForm a` lie in the same `SL₂(ℤ)`-orbit.
The valence formula gives `3A + 2B + 6S = 6` with `A, B, S ≥ 0`; if the two zeros were in
distinct orbits, every case produces lower bounds making this equation infeasible. -/
private lemma unique_orbit (a : ℂ) {z w : ℍ}
    (hz : gForm a z = 0) (hw : gForm a w = 0) : orbFM z = orbFM w := by
  by_contra hne
  have hdioph := gForm_valence_diophantine a
  set A := orderOfVanishingAt' (gForm a) ellipticPointI' with hA
  set B := orderOfVanishingAt' (gForm a) ellipticPointRho' with hB
  set S := gFormOrbitSumℤ a with hS
  have hAnn : 0 ≤ A := hA ▸ orderOfVanishingAt'_gForm_nonneg a ellipticPointI'
  have hBnn : 0 ≤ B := hB ▸ orderOfVanishingAt'_gForm_nonneg a ellipticPointRho'
  have hSnn : 0 ≤ S := hS ▸ gFormOrbitSumℤ_nonneg a
  rcases slot_classify a z hz with hz' | hz' | ⟨qz, hqz_val, hqz_ord⟩
  · -- z ∼ i, so A ≥ 1
    have hzi : 1 ≤ A := hA ▸ slot_i a z hz hz'
    rcases slot_classify a w hw with hw' | hw' | ⟨qw, hqw_val, hqw_ord⟩
    · exact hne (hz'.trans hw'.symm)
    · have hwr : 1 ≤ B := hB ▸ slot_rho a w hw hw'; omega
    · have hws : 1 ≤ S := hS ▸ slot_nonEll_one a qw (hqw_val ▸ one_le_ordOrbitFM_gForm a w hw)
      omega
  · -- z ∼ ρ, so B ≥ 1
    have hzr : 1 ≤ B := hB ▸ slot_rho a z hz hz'
    rcases slot_classify a w hw with hw' | hw' | ⟨qw, hqw_val, hqw_ord⟩
    · have hwi : 1 ≤ A := hA ▸ slot_i a w hw hw'; omega
    · exact hne (hz'.trans hw'.symm)
    · have hws : 1 ≤ S := hS ▸ slot_nonEll_one a qw (hqw_val ▸ one_le_ordOrbitFM_gForm a w hw)
      omega
  · -- z generic, so the orbit qz contributes; case on w
    have hzs : 1 ≤ S := hS ▸ slot_nonEll_one a qz hqz_ord
    rcases slot_classify a w hw with hw' | hw' | ⟨qw, hqw_val, hqw_ord⟩
    · have hwi : 1 ≤ A := hA ▸ slot_i a w hw hw'; omega
    · have hwr : 1 ≤ B := hB ▸ slot_rho a w hw hw'; omega
    · -- both generic, distinct orbits ⟹ S ≥ 2
      have hqne : qz ≠ qw := by
        intro h
        exact hne (hqz_val.symm.trans (h ▸ hqw_val))
      have htwo : 2 ≤ S := hS ▸ slot_nonEll_two a qz qw hqne hqz_ord hqw_ord
      omega

/-- **If `j z = j w`, then `z` and `w` are in the same `SL₂(ℤ)`-orbit.** -/
theorem sameOrbit_of_j_eq_j (z w : ℍ) (h : j z = j w) : ∃ γ : SL(2, ℤ), γ • z = w := by
  have hz : gForm (j z) z = 0 := (j_eq_iff_gForm_zero (j z) z).mp rfl
  have hw : gForm (j z) w = 0 := (j_eq_iff_gForm_zero (j z) w).mp h.symm
  have horb : orbFM z = orbFM w := unique_orbit (j z) hz hw
  obtain ⟨γ, hγ⟩ := (Quotient.exact' horb.symm : ∃ g : SL(2, ℤ), g • z = w)
  exact ⟨γ, hγ⟩

/-- **The `j`-function is injective on the open fundamental domain `𝒟ᵒ`.** -/
theorem j_injOn_fdo : Set.InjOn j ModularGroup.fdo := by
  intro z hz w hw hjzw
  obtain ⟨γ, hγ⟩ := sameOrbit_of_j_eq_j z w hjzw
  have hw' : γ • z ∈ ModularGroup.fdo := hγ ▸ hw
  have hzeq : z = γ • z := ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo hz hw'
  rw [← hγ, ← hzeq]

end

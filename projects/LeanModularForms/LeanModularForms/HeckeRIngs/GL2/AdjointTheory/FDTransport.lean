/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.AdjointTheory
import LeanModularForms.HeckeRIngs.GL2.FourierHecke
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_Gamma1
import LeanModularForms.Modularforms.PeterssonInner
import LeanModularForms.Modularforms.PeterssonLevelN
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Semisimple

/-!
# Hecke adjoint theory: FD-transport infrastructure.

The Hecke conjugate intersection group `Γ_p(α)`, fundamental-domain transport
adapters, and their `PSL(2, ℝ)` ambient instantiations.
-/

noncomputable section

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped Pointwise MatrixGroups ModularForm

variable {k : ℤ}

namespace HeckeRing.GL2

open CuspForm

variable {N : ℕ} [NeZero N]

open CongruenceSubgroup Pointwise ConjAct in
/-- The Hecke conjugate intersection group `Γ_p(α) := conjGL Γ₁(N) α ⊓ Γ₁(N)`. -/
noncomputable def Gamma_p_α (α : GL (Fin 2) ℚ) : Subgroup SL(2, ℤ) :=
  conjGL (Gamma1 N) (α.map (Rat.castHom ℝ)) ⊓ Gamma1 N

open CongruenceSubgroup Pointwise ConjAct in
/-- `Γ_p(α)` has finite index in `SL(2, ℤ)`. -/
theorem Gamma_p_α_finiteIndex (α : GL (Fin 2) ℚ) :
    (Gamma_p_α (N := N) α).FiniteIndex := by
  have : (conjGL (Gamma1 N) (α.map (Rat.castHom ℝ))).FiniteIndex :=
    ((Gamma1_is_congruence N).conjGL α).finiteIndex
  show (conjGL (Gamma1 N) (α.map (Rat.castHom ℝ)) ⊓ Gamma1 N).FiniteIndex
  exact inferInstance

omit [NeZero N] in
open CongruenceSubgroup Pointwise ConjAct in
/-- `Γ_p(α) ≤ Γ₁(N)`. -/
lemma Gamma_p_α_le_Gamma1 (α : GL (Fin 2) ℚ) :
    Gamma_p_α (N := N) α ≤ Gamma1 N :=
  inf_le_right

omit [NeZero N] in
open CongruenceSubgroup Pointwise ConjAct in
/-- `Γ_p(α)` conjugation embedding. -/
lemma Gamma_p_α_conj_mem_Gamma1 (α : GL (Fin 2) ℚ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma_p_α (N := N) α) :
    ∃ δ ∈ Gamma1 N,
      ((mapGL ℝ δ : GL (Fin 2) ℝ)) =
        (α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) *
          (mapGL ℝ γ : GL (Fin 2) ℝ) *
          ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ))⁻¹ :=
  mem_conjGL.mp hγ.1

open CongruenceSubgroup Pointwise ConjAct in
/-- Conjugation-by-α function `Γ_p(α) → Γ₁(N)`. -/
noncomputable def Gamma_p_α_conjBy (α : GL (Fin 2) ℚ)
    (γ : Gamma_p_α (N := N) α) : Gamma1 N :=
  ⟨Classical.choose (Gamma_p_α_conj_mem_Gamma1 α γ.property),
    (Classical.choose_spec (Gamma_p_α_conj_mem_Gamma1 α γ.property)).1⟩

omit [NeZero N] in
open CongruenceSubgroup Pointwise ConjAct in
/-- Defining equality of `Gamma_p_α_conjBy`:
`mapGL ℝ (Gamma_p_α_conjBy α γ) = α · mapGL ℝ γ · α⁻¹` in `GL (Fin 2) ℝ`. -/
lemma Gamma_p_α_conjBy_spec (α : GL (Fin 2) ℚ)
    (γ : Gamma_p_α (N := N) α) :
    (mapGL ℝ ((Gamma_p_α_conjBy α γ : SL(2, ℤ))) : GL (Fin 2) ℝ) =
      (α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) *
        (mapGL ℝ ((γ : SL(2, ℤ))) : GL (Fin 2) ℝ) *
        ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ))⁻¹ :=
  (Classical.choose_spec (Gamma_p_α_conj_mem_Gamma1 α γ.property)).2

omit [NeZero N] in
open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- Slash by α is `Γ_p(α)`-invariant on Γ₁(N)-cusp forms. -/
lemma slash_α_Gamma_p_α_invariant (α : GL (Fin 2) ℚ)
    (f : ℍ → ℂ)
    (hf : ∀ δ ∈ Gamma1 N,
      f ∣[k] ((mapGL ℝ δ : GL (Fin 2) ℝ)) = f)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma_p_α (N := N) α) :
    (f ∣[k] ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ))) ∣[k]
      ((mapGL ℝ γ : GL (Fin 2) ℝ)) =
    f ∣[k] ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ)) := by
  obtain ⟨δ, hδ_mem, hδ_eq⟩ := Gamma_p_α_conj_mem_Gamma1 α hγ
  have hαγ : (α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) *
      (mapGL ℝ γ : GL (Fin 2) ℝ) =
      (mapGL ℝ δ : GL (Fin 2) ℝ) * (α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) := by
    rw [hδ_eq]
    group
  rw [← SlashAction.slash_mul, hαγ, SlashAction.slash_mul, hf δ hδ_mem]

omit [NeZero N] in
open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- Cusp-form specialization of `slash_α_Gamma_p_α_invariant`. -/
lemma slash_α_Gamma_p_α_invariant_cuspForm
    (α : GL (Fin 2) ℚ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma_p_α (N := N) α) :
    ((⇑f) ∣[k] ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ))) ∣[k]
      ((mapGL ℝ γ : GL (Fin 2) ℝ)) =
    (⇑f) ∣[k] ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ)) := by
  refine slash_α_Gamma_p_α_invariant α (⇑f) ?_ hγ
  intro δ hδ
  rw [show ((mapGL ℝ δ : GL (Fin 2) ℝ)) =
        (((δ : SL(2, ℤ)) : GL (Fin 2) ℝ)) from rfl, ← ModularForm.SL_slash]
  exact slash_Gamma1_eq f δ hδ

omit [NeZero N] in
open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- Finite-index FD decomposition for `Γ_p(α) ≤ Γ₁(N)` (generic ambient). -/
theorem Gamma_p_α_FD_finite_index_decomp
    {G_outer : Type*} [Group G_outer] [MulAction G_outer ℍ]
    [MeasurableConstSMul G_outer ℍ] [SMulInvariantMeasure G_outer ℍ μ_hyp]
    (α : GL (Fin 2) ℚ) (φ : SL(2, ℤ) →* G_outer) {D : Set ℍ}
    (hD : IsFundamentalDomain ((Gamma1 N).map φ) D μ_hyp)
    [Countable
      (((Gamma1 N).map φ) ⧸
        (((Gamma_p_α (N := N) α).map φ).subgroupOf ((Gamma1 N).map φ)))] :
    IsFundamentalDomain
      (((Gamma_p_α (N := N) α).map φ).subgroupOf ((Gamma1 N).map φ))
      (⋃ q : ((Gamma1 N).map φ) ⧸
              (((Gamma_p_α (N := N) α).map φ).subgroupOf ((Gamma1 N).map φ)),
        ((q.out : ((Gamma1 N).map φ)) : G_outer)⁻¹ • D)
      μ_hyp :=
  hD.subgroup_iUnion_out_smul _

open CongruenceSubgroup in
/-- Finite-index instance for the projective image of `Γ_p(α)` inside the
projective image of `Γ₁(N)`. -/
instance Gamma_p_α_image_PSL_R_finiteIndex_in_Gamma1_image
    (α : GL (Fin 2) ℚ) :
    (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
      ((Gamma1 N).map SL2Z_to_PSL2R)).FiniteIndex := by
  have : (Gamma_p_α (N := N) α).FiniteIndex := Gamma_p_α_finiteIndex α
  have : (Gamma_p_α (N := N) α ⊔ SL2Z_to_PSL2R.ker).FiniteIndex :=
    Subgroup.finiteIndex_of_le le_sup_left
  refine ⟨?_⟩
  show ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).relIndex
        ((Gamma1 N).map SL2Z_to_PSL2R) ≠ 0
  rw [Subgroup.relIndex_map_map]
  exact (Subgroup.instFiniteIndex_subgroupOf
    (Gamma1 N ⊔ SL2Z_to_PSL2R.ker)
    (H := Gamma_p_α (N := N) α ⊔ SL2Z_to_PSL2R.ker)).index_ne_zero

open CongruenceSubgroup in
/-- `Fintype` of the right-coset space. -/
noncomputable instance Gamma_p_α_image_PSL_R_quotient_fintype
    (α : GL (Fin 2) ℚ) :
    Fintype
      (((Gamma1 N).map SL2Z_to_PSL2R) ⧸
        (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
          ((Gamma1 N).map SL2Z_to_PSL2R))) :=
  Subgroup.fintypeQuotientOfFiniteIndex

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- Finite-index FD decomposition for `Γ_p(α) ≤ Γ₁(N)` at the `PSL(2, ℝ)`
ambient.  Canonical form; the `[Countable …]` variant is folded in via the
`Gamma_p_α_quotient_in_Gamma1_PSL_R_fintype` instance. -/
private theorem Gamma_p_α_PSL_R_FD_finite_index_decomp_auto
    (α : GL (Fin 2) ℚ) :
    IsFundamentalDomain
      (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
        ((Gamma1 N).map SL2Z_to_PSL2R))
      (⋃ q : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
              (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
                ((Gamma1 N).map SL2Z_to_PSL2R)),
        ((q.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹ •
          Gamma1_fundDomain_PSL N)
      μ_hyp :=
  Gamma_p_α_FD_finite_index_decomp α SL2Z_to_PSL2R <| by
    rw [map_SL2Z_to_PSL2R_eq_imageGamma1_PSL_R]; exact isFundamentalDomain_Gamma1_PSL_R

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- Packaged per-α `Γ_p(α)`-fundamental-domain set. -/
noncomputable def Gamma_p_α_fundDomain_PSL (α : GL (Fin 2) ℚ) : Set ℍ :=
  ⋃ q : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
          (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
            ((Gamma1 N).map SL2Z_to_PSL2R)),
    ((q.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹ •
      (Gamma1_fundDomain_PSL N : Set ℍ)

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- Generic SL outer-quotient ↔ scaled `Gamma1_fundDomain_PSL` integral bridge. -/
theorem setIntegral_Gamma1_fundDomain_PSL_eq_SL_outer_q_sum
    (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma1 N, ∀ τ : ℍ, h (γ • τ) = h τ)
    (h_int : IntegrableOn h (Gamma1_fundDomain_PSL N) μ_hyp) :
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp =
    (slToPslQuot_fiberCard N) • ∫ τ in Gamma1_fundDomain_PSL N, h τ ∂μ_hyp := by
  classical
  calc ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
          ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp
      = ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
          ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp :=
        Finset.sum_congr rfl fun q _ ↦ setIntegral_SL_tile_fd_eq_fdo h q
    _ = ∑ q' : PSL(2, ℤ) ⧸ imageGamma1_PSL N,
          (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ slToPslQuot q = q')).card •
            ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp :=
        sum_SL_tile_eq_fiberwise_PSL_tile h h_inv
    _ = (slToPslQuot_fiberCard N) • ∑ q' : PSL(2, ℤ) ⧸ imageGamma1_PSL N,
          ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun q' _ ↦ ?_
        congr 1
        convert slToPslQuot_fiberCard_eq q' using 2
        congr
    _ = (slToPslQuot_fiberCard N) • ∫ τ in Gamma1_fundDomain_PSL N, h τ ∂μ_hyp := by
        rw [← setIntegral_Gamma1_fundDomain_PSL_eq_sum h h_int]

open CongruenceSubgroup ModularGroup MeasureTheory in
/-- The image of `Γ_p(α)` in `PSL(2, ℤ) = SL(2, ℤ) / {±I}`. -/
noncomputable def image_Gamma_p_α_PSL (α : GL (Fin 2) ℚ) : Subgroup PSL(2, ℤ) :=
  (Gamma_p_α (N := N) α).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))

open CongruenceSubgroup in
/-- `image_Gamma_p_α_PSL α` has finite index in `PSL(2, ℤ)`. -/
instance image_Gamma_p_α_PSL_finiteIndex (α : GL (Fin 2) ℚ) :
    (image_Gamma_p_α_PSL (N := N) α).FiniteIndex := by
  have : (Gamma_p_α (N := N) α).FiniteIndex := Gamma_p_α_finiteIndex (N := N) α
  refine ⟨fun h ↦ ?_⟩
  have h_dvd : (image_Gamma_p_α_PSL (N := N) α).index ∣ (Gamma_p_α (N := N) α).index := by
    apply Subgroup.index_map_dvd; exact QuotientGroup.mk_surjective
  rw [h] at h_dvd
  exact Subgroup.FiniteIndex.index_ne_zero (Nat.eq_zero_of_zero_dvd h_dvd)

open CongruenceSubgroup in
/-- `Fintype` of the right-coset space `PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL α`. -/
noncomputable instance image_Gamma_p_α_PSL_quotient_fintype (α : GL (Fin 2) ℚ) :
    Fintype (PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) :=
  Subgroup.fintypeQuotientOfFiniteIndex

open CongruenceSubgroup in
/-- `Fintype` of `SL(2, ℤ) ⧸ Γ_p(α)`. -/
noncomputable instance Gamma_p_α_quotient_fintype (α : GL (Fin 2) ℚ) :
    Fintype (SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) := by
  have : (Gamma_p_α (N := N) α).FiniteIndex :=
    Gamma_p_α_finiteIndex (N := N) α
  exact Subgroup.fintypeQuotientOfFiniteIndex

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- Canonical PSL-coset fundamental domain for `image_Gamma_p_α_PSL α`. -/
noncomputable def Gamma_p_α_fundDomain_PSL_canonical (α : GL (Fin 2) ℚ) : Set ℍ :=
  ⋃ q : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α,
    ((q.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ)

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- `Gamma_p_α_fundDomain_PSL_canonical α` is a fundamental domain for
`image_Gamma_p_α_PSL α` acting on `ℍ`. -/
theorem isFundamentalDomain_Gamma_p_α_PSL_canonical (α : GL (Fin 2) ℚ) :
    MeasureTheory.IsFundamentalDomain (image_Gamma_p_α_PSL (N := N) α)
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) μ_hyp :=
  isFundamentalDomain_fdo_PSL.subgroup_iUnion_out_smul
    (image_Gamma_p_α_PSL (N := N) α)

open CongruenceSubgroup in
/-- The natural quotient map `SL ⧸ Γ_p(α) → PSL ⧸ image_Γ_p(α)_PSL`,
sending each `Γ_p(α)`-coset `[g]` to the `image_Gamma_p_α_PSL`-coset `[PSL.mk g]`. -/
noncomputable def slToPslQuot_Gamma_p_α (α : GL (Fin 2) ℚ) :
    SL(2, ℤ) ⧸ Gamma_p_α (N := N) α →
      PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α :=
  Quotient.lift
    (fun g : SL(2, ℤ) ↦ (QuotientGroup.mk (QuotientGroup.mk g : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α))
    (by
      intro a b hab
      change (QuotientGroup.leftRel _).r _ _ at hab
      rw [QuotientGroup.leftRel_apply] at hab
      apply (QuotientGroup.eq).mpr
      have h_psl : (QuotientGroup.mk a : PSL(2, ℤ))⁻¹ * QuotientGroup.mk b =
          QuotientGroup.mk (a⁻¹ * b) := by
        rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      rw [h_psl]
      exact ⟨a⁻¹ * b, hab, rfl⟩)

omit [NeZero N] in
@[simp]
theorem slToPslQuot_Gamma_p_α_mk (α : GL (Fin 2) ℚ) (g : SL(2, ℤ)) :
    slToPslQuot_Gamma_p_α (N := N) α
        (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) =
      QuotientGroup.mk (QuotientGroup.mk g : PSL(2, ℤ)) :=
  rfl

omit [NeZero N] in
theorem slToPslQuot_Gamma_p_α_surjective (α : GL (Fin 2) ℚ) :
    Function.Surjective (slToPslQuot_Gamma_p_α (N := N) α) := fun q' ↦ by
  obtain ⟨g_psl, hg_psl⟩ := QuotientGroup.mk_surjective q'
  obtain ⟨g_sl, hg_sl⟩ := QuotientGroup.mk_surjective g_psl
  exact ⟨QuotientGroup.mk g_sl, by rw [slToPslQuot_Gamma_p_α_mk, hg_sl, hg_psl]⟩

open CongruenceSubgroup in
/-- Left-multiplication action on `SL ⧸ Γ_p(α)`. -/
noncomputable def slLeftMul_Gamma_p_α (α : GL (Fin 2) ℚ) (h : SL(2, ℤ)) :
    SL(2, ℤ) ⧸ Gamma_p_α (N := N) α → SL(2, ℤ) ⧸ Gamma_p_α (N := N) α :=
  Quotient.lift (fun g : SL(2, ℤ) ↦ (QuotientGroup.mk (h * g) : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α))
    (by
      intro a b hab
      change (QuotientGroup.leftRel _).r _ _ at hab
      rw [QuotientGroup.leftRel_apply] at hab
      apply QuotientGroup.eq.mpr
      have : (h * a)⁻¹ * (h * b) = a⁻¹ * b := by group
      rwa [this])

omit [NeZero N] in
@[simp]
theorem slLeftMul_Gamma_p_α_mk (α : GL (Fin 2) ℚ) (h g : SL(2, ℤ)) :
    slLeftMul_Gamma_p_α (N := N) α h
        (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) =
      QuotientGroup.mk (h * g) :=
  rfl

omit [NeZero N] in
theorem slLeftMul_Gamma_p_α_one (α : GL (Fin 2) ℚ)
    (q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) :
    slLeftMul_Gamma_p_α (N := N) α 1 q = q := by
  induction q using QuotientGroup.induction_on with | _ g => simp

omit [NeZero N] in
theorem slLeftMul_Gamma_p_α_comp (α : GL (Fin 2) ℚ) (h₁ h₂ : SL(2, ℤ))
    (q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) :
    slLeftMul_Gamma_p_α (N := N) α h₁ (slLeftMul_Gamma_p_α (N := N) α h₂ q) =
      slLeftMul_Gamma_p_α (N := N) α (h₁ * h₂) q := by
  induction q using QuotientGroup.induction_on with | _ g => simp [mul_assoc]

omit [NeZero N] in
private lemma slToPslQuot_mk_left_transport (α : GL (Fin 2) ℚ) (a b g : SL(2, ℤ))
    (hg : slToPslQuot_Gamma_p_α (N := N) α (QuotientGroup.mk g) =
        slToPslQuot_Gamma_p_α (N := N) α (QuotientGroup.mk b)) :
    slToPslQuot_Gamma_p_α (N := N) α (QuotientGroup.mk (a * b⁻¹ * g)) =
      slToPslQuot_Gamma_p_α (N := N) α (QuotientGroup.mk a) := by
  rw [slToPslQuot_Gamma_p_α_mk, slToPslQuot_Gamma_p_α_mk] at hg ⊢
  rw [QuotientGroup.eq] at hg ⊢
  have key : ((QuotientGroup.mk (a * b⁻¹ * g) : PSL(2, ℤ)))⁻¹ * QuotientGroup.mk a =
      (QuotientGroup.mk g : PSL(2, ℤ))⁻¹ * QuotientGroup.mk b := by
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (by group)
  rwa [key]

open CongruenceSubgroup Classical in
/-- Uniform fiber size of `slToPslQuot_Gamma_p_α`. -/
theorem slToPslQuot_Gamma_p_α_fiber_card_uniform (α : GL (Fin 2) ℚ)
    (q₁' q₂' : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) :
    haveI : DecidableEq (PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) := Classical.decEq _
    (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α ↦
        slToPslQuot_Gamma_p_α (N := N) α q = q₁')).card =
      (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α ↦
        slToPslQuot_Gamma_p_α (N := N) α q = q₂')).card := by
  haveI : DecidableEq (PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) := Classical.decEq _
  obtain ⟨q₁, hq₁⟩ := slToPslQuot_Gamma_p_α_surjective (N := N) α q₁'
  obtain ⟨q₂, hq₂⟩ := slToPslQuot_Gamma_p_α_surjective (N := N) α q₂'
  induction q₁ using QuotientGroup.induction_on with | _ g₁ => ?_
  induction q₂ using QuotientGroup.induction_on with | _ g₂ => ?_
  set h := g₂ * g₁⁻¹ with hh_def
  refine Finset.card_bij'
    (fun q _ ↦ slLeftMul_Gamma_p_α (N := N) α h q)
    (fun q _ ↦ slLeftMul_Gamma_p_α (N := N) α h⁻¹ q)
    (fun q hq ↦ ?_)
    (fun q hq ↦ ?_)
    (fun q _ ↦ by
      show slLeftMul_Gamma_p_α (N := N) α h⁻¹
        (slLeftMul_Gamma_p_α (N := N) α h q) = q
      rw [slLeftMul_Gamma_p_α_comp, inv_mul_cancel, slLeftMul_Gamma_p_α_one])
    (fun q _ ↦ by
      show slLeftMul_Gamma_p_α (N := N) α h
        (slLeftMul_Gamma_p_α (N := N) α h⁻¹ q) = q
      rw [slLeftMul_Gamma_p_α_comp, mul_inv_cancel, slLeftMul_Gamma_p_α_one])
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    induction q using QuotientGroup.induction_on with | _ g => ?_
    show slToPslQuot_Gamma_p_α (N := N) α (QuotientGroup.mk (h * g)) = q₂'
    rw [hh_def, ← hq₂]
    exact slToPslQuot_mk_left_transport α g₂ g₁ g (hq.trans hq₁.symm)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    induction q using QuotientGroup.induction_on with | _ g => ?_
    show slToPslQuot_Gamma_p_α (N := N) α (QuotientGroup.mk (h⁻¹ * g)) = q₁'
    rw [hh_def, mul_inv_rev, inv_inv, ← hq₁]
    exact slToPslQuot_mk_left_transport α g₁ g₂ g (hq.trans hq₂.symm)

open CongruenceSubgroup Classical in
/-- Uniform fiber cardinality of `slToPslQuot_Gamma_p_α`, computed at the
identity coset. -/
noncomputable def slToPslQuot_fiberCard_Gamma_p_α (α : GL (Fin 2) ℚ) : ℕ :=
  haveI : DecidableEq (PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) := Classical.decEq _
  (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α ↦
    slToPslQuot_Gamma_p_α (N := N) α q =
      (QuotientGroup.mk (1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α))).card

theorem slToPslQuot_fiberCard_Gamma_p_α_eq (α : GL (Fin 2) ℚ)
    (q' : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) :
    haveI : DecidableEq (PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) := Classical.decEq _
    (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α ↦
      slToPslQuot_Gamma_p_α (N := N) α q = q')).card =
    slToPslQuot_fiberCard_Gamma_p_α (N := N) α :=
  slToPslQuot_Gamma_p_α_fiber_card_uniform (N := N) α q' _

omit [NeZero N] in
open CongruenceSubgroup UpperHalfPlane MeasureTheory in
/-- Fiber-invariance of the SL-tile integral at `H = Γ_p(α)`. -/
theorem setIntegral_SL_tile_eq_PSL_tile_Gamma_p_α (α : GL (Fin 2) ℚ)
    (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma_p_α (N := N) α, ∀ τ : ℍ, h (γ • τ) = h τ)
    (q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) :
    ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp =
      ∫ τ in ((slToPslQuot_Gamma_p_α (N := N) α q).out : PSL(2, ℤ))⁻¹ •
        (fdo : Set ℍ), h τ ∂μ_hyp := by
  have h_quot_eq :
      (QuotientGroup.mk (QuotientGroup.mk q.out : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) =
      QuotientGroup.mk ((slToPslQuot_Gamma_p_α (N := N) α q).out : PSL(2, ℤ)) := by
    have h1 : slToPslQuot_Gamma_p_α (N := N) α q =
        QuotientGroup.mk (QuotientGroup.mk q.out : PSL(2, ℤ)) := by
      conv_lhs => rw [← q.out_eq]
      rfl
    exact h1.symm.trans (slToPslQuot_Gamma_p_α (N := N) α q).out_eq.symm
  rw [QuotientGroup.eq] at h_quot_eq
  obtain ⟨γ, hγ_mem, hγ_eq⟩ := h_quot_eq
  have h_eq_PSL : ((slToPslQuot_Gamma_p_α (N := N) α q).out : PSL(2, ℤ)) =
      QuotientGroup.mk q.out * QuotientGroup.mk γ := by
    have h_mul : (QuotientGroup.mk q.out : PSL(2, ℤ)) *
        ((QuotientGroup.mk q.out : PSL(2, ℤ))⁻¹ *
          (slToPslQuot_Gamma_p_α (N := N) α q).out) =
        (slToPslQuot_Gamma_p_α (N := N) α q).out := by group
    rw [← h_mul, ← hγ_eq]
    rfl
  rw [show ((slToPslQuot_Gamma_p_α (N := N) α q).out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ) =
      ((QuotientGroup.mk γ : PSL(2, ℤ))⁻¹ •
        ((QuotientGroup.mk q.out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ))) by
      rw [h_eq_PSL, mul_inv_rev, mul_smul]]
  have h_psl_q : ((QuotientGroup.mk q.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ) =
      (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ) := by
    rw [show ((QuotientGroup.mk q.out : PSL(2, ℤ)))⁻¹ =
          (QuotientGroup.mk q.out⁻¹ : PSL(2, ℤ)) from
        (QuotientGroup.mk_inv _ _).symm]
    rfl
  have h_psl_γ : ((QuotientGroup.mk γ : PSL(2, ℤ)))⁻¹ •
        ((q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ)) =
      (γ : SL(2, ℤ))⁻¹ • ((q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ)) := by
    rw [show ((QuotientGroup.mk γ : PSL(2, ℤ)))⁻¹ =
          (QuotientGroup.mk γ⁻¹ : PSL(2, ℤ)) from
        (QuotientGroup.mk_inv _ _).symm]
    rfl
  rw [h_psl_q, h_psl_γ]
  symm
  rw [show ((γ⁻¹ : SL(2, ℤ)) • ((q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ)) : Set ℍ) =
      (fun τ ↦ (γ⁻¹ : SL(2, ℤ)) • τ) '' ((q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ)) from rfl,
    (measurePreserving_smul (γ⁻¹ : SL(2, ℤ)) μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul _)]
  congr 1
  ext τ
  exact h_inv γ⁻¹ ((Gamma_p_α (N := N) α).inv_mem hγ_mem) τ

open CongruenceSubgroup UpperHalfPlane MeasureTheory Classical in
/-- SL→PSL fiber-sum reindexing for `Γ_p(α)`-invariant integrands. -/
theorem sum_SL_tile_eq_fiberwise_PSL_tile_Gamma_p_α (α : GL (Fin 2) ℚ)
    (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma_p_α (N := N) α, ∀ τ : ℍ, h (γ • τ) = h τ) :
    ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
        ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp =
      ∑ q' : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α,
        (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α ↦
          slToPslQuot_Gamma_p_α (N := N) α q = q')).card •
            ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
  calc ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
          ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp
      = ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
          ∫ τ in ((slToPslQuot_Gamma_p_α (N := N) α q).out : PSL(2, ℤ))⁻¹ •
            (fdo : Set ℍ), h τ ∂μ_hyp :=
        Finset.sum_congr rfl fun q _ ↦ setIntegral_SL_tile_eq_PSL_tile_Gamma_p_α (N := N) α h h_inv q
    _ = ∑ q' : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α,
          ∑ q ∈ Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α ↦
            slToPslQuot_Gamma_p_α (N := N) α q = q'),
            ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp :=
        (Finset.sum_fiberwise' Finset.univ
          (slToPslQuot_Gamma_p_α (N := N) α)
          (fun q' ↦ ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp)).symm
    _ = ∑ q' : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α,
          (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α ↦
            slToPslQuot_Gamma_p_α (N := N) α q = q')).card •
              ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
        refine Finset.sum_congr rfl fun q' _ ↦ ?_
        exact Finset.sum_const _

omit [NeZero N] in
open UpperHalfPlane ModularGroup MeasureTheory in
/-- `fd` ↔ `fdo` SL-tile integral equality at `H = Γ_p(α)`. -/
theorem setIntegral_SL_tile_fd_eq_fdo_Gamma_p_α
    (α : GL (Fin 2) ℚ) (h : ℍ → ℂ)
    (q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) :
    ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp =
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
  rw [show ((q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ) : Set ℍ) =
        (fun τ ↦ (q.out : SL(2, ℤ))⁻¹ • τ) '' (fd : Set ℍ) from rfl,
    (measurePreserving_smul (q.out : SL(2, ℤ))⁻¹ μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul _),
    show ((q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ) : Set ℍ) =
        (fun τ ↦ (q.out : SL(2, ℤ))⁻¹ • τ) '' (fdo : Set ℍ) from rfl,
    (measurePreserving_smul (q.out : SL(2, ℤ))⁻¹ μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul _),
    setIntegral_fd_eq_fdo]

omit [NeZero N] in
open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- Pairwise AE-disjointness of the canonical PSL coset tiles for `Γ_p(α)`. -/
theorem aedisjoint_PSL_coset_tiles_Gamma_p_α (α : GL (Fin 2) ℚ) :
    Pairwise (fun q₁ q₂ : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α ↦
      MeasureTheory.AEDisjoint μ_hyp
        ((q₁.out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ))
        ((q₂.out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ))) := by
  intro q₁ q₂ hne
  have h_inv_ne : (q₁.out : PSL(2, ℤ))⁻¹ ≠ (q₂.out : PSL(2, ℤ))⁻¹ := by
    intro hg
    apply hne
    rw [← q₁.out_eq, ← q₂.out_eq, inv_injective hg]
  exact isFundamentalDomain_fdo_PSL.aedisjoint h_inv_ne

omit [NeZero N] in
open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- Null-measurability of the canonical PSL coset tiles for `Γ_p(α)`. -/
theorem nullMeasurableSet_PSL_coset_tile_Gamma_p_α
    (α : GL (Fin 2) ℚ)
    (q : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) :
    MeasureTheory.NullMeasurableSet
      ((q.out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ)) μ_hyp :=
  isFundamentalDomain_fdo_PSL.nullMeasurableSet_smul _

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- `Gamma_p_α_fundDomain_PSL_canonical` integral as a PSL-tile sum. -/
theorem setIntegral_Gamma_p_α_fundDomain_PSL_canonical_eq_sum
    (α : GL (Fin 2) ℚ) (h : ℍ → ℂ)
    (h_int : IntegrableOn h
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) μ_hyp) :
    ∫ τ in Gamma_p_α_fundDomain_PSL_canonical (N := N) α, h τ ∂μ_hyp =
      ∑ q : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α,
        ∫ τ in ((q.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
  rw [Gamma_p_α_fundDomain_PSL_canonical,
    integral_iUnion_ae
      (nullMeasurableSet_PSL_coset_tile_Gamma_p_α (N := N) α)
      (aedisjoint_PSL_coset_tiles_Gamma_p_α (N := N) α) h_int,
    tsum_fintype]

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- SL outer-q sum ↔ scaled `Gamma_p_α_fundDomain_PSL_canonical` integral. -/
theorem setIntegral_Gamma_p_α_fundDomain_PSL_canonical_eq_SL_outer_q_sum
    (α : GL (Fin 2) ℚ) (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma_p_α (N := N) α, ∀ τ : ℍ, h (γ • τ) = h τ)
    (h_int : IntegrableOn h
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) μ_hyp) :
    ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp =
    (slToPslQuot_fiberCard_Gamma_p_α (N := N) α) •
      ∫ τ in Gamma_p_α_fundDomain_PSL_canonical (N := N) α, h τ ∂μ_hyp := by
  classical
  calc ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
          ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp
      = ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
          ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp :=
        Finset.sum_congr rfl fun q _ ↦ setIntegral_SL_tile_fd_eq_fdo_Gamma_p_α (N := N) α h q
    _ = ∑ q' : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α,
          (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α ↦
            slToPslQuot_Gamma_p_α (N := N) α q = q')).card •
            ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp :=
        sum_SL_tile_eq_fiberwise_PSL_tile_Gamma_p_α (N := N) α h h_inv
    _ = (slToPslQuot_fiberCard_Gamma_p_α (N := N) α) •
          ∑ q' : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α,
            ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun q' _ ↦ ?_
        congr 1
        convert slToPslQuot_fiberCard_Gamma_p_α_eq (N := N) α q' using 2
        congr
    _ = (slToPslQuot_fiberCard_Gamma_p_α (N := N) α) •
          ∫ τ in Gamma_p_α_fundDomain_PSL_canonical (N := N) α, h τ ∂μ_hyp := by
        rw [← setIntegral_Gamma_p_α_fundDomain_PSL_canonical_eq_sum
          (N := N) α h h_int]

omit [NeZero N] in
open CongruenceSubgroup Pointwise in
/-- `(Γ_p(α)).map SL2Z_to_PSL2R = (image_Gamma_p_α_PSL α).map PSL2Z_to_PSL2R`. -/
theorem map_SL2Z_to_PSL2R_eq_image_Gamma_p_α_PSL_R
    (α : GL (Fin 2) ℚ) :
    (Gamma_p_α (N := N) α).map SL2Z_to_PSL2R =
      (image_Gamma_p_α_PSL (N := N) α).map PSL2Z_to_PSL2R := by
  unfold image_Gamma_p_α_PSL
  rw [Subgroup.map_map]
  rfl

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- The canonical FD is also a FD for `(Γ_p(α)).map SL2Z_to_PSL2R`. -/
theorem isFundamentalDomain_Gamma_p_α_PSL_canonical_at_PSL_R
    (α : GL (Fin 2) ℚ) :
    IsFundamentalDomain ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R)
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) μ_hyp := by
  rw [map_SL2Z_to_PSL2R_eq_image_Gamma_p_α_PSL_R]
  have h_image_eq : (Equiv.refl ℍ) '' (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) =
      Gamma_p_α_fundDomain_PSL_canonical (N := N) α := by
    simp
  rw [← h_image_eq]
  refine (isFundamentalDomain_Gamma_p_α_PSL_canonical (N := N) α).image_of_equiv (Equiv.refl ℍ)
    (MeasureTheory.Measure.QuasiMeasurePreserving.id μ_hyp)
    ((Subgroup.equivMapOfInjective (image_Gamma_p_α_PSL (N := N) α)
      PSL2Z_to_PSL2R PSL2Z_to_PSL2R_injective).toEquiv.symm) ?_
  intro g τ
  show (Equiv.refl ℍ) (((Subgroup.equivMapOfInjective
        (image_Gamma_p_α_PSL (N := N) α) PSL2Z_to_PSL2R
        PSL2Z_to_PSL2R_injective).toEquiv.symm g :
        image_Gamma_p_α_PSL (N := N) α) • τ) =
      ((g : (image_Gamma_p_α_PSL (N := N) α).map PSL2Z_to_PSL2R) :
        PSL(2, ℝ)) • (Equiv.refl ℍ) τ
  simp only [Equiv.refl_apply]
  set g' : image_Gamma_p_α_PSL (N := N) α :=
    (Subgroup.equivMapOfInjective (image_Gamma_p_α_PSL (N := N) α)
      PSL2Z_to_PSL2R PSL2Z_to_PSL2R_injective).toEquiv.symm g
  have h_g_coe :
      ((g : (image_Gamma_p_α_PSL (N := N) α).map PSL2Z_to_PSL2R) : PSL(2, ℝ)) =
        PSL2Z_to_PSL2R (g' : PSL(2, ℤ)) := by
    rw [← Subgroup.coe_equivMapOfInjective_apply (f := PSL2Z_to_PSL2R)
      (hf := PSL2Z_to_PSL2R_injective)]
    congr 1
    exact ((Subgroup.equivMapOfInjective (image_Gamma_p_α_PSL (N := N) α)
      PSL2Z_to_PSL2R PSL2Z_to_PSL2R_injective).toEquiv.apply_symm_apply g).symm
  rw [h_g_coe, PSL2Z_to_PSL2R_smul_eq]
  rfl

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- `Gamma_p_α_fundDomain_PSL` is also a FD for `(Γ_p(α)).map SL2Z_to_PSL2R`. -/
theorem isFundamentalDomain_Gamma_p_α_fundDomain_PSL_at_PSL_R
    (α : GL (Fin 2) ℚ) :
    IsFundamentalDomain ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R)
      (Gamma_p_α_fundDomain_PSL (N := N) α) μ_hyp := by
  have h_image := (Gamma_p_α_PSL_R_FD_finite_index_decomp_auto (N := N) α).image_of_equiv
    (Equiv.refl ℍ) (MeasureTheory.Measure.QuasiMeasurePreserving.id _)
    ((Subgroup.subgroupOfEquivOfLe (Subgroup.map_mono (Gamma_p_α_le_Gamma1 α))).symm.toEquiv)
    (fun _ _ ↦ rfl)
  rw [Gamma_p_α_fundDomain_PSL]
  simpa using h_image

omit [NeZero N] in
open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- `Γ_p(α)`-invariance lifts to `(Γ_p(α)).map SL2Z_to_PSL2R`-invariance. -/
theorem inv_under_Gamma_p_α_PSL_R_of_inv_under_Gamma_p_α
    (α : GL (Fin 2) ℚ) {h : ℍ → ℂ}
    (h_inv : ∀ γ ∈ Gamma_p_α (N := N) α, ∀ τ : ℍ, h (γ • τ) = h τ)
    (g : ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R)) (τ : ℍ) :
    h (g • τ) = h τ := by
  obtain ⟨γ, hγ_mem, hγ_eq⟩ := g.property
  have h_smul : (g : PSL(2, ℝ)) • τ = γ • τ := by
    rw [← hγ_eq, SL2Z_to_PSL2R_smul]; rfl
  change h ((g : PSL(2, ℝ)) • τ) = h τ
  rw [h_smul]
  exact h_inv γ hγ_mem τ

open CongruenceSubgroup Pointwise in
/-- Countability of the `PSL(2, ℝ)`-side image of `Γ_p(α)`. -/
instance Gamma_p_α_PSL_R_countable
    (α : GL (Fin 2) ℚ) :
    Countable ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R) := by
  classical
  let F : Gamma_p_α (N := N) α → ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R) :=
    fun γ ↦ ⟨SL2Z_to_PSL2R (γ : SL(2, ℤ)), ⟨(γ : SL(2, ℤ)), γ.property, rfl⟩⟩
  exact Function.Surjective.countable (f := F) fun g ↦ by
    rcases g.property with ⟨γ, hγ, hγ_eq⟩
    exact ⟨⟨γ, hγ⟩, Subtype.ext hγ_eq⟩

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- Integral equality between `Gamma_p_α_fundDomain_PSL` and the canonical FD
for `Γ_p(α)`-invariant integrands. -/
theorem setIntegral_Gamma_p_α_fundDomain_PSL_eq_canonical
    (α : GL (Fin 2) ℚ) (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma_p_α (N := N) α, ∀ τ : ℍ, h (γ • τ) = h τ) :
    ∫ τ in Gamma_p_α_fundDomain_PSL (N := N) α, h τ ∂μ_hyp =
      ∫ τ in Gamma_p_α_fundDomain_PSL_canonical (N := N) α, h τ ∂μ_hyp :=
  (isFundamentalDomain_Gamma_p_α_fundDomain_PSL_at_PSL_R (N := N) α).setIntegral_eq
    (isFundamentalDomain_Gamma_p_α_PSL_canonical_at_PSL_R (N := N) α)
    (fun g τ ↦ inv_under_Gamma_p_α_PSL_R_of_inv_under_Gamma_p_α (N := N) α h_inv g τ)

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- The `Γ_p(α)` outer-SL bridge for `Gamma_p_α_fundDomain_PSL`. -/
theorem setIntegral_Gamma_p_α_fundDomain_PSL_eq_SL_outer_q_sum
    (α : GL (Fin 2) ℚ) (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma_p_α (N := N) α, ∀ τ : ℍ, h (γ • τ) = h τ)
    (h_int : IntegrableOn h
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) μ_hyp) :
    ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (ModularGroup.fd : Set ℍ), h τ ∂μ_hyp =
    (slToPslQuot_fiberCard_Gamma_p_α (N := N) α) •
      ∫ τ in Gamma_p_α_fundDomain_PSL (N := N) α, h τ ∂μ_hyp := by
  rw [setIntegral_Gamma_p_α_fundDomain_PSL_eq_canonical (N := N) α h h_inv]
  exact setIntegral_Gamma_p_α_fundDomain_PSL_canonical_eq_SL_outer_q_sum (N := N) α h h_inv h_int

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- `Gamma_p_α_fundDomain_PSL_canonical α` has finite measure. -/
theorem hyperbolicMeasure_Gamma_p_α_fundDomain_PSL_canonical_lt_top
    (α : GL (Fin 2) ℚ) :
    μ_hyp (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) < ⊤ := by
  rw [Gamma_p_α_fundDomain_PSL_canonical]
  refine lt_of_le_of_lt (measure_iUnion_le _) ?_
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.mpr fun q' _ ↦ ?_
  rw [(isFundamentalDomain_fdo_PSL.smul _).measure_eq isFundamentalDomain_fdo_PSL]
  exact lt_of_le_of_lt (measure_mono ModularGroup.fdo_subset_fd)
    hyperbolicMeasure_fd_lt_top

open CongruenceSubgroup in
/-- The natural quotient map `SL ⧸ Γ_p(α) → SL ⧸ Γ₁(N)`, sending each
`Γ_p(α)`-coset `[g]` to its `Γ₁(N)`-coset `[g]`. -/
noncomputable def slGamma_p_αToGamma1 (α : GL (Fin 2) ℚ) :
    SL(2, ℤ) ⧸ Gamma_p_α (N := N) α →
      SL(2, ℤ) ⧸ Gamma1 N :=
  Quotient.lift
    (fun g : SL(2, ℤ) ↦ (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma1 N))
    (by
      intro a b hab
      change (QuotientGroup.leftRel _).r _ _ at hab
      rw [QuotientGroup.leftRel_apply] at hab
      exact QuotientGroup.eq.mpr (Gamma_p_α_le_Gamma1 α hab))

omit [NeZero N] in
@[simp]
theorem slGamma_p_αToGamma1_mk (α : GL (Fin 2) ℚ) (g : SL(2, ℤ)) :
    slGamma_p_αToGamma1 (N := N) α
        (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) =
      QuotientGroup.mk g := rfl

omit [NeZero N] in
theorem slGamma_p_αToGamma1_surjective (α : GL (Fin 2) ℚ) :
    Function.Surjective (slGamma_p_αToGamma1 (N := N) α) := fun q' ↦ by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective q'
  exact ⟨QuotientGroup.mk g, by rw [slGamma_p_αToGamma1_mk, hg]⟩

open CongruenceSubgroup Classical in
/-- Uniform fiber cardinality of `slGamma_p_αToGamma1`. -/
theorem slGamma_p_αToGamma1_fiber_card_uniform (α : GL (Fin 2) ℚ)
    (q₁' q₂' : SL(2, ℤ) ⧸ Gamma1 N) :
    haveI : DecidableEq (SL(2, ℤ) ⧸ Gamma1 N) := Classical.decEq _
    (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α ↦
        slGamma_p_αToGamma1 (N := N) α q = q₁')).card =
      (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α ↦
        slGamma_p_αToGamma1 (N := N) α q = q₂')).card := by
  haveI : DecidableEq (SL(2, ℤ) ⧸ Gamma1 N) := Classical.decEq _
  obtain ⟨q₁, hq₁⟩ := slGamma_p_αToGamma1_surjective (N := N) α q₁'
  obtain ⟨q₂, hq₂⟩ := slGamma_p_αToGamma1_surjective (N := N) α q₂'
  induction q₁ using QuotientGroup.induction_on with | _ g₁ => ?_
  induction q₂ using QuotientGroup.induction_on with | _ g₂ => ?_
  set h := g₂ * g₁⁻¹ with hh_def
  refine Finset.card_bij'
    (fun q _ ↦ slLeftMul_Gamma_p_α (N := N) α h q)
    (fun q _ ↦ slLeftMul_Gamma_p_α (N := N) α h⁻¹ q)
    (fun q hq ↦ ?_) (fun q hq ↦ ?_)
    (fun q _ ↦ by
      show slLeftMul_Gamma_p_α (N := N) α h⁻¹
        (slLeftMul_Gamma_p_α (N := N) α h q) = q
      rw [slLeftMul_Gamma_p_α_comp, inv_mul_cancel, slLeftMul_Gamma_p_α_one])
    (fun q _ ↦ by
      show slLeftMul_Gamma_p_α (N := N) α h
        (slLeftMul_Gamma_p_α (N := N) α h⁻¹ q) = q
      rw [slLeftMul_Gamma_p_α_comp, mul_inv_cancel, slLeftMul_Gamma_p_α_one])
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    induction q using QuotientGroup.induction_on with | _ g => ?_
    show slGamma_p_αToGamma1 (N := N) α (QuotientGroup.mk (h * g)) = q₂'
    rw [slGamma_p_αToGamma1_mk]
    have h_g₂ : (QuotientGroup.mk g₂ : SL(2, ℤ) ⧸ Gamma1 N) = q₂' := hq₂
    have h_g : (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma1 N) = q₁' := hq
    have h_g₁ : (QuotientGroup.mk g₁ : SL(2, ℤ) ⧸ Gamma1 N) = q₁' := hq₁
    rw [← h_g₂, hh_def, QuotientGroup.eq]
    have hq_eq : (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma1 N) = QuotientGroup.mk g₁ :=
      h_g.trans h_g₁.symm
    rw [QuotientGroup.eq] at hq_eq
    have : (g₂ * g₁⁻¹ * g)⁻¹ * g₂ = g⁻¹ * g₁ := by group
    rwa [this]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    induction q using QuotientGroup.induction_on with | _ g => ?_
    show slGamma_p_αToGamma1 (N := N) α (QuotientGroup.mk (h⁻¹ * g)) = q₁'
    rw [slGamma_p_αToGamma1_mk]
    have h_g₁ : (QuotientGroup.mk g₁ : SL(2, ℤ) ⧸ Gamma1 N) = q₁' := hq₁
    have h_g : (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma1 N) = q₂' := hq
    have h_g₂ : (QuotientGroup.mk g₂ : SL(2, ℤ) ⧸ Gamma1 N) = q₂' := hq₂
    rw [← h_g₁, hh_def, QuotientGroup.eq]
    have hq_eq : (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma1 N) = QuotientGroup.mk g₂ :=
      h_g.trans h_g₂.symm
    rw [QuotientGroup.eq] at hq_eq
    have : ((g₂ * g₁⁻¹)⁻¹ * g)⁻¹ * g₁ = g⁻¹ * g₂ := by group
    rwa [this]

open CongruenceSubgroup Classical in
/-- Uniform fiber cardinality of `slGamma_p_αToGamma1`, computed at the identity. -/
noncomputable def slGamma_p_αToGamma1_fiberCard (α : GL (Fin 2) ℚ) : ℕ :=
  haveI : DecidableEq (SL(2, ℤ) ⧸ Gamma1 N) := Classical.decEq _
  (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α ↦
    slGamma_p_αToGamma1 (N := N) α q =
      (QuotientGroup.mk (1 : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma1 N))).card

theorem slGamma_p_αToGamma1_fiberCard_eq (α : GL (Fin 2) ℚ)
    (q' : SL(2, ℤ) ⧸ Gamma1 N) :
    haveI : DecidableEq (SL(2, ℤ) ⧸ Gamma1 N) := Classical.decEq _
    (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α ↦
      slGamma_p_αToGamma1 (N := N) α q = q')).card =
    slGamma_p_αToGamma1_fiberCard (N := N) α :=
  slGamma_p_αToGamma1_fiber_card_uniform (N := N) α q' _

omit [NeZero N] in
open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory in
/-- **Per-tile slash-reindex (DS 5.4.4 leaf).** A single `SL/Γ_p(α)`-coset tile
integral `∫_{q.out⁻¹•fd} petersson k F G` is reindexed onto its image
`SL/Γ₁(N)`-coset tile `∫_{q'.out⁻¹•fd}` (`q' = slGamma_p_αToGamma1 α q`), at the cost
of slashing the *linear* argument `G` by the connecting element
`δ = q.out⁻¹ · q'.out ∈ Γ₁(N)`. The `Γ₁(N)`-invariance hypothesis `hF` on the
conjugate argument `F` (`F ∣[k] γ = F` for `γ ∈ Γ₁(N)`) absorbs the slash on `F`.
This is the geometric heart of the trace mechanism: distinct fiber members of a fixed
`Γ₁`-coset contribute distinct `G`-slashes over the *same* `Γ₁`-tile, so summing the
fiber reassembles the trace `tr G` on that tile. -/
theorem setIntegral_SL_tile_petersson_Gamma_p_α_slash_reindex_Gamma1
    (α : GL (Fin 2) ℚ) (F G : ℍ → ℂ)
    (hF : ∀ γ ∈ Gamma1 N, F ∣[k] γ = F)
    (q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) :
    ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), petersson k F G τ ∂μ_hyp =
      ∫ τ in ((slGamma_p_αToGamma1 (N := N) α q).out : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
        petersson k F (G ∣[k] ((q.out : SL(2, ℤ))⁻¹ *
          (slGamma_p_αToGamma1 (N := N) α q).out)) τ ∂μ_hyp := by
  set q' := slGamma_p_αToGamma1 (N := N) α q with hq'_def
  have h_quot_eq : (QuotientGroup.mk q.out : SL(2, ℤ) ⧸ Gamma1 N) =
      QuotientGroup.mk (q'.out : SL(2, ℤ)) := by
    have h1 : q' = QuotientGroup.mk q.out := by
      rw [hq'_def]
      conv_lhs => rw [← q.out_eq]
      rfl
    exact h1.symm.trans q'.out_eq.symm
  rw [QuotientGroup.eq] at h_quot_eq
  set γ := (q.out : SL(2, ℤ))⁻¹ * (q'.out : SL(2, ℤ)) with hγ
  have h_smul_eq : (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ) =
      (γ : SL(2, ℤ)) • ((q'.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ)) := by
    rw [hγ, ← mul_smul, mul_assoc, mul_inv_cancel, mul_one]
  rw [h_smul_eq, show ((γ : SL(2, ℤ)) • ((q'.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ)) : Set ℍ) =
      (fun τ ↦ (γ : SL(2, ℤ)) • τ) '' ((q'.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ)) from rfl,
    (measurePreserving_smul (γ : SL(2, ℤ)) μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul _)]
  refine setIntegral_congr_fun ?_ fun τ _ ↦ ?_
  · refine MeasurableSet.const_smul ?_ _
    exact ((isClosed_le continuous_const
        (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)).inter
      (isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re)
        continuous_const)).measurableSet
  rw [show petersson k F G ((γ : SL(2, ℤ)) • τ) =
      petersson k (F ∣[k] γ) (G ∣[k] γ) τ from (petersson_slash_SL k F G γ τ).symm,
    hF γ h_quot_eq]

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory Classical in
/-- **The local trace operator `tr_{q'} G` (DS 5.4.4).** For a fixed `Γ₁(N)`-coset
`q'`, the partial trace of `G` along the fiber of `slGamma_p_αToGamma1 α` over `q'`:
`tr_{q'} G = ∑_{q : slGamma_p_αToGamma1 α q = q'} G ∣[k] (q.out⁻¹ · q'.out)`. Summing
`G` over the `Γ₁(N)/Γ_p(α)` cosets lying above `q'` is the DS trace `tr g = Σᵢ g[αᵢ]`
restricted to the `q'`-tile. -/
noncomputable def traceSlash_Gamma_p_α (α : GL (Fin 2) ℚ) (G : ℍ → ℂ)
    (q' : SL(2, ℤ) ⧸ Gamma1 N) : ℍ → ℂ :=
  ∑ q ∈ Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α ↦
      slGamma_p_αToGamma1 (N := N) α q = q'),
    G ∣[k] ((q.out : SL(2, ℤ))⁻¹ * q'.out)

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory Classical in
/-- **Fiberwise integrability of the trace-shifted Petersson pairing.** For each
`Γ₁`-coset `q'` and each `Γ_p(α)`-coset `q` lying above it (via `slGamma_p_αToGamma1 α`),
the function `petersson k F (G ∣[k] (q.out⁻¹·q'.out))` is integrable on the `q'`-tile
`(q'.out)⁻¹ • fd`. This is the "fiberwise traced integrability" hypothesis used by the
trace-transfer engines. -/
def TraceFiberIntegrable (α : GL (Fin 2) ℚ) (F G : ℍ → ℂ) : Prop :=
  ∀ q' : SL(2, ℤ) ⧸ Gamma1 N,
    ∀ q ∈ Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α ↦
      slGamma_p_αToGamma1 (N := N) α q = q'),
    IntegrableOn (fun τ ↦ petersson k F
      (G ∣[k] ((q.out : SL(2, ℤ))⁻¹ * q'.out)) τ)
      ((q'.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ)) μ_hyp

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory Classical in
/-- **DS Exercise 5.4.4 (outer-`SL`-coset trace/transfer).** The full `SL/Γ_p(α)`-tile
sum of `petersson k F G` (`F` `Γ₁(N)`-invariant in the slash sense, `G` arbitrary)
reassembles, fiber by fiber over `slGamma_p_αToGamma1 α`, into the `SL/Γ₁(N)`-tile sum
of `petersson k F (tr_{q'} G)`, where `tr_{q'} G` is the partial trace
`traceSlash_Gamma_p_α α G q'`. This is the level-`Γ_p(α)` ↔ level-`Γ₁(N)` reassembly
that DS uses to glue the per-representative exchange into the global adjoint. -/
theorem sum_SL_tile_petersson_Gamma_p_α_eq_sum_SL_tile_traceSlash_Gamma1
    (α : GL (Fin 2) ℚ) (F G : ℍ → ℂ)
    (hF : ∀ γ ∈ Gamma1 N, F ∣[k] γ = F)
    (h_int : TraceFiberIntegrable (N := N) (k := k) α F G) :
    ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), petersson k F G τ ∂μ_hyp =
    ∑ q' : SL(2, ℤ) ⧸ Gamma1 N,
      ∫ τ in (q'.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
        petersson k F (traceSlash_Gamma_p_α (N := N) (k := k) α G q') τ ∂μ_hyp := by
  calc ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
        ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), petersson k F G τ ∂μ_hyp
      = ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
          ∫ τ in ((slGamma_p_αToGamma1 (N := N) α q).out : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
            petersson k F (G ∣[k] ((q.out : SL(2, ℤ))⁻¹ *
              (slGamma_p_αToGamma1 (N := N) α q).out)) τ ∂μ_hyp :=
        Finset.sum_congr rfl fun q _ ↦
          setIntegral_SL_tile_petersson_Gamma_p_α_slash_reindex_Gamma1
            (N := N) α F G hF q
    _ = ∑ q' : SL(2, ℤ) ⧸ Gamma1 N,
          ∑ q ∈ Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α ↦
            slGamma_p_αToGamma1 (N := N) α q = q'),
            ∫ τ in (q'.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
              petersson k F (G ∣[k] ((q.out : SL(2, ℤ))⁻¹ * q'.out)) τ ∂μ_hyp := by
        rw [← Finset.sum_fiberwise Finset.univ (slGamma_p_αToGamma1 (N := N) α)
          (fun q ↦ ∫ τ in ((slGamma_p_αToGamma1 (N := N) α q).out : SL(2, ℤ))⁻¹ •
            (fd : Set ℍ),
            petersson k F (G ∣[k] ((q.out : SL(2, ℤ))⁻¹ *
              (slGamma_p_αToGamma1 (N := N) α q).out)) τ ∂μ_hyp)]
        refine Finset.sum_congr rfl fun q' _ ↦ Finset.sum_congr rfl fun q hq ↦ ?_
        rw [(Finset.mem_filter.mp hq).2]
    _ = ∑ q' : SL(2, ℤ) ⧸ Gamma1 N,
          ∫ τ in (q'.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
            petersson k F (traceSlash_Gamma_p_α (N := N) (k := k) α G q') τ ∂μ_hyp := by
        refine Finset.sum_congr rfl fun q' _ ↦ ?_
        rw [traceSlash_Gamma_p_α]
        rw [show (fun τ ↦ petersson k F
              (∑ q ∈ Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α ↦
                slGamma_p_αToGamma1 (N := N) α q = q'),
                G ∣[k] ((q.out : SL(2, ℤ))⁻¹ * q'.out)) τ) =
            fun τ ↦ ∑ q ∈ Finset.univ.filter
              (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α ↦
                slGamma_p_αToGamma1 (N := N) α q = q'),
                petersson k F (G ∣[k] ((q.out : SL(2, ℤ))⁻¹ * q'.out)) τ from by
          funext τ
          simp only [petersson, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]]
        rw [integral_finsetSum _ (h_int q')]

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory Classical in
/-- **DS Exercise 5.4.4 (fundamental-domain transfer form).** The `Γ_p(α)`-fundamental
domain Petersson integral of `petersson k F G` (`F` `Γ₁(N)`-invariant in the slash
sense, `G` `Γ_p(α)`-invariant under the `SL(2,ℤ)`-action and integrable on the
canonical FD) transfers — up to the uniform `SL → PSL` fiber count
`c_p = slToPslQuot_fiberCard_Gamma_p_α α` — into the `SL/Γ₁(N)`-tile sum of the
*traced* integrand `petersson k F (tr_{q'} G)`:
```
c_p • ∫_{Γ_p(α)-FD} petersson k F G
  = ∑_{q' : SL/Γ₁} ∫_{q'.out⁻¹•fd} petersson k F (traceSlash_Gamma_p_α α G q').
```
This is the reusable level-`Γ_p(α)` → level-`Γ₁(N)` reassembly: the LHS is the
substrate outer-`SL` bridge (`setIntegral_Gamma_p_α_fundDomain_PSL_eq_SL_outer_q_sum`),
the RHS the fiberwise trace identity
(`sum_SL_tile_petersson_Gamma_p_α_eq_sum_SL_tile_traceSlash_Gamma1`). The `c_p` factor
is exactly the multiplicity that converts the `Γ_p(α)`-FD integral into the full
`SL/Γ_p(α)`-coset tile sum; on the `Γ₁`-side it is reabsorbed by the analogous Γ₁
substrate when the trace target is a genuine `Γ₁`-form (see the composition note). -/
theorem setIntegral_Gamma_p_α_fundDomain_PSL_petersson_eq_traceSlash_SL_outer_q_sum
    (α : GL (Fin 2) ℚ) (F G : ℍ → ℂ)
    (hF_slash : ∀ γ ∈ Gamma1 N, F ∣[k] γ = F)
    (hG_slash : ∀ γ ∈ Gamma_p_α (N := N) α, G ∣[k] γ = G)
    (h_int : IntegrableOn (fun τ ↦ petersson k F G τ)
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) μ_hyp)
    (h_int_trace : TraceFiberIntegrable (N := N) (k := k) α F G) :
    (slToPslQuot_fiberCard_Gamma_p_α (N := N) α) •
        ∫ τ in Gamma_p_α_fundDomain_PSL (N := N) α, petersson k F G τ ∂μ_hyp =
      ∑ q' : SL(2, ℤ) ⧸ Gamma1 N,
        ∫ τ in (q'.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
          petersson k F (traceSlash_Gamma_p_α (N := N) (k := k) α G q') τ ∂μ_hyp := by
  rw [← setIntegral_Gamma_p_α_fundDomain_PSL_eq_SL_outer_q_sum (N := N) α
      (petersson k F G)
      (fun γ hγ τ ↦ by
        rw [← petersson_slash_SL,
          show F ∣[k] (γ : SL(2, ℤ)) = F from hF_slash γ ((Gamma_p_α_le_Gamma1 α) hγ),
          show G ∣[k] (γ : SL(2, ℤ)) = G from hG_slash γ hγ])
      h_int]
  exact sum_SL_tile_petersson_Gamma_p_α_eq_sum_SL_tile_traceSlash_Gamma1
    (N := N) α F G hF_slash h_int_trace

omit [NeZero N] in
open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory Classical in
/-- Fiber-transport for `slLeftMul_Gamma_p_α`: left-multiplication by
`q₂'.out · q₁'.out⁻¹` carries the `slGamma_p_αToGamma1`-fiber over `q₁'` into the
fiber over `q₂'`. Used in `traceSlash_Gamma_p_α_indep` and
`traceSlash_Gamma_p_α_slash_Gamma1` to reindex the inner trace sum across base cosets. -/
private lemma slGamma_p_αToGamma1_slLeftMul_fiber
    (α : GL (Fin 2) ℚ) (q₁' q₂' : SL(2, ℤ) ⧸ Gamma1 N)
    {q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α}
    (hq : slGamma_p_αToGamma1 (N := N) α q = q₁') :
    slGamma_p_αToGamma1 (N := N) α
        (slLeftMul_Gamma_p_α (N := N) α
          ((q₂'.out : SL(2, ℤ)) * (q₁'.out : SL(2, ℤ))⁻¹) q) = q₂' := by
  set h := (q₂'.out : SL(2, ℤ)) * (q₁'.out : SL(2, ℤ))⁻¹ with hh_def
  induction q using QuotientGroup.induction_on with | _ g => ?_
  show slGamma_p_αToGamma1 (N := N) α (QuotientGroup.mk (h * g)) = q₂'
  rw [slGamma_p_αToGamma1_mk]
  have h_g : (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma1 N) = q₁' := by
    rwa [← slGamma_p_αToGamma1_mk (N := N) α g]
  have h_gm : g⁻¹ * q₁'.out ∈ Gamma1 N :=
    QuotientGroup.eq.mp (h_g.trans q₁'.out_eq.symm)
  rw [← q₂'.out_eq, hh_def, QuotientGroup.eq]
  have hrw :
      ((q₂'.out : SL(2, ℤ)) * (q₁'.out : SL(2, ℤ))⁻¹ * g)⁻¹ * q₂'.out =
        g⁻¹ * q₁'.out := by group
  rwa [hrw]

omit [NeZero N] in
open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory Classical in
/-- Summand equality used by `traceSlash_Gamma_p_α_indep`: shifting `q` by
`h = q₂'.out · q₁'.out⁻¹` differs from the connector by a left `Γ_p(α)`-factor that
`G` absorbs via `hG_slash`. -/
private lemma traceSlash_Gamma_p_α_indep_summand
    (α : GL (Fin 2) ℚ) (G : ℍ → ℂ)
    (hG_slash : ∀ γ ∈ Gamma_p_α (N := N) α, G ∣[k] γ = G)
    (q₁' q₂' : SL(2, ℤ) ⧸ Gamma1 N)
    (q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) :
    G ∣[k] ((q.out : SL(2, ℤ))⁻¹ * q₁'.out) =
      G ∣[k] ((slLeftMul_Gamma_p_α (N := N) α
        ((q₂'.out : SL(2, ℤ)) * (q₁'.out : SL(2, ℤ))⁻¹) q).out⁻¹ * q₂'.out) := by
  set h := (q₂'.out : SL(2, ℤ)) * (q₁'.out : SL(2, ℤ))⁻¹ with hh_def
  set qt := slLeftMul_Gamma_p_α (N := N) α h q with hqt_def
  have hqt_mk : qt = QuotientGroup.mk (h * q.out) := by
    rw [hqt_def]
    conv_lhs => rw [← q.out_eq]
    rfl
  have hγp : qt.out⁻¹ * (h * q.out) ∈ Gamma_p_α (N := N) α :=
    QuotientGroup.eq.mp (qt.out_eq.trans hqt_mk)
  set γp := qt.out⁻¹ * (h * q.out) with hγp_def
  have h_rewrite : (qt.out : SL(2, ℤ))⁻¹ * q₂'.out =
      γp * ((q.out : SL(2, ℤ))⁻¹ * q₁'.out) := by
    rw [hγp_def, hh_def]; group
  rw [h_rewrite]
  conv_rhs => rw [SlashAction.slash_mul, hG_slash γp hγp]

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory Classical in
/-- **Well-definedness of the DS trace (DS 5.4.4: `tr g ∈ S_k(Γ)`).** When `G` is
`Γ_p(α)`-slash-invariant, the partial trace `traceSlash_Gamma_p_α α G q'` is
*independent of the base coset `q'`*: it is the genuine global trace `tr G`. The proof
re-bases the fiber of `q₂'` onto the fiber of `q₁'` via the uniform left-multiplication
bijection `slLeftMul_Gamma_p_α`, under which each connecting element changes only by a
right `Γ_p(α)`-factor, which `G` absorbs. -/
theorem traceSlash_Gamma_p_α_indep
    (α : GL (Fin 2) ℚ) (G : ℍ → ℂ)
    (hG_slash : ∀ γ ∈ Gamma_p_α (N := N) α, G ∣[k] γ = G)
    (q₁' q₂' : SL(2, ℤ) ⧸ Gamma1 N) :
    traceSlash_Gamma_p_α (N := N) (k := k) α G q₁' =
      traceSlash_Gamma_p_α (N := N) (k := k) α G q₂' := by
  rw [traceSlash_Gamma_p_α, traceSlash_Gamma_p_α]
  set h := (q₂'.out : SL(2, ℤ)) * (q₁'.out : SL(2, ℤ))⁻¹ with hh_def
  refine Finset.sum_bij'
    (fun q _ ↦ slLeftMul_Gamma_p_α (N := N) α h q)
    (fun q _ ↦ slLeftMul_Gamma_p_α (N := N) α h⁻¹ q)
    (fun q hq ↦ ?_) (fun q hq ↦ ?_)
    (fun q _ ↦ by
      show slLeftMul_Gamma_p_α (N := N) α h⁻¹
        (slLeftMul_Gamma_p_α (N := N) α h q) = q
      rw [slLeftMul_Gamma_p_α_comp, inv_mul_cancel, slLeftMul_Gamma_p_α_one])
    (fun q _ ↦ by
      show slLeftMul_Gamma_p_α (N := N) α h
        (slLeftMul_Gamma_p_α (N := N) α h⁻¹ q) = q
      rw [slLeftMul_Gamma_p_α_comp, mul_inv_cancel, slLeftMul_Gamma_p_α_one])
    (fun q _ ↦ traceSlash_Gamma_p_α_indep_summand α G hG_slash q₁' q₂' q)
  · -- forward fiber transport: q ∈ fiber(q₁') ⇒ slLeftMul h q ∈ fiber(q₂')
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact slGamma_p_αToGamma1_slLeftMul_fiber α q₁' q₂' hq
  · -- backward fiber transport: q ∈ fiber(q₂') ⇒ slLeftMul h⁻¹ q ∈ fiber(q₁')
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rw [show (h⁻¹ : SL(2, ℤ)) = (q₁'.out : SL(2, ℤ)) * (q₂'.out : SL(2, ℤ))⁻¹ by
      rw [hh_def, mul_inv_rev, inv_inv]]
    exact slGamma_p_αToGamma1_slLeftMul_fiber α q₂' q₁' hq

omit [NeZero N] in
open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory Classical in
/-- Self-fiber stability under `slLeftMul_Gamma_p_α` by a `q'`-conjugate of a `Γ₁(N)`
element: the fiber of `slGamma_p_αToGamma1 α` over `q'` is closed under left
multiplication by `q'.out · δ · q'.out⁻¹` for any `δ ∈ Γ₁(N)`. Used in
`traceSlash_Gamma_p_α_slash_Gamma1` to reindex the inner trace by the two conjugates
`q'.out · γ · q'.out⁻¹` and `q'.out · γ⁻¹ · q'.out⁻¹`. -/
private lemma slGamma_p_αToGamma1_slLeftMul_conj_self
    (α : GL (Fin 2) ℚ) (q' : SL(2, ℤ) ⧸ Gamma1 N)
    {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma1 N)
    {q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α}
    (hq : slGamma_p_αToGamma1 (N := N) α q = q') :
    slGamma_p_αToGamma1 (N := N) α
        (slLeftMul_Gamma_p_α (N := N) α
          ((q'.out : SL(2, ℤ)) * δ * (q'.out : SL(2, ℤ))⁻¹) q) = q' := by
  set s := (q'.out : SL(2, ℤ)) * δ * (q'.out : SL(2, ℤ))⁻¹ with hs_def
  induction q using QuotientGroup.induction_on with | _ g => ?_
  show slGamma_p_αToGamma1 (N := N) α (QuotientGroup.mk (s * g)) = q'
  rw [slGamma_p_αToGamma1_mk]
  have h_g : (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma1 N) = q' := by
    rwa [← slGamma_p_αToGamma1_mk (N := N) α g]
  have h_gm : g⁻¹ * q'.out ∈ Gamma1 N :=
    QuotientGroup.eq.mp (h_g.trans q'.out_eq.symm)
  rw [← q'.out_eq, hs_def, QuotientGroup.eq]
  have hrw :
      ((q'.out : SL(2, ℤ)) * δ * (q'.out : SL(2, ℤ))⁻¹ * g)⁻¹ * q'.out =
        (g⁻¹ * q'.out) * δ⁻¹ := by group
  rw [hrw]
  exact mul_mem h_gm (inv_mem hδ)

omit [NeZero N] in
open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory Classical in
/-- Summand equality used by `traceSlash_Gamma_p_α_slash_Gamma1`: after reindexing the
fiber by left-multiplication by `hr⁻¹` where `hr = q'.out · γ⁻¹ · q'.out⁻¹`, the connector
`(slLeftMul hr⁻¹ q).out⁻¹ · q'.out · γ` differs from the original connector
`q.out⁻¹ · q'.out` by a left `Γ_p(α)`-factor that `G` absorbs via `hG_slash`. -/
private lemma traceSlash_Gamma_p_α_slash_Gamma1_summand
    (α : GL (Fin 2) ℚ) (G : ℍ → ℂ)
    (hG_slash : ∀ γ ∈ Gamma_p_α (N := N) α, G ∣[k] γ = G)
    (q' : SL(2, ℤ) ⧸ Gamma1 N) (γ : SL(2, ℤ))
    (q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) :
    G ∣[k] ((q.out : SL(2, ℤ))⁻¹ * q'.out) =
      G ∣[k] ((slLeftMul_Gamma_p_α (N := N) α
        ((q'.out : SL(2, ℤ)) * (γ : SL(2, ℤ))⁻¹ * (q'.out : SL(2, ℤ))⁻¹)⁻¹ q).out⁻¹
          * q'.out * γ) := by
  set hr := (q'.out : SL(2, ℤ)) * (γ : SL(2, ℤ))⁻¹ * (q'.out : SL(2, ℤ))⁻¹ with hr_def
  set qt := slLeftMul_Gamma_p_α (N := N) α hr⁻¹ q with hqt_def
  have hqt_mk : qt = QuotientGroup.mk (hr⁻¹ * q.out) := by
    rw [hqt_def]
    conv_lhs => rw [← q.out_eq]
    rfl
  have hγp : qt.out⁻¹ * (hr⁻¹ * q.out) ∈ Gamma_p_α (N := N) α :=
    QuotientGroup.eq.mp (qt.out_eq.trans hqt_mk)
  set γp := qt.out⁻¹ * (hr⁻¹ * q.out) with hγp_def
  have h_rewrite : (qt.out : SL(2, ℤ))⁻¹ * q'.out * γ =
      γp * ((q.out : SL(2, ℤ))⁻¹ * q'.out) := by
    rw [hγp_def, hr_def]; group
  rw [h_rewrite]
  conv_rhs => rw [SlashAction.slash_mul, hG_slash γp hγp]

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory Classical in
/-- **The DS trace is a `Γ₁(N)`-form (DS 5.4.4: `tr g ∈ S_k(Γ)`, slash-invariance).**
When `G` is `Γ_p(α)`-slash-invariant, the partial trace `traceSlash_Gamma_p_α α G q'`
is invariant under the weight-`k` slash by any `γ ∈ Γ₁(N)`. The proof reindexes the
fiber over `q'` by the uniform left-multiplication bijection
`slLeftMul_Gamma_p_α (q'.out·γ⁻¹·q'.out⁻¹)` (which permutes the fiber because right
multiplication by `γ ∈ Γ₁(N)` permutes the `Γ_p(α)\SL` cosets above `q'`), under which
each connecting element changes only by a left `Γ_p(α)`-factor that `G` absorbs. This
upgrades `traceSlash_Gamma_p_α_indep` (independence of base coset) to genuine
membership `tr G ∈ S_k(Γ₁(N))`. -/
theorem traceSlash_Gamma_p_α_slash_Gamma1
    (α : GL (Fin 2) ℚ) (G : ℍ → ℂ)
    (hG_slash : ∀ γ ∈ Gamma_p_α (N := N) α, G ∣[k] γ = G)
    (q' : SL(2, ℤ) ⧸ Gamma1 N) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N) :
    (traceSlash_Gamma_p_α (N := N) (k := k) α G q') ∣[k] (γ : SL(2, ℤ)) =
      traceSlash_Gamma_p_α (N := N) (k := k) α G q' := by
  conv_lhs => rw [traceSlash_Gamma_p_α, SlashAction.sum_slash]
  rw [traceSlash_Gamma_p_α]
  rw [show (∑ q ∈ Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α ↦
        slGamma_p_αToGamma1 (N := N) α q = q'),
        (G ∣[k] ((q.out : SL(2, ℤ))⁻¹ * q'.out)) ∣[k] (γ : SL(2, ℤ))) =
      ∑ q ∈ Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α ↦
        slGamma_p_αToGamma1 (N := N) α q = q'),
        G ∣[k] ((q.out : SL(2, ℤ))⁻¹ * q'.out * γ) from
    Finset.sum_congr rfl fun q _ ↦ by rw [← SlashAction.slash_mul]]
  -- reindex the fiber by left-multiplication by `hr = q'.out·γ⁻¹·q'.out⁻¹`.
  set hr := (q'.out : SL(2, ℤ)) * (γ : SL(2, ℤ))⁻¹ * (q'.out : SL(2, ℤ))⁻¹ with hr_def
  refine (Finset.sum_bij'
    (fun q _ ↦ slLeftMul_Gamma_p_α (N := N) α hr⁻¹ q)
    (fun q _ ↦ slLeftMul_Gamma_p_α (N := N) α hr q)
    (fun q hq ↦ ?_) (fun q hq ↦ ?_)
    (fun q _ ↦ by
      show slLeftMul_Gamma_p_α (N := N) α hr
        (slLeftMul_Gamma_p_α (N := N) α hr⁻¹ q) = q
      rw [slLeftMul_Gamma_p_α_comp, mul_inv_cancel, slLeftMul_Gamma_p_α_one])
    (fun q _ ↦ by
      show slLeftMul_Gamma_p_α (N := N) α hr⁻¹
        (slLeftMul_Gamma_p_α (N := N) α hr q) = q
      rw [slLeftMul_Gamma_p_α_comp, inv_mul_cancel, slLeftMul_Gamma_p_α_one])
    (fun q _ ↦ traceSlash_Gamma_p_α_slash_Gamma1_summand α G hG_slash q' γ q)).symm
  · -- bullet 1: slLeftMul hr⁻¹ q stays in fiber(q'), using δ = γ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rw [show (hr⁻¹ : SL(2, ℤ)) =
        (q'.out : SL(2, ℤ)) * γ * (q'.out : SL(2, ℤ))⁻¹ by rw [hr_def]; group]
    exact slGamma_p_αToGamma1_slLeftMul_conj_self α q' hγ hq
  · -- bullet 2: slLeftMul hr q stays in fiber(q'), using δ = γ⁻¹
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rw [show (hr : SL(2, ℤ)) =
        (q'.out : SL(2, ℤ)) * γ⁻¹ * (q'.out : SL(2, ℤ))⁻¹ by rw [hr_def]]
    exact slGamma_p_αToGamma1_slLeftMul_conj_self α q' (inv_mem hγ) hq

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory Classical in
/-- **DS 5.4.4 — clean `Γ_p(α)`-FD ↔ `Γ₁(N)`-FD transfer corollary (the step-(a)
upgrade).** Combining the fundamental-domain transfer form
(`setIntegral_Gamma_p_α_fundDomain_PSL_petersson_eq_traceSlash_SL_outer_q_sum`), the
base-coset independence of the trace (`traceSlash_Gamma_p_α_indep`), and the fact that
the trace `tr G` is itself a `Γ₁(N)`-form (`traceSlash_Gamma_p_α_slash_Gamma1`), the
`Γ_p(α)`-FD Petersson integral of `pet F G` (carrying its fiber count
`c_p = slToPslQuot_fiberCard_Gamma_p_α α`) reassembles into the `Γ₁(N)`-FD integral of
`pet F (tr G)` (carrying the `Γ₁(N)` fiber count `c_N = slToPslQuot_fiberCard N`):
```
c_p • ∫_{Γ_p(α)-FD} pet F G = c_N • ∫_{Γ₁-FD} pet F (tr_{q₀} G).
```
This is the exact `[Γ₁ : Γ_p(α)]`-vs-`c_N` reconciliation the global adjoint route
needs: both sides are honest level-`Γ` integrals once the trace lands on the linear
slot. `q₀` is any chosen base coset (the value is independent of it by `_indep`). -/
theorem setIntegral_Gamma_p_α_fundDomain_PSL_petersson_eq_traceSlash_Gamma1_fundDomain
    (α : GL (Fin 2) ℚ) (F G : ℍ → ℂ) (q₀ : SL(2, ℤ) ⧸ Gamma1 N)
    (hF_slash : ∀ γ ∈ Gamma1 N, F ∣[k] γ = F)
    (hG_slash : ∀ γ ∈ Gamma_p_α (N := N) α, G ∣[k] γ = G)
    (h_int : IntegrableOn (fun τ ↦ petersson k F G τ)
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) μ_hyp)
    (h_int_trace : TraceFiberIntegrable (N := N) (k := k) α F G)
    (h_int_tr : IntegrableOn
      (fun τ ↦ petersson k F (traceSlash_Gamma_p_α (N := N) (k := k) α G q₀) τ)
      (Gamma1_fundDomain_PSL N) μ_hyp) :
    (slToPslQuot_fiberCard_Gamma_p_α (N := N) α) •
        ∫ τ in Gamma_p_α_fundDomain_PSL (N := N) α, petersson k F G τ ∂μ_hyp =
      (slToPslQuot_fiberCard N) •
        ∫ τ in Gamma1_fundDomain_PSL N,
          petersson k F (traceSlash_Gamma_p_α (N := N) (k := k) α G q₀) τ ∂μ_hyp := by
  rw [setIntegral_Gamma_p_α_fundDomain_PSL_petersson_eq_traceSlash_SL_outer_q_sum
    (N := N) α F G hF_slash hG_slash h_int h_int_trace]
  -- collapse the per-`q'` trace to the single base trace `tr_{q₀} G`, then re-fold
  -- the uniform `SL/Γ₁`-tile sum via the `Γ₁` substrate.
  rw [show (∑ q' : SL(2, ℤ) ⧸ Gamma1 N,
        ∫ τ in (q'.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
          petersson k F (traceSlash_Gamma_p_α (N := N) (k := k) α G q') τ ∂μ_hyp) =
      ∑ q' : SL(2, ℤ) ⧸ Gamma1 N,
        ∫ τ in (q'.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
          petersson k F (traceSlash_Gamma_p_α (N := N) (k := k) α G q₀) τ ∂μ_hyp from
    Finset.sum_congr rfl fun q' _ ↦ by
      rw [traceSlash_Gamma_p_α_indep (N := N) α G hG_slash q' q₀]]
  exact setIntegral_Gamma1_fundDomain_PSL_eq_SL_outer_q_sum
    (petersson k F (traceSlash_Gamma_p_α (N := N) (k := k) α G q₀))
    (fun γ hγ τ ↦ by
      rw [← petersson_slash_SL,
        show F ∣[k] (γ : SL(2, ℤ)) = F from hF_slash γ hγ,
        show traceSlash_Gamma_p_α (N := N) (k := k) α G q₀ ∣[k] (γ : SL(2, ℤ)) =
          traceSlash_Gamma_p_α (N := N) (k := k) α G q₀ from
          traceSlash_Gamma_p_α_slash_Gamma1 (N := N) α G hG_slash q₀ hγ])
    h_int_tr

section W5a

/-- The real matrix `map (Rat.castHom ℝ) (T_p_lower p hp) = diag(p,1)`. -/
lemma map_T_p_lower_real_val (p : ℕ) (hp : 0 < p) :
    ((Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (T_p_lower p hp)) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![(p : ℝ), 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T_p_lower, Matrix.GeneralLinearGroup.map, Matrix.map_apply]

/-- The conjugate `A·(mapGL ℝ γ)·A⁻¹` for `A = diag(p,1)` has entries
`!![a, p·b; c/p, d]` (over ℝ), where `γ = !![a,b;c,d]`. -/
lemma conj_T_p_lower_real_val (p : ℕ) (hp : 0 < p) (γ : SL(2, ℤ)) :
    (((Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (T_p_lower p hp)) *
        (toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) *
        ((Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (T_p_lower p hp)))⁻¹) :
      Matrix (Fin 2) (Fin 2) ℝ) =
    !![((γ.val 0 0 : ℤ) : ℝ), (p : ℝ) * ((γ.val 0 1 : ℤ) : ℝ);
       ((γ.val 1 0 : ℤ) : ℝ) / (p : ℝ), ((γ.val 1 1 : ℤ) : ℝ)] := by
  have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hinv : ((((Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (T_p_lower p hp)))⁻¹ :
      GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![1 / (p : ℝ), 0; 0, 1] := by
    rw [Matrix.coe_units_inv, map_T_p_lower_real_val p hp, Matrix.inv_def,
      Matrix.adjugate_fin_two_of, Ring.inverse_eq_inv']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_two_of]; field_simp
  have hγr : ((toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      !![((γ.val 0 0 : ℤ) : ℝ), ((γ.val 0 1 : ℤ) : ℝ);
         ((γ.val 1 0 : ℤ) : ℝ), ((γ.val 1 1 : ℤ) : ℝ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [map_T_p_lower_real_val p hp, hinv, hγr, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

omit [NeZero N] in
open CongruenceSubgroup Pointwise ConjAct in
/-- Forward direction of `mem_Gamma_p_α_T_p_lower`: if `γ` lies in the conjugate
intersection `conjGL Γ₁(N) (mapGL A)` (with `A = diag(p,1)`), the resulting integral
preimage `y` has `(1,0)`-entry `γ₁₀ / p`, forcing `p ∣ γ₁₀`. -/
private lemma mem_Gamma_p_α_T_p_lower_mp
    (p : ℕ) (hp : 0 < p) {γ : SL(2, ℤ)}
    (h : γ ∈ conjGL (Gamma1 N) ((T_p_lower p hp).map (Rat.castHom ℝ))) :
    (p : ℤ) ∣ γ.val 1 0 := by
  have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  obtain ⟨y, _, hy_eq⟩ := mem_conjGL.mp h
  -- The `(1,0)` entry of `mapGL y = A·γ·A⁻¹` is the integer `y₁₀ = c/p`, so `p ∣ c`.
  have hentry : ((y.val 1 0 : ℤ) : ℝ) = ((γ.val 1 0 : ℤ) : ℝ) / (p : ℝ) := by
    have h1 : ((toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) y)) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        !![((γ.val 0 0 : ℤ) : ℝ), (p : ℝ) * ((γ.val 0 1 : ℤ) : ℝ);
           ((γ.val 1 0 : ℤ) : ℝ) / (p : ℝ), ((γ.val 1 1 : ℤ) : ℝ)] := by
      rw [hy_eq, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
        conj_T_p_lower_real_val p hp γ]
    have h10 := congrFun (congrFun h1 1) 0
    simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] using h10
  have : ((γ.val 1 0 : ℤ) : ℝ) = ((y.val 1 0 : ℤ) : ℝ) * (p : ℝ) := by
    rw [hentry]; field_simp
  have hcast : (γ.val 1 0 : ℤ) = (y.val 1 0 : ℤ) * (p : ℤ) := by exact_mod_cast this
  exact ⟨y.val 1 0, by rw [hcast]; ring⟩

open CongruenceSubgroup Pointwise ConjAct in
/-- Helper: the explicit integral matrix `y = [[a, p·b], [k, d]]` (with `d·a - p·b·k = 1`
guaranteed by the `Γ₁(N)`-side data of `γ` and `γ₁₀ = p·k`) used to witness conjugacy
in the reverse direction of `mem_Gamma_p_α_T_p_lower`. The determinant is `1` because
`γ.val.det = 1` and `(p·γ₀₁·k) = γ₀₁·γ₁₀`. -/
private lemma mem_Gamma_p_α_T_p_lower_mpr_det
    (p : ℕ) {γ : SL(2, ℤ)} {k : ℤ} (hk : γ.val 1 0 = p * k) :
    (!![γ.val 0 0, (p : ℤ) * γ.val 0 1; k, γ.val 1 1] :
      Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  rw [Matrix.det_fin_two_of]
  have hγdet : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = 1 := by
    have := γ.property
    rw [Matrix.det_fin_two] at this
    linarith [this]
  have : (p : ℤ) * γ.val 0 1 * k = γ.val 0 1 * γ.val 1 0 := by
    rw [hk]; ring
  linarith [hγdet, this]

omit [NeZero N] in
open CongruenceSubgroup Pointwise ConjAct in
/-- Helper: the `(1,0)` entry `k` of the witness `y` reduces to `0 mod N`. This is the
key Γ₁(N) membership ingredient on the reverse side, deduced from
`hc : γ₁₀ ≡ 0 mod N`, `hk : γ₁₀ = p·k`, and `gcd(p, N) = 1`. -/
private lemma mem_Gamma_p_α_T_p_lower_mpr_k_mod_N
    (p : ℕ) (hpN : Nat.Coprime p N) {γ : SL(2, ℤ)} {k : ℤ}
    (hc : (γ.val 1 0 : ZMod N) = 0) (hk : γ.val 1 0 = p * k) :
    (k : ZMod N) = 0 := by
  have hN_dvd : (N : ℤ) ∣ γ.val 1 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hc
  have hN_dvd_pk : (N : ℤ) ∣ (p : ℤ) * k := hk ▸ hN_dvd
  have hco : IsCoprime (N : ℤ) (p : ℤ) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by exact_mod_cast hpN.symm)
  have hN_dvd_k : (N : ℤ) ∣ k := hco.dvd_of_dvd_mul_left hN_dvd_pk
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hN_dvd_k; exact_mod_cast hN_dvd_k

omit [NeZero N] in
open CongruenceSubgroup Pointwise ConjAct in
/-- Reverse direction of `mem_Gamma_p_α_T_p_lower`: given `γ ∈ Γ₁(N)` with `p ∣ γ₁₀`,
the integral matrix `y = [[a, p·b], [k, d]]` (with `k = γ₁₀/p`) lies in `Γ₁(N)` and
satisfies `mapGL y = A · mapGL γ · A⁻¹`, witnessing membership in
`conjGL Γ₁(N) (mapGL A)` (and hence in `Γ_p(T_p_lower)` after intersecting with
`Γ₁(N)`). -/
private lemma mem_Gamma_p_α_T_p_lower_mpr
    (p : ℕ) (hp : 0 < p) (hpN : Nat.Coprime p N) {γ : SL(2, ℤ)}
    (hγ₁ : γ ∈ Gamma1 N) (hdvd : (p : ℤ) ∣ γ.val 1 0) :
    γ ∈ conjGL (Gamma1 N) ((T_p_lower p hp).map (Rat.castHom ℝ)) := by
  have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  rw [mem_conjGL]
  obtain ⟨k, hk⟩ := hdvd
  obtain ⟨ha, hd, hc⟩ := (Gamma1_mem N γ).mp hγ₁
  have hdet := mem_Gamma_p_α_T_p_lower_mpr_det p hk
  set y : SL(2, ℤ) := ⟨!![γ.val 0 0, (p : ℤ) * γ.val 0 1; k, γ.val 1 1], hdet⟩ with hy_def
  have hk_N : (k : ZMod N) = 0 := mem_Gamma_p_α_T_p_lower_mpr_k_mod_N (N := N) p hpN hc hk
  have hy_mem : y ∈ Gamma1 N := by
    rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · show ((y.val 0 0 : ℤ) : ZMod N) = 1
      simp only [hy_def, Matrix.SpecialLinearGroup.coe_mk, Matrix.cons_val', Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one]
      exact ha
    · show ((y.val 1 1 : ℤ) : ZMod N) = 1
      simp only [hy_def, Matrix.SpecialLinearGroup.coe_mk, Matrix.cons_val', Matrix.of_apply,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      exact hd
    · show ((y.val 1 0 : ℤ) : ZMod N) = 0
      simp only [hy_def, Matrix.SpecialLinearGroup.coe_mk, Matrix.cons_val', Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      exact hk_N
  refine ⟨y, hy_mem, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    conj_T_p_lower_real_val p hp γ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hy_def, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, hk]; field_simp

omit [NeZero N] in
open CongruenceSubgroup Pointwise ConjAct in
/-- **Membership characterization of `Γ_p(T_p_lower)`.** For `A = diag(p,1)`, conjugation
`A·γ·A⁻¹ = [[a, p·b], [c/p, d]]` is integral (and lands in `Γ₁(N)`) iff `p ∣ c`. Hence
`Γ_p(A) = {γ ∈ Γ₁(N) : p ∣ γ₁₀}` (the `Γ₀(p)`-type lower-left condition). -/
lemma mem_Gamma_p_α_T_p_lower (p : ℕ) (hp : 0 < p) (hpN : Nat.Coprime p N)
    {γ : SL(2, ℤ)} :
    γ ∈ Gamma_p_α (N := N) (T_p_lower p hp) ↔
      γ ∈ Gamma1 N ∧ (p : ℤ) ∣ γ.val 1 0 := by
  rw [Gamma_p_α, Subgroup.mem_inf]
  refine ⟨fun ⟨h, hγ₁⟩ ↦ ⟨hγ₁, mem_Gamma_p_α_T_p_lower_mp p hp h⟩, fun ⟨hγ₁, hdvd⟩ ↦ ?_⟩
  exact ⟨mem_Gamma_p_α_T_p_lower_mpr p hp hpN hγ₁ hdvd, hγ₁⟩

omit [NeZero N] in
open CongruenceSubgroup Pointwise ConjAct in
/-- `Γ_p(T_p_lower) = Γ₁(N) ⊓ Γ₀(p)`. -/
lemma Gamma_p_α_T_p_lower_eq_inf (p : ℕ) (hp : 0 < p) (hpN : Nat.Coprime p N) :
    Gamma_p_α (N := N) (T_p_lower p hp) = Gamma1 N ⊓ Gamma0 p := by
  ext γ
  rw [mem_Gamma_p_α_T_p_lower p hp hpN, Subgroup.mem_inf, Gamma0_mem,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The explicit `Γ₁(N)` element `k = [[1, m], [N, a⁻¹p]]` where `a⁻¹p - Nm = 1`
(`a⁻¹ = aInvOfCoprime`, `m = mIdxOfCoprime`).  Its lower-right entry `a⁻¹p ≡ 0 (mod p)`,
which lets `S·k⁻¹` land in `Γ₀(p)`. -/
private noncomputable def Gamma1_S_corrector (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    SL(2, ℤ) :=
  ⟨!![1, mIdxOfCoprime N p hpN; (N : ℤ), (aInvOfCoprime N p hpN : ℤ) * p],
    by rw [Matrix.det_fin_two_of]; linarith [N_mul_mIdx_eq N p hpN]⟩

private lemma Gamma1_S_corrector_mem (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    Gamma1_S_corrector N p hpN ∈ Gamma1 N := by
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩
  · change ((1 : ℤ) : ZMod N) = 1; push_cast; rfl
  · change (((aInvOfCoprime N p hpN : ℤ) * p : ℤ) : ZMod N) = 1
    push_cast; exact aInvOfCoprime_mul_eq_one N p hpN
  · change ((N : ℤ) : ZMod N) = 0; push_cast; rw [ZMod.natCast_self]

/-- The lower-unipotent `[[1,0],[m,1]] ∈ SL₂(ℤ)`. -/
private def lowerUni (m : ℤ) : SL(2, ℤ) :=
  ⟨!![1, 0; m, 1], by rw [Matrix.det_fin_two_of]; ring⟩

omit [NeZero N] in
private lemma lowerUni_mem_Gamma1 {m : ℤ} (hm : (m : ZMod N) = 0) :
    lowerUni m ∈ Gamma1 N := by
  rw [Gamma1_mem]
  refine ⟨by change ((1 : ℤ) : ZMod N) = 1; push_cast; rfl,
    by change ((1 : ℤ) : ZMod N) = 1; push_cast; rfl, ?_⟩
  change ((m : ℤ) : ZMod N) = 0; exact hm

/-- **Set-product surjectivity (the genuine W5a content).** For `gcd(p, N) = 1`, every
`g ∈ SL₂(ℤ)` factors as `g = (g·k⁻¹)·k` with `k ∈ Γ₁(N)` and `g·k⁻¹ ∈ Γ₀(p)`.  Two cases on
the bottom-right entry `d = g₁₁` mod `p`: if `d` is a unit pick a lower-unipotent `k`
killing the lower-left mod `p`; if `d ≡ 0` reuse `Gamma1_S_corrector`. -/
theorem exists_Gamma1_mul_inv_mem_Gamma0 (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (g : SL(2, ℤ)) : ∃ k ∈ Gamma1 N, g * k⁻¹ ∈ Gamma0 p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  by_cases hd : ((g.1 1 1 : ℤ) : ZMod p) = 0
  · -- `d ≡ 0 mod p`: `k = Gamma1_S_corrector`, lower-left of `g·k⁻¹` is `c·(a⁻¹p) - d·N ≡ 0`.
    refine ⟨Gamma1_S_corrector N p hpN, Gamma1_S_corrector_mem N p hpN, ?_⟩
    rw [Gamma0_mem]
    have h10 : ((g * (Gamma1_S_corrector N p hpN)⁻¹).1 1 0 : ℤ) =
        g.1 1 0 * ((aInvOfCoprime N p hpN : ℤ) * p) - g.1 1 1 * (N : ℤ) := by
      rw [show ((g * (Gamma1_S_corrector N p hpN)⁻¹).1 1 0 : ℤ) =
          (g.1 1 0) * (((Gamma1_S_corrector N p hpN)⁻¹).1 0 0) +
          (g.1 1 1) * (((Gamma1_S_corrector N p hpN)⁻¹).1 1 0)
        from by rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]]
      simp only [Gamma1_S_corrector, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two_of,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
      ring
    rw [h10]; push_cast
    rw [show ((g.1 1 1 : ℤ) : ZMod p) * (N : ZMod p) = 0 by rw [hd]; ring, sub_zero,
      ZMod.natCast_self, mul_zero, mul_zero]
  · -- `d` a unit mod p: `k = lowerUni m`, `m ≡ 0 mod N`, `m ≡ c·d⁻¹ mod p`.
    obtain ⟨m, hmN, hmp⟩ := Nat.chineseRemainder (n := N) (m := p) (Nat.Coprime.symm hpN) 0
      (((g.1 1 0 : ZMod p) * ((g.1 1 1 : ZMod p))⁻¹).val)
    refine ⟨lowerUni (m : ℤ), lowerUni_mem_Gamma1 ?_, ?_⟩
    · have hdvd : (N : ℤ) ∣ (m : ℤ) := by
        exact_mod_cast Nat.modEq_zero_iff_dvd.mp hmN
      rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hdvd
    · rw [Gamma0_mem]
      have h10 : ((g * (lowerUni (m : ℤ))⁻¹).1 1 0 : ℤ) =
          g.1 1 0 - g.1 1 1 * (m : ℤ) := by
        rw [show ((g * (lowerUni (m : ℤ))⁻¹).1 1 0 : ℤ) =
            (g.1 1 0) * (((lowerUni (m : ℤ))⁻¹).1 0 0) +
            (g.1 1 1) * (((lowerUni (m : ℤ))⁻¹).1 1 0)
          from by rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]]
        simp only [lowerUni, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two_of,
          Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
        ring
      rw [h10]; push_cast
      have hmp' : (m : ZMod p) = (g.1 1 0 : ZMod p) * ((g.1 1 1 : ZMod p))⁻¹ := by
        have hmod : (m : ZMod p) = (((g.1 1 0 : ZMod p) * ((g.1 1 1 : ZMod p))⁻¹).val : ZMod p) :=
          (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmp
        rwa [ZMod.natCast_val, ZMod.cast_id] at hmod
      rw [hmp']
      have hone : (g.1 1 1 : ZMod p) * ((g.1 1 1 : ZMod p))⁻¹ = 1 := by
        rw [ZMod.mul_inv_eq_gcd]
        have hndvd : ¬ p ∣ (g.1 1 1 : ZMod p).val := by
          rw [← ZMod.natCast_eq_zero_iff _ p, ZMod.natCast_val, ZMod.cast_id]
          exact hd
        have hcop : (g.1 1 1 : ZMod p).val.gcd p = 1 :=
          (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd))
        rw [hcop, Nat.cast_one]
      rw [show (g.1 1 1 : ZMod p) * ((g.1 1 0 : ZMod p) * ((g.1 1 1 : ZMod p))⁻¹) =
          (g.1 1 0 : ZMod p) * ((g.1 1 1 : ZMod p) * ((g.1 1 1 : ZMod p))⁻¹) by ring,
        hone, mul_one, sub_self]

/-- **Coprimality index equality.** Since `Γ₀(p) · Γ₁(N) = SL₂(ℤ)`, the natural map
`Γ₀(p) ⧸ (Γ₁(N) ∩ Γ₀(p)) → SL₂(ℤ) ⧸ Γ₁(N)` is a bijection, so
`[Γ₀(p) : Γ₀(p) ∩ Γ₁(N)] = [SL₂(ℤ) : Γ₁(N)]`. -/
theorem Gamma1_relIndex_Gamma0_eq_index (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    (Gamma1 N).relIndex (Gamma0 p) = (Gamma1 N).index := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card, Subgroup.index_eq_card]
  -- The natural map `Γ₀p ⧸ (Γ₁N ∩ Γ₀p) → SL₂ ⧸ Γ₁N`, `⟦h⟧ ↦ ⟦h⟧`.
  set f : (Gamma0 p) ⧸ ((Gamma1 N).subgroupOf (Gamma0 p)) → SL(2, ℤ) ⧸ Gamma1 N :=
    Quotient.lift (fun h : Gamma0 p ↦ (QuotientGroup.mk (h : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma1 N))
      (by
        intro a b hab
        change (QuotientGroup.leftRel _).r _ _ at hab
        rw [QuotientGroup.leftRel_apply] at hab
        rw [Subgroup.mem_subgroupOf] at hab
        exact QuotientGroup.eq.mpr hab) with hf_def
  have hf_bij : Function.Bijective f := by
    constructor
    · -- injective
      intro x y hxy
      induction x using QuotientGroup.induction_on with | _ a => ?_
      induction y using QuotientGroup.induction_on with | _ b => ?_
      have : (QuotientGroup.mk (a : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma1 N) =
          QuotientGroup.mk (b : SL(2, ℤ)) := hxy
      rw [QuotientGroup.eq] at this ⊢
      rw [Subgroup.mem_subgroupOf]
      exact this
    · -- surjective: every `⟦g⟧` has a `Γ₀p`-rep by the set-product surjectivity
      intro y
      induction y using QuotientGroup.induction_on with | _ g => ?_
      obtain ⟨k, hk_mem, hgk⟩ := exists_Gamma1_mul_inv_mem_Gamma0 p hp hpN g
      refine ⟨QuotientGroup.mk ⟨g * k⁻¹, hgk⟩, ?_⟩
      show (QuotientGroup.mk ((⟨g * k⁻¹, hgk⟩ : Gamma0 p) : SL(2, ℤ)) :
        SL(2, ℤ) ⧸ Gamma1 N) = QuotientGroup.mk g
      rw [QuotientGroup.eq]
      have : (g * k⁻¹)⁻¹ * g = k := by group
      rwa [this]
  rw [Nat.card_congr (Equiv.ofBijective f hf_bij)]

/-- **W5a index — the crux.** `[Γ₁(N) : Γ_p(T_p_lower)] = p + 1`.  Combinatorially this is
the `(p+1)`-coset count of `(Γ₁ ∩ A Γ₁ A⁻¹)\Γ₁` for the `T_p` double coset (Miyake 4.5.6(1)).
Reduces to `[SL₂(ℤ) : Γ₀(p)] = p + 1` (`Gamma0_prime_index`) via the coprimality
`gcd(p, N) = 1`. -/
theorem relIndex_Gamma_p_α_T_p_lower (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    (Gamma_p_α (N := N) (T_p_lower p hp.pos)).relIndex (Gamma1 N) = p + 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [Gamma_p_α_T_p_lower_eq_inf p hp.pos hpN, inf_comm, Subgroup.inf_relIndex_right]
  -- Tower law on `Γ₀p ⊓ Γ₁ ≤ Γ₁ ≤ ⊤` and `Γ₀p ⊓ Γ₁ ≤ Γ₀p ≤ ⊤`.
  have hle₁ : Gamma0 p ⊓ Gamma1 N ≤ Gamma1 N := inf_le_right
  have hle₀ : Gamma0 p ⊓ Gamma1 N ≤ Gamma0 p := inf_le_left
  have hN_pos : 0 < (Gamma1 N).index := Nat.pos_of_ne_zero
    (CongruenceSubgroup.instFiniteIndexGamma1 N).index_ne_zero
  -- `r := relIndex (Γ₀p ⊓ Γ₁) Γ₁ = (Γ₀p).relIndex Γ₁`.
  have hrA := Subgroup.relIndex_mul_index hle₁
  have hrB := Subgroup.relIndex_mul_index hle₀
  rw [Subgroup.inf_relIndex_right] at hrA
  rw [Subgroup.inf_relIndex_left, Gamma1_relIndex_Gamma0_eq_index p hp hpN,
    Gamma0_prime_index p hp] at hrB
  -- Now: `(Γ₀p).relIndex Γ₁ · Γ₁.index = (Γ₀p ⊓ Γ₁).index = Γ₁.index · (p+1)`.
  have hkey : (Gamma0 p).relIndex (Gamma1 N) * (Gamma1 N).index =
      (Gamma1 N).index * (p + 1) := by
    rw [hrA, hrB]
  exact Nat.eq_of_mul_eq_mul_right hN_pos (by rw [hkey]; ring)

open CongruenceSubgroup in
/-- The upper-triangular congruence subgroup `Γ⁰(p) = {γ ∈ SL₂(ℤ) : γ₀₁ ≡ 0 mod p}`. -/
def Gamma_up (p : ℕ) : Subgroup SL(2, ℤ) where
  carrier := { g | (g 0 1 : ZMod p) = 0 }
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    have h := (Matrix.two_mul_expl a.1 b.1).2.1
    simp only [Matrix.SpecialLinearGroup.coe_mul] at *
    rw [h]; push_cast; rw [ha, hb]; ring
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [SL2_inv_expl a]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Int.cast_neg, neg_eq_zero]
    exact ha

@[simp]
theorem Gamma_up_mem {p : ℕ} {A : SL(2, ℤ)} : A ∈ Gamma_up p ↔ (A 0 1 : ZMod p) = 0 :=
  Iff.rfl

open CongruenceSubgroup Pointwise ConjAct in
/-- **Fricke conjugate.** `Γ⁰(p) = S·Γ₀(p)·S⁻¹`, where `S = [[0,-1],[1,0]] ∈ SL₂(ℤ)`.
Conjugation by `S` sends the lower-left entry `γ₁₀` to `-γ₀₁`, so the `Γ₀(p)` lower-left
condition becomes the `Γ⁰(p)` upper-right condition. -/
theorem Gamma_up_eq_conj_Gamma0 (p : ℕ) :
    Gamma_up p = ConjAct.toConjAct ModularGroup.S • Gamma0 p := by
  ext γ
  rw [Gamma_up_mem, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Gamma0_mem]
  have hentry : (((ConjAct.toConjAct ModularGroup.S)⁻¹ • γ : SL(2, ℤ)).val 1 0 : ℤ) =
      -(γ.val 0 1) := by
    rw [← map_inv, ConjAct.toConjAct_smul]
    simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two_of, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      Matrix.cons_val']
    ring
  rw [hentry]; push_cast; rw [neg_eq_zero]

open CongruenceSubgroup in
/-- `[SL₂(ℤ) : Γ⁰(p)] = p + 1` for prime `p`.  Fricke-conjugate of `Gamma0_prime_index`. -/
theorem Gamma_up_prime_index (p : ℕ) (hp : Nat.Prime p) : (Gamma_up p).index = p + 1 := by
  have htop : (ConjAct.toConjAct ModularGroup.S • (⊤ : Subgroup SL(2, ℤ))) = ⊤ := by
    ext x; simp [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rw [Gamma_up_eq_conj_Gamma0, ← Subgroup.relIndex_top_right, ← htop,
    Subgroup.relIndex_pointwise_smul, Subgroup.relIndex_top_right,
    HeckeRing.GL2.Gamma0_prime_index p hp]

omit [NeZero N] in
/-- The standard generator `T = [[1,1],[0,1]] ∈ Γ₁(N)` since `T₀₀ = T₁₁ = 1`, `T₁₀ = 0`. -/
private lemma ModularGroup_T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 N := by
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.coe_T]

/-- The explicit `Γ₁(N)` element `kᵤ = [[a⁻¹p, -1], [-N·m, 1]]` where `a⁻¹p - N·m = 1`
(`a⁻¹ = aInvOfCoprime`, `m = mIdxOfCoprime`).  Its upper-left entry `a⁻¹p ≡ 0 (mod p)`,
which lets `S·kᵤ⁻¹` land in `Γ⁰(p)`. -/
private noncomputable def Gamma1_S_corrector_up (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    SL(2, ℤ) :=
  ⟨!![(aInvOfCoprime N p hpN : ℤ) * p, -1; -(N : ℤ) * mIdxOfCoprime N p hpN, 1],
    by rw [Matrix.det_fin_two_of]; have := N_mul_mIdx_eq N p hpN; ring_nf; linarith⟩

private lemma Gamma1_S_corrector_up_mem (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    Gamma1_S_corrector_up N p hpN ∈ Gamma1 N := by
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩
  · change (((aInvOfCoprime N p hpN : ℤ) * p : ℤ) : ZMod N) = 1
    push_cast; exact aInvOfCoprime_mul_eq_one N p hpN
  · change ((1 : ℤ) : ZMod N) = 1; push_cast; rfl
  · change ((-(N : ℤ) * mIdxOfCoprime N p hpN : ℤ) : ZMod N) = 0
    push_cast; rw [ZMod.natCast_self]; ring

open CongruenceSubgroup in
/-- **Set-product surjectivity (the upper analog).** For `gcd(p, N) = 1`, every `g ∈ SL₂(ℤ)`
factors as `g = (g·k⁻¹)·k` with `k ∈ Γ₁(N)` and `g·k⁻¹ ∈ Γ⁰(p)`.  Two cases on the top-left
entry `a = g₀₀` mod `p`: if `a` is a unit pick `k = Tᵐ ∈ Γ₁(N)` (any power, since `T ∈ Γ₁`)
killing the upper-right mod `p`; if `a ≡ 0` reuse `Gamma1_S_corrector_up`. -/
theorem exists_Gamma1_mul_inv_mem_Gamma_up (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (g : SL(2, ℤ)) : ∃ k ∈ Gamma1 N, g * k⁻¹ ∈ Gamma_up p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  by_cases ha : ((g.1 0 0 : ℤ) : ZMod p) = 0
  · -- `a ≡ 0 mod p`: `k = Gamma1_S_corrector_up`, upper-right of `g·k⁻¹` is `a + b·(a⁻¹p) ≡ 0`.
    refine ⟨Gamma1_S_corrector_up N p hpN, Gamma1_S_corrector_up_mem N p hpN, ?_⟩
    rw [Gamma_up_mem]
    have h01 : ((g * (Gamma1_S_corrector_up N p hpN)⁻¹).1 0 1 : ℤ) =
        g.1 0 0 * 1 + g.1 0 1 * ((aInvOfCoprime N p hpN : ℤ) * p) := by
      rw [show ((g * (Gamma1_S_corrector_up N p hpN)⁻¹).1 0 1 : ℤ) =
          (g.1 0 0) * (((Gamma1_S_corrector_up N p hpN)⁻¹).1 0 1) +
          (g.1 0 1) * (((Gamma1_S_corrector_up N p hpN)⁻¹).1 1 1)
        from by rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]]
      simp only [Gamma1_S_corrector_up, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two_of,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
      ring
    rw [h01]; push_cast
    rw [show ((g.1 0 1 : ℤ) : ZMod p) * ((aInvOfCoprime N p hpN : ZMod p) * (p : ZMod p)) = 0 by
      rw [ZMod.natCast_self, mul_zero, mul_zero], add_zero, mul_one, ha]
  · -- `a` a unit mod p: `k = Tᵐ`, `m ≡ b·a⁻¹ mod p`; `Tᵐ ∈ Γ₁(N)` for any `m`.
    set m : ℤ := (((g.1 0 1 : ZMod p) * ((g.1 0 0 : ZMod p))⁻¹).val : ℤ) with hm_def
    refine ⟨ModularGroup.T ^ m,
      Subgroup.zpow_mem (Gamma1 N) (ModularGroup_T_mem_Gamma1 (N := N)) m, ?_⟩
    rw [Gamma_up_mem]
    have h01 : ((g * (ModularGroup.T ^ m)⁻¹).1 0 1 : ℤ) = g.1 0 1 - g.1 0 0 * m := by
      rw [show ((g * (ModularGroup.T ^ m)⁻¹).1 0 1 : ℤ) =
          (g.1 0 0) * (((ModularGroup.T ^ m)⁻¹).1 0 1) +
          (g.1 0 1) * (((ModularGroup.T ^ m)⁻¹).1 1 1)
        from by rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]]
      rw [← zpow_neg, ModularGroup.coe_T_zpow]
      simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
      ring
    rw [h01]; push_cast
    have hm' : (m : ZMod p) = (g.1 0 1 : ZMod p) * ((g.1 0 0 : ZMod p))⁻¹ := by
      rw [hm_def]; push_cast; rw [ZMod.natCast_val, ZMod.cast_id]
    rw [hm']
    have hone : (g.1 0 0 : ZMod p) * ((g.1 0 0 : ZMod p))⁻¹ = 1 := by
      rw [ZMod.mul_inv_eq_gcd]
      have hndvd : ¬ p ∣ (g.1 0 0 : ZMod p).val := by
        rw [← ZMod.natCast_eq_zero_iff _ p, ZMod.natCast_val, ZMod.cast_id]
        exact ha
      have hcop : (g.1 0 0 : ZMod p).val.gcd p = 1 :=
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd))
      rw [hcop, Nat.cast_one]
    rw [show (g.1 0 0 : ZMod p) * ((g.1 0 1 : ZMod p) * ((g.1 0 0 : ZMod p))⁻¹) =
        (g.1 0 1 : ZMod p) * ((g.1 0 0 : ZMod p) * ((g.1 0 0 : ZMod p))⁻¹) by ring,
      hone, mul_one, sub_self]

open CongruenceSubgroup in
/-- **Coprimality index equality (upper).** Since `Γ⁰(p) · Γ₁(N) = SL₂(ℤ)`, the natural map
`Γ⁰(p) ⧸ (Γ₁(N) ∩ Γ⁰(p)) → SL₂(ℤ) ⧸ Γ₁(N)` is a bijection, so
`[Γ⁰(p) : Γ⁰(p) ∩ Γ₁(N)] = [SL₂(ℤ) : Γ₁(N)]`. -/
theorem Gamma1_relIndex_Gamma_up_eq_index (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    (Gamma1 N).relIndex (Gamma_up p) = (Gamma1 N).index := by
  rw [Subgroup.relIndex, Subgroup.index_eq_card, Subgroup.index_eq_card]
  -- The natural map `Γ⁰p ⧸ (Γ₁N ∩ Γ⁰p) → SL₂ ⧸ Γ₁N`, `⟦h⟧ ↦ ⟦h⟧`.
  set f : (Gamma_up p) ⧸ ((Gamma1 N).subgroupOf (Gamma_up p)) → SL(2, ℤ) ⧸ Gamma1 N :=
    Quotient.lift (fun h : Gamma_up p ↦ (QuotientGroup.mk (h : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma1 N))
      (by
        intro a b hab
        change (QuotientGroup.leftRel _).r _ _ at hab
        rw [QuotientGroup.leftRel_apply] at hab
        rw [Subgroup.mem_subgroupOf] at hab
        exact QuotientGroup.eq.mpr hab) with hf_def
  have hf_bij : Function.Bijective f := by
    constructor
    · -- injective
      intro x y hxy
      induction x using QuotientGroup.induction_on with | _ a => ?_
      induction y using QuotientGroup.induction_on with | _ b => ?_
      have : (QuotientGroup.mk (a : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma1 N) =
          QuotientGroup.mk (b : SL(2, ℤ)) := hxy
      rw [QuotientGroup.eq] at this ⊢
      rw [Subgroup.mem_subgroupOf]
      exact this
    · -- surjective: every `⟦g⟧` has a `Γ⁰p`-rep by the set-product surjectivity
      intro y
      induction y using QuotientGroup.induction_on with | _ g => ?_
      obtain ⟨k, hk_mem, hgk⟩ := exists_Gamma1_mul_inv_mem_Gamma_up p hp hpN g
      refine ⟨QuotientGroup.mk ⟨g * k⁻¹, hgk⟩, ?_⟩
      show (QuotientGroup.mk ((⟨g * k⁻¹, hgk⟩ : Gamma_up p) : SL(2, ℤ)) :
        SL(2, ℤ) ⧸ Gamma1 N) = QuotientGroup.mk g
      rw [QuotientGroup.eq]
      have : (g * k⁻¹)⁻¹ * g = k := by group
      rwa [this]
  rw [Nat.card_congr (Equiv.ofBijective f hf_bij)]

open CongruenceSubgroup in
/-- **W5a adjoint index — the upper crux.** `[Γ₁(N) : Γ₁(N) ∩ Γ⁰(p)] = p + 1`.  The
adjoint-side `(p+1)`-coset count (Miyake 4.5.6, mirror of `relIndex_Gamma_p_α_T_p_lower`).
Reduces to `[SL₂(ℤ) : Γ⁰(p)] = p + 1` (`Gamma_up_prime_index`) via `gcd(p, N) = 1`. -/
theorem Gamma_up_relIndex_Gamma1 (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    (Gamma_up p).relIndex (Gamma1 N) = p + 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hle₁ : Gamma_up p ⊓ Gamma1 N ≤ Gamma1 N := inf_le_right
  have hle₀ : Gamma_up p ⊓ Gamma1 N ≤ Gamma_up p := inf_le_left
  have hN_pos : 0 < (Gamma1 N).index := Nat.pos_of_ne_zero
    (CongruenceSubgroup.instFiniteIndexGamma1 N).index_ne_zero
  have hrA := Subgroup.relIndex_mul_index hle₁
  have hrB := Subgroup.relIndex_mul_index hle₀
  rw [Subgroup.inf_relIndex_right] at hrA
  rw [Subgroup.inf_relIndex_left, Gamma1_relIndex_Gamma_up_eq_index p hp hpN,
    Gamma_up_prime_index p hp] at hrB
  -- Now: `(Γ⁰p).relIndex Γ₁ · Γ₁.index = (Γ⁰p ⊓ Γ₁).index = Γ₁.index · (p+1)`.
  have hkey : (Gamma_up p).relIndex (Gamma1 N) * (Gamma1 N).index =
      (Gamma1 N).index * (p + 1) := by
    rw [hrA, hrB]
  exact Nat.eq_of_mul_eq_mul_right hN_pos (by rw [hkey]; ring)

open CongruenceSubgroup Classical in
/-- **Fiber-card ↔ relindex bridge (the W5b foundation).** The SL-level fiber of
`slGamma_p_αToGamma1` over the trivial `Γ₁(N)`-coset is in bijection with
`Γ₁(N) ⧸ Γ_p(α)`, so the abstract uniform fiber count equals the relative index
`[Γ₁(N) : Γ_p(α)]`. (The trace engine FDT:1612 consumes the PSL-level fiber cards
`slToPslQuot_fiberCard_Gamma_p_α`; this SL-level card is the one feeding the
`relIndex • petN` reassembly `sum_SL_Gamma_p_α_petN_summand_eq_relIndex_mul_petN`.) -/
theorem slGamma_p_αToGamma1_fiberCard_eq_relIndex (α : GL (Fin 2) ℚ) :
    slGamma_p_αToGamma1_fiberCard (N := N) α =
      (Gamma_p_α (N := N) α).relIndex (Gamma1 N) := by
  rw [← slGamma_p_αToGamma1_fiberCard_eq α (QuotientGroup.mk 1), Subgroup.relIndex,
    Subgroup.index_eq_card, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  -- Forward map `Γ₁ ⧸ Γ_p.subgroupOf Γ₁ → fiber`, `[h] ↦ [h]_{Γ_p}`.
  refine Equiv.symm (Equiv.ofBijective
    (Quotient.lift (fun h : Gamma1 N ↦
      (⟨QuotientGroup.mk (h : SL(2, ℤ)), ?_⟩))
      ?_) ?_)
  · -- the value lands in the fiber over `[1]`
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [slGamma_p_αToGamma1_mk, QuotientGroup.eq, mul_one]
    exact (Gamma1 N).inv_mem h.property
  · -- well-defined: `Γ_p`-coset only depends on the `Γ_p.subgroupOf Γ₁`-coset
    intro a b hab
    change (QuotientGroup.leftRel _).r _ _ at hab
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab
    apply Subtype.ext
    show (QuotientGroup.mk (a : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) =
      QuotientGroup.mk (b : SL(2, ℤ))
    rw [QuotientGroup.eq]
    exact hab
  · -- bijective: the lift is injective and surjective onto the fiber
    constructor
    · -- injective
      intro x y hxy
      induction x using QuotientGroup.induction_on with | _ a => ?_
      induction y using QuotientGroup.induction_on with | _ b => ?_
      have hmk : (QuotientGroup.mk (a : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) =
          QuotientGroup.mk (b : SL(2, ℤ)) := congrArg Subtype.val hxy
      rw [QuotientGroup.eq] at hmk
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      exact hmk
    · -- surjective: every fiber element `⟨[g], _⟩` has `g ∈ Γ₁`, giving the `Γ₁`-rep
      rintro ⟨q, hq⟩
      induction q using QuotientGroup.induction_on with | _ g => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, slGamma_p_αToGamma1_mk,
        QuotientGroup.eq, mul_one] at hq
      refine ⟨QuotientGroup.mk ⟨g, (Gamma1 N).inv_mem_iff.mp hq⟩, ?_⟩
      apply Subtype.ext
      rfl

/-- **W5b fiber-card bridge — the `T_p_lower` instance.** The SL-level fiber count of
`slGamma_p_αToGamma1` at `α = T_p_lower = diag(p,1)` is `p + 1`, the `T_p` coset count
`[Γ₁(N) : Γ_p(A)]` (Miyake 4.5.6(1)). Combines the generic bridge with the crux index
`relIndex_Gamma_p_α_T_p_lower`. -/
theorem slGamma_p_αToGamma1_fiberCard_T_p_lower (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) :
    slGamma_p_αToGamma1_fiberCard (N := N) (T_p_lower p hp.pos) = p + 1 := by
  rw [slGamma_p_αToGamma1_fiberCard_eq_relIndex, relIndex_Gamma_p_α_T_p_lower p hp hpN]

end W5a

end HeckeRing.GL2

import Mathlib

open CongruenceSubgroup Matrix.SpecialLinearGroup Complex Function MatrixGroups ModularForm Pointwise
open UpperHalfPlane hiding I
open scoped ComplexConjugate

local notation "𝕢" => Periodic.qParam

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

noncomputable def Subgroup.dual (Γ : Subgroup (GL (Fin 2) ℝ)) : Subgroup (GL (Fin 2) ℝ) :=
  (ConjAct.toConjAct J⁻¹) • Γ

class Subgroup.IsSelfDual (Γ : Subgroup (GL (Fin 2) ℝ)) : Prop where
  self_dual : Subgroup.dual Γ = Γ

noncomputable def ModularForm.dual (f : ModularForm Γ k) : ModularForm (Subgroup.dual Γ) k :=
  ModularForm.translate f J

@[simp]
theorem ModularForm.coe_dual (f : ModularForm Γ k) :
    ⇑(ModularForm.dual f) = ⇑f ∣[k] J :=
  ModularForm.coe_translate f J

@[simp]
theorem ModularForm.dual_apply (f : ModularForm Γ k) (z : ℍ) :
    ModularForm.dual f z = (⇑f ∣[k] J) z :=
  rfl

@[simp]
theorem ModularForm.dual_zero :
    ModularForm.dual (0 : ModularForm Γ k) = 0 := by
  ext z
  simp

@[simp]
theorem ModularForm.dual_add (f g : ModularForm Γ k) :
    ModularForm.dual (f + g) = ModularForm.dual f + ModularForm.dual g := by
  ext z
  simp

@[simp]
theorem ModularForm.dual_neg (f : ModularForm Γ k) :
    ModularForm.dual (-f) = -ModularForm.dual f := by
  ext z
  simp

@[simp]
theorem ModularForm.dual_sub (f g : ModularForm Γ k) :
    ModularForm.dual (f - g) = ModularForm.dual f - ModularForm.dual g := by
  ext z
  simp [sub_eq_add_neg]

@[simp]
theorem ModularForm.dual_smul_real (c : ℝ) (f : ModularForm Γ k) :
    ModularForm.dual (c • f) = c • ModularForm.dual f := by
  ext z
  change (((c : ℂ) • ⇑f) ∣[k] J) z = (c : ℂ) * ModularForm.dual f z
  rw [smul_slash, σ_ofReal J c]
  rfl

theorem ModularForm.dual_apply_conj (f : ModularForm Γ k) (z : ℍ) :
    ModularForm.dual f z = conj (f (ofComplex (-(conj (z : ℂ))))) := by
  simp [ModularForm.slash_def, J_smul]

private theorem qParam_neg_conj (h : ℝ) (z : ℂ) :
    𝕢 h (-(conj z)) = conj (𝕢 h z) := by
  simp [Periodic.qParam, ← Complex.exp_conj, map_ofNat]

theorem ModularForm.hasSum_qExpansion_dual [Γ.IsArithmetic] (f : ModularForm Γ k) :
    ∀ z : ℍ, HasSum (fun m : ℕ ↦ conj ((qExpansion Γ.strictWidthInfty f).coeff m) • 𝕢 Γ.strictWidthInfty (z : ℂ) ^ m)
      (ModularForm.dual f z) := by
  let h := Γ.strictWidthInfty
  have hh : 0 < h := by simpa [h] using Subgroup.strictWidthInfty_pos Γ
  have hΓ : h ∈ Γ.strictPeriods := by
    simpa [h] using Subgroup.strictWidthInfty_mem_strictPeriods Γ
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Subgroup.isCusp_of_mem_strictPeriods hh hΓ⟩
  intro z
  let z' : ℍ := ofComplex (-(conj (z : ℂ)))
  have hz' : 0 < (-(conj (z : ℂ))).im := by simpa using z.im_pos
  have hcoe : (z' : ℂ) = -(conj (z : ℂ)) := by
    simp [z', ofComplex_apply_of_im_pos hz']
  have hq : 𝕢 h (z' : ℂ) = conj (𝕢 h (z : ℂ)) := by
    rw [hcoe]
    exact qParam_neg_conj h (z : ℂ)
  have hval : (⇑f ∣[k] J) z = conj (f z') := by
    simpa [ModularForm.dual_apply, z'] using ModularForm.dual_apply_conj f z
  have hs1 : HasSum (fun m : ℕ ↦ conj ((qExpansion h f).coeff m • 𝕢 h (z' : ℂ) ^ m)) (conj (f z')) :=
    (RCLike.hasSum_conj ℂ).mpr (by
      simpa using hasSum_qExpansion hh (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
        (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) z')
  simpa [h, ModularForm.dual_apply, hval, hq, Complex.conj_conj, map_mul, map_pow, smul_eq_mul] using hs1

theorem ModularForm.qExpansion_dual_coeff [Γ.IsSelfDual] [Γ.IsArithmetic]
    (f : ModularForm Γ k) (n : ℕ) :
    (qExpansion Γ.strictWidthInfty (ModularForm.dual f)).coeff n =
      conj ((qExpansion Γ.strictWidthInfty f).coeff n) := by
  let h := Γ.strictWidthInfty
  have hh : 0 < h := by simpa [h] using Subgroup.strictWidthInfty_pos Γ
  have hΓdual : h ∈ (Subgroup.dual Γ).strictPeriods := by
    simpa [h, Subgroup.IsSelfDual.self_dual (Γ := Γ)] using
      Subgroup.strictWidthInfty_mem_strictPeriods Γ
  simpa [h] using (ModularFormClass.qExpansion_coeff_unique
    (Γ := Subgroup.dual Γ) (F := ModularForm (Subgroup.dual Γ) k)
    (h := h) (hh := hh) (hΓ := hΓdual) (f := ModularForm.dual f)
    (by simpa [h] using ModularForm.hasSum_qExpansion_dual (Γ := Γ) (k := k) f) n).symm

theorem ModularForm.coe_cast_group {Γ Γ' : Subgroup (GL (Fin 2) ℝ)}
    (h : Γ = Γ') (f : ModularForm Γ k) : ⇑(h ▸ f : ModularForm Γ' k) = ⇑f := by
  cases h
  rfl

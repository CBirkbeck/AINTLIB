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
  sorry

@[simp]
theorem ModularForm.dual_add (f g : ModularForm Γ k) :
    ModularForm.dual (f + g) = ModularForm.dual f + ModularForm.dual g := by
  sorry

@[simp]
theorem ModularForm.dual_neg (f : ModularForm Γ k) :
    ModularForm.dual (-f) = -ModularForm.dual f := by
  sorry

@[simp]
theorem ModularForm.dual_sub (f g : ModularForm Γ k) :
    ModularForm.dual (f - g) = ModularForm.dual f - ModularForm.dual g := by
  sorry

@[simp]
theorem ModularForm.dual_smul_real (c : ℝ) (f : ModularForm Γ k) :
    ModularForm.dual (c • f) = c • ModularForm.dual f := by
  sorry

theorem ModularForm.dual_apply_conj (f : ModularForm Γ k) (z : ℍ) :
    ModularForm.dual f z = conj (f (ofComplex (-(conj (z : ℂ))))) := by
  sorry

private theorem qParam_neg_conj (h : ℝ) (z : ℂ) :
    𝕢 h (-(conj z)) = conj (𝕢 h z) := by
  sorry

theorem ModularForm.hasSum_qExpansion_dual [Γ.IsArithmetic] (f : ModularForm Γ k) :
    ∀ z : ℍ, HasSum (fun m : ℕ ↦ conj ((qExpansion Γ.strictWidthInfty f).coeff m) • 𝕢 Γ.strictWidthInfty (z : ℂ) ^ m)
      (ModularForm.dual f z) := by
  sorry

theorem ModularForm.qExpansion_dual_coeff [Γ.IsSelfDual] [Γ.IsArithmetic] (f : ModularForm Γ k) (n : ℕ) :
    (qExpansion Γ.strictWidthInfty (ModularForm.dual f)).coeff n = conj ((qExpansion Γ.strictWidthInfty f).coeff n) := by
  sorry

theorem ModularForm.coe_cast_group {Γ Γ' : Subgroup (GL (Fin 2) ℝ)}
    (h : Γ = Γ') (f : ModularForm Γ k) : ⇑(h ▸ f : ModularForm Γ' k) = ⇑f := by
  sorry

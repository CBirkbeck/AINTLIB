import LeanModularForms.Issues.SelfDual.Basic

open CongruenceSubgroup Matrix.SpecialLinearGroup Complex MatrixGroups ModularForm Pointwise

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

def ModularForm.isSelfDual [Γ.IsSelfDual] (f : ModularForm Γ k) : Prop :=
  (‹Γ.IsSelfDual›.self_dual ▸ ModularForm.dual f) = f

theorem ModularForm.isSelfDual_iff_coe_dual_eq [Γ.IsSelfDual] (f : ModularForm Γ k) :
    ModularForm.isSelfDual f ↔ ⇑(ModularForm.dual f) = ⇑f := by
  sorry

theorem ModularForm.isSelfDual_iff_apply [Γ.IsSelfDual] (f : ModularForm Γ k) :
    ModularForm.isSelfDual f ↔ ∀ z, ModularForm.dual f z = f z := by
  sorry

@[simp]
theorem ModularForm.isSelfDual_zero [Γ.IsSelfDual] :
    ModularForm.isSelfDual (0 : ModularForm Γ k) := by
  sorry

@[simp]
theorem ModularForm.isSelfDual_add [Γ.IsSelfDual] {f g : ModularForm Γ k}
    (hf : ModularForm.isSelfDual f) (hg : ModularForm.isSelfDual g) :
    ModularForm.isSelfDual (f + g) := by
  sorry

@[simp]
theorem ModularForm.isSelfDual_neg [Γ.IsSelfDual] {f : ModularForm Γ k}
    (hf : ModularForm.isSelfDual f) :
    ModularForm.isSelfDual (-f) := by
  sorry

@[simp]
theorem ModularForm.isSelfDual_sub [Γ.IsSelfDual] {f g : ModularForm Γ k}
    (hf : ModularForm.isSelfDual f) (hg : ModularForm.isSelfDual g) :
    ModularForm.isSelfDual (f - g) := by
  sorry

@[simp]
theorem ModularForm.isSelfDual_smul_real [Γ.IsSelfDual] (c : ℝ) {f : ModularForm Γ k}
    (hf : ModularForm.isSelfDual f) :
    ModularForm.isSelfDual (c • f) := by
  sorry

theorem ModularForm.isSelfDual_iff [Γ.IsSelfDual] [Γ.IsArithmetic] (f : ModularForm Γ k) :
    ModularForm.isSelfDual f ↔
      ∀ n, ((UpperHalfPlane.qExpansion (Subgroup.strictWidthInfty Γ) f).coeff n).im = 0 := by
  sorry

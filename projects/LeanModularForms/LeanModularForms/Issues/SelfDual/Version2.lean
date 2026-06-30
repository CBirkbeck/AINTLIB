import LeanModularForms.Issues.SelfDual.Basic

open CongruenceSubgroup Matrix.SpecialLinearGroup Complex MatrixGroups ModularForm Pointwise

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

def ModularForm.isSelfDual' (f : ModularForm Γ k) : Prop :=
  ⇑(ModularForm.dual f) = ⇑f

theorem ModularForm.isSelfDual'_iff_apply (f : ModularForm Γ k) :
    ModularForm.isSelfDual' f ↔ ∀ z, ModularForm.dual f z = f z :=
  ⟨fun h z => congrFun h z, fun h => funext h⟩

@[simp]
theorem ModularForm.isSelfDual'_zero :
    ModularForm.isSelfDual' (0 : ModularForm Γ k) := by
  sorry

@[simp]
theorem ModularForm.isSelfDual'_add {f g : ModularForm Γ k}
    (hf : ModularForm.isSelfDual' f) (hg : ModularForm.isSelfDual' g) :
    ModularForm.isSelfDual' (f + g) := by
  sorry

@[simp]
theorem ModularForm.isSelfDual'_neg {f : ModularForm Γ k}
    (hf : ModularForm.isSelfDual' f) :
    ModularForm.isSelfDual' (-f) := by
  sorry

@[simp]
theorem ModularForm.isSelfDual'_sub {f g : ModularForm Γ k}
    (hf : ModularForm.isSelfDual' f) (hg : ModularForm.isSelfDual' g) :
    ModularForm.isSelfDual' (f - g) := by
  sorry

@[simp]
theorem ModularForm.isSelfDual'_smul_real (c : ℝ) {f : ModularForm Γ k}
    (hf : ModularForm.isSelfDual' f) :
    ModularForm.isSelfDual' (c • f) := by
  sorry

theorem ModularForm.isSelfDual_iff' [Γ.IsSelfDual] [Γ.IsArithmetic] (f : ModularForm Γ k) :
    ModularForm.isSelfDual' f ↔
      ∀ n, ((UpperHalfPlane.qExpansion (Subgroup.strictWidthInfty Γ) f).coeff n).im = 0 := by
  sorry

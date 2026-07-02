import Mathlib

open CongruenceSubgroup Matrix.SpecialLinearGroup Complex MatrixGroups ModularForm Pointwise
  Subgroup
open UpperHalfPlane hiding I

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

noncomputable def Subgroup.dual (Γ : Subgroup (GL (Fin 2) ℝ)) : Subgroup (GL (Fin 2) ℝ) :=
  (ConjAct.toConjAct UpperHalfPlane.J⁻¹) • Γ

/-- `Γ` is self-dual when it is fixed by conjugation by `J`. -/
class Subgroup.IsSelfDual (Γ : Subgroup (GL (Fin 2) ℝ)) : Prop where
  self_dual : Subgroup.dual Γ = Γ

noncomputable def ModularForm.dual (f : ModularForm Γ k) : ModularForm (Subgroup.dual Γ) k :=
  ModularForm.translate f UpperHalfPlane.J

def ModularForm.isSelfDual (f : ModularForm Γ k) : Prop :=
  ⇑(ModularForm.dual f) = ⇑f







theorem Subgroup.dual_width_eq (Γ : Subgroup (GL (Fin 2) ℝ)) :
    strictWidthInfty (Subgroup.dual Γ) = strictWidthInfty Γ := by
  sorry

theorem ModularForm.isSelfDual_iff (f : ModularForm Γ k) :
    ModularForm.isSelfDual f ↔
      ∀ n, ((qExpansion (strictWidthInfty Γ) f).coeff n).im = 0 := by
  sorry

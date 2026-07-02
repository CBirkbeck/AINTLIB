import Mathlib

open CongruenceSubgroup Matrix.SpecialLinearGroup Complex MatrixGroups ModularForm Pointwise Subgroup

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

noncomputable def Subgroup.dual (Γ : Subgroup (GL (Fin 2) ℝ)) : Subgroup (GL (Fin 2) ℝ) :=
  (ConjAct.toConjAct UpperHalfPlane.J⁻¹) • Γ

/-
def Subgroup.isSelfDual (Γ : Subgroup (GL (Fin 2) ℝ)) : Prop :=
  Subgroup.dual Γ = Γ

noncomputable def ModularForm.dual (f : ModularForm Γ k) : ModularForm (Subgroup.dual Γ) k :=
  ModularForm.translate f UpperHalfPlane.J

def ModularForm.isSelfDual [Fact (Subgroup.isSelfDual Γ)] (f : ModularForm Γ k) : Prop :=
  ((Fact.out : Subgroup.isSelfDual Γ) ▸ ModularForm.dual f) = f

theorem ModularForm.isSelfDual_iff [Fact (Subgroup.isSelfDual Γ)] (f : ModularForm Γ k) :
    ModularForm.isSelfDual f ↔ ∀ n, ((UpperHalfPlane.qExpansion (Subgroup.strictWidthInfty Γ) f).coeff n).im = 0 := by
  sorry
-/

/-- `Γ` is self-dual when it is fixed by conjugation by `J`. -/
class Subgroup.IsSelfDual (Γ : Subgroup (GL (Fin 2) ℝ)) : Prop where
  self_dual : Subgroup.dual Γ = Γ

instance : Subgroup.IsSelfDual (⊥ : Subgroup (GL (Fin 2) ℝ)) where
  self_dual := by simp [Subgroup.dual]

noncomputable def ModularForm.dual (f : ModularForm Γ k) : ModularForm (Subgroup.dual Γ) k :=
  ModularForm.translate f UpperHalfPlane.J

def ModularForm.isSelfDual [Γ.IsSelfDual] (f : ModularForm Γ k) : Prop :=
  (‹Γ.IsSelfDual›.self_dual ▸ ModularForm.dual f) = f

theorem ModularForm.isSelfDual_iff [Γ.IsSelfDual] (f : ModularForm Γ k) :
    ModularForm.isSelfDual f ↔
      ∀ n, ((UpperHalfPlane.qExpansion (Subgroup.strictWidthInfty Γ) f).coeff n).im = 0 := by
  sorry

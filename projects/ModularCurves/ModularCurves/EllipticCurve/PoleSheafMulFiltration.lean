import ModularCurves.EllipticCurve.PoleSheaf

/-!
# Pole-sheaf multiplication and the pole filtration

Multiplication of pole sheaves commutes with the canonical inclusion in the
right tensor factor.
-/

open AlgebraicGeometry CategoryTheory MonoidalCategory

universe u v

namespace ModularCurves

noncomputable section

local instance poleSheafMulFiltrationMonoidalCategory (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem tensor_succ_mul
    {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {M N L P : D} (f : M ⊗ N ⟶ P) (unit : 𝟙_ D ⟶ L) :
    (𝟙 M ⊗ₘ ((ρ_ N).inv ≫ (𝟙 N ⊗ₘ unit))) ≫
        (α_ M N L).inv ≫ (f ⊗ₘ 𝟙 L) =
      f ≫ (ρ_ P).inv ≫ (𝟙 P ⊗ₘ unit) := by
  simp
  have hassoc :
      (M ⊗ N) ◁ unit =
        (α_ M N (𝟙_ D)).hom ≫ M ◁ N ◁ unit ≫ (α_ M N L).inv := by
    simp
  slice_lhs 2 4 =>
    rw [← hassoc]
  rw [← tensorHom_id f L]
  rw [whiskerLeft_comp_tensorHom]
  simpa using rightUnitor_inv_comp_tensorHom f unit

private theorem sectionPoleSheafSuccHom_comp_powerSucc
    {C S : Scheme.{u}} (π : C ⟶ S) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (n : ℕ) :
    sectionPoleSheafSuccHom π z hz n ≫
        eqToHom (sectionPoleSheafPower_succ π z hz n) =
      (ρ_ (sectionPoleSheafPower π z hz n)).inv ≫
        (𝟙 _ ⊗ₘ ((monoidalUnitObjIso C).hom ≫
          sectionPoleUnitHom π z hz)) := by
  rfl

private theorem sectionPoleSheafSuccHom_eq_raw
    {C S : Scheme.{u}} (π : C ⟶ S) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (n : ℕ) :
    sectionPoleSheafSuccHom π z hz n =
      (ρ_ (sectionPoleSheafPower π z hz n)).inv ≫
        (𝟙 _ ⊗ₘ ((monoidalUnitObjIso C).hom ≫
          sectionPoleUnitHom π z hz)) := by
  rfl

private theorem sectionPoleSheafMulHom_succ_comp_powerSucc
    {C S : Scheme.{u}} (π : C ⟶ S) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (m n : ℕ) :
    sectionPoleSheafMulHom π z hz m (n + 1) ≫
        eqToHom (sectionPoleSheafPower_succ π z hz (m + n)) =
      (α_ (sectionPoleSheafPower π z hz m)
        (sectionPoleSheafPower π z hz n)
        (sectionPoleSheaf π z hz)).inv ≫
        (sectionPoleSheafMulHom π z hz m n ⊗ₘ 𝟙 _) := by
  rfl

/-- Multiplication of pole sheaves commutes with the canonical inclusion in
the right factor. -/
theorem sectionPoleSheafMulHom_succ_right
    {C S : Scheme.{u}} (π : C ⟶ S) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (m n : ℕ) :
    (𝟙 (sectionPoleSheafPower π z hz m) ⊗ₘ
        sectionPoleSheafSuccHom π z hz n) ≫
        sectionPoleSheafMulHom π z hz m (n + 1) =
      sectionPoleSheafMulHom π z hz m n ≫
        sectionPoleSheafSuccHom π z hz (m + n) := by
  apply (cancel_mono
    (eqToHom (sectionPoleSheafPower_succ π z hz (m + n)))).mp
  simp only [Category.assoc]
  rw [sectionPoleSheafSuccHom_comp_powerSucc]
  rw [sectionPoleSheafMulHom_succ_comp_powerSucc]
  rw [sectionPoleSheafSuccHom_eq_raw]
  exact tensor_succ_mul (sectionPoleSheafMulHom π z hz m n)
    ((monoidalUnitObjIso C).hom ≫ sectionPoleUnitHom π z hz)

end


end ModularCurves

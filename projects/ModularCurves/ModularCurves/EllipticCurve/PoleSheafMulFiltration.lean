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

local instance poleSheafMulFiltrationSymmetricCategory (X : Scheme.{u}) :
    SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X

private theorem tensor_left_comp_braiding_comp_of_right
    {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    {M M' N P P' : D} (g : M ⟶ M')
    (mul : N ⊗ M ⟶ P) (mul' : N ⊗ M' ⟶ P') (h : P ⟶ P')
    (hright : (𝟙 N ⊗ₘ g) ≫ mul' = mul ≫ h) :
    (g ⊗ₘ 𝟙 N) ≫ (β_ M' N).hom ≫ mul' =
      (β_ M N).hom ≫ mul ≫ h := by
  calc
    _ = ((g ⊗ₘ 𝟙 N) ≫ (β_ M' N).hom) ≫ mul' :=
      (Category.assoc _ _ _).symm
    _ = ((β_ M N).hom ≫ (𝟙 N ⊗ₘ g)) ≫ mul' :=
      congrArg (fun k => k ≫ mul')
        (BraidedCategory.braiding_naturality g (𝟙 N))
    _ = (β_ M N).hom ≫ ((𝟙 N ⊗ₘ g) ≫ mul') :=
      Category.assoc _ _ _
    _ = (β_ M N).hom ≫ (mul ≫ h) :=
      congrArg (fun k => (β_ M N).hom ≫ k) hright
    _ = (β_ M N).hom ≫ mul ≫ h := rfl

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

/-- After braiding the left factor to the right, multiplication commutes with
the canonical inclusion in that factor. -/
theorem sectionPoleSheafMulHom_succ_left_swapped
    {C S : Scheme.{u}} (π : C ⟶ S) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (m n : ℕ) :
    (sectionPoleSheafSuccHom π z hz m ⊗ₘ
        𝟙 (sectionPoleSheafPower π z hz n)) ≫
      (β_ (sectionPoleSheafPower π z hz (m + 1))
        (sectionPoleSheafPower π z hz n)).hom ≫
      sectionPoleSheafMulHom π z hz n (m + 1) =
    (β_ (sectionPoleSheafPower π z hz m)
      (sectionPoleSheafPower π z hz n)).hom ≫
      sectionPoleSheafMulHom π z hz n m ≫
      sectionPoleSheafSuccHom π z hz (n + m) := by
  exact tensor_left_comp_braiding_comp_of_right
    (sectionPoleSheafSuccHom π z hz m)
    (sectionPoleSheafMulHom π z hz n m)
    (sectionPoleSheafMulHom π z hz n (m + 1))
    (sectionPoleSheafSuccHom π z hz (n + m))
    (sectionPoleSheafMulHom_succ_right π z hz n m)

end


end ModularCurves

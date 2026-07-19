import ModularCurves.EllipticCurve.PoleSheafBaseSectionsMul
import ModularCurves.EllipticCurve.PoleSheafMulFiltration

/-!
# Base-section multiplication and the pole filtration

Multiplication on global sections of pole sheaves commutes with the canonical
inclusion in the right factor.
-/

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

universe u v

namespace ModularCurves

noncomputable section

local instance poleSheafBaseSectionsMulFiltrationMonoidalCategory
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem comp_three_squares
    {D : Type u} [Category.{v} D]
    {A₀ A₁ B₀ B₁ C₀ C₁ E₀ E₁ : D}
    (f₀ : A₀ ⟶ A₁) (g₀ : A₀ ⟶ B₀) (g₁ : A₁ ⟶ B₁)
    (f₁ : B₀ ⟶ B₁) (h₀ : B₀ ⟶ C₀) (h₁ : B₁ ⟶ C₁)
    (f₂ : C₀ ⟶ C₁) (i₀ : C₀ ⟶ E₀) (i₁ : C₁ ⟶ E₁)
    (f₃ : E₀ ⟶ E₁)
    (hg : f₀ ≫ g₁ = g₀ ≫ f₁)
    (hh : f₁ ≫ h₁ = h₀ ≫ f₂)
    (hi : f₂ ≫ i₁ = i₀ ≫ f₃) :
    f₀ ≫ g₁ ≫ h₁ ≫ i₁ = g₀ ≫ h₀ ≫ i₀ ≫ f₃ := by
  calc
    _ = ((f₀ ≫ g₁) ≫ h₁) ≫ i₁ := by simp only [Category.assoc]
    _ = ((g₀ ≫ f₁) ≫ h₁) ≫ i₁ :=
      congrArg (fun k => (k ≫ h₁) ≫ i₁) hg
    _ = (g₀ ≫ (f₁ ≫ h₁)) ≫ i₁ :=
      congrArg (fun k => k ≫ i₁) (Category.assoc g₀ f₁ h₁)
    _ = (g₀ ≫ (h₀ ≫ f₂)) ≫ i₁ :=
      congrArg (fun k => (g₀ ≫ k) ≫ i₁) hh
    _ = g₀ ≫ (h₀ ≫ (f₂ ≫ i₁)) :=
      (Category.assoc g₀ (h₀ ≫ f₂) i₁).trans
        (congrArg (fun k => g₀ ≫ k) (Category.assoc h₀ f₂ i₁))
    _ = g₀ ≫ (h₀ ≫ (i₀ ≫ f₃)) :=
      congrArg (fun k => g₀ ≫ (h₀ ≫ k)) hi
    _ = g₀ ≫ h₀ ≫ i₀ ≫ f₃ := rfl

private theorem moduleCat_comp_four_apply
    {R : Type u} [CommRing R]
    {A B C D E : ModuleCat.{u} R}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (i : D ⟶ E) (x : A) :
    (f ≫ g ≫ h ≫ i) x = i (h (g (f x))) := by
  rfl

private theorem sheafifyValIso_hom_naturality
    {X : Scheme.{u}} {N N' : X.Modules} (g : N ⟶ N') :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map g.val ≫
        (Scheme.Modules.sheafifyValIso N').hom =
      (Scheme.Modules.sheafifyValIso N).hom ≫ g := by
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).counit.naturality g

private theorem sheafificationUnit_naturality
    {X : Scheme.{u}} {A B : X.PresheafOfModules} (f : A ⟶ B) :
    f ≫ (PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app B =
      (PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app A ≫
        ((PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map f).val := by
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.naturality f

private theorem monoidalTensorObjIso_inv_natural_right
    {X : Scheme.{u}} (M : X.Modules) {N N' : X.Modules} (g : N ⟶ N') :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
          (𝟙 M.val ⊗ₘ g.val) ≫
        (monoidalTensorObjIso M N').inv =
      (monoidalTensorObjIso M N).inv ≫ (𝟙 M ⊗ₘ g) := by
  letI : (PresheafOfModules.sheafificationW
      (𝟙 X.ringCatSheaf.obj)).IsMonoidal :=
    @PresheafOfModules.instSheafificationW_isMonoidal_commRingSheaf
      _ _ _ _ _ X.sheaf.obj X.ringCatSheaf.property
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let sh (A : X.PresheafOfModules) : X.Modules := L.obj A
  let μInv (A B : X.PresheafOfModules) : sh (A ⊗ B) ⟶ sh A ⊗ sh B :=
    (Localization.Monoidal.μ
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _) A B).inv
  let ε (A : X.Modules) : sh A.val ⟶ A :=
    (Scheme.Modules.sheafifyValIso A).hom
  let Lmap {A B : X.PresheafOfModules} (f : A ⟶ B) : sh A ⟶ sh B :=
    L.map f
  have hIso (A B : X.Modules) :
      (monoidalTensorObjIso A B).inv =
        μInv A.val B.val ≫ (ε A ⊗ₘ ε B) := by
    rfl
  have hμ :
      Lmap (M.val ◁ g.val) ≫ μInv M.val N'.val =
        μInv M.val N.val ≫ (sh M.val ◁ Lmap g.val) := by
    exact (Localization.Monoidal.μ_inv_natural_right
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      (PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
      (Iso.refl _) M.val g.val).symm
  have hε : Lmap g.val ≫ ε N' = ε N ≫ g := by
    exact sheafifyValIso_hom_naturality g
  rw [hIso M N', hIso M N, id_tensorHom, id_tensorHom]
  calc
    _ = (Lmap (M.val ◁ g.val) ≫ μInv M.val N'.val) ≫
          (ε M ⊗ₘ ε N') := (Category.assoc _ _ _).symm
    _ = (μInv M.val N.val ≫ (sh M.val ◁ Lmap g.val)) ≫
          (ε M ⊗ₘ ε N') := congrArg (fun k => k ≫ (ε M ⊗ₘ ε N')) hμ
    _ = μInv M.val N.val ≫
          ((sh M.val ◁ Lmap g.val) ≫ (ε M ⊗ₘ ε N')) :=
      Category.assoc _ _ _
    _ = μInv M.val N.val ≫ (ε M ⊗ₘ (Lmap g.val ≫ ε N')) := by
      rw [whiskerLeft_comp_tensorHom]
    _ = μInv M.val N.val ≫ (ε M ⊗ₘ (ε N ≫ g)) := by
      rw [hε]
    _ = μInv M.val N.val ≫ ((ε M ⊗ₘ ε N) ≫ (M ◁ g)) := by
      rw [tensorHom_comp_whiskerLeft]
    _ = (μInv M.val N.val ≫ (ε M ⊗ₘ ε N)) ≫ (M ◁ g) :=
      (Category.assoc _ _ _).symm

private theorem presheafTensorHom_tmul_baseSectionsMap
    {C S : Scheme.{u}} (π : C ⟶ S) (M N N' : C.Modules)
    (g : N ⟶ N')
    (x : Scheme.Modules.baseSections π M)
    (y : Scheme.Modules.baseSections π N) :
    (𝟙 M.val ⊗ₘ g.val).app (op (⊤ : C.Opens))
        (show ↑((M.val ⊗ N.val).obj (op (⊤ : C.Opens))) from
          (show Γ(M, (⊤ : C.Opens)) from x) ⊗ₜ
            (show Γ(N, (⊤ : C.Opens)) from y)) =
      (show ↑((M.val ⊗ N'.val).obj (op (⊤ : C.Opens))) from
        (show Γ(M, (⊤ : C.Opens)) from x) ⊗ₜ
          (show Γ(N', (⊤ : C.Opens)) from
            Scheme.Modules.baseSectionsMap π g y)) := by
  rfl

private theorem sectionPoleSheafMulPipeline_succ_right_appTop
    {C S : Scheme.{u}} (π : C ⟶ S) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (m n : ℕ) :
    (𝟙 (sectionPoleSheafPower π z hz m).val ⊗ₘ
        (sectionPoleSheafSuccHom π z hz n).val).app (op (⊤ : C.Opens)) ≫
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).unit.app
          ((sectionPoleSheafPower π z hz m).val ⊗
            (sectionPoleSheafPower π z hz (n + 1)).val)).app
              (op (⊤ : C.Opens)) ≫
      (monoidalTensorObjIso
        (sectionPoleSheafPower π z hz m)
        (sectionPoleSheafPower π z hz (n + 1))).inv.val.app
          (op (⊤ : C.Opens)) ≫
      (sectionPoleSheafMulHom π z hz m (n + 1)).val.app
        (op (⊤ : C.Opens)) =
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 C.ringCatSheaf.obj)).unit.app
        ((sectionPoleSheafPower π z hz m).val ⊗
          (sectionPoleSheafPower π z hz n).val)).app
            (op (⊤ : C.Opens)) ≫
      (monoidalTensorObjIso
        (sectionPoleSheafPower π z hz m)
        (sectionPoleSheafPower π z hz n)).inv.val.app
          (op (⊤ : C.Opens)) ≫
      (sectionPoleSheafMulHom π z hz m n).val.app
        (op (⊤ : C.Opens)) ≫
      (sectionPoleSheafSuccHom π z hz (m + n)).val.app
        (op (⊤ : C.Opens)) := by
  have hUnit := sheafificationUnit_naturality
    (𝟙 (sectionPoleSheafPower π z hz m).val ⊗ₘ
      (sectionPoleSheafSuccHom π z hz n).val)
  have hUnitTop :
      (𝟙 (sectionPoleSheafPower π z hz m).val ⊗ₘ
          (sectionPoleSheafSuccHom π z hz n).val).app (op (⊤ : C.Opens)) ≫
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 C.ringCatSheaf.obj)).unit.app
            ((sectionPoleSheafPower π z hz m).val ⊗
              (sectionPoleSheafPower π z hz (n + 1)).val)).app
                (op (⊤ : C.Opens)) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).unit.app
          ((sectionPoleSheafPower π z hz m).val ⊗
            (sectionPoleSheafPower π z hz n).val)).app
              (op (⊤ : C.Opens)) ≫
        (((PresheafOfModules.sheafification
          (𝟙 C.ringCatSheaf.obj)).map
            (𝟙 (sectionPoleSheafPower π z hz m).val ⊗ₘ
              (sectionPoleSheafSuccHom π z hz n).val)).val.app
                (op (⊤ : C.Opens))) := by
    exact congrArg (fun q => q.app (op (⊤ : C.Opens))) hUnit
  have hTensorTop :
      (((PresheafOfModules.sheafification
        (𝟙 C.ringCatSheaf.obj)).map
          (𝟙 (sectionPoleSheafPower π z hz m).val ⊗ₘ
            (sectionPoleSheafSuccHom π z hz n).val)).val.app
              (op (⊤ : C.Opens))) ≫
        (monoidalTensorObjIso
          (sectionPoleSheafPower π z hz m)
          (sectionPoleSheafPower π z hz (n + 1))).inv.val.app
            (op (⊤ : C.Opens)) =
      (monoidalTensorObjIso
        (sectionPoleSheafPower π z hz m)
        (sectionPoleSheafPower π z hz n)).inv.val.app
          (op (⊤ : C.Opens)) ≫
        (𝟙 (sectionPoleSheafPower π z hz m) ⊗ₘ
          sectionPoleSheafSuccHom π z hz n).val.app
            (op (⊤ : C.Opens)) := by
    exact congrArg (fun q => q.val.app (op (⊤ : C.Opens)))
      (monoidalTensorObjIso_inv_natural_right
        (sectionPoleSheafPower π z hz m)
        (sectionPoleSheafSuccHom π z hz n))
  have hMulTop :
      (𝟙 (sectionPoleSheafPower π z hz m) ⊗ₘ
          sectionPoleSheafSuccHom π z hz n).val.app
            (op (⊤ : C.Opens)) ≫
        (sectionPoleSheafMulHom π z hz m (n + 1)).val.app
          (op (⊤ : C.Opens)) =
      (sectionPoleSheafMulHom π z hz m n).val.app
          (op (⊤ : C.Opens)) ≫
        (sectionPoleSheafSuccHom π z hz (m + n)).val.app
          (op (⊤ : C.Opens)) := by
    exact congrArg (fun q => q.val.app (op (⊤ : C.Opens)))
      (sectionPoleSheafMulHom_succ_right π z hz m n)
  exact comp_three_squares _ _ _ _ _ _ _ _ _ _ hUnitTop hTensorTop hMulTop

/-- Base-section multiplication commutes with the canonical inclusion in the
right pole-filtration factor on pure tensors. -/
theorem sectionPoleSheafPower_baseSectionsMul_tmul_succ_right
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (m n : ℕ)
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz m))
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz n)) :
    sectionPoleSheafPower_baseSectionsMul z hz m (n + 1)
        (x ⊗ₜ Scheme.Modules.baseSectionsMap π
          (sectionPoleSheafSuccHom π z hz n) y) =
      Scheme.Modules.baseSectionsMap π
        (sectionPoleSheafSuccHom π z hz (m + n))
        (sectionPoleSheafPower_baseSectionsMul z hz m n (x ⊗ₜ y)) := by
  rw [sectionPoleSheafPower_baseSectionsMul_tmul]
  rw [sectionPoleSheafPower_baseSectionsMul_tmul]
  let f := (𝟙 (sectionPoleSheafPower π z hz m).val ⊗ₘ
    (sectionPoleSheafSuccHom π z hz n).val).app (op (⊤ : C.Opens))
  let η₀ := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 C.ringCatSheaf.obj)).unit.app
      ((sectionPoleSheafPower π z hz m).val ⊗
        (sectionPoleSheafPower π z hz n).val)).app (op (⊤ : C.Opens))
  let η₁ := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 C.ringCatSheaf.obj)).unit.app
      ((sectionPoleSheafPower π z hz m).val ⊗
        (sectionPoleSheafPower π z hz (n + 1)).val)).app (op (⊤ : C.Opens))
  let κ₀ := (monoidalTensorObjIso
    (sectionPoleSheafPower π z hz m)
    (sectionPoleSheafPower π z hz n)).inv.val.app (op (⊤ : C.Opens))
  let κ₁ := (monoidalTensorObjIso
    (sectionPoleSheafPower π z hz m)
    (sectionPoleSheafPower π z hz (n + 1))).inv.val.app (op (⊤ : C.Opens))
  let μ₀ := (sectionPoleSheafMulHom π z hz m n).val.app (op (⊤ : C.Opens))
  let μ₁ := (sectionPoleSheafMulHom π z hz m (n + 1)).val.app
    (op (⊤ : C.Opens))
  let s := (sectionPoleSheafSuccHom π z hz (m + n)).val.app
    (op (⊤ : C.Opens))
  let t := show ↑(((sectionPoleSheafPower π z hz m).val ⊗
    (sectionPoleSheafPower π z hz n).val).obj (op (⊤ : C.Opens))) from
      (show Γ(sectionPoleSheafPower π z hz m, (⊤ : C.Opens)) from x) ⊗ₜ
        (show Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens)) from y)
  have hTop : f ≫ η₁ ≫ κ₁ ≫ μ₁ = η₀ ≫ κ₀ ≫ μ₀ ≫ s :=
    sectionPoleSheafMulPipeline_succ_right_appTop π z hz m n
  have hApply := congrArg (fun q => q t) hTop
  have hNested : μ₁ (κ₁ (η₁ (f t))) = s (μ₀ (κ₀ (η₀ t))) :=
    (moduleCat_comp_four_apply
      (R := ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
        (op (⊤ : C.Opens)))) f η₁ κ₁ μ₁ t).symm.trans
      (hApply.trans (moduleCat_comp_four_apply
        (R := ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
          (op (⊤ : C.Opens)))) η₀ κ₀ μ₀ s t))
  have hInput : f t =
      (show ↑(((sectionPoleSheafPower π z hz m).val ⊗
        (sectionPoleSheafPower π z hz (n + 1)).val).obj
          (op (⊤ : C.Opens))) from
        (show Γ(sectionPoleSheafPower π z hz m, (⊤ : C.Opens)) from x) ⊗ₜ
          (show Γ(sectionPoleSheafPower π z hz (n + 1),
            (⊤ : C.Opens)) from Scheme.Modules.baseSectionsMap π
              (sectionPoleSheafSuccHom π z hz n) y)) :=
    presheafTensorHom_tmul_baseSectionsMap π
      (sectionPoleSheafPower π z hz m)
      (sectionPoleSheafPower π z hz n)
      (sectionPoleSheafPower π z hz (n + 1))
      (sectionPoleSheafSuccHom π z hz n) x y
  calc
    _ = μ₁ (κ₁ (η₁ (f t))) :=
      congrArg (fun q => μ₁ (κ₁ (η₁ q))) hInput.symm
    _ = s (μ₀ (κ₀ (η₀ t))) := hNested
    _ = _ := rfl

/-- After swapping the two pure-tensor factors, base-section multiplication
commutes with the canonical inclusion in the original left factor. -/
theorem sectionPoleSheafPower_baseSectionsMul_tmul_succ_left_swapped
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (m n : ℕ)
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz m))
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz n)) :
    sectionPoleSheafPower_baseSectionsMul z hz n (m + 1)
        (y ⊗ₜ Scheme.Modules.baseSectionsMap π
          (sectionPoleSheafSuccHom π z hz m) x) =
      Scheme.Modules.baseSectionsMap π
        (sectionPoleSheafSuccHom π z hz (n + m))
        (sectionPoleSheafPower_baseSectionsMul z hz n m (y ⊗ₜ x)) := by
  exact sectionPoleSheafPower_baseSectionsMul_tmul_succ_right
    z hz n m y x

end

end ModularCurves

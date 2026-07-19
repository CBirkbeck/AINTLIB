import ModularCurves.EllipticCurve.PoleSheaf
import ModularCurves.ForMathlib.SchemeModuleBaseCechZero

/-!
# Multiplication on base sections of pole sheaves

The sheaf-level multiplication `O(m[0]) tensor O(n[0]) -> O((m+n)[0])`
induces a base-linear multiplication on global sections. The construction uses the
existing comparison between the localized tensor and the explicit sheafified tensor.
-/

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u


namespace ModularCurves

noncomputable section

local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private noncomputable def sectionPoleSheafPower_baseSectionsMulTopHom
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (m n : ℕ) :
    (((sectionPoleSheafPower π z hz m).val ⊗
      (sectionPoleSheafPower π z hz n).val).obj (op (⊤ : C.Opens))) ⟶
        (sectionPoleSheafPower π z hz (m + n)).val.obj (op (⊤ : C.Opens)) :=
  ((PresheafOfModules.sheafificationAdjunction
      (𝟙 C.ringCatSheaf.obj)).unit.app
        ((sectionPoleSheafPower π z hz m).val ⊗
          (sectionPoleSheafPower π z hz n).val)).app (op (⊤ : C.Opens)) ≫
    (monoidalTensorObjIso
      (sectionPoleSheafPower π z hz m)
      (sectionPoleSheafPower π z hz n)).inv.val.app (op (⊤ : C.Opens)) ≫
    (sectionPoleSheafMulHom π z hz m n).val.app (op (⊤ : C.Opens))

private noncomputable def sectionPoleSheafPower_baseSectionsMulPure
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (m n : ℕ)
    (x : Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz m))
    (y : Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz n)) :
    Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz (m + n)) :=
  sectionPoleSheafPower_baseSectionsMulTopHom z hz m n (x ⊗ₜ y)

private theorem sectionPoleSheafPower_baseSectionsMulPure_add_left
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (m n : ℕ)
    (x x' : Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz m))
    (y : Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz n)) :
    sectionPoleSheafPower_baseSectionsMulPure z hz m n (x + x') y =
      sectionPoleSheafPower_baseSectionsMulPure z hz m n x y + sectionPoleSheafPower_baseSectionsMulPure z hz m n x' y := by
  letI : Module
      ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
      Γ(sectionPoleSheafPower π z hz m, (⊤ : C.Opens)) :=
    ModuleCat.isModule _
  letI : Module
      ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
      ↑((sectionPoleSheafPower π z hz m).val.obj (op (⊤ : C.Opens))) :=
    ModuleCat.isModule _
  letI : Module
      ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
      Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens)) :=
    ModuleCat.isModule _
  letI : Module
      ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
      ↑((sectionPoleSheafPower π z hz n).val.obj (op (⊤ : C.Opens))) :=
    ModuleCat.isModule _
  change sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
      (((show Γ(sectionPoleSheafPower π z hz m, (⊤ : C.Opens)) from x) +
        (show Γ(sectionPoleSheafPower π z hz m, (⊤ : C.Opens)) from x')) ⊗ₜ
          (show Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens)) from y)) =
    sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
        ((show Γ(sectionPoleSheafPower π z hz m, (⊤ : C.Opens)) from x) ⊗ₜ
          (show Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens)) from y)) +
      sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
        ((show Γ(sectionPoleSheafPower π z hz m, (⊤ : C.Opens)) from x') ⊗ₜ
          (show Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens)) from y))
  calc
    _ = sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
        (((show Γ(sectionPoleSheafPower π z hz m, (⊤ : C.Opens)) from x) ⊗ₜ
          (show Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens)) from y)) +
        ((show Γ(sectionPoleSheafPower π z hz m, (⊤ : C.Opens)) from x') ⊗ₜ
          (show Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens)) from y))) :=
      congrArg (sectionPoleSheafPower_baseSectionsMulTopHom z hz m n)
        (TensorProduct.add_tmul
          (R := (C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
          (show Γ(sectionPoleSheafPower π z hz m, (⊤ : C.Opens)) from x)
          (show Γ(sectionPoleSheafPower π z hz m, (⊤ : C.Opens)) from x')
          (show Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens)) from y))
    _ = _ := (sectionPoleSheafPower_baseSectionsMulTopHom z hz m n).hom.map_add _ _

private theorem sectionPoleSheafPower_baseSectionsMulPure_smul_left
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (m n : ℕ)
    (a : Γ(S, (⊤ : S.Opens)))
    (x : Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz m))
    (y : Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz n)) :
    sectionPoleSheafPower_baseSectionsMulPure z hz m n (a • x) y =
      a • sectionPoleSheafPower_baseSectionsMulPure z hz m n x y := by
  letI : Module
      ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
      Γ(sectionPoleSheafPower π z hz m, (⊤ : C.Opens)) :=
    ModuleCat.isModule _
  letI : Module
      ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
      ↑((sectionPoleSheafPower π z hz m).val.obj (op (⊤ : C.Opens))) :=
    ModuleCat.isModule _
  letI : Module
      ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
      Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens)) :=
    ModuleCat.isModule _
  letI : Module
      ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
      ↑((sectionPoleSheafPower π z hz n).val.obj (op (⊤ : C.Opens))) :=
    ModuleCat.isModule _
  letI : Module
      ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
      Γ(sectionPoleSheafPower π z hz (m + n), (⊤ : C.Opens)) :=
    ModuleCat.isModule _
  letI : Module
      ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
      ↑((sectionPoleSheafPower π z hz (m + n)).val.obj (op (⊤ : C.Opens))) :=
    ModuleCat.isModule _
  change sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
      ((show ↑((sectionPoleSheafPower π z hz m).val.obj (op (⊤ : C.Opens))) from
        a • (show Scheme.Modules.baseSections π
          (sectionPoleSheafPower π z hz m) from x)) ⊗ₜ
        (show ↑((sectionPoleSheafPower π z hz n).val.obj (op (⊤ : C.Opens))) from y)) =
    (show ↑((sectionPoleSheafPower π z hz (m + n)).val.obj (op (⊤ : C.Opens))) from
      a • (show Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz (m + n)) from
          sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
            ((show ↑((sectionPoleSheafPower π z hz m).val.obj
                (op (⊤ : C.Opens))) from x) ⊗ₜ
              (show ↑((sectionPoleSheafPower π z hz n).val.obj
                (op (⊤ : C.Opens))) from y))))
  have htarget :
      (show ↑((sectionPoleSheafPower π z hz (m + n)).val.obj
          (op (⊤ : C.Opens))) from
        a • (show Scheme.Modules.baseSections π
          (sectionPoleSheafPower π z hz (m + n)) from
            sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
              ((show ↑((sectionPoleSheafPower π z hz m).val.obj
                  (op (⊤ : C.Opens))) from x) ⊗ₜ
                (show ↑((sectionPoleSheafPower π z hz n).val.obj
                  (op (⊤ : C.Opens))) from y)))) =
        (show ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
            (op (⊤ : C.Opens))) from π.appTop.hom a) •
          sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
            ((show ↑((sectionPoleSheafPower π z hz m).val.obj
                (op (⊤ : C.Opens))) from x) ⊗ₜ
              (show ↑((sectionPoleSheafPower π z hz n).val.obj
                (op (⊤ : C.Opens))) from y)) :=
    Scheme.Modules.baseSections_smul π
      (sectionPoleSheafPower π z hz (m + n)) a
        (sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
          ((show ↑((sectionPoleSheafPower π z hz m).val.obj
              (op (⊤ : C.Opens))) from x) ⊗ₜ
            (show ↑((sectionPoleSheafPower π z hz n).val.obj
              (op (⊤ : C.Opens))) from y)))
  calc
    _ = sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
        (((show ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
            (op (⊤ : C.Opens))) from π.appTop.hom a) •
          (show ↑((sectionPoleSheafPower π z hz m).val.obj
            (op (⊤ : C.Opens))) from x)) ⊗ₜ
            (show ↑((sectionPoleSheafPower π z hz n).val.obj
              (op (⊤ : C.Opens))) from y)) :=
      congrArg (fun x' => sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
        (x' ⊗ₜ (show ↑((sectionPoleSheafPower π z hz n).val.obj
          (op (⊤ : C.Opens))) from y)))
          (Scheme.Modules.baseSections_smul π
            (sectionPoleSheafPower π z hz m) a x)
    _ = sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
        (show TensorProduct
            ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
            ↑((sectionPoleSheafPower π z hz m).val.obj (op (⊤ : C.Opens)))
            ↑((sectionPoleSheafPower π z hz n).val.obj (op (⊤ : C.Opens))) from
          (show ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
              (op (⊤ : C.Opens))) from π.appTop.hom a) •
            ((show ↑((sectionPoleSheafPower π z hz m).val.obj
                (op (⊤ : C.Opens))) from x) ⊗ₜ
              (show ↑((sectionPoleSheafPower π z hz n).val.obj
                (op (⊤ : C.Opens))) from y))) :=
      congrArg (sectionPoleSheafPower_baseSectionsMulTopHom z hz m n)
        (TensorProduct.smul_tmul'
          (R := (C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
          (show ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
            (op (⊤ : C.Opens))) from π.appTop.hom a)
          (show ↑((sectionPoleSheafPower π z hz m).val.obj
            (op (⊤ : C.Opens))) from x)
          (show ↑((sectionPoleSheafPower π z hz n).val.obj
            (op (⊤ : C.Opens))) from y)).symm
    _ = (show ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
          (op (⊤ : C.Opens))) from π.appTop.hom a) •
        sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
        ((show ↑((sectionPoleSheafPower π z hz m).val.obj
            (op (⊤ : C.Opens))) from x) ⊗ₜ
          (show ↑((sectionPoleSheafPower π z hz n).val.obj
            (op (⊤ : C.Opens))) from y)) :=
      (sectionPoleSheafPower_baseSectionsMulTopHom z hz m n).hom.map_smul _ _
    _ = _ := htarget.symm

private theorem sectionPoleSheafPower_baseSectionsMulPure_add_right
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (m n : ℕ)
    (x : Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz m))
    (y y' : Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz n)) :
    sectionPoleSheafPower_baseSectionsMulPure z hz m n x (y + y') =
      sectionPoleSheafPower_baseSectionsMulPure z hz m n x y + sectionPoleSheafPower_baseSectionsMulPure z hz m n x y' := by
  letI : Module
      ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
      Γ(sectionPoleSheafPower π z hz m, (⊤ : C.Opens)) :=
    ModuleCat.isModule _
  letI : Module
      ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
      Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens)) :=
    ModuleCat.isModule _
  change sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
      ((show Γ(sectionPoleSheafPower π z hz m, (⊤ : C.Opens)) from x) ⊗ₜ
        ((show Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens)) from y) +
          (show Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens)) from y'))) =
    sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
        ((show Γ(sectionPoleSheafPower π z hz m, (⊤ : C.Opens)) from x) ⊗ₜ
          (show Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens)) from y)) +
      sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
        ((show Γ(sectionPoleSheafPower π z hz m, (⊤ : C.Opens)) from x) ⊗ₜ
          (show Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens)) from y'))
  calc
    _ = sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
        (((show Γ(sectionPoleSheafPower π z hz m, (⊤ : C.Opens)) from x) ⊗ₜ
          (show Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens)) from y)) +
        ((show Γ(sectionPoleSheafPower π z hz m, (⊤ : C.Opens)) from x) ⊗ₜ
          (show Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens)) from y'))) :=
      congrArg (sectionPoleSheafPower_baseSectionsMulTopHom z hz m n)
        (TensorProduct.tmul_add
          (R := (C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
          (show Γ(sectionPoleSheafPower π z hz m, (⊤ : C.Opens)) from x)
          (show Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens)) from y)
          (show Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens)) from y'))
    _ = _ := (sectionPoleSheafPower_baseSectionsMulTopHom z hz m n).hom.map_add _ _

private theorem sectionPoleSheafPower_baseSectionsMulPure_smul_right
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (m n : ℕ)
    (a : Γ(S, (⊤ : S.Opens)))
    (x : Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz m))
    (y : Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz n)) :
    sectionPoleSheafPower_baseSectionsMulPure z hz m n x (a • y) =
      a • sectionPoleSheafPower_baseSectionsMulPure z hz m n x y := by
  letI : Module
      ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
      Γ(sectionPoleSheafPower π z hz m, (⊤ : C.Opens)) :=
    ModuleCat.isModule _
  letI : Module
      ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
      ↑((sectionPoleSheafPower π z hz m).val.obj (op (⊤ : C.Opens))) :=
    ModuleCat.isModule _
  letI : Module
      ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
      Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens)) :=
    ModuleCat.isModule _
  letI : Module
      ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
      ↑((sectionPoleSheafPower π z hz n).val.obj (op (⊤ : C.Opens))) :=
    ModuleCat.isModule _
  letI : Module
      ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
      Γ(sectionPoleSheafPower π z hz (m + n), (⊤ : C.Opens)) :=
    ModuleCat.isModule _
  letI : Module
      ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
      ↑((sectionPoleSheafPower π z hz (m + n)).val.obj (op (⊤ : C.Opens))) :=
    ModuleCat.isModule _
  change sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
      ((show ↑((sectionPoleSheafPower π z hz m).val.obj (op (⊤ : C.Opens))) from x) ⊗ₜ
        (show ↑((sectionPoleSheafPower π z hz n).val.obj (op (⊤ : C.Opens))) from
          a • (show Scheme.Modules.baseSections π
            (sectionPoleSheafPower π z hz n) from y))) =
    (show ↑((sectionPoleSheafPower π z hz (m + n)).val.obj (op (⊤ : C.Opens))) from
      a • (show Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz (m + n)) from
          sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
            ((show ↑((sectionPoleSheafPower π z hz m).val.obj
                (op (⊤ : C.Opens))) from x) ⊗ₜ
              (show ↑((sectionPoleSheafPower π z hz n).val.obj
                (op (⊤ : C.Opens))) from y))))
  have htarget :
      (show ↑((sectionPoleSheafPower π z hz (m + n)).val.obj
          (op (⊤ : C.Opens))) from
        a • (show Scheme.Modules.baseSections π
          (sectionPoleSheafPower π z hz (m + n)) from
            sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
              ((show ↑((sectionPoleSheafPower π z hz m).val.obj
                  (op (⊤ : C.Opens))) from x) ⊗ₜ
                (show ↑((sectionPoleSheafPower π z hz n).val.obj
                  (op (⊤ : C.Opens))) from y)))) =
        (show ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
            (op (⊤ : C.Opens))) from π.appTop.hom a) •
          sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
            ((show ↑((sectionPoleSheafPower π z hz m).val.obj
                (op (⊤ : C.Opens))) from x) ⊗ₜ
              (show ↑((sectionPoleSheafPower π z hz n).val.obj
                (op (⊤ : C.Opens))) from y)) :=
    Scheme.Modules.baseSections_smul π
      (sectionPoleSheafPower π z hz (m + n)) a
        (sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
          ((show ↑((sectionPoleSheafPower π z hz m).val.obj
              (op (⊤ : C.Opens))) from x) ⊗ₜ
            (show ↑((sectionPoleSheafPower π z hz n).val.obj
              (op (⊤ : C.Opens))) from y)))
  calc
    _ = sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
        ((show ↑((sectionPoleSheafPower π z hz m).val.obj
            (op (⊤ : C.Opens))) from x) ⊗ₜ
          ((show ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
              (op (⊤ : C.Opens))) from π.appTop.hom a) •
            (show ↑((sectionPoleSheafPower π z hz n).val.obj
              (op (⊤ : C.Opens))) from y))) :=
      congrArg (fun y' => sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
        ((show ↑((sectionPoleSheafPower π z hz m).val.obj
          (op (⊤ : C.Opens))) from x) ⊗ₜ y'))
          (Scheme.Modules.baseSections_smul π
            (sectionPoleSheafPower π z hz n) a y)
    _ = sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
        (show TensorProduct
            ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
            ↑((sectionPoleSheafPower π z hz m).val.obj (op (⊤ : C.Opens)))
            ↑((sectionPoleSheafPower π z hz n).val.obj (op (⊤ : C.Opens))) from
          (show ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
              (op (⊤ : C.Opens))) from π.appTop.hom a) •
            ((show ↑((sectionPoleSheafPower π z hz m).val.obj
                (op (⊤ : C.Opens))) from x) ⊗ₜ
              (show ↑((sectionPoleSheafPower π z hz n).val.obj
                (op (⊤ : C.Opens))) from y))) :=
      congrArg (sectionPoleSheafPower_baseSectionsMulTopHom z hz m n)
        (TensorProduct.tmul_smul
          (R := (C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op (⊤ : C.Opens)))
          (show ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
            (op (⊤ : C.Opens))) from π.appTop.hom a)
          (show ↑((sectionPoleSheafPower π z hz m).val.obj
            (op (⊤ : C.Opens))) from x)
          (show ↑((sectionPoleSheafPower π z hz n).val.obj
            (op (⊤ : C.Opens))) from y))
    _ = (show ↑((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
          (op (⊤ : C.Opens))) from π.appTop.hom a) •
        sectionPoleSheafPower_baseSectionsMulTopHom z hz m n
          ((show ↑((sectionPoleSheafPower π z hz m).val.obj
              (op (⊤ : C.Opens))) from x) ⊗ₜ
            (show ↑((sectionPoleSheafPower π z hz n).val.obj
              (op (⊤ : C.Opens))) from y)) :=
      (sectionPoleSheafPower_baseSectionsMulTopHom z hz m n).hom.map_smul _ _
    _ = _ := htarget.symm

/-- Multiplication of pole sheaves induces a base-linear multiplication on global sections. -/
noncomputable def sectionPoleSheafPower_baseSectionsMul
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (m n : ℕ) :
    Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz m) ⊗
        Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz n) ⟶
      Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz (m + n)) :=
  ModuleCat.MonoidalCategory.tensorLift
    (sectionPoleSheafPower_baseSectionsMulPure z hz m n)
    (sectionPoleSheafPower_baseSectionsMulPure_add_left z hz m n)
    (sectionPoleSheafPower_baseSectionsMulPure_smul_left z hz m n)
    (sectionPoleSheafPower_baseSectionsMulPure_add_right z hz m n)
    (sectionPoleSheafPower_baseSectionsMulPure_smul_right z hz m n)

private theorem sectionPoleSheafPower_baseSectionsMul_tmul_aux
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (m n : ℕ)
    (x : Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz m))
    (y : Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz n)) :
    sectionPoleSheafPower_baseSectionsMul z hz m n (x ⊗ₜ y) = sectionPoleSheafPower_baseSectionsMulPure z hz m n x y := by
  exact ModuleCat.MonoidalCategory.tensorLift_tmul _ _ _ _ _ x y

/-- Base-section multiplication evaluates a pure tensor through the sheafification unit,
the canonical tensor comparison, and multiplication of pole sheaves. -/
theorem sectionPoleSheafPower_baseSectionsMul_tmul
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (m n : ℕ)
    (x : Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz m))
    (y : Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz n)) :
    sectionPoleSheafPower_baseSectionsMul z hz m n (x ⊗ₜ y) =
      (sectionPoleSheafMulHom π z hz m n).val.app (op (⊤ : C.Opens))
        ((monoidalTensorObjIso
          (sectionPoleSheafPower π z hz m)
          (sectionPoleSheafPower π z hz n)).inv.val.app (op (⊤ : C.Opens))
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 C.ringCatSheaf.obj)).unit.app
              ((sectionPoleSheafPower π z hz m).val ⊗
                (sectionPoleSheafPower π z hz n).val)).app
                  (op (⊤ : C.Opens)) (x ⊗ₜ y))) := by
  change sectionPoleSheafPower_baseSectionsMul z hz m n (x ⊗ₜ y) = sectionPoleSheafPower_baseSectionsMulPure z hz m n x y
  exact sectionPoleSheafPower_baseSectionsMul_tmul_aux z hz m n x y

/-- In compatible local tensor-power coordinates, the coefficient of a pure-tensor
pole product is the product of the two coefficients. -/
theorem localTrivializationCoefficient_sectionPoleSheafPower_baseSectionsMul_tmul
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (U : C.affineOpens)
    (e : (sectionPoleSheaf π z hz).restrict U.1.ι ≅
      Scheme.Modules.unitObj U.1.toScheme) (m n : ℕ)
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz m))
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz n)) :
    localTrivializationCoefficient
        (sectionPoleSheafPower π z hz (m + n)) U
        (sectionPoleSheafPowerTrivialization z hz U.1 e (m + n))
        (sectionPoleSheafPower_baseSectionsMul z hz m n (x ⊗ₜ y)) =
      localTrivializationCoefficient
          (sectionPoleSheafPower π z hz m) U
          (sectionPoleSheafPowerTrivialization z hz U.1 e m) x *
        localTrivializationCoefficient
          (sectionPoleSheafPower π z hz n) U
          (sectionPoleSheafPowerTrivialization z hz U.1 e n) y := by
  unfold localTrivializationCoefficient
  rw [← affineOpenAmbientSection_mul]
  congr 1
  unfold localTrivializationTopSection
  rw [sectionPoleSheafPower_baseSectionsMul_tmul]
  erw [localTrivializationRestriction_map]
  let P := sectionPoleSheafPower π z hz m
  let Q := sectionPoleSheafPower π z hz n
  let q : Γ(P ⊗ Q, (⊤ : C.Opens)) :=
    (monoidalTensorObjIso P Q).inv.val.app (.op (⊤ : C.Opens))
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).unit.app (P.val ⊗ Q.val)).app
          (.op (⊤ : C.Opens))
            ((show Γ(P, (⊤ : C.Opens)) from x) ⊗ₜ
              (show Γ(Q, (⊤ : C.Opens)) from y)))
  change
    (sectionPoleSheafPowerTrivialization z hz U.1 e (m + n)).hom.val.app
      (.op (⊤ : U.1.toScheme.Opens))
        (((Scheme.Modules.restrictFunctor U.1.ι).map
          (sectionPoleSheafMulHom π z hz m n)).val.app
            (.op (⊤ : U.1.toScheme.Opens))
              (localTrivializationRestriction (P ⊗ Q) U q)) = _
  have hcoord := sectionPoleSheafMulHom_restrict_comp_powerTrivialization
    z hz U.1 e m n
  have hcoordTop := congrArg
    (fun k ↦ k.val.app (.op (⊤ : U.1.toScheme.Opens))) hcoord
  have hcoordApply := ConcreteCategory.congr_hom hcoordTop
    (localTrivializationRestriction (P ⊗ Q) U q)
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hcoordApply
  rw [hcoordApply]
  exact
    sectionPoleSheafPowerMulTrivialization_localTrivializationRestriction_tmul
      z hz U e m n x y


end

end ModularCurves

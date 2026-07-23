import ModularCurves.EllipticCurve.PoleSheafUnitBaseChange

/-!
# Base change for the pole-sheaf filtration

The canonical inclusions `𝒪_C(n[0]) → 𝒪_C((n+1)[0])` commute with arbitrary base change.
Together with base change for the pole unit, this keeps the literal section `1` compatible in
all pole modules used to construct local Weierstrass coordinates.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory

noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

namespace ModularCurves

private theorem sectionPoleMonoidalUnitHom_baseChangeT
    {C S T : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) :
    let g := pullback.fst π t
    let πT := pullback.snd π t
    let zT := sectionBaseChange z hz t
    let hzT := sectionBaseChange_snd z hz t
    letI : (Scheme.Modules.pullback g).Monoidal :=
      Scheme.Modules.pullbackMonoidal g
    (Scheme.Modules.pullback g).map
          ((monoidalUnitObjIso C).hom ≫ sectionPoleUnitHom π z hz) ≫
        (sectionPoleSheafBaseChangeIso hsm z hz t).hom =
      Functor.OplaxMonoidal.η (Scheme.Modules.pullback g) ≫
        (monoidalUnitObjIso (pullback π t)).hom ≫
        sectionPoleUnitHom πT zT hzT := by
  dsimp only
  letI : (Scheme.Modules.pullback (pullback.fst π t)).Monoidal :=
    Scheme.Modules.pullbackMonoidal (pullback.fst π t)
  rw [Functor.map_comp]
  rw [Category.assoc]
  rw [sectionPoleUnitHom_baseChange]
  rw [← Category.assoc]
  have hunit := Scheme.Modules.pullback_monoidalUnitObjIso
    (pullback.fst π t)
  have hunitHom := congrArg Iso.hom hunit
  change Functor.OplaxMonoidal.η
        (Scheme.Modules.pullback (pullback.fst π t)) ≫
      (monoidalUnitObjIso (pullback π t)).hom =
    (Scheme.Modules.pullback (pullback.fst π t)).map
        (monoidalUnitObjIso C).hom ≫
      (Scheme.Modules.pullbackUnitIso (pullback.fst π t)).hom at hunitHom
  rw [← hunitHom]
  simp only [Category.assoc]

private theorem monoidalSuccHom_naturalityT
    {C D : Type u} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal]
    {A L : C} {A' L' : D}
    (eA : F.obj A ≅ A') (eL : F.obj L ≅ L')
    (u : (𝟙_ C) ⟶ L) (u' : (𝟙_ D) ⟶ L')
    (hu : F.map u ≫ eL.hom = Functor.OplaxMonoidal.η F ≫ u') :
    F.map ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ u)) ≫
        Functor.OplaxMonoidal.δ F A L ≫
        (eA.hom ⊗ₘ eL.hom) =
      eA.hom ≫ (ρ_ A').inv ≫ (𝟙 A' ⊗ₘ u') := by
  rw [F.map_comp]
  rw [Functor.Monoidal.map_rightUnitor_inv]
  rw [Functor.Monoidal.map_tensor]
  rw [F.map_id]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
  have htensor :
      (𝟙 (F.obj A) ⊗ₘ F.map u) ≫ (eA.hom ⊗ₘ eL.hom) =
        (eA.hom ⊗ₘ Functor.OplaxMonoidal.η F) ≫
          (𝟙 A' ⊗ₘ u') := by
    calc
      _ = (𝟙 (F.obj A) ≫ eA.hom) ⊗ₘ
          (F.map u ≫ eL.hom) :=
        tensorHom_comp_tensorHom (𝟙 (F.obj A)) (F.map u)
          eA.hom eL.hom
      _ = (eA.hom ⊗ₘ
          (Functor.OplaxMonoidal.η F ≫ u')) := by
        rw [Category.id_comp, hu]
      _ = (eA.hom ⊗ₘ Functor.OplaxMonoidal.η F) ≫
          (𝟙 A' ⊗ₘ u') := by
        simpa only [Category.comp_id] using
          (tensorHom_comp_tensorHom eA.hom
            (Functor.OplaxMonoidal.η F) (𝟙 A') u').symm
  rw [htensor]
  have hunit :
      (F.obj A ◁ Functor.LaxMonoidal.ε F) ≫
          (eA.hom ⊗ₘ Functor.OplaxMonoidal.η F) =
        eA.hom ⊗ₘ 𝟙 (𝟙_ D) := by
    rw [← id_tensorHom]
    rw [tensorHom_comp_tensorHom]
    rw [Category.id_comp]
    rw [Functor.Monoidal.ε_η]
  calc
    _ = (ρ_ (F.obj A)).inv ≫
        (eA.hom ⊗ₘ 𝟙 (𝟙_ D)) ≫ (𝟙 A' ⊗ₘ u') := by
      simpa only [Category.assoc, tensorHom_id] using congrArg
        (fun k => (ρ_ (F.obj A)).inv ≫ k ≫ (𝟙 A' ⊗ₘ u')) hunit
    _ = _ := by
      simpa only [Category.assoc, tensorHom_id] using congrArg
        (fun k => k ≫ (𝟙 A' ⊗ₘ u'))
        (rightUnitor_inv_naturality eA.hom).symm

/-- The canonical pole-filtration inclusion is preserved by arbitrary base change. -/
theorem sectionPoleSheafSuccHom_baseChange
    {C S T : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) (n : ℕ) :
    let g := pullback.fst π t
    let πT := pullback.snd π t
    let zT := sectionBaseChange z hz t
    let hzT := sectionBaseChange_snd z hz t
    (Scheme.Modules.pullback g).map
          (sectionPoleSheafSuccHom π z hz n) ≫
        (sectionPoleSheafPowerBaseChangeIso hsm z hz t (n + 1)).hom =
      (sectionPoleSheafPowerBaseChangeIso hsm z hz t n).hom ≫
        sectionPoleSheafSuccHom πT zT hzT n := by
  dsimp only
  let g := pullback.fst π t
  let πT := pullback.snd π t
  let zT := sectionBaseChange z hz t
  let hzT := sectionBaseChange_snd z hz t
  let A := sectionPoleSheafPower π z hz n
  let L := sectionPoleSheaf π z hz
  let A' := sectionPoleSheafPower πT zT hzT n
  let L' := sectionPoleSheaf πT zT hzT
  let eA := sectionPoleSheafPowerBaseChangeIso hsm z hz t n
  let eL := sectionPoleSheafBaseChangeIso hsm z hz t
  let u := (monoidalUnitObjIso C).hom ≫ sectionPoleUnitHom π z hz
  let u' := (monoidalUnitObjIso (pullback π t)).hom ≫
    sectionPoleUnitHom πT zT hzT
  letI : IsSeparated πT := inferInstance
  letI : (Scheme.Modules.pullback g).Monoidal :=
    Scheme.Modules.pullbackMonoidal g
  have hu : (Scheme.Modules.pullback g).map u ≫ eL.hom =
      Functor.OplaxMonoidal.η (Scheme.Modules.pullback g) ≫ u' := by
    simpa only [g, πT, zT, hzT, eL, u, u', Category.assoc] using
      sectionPoleMonoidalUnitHom_baseChangeT hsm z hz t
  change (Scheme.Modules.pullback g).map
        ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ u)) ≫
      Functor.OplaxMonoidal.δ (Scheme.Modules.pullback g) A L ≫
      (eA.hom ⊗ₘ eL.hom) =
    eA.hom ≫ (ρ_ A').inv ≫ (𝟙 A' ⊗ₘ u')
  exact monoidalSuccHom_naturalityT
    (Scheme.Modules.pullback g) eA eL u u' hu

end ModularCurves

/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Epimorphisms of scheme modules on open covers

This file proves that epimorphisms of scheme modules can be checked after
restriction to an open cover.
-/

open CategoryTheory Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme.Modules

private theorem hom_ext_of_restrictFunctor_map_eq_of_iSup_eq_top
    {X : Scheme.{u}} {ι : Type v} (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) {M N : X.Modules} {g h : M ⟶ N}
    (hgh : ∀ i, (restrictFunctor (U i).ι).map g =
      (restrictFunctor (U i).ι).map h) :
    g = h := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  ext s
  apply TopCat.Presheaf.section_ext
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj N) V.unop
  intro x hx
  have hxcover : x ∈ ⨆ i, U i := by
    rw [hU]
    trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hxcover
  let y : (U i).toScheme := ⟨x, hxi⟩
  let e := restrictStalkNatIso (U i).ι y
  let F := restrictFunctor (U i).ι ⋙ toPresheaf (U i).toScheme ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
  let G := toPresheaf X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} ((U i).ι y)
  have hrestrictStalk : F.map g = F.map h := by
    exact congrArg
      (fun k : (restrictFunctor (U i).ι).obj M ⟶
          (restrictFunctor (U i).ι).obj N ↦
        (toPresheaf (U i).toScheme ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map k) (hgh i)
  have hstalk : G.map g = G.map h := by
    dsimp only [G]
    rw [← cancel_epi (e.hom.app M)]
    rw [← e.hom.naturality g, ← e.hom.naturality h]
    change F.map g ≫ e.hom.app N = F.map h ≫ e.hom.app N
    exact congrArg (fun k ↦ k ≫ e.hom.app N) hrestrictStalk
  dsimp only [G, y, toPresheaf, toPresheafOfModules,
    Functor.comp_map] at hstalk
  have hxy : (U i).ι y = x := rfl
  rw [hxy] at hstalk
  have happly := ConcreteCategory.congr_hom hstalk
    (M.presheaf.germ V.unop x hx s)
  let gp := (toPresheaf X).map g
  let hp := (toPresheaf X).map h
  have hgerm := TopCat.Presheaf.stalkFunctor_map_germ_apply
    V.unop x hx gp s
  have hhgerm := TopCat.Presheaf.stalkFunctor_map_germ_apply
    V.unop x hx hp s
  exact hgerm.symm.trans (happly.trans hhgerm)

/-- A morphism of scheme modules is an epimorphism if its restrictions to an
open cover are epimorphisms. -/
theorem epi_of_restrictFunctor_map_epi_of_iSup_eq_top
    {X : Scheme.{u}} {ι : Type v} (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ i, Epi ((restrictFunctor (U i).ι).map f)) :
    Epi f := by
  constructor
  intro Z g h hcomp
  apply hom_ext_of_restrictFunctor_map_eq_of_iSup_eq_top U hU
  intro i
  letI : Epi ((restrictFunctor (U i).ι).map f) := hf i
  rw [← cancel_epi ((restrictFunctor (U i).ι).map f)]
  rw [← Functor.map_comp, ← Functor.map_comp, hcomp]

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import ModularCurves.ForMathlib.SchemeModuleBaseCechBasic
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent
import ModularCurves.ForMathlib.SchemeModuleSheaf

/-!
# Exact sequences of base-linear Cech complexes

This file proves that a short exact sequence of quasicoherent scheme modules remains short exact
after taking base-linear sections over an affine open. The finite affine Cech-complex consequence
is assembled degreewise below.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- A short exact sequence of quasicoherent scheme modules remains short exact after taking
base-linear sections over an affine open. -/
theorem _root_.CategoryTheory.ShortComplex.ShortExact.map_baseModulePresheafFunctor_eval_of_isAffineOpen
    {X S : Scheme.{u}} (π : X ⟶ S)
    {T : ShortComplex X.Modules} (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    (T.map (baseModulePresheafFunctor π ⋙
      (CategoryTheory.evaluation X.Opensᵒᵖ
        (ModuleCat.{u} Γ(S, (⊤ : S.Opens)))).obj (op U))).ShortExact := by
  let A := T.map (baseModulePresheafFunctor π ⋙
    (CategoryTheory.evaluation X.Opensᵒᵖ
      (ModuleCat.{u} Γ(S, (⊤ : S.Opens)))).obj (op U))
  let K := T.map (toSheaf X)
  have hK : K.ShortExact := hT.map_of_exact (toSheaf X)
  haveI : Mono T.f := hT.mono_f
  haveI : Epi T.g := hT.epi_g
  haveI : Mono A.f := by
    rw [ModuleCat.mono_iff_injective]
    change Function.Injective (K.f.hom.app (op U)).hom
    haveI : Mono K.f := hK.mono_f
    haveI : Mono K.f.hom := by
      change Mono ((TopCat.Sheaf.forget AddCommGrpCat X).map K.f)
      infer_instance
    haveI : Mono (K.f.hom.app (op U)) := by infer_instance
    exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  haveI : Epi A.g := by
    rw [ModuleCat.epi_iff_surjective]
    exact isQuasicoherent_app_surjective_of_epi U hU T.g
  refine ShortComplex.ShortExact.mk ?_
  change A.Exact
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  have hy' : K.g.hom.app (op U) y = 0 := hy
  obtain ⟨x, hx⟩ := TopCat.Sheaf.sections_exact_of_left_exact
    (U := U) hK.exact hK.mono_f y hy'
  exact ⟨x, hx⟩

end

end AlgebraicGeometry.Scheme.Modules

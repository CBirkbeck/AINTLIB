/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.AffineModuleCechBaseChange
import ModularCurves.ForMathlib.CochainComplexBaseChangeExactAt
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechFunctor

/-!
# Exactness of ordered Cech complexes after affine base change

This file transports exactness of algebraically base-changed ordered Cech
differentials to the ordered Cech complex of an isomorphic pulled-back module.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Algebraic base change of two consecutive ordered Cech differentials is
exact if and only if the corresponding differentials for an isomorphic
pulled-back module are exact. -/
theorem orderedBaseCechComplex_baseChange_exact_iff_of_iso
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i))
    [X.IsSeparated] [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    (P : (Limits.pullback f t).Modules)
    (e : (Scheme.Modules.pullback (Limits.pullback.fst f t)).obj M ≅ P)
    (q : ℕ) :
    let B := Γ(S, (⊤ : S.Opens))
    let A := Γ(T, (⊤ : T.Opens))
    letI : Algebra B A := t.appTop.hom.toAlgebra
    let C := orderedBaseCechComplex f M U
    let UT := fun i ↦ Limits.pullback.fst f t ⁻¹ᵁ U i
    let D := orderedBaseCechComplex (Limits.pullback.snd f t) P UT
    Function.Exact
        ((C.d q (q + 1)).hom.baseChange A)
        ((C.d (q + 1) (q + 2)).hom.baseChange A) ↔
      Function.Exact
        (D.d q (q + 1)).hom
        (D.d (q + 1) (q + 2)).hom := by
  dsimp only
  let B := Γ(S, (⊤ : S.Opens))
  let A := Γ(T, (⊤ : T.Opens))
  letI : Algebra B A := t.appTop.hom.toAlgebra
  let C := orderedBaseCechComplex f M U
  let UT := fun i ↦ Limits.pullback.fst f t ⁻¹ᵁ U i
  let D₀ := orderedBaseCechComplex (Limits.pullback.snd f t)
    ((Scheme.Modules.pullback (Limits.pullback.fst f t)).obj M) UT
  let D := orderedBaseCechComplex (Limits.pullback.snd f t) P UT
  let eBase :
      (((ModuleCat.extendScalars t.appTop.hom).mapHomologicalComplex
        (.up ℕ)).obj C) ≅ D₀ :=
    orderedBaseCechComplexBaseChangeIso f t M U hU
  let eModule : D₀ ≅ D :=
    (orderedBaseCechComplexFunctor (Limits.pullback.snd f t) UT).mapIso e
  let eTotal :
      (((ModuleCat.extendScalars t.appTop.hom).mapHomologicalComplex
        (.up ℕ)).obj C) ≅ D :=
    eBase ≪≫ eModule
  constructor
  · intro h
    have hA :
        (((ModuleCat.extendScalars t.appTop.hom).mapHomologicalComplex
          (.up ℕ)).obj C).ExactAt (q + 1) := by
      simpa only [RingHom.algebraMap_toAlgebra] using
        ModularCurves.cochainComplex_map_exactAt_of_baseChange_functionExact
          A C q h
    exact (ModularCurves.cochainComplex_functionExact_iff_exactAt D q).mpr
      (hA.of_iso eTotal)
  · intro h
    have hD : D.ExactAt (q + 1) :=
      (ModularCurves.cochainComplex_functionExact_iff_exactAt D q).mp h
    have hA :
        (((ModuleCat.extendScalars t.appTop.hom).mapHomologicalComplex
          (.up ℕ)).obj C).ExactAt (q + 1) :=
      hD.of_iso eTotal.symm
    apply ModularCurves.cochainComplex_baseChange_functionExact_of_map_exactAt
      A C q
    simpa only [RingHom.algebraMap_toAlgebra] using hA

end

end AlgebraicGeometry.Scheme.Modules

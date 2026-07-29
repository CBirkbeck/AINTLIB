/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.Algebra.Homology.Homotopy
import ModularCurves.ForMathlib.SchemeModuleBaseCechTupleHomotopy

/-!
# Homotopy equivalence between native and ordered base-Cech complexes

The signed sorting homotopy makes the native all-tuples base-Cech complex homotopy
equivalent to its bounded ordered subcomplex. Consequently their homology modules
are isomorphic in every degree.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Category
  CategoryTheory.Limits CategoryTheory.Preadditive TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

private noncomputable def baseCechAlternatingHomotopyComponent
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (i j : ℕ) (h : (ComplexShape.up ℕ).Rel j i) :
    (baseCechComplex π M U).X i ⟶
      (baseCechComplex π M U).X j := by
  change j + 1 = i at h
  subst i
  exact baseCechAlternatingHomotopyF π M U j

private noncomputable def baseCechAlternatingNullHomotopicMap
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    baseCechComplex π M U ⟶ baseCechComplex π M U :=
  Homotopy.nullHomotopicMap' fun i j h =>
    baseCechAlternatingHomotopyComponent π M U i j h

private theorem baseCechAlternatingNullHomotopicMap_f_zero
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    (baseCechAlternatingNullHomotopicMap π M U).f 0 =
      (baseCechComplex π M U).d 0 1 ≫
        baseCechAlternatingHomotopyF π M U 0 := by
  let h01 : (ComplexShape.up ℕ).Rel 0 1 :=
    ComplexShape.up_mk 0 1 rfl
  rw [baseCechAlternatingNullHomotopicMap,
    Homotopy.nullHomotopicMap'_f_of_not_rel_right h01]
  · rfl
  · intro l hl
    change l + 1 = 0 at hl
    omega

private theorem baseCechAlternatingNullHomotopicMap_f_succ
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (baseCechAlternatingNullHomotopicMap π M U).f (n + 1) =
      (baseCechComplex π M U).d (n + 1) (n + 2) ≫
          baseCechAlternatingHomotopyF π M U (n + 1) +
        baseCechAlternatingHomotopyF π M U n ≫
          (baseCechComplex π M U).d n (n + 1) := by
  let hn : (ComplexShape.up ℕ).Rel n (n + 1) :=
    ComplexShape.up_mk n (n + 1) rfl
  let hn' : (ComplexShape.up ℕ).Rel (n + 1) (n + 2) :=
    ComplexShape.up_mk (n + 1) (n + 2) rfl
  rw [baseCechAlternatingNullHomotopicMap,
    Homotopy.nullHomotopicMap'_f hn hn']
  rfl

private theorem baseCechAlternatingNullHomotopicMap_eq
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    baseCechAlternatingNullHomotopicMap π M U =
      baseCechToOrdered π M U ≫
          orderedToBaseCechAlternating π M U -
        𝟙 (baseCechComplex π M U) := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
      rw [baseCechAlternatingNullHomotopicMap_f_zero]
      exact baseCechAlternatingHomotopy_identity_zero π M U
  | succ n =>
      rw [baseCechAlternatingNullHomotopicMap_f_succ]
      exact baseCechAlternatingHomotopy_identity_succ π M U n

/-- Projection to ordered tuples followed by alternating extension is homotopic
to the identity on the native base-Cech complex. -/
noncomputable def baseCechToOrdered_comp_orderedToBaseCechAlternating_homotopy
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    Homotopy
      (baseCechToOrdered π M U ≫
        orderedToBaseCechAlternating π M U)
      (𝟙 (baseCechComplex π M U)) := by
  refine (Homotopy.equivSubZero
    (f := baseCechToOrdered π M U ≫
      orderedToBaseCechAlternating π M U)
    (g := 𝟙 (baseCechComplex π M U))).symm ?_
  refine (Homotopy.ofEq
    (baseCechAlternatingNullHomotopicMap_eq π M U).symm).trans ?_
  exact Homotopy.nullHomotopy' fun i j h =>
    baseCechAlternatingHomotopyComponent π M U i j h

/-- The native and ordered base-Cech complexes are homotopy equivalent. -/
noncomputable def baseCechOrderedHomotopyEquiv
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    HomotopyEquiv
      (baseCechComplex π M U)
      (orderedBaseCechComplex π M U) where
  hom := baseCechToOrdered π M U
  inv := orderedToBaseCechAlternating π M U
  homotopyHomInvId :=
    baseCechToOrdered_comp_orderedToBaseCechAlternating_homotopy π M U
  homotopyInvHomId := Homotopy.ofEq
    (orderedToBaseCechAlternating_comp_baseCechToOrdered π M U)

/-- Native and ordered base-Cech homology are isomorphic in every degree. -/
noncomputable def baseCechOrderedHomologyIso
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    (baseCechComplex π M U).homology n ≅
      (orderedBaseCechComplex π M U).homology n :=
  (baseCechOrderedHomotopyEquiv π M U).toHomologyIso n

/-- Finite ordered base-Cech homology implies finite native base-Cech homology
in every degree. -/
theorem baseCechComplex_homology_module_finite_of_orderedBaseCechComplex
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    [Module.Finite Γ(S, (⊤ : S.Opens))
      ((orderedBaseCechComplex π M U).homology n)] :
    Module.Finite Γ(S, (⊤ : S.Opens))
      ((baseCechComplex π M U).homology n) :=
  Module.Finite.equiv
    (baseCechOrderedHomologyIso π M U n).symm.toLinearEquiv

end

end AlgebraicGeometry.Scheme.Modules

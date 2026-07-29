/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.AffineSourcePushforwardCohomology
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechGlobalSections
import ModularCurves.ForMathlib.SheafOrderedCechAcyclicComparison
import ModularCurves.ForMathlib.SheafOrderedCechCohomologyFiniteProducts

/-!
# Ordered Cech cohomology for affine open covers

For a finite affine open cover of a separated scheme, every positive cohomology group of
every ordered sheaf-Cech term vanishes. Consequently, exactness of the ordered base-linear
Cech complex is equivalent to vanishing of intrinsic sheaf cohomology.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

open TopCat TopCat.Sheaf

private theorem isAffineHom_open_immersion_of_isAffineOpen
    {X : Scheme.{u}} [X.IsSeparated] (V : X.Opens)
    (hV : IsAffineOpen V) :
    IsAffineHom V.ι := by
  constructor
  intro W hW
  apply (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion V.ι).mp
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]
  exact hV.inf hW

/-- A restriction-pushforward factor of an ordered Cech term for a finite affine open cover
has vanishing positive-degree cohomology. -/
theorem orderedCechTermFactor_subsingleton_H_of_affine_openCover
    {X : Scheme.{u}} [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (p : ℕ) (i : OrderedCechIndex ι p) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (orderedCechTermFactor M.sheaf U p i) (q + 1)) := by
  let V : X.Opens := ∏ᶜ fun k : Fin (p + 1) => U (i.1 k)
  have hV : IsAffineOpen V :=
    IsAffineOpen.cechIntersection U hUaff p i.1
  letI : IsAffine V.toScheme := hV
  letI : IsAffineHom V.ι :=
    isAffineHom_open_immersion_of_isAffineOpen V hV
  have h := subsingleton_H_pushforward_of_isAffineHom
    V.ι (M.restrict V.ι) U hU hUaff q
  change Subsingleton (CategoryTheory.Sheaf.H
    (((pushforward V.ι).obj (M.restrict V.ι)).sheaf) (q + 1))
  exact h

/-- Every ordered Cech term for a finite affine open cover has vanishing positive-degree
cohomology. -/
theorem orderedCechTerm_subsingleton_H_of_affine_openCover
    {X : Scheme.{u}} [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (p q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (orderedCechTerm M.sheaf U p) (q + 1)) :=
  orderedCechTerm_subsingleton_H_of_factors M.sheaf U p (q + 1)
    (fun i =>
      orderedCechTermFactor_subsingleton_H_of_affine_openCover
        M U hU hUaff p i q)

/-- For a finite affine open cover of a separated scheme, exactness of the ordered
base-linear Cech complex is equivalent to vanishing of intrinsic sheaf cohomology. -/
theorem orderedBaseCechComplex_exactAt_succ_iff_subsingleton_H_of_affine_openCover
    {X S : Scheme.{u}} [X.IsSeparated]
    (π : X ⟶ S) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) (n : ℕ) :
    (orderedBaseCechComplex π M U).ExactAt (n + 1) ↔
      Subsingleton (CategoryTheory.Sheaf.H M.sheaf (n + 1)) := by
  have hterm : ∀ (p q : ℕ), 1 ≤ q →
      Subsingleton (CategoryTheory.Sheaf.H
        (orderedCechTerm M.sheaf U p) q) := by
    intro p q hq
    simpa only [Nat.sub_add_cancel hq] using
      orderedCechTerm_subsingleton_H_of_affine_openCover
        M U hU hUaff p (q - 1)
  rw [orderedBaseCechComplex_exactAt_iff_globalSections]
  exact orderedCechGlobalSections_exactAt_succ_iff_subsingleton_H
    M.sheaf U (by simpa only [IsOpenCover] using hU) hterm n

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.CechTupleAlternatingHomotopy

/-!
# Lifting tuple-chain homotopies to base-linear Cech cochains

This file turns a support-nonincreasing map of free tuple chains into a map between degrees of
the existing base-linear Cech complex. A tuple in the support of the image uses only indices from
the source tuple, so restriction of sections supplies the corresponding matrix coefficient.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Category
  CategoryTheory.Limits CategoryTheory.Preadditive Opposite Set
  TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

open ModularCurves

/-- Inclusion of tuple intersections induced by inclusion of their index ranges. -/
theorem cechTupleIntersection_le_of_range_subset
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {n m : ℕ} (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (h : Set.range j ⊆ Set.range i) :
    (∏ᶜ fun k : Fin (n + 1) => U (i k)) ≤
      ∏ᶜ fun k : Fin (m + 1) => U (j k) := by
  classical
  choose q hq using fun k => h ⟨k, rfl⟩
  have hcomp : i ∘ q = j := funext hq
  have hmap :
      ((FormalCoproduct.mk _ U).mapPower q).f i = j := hcomp
  exact leOfHom
    (((FormalCoproduct.mk _ U).mapPower q).φ i ≫
      eqToHom (congrArg
        (fun t : Fin (m + 1) → ι => ∏ᶜ fun k => U (t k)) hmap))

/-- Restrict sections from a tuple intersection to a smaller tuple intersection. -/
noncomputable def baseCechTupleRestriction
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (h : Set.range j ⊆ Set.range i) :
    baseCechFactor π M U m j ⟶ baseCechFactor π M U n i :=
  (baseModulePresheaf π M).map
    (homOfLE (cechTupleIntersection_le_of_range_subset U i j h)).op

/-- One row of the restriction matrix associated to a support-nonincreasing tuple-chain map. -/
noncomputable def baseCechTupleMapComponent
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (f : CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι m)
    (hf : CechTupleSupportNonincreasing f)
    (i : Fin (n + 1) → ι) :
    (baseCechComplex π M U).X m ⟶ baseCechFactor π M U n i :=
  ∑ j : (f (Finsupp.single i 1)).support,
    (f (Finsupp.single i 1) j.1) •
      (Pi.π (fun q : Fin (m + 1) → ι =>
          baseCechFactor π M U m q) j.1 ≫
        baseCechTupleRestriction π M U i j.1 (hf i j.2))

/-- The cochain map between two degrees dual to a support-nonincreasing tuple-chain map. -/
noncomputable def baseCechTupleMapF
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (f : CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι m)
    (hf : CechTupleSupportNonincreasing f) :
    (baseCechComplex π M U).X m ⟶ (baseCechComplex π M U).X n :=
  Pi.lift fun i => baseCechTupleMapComponent π M U f hf i

theorem baseCechTupleMapF_comp_π
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (f : CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι m)
    (hf : CechTupleSupportNonincreasing f)
    (i : Fin (n + 1) → ι) :
    baseCechTupleMapF π M U f hf ≫
        Pi.π (fun q : Fin (n + 1) → ι =>
          baseCechFactor π M U n q) i =
      baseCechTupleMapComponent π M U f hf i :=
  Pi.lift_π _ i

end

end AlgebraicGeometry.Scheme.Modules

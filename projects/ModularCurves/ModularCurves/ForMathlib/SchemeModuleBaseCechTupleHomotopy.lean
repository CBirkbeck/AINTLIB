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

/-- Restricting a tuple factor to itself is the identity. -/
theorem baseCechTupleRestriction_self
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n : ℕ}
    (i : Fin (n + 1) → ι) (h : Set.range i ⊆ Set.range i) :
    baseCechTupleRestriction π M U i i h = 𝟙 _ := by
  let F := baseModulePresheaf π M
  let a := (homOfLE
    (cechTupleIntersection_le_of_range_subset U i i h)).op
  change F.map a = 𝟙 _
  calc
    F.map a = F.map (𝟙 _) :=
      congrArg F.map (Subsingleton.elim _ _)
    _ = 𝟙 _ := F.map_id _

/-- A tuple chain defines a finite row of restriction maps, with unsupported entries discarded. -/
noncomputable def baseCechTupleRow
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) :
    CechTupleChain ι m →ₗ[ℤ]
      ((baseCechComplex π M U).X m ⟶ baseCechFactor π M U n i) :=
  by
    classical
    exact Finsupp.lsum ℤ fun j =>
      LinearMap.toSpanSingleton ℤ _ <|
        if h : Set.range j ⊆ Set.range i then
          Pi.π (fun q : Fin (m + 1) → ι =>
              baseCechFactor π M U m q) j ≫
            baseCechTupleRestriction π M U i j h
        else 0

theorem baseCechTupleRow_single_of_subset
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι) (a : ℤ)
    (h : Set.range j ⊆ Set.range i) :
    baseCechTupleRow π M U i (Finsupp.single j a) =
      a • (Pi.π (fun q : Fin (m + 1) → ι =>
          baseCechFactor π M U m q) j ≫
        baseCechTupleRestriction π M U i j h) := by
  classical
  simp [baseCechTupleRow, h]
  congr

theorem baseCechTupleRow_single_of_not_subset
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι) (a : ℤ)
    (h : ¬Set.range j ⊆ Set.range i) :
    baseCechTupleRow π M U i (Finsupp.single j a) = 0 := by
  classical
  simp [baseCechTupleRow, h]

/-- One row of the restriction matrix associated to a support-nonincreasing tuple-chain map. -/
noncomputable def baseCechTupleMapComponent
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (f : CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι m)
    (_hf : CechTupleSupportNonincreasing f)
    (i : Fin (n + 1) → ι) :
    (baseCechComplex π M U).X m ⟶ baseCechFactor π M U n i :=
  baseCechTupleRow π M U i (f (Finsupp.single i 1))

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

/-- The identity tuple-chain map does not enlarge support. -/
theorem cechTupleSupportNonincreasing_id
    {ι : Type u} {n : ℕ} :
    CechTupleSupportNonincreasing
      (LinearMap.id : CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι n) := by
  intro i
  simpa using CechTupleChain.supportedBy_single i 1 Subset.rfl

/-- A sum of support-nonincreasing tuple-chain maps is support-nonincreasing. -/
theorem CechTupleSupportNonincreasing.add
    {ι : Type u} {n m : ℕ}
    {f g : CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι m}
    (hf : CechTupleSupportNonincreasing f)
    (hg : CechTupleSupportNonincreasing g) :
    CechTupleSupportNonincreasing (f + g) := by
  intro i
  simpa using (hf i).add (hg i)

/-- A negated support-nonincreasing tuple-chain map is support-nonincreasing. -/
theorem CechTupleSupportNonincreasing.neg
    {ι : Type u} {n m : ℕ}
    {f : CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι m}
    (hf : CechTupleSupportNonincreasing f) :
    CechTupleSupportNonincreasing (-f) := by
  intro i
  simpa using (hf i).smul (-1)

/-- Extensionality for a map into one native base-Cech degree, using its concrete tuple factors. -/
theorem baseCechHom_ext
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    {A : ModuleCat.{u} Γ(S, (⊤ : S.Opens))}
    {f g : A ⟶ (baseCechComplex π M U).X n}
    (h : ∀ i : Fin (n + 1) → ι,
      f ≫ Pi.π (fun q : Fin (n + 1) → ι =>
          baseCechFactor π M U n q) i =
        g ≫ Pi.π (fun q : Fin (n + 1) → ι =>
          baseCechFactor π M U n q) i) :
    f = g := by
  apply (cancel_mono (baseCechXIsoPi π M U n).hom).1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  have hi := h i
  have hcomp :
      (f ≫ (baseCechXIsoPi π M U n).hom) ≫
          ModuleCat.ofHom
            (LinearMap.proj i :
              (∀ q : Fin (n + 1) → ι,
                baseCechFactor π M U n q) →ₗ[
                  Γ(S, (⊤ : S.Opens))]
                baseCechFactor π M U n i) =
        (g ≫ (baseCechXIsoPi π M U n).hom) ≫
          ModuleCat.ofHom
            (LinearMap.proj i :
              (∀ q : Fin (n + 1) → ι,
                baseCechFactor π M U n q) →ₗ[
                  Γ(S, (⊤ : S.Opens))]
                baseCechFactor π M U n i) := by
    simpa only [Category.assoc, baseCechXIsoPi_hom_comp_proj]
      using hi
  exact ConcreteCategory.congr_hom hcomp x

/-- The lift of the identity tuple-chain map is the identity on Cech cochains. -/
theorem baseCechTupleMapF_id
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    baseCechTupleMapF π M U
        (LinearMap.id :
          CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι n)
        cechTupleSupportNonincreasing_id =
      𝟙 (baseCechComplex π M U).X n := by
  apply baseCechHom_ext π M U n
  intro i
  let p : (baseCechComplex π M U).X n ⟶
      baseCechFactor π M U n i :=
    Pi.π (fun q : Fin (n + 1) → ι =>
      baseCechFactor π M U n q) i
  calc
    baseCechTupleMapF π M U LinearMap.id
          cechTupleSupportNonincreasing_id ≫ p =
        baseCechTupleMapComponent π M U LinearMap.id
          cechTupleSupportNonincreasing_id i := by
      dsimp only [p]
      exact baseCechTupleMapF_comp_π π M U
        LinearMap.id cechTupleSupportNonincreasing_id i
    _ = p := by
      change baseCechTupleRow π M U i (Finsupp.single i 1) = p
      rw [baseCechTupleRow_single_of_subset
        π M U i i 1 Subset.rfl, one_zsmul,
        baseCechTupleRestriction_self]
      simp [p]
      rfl
    _ = 𝟙 (baseCechComplex π M U).X n ≫ p :=
      (Category.id_comp p).symm

/-- The restriction lift is additive in the tuple-chain map. -/
theorem baseCechTupleMapF_add
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (f g : CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι m)
    (hf : CechTupleSupportNonincreasing f)
    (hg : CechTupleSupportNonincreasing g) :
    baseCechTupleMapF π M U (f + g)
        (CechTupleSupportNonincreasing.add hf hg) =
      baseCechTupleMapF π M U f hf +
        baseCechTupleMapF π M U g hg := by
  apply baseCechHom_ext π M U n
  intro i
  let p : (baseCechComplex π M U).X n ⟶
      baseCechFactor π M U n i :=
    Pi.π (fun q : Fin (n + 1) → ι =>
      baseCechFactor π M U n q) i
  calc
    baseCechTupleMapF π M U (f + g)
          (CechTupleSupportNonincreasing.add hf hg) ≫ p =
        baseCechTupleMapComponent π M U (f + g)
          (CechTupleSupportNonincreasing.add hf hg) i := by
      dsimp only [p]
      exact baseCechTupleMapF_comp_π π M U
        (f + g) (CechTupleSupportNonincreasing.add hf hg) i
    _ = baseCechTupleMapComponent π M U f hf i +
        baseCechTupleMapComponent π M U g hg i := by
      change baseCechTupleRow π M U i
          ((f + g) (Finsupp.single i 1)) =
        baseCechTupleRow π M U i (f (Finsupp.single i 1)) +
          baseCechTupleRow π M U i (g (Finsupp.single i 1))
      simp
    _ = (baseCechTupleMapF π M U f hf ≫ p) +
        (baseCechTupleMapF π M U g hg ≫ p) := by
      dsimp only [p]
      rw [baseCechTupleMapF_comp_π,
        baseCechTupleMapF_comp_π]
    _ = (baseCechTupleMapF π M U f hf +
          baseCechTupleMapF π M U g hg) ≫ p :=
      by rw [add_comp]

/-- The restriction lift sends negation to negation. -/
theorem baseCechTupleMapF_neg
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (f : CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι m)
    (hf : CechTupleSupportNonincreasing f) :
    baseCechTupleMapF π M U (-f)
        (CechTupleSupportNonincreasing.neg hf) =
      -baseCechTupleMapF π M U f hf := by
  apply baseCechHom_ext π M U n
  intro i
  let p : (baseCechComplex π M U).X n ⟶
      baseCechFactor π M U n i :=
    Pi.π (fun q : Fin (n + 1) → ι =>
      baseCechFactor π M U n q) i
  calc
    baseCechTupleMapF π M U (-f)
          (CechTupleSupportNonincreasing.neg hf) ≫ p =
        baseCechTupleMapComponent π M U (-f)
          (CechTupleSupportNonincreasing.neg hf) i := by
      dsimp only [p]
      exact baseCechTupleMapF_comp_π π M U (-f)
        (CechTupleSupportNonincreasing.neg hf) i
    _ = -baseCechTupleMapComponent π M U f hf i := by
      change baseCechTupleRow π M U i
          ((-f) (Finsupp.single i 1)) =
        -baseCechTupleRow π M U i (f (Finsupp.single i 1))
      simp
    _ = -(baseCechTupleMapF π M U f hf ≫ p) := by
      dsimp only [p]
      rw [baseCechTupleMapF_comp_π]
    _ = (-baseCechTupleMapF π M U f hf) ≫ p :=
      by rw [neg_comp]

end

end AlgebraicGeometry.Scheme.Modules

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

/-- Tuple-factor restrictions compose along inclusions of index ranges. -/
theorem baseCechTupleRestriction_comp
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m l : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (k : Fin (l + 1) → ι) (hkj : Set.range k ⊆ Set.range j)
    (hji : Set.range j ⊆ Set.range i) :
    baseCechTupleRestriction π M U j k hkj ≫
        baseCechTupleRestriction π M U i j hji =
      baseCechTupleRestriction π M U i k (hkj.trans hji) := by
  let F := baseModulePresheaf π M
  let a := (homOfLE
    (cechTupleIntersection_le_of_range_subset U j k hkj)).op
  let b := (homOfLE
    (cechTupleIntersection_le_of_range_subset U i j hji)).op
  let c := (homOfLE
    (cechTupleIntersection_le_of_range_subset U i k
      (hkj.trans hji))).op
  change F.map a ≫ F.map b = F.map c
  calc
    F.map a ≫ F.map b = F.map (a ≫ b) :=
      (F.map_comp a b).symm
    _ = F.map c := congrArg F.map (Subsingleton.elim _ _)

/-- Tuple restriction agrees with any map between the same two intersection opens. -/
theorem baseCechTupleRestriction_eq_map
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (h : Set.range j ⊆ Set.range i)
    (a : (∏ᶜ fun k : Fin (n + 1) => U (i k)) ⟶
      ∏ᶜ fun k : Fin (m + 1) => U (j k)) :
    baseCechTupleRestriction π M U i j h =
      (baseModulePresheaf π M).map a.op := by
  apply congrArg (baseModulePresheaf π M).map
  exact Subsingleton.elim _ _

/-- One basis entry in a tuple row, with unsupported entries discarded. -/
noncomputable def baseCechTupleRowBasis
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι) :
    (baseCechComplex π M U).X m ⟶ baseCechFactor π M U n i := by
  classical
  let p : (baseCechComplex π M U).X m ⟶
      baseCechFactor π M U m j :=
    Pi.π (fun q : Fin (m + 1) → ι =>
      baseCechFactor π M U m q) j
  exact if h : Set.range j ⊆ Set.range i then
    p ≫ baseCechTupleRestriction π M U i j h
  else 0

theorem baseCechTupleRowBasis_of_subset
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (h : Set.range j ⊆ Set.range i) :
    baseCechTupleRowBasis π M U i j =
      Pi.π (fun q : Fin (m + 1) → ι =>
          baseCechFactor π M U m q) j ≫
        baseCechTupleRestriction π M U i j h := by
  classical
  simp [baseCechTupleRowBasis, h]
  congr

theorem baseCechTupleRowBasis_of_not_subset
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (h : ¬Set.range j ⊆ Set.range i) :
    baseCechTupleRowBasis π M U i j = 0 := by
  classical
  simp [baseCechTupleRowBasis, h]

/-- A supported row-basis entry composes with tuple-factor restriction. -/
theorem baseCechTupleRowBasis_comp_restriction
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m l : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (k : Fin (l + 1) → ι) (hkj : Set.range k ⊆ Set.range j)
    (hji : Set.range j ⊆ Set.range i) :
    baseCechTupleRowBasis π M U j k ≫
        baseCechTupleRestriction π M U i j hji =
      baseCechTupleRowBasis π M U i k := by
  let p : (baseCechComplex π M U).X l ⟶
      baseCechFactor π M U l k :=
    Pi.π (fun q : Fin (l + 1) → ι =>
      baseCechFactor π M U l q) k
  calc
    baseCechTupleRowBasis π M U j k ≫
          baseCechTupleRestriction π M U i j hji =
        (p ≫ baseCechTupleRestriction π M U j k hkj) ≫
          baseCechTupleRestriction π M U i j hji := by
      rw [baseCechTupleRowBasis_of_subset π M U j k hkj]
      rfl
    _ = p ≫
        (baseCechTupleRestriction π M U j k hkj ≫
          baseCechTupleRestriction π M U i j hji) :=
      Category.assoc _ _ _
    _ = p ≫ baseCechTupleRestriction π M U i k
        (hkj.trans hji) := by
      rw [baseCechTupleRestriction_comp]
    _ = baseCechTupleRowBasis π M U i k := by
      rw [baseCechTupleRowBasis_of_subset
        π M U i k (hkj.trans hji)]
      rfl

/-- A tuple chain defines a finite row of restriction maps. -/
noncomputable def baseCechTupleRow
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) :
    CechTupleChain ι m →ₗ[ℤ]
      ((baseCechComplex π M U).X m ⟶ baseCechFactor π M U n i) :=
  by
    exact Finsupp.lsum ℤ fun j =>
      LinearMap.toSpanSingleton ℤ _
        (baseCechTupleRowBasis π M U i j)

theorem baseCechTupleRow_single_of_subset
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι) (a : ℤ)
    (h : Set.range j ⊆ Set.range i) :
    baseCechTupleRow π M U i (Finsupp.single j a) =
      a • (Pi.π (fun q : Fin (m + 1) → ι =>
          baseCechFactor π M U m q) j ≫
        baseCechTupleRestriction π M U i j h) := by
  rw [baseCechTupleRow, Finsupp.lsum_single,
    LinearMap.toSpanSingleton_apply,
    baseCechTupleRowBasis_of_subset π M U i j h]
  rfl

theorem baseCechTupleRow_single_of_not_subset
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι) (a : ℤ)
    (h : ¬Set.range j ⊆ Set.range i) :
    baseCechTupleRow π M U i (Finsupp.single j a) = 0 := by
  rw [baseCechTupleRow, Finsupp.lsum_single,
    LinearMap.toSpanSingleton_apply,
    baseCechTupleRowBasis_of_not_subset π M U i j h,
    smul_zero]

/-- Postcomposing a tuple row with restriction only changes its target tuple. -/
theorem baseCechTupleRow_comp_restriction
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m l : ℕ}
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (hji : Set.range j ⊆ Set.range i) (x : CechTupleChain ι l)
    (hx : CechTupleChain.SupportedBy x (Set.range j)) :
    baseCechTupleRow π M U j x ≫
        baseCechTupleRestriction π M U i j hji =
      baseCechTupleRow π M U i x := by
  classical
  rw [baseCechTupleRow, baseCechTupleRow,
    Finsupp.lsum_apply, Finsupp.lsum_apply]
  rw [Finsupp.sum, Finsupp.sum, sum_comp]
  apply Finset.sum_congr rfl
  intro k hk
  have hkj := hx hk
  simp only [LinearMap.toSpanSingleton_apply]
  rw [zsmul_comp,
    baseCechTupleRowBasis_comp_restriction
      π M U i j k hkj hji]

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

/-- A linear map out of a free integral module is the sum of its values on basis vectors. -/
theorem linearMap_apply_eq_finsupp_sum_single
    {α N : Type u} [AddCommGroup N]
    (f : (α →₀ ℤ) →ₗ[ℤ] N) (x : α →₀ ℤ) :
    f x = x.sum fun i a => a • f (Finsupp.single i 1) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, hx, hy,
        Finsupp.sum_add_index (by simp) (by simp [add_smul])]
  | single i a =>
      calc
        f (Finsupp.single i a) =
            a • f (Finsupp.single i 1) := by
          simpa using f.map_smul a (Finsupp.single i 1)
        _ = (Finsupp.single i a).sum
            (fun j b => b • f (Finsupp.single j 1)) := by
          simp

/-- A support-nonincreasing map preserves any prescribed containing support. -/
theorem CechTupleSupportNonincreasing.map_supportedBy
    {ι : Type u} {n m : ℕ}
    {f : CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι m}
    (hf : CechTupleSupportNonincreasing f)
    (x : CechTupleChain ι n) (N : Set ι)
    (hx : CechTupleChain.SupportedBy x N) :
    CechTupleChain.SupportedBy (f x) N := by
  rw [linearMap_apply_eq_finsupp_sum_single]
  change CechTupleChain.SupportedBy
    (∑ i ∈ x.support,
      x i • f (Finsupp.single i 1)) N
  apply CechTupleChain.supportedBy_sum x.support _
  intro i hi
  exact CechTupleChain.SupportedBy.smul
    (CechTupleChain.SupportedBy.mono (hf i) (hx hi)) (x i)

/-- A composite of support-nonincreasing tuple-chain maps is support-nonincreasing. -/
theorem CechTupleSupportNonincreasing.comp
    {ι : Type u} {n m l : ℕ}
    {f : CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι m}
    {g : CechTupleChain ι m →ₗ[ℤ] CechTupleChain ι l}
    (hg : CechTupleSupportNonincreasing g)
    (hf : CechTupleSupportNonincreasing f) :
    CechTupleSupportNonincreasing (g.comp f) := by
  intro i
  exact CechTupleSupportNonincreasing.map_supportedBy
    hg (f (Finsupp.single i 1)) (Set.range i) (hf i)

/-- The tuple deletion boundary does not enlarge support. -/
theorem cechTupleBoundary_supportNonincreasing
    {ι : Type u} (n : ℕ) :
    CechTupleSupportNonincreasing
      (cechTupleBoundary (ι := ι) n) := by
  intro i
  apply cechTupleBoundary_supportedBy
  exact CechTupleChain.supportedBy_single i 1 Subset.rfl

/-- The sorted-tuple projection does not enlarge support. -/
theorem cechTupleAlternatingProjection_supportNonincreasing
    {ι : Type u} [LinearOrder ι] (n : ℕ) :
    CechTupleSupportNonincreasing
      (cechTupleAlternatingProjection (ι := ι) n) := by
  intro i
  apply cechTupleAlternatingProjection_supportedBy
  exact CechTupleChain.supportedBy_single i 1 Subset.rfl

/-- The lower-degree term in the tuple homotopy does not enlarge support. -/
theorem cechTupleAlternatingHomotopyPrevious_supportNonincreasing
    {ι : Type u} [LinearOrder ι] (n : ℕ) :
    CechTupleSupportNonincreasing
      (cechTupleAlternatingHomotopyPrevious (ι := ι) n) := by
  intro i
  cases n with
  | zero =>
      exact CechTupleChain.supportedBy_zero
  | succ n =>
      apply cechTupleAlternatingHomotopy_supportedBy
      apply cechTupleBoundary_supportedBy
      exact CechTupleChain.supportedBy_single i 1 Subset.rfl

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

/-- A lifted tuple map commutes with one supported tuple-row basis vector. -/
theorem baseCechTupleMapF_comp_row_single
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m l : ℕ}
    (g : CechTupleChain ι m →ₗ[ℤ] CechTupleChain ι l)
    (hg : CechTupleSupportNonincreasing g)
    (i : Fin (n + 1) → ι) (j : Fin (m + 1) → ι)
    (hji : Set.range j ⊆ Set.range i) :
    baseCechTupleMapF π M U g hg ≫
        baseCechTupleRow π M U i (Finsupp.single j 1) =
      baseCechTupleRow π M U i
        (g (Finsupp.single j 1)) := by
  let p : (baseCechComplex π M U).X m ⟶
      baseCechFactor π M U m j :=
    Pi.π (fun q : Fin (m + 1) → ι =>
      baseCechFactor π M U m q) j
  have hrow :
      baseCechTupleRow π M U i (Finsupp.single j 1) =
        p ≫ baseCechTupleRestriction π M U i j hji := by
    rw [baseCechTupleRow_single_of_subset
      π M U i j 1 hji, one_zsmul]
    rfl
  have hproj :
      baseCechTupleMapF π M U g hg ≫ p =
        baseCechTupleMapComponent π M U g hg j := by
    dsimp only [p]
    exact baseCechTupleMapF_comp_π π M U g hg j
  calc
    baseCechTupleMapF π M U g hg ≫
          baseCechTupleRow π M U i (Finsupp.single j 1) =
        baseCechTupleMapF π M U g hg ≫
          (p ≫ baseCechTupleRestriction π M U i j hji) := by
      rw [hrow]
    _ = (baseCechTupleMapF π M U g hg ≫ p) ≫
        baseCechTupleRestriction π M U i j hji :=
      (Category.assoc _ _ _).symm
    _ = baseCechTupleMapComponent π M U g hg j ≫
        baseCechTupleRestriction π M U i j hji := by
      rw [hproj]
    _ = baseCechTupleRow π M U j
          (g (Finsupp.single j 1)) ≫
        baseCechTupleRestriction π M U i j hji := rfl
    _ = baseCechTupleRow π M U i
        (g (Finsupp.single j 1)) :=
      baseCechTupleRow_comp_restriction π M U i j hji
        (g (Finsupp.single j 1)) (hg j)

/-- A lifted tuple map commutes with every supported tuple row. -/
theorem baseCechTupleMapF_comp_row
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m l : ℕ}
    (g : CechTupleChain ι m →ₗ[ℤ] CechTupleChain ι l)
    (hg : CechTupleSupportNonincreasing g)
    (i : Fin (n + 1) → ι) (x : CechTupleChain ι m)
    (hx : CechTupleChain.SupportedBy x (Set.range i)) :
    baseCechTupleMapF π M U g hg ≫
        baseCechTupleRow π M U i x =
      baseCechTupleRow π M U i (g x) := by
  classical
  have hsource := linearMap_apply_eq_finsupp_sum_single
    (baseCechTupleRow π M U i) x
  have htarget := linearMap_apply_eq_finsupp_sum_single
    ((baseCechTupleRow π M U i).comp g) x
  change baseCechTupleRow π M U i (g x) =
    x.sum (fun j a => a • baseCechTupleRow π M U i
      (g (Finsupp.single j 1))) at htarget
  rw [hsource, htarget]
  rw [Finsupp.sum, Finsupp.sum, comp_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [comp_zsmul,
    baseCechTupleMapF_comp_row_single π M U g hg i j (hx hj)]

/-- Lifting support-nonincreasing tuple maps reverses their composition. -/
theorem baseCechTupleMapF_comp
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m l : ℕ}
    (f : CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι m)
    (g : CechTupleChain ι m →ₗ[ℤ] CechTupleChain ι l)
    (hf : CechTupleSupportNonincreasing f)
    (hg : CechTupleSupportNonincreasing g) :
    baseCechTupleMapF π M U (g.comp f)
        (CechTupleSupportNonincreasing.comp hg hf) =
      baseCechTupleMapF π M U g hg ≫
        baseCechTupleMapF π M U f hf := by
  apply baseCechHom_ext π M U n
  intro i
  let p : (baseCechComplex π M U).X n ⟶
      baseCechFactor π M U n i :=
    Pi.π (fun q : Fin (n + 1) → ι =>
      baseCechFactor π M U n q) i
  calc
    baseCechTupleMapF π M U (g.comp f)
          (CechTupleSupportNonincreasing.comp hg hf) ≫ p =
        baseCechTupleMapComponent π M U (g.comp f)
          (CechTupleSupportNonincreasing.comp hg hf) i := by
      dsimp only [p]
      exact baseCechTupleMapF_comp_π π M U (g.comp f)
        (CechTupleSupportNonincreasing.comp hg hf) i
    _ = baseCechTupleRow π M U i
        (g (f (Finsupp.single i 1))) := rfl
    _ = baseCechTupleMapF π M U g hg ≫
        baseCechTupleRow π M U i
          (f (Finsupp.single i 1)) :=
      (baseCechTupleMapF_comp_row π M U g hg i
        (f (Finsupp.single i 1)) (hf i)).symm
    _ = baseCechTupleMapF π M U g hg ≫
        baseCechTupleMapComponent π M U f hf i := rfl
    _ = baseCechTupleMapF π M U g hg ≫
        (baseCechTupleMapF π M U f hf ≫ p) := by
      dsimp only [p]
      rw [baseCechTupleMapF_comp_π]
    _ = (baseCechTupleMapF π M U g hg ≫
          baseCechTupleMapF π M U f hf) ≫ p :=
      (Category.assoc _ _ _).symm

/-- Deleting an entry does not introduce a new tuple index. -/
theorem cechTupleDelete_range_subset
    {ι : Type u} {n : ℕ} (i : Fin (n + 2) → ι)
    (k : Fin (n + 2)) :
    Set.range (cechTupleDelete i k) ⊆ Set.range i := by
  rintro x ⟨l, rfl⟩
  exact ⟨k.succAbove l, rfl⟩

/-- The restriction lift of the tuple boundary is the native base-Cech differential. -/
theorem baseCechTupleMapF_boundary
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    baseCechTupleMapF π M U
        (cechTupleBoundary (ι := ι) n)
        (cechTupleBoundary_supportNonincreasing n) =
      (baseCechComplex π M U).d n (n + 1) := by
  apply baseCechHom_ext π M U (n + 1)
  intro i
  let p : (baseCechComplex π M U).X (n + 1) ⟶
      baseCechFactor π M U (n + 1) i :=
    Pi.π (fun q : Fin (n + 2) → ι =>
      baseCechFactor π M U (n + 1) q) i
  let t : (baseCechComplex π M U).X n ⟶
      baseCechFactor π M U (n + 1) i :=
    ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
      (Pi.π (fun q : Fin (n + 1) → ι =>
          baseCechFactor π M U n q)
            (cechTupleDelete i k) ≫
        (baseModulePresheaf π M).map
          (((FormalCoproduct.mk _ U).mapPower k.succAbove).φ i).op)
  have hcomponent :
      baseCechTupleMapComponent π M U
          (cechTupleBoundary (ι := ι) n)
          (cechTupleBoundary_supportNonincreasing n) i = t := by
    change baseCechTupleRow π M U i
        (cechTupleBoundary n (Finsupp.single i 1)) = t
    rw [cechTupleBoundary_single, one_smul]
    unfold cechTupleBoundaryBasis
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    let h := cechTupleDelete_range_subset i k
    rw [baseCechTupleRow_single_of_subset
      π M U i (cechTupleDelete i k)
        ((-1 : ℤ) ^ (k : ℕ)) h]
    congr 2
  calc
    baseCechTupleMapF π M U (cechTupleBoundary n)
          (cechTupleBoundary_supportNonincreasing n) ≫ p =
        baseCechTupleMapComponent π M U (cechTupleBoundary n)
          (cechTupleBoundary_supportNonincreasing n) i := by
      dsimp only [p]
      exact baseCechTupleMapF_comp_π π M U
        (cechTupleBoundary n)
          (cechTupleBoundary_supportNonincreasing n) i
    _ = t := hcomponent
    _ = (baseCechComplex π M U).d n (n + 1) ≫ p := by
      dsimp only [t, p]
      rw [baseCechComplex_d_comp_π]
      apply Finset.sum_congr rfl
      intro k _
      have hδ :
          (SimplexCategory.δ k).toOrderHom.toFun =
            k.succAbove := by
        change (⇑(ConcreteCategory.hom (SimplexCategory.δ k))) =
          k.succAbove
        exact SimplexCategory.coe_δ k
      rw [hδ]
      rfl

/-- The restriction lift of signed sorting is projection to ordered tuples followed by
alternating extension. -/
theorem baseCechTupleMapF_alternatingProjection
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ) :
    baseCechTupleMapF π M U
        (cechTupleAlternatingProjection (ι := ι) n)
        (cechTupleAlternatingProjection_supportNonincreasing n) =
      baseCechToOrderedF π M U n ≫
        orderedToBaseCechAlternatingF π M U n := by
  apply baseCechHom_ext π M U n
  intro i
  let p : (baseCechComplex π M U).X n ⟶
      baseCechFactor π M U n i :=
    Pi.π (fun q : Fin (n + 1) → ι =>
      baseCechFactor π M U n q) i
  change baseCechTupleMapF π M U
      (cechTupleAlternatingProjection n)
        (cechTupleAlternatingProjection_supportNonincreasing n) ≫ p =
    (baseCechToOrderedF π M U n ≫
      orderedToBaseCechAlternatingF π M U n) ≫ p
  rw [Category.assoc]
  by_cases hi : Function.Injective i
  · let s := Tuple.sort i
    let j := i ∘ s
    have hj : StrictMono j :=
      (Tuple.monotone_sort i).strictMono_of_injective
        (hi.comp s.injective)
    let pj : (baseCechComplex π M U).X n ⟶
        baseCechFactor π M U n j :=
      Pi.π (fun q : Fin (n + 1) → ι =>
        baseCechFactor π M U n q) j
    let q : orderedBaseCechObject π M U n ⟶
        baseCechFactor π M U n j :=
      Pi.π (fun t : OrderedCechIndex ι n =>
        baseCechFactor π M U n t.1) ⟨j, hj⟩
    have hji : Set.range j ⊆ Set.range i := by
      rintro x ⟨k, rfl⟩
      exact ⟨s k, rfl⟩
    let r : baseCechFactor π M U n j ⟶
        baseCechFactor π M U n i :=
      baseCechTupleRestriction π M U i j hji
    have hr :
        r = (baseModulePresheaf π M).map
          (((FormalCoproduct.mk _ U).mapPower s).φ i).op := by
      dsimp only [r]
      exact baseCechTupleRestriction_eq_map π M U i j hji
        (((FormalCoproduct.mk _ U).mapPower s).φ i)
    have hleft :
        baseCechTupleMapF π M U
            (cechTupleAlternatingProjection n)
            (cechTupleAlternatingProjection_supportNonincreasing n) ≫ p =
          (Equiv.Perm.sign s : ℤ) • (pj ≫ r) := by
      calc
        baseCechTupleMapF π M U
              (cechTupleAlternatingProjection n)
              (cechTupleAlternatingProjection_supportNonincreasing n) ≫ p =
            baseCechTupleMapComponent π M U
              (cechTupleAlternatingProjection n)
              (cechTupleAlternatingProjection_supportNonincreasing n) i := by
          dsimp only [p]
          exact baseCechTupleMapF_comp_π π M U
            (cechTupleAlternatingProjection n)
              (cechTupleAlternatingProjection_supportNonincreasing n) i
        _ = baseCechTupleRow π M U i
              (cechTupleAlternatingProjectionBasis n i) := by
          change baseCechTupleRow π M U i
              (cechTupleAlternatingProjection n
                (Finsupp.single i 1)) =
            baseCechTupleRow π M U i
              (cechTupleAlternatingProjectionBasis n i)
          rw [cechTupleAlternatingProjection_single, one_smul]
        _ = baseCechTupleRow π M U i
              (Finsupp.single j (Equiv.Perm.sign s : ℤ)) := by
          rw [cechTupleAlternatingProjectionBasis_of_injective i hi]
        _ = (Equiv.Perm.sign s : ℤ) • (pj ≫ r) := by
          exact baseCechTupleRow_single_of_subset
            π M U i j (Equiv.Perm.sign s : ℤ) hji
    have hproj : baseCechToOrderedF π M U n ≫ q = pj := by
      dsimp only [q, pj]
      exact baseCechToOrderedF_comp_π π M U n ⟨j, hj⟩
    have halt :
        orderedToBaseCechAlternatingF π M U n ≫ p =
          (Equiv.Perm.sign s : ℤ) • (q ≫ r) := by
      rw [hr]
      exact orderedToBaseCechAlternatingF_comp_π_of_injective
        π M U n i hi
    rw [hleft]
    calc
      (Equiv.Perm.sign s : ℤ) • (pj ≫ r) =
          (Equiv.Perm.sign s : ℤ) •
            ((baseCechToOrderedF π M U n ≫ q) ≫ r) := by
        rw [hproj]
      _ = baseCechToOrderedF π M U n ≫
          ((Equiv.Perm.sign s : ℤ) • (q ≫ r)) := by
        simp only [comp_zsmul, Category.assoc]
      _ = baseCechToOrderedF π M U n ≫
          (orderedToBaseCechAlternatingF π M U n ≫ p) := by
        rw [halt]
  · have hleft :
        baseCechTupleMapF π M U
            (cechTupleAlternatingProjection n)
            (cechTupleAlternatingProjection_supportNonincreasing n) ≫ p = 0 := by
      calc
        baseCechTupleMapF π M U
              (cechTupleAlternatingProjection n)
              (cechTupleAlternatingProjection_supportNonincreasing n) ≫ p =
            baseCechTupleMapComponent π M U
              (cechTupleAlternatingProjection n)
              (cechTupleAlternatingProjection_supportNonincreasing n) i := by
          dsimp only [p]
          exact baseCechTupleMapF_comp_π π M U
            (cechTupleAlternatingProjection n)
              (cechTupleAlternatingProjection_supportNonincreasing n) i
        _ = 0 := by
          change baseCechTupleRow π M U i
              (cechTupleAlternatingProjection n
                (Finsupp.single i 1)) = 0
          rw [cechTupleAlternatingProjection_single, one_smul,
            cechTupleAlternatingProjectionBasis_of_not_injective i hi,
            map_zero]
    rw [hleft]
    rw [orderedToBaseCechAlternatingF_comp_π_of_not_injective
      π M U n i hi]
    simp

/-- The zero tuple-chain map does not enlarge support. -/
theorem cechTupleSupportNonincreasing_zero
    {ι : Type u} {n m : ℕ} :
    CechTupleSupportNonincreasing
      (0 : CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι m) := by
  intro i
  change CechTupleChain.SupportedBy 0 (Set.range i)
  exact CechTupleChain.supportedBy_zero

/-- The restriction lift sends the zero tuple-chain map to zero. -/
theorem baseCechTupleMapF_zero
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n m : ℕ) :
    baseCechTupleMapF π M U
        (0 : CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι m)
        cechTupleSupportNonincreasing_zero = 0 := by
  apply baseCechHom_ext π M U n
  intro i
  let p : (baseCechComplex π M U).X n ⟶
      baseCechFactor π M U n i :=
    Pi.π (fun q : Fin (n + 1) → ι =>
      baseCechFactor π M U n q) i
  calc
    baseCechTupleMapF π M U 0
          cechTupleSupportNonincreasing_zero ≫ p =
        baseCechTupleMapComponent π M U 0
          cechTupleSupportNonincreasing_zero i := by
      dsimp only [p]
      exact baseCechTupleMapF_comp_π π M U 0
        cechTupleSupportNonincreasing_zero i
    _ = 0 := by
      change baseCechTupleRow π M U i
        ((0 : CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι m)
          (Finsupp.single i 1)) = 0
      simp
    _ = 0 ≫ p := by simp

/-- Equal support-nonincreasing tuple maps have equal restriction lifts. -/
theorem baseCechTupleMapF_congr
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) {n m : ℕ}
    (f g : CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι m)
    (hf : CechTupleSupportNonincreasing f)
    (hg : CechTupleSupportNonincreasing g) (hfg : f = g) :
    baseCechTupleMapF π M U f hf =
      baseCechTupleMapF π M U g hg := by
  subst g
  rfl

/-- The tuple homotopy identity as an equality of integral linear maps. -/
theorem cechTupleAlternatingHomotopy_linear_identity
    {ι : Type u} [LinearOrder ι] (n : ℕ) :
    (cechTupleBoundary n).comp
          (cechTupleAlternatingHomotopy n) +
        cechTupleAlternatingHomotopyPrevious n =
      cechTupleAlternatingProjection n +
        -(LinearMap.id :
          CechTupleChain ι n →ₗ[ℤ] CechTupleChain ι n) := by
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.neg_apply, LinearMap.id_apply, sub_eq_add_neg]
    using cechTupleAlternatingHomotopy_identity n x

end

end AlgebraicGeometry.Scheme.Modules

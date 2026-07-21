/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistCechFirstLaurent

/-!
# Homogeneous-weight coordinates for the projective twist Cech complex

This file reindexes each standard-intersection factor of the existing ordered Cech complex by its
allowed global homogeneous Laurent weights.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

local instance : DecidableEq σ := Classical.decEq σ

/-- The degree-`n` coordinate Cech term, with each standard-intersection factor reindexed by the
global degree-`d` homogeneous Laurent weights allowed on its ordered tuple. -/
noncomputable def coordinateHomogeneousLaurentOrderedCechObject
    [LinearOrder σ] (d : ℤ) (n : ℕ) :
    ModuleCat.{u} Γ(Spec (CommRingCat.of R),
      (⊤ : (Spec (CommRingCat.of R)).Opens)) :=
  ∏ᶜ fun a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
    ModuleCat.of
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (AddMonoidAlgebra
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        {e : HomogeneousLaurentExponent σ d //
          e.IsAllowedOn (fun k => (a.1 k).down)})

/-- The existing structure-sheaf coordinate Cech term is factorwise equivalent to its
homogeneous-weight presentation. -/
noncomputable def coordinateHomogeneousLaurentOrderedCechObjectIso
    [LinearOrder σ] (d : ℤ) (n : ℕ) :
    Scheme.Modules.orderedBaseCechObject
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n ≅
      coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n :=
  Pi.mapIso fun a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
    (coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
      (R := R) a.1 d).toModuleIso

/-- The degreewise homogeneous-weight comparison is the landed factor equivalence on every
ordered tuple. -/
@[reassoc]
theorem coordinateHomogeneousLaurentOrderedCechObjectIso_hom_comp_π
    [LinearOrder σ] (d : ℤ) (n : ℕ)
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    (coordinateHomogeneousLaurentOrderedCechObjectIso
        (R := R) (σ := σ) d n).hom ≫
      Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
        ModuleCat.of
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          (AddMonoidAlgebra
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            {e : HomogeneousLaurentExponent σ d //
              e.IsAllowedOn (fun k => (b.1 k).down)})) a =
      Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
        Scheme.Modules.baseCechFactor
          (homogeneousProjπ (R := R) (σ := σ))
          (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
          (coordinateOpenCover (R := R) (σ := σ)) n b.1) a ≫
        (coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
          (R := R) a.1 d).toModuleIso.hom := by
  exact Pi.mapIso_hom_π
    (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      (coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
        (R := R) b.1 d).toModuleIso) a

/-- The ordered Cech coface on homogeneous Laurent weights deletes one entry from the ordered
tuple and extends each allowed weight to the larger intersection. -/
noncomputable def coordinateHomogeneousLaurentOrderedCechCoface
    [LinearOrder σ] (d : ℤ) (n : ℕ) (k : Fin (n + 2)) :
    coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n ⟶
      coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d (n + 1) :=
  Pi.lift fun a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1) =>
    Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      ModuleCat.of
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (AddMonoidAlgebra
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          {e : HomogeneousLaurentExponent σ d //
            e.IsAllowedOn (fun l => (b.1 l).down)})) (a.delete k) ≫
      ModuleCat.ofHom
        (coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k d)

/-- Projecting a homogeneous-weight coface to an ordered tuple gives the corresponding deletion
map on allowed weights. -/
@[reassoc]
theorem coordinateHomogeneousLaurentOrderedCechCoface_comp_π
    [LinearOrder σ] (d : ℤ) (n : ℕ) (k : Fin (n + 2))
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    coordinateHomogeneousLaurentOrderedCechCoface
        (R := R) (σ := σ) d n k ≫
      Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1) =>
        ModuleCat.of
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          (AddMonoidAlgebra
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            {e : HomogeneousLaurentExponent σ d //
              e.IsAllowedOn (fun l => (b.1 l).down)})) a =
      Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
        ModuleCat.of
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          (AddMonoidAlgebra
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            {e : HomogeneousLaurentExponent σ d //
              e.IsAllowedOn (fun l => (b.1 l).down)})) (a.delete k) ≫
        ModuleCat.ofHom
          (coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k d) := by
  exact Pi.lift_π _ a

/-- On the first face, the homogeneous-weight deletion map is conjugate to restriction followed
by the first-face transition factor. -/
theorem coordinateHomogeneousLaurentFactorCoface_naturality_delete_zero
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) (d : ℤ) :
    (coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
        (R := R) (a.delete 0).1 d).toModuleIso.hom ≫
      ModuleCat.ofHom
        (coordinateHomogeneousLaurentDeleteLinearMap (R := R) a 0 d) =
    (Scheme.Modules.baseModulePresheaf
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
          (coordinateOpenCechDelete (R := R) a 0).op ≫
      coordinateOpenCechFirstTransitionFactorEnd (R := R) a d ≫
        (coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
          (R := R) a.1 d).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv_naturality_delete_zero
    (R := R) a d x).symm

/-- On every noninitial face, the homogeneous-weight deletion map is conjugate to ordinary
restriction. -/
theorem coordinateHomogeneousLaurentFactorCoface_naturality_delete_succ
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 1)) (d : ℤ) :
    (coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
        (R := R) (a.delete k.succ).1 d).toModuleIso.hom ≫
      ModuleCat.ofHom
        (coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k.succ d) =
    (Scheme.Modules.baseModulePresheaf
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
          (coordinateOpenCechDelete (R := R) a k.succ).op ≫
        (coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv
          (R := R) a.1 d).toModuleIso.hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv_naturality_delete_succ
    (R := R) a k d x).symm

/-- The factorwise homogeneous-weight equivalences conjugate every geometric ordered Cech coface
to deletion of allowed global weights. -/
theorem coordinateHomogeneousLaurentOrderedCechCoface_naturality
    [LinearOrder σ] (d : ℤ) (n : ℕ) (k : Fin (n + 2)) :
    (coordinateHomogeneousLaurentOrderedCechObjectIso
        (R := R) (σ := σ) d n).hom ≫
      coordinateHomogeneousLaurentOrderedCechCoface
        (R := R) (σ := σ) d n k =
    coordinateHyperplaneTwistOrderedBaseCechCoface
        (R := R) (σ := σ) d n k ≫
      (coordinateHomogeneousLaurentOrderedCechObjectIso
        (R := R) (σ := σ) d (n + 1)).hom := by
  unfold coordinateHomogeneousLaurentOrderedCechObjectIso
  unfold coordinateHomogeneousLaurentOrderedCechCoface
  apply Pi.hom_ext
  intro a
  erw [Category.assoc, Pi.lift_π, Pi.mapIso_hom_π_assoc,
    Category.assoc, Pi.mapIso_hom_π]
  by_cases hk : k = 0
  · subst k
    rw [coordinateHyperplaneTwistOrderedBaseCechCoface, if_pos rfl]
    conv_rhs =>
      erw [← Category.assoc,
        coordinateHyperplaneTwistOrderedBaseCechFirstCoface_comp_π]
    let p : Scheme.Modules.orderedBaseCechObject
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n ⟶
      Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n (a.delete 0).1 :=
      Pi.π _ (a.delete 0)
    have hp :
        Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
          Scheme.Modules.baseCechFactor
            (homogeneousProjπ (R := R) (σ := σ))
            (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
            (coordinateOpenCover (R := R) (σ := σ)) n b.1) (a.delete 0) = p := rfl
    rw [hp]
    exact congrArg (fun f => p ≫ f)
      (coordinateHomogeneousLaurentFactorCoface_naturality_delete_zero
        (R := R) a d)
  · obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hk
    rw [coordinateHyperplaneTwistOrderedBaseCechCoface,
      if_neg (Fin.succ_ne_zero k)]
    conv_rhs =>
      erw [← Category.assoc, Scheme.Modules.orderedBaseCechCoface_comp_π]
    let p : Scheme.Modules.orderedBaseCechObject
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n ⟶
      Scheme.Modules.baseCechFactor
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n (a.delete k.succ).1 :=
      Pi.π _ (a.delete k.succ)
    have hp :
        Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
          Scheme.Modules.baseCechFactor
            (homogeneousProjπ (R := R) (σ := σ))
            (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
            (coordinateOpenCover (R := R) (σ := σ)) n b.1)
          (a.delete k.succ) = p := rfl
    rw [hp]
    exact congrArg (fun f => p ≫ f)
      (coordinateHomogeneousLaurentFactorCoface_naturality_delete_succ
        (R := R) a k d)

/-- The alternating ordered Cech differential in homogeneous Laurent weights. -/
noncomputable def coordinateHomogeneousLaurentOrderedCechDifferential
    [LinearOrder σ] (d : ℤ) (n : ℕ) :
    coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n ⟶
      coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d (n + 1) :=
  ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
    coordinateHomogeneousLaurentOrderedCechCoface (R := R) (σ := σ) d n k

/-- The degreewise homogeneous-weight comparison conjugates the geometric coordinate differential
to the alternating deletion differential. -/
theorem coordinateHomogeneousLaurentOrderedCechDifferential_naturality
    [LinearOrder σ] (d : ℤ) (n : ℕ) :
    (coordinateHomogeneousLaurentOrderedCechObjectIso
        (R := R) (σ := σ) d n).hom ≫
      coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d n =
    coordinateHyperplaneTwistOrderedBaseCechDifferential
        (R := R) (σ := σ) d n ≫
      (coordinateHomogeneousLaurentOrderedCechObjectIso
        (R := R) (σ := σ) d (n + 1)).hom := by
  rw [coordinateHomogeneousLaurentOrderedCechDifferential,
    coordinateHyperplaneTwistOrderedBaseCechDifferential,
    Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro k _
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    coordinateHomogeneousLaurentOrderedCechCoface_naturality]

/-- Consecutive homogeneous-weight differentials compose to zero. -/
theorem coordinateHomogeneousLaurentOrderedCechDifferential_comp
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d n ≫
      coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d (n + 1) = 0 := by
  apply (cancel_epi
    (coordinateHomogeneousLaurentOrderedCechObjectIso
      (R := R) (σ := σ) d n).hom).1
  rw [Limits.comp_zero, ← Category.assoc,
    coordinateHomogeneousLaurentOrderedCechDifferential_naturality,
    Category.assoc,
    coordinateHomogeneousLaurentOrderedCechDifferential_naturality,
    ← Category.assoc,
    coordinateHyperplaneTwistOrderedBaseCechDifferential_comp (R := R) j d n,
    Limits.zero_comp]

/-- The homogeneous-weight presentation of the ordered Cech complex for `O(d)`. -/
noncomputable def coordinateHomogeneousLaurentOrderedCechComplex
    [LinearOrder σ] (j : σ) (d : ℤ) :
    CochainComplex
      (ModuleCat.{u} Γ(Spec (CommRingCat.of R),
        (⊤ : (Spec (CommRingCat.of R)).Opens))) ℕ :=
  CochainComplex.of
    (coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d)
    (coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) d)
    (coordinateHomogeneousLaurentOrderedCechDifferential_comp
      (R := R) j d)

@[simp]
theorem coordinateHomogeneousLaurentOrderedCechComplex_X
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    (coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) j d).X n =
      coordinateHomogeneousLaurentOrderedCechObject
        (R := R) (σ := σ) d n := rfl

@[simp]
theorem coordinateHomogeneousLaurentOrderedCechComplex_d
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    (coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) j d).d n (n + 1) =
      coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d n := by
  simp [coordinateHomogeneousLaurentOrderedCechComplex]

/-- The geometric coordinate Cech complex for `O(d)` is isomorphic to its homogeneous-weight
presentation. -/
noncomputable def coordinateHomogeneousLaurentOrderedCechComplexIso
    [LinearOrder σ] (j : σ) (d : ℤ) :
    coordinateHyperplaneTwistOrderedBaseCechComplex (R := R) j d ≅
      coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => coordinateHomogeneousLaurentOrderedCechObjectIso
      (R := R) (σ := σ) d n) (by
        intro n m hnm
        simp only [ComplexShape.up_Rel] at hnm
        subst m
        rw [coordinateHyperplaneTwistOrderedBaseCechComplex_d,
          coordinateHomogeneousLaurentOrderedCechComplex_d]
        exact coordinateHomogeneousLaurentOrderedCechDifferential_naturality
          (R := R) d n)

@[simp]
theorem coordinateHomogeneousLaurentOrderedCechComplexIso_hom_f
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    (coordinateHomogeneousLaurentOrderedCechComplexIso
      (R := R) j d).hom.f n =
      (coordinateHomogeneousLaurentOrderedCechObjectIso
        (R := R) (σ := σ) d n).hom := rfl

end

end MvPolynomial

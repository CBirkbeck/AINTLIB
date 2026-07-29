/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistCechWeights
import ModularCurves.ForMathlib.OrderedCechSupportContraction

/-!
# Fixed-weight components of the projective twist Cech complex

This file identifies each global homogeneous Laurent weight in the ordered projective twist Cech
complex with the ordered support-restricted complex used in the Stacks Project computation of the
cohomology of projective space.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

local instance : DecidableEq σ := Classical.decEq σ

private abbrev coordinateBaseRing (R : Type u) [CommRing R] :=
  Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))

/-- The negative coordinates of a global homogeneous Laurent exponent, lifted to the ordered-Cech
index universe. -/
def HomogeneousLaurentExponent.liftedNegativeSupport {d : ℤ}
    (e : HomogeneousLaurentExponent σ d) : Set (ULift.{u} σ) :=
  {i | e.1 i.down < 0}

/-- A global homogeneous Laurent exponent is allowed on an ordered tuple exactly when that tuple
contains every coordinate on which the exponent is negative. -/
theorem HomogeneousLaurentExponent.isAllowedOn_iff_liftedNegativeSupport_subset
    [LinearOrder σ] {d : ℤ} (e : HomogeneousLaurentExponent σ d) {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    e.IsAllowedOn (fun k => (a.1 k).down) ↔
      e.liftedNegativeSupport ⊆ Set.range a.1 := by
  constructor
  · intro h i hi
    obtain ⟨k, hk⟩ := h hi
    refine ⟨k, ?_⟩
    apply ULift.ext
    exact hk
  · intro h i hi
    obtain ⟨k, hk⟩ := h (show e.1 (ULift.up i).down < 0 by exact hi)
    refine ⟨k, ?_⟩
    exact congrArg ULift.down hk

/-- A Cech deletion map preserves the coefficient of every allowed global homogeneous weight. -/
@[simp]
theorem coordinateHomogeneousLaurentDeleteLinearMap_coeff
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) (d : ℤ)
    (e : {e : HomogeneousLaurentExponent σ d //
      e.IsAllowedOn (fun l => ((a.delete k).1 l).down)})
    (x : AddMonoidAlgebra
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      {e : HomogeneousLaurentExponent σ d //
        e.IsAllowedOn (fun l => ((a.delete k).1 l).down)}) :
    (coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k d x).coeff
        (coordinateLaurentExponentDeleteEmbedding a k d e) = x.coeff e := by
  rw [coordinateHomogeneousLaurentDeleteLinearMap,
    AddMonoidAlgebra.coeff_mapDomainLinearMap,
    Finsupp.mapDomain_apply (coordinateLaurentExponentDeleteEmbedding a k d).injective]

private abbrev coordinateHomogeneousLaurentWeightFactor
    [LinearOrder σ] (d : ℤ) {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    ModuleCat.{u} (coordinateBaseRing R) :=
  ModuleCat.of (coordinateBaseRing R)
    (AddMonoidAlgebra (coordinateBaseRing R)
      {e : HomogeneousLaurentExponent σ d //
        e.IsAllowedOn (fun k => (a.1 k).down)})

private noncomputable def coordinateHomogeneousLaurentWeightProjection
    [LinearOrder σ] (d : ℤ) {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n ⟶
      coordinateHomogeneousLaurentWeightFactor (R := R) d a :=
  Pi.π _ a

private noncomputable def coordinateHomogeneousLaurentWeightFactorCoefficient
    [LinearOrder σ] (d : ℤ) (e : HomogeneousLaurentExponent σ d) {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    coordinateHomogeneousLaurentWeightFactor (R := R) d a ⟶
      ModuleCat.of (coordinateBaseRing R) (coordinateBaseRing R) := by
  classical
  exact if h : e.IsAllowedOn (fun k => (a.1 k).down) then
    ModuleCat.ofHom ((Finsupp.lapply (R := coordinateBaseRing R)
      (M := coordinateBaseRing R)
      (⟨e, h⟩ : {e : HomogeneousLaurentExponent σ d //
        e.IsAllowedOn (fun k => (a.1 k).down)})).comp
      (AddMonoidAlgebra.coeffLinearEquiv
      (coordinateBaseRing R)).toLinearMap)
  else 0

private theorem coordinateHomogeneousLaurentWeightFactorCoefficient_delete
    [LinearOrder σ] {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) (d : ℤ) (e : HomogeneousLaurentExponent σ d) :
    ModuleCat.ofHom (coordinateHomogeneousLaurentDeleteLinearMap
        (R := R) a k d) ≫
      coordinateHomogeneousLaurentWeightFactorCoefficient
        (R := R) d e a =
    coordinateHomogeneousLaurentWeightFactorCoefficient
      (R := R) d e (a.delete k) := by
  classical
  by_cases hdelete : e.IsAllowedOn (fun l => ((a.delete k).1 l).down)
  · have hfull : e.IsAllowedOn (fun l => (a.1 l).down) :=
      (coordinateLaurentExponentDeleteEmbedding a k d
        (⟨e, hdelete⟩ : {e : HomogeneousLaurentExponent σ d //
          e.IsAllowedOn (fun l => ((a.delete k).1 l).down)})).2
    rw [coordinateHomogeneousLaurentWeightFactorCoefficient,
      dif_pos hfull,
      coordinateHomogeneousLaurentWeightFactorCoefficient,
      dif_pos hdelete]
    apply ModuleCat.hom_ext
    apply AddMonoidAlgebra.lhom_ext'
    intro f
    apply LinearMap.ext
    intro r
    by_cases hf : f = ⟨e, hdelete⟩
    · subst f
      have hembed : coordinateLaurentExponentDeleteEmbedding a k d
          (⟨e, hdelete⟩ : {e : HomogeneousLaurentExponent σ d //
            e.IsAllowedOn (fun l => ((a.delete k).1 l).down)}) =
          (⟨e, hfull⟩ : {e : HomogeneousLaurentExponent σ d //
            e.IsAllowedOn (fun l => (a.1 l).down)}) := by
        rfl
      simp [hembed]
    · have hne : coordinateLaurentExponentDeleteEmbedding a k d f ≠
          (⟨e, hfull⟩ : {e : HomogeneousLaurentExponent σ d //
            e.IsAllowedOn (fun l => (a.1 l).down)}) := by
        intro h
        apply hf
        apply Subtype.ext
        exact congrArg
          (fun x : {e : HomogeneousLaurentExponent σ d //
            e.IsAllowedOn (fun l => (a.1 l).down)} => x.1) h
      simp [hne, hf]
  · by_cases hfull : e.IsAllowedOn (fun l => (a.1 l).down)
    · rw [coordinateHomogeneousLaurentWeightFactorCoefficient,
        dif_pos hfull,
        coordinateHomogeneousLaurentWeightFactorCoefficient,
        dif_neg hdelete]
      apply ModuleCat.hom_ext
      apply AddMonoidAlgebra.lhom_ext'
      intro f
      apply LinearMap.ext
      intro r
      have hne : coordinateLaurentExponentDeleteEmbedding a k d f ≠
          (⟨e, hfull⟩ : {e : HomogeneousLaurentExponent σ d //
            e.IsAllowedOn (fun l => (a.1 l).down)}) := by
        intro h
        apply hdelete
        have hfe : f.1 = e := congrArg Subtype.val h
        rw [← hfe]
        exact f.2
      simp [hne]
    · simp [coordinateHomogeneousLaurentWeightFactorCoefficient,
        hdelete, hfull]

private noncomputable def coordinateHomogeneousLaurentWeightCoefficientProjection
    [LinearOrder σ] (d : ℤ) (e : HomogeneousLaurentExponent σ d) {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n ⟶
      ModuleCat.of (coordinateBaseRing R) (coordinateBaseRing R) := by
  classical
  exact coordinateHomogeneousLaurentWeightProjection (R := R) d a ≫
    coordinateHomogeneousLaurentWeightFactorCoefficient (R := R) d e a

private theorem coordinateHomogeneousLaurentOrderedCechCoface_comp_weightCoefficient
    [LinearOrder σ] (d : ℤ) (e : HomogeneousLaurentExponent σ d)
    (n : ℕ) (k : Fin (n + 2))
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    coordinateHomogeneousLaurentOrderedCechCoface
        (R := R) (σ := σ) d n k ≫
      coordinateHomogeneousLaurentWeightCoefficientProjection
        (R := R) d e a =
  coordinateHomogeneousLaurentWeightCoefficientProjection
      (R := R) d e (a.delete k) := by
  unfold coordinateHomogeneousLaurentWeightCoefficientProjection
  rw [← Category.assoc]
  unfold coordinateHomogeneousLaurentWeightProjection
  rw [coordinateHomogeneousLaurentOrderedCechCoface_comp_π]
  erw [Category.assoc]
  rw [coordinateHomogeneousLaurentWeightFactorCoefficient_delete]

private theorem coordinateHomogeneousLaurentOrderedCechCoface_weightCoefficient_apply
    [LinearOrder σ] (d : ℤ) (e : HomogeneousLaurentExponent σ d)
    (n : ℕ) (k : Fin (n + 2))
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (x : coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d n) :
    (coordinateHomogeneousLaurentWeightCoefficientProjection
        (R := R) d e a).hom
      ((coordinateHomogeneousLaurentOrderedCechCoface
        (R := R) (σ := σ) d n k).hom x) =
    (coordinateHomogeneousLaurentWeightCoefficientProjection
      (R := R) d e (a.delete k)).hom x := by
  have h := congrArg (fun f => f.hom x)
    (coordinateHomogeneousLaurentOrderedCechCoface_comp_weightCoefficient
      (R := R) d e n k a)
  exact h

@[simp]
private theorem coordinateHomogeneousLaurentWeightCoefficientProjection_apply_of_allowed
    [LinearOrder σ] (d : ℤ) (e : HomogeneousLaurentExponent σ d) {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n)
    (h : e.IsAllowedOn (fun k => (a.1 k).down))
    (x : coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d n) :
    (coordinateHomogeneousLaurentWeightCoefficientProjection
      (R := R) d e a).hom x =
      ((coordinateHomogeneousLaurentWeightProjection
        (R := R) d a).hom x).coeff
          (⟨e, h⟩ : {e : HomogeneousLaurentExponent σ d //
            e.IsAllowedOn (fun k => (a.1 k).down)}) := by
  simp [coordinateHomogeneousLaurentWeightCoefficientProjection,
    coordinateHomogeneousLaurentWeightFactorCoefficient, h]

@[simp]
private theorem coordinateHomogeneousLaurentWeightCoefficientProjection_apply_of_not_allowed
    [LinearOrder σ] (d : ℤ) (e : HomogeneousLaurentExponent σ d) {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n)
    (h : ¬e.IsAllowedOn (fun k => (a.1 k).down))
    (x : coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d n) :
    (coordinateHomogeneousLaurentWeightCoefficientProjection
      (R := R) d e a).hom x = 0 := by
  simp [coordinateHomogeneousLaurentWeightCoefficientProjection,
    coordinateHomogeneousLaurentWeightFactorCoefficient, h]

/-- Project a homogeneous-weight Cech cochain onto one global Laurent weight. Its values form a
support-restricted ordered Cech cochain indexed by the negative support of that weight. -/
noncomputable def coordinateHomogeneousLaurentWeightComponent
    [LinearOrder σ] (d : ℤ) (e : HomogeneousLaurentExponent σ d) (n : ℕ) :
    coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n →ₗ[
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))]
      ModularCurves.OrderedCechSupportCochain
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        e.liftedNegativeSupport n := by
  classical
  exact
    { toFun := fun x =>
        ⟨fun a =>
            (coordinateHomogeneousLaurentWeightCoefficientProjection
              (R := R) d e a).hom x,
          fun a ha => by
            have hnot : ¬e.IsAllowedOn (fun k => (a.1 k).down) :=
              fun h => ha ((e.isAllowedOn_iff_liftedNegativeSupport_subset a).mp h)
            simp [coordinateHomogeneousLaurentWeightCoefficientProjection,
              coordinateHomogeneousLaurentWeightFactorCoefficient, hnot]⟩
      map_add' := fun x y => by
        apply Subtype.ext
        funext a
        simp
      map_smul' := fun r x => by
        apply Subtype.ext
        funext a
        simp }

@[simp]
private theorem coordinateHomogeneousLaurentWeightComponent_apply
    [LinearOrder σ] (d : ℤ) (e : HomogeneousLaurentExponent σ d) (n : ℕ)
    (x : coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d n)
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    (coordinateHomogeneousLaurentWeightComponent
      (R := R) d e n x).1 a =
      (coordinateHomogeneousLaurentWeightCoefficientProjection
        (R := R) d e a).hom x := rfl

/-- On a tuple allowing `e`, the `e`-component is the corresponding Laurent coefficient. -/
theorem coordinateHomogeneousLaurentWeightComponent_apply_of_allowed
    [LinearOrder σ] (d : ℤ) (e : HomogeneousLaurentExponent σ d) {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n)
    (h : e.IsAllowedOn (fun k => (a.1 k).down))
    (x : coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d n) :
    (coordinateHomogeneousLaurentWeightComponent (R := R) d e n x).1 a =
      ((Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
        ModuleCat.of
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          (AddMonoidAlgebra
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            {e : HomogeneousLaurentExponent σ d //
              e.IsAllowedOn (fun k => (b.1 k).down)})) a).hom x).coeff
        (⟨e, h⟩ : {e : HomogeneousLaurentExponent σ d //
          e.IsAllowedOn (fun k => (a.1 k).down)}) := by
  rw [coordinateHomogeneousLaurentWeightComponent_apply,
    coordinateHomogeneousLaurentWeightCoefficientProjection_apply_of_allowed (h := h)]
  rfl

/-- On a tuple not allowing `e`, the `e`-component vanishes. -/
theorem coordinateHomogeneousLaurentWeightComponent_apply_of_not_allowed
    [LinearOrder σ] (d : ℤ) (e : HomogeneousLaurentExponent σ d) {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n)
    (h : ¬e.IsAllowedOn (fun k => (a.1 k).down))
    (x : coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d n) :
    (coordinateHomogeneousLaurentWeightComponent (R := R) d e n x).1 a = 0 := by
  rw [coordinateHomogeneousLaurentWeightComponent_apply,
    coordinateHomogeneousLaurentWeightCoefficientProjection_apply_of_not_allowed (h := h)]

private def orderedCechSupportEvaluation
    [LinearOrder σ] (d : ℤ) (e : HomogeneousLaurentExponent σ d) (n : ℕ)
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    ModularCurves.OrderedCechSupportCochain (coordinateBaseRing R)
        e.liftedNegativeSupport n →ₗ[coordinateBaseRing R]
      coordinateBaseRing R where
  toFun s := s.1 a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def coordinateHomogeneousLaurentWeightSingle
    [LinearOrder σ] (d : ℤ) (e : HomogeneousLaurentExponent σ d) {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :
    ModuleCat.of (coordinateBaseRing R)
        (ModularCurves.OrderedCechSupportCochain (coordinateBaseRing R)
          e.liftedNegativeSupport n) ⟶
      coordinateHomogeneousLaurentWeightFactor (R := R) d a := by
  classical
  exact if h : e.IsAllowedOn (fun k => (a.1 k).down) then
    ModuleCat.ofHom ((AddMonoidAlgebra.lsingle (R := coordinateBaseRing R)
      (⟨e, h⟩ : {e : HomogeneousLaurentExponent σ d //
        e.IsAllowedOn (fun k => (a.1 k).down)})).comp
      (orderedCechSupportEvaluation (R := R) d e n a))
  else 0

@[simp]
private theorem coordinateHomogeneousLaurentWeightSingle_apply_of_allowed
    [LinearOrder σ] (d : ℤ) (e : HomogeneousLaurentExponent σ d) {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n)
    (h : e.IsAllowedOn (fun k => (a.1 k).down))
    (s : ModularCurves.OrderedCechSupportCochain (coordinateBaseRing R)
      e.liftedNegativeSupport n) :
    (coordinateHomogeneousLaurentWeightSingle
      (R := R) d e a).hom s =
      AddMonoidAlgebra.single
        (⟨e, h⟩ : {e : HomogeneousLaurentExponent σ d //
          e.IsAllowedOn (fun k => (a.1 k).down)}) (s.1 a) := by
  simp [coordinateHomogeneousLaurentWeightSingle,
    orderedCechSupportEvaluation, h]

@[simp]
private theorem coordinateHomogeneousLaurentWeightSingle_apply_of_not_allowed
    [LinearOrder σ] (d : ℤ) (e : HomogeneousLaurentExponent σ d) {n : ℕ}
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n)
    (h : ¬e.IsAllowedOn (fun k => (a.1 k).down))
    (s : ModularCurves.OrderedCechSupportCochain (coordinateBaseRing R)
      e.liftedNegativeSupport n) :
    (coordinateHomogeneousLaurentWeightSingle
      (R := R) d e a).hom s = 0 := by
  simp [coordinateHomogeneousLaurentWeightSingle, h]

/-- Insert a support-restricted ordered Cech cochain as one global Laurent weight in the
homogeneous-weight Cech term. -/
noncomputable def coordinateHomogeneousLaurentWeightInclusion
    [LinearOrder σ] (d : ℤ) (e : HomogeneousLaurentExponent σ d) (n : ℕ) :
    ModularCurves.OrderedCechSupportCochain
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        e.liftedNegativeSupport n →ₗ[
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))]
      coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n := by
  classical
  exact (Pi.lift fun a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
    coordinateHomogeneousLaurentWeightSingle (R := R) d e a).hom

private theorem coordinateHomogeneousLaurentWeightProjection_inclusion_apply
    [LinearOrder σ] (d : ℤ) (e : HomogeneousLaurentExponent σ d) (n : ℕ)
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n)
    (s : ModularCurves.OrderedCechSupportCochain (coordinateBaseRing R)
      e.liftedNegativeSupport n) :
    (coordinateHomogeneousLaurentWeightProjection (R := R) d a).hom
        (coordinateHomogeneousLaurentWeightInclusion
          (R := R) d e n s) =
      (coordinateHomogeneousLaurentWeightSingle
        (R := R) d e a).hom s := by
  classical
  unfold coordinateHomogeneousLaurentWeightInclusion
  unfold coordinateHomogeneousLaurentWeightProjection
  have h := congrArg (fun f => f.hom s)
    (Pi.lift_π
      (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
        coordinateHomogeneousLaurentWeightSingle (R := R) d e b) a)
  exact h

/-- Projecting a cochain immediately after inserting it at the same weight is the identity. -/
theorem coordinateHomogeneousLaurentWeightComponent_inclusion
    [LinearOrder σ] (d : ℤ) (e : HomogeneousLaurentExponent σ d) (n : ℕ)
    (s : ModularCurves.OrderedCechSupportCochain
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      e.liftedNegativeSupport n) :
    coordinateHomogeneousLaurentWeightComponent (R := R) d e n
        (coordinateHomogeneousLaurentWeightInclusion
          (R := R) d e n s) = s := by
  apply Subtype.ext
  funext a
  by_cases h : e.IsAllowedOn (fun k => (a.1 k).down)
  · rw [coordinateHomogeneousLaurentWeightComponent_apply,
      coordinateHomogeneousLaurentWeightCoefficientProjection_apply_of_allowed (h := h),
      coordinateHomogeneousLaurentWeightProjection_inclusion_apply,
      coordinateHomogeneousLaurentWeightSingle_apply_of_allowed (h := h)]
    simp
  · rw [coordinateHomogeneousLaurentWeightComponent_apply,
      coordinateHomogeneousLaurentWeightCoefficientProjection_apply_of_not_allowed (h := h)]
    have hsupport : ¬e.liftedNegativeSupport ⊆ Set.range a.1 :=
      fun hs => h ((e.isAllowedOn_iff_liftedNegativeSupport_subset a).2 hs)
    exact (s.2 a hsupport).symm

/-- Inserting one global Laurent weight has zero component at every distinct weight. -/
theorem coordinateHomogeneousLaurentWeightComponent_inclusion_ne
    [LinearOrder σ] (d : ℤ)
    (e f : HomogeneousLaurentExponent σ d) (hef : f ≠ e) (n : ℕ)
    (s : ModularCurves.OrderedCechSupportCochain
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      e.liftedNegativeSupport n) :
    coordinateHomogeneousLaurentWeightComponent (R := R) d f n
        (coordinateHomogeneousLaurentWeightInclusion
          (R := R) d e n s) = 0 := by
  apply Subtype.ext
  funext a
  by_cases hf : f.IsAllowedOn (fun k => (a.1 k).down)
  · rw [coordinateHomogeneousLaurentWeightComponent_apply,
      coordinateHomogeneousLaurentWeightCoefficientProjection_apply_of_allowed (h := hf),
      coordinateHomogeneousLaurentWeightProjection_inclusion_apply]
    by_cases he : e.IsAllowedOn (fun k => (a.1 k).down)
    · rw [coordinateHomogeneousLaurentWeightSingle_apply_of_allowed (h := he)]
      have hne :
          (⟨e, he⟩ : {e : HomogeneousLaurentExponent σ d //
            e.IsAllowedOn (fun k => (a.1 k).down)}) ≠
          (⟨f, hf⟩ : {e : HomogeneousLaurentExponent σ d //
            e.IsAllowedOn (fun k => (a.1 k).down)}) := by
        intro h
        exact hef (congrArg Subtype.val h).symm
      simp [hne]
    · rw [coordinateHomogeneousLaurentWeightSingle_apply_of_not_allowed (h := he)]
      rfl
  · rw [coordinateHomogeneousLaurentWeightComponent_apply,
      coordinateHomogeneousLaurentWeightCoefficientProjection_apply_of_not_allowed (h := hf)]
    rfl

/-- Fixed-weight projection commutes with the alternating ordered Cech differentials. -/
theorem coordinateHomogeneousLaurentWeightComponent_differential
    [LinearOrder σ] (d : ℤ) (e : HomogeneousLaurentExponent σ d) (n : ℕ)
    (x : coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d n) :
    coordinateHomogeneousLaurentWeightComponent (R := R) d e (n + 1)
        ((coordinateHomogeneousLaurentOrderedCechDifferential
          (R := R) (σ := σ) d n).hom x) =
      ModularCurves.orderedCechSupportDifferential
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        e.liftedNegativeSupport n
        (coordinateHomogeneousLaurentWeightComponent
          (R := R) d e n x) := by
  apply Subtype.ext
  funext a
  simp only [coordinateHomogeneousLaurentOrderedCechDifferential,
    Int.reduceNeg, ModuleCat.hom_sum, ModuleCat.hom_smul, LinearMap.coe_sum,
    LinearMap.coe_smul, Finset.sum_apply, Pi.smul_apply, map_sum,
    LinearMap.map_smul_of_tower, AddSubmonoidClass.coe_finsetSum,
    SetLike.val_smul_of_tower, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply,
    coordinateHomogeneousLaurentWeightComponent_apply,
    ModularCurves.orderedCechSupportDifferential, LinearMap.coe_mk,
    AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro k _
  rw [coordinateHomogeneousLaurentOrderedCechCoface_weightCoefficient_apply]

/-- Fixed-weight inclusion commutes with the alternating ordered Cech differentials. -/
theorem coordinateHomogeneousLaurentWeightInclusion_differential
    [LinearOrder σ] (d : ℤ) (e : HomogeneousLaurentExponent σ d) (n : ℕ)
    (s : ModularCurves.OrderedCechSupportCochain
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      e.liftedNegativeSupport n) :
    (coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d n).hom
      (coordinateHomogeneousLaurentWeightInclusion
        (R := R) d e n s) =
    coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
      (ModularCurves.orderedCechSupportDifferential
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        e.liftedNegativeSupport n s) := by
  apply Concrete.limit_ext (Discrete.functor fun
    a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1) =>
      coordinateHomogeneousLaurentWeightFactor (R := R) d a)
  intro a
  rcases a with ⟨a⟩
  change
    (coordinateHomogeneousLaurentWeightProjection (R := R) d a).hom
        ((coordinateHomogeneousLaurentOrderedCechDifferential
          (R := R) (σ := σ) d n).hom
            (coordinateHomogeneousLaurentWeightInclusion
              (R := R) d e n s)) =
      (coordinateHomogeneousLaurentWeightProjection (R := R) d a).hom
        (coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
          (ModularCurves.orderedCechSupportDifferential
            (coordinateBaseRing R) e.liftedNegativeSupport n s))
  apply AddMonoidAlgebra.coeff_injective
  ext f
  have hf : f.1.IsAllowedOn (fun k => (a.1 k).down) := f.2
  have hleft :
      ((coordinateHomogeneousLaurentWeightProjection (R := R) d a).hom
        ((coordinateHomogeneousLaurentOrderedCechDifferential
          (R := R) (σ := σ) d n).hom
            (coordinateHomogeneousLaurentWeightInclusion
              (R := R) d e n s))).coeff f =
        (coordinateHomogeneousLaurentWeightComponent (R := R) d f.1 (n + 1)
          ((coordinateHomogeneousLaurentOrderedCechDifferential
            (R := R) (σ := σ) d n).hom
              (coordinateHomogeneousLaurentWeightInclusion
                (R := R) d e n s))).1 a := by
    rw [coordinateHomogeneousLaurentWeightComponent_apply,
      coordinateHomogeneousLaurentWeightCoefficientProjection_apply_of_allowed
        (h := hf)]
  have hright :
      ((coordinateHomogeneousLaurentWeightProjection (R := R) d a).hom
        (coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
          (ModularCurves.orderedCechSupportDifferential
            (coordinateBaseRing R) e.liftedNegativeSupport n s))).coeff f =
        (coordinateHomogeneousLaurentWeightComponent (R := R) d f.1 (n + 1)
          (coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
            (ModularCurves.orderedCechSupportDifferential
              (coordinateBaseRing R) e.liftedNegativeSupport n s))).1 a := by
    rw [coordinateHomogeneousLaurentWeightComponent_apply,
      coordinateHomogeneousLaurentWeightCoefficientProjection_apply_of_allowed
        (h := hf)]
  rw [hleft, hright,
    coordinateHomogeneousLaurentWeightComponent_differential]
  by_cases hfe : f.1 = e
  · subst e
    rw [coordinateHomogeneousLaurentWeightComponent_inclusion,
      coordinateHomogeneousLaurentWeightComponent_inclusion]
  · rw [coordinateHomogeneousLaurentWeightComponent_inclusion_ne
        (hef := hfe),
      map_zero,
      coordinateHomogeneousLaurentWeightComponent_inclusion_ne
        (hef := hfe)]

end

end MvPolynomial

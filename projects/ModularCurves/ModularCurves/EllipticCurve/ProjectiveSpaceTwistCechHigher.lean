/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.AlgebraicGeometry.Noetherian
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistCechWeightAssembly
import ModularCurves.ForMathlib.OrderedCechSupportAlternating

/-!
# Higher exactness for nonnegative projective twists

This file assembles the all-degree support contraction from
[Stacks Project, Lemma 30.8.1 (Tag 01XT)](https://stacks.math.columbia.edu/tag/01XT) weight by
weight in the homogeneous Laurent presentation of the ordered Cech complex.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

local instance : DecidableEq σ := Classical.decEq σ

/-- For fixed total degree and finitely many coordinates, there are only finitely many homogeneous
Laurent exponents that are negative in every coordinate. -/
theorem HomogeneousLaurentExponent.finite_setOf_liftedNegativeSupport_eq_univ
    [Fintype σ] (d : ℤ) :
    {e : HomogeneousLaurentExponent σ d |
      e.liftedNegativeSupport = Set.univ}.Finite := by
  classical
  apply Set.Finite.of_finite_image
      (f := fun e : HomogeneousLaurentExponent σ d => (e.1 : σ → ℤ))
  · apply (Set.Finite.pi' fun _ => Set.finite_Icc d (-1)).subset
    rintro f ⟨e, he, rfl⟩
    intro i
    have hneg (j : σ) : e.1 j < 0 := by
      have hj : ULift.up j ∈ e.liftedNegativeSupport := by
        rw [he]
        exact Set.mem_univ _
      exact hj
    have hrest : ∑ j ∈ Finset.univ.erase i, e.1 j ≤ 0 := by
      apply Finset.sum_nonpos
      intro j _
      exact (hneg j).le
    have hsum : ∑ j, e.1 j = d := by
      rw [← Finsupp.degree_eq_sum]
      exact e.2
    have hi : i ∈ (Finset.univ : Finset σ) := Finset.mem_univ i
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset σ)
      (fun j => e.1 j) hi
    simp only [Set.mem_Icc]
    constructor
    · omega
    · have := hneg i
      omega
  · intro e _ f _ hef
    apply Subtype.ext
    ext i
    exact congrFun hef i

/-- The finite product of support cochains indexed by the homogeneous Laurent exponents that are
negative in every coordinate. -/
abbrev coordinateHomogeneousLaurentFullNegativeCochain
    [LinearOrder σ] (d : ℤ) (n : ℕ) :=
  (e : {e : HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))}) →
    ModularCurves.OrderedCechSupportCochain
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      e.1.liftedNegativeSupport n

/-- Full-negative homogeneous Laurent cochains form a finite module over a Noetherian affine
coefficient ring. -/
theorem coordinateHomogeneousLaurentFullNegativeCochain.module_finite
    [Fintype σ] [LinearOrder σ] [IsNoetherianRing R] (d : ℤ) (n : ℕ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (coordinateHomogeneousLaurentFullNegativeCochain
        (R := R) (σ := σ) d n) := by
  letI : IsNoetherianRing
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)) :=
    isNoetherianRing_of_ringEquiv R
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  letI : Finite {e : HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))} :=
    (HomogeneousLaurentExponent.finite_setOf_liftedNegativeSupport_eq_univ
      (σ := σ) d).to_subtype
  letI (e : {e : HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))}) :
      Module.Finite
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (ModularCurves.OrderedCechSupportCochain
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          e.1.liftedNegativeSupport n) :=
    ModularCurves.OrderedCechSupportCochain.module_finite _ _ _
  infer_instance

/-- Assemble the finitely many full-negative homogeneous Laurent weights into the ordered Cech
term. -/
noncomputable def coordinateHomogeneousLaurentFullNegativeAssembly
    [Fintype σ] [LinearOrder σ] (d : ℤ) (n : ℕ) :
    coordinateHomogeneousLaurentFullNegativeCochain
        (R := R) (σ := σ) d n →ₗ[
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))]
      coordinateHomogeneousLaurentOrderedCechObject
        (R := R) (σ := σ) d n := by
  classical
  letI : Fintype {e : HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))} :=
    (HomogeneousLaurentExponent.finite_setOf_liftedNegativeSupport_eq_univ
      (σ := σ) d).fintype
  exact LinearMap.lsum
    Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
    (fun e : {e : HomogeneousLaurentExponent σ d //
        e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))} =>
      ModularCurves.OrderedCechSupportCochain
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        e.1.liftedNegativeSupport n)
    Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
    (fun e => coordinateHomogeneousLaurentWeightInclusion
      (R := R) d e.1 n)

/-- Full-negative assembly is the finite sum of the fixed-weight inclusions. -/
theorem coordinateHomogeneousLaurentFullNegativeAssembly_apply
    [Fintype σ] [LinearOrder σ] (d : ℤ) (n : ℕ)
    (s : coordinateHomogeneousLaurentFullNegativeCochain
      (R := R) (σ := σ) d n) :
    letI : Fintype {e : HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))} :=
    (HomogeneousLaurentExponent.finite_setOf_liftedNegativeSupport_eq_univ
      (σ := σ) d).fintype
    coordinateHomogeneousLaurentFullNegativeAssembly
        (R := R) (σ := σ) d n s =
      ∑ e : {e : HomogeneousLaurentExponent σ d //
          e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))},
        coordinateHomogeneousLaurentWeightInclusion
          (R := R) d e.1 n (s e) := by
  classical
  simp [coordinateHomogeneousLaurentFullNegativeAssembly, LinearMap.lsum_apply]

/-- The componentwise ordered support differential on full-negative homogeneous Laurent
cochains. -/
noncomputable def coordinateHomogeneousLaurentFullNegativeDifferential
    [LinearOrder σ] (d : ℤ) (n : ℕ) :
    coordinateHomogeneousLaurentFullNegativeCochain
        (R := R) (σ := σ) d n →ₗ[
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))]
      coordinateHomogeneousLaurentFullNegativeCochain
        (R := R) (σ := σ) d (n + 1) :=
  LinearMap.pi fun e =>
    (ModularCurves.orderedCechSupportDifferential
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      e.1.liftedNegativeSupport n).comp (LinearMap.proj e)

@[simp]
theorem coordinateHomogeneousLaurentFullNegativeDifferential_apply
    [LinearOrder σ] (d : ℤ) (n : ℕ)
    (s : coordinateHomogeneousLaurentFullNegativeCochain
      (R := R) (σ := σ) d n)
    (e : {e : HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))}) :
    coordinateHomogeneousLaurentFullNegativeDifferential
        (R := R) d n s e =
      ModularCurves.orderedCechSupportDifferential
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        e.1.liftedNegativeSupport n (s e) := rfl

/-- Full-negative assembly commutes with the homogeneous Laurent ordered Cech differential. -/
theorem coordinateHomogeneousLaurentFullNegativeAssembly_differential
    [Fintype σ] [LinearOrder σ] (d : ℤ) (n : ℕ)
    (s : coordinateHomogeneousLaurentFullNegativeCochain
      (R := R) (σ := σ) d n) :
    (coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) d n).hom
        (coordinateHomogeneousLaurentFullNegativeAssembly
          (R := R) (σ := σ) d n s) =
      coordinateHomogeneousLaurentFullNegativeAssembly
        (R := R) (σ := σ) d (n + 1)
        (coordinateHomogeneousLaurentFullNegativeDifferential
          (R := R) d n s) := by
  classical
  letI : Fintype {e : HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))} :=
    (HomogeneousLaurentExponent.finite_setOf_liftedNegativeSupport_eq_univ
      (σ := σ) d).fintype
  have hleft :
      (coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d n).hom
          (coordinateHomogeneousLaurentFullNegativeAssembly
            (R := R) (σ := σ) d n s) =
        ∑ e : {e : HomogeneousLaurentExponent σ d //
            e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))},
          (coordinateHomogeneousLaurentOrderedCechDifferential
            (R := R) (σ := σ) d n).hom
            (coordinateHomogeneousLaurentWeightInclusion
              (R := R) d e.1 n (s e)) := by
    rw [coordinateHomogeneousLaurentFullNegativeAssembly_apply, map_sum]
  have hright :
      coordinateHomogeneousLaurentFullNegativeAssembly
          (R := R) (σ := σ) d (n + 1)
          (coordinateHomogeneousLaurentFullNegativeDifferential
            (R := R) d n s) =
        ∑ e : {e : HomogeneousLaurentExponent σ d //
            e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))},
          coordinateHomogeneousLaurentWeightInclusion
            (R := R) d e.1 (n + 1)
            (coordinateHomogeneousLaurentFullNegativeDifferential
              (R := R) d n s e) := by
    rw [coordinateHomogeneousLaurentFullNegativeAssembly_apply]
  rw [hleft, hright]
  apply Finset.sum_congr rfl
  intro e _
  rw [coordinateHomogeneousLaurentWeightInclusion_differential
    (R := R) (σ := σ) (d := d) (e := e.1) (n := n),
    coordinateHomogeneousLaurentFullNegativeDifferential_apply
      (R := R) (σ := σ) (d := d) (n := n) (s := s) (e := e)]

/-- Project a homogeneous Laurent ordered Cech cochain onto all full-negative weight
components. -/
noncomputable def coordinateHomogeneousLaurentFullNegativeProjection
    [LinearOrder σ] (d : ℤ) (n : ℕ) :
    coordinateHomogeneousLaurentOrderedCechObject
        (R := R) (σ := σ) d n →ₗ[
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))]
      coordinateHomogeneousLaurentFullNegativeCochain
        (R := R) (σ := σ) d n :=
  LinearMap.pi fun e =>
    coordinateHomogeneousLaurentWeightComponent
      (R := R) d e.1 n

@[simp]
theorem coordinateHomogeneousLaurentFullNegativeProjection_apply
    [LinearOrder σ] (d : ℤ) (n : ℕ)
    (s : coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d n)
    (e : {e : HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))}) :
    coordinateHomogeneousLaurentFullNegativeProjection
        (R := R) d n s e =
      coordinateHomogeneousLaurentWeightComponent
        (R := R) d e.1 n s := rfl

/-- Projection onto the full-negative weights commutes with the ordered Cech differential. -/
theorem coordinateHomogeneousLaurentFullNegativeProjection_differential
    [LinearOrder σ] (d : ℤ) (n : ℕ)
    (s : coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d n) :
    coordinateHomogeneousLaurentFullNegativeDifferential
        (R := R) (σ := σ) d n
        (coordinateHomogeneousLaurentFullNegativeProjection
          (R := R) d n s) =
      coordinateHomogeneousLaurentFullNegativeProjection
        (R := R) d (n + 1)
        ((coordinateHomogeneousLaurentOrderedCechDifferential
          (R := R) (σ := σ) d n).hom s) := by
  ext e
  rw [coordinateHomogeneousLaurentFullNegativeDifferential_apply,
    coordinateHomogeneousLaurentFullNegativeProjection_apply,
    coordinateHomogeneousLaurentFullNegativeProjection_apply,
    coordinateHomogeneousLaurentWeightComponent_differential]

/-- The full-negative cocycles in one degree of the homogeneous Laurent ordered Cech
presentation. -/
def coordinateHomogeneousLaurentFullNegativeCycles
    [LinearOrder σ] (d : ℤ) (n : ℕ) :=
  LinearMap.ker
    (coordinateHomogeneousLaurentFullNegativeDifferential
      (R := R) (σ := σ) d n)

/-- Full-negative homogeneous Laurent cycles form a finite module over a Noetherian affine
coefficient ring. -/
theorem coordinateHomogeneousLaurentFullNegativeCycles.module_finite
    [Fintype σ] [LinearOrder σ] [IsNoetherianRing R] (d : ℤ) (n : ℕ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (coordinateHomogeneousLaurentFullNegativeCycles
        (R := R) (σ := σ) d n) := by
  letI : IsNoetherianRing
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)) :=
    isNoetherianRing_of_ringEquiv R
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  letI : Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (coordinateHomogeneousLaurentFullNegativeCochain
        (R := R) (σ := σ) d n) :=
    coordinateHomogeneousLaurentFullNegativeCochain.module_finite d n
  have hsource : IsNoetherian
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (coordinateHomogeneousLaurentFullNegativeCochain
        (R := R) (σ := σ) d n) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  letI : IsNoetherian
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (coordinateHomogeneousLaurentFullNegativeCycles
        (R := R) (σ := σ) d n) :=
    isNoetherian_of_submodule_of_noetherian _ _ _ hsource
  infer_instance

/-- Assemble a full-negative cocycle into the homogeneous Laurent ordered Cech term. -/
noncomputable def coordinateHomogeneousLaurentFullNegativeCyclesAssembly
    [Fintype σ] [LinearOrder σ] (d : ℤ) (n : ℕ) :
    coordinateHomogeneousLaurentFullNegativeCycles
        (R := R) (σ := σ) d n →ₗ[
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))]
      coordinateHomogeneousLaurentOrderedCechObject
        (R := R) (σ := σ) d n :=
  (coordinateHomogeneousLaurentFullNegativeAssembly
    (R := R) (σ := σ) d n).comp
      (coordinateHomogeneousLaurentFullNegativeCycles
        (R := R) (σ := σ) d n).subtype

/-- The assembly of a full-negative cocycle is a cocycle in the homogeneous Laurent ordered Cech
complex. -/
theorem coordinateHomogeneousLaurentFullNegativeCyclesAssembly_differential
    [Fintype σ] [LinearOrder σ] (d : ℤ) (n : ℕ)
    (s : coordinateHomogeneousLaurentFullNegativeCycles
      (R := R) (σ := σ) d n) :
    (coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) d n).hom
        (coordinateHomogeneousLaurentFullNegativeCyclesAssembly
          (R := R) (σ := σ) d n s) = 0 := by
  change
    (coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) d n).hom
        (coordinateHomogeneousLaurentFullNegativeAssembly
          (R := R) (σ := σ) d n s.1) = 0
  rw [coordinateHomogeneousLaurentFullNegativeAssembly_differential]
  have hs : coordinateHomogeneousLaurentFullNegativeDifferential
      (R := R) (σ := σ) d n s.1 = 0 := by
    simpa [coordinateHomogeneousLaurentFullNegativeCycles] using s.2
  rw [hs, map_zero]

/-- The exceptional full-negative cycles, lifted to the cycle object of the homogeneous Laurent
ordered Cech complex. -/
noncomputable def coordinateHomogeneousLaurentFullNegativeCyclesToCycles
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    ModuleCat.of
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (coordinateHomogeneousLaurentFullNegativeCycles
          (R := R) (σ := σ) d n) ⟶
      (coordinateHomogeneousLaurentOrderedCechComplex
        (R := R) j d).cycles n :=
  by
    let k : ModuleCat.of
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (coordinateHomogeneousLaurentFullNegativeCycles
          (R := R) (σ := σ) d n) ⟶
        (coordinateHomogeneousLaurentOrderedCechComplex
          (R := R) j d).X n :=
      ModuleCat.ofHom
        (coordinateHomogeneousLaurentFullNegativeCyclesAssembly
          (R := R) (σ := σ) d n)
    refine (coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) j d).liftCycles (i := n) k (n + 1) (by simp) ?_
    rw [coordinateHomogeneousLaurentOrderedCechComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact coordinateHomogeneousLaurentFullNegativeCyclesAssembly_differential
      (R := R) (σ := σ) d n s

/-- The exceptional-cycle lift followed by the cycle inclusion is the original assembly. -/
theorem coordinateHomogeneousLaurentFullNegativeCyclesToCycles_i
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    coordinateHomogeneousLaurentFullNegativeCyclesToCycles
        (R := R) j d n ≫
      (coordinateHomogeneousLaurentOrderedCechComplex
        (R := R) j d).iCycles n =
    (ModuleCat.ofHom
        (coordinateHomogeneousLaurentFullNegativeCyclesAssembly
          (R := R) (σ := σ) d n) :
      ModuleCat.of
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          (coordinateHomogeneousLaurentFullNegativeCycles
            (R := R) (σ := σ) d n) ⟶
        (coordinateHomogeneousLaurentOrderedCechComplex
          (R := R) j d).X n) := by
  let k : ModuleCat.of
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (coordinateHomogeneousLaurentFullNegativeCycles
        (R := R) (σ := σ) d n) ⟶
      (coordinateHomogeneousLaurentOrderedCechComplex
        (R := R) j d).X n :=
    ModuleCat.ofHom
      (coordinateHomogeneousLaurentFullNegativeCyclesAssembly
        (R := R) (σ := σ) d n)
  have hk : k ≫ (coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) j d).d n (n + 1) = 0 := by
    rw [coordinateHomogeneousLaurentOrderedCechComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact coordinateHomogeneousLaurentFullNegativeCyclesAssembly_differential
      (R := R) (σ := σ) d n s
  simpa only [coordinateHomogeneousLaurentFullNegativeCyclesToCycles, k] using
    (HomologicalComplex.liftCycles_i
      (coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d)
      k (n + 1) (by simp) hk)

/-- The homology class represented by an exceptional full-negative cycle. -/
noncomputable def coordinateHomogeneousLaurentFullNegativeCyclesToHomology
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    ModuleCat.of
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (coordinateHomogeneousLaurentFullNegativeCycles
          (R := R) (σ := σ) d n) ⟶
      (coordinateHomogeneousLaurentOrderedCechComplex
        (R := R) j d).homology n :=
  coordinateHomogeneousLaurentFullNegativeCyclesToCycles
      (R := R) j d n ≫
    (coordinateHomogeneousLaurentOrderedCechComplex
      (R := R) j d).homologyπ n

/-- Project a cycle in the homogeneous Laurent complex to its full-negative weight cycle. -/
noncomputable def coordinateHomogeneousLaurentCyclesToFullNegativeCycles
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    (coordinateHomogeneousLaurentOrderedCechComplex
        (R := R) j d).cycles n ⟶
      ModuleCat.of
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (coordinateHomogeneousLaurentFullNegativeCycles
          (R := R) (σ := σ) d n) :=
  by
    let p : (coordinateHomogeneousLaurentOrderedCechComplex
        (R := R) j d).cycles n ⟶ ModuleCat.of
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (coordinateHomogeneousLaurentFullNegativeCochain
          (R := R) (σ := σ) d n) :=
      (coordinateHomogeneousLaurentOrderedCechComplex
          (R := R) j d).iCycles n ≫
        ModuleCat.ofHom
          (coordinateHomogeneousLaurentFullNegativeProjection
            (R := R) d n)
    have hprojection :
        (ModuleCat.ofHom
            (coordinateHomogeneousLaurentFullNegativeProjection
              (R := R) d n) :
          coordinateHomogeneousLaurentOrderedCechObject
              (R := R) (σ := σ) d n ⟶
            ModuleCat.of
              Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
              (coordinateHomogeneousLaurentFullNegativeCochain
                (R := R) (σ := σ) d n)) ≫
          ModuleCat.ofHom
            (coordinateHomogeneousLaurentFullNegativeDifferential
              (R := R) (σ := σ) d n) =
        coordinateHomogeneousLaurentOrderedCechDifferential
            (R := R) (σ := σ) d n ≫
          ModuleCat.ofHom
            (coordinateHomogeneousLaurentFullNegativeProjection
              (R := R) d (n + 1)) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      exact coordinateHomogeneousLaurentFullNegativeProjection_differential
        (R := R) (σ := σ) d n s
    have hp : p ≫ ModuleCat.ofHom
        (coordinateHomogeneousLaurentFullNegativeDifferential
          (R := R) (σ := σ) d n) = 0 := by
      dsimp only [p]
      calc
        ((coordinateHomogeneousLaurentOrderedCechComplex
              (R := R) j d).iCycles n ≫
            ModuleCat.ofHom
              (coordinateHomogeneousLaurentFullNegativeProjection
                (R := R) d n)) ≫
            ModuleCat.ofHom
              (coordinateHomogeneousLaurentFullNegativeDifferential
                (R := R) (σ := σ) d n) =
          (coordinateHomogeneousLaurentOrderedCechComplex
              (R := R) j d).iCycles n ≫
            (ModuleCat.ofHom
                (coordinateHomogeneousLaurentFullNegativeProjection
                  (R := R) d n) ≫
              ModuleCat.ofHom
                (coordinateHomogeneousLaurentFullNegativeDifferential
                  (R := R) (σ := σ) d n)) := Category.assoc _ _ _
        _ = (coordinateHomogeneousLaurentOrderedCechComplex
              (R := R) j d).iCycles n ≫
            (coordinateHomogeneousLaurentOrderedCechDifferential
                (R := R) (σ := σ) d n ≫
              ModuleCat.ofHom
                (coordinateHomogeneousLaurentFullNegativeProjection
                  (R := R) d (n + 1))) :=
          congrArg (fun q =>
            (coordinateHomogeneousLaurentOrderedCechComplex
              (R := R) j d).iCycles n ≫ q) hprojection
        _ = ((coordinateHomogeneousLaurentOrderedCechComplex
              (R := R) j d).iCycles n ≫
            coordinateHomogeneousLaurentOrderedCechDifferential
              (R := R) (σ := σ) d n) ≫
              ModuleCat.ofHom
                (coordinateHomogeneousLaurentFullNegativeProjection
                  (R := R) d (n + 1)) := (Category.assoc _ _ _).symm
        _ = ((coordinateHomogeneousLaurentOrderedCechComplex
              (R := R) j d).iCycles n ≫
            (coordinateHomogeneousLaurentOrderedCechComplex
              (R := R) j d).d n (n + 1)) ≫
              ModuleCat.ofHom
                (coordinateHomogeneousLaurentFullNegativeProjection
                  (R := R) d (n + 1)) :=
          congrArg (fun q =>
            ((coordinateHomogeneousLaurentOrderedCechComplex
                (R := R) j d).iCycles n ≫ q) ≫
              ModuleCat.ofHom
                (coordinateHomogeneousLaurentFullNegativeProjection
                  (R := R) d (n + 1)))
            (coordinateHomogeneousLaurentOrderedCechComplex_d
              (R := R) j d n).symm
        _ = 0 := calc
          _ = 0 ≫ ModuleCat.ofHom
              (coordinateHomogeneousLaurentFullNegativeProjection
                (R := R) d (n + 1)) :=
            congrArg (fun q => q ≫ ModuleCat.ofHom
              (coordinateHomogeneousLaurentFullNegativeProjection
                (R := R) d (n + 1)))
              ((coordinateHomogeneousLaurentOrderedCechComplex
                (R := R) j d).iCycles_d n (n + 1))
          _ = 0 := Limits.zero_comp
    refine ModuleCat.ofHom (p.hom.codRestrict
      (coordinateHomogeneousLaurentFullNegativeCycles
        (R := R) (σ := σ) d n) (fun s => ?_))
    rw [coordinateHomogeneousLaurentFullNegativeCycles, LinearMap.mem_ker]
    change coordinateHomogeneousLaurentFullNegativeDifferential
      (R := R) (σ := σ) d n (p.hom s) = 0
    exact congrArg (fun f => f s) hp

/-- Projecting an ambient cycle and then including the full-negative cycle recovers the
componentwise projection of that ambient cycle. -/
theorem coordinateHomogeneousLaurentCyclesToFullNegativeCycles_i
    [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ) :
    coordinateHomogeneousLaurentCyclesToFullNegativeCycles
        (R := R) j d n ≫
        ModuleCat.ofHom
          (coordinateHomogeneousLaurentFullNegativeCycles
            (R := R) (σ := σ) d n).subtype =
      (coordinateHomogeneousLaurentOrderedCechComplex
          (R := R) j d).iCycles n ≫
        ModuleCat.ofHom
          (coordinateHomogeneousLaurentFullNegativeProjection
            (R := R) d n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  rfl

/-- Every positive-degree cocycle in the homogeneous Laurent presentation is a boundary modulo
the active weights that are negative in every coordinate. -/
theorem exists_boundary_add_fullNegativeWeights_eq_coordinateHomogeneousLaurentCocycle
    [Fintype σ] [LinearOrder σ] (d : ℤ) (n : ℕ)
    (s : coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d (n + 1))
    (hs : (coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) d (n + 1)).hom s = 0) :
    ∃ t : coordinateHomogeneousLaurentOrderedCechObject
        (R := R) (σ := σ) d n,
      (coordinateHomogeneousLaurentOrderedCechDifferential
          (R := R) (σ := σ) d n).hom t +
        (∑ e ∈ (coordinateHomogeneousLaurentActiveWeights d (n + 1) s).filter
            fun e => e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ)),
          coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
            (coordinateHomogeneousLaurentWeightComponent
              (R := R) d e (n + 1) s)) = s := by
  classical
  let A := coordinateHomogeneousLaurentActiveWeights d (n + 1) s
  let N := A.filter fun e =>
    e.liftedNegativeSupport ≠ (Set.univ : Set (ULift.{u} σ))
  have hcomponent_cycle (e : HomogeneousLaurentExponent σ d) :
      ModularCurves.orderedCechSupportDifferential
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          e.liftedNegativeSupport (n + 1)
          (coordinateHomogeneousLaurentWeightComponent
            (R := R) d e (n + 1) s) = 0 := by
    rw [← coordinateHomogeneousLaurentWeightComponent_differential
      (R := R) (σ := σ) (d := d) (e := e) (n := n + 1), hs]
    exact map_zero
      (coordinateHomogeneousLaurentWeightComponent (R := R) d e (n + 2))
  have hpreimage (e : {e : HomogeneousLaurentExponent σ d // e ∈ N}) :
      ∃ t : ModularCurves.OrderedCechSupportCochain
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          e.1.liftedNegativeSupport n,
        ModularCurves.orderedCechSupportDifferential
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            e.1.liftedNegativeSupport n t =
          coordinateHomogeneousLaurentWeightComponent
            (R := R) d e.1 (n + 1) s := by
    have he : e.1.liftedNegativeSupport ≠ (Set.univ : Set (ULift.{u} σ)) := by
      exact (Finset.mem_filter.mp e.2).2
    obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem _).mp he
    exact ModularCurves.exists_preimage_orderedCechSupportDifferential
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      e.1.liftedNegativeSupport i hi n
      (coordinateHomogeneousLaurentWeightComponent (R := R) d e.1 (n + 1) s)
      (hcomponent_cycle e.1)
  choose t ht using hpreimage
  refine ⟨∑ e : {e : HomogeneousLaurentExponent σ d // e ∈ N},
    coordinateHomogeneousLaurentWeightInclusion (R := R) d e.1 n (t e), ?_⟩
  rw [map_sum]
  simp only [coordinateHomogeneousLaurentWeightInclusion_differential, ht]
  rw [Finset.univ_eq_attach N]
  have hsum :
      (∑ x ∈ N.attach,
        coordinateHomogeneousLaurentWeightInclusion (R := R) d x.1 (n + 1)
          (coordinateHomogeneousLaurentWeightComponent
            (R := R) d x.1 (n + 1) s)) =
      ∑ e ∈ N,
        coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
          (coordinateHomogeneousLaurentWeightComponent
            (R := R) d e (n + 1) s) :=
    Finset.sum_attach N fun e =>
      coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
        (coordinateHomogeneousLaurentWeightComponent
          (R := R) d e (n + 1) s)
  rw [hsum]
  change (∑ e ∈ N,
      coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
        (coordinateHomogeneousLaurentWeightComponent
          (R := R) d e (n + 1) s)) +
      (∑ e ∈ A.filter (fun e =>
          e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))),
        coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
          (coordinateHomogeneousLaurentWeightComponent
            (R := R) d e (n + 1) s)) = s
  rw [show N = A.filter (fun e =>
      ¬e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))) by rfl]
  calc
    _ = (∑ e ∈ A.filter (fun e =>
          e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))),
          coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
            (coordinateHomogeneousLaurentWeightComponent
              (R := R) d e (n + 1) s)) +
        (∑ e ∈ A.filter (fun e =>
          ¬e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))),
          coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
            (coordinateHomogeneousLaurentWeightComponent
              (R := R) d e (n + 1) s)) := add_comm _ _
    _ = ∑ e ∈ A,
          coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
            (coordinateHomogeneousLaurentWeightComponent
              (R := R) d e (n + 1) s) :=
      Finset.sum_filter_add_sum_filter_not A
        (fun e => e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))) _
    _ = s := coordinateHomogeneousLaurentActiveWeights_reconstruct d (n + 1) s

/-- Every positive-degree cocycle in the homogeneous Laurent presentation of the ordered Cech
complex for a nonnegative projective twist is a boundary. -/
theorem exists_preimage_coordinateHomogeneousLaurentOrderedCechDifferential
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (hd : 0 ≤ d) (n : ℕ)
    (s : coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d (n + 1))
    (hs : (coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) d (n + 1)).hom s = 0) :
    ∃ t : coordinateHomogeneousLaurentOrderedCechObject
        (R := R) (σ := σ) d n,
      (coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d n).hom t = s := by
  classical
  have hcomponent_cycle (e : HomogeneousLaurentExponent σ d) :
      ModularCurves.orderedCechSupportDifferential
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          e.liftedNegativeSupport (n + 1)
          (coordinateHomogeneousLaurentWeightComponent
            (R := R) d e (n + 1) s) = 0 := by
    rw [← coordinateHomogeneousLaurentWeightComponent_differential
      (R := R) (σ := σ) (d := d) (e := e) (n := n + 1), hs]
    exact map_zero
      (coordinateHomogeneousLaurentWeightComponent (R := R) d e (n + 2))
  have hpreimage (e : HomogeneousLaurentExponent σ d) :
      ∃ t : ModularCurves.OrderedCechSupportCochain
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          e.liftedNegativeSupport n,
        ModularCurves.orderedCechSupportDifferential
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            e.liftedNegativeSupport n t =
          coordinateHomogeneousLaurentWeightComponent
            (R := R) d e (n + 1) s := by
    obtain ⟨i, hi⟩ := e.exists_not_mem_liftedNegativeSupport_of_nonneg j hd
    exact ModularCurves.exists_preimage_orderedCechSupportDifferential
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      e.liftedNegativeSupport i hi n
      (coordinateHomogeneousLaurentWeightComponent (R := R) d e (n + 1) s)
      (hcomponent_cycle e)
  choose t ht using hpreimage
  refine ⟨∑ e ∈ coordinateHomogeneousLaurentActiveWeights d (n + 1) s,
    coordinateHomogeneousLaurentWeightInclusion (R := R) d e n (t e), ?_⟩
  rw [map_sum]
  calc
    (∑ e ∈ coordinateHomogeneousLaurentActiveWeights d (n + 1) s,
        (coordinateHomogeneousLaurentOrderedCechDifferential
          (R := R) (σ := σ) d n).hom
          (coordinateHomogeneousLaurentWeightInclusion (R := R) d e n (t e))) =
      ∑ e ∈ coordinateHomogeneousLaurentActiveWeights d (n + 1) s,
        coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
          (ModularCurves.orderedCechSupportDifferential
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            e.liftedNegativeSupport n (t e)) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [coordinateHomogeneousLaurentWeightInclusion_differential]
    _ = ∑ e ∈ coordinateHomogeneousLaurentActiveWeights d (n + 1) s,
        coordinateHomogeneousLaurentWeightInclusion (R := R) d e (n + 1)
          (coordinateHomogeneousLaurentWeightComponent
            (R := R) d e (n + 1) s) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [ht e]
    _ = s := coordinateHomogeneousLaurentActiveWeights_reconstruct d (n + 1) s

/-- Every positive-degree cocycle in the explicit standard-coordinate ordered Cech complex for a
nonnegative projective twist is a boundary. -/
theorem exists_preimage_coordinateHyperplaneTwistOrderedBaseCechDifferential
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (hd : 0 ≤ d) (n : ℕ)
    (s : Scheme.Modules.orderedBaseCechObject
      (homogeneousProjπ (R := R) (σ := σ))
      (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
      (coordinateOpenCover (R := R) (σ := σ)) (n + 1))
    (hs : (coordinateHyperplaneTwistOrderedBaseCechDifferential
      (R := R) (σ := σ) d (n + 1)).hom s = 0) :
    ∃ t : Scheme.Modules.orderedBaseCechObject
        (homogeneousProjπ (R := R) (σ := σ))
        (Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))
        (coordinateOpenCover (R := R) (σ := σ)) n,
      (coordinateHyperplaneTwistOrderedBaseCechDifferential
        (R := R) (σ := σ) d n).hom t = s := by
  have hs_weight :
      (coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d (n + 1)).hom
          ((coordinateHomogeneousLaurentOrderedCechObjectIso
            (R := R) (σ := σ) d (n + 1)).hom.hom s) = 0 := by
    have h := congrArg (fun f => f.hom s)
      (coordinateHomogeneousLaurentOrderedCechDifferential_naturality
        (R := R) (σ := σ) d (n + 1))
    simpa [hs] using h
  obtain ⟨t, ht⟩ :=
    exists_preimage_coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) j d hd n
      ((coordinateHomogeneousLaurentOrderedCechObjectIso
        (R := R) (σ := σ) d (n + 1)).hom.hom s) hs_weight
  refine ⟨(coordinateHomogeneousLaurentOrderedCechObjectIso
    (R := R) (σ := σ) d n).inv.hom t, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso
    (coordinateHomogeneousLaurentOrderedCechObjectIso
      (R := R) (σ := σ) d (n + 1)).hom).1
  have h := congrArg (fun f => f.hom
      ((coordinateHomogeneousLaurentOrderedCechObjectIso
        (R := R) (σ := σ) d n).inv.hom t))
    (coordinateHomogeneousLaurentOrderedCechDifferential_naturality
      (R := R) (σ := σ) d n)
  have h' :
      (coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) d n).hom
          ((coordinateHomogeneousLaurentOrderedCechObjectIso
            (R := R) (σ := σ) d n).hom.hom
            ((coordinateHomogeneousLaurentOrderedCechObjectIso
              (R := R) (σ := σ) d n).inv.hom t)) =
        (coordinateHomogeneousLaurentOrderedCechObjectIso
          (R := R) (σ := σ) d (n + 1)).hom.hom
          ((coordinateHyperplaneTwistOrderedBaseCechDifferential
            (R := R) (σ := σ) d n).hom
            ((coordinateHomogeneousLaurentOrderedCechObjectIso
              (R := R) (σ := σ) d n).inv.hom t)) := by
    simpa only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] using h
  rw [← h']
  simpa using ht

/-- The explicit standard-coordinate ordered Cech complex for a nonnegative projective twist is
exact in every positive degree. -/
theorem coordinateHyperplaneTwistOrderedBaseCechComplex_exactAt_succ
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (hd : 0 ≤ d) (n : ℕ) :
    (coordinateHyperplaneTwistOrderedBaseCechComplex
      (R := R) j d).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) ((n + 1) + 1)
    (by simp) (by simp)]
  have hsc : (ShortComplex.mk
      (coordinateHyperplaneTwistOrderedBaseCechDifferential
        (R := R) (σ := σ) d n)
      (coordinateHyperplaneTwistOrderedBaseCechDifferential
        (R := R) (σ := σ) d (n + 1))
      (coordinateHyperplaneTwistOrderedBaseCechDifferential_comp
        (R := R) j d n)).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro s hs
    exact exists_preimage_coordinateHyperplaneTwistOrderedBaseCechDifferential
      (R := R) (σ := σ) j d hd n s hs
  simpa only [HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor',
    coordinateHyperplaneTwistOrderedBaseCechComplex_X,
    coordinateHyperplaneTwistOrderedBaseCechComplex_d] using hsc

/-- The native ordered Cech complex of a nonnegative coordinate-hyperplane twist is exact in
every positive degree. -/
theorem coordinateHyperplaneTwist_orderedBaseCechComplex_exactAt_succ
    [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (hd : 0 ≤ d) (n : ℕ) :
    (Scheme.Modules.orderedBaseCechComplex
      (homogeneousProjπ (R := R) (σ := σ))
      (coordinateHyperplaneTwist (R := R) j d)
      (coordinateOpenCover (R := R) (σ := σ))).ExactAt (n + 1) := by
  exact (coordinateHyperplaneTwistOrderedBaseCechComplex_exactAt_succ
    (R := R) (σ := σ) j d hd n).of_iso
      (coordinateHyperplaneTwistOrderedBaseCechComplexIso
        (R := R) j d).symm

end

end MvPolynomial

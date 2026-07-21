/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistCechWeightComponents

/-!
# Finite assembly of projective twist Cech weight components

For a finite coordinate set, every cochain in the ordered projective twist Cech complex has only
finitely many active global Laurent weights. This file records those weights and reconstructs the
cochain as the finite sum of its fixed-weight components.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

local instance : DecidableEq σ := Classical.decEq σ

/-- A homogeneous Laurent exponent of nonnegative degree has a coordinate outside its negative
support. -/
theorem HomogeneousLaurentExponent.exists_not_mem_liftedNegativeSupport_of_nonneg
    {d : ℤ} (e : HomogeneousLaurentExponent σ d) (j : σ) (hd : 0 ≤ d) :
    ∃ i : ULift.{u} σ, i ∉ e.liftedNegativeSupport := by
  by_contra h
  have hall : ∀ i : σ, e.1 i < 0 := by
    intro i
    by_contra hi
    apply h
    exact ⟨ULift.up i, hi⟩
  have hdegree : Finsupp.degree e.1 < 0 := by
    rw [Finsupp.degree_apply]
    apply Finset.sum_neg
    · intro i _
      exact hall i
    · exact ⟨j, Finsupp.mem_support_iff.mpr (ne_of_lt (hall j))⟩
  rw [e.2] at hdegree
  exact (not_lt_of_ge hd) hdegree

/-- The finite set of global Laurent weights occurring in a homogeneous ordered Cech cochain. -/
noncomputable def coordinateHomogeneousLaurentActiveWeights
    [Fintype σ] [LinearOrder σ] (d : ℤ) (n : ℕ)
    (x : coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d n) :
    Finset (HomogeneousLaurentExponent σ d) := by
  classical
  letI : Fintype (Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) := by
    unfold Scheme.Modules.OrderedCechIndex
    infer_instance
  exact Finset.univ.biUnion fun a =>
    (((Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      ModuleCat.of
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (AddMonoidAlgebra
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          {e : HomogeneousLaurentExponent σ d //
            e.IsAllowedOn (fun k => (b.1 k).down)})) a).hom x).coeff.support.image
      (fun e => e.1))

/-- A global Laurent weight is active exactly when one ordered Cech factor has a nonzero
coefficient at that weight. -/
theorem mem_coordinateHomogeneousLaurentActiveWeights_iff
    [Fintype σ] [LinearOrder σ] (d : ℤ) (n : ℕ)
    (x : coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d n) (e : HomogeneousLaurentExponent σ d) :
    e ∈ coordinateHomogeneousLaurentActiveWeights d n x ↔
      ∃ (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n)
        (h : e.IsAllowedOn (fun k => (a.1 k).down)),
        ((Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
          ModuleCat.of
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            (AddMonoidAlgebra
              Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
              {e : HomogeneousLaurentExponent σ d //
                e.IsAllowedOn (fun k => (b.1 k).down)})) a).hom x).coeff
            (⟨e, h⟩ : {e : HomogeneousLaurentExponent σ d //
              e.IsAllowedOn (fun k => (a.1 k).down)}) ≠ 0 := by
  classical
  letI : Fintype (Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) := by
    unfold Scheme.Modules.OrderedCechIndex
    infer_instance
  rw [coordinateHomogeneousLaurentActiveWeights]
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨a, _, ha⟩
    rcases Finset.mem_image.mp ha with ⟨f, hf, rfl⟩
    exact ⟨a, f.2, Finsupp.mem_support_iff.mp hf⟩
  · rintro ⟨a, h, ha⟩
    refine ⟨a, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨⟨e, h⟩, Finsupp.mem_support_iff.mpr ha, rfl⟩

/-- Every homogeneous ordered Cech cochain is the finite sum of its active Laurent-weight
components. -/
theorem coordinateHomogeneousLaurentActiveWeights_reconstruct
    [Fintype σ] [LinearOrder σ] (d : ℤ) (n : ℕ)
    (x : coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) d n) :
    (∑ e ∈ coordinateHomogeneousLaurentActiveWeights d n x,
      coordinateHomogeneousLaurentWeightInclusion (R := R) d e n
        (coordinateHomogeneousLaurentWeightComponent (R := R) d e n x)) = x := by
  classical
  letI : Fintype (Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) := by
    unfold Scheme.Modules.OrderedCechIndex
    infer_instance
  apply Concrete.limit_ext (Discrete.functor fun
    a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      ModuleCat.of
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (AddMonoidAlgebra
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          {e : HomogeneousLaurentExponent σ d //
            e.IsAllowedOn (fun k => (a.1 k).down)}))
  intro a
  rcases a with ⟨a⟩
  let p : coordinateHomogeneousLaurentOrderedCechObject
        (R := R) (σ := σ) d n ⟶
      ModuleCat.of
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (AddMonoidAlgebra
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          {e : HomogeneousLaurentExponent σ d //
            e.IsAllowedOn (fun k => (a.1 k).down)}) :=
    Pi.π _ a
  change p.hom
      (∑ e ∈ coordinateHomogeneousLaurentActiveWeights d n x,
        coordinateHomogeneousLaurentWeightInclusion (R := R) d e n
          (coordinateHomogeneousLaurentWeightComponent (R := R) d e n x)) = p.hom x
  rw [map_sum]
  apply AddMonoidAlgebra.coeff_injective
  ext f
  let c : AddMonoidAlgebra
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        {e : HomogeneousLaurentExponent σ d //
          e.IsAllowedOn (fun k => (a.1 k).down)} →ₗ[
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))]
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens)) :=
    (Finsupp.lapply f).comp
      (AddMonoidAlgebra.coeffLinearEquiv
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))).toLinearMap
  change c (∑ e ∈ coordinateHomogeneousLaurentActiveWeights d n x,
      p.hom (coordinateHomogeneousLaurentWeightInclusion (R := R) d e n
        (coordinateHomogeneousLaurentWeightComponent (R := R) d e n x))) = c (p.hom x)
  rw [map_sum]
  have hcoefficient
      (y : coordinateHomogeneousLaurentOrderedCechObject
        (R := R) (σ := σ) d n) :
      c (p.hom y) =
        (coordinateHomogeneousLaurentWeightComponent
          (R := R) d f.1 n y).1 a := by
    symm
    rw [coordinateHomogeneousLaurentWeightComponent_apply_of_allowed
      (R := R) (σ := σ) (d := d) (e := f.1) (n := n) (a := a) (h := f.2)]
    rfl
  have hterm_ne (e : HomogeneousLaurentExponent σ d) (hef : e ≠ f.1) :
      c (p.hom (coordinateHomogeneousLaurentWeightInclusion (R := R) d e n
        (coordinateHomogeneousLaurentWeightComponent (R := R) d e n x))) = 0 := by
    rw [hcoefficient,
      coordinateHomogeneousLaurentWeightComponent_inclusion_ne
        (R := R) (σ := σ) (d := d) (e := e) (f := f.1)
          (hef := Ne.symm hef) (n := n)]
    rfl
  have hterm_self :
      c (p.hom (coordinateHomogeneousLaurentWeightInclusion (R := R) d f.1 n
        (coordinateHomogeneousLaurentWeightComponent (R := R) d f.1 n x))) = c (p.hom x) := by
    rw [hcoefficient,
      coordinateHomogeneousLaurentWeightComponent_inclusion
        (R := R) (σ := σ) (d := d) (e := f.1) (n := n),
      hcoefficient]
  by_cases hf : f.1 ∈ coordinateHomogeneousLaurentActiveWeights d n x
  · rw [Finset.sum_eq_single_of_mem f.1 hf]
    · exact hterm_self
    · intro e _ hef
      exact hterm_ne e hef
  · rw [Finset.sum_eq_zero]
    · symm
      by_contra hcoeff
      apply hf
      apply (mem_coordinateHomogeneousLaurentActiveWeights_iff d n x f.1).2
      refine ⟨a, f.2, ?_⟩
      rw [hcoefficient] at hcoeff
      rw [coordinateHomogeneousLaurentWeightComponent_apply_of_allowed
        (R := R) (σ := σ) (d := d) (e := f.1) (n := n) (a := a) (h := f.2)] at hcoeff
      exact hcoeff
    · intro e he
      exact hterm_ne e (fun hef => hf (hef ▸ he))

end

end MvPolynomial

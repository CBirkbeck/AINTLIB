/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.LowDegreeFiniteProjectiveReplacement

/-!
# Bounded flat cochain complexes

This file translates between categorical homology of cochain complexes of modules and the
explicit kernels and quotients used by the algebraic base-change API.
-/

open CategoryTheory

universe u v

namespace ModularCurves

variable {R : Type u} [CommRing R]

/-- A bounded cochain complex of flat modules with finite homology is exact over the base when
it is exact after every field base change. -/
theorem HomologicalComplex.functionExact_of_bounded_flat_forall_field_baseChange_exact_of_finite_homology
    (C : CochainComplex (ModuleCat.{v} R) ℕ)
    [∀ q, Module.Flat R (C.X q)]
    [∀ q, Module.Finite R (C.homology q)]
    (N : ℕ) [Subsingleton (C.X (N + 1))]
    (hfield : ∀ q, q < N → ∀ (K : Type u) [Field K] [Algebra R K],
      Function.Exact
        ((C.d q (q + 1)).hom.baseChange K)
        ((C.d (q + 1) (q + 2)).hom.baseChange K))
    (q : ℕ) (hq : q < N) :
    Function.Exact (C.d q (q + 1)).hom (C.d (q + 1) (q + 2)).hom := by
  let M : ℕ → Type v := fun i ↦ C.X i
  let d : ∀ i, M i →ₗ[R] M (i + 1) := fun i ↦ (C.d i (i + 1)).hom
  have hcomp : ∀ i, d (i + 1) ∘ₗ d i = 0 := by
    intro i
    exact shortComplexModuleCatCompEqZero (C.sc' i (i + 1) (i + 2))
  have hfinite : ∀ i, i < N →
      Module.Finite R
        (LinearMap.ker (d (i + 1)) ⧸
          LinearMap.range
            (LinearMap.codRestrictToKer (d i) (d (i + 1)) (hcomp i))) := by
    intro i _
    let S := C.sc' i (i + 1) (i + 2)
    have hprev : (ComplexShape.up ℕ).prev (i + 1) = i :=
      CochainComplex.prev_nat_succ i
    have hnext : (ComplexShape.up ℕ).next (i + 1) = i + 2 := by
      rw [CochainComplex.next]
      omega
    letI : Module.Finite R S.homology :=
      Module.Finite.equiv
        (C.homologyIsoSc' i (i + 1) (i + 2) hprev hnext).toLinearEquiv
    exact Module.Finite.quotient_range_moduleCatToCycles S
  exact LinearMap.exact_of_bounded_flat_forall_field_baseChange_exact_of_finite_homology
    M d N hcomp hfinite hfield q hq

/-- Finite degree-zero homology of a cochain complex gives a finite kernel of its first
differential. -/
theorem HomologicalComplex.finite_kernel_zero_of_finite_homology
    (C : CochainComplex (ModuleCat.{v} R) ℕ)
    [Module.Finite R (C.homology 0)] :
    Module.Finite R (LinearMap.ker (C.d 0 1).hom) := by
  let S := C.sc' 0 0 1
  have hprev : (ComplexShape.up ℕ).prev 0 = 0 :=
    CochainComplex.prev_nat_zero
  have hnext : (ComplexShape.up ℕ).next 0 = 1 := by simp
  letI : Module.Finite R S.homology :=
    Module.Finite.equiv
      (C.homologyIsoSc' 0 0 1 hprev hnext).toLinearEquiv
  have hto : S.moduleCatToCycles = 0 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (C.d 0 0).hom x = 0
    rw [C.shape 0 0 (by simp)]
    rfl
  have hrange : LinearMap.range S.moduleCatToCycles = ⊥ := by
    rw [hto, LinearMap.range_zero]
  let e : S.homology ≃ₗ[R] LinearMap.ker (C.d 0 1).hom :=
    S.moduleCatHomologyIso.toLinearEquiv.trans
      ((LinearMap.range S.moduleCatToCycles).quotEquivOfEqBot hrange)
  exact Module.Finite.equiv e

end ModularCurves

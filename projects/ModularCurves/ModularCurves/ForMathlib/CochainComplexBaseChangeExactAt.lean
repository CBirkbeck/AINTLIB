/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.LowDegreeFiniteProjectiveReplacement

/-!
# Exactness after scalar extension

This file translates algebraic exactness of consecutive base-changed
differentials into categorical exactness of the scalar-extended complex.
-/

open CategoryTheory

universe u v

namespace ModularCurves

variable {R : Type u} [CommRing R]

/-- Exactness of consecutive differentials in a module cochain complex is categorical
exactness at the intervening positive degree. -/
theorem cochainComplex_functionExact_iff_exactAt
    (K : CochainComplex (ModuleCat.{v} R) ℕ) (q : ℕ) :
    Function.Exact (K.d q (q + 1)).hom
      (K.d (q + 1) (q + 2)).hom ↔ K.ExactAt (q + 1) := by
  have hprev : (ComplexShape.up ℕ).prev (q + 1) = q :=
    CochainComplex.prev_nat_succ q
  have hnext : (ComplexShape.up ℕ).next (q + 1) = q + 2 := by
    rw [CochainComplex.next]
    omega
  rw [HomologicalComplex.exactAt_iff'
    (K := K) (i := q) (j := q + 1) (k := q + 2) hprev hnext]
  exact
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (K.sc' q (q + 1) (q + 2))).symm

/-- Exactness of algebraically base-changed consecutive differentials is
categorical exactness at the corresponding positive degree after extension of
scalars. -/
theorem cochainComplex_map_exactAt_of_baseChange_functionExact
    (A : Type v) [CommRing A] [Algebra R A]
    (K : CochainComplex (ModuleCat.{v} R) ℕ) (q : ℕ)
    (h : Function.Exact
      ((K.d q (q + 1)).hom.baseChange A)
      ((K.d (q + 1) (q + 2)).hom.baseChange A)) :
    (((ModuleCat.extendScalars (algebraMap R A)).mapHomologicalComplex
      (.up ℕ)).obj K).ExactAt (q + 1) := by
  let F := ModuleCat.extendScalars (algebraMap R A)
  have hprev : (ComplexShape.up ℕ).prev (q + 1) = q :=
    CochainComplex.prev_nat_succ q
  have hnext : (ComplexShape.up ℕ).next (q + 1) = q + 2 := by
    rw [CochainComplex.next]
    omega
  apply (HomologicalComplex.exactAt_iff'
    (K := (F.mapHomologicalComplex (.up ℕ)).obj K)
    (i := q) (j := q + 1) (k := q + 2) hprev hnext).mpr
  let S : ShortComplex (ModuleCat.{v} R) :=
    K.sc' q (q + 1) (q + 2)
  let T : ShortComplex (ModuleCat.{v} A) :=
    ShortComplex.moduleCatMk
      (S.f.hom.baseChange A) (S.g.hom.baseChange A)
      (LinearMap.baseChange_comp_eq_zero
        S.f.hom S.g.hom
        (shortComplexModuleCatCompEqZero S) A)
  have hT : T.Exact := by
    apply
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mpr
    intro x
    exact h x
  have e : T ≅ S.map F :=
    shortComplexModuleCatMkBaseChangeIso S A
  exact (ShortComplex.exact_iff_of_iso e).mp hT

end ModularCurves

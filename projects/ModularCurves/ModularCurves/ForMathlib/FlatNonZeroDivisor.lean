/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RingHom.Flat

/-!
# Nonzerodivisors under flat ring maps

This file records that flat ring maps preserve nonzerodivisors.
-/

open scoped nonZeroDivisors

namespace RingHom.Flat

/-- A flat map of commutative rings carries nonzerodivisors to nonzerodivisors. -/
theorem map_mem_nonZeroDivisors {R S : Type*} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : f.Flat) {r : R} (hr : r ∈ nonZeroDivisors R) :
    f r ∈ nonZeroDivisors S := by
  letI : Algebra R S := f.toAlgebra
  haveI : Module.Flat R S := hf
  have hreg : IsSMulRegular S r := Module.Flat.isSMulRegular_of_nonZeroDivisors hr
  rw [mem_nonZeroDivisors_iff]
  constructor
  · intro x hx
    apply hreg
    show r • x = r • 0
    rw [smul_zero, Algebra.smul_def, f.algebraMap_toAlgebra, hx]
  · intro x hx
    apply hreg
    show r • x = r • 0
    rw [smul_zero, Algebra.smul_def, f.algebraMap_toAlgebra, mul_comm, hx]

end RingHom.Flat

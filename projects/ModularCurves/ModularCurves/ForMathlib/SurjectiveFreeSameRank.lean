/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.FiniteType

/-!
# A surjection of free modules of equal rank is injective (YFULL route γ)

Over a commutative ring `R`, a surjective linear map `f : M →ₗ[R] Q` between two finite
free `R`-modules of the same rank is injective (hence bijective). This is the module core
of the "same-degree effective Cartier divisor containment ⟹ equality" step in the `Y(N)`
clopen full-level argument.

The proof combines two mathlib facts: two finite free modules of equal rank are linearly
isomorphic (`FiniteDimensional.nonempty_linearEquiv_of_finrank_eq`), and every commutative
ring has the Orzech property (`instOrzechPropertyOfCommRing`), i.e. a surjection onto a
finite module that also *embeds* into it is injective
(`OrzechProperty.injective_of_surjective_of_injective`).
-/

open Module

universe u v

namespace ModularCurves

/-- **A surjection of finite free modules of equal rank is injective.** -/
theorem injective_of_surjective_of_free_finrank_eq {R : Type u} [CommRing R] [Nontrivial R]
    {M Q : Type v} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup Q] [Module R Q] [Module.Free R Q] [Module.Finite R Q]
    (h : Module.finrank R M = Module.finrank R Q)
    (f : M →ₗ[R] Q) (hf : Function.Surjective f) : Function.Injective f := by
  obtain ⟨i⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (R := R) (M := M) (M' := Q) h
  exact OrzechProperty.injective_of_surjective_of_injective i.toLinearMap f i.injective hf

/-- A surjection of finite free modules of equal rank is bijective. -/
theorem bijective_of_surjective_of_free_finrank_eq {R : Type u} [CommRing R] [Nontrivial R]
    {M Q : Type v} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup Q] [Module R Q] [Module.Free R Q] [Module.Finite R Q]
    (h : Module.finrank R M = Module.finrank R Q)
    (f : M →ₗ[R] Q) (hf : Function.Surjective f) : Function.Bijective f :=
  ⟨injective_of_surjective_of_free_finrank_eq h f hf, hf⟩

end ModularCurves

/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.InvariantBasisNumber

/-!
# Surjective maps of finite free modules of equal rank are bijective

Over a commutative ring satisfying the strong rank condition and stable finiteness (in particular
any commutative ring), a surjective `R`-linear map between two finite free modules of the same rank
is bijective. This is the module core behind "an inclusion of finite locally free schemes of the
same degree is an isomorphism": choosing bases identifies the map with a surjective endomorphism of
`M`, which is injective by `Module.End.injective_of_surjective`.
-/

open Module

namespace ModularCurves

/-- A surjective linear map between finite free modules of the same rank is bijective. -/
theorem bijective_of_surjective_of_finrank_eq {R : Type*} [CommRing R]
    [StrongRankCondition R] [IsStablyFiniteRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hrank : Module.finrank R M = Module.finrank R N) : Function.Bijective f := by
  let e : N ≃ₗ[R] M := LinearEquiv.ofFinrankEq N M hrank.symm
  have hcomp : Function.Surjective ⇑((e : N →ₗ[R] M).comp f) := e.surjective.comp hf
  have hinj : Function.Injective ⇑((e : N →ₗ[R] M).comp f) :=
    Module.End.injective_of_surjective R M hcomp
  rw [LinearMap.coe_comp] at hinj
  exact ⟨hinj.of_comp, hf⟩

end ModularCurves

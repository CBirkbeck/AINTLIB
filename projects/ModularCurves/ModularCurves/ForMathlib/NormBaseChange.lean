/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The norm commutes with base change

For a finite free `R`-algebra `B` and a map `ψ : A →ₐ[R] A'` of `R`-algebras, the norm
of `A ⊗[R] B` over `A` maps to the norm of `A' ⊗[R] B` over `A'`:
`Norm_{A'}((ψ ⊗ id) f) = ψ (Norm_A f)`.

Proof: the multiplication operator of `(ψ ⊗ id) f` is conjugate, along the canonical
algebra isomorphism `A' ⊗[A] (A ⊗[R] B) ≃ₐ[A'] A' ⊗[R] B`, to the base change of the
multiplication operator of `f`, and determinants are invariant under conjugation and
compatible with base change (`LinearMap.det_baseChange`). Upstream candidate.
-/

open TensorProduct

namespace ModularCurves

variable {R B A A' : Type*} [CommRing R] [CommRing B] [CommRing A] [CommRing A']
variable [Algebra R B] [Algebra R A] [Algebra R A']
variable [Module.Free R B] [Module.Finite R B]

/-- The norm of a finite free extension commutes with base change along a map of
coefficient algebras. -/
theorem norm_tensor_map (ψ : A →ₐ[R] A') (f : A ⊗[R] B) :
    Algebra.norm A' (Algebra.TensorProduct.map ψ (AlgHom.id R B) f) =
      ψ (Algebra.norm A f) := by
  letI : Algebra A A' := ψ.toRingHom.toAlgebra
  haveI : IsScalarTower R A A' :=
    IsScalarTower.of_algebraMap_eq' (ψ.comp_algebraMap).symm
  let e : A' ⊗[A] (A ⊗[R] B) ≃ₐ[A'] A' ⊗[R] B :=
    Algebra.TensorProduct.cancelBaseChange R A A' A' B
  have hconj : (Algebra.lmul A' (A' ⊗[R] B))
        (Algebra.TensorProduct.map ψ (AlgHom.id R B) f) =
      (e.toLinearEquiv : A' ⊗[A] (A ⊗[R] B) →ₗ[A'] A' ⊗[R] B) ∘ₗ
        (LinearMap.baseChange A' ((Algebra.lmul A (A ⊗[R] B)) f)) ∘ₗ
        (e.toLinearEquiv.symm : A' ⊗[R] B →ₗ[A'] A' ⊗[A] (A ⊗[R] B)) := by
    apply LinearMap.ext
    intro y
    induction y with
    | zero => rw [map_zero, map_zero]
    | add y₁ y₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
    | tmul a' z =>
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        AlgEquiv.toLinearEquiv_apply,
        Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
      rw [show (e.toLinearEquiv.symm) (a' ⊗ₜ[R] z) =
          a' ⊗ₜ[A] ((1 : A) ⊗ₜ[R] z) from
        Algebra.TensorProduct.cancelBaseChange_symm_tmul
          (R := R) (S := A) (T := A') (A := A') (B := B) a' z]
      rw [LinearMap.baseChange_tmul]
      simp only [LinearMap.mul_apply']
      induction f with
      | zero => rw [map_zero, zero_mul, zero_mul, tmul_zero, map_zero]
      | add f₁ f₂ g₁ g₂ =>
        rw [map_add, add_mul, add_mul, tmul_add, map_add, g₁, g₂]
      | tmul a b =>
        rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
          Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          mul_one,
          Algebra.TensorProduct.cancelBaseChange_tmul
            (R := R) (S := A) (T := A') (A := A') (B := B),
          Algebra.smul_def]
        rfl
  rw [Algebra.norm_apply, Algebra.norm_apply,
    show (ψ (LinearMap.det ((Algebra.lmul A (A ⊗[R] B)) f)) : A') =
      algebraMap A A' (LinearMap.det ((Algebra.lmul A (A ⊗[R] B)) f)) from rfl,
    ← LinearMap.det_baseChange, hconj, LinearMap.det_conj]

end ModularCurves

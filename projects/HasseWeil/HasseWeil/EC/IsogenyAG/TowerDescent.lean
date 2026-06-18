/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.IsogenyAG.DualDescent

/-!
# The infinite-Galois tower descent `K̄ → F` for the base-changed function field

Route A, step 1 — the **tower fact**.  For a smooth plane curve `C / F` over a characteristic-zero
field `F`, every element of the `K̄`-function-field `(C.baseChange (AlgebraicClosure F)).FunctionField`
already lives over a **finite** intermediate level, and a `Gal(K̄/F)`-fixed element descends all the
way to `F(C)`.  This is the infinite-Galois (`L = K̄ = AlgebraicClosure F`) version of the finite
`mem_range_functionField_baseChange_iff_fixed`.

The genuinely new content is the *tensor-level tower descent* (`tensor_galFixed_kbar_mem_range`): a
`Gal(K̄/F)`-fixed element of `K̄ ⊗_F R` (for the `σ ⊗ id` action) lies in `1 ⊗ R`.  It is reduced to
the finite descent (`tensor_fixed_mem_range`) by the observation that any tensor `z` is a *finite*
sum `∑ lᵢ ⊗ uᵢ`, so the finitely many scalars `lᵢ ∈ K̄` lie in a finite Galois `M ⊆ K̄`
(`exists_finiteGalois_fieldOfDefinition`), whence `z` is the image of `z_M ∈ M ⊗_F R` under the
`F`-algebra inclusion `M ⊗_F R → K̄ ⊗_F R` (`Algebra.TensorProduct.map (val M) (id)`); `z_M` is
`Gal(M/F)`-fixed by `galFixed_of_galFixed_top`, so the finite descent applies.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.6.1.
-/

open WeierstrassCurve
open scoped TensorProduct

namespace HasseWeil.EC

open Curves

universe u

variable {F : Type u} [Field F]

/-! ### The `F`-algebra inclusion `M ⊗_F R → K̄ ⊗_F R` for `M ⊆ K̄` -/

/-- The `F`-algebra inclusion `M ⊗_F R → K̄ ⊗_F R` induced by `IntermediateField.val M : M →ₐ[F] K̄`
(`M ⊆ K̄ = AlgebraicClosure F` an intermediate field) tensored with the identity on `R`. -/
noncomputable def towerTensorIncl (R : Type*) [CommRing R] [Algebra F R]
    (M : IntermediateField F (AlgebraicClosure F)) :
    (M ⊗[F] R) →ₐ[F] (AlgebraicClosure F ⊗[F] R) :=
  Algebra.TensorProduct.map (M.val) (AlgHom.id F R)

@[simp] theorem towerTensorIncl_tmul (R : Type*) [CommRing R] [Algebra F R]
    (M : IntermediateField F (AlgebraicClosure F)) (m : M) (r : R) :
    towerTensorIncl R M (m ⊗ₜ[F] r) = (m : AlgebraicClosure F) ⊗ₜ[F] r :=
  Algebra.TensorProduct.map_tmul _ _ _ _

/-- `towerTensorIncl` is injective: it is `val M ⊗ id` with `val M` injective and everything flat
over the field `F`. -/
theorem towerTensorIncl_injective (R : Type*) [CommRing R] [Algebra F R]
    (M : IntermediateField F (AlgebraicClosure F)) :
    Function.Injective (towerTensorIncl R M) := by
  have hfun : ⇑(towerTensorIncl R M) =
      ⇑(TensorProduct.map (M.val.toLinearMap) (LinearMap.id (R := F) (M := R))) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m r => simp [towerTensorIncl_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [hfun]
  exact TensorProduct.map_injective_of_flat_flat _ _
    (M.val.injective) Function.injective_id

/-! ### Equivariance of `towerTensorIncl` under compatible Galois elements -/

/-- **Equivariance of the tower inclusion.** If `σ : K̄ ≃ₐ[F] K̄` restricts to `τ : M ≃ₐ[F] M`
(i.e. `σ (m : K̄) = (τ m : K̄)` for all `m ∈ M`), then `towerTensorIncl` intertwines the `σ ⊗ id`
action upstairs with the `τ ⊗ id` action downstairs. -/
theorem towerTensorIncl_congr (R : Type*) [CommRing R] [Algebra F R]
    (M : IntermediateField F (AlgebraicClosure F)) (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
    (τ : M ≃ₐ[F] M) (hστ : ∀ m : M, σ (m : AlgebraicClosure F) = (τ m : AlgebraicClosure F))
    (z : M ⊗[F] R) :
    towerTensorIncl R M
        ((Algebra.TensorProduct.congr τ (AlgEquiv.refl (R := F) (A₁ := R))) z) =
      (Algebra.TensorProduct.congr σ (AlgEquiv.refl (R := F) (A₁ := R)))
        (towerTensorIncl R M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul m r =>
      rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
        towerTensorIncl_tmul, towerTensorIncl_tmul, Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.map_tmul]
      simp only [AlgEquiv.coe_refl, id_eq, AlgEquiv.coe_algHom]
      rw [hστ m]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

end HasseWeil.EC

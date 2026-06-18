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

end HasseWeil.EC

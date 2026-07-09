import ModularCurves.ForMathlib.Coaction
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The comultiplication matrix of a finite free Hopf algebra

Construction support for `[CHARTER-HOPF]` / `T-G3d-infra` Piece 3
(`.mathlib-quality/decomposition-hopf-crux.md`, leaf `[HG-B2]`, design refinement §Δ-matrix):
for a Hopf `R`-algebra `A` that is finite free as an `R`-module with basis `e`, the
**comultiplication matrix** `T ∈ Mat(A)` is defined by `Δ(eⱼ) = ∑ᵢ eᵢ ⊗ Tᵢⱼ`. The
coalgebra axioms expand along the basis to the *matrix-coalgebra identities*

* `counit_comulMatrix` — `ε(Tᵢⱼ) = δᵢⱼ`;
* `comul_comulMatrix` — `Δ(Tᵢⱼ) = ∑ₖ Tᵢₖ ⊗ Tₖⱼ`;

and the antipode axioms then make `T` invertible with **explicit inverse the entrywise
antipode**:

* `antipodeMatrix_mul_comulMatrix : T.map S * T = 1`;
* `comulMatrix_mul_antipodeMatrix : T * T.map S = 1`.

This is the engine of the `03BH` coefficient-invariance step: the matrix of
multiplication-by-`ρ(f)` on `B ⊗ A` is conjugate, over `B ⊗ A`, to its own `ρ`-image via
`T`, so its characteristic polynomial has coinvariant coefficients (next increments).
-/

open scoped TensorProduct

namespace ModularCurves

variable (R A : Type*) [CommRing R] [CommRing A] [HopfAlgebra R A]
  [Module.Free R A] [Module.Finite R A]

/-- The index type of the chosen basis of `A` over `R`. -/
abbrev hopfBasisIndex := Module.Free.ChooseBasisIndex R A

/-- The chosen `R`-basis of `A`. -/
noncomputable def hopfBasis : Module.Basis (hopfBasisIndex R A) R A :=
  Module.Free.chooseBasis R A

/-- Extract the `i`-th basis coefficient of the *first* tensor factor: the linear map
`A ⊗[R] A → A` sending `x ⊗ y ↦ (eᵢ-coefficient of x) • y`. -/
noncomputable def leftCoeff (i : hopfBasisIndex R A) : A ⊗[R] A →ₗ[R] A :=
  (TensorProduct.lid R A).toLinearMap.comp
    (LinearMap.rTensor A ((hopfBasis R A).coord i))

omit [Module.Finite R A] in
@[simp]
theorem leftCoeff_tmul (i : hopfBasisIndex R A) (x y : A) :
    leftCoeff R A i (x ⊗ₜ[R] y) = (hopfBasis R A).coord i x • y := by
  simp [leftCoeff]

/-- Every element of `A ⊗[R] A` is the sum of basis vectors tensor its left
coefficients. -/
theorem sum_tmul_leftCoeff (x : A ⊗[R] A) :
    ∑ i, (hopfBasis R A) i ⊗ₜ[R] leftCoeff R A i x = x := by
  classical
  induction x with
  | zero => simp
  | tmul a y =>
    calc ∑ i, (hopfBasis R A) i ⊗ₜ[R] leftCoeff R A i (a ⊗ₜ[R] y)
        = ∑ i, ((hopfBasis R A).coord i a • (hopfBasis R A) i) ⊗ₜ[R] y := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [leftCoeff_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    _ = (∑ i, (hopfBasis R A).coord i a • (hopfBasis R A) i) ⊗ₜ[R] y := by
          rw [TensorProduct.sum_tmul]
    _ = a ⊗ₜ[R] y := by
          congr 1
          simp only [Module.Basis.coord_apply]
          exact (hopfBasis R A).sum_repr a
  | add x y ihx ihy =>
    simp only [map_add, TensorProduct.tmul_add]
    rw [Finset.sum_add_distrib, ihx, ihy]

/-- **The comultiplication matrix**: `Tᵢⱼ` is the `eᵢ`-left-coefficient of `Δ(eⱼ)`, so that
`Δ(eⱼ) = ∑ᵢ eᵢ ⊗ Tᵢⱼ` (`comul_hopfBasis`). -/
noncomputable def comulMatrix : Matrix (hopfBasisIndex R A) (hopfBasisIndex R A) A :=
  fun i j => leftCoeff R A i (Coalgebra.comul ((hopfBasis R A) j))

/-- The defining expansion of the comultiplication matrix. -/
theorem comul_hopfBasis (j : hopfBasisIndex R A) :
    Coalgebra.comul ((hopfBasis R A) j)
      = ∑ i, (hopfBasis R A) i ⊗ₜ[R] comulMatrix R A i j :=
  (sum_tmul_leftCoeff R A _).symm

end ModularCurves

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

section LeftCoeff

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Extract the `i`-th basis coefficient of the *first* tensor factor: the linear map
`A ⊗[R] M → M` sending `x ⊗ m ↦ (eᵢ-coefficient of x) • m`. -/
noncomputable def leftCoeff (i : hopfBasisIndex R A) : A ⊗[R] M →ₗ[R] M :=
  (TensorProduct.lid R M).toLinearMap.comp
    (LinearMap.rTensor M ((hopfBasis R A).coord i))

omit [Module.Finite R A] in
@[simp]
theorem leftCoeff_tmul (i : hopfBasisIndex R A) (x : A) (m : M) :
    leftCoeff R A i (x ⊗ₜ[R] m) = (hopfBasis R A).coord i x • m := by
  simp [leftCoeff]

/-- Every element of `A ⊗[R] M` is the sum of basis vectors tensor its left
coefficients. -/
theorem sum_tmul_leftCoeff (x : A ⊗[R] M) :
    ∑ i, (hopfBasis R A) i ⊗ₜ[R] leftCoeff R A i x = x := by
  classical
  induction x with
  | zero => simp
  | tmul a m =>
    calc ∑ i, (hopfBasis R A) i ⊗ₜ[R] leftCoeff R A i (a ⊗ₜ[R] m)
        = ∑ i, ((hopfBasis R A).coord i a • (hopfBasis R A) i) ⊗ₜ[R] m := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [leftCoeff_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    _ = (∑ i, (hopfBasis R A).coord i a • (hopfBasis R A) i) ⊗ₜ[R] m := by
          rw [TensorProduct.sum_tmul]
    _ = a ⊗ₜ[R] m := by
          congr 1
          simp only [Module.Basis.coord_apply]
          exact (hopfBasis R A).sum_repr a
  | add x y ihx ihy =>
    simp only [map_add, TensorProduct.tmul_add]
    rw [Finset.sum_add_distrib, ihx, ihy]

/-- Left coefficients of a basis-indexed sum of pure tensors. -/
theorem leftCoeff_sum_tmul (x : hopfBasisIndex R A → M) (k : hopfBasisIndex R A) :
    leftCoeff R A k (∑ i, (hopfBasis R A) i ⊗ₜ[R] x i) = x k := by
  classical
  rw [map_sum]
  simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

/-- Basis-indexed sums of pure tensors are determined by their coefficients. -/
theorem sum_tmul_injective {x y : hopfBasisIndex R A → M}
    (h : ∑ i, (hopfBasis R A) i ⊗ₜ[R] x i = ∑ i, (hopfBasis R A) i ⊗ₜ[R] y i) :
    x = y := by
  funext k
  rw [← leftCoeff_sum_tmul R A x k, h, leftCoeff_sum_tmul R A y k]

end LeftCoeff

/-- **The comultiplication matrix**: `Tᵢⱼ` is the `eᵢ`-left-coefficient of `Δ(eⱼ)`, so that
`Δ(eⱼ) = ∑ᵢ eᵢ ⊗ Tᵢⱼ` (`comul_hopfBasis`). -/
noncomputable def comulMatrix : Matrix (hopfBasisIndex R A) (hopfBasisIndex R A) A :=
  fun i j => leftCoeff R A i (Coalgebra.comul ((hopfBasis R A) j))

/-- The defining expansion of the comultiplication matrix. -/
theorem comul_hopfBasis (j : hopfBasisIndex R A) :
    Coalgebra.comul ((hopfBasis R A) j)
      = ∑ i, (hopfBasis R A) i ⊗ₜ[R] comulMatrix R A i j :=
  (sum_tmul_leftCoeff R A _).symm

/-- **Counit identity of the Δ-matrix**: `ε(Tᵢⱼ) = δᵢⱼ`. -/
theorem counit_comulMatrix (i j : hopfBasisIndex R A) :
    Coalgebra.counit (R := R) (comulMatrix R A i j) = if i = j then (1 : R) else 0 := by
  classical
  have hlaw := congr($(Coalgebra.lTensor_counit_comp_comul (R := R) (A := A))
    ((hopfBasis R A) j))
  rw [LinearMap.comp_apply, comul_hopfBasis, map_sum] at hlaw
  have hexp : ∀ k, (LinearMap.lTensor A (Coalgebra.counit (R := R)))
      ((hopfBasis R A) k ⊗ₜ[R] comulMatrix R A k j)
      = (hopfBasis R A) k ⊗ₜ[R] Coalgebra.counit (R := R) (comulMatrix R A k j) := by
    intro k
    rw [LinearMap.lTensor_tmul]
  rw [Finset.sum_congr rfl fun k _ => hexp k] at hlaw
  have hflip : ((TensorProduct.mk R A R).flip 1) ((hopfBasis R A) j)
      = ∑ k, (hopfBasis R A) k ⊗ₜ[R] (if k = j then (1 : R) else 0) := by
    rw [show ((TensorProduct.mk R A R).flip 1) ((hopfBasis R A) j)
        = (hopfBasis R A) j ⊗ₜ[R] (1 : R) from rfl]
    rw [Finset.sum_congr rfl fun k _ => by
      rw [TensorProduct.tmul_ite]]
    rw [Finset.sum_ite_eq' Finset.univ j (fun k => (hopfBasis R A) k ⊗ₜ[R] (1 : R))]
    simp
  rw [hflip] at hlaw
  have := congrFun (sum_tmul_injective R A hlaw) i
  simpa using this

/-- **Matrix-comultiplication identity of the Δ-matrix**: `Δ(Tᵢⱼ) = ∑ₖ Tᵢₖ ⊗ Tₖⱼ` —
coassociativity along the basis. -/
theorem comul_comulMatrix (i j : hopfBasisIndex R A) :
    Coalgebra.comul (R := R) (comulMatrix R A i j)
      = ∑ k, comulMatrix R A i k ⊗ₜ[R] comulMatrix R A k j := by
  classical
  have hlaw := congr($(Coalgebra.coassoc (R := R) (A := A)) ((hopfBasis R A) j))
  rw [LinearMap.comp_apply, LinearMap.comp_apply, comul_hopfBasis, map_sum, map_sum] at hlaw
  have hL : ∀ k, (TensorProduct.assoc R A A A)
      ((LinearMap.rTensor A (Coalgebra.comul (R := R)))
        ((hopfBasis R A) k ⊗ₜ[R] comulMatrix R A k j))
      = ∑ l, (hopfBasis R A) l ⊗ₜ[R]
          (comulMatrix R A l k ⊗ₜ[R] comulMatrix R A k j) := by
    intro k
    rw [LinearMap.rTensor_tmul, comul_hopfBasis, TensorProduct.sum_tmul, map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [TensorProduct.assoc_tmul]
  have hlhs : (∑ k, (TensorProduct.assoc R A A A)
        ((LinearMap.rTensor A (Coalgebra.comul (R := R)))
          ((hopfBasis R A) k ⊗ₜ[R] comulMatrix R A k j)))
      = ∑ l, (hopfBasis R A) l ⊗ₜ[R]
          (∑ k, comulMatrix R A l k ⊗ₜ[R] comulMatrix R A k j) :=
    (Finset.sum_congr rfl fun k _ => hL k).trans
      ((Finset.sum_comm).trans
        (Finset.sum_congr rfl fun l _ => (TensorProduct.tmul_sum _ _ _).symm))
  have hrhs : (∑ k, (LinearMap.lTensor A (Coalgebra.comul (R := R)))
        ((hopfBasis R A) k ⊗ₜ[R] comulMatrix R A k j))
      = ∑ k, (hopfBasis R A) k ⊗ₜ[R]
          Coalgebra.comul (R := R) (comulMatrix R A k j) :=
    Finset.sum_congr rfl fun k _ => LinearMap.lTensor_tmul _ _ _ _
  have hrhs2 : (LinearMap.lTensor A (Coalgebra.comul (R := R)) ∘ₗ
        (Coalgebra.comul (R := R))) ((hopfBasis R A) j)
      = ∑ k, (hopfBasis R A) k ⊗ₜ[R]
          Coalgebra.comul (R := R) (comulMatrix R A k j) := by
    rw [LinearMap.comp_apply, comul_hopfBasis, map_sum]
    exact hrhs
  have hcombined := (hlhs.symm.trans hlaw).trans hrhs2
  exact (congrFun (sum_tmul_injective R A hcombined) i).symm

end ModularCurves

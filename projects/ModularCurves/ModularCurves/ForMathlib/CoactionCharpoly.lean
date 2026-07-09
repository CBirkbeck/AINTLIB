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

/-- The matrix-comultiplication identity packaged as a `Coalgebra.Repr` of `Δ(Tᵢⱼ)`. -/
noncomputable def comulMatrixRepr (i j : hopfBasisIndex R A) :
    Coalgebra.Repr R (comulMatrix R A i j) (hopfBasisIndex R A) where
  index := Finset.univ
  left := fun k => comulMatrix R A i k
  right := fun k => comulMatrix R A k j
  eq := (comul_comulMatrix R A i j).symm

/-- **The entrywise antipode inverts the Δ-matrix from the left**: `T.map S * T = 1`. -/
theorem antipodeMatrix_mul_comulMatrix :
    (comulMatrix R A).map (HopfAlgebra.antipode R) * comulMatrix R A = 1 := by
  classical
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have h := HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit (comulMatrixRepr R A i j)
  rw [counit_comulMatrix] at h
  simpa [Matrix.map_apply, apply_ite (algebraMap R A), comulMatrixRepr] using h

/-- **The entrywise antipode inverts the Δ-matrix from the right**: `T * T.map S = 1`. -/
theorem comulMatrix_mul_antipodeMatrix :
    comulMatrix R A * (comulMatrix R A).map (HopfAlgebra.antipode R) = 1 := by
  classical
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have h := HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit (comulMatrixRepr R A i j)
  rw [counit_comulMatrix] at h
  simpa [Matrix.map_apply, apply_ite (algebraMap R A), comulMatrixRepr] using h

/-- The Δ-matrix is a unit of the matrix ring, with explicit inverse the entrywise
antipode. -/
theorem isUnit_comulMatrix : IsUnit (comulMatrix R A) :=
  ⟨⟨comulMatrix R A, (comulMatrix R A).map (HopfAlgebra.antipode R),
    comulMatrix_mul_antipodeMatrix R A, antipodeMatrix_mul_comulMatrix R A⟩, rfl⟩

/-! ### The right-slot mirror -/

section RightCoeff

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Extract the `i`-th basis coefficient of the *second* tensor factor: the linear map
`M ⊗[R] A → M` sending `m ⊗ x ↦ (eᵢ-coefficient of x) • m`. -/
noncomputable def rightCoeff (i : hopfBasisIndex R A) : M ⊗[R] A →ₗ[R] M :=
  (TensorProduct.rid R M).toLinearMap.comp
    (LinearMap.lTensor M ((hopfBasis R A).coord i))

omit [Module.Finite R A] in
@[simp]
theorem rightCoeff_tmul (i : hopfBasisIndex R A) (m : M) (x : A) :
    rightCoeff R A i (m ⊗ₜ[R] x) = (hopfBasis R A).coord i x • m := by
  simp [rightCoeff]

/-- Every element of `M ⊗[R] A` is the sum of its right coefficients tensor basis
vectors. -/
theorem sum_rightCoeff_tmul (x : M ⊗[R] A) :
    ∑ i, rightCoeff R A i x ⊗ₜ[R] (hopfBasis R A) i = x := by
  classical
  induction x with
  | zero => simp
  | tmul m a =>
    calc ∑ i, rightCoeff R A i (m ⊗ₜ[R] a) ⊗ₜ[R] (hopfBasis R A) i
        = ∑ i, m ⊗ₜ[R] ((hopfBasis R A).coord i a • (hopfBasis R A) i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [rightCoeff_tmul, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    _ = m ⊗ₜ[R] (∑ i, (hopfBasis R A).coord i a • (hopfBasis R A) i) := by
          rw [TensorProduct.tmul_sum]
    _ = m ⊗ₜ[R] a := by
          congr 1
          simp only [Module.Basis.coord_apply]
          exact (hopfBasis R A).sum_repr a
  | add x y ihx ihy =>
    simp only [map_add, TensorProduct.add_tmul]
    rw [Finset.sum_add_distrib, ihx, ihy]

/-- Right coefficients of a basis-indexed sum of pure tensors. -/
theorem rightCoeff_sum_tmul (x : hopfBasisIndex R A → M) (k : hopfBasisIndex R A) :
    rightCoeff R A k (∑ i, x i ⊗ₜ[R] (hopfBasis R A) i) = x k := by
  classical
  rw [map_sum]
  simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

/-- Basis-indexed sums of pure tensors are determined by their right coefficients. -/
theorem sum_tmul_injective' {x y : hopfBasisIndex R A → M}
    (h : ∑ i, x i ⊗ₜ[R] (hopfBasis R A) i = ∑ i, y i ⊗ₜ[R] (hopfBasis R A) i) :
    x = y := by
  funext k
  rw [← rightCoeff_sum_tmul R A x k, h, rightCoeff_sum_tmul R A y k]

end RightCoeff

/-- **The right-slot Δ-matrix**: `T̃ᵢⱼ` is the `eᵢ`-right-coefficient of `Δ(eⱼ)`, so that
`Δ(eⱼ) = ∑ᵢ T̃ᵢⱼ ⊗ eᵢ` (`comul_hopfBasis'`). -/
noncomputable def comulMatrixR : Matrix (hopfBasisIndex R A) (hopfBasisIndex R A) A :=
  fun i j => rightCoeff R A i (Coalgebra.comul ((hopfBasis R A) j))

/-- The defining expansion of the right-slot Δ-matrix. -/
theorem comul_hopfBasis' (j : hopfBasisIndex R A) :
    Coalgebra.comul ((hopfBasis R A) j)
      = ∑ i, comulMatrixR R A i j ⊗ₜ[R] (hopfBasis R A) i :=
  (sum_rightCoeff_tmul R A _).symm

/-- **Counit identity of the right-slot Δ-matrix**: `ε(T̃ᵢⱼ) = δᵢⱼ`. -/
theorem counit_comulMatrixR (i j : hopfBasisIndex R A) :
    Coalgebra.counit (R := R) (comulMatrixR R A i j) = if i = j then (1 : R) else 0 := by
  classical
  have hlaw := congr($(Coalgebra.rTensor_counit_comp_comul (R := R) (A := A))
    ((hopfBasis R A) j))
  rw [LinearMap.comp_apply, comul_hopfBasis', map_sum] at hlaw
  have hexp : (∑ k, (LinearMap.rTensor A (Coalgebra.counit (R := R)))
      (comulMatrixR R A k j ⊗ₜ[R] (hopfBasis R A) k))
      = ∑ k, Coalgebra.counit (R := R) (comulMatrixR R A k j)
          ⊗ₜ[R] (hopfBasis R A) k :=
    Finset.sum_congr rfl fun k _ => LinearMap.rTensor_tmul _ _ _ _
  rw [hexp] at hlaw
  have hone : (∑ k, (if k = j then (1 : R) else 0) ⊗ₜ[R] (hopfBasis R A) k)
      = ((TensorProduct.mk R R A) 1) ((hopfBasis R A) j) := by
    rw [Finset.sum_congr rfl fun k _ =>
      TensorProduct.ite_tmul (1 : R) ((hopfBasis R A) k) (k = j)]
    rw [Finset.sum_ite_eq' Finset.univ j (fun k => (1 : R) ⊗ₜ[R] (hopfBasis R A) k)]
    simp
  rw [← hone] at hlaw
  exact congrFun (sum_tmul_injective' R A hlaw) i

/-- **Matrix-comultiplication identity of the right-slot Δ-matrix**:
`Δ(T̃ᵢⱼ) = ∑ₖ T̃ₖⱼ ⊗ T̃ᵢₖ` — coassociativity along the basis, mirrored. -/
theorem comul_comulMatrixR (i j : hopfBasisIndex R A) :
    Coalgebra.comul (R := R) (comulMatrixR R A i j)
      = ∑ k, comulMatrixR R A k j ⊗ₜ[R] comulMatrixR R A i k := by
  classical
  have hlaw := congr($(Coalgebra.coassoc (R := R) (A := A)) ((hopfBasis R A) j))
  have hlaw2 := congrArg (TensorProduct.assoc R A A A).symm hlaw
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at hlaw2
  have hlhs : (LinearMap.rTensor A (Coalgebra.comul (R := R)) ∘ₗ
        (Coalgebra.comul (R := R))) ((hopfBasis R A) j)
      = ∑ k, Coalgebra.comul (R := R) (comulMatrixR R A k j) ⊗ₜ[R] (hopfBasis R A) k := by
    rw [LinearMap.comp_apply, comul_hopfBasis', map_sum]
    exact Finset.sum_congr rfl fun k _ => LinearMap.rTensor_tmul _ _ _ _
  have hR : ∀ p, (TensorProduct.assoc R A A A).symm
      ((LinearMap.lTensor A (Coalgebra.comul (R := R)))
        (comulMatrixR R A p j ⊗ₜ[R] (hopfBasis R A) p))
      = ∑ q, (comulMatrixR R A p j ⊗ₜ[R] comulMatrixR R A q p)
          ⊗ₜ[R] (hopfBasis R A) q := by
    intro p
    rw [LinearMap.lTensor_tmul, comul_hopfBasis', TensorProduct.tmul_sum, map_sum]
    exact Finset.sum_congr rfl fun q _ => by
      rw [show (TensorProduct.assoc R A A A).symm
          (comulMatrixR R A p j ⊗ₜ[R] (comulMatrixR R A q p ⊗ₜ[R] (hopfBasis R A) q))
          = (comulMatrixR R A p j ⊗ₜ[R] comulMatrixR R A q p) ⊗ₜ[R] (hopfBasis R A) q from
        TensorProduct.assoc_symm_tmul _ _ _]
  have hrhs : (TensorProduct.assoc R A A A).symm
      ((LinearMap.lTensor A (Coalgebra.comul (R := R)) ∘ₗ
        (Coalgebra.comul (R := R))) ((hopfBasis R A) j))
      = ∑ q, (∑ p, comulMatrixR R A p j ⊗ₜ[R] comulMatrixR R A q p)
          ⊗ₜ[R] (hopfBasis R A) q := by
    rw [LinearMap.comp_apply, comul_hopfBasis', map_sum, map_sum]
    refine (Finset.sum_congr rfl fun p _ => hR p).trans ?_
    refine (Finset.sum_comm).trans ?_
    exact Finset.sum_congr rfl fun q _ => (TensorProduct.sum_tmul _ _ _).symm
  have hcombined := (hlhs.symm.trans hlaw2).trans hrhs
  exact congrFun (sum_tmul_injective' R A hcombined) i

/-- The mirrored matrix-comultiplication identity packaged as a `Coalgebra.Repr`. -/
noncomputable def comulMatrixRRepr (i j : hopfBasisIndex R A) :
    Coalgebra.Repr R (comulMatrixR R A i j) (hopfBasisIndex R A) where
  index := Finset.univ
  left := fun k => comulMatrixR R A k j
  right := fun k => comulMatrixR R A i k
  eq := (comul_comulMatrixR R A i j).symm

/-- The entrywise antipode inverts the right-slot Δ-matrix from the right:
`T̃ * T̃.map S = 1`. -/
theorem comulMatrixR_mul_antipodeMatrixR :
    comulMatrixR R A * (comulMatrixR R A).map (HopfAlgebra.antipode R) = 1 := by
  classical
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have h := HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit (comulMatrixRRepr R A i j)
  rw [counit_comulMatrixR] at h
  rw [Finset.sum_congr rfl fun p _ => show comulMatrixR R A i p *
      (comulMatrixR R A).map (HopfAlgebra.antipode R) p j
      = HopfAlgebra.antipode R (comulMatrixR R A p j) * comulMatrixR R A i p from by
    rw [Matrix.map_apply, mul_comm]]
  simpa [comulMatrixRRepr, apply_ite (algebraMap R A)] using h

/-- The entrywise antipode inverts the right-slot Δ-matrix from the left:
`T̃.map S * T̃ = 1`. -/
theorem antipodeMatrixR_mul_comulMatrixR :
    (comulMatrixR R A).map (HopfAlgebra.antipode R) * comulMatrixR R A = 1 := by
  classical
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have h := HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit (comulMatrixRRepr R A i j)
  rw [counit_comulMatrixR] at h
  rw [Finset.sum_congr rfl fun p _ => show (comulMatrixR R A).map
      (HopfAlgebra.antipode R) i p * comulMatrixR R A p j
      = comulMatrixR R A p j * HopfAlgebra.antipode R (comulMatrixR R A i p) from by
    rw [Matrix.map_apply, mul_comm]]
  simpa [comulMatrixRRepr, apply_ite (algebraMap R A)] using h

/-- The right-slot Δ-matrix is a unit. -/
theorem isUnit_comulMatrixR : IsUnit (comulMatrixR R A) :=
  ⟨⟨comulMatrixR R A, (comulMatrixR R A).map (HopfAlgebra.antipode R),
    comulMatrixR_mul_antipodeMatrixR R A, antipodeMatrixR_mul_comulMatrixR R A⟩, rfl⟩

/-! ### The multiplication matrix on `B ⊗ A` -/

section MulMatrix

variable {B : Type*} [CommRing B] [Algebra R B]

/-- **The multiplication matrix** of `u : B ⊗[R] A` in the `B`-basis `1 ⊗ eⱼ`:
`u·(1 ⊗ eⱼ) = ∑ᵢ Mᵢⱼ ⊗ eᵢ` (`mul_one_tmul_hopfBasis`). -/
noncomputable def mulMatrix (u : B ⊗[R] A) :
    Matrix (hopfBasisIndex R A) (hopfBasisIndex R A) B :=
  fun i j => rightCoeff R A i (u * (1 : B) ⊗ₜ[R] (hopfBasis R A) j)

/-- The defining expansion of the multiplication matrix. -/
theorem mul_one_tmul_hopfBasis (u : B ⊗[R] A) (j : hopfBasisIndex R A) :
    u * (1 : B) ⊗ₜ[R] (hopfBasis R A) j
      = ∑ i, mulMatrix R A u i j ⊗ₜ[R] (hopfBasis R A) i :=
  (sum_rightCoeff_tmul R A _).symm

/-- **Transport of the multiplication matrix along an algebra map** `φ : B → B''`:
the matrix of `(φ ⊗ id)(u)` is the entrywise `φ`-image of the matrix of `u`. -/
theorem mulMatrix_map {B'' : Type*} [CommRing B''] [Algebra R B''] (φ : B →ₐ[R] B'')
    (u : B ⊗[R] A) :
    mulMatrix R A ((Algebra.TensorProduct.map φ (AlgHom.id R A)) u)
      = (mulMatrix R A u).map φ := by
  classical
  ext i j
  have hexp := congrArg (Algebra.TensorProduct.map φ (AlgHom.id R A))
    (mul_one_tmul_hopfBasis R A u j)
  rw [map_mul, map_sum] at hexp
  rw [show (Algebra.TensorProduct.map φ (AlgHom.id R A)) ((1 : B) ⊗ₜ[R] (hopfBasis R A) j)
      = (1 : B'') ⊗ₜ[R] (hopfBasis R A) j from by
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.coe_id, id_eq]] at hexp
  rw [Finset.sum_congr rfl (fun k _ => show (Algebra.TensorProduct.map φ (AlgHom.id R A))
      (mulMatrix R A u k j ⊗ₜ[R] (hopfBasis R A) k)
      = φ (mulMatrix R A u k j) ⊗ₜ[R] (hopfBasis R A) k from by
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq])] at hexp
  rw [show mulMatrix R A ((Algebra.TensorProduct.map φ (AlgHom.id R A)) u) i j
      = rightCoeff R A i ((Algebra.TensorProduct.map φ (AlgHom.id R A)) u
        * (1 : B'') ⊗ₜ[R] (hopfBasis R A) j) from rfl, hexp, rightCoeff_sum_tmul]
  rfl

omit [Module.Finite R A] in
/-- `rightCoeff` commutes with the left `B`-action on `B ⊗[R] A`. -/
theorem rightCoeff_smul (i : hopfBasisIndex R A) (b : B) (x : B ⊗[R] A) :
    rightCoeff R A i (b • x) = b * rightCoeff R A i x := by
  induction x with
  | zero => simp
  | tmul m a =>
    rw [TensorProduct.smul_tmul', rightCoeff_tmul, rightCoeff_tmul, smul_eq_mul,
      Algebra.mul_smul_comm]
  | add x y ihx ihy => rw [smul_add, map_add, map_add, ihx, ihy, mul_add]

omit [Module.Finite R A] in
/-- The multiplication matrix of the left inclusion is scalar: `mulMatrix (b ⊗ 1) = b•1`. -/
theorem mulMatrix_includeLeft (b : B) :
    mulMatrix R A (b ⊗ₜ[R] (1 : A)) = Matrix.diagonal (fun _ => b) := by
  classical
  ext i j
  rw [show mulMatrix R A (b ⊗ₜ[R] (1 : A)) i j
      = rightCoeff R A i ((b ⊗ₜ[R] (1 : A)) * (1 : B) ⊗ₜ[R] (hopfBasis R A) j) from rfl]
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, rightCoeff_tmul,
    Module.Basis.coord_apply, Module.Basis.repr_self, Matrix.diagonal_apply]
  rw [Finsupp.single_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- Multiplicativity of the multiplication matrix: `mulMatrix (u·v) = mulMatrix u * mulMatrix v`. -/
theorem mulMatrix_mul (u v : B ⊗[R] A) :
    mulMatrix R A (u * v) = mulMatrix R A u * mulMatrix R A v := by
  classical
  ext i j
  have hexp : (u * v) * (1 : B) ⊗ₜ[R] (hopfBasis R A) j
      = ∑ k, mulMatrix R A v k j • (u * (1 : B) ⊗ₜ[R] (hopfBasis R A) k) := by
    calc (u * v) * (1 : B) ⊗ₜ[R] (hopfBasis R A) j
        = u * (v * (1 : B) ⊗ₜ[R] (hopfBasis R A) j) := by ring
      _ = u * (∑ k, mulMatrix R A v k j ⊗ₜ[R] (hopfBasis R A) k) := by
          rw [mul_one_tmul_hopfBasis]
      _ = ∑ k, u * (mulMatrix R A v k j ⊗ₜ[R] (hopfBasis R A) k) := by
          rw [Finset.mul_sum]
      _ = ∑ k, mulMatrix R A v k j • (u * (1 : B) ⊗ₜ[R] (hopfBasis R A) k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [show mulMatrix R A v k j ⊗ₜ[R] (hopfBasis R A) k
              = mulMatrix R A v k j • ((1 : B) ⊗ₜ[R] (hopfBasis R A) k) from by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], mul_smul_comm]
  rw [show mulMatrix R A (u * v) i j
      = rightCoeff R A i ((u * v) * (1 : B) ⊗ₜ[R] (hopfBasis R A) j) from rfl, hexp,
    map_sum, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rightCoeff_smul]
  show mulMatrix R A v k j * mulMatrix R A u i k
      = mulMatrix R A u i k * mulMatrix R A v k j
  ring

end MulMatrix

end ModularCurves

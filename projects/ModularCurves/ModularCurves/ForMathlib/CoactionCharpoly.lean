/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.Coaction
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Algebra.Polynomial.Lifts

/-!
# The comultiplication matrix of a finite free Hopf algebra

Construction support for `[CHARTER-HOPF]` / `T-G3d-infra` Piece 3
(`.mathlib-quality/decomposition-hopf-crux.md`, leaf `[HG-B2]`, design refinement §Δ-matrix):
for a Hopf `R`-algebra `A` that is finite free as an `R`-module with basis `e`, the
**right-slot comultiplication matrix** `T̃ ∈ Mat(A)` is defined by `Δ(eⱼ) = ∑ᵢ T̃ᵢⱼ ⊗ eᵢ`
(`comulMatrixR`, `comul_hopfBasis'`). The coalgebra axioms expand along the basis to the
*matrix-coalgebra identities*

* `counit_comulMatrixR` — `ε(T̃ᵢⱼ) = δᵢⱼ`;
* `comul_comulMatrixR` — `Δ(T̃ᵢⱼ) = ∑ₖ T̃ₖⱼ ⊗ T̃ᵢₖ`;

and the antipode axioms make `T̃` invertible with **explicit inverse the entrywise
antipode** (`comulMatrixR_mul_antipodeMatrixR`, `antipodeMatrixR_mul_comulMatrixR`,
`isUnit_comulMatrixR`).

This is the engine of the `03BH`/`03BJ` chain: the **multiplication matrix** `mulMatrix`
of `ρ(f)` on `B ⊗ A` is conjugate, over `B ⊗ A`, to its own `ρ`-image via `T̃`
(`mulMatrix_map_coaction_conj`, the conjugation identity (★)), so the **co-action
characteristic polynomial** `coactionCharpoly` has coinvariant coefficients
(`map_coactionCharpoly`, 03BH) and witnesses integrality of `B` over the co-invariants
(`isIntegral_coinvariants`, 03BJ).
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

section Star

variable {B : Type*} [CommRing B] [Algebra R B]

/-- The reassociated comultiplication `δ̃ : B⊗A → (B⊗A)⊗A`, an algebra map. -/
noncomputable def deltaTilde : (B ⊗[R] A) →ₐ[R] (B ⊗[R] A) ⊗[R] A :=
  (Algebra.TensorProduct.assoc R R R B A A).symm.toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id R B) (Bialgebra.comulAlgHom R A))

omit [Module.Free R A] [Module.Finite R A] in
/-- The coassociativity bridge: on the image of the co-action, `δ̃` is `ρ ⊗ id`. -/
theorem deltaTilde_comp_coaction (ρ : B →ₐ[R] B ⊗[R] A) (hρ : IsCoaction ρ) :
    (deltaTilde R A).comp ρ
      = (Algebra.TensorProduct.map ρ (AlgHom.id R A)).comp ρ := by
  rw [deltaTilde, AlgHom.comp_assoc, ← hρ.coassoc, ← AlgHom.comp_assoc,
    ← AlgHom.comp_assoc]
  rw [show ((Algebra.TensorProduct.assoc R R R B A A).symm.toAlgHom.comp
      (Algebra.TensorProduct.assoc R R R B A A).toAlgHom)
      = AlgHom.id R ((B ⊗[R] A) ⊗[R] A) from by
    ext <;> rfl]
  rw [AlgHom.id_comp]

/-- `δ̃` of the right inclusion, expanded along the right-slot Δ-matrix. -/
theorem deltaTilde_one_tmul (j : hopfBasisIndex R A) :
    deltaTilde R A ((1 : B) ⊗ₜ[R] (hopfBasis R A) j)
      = ∑ p, ((1 : B) ⊗ₜ[R] comulMatrixR R A p j) ⊗ₜ[R] (hopfBasis R A) p := by
  rw [deltaTilde, AlgHom.comp_apply]
  rw [show (Algebra.TensorProduct.map (AlgHom.id R B) (Bialgebra.comulAlgHom R A))
      ((1 : B) ⊗ₜ[R] (hopfBasis R A) j)
      = (1 : B) ⊗ₜ[R] Coalgebra.comul (R := R) ((hopfBasis R A) j) from by
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl]
  rw [comul_hopfBasis', TensorProduct.tmul_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  show (Algebra.TensorProduct.assoc R R R B A A).symm
      ((1 : B) ⊗ₜ[R] (comulMatrixR R A p j ⊗ₜ[R] (hopfBasis R A) p))
      = ((1 : B) ⊗ₜ[R] comulMatrixR R A p j) ⊗ₜ[R] (hopfBasis R A) p
  simp

omit [Module.Free R A] [Module.Finite R A] in
/-- `δ̃` of a left-inclusion scalar is the ambient left-inclusion scalar. -/
theorem deltaTilde_tmul_one (b : B) :
    deltaTilde R A (b ⊗ₜ[R] (1 : A))
      = (b ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A) := by
  rw [deltaTilde, AlgHom.comp_apply]
  rw [show (Algebra.TensorProduct.map (AlgHom.id R B) (Bialgebra.comulAlgHom R A))
      (b ⊗ₜ[R] (1 : A)) = b ⊗ₜ[R] ((1 : A) ⊗ₜ[R] (1 : A)) from by
    rw [Algebra.TensorProduct.map_tmul]
    rw [show (Bialgebra.comulAlgHom R A) (1 : A) = (1 : A) ⊗ₜ[R] (1 : A) from by
      rw [map_one, Algebra.TensorProduct.one_def]]
    rfl]
  show (Algebra.TensorProduct.assoc R R R B A A).symm
      (b ⊗ₜ[R] ((1 : A) ⊗ₜ[R] (1 : A)))
      = (b ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A)
  simp

/-- The LHS `deltaTilde`-expansion of the conjugation identity: `Δ̃(ρf · (1 ⊗ eⱼ))`
expands, via the co-action square `deltaTilde_comp_coaction`, into a double sum over the
Hopf basis with `mulMatrix (ρ f)` coefficients. -/
theorem deltaTilde_coaction_mul_hopfBasis (ρ : B →ₐ[R] B ⊗[R] A) (hρ : IsCoaction ρ) (f : B) :
    ∀ j, deltaTilde R A ((ρ f) * (1 : B) ⊗ₜ[R] (hopfBasis R A) j)
      = ∑ q, (∑ p, ρ (mulMatrix R A (ρ f) q p) * ((1 : B) ⊗ₜ[R] comulMatrixR R A p j))
          ⊗ₜ[R] (hopfBasis R A) q := by
  classical
  set M := mulMatrix R A (ρ f) with hM
  intro j
  rw [map_mul, show deltaTilde R A (ρ f)
      = (Algebra.TensorProduct.map ρ (AlgHom.id R A)) (ρ f) from
    AlgHom.congr_fun (deltaTilde_comp_coaction R A ρ hρ) f, deltaTilde_one_tmul,
    Finset.mul_sum]
  have hterm : ∀ p, (Algebra.TensorProduct.map ρ (AlgHom.id R A)) (ρ f)
      * (((1 : B) ⊗ₜ[R] comulMatrixR R A p j) ⊗ₜ[R] (hopfBasis R A) p)
      = ∑ q, (ρ (M q p) * ((1 : B) ⊗ₜ[R] comulMatrixR R A p j))
          ⊗ₜ[R] (hopfBasis R A) q := by
    intro p
    have hsmul : (((1 : B) ⊗ₜ[R] comulMatrixR R A p j) ⊗ₜ[R] (hopfBasis R A) p)
        = ((1 : B) ⊗ₜ[R] comulMatrixR R A p j)
          • ((1 : B ⊗[R] A) ⊗ₜ[R] (hopfBasis R A) p) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hsmul, mul_smul_comm]
    rw [show (Algebra.TensorProduct.map ρ (AlgHom.id R A)) (ρ f)
        * ((1 : B ⊗[R] A) ⊗ₜ[R] (hopfBasis R A) p)
        = ∑ q, mulMatrix R A ((Algebra.TensorProduct.map ρ (AlgHom.id R A)) (ρ f)) q p
            ⊗ₜ[R] (hopfBasis R A) q from mul_one_tmul_hopfBasis R A _ p]
    rw [mulMatrix_map, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.map_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_comm]
  rw [Finset.sum_congr rfl fun p _ => hterm p, Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => (TensorProduct.sum_tmul _ _ _).symm

/-- The RHS `deltaTilde`-expansion of the conjugation identity: `Δ̃(∑ₖ Mₖⱼ ⊗ eₖ)`
(where `M = mulMatrix (ρ f)`) expands into a double sum over the Hopf basis. -/
theorem deltaTilde_sum_mulMatrix_hopfBasis (ρ : B →ₐ[R] B ⊗[R] A) (f : B) :
    ∀ j, deltaTilde R A (∑ k, mulMatrix R A (ρ f) k j ⊗ₜ[R] (hopfBasis R A) k)
      = ∑ q, (∑ k, ((1 : B) ⊗ₜ[R] comulMatrixR R A q k)
            * (mulMatrix R A (ρ f) k j ⊗ₜ[R] (1 : A)))
          ⊗ₜ[R] (hopfBasis R A) q := by
  classical
  set M := mulMatrix R A (ρ f) with hM
  intro j
  rw [map_sum]
  have hterm : ∀ k, deltaTilde R A (M k j ⊗ₜ[R] (hopfBasis R A) k)
      = ∑ q, ((M k j ⊗ₜ[R] (1 : A)) * ((1 : B) ⊗ₜ[R] comulMatrixR R A q k))
          ⊗ₜ[R] (hopfBasis R A) q := by
    intro k
    rw [show (M k j ⊗ₜ[R] (hopfBasis R A) k)
        = (M k j ⊗ₜ[R] (1 : A)) * ((1 : B) ⊗ₜ[R] (hopfBasis R A) k) from by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], map_mul,
      deltaTilde_tmul_one, deltaTilde_one_tmul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show ((M k j ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A))
        * (((1 : B) ⊗ₜ[R] comulMatrixR R A q k) ⊗ₜ[R] (hopfBasis R A) q)
        = ((M k j ⊗ₜ[R] (1 : A)) * ((1 : B) ⊗ₜ[R] comulMatrixR R A q k))
          ⊗ₜ[R] ((1 : A) * (hopfBasis R A) q) from
      Algebra.TensorProduct.tmul_mul_tmul _ _ _ _, one_mul]
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => by
    rw [← TensorProduct.sum_tmul]
    congr 1
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **The conjugation identity (★)**: for a co-action `ρ` and `f : B`, with
`M := mulMatrix (ρ f)` and `Θ := (comulMatrixR).map includeRight`,
`M.map ρ * Θ = Θ * M.map includeLeft` in matrices over `B ⊗[R] A`. -/
theorem mulMatrix_map_coaction_conj (ρ : B →ₐ[R] B ⊗[R] A) (hρ : IsCoaction ρ) (f : B) :
    (mulMatrix R A (ρ f)).map ρ
        * (comulMatrixR R A).map (Algebra.TensorProduct.includeRight (R := R) (A := B))
      = (comulMatrixR R A).map (Algebra.TensorProduct.includeRight (R := R) (A := B))
        * (mulMatrix R A (ρ f)).map (Algebra.TensorProduct.includeLeft (S := R)) := by
  classical
  have hLHS := deltaTilde_coaction_mul_hopfBasis R A ρ hρ f
  have hRHS := deltaTilde_sum_mulMatrix_hopfBasis R A ρ f
  set M := mulMatrix R A (ρ f) with hM
  ext i j
  have hcombined := (hLHS j).symm.trans
    ((congrArg (deltaTilde R A) (mul_one_tmul_hopfBasis R A (ρ f) j)).trans (hRHS j))
  have hcoef := congrFun (sum_tmul_injective' R A hcombined) i
  rw [Matrix.mul_apply, Matrix.mul_apply]
  calc ∑ p, (M.map ρ) i p
        * (comulMatrixR R A).map (Algebra.TensorProduct.includeRight (R := R) (A := B)) p j
      = ∑ p, ρ (M i p) * ((1 : B) ⊗ₜ[R] comulMatrixR R A p j) :=
        Finset.sum_congr rfl fun p _ => by rw [Matrix.map_apply, Matrix.map_apply]; rfl
    _ = ∑ k, ((1 : B) ⊗ₜ[R] comulMatrixR R A i k) * (M k j ⊗ₜ[R] (1 : A)) := hcoef
    _ = ∑ k, (comulMatrixR R A).map (Algebra.TensorProduct.includeRight (R := R) (A := B)) i k
          * (M.map (Algebra.TensorProduct.includeLeft (S := R))) k j :=
        Finset.sum_congr rfl fun k _ => by rw [Matrix.map_apply, Matrix.map_apply]; rfl

end Star

section Integrality

variable {B : Type*} [CommRing B] [Algebra R B]

/-- Characteristic polynomials of matrices conjugate by an explicitly invertible matrix
agree. -/
theorem _root_.Matrix.charpoly_eq_of_conj {n : Type*} [Fintype n] [DecidableEq n]
    {K : Type*} [CommRing K] {N₁ N₂ U V : Matrix n n K} (hUV : U * V = 1)
    (hconj : N₁ * U = U * N₂) : N₁.charpoly = N₂.charpoly := by
  classical
  have hdet : (U.map Polynomial.C) * (V.map Polynomial.C) = 1 := by
    rw [← Matrix.map_mul, hUV]
    exact Matrix.map_one _ Polynomial.C_0 Polynomial.C_1
  have hdetUV : (U.map Polynomial.C).det * (V.map Polynomial.C).det = 1 := by
    rw [← Matrix.det_mul, hdet, Matrix.det_one]
  have hcharm : Matrix.charmatrix N₁ * (U.map Polynomial.C)
      = (U.map Polynomial.C) * Matrix.charmatrix N₂ := by
    rw [Matrix.charmatrix, Matrix.charmatrix, sub_mul, mul_sub]
    congr 1
    · exact (Matrix.scalar_commute (Polynomial.X : Polynomial K)
        (fun r => Commute.all _ r) (U.map Polynomial.C)).eq
    · rw [show U.map ⇑Polynomial.C = Polynomial.C.mapMatrix U from
        (RingHom.mapMatrix_apply _ _).symm, ← map_mul, ← map_mul, hconj]
  have hdet2 : N₁.charmatrix.det
      = ((U.map Polynomial.C) * (N₂.charmatrix * (V.map Polynomial.C))).det := by
    simpa [Matrix.mul_assoc, hdet] using
      congrArg (fun W => Matrix.det (W * (V.map Polynomial.C))) hcharm
  calc N₁.charpoly
      = (U.map Polynomial.C).det * (N₂.charmatrix.det * (V.map Polynomial.C).det) := by
        rw [Matrix.charpoly, hdet2, Matrix.det_mul, Matrix.det_mul]
    _ = N₂.charmatrix.det * ((U.map Polynomial.C).det * (V.map Polynomial.C).det) := by
        ring
    _ = N₂.charpoly := by rw [hdetUV, mul_one, Matrix.charpoly]

/-- **The characteristic polynomial of the co-action** of `f : B`: the charpoly of the
multiplication matrix of `ρ(f)` on `B ⊗[R] A`. Monic, with coinvariant coefficients
(`coactionCharpoly_coeff_mem`). -/
noncomputable def coactionCharpoly (ρ : B →ₐ[R] B ⊗[R] A) (f : B) : Polynomial B :=
  (mulMatrix R A (ρ f)).charpoly

theorem coactionCharpoly_monic (ρ : B →ₐ[R] B ⊗[R] A) (f : B) :
    (coactionCharpoly R A ρ f).Monic :=
  Matrix.charpoly_monic _

/-- **03BH, comodule form**: the coefficients of the co-action charpoly are coinvariant —
`map ρ P = map ι P` via the conjugation identity (★). -/
theorem map_coactionCharpoly (ρ : B →ₐ[R] B ⊗[R] A) (hρ : IsCoaction ρ) (f : B) :
    (coactionCharpoly R A ρ f).map ρ.toRingHom
      = (coactionCharpoly R A ρ f).map
          (Algebra.TensorProduct.includeLeft (S := R)).toRingHom := by
  classical
  rw [coactionCharpoly, ← Matrix.charpoly_map, ← Matrix.charpoly_map]
  have hUV : (comulMatrixR R A).map
        ⇑(Algebra.TensorProduct.includeRight (R := R) (A := B) (B := A))
      * (comulMatrixR R A).map
          (⇑(Algebra.TensorProduct.includeRight (R := R) (A := B) (B := A))
            ∘ ⇑(HopfAlgebra.antipode R)) = 1 := by
    have h := congrArg
      ((Algebra.TensorProduct.includeRight (R := R) (A := B)
        (B := A)).toRingHom.mapMatrix (m := hopfBasisIndex R A))
      (comulMatrixR_mul_antipodeMatrixR R A)
    have h1 : (Matrix.map (1 : Matrix (hopfBasisIndex R A) (hopfBasisIndex R A) A)
        ⇑(Algebra.TensorProduct.includeRight (R := R) (A := B) (B := A))) = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    rw [← h1]
    simpa [map_mul, RingHom.mapMatrix_apply] using h
  exact Matrix.charpoly_eq_of_conj hUV (mulMatrix_map_coaction_conj R A ρ hρ f)

theorem coactionCharpoly_coeff_mem (ρ : B →ₐ[R] B ⊗[R] A) (hρ : IsCoaction ρ) (f : B)
    (k : ℕ) : (coactionCharpoly R A ρ f).coeff k ∈ coinvariants ρ := by
  simpa [Polynomial.coeff_map, mem_coinvariants] using
    congrArg (fun q => Polynomial.coeff q k) (map_coactionCharpoly R A ρ hρ f)

/-- The multiplication-matrix map, packaged as a ring homomorphism — the (faithful) matrix
representation of `B ⊗[R] A` acting on itself in the basis `1 ⊗ eⱼ`. -/
noncomputable def mulMatrixHom :
    (B ⊗[R] A) →+* Matrix (hopfBasisIndex R A) (hopfBasisIndex R A) B where
  toFun := mulMatrix R A
  map_one' := by
    classical
    have h := mulMatrix_includeLeft R A (B := B) 1
    rw [show ((1 : B) ⊗ₜ[R] (1 : A)) = (1 : B ⊗[R] A) from
      (Algebra.TensorProduct.one_def).symm] at h
    exact h.trans Matrix.diagonal_one
  map_mul' := mulMatrix_mul R A
  map_zero' := by
    ext i j
    show rightCoeff R A i ((0 : B ⊗[R] A) * _) = 0
    rw [zero_mul, map_zero]
  map_add' := fun u v => by
    ext i j
    show rightCoeff R A i ((u + v) * _) = _
    rw [add_mul, map_add]
    rfl

/-- The matrix representation is faithful: `mulMatrix u = 0` forces `u = 0`
(reconstruct `u = u·1` from the expansions over a basis decomposition of `1`). -/
theorem eq_zero_of_mulMatrix_eq_zero {u : B ⊗[R] A} (h : mulMatrix R A u = 0) :
    u = 0 := by
  classical
  have hu : u = u * ((1 : B) ⊗ₜ[R] (1 : A)) := by
    rw [← Algebra.TensorProduct.one_def, mul_one]
  have hone : ((1 : B) ⊗ₜ[R] (1 : A) : B ⊗[R] A)
      = ∑ j, (hopfBasis R A).coord j 1 • ((1 : B) ⊗ₜ[R] (hopfBasis R A) j) := by
    have h1A : (1 : A) = ∑ j, (hopfBasis R A).coord j 1 • (hopfBasis R A) j := by
      simp only [Module.Basis.coord_apply]
      exact ((hopfBasis R A).sum_repr 1).symm
    calc ((1 : B) ⊗ₜ[R] (1 : A) : B ⊗[R] A)
        = (1 : B) ⊗ₜ[R] (∑ j, (hopfBasis R A).coord j 1 • (hopfBasis R A) j) := by
          rw [← h1A]
      _ = ∑ j, (hopfBasis R A).coord j 1 • ((1 : B) ⊗ₜ[R] (hopfBasis R A) j) := by
          rw [TensorProduct.tmul_sum]
          exact Finset.sum_congr rfl fun j _ => TensorProduct.tmul_smul _ _ _
  rw [hu, hone, Finset.mul_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [mul_smul_comm, mul_one_tmul_hopfBasis, h]
  simp

/-- **Cayley–Hamilton, scalar form**: the co-action charpoly, evaluated through the left
inclusion at `ρ(f)`, vanishes — `∑ᵢ (Pᵢ ⊗ 1)·ρ(f)^i = 0`. -/
theorem eval₂_includeLeft_coactionCharpoly (ρ : B →ₐ[R] B ⊗[R] A) (f : B) :
    Polynomial.eval₂ (Algebra.TensorProduct.includeLeft (S := R)).toRingHom (ρ f)
      (coactionCharpoly R A ρ f) = 0 := by
  classical
  refine eq_zero_of_mulMatrix_eq_zero R A ?_
  have h := Polynomial.hom_eval₂ (coactionCharpoly R A ρ f)
    (Algebra.TensorProduct.includeLeft (S := R)).toRingHom (mulMatrixHom R A) (ρ f)
  rw [show (mulMatrixHom R A).comp
      (Algebra.TensorProduct.includeLeft (S := R)).toRingHom
      = algebraMap B (Matrix (hopfBasisIndex R A) (hopfBasisIndex R A) B) from by
    refine RingHom.ext fun b => ?_
    show mulMatrix R A (b ⊗ₜ[R] (1 : A)) = _
    rw [mulMatrix_includeLeft, Matrix.algebraMap_eq_diagonal]
    rfl] at h
  show (mulMatrixHom R A) (Polynomial.eval₂
      (Algebra.TensorProduct.includeLeft (S := R)).toRingHom (ρ f)
      (coactionCharpoly R A ρ f)) = 0
  rw [h]
  show Polynomial.aeval (mulMatrixHom R A (ρ f)) (coactionCharpoly R A ρ f) = 0
  rw [show mulMatrixHom R A (ρ f) = mulMatrix R A (ρ f) from rfl, coactionCharpoly]
  exact Matrix.aeval_self_charpoly _

/-- The counit retraction `σ : B ⊗[R] A → B`, `b ⊗ a ↦ ε(a)·b` — a left inverse of both
the inclusion and (by counitality) the co-action. -/
noncomputable def counitRetraction : (B ⊗[R] A) →ₐ[R] B :=
  (Algebra.TensorProduct.rid R R B).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id R B) (Bialgebra.counitAlgHom R A))

omit [Module.Free R A] [Module.Finite R A] in
theorem counitRetraction_comp_coaction (ρ : B →ₐ[R] B ⊗[R] A) (hρ : IsCoaction ρ) :
    (counitRetraction R A).comp ρ = AlgHom.id R B := by
  rw [counitRetraction, AlgHom.comp_assoc]
  exact hρ.counit

omit [Module.Free R A] [Module.Finite R A] in
theorem counitRetraction_comp_includeLeft :
    (counitRetraction R A).comp (Algebra.TensorProduct.includeLeft (S := R))
      = AlgHom.id R B := by
  ext b
  show (Algebra.TensorProduct.rid R R B)
      ((Algebra.TensorProduct.map (AlgHom.id R B) (Bialgebra.counitAlgHom R A))
        (b ⊗ₜ[R] 1)) = b
  rw [Algebra.TensorProduct.map_tmul, map_one, Algebra.TensorProduct.rid_tmul, one_smul]
  rfl

/-- **03BJ, comodule form — the integrality theorem**: every element of `B` is integral
over the co-invariants of a co-action of a finite free Hopf algebra, via the monic
co-action charpoly. -/
theorem isIntegral_coinvariants (ρ : B →ₐ[R] B ⊗[R] A) (hρ : IsCoaction ρ) (f : B) :
    IsIntegral (coinvariants ρ) f := by
  classical
  rcases subsingleton_or_nontrivial B with hB | hB
  · exact ⟨Polynomial.X, Polynomial.monic_X, Subsingleton.elim _ _⟩
  -- the charpoly annihilates f in B, via the counit retraction
  have hev : (coactionCharpoly R A ρ f).eval f = 0 := by
    have h := congrArg (counitRetraction R A) (eval₂_includeLeft_coactionCharpoly R A ρ f)
    rw [map_zero] at h
    rw [← h, show (counitRetraction R A) (Polynomial.eval₂
        (Algebra.TensorProduct.includeLeft (S := R)).toRingHom (ρ f)
        (coactionCharpoly R A ρ f))
      = Polynomial.eval₂ ((counitRetraction R A).toRingHom.comp
          (Algebra.TensorProduct.includeLeft (S := R)).toRingHom)
        ((counitRetraction R A) (ρ f)) (coactionCharpoly R A ρ f) from
      Polynomial.hom_eval₂ _ _ _ _]
    rw [show (counitRetraction R A).toRingHom.comp
        (Algebra.TensorProduct.includeLeft (S := R)).toRingHom = RingHom.id B from by
      have := counitRetraction_comp_includeLeft R A (B := B)
      exact congrArg AlgHom.toRingHom this,
      show (counitRetraction R A) (ρ f) = f from
        AlgHom.congr_fun (counitRetraction_comp_coaction R A ρ hρ) f,
      Polynomial.eval₂_id]
  -- lift the charpoly to the co-invariants
  have hlift : coactionCharpoly R A ρ f
      ∈ Polynomial.lifts (algebraMap (coinvariants ρ) B) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, coactionCharpoly_coeff_mem R A ρ hρ f n⟩, rfl⟩
  obtain ⟨q, hq_map, _, hq_monic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlift (coactionCharpoly_monic R A ρ f)
  exact ⟨q, hq_monic, by
    rw [Polynomial.eval₂_eq_eval_map, hq_map]
    exact hev⟩

end Integrality

end ModularCurves

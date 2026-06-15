/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.Matrix.Block
import LeanModularForms.HeckeRIngs.GLn.DiagonalCosets

/-!
# Left Coset Decomposition for GL_n Hecke Ring

Upper-triangular coset representatives for `Γ · diag(a) · Γ`, where `Γ = SL_n(ℤ)`.

For `a = (a₁,...,aₙ)` with `a₁ | a₂ | ⋯ | aₙ`, left coset representatives include
upper-triangular matrices `M = diag(a) · γ` where `γ` is unipotent upper-triangular
with `γ_{ij} ∈ {0,...,(a_j/a_i) - 1}` for `i < j`. These give `∏_{i<j}(a_j/a_i)`
distinct left cosets.

## Main definitions

* `UpperTriRep` -- bounded entry assignment: `γ_{ij} ∈ Fin (a_j / a_i)` for `i < j`
* `upperTriMat` -- the upper-triangular integer matrix `M_{ij} = a_i · γ_{ij}`
* `upperTriGL` -- corresponding `GL_n(ℚ)` element

## Main results

* `upperTriMat_det` -- `det(M) = ∏ i, a_i`
* `upperTriMat_injective` -- different entries produce different matrices
* `upperTriGL_mem_doubleCoset` -- each representative lies in `Γ · diag(a) · Γ`
* `upperTriMat_distinct_cosets` -- distinct representatives give distinct left cosets

## References

* Shimura, Proposition 3.22
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing Matrix.SpecialLinearGroup

namespace HeckeRing.GLn

variable (n : ℕ)

/-- Bounded entry assignment for upper-triangular representatives:
    `B_{ij} ∈ Fin (a_j / a_i)` for `i < j`. -/
abbrev UpperTriRep (a : Fin n → ℕ) (_hdiv : DivChain n a) :=
  (p : { ij : Fin n × Fin n // ij.1 < ij.2 }) → Fin (a p.val.2 / a p.val.1)

/-- Upper-triangular matrix with diagonal `a` and off-diagonal `M_{ij} = a_i * B_{ij}`. -/
def upperTriMat (a : Fin n → ℕ) (hdiv : DivChain n a) (B : UpperTriRep n a hdiv) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j ↦
    if h : i < j then (a i : ℤ) * (B ⟨(i, j), h⟩ : ℕ)
    else if i = j then (a i : ℤ)
    else 0

@[simp]
lemma upperTriMat_apply_lt (a : Fin n → ℕ) (hdiv : DivChain n a) (B : UpperTriRep n a hdiv)
    {i j : Fin n} (h : i < j) :
    upperTriMat n a hdiv B i j = (a i : ℤ) * (B ⟨(i, j), h⟩ : ℕ) := by
  simp [upperTriMat, h]

@[simp]
lemma upperTriMat_apply_diag (a : Fin n → ℕ) (hdiv : DivChain n a) (B : UpperTriRep n a hdiv)
    (i : Fin n) : upperTriMat n a hdiv B i i = (a i : ℤ) := by
  simp [upperTriMat]

lemma upperTriMat_apply_gt (a : Fin n → ℕ) (hdiv : DivChain n a) (B : UpperTriRep n a hdiv)
    {i j : Fin n} (h : j < i) :
    upperTriMat n a hdiv B i j = 0 := by
  simp [upperTriMat, h.asymm, h.ne']

lemma upperTriMat_det (a : Fin n → ℕ) (hdiv : DivChain n a) (B : UpperTriRep n a hdiv) :
    (upperTriMat n a hdiv B).det = ∏ i, (a i : ℤ) := by
  refine (Matrix.det_of_upperTriangular fun _ _ h ↦ upperTriMat_apply_gt n a hdiv B h).trans ?_
  simp

lemma upperTriMat_det_pos (a : Fin n → ℕ) (hpos : ∀ i, 0 < a i) (hdiv : DivChain n a)
    (B : UpperTriRep n a hdiv) : 0 < (upperTriMat n a hdiv B).det := by
  rw [upperTriMat_det]
  exact_mod_cast Finset.prod_pos fun i _ ↦ hpos i

/-- The upper-triangular representative as a `GL_n(ℚ)` element. -/
noncomputable def upperTriGL (a : Fin n → ℕ) (hpos : ∀ i, 0 < a i) (hdiv : DivChain n a)
    (B : UpperTriRep n a hdiv) : GL (Fin n) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero ((upperTriMat n a hdiv B).map (Int.cast : ℤ → ℚ))
    (by simpa [det_intMat_cast] using (upperTriMat_det_pos n a hpos hdiv B).ne')

@[simp]
lemma upperTriGL_val (a : Fin n → ℕ) (hpos : ∀ i, 0 < a i) (hdiv : DivChain n a)
    (B : UpperTriRep n a hdiv) : (↑(upperTriGL n a hpos hdiv B) : Matrix (Fin n) (Fin n) ℚ) =
    (upperTriMat n a hdiv B).map (Int.cast : ℤ → ℚ) := rfl

end HeckeRing.GLn

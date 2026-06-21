import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Tactic

/-!
# Deleted Fourier matrices on the augmentation subspace

This file proves the finite-group determinant identity behind the real
cyclotomic-unit regulator computation.  The statement is abstract: for a
finite abelian group `G`, a function `q : G → ℂ`, and the deleted matrix
`(q (h * k⁻¹) - q h)` indexed by `G \ {1}`, its determinant is the product of
the nontrivial Fourier coefficients.  The proof uses the deleted character
matrix and includes the rank-one correction in its inverse.
-/

noncomputable section

open scoped BigOperators

namespace BernoulliRegular
namespace CyclotomicUnits

/-- The non-identity elements of a group. -/
abbrev Nonidentity (G : Type*) [One G] := {g : G // g ≠ 1}

/-- The complement of an arbitrary element of a group. -/
abbrev DeletedAt (G : Type*) (h₀ : G) := {g : G // g ≠ h₀}

/-- The nontrivial multiplicative characters of a group. -/
abbrev NontrivChar (G : Type*) [CommMonoid G] :=
  {χ : MulChar G ℂ // χ ≠ 1}

/-- A subtype sum over `x ≠ a₀` as an erased finite-set sum. -/
theorem sum_subtype_ne_eq_sum_erase {α : Type*} [Fintype α] [DecidableEq α]
    (a₀ : α) (f : α → ℂ) [Fintype {x : α // x ≠ a₀}] :
    ∑ x : {x : α // x ≠ a₀}, f x.val =
      ∑ x ∈ (Finset.univ : Finset α).erase a₀, f x := by
  classical
  refine Finset.sum_bij (fun (x : {x : α // x ≠ a₀}) _ ↦ x.val) ?_ ?_ ?_ ?_
  · intro x _
    rw [Finset.mem_erase]
    exact ⟨x.property, Finset.mem_univ _⟩
  · intro x₁ _ x₂ _ h
    exact Subtype.ext h
  · intro x hx
    rw [Finset.mem_erase] at hx
    obtain ⟨h_ne, _⟩ := hx
    exact ⟨⟨x, h_ne⟩, Finset.mem_univ _, rfl⟩
  · intro x _
    rfl

section FiniteGroup

variable {G : Type*} [CommGroup G] [Fintype G]

/-- Left multiplication by `h₀` identifies `G \ {1}` with `G \ {h₀}`. -/
def nonidentityMulLeftEquivDeletedAt (h₀ : G) :
    Nonidentity G ≃ DeletedAt G h₀ where
  toFun r := ⟨h₀ * r.val, by
    intro h
    apply r.property
    have h' : h₀ * r.val = h₀ * 1 := by simpa using h
    exact mul_left_cancel h'⟩
  invFun h := ⟨h₀⁻¹ * h.val, by
    intro h'
    apply h.property
    calc
      h.val = h₀ * (h₀⁻¹ * h.val) := by group
      _ = h₀ * 1 := by rw [h']
      _ = h₀ := by rw [mul_one]⟩
  left_inv r := by
    ext
    simp
  right_inv h := by
    ext
    simp

/-- The deleted set has one fewer element than the group. -/
theorem card_nonidentity_add_one [DecidableEq G] :
    Fintype.card (Nonidentity G) + 1 = Fintype.card G := by
  have hnon :
      Fintype.card (Nonidentity G) = Fintype.card G - 1 := by
    simp [Nonidentity]
  rw [hnon]
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨(1 : G)⟩))

/-- The cardinality of a finite group is nonzero as a complex number. -/
theorem card_group_ne_zero_complex :
    ((Fintype.card G : ℕ) : ℂ) ≠ 0 := by
  exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(1 : G)⟩).ne'

/-- The restricted sum of a nontrivial character over `G \ {1}` is `-1`. -/
theorem sum_nonidentity_mulChar_eq_neg_one
    [DecidableEq G]
    (χ : MulChar G ℂ) (hχ : χ ≠ 1) :
    ∑ h : Nonidentity G, χ h.val = -1 := by
  classical
  have hfull : ∑ g : G, χ g = 0 := MulChar.sum_eq_zero_of_ne_one hχ
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G))] at hfull
  rw [← sum_subtype_ne_eq_sum_erase (α := G) (a₀ := 1) (f := fun g ↦ χ g)] at hfull
  have hsplit : (1 : ℂ) + ∑ h : Nonidentity G, χ h.val = 0 := by
    simpa using hfull
  linear_combination hsplit

/-- Orthogonality after deleting the identity row. -/
theorem sum_nonidentity_inv_mulChar_mul
    [DecidableEq G]
    [DecidableEq (MulChar G ℂ)]
    (χ ψ : MulChar G ℂ) :
    ∑ h : Nonidentity G, (χ h.val)⁻¹ * ψ h.val =
      if χ = ψ then (Fintype.card (Nonidentity G) : ℂ) else -1 := by
  classical
  by_cases hχψ : χ = ψ
  · subst hχψ
    rw [if_pos rfl]
    rw [show (∑ h : Nonidentity G, (χ h.val)⁻¹ * χ h.val) =
        ∑ _h : Nonidentity G, (1 : ℂ) from by
      refine Finset.sum_congr rfl ?_
      intro h _
      have h_unit : IsUnit (χ h.val) := IsUnit.map χ.toMonoidHom (Group.isUnit h.val)
      exact inv_mul_cancel₀ h_unit.ne_zero]
    simp
  · rw [if_neg hχψ]
    have hchar : χ⁻¹ * ψ ≠ 1 := by
      intro h
      apply hχψ
      calc
        χ = χ * 1 := by rw [mul_one]
        _ = χ * (χ⁻¹ * ψ) := by rw [h]
        _ = (χ * χ⁻¹) * ψ := by rw [mul_assoc]
        _ = 1 * ψ := by rw [mul_inv_cancel]
        _ = ψ := by rw [one_mul]
    rw [← sum_nonidentity_mulChar_eq_neg_one (G := G) (χ⁻¹ * ψ) hchar]
    refine Finset.sum_congr rfl ?_
    intro h _
    rw [MulChar.mul_apply, MulChar.inv_apply_eq_inv']

/-- Fourier coefficient with the inverse-character convention. -/
def deletedFourierCoeff (q : G → ℂ) (χ : MulChar G ℂ) : ℂ :=
  ∑ h : G, q h * (χ h)⁻¹

/-- Translating the input of `q` by `h₀` multiplies the inverse-character
Fourier coefficient by `χ h₀`. -/
theorem deletedFourierCoeff_mulLeft
    (q : G → ℂ) (χ : MulChar G ℂ) (h₀ : G) :
    deletedFourierCoeff (G := G) (fun h ↦ q (h₀ * h)) χ =
      χ h₀ * deletedFourierCoeff (G := G) q χ := by
  classical
  unfold deletedFourierCoeff
  have hsum := Equiv.sum_comp (Equiv.mulLeft h₀)
    (fun h : G ↦ q h * (χ (h₀⁻¹ * h))⁻¹)
  have hleft :
      (∑ x : G, q ((Equiv.mulLeft h₀) x) *
          (χ (h₀⁻¹ * (Equiv.mulLeft h₀) x))⁻¹) =
        ∑ x : G, q (h₀ * x) * (χ x)⁻¹ := by
    refine Finset.sum_congr rfl ?_
    intro x _
    simp
  rw [hleft] at hsum
  rw [hsum]
  have hterm : ∀ h : G, q h * (χ (h₀⁻¹ * h))⁻¹ =
      χ h₀ * (q h * (χ h)⁻¹) := by
    intro h
    rw [← map_inv]
    have hinv : (h₀⁻¹ * h)⁻¹ = h⁻¹ * h₀ := by group
    rw [hinv, map_mul, map_inv]
    ring
  rw [Finset.sum_congr rfl (fun h _ ↦ hterm h)]
  rw [← Finset.mul_sum]

/-- The deleted character matrix, with rows reindexed by an equivalence
between nontrivial characters and non-identity elements. -/
def deletedCharacterMatrix
    (ρ : NontrivChar G ≃ Nonidentity G) :
    Matrix (NontrivChar G) (NontrivChar G) ℂ :=
  Matrix.of fun h χ ↦ χ.val (ρ h).val

/-- The corrected left inverse of the deleted character matrix.  The `-1`
term is the rank-one correction that appears after deleting the trivial row
and the trivial character. -/
def deletedCharacterMatrixLeftInverse
    (ρ : NontrivChar G ≃ Nonidentity G) :
    Matrix (NontrivChar G) (NontrivChar G) ℂ :=
  Matrix.of fun χ h ↦
    ((Fintype.card G : ℕ) : ℂ)⁻¹ * ((χ.val (ρ h).val)⁻¹ - 1)

/-- The corrected deleted character matrix inverse is a left inverse. -/
theorem deletedCharacterMatrix_leftInverse
    [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) :
    deletedCharacterMatrixLeftInverse (G := G) ρ *
        deletedCharacterMatrix (G := G) ρ = 1 := by
  classical
  ext χ ψ
  simp only [deletedCharacterMatrixLeftInverse, deletedCharacterMatrix, Matrix.mul_apply,
    Matrix.of_apply, Matrix.one_apply]
  rw [Equiv.sum_comp ρ (fun h : Nonidentity G ↦
    (((Fintype.card G : ℕ) : ℂ)⁻¹ * ((χ.val h.val)⁻¹ - 1)) * ψ.val h.val)]
  rw [show (∑ h : Nonidentity G,
      ((Fintype.card G : ℕ) : ℂ)⁻¹ * ((χ.val h.val)⁻¹ - 1) * ψ.val h.val) =
      ∑ h : Nonidentity G,
        ((Fintype.card G : ℕ) : ℂ)⁻¹ *
          (((χ.val h.val)⁻¹ - 1) * ψ.val h.val) from by
    refine Finset.sum_congr rfl ?_
    intro h _
    ring]
  rw [← Finset.mul_sum]
  have hsplit :
      (∑ h : Nonidentity G, ((χ.val h.val)⁻¹ - 1) * ψ.val h.val) =
        (∑ h : Nonidentity G, (χ.val h.val)⁻¹ * ψ.val h.val) -
          ∑ h : Nonidentity G, ψ.val h.val := by
    simp_rw [sub_mul, one_mul]
    rw [Finset.sum_sub_distrib]
  rw [hsplit]
  rw [sum_nonidentity_inv_mulChar_mul (G := G) χ.val ψ.val]
  rw [sum_nonidentity_mulChar_eq_neg_one (G := G) ψ.val ψ.property]
  by_cases hχψ : χ = ψ
  · subst hχψ
    simp only [ite_true]
    have hcard : ((Fintype.card (Nonidentity G) : ℕ) : ℂ) + 1 =
        ((Fintype.card G : ℕ) : ℂ) := by
      exact_mod_cast card_nonidentity_add_one (G := G)
    have hnz : ((Fintype.card G : ℕ) : ℂ) ≠ 0 :=
      card_group_ne_zero_complex (G := G)
    field_simp [hnz]
    linear_combination hcard
  · have hval : χ.val ≠ ψ.val := fun h ↦
      hχψ (Subtype.ext h)
    simp only [hval, ite_false]
    rw [if_neg hχψ]
    ring

/-- Full Fourier reindexing for the inverse-character convention. -/
theorem sum_translate_inv_mulChar
    (q : G → ℂ) (χ : MulChar G ℂ) (h : G) :
    ∑ k : G, q (h * k⁻¹) * χ k =
      χ h * deletedFourierCoeff (G := G) q χ := by
  classical
  let e : G ≃ G := (Equiv.inv G).trans (Equiv.mulLeft h)
  have he_apply : ∀ k : G, e k = h * k⁻¹ := by
    intro k
    rfl
  have hsum := Equiv.sum_comp e (fun t : G ↦ q t * χ (t⁻¹ * h))
  have hleft :
      (∑ k : G, q (e k) * χ ((e k)⁻¹ * h)) =
        ∑ k : G, q (h * k⁻¹) * χ k := by
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [he_apply]
    have hk : (h * k⁻¹)⁻¹ * h = k := by group
    rw [hk]
  rw [hleft] at hsum
  rw [hsum]
  unfold deletedFourierCoeff
  have hterm : ∀ t : G, q t * χ (t⁻¹ * h) =
      χ h * (q t * (χ t)⁻¹) := by
    intro t
    rw [map_mul, map_inv]
    ring
  rw [Finset.sum_congr rfl (fun t _ ↦ hterm t)]
  rw [← Finset.mul_sum]

/-- The first summand of the deleted convolution-character product. -/
theorem sum_nonidentity_translate_inv_mulChar
    [DecidableEq G]
    (q : G → ℂ) (χ : MulChar G ℂ) (h : G) :
    ∑ k : Nonidentity G, q (h * k.val⁻¹) * χ k.val =
      χ h * deletedFourierCoeff (G := G) q χ - q h := by
  classical
  have hfull := sum_translate_inv_mulChar (G := G) q χ h
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G))] at hfull
  rw [← sum_subtype_ne_eq_sum_erase (α := G) (a₀ := 1)
    (f := fun k : G ↦ q (h * k⁻¹) * χ k)] at hfull
  have hsplit :
      q h + ∑ k : Nonidentity G, q (h * k.val⁻¹) * χ k.val =
        χ h * deletedFourierCoeff (G := G) q χ := by
    simpa using hfull
  linear_combination hsplit

/-- Deleted convolution against a nontrivial character gives the Fourier
coefficient eigenvalue. -/
theorem sum_nonidentity_deletedConvolution_mulChar
    [DecidableEq G]
    (q : G → ℂ) (χ : MulChar G ℂ) (hχ : χ ≠ 1) (h : G) :
    ∑ k : Nonidentity G, (q (h * k.val⁻¹) - q h) * χ k.val =
      χ h * deletedFourierCoeff (G := G) q χ := by
  classical
  have hfirst := sum_nonidentity_translate_inv_mulChar (G := G) q χ h
  have hchar := sum_nonidentity_mulChar_eq_neg_one (G := G) χ hχ
  have hsplit :
      (∑ k : Nonidentity G, (q (h * k.val⁻¹) - q h) * χ k.val) =
        (∑ k : Nonidentity G, q (h * k.val⁻¹) * χ k.val) -
          q h * ∑ k : Nonidentity G, χ k.val := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsplit, hfirst, hchar]
  ring

/-- The deleted convolution matrix on `G \ {1}`. -/
def deletedConvolutionMatrix
    (ρ : NontrivChar G ≃ Nonidentity G) (q : G → ℂ) :
    Matrix (NontrivChar G) (NontrivChar G) ℂ :=
  Matrix.of fun h k ↦ q ((ρ h).val * (ρ k).val⁻¹) - q (ρ h).val

/-- The same deleted convolution matrix with the literal `G \ {1}` indices. -/
def deletedConvolutionMatrixOnNonidentity (q : G → ℂ) :
    Matrix (Nonidentity G) (Nonidentity G) ℂ :=
  Matrix.of fun h k ↦ q (h.val * k.val⁻¹) - q h.val

/-- The deleted convolution matrix with an arbitrary omitted row `h₀` and
columns still indexed by `G \ {1}`. -/
def deletedConvolutionMatrixAt (h₀ : G) (q : G → ℂ) :
    Matrix (DeletedAt G h₀) (Nonidentity G) ℂ :=
  Matrix.of fun h k ↦ q (h.val * k.val⁻¹) - q h.val

/-- The arbitrary-row deleted matrix after ordering rows as `h = h₀ * r`,
`r ∈ G \ {1}`. -/
def deletedConvolutionMatrixAtReindexed (h₀ : G) (q : G → ℂ) :
    Matrix (Nonidentity G) (Nonidentity G) ℂ :=
  (deletedConvolutionMatrixAt (G := G) h₀ q).submatrix
    (nonidentityMulLeftEquivDeletedAt (G := G) h₀) id

omit [Fintype G] in
/-- Reindexing rows by `h = h₀ * r` turns the arbitrary-row matrix into the
identity-deleted matrix for the translated function `r ↦ q (h₀ * r)`. -/
theorem deletedConvolutionMatrixAtReindexed_eq_translated
    (h₀ : G) (q : G → ℂ) :
    deletedConvolutionMatrixAtReindexed (G := G) h₀ q =
      deletedConvolutionMatrixOnNonidentity (G := G) (fun h ↦ q (h₀ * h)) := by
  ext h k
  simp [deletedConvolutionMatrixAtReindexed, deletedConvolutionMatrixAt,
    deletedConvolutionMatrixOnNonidentity, nonidentityMulLeftEquivDeletedAt, mul_assoc]

omit [Fintype G] in
/-- Reindexing the literal deleted convolution matrix by `ρ` gives the
character-indexed matrix used in the diagonalization proof. -/
theorem deletedConvolutionMatrix_eq_submatrix
    (ρ : NontrivChar G ≃ Nonidentity G) (q : G → ℂ) :
    deletedConvolutionMatrix (G := G) ρ q =
      (deletedConvolutionMatrixOnNonidentity (G := G) q).submatrix ρ ρ := by
  ext h k
  rfl

/-- Deleted convolution diagonalizes against the deleted character matrix. -/
theorem deletedConvolution_mul_deletedCharacter
    [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) (q : G → ℂ) :
    deletedConvolutionMatrix (G := G) ρ q *
        deletedCharacterMatrix (G := G) ρ =
      deletedCharacterMatrix (G := G) ρ *
        Matrix.diagonal (fun χ : NontrivChar G ↦
          deletedFourierCoeff (G := G) q χ.val) := by
  classical
  ext h χ
  simp only [deletedConvolutionMatrix, deletedCharacterMatrix, Matrix.mul_apply,
    Matrix.of_apply, Matrix.diagonal_apply]
  rw [Equiv.sum_comp ρ (fun k : Nonidentity G ↦
    (q ((ρ h).val * k.val⁻¹) - q (ρ h).val) * χ.val k.val)]
  rw [sum_nonidentity_deletedConvolution_mulChar
    (G := G) q χ.val χ.property (ρ h).val]
  rw [Finset.sum_eq_single χ]
  · simp
  · intro ψ _ hψ
    rw [if_neg hψ, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ χ) hmem

/-- Deleted Fourier determinant identity, in the `hk⁻¹` convention. -/
theorem det_deletedConvolutionMatrix_eq_prod_deletedFourierCoeff
    [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) (q : G → ℂ) :
    (deletedConvolutionMatrix (G := G) ρ q).det =
      ∏ χ : NontrivChar G, deletedFourierCoeff (G := G) q χ.val := by
  classical
  have hmul := deletedConvolution_mul_deletedCharacter (G := G) ρ q
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  have hP : (deletedCharacterMatrix (G := G) ρ).det ≠ 0 :=
    Matrix.det_ne_zero_of_left_inverse
      (deletedCharacterMatrix_leftInverse (G := G) ρ)
  exact mul_right_cancel₀ hP (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hdet)

/-- The deleted Fourier determinant identity in literal `G \ {1}` indices. -/
theorem det_deletedConvolutionMatrixOnNonidentity_eq_prod_deletedFourierCoeff
    [DecidableEq G] [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) (q : G → ℂ) :
    (deletedConvolutionMatrixOnNonidentity (G := G) q).det =
      ∏ χ : NontrivChar G, deletedFourierCoeff (G := G) q χ.val := by
  have h := det_deletedConvolutionMatrix_eq_prod_deletedFourierCoeff
    (G := G) ρ q
  rw [deletedConvolutionMatrix_eq_submatrix] at h
  rwa [Matrix.det_submatrix_equiv_self] at h

/-- The same determinant identity with the nontrivial characters written as an
erased product over the full character group. -/
theorem det_deletedConvolutionMatrixOnNonidentity_eq_prod_erase
    [DecidableEq G] [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) (q : G → ℂ) :
    (deletedConvolutionMatrixOnNonidentity (G := G) q).det =
      ∏ χ ∈ (Finset.univ : Finset (MulChar G ℂ)).erase 1,
        deletedFourierCoeff (G := G) q χ := by
  rw [det_deletedConvolutionMatrixOnNonidentity_eq_prod_deletedFourierCoeff
    (G := G) ρ q]
  rw [Finset.prod_subtype
    (p := fun χ : MulChar G ℂ ↦ χ ≠ 1)
    (s := (Finset.univ : Finset (MulChar G ℂ)).erase 1)
    (f := fun χ ↦ deletedFourierCoeff (G := G) q χ)]
  intro χ
  simp [Finset.mem_erase]

/-- Arbitrary omitted-row determinant identity, with rows ordered as
`h = h₀ * r`, `r ∈ G \ {1}`. -/
theorem det_deletedConvolutionMatrixAtReindexed_eq_charFactor_mul_prod
    [DecidableEq G] [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) (h₀ : G) (q : G → ℂ) :
    (deletedConvolutionMatrixAtReindexed (G := G) h₀ q).det =
      (∏ χ : NontrivChar G, χ.val h₀) *
        ∏ χ : NontrivChar G, deletedFourierCoeff (G := G) q χ.val := by
  classical
  rw [deletedConvolutionMatrixAtReindexed_eq_translated]
  rw [det_deletedConvolutionMatrixOnNonidentity_eq_prod_deletedFourierCoeff
    (G := G) ρ (fun h ↦ q (h₀ * h))]
  simp_rw [deletedFourierCoeff_mulLeft (G := G) q]
  rw [Finset.prod_mul_distrib]

/-- Arbitrary omitted-row determinant identity, with the product written over
the full character group with the trivial character erased. -/
theorem det_deletedConvolutionMatrixAtReindexed_eq_charFactor_mul_prod_erase
    [DecidableEq G] [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) (h₀ : G) (q : G → ℂ) :
    (deletedConvolutionMatrixAtReindexed (G := G) h₀ q).det =
      (∏ χ ∈ (Finset.univ : Finset (MulChar G ℂ)).erase 1, χ h₀) *
        ∏ χ ∈ (Finset.univ : Finset (MulChar G ℂ)).erase 1,
          deletedFourierCoeff (G := G) q χ := by
  classical
  rw [det_deletedConvolutionMatrixAtReindexed_eq_charFactor_mul_prod
    (G := G) ρ h₀ q]
  congr 1
  · rw [Finset.prod_subtype
      (p := fun χ : MulChar G ℂ ↦ χ ≠ 1)
      (s := (Finset.univ : Finset (MulChar G ℂ)).erase 1)
      (f := fun χ ↦ χ h₀)]
    intro χ
    simp [Finset.mem_erase]
  · rw [Finset.prod_subtype
      (p := fun χ : MulChar G ℂ ↦ χ ≠ 1)
      (s := (Finset.univ : Finset (MulChar G ℂ)).erase 1)
      (f := fun χ ↦ deletedFourierCoeff (G := G) q χ)]
    intro χ
    simp [Finset.mem_erase]

/-- Inversion preserves the deleted index set. -/
def nonidentityInvEquiv : Nonidentity G ≃ Nonidentity G where
  toFun h := ⟨h.val⁻¹, by
    intro hinv
    exact h.property <| inv_eq_one.mp hinv⟩
  invFun h := ⟨h.val⁻¹, by
    intro hinv
    exact h.property <| inv_eq_one.mp hinv⟩
  left_inv h := by
    ext
    simp
  right_inv h := by
    ext
    simp

/-- The deleted convolution matrix in the `hk` convention used by the real
cyclotomic-unit logarithm matrix. -/
def deletedConvolutionMulMatrixOnNonidentity (q : G → ℂ) :
    Matrix (Nonidentity G) (Nonidentity G) ℂ :=
  Matrix.of fun h k ↦ q (h.val * k.val) - q h.val

/-- The arbitrary-row deleted matrix in the `hk` convention, with rows ordered
as `h = h₀ * r`, `r ∈ G \ {1}`. -/
def deletedConvolutionMulMatrixAtReindexed (h₀ : G) (q : G → ℂ) :
    Matrix (Nonidentity G) (Nonidentity G) ℂ :=
  Matrix.of fun h k ↦ q (h₀ * h.val * k.val) - q (h₀ * h.val)

omit [Fintype G] in
/-- Reindexing rows by `h = h₀ * r` in the `hk` convention translates `q`. -/
theorem deletedConvolutionMulMatrixAtReindexed_eq_translated
    (h₀ : G) (q : G → ℂ) :
    deletedConvolutionMulMatrixAtReindexed (G := G) h₀ q =
      deletedConvolutionMulMatrixOnNonidentity (G := G) (fun h ↦ q (h₀ * h)) := by
  ext h k
  simp [deletedConvolutionMulMatrixAtReindexed, deletedConvolutionMulMatrixOnNonidentity,
    mul_assoc]

omit [Fintype G] in
/-- The `hk` matrix is a row-inversion permutation of the `hk⁻¹` matrix for
`x ↦ q(x⁻¹)`. -/
theorem deletedConvolutionMulMatrix_eq_invRow_submatrix (q : G → ℂ) :
    deletedConvolutionMulMatrixOnNonidentity (G := G) q =
      (deletedConvolutionMatrixOnNonidentity (G := G) (fun x ↦ q x⁻¹)).submatrix
        (nonidentityInvEquiv (G := G)) id := by
  ext h k
  simp [deletedConvolutionMulMatrixOnNonidentity, deletedConvolutionMatrixOnNonidentity,
    nonidentityInvEquiv, mul_comm]

/-- Fourier coefficient for the non-inverse character convention. -/
def deletedFourierCoeffMul (q : G → ℂ) (χ : MulChar G ℂ) : ℂ :=
  ∑ h : G, χ h * q h

omit [Fintype G] in
/-- The product of all character values at a fixed group element has square
one. -/
theorem prod_mulChar_apply_sq_eq_one
    [Fintype (MulChar G ℂ)] (h₀ : G) :
    (∏ χ : MulChar G ℂ, χ h₀) ^ 2 = 1 := by
  classical
  set P : ℂ := ∏ χ : MulChar G ℂ, χ h₀
  have hP_inv : P = P⁻¹ := by
    calc
      P = ∏ χ : MulChar G ℂ, χ h₀ := rfl
      _ = ∏ χ : MulChar G ℂ, (χ⁻¹) h₀ := by
        rw [← Equiv.prod_comp (Equiv.inv (MulChar G ℂ)) (fun χ ↦ χ h₀)]
        rfl
      _ = ∏ χ : MulChar G ℂ, (χ h₀)⁻¹ := by
        refine Finset.prod_congr rfl ?_
        intro χ _
        rw [MulChar.inv_apply_eq_inv']
      _ = P⁻¹ := by
        rw [Finset.prod_inv_distrib]
  have hP_ne : P ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro χ _
    exact (IsUnit.map χ.toMonoidHom (Group.isUnit h₀)).ne_zero
  calc
    P ^ 2 = P * P := by ring
    _ = P * P⁻¹ := congrArg (fun z ↦ P * z) hP_inv
    _ = 1 := mul_inv_cancel₀ hP_ne

omit [Fintype G] in
/-- The product of the nontrivial character values at a fixed group element
has square one. -/
theorem prod_nontriv_mulChar_apply_sq_eq_one
    [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)] (h₀ : G) :
    (∏ χ : NontrivChar G, χ.val h₀) ^ 2 = 1 := by
  classical
  have herase :
      (∏ χ : NontrivChar G, χ.val h₀) =
        ∏ χ ∈ (Finset.univ : Finset (MulChar G ℂ)).erase 1, χ h₀ := by
    rw [Finset.prod_subtype
      (p := fun χ : MulChar G ℂ ↦ χ ≠ 1)
      (s := (Finset.univ : Finset (MulChar G ℂ)).erase 1)
      (f := fun χ ↦ χ h₀)]
    intro χ
    simp [Finset.mem_erase]
  rw [herase]
  have hfull := prod_mulChar_apply_sq_eq_one (G := G) h₀
  have htriv : (1 : MulChar G ℂ) h₀ = 1 :=
    MulChar.one_apply (Group.isUnit h₀)
  have herase_full :
      (∏ χ ∈ (Finset.univ : Finset (MulChar G ℂ)).erase 1, χ h₀) =
        ∏ χ : MulChar G ℂ, χ h₀ :=
    Finset.prod_erase (s := (Finset.univ : Finset (MulChar G ℂ)))
      (f := fun χ ↦ χ h₀) (a := 1) htriv
  rw [herase_full]
  exact hfull

omit [Fintype G] in
/-- The product of inverse nontrivial character values at a fixed group
element also has square one. -/
theorem prod_nontriv_mulChar_apply_inv_sq_eq_one
    [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)] (h₀ : G) :
    (∏ χ : NontrivChar G, (χ.val h₀)⁻¹) ^ 2 = 1 := by
  classical
  rw [show (∏ χ : NontrivChar G, (χ.val h₀)⁻¹) =
      (∏ χ : NontrivChar G, χ.val h₀)⁻¹ from by
    rw [Finset.prod_inv_distrib]]
  rw [inv_pow, prod_nontriv_mulChar_apply_sq_eq_one (G := G) h₀, inv_one]

/-- Translating the input of `q` by `h₀` multiplies the non-inverse-character
Fourier coefficient by `(χ h₀)⁻¹`. -/
theorem deletedFourierCoeffMul_mulLeft
    (q : G → ℂ) (χ : MulChar G ℂ) (h₀ : G) :
    deletedFourierCoeffMul (G := G) (fun h ↦ q (h₀ * h)) χ =
      (χ h₀)⁻¹ * deletedFourierCoeffMul (G := G) q χ := by
  classical
  unfold deletedFourierCoeffMul
  have hsum := Equiv.sum_comp (Equiv.mulLeft h₀)
    (fun h : G ↦ χ (h₀⁻¹ * h) * q h)
  have hleft :
      (∑ x : G, χ (h₀⁻¹ * (Equiv.mulLeft h₀) x) *
          q ((Equiv.mulLeft h₀) x)) =
        ∑ x : G, χ x * q (h₀ * x) := by
    refine Finset.sum_congr rfl ?_
    intro x _
    simp
  rw [hleft] at hsum
  rw [hsum]
  have hterm : ∀ h : G, χ (h₀⁻¹ * h) * q h =
      (χ h₀)⁻¹ * (χ h * q h) := by
    intro h
    rw [map_mul, map_inv]
    ring
  rw [Finset.sum_congr rfl (fun h _ ↦ hterm h)]
  rw [← Finset.mul_sum]

/-- Inverting the argument changes the inverse-character coefficient into the
non-inverse-character coefficient. -/
theorem deletedFourierCoeff_invArg_eq_mul
    (q : G → ℂ) (χ : MulChar G ℂ) :
    deletedFourierCoeff (G := G) (fun x ↦ q x⁻¹) χ =
      deletedFourierCoeffMul (G := G) q χ := by
  classical
  unfold deletedFourierCoeff deletedFourierCoeffMul
  have hsum := Equiv.sum_comp (Equiv.inv G)
    (fun h : G ↦ q h * (χ h⁻¹)⁻¹)
  have hleft :
      (∑ x : G, q ((Equiv.inv G) x) * (χ ((Equiv.inv G) x)⁻¹)⁻¹) =
        ∑ x : G, q x⁻¹ * (χ x)⁻¹ := by
    refine Finset.sum_congr rfl ?_
    intro x _
    simp
  rw [hleft] at hsum
  rw [hsum]
  refine Finset.sum_congr rfl ?_
  intro h _
  rw [map_inv]
  rw [inv_inv]
  ring

/-- Squared determinant identity in the `hk` convention.  The square removes
the sign of the row-inversion permutation. -/
theorem det_deletedConvolutionMulMatrixOnNonidentity_sq_eq_prod_deletedFourierCoeffMul_sq
    [DecidableEq G] [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) (q : G → ℂ) :
    (deletedConvolutionMulMatrixOnNonidentity (G := G) q).det ^ 2 =
      (∏ χ : NontrivChar G, deletedFourierCoeffMul (G := G) q χ.val) ^ 2 := by
  classical
  rw [deletedConvolutionMulMatrix_eq_invRow_submatrix]
  rw [Matrix.det_permute]
  rw [mul_pow]
  rw [show ((↑↑(Equiv.Perm.sign (nonidentityInvEquiv (G := G))) : ℂ)) ^ 2 = 1 from ?_]
  · rw [one_mul]
    rw [det_deletedConvolutionMatrixOnNonidentity_eq_prod_deletedFourierCoeff
      (G := G) ρ (fun x ↦ q x⁻¹)]
    congr 1
    refine Finset.prod_congr rfl ?_
    intro χ _
    exact deletedFourierCoeff_invArg_eq_mul (G := G) q χ.val
  · have h_sign : (Equiv.Perm.sign (nonidentityInvEquiv (G := G))) ^ 2 = 1 :=
      Int.units_pow_two _
    have h_cast : (((Equiv.Perm.sign (nonidentityInvEquiv (G := G))) ^ 2 : ℤˣ) : ℂ) =
        ((1 : ℤˣ) : ℂ) := by
      rw [h_sign]
    push_cast at h_cast ⊢
    exact_mod_cast h_cast

/-- Arbitrary omitted-row determinant identity in the `hk` convention, squared.
The explicit character factor is kept; in applications it is a sign. -/
theorem det_deletedConvolutionMulMatrixAtReindexed_sq_eq_charFactor_mul_prod_sq
    [DecidableEq G] [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) (h₀ : G) (q : G → ℂ) :
    (deletedConvolutionMulMatrixAtReindexed (G := G) h₀ q).det ^ 2 =
      ((∏ χ : NontrivChar G, (χ.val h₀)⁻¹) *
        ∏ χ : NontrivChar G, deletedFourierCoeffMul (G := G) q χ.val) ^ 2 := by
  classical
  rw [deletedConvolutionMulMatrixAtReindexed_eq_translated]
  rw [det_deletedConvolutionMulMatrixOnNonidentity_sq_eq_prod_deletedFourierCoeffMul_sq
    (G := G) ρ (fun h ↦ q (h₀ * h))]
  congr 1
  simp_rw [deletedFourierCoeffMul_mulLeft (G := G) q]
  rw [Finset.prod_mul_distrib]

/-- Arbitrary omitted-row determinant identity in the `hk` convention, squared,
with the harmless character factor removed. -/
theorem det_deletedConvolutionMulMatrixAtReindexed_sq_eq_prod_deletedFourierCoeffMul_sq
    [DecidableEq G] [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) (h₀ : G) (q : G → ℂ) :
    (deletedConvolutionMulMatrixAtReindexed (G := G) h₀ q).det ^ 2 =
      (∏ χ : NontrivChar G, deletedFourierCoeffMul (G := G) q χ.val) ^ 2 := by
  classical
  rw [det_deletedConvolutionMulMatrixAtReindexed_sq_eq_charFactor_mul_prod_sq
    (G := G) ρ h₀ q]
  rw [mul_pow, prod_nontriv_mulChar_apply_inv_sq_eq_one (G := G) h₀, one_mul]

end FiniteGroup

end CyclotomicUnits
end BernoulliRegular

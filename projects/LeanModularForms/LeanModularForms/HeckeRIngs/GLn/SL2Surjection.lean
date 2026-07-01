/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Surjectivity of the reduction map SL₂(ℤ) → SL₂(ℤ/dℤ)

This file proves that the natural reduction map `SL₂(ℤ) → SL₂(ℤ/dℤ)` is surjective
(strong approximation for SL₂). This is a fundamental result in the theory of
congruence subgroups and Hecke operators.

## Main results

* `SL2_reduction_surjective` — the map `SL₂(ℤ) → SL₂(ℤ/dℤ)` is surjective.

## Proof strategy

Given `g = !![a, b; c, d] ∈ SL₂(ℤ/dℤ)` with `a * d - b * c = 1`:

1. **Coprime lifting**: Lift `a, c` to integers `a₁, c₀` with `a₁ ≡ a (mod d)`,
   `c₀ ≡ c (mod d)`, and `gcd(a₁, c₀) = 1`. This uses the stable range property of `ℤ`:
   since `gcd(a₀, c₀, d) = 1` for arbitrary lifts, we can adjust `a₀` by multiples of `d`
   to eliminate common factors with `c₀`.

2. **Bezout completion**: By `IsCoprime.exists_SL2_col`, find `σ ∈ SL₂(ℤ)` whose
   first column is `(a₁, c₀)`.

3. **Upper triangular remainder**: The matrix `map(σ)⁻¹ * g` has first column `(1, 0)`
   by direct computation, so it equals `!![1, t; 0, 1]` for some `t ∈ ℤ/dℤ`.

4. **Lift upper triangular**: `!![1, t; 0, 1]` is the image of `!![1, t'; 0, 1] ∈ SL₂(ℤ)`
   for any integer lift `t'` of `t`.

5. **Combine**: `g = map(σ) * !![1, t; 0, 1] = map(σ * !![1, t'; 0, 1])`.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §1.6
* Serre, *A Course in Arithmetic*, Ch. VII, Lemma 15
-/

open Matrix SpecialLinearGroup

namespace SL2Reduction

private lemma det_upperUniTri {R : Type*} [CommRing R] (t : R) :
    (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) R).det = 1 := by
  simp [det_fin_two_of]

private lemma natAbs_emod_lt (a c : ℤ) (hc : c ≠ 0) : (a % c).natAbs < c.natAbs := by
  have hlt := Int.emod_lt a hc
  have hnonneg := Int.emod_nonneg a hc
  omega

private lemma isCoprime_emod {d : ℕ} [NeZero d] {a₁ c₁ : ℤ}
    (hac : IsCoprime (a₁ : ZMod d) (c₁ : ZMod d)) :
    IsCoprime (c₁ : ZMod d) ((a₁ % c₁ : ℤ) : ZMod d) := by
  rw [show (a₁ % c₁ : ℤ) = a₁ + c₁ * (-(a₁ / c₁)) from by rw [Int.emod_def]; ring]
  push_cast
  exact hac.symm.add_mul_left_right _

/-- Coprime elements of `ZMod d` lift to coprime integers. -/
theorem IsCoprime.lift_to_int {d : ℕ} [NeZero d] {a c : ZMod d} (hac : IsCoprime a c) :
    ∃ a₀ c₀ : ℤ, (a₀ : ZMod d) = a ∧ (c₀ : ZMod d) = c ∧ IsCoprime a₀ c₀ := by
  obtain ⟨a₁, rfl⟩ := ZMod.intCast_surjective a
  obtain ⟨c₁, rfl⟩ := ZMod.intCast_surjective c
  suffices h : ∀ n, ∀ a₁ c₁ : ℤ, c₁.natAbs ≤ n →
      IsCoprime (a₁ : ZMod d) (c₁ : ZMod d) →
      ∃ a₀ c₀ : ℤ, (a₀ : ZMod d) = a₁ ∧ (c₀ : ZMod d) = c₁ ∧ IsCoprime a₀ c₀ from
    h c₁.natAbs a₁ c₁ le_rfl hac
  have zero_case : ∀ a₁ : ℤ, IsCoprime (a₁ : ZMod d) 0 →
      ∃ a₀ c₀ : ℤ,
        (a₀ : ZMod d) = a₁ ∧ (c₀ : ZMod d) = 0 ∧ IsCoprime a₀ c₀ := by
    intro a₁ hac
    have hunit : IsUnit (a₁ : ZMod d) := by rwa [isCoprime_zero_right] at hac
    rw [ZMod.coe_int_isUnit_iff_isCoprime] at hunit
    exact ⟨a₁, d, rfl, by simp, hunit.symm⟩
  intro n
  induction n with
  | zero =>
    intro a₁ c₁ hle hac
    have hc₁ : c₁ = 0 := by omega
    subst hc₁
    simpa using zero_case a₁ (by simpa using hac)
  | succ n ih =>
    intro a₁ c₁ hle hac
    by_cases hc₁ : c₁ = 0
    · subst hc₁; simpa using zero_case a₁ (by simpa using hac)
    obtain ⟨c₀, r₀, hc₀, hr₀, hcop⟩ := ih c₁ (a₁ % c₁)
      (Nat.lt_succ_iff.mp ((natAbs_emod_lt a₁ c₁ hc₁).trans_le hle)) (isCoprime_emod hac)
    refine ⟨r₀ + a₁ / c₁ * c₀, c₀, ?_, hc₀, hcop.symm.add_mul_right_left _⟩
    conv_rhs => rw [← Int.emod_add_ediv_mul a₁ c₁]
    push_cast
    rw [hr₀, hc₀]

/-- The first column of an SL₂ matrix is coprime (from the determinant condition). -/
theorem isCoprime_of_det_eq_one {R : Type*} [CommRing R]
    {a b c d : R} (h : a * d - b * c = 1) : IsCoprime a c :=
  ⟨d, -b, by linear_combination h⟩

/-- An SL₂ element with first column `(1, 0)` is upper unitriangular. -/
theorem SL2_eq_upperUniTri {R : Type*} [CommRing R] (h : SpecialLinearGroup (Fin 2) R)
    (h00 : h 0 0 = 1) (h10 : h 1 0 = 0) :
    h = ⟨!![1, h 0 1; 0, 1], det_upperUniTri _⟩ := by
  ext i j
  induction h using fin_two_induction with
  | _ a b c dd hdet =>
    simp at h00 h10
    subst h00; subst h10
    fin_cases i <;> fin_cases j <;> simp
    linear_combination hdet

/-- An upper unitriangular matrix in SL₂(ℤ/dℤ) is in the range of the reduction map. -/
theorem upperUniTri_mem_range (d : ℕ) [NeZero d] (t : ZMod d) :
    ∃ σ : SpecialLinearGroup (Fin 2) ℤ,
      SpecialLinearGroup.map (Int.castRingHom (ZMod d)) σ =
      (⟨!![1, t; 0, 1], det_upperUniTri _⟩ :
        SpecialLinearGroup (Fin 2) (ZMod d)) := by
  obtain ⟨t₀, rfl⟩ := ZMod.intCast_surjective t
  refine ⟨⟨!![1, t₀; 0, 1], det_upperUniTri _⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- If two SL₂ elements share the same first column, their quotient has
`(1, 0)` entry equal to `0`. -/
theorem inv_mul_10_eq_zero {R : Type*} [CommRing R] (M g : SpecialLinearGroup (Fin 2) R)
    (h0 : M 0 0 = g 0 0) (h1 : M 1 0 = g 1 0) : (M⁻¹ * g) 1 0 = 0 := by
  induction M using fin_two_induction with
  | _ a₁ b₁ c₁ d₁ hdet₁ =>
  induction g using fin_two_induction with
  | _ a₂ b₂ c₂ d₂ hdet₂ =>
    simp at h0 h1
    subst h0; subst h1
    simp [coe_inv, adjugate_fin_two, mul_apply, Fin.sum_univ_two, of_apply]
    ring

/-- If two SL₂ elements share the same first column, their quotient has
`(0, 0)` entry equal to `1`. -/
theorem inv_mul_00_eq_one {R : Type*} [CommRing R] (M g : SpecialLinearGroup (Fin 2) R)
    (h0 : M 0 0 = g 0 0) (h1 : M 1 0 = g 1 0) : (M⁻¹ * g) 0 0 = 1 := by
  induction M using fin_two_induction with
  | _ a₁ b₁ c₁ d₁ hdet₁ =>
  induction g using fin_two_induction with
  | _ a₂ b₂ c₂ d₂ hdet₂ =>
    simp at h0 h1
    subst h0; subst h1
    simp [coe_inv, adjugate_fin_two, mul_apply, Fin.sum_univ_two, of_apply]
    linear_combination hdet₁

/-- The reduction map `SL₂(ℤ) → SL₂(ℤ/dℤ)` is surjective. -/
theorem SL2_reduction_surjective (d : ℕ) [NeZero d] :
    Function.Surjective (SpecialLinearGroup.map (Int.castRingHom (ZMod d)) :
      SpecialLinearGroup (Fin 2) ℤ →* SpecialLinearGroup (Fin 2) (ZMod d)) := by
  intro g
  induction g using fin_two_induction with
  | _ a b c dd hdet =>
    obtain ⟨a₀, c₀, ha₀, hc₀, hcop⟩ :=
      IsCoprime.lift_to_int (isCoprime_of_det_eq_one hdet)
    obtain ⟨σ, hσ0, hσ1⟩ := hcop.exists_SL2_col (0 : Fin 2)
    set M := SpecialLinearGroup.map (Int.castRingHom (ZMod d)) σ
    have hdet' : (!![a, b; c, dd] : Matrix (Fin 2) (Fin 2) (ZMod d)).det = 1 := by
      rw [det_fin_two_of]; exact hdet
    set g₀ : SpecialLinearGroup (Fin 2) (ZMod d) := ⟨!![a, b; c, dd], hdet'⟩
    have hcol0 : M 0 0 = g₀ 0 0 := by
      simp [M, g₀, map_apply_coe, RingHom.mapMatrix_apply, map_apply, hσ0, ha₀]
    have hcol1 : M 1 0 = g₀ 1 0 := by
      simp [M, g₀, map_apply_coe, RingHom.mapMatrix_apply, map_apply, hσ1, hc₀,
        cons_val_one]
    set t := (M⁻¹ * g₀) 0 1
    have hQ : M⁻¹ * g₀ = ⟨!![1, t; 0, 1], det_upperUniTri _⟩ :=
      SL2_eq_upperUniTri _ (inv_mul_00_eq_one M g₀ hcol0 hcol1)
        (inv_mul_10_eq_zero M g₀ hcol0 hcol1)
    obtain ⟨τ, hτ⟩ := upperUniTri_mem_range d t
    refine ⟨σ * τ, ?_⟩
    rw [map_mul, show g₀ = M * (M⁻¹ * g₀) by group, hQ, ← hτ]

end SL2Reduction

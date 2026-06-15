/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeActionGeneral
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p

/-!
# Adjugated `T_p` representatives lie in distinct `SL₂(ℤ)`-cosets

The adjugates of the standard `T_p` coset representatives `T_p_upper(b)`, `T_p_lower`
(from `HeckeT_p.lean`) represent pairwise distinct right `SL₂(ℤ)`-cosets: each pairwise
quotient has a non-integral entry (`(b₁−b₂)/p` or `1/p`).  These disjointness lemmas feed
the injectivity of the index bijections (`twistedTpPsi_injective`) used to match the
abstract χ-twisted Hecke slash with the explicit `T_p` coset sum.

## Main results

* `adj_upper_inv_mul_upper_not_mem_H` — for distinct `b₁, b₂ < p`,
  `adj(T_p_upper(b₁))⁻¹ · adj(T_p_upper(b₂)) ∉ SL₂(ℤ)`.
* `adj_upper_inv_mul_lower_not_mem_H` / `adj_lower_inv_mul_upper_not_mem_H` — the
  mixed upper/lower quotients are likewise not in `SL₂(ℤ)`.

## References

* Diamond-Shurman, *A First Course in Modular Forms*, §5.2
* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4
-/

open Matrix Subgroup.Commensurable Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2

private lemma SLnZ_entry_is_int (g : GL (Fin 2) ℚ) (hg : g ∈ SLnZ_subgroup 2) (i j : Fin 2) :
    ∃ n : ℤ, g.val i j = (n : ℚ) :=
  let ⟨s, hs⟩ := hg
  ⟨s.val i j, by simp [← hs, mapGL_coe_matrix, algebraMap_int_eq]⟩

/-- `adj(T_p_upper(b₁))⁻¹ · adj(T_p_upper(b₂)) ∉ SL₂(ℤ)` for distinct
`b₁, b₂ < p`. The product has `(0,1)`-entry `(b₁ - b₂)/p ∉ ℤ`. -/
lemma adj_upper_inv_mul_upper_not_mem_H (p : ℕ) (hp : Nat.Prime p) (b₁ b₂ : ℕ) (hb₁ : b₁ < p)
    (hb₂ : b₂ < p) (hne : b₁ ≠ b₂) :
    (GL_adjugate (T_p_upper p hp.pos b₁ : GL (Fin 2) ℚ))⁻¹ *
     GL_adjugate (T_p_upper p hp.pos b₂ : GL (Fin 2) ℚ) ∉ (GL_pair 2).H := by
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h_eq : (GL_adjugate (T_p_upper p hp.pos b₁))⁻¹ * GL_adjugate (T_p_upper p hp.pos b₂) =
      GeneralLinearGroup.mkOfDetNeZero !![(1 : ℚ), ((b₁ - b₂ : ℤ) : ℚ) / p; 0, 1]
        (by simp) := by
    rw [inv_mul_eq_iff_eq_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, hp_ne, mul_div_cancel₀]
    ring
  intro hmem
  obtain ⟨n, hn⟩ := SLnZ_entry_is_int _ (h_eq ▸ hmem) 0 1
  simp at hn
  have h_int : (b₁ : ℤ) - b₂ = n * p := by exact_mod_cast (div_eq_iff hp_ne).mp hn
  have h_dvd : (p : ℤ) ∣ (b₁ : ℤ) - b₂ := ⟨n, by lia⟩
  have h0 : (b₁ : ℤ) - b₂ = 0 :=
    Int.eq_zero_of_abs_lt_dvd h_dvd (abs_sub_lt_iff.mpr ⟨by lia, by lia⟩)
  lia

/-- `adj(T_p_upper(b))⁻¹ · adj(T_p_lower) ∉ SL₂(ℤ)`.
The product has `(0,0)`-entry `1/p ∉ ℤ`. -/
lemma adj_upper_inv_mul_lower_not_mem_H (p : ℕ) (hp : Nat.Prime p) (b : ℕ) :
    (GL_adjugate (T_p_upper p hp.pos b : GL (Fin 2) ℚ))⁻¹ *
     GL_adjugate (T_p_lower p hp.pos : GL (Fin 2) ℚ) ∉ (GL_pair 2).H := by
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h_eq : (GL_adjugate (T_p_upper p hp.pos b))⁻¹ * GL_adjugate (T_p_lower p hp.pos) =
      GeneralLinearGroup.mkOfDetNeZero !![1 / (p : ℚ), (b : ℚ); 0, p] (by simp [hp_ne]) := by
    rw [inv_mul_eq_iff_eq_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, hp_ne]
    ring
  intro hmem
  obtain ⟨n, hn⟩ := SLnZ_entry_is_int _ (h_eq ▸ hmem) 0 0
  simp at hn
  exact hp.ne_one <| by simpa [Rat.inv_natCast_den_of_pos hp.pos] using congrArg Rat.den hn

/-- `adj(T_p_lower)⁻¹ · adj(T_p_upper(b)) ∉ SL₂(ℤ)`.
The product has `(1,1)`-entry `1/p ∉ ℤ`. -/
lemma adj_lower_inv_mul_upper_not_mem_H (p : ℕ) (hp : Nat.Prime p) (b : ℕ) :
    (GL_adjugate (T_p_lower p hp.pos : GL (Fin 2) ℚ))⁻¹ *
     GL_adjugate (T_p_upper p hp.pos b : GL (Fin 2) ℚ) ∉ (GL_pair 2).H := fun hmem ↦
  adj_upper_inv_mul_lower_not_mem_H p hp b <| by simpa using inv_mem hmem

end HeckeRing.GL2

/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.CosetDecomposition
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Degree
import LeanModularForms.HeckeRIngs.GL2.CongruenceIndex

/-!
# Degree Formulas for GL_n Hecke Ring

Degree formulas for the diagonal Hecke operators `T(a₁,...,aₙ)`, including Gaussian binomial
coefficients for the prime-power case.

## Main definitions

* `gaussianBinom q n k` : the Gaussian binomial coefficient `[n choose k]_q`

## Main results

* `upperTriRep_card_le_HeckeCoset_deg` : `∏_{i<j} (a_j / a_i) ≤ deg(T(a₁,...,aₙ))`

## Important note on degree formulas

The degree of `T(a₁,...,aₙ)` is **not** simply `∏_{i<j} (aⱼ/aᵢ)`. The upper-triangular
representatives with fixed diagonal `(a₁,...,aₙ)` account for
`∏_{i<j}(aⱼ/aᵢ)` left cosets,
but the double coset also contains representatives with permuted diagonals (those whose
Hermite Normal Form has a different diagonal but the same Smith Normal Form).

**Counterexample:** For `n = 2`, `a = (1, p)` with `p` prime, the `UpperTriRep` count is `p`,
but the actual degree is `p + 1`. The additional representative is `[[p,0],[0,1]]`, which lies
in the double coset `SL₂(ℤ) · diag(1,p) · SL₂(ℤ)` but has a different diagonal.

**Correct formula for n = 2:** `deg(T(a₁,a₂)) = ψ(a₂/a₁)` where `ψ` is the Dedekind psi
function `ψ(d) = d · ∏_{p | d} (1 + 1/p)`. For the prime-power case needed for Theorem 3.24:
`deg(T(pⁱ, pⁱ⁺ᵏ)) = pᵏ⁻¹(p + 1)` for `k ≥ 1`.

## References

* Shimura, Proposition 3.14, 3.18, Theorem 3.24
-/

open HeckeRing HeckeRing.GL2 Finset CongruenceSubgroup Matrix.SpecialLinearGroup Matrix
  ModularGroup
open scoped Pointwise MatrixGroups

namespace HeckeRing.GLn

private lemma conjAct_smul_eq_of_mem {G : Type*} [Group G] (H : Subgroup G)
    {h : G} (hh : h ∈ H) : ConjAct.toConjAct h • H = H :=
  Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hh)

variable (n : ℕ)

private lemma mapGL_injective : Function.Injective (mapGL ℚ : SL(n, ℤ) →* GL (Fin n) ℚ) := by
  intro x y hxy; ext i j
  have h := congr_arg (fun g ↦ (Units.val g) i j) hxy
  simp only [mapGL_coe_matrix, map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] at h; exact_mod_cast h

variable [NeZero n]

private lemma a1_eq_a0_mul_pk {p : ℕ} {a : Fin 2 → ℕ} {k : ℕ}
    (h_ratio : a 1 / a 0 = p ^ k) (h_dvd_a : a 0 ∣ a 1) :
    (a 1 : ℚ) = (a 0 : ℚ) * (↑(p ^ k) : ℚ) := by
  have h1 := Nat.div_mul_cancel h_dvd_a
  rw [h_ratio] at h1
  push_cast [← h1]; ring

private lemma conj_diagMat_mem_of_Gamma0 (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i) (k : ℕ)
    (h_ratio : a 1 / a 0 = p ^ k) (h_dvd_a : a 0 ∣ a 1) (σ : SL(2, ℤ))
    (hσ : (↑(p ^ k) : ℤ) ∣ σ.1 1 0) :
    (diagMat 2 a)⁻¹ * (σ : GL (Fin 2) ℚ) * diagMat 2 a ∈ SLnZ_subgroup 2 := by
  obtain ⟨c, hc⟩ := hσ
  let τ_mat : Matrix (Fin 2) (Fin 2) ℤ :=
    !![σ.1 0 0, ↑(p ^ k) * σ.1 0 1; c, σ.1 1 1]
  have h_det : τ_mat.det = 1 := by
    simp only [τ_mat, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have hσ_det := σ.prop; simp only [Matrix.det_fin_two] at hσ_det
    rw [hc] at hσ_det; linarith
  let τ : SL(2, ℤ) := ⟨τ_mat, h_det⟩
  rw [MonoidHom.mem_range]
  refine ⟨τ, ?_⟩
  have ha1 := a1_eq_a0_mul_pk h_ratio h_dvd_a
  have hcQ : (σ.1 1 0 : ℚ) = (↑(p ^ k) : ℚ) * (c : ℚ) := by exact_mod_cast hc
  push_cast at ha1 hcQ
  suffices h : diagMat 2 a * (τ : GL (Fin 2) ℚ) = (σ : GL (Fin 2) ℚ) * diagMat 2 a by
    have h' := congr_arg ((diagMat 2 a)⁻¹ * ·) h
    simp only [← mul_assoc, inv_mul_cancel, one_mul] at h'; exact h'
  apply Units.ext
  have hval : ∀ μ : SL(2, ℤ), (↑(mapGL ℚ μ) : Matrix _ _ ℚ) = μ.val.map (Int.cast) :=
    fun μ ↦ by simp [mapGL_coe_matrix, algebraMap_int_eq, RingHom.mapMatrix_apply]
  simp only [Units.val_mul, hval]
  ext i j
  simp only [diagMat_val 2 a ha, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [τ, τ_mat, Matrix.of_apply, Matrix.cons_val', Fin.isValue] <;>
    push_cast <;> (try rw [hcQ]) <;> (try rw [ha1]) <;> ring

private lemma Gamma0_of_conj_diagMat_mem (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i) (k : ℕ)
    (h_ratio : a 1 / a 0 = p ^ k) (h_dvd_a : a 0 ∣ a 1) (σ : SL(2, ℤ))
    (hmem : (diagMat 2 a)⁻¹ * (σ : GL (Fin 2) ℚ) * diagMat 2 a ∈ SLnZ_subgroup 2) :
    (↑(p ^ k) : ℤ) ∣ σ.1 1 0 := by
  rw [MonoidHom.mem_range] at hmem
  obtain ⟨τ, hτ⟩ := hmem
  have ha1 := a1_eq_a0_mul_pk h_ratio h_dvd_a
  have ha0_ne : (a 0 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ha 0).ne'
  have h_mul : diagMat 2 a * (τ : GL (Fin 2) ℚ) = (σ : GL (Fin 2) ℚ) * diagMat 2 a := by
    have := congr_arg (diagMat 2 a * ·) hτ
    simp only [← mul_assoc, mul_inv_cancel, one_mul] at this; exact this
  have h_entry : (a 1 : ℚ) * (τ.1 1 0 : ℚ) = (σ.1 1 0 : ℚ) * (a 0 : ℚ) := by
    have h10 := Units.ext_iff.mp h_mul
    have := congr_arg (fun M ↦ M 1 0) h10
    simpa only [Units.val_mul, mapGL_coe_matrix, map_apply_coe, RingHom.mapMatrix_apply,
      diagMat_val 2 a ha, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.map_apply, algebraMap_int_eq, eq_intCast] using this
  have h_σ₁₀ : (σ.1 1 0 : ℚ) = ↑(p ^ k) * (τ.1 1 0 : ℚ) := by
    rw [ha1] at h_entry; field_simp at h_entry ⊢; linarith
  exact ⟨τ.1 1 0, by exact_mod_cast h_σ₁₀⟩

private lemma conjDiag_relIndex_eq_Gamma0_index (p : ℕ) (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i)
    (k : ℕ) (h_ratio : a 1 / a 0 = p ^ k) (h_dvd_a : a 0 ∣ a 1) :
    (ConjAct.toConjAct (diagMat 2 a) • SLnZ_subgroup 2).relIndex (SLnZ_subgroup 2) =
    (Gamma0 (p ^ k)).index := by
  set H := SLnZ_subgroup 2
  set α := diagMat 2 a
  set f := (mapGL ℚ : SL(2, ℤ) →* GL (Fin 2) ℚ)
  have h_inj : Function.Injective f := mapGL_injective 2
  have h_H_eq : H = Subgroup.map f ⊤ := MonoidHom.range_eq_map f
  have h_gamma0_iff : ∀ σ : SL(2, ℤ),
      σ ∈ Gamma0 (p ^ k) ↔ α⁻¹ * f σ * α ∈ H := by
    intro σ
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨conj_diagMat_mem_of_Gamma0 a ha k h_ratio h_dvd_a σ,
           Gamma0_of_conj_diagMat_mem a ha k h_ratio h_dvd_a σ⟩
  have h_inf_eq : (ConjAct.toConjAct α • H) ⊓ H = Subgroup.map f (Gamma0 (p ^ k)) := by
    ext g; simp only [Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨h_smul, h_mem⟩
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
        ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at h_smul
      obtain ⟨σ, rfl⟩ := h_mem
      exact ⟨σ, (h_gamma0_iff σ).mpr h_smul, rfl⟩
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨?_, ⟨σ, rfl⟩⟩
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
        ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
      exact (h_gamma0_iff σ).mp hσ
  calc (ConjAct.toConjAct α • H).relIndex H
      = ((ConjAct.toConjAct α • H) ⊓ H).relIndex H :=
          (Subgroup.inf_relIndex_right _ _).symm
    _ = (Subgroup.map f (Gamma0 (p ^ k))).relIndex (Subgroup.map f ⊤) := by
          rw [h_inf_eq, h_H_eq]
    _ = (Gamma0 (p ^ k)).relIndex ⊤ :=
          Subgroup.relIndex_map_map_of_injective _ _ h_inj
    _ = (Gamma0 (p ^ k)).index := (Gamma0 (p ^ k)).relIndex_top_right

/-- For `n = 2` and prime `p`: `deg(T(p^i, p^(i+k))) = p^(k-1) * (p + 1)` for `k >= 1`. -/
theorem HeckeCoset_deg_T_diag_two_prime (p : ℕ) (hp : Nat.Prime p) (a : Fin 2 → ℕ)
    (ha : ∀ i, 0 < a i) (hdiv : DivChain 2 a) (k : ℕ) (hk : 0 < k)
    (h_ratio : a 1 / a 0 = p ^ k) :
    HeckeCoset_deg (GL_pair 2) (T_diag a) = ↑(p ^ (k - 1) * (p + 1)) := by
  set D := T_diag a
  set δ := (HeckeCoset.rep D : GL (Fin 2) ℚ)
  set α := (diagMat 2 a : GL (Fin 2) ℚ) with hα_def
  set H := (GL_pair 2).H
  have h_dvd_a : a 0 ∣ a 1 := hdiv 0 (by lia)
  have h_in_set : δ ∈ HeckeCoset.toSet D := HeckeCoset.rep_mem D
  have h_D_set : HeckeCoset.toSet D = DoubleCoset.doubleCoset α ↑H ↑H := by
    simp only [D, T_diag, HeckeCoset.toSet_mk, hα_def]; congr 1; exact diagMat_delta_val 2 a ha
  rw [h_D_set, DoubleCoset.mem_doubleCoset] at h_in_set
  obtain ⟨σ₁, hσ₁, σ₂, hσ₂, hδ_eq⟩ := h_in_set
  have h_smul_σ₁ : ConjAct.toConjAct σ₁ • H = H := conjAct_smul_eq_of_mem H hσ₁
  have h_δ_smul : ConjAct.toConjAct δ • H =
      ConjAct.toConjAct σ₁ • (ConjAct.toConjAct α • H) := by
    rw [hδ_eq, map_mul, map_mul, ← smul_smul, ← smul_smul, conjAct_smul_eq_of_mem H hσ₂]
  have h_S1 : (ConjAct.toConjAct α • H).relIndex H =
      (ConjAct.toConjAct δ • H).relIndex H := by
    rw [h_δ_smul]
    have := Subgroup.relIndex_pointwise_smul
      (ConjAct.toConjAct σ₁) (ConjAct.toConjAct α • H) H
    rw [h_smul_σ₁] at this; exact this.symm
  have h_def : HeckeCoset_deg (GL_pair 2) D =
      ↑((ConjAct.toConjAct δ • H).relIndex H) := by
    simp only [HeckeCoset_deg]; rw [← Nat.card_eq_fintype_card]; rfl
  have h_Gamma0 : (ConjAct.toConjAct α • H).relIndex H =
      (Gamma0 (p ^ k)).index := conjDiag_relIndex_eq_Gamma0_index p a ha k h_ratio h_dvd_a
  rw [h_def, show (ConjAct.toConjAct δ • H).relIndex H =
      (ConjAct.toConjAct α • H).relIndex H from h_S1.symm,
    h_Gamma0, Gamma0_prime_power_index p hp k hk]

private lemma diagMat_comm_of_const (a : Fin n → ℕ) (ha : ∀ i, 0 < a i)
    (h_const : ∀ i, a i = a 0) (g : GL (Fin n) ℚ) :
    diagMat n a * g = g * diagMat n a := by
  apply Units.ext
  simp only [Units.val_mul, diagMat_val n a ha]
  have h_diag : Matrix.diagonal (fun i ↦ (a i : ℚ)) =
      (a 0 : ℚ) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs with h
    · subst h; simp [h_const]
    · simp
  rw [h_diag, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]

/-- For `n = 2`, scalar case: `deg(T(c, c)) = 1`. -/
theorem HeckeCoset_deg_T_diag_two_scalar (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i)
    (_hdiv : DivChain 2 a) (h_eq : a 0 = a 1) : HeckeCoset_deg (GL_pair 2) (T_diag a) = 1 := by
  have h_const : ∀ i, a i = a 0 := fun i ↦ by fin_cases i <;> simp [h_eq]
  set D := T_diag a
  set δ := HeckeCoset.rep D
  set H := (GL_pair 2).H
  suffices hsmul : ConjAct.toConjAct (δ : GL (Fin 2) ℚ) • H = H by
    have h_def : HeckeCoset_deg (GL_pair 2) D =
        ↑((ConjAct.toConjAct (δ : GL (Fin 2) ℚ) • H).relIndex H) := by
      simp only [HeckeCoset_deg, Subgroup.relIndex, Subgroup.index,
        ← Nat.card_eq_fintype_card]; rfl
    rw [h_def, hsmul, Subgroup.relIndex_self]; simp
  have hδ_mem : (δ : GL (Fin 2) ℚ) ∈
      DoubleCoset.doubleCoset (↑(diagMat_delta 2 a)) H H := by
    rw [show DoubleCoset.doubleCoset (↑(diagMat_delta 2 a)) H H = HeckeCoset.toSet D from by
      simp only [D, H, T_diag, HeckeCoset.toSet_mk]]
    exact HeckeCoset.rep_mem D
  rw [DoubleCoset.mem_doubleCoset] at hδ_mem; obtain ⟨h₁, hh₁, h₂, hh₂, hδ_eq⟩ := hδ_mem
  have h_comm : diagMat 2 a * h₂ = h₂ * diagMat 2 a :=
    diagMat_comm_of_const 2 a ha h_const h₂
  have hδ_simp : (δ : GL (Fin 2) ℚ) = (h₁ * h₂) * diagMat 2 a := by
    rw [hδ_eq, show (↑(diagMat_delta 2 a) : GL (Fin 2) ℚ) =
        diagMat 2 a from diagMat_delta_val 2 a ha, mul_assoc]
    rw [h_comm, ← mul_assoc]
  have h_diag_conj : ∀ (g : GL (Fin 2) ℚ),
      (diagMat 2 a)⁻¹ * g * diagMat 2 a = g := by
    intro g; rw [mul_assoc, ← diagMat_comm_of_const 2 a ha h_const g, ← mul_assoc,
      inv_mul_cancel, one_mul]
  rw [hδ_simp, map_mul, ← smul_smul]
  have h_smul_diag : ConjAct.toConjAct (diagMat 2 a) • H = H := by
    ext x
    simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
      map_inv, ConjAct.ofConjAct_toConjAct, inv_inv, h_diag_conj]
  rw [h_smul_diag]
  exact conjAct_smul_eq_of_mem H (H.mul_mem hh₁ hh₂)

end HeckeRing.GLn

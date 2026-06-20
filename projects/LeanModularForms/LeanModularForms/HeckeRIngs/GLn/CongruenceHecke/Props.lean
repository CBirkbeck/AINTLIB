/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.CongruenceHecke.Foundation

/-!
# Hecke Ring for Congruence Subgroups (Shimura §3.3) — Propositions 3.30–3.33

The coset map `HeckeCoset (Γ₀(N)) → HeckeCoset (Γ)` and the additive
homomorphism `R(Γ₀(N), Δ₀(N)) → R(Γ, Δ)` (Shimura Prop 3.30), its injectivity
on coprime-determinant cosets (Prop 3.31), the `N`-power determinant structure
(Prop 3.33), and the bad-prime degree/multiplication lemmas (`T_bad_mul`).

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.3
-/

open Matrix Subgroup.Commensurable Pointwise Matrix.SpecialLinearGroup

open scoped Pointwise MatrixGroups

namespace HeckeRing.GLn

/-- The inclusion `Δ₀(N) ↪ Δ` as a submonoid inclusion. -/
noncomputable def Delta0_inclusion (N : ℕ) [NeZero N] :
    (Gamma0_pair N).Δ → (GL_pair 2).Δ :=
  fun g ↦ ⟨g.1, Delta0_le_posDetInt N g.2⟩

private lemma doubleCoset_eq_of_Gamma0_eq (N : ℕ) [NeZero N]
    (a b : (Gamma0_pair N).Δ)
    (hab : dcRel (Gamma0_pair N) a b) :
    dcRel (GL_pair 2) (Delta0_inclusion N a) (Delta0_inclusion N b) := by
  simp only [dcRel] at hab ⊢
  have hb_mem : (b : GL (Fin 2) ℚ) ∈ DoubleCoset.doubleCoset (a : GL (Fin 2) ℚ)
      ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
    rw [hab]; exact DoubleCoset.mem_doubleCoset_self _ _ _
  rw [DoubleCoset.mem_doubleCoset] at hb_mem
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hb_eq⟩ := hb_mem
  exact (DoubleCoset.doubleCoset_eq_of_mem (DoubleCoset.mem_doubleCoset.mpr
    ⟨γ₁, Gamma0_le_SLnZ N hγ₁, γ₂, Gamma0_le_SLnZ N hγ₂, hb_eq⟩)).symm

/-- The coset map `HeckeCoset (Gamma0_pair N) → HeckeCoset (GL_pair 2)`:
    sends `Γ₀(N)αΓ₀(N)` to `ΓαΓ`. -/
noncomputable def cosetMap (N : ℕ) [NeZero N] :
    HeckeCoset (Gamma0_pair N) → HeckeCoset (GL_pair 2) :=
  Quotient.lift
    (fun g ↦ ⟦Delta0_inclusion N g⟧)
    (fun a b hab ↦ by
      show ⟦Delta0_inclusion N a⟧ = ⟦Delta0_inclusion N b⟧
      rw [HeckeCoset.eq_iff]
      exact doubleCoset_eq_of_Gamma0_eq N a b hab)

/-- An element `g ∈ Δ₀(N)` has **coprime determinant** if `gcd(det(A), N) = 1`
    where `A` is the integer matrix representing `g`. -/
def CoprimeDet (N : ℕ) [NeZero N] (g : (Gamma0_pair N).Δ) : Prop :=
  ∀ A : Matrix (Fin 2) (Fin 2) ℤ,
    (↑(g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      A.map (Int.cast : ℤ → ℚ) →
    Int.gcd A.det N = 1

/-- **Shimura Proposition 3.31 (Injectivity of `cosetMap`)**: The coset map
    `Γ₀(N)αΓ₀(N) ↦ ΓαΓ` is injective on double cosets with coprime determinant. -/
theorem shimura_prop_3_31 (N : ℕ) [NeZero N]
    (a b : (Gamma0_pair N).Δ)
    (ha : CoprimeDet N a) (hb : CoprimeDet N b)
    (h : cosetMap N ⟦a⟧ = cosetMap N ⟦b⟧) :
    (⟦a⟧ : HeckeCoset (Gamma0_pair N)) = ⟦b⟧ := by
  change (⟦Delta0_inclusion N a⟧ : HeckeCoset (GL_pair 2)) =
    ⟦Delta0_inclusion N b⟧ at h
  rw [HeckeCoset.eq_iff] at h
  rw [HeckeCoset.eq_iff]
  obtain ⟨_, _, Aa, hAa, hAaN, _⟩ := a.2
  obtain ⟨_, _, Ab, hAb, hAbN, _⟩ := b.2
  have eq_a := doubleCoset_eq_of_Gamma0_coprimeDet N a.1 a.2 Aa hAa hAaN (ha Aa hAa)
  have eq_b := doubleCoset_eq_of_Gamma0_coprimeDet N b.1 b.2 Ab hAb hAbN (hb Ab hAb)
  have h' : DoubleCoset.doubleCoset (↑a : GL (Fin 2) ℚ) (SLnZ_subgroup 2)
      (SLnZ_subgroup 2) =
    DoubleCoset.doubleCoset (↑b : GL (Fin 2) ℚ) (SLnZ_subgroup 2)
      (SLnZ_subgroup 2) := h
  have h_inter : DoubleCoset.doubleCoset (↑a : GL (Fin 2) ℚ) (SLnZ_subgroup 2)
      (SLnZ_subgroup 2) ∩ ↑(Delta0_submonoid N) =
    DoubleCoset.doubleCoset (↑b : GL (Fin 2) ℚ) (SLnZ_subgroup 2)
      (SLnZ_subgroup 2) ∩ ↑(Delta0_submonoid N) := by rw [h']
  rwa [eq_a, eq_b] at h_inter

private instance instCountableM2 : Countable (Matrix (Fin 2) (Fin 2) ℚ) :=
  show Countable (Fin 2 → Fin 2 → ℚ) from inferInstance

private noncomputable instance instCountableGL2 : Countable (GL (Fin 2) ℚ) := by
  apply Function.Injective.countable
    (f := fun g : GL (Fin 2) ℚ ↦
      ((g : Matrix (Fin 2) (Fin 2) ℚ), (g⁻¹ : Matrix (Fin 2) (Fin 2) ℚ)))
  intro g₁ g₂ h; exact Units.ext (Prod.mk.inj h).1

private lemma divChain_one_succ (k : ℕ) : DivChain 2 (![1, k + 1]) := by
  intro i hi
  obtain rfl : i = 0 := by omega
  simp

private noncomputable instance instInfiniteGLCoset : Infinite (HeckeCoset (GL_pair 2)) :=
  Infinite.of_injective (fun n : ℕ ↦ T_diag (![1, n + 1]))
    (fun m n h ↦ by
      have hpos : ∀ k : ℕ, ∀ i, 0 < (![1, k + 1]) i :=
        fun k i ↦ by fin_cases i <;> simp
      have := diagonal_representative_unique 2 _ _ (hpos m) (hpos n)
        (divChain_one_succ m) (divChain_one_succ n) h
      have h1 := congr_fun this 1
      simp [Matrix.cons_val_one] at h1
      omega)

private lemma diagMat_one_mem_Delta0 (N : ℕ) (n : ℕ) :
    diagMat 2 (![1, n + 1]) ∈ Delta0_submonoid N := by
  refine ⟨diagMat_hasIntEntries 2 _ (fun i ↦ by fin_cases i <;> simp),
    diagMat_det_pos 2 _ (fun i ↦ by fin_cases i <;> simp),
    Matrix.diagonal (fun i ↦ (![1, n + 1] i : ℤ)), ?_, ?_, ?_⟩
  · ext i j; simp [diagMat, Matrix.diagonal, Matrix.map_apply]
  · simp [Matrix.diagonal]
  · simp [Matrix.diagonal]

private noncomputable instance instInfiniteGamma0Coset (N : ℕ) [NeZero N] :
    Infinite (HeckeCoset (Gamma0_pair N)) :=
  Infinite.of_injective
    (fun n : ℕ ↦ (⟦⟨diagMat 2 (![1, n + 1]), diagMat_one_mem_Delta0 N n⟩⟧ :
      HeckeCoset (Gamma0_pair N)))
    (fun m n h ↦ by
      change (⟦⟨diagMat 2 (![1, m + 1]), diagMat_one_mem_Delta0 N m⟩⟧ :
        HeckeCoset (Gamma0_pair N)) = ⟦⟨diagMat 2 (![1, n + 1]), diagMat_one_mem_Delta0 N n⟩⟧ at h
      rw [HeckeCoset.eq_iff] at h
      have h_gl : DoubleCoset.doubleCoset (diagMat 2 (![1, m + 1]) : GL (Fin 2) ℚ)
          (SLnZ_subgroup 2 : Set _) (SLnZ_subgroup 2 : Set _) =
        DoubleCoset.doubleCoset (diagMat 2 (![1, n + 1]) : GL (Fin 2) ℚ)
          (SLnZ_subgroup 2 : Set _) (SLnZ_subgroup 2 : Set _) := by
        have h_mem_dc : (diagMat 2 (![1, n + 1]) : GL (Fin 2) ℚ) ∈
            DoubleCoset.doubleCoset (diagMat 2 (![1, m + 1]) : GL (Fin 2) ℚ)
              ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
          rw [h]; exact DoubleCoset.mem_doubleCoset_self _ _ _
        exact (DoubleCoset.doubleCoset_eq_of_mem
          (Gamma0_doubleCoset_subset_Gamma N _ h_mem_dc)).symm
      have h_T : T_diag (![1, m + 1]) = T_diag (![1, n + 1]) := by
        rw [T_diag, T_diag]
        show (⟦diagMat_delta 2 (![1, m + 1])⟧ : HeckeCoset (GL_pair 2)) =
          ⟦diagMat_delta 2 (![1, n + 1])⟧
        rw [HeckeCoset.eq_iff]
        simp only [diagMat_delta, show ∀ k : ℕ, (∀ i : Fin 2, 0 < (![1, k + 1]) i) from
          fun k i ↦ by fin_cases i <;> simp]
        exact h_gl
      have hpos : ∀ k : ℕ, ∀ i, 0 < (![1, k + 1]) i :=
        fun k i ↦ by fin_cases i <;> simp
      have := diagonal_representative_unique 2 _ _ (hpos m) (hpos n)
        (divChain_one_succ m) (divChain_one_succ n) h_T
      have h1 := congr_fun this 1
      simp [Matrix.cons_val_one] at h1
      omega)

/-- `diagMat 2 a ∈ Δ₀(N)` when all entries are positive and `gcd(a 0, N) = 1`. -/
lemma diagMat_mem_Delta0_of_gcd (N : ℕ) (a : Fin 2 → ℕ)
    (ha : ∀ i, 0 < a i) (hgcd : Int.gcd (a 0) N = 1) :
    diagMat 2 a ∈ Delta0_submonoid N := by
  refine ⟨diagMat_hasIntEntries 2 a ha, diagMat_det_pos 2 a ha,
    Matrix.diagonal (fun i ↦ (a i : ℤ)), ?_, ?_, ?_⟩
  · ext i j; simp [diagMat, ha, Matrix.diagonal, Matrix.map_apply]
  · simp [Matrix.diagonal]
  · simpa [Matrix.diagonal] using hgcd

/-- The Gamma0 coset of `diag(a)` when `gcd(a₁, N) = 1`:
    the Gamma0-level analogue of `T_diag`. -/
noncomputable def T_diag_Gamma0 (N : ℕ) [NeZero N] (a : Fin 2 → ℕ)
    (ha : ∀ i, 0 < a i) (hgcd : Int.gcd (a 0) N = 1) :
    HeckeCoset (Gamma0_pair N) :=
  ⟦⟨diagMat 2 a, diagMat_mem_Delta0_of_gcd N a ha hgcd⟩⟧

private lemma exists_mod_clearing (a c : ℤ) (p : ℕ)
    (hap : Int.gcd a p = 1) :
    ∃ t : ℤ, (p : ℤ) ∣ (t * a + c) := by
  refine ⟨-c * Int.gcdA a p, ⟨c * Int.gcdB a p, ?_⟩⟩
  have bez := Int.gcd_eq_gcd_ab a p
  rw [hap] at bez
  linear_combination c * bez

private lemma dvd_lowerRight_witness (A : Matrix (Fin 2) (Fin 2) ℤ) (N m : ℕ) (c₀ r : ℤ)
    (hc₀ : A 1 0 = (N : ℤ) * c₀) (hdet : A.det = m) (ham : Int.gcd (A 0 0) m = 1)
    (hm_ar_b : (m : ℤ) ∣ (A 0 0 * r - A 0 1)) :
    (m : ℤ) ∣ (A 1 1 - ↑N * c₀ * r) := by
  have h_key : A 0 0 * (A 1 1 - ↑N * c₀ * r) = ↑m + (A 0 1 - A 0 0 * r) * (↑N * c₀) := by
    have h_det := Matrix.det_fin_two A; rw [hc₀, hdet] at h_det; linarith
  have hm_ba : (↑m : ℤ) ∣ (A 0 1 - A 0 0 * r) := by
    obtain ⟨w, hw⟩ := hm_ar_b; exact ⟨-w, by linarith⟩
  exact ((Int.isCoprime_iff_gcd_eq_one.mpr ham).symm).dvd_of_dvd_mul_left
    (h_key ▸ dvd_add (dvd_refl _) (dvd_mul_of_dvd_left hm_ba _))

private lemma Gamma0_left_coset_of_Npow_det (N : ℕ) [NeZero N]
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hA_det_pos : 0 < A.det) (hAN : (N : ℤ) ∣ A 1 0)
    (m : ℕ) (_hm_pos : 0 < m) (hdet : A.det = m) (ham : Int.gcd (A 0 0) m = 1) :
    ∃ (L : Matrix (Fin 2) (Fin 2) ℤ) (r : ℤ),
      L.det = 1 ∧ (N : ℤ) ∣ L 1 0 ∧ 0 ≤ r ∧ r < m ∧
      A = L * (Matrix.of ![![(1 : ℤ), r], ![0, m]]) := by
  obtain ⟨c₀, hc₀⟩ := hAN
  obtain ⟨t_inv, ht⟩ := exists_mod_clearing (A 0 0) (- A 0 1) m ham
  set r := t_inv % (m : ℤ) with hr_def
  have hr_nonneg : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have hr_lt : r < m := Int.emod_lt_of_pos _ (by omega)
  have hm_tr : (m : ℤ) ∣ (t_inv - r) := by
    rw [hr_def, show t_inv - t_inv % ↑m = ↑m * (t_inv / ↑m) from by
      linarith [Int.mul_ediv_add_emod t_inv (↑m : ℤ)]]
    exact dvd_mul_right _ _
  have hm_ar_b : (m : ℤ) ∣ (A 0 0 * r - A 0 1) := by
    have h := dvd_sub ht (dvd_mul_of_dvd_left hm_tr (A 0 0))
    rwa [show t_inv * A 0 0 + -A 0 1 - (t_inv - r) * A 0 0 = A 0 0 * r - A 0 1 from by ring] at h
  obtain ⟨q₂, hq₂⟩ := dvd_lowerRight_witness A N m c₀ r hc₀ hdet ham hm_ar_b
  obtain ⟨q₁, hq₁⟩ := hm_ar_b
  refine ⟨Matrix.of ![![A 0 0, -q₁], ![↑N * c₀, q₂]], r, ?_, ?_, hr_nonneg, hr_lt, ?_⟩
  · simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val']
    have hAdet' : A.det = A 0 0 * A 1 1 - A 0 1 * (↑N * c₀) := by rw [Matrix.det_fin_two, hc₀]
    have h1 : (A 0 0 * q₂ + q₁ * (↑N * c₀)) * ↑m = ↑m := by
      have h_det_val := hAdet'; rw [hdet] at h_det_val
      calc (A 0 0 * q₂ + q₁ * (↑N * c₀)) * ↑m
          = A 0 0 * (↑m * q₂) + (↑m * q₁) * (↑N * c₀) := by ring
        _ = A 0 0 * (A 1 1 - ↑N * c₀ * r) + (A 0 0 * r - A 0 1) * (↑N * c₀) := by
            rw [← hq₂, ← hq₁]
        _ = A 0 0 * A 1 1 - A 0 1 * (↑N * c₀) := by ring
        _ = ↑m := h_det_val.symm
    have := mul_right_cancel₀ (show (↑m : ℤ) ≠ 0 from by omega) (show
      (A 0 0 * q₂ + q₁ * (↑N * c₀)) * ↑m = 1 * ↑m by rw [one_mul]; exact h1)
    linarith
  · norm_num [Matrix.of_apply, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val', Matrix.cons_val_zero]
  · have h00 : A 0 0 = A 0 0 * 1 + (-q₁) * 0 := by ring
    have h01 : A 0 1 = A 0 0 * r + (-q₁) * ↑m := by linarith [hq₁]
    have h10 : A 1 0 = ↑N * c₀ * 1 + q₂ * 0 := by linarith [hc₀]
    have h11 : A 1 1 = ↑N * c₀ * r + q₂ * ↑m := by linarith [hq₂]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.isValue,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val'] <;>
      first | exact h00 | exact h01 | exact h10 | exact h11

private lemma fin2_col_scale (m : ℕ) (j : Fin 2) :
    (![0, (m : ℤ)] : Fin 2 → ℤ) j = (m : ℤ) * (![0, 1] : Fin 2 → ℤ) j := by
  fin_cases j <;> simp

noncomputable def lunip_inject (N : ℕ) [NeZero N] (k_exp : ℕ)
    (g : (Gamma0_pair N).Δ) : Fin k_exp → HeckeRing.decompQuot (Gamma0_pair N) g :=
  fun r ↦ ⟦⟨mapGL ℚ ⟨Matrix.of ![![(1 : ℤ), 0], ![↑N * (↑r : ℤ), 1]],
    by simp [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]⟩,
    Subgroup.mem_map_of_mem _ (by
      rw [CongruenceSubgroup.Gamma0_mem]
      simp [Matrix.of_apply, Matrix.cons_val_one])⟩⟧

private lemma coprime_of_gcd_one_dvd_pow (a : ℤ) (N : ℕ) (k : ℕ) (hk : ℕ)
    (haN : Int.gcd a N = 1) (hk_dvd : k ∣ N ^ hk) : Int.gcd a k = 1 :=
  Nat.Coprime.coprime_dvd_right hk_dvd (Nat.Coprime.pow_right hk haN)

/-- **Generalized Shimura 3.33**: all `β ∈ Δ₀(N)` with `det = m` and
`gcd(A 0 0, m) = 1` are in `DC(diag(1, m), Γ₀, Γ₀)`. -/
lemma shimura_prop_3_33_gen (N : ℕ) [NeZero N]
    (m : ℕ) (hm_pos : 0 < m)
    (β : GL (Fin 2) ℚ) (hβ : β ∈ Delta0_submonoid N)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : (β : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hAN : (N : ℤ) ∣ A 1 0)
    (hdet : (β : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ))
    (ham : Int.gcd (A 0 0) m = 1) :
    β ∈ DoubleCoset.doubleCoset
      ((diagMat 2 (![1, m] : Fin 2 → ℕ) : GL (Fin 2) ℚ))
      ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
  have hdet_pos : 0 < (β : Matrix (Fin 2) (Fin 2) ℚ).det := hβ.2.1
  have hA_det_pos : 0 < A.det := by
    rwa [← Int.cast_pos (R := ℚ), ← det_intMat_cast 2 A, ← hA]
  have hA_det : A.det = ↑m := by
    have : (A.det : ℚ) = ↑m := by rw [← det_intMat_cast 2 A, ← hA]; exact hdet
    exact_mod_cast this
  obtain ⟨L, r, hL_det, hL_N, hr_nn, hr_lt, hA_eq⟩ :=
    Gamma0_left_coset_of_Npow_det N A hA_det_pos hAN m hm_pos hA_det ham
  rw [DoubleCoset.mem_doubleCoset]
  set L_sl : SpecialLinearGroup (Fin 2) ℤ := ⟨L, hL_det⟩
  set R : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of ![![1, r], ![0, 1]] with hR_def
  have hR_det : R.det = 1 := by
    simp [R, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  set R_sl : SpecialLinearGroup (Fin 2) ℤ := ⟨R, hR_det⟩
  have hL_Gamma0 : L_sl ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hL_N
  have hR_Gamma0 : R_sl ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [R_sl, R, Matrix.of_apply, Matrix.cons_val_one]
  refine ⟨mapGL ℚ L_sl, Subgroup.mem_map_of_mem _ hL_Gamma0,
    mapGL ℚ R_sl, Subgroup.mem_map_of_mem _ hR_Gamma0, ?_⟩
  apply Units.ext; ext i j
  have hA_ij := congr_fun₂ hA_eq i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Fin.isValue,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val'] at hA_ij
  set D := diagMat 2 (![1, m] : Fin 2 → ℕ)
  have hD_pos : ∀ i : Fin 2, 0 < (![1, m] : Fin 2 → ℕ) i := by intro i; fin_cases i <;> simp [hm_pos]
  have hDv := diagMat_val 2 (![1, m] : Fin 2 → ℕ) hD_pos
  have hd00 : (D : GL (Fin 2) ℚ).val 0 0 = 1 := by rw [hDv]; simp [Matrix.diagonal]
  have hd01 : (D : GL (Fin 2) ℚ).val 0 1 = 0 := by rw [hDv]; simp [Matrix.diagonal]
  have hd10 : (D : GL (Fin 2) ℚ).val 1 0 = 0 := by rw [hDv]; simp [Matrix.diagonal]
  have hd11 : (D : GL (Fin 2) ℚ).val 1 1 = ↑m := by rw [hDv]; simp [Matrix.diagonal]
  simp only [GeneralLinearGroup.coe_mul, mapGL_coe_matrix, RingHom.mapMatrix_apply,
    algebraMap_int_eq, Int.coe_castRingHom, hA, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.map_apply, SpecialLinearGroup.map, MonoidHom.coe_mk, OneHom.coe_mk,
    L_sl, R_sl, SpecialLinearGroup.coe_mk, R, Matrix.of_apply, Fin.isValue,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', hd00, hd01, hd10, hd11]
  fin_cases i <;> fin_cases j <;> (
    simp only [Fin.isValue, mul_zero, mul_one, add_zero, zero_add] at hA_ij ⊢
    simp only [fin2_col_scale] at hA_ij
    norm_cast; linarith [hA_ij])

/-- **Shimura Proposition 3.33** (double coset form): Every element of `Δ₀(N)` with
determinant `m` (where `m ∣ N^k`) is in the `Γ₀(N)`-double coset of `[[1,0],[0,m]]`. -/
lemma shimura_prop_3_33 (N : ℕ) [NeZero N]
    (m : ℕ) (hm_pos : 0 < m) (k : ℕ) (hm_dvd : m ∣ N ^ k)
    (β : GL (Fin 2) ℚ) (hβ : β ∈ Delta0_submonoid N)
    (hdet : (β : Matrix (Fin 2) (Fin 2) ℚ).det = (m : ℚ)) :
    β ∈ DoubleCoset.doubleCoset
      ((diagMat 2 (![1, m] : Fin 2 → ℕ) : GL (Fin 2) ℚ))
      ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
  obtain ⟨_, _, A, hA, hAN, hAco⟩ := id hβ
  exact shimura_prop_3_33_gen N m hm_pos β hβ A hA hAN hdet
    (coprime_of_gcd_one_dvd_pow (A 0 0) N m k hAco hm_dvd)

private lemma sl2_conj_lunip_10 (σ : SpecialLinearGroup (Fin 2) ℤ) (c : ℤ) :
    ((σ⁻¹ : SpecialLinearGroup (Fin 2) ℤ).1 *
      Matrix.of ![![(1 : ℤ), 0], ![c, 1]] * σ.1) 1 0 = σ.1 0 0 ^ 2 * c := by
  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Fin.isValue]
  ring

private lemma exists_clearing_mod (a c' : ℤ) (k : ℕ) (hk_pos : 0 < k)
    (hak : Int.gcd a k = 1) :
    ∃ r : ℤ, 0 ≤ r ∧ r < k ∧ ∃ c'' : ℤ, a * r - c' = k * c'' := by
  obtain ⟨u_bez, w, huv⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hak
  have hr₀_mod : (k : ℤ) ∣ (a * (u_bez * c') - c') := by
    have : a * (u_bez * c') - c' = (a * u_bez - 1) * c' := by ring
    rw [this]; exact dvd_mul_of_dvd_left ⟨-w, by linarith⟩ c'
  refine ⟨(u_bez * c') % k, Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega), ?_⟩
  have h2 : (k : ℤ) ∣ ((u_bez * c') - (u_bez * c') % k) :=
    ⟨(u_bez * c') / k, by have := Int.mul_ediv_add_emod (u_bez * c') (k : ℤ); omega⟩
  have e : a * ((u_bez * c') % k) - c' =
      (a * (u_bez * c') - c') - a * ((u_bez * c') - (u_bez * c') % k) := by ring
  exact e ▸ dvd_sub hr₀_mod (dvd_mul_of_dvd_right h2 _)

private lemma lunip_conj_diag_eq (N : ℕ) [NeZero N] (k_exp : ℕ)
    (ha : ∀ i : Fin 2, 0 < (![1, k_exp] : Fin 2 → ℕ) i)
    (τ' : SpecialLinearGroup (Fin 2) ℤ) (r_int c' c'' : ℤ)
    (hc' : τ'.1 1 0 = (N : ℤ) * c') (hc'' : τ'.1 0 0 * r_int - c' = ↑k_exp * c'')
    (hW : (Matrix.of ![![τ'.1 1 1 - (N : ℤ) * r_int * τ'.1 0 1, -(τ'.1 0 1) * k_exp],
        ![(N : ℤ) * c'', τ'.1 0 0]]).det = 1)
    (hU : (!![1, 0; (N : ℤ) * ↑r_int.toNat, 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1)
    (hr_nn : 0 ≤ r_int) :
    (↑(diagMat 2 (![1, k_exp] : Fin 2 → ℕ)) : GL (Fin 2) ℚ) *
        mapGL ℚ ⟨Matrix.of ![![τ'.1 1 1 - (N : ℤ) * r_int * τ'.1 0 1, -(τ'.1 0 1) * k_exp],
          ![(N : ℤ) * c'', τ'.1 0 0]], hW⟩ =
      (mapGL ℚ τ')⁻¹ * mapGL ℚ ⟨!![1, 0; (N : ℤ) * ↑r_int.toNat, 1], hU⟩ *
        ↑(diagMat 2 (![1, k_exp] : Fin 2 → ℕ)) := by
  rw [show ((mapGL ℚ τ')⁻¹ : GL (Fin 2) ℚ) = mapGL ℚ τ'⁻¹ from (map_inv (mapGL ℚ) τ').symm,
    ← map_mul]
  apply Units.ext; ext i j
  simp only [diagMat_val 2 _ ha, mapGL_coe_matrix, GeneralLinearGroup.coe_mul,
    algebraMap_int_eq, Int.coe_castRingHom, Matrix.map_apply,
    SpecialLinearGroup.coe_matrix_coe,
    SpecialLinearGroup.coe_inv, SpecialLinearGroup.coe_mul,
    Matrix.adjugate_fin_two, Matrix.of_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue, Matrix.diagonal_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', mul_zero, mul_one, zero_add, neg_mul, Nat.cast_one]
  have hr_cast : ((r_int).toNat : ℤ) = r_int := Int.toNat_of_nonneg hr_nn
  fin_cases i <;> fin_cases j <;>
    simp only [hr_cast] <;>
    push_cast [hc', hc''] <;>
    (try ring) <;>
    (have := congr_arg (Int.cast (R := ℚ)) hc''; push_cast at this ⊢; nlinarith)

lemma lunip_inject_surjective (N : ℕ) [NeZero N]
    (k_exp : ℕ) (hk_pos : 0 < k_exp) (hk : ℕ) (hk_dvd : k_exp ∣ N ^ hk)
    (ha : ∀ i : Fin 2, 0 < (![1, k_exp] : Fin 2 → ℕ) i) :
    Function.Surjective (lunip_inject N k_exp
      ⟨diagMat 2 (![1, k_exp] : Fin 2 → ℕ), diagMat_mem_Delta0_of_gcd N _ ha (by simp)⟩) := by
  set g_diag : (Gamma0_pair N).Δ := ⟨diagMat 2 (![1, k_exp] : Fin 2 → ℕ),
    diagMat_mem_Delta0_of_gcd N _ ha (by simp)⟩
  intro q; revert q; apply Quotient.ind; intro ⟨σ_gl, hσ_gl⟩
  obtain ⟨τ', hτ'_mem, hτ'_eq⟩ := Subgroup.mem_map.mp hσ_gl
  rw [CongruenceSubgroup.Gamma0_mem] at hτ'_mem
  obtain ⟨c', hc'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hτ'_mem
  have hτ'_det := τ'.prop; rw [Matrix.det_fin_two] at hτ'_det
  have hτ'_a_N : Int.gcd (τ'.1 0 0) ↑N = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp ⟨τ'.1 1 1, -(τ'.1 0 1) * c',
      by rw [hc'] at hτ'_det; nlinarith⟩
  obtain ⟨r_int, hr_nn, hr_lt, c'', hc''⟩ := exists_clearing_mod (τ'.1 0 0) c' k_exp hk_pos
    (coprime_of_gcd_one_dvd_pow _ N k_exp hk hτ'_a_N hk_dvd)
  refine ⟨⟨r_int.toNat, by omega⟩, ?_⟩
  simp only [lunip_inject]
  symm; rw [@Quotient.eq'', QuotientGroup.leftRel_apply]
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def]
  simp only [ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  set wit : Matrix (Fin 2) (Fin 2) ℤ :=
    Matrix.of ![![τ'.1 1 1 - (N : ℤ) * r_int * τ'.1 0 1, -(τ'.1 0 1) * k_exp],
      ![(N : ℤ) * c'', τ'.1 0 0]]
  have hc'_eq : c' = τ'.1 0 0 * r_int - ↑k_exp * c'' := by linarith [hc'']
  have hwit_det : wit.det = 1 := by
    simp only [wit, Matrix.det_fin_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hc'] at hτ'_det
    linear_combination hτ'_det + τ'.1 0 1 * (N : ℤ) * hc'_eq
  have hwit_Gamma0 : (⟨wit, hwit_det⟩ : SL(2, ℤ)) ∈
      CongruenceSubgroup.Gamma0 N :=
    CongruenceSubgroup.Gamma0_mem.mpr (by simp [wit, Matrix.of_apply, Matrix.cons_val_one])
  have h_wit_mem := Subgroup.mem_map_of_mem (mapGL ℚ) hwit_Gamma0
  set D_gl := (↑g_diag : GL (Fin 2) ℚ)
  set U_r : SpecialLinearGroup (Fin 2) ℤ := ⟨!![1, 0; (N : ℤ) * ↑r_int.toNat, 1],
    by simp [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]⟩ with hU_r_def
  have h_eq : D_gl * mapGL ℚ ⟨wit, hwit_det⟩ = σ_gl⁻¹ * mapGL ℚ U_r * D_gl := by
    rw [← hτ'_eq]
    exact lunip_conj_diag_eq N k_exp ha τ' r_int c' c'' hc' hc'' hwit_det U_r.2 hr_nn
  show D_gl⁻¹ * (σ_gl⁻¹ * mapGL ℚ U_r) * D_gl ∈ (Gamma0_pair N).H
  have h_conj : mapGL ℚ ⟨wit, hwit_det⟩ = D_gl⁻¹ * (σ_gl⁻¹ * mapGL ℚ U_r) * D_gl := by
    have := congr_arg (D_gl⁻¹ * ·) h_eq
    simp only [← mul_assoc, inv_mul_cancel, one_mul] at this
    convert this using 2; group
  rw [← h_conj]; exact h_wit_mem

/-- Algebraic identity in `SL₂(ℤ)`: the inverse-product of two row-2 unipotents
indexed by `r₁, r₂` (i.e. `(1,0; N·r,1)`) equals the row-2 unipotent indexed
by `r₂ - r₁`. -/
private lemma lunip_diff_unipotent_mul (N : ℕ) (r₁ r₂ : ℤ)
    (u1 u2 u_diff : SpecialLinearGroup (Fin 2) ℤ)
    (hu1 : u1.1 = Matrix.of ![![(1 : ℤ), 0], ![(N : ℤ) * r₁, 1]])
    (hu2 : u2.1 = Matrix.of ![![(1 : ℤ), 0], ![(N : ℤ) * r₂, 1]])
    (huD : u_diff.1 = Matrix.of ![![(1 : ℤ), 0], ![(N : ℤ) * (r₂ - r₁), 1]]) :
    u1⁻¹ * u2 = u_diff := by
  apply Subtype.ext
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [hu1, hu2, huD, Matrix.mul_apply, Fin.sum_univ_two,
      SpecialLinearGroup.coe_inv, SpecialLinearGroup.coe_mul,
      Matrix.adjugate_fin_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val']
    <;> ring

/-- Given the matrix equation `D · τ = σ₁⁻¹ · u_diff · σ₁ · D` in `GL₂(ℚ)`
(viewed at position `(1,0)`), with `τ.1 1 0 = N·q₂`, derive the integer
identity `σ₁.1 0 0 ^ 2 · (r₂ - r₁) = k_exp · q₂`. This is the arithmetic
core of `lunip_inject_injective`. -/
lemma lunip_inject_witness_eq (N : ℕ) [NeZero N] (k_exp : ℕ)
    (ha : ∀ i : Fin 2, 0 < (![1, k_exp] : Fin 2 → ℕ) i)
    (σ₁ τ u_diff : SpecialLinearGroup (Fin 2) ℤ)
    (r₁ r₂ : Fin k_exp) (q₂ : ℤ) (hq₂ : τ.1 1 0 = ↑N * q₂)
    (huD : u_diff.1 = Matrix.of ![![(1 : ℤ), 0], ![(N : ℤ) * (↑↑r₂ - ↑↑r₁), 1]])
    (h_mul : (↑(diagMat 2 (![1, k_exp] : Fin 2 → ℕ)) : GL (Fin 2) ℚ) * mapGL ℚ τ =
      mapGL ℚ (σ₁⁻¹ * u_diff * σ₁) *
        ↑(diagMat 2 (![1, k_exp] : Fin 2 → ℕ))) :
    σ₁.1 0 0 ^ 2 * ((↑↑r₂ : ℤ) - ↑↑r₁) = ↑k_exp * q₂ := by
  set D := diagMat 2 (![1, k_exp] : Fin 2 → ℕ)
  have h_e2 := congr_arg
    (fun x : GL (Fin 2) ℚ ↦ (x : Matrix (Fin 2) (Fin 2) ℚ) 1 0) h_mul
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, D,
    diagMat_val 2 _ ha, Matrix.diagonal_apply, if_true,
    mapGL_coe_matrix, algebraMap_int_eq] at h_e2
  simp only [SpecialLinearGroup.coe_matrix_coe, Matrix.map_apply,
    Int.coe_castRingHom, SpecialLinearGroup.coe_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Nat.cast_one, mul_one] at h_e2
  have h_sl2 := sl2_conj_lunip_10 σ₁ (↑N * (↑↑r₂ - ↑↑r₁))
  have h_rhs_z : ((σ₁⁻¹ : SpecialLinearGroup (Fin 2) ℤ).1 * u_diff.1 * σ₁.1) 1 0 =
      σ₁.1 0 0 ^ 2 * ((N : ℤ) * ((↑↑r₂ : ℤ) - ↑↑r₁)) := by
    rw [huD]; exact h_sl2
  rw [congr_arg (Int.cast (R := ℚ)) h_rhs_z, hq₂] at h_e2
  have hN_ne : ((N : ℤ) : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne N))
  have h_q : ((σ₁.1 0 0 ^ 2 * ((↑↑r₂ : ℤ) - ↑↑r₁) : ℤ) : ℚ) =
      ((↑k_exp * q₂ : ℤ) : ℚ) := by
    apply mul_left_cancel₀ hN_ne; push_cast; push_cast at h_e2; nlinarith [h_e2]
  exact_mod_cast h_q

/-- The conjugation bridge for `lunip_inject_injective`: combines the unipotent
algebra with the matrix-coefficient witness to extract divisibility from the
conjugation hypothesis. -/
lemma lunip_inject_dvd_of_conj (N : ℕ) [NeZero N] (k_exp : ℕ)
    (ha : ∀ i : Fin 2, 0 < (![1, k_exp] : Fin 2 → ℕ) i)
    (σ₁ τ : SpecialLinearGroup (Fin 2) ℤ) (r₁ r₂ : Fin k_exp)
    (hτ_dvd : (↑N : ℤ) ∣ τ.1 1 0)
    (ha₁k : Int.gcd (σ₁.1 0 0) ↑k_exp = 1)
    (h_mul : (↑(diagMat 2 (![1, k_exp] : Fin 2 → ℕ)) : GL (Fin 2) ℚ) * mapGL ℚ τ =
      (mapGL ℚ σ₁)⁻¹ *
        ((mapGL ℚ ⟨Matrix.of ![![(1 : ℤ), 0], ![(N : ℤ) * ↑↑r₁, 1]],
            by simp [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
              Matrix.cons_val_one]⟩)⁻¹ *
         mapGL ℚ ⟨Matrix.of ![![(1 : ℤ), 0], ![(N : ℤ) * ↑↑r₂, 1]],
            by simp [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
              Matrix.cons_val_one]⟩) *
        mapGL ℚ σ₁ * ↑(diagMat 2 (![1, k_exp] : Fin 2 → ℕ))) :
    (k_exp : ℤ) ∣ ((↑↑r₂ : ℤ) - ↑↑r₁) := by
  set u1 : SpecialLinearGroup (Fin 2) ℤ :=
    ⟨Matrix.of ![![(1 : ℤ), 0], ![(N : ℤ) * ↑↑r₁, 1]],
     by simp [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
       Matrix.cons_val_one]⟩
  set u2 : SpecialLinearGroup (Fin 2) ℤ :=
    ⟨Matrix.of ![![(1 : ℤ), 0], ![(N : ℤ) * ↑↑r₂, 1]],
     by simp [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
       Matrix.cons_val_one]⟩
  set u_diff : SpecialLinearGroup (Fin 2) ℤ :=
    ⟨Matrix.of ![![(1 : ℤ), 0], ![(N : ℤ) * (↑↑r₂ - ↑↑r₁), 1]],
     by simp [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
       Matrix.cons_val_one]⟩
  have hu : u1⁻¹ * u2 = u_diff :=
    lunip_diff_unipotent_mul N (↑↑r₁) (↑↑r₂) u1 u2 u_diff rfl rfl rfl
  have h_mul' : (↑(diagMat 2 (![1, k_exp] : Fin 2 → ℕ)) : GL (Fin 2) ℚ) * mapGL ℚ τ =
      mapGL ℚ (σ₁⁻¹ * u_diff * σ₁) *
        ↑(diagMat 2 (![1, k_exp] : Fin 2 → ℕ)) := by
    rw [h_mul, show ((mapGL ℚ σ₁)⁻¹ : GL (Fin 2) ℚ) = mapGL ℚ σ₁⁻¹ from
      (map_inv (mapGL ℚ) σ₁).symm,
      show (mapGL ℚ u1)⁻¹ = mapGL ℚ u1⁻¹ from (map_inv (mapGL ℚ) u1).symm,
      ← map_mul, hu, ← map_mul, ← map_mul]
  have ha₁k_cop : IsCoprime (σ₁.1 0 0 ^ 2) (↑k_exp : ℤ) :=
    (Int.isCoprime_iff_gcd_eq_one.mpr ha₁k).pow_left
  refine ha₁k_cop.symm.dvd_of_dvd_mul_left ?_
  obtain ⟨q₂, hq₂⟩ := hτ_dvd
  exact ⟨q₂, lunip_inject_witness_eq N k_exp ha σ₁ τ u_diff r₁ r₂ q₂ hq₂ rfl h_mul'⟩

lemma lunip_inject_injective (N : ℕ) [NeZero N]
    (k_exp : ℕ) (hk_pos : 0 < k_exp) (g : (Gamma0_pair N).Δ)
    (γ₁ γ₂ : GL (Fin 2) ℚ) (hγ₂ : γ₂ ∈ (Gamma0_pair N).H)
    (σ₁ : SpecialLinearGroup (Fin 2) ℤ) (hσ₁_eq : mapGL ℚ σ₁ = γ₁)
    (ha₁k : Int.gcd (σ₁.1 0 0) ↑k_exp = 1)
    (hg_eq : (↑g : GL (Fin 2) ℚ) = γ₁ * ↑(diagMat 2 (![1, k_exp] : Fin 2 → ℕ)) * γ₂) :
    Function.Injective (lunip_inject N k_exp g) := by
  have ha : ∀ i : Fin 2, 0 < (![1, k_exp] : Fin 2 → ℕ) i := by intro i; fin_cases i <;> simp [hk_pos]
  intro r₁ r₂ h_eq
  simp only [lunip_inject] at h_eq
  rw [@Quotient.eq'', QuotientGroup.leftRel_apply] at h_eq
  have h_mem := Subgroup.mem_subgroupOf.mp h_eq
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def] at h_mem
  simp only [ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at h_mem
  rw [hg_eq] at h_mem
  suffices h_dvd : (k_exp : ℤ) ∣ ((↑↑r₂ : ℤ) - ↑↑r₁) by
    have h0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h_dvd
      (by have := r₁.isLt; have := r₂.isLt; omega)
    exact Fin.ext (by omega)
  set D := diagMat 2 (![1, k_exp] : Fin 2 → ℕ)
  have h_conj := (Gamma0_pair N).H.mul_mem ((Gamma0_pair N).H.mul_mem hγ₂ h_mem)
    ((Gamma0_pair N).H.inv_mem hγ₂)
  have h_grp : ∀ (x : GL (Fin 2) ℚ),
      γ₂ * ((γ₁ * D * γ₂)⁻¹ * x * (γ₁ * D * γ₂)) * γ₂⁻¹ =
      D⁻¹ * (γ₁⁻¹ * x * γ₁) * D := fun x ↦ by group
  rw [h_grp] at h_conj
  obtain ⟨τ, hτ_mem, hτ_eq⟩ := Subgroup.mem_map.mp h_conj
  rw [CongruenceSubgroup.Gamma0_mem] at hτ_mem
  rw [← hσ₁_eq] at hτ_eq
  have h_mul := congr_arg (D * ·) hτ_eq
  simp only [← mul_assoc, mul_inv_cancel, one_mul] at h_mul
  have hτ_dvd : (↑N : ℤ) ∣ τ.1 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hτ_mem
  exact lunip_inject_dvd_of_conj N k_exp ha σ₁ τ r₁ r₂ hτ_dvd ha₁k h_mul

lemma decompQuot_Npow_natcard (N : ℕ) [NeZero N]
    (k_exp : ℕ) (hk_pos : 0 < k_exp) (hk : ℕ) (hk_dvd : k_exp ∣ N ^ hk)
    (g : (Gamma0_pair N).Δ)
    (hg : (⟦g⟧ : HeckeCoset (Gamma0_pair N)) = T_diag_Gamma0 N (![1, k_exp])
        (by intro i; fin_cases i <;> simp [hk_pos]) (by simp)) :
    Nat.card (HeckeRing.decompQuot (Gamma0_pair N) g) = k_exp := by
  have ha : ∀ i : Fin 2, 0 < (![1, k_exp] : Fin 2 → ℕ) i := by intro i; fin_cases i <;> simp [hk_pos]
  have hgcd : Int.gcd (↑((![1, k_exp] : Fin 2 → ℕ) 0)) ↑N = 1 := by simp
  have h_dc : DoubleCoset.doubleCoset (g : GL (Fin 2) ℚ)
      ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) =
    DoubleCoset.doubleCoset (diagMat 2 (![1, k_exp] : Fin 2 → ℕ) : GL (Fin 2) ℚ)
      ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) :=
    (HeckeCoset.eq_iff g _).mp hg
  have h_g_mem : (g : GL (Fin 2) ℚ) ∈ DoubleCoset.doubleCoset
      (diagMat 2 (![1, k_exp] : Fin 2 → ℕ) : GL (Fin 2) ℚ)
      ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _) := by
    rw [← h_dc]; exact DoubleCoset.mem_doubleCoset_self _ _ _
  rw [DoubleCoset.mem_doubleCoset] at h_g_mem
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hg_eq⟩ := h_g_mem
  obtain ⟨σ₁, hσ₁_mem, hσ₁_eq⟩ := Subgroup.mem_map.mp hγ₁
  rw [CongruenceSubgroup.Gamma0_mem] at hσ₁_mem
  have hN_c : (↑N : ℤ) ∣ (σ₁.1 1 0) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hσ₁_mem
  obtain ⟨q₁, hq₁⟩ := hN_c
  have hdet₁ := σ₁.prop; rw [Matrix.det_fin_two] at hdet₁
  have ha₁N : Int.gcd (σ₁.1 0 0) ↑N = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp ⟨σ₁.1 1 1, -(σ₁.1 0 1) * q₁,
      by rw [hq₁] at hdet₁; nlinarith⟩
  have ha₁k : Int.gcd (σ₁.1 0 0) ↑k_exp = 1 :=
    coprime_of_gcd_one_dvd_pow (σ₁.1 0 0) N k_exp hk ha₁N hk_dvd
  rw [show k_exp = Fintype.card (Fin k_exp) from (Fintype.card_fin k_exp).symm,
    ← Nat.card_eq_fintype_card]
  apply le_antisymm
  · set g_diag : (Gamma0_pair N).Δ := ⟨diagMat 2 (![1, k_exp] : Fin 2 → ℕ),
      diagMat_mem_Delta0_of_gcd N _ ha (by simp)⟩
    have h_card_eq : Nat.card (HeckeRing.decompQuot (Gamma0_pair N) g) =
        Nat.card (HeckeRing.decompQuot (Gamma0_pair N) g_diag) := by
      let g_mid : (Gamma0_pair N).Δ := ⟨γ₁ * ↑g_diag * γ₂, hg_eq ▸ g.2⟩
      have h_mid : (g_mid : GL (Fin 2) ℚ) = g := hg_eq.symm
      let e : HeckeRing.decompQuot (Gamma0_pair N) g ≃
          HeckeRing.decompQuot (Gamma0_pair N) g_diag :=
        (Equiv.cast (congrArg (HeckeRing.decompQuot (Gamma0_pair N))
          (Subtype.ext h_mid))).symm.trans
          (HeckeRing.decompQuot_double_H_equiv (Gamma0_pair N) g_diag ⟨γ₁, hγ₁⟩ ⟨γ₂, hγ₂⟩ (hg_eq ▸ g.2))
      exact Nat.card_congr e
    rw [h_card_eq]
    haveI : Fintype (HeckeRing.decompQuot (Gamma0_pair N) g_diag) :=
      HeckeRing.instFintypeDecompQuot _ _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_surjective (lunip_inject N k_exp g_diag)
      (lunip_inject_surjective N k_exp hk_pos hk hk_dvd ha)
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective (lunip_inject N k_exp g)
      (lunip_inject_injective N k_exp hk_pos g γ₁ γ₂ hγ₂ σ₁ hσ₁_eq ha₁k hg_eq)

/-- The Γ₀(N)-double-coset degree of the bad diagonal class `T(1,m)` for `m ∣ N^k` is `m`
(Shimura §3.3): the class decomposes into exactly `m` upper-triangular left cosets. -/
lemma Gamma0_bad_deg (N : ℕ) [NeZero N]
    (k_exp : ℕ) (hk_pos : 0 < k_exp) (hk : ℕ) (hk_dvd : k_exp ∣ N ^ hk) :
    HeckeRing.HeckeCoset_deg (Gamma0_pair N)
      (T_diag_Gamma0 N (![1, k_exp])
        (by intro i; fin_cases i <;> simp [hk_pos]) (by simp)) = k_exp := by
  simp only [HeckeRing.HeckeCoset_deg]
  rw [← Nat.card_eq_fintype_card]
  exact_mod_cast decompQuot_Npow_natcard N k_exp hk_pos hk hk_dvd _ (HeckeCoset.mk_rep _)

private lemma rep_T_diag_Gamma0_det (N : ℕ) [NeZero N] (a : Fin 2 → ℕ)
    (ha : ∀ i, 0 < a i) (hgcd : Int.gcd (↑(a 0)) ↑N = 1) :
    (↑(HeckeCoset.rep (T_diag_Gamma0 N a ha hgcd)) : GL (Fin 2) ℚ).val.det = ∏ i, (a i : ℚ) := by
  have h_in := DoubleCoset.mem_doubleCoset_self (Gamma0_pair N).H (Gamma0_pair N).H
    (↑(HeckeCoset.rep (T_diag_Gamma0 N a ha hgcd)) : GL (Fin 2) ℚ)
  rw [(HeckeCoset.eq_iff (HeckeCoset.rep (T_diag_Gamma0 N a ha hgcd))
      ⟨diagMat 2 a, diagMat_mem_Delta0_of_gcd N _ ha hgcd⟩).mp (HeckeCoset.mk_rep _)] at h_in
  rw [DoubleCoset.mem_doubleCoset] at h_in
  obtain ⟨h1, hh1, h2, hh2, hprod⟩ := h_in
  obtain ⟨s1, _, hs1⟩ := Subgroup.mem_map.mp hh1
  obtain ⟨s2, _, hs2⟩ := Subgroup.mem_map.mp hh2
  rw [show (HeckeCoset.rep (T_diag_Gamma0 N a ha hgcd) : GL (Fin 2) ℚ).val =
      h1.val * (diagMat 2 a : GL (Fin 2) ℚ).val * h2.val from congr_arg Units.val hprod,
    Matrix.det_mul, Matrix.det_mul,
    show h1.val.det = 1 from by rw [← hs1, mapGL_coe_matrix]; simp [det_intMat_cast 2, s1.prop],
    show h2.val.det = 1 from by rw [← hs2, mapGL_coe_matrix]; simp [det_intMat_cast 2, s2.prop],
    diagMat_det 2 _ ha]
  simp

private lemma mulMap_rep_T_diag_eq (N : ℕ) [NeZero N]
    (m n : ℕ) (hm_pos : 0 < m) (hn_pos : 0 < n)
    (km : ℕ) (hm_dvd : m ∣ N ^ km) (kn : ℕ) (hn_dvd : n ∣ N ^ kn)
    (ham : ∀ i, 0 < (![1, m] : Fin 2 → ℕ) i) (hgm : Int.gcd (↑((![1, m] : Fin 2 → ℕ) 0)) ↑N = 1)
    (han : ∀ i, 0 < (![1, n] : Fin 2 → ℕ) i) (hgn : Int.gcd (↑((![1, n] : Fin 2 → ℕ) 0)) ↑N = 1)
    (hamn : ∀ i, 0 < (![1, m * n] : Fin 2 → ℕ) i)
    (hgmn : Int.gcd (↑((![1, m * n] : Fin 2 → ℕ) 0)) ↑N = 1)
    (p : HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N (![1, m]) ham hgm)) ×
      HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N (![1, n]) han hgn))) :
    HeckeRing.mulMap (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N (![1, m]) ham hgm))
        (HeckeCoset.rep (T_diag_Gamma0 N (![1, n]) han hgn)) p =
      T_diag_Gamma0 N (![1, m * n]) hamn hgmn := by
  simp only [HeckeRing.mulMap]
  rw [show (T_diag_Gamma0 N (![1, m * n]) hamn hgmn) =
      ⟦(⟨diagMat 2 (![1, m * n]), diagMat_mem_Delta0_of_gcd N _ hamn hgmn⟩ :
        (Gamma0_pair N).Δ)⟧ from rfl]
  apply (HeckeCoset.eq_iff _ _).mpr
  refine DoubleCoset.doubleCoset_eq_of_mem
    (shimura_prop_3_33 N (m * n) (Nat.mul_pos hm_pos hn_pos) (km + kn)
      (Nat.mul_dvd_mul hm_dvd hn_dvd |>.trans (by rw [pow_add])) _ ?_ ?_)
  · exact Submonoid.mul_mem _
      (Submonoid.mul_mem _ ((Gamma0_pair N).h₀ p.1.out.2)
        (HeckeCoset.rep (T_diag_Gamma0 N (![1, m]) ham hgm)).2)
      (Submonoid.mul_mem _ ((Gamma0_pair N).h₀ p.2.out.2)
        (HeckeCoset.rep (T_diag_Gamma0 N (![1, n]) han hgn)).2)
  · simp only [Units.val_mul, Matrix.det_mul]
    obtain ⟨σi, _, hσi⟩ := Subgroup.mem_map.mp p.1.out.2
    obtain ⟨σj, _, hσj⟩ := Subgroup.mem_map.mp p.2.out.2
    have hdi : (↑p.1.out : GL (Fin 2) ℚ).val.det = 1 := by
      rw [← hσi, mapGL_coe_matrix]; simp [det_intMat_cast 2, σi.prop]
    have hdj : (↑p.2.out : GL (Fin 2) ℚ).val.det = 1 := by
      rw [← hσj, mapGL_coe_matrix]; simp [det_intMat_cast 2, σj.prop]
    rw [hdi, hdj, rep_T_diag_Gamma0_det N (![1, m]) ham hgm,
      rep_T_diag_Gamma0_det N (![1, n]) han hgn]
    simp only [one_mul, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast; ring

/-- **Bad-part multiplication** (Shimura Prop 3.33 consequence):
`T'(m) * T'(n) = T'(m*n)` for `m, n ∣ N^∞`. -/
theorem T_bad_mul (N : ℕ) [NeZero N]
    (m n : ℕ) (hm_pos : 0 < m) (hn_pos : 0 < n)
    (km : ℕ) (hm_dvd : m ∣ N ^ km) (kn : ℕ) (hn_dvd : n ∣ N ^ kn) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, m])
        (by intro i; fin_cases i <;> simp [hm_pos]) (by simp)) 1 *
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, n])
        (by intro i; fin_cases i <;> simp [hn_pos]) (by simp)) 1 =
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, m * n])
        (by intro i; fin_cases i <;> simp [Nat.mul_pos hm_pos hn_pos])
        (by simp)) 1 := by
  set D₁ := T_diag_Gamma0 N (![1, m]) (by intro i; fin_cases i <;> simp [hm_pos])
    (by simp)
  set D₂ := T_diag_Gamma0 N (![1, n]) (by intro i; fin_cases i <;> simp [hn_pos])
    (by simp)
  set D_out := T_diag_Gamma0 N (![1, m * n])
    (by intro i; fin_cases i <;> simp [Nat.mul_pos hm_pos hn_pos])
    (by simp)
  have h_mulMap : ∀ (p : HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
      HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂)),
      HeckeRing.mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) p = D_out :=
    fun p ↦ mulMap_rep_T_diag_eq N m n hm_pos hn_pos km hm_dvd kn hn_dvd _ _ _ _ _ _ p
  have h_deg_m : HeckeRing.HeckeCoset_deg (Gamma0_pair N) D₁ = m :=
    Gamma0_bad_deg N m hm_pos km hm_dvd
  have h_deg_n : HeckeRing.HeckeCoset_deg (Gamma0_pair N) D₂ = n :=
    Gamma0_bad_deg N n hn_pos kn hn_dvd
  have h_deg_mn : HeckeRing.HeckeCoset_deg (Gamma0_pair N) D_out = ↑m * ↑n :=
    Gamma0_bad_deg N (m * n) (Nat.mul_pos hm_pos hn_pos) (km + kn)
      (Nat.mul_dvd_mul hm_dvd hn_dvd |>.trans (by rw [pow_add]))
  have h_deg_prod : HeckeRing.deg (Gamma0_pair N)
      (HeckeRing.T_single _ ℤ D₁ 1 * HeckeRing.T_single _ ℤ D₂ 1) = (m : ℤ) * n := by
    rw [HeckeRing.deg_mul, HeckeRing.deg_T_single, HeckeRing.deg_T_single,
      one_mul, one_mul, h_deg_m, h_deg_n]
  apply HeckeRing.T_single_one_mul_eq_single
  · set μ := HeckeRing.heckeMultiplicity (Gamma0_pair N) D₁.rep D₂.rep D_out.rep
    have h_zero_all : ∀ A, A ≠ D_out → (HeckeRing.m (Gamma0_pair N) D₁.rep D₂.rep) A = 0 := by
      intro A hA; simp only [HeckeRing.m_apply]
      exact HeckeRing.heckeMultiplicity_eq_zero_of_mulMap_unique
        (Gamma0_pair N) _ _ D_out A hA h_mulMap
    have h_m_eq : HeckeRing.m (Gamma0_pair N) D₁.rep D₂.rep = Finsupp.single D_out μ := by
      ext A; simp only [Finsupp.single_apply, HeckeRing.m_apply]
      split_ifs with h
      · subst h; rfl
      · exact h_zero_all A (Ne.symm h)
    have h_deg_m_eq : HeckeRing.deg (Gamma0_pair N)
        (HeckeRing.m (Gamma0_pair N) D₁.rep D₂.rep) = μ * (↑m * ↑n) := by
      rw [h_m_eq]; simp [HeckeRing.deg_T_single, h_deg_mn]
    rw [HeckeRing.T_single_one_mul_T_single_one] at h_deg_prod
    have hmn_ne : (↑m * ↑n : ℤ) ≠ 0 := by positivity
    exact mul_right_cancel₀ hmn_ne (by linarith [h_deg_prod, h_deg_m_eq])
  · exact fun A hA ↦ HeckeRing.heckeMultiplicity_eq_zero_of_mulMap_unique (Gamma0_pair N)
      (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) D_out A hA h_mulMap

end HeckeRing.GLn

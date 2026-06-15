/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.CongruenceHecke.Presentation

/-!
# Hecke Ring for Congruence Subgroups (Shimura §3.3) — Degree combinatorics

Chinese-remainder degree multiplicativity for `Γ₀(N)` double cosets:
the diagonal stabilizer identification (`stab_diag_eq_Gamma0`), the coprime
degree multiplicativity `Gamma0_deg_coprime_mul`, and the prime-power degree
formulas (`HeckeCoset_deg_Gamma0_one_ppow`, `HeckeCoset_deg_Gamma0_p_ppow`).

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.2–3.3
-/

open Matrix Subgroup.Commensurable Pointwise Matrix.SpecialLinearGroup

open scoped Pointwise MatrixGroups

namespace HeckeRing.GLn

private lemma card_quotient_inf_of_set_mul {G : Type*} [Group G]
    (K₁ K₂ : Subgroup G) [K₁.FiniteIndex] [K₂.FiniteIndex] [(K₁ ⊓ K₂).FiniteIndex]
    (h_prod : ∀ g : G, ∃ k₁ ∈ K₁, ∃ k₂ ∈ K₂, g = k₁ * k₂) :
    Nat.card (G ⧸ (K₁ ⊓ K₂)) = Nat.card (G ⧸ K₁) * Nat.card (G ⧸ K₂) := by
  set f : G ⧸ (K₁ ⊓ K₂) → (G ⧸ K₁) × (G ⧸ K₂) :=
    Quotient.lift (fun g ↦ (QuotientGroup.mk g, QuotientGroup.mk g))
      (fun a b hab ↦ by
        have hmem := QuotientGroup.leftRel_apply.mp hab
        exact Prod.ext (QuotientGroup.eq.mpr (Subgroup.mem_inf.mp hmem).1)
          (QuotientGroup.eq.mpr (Subgroup.mem_inf.mp hmem).2))
  have hf_inj : Function.Injective f := by
    intro a b; refine Quotient.inductionOn₂ a b (fun x y h ↦ ?_)
    simp only [f, Quotient.lift_mk] at h
    have h1 := QuotientGroup.eq.mp (Prod.ext_iff.mp h).1
    have h2 := QuotientGroup.eq.mp (Prod.ext_iff.mp h).2
    exact QuotientGroup.eq.mpr (Subgroup.mem_inf.mpr ⟨h1, h2⟩)
  have hf_surj : Function.Surjective f := by
    rintro ⟨a, b⟩; refine Quotient.inductionOn₂ a b (fun α β ↦ ?_)
    obtain ⟨k₁, hk₁, k₂, hk₂, h_eq⟩ := h_prod (α⁻¹ * β)
    refine ⟨QuotientGroup.mk (α * k₁), Prod.ext ?_ ?_⟩
    · refine QuotientGroup.eq.mpr (?_ : (α * k₁)⁻¹ * α ∈ K₁)
      rw [show (α * k₁)⁻¹ * α = k₁⁻¹ from by group]; exact Subgroup.inv_mem _ hk₁
    · refine QuotientGroup.eq.mpr (?_ : (α * k₁)⁻¹ * β ∈ K₂)
      rw [show (α * k₁)⁻¹ * β = k₁⁻¹ * (α⁻¹ * β) from by group, h_eq,
        show k₁⁻¹ * (k₁ * k₂) = k₂ from by group]
      exact hk₂
  rw [← Nat.card_prod]
  exact Nat.card_eq_of_bijective _ ⟨hf_inj, hf_surj⟩

open CongruenceSubgroup in
private lemma Gamma0_inf_eq_of_coprime (N m n : ℕ) [NeZero N] [NeZero (m * N)] [NeZero (n * N)]
    [NeZero (m * n * N)] (hcop : Nat.Coprime m n) :
    Gamma0 (m * N) ⊓ Gamma0 (n * N) = Gamma0 (m * n * N) := by
  have hN_ne : (↑N : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hcop_int : IsCoprime (↑m : ℤ) (↑n : ℤ) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by simp only [Int.gcd, Int.natAbs_natCast]; exact hcop)
  ext g; simp only [Subgroup.mem_inf, Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  set c := (g 1 0 : ℤ)
  constructor
  · rintro ⟨hmN, hnN⟩
    have hN_dvd : (↑N : ℤ) ∣ c := dvd_trans (dvd_mul_left (↑N : ℤ) ↑m) hmN
    obtain ⟨q, hq⟩ := hN_dvd
    have hm : (↑m : ℤ) ∣ q := by
      rw [hq, show (↑(m * N) : ℤ) = ↑N * ↑m from by push_cast; ring] at hmN
      exact (mul_dvd_mul_iff_left hN_ne).mp hmN
    have hn : (↑n : ℤ) ∣ q := by
      rw [hq, show (↑(n * N) : ℤ) = ↑N * ↑n from by push_cast; ring] at hnN
      exact (mul_dvd_mul_iff_left hN_ne).mp hnN
    obtain ⟨r, hr⟩ := hcop_int.mul_dvd hm hn
    exact ⟨r, by rw [hq, hr]; push_cast; ring⟩
  · rintro ⟨r, hr⟩
    exact ⟨⟨n * r, by rw [hr]; push_cast; ring⟩,
           ⟨m * r, by rw [hr]; push_cast; ring⟩⟩

private lemma exists_coprime_shift_prime (f d : ℤ) (p : ℕ) (hp : p.Prime)
    (hdf : IsCoprime d f) : ∃ b₁ : ℤ, IsCoprime (f * b₁ - d) (↑p : ℤ) := by
  have hp_int : Prime (↑p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_cases hpd : (↑p : ℤ) ∣ d
  · have hpf : ¬(↑p : ℤ) ∣ f := by
      rw [← hp_int.coprime_iff_not_dvd, isCoprime_comm]
      exact (hdf.of_isCoprime_of_dvd_left hpd).symm
    exact ⟨1, by
      rw [mul_one, isCoprime_comm, hp_int.coprime_iff_not_dvd]
      intro h; exact hpf (by have := dvd_add h hpd; rwa [sub_add_cancel] at this)⟩
  · exact ⟨0, by
      simp only [mul_zero, zero_sub]
      rw [isCoprime_comm, hp_int.coprime_iff_not_dvd, dvd_neg]; exact hpd⟩

private lemma exists_coprime_shift_mul (f d a b : ℤ) (hab : IsCoprime a b)
    (ha : ∃ ba : ℤ, IsCoprime (f * ba - d) a) (hb : ∃ bb : ℤ, IsCoprime (f * bb - d) b) :
    ∃ b₁ : ℤ, IsCoprime (f * b₁ - d) (a * b) := by
  obtain ⟨ba, hba⟩ := ha
  obtain ⟨bb, hbb⟩ := hb
  obtain ⟨u, v, huv⟩ := hab
  have add_mul_coprime : ∀ {x y : ℤ} (z : ℤ), IsCoprime x y → IsCoprime (x + y * z) y := by
    intro x y z ⟨u, v, huv⟩; exact ⟨u, v - z * u, by linear_combination huv⟩
  refine ⟨ba * b * v + bb * a * u, ?_⟩
  rw [show f * (ba * b * v + bb * a * u) - d =
      (f * ba - d) * (b * v) + (f * bb - d) * (a * u) from by linear_combination d * huv]
  have hbv_a : IsCoprime a (b * v) := ⟨u, 1, by linear_combination huv⟩
  have hau_b : IsCoprime b (a * u) := ⟨v, 1, by linear_combination huv⟩
  apply IsCoprime.mul_right
  · rw [show (f * ba - d) * (b * v) + (f * bb - d) * (a * u) =
      (f * ba - d) * (b * v) + a * ((f * bb - d) * u) from by ring]
    exact add_mul_coprime _ (isCoprime_comm.mp ((isCoprime_comm.mp hba).mul_right hbv_a))
  · rw [show (f * ba - d) * (b * v) + (f * bb - d) * (a * u) =
      (f * bb - d) * (a * u) + b * (v * (f * ba - d)) from by ring]
    exact add_mul_coprime _ (isCoprime_comm.mp ((isCoprime_comm.mp hbb).mul_right hau_b))

private lemma exists_coprime_shift (N s d : ℤ) (m : ℕ) (hm_pos : 0 < m)
    (hdN : IsCoprime d N) (hds : IsCoprime d s) :
    ∃ b₁ : ℤ, Int.gcd (N * s * b₁ - d) m = 1 := by
  have hdNs : IsCoprime d (N * s) := hdN.mul_right hds
  set f := N * s
  suffices ∃ b₁ : ℤ, IsCoprime (f * b₁ - d) (↑m : ℤ) by
    obtain ⟨b₁, h⟩ := this; exact ⟨b₁, Int.isCoprime_iff_gcd_eq_one.mp h⟩
  revert hm_pos; refine Nat.recOnPosPrimePosCoprime ?_ ?_ ?_ ?_ m
  · intro p n hp hn _
    exact (exists_coprime_shift_prime f d p hp hdNs).imp fun b₁ h ↦ h.pow_right
  · intro h; omega
  · exact fun _ ↦ ⟨0, by simp [isCoprime_one_right]⟩
  · intro a b ha hb hab iha ihb _
    have hab_int : IsCoprime (↑a : ℤ) (↑b : ℤ) := by exact_mod_cast hab
    rw [show (↑(a * b) : ℤ) = ↑a * ↑b from by push_cast; ring]
    exact exists_coprime_shift_mul f d _ _ hab_int (iha (by omega)) (ihb (by omega))

open CongruenceSubgroup in
private lemma Gamma0_mN_mul_GammaN_eq_Gamma0 (N m : ℕ) [NeZero N] [NeZero (m * N)]
    (hm_pos : 0 < m) :
    ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N →
    ∃ σ : SL(2, ℤ), σ ∈ Gamma0 (m * N) ∧ σ⁻¹ * γ ∈ Gamma N := by
  intro γ hγ
  refine SpecialLinearGroup.fin_two_induction
    (P := fun g ↦ g ∈ Gamma0 N →
      ∃ σ : SL(2, ℤ), σ ∈ Gamma0 (m * N) ∧ σ⁻¹ * g ∈ Gamma N) ?_ γ hγ
  clear hγ γ
  intro a b c d hdet hγ
  have hNc : (↑N : ℤ) ∣ c := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
    simpa [Matrix.cons_val_one, Matrix.head_cons] using hγ
  obtain ⟨s, hs⟩ := hNc
  have hd_N : IsCoprime d (↑N : ℤ) := ⟨a, -b * s, by linarith [hs ▸ hdet]⟩
  have hd_s : IsCoprime d s := ⟨a, -b * ↑N, by linarith [hs ▸ hdet]⟩
  obtain ⟨b₁, hb₁⟩ := exists_coprime_shift (↑N * ↑N) s d m hm_pos (hd_N.mul_right hd_N) hd_s
  obtain ⟨u, v, huv⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hb₁
  set c₁ := -s * u
  have hσ10 : ↑N * s * (1 + ↑N * ↑N * b₁ * c₁) - d * (↑N * c₁) = ↑N * (s * ↑m * v) := by
    show ↑N * s * (1 + ↑N * ↑N * b₁ * c₁) - d * (↑N * (-s * u)) = ↑N * (s * ↑m * v)
    linear_combination (-↑N * s) * huv
  set σ₀₀ := a * (1 + ↑N * ↑N * b₁ * c₁) - b * (↑N * c₁)
  set σ₀₁ := b - a * (↑N * b₁)
  set σ₁₀ := ↑N * (s * ↑m * v)
  set σ₁₁ := d - ↑N * ↑N * s * b₁
  have hσ_det : σ₀₀ * σ₁₁ - σ₀₁ * σ₁₀ = 1 := by
    simp only [σ₀₀, σ₀₁, σ₁₀, σ₁₁]
    linear_combination -↑N * s * (b - a * ↑N * b₁) * huv + b * hs + hdet
  set σ : SL(2, ℤ) := ⟨!![σ₀₀, σ₀₁; σ₁₀, σ₁₁], by rwa [Matrix.det_fin_two_of]⟩
  refine ⟨σ, ?_, ?_⟩
  · rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    show (↑(m * N) : ℤ) ∣ σ₁₀
    exact ⟨s * v, by simp [σ₁₀]; ring⟩
  · rw [Gamma_mem']
    have hc_cast : (↑c : ZMod N) = 0 := by rw [hs]; push_cast; simp
    have hmod : (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))) σ =
        (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)))
          ⟨!![a, b; c, d], by rwa [Matrix.det_fin_two_of]⟩ := by
      ext i j
      simp only [σ, σ₀₀, σ₀₁, σ₁₀, σ₁₁, SL_reduction_mod_hom_val,
        Matrix.of_apply, Matrix.cons_val', Matrix.empty_val']
      fin_cases i <;> fin_cases j <;> push_cast <;> simp [hc_cast]
    rw [map_mul, map_inv, hmod, inv_mul_cancel]

private lemma diagConj_entry (k : ℕ) (hk : 0 < k) (σ : GL (Fin 2) ℚ) (i j : Fin 2) :
    ((diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ)⁻¹ * σ *
      (diagMat 2 (![1, k] : Fin 2 → ℕ))).val i j =
    !![σ.1 0 0, (k : ℚ) * σ.1 0 1;
       σ.1 1 0 / (k : ℚ), σ.1 1 1] i j := by
  have hk_ne : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hk_pos : ∀ i : Fin 2, 0 < (![1, k] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp [hk]
  have h_diag_val : (diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ).val =
      !![(1 : ℚ), 0; 0, (k : ℚ)] := by
    ext i j
    rw [diagMat_val 2 _ hk_pos]
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  have h_diag_inv_val : ((diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ)⁻¹).val =
      !![(1 : ℚ), 0; 0, (1 : ℚ) / k] := by
    rw [Matrix.coe_units_inv, h_diag_val, Matrix.inv_def, Matrix.adjugate_fin_two,
      Ring.inverse_eq_inv']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_two_of] <;> field_simp
  rw [Units.val_mul, Units.val_mul, h_diag_inv_val, h_diag_val, Matrix.mul_apply,
    Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    field_simp <;> ring

private lemma mem_Gamma0_kN_of_conj_mem_Gamma0_N (N : ℕ) [NeZero N] (k : ℕ) (hk : 0 < k)
    (σ τ : SL(2, ℤ)) (hτ_mem : τ ∈ CongruenceSubgroup.Gamma0 N)
    (h_conj : mapGL ℚ τ = (diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ)⁻¹ *
      mapGL ℚ σ * diagMat 2 (![1, k] : Fin 2 → ℕ)) :
    σ ∈ CongruenceSubgroup.Gamma0 (k * N) := by
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h_10_eq : (mapGL ℚ τ).val 1 0 = ((diagMat 2 (![1, k] : Fin 2 → ℕ) : GL _ ℚ)⁻¹ *
      mapGL ℚ σ * diagMat 2 (![1, k] : Fin 2 → ℕ)).val 1 0 := by rw [h_conj]
  rw [diagConj_entry k hk (mapGL ℚ σ) 1 0] at h_10_eq
  have h_lhs : (mapGL ℚ τ).val 1 0 = ((τ.1 1 0 : ℤ) : ℚ) := by
    simp [mapGL_coe_matrix, algebraMap_int_eq]
  have h_rhs : ((mapGL ℚ σ).val 1 0) = ((σ.1 1 0 : ℤ) : ℚ) := by
    simp [mapGL_coe_matrix, algebraMap_int_eq]
  have h_10 : ((τ.1 1 0 : ℤ) : ℚ) = ((σ.1 1 0 : ℤ) : ℚ) / (k : ℚ) := by
    rw [← h_lhs, h_10_eq]; simp [h_rhs]
  have h_mul : σ.1 1 0 = k * τ.1 1 0 := by
    have : ((σ.1 1 0 : ℤ) : ℚ) = (k : ℚ) * ((τ.1 1 0 : ℤ) : ℚ) := by rw [h_10]; field_simp
    exact_mod_cast this
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hτ_mem
  obtain ⟨r, hr⟩ := (by simpa using hτ_mem : (N : ℤ) ∣ τ.1 1 0)
  exact ⟨r, by rw [h_mul, hr]; push_cast; ring⟩

private lemma exists_conj_mem_Gamma0_N_of_mem_Gamma0_kN (N : ℕ) [NeZero N] (k : ℕ) (hk : 0 < k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 (k * N)) :
    ∃ τ : SL(2, ℤ), τ ∈ CongruenceSubgroup.Gamma0 N ∧
      mapGL ℚ τ = (diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ)⁻¹ *
        mapGL ℚ σ * diagMat 2 (![1, k] : Fin 2 → ℕ) := by
  have hk_ne_z : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hk.ne'
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hσ
  have hkN_dvd : (↑(k * N) : ℤ) ∣ σ.1 1 0 := by simpa using hσ
  have hk_dvd : (k : ℤ) ∣ σ.1 1 0 :=
    dvd_trans (show (k : ℤ) ∣ (↑(k * N) : ℤ) from by push_cast; exact dvd_mul_right _ _) hkN_dvd
  obtain ⟨q, hq⟩ := hk_dvd
  have hN_q : (N : ℤ) ∣ q := by
    obtain ⟨r, hr⟩ := hkN_dvd
    have heq : (k : ℤ) * q = (↑(k * N) : ℤ) * r := hq ▸ hr
    rw [show (↑(k * N) : ℤ) = (k : ℤ) * (N : ℤ) from by push_cast; ring] at heq
    rw [mul_assoc] at heq
    exact ⟨r, mul_left_cancel₀ hk_ne_z heq⟩
  have h_det : σ.1 0 0 * σ.1 1 1 - (k * σ.1 0 1) * q = 1 := by
    have hdet := σ.2
    rw [Matrix.det_fin_two] at hdet
    have hq' : σ.1 1 0 = k * q := hq
    linear_combination hdet + σ.1 0 1 * hq'
  refine ⟨⟨!![σ.1 0 0, k * σ.1 0 1; q, σ.1 1 1], by
      rw [Matrix.det_fin_two_of]; linarith [h_det]⟩, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa using hN_q
  · apply Units.ext
    ext i j
    rw [diagConj_entry k hk]
    have hq_q : ((σ.1 1 0 : ℤ) : ℚ) = (k : ℚ) * ((q : ℤ) : ℚ) := by exact_mod_cast hq
    have h_τ_val : ∀ a b, ((mapGL ℚ ⟨!![σ.1 0 0, k * σ.1 0 1; q, σ.1 1 1], by
        rw [Matrix.det_fin_two_of]; linarith [h_det]⟩).val a b : ℚ) =
        ((!![σ.1 0 0, k * σ.1 0 1; q, σ.1 1 1] a b : ℤ) : ℚ) := by
      intros; simp [mapGL_coe_matrix, Matrix.map_apply, algebraMap_int_eq]
    have h_σ_val : ∀ a b, ((mapGL ℚ σ).val a b : ℚ) = ((σ.val a b : ℤ) : ℚ) := by
      intros; simp [mapGL_coe_matrix, Matrix.map_apply, algebraMap_int_eq]
    simp only [h_τ_val, h_σ_val]
    have h_div : ((σ.val 1 0 : ℤ) : ℚ) / (k : ℚ) = (q : ℚ) := by rw [hq_q]; field_simp
    fin_cases i <;> fin_cases j <;> simp
    · exact h_div.symm

/-- **Diagonal stabilizer = Γ₀(kN)**: for the Hecke pair `(Γ₀(N), Δ₀(N))` and a
diagonal element `diag(1,k)`, the double-coset stabilizer
`(ConjAct g • H).subgroupOf H` inside `H = Γ₀(N).map(mapGL)` equals
`Γ₀(kN).map(mapGL).subgroupOf H`. -/
lemma stab_diag_eq_Gamma0 (N : ℕ) [NeZero N] (k : ℕ) (hk : 0 < k) :
    (ConjAct.toConjAct (diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ) •
      (Gamma0_pair N).H).subgroupOf (Gamma0_pair N).H =
    ((CongruenceSubgroup.Gamma0 (k * N)).map (mapGL ℚ)).subgroupOf
      (Gamma0_pair N).H := by
  ext ⟨γ, hγ_H⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def, ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  obtain ⟨σ, hσ_mem, hσ_eq⟩ := Subgroup.mem_map.mp hγ_H
  constructor
  · intro h_conj
    obtain ⟨τ, hτ_mem, hτ_eq⟩ := Subgroup.mem_map.mp h_conj
    exact Subgroup.mem_map.mpr ⟨σ, mem_Gamma0_kN_of_conj_mem_Gamma0_N N k hk σ τ hτ_mem
      (by rw [hτ_eq, hσ_eq]), hσ_eq⟩
  · intro h_σ_kN
    obtain ⟨σ', hσ'_mem, hσ'_eq⟩ := Subgroup.mem_map.mp h_σ_kN
    have hσ_eq_σ' : σ = σ' := mapGL_injective (hσ_eq.trans hσ'_eq.symm)
    subst hσ_eq_σ'
    obtain ⟨τ, hτ_mem, hτ_eq⟩ := exists_conj_mem_Gamma0_N_of_mem_Gamma0_kN N k hk σ hσ'_mem
    exact Subgroup.mem_map.mpr ⟨τ, hτ_mem, by rw [hτ_eq, hσ_eq]⟩

private lemma decompQuot_rep_card_eq {G : Type*} [Group G] (P : HeckeRing.HeckePair G)
    (g : P.Δ) :
    Nat.card (HeckeRing.decompQuot P (HeckeCoset.rep ⟦g⟧)) =
    Nat.card (HeckeRing.decompQuot P g) := by
  have h_mk := HeckeCoset.mk_rep (⟦g⟧ : HeckeRing.HeckeCoset P)
  rw [HeckeCoset.eq_iff] at h_mk
  have h_in : (HeckeCoset.rep ⟦g⟧ : G) ∈
      DoubleCoset.doubleCoset (g : G) (P.H : Set _) (P.H : Set _) := by
    rw [← h_mk]; exact DoubleCoset.mem_doubleCoset_self _ _ _
  rw [DoubleCoset.mem_doubleCoset] at h_in
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, h_eq⟩ := h_in
  have h_mid : ((⟨γ₁ * ↑g * γ₂, h_eq ▸ (HeckeCoset.rep ⟦g⟧).2⟩ : P.Δ) : G) =
      HeckeCoset.rep ⟦g⟧ := h_eq.symm
  exact Nat.card_congr (
    (Equiv.cast (congrArg (HeckeRing.decompQuot P) (Subtype.ext h_mid))).symm.trans
    (HeckeRing.decompQuot_double_H_equiv P g ⟨γ₁, hγ₁⟩ ⟨γ₂, hγ₂⟩
      (h_eq ▸ (HeckeCoset.rep ⟦g⟧).2)))

private lemma Gamma0_le_of_dvd {a b : ℕ} (hab : a ∣ b) :
    CongruenceSubgroup.Gamma0 b ≤ CongruenceSubgroup.Gamma0 a := by
  intro η hη
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hη ⊢
  exact dvd_trans (Int.natCast_dvd_natCast.mpr hab) hη

open CongruenceSubgroup in
private lemma mem_Gamma_mN_sup_nN_of_mem_Gamma_N (N m n : ℕ) [NeZero N]
    [NeZero (m * N)] [NeZero (n * N)] (hcop : Nat.Coprime m n)
    {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma N) :
    δ ∈ CongruenceSubgroup.Gamma (m * N) ⊔ CongruenceSubgroup.Gamma (n * N) := by
  have h_gcd : Nat.gcd (m * N) (n * N) = N := by
    rw [Nat.gcd_mul_right, hcop.gcd_eq_one, one_mul]
  haveI : NeZero ((m * N).gcd (n * N)) := ⟨by rw [h_gcd]; exact (Nat.pos_of_neZero N).ne'⟩
  have h_eq := Gamma_gcd_eq_mul (m * N) (n * N)
  rw [← Subgroup.map_sup, h_gcd] at h_eq
  exact Subgroup.map_injective mapGL_injective h_eq ▸ (h_gcd ▸ hδ)

open CongruenceSubgroup in
private lemma Gamma0_H_factor_through_mN_nN (N m n : ℕ) [NeZero N]
    (hm_pos : 0 < m) (hn_pos : 0 < n) (hcop : Nat.Coprime m n)
    (g : (Gamma0_pair N).H) :
    ∃ k₁ ∈ ((CongruenceSubgroup.Gamma0 (m * N)).map (mapGL ℚ)).subgroupOf (Gamma0_pair N).H,
    ∃ k₂ ∈ ((CongruenceSubgroup.Gamma0 (n * N)).map (mapGL ℚ)).subgroupOf (Gamma0_pair N).H,
      g = k₁ * k₂ := by
  obtain ⟨g, hg⟩ := g
  obtain ⟨γ, hγ_mem, hγ_eq⟩ := Subgroup.mem_map.mp hg
  have hN_pos : 0 < N := Nat.pos_of_neZero N
  haveI : NeZero (m * N) := ⟨by positivity⟩
  haveI : NeZero (n * N) := ⟨by positivity⟩
  obtain ⟨σ_m, hσ_m, hδ_m⟩ := Gamma0_mN_mul_GammaN_eq_Gamma0 N m hm_pos γ hγ_mem
  set δ := σ_m⁻¹ * γ with hδ_def
  haveI : (CongruenceSubgroup.Gamma (n * N)).Normal := CongruenceSubgroup.Gamma_normal _
  obtain ⟨α, hα, β, hβ, hαβ⟩ := Subgroup.mem_sup_of_normal_right.mp
    (mem_Gamma_mN_sup_nN_of_mem_Gamma_N N m n hcop hδ_m)
  have hα_Gamma0 : α ∈ CongruenceSubgroup.Gamma0 (m * N) := GammaN_le_Gamma0 (m * N) hα
  have hβ_Gamma0 : β ∈ CongruenceSubgroup.Gamma0 (n * N) := GammaN_le_Gamma0 (n * N) hβ
  have h_factor : γ = σ_m * α * β := by
    rw [mul_assoc, hαβ, hδ_def, ← mul_assoc, mul_inv_cancel, one_mul]
  refine ⟨⟨mapGL ℚ (σ_m * α), ?_⟩, ?_, ⟨mapGL ℚ β, ?_⟩, ?_, ?_⟩
  · exact Subgroup.mem_map_of_mem _ (Gamma0_le_of_dvd (Nat.dvd_mul_left N m)
      (Subgroup.mul_mem _ hσ_m hα_Gamma0))
  · exact Subgroup.mem_map_of_mem _ (Subgroup.mul_mem _ hσ_m hα_Gamma0)
  · exact Subgroup.mem_map_of_mem _ (Gamma0_le_of_dvd (Nat.dvd_mul_left N n) hβ_Gamma0)
  · exact Subgroup.mem_map_of_mem _ hβ_Gamma0
  · apply Subtype.ext
    show g = mapGL ℚ (σ_m * α) * mapGL ℚ β
    rw [← hγ_eq, h_factor]
    simp only [map_mul, mul_assoc]

private lemma HeckeCoset_deg_diagMat_eq_card_quotient (N k : ℕ) [NeZero N] (hk : 0 < k)
    (g : (Gamma0_pair N).Δ) (hg : (g : GL (Fin 2) ℚ) = diagMat 2 (![1, k] : Fin 2 → ℕ)) :
    (HeckeRing.HeckeCoset_deg (Gamma0_pair N) ⟦g⟧ : ℤ) =
    Nat.card (↥(Gamma0_pair N).H ⧸
      ((CongruenceSubgroup.Gamma0 (k * N)).map (mapGL ℚ)).subgroupOf (Gamma0_pair N).H) := by
  have h_stab : (ConjAct.toConjAct (g : GL (Fin 2) ℚ) • (Gamma0_pair N).H).subgroupOf
      (Gamma0_pair N).H =
      ((CongruenceSubgroup.Gamma0 (k * N)).map (mapGL ℚ)).subgroupOf (Gamma0_pair N).H := by
    rw [hg]; exact stab_diag_eq_Gamma0 N k hk
  simp only [HeckeRing.HeckeCoset_deg]
  haveI : Fintype (HeckeRing.decompQuot (Gamma0_pair N) g) := HeckeRing.instFintypeDecompQuot _ _
  rw [← Nat.card_eq_fintype_card, decompQuot_rep_card_eq]
  exact_mod_cast Nat.card_congr (Subgroup.quotientEquivOfEq h_stab)

private lemma finiteIndex_Gamma0_map_subgroupOf (N k : ℕ) [NeZero N] (hk : 0 < k) :
    (((CongruenceSubgroup.Gamma0 (k * N)).map (mapGL ℚ)).subgroupOf
      (Gamma0_pair N).H).FiniteIndex := by
  rw [← stab_diag_eq_Gamma0 N k hk]
  exact ⟨((Gamma0_pair N).h₁ (⟨diagMat 2 (![1, k] : Fin 2 → ℕ), diagMat_mem_Delta0_of_gcd N _
    (fun i ↦ by fin_cases i <;> simp [hk]) (by simp)⟩ : (Gamma0_pair N).Δ).2).1⟩

/-- **Gamma0 degree multiplicativity**: for coprime `m, n`,
`deg(diag(1,m)) * deg(diag(1,n)) = deg(diag(1,mn))` at the `Γ₀(N)` level, i.e.
`[Γ₀(N) : Γ₀(Nm)] * [Γ₀(N) : Γ₀(Nn)] = [Γ₀(N) : Γ₀(Nmn)]`. -/
lemma Gamma0_deg_coprime_mul (N : ℕ) [NeZero N]
    (m n : ℕ) (hm_pos : 0 < m) (hn_pos : 0 < n) (hcop : Nat.Coprime m n) :
    HeckeRing.HeckeCoset_deg (Gamma0_pair N)
      (T_diag_Gamma0 N (![1, m]) (fun i ↦ by fin_cases i <;> simp [hm_pos])
        (by simp)) *
    HeckeRing.HeckeCoset_deg (Gamma0_pair N)
      (T_diag_Gamma0 N (![1, n]) (fun i ↦ by fin_cases i <;> simp [hn_pos])
        (by simp)) =
    HeckeRing.HeckeCoset_deg (Gamma0_pair N)
      (T_diag_Gamma0 N (![1, m * n])
        (fun i ↦ by fin_cases i <;> simp [Nat.mul_pos hm_pos hn_pos])
        (by simp)) := by
  set g_m : (Gamma0_pair N).Δ := ⟨diagMat 2 (![1, m]),
    diagMat_mem_Delta0_of_gcd N _ (fun i ↦ by fin_cases i <;> simp [hm_pos]) (by simp)⟩
  set g_n : (Gamma0_pair N).Δ := ⟨diagMat 2 (![1, n]),
    diagMat_mem_Delta0_of_gcd N _ (fun i ↦ by fin_cases i <;> simp [hn_pos]) (by simp)⟩
  set g_mn : (Gamma0_pair N).Δ := ⟨diagMat 2 (![1, m * n]),
    diagMat_mem_Delta0_of_gcd N _ (fun i ↦ by fin_cases i <;> simp [Nat.mul_pos hm_pos hn_pos])
      (by simp)⟩
  show HeckeRing.HeckeCoset_deg _ ⟦g_m⟧ * HeckeRing.HeckeCoset_deg _ ⟦g_n⟧ =
    HeckeRing.HeckeCoset_deg _ ⟦g_mn⟧
  rw [HeckeCoset_deg_diagMat_eq_card_quotient N m hm_pos g_m rfl,
    HeckeCoset_deg_diagMat_eq_card_quotient N n hn_pos g_n rfl,
    HeckeCoset_deg_diagMat_eq_card_quotient N (m * n) (Nat.mul_pos hm_pos hn_pos) g_mn rfl]
  set H := (Gamma0_pair N).H
  set K_m := ((CongruenceSubgroup.Gamma0 (m * N)).map (mapGL ℚ)).subgroupOf H
  set K_n := ((CongruenceSubgroup.Gamma0 (n * N)).map (mapGL ℚ)).subgroupOf H
  set K_mn := ((CongruenceSubgroup.Gamma0 (m * n * N)).map (mapGL ℚ)).subgroupOf H
  have hN_pos : 0 < N := Nat.pos_of_neZero N
  haveI : NeZero (m * N) := ⟨by positivity⟩
  haveI : NeZero (n * N) := ⟨by positivity⟩
  haveI : NeZero (m * n * N) := ⟨by positivity⟩
  have h_inf : K_m ⊓ K_n = K_mn := by
    simp only [K_m, K_n, K_mn, Subgroup.subgroupOf, ← Subgroup.comap_inf]
    congr 1
    rw [← Subgroup.map_inf_eq (f := mapGL ℚ) (hf := mapGL_injective)]
    exact congrArg _ (Gamma0_inf_eq_of_coprime N m n hcop)
  haveI : K_m.FiniteIndex := finiteIndex_Gamma0_map_subgroupOf N m hm_pos
  haveI : K_n.FiniteIndex := finiteIndex_Gamma0_map_subgroupOf N n hn_pos
  haveI : (K_m ⊓ K_n).FiniteIndex :=
    h_inf ▸ finiteIndex_Gamma0_map_subgroupOf N (m * n) (Nat.mul_pos hm_pos hn_pos)
  rw [← h_inf]
  exact_mod_cast (card_quotient_inf_of_set_mul K_m K_n
    (Gamma0_H_factor_through_mN_nN N m n hm_pos hn_pos hcop)).symm

private lemma relIndex_conjAct_eq_of_mem_doubleCoset (α : GL (Fin 2) ℚ)
    (H : Subgroup (GL (Fin 2) ℚ)) (δ : GL (Fin 2) ℚ)
    (hδ : δ ∈ DoubleCoset.doubleCoset α (H : Set _) (H : Set _)) :
    (ConjAct.toConjAct δ • H).relIndex H = (ConjAct.toConjAct α • H).relIndex H := by
  rw [DoubleCoset.mem_doubleCoset] at hδ
  obtain ⟨σ₁, hσ₁, σ₂, hσ₂, hδ_eq⟩ := hδ
  have h_δ_smul : ConjAct.toConjAct δ • H =
      ConjAct.toConjAct σ₁ • (ConjAct.toConjAct α • H) := by
    rw [hδ_eq, map_mul, map_mul, ← smul_smul, ← smul_smul, conjAct_smul_elt_eq H ⟨σ₂, hσ₂⟩]
  rw [h_δ_smul]
  have := Subgroup.relIndex_pointwise_smul (ConjAct.toConjAct σ₁) (ConjAct.toConjAct α • H) H
  rw [conjAct_smul_elt_eq H ⟨σ₁, hσ₁⟩] at this; exact this

private lemma conjAct_scalar_diagMat_smul_eq (p : ℕ) (hp : 0 < p)
    (X : Subgroup (GL (Fin 2) ℚ)) :
    ConjAct.toConjAct (diagMat 2 (fun _ : Fin 2 ↦ p) : GL (Fin 2) ℚ) • X = X := by
  ext x; constructor
  · intro hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    simp only [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hx
    rwa [diagMat_scalar_conj_eq 2 p hp] at hx
  · intro hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
    rwa [diagMat_scalar_conj_eq 2 p hp]

private lemma HeckeCoset_deg_eq_relIndex_of_rep_mem_doubleCoset (N : ℕ) [NeZero N]
    (D : HeckeRing.HeckeCoset (Gamma0_pair N)) (α : GL (Fin 2) ℚ)
    (hD : (HeckeCoset.rep D : GL (Fin 2) ℚ) ∈ DoubleCoset.doubleCoset α
      ((Gamma0_pair N).H : Set _) ((Gamma0_pair N).H : Set _)) :
    (HeckeRing.HeckeCoset_deg (Gamma0_pair N) D : ℤ) =
    ((ConjAct.toConjAct α • (Gamma0_pair N).H).relIndex (Gamma0_pair N).H : ℕ) := by
  have h_def : HeckeRing.HeckeCoset_deg (Gamma0_pair N) D =
      ↑((ConjAct.toConjAct (HeckeCoset.rep D : GL (Fin 2) ℚ) • (Gamma0_pair N).H).relIndex
        (Gamma0_pair N).H) := by
    simp only [HeckeRing.HeckeCoset_deg, Subgroup.relIndex, Subgroup.index,
      ← Nat.card_eq_fintype_card]
  rw [h_def, relIndex_conjAct_eq_of_mem_doubleCoset α _ _ hD]

private lemma HeckeCoset_deg_Gamma0_one_k_eq_relIndex (N : ℕ) [NeZero N]
    (k : ℕ) (hk : 0 < k) :
    HeckeRing.HeckeCoset_deg (Gamma0_pair N)
      (T_diag_Gamma0 N (![1, k]) (fun i ↦ by fin_cases i <;> simp [hk])
        (by simp)) =
    ((CongruenceSubgroup.Gamma0 (k * N)).relIndex (CongruenceSubgroup.Gamma0 N) : ℤ) := by
  set D := T_diag_Gamma0 N (![1, k]) (fun i ↦ by fin_cases i <;> simp [hk]) (by simp)
  set α := (diagMat 2 (![1, k] : Fin 2 → ℕ) : GL (Fin 2) ℚ)
  set H := (Gamma0_pair N).H
  have hδ_mem : (HeckeCoset.rep D : GL (Fin 2) ℚ) ∈
      DoubleCoset.doubleCoset α (H : Set _) (H : Set _) := by
    have h1 : HeckeCoset.toSet D = DoubleCoset.doubleCoset α (H : Set _) (H : Set _) := by
      simp only [D, T_diag_Gamma0, HeckeCoset.toSet_mk]; rfl
    rw [← h1]; exact HeckeCoset.rep_mem D
  have h_relIndex_stab : (ConjAct.toConjAct α • H).relIndex H =
      ((CongruenceSubgroup.Gamma0 (k * N)).map (mapGL ℚ)).relIndex H := by
    unfold Subgroup.relIndex; rw [stab_diag_eq_Gamma0 N k hk]
  rw [HeckeCoset_deg_eq_relIndex_of_rep_mem_doubleCoset N D α hδ_mem, h_relIndex_stab,
    ← Subgroup.relIndex_map_map_of_injective (CongruenceSubgroup.Gamma0 (k * N))
      (CongruenceSubgroup.Gamma0 N) (f := mapGL ℚ) mapGL_injective]
  rfl

private lemma Gamma0_relIndex_eq_Gamma_index_of_coprime (N : ℕ) [NeZero N]
    (m : ℕ) (hm_pos : 0 < m) (hcop : Nat.Coprime m N) :
    (CongruenceSubgroup.Gamma0 (m * N)).relIndex (CongruenceSubgroup.Gamma0 N) =
    (CongruenceSubgroup.Gamma0 m).index := by
  have hN_pos : 0 < N := Nat.pos_of_neZero N
  have h_deg_level1 := Gamma0_deg_coprime_mul 1 m N hm_pos hN_pos hcop
  have h_bridge_m := HeckeCoset_deg_Gamma0_one_k_eq_relIndex 1 m hm_pos
  have h_bridge_N := HeckeCoset_deg_Gamma0_one_k_eq_relIndex 1 N hN_pos
  have h_bridge_mN := HeckeCoset_deg_Gamma0_one_k_eq_relIndex 1 (m * N)
    (Nat.mul_pos hm_pos hN_pos)
  have hGamma0_one : CongruenceSubgroup.Gamma0 1 = (⊤ : Subgroup SL(2, ℤ)) := by
    ext g; simpa [CongruenceSubgroup.Gamma0_mem] using Subsingleton.elim _ _
  have h_relIndex_to_index : ∀ (k : ℕ),
      (CongruenceSubgroup.Gamma0 (k * 1)).relIndex (CongruenceSubgroup.Gamma0 1) =
      (CongruenceSubgroup.Gamma0 k).index := fun k ↦ by
    rw [Nat.mul_one, hGamma0_one, Subgroup.relIndex_top_right]
  rw [h_relIndex_to_index m] at h_bridge_m
  rw [h_relIndex_to_index N] at h_bridge_N
  rw [h_relIndex_to_index (m * N)] at h_bridge_mN
  rw [h_bridge_m, h_bridge_N, h_bridge_mN] at h_deg_level1
  have h_tower : (CongruenceSubgroup.Gamma0 (m * N)).relIndex (CongruenceSubgroup.Gamma0 N) *
      (CongruenceSubgroup.Gamma0 N).index = (CongruenceSubgroup.Gamma0 (m * N)).index :=
    Subgroup.relIndex_mul_index (Gamma0_le_of_dvd (Nat.dvd_mul_left N m))
  have hN_pos_index : 0 < (CongruenceSubgroup.Gamma0 N).index :=
    Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  refine (mul_right_cancel_iff_of_pos hN_pos_index).mp ?_
  rw [h_tower]; exact_mod_cast h_deg_level1.symm

/-- **Degree formula for `T'(1, p^k)` at the `Γ₀(N)` level**: for a prime `p` coprime
to `N` and `k ≥ 1`, `deg_{Γ₀(N)}(T'(1, p^k)) = p^(k-1) · (p + 1)`. -/
lemma HeckeCoset_deg_Gamma0_one_ppow (N : ℕ) [NeZero N]
    (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N) (k : ℕ) (hk : 0 < k) :
    HeckeRing.HeckeCoset_deg (Gamma0_pair N)
      (T_diag_Gamma0 N (![1, p^k])
        (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
        (by simp)) =
    ((p ^ (k - 1) * (p + 1) : ℕ) : ℤ) := by
  rw [HeckeCoset_deg_Gamma0_one_k_eq_relIndex N (p^k) (pow_pos hp.pos k),
    Gamma0_relIndex_eq_Gamma_index_of_coprime N (p^k) (pow_pos hp.pos k) (hpN.pow_left k),
    HeckeRing.GL2.Gamma0_prime_power_index p hp k hk]

private lemma diagMat_two_one_one_eq_one :
    (diagMat 2 (![1, 1] : Fin 2 → ℕ) : GL (Fin 2) ℚ) = 1 := by
  apply Units.ext
  ext i j
  rw [diagMat_val 2 (![1, 1] : Fin 2 → ℕ) (fun i ↦ by fin_cases i <;> simp), Units.val_one]
  fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

private lemma diagMat_p_ppow_eq_scalar_mul_diag (p k : ℕ) (hp : 0 < p) (hk : 1 ≤ k) :
    (diagMat 2 (![p, p^k] : Fin 2 → ℕ) : GL (Fin 2) ℚ) =
    (diagMat 2 (fun _ : Fin 2 ↦ p) : GL (Fin 2) ℚ) *
      (diagMat 2 (![1, p^(k-1)] : Fin 2 → ℕ) : GL (Fin 2) ℚ) := by
  apply Units.ext
  simp only [Units.val_mul]
  rw [diagMat_val 2 (![p, p^k] : Fin 2 → ℕ) (fun i ↦ by fin_cases i <;> simp [hp, pow_pos hp]),
      diagMat_val 2 (fun _ : Fin 2 ↦ p) (fun _ ↦ hp),
      diagMat_val 2 (![1, p^(k-1)] : Fin 2 → ℕ) (fun i ↦ by fin_cases i <;> simp [pow_pos hp])]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]
  have hpk : (p : ℚ) ^ k = (p : ℚ) * (p : ℚ) ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  fin_cases i <;> fin_cases j <;> push_cast <;> simp [hpk]

/-- **Degree formula for `T'(p, p^k)` at the `Γ₀(N)` level**: for a prime `p` coprime
to `N` and `k ≥ 1`, `deg_{Γ₀(N)}(T'(p, p^k))` is `1` when `k = 1` and
`p^(k-2) · (p + 1)` when `k ≥ 2`. -/
lemma HeckeCoset_deg_Gamma0_p_ppow (N : ℕ) [NeZero N]
    (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N) (k : ℕ) (hk : 1 ≤ k) :
    HeckeRing.HeckeCoset_deg (Gamma0_pair N)
      (T_diag_Gamma0 N (![p, p^k])
        (fun i ↦ by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
        (by show Int.gcd (↑p) ↑N = 1
            rw [Int.gcd_natCast_natCast]; exact hpN)) =
    (if k = 1 then (1 : ℤ) else ((p^(k-2) * (p + 1) : ℕ) : ℤ)) := by
  set D := T_diag_Gamma0 N (![p, p^k])
    (fun i ↦ by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
    (by show Int.gcd (↑p) ↑N = 1; rw [Int.gcd_natCast_natCast]; exact hpN)
  set δ := (HeckeCoset.rep D : GL (Fin 2) ℚ) with hδ_def
  set α : GL (Fin 2) ℚ := diagMat 2 (![p, p^k] : Fin 2 → ℕ)
  set α_sc : GL (Fin 2) ℚ := diagMat 2 (fun _ : Fin 2 ↦ p)
  set α_diag : GL (Fin 2) ℚ := diagMat 2 (![1, p^(k-1)] : Fin 2 → ℕ)
  set H := (Gamma0_pair N).H
  have hδ_mem : δ ∈ DoubleCoset.doubleCoset α (↑H : Set _) (↑H : Set _) := by
    have h_set : HeckeCoset.toSet D = DoubleCoset.doubleCoset α (↑H : Set _) (↑H : Set _) := by
      simp only [D, T_diag_Gamma0, HeckeCoset.toSet_mk, α]; rfl
    rw [← h_set]; exact HeckeCoset.rep_mem D
  have hα_factor : α = α_sc * α_diag := diagMat_p_ppow_eq_scalar_mul_diag p k hp.pos hk
  have h_conj_eq : ConjAct.toConjAct α • H = ConjAct.toConjAct α_diag • H := by
    rw [hα_factor, map_mul, ← smul_smul, conjAct_scalar_diagMat_smul_eq p hp.pos]
  rw [HeckeCoset_deg_eq_relIndex_of_rep_mem_doubleCoset N D α hδ_mem, h_conj_eq]
  by_cases hk1 : k = 1
  · subst hk1
    have h_α_diag_one : α_diag = (1 : GL (Fin 2) ℚ) := by
      simpa [α_diag, show (1 : ℕ) - 1 = 0 from rfl] using diagMat_two_one_one_eq_one
    rw [if_pos rfl, h_α_diag_one, ConjAct.toConjAct_one, one_smul, Subgroup.relIndex_self]
    simp
  · set D' := T_diag_Gamma0 N (![1, p ^ (k-1)])
      (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos]) (by simp)
    have hδ'_mem : (HeckeCoset.rep D' : GL (Fin 2) ℚ) ∈
        DoubleCoset.doubleCoset α_diag (↑H : Set _) (↑H : Set _) := by
      have h_set : HeckeCoset.toSet D' =
          DoubleCoset.doubleCoset α_diag (↑H : Set _) (↑H : Set _) := by
        simp only [D', T_diag_Gamma0, HeckeCoset.toSet_mk, α_diag]; rfl
      rw [← h_set]; exact HeckeCoset.rep_mem D'
    rw [if_neg hk1, ← HeckeCoset_deg_eq_relIndex_of_rep_mem_doubleCoset N D' α_diag hδ'_mem,
      HeckeCoset_deg_Gamma0_one_ppow N p hp hpN (k - 1) (by omega),
      show k - 1 - 1 = k - 2 from by omega]

end HeckeRing.GLn

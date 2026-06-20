/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.CongruenceHecke.DegreeCombinatorics

/-!
# Hecke Ring for Congruence Subgroups (Shimura §3.3) — Surjectivity (Theorem 3.35)

This file assembles the surjective ring homomorphism `R(Γ, Δ) ↠ R(Γ₀(N), Δ₀(N))`
from coprime/bad-prime multiplicativity, algebraic independence of the generators,
and the `ψ`-range computations.

## Main results

* `shimura_thm_3_35` — the surjection `R(Γ, Δ) →+* R(Γ₀(N), Δ₀(N))`

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.3
-/

open Matrix Subgroup.Commensurable Pointwise Matrix.SpecialLinearGroup

open scoped Pointwise MatrixGroups

namespace HeckeRing.GLn

variable (N : ℕ) [NeZero N]

private lemma T_diag_Gamma0_congr {a b : Fin 2 → ℕ}
    (ha : ∀ i, 0 < a i) (hga : Int.gcd (a 0) N = 1)
    (hb : ∀ i, 0 < b i) (hgb : Int.gcd (b 0) N = 1) (hab : a = b) :
    T_diag_Gamma0 N a ha hga = T_diag_Gamma0 N b hb hgb := by
  subst hab; rfl

private theorem T_coprime_mul (N : ℕ) [NeZero N]
    (m n : ℕ) (hm_pos : 0 < m) (hn_pos : 0 < n) (hcop : Nat.Coprime m n) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, m])
        (fun i ↦ by fin_cases i <;> simp [hm_pos]) (by simp)) 1 *
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, n])
        (fun i ↦ by fin_cases i <;> simp [hn_pos]) (by simp)) 1 =
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, m * n])
        (fun i ↦ by fin_cases i <;> simp [Nat.mul_pos hm_pos hn_pos])
        (by simp)) 1 := by
  refine HeckeRing.T_single_one_mul_eq_single (Gamma0_pair N) _ _ _ (by
    set D₁ := T_diag_Gamma0 N (![1, m]) (fun i ↦ by fin_cases i <;> simp [hm_pos])
      (by simp)
    set D₂ := T_diag_Gamma0 N (![1, n]) (fun i ↦ by fin_cases i <;> simp [hn_pos])
      (by simp)
    set D_out := T_diag_Gamma0 N (![1, m * n])
      (fun i ↦ by fin_cases i <;> simp [Nat.mul_pos hm_pos hn_pos])
      (by simp)
    set μ := HeckeRing.heckeMultiplicity (Gamma0_pair N) D₁.rep D₂.rep D_out.rep
    have h_mulMap : ∀ p, HeckeRing.mulMap (Gamma0_pair N) D₁.rep D₂.rep p = D_out :=
      mulMap_Gamma0_coprime_eq N m n hm_pos hn_pos hcop
    have h_zero_all : ∀ A, A ≠ D_out →
        (HeckeRing.m (Gamma0_pair N) D₁.rep D₂.rep) A = 0 := by
      intro A hA; simp only [HeckeRing.m_apply]
      exact HeckeRing.heckeMultiplicity_eq_zero_of_mulMap_unique
        (Gamma0_pair N) _ _ D_out A hA h_mulMap
    have h_m_eq : HeckeRing.m (Gamma0_pair N) D₁.rep D₂.rep =
        Finsupp.single D_out μ := by
      ext A; simp only [Finsupp.single_apply]
      split_ifs with h
      · subst h; simp only [HeckeRing.m_apply]; rfl
      · exact h_zero_all A (Ne.symm h)
    have h_deg_mul := Gamma0_deg_coprime_mul N m n hm_pos hn_pos hcop
    have h_deg_prod : HeckeRing.deg (Gamma0_pair N)
        (HeckeRing.T_single _ ℤ D₁ 1 * HeckeRing.T_single _ ℤ D₂ 1) =
        HeckeRing.HeckeCoset_deg (Gamma0_pair N) D_out := by
      rw [HeckeRing.deg_mul, HeckeRing.deg_T_single, HeckeRing.deg_T_single,
        one_mul, one_mul, h_deg_mul]
    have h_deg_m_eq : HeckeRing.deg (Gamma0_pair N)
        (HeckeRing.m (Gamma0_pair N) D₁.rep D₂.rep) =
        μ * HeckeRing.HeckeCoset_deg (Gamma0_pair N) D_out := by
      rw [h_m_eq]; simp [HeckeRing.deg_T_single]
    rw [HeckeRing.T_single_one_mul_T_single_one] at h_deg_prod
    have hd_out_ne : HeckeRing.HeckeCoset_deg (Gamma0_pair N) D_out ≠ 0 :=
      (HeckeRing.HeckeCoset_deg_pos (Gamma0_pair N) D_out).ne'
    exact mul_right_cancel₀ hd_out_ne (by linarith [h_deg_prod, h_deg_m_eq])) ?_
  · intro A hA
    exact HeckeRing.heckeMultiplicity_eq_zero_of_mulMap_unique (Gamma0_pair N) _ _ _ A hA
      (mulMap_Gamma0_coprime_eq N m n hm_pos hn_pos hcop)

private lemma coprime_mul_m_coeff_indicator (f g : HeckeAlgebra 2) (d₁ d₂ : Fin 2 → ℕ)
    (hd₁_pos : ∀ i, 0 < d₁ i) (hd₂_pos : ∀ i, 0 < d₂ i)
    (hd₁_div : DivChain 2 d₁) (hd₂_div : DivChain 2 d₂)
    (hcop_pair : ∀ D₁ D₂ a b, f D₁ ≠ 0 → g D₂ ≠ 0 →
      D₁ = T_diag a → D₂ = T_diag b →
      (∀ i, 0 < a i) → (∀ i, 0 < b i) → DivChain 2 a → DivChain 2 b →
      Nat.Coprime (∏ i, a i) (∏ i, b i))
    (huniq : ∀ D₁ D₂ a b, f D₁ ≠ 0 → g D₂ ≠ 0 →
      D₁ = T_diag a → D₂ = T_diag b →
      (∀ i, 0 < a i) → (∀ i, 0 < b i) → DivChain 2 a → DivChain 2 b →
      Nat.Coprime (∏ i, a i) (∏ i, b i) →
      T_diag (a * b) = T_diag (d₁ * d₂) → a = d₁ ∧ b = d₂)
    (hf_diag : ∀ D, f D ≠ 0 → ∃ a, D = T_diag a ∧ (∀ i, 0 < a i) ∧ DivChain 2 a)
    (hg_diag : ∀ D, g D ≠ 0 → ∃ b, D = T_diag b ∧ (∀ i, 0 < b i) ∧ DivChain 2 b)
    (D₁ D₂ : HeckeCoset (GL_pair 2)) (hD₁ : f D₁ ≠ 0) (hD₂ : g D₂ ≠ 0) :
    (HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) (T_diag (d₁ * d₂)) =
    if D₁ = T_diag d₁ ∧ D₂ = T_diag d₂ then 1 else 0 := by
  obtain ⟨a, rfl, ha_pos, ha_div⟩ := hf_diag D₁ hD₁
  obtain ⟨b, rfl, hb_pos, hb_div⟩ := hg_diag D₂ hD₂
  have hcop_ab := hcop_pair _ _ a b hD₁ hD₂ rfl rfl ha_pos hb_pos ha_div hb_div
  have hm_eq : HeckeRing.m (GL_pair 2) (HeckeCoset.rep (T_diag a))
      (HeckeCoset.rep (T_diag b)) = Finsupp.single (T_diag (a * b)) 1 := by
    rw [← HeckeRing.T_single_one_mul_T_single_one]
    exact T_diag_mul_coprime 2 a b ha_pos hb_pos ha_div hb_div hcop_ab
  rw [hm_eq, Finsupp.single_apply]
  congr 1; apply propext
  exact ⟨fun h ↦ by
      have ⟨ha, hb⟩ := huniq _ _ a b hD₁ hD₂ rfl rfl ha_pos hb_pos ha_div hb_div hcop_ab h
      exact ⟨congr_arg T_diag ha, congr_arg T_diag hb⟩,
    fun ⟨ha, hb⟩ ↦ by
      rw [diagonal_representative_unique 2 a d₁ ha_pos hd₁_pos ha_div hd₁_div ha,
          diagonal_representative_unique 2 b d₂ hb_pos hd₂_pos hb_div hd₂_div hb]⟩

private lemma coprime_mul_coeff (f g : HeckeAlgebra 2)
    (d₁ d₂ : Fin 2 → ℕ)
    (hd₁_pos : ∀ i, 0 < d₁ i) (hd₂_pos : ∀ i, 0 < d₂ i)
    (hd₁_div : DivChain 2 d₁) (hd₂_div : DivChain 2 d₂)
    (hf_diag : ∀ D, f D ≠ 0 → ∃ a, D = T_diag a ∧ (∀ i, 0 < a i) ∧ DivChain 2 a)
    (hg_diag : ∀ D, g D ≠ 0 → ∃ b, D = T_diag b ∧ (∀ i, 0 < b i) ∧ DivChain 2 b)
    (hcop_pair : ∀ D₁ D₂ a b, f D₁ ≠ 0 → g D₂ ≠ 0 →
      D₁ = T_diag a → D₂ = T_diag b →
      (∀ i, 0 < a i) → (∀ i, 0 < b i) → DivChain 2 a → DivChain 2 b →
      Nat.Coprime (∏ i, a i) (∏ i, b i))
    (huniq : ∀ D₁ D₂ a b, f D₁ ≠ 0 → g D₂ ≠ 0 →
      D₁ = T_diag a → D₂ = T_diag b →
      (∀ i, 0 < a i) → (∀ i, 0 < b i) → DivChain 2 a → DivChain 2 b →
      Nat.Coprime (∏ i, a i) (∏ i, b i) →
      T_diag (a * b) = T_diag (d₁ * d₂) → a = d₁ ∧ b = d₂) :
    (f * g) (T_diag (d₁ * d₂)) = f (T_diag d₁) * g (T_diag d₂) := by
  set D := T_diag (d₁ * d₂) with hD_def
  have hm_delta : ∀ D₁ D₂ : HeckeCoset (GL_pair 2),
      f D₁ ≠ 0 → g D₂ ≠ 0 →
      (HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) D =
      if D₁ = T_diag d₁ ∧ D₂ = T_diag d₂ then 1 else 0 := fun D₁ D₂ hD₁ hD₂ ↦
    hD_def.symm ▸ coprime_mul_m_coeff_indicator f g d₁ d₂ hd₁_pos hd₂_pos hd₁_div hd₂_div
      hcop_pair huniq hf_diag hg_diag D₁ D₂ hD₁ hD₂
  have h_expand : (f * g) D = ∑ D₁ ∈ f.support, ∑ D₂ ∈ g.support,
      f D₁ * g D₂ * (HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂)) D := by
    show (Finsupp.sum f (fun D₁ b₁ ↦ Finsupp.sum g (fun D₂ b₂ ↦
      b₁ • b₂ • HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂)))) D = _
    simp only [Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul, mul_assoc]
    rfl
  rw [h_expand]
  conv_lhs =>
    arg 2; ext D₁; arg 2; ext D₂
    rw [show f D₁ * g D₂ * (HeckeRing.m (GL_pair 2) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂)) D =
        if D₁ = T_diag d₁ ∧ D₂ = T_diag d₂ then f D₁ * g D₂ else 0 by
      by_cases hD₁ : f D₁ = 0
      · simp [hD₁]
      · by_cases hD₂ : g D₂ = 0
        · simp [hD₂]
        · rw [hm_delta D₁ D₂ hD₁ hD₂, mul_ite, mul_one, mul_zero]]
  have h_inner : ∀ D₁ ∈ f.support, (∑ D₂ ∈ g.support,
      if D₁ = T_diag d₁ ∧ D₂ = T_diag d₂ then f D₁ * g D₂ else 0) =
      if D₁ = T_diag d₁ then f D₁ * g (T_diag d₂) else 0 := by
    intro D₁ _
    by_cases h : D₁ = T_diag d₁
    · subst h; simp only [true_and]
      rw [Finset.sum_ite_eq']; split_ifs with hm
      · rfl
      · have h_zero : g (T_diag d₂) = 0 := Finsupp.notMem_support_iff.mp hm
        rw [h_zero, mul_zero]
    · simp [h]
  rw [Finset.sum_congr rfl h_inner, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · have h_zero : f (T_diag d₁) = 0 := Finsupp.notMem_support_iff.mp hm
    rw [h_zero, zero_mul]

open HeckeRing.GLn.Inj
  (T_gen_pow_support_qpower T_gen_pow_entries_qpower support_mul_exists
   det_SLnZ_eq_one det_doubleCoset_eq prod_rep_T_diag det_mulMap_eq)

private lemma support_det_mul (f g : HeckeAlgebra 2) (d₁ d₂ : ℚ)
    (hf : ∀ D, f D ≠ 0 →
      (↑(↑(HeckeCoset.rep D) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = d₁)
    (hg : ∀ D, g D ≠ 0 →
      (↑(↑(HeckeCoset.rep D) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = d₂)
    (D : HeckeCoset (GL_pair 2)) (hD : (f * g) D ≠ 0) :
    (↑(↑(HeckeCoset.rep D) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = d₁ * d₂ := by
  obtain ⟨D₁, D₂, hfD₁, hgD₂, hD_mem⟩ := support_mul_exists f g D hD
  rw [HeckeRing.mulSupport, Finset.mem_image] at hD_mem
  obtain ⟨p, _, hD_eq⟩ := hD_mem
  rw [← hD_eq, det_mulMap_eq, hf D₁ hfD₁, hg D₂ hgD₂]

private lemma prod_gen_det_eq (S : Finset {p : ℕ // p.Prime})
    (e : {p : ℕ // p.Prime} → Fin 2 → ℕ) :
    ∀ D : HeckeCoset (GL_pair 2),
    (∏ p ∈ S, (T_gen 2 p.1 0 ^ (e p 0) * T_gen 2 p.1 1 ^ (e p 1))) D ≠ 0 →
    (↑(↑(HeckeCoset.rep D) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
    ↑(∏ p ∈ S, p.1 ^ (e p 0 + 2 * e p 1) : ℕ) := by
  induction S using Finset.induction with
  | empty =>
    intro D hD
    simp only [Finset.prod_empty] at hD ⊢
    have hD' : (HeckeRing.T_single (GL_pair 2) ℤ (HeckeCoset.one (GL_pair 2)) 1) D ≠ 0 := by
      change (1 : HeckeAlgebra 2) D ≠ 0
      exact hD
    have hD_eq : D = HeckeCoset.one (GL_pair 2) := by
      by_contra hne
      apply hD'
      show (Finsupp.single (HeckeCoset.one (GL_pair 2)) 1) D = 0
      rw [Finsupp.single_apply, if_neg (Ne.symm hne)]
    rw [hD_eq, show (HeckeCoset.one (GL_pair 2) : HeckeCoset (GL_pair 2)) =
      T_diag (fun _ : Fin 2 ↦ 1) from T_diag_ones.symm,
      prod_rep_T_diag _ (fun _ ↦ Nat.one_pos)]
    simp
  | @insert q' S'' hq'' ih =>
    intro D hD
    rw [Finset.prod_insert hq''] at hD
    have h := support_det_mul _ _
      (↑(q'.1 ^ (e q' 0 + 2 * e q' 1) : ℕ) : ℚ)
      (↑(∏ p ∈ S'', p.1 ^ (e p 0 + 2 * e p 1) : ℕ) : ℚ)
      (fun D' hD' ↦ by
        obtain ⟨a, hDa, ha_pos, _, ha_det⟩ := T_gen_pow_support_qpower q' (e q') D' hD'
        rw [hDa, prod_rep_T_diag a ha_pos]
        exact_mod_cast ha_det)
      (fun D' hD' ↦ ih D' hD')
      D hD
    rw [h]; push_cast [Finset.prod_insert hq'']; ring

private lemma prod_gen_support_det (S : Finset {p : ℕ // p.Prime})
    (e : {p : ℕ // p.Prime} → Fin 2 → ℕ) (D : HeckeCoset (GL_pair 2))
    (hD : (∏ p ∈ S, (T_gen 2 p.1 0 ^ (e p 0) * T_gen 2 p.1 1 ^ (e p 1))) D ≠ 0) :
    ∃ a, D = T_diag a ∧ (∀ i, 0 < a i) ∧ DivChain 2 a ∧
      (∏ i, a i) = ∏ p ∈ S, p.1 ^ (e p 0 + 2 * e p 1) := by
  obtain ⟨a, ha_pos, ha_div, ha_eq⟩ := exists_diagonal_representative 2 (HeckeCoset.rep D)
  have hD_eq : D = T_diag a := by rw [← Quotient.out_eq D]; exact ha_eq
  refine ⟨a, hD_eq, ha_pos, ha_div, ?_⟩
  have h_det := prod_gen_det_eq S e D hD
  rw [hD_eq, prod_rep_T_diag a ha_pos] at h_det
  exact_mod_cast h_det

private lemma prod_ppowDiag_pos (S : Finset {p : ℕ // p.Prime})
    (v : {p : ℕ // p.Prime} → Fin 2 → ℕ) (i : Fin 2) :
    0 < (∏ p ∈ S, ppowDiag 2 p.1 (v p)) i := by
  simpa only [Finset.prod_apply] using
    Finset.prod_pos (fun (p : {p : ℕ // p.Prime}) _ ↦ ppowDiag_pos 2 p.1 p.2 _ i)

private lemma prod_ppowDiag_divChain (S : Finset {p : ℕ // p.Prime})
    (v : {p : ℕ // p.Prime} → Fin 2 → ℕ) (hmono : ∀ p, Monotone (v p)) :
    DivChain 2 (∏ p ∈ S, ppowDiag 2 p.1 (v p)) :=
  Finset.prod_induction _ (DivChain 2) (DivChain_mul 2)
    (fun _ _ ↦ dvd_refl 1) (fun (p : {p : ℕ // p.Prime}) _ ↦ divChain_ppow 2 p.1 _ (hmono p))

private lemma eq_of_mul_eq_mul_coprime_cross {a b c d : ℕ} (h : a * b = c * d)
    (hac : Nat.Coprime a d) (hcb : Nat.Coprime c b) : a = c :=
  Nat.dvd_antisymm
    (Nat.Coprime.dvd_of_dvd_mul_right hac (h ▸ dvd_mul_right _ _))
    (Nat.Coprime.dvd_of_dvd_mul_right hcb (h.symm ▸ dvd_mul_right _ _))

private lemma monotone_cons_le {a b : ℕ} (h : a ≤ b) : Monotone (![a, b] : Fin 2 → ℕ) := by
  intro i j hij; fin_cases i <;> fin_cases j <;> simp_all

private lemma multi_prime_step_coprime (q : {p : ℕ // p.Prime})
    (S' : Finset {p : ℕ // p.Prime}) (hq : q ∉ S') (e : {p : ℕ // p.Prime} → Fin 2 → ℕ)
    (D₁ D₂ : HeckeCoset (GL_pair 2)) (a b : Fin 2 → ℕ)
    (hfD₁ : (T_gen 2 q.1 0 ^ (e q 0) * T_gen 2 q.1 1 ^ (e q 1)) D₁ ≠ 0)
    (hgD₂ : (∏ p ∈ S', T_gen 2 p.1 0 ^ (e p 0) * T_gen 2 p.1 1 ^ (e p 1)) D₂ ≠ 0)
    (hD₁_eq : D₁ = T_diag a) (hD₂_eq : D₂ = T_diag b)
    (ha_pos : ∀ i, 0 < a i) (hb_pos : ∀ i, 0 < b i)
    (ha_div : DivChain 2 a) (hb_div : DivChain 2 b) :
    Nat.Coprime (∏ i, a i) (∏ i, b i) := by
  obtain ⟨a', hDa'_eq, ha'_pos, ha'_div, ha'_det⟩ := T_gen_pow_support_qpower q (e q) D₁ hfD₁
  have ha_eq : a = a' := diagonal_representative_unique 2 a a' ha_pos ha'_pos ha_div ha'_div
    (hD₁_eq ▸ hDa'_eq)
  subst ha_eq; rw [ha'_det]
  obtain ⟨b', hDb', hb'_pos, hb'_div, hb'_det⟩ := prod_gen_support_det S' e D₂ hgD₂
  have hb_eq : b = b' := diagonal_representative_unique 2 b b' hb_pos hb'_pos hb_div hb'_div
    (hD₂_eq ▸ hDb')
  subst hb_eq; rw [hb'_det]
  apply Nat.Coprime.pow_left
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  apply Nat.Coprime.pow_right
  exact (Nat.coprime_primes q.2 p.2).mpr (fun h ↦ hq (by rw [Subtype.ext h]; exact hp))

private lemma multi_prime_step_uniq (q : {p : ℕ // p.Prime})
    (S' : Finset {p : ℕ // p.Prime}) (hq : q ∉ S') (e d : {p : ℕ // p.Prime} → Fin 2 → ℕ)
    (D₁ D₂ : HeckeCoset (GL_pair 2)) (a b : Fin 2 → ℕ)
    (hfD₁ : (T_gen 2 q.1 0 ^ (e q 0) * T_gen 2 q.1 1 ^ (e q 1)) D₁ ≠ 0)
    (hgD₂ : (∏ p ∈ S', T_gen 2 p.1 0 ^ (e p 0) * T_gen 2 p.1 1 ^ (e p 1)) D₂ ≠ 0)
    (hD₁_eq : D₁ = T_diag a) (hD₂_eq : D₂ = T_diag b)
    (ha_pos : ∀ i, 0 < a i) (hb_pos : ∀ i, 0 < b i)
    (ha_div : DivChain 2 a) (hb_div : DivChain 2 b)
    (h_eq : T_diag (a * b) = T_diag (ppowDiag 2 q.1 ![d q 1, d q 0 + d q 1] *
      ∏ p ∈ S', ppowDiag 2 p.1 ![d p 1, d p 0 + d p 1])) :
    a = ppowDiag 2 q.1 ![d q 1, d q 0 + d q 1] ∧
      b = ∏ p ∈ S', ppowDiag 2 p.1 ![d p 1, d p 0 + d p 1] := by
  set d₁ := ppowDiag 2 q.1 ![d q 1, d q 0 + d q 1]
  set d₂ := ∏ p ∈ S', ppowDiag 2 p.1 ![d p 1, d p 0 + d p 1]
  have hab := diagonal_representative_unique 2 (a * b) (d₁ * d₂)
    (pi_mul_pos 2 a b ha_pos hb_pos)
    (pi_mul_pos 2 d₁ d₂ (ppowDiag_pos 2 q.1 q.2 _) (prod_ppowDiag_pos S' _))
    (DivChain_mul 2 a b ha_div hb_div)
    (DivChain_mul 2 d₁ d₂ (divChain_ppow 2 q.1 _ (monotone_cons_le (by omega)))
      (prod_ppowDiag_divChain S' _ (fun _ ↦ monotone_cons_le (by omega))))
    h_eq
  have ha_qpow := T_gen_pow_entries_qpower q (e q) D₁ hfD₁ a hD₁_eq ha_pos ha_div
  obtain ⟨b', hDb'_eq, hb'_pos, hb'_div, hb'_det⟩ := prod_gen_support_det S' e D₂ hgD₂
  have hb_eq' : b = b' := diagonal_representative_unique 2 b b' hb_pos hb'_pos hb_div hb'_div
    (hD₂_eq ▸ hDb'_eq)
  subst hb_eq'
  have hcop_q_S'_prod : Nat.Coprime q.1 (∏ p ∈ S', p.1 ^ (e p 0 + 2 * e p 1)) :=
    Nat.coprime_prod_right_iff.mpr fun p hp ↦ Nat.Coprime.pow_right _
      ((Nat.coprime_primes q.2 p.2).mpr
        (fun h_eq_p ↦ hq (by rw [show q = p from Subtype.ext h_eq_p]; exact hp)))
  have hi_all : ∀ i, a i * b i = d₁ i * d₂ i :=
    fun i ↦ by simpa only [Pi.mul_apply] using congr_fun hab i
  have entry_eq : ∀ i, a i = d₁ i := by
    intro i
    have hq_not_dvd_b : ¬(q.1 ∣ b i) := fun hdvd ↦
      (Nat.Prime.coprime_iff_not_dvd q.2).mp hcop_q_S'_prod
        (hb'_det ▸ dvd_trans hdvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
    have hq_not_dvd_d₂ : ¬(q.1 ∣ d₂ i) := by
      intro hdvd
      change q.1 ∣ (∏ p ∈ S', ppowDiag 2 p.1 ![d p 1, d p 0 + d p 1]) i at hdvd
      rw [Finset.prod_apply] at hdvd
      rcases (q.2.prime.dvd_finsetProd_iff _).mp hdvd with ⟨p, hp_mem, hp_dvd⟩
      simp only [ppowDiag] at hp_dvd
      exact hq (Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp
        (q.2.dvd_of_dvd_pow hp_dvd)) ▸ hp_mem)
    have hcop_a_d₂ : Nat.Coprime (a i) (d₂ i) := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hne
      by_cases hpq : p = q.1
      · exact hq_not_dvd_d₂ (hpq ▸ dvd_trans hp_dvd (Nat.gcd_dvd_right _ _))
      · exact ha_qpow p hp_prime hpq i (dvd_trans hp_dvd (Nat.gcd_dvd_left _ _))
    have hcop_d₁_b : Nat.Coprime (d₁ i) (b i) := by
      show Nat.Coprime (ppowDiag 2 q.1 ![d q 1, d q 0 + d q 1] i) (b i)
      simp only [ppowDiag]
      exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd q.2).mpr hq_not_dvd_b)
    exact eq_of_mul_eq_mul_coprime_cross (hi_all i) hcop_a_d₂ hcop_d₁_b
  exact ⟨funext entry_eq, funext fun i ↦
    Nat.eq_of_mul_eq_mul_left (ha_pos i) (entry_eq i ▸ hi_all i)⟩

private lemma multi_prime_factor_step (q : {p : ℕ // p.Prime})
    (S' : Finset {p : ℕ // p.Prime}) (hq : q ∉ S')
    (e d : {p : ℕ // p.Prime} → Fin 2 → ℕ) :
    ((T_gen 2 q.1 0 ^ (e q 0) * T_gen 2 q.1 1 ^ (e q 1)) *
      ∏ p ∈ S', T_gen 2 p.1 0 ^ (e p 0) * T_gen 2 p.1 1 ^ (e p 1))
      (T_diag (ppowDiag 2 q.1 ![d q 1, d q 0 + d q 1] *
        ∏ p ∈ S', ppowDiag 2 p.1 ![d p 1, d p 0 + d p 1])) =
    (T_gen 2 q.1 0 ^ (e q 0) * T_gen 2 q.1 1 ^ (e q 1))
      (T_diag (ppowDiag 2 q.1 ![d q 1, d q 0 + d q 1])) *
    (∏ p ∈ S', T_gen 2 p.1 0 ^ (e p 0) * T_gen 2 p.1 1 ^ (e p 1))
      (T_diag (∏ p ∈ S', ppowDiag 2 p.1 ![d p 1, d p 0 + d p 1])) := by
  have h_diag_of_support : ∀ D : HeckeCoset (GL_pair 2),
      ∃ a, D = T_diag a ∧ (∀ i, 0 < a i) ∧ DivChain 2 a := fun D ↦ by
    obtain ⟨a, ha_pos, ha_div, ha_eq⟩ := exists_diagonal_representative 2 (HeckeCoset.rep D)
    exact ⟨a, by rw [← Quotient.out_eq D]; exact ha_eq, ha_pos, ha_div⟩
  exact coprime_mul_coeff _ _ _ _
    (ppowDiag_pos 2 q.1 q.2 _) (prod_ppowDiag_pos S' _)
    (divChain_ppow 2 q.1 _ (monotone_cons_le (by omega)))
    (prod_ppowDiag_divChain S' _ (fun _ ↦ monotone_cons_le (by omega)))
    (fun D _ ↦ h_diag_of_support D) (fun D _ ↦ h_diag_of_support D)
    (fun D₁ D₂ a b hfD₁ hgD₂ ↦ multi_prime_step_coprime q S' hq e D₁ D₂ a b hfD₁ hgD₂)
    (fun D₁ D₂ a b hfD₁ hgD₂ hD₁ hD₂ hap hbp had hbd _ h_eq ↦
      multi_prime_step_uniq q S' hq e d D₁ D₂ a b hfD₁ hgD₂ hD₁ hD₂ hap hbp had hbd h_eq)

private lemma multi_prime_coeff_factor (S : Finset {p : ℕ // p.Prime})
    (e d : {p : ℕ // p.Prime} → Fin 2 → ℕ) :
    (∏ p ∈ S, (T_gen 2 p.1 0 ^ (e p 0) * T_gen 2 p.1 1 ^ (e p 1)))
      (T_diag (∏ p ∈ S, ppowDiag 2 p.1 ![d p 1, d p 0 + d p 1])) =
    ∏ p ∈ S, (T_gen 2 p.1 0 ^ (e p 0) * T_gen 2 p.1 1 ^ (e p 1))
      (T_diag (ppowDiag 2 p.1 ![d p 1, d p 0 + d p 1])) := by
  induction S using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    change (HeckeRing.T_single (GL_pair 2) ℤ (HeckeCoset.one (GL_pair 2)) 1) (T_diag 1) = 1
    show (Finsupp.single (HeckeCoset.one (GL_pair 2)) (1 : ℤ)) (T_diag 1) = 1
    rw [Finsupp.single_apply, if_pos]
    show HeckeCoset.one (GL_pair 2) = T_diag 1
    exact T_diag_ones.symm
  | @insert q S' hq ih =>
    rw [Finset.prod_insert hq, Finset.prod_insert hq, Finset.prod_insert hq]
    exact (multi_prime_factor_step q S' hq e d).trans
      (congr_arg ((T_gen 2 q.1 0 ^ (e q 0) * T_gen 2 q.1 1 ^ (e q 1))
        (T_diag (ppowDiag 2 q.1 ![d q 1, d q 0 + d q 1])) * ·) ih)

private noncomputable def toPrimeExp (d : GenIdx →₀ ℕ) : {p : ℕ // p.Prime} → Fin 2 → ℕ :=
  fun p k ↦ d (p, k)

private def primesOf (d : GenIdx →₀ ℕ) : Finset {p : ℕ // p.Prime} :=
  d.support.image Prod.fst

private lemma monomial_eval_eq_prod_primes (d : GenIdx →₀ ℕ) :
    (∏ i ∈ d.support, (fun j : GenIdx ↦ T_gen 2 j.1.1 j.2) i ^ d i) =
    ∏ p ∈ primesOf d, (T_gen 2 p.1 0 ^ (toPrimeExp d p 0) *
      T_gen 2 p.1 1 ^ (toPrimeExp d p 1)) := by
  rw [← Finset.prod_fiberwise_of_maps_to
    (g := Prod.fst) (t := primesOf d)
    (fun i hi ↦ Finset.mem_image.mpr ⟨i, hi, rfl⟩)]
  congr 1; ext p; congr 1
  set S := Finset.univ.image (fun k : Fin 2 ↦ (p, k)) with hS_def
  rw [show T_gen 2 (↑p) 0 ^ toPrimeExp d p 0 * T_gen 2 (↑p) 1 ^ toPrimeExp d p 1 =
    ∏ i ∈ S, (fun j : GenIdx ↦ T_gen 2 (↑j.1) j.2) i ^ d i by
      simp [S, Fin.prod_univ_two, toPrimeExp, Finset.prod_image (fun
        (_ : Fin 2) _ (_ : Fin 2) _ h ↦ Prod.mk.injEq _ _ _ _ |>.mp h |>.2)]]
  refine Finset.prod_subset (M := HeckeAlgebra 2) ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finsupp.mem_support_iff] at hi
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨i.2, Prod.ext hi.2.symm rfl⟩
  · intro i hiS hi_not
    simp only [Finset.mem_filter, Finsupp.mem_support_iff, not_and] at hi_not
    have hi_fst : i.1 = p := by
      simp only [S, Finset.mem_image, Finset.mem_univ, true_and] at hiS
      obtain ⟨k, hk⟩ := hiS
      exact hk ▸ rfl
    have h_zero : d i = 0 := by
      by_contra hne
      exact hi_not hne hi_fst
    rw [h_zero]; exact pow_zero _

private lemma prod_ppowDiag_eq (S : Finset {p : ℕ // p.Prime})
    (e : {p : ℕ // p.Prime} → Fin 2 → ℕ) :
    ∏ i, (∏ p ∈ S, ppowDiag 2 p.1 ![e p 1, e p 0 + e p 1]) i =
    ∏ p ∈ S, p.1 ^ (e p 0 + 2 * e p 1) := by
  simp only [Finset.prod_apply]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p _
  simp only [ppowDiag, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    ← pow_add]
  congr 1; omega

private lemma monomial_eval_zero_of_det_ne (d s : GenIdx →₀ ℕ)
    (h_det : ∏ p ∈ primesOf d, p.1 ^ (toPrimeExp d p 0 + 2 * toPrimeExp d p 1) ≠
             ∏ p ∈ primesOf s, p.1 ^ (toPrimeExp s p 0 + 2 * toPrimeExp s p 1)) :
    (∏ p ∈ primesOf d, (T_gen 2 p.1 0 ^ (toPrimeExp d p 0) *
      T_gen 2 p.1 1 ^ (toPrimeExp d p 1)))
      (T_diag (∏ p ∈ primesOf s, ppowDiag 2 p.1
        ![toPrimeExp s p 1, toPrimeExp s p 0 + toPrimeExp s p 1])) = 0 := by
  by_contra! h
  apply h_det
  obtain ⟨a, ha_eq, ha_pos, ha_div, ha_det⟩ := prod_gen_support_det (primesOf d) (toPrimeExp d)
    (T_diag _) (by rwa [ne_eq] at h)
  set c := ∏ p ∈ primesOf s, ppowDiag 2 p.1 ![toPrimeExp s p 1, toPrimeExp s p 0 + toPrimeExp s p 1]
  have hc_pos : ∀ i, 0 < c i := fun i ↦ by
    simpa only [c, Finset.prod_apply] using
      Finset.prod_pos (fun (p : {p : ℕ // p.Prime}) _ ↦ ppowDiag_pos 2 p.1 p.2 _ i)
  have hc_div : DivChain 2 c := Finset.prod_induction _ (DivChain 2)
    (DivChain_mul 2) (fun _ _ ↦ dvd_refl 1)
    (fun (p : {p : ℕ // p.Prime}) _ ↦ divChain_ppow 2 p.1 _ (by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all))
  have hc_prod : ∏ i, c i = ∏ p ∈ primesOf s, p.1 ^ (toPrimeExp s p 0 + 2 * toPrimeExp s p 1) :=
    prod_ppowDiag_eq (primesOf s) (toPrimeExp s)
  have hac := diagonal_representative_unique 2 a c ha_pos hc_pos ha_div hc_div ha_eq.symm
  rw [hac] at ha_det; rw [← ha_det, ← hc_prod]

private lemma detCombo_pos_of_mem_primesOf (e : GenIdx →₀ ℕ) (p : {p : ℕ // p.Prime})
    (hp : p ∈ primesOf e) : 0 < toPrimeExp e p 0 + 2 * toPrimeExp e p 1 := by
  obtain ⟨⟨q, k⟩, hq_mem, hq_eq⟩ := Finset.mem_image.mp hp
  simp only at hq_eq
  subst hq_eq
  have hq_ne_zero : e (q, k) ≠ 0 := Finsupp.mem_support_iff.mp hq_mem
  fin_cases k <;> simp [toPrimeExp] at hq_ne_zero ⊢ <;> omega

private lemma primesOf_subset_of_detProd_dvd (d s : GenIdx →₀ ℕ)
    (h_dvd : (∏ p ∈ primesOf d, p.1 ^ (toPrimeExp d p 0 + 2 * toPrimeExp d p 1)) ∣
             ∏ p ∈ primesOf s, p.1 ^ (toPrimeExp s p 0 + 2 * toPrimeExp s p 1)) :
    primesOf d ⊆ primesOf s := by
  intro p hp
  have hdvd_full : p.1 ∣ ∏ q ∈ primesOf s, q.1 ^ (toPrimeExp s q 0 + 2 * toPrimeExp s q 1) :=
    (dvd_pow_self _ (Nat.pos_iff_ne_zero.mp (detCombo_pos_of_mem_primesOf d p hp))).trans
      ((Finset.dvd_prod_of_mem _ hp).trans h_dvd)
  rw [p.2.prime.dvd_finsetProd_iff] at hdvd_full
  obtain ⟨q, hq, hpq⟩ := hdvd_full
  rwa [show p = q from Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.2 q.2).mp
    (p.2.dvd_of_dvd_pow hpq))]

private lemma toPrimeExp_detCombo_eq_of_detProd_eq (d s : GenIdx →₀ ℕ)
    (h_same_primes : primesOf d = primesOf s)
    (h_det_eq : ∏ p ∈ primesOf d, p.1 ^ (toPrimeExp d p 0 + 2 * toPrimeExp d p 1) =
                ∏ p ∈ primesOf s, p.1 ^ (toPrimeExp s p 0 + 2 * toPrimeExp s p 1))
    (p : {p : ℕ // p.Prime}) (hp : p ∈ primesOf s) :
    toPrimeExp d p 0 + 2 * toPrimeExp d p 1 = toPrimeExp s p 0 + 2 * toPrimeExp s p 1 := by
  have h_fact := congr_arg (fun n ↦ n.factorization p.1) (h_same_primes ▸ h_det_eq)
  rw [Nat.factorization_prod_apply (fun (q : {p : ℕ // p.Prime}) _ ↦ pow_ne_zero _ q.2.ne_zero),
      Nat.factorization_prod_apply
        (fun (q : {p : ℕ // p.Prime}) _ ↦ pow_ne_zero _ q.2.ne_zero)] at h_fact
  have h_each : ∀ (x : {p : ℕ // p.Prime}) (e : ℕ),
      (x.1 ^ e).factorization p.1 = if x = p then e else 0 := by
    intro x e
    rw [Nat.Prime.factorization_pow x.2, Finsupp.single_apply]
    by_cases hxp : x = p
    · rw [if_pos hxp, if_pos (congr_arg Subtype.val hxp)]
    · rw [if_neg hxp, if_neg (fun h ↦ hxp (Subtype.ext h))]
  conv at h_fact => lhs; arg 2; ext x; rw [h_each x _]
  conv at h_fact => rhs; arg 2; ext x; rw [h_each x _]
  rw [Finset.sum_ite_eq_of_mem' _ p _ hp, Finset.sum_ite_eq_of_mem' _ p _ hp] at h_fact
  exact h_fact

private lemma exists_primesOf_snd_exp_lt (d s : GenIdx →₀ ℕ) (hds : d ≠ s)
    (h_same_primes : primesOf d = primesOf s)
    (h_det_eq : ∏ p ∈ primesOf d, p.1 ^ (toPrimeExp d p 0 + 2 * toPrimeExp d p 1) =
                ∏ p ∈ primesOf s, p.1 ^ (toPrimeExp s p 0 + 2 * toPrimeExp s p 1))
    (h_weight_le : (s.sum (fun i c ↦ if i.2 = (1 : Fin 2) then c else 0)) ≤
                   (d.sum (fun i c ↦ if i.2 = (1 : Fin 2) then c else 0))) :
    ∃ p₀ ∈ primesOf s, toPrimeExp s p₀ 1 < toPrimeExp d p₀ 1 := by
  by_contra! h_all_le
  apply hds; ext ⟨p, k⟩
  by_cases hp : p ∈ primesOf s
  · have h_per_prime : toPrimeExp d p 0 + 2 * toPrimeExp d p 1 =
        toPrimeExp s p 0 + 2 * toPrimeExp s p 1 :=
      toPrimeExp_detCombo_eq_of_detProd_eq d s h_same_primes h_det_eq p hp
    have h_le := h_all_le p hp
    set T := d.support ∪ s.support
    set g := fun (i : GenIdx) (c : ℕ) ↦ if i.2 = (1 : Fin 2) then c else 0
    have hg0 : ∀ i ∈ T, g i 0 = 0 := fun i _ ↦ by simp [g]
    have hd_sum : d.sum g = ∑ i ∈ T, g i (d i) :=
      Finsupp.sum_of_support_subset d Finset.subset_union_left g hg0
    have hs_sum : s.sum g = ∑ i ∈ T, g i (s i) :=
      Finsupp.sum_of_support_subset s Finset.subset_union_right g hg0
    have h_ptwise : ∀ i ∈ T, g i (d i) ≤ g i (s i) := by
      intro ⟨q, k'⟩ _; simp only [g]
      split_ifs with hk
      · by_cases hq : q ∈ primesOf s
        · have := h_all_le q hq
          show d (q, k') ≤ s (q, k')
          rwa [hk]
        · have hq_d : (q, k') ∉ d.support := fun h ↦
            (h_same_primes ▸ hq) (Finset.mem_image.mpr ⟨_, h, rfl⟩)
          rw [Finsupp.notMem_support_iff.mp hq_d]; exact Nat.zero_le _
      · exact le_refl 0
    have h_sum_eq : d.sum g = s.sum g := le_antisymm
      (by rw [hd_sum, hs_sum]; exact Finset.sum_le_sum h_ptwise) h_weight_le
    have h_eq1 : toPrimeExp d p 1 = toPrimeExp s p 1 := by
      by_contra h_ne
      have hlt : g (p, (1 : Fin 2)) (d (p, 1)) < g (p, (1 : Fin 2)) (s (p, 1)) := by
        simp only [g]; exact lt_of_le_of_ne h_le h_ne
      have h_sum_strict : ∑ i ∈ T, g i (d i) < ∑ i ∈ T, g i (s i) :=
        Finset.sum_lt_sum h_ptwise ⟨(p, 1), Finset.mem_union.mpr
          (Or.inr (Finsupp.mem_support_iff.mpr (fun h ↦ by simp [g, h] at hlt))), hlt⟩
      linarith [hd_sum ▸ hs_sum ▸ h_sum_eq]
    fin_cases k
    · show toPrimeExp d p 0 = toPrimeExp s p 0; omega
    · exact h_eq1
  · have hp' : p ∉ primesOf d := h_same_primes ▸ hp
    simp only [toPrimeExp] at *
    have : (p, k) ∉ d.support := fun h ↦ hp' (Finset.mem_image.mpr ⟨_, h, rfl⟩)
    have : (p, k) ∉ s.support := fun h ↦ hp (Finset.mem_image.mpr ⟨_, h, rfl⟩)
    simp [Finsupp.notMem_support_iff.mp ‹(p,k) ∉ d.support›,
          Finsupp.notMem_support_iff.mp ‹(p,k) ∉ s.support›]

/-- The non-equal, equal-primes-and-determinant branch of
`monomial_prod_eval_at_Ds_eq_indicator`: given `d ≠ s` with the same `primesOf` and
matching `detProd`, the test monomial evaluates to `0` via a strict descent at some
prime where `toPrimeExp s · 1 < toPrimeExp d · 1`. -/
private lemma monomial_prod_eval_at_Ds_eq_zero_of_same_primes
    (s d : GenIdx →₀ ℕ) (hds : d ≠ s)
    (h_same_primes : primesOf d = primesOf s)
    (h_det_eq : ∏ p ∈ primesOf d, p.1 ^ (toPrimeExp d p 0 + 2 * toPrimeExp d p 1) =
                ∏ p ∈ primesOf s, p.1 ^ (toPrimeExp s p 0 + 2 * toPrimeExp s p 1))
    (h_weight_le : (s.sum (fun i c ↦ if i.2 = (1 : Fin 2) then c else 0)) ≤
                   (d.sum (fun i c ↦ if i.2 = (1 : Fin 2) then c else 0))) :
    (∏ p ∈ primesOf d, (T_gen 2 p.1 0 ^ (toPrimeExp d p 0) *
      T_gen 2 p.1 1 ^ (toPrimeExp d p 1)))
      (T_diag (∏ p ∈ primesOf s, ppowDiag 2 p.1
        ![toPrimeExp s p 1, toPrimeExp s p 0 + toPrimeExp s p 1])) = 0 := by
  rw [h_same_primes, multi_prime_coeff_factor (primesOf s) (toPrimeExp d) (toPrimeExp s)]
  obtain ⟨p₀, hp₀_mem, hp₀_lt⟩ :=
    exists_primesOf_snd_exp_lt d s hds h_same_primes h_det_eq h_weight_le
  apply Finset.prod_eq_zero hp₀_mem
  rw [HeckeRing.GLn.Inj.monomial_eval_kronecker p₀.1 p₀.2
    (toPrimeExp d p₀ 0) (toPrimeExp d p₀ 1)
    (toPrimeExp s p₀ 0) (toPrimeExp s p₀ 1) hp₀_lt.le]
  simp only [ite_eq_right_iff, one_ne_zero]
  intro ⟨_, h1⟩; exact absurd h1 (Nat.ne_of_gt hp₀_lt)

private lemma monomial_prod_eval_at_Ds_eq_indicator (s d : GenIdx →₀ ℕ)
    (h_weight_le : (s.sum (fun i c ↦ if i.2 = (1 : Fin 2) then c else 0)) ≤
                   (d.sum (fun i c ↦ if i.2 = (1 : Fin 2) then c else 0))) :
    (∏ p ∈ primesOf d, (T_gen 2 p.1 0 ^ (toPrimeExp d p 0) *
      T_gen 2 p.1 1 ^ (toPrimeExp d p 1)))
      (T_diag (∏ p ∈ primesOf s, ppowDiag 2 p.1
        ![toPrimeExp s p 1, toPrimeExp s p 0 + toPrimeExp s p 1])) =
    if d = s then 1 else 0 := by
  by_cases hds : d = s
  · subst hds; simp only [ite_true]
    rw [multi_prime_coeff_factor (primesOf d) (toPrimeExp d) (toPrimeExp d)]
    simp only [Finset.prod_congr rfl (fun p _ ↦
      HeckeRing.GLn.Inj.monomial_eval_kronecker p.1 p.2
        (toPrimeExp d p 0) (toPrimeExp d p 1)
        (toPrimeExp d p 0) (toPrimeExp d p 1) le_rfl)]
    simp
  · simp only [hds, ite_false]
    by_cases h_det_eq :
        ∏ p ∈ primesOf d, p.1 ^ (toPrimeExp d p 0 + 2 * toPrimeExp d p 1) =
        ∏ p ∈ primesOf s, p.1 ^ (toPrimeExp s p 0 + 2 * toPrimeExp s p 1)
    · exact monomial_prod_eval_at_Ds_eq_zero_of_same_primes s d hds
        (Finset.Subset.antisymm
          (primesOf_subset_of_detProd_dvd d s (dvd_of_eq h_det_eq))
          (primesOf_subset_of_detProd_dvd s d (dvd_of_eq h_det_eq.symm)))
        h_det_eq h_weight_le
    · exact monomial_eval_zero_of_det_ne d s h_det_eq

private lemma π_injective : Function.Injective π_hom := by
  rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
  intro P hP; rw [RingHom.mem_ker] at hP; rw [Submodule.mem_bot]
  by_contra hP_ne
  obtain ⟨s, hs_mem, hs_min⟩ := Finset.exists_min_image P.support
    (fun d : GenIdx →₀ ℕ ↦ d.sum (fun i c ↦ if i.2 = (1 : Fin 2) then c else 0))
    (MvPolynomial.support_nonempty.mpr hP_ne)
  have hs_coeff : P.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs_mem
  set D_s := T_diag (∏ p ∈ primesOf s, ppowDiag 2 p.1
    ![toPrimeExp s p 1, toPrimeExp s p 0 + toPrimeExp s p 1]) with hD_s
  have h_zero : (π_hom P) D_s = 0 := by rw [hP]; rfl
  change (MvPolynomial.eval₂ (Int.castRingHom (HeckeAlgebra 2))
    (fun i : GenIdx ↦ T_gen 2 i.1.1 i.2) P) D_s = 0 at h_zero
  rw [MvPolynomial.eval₂_eq] at h_zero
  change (∑ d ∈ MvPolynomial.support P, (Int.castRingHom (HeckeAlgebra 2)) (MvPolynomial.coeff d P) *
    ∏ i ∈ d.support, T_gen 2 (↑i.1) i.2 ^ d i) D_s = 0 at h_zero
  rw [show (∑ d ∈ MvPolynomial.support P, (Int.castRingHom (HeckeAlgebra 2)) (MvPolynomial.coeff d P) *
        ∏ i ∈ d.support, T_gen 2 (↑i.1) i.2 ^ d i) D_s =
      ∑ d ∈ MvPolynomial.support P, ((Int.castRingHom (HeckeAlgebra 2)) (MvPolynomial.coeff d P) *
        ∏ i ∈ d.support, T_gen 2 (↑i.1) i.2 ^ d i) D_s from Finset.sum_apply' _] at h_zero
  have h_term : ∀ d ∈ P.support,
      (((Int.castRingHom (HeckeAlgebra 2)) (P.coeff d)) *
        (∏ i ∈ d.support, T_gen 2 i.1.1 i.2 ^ d i)) D_s =
      P.coeff d * (∏ i ∈ d.support, T_gen 2 i.1.1 i.2 ^ d i) D_s := by
    intro d _
    show (((P.coeff d : ℤ) : HeckeAlgebra 2) *
      (∏ i ∈ d.support, T_gen 2 i.1.1 i.2 ^ d i)) D_s = _
    rw [show ((P.coeff d : ℤ) : HeckeAlgebra 2) =
      (P.coeff d) • (1 : HeckeAlgebra 2) from (zsmul_one _).symm,
      smul_mul_assoc, one_mul]
    rw [show ((P.coeff d) • (∏ i ∈ d.support, T_gen 2 i.1.1 i.2 ^ d i : HeckeAlgebra 2)) D_s =
      P.coeff d • (∏ i ∈ d.support, T_gen 2 i.1.1 i.2 ^ d i : HeckeAlgebra 2) D_s from
      Finsupp.smul_apply _ _ _, smul_eq_mul]
  rw [Finset.sum_congr rfl h_term] at h_zero
  conv at h_zero =>
    arg 1; arg 2; ext d
    rw [show (∏ i ∈ d.support, T_gen 2 i.1.1 i.2 ^ d i) =
      ∏ p ∈ primesOf d, (T_gen 2 p.1 0 ^ (toPrimeExp d p 0) *
        T_gen 2 p.1 1 ^ (toPrimeExp d p 1)) from monomial_eval_eq_prod_primes d]
  have h_delta : ∀ d ∈ P.support,
      P.coeff d * (∏ p ∈ primesOf d, (T_gen 2 p.1 0 ^ (toPrimeExp d p 0) *
        T_gen 2 p.1 1 ^ (toPrimeExp d p 1))) D_s =
      if d = s then P.coeff d else 0 := by
    intro d hd_mem
    rw [hD_s, monomial_prod_eval_at_Ds_eq_indicator s d
      (hs_min d (MvPolynomial.mem_support_iff.mpr (MvPolynomial.mem_support_iff.mp hd_mem)))]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h_delta] at h_zero
  rw [Finset.sum_ite_eq_of_mem' (P.support) s _ hs_mem] at h_zero
  exact hs_coeff h_zero

private lemma ker_π_le_ker_ψ :
    RingHom.ker π_hom ≤ RingHom.ker (ψ_hom N) := by
  rw [(RingHom.injective_iff_ker_eq_bot π_hom).mp π_injective]
  exact bot_le

private lemma product_mem_GL_DC_scalar
    (c : ℕ) (hc : 0 < c) (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i)
    (hc_gcd : Int.gcd (↑c) ↑N = 1) (ha_gcd : Int.gcd (a 0) N = 1)
    (p : HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N
          (fun _ : Fin 2 ↦ c) (fun _ ↦ hc) hc_gcd)) ×
      HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N a ha ha_gcd))) :
    (p.1.out : GL (Fin 2) ℚ) * HeckeCoset.rep (T_diag_Gamma0 N
        (fun _ : Fin 2 ↦ c) (fun _ ↦ hc) hc_gcd) *
      ((p.2.out : GL (Fin 2) ℚ) * HeckeCoset.rep (T_diag_Gamma0 N a ha ha_gcd)) ∈
    DoubleCoset.doubleCoset (diagMat 2 ((fun _ : Fin 2 ↦ c) * a) : GL (Fin 2) ℚ)
      (SLnZ_subgroup 2 : Set _) (SLnZ_subgroup 2 : Set _) := by
  have hc_rep := HeckeCoset.rep_mem (T_diag_Gamma0 N (fun _ : Fin 2 ↦ c) (fun _ ↦ hc) hc_gcd)
  simp only [T_diag_Gamma0, HeckeCoset.toSet_mk] at hc_rep
  have ha_rep := HeckeCoset.rep_mem (T_diag_Gamma0 N a ha ha_gcd)
  simp only [T_diag_Gamma0, HeckeCoset.toSet_mk] at ha_rep
  have hc_gl := Gamma0_doubleCoset_subset_Gamma N _ hc_rep
  have ha_gl := Gamma0_doubleCoset_subset_Gamma N _ ha_rep
  rw [DoubleCoset.mem_doubleCoset] at hc_gl ha_gl
  obtain ⟨L_c, ⟨σL_c, rfl⟩, R_c, ⟨σR_c, rfl⟩, hc_eq⟩ := hc_gl
  obtain ⟨L_a, ⟨σL_a, rfl⟩, R_a, ⟨σR_a, rfl⟩, ha_eq⟩ := ha_gl
  obtain ⟨σp₁, hp₁_eq⟩ := Gamma0_le_SLnZ N (SetLike.coe_mem p.1.out)
  obtain ⟨σp₂, hp₂_eq⟩ := Gamma0_le_SLnZ N (SetLike.coe_mem p.2.out)
  set X : GL (Fin 2) ℚ := mapGL ℚ (σp₁ * σL_c * σR_c * σp₂ * σL_a) *
    diagMat 2 ((fun _ : Fin 2 ↦ c) * a) * mapGL ℚ σR_a with hX_def
  have h_rewrite : (p.1.out : GL (Fin 2) ℚ) *
      HeckeCoset.rep (T_diag_Gamma0 N (fun _ : Fin 2 ↦ c) (fun _ ↦ hc) hc_gcd) *
      ((p.2.out : GL (Fin 2) ℚ) * HeckeCoset.rep (T_diag_Gamma0 N a ha ha_gcd)) = X := by
    simp only [T_diag_Gamma0]
    rw [← hp₁_eq, ← hp₂_eq, hc_eq, ha_eq]
    show mapGL ℚ σp₁ * (mapGL ℚ σL_c * diagMat 2 (fun _ ↦ c) * mapGL ℚ σR_c) *
      (mapGL ℚ σp₂ * (mapGL ℚ σL_a * diagMat 2 a * mapGL ℚ σR_a)) = X
    rw [hX_def]
    calc mapGL ℚ σp₁ * (mapGL ℚ σL_c * diagMat 2 (fun _ ↦ c) * mapGL ℚ σR_c) *
          (mapGL ℚ σp₂ * (mapGL ℚ σL_a * diagMat 2 a * mapGL ℚ σR_a))
        = mapGL ℚ σp₁ * mapGL ℚ σL_c *
          (diagMat 2 (fun _ ↦ c) * (mapGL ℚ σR_c * mapGL ℚ σp₂ * mapGL ℚ σL_a)) *
          (diagMat 2 a * mapGL ℚ σR_a) := by group
      _ = mapGL ℚ σp₁ * mapGL ℚ σL_c *
          ((mapGL ℚ σR_c * mapGL ℚ σp₂ * mapGL ℚ σL_a) * diagMat 2 (fun _ ↦ c)) *
          (diagMat 2 a * mapGL ℚ σR_a) := by rw [diagMat_scalar_comm 2 c hc]
      _ = mapGL ℚ (σp₁ * σL_c * σR_c * σp₂ * σL_a) *
          (diagMat 2 (fun _ ↦ c) * diagMat 2 a) * mapGL ℚ σR_a := by
            simp only [map_mul]; group
      _ = mapGL ℚ (σp₁ * σL_c * σR_c * σp₂ * σL_a) *
          diagMat 2 ((fun _ ↦ c) * a) * mapGL ℚ σR_a := by
            rw [diagMat_mul 2 _ a (fun _ ↦ hc) ha]
  rw [h_rewrite]
  rw [DoubleCoset.mem_doubleCoset]
  exact ⟨mapGL ℚ (σp₁ * σL_c * σR_c * σp₂ * σL_a),
    ⟨σp₁ * σL_c * σR_c * σp₂ * σL_a, rfl⟩,
    mapGL ℚ σR_a, ⟨σR_a, rfl⟩, hX_def⟩

private lemma mulMap_Gamma0_scalar_eq
    (c : ℕ) (hc : 0 < c) (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i)
    (hc_gcd : Int.gcd (↑c) ↑N = 1) (ha_gcd : Int.gcd (a 0) N = 1)
    (hdiv : a 0 ∣ a 1)
    (hca_gcd : Int.gcd ((((fun _ : Fin 2 ↦ c) * a) 0 : ℕ) : ℤ) ↑N = 1)
    (p : HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N
          (fun _ : Fin 2 ↦ c) (fun _ ↦ hc) hc_gcd)) ×
      HeckeRing.decompQuot (Gamma0_pair N) (HeckeCoset.rep (T_diag_Gamma0 N a ha ha_gcd))) :
    HeckeRing.mulMap (Gamma0_pair N)
      (HeckeCoset.rep (T_diag_Gamma0 N (fun _ : Fin 2 ↦ c) (fun _ ↦ hc) hc_gcd))
      (HeckeCoset.rep (T_diag_Gamma0 N a ha ha_gcd)) p =
    T_diag_Gamma0 N ((fun _ : Fin 2 ↦ c) * a)
      (fun i ↦ Nat.mul_pos hc (ha i)) hca_gcd := by
  set D := HeckeRing.mulMap (Gamma0_pair N) _ _ p
  obtain ⟨b, hb, hgcd_b, hdiv_b, hrep⟩ := Gamma0_exists_diag_rep N (HeckeCoset.rep D)
  have hrep' : D = T_diag_Gamma0 N b hb hgcd_b := by rw [← hrep]; exact (HeckeCoset.mk_rep D).symm
  have hGL : cosetMap N D = T_diag b := by rw [hrep', cosetMap_T_diag_Gamma0]
  have hGL_ca : cosetMap N D = T_diag ((fun _ : Fin 2 ↦ c) * a) := by
    apply cosetMap_mulMap_mem_GL_DC N _ _ p _
    have h_mem := product_mem_GL_DC_scalar N c hc a ha hc_gcd ha_gcd p
    have h_pos : ∀ i : Fin 2, 0 < ((fun _ : Fin 2 ↦ c) * a) i :=
      fun i ↦ Nat.mul_pos hc (ha i)
    have h_eq : DoubleCoset.doubleCoset
        (diagMat 2 ((fun _ : Fin 2 ↦ c) * a) : GL (Fin 2) ℚ)
        ((SLnZ_subgroup 2) : Set _) ((SLnZ_subgroup 2) : Set _) =
        DoubleCoset.doubleCoset
        (↑(T_diag ((fun _ : Fin 2 ↦ c) * a)).rep : GL (Fin 2) ℚ)
        ((GL_pair 2).H : Set _) ((GL_pair 2).H : Set _) := by
      rw [show (diagMat 2 ((fun _ : Fin 2 ↦ c) * a) : GL (Fin 2) ℚ) =
          ↑(diagMat_delta 2 ((fun _ : Fin 2 ↦ c) * a)) from
          (diagMat_delta_val 2 _ h_pos).symm]
      have h_toSet := HeckeCoset.toSet_eq_rep (T_diag ((fun _ : Fin 2 ↦ c) * a))
      simp only [HeckeCoset.toSet, T_diag] at h_toSet
      exact h_toSet
    rw [← h_eq]
    exact h_mem
  have hdiv_b' : DivChain 2 b := fun i hi ↦ (show i = 0 by omega) ▸ hdiv_b
  have hdiv_ca : DivChain 2 ((fun _ : Fin 2 ↦ c) * a) := fun i hi ↦ by
    have h0 : (⟨i, by omega⟩ : Fin 2) = (0 : Fin 2) := Fin.ext (show i = 0 by omega)
    have h1 : (⟨i + 1, hi⟩ : Fin 2) = (1 : Fin 2) := Fin.ext (show i + 1 = 1 by omega)
    show ((fun _ : Fin 2 ↦ c) * a) ⟨i, _⟩ ∣ ((fun _ : Fin 2 ↦ c) * a) ⟨i + 1, hi⟩
    rw [h0, h1]; simp only [Pi.mul_apply]; exact Nat.mul_dvd_mul_left c hdiv
  have hb_eq : b = (fun _ : Fin 2 ↦ c) * a := diagonal_representative_unique 2 b
    ((fun _ : Fin 2 ↦ c) * a) hb (fun i ↦ Nat.mul_pos hc (ha i)) hdiv_b' hdiv_ca
    (by rw [← hGL, hGL_ca])
  subst hb_eq; exact hrep'

private lemma Gamma0_HeckeCoset_deg_scalar (c : ℕ) (hc : 0 < c)
    (hc_gcd : Int.gcd (↑c) ↑N = 1) :
    HeckeRing.HeckeCoset_deg (Gamma0_pair N)
      (T_diag_Gamma0 N (fun _ : Fin 2 ↦ c) (fun _ ↦ hc) hc_gcd) = 1 := by
  set D := T_diag_Gamma0 N (fun _ : Fin 2 ↦ c) (fun _ ↦ hc) hc_gcd
  set δ := HeckeCoset.rep D
  set H := (Gamma0_pair N).H
  suffices hsmul : ConjAct.toConjAct (δ : GL (Fin 2) ℚ) • H = H by
    have h_def : HeckeRing.HeckeCoset_deg (Gamma0_pair N) D =
        ↑((ConjAct.toConjAct (δ : GL (Fin 2) ℚ) • H).relIndex H) := by
      simp only [HeckeRing.HeckeCoset_deg, Subgroup.relIndex, Subgroup.index,
        ← Nat.card_eq_fintype_card]; rfl
    rw [h_def, hsmul, Subgroup.relIndex_self]; simp
  have hδ_mem : (δ : GL (Fin 2) ℚ) ∈
      DoubleCoset.doubleCoset (diagMat 2 (fun _ : Fin 2 ↦ c) : GL (Fin 2) ℚ) H H := by
    have h1 : HeckeCoset.toSet D =
        DoubleCoset.doubleCoset (diagMat 2 (fun _ : Fin 2 ↦ c) : GL (Fin 2) ℚ) H H := by
      simp only [D, T_diag_Gamma0, HeckeCoset.toSet_mk]; rfl
    rw [← h1]; exact HeckeCoset.rep_mem D
  rw [DoubleCoset.mem_doubleCoset] at hδ_mem; obtain ⟨h₁, hh₁, h₂, hh₂, hδ_eq⟩ := hδ_mem
  have hδ_simp : (δ : GL (Fin 2) ℚ) = (h₁ * h₂) * diagMat 2 (fun _ : Fin 2 ↦ c) := by
    rw [hδ_eq, mul_assoc, diagMat_scalar_comm 2 c hc h₂, ← mul_assoc]
  rw [hδ_simp, map_mul, ← smul_smul]
  have hscalar_smul : ConjAct.toConjAct (diagMat 2 (fun _ : Fin 2 ↦ c)) • H = H := by
    ext x; constructor
    · intro hx; rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
      simp only [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hx
      rwa [diagMat_scalar_conj_eq 2 c hc] at hx
    · intro hx; rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp only [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
      rwa [diagMat_scalar_conj_eq 2 c hc]
  rw [hscalar_smul]
  ext x; simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  constructor
  · intro hx; have : x = (h₁ * h₂) * ((h₁ * h₂)⁻¹ * x * (h₁ * h₂)) * (h₁ * h₂)⁻¹ := by group
    rw [this]; exact H.mul_mem (H.mul_mem (H.mul_mem hh₁ hh₂) hx) (H.inv_mem (H.mul_mem hh₁ hh₂))
  · intro hx; exact H.mul_mem (H.mul_mem (H.inv_mem (H.mul_mem hh₁ hh₂)) hx) (H.mul_mem hh₁ hh₂)

private lemma T_single_mul_eq_of_deg_one_left
    (D_c D_x D_out : HeckeCoset (Gamma0_pair N))
    (h_deg : HeckeRing.HeckeCoset_deg (Gamma0_pair N) D_c = 1)
    (h_mulMap : ∀ p, HeckeRing.mulMap (Gamma0_pair N) D_c.rep D_x.rep p = D_out) :
    HeckeRing.T_single (Gamma0_pair N) ℤ D_c 1 *
      HeckeRing.T_single (Gamma0_pair N) ℤ D_x 1 =
    HeckeRing.T_single (Gamma0_pair N) ℤ D_out 1 := by
  have h_card : Fintype.card (HeckeRing.decompQuot (Gamma0_pair N) D_c.rep) = 1 := by
    simp only [HeckeRing.HeckeCoset_deg] at h_deg; exact_mod_cast h_deg
  haveI : Subsingleton (HeckeRing.decompQuot (Gamma0_pair N) D_c.rep) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h_card)
  refine HeckeRing.T_single_one_mul_eq_single (Gamma0_pair N) D_c D_x D_out ?_ ?_
  · have h_le : HeckeRing.heckeMultiplicity (Gamma0_pair N) D_c.rep D_x.rep D_out.rep ≤ 1 := by
      classical
      simp only [HeckeRing.heckeMultiplicity]; norm_cast; rw [Nat.card_eq_fintype_card]
      apply Fintype.card_le_one_iff_subsingleton.mpr; constructor
      intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩
      have hi : i₁ = i₂ := Subsingleton.elim i₁ i₂; subst hi
      simp only [Set.mem_setOf_eq] at h₁ h₂
      have hj := HeckeRing.decompQuot_snd_eq_of_fst_eq (Gamma0_pair N) D_c.rep D_x.rep D_out.rep
        i₁ j₁ j₂ h₁ h₂
      subst hj; rfl
    have h_pos : 0 < HeckeRing.heckeMultiplicity (Gamma0_pair N) D_c.rep D_x.rep D_out.rep := by
      have h_mem : D_out ∈ HeckeRing.mulSupport (Gamma0_pair N) D_c.rep D_x.rep := by
        simp only [HeckeRing.mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
          true_and, Prod.exists]
        have ⟨i₀⟩ : Nonempty (HeckeRing.decompQuot (Gamma0_pair N) D_c.rep) :=
          Fintype.card_pos_iff.mp (h_card ▸ Nat.one_pos)
        have ⟨j₀⟩ : Nonempty (HeckeRing.decompQuot (Gamma0_pair N) D_x.rep) :=
          Fintype.card_pos_iff.mp (by
            have := HeckeRing.HeckeCoset_deg_pos (Gamma0_pair N) D_x
            simp only [HeckeRing.HeckeCoset_deg] at this; omega)
        exact ⟨i₀, j₀, h_mulMap (i₀, j₀)⟩
      exact HeckeRing.heckeMultiplicity_pos_of_mem (Gamma0_pair N) _ _ _ h_mem
    omega
  · intro A hA
    exact HeckeRing.heckeMultiplicity_eq_zero_of_mulMap_unique (Gamma0_pair N) _ _ D_out A hA
      h_mulMap

private lemma T_Gamma0_scalar_mul_gen (c : ℕ) (hc : 0 < c) (a : Fin 2 → ℕ)
    (ha : ∀ i, 0 < a i) (hc_gcd : Int.gcd (↑c) ↑N = 1)
    (ha_gcd : Int.gcd (a 0) N = 1) (hdiv : a 0 ∣ a 1) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (fun _ : Fin 2 ↦ c) (fun _ ↦ hc) hc_gcd) 1 *
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N a ha ha_gcd) 1 =
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N ((fun _ : Fin 2 ↦ c) * a)
        (fun i ↦ Nat.mul_pos hc (ha i))
        (by show Int.gcd (↑(c * a 0)) ↑N = 1
            simp only [Int.gcd_natCast_natCast]
            exact Nat.Coprime.mul_left
              (by rwa [Int.gcd_natCast_natCast] at hc_gcd)
              (by rwa [Int.gcd_natCast_natCast] at ha_gcd))) 1 := by
  set D_c := T_diag_Gamma0 N (fun _ : Fin 2 ↦ c) (fun _ ↦ hc) hc_gcd
  set D_a := T_diag_Gamma0 N a ha ha_gcd
  have hca_gcd' : Int.gcd ((((fun _ : Fin 2 ↦ c) * a) 0 : ℕ) : ℤ) ↑N = 1 := by
    show Int.gcd ((c * a 0 : ℕ) : ℤ) ↑N = 1
    simp only [Int.gcd_natCast_natCast]
    exact Nat.Coprime.mul_left
      (by rwa [Int.gcd_natCast_natCast] at hc_gcd)
      (by rwa [Int.gcd_natCast_natCast] at ha_gcd)
  set D_out := T_diag_Gamma0 N ((fun _ : Fin 2 ↦ c) * a)
    (fun i ↦ Nat.mul_pos hc (ha i)) hca_gcd'
  change HeckeRing.T_single _ ℤ D_c 1 * HeckeRing.T_single _ ℤ D_a 1 =
    HeckeRing.T_single _ ℤ D_out 1
  exact T_single_mul_eq_of_deg_one_left N D_c D_a D_out (Gamma0_HeckeCoset_deg_scalar N c hc hc_gcd)
    (mulMap_Gamma0_scalar_eq N c hc a ha hc_gcd ha_gcd hdiv hca_gcd')

private lemma T_Gamma0_scalar_mul (c m : ℕ) (hc : 0 < c) (hm : 0 < m)
    (hc_gcd : Int.gcd (↑c) ↑N = 1) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (fun _ : Fin 2 ↦ c) (fun _ ↦ hc) hc_gcd) 1 *
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, m]) (fun i ↦ by fin_cases i <;> simp [hm]) (by simp)) 1 =
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N ((fun _ : Fin 2 ↦ c) * ![1, m])
        (fun i ↦ Nat.mul_pos hc (by fin_cases i <;> simp [hm]))
        (by show Int.gcd (↑(c * 1)) ↑N = 1; simp [hc_gcd])) 1 := by
  set D_c := T_diag_Gamma0 N (fun _ : Fin 2 ↦ c) (fun _ ↦ hc) hc_gcd
  set D_m := T_diag_Gamma0 N (![1, m]) (fun i ↦ by fin_cases i <;> simp [hm]) (by simp)
  set D_out := T_diag_Gamma0 N ((fun _ : Fin 2 ↦ c) * ![1, m])
    (fun i ↦ Nat.mul_pos hc (by fin_cases i <;> simp [hm]))
    (by show Int.gcd (↑(c * 1)) ↑N = 1; simp [hc_gcd])
  have hca_gcd : Int.gcd ((((fun _ : Fin 2 ↦ c) * (![1, m] : Fin 2 → ℕ)) 0 : ℕ) : ℤ) ↑N = 1 := by
    simp [hc_gcd]
  have h_mulMap : ∀ p, HeckeRing.mulMap (Gamma0_pair N) D_c.rep D_m.rep p = D_out := by
    intro p
    have h := mulMap_Gamma0_scalar_eq N c hc ![1, m]
      (fun i ↦ by fin_cases i <;> simp [hm]) hc_gcd (by simp) (by simp) hca_gcd p
    convert h using 2
  exact T_single_mul_eq_of_deg_one_left N D_c D_m D_out (Gamma0_HeckeCoset_deg_scalar N c hc hc_gcd)
    h_mulMap

private lemma T_1p_mem_ψ_range (p : ℕ) (hp : p.Prime) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, p])
        (fun i ↦ by fin_cases i <;> simp [hp.pos])
        (by simp)) 1 ∈ (ψ_hom N).range :=
  ⟨MvPolynomial.X (⟨p, hp⟩, (0 : Fin 2)), by
    show ψ_hom N (MvPolynomial.X (⟨p, hp⟩, (0 : Fin 2))) = _
    letI : CommRing (𝕋 (Gamma0_pair N) ℤ) := instCommRing_Gamma0 N
    refine (MvPolynomial.eval₂Hom_X' _ _ _).trans ?_
    rfl⟩

private lemma T_pp_mem_ψ_range (p : ℕ) (hp : p.Prime) (hpN : (p : ℤ).gcd N = 1) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![p, p])
        (fun i ↦ by fin_cases i <;> simp [hp.pos])
        (by show Int.gcd (↑p) ↑N = 1; exact hpN)) 1 ∈ (ψ_hom N).range := by
  have hp_not_dvd_N : ¬(p ∣ N) := fun h ↦ by
    rw [Int.gcd_natCast_natCast] at hpN
    exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, dvd_refl p, h⟩ hpN
  refine ⟨MvPolynomial.X (⟨p, hp⟩, (1 : Fin 2)), ?_⟩
  show ψ_hom N (MvPolynomial.X (⟨p, hp⟩, (1 : Fin 2))) = _
  letI : CommRing (𝕋 (Gamma0_pair N) ℤ) := instCommRing_Gamma0 N
  refine (MvPolynomial.eval₂Hom_X' _ _ _).trans ?_
  simp only [show (1 : Fin 2) ≠ 0 by omega, ↓reduceIte, dif_neg hp_not_dvd_N]

private lemma T_p_ppow_mem_ψ_range (p : ℕ) (hp : p.Prime) (hpN : (p : ℤ).gcd N = 1)
    (j : ℕ) (hj : 1 ≤ j)
    (h_IH : HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, p^(j-1)])
        (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
        (by simp)) 1 ∈ (ψ_hom N).range) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![p, p^j])
        (fun i ↦ by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
        (by show Int.gcd (↑p) ↑N = 1; exact hpN)) 1 ∈ (ψ_hom N).range := by
  have h_Tpp := T_pp_mem_ψ_range N p hp hpN
  have h_pp_eq : T_diag_Gamma0 N (![p, p])
      (fun i ↦ by fin_cases i <;> simp [hp.pos])
      (by show Int.gcd (↑p) ↑N = 1; exact hpN) =
    T_diag_Gamma0 N (fun _ : Fin 2 ↦ p) (fun _ ↦ hp.pos) hpN :=
    T_diag_Gamma0_congr N _ _ _ _ (by funext i; fin_cases i <;> rfl)
  rw [h_pp_eq] at h_Tpp
  have h_mul := T_Gamma0_scalar_mul N p (p^(j-1)) hp.pos (pow_pos hp.pos _) hpN
  have h_diag_eq : (fun _ : Fin 2 ↦ p) * ![1, p^(j-1)] = ![p, p^j] := by
    funext i
    fin_cases i
    · show p * 1 = p; ring
    · show p * p^(j-1) = p^j
      rw [← pow_succ', show j - 1 + 1 = j from Nat.sub_add_cancel hj]
  have h_eq : T_diag_Gamma0 N ((fun _ : Fin 2 ↦ p) * ![1, p^(j-1)])
      (fun i ↦ Nat.mul_pos hp.pos (by fin_cases i <;> simp [pow_pos hp.pos]))
      (by show Int.gcd (↑(p * 1)) ↑N = 1; simp [hpN]) =
    T_diag_Gamma0 N (![p, p^j])
      (fun i ↦ by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
      (by show Int.gcd (↑p) ↑N = 1; exact hpN) :=
    T_diag_Gamma0_congr N _ _ _ _ h_diag_eq
  rw [h_eq] at h_mul
  rw [← h_mul]
  exact (ψ_hom N).range.mul_mem h_Tpp h_IH

private lemma Gamma0_T_diag_rep_decompose (a : Fin 2 → ℕ)
    (ha : ∀ i, 0 < a i) (hgcd : Int.gcd (a 0) N = 1) :
    ∃ L ∈ (Gamma0_pair N).H, ∃ R ∈ (Gamma0_pair N).H,
      (HeckeCoset.rep (T_diag_Gamma0 N a ha hgcd) : GL (Fin 2) ℚ) =
        L * diagMat 2 a * R := by
  have h_rep := HeckeCoset.rep_mem (T_diag_Gamma0 N a ha hgcd)
  simp only [T_diag_Gamma0, HeckeCoset.toSet_mk] at h_rep
  rwa [DoubleCoset.mem_doubleCoset] at h_rep

private lemma Gamma0_T_diag_rep_det (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i)
    (hgcd : Int.gcd (a 0) N = 1) :
    (HeckeCoset.rep (T_diag_Gamma0 N a ha hgcd) : GL (Fin 2) ℚ).val.det =
      ((a 0 * a 1 : ℕ) : ℚ) := by
  obtain ⟨L, hL, R, hR, hLR_eq⟩ := Gamma0_T_diag_rep_decompose N a ha hgcd
  obtain ⟨σL, hσL⟩ := Gamma0_le_SLnZ N hL
  obtain ⟨σR, hσR⟩ := Gamma0_le_SLnZ N hR
  rw [hLR_eq, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
  rw [show (L : Matrix (Fin 2) (Fin 2) ℚ).det = 1 by
        rw [show (L : GL _ ℚ) = (σL : GL _ ℚ) from hσL.symm]
        exact HeckeRing.GL2.SLnZ_to_GLnQ_det σL,
      show (R : Matrix (Fin 2) (Fin 2) ℚ).det = 1 by
        rw [show (R : GL _ ℚ) = (σR : GL _ ℚ) from hσR.symm]
        exact HeckeRing.GL2.SLnZ_to_GLnQ_det σR,
      diagMat_det 2 a ha]
  push_cast; simp [Fin.prod_univ_two]

private lemma T_diag_Gamma0_one_ppow_ne_p_ppow (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 1 ≤ k)
    (h1 : ∀ i, 0 < (![1, p^(k+1)] : Fin 2 → ℕ) i) (hg1 : Int.gcd ((![1, p^(k+1)] : Fin 2 → ℕ) 0) N = 1)
    (h2 : ∀ i, 0 < (![p, p^k] : Fin 2 → ℕ) i) (hg2 : Int.gcd ((![p, p^k] : Fin 2 → ℕ) 0) N = 1) :
    T_diag_Gamma0 N (![1, p^(k+1)]) h1 hg1 ≠ T_diag_Gamma0 N (![p, p^k]) h2 hg2 := by
  intro heq
  have h_GL_eq : cosetMap N (T_diag_Gamma0 N (![1, p^(k+1)]) h1 hg1) =
      cosetMap N (T_diag_Gamma0 N (![p, p^k]) h2 hg2) := congr_arg _ heq
  rw [cosetMap_T_diag_Gamma0, cosetMap_T_diag_Gamma0] at h_GL_eq
  have h1_div : DivChain 2 (![1, p^(k+1)]) := fun i hi ↦ by
    have hi0 : i = 0 := by omega
    subst hi0; simp
  have h2_div : DivChain 2 (![p, p^k]) := fun i hi ↦ by
    have hi0 : i = 0 := by omega
    subst hi0; simpa using dvd_pow_self p (show k ≠ 0 by omega)
  have := congr_fun (diagonal_representative_unique 2 _ _ h1 h2 h1_div h2_div h_GL_eq) 0
  simp only [Matrix.cons_val_zero] at this
  exact absurd this.symm (Nat.Prime.one_lt hp).ne'

private lemma D_out1_Gamma0_pp_in_mulSupport (p : ℕ) (hp : p.Prime)
    (_hpN : (p : ℤ).gcd N = 1) (k : ℕ) (_hk : 1 ≤ k) :
    (T_diag_Gamma0 N (![1, p^(k+1)])
        (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos]) (by simp)) ∈
      HeckeRing.mulSupport (Gamma0_pair N)
        (HeckeCoset.rep (T_diag_Gamma0 N (![1, p])
          (fun i ↦ by fin_cases i <;> simp [hp.pos]) (by simp)))
        (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k])
          (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos]) (by simp))) := by
  set H := (Gamma0_pair N).H
  have h_pos1 : ∀ i : Fin 2, 0 < (![1, p] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp [hp.pos]
  have h_pos2 : ∀ i : Fin 2, 0 < (![1, p^k] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp [pow_pos hp.pos]
  have h_pos3 : ∀ i : Fin 2, 0 < (![1, p^(k+1)] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp [pow_pos hp.pos]
  obtain ⟨L₁, hL₁, R₁, hR₁, hα_eq⟩ :=
    Gamma0_T_diag_rep_decompose N (![1, p]) h_pos1 (by simp)
  obtain ⟨L₂, hL₂, R₂, hR₂, hβ_eq⟩ :=
    Gamma0_T_diag_rep_decompose N (![1, p^k]) h_pos2 (by simp)
  apply HeckeRing.mem_mulSupport_of_product_mem _ _ _
    ⟨diagMat 2 (![1, p^(k+1)]), diagMat_mem_Delta0_of_gcd N _ h_pos3 (by simp)⟩
    ⟨L₁⁻¹, H.inv_mem hL₁⟩
    ⟨R₁⁻¹ * L₂⁻¹, H.mul_mem (H.inv_mem hR₁) (H.inv_mem hL₂)⟩
  show (L₁⁻¹ : GL (Fin 2) ℚ) *
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p]) h_pos1 (by simp)) : GL (Fin 2) ℚ) *
      ((R₁⁻¹ * L₂⁻¹ : GL (Fin 2) ℚ) *
        (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k]) h_pos2 (by simp)) :
          GL (Fin 2) ℚ)) ∈
    DoubleCoset.doubleCoset (diagMat 2 (![1, p^(k+1)]) : GL (Fin 2) ℚ)
      (H : Set _) (H : Set _)
  rw [hα_eq, hβ_eq, DoubleCoset.mem_doubleCoset]
  refine ⟨1, H.one_mem, R₂, hR₂, ?_⟩
  have h_alg : (L₁⁻¹ : GL (Fin 2) ℚ) * (L₁ * diagMat 2 (![1, p]) * R₁) *
      ((R₁⁻¹ * L₂⁻¹ : GL (Fin 2) ℚ) * (L₂ * diagMat 2 (![1, p^k]) * R₂)) =
      diagMat 2 (![1, p]) * diagMat 2 (![1, p^k]) * R₂ := by group
  rw [h_alg]
  rw [diagMat_mul 2 (![1, p]) (![1, p^k]) h_pos1 h_pos2]
  rw [show (1 : GL (Fin 2) ℚ) * diagMat 2 (![1, p^(k+1)]) * R₂ =
      diagMat 2 (![1, p^(k+1)]) * R₂ by group]
  congr 2
  ext i; fin_cases i <;> simp [Pi.mul_apply, pow_succ, mul_comm]

private lemma coprimeDet_diagMat (v : Fin 2 → ℕ) (hv : ∀ i, 0 < v i)
    (hmem : diagMat 2 v ∈ Delta0_submonoid N) (hcop : Nat.Coprime (v 0 * v 1) N) :
    CoprimeDet N ⟨diagMat 2 v, hmem⟩ := by
  intro A' hA'
  have h_det_eq : (A'.det : ℚ) = ((v 0 * v 1 : ℕ) : ℚ) := by
    rw [show (A'.det : ℚ) = (A'.map (Int.cast : ℤ → ℚ)).det from (det_intMat_cast 2 A').symm, ← hA']
    show (diagMat 2 v : GL (Fin 2) ℚ).val.det = _
    rw [diagMat_det 2 v hv]; push_cast; rw [Fin.prod_univ_two]
  have h_A'_det : A'.det = (v 0 * v 1 : ℕ) := by exact_mod_cast h_det_eq
  rw [h_A'_det, Int.gcd_natCast_natCast]; exact_mod_cast hcop

private lemma T_diag_Gamma0_eq_of_GL_eq (a b : Fin 2 → ℕ)
    (ha : ∀ i, 0 < a i) (hga : Int.gcd (a 0) N = 1) (hcop_a : Nat.Coprime (a 0 * a 1) N)
    (hb : ∀ i, 0 < b i) (hgb : Int.gcd (b 0) N = 1) (hcop_b : Nat.Coprime (b 0 * b 1) N)
    (h_GL : (T_diag a : HeckeCoset (GL_pair 2)) = T_diag b) :
    T_diag_Gamma0 N a ha hga = T_diag_Gamma0 N b hb hgb := by
  refine shimura_prop_3_31 N ⟨diagMat 2 a, diagMat_mem_Delta0_of_gcd N a ha hga⟩
    ⟨diagMat 2 b, diagMat_mem_Delta0_of_gcd N b hb hgb⟩
    (coprimeDet_diagMat N a ha _ hcop_a) (coprimeDet_diagMat N b hb _ hcop_b) ?_
  show cosetMap N (T_diag_Gamma0 N a ha hga) = cosetMap N (T_diag_Gamma0 N b hb hgb)
  rwa [cosetMap_T_diag_Gamma0, cosetMap_T_diag_Gamma0]

private lemma mulSupport_Gamma0_pp_GL_split (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 1 ≤ k)
    (A : HeckeCoset (Gamma0_pair N)) (a : Fin 2 → ℕ) (ha_pos : ∀ i, 0 < a i)
    (ha_gcd : Int.gcd (a 0) N = 1) (h_a_div : DivChain 2 a)
    (hA_eq : A = T_diag_Gamma0 N a ha_pos ha_gcd)
    (hA : A ∈ HeckeRing.mulSupport (Gamma0_pair N)
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p]) (fun i ↦ by fin_cases i <;> simp [hp.pos])
        (by simp)))
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k])
        (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos]) (by simp)))) :
    a 0 * a 1 = p ^ (k + 1) ∧
    ((T_diag a : HeckeCoset (GL_pair 2)) = T_diag (![1, p^(k+1)]) ∨
    (T_diag a : HeckeCoset (GL_pair 2)) = T_diag (![p, p^k])) := by
  set H := (Gamma0_pair N).H
  have h_pos1 : ∀ i : Fin 2, 0 < (![1, p] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp [hp.pos]
  have h_pos2 : ∀ i : Fin 2, 0 < (![1, p^k] : Fin 2 → ℕ) i := by
    intro i; fin_cases i <;> simp [pow_pos hp.pos]
  rw [HeckeRing.mulSupport] at hA
  simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists] at hA
  obtain ⟨i₀, j₀, hmap⟩ := hA
  obtain ⟨L₁, hL₁, R₁, hR₁, hα_eq⟩ :=
    Gamma0_T_diag_rep_decompose N (![1, p]) h_pos1 (by simp)
  obtain ⟨L₂, hL₂, R₂, hR₂, hβ_eq⟩ :=
    Gamma0_T_diag_rep_decompose N (![1, p^k]) h_pos2 (by simp)
  have h_prod_in_A_Γ₀ : ((i₀.out : GL (Fin 2) ℚ)) *
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p]) h_pos1 (by simp)) : GL (Fin 2) ℚ) *
      (((j₀.out : GL (Fin 2) ℚ)) *
        (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k]) h_pos2 (by simp)) : GL (Fin 2) ℚ)) ∈
      DoubleCoset.doubleCoset (diagMat 2 a : GL (Fin 2) ℚ) (H : Set _) (H : Set _) := by
    have h1 : ((i₀.out : GL (Fin 2) ℚ)) *
        (HeckeCoset.rep (T_diag_Gamma0 N (![1, p]) h_pos1 (by simp)) : GL (Fin 2) ℚ) *
        (((j₀.out : GL (Fin 2) ℚ)) *
          (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k]) h_pos2 (by simp)) : GL (Fin 2) ℚ)) ∈
        HeckeCoset.toSet (HeckeRing.mulMap (Gamma0_pair N)
          (HeckeCoset.rep (T_diag_Gamma0 N (![1, p]) h_pos1 (by simp)))
          (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k]) h_pos2 (by simp))) (i₀, j₀)) := by
      rw [HeckeRing.mulMap, HeckeCoset.toSet_mk]
      exact DoubleCoset.mem_doubleCoset_self _ _ _
    rw [hmap, hA_eq, T_diag_Gamma0, HeckeCoset.toSet_mk] at h1
    exact h1
  have h_prod_in_SL := Gamma0_doubleCoset_subset_Gamma N _ h_prod_in_A_Γ₀
  rw [DoubleCoset.mem_doubleCoset] at h_prod_in_SL
  obtain ⟨L_a, ⟨SL_La, rfl⟩, R_a, ⟨SL_Ra, rfl⟩, h_prod_eq⟩ := h_prod_in_SL
  obtain ⟨SL_L₁, hSL_L₁⟩ := Gamma0_le_SLnZ N hL₁
  obtain ⟨SL_R₁, hSL_R₁⟩ := Gamma0_le_SLnZ N hR₁
  obtain ⟨SL_L₂, hSL_L₂⟩ := Gamma0_le_SLnZ N hL₂
  obtain ⟨SL_R₂, hSL_R₂⟩ := Gamma0_le_SLnZ N hR₂
  obtain ⟨SL_i₀, hSL_i₀⟩ := Gamma0_le_SLnZ N (SetLike.coe_mem i₀.out)
  obtain ⟨SL_j₀, hSL_j₀⟩ := Gamma0_le_SLnZ N (SetLike.coe_mem j₀.out)
  have h_det := HeckeRing.GL2.mulSupport_pp_det_eq p k a ha_pos (i₀.out : GL (Fin 2) ℚ)
    (HeckeCoset.rep (T_diag_Gamma0 N (![1, p]) h_pos1 (by simp)) : GL (Fin 2) ℚ)
    (j₀.out : GL (Fin 2) ℚ)
    (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k]) h_pos2 (by simp)) : GL (Fin 2) ℚ)
    (by rw [show ((i₀.out : H) : GL (Fin 2) ℚ) = (SL_i₀ : GL (Fin 2) ℚ) from hSL_i₀.symm]
        exact HeckeRing.GL2.SLnZ_to_GLnQ_det SL_i₀)
    (by have := Gamma0_T_diag_rep_det N (![1, p]) h_pos1 (by simp); push_cast at this; rw [this]; ring)
    (by rw [show ((j₀.out : H) : GL (Fin 2) ℚ) = (SL_j₀ : GL (Fin 2) ℚ) from hSL_j₀.symm]
        exact HeckeRing.GL2.SLnZ_to_GLnQ_det SL_j₀)
    (by have := Gamma0_T_diag_rep_det N (![1, p^k]) h_pos2 (by simp); push_cast at this; rw [this]; ring)
    SL_La SL_Ra h_prod_eq
  have h_dvd := HeckeRing.GL2.mulSupport_pp_dvd_p p hp k hk a ha_pos h_a_div
    (HeckeCoset.rep (T_diag_Gamma0 N (![1, p]) h_pos1 (by simp)) : GL (Fin 2) ℚ)
    (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k]) h_pos2 (by simp)) : GL (Fin 2) ℚ)
    (i₀.out : GL (Fin 2) ℚ) (j₀.out : GL (Fin 2) ℚ) SL_L₁ SL_R₁ SL_L₂ SL_R₂ SL_La SL_Ra SL_i₀ SL_j₀
    (by rw [hα_eq, hSL_L₁, hSL_R₁]) (by rw [hβ_eq, hSL_L₂, hSL_R₂]) hSL_i₀.symm hSL_j₀.symm h_prod_eq
  exact ⟨h_det, HeckeRing.GL2.mulSupport_pp_case_split p hp k hk a ha_pos h_a_div h_det h_dvd⟩

private lemma mulSupport_Gamma0_pp_subset (p : ℕ) (hp : p.Prime)
    (hpN : (p : ℤ).gcd N = 1) (k : ℕ) (hk : 1 ≤ k)
    (A : HeckeCoset (Gamma0_pair N))
    (hA : A ∈ HeckeRing.mulSupport (Gamma0_pair N)
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p])
        (fun i ↦ by fin_cases i <;> simp [hp.pos]) (by simp)))
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k])
        (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos]) (by simp)))) :
    A = T_diag_Gamma0 N (![1, p^(k+1)])
        (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos]) (by simp) ∨
    A = T_diag_Gamma0 N (![p, p^k])
        (fun i ↦ by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
        (by show Int.gcd (↑p) ↑N = 1; exact hpN) := by
  obtain ⟨a, ha_pos, ha_gcd, ha_div, hrep⟩ := Gamma0_exists_diag_rep N (HeckeCoset.rep A)
  have hA_eq : A = T_diag_Gamma0 N a ha_pos ha_gcd := by rw [← hrep]; exact (HeckeCoset.mk_rep A).symm
  have h_a_div : DivChain 2 a := fun i hi ↦ (show i = 0 by omega) ▸ ha_div
  have h_pN_cop : Nat.Coprime p N := by rwa [Int.gcd_natCast_natCast] at hpN
  obtain ⟨h_det, h_GL⟩ :=
    mulSupport_Gamma0_pp_GL_split N p hp k hk A a ha_pos ha_gcd h_a_div hA_eq hA
  have h_a_coprime_det : Nat.Coprime (a 0 * a 1) N := by rw [h_det]; exact h_pN_cop.pow_left _
  rcases h_GL with h | h
  · exact Or.inl <| hA_eq.trans <| T_diag_Gamma0_eq_of_GL_eq N a (![1, p^(k+1)]) ha_pos ha_gcd
      h_a_coprime_det (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos]) (by simp)
      (by simpa using h_pN_cop.pow_left (k+1)) h
  · exact Or.inr <| hA_eq.trans <| T_diag_Gamma0_eq_of_GL_eq N a (![p, p^k]) ha_pos ha_gcd
      h_a_coprime_det (fun i ↦ by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
      (by show Int.gcd (↑p) ↑N = 1; exact hpN)
      (by simpa [pow_succ, mul_comm] using h_pN_cop.pow_left (k+1)) h

private lemma heckeMult_k1_solve (p m1 m2 : ℤ) (hp2 : 2 ≤ p) (hm2_nn : 0 ≤ m2)
    (hm1_pos : 1 ≤ m1) (h : m1 * (p * (p + 1)) + m2 = (p + 1) * (p + 1)) :
    m1 = 1 ∧ m2 = p + 1 :=
  have h_m1 : m1 = 1 := by nlinarith [hm2_nn, mul_self_nonneg (p - 1)]
  ⟨h_m1, by rw [h_m1] at h; linarith⟩

private lemma heckeMult_kge2_solve (p m1 m2 : ℤ) (hp2 : 2 ≤ p) (hm2_nn : 0 ≤ m2)
    (hm1_pos : 1 ≤ m1) (h : m1 * p ^ 2 + m2 = p * (p + 1)) :
    m1 = 1 ∧ m2 = p :=
  have h_m1 : m1 = 1 := by nlinarith [show (4 : ℤ) ≤ p ^ 2 by nlinarith]
  ⟨h_m1, by rw [h_m1] at h; linarith⟩

private lemma heckeMult_pp_deg_facts (p : ℕ) (hp : p.Prime)
    (hpN : (p : ℤ).gcd N = 1) (k : ℕ) (hk : 1 ≤ k) :
    1 ≤ HeckeRing.heckeMultiplicity (Gamma0_pair N)
      (T_diag_Gamma0 N (![1, p]) (fun i ↦ by fin_cases i <;> simp [hp.pos]) (by simp)).rep
      (T_diag_Gamma0 N (![1, p^k]) (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
        (by simp)).rep
      (T_diag_Gamma0 N (![1, p^(k+1)]) (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
        (by simp)).rep ∧
    0 ≤ HeckeRing.heckeMultiplicity (Gamma0_pair N)
      (T_diag_Gamma0 N (![1, p]) (fun i ↦ by fin_cases i <;> simp [hp.pos]) (by simp)).rep
      (T_diag_Gamma0 N (![1, p^k]) (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
        (by simp)).rep
      (T_diag_Gamma0 N (![p, p^k]) (fun i ↦ by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
        (by show Int.gcd (↑p) ↑N = 1; exact hpN)).rep ∧
    HeckeRing.heckeMultiplicity (Gamma0_pair N)
      (T_diag_Gamma0 N (![1, p]) (fun i ↦ by fin_cases i <;> simp [hp.pos]) (by simp)).rep
      (T_diag_Gamma0 N (![1, p^k]) (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
        (by simp)).rep
      (T_diag_Gamma0 N (![1, p^(k+1)]) (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
        (by simp)).rep * ((p ^ ((k + 1) - 1) * (p + 1) : ℕ) : ℤ) +
    HeckeRing.heckeMultiplicity (Gamma0_pair N)
      (T_diag_Gamma0 N (![1, p]) (fun i ↦ by fin_cases i <;> simp [hp.pos]) (by simp)).rep
      (T_diag_Gamma0 N (![1, p^k]) (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
        (by simp)).rep
      (T_diag_Gamma0 N (![p, p^k]) (fun i ↦ by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
        (by show Int.gcd (↑p) ↑N = 1; exact hpN)).rep *
      (if k = 1 then (1 : ℤ) else ((p ^ (k - 2) * (p + 1) : ℕ) : ℤ)) =
    ((p + 1 : ℕ) : ℤ) * ((p ^ (k - 1) * (p + 1) : ℕ) : ℤ) := by
  have h_pN_cop : Nat.Coprime p N := by rwa [Int.gcd_natCast_natCast] at hpN
  set D1 := T_diag_Gamma0 N (![1, p])
    (fun i ↦ by fin_cases i <;> simp [hp.pos]) (by simp)
  set D2 := T_diag_Gamma0 N (![1, p^k])
    (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos]) (by simp)
  set D_out1 := T_diag_Gamma0 N (![1, p^(k+1)])
    (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos]) (by simp)
  set D_out2 := T_diag_Gamma0 N (![p, p^k])
    (fun i ↦ by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
    (by show Int.gcd (↑p) ↑N = 1; exact hpN)
  have h_ne : D_out1 ≠ D_out2 := T_diag_Gamma0_one_ppow_ne_p_ppow N p hp k hk _ _ _ _
  have h_zero : ∀ A, A ≠ D_out1 → A ≠ D_out2 →
      HeckeRing.heckeMultiplicity (Gamma0_pair N) D1.rep D2.rep (HeckeCoset.rep A) = 0 :=
    fun A h1 h2 ↦ HeckeRing.heckeMultiplicity_eq_zero_of_nmem_mulSupport _ _ _ _ (fun hmem ↦
      (mulSupport_Gamma0_pp_subset N p hp hpN k hk A hmem).elim h1 h2)
  have h_deg : HeckeRing.heckeMultiplicity (Gamma0_pair N) D1.rep D2.rep D_out1.rep *
      HeckeRing.HeckeCoset_deg (Gamma0_pair N) D_out1 +
      HeckeRing.heckeMultiplicity (Gamma0_pair N) D1.rep D2.rep D_out2.rep *
      HeckeRing.HeckeCoset_deg (Gamma0_pair N) D_out2 =
      HeckeRing.HeckeCoset_deg (Gamma0_pair N) D1 *
        HeckeRing.HeckeCoset_deg (Gamma0_pair N) D2 :=
    HeckeRing.heckeMultiplicity_deg_sum_eq (Gamma0_pair N) D1 D2 D_out1 D_out2 h_ne h_zero
  have h_D1_eq : D1 = T_diag_Gamma0 N (![1, p^1])
      (fun i ↦ by fin_cases i <;> simp [hp.pos]) (by simp) := by
    show T_diag_Gamma0 N (![1, p]) _ _ = _
    exact T_diag_Gamma0_congr N _ _ _ _ (by funext i; fin_cases i <;> simp)
  rw [show HeckeRing.HeckeCoset_deg (Gamma0_pair N) D1 = ↑((p + 1 : ℕ) : ℤ) by
        rw [h_D1_eq]
        have := HeckeCoset_deg_Gamma0_one_ppow N p hp h_pN_cop 1 (by omega)
        push_cast at this ⊢; convert this using 1; ring,
      HeckeCoset_deg_Gamma0_one_ppow N p hp h_pN_cop k hk,
      HeckeCoset_deg_Gamma0_one_ppow N p hp h_pN_cop (k+1) (by omega),
      HeckeCoset_deg_Gamma0_p_ppow N p hp h_pN_cop k hk] at h_deg
  refine ⟨?_, HeckeRing.heckeMultiplicity_nonneg (Gamma0_pair N) D1.rep D2.rep D_out2.rep, h_deg⟩
  have hne : (HeckeRing.m (Gamma0_pair N) D1.rep D2.rep) D_out1 ≠ 0 := by
    rw [← Finsupp.mem_support_iff, HeckeRing.m_support]
    exact D_out1_Gamma0_pp_in_mulSupport N p hp hpN k hk
  exact Int.lt_iff_add_one_le.mp (lt_of_le_of_ne
    (HeckeRing.heckeMultiplicity_nonneg (Gamma0_pair N) D1.rep D2.rep D_out1.rep) (Ne.symm hne))

private lemma heckeMultiplicity_Gamma0_values (p : ℕ) (hp : p.Prime)
    (hpN : (p : ℤ).gcd N = 1) (k : ℕ) (hk : 1 ≤ k) :
    HeckeRing.heckeMultiplicity (Gamma0_pair N)
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p])
        (fun i ↦ by fin_cases i <;> simp [hp.pos]) (by simp)))
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k])
        (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos]) (by simp)))
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^(k+1)])
        (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos]) (by simp))) = 1 ∧
    HeckeRing.heckeMultiplicity (Gamma0_pair N)
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p])
        (fun i ↦ by fin_cases i <;> simp [hp.pos]) (by simp)))
      (HeckeCoset.rep (T_diag_Gamma0 N (![1, p^k])
        (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos]) (by simp)))
      (HeckeCoset.rep (T_diag_Gamma0 N (![p, p^k])
        (fun i ↦ by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
        (by show Int.gcd (↑p) ↑N = 1; exact hpN))) =
      if k = 1 then ((p : ℤ) + 1) else (p : ℤ) := by
  obtain ⟨hm1_pos, hm2_nn, h_deg⟩ := heckeMult_pp_deg_facts N p hp hpN k hk
  set m1 := HeckeRing.heckeMultiplicity (Gamma0_pair N)
    (T_diag_Gamma0 N (![1, p]) (fun i ↦ by fin_cases i <;> simp [hp.pos]) (by simp)).rep
    (T_diag_Gamma0 N (![1, p^k]) (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos]) (by simp)).rep
    (T_diag_Gamma0 N (![1, p^(k+1)]) (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
      (by simp)).rep with hm1_def
  set m2 := HeckeRing.heckeMultiplicity (Gamma0_pair N)
    (T_diag_Gamma0 N (![1, p]) (fun i ↦ by fin_cases i <;> simp [hp.pos]) (by simp)).rep
    (T_diag_Gamma0 N (![1, p^k]) (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos]) (by simp)).rep
    (T_diag_Gamma0 N (![p, p^k]) (fun i ↦ by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
      (by show Int.gcd (↑p) ↑N = 1; exact hpN)).rep with hm2_def
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  by_cases hk1 : k = 1
  · subst hk1
    simp only [if_true, Nat.add_sub_cancel, pow_one, show (1 - 1 : ℕ) = 0 from rfl,
      pow_zero, one_mul] at h_deg ⊢
    push_cast at h_deg ⊢
    exact heckeMult_k1_solve p m1 m2 hp2 hm2_nn hm1_pos (by linarith [h_deg])
  · simp only [if_neg hk1, Nat.add_sub_cancel] at h_deg ⊢
    have hk2 : 2 ≤ k := by omega
    have hpk : (p : ℤ) ^ k = (p : ℤ) ^ (k - 2) * (p : ℤ) ^ 2 := by
      exact_mod_cast show (p : ℕ) ^ k = p ^ (k - 2) * p ^ 2 by rw [← pow_add]; congr 1; omega
    have hpk1 : (p : ℤ) ^ (k - 1) = (p : ℤ) ^ (k - 2) * p := by
      have : (p : ℕ) ^ (k - 1) = p ^ (k - 2) * p ^ 1 := by rw [← pow_add]; congr 1; omega
      simp only [pow_one] at this; exact_mod_cast this
    push_cast at h_deg
    rw [hpk, hpk1] at h_deg
    refine heckeMult_kge2_solve p m1 m2 hp2 hm2_nn hm1_pos ?_
    have key : (p : ℤ) ^ (k - 2) * ((p : ℤ) + 1) ≠ 0 := by positivity
    exact mul_right_cancel₀ key (by nlinarith [h_deg])

private lemma Gamma0_T1p_mul_T1ppow_coprime (p : ℕ) (hp : p.Prime)
    (hpN : (p : ℤ).gcd N = 1) (k : ℕ) (hk : 1 ≤ k) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, p])
        (fun i ↦ by fin_cases i <;> simp [hp.pos])
        (by simp)) 1 *
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, p^k])
        (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
        (by simp)) 1 =
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, p^(k+1)])
        (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
        (by simp)) 1 +
    (if k = 1 then ((p : ℤ) + 1) else (p : ℤ)) •
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![p, p^k])
        (fun i ↦ by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
        (by show Int.gcd (↑p) ↑N = 1; exact hpN)) 1 := by
  set D1 := T_diag_Gamma0 N (![1, p])
    (fun i ↦ by fin_cases i <;> simp [hp.pos]) (by simp)
  set D2 := T_diag_Gamma0 N (![1, p^k])
    (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos]) (by simp)
  set D_out1 := T_diag_Gamma0 N (![1, p^(k+1)])
    (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos]) (by simp)
  set D_out2 := T_diag_Gamma0 N (![p, p^k])
    (fun i ↦ by fin_cases i <;> simp [hp.pos, pow_pos hp.pos])
    (by show Int.gcd (↑p) ↑N = 1; exact hpN)
  set c : ℤ := if k = 1 then ((p : ℤ) + 1) else (p : ℤ)
  have h_ne : D_out1 ≠ D_out2 := T_diag_Gamma0_one_ppow_ne_p_ppow N p hp k hk _ _ _ _
  have h_mul : HeckeRing.T_single (Gamma0_pair N) ℤ D1 1 *
      HeckeRing.T_single (Gamma0_pair N) ℤ D2 1 =
      HeckeRing.m (Gamma0_pair N) (HeckeCoset.rep D1) (HeckeCoset.rep D2) :=
    HeckeRing.T_single_one_mul_T_single_one (Gamma0_pair N) D1 D2
  rw [h_mul]
  show HeckeRing.m (Gamma0_pair N) D1.rep D2.rep =
      HeckeRing.T_single (Gamma0_pair N) ℤ D_out1 1 +
      c • HeckeRing.T_single (Gamma0_pair N) ℤ D_out2 1
  have h_rhs : HeckeRing.T_single (Gamma0_pair N) ℤ D_out1 1 +
      c • HeckeRing.T_single (Gamma0_pair N) ℤ D_out2 1 =
      Finsupp.single D_out1 1 + c • Finsupp.single D_out2 1 := rfl
  rw [h_rhs, Finsupp.smul_single', mul_one]
  apply Finsupp.ext; intro A
  show HeckeRing.heckeMultiplicity (Gamma0_pair N) D1.rep D2.rep (HeckeCoset.rep A) =
    (Finsupp.single D_out1 (1 : ℤ) + Finsupp.single D_out2 c) A
  rw [Finsupp.add_apply]
  by_cases h1 : A = D_out1
  · subst h1
    rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne h_ne, add_zero]
    exact (heckeMultiplicity_Gamma0_values N p hp hpN k hk).1
  · by_cases h2 : A = D_out2
    · subst h2
      rw [Finsupp.single_eq_of_ne (Ne.symm h_ne), Finsupp.single_eq_same, zero_add]
      exact (heckeMultiplicity_Gamma0_values N p hp hpN k hk).2
    · rw [Finsupp.single_eq_of_ne h1, Finsupp.single_eq_of_ne h2, add_zero]
      apply HeckeRing.heckeMultiplicity_eq_zero_of_nmem_mulSupport
      intro hmem
      exact (mulSupport_Gamma0_pp_subset N p hp hpN k hk A hmem).elim h1 h2

private lemma T_diag_Gamma0_eq_one (v : Fin 2 → ℕ) (hv : ∀ i, 0 < v i)
    (hg : Int.gcd (v 0) N = 1) (h_one : (diagMat 2 v : GL (Fin 2) ℚ) = 1) :
    T_diag_Gamma0 N v hv hg = HeckeCoset.one (Gamma0_pair N) := by
  show (⟦⟨diagMat 2 v, _⟩⟧ : HeckeCoset _) = ⟦⟨(1 : GL (Fin 2) ℚ), _⟩⟧
  apply Quotient.sound
  show DoubleCoset.doubleCoset (diagMat 2 v) _ _ = DoubleCoset.doubleCoset 1 _ _
  rw [h_one]

private lemma T_1m_coprime_mem (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (hcop : Nat.Coprime x y)
    (hX : HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, x]) (fun i ↦ by fin_cases i <;> simp [hx]) (by simp)) 1 ∈
      (ψ_hom N).range)
    (hY : HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, y]) (fun i ↦ by fin_cases i <;> simp [hy]) (by simp)) 1 ∈
      (ψ_hom N).range) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, x * y]) (fun i ↦ by fin_cases i <;> simp [Nat.mul_pos hx hy])
        (by simp)) 1 ∈ (ψ_hom N).range := by
  have h_combine := (ψ_hom N).range.mul_mem hX hY
  rwa [T_coprime_mul N x y hx hy hcop] at h_combine

private lemma T_1ppow_coprime_mem (p : ℕ) (hp : p.Prime) (hpN : (p : ℤ).gcd N = 1)
    (k : ℕ) (hk : 2 ≤ k)
    (hIHp : HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, p]) (fun i ↦ by fin_cases i <;> simp [hp.pos]) (by simp)) 1 ∈
      (ψ_hom N).range)
    (hIHpk1 : HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, p^(k-1)]) (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
        (by simp)) 1 ∈ (ψ_hom N).range)
    (hIHpk2 : HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, p^(k-2)]) (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
        (by simp)) 1 ∈ (ψ_hom N).range) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, p^k]) (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
        (by simp)) 1 ∈ (ψ_hom N).range := by
  have hk1_pos : 1 ≤ k - 1 := by omega
  have h_IHpk1_alt : HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, p^((k-1)-1)]) (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
        (by simp)) 1 ∈ (ψ_hom N).range := by
    rw [show k - 1 - 1 = k - 2 by omega]; exact hIHpk2
  have h_Tppk1 := T_p_ppow_mem_ψ_range N p hp hpN (k - 1) hk1_pos h_IHpk1_alt
  have h_formula := Gamma0_T1p_mul_T1ppow_coprime N p hp hpN (k - 1) hk1_pos
  rw [show k - 1 + 1 = k from Nat.sub_add_cancel (by omega : 1 ≤ k)] at h_formula
  rw [eq_sub_of_add_eq h_formula.symm]
  exact (ψ_hom N).range.sub_mem ((ψ_hom N).range.mul_mem hIHp hIHpk1)
    ((ψ_hom N).range.zsmul_mem h_Tppk1 _)

private lemma T_1ppow_bad_mem (p : ℕ) (hp : p.Prime) (hp_dvd_N : p ∣ N) (k : ℕ) (hk : 2 ≤ k)
    (hIHp : HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, p]) (fun i ↦ by fin_cases i <;> simp [hp.pos]) (by simp)) 1 ∈
      (ψ_hom N).range)
    (hIHpk1 : HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, p^(k-1)]) (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
        (by simp)) 1 ∈ (ψ_hom N).range) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, p^k]) (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
        (by simp)) 1 ∈ (ψ_hom N).range := by
  have h_combine := (ψ_hom N).range.mul_mem hIHp hIHpk1
  rw [T_bad_mul N p (p ^ (k - 1)) hp.pos (pow_pos hp.pos _) 1
      (dvd_trans hp_dvd_N (dvd_pow_self N (by omega)))
      (k - 1) (pow_dvd_pow_of_dvd hp_dvd_N (k - 1))] at h_combine
  rwa [T_diag_Gamma0_congr N _ _ _ _
    (show (![1, p * p ^ (k - 1)] : Fin 2 → ℕ) = ![1, p ^ k] by
      rw [show p ^ k = p * p ^ (k - 1) by rw [← pow_succ']; congr 1; omega])] at h_combine

private lemma T_1ppow_mem (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 2 ≤ k)
    (hIH : ∀ x (hx : 0 < x), x < p ^ k → HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, x]) (fun i ↦ by fin_cases i <;> simp [hx]) (by simp)) 1 ∈
      (ψ_hom N).range) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, p^k]) (fun i ↦ by fin_cases i <;> simp [pow_pos hp.pos])
        (by simp)) 1 ∈ (ψ_hom N).range := by
  have hp_lt : p < p ^ k :=
    (pow_one p).symm.trans_lt (Nat.pow_lt_pow_right hp.one_lt hk)
  have hpk1_lt : p ^ (k - 1) < p ^ k := Nat.pow_lt_pow_right hp.one_lt (by omega)
  by_cases hpN : (p : ℤ).gcd N = 1
  · exact T_1ppow_coprime_mem N p hp hpN k hk (hIH p hp.pos hp_lt)
      (hIH (p ^ (k - 1)) (pow_pos hp.pos _) hpk1_lt)
      (hIH (p ^ (k - 2)) (pow_pos hp.pos _) (Nat.pow_lt_pow_right hp.one_lt (by omega)))
  · have hp_dvd_N : p ∣ N := by
      by_contra h
      exact hpN (by rw [Int.gcd_natCast_natCast]; exact hp.coprime_iff_not_dvd.mpr h)
    exact T_1ppow_bad_mem N p hp hp_dvd_N k hk (hIH p hp.pos hp_lt)
      (hIH (p ^ (k - 1)) (pow_pos hp.pos _) hpk1_lt)

private lemma T_1m_composite_mem (m p : ℕ) (hp : p.Prime) (hp_dvd : p ∣ m) (hm : 0 < m)
    (hm_not_ppow : ¬∃ k, m = p ^ k)
    (hIH : ∀ x (hx : 0 < x), x < m → HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, x]) (fun i ↦ by fin_cases i <;> simp [hx]) (by simp)) 1 ∈
      (ψ_hom N).range) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, m]) (fun i ↦ by fin_cases i <;> simp [hm]) (by simp)) 1 ∈
      (ψ_hom N).range := by
  set v := m.factorization p
  set a := p ^ v with ha_def
  set b := m / a with hb_def
  have ha_dvd : a ∣ m := (Nat.Prime.pow_dvd_iff_le_factorization hp (by omega)).mpr le_rfl
  have hab : m = a * b := (Nat.mul_div_cancel' ha_dvd).symm
  have hv_pos : 0 < v := Nat.Prime.factorization_pos_of_dvd hp (by omega) hp_dvd
  have ha_pos : 0 < a := pow_pos hp.pos v
  have hb_pos : 0 < b := Nat.pos_of_ne_zero (by intro hb0; rw [hb0, Nat.mul_zero] at hab; omega)
  have ha_lt : a < m := by
    rw [hab]; refine lt_mul_of_one_lt_right ha_pos ?_
    by_contra! h
    rw [show b = 1 by omega, Nat.mul_one] at hab
    exact hm_not_ppow ⟨v, hab⟩
  have hb_lt : b < m := by
    rw [hab]; exact lt_mul_of_one_lt_left hb_pos (Nat.one_lt_pow hv_pos.ne' hp.one_lt)
  have hcop_ab : Nat.Coprime a b :=
    (Nat.Prime.coprime_pow_of_not_dvd hp
      (by simp [hb_def]; exact Nat.not_dvd_ordCompl hp (by omega))).symm
  rw [T_diag_Gamma0_congr N (fun i ↦ by fin_cases i <;> simp [hm]) (by simp)
    (fun i ↦ by fin_cases i <;> simp [Nat.mul_pos ha_pos hb_pos]) (by simp)
    (show (![1, m] : Fin 2 → ℕ) = ![1, a * b] by rw [hab])]
  exact T_1m_coprime_mem N a b ha_pos hb_pos hcop_ab (hIH a ha_pos ha_lt) (hIH b hb_pos hb_lt)

private lemma T_1m_mem_ψ_range (m : ℕ) (hm : 0 < m) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (![1, m])
        (fun i ↦ by fin_cases i <;> simp [hm])
        (by simp)) 1 ∈ (ψ_hom N).range := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
  by_cases hm1 : m = 1
  · subst hm1; convert (ψ_hom N).range.one_mem using 1
    rw [T_diag_Gamma0_eq_one N _ _ _ (by ext i j; fin_cases i <;> fin_cases j <;>
          simp [diagMat, Matrix.diagonal])]
    exact (HeckeRing.one_def (Gamma0_pair N) (Z := ℤ)).symm
  · obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
    set q := m / p with hq_def
    have hpq : m = p * q := (Nat.mul_div_cancel' hp_dvd).symm
    have hq_pos : 0 < q := Nat.pos_of_ne_zero
      (by intro h; rw [h, Nat.mul_zero] at hpq; omega)
    have hq_lt : q < m := by
      rw [hpq]; exact lt_mul_of_one_lt_left hq_pos hp.one_lt
    by_cases hcop : Nat.Coprime p q
    · by_cases hq1 : q = 1
      · rw [T_diag_Gamma0_congr N (fun i ↦ by fin_cases i <;> simp [hm]) (by simp)
          (fun i ↦ by fin_cases i <;> simp [hp.pos]) (by simp)
          (show (![1, m] : Fin 2 → ℕ) = ![1, p] by rw [hpq, hq1, mul_one])]
        exact T_1p_mem_ψ_range N p hp
      have hp_lt : p < m := by
        rw [hpq]; exact lt_mul_of_one_lt_right hp.pos (by omega)
      rw [T_diag_Gamma0_congr N (fun i ↦ by fin_cases i <;> simp [hm]) (by simp)
        (fun i ↦ by fin_cases i <;> simp [Nat.mul_pos hp.pos hq_pos]) (by simp)
        (show (![1, m] : Fin 2 → ℕ) = ![1, p * q] by rw [hpq])]
      exact T_1m_coprime_mem N p q hp.pos hq_pos hcop (ih p hp_lt hp.pos) (ih q hq_lt hq_pos)
    · by_cases hm_ppow : ∃ k, m = p ^ k
      · obtain ⟨k, rfl⟩ := hm_ppow
        have hk : 2 ≤ k := by
          by_contra! h
          interval_cases k
          · exact hm1 rfl
          · apply hcop
            rw [show q = 1 by rw [hq_def, pow_one, Nat.div_self hp.pos]]
            exact Nat.coprime_one_right p
        exact T_1ppow_mem N p hp k hk (fun x hx hlt ↦ ih x hlt hx)
      · exact T_1m_composite_mem N m p hp hp_dvd hm hm_ppow (fun x hx hlt ↦ ih x hlt hx)

private lemma T_scalar_diag_mem (d : ℕ) (hd : 0 < d) (hd_gcd : Int.gcd (↑d) ↑N = 1) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N (fun _ : Fin 2 ↦ d) (fun _ ↦ hd) hd_gcd) 1 ∈ (ψ_hom N).range := by
  revert hd hd_gcd
  induction d using Nat.strongRecOn with
  | _ d ih =>
  intro hd hd_gcd
  by_cases hd1 : d = 1
  · subst hd1
    convert (ψ_hom N).range.one_mem using 1
    rw [T_diag_Gamma0_eq_one N _ _ _ (by ext i j; fin_cases i <;> fin_cases j <;>
          simp [diagMat, Matrix.diagonal])]
    exact (HeckeRing.one_def (Gamma0_pair N) (Z := ℤ)).symm
  · obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
    have hp_gcd : Int.gcd (↑p) ↑N = 1 := by
      rw [Int.gcd_natCast_natCast] at hd_gcd ⊢
      exact Nat.Coprime.coprime_dvd_left hp_dvd hd_gcd
    have hp_not_dvd_N : ¬(p ∣ N) := fun h ↦ by
      rw [Int.gcd_natCast_natCast] at hp_gcd
      exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, dvd_refl p, h⟩ hp_gcd
    have h_Tpp : HeckeRing.T_single (Gamma0_pair N) ℤ
        (T_diag_Gamma0 N (![p, p]) (fun i ↦ by fin_cases i <;> simp [hp.pos])
          (by show Int.gcd (↑p) ↑N = 1; exact hp_gcd)) 1 ∈ (ψ_hom N).range :=
      ⟨MvPolynomial.X (⟨p, hp⟩, (1 : Fin 2)), by
        show ψ_hom N (MvPolynomial.X (⟨p, hp⟩, (1 : Fin 2))) = _
        letI : CommRing (𝕋 (Gamma0_pair N) ℤ) := instCommRing_Gamma0 N
        refine (MvPolynomial.eval₂Hom_X' _ _ _).trans ?_
        simp only [show (1 : Fin 2) ≠ 0 by omega, ↓reduceIte, dif_neg hp_not_dvd_N]⟩
    rw [T_diag_Gamma0_congr N (fun i ↦ by fin_cases i <;> simp [hp.pos])
      (by show Int.gcd (↑p) ↑N = 1; exact hp_gcd) (fun _ ↦ hp.pos) hp_gcd
      (by funext i; fin_cases i <;> rfl)] at h_Tpp
    set e := d / p with he_def
    have he_pos : 0 < e := Nat.div_pos (Nat.le_of_dvd hd hp_dvd) hp.pos
    have he_mul : d = p * e := (Nat.mul_div_cancel' hp_dvd).symm
    have he_gcd : Int.gcd (↑e) ↑N = 1 := by
      rw [Int.gcd_natCast_natCast] at hd_gcd ⊢
      exact Nat.Coprime.coprime_dvd_left ⟨p, he_mul.trans (mul_comm p e)⟩ hd_gcd
    have h_Te := ih e (by rw [he_mul]; exact lt_mul_of_one_lt_left he_pos hp.one_lt) he_pos he_gcd
    have h_prod := T_Gamma0_scalar_mul_gen N p hp.pos (fun _ : Fin 2 ↦ e)
      (fun _ ↦ he_pos) hp_gcd he_gcd (dvd_refl e)
    have hD_eq' : T_diag_Gamma0 N ((fun _ : Fin 2 ↦ p) * (fun _ : Fin 2 ↦ e))
        (fun i ↦ Nat.mul_pos hp.pos he_pos)
        (by show Int.gcd (↑(p * e)) ↑N = 1; rw [← he_mul]; exact hd_gcd) =
      T_diag_Gamma0 N (fun _ : Fin 2 ↦ d) (fun _ ↦ hd) hd_gcd :=
      T_diag_Gamma0_congr N _ _ _ _ (by ext i; simp [Pi.mul_apply, ← he_mul])
    rw [hD_eq'] at h_prod
    rw [← h_prod]
    exact (ψ_hom N).range.mul_mem h_Tpp h_Te

private lemma T_diag_mem_ψ_range (a : Fin 2 → ℕ)
    (ha : ∀ i, 0 < a i) (hgcd : Int.gcd (a 0) N = 1) (hdiv : a 0 ∣ a 1) :
    HeckeRing.T_single (Gamma0_pair N) ℤ
      (T_diag_Gamma0 N a ha hgcd) 1 ∈ (ψ_hom N).range := by
  by_cases ha1 : a 0 = 1
  · have ha_eq : a = ![1, a 1] := by ext i; fin_cases i <;> simp [ha1]
    rw [T_diag_Gamma0_congr N ha hgcd (fun i ↦ by fin_cases i <;> simp [ha 1]) (by simp) ha_eq]
    exact T_1m_mem_ψ_range N (a 1) (ha 1)
  · set q := a 1 / a 0 with hq_def
    have hq_pos : 0 < q := Nat.div_pos (Nat.le_of_dvd (ha 1) hdiv) (ha 0)
    have hq_mul : a 1 = a 0 * q := (Nat.mul_div_cancel' hdiv).symm
    have h_product := T_Gamma0_scalar_mul N (a 0) q (ha 0) hq_pos hgcd
    have hD_eq : T_diag_Gamma0 N ((fun _ : Fin 2 ↦ a 0) * ![1, q])
        (fun i ↦ Nat.mul_pos (ha 0) (by fin_cases i <;> simp [hq_pos]))
        (by show Int.gcd (↑(a 0 * 1)) ↑N = 1; simp [hgcd]) =
      T_diag_Gamma0 N a ha hgcd :=
      T_diag_Gamma0_congr N _ _ _ _ (by
        ext i; fin_cases i
        · simp [Pi.mul_apply]
        · simp [Pi.mul_apply, hq_mul])
    rw [hD_eq] at h_product
    rw [← h_product]
    exact (ψ_hom N).range.mul_mem (T_scalar_diag_mem N (a 0) (ha 0) hgcd)
      (T_1m_mem_ψ_range N q hq_pos)

private lemma ψ_surjective :
    Function.Surjective (ψ_hom N) := by
  intro y
  induction y using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add f g hf hg =>
    obtain ⟨xf, rfl⟩ := hf; obtain ⟨xg, rfl⟩ := hg
    exact ⟨xf + xg, map_add _ _ _⟩
  | single D c =>
    suffices h : Finsupp.single D 1 ∈ (ψ_hom N).range by
      obtain ⟨x, hx⟩ := h
      refine ⟨c • x, ?_⟩
      rw [map_zsmul, hx]
      show c • Finsupp.single D (1 : ℤ) = Finsupp.single D c
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    obtain ⟨a, ha, hgcd, hdiv, hrep⟩ := Gamma0_exists_diag_rep N (HeckeCoset.rep D)
    have hD : D = T_diag_Gamma0 N a ha hgcd := by
      rw [show D = (⟦HeckeCoset.rep D⟧ : HeckeCoset (Gamma0_pair N)) from
        (Quotient.out_eq D).symm, hrep]
    rw [hD]
    exact T_diag_mem_ψ_range N a ha hgcd hdiv

private noncomputable def shimura_ring_hom :
    HeckeAlgebra 2 →+* HeckeRing.𝕋 (Gamma0_pair N) ℤ :=
  (Ideal.Quotient.lift (RingHom.ker π_hom) (ψ_hom N)
    (fun _ ha ↦ (ker_π_le_ker_ψ N) ha)).comp
    (RingHom.quotientKerEquivOfSurjective π_surjective).symm.toRingHom

private theorem shimura_ring_hom_surjective :
    Function.Surjective (shimura_ring_hom N) :=
  (Ideal.Quotient.lift_surjective_of_surjective (RingHom.ker π_hom)
      (fun _ ha ↦ (ker_π_le_ker_ψ N) ha) (ψ_surjective N)).comp
    (RingHom.quotientKerEquivOfSurjective π_surjective).symm.surjective

/-- **Shimura Theorem 3.35**: There exists a surjective ring homomorphism
    `R(Γ, Δ) →+* R(Γ₀(N), Δ₀(N))`. -/
theorem shimura_thm_3_35 (N : ℕ) [NeZero N] :
    ∃ φ : HeckeRing.𝕋 (GL_pair 2) ℤ →+* HeckeRing.𝕋 (Gamma0_pair N) ℤ,
      Function.Surjective φ :=
  ⟨shimura_ring_hom N, shimura_ring_hom_surjective N⟩

end HeckeRing.GLn

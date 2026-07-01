/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.PrimeDecomposition

/-!
# GL₂ Hecke Algebra: Definitions for Theorem 3.24

Specialization of the GL_n Hecke algebra to n=2. Defines T(a,d), T(m), and
structural lemmas for Shimura's Theorem 3.24.

## Main definitions

* `T_ad` -- `T(a,d)` basis element
* `T_pp` -- scalar double coset `T(p,p)`
* `T_sum` -- Shimura's `T(m) = Σ T(a,d)` over divisor pairs

## Main results

* `T_elem_mul_scalar` -- `T_elem(b) * T_elem(c,c) = T_elem(b * c)`
* `T_pp_comm_T_elem` -- `T(p,p)` commutes with every diagonal `T_elem(a)`
* `T_pp_pow` -- `T(p,p)^i = T_elem(p^i, p^i)`
* `T_sum_ppow_expansion` -- `T(p^k) = Σ_{i ≤ k/2} T(p^i, p^(k-i))`

## References

* Shimura, Theorem 3.24
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset HeckeRing.GLn

open scoped Pointwise

namespace HeckeRing.GL2

/-- `T(a,d)` for n=2: the Hecke basis element for diagonal `(a,d)` with `a | d`.
Returns 0 when `a = 0` or `d = 0` or `a ∤ d`. -/
noncomputable def T_ad (a d : ℕ) : HeckeAlgebra 2 :=
  if _ : 0 < a ∧ 0 < d ∧ a ∣ d then T_elem ![a, d] else 0

/-- `T_ad a d` equals `T_elem ![a, d]` when the positivity and divisibility conditions hold. -/
lemma T_ad_of_pos (a d : ℕ) (ha : 0 < a) (hd : 0 < d) (h : a ∣ d) : T_ad a d = T_elem ![a, d] :=
  dif_pos ⟨ha, hd, h⟩

/-- `T_ad a d` is zero when the positivity or divisibility conditions fail. -/
lemma T_ad_eq_zero {a d : ℕ} (h : ¬(0 < a ∧ 0 < d ∧ a ∣ d)) : T_ad a d = 0 := dif_neg h

/-- `T(p,p)`: the scalar double coset for prime `p`, equal to `T_ad p p`. -/
noncomputable def T_pp (p : ℕ) : HeckeAlgebra 2 := T_ad p p

/-- For `p` prime, `T(p,p)` equals the scalar diagonal element `T_elem(p,p)`. -/
lemma T_pp_of_pos (p : ℕ) (hp : p.Prime) : T_pp p = T_elem (fun _ : Fin 2 ↦ p) :=
  (T_ad_of_pos p p hp.pos hp.pos dvd_rfl).trans
    (T_elem_congr_diag 2 (funext fun i ↦ by fin_cases i <;> rfl))

private lemma T_elem_ones_eq : T_elem (fun _ : Fin 2 ↦ 1) = 1 :=
  congrArg (T_single (GL_pair 2) ℤ · 1) T_diag_ones

/-- T(1,1) is the identity element. -/
@[simp] lemma T_ad_one_one : T_ad 1 1 = 1 :=
  (T_ad_of_pos 1 1 one_pos one_pos dvd_rfl).trans
    ((T_elem_congr_diag 2 (funext fun i ↦ by fin_cases i <;> rfl)).trans T_elem_ones_eq)

/-- `T(m) = Σ_{a | m} T(a, m/a)`. -/
noncomputable def T_sum (m : ℕ+) : HeckeAlgebra 2 := ∑ a ∈ (m : ℕ).divisors, T_ad a ((m : ℕ) / a)

section Structural

variable (p : ℕ) (hp : p.Prime)

private lemma doubleCoset_eq_of_mem' (g δ : GL (Fin 2) ℚ)
    (h : g ∈ DoubleCoset.doubleCoset δ (SLnZ_subgroup 2) (SLnZ_subgroup 2)) :
    DoubleCoset.doubleCoset g (SLnZ_subgroup 2) (SLnZ_subgroup 2) =
      DoubleCoset.doubleCoset δ (SLnZ_subgroup 2) (SLnZ_subgroup 2) := by
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp h
  exact (doubleCoset_mul_right_eq_self (GL_pair 2) ⟨h₂, hh₂⟩ (h₁ * δ)).trans
    (doset_mul_left_eq_self (GL_pair 2) ⟨h₁, hh₁⟩ δ)

/-- For p prime, T(p) = T_ad(1,p). -/
lemma T_sum_prime : T_sum ⟨p, hp.pos⟩ = T_ad 1 p := by
  change ∑ a ∈ p.divisors, T_ad a (p / a) = _
  rw [hp.sum_divisors, Nat.div_self hp.pos, Nat.div_one,
    T_ad_eq_zero (fun ⟨_, _, hdvd⟩ ↦ hp.ne_one (Nat.dvd_one.mp hdvd)), zero_add]

private lemma scalar_product_mem_doubleCoset (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i) (c : ℕ)
    (hc : 0 < c) {x1 x2 : GL (Fin 2) ℚ} (hx1 : x1 ∈ (GL_pair 2).H) (hx2 : x2 ∈ (GL_pair 2).H) :
    x1 * (HeckeCoset.rep (T_diag b) : GL (Fin 2) ℚ) *
        (x2 * (HeckeCoset.rep (T_diag fun _ : Fin 2 ↦ c) : GL (Fin 2) ℚ)) ∈
      DoubleCoset.doubleCoset (diagMat 2 (b * (fun _ ↦ c)) : GL (Fin 2) ℚ) (GL_pair 2).H
        (GL_pair 2).H := by
  obtain ⟨h₁b, hh₁b, h₂b, hh₂b, hδb_eq⟩ := T_diag_rep_decompose b hb_pos
  obtain ⟨h₁c, hh₁c, h₂c, hh₂c, hδc_eq⟩ := T_diag_rep_decompose (fun _ : Fin 2 ↦ c) fun _ ↦ hc
  rw [hδb_eq, hδc_eq, DoubleCoset.mem_doubleCoset]
  refine ⟨x1 * h₁b, mul_mem hx1 hh₁b, h₂b * x2 * h₁c * h₂c,
    mul_mem (mul_mem (mul_mem hh₂b hx2) hh₁c) hh₂c, ?_⟩
  calc x1 * (h₁b * diagMat 2 b * h₂b) * (x2 * (h₁c * diagMat 2 (fun _ ↦ c) * h₂c))
      = x1 * h₁b * (diagMat 2 b * ((h₂b * x2 * h₁c) * diagMat 2 (fun _ ↦ c))) * h₂c := by group
    _ = x1 * h₁b * ((diagMat 2 b * diagMat 2 (fun _ ↦ c)) * (h₂b * x2 * h₁c)) * h₂c := by
      rw [← diagMat_scalar_comm 2 c hc (h₂b * x2 * h₁c)]
      group
    _ = x1 * h₁b * diagMat 2 (b * (fun _ ↦ c)) * (h₂b * x2 * h₁c * h₂c) := by
      rw [diagMat_mul 2 b (fun _ ↦ c) hb_pos fun _ ↦ hc]
      group

private lemma mulMap_right_scalar_eq (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i) (c : ℕ) (hc : 0 < c)
    (p : decompQuot (GL_pair 2) (HeckeCoset.rep (T_diag b)) ×
         decompQuot (GL_pair 2) (HeckeCoset.rep (T_diag (fun _ : Fin 2 ↦ c)))) :
    mulMap (GL_pair 2) (HeckeCoset.rep (T_diag b)) (HeckeCoset.rep (T_diag (fun _ : Fin 2 ↦ c)))
      p = T_diag (b * (fun _ ↦ c)) := by
  have h_mem := scalar_product_mem_doubleCoset b hb_pos c hc
    (SetLike.coe_mem p.1.out) (SetLike.coe_mem p.2.out)
  rw [show (diagMat 2 (b * fun _ ↦ c) : GL (Fin 2) ℚ) =
    ↑(diagMat_delta 2 (b * fun _ ↦ c)) from (diagMat_delta_val 2 _
      fun i ↦ Nat.mul_pos (hb_pos i) hc).symm] at h_mem
  exact HeckeCoset_ext_toSet (P := GL_pair 2) (doubleCoset_eq_of_mem' _ _ h_mem)

private lemma scalar_coset_rep_normalizes (c : ℕ) (hc : 0 < c) :
    let δ_c := (HeckeCoset.rep (T_diag fun _ : Fin 2 ↦ c) : GL (Fin 2) ℚ)
    ({δ_c} : Set (GL (Fin 2) ℚ)) * ((GL_pair 2).H : Set (GL (Fin 2) ℚ)) =
      ((GL_pair 2).H : Set (GL (Fin 2) ℚ)) * {δ_c} := by
  intro δ_c
  obtain ⟨h₁c, hh₁c, h₂c, hh₂c, hδc_eq⟩ := T_diag_rep_decompose (fun _ : Fin 2 ↦ c) fun _ ↦ hc
  have hδc_simp : δ_c = h₁c * h₂c * diagMat 2 (fun _ ↦ c) := by
    change (HeckeCoset.rep (T_diag (fun _ : Fin 2 ↦ c)) : GL (Fin 2) ℚ) = _
    rw [hδc_eq, mul_assoc, diagMat_scalar_comm 2 c hc h₂c, ← mul_assoc]
  have hδc_norm : ConjAct.toConjAct δ_c • (GL_pair 2).H = (GL_pair 2).H := by
    rw [hδc_simp, map_mul, ← smul_smul, conjAct_scalar_smul_eq 2 c hc]
    exact HeckeRing.conjAct_smul_elt_eq _ ⟨h₁c * h₂c, mul_mem hh₁c hh₂c⟩
  have h_norm_coe : ({δ_c} : Set (GL (Fin 2) ℚ)) * ((GL_pair 2).H : Set (GL (Fin 2) ℚ)) *
      {δ_c⁻¹} = ((GL_pair 2).H : Set (GL (Fin 2) ℚ)) := by
    rw [← conjAct_smul_coe_eq, ← Subgroup.coe_pointwise_smul, hδc_norm]
  have h := congrArg (· * {δ_c}) h_norm_coe
  simp only [mul_assoc, Set.singleton_mul_singleton] at h
  simpa using h

private lemma card_decompQuot_scalar (c : ℕ) (hc : 0 < c) :
    Fintype.card (decompQuot (GL_pair 2) (HeckeCoset.rep (T_diag fun _ : Fin 2 ↦ c))) = 1 := by
  simpa [HeckeRing.HeckeCoset_deg] using HeckeCoset_deg_scalar 2 c hc

private lemma mem_mulSupport_right_scalar (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i) (c : ℕ)
    (hc : 0 < c) : T_diag (b * (fun _ ↦ c)) ∈ HeckeRing.mulSupport (GL_pair 2)
      (HeckeCoset.rep (T_diag b)) (HeckeCoset.rep (T_diag (fun _ : Fin 2 ↦ c))) := by
  have ⟨i₀⟩ : Nonempty (decompQuot (GL_pair 2) (HeckeCoset.rep (T_diag b))) :=
    Fintype.card_pos_iff.mp <| by
      simpa [HeckeRing.HeckeCoset_deg] using HeckeRing.HeckeCoset_deg_pos (GL_pair 2) (T_diag b)
  have ⟨j₀⟩ : Nonempty (decompQuot (GL_pair 2) (HeckeCoset.rep (T_diag fun _ : Fin 2 ↦ c))) :=
    Fintype.card_pos_iff.mp (lt_of_lt_of_eq one_pos (card_decompQuot_scalar c hc).symm)
  simp only [HeckeRing.mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
    true_and, Prod.exists]
  exact ⟨i₀, j₀, mulMap_right_scalar_eq b hb_pos c hc (i₀, j₀)⟩

private lemma heckeMultiplicity_right_scalar_le_one (b : Fin 2 → ℕ) (c : ℕ) (hc : 0 < c) :
    HeckeRing.heckeMultiplicity (GL_pair 2) (HeckeCoset.rep (T_diag b))
      (HeckeCoset.rep (T_diag (fun _ : Fin 2 ↦ c)))
      (HeckeCoset.rep (T_diag (b * (fun _ ↦ c)))) ≤ 1 := by
  haveI : Subsingleton (decompQuot (GL_pair 2) (HeckeCoset.rep (T_diag fun _ : Fin 2 ↦ c))) :=
    Fintype.card_le_one_iff_subsingleton.mp (card_decompQuot_scalar c hc).le
  classical
  simp only [HeckeRing.heckeMultiplicity]
  norm_cast
  rw [Nat.card_eq_fintype_card]
  refine Fintype.card_le_one_iff_subsingleton.mpr ⟨fun ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩ ↦ ?_⟩
  obtain rfl : j₁ = j₂ := Subsingleton.elim j₁ j₂
  simp only [Set.mem_setOf_eq] at h₁ h₂
  suffices hi : i₁ = i₂ from hi ▸ rfl
  by_contra hne
  apply HeckeRing.decompQuot_coset_diff (GL_pair 2) (HeckeCoset.rep (T_diag b)) i₁ i₂ hne
  let δ_c := (HeckeCoset.rep (T_diag (fun _ : Fin 2 ↦ c)) : GL (Fin 2) ℚ)
  have h_coset : ({(j₁.out : GL (Fin 2) ℚ) * δ_c} : Set _) * ((GL_pair 2).H : Set _) =
      ((GL_pair 2).H : Set _) * {δ_c} := by
    rw [← Set.singleton_mul_singleton, mul_assoc, scalar_coset_rep_normalizes c hc,
      ← mul_assoc, Subgroup.singleton_mul_subgroup (SetLike.coe_mem j₁.out)]
  have key : ∀ i : decompQuot (GL_pair 2) (HeckeCoset.rep (T_diag b)),
      ({(i.out : GL (Fin 2) ℚ) * (HeckeCoset.rep (T_diag b) : GL (Fin 2) ℚ)} : Set _) *
          {(j₁.out : GL (Fin 2) ℚ) * δ_c} * ((GL_pair 2).H : Set _) =
        ({(i.out : GL (Fin 2) ℚ) * (HeckeCoset.rep (T_diag b) : GL (Fin 2) ℚ)} : Set _) *
          (((GL_pair 2).H : Set _) * {δ_c}) := fun i ↦ by rw [mul_assoc, h_coset]
  have h12' := ((key i₁).symm.trans (h₁.trans h₂.symm)).trans (key i₂)
  rw [← mul_assoc, ← mul_assoc] at h12'
  exact HeckeRing.mul_singleton_right_cancel δ_c _ _ h12'

private lemma heckeMultiplicity_right_scalar_eq_one (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i)
    (c : ℕ) (hc : 0 < c) : HeckeRing.heckeMultiplicity (GL_pair 2) (HeckeCoset.rep (T_diag b))
      (HeckeCoset.rep (T_diag (fun _ : Fin 2 ↦ c)))
      (HeckeCoset.rep (T_diag (b * (fun _ ↦ c)))) = 1 :=
  HeckeRing.heckeMultiplicity_eq_one_of_le_one_and_pos (GL_pair 2) _ _ _
    (heckeMultiplicity_right_scalar_le_one b c hc)
    (HeckeRing.heckeMultiplicity_pos_of_mem (GL_pair 2) _ _ _
      (mem_mulSupport_right_scalar b hb_pos c hc))

private lemma heckeMultiplicity_right_scalar_eq_zero (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i)
    (c : ℕ) (hc : 0 < c) (A : HeckeCoset (GL_pair 2)) (hA : A ≠ T_diag (b * (fun _ : Fin 2 ↦ c))) :
    HeckeRing.heckeMultiplicity (GL_pair 2) (HeckeCoset.rep (T_diag b))
      (HeckeCoset.rep (T_diag (fun _ : Fin 2 ↦ c))) (HeckeCoset.rep A) = 0 := by
  refine HeckeRing.heckeMultiplicity_eq_zero_of_nmem_mulSupport _ _ _ _ fun h_mem ↦ ?_
  simp only [HeckeRing.mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
    true_and] at h_mem
  exact h_mem.elim fun ⟨i, j⟩ heq ↦
    hA (heq.symm.trans (mulMap_right_scalar_eq b hb_pos c hc (i, j)))

/-- Multiplication by a scalar diagonal element: `T_elem(b) * T_elem(c,c) = T_elem(b * c)`. -/
theorem T_elem_mul_scalar (b : Fin 2 → ℕ) (hb_pos : ∀ i, 0 < b i) (_hb : DivChain 2 b) (c : ℕ)
    (hc : 0 < c) : T_elem b * T_elem (fun _ : Fin 2 ↦ c) = T_elem (b * (fun _ ↦ c)) := by
  set D_b := T_diag b
  set D_c := T_diag (fun _ : Fin 2 ↦ c)
  set D_bc := T_diag (b * (fun _ : Fin 2 ↦ c))
  change T_single (GL_pair 2) ℤ D_b 1 * T_single (GL_pair 2) ℤ D_c 1 =
    T_single (GL_pair 2) ℤ D_bc 1
  rw [HeckeRing.T_single_one_mul_T_single_one]
  refine Finsupp.ext fun A ↦ ?_
  simp only [HeckeRing.m, Finsupp.coe_mk, HeckeRing.T_single]
  by_cases h1 : A = D_bc
  · subst h1
    norm_num [Finsupp.single_apply]
    exact heckeMultiplicity_right_scalar_eq_one b hb_pos c hc
  · norm_num [Finsupp.single_apply, h1]
    exact heckeMultiplicity_right_scalar_eq_zero b hb_pos c hc A h1

/-- `T(p,p)` commutes with every diagonal element `T_elem(a)` for `p` prime. -/
lemma T_pp_comm_T_elem (p : ℕ) (hp : p.Prime) (a : Fin 2 → ℕ) (ha_pos : ∀ i, 0 < a i)
    (ha : DivChain 2 a) : T_pp p * T_elem a = T_elem a * T_pp p := by
  rw [T_pp_of_pos p hp, T_diag_scalar_mul 2 p hp.pos a ha_pos ha,
    T_elem_mul_scalar a ha_pos ha p hp.pos]
  exact (T_elem_congr_diag 2 (mul_comm a fun _ ↦ p)).symm

include hp in
/-- `T(p,p)^i = T_elem(p^i, p^i)`: the `i`-th power of the scalar double coset. -/
lemma T_pp_pow (i : ℕ) : T_pp p ^ i = T_elem (fun _ : Fin 2 ↦ p ^ i) := by
  induction i with
  | zero =>
    rw [pow_zero]
    exact ((T_elem_congr_diag 2 (funext fun _ ↦ by simp)).trans T_elem_ones_eq).symm
  | succ i ih =>
    rw [pow_succ', ih, T_pp_of_pos p hp, T_diag_scalar_mul 2 p hp.pos (fun _ ↦ p ^ i)
      (fun _ ↦ pow_pos hp.pos i) (divChain_const 2 _)]
    exact T_elem_congr_diag 2 (funext fun _ ↦ by simp [Pi.mul_apply, pow_succ, mul_comm])

/-- Expand `T(p^k)` as a sum over divisor pairs with non-zero `T_ad` terms. -/
lemma T_sum_ppow_expansion (k : ℕ) : T_sum ⟨p ^ k, pow_pos hp.pos k⟩ =
    ∑ i ∈ Finset.range (k / 2 + 1), T_ad (p ^ i) (p ^ (k - i)) := by
  change ∑ a ∈ (p ^ k).divisors, T_ad a (p ^ k / a) = _
  rw [Nat.sum_divisors_prime_pow hp, Finset.sum_congr rfl
    (g := fun j ↦ T_ad (p ^ j) (p ^ (k - j))) fun j hj ↦ by
    rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hp.pos]]
  exact (Finset.sum_subset (Finset.range_mono (by lia)) fun j hj hnj ↦ by
    simp only [Finset.mem_range] at hj hnj
    exact T_ad_eq_zero fun ⟨_, _, hdvd⟩ ↦ absurd (Nat.le_of_dvd (pow_pos hp.pos _) hdvd)
      (not_le_of_gt (Nat.pow_lt_pow_right hp.one_lt (by lia)))).symm

end Structural

end HeckeRing.GL2

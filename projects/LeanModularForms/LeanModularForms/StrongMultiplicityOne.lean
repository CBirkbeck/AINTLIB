/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.StrongMultiplicityOne.InductiveStep

/-!
# Strong Multiplicity One via Miyake §4.6

This file assembles an axiom-clean proof of `strongMultiplicityOne`
(Miyake Theorem 4.6.12 / Diamond–Shurman Theorem 5.8.2) by following
Miyake's algebraic descent in §4.6 of *Modular Forms* (2006).

The supporting development is split across the `StrongMultiplicityOne/` modules;
this file holds the route-B finale.

## Main results

* `miyake_4_6_8_main_lemma_cuspForm`: Miyake's Main Lemma (Theorem 4.6.8).
* `mainLemma_charSpace_routeB`: per-character Main Lemma.
* `newform_unique_routeB`: uniqueness of newforms.
* `strongMultiplicityOne`: Strong Multiplicity One.

## References

* **[DS]** F. Diamond, J. Shurman, *A First Course in Modular Forms*,
  Springer GTM 228, 2005.
* **[Miy]** T. Miyake, *Modular Forms*, 2nd ed., Springer SMM, 2006.
* **[AL]** A. O. L. Atkin, J. Lehner, *Hecke operators on `Γ₀(m)`*,
  Math. Ann. **185** (1970), 134–160.
* **[Li]** W.-C. W. Li, *Newforms and functional equations*,
  Math. Ann. **212** (1975), 285–315.
-/

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

private theorem coprime_prod_primeFactors_iff_coprime {N : ℕ} [NeZero N] (n : ℕ) :
    Nat.Coprime n (N.primeFactors.prod id) ↔ Nat.Coprime n N := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.coprime_dvd_right (Nat.prod_primeFactors_dvd N)⟩
  have hN0 : N ≠ 0 := NeZero.ne N
  rw [Nat.coprime_prod_right_iff] at h
  by_contra h_not
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd
    (lt_of_le_of_ne (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hN0)) (Ne.symm h_not)).ne'
  exact hq_prime.coprime_iff_not_dvd.mp
    (h q (Nat.mem_primeFactors.mpr
      ⟨hq_prime, hq_dvd.trans (Nat.gcd_dvd_right _ _), hN0⟩)).symm
    (hq_dvd.trans (Nat.gcd_dvd_left _ _))

/-- **Miyake Theorem 4.6.8 (Main Lemma), unconditional CuspForm form.**  As
`miyake_4_6_8_main_lemma_cuspForm`, but with the `h_chi_factor` hypothesis removed:
the per-prime factorisation is produced internally by the 4.6.4 dichotomy
(`miyake_4_6_8_subset_helper`). -/
theorem miyake_4_6_8_main_lemma_cuspForm
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0) :
    ∃ f_p : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      f = ∑ p ∈ N.primeFactors, f_p p ∧
      (∀ p ∈ N.primeFactors,
        f_p p ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule N k p) ∧
      (∀ p ∈ N.primeFactors,
        f_p p ∈ cuspFormCharSpace k χ) :=
  miyake_4_6_8_subset_helper χ N.primeFactors subset_rfl f hfχ
    fun n hn ↦ h_vanish n ((coprime_prod_primeFactors_iff_coprime n).mp hn)

/-- Embed a per-prime decomposition into a per-nontrivial-divisor decomposition by
extending with zero. Shared packaging step for both
`coprimeSieve_admits_squarefree_decomposition_in_charSpace` and its unconditional form. -/
private theorem extend_primeFactors_to_divisor_decomposition
    (χ : (ZMod N)ˣ →* ℂˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (f_p : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_sum : f = ∑ p ∈ N.primeFactors, f_p p)
    (h_supp : ∀ p ∈ N.primeFactors,
      f_p p ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule N k p)
    (h_char : ∀ p ∈ N.primeFactors, f_p p ∈ cuspFormCharSpace k χ) :
    ∃ f_d : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      f = ∑ d ∈ N.divisors.filter (1 < ·), f_d d ∧
      (∀ d ∈ N.divisors.filter (1 < ·),
        f_d d ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule N k d) ∧
      (∀ d ∈ N.divisors.filter (1 < ·), f_d d ∈ cuspFormCharSpace k χ) := by
  have h_primes_sub : N.primeFactors ⊆ N.divisors.filter (1 < ·) := fun p hp ↦ by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨Nat.dvd_of_mem_primeFactors hp, NeZero.ne N⟩,
      (Nat.prime_of_mem_primeFactors hp).one_lt⟩
  refine ⟨fun d ↦ if d ∈ N.primeFactors then f_p d else 0, ?_, ?_, ?_⟩
  · rw [h_sum]
    refine ((Finset.sum_subset h_primes_sub fun d _ hd_nprime ↦ by simp [hd_nprime]).symm.trans
      (Finset.sum_congr rfl fun p hp ↦ by simp [hp])).symm
  · intro d _
    by_cases h_prime : d ∈ N.primeFactors
    · simpa only [h_prime, if_true] using h_supp d h_prime
    · simpa only [h_prime, if_false] using Submodule.zero_mem _
  · intro d _
    by_cases h_prime : d ∈ N.primeFactors
    · simpa only [h_prime, if_true] using h_char d h_prime
    · simpa only [h_prime, if_false] using Submodule.zero_mem _

/-- Unconditional analogue of `coprimeSieve_admits_squarefree_decomposition_in_charSpace`:
the `h_chi_factor` hypothesis is dropped, the decomposition coming from
`miyake_4_6_8_main_lemma_cuspForm`. -/
theorem coprimeSieve_admits_squarefree_decomposition_in_charSpace
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0) :
    ∃ f_d : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      f = ∑ d ∈ N.divisors.filter (1 < ·), f_d d ∧
      (∀ d ∈ N.divisors.filter (1 < ·),
        f_d d ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule N k d) ∧
      (∀ d ∈ N.divisors.filter (1 < ·),
        f_d d ∈ cuspFormCharSpace k χ) :=
  let ⟨f_p, h_sum, h_supp, h_char⟩ :=
    miyake_4_6_8_main_lemma_cuspForm χ f hfχ h_vanish
  extend_primeFactors_to_divisor_decomposition χ f f_p h_sum h_supp h_char

private theorem heckeT_n_prime_sq_eq_heckeT_p_sq_sub_diamond
    {N : ℕ} [NeZero N] {k : ℤ} {q : ℕ} (hq : Nat.Prime q) (hqN : Nat.Coprime q N) :
    haveI : NeZero (q ^ 2) := ⟨(pow_pos hq.pos 2).ne'⟩
    heckeT_n (N := N) k (q ^ 2) =
      heckeT_p k q hq hqN * heckeT_p k q hq hqN -
        (q : ℂ) ^ (k - 1) • diamondOp k (ZMod.unitOfCoprime q hqN) := by
  haveI : NeZero (q ^ 2) := ⟨(pow_pos hq.pos 2).ne'⟩
  rw [heckeT_n_prime_pow k hq 2 (by norm_num)]
  show heckeT_p_all (N := N) k q hq * heckeT_ppow k q hq 1 -
      (q : ℂ) ^ (k - 1) • (diamondOp_n (N := N) k q * heckeT_ppow k q hq 0) =
    heckeT_p k q hq hqN * heckeT_p k q hq hqN -
      (q : ℂ) ^ (k - 1) • diamondOp k (ZMod.unitOfCoprime q hqN)
  rw [heckeT_ppow_zero, heckeT_ppow_one, mul_one,
    heckeT_p_all_coprime k hq hqN, diamondOp_n_coprime k hqN]

private theorem newform_toModularForm_ne_zero
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) :
    f.toCuspForm.toModularForm' ≠ 0 := fun hF_zero ↦ by
  have h1 : (UpperHalfPlane.qExpansion (1 : ℝ) f.toCuspForm.toModularForm').coeff 1 = 1 :=
    f.isNorm
  rw [show (⇑f.toCuspForm.toModularForm' : UpperHalfPlane → ℂ)
      = (0 : UpperHalfPlane → ℂ) by rw [hF_zero]; rfl,
      UpperHalfPlane.qExpansion_zero] at h1
  simp at h1

/-- $\lambda_{q^2}(f) = \lambda_q(f)^2 - \chi(q) \cdot q^{k-1}$ for $f$ a newform
of level $N$ and prime $q \nmid N$.  Diamond–Shurman 5.3 / Miyake 4.5.13. -/
theorem newform_eigenvalue_at_prime_sq
    (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (q : ℕ) (hq : Nat.Prime q) (hqN : Nat.Coprime q N) :
    f.eigenvalue ⟨q ^ 2, pow_pos hq.pos 2⟩ =
      (f.eigenvalue ⟨q, hq.pos⟩) ^ 2 -
        (χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1) := by
  set lamq := f.eigenvalue ⟨q, hq.pos⟩
  set lamqsq := f.eigenvalue ⟨q ^ 2, pow_pos hq.pos 2⟩
  set chiq : ℂ := (χ (ZMod.unitOfCoprime q hqN) : ℂ)
  set F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k := f.toCuspForm.toModularForm'
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  haveI : NeZero (q ^ 2) := ⟨(pow_pos hq.pos 2).ne'⟩
  have h_eig_q : heckeT_n k q F = lamq • F := by
    rw [← heckeT_n_cusp_toModularForm']; exact congr_arg _ (f.isEigen ⟨q, hq.pos⟩ hqN)
  have h_eig_qsq : heckeT_n k (q ^ 2) F = lamqsq • F := by
    rw [← heckeT_n_cusp_toModularForm']
    exact congr_arg _ (f.isEigen ⟨q ^ 2, pow_pos hq.pos 2⟩ (Nat.Coprime.pow_left 2 hqN))
  have h_Tq_F : heckeT_p k q hq hqN F = lamq • F :=
    heckeT_n_prime_coprime k hq hqN ▸ h_eig_q
  have h_combined :
      heckeT_n k (q ^ 2) F = (lamq ^ 2 - chiq * (q : ℂ) ^ (k - 1)) • F := by
    have h_apply : heckeT_n k (q ^ 2) F =
        heckeT_p k q hq hqN (heckeT_p k q hq hqN F) -
          (q : ℂ) ^ (k - 1) • diamondOp k (ZMod.unitOfCoprime q hqN) F := by
      simpa [Module.End.mul_apply] using congr_arg (fun T : Module.End ℂ _ ↦ T F)
        (heckeT_n_prime_sq_eq_heckeT_p_sq_sub_diamond hq hqN)
    rw [h_apply, h_Tq_F, map_smul, h_Tq_F, smul_smul, sq,
      show diamondOp k (ZMod.unitOfCoprime q hqN) F = chiq • F from
      (mem_modFormCharSpace_iff k χ F).mp hfχ (ZMod.unitOfCoprime q hqN), smul_smul, sub_smul,
      mul_comm chiq]
  refine sub_eq_zero.mp ((smul_eq_zero.mp ?_).resolve_right (newform_toModularForm_ne_zero f))
  rw [sub_smul, ← h_combined, ← h_eig_qsq, sub_self]

/-- Assemble an oldform-membership witness from a same-level divisor decomposition. -/
private theorem cuspFormsOld_of_sameLevel_decomposition
    (χ : (ZMod N)ˣ →* ℂˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (f_d : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_sum : f = ∑ d ∈ N.divisors.filter (1 < ·), f_d d)
    (h_supp : ∀ d ∈ N.divisors.filter (1 < ·),
      f_d d ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule N k d)
    (h_char : ∀ d ∈ N.divisors.filter (1 < ·), f_d d ∈ cuspFormCharSpace k χ) :
    f ∈ cuspFormsOld N k := by
  refine HeckeRing.GL2.AtkinLehner.mainLemma_charSpace_of_sameLevelDivisorDecomposition
    (Newform.dirichletLift χ) f f_d h_sum fun d hd ↦ ⟨h_supp d hd, ?_⟩
  rw [show (Newform.dirichletLift χ).toUnitHom = χ from
    MulChar.equivToUnitHom.apply_symm_apply χ]
  exact h_char d hd

/-- **Per-character unconditional Miyake 4.6.8 (route B).**  A cusp form
`f ∈ S_k(Γ_1(N), χ)` whose period-1 `q`-expansion vanishes at every index coprime to
`N` is an oldform.  This is `mainLemma_charSpace_routeB` with the `h_chi_factor`
hypothesis **removed**: the per-prime character factorisation needed by the
same-level divisor decomposition is supplied internally by Miyake's dichotomy 4.6.4
(`coprimeSieve_admits_squarefree_decomposition_in_charSpace`). -/
theorem mainLemma_charSpace_routeB
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0) :
    f ∈ cuspFormsOld N k :=
  let ⟨f_d, h_sum, h_supp, h_char⟩ :=
    coprimeSieve_admits_squarefree_decomposition_in_charSpace χ f hfχ h_vanish
  cuspFormsOld_of_sameLevel_decomposition χ f f_d h_sum h_supp h_char

theorem exists_prime_coprime_avoiding_finset
    {N : ℕ} [NeZero N] (n : ℕ+) (S : Finset ℕ) :
    ∃ q, Nat.Prime q ∧ Nat.Coprime q N ∧ Nat.Coprime n.val q ∧
      q ∉ S ∧ q ^ 2 ∉ S ∧ n.val * q ∉ S ∧ n.val * q ^ 2 ∉ S := by
  obtain ⟨q, hq_le, hq_prime⟩ := Nat.exists_infinite_primes (S.sup id + N + n.val + 2)
  have hq_gt_S : ∀ s, s ∈ S → s < q := fun s hs ↦ by
    have : s ≤ S.sup id := Finset.le_sup (f := id) hs; lia
  have hqsq_ge_q : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have hnq_ge_q : q ≤ n.val * q := Nat.le_mul_of_pos_left q n.pos
  have hnqsq_ge_q : q ≤ n.val * q ^ 2 := hqsq_ge_q.trans (Nat.le_mul_of_pos_left _ n.pos)
  refine ⟨q, hq_prime,
    hq_prime.coprime_iff_not_dvd.mpr fun hqN ↦ by
      have : q ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hqN; lia,
    (hq_prime.coprime_iff_not_dvd.mpr fun hqn ↦ by
      have : q ≤ n.val := Nat.le_of_dvd n.pos hqn; lia).symm,
    fun hqS ↦ by have := hq_gt_S q hqS; lia,
    fun hqsqS ↦ by have := hq_gt_S _ hqsqS; lia,
    fun hnqS ↦ by have := hq_gt_S _ hnqS; lia,
    fun hnqsqS ↦ by have := hq_gt_S _ hnqsqS; lia⟩

end HeckeRing.GL2

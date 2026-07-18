/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.Newforms.AdjointTheoryBadPrime
import LeanModularForms.HeckeRIngs.GL2.Newforms.MainLemmaProof
import LeanModularForms.Modularforms.QExpansionSlash

/-!
# Newforms are full eigenforms (Diamond–Shurman Theorem 5.8.2(a))

A `Newform N k` is an eigenform for the Hecke operators `T_n` at **every** index `n` (not only the
good indices `(n, N) = 1`).  The bad-prime eigen-property is the only nontrivial content, and DS
Theorem 5.8.2(a) proves it elementarily from the Atkin–Lehner **Main Lemma** (`mainLemma`):
for a bad prime `p`, the auxiliary form `g_p = U_p f − a_p(f) · f` lies in the new subspace, has
vanishing prime-to-`N` Fourier coefficients (so it is old by the Main Lemma), hence lies in
`new ⊓ old = {0}`, i.e. `U_p f = a_p(f) · f`.

## Main results

* `Newform.isFullEigenform` — a `Newform` is a `T_n`-eigenform for all `n`.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm UpperHalfPlane
open scoped MatrixGroups ModularForm Pointwise

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **[T006-a]** Bad-prime `U_p` Fourier relation at the cusp level: for a prime `p ∣ N`, the
`l`-th canonical Fourier coefficient of `T_p f = U_p f` is `a_{pl}(f)`. -/
lemma heckeT_n_cusp_divN_coeff (p : ℕ) [NeZero p] (hp : Nat.Prime p)
    (hpN : ¬ Nat.Coprime p N) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (l : ℕ) :
    (qExpansion (1 : ℝ) (heckeT_n_cusp k p f)).coeff l =
      (qExpansion (1 : ℝ) f).coeff (p * l) := by
  have hForm : (heckeT_n_cusp k p f).toModularForm' =
      heckeT_p_divN k p hp hpN f.toModularForm' := by
    rw [heckeT_n_cusp_toModularForm', heckeT_n_prime k hp,
      show heckeT_p_all k p hp = heckeT_p_divN k p hp hpN from dif_neg hpN]
  have hfun : (⇑(heckeT_n_cusp k p f) : UpperHalfPlane → ℂ) =
      ⇑(heckeT_p_divN k p hp hpN f.toModularForm') := by
    rw [show (⇑(heckeT_n_cusp k p f) : UpperHalfPlane → ℂ) =
        ⇑(heckeT_n_cusp k p f).toModularForm' from rfl, hForm]
  rw [show (qExpansion (1 : ℝ) (heckeT_n_cusp k p f)) =
      qExpansion (1 : ℝ) (heckeT_p_divN k p hp hpN f.toModularForm') from by rw [hfun],
    qExpansion_one_heckeT_p_divN_coeff hp hpN]
  rfl

omit [NeZero N] in
/-- Additivity of the canonical (period-1) `q`-coefficient over a cusp-form difference. -/
private lemma qExpansion_sub_coeff
    (a b : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    (PowerSeries.coeff n) (qExpansion (1 : ℝ) (⇑(a - b) : UpperHalfPlane → ℂ)) =
      (PowerSeries.coeff n) (qExpansion (1 : ℝ) (⇑a : UpperHalfPlane → ℂ)) -
      (PowerSeries.coeff n) (qExpansion (1 : ℝ) (⇑b : UpperHalfPlane → ℂ)) := by
  have h1 := one_mem_strictPeriods_Gamma1_map N
  have h_sub_qexp : qExpansion (1 : ℝ) (a - b) =
      qExpansion (1 : ℝ) a - qExpansion (1 : ℝ) b := by
    rw [sub_eq_add_neg, sub_eq_add_neg, ← ModularForm.qExpansion_neg one_pos h1 b]
    exact ModularForm.qExpansion_add (Γ := (Gamma1 N).map (mapGL ℝ))
      (h := (1 : ℝ)) (a := k) (b := k) one_pos h1 a (- b)
  rw [show qExpansion (1 : ℝ) (⇑(a - b) : UpperHalfPlane → ℂ) =
    qExpansion (1 : ℝ) (a - b) from rfl, h_sub_qexp, map_sub]

omit [NeZero N] in
/-- Scalar multiplication of the canonical (period-1) `q`-coefficient of a cusp form. -/
private lemma qExpansion_smul_coeff (c : ℂ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    (PowerSeries.coeff n) (qExpansion (1 : ℝ) (⇑(c • f) : UpperHalfPlane → ℂ)) =
      c * (PowerSeries.coeff n) (qExpansion (1 : ℝ) (⇑f : UpperHalfPlane → ℂ)) := by
  change (qExpansion (1 : ℝ) (c • f.toModularForm')).coeff n =
    c * (qExpansion (1 : ℝ) (⇑f : UpperHalfPlane → ℂ)).coeff n
  rw [ModularForm.qExpansion_smul (F := ModularForm ((Gamma1 N).map (mapGL ℝ)) k) one_pos
    (one_mem_strictPeriods_Gamma1_map N) c f.toModularForm',
    PowerSeries.coeff_smul, smul_eq_mul]
  rfl

/-- **[T006-b]** A bad prime `p ∣ N` preserves the extended new subspace.
Proved in `Newforms/AdjointTheoryBadPrime.lean` via the bad-prime `U_p` Petersson-adjoint
chain (Diamond–Shurman Prop 5.6.2). -/
theorem heckeT_n_cusp_preserves_cuspFormsNewExtended_bad
    (p : ℕ) [NeZero p] (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ cuspFormsNewExtended N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNewExtended N k :=
  heckeT_n_cusp_preserves_cuspFormsNewExtended_bad' p hp hpN f hf

/-- **[T006-c]** At a bad prime `p ∣ N`, a newform is a `T_p`-eigenform with eigenvalue the
`p`-th Fourier coefficient: `U_p f = a_p(f) · f` (Diamond–Shurman Theorem 5.8.2(a)). -/
theorem Newform.heckeT_n_cusp_bad_prime_eq (f : Newform N k)
    (p : ℕ) [NeZero p] (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) :
    heckeT_n_cusp k p f.toCuspForm =
      (qExpansion (1 : ℝ) f.toCuspForm).coeff p • f.toCuspForm := by
  have hpdvdN : p ∣ N := by
    by_contra h; exact hpN (hp.coprime_iff_not_dvd.mpr h)
  have hN2 : 2 ≤ N := le_trans hp.two_le
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hpdvdN)
  set ap : ℂ := (qExpansion (1 : ℝ) f.toCuspForm).coeff p with hap
  set g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
    heckeT_n_cusp k p f.toCuspForm - ap • f.toCuspForm with hg
  -- (1) prime-to-`N` Fourier coefficients of `g` vanish
  have hvanish : ∀ l : ℕ, Nat.Coprime l N → (qExpansion (1 : ℝ) g).coeff l = 0 := by
    intro l hl
    have hl0 : l ≠ 0 := by rintro rfl; rw [Nat.coprime_zero_left] at hl; omega
    haveI : NeZero l := ⟨hl0⟩
    have hlpos : 0 < l := Nat.pos_of_ne_zero hl0
    have hpl : Nat.Coprime p l := Nat.Coprime.coprime_dvd_left hpdvdN hl.symm
    -- the good Fourier formula `T_l f = a_l f` read off at coefficient `p`
    have heig : heckeT_n_cusp k l f.toCuspForm
        = (qExpansion (1 : ℝ) f.toCuspForm).coeff l • f.toCuspForm := by
      have h := f.isEigen ⟨l, hlpos⟩ hl
      rwa [Newform.eigenvalue_eq_coeff f ⟨l, hlpos⟩ hl f.χ f.mem_charSpace] at h
    -- multiplicativity `a_{pl}(f) = a_l(f) · a_p(f)` (good Fourier formula at coeff `p`)
    have hmult : (qExpansion (1 : ℝ) f.toCuspForm).coeff (p * l)
        = (qExpansion (1 : ℝ) f.toCuspForm).coeff l * ap := by
      have hFour := fourierCoeff_heckeT_n_period_one (N := N) k l hl f.χ f.mem_charSpace p
      have hunit : ZMod.unitOfCoprime 1 (Nat.coprime_one_left N) = 1 := by
        ext; simp [ZMod.coe_unitOfCoprime]
      rw [show Nat.gcd p l = 1 from hpl, Nat.divisors_one, Finset.sum_singleton,
        dif_pos (Nat.coprime_one_left N)] at hFour
      simp only [hunit, Nat.cast_one, one_zpow, map_one, Units.val_one, mul_one, Nat.div_one,
        one_mul] at hFour
      have hLHS : (qExpansion (1 : ℝ) f.toCuspForm).coeff (p * l)
          = (qExpansion (1 : ℝ) (heckeT_n_cusp k l f.toCuspForm)).coeff p := hFour.symm
      rw [hLHS, heig, qExpansion_smul_coeff]
    rw [hg, qExpansion_sub_coeff, qExpansion_smul_coeff,
      heckeT_n_cusp_divN_coeff p hp hpN f.toCuspForm l, hmult]
    ring
  -- (2) `g` is old by the Main Lemma; (3) `g` is new (extended); (4) so `g = 0`
  have hg_old : g ∈ cuspFormsOldExtended N k :=
    cuspFormsOld_le_cuspFormsOldExtended (mainLemma g hvanish)
  have hg_new : g ∈ cuspFormsNewExtended N k := by
    rw [hg]
    exact (cuspFormsNewExtended N k).sub_mem
      (heckeT_n_cusp_preserves_cuspFormsNewExtended_bad p hp hpN f.toCuspForm f.isNew)
      ((cuspFormsNewExtended N k).smul_mem ap f.isNew)
  have hg0 : g = 0 :=
    (Submodule.disjoint_def.mp cuspFormsOldExtended_disjoint_cuspFormsNewExtended) g hg_old hg_new
  rwa [hg, sub_eq_zero] at hg0

/-- At a bad prime `p ∣ N`, `T_{p^v} f = a_p(f)^v · f` for a newform `f`. -/
private lemma Newform.heckeT_ppow_bad_smul (f : Newform N k)
    (p : ℕ) (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) (v : ℕ) :
    haveI : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
    heckeT_n_cusp k (p ^ v) f.toCuspForm =
      (qExpansion (1 : ℝ) f.toCuspForm).coeff p ^ v • f.toCuspForm := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  induction v with
  | zero => simpa using heckeT_n_cusp_one f.toCuspForm
  | succ w ih =>
    haveI : NeZero (p ^ (w + 1)) := ⟨(pow_pos hp.pos _).ne'⟩
    haveI : NeZero (p ^ w) := ⟨(pow_pos hp.pos _).ne'⟩
    have hpow_all : ∀ r : ℕ, heckeT_n (N := N) k (p ^ r) =
        haveI : NeZero (p ^ r) := ⟨(pow_pos hp.pos r).ne'⟩
        heckeT_p_all k p hp ^ r := by
      intro r
      cases r with
      | zero => simp [heckeT_n_one]
      | succ r' =>
        haveI : NeZero (p ^ (r' + 1)) := ⟨(pow_pos hp.pos _).ne'⟩
        rw [heckeT_n_prime_pow k hp (r' + 1) (Nat.succ_pos _),
          heckeT_ppow_eq_pow_of_not_coprime k hp hpN (r' + 1)]
    have hmul : heckeT_n (N := N) k (p ^ (w + 1)) = heckeT_n k p * heckeT_n k (p ^ w) := by
      rw [hpow_all (w + 1), hpow_all w, heckeT_n_prime k hp, pow_succ']
    rw [heckeT_n_cusp_decomp_of_mul p (p ^ w) (p ^ (w + 1)) hmul, ih,
      heckeT_n_cusp_smul, f.heckeT_n_cusp_bad_prime_eq p hp hpN, smul_smul, pow_succ]

/-- **[T006-d]** Every Hecke operator `T_n` acts on a newform by a scalar. -/
theorem Newform.exists_heckeT_n_cusp_smul (f : Newform N k) (n : ℕ) [NeZero n] :
    ∃ c : ℂ, heckeT_n_cusp k n f.toCuspForm = c • f.toCuspForm := by
  suffices key : ∀ m : ℕ, (hm : m ≠ 0) →
      haveI : NeZero m := ⟨hm⟩
      ∃ c : ℂ, heckeT_n_cusp k m f.toCuspForm = c • f.toCuspForm by
    exact key n (NeZero.ne n)
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro hm0
  haveI : NeZero m := ⟨hm0⟩
  by_cases hm1 : m = 1
  · subst hm1
    exact ⟨1, by rw [heckeT_n_cusp_one, one_smul]⟩
  · have hm_gt : 1 < m := by omega
    set p := m.minFac with hp_def
    have hp : Nat.Prime p := Nat.minFac_prime (by omega)
    set v := m.factorization p with hv_def
    have hv_pos : 0 < v := hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd m)
    have hdiv_pos : 0 < m / p ^ v :=
      Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p)) (pow_pos hp.pos v)
    haveI : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
    haveI : NeZero (m / p ^ v) := ⟨hdiv_pos.ne'⟩
    -- decompose `T_m = T_{p^v} ∘ T_{m/p^v}` and recurse on the smaller coprime cofactor
    have hmul : heckeT_n (N := N) k m = heckeT_n k (p ^ v) * heckeT_n k (m / p ^ v) :=
      heckeT_n_mul_ppow_quot (N := N) (k := k) m hm_gt p hp hp_def v hv_def hv_pos hdiv_pos
    obtain ⟨cq, hcq⟩ := ih (m / p ^ v) (heckeT_n_unfold_lt m hm_gt) hdiv_pos.ne'
    -- prime-power factor acts by a scalar (good: `isEigen`; bad: `heckeT_ppow_bad_smul`)
    obtain ⟨cp, hcp⟩ : ∃ cp : ℂ, heckeT_n_cusp k (p ^ v) f.toCuspForm = cp • f.toCuspForm := by
      by_cases hpN : Nat.Coprime p N
      · exact ⟨f.eigenvalue ⟨p ^ v, pow_pos hp.pos v⟩,
          f.isEigen ⟨p ^ v, pow_pos hp.pos v⟩ (hpN.pow_left v)⟩
      · exact ⟨_, f.heckeT_ppow_bad_smul p hp hpN v⟩
    refine ⟨cq * cp, ?_⟩
    rw [heckeT_n_cusp_decomp_of_mul (p ^ v) (m / p ^ v) m hmul, hcq,
      heckeT_n_cusp_smul, hcp, smul_smul]

/-- **[T006]** A `Newform` is a full eigenform: a `T_n`-eigenform for **all** `n ∈ ℕ⁺`
(Diamond–Shurman Theorem 5.8.2(a)). -/
theorem Newform.isFullEigenform (f : Newform N k) : IsFullEigenform f.toCuspForm := by
  exact ⟨fun n ↦ (f.exists_heckeT_n_cusp_smul n.val).choose,
    fun n ↦ (f.exists_heckeT_n_cusp_smul n.val).choose_spec⟩

end HeckeRing.GL2

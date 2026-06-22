/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.Eigenforms.AtkinLehner
import LeanModularForms.Eigenforms.ConductorTheorem
import LeanModularForms.Eigenforms.MainLemma
import LeanModularForms.HeckeRIngs.GL2.Newforms

/-!
# Strong Multiplicity One via Miyake §4.6 — Lemma 4.6.5

CuspForm-level preservation lemmas and Miyake's Lemma 4.6.5 (single-prime
coprime filter and its iterated forms).
-/

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- CuspForm-level subgroup-restriction preserves the Nebentypus
character space (with the natural pullback of `χ` along the unit map). -/
lemma cuspForm_restrictSubgroup_mem_cuspFormCharSpace
    {M N : ℕ} [NeZero M] [NeZero N] {k : ℤ} (χ : (ZMod M)ˣ →* ℂˣ) (h : M ∣ N)
    {f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    CuspForm.restrictSubgroup (Gamma1_map_le_Gamma1_map_of_dvd h) f ∈
      cuspFormCharSpace k (χ.comp (ZMod.unitsMap h)) := by
  rw [← cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace,
    show cuspFormToModularForm
          (CuspForm.restrictSubgroup (Gamma1_map_le_Gamma1_map_of_dvd h) f) =
        ModularForm.restrictSubgroup (HeckeRing.GL2.MainLemma.Gamma1_mapGL_le_of_dvd h)
          (cuspFormToModularForm f) from ModularForm.ext fun _ ↦ rfl]
  exact HeckeRing.GL2.MainLemma.restrictSubgroup_mem_modFormCharSpace χ h _
    ((cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
      (k := k) χ f).mpr hf)

/-- CuspForm-level `V_p` (`levelRaise`) preserves the Nebentypus
character space, with the lifted character on the higher level. -/
lemma cuspForm_levelRaise_mem_cuspFormCharSpace
    (M : ℕ) [NeZero M] (d : ℕ) [NeZero d] (k : ℤ) (χ : (ZMod M)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    HeckeRing.GL2.levelRaise M d k f ∈
      cuspFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left M d))) := by
  rw [← cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace,
    show cuspFormToModularForm (HeckeRing.GL2.levelRaise M d k f) =
        HeckeRing.GL2.modularFormLevelRaise M d k (cuspFormToModularForm f)
      from ModularForm.ext fun _ ↦ rfl]
  exact HeckeRing.GL2.MainLemma.modularFormLevelRaise_mem_modFormCharSpace M d k χ
    ((cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
      (k := k) χ f).mpr hf)

private lemma heckeT_n_cusp_preserves_cuspFormCharSpace_divN
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    heckeT_n_cusp k p f ∈ cuspFormCharSpace k χ := by
  rw [mem_cuspFormCharSpace_iff] at hf ⊢
  intro d
  have hfχ_mod : f.toModularForm' ∈ modFormCharSpace k χ := by
    rw [mem_modFormCharSpace_iff]
    refine fun d' ↦ ModularForm.ext fun τ ↦ ?_
    show ((diamondOp k d') f.toModularForm').toFun τ = ↑(χ d') • f.toModularForm'.toFun τ
    exact congr_arg (fun (g : CuspForm _ k) ↦ g.toFun τ) (hf d')
  have h_diamond := ((mem_modFormCharSpace_iff k χ _).mp
    (HeckeRing.GL2.MainLemma.heckeT_p_divN_preserves_modFormCharSpace hp hpN χ hfχ_mod)) d
  refine CuspForm.ext fun τ ↦ ?_
  show ((diamondOp k d) (heckeT_n k p f.toModularForm')).toFun τ =
    ↑(χ d) • (heckeT_n k p f.toModularForm').toFun τ
  rw [show heckeT_n k p = HeckeRing.GL2.heckeT_p_divN k p hp hpN by
    rw [heckeT_n_prime k hp]; exact dif_neg hpN]
  exact congr_arg (fun (m : ModularForm _ k) ↦ m.toFun τ) h_diamond

private lemma qExpansion_restrict_sub_levelRaise_heckeT_coeff
    {N₀ : ℕ} [NeZero N₀] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N₀)
    (f₀ : CuspForm ((Gamma1 N₀).map (mapGL ℝ)) k) (n : ℕ) :
    haveI : NeZero (p * N₀) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne N₀)⟩
    (UpperHalfPlane.qExpansion (1 : ℝ)
        (CuspForm.restrictSubgroup (Gamma1_map_le_Gamma1_map_of_dvd (Nat.dvd_mul_left N₀ p)) f₀
          - HeckeRing.GL2.levelRaise N₀ p k (heckeT_n_cusp k p f₀))).coeff n
      = if ¬ p ∣ n then (UpperHalfPlane.qExpansion (1 : ℝ) f₀).coeff n else 0 := by
  haveI : NeZero (p * N₀) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne N₀)⟩
  set f_res : CuspForm ((Gamma1 (p * N₀)).map (mapGL ℝ)) k :=
    CuspForm.restrictSubgroup (Gamma1_map_le_Gamma1_map_of_dvd (Nat.dvd_mul_left N₀ p)) f₀
  set V_p_U_p_f : CuspForm ((Gamma1 (p * N₀)).map (mapGL ℝ)) k :=
    HeckeRing.GL2.levelRaise N₀ p k (heckeT_n_cusp k p f₀)
  have h1_period : (1 : ℝ) ∈ ((Gamma1 (p * N₀)).map (mapGL ℝ)).strictPeriods := by
    rw [strictPeriods_Gamma1]; exact ⟨1, by simp⟩
  have h_VUp_fun :
      (⇑V_p_U_p_f : UpperHalfPlane → ℂ) =
        ⇑(HeckeRing.GL2.AtkinLehner.pSupportedRaise k p hp hpN f₀.toModularForm') := by
    show (HeckeRing.GL2.modularFormLevelRaise N₀ p k
        (heckeT_n k p f₀.toModularForm')).toFun = _
    rw [show heckeT_n k p = HeckeRing.GL2.heckeT_p_divN k p hp hpN by
      rw [heckeT_n_prime k hp]; exact dif_neg hpN]; rfl
  have h_coe_sub : (⇑(f_res - V_p_U_p_f) : UpperHalfPlane → ℂ) =
      ⇑f₀ - ⇑(HeckeRing.GL2.AtkinLehner.pSupportedRaise k p hp hpN f₀.toModularForm') := by
    show (⇑f_res - ⇑V_p_U_p_f : UpperHalfPlane → ℂ) = _; rw [h_VUp_fun]; rfl
  show (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ)
    (⇑(f_res - V_p_U_p_f))) = _
  rw [h_coe_sub]
  set raised : ModularForm ((Gamma1 (p * N₀)).map (mapGL ℝ)) k :=
    HeckeRing.GL2.AtkinLehner.pSupportedRaise k p hp hpN f₀.toModularForm'
  set f_pN : ModularForm ((Gamma1 (p * N₀)).map (mapGL ℝ)) k :=
    ModularForm.restrictSubgroup (HeckeRing.GL2.MainLemma.Gamma1_mapGL_le_of_dvd
      (Nat.dvd_mul_left N₀ p)) f₀.toModularForm'
  rw [show (⇑f₀ - ⇑raised : UpperHalfPlane → ℂ) = ⇑(f_pN - raised) from rfl,
    show UpperHalfPlane.qExpansion (1 : ℝ) (⇑(f_pN - raised)) =
      UpperHalfPlane.qExpansion (1 : ℝ) (f_pN - raised) from rfl,
    ModularForm.qExpansion_sub one_pos h1_period f_pN raised, map_sub,
    HeckeRing.GL2.AtkinLehner.qExpansion_one_pSupportedRaise_coeff hp hpN
      f₀.toModularForm' n]
  by_cases hpn : p ∣ n <;>
    simp [hpn, f_pN, show (⇑f₀.toModularForm' : UpperHalfPlane → ℂ) = ⇑f₀ from rfl]

private lemma ite_coprime_filter_compose {α : Type*} [Zero α]
    {q : ℕ} (hq : q.Prime) (n m : ℕ) (a : α) :
    (if Nat.Coprime n m then (if ¬ q ∣ n then a else 0) else 0)
      = if Nat.Coprime n (q * m) then a else 0 := by
  have h : Nat.Coprime n (q * m) ↔ (¬ q ∣ n) ∧ Nat.Coprime n m := by
    rw [Nat.coprime_mul_iff_right]
    exact and_congr_left fun _ ↦
      ⟨fun h ↦ hq.coprime_iff_not_dvd.mp h.symm,
       fun h ↦ (hq.coprime_iff_not_dvd.mpr h).symm⟩
  by_cases h_rest : Nat.Coprime n m <;> by_cases h_q : q ∣ n <;> simp_all

private lemma dvd_conditions_mul_left_of_dvd
    {N M q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hr_ne_q : r ≠ q)
    (hr_cond : (¬ r ∣ N → r ^ 2 ∣ M) ∧ (r ∣ N → r ∣ M / N))
    (hq_div : q ∣ M / N) :
    (¬ r ∣ q * N → r ^ 2 ∣ M) ∧ (r ∣ q * N → r ∣ M / (q * N)) := by
  obtain ⟨hr_not, hr_dvd⟩ := hr_cond
  refine ⟨fun h ↦ hr_not fun hrN ↦ h (hrN.mul_left q), fun h ↦ ?_⟩
  have hr_dvd_N : r ∣ N :=
    (hr.dvd_mul.mp h).resolve_left fun h' ↦
      hr_ne_q ((Nat.prime_dvd_prime_iff_eq hr hq).mp h')
  rw [show M / (q * N) = M / N / q by rw [mul_comm q N, Nat.div_div_eq_div_mul]]
  obtain ⟨c, hc⟩ := ((Nat.coprime_primes hr hq).mpr hr_ne_q).mul_dvd_of_dvd_of_dvd
    (hr_dvd hr_dvd_N) hq_div
  exact ⟨c, by rw [hc, show r * q * c = r * c * q by ring, Nat.mul_div_cancel _ hq.pos]⟩

private lemma dvd_conditions_mul_right_sq_of_not_dvd
    {N M q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hr_ne_q : r ≠ q)
    (hqN : ¬ q ∣ N) (hNM : N ∣ M)
    (hr_cond : (¬ r ∣ N → r ^ 2 ∣ M) ∧ (r ∣ N → r ∣ M / N))
    (hq2_dvd_M : q ^ 2 ∣ M) :
    (¬ r ∣ N * q ^ 2 → r ^ 2 ∣ M) ∧ (r ∣ N * q ^ 2 → r ∣ M / (N * q ^ 2)) := by
  obtain ⟨hr_not, hr_dvd⟩ := hr_cond
  refine ⟨fun h ↦ hr_not fun hrN ↦ h (hrN.mul_right (q ^ 2)), fun h ↦ ?_⟩
  have hr_dvd_N : r ∣ N :=
    (hr.dvd_mul.mp h).resolve_right fun h' ↦
      hr_ne_q ((Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow h'))
  have hq2_dvd_MN : q ^ 2 ∣ M / N := by
    rw [(Nat.mul_div_cancel' hNM).symm] at hq2_dvd_M
    exact ((hq.coprime_iff_not_dvd.mpr hqN).pow_left 2).dvd_of_dvd_mul_left hq2_dvd_M
  rw [show M / (N * q ^ 2) = M / N / q ^ 2 by rw [Nat.div_div_eq_div_mul]]
  obtain ⟨c, hc⟩ := (((Nat.coprime_primes hr hq).mpr hr_ne_q).pow_right 2).mul_dvd_of_dvd_of_dvd
    (hr_dvd hr_dvd_N) hq2_dvd_MN
  exact ⟨c, by rw [hc, show r * q ^ 2 * c = r * c * q ^ 2 by ring,
    Nat.mul_div_cancel _ (pow_pos hq.pos 2)]⟩

private theorem miyake_4_6_5_single_prime_dvd_N
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : ¬ Nat.Coprime p N) :
    let M := p * N
    haveI : NeZero M := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne N)⟩
    have hNM : N ∣ M := Nat.dvd_mul_left N p
    ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n =
        if ¬ p ∣ n then
          (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n
        else 0 := by
  haveI : NeZero (p * N) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne N)⟩
  exact ⟨CuspForm.restrictSubgroup (Gamma1_map_le_Gamma1_map_of_dvd (Nat.dvd_mul_left N p)) f -
      HeckeRing.GL2.levelRaise N p k (heckeT_n_cusp k p f),
    Submodule.sub_mem _ (cuspForm_restrictSubgroup_mem_cuspFormCharSpace χ _ hfχ)
      (cuspForm_levelRaise_mem_cuspFormCharSpace N p k χ
        (heckeT_n_cusp_preserves_cuspFormCharSpace_divN hp hpN χ hfχ)),
    qExpansion_restrict_sub_levelRaise_heckeT_coeff hp hpN f⟩

private theorem miyake_4_6_5_iterated_helper
    (n_iter : ℕ) :
    ∀ {M : ℕ} [NeZero M] {k : ℤ}
      (χ_M : (ZMod M)ˣ →* ℂˣ)
      (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
      (_ : g ∈ cuspFormCharSpace k χ_M)
      (S : Finset ℕ) (_ : S ⊆ M.primeFactors)
      (_ : S.card = n_iter)
      (_ : Squarefree (S.prod id)),
      ∃ (M' : ℕ) (_ : NeZero M') (hMM' : M ∣ M') (_ : M' = M * S.prod id)
        (g' : CuspForm ((Gamma1 M').map (mapGL ℝ)) k),
        g' ∈ cuspFormCharSpace k (χ_M.comp (ZMod.unitsMap hMM')) ∧
        ∀ n : ℕ,
          (UpperHalfPlane.qExpansion (1 : ℝ) g').coeff n =
          if Nat.Coprime n (S.prod id) then
            (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n
          else 0 := by
  induction n_iter with
  | zero =>
    intro M _ k χ_M g hgχ S hS_sub hS_card _
    obtain rfl := Finset.card_eq_zero.mp hS_card
    exact ⟨M, ‹NeZero M›, dvd_refl M, by simp, g,
      by simpa [ZMod.unitsMap] using hgχ, fun _ ↦ by simp [Nat.Coprime, Finset.prod_empty]⟩
  | succ k ih =>
    intro M _ k_int χ_M g hgχ S hS_sub hS_card hS_sqfree
    obtain ⟨q, hq_in⟩ := Finset.card_pos.mp (by lia : 0 < S.card)
    have hq_prime_factor : q ∈ M.primeFactors := hS_sub hq_in
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_prime_factor
    haveI : NeZero q := ⟨hq_prime.ne_zero⟩
    obtain ⟨g_step, hg_step_χ, hg_step_qexp⟩ :=
      miyake_4_6_5_single_prime_dvd_N χ_M g hgχ q hq_prime
        (fun h ↦ hq_prime.coprime_iff_not_dvd.mp h
          (Nat.dvd_of_mem_primeFactors hq_prime_factor))
    haveI : NeZero (q * M) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne M)⟩
    have hM_dvd_qM : M ∣ q * M := Nat.dvd_mul_left M q
    have hS_erase_sub : S.erase q ⊆ (q * M).primeFactors := fun r hr ↦ by
      have hr_in_M : r ∈ M.primeFactors := hS_sub (Finset.mem_of_mem_erase hr)
      rw [Nat.mem_primeFactors] at hr_in_M ⊢
      exact ⟨hr_in_M.1, hr_in_M.2.1.mul_left q, NeZero.ne _⟩
    have hS_erase_card : (S.erase q).card = k := by
      rw [Finset.card_erase_of_mem hq_in, hS_card]; lia
    have h_prod_eq : S.prod id = q * (S.erase q).prod id :=
      (Finset.mul_prod_erase _ _ hq_in).symm
    obtain ⟨M', hM'_NeZero, hqM_dvd_M', hM'_eq, g', hg'_χ, hg'_qexp⟩ :=
      ih (χ_M.comp (ZMod.unitsMap hM_dvd_qM)) g_step hg_step_χ
        (S.erase q) hS_erase_sub hS_erase_card (h_prod_eq ▸ hS_sqfree).of_mul_right
    refine ⟨M', hM'_NeZero, dvd_trans hM_dvd_qM hqM_dvd_M',
        by rw [hM'_eq, h_prod_eq]; ring, g', ?_, fun n ↦ by
          rw [hg'_qexp n, hg_step_qexp n, h_prod_eq]
          exact ite_coprime_filter_compose hq_prime n _ _⟩
    rw [show χ_M.comp (ZMod.unitsMap (dvd_trans hM_dvd_qM hqM_dvd_M')) =
        (χ_M.comp (ZMod.unitsMap hM_dvd_qM)).comp (ZMod.unitsMap hqM_dvd_M') from by
      rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]]
    exact hg'_χ

/-- Iterated single-prime coprime filter: for `f ∈ S_k(Γ_1(N), χ)` and
`L ∣ N` squarefree, there is a form `g` at level `Γ_1(L · N)` with
`q`-expansion `aₙ(g) = aₙ(f) · [(n, L) = 1]`. -/
theorem miyake_4_6_5_iterated_L
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (L : ℕ) (hL_pos : 0 < L) (hL_sqfree : Squarefree L)
    (hL_dvd : ∀ p ∈ L.primeFactors, p ∈ N.primeFactors) :
    let M := L * N
    haveI : NeZero M := ⟨Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp hL_pos) (NeZero.ne N)⟩
    have hNM : N ∣ M := Nat.dvd_mul_left N L
    ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n =
        if Nat.Coprime n L then
          (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n
        else 0 := by
  have hS_prod : L.primeFactors.prod id = L := by
    simp [Nat.prod_primeFactors_of_squarefree hL_sqfree]
  obtain ⟨M', hM'_NeZero, hNM', hM'_eq, g', hg'_χ, hg'_qexp⟩ :=
    miyake_4_6_5_iterated_helper L.primeFactors.card χ f hfχ
      L.primeFactors hL_dvd rfl (hS_prod.symm ▸ hL_sqfree)
  have hM'_eq_LN : M' = L * N := by rw [hM'_eq, hS_prod, mul_comm]
  subst hM'_eq_LN
  refine ⟨g', by convert hg'_χ using 2, fun n ↦ ?_⟩
  have h := hg'_qexp n
  rwa [hS_prod] at h

private theorem miyake_4_6_5_single_prime_coprime_to_N
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (p : ℕ) [NeZero p] (hp : p.Prime) :
    let M := N * p ^ 2
    haveI : NeZero M :=
      ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 hp.ne_zero)⟩
    have hNM : N ∣ M := Nat.dvd_mul_right N (p ^ 2)
    ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n =
        if ¬ p ∣ n then
          (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n
        else 0 := by
  haveI hM_NeZero : NeZero (N * p ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 hp.ne_zero)⟩
  have hN_dvd_pN : N ∣ p * N := Nat.dvd_mul_left N p
  haveI : NeZero (p * N) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne N)⟩
  have hM_eq' : p * (p * N) = N * p ^ 2 := by ring
  haveI : NeZero (p * (p * N)) := ⟨hM_eq' ▸ hM_NeZero.ne⟩
  have hN_dvd_ppN : N ∣ p * (p * N) := hM_eq' ▸ Nat.dvd_mul_right N (p ^ 2)
  obtain ⟨g_ppN, h_g_ppN_χ, h_g_ppN_qexp⟩ :=
    miyake_4_6_5_single_prime_dvd_N (χ.comp (ZMod.unitsMap hN_dvd_pN))
      (CuspForm.restrictSubgroup (Gamma1_map_le_Gamma1_map_of_dvd hN_dvd_pN) f)
      (cuspForm_restrictSubgroup_mem_cuspFormCharSpace χ hN_dvd_pN hfχ) p hp
      (fun h ↦ hp.coprime_iff_not_dvd.mp h (Nat.dvd_mul_right p N))
  rw [show (χ.comp (ZMod.unitsMap hN_dvd_pN)).comp
        (ZMod.unitsMap (Nat.dvd_mul_left (p * N) p)) = χ.comp (ZMod.unitsMap hN_dvd_ppN) from by
      rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]] at h_g_ppN_χ
  have key : ∀ (inst : NeZero (p * (p * N))) (h : N ∣ p * (p * N)),
      ∃ g : CuspForm (Subgroup.map (mapGL ℝ) (Gamma1 (p * (p * N)))) k,
      g ∈ @cuspFormCharSpace (p * (p * N)) inst k (χ.comp (ZMod.unitsMap h)) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n =
        if ¬ p ∣ n then (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n else 0 :=
    fun _ h ↦ ⟨g_ppN, by convert h_g_ppN_χ using 2, h_g_ppN_qexp⟩
  exact @Eq.ndrec ℕ (p * (p * N))
    (fun M ↦ ∀ (inst : NeZero M) (h : N ∣ M),
      ∃ g : CuspForm (Subgroup.map (mapGL ℝ) (Gamma1 M)) k,
      g ∈ @cuspFormCharSpace M inst k (χ.comp (ZMod.unitsMap h)) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n =
        if ¬ p ∣ n then (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n else 0)
    key (N * p ^ 2) hM_eq' hM_NeZero (Nat.dvd_mul_right N (p ^ 2))

private theorem finish_peel_step
    {N N' M : ℕ} [NeZero N] [NeZero N'] [NeZero M] {k : ℤ} {q : ℕ} {n_pred : ℕ}
    (hq_prime : q.Prime)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hNM : N ∣ M) (hNN' : N ∣ N') (hN'M : N' ∣ M)
    (S : Finset ℕ)
    (h_S_prod_split : S.prod id = q * (S.erase q).prod id)
    (hS_erase_prime : ∀ p ∈ S.erase q, p.Prime)
    (hS_erase_card : (S.erase q).card = n_pred)
    (hS_erase_sqfree : Squarefree ((S.erase q).prod id))
    (h_S_erase_prod_dvd_M : (S.erase q).prod id ∣ M)
    (g_int : CuspForm ((Gamma1 N').map (mapGL ℝ)) k)
    (hg_int_χ : g_int ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNN')))
    (hg_int_qexp : ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℝ) g_int).coeff n =
      if ¬ q ∣ n then (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n else 0)
    (h_pf_dvd_new : ∀ p ∈ S.erase q,
      (¬ p ∣ N' → p ^ 2 ∣ M) ∧ (p ∣ N' → p ∣ M / N'))
    (ih : ∀ {N : ℕ} [NeZero N] {k : ℤ}
      (χ : (ZMod N)ˣ →* ℂˣ)
      (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
      (_ : f ∈ cuspFormCharSpace k χ)
      (S : Finset ℕ) (_ : ∀ p ∈ S, p.Prime)
      (_ : S.card = n_pred)
      (_ : Squarefree (S.prod id))
      {M : ℕ} (_ : NeZero M) (hNM : N ∣ M) (_ : S.prod id ∣ M)
      (_ : ∀ p ∈ S, (¬ p ∣ N → p ^ 2 ∣ M) ∧ (p ∣ N → p ∣ M / N)),
      ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
        g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
        ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n =
          if Nat.Coprime n (S.prod id) then
            (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n else 0) :
    ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n =
        if Nat.Coprime n (S.prod id) then
          (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n else 0 := by
  obtain ⟨g', hg'_χ, hg'_qexp⟩ :=
    ih (χ.comp (ZMod.unitsMap hNN')) g_int hg_int_χ
      (S.erase q) hS_erase_prime hS_erase_card hS_erase_sqfree
      ‹NeZero M› hN'M h_S_erase_prod_dvd_M h_pf_dvd_new
  refine ⟨g', ?_, fun n ↦ by
    rw [hg'_qexp n, hg_int_qexp n, h_S_prod_split]
    exact ite_coprime_filter_compose hq_prime n _ _⟩
  rw [show χ.comp (ZMod.unitsMap hNM) =
      (χ.comp (ZMod.unitsMap hNN')).comp (ZMod.unitsMap hN'M) from by
    rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]]
  exact hg'_χ

private theorem peel_step_of_dvd_N
    {N M : ℕ} [NeZero N] [NeZero M] {k : ℤ} {q : ℕ} {n_pred : ℕ}
    (hq_prime : q.Prime) (hqN : q ∣ N)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hfχ : f ∈ cuspFormCharSpace k χ)
    (hNM : N ∣ M) (S : Finset ℕ)
    (h_S_prod_split : S.prod id = q * (S.erase q).prod id)
    (hS_prime : ∀ p ∈ S, p.Prime)
    (h_pf_dvd : ∀ p ∈ S, (¬ p ∣ N → p ^ 2 ∣ M) ∧ (p ∣ N → p ∣ M / N))
    (hq_pf_dvd : q ∣ N → q ∣ M / N)
    (hS_erase_prime : ∀ p ∈ S.erase q, p.Prime)
    (hS_erase_card : (S.erase q).card = n_pred)
    (hS_erase_sqfree : Squarefree ((S.erase q).prod id))
    (h_S_erase_prod_dvd_M : (S.erase q).prod id ∣ M)
    (ih : ∀ {N : ℕ} [NeZero N] {k : ℤ}
      (χ : (ZMod N)ˣ →* ℂˣ)
      (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
      (_ : f ∈ cuspFormCharSpace k χ)
      (S : Finset ℕ) (_ : ∀ p ∈ S, p.Prime)
      (_ : S.card = n_pred) (_ : Squarefree (S.prod id))
      {M : ℕ} (_ : NeZero M) (hNM : N ∣ M) (_ : S.prod id ∣ M)
      (_ : ∀ p ∈ S, (¬ p ∣ N → p ^ 2 ∣ M) ∧ (p ∣ N → p ∣ M / N)),
      ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
        g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
        ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n =
          if Nat.Coprime n (S.prod id) then
            (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n else 0) :
    ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n =
        if Nat.Coprime n (S.prod id) then
          (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n else 0 := by
  haveI : NeZero q := ⟨hq_prime.ne_zero⟩
  obtain ⟨g_int, hg_int_χ, hg_int_qexp⟩ :=
    miyake_4_6_5_single_prime_dvd_N χ f hfχ q hq_prime
      (fun h ↦ hq_prime.coprime_iff_not_dvd.mp h hqN)
  haveI : NeZero (q * N) := ⟨Nat.mul_ne_zero hq_prime.ne_zero (NeZero.ne N)⟩
  have hqN_dvd_M : q * N ∣ M :=
    calc q * N = N * q := by ring
      _ ∣ N * (M / N) := Nat.mul_dvd_mul_left N (hq_pf_dvd hqN)
      _ = M := Nat.mul_div_cancel' hNM
  exact finish_peel_step hq_prime χ f hNM (Nat.dvd_mul_left N q) hqN_dvd_M S h_S_prod_split
    hS_erase_prime hS_erase_card hS_erase_sqfree h_S_erase_prod_dvd_M g_int hg_int_χ
    hg_int_qexp (fun r hr ↦ dvd_conditions_mul_left_of_dvd hq_prime
      (hS_prime r (Finset.mem_of_mem_erase hr)) (Finset.ne_of_mem_erase hr)
      (h_pf_dvd r (Finset.mem_of_mem_erase hr)) (hq_pf_dvd hqN)) ih

private theorem peel_step_of_not_dvd_N
    {N M : ℕ} [NeZero N] [NeZero M] {k : ℤ} {q : ℕ} {n_pred : ℕ}
    (hq_prime : q.Prime) (hqN : ¬ q ∣ N)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hfχ : f ∈ cuspFormCharSpace k χ)
    (hNM : N ∣ M) (S : Finset ℕ)
    (h_S_prod_split : S.prod id = q * (S.erase q).prod id)
    (hS_prime : ∀ p ∈ S, p.Prime)
    (h_pf_dvd : ∀ p ∈ S, (¬ p ∣ N → p ^ 2 ∣ M) ∧ (p ∣ N → p ∣ M / N))
    (hq_pf_not_dvd : ¬ q ∣ N → q ^ 2 ∣ M)
    (hS_erase_prime : ∀ p ∈ S.erase q, p.Prime)
    (hS_erase_card : (S.erase q).card = n_pred)
    (hS_erase_sqfree : Squarefree ((S.erase q).prod id))
    (h_S_erase_prod_dvd_M : (S.erase q).prod id ∣ M)
    (ih : ∀ {N : ℕ} [NeZero N] {k : ℤ}
      (χ : (ZMod N)ˣ →* ℂˣ)
      (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
      (_ : f ∈ cuspFormCharSpace k χ)
      (S : Finset ℕ) (_ : ∀ p ∈ S, p.Prime)
      (_ : S.card = n_pred) (_ : Squarefree (S.prod id))
      {M : ℕ} (_ : NeZero M) (hNM : N ∣ M) (_ : S.prod id ∣ M)
      (_ : ∀ p ∈ S, (¬ p ∣ N → p ^ 2 ∣ M) ∧ (p ∣ N → p ∣ M / N)),
      ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
        g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
        ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n =
          if Nat.Coprime n (S.prod id) then
            (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n else 0) :
    ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n =
        if Nat.Coprime n (S.prod id) then
          (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n else 0 := by
  haveI : NeZero q := ⟨hq_prime.ne_zero⟩
  obtain ⟨g_int, hg_int_χ, hg_int_qexp⟩ :=
    miyake_4_6_5_single_prime_coprime_to_N χ f hfχ q hq_prime
  haveI : NeZero (N * q ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 hq_prime.ne_zero)⟩
  exact finish_peel_step hq_prime χ f hNM (Nat.dvd_mul_right N (q ^ 2))
    (((hq_prime.coprime_iff_not_dvd.mpr hqN).symm.pow_right 2).mul_dvd_of_dvd_of_dvd hNM
      (hq_pf_not_dvd hqN)) S
    h_S_prod_split hS_erase_prime hS_erase_card hS_erase_sqfree h_S_erase_prod_dvd_M g_int
    hg_int_χ hg_int_qexp (fun r hr ↦ dvd_conditions_mul_right_sq_of_not_dvd hq_prime
      (hS_prime r (Finset.mem_of_mem_erase hr)) (Finset.ne_of_mem_erase hr) hqN hNM
      (h_pf_dvd r (Finset.mem_of_mem_erase hr)) (hq_pf_not_dvd hqN)) ih

private theorem miyake_4_6_5_iterated_helper_general (n_iter : ℕ) :
    ∀ {N : ℕ} [NeZero N] {k : ℤ}
      (χ : (ZMod N)ˣ →* ℂˣ)
      (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
      (_ : f ∈ cuspFormCharSpace k χ)
      (S : Finset ℕ) (_ : ∀ p ∈ S, p.Prime)
      (_ : S.card = n_iter)
      (_ : Squarefree (S.prod id))
      {M : ℕ} (_ : NeZero M) (hNM : N ∣ M) (_ : S.prod id ∣ M)
      (_ : ∀ p ∈ S, (¬ p ∣ N → p ^ 2 ∣ M) ∧ (p ∣ N → p ∣ M / N)),
      ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
        g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
        ∀ n : ℕ,
          (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n =
          if Nat.Coprime n (S.prod id) then
            (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n
          else 0 := by
  induction n_iter with
  | zero =>
    intro N _ k χ f hfχ S _hS_prime hS_card _hS_sqfree M _hM hNM _hSM _h_pf_dvd
    obtain rfl := Finset.card_eq_zero.mp hS_card
    refine ⟨CuspForm.restrictSubgroup (Gamma1_map_le_Gamma1_map_of_dvd hNM) f,
      cuspForm_restrictSubgroup_mem_cuspFormCharSpace χ hNM hfχ, fun n ↦ ?_⟩
    simp only [Finset.prod_empty, Nat.coprime_one_right_eq_true, if_true]
    rfl
  | succ k ih =>
    intro N _ k_int χ f hfχ S hS_prime hS_card hS_sqfree M hM_NeZero hNM hSM h_pf_dvd
    obtain ⟨q, hq_in⟩ : S.Nonempty := Finset.card_pos.mp (hS_card ▸ Nat.succ_pos k)
    have hq_prime : q.Prime := hS_prime q hq_in
    haveI : NeZero q := ⟨hq_prime.ne_zero⟩
    have h_S_prod_split : S.prod id = q * (S.erase q).prod id :=
      (Finset.mul_prod_erase _ _ hq_in).symm
    have hS_erase_prime : ∀ p ∈ S.erase q, p.Prime :=
      fun p hp ↦ hS_prime p (Finset.mem_of_mem_erase hp)
    have hS_erase_card : (S.erase q).card = k := by
      rw [Finset.card_erase_of_mem hq_in, hS_card]; lia
    have h_S_erase_prod_dvd_M : (S.erase q).prod id ∣ M :=
      (h_S_prod_split ▸ Dvd.intro_left _ rfl).trans hSM
    obtain ⟨hq_pf_not_dvd, hq_pf_dvd⟩ := h_pf_dvd q hq_in
    by_cases hqN : q ∣ N
    · exact peel_step_of_dvd_N hq_prime hqN χ f hfχ hNM S h_S_prod_split hS_prime
        h_pf_dvd hq_pf_dvd hS_erase_prime hS_erase_card (h_S_prod_split ▸ hS_sqfree).of_mul_right
        h_S_erase_prod_dvd_M ih
    · exact peel_step_of_not_dvd_N hq_prime hqN χ f hfχ hNM S h_S_prod_split hS_prime
        h_pf_dvd hq_pf_not_dvd hS_erase_prime hS_erase_card
        (h_S_prod_split ▸ hS_sqfree).of_mul_right h_S_erase_prod_dvd_M ih

private theorem miyake_4_6_5_iterated_L_general
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (L : ℕ) (_hL_pos : 0 < L) (hL_sqfree : Squarefree L) (M : ℕ) [NeZero M]
    (hNM : N ∣ M) (hLM : L ∣ M)
    (h_pf_dvd : ∀ p ∈ L.primeFactors,
      (¬ p ∣ N → p ^ 2 ∣ M) ∧ (p ∣ N → p ∣ M / N)) :
    ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n =
        if Nat.Coprime n L then
          (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n
        else 0 := by
  have hS_prod : L.primeFactors.prod id = L := by
    simp [Nat.prod_primeFactors_of_squarefree hL_sqfree]
  obtain ⟨g, hg_χ, hg_qexp⟩ :=
    miyake_4_6_5_iterated_helper_general L.primeFactors.card χ f hfχ
      L.primeFactors (fun _ ↦ Nat.prime_of_mem_primeFactors) rfl
      (hS_prod.symm ▸ hL_sqfree) ‹NeZero M› hNM (hS_prod.symm ▸ hLM) h_pf_dvd
  exact ⟨g, hg_χ, fun n ↦ by simpa only [hS_prod] using hg_qexp n⟩

/-- For `f ∈ S_k(Γ_1(N), χ)` and `l'` squarefree positive, there exists
`h_form` at level `Γ_1(l'² · N)` with `q`-expansion supported on
`(n, l') ≠ 1`. -/
theorem miyake_h_form_general
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (l' : ℕ) (hl'_pos : 0 < l') (hl'_sqfree : Squarefree l') :
    let M := N * l' ^ 2
    haveI : NeZero M := ⟨Nat.mul_ne_zero (NeZero.ne N)
      (pow_ne_zero 2 (Nat.pos_iff_ne_zero.mp hl'_pos))⟩
    have hNM : N ∣ M := Nat.dvd_mul_right N (l' ^ 2)
    ∃ h_form : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      h_form ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℝ) h_form).coeff n =
        if ¬ Nat.Coprime n l' then
          (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n
        else 0 := by
  haveI : NeZero (N * l' ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 (Nat.pos_iff_ne_zero.mp hl'_pos))⟩
  have hNM : N ∣ N * l' ^ 2 := Nat.dvd_mul_right N (l' ^ 2)
  have hl'M : l' ∣ N * l' ^ 2 := dvd_mul_of_dvd_right (dvd_pow_self l' two_ne_zero) N
  have h_pf_dvd : ∀ p ∈ l'.primeFactors,
      (¬ p ∣ N → p ^ 2 ∣ (N * l' ^ 2)) ∧
      (p ∣ N → p ∣ (N * l' ^ 2) / N) := fun p hp_in ↦ by
    have hp_dvd_l' : p ∣ l' := Nat.dvd_of_mem_primeFactors hp_in
    refine ⟨fun _ ↦ dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hp_dvd_l' 2) N, fun _ ↦ ?_⟩
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne N))]
    exact dvd_pow hp_dvd_l' two_ne_zero
  obtain ⟨g, hg_char, hg_qexp⟩ :=
    miyake_4_6_5_iterated_L_general χ f hfχ l' hl'_pos hl'_sqfree
      (N * l' ^ 2) hNM hl'M h_pf_dvd
  let f_at_M : CuspForm ((Gamma1 (N * l' ^ 2)).map (mapGL ℝ)) k :=
    CuspForm.restrictSubgroup
      (HeckeRing.GL2.MainLemma.Gamma1_mapGL_le_of_dvd hNM) f
  refine ⟨f_at_M - g, Submodule.sub_mem _
    (cuspForm_restrictSubgroup_mem_cuspFormCharSpace χ hNM hfχ) hg_char, fun n ↦ ?_⟩
  have h1_period : (1 : ℝ) ∈ ((Gamma1 (N * l' ^ 2)).map (mapGL ℝ)).strictPeriods := by
    simp [strictPeriods_Gamma1]
  have h_sub :
      UpperHalfPlane.qExpansion (1 : ℝ) (f_at_M - g) =
        UpperHalfPlane.qExpansion (1 : ℝ) f_at_M -
        UpperHalfPlane.qExpansion (1 : ℝ) g := by
    rw [sub_eq_add_neg, sub_eq_add_neg, ← ModularForm.qExpansion_neg one_pos h1_period g]
    exact ModularForm.qExpansion_add (Γ := (Gamma1 (N * l' ^ 2)).map (mapGL ℝ))
      (h := (1 : ℝ)) (a := k) (b := k) one_pos h1_period f_at_M (- g)
  rw [show UpperHalfPlane.qExpansion (1 : ℝ) (⇑(f_at_M - g) : UpperHalfPlane → ℂ) =
        UpperHalfPlane.qExpansion (1 : ℝ) (f_at_M - g) from rfl, h_sub, map_sub,
      show UpperHalfPlane.qExpansion (1 : ℝ) f_at_M =
        UpperHalfPlane.qExpansion (1 : ℝ) f from rfl, hg_qexp n]
  split_ifs <;> simp

end HeckeRing.GL2

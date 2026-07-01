/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.StrongMultiplicityOne.SquarefreeDecomp

/-!
# Strong Multiplicity One via Miyake §4.6 — Lemma 4.6.14

The `δ`-slash-sum coefficient vanishing (`miyake_4_6_14_delta_slash_sum_coeff_zero`)
and the descent-witness apparatus for the `l' > 1` case. Part of a multi-file
split of `StrongMultiplicityOne.lean`.

## Main definitions

* `descendSlashSumCuspForm`: the cusp form obtained by summing slash-actions of a
  cusp form over the descend-coset list at a prime `p`.

## Main results

* `descendSlashSumCuspForm_mem_charSpace`: the descend slash-sum lies in the
  appropriate character space.
* `Φ_qExp_coeff_eq_count_div_p_mul_g_low_coeff`: the `q`-expansion coefficient
  of `descendSlashSumCuspForm` equals `descendCosetCount / p` times the
  coefficient of the low-level form on indices coprime to `l'`.
* `qExpansion_smul_cuspForm_coeff_aux`: scalar multiplication of cusp forms
  commutes with `q`-expansion coefficient extraction.
-/

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

private lemma prime_in_factors_p_dvd_div_q {N p l' : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (hp_not_in : p ∉ l'.primeFactors) (q : ℕ) (hq_mem : q ∈ l'.primeFactors)
    (hq_dvd_Ll2 : q ∣ (l' * N) * l' ^ 2) : p ∣ ((l' * N) * l' ^ 2) / q := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
  have hpq_cop : Nat.Coprime p q := by
    rw [hp.coprime_iff_not_dvd]
    intro hpq
    exact hp_not_in <| (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hpq ▸ hq_mem
  have hp_dvd_full : p ∣ (l' * N) * l' ^ 2 :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpN l') _
  rcases hp_dvd_full with ⟨c1, hc1⟩
  have : q ∣ c1 := hpq_cop.symm.dvd_of_dvd_mul_left (hc1 ▸ hq_dvd_Ll2)
  rcases this with ⟨c2, hc2⟩
  refine ⟨c2, ?_⟩
  rw [hc1, hc2, show p * (q * c2) = q * (p * c2) by ring,
    Nat.mul_div_cancel_left _ hq_prime.pos]

private lemma prime_in_factors_q_dvd_div_q_div_p {N p l' : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (q : ℕ) (hq_mem : q ∈ l'.primeFactors) (hq_dvd_Ll2 : q ∣ (l' * N) * l' ^ 2) :
    q ∣ ((l' * N) * l' ^ 2) / q / p := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
  have hq_dvd_l' : q ∣ l' := Nat.dvd_of_mem_primeFactors hq_mem
  have hq_dvd_l'2 : q ∣ l' ^ 2 := hq_dvd_l'.trans (dvd_pow_self l' two_ne_zero)
  have hq2p_dvd : q * (q * p) ∣ (l' * N) * l' ^ 2 := by
    have h1 : q * q ∣ l' ^ 2 := by rw [sq]; exact mul_dvd_mul hq_dvd_l' hq_dvd_l'
    have h2 : (q * q) * p ∣ l' ^ 2 * N := mul_dvd_mul h1 hpN
    have h_reorg : l' ^ 2 * N ∣ (l' * N) * l' ^ 2 := ⟨l', by ring⟩
    rw [show q * (q * p) = q * q * p by ring]
    exact h2.trans h_reorg
  have hM_q_eq : q * (((l' * N) * l' ^ 2) / q) = (l' * N) * l' ^ 2 :=
    Nat.mul_div_cancel' hq_dvd_Ll2
  have hqp_dvd_Mq : q * p ∣ ((l' * N) * l' ^ 2) / q := by
    rcases hq2p_dvd with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have h_extract : q * (q * p * c) = (l' * N) * l' ^ 2 := by rw [hc]; ring
    exact Nat.eq_of_mul_eq_mul_left hq_prime.pos (by rw [hM_q_eq, ← h_extract])
  rcases hqp_dvd_Mq with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rw [hc, show q * p * c = p * (q * c) by ring, Nat.mul_div_cancel_left _ hp.pos]

private lemma prime_in_factors_lN_div_p_dvd_div_q_div_p {N p l' : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (q : ℕ) (hq_mem : q ∈ l'.primeFactors) :
    (l' * N) / p ∣ ((l' * N) * l' ^ 2) / q / p := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
  have hq_dvd_l'2 : q ∣ l' ^ 2 :=
    (Nat.dvd_of_mem_primeFactors hq_mem).trans (dvd_pow_self l' two_ne_zero)
  have h_lN_dvd_Mq : l' * N ∣ ((l' * N) * l' ^ 2) / q := by
    rcases hq_dvd_l'2 with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [show (l' * N) * l' ^ 2 = q * (l' * N * c) by rw [hc]; ring,
      Nat.mul_div_cancel_left _ hq_prime.pos]
  rcases h_lN_dvd_Mq with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rcases hpN with ⟨d, hd⟩
  rw [hc, show l' * N = p * (l' * d) by rw [hd]; ring,
    show p * (l' * d) * c = p * (l' * d * c) by ring,
    Nat.mul_div_cancel_left _ hp.pos, Nat.mul_div_cancel_left _ hp.pos]

private lemma χ_F_factor_via_χ_M_unit_low {N l' p : ℕ} [NeZero (l' * N)]
    [NeZero (l' * N * l' ^ 2)] (hpN : p ∣ N) (q : ℕ) (hq_dvd_Ll2 : q ∣ (l' * N) * l' ^ 2)
    [NeZero ((l' * N * l' ^ 2) / q)] (hp_dvd_Mq : p ∣ ((l' * N) * l' ^ 2) / q)
    (h_lN_div_p_dvd_Mq_div_p : (l' * N) / p ∣ ((l' * N) * l' ^ 2) / q / p)
    (χ_M_unit : (ZMod (l' * N))ˣ →* ℂˣ) (χ_M_unit_low : (ZMod (l' * N / p))ˣ →* ℂˣ)
    (hχ_M_unit_eq : χ_M_unit =
      χ_M_unit_low.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd (dvd_mul_of_dvd_right hpN l'))))
    (χ_F_q : (ZMod ((l' * N) * l' ^ 2 / q))ˣ →* ℂˣ)
    (hχ_F_q : χ_F_q.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hq_dvd_Ll2)) =
      χ_M_unit.comp (ZMod.unitsMap (Nat.dvd_mul_right (l' * N) (l' ^ 2)))) :
    χ_F_q = (χ_M_unit_low.comp (ZMod.unitsMap h_lN_div_p_dvd_Mq_div_p)).comp
      (ZMod.unitsMap (Nat.div_dvd_of_dvd hp_dvd_Mq)) := by
  have h_surj : Function.Surjective (ZMod.unitsMap (Nat.div_dvd_of_dvd hq_dvd_Ll2)) :=
    ZMod.unitsMap_surjective _
  rw [← MonoidHom.cancel_right h_surj, hχ_F_q, hχ_M_unit_eq,
    MonoidHom.comp_assoc _ _ χ_M_unit_low, ZMod.unitsMap_comp,
    MonoidHom.comp_assoc _ _ χ_M_unit_low, MonoidHom.comp_assoc _ _ χ_M_unit_low,
    ZMod.unitsMap_comp, ZMod.unitsMap_comp]

private lemma slash_sum_descendCoset_level_recast {A B : ℕ} [NeZero A] [NeZero B] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (h_eq : A = B) (g : UpperHalfPlane → ℂ) :
    (fun z : UpperHalfPlane ↦
        ∑ v : Fin (descendCosetCount p A), (g ∣[k] descendCosetList p A hp v) z) =
    (fun z : UpperHalfPlane ↦
        ∑ v : Fin (descendCosetCount p B), (g ∣[k] descendCosetList p B hp v) z) := by
  cases h_eq; rfl

private lemma cuspForm_level_recast_coe_apply {A B : ℕ} [NeZero A] [NeZero B] {k : ℤ}
    (h_eq : A = B) (x : CuspForm ((Gamma1 A).map (mapGL ℝ)) k) (z : UpperHalfPlane) :
    (⇑(h_eq ▸ x : CuspForm ((Gamma1 B).map (mapGL ℝ)) k) : UpperHalfPlane → ℂ) z =
    (⇑x : UpperHalfPlane → ℂ) z := by
  cases h_eq; rfl

private lemma cuspForm_finsetSum_coe_apply {α : Type*} [DecidableEq α]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (s : Finset α) (F : α → CuspForm Γ k)
    (z : UpperHalfPlane) :
    (⇑(∑ q ∈ s, F q) : UpperHalfPlane → ℂ) z = ∑ q ∈ s, (⇑(F q) : UpperHalfPlane → ℂ) z := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro q s hqs ih
    rw [Finset.sum_insert hqs, Finset.sum_insert hqs, CuspForm.coe_add, Pi.add_apply, ih]

private lemma cuspForm_finsetSum_toModularForm' {α : Type*} [DecidableEq α]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (s : Finset α) (F : α → CuspForm Γ k) :
    (∑ q ∈ s, F q : CuspForm Γ k).toModularForm' = ∑ q ∈ s, (F q).toModularForm' := by
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]; rfl
  · intro q s hqs ih
    rw [Finset.sum_insert hqs, Finset.sum_insert hqs, ← ih]; rfl

/-- Helper for `miyake_4_6_14_delta_slash_sum_coeff_zero`: if a cusp-form family
`Φ_q : α → CuspForm (Gamma1 M) k` identifies the family of functions
`inner_fun : α → UpperHalfPlane → ℂ` pointwise, and the period-1 `q`-expansion of every
`inner_fun q` has vanishing `m`-th coefficient, then so does the period-1 `q`-expansion
of `fun z ↦ ∑ q ∈ s, inner_fun q z`. -/
private lemma qExp_finsetSum_inner_fun_coeff_zero_via_cuspForm_family
    {α : Type*} [DecidableEq α] {M : ℕ} [NeZero M] {k : ℤ}
    (Φ_q : α → CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (inner_fun : α → UpperHalfPlane → ℂ) (s : Finset α)
    (hΦ_q_fun : ∀ q ∈ s, (⇑(Φ_q q) : UpperHalfPlane → ℂ) = inner_fun q)
    (m : ℕ)
    (h_per_q_zero : ∀ q ∈ s,
        (UpperHalfPlane.qExpansion (1 : ℝ) (inner_fun q)).coeff m = 0) :
    (UpperHalfPlane.qExpansion (1 : ℝ)
        fun z : UpperHalfPlane ↦ ∑ q ∈ s, inner_fun q z).coeff m = 0 := by
  let Φ_total : CuspForm ((Gamma1 M).map (mapGL ℝ)) k := ∑ q ∈ s, Φ_q q
  have hΦ_total_fun : (⇑Φ_total : UpperHalfPlane → ℂ) =
      fun z : UpperHalfPlane ↦ ∑ q ∈ s, inner_fun q z := by
    funext z
    rw [show (⇑Φ_total : UpperHalfPlane → ℂ) z =
      (⇑(∑ q ∈ s, Φ_q q) : UpperHalfPlane → ℂ) z from rfl,
      cuspForm_finsetSum_coe_apply s Φ_q z]
    exact Finset.sum_congr rfl fun q hq ↦ congr_fun (hΦ_q_fun q hq) z
  have h_qexp_sum : UpperHalfPlane.qExpansion (1 : ℝ)
      (fun z : UpperHalfPlane ↦ ∑ q ∈ s, inner_fun q z) =
      ∑ q ∈ s, UpperHalfPlane.qExpansion (1 : ℝ) (Φ_q q).toModularForm' := by
    rw [show (fun z : UpperHalfPlane ↦ ∑ q ∈ s, inner_fun q z) =
          (⇑Φ_total.toModularForm' : UpperHalfPlane → ℂ) from hΦ_total_fun.symm,
      show Φ_total.toModularForm' = ∑ q ∈ s, (Φ_q q).toModularForm' from
          cuspForm_finsetSum_toModularForm' s Φ_q]
    exact map_sum (ModularForm.qExpansionAddHom
      (Γ := (Gamma1 M).map (mapGL ℝ)) (h := (1 : ℝ)) one_pos
      (one_mem_strictPeriods_Gamma1_map M) k) (fun q ↦ (Φ_q q).toModularForm') s
  rw [h_qexp_sum, map_sum]
  refine Finset.sum_eq_zero fun q hq ↦ ?_
  rw [show (UpperHalfPlane.qExpansion (1 : ℝ) (Φ_q q).toModularForm').coeff m =
      (UpperHalfPlane.qExpansion (1 : ℝ) (inner_fun q)).coeff m from
    congrArg (fun ps : PowerSeries ℂ ↦ ps.coeff m)
      (qExpansion_ext2 (⇑(Φ_q q) : UpperHalfPlane → ℂ) (inner_fun q) (hΦ_q_fun q hq))]
  exact h_per_q_zero q hq

/-- A `descendCosetList` slash-sum at a level divisible by `p ^ 2` (so that the coset
count is `p`) collapses to the slash-sum over the upper-triangular representatives
`T_p_upper`. -/
private lemma descendCosetList_slash_sum_eq_T_p_upper_range_slash_sum {L : ℕ} [NeZero L] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (h_cnt : descendCosetCount p L = p)
    (g : UpperHalfPlane → ℂ) :
    (fun z : UpperHalfPlane ↦
        ∑ v : Fin (descendCosetCount p L), (g ∣[k] descendCosetList p L hp v) z) =
      (fun z : UpperHalfPlane ↦
        ∑ v ∈ Finset.range p, (g ∣[k] (T_p_upper p hp.pos v : GL (Fin 2) ℚ)) z) := by
  funext z
  have h_each_eq : ∀ v : Fin p,
      (g ∣[k] descendCosetList p L hp (Fin.cast h_cnt.symm v)) z =
      (g ∣[k] (T_p_upper p hp.pos v.val : GL (Fin 2) ℚ)) z := by
    intro v
    have h_v_lt : (Fin.cast h_cnt.symm v).val < p := v.isLt
    have h_mat : descendCosetList p L hp (Fin.cast h_cnt.symm v) =
        glMap (T_p_upper p hp.pos v.val) := by
      unfold descendCosetList
      rw [dif_pos h_v_lt]
      apply Units.ext
      show (Matrix.GeneralLinearGroup.mkOfDetNeZero _ _).val = (glMap _).val
      rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      show !![(1 : ℝ), (v.val : ℝ); 0, (p : ℝ)] =
          (T_p_upper p hp.pos v.val).val.map (algebraMap ℚ ℝ)
      rw [T_p_upper_coe]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.map_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h_mat]; rfl
  rw [show ∑ v : Fin (descendCosetCount p L), (g ∣[k] descendCosetList p L hp v) z =
        ∑ v : Fin p, (g ∣[k] descendCosetList p L hp (Fin.cast h_cnt.symm v)) z from
    (Fintype.sum_equiv (finCongr h_cnt.symm) _ _ (fun _ ↦ rfl)).symm,
    show ∑ v : Fin p, (g ∣[k] descendCosetList p L hp (Fin.cast h_cnt.symm v)) z =
        ∑ v : Fin p, (g ∣[k] (T_p_upper p hp.pos v.val : GL (Fin 2) ℚ)) z from
    Finset.sum_congr rfl (fun v _ ↦ h_each_eq v)]
  exact Fin.sum_univ_eq_sum_range
    (f := fun n ↦ (g ∣[k] (T_p_upper p hp.pos n : GL (Fin 2) ℚ)) z) p

private lemma delta_slash_sum_coeff_zero_sq_case {L : ℕ} [NeZero L] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpL : p ∣ L) (hp_sq : p ^ 2 ∣ L)
    (Δ_form : CuspForm ((Gamma1 L).map (mapGL ℝ)) k) (m : ℕ)
    (h_apm_zero : (UpperHalfPlane.qExpansion (1 : ℝ) ⇑Δ_form).coeff (p * m) = 0) :
    (UpperHalfPlane.qExpansion (1 : ℝ)
      (fun z ↦ ∑ v : Fin (descendCosetCount p L),
        ((⇑Δ_form : UpperHalfPlane → ℂ) ∣[k]
          descendCosetList p L hp v) z)).coeff m = 0 := by
  have h_cnt : descendCosetCount p L = p := by rw [descendCosetCount, if_pos hp_sq]
  rw [descendCosetList_slash_sum_eq_T_p_upper_range_slash_sum p hp h_cnt
    (⇑Δ_form : UpperHalfPlane → ℂ),
    show (⇑Δ_form : UpperHalfPlane → ℂ) =
      (⇑Δ_form.toModularForm' : UpperHalfPlane → ℂ) from rfl,
    miyake_descent_upper_tri_qExpansion p hp hpL Δ_form.toModularForm' m]
  exact h_apm_zero

/-- Recast-and-apply step for `delta_slash_sum_per_q_inner_fun_coeff_zero` (Miyake 4.6.14
helper).  Given the eigenform data at the deep level `M_q` with the required
divisibility and factorisation hypotheses, rewriting the descend-coset slash-sum at the
oversized level `L = q * M_q` to its standard form lets us invoke
`per_q_slash_sum_at_deep_qexp_zero` directly. -/
private lemma delta_slash_sum_per_q_recast_and_apply
    {M_q : ℕ} [NeZero M_q] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp_dvd_Mq : p ∣ M_q) [NeZero (M_q / p)]
    (q : ℕ) [NeZero q] (hpq : Nat.Coprime p q) (hq_dvd_Mq_div_p : q ∣ M_q / p)
    (χ_F : (ZMod M_q)ˣ →* ℂˣ) (χ_F_low : (ZMod (M_q / p))ˣ →* ℂˣ)
    (h_χ_F_factor : χ_F = χ_F_low.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hp_dvd_Mq)))
    (F_q : CuspForm ((Gamma1 M_q).map (mapGL ℝ)) k)
    (hF_q_char : F_q ∈ cuspFormCharSpace k χ_F)
    (m : ℕ) (hq_not_m : ¬ q ∣ m)
    {L : ℕ} [NeZero L] (h_L_eq : L = q * M_q) :
    (UpperHalfPlane.qExpansion (1 : ℝ)
      (fun z : UpperHalfPlane ↦
        ∑ v : Fin (descendCosetCount p L),
          ((⇑(HeckeRing.GL2.modularFormLevelRaise M_q q k F_q.toModularForm') :
            UpperHalfPlane → ℂ) ∣[k]
            descendCosetList p L hp v) z)).coeff m = 0 := by
  haveI : NeZero (q * M_q) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne M_q)⟩
  rw [show (fun z : UpperHalfPlane ↦
        ∑ v : Fin (descendCosetCount p L),
          ((⇑(HeckeRing.GL2.modularFormLevelRaise M_q q k F_q.toModularForm') :
            UpperHalfPlane → ℂ) ∣[k] descendCosetList p L hp v) z) =
      (fun z : UpperHalfPlane ↦
        ∑ v : Fin (descendCosetCount p (q * M_q)),
          ((⇑(HeckeRing.GL2.modularFormLevelRaise M_q q k F_q.toModularForm') :
            UpperHalfPlane → ℂ) ∣[k] descendCosetList p (q * M_q) hp v) z) from
    slash_sum_descendCoset_level_recast p hp h_L_eq _]
  exact per_q_slash_sum_at_deep_qexp_zero p hp hp_dvd_Mq q hpq
    hq_dvd_Mq_div_p χ_F χ_F_low h_χ_F_factor F_q hF_q_char m hq_not_m

private lemma delta_slash_sum_per_q_inner_fun_coeff_zero {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) {l' : ℕ}
    (hp_not_in : p ∉ l'.primeFactors) [NeZero l'] [NeZero (l' * N)] [NeZero (l' * N / p)]
    [hLl2_NeZero : NeZero ((l' * N) * l' ^ 2)]
    (h_q_NeZero_aux : ∀ q ∈ l'.primeFactors, NeZero ((l' * N * l' ^ 2) / q))
    (h_q_dvd_Ll2_aux : ∀ q ∈ l'.primeFactors, q ∣ (l' * N) * l' ^ 2)
    (χ_M_unit : (ZMod (l' * N))ˣ →* ℂˣ) (χ_M_unit_low : (ZMod (l' * N / p))ˣ →* ℂˣ)
    (hχ_M_unit_eq : χ_M_unit =
      χ_M_unit_low.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd (dvd_mul_of_dvd_right hpN l'))))
    (F_q_fam : (q : ℕ) → (hq : q ∈ l'.primeFactors) →
      haveI := h_q_NeZero_aux q hq
      CuspForm ((Gamma1 (((l' * N) * l' ^ 2) / q)).map (mapGL ℝ)) k)
    (χ_F_fam : (q : ℕ) → (hq : q ∈ l'.primeFactors) →
      haveI := h_q_NeZero_aux q hq
      (ZMod ((l' * N * l' ^ 2) / q))ˣ →* ℂˣ)
    (hF_q_char : ∀ q (hq : q ∈ l'.primeFactors),
      haveI := h_q_NeZero_aux q hq
      F_q_fam q hq ∈ cuspFormCharSpace k (χ_F_fam q hq))
    (hχ_F_fam_rel : ∀ q (hq : q ∈ l'.primeFactors),
      haveI := h_q_NeZero_aux q hq
      (χ_F_fam q hq).comp (ZMod.unitsMap (Nat.div_dvd_of_dvd (h_q_dvd_Ll2_aux q hq))) =
        χ_M_unit.comp (ZMod.unitsMap (Nat.dvd_mul_right (l' * N) (l' ^ 2))))
    (q : l'.primeFactors) (m : ℕ) (hm_cop : Nat.Coprime m l') :
    haveI := h_q_NeZero_aux q.val q.property
    haveI : NeZero q.val := ⟨(Nat.prime_of_mem_primeFactors q.property).ne_zero⟩
    (UpperHalfPlane.qExpansion (1 : ℝ)
      (fun z : UpperHalfPlane ↦
        ∑ v : Fin (descendCosetCount p ((l' * N) * l' ^ 2)),
          ((⇑(HeckeRing.GL2.modularFormLevelRaise ((l' * N * l' ^ 2) / q.val) q.val k
            (F_q_fam q.val q.property).toModularForm') : UpperHalfPlane → ℂ) ∣[k]
            descendCosetList p ((l' * N) * l' ^ 2) hp v) z)).coeff m = 0 := by
  have hq_prime : q.val.Prime := Nat.prime_of_mem_primeFactors q.property
  haveI hq_NeZero : NeZero q.val := ⟨hq_prime.ne_zero⟩
  haveI hM_q_NeZero : NeZero ((l' * N * l' ^ 2) / q.val) := h_q_NeZero_aux q.val q.property
  have hpq_cop : Nat.Coprime p q.val := by
    rw [hp.coprime_iff_not_dvd]
    intro hpq
    exact hp_not_in <| (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hpq ▸ q.property
  have hp_dvd_Mq : p ∣ ((l' * N) * l' ^ 2) / q.val :=
    prime_in_factors_p_dvd_div_q hp hpN hp_not_in q.val q.property
      (h_q_dvd_Ll2_aux q.val q.property)
  haveI : NeZero (((l' * N) * l' ^ 2) / q.val / p) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM_q_NeZero.out) hp_dvd_Mq)
      hp.pos).ne'⟩
  have hq_dvd_Mq_div_p : q.val ∣ ((l' * N) * l' ^ 2) / q.val / p :=
    prime_in_factors_q_dvd_div_q_div_p hp hpN q.val q.property
      (h_q_dvd_Ll2_aux q.val q.property)
  have h_lN_div_p_dvd_Mq_div_p : (l' * N) / p ∣ ((l' * N) * l' ^ 2) / q.val / p :=
    prime_in_factors_lN_div_p_dvd_div_q_div_p hp hpN q.val q.property
  let χ_F_low_q : (ZMod (((l' * N) * l' ^ 2) / q.val / p))ˣ →* ℂˣ :=
    χ_M_unit_low.comp (ZMod.unitsMap h_lN_div_p_dvd_Mq_div_p)
  have h_χ_F_factor : χ_F_fam q.val q.property =
      χ_F_low_q.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hp_dvd_Mq)) :=
    χ_F_factor_via_χ_M_unit_low (p := p) hpN q.val (h_q_dvd_Ll2_aux q.val q.property)
      hp_dvd_Mq h_lN_div_p_dvd_Mq_div_p χ_M_unit χ_M_unit_low hχ_M_unit_eq
      (χ_F_fam q.val q.property) (hχ_F_fam_rel q.val q.property)
  have hq_not_m : ¬ q.val ∣ m := fun hqm ↦
    hq_prime.one_lt.ne' (Nat.dvd_one.mp
      (hm_cop ▸ Nat.dvd_gcd hqm (Nat.dvd_of_mem_primeFactors q.property)))
  have h_q_M_q_eq : (l' * N) * l' ^ 2 = q.val * (((l' * N) * l' ^ 2) / q.val) :=
    (Nat.mul_div_cancel' (h_q_dvd_Ll2_aux q.val q.property)).symm
  exact delta_slash_sum_per_q_recast_and_apply (M_q := ((l' * N) * l' ^ 2) / q.val)
    p hp hp_dvd_Mq q.val hpq_cop hq_dvd_Mq_div_p (χ_F_fam q.val q.property) χ_F_low_q
    h_χ_F_factor (F_q_fam q.val q.property) (hF_q_char q.val q.property) m hq_not_m
    h_q_M_q_eq

private lemma miyake_4_6_14_delta_slash_sum_coeff_zero
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N)
    {l' : ℕ} (hl1_gt : 1 < l') (hl'_sqfree : Squarefree l')
    (hpl' : Nat.Coprime p l')
    (hp_not_in : p ∉ l'.primeFactors)
    [hl'_NeZero : NeZero l']
    [NeZero (l' * N)]
    [NeZero (l' * N / p)]
    (χ_M_unit : (ZMod (l' * N))ˣ →* ℂˣ)
    (χ_M_unit_low : (ZMod (l' * N / p))ˣ →* ℂˣ)
    (hχ_M_unit_eq : χ_M_unit =
      χ_M_unit_low.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd
        (dvd_mul_of_dvd_right hpN l'))))
    (Δ_form : CuspForm ((Gamma1 (l' * N)).map (mapGL ℝ)) k)
    (hΔ_form_χ : Δ_form ∈ cuspFormCharSpace k χ_M_unit)
    (hΔ_form_vanish : ∀ n : ℕ, Nat.Coprime n l' →
      (UpperHalfPlane.qExpansion (1 : ℝ) ⇑Δ_form).coeff n = 0)
    (m : ℕ) (hm_cop : Nat.Coprime m l') :
    (UpperHalfPlane.qExpansion (1 : ℝ)
      (fun z ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
        ((⇑Δ_form : UpperHalfPlane → ℂ) ∣[k]
          descendCosetList p (l' * N) hp v) z)).coeff m = 0 := by
  have hp_dvd_lN : p ∣ l' * N := dvd_mul_of_dvd_right hpN l'
  have h_apm_zero : (UpperHalfPlane.qExpansion (1 : ℝ) ⇑Δ_form).coeff (p * m) = 0 :=
    hΔ_form_vanish (p * m) (Nat.coprime_mul_iff_left.mpr ⟨hpl', hm_cop⟩)
  obtain ⟨g_q_fam, F_q_fam, χ_F_fam, hg_q_char, hF_q_char, hF_eq_g,
      hχ_F_fam_rel, hg_q_qexp⟩ :=
    miyake_4_6_7_squarefree_decomp_with_lower_level χ_M_unit Δ_form hΔ_form_χ l'
      hl1_gt hl'_sqfree hΔ_form_vanish
  haveI hLl2_NeZero : NeZero ((l' * N) * l' ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne (l' * N)) (pow_ne_zero 2 (NeZero.ne l'))⟩
  have hL_dvd : (l' * N) ∣ (l' * N) * l' ^ 2 := Nat.dvd_mul_right _ _
  have h_q_dvd_Ll2_aux : ∀ q ∈ l'.primeFactors, q ∣ (l' * N) * l' ^ 2 := fun q hq ↦
    dvd_mul_of_dvd_right ((Nat.dvd_of_mem_primeFactors hq).trans
      (dvd_pow_self l' two_ne_zero)) _
  have h_q_NeZero_aux : ∀ q ∈ l'.primeFactors, NeZero ((l' * N * l' ^ 2) / q) := fun q hq ↦
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hLl2_NeZero.out) (h_q_dvd_Ll2_aux q hq))
      (Nat.prime_of_mem_primeFactors hq).pos).ne'⟩
  have h_qexp_eq : ∀ n : ℕ,
      (UpperHalfPlane.qExpansion (1 : ℝ) Δ_form).coeff n =
      ∑ q ∈ l'.primeFactors,
        if q ∣ n then (UpperHalfPlane.qExpansion (1 : ℝ) (g_q_fam q)).coeff (n / q)
        else 0 := hg_q_qexp
  have h_Δ_fun_eq :=
    function_identity_Δ_eq_sum_V_q_F (L := l' * N) (k := k) Δ_form l' g_q_fam
      hL_dvd h_q_NeZero_aux h_q_dvd_Ll2_aux F_q_fam hF_eq_g h_qexp_eq
  by_cases hp_sq : p ^ 2 ∣ l' * N
  · exact delta_slash_sum_coeff_zero_sq_case p hp hp_dvd_lN hp_sq Δ_form m h_apm_zero
  ·
    have h_M6_1_pt := miyake_4_6_6_level_commute (N := l' * N) (l := l' ^ 2) (k := k)
      p hp hp_dvd_lN (hpl'.pow_right 2) χ_M_unit Δ_form.toModularForm'
      ((cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
        (k := k) χ_M_unit Δ_form).mpr hΔ_form_χ)
    have hLevel_eq : l' ^ 2 * (l' * N) = l' * N * l' ^ 2 := by ring
    have h_combined_fun : (⇑Δ_form.toModularForm' : UpperHalfPlane → ℂ) =
        fun z ↦ ∑ q ∈ l'.primeFactors.attach,
          (haveI : NeZero ((l' * N * l' ^ 2) / q.val) :=
            h_q_NeZero_aux q.val q.property
           haveI : NeZero q.val :=
            ⟨(Nat.prime_of_mem_primeFactors q.property).ne_zero⟩
           (⇑(HeckeRing.GL2.modularFormLevelRaise ((l' * N * l' ^ 2) / q.val) q.val k
             (F_q_fam q.val q.property).toModularForm') :
             UpperHalfPlane → ℂ) z) := h_Δ_fun_eq
    rw [show (fun z : UpperHalfPlane ↦
        ∑ v : Fin (descendCosetCount p (l' * N)),
          ((⇑Δ_form : UpperHalfPlane → ℂ) ∣[k]
            descendCosetList p (l' * N) hp v) z) =
        (fun z : UpperHalfPlane ↦
          ∑ v : Fin (descendCosetCount p (l' ^ 2 * (l' * N))),
            ((⇑Δ_form.toModularForm' : UpperHalfPlane → ℂ) ∣[k]
              descendCosetList p (l' ^ 2 * (l' * N)) hp v) z) from funext h_M6_1_pt,
      slash_sum_descendCoset_level_recast p hp hLevel_eq (⇑Δ_form.toModularForm'),
      slash_sum_at_M_eq_of_function_eq p ((l' * N) * l' ^ 2) hp k _ _ h_combined_fun,
      slash_sum_linear_over_Finset_sum p ((l' * N) * l' ^ 2) hp k
        l'.primeFactors.attach (fun q ↦ fun z ↦
          (haveI : NeZero ((l' * N * l' ^ 2) / q.val) :=
            h_q_NeZero_aux q.val q.property
           haveI : NeZero q.val :=
            ⟨(Nat.prime_of_mem_primeFactors q.property).ne_zero⟩
           (⇑(HeckeRing.GL2.modularFormLevelRaise ((l' * N * l' ^ 2) / q.val) q.val k
             (F_q_fam q.val q.property).toModularForm') :
             UpperHalfPlane → ℂ) z))]
    set inner_fun : (q : l'.primeFactors) → UpperHalfPlane → ℂ := fun q ↦
      fun z ↦
        ∑ v : Fin (descendCosetCount p ((l' * N) * l' ^ 2)),
          (haveI : NeZero ((l' * N * l' ^ 2) / q.val) := h_q_NeZero_aux q.val q.property
           haveI : NeZero q.val :=
            ⟨(Nat.prime_of_mem_primeFactors q.property).ne_zero⟩
           (⇑(HeckeRing.GL2.modularFormLevelRaise ((l' * N * l' ^ 2) / q.val) q.val k
             (F_q_fam q.val q.property).toModularForm') : UpperHalfPlane → ℂ) ∣[k]
              descendCosetList p ((l' * N) * l' ^ 2) hp v) z
    show (UpperHalfPlane.qExpansion (1 : ℝ)
        (fun z : UpperHalfPlane ↦ ∑ q ∈ l'.primeFactors.attach, inner_fun q z)).coeff m = 0
    have h_per_q_zero : ∀ q : l'.primeFactors,
        (UpperHalfPlane.qExpansion (1 : ℝ) (inner_fun q)).coeff m = 0 := fun q ↦
      delta_slash_sum_per_q_inner_fun_coeff_zero p hp hpN hp_not_in
        h_q_NeZero_aux h_q_dvd_Ll2_aux χ_M_unit χ_M_unit_low hχ_M_unit_eq
        F_q_fam χ_F_fam hF_q_char hχ_F_fam_rel q m hm_cop
    have h_q_M_q_eq : ∀ q : l'.primeFactors,
        q.val * (((l' * N) * l' ^ 2) / q.val) = (l' * N) * l' ^ 2 := fun q ↦
      Nat.mul_div_cancel' (h_q_dvd_Ll2_aux q.val q.property)
    haveI hq_NeZero_inst : ∀ q : l'.primeFactors, NeZero q.val := fun q ↦
      ⟨(Nat.prime_of_mem_primeFactors q.property).ne_zero⟩
    haveI hM_q_NeZero_inst : ∀ q : l'.primeFactors, NeZero ((l' * N * l' ^ 2) / q.val) :=
      fun q ↦ h_q_NeZero_aux q.val q.property
    have hp_dvd_Mq_inst : ∀ q : l'.primeFactors, p ∣ ((l' * N) * l' ^ 2) / q.val := fun q ↦
      prime_in_factors_p_dvd_div_q hp hpN hp_not_in q.val q.property
        (h_q_dvd_Ll2_aux q.val q.property)
    have h_lN_div_p_dvd_Mq_div_p_inst : ∀ q : l'.primeFactors,
        (l' * N) / p ∣ ((l' * N) * l' ^ 2) / q.val / p := fun q ↦
      prime_in_factors_lN_div_p_dvd_div_q_div_p hp hpN q.val q.property
    let χ_F_low_q : (q : l'.primeFactors) →
        (ZMod (((l' * N) * l' ^ 2) / q.val / p))ˣ →* ℂˣ := fun q ↦
      χ_M_unit_low.comp (ZMod.unitsMap (h_lN_div_p_dvd_Mq_div_p_inst q))
    have h_Mq_div_p_eq : ∀ q : l'.primeFactors,
        (q.val * (((l' * N) * l' ^ 2) / q.val)) / p = ((l' * N) * l' ^ 2) / p := fun q ↦ by
      rw [h_q_M_q_eq q]
    haveI hMfull_div_p_NeZero : NeZero (((l' * N) * l' ^ 2) / p) :=
      ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hLl2_NeZero.out)
        (dvd_mul_of_dvd_left hp_dvd_lN _)) hp.pos).ne'⟩
    haveI hMq_div_p_NeZero_inst : ∀ q : l'.primeFactors,
        NeZero (((l' * N) * l' ^ 2) / q.val / p) := fun q ↦
      ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (hM_q_NeZero_inst q).out)
        (hp_dvd_Mq_inst q)) hp.pos).ne'⟩
    have h_per_q_factor : ∀ q : l'.primeFactors,
        (χ_F_fam q.val q.property) = (χ_F_low_q q).comp
          (ZMod.unitsMap (Nat.div_dvd_of_dvd (hp_dvd_Mq_inst q))) := fun q ↦
      χ_F_factor_via_χ_M_unit_low (p := p) hpN q.val
        (h_q_dvd_Ll2_aux q.val q.property) (hp_dvd_Mq_inst q)
        (h_lN_div_p_dvd_Mq_div_p_inst q) χ_M_unit χ_M_unit_low hχ_M_unit_eq
        (χ_F_fam q.val q.property) (hχ_F_fam_rel q.val q.property)
    let Φ_pre : (q : l'.primeFactors) →
        CuspForm ((Gamma1 ((q.val * (((l' * N) * l' ^ 2) / q.val)) / p)).map (mapGL ℝ)) k :=
      fun q ↦
      haveI := hq_NeZero_inst q
      haveI := hM_q_NeZero_inst q
      slash_sum_V_q_cuspForm_descend p hp (hp_dvd_Mq_inst q) q.val
        (χ_F_fam q.val q.property) (χ_F_low_q q) (h_per_q_factor q)
        (F_q_fam q.val q.property) (hF_q_char q.val q.property)
    let Φ_q : (q : l'.primeFactors) →
        CuspForm ((Gamma1 (((l' * N) * l' ^ 2) / p)).map (mapGL ℝ)) k := fun q ↦
      haveI := hq_NeZero_inst q
      haveI := hM_q_NeZero_inst q
      haveI := hMq_div_p_NeZero_inst q
      h_Mq_div_p_eq q ▸ Φ_pre q
    have hΦ_q_fun : ∀ q : l'.primeFactors, ∀ z : UpperHalfPlane,
        (⇑(Φ_q q) : UpperHalfPlane → ℂ) z = inner_fun q z := by
      intro q z
      haveI := hq_NeZero_inst q
      haveI := hM_q_NeZero_inst q
      haveI : NeZero (q.val * (((l' * N) * l' ^ 2) / q.val) / p) := by
        rw [h_Mq_div_p_eq q]; exact hMfull_div_p_NeZero
      haveI : NeZero (q.val * (((l' * N) * l' ^ 2) / q.val)) := by
        rw [h_q_M_q_eq q]; infer_instance
      rw [show (⇑(Φ_q q) : UpperHalfPlane → ℂ) z =
        (⇑(h_Mq_div_p_eq q ▸ Φ_pre q :
          CuspForm ((Gamma1 (((l' * N) * l' ^ 2) / p)).map (mapGL ℝ)) k) :
            UpperHalfPlane → ℂ) z from rfl,
        cuspForm_level_recast_coe_apply (h_Mq_div_p_eq q) (Φ_pre q) z]
      exact congr_fun
        (slash_sum_descendCoset_level_recast p hp (h_q_M_q_eq q)
          (⇑(HeckeRing.GL2.modularFormLevelRaise (((l' * N) * l' ^ 2) / q.val) q.val k
            (F_q_fam q.val q.property).toModularForm') : UpperHalfPlane → ℂ)) z
    exact qExp_finsetSum_inner_fun_coeff_zero_via_cuspForm_family Φ_q inner_fun
      l'.primeFactors.attach (fun q _ ↦ funext (hΦ_q_fun q)) m
      (fun q _ ↦ h_per_q_zero q)

/-- The level descent of a cusp form `f` from `Γ₁(N)` to `Γ₁(N/p)`: the weight-`k` cusp form
obtained by summing the weight-`k` slash-actions of `f` over the descent cosets (Miyake §4.6.14). -/
noncomputable def descendSlashSumCuspForm {N : ℕ} [NeZero N] {k : ℤ} (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N)
    [NeZero (N / p)] (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    (hfχ_mod : f.toModularForm' ∈ modFormCharSpace k χ) :
    CuspForm ((Gamma1 (N / p)).map (mapGL ℝ)) k where
  toFun z := ∑ v : Fin (descendCosetCount p N),
    (⇑f.toModularForm' ∣[k] descendCosetList p N hp v) z
  slash_action_eq' γ hγ := by
    obtain ⟨γ', h_γ'_Gamma1, rfl⟩ := Subgroup.mem_map.mp hγ
    exact miyake_hecke_descend_Gamma1_inv p hp hpN χ χ' hχ_eq hfχ_mod γ' h_γ'_Gamma1
  holo' := by
    show MDifferentiable _ _ (fun z : UpperHalfPlane ↦
      ∑ v : Fin (descendCosetCount p N),
        (⇑f.toModularForm' ∣[k] descendCosetList p N hp v) z)
    rw [show (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p N),
          (⇑f.toModularForm' ∣[k] descendCosetList p N hp v) z) =
        ∑ v : Fin (descendCosetCount p N),
          (⇑f.toModularForm' ∣[k] descendCosetList p N hp v) from
      funext fun z ↦ (Finset.sum_apply _ _ _).symm]
    exact MDifferentiable.sum fun v _ ↦ (ModularFormClass.holo f.toModularForm').slash k _
  zero_at_cusps' {_} hc := miyake_hecke_descend_cusp p hp hpN f hc

lemma descendSlashSumCuspForm_mem_charSpace {N : ℕ} [NeZero N] {k : ℤ} (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N)
    [NeZero (N / p)] (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    (hfχ_mod : f.toModularForm' ∈ modFormCharSpace k χ) :
    descendSlashSumCuspForm χ f p hp hpN χ' hχ_eq hfχ_mod ∈ cuspFormCharSpace k χ' :=
  (cuspFormCharSpace_iff_nebentypus k χ' _).mpr fun γ ↦
    miyake_hecke_descend_char p hp hpN χ χ' hχ_eq hfχ_mod ⟨γ.val, γ.property⟩

private lemma slash_sum_V_p_pointwise_eq_smul_g_low {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (g_low : ModularForm ((Gamma1 (N / p)).map (mapGL ℝ)) k) (z : UpperHalfPlane) :
    (∑ v : Fin (descendCosetCount p N),
        (⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low) ∣[k]
          descendCosetList p N hp v) z) =
      (descendCosetCount p N : ℂ) / (p : ℂ) * g_low z := by
  simp_rw [fun v ↦ multipass_V_p_slash_descendCoset p hp hpN g_low v z]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private lemma slash_sum_V_p_qExp_coeff_eq {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (g_low_cast : CuspForm ((Gamma1 (N / p)).map (mapGL ℝ)) k) (m : ℕ) :
    (UpperHalfPlane.qExpansion (1 : ℝ)
        (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p N),
          (⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k
            g_low_cast.toModularForm') ∣[k] descendCosetList p N hp v) z)).coeff m =
      (descendCosetCount p N : ℂ) / (p : ℂ) *
        (UpperHalfPlane.qExpansion (1 : ℝ)
          (⇑g_low_cast.toModularForm' : UpperHalfPlane → ℂ)).coeff m := by
  set D : ℂ := (descendCosetCount p N : ℂ) / (p : ℂ)
  set f : UpperHalfPlane → ℂ := fun z ↦ ∑ v : Fin (descendCosetCount p N),
    (⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k
      g_low_cast.toModularForm') ∣[k] descendCosetList p N hp v) z
  have h_qexp : UpperHalfPlane.qExpansion (1 : ℝ) f =
      UpperHalfPlane.qExpansion (1 : ℝ) (D • g_low_cast.toModularForm') :=
    qExpansion_ext2 f (D • g_low_cast.toModularForm') <| funext fun z ↦
      slash_sum_V_p_pointwise_eq_smul_g_low p hp hpN g_low_cast.toModularForm' z
  rw [h_qexp, ModularForm.qExpansion_smul (F := ModularForm ((Gamma1 (N / p)).map (mapGL ℝ)) k)
      one_pos (one_mem_strictPeriods_Gamma1_map (N / p)) D g_low_cast.toModularForm',
    PowerSeries.coeff_smul, smul_eq_mul]

private lemma slash_sum_Δ_form_qExp_coeff_zero {N : ℕ} [NeZero N] {k : ℤ} (χ : (ZMod N)ˣ →* ℂˣ)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {l' : ℕ} (hl1_gt : 1 < l') (hl'_sqfree : Squarefree l') (hpl' : Nat.Coprime p l')
    (hp_not_in : p ∉ l'.primeFactors) [NeZero l'] [NeZero (l' * N)] [NeZero (l' * N / p)]
    (χ_M_unit : (ZMod (l' * N))ˣ →* ℂˣ)
    (hχ_M_unit_eq_chi : χ_M_unit = χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N l')))
    (Δ_form : CuspForm ((Gamma1 (l' * N)).map (mapGL ℝ)) k)
    (hΔ_form_χ : Δ_form ∈ cuspFormCharSpace k χ_M_unit)
    (hΔ_form_vanish : ∀ n : ℕ, Nat.Coprime n l' →
      (UpperHalfPlane.qExpansion (1 : ℝ) ⇑Δ_form).coeff n = 0)
    (m : ℕ) (hm_cop : Nat.Coprime m l') :
    (UpperHalfPlane.qExpansion (1 : ℝ)
      (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
        ((⇑Δ_form : UpperHalfPlane → ℂ) ∣[k]
          descendCosetList p (l' * N) hp v) z)).coeff m = 0 := by
  have hp_dvd_lN : p ∣ l' * N := dvd_mul_of_dvd_right hpN l'
  have hNp_dvd_l'Np : N / p ∣ l' * N / p := by
    rw [Nat.mul_div_assoc l' hpN]; exact Nat.dvd_mul_left (N / p) l'
  let χ_lifted_low : (ZMod (l' * N / p))ˣ →* ℂˣ := χ'.comp (ZMod.unitsMap hNp_dvd_l'Np)
  have hχ_M_unit_eq : χ_M_unit =
      χ_lifted_low.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hp_dvd_lN)) := by
    rw [hχ_M_unit_eq_chi, hχ_eq, MonoidHom.comp_assoc, MonoidHom.comp_assoc,
      ZMod.unitsMap_comp, ZMod.unitsMap_comp]
  exact miyake_4_6_14_delta_slash_sum_coeff_zero p hp hpN hl1_gt hl'_sqfree hpl'
    hp_not_in χ_M_unit χ_lifted_low hχ_M_unit_eq Δ_form hΔ_form_χ
    hΔ_form_vanish m hm_cop

private lemma slash_sum_qExp_split_via_cuspForm {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) [NeZero (N / p)]
    (Φ_RHS Φ_Δ : CuspForm ((Gamma1 (N / p)).map (mapGL ℝ)) k)
    (V_p_g_low_fun Δ_form_slash : UpperHalfPlane → ℂ)
    (hΦ_RHS_eq : (⇑Φ_RHS : UpperHalfPlane → ℂ) =
      fun z ↦ ∑ v : Fin (descendCosetCount p N),
        (V_p_g_low_fun ∣[k] descendCosetList p N hp v) z)
    (hΦ_Δ_eq : (⇑Φ_Δ : UpperHalfPlane → ℂ) = Δ_form_slash) (m : ℕ) :
    (UpperHalfPlane.qExpansion (1 : ℝ)
        ((fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p N),
          (V_p_g_low_fun ∣[k] descendCosetList p N hp v) z) + Δ_form_slash)).coeff m =
      (UpperHalfPlane.qExpansion (1 : ℝ)
          (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p N),
            (V_p_g_low_fun ∣[k] descendCosetList p N hp v) z)).coeff m +
        (UpperHalfPlane.qExpansion (1 : ℝ) Δ_form_slash).coeff m := by
  set lhs_fn : UpperHalfPlane → ℂ := fun z : UpperHalfPlane ↦
    ∑ v : Fin (descendCosetCount p N), (V_p_g_low_fun ∣[k] descendCosetList p N hp v) z
  have h_sum_eq_fn : (lhs_fn + Δ_form_slash : UpperHalfPlane → ℂ) =
      (⇑(Φ_RHS.toModularForm' + Φ_Δ.toModularForm') : UpperHalfPlane → ℂ) := by
    funext z
    show lhs_fn z + Δ_form_slash z = (⇑Φ_RHS : UpperHalfPlane → ℂ) z + (⇑Φ_Δ) z
    rw [hΦ_RHS_eq, hΦ_Δ_eq]
  have h_bridge : UpperHalfPlane.qExpansion (1 : ℝ)
        ((lhs_fn + Δ_form_slash) : UpperHalfPlane → ℂ) =
      UpperHalfPlane.qExpansion (1 : ℝ) (Φ_RHS.toModularForm' + Φ_Δ.toModularForm') :=
    qExpansion_ext2 ((lhs_fn + Δ_form_slash) : UpperHalfPlane → ℂ)
      (Φ_RHS.toModularForm' + Φ_Δ.toModularForm') h_sum_eq_fn
  rw [h_bridge,
    ModularForm.qExpansion_add (Γ := (Gamma1 (N / p)).map (mapGL ℝ)) (h := (1 : ℝ))
      (a := k) (b := k) one_pos (one_mem_strictPeriods_Gamma1_map (N / p))
      Φ_RHS.toModularForm' Φ_Δ.toModularForm', map_add,
    qExpansion_ext2 Φ_RHS.toModularForm' (lhs_fn : UpperHalfPlane → ℂ) hΦ_RHS_eq,
    qExpansion_ext2 Φ_Δ.toModularForm' (Δ_form_slash : UpperHalfPlane → ℂ) hΦ_Δ_eq]
  rfl

/-- If `F = Vp + g` pointwise, the `descendCosetList` slash-sum of `F` splits as the sum
of the slash-sums of `Vp` and `g`. -/
private lemma descendCosetList_slash_sum_eq_add_of_sub
    {M : ℕ} [NeZero M] {k : ℤ} (p : ℕ) [NeZero p] (hp : p.Prime)
    (F Vp g : UpperHalfPlane → ℂ) (h_g_eq : ∀ w, g w = F w - Vp w) :
    (fun z : UpperHalfPlane ↦
        ∑ v : Fin (descendCosetCount p M), (F ∣[k] descendCosetList p M hp v) z) =
      ((fun z ↦ ∑ v : Fin (descendCosetCount p M),
          (Vp ∣[k] descendCosetList p M hp v) z) +
        fun z ↦ ∑ v : Fin (descendCosetCount p M),
          (g ∣[k] descendCosetList p M hp v) z) := by
  have h_F_eq : F = Vp + g := by
    funext w
    simp [Pi.add_apply, h_g_eq w]
  simp_rw [h_F_eq]
  funext z
  simp only [SlashAction.add_slash, Finset.sum_add_distrib, Pi.add_apply]

private lemma miyake_descent_l_prime_gt_one_helper {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {l' : ℕ} (hl1_gt : 1 < l') (hl'_sqfree : Squarefree l') (hpl' : Nat.Coprime p l')
    (hp_not_in : p ∉ l'.primeFactors)
    [hl'_NeZero : NeZero l'] [NeZero (l' * N)] [NeZero (l' * N / p)]
    (g_low_cast : CuspForm ((Gamma1 (l' * N / p)).map (mapGL ℝ)) k)
    (χ_M_unit : (ZMod (l' * N))ˣ →* ℂˣ)
    (hχ_M_unit_eq_chi : χ_M_unit = χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N l')))
    (Δ_form : CuspForm ((Gamma1 (l' * N)).map (mapGL ℝ)) k)
    (hΔ_form_χ : Δ_form ∈ cuspFormCharSpace k χ_M_unit)
    (hΔ_form_vanish : ∀ n : ℕ, Nat.Coprime n l' →
      (UpperHalfPlane.qExpansion (1 : ℝ) ⇑Δ_form).coeff n = 0)
    (hΔ_form_fun_eq : (⇑Δ_form : UpperHalfPlane → ℂ) =
      fun z ↦ ⇑f.toModularForm' z -
        ⇑((HeckeRing.GL2.modularFormLevelRaise (l' * N / p) p k)
          g_low_cast.toModularForm') z)
    (m : ℕ) (hm_cop : Nat.Coprime m l') :
    (PowerSeries.coeff m) (UpperHalfPlane.qExpansion (1 : ℝ)
      (fun z ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
        (⇑f.toModularForm' ∣[k] descendCosetList p (l' * N) hp v) z)) =
    (PowerSeries.coeff m) (UpperHalfPlane.qExpansion (1 : ℝ)
      (fun z ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
        (⇑((HeckeRing.GL2.modularFormLevelRaise (l' * N / p) p k)
          g_low_cast.toModularForm') ∣[k] descendCosetList p (l' * N) hp v) z)) := by
  have hp_dvd_lN : p ∣ l' * N := dvd_mul_of_dvd_right hpN l'
  set V_p_g_low_fun : UpperHalfPlane → ℂ :=
    ⇑((HeckeRing.GL2.modularFormLevelRaise (l' * N / p) p k)
      g_low_cast.toModularForm')
  set D_lifted : ℂ := (descendCosetCount p (l' * N) : ℂ) / (p : ℂ)
  set Δ_form_slash : UpperHalfPlane → ℂ :=
    fun z ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
      ((⇑Δ_form : UpperHalfPlane → ℂ) ∣[k] descendCosetList p (l' * N) hp v) z
  have hNp_dvd_l'Np : N / p ∣ l' * N / p := by
    rw [Nat.mul_div_assoc l' hpN]; exact Nat.dvd_mul_left (N / p) l'
  let χ_M_unit_low : (ZMod (l' * N / p))ˣ →* ℂˣ :=
    χ'.comp (ZMod.unitsMap hNp_dvd_l'Np)
  have hχ_M_unit_eq : χ_M_unit =
      χ_M_unit_low.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hp_dvd_lN)) := by
    rw [hχ_M_unit_eq_chi, hχ_eq, MonoidHom.comp_assoc, MonoidHom.comp_assoc,
      ZMod.unitsMap_comp, ZMod.unitsMap_comp]
  let Φ_RHS_cusp : CuspForm ((Gamma1 (l' * N / p)).map (mapGL ℝ)) k :=
    D_lifted • g_low_cast
  let Φ_Δ : CuspForm ((Gamma1 (l' * N / p)).map (mapGL ℝ)) k :=
    descendSlashSumCuspForm χ_M_unit Δ_form p hp hp_dvd_lN χ_M_unit_low
      hχ_M_unit_eq
      ((cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
        (k := k) χ_M_unit Δ_form).mpr hΔ_form_χ)
  have hΦ_RHS_cusp_fun_eq : (⇑Φ_RHS_cusp : UpperHalfPlane → ℂ) =
      fun z ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
        (V_p_g_low_fun ∣[k] descendCosetList p (l' * N) hp v) z :=
    funext fun z ↦
      (slash_sum_V_p_pointwise_eq_smul_g_low p hp hp_dvd_lN
        g_low_cast.toModularForm' z).symm
  have h_LHS_fun_eq : (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
      (⇑f.toModularForm' ∣[k] descendCosetList p (l' * N) hp v) z) =
      ((fun z ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
        (V_p_g_low_fun ∣[k] descendCosetList p (l' * N) hp v) z) +
        Δ_form_slash : UpperHalfPlane → ℂ) :=
    descendCosetList_slash_sum_eq_add_of_sub p hp (⇑f.toModularForm')
      V_p_g_low_fun (⇑Δ_form) (fun w ↦ congr_fun hΔ_form_fun_eq w)
  rw [h_LHS_fun_eq,
    slash_sum_qExp_split_via_cuspForm p hp Φ_RHS_cusp Φ_Δ V_p_g_low_fun
      Δ_form_slash hΦ_RHS_cusp_fun_eq rfl m,
    slash_sum_V_p_qExp_coeff_eq p hp hp_dvd_lN g_low_cast m,
    slash_sum_Δ_form_qExp_coeff_zero χ p hp hpN χ' hχ_eq hl1_gt hl'_sqfree hpl'
      hp_not_in χ_M_unit hχ_M_unit_eq_chi Δ_form hΔ_form_χ hΔ_form_vanish m hm_cop,
    add_zero]

private lemma cuspForm_cast_coe {A B : ℕ} {k : ℤ} (h : A = B)
    (x : CuspForm ((Gamma1 A).map (mapGL ℝ)) k) :
    (⇑(h ▸ x : CuspForm ((Gamma1 B).map (mapGL ℝ)) k) : UpperHalfPlane → ℂ) = ⇑x := by
  cases h; rfl

private lemma modularForm_cast_coe {A B : ℕ} [NeZero A] [NeZero B] {k : ℤ} (h : A = B)
    (x : ModularForm ((Gamma1 A).map (mapGL ℝ)) k) :
    (⇑(h ▸ x : ModularForm ((Gamma1 B).map (mapGL ℝ)) k) :
      UpperHalfPlane → ℂ) = ⇑x := by
  cases h; rfl

private lemma descendCosetCount_mul_left_of_coprime
    {p l N : ℕ} (hpl : Nat.Coprime p l) :
    descendCosetCount p (l * N) = descendCosetCount p N := by
  unfold descendCosetCount
  have h_iff : p ^ 2 ∣ l * N ↔ p ^ 2 ∣ N :=
    ⟨fun h_sq ↦ (hpl.pow_left 2).dvd_of_dvd_mul_left h_sq, fun h ↦ h.mul_left l⟩
  split_ifs <;> tauto

lemma qExpansion_smul_cuspForm_coeff_aux {M : ℕ} [NeZero M] {k : ℤ} (c : ℂ)
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) (m : ℕ) :
    (UpperHalfPlane.qExpansion (1 : ℝ) (c • f)).coeff m =
      c * (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m := by
  change (UpperHalfPlane.qExpansion (1 : ℝ) (c • f.toModularForm')).coeff m =
    c * (UpperHalfPlane.qExpansion (1 : ℝ) (⇑f : UpperHalfPlane → ℂ)).coeff m
  rw [ModularForm.qExpansion_smul (F := ModularForm ((Gamma1 M).map (mapGL ℝ)) k) one_pos
    (one_mem_strictPeriods_Gamma1_map M) c f.toModularForm',
    PowerSeries.coeff_smul, smul_eq_mul]
  rfl

/-- Helper for `descent_slashSum_qExp_coeff_eq_Dp_g_low_coeff`: at level `L` with `p ∣ L`,
the `q`-expansion coefficient of the descend-coset slash-sum of the `V_p`-lift of
`g_low_cast` equals `D_p · (q-coeff of g_low)`, using `h_cast_fun : ⇑g_low_cast = ⇑g_low`. -/
private lemma slash_sum_V_p_lifted_qExp_coeff_at_cast_eq
    {L M : ℕ} [NeZero L] [NeZero M] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpL : p ∣ L) [NeZero (L / p)]
    (g_low : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (g_low_cast : CuspForm ((Gamma1 (L / p)).map (mapGL ℝ)) k)
    (h_cast_fun : (⇑g_low_cast : UpperHalfPlane → ℂ) = ⇑g_low) (m : ℕ) :
    (UpperHalfPlane.qExpansion (1 : ℝ)
        fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p L),
          (⇑(HeckeRing.GL2.modularFormLevelRaise (L / p) p k g_low_cast.toModularForm') ∣[k]
            descendCosetList p L hp v) z).coeff m =
      (descendCosetCount p L : ℂ) / (p : ℂ) *
        (UpperHalfPlane.qExpansion (1 : ℝ) g_low).coeff m := by
  set Vp_slash_lifted_fun : UpperHalfPlane → ℂ := fun z ↦
    ∑ v : Fin (descendCosetCount p L),
      (⇑(HeckeRing.GL2.modularFormLevelRaise (L / p) p k g_low_cast.toModularForm') ∣[k]
        descendCosetList p L hp v) z
  set Dp_g_low : UpperHalfPlane → ℂ := fun z ↦
    (descendCosetCount p L : ℂ) / (p : ℂ) * g_low z
  have h_Vp_slash_lifted : ∀ z : UpperHalfPlane, Vp_slash_lifted_fun z = Dp_g_low z := fun z ↦ by
    simp_rw [Vp_slash_lifted_fun, fun v ↦ multipass_V_p_slash_descendCoset p hp hpL
      g_low_cast.toModularForm' v z]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      show (g_low_cast.toModularForm' : UpperHalfPlane → ℂ) z = g_low z by
        show (⇑g_low_cast : UpperHalfPlane → ℂ) z = ⇑g_low z; rw [h_cast_fun]]
    ring
  have h_Vp_qexp_eq : UpperHalfPlane.qExpansion (1 : ℝ) Vp_slash_lifted_fun =
      UpperHalfPlane.qExpansion (1 : ℝ) Dp_g_low :=
    qExpansion_ext2 Vp_slash_lifted_fun Dp_g_low (funext h_Vp_slash_lifted)
  rw [h_Vp_qexp_eq]
  exact qExpansion_smul_cuspForm_coeff_aux _ g_low m

private lemma qExpansion_sub_cuspForm_coeff {M : ℕ} [NeZero M] {k : ℤ}
    (a b : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) (n : ℕ) :
    (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) ⇑(a - b)) =
    (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) ⇑a) -
    (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) ⇑b) := by
  have h1 := one_mem_strictPeriods_Gamma1_map M
  have h_sub_qexp : UpperHalfPlane.qExpansion (1 : ℝ) (a - b) =
      UpperHalfPlane.qExpansion (1 : ℝ) a - UpperHalfPlane.qExpansion (1 : ℝ) b := by
    rw [sub_eq_add_neg, sub_eq_add_neg, ← ModularForm.qExpansion_neg one_pos h1 b]
    exact ModularForm.qExpansion_add (Γ := (Gamma1 M).map (mapGL ℝ))
      (h := (1 : ℝ)) (a := k) (b := k) one_pos h1 a (- b)
  rw [show UpperHalfPlane.qExpansion (1 : ℝ) (⇑(a - b) : UpperHalfPlane → ℂ) =
    UpperHalfPlane.qExpansion (1 : ℝ) (a - b) from rfl, h_sub_qexp, map_sub]

private lemma f_qExp_eq_levelRaise_qExp_at_coprime {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {p : ℕ} [NeZero p] (hp : p.Prime) {l' : ℕ}
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p * l') →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0)
    {Mp : ℕ} [NeZero Mp] (g_low_cast : CuspForm ((Gamma1 Mp).map (mapGL ℝ)) k)
    {L : ℕ} [NeZero L] (g_low : CuspForm ((Gamma1 L).map (mapGL ℝ)) k)
    (h_cast_fun : (⇑g_low_cast : UpperHalfPlane → ℂ) = ⇑g_low)
    (hg_low_qexp : ∀ n : ℕ, p ∣ n → Nat.Coprime n l' →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n =
        (UpperHalfPlane.qExpansion (1 : ℝ) g_low).coeff (n / p)) :
    ∀ n : ℕ, Nat.Coprime n l' →
      (UpperHalfPlane.qExpansion (1 : ℝ) ⇑f).coeff n =
        (UpperHalfPlane.qExpansion (1 : ℝ)
          ⇑(HeckeRing.GL2.modularFormLevelRaise Mp p k
            g_low_cast.toModularForm')).coeff n := by
  intro n hn_cop
  rw [HeckeRing.GL2.qExpansion_one_modularFormLevelRaise_coeff _ n]
  by_cases hpn : p ∣ n
  · rw [if_pos hpn, hg_low_qexp n hpn hn_cop,
      show UpperHalfPlane.qExpansion (1 : ℝ) g_low_cast.toModularForm' =
        UpperHalfPlane.qExpansion (1 : ℝ) (⇑g_low : UpperHalfPlane → ℂ) from
        h_cast_fun ▸ rfl]
  · rw [if_neg hpn]
    exact h_vanish n (Nat.Coprime.mul_right ((hp.coprime_iff_not_dvd).mpr hpn).symm hn_cop)

private lemma g_bundled_qExp_eq_levelRaise_qExp {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {p : ℕ} [NeZero p] (hp : p.Prime)
    {l' : ℕ} [NeZero l'] (hpl' : Nat.Coprime p l')
    [NeZero (l' * N)] [NeZero ((l' * N) / p)]
    (g_low_cast : CuspForm ((Gamma1 ((l' * N) / p)).map (mapGL ℝ)) k)
    {L : ℕ} [NeZero L] (g_low : CuspForm ((Gamma1 L).map (mapGL ℝ)) k)
    (h_cast_fun : (⇑g_low_cast : UpperHalfPlane → ℂ) = ⇑g_low)
    (hg_low_full_qexp : ∀ m : ℕ,
      (UpperHalfPlane.qExpansion (1 : ℝ) g_low).coeff m =
        if Nat.Coprime m l' then
          (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff (p * m)
        else 0)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p * l') →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0)
    (g_bundled : CuspForm ((Gamma1 (l' * N)).map (mapGL ℝ)) k)
    (hg_bundled_qexp : ∀ n : ℕ,
      (UpperHalfPlane.qExpansion (1 : ℝ) g_bundled).coeff n =
        if Nat.Coprime n l' then
          (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n
        else 0)
    (hpM_eq : p * ((l' * N) / p) = l' * N) :
    (⇑g_bundled : UpperHalfPlane → ℂ) =
      ⇑(HeckeRing.GL2.modularFormLevelRaise ((l' * N) / p) p k
        g_low_cast.toModularForm') := by
  haveI hpMp_NeZero : NeZero (p * ((l' * N) / p)) := by rw [hpM_eq]; infer_instance
  have h_qExp_eq : ∀ n : ℕ,
      (UpperHalfPlane.qExpansion (1 : ℝ) ⇑g_bundled).coeff n =
        (UpperHalfPlane.qExpansion (1 : ℝ)
          ⇑(HeckeRing.GL2.modularFormLevelRaise ((l' * N) / p) p k
            g_low_cast.toModularForm')).coeff n := by
    intro n
    rw [hg_bundled_qexp n, HeckeRing.GL2.qExpansion_one_modularFormLevelRaise_coeff _ n]
    by_cases hpn : p ∣ n
    · rw [if_pos hpn,
        show UpperHalfPlane.qExpansion (1 : ℝ) g_low_cast.toModularForm' =
          UpperHalfPlane.qExpansion (1 : ℝ) (⇑g_low : UpperHalfPlane → ℂ) from
            h_cast_fun ▸ rfl,
        hg_low_full_qexp (n / p)]
      have h_cop_iff : Nat.Coprime n l' ↔ Nat.Coprime (n / p) l' := by
        rcases hpn with ⟨q_idx, hq_idx_eq⟩
        rw [hq_idx_eq, Nat.mul_div_cancel_left _ hp.pos, Nat.coprime_mul_iff_left]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨hpl', h⟩⟩
      by_cases hcop : Nat.Coprime n l'
      · rw [if_pos hcop, if_pos (h_cop_iff.mp hcop),
          show p * (n / p) = n from Nat.mul_div_cancel' hpn]
      · rw [if_neg hcop, if_neg (mt h_cop_iff.mpr hcop)]
    · rw [if_neg hpn]
      by_cases hcop : Nat.Coprime n l'
      · rw [if_pos hcop]
        exact h_vanish n
          (Nat.Coprime.mul_right ((hp.coprime_iff_not_dvd).mpr hpn).symm hcop)
      · rw [if_neg hcop]
  let Vp_form : ModularForm ((Gamma1 (p * ((l' * N) / p))).map (mapGL ℝ)) k :=
    HeckeRing.GL2.modularFormLevelRaise ((l' * N) / p) p k g_low_cast.toModularForm'
  let Vp_form_cast : ModularForm ((Gamma1 (l' * N)).map (mapGL ℝ)) k :=
    hpM_eq ▸ Vp_form
  have h_Vp_form_cast_fun : (⇑Vp_form_cast : UpperHalfPlane → ℂ) = ⇑Vp_form :=
    modularForm_cast_coe hpM_eq Vp_form
  have h_eq := modularForm_fun_eq_of_qExp_eq_at_period_one (M := l' * N) (k := k)
    (one_mem_strictPeriods_Gamma1_map (l' * N))
    g_bundled.toModularForm' Vp_form_cast (by
      intro n
      have h_V : UpperHalfPlane.qExpansion (1 : ℝ) Vp_form_cast =
          UpperHalfPlane.qExpansion (1 : ℝ) Vp_form := by
        show UpperHalfPlane.qExpansion (1 : ℝ) (⇑Vp_form_cast : UpperHalfPlane → ℂ) =
          UpperHalfPlane.qExpansion (1 : ℝ) (⇑Vp_form : UpperHalfPlane → ℂ)
        rw [h_Vp_form_cast_fun]
      rw [h_V]
      exact h_qExp_eq n)
  rw [show (⇑g_bundled : UpperHalfPlane → ℂ) =
        (⇑g_bundled.toModularForm' : UpperHalfPlane → ℂ) from rfl, h_eq,
    h_Vp_form_cast_fun]

private lemma descent_l_prime_gt_one_apply {N : ℕ} [NeZero N] {k : ℤ} (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hfχ : f ∈ cuspFormCharSpace k χ)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {l' : ℕ} (hl1_gt : 1 < l') (hl'_sqfree : Squarefree l') (hpl' : Nat.Coprime p l')
    (hl'_dvd : ∀ q ∈ l'.primeFactors, q ∈ N.primeFactors)
    (hp_not_in : p ∉ l'.primeFactors)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p * l') →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0)
    [NeZero l'] [NeZero (l' * N)] [NeZero ((l' * N) / p)]
    {L : ℕ} [NeZero L] (g_low : CuspForm ((Gamma1 L).map (mapGL ℝ)) k)
    (g_low_cast : CuspForm ((Gamma1 ((l' * N) / p)).map (mapGL ℝ)) k)
    (h_cast_fun : (⇑g_low_cast : UpperHalfPlane → ℂ) = ⇑g_low)
    (hg_low_full_qexp : ∀ m : ℕ,
      (UpperHalfPlane.qExpansion (1 : ℝ) g_low).coeff m =
        if Nat.Coprime m l' then
          (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff (p * m)
        else 0)
    (m : ℕ) (hm_cop : Nat.Coprime m l') :
    (PowerSeries.coeff m) (UpperHalfPlane.qExpansion (1 : ℝ)
      (fun z ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
        (⇑f.toModularForm' ∣[k] descendCosetList p (l' * N) hp v) z)) =
    (PowerSeries.coeff m) (UpperHalfPlane.qExpansion (1 : ℝ)
      (fun z ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
        (⇑((HeckeRing.GL2.modularFormLevelRaise (l' * N / p) p k)
          g_low_cast.toModularForm') ∣[k] descendCosetList p (l' * N) hp v) z)) := by
  have hl'_pos : 0 < l' := lt_trans Nat.zero_lt_one hl1_gt
  let χ_M_unit : (ZMod (l' * N))ˣ →* ℂˣ :=
    χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N l'))
  obtain ⟨g_bundled, hg_bundled_χ, _hg_bundled_supp, hg_bundled_qexp⟩ :=
    miyake_g_p_supported χ f hfχ p hp l' hl'_pos hl'_sqfree hl'_dvd h_vanish
  have hN_dvd_lN : N ∣ l' * N := Nat.dvd_mul_left N l'
  let f_restricted : CuspForm ((Gamma1 (l' * N)).map (mapGL ℝ)) k :=
    CuspForm.restrictSubgroup (Gamma1_map_le_Gamma1_map_of_dvd hN_dvd_lN) f
  have hf_restricted_χ : f_restricted ∈ cuspFormCharSpace k χ_M_unit :=
    cuspForm_restrictSubgroup_mem_cuspFormCharSpace χ hN_dvd_lN hfχ
  let Δ_form : CuspForm ((Gamma1 (l' * N)).map (mapGL ℝ)) k :=
    f_restricted - g_bundled
  have hΔ_form_χ : Δ_form ∈ cuspFormCharSpace k χ_M_unit :=
    Submodule.sub_mem _ hf_restricted_χ hg_bundled_χ
  have hp_dvd_lN : p ∣ l' * N := dvd_mul_of_dvd_right hpN l'
  have hpM_eq : p * ((l' * N) / p) = l' * N := Nat.mul_div_cancel' hp_dvd_lN
  have h_Δ_form_sub_qexp : ∀ n : ℕ,
      (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) ⇑Δ_form) =
      (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) ⇑f_restricted) -
      (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) ⇑g_bundled) :=
    fun n ↦ qExpansion_sub_cuspForm_coeff f_restricted g_bundled n
  have hΔ_form_vanish : ∀ n : ℕ, Nat.Coprime n l' →
      (UpperHalfPlane.qExpansion (1 : ℝ) ⇑Δ_form).coeff n = 0 := fun n hn ↦ by
    rw [h_Δ_form_sub_qexp n,
      show (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) ⇑f_restricted) =
        (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) ⇑f) from rfl,
      hg_bundled_qexp n, if_pos hn, sub_self]
  have h_g_bundled_eq_Vp :=
    g_bundled_qExp_eq_levelRaise_qExp f hp hpl' g_low_cast g_low h_cast_fun
      hg_low_full_qexp h_vanish g_bundled hg_bundled_qexp hpM_eq
  have hΔ_form_fun_eq : (⇑Δ_form : UpperHalfPlane → ℂ) =
      fun z ↦ ⇑f.toModularForm' z -
        ⇑((HeckeRing.GL2.modularFormLevelRaise (l' * N / p) p k)
          g_low_cast.toModularForm') z := by
    funext z
    show (⇑f_restricted : UpperHalfPlane → ℂ) z - (⇑g_bundled) z = _
    rw [h_g_bundled_eq_Vp]
    rfl
  exact miyake_descent_l_prime_gt_one_helper χ f p hp hpN χ' hχ_eq
    hl1_gt hl'_sqfree hpl' hp_not_in g_low_cast χ_M_unit rfl Δ_form hΔ_form_χ
    hΔ_form_vanish hΔ_form_fun_eq m hm_cop

private lemma descent_slashSum_qExp_coeff_eq_of_l_eq_one {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {p : ℕ} [NeZero p] (hp : p.Prime)
    {l' : ℕ} [NeZero l'] (hl'_le : l' ≤ 1)
    [NeZero (l' * N)] [NeZero ((l' * N) / p)]
    (g_low_cast : CuspForm ((Gamma1 ((l' * N) / p)).map (mapGL ℝ)) k)
    (hp_dvd_lN : p ∣ l' * N)
    (h_delta_Fourier_vanish : ∀ n : ℕ, Nat.Coprime n l' →
      (UpperHalfPlane.qExpansion (1 : ℝ) ⇑f).coeff n =
      (UpperHalfPlane.qExpansion (1 : ℝ)
        ⇑(HeckeRing.GL2.modularFormLevelRaise ((l' * N) / p) p k
          g_low_cast.toModularForm')).coeff n)
    (m : ℕ) :
    (UpperHalfPlane.qExpansion (1 : ℝ)
      (fun z ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
        (⇑f.toModularForm' ∣[k] descendCosetList p (l' * N) hp v) z)).coeff m =
    (UpperHalfPlane.qExpansion (1 : ℝ)
      (fun z ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
        (⇑(HeckeRing.GL2.modularFormLevelRaise ((l' * N) / p) p k
          g_low_cast.toModularForm') ∣[k] descendCosetList p (l' * N) hp v) z)).coeff m := by
  have hl'_eq_1 : l' = 1 := by have := NeZero.pos l'; lia
  have h_all_cop : ∀ n : ℕ, Nat.Coprime n l' := fun n ↦ hl'_eq_1 ▸ Nat.coprime_one_right n
  have hp_M_eq_N : p * ((l' * N) / p) = N := by
    rw [Nat.mul_div_cancel' hp_dvd_lN, hl'_eq_1, one_mul]
  rw [miyake_descent_l_prime_eq_one_helper f g_low_cast hp_M_eq_N
    (fun n ↦ h_delta_Fourier_vanish n (h_all_cop n))]

private lemma descent_slashSum_qExp_coeff_eq_Dp_g_low_coeff {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {l' : ℕ} (hl'_sqfree : Squarefree l') (hpl' : Nat.Coprime p l')
    (hl'_dvd : ∀ q ∈ l'.primeFactors, q ∈ N.primeFactors) (hp_not_in : p ∉ l'.primeFactors)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p * l') →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0)
    [NeZero l'] [NeZero (l' * N)] [NeZero ((l' * N) / p)]
    {L : ℕ} [NeZero L] (g_low : CuspForm ((Gamma1 L).map (mapGL ℝ)) k)
    (g_low_cast : CuspForm ((Gamma1 ((l' * N) / p)).map (mapGL ℝ)) k)
    (h_cast_fun : (⇑g_low_cast : UpperHalfPlane → ℂ) = ⇑g_low)
    (hg_low_qexp : ∀ n : ℕ, p ∣ n → Nat.Coprime n l' →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n =
        (UpperHalfPlane.qExpansion (1 : ℝ) g_low).coeff (n / p))
    (hg_low_full_qexp : ∀ m : ℕ,
      (UpperHalfPlane.qExpansion (1 : ℝ) g_low).coeff m =
        if Nat.Coprime m l' then
          (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff (p * m)
        else 0)
    (m : ℕ) (hm_cop : Nat.Coprime m l') :
    (UpperHalfPlane.qExpansion (1 : ℝ)
      (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
        (⇑f.toModularForm' ∣[k] descendCosetList p (l' * N) hp v) z)).coeff m =
      (descendCosetCount p (l' * N) : ℂ) / (p : ℂ) *
        (UpperHalfPlane.qExpansion (1 : ℝ) g_low).coeff m := by
  have hp_dvd_lN : p ∣ l' * N := dvd_mul_of_dvd_right hpN l'
  have h_delta_Fourier_vanish :=
    f_qExp_eq_levelRaise_qExp_at_coprime f hp h_vanish g_low_cast g_low h_cast_fun hg_low_qexp
  have h_Psi_eq_Vp_coeff :
      (UpperHalfPlane.qExpansion (1 : ℝ)
          fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
            (⇑f.toModularForm' ∣[k] descendCosetList p (l' * N) hp v) z).coeff m =
        (UpperHalfPlane.qExpansion (1 : ℝ)
          fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
            (⇑(HeckeRing.GL2.modularFormLevelRaise ((l' * N) / p) p k
              g_low_cast.toModularForm') ∣[k] descendCosetList p (l' * N) hp v) z).coeff m := by
    rcases Nat.lt_or_ge 1 l' with hl1_gt | hl1_le
    · exact descent_l_prime_gt_one_apply χ f hfχ p hp hpN χ' hχ_eq
        hl1_gt hl'_sqfree hpl' hl'_dvd hp_not_in h_vanish g_low g_low_cast
        h_cast_fun hg_low_full_qexp m hm_cop
    · exact descent_slashSum_qExp_coeff_eq_of_l_eq_one f hp hl1_le g_low_cast
        hp_dvd_lN h_delta_Fourier_vanish m
  rw [h_Psi_eq_Vp_coeff, slash_sum_V_p_lifted_qExp_coeff_at_cast_eq p hp hp_dvd_lN
    g_low g_low_cast h_cast_fun m]

lemma Φ_qExp_coeff_eq_count_div_p_mul_g_low_coeff {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    (hfχ_mod : f.toModularForm' ∈ modFormCharSpace k χ)
    {l' : ℕ} (hl'_pos : 0 < l') (hl'_sqfree : Squarefree l') (hpl' : Nat.Coprime p l')
    (hl'_dvd : ∀ q ∈ l'.primeFactors, q ∈ N.primeFactors) (hp_not_in : p ∉ l'.primeFactors)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p * l') →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0)
    [NeZero (l' * (N / p))] (g_low : CuspForm ((Gamma1 (l' * (N / p))).map (mapGL ℝ)) k)
    (hg_low_qexp : ∀ n : ℕ, p ∣ n → Nat.Coprime n l' →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n =
        (UpperHalfPlane.qExpansion (1 : ℝ) g_low).coeff (n / p))
    (hg_low_full_qexp : ∀ m : ℕ,
      (UpperHalfPlane.qExpansion (1 : ℝ) g_low).coeff m =
        if Nat.Coprime m l' then
          (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff (p * m)
        else 0)
    (m : ℕ) (hm_cop : Nat.Coprime m l') :
    (UpperHalfPlane.qExpansion (1 : ℝ)
      (descendSlashSumCuspForm χ f p hp hpN χ' hχ_eq hfχ_mod)).coeff m =
      (descendCosetCount p N : ℂ) / (p : ℂ) *
        (UpperHalfPlane.qExpansion (1 : ℝ) g_low).coeff m := by
  haveI hl'_NeZero : NeZero l' := ⟨hl'_pos.ne'⟩
  haveI : NeZero (l' * N) := ⟨Nat.mul_ne_zero hl'_pos.ne' (NeZero.ne N)⟩
  have hp_dvd_lN : p ∣ l' * N := dvd_mul_of_dvd_right hpN l'
  haveI hlN_div_NeZero : NeZero ((l' * N) / p) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hl'_pos (NeZero.pos N)) hp_dvd_lN)
      hp.pos).ne'⟩
  have h_D_eq : descendCosetCount p (l' * N) = descendCosetCount p N :=
    descendCosetCount_mul_left_of_coprime hpl'
  set Φ_fun : UpperHalfPlane → ℂ := fun z ↦
      ∑ v : Fin (descendCosetCount p N),
        (⇑f.toModularForm' ∣[k] descendCosetList p N hp v) z
  set Ψ_fun : UpperHalfPlane → ℂ := fun z ↦
      ∑ v : Fin (descendCosetCount p (l' * N)),
        (⇑f.toModularForm' ∣[k] descendCosetList p (l' * N) hp v) z
  have hΦ_eq_Ψ : Φ_fun = Ψ_fun :=
    funext fun z ↦
      miyake_4_6_6_level_commute p hp hpN hpl' χ f.toModularForm' hfχ_mod z
  have h_Mp_eq : (l' * N) / p = l' * (N / p) := by
    rcases hpN with ⟨d, hd⟩
    rw [hd, show l' * (p * d) = p * (l' * d) by ring,
      Nat.mul_div_cancel_left _ hp.pos, Nat.mul_div_cancel_left _ hp.pos]
  let g_low_cast : CuspForm ((Gamma1 ((l' * N) / p)).map (mapGL ℝ)) k :=
    h_Mp_eq.symm ▸ g_low
  have h_cast_fun : (⇑g_low_cast : UpperHalfPlane → ℂ) = ⇑g_low :=
    cuspForm_cast_coe h_Mp_eq.symm g_low
  have h_slash_sum_lifted_qexp :=
    descent_slashSum_qExp_coeff_eq_Dp_g_low_coeff χ f hfχ p hp hpN χ' hχ_eq
      hl'_sqfree hpl' hl'_dvd hp_not_in h_vanish g_low g_low_cast
      h_cast_fun hg_low_qexp hg_low_full_qexp m hm_cop
  rw [show UpperHalfPlane.qExpansion (1 : ℝ)
      (descendSlashSumCuspForm χ f p hp hpN χ' hχ_eq hfχ_mod) =
      UpperHalfPlane.qExpansion (1 : ℝ) Ψ_fun from
    qExpansion_ext2 Φ_fun Ψ_fun hΦ_eq_Ψ,
    h_slash_sum_lifted_qexp, h_D_eq]

end HeckeRing.GL2

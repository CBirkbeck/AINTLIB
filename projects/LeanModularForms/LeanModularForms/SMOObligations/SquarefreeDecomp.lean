/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.SMOObligations.LevelCommute

/-!
# Strong Multiplicity One via Miyake §4.6 — squarefree decomposition (4.6.7)

The `m7_*` helpers, Miyake Lemma 4.6.7 (squarefree decomposition), the `V_p`
descent identity, and the per-`q` slash-sum machinery up to
`function_identity_Δ_eq_sum_V_q_F`. Part of a multi-file split of
`SMOObligations.lean`.
-/

open CongruenceSubgroup Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

private lemma m7_N_dvd_div_prime {N l q : ℕ} (hq_prime : q.Prime) (hq_dvd_l : q ∣ l) :
    N ∣ N * l ^ 2 / q := by
  obtain ⟨c, hc⟩ : q ∣ l ^ 2 := hq_dvd_l.trans (dvd_pow_self l two_ne_zero)
  refine ⟨c, ?_⟩
  rw [show N * l ^ 2 = N * (q * c) by rw [hc],
    show N * (q * c) = q * (N * c) by ring,
    Nat.mul_div_cancel_left _ hq_prime.pos]

private lemma m7_gHelper_char_restrict {N M₁ M₂ M : ℕ}
    [NeZero N] [NeZero M₁] [NeZero M₂] [NeZero M] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ) (hNM₁ : N ∣ M₁) (h_inner_dvd : M₁ ∣ M₂) (h_lvl_dvd : M₂ ∣ M)
    (hNM : N ∣ M)
    {g : CuspForm ((Gamma1 M₂).map (mapGL ℝ)) k}
    (hg : g ∈ cuspFormCharSpace k ((χ.comp (ZMod.unitsMap hNM₁)).comp
      (ZMod.unitsMap h_inner_dvd)))
    (h_le : (Gamma1 M).map (mapGL ℝ) ≤ (Gamma1 M₂).map (mapGL ℝ)) :
    CuspForm.restrictSubgroup h_le g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) := by
  have h_collapse :
      ((χ.comp (ZMod.unitsMap hNM₁)).comp (ZMod.unitsMap h_inner_dvd)).comp
        (ZMod.unitsMap h_lvl_dvd) = χ.comp (ZMod.unitsMap hNM) := by
    rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp,
      MonoidHom.comp_assoc, ZMod.unitsMap_comp]
  rw [← h_collapse]
  exact cuspForm_restrictSubgroup_mem_cuspFormCharSpace _ h_lvl_dvd hg

private lemma m7_chiFHelper_chain {N M₁ M₂ M N₂ : ℕ}
    [NeZero N] [NeZero M₁] [NeZero M₂] [NeZero N₂] [NeZero M]
    (χ : (ZMod N)ˣ →* ℂˣ) (hNM₁ : N ∣ M₁) (h_inner_dvd : M₁ ∣ M₂) (hNM : N ∣ M)
    (h_dvd_outer : M₂ ∣ M) {χ_F : (ZMod N₂)ˣ →* ℂˣ} (h_N₂_dvd_M₂ : N₂ ∣ M₂)
    (h_rel : χ_F.comp (ZMod.unitsMap h_N₂_dvd_M₂) =
      (χ.comp (ZMod.unitsMap hNM₁)).comp (ZMod.unitsMap h_inner_dvd)) :
    χ_F.comp (ZMod.unitsMap (h_N₂_dvd_M₂.trans h_dvd_outer)) =
      χ.comp (ZMod.unitsMap hNM) := by
  rw [← ZMod.unitsMap_comp h_N₂_dvd_M₂ h_dvd_outer, ← MonoidHom.comp_assoc, h_rel,
    MonoidHom.comp_assoc, ZMod.unitsMap_comp,
    MonoidHom.comp_assoc, ZMod.unitsMap_comp]

private lemma m7_q_dvd_Nl2 {N l q : ℕ} (hq : q ∈ l.primeFactors) :
    q ∣ N * l ^ 2 :=
  dvd_mul_of_dvd_right
    ((Nat.dvd_of_mem_primeFactors hq).trans (dvd_pow_self l two_ne_zero)) N

private lemma m7_divq_dvd_Nl2 {N l q : ℕ} (hq : q ∈ l.primeFactors) :
    (N * l ^ 2) / q ∣ N * l ^ 2 :=
  Nat.div_dvd_of_dvd (m7_q_dvd_Nl2 (N := N) hq)

private lemma m7_NeZero_Nl2_div_q {N l q : ℕ} [NeZero (N * l ^ 2)]
    (hq : q ∈ l.primeFactors) :
    NeZero ((N * l ^ 2) / q) :=
  ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne _))
    (m7_q_dvd_Nl2 (N := N) hq)) (Nat.prime_of_mem_primeFactors hq).pos).ne'⟩

private lemma m7_levelRaiseFun_zero (q : ℕ) [NeZero q] (k : ℤ) :
    (levelRaiseFun q k (0 : UpperHalfPlane → ℂ)) = 0 := by
  ext τ; simp [levelRaiseFun]

private lemma m7_qExp_coeff_levelRaise_case_A {M q : ℕ} [NeZero M] [NeZero q] {k : ℤ}
    {Γ : Subgroup (GL (Fin 2) ℝ)}
    (g : CuspForm Γ k) (F : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (h_eq : (⇑g : UpperHalfPlane → ℂ) =
      ⇑(HeckeRing.GL2.levelRaise M q k F)) (n : ℕ) :
    (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) ⇑g) =
      if q ∣ n then (PowerSeries.coeff (n / q))
        (UpperHalfPlane.qExpansion (1 : ℝ) ⇑F)
      else 0 := by
  rw [show (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) ⇑g) =
    (UpperHalfPlane.qExpansion (1 : ℝ)
      (HeckeRing.GL2.modularFormLevelRaise M q k F.toModularForm')).coeff n by
      rw [h_eq]; rfl,
    HeckeRing.GL2.qExpansion_one_modularFormLevelRaise_coeff]
  split_ifs with hqn <;> rfl

private lemma m7_qExp_coeff_of_fun_eq_zero {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    {g : CuspForm Γ k} (hg : (⇑g : UpperHalfPlane → ℂ) = 0) (n : ℕ) :
    (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) ⇑g) = 0 := by
  simp [hg, qExpansion_zero]

private lemma m7_qExp_zero_branch {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (q n : ℕ) :
    (if q ∣ n then
        (PowerSeries.coeff (n / q))
          (UpperHalfPlane.qExpansion (1 : ℝ) (⇑(0 : CuspForm Γ k)))
      else (0 : ℂ)) = 0 := by
  simp [qExpansion_zero]

private lemma m7_eq_q_of_mem_factors_one_eq_l {l l' q q' : ℕ} (hl'_eq1 : 1 = l')
    (h_pf_eq : l.primeFactors = insert q l'.primeFactors)
    (hq' : q' ∈ l.primeFactors) : q' = q := by
  simpa [h_pf_eq, ← hl'_eq1, Nat.primeFactors_one] using hq'

private lemma m7_mem_l'_of_ne_q {l l' q q' : ℕ}
    (h_pf_eq : l.primeFactors = insert q l'.primeFactors)
    (hq' : q' ∈ l.primeFactors) (hq'_ne : q' ≠ q) : q' ∈ l'.primeFactors :=
  (Finset.mem_insert.mp (h_pf_eq ▸ hq')).resolve_left hq'_ne


private lemma m7_qExp_split_f_eq_f'_plus_hform {ϕ_f ϕ_f' ϕ_h : PowerSeries ℂ} {q : ℕ}
    (hf'_qexp : ∀ n : ℕ,
      (PowerSeries.coeff n) ϕ_f' = if n.Coprime q then (PowerSeries.coeff n) ϕ_f else 0)
    (h_form_qexp : ∀ n : ℕ,
      (PowerSeries.coeff n) ϕ_h = if ¬ n.Coprime q then (PowerSeries.coeff n) ϕ_f else 0)
    (n : ℕ) :
    (PowerSeries.coeff n) ϕ_f =
      (PowerSeries.coeff n) ϕ_f' + (PowerSeries.coeff n) ϕ_h := by
  rw [hf'_qexp n, h_form_qexp n]
  by_cases hcop : n.Coprime q <;> simp [hcop]

/-- The conclusion of the strengthened squarefree decomposition (Miyake 4.6.7): cusp forms `g`
at level `Γ_1(N·l²)`, companions `F` at the lower levels `Γ_1((N·l²)/q)` with characters `χ_F`,
sharing functions with `g`, restricting to `χ` and assembling the `q`-expansion of `f`. Used as a
named target so the induction's leaf branches can be factored into helper lemmas. -/
private def Miyake467Decomp {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (l : ℕ)
    (hl : 1 < l) : Prop :=
  haveI hM_NeZero : NeZero (N * l ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 (by lia : l ≠ 0))⟩
  have hNM : N ∣ N * l ^ 2 := Nat.dvd_mul_right N (l ^ 2)
  ∃ (g : ℕ → CuspForm ((Gamma1 (N * l ^ 2)).map (mapGL ℝ)) k)
    (F : (q : ℕ) → (hq : q ∈ l.primeFactors) →
          haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq
          CuspForm ((Gamma1 ((N * l ^ 2) / q)).map (mapGL ℝ)) k)
    (χ_F : (q : ℕ) → (hq : q ∈ l.primeFactors) →
          haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq
          (ZMod ((N * l ^ 2) / q))ˣ →* ℂˣ),
    (∀ q ∈ l.primeFactors,
      g q ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM))) ∧
    (∀ q (hq : q ∈ l.primeFactors),
      haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq
      F q hq ∈ cuspFormCharSpace k (χ_F q hq)) ∧
    (∀ q (hq : q ∈ l.primeFactors),
      (⇑(F q hq) : UpperHalfPlane → ℂ) = ⇑(g q)) ∧
    (∀ q (hq : q ∈ l.primeFactors),
      haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq
      (χ_F q hq).comp (ZMod.unitsMap (m7_divq_dvd_Nl2 (N := N) hq)) =
        χ.comp (ZMod.unitsMap hNM)) ∧
    ∀ n : ℕ,
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n =
      ∑ q ∈ l.primeFactors,
        if q ∣ n then (UpperHalfPlane.qExpansion (1 : ℝ) (g q)).coeff (n / q)
        else 0

/-- If `b`'s `q`-expansion is supported away from `Coprime · q` (it equals `a`'s coefficients
exactly off the coprime indices), then `a - b` keeps precisely the coprime-to-`q` coefficients. -/
private lemma qExpansion_one_sub_coeff_coprime {M : ℕ} [NeZero M] {k : ℤ} {q : ℕ}
    (a b : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (h_period : (1 : ℝ) ∈ ((Gamma1 M).map (mapGL ℝ)).strictPeriods)
    (hb : ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℝ) ⇑b).coeff n =
      if ¬ n.Coprime q then (UpperHalfPlane.qExpansion (1 : ℝ) ⇑a).coeff n else 0)
    (n : ℕ) :
    (UpperHalfPlane.qExpansion (1 : ℝ) ⇑(a - b)).coeff n =
      if n.Coprime q then (UpperHalfPlane.qExpansion (1 : ℝ) ⇑a).coeff n else 0 := by
  have h_sub_qexp : UpperHalfPlane.qExpansion (1 : ℝ) (a - b) =
      UpperHalfPlane.qExpansion (1 : ℝ) a - UpperHalfPlane.qExpansion (1 : ℝ) b := by
    rw [sub_eq_add_neg, sub_eq_add_neg, ← ModularForm.qExpansion_neg one_pos h_period b]
    exact ModularForm.qExpansion_add (Γ := (Gamma1 M).map (mapGL ℝ))
      (h := (1 : ℝ)) (a := k) (b := k) one_pos h_period a (- b)
  show (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) (⇑(a - b))) = _
  rw [show UpperHalfPlane.qExpansion (1 : ℝ) (⇑(a - b)) =
      UpperHalfPlane.qExpansion (1 : ℝ) (a - b) from rfl, h_sub_qexp, map_sub, hb n]
  by_cases hcop : n.Coprime q <;> simp [hcop]

/-- Assembles `Miyake467Decomp` in the single-prime case `l = q` (so `l.primeFactors = {q}`) from
data for the prime `q` alone: a level-`N·l²` form `g_q`, a lower-level companion `F_q` sharing its
function, and a character `χ_q` restricting to `χ`, together with the one-prime `q`-expansion rule.
Both conductor-dichotomy branches of `Miyake467Decomp_of_prime` feed this. -/
private lemma Miyake467Decomp_single_prime_assemble {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (l q : ℕ) [NeZero (N * l ^ 2)] (hl : 1 < l)
    (hq_in : q ∈ l.primeFactors) (hl'_eq1 : 1 = l / q) (hNM' : N ∣ N * l ^ 2)
    (g_q : CuspForm ((Gamma1 (N * l ^ 2)).map (mapGL ℝ)) k)
    (F_q : haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq_in
      CuspForm ((Gamma1 ((N * l ^ 2) / q)).map (mapGL ℝ)) k)
    (χ_q : haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq_in
      (ZMod ((N * l ^ 2) / q))ˣ →* ℂˣ)
    (h_g_char : g_q ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM')))
    (h_F_char : haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq_in
      F_q ∈ cuspFormCharSpace k χ_q)
    (h_Fg : (⇑F_q : UpperHalfPlane → ℂ) = ⇑g_q)
    (h_χ : haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq_in
      χ_q.comp (ZMod.unitsMap (m7_divq_dvd_Nl2 (N := N) hq_in)) = χ.comp (ZMod.unitsMap hNM'))
    (h_qexp : ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n =
      if q ∣ n then (UpperHalfPlane.qExpansion (1 : ℝ) g_q).coeff (n / q) else 0) :
    Miyake467Decomp χ f l hl := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_in
  have hl_eq_q : l = q := by
    rw [← Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hq_in), ← hl'_eq1, mul_one]
  have h_pf_eq : l.primeFactors = insert q (l / q).primeFactors := by
    rw [← hl'_eq1, Nat.primeFactors_one, hl_eq_q, hq_prime.primeFactors]; rfl
  unfold Miyake467Decomp
  refine ⟨fun q' ↦ if q' = q then g_q else 0,
    fun q' hq' ↦ if hq'_eq : q' = q then hq'_eq ▸ F_q else 0,
    fun q' hq' ↦ if hq'_eq : q' = q then hq'_eq ▸ χ_q else 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro q' hq'
    obtain rfl := m7_eq_q_of_mem_factors_one_eq_l hl'_eq1 h_pf_eq hq'
    simpa using h_g_char
  · intro q' hq'
    obtain rfl := m7_eq_q_of_mem_factors_one_eq_l hl'_eq1 h_pf_eq hq'
    simpa using h_F_char
  · intro q' hq'
    obtain rfl := m7_eq_q_of_mem_factors_one_eq_l hl'_eq1 h_pf_eq hq'
    simp only [↓reduceDIte, ↓reduceIte]
    exact h_Fg
  · intro q' hq'
    obtain rfl := m7_eq_q_of_mem_factors_one_eq_l hl'_eq1 h_pf_eq hq'
    simp only [↓reduceDIte]
    exact h_χ
  · intro n
    rw [h_pf_eq, ← hl'_eq1, Nat.primeFactors_one]
    simp only [Finset.sum_insert, Finset.notMem_empty,
      not_false_eq_true, Finset.sum_empty, add_zero, if_true]
    exact h_qexp n

/-- Character chain identity used in both branches of `Miyake467Decomp_of_prime`: composing
the lowered character of `χ_M = ofUnitHom (χ ∘ ZMod.unitsMap hNM')` with the unit-group reduction
at level `N·l²/q` recovers the original lifted `χ ∘ ZMod.unitsMap hNM'`. -/
private lemma Miyake467Decomp_of_prime_lowered_char_chain {N : ℕ} [NeZero N]
    (χ : (ZMod N)ˣ →* ℂˣ) (l q : ℕ) [NeZero (N * l ^ 2)] [NeZero ((N * l ^ 2) / q)]
    (hNM' : N ∣ N * l ^ 2) (h_divq_dvd_M : (N * l ^ 2) / q ∣ N * l ^ 2)
    {χ_M : DirichletCharacter ℂ (N * l ^ 2)}
    (h_χ_M_toUnit : χ_M.toUnitHom = χ.comp (ZMod.unitsMap hNM'))
    (h_fac : χ_M.FactorsThrough ((N * l ^ 2) / q)) :
    (loweredCharacter h_fac).toUnitHom.comp (ZMod.unitsMap h_divq_dvd_M) =
      χ.comp (ZMod.unitsMap hNM') := by
  rw [← toUnitHom_loweredCharacter h_fac, h_χ_M_toUnit]

/-- Dichotomy left-branch (factorization) discharge for `Miyake467Decomp_of_prime`: from the
factored character data `(h_fac, F, hF_char, hF_eq)` produced by Case A of
`conductor_theorem_dichotomy_cuspForm_strong`, build the singleton `Miyake467Decomp`. -/
private lemma Miyake467Decomp_of_prime_left_branch {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (l q : ℕ) [NeZero q] (hl : 1 < l) (hq_in : q ∈ l.primeFactors)
    (hl'_eq1 : 1 = l / q) [NeZero (N * l ^ 2)] [NeZero ((N * l ^ 2) / q)]
    (hNM' : N ∣ N * l ^ 2) (h_divq_dvd_M : (N * l ^ 2) / q ∣ N * l ^ 2)
    (h_sub : (Gamma1 (N * l ^ 2)).map (mapGL ℝ) ≤ (Gamma1 N).map (mapGL ℝ))
    (h_sub_q : (Gamma1 (N * l ^ 2)).map (mapGL ℝ) ≤
      (Gamma1 ((N * l ^ 2) / q)).map (mapGL ℝ))
    {χ_M : DirichletCharacter ℂ (N * l ^ 2)}
    (h_χ_M_toUnit : χ_M.toUnitHom = χ.comp (ZMod.unitsMap hNM'))
    (φ : UpperHalfPlane → ℂ)
    (h_eq : (⇑(CuspForm.restrictSubgroup h_sub f) : UpperHalfPlane → ℂ) =
      levelRaiseFun q k φ)
    {h_fac : χ_M.FactorsThrough ((N * l ^ 2) / q)}
    {F : CuspForm ((Gamma1 ((N * l ^ 2) / q)).map (mapGL ℝ)) k}
    (hF_char : F ∈ cuspFormCharSpace k (loweredCharacter h_fac).toUnitHom)
    (hF_eq : (⇑F : UpperHalfPlane → ℂ) = φ) :
    Miyake467Decomp χ f l hl := by
  refine Miyake467Decomp_single_prime_assemble χ f l q hl
      hq_in hl'_eq1 hNM' (CuspForm.restrictSubgroup h_sub_q F) F
      (loweredCharacter h_fac).toUnitHom ?_ hF_char rfl ?_ ?_
  · rw [← Miyake467Decomp_of_prime_lowered_char_chain χ l q hNM' h_divq_dvd_M
      h_χ_M_toUnit h_fac]
    exact cuspForm_restrictSubgroup_mem_cuspFormCharSpace
      (loweredCharacter h_fac).toUnitHom h_divq_dvd_M hF_char
  · exact Miyake467Decomp_of_prime_lowered_char_chain χ l q hNM' h_divq_dvd_M
      h_χ_M_toUnit h_fac
  · intro n
    have h_fres_eq : (⇑(CuspForm.restrictSubgroup h_sub f) : UpperHalfPlane → ℂ) =
        ⇑(HeckeRing.GL2.levelRaise ((N * l ^ 2) / q) q k F) := by
      rw [h_eq, ← hF_eq]; rfl
    exact m7_qExp_coeff_levelRaise_case_A (CuspForm.restrictSubgroup h_sub f) F h_fres_eq n

/-- Dichotomy right-branch (vanishing) discharge for `Miyake467Decomp_of_prime`: from the
zero witness `hφ_zero` produced by Case B of `conductor_theorem_dichotomy_cuspForm_strong`,
build the singleton `Miyake467Decomp` using zero data. -/
private lemma Miyake467Decomp_of_prime_right_branch {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (l q : ℕ) [NeZero q] (hl : 1 < l) (hq_prime : q.Prime) (hq_dvd_l : q ∣ l)
    (hq_in : q ∈ l.primeFactors)
    (hl'_eq1 : 1 = l / q) [NeZero (N * l ^ 2)] [NeZero ((N * l ^ 2) / q)]
    (hNM' : N ∣ N * l ^ 2)
    (h_sub : (Gamma1 (N * l ^ 2)).map (mapGL ℝ) ≤ (Gamma1 N).map (mapGL ℝ))
    (hf_res_zero : (⇑(CuspForm.restrictSubgroup h_sub f) : UpperHalfPlane → ℂ) = 0) :
    Miyake467Decomp χ f l hl := by
  refine Miyake467Decomp_single_prime_assemble χ f l q hl
      hq_in hl'_eq1 hNM' 0 0 (χ.comp (ZMod.unitsMap (m7_N_dvd_div_prime hq_prime hq_dvd_l)))
      (Submodule.zero_mem _) (Submodule.zero_mem _) rfl ?_ ?_
  · rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
  · intro n
    have h_f_zero : (⇑f : UpperHalfPlane → ℂ) = 0 := hf_res_zero
    rw [m7_qExp_coeff_of_fun_eq_zero h_f_zero]
    exact (m7_qExp_zero_branch q n).symm

/-- Base case of Miyake 4.6.7 (`l` itself prime): peel the single prime `q = l` off `f` directly,
either via the conductor dichotomy's lowered form or (in the vanishing case) the zero form. -/
private lemma Miyake467Decomp_of_prime {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ) (l q : ℕ) (hq_prime : q.Prime) (hl_eq_q : l = q)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n l →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0) :
    Miyake467Decomp χ f l (hl_eq_q ▸ hq_prime.one_lt) := by
  haveI hq_ne : NeZero q := ⟨hq_prime.ne_zero⟩
  have hq_dvd_l : q ∣ l := hl_eq_q ▸ dvd_refl q
  have hl'_eq1 : 1 = l / q := by rw [hl_eq_q, Nat.div_self hq_prime.pos]
  haveI hNl2_ne : NeZero (N * l ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 (hl_eq_q ▸ hq_prime.ne_zero))⟩
  have hNM' : N ∣ N * l ^ 2 := Nat.dvd_mul_right N (l ^ 2)
  have hq_dvd_Nl2 : q ∣ N * l ^ 2 := by
    rw [hl_eq_q, sq]; exact dvd_mul_of_dvd_right (Nat.dvd_mul_left q q) N
  have h_Nl2_div_q : N * l ^ 2 / q = N * q := by
    rw [hl_eq_q, sq, ← mul_assoc, Nat.mul_div_cancel _ hq_prime.pos]
  haveI hNl2_div_q_ne : NeZero (N * l ^ 2 / q) := by
    rw [h_Nl2_div_q]
    exact ⟨Nat.mul_ne_zero (NeZero.ne N) hq_prime.ne_zero⟩
  let χ_M : DirichletCharacter ℂ (N * l ^ 2) :=
    MulChar.ofUnitHom (χ.comp (ZMod.unitsMap hNM'))
  have h_χ_M_toUnit : χ_M.toUnitHom = χ.comp (ZMod.unitsMap hNM') :=
    MulChar.equivToUnitHom.apply_symm_apply _
  have h_sub : (Gamma1 (N * l ^ 2)).map (mapGL ℝ) ≤ (Gamma1 N).map (mapGL ℝ) :=
    Gamma1_map_le_Gamma1_map_of_dvd hNM'
  let f_res : CuspForm ((Gamma1 (N * l ^ 2)).map (mapGL ℝ)) k :=
    CuspForm.restrictSubgroup h_sub f
  have hf_res_char : f_res ∈ cuspFormCharSpace k χ_M.toUnitHom := by
    rw [h_χ_M_toUnit]
    exact cuspForm_restrictSubgroup_mem_cuspFormCharSpace χ hNM' hfχ
  have hf_res_supp : f_res ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule
      (N * l ^ 2) k q := fun n hn ↦
    h_vanish n (hl_eq_q ▸ (hq_prime.coprime_iff_not_dvd.mpr hn).symm)
  have h_period_one : (1 : ℝ) ∈ ((Gamma1 (N * l ^ 2)).map (mapGL ℝ)).strictPeriods :=
    one_mem_strictPeriods_Gamma1_map _
  obtain ⟨φ, h_eq, h_period⟩ :=
    HeckeRing.GL2.exists_levelRaise_preimage_of_coeff_support_multiples
      hq_prime.one_lt hq_dvd_Nl2 f_res (fun n hn ↦ hf_res_supp n hn)
  have h_divq_dvd_M : (N * l ^ 2) / q ∣ N * l ^ 2 := by
    rw [h_Nl2_div_q, hl_eq_q, sq, ← mul_assoc]
    exact Nat.dvd_mul_right (N * q) q
  have h_sub_q : (Gamma1 (N * l ^ 2)).map (mapGL ℝ) ≤
      (Gamma1 ((N * l ^ 2) / q)).map (mapGL ℝ) :=
    Gamma1_map_le_Gamma1_map_of_dvd h_divq_dvd_M
  have hq_in : q ∈ l.primeFactors := by
    rw [hl_eq_q, hq_prime.primeFactors]; exact Finset.mem_singleton_self q
  rcases HeckeRing.GL2.conductor_theorem_dichotomy_cuspForm_strong
      q (N * l ^ 2) hq_dvd_Nl2 k χ_M φ f_res hf_res_char h_eq h_period with
    ⟨h_fac, F, hF_char, hF_eq⟩ | hφ_zero
  · exact Miyake467Decomp_of_prime_left_branch χ f l q (hl_eq_q ▸ hq_prime.one_lt) hq_in hl'_eq1
      hNM' h_divq_dvd_M h_sub h_sub_q (χ_M := χ_M) h_χ_M_toUnit φ h_eq hF_char hF_eq
  · have hf_res_zero : (⇑f_res : UpperHalfPlane → ℂ) = 0 := by
      rw [h_eq, hφ_zero]; exact m7_levelRaiseFun_zero q k
    exact Miyake467Decomp_of_prime_right_branch χ f l q (hl_eq_q ▸ hq_prime.one_lt) hq_prime
      hq_dvd_l hq_in hl'_eq1 hNM' h_sub hf_res_zero

/-- Assembles `Miyake467Decomp` for `l = q · l'` (`l' > 1`) from the induction hypothesis applied to
an auxiliary form `f'` at modulus `l'` (`h_IH`, whose families cover the primes of `l'`), the
splitting `f = V_q g_q + f'` of `q`-expansions (`h_f_split`), and the per-prime-`q` data
(`g_q`, `F_q`, `χ_q`). Both conductor-dichotomy branches of the inductive step feed this. -/
private lemma Miyake467Decomp_inductive_assemble {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (l q l' : ℕ) [NeZero (N * l ^ 2)] [NeZero (N * q ^ 2)] (hl : 1 < l) (hl'_gt1 : 1 < l')
    (hq_in : q ∈ l.primeFactors)
    (h_pf_eq : l.primeFactors = insert q l'.primeFactors) (hq_not_in_l' : q ∉ l'.primeFactors)
    (hNM' : N ∣ N * l ^ 2) (hNNq2 : N ∣ N * q ^ 2)
    (h_level_eq : N * q ^ 2 * l' ^ 2 = N * l ^ 2)
    (h_lvl_dvd : N * q ^ 2 * l' ^ 2 ∣ N * l ^ 2)
    (hNq2_dvd_Nl2 : N * q ^ 2 ∣ N * l ^ 2)
    (hNq_dvd_Nl2divq : N * q ^ 2 / q ∣ N * l ^ 2 / q)
    (f' : CuspForm ((Gamma1 (N * q ^ 2)).map (mapGL ℝ)) k)
    (h_IH : Miyake467Decomp (χ.comp (ZMod.unitsMap hNNq2)) f' l' hl'_gt1)
    (g_q : CuspForm ((Gamma1 (N * l ^ 2)).map (mapGL ℝ)) k)
    (F_q : haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq_in
      CuspForm ((Gamma1 ((N * l ^ 2) / q)).map (mapGL ℝ)) k)
    (χ_q : haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq_in
      (ZMod ((N * l ^ 2) / q))ˣ →* ℂˣ)
    (h_g_q_char : g_q ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM')))
    (h_F_q_char : haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq_in
      F_q ∈ cuspFormCharSpace k χ_q)
    (h_F_q_g_q : (⇑F_q : UpperHalfPlane → ℂ) = ⇑g_q)
    (h_χ_q : haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq_in
      χ_q.comp (ZMod.unitsMap (m7_divq_dvd_Nl2 (N := N) hq_in)) = χ.comp (ZMod.unitsMap hNM'))
    (h_f_split : ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n =
      (if q ∣ n then (UpperHalfPlane.qExpansion (1 : ℝ) g_q).coeff (n / q) else 0) +
        (UpperHalfPlane.qExpansion (1 : ℝ) f').coeff n) :
    Miyake467Decomp χ f l hl := by
  haveI hNq2l'2_ne : NeZero (N * q ^ 2 * l' ^ 2) := by rw [h_level_eq]; infer_instance
  obtain ⟨g_helper, F_helper, χ_F_helper, g_helper_char, F_helper_char,
      F_helper_eq, χ_F_helper_rel, g_helper_qexp⟩ := h_IH
  unfold Miyake467Decomp
  refine ⟨fun q' ↦ if q' = q then g_q else
    CuspForm.restrictSubgroup
      (le_of_eq_of_le (by rw [h_level_eq]) (le_refl _)) (g_helper q'),
    fun q' hq' ↦ if hq'_eq : q' = q then hq'_eq ▸ F_q
      else CuspForm.restrictSubgroup
        (show (Gamma1 ((N * l ^ 2) / q')).map (mapGL ℝ) ≤
            (Gamma1 ((N * q ^ 2 * l' ^ 2) / q')).map (mapGL ℝ) by rw [h_level_eq])
        (F_helper q' (m7_mem_l'_of_ne_q h_pf_eq hq' hq'_eq)),
    fun q' hq' ↦ if hq'_eq : q' = q then hq'_eq ▸ χ_q
      else (χ_F_helper q' (m7_mem_l'_of_ne_q h_pf_eq hq' hq'_eq)).comp
        (ZMod.unitsMap (show (N * q ^ 2 * l' ^ 2) / q' ∣ (N * l ^ 2) / q' by rw [h_level_eq])),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro q' hq'_in
    show (if q' = q then g_q else CuspForm.restrictSubgroup _ (g_helper q')) ∈ _
    split_ifs with hq'_eq
    · exact h_g_q_char
    · exact m7_gHelper_char_restrict χ hNNq2 (Nat.dvd_mul_right _ _) h_lvl_dvd hNM'
        (g_helper_char q' (m7_mem_l'_of_ne_q h_pf_eq hq'_in hq'_eq))
        (Gamma1_map_le_Gamma1_map_of_dvd h_lvl_dvd)
  · intro q' hq'_in
    by_cases hq'_eq : q' = q
    · subst hq'_eq; simpa using h_F_q_char
    · have hq'_in_l' : q' ∈ l'.primeFactors := m7_mem_l'_of_ne_q h_pf_eq hq'_in hq'_eq
      haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq'_in
      haveI : NeZero ((N * q ^ 2 * l' ^ 2) / q') := by rw [h_level_eq]; infer_instance
      simp only [dif_neg hq'_eq]
      exact cuspForm_restrictSubgroup_mem_cuspFormCharSpace
        (χ_F_helper q' hq'_in_l') (by rw [h_level_eq]) (F_helper_char q' hq'_in_l')
  · intro q' hq'_in
    by_cases hq'_eq : q' = q
    · subst hq'_eq; simp only [↓reduceDIte, ↓reduceIte]; exact h_F_q_g_q
    · simp only [dif_neg hq'_eq, if_neg hq'_eq]
      exact F_helper_eq q' (m7_mem_l'_of_ne_q h_pf_eq hq'_in hq'_eq)
  · intro q' hq'_in
    by_cases hq'_eq : q' = q
    · subst hq'_eq; simp only [↓reduceDIte]; exact h_χ_q
    · have hq'_in_l' : q' ∈ l'.primeFactors := m7_mem_l'_of_ne_q h_pf_eq hq'_in hq'_eq
      haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq'_in
      haveI : NeZero ((N * q ^ 2 * l' ^ 2) / q') := by rw [h_level_eq]; infer_instance
      dsimp only
      rw [dif_neg hq'_eq, MonoidHom.comp_assoc, ZMod.unitsMap_comp]
      convert m7_chiFHelper_chain χ hNNq2 (Nat.dvd_mul_right _ _) hNM' h_lvl_dvd
        (Nat.div_dvd_of_dvd (by rw [h_level_eq]; exact m7_q_dvd_Nl2 (N := N) hq'_in))
        (χ_F_helper_rel q' hq'_in_l') using 2
  · intro n
    rw [h_pf_eq, Finset.sum_insert hq_not_in_l', h_f_split n, g_helper_qexp n]
    simp only [↓reduceIte]
    congr 1
    apply Finset.sum_congr rfl
    intro q' hq'_in_l'
    have hq'_ne_q : q' ≠ q := fun h ↦ hq_not_in_l' (h ▸ hq'_in_l')
    rw [if_neg hq'_ne_q]
    rfl

/-- Prime-factor structure for the Miyake 4.6.7 induction step at `l` squarefree with
`l.primeFactors.card = n+1`: pick a prime `q ∣ l` and decompose `l = q · l'`, package
the squarefreeness of `l'`, the `primeFactors` insertion `{q} ∪ l'.pf = l.pf`, the
`q ∉ l'.primeFactors` (from squarefreeness), and the inductive step's card reduction
`l'.pf.card = n`. -/
private lemma Miyake467Decomp_inductive_step_factor_structure
    (l q : ℕ) (hl_sqfree : Squarefree l) (hq_in : q ∈ l.primeFactors) {n : ℕ}
    (hl_card : l.primeFactors.card = n + 1) :
    let l' := l / q
    Squarefree l' ∧ q * l' = l ∧ 0 < l' ∧
    l.primeFactors = insert q l'.primeFactors ∧
    q ∉ l'.primeFactors ∧ l'.primeFactors.card = n := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_in
  have hq_dvd_l : q ∣ l := Nat.dvd_of_mem_primeFactors hq_in
  set l' := l / q
  have hq_dvd_l' : q * l' = l := Nat.mul_div_cancel' hq_dvd_l
  have hl_ne : l ≠ 0 := hl_sqfree.ne_zero
  have hl'_pos : 0 < l' :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hl_ne) hq_dvd_l) hq_prime.pos
  have hl'_sqfree : Squarefree l' :=
    hl_sqfree.squarefree_of_dvd (Nat.div_dvd_of_dvd hq_dvd_l)
  have h_pf_eq : l.primeFactors = insert q l'.primeFactors := by
    rw [← hq_dvd_l', Nat.primeFactors_mul hq_prime.ne_zero hl'_pos.ne',
        hq_prime.primeFactors, Finset.singleton_union]
  have hq_not_in_l' : q ∉ l'.primeFactors := fun hq_in_l' ↦
    (Nat.squarefree_iff_prime_squarefree.mp hl_sqfree q hq_prime)
      (hq_dvd_l' ▸ Nat.mul_dvd_mul_left q (Nat.dvd_of_mem_primeFactors hq_in_l'))
  have hl'_pf_card : l'.primeFactors.card = n := by
    have := hl_card
    rw [h_pf_eq, Finset.card_insert_of_notMem hq_not_in_l'] at this
    lia
  exact ⟨hl'_sqfree, hq_dvd_l', hl'_pos, h_pf_eq, hq_not_in_l', hl'_pf_card⟩

/-- Bundle of level relations needed by the Miyake 4.6.7 induction step: for `l = q · l'`,
the level shifts among `N·l²`, `N·q²`, `N·q²·l'²`, and `(N·l²)/q` and the corresponding
subgroup inclusions on `Γ_1`. Returned as a single `∃`-tuple to slim the inductive-step body. -/
private lemma Miyake467Decomp_inductive_step_level_relations {N : ℕ} [NeZero N]
    (l q l' : ℕ) [NeZero (N * l ^ 2)] [NeZero (N * q ^ 2)] [NeZero ((N * q ^ 2) / q)]
    (hq_prime : q.Prime) (hl_eq_ql' : l = q * l') (hl'_pos : 0 < l') :
    NeZero ((N * q ^ 2) * l' ^ 2) ∧
    ((N * q ^ 2) * l' ^ 2 = N * l ^ 2) ∧
    ((N * q ^ 2) * l' ^ 2 ∣ N * l ^ 2) ∧
    (N * q ^ 2 / q ∣ N * q ^ 2) ∧
    ((Gamma1 (N * q ^ 2)).map (mapGL ℝ) ≤ (Gamma1 ((N * q ^ 2) / q)).map (mapGL ℝ)) ∧
    (N * q ^ 2 ∣ N * l ^ 2) ∧
    ((Gamma1 (N * l ^ 2)).map (mapGL ℝ) ≤ (Gamma1 (N * q ^ 2)).map (mapGL ℝ)) ∧
    (N * q ^ 2 / q ∣ N * l ^ 2 / q) ∧
    ((Gamma1 ((N * l ^ 2) / q)).map (mapGL ℝ) ≤ (Gamma1 (N * q ^ 2 / q)).map (mapGL ℝ)) := by
  have hNq2l'2_ne : NeZero ((N * q ^ 2) * l' ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne _) (pow_ne_zero 2 hl'_pos.ne')⟩
  have h_level_eq : (N * q ^ 2) * l' ^ 2 = N * l ^ 2 := by
    rw [hl_eq_ql', mul_pow]; ring
  have h_lvl_dvd : (N * q ^ 2) * l' ^ 2 ∣ N * l ^ 2 := by rw [h_level_eq]
  have h_Nq2_div_q : N * q ^ 2 / q = N * q := by
    rw [sq, ← mul_assoc, Nat.mul_div_cancel _ hq_prime.pos]
  have h_divq_dvd_Nq2 : (N * q ^ 2) / q ∣ N * q ^ 2 := by
    rw [h_Nq2_div_q, sq, ← mul_assoc]
    exact Nat.dvd_mul_right (N * q) q
  have hNq2_dvd_Nl2 : N * q ^ 2 ∣ N * l ^ 2 := by
    rw [hl_eq_ql', mul_pow]; exact ⟨l' ^ 2, by ring⟩
  have h_Nl2_div_q_eq : (N * l ^ 2) / q = (N * q ^ 2 / q) * l' ^ 2 := by
    rw [h_Nq2_div_q, hl_eq_ql', mul_pow,
      show N * (q ^ 2 * l' ^ 2) = (N * q * l' ^ 2) * q by ring,
      Nat.mul_div_cancel _ hq_prime.pos]
  have hNq_dvd_Nl2divq : (N * q ^ 2 / q) ∣ (N * l ^ 2) / q := by
    rw [h_Nl2_div_q_eq]; exact Nat.dvd_mul_right _ _
  exact ⟨hNq2l'2_ne, h_level_eq, h_lvl_dvd,
    h_divq_dvd_Nq2, Gamma1_map_le_Gamma1_map_of_dvd h_divq_dvd_Nq2,
    hNq2_dvd_Nl2, Gamma1_map_le_Gamma1_map_of_dvd hNq2_dvd_Nl2,
    hNq_dvd_Nl2divq, Gamma1_map_le_Gamma1_map_of_dvd hNq_dvd_Nl2divq⟩

/-- `(N · q^2) / q = N · q`, hence `NeZero` whenever `N` and `q` are nonzero. Used to populate
the level-`(N·q²)/q` typeclass at the conductor-theorem application in the inductive step. -/
private lemma m7_NeZero_Nq2_div_q {N q : ℕ} [NeZero N] (hq_prime : q.Prime) :
    NeZero ((N * q ^ 2) / q) := by
  rw [show N * q ^ 2 / q = N * q from by
    rw [sq, ← mul_assoc, Nat.mul_div_cancel _ hq_prime.pos]]
  exact ⟨Nat.mul_ne_zero (NeZero.ne N) hq_prime.ne_zero⟩

/-- `q ∣ N · q^2`. -/
private lemma m7_q_dvd_Nq2 (N q : ℕ) : q ∣ N * q ^ 2 := by
  rw [sq, ← mul_assoc]; exact Nat.dvd_mul_left q (N * q)

/-- Constructs the level-`N·q²` auxiliary form `f'` for the Miyake 4.6.7 induction step,
returning `f' = restrictSubgroup f - h_form` together with its character membership,
`q`-coprime `q`-expansion identity, and `l'`-coprime vanishing. Used in the inductive step
to feed the IH at modulus `l'`. -/
private lemma Miyake467Decomp_inductive_auxiliary_form {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ) (l q l' : ℕ) [NeZero (N * q ^ 2)]
    (hq_dvd_l' : q * l' = l) (hNNq2 : N ∣ N * q ^ 2)
    (h_form : CuspForm ((Gamma1 (N * q ^ 2)).map (mapGL ℝ)) k)
    (h_form_char : h_form ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNNq2)))
    (h_form_qexp : ∀ n : ℕ,
      (UpperHalfPlane.qExpansion (1 : ℝ) h_form).coeff n =
      if ¬ n.Coprime q then (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n else 0)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n l →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0) :
    ∃ f' : CuspForm ((Gamma1 (N * q ^ 2)).map (mapGL ℝ)) k,
      f' ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNNq2)) ∧
      (∀ n : ℕ, (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) ⇑f') =
        if n.Coprime q then (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) ⇑f)
        else 0) ∧
      (∀ n : ℕ, n.Coprime l' →
        (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) ⇑f') = 0) := by
  have h_sub_Nq2 : (Gamma1 (N * q ^ 2)).map (mapGL ℝ) ≤ (Gamma1 N).map (mapGL ℝ) :=
    Gamma1_map_le_Gamma1_map_of_dvd hNNq2
  let f_at_Nq2 : CuspForm ((Gamma1 (N * q ^ 2)).map (mapGL ℝ)) k :=
    CuspForm.restrictSubgroup h_sub_Nq2 f
  have hf_at_Nq2_char : f_at_Nq2 ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNNq2)) :=
    cuspForm_restrictSubgroup_mem_cuspFormCharSpace χ hNNq2 hfχ
  refine ⟨f_at_Nq2 - h_form, Submodule.sub_mem _ hf_at_Nq2_char h_form_char,
    qExpansion_one_sub_coeff_coprime f_at_Nq2 h_form
      (one_mem_strictPeriods_Gamma1_map _) h_form_qexp, ?_⟩
  intro n hn_cop_l'
  rw [qExpansion_one_sub_coeff_coprime f_at_Nq2 h_form
    (one_mem_strictPeriods_Gamma1_map _) h_form_qexp n]
  split_ifs with hcop_q
  · exact h_vanish n (hq_dvd_l' ▸ Nat.Coprime.mul_right hcop_q hn_cop_l')
  · rfl

/-- Inductive-step dichotomy left-branch (Case A) discharge: from the conductor-theorem
factorization data `(h_fac, F, hF_char, hF_eq)` for `h_form` at level `N·q²`, build the
`Miyake467Decomp` at level `N·l²` via `Miyake467Decomp_inductive_assemble`. -/
private lemma Miyake467Decomp_inductive_step_left_branch {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (l q l' : ℕ) [NeZero (N * l ^ 2)] [NeZero (N * q ^ 2)] [NeZero q]
    [NeZero ((N * q ^ 2) / q)] [NeZero ((N * l ^ 2) / q)]
    (hl_gt : 1 < l) (hl'_gt1 : 1 < l') (hq_in : q ∈ l.primeFactors)
    (h_pf_eq : l.primeFactors = insert q l'.primeFactors)
    (hq_not_in_l' : q ∉ l'.primeFactors)
    (hNM' : N ∣ N * l ^ 2) (hNNq2 : N ∣ N * q ^ 2)
    (h_level_eq : N * q ^ 2 * l' ^ 2 = N * l ^ 2)
    (h_lvl_dvd : N * q ^ 2 * l' ^ 2 ∣ N * l ^ 2)
    (hNq2_dvd_Nl2 : N * q ^ 2 ∣ N * l ^ 2)
    (hNq_dvd_Nl2divq : N * q ^ 2 / q ∣ N * l ^ 2 / q)
    (h_divq_dvd_Nq2 : (N * q ^ 2) / q ∣ N * q ^ 2)
    (h_sub_q : (Gamma1 (N * q ^ 2)).map (mapGL ℝ) ≤
      (Gamma1 ((N * q ^ 2) / q)).map (mapGL ℝ))
    (h_sub_Nl2_Nq2 : (Gamma1 (N * l ^ 2)).map (mapGL ℝ) ≤
      (Gamma1 (N * q ^ 2)).map (mapGL ℝ))
    (h_sub_lift_q : (Gamma1 ((N * l ^ 2) / q)).map (mapGL ℝ) ≤
      (Gamma1 (N * q ^ 2 / q)).map (mapGL ℝ))
    (h_form : CuspForm ((Gamma1 (N * q ^ 2)).map (mapGL ℝ)) k)
    (h_form_qexp : ∀ n : ℕ,
      (UpperHalfPlane.qExpansion (1 : ℝ) h_form).coeff n =
      if ¬ n.Coprime q then (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n else 0)
    (f' : CuspForm ((Gamma1 (N * q ^ 2)).map (mapGL ℝ)) k)
    (h_IH : Miyake467Decomp (χ.comp (ZMod.unitsMap hNNq2)) f' l' hl'_gt1)
    (hf'_qexp : ∀ n : ℕ,
      (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) ⇑f') =
      if n.Coprime q then
        (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) ⇑f)
      else 0)
    {χ_M : DirichletCharacter ℂ (N * q ^ 2)}
    (h_χ_M_toUnit : χ_M.toUnitHom = χ.comp (ZMod.unitsMap hNNq2))
    (φ : UpperHalfPlane → ℂ)
    (hφ_eq : (⇑h_form : UpperHalfPlane → ℂ) = levelRaiseFun q k φ)
    {h_fac : χ_M.FactorsThrough ((N * q ^ 2) / q)}
    {F : CuspForm ((Gamma1 ((N * q ^ 2) / q)).map (mapGL ℝ)) k}
    (hF_char : F ∈ cuspFormCharSpace k (loweredCharacter h_fac).toUnitHom)
    (hF_eq : (⇑F : UpperHalfPlane → ℂ) = φ) :
    Miyake467Decomp χ f l hl_gt := by
  have h_hform_eq : (⇑h_form : UpperHalfPlane → ℂ) =
      ⇑(HeckeRing.GL2.levelRaise ((N * q ^ 2) / q) q k F) := by
    rw [hφ_eq, ← hF_eq]; rfl
  have h_char_eq : (loweredCharacter h_fac).toUnitHom.comp
      (ZMod.unitsMap h_divq_dvd_Nq2) = χ.comp (ZMod.unitsMap hNNq2) := by
    rw [← toUnitHom_loweredCharacter h_fac, h_χ_M_toUnit]
  have hF_at_Nq2_char :
      CuspForm.restrictSubgroup h_sub_q F ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNNq2)) :=
    h_char_eq ▸ cuspForm_restrictSubgroup_mem_cuspFormCharSpace
      (loweredCharacter h_fac).toUnitHom h_divq_dvd_Nq2 hF_char
  have h_chainNl2 : (χ.comp (ZMod.unitsMap hNNq2)).comp
      (ZMod.unitsMap hNq2_dvd_Nl2) = χ.comp (ZMod.unitsMap hNM') := by
    rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
  refine Miyake467Decomp_inductive_assemble χ f l q l' hl_gt hl'_gt1 hq_in h_pf_eq
    hq_not_in_l' hNM' hNNq2 h_level_eq h_lvl_dvd hNq2_dvd_Nl2 hNq_dvd_Nl2divq f' h_IH
    (CuspForm.restrictSubgroup h_sub_Nl2_Nq2 (CuspForm.restrictSubgroup h_sub_q F))
    (CuspForm.restrictSubgroup h_sub_lift_q F)
    ((loweredCharacter h_fac).toUnitHom.comp (ZMod.unitsMap hNq_dvd_Nl2divq))
    (h_chainNl2 ▸ cuspForm_restrictSubgroup_mem_cuspFormCharSpace
      (χ.comp (ZMod.unitsMap hNNq2)) hNq2_dvd_Nl2 hF_at_Nq2_char)
    (cuspForm_restrictSubgroup_mem_cuspFormCharSpace
      (loweredCharacter h_fac).toUnitHom hNq_dvd_Nl2divq hF_char) rfl ?_ ?_
  · rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp,
      ← ZMod.unitsMap_comp h_divq_dvd_Nq2 hNq2_dvd_Nl2, ← MonoidHom.comp_assoc,
      ← toUnitHom_loweredCharacter h_fac, h_χ_M_toUnit, MonoidHom.comp_assoc, ZMod.unitsMap_comp]
  · intro n
    rw [m7_qExp_split_f_eq_f'_plus_hform hf'_qexp h_form_qexp n,
      m7_qExp_coeff_levelRaise_case_A h_form F h_hform_eq n, add_comm]
    rfl

/-- Inductive-step dichotomy right-branch (Case B) discharge: from the vanishing witness
`hφ_zero` for `h_form`'s level-raise preimage, build the `Miyake467Decomp` at level
`N·l²` using zero data for the per-prime-`q` slot. -/
private lemma Miyake467Decomp_inductive_step_right_branch {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (l q l' : ℕ) [NeZero (N * l ^ 2)] [NeZero (N * q ^ 2)] [NeZero q]
    (hl_gt : 1 < l) (hl'_gt1 : 1 < l') (hq_prime : q.Prime) (hq_dvd_l : q ∣ l)
    (hq_in : q ∈ l.primeFactors)
    (h_pf_eq : l.primeFactors = insert q l'.primeFactors)
    (hq_not_in_l' : q ∉ l'.primeFactors)
    (hNM' : N ∣ N * l ^ 2) (hNNq2 : N ∣ N * q ^ 2)
    (h_level_eq : N * q ^ 2 * l' ^ 2 = N * l ^ 2)
    (h_lvl_dvd : N * q ^ 2 * l' ^ 2 ∣ N * l ^ 2)
    (hNq2_dvd_Nl2 : N * q ^ 2 ∣ N * l ^ 2)
    (hNq_dvd_Nl2divq : N * q ^ 2 / q ∣ N * l ^ 2 / q)
    (h_form : CuspForm ((Gamma1 (N * q ^ 2)).map (mapGL ℝ)) k)
    (h_form_qexp : ∀ n : ℕ,
      (UpperHalfPlane.qExpansion (1 : ℝ) h_form).coeff n =
      if ¬ n.Coprime q then (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n else 0)
    (f' : CuspForm ((Gamma1 (N * q ^ 2)).map (mapGL ℝ)) k)
    (h_IH : Miyake467Decomp (χ.comp (ZMod.unitsMap hNNq2)) f' l' hl'_gt1)
    (hf'_qexp : ∀ n : ℕ,
      (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) ⇑f') =
      if n.Coprime q then
        (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) ⇑f)
      else 0)
    (hh_form_zero : (⇑h_form : UpperHalfPlane → ℂ) = 0) :
    Miyake467Decomp χ f l hl_gt := by
  have h_an_f'_eq_f : ∀ n,
      (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) ⇑f') =
      (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) ⇑f) := fun n ↦ by
    rw [m7_qExp_split_f_eq_f'_plus_hform hf'_qexp h_form_qexp n,
      m7_qExp_coeff_of_fun_eq_zero hh_form_zero n, add_zero]
  have hN_dvd_divq_indB : N ∣ (N * l ^ 2) / q := m7_N_dvd_div_prime hq_prime hq_dvd_l
  haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq_in
  refine Miyake467Decomp_inductive_assemble χ f l q l' hl_gt hl'_gt1 hq_in h_pf_eq
    hq_not_in_l' hNM' hNNq2 h_level_eq h_lvl_dvd hNq2_dvd_Nl2 hNq_dvd_Nl2divq f' h_IH
    0 0 (χ.comp (ZMod.unitsMap hN_dvd_divq_indB))
    (Submodule.zero_mem _) (Submodule.zero_mem _) rfl ?_ ?_
  · rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
  · intro n
    rw [m7_qExp_zero_branch q n, zero_add, h_an_f'_eq_f n]

/-- Dispatches the Miyake 4.6.7 inductive step into the left or right branch using the
conductor-theorem dichotomy on the `q`-supported piece `h_form` at level `N·q²`. -/
private lemma Miyake467Decomp_inductive_step_dispatch {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (l q l' : ℕ) [NeZero (N * l ^ 2)] [NeZero (N * q ^ 2)] [NeZero q]
    [NeZero ((N * q ^ 2) / q)] [NeZero ((N * l ^ 2) / q)]
    (hl_gt : 1 < l) (hl'_gt1 : 1 < l') (hq_prime : q.Prime) (hq_dvd_l : q ∣ l)
    (hq_in : q ∈ l.primeFactors)
    (h_pf_eq : l.primeFactors = insert q l'.primeFactors)
    (hq_not_in_l' : q ∉ l'.primeFactors)
    (hNM' : N ∣ N * l ^ 2) (hNNq2 : N ∣ N * q ^ 2)
    (h_level_eq : N * q ^ 2 * l' ^ 2 = N * l ^ 2)
    (h_lvl_dvd : N * q ^ 2 * l' ^ 2 ∣ N * l ^ 2)
    (hNq2_dvd_Nl2 : N * q ^ 2 ∣ N * l ^ 2)
    (hNq_dvd_Nl2divq : N * q ^ 2 / q ∣ N * l ^ 2 / q)
    (h_divq_dvd_Nq2 : (N * q ^ 2) / q ∣ N * q ^ 2)
    (h_sub_q : (Gamma1 (N * q ^ 2)).map (mapGL ℝ) ≤
      (Gamma1 ((N * q ^ 2) / q)).map (mapGL ℝ))
    (h_sub_Nl2_Nq2 : (Gamma1 (N * l ^ 2)).map (mapGL ℝ) ≤
      (Gamma1 (N * q ^ 2)).map (mapGL ℝ))
    (h_sub_lift_q : (Gamma1 ((N * l ^ 2) / q)).map (mapGL ℝ) ≤
      (Gamma1 (N * q ^ 2 / q)).map (mapGL ℝ))
    (h_form : CuspForm ((Gamma1 (N * q ^ 2)).map (mapGL ℝ)) k)
    (h_form_char : h_form ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNNq2)))
    (h_form_qexp : ∀ n : ℕ,
      (UpperHalfPlane.qExpansion (1 : ℝ) h_form).coeff n =
      if ¬ n.Coprime q then (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n else 0)
    (f' : CuspForm ((Gamma1 (N * q ^ 2)).map (mapGL ℝ)) k)
    (h_IH : Miyake467Decomp (χ.comp (ZMod.unitsMap hNNq2)) f' l' hl'_gt1)
    (hf'_qexp : ∀ n : ℕ,
      (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) ⇑f') =
      if n.Coprime q then
        (PowerSeries.coeff n) (UpperHalfPlane.qExpansion (1 : ℝ) ⇑f)
      else 0) :
    Miyake467Decomp χ f l hl_gt := by
  let χ_M : DirichletCharacter ℂ (N * q ^ 2) :=
    MulChar.ofUnitHom (χ.comp (ZMod.unitsMap hNNq2))
  have h_χ_M_toUnit : χ_M.toUnitHom = χ.comp (ZMod.unitsMap hNNq2) :=
    MulChar.equivToUnitHom.apply_symm_apply _
  obtain ⟨φ, hφ_eq, hφ_period⟩ :=
    HeckeRing.GL2.exists_levelRaise_preimage_of_coeff_support_multiples
      hq_prime.one_lt (m7_q_dvd_Nq2 N q) h_form fun n hn_not_dvd ↦ by
        rw [h_form_qexp n, if_neg (not_not_intro
          (hq_prime.coprime_iff_not_dvd.mpr hn_not_dvd).symm)]
  rcases HeckeRing.GL2.conductor_theorem_dichotomy_cuspForm_strong
      q (N * q ^ 2) (m7_q_dvd_Nq2 N q) k χ_M φ h_form (h_χ_M_toUnit ▸ h_form_char)
      hφ_eq hφ_period with
    ⟨h_fac, F, hF_char, hF_eq⟩ | hφ_zero
  · exact Miyake467Decomp_inductive_step_left_branch χ f l q l' hl_gt hl'_gt1 hq_in h_pf_eq
      hq_not_in_l' hNM' hNNq2 h_level_eq h_lvl_dvd hNq2_dvd_Nl2 hNq_dvd_Nl2divq
      h_divq_dvd_Nq2 h_sub_q h_sub_Nl2_Nq2 h_sub_lift_q h_form h_form_qexp f' h_IH hf'_qexp
      (χ_M := χ_M) h_χ_M_toUnit φ hφ_eq hF_char hF_eq
  · have hh_form_zero : (⇑h_form : UpperHalfPlane → ℂ) = 0 := by
      rw [hφ_eq, hφ_zero]; exact m7_levelRaiseFun_zero q k
    exact Miyake467Decomp_inductive_step_right_branch χ f l q l' hl_gt hl'_gt1 hq_prime
      hq_dvd_l hq_in h_pf_eq hq_not_in_l' hNM' hNNq2 h_level_eq h_lvl_dvd hNq2_dvd_Nl2
      hNq_dvd_Nl2divq h_form h_form_qexp f' h_IH hf'_qexp hh_form_zero

/-- Inductive step of Miyake 4.6.7 (`l = q · l'` with `l' > 1`): split off the prime `q` via the
auxiliary `h_form` and `f' = f - h_form`, apply the induction hypothesis `ih` to `f'` at level
`N·q²` and modulus `l'`, then reassemble the per-prime data at level `N·l²` via the
`_dispatch` helper. -/
private lemma Miyake467Decomp_inductive_step {N : ℕ} [NeZero N] {k : ℤ} (n : ℕ)
    (ih : ∀ (l : ℕ), l.primeFactors.card = n →
      ∀ (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
        (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k), f ∈ cuspFormCharSpace k χ →
        ∀ (hl : 1 < l), Squarefree l →
          (∀ n : ℕ, Nat.Coprime n l →
            (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0) →
          Miyake467Decomp χ f l hl)
    (χ : (ZMod N)ˣ →* ℂˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (l : ℕ) (hl_card : l.primeFactors.card = n + 1) (hl_sqfree : Squarefree l) (hl_gt : 1 < l)
    (q : ℕ) (hq_in : q ∈ l.primeFactors) (hl'_gt1 : 1 < l / q)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n l →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0) :
    Miyake467Decomp χ f l hl_gt := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_in
  have hq_dvd_l : q ∣ l := Nat.dvd_of_mem_primeFactors hq_in
  haveI hq_ne : NeZero q := ⟨hq_prime.ne_zero⟩
  set l' := l / q with hl'_def
  obtain ⟨hl'_sqfree, hq_dvd_l', hl'_pos, h_pf_eq, hq_not_in_l', hl'_pf_card⟩ :=
    Miyake467Decomp_inductive_step_factor_structure l q hl_sqfree hq_in hl_card
  haveI hNl2_ne : NeZero (N * l ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 (by lia : l ≠ 0))⟩
  have hNM' : N ∣ N * l ^ 2 := Nat.dvd_mul_right N (l ^ 2)
  have hl_eq_ql' : l = q * l' := hq_dvd_l'.symm
  haveI hNq2_ne : NeZero (N * q ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 hq_prime.ne_zero)⟩
  have hNNq2 : N ∣ N * q ^ 2 := Nat.dvd_mul_right N _
  obtain ⟨h_form, h_form_char, h_form_qexp⟩ :=
    miyake_h_form_general (N := N) (k := k) χ f hfχ q hq_prime.pos hq_prime.squarefree
  obtain ⟨f', hf'_char, hf'_qexp, hf'_vanish⟩ :=
    Miyake467Decomp_inductive_auxiliary_form χ f hfχ l q l' hq_dvd_l' hNNq2
      h_form h_form_char h_form_qexp h_vanish
  have h_IH : Miyake467Decomp (χ.comp (ZMod.unitsMap hNNq2)) f' l' hl'_gt1 :=
    ih l' hl'_pf_card (N * q ^ 2) k (χ.comp (ZMod.unitsMap hNNq2))
      f' hf'_char hl'_gt1 hl'_sqfree hf'_vanish
  haveI hNq2_div_q_ne : NeZero (N * q ^ 2 / q) := m7_NeZero_Nq2_div_q (N := N) hq_prime
  haveI hNl2_div_q_ne : NeZero ((N * l ^ 2) / q) :=
    m7_NeZero_Nl2_div_q (N := N) (l := l) hq_in
  obtain ⟨hNq2l'2_ne, h_level_eq, h_lvl_dvd, h_divq_dvd_Nq2, h_sub_q,
      hNq2_dvd_Nl2, h_sub_Nl2_Nq2, hNq_dvd_Nl2divq, h_sub_lift_q⟩ :=
    Miyake467Decomp_inductive_step_level_relations (N := N) l q l' hq_prime hl_eq_ql' hl'_pos
  haveI : NeZero ((N * q ^ 2) * l' ^ 2) := hNq2l'2_ne
  exact Miyake467Decomp_inductive_step_dispatch χ f l q l' hl_gt hl'_gt1 hq_prime
    hq_dvd_l hq_in h_pf_eq hq_not_in_l' hNM' hNNq2 h_level_eq h_lvl_dvd hNq2_dvd_Nl2
    hNq_dvd_Nl2divq h_divq_dvd_Nq2 h_sub_q h_sub_Nl2_Nq2 h_sub_lift_q h_form
    h_form_char h_form_qexp f' h_IH hf'_qexp

/-- **Strengthened M7-sqfree** (Miyake p. 159-160) — same as
`miyake_4_6_7_squarefree_decomp` but ALSO exposes, for each prime `q ∣ l`, a
companion `F q` at the natural lower level `Γ_1((N·l²)/q)` whose underlying
function on `ℍ` agrees with `⇑(g q)`.  This is the level where the V_q
preimage of `g q` naturally lives (Miyake's `g_p ∈ G_k(N·l/p, χ)` when `p ∣ l`).

The g and F outputs share the same underlying function — F is g viewed at the
lower level (one factor of q peeled off), and g is F restricted/lifted along
the inclusion `Γ_1(N·l²) ≤ Γ_1((N·l²)/q)`.  Concretely the relationship is
`⇑(F q hq) = ⇑(g q)` (definitionally, after restrictSubgroup).

Helper consumers that need to invoke M6(2) (smaller level (l·N)/q) on the
V_q-preimage of each `g q` should use F here rather than g, then the inclusion
witness comes for free. -/
theorem miyake_4_6_7_squarefree_decomp_with_lower_level
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (l : ℕ) (hl_gt : 1 < l) (hl_sqfree : Squarefree l)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n l →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0) :
    haveI hM_NeZero : NeZero (N * l ^ 2) :=
      ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 (by lia : l ≠ 0))⟩
    have hNM : N ∣ N * l ^ 2 := Nat.dvd_mul_right N (l ^ 2)
    ∃ (g : ℕ → CuspForm ((Gamma1 (N * l ^ 2)).map (mapGL ℝ)) k)
      (F : (q : ℕ) → (hq : q ∈ l.primeFactors) →
            haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq
            CuspForm ((Gamma1 ((N * l ^ 2) / q)).map (mapGL ℝ)) k)
      (χ_F : (q : ℕ) → (hq : q ∈ l.primeFactors) →
            haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq
            (ZMod ((N * l ^ 2) / q))ˣ →* ℂˣ),
      (∀ q ∈ l.primeFactors,
        g q ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM))) ∧
      (∀ q (hq : q ∈ l.primeFactors),
        haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq
        F q hq ∈ cuspFormCharSpace k (χ_F q hq)) ∧
      (∀ q (hq : q ∈ l.primeFactors),
        (⇑(F q hq) : UpperHalfPlane → ℂ) = ⇑(g q)) ∧
      (∀ q (hq : q ∈ l.primeFactors),
        haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq
        (χ_F q hq).comp (ZMod.unitsMap (m7_divq_dvd_Nl2 (N := N) hq)) =
          χ.comp (ZMod.unitsMap hNM)) ∧
      ∀ n : ℕ,
        (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n =
        ∑ q ∈ l.primeFactors,
          if q ∣ n then (UpperHalfPlane.qExpansion (1 : ℝ) (g q)).coeff (n / q)
          else 0 := by
  suffices key : ∀ (m : ℕ) (l : ℕ) (_ : l.primeFactors.card = m)
      (N : ℕ) [NeZero N] (k : ℤ)
      (χ : (ZMod N)ˣ →* ℂˣ)
      (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
      (_ : f ∈ cuspFormCharSpace k χ)
      (hl : 1 < l) (_ : Squarefree l)
      (_ : ∀ n : ℕ, Nat.Coprime n l → (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0),
      Miyake467Decomp χ f l hl by
    exact key l.primeFactors.card l rfl N k χ f hfχ hl_gt hl_sqfree h_vanish
  intro m
  induction m with
  | zero =>
    intro l hl_card _ _ _ _ _ _ hl_gt _ _
    have h_empty : l.primeFactors = ∅ := Finset.card_eq_zero.mp hl_card
    rw [Nat.primeFactors_eq_empty] at h_empty
    rcases h_empty with rfl | rfl <;> lia
  | succ n ih =>
    intro l hl_card N _ k χ f hfχ hl_gt hl_sqfree h_vanish
    obtain ⟨q, hq_in⟩ : l.primeFactors.Nonempty :=
      Finset.card_pos.mp (hl_card ▸ Nat.succ_pos n)
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_in
    have hq_dvd_l : q ∣ l := Nat.dvd_of_mem_primeFactors hq_in
    have hq_dvd_l' : q * (l / q) = l := Nat.mul_div_cancel' hq_dvd_l
    have hl'_pos : 0 < l / q := Nat.div_pos (Nat.le_of_dvd (by lia) hq_dvd_l) hq_prime.pos
    rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hl'_pos)) with
      hl'_eq1 | hl'_gt1
    · have hl_eq_q : l = q := by rw [← hq_dvd_l', ← hl'_eq1, mul_one]
      exact Miyake467Decomp_of_prime χ f hfχ l q hq_prime hl_eq_q h_vanish
    · exact Miyake467Decomp_inductive_step n ih χ f hfχ l hl_card hl_sqfree hl_gt q hq_in
        hl'_gt1 h_vanish

private lemma qExpansion_one_coe_zero_coeff (f : UpperHalfPlane → ℂ) (hf : f = 0) (n : ℕ) :
    (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0 := by
  subst hf; simp [qExpansion_zero]

private lemma qExpansion_one_cuspForm_cast_coeff {A B : ℕ} {k : ℤ} (h : A = B)
    (x : CuspForm ((Gamma1 A).map (mapGL ℝ)) k) (n : ℕ) :
    (UpperHalfPlane.qExpansion (1 : ℝ)
        ⇑(h ▸ x : CuspForm ((Gamma1 B).map (mapGL ℝ)) k)).coeff n =
      (UpperHalfPlane.qExpansion (1 : ℝ) ⇑x).coeff n := by
  cases h; rfl

private lemma cuspFormCharSpace_mem_cast {A B : ℕ} [NeZero A] [NeZero B] {k : ℤ}
    (h : A = B) (χ₀ : (ZMod A)ˣ →* ℂˣ) (x : CuspForm ((Gamma1 A).map (mapGL ℝ)) k)
    (hx : x ∈ cuspFormCharSpace k χ₀) :
    (h ▸ x : CuspForm ((Gamma1 B).map (mapGL ℝ)) k) ∈
      cuspFormCharSpace k (h ▸ χ₀ : (ZMod B)ˣ →* ℂˣ) := by
  cases h; exact hx

private lemma qExpansion_one_levelRaise_coeff {M : ℕ} [NeZero M] {k : ℤ} (p : ℕ) [NeZero p]
    (g_p : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) (n : ℕ) :
    (UpperHalfPlane.qExpansion (1 : ℝ)
        ⇑(HeckeRing.GL2.levelRaise M p k g_p)).coeff n =
      if p ∣ n then (UpperHalfPlane.qExpansion (1 : ℝ) ⇑g_p).coeff (n / p) else 0 :=
  HeckeRing.GL2.qExpansion_one_modularFormLevelRaise_coeff g_p.toModularForm' n

/-- The degenerate `V_p`-descent: if `f` has vanishing `q`-coefficients at every index coprime to
`l'`, the zero form at the lower level (with trivial character) witnesses the descent identity. -/
private lemma miyake_V_p_descend_with_char_of_vanishing
    {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (p l' : ℕ) [NeZero (l' * (N / p))]
    (hpl' : Nat.Coprime p l')
    (hf_zero_cop : ∀ n : ℕ, Nat.Coprime n l' →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0) :
    ∃ (χ_low : (ZMod (l' * (N / p)))ˣ →* ℂˣ)
      (g_low : CuspForm ((Gamma1 (l' * (N / p))).map (mapGL ℝ)) k),
      g_low ∈ cuspFormCharSpace k χ_low ∧
      (∀ n : ℕ, p ∣ n → Nat.Coprime n l' →
        (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n =
        (UpperHalfPlane.qExpansion (1 : ℝ) g_low).coeff (n / p)) ∧
      (∀ m : ℕ,
        (UpperHalfPlane.qExpansion (1 : ℝ) g_low).coeff m =
        if Nat.Coprime m l' then
          (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff (p * m)
        else 0) := by
  have h_zero_low : (⇑(0 : CuspForm ((Gamma1 (l' * (N / p))).map (mapGL ℝ)) k) :
      UpperHalfPlane → ℂ) = 0 := rfl
  refine ⟨1, 0, Submodule.zero_mem _, ?_, ?_⟩
  · intro n _ hn_cop_l'
    rw [qExpansion_one_coe_zero_coeff _ h_zero_low (n / p), hf_zero_cop n hn_cop_l']
  · intro m
    rw [qExpansion_one_coe_zero_coeff _ h_zero_low m]
    split_ifs with hcop
    · exact (hf_zero_cop (p * m) (Nat.coprime_mul_iff_left.mpr ⟨hpl', hcop⟩)).symm
    · rfl

/-- **M-V_p-descend-strong: strengthened V_p descent identity with character info.**

Like `miyake_V_p_descend_identity`, but additionally exposes a character `χ_low`
on `(ZMod (l' * (N/p)))ˣ` with `g_low ∈ cuspFormCharSpace k χ_low`, derived from
M4-strong's lowered character `(loweredCharacter h_fac).toUnitHom` at level
`(l'·N)/p` and transported across `(l'·N)/p = l' · (N/p)`. -/
theorem miyake_V_p_descend_identity_with_char
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (l' : ℕ) (hl'_pos : 0 < l') (hl'_sqfree : Squarefree l')
    (hpl' : Nat.Coprime p l')
    (hl'_dvd : ∀ q ∈ l'.primeFactors, q ∈ N.primeFactors)
    (_hp_not_in : p ∉ l'.primeFactors)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p * l') →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0) :
    haveI : NeZero (l' * (N / p)) := ⟨Nat.mul_ne_zero
      (Nat.pos_iff_ne_zero.mp hl'_pos) (NeZero.ne _)⟩
    ∃ (χ_low : (ZMod (l' * (N / p)))ˣ →* ℂˣ)
      (g_low : CuspForm ((Gamma1 (l' * (N / p))).map (mapGL ℝ)) k),
      g_low ∈ cuspFormCharSpace k χ_low ∧
      (∀ n : ℕ, p ∣ n → Nat.Coprime n l' →
        (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n =
        (UpperHalfPlane.qExpansion (1 : ℝ) g_low).coeff (n / p)) ∧
      (∀ m : ℕ,
        (UpperHalfPlane.qExpansion (1 : ℝ) g_low).coeff m =
        if Nat.Coprime m l' then
          (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff (p * m)
        else 0) := by
  haveI : NeZero l' := ⟨hl'_pos.ne'⟩
  obtain ⟨g, hg_char, hg_supp, hg_qexp⟩ :=
    miyake_g_p_supported χ f hfχ p hp l' hl'_pos hl'_sqfree hl'_dvd h_vanish
  have hpM : p ∣ l' * N := dvd_mul_of_dvd_right hpN l'
  have h_Mp_eq : (l' * N) / p = l' * (N / p) := Nat.mul_div_assoc l' hpN
  haveI : NeZero ((l' * N) / p) := h_Mp_eq ▸ inferInstance
  let χ_M_homU : (ZMod (l' * N))ˣ →* ℂˣ := χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N l'))
  let χ_M : DirichletCharacter ℂ (l' * N) := MulChar.ofUnitHom χ_M_homU
  have hg_χM : g ∈ cuspFormCharSpace k χ_M.toUnitHom := by
    rw [show χ_M.toUnitHom = χ_M_homU from MulChar.equivToUnitHom.apply_symm_apply _]
    exact hg_char
  have h_cop_iff : ∀ m : ℕ, Nat.Coprime (p * m) l' ↔ Nat.Coprime m l' := fun m ↦
    ⟨fun h ↦ (Nat.coprime_mul_iff_left.mp h).2,
      fun h ↦ Nat.coprime_mul_iff_left.mpr ⟨hpl', h⟩⟩
  rcases miyake_4_6_4_dichotomy_strong χ_M p hp hpM g hg_χM hg_supp with
    hg_zero | ⟨h_fac, g_p, hg_p_char, hg_p_eq⟩
  · have h_g_zero : (⇑g : UpperHalfPlane → ℂ) = 0 := by rw [hg_zero]; rfl
    refine miyake_V_p_descend_with_char_of_vanishing f p l' hpl' (fun n hn_cop_l' ↦ ?_)
    have := hg_qexp n
    rwa [if_pos hn_cop_l', qExpansion_one_coe_zero_coeff _ h_g_zero n, eq_comm] at this
  · have h_qExp_Vp_eq_g :
        UpperHalfPlane.qExpansion (1 : ℝ)
          ⇑(HeckeRing.GL2.levelRaise ((l' * N) / p) p k g_p) =
        UpperHalfPlane.qExpansion (1 : ℝ) ⇑g :=
      qExpansion_ext2 _ _ hg_p_eq
    refine ⟨h_Mp_eq ▸ (HeckeRing.GL2.loweredCharacter h_fac).toUnitHom, h_Mp_eq ▸ g_p,
      cuspFormCharSpace_mem_cast h_Mp_eq _ g_p hg_p_char, ?_, ?_⟩
    · intro n hpn hn_cop_l'
      have h_an_g_eq_f : (UpperHalfPlane.qExpansion (1 : ℝ) ⇑g).coeff n =
          (UpperHalfPlane.qExpansion (1 : ℝ) ⇑f).coeff n := by
        have := hg_qexp n
        rwa [if_pos hn_cop_l'] at this
      rw [qExpansion_one_cuspForm_cast_coeff h_Mp_eq g_p (n / p), ← h_an_g_eq_f,
        ← h_qExp_Vp_eq_g, qExpansion_one_levelRaise_coeff p g_p n, if_pos hpn]
    · intro m
      have h_g_p_eq : (UpperHalfPlane.qExpansion (1 : ℝ) ⇑g_p).coeff m =
          (UpperHalfPlane.qExpansion (1 : ℝ) ⇑g).coeff (p * m) := by
        rw [← h_qExp_Vp_eq_g, qExpansion_one_levelRaise_coeff p g_p (p * m),
          if_pos (dvd_mul_right p m), Nat.mul_div_cancel_left m hp.pos]
      rw [qExpansion_one_cuspForm_cast_coeff h_Mp_eq g_p m, h_g_p_eq, hg_qexp (p * m)]
      simp only [h_cop_iff]

lemma modularForm_fun_eq_of_qExp_eq_at_period_one
    {M : ℕ} [NeZero M] {k : ℤ}
    (h_period : (1 : ℝ) ∈ ((Gamma1 M).map (mapGL ℝ)).strictPeriods)
    (f g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (h_qExp_eq : ∀ n : ℕ,
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n =
        (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n) :
    (⇑f : UpperHalfPlane → ℂ) = ⇑g := by
  have h_diff_qExp_zero : UpperHalfPlane.qExpansion (1 : ℝ) (f - g) = 0 := by
    rw [ModularForm.qExpansion_sub one_pos h_period f g]
    ext n
    simp [map_sub, h_qExp_eq n]
  have h_diff_zero : f - g = 0 :=
    (ModularForm.qExpansion_eq_zero_iff one_pos h_period (f := f - g)).mp h_diff_qExp_zero
  funext z
  exact sub_eq_zero.mp (DFunLike.congr_fun h_diff_zero z)

lemma miyake_descent_l_prime_eq_one_helper
    {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {p : ℕ} [NeZero p]
    {M : ℕ} [NeZero M]
    (g_low_cast : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hp_M_eq_N : p * M = N)
    (h_Fourier_eq : ∀ n : ℕ,
      (UpperHalfPlane.qExpansion (1 : ℝ) ⇑f).coeff n =
      (UpperHalfPlane.qExpansion (1 : ℝ)
        ⇑(HeckeRing.GL2.modularFormLevelRaise M p k g_low_cast.toModularForm')).coeff n) :
    (⇑f.toModularForm' : UpperHalfPlane → ℂ) =
    ⇑(HeckeRing.GL2.modularFormLevelRaise M p k g_low_cast.toModularForm') := by
  have hN_dvd_pM : N ∣ p * M := hp_M_eq_N ▸ dvd_refl _
  have h1_period_pM : (1 : ℝ) ∈ ((Gamma1 (p * M)).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 (p * M)).map (mapGL ℝ) =
        (Gamma1 (p * M) : Subgroup (GL (Fin 2) ℝ)) from rfl,
      strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  haveI : NeZero (p * M) := hp_M_eq_N ▸ inferInstance
  exact modularForm_fun_eq_of_qExp_eq_at_period_one (M := p * M)
    (k := k) h1_period_pM
    (ModularForm.restrictSubgroup
      (HeckeRing.GL2.MainLemma.Gamma1_mapGL_le_of_dvd hN_dvd_pM)
      f.toModularForm')
    (HeckeRing.GL2.modularFormLevelRaise M p k g_low_cast.toModularForm')
    h_Fourier_eq

private lemma qExp_z_to_qz_zero_of_not_dvd
    {L : ℕ} [NeZero L] {k : ℤ}
    (q : ℕ) [NeZero q]
    (G : ModularForm ((Gamma1 L).map (mapGL ℝ)) k)
    (m : ℕ) (hq_not_m : ¬ q ∣ m) :
    (UpperHalfPlane.qExpansion (1 : ℝ)
      (fun z : UpperHalfPlane ↦
        (⇑(HeckeRing.GL2.modularFormLevelRaise L q k G) :
          UpperHalfPlane → ℂ) z)).coeff m = 0 := by
  simp only [HeckeRing.GL2.qExpansion_one_modularFormLevelRaise_coeff G m, if_neg hq_not_m]

/-- The pointwise sum over the descent-coset list of slash-actions of a modular form is
holomorphic: rewrite it as a `Finset` sum of slashed forms and apply `MDifferentiable.sum`. -/
private lemma mdifferentiable_descendCosetList_slash_sum {M : ℕ} [NeZero M]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (G : ModularForm Γ k) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun z : UpperHalfPlane ↦
        ∑ v : Fin (descendCosetCount p M), ((⇑G : UpperHalfPlane → ℂ) ∣[k]
          descendCosetList p M hp v) z) := by
  rw [show (fun z : UpperHalfPlane ↦
        ∑ v : Fin (descendCosetCount p M), ((⇑G : UpperHalfPlane → ℂ) ∣[k]
          descendCosetList p M hp v) z) =
      ∑ v : Fin (descendCosetCount p M), ((⇑G : UpperHalfPlane → ℂ) ∣[k]
        descendCosetList p M hp v) from funext fun z ↦ (Finset.sum_apply _ _ _).symm]
  exact MDifferentiable.sum (fun v _ ↦ (ModularFormClass.holo G).slash k _)

/-- The weight-`k` cusp form on `Γ₁((q·M_q)/p)` obtained from a cusp form `F_q` on `Γ₁(M_q)`
(in the `χ_F`-eigenspace) by the `V_q` level-raise to `Γ₁(q·M_q)` followed by the slash-sum
descent by the prime `p`. -/
noncomputable def slash_sum_V_q_cuspForm_descend
    {M_q : ℕ} [NeZero M_q] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpM_q : p ∣ M_q) [NeZero (M_q / p)]
    (q : ℕ) [NeZero q]
    (χ_F : (ZMod M_q)ˣ →* ℂˣ)
    (χ_F_low : (ZMod (M_q / p))ˣ →* ℂˣ)
    (h_χ_F_factor : χ_F = χ_F_low.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM_q)))
    (F_q : CuspForm ((Gamma1 M_q).map (mapGL ℝ)) k)
    (hF_q_char : F_q ∈ cuspFormCharSpace k χ_F) :
    haveI : NeZero (q * M_q) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne M_q)⟩
    have h_qMp_dvd : p ∣ q * M_q := dvd_mul_of_dvd_right hpM_q q
    haveI : NeZero ((q * M_q) / p) := ⟨Nat.ne_of_gt (Nat.div_pos
        (Nat.le_of_dvd (Nat.mul_pos (NeZero.pos q) (NeZero.pos M_q)) h_qMp_dvd) hp.pos)⟩
    CuspForm ((Gamma1 ((q * M_q) / p)).map (mapGL ℝ)) k :=
  have : NeZero (q * M_q) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne M_q)⟩
  have h_qMp_dvd : p ∣ q * M_q := dvd_mul_of_dvd_right hpM_q q
  have : NeZero ((q * M_q) / p) := ⟨Nat.ne_of_gt (Nat.div_pos
      (Nat.le_of_dvd (Nat.mul_pos (NeZero.pos q) (NeZero.pos M_q)) h_qMp_dvd) hp.pos)⟩
  let V_q_F_q : CuspForm ((Gamma1 (q * M_q)).map (mapGL ℝ)) k :=
    HeckeRing.GL2.levelRaise M_q q k F_q
  have hV_q_F_q_char : V_q_F_q ∈ cuspFormCharSpace k
      (χ_F.comp (ZMod.unitsMap (Nat.dvd_mul_left M_q q))) :=
    cuspForm_levelRaise_mem_cuspFormCharSpace M_q q k χ_F hF_q_char
  have hV_q_F_q_mod : V_q_F_q.toModularForm' ∈ modFormCharSpace k
      (χ_F.comp (ZMod.unitsMap (Nat.dvd_mul_left M_q q))) :=
    (cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
      (k := k) _ V_q_F_q).mpr hV_q_F_q_char
  have h_Mq_div_p_dvd_qMq_div_p : M_q / p ∣ (q * M_q) / p := by
    obtain ⟨a, rfl⟩ := hpM_q
    simp [Nat.mul_div_cancel_left _ hp.pos, mul_comm q, mul_assoc]
  let χ_F_low_lifted : (ZMod ((q * M_q) / p))ˣ →* ℂˣ :=
    χ_F_low.comp (ZMod.unitsMap h_Mq_div_p_dvd_qMq_div_p)
  have h_χ_F_lifted_factor :
      χ_F.comp (ZMod.unitsMap (Nat.dvd_mul_left M_q q)) =
      χ_F_low_lifted.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd h_qMp_dvd)) := by
    change χ_F.comp (ZMod.unitsMap (Nat.dvd_mul_left M_q q)) =
      (χ_F_low.comp (ZMod.unitsMap h_Mq_div_p_dvd_qMq_div_p)).comp
        (ZMod.unitsMap (Nat.div_dvd_of_dvd h_qMp_dvd))
    rw [h_χ_F_factor, MonoidHom.comp_assoc _ _ χ_F_low, ZMod.unitsMap_comp,
        MonoidHom.comp_assoc _ _ χ_F_low, ZMod.unitsMap_comp]
  { toFun := fun z ↦ ∑ v : Fin (descendCosetCount p (q * M_q)),
      ((⇑V_q_F_q.toModularForm' : UpperHalfPlane → ℂ) ∣[k]
        descendCosetList p (q * M_q) hp v) z
    slash_action_eq' := fun γ hγ ↦ by
      obtain ⟨γ', h_γ'_Gamma1, rfl⟩ := Subgroup.mem_map.mp hγ
      exact miyake_hecke_descend_Gamma1_inv p hp h_qMp_dvd
        (χ_F.comp (ZMod.unitsMap (Nat.dvd_mul_left M_q q)))
        χ_F_low_lifted h_χ_F_lifted_factor
        hV_q_F_q_mod γ' h_γ'_Gamma1
    holo' := by
      change MDifferentiable _ _ (fun z : UpperHalfPlane ↦
        ∑ v : Fin (descendCosetCount p (q * M_q)),
          ((⇑V_q_F_q.toModularForm' : UpperHalfPlane → ℂ) ∣[k]
            descendCosetList p (q * M_q) hp v) z)
      exact mdifferentiable_descendCosetList_slash_sum p hp V_q_F_q.toModularForm'
    zero_at_cusps' := fun {cusp} hc ↦ miyake_hecke_descend_cusp p hp h_qMp_dvd V_q_F_q hc }

lemma per_q_slash_sum_at_deep_qexp_zero
    {M_q : ℕ} [NeZero M_q] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpM_q : p ∣ M_q) [NeZero (M_q / p)]
    (q : ℕ) [NeZero q] (hpq : Nat.Coprime p q) (hq_dvd_Mq_div_p : q ∣ M_q / p)
    (χ_F : (ZMod M_q)ˣ →* ℂˣ)
    (χ_F_low : (ZMod (M_q / p))ˣ →* ℂˣ)
    (h_χ_F_factor : χ_F = χ_F_low.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM_q)))
    (F_q : CuspForm ((Gamma1 M_q).map (mapGL ℝ)) k)
    (hF_q_char : F_q ∈ cuspFormCharSpace k χ_F)
    (m : ℕ) (hq_not_m : ¬ q ∣ m) :
    haveI : NeZero (q * M_q) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne M_q)⟩
    (UpperHalfPlane.qExpansion (1 : ℝ)
      (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p (q * M_q)),
        ((⇑(HeckeRing.GL2.modularFormLevelRaise M_q q k F_q.toModularForm') :
          UpperHalfPlane → ℂ) ∣[k]
          descendCosetList p (q * M_q) hp v) z)).coeff m = 0 := by
  haveI : NeZero (q * M_q) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne M_q)⟩
  have hF_q_mod : F_q.toModularForm' ∈ modFormCharSpace k χ_F :=
    (cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
      (k := k) χ_F F_q).mpr hF_q_char
  have h_M6_2 := miyake_4_6_6_level_commute_delta (N := M_q) (l := q) (k := k)
    p hp hpM_q hpq hq_dvd_Mq_div_p χ_F χ_F_low h_χ_F_factor
    F_q.toModularForm' hF_q_mod
  let G_q : CuspForm ((Gamma1 (M_q / p)).map (mapGL ℝ)) k :=
    { toFun := fun z ↦ ∑ v : Fin (descendCosetCount p M_q),
        ((⇑F_q.toModularForm' : UpperHalfPlane → ℂ) ∣[k]
          descendCosetList p M_q hp v) z
      slash_action_eq' := fun γ hγ ↦ by
        obtain ⟨γ', h_γ'_Gamma1, rfl⟩ := Subgroup.mem_map.mp hγ
        exact miyake_hecke_descend_Gamma1_inv p hp hpM_q χ_F χ_F_low h_χ_F_factor
          hF_q_mod γ' h_γ'_Gamma1
      holo' := by
        change MDifferentiable _ _ (fun z : UpperHalfPlane ↦
          ∑ v : Fin (descendCosetCount p M_q),
            ((⇑F_q.toModularForm' : UpperHalfPlane → ℂ) ∣[k]
              descendCosetList p M_q hp v) z)
        exact mdifferentiable_descendCosetList_slash_sum p hp F_q.toModularForm'
      zero_at_cusps' := fun {cusp} hc ↦ miyake_hecke_descend_cusp p hp hpM_q F_q hc }
  have h_fun_eq_V_q_G : (fun z : UpperHalfPlane ↦
      ∑ v : Fin (descendCosetCount p M_q),
        ((⇑F_q.toModularForm' : UpperHalfPlane → ℂ) ∣[k]
          descendCosetList p M_q hp v) (HeckeRing.GL2.levelRaiseMatrix q • z)) =
      (fun z : UpperHalfPlane ↦
        (⇑(HeckeRing.GL2.modularFormLevelRaise (M_q / p) q k G_q.toModularForm') :
          UpperHalfPlane → ℂ) z) := by
    funext z
    rw [HeckeRing.GL2.modularFormLevelRaise_apply]
    rfl
  have h_slash_sum_eq : (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p (q * M_q)),
      ((⇑(HeckeRing.GL2.modularFormLevelRaise M_q q k F_q.toModularForm') :
        UpperHalfPlane → ℂ) ∣[k]
        descendCosetList p (q * M_q) hp v) z) =
    (fun z : UpperHalfPlane ↦
      (⇑(HeckeRing.GL2.modularFormLevelRaise (M_q / p) q k G_q.toModularForm') :
        UpperHalfPlane → ℂ) z) := by
    funext z
    rw [h_M6_2 z]
    exact congr_fun h_fun_eq_V_q_G z
  rw [h_slash_sum_eq]
  exact qExp_z_to_qz_zero_of_not_dvd q G_q.toModularForm' m hq_not_m

lemma slash_sum_at_M_eq_of_function_eq
    (p M : ℕ) [NeZero p] [NeZero M] (hp : p.Prime)
    (k : ℤ) (f g : UpperHalfPlane → ℂ) (hfg : f = g) :
    (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p M),
      (f ∣[k] descendCosetList p M hp v) z) =
    (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p M),
      (g ∣[k] descendCosetList p M hp v) z) :=
  hfg ▸ rfl

lemma slash_sum_linear_over_Finset_sum
    {α : Type*}
    (p M : ℕ) [NeZero p] [NeZero M] (hp : p.Prime) (k : ℤ)
    (s : Finset α) (h : α → UpperHalfPlane → ℂ) :
    (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p M),
      ((fun w : UpperHalfPlane ↦ ∑ a ∈ s, h a w) ∣[k]
        descendCosetList p M hp v) z) =
    (fun z : UpperHalfPlane ↦ ∑ a ∈ s,
      ∑ v : Fin (descendCosetCount p M),
        (h a ∣[k] descendCosetList p M hp v) z) := by
  funext z
  have h_pi_sum : (fun w : UpperHalfPlane ↦ ∑ a ∈ s, h a w) =
      (∑ a ∈ s, h a : UpperHalfPlane → ℂ) := by
    funext w; rw [Finset.sum_apply]
  rw [h_pi_sum]
  have h_inner : ∀ v : Fin (descendCosetCount p M),
      ((∑ a ∈ s, h a : UpperHalfPlane → ℂ) ∣[k] descendCosetList p M hp v) z =
      ∑ a ∈ s, (h a ∣[k] descendCosetList p M hp v) z := by
    intro v
    rw [SlashAction.sum_slash, Finset.sum_apply]
  simp_rw [h_inner]
  rw [Finset.sum_comm]

/-- Evaluating a level-cast modular form agrees with evaluating the original. -/
private lemma modularForm_cast_level_apply {A B : ℕ} [NeZero A] [NeZero B] {k : ℤ}
    (h : A = B) (f₀ : ModularForm ((Gamma1 A).map (mapGL ℝ)) k) (z₀ : UpperHalfPlane) :
    ((h ▸ f₀ : ModularForm ((Gamma1 B).map (mapGL ℝ)) k) : UpperHalfPlane → ℂ) z₀ =
      (f₀ : UpperHalfPlane → ℂ) z₀ := by subst h; rfl

/-- The `q`-expansion of a level-cast modular form agrees with that of the original. -/
private lemma qExpansion_one_modularForm_cast_level {A B : ℕ} [NeZero A] [NeZero B] {k : ℤ}
    (h : A = B) (f₀ : ModularForm ((Gamma1 A).map (mapGL ℝ)) k) :
    UpperHalfPlane.qExpansion (1 : ℝ)
        (h ▸ f₀ : ModularForm ((Gamma1 B).map (mapGL ℝ)) k) =
      UpperHalfPlane.qExpansion (1 : ℝ) f₀ := by subst h; rfl

/-- The coercion of a `Finset` sum of modular forms, evaluated at a point, equals the sum of
the pointwise evaluations. -/
private lemma coe_finset_sum_modularForm_apply {ι : Type*} [DecidableEq ι]
    {M : ℕ} [NeZero M] {k : ℤ}
    (s : Finset ι) (F : ι → ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (z : UpperHalfPlane) :
    ((∑ q ∈ s, F q : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) : UpperHalfPlane → ℂ) z =
      ∑ q ∈ s, (⇑(F q) : UpperHalfPlane → ℂ) z := by
  refine Finset.induction_on s (by simp) fun q s hqs ih ↦ ?_
  rw [Finset.sum_insert hqs, Finset.sum_insert hqs, ModularForm.coe_add, Pi.add_apply, ih]

/-- A modular form whose `q`-expansion coefficients are, term by term, the sum of the
`q`-expansion coefficients of a finite family equals (as a function on `ℍ`) the pointwise sum
of that family. -/
private lemma modularForm_eq_sum_of_qExpansion_coeff_eq {M : ℕ} [NeZero M] {k : ℤ}
    {ι : Type*} [DecidableEq ι]
    (h_period : (1 : ℝ) ∈ ((Gamma1 M).map (mapGL ℝ)).strictPeriods)
    (G : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (s : Finset ι) (φ : ι → ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (h_coeff : ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℝ) G).coeff n =
      ∑ q ∈ s, (UpperHalfPlane.qExpansion (1 : ℝ) (φ q)).coeff n) :
    (⇑G : UpperHalfPlane → ℂ) =
      fun z ↦ ∑ q ∈ s, (⇑(φ q) : UpperHalfPlane → ℂ) z := by
  set RHS_sum : ModularForm ((Gamma1 M).map (mapGL ℝ)) k := ∑ q ∈ s, φ q with hRHS
  have h_eq : (⇑G : UpperHalfPlane → ℂ) = ⇑RHS_sum := by
    apply modularForm_fun_eq_of_qExp_eq_at_period_one h_period
    intro n
    rw [h_coeff n,
      show UpperHalfPlane.qExpansion (1 : ℝ) RHS_sum =
          ∑ q ∈ s, UpperHalfPlane.qExpansion (1 : ℝ) (φ q) from
        map_sum (ModularForm.qExpansionAddHom (Γ := (Gamma1 M).map (mapGL ℝ))
          (h := (1 : ℝ)) one_pos h_period k) φ s,
      map_sum (PowerSeries.coeff (R := ℂ) n) _ s]
  rw [h_eq]
  funext z
  exact coe_finset_sum_modularForm_apply s φ z

/-- The `q`-expansion coefficient of a level-cast `V_q`-raise of a cusp form `G` agrees, via the
`V_q` Fourier rule, with the corresponding coefficient of any form `g` sharing `G`'s function. -/
private lemma qExpansion_one_cast_modularFormLevelRaise_coeff
    {A M : ℕ} [NeZero A] [NeZero M] {k : ℤ} (q : ℕ) [NeZero q]
    (h_eq : q * A = M)
    (G : ModularForm ((Gamma1 A).map (mapGL ℝ)) k)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hGg : (⇑G : UpperHalfPlane → ℂ) = ⇑g) (n : ℕ) :
    (UpperHalfPlane.qExpansion (1 : ℝ)
        (h_eq ▸ HeckeRing.GL2.modularFormLevelRaise A q k G :
          ModularForm ((Gamma1 M).map (mapGL ℝ)) k)).coeff n =
      if q ∣ n then (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff (n / q) else 0 := by
  rw [qExpansion_one_modularForm_cast_level h_eq _,
    HeckeRing.GL2.qExpansion_one_modularFormLevelRaise_coeff G n,
    qExpansion_ext2 G g hGg]

lemma function_identity_Δ_eq_sum_V_q_F
    {L : ℕ} [NeZero L] {k : ℤ}
    (Δ : CuspForm ((Gamma1 L).map (mapGL ℝ)) k)
    (l : ℕ) [NeZero l]
    (g_q_fam : ℕ → CuspForm ((Gamma1 (L * l ^ 2)).map (mapGL ℝ)) k)
    (hL_dvd : L ∣ L * l ^ 2)
    (h_q_NeZero : ∀ q ∈ l.primeFactors, NeZero ((L * l ^ 2) / q))
    (h_q_dvd_Ll2 : ∀ q ∈ l.primeFactors, q ∣ L * l ^ 2)
    (F_q_fam : (q : ℕ) → (hq : q ∈ l.primeFactors) →
      letI := h_q_NeZero q hq
      CuspForm ((Gamma1 ((L * l ^ 2) / q)).map (mapGL ℝ)) k)
    (hF_eq_g : ∀ q (hq : q ∈ l.primeFactors),
      letI := h_q_NeZero q hq
      (⇑(F_q_fam q hq) : UpperHalfPlane → ℂ) = ⇑(g_q_fam q))
    (h_qexp_eq : ∀ n : ℕ,
      (UpperHalfPlane.qExpansion (1 : ℝ) Δ).coeff n =
      ∑ q ∈ l.primeFactors,
        if q ∣ n then (UpperHalfPlane.qExpansion (1 : ℝ) (g_q_fam q)).coeff (n / q)
        else 0) :
    haveI : NeZero (L * l ^ 2) :=
      ⟨Nat.mul_ne_zero (NeZero.ne L) (pow_ne_zero 2 (NeZero.ne l))⟩
    (⇑(CuspForm.restrictSubgroup (Gamma1_map_le_Gamma1_map_of_dvd hL_dvd) Δ) :
      UpperHalfPlane → ℂ) =
    fun z ↦ ∑ q ∈ l.primeFactors.attach,
      (haveI : NeZero ((L * l ^ 2) / q.val) := h_q_NeZero q.val q.property
       haveI : NeZero q.val := ⟨(Nat.prime_of_mem_primeFactors q.property).ne_zero⟩
       (⇑(HeckeRing.GL2.modularFormLevelRaise ((L * l ^ 2) / q.val) q.val k
         (F_q_fam q.val q.property).toModularForm') :
         UpperHalfPlane → ℂ) z) := by
  haveI hLl2_NeZero : NeZero (L * l ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne L) (pow_ne_zero 2 (NeZero.ne l))⟩
  have h1_period_Ll2 := one_mem_strictPeriods_Gamma1_map (L * l ^ 2)
  let φ : (q : l.primeFactors) → ModularForm ((Gamma1 (L * l ^ 2)).map (mapGL ℝ)) k :=
    fun q ↦
      haveI : NeZero ((L * l ^ 2) / q.val) := h_q_NeZero q.val q.property
      haveI : NeZero q.val := ⟨(Nat.prime_of_mem_primeFactors q.property).ne_zero⟩
      have h_eq : q.val * ((L * l ^ 2) / q.val) = L * l ^ 2 :=
        Nat.mul_div_cancel' (h_q_dvd_Ll2 q.val q.property)
      h_eq ▸ HeckeRing.GL2.modularFormLevelRaise
        ((L * l ^ 2) / q.val) q.val k (F_q_fam q.val q.property).toModularForm'
  let Δ_lifted : ModularForm ((Gamma1 (L * l ^ 2)).map (mapGL ℝ)) k :=
    ModularForm.restrictSubgroup
      (HeckeRing.GL2.MainLemma.Gamma1_mapGL_le_of_dvd hL_dvd) Δ.toModularForm'
  have h_φ_qexp : ∀ q : l.primeFactors, ∀ n : ℕ,
      (UpperHalfPlane.qExpansion (1 : ℝ) (φ q)).coeff n =
      (if q.val ∣ n then
        (UpperHalfPlane.qExpansion (1 : ℝ) (g_q_fam q.val)).coeff (n / q.val)
       else 0) := by
    intro q n
    haveI : NeZero ((L * l ^ 2) / q.val) := h_q_NeZero q.val q.property
    haveI : NeZero q.val := ⟨(Nat.prime_of_mem_primeFactors q.property).ne_zero⟩
    exact qExpansion_one_cast_modularFormLevelRaise_coeff q.val
      (Nat.mul_div_cancel' (h_q_dvd_Ll2 q.val q.property)) _ (g_q_fam q.val)
      (hF_eq_g q.val q.property) n
  have h_coeff : ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℝ) Δ_lifted).coeff n =
      ∑ q ∈ l.primeFactors.attach,
        (UpperHalfPlane.qExpansion (1 : ℝ) (φ q)).coeff n := by
    intro n
    change (PowerSeries.coeff (R := ℂ) n) (UpperHalfPlane.qExpansion 1 ⇑Δ) = _
    rw [h_qexp_eq n, ← Finset.sum_attach l.primeFactors
      (fun q ↦ if q ∣ n then
        (UpperHalfPlane.qExpansion (1 : ℝ) (g_q_fam q)).coeff (n / q) else 0)]
    exact Finset.sum_congr rfl fun q _ ↦ (h_φ_qexp q n).symm
  change (⇑Δ_lifted : UpperHalfPlane → ℂ) = _
  rw [modularForm_eq_sum_of_qExpansion_coeff_eq h1_period_Ll2 Δ_lifted
    l.primeFactors.attach φ h_coeff]
  refine funext fun z ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  haveI : NeZero ((L * l ^ 2) / q.val) := h_q_NeZero q.val q.property
  haveI : NeZero q.val := ⟨(Nat.prime_of_mem_primeFactors q.property).ne_zero⟩
  exact modularForm_cast_level_apply
    (Nat.mul_div_cancel' (h_q_dvd_Ll2 q.val q.property)) _ z

end HeckeRing.GL2

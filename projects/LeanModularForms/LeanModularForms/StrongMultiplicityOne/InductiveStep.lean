/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.StrongMultiplicityOne.DescentCharSpace

/-!
# Strong Multiplicity One via Miyake §4.6 — Main Lemma (4.6.8)

The descent witness, the inductive step, and the subset-indexed helper for
Miyake Theorem 4.6.8. Part of a multi-file split of `StrongMultiplicityOne.lean`.
-/

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

private theorem miyake_descent_witness_exists
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    (l' : ℕ) (hl'_pos : 0 < l') (hl'_sqfree : Squarefree l')
    (hpl' : Nat.Coprime p l')
    (hl'_dvd : ∀ q ∈ l'.primeFactors, q ∈ N.primeFactors)
    (hp_not_in : p ∉ l'.primeFactors)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p * l') →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0) :
    ∃ f_lower : CuspForm ((Gamma1 (N / p)).map (mapGL ℝ)) k,
      f_lower ∈ cuspFormCharSpace k χ' ∧
      ∀ m : ℕ, Nat.Coprime m l' →
        (UpperHalfPlane.qExpansion (1 : ℝ) f_lower).coeff m =
          (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff (p * m) := by
  have hfχ_mod : f.toModularForm' ∈ modFormCharSpace k χ :=
    (cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
      (k := k) χ f).mpr hfχ
  have h_cnt_pos : 0 < descendCosetCount p N := by
    have := hp.pos; unfold descendCosetCount; split_ifs <;> lia
  set c : ℂ := (p : ℂ) / (descendCosetCount p N : ℂ) with hc_def
  let Φ : CuspForm ((Gamma1 (N / p)).map (mapGL ℝ)) k :=
    descendSlashSumCuspForm χ f p hp hpN χ' hχ_eq hfχ_mod
  refine ⟨c • Φ, Submodule.smul_mem _ c
    (descendSlashSumCuspForm_mem_charSpace χ f p hp hpN χ' hχ_eq hfχ_mod), fun m hm_cop ↦ ?_⟩
  rw [show (UpperHalfPlane.qExpansion (1 : ℝ) ⇑(c • Φ)).coeff m =
        c * (UpperHalfPlane.qExpansion (1 : ℝ) Φ).coeff m from
      qExpansion_smul_cuspForm_coeff_aux c Φ m]
  haveI : NeZero (l' * (N / p)) := ⟨Nat.mul_ne_zero hl'_pos.ne' (NeZero.ne _)⟩
  obtain ⟨_χ_low, g_low, _hg_low_χ, hg_low_qexp, hg_low_full_qexp⟩ :=
    miyake_V_p_descend_identity_with_char χ f hfχ p hp hpN l' hl'_pos hl'_sqfree hpl'
      hl'_dvd hp_not_in h_vanish
  rw [Φ_qExp_coeff_eq_count_div_p_mul_g_low_coeff χ f hfχ p hp hpN χ' hχ_eq hfχ_mod
      hl'_pos hl'_sqfree hpl' hl'_dvd hp_not_in h_vanish g_low hg_low_qexp
      hg_low_full_qexp m hm_cop,
    show (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff (p * m) =
      (UpperHalfPlane.qExpansion (1 : ℝ) g_low).coeff m by
        have := hg_low_qexp (p * m) (dvd_mul_right p m)
          (Nat.coprime_mul_iff_left.mpr ⟨hpl', hm_cop⟩)
        rwa [Nat.mul_div_cancel_left m hp.pos] at this, hc_def]
  have : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have : (descendCosetCount p N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h_cnt_pos.ne'
  field_simp

private theorem erase_prod_descent_properties
    (S : Finset ℕ) (hS : S ⊆ N.primeFactors) {p : ℕ} (hp_prime : p.Prime) :
    0 < (S.erase p).prod id ∧ Nat.Coprime p ((S.erase p).prod id) ∧
      Squarefree ((S.erase p).prod id) ∧
      (∀ q ∈ ((S.erase p).prod id).primeFactors, q ∈ N.primeFactors) ∧
      p ∉ ((S.erase p).prod id).primeFactors := by
  have hl'_pos : 0 < (S.erase p).prod id :=
    Finset.prod_pos fun q hq ↦
      (Nat.prime_of_mem_primeFactors (hS (Finset.mem_of_mem_erase hq))).pos
  have hpl' : Nat.Coprime p ((S.erase p).prod id) :=
    Nat.Coprime.prod_right fun q hq ↦ (Nat.coprime_primes hp_prime
      (Nat.prime_of_mem_primeFactors (hS (Finset.mem_of_mem_erase hq)))).mpr
      (Finset.ne_of_mem_erase hq).symm
  have hl'_sqfree : Squarefree ((S.erase p).prod id) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun q₁ hq₁ q₂ hq₂ hne ↦ ?_)
      fun q hq ↦
        (Nat.prime_of_mem_primeFactors (hS (Finset.mem_of_mem_erase hq))).squarefree
    show IsRelPrime (id q₁) (id q₂)
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (hS (Finset.mem_of_mem_erase hq₁)))
      (Nat.prime_of_mem_primeFactors (hS (Finset.mem_of_mem_erase hq₂)))).mpr hne
  exact ⟨hl'_pos, hpl', hl'_sqfree,
    fun _ hq ↦ Nat.primeFactors_mono (Finset.prod_primes_dvd N
      (fun _ hq ↦ (Nat.prime_of_mem_primeFactors (hS (Finset.mem_of_mem_erase hq))).prime)
      fun _ hq ↦ Nat.dvd_of_mem_primeFactors (hS (Finset.mem_of_mem_erase hq)))
        (NeZero.ne N) hq,
    fun hp_in_l' ↦
      (hp_prime.coprime_iff_not_dvd.mp hpl') (Nat.dvd_of_mem_primeFactors hp_in_l')⟩

private theorem castLevelRaise_mem_cuspFormCharSpace
    {p : ℕ} [NeZero p] [NeZero (N / p)]
    (hpN : p ∣ N) (χ : (ZMod N)ˣ →* ℂˣ) (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    (f_lower : CuspForm ((Gamma1 (N / p)).map (mapGL ℝ)) k)
    (hf_lower_char : f_lower ∈ cuspFormCharSpace k χ') :
    HeckeRing.GL2.AtkinLehner.castLevelRaise N p hpN k f_lower ∈
      cuspFormCharSpace k χ := by
  have h_lr_char :
      HeckeRing.GL2.levelRaise (N / p) p k f_lower ∈
        cuspFormCharSpace k (χ'.comp (ZMod.unitsMap (Nat.dvd_mul_left (N / p) p))) :=
    cuspForm_levelRaise_mem_cuspFormCharSpace (N / p) p k χ' hf_lower_char
  rw [HeckeRing.GL2.AtkinLehner.castLevelRaise_apply, hχ_eq]
  exact (show ∀ (M : ℕ) [NeZero M] (heq : p * (N / p) = M) (h₁ : (N / p) ∣ M),
      (heq ▸ HeckeRing.GL2.levelRaise (N / p) p k f_lower :
          CuspForm ((Gamma1 M).map (mapGL ℝ)) k) ∈
        cuspFormCharSpace k (χ'.comp (ZMod.unitsMap h₁)) by
    rintro M _ rfl h₁; convert h_lr_char using 2) N (Nat.mul_div_cancel' hpN) _

private theorem castLevelRaise_qExpansion_coeff_eq
    {p : ℕ} [NeZero p] [NeZero (N / p)] (hp_prime : p.Prime) (hpN : p ∣ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (f_lower : CuspForm ((Gamma1 (N / p)).map (mapGL ℝ)) k) {l' : ℕ}
    (hf_lower_qexp : ∀ m : ℕ, Nat.Coprime m l' →
      (UpperHalfPlane.qExpansion (1 : ℝ) f_lower).coeff m =
        (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff (p * m))
    (h_vanish' : ∀ n : ℕ, Nat.Coprime n (p * l') →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0)
    {n : ℕ} (hn : Nat.Coprime n l') :
    (UpperHalfPlane.qExpansion (1 : ℝ)
        (HeckeRing.GL2.AtkinLehner.castLevelRaise N p hpN k f_lower)).coeff n =
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n := by
  have h_cast_coe :
      (⇑(HeckeRing.GL2.AtkinLehner.castLevelRaise N p hpN k f_lower) :
          UpperHalfPlane → ℂ) =
        ⇑(HeckeRing.GL2.levelRaise (N / p) p k f_lower) := by
    rw [HeckeRing.GL2.AtkinLehner.castLevelRaise_apply]
    exact (show ∀ {A B : ℕ} (heq : A = B) (x : CuspForm ((Gamma1 A).map (mapGL ℝ)) k),
        (⇑(heq ▸ x : CuspForm ((Gamma1 B).map (mapGL ℝ)) k) :
            UpperHalfPlane → ℂ) = ⇑x from fun heq x ↦ by cases heq; rfl)
      (Nat.mul_div_cancel' hpN) _
  have h_lr_coe : (⇑(HeckeRing.GL2.levelRaise (N / p) p k f_lower) :
          UpperHalfPlane → ℂ) =
        ⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k
            f_lower.toModularForm') := rfl
  rw [qExpansion_ext2 _ _ h_cast_coe, qExpansion_ext2 _ _ h_lr_coe,
    HeckeRing.GL2.qExpansion_one_modularFormLevelRaise_coeff f_lower.toModularForm' n]
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    show (UpperHalfPlane.qExpansion (1 : ℝ) f_lower).coeff (n / p) =
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n
    rw [hf_lower_qexp (n / p) (hn.coprime_div_left hpn), Nat.mul_div_cancel' hpn]
  · rw [if_neg hpn]
    exact (h_vanish' n (Nat.Coprime.mul_right
      (hp_prime.coprime_iff_not_dvd.mpr hpn).symm hn)).symm

/-- **M8: Inductive step for Miyake 4.6.8.** For `f ∈ S_k(Γ_1(N), χ)` with
coprime-vanishing on the prime-subset `S` and `p ∈ S`, there exists
`f_p ∈ qSupportedOnDvdSubmodule N k p ∩ cuspFormCharSpace` such that
`f - f_p` has coprime-vanishing on `S.erase p`. -/
theorem miyake_4_6_8_inductive_step
    (χ : (ZMod N)ˣ →* ℂˣ)
    (S : Finset ℕ) (hS : S ⊆ N.primeFactors)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (S.prod id) →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0)
    {p : ℕ} (hp_in : p ∈ S) [NeZero (N / p)]
    (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap
      (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors (hS hp_in))))) :
    ∃ f_p : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      f_p ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule N k p ∧
      f_p ∈ cuspFormCharSpace k χ ∧
      ∀ n : ℕ, Nat.Coprime n ((S.erase p).prod id) →
        (UpperHalfPlane.qExpansion (1 : ℝ) (f - f_p)).coeff n = 0 := by
  set l' := (S.erase p).prod id with hl'_def
  have h_prod_eq : S.prod id = p * l' := by
    rw [hl'_def, ← Finset.mul_prod_erase S id hp_in]; simp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors (hS hp_in)
  have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors (hS hp_in)
  have h_vanish' (n : ℕ) (hn : Nat.Coprime n (p * l')) :
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0 := h_vanish n (h_prod_eq ▸ hn)
  haveI : NeZero p := ⟨hp_prime.ne_zero⟩
  obtain ⟨hl'_pos, hpl', hl'_sqfree, hl'_dvd, hp_not_in_l'⟩ :=
    erase_prod_descent_properties S hS hp_prime
  obtain ⟨f_lower, hf_lower_char, hf_lower_qexp⟩ :=
    miyake_descent_witness_exists χ f hfχ p hp_prime hpN χ' hχ_eq l' hl'_pos
      hl'_sqfree hpl' hl'_dvd hp_not_in_l' h_vanish'
  set f_p : CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
    HeckeRing.GL2.AtkinLehner.castLevelRaise N p hpN k f_lower
  have h_qexp_eq (n : ℕ) (hn : Nat.Coprime n l') :
      (UpperHalfPlane.qExpansion (1 : ℝ) f_p).coeff n =
        (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n :=
    castLevelRaise_qExpansion_coeff_eq hp_prime hpN f f_lower hf_lower_qexp h_vanish' hn
  refine ⟨f_p, HeckeRing.GL2.AtkinLehner.range_castLevelRaise_le_qSupportedOnDvdSubmodule
      hpN k ⟨f_lower, rfl⟩,
    castLevelRaise_mem_cuspFormCharSpace hpN χ χ' hχ_eq f_lower hf_lower_char,
    fun n hn ↦ ?_⟩
  have h1_period := one_mem_strictPeriods_Gamma1_map N
  have h_sub : UpperHalfPlane.qExpansion (1 : ℝ) (f - f_p) =
      UpperHalfPlane.qExpansion (1 : ℝ) f -
      UpperHalfPlane.qExpansion (1 : ℝ) f_p := by
    rw [sub_eq_add_neg, sub_eq_add_neg, ← ModularForm.qExpansion_neg one_pos h1_period f_p]
    exact ModularForm.qExpansion_add (Γ := (Gamma1 N).map (mapGL ℝ)) (h := 1) (a := k) (b := k)
      one_pos h1_period f (- f_p)
  rw [h_sub, map_sub, h_qexp_eq n hn, sub_self]

private theorem cuspForm_eq_zero_of_qExpansion_coeff_eq_zero {N : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h : ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℝ) f.toModularForm').coeff n = 0) :
    f = 0 := by
  refine DFunLike.coe_injective ?_
  show (⇑f : UpperHalfPlane → ℂ) = 0
  rw [show (⇑f : UpperHalfPlane → ℂ) = ⇑f.toModularForm' from rfl,
    (ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods_Gamma1_map N)
      (f := f.toModularForm')).mp
      (PowerSeries.ext fun n ↦ by rw [map_zero]; exact h n)]; rfl

private theorem sum_ite_eq_add_sum_erase {M : Type*} [AddCommMonoid M]
    {S : Finset ℕ} {p : ℕ} (hp_in : p ∈ S) (a : M) (g : ℕ → M) :
    ∑ q ∈ S, (if q = p then a else g q) = a + ∑ q ∈ S.erase p, g q := by
  rw [← Finset.sum_erase_add _ _ hp_in, add_comm]
  congr 1
  · simp
  · exact Finset.sum_congr rfl fun q hq ↦ by simp [Finset.ne_of_mem_erase hq]

private lemma factorsThrough_of_conductor_dvd {n : ℕ} (χ : DirichletCharacter ℂ n)
    {d : ℕ} (hcd : χ.conductor ∣ d) (hdn : d ∣ n) :
    χ.FactorsThrough d :=
  ⟨hdn, DirichletCharacter.changeLevel hcd χ.primitiveCharacter, by
    rw [← DirichletCharacter.changeLevel_trans χ.primitiveCharacter hcd hdn,
      DirichletCharacter.changeLevel_primitiveCharacter]⟩

private lemma conductor_dvd_of_factorsThrough {n : ℕ} (χ : DirichletCharacter ℂ n)
    (hn : n ≠ 0) {d : ℕ} (hfac : χ.FactorsThrough d) :
    χ.conductor ∣ d :=
  haveI : NeZero n := ⟨hn⟩
  χ.conductor_dvd_of_mem_conductorSet ((DirichletCharacter.mem_conductorSet_iff χ).mpr hfac)

private lemma conductor_changeLevel {n m : ℕ} (hnm : n ∣ m) [NeZero n] [NeZero m]
    (χ : DirichletCharacter ℂ n) :
    (DirichletCharacter.changeLevel hnm χ).conductor = χ.conductor := by
  set c := (DirichletCharacter.changeLevel hnm χ).conductor
  have hcn : c ∣ n :=
    conductor_dvd_of_factorsThrough (DirichletCharacter.changeLevel hnm χ) (NeZero.ne m)
      (DirichletCharacter.changeLevel_factorsThrough χ hnm)
  have hχ_fac_c : χ.FactorsThrough c := by
    obtain ⟨_hcm, χ_c, hχc⟩ := DirichletCharacter.factorsThrough_conductor
      (DirichletCharacter.changeLevel hnm χ)
    exact ⟨hcn, χ_c, DirichletCharacter.changeLevel_injective hnm <| by
      rw [← DirichletCharacter.changeLevel_trans χ_c hcn hnm, ← hχc]⟩
  refine Nat.dvd_antisymm ?_ (conductor_dvd_of_factorsThrough χ (NeZero.ne n) hχ_fac_c)
  refine conductor_dvd_of_factorsThrough (DirichletCharacter.changeLevel hnm χ) (NeZero.ne m)
    ⟨χ.conductor_dvd_level.trans hnm, χ.primitiveCharacter, ?_⟩
  conv_rhs => rw [DirichletCharacter.changeLevel_trans χ.primitiveCharacter
    χ.conductor_dvd_level hnm, DirichletCharacter.changeLevel_primitiveCharacter]

private theorem miyake_4_6_8_factor_dichotomy
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (l' : ℕ) (hl'_pos : 0 < l') (hl'_sqfree : Squarefree l')
    (hpl' : Nat.Coprime p l')
    (hl'_dvd : ∀ q ∈ l'.primeFactors, q ∈ N.primeFactors)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p * l') →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0) :
    (∀ n : ℕ, Nat.Coprime n l' →
        (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0) ∨
      ∃ (χ' : (ZMod (N / p))ˣ →* ℂˣ),
        χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero l' := ⟨hl'_pos.ne'⟩
  haveI : NeZero (l' * N) :=
    ⟨Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp hl'_pos) (NeZero.ne N)⟩
  obtain ⟨g, hg_char, hg_supp, hg_qexp⟩ :=
    miyake_g_p_supported χ f hfχ p hp l' hl'_pos hl'_sqfree hl'_dvd h_vanish
  have hNlN : N ∣ l' * N := Nat.dvd_mul_left N l'
  have hpM : p ∣ l' * N := dvd_mul_of_dvd_right hpN l'
  have h_Mp_eq : (l' * N) / p = l' * (N / p) := Nat.mul_div_assoc l' hpN
  haveI : NeZero ((l' * N) / p) := h_Mp_eq ▸ inferInstance
  set χ_dir : DirichletCharacter ℂ N := Newform.dirichletLift χ
  set χ_M : DirichletCharacter ℂ (l' * N) := DirichletCharacter.changeLevel hNlN χ_dir with hχM
  have hχ_dir_unit : χ_dir.toUnitHom = χ :=
    MulChar.equivToUnitHom.apply_symm_apply χ
  have hχM_unit : χ_M.toUnitHom = χ.comp (ZMod.unitsMap hNlN) := by
    rw [hχM, DirichletCharacter.changeLevel_toUnitHom, hχ_dir_unit]
  rcases miyake_4_6_4_dichotomy_strong χ_M p hp hpM g
    (by rw [hχM_unit]; exact hg_char) hg_supp with
    hg_zero | ⟨h_fac, _g_p, _hg_p_char, _hg_p_eq⟩
  · refine Or.inl fun n hn_cop ↦ ?_
    have hgn := hg_qexp n
    rw [if_pos hn_cop] at hgn
    rw [← hgn, hg_zero, show (⇑(0 : CuspForm ((Gamma1 (l' * N)).map (mapGL ℝ)) k) :
      UpperHalfPlane → ℂ) = (0 : UpperHalfPlane → ℂ) from rfl, UpperHalfPlane.qExpansion_zero,
      map_zero]
  · refine Or.inr ?_
    have h_cond_dvd_lNp : χ_dir.conductor ∣ l' * (N / p) := by
      have : χ_M.conductor ∣ (l' * N) / p :=
        conductor_dvd_of_factorsThrough χ_M (NeZero.ne (l' * N)) h_fac
      rwa [hχM, conductor_changeLevel hNlN χ_dir, h_Mp_eq] at this
    have h_cond_dvd_Np : χ_dir.conductor ∣ N / p := by
      have hcd_gcd : χ_dir.conductor ∣ Nat.gcd (p * (N / p)) (l' * (N / p)) :=
        Nat.dvd_gcd ((Nat.mul_div_cancel' hpN).symm ▸ χ_dir.conductor_dvd_level) h_cond_dvd_lNp
      rwa [show Nat.gcd (p * (N / p)) (l' * (N / p)) = (N / p) * Nat.gcd p l' by
        rw [Nat.mul_comm p (N / p), Nat.mul_comm l' (N / p), Nat.gcd_mul_left],
        hpl', Nat.mul_one] at hcd_gcd
    refine ⟨(loweredCharacter (l := p)
      (factorsThrough_of_conductor_dvd χ_dir h_cond_dvd_Np (Nat.div_dvd_of_dvd hpN))).toUnitHom, ?_⟩
    have := toUnitHom_loweredCharacter (χ := χ_dir) (l := p)
      (factorsThrough_of_conductor_dvd χ_dir h_cond_dvd_Np (Nat.div_dvd_of_dvd hpN))
    rwa [hχ_dir_unit] at this

/-- **Unconditional subset-indexed helper for Miyake 4.6.8.**  For `f ∈ S_k(Γ_1(N), χ)`
vanishing on indices coprime to `S.prod id` (`S ⊆ N.primeFactors`), there is a
decomposition `f = ∑_{p ∈ S} f_p` with each `f_p` `p`-supported and in the character
space.  No `h_chi_factor` is needed: the per-prime factorisation is produced by
`miyake_4_6_8_factor_dichotomy`. -/
theorem miyake_4_6_8_subset_helper
    (χ : (ZMod N)ˣ →* ℂˣ)
    (S : Finset ℕ) (hS : S ⊆ N.primeFactors)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (S.prod id) →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0) :
    ∃ f_p : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      f = ∑ p ∈ S, f_p p ∧
      (∀ p ∈ S, f_p p ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule N k p) ∧
      (∀ p ∈ S, f_p p ∈ cuspFormCharSpace k χ) := by
  induction hSc : S.card generalizing f S with
  | zero =>
    obtain rfl : S = ∅ := Finset.card_eq_zero.mp hSc
    refine ⟨fun _ ↦ 0, ?_, ?_, ?_⟩
    · rw [cuspForm_eq_zero_of_qExpansion_coeff_eq_zero f fun n ↦
        h_vanish n (by simp [Nat.Coprime, Finset.prod_empty]), Finset.sum_empty]
    · exact fun p hp ↦ absurd hp (Finset.notMem_empty p)
    · exact fun p hp ↦ absurd hp (Finset.notMem_empty p)
  | succ n ih =>
    obtain ⟨p, hp_in⟩ : S.Nonempty := Finset.card_pos.mp (hSc ▸ Nat.succ_pos n)
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors (hS hp_in)
    have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors (hS hp_in)
    haveI : NeZero (N / p) := ⟨(Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hpN) hp_prime.pos).ne'⟩
    have h_erase_sub : S.erase p ⊆ N.primeFactors := fun q hq ↦
      hS (Finset.mem_of_mem_erase hq)
    have h_erase_card : (S.erase p).card = n := by
      rw [Finset.card_erase_of_mem hp_in, hSc]; lia
    set l' := (S.erase p).prod id with hl'_def
    have h_prod_eq : S.prod id = p * l' := by
      rw [hl'_def, ← Finset.mul_prod_erase S id hp_in]; simp
    obtain ⟨hl'_pos, hpl', hl'_sqfree, hl'_dvd, _hp_not_in_l'⟩ :=
      erase_prod_descent_properties S hS hp_prime
    rcases miyake_4_6_8_factor_dichotomy χ f hfχ hp_prime hpN l' hl'_pos hl'_sqfree hpl'
      hl'_dvd (fun m hm ↦ h_vanish m (h_prod_eq ▸ hm)) with h_f_vanish | ⟨χ', hχ_eq⟩
    · obtain ⟨f_q, h_sum, h_supp_q, h_char_q⟩ :=
        ih (S.erase p) h_erase_sub f hfχ h_f_vanish h_erase_card
      refine ⟨fun q ↦ if q = p then 0 else f_q q, ?_, ?_, ?_⟩
      · rw [sum_ite_eq_add_sum_erase hp_in 0 f_q, zero_add, ← h_sum]
      · intro q hq
        by_cases hqp : q = p
        · subst hqp; simpa only [if_true] using Submodule.zero_mem _
        · simp only [hqp, if_false]
          exact h_supp_q q (Finset.mem_erase.mpr ⟨hqp, hq⟩)
      · intro q hq
        by_cases hqp : q = p
        · subst hqp; simpa only [if_true] using Submodule.zero_mem _
        · simp only [hqp, if_false]
          exact h_char_q q (Finset.mem_erase.mpr ⟨hqp, hq⟩)
    · obtain ⟨f_p, h_supp, h_char, h_diff_vanish⟩ :=
        miyake_4_6_8_inductive_step χ S hS f hfχ h_vanish hp_in χ' hχ_eq
      obtain ⟨f_q, h_sum, h_supp_q, h_char_q⟩ :=
        ih (S.erase p) h_erase_sub (f - f_p) (Submodule.sub_mem _ hfχ h_char) h_diff_vanish
          h_erase_card
      refine ⟨fun q ↦ if q = p then f_p else f_q q, ?_, ?_, ?_⟩
      · rw [sum_ite_eq_add_sum_erase hp_in f_p f_q, ← h_sum]; abel
      · intro q hq
        by_cases hqp : q = p
        · subst hqp; simpa only [if_true] using h_supp
        · simp only [hqp, if_false]
          exact h_supp_q q (Finset.mem_erase.mpr ⟨hqp, hq⟩)
      · intro q hq
        by_cases hqp : q = p
        · subst hqp; simpa only [if_true] using h_char
        · simp only [hqp, if_false]
          exact h_char_q q (Finset.mem_erase.mpr ⟨hqp, hq⟩)

end HeckeRing.GL2

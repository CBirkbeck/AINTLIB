/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.SMOObligations.MiyakeDescend

/-!
# Strong Multiplicity One via Miyake §4.6 — level commutation (4.6.6)

Coset agreement across levels, slash-sum commutation, and Miyake Lemma 4.6.6
(`miyake_4_6_6_level_commute` and its `δ_l` variant). Part of a multi-file
split of `SMOObligations.lean`.
-/

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **T6a: Coset agreement across levels** (M6's combinatorial input).

For `p` prime with `(p, l) = 1`, the explicit coset list
`descendCosetList p N hp` and `descendCosetList p (l·N) hp` give
**identical matrix lists** (up to the `Fin (descendCosetCount p _)` type
adjustment).  The matrices `[1, m; 0, p]` are intrinsically independent
of the level.  The extra rep `[1,0;0,p] · mapGL γ_p^(p)` (when `p² ∤ N`)
depends on `descendExtraGamma`, which itself is chosen at each level;
however, since `(l, p) = 1`, the congruence conditions defining `γ_p^(p)`
at level `N` and at level `l·N` produce compatible choices (any such
γ_p^(p) works).  `descendCosetCount p N = descendCosetCount p (l·N)` since
`(l, p) = 1` means `p² ∣ N ↔ p² ∣ l·N`.

This is the combinatorial step in Miyake Lemma 4.6.6's proof
(p. 158, in the diagram setup). -/
theorem descendCosetList_level_agree
    {N : ℕ} [NeZero N] (l : ℕ) [NeZero l] (p : ℕ) [NeZero p] (hpl : Nat.Coprime p l) :
    haveI : NeZero (l * N) := ⟨Nat.mul_ne_zero (NeZero.ne l) (NeZero.ne N)⟩
    descendCosetCount p N = descendCosetCount p (l * N) := by
  unfold descendCosetCount
  congr 1
  exact propext ⟨fun h ↦ h.mul_left l, fun h ↦ (hpl.pow_left 2).dvd_of_dvd_mul_left h⟩

private lemma SL2_diff_map_eq_one_aux {R : Type*} [CommRing R]
    (γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (h : (γ₁ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → R) =
          (γ₂ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → R)) :
    ((γ₁ * γ₂⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → R) = 1 := by
  let φ : Matrix.SpecialLinearGroup (Fin 2) ℤ →*
      Matrix.SpecialLinearGroup (Fin 2) R :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom R)
  have h_φ_def : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → R) = (φ γ).val := fun γ ↦ by
    ext i j; rw [map_apply_coe]; simp [RingHom.mapMatrix_apply]
  rw [h_φ_def, show φ (γ₁ * γ₂⁻¹) = φ γ₁ * (φ γ₂)⁻¹ from map_mul_inv φ γ₁ γ₂,
    show φ γ₁ = φ γ₂ from Matrix.SpecialLinearGroup.ext _ _ fun i j ↦ by
      simpa [← h_φ_def] using congr_fun (congr_fun h i) j,
    mul_inv_cancel]
  rfl

private lemma SL2_map_eq_one_of_mod_aux
    {N : ℕ} [NeZero N] {p : ℕ} [NeZero p] [NeZero (N / p)] (hpN : p ∣ N)
    (hcop_int : IsCoprime ((p : ℕ) : ℤ) ((N / p : ℕ) : ℤ))
    (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hp : (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod p) = 1)
    (hNp : (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod (N / p)) = 1) :
    (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) = 1 := by
  have hpNp_eq : ((p : ℕ) : ℤ) * ((N / p : ℕ) : ℤ) = (N : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' hpN
  have hN_of_dvd : ∀ x : ℤ,
      ((p : ℕ) : ℤ) ∣ x → ((N / p : ℕ) : ℤ) ∣ x → (N : ℤ) ∣ x :=
    fun _ h₁ h₂ ↦ hpNp_eq ▸ hcop_int.mul_dvd h₁ h₂
  ext i j
  simp only [Matrix.map_apply, Matrix.one_apply]
  have h_ij_p : ((δ : Matrix (Fin 2) (Fin 2) ℤ) i j : ZMod p) = if i = j then 1 else 0 := by
    simpa [Matrix.map_apply, Matrix.one_apply] using congr_fun (congr_fun hp i) j
  have h_ij_Np : ((δ : Matrix (Fin 2) (Fin 2) ℤ) i j : ZMod (N / p)) =
      if i = j then 1 else 0 := by
    simpa [Matrix.map_apply, Matrix.one_apply] using congr_fun (congr_fun hNp i) j
  split_ifs with h
  · subst h
    simp only [if_true] at h_ij_p h_ij_Np
    have hp_dvd : ((p : ℕ) : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) i i - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; simp [h_ij_p]
    have hNp_dvd : ((N / p : ℕ) : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) i i - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; simp [h_ij_Np]
    have hmodeq : (δ : Matrix (Fin 2) (Fin 2) ℤ) i i ≡ 1 [ZMOD (N : ℤ)] := by
      rw [Int.modEq_iff_dvd, show 1 - (δ : Matrix (Fin 2) (Fin 2) ℤ) i i =
        -((δ : Matrix (Fin 2) (Fin 2) ℤ) i i - 1) by ring]
      exact dvd_neg.mpr (hN_of_dvd _ hp_dvd hNp_dvd)
    simpa using (ZMod.intCast_eq_intCast_iff _ 1 N).mpr hmodeq
  · simp only [if_neg h] at h_ij_p h_ij_Np
    have hp_dvd : ((p : ℕ) : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) i j := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h_ij_p
    have hNp_dvd : ((N / p : ℕ) : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) i j := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h_ij_Np
    have hmodeq : (δ : Matrix (Fin 2) (Fin 2) ℤ) i j ≡ 0 [ZMOD (N : ℤ)] := by
      rw [Int.modEq_iff_dvd]; simpa using hN_of_dvd _ hp_dvd hNp_dvd
    simpa using (ZMod.intCast_eq_intCast_iff _ 0 N).mpr hmodeq

private lemma SL2_diff_reduces_mod_level_of_mod_p_mod_div
    {N : ℕ} [NeZero N] {p : ℕ} [NeZero p] (hp : p.Prime) (hpN : p ∣ N)
    (hp_sq : ¬ p ^ 2 ∣ N) [NeZero (N / p)]
    (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hδ_mod_p : (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod p) = 1)
    (hδ_mod_Np : (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod (N / p)) = 1) :
    (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) = 1 := by
  have hcop : Nat.Coprime p (N / p) := by
    rw [hp.coprime_iff_not_dvd]
    refine fun h_dvd ↦ hp_sq ?_
    rw [show N = p * (N / p) from (Nat.mul_div_cancel' hpN).symm, pow_two]
    exact Nat.mul_dvd_mul_left p h_dvd
  exact SL2_map_eq_one_of_mod_aux hpN (by exact_mod_cast hcop.isCoprime) δ hδ_mod_p hδ_mod_Np

private lemma diag_conj_mapGL_eq_of_entries {p : ℕ} [NeZero p] (hp : p.Prime)
    (δ α' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (k' : ℤ)
    (hk' : (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = (p : ℤ) * k')
    (hα'_val : (α' : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0, k';
         (p : ℤ) * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0,
         (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1]) :
    (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), 0; 0, (p : ℝ)]
        (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) : GL (Fin 2) ℝ) *
          mapGL ℝ δ =
      mapGL ℝ α' *
        (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), 0; 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) : GL (Fin 2) ℝ) := by
  apply Units.ext
  simp only [Units.val_mul, mapGL_coe_matrix, map_apply_coe, RingHom.mapMatrix_apply,
    show (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), 0; 0, (p : ℝ)]
        (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) : GL (Fin 2) ℝ).val =
      !![1, 0; 0, (p : ℝ)] from rfl, hα'_val]
  refine Matrix.ext fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply] <;>
    linarith [hk', mul_comm (p : ℝ) (k' : ℝ),
              show ((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℝ) = (p : ℝ) * k' by
                exact_mod_cast hk']

/-- **T6b-coset-invariance**: the slash sum is invariant under choice of extra coset
representative `γ_p^(p)` (within the CRT congruence class), provided `f` is a
`χ`-eigenform under `Γ_0(N)`. -/
theorem descendCosetList_slash_sum_rep_invariance {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) (hp_sq : ¬ p ^ 2 ∣ N) [NeZero (N / p)]
    (χ : (ZMod N)ˣ →* ℂˣ) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ modFormCharSpace k χ)
    (γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (h₁_mod_p : ((γ₁ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod p)
                  = !![(0 : ZMod p), -1; 1, 0]))
    (h₂_mod_p : ((γ₂ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod p)
                  = !![(0 : ZMod p), -1; 1, 0]))
    (h₁_mod_Np : ((γ₁ : Matrix (Fin 2) (Fin 2) ℤ).map
                    (Int.cast : ℤ → ZMod (N / p)) = 1))
    (h₂_mod_Np : ((γ₂ : Matrix (Fin 2) (Fin 2) ℤ).map
                    (Int.cast : ℤ → ZMod (N / p)) = 1)) :
    ∀ z : UpperHalfPlane,
      (⇑f ∣[k]
        ((Matrix.GeneralLinearGroup.mkOfDetNeZero
            !![(1 : ℝ), 0; 0, (p : ℝ)]
            (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
          : GL (Fin 2) ℝ) * mapGL ℝ γ₁)) z =
      (⇑f ∣[k]
        ((Matrix.GeneralLinearGroup.mkOfDetNeZero
            !![(1 : ℝ), 0; 0, (p : ℝ)]
            (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
          : GL (Fin 2) ℝ) * mapGL ℝ γ₂)) z := by
  let δ := γ₁ * γ₂⁻¹
  have hδ_mod_p : (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod p) = 1 :=
    SL2_diff_map_eq_one_aux γ₁ γ₂ (h₁_mod_p.trans h₂_mod_p.symm)
  have hδ_mod_Np : (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod (N / p)) = 1 :=
    SL2_diff_map_eq_one_aux γ₁ γ₂ (h₁_mod_Np.trans h₂_mod_Np.symm)
  have hδ_mod_N : (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) = 1 :=
    SL2_diff_reduces_mod_level_of_mod_p_mod_div hp hpN hp_sq δ hδ_mod_p hδ_mod_Np
  have hδ_Gamma1 : δ ∈ Gamma1 N := multipass_gamma1_conjugate_in_gamma1 δ hδ_mod_N
  have hδ_01_N : (N : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa [Matrix.map_apply, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)] using
      congr_fun (congr_fun hδ_mod_N 0) 1
  obtain ⟨k', hk'⟩ : (p : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 :=
    (by exact_mod_cast hpN : (p : ℤ) ∣ (N : ℤ)).trans hδ_01_N
  let a := (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  let c := (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  let d := (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have h_det_α' : (!![a, k'; (p : ℤ) * c, d] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    have hdet : (δ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by exact_mod_cast δ.det_coe
    simp only [Matrix.det_fin_two] at hdet
    linarith [hk'.symm ▸ hdet]
  let α' : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨!![a, k'; (p : ℤ) * c, d], h_det_α'⟩
  obtain ⟨_, h22, h10⟩ := Gamma1_mem _ _|>.mp hδ_Gamma1
  have hα'_mem : α' ∈ Gamma0 N := by
    rw [Gamma0_mem]
    change ((!![a, k'; (p : ℤ) * c, d] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N) = 0
    simp [Matrix.cons_val_one, show c = (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 from rfl, h10]
  have h_chi_α' : χ (Gamma0MapUnits ⟨α', hα'_mem⟩) = 1 := by
    rw [show Gamma0MapUnits ⟨α', hα'_mem⟩ = 1 from Units.ext <| by
      simpa [Gamma0MapUnits_val, Gamma0Map, α', Matrix.cons_val_one, Matrix.head_cons,
        show d = (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 from rfl] using h22, map_one]
  let D : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![(1 : ℝ), 0; 0, (p : ℝ)]
      (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
  have hD_δ : D * mapGL ℝ δ = mapGL ℝ α' * D :=
    diag_conj_mapGL_eq_of_entries hp δ α' k' hk' rfl
  have h_split : D * mapGL ℝ γ₁ = mapGL ℝ α' * (D * mapGL ℝ γ₂) := by
    rw [show mapGL ℝ γ₁ = mapGL ℝ δ * mapGL ℝ γ₂ by simp [δ],
      ← mul_assoc, ← mul_assoc, hD_δ, mul_assoc]
  intro z
  rw [h_split, SlashAction.slash_mul,
    multipass_modFormCharSpace_slash_apply χ hfχ α' hα'_mem]
  simp [h_chi_α']; rfl

private lemma map_intCast_eq_one_of_dvd_aux {m₁ m₂ : ℕ} (hdvd : m₂ ∣ m₁)
    (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : M.map (Int.cast : ℤ → ZMod m₁) = 1) :
    M.map (Int.cast : ℤ → ZMod m₂) = 1 := by
  have h_factor : ∀ a : ℤ, ((a : ZMod m₂)) =
      (ZMod.castHom hdvd (ZMod m₂)) ((a : ZMod m₁)) :=
    fun a ↦ congr_fun (congr_arg DFunLike.coe
      (Subsingleton.elim (Int.castRingHom (ZMod m₂))
        ((ZMod.castHom hdvd (ZMod m₂)).comp (Int.castRingHom (ZMod m₁)))) : _) a
  ext i j
  have h_entry : ((M i j : ZMod m₁)) = ((1 : Matrix (Fin 2) (Fin 2) (ZMod m₁)) i j) := by
    simpa [Matrix.map_apply] using congr_fun (congr_fun hM i) j
  simp only [Matrix.map_apply]
  rw [h_factor, h_entry]
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]

/-- Function-level commutation of the slash sum across levels (Miyake Lemma 4.6.6(1)). -/
theorem descendCosetList_slash_sum_commute {N : ℕ} [NeZero N] (l : ℕ) [NeZero l] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) (hpl : Nat.Coprime p l) [NeZero (N / p)]
    (χ : (ZMod N)ˣ →* ℂˣ) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ modFormCharSpace k χ) :
    haveI : NeZero (l * N) := ⟨Nat.mul_ne_zero (NeZero.ne l) (NeZero.ne N)⟩
    ∀ z : UpperHalfPlane,
      (∑ v : Fin (descendCosetCount p N),
        (⇑f ∣[k] (descendCosetList p N hp v)) z) =
      (∑ v : Fin (descendCosetCount p (l * N)),
        (⇑f ∣[k] (descendCosetList p (l * N) hp v)) z) := by
  haveI : NeZero (l * N) := ⟨Nat.mul_ne_zero (NeZero.ne l) (NeZero.ne N)⟩
  intro z
  have h_count_eq : descendCosetCount p N = descendCosetCount p (l * N) :=
    descendCosetList_level_agree l p hpl
  symm
  refine Fintype.sum_equiv (finCongr h_count_eq.symm) _ _ fun v ↦ ?_
  by_cases h_v_lt : v.val < p
  · rw [descendCosetList_apply_lt hp h_v_lt,
        descendCosetList_apply_lt hp
          (show (finCongr h_count_eq.symm v).val < p from h_v_lt)]
    rfl
  have hp_sq_lN := not_p_sq_dvd_of_not_lt h_v_lt
  have hp_sq : ¬ p ^ 2 ∣ N := fun h ↦ hp_sq_lN (h.mul_left l)
  have hpN_lN : p ∣ l * N := dvd_mul_of_dvd_right hpN l
  haveI : NeZero ((l * N) / p) := ⟨(Nat.div_pos
    (Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne l))
      (Nat.pos_of_ne_zero (NeZero.ne N))) hpN_lN) hp.pos).ne'⟩
  obtain ⟨-, h_γ_lN_one, h_γ_lN_stronger⟩ :=
    descendExtraGamma_spec hp hpN_lN hp_sq_lN (p := p) (N := l * N)
  obtain ⟨-, h_γ_N_one, h_γ_N_mod⟩ :=
    descendExtraGamma_spec hp hpN hp_sq (p := p) (N := N)
  have h_Np_dvd_lNp : N / p ∣ (l * N) / p := by
    obtain ⟨c, hc⟩ := hpN
    exact ⟨l, by rw [hc, show l * (p * c) = p * (l * c) by ring,
      Nat.mul_div_cancel_left _ hp.pos, Nat.mul_div_cancel_left _ hp.pos, mul_comm]⟩
  rw [descendCosetList_apply_extra hp h_v_lt,
      descendCosetList_apply_extra hp (show ¬ (finCongr h_count_eq.symm v).val < p from h_v_lt)]
  exact descendCosetList_slash_sum_rep_invariance p hp hpN hp_sq χ f hfχ
    (descendExtraGamma p (l * N)) (descendExtraGamma p N)
    h_γ_lN_one h_γ_N_one
    (map_intCast_eq_one_of_dvd_aux h_Np_dvd_lNp _ h_γ_lN_stronger) h_γ_N_mod z

/-- **M6: Miyake Lemma 4.6.6 — level commutation of the Hecke descent
operator** (Miyake p. 158).

For `p` prime dividing `N`, `l > 0` with `Nat.Coprime l p`, set
`M := l · N`.  Then for any choice of Hecke descent operators `Φ_N`
(at level `N`) and `Φ_M` (at level `M`) from M5, the diagram

```
M_k(Γ_1(N)) ─Φ_N→ M_k(Γ_1(N/p))
   ↓ incl              ↓ incl
M_k(Γ_1(M)) ─Φ_M→ M_k(Γ_1(M/p))
```

commutes at the function level on `ℍ`. -/
theorem miyake_4_6_6_level_commute {N l : ℕ} [NeZero N] [NeZero l] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) (hpl : Nat.Coprime p l) [NeZero (N / p)]
    (χ : (ZMod N)ˣ →* ℂˣ) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ modFormCharSpace k χ) :
    haveI : NeZero (l * N) := ⟨Nat.mul_ne_zero (NeZero.ne l) (NeZero.ne N)⟩
    ∀ z : UpperHalfPlane,
      (∑ v : Fin (descendCosetCount p N),
        (⇑f ∣[k] (descendCosetList p N hp v)) z) =
      (∑ v : Fin (descendCosetCount p (l * N)),
        (⇑f ∣[k] (descendCosetList p (l * N) hp v)) z) :=
  descendCosetList_slash_sum_commute l p hp hpN hpl χ f hfχ

private lemma descendCosetList_upper_tri_eq_glMap_T_p_upper {p N : ℕ} [NeZero p] [NeZero N]
    (hp : p.Prime) {v : Fin (descendCosetCount p N)} (hv : v.val < p) :
    descendCosetList p N hp v = glMap (T_p_upper p hp.pos v.val) := by
  rw [descendCosetList_apply_lt hp hv]
  ext1; ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glMap, T_p_upper, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      Matrix.GeneralLinearGroup.map]

private lemma m6_2_delta_period_aux
    {N : ℕ} [NeZero N] {k : ℤ}
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (m : ℕ) (w : UpperHalfPlane) :
    f ((m : ℝ) +ᵥ w) = f w := by
  apply SlashInvariantForm.vAdd_apply_of_mem_strictPeriods
  rw [strictPeriods_Gamma1]
  exact ⟨(m : ℤ), by simp⟩

private lemma m6_2_delta_div_p_im_pos {p : ℕ} (hp : p.Prime) (z : UpperHalfPlane) (b : ℕ) :
    0 < (((z : ℂ) + (b : ℂ)) / (p : ℂ)).im := by
  rw [show (p : ℂ) = ((p : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal]
  simpa [Complex.add_im] using div_pos z.im_pos (Nat.cast_pos.mpr hp.pos)

private lemma m6_2_delta_slash_V_l_upper_tri {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (l : ℕ) [NeZero l]
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) [NeZero (l * N)]
    {v : Fin (descendCosetCount p (l * N))} (hv : v.val < p) (z : UpperHalfPlane) :
    (⇑(HeckeRing.GL2.modularFormLevelRaise N l k f) ∣[k]
        descendCosetList p (l * N) hp v) z =
      (p : ℂ)⁻¹ * f (HeckeRing.GL2.levelRaiseMatrix l •
        (⟨((z : ℂ) + v.val) / p, m6_2_delta_div_p_im_pos hp z v.val⟩ :
          UpperHalfPlane)) := by
  rw [descendCosetList_upper_tri_eq_glMap_T_p_upper hp hv,
    show ((⇑(HeckeRing.GL2.modularFormLevelRaise N l k f)) ∣[k]
        (glMap (T_p_upper p hp.pos v.val) : GL (Fin 2) ℝ)) z =
      ((⇑(HeckeRing.GL2.modularFormLevelRaise N l k f)) ∣[k]
        (T_p_upper p hp.pos v.val : GL (Fin 2) ℚ)) z from rfl,
    HeckeRing.GL2.slash_T_p_upper_eval k p hp v.val _ z,
    HeckeRing.GL2.modularFormLevelRaise_apply N l k f]

private lemma m6_2_delta_period_shift {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (l : ℕ) [NeZero l]
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ_perm : Equiv.Perm (Fin p)) (hσ : ∀ m : Fin p, (σ_perm m).val = (l * m.val) % p)
    (z : UpperHalfPlane) (v : Fin p) :
    f (HeckeRing.GL2.levelRaiseMatrix l •
        (⟨((z : ℂ) + v.val) / p, m6_2_delta_div_p_im_pos hp z v.val⟩ :
          UpperHalfPlane)) =
      f (⟨(((HeckeRing.GL2.levelRaiseMatrix l • z : UpperHalfPlane) : ℂ) +
          (σ_perm v).val) / (p : ℂ),
        m6_2_delta_div_p_im_pos hp _ (σ_perm v).val⟩ : UpperHalfPlane) := by
  set n := l * v.val / p with hn_def
  set lhs_pt : UpperHalfPlane :=
    ⟨((z : ℂ) + v.val) / p, m6_2_delta_div_p_im_pos hp z v.val⟩
  set rhs_pt : UpperHalfPlane :=
    ⟨(((HeckeRing.GL2.levelRaiseMatrix l • z : UpperHalfPlane) : ℂ) +
      (σ_perm v).val) / (p : ℂ), m6_2_delta_div_p_im_pos hp _ (σ_perm v).val⟩
  have h_arith : l * v.val = p * n + (σ_perm v).val := by
    rw [hn_def, hσ]; exact (Nat.div_add_mod (l * v.val) p).symm
  have h_pt_eq : HeckeRing.GL2.levelRaiseMatrix l • lhs_pt = (n : ℝ) +ᵥ rhs_pt := by
    apply UpperHalfPlane.ext
    simp only [lhs_pt, rhs_pt, HeckeRing.GL2.coe_levelRaiseMatrix_smul,
      UpperHalfPlane.coe_vadd]
    have h_arith_C : (l : ℂ) * v.val = p * n + (σ_perm v).val := by exact_mod_cast h_arith
    field_simp [show (p : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr hp.ne_zero]
    linear_combination h_arith_C
  exact h_pt_eq ▸ m6_2_delta_period_aux f n _

private lemma m6_2_delta_diag_commute {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (l : ℕ) [NeZero l]
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(HeckeRing.GL2.modularFormLevelRaise N l k f) ∣[k]
        (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), 0; 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) : GL (Fin 2) ℝ)) =
      HeckeRing.GL2.levelRaiseFun l k (⇑f ∣[k]
        (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), 0; 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) : GL (Fin 2) ℝ)) := by
  have hσ_D := multipass_sigma_eq_id_of_det_pos
    (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), 0; 0, (p : ℝ)]
      (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) : GL (Fin 2) ℝ)
    (by simp [Matrix.GeneralLinearGroup.det, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.det_fin_two]; exact_mod_cast hp.pos)
  simp only [HeckeRing.GL2.coe_modularFormLevelRaise, HeckeRing.GL2.levelRaiseFun,
    ModularForm.smul_slash, hσ_D, ← SlashAction.slash_mul]
  congr 2
  refine Matrix.GeneralLinearGroup.ext fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;>
    simp [HeckeRing.GL2.levelRaiseMatrix, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

private lemma m6_2_delta_upper_tri_match
    {N : ℕ} [NeZero N] {k : ℤ} (p : ℕ) [NeZero p] (hp : p.Prime) (l : ℕ) [NeZero l]
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ_perm : Equiv.Perm (Fin p)) (hσ : ∀ m : Fin p, (σ_perm m).val = (l * m.val) % p)
    (z : UpperHalfPlane) [NeZero (l * N)]
    {v : Fin (descendCosetCount p (l * N))} (hv : v.val < p)
    {w : Fin (descendCosetCount p N)} (hw : w.val < p)
    (hvw : w.val = (σ_perm ⟨v.val, hv⟩).val) :
    (⇑(HeckeRing.GL2.modularFormLevelRaise N l k f) ∣[k]
        descendCosetList p (l * N) hp v) z =
      (⇑f ∣[k] descendCosetList p N hp w) (HeckeRing.GL2.levelRaiseMatrix l • z) := by
  rw [m6_2_delta_slash_V_l_upper_tri p hp l f hv z,
    descendCosetList_upper_tri_eq_glMap_T_p_upper hp hw,
    show ((⇑f) ∣[k] (glMap (T_p_upper p hp.pos w.val) : GL (Fin 2) ℝ))
          (HeckeRing.GL2.levelRaiseMatrix l • z) =
        ((⇑f) ∣[k] (T_p_upper p hp.pos w.val : GL (Fin 2) ℚ))
          (HeckeRing.GL2.levelRaiseMatrix l • z) from rfl,
    HeckeRing.GL2.slash_T_p_upper_eval k p hp w.val (⇑f) _, hvw,
    m6_2_delta_period_shift p hp l f σ_perm hσ z ⟨v.val, hv⟩]

private lemma m6_2_delta_l_dvd_extra {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N)
    (l : ℕ) [NeZero l] [NeZero (l * N)] (hpN_lN : p ∣ l * N) (hp_sq_lN : ¬ p ^ 2 ∣ l * N) :
    (l : ℤ) ∣ (descendExtraGamma p (l * N) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  haveI : NeZero (l * N / p) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne _)) hpN_lN) hp.pos).ne'⟩
  refine ((?_ : (l : ℤ) ∣ ((l * N / p : ℕ) : ℤ)).trans
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      (Gamma0_mem.mp (descendExtraGamma_spec hp hpN_lN hp_sq_lN).1)))
  rcases hpN with ⟨c, hc⟩
  refine ⟨(N / p : ℕ), ?_⟩
  push_cast [show l * N / p = l * (N / p) by
    rw [hc, show l * (p * c) = p * (l * c) by ring,
      Nat.mul_div_cancel_left _ hp.pos, Nat.mul_div_cancel_left _ hp.pos]]
  ring

private lemma delta_levelRaise_sum_commute_of_p_sq_dvd
    {N : ℕ} [NeZero N] {k : ℤ} (p : ℕ) [NeZero p] (hp : p.Prime) (l : ℕ) [NeZero l]
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hp_sq : p ^ 2 ∣ N) [NeZero (l * N)]
    (σ_perm : Equiv.Perm (Fin p)) (hσ : ∀ m : Fin p, (σ_perm m).val = (l * m.val) % p)
    (z : UpperHalfPlane) :
    (∑ v : Fin (descendCosetCount p (l * N)),
      (⇑(HeckeRing.GL2.modularFormLevelRaise N l k f) ∣[k]
        (descendCosetList p (l * N) hp v)) z) =
    (∑ v : Fin (descendCosetCount p N),
      (⇑f ∣[k] (descendCosetList p N hp v))
        (HeckeRing.GL2.levelRaiseMatrix l • z)) := by
  have h_cnt_N : descendCosetCount p N = p := by simp [descendCosetCount, hp_sq]
  have h_cnt_lN : descendCosetCount p (l * N) = p := by
    simp [descendCosetCount, hp_sq.mul_left l]
  refine Fintype.sum_equiv
    ((finCongr h_cnt_lN).trans (σ_perm.trans (finCongr h_cnt_N.symm))) _ _ fun v ↦ ?_
  have hv_lt : v.val < p := by simpa [h_cnt_lN] using v.isLt
  have h_bij_val : ((finCongr h_cnt_lN).trans (σ_perm.trans (finCongr h_cnt_N.symm)) v).val =
      (σ_perm ⟨v.val, hv_lt⟩).val := by
    simp only [Equiv.trans_apply, finCongr_apply, Fin.val_cast]
    rw [show Fin.cast h_cnt_lN v = (⟨v.val, hv_lt⟩ : Fin p) by ext; simp]
  exact m6_2_delta_upper_tri_match p hp l f σ_perm hσ z hv_lt
    (h_bij_val ▸ (σ_perm ⟨v.val, hv_lt⟩).isLt) h_bij_val

private lemma delta_levelRaise_extra_term_commute {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (l : ℕ) [NeZero l] (hpl : Nat.Coprime p l) (hlNp : l ∣ N / p)
    (χ : (ZMod N)ˣ →* ℂˣ) (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (hfχ : f ∈ modFormCharSpace k χ)
    (hp_sq : ¬ p ^ 2 ∣ N) [NeZero (l * N)] (hp_sq_lN : ¬ p ^ 2 ∣ l * N)
    (h_cnt_N : descendCosetCount p N = p + 1)
    (h_cnt_lN : descendCosetCount p (l * N) = p + 1) (z : UpperHalfPlane) :
    (⇑(HeckeRing.GL2.modularFormLevelRaise N l k f) ∣[k]
        descendCosetList p (l * N) hp (finCongr h_cnt_lN.symm (Fin.last p))) z =
      (⇑f ∣[k] descendCosetList p N hp (finCongr h_cnt_N.symm (Fin.last p)))
        (HeckeRing.GL2.levelRaiseMatrix l • z) := by
  have hpN_lN : p ∣ l * N := dvd_mul_of_dvd_right hpN l
  haveI : NeZero (l * N / p) := ⟨(Nat.div_pos (Nat.le_of_dvd
    (Nat.pos_of_ne_zero (NeZero.ne _)) hpN_lN) hp.pos).ne'⟩
  have hdvd_lN : (l : ℤ) ∣
      (descendExtraGamma p (l * N) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    m6_2_delta_l_dvd_extra p hp hpN l hpN_lN hp_sq_lN
  rw [descendCosetList_apply_extra hp (by simp [finCongr_apply] : ¬ _ < p),
    descendCosetList_apply_extra hp (by simp [finCongr_apply] : ¬ _ < p),
    SlashAction.slash_mul, SlashAction.slash_mul,
    m6_2_delta_diag_commute p hp l f,
    HeckeRing.GL2.slash_mapGL_levelRaiseFun l k (descendExtraGamma p (l * N)) hdvd_lN,
    HeckeRing.GL2.levelRaiseFun_apply]
  exact m6_2_extra_rep_levelRaise_bridge p hp hpN hp_sq l hpl hlNp
    χ χ' hχ_eq f hfχ hpN_lN hp_sq_lN hdvd_lN _

/-- **M6(2): Miyake Lemma 4.6.6 part (2)** — descent commutes with `δ_l = V_l`
(p. 158).

For prime `p` dividing `N`, `l > 0` with `(p, l) = 1`, Miyake's diagram (2):

```
G_k(Γ_1(N), χ) ──── T_p ────→ G_k(Γ_1(N/p), χ)
       │ δ_l                          │ δ_l
       ↓                              ↓
G_k(Γ_1(lN), χ) ──── T_p ────→ G_k(Γ_1(lN/p), χ)
```

commutes, where `T_p` is the descent slash-sum operator
`f ↦ Σ_v f|[1,0;0,p]γ_v` (Miyake Eq. 4.6.13, `descendCosetList`)
and `δ_l(g)(z) = g(l·z)` is the level-raising operator
(`modularFormLevelRaise`).

Requires `f ∈ modFormCharSpace k χ` because at p² ∤ N the level-`N` and
level-`lN` coset representatives (`descendExtraGamma`) differ and must be
reconciled via `descendCosetList_slash_sum_rep_invariance`.

Requires `l ∣ N/p` to ensure the level-`lN` extra representative satisfies
the level-`N` congruence mod `N/p`, as needed by rep-invariance. -/
theorem miyake_4_6_6_level_commute_delta {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (l : ℕ) [NeZero l] (hpl : Nat.Coprime p l) (hlNp : l ∣ N / p)
    (χ : (ZMod N)ˣ →* ℂˣ) (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (hfχ : f ∈ modFormCharSpace k χ) :
    haveI : NeZero (l * N) := ⟨Nat.mul_ne_zero (NeZero.ne l) (NeZero.ne N)⟩
    ∀ z : UpperHalfPlane,
      (∑ v : Fin (descendCosetCount p (l * N)),
        (⇑(HeckeRing.GL2.modularFormLevelRaise N l k f) ∣[k]
          (descendCosetList p (l * N) hp v)) z) =
      (∑ v : Fin (descendCosetCount p N),
        (⇑f ∣[k] (descendCosetList p N hp v))
          (HeckeRing.GL2.levelRaiseMatrix l • z)) := by
  haveI : NeZero (l * N) := ⟨Nat.mul_ne_zero (NeZero.ne l) (NeZero.ne N)⟩
  intro z
  obtain ⟨σ_perm, hσ⟩ := multipass_mul_mod_p_perm_exists hp hpl
  by_cases hp_sq : p ^ 2 ∣ N
  · exact delta_levelRaise_sum_commute_of_p_sq_dvd p hp l f hp_sq σ_perm hσ z
  · have h_cnt_N : descendCosetCount p N = p + 1 := by simp [descendCosetCount, hp_sq]
    have hp_sq_lN : ¬ p ^ 2 ∣ l * N := fun h ↦
      hp_sq ((hpl.pow_left 2).dvd_of_dvd_mul_left h)
    have h_cnt_lN : descendCosetCount p (l * N) = p + 1 := by
      simp [descendCosetCount, hp_sq_lN]
    rw [Fintype.sum_equiv (finCongr h_cnt_lN) _
        (fun v ↦ (⇑(HeckeRing.GL2.modularFormLevelRaise N l k f) ∣[k]
            descendCosetList p (l * N) hp (finCongr h_cnt_lN.symm v)) z)
        (fun v ↦ by simp [finCongr_apply]),
      Fintype.sum_equiv (finCongr h_cnt_N) _
        (fun v ↦ (⇑f ∣[k] descendCosetList p N hp (finCongr h_cnt_N.symm v))
            (HeckeRing.GL2.levelRaiseMatrix l • z))
        (fun v ↦ by simp [finCongr_apply]),
      Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    congr 1
    · refine Fintype.sum_equiv σ_perm _ _ fun i ↦ ?_
      have hi_lN : i.val < descendCosetCount p (l * N) :=
        h_cnt_lN ▸ Nat.lt_succ_of_lt i.isLt
      have hsi_N : (σ_perm i).val < descendCosetCount p N :=
        h_cnt_N ▸ Nat.lt_succ_of_lt (σ_perm i).isLt
      rw [show descendCosetList p (l * N) hp (finCongr h_cnt_lN.symm i.castSucc) =
            descendCosetList p (l * N) hp ⟨i.val, hi_lN⟩ from by congr 1,
        show descendCosetList p N hp (finCongr h_cnt_N.symm (σ_perm i).castSucc) =
            descendCosetList p N hp ⟨(σ_perm i).val, hsi_N⟩ from by congr 1]
      exact m6_2_delta_upper_tri_match p hp l f σ_perm hσ z i.isLt
        (σ_perm i).isLt (by simp)
    · exact delta_levelRaise_extra_term_commute p hp hpN l hpl hlNp χ χ' hχ_eq f hfχ
        hp_sq hp_sq_lN h_cnt_N h_cnt_lN z

end HeckeRing.GL2

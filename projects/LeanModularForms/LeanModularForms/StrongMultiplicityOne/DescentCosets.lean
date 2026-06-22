/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.StrongMultiplicityOne.LevelChangeCharSpace

/-!
# Strong Multiplicity One via Miyake §4.6 — descent coset list

The forms `h`, `g`, Miyake's dichotomy 4.6.4, and the descent coset
machinery: `descendExtraGamma`, `descendCosetList`, their determinant and
action properties, culminating in `descendCosetList_action`.
-/

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The form `g := f − h` is `p`-supported when `f` satisfies the
coprime-vanishing hypothesis for `l = p · l'` (Miyake Eq. 4.6.11): `g` is the
coprime-to-`l'` filter of `f`, so `aₙ(g) = 0` whenever `(n, p) = 1`. -/
theorem miyake_g_p_supported
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (l' : ℕ) (hl'_pos : 0 < l') (hl'_sqfree : Squarefree l')
    (hl'_dvd : ∀ q ∈ l'.primeFactors, q ∈ N.primeFactors)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p * l') →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0) :
    let M := l' * N
    haveI : NeZero M := ⟨Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp hl'_pos) (NeZero.ne N)⟩
    have hNM : N ∣ M := Nat.dvd_mul_left N l'
    ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
      g ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule M k p ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n =
        if Nat.Coprime n l' then
          (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n
        else 0 := by
  obtain ⟨g, hg_char, hg_qexp⟩ :=
    miyake_4_6_5_iterated_L χ f hfχ l' hl'_pos hl'_sqfree hl'_dvd
  refine ⟨g, hg_char, ?_, hg_qexp⟩
  intro n hn_no_p
  by_cases hcop_l' : Nat.Coprime n l'
  · rw [hg_qexp n, if_pos hcop_l']
    exact h_vanish n (Nat.Coprime.mul_right (hp.coprime_iff_not_dvd.mpr hn_no_p).symm hcop_l')
  · rw [hg_qexp n, if_neg hcop_l']

/-- Strengthened Miyake 4.6.4 dichotomy: for `g ∈ qSupportedOnDvdSubmodule M k p ∩
cuspFormCharSpace`, with `p ∣ M` and `NeZero (M / p)`, either `g = 0`, or there
is `g_p` at level `Γ_1(M/p)` in the character space of the factored Dirichlet
character `χ_M`, with `V_p g_p = g` as functions on `ℍ`. -/
theorem miyake_4_6_4_dichotomy_strong
    {M : ℕ} [NeZero M] {k : ℤ}
    (χ_M : DirichletCharacter ℂ M)
    (p : ℕ) [NeZero p] [NeZero (M / p)]
    (hp : p.Prime) (hpM : p ∣ M)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hgχ : g ∈ cuspFormCharSpace k χ_M.toUnitHom)
    (hg_supp : g ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule M k p) :
    g = 0 ∨ ∃ (h_fac : χ_M.FactorsThrough (M / p))
              (g_p : CuspForm ((Gamma1 (M / p)).map (mapGL ℝ)) k),
      g_p ∈ cuspFormCharSpace k
        (HeckeRing.GL2.loweredCharacter h_fac).toUnitHom ∧
      (⇑(HeckeRing.GL2.levelRaise (M / p) p k g_p) : UpperHalfPlane → ℂ) = ⇑g := by
  obtain ⟨φ, h_eq, h_period⟩ :=
    HeckeRing.GL2.exists_levelRaise_preimage_of_coeff_support_multiples
      hp.one_lt hpM g hg_supp
  rcases HeckeRing.GL2.conductor_theorem_dichotomy_cuspForm_strong
      p M hpM k χ_M φ g hgχ h_eq h_period with
    ⟨h_fac, F, hF_char, hF_eq⟩ | hφ_zero
  · right
    refine ⟨h_fac, F, hF_char, ?_⟩
    change (HeckeRing.GL2.levelRaiseFun p k ⇑F : UpperHalfPlane → ℂ) = ⇑g
    rw [hF_eq, ← h_eq]
  · left
    exact DFunLike.ext _ _ (fun τ ↦ by simp [h_eq, hφ_zero, HeckeRing.GL2.levelRaiseFun])

private lemma matrix_int_cast_factor_aux {n : Type*} {a m : ℕ} (hm : a ∣ m)
    (M : Matrix n n ℤ) :
    M.map (Int.cast : ℤ → ZMod a) =
      (M.map (Int.cast : ℤ → ZMod m)).map (ZMod.castHom hm (ZMod a)) := by
  rw [Matrix.map_map]; congr 1; ext x; simp

private lemma descend_rotation_mat_det_map_eq_one
    {N : ℕ} {u v a b : ℤ} (h_bez : u * a + v * b = 1) (h_ab : a * b = (N : ℤ)) :
    ((!![u * a, -(v * b); v * b, u * a] : Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.cast : ℤ → ZMod N)).det = 1 := by
  rw [show (!![u * a, -(v * b); v * b, u * a] : Matrix (Fin 2) (Fin 2) ℤ).map
        (Int.cast : ℤ → ZMod N) =
      (Int.castRingHom (ZMod N)).mapMatrix !![u * a, -(v * b); v * b, u * a] from by
    ext i j; fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply, Matrix.map_apply],
    ← RingHom.map_det,
    show (!![u * a, -(v * b); v * b, u * a] : Matrix (Fin 2) (Fin 2) ℤ).det =
        (u * a) ^ 2 + (v * b) ^ 2 from by simp only [Matrix.det_fin_two_of]; ring,
    map_add, map_pow, map_pow]
  set x := (Int.castRingHom (ZMod N)) (u * a)
  set y := (Int.castRingHom (ZMod N)) (v * b)
  have h_sum : x + y = 1 := by rw [← map_add, h_bez]; simp
  have h_prd : x * y = 0 := by
    rw [← map_mul, show u * a * (v * b) = u * v * (a * b) by ring, h_ab,
      map_mul, map_natCast, ZMod.natCast_self, mul_zero]
  rw [show x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) by ring, h_sum, h_prd]; ring

/-- Existence of the extra coset representative `γ_p^(p)` in Miyake's
Lemma 4.5.11 (pp. 143–144): for prime `p` and `N` with `p ∣ N` and `p² ∤ N`,
there exists `γ ∈ Γ_0(N/p)` with `γ ≡ [0, -1; 1, 0] (mod p)` and
`γ ≡ I (mod N/p)`. -/
theorem descendExtraGamma_exists
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (N : ℕ) [NeZero N] (hpN : p ∣ N) (hp_sq : ¬ p ^ 2 ∣ N) [NeZero (N / p)] :
    ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      γ ∈ Gamma0 (N / p) ∧
      ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod p)
        = !![(0 : ZMod p), -1; 1, 0]) ∧
      ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod (N / p)) = 1) := by
  have hcop : Nat.Coprime p (N / p) := hp.coprime_iff_not_dvd.mpr fun h ↦ hp_sq <| by
    simpa [sq] using (Nat.mul_div_cancel' hpN) ▸ Nat.mul_dvd_mul_left p h
  obtain ⟨u, v, h_bez⟩ := hcop.isCoprime
  let a : ℤ := (p : ℤ)
  let b : ℤ := ((N / p : ℕ) : ℤ)
  have h_ab : a * b = (N : ℤ) := by
    change (p : ℤ) * ((N / p : ℕ) : ℤ) = (N : ℤ)
    exact_mod_cast Nat.mul_div_cancel' hpN
  let γ_mat : Matrix (Fin 2) (Fin 2) ℤ := !![u * a, -(v * b); v * b, u * a]
  have h_ua_p : ((u * a : ℤ) : ZMod p) = 0 := by simp [a]
  have h_vb_p : ((v * b : ℤ) : ZMod p) = 1 := by
    have h' : ((u * a + v * b : ℤ) : ZMod p) = 1 := by rw [h_bez]; simp
    rwa [Int.cast_add, h_ua_p, zero_add] at h'
  have h_vb_Np : ((v * b : ℤ) : ZMod (N / p)) = 0 := by
    have hb : ((b : ℤ) : ZMod (N / p)) = 0 := by
      show (((N / p : ℕ) : ℤ) : ZMod (N / p)) = 0
      exact_mod_cast ZMod.natCast_self (N / p)
    rw [Int.cast_mul, hb, mul_zero]
  have h_ua_Np : ((u * a : ℤ) : ZMod (N / p)) = 1 := by
    have h' : ((u * a + v * b : ℤ) : ZMod (N / p)) = 1 := by rw [h_bez]; simp
    rwa [Int.cast_add, h_vb_Np, add_zero] at h'
  have h_mat_p : γ_mat.map (Int.cast : ℤ → ZMod p) = !![(0 : ZMod p), -1; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [γ_mat, h_vb_p, h_ua_p]
  have h_mat_Np : γ_mat.map (Int.cast : ℤ → ZMod (N / p)) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [γ_mat, h_vb_Np, h_ua_Np]
  obtain ⟨γ, hγ⟩ := SL2Reduction.SL2_reduction_surjective N
    ⟨γ_mat.map (Int.cast : ℤ → ZMod N), descend_rotation_mat_det_map_eq_one h_bez h_ab⟩
  have h_γ_mat_N : (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) =
      γ_mat.map (Int.cast : ℤ → ZMod N) := (hγ ▸ coe_matrix_coe (R := ZMod N) γ).symm
  have h_mod_p : (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod p) =
      !![(0 : ZMod p), -1; 1, 0] := by
    rw [matrix_int_cast_factor_aux hpN, h_γ_mat_N, ← matrix_int_cast_factor_aux hpN, h_mat_p]
  have h_mod_Np : (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod (N / p)) = 1 := by
    rw [matrix_int_cast_factor_aux (Nat.div_dvd_of_dvd hpN), h_γ_mat_N,
        ← matrix_int_cast_factor_aux (Nat.div_dvd_of_dvd hpN), h_mat_Np]
  refine ⟨γ, ?_, h_mod_p, h_mod_Np⟩
  rw [Gamma0_mem]; simpa using congr_fun (congr_fun h_mod_Np 1) 0

/-- Number of coset representatives for the Hecke descent operator: `p` when `p² ∣ N`,
`p + 1` when `p² ∤ N` (Miyake's `d + 1`). -/
def descendCosetCount (p N : ℕ) : ℕ := if p ^ 2 ∣ N then p else p + 1

/-- A fixed element of `Γ_0(N/p)` satisfying `γ ≡ [0,-1;1,0] (mod p)` and
`γ ≡ I (mod N/p)`, used as the extra coset representative when `p² ∤ N`.
Returns `1` when the primality/divisibility conditions fail. -/
noncomputable def descendExtraGamma
    (p : ℕ) [NeZero p] (N : ℕ) [NeZero N] :
    Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  if h : p.Prime ∧ p ∣ N ∧ ¬ p ^ 2 ∣ N ∧ N / p ≠ 0 then
    haveI : NeZero (N / p) := ⟨h.2.2.2⟩
    (descendExtraGamma_exists p h.1 N h.2.1 h.2.2.1).choose
  else 1

/-- Coset matrices for the Hecke descent operator `Γ_0(N) → Γ_0(N/p)`
(Miyake Lemma 4.5.11, pp. 143–144).

For `v < p`: the upper-triangular representative `[1, v; 0, p]`.
For `v = p` (only when `p² ∤ N`): the product `[1, 0; 0, p] · descendExtraGamma p N`. -/
noncomputable def descendCosetList (p N : ℕ) [NeZero p] [NeZero N] (hp : p.Prime) :
    Fin (descendCosetCount p N) → GL (Fin 2) ℝ :=
  fun v ↦
    if h_v : v.val < p then
      Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(1 : ℝ), (v.val : ℝ); 0, (p : ℝ)]
        (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
    else
      (Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), 0; 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)) *
      mapGL ℝ (descendExtraGamma p N)

private lemma descend_upper_tri_raw_matrix_identity
    (p : ℕ) (A B C D : ℤ) (v v' a01 : ℤ)
    (ha01 : (p : ℤ) * a01 = B + v * D - (A + v * C) * v') :
    (!![(1 : ℤ), v; 0, (p : ℤ)] * !![A, B; C, D] : Matrix (Fin 2) (Fin 2) ℤ) =
      !![A + v * C, a01; (p : ℤ) * C, D - C * v'] *
        !![(1 : ℤ), v'; 0, (p : ℤ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    lia

private lemma descend_extra_raw_matrix_identity (p : ℕ) (A B C D a b c d : ℤ)
    (v α01 : ℤ) (had : a * d - b * c = 1)
    (h01 : (p : ℤ) * α01 = a * (B + v * D) - b * (A + v * C)) :
    (!![(1 : ℤ), v; 0, (p : ℤ)] * !![A, B; C, D] : Matrix (Fin 2) (Fin 2) ℤ) =
      !![A * d - B * c + v * (C * d - D * c), α01;
         (p : ℤ) * (C * d - D * c), D * a - C * b] *
        !![(a : ℤ), b; (p : ℤ) * c, (p : ℤ) * d] := by
  have hL : (!![(1 : ℤ), v; 0, (p : ℤ)] * !![A, B; C, D] : Matrix (Fin 2) (Fin 2) ℤ) =
      !![A + v * C, B + v * D; (p : ℤ) * C, (p : ℤ) * D] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hR : !![A * d - B * c + v * (C * d - D * c), α01;
         (p : ℤ) * (C * d - D * c), D * a - C * b] *
        !![(a : ℤ), b; (p : ℤ) * c, (p : ℤ) * d] =
      !![A + v * C, B + v * D; (p : ℤ) * C, (p : ℤ) * D] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · have : α01 * ((p : ℤ) * c) = ((p : ℤ) * α01) * c := by ring
      rw [this, h01]; linear_combination (A + v * C) * had
    · have : α01 * ((p : ℤ) * d) = ((p : ℤ) * α01) * d := by ring
      rw [this, h01]; linear_combination (B + v * D) * had
    · linear_combination (p : ℤ) * C * had
    · linear_combination (p : ℤ) * D * had
  rw [hL, hR]

/-- Every matrix in `descendCosetList p N hp` has determinant `p`. -/
theorem descendCosetList_det (p N : ℕ) [NeZero p] [NeZero N] (hp : p.Prime) :
    ∀ v : Fin (descendCosetCount p N),
      (descendCosetList p N hp v : Matrix (Fin 2) (Fin 2) ℝ).det = (p : ℝ) := by
  intro v
  unfold descendCosetList
  split_ifs with h_v
  · simp [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.det_fin_two]
  · rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul,
        Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
        Matrix.SpecialLinearGroup.mapGL_coe_matrix,
        Matrix.SpecialLinearGroup.map_apply_coe,
        RingHom.mapMatrix_apply,
        show ((descendExtraGamma p N).val.map (algebraMap ℤ ℝ)).det = 1 from by
          simp [← Int.cast_det, (descendExtraGamma p N).property]]
    simp [Matrix.det_fin_two]

private lemma descend_aux_lit_real_eq_map_int (p v : ℕ) :
    (!![(1 : ℝ), (v : ℝ); 0, (p : ℝ)] : Matrix (Fin 2) (Fin 2) ℝ) =
      (!![(1 : ℤ), (v : ℤ); 0, (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

private lemma descend_aux_α_mat_in_Gamma0
    {p N : ℕ} [NeZero N] (hpN : p ∣ N) {α : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    {x : ℤ} (hα_10 : (α : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (p : ℤ) * x)
    (hx : ((N / p : ℕ) : ℤ) ∣ x) : α ∈ Gamma0 N := by
  rw [CongruenceSubgroup.Gamma0_mem, hα_10]
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_
  obtain ⟨y, hy⟩ := hx
  have hpNp : (p : ℤ) * ((N / p : ℕ) : ℤ) = (N : ℤ) := by exact_mod_cast Nat.mul_div_cancel' hpN
  exact ⟨y, by linear_combination (p : ℤ) * hy + y * hpNp⟩

private lemma descend_aux_lift_int_eq_to_GL
    {p : ℕ} [NeZero p] (hp : p.Prime) (m : ℕ)
    {γ' α : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    {X : GL (Fin 2) ℝ} {M_R : Matrix (Fin 2) (Fin 2) ℤ}
    (hX : (X : Matrix (Fin 2) (Fin 2) ℝ) = M_R.map (algebraMap ℤ ℝ))
    (h_int : (!![(1 : ℤ), (m : ℤ); 0, (p : ℤ)] *
        (γ' : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      (α : Matrix (Fin 2) (Fin 2) ℤ) * M_R) :
    (Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(1 : ℝ), (m : ℝ); 0, (p : ℝ)]
        (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
      : GL (Fin 2) ℝ) * mapGL ℝ γ' = mapGL ℝ α * X := by
  apply Units.ext
  change (!![(1 : ℝ), (m : ℝ); 0, (p : ℝ)] *
      (γ' : Matrix _ _ ℤ).map (algebraMap ℤ ℝ) : Matrix _ _ ℝ) =
      ((α : Matrix _ _ ℤ).map (algebraMap ℤ ℝ) * (X : Matrix _ _ ℝ) : Matrix _ _ ℝ)
  rw [hX, descend_aux_lit_real_eq_map_int p m, ← Matrix.map_mul, ← Matrix.map_mul]
  exact congr_arg (·.map (algebraMap ℤ ℝ)) h_int

private lemma descend_exists_fin_isUnit_mul_eq {p : ℕ} [NeZero p]
    {a : ZMod p} (ha : IsUnit a) (b : ZMod p) :
    ∃ m : Fin p, a * (m.val : ZMod p) = b := by
  obtain ⟨u, rfl⟩ := ha
  refine ⟨⟨((u⁻¹ : (ZMod p)ˣ).val * b).val, ZMod.val_lt _⟩, ?_⟩
  rw [ZMod.natCast_zmod_val, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

private lemma descend_upper_tri_target_witness
    {N : ℕ} [NeZero N] {p : ℕ} [NeZero p] (hp : p.Prime) (hpN : p ∣ N)
    {γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (h_C_dvd_Np : ((N / p : ℕ) : ℤ) ∣ (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (m m' : Fin p)
    (h_moeb : (((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) +
        (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod p)) *
        (m'.val : ZMod p) =
      ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod p) +
        (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod p)) :
    ∃ α : Matrix.SpecialLinearGroup (Fin 2) ℤ, α ∈ Gamma0 N ∧
      (Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), (m.val : ℝ); 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
        : GL (Fin 2) ℝ) * mapGL ℝ γ' =
      mapGL ℝ α *
      (Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), (m'.val : ℝ); 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
        : GL (Fin 2) ℝ) := by
  set A := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set B := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  set C := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set D := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have hdet : A * D - B * C = 1 := by rw [← Matrix.det_fin_two]; exact γ'.property
  obtain ⟨α01_int, hα01⟩ : (p : ℤ) ∣
      (B + (m.val : ℤ) * D - (A + (m.val : ℤ) * C) * (m'.val : ℤ)) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    linear_combination -h_moeb
  let α_mat : Matrix (Fin 2) (Fin 2) ℤ :=
    !![A + (m.val : ℤ) * C, α01_int; (p : ℤ) * C, D - C * (m'.val : ℤ)]
  have hα01' : (p : ℤ) * α01_int =
      B + (m.val : ℤ) * D - (A + (m.val : ℤ) * C) * (m'.val : ℤ) := by lia
  have h_det_α : α_mat.det = 1 := by
    rw [show α_mat.det = (A + (m.val : ℤ) * C) * (D - C * (m'.val : ℤ)) -
      α01_int * ((p : ℤ) * C) from Matrix.det_fin_two_of _ _ _ _]
    linear_combination hdet - C * hα01'
  refine ⟨⟨α_mat, h_det_α⟩,
    descend_aux_α_mat_in_Gamma0 (x := C) hpN (by simp [α_mat]) h_C_dvd_Np, ?_⟩
  refine descend_aux_lift_int_eq_to_GL hp m.val
    (by rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
        exact descend_aux_lit_real_eq_map_int p m'.val) ?_
  rw [show (γ' : Matrix (Fin 2) (Fin 2) ℤ) = !![A, B; C, D] from by
    ext i j; fin_cases i <;> fin_cases j <;> rfl]
  exact descend_upper_tri_raw_matrix_identity p A B C D
    (m.val : ℤ) (m'.val : ℤ) α01_int hα01'

/-- Miyake Lemma 4.5.11 (`p ∣ M` case, p. 144): when `p² ∣ N`, the action of
`γ' ∈ Γ_0(N/p)` on `[1, m; 0, p]` stays within the upper-triangular coset
representatives. The canonical target `m'` is pinned by
`a · m' ≡ b + m · d (mod p)`. -/
theorem descendCosetList_action_upper_tri_clean
    {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) (hp_sq : p ^ 2 ∣ N)
    [NeZero (N / p)]
    (γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h_γ' : γ' ∈ Gamma0 (N / p))
    (m : Fin p) :
    ∃ (m' : Fin p) (α : Matrix.SpecialLinearGroup (Fin 2) ℤ)
      (_ : α ∈ Gamma0 N),
      (((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) * (m'.val : ZMod p) =
        ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod p) +
         (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod p)) ∧
      ((Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), (m.val : ℝ); 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
        : GL (Fin 2) ℝ) * mapGL ℝ γ' =
      mapGL ℝ α *
      (Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), (m'.val : ℝ); 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
        : GL (Fin 2) ℝ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set A := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set B := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  set C := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set D := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have h_C_dvd_Np : ((N / p : ℕ) : ℤ) ∣ C :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp h_γ')
  have hp_dvd_C : (p : ℤ) ∣ C := dvd_trans
    (by exact_mod_cast (Nat.dvd_div_iff_mul_dvd hpN).mpr (by rwa [← sq])) h_C_dvd_Np
  have h_C_mod_p : (C : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hp_dvd_C
  have hdet : A * D - B * C = 1 := by rw [← Matrix.det_fin_two]; exact γ'.property
  have h_AD_mod_p : (A : ZMod p) * (D : ZMod p) = 1 := by
    have h := congr_arg (Int.cast : ℤ → ZMod p) hdet
    push_cast [h_C_mod_p] at h
    simpa using h
  have h_A_unit : IsUnit ((A : ZMod p)) :=
    ⟨⟨_, _, h_AD_mod_p, by rw [mul_comm]; exact h_AD_mod_p⟩, rfl⟩
  obtain ⟨m', h_moebius⟩ :=
    descend_exists_fin_isUnit_mul_eq h_A_unit ((B : ZMod p) + (m.val : ZMod p) * (D : ZMod p))
  obtain ⟨α, h_α_in_Γ0, h_GL⟩ := descend_upper_tri_target_witness hp hpN h_C_dvd_Np m m'
    (by linear_combination h_moebius + (m.val : ZMod p) * (m'.val : ZMod p) * h_C_mod_p)
  exact ⟨m', α, h_α_in_Γ0, h_moebius, h_GL⟩

/-- Defining properties of `descendExtraGamma p N` (when `p.Prime`, `p ∣ N`,
`¬ p² ∣ N`): it lies in `Γ_0(N/p)`, reduces to `[0, -1; 1, 0]` mod `p`, and to
the identity mod `N/p`. -/
lemma descendExtraGamma_spec
    {p N : ℕ} [NeZero p] [NeZero N]
    (hp : p.Prime) (hpN : p ∣ N) (hp_sq : ¬ p ^ 2 ∣ N) [NeZero (N / p)] :
    descendExtraGamma p N ∈ Gamma0 (N / p) ∧
    ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod p)
      = !![(0 : ZMod p), -1; 1, 0]) ∧
    ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.cast : ℤ → ZMod (N / p)) = 1) := by
  have h_eq : descendExtraGamma p N =
      (descendExtraGamma_exists p hp N hpN hp_sq).choose := by
    change (if h : p.Prime ∧ p ∣ N ∧ ¬ p ^ 2 ∣ N ∧ N / p ≠ 0 then
            have : NeZero (N / p) := ⟨h.2.2.2⟩
            (descendExtraGamma_exists p h.1 N h.2.1 h.2.2.1).choose
          else 1) = _
    rw [dif_pos ⟨hp, hpN, hp_sq, NeZero.ne _⟩]
  exact h_eq ▸ (descendExtraGamma_exists p hp N hpN hp_sq).choose_spec

private lemma descendCosetList_action_upper_tri_extra_unit_aux
    {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) (hp_sq : ¬ p ^ 2 ∣ N)
    [NeZero (N / p)]
    (γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h_γ' : γ' ∈ Gamma0 (N / p))
    (m : Fin p)
    (h_unit : IsUnit ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
        (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod p))) :
    ∃ (target : Fin (descendCosetCount p N))
      (α : Matrix.SpecialLinearGroup (Fin 2) ℤ)
      (_ : α ∈ Gamma0 N),
      (let A : ZMod p :=
        ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) +
        (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod p)
       (target.val < p →
         A * (target.val : ZMod p) =
           ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod p) +
           (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod p)) ∧
       (target.val = p → A = 0)) ∧
      ((Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), (m.val : ℝ); 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
        : GL (Fin 2) ℝ) * mapGL ℝ γ' =
      mapGL ℝ α * descendCosetList p N hp target) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h_C_dvd_Np : ((N / p : ℕ) : ℤ) ∣ (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp h_γ')
  obtain ⟨m', h_moebius⟩ := descend_exists_fin_isUnit_mul_eq h_unit
    (((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod p) +
      (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod p))
  obtain ⟨α, h_α_in_Γ0, h_GL⟩ :=
    descend_upper_tri_target_witness hp hpN h_C_dvd_Np m m' h_moebius
  have h_m_lt_dccn : m'.val < descendCosetCount p N := by
    have := m'.isLt; simp [descendCosetCount, hp_sq]
  refine ⟨⟨m'.val, h_m_lt_dccn⟩, α, h_α_in_Γ0,
    ⟨fun _ ↦ h_moebius, fun h_eq ↦ absurd h_eq (by show m'.val ≠ p; have := m'.isLt; omega)⟩, ?_⟩
  rwa [show descendCosetList p N hp ⟨m'.val, h_m_lt_dccn⟩ = _ from
    dif_pos (show (⟨m'.val, h_m_lt_dccn⟩ : Fin _).val < p from m'.isLt)]

private lemma descend_extra_alpha_det_eq_one (p A B C D a b c d m α01 : ℤ)
    (hdet : A * D - B * C = 1) (h_det_γp : a * d - b * c = 1)
    (hα01' : p * α01 = a * (B + m * D) - b * (A + m * C)) :
    (A * d - B * c + m * (C * d - D * c)) * (D * a - C * b) -
      α01 * (p * (C * d - D * c)) = 1 := by
  rw [show α01 * (p * (C * d - D * c)) = p * α01 * (C * d - D * c) by ring, hα01']
  nlinarith [hdet, h_det_γp, mul_comm A D, mul_comm B C, mul_comm a d, mul_comm b c]

private lemma descend_extra_target_witness
    {N : ℕ} [NeZero N] {p : ℕ} [NeZero p] (hp : p.Prime) (hpN : p ∣ N)
    {γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (h_C_dvd_Np : ((N / p : ℕ) : ℤ) ∣ (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    {γ_p : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (h_a_p : ((γ_p : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) = 0)
    (h_b_p : ((γ_p : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod p) = -1)
    (h_c_dvd_Np : ((N / p : ℕ) : ℤ) ∣ (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (m : Fin p)
    (h_A_ext_zero : ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) +
        (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod p) = 0) :
    ∃ α : Matrix.SpecialLinearGroup (Fin 2) ℤ, α ∈ Gamma0 N ∧
      (Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), (m.val : ℝ); 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
        : GL (Fin 2) ℝ) * mapGL ℝ γ' =
      mapGL ℝ α *
        ((Matrix.GeneralLinearGroup.mkOfDetNeZero
            !![(1 : ℝ), 0; 0, (p : ℝ)]
            (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
          : GL (Fin 2) ℝ) * mapGL ℝ γ_p) := by
  set Aint := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set Bint := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  set Cint := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set Dint := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  set aint := (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set bint := (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  set cint := (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set dint := (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have hdet : Aint * Dint - Bint * Cint = 1 := by rw [← Matrix.det_fin_two]; exact γ'.property
  have h_det_γp : aint * dint - bint * cint = 1 := by
    rw [← Matrix.det_fin_two]; exact γ_p.property
  obtain ⟨α01_int, hα01⟩ : (p : ℤ) ∣
      aint * (Bint + (m.val : ℤ) * Dint) - bint * (Aint + (m.val : ℤ) * Cint) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast; rw [h_a_p, h_b_p]; linear_combination h_A_ext_zero
  have hα01' : (p : ℤ) * α01_int =
      aint * (Bint + (m.val : ℤ) * Dint) - bint * (Aint + (m.val : ℤ) * Cint) := by lia
  let α_mat : Matrix (Fin 2) (Fin 2) ℤ :=
    !![Aint * dint - Bint * cint + (m.val : ℤ) * (Cint * dint - Dint * cint), α01_int;
       (p : ℤ) * (Cint * dint - Dint * cint), Dint * aint - Cint * bint]
  have h_det_α : α_mat.det = 1 := by
    rw [show α_mat.det = (Aint * dint - Bint * cint + (m.val : ℤ) * (Cint * dint - Dint * cint)) *
        (Dint * aint - Cint * bint) - α01_int * ((p : ℤ) * (Cint * dint - Dint * cint))
        from Matrix.det_fin_two_of _ _ _ _]
    exact descend_extra_alpha_det_eq_one p Aint Bint Cint Dint aint bint cint dint
      (m.val : ℤ) α01_int hdet h_det_γp hα01'
  refine ⟨⟨α_mat, h_det_α⟩,
    descend_aux_α_mat_in_Gamma0 (x := Cint * dint - Dint * cint) hpN (by simp [α_mat])
      ((h_C_dvd_Np.mul_right dint).sub (h_c_dvd_Np.mul_left Dint)), ?_⟩
  refine descend_aux_lift_int_eq_to_GL hp m.val
    (M_R := !![(1:ℤ), 0; 0, (p:ℤ)] * (γ_p : Matrix (Fin 2) (Fin 2) ℤ)) ?_ ?_
  · rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.map_mul,
      show (!![(1:ℝ), 0; 0, (p:ℝ)] : Matrix (Fin 2) (Fin 2) ℝ) =
          (!![(1:ℤ), 0; 0, (p:ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]]
    rfl
  · have h10p_γp : (!![(1 : ℤ), 0; 0, (p : ℤ)] * (γ_p : Matrix (Fin 2) (Fin 2) ℤ) :
          Matrix (Fin 2) (Fin 2) ℤ) =
        !![aint, bint; (p : ℤ) * cint, (p : ℤ) * dint] := by
      rw [show (γ_p : Matrix (Fin 2) (Fin 2) ℤ) = !![aint, bint; cint, dint] from by
        ext i j; fin_cases i <;> fin_cases j <;> rfl]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [h10p_γp, show (γ' : Matrix (Fin 2) (Fin 2) ℤ) = !![Aint, Bint; Cint, Dint] from by
      ext i j; fin_cases i <;> fin_cases j <;> rfl]
    exact descend_extra_raw_matrix_identity p Aint Bint Cint Dint
      aint bint cint dint (m.val : ℤ) α01_int h_det_γp hα01'

private lemma descendCosetList_action_upper_tri_extra_zero_aux
    {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) (hp_sq : ¬ p ^ 2 ∣ N)
    [NeZero (N / p)]
    (γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h_γ' : γ' ∈ Gamma0 (N / p))
    (m : Fin p)
    (h_A_ext_zero : ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) +
        (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod p) = 0) :
    ∃ (target : Fin (descendCosetCount p N))
      (α : Matrix.SpecialLinearGroup (Fin 2) ℤ)
      (_ : α ∈ Gamma0 N),
      (let A : ZMod p :=
        ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) +
        (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod p)
       (target.val < p →
         A * (target.val : ZMod p) =
           ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod p) +
           (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod p)) ∧
       (target.val = p → A = 0)) ∧
      ((Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), (m.val : ℝ); 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
        : GL (Fin 2) ℝ) * mapGL ℝ γ' =
      mapGL ℝ α * descendCosetList p N hp target) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h_C_dvd_Np : ((N / p : ℕ) : ℤ) ∣ (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp h_γ')
  obtain ⟨h_γ_p_mem, h_γ_p_modp, _⟩ := descendExtraGamma_spec hp hpN hp_sq
  have h_a_p : ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) = 0 := by
    simpa [Matrix.map_apply] using congr_fun (congr_fun h_γ_p_modp 0) 0
  have h_b_p : ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod p) = -1 := by
    simpa [Matrix.map_apply] using congr_fun (congr_fun h_γ_p_modp 0) 1
  have h_c_dvd_Np : ((N / p : ℕ) : ℤ) ∣ (descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp h_γ_p_mem)
  obtain ⟨α, h_α_in_Γ0, h_GL⟩ :=
    descend_extra_target_witness hp hpN h_C_dvd_Np h_a_p h_b_p h_c_dvd_Np m h_A_ext_zero
  have h_p_lt_dccn : p < descendCosetCount p N := by simp [descendCosetCount, hp_sq]
  refine ⟨⟨p, h_p_lt_dccn⟩, α, h_α_in_Γ0,
    ⟨fun h_lt ↦ (lt_irrefl _ h_lt).elim, fun _ ↦ h_A_ext_zero⟩, ?_⟩
  rwa [show descendCosetList p N hp ⟨p, h_p_lt_dccn⟩ = _ from dif_neg (lt_irrefl _)]

/-- Miyake Lemma 4.5.11 (p. 144, `p² ∤ N` case): given `γ' ∈ Γ_0(N/p)` and
`m : Fin p`, produces a target index in `Fin (descendCosetCount p N)` and
`α ∈ Γ_0(N)` with `[1, m; 0, p] · γ' = α · descendCosetList p N hp target`. The
target lies in `Fin p` when `A := a + m·c ≠ 0 mod p`, else it is the extra
coset `p`. -/
theorem descendCosetList_action_upper_tri_extra
    {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) (hp_sq : ¬ p ^ 2 ∣ N)
    [NeZero (N / p)]
    (γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h_γ' : γ' ∈ Gamma0 (N / p))
    (m : Fin p) :
    ∃ (target : Fin (descendCosetCount p N))
      (α : Matrix.SpecialLinearGroup (Fin 2) ℤ)
      (_ : α ∈ Gamma0 N),
      (let A : ZMod p :=
        ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) +
        (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod p)
       (target.val < p →
         A * (target.val : ZMod p) =
           ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod p) +
           (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod p)) ∧
       (target.val = p → A = 0)) ∧
      ((Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), (m.val : ℝ); 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
        : GL (Fin 2) ℝ) * mapGL ℝ γ' =
      mapGL ℝ α * descendCosetList p N hp target) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases Classical.em (IsUnit (((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) +
      (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod p))) with h | h
  · exact descendCosetList_action_upper_tri_extra_unit_aux p hp hpN hp_sq γ' h_γ' m h
  · exact descendCosetList_action_upper_tri_extra_zero_aux p hp hpN hp_sq γ' h_γ' m
      (by rwa [isUnit_iff_ne_zero, ne_eq, not_not] at h)

/-- Matrix identity for the upper-triangular case `γ_v = [1, m; 0, p]` with
`m < p`: for `γ' ∈ Γ_0(N/p)` there exist a target index
`target : Fin (descendCosetCount p N)` and `α ∈ Γ_0(N)` with
`[1, m; 0, p] · mapGL γ' = mapGL α · descendCosetList p N hp target`. -/
theorem descendCosetList_action_upper_tri
    {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h_γ' : γ' ∈ Gamma0 (N / p))
    (m : Fin p) :
    ∃ (target : Fin (descendCosetCount p N))
      (α : Matrix.SpecialLinearGroup (Fin 2) ℤ)
      (_ : α ∈ Gamma0 N),
      (Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), (m.val : ℝ); 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
        : GL (Fin 2) ℝ) * mapGL ℝ γ' =
      mapGL ℝ α * descendCosetList p N hp target := by
  by_cases hp_sq : p ^ 2 ∣ N
  · obtain ⟨m', α, h_mem, _h_canonical, h_eq⟩ :=
      descendCosetList_action_upper_tri_clean p hp hpN hp_sq γ' h_γ' m
    have h_count : descendCosetCount p N = p := by simp [descendCosetCount, hp_sq]
    have h_lt : m'.val < descendCosetCount p N := by lia
    refine ⟨⟨m'.val, h_lt⟩, α, h_mem, ?_⟩
    rw [h_eq]
    exact congr_arg _ (by simp [descendCosetList, m'.isLt])
  · obtain ⟨target, α, h_mem, _, h_eq⟩ :=
      descendCosetList_action_upper_tri_extra p hp hpN hp_sq γ' h_γ' m
    exact ⟨target, α, h_mem, h_eq⟩

/-- Matrix identity for the extra rep case (only `p² ∤ N`), where the extra rep
is `[1, 0; 0, p] · mapGL ℝ γ_p^(p)`: for `γ' ∈ Γ_0(N/p)` there exist a target
index in `Fin (descendCosetCount p N)` and `α ∈ Γ_0(N)` with
`(extra rep) · mapGL γ' = mapGL α · descendCosetList p N hp target`. -/
theorem descendCosetList_action_extra
    {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (hp_sq : ¬ p ^ 2 ∣ N)
    (γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h_γ' : γ' ∈ Gamma0 (N / p)) :
    let hpExtra : p < descendCosetCount p N := by
      simp [descendCosetCount, hp_sq]
    ∃ (target : Fin (descendCosetCount p N))
      (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) (_ : α ∈ Gamma0 N),
      descendCosetList p N hp ⟨p, hpExtra⟩ * mapGL ℝ γ' =
      mapGL ℝ α * descendCosetList p N hp target := by
  intro hpExtra
  obtain ⟨target, α, hα_mem, h_eq⟩ :=
    descendCosetList_action_upper_tri p hp hpN (descendExtraGamma p N * γ')
      (Subgroup.mul_mem _ (descendExtraGamma_spec hp hpN hp_sq).1 h_γ') ⟨0, hp.pos⟩
  exact ⟨target, α, hα_mem, by grind [descendCosetList]⟩

/-- Value of `descendCosetList p N hp v` on the upper-triangular branch
(`v.val < p`): the matrix `[1, v.val; 0, p]`. -/
lemma descendCosetList_apply_lt {p N : ℕ} [NeZero p] [NeZero N] (hp : p.Prime)
    {v : Fin (descendCosetCount p N)} (hv : v.val < p) :
    descendCosetList p N hp v =
      Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(1 : ℝ), (v.val : ℝ); 0, (p : ℝ)]
        (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) :=
  dif_pos hv

/-- Value of `descendCosetList p N hp v` on the extra branch (`¬ v.val < p`,
only possible when `p² ∤ N`): the product `[1, 0; 0, p] · descendExtraGamma p N`. -/
lemma descendCosetList_apply_extra {p N : ℕ} [NeZero p] [NeZero N] (hp : p.Prime)
    {v : Fin (descendCosetCount p N)} (hv : ¬ v.val < p) :
    descendCosetList p N hp v =
      Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(1 : ℝ), 0; 0, (p : ℝ)]
        (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) *
        mapGL ℝ (descendExtraGamma p N) :=
  dif_neg hv

private lemma descendCosetList_lt_matrix {p N : ℕ} [NeZero p] [NeZero N] (hp : p.Prime)
    {v : Fin (descendCosetCount p N)} (hv : v.val < p) :
    (descendCosetList p N hp v : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), (v.val : ℝ); 0, (p : ℝ)] := by
  rw [descendCosetList_apply_lt hp hv]; rfl

private lemma descendCosetCount_val_eq_p {p N : ℕ}
    (v : Fin (descendCosetCount p N)) (hv : ¬ v.val < p) : v.val = p := by
  have hlt := v.isLt
  simp only [descendCosetCount] at hlt
  split_ifs at hlt <;> lia

/-- If a `Fin (descendCosetCount p N)` index `v` falls in the extra branch
(`¬ v.val < p`), then `p² ∤ N` (the upper-triangular branch has only `p`
indices when `p² ∣ N`, so the extra index `p` is unreachable). -/
lemma not_p_sq_dvd_of_not_lt {p N : ℕ}
    {v : Fin (descendCosetCount p N)} (hv : ¬ v.val < p) : ¬ p ^ 2 ∣ N := by
  intro h
  have hlt := v.isLt
  simp only [descendCosetCount, h, ite_true] at hlt
  lia

private lemma p_lt_descendCosetCount_of_not_p_sq_dvd {p N : ℕ}
    (hp_sq : ¬ p ^ 2 ∣ N) : p < descendCosetCount p N := by
  simp [descendCosetCount, hp_sq]

private lemma isUnit_p_zmod_of_not_p_sq_dvd {p N : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : p ∣ N) (hp_sq : ¬ p ^ 2 ∣ N) :
    IsUnit (p : ZMod (N / p)) := by
  rw [ZMod.isUnit_prime_iff_not_dvd hp]
  intro h_dvd
  exact hp_sq <| (Nat.mul_div_cancel' hpN).symm ▸ pow_two p ▸ Nat.mul_dvd_mul_left _ h_dvd

private lemma descend_diamond_compat_upper_target
    {N : ℕ} [NeZero N]
    {p : ℕ} [NeZero p] (hp : p.Prime) (hpN : p ∣ N)
    {γ' β : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hβ : β ∈ Gamma0 N)
    (t : ℕ)
    (h_11 : (p : ℤ) * (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 =
        (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (t : ℤ) +
        (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * (p : ℤ)) :
    ((β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) =
      ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) := by
  obtain ⟨k, hk⟩ : (N : ℤ) ∣ (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      (by exact_mod_cast CongruenceSubgroup.Gamma0_mem.mp hβ)
  have hpNp : (p : ℤ) * ((N / p : ℕ) : ℤ) = (N : ℤ) := by exact_mod_cast Nat.mul_div_cancel' hpN
  have hβ11_sub : (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = -((N / p : ℕ) : ℤ) * k * (t : ℤ) := by
    apply mul_left_cancel₀ (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0)
    rw [hk] at h_11
    linear_combination -h_11 + k * (t : ℤ) * hpNp
  rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd, hβ11_sub]
  exact ⟨-(k * (t : ℤ)), by ring⟩

private lemma descend_diamond_compat_from_zmod
    {N p : ℕ} [NeZero p] (hp : p.Prime) (hpN : p ∣ N) (hp_sq : ¬ p ^ 2 ∣ N)
    {β γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (h_zmod : (p : ZMod (N / p)) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) =
      ((β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) * (p : ZMod (N / p))) :
    ((β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) =
      ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) :=
  ((isUnit_p_zmod_of_not_p_sq_dvd hp hpN hp_sq).mul_left_cancel
    (h_zmod.trans (mul_comm _ _))).symm

private lemma beta_10_zmod_eq_zero
    {N p : ℕ} [NeZero N] (hpN : p ∣ N)
    {β : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hβ : β ∈ Gamma0 N) :
    ((β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod (N / p)) = 0 := by
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (dvd_trans ?_
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      (by exact_mod_cast CongruenceSubgroup.Gamma0_mem.mp hβ)))
  exact_mod_cast Nat.div_dvd_of_dvd hpN

private lemma mapGL_coe_matrix_apply (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) (i j : Fin 2) :
    ((mapGL ℝ α : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      ((α : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ) := by
  simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply]

private lemma descendCosetList_extra_matrix_entry
    {p N : ℕ} [NeZero p] [NeZero N] (hp : p.Prime)
    {v : Fin (descendCosetCount p N)} (hv : ¬ v.val < p) (i j : Fin 2) :
    (descendCosetList p N hp v : Matrix (Fin 2) (Fin 2) ℝ) i j =
      (!![(1 : ℝ), 0; 0, (p : ℝ)] *
        ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ))) i j := by
  rw [descendCosetList_apply_extra hp hv]
  simp [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, mapGL, toGL, map_apply_coe]

private lemma descend_diamond_reg_lhs_reg_target
    {N : ℕ} [NeZero N] {p : ℕ} [NeZero p] (hp : p.Prime) (hpN : p ∣ N)
    {γ' β : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hβ : β ∈ Gamma0 N)
    {v t : Fin (descendCosetCount p N)} (hv : v.val < p) (ht : t.val < p)
    (h_main : descendCosetList p N hp v * mapGL ℝ γ' =
      mapGL ℝ β * descendCosetList p N hp t) :
    ((β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) =
      ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) := by
  refine descend_diamond_compat_upper_target hp hpN hβ t.val ?_
  have h_ℝ := congr_arg Units.val h_main
  rw [Units.val_mul, Units.val_mul, descendCosetList_lt_matrix hp hv,
    descendCosetList_lt_matrix hp ht] at h_ℝ
  have h_11r := congr_fun (congr_fun h_ℝ 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, mapGL_coe_matrix_apply _ 1 0,
    mapGL_coe_matrix_apply _ 1 1, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h_11r
  norm_num at h_11r
  exact_mod_cast h_11r

private lemma descend_diamond_reg_lhs_extra_target
    {N : ℕ} [NeZero N] {p : ℕ} [NeZero p] [NeZero (N / p)] (hp : p.Prime) (hpN : p ∣ N)
    (hp_sq : ¬ p ^ 2 ∣ N)
    {γ' β : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hβ : β ∈ Gamma0 N)
    {v t : Fin (descendCosetCount p N)} (hv : v.val < p) (ht : ¬ t.val < p)
    (h_main : descendCosetList p N hp v * mapGL ℝ γ' =
      mapGL ℝ β * descendCosetList p N hp t) :
    ((β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) =
      ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) := by
  refine descend_diamond_compat_from_zmod hp hpN hp_sq ?_
  set γ_p := descendExtraGamma p N
  have h_γ_p_spec := (descendExtraGamma_spec hp hpN hp_sq).2.2
  rw [descendCosetList_apply_extra hp ht] at h_main
  have h_ℝ := congr_arg Units.val h_main
  rw [Units.val_mul, Units.val_mul, descendCosetList_lt_matrix hp hv] at h_ℝ
  simp only [Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h_ℝ
  have h_11r := congr_fun (congr_fun h_ℝ 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply] at h_11r
  have h_11 : (p : ℤ) * (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 =
      (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
      (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 *
        (p * (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 1) := by
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h_11r
    exact_mod_cast h_11r
  have hγ_p_01 : ((γ_p : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod (N/p)) = 0 := by
    simpa [Matrix.map_apply] using congr_fun (congr_fun h_γ_p_spec 0) 1
  have hγ_p_11 : ((γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N/p)) = 1 := by
    simpa [Matrix.map_apply] using congr_fun (congr_fun h_γ_p_spec 1) 1
  have h_zmod := congr_arg (Int.cast : ℤ → ZMod (N/p)) h_11
  push_cast at h_zmod
  rw [hγ_p_01, hγ_p_11, beta_10_zmod_eq_zero (p := p) hpN hβ] at h_zmod
  linear_combination h_zmod

private lemma descend_diamond_extra_lhs_reg_target
    {N : ℕ} [NeZero N] {p : ℕ} [NeZero p] [NeZero (N / p)] (hp : p.Prime) (hpN : p ∣ N)
    (hp_sq : ¬ p ^ 2 ∣ N)
    {γ' β : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hβ : β ∈ Gamma0 N)
    {v t : Fin (descendCosetCount p N)} (hv : ¬ v.val < p) (ht : t.val < p)
    (h_main : descendCosetList p N hp v * mapGL ℝ γ' =
      mapGL ℝ β * descendCosetList p N hp t) :
    ((β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) =
      ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) := by
  refine descend_diamond_compat_from_zmod hp hpN hp_sq ?_
  set γ_p := descendExtraGamma p N
  have h_γ_p_spec := (descendExtraGamma_spec hp hpN hp_sq).2.2
  rw [descendCosetList_apply_extra hp hv] at h_main
  have hγ_p_10 : ((γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod (N/p)) = 0 := by
    simpa [Matrix.map_apply] using congr_fun (congr_fun h_γ_p_spec 1) 0
  have hγ_p_11 : ((γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N/p)) = 1 := by
    simpa [Matrix.map_apply] using congr_fun (congr_fun h_γ_p_spec 1) 1
  have hdcl_t11 : (descendCosetList p N hp t : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = p := by
    rw [descendCosetList_lt_matrix hp ht]; simp
  have hdcl_t01 : (descendCosetList p N hp t : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = (t.val : ℝ) := by
    rw [descendCosetList_lt_matrix hp ht]; simp
  have h_ℝ := congr_arg Units.val h_main
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h_ℝ
  have h_11r := congr_fun (congr_fun h_ℝ 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply,
    hdcl_t01, hdcl_t11, algebraMap_int_eq] at h_11r
  have h_11 : (p : ℤ) * (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 0 *
        (γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
      (p : ℤ) * (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 1 *
        (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 =
      (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * t.val +
      (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * p := by
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h_11r
    exact_mod_cast h_11r
  have h_zmod := congr_arg (Int.cast : ℤ → ZMod (N/p)) h_11
  push_cast at h_zmod
  rw [hγ_p_10, hγ_p_11, beta_10_zmod_eq_zero (p := p) hpN hβ] at h_zmod
  linear_combination h_zmod

private lemma descend_diamond_extra_lhs_extra_target
    {N : ℕ} [NeZero N] {p : ℕ} [NeZero p] [NeZero (N / p)] (hp : p.Prime) (hpN : p ∣ N)
    (hp_sq : ¬ p ^ 2 ∣ N)
    {γ' β : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hβ : β ∈ Gamma0 N)
    {v t : Fin (descendCosetCount p N)} (hv : ¬ v.val < p) (ht : ¬ t.val < p)
    (h_main : descendCosetList p N hp v * mapGL ℝ γ' =
      mapGL ℝ β * descendCosetList p N hp t) :
    ((β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) =
      ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) := by
  refine descend_diamond_compat_from_zmod hp hpN hp_sq ?_
  set γ_p := descendExtraGamma p N
  have h_γ_p_spec := (descendExtraGamma_spec hp hpN hp_sq).2.2
  rw [descendCosetList_apply_extra hp hv, descendCosetList_apply_extra hp ht] at h_main
  have hγ_p_10 : ((γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod (N/p)) = 0 := by
    simpa [Matrix.map_apply] using congr_fun (congr_fun h_γ_p_spec 1) 0
  have hγ_p_11 : ((γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N/p)) = 1 := by
    simpa [Matrix.map_apply] using congr_fun (congr_fun h_γ_p_spec 1) 1
  have hγ_p_01 : ((γ_p : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod (N/p)) = 0 := by
    simpa [Matrix.map_apply] using congr_fun (congr_fun h_γ_p_spec 0) 1
  have h_ℝ := congr_arg Units.val h_main
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h_ℝ
  have h_11r := congr_fun (congr_fun h_ℝ 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply] at h_11r
  have h_11 : (p : ℤ) * (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 0 *
        (γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
      (p : ℤ) * (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 1 *
        (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 =
      (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
      (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 *
        ((p : ℤ) * (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 1) := by
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h_11r
    exact_mod_cast h_11r
  have h_zmod := congr_arg (Int.cast : ℤ → ZMod (N/p)) h_11
  push_cast at h_zmod
  rw [hγ_p_10, hγ_p_11, beta_10_zmod_eq_zero (p := p) hpN hβ, hγ_p_01] at h_zmod
  linear_combination h_zmod

private lemma descendCosetList_per_v_witness
    {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h_γ' : γ' ∈ Gamma0 (N / p))
    (v : Fin (descendCosetCount p N)) :
    ∃ (t : Fin (descendCosetCount p N))
      (β : Matrix.SpecialLinearGroup (Fin 2) ℤ) (_ : β ∈ Gamma0 N),
      (descendCosetList p N hp v * mapGL ℝ γ' =
        mapGL ℝ β * descendCosetList p N hp t) ∧
      (((β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) =
        ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p))) := by
  by_cases hv : v.val < p
  · by_cases hp_sq : p ^ 2 ∣ N
    · obtain ⟨m', β, hβ, _, heq⟩ :=
        descendCosetList_action_upper_tri_clean p hp hpN hp_sq γ' h_γ' ⟨v.val, hv⟩
      have h_dcc_eq : descendCosetCount p N = p := by simp [descendCosetCount, hp_sq]
      have h_m'lt : m'.val < descendCosetCount p N := h_dcc_eq.symm ▸ m'.isLt
      have h_m'lt_p : (⟨m'.val, h_m'lt⟩ : Fin (descendCosetCount p N)).val < p := m'.isLt
      have h_main : descendCosetList p N hp v * mapGL ℝ γ' =
          mapGL ℝ β * descendCosetList p N hp ⟨m'.val, h_m'lt⟩ := by
        rw [descendCosetList_apply_lt hp hv, descendCosetList_apply_lt hp h_m'lt_p]; exact heq
      exact ⟨⟨m'.val, h_m'lt⟩, β, hβ, h_main,
        descend_diamond_reg_lhs_reg_target hp hpN hβ hv h_m'lt_p h_main⟩
    · obtain ⟨t, β, hβ, _, heq⟩ :=
        descendCosetList_action_upper_tri_extra p hp hpN hp_sq γ' h_γ' ⟨v.val, hv⟩
      have h_main : descendCosetList p N hp v * mapGL ℝ γ' =
          mapGL ℝ β * descendCosetList p N hp t := by
        rw [descendCosetList_apply_lt hp hv]; exact heq
      refine ⟨t, β, hβ, h_main, ?_⟩
      by_cases ht : t.val < p
      · exact descend_diamond_reg_lhs_reg_target hp hpN hβ hv ht h_main
      · exact descend_diamond_reg_lhs_extra_target hp hpN hp_sq hβ hv ht h_main
  · have hp_sq : ¬ p ^ 2 ∣ N := not_p_sq_dvd_of_not_lt hv
    obtain ⟨t, β, hβ, heq⟩ := descendCosetList_action_extra p hp hpN hp_sq γ' h_γ'
    have hv_extra : v = ⟨p, p_lt_descendCosetCount_of_not_p_sq_dvd hp_sq⟩ :=
      Fin.ext (descendCosetCount_val_eq_p v hv)
    have h_main : descendCosetList p N hp v * mapGL ℝ γ' =
        mapGL ℝ β * descendCosetList p N hp t := by rw [hv_extra]; exact heq
    refine ⟨t, β, hβ, h_main, ?_⟩
    by_cases ht : t.val < p
    · exact descend_diamond_extra_lhs_reg_target hp hpN hp_sq hβ hv ht h_main
    · exact descend_diamond_extra_lhs_extra_target hp hpN hp_sq hβ hv ht h_main

private lemma descendCosetList_cross_regular_extra_aux
    {N : ℕ} [NeZero N] (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    {va vb : Fin (descendCosetCount p N)} (hva : va.val < p) (hvb : ¬ vb.val < p)
    (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (descendCosetList p N hp va : Matrix (Fin 2) (Fin 2) ℝ) ≠
      (mapGL ℝ α : GL (Fin 2) ℝ) * descendCosetList p N hp vb := by
  intro heq_cross
  have hp_sq : ¬ p ^ 2 ∣ N := not_p_sq_dvd_of_not_lt hvb
  have hpExtra : p < descendCosetCount p N := p_lt_descendCosetCount_of_not_p_sq_dvd hp_sq
  have h_γp_00 : ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) = 0 := by
    simpa [Matrix.map_apply] using
      congr_fun (congr_fun (descendExtraGamma_spec hp hpN hp_sq).2.1 0) 0
  have hLHS_00 : (descendCosetList p N hp va : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 := by
    rw [descendCosetList_lt_matrix hp hva]; simp
  have hdcl_extra_00 : (descendCosetList p N hp ⟨p, hpExtra⟩ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 =
      ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℝ) := by
    rw [descendCosetList_extra_matrix_entry hp (lt_irrefl p) 0 0]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hdcl_extra_10 : (descendCosetList p N hp ⟨p, hpExtra⟩ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 =
      (p : ℝ) * ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) := by
    rw [descendCosetList_extra_matrix_entry hp (lt_irrefl p) 1 0]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h_vb_eq_fin : vb = ⟨p, hpExtra⟩ := Fin.ext (descendCosetCount_val_eq_p vb hvb)
  have hRHS_00 := congr_fun (congr_fun heq_cross 0) 0
  rw [hLHS_00, h_vb_eq_fin, Matrix.mul_apply, Fin.sum_univ_two,
    hdcl_extra_00, hdcl_extra_10,
    mapGL_coe_matrix_apply _ 0 0, mapGL_coe_matrix_apply _ 0 1] at hRHS_00
  have h1_int : (1 : ℤ) =
      (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 *
        (descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      (α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 *
        (p * (descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 1 0) := by
    have : (1 : ℝ) =
        ((α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℝ) *
          ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℝ) +
        ((α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℝ) *
          ((p : ℝ) * ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ)) := by linarith
    exact_mod_cast this
  have h_γp_00_dvd : (p : ℤ) ∣ (descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 0 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast h_γp_00)
  have hp_dvd_one : (p : ℤ) ∣ 1 := h1_int ▸
    dvd_add (dvd_mul_of_dvd_right h_γp_00_dvd _)
      ⟨(α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 *
        (descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 1 0, by ring⟩
  linarith [Int.le_of_dvd one_pos hp_dvd_one, show (2 : ℤ) ≤ p by exact_mod_cast hp.two_le]

private lemma descendCosetList_cross_extra_regular_aux
    {N : ℕ} [NeZero N] (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    {va vb : Fin (descendCosetCount p N)} (hva : ¬ va.val < p) (hvb : vb.val < p)
    (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (descendCosetList p N hp va : Matrix (Fin 2) (Fin 2) ℝ) ≠
      (mapGL ℝ α : GL (Fin 2) ℝ) * descendCosetList p N hp vb := by
  intro h_mat
  have hp_sq : ¬ p ^ 2 ∣ N := not_p_sq_dvd_of_not_lt hva
  have hva_extra : va = ⟨p, p_lt_descendCosetCount_of_not_p_sq_dvd hp_sq⟩ :=
    Fin.ext (descendCosetCount_val_eq_p va hva)
  have h_γp_00 : ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) = 0 := by
    simpa [Matrix.map_apply] using
      congr_fun (congr_fun (descendExtraGamma_spec hp hpN hp_sq).2.1 0) 0
  have hdcl_va_00 : (descendCosetList p N hp va : Matrix (Fin 2) (Fin 2) ℝ) 0 0 =
      ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℝ) := by
    rw [hva_extra, descendCosetList_extra_matrix_entry hp (lt_irrefl p) 0 0]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hdcl_va_10 : (descendCosetList p N hp va : Matrix (Fin 2) (Fin 2) ℝ) 1 0 =
      (p : ℝ) * ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) := by
    rw [hva_extra, descendCosetList_extra_matrix_entry hp (lt_irrefl p) 1 0]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h00 := congr_fun (congr_fun h_mat 0) 0
  have h10 := congr_fun (congr_fun h_mat 1) 0
  rw [hdcl_va_00, descendCosetList_lt_matrix hp hvb] at h00
  rw [hdcl_va_10, descendCosetList_lt_matrix hp hvb] at h10
  simp only [Matrix.mul_apply, Fin.sum_univ_two,
    mapGL_coe_matrix_apply _ 0 0, mapGL_coe_matrix_apply _ 0 1,
    mapGL_coe_matrix_apply _ 1 0, mapGL_coe_matrix_apply _ 1 1,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h10
  have hα00_eq : (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 =
      (descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
    have : (descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 0 0 =
        (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * 1 +
        (α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * 0 := by exact_mod_cast h00
    lia
  have hα10_eq : (p : ℤ) * (descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
      (α : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have h10' : (p : ℤ) * (descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
        (α : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * 1 +
        (α : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * 0 := by exact_mod_cast h10
    lia
  have hα00_dvd : (p : ℤ) ∣ (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
    rw [hα00_eq]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast h_γp_00)
  have hdet : (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact α.property
  have hp_dvd_one : (p : ℤ) ∣ 1 := hdet ▸
    dvd_sub (dvd_mul_of_dvd_left hα00_dvd _) (dvd_mul_of_dvd_right ⟨_, hα10_eq.symm⟩ _)
  linarith [Int.le_of_dvd one_pos hp_dvd_one, show (2 : ℤ) ≤ p by exact_mod_cast hp.two_le]

private lemma descendCosetList_sigma_aux_injective
    {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (α_fn : Fin (descendCosetCount p N) → Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (σ_fn : Fin (descendCosetCount p N) → Fin (descendCosetCount p N))
    (h_eq_fn : ∀ v, descendCosetList p N hp v * mapGL ℝ γ' =
      mapGL ℝ (α_fn v) * descendCosetList p N hp (σ_fn v)) :
    Function.Injective σ_fn := by
  intro v₁ v₂ h_σ
  have heq₁ := h_eq_fn v₁
  rw [h_σ] at heq₁
  have h_gl : descendCosetList p N hp v₁ =
      mapGL ℝ (α_fn v₁ * (α_fn v₂)⁻¹) * descendCosetList p N hp v₂ :=
    mul_right_cancel (b := mapGL ℝ γ') <| by
      rw [mul_assoc, h_eq_fn v₂, ← mul_assoc, ← map_mul]
      simp [heq₁]
  have h_mat : (descendCosetList p N hp v₁ : Matrix (Fin 2) (Fin 2) ℝ) =
      (mapGL ℝ (α_fn v₁ * (α_fn v₂)⁻¹) : GL (Fin 2) ℝ) *
      descendCosetList p N hp v₂ := congr_arg Units.val h_gl
  by_cases hv₁ : v₁.val < p
  · by_cases hv₂ : v₂.val < p
    · set ξ := (α_fn v₁ * (α_fn v₂)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
      rw [descendCosetList_lt_matrix hp hv₁, descendCosetList_lt_matrix hp hv₂] at h_mat
      have h00 := congr_fun (congr_fun h_mat 0) 0
      have h01 := congr_fun (congr_fun h_mat 0) 1
      simp only [Matrix.mul_apply, Fin.sum_univ_two,
        mapGL_coe_matrix_apply ξ 0 0, mapGL_coe_matrix_apply ξ 0 1,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h01
      have hcast00 : (1 : ℤ) = (ξ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * 1 +
          (ξ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * 0 := by exact_mod_cast h00
      have hcast01 : (v₁.val : ℤ) = (ξ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * v₂.val +
          (ξ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * p := by exact_mod_cast h01
      have hξ00 : (ξ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 := by lia
      rw [hξ00, one_mul] at hcast01
      have hv1z : (v₁.val : ℤ) < p := by exact_mod_cast hv₁
      have hv2z : (v₂.val : ℤ) < p := by exact_mod_cast hv₂
      have hdvd : (p : ℤ) ∣ ((v₁.val : ℤ) - v₂.val) :=
        ⟨(ξ : Matrix (Fin 2) (Fin 2) ℤ) 0 1, by linarith⟩
      have habs : |((v₁.val : ℤ) - v₂.val)| < p := abs_lt.mpr
        ⟨by linarith [Int.natCast_nonneg v₂.val],
          by linarith [Int.natCast_nonneg v₁.val]⟩
      exact Fin.ext <| by
        exact_mod_cast (sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hdvd habs))
    · exact absurd h_mat (descendCosetList_cross_regular_extra_aux p hp hpN hv₁ hv₂ _)
  · by_cases hv₂ : v₂.val < p
    · exact absurd h_mat (descendCosetList_cross_extra_regular_aux p hp hpN hv₁ hv₂ _)
    · exact Fin.ext (by
        have := descendCosetCount_val_eq_p v₁ hv₁
        have := descendCosetCount_val_eq_p v₂ hv₂
        lia)

/-- Action property of the descent cosets `Γ_0(N/p) → Γ_0(N)`: for every
`γ' ∈ Γ_0(N/p)` there exist a permutation `σ` of `Fin (descendCosetCount p N)`
and matrices `α_v ∈ Γ_0(N)` with
`descendCosetList p N hp v · mapGL γ' = mapGL (α_v) · descendCosetList p N hp (σ v)`,
together with the diamond compatibility
`ZMod.unitsMap (Gamma0MapUnits α_v) = Gamma0MapUnits γ'`. -/
theorem descendCosetList_action
    {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h_γ' : γ' ∈ Gamma0 (N / p)) :
    ∃ (σ : Equiv.Perm (Fin (descendCosetCount p N)))
      (α : Fin (descendCosetCount p N) → Matrix.SpecialLinearGroup (Fin 2) ℤ)
      (h_mem : ∀ v, α v ∈ Gamma0 N),
      (∀ v, descendCosetList p N hp v * mapGL ℝ γ' =
            mapGL ℝ (α v) * descendCosetList p N hp (σ v)) ∧
      (∀ v, ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)
          (Gamma0MapUnits (N := N) ⟨α v, h_mem v⟩) =
          Gamma0MapUnits (N := N / p) ⟨γ', h_γ'⟩) := by
  let per_v := descendCosetList_per_v_witness p hp hpN γ' h_γ'
  let σ_fn : Fin (descendCosetCount p N) → Fin (descendCosetCount p N) :=
    fun v ↦ (per_v v).choose
  let α_fn : Fin (descendCosetCount p N) → Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    fun v ↦ (per_v v).choose_spec.choose
  have h_eq_fn : ∀ v, descendCosetList p N hp v * mapGL ℝ γ' =
      mapGL ℝ (α_fn v) * descendCosetList p N hp (σ_fn v) :=
    fun v ↦ (per_v v).choose_spec.choose_spec.choose_spec.1
  have h_inj : Function.Injective σ_fn :=
    descendCosetList_sigma_aux_injective p hp hpN γ' α_fn σ_fn h_eq_fn
  refine ⟨Equiv.ofBijective σ_fn ⟨h_inj, Finite.injective_iff_surjective.mp h_inj⟩, α_fn,
    fun v ↦ (per_v v).choose_spec.choose_spec.choose, h_eq_fn, fun v ↦ ?_⟩
  apply Units.ext
  simp only [ZMod.unitsMap_val, Gamma0MapUnits_val, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [ZMod.cast_intCast (Nat.div_dvd_of_dvd hpN)]
  exact (per_v v).choose_spec.choose_spec.choose_spec.2

end HeckeRing.GL2

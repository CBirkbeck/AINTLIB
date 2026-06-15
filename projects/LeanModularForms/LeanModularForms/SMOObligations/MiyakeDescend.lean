/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.SMOObligations.DescentCosets

/-!
# Strong Multiplicity One via Miyake §4.6 — Hecke descent map

The `multipass_*` slash-sum machinery and the Hecke descent linear map
`miyake_hecke_descend` together with its q-expansion/character properties.
Part of a multi-file split of `SMOObligations.lean`.
-/

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- For `g : GL (Fin 2) ℝ` with positive determinant, `UpperHalfPlane.σ g` is the identity. -/
lemma multipass_sigma_eq_id_of_det_pos (g : GL (Fin 2) ℝ)
    (hg : 0 < g.det.val) : UpperHalfPlane.σ g = ContinuousAlgEquiv.refl ℝ ℂ := by
  simp only [UpperHalfPlane.σ, if_pos hg]

/-- For `γ ∈ Γ₁(N)`, there exists `hγ' : γ ∈ Γ₀(N)` with `Gamma0MapUnits ⟨γ, hγ'⟩ = 1`. -/
lemma multipass_char_trivial_on_Gamma1 {N : ℕ} [NeZero N]
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hγ : γ ∈ Gamma1 N) :
    ∃ hγ' : γ ∈ Gamma0 N,
      Gamma0MapUnits (N := N) ⟨γ, hγ'⟩ = 1 := by
  rw [Gamma1_mem] at hγ
  obtain ⟨_h00, h11, h10⟩ := hγ
  exact ⟨Gamma0_mem.mpr h10, by ext; simpa [Gamma0MapUnits_val, Gamma0Map] using h11⟩

/-- For `f ∈ modFormCharSpace k χ` and `α ∈ Γ₀(N)`, `f ∣[k] mapGL ℝ α = χ(α) • f`. -/
lemma multipass_modFormCharSpace_slash_apply
    {N : ℕ} [NeZero N] {k : ℤ} (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hfχ : f ∈ modFormCharSpace k χ)
    (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hα : α ∈ Gamma0 N) :
    (⇑f ∣[k] (mapGL ℝ α : GL (Fin 2) ℝ) : UpperHalfPlane → ℂ) =
      ((χ (Gamma0MapUnits ⟨α, hα⟩) : ℂ) • ⇑f) :=
  (modFormCharSpace_iff_nebentypus k χ f).mp hfχ ⟨α, hα⟩

/-- If the image of `α ∈ SL(2, ℤ)` under reduction mod `N` equals the identity, then
`α ∈ Γ_1(N)`. -/
lemma multipass_gamma1_conjugate_in_gamma1
    {N : ℕ} [NeZero N]
    (α : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (h_α_mod_N : ((α : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) = 1)) :
    α ∈ Gamma1 N := by
  rw [Gamma1_mem]
  have h : ∀ i j : Fin 2, Int.cast (α i j) = (1 : Matrix (Fin 2) (Fin 2) (ZMod N)) i j :=
    fun i j ↦ congr_fun (congr_fun h_α_mod_N i) j ▸ by simp [Matrix.map_apply]
  simp only [Matrix.one_apply] at h
  exact ⟨h 0 0, h 1 1, h 1 0⟩

/-- When `l` is coprime to prime `p`, there exists a permutation `σ` of `Fin p`
satisfying `(σ m).val = (l * m.val) % p` for all `m`. -/
lemma multipass_mul_mod_p_perm_exists {p l : ℕ} [NeZero p] (hp : p.Prime) (hpl : Nat.Coprime p l) :
    ∃ σ : Equiv.Perm (Fin p), ∀ m : Fin p, (σ m).val = (l * m.val) % p := by
  have : Fact p.Prime := ⟨hp⟩
  let f : Fin p → Fin p := fun m ↦ ⟨(l * m.val) % p, Nat.mod_lt _ hp.pos⟩
  have hl_ne : (l : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hp.coprime_iff_not_dvd.mp hpl
  have hf_inj : Function.Injective f := fun a b hab ↦ by
    have hab_val : (l * a.val) % p = (l * b.val) % p := congr_arg Fin.val hab
    have h_zmod : ((l : ZMod p) * (a.val : ZMod p)) = ((l : ZMod p) * (b.val : ZMod p)) := by
      simpa [ZMod.natCast_mod] using congr_arg (Nat.cast : ℕ → ZMod p) hab_val
    exact Fin.val_injective (by rw [← ZMod.val_natCast_of_lt a.isLt, ← ZMod.val_natCast_of_lt b.isLt,
        mul_left_cancel₀ hl_ne h_zmod])
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj), fun _ ↦ rfl⟩

/-- Reducing an integer matrix modulo a divisor: if `M ≡ 1 (mod m)` and `d ∣ m`, then
`M ≡ 1 (mod d)`. -/
private lemma matrix_intCast_map_eq_one_of_dvd {ι : Type*} [DecidableEq ι]
    {d m : ℕ} (hdm : d ∣ m) {M : Matrix ι ι ℤ}
    (hM : M.map (Int.cast : ℤ → ZMod m) = 1) :
    M.map (Int.cast : ℤ → ZMod d) = 1 := by
  have h_factor : ∀ a : ℤ, ((a : ZMod d)) =
      (ZMod.castHom hdm (ZMod d)) ((a : ZMod m)) := fun a ↦
    congr_fun (congr_arg DFunLike.coe (show (Int.castRingHom (ZMod d) : ℤ →+* ZMod d) =
      (ZMod.castHom hdm (ZMod d)).comp (Int.castRingHom (ZMod m)) from Subsingleton.elim _ _)) a
  ext i j
  have h_entry : (((M i j : ℤ) : ZMod m)) = ((1 : Matrix ι ι (ZMod m)) i j) := by
    simpa [Matrix.map_apply] using congr_fun (congr_fun hM i) j
  simp only [Matrix.map_apply]
  rw [h_factor, h_entry]
  by_cases hij : i = j
  · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]

/-- The lower-left entry `γ.val 1 0 / l` of `levelRaiseConjOfDvd l γ` is divisible by `d`
whenever the original entry is divisible by `l * d`. -/
private lemma levelRaiseConjOfDvd_lower_left_dvd
    {p N l : ℕ} [NeZero l] (hp : p.Prime) (hpN : p ∣ N) (hl : (l : ℤ) ≠ 0)
    (γ : SL(2, ℤ)) (hdvd : (l : ℤ) ∣ γ.val 1 0)
    (h : (((l * N) / p : ℕ) : ℤ) ∣ γ.val 1 0) :
    ((N / p : ℕ) : ℤ) ∣ (HeckeRing.GL2.levelRaiseConjOfDvd l γ hdvd).val 1 0 := by
  have h_lNp_eq : (l * N) / p = l * (N / p) := by
    rcases hpN with ⟨c, hc⟩
    rw [hc, show l * (p * c) = p * (l * c) by ring,
        Nat.mul_div_cancel_left _ hp.pos, Nat.mul_div_cancel_left _ hp.pos]
  have h10_eq : γ.val 1 0 =
      (l : ℤ) * (HeckeRing.GL2.levelRaiseConjOfDvd l γ hdvd).val 1 0 := by
    show _ = (l : ℤ) * (γ.val 1 0 / (l : ℤ))
    rw [mul_comm, Int.ediv_mul_cancel hdvd]
  obtain ⟨j, hj⟩ : ((l * (N / p) : ℕ) : ℤ) ∣ γ.val 1 0 :=
    (show (((l * N) / p : ℕ) : ℤ) = ((l * (N / p) : ℕ) : ℤ) by exact_mod_cast h_lNp_eq) ▸ h
  refine ⟨j, mul_left_cancel₀ hl ?_⟩
  rw [← h10_eq, hj]; push_cast; ring

/-- If `γ ≡ 1 (mod d)` and `d ∣ (γ.val 1 0 / l)`, then `levelRaiseConjOfDvd l γ ≡ 1 (mod d)`. -/
private lemma levelRaiseConjOfDvd_intCast_map_eq_one
    {d l : ℕ} [NeZero l] (γ : SL(2, ℤ)) (hdvd : (l : ℤ) ∣ γ.val 1 0)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod d) = 1)
    (h10 : (d : ℤ) ∣ (HeckeRing.GL2.levelRaiseConjOfDvd l γ hdvd).val 1 0) :
    (HeckeRing.GL2.levelRaiseConjOfDvd l γ hdvd : Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.cast : ℤ → ZMod d) = 1 := by
  ext i j
  have h00 := congr_fun (congr_fun hγ 0) 0
  have h01 := congr_fun (congr_fun hγ 0) 1
  have h11 := congr_fun (congr_fun hγ 1) 1
  simp only [Matrix.map_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)] at h00 h01 h11
  have h_val : ∀ a b : Fin 2,
      (HeckeRing.GL2.levelRaiseConjOfDvd l γ hdvd : Matrix (Fin 2) (Fin 2) ℤ) a b =
      !![γ.val 0 0, l * γ.val 0 1; γ.val 1 0 / l, γ.val 1 1] a b := fun _ _ ↦ rfl
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.map_apply, Matrix.one_apply, Fin.zero_eta, Fin.mk_one,
      h_val, ite_true, Fin.isValue]
  · exact h00
  · show (((l : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod d) = 0
    push_cast; rw [h01, mul_zero]
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h10
  · exact h11

/-- If `a ≡ 1` and `b ≡ 1 (mod d)` in `SL(2, ℤ)`, then `a * b⁻¹ ≡ 1 (mod d)`. -/
private lemma specialLinearGroup_map_intCast_mul_inv_eq_one
    {d : ℕ} (a b : SL(2, ℤ))
    (ha : (a : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod d) = 1)
    (hb : (b : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod d) = 1) :
    ((a * b⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod d) = 1 := by
  let φ : SL(2, ℤ) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod d) :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod d))
  have h_φ_def : ∀ γ : SL(2, ℤ),
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod d) = (φ γ).val := fun γ ↦ by
    ext i j; rw [map_apply_coe]; simp [RingHom.mapMatrix_apply]
  rw [h_φ_def, show φ (a * b⁻¹) = φ a * (φ b)⁻¹ from by rw [map_mul, map_inv],
    show φ a = φ b from by
      ext i j; simp only [← h_φ_def]; exact congr_fun (congr_fun (ha.trans hb.symm) i) j,
    mul_inv_cancel]
  rfl

/-- For `δ = levelRaiseConjOfDvd l γ * γ'⁻¹` with `γ, γ'` both reducing to `!![0,-1;1,0]`
modulo `p`, the entry `δ 0 1` is divisible by `p`. -/
private lemma levelRaiseConj_mul_inv_zero_one_dvd_p
    {p l : ℕ} [NeZero l] (γ γ' : SL(2, ℤ)) (hdvd : (l : ℤ) ∣ γ.val 1 0)
    (hγ_p : (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod p) = !![0, -1; 1, 0])
    (hγ'_p : (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod p) = !![0, -1; 1, 0]) :
    (p : ℤ) ∣ ((HeckeRing.GL2.levelRaiseConjOfDvd l γ hdvd * γ'⁻¹ : SL(2, ℤ))
                : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by
  set γt := HeckeRing.GL2.levelRaiseConjOfDvd l γ hdvd
  have h_γt_00 : ((γt : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) = 0 := by
    show ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) = 0
    simpa [Matrix.map_apply] using congr_fun (congr_fun hγ_p 0) 0
  have h_γt_01 : ((γt : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod p) = -(l : ZMod p) := by
    have h := congr_fun (congr_fun hγ_p 0) 1
    simp [Matrix.map_apply] at h
    show (((l : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod p) = -(l : ZMod p)
    push_cast; rw [h]; ring
  have h_inv_11 : ((γ'⁻¹).val 1 1 : ZMod p) = 0 := by
    rw [show ((γ'⁻¹).val 1 1 : ℤ) =
        ((γ' : Matrix (Fin 2) (Fin 2) ℤ).adjugate 1 1) from
      congr_fun (congr_fun (Matrix.SpecialLinearGroup.coe_inv γ') 1) 1,
      Matrix.adjugate_fin_two]
    simpa [Matrix.map_apply] using congr_fun (congr_fun hγ'_p 0) 0
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,
    show ((γt * γ'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 =
      (γt : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ'⁻¹).val 0 1 +
      (γt : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ'⁻¹).val 1 1 from by
      show (γt.val * γ'⁻¹.val) 0 1 = _
      simp [Matrix.mul_apply, Fin.sum_univ_two]]
  push_cast
  rw [h_γt_00, h_γt_01, h_inv_11]; ring

/-- The diagonal conjugation identity `D · δ = β · D` for `D = diag(1, p)`, where `β` is `δ`
with its `(0,1)` entry replaced by `k'` (with `δ 0 1 = p · k'`) and its `(1,0)` entry scaled
by `p`. -/
private lemma diag_p_mapGL_conj_eq
    {p : ℕ} (δ β : SL(2, ℤ)) (k' : ℤ)
    (hk' : (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = (p : ℤ) * k')
    (hβval : (β : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0, k';
         (p : ℤ) * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1])
    (D : GL (Fin 2) ℝ) (hD : (D : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; 0, (p : ℝ)]) :
    D * mapGL ℝ δ = mapGL ℝ β * D := by
  apply Units.ext
  simp only [Units.val_mul, mapGL_coe_matrix, map_apply_coe, RingHom.mapMatrix_apply]
  rw [hD]
  simp only [hβval]
  refine Matrix.ext fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply] <;>
    linarith [hk', mul_comm (p : ℝ) (k' : ℝ),
              show ((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℝ) = (p : ℝ) * k' by exact_mod_cast hk']

/-- Conjugating `δ ≡ 1 (mod N/p)` with `p ∣ δ 0 1` by `D = diag(1, p)` yields a matrix
`β ∈ Γ₀(N)` with trivial character and `D · δ = β · D`. -/
private lemma exists_Gamma0_conj_of_delta_mod
    {N p : ℕ} [NeZero N] (hpN : p ∣ N)
    (χ : (ZMod N)ˣ →* ℂˣ) (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    (δ : SL(2, ℤ))
    (hδ_mod_Np : (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod (N / p)) = 1)
    (hδ_01_p : (p : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1)
    (D : GL (Fin 2) ℝ) (hD : (D : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; 0, (p : ℝ)]) :
    ∃ (β : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hβ : β ∈ Gamma0 N),
      χ (Gamma0MapUnits ⟨β, hβ⟩) = 1 ∧ D * mapGL ℝ δ = mapGL ℝ β * D := by
  obtain ⟨k', hk'⟩ := hδ_01_p
  let a := (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  let c := (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  let d := (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have h_det_β : (!![a, k'; (p : ℤ) * c, d] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    have hdet : (δ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by exact_mod_cast δ.det_coe
    simp only [Matrix.det_fin_two] at hdet
    lia
  let β : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨!![a, k'; (p : ℤ) * c, d], h_det_β⟩
  have hδ_10_Np : ((N / p : ℕ) : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa [Matrix.map_apply, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
      using congr_fun (congr_fun hδ_mod_Np 1) 0
  have hβ_mem : β ∈ Gamma0 N := by
    rw [Gamma0_mem]
    show (((p : ℤ) * c : ℤ) : ZMod N) = 0
    obtain ⟨c', hc'⟩ := hδ_10_Np
    have hpNp_eq_N : ((p : ℤ)) * ((N / p : ℕ) : ℤ) = (N : ℤ) := by
      exact_mod_cast Nat.mul_div_cancel' hpN
    rw [show c = (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 from rfl, hc',
      show (p : ℤ) * (((N / p : ℕ) : ℤ) * c') = (N : ℤ) * c' by rw [← mul_assoc, hpNp_eq_N],
      Int.cast_mul]
    simp
  refine ⟨β, hβ_mem, ?_, diag_p_mapGL_conj_eq δ β k' hk' rfl D hD⟩
  have h_unitsMap_β :
      ZMod.unitsMap (Nat.div_dvd_of_dvd hpN) (Gamma0MapUnits ⟨β, hβ_mem⟩) = 1 := by
    apply Units.ext
    simp only [ZMod.unitsMap_val, Gamma0MapUnits_val, Gamma0Map, MonoidHom.coe_mk,
      OneHom.coe_mk, Units.val_one]
    rw [ZMod.cast_intCast (Nat.div_dvd_of_dvd hpN)]
    show ((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) = 1
    simpa [Matrix.map_apply, Matrix.one_apply_eq] using congr_fun (congr_fun hδ_mod_Np 1) 1
  rw [hχ_eq]
  show (χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN))) (Gamma0MapUnits ⟨β, hβ_mem⟩) = 1
  simp only [MonoidHom.comp_apply]
  rw [h_unitsMap_β, map_one]

lemma m6_2_extra_rep_levelRaise_bridge
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) (hp_sq : ¬ p ^ 2 ∣ N)
    [NeZero (N / p)]
    (l : ℕ) [NeZero l] (_hpl : Nat.Coprime p l) (_hlNp : l ∣ N / p)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ modFormCharSpace k χ)
    [NeZero (l * N)] [NeZero ((l * N) / p)] (hpN_lN : p ∣ l * N)
    (hp_sq_lN : ¬ p ^ 2 ∣ l * N)
    (hdvd_lN : (l : ℤ) ∣ (descendExtraGamma p (l * N) : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    ∀ z : UpperHalfPlane,
      ((⇑f ∣[k] (Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), 0; 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) : GL (Fin 2) ℝ)) ∣[k]
          (mapGL ℝ (HeckeRing.GL2.levelRaiseConjOfDvd l (descendExtraGamma p (l * N)) hdvd_lN)
            : GL (Fin 2) ℝ)) z =
      ((⇑f ∣[k] (Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), 0; 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) : GL (Fin 2) ℝ)) ∣[k]
          (mapGL ℝ (descendExtraGamma p N) : GL (Fin 2) ℝ)) z := by
  intro z
  set γ_lN := descendExtraGamma p (l * N)
  set γtilde : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    HeckeRing.GL2.levelRaiseConjOfDvd l γ_lN hdvd_lN
  set γ_N := descendExtraGamma p N
  have h_γ_N_spec := descendExtraGamma_spec hp hpN hp_sq
  have h_γ_lN_spec := descendExtraGamma_spec (p := p) (N := l * N) hp hpN_lN hp_sq_lN
  have h_Np_dvd_lNp : N / p ∣ (l * N) / p := by
    rcases hpN with ⟨c, hc⟩
    exact ⟨l, by rw [hc, show l * (p * c) = p * (l * c) by ring,
      Nat.mul_div_cancel_left _ hp.pos, Nat.mul_div_cancel_left _ hp.pos, mul_comm]⟩
  have h_γtilde_mod_Np :
      (γtilde : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod (N / p)) = 1 :=
    levelRaiseConjOfDvd_intCast_map_eq_one γ_lN hdvd_lN
      (matrix_intCast_map_eq_one_of_dvd h_Np_dvd_lNp h_γ_lN_spec.2.2)
      (levelRaiseConjOfDvd_lower_left_dvd hp hpN (Nat.cast_ne_zero.mpr (NeZero.ne l)) γ_lN hdvd_lN
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp h_γ_lN_spec.1)))
  set δ : Matrix.SpecialLinearGroup (Fin 2) ℤ := γtilde * γ_N⁻¹ with hδ_def
  let D : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![(1 : ℝ), 0; 0, (p : ℝ)]
      (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
  obtain ⟨β, hβ_mem, h_chi_β, hD_δ⟩ :=
    exists_Gamma0_conj_of_delta_mod hpN χ χ' hχ_eq δ
      (specialLinearGroup_map_intCast_mul_inv_eq_one γtilde γ_N h_γtilde_mod_Np h_γ_N_spec.2.2)
      (levelRaiseConj_mul_inv_zero_one_dvd_p γ_lN γ_N hdvd_lN h_γ_lN_spec.2.1 h_γ_N_spec.2.1) D rfl
  change ((⇑f ∣[k] D) ∣[k] (mapGL ℝ γtilde : GL (Fin 2) ℝ)) z =
      ((⇑f ∣[k] D) ∣[k] (mapGL ℝ γ_N : GL (Fin 2) ℝ)) z
  have h_γtilde_eq : mapGL ℝ γtilde = mapGL ℝ δ * mapGL ℝ γ_N := by simp [hδ_def]
  simp_rw [← SlashAction.slash_mul]
  rw [h_γtilde_eq, ← mul_assoc, hD_δ, mul_assoc, SlashAction.slash_mul,
    multipass_modFormCharSpace_slash_apply χ hfχ β hβ_mem]
  simp [h_chi_β]

private lemma multipass_V_p_slash_upper_aux
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) [NeZero (N / p)]
    (g_low : ModularForm ((Gamma1 (N / p)).map (mapGL ℝ)) k)
    (j : ℕ) (w : UpperHalfPlane) :
    (⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low) ∣[k]
      (Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), (j : ℝ); 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
        : GL (Fin 2) ℝ)) w = (p : ℂ)⁻¹ * g_low w := by
  have h_glMap_eq : (Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), (j : ℝ); 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
      : GL (Fin 2) ℝ) = glMap (T_p_upper p hp.pos j) := by
    refine Units.ext ?_
    ext i k'
    fin_cases i <;> fin_cases k' <;>
      simp [glMap, T_p_upper, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
        Matrix.GeneralLinearGroup.map, Matrix.map_apply]
  rw [h_glMap_eq]
  change ((⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low)) ∣[k]
      (T_p_upper p hp.pos j : GL (Fin 2) ℚ)) w = _
  rw [HeckeRing.GL2.slash_T_p_upper_eval k p hp j _ w]
  congr 1
  rw [HeckeRing.GL2.modularFormLevelRaise_apply (N / p) p k g_low,
    show (HeckeRing.GL2.levelRaiseMatrix p • (⟨(↑w + ↑j) / ↑p,
        by simpa using div_pos (by linarith [w.im_pos]) (Nat.cast_pos.mpr hp.pos)⟩
          : UpperHalfPlane)) = (j : ℝ) +ᵥ w from by
      refine UpperHalfPlane.ext ?_
      rw [HeckeRing.GL2.coe_levelRaiseMatrix_smul, UpperHalfPlane.coe_vadd]
      push_cast; field_simp [Nat.cast_ne_zero.mpr hp.ne_zero]; ring]
  apply SlashInvariantForm.vAdd_apply_of_mem_strictPeriods
  rw [show (Gamma1 (N / p)).map (mapGL ℝ) = (Gamma1 (N / p) : Subgroup (GL (Fin 2) ℝ)) from rfl,
    strictPeriods_Gamma1]
  exact ⟨(j : ℤ), by simp⟩

/-- For each `v` in the descent coset list, the slash of `V_p g_low` by the corresponding
coset matrix equals `p⁻¹ * g_low(z)` pointwise. -/
lemma multipass_V_p_slash_descendCoset
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (g_low : ModularForm ((Gamma1 (N / p)).map (mapGL ℝ)) k)
    (v : Fin (descendCosetCount p N)) (z : UpperHalfPlane) :
    (⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low) ∣[k]
      (descendCosetList p N hp v)) z = (p : ℂ)⁻¹ * g_low z := by
  unfold descendCosetList
  split_ifs with h_v
  · exact multipass_V_p_slash_upper_aux p hp g_low v.val z
  · rw [SlashAction.slash_mul]
    have h_inner_fun : ((⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low)) ∣[k]
        (Matrix.GeneralLinearGroup.mkOfDetNeZero
            !![(1 : ℝ), 0; 0, (p : ℝ)]
            (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
          : GL (Fin 2) ℝ)) = ((p : ℂ)⁻¹ • ⇑g_low : UpperHalfPlane → ℂ) := by
      ext w
      simpa using multipass_V_p_slash_upper_aux p hp g_low 0 w
    have h_γ_in_Γ1 : descendExtraGamma p N ∈ Gamma1 (N / p) := by
      rw [Gamma1_mem]
      have h_spec := (descendExtraGamma_spec hp hpN (not_p_sq_dvd_of_not_lt h_v)).2.2
      refine ⟨?_, ?_, ?_⟩
      · have h := congr_fun (congr_fun h_spec 0) 0
        simpa [Matrix.map_apply, Matrix.one_apply_eq] using h
      · have h := congr_fun (congr_fun h_spec 1) 1
        simpa [Matrix.map_apply, Matrix.one_apply_eq] using h
      · have h := congr_fun (congr_fun h_spec 1) 0
        simpa [Matrix.map_apply,
          Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] using h
    have h_g_low_inv : (⇑g_low : UpperHalfPlane → ℂ) ∣[k]
        (mapGL ℝ (descendExtraGamma p N) : GL (Fin 2) ℝ) = ⇑g_low :=
      g_low.slash_action_eq' _ ⟨descendExtraGamma p N, h_γ_in_Γ1, rfl⟩
    have h_σ : UpperHalfPlane.σ (mapGL ℝ (descendExtraGamma p N) : GL (Fin 2) ℝ) =
        ContinuousAlgEquiv.refl ℝ ℂ :=
      multipass_sigma_eq_id_of_det_pos _ (by simp)
    rw [h_inner_fun, ModularForm.smul_slash, h_σ, ContinuousAlgEquiv.refl_apply, h_g_low_inv]
    simp [Pi.smul_apply, smul_eq_mul]

/-- **H31 (audit-multipass descendCosetList_lift_eq_glMap)**: every coset
matrix `descendCosetList p N hp v : GL (Fin 2) ℝ` admits a rational lift
`A_v : GL (Fin 2) ℚ` with `glMap A_v = descendCosetList p N hp v`.

This is exactly what makes the cusp transport lemma
`glMap_smul_isCusp_Gamma1` (and the inner Hecke operators) applicable to
the descent operator: the lift's existence is the algebraic reason that
the slash sum of a cusp form again has cusp-form-like behaviour.

The lift mirrors the definition of `descendCosetList` entry-wise:
* For `v.val < p`: `[1, v.val; 0, p]` over `ℚ`.
* For the extra rep: `[1, 0; 0, p] · mapGL ℚ γ_p^(p)` over `ℚ`. -/
lemma descendCosetList_lift_eq_glMap
    {p N : ℕ} [NeZero p] [NeZero N] (hp : p.Prime)
    (v : Fin (descendCosetCount p N)) :
    ∃ A : GL (Fin 2) ℚ, glMap A = descendCosetList p N hp v := by
  unfold descendCosetList
  split_ifs with h_v
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(1 : ℚ), (v.val : ℚ); 0, (p : ℚ)]
        (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero), Units.ext ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [glMap, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, algebraMap]
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℚ), 0; 0, (p : ℚ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) *
        mapGL ℚ (descendExtraGamma p N), ?_⟩
    rw [map_mul, glMap_mapGL_eq]
    refine congrArg (· * _) (Units.ext ?_)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [glMap, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, algebraMap]

lemma miyake_descent_upper_tri_qExpansion
    {M : ℕ} [NeZero M] (p : ℕ) [NeZero p] (hp : p.Prime) (hpM : p ∣ M)
    {k : ℤ}
    (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (m : ℕ) :
    (UpperHalfPlane.qExpansion (1 : ℝ)
        (fun z ↦ ∑ v ∈ Finset.range p,
          (⇑g ∣[k] (T_p_upper p hp.pos v : GL (Fin 2) ℚ)) z)).coeff m =
      (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff (p * m) := by
  have hpM_not_coprime : ¬ Nat.Coprime p M := fun h ↦ hp.coprime_iff_not_dvd.mp h hpM
  rw [show (fun z : UpperHalfPlane ↦
      ∑ v ∈ Finset.range p,
        (⇑g ∣[k] (T_p_upper p hp.pos v : GL (Fin 2) ℚ)) z) =
      (⇑(heckeT_p_divN k p hp hpM_not_coprime g) : UpperHalfPlane → ℂ) from by
    funext z
    show ∑ v ∈ Finset.range p,
        (⇑g ∣[k] (T_p_upper p hp.pos v : GL (Fin 2) ℚ)) z =
      heckeT_p_ut k p hp.pos (⇑g) z
    rw [heckeT_p_ut, Finset.sum_apply]]
  exact qExpansion_one_heckeT_p_divN_coeff hp hpM_not_coprime g m

/-- **M5c**: The slash sum `Σ_v ⇑f ∣[k] (descendCosetList p N hp v)` of any cusp form `f`
vanishes at every cusp of `Γ_1(N/p)` (Miyake p. 158). -/
theorem miyake_hecke_descend_cusp
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (_hpN : p ∣ N) [NeZero (N / p)]
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∀ {c : OnePoint ℝ}, IsCusp c ((Gamma1 (N / p)).map (mapGL ℝ)) →
      c.IsZeroAt
        (fun z ↦ ∑ v : Fin (descendCosetCount p N),
          (⇑f ∣[k] (descendCosetList p N hp v)) z) k := by
  intro c hc
  have hc_N : IsCusp c ((Gamma1 N).map (mapGL ℝ)) :=
    (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z ((Gamma1 N).map (mapGL ℝ))).mpr
      ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z ((Gamma1 (N / p)).map (mapGL ℝ))).mp hc)
  rw [show (fun z ↦ ∑ v : Fin (descendCosetCount p N),
              (⇑f ∣[k] (descendCosetList p N hp v)) z) =
        ∑ v : Fin (descendCosetCount p N),
              (⇑f ∣[k] (descendCosetList p N hp v)) from
          funext fun z ↦ (Finset.sum_apply z _ _).symm]
  refine Finset.sum_induction _ (fun g ↦ c.IsZeroAt g k)
    (fun _ _ ha hb ↦ ha.add hb)
    ((0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k).zero_at_cusps' hc_N) fun v _ ↦ ?_
  obtain ⟨A, hA⟩ := descendCosetList_lift_eq_glMap hp v
  exact hA ▸ OnePoint.IsZeroAt.smul_iff.mp (f.zero_at_cusps' (glMap_smul_isCusp_Gamma1 N A hc_N))

/-- For `f ∈ modFormCharSpace k χ` with `χ = χ'.comp (ZMod.unitsMap h)`, slashing the coset sum
by `γ_d ∈ Γ₀(N/p)` scales it by `χ'(Gamma0MapUnits ⟨γ_d, _⟩)`. -/
theorem miyake_hecke_descend_char
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ : (ZMod N)ˣ →* ℂˣ) (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hfχ : f ∈ modFormCharSpace k χ) :
    ∀ (γ_d_pair : { γ_d : Matrix.SpecialLinearGroup (Fin 2) ℤ //
                     γ_d ∈ Gamma0 (N / p) }),
      (fun z ↦ ∑ v : Fin (descendCosetCount p N),
        (⇑f ∣[k] (descendCosetList p N hp v)) z) ∣[k]
        (mapGL ℝ γ_d_pair.val : GL (Fin 2) ℝ) =
      ((χ' (Gamma0MapUnits ⟨γ_d_pair.val, γ_d_pair.property⟩) : ℂ) •
        (fun z ↦ ∑ v : Fin (descendCosetCount p N),
          (⇑f ∣[k] (descendCosetList p N hp v)) z) : UpperHalfPlane → ℂ) := by
  intro γ_d_pair
  obtain ⟨γ_d, h_γ_d⟩ := γ_d_pair
  obtain ⟨σ, α, h_α_mem, h_action_eq, h_diamond⟩ :=
      descendCosetList_action p hp hpN γ_d h_γ_d
  have h_chi_eq : ∀ v,
      (χ (Gamma0MapUnits ⟨α v, h_α_mem v⟩) : ℂ) =
        (χ' (Gamma0MapUnits ⟨γ_d, h_γ_d⟩) : ℂ) := fun v ↦ by
    have : χ (Gamma0MapUnits ⟨α v, h_α_mem v⟩) =
        χ' (Gamma0MapUnits ⟨γ_d, h_γ_d⟩) := by
      rw [hχ_eq, MonoidHom.comp_apply, h_diamond v]
    exact_mod_cast congr_arg ((↑·) : ℂˣ → ℂ) this
  have h_det_pos : ∀ w : Fin (descendCosetCount p N),
      (0 : ℝ) < (descendCosetList p N hp w).det.val := fun w ↦ by
    rw [Matrix.GeneralLinearGroup.val_det_apply, descendCosetList_det p N hp w]
    exact_mod_cast hp.pos
  ext z
  rw [show (fun z' : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p N),
      (⇑f ∣[k] descendCosetList p N hp v) z') =
      (∑ v : Fin (descendCosetCount p N), (⇑f ∣[k] descendCosetList p N hp v)) from by
    ext z'; rw [Finset.sum_apply],
    SlashAction.sum_slash, Pi.smul_apply, Finset.sum_apply, Finset.sum_apply,
    (Equiv.sum_comp σ (fun v ↦ (⇑f ∣[k] descendCosetList p N hp v) z)).symm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [(SlashAction.slash_mul k _ _ _).symm, h_action_eq v, SlashAction.slash_mul,
      multipass_modFormCharSpace_slash_apply χ hfχ (α v) (h_α_mem v),
      ModularForm.smul_slash, multipass_sigma_eq_id_of_det_pos _ (h_det_pos (σ v)),
      ContinuousAlgEquiv.refl_apply]
  simp only [Pi.smul_apply, smul_eq_mul, h_chi_eq v]

lemma miyake_hecke_descend_Gamma1_inv
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ : (ZMod N)ˣ →* ℂˣ) (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hfχ : f ∈ modFormCharSpace k χ)
    (γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h_γ' : γ' ∈ Gamma1 (N / p)) :
    (fun z ↦ ∑ v : Fin (descendCosetCount p N),
      (⇑f ∣[k] descendCosetList p N hp v) z) ∣[k] (mapGL ℝ γ' : GL (Fin 2) ℝ) =
    fun z ↦ ∑ v : Fin (descendCosetCount p N),
      (⇑f ∣[k] descendCosetList p N hp v) z := by
  obtain ⟨h_γ'_Gamma0, h_units_one⟩ := multipass_char_trivial_on_Gamma1 γ' h_γ'
  have h_char := miyake_hecke_descend_char p hp hpN χ χ' hχ_eq hfχ ⟨γ', h_γ'_Gamma0⟩
  rw [h_units_one, map_one] at h_char
  simpa only [Units.val_one, one_smul] using h_char

end HeckeRing.GL2

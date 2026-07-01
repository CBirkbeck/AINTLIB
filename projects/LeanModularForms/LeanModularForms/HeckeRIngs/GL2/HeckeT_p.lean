/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.Gamma1Pair
import LeanModularForms.HeckeRIngs.GL2.HeckeAction

/-!
# Hecke Operator T_p on M_k(Γ₁(N))

Defines the Hecke operator `T_p` on modular forms for `Γ₁(N)` following
Diamond–Shurman §5.2, Proposition 5.2.1.

For `p` prime and `p` coprime to `N`:

  `T_p(f) = Σ_{j=0}^{p-1} f ∣[k] [[1,j],[0,p]] + (⟨p⟩ f) ∣[k] [[p,0],[0,1]]`

where `⟨p⟩` is the diamond operator for `p ∈ (ℤ/Nℤ)ˣ`.

## Main definitions

* `T_p_upper` — the coset representative `[[1,b],[0,p]]` as `GL₂(ℚ)`
* `T_p_lower` — the matrix `[[p,0],[0,1]]` as `GL₂(ℚ)`
* `heckeT_p` — `T_p` as a ℂ-linear endomorphism of `M_k(Γ₁(N))`

## Main results

* `heckeT_p_comm_diamondOp` — `T_p` commutes with `⟨d⟩`
* `heckeT_p_preserves_modFormCharSpace` — `T_p` preserves character spaces

## References

* Diamond–Shurman, *A First Course in Modular Forms*, §5.2, Proposition 5.2.1
* Miyake, *Modular Forms*, §4.5
-/

open Matrix Subgroup.Commensurable Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane Manifold

namespace HeckeRing.GL2

variable {N : ℕ}

/-- The upper triangular coset representative `[[1, b], [0, p]]` as a `GL₂(ℚ)` element.
These are the standard representatives for the double coset `Γ₁(N)\Γ₁(N)αΓ₁(N)`. -/
noncomputable def T_p_upper (p : ℕ) (hp : 0 < p) (b : ℕ) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero !![1, (b : ℚ); 0, (p : ℚ)]
    (by simpa using hp.ne')

/-- The diagonal representative `[[p, 0], [0, 1]]` as a `GL₂(ℚ)` element.
Used in the `(p+1)`-th term of `T_p` when `gcd(p, N) = 1`. -/
noncomputable def T_p_lower (p : ℕ) (hp : 0 < p) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero !![(p : ℚ), 0; 0, 1]
    (by simpa using hp.ne')

@[simp]
lemma T_p_upper_coe (p : ℕ) (hp : 0 < p) (b : ℕ) :
    (↑(T_p_upper p hp b) : Matrix (Fin 2) (Fin 2) ℚ) = !![1, (b : ℚ); 0, (p : ℚ)] := rfl

@[simp]
lemma T_p_lower_coe (p : ℕ) (hp : 0 < p) :
    (↑(T_p_lower p hp) : Matrix (Fin 2) (Fin 2) ℚ) = !![(p : ℚ), 0; 0, 1] := rfl

lemma T_p_upper_det (p : ℕ) (hp : 0 < p) (b : ℕ) :
    (↑(T_p_upper p hp b) : Matrix (Fin 2) (Fin 2) ℚ).det = p := by
  simp

lemma T_p_lower_det (p : ℕ) (hp : 0 < p) :
    (↑(T_p_lower p hp) : Matrix (Fin 2) (Fin 2) ℚ).det = p := by
  simp

lemma glMap_det_pos_of_rat_det_pos (g : GL (Fin 2) ℚ) (h : 0 < g.det.val) :
    0 < (glMap g).det.val := by
  rw [show (glMap g).det.val = algebraMap ℚ ℝ g.det.val from
    congr_arg Units.val (GeneralLinearGroup.map_det (algebraMap ℚ ℝ) g)]
  exact Rat.cast_pos.mpr h

lemma smul_slash_pos_det (k : ℤ) (c : ℂ) (φ : UpperHalfPlane → ℂ)
    (g : GL (Fin 2) ℚ) (hg : 0 < g.det.val) :
    (c • φ) ∣[k] g = c • (φ ∣[k] g) := by
  show (c • φ) ∣[k] glMap g = c • (φ ∣[k] glMap g)
  have hσ : UpperHalfPlane.σ (glMap g) = ContinuousAlgEquiv.refl ℝ ℂ := by
    unfold UpperHalfPlane.σ
    rw [if_pos (glMap_det_pos_of_rat_det_pos g hg)]
  ext z
  show ((c • φ) ∣[k] glMap g) z = (c • (φ ∣[k] glMap g)) z
  rw [ModularForm.smul_slash, hσ, ContinuousAlgEquiv.refl_apply]

lemma T_p_upper_det_pos (p : ℕ) (hp : 0 < p) (b : ℕ) :
    0 < (T_p_upper p hp b).det.val := by
  rw [GeneralLinearGroup.val_det_apply, T_p_upper_det]
  exact_mod_cast hp

lemma T_p_lower_det_pos (p : ℕ) (hp : 0 < p) :
    0 < (T_p_lower p hp).det.val := by
  rw [GeneralLinearGroup.val_det_apply, T_p_lower_det]
  exact_mod_cast hp

/-- The "upper triangular" part of `T_p`: the sum `Σ_{b=0}^{p-1} f ∣[k] [[1,b],[0,p]]`.
This is the full `T_p` when `p ∣ N`, and the first `p` terms when `p ∤ N`. -/
noncomputable def heckeT_p_ut (k : ℤ) (p : ℕ) (hp : 0 < p)
    (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  ∑ b ∈ Finset.range p, f ∣[k] (T_p_upper p hp b : GL (Fin 2) ℚ)

/-- The full Hecke operator `T_p` on `M_k(Γ₁(N))` for `p` prime coprime to `N`.
Defined as `Σ_{b=0}^{p-1} f ∣[k] [[1,b],[0,p]] + (⟨p⟩ f) ∣[k] [[p,0],[0,1]]`,
following Diamond–Shurman Proposition 5.2.1. -/
noncomputable def heckeT_p_fun [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : UpperHalfPlane → ℂ :=
  heckeT_p_ut k p hp.pos (⇑f) +
  (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
    (T_p_lower p hp.pos : GL (Fin 2) ℚ)

private lemma heckeT_p_holomorphic [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (heckeT_p_fun k p hp hpN f) :=
  (MDifferentiable.sum fun _ _ ↦ (ModularFormClass.holo f).slash k _).add
    ((ModularFormClass.holo (diamondOp k (ZMod.unitOfCoprime p hpN) f)).slash k _)

private noncomputable def moebiusFin (p : ℕ) (hp : Nat.Prime p)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (b : Fin p) : Fin p :=
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let A : ℤ := M 0 0 + ↑b.val * M 1 0
  let B : ℤ := M 0 1 + ↑b.val * M 1 1
  if (A : ZMod p) = 0 then
    ⟨((M 1 1 : ZMod p) * (M 1 0 : ZMod p)⁻¹).val, ZMod.val_lt _⟩
  else
    ⟨((B : ZMod p) * (A : ZMod p)⁻¹).val, ZMod.val_lt _⟩

private lemma intCast_zmod_eq_zero_of_mul (p : ℕ) (hp : Nat.Prime p) {a b : ℤ}
    (hab : ((a * b : ℤ) : ZMod p) = 0) (hb : ((b : ℤ) : ZMod p) ≠ 0) :
    ((a : ℤ) : ZMod p) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hab ⊢
  exact (Int.Prime.dvd_mul' hp hab).resolve_right fun h ↦
    hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mpr h)

private lemma fin_val_eq_of_intCast_sub_dvd {p : ℕ} (hp : Nat.Prime p) (x y : Fin p)
    (h : (p : ℤ) ∣ ((x.val : ℤ) - y.val)) : x.val = y.val := by
  obtain ⟨c, hc⟩ := h
  have hxp : (x.val : ℤ) < p := by exact_mod_cast x.prop
  have hyp : (y.val : ℤ) < p := by exact_mod_cast y.prop
  have hpp : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hc0 : c = 0 := by nlinarith
  subst hc0
  omega

private lemma zmod_mul_eq_of_mul_inv_eq {p : ℕ} [Fact p.Prime] [NeZero p]
    {a b c d : ZMod p} (hb : b ≠ 0) (hd : d ≠ 0)
    (h : a * b⁻¹ = c * d⁻¹) : a * d = c * b := by
  have := congr_arg (· * (b * d)) h
  simp only [mul_assoc] at this
  rwa [show b⁻¹ * (b * d) = d by rw [← mul_assoc, inv_mul_cancel₀ hb, one_mul],
       show d⁻¹ * (b * d) = b by
          rw [mul_comm b d, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]] at this

private lemma botLeft_ne_zero_of_topLeft_add_eq_zero {p : ℕ} [Fact p.Prime]
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1)
    (c : ℤ) (hAc : ((M 0 0 + c * M 1 0 : ℤ) : ZMod p) = 0) :
    ((M 1 0 : ℤ) : ZMod p) ≠ 0 := by
  intro h10
  have hdet_p : ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) = 1 := by simp [hdet]
  have h00 : ((M 0 0 : ℤ) : ZMod p) = 0 := by
    have hsum := hAc
    push_cast at hsum
    rw [h10, mul_zero, add_zero] at hsum
    exact_mod_cast hsum
  push_cast at hdet_p
  rw [h00, h10] at hdet_p
  simp at hdet_p

private lemma false_of_topLeft_zero_and_nonzero {p : ℕ} [Fact p.Prime] [NeZero p]
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1)
    (c d : ℤ) (hAc : ((M 0 0 + c * M 1 0 : ℤ) : ZMod p) = 0)
    (hAd : ((M 0 0 + d * M 1 0 : ℤ) : ZMod p) ≠ 0)
    (heq : ((M 1 1 : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p)⁻¹ =
      ((M 0 1 + d * M 1 1 : ℤ) : ZMod p) * ((M 0 0 + d * M 1 0 : ℤ) : ZMod p)⁻¹) :
    False := by
  have hdet_p : ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) = 1 := by simp [hdet]
  have hdet_d : ((M 1 1 : ℤ) : ZMod p) * ((M 0 0 + d * M 1 0 : ℤ) : ZMod p) -
      ((M 1 0 : ℤ) : ZMod p) * ((M 0 1 + d * M 1 1 : ℤ) : ZMod p) = 1 := by
    push_cast at hdet_p ⊢
    linear_combination hdet_p
  exact one_ne_zero (hdet_d.symm.trans (by
    rw [zmod_mul_eq_of_mul_inv_eq (botLeft_ne_zero_of_topLeft_add_eq_zero M hdet c hAc) hAd heq]
    ring))

private lemma moebiusFin_injective (p : ℕ) (hp : Nat.Prime p)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1) :
    Function.Injective (moebiusFin p hp M) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hdet_eq : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rwa [det_fin_two] at hdet
  have hdet_p : ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) = 1 := by simp [hdet_eq]
  intro b₁ b₂ heq
  have hv : (moebiusFin p hp M b₁).val = (moebiusFin p hp M b₂).val :=
    congr_arg Fin.val heq
  simp only [moebiusFin] at hv
  set A₁ : ZMod p := ((M 0 0 + ↑b₁.val * M 1 0 : ℤ) : ZMod p) with hA₁_def
  set A₂ : ZMod p := ((M 0 0 + ↑b₂.val * M 1 0 : ℤ) : ZMod p) with hA₂_def
  set B₁ : ZMod p := ((M 0 1 + ↑b₁.val * M 1 1 : ℤ) : ZMod p) with hB₁_def
  set B₂ : ZMod p := ((M 0 1 + ↑b₂.val * M 1 1 : ℤ) : ZMod p) with hB₂_def
  suffices hsuff : b₁.val = b₂.val by
    ext
    exact hsuff
  by_cases hA₁ : A₁ = 0 <;> by_cases hA₂ : A₂ = 0
  · have h_ring : A₁ - A₂ =
        ((↑b₁.val - ↑b₂.val : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p) := by
      simp only [hA₁_def, hA₂_def]
      push_cast
      ring
    rw [hA₁, hA₂, sub_self] at h_ring
    have hb_zero : ((↑b₁.val - ↑b₂.val : ℤ) : ZMod p) = 0 := by
      have h := h_ring.symm
      rw [← Int.cast_mul] at h
      exact intCast_zmod_eq_zero_of_mul p hp h
        (botLeft_ne_zero_of_topLeft_add_eq_zero M hdet_eq _ hA₁)
    exact fin_val_eq_of_intCast_sub_dvd hp b₁ b₂
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb_zero)
  · rw [if_pos hA₁, if_neg hA₂] at hv
    exact (false_of_topLeft_zero_and_nonzero M hdet_eq _ _ hA₁ hA₂
      (ZMod.val_injective p hv)).elim
  · rw [if_neg hA₁, if_pos hA₂] at hv
    exact (false_of_topLeft_zero_and_nonzero M hdet_eq _ _ hA₂ hA₁
      (ZMod.val_injective p hv).symm).elim
  · rw [if_neg hA₁, if_neg hA₂] at hv
    have h_cross_det : B₁ * A₂ - B₂ * A₁ =
        ((↑b₁.val - ↑b₂.val : ℤ) : ZMod p) *
        ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) := by
      simp only [hA₁_def, hA₂_def, hB₁_def, hB₂_def]
      push_cast
      ring
    have h0 : B₁ * A₂ - B₂ * A₁ = 0 := by
      rw [zmod_mul_eq_of_mul_inv_eq hA₁ hA₂ (ZMod.val_injective p hv)]
      ring
    rw [h0, hdet_p, mul_one] at h_cross_det
    exact fin_val_eq_of_intCast_sub_dvd hp b₁ b₂
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h_cross_det.symm)

private lemma sl2z_fin_two_det_eq_one (σ : SL(2, ℤ)) :
    (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
  simpa only [Matrix.det_fin_two] using σ.prop

private lemma not_dvd_topLeft_add_of_dvd_botLeft (p : ℕ) (hp : Nat.Prime p)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1)
    (h10 : (p : ℤ) ∣ M 1 0) (b : ℤ) : ¬(p : ℤ) ∣ (M 0 0 + b * M 1 0) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hdvd
  have h10' : ((M 1 0 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h10
  have h00 : ((M 0 0 : ℤ) : ZMod p) = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
    push_cast at this
    rwa [h10', mul_zero, add_zero] at this
  have hd : ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) = 1 := by simp [hdet]
  push_cast at hd
  rw [h00, h10', zero_mul, mul_zero, sub_zero] at hd
  exact zero_ne_one hd

private lemma dvd_topLeft_add_canonicalIndex (p : ℕ) (hp : Nat.Prime p)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (h10_ne : ((M 1 0 : ℤ) : ZMod p) ≠ 0) :
    (p : ℤ) ∣ (M 0 0 +
      ↑((-(M 0 0 : ZMod p) * ((M 1 0 : ℤ) : ZMod p)⁻¹).val) * M 1 0) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id]
  have : (-(M 0 0 : ZMod p) * ((M 1 0 : ℤ) : ZMod p)⁻¹) * ((M 1 0 : ℤ) : ZMod p) =
      -(M 0 0 : ZMod p) := by
    rw [mul_assoc, mul_comm ((M 1 0 : ℤ) : ZMod p)⁻¹ _, mul_inv_cancel₀ h10_ne, mul_one]
  rw [this, add_neg_cancel]

private lemma sum_ite_swap_eq {p : ℕ} {V : Type*} [AddCommGroup V]
    (g : Fin p → V) (lower' : V) (φ : Fin p → Fin p) (hφ : Function.Bijective φ)
    (b₀ : Fin p) (P : Fin p → Prop) [DecidablePred P]
    (hP : ∀ i, P i ↔ i = b₀) :
    (∑ x, if P x then lower' else g (φ x)) + g (φ b₀) = (∑ x, g x) + lower' := by
  have h_ite_eq : ∀ i : Fin p,
      (if P i then lower' else g (φ i)) =
      g (φ i) + if i = b₀ then lower' - g (φ b₀) else 0 := by
    intro i
    simp only [hP]
    split_ifs with h1
    · subst h1
      abel
    · rw [add_zero]
  simp_rw [h_ite_eq, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' Finset.univ b₀ (fun _ ↦ lower' - g (φ b₀)),
      if_pos (Finset.mem_univ _)]
  have h_bij_sum : ∑ x : Fin p, g (φ x) = ∑ x, g x :=
    Finset.sum_equiv (Equiv.ofBijective _ hφ)
      (fun _ ↦ ⟨fun _ ↦ Finset.mem_univ _, fun _ ↦ Finset.mem_univ _⟩)
      (fun _ _ ↦ rfl)
  rw [h_bij_sum]
  abel

private lemma dvd_topLeft_add_iff_eq_canonicalIndex (p : ℕ) (hp : Nat.Prime p)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1) (b₀ : Fin p)
    (hb₀ : (p : ℤ) ∣ (M 0 0 + ↑b₀.val * M 1 0)) (i : Fin p) :
    (p : ℤ) ∣ (M 0 0 + ↑i.val * M 1 0) ↔ i = b₀ := by
  refine ⟨fun hdvd ↦ moebiusFin_injective p hp M hdet ?_, fun h ↦ h ▸ hb₀⟩
  simp only [moebiusFin,
    show ((M 0 0 + ↑i.val * M 1 0 : ℤ) : ZMod p) = 0 from
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd,
    show ((M 0 0 + ↑b₀.val * M 1 0 : ℤ) : ZMod p) = 0 from
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hb₀, ↓reduceIte]

private lemma dvd_sub_mul_inv_val {p : ℕ} [Fact p.Prime] [NeZero p]
    (num den : ℤ) (hden : (den : ZMod p) ≠ 0) :
    (p : ℤ) ∣ (num - den * ↑((num : ZMod p) * (den : ZMod p)⁻¹).val) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id, sub_eq_zero, mul_comm (num : ZMod p) _, ← mul_assoc,
    mul_inv_cancel₀ hden, one_mul]

private lemma upper_tau_det_eq_one {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1) (p : ℕ) (b j' q : ℤ)
    (hq : (M 0 1 + b * M 1 1) - (M 0 0 + b * M 1 0) * j' = ↑p * q) :
    (!![M 0 0 + b * M 1 0, q; ↑p * M 1 0, M 1 1 - M 1 0 * j'] :
      Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  rw [det_fin_two_of]
  linear_combination M 1 0 * hq + hdet

private lemma upper_div_tau_det_eq_one {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1) (p : ℕ) (a b : ℤ)
    (ha : M 0 0 + b * M 1 0 = a * ↑p) :
    (!![a, M 0 1 + b * M 1 1; M 1 0, ↑p * M 1 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  rw [det_fin_two_of]
  linear_combination -M 1 1 * ha + hdet

private lemma lower_tau_det_eq_one {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1) (p : ℕ) (j' q : ℤ)
    (hq : M 1 1 - M 1 0 * j' = ↑p * q) :
    (!![↑p * M 0 0, M 0 1 - M 0 0 * j'; M 1 0, q] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  rw [det_fin_two_of]
  linear_combination -M 0 0 * hq + hdet

private lemma lower_div_tau_det_eq_one {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1) (p : ℕ) (c : ℤ)
    (hc : M 1 0 = ↑p * c) :
    (!![M 0 0, ↑p * M 0 1; c, M 1 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  rw [det_fin_two_of]
  linear_combination M 0 1 * hc + hdet

private lemma diamondOpAux_gamma1 [NeZero N] (k : ℤ)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma1 N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOpAux k ⟨σ, Gamma1_in_Gamma0 N hσ⟩ f = f := by
  have h1 : Gamma0MapUnits ⟨σ, Gamma1_in_Gamma0 N hσ⟩ = 1 := by
    ext
    simp only [Gamma0MapUnits_val, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_one]
    exact ((Gamma1_mem N σ).mp hσ).2.1
  rw [(diamondOp_eq_diamondOpAux k 1 ⟨σ, Gamma1_in_Gamma0 N hσ⟩ h1).symm,
      diamondOp_one, LinearMap.id_apply]

private lemma diamondOpAux_eq_diamondOp_mul [NeZero N] (k : ℤ) (d : (ZMod N)ˣ)
    (τ σ : ↥(Gamma0 N)) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h : Gamma0MapUnits τ = d * Gamma0MapUnits σ) :
    diamondOpAux k τ f = diamondOp k d (diamondOpAux k σ f) := by
  rw [show diamondOpAux k τ = diamondOp k (Gamma0MapUnits τ) from
        (diamondOp_eq_diamondOpAux k _ τ rfl).symm, h, diamondOp_mul, LinearMap.comp_apply,
      diamondOp_eq_diamondOpAux k _ σ rfl]

private lemma diamondOpAux_diamondOp_eq [NeZero N] (k : ℤ) (d : (ZMod N)ˣ)
    (τ σ : ↥(Gamma0 N)) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h : Gamma0MapUnits τ * d = Gamma0MapUnits σ) :
    diamondOpAux k τ (diamondOp k d f) = diamondOpAux k σ f := by
  rw [show diamondOpAux k τ = diamondOp k (Gamma0MapUnits τ) from
        (diamondOp_eq_diamondOpAux k _ τ rfl).symm,
      show diamondOp k (Gamma0MapUnits τ) (diamondOp k d f) =
        ((diamondOp k (Gamma0MapUnits τ)).comp (diamondOp k d)) f from rfl,
      ← diamondOp_mul, h, diamondOp_eq_diamondOpAux k _ σ rfl]

private lemma diamondOpAux_diamondOp_comm [NeZero N] (k : ℤ) (d : (ZMod N)ˣ)
    (τ σ : ↥(Gamma0 N)) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h : Gamma0MapUnits τ = Gamma0MapUnits σ) :
    diamondOpAux k τ (diamondOp k d f) = diamondOp k d (diamondOpAux k σ f) := by
  rw [show diamondOpAux k τ = diamondOp k (Gamma0MapUnits τ) from
        (diamondOp_eq_diamondOpAux k _ τ rfl).symm, h,
      show diamondOp k (Gamma0MapUnits σ) (diamondOp k d f) =
        ((diamondOp k (Gamma0MapUnits σ)).comp (diamondOp k d)) f from rfl,
      ← diamondOp_mul, mul_comm, diamondOp_mul, LinearMap.comp_apply,
      diamondOp_eq_diamondOpAux k _ σ rfl]

private theorem orbit_upper_gamma0 [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (_hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (b : Fin p)
    (hA : ¬(p : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      ↑b.val * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)) :
    ⇑f ∣[k] (glMap (T_p_upper p hp.pos b.val) * mapGL ℝ σ) =
    ⇑(diamondOpAux k ⟨σ, hσ⟩ f) ∣[k]
      glMap (T_p_upper p hp.pos
        (moebiusFin p hp (σ : Matrix (Fin 2) (Fin 2) ℤ) b).val) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← glMap_mapGL_eq, ← map_mul]
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ)
  rw [Gamma0_mem] at hσ
  have hA_ne : ((M 0 0 + ↑b.val * M 1 0 : ℤ) : ZMod p) ≠ 0 :=
    fun h ↦ hA ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h)
  set j' := (((M 0 1 + ↑b.val * M 1 1 : ℤ) : ZMod p) *
    ((M 0 0 + ↑b.val * M 1 0 : ℤ) : ZMod p)⁻¹).val with hj'_def
  have hmoeb : (moebiusFin p hp M b).val = j' := by
    simp only [moebiusFin]
    rw [if_neg hA_ne]
  obtain ⟨q, hq_eq⟩ :=
    dvd_sub_mul_inv_val (M 0 1 + ↑b.val * M 1 1) (M 0 0 + ↑b.val * M 1 0) hA_ne
  rw [← hj'_def] at hq_eq
  set τ_mat : Matrix (Fin 2) (Fin 2) ℤ :=
    !![M 0 0 + ↑b.val * M 1 0, q; ↑p * M 1 0, M 1 1 - M 1 0 * ↑j'] with hτ_mat_def
  set τ : SL(2, ℤ) :=
    ⟨τ_mat, upper_tau_det_eq_one (sl2z_fin_two_det_eq_one σ) p b.val j' q hq_eq⟩ with hτ_def
  have hτ_g0 : τ ∈ Gamma0 N := by
    rw [Gamma0_mem]
    show ((↑p * M 1 0 : ℤ) : ZMod N) = 0
    push_cast
    rw [hσ, mul_zero]
  have hmap : Gamma0Map N ⟨τ, hτ_g0⟩ = Gamma0Map N ⟨σ, Gamma0_mem.mpr hσ⟩ := by
    simp only [Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk]
    show ((M 1 1 - M 1 0 * ↑j' : ℤ) : ZMod N) = ((M 1 1 : ℤ) : ZMod N)
    push_cast
    rw [hσ, zero_mul, sub_zero]
  have hmatrix : T_p_upper p hp.pos b.val * mapGL ℚ σ = mapGL ℚ τ * T_p_upper p hp.pos j' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [GeneralLinearGroup.coe_mul, mul_apply, T_p_upper_coe, Fin.isValue,
        Matrix.SpecialLinearGroup.mapGL_coe_matrix, Fin.sum_univ_two, algebraMap_int_eq,
        hτ_def, hτ_mat_def] <;>
      norm_num [mapGL_coe_matrix, RingHom.mapMatrix_apply, map_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const] <;>
      simp only [show (↑σ : Matrix (Fin 2) (Fin 2) ℤ) = M from rfl] <;>
      first | rfl | simp |
        exact_mod_cast (show M 0 1 + ↑b.val * M 1 1 = (M 0 0 + ↑b.val * M 1 0) * ↑j' + q * ↑p by
          linarith [hq_eq]) | ring
  rw [hmoeb]
  conv_lhs => rw [hmatrix, map_mul, glMap_mapGL_eq, SlashAction.slash_mul]
  exact congr_arg (· ∣[k] glMap (T_p_upper p hp.pos j'))
    (slash_eq_of_Gamma0Map_eq
      (fun _ hγ ↦ SlashInvariantFormClass.slash_action_eq f _ hγ)
      ⟨τ, hτ_g0⟩ ⟨σ, Gamma0_mem.mpr hσ⟩ hmap)

private theorem orbit_upper_div_gamma0 [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (b : Fin p)
    (hA : (p : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      ↑b.val * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)) :
    ⇑f ∣[k] (glMap (T_p_upper p hp.pos b.val) * mapGL ℝ σ) =
    ⇑(diamondOp k (ZMod.unitOfCoprime p hpN)
      (diamondOpAux k ⟨σ, hσ⟩ f)) ∣[k]
      glMap (T_p_lower p hp.pos) := by
  rw [← glMap_mapGL_eq, ← map_mul]
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ)
  set A : ℤ := M 0 0 + ↑b.val * M 1 0 with hA_def
  set B : ℤ := M 0 1 + ↑b.val * M 1 1 with hB_def
  rw [Gamma0_mem] at hσ
  obtain ⟨a, ha⟩ := hA
  set τ_mat : Matrix (Fin 2) (Fin 2) ℤ := !![a, B; M 1 0, ↑p * M 1 1] with hτ_mat_def
  set τ : SL(2, ℤ) := ⟨τ_mat, upper_div_tau_det_eq_one (sl2z_fin_two_det_eq_one σ) p a b.val
    (by rw [← hA_def, ha]; ring)⟩ with hτ_def
  have hτ_g0 : τ ∈ Gamma0 N := by
    rw [Gamma0_mem]
    show ((M 1 0 : ℤ) : ZMod N) = 0
    exact hσ
  have hmap : Gamma0MapUnits ⟨τ, hτ_g0⟩ =
      ZMod.unitOfCoprime p hpN * Gamma0MapUnits ⟨σ, Gamma0_mem.mpr hσ⟩ := by
    ext
    simp only [Gamma0MapUnits_val, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk,
      ZMod.coe_unitOfCoprime, Units.val_mul]
    show ((↑p * M 1 1 : ℤ) : ZMod N) = ((p : ℕ) : ZMod N) * ((M 1 1 : ℤ) : ZMod N)
    push_cast
    ring
  have hmatrix : T_p_upper p hp.pos b.val * mapGL ℚ σ =
      mapGL ℚ τ * T_p_lower p hp.pos := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [GeneralLinearGroup.coe_mul, mul_apply, T_p_upper_coe, T_p_lower_coe, Fin.isValue,
        Matrix.SpecialLinearGroup.mapGL_coe_matrix, Fin.sum_univ_two,
        algebraMap_int_eq, hτ_def, hτ_mat_def,
        hB_def] <;>
      norm_num [mapGL_coe_matrix, RingHom.mapMatrix_apply, map_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.head_fin_const] <;>
      simp only [show (↑σ : Matrix (Fin 2) (Fin 2) ℤ) = M from rfl] <;>
      first | rfl | simp |
        (exact_mod_cast (show A = a * ↑p by linarith [ha])) |
        ring
  conv_lhs => rw [hmatrix, map_mul, glMap_mapGL_eq, SlashAction.slash_mul]
  exact congr_arg (· ∣[k] glMap (T_p_lower p hp.pos))
    (congr_arg DFunLike.coe
      (diamondOpAux_eq_diamondOp_mul k (ZMod.unitOfCoprime p hpN)
        ⟨τ, hτ_g0⟩ ⟨σ, Gamma0_mem.mpr hσ⟩ f hmap))

private theorem orbit_lower_gamma0 [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N)
    (hσ10 : ¬(p : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (b₀ : Fin p) (hb₀ : (p : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      ↑b₀.val * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)) :
    ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (glMap (T_p_lower p hp.pos) * mapGL ℝ σ) =
    ⇑(diamondOpAux k ⟨σ, hσ⟩ f) ∣[k] glMap (T_p_upper p hp.pos
        (moebiusFin p hp (σ : Matrix (Fin 2) (Fin 2) ℤ) b₀).val) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [← glMap_mapGL_eq, ← map_mul]
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ)
  rw [Gamma0_mem] at hσ
  set j' := (((M 1 1 : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p)⁻¹).val with hj'_def
  have hj'_eq : (moebiusFin p hp M b₀).val = j' := by
    dsimp only [moebiusFin]
    rw [if_pos ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hb₀)]
  rw [hj'_eq]
  obtain ⟨q, hq_eq⟩ := dvd_sub_mul_inv_val (M 1 1) (M 1 0)
    fun h ↦ hσ10 ((ZMod.intCast_zmod_eq_zero_iff_dvd (M 1 0) p).mp h)
  rw [← hj'_def] at hq_eq
  set τ_mat : Matrix (Fin 2) (Fin 2) ℤ :=
    !![↑p * M 0 0, M 0 1 - M 0 0 * ↑j'; M 1 0, q] with hτ_mat_def
  set τ : SL(2, ℤ) :=
    ⟨τ_mat, lower_tau_det_eq_one (sl2z_fin_two_det_eq_one σ) p j' q hq_eq⟩ with hτ_def
  have hτ_g0 : τ ∈ Gamma0 N := by
    rw [Gamma0_mem]
    show ((M 1 0 : ℤ) : ZMod N) = 0
    exact hσ
  have hunit_prod : Gamma0MapUnits ⟨τ, hτ_g0⟩ * ZMod.unitOfCoprime p hpN =
      Gamma0MapUnits ⟨σ, Gamma0_mem.mpr hσ⟩ := by
    ext
    simp only [Gamma0MapUnits_val, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk,
      ZMod.coe_unitOfCoprime, Units.val_mul]
    show ((q : ℤ) : ZMod N) * ((p : ℕ) : ZMod N) = ((M 1 1 : ℤ) : ZMod N)
    rw [mul_comm, ← Int.cast_natCast (R := ZMod N), ← Int.cast_mul, ← hq_eq]
    push_cast
    rw [hσ, zero_mul, sub_zero]
  have hmatrix : T_p_lower p hp.pos * mapGL ℚ σ =
      mapGL ℚ τ * T_p_upper p hp.pos j' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [GeneralLinearGroup.coe_mul, mul_apply, T_p_lower_coe, T_p_upper_coe, Fin.isValue,
        Matrix.SpecialLinearGroup.mapGL_coe_matrix, Fin.sum_univ_two,
        algebraMap_int_eq, hτ_def, hτ_mat_def] <;>
      norm_num [mapGL_coe_matrix, RingHom.mapMatrix_apply, map_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.head_fin_const] <;>
      simp only [show (↑σ : Matrix (Fin 2) (Fin 2) ℤ) = M from rfl] <;>
      first | rfl | simp |
        (exact_mod_cast (show M 1 1 = M 1 0 * ↑j' + q * ↑p by linarith [hq_eq])) |
        ring
  conv_lhs => rw [hmatrix, map_mul, glMap_mapGL_eq, SlashAction.slash_mul]
  exact congr_arg (· ∣[k] glMap (T_p_upper p hp.pos j'))
    (congr_arg DFunLike.coe
      (diamondOpAux_diamondOp_eq k (ZMod.unitOfCoprime p hpN)
        ⟨τ, hτ_g0⟩ ⟨σ, Gamma0_mem.mpr hσ⟩ f hunit_prod))

private theorem orbit_lower_div_gamma0 [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N)
    (hσ10 : (p : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      (glMap (T_p_lower p hp.pos) * mapGL ℝ σ) =
    ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) (diamondOpAux k ⟨σ, hσ⟩ f)) ∣[k]
      glMap (T_p_lower p hp.pos) := by
  rw [← glMap_mapGL_eq, ← map_mul]
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ)
  have hσ10_N : ((M 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp hσ
  obtain ⟨c, hc⟩ := hσ10
  set τ_mat : Matrix (Fin 2) (Fin 2) ℤ := !![M 0 0, ↑p * M 0 1; c, M 1 1] with hτ_mat_def
  set τ : SL(2, ℤ) :=
    ⟨τ_mat, lower_div_tau_det_eq_one (sl2z_fin_two_det_eq_one σ) p c hc⟩ with hτ_def
  have hτ_g0 : τ ∈ Gamma0 N := by
    rw [Gamma0_mem]
    show ((c : ℤ) : ZMod N) = 0
    have h1 : ((↑p * c : ℤ) : ZMod N) = 0 := by rwa [← hc]
    rw [Int.cast_mul, Int.cast_natCast] at h1
    exact (IsUnit.mul_right_eq_zero (ZMod.unitOfCoprime p hpN).isUnit).mp h1
  have hmap_u : Gamma0MapUnits ⟨τ, hτ_g0⟩ = Gamma0MapUnits ⟨σ, hσ⟩ := by
    ext
    simp only [Gamma0MapUnits_val, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk]
    show ((τ_mat 1 1 : ℤ) : ZMod N) = ((M 1 1 : ℤ) : ZMod N)
    simp [τ_mat, Matrix.cons_val_one]
  have hmatrix : T_p_lower p hp.pos * mapGL ℚ σ =
      mapGL ℚ τ * T_p_lower p hp.pos := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [GeneralLinearGroup.coe_mul, mul_apply, T_p_lower_coe, Fin.isValue,
        Matrix.SpecialLinearGroup.mapGL_coe_matrix, Fin.sum_univ_two,
        algebraMap_int_eq, hτ_def, hτ_mat_def] <;>
      norm_num [mapGL_coe_matrix, RingHom.mapMatrix_apply, map_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.head_fin_const] <;>
      simp only [show (↑σ : Matrix (Fin 2) (Fin 2) ℤ) = M from rfl] <;>
      first | rfl | simp |
        (exact_mod_cast (show M 1 0 = c * ↑p by linarith [hc])) |
        ring
  conv_lhs => rw [hmatrix, map_mul, glMap_mapGL_eq, SlashAction.slash_mul]
  exact congr_arg (· ∣[k] glMap (T_p_lower p hp.pos))
    (congr_arg DFunLike.coe
      (diamondOpAux_diamondOp_comm k (ZMod.unitOfCoprime p hpN) ⟨τ, hτ_g0⟩ ⟨σ, hσ⟩ f hmap_u))

private lemma slash_upper_eq_under_gamma1 [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma1 N) (b : Fin p)
    (hA : ¬(p : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      ↑b.val * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)) :
    (⇑f ∣[k] (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
    ⇑f ∣[k] (T_p_upper p hp.pos (moebiusFin p hp (σ : Matrix (Fin 2) (Fin 2) ℤ) b).val :
      GL (Fin 2) ℚ) := by
  change (⇑f ∣[k] glMap (T_p_upper p hp.pos b.val)) ∣[k] mapGL ℝ σ =
    ⇑f ∣[k] glMap (T_p_upper p hp.pos (moebiusFin p hp _ b).val)
  rw [← SlashAction.slash_mul,
      orbit_upper_gamma0 k p hp hpN f σ (Gamma1_in_Gamma0 N hσ) b hA,
      show ⇑(diamondOpAux k ⟨σ, Gamma1_in_Gamma0 N hσ⟩ f) = ⇑f from
        congr_arg _ (diamondOpAux_gamma1 k σ hσ f)]

private lemma slash_upper_div_eq_under_gamma1 [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma1 N) (b : Fin p)
    (hA : (p : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      ↑b.val * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)) :
    (⇑f ∣[k] (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
    ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k] (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
  change (⇑f ∣[k] glMap (T_p_upper p hp.pos b.val)) ∣[k] mapGL ℝ σ = _
  rw [← SlashAction.slash_mul,
      orbit_upper_div_gamma0 k p hp hpN f σ (Gamma1_in_Gamma0 N hσ) b hA,
      diamondOpAux_gamma1 k σ hσ f]
  rfl

private lemma slash_lower_eq_under_gamma1 [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma1 N)
    (hσ10p : ¬(p : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) (b₀ : Fin p)
    (hb₀ : (p : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      ↑b₀.val * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)) :
    (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k] (T_p_lower p hp.pos : GL (Fin 2) ℚ)) ∣[k]
      mapGL ℝ σ =
    ⇑f ∣[k] (T_p_upper p hp.pos (moebiusFin p hp (σ : Matrix (Fin 2) (Fin 2) ℤ) b₀).val :
      GL (Fin 2) ℚ) := by
  change (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
    glMap (T_p_lower p hp.pos)) ∣[k] mapGL ℝ σ = _
  rw [← SlashAction.slash_mul,
      orbit_lower_gamma0 k p hp hpN f σ (Gamma1_in_Gamma0 N hσ) hσ10p b₀ hb₀,
      show ⇑(diamondOpAux k ⟨σ, Gamma1_in_Gamma0 N hσ⟩ f) = ⇑f from
        congr_arg _ (diamondOpAux_gamma1 k σ hσ f)]
  rfl

private lemma slash_upper_eq_under_gamma0 [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (b : Fin p)
    (hA : ¬(p : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      ↑b.val * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)) :
    (⇑f ∣[k] (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
    ⇑(diamondOpAux k ⟨σ, hσ⟩ f) ∣[k]
      (T_p_upper p hp.pos (moebiusFin p hp (σ : Matrix (Fin 2) (Fin 2) ℤ) b).val :
        GL (Fin 2) ℚ) := by
  change (⇑f ∣[k] glMap (T_p_upper p hp.pos b.val)) ∣[k] mapGL ℝ σ = _
  rw [← SlashAction.slash_mul]
  exact orbit_upper_gamma0 k p hp hpN f σ hσ b hA

private lemma slash_upper_div_eq_under_gamma0 [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (b : Fin p)
    (hA : (p : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      ↑b.val * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)) :
    (⇑f ∣[k] (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
    ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) (diamondOpAux k ⟨σ, hσ⟩ f)) ∣[k]
      (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
  change (⇑f ∣[k] glMap (T_p_upper p hp.pos b.val)) ∣[k] mapGL ℝ σ = _
  rw [← SlashAction.slash_mul]
  exact orbit_upper_div_gamma0 k p hp hpN f σ hσ b hA

private lemma slash_lower_eq_under_gamma0 [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N)
    (hσ10p : ¬(p : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) (b₀ : Fin p)
    (hb₀ : (p : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      ↑b₀.val * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)) :
    (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k] (T_p_lower p hp.pos : GL (Fin 2) ℚ)) ∣[k]
      mapGL ℝ σ =
    ⇑(diamondOpAux k ⟨σ, hσ⟩ f) ∣[k]
      (T_p_upper p hp.pos (moebiusFin p hp (σ : Matrix (Fin 2) (Fin 2) ℤ) b₀).val :
        GL (Fin 2) ℚ) := by
  change (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
    glMap (T_p_lower p hp.pos)) ∣[k] mapGL ℝ σ = _
  rw [← SlashAction.slash_mul]
  exact orbit_lower_gamma0 k p hp hpN f σ hσ hσ10p b₀ hb₀

private theorem heckeT_p_slash_invariant_case1 [NeZero N] (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma1 N)
    (hσ10p : (p : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    (∑ b ∈ Finset.range p, (⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
        mapGL ℝ σ) +
      ((⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ) =
    (∑ b ∈ Finset.range p, ⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) +
      ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ)
  have hdet_M : M.det = 1 := by exact_mod_cast σ.prop
  have h_lower : (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      (T_p_lower p hp.pos : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
    ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
    change (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      glMap (T_p_lower p hp.pos)) ∣[k] mapGL ℝ σ = _
    rw [← SlashAction.slash_mul,
        orbit_lower_div_gamma0 k p hp hpN f σ (Gamma1_in_Gamma0 N hσ) hσ10p,
        diamondOpAux_gamma1 k σ hσ f]
    rfl
  rw [h_lower]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_equiv (Equiv.ofBijective _
    (Finite.injective_iff_bijective.mp (moebiusFin_injective p hp M hdet_M)))
    (fun _ ↦ ⟨fun _ ↦ Finset.mem_univ _, fun _ ↦ Finset.mem_univ _⟩)
    (fun b _ ↦ slash_upper_eq_under_gamma1 k p hp hpN f σ hσ b
      (not_dvd_topLeft_add_of_dvd_botLeft p hp M (sl2z_fin_two_det_eq_one σ) hσ10p _))

private theorem heckeT_p_slash_invariant_case2 [NeZero N] (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma1 N)
    (hσ10p : ¬(p : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    (∑ b ∈ Finset.range p, (⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
        mapGL ℝ σ) +
      ((⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ) =
    (∑ b ∈ Finset.range p, ⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) +
      ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ)
  have hdet_M : M.det = 1 := by exact_mod_cast σ.prop
  set b₀ : Fin p := ⟨(-(M 0 0 : ZMod p) * (M 1 0 : ZMod p)⁻¹).val, ZMod.val_lt _⟩
  have hb₀_dvd : (p : ℤ) ∣ (M 0 0 + ↑b₀.val * M 1 0) :=
    dvd_topLeft_add_canonicalIndex p hp M
      fun h ↦ hσ10p ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  have h_all : ∀ b : Fin p,
      (⇑f ∣[k] (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
      if (p : ℤ) ∣ (M 0 0 + ↑b.val * M 1 0)
      then ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ)
      else ⇑f ∣[k] (T_p_upper p hp.pos (moebiusFin p hp M b).val : GL (Fin 2) ℚ) := by
    intro b
    split_ifs with h
    · exact slash_upper_div_eq_under_gamma1 k p hp hpN f σ hσ b h
    · exact slash_upper_eq_under_gamma1 k p hp hpN f σ hσ b h
  simp_rw [h_all]
  rw [slash_lower_eq_under_gamma1 k p hp hpN f σ hσ hσ10p b₀ hb₀_dvd]
  set g : Fin p → UpperHalfPlane → ℂ :=
    fun i ↦ ⇑f ∣[k] (T_p_upper p hp.pos i.val : GL (Fin 2) ℚ)
  set lower' := ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
    (T_p_lower p hp.pos : GL (Fin 2) ℚ)
  show (∑ x, if (p : ℤ) ∣ (M 0 0 + ↑x.val * M 1 0) then lower'
        else g (moebiusFin p hp M x)) + g (moebiusFin p hp M b₀) =
      Finset.univ.sum g + lower'
  exact sum_ite_swap_eq g lower' (moebiusFin p hp M)
    (Finite.injective_iff_bijective.mp (moebiusFin_injective p hp M hdet_M)) b₀ _
    (dvd_topLeft_add_iff_eq_canonicalIndex p hp M hdet_M b₀ hb₀_dvd)

private theorem heckeT_p_slash_invariant [NeZero N] (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ (Gamma1 N).map (mapGL ℝ)) :
    (heckeT_p_fun k p hp hpN f) ∣[k] γ = heckeT_p_fun k p hp hpN f := by
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hγ
  simp only [heckeT_p_fun, heckeT_p_ut]
  rw [SlashAction.add_slash, SlashAction.sum_slash]
  by_cases hσ10p : (p : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  · exact heckeT_p_slash_invariant_case1 k p hp hpN f σ hσ hσ10p
  · exact heckeT_p_slash_invariant_case2 k p hp hpN f σ hσ hσ10p

private theorem orbit_sum_comm_case1 [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (g : ↥(Gamma0 N))
    (hσ10p : (p : ℤ) ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    (∑ b ∈ Finset.range p, (⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
        mapGL ℝ (g : SL(2, ℤ))) +
      ((⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ (g : SL(2, ℤ))) =
    (∑ b ∈ Finset.range p,
        ⇑(diamondOpAux k g f) ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) +
      ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) (diamondOpAux k g f)) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
  set σ := (g : SL(2, ℤ))
  have hσ : σ ∈ Gamma0 N := g.property
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ)
  have hdet_M : M.det = 1 := by exact_mod_cast σ.prop
  have h_coe : (⇑(diamondOpAux k g f) : UpperHalfPlane → ℂ) = ⇑f ∣[k] mapGL ℝ σ := rfl
  have h_upper : ∀ b : Fin p,
      (⇑f ∣[k] (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
      (⇑f ∣[k] mapGL ℝ σ) ∣[k]
      (T_p_upper p hp.pos (moebiusFin p hp M b).val :
        GL (Fin 2) ℚ) := by
    intro b
    change (⇑f ∣[k] glMap (T_p_upper p hp.pos b.val)) ∣[k] mapGL ℝ σ =
      (⇑f ∣[k] mapGL ℝ σ) ∣[k] glMap (T_p_upper p hp.pos (moebiusFin p hp M b).val)
    rw [← SlashAction.slash_mul]
    have := orbit_upper_gamma0 k p hp hpN f σ hσ b
      (not_dvd_topLeft_add_of_dvd_botLeft p hp M (sl2z_fin_two_det_eq_one σ) hσ10p _)
    rw [h_coe] at this
    exact this
  have h_lower : (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      (T_p_lower p hp.pos : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
    ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) (diamondOpAux k g f)) ∣[k]
      (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
    change (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      glMap (T_p_lower p hp.pos)) ∣[k] mapGL ℝ σ = _
    rw [← SlashAction.slash_mul]
    exact orbit_lower_div_gamma0 k p hp hpN f σ hσ hσ10p
  rw [h_lower]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  rw [h_coe]
  exact Finset.sum_equiv (Equiv.ofBijective _
    (Finite.injective_iff_bijective.mp (moebiusFin_injective p hp M hdet_M)))
    (fun _ ↦ ⟨fun _ ↦ Finset.mem_univ _, fun _ ↦ Finset.mem_univ _⟩)
    (fun b _ ↦ h_upper b)

private theorem orbit_sum_comm_case2 [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (g : ↥(Gamma0 N))
    (hσ10p : ¬(p : ℤ) ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    (∑ b ∈ Finset.range p, (⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
        mapGL ℝ (g : SL(2, ℤ))) +
      ((⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ (g : SL(2, ℤ))) =
    (∑ b ∈ Finset.range p,
        ⇑(diamondOpAux k g f) ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) +
      ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) (diamondOpAux k g f)) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
  set σ := (g : SL(2, ℤ))
  have hσ : σ ∈ Gamma0 N := g.property
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ)
  have hdet_M : M.det = 1 := by exact_mod_cast σ.prop
  set b₀ : Fin p := ⟨(-(M 0 0 : ZMod p) * (M 1 0 : ZMod p)⁻¹).val, ZMod.val_lt _⟩
  have hb₀_dvd : (p : ℤ) ∣ (M 0 0 + ↑b₀.val * M 1 0) :=
    dvd_topLeft_add_canonicalIndex p hp M
      fun h ↦ hσ10p ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  have h_all : ∀ b : Fin p,
      (⇑f ∣[k] (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
      if (p : ℤ) ∣ (M 0 0 + ↑b.val * M 1 0)
      then ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) (diamondOpAux k ⟨σ, hσ⟩ f)) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ)
      else ⇑(diamondOpAux k ⟨σ, hσ⟩ f) ∣[k]
        (T_p_upper p hp.pos (moebiusFin p hp M b).val : GL (Fin 2) ℚ) := by
    intro b
    split_ifs with h
    · exact slash_upper_div_eq_under_gamma0 k p hp hpN f σ hσ b h
    · exact slash_upper_eq_under_gamma0 k p hp hpN f σ hσ b h
  simp_rw [h_all]
  rw [slash_lower_eq_under_gamma0 k p hp hpN f σ hσ hσ10p b₀ hb₀_dvd]
  set g' : Fin p → UpperHalfPlane → ℂ :=
    fun i ↦ ⇑(diamondOpAux k ⟨σ, hσ⟩ f) ∣[k] (T_p_upper p hp.pos i.val : GL (Fin 2) ℚ)
  set lower' := ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) (diamondOpAux k ⟨σ, hσ⟩ f)) ∣[k]
    (T_p_lower p hp.pos : GL (Fin 2) ℚ)
  show (∑ x, if (p : ℤ) ∣ (M 0 0 + ↑x.val * M 1 0) then lower'
        else g' (moebiusFin p hp M x)) + g' (moebiusFin p hp M b₀) =
      Finset.univ.sum g' + lower'
  exact sum_ite_swap_eq g' lower' (moebiusFin p hp M)
    (Finite.injective_iff_bijective.mp (moebiusFin_injective p hp M hdet_M)) b₀ _
    (dvd_topLeft_add_iff_eq_canonicalIndex p hp M hdet_M b₀ hb₀_dvd)

private theorem orbit_sum_comm [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (g : ↥(Gamma0 N)) :
    heckeT_p_fun k p hp hpN f ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
    heckeT_p_fun k p hp hpN (diamondOpAux k g f) := by
  simp only [heckeT_p_fun, heckeT_p_ut]
  rw [SlashAction.add_slash, SlashAction.sum_slash]
  by_cases hσ10p : (p : ℤ) ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  · exact orbit_sum_comm_case1 k p hp hpN f g hσ10p
  · exact orbit_sum_comm_case2 k p hp hpN f g hσ10p

private lemma Gamma1_isCusp_glMap_smul [NeZero N] (A : GL (Fin 2) ℚ) {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    IsCusp (glMap A • c) ((Gamma1 N).map (mapGL ℝ)) := by
  have hc_SL : IsCusp c ((⊤ : Subgroup SL(2, ℤ)).map (mapGL ℝ)) :=
    hc.mono (Subgroup.map_mono le_top)
  rw [← MonoidHom.range_eq_map] at hc_SL
  have hsmul_SL : IsCusp (glMap A • c) (mapGL ℝ : SL(2, ℤ) →* _).range := by
    rw [isCusp_SL2Z_iff] at hc_SL ⊢
    obtain ⟨q, rfl⟩ := hc_SL
    refine ⟨A • q, ?_⟩
    show OnePoint.map (algebraMap ℚ ℝ) (A • q) =
      glMap A • OnePoint.map (algebraMap ℚ ℝ) q
    simp [OnePoint.map_smul, glMap]
  rw [MonoidHom.range_eq_map] at hsmul_SL
  haveI : ((Gamma1 N).map (mapGL ℝ)).IsFiniteRelIndex
      ((⊤ : Subgroup SL(2, ℤ)).map (mapGL ℝ)) := ⟨by
    rw [Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective,
        Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero⟩
  exact hsmul_SL.of_isFiniteRelIndex

private theorem heckeT_p_bdd_at_cusps [NeZero N] (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    {c : OnePoint ℝ} (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    c.IsBoundedAt (heckeT_p_fun k p hp hpN f) k := by
  simp only [heckeT_p_fun, heckeT_p_ut]
  apply OnePoint.IsBoundedAt.add
  · apply Finset.sum_induction _ (fun g ↦ c.IsBoundedAt g k)
      (fun _ _ ha hb ↦ ha.add hb)
      ((0 : ModularForm ((Gamma1 N).map (mapGL ℝ)) k).bdd_at_cusps' hc)
    intro b _
    exact OnePoint.IsBoundedAt.smul_iff.mp
      (f.bdd_at_cusps' (Gamma1_isCusp_glMap_smul _ hc))
  · exact OnePoint.IsBoundedAt.smul_iff.mp
      ((diamondOp k (ZMod.unitOfCoprime p hpN) f).bdd_at_cusps'
        (Gamma1_isCusp_glMap_smul _ hc))

/-- **The Hecke operator `T_p` on `M_k(Γ₁(N))`** for `p` prime coprime to `N`.
Following Diamond–Shurman Proposition 5.2.1:
`T_p(f) = Σ_{b=0}^{p-1} f ∣[k] [[1,b],[0,p]] + (⟨p⟩ f) ∣[k] [[p,0],[0,1]]`. -/
noncomputable def heckeT_p [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    { toSlashInvariantForm :=
      { toFun := heckeT_p_fun k p hp hpN f
        slash_action_eq' γ hγ := heckeT_p_slash_invariant k p hp hpN f γ hγ }
      holo' := heckeT_p_holomorphic k p hp hpN f
      bdd_at_cusps' hc := heckeT_p_bdd_at_cusps k p hp hpN f hc }
  map_add' f g := by
    ext z
    simp only [ModularForm.add_apply]
    show heckeT_p_fun k p hp hpN (f + g) z =
      heckeT_p_fun k p hp hpN f z + heckeT_p_fun k p hp hpN g z
    simp only [heckeT_p_fun, heckeT_p_ut, Pi.add_apply]
    rw [show (⇑(f + g) : UpperHalfPlane → ℂ) = ⇑f + ⇑g from rfl,
      show diamondOp k (ZMod.unitOfCoprime p hpN) (f + g) =
        diamondOp k (ZMod.unitOfCoprime p hpN) f +
        diamondOp k (ZMod.unitOfCoprime p hpN) g from map_add _ f g,
      show (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f +
        diamondOp k (ZMod.unitOfCoprime p hpN) g) : UpperHalfPlane → ℂ) =
        ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) +
        ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) g) from rfl]
    simp only [SlashAction.add_slash, Finset.sum_add_distrib, Pi.add_apply,
      Finset.sum_apply]
    ring
  map_smul' c f := by
    ext z
    simp only [RingHom.id_apply]
    show heckeT_p_fun k p hp hpN (c • f) z = c * heckeT_p_fun k p hp hpN f z
    simp only [heckeT_p_fun, heckeT_p_ut, Pi.add_apply]
    rw [show (⇑(c • f) : UpperHalfPlane → ℂ) = c • ⇑f from rfl,
      show diamondOp k (ZMod.unitOfCoprime p hpN) (c • f) =
        c • diamondOp k (ZMod.unitOfCoprime p hpN) f from map_smul _ c f,
      show (⇑(c • diamondOp k (ZMod.unitOfCoprime p hpN) f) : UpperHalfPlane → ℂ) =
        c • ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) from rfl]
    simp_rw [smul_slash_pos_det k c _ _ (T_p_upper_det_pos p hp.pos _)]
    rw [smul_slash_pos_det k c _ _ (T_p_lower_det_pos p hp.pos)]
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, Finset.sum_apply]
    ring

/-- `T_p` commutes with the diamond operators: `⟨d⟩ ∘ T_p = T_p ∘ ⟨d⟩`. -/
theorem heckeT_p_comm_diamondOp [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (d : (ZMod N)ˣ) :
    (diamondOp k d).comp (heckeT_p k p hp hpN) =
    (heckeT_p k p hp hpN).comp (diamondOp k d) := by
  obtain ⟨g, hg⟩ := Gamma0MapUnits_surjective (N := N) d
  ext f z
  change (diamondOp k d (heckeT_p k p hp hpN f)) z =
    (heckeT_p k p hp hpN (diamondOp k d f)) z
  rw [diamondOp_eq_diamondOpAux k d g hg]
  exact congr_fun (orbit_sum_comm k p hp hpN f g) z

end HeckeRing.GL2

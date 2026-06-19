/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p

/-!
# Hecke operators T_n for general n on M_k(Γ₁(N))

Defines the Hecke operator `T_n` for all positive integers `n`, building on
the prime operator `T_p` from `GL2/HeckeT_p.lean`.

## Main definitions

* `diamondOp_n` — extended diamond: `⟨p⟩` when `(p,N)=1`, zero when `p∣N`
* `heckeT_p_all` — `T_p` for all primes (coprime and dividing `N`)
* `heckeT_ppow` — `T_{p^r}` via the recurrence
    `T_{p^{r+2}} = T_p T_{p^{r+1}} - p^{k-1} ⟨p⟩ T_{p^r}`
* `heckeT_n` — `T_n` for general `n`, assembled from prime-power components

## Main results

* `heckeT_ppow_succ_succ` — the prime-power recurrence (definitional)
* `heckeT_ppow_eq_pow_of_not_coprime` — `T_{p^r} = T_p^r` when `p ∣ N`
* `heckeT_n_one` — `T_1 = id`
* `heckeT_n_mul_coprime` — `T_{mn} = T_m T_n` when `(m,n) = 1`
* `heckeT_n_comm` — `T_m T_n = T_n T_m`
* `heckeT_n_preserves_charSpace` — `T_n` preserves `M_k(N, χ)`

## Implementation notes

Mathlib's slash action includes `|det|^{k-1}`, matching Diamond–Shurman.
The recurrence scalar `p^{k-1}` in `heckeT_ppow` arises from the abstract Hecke
ring identity `T(p²) = T(p)² - p · T(p,p)` where `T(p,p)` acts by `p^{k-2}`
on weight-k forms (since `|det(diag(p,p))|^{k-1} · (cz+d)^{-k} = p^{k-2}`),
giving `p · T(p,p) → p^{k-1} · ⟨p⟩` (DS (5.10), Shimura Thm 3.24(6)).

When `p ∣ N` the diamond operator `⟨p⟩ = 0`, so the recurrence simplifies to
`T_{p^r} = T_p^r`.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.2–5.3
* [Miy] Miyake, *Modular Forms*, §4.5
-/

open Matrix Subgroup.Commensurable Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane Manifold

noncomputable section

namespace HeckeRing.GL2

variable {N : ℕ}

/-- Extended diamond operator for general `n ∈ ℕ`:
equals `diamondOp k (n mod N)ˣ` when `(n, N) = 1`, zero otherwise.
This is `⟨n⟩` in Diamond–Shurman §5.3.  At a prime argument it provides the
uniform extension used in the `T_{p^r}` recurrence (vanishing when `p ∣ N`). -/
def diamondOp_n [NeZero N] (k : ℤ) (n : ℕ) :
    Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  if h : Nat.Coprime n N then diamondOp k (ZMod.unitOfCoprime n h) else 0

@[simp]
theorem diamondOp_n_coprime [NeZero N] (k : ℤ) {n : ℕ} (h : Nat.Coprime n N) :
    diamondOp_n k n = diamondOp k (ZMod.unitOfCoprime n h) := dif_pos h

@[simp]
theorem diamondOp_n_not_coprime [NeZero N] (k : ℤ) {n : ℕ} (h : ¬Nat.Coprime n N) :
    diamondOp_n (N := N) k n = 0 := dif_neg h

private lemma sum_slash' (k : ℤ) {ι : Type*} (s : Finset ι)
    (φ : ι → (UpperHalfPlane → ℂ)) (g : GL (Fin 2) ℝ) :
    (∑ b ∈ s, φ b) ∣[k] g = ∑ b ∈ s, (φ b ∣[k] g) := by
  induction s using Finset.cons_induction with
  | empty => simp [SlashAction.zero_slash]
  | cons a s has ih => simp only [Finset.sum_cons, SlashAction.add_slash, ih]

private lemma zmod_mul_inv' {p : ℕ} [hp : Fact p.Prime] [NeZero p]
    {a : ZMod p} (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  have hne : a.val ≠ 0 := fun h ↦ ha (by
    rw [show a = (a.val : ZMod p) by rw [ZMod.natCast_val, ZMod.cast_id]]; simp [h])
  have hcop : a.val.Coprime p :=
    (hp.out.coprime_iff_not_dvd.2 (fun h ↦ hne (Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt a)))).symm
  have vcz : ∀ x : ZMod p, (x.val : ZMod p) = x := fun x ↦ by rw [ZMod.natCast_val, ZMod.cast_id]
  conv_lhs => rw [show a = (a.val : ZMod p) from (vcz a).symm,
    show (a.val : ZMod p)⁻¹ = (((a.val : ZMod p)⁻¹).val : ZMod p) from (vcz _).symm]
  exact ZMod.mul_val_inv hcop

/-- Two elements of `Fin p` whose values differ by a multiple of `p` are equal. -/
private lemma fin_val_eq_of_dvd_sub {p : ℕ} (hp : Nat.Prime p) (x y : Fin p)
    (h : (p : ℤ) ∣ ((x.val : ℤ) - y.val)) : x.val = y.val := by
  obtain ⟨c, hc⟩ := h
  have h1 : (x.val : ℤ) < p := by exact_mod_cast x.prop
  have h2 : (y.val : ℤ) < p := by exact_mod_cast y.prop
  have h5 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hc0 : c = 0 := by nlinarith
  subst hc0; omega

/-- Cancellation mod a prime: if `p ∣ a * b` and `p ∤ b`, then `p ∣ a` (cast form). -/
private lemma zmod_eq_zero_of_mul_eq_zero {p : ℕ} [Fact p.Prime] {a b : ℤ}
    (hab : ((a * b : ℤ) : ZMod p) = 0) (hb : ((b : ℤ) : ZMod p) ≠ 0) :
    ((a : ℤ) : ZMod p) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hab ⊢
  have hb' : ¬((p : ℤ) ∣ b) := fun h ↦ hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mpr h)
  have hab_abs : p ∣ a.natAbs * b.natAbs := by
    rw [← Int.natAbs_mul]; exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hab)
  rcases (Fact.out (p := p.Prime)).dvd_mul.mp hab_abs with h | h
  · exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h)
  · exact absurd (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h)) hb'

/-- Cross-multiplication of equal ratios in `ZMod p`: `a / b = c / d → a * d = c * b`. -/
private lemma zmod_cross_mul {p : ℕ} [Fact p.Prime] [NeZero p] {a b c d : ZMod p}
    (hb : b ≠ 0) (hd : d ≠ 0) (h : a * b⁻¹ = c * d⁻¹) : a * d = c * b := by
  have inv_mul {x : ZMod p} (hx : x ≠ 0) : x⁻¹ * x = 1 := by
    rw [mul_comm]; exact zmod_mul_inv' hx
  have := congr_arg (· * (b * d)) h
  simp only [mul_assoc] at this
  rwa [show b⁻¹ * (b * d) = d by rw [← mul_assoc, inv_mul hb, one_mul],
       show d⁻¹ * (b * d) = b by
          rw [mul_comm b d, ← mul_assoc, inv_mul hd, one_mul]] at this

/-- For an SL₂ matrix mod `p`, the first column entry `M₀₀ + b·M₁₀` and `M₁₀` cannot
both vanish (else the determinant would be `0`, not `1`). -/
private lemma moebius_col_not_double_zero {p : ℕ} [Fact p.Prime]
    (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet_p : ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) = 1) (c : Fin p)
    (hAc : ((M 0 0 + ↑c.val * M 1 0 : ℤ) : ZMod p) = 0) :
    ((M 1 0 : ℤ) : ZMod p) ≠ 0 := by
  intro h10
  have h00 : ((M 0 0 : ℤ) : ZMod p) = 0 := by
    have : ((M 0 0 + ↑c.val * M 1 0 : ℤ) : ZMod p) =
      ((M 0 0 : ℤ) : ZMod p) + ((c.val : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p) := by
      push_cast; ring
    rw [h10, mul_zero, add_zero] at this; rw [← this]; exact hAc
  have : ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) = 0 := by
    push_cast; rw [h00, h10]; ring
  rw [hdet_p] at this; exact one_ne_zero this

/-- The "second-row determinant" identity mod `p`: `M₁₁·(M₀₀+b·M₁₀) - M₁₀·(M₀₁+b·M₁₁)`
equals `det M` (cast to `ZMod p`). -/
private lemma moebius_row2_det_eq {p : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ) (b : ℕ) :
    ((M 1 1 : ℤ) : ZMod p) * ((M 0 0 + ↑b * M 1 0 : ℤ) : ZMod p) -
      ((M 1 0 : ℤ) : ZMod p) * ((M 0 1 + ↑b * M 1 1 : ℤ) : ZMod p) =
    ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) := by push_cast; ring

noncomputable def moebiusFin' (p : ℕ) (hp : Nat.Prime p)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (b : Fin p) : Fin p :=
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let A : ℤ := M 0 0 + ↑b.val * M 1 0
  let B : ℤ := M 0 1 + ↑b.val * M 1 1
  if (A : ZMod p) = 0 then
    ⟨((M 1 1 : ZMod p) * (M 1 0 : ZMod p)⁻¹).val, ZMod.val_lt _⟩
  else
    ⟨((B : ZMod p) * (A : ZMod p)⁻¹).val, ZMod.val_lt _⟩

lemma moebiusFin'_injective (p : ℕ) (hp : Nat.Prime p)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1) :
    Function.Injective (moebiusFin' p hp M) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hdet_eq : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [det_fin_two] at hdet; exact hdet
  have hdet_p : ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) = 1 := by simp [hdet_eq]
  intro b₁ b₂ heq
  have hv : (moebiusFin' p hp M b₁).val = (moebiusFin' p hp M b₂).val :=
    congr_arg Fin.val heq
  simp only [moebiusFin'] at hv
  set A₁ : ZMod p := ((M 0 0 + ↑b₁.val * M 1 0 : ℤ) : ZMod p) with hA₁_def
  set A₂ : ZMod p := ((M 0 0 + ↑b₂.val * M 1 0 : ℤ) : ZMod p) with hA₂_def
  set B₁ : ZMod p := ((M 0 1 + ↑b₁.val * M 1 1 : ℤ) : ZMod p) with hB₁_def
  set B₂ : ZMod p := ((M 0 1 + ↑b₂.val * M 1 1 : ℤ) : ZMod p) with hB₂_def
  suffices hsuff : b₁.val = b₂.val by ext; exact hsuff
  by_cases hA₁ : A₁ = 0 <;> by_cases hA₂ : A₂ = 0
  · have h_ring : A₁ - A₂ =
        ((↑b₁.val - ↑b₂.val : ℤ) : ZMod p) *
        ((M 1 0 : ℤ) : ZMod p) := by
      simp only [hA₁_def, hA₂_def]; push_cast; ring
    rw [hA₁, hA₂, sub_self] at h_ring
    have h10_ne := moebius_col_not_double_zero M hdet_p b₁ hA₁
    have hb_zero : ((↑b₁.val - ↑b₂.val : ℤ) : ZMod p) = 0 := by
      have h := h_ring.symm; rw [← Int.cast_mul] at h; exact zmod_eq_zero_of_mul_eq_zero h h10_ne
    exact fin_val_eq_of_dvd_sub hp b₁ b₂ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb_zero)
  · exfalso
    rw [if_pos hA₁, if_neg hA₂] at hv
    have hcross := zmod_cross_mul (moebius_col_not_double_zero M hdet_p b₁ hA₁) hA₂
      (ZMod.val_injective p hv)
    have hdet₂ := (moebius_row2_det_eq M b₂.val).trans hdet_p
    exact one_ne_zero (hdet₂.symm.trans (by rw [hcross]; ring))
  · exfalso
    rw [if_neg hA₁, if_pos hA₂] at hv
    have hcross := zmod_cross_mul hA₁ (moebius_col_not_double_zero M hdet_p b₂ hA₂)
      (ZMod.val_injective p hv)
    have hdet₁ := (moebius_row2_det_eq M b₁.val).trans hdet_p
    exact one_ne_zero (hdet₁.symm.trans (by
      rw [show ((M 1 1 : ℤ) : ZMod p) * A₁ = B₁ * ((M 1 0 : ℤ) : ZMod p) from hcross.symm]; ring))
  · rw [if_neg hA₁, if_neg hA₂] at hv
    have hcross := zmod_cross_mul hA₁ hA₂ (ZMod.val_injective p hv)
    have h_cross_det : B₁ * A₂ - B₂ * A₁ =
        ((↑b₁.val - ↑b₂.val : ℤ) : ZMod p) *
        ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) := by
      simp only [hA₁_def, hA₂_def, hB₁_def, hB₂_def]; push_cast; ring
    have h0 : B₁ * A₂ - B₂ * A₁ = 0 := by rw [hcross]; ring
    rw [h0, hdet_p, mul_one] at h_cross_det
    exact fin_val_eq_of_dvd_sub hp b₁ b₂ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h_cross_det.symm)

/-- Determinant of the moebius conjugating matrix is `1`, from the integer relations
`A·M₁₁ - B·M₁₀ = 1` (the row-swapped `det σ`) and `B - A·j = p·q`. -/
private lemma det_fin_two_moebius {A M10 M11 B q jj p : ℤ}
    (hAB : A * M11 - B * M10 = 1) (hq : B - A * jj = p * q) :
    (!![A, q; p * M10, M11 - M10 * jj]).det = 1 := by
  rw [det_fin_two_of]
  linear_combination hAB + M10 * hq

/-- The conjugating `SL₂(ℤ)` matrix for the `T_p` orbit action.  For `σ ∈ SL₂(ℤ)` and
`b : Fin p` with `M₀₀ + b·M₁₀ ≢ 0 (mod p)`, there is `τ ∈ SL₂(ℤ)` with
`[1,b;0,p]·σ = τ·[1,j;0,p]` (where `j = moebiusFin' p hp M b`) and explicit entries
`τ₀₀ = M₀₀ + b·M₁₀`, `τ₁₀ = p·M₁₀`, `τ₁₁ = M₁₁ - M₁₀·j`.  The entry data lets callers
verify `τ ∈ Γ₁(N)` or `Γ₀(N)`. -/
lemma moebius_conj {p : ℕ} [Fact p.Prime] (hp : Nat.Prime p)
    (σ : SL(2, ℤ)) (b : Fin p)
    (hA : ¬(p : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      ↑b.val * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)) :
    ∃ τ : SL(2, ℤ),
      (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ) * mapGL ℚ σ =
        mapGL ℚ τ * T_p_upper p hp.pos
          (moebiusFin' p hp (σ : Matrix (Fin 2) (Fin 2) ℤ) b).val ∧
      (τ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 =
        (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + ↑b.val * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
      (τ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = ↑p * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
      (τ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
        (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 *
          ↑(moebiusFin' p hp (σ : Matrix (Fin 2) (Fin 2) ℤ) b).val := by
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ)
  set A : ℤ := M 0 0 + ↑b.val * M 1 0 with hA_def
  set B : ℤ := M 0 1 + ↑b.val * M 1 1 with hB_def
  have hA_ne : (A : ZMod p) ≠ 0 :=
    fun h ↦ hA ((ZMod.intCast_zmod_eq_zero_iff_dvd A p).mp h)
  set j'_zmod : ZMod p := (B : ZMod p) * (A : ZMod p)⁻¹
  set j' := j'_zmod.val
  have hmoeb : (moebiusFin' p hp M b).val = j' := by
    simp only [moebiusFin', show (M 0 0 + ↑b.val * M 1 0 : ℤ) = A from rfl,
      show (M 0 1 + ↑b.val * M 1 1 : ℤ) = B from rfl]
    rw [if_neg hA_ne]
  have hAj'_mod : (A : ZMod p) * (j' : ZMod p) = (B : ZMod p) := by
    have key : (A : ZMod p) * ((B : ZMod p) * (A : ZMod p)⁻¹) = (B : ZMod p) := by
      rw [mul_comm (B : ZMod p) _, ← mul_assoc, zmod_mul_inv' hA_ne, one_mul]
    rw [show (j' : ZMod p) = j'_zmod by
      show (j'_zmod.val : ZMod p) = j'_zmod; rw [ZMod.natCast_val, ZMod.cast_id]]
    exact key
  have hpBAj : (p : ℤ) ∣ (B - A * ↑j') := by
    have : ((B - A * ↑j' : ℤ) : ZMod p) = 0 := by
      push_cast; rw [sub_eq_zero]; exact hAj'_mod.symm
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  obtain ⟨q, hq⟩ := hpBAj
  have hq_eq : B - A * ↑j' = ↑p * q := hq
  set τ_mat : Matrix (Fin 2) (Fin 2) ℤ :=
    !![A, q; ↑p * M 1 0, M 1 1 - M 1 0 * ↑j'] with hτ_mat_def
  have hτ_det : τ_mat.det = 1 := by
    have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
      have := σ.prop; rw [Matrix.det_fin_two] at this; exact_mod_cast this
    have hAB : A * M 1 1 - B * M 1 0 = 1 := by
      simp only [hA_def, hB_def]; linear_combination hdet
    simpa only [τ_mat] using det_fin_two_moebius hAB hq_eq
  refine ⟨⟨τ_mat, hτ_det⟩, ?_, ?_, ?_, ?_⟩
  · apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
      simp only [GeneralLinearGroup.coe_mul, mul_apply, T_p_upper_coe, Fin.isValue,
        Matrix.SpecialLinearGroup.mapGL_coe_matrix, Fin.sum_univ_two,
        algebraMap_int_eq, hτ_mat_def, hA_def, hmoeb] <;>
      norm_num [mapGL_coe_matrix, RingHom.mapMatrix_apply, map_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.head_fin_const] <;>
      simp only [show (↑σ : Matrix (Fin 2) (Fin 2) ℤ) = M from rfl] <;>
      first | rfl | simp |
        (exact_mod_cast (show B = A * ↑j' + q * ↑p by linarith [hq_eq])) |
        ring
  · show τ_mat 0 0 = A; simp [hτ_mat_def]
  · show τ_mat 1 0 = ↑p * M 1 0; simp [hτ_mat_def]
  · show τ_mat 1 1 = M 1 1 - M 1 0 * ↑(moebiusFin' p hp M b).val
    rw [hmoeb]; simp [hτ_mat_def]

theorem orbit_upper_divN [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma1 N) (b : Fin p)
    (hA : ¬(p : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      ↑b.val * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)) :
    (⇑f ∣[k] (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
    ⇑f ∣[k] (T_p_upper p hp.pos
      (moebiusFin' p hp (σ : Matrix (Fin 2) (Fin 2) ℤ) b).val : GL (Fin 2) ℚ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  change (⇑f ∣[k] glMap (T_p_upper p hp.pos b.val)) ∣[k] mapGL ℝ σ =
    ⇑f ∣[k] glMap (T_p_upper p hp.pos
      (moebiusFin' p hp (σ : Matrix (Fin 2) (Fin 2) ℤ) b).val)
  rw [← SlashAction.slash_mul, ← glMap_mapGL_eq, ← map_mul]
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ)
  have hσ_g1 := (Gamma1_mem N σ).mp hσ
  obtain ⟨τ, hmatrix, hτ00, hτ10, hτ11⟩ := moebius_conj hp σ b hA
  have hτ_g1 : τ ∈ Gamma1 N := by
    rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · rw [hτ00]; push_cast; rw [hσ_g1.2.2, mul_zero, add_zero]; exact hσ_g1.1
    · rw [hτ11]; push_cast; rw [hσ_g1.2.2, zero_mul, sub_zero]; exact hσ_g1.2.1
    · rw [hτ10]; push_cast; rw [hσ_g1.2.2, mul_zero]
  rw [hmatrix, map_mul, glMap_mapGL_eq, SlashAction.slash_mul]
  congr 1
  exact f.slash_action_eq' _ (Subgroup.mem_map.mpr ⟨τ, hτ_g1, rfl⟩)

theorem heckeT_p_ut_slash_invariant_divN [NeZero N] (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : ¬Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ (Gamma1 N).map (mapGL ℝ)) :
    (heckeT_p_ut k p hp.pos (⇑f)) ∣[k] γ = heckeT_p_ut k p hp.pos (⇑f) := by
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hγ
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  simp only [heckeT_p_ut]
  rw [sum_slash']
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have hdet_M : M.det = 1 := by
    change (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1; exact_mod_cast σ.prop
  have hσ_g1 := (Gamma1_mem N σ).mp hσ
  have hp_dvd_N : (p : ℤ) ∣ (N : ℤ) := by
    rw [Int.natCast_dvd_natCast]; by_contra h; exact hpN (hp.coprime_iff_not_dvd.mpr h)
  have hp_dvd_σ10 : (p : ℤ) ∣ M 1 0 :=
    hp_dvd_N.trans <| by rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hσ_g1.2.2
  have hσ00_mod_p : ((M 0 0 : ℤ) : ZMod p) = 1 := by
    have hp_dvd : (p : ℤ) ∣ (M 0 0 - 1) := hp_dvd_N.trans <| by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hσ_g1.1]; ring
    rw [← sub_eq_zero]
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (M 0 0 - 1) p).mpr hp_dvd
    push_cast at this ⊢; exact this
  have hA_all : ∀ b : Fin p,
      ¬(p : ℤ) ∣ (M 0 0 + ↑b.val * M 1 0) := by
    intro b hdvd
    have : ((M 0 0 + ↑b.val * M 1 0 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
    have h10 : ((M 1 0 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hp_dvd_σ10
    rw [show ((M 0 0 + ↑b.val * M 1 0 : ℤ) : ZMod p) =
      ((M 0 0 : ℤ) : ZMod p) + ((b.val : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p) by
      push_cast; ring, h10, mul_zero, add_zero, hσ00_mod_p] at this
    exact one_ne_zero this
  have h_bij : Function.Bijective (moebiusFin' p hp M) :=
    Finite.injective_iff_bijective.mp (moebiusFin'_injective p hp M hdet_M)
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_equiv (Equiv.ofBijective _ h_bij)
    (fun _ ↦ ⟨fun _ ↦ Finset.mem_univ _, fun _ ↦ Finset.mem_univ _⟩)
    (fun b _ ↦ orbit_upper_divN k p hp f σ hσ b (hA_all b))

private lemma Gamma1_isCusp_glMap_smul' [NeZero N] (A : GL (Fin 2) ℚ) {c : OnePoint ℝ}
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

/-- `T_p` for `p ∣ N`: upper-triangular sum only. -/
noncomputable def heckeT_p_divN [NeZero N] (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : ¬Nat.Coprime p N) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    { toSlashInvariantForm :=
      { toFun := heckeT_p_ut k p hp.pos (⇑f)
        slash_action_eq' γ hγ :=
          heckeT_p_ut_slash_invariant_divN k p hp hpN f γ hγ }
      holo' := by
        show MDifferentiable _ _ (heckeT_p_ut k p hp.pos (⇑f))
        simp only [heckeT_p_ut]
        exact MDifferentiable.sum fun b _ ↦ (ModularFormClass.holo f).slash k _
      bdd_at_cusps' := fun {cusp} hc ↦ by
        show cusp.IsBoundedAt (heckeT_p_ut k p hp.pos (⇑f)) k
        simp only [heckeT_p_ut]
        apply Finset.sum_induction _ (fun g ↦ cusp.IsBoundedAt g k)
          (fun _ _ ha hb ↦ ha.add hb)
          ((0 : ModularForm ((Gamma1 N).map (mapGL ℝ)) k).bdd_at_cusps' hc)
        intro b _
        exact OnePoint.IsBoundedAt.smul_iff.mp
          (f.bdd_at_cusps' (Gamma1_isCusp_glMap_smul' _ hc)) }
  map_add' f g := by
    ext z; simp only [ModularForm.add_apply]
    show heckeT_p_ut k p hp.pos (⇑(f + g)) z =
      heckeT_p_ut k p hp.pos (⇑f) z + heckeT_p_ut k p hp.pos (⇑g) z
    simp only [heckeT_p_ut]
    rw [show (⇑(f + g) : UpperHalfPlane → ℂ) = ⇑f + ⇑g from rfl]
    simp only [SlashAction.add_slash]; rw [Finset.sum_add_distrib]; simp [Finset.sum_apply]
  map_smul' c f := by
    ext z; simp only [RingHom.id_apply]
    show heckeT_p_ut k p hp.pos (⇑(c • f)) z = c * heckeT_p_ut k p hp.pos (⇑f) z
    simp only [heckeT_p_ut]
    rw [show (⇑(c • f) : UpperHalfPlane → ℂ) = c • ⇑f from rfl]
    have smul_slash_upper : ∀ b, (c • ⇑f) ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ) =
        c • (⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) := by
      intro b
      show (c • ⇑f) ∣[k] glMap (T_p_upper p hp.pos b) =
        c • (⇑f ∣[k] glMap (T_p_upper p hp.pos b))
      have hdet_pos : 0 < (glMap (T_p_upper p hp.pos b)).det.val := by
        have hdet : (glMap (T_p_upper p hp.pos b)).det.val =
          algebraMap ℚ ℝ (T_p_upper p hp.pos b).det.val :=
          congr_arg Units.val (GeneralLinearGroup.map_det (algebraMap ℚ ℝ)
            (T_p_upper p hp.pos b))
        rw [hdet]; apply Rat.cast_pos.mpr
        rw [GeneralLinearGroup.val_det_apply, T_p_upper_det]; exact_mod_cast hp.pos
      have hσ : UpperHalfPlane.σ (glMap (T_p_upper p hp.pos b)) =
          ContinuousAlgEquiv.refl ℝ ℂ := by
        unfold UpperHalfPlane.σ; rw [if_pos hdet_pos]
      ext w; show ((c • ⇑f) ∣[k] glMap (T_p_upper p hp.pos b)) w =
        (c • (⇑f ∣[k] glMap (T_p_upper p hp.pos b))) w
      rw [ModularForm.smul_slash, hσ, ContinuousAlgEquiv.refl_apply]
    simp_rw [smul_slash_upper]
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, Finset.sum_apply]

/-- `T_p` for all primes `p`, including `p ∣ N`.

When `(p, N) = 1`: the standard `heckeT_p` from `GL2/HeckeT_p.lean`.
When `p ∣ N`: the upper-triangular sum `Σ_{b=0}^{p-1} f ∣[k] [[1,b],[0,p]]`. -/
def heckeT_p_all [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p) :
    Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  if hpN : Nat.Coprime p N then heckeT_p k p hp hpN
  else heckeT_p_divN k p hp hpN

theorem heckeT_p_all_coprime [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) :
    heckeT_p_all k p hp = heckeT_p k p hp hpN :=
  dif_pos hpN

/-- `T_{p^r}` for prime `p`, defined by the Diamond–Shurman recurrence (5.10):
- `T_{p^0} = id`
- `T_{p^1} = T_p`
- `T_{p^{r+2}} = T_p · T_{p^{r+1}} - p^{k-1} · ⟨p⟩ · T_{p^r}`

When `p ∣ N` the diamond term `⟨p⟩ = 0`, giving `T_{p^r} = T_p^r`. -/
def heckeT_ppow [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p) :
    ℕ → Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
  | 0 => 1
  | 1 => heckeT_p_all k p hp
  | r + 2 =>
    heckeT_p_all k p hp * heckeT_ppow k p hp (r + 1) -
      ((↑p : ℂ) ^ (k - 1)) • (diamondOp_n k p * heckeT_ppow k p hp r)

@[simp]
theorem heckeT_ppow_zero [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p) :
    heckeT_ppow (N := N) k p hp 0 = 1 := rfl

@[simp]
theorem heckeT_ppow_one [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p) :
    heckeT_ppow (N := N) k p hp 1 = heckeT_p_all k p hp := rfl

/-- The defining recurrence for `T_{p^r}`. -/
theorem heckeT_ppow_succ_succ [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p) (r : ℕ) :
    heckeT_ppow (N := N) k p hp (r + 2) =
      heckeT_p_all k p hp * heckeT_ppow k p hp (r + 1) -
        ((↑p : ℂ) ^ (k - 1)) • (diamondOp_n k p * heckeT_ppow k p hp r) := rfl

/-- When `p ∣ N` the diamond term vanishes, so `T_{p^r} = T_p^r`. -/
theorem heckeT_ppow_eq_pow_of_not_coprime [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (hpN : ¬Nat.Coprime p N) (r : ℕ) :
    heckeT_ppow (N := N) k p hp r = heckeT_p_all k p hp ^ r := by
  induction r with
  | zero => simp [pow_zero]
  | succ r ih =>
    cases r with
    | zero => simp [heckeT_ppow, pow_one]
    | succ r =>
      rw [heckeT_ppow_succ_succ, diamondOp_n_not_coprime k hpN,
        zero_mul, smul_zero, sub_zero, ih, ← pow_succ']

/-- `T_{p^1}` for coprime `p` equals the concrete `heckeT_p`. -/
theorem heckeT_ppow_one_eq_heckeT_p [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) :
    heckeT_ppow (N := N) k p hp 1 = heckeT_p k p hp hpN :=
  (heckeT_ppow_one ..).trans (heckeT_p_all_coprime k hp hpN)

/-- Auxiliary definition for `heckeT_n`: peels off the smallest prime factor. -/
def heckeT_n_aux [NeZero N] (k : ℤ) (m : ℕ) :
    Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  if h : m ≤ 1 then 1
  else
    let p := m.minFac
    let hp := Nat.minFac_prime (by omega : m ≠ 1)
    let v := m.factorization p
    heckeT_ppow k p hp v * heckeT_n_aux k (m / p ^ v)
termination_by m
decreasing_by
  have hp := Nat.minFac_prime (by omega : m ≠ 1)
  exact Nat.div_lt_self (by omega) (Nat.one_lt_pow
    (hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd m)).ne' hp.one_lt)

/-- **Hecke operator `T_n`** on `M_k(Γ₁(N))` for general `n ∈ ℕ⁺`.

Defined as the product of prime-power components:
`T_n = ∏_{p^v ‖ n} T_{p^v}`, assembled by peeling off `minFac(n)`.

The key algebraic properties (`heckeT_n_mul_coprime`, `heckeT_n_comm`) ensure
this is independent of the factorisation order.

Reference: [DS] §5.3, [Miy] §4.5. -/
def heckeT_n [NeZero N] (k : ℤ) (n : ℕ) [NeZero n] :
    Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  heckeT_n_aux k n

@[simp]
theorem heckeT_n_one [NeZero N] (k : ℤ) :
    heckeT_n (N := N) k 1 = 1 := by
  simp [heckeT_n, heckeT_n_aux]

theorem heckeT_n_prime [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    heckeT_n (N := N) k p = heckeT_p_all k p hp := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  show heckeT_n_aux k p = heckeT_p_all k p hp
  rw [heckeT_n_aux, dif_neg (not_le.mpr hp.one_lt)]
  simp only [hp.minFac_eq, hp.factorization_self, pow_one, Nat.div_self hp.pos]
  rw [heckeT_n_aux, dif_pos le_rfl, mul_one]; rfl

theorem heckeT_n_prime_coprime [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    heckeT_n (N := N) k p = heckeT_p k p hp hpN := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [heckeT_n_prime k hp, heckeT_p_all_coprime k hp hpN]

theorem heckeT_n_prime_pow [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (r : ℕ) (hr : 0 < r) :
    haveI : NeZero (p ^ r) := ⟨(pow_pos hp.pos r).ne'⟩
    heckeT_n (N := N) k (p ^ r) = heckeT_ppow k p hp r := by
  haveI : NeZero (p ^ r) := ⟨(pow_pos hp.pos r).ne'⟩
  show heckeT_n_aux k (p ^ r) = heckeT_ppow k p hp r
  rw [heckeT_n_aux, dif_neg (not_le.mpr (one_lt_pow₀ hp.one_lt (by omega)))]
  have hmin : (p ^ r).minFac = p := hp.pow_minFac (by omega)
  have hfact : (p ^ r).factorization p = r := by
    rw [hp.factorization_pow, Finsupp.single_eq_same]
  simp only [hmin, hfact, Nat.div_self (pow_pos hp.pos r)]
  rw [heckeT_n_aux, dif_pos le_rfl, mul_one]

/-- Recursive unfolding of `T_n` for `n > 1`: peels off the smallest prime factor.
If `p = minFac n` and `v = n.factorization p`, then `T_n = T_{p^v} * T_{n/p^v}`. -/
theorem heckeT_n_unfold [NeZero N] (k : ℤ) (n : ℕ) [NeZero n] (hn : 1 < n) :
    heckeT_n (N := N) k n =
      let p := n.minFac
      let hp := Nat.minFac_prime (by omega : n ≠ 1)
      let v := n.factorization p
      have hv_pos : 0 < v :=
        hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd n)
      have hdiv_pos : 0 < n / p ^ v :=
        Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n p))
          (pow_pos hp.pos v)
      haveI : NeZero (n / p ^ v) := ⟨hdiv_pos.ne'⟩
      heckeT_ppow k p hp v * heckeT_n k (n / p ^ v) := by
  show heckeT_n_aux k n = _
  rw [heckeT_n_aux, dif_neg (not_le.mpr hn)]
  rfl

/-- The quotient `n / p^v` (where `v = n.factorization(minFac n)`) is strictly less than `n`
for `n > 1`. -/
theorem heckeT_n_unfold_lt (n : ℕ) (hn : 1 < n) :
    n / n.minFac ^ (n.factorization n.minFac) < n :=
  let hp := Nat.minFac_prime (by omega : n ≠ 1)
  Nat.div_lt_self (by omega) (Nat.one_lt_pow
    (hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd n)).ne' hp.one_lt)

private lemma T_p_upper_mul (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (b c : ℕ)
    (hpq : 0 < p * q) :
    (T_p_upper q hq c : GL (Fin 2) ℚ) * T_p_upper p hp b =
    T_p_upper (p * q) hpq (b + c * p) := by
  apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
    simp [T_p_upper, GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply,
      Fin.sum_univ_two]; ring

private lemma T_p_lower_mul_lower (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hpq : 0 < p * q) :
    (T_p_lower p hp : GL (Fin 2) ℚ) * T_p_lower q hq =
    T_p_lower (p * q) hpq := by
  apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
    simp [T_p_lower, GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply,
      Fin.sum_univ_two]

private lemma crt_sum_eq {α : Type*} [AddCommMonoid α]
    {p q : ℕ} (hp : 0 < p)
    (f : ℕ → α) :
    ∑ b ∈ Finset.range p, ∑ c ∈ Finset.range q, f (b + c * p) =
    ∑ j ∈ Finset.range (p * q), f j := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij (fun bc ↦ bc.1 + bc.2 * p) ?_ ?_ ?_ ?_
  · intro ⟨b, c⟩ hbc
    simp only [Finset.mem_product, Finset.mem_range] at hbc ⊢
    nlinarith [hbc.1, hbc.2]
  · intro ⟨b₁, c₁⟩ hbc₁ ⟨b₂, c₂⟩ hbc₂ h
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hbc₁ hbc₂
    simp only at h
    have hbeq : b₁ = b₂ := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · have : c₁ > c₂ := by nlinarith [hbc₁.1, hbc₂.1]
        nlinarith [hbc₁.1, hbc₂.1]
      · have : c₂ > c₁ := by nlinarith [hbc₁.1, hbc₂.1]
        nlinarith [hbc₁.1, hbc₂.1]
    subst hbeq; simp only [Prod.mk.injEq, true_and]
    exact mul_right_cancel₀ (by omega : (p : ℕ) ≠ 0) (by omega : c₁ * p = c₂ * p)
  · intro j hj
    simp only [Set.mem_image, Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hj ⊢
    refine ⟨(j % p, j / p), ⟨Nat.mod_lt j hp,
      Nat.div_lt_of_lt_mul (mul_comm p q ▸ hj)⟩, ?_⟩
    show j % p + j / p * p = j
    rw [mul_comm]; exact Nat.mod_add_div j p
  · intro _ _; rfl

private lemma heckeT_p_ut_comm (k : ℤ) {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (f : UpperHalfPlane → ℂ) :
    heckeT_p_ut k p hp.pos (heckeT_p_ut k q hq.pos f) =
    heckeT_p_ut k q hq.pos (heckeT_p_ut k p hp.pos f) := by
  have hpq_cop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hpq_pos : 0 < p * q := mul_pos hp.pos hq.pos
  suffices h : ∀ (r s : ℕ) (hr : Nat.Prime r) (hs : Nat.Prime s) (hrs : r ≠ s)
      (hrs_cop : Nat.Coprime r s) (hrs_pos : 0 < r * s),
      heckeT_p_ut k r hr.pos (heckeT_p_ut k s hs.pos f) =
      ∑ j ∈ Finset.range (r * s), f ∣[k] (T_p_upper (r * s) hrs_pos j : GL (Fin 2) ℚ) by
    rw [h p q hp hq hpq hpq_cop hpq_pos,
        h q p hq hp (Ne.symm hpq) hpq_cop.symm (mul_comm q p ▸ hpq_pos)]
    simp only [mul_comm q p]
  intro r s hr hs _ _ hrs_pos
  unfold heckeT_p_ut
  simp only [SlashAction.sum_slash]
  simp_rw [← SlashAction.slash_mul, T_p_upper_mul r s hr.pos hs.pos _ _ hrs_pos]
  exact crt_sum_eq hr.pos
    (fun j ↦ f ∣[k] (T_p_upper (r * s) hrs_pos j : GL (Fin 2) ℚ))

/-- When `p ∣ N`, `heckeT_p_all` agrees with `heckeT_p_divN` and its coercion
is `heckeT_p_ut`. -/
lemma heckeT_p_all_not_coprime_apply [NeZero N] (k : ℤ) {p : ℕ}
    (hp : Nat.Prime p) (hpN : ¬Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(heckeT_p_all k p hp f) : UpperHalfPlane → ℂ) = heckeT_p_ut k p hp.pos (⇑f) := by
  show ⇑((if h : Nat.Coprime p N then heckeT_p k p hp h else heckeT_p_divN k p hp hpN) f) = _
  rw [dif_neg hpN]; rfl

private lemma heckeT_p_all_coprime_apply [NeZero N] (k : ℤ) {p : ℕ}
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(heckeT_p_all k p hp f) : UpperHalfPlane → ℂ) = heckeT_p_fun k p hp hpN f := by
  show ⇑((if h : Nat.Coprime p N then heckeT_p k p hp h else heckeT_p_divN k p hp (by tauto)) f) = _
  rw [dif_pos hpN]; rfl

private theorem orbit_upper_gamma0_divN [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (b : Fin p)
    (hA : ¬(p : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      ↑b.val * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)) :
    (⇑f ∣[k] (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ)) ∣[k] mapGL ℝ σ =
    (⇑f ∣[k] mapGL ℝ σ) ∣[k]
      (T_p_upper p hp.pos
        (moebiusFin' p hp (σ : Matrix (Fin 2) (Fin 2) ℤ) b).val : GL (Fin 2) ℚ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  change (⇑f ∣[k] glMap (T_p_upper p hp.pos b.val)) ∣[k] mapGL ℝ σ =
    (⇑f ∣[k] mapGL ℝ σ) ∣[k] glMap (T_p_upper p hp.pos
      (moebiusFin' p hp (σ : Matrix (Fin 2) (Fin 2) ℤ) b).val)
  rw [← SlashAction.slash_mul, ← SlashAction.slash_mul, ← glMap_mapGL_eq, ← map_mul]
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ)
  rw [Gamma0_mem] at hσ
  obtain ⟨τ, hmatrix, _hτ00, hτ10, hτ11⟩ := moebius_conj hp σ b hA
  have hτ_g0 : τ ∈ Gamma0 N := by
    rw [Gamma0_mem]; rw [hτ10]; push_cast; rw [hσ, mul_zero]
  have hmap : Gamma0Map N ⟨τ, hτ_g0⟩ = Gamma0Map N ⟨σ, Gamma0_mem.mpr hσ⟩ := by
    simp only [Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk]
    show ((τ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod N) = ((M 1 1 : ℤ) : ZMod N)
    rw [hτ11]; push_cast; rw [hσ, zero_mul, sub_zero]
  conv_lhs => rw [hmatrix, map_mul, glMap_mapGL_eq, SlashAction.slash_mul]
  conv_rhs => rw [show glMap ((mapGL ℚ) σ) = mapGL ℝ σ from glMap_mapGL_eq σ,
    SlashAction.slash_mul]
  congr 1
  exact slash_eq_of_Gamma0Map_eq
    (fun _ hγ ↦ SlashInvariantFormClass.slash_action_eq f _ hγ)
    ⟨τ, hτ_g0⟩ ⟨σ, Gamma0_mem.mpr hσ⟩ hmap

private theorem heckeT_p_ut_orbit_comm_gamma0 [NeZero N] (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : ¬Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) :
    (heckeT_p_ut k p hp.pos (⇑f)) ∣[k] mapGL ℝ σ =
    heckeT_p_ut k p hp.pos (⇑f ∣[k] mapGL ℝ σ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  simp only [heckeT_p_ut]
  rw [sum_slash']
  set M := (σ : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have hdet_M : M.det = 1 := by
    change (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1; exact_mod_cast σ.prop
  have hσ_g0 := (Gamma0_mem (N := N)).mp hσ
  have hp_dvd_N : (p : ℤ) ∣ (N : ℤ) := by
    rw [Int.natCast_dvd_natCast]; by_contra h; exact hpN (hp.coprime_iff_not_dvd.mpr h)
  have hp_dvd_σ10 : (p : ℤ) ∣ M 1 0 :=
    hp_dvd_N.trans <| by rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hσ_g0
  have hσ00_ne : ((M 0 0 : ℤ) : ZMod p) ≠ 0 := by
    intro h00
    have h10 : ((M 1 0 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hp_dvd_σ10
    have hdet_zmod : ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) = 1 := by
      rw [det_fin_two] at hdet_M; simp [hdet_M]
    rw [show ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : ZMod p) =
      (M 0 0 : ZMod p) * (M 1 1 : ZMod p) - (M 0 1 : ZMod p) * (M 1 0 : ZMod p) by
      push_cast; ring, show (M 0 0 : ZMod p) = ((M 0 0 : ℤ) : ZMod p) by ring,
      h00, show (M 1 0 : ZMod p) = ((M 1 0 : ℤ) : ZMod p) by ring,
      h10, zero_mul, mul_zero, sub_zero] at hdet_zmod
    exact zero_ne_one hdet_zmod
  have hA_all : ∀ b : Fin p,
      ¬(p : ℤ) ∣ (M 0 0 + ↑b.val * M 1 0) := by
    intro b hdvd
    have : ((M 0 0 + ↑b.val * M 1 0 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
    have h10 : ((M 1 0 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hp_dvd_σ10
    rw [show ((M 0 0 + ↑b.val * M 1 0 : ℤ) : ZMod p) =
      ((M 0 0 : ℤ) : ZMod p) + ((b.val : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p) by
      push_cast; ring, h10, mul_zero, add_zero] at this
    exact hσ00_ne this
  have h_bij : Function.Bijective (moebiusFin' p hp M) :=
    Finite.injective_iff_bijective.mp (moebiusFin'_injective p hp M hdet_M)
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_equiv (Equiv.ofBijective _ h_bij)
    (fun _ ↦ ⟨fun _ ↦ Finset.mem_univ _, fun _ ↦ Finset.mem_univ _⟩)
    (fun b _ ↦ orbit_upper_gamma0_divN k p hp f σ hσ b (hA_all b))

/-- Functional form: applying `heckeT_p_ut` to a diamond-twisted form equals
slash-twisting the `heckeT_p_ut` result. Used for mixed-coprimality commutativity. -/
theorem heckeT_p_ut_orbit_comm_gamma0_fun [NeZero N] (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : ¬Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (g : ↥(Gamma0 N)) :
    (heckeT_p_ut k p hp.pos (⇑f)) ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
    heckeT_p_ut k p hp.pos (⇑(diamondOpAux k g f)) :=
  heckeT_p_ut_orbit_comm_gamma0 k p hp hpN f g g.property

private def shiftSL' (m : ℤ) : SL(2, ℤ) :=
  ⟨!![1, m; 0, 1], by simp [Matrix.det_fin_two]⟩

private lemma shiftSL'_mem_Gamma1 (M : ℕ) (m : ℤ) : shiftSL' m ∈ Gamma1 M := by
  rw [Gamma1_mem]; refine ⟨?_, ?_, ?_⟩ <;> simp [shiftSL']

private lemma T_p_lower_upper_shift (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (b : ℕ) :
    (T_p_lower q hq : GL (Fin 2) ℚ) * T_p_upper p hp b =
    mapGL ℚ (shiftSL' (↑(q * b / p : ℕ) : ℤ)) *
      ((T_p_upper p hp (q * b % p) : GL (Fin 2) ℚ) * T_p_lower q hq) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T_p_lower, T_p_upper, shiftSL', mapGL, GeneralLinearGroup.mkOfDetNeZero,
      Matrix.mul_apply, Fin.sum_univ_two]
  have h1 : (↑q : ℚ) * ↑b = ((q * b : Nat) : ℚ) := by push_cast; ring
  have h2 : ((↑q * ↑b / ↑p : ℤ) : ℚ) = ((q * b / p : Nat) : ℚ) := by congr 1
  have h3 : q * b = q * b % p + q * b / p * p := by
    have h := Nat.div_add_mod (q * b) p; linarith
  rw [h1, h2, ← Nat.cast_mul, ← Nat.cast_add,
    show q * b % p + q * b / p * p = q * b from h3.symm]

private lemma slash_lower_upper_mod [NeZero N] (k : ℤ) {p q : ℕ}
    (hp : Nat.Prime p) (hq : 0 < q)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (b : ℕ) :
    (⇑g) ∣[k] ((T_p_lower q hq : GL (Fin 2) ℚ) * T_p_upper p hp.pos b) =
    (⇑g) ∣[k] ((T_p_upper p hp.pos (q * b % p) : GL (Fin 2) ℚ) * T_p_lower q hq) := by
  rw [T_p_lower_upper_shift p q hp.pos hq b, SlashAction.slash_mul]
  congr 1
  change (⇑g) ∣[k] (glMap (mapGL ℚ (shiftSL' _)) : GL (Fin 2) ℝ) = ⇑g
  rw [glMap_mapGL_eq]
  exact g.slash_action_eq' _ (Subgroup.mem_map.mpr ⟨_, shiftSL'_mem_Gamma1 N _, rfl⟩)

private lemma heckeT_p_ut_slash_lower_comm [NeZero N] (k : ℤ) {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (heckeT_p_ut k p hp.pos (⇑g)) ∣[k] (T_p_lower q hq.pos : GL (Fin 2) ℚ) =
    heckeT_p_ut k p hp.pos ((⇑g) ∣[k] (T_p_lower q hq.pos : GL (Fin 2) ℚ)) := by
  simp only [heckeT_p_ut, SlashAction.sum_slash]
  simp_rw [← SlashAction.slash_mul]
  conv_rhs => arg 2; ext b; rw [slash_lower_upper_mod k hp hq.pos g b]
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpq_cop : Nat.Coprime q p := (Nat.coprime_primes hq hp).mpr (Ne.symm hpq)
  symm
  refine Finset.sum_nbij (fun b ↦ q * b % p)
    (fun b _ ↦ Finset.mem_range.mpr (Nat.mod_lt _ hp.pos))
    (fun b₁ hb₁ b₂ hb₂ he ↦ ?_)
    (fun c hc ↦ ?_)
    (fun _ _ ↦ rfl)
  · simp only [Finset.mem_coe, Finset.mem_range] at hb₁ hb₂
    simp only at he
    have hmod : q * b₁ ≡ q * b₂ [MOD p] := by rwa [Nat.ModEq]
    have hbb : b₁ ≡ b₂ [MOD p] :=
      Nat.ModEq.cancel_left_of_coprime hpq_cop.symm hmod
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hb₁, Nat.mod_eq_of_lt hb₂] at hbb
  · simp only [Finset.mem_coe, Finset.mem_range, Set.mem_image] at hc ⊢
    have hq_unit : IsUnit ((q : ZMod p)) := (ZMod.isUnit_iff_coprime q p).mpr hpq_cop
    obtain ⟨u, hu⟩ := hq_unit
    set b_zmod := u⁻¹ * (c : ZMod p)
    use b_zmod.val
    refine ⟨ZMod.val_lt _, ?_⟩
    have key : (q : ZMod p) * b_zmod = (c : ZMod p) := by
      simp only [b_zmod, ← hu, Units.mul_inv_cancel_left]
    rw [show q * b_zmod.val % p = (((q * b_zmod.val : Nat) : ZMod p)).val from
      (ZMod.val_natCast p _).symm]
    simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
    rw [key, ZMod.val_cast_of_lt hc]

private lemma T_p_lower_comm (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    (T_p_lower p hp : GL (Fin 2) ℚ) * T_p_lower q hq =
    T_p_lower q hq * T_p_lower p hp := by
  have hpq : 0 < p * q := Nat.mul_pos hp hq
  rw [T_p_lower_mul_lower p q hp hq hpq,
      T_p_lower_mul_lower q p hq hp (mul_comm q p ▸ hpq)]
  congr 1; ring

private lemma diamondOp_unitOfCoprime_comm [NeZero N] (k : ℤ)
    {p q : ℕ} (hpN : Nat.Coprime p N) (hqN : Nat.Coprime q N) :
    (diamondOp k (ZMod.unitOfCoprime p hpN)).comp
        (diamondOp k (ZMod.unitOfCoprime q hqN)) =
    (diamondOp k (ZMod.unitOfCoprime q hqN)).comp
        (diamondOp k (ZMod.unitOfCoprime p hpN)) := by
  rw [← diamondOp_mul, ← diamondOp_mul, mul_comm]

/-- For `(p, N) = 1` and `q ∣ N`, applying the diamond `⟨p⟩` to `T_q f` equals the
upper-triangular `T_q` applied to `⟨p⟩ f`. -/
private lemma diamondOp_heckeT_p_all_eq_ut_of_divN [NeZero N] (k : ℤ) {p q : ℕ}
    (hpN : Nat.Coprime p N) (hq : Nat.Prime q) (hqN : ¬Nat.Coprime q N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) (heckeT_p_all k q hq f)) : UpperHalfPlane → ℂ) =
      heckeT_p_ut k q hq.pos (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f)) := by
  set σ_p := (Gamma0MapUnits_surjective (N := N) (ZMod.unitOfCoprime p hpN)).choose
  have hσ_p : Gamma0MapUnits σ_p = ZMod.unitOfCoprime p hpN :=
    (Gamma0MapUnits_surjective (ZMod.unitOfCoprime p hpN)).choose_spec
  have hdia : diamondOp k (ZMod.unitOfCoprime p hpN) = diamondOpAux k σ_p :=
    diamondOp_eq_diamondOpAux k _ σ_p hσ_p
  conv_lhs => rw [hdia]
  change (⇑(heckeT_p_all k q hq f) ∣[k] mapGL ℝ (σ_p : SL(2, ℤ))) =
    heckeT_p_ut k q hq.pos (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f))
  rw [heckeT_p_all_not_coprime_apply k hq hqN f,
      heckeT_p_ut_orbit_comm_gamma0 k q hq hqN f σ_p σ_p.property]
  congr 1

/-- Definitional unfolding of the coprime `T_r` on coefficient functions: the upper sum
plus the diamond-twisted lower term. -/
private lemma heckeT_p_coe_eq_ut_add_lower [NeZero N] (k : ℤ) {r : ℕ}
    (hr : Nat.Prime r) (hrN : Nat.Coprime r N)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(heckeT_p k r hr hrN g) : UpperHalfPlane → ℂ) =
      heckeT_p_ut k r hr.pos (⇑g) +
        (⇑(diamondOp k (ZMod.unitOfCoprime r hrN) g)) ∣[k]
          (T_p_lower r hr.pos : GL (Fin 2) ℚ) := rfl

/-- The both-coprime case of `heckeT_p_all_comm_distinct`: when `(p, N) = (q, N) = 1`,
`T_p (T_q f) = T_q (T_p f)` pointwise. -/
private lemma heckeT_p_comm_distinct_both_coprime [NeZero N] (k : ℤ) {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hpN : Nat.Coprime p N) (hqN : Nat.Coprime q N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (z : UpperHalfPlane) :
    heckeT_p_fun k p hp hpN (heckeT_p k q hq hqN f) z =
      heckeT_p_fun k q hq hqN (heckeT_p k p hp hpN f) z := by
  suffices h : heckeT_p_fun k p hp hpN (heckeT_p k q hq hqN f) =
      heckeT_p_fun k q hq hqN (heckeT_p k p hp hpN f) from congr_fun h z
  have hdp_comm := LinearMap.congr_fun
    (heckeT_p_comm_diamondOp k q hq hqN (ZMod.unitOfCoprime p hpN)) f
  have hdq_comm := LinearMap.congr_fun
    (heckeT_p_comm_diamondOp k p hp hpN (ZMod.unitOfCoprime q hqN)) f
  have hDD : (⇑(diamondOp k (ZMod.unitOfCoprime q hqN)
      (diamondOp k (ZMod.unitOfCoprime p hpN) f)) : UpperHalfPlane → ℂ) =
    ⇑(diamondOp k (ZMod.unitOfCoprime p hpN)
      (diamondOp k (ZMod.unitOfCoprime q hqN) f)) :=
    congr_arg DFunLike.coe <| by
      simpa only [LinearMap.comp_apply]
        using (LinearMap.congr_fun (diamondOp_unitOfCoprime_comm k hpN hqN) f).symm
  have hLC := T_p_lower_comm q p hq.pos hp.pos
  ext w
  simp only [heckeT_p_fun, Pi.add_apply]
  rw [heckeT_p_coe_eq_ut_add_lower k hq hqN f, heckeT_p_coe_eq_ut_add_lower k hp hpN f]
  rw [show (⇑(diamondOp k (ZMod.unitOfCoprime p hpN)
      (heckeT_p k q hq hqN f)) : UpperHalfPlane → ℂ) =
    ⇑(heckeT_p k q hq hqN (diamondOp k (ZMod.unitOfCoprime p hpN) f))
    from congr_arg _ hdp_comm,
    show (⇑(diamondOp k (ZMod.unitOfCoprime q hqN)
      (heckeT_p k p hp hpN f)) : UpperHalfPlane → ℂ) =
    ⇑(heckeT_p k p hp hpN (diamondOp k (ZMod.unitOfCoprime q hqN) f))
    from congr_arg _ hdq_comm]
  rw [heckeT_p_coe_eq_ut_add_lower k hq hqN (diamondOp k (ZMod.unitOfCoprime p hpN) f),
    heckeT_p_coe_eq_ut_add_lower k hp hpN (diamondOp k (ZMod.unitOfCoprime q hqN) f)]
  simp only [heckeT_p_ut, SlashAction.add_slash, Finset.sum_add_distrib,
    SlashAction.sum_slash, Pi.add_apply, Finset.sum_apply]
  have hUU := congr_fun (heckeT_p_ut_comm k hp hq hpq (⇑f)) w
  simp only [heckeT_p_ut, SlashAction.sum_slash, Finset.sum_apply] at hUU
  have hC1 := congr_fun
    (heckeT_p_ut_slash_lower_comm k hp hq hpq (diamondOp k (ZMod.unitOfCoprime q hqN) f)) w
  simp only [heckeT_p_ut, SlashAction.sum_slash, Finset.sum_apply] at hC1
  have hC2 := congr_fun
    (heckeT_p_ut_slash_lower_comm k hq hp (Ne.symm hpq) (diamondOp k (ZMod.unitOfCoprime p hpN) f)) w
  simp only [heckeT_p_ut, SlashAction.sum_slash, Finset.sum_apply] at hC2
  have hLL : (((⇑(diamondOp k (ZMod.unitOfCoprime q hqN)
        (diamondOp k (ZMod.unitOfCoprime p hpN) f))) ∣[k]
      (T_p_lower q hq.pos : GL (Fin 2) ℚ)) ∣[k]
      (T_p_lower p hp.pos : GL (Fin 2) ℚ)) w =
    (((⇑(diamondOp k (ZMod.unitOfCoprime p hpN)
        (diamondOp k (ZMod.unitOfCoprime q hqN) f))) ∣[k]
      (T_p_lower p hp.pos : GL (Fin 2) ℚ)) ∣[k]
      (T_p_lower q hq.pos : GL (Fin 2) ℚ)) w := by
    rw [hDD, ← SlashAction.slash_mul, hLC, SlashAction.slash_mul]
  rw [hUU, hC2, hLL, ← hC1]; ring

/-- `T_p` commutes with `T_q` for distinct primes `p ≠ q`. -/
theorem heckeT_p_all_comm_distinct [NeZero N] (k : ℤ)
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    heckeT_p_all (N := N) k p hp * heckeT_p_all k q hq =
      heckeT_p_all k q hq * heckeT_p_all k p hp := by
  ext f z
  show ((heckeT_p_all k p hp (heckeT_p_all k q hq f)) : UpperHalfPlane → ℂ) z =
    ((heckeT_p_all k q hq (heckeT_p_all k p hp f)) : UpperHalfPlane → ℂ) z
  by_cases hpN : Nat.Coprime p N <;> by_cases hqN : Nat.Coprime q N
  · rw [heckeT_p_all_coprime k hp hpN, heckeT_p_all_coprime k hq hqN]
    exact heckeT_p_comm_distinct_both_coprime k hp hq hpq hpN hqN f z
  · rw [heckeT_p_all_coprime_apply k hp hpN (heckeT_p_all k q hq f),
        heckeT_p_all_not_coprime_apply k hq hqN (heckeT_p_all k p hp f),
        heckeT_p_all_coprime_apply k hp hpN f]
    simp only [heckeT_p_fun, Pi.add_apply]
    rw [heckeT_p_all_not_coprime_apply k hq hqN f,
        diamondOp_heckeT_p_all_eq_ut_of_divN k hpN hq hqN f]
    simp only [heckeT_p_ut, SlashAction.add_slash, Finset.sum_add_distrib,
      SlashAction.sum_slash, Pi.add_apply, Finset.sum_apply]
    have hUU := congr_fun (heckeT_p_ut_comm k hp hq hpq (⇑f)) z
    simp only [heckeT_p_ut, SlashAction.sum_slash, Finset.sum_apply] at hUU
    have hC := congr_fun
      (heckeT_p_ut_slash_lower_comm k hq hp (Ne.symm hpq)
        (diamondOp k (ZMod.unitOfCoprime p hpN) f)) z
    simp only [heckeT_p_ut, SlashAction.sum_slash, Finset.sum_apply] at hC
    rw [hUU, hC]
  · rw [heckeT_p_all_not_coprime_apply k hp hpN (heckeT_p_all k q hq f),
        heckeT_p_all_coprime_apply k hq hqN f,
        heckeT_p_all_coprime_apply k hq hqN (heckeT_p_all k p hp f)]
    simp only [heckeT_p_fun, Pi.add_apply]
    rw [heckeT_p_all_not_coprime_apply k hp hpN f,
        diamondOp_heckeT_p_all_eq_ut_of_divN k hqN hp hpN f]
    simp only [heckeT_p_ut, SlashAction.add_slash, Finset.sum_add_distrib,
      SlashAction.sum_slash, Pi.add_apply, Finset.sum_apply]
    have hUU := congr_fun (heckeT_p_ut_comm k hp hq hpq (⇑f)) z
    simp only [heckeT_p_ut, SlashAction.sum_slash, Finset.sum_apply] at hUU
    have hC := congr_fun
      (heckeT_p_ut_slash_lower_comm k hp hq hpq
        (diamondOp k (ZMod.unitOfCoprime q hqN) f)) z
    simp only [heckeT_p_ut, SlashAction.sum_slash, Finset.sum_apply] at hC
    rw [hUU, hC]
  · rw [heckeT_p_all_not_coprime_apply k hp hpN (heckeT_p_all k q hq f),
        heckeT_p_all_not_coprime_apply k hq hqN f,
        heckeT_p_all_not_coprime_apply k hq hqN (heckeT_p_all k p hp f),
        heckeT_p_all_not_coprime_apply k hp hpN f]
    exact congr_fun (heckeT_p_ut_comm k hp hq hpq (⇑f)) z

/-- Diamond operators commute with `diamondOp_n`: `⟨d⟩ · ⟨p⟩_ext = ⟨p⟩_ext · ⟨d⟩`. -/
theorem diamondOp_n_comm_diamondOp [NeZero N] (k : ℤ) (d : (ZMod N)ˣ) (p : ℕ) :
    diamondOp k d * diamondOp_n (N := N) k p =
      diamondOp_n k p * diamondOp k d := by
  by_cases hpN : Nat.Coprime p N
  · rw [diamondOp_n_coprime k hpN, Module.End.mul_eq_comp, ← diamondOp_mul,
        Module.End.mul_eq_comp, ← diamondOp_mul, mul_comm]
  · simp [diamondOp_n_not_coprime k hpN]

/-- `T_{p^r}` commutes with all diamond operators `⟨d⟩`. -/
theorem heckeT_ppow_comm_diamondOp [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (r : ℕ) (d : (ZMod N)ˣ) :
    (diamondOp k d) * heckeT_ppow (N := N) k p hp r =
      heckeT_ppow k p hp r * (diamondOp k d) := by
  induction r using Nat.strongRecOn with
  | _ r ih =>
    match r with
    | 0 => simp [mul_one, one_mul]
    | 1 =>
      rw [heckeT_ppow_one, heckeT_p_all_coprime k hp hpN]
      exact LinearMap.ext fun f ↦ congr_fun (congr_arg DFunLike.coe
        (heckeT_p_comm_diamondOp k p hp hpN d)) f
    | (n + 2) =>
      have hbase : diamondOp k d * heckeT_p_all k p hp =
          heckeT_p_all k p hp * diamondOp k d := by
        rw [heckeT_p_all_coprime k hp hpN]
        exact LinearMap.ext fun f ↦ congr_fun (congr_arg DFunLike.coe
          (heckeT_p_comm_diamondOp k p hp hpN d)) f
      rw [heckeT_ppow_succ_succ, mul_sub, sub_mul]
      congr 1
      · rw [← mul_assoc, hbase, mul_assoc, ih (n + 1) (by omega), ← mul_assoc]
      · rw [mul_smul_comm, smul_mul_assoc]; congr 1
        rw [← mul_assoc, diamondOp_n_comm_diamondOp k d p,
            mul_assoc, ih n (by omega), ← mul_assoc]

/-! ### Character-space preservation

These preservation lemmas hold for **all** indices, including bad primes `p ∣ N` and
composites sharing factors with `N`.  They are proven by direct block induction over the
construction of `T_n` (each building block — `heckeT_p_all`, the diamond, the recurrence —
preserves the eigenspace), *not* via commutation with the diamond operators, so they are
available before any commutativity is established.  This is what lets operator identities be
transported from the Hecke ring `𝕋(Γ₀(N))` per character space and then glued. -/

/-- For `p ∣ N`, the operator `heckeT_p_all k p hp` commutes with every diamond
operator `⟨d⟩`. This is the `p ∣ N` analogue of `heckeT_p_comm_diamondOp`. -/
theorem heckeT_p_all_comm_diamondOp_divN [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : ¬Nat.Coprime p N) (d : (ZMod N)ˣ) :
    (diamondOp k d).comp (heckeT_p_all k p hp) =
    (heckeT_p_all k p hp).comp (diamondOp k d) := by
  obtain ⟨g, hg⟩ := Gamma0MapUnits_surjective (N := N) d
  ext f z
  show (diamondOp k d (heckeT_p_all k p hp f)) z =
    (heckeT_p_all k p hp (diamondOp k d f)) z
  rw [diamondOp_eq_diamondOpAux k d g hg]
  show (⇑(heckeT_p_all k p hp f) ∣[k] mapGL ℝ (g : SL(2, ℤ))) z =
    ⇑(heckeT_p_all k p hp (diamondOpAux k g f)) z
  rw [heckeT_p_all_not_coprime_apply k hp hpN f,
    heckeT_p_all_not_coprime_apply k hp hpN (diamondOpAux k g f)]
  exact congr_fun (heckeT_p_ut_orbit_comm_gamma0_fun k p hp hpN f g) z

/-- Unified diamond commutation for `heckeT_p_all`, covering both the coprime and
non-coprime cases. -/
theorem heckeT_p_all_comm_diamondOp [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (d : (ZMod N)ˣ) :
    (diamondOp k d).comp (heckeT_p_all k p hp) =
    (heckeT_p_all k p hp).comp (diamondOp k d) := by
  by_cases hpN : Nat.Coprime p N
  · rw [heckeT_p_all_coprime k hp hpN]
    exact heckeT_p_comm_diamondOp k p hp hpN d
  · exact heckeT_p_all_comm_diamondOp_divN k p hp hpN d

/-- `heckeT_p_all k p hp` preserves the modular-form character space
`M_k(Γ₁(N), χ)`, unconditionally on `p` and `χ`. -/
theorem heckeT_p_all_preserves_modFormCharSpace [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (χ : (ZMod N)ˣ →* ℂˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    heckeT_p_all k p hp f ∈ modFormCharSpace k χ := by
  rw [mem_modFormCharSpace_iff] at hf ⊢
  intro d
  have h1 : diamondOpHom k d (heckeT_p_all k p hp f) =
      heckeT_p_all k p hp (diamondOpHom k d f) := by
    show (diamondOp k d).comp (heckeT_p_all k p hp) f =
      (heckeT_p_all k p hp).comp (diamondOp k d) f
    rw [heckeT_p_all_comm_diamondOp]
  rw [h1, hf d, map_smul]

/-- The diamond operator `⟨n⟩` preserves each character space `M_k(Γ₁(N), χ)` for every
index: at coprime `n` it acts by the scalar `χ(n)`, otherwise it vanishes. -/
theorem diamondOp_n_preserves_modFormCharSpace [NeZero N] (k : ℤ) (n : ℕ) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    diamondOp_n k n f ∈ modFormCharSpace k χ := by
  by_cases h : Nat.Coprime n N
  · rw [diamondOp_n_coprime k h]
    have heig : diamondOp k (ZMod.unitOfCoprime n h) f =
        (↑(χ (ZMod.unitOfCoprime n h)) : ℂ) • f :=
      (mem_modFormCharSpace_iff k χ f).mp hf _
    rw [heig]
    exact Submodule.smul_mem _ _ hf
  · rw [diamondOp_n_not_coprime k h]
    simp

/-- `T_{p^r}` preserves each character space, for **every** prime `p` (including
`p ∣ N`).  Direct induction over the defining recurrence. -/
theorem heckeT_ppow_preserves_modFormCharSpace [NeZero N] (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (r : ℕ) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    heckeT_ppow k p hp r f ∈ modFormCharSpace k χ := by
  induction r using Nat.strong_induction_on generalizing f with
  | _ r ih =>
    match r, ih with
    | 0, _ => simpa using hf
    | 1, _ =>
      rw [heckeT_ppow_one]
      exact heckeT_p_all_preserves_modFormCharSpace k p hp χ hf
    | (r + 2), ih =>
      rw [heckeT_ppow_succ_succ]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply]
      refine Submodule.sub_mem _
        (heckeT_p_all_preserves_modFormCharSpace k p hp χ (ih (r + 1) (by omega) hf)) ?_
      exact Submodule.smul_mem _ _
        (diamondOp_n_preserves_modFormCharSpace k p χ (ih r (by omega) hf))

/-- `T_n` preserves each character space `M_k(Γ₁(N), χ)` for **every** positive `n`
(no coprimality with the level required).  Induction over the `minFac`-peeling
assembly of `T_n`. -/
theorem heckeT_n_preserves_modFormCharSpace_all [NeZero N] (k : ℤ) (n : ℕ) [NeZero n]
    (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    heckeT_n k n f ∈ modFormCharSpace k χ := by
  suffices H : ∀ m : ℕ, (hm0 : NeZero m) →
      ∀ {g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}, g ∈ modFormCharSpace k χ →
        heckeT_n k m g ∈ modFormCharSpace k χ from H n ‹_› hf
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm0 g hg
    haveI := hm0
    rcases eq_or_ne m 1 with rfl | hm1
    · rw [heckeT_n_one]
      simpa using hg
    · have hm : 1 < m := by
        have := NeZero.ne m
        omega
      rw [heckeT_n_unfold k m hm]
      simp only [Module.End.mul_apply]
      set p := m.minFac with hp_def
      have hp : Nat.Prime p := Nat.minFac_prime (by omega)
      set v := m.factorization p with hv_def
      have hv_pos : 0 < v :=
        hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd m)
      have hdiv_pos : 0 < m / p ^ v :=
        Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p)) (pow_pos hp.pos v)
      have hdiv_lt : m / p ^ v < m :=
        Nat.div_lt_self (by omega) (Nat.one_lt_pow hv_pos.ne' hp.one_lt)
      exact heckeT_ppow_preserves_modFormCharSpace k p hp v χ
        (ih _ hdiv_lt ⟨hdiv_pos.ne'⟩ hg)

/-- `T_n` preserves the character space `M_k(Γ₁(N), χ)` for `n` coprime to `N`.

A thin wrapper over the general `heckeT_n_preserves_modFormCharSpace_all` (which holds for
**all** `n`); kept under its original name and signature for downstream consumers.

Reference: [DS] Prop 5.2.2(b) generalised. -/
theorem heckeT_n_preserves_charSpace [NeZero N] (k : ℤ) (n : ℕ) [NeZero n]
    (_hn : Nat.Coprime n N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    heckeT_n k n f ∈ modFormCharSpace k χ :=
  heckeT_n_preserves_modFormCharSpace_all k n χ hf

end HeckeRing.GL2

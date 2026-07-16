/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.AdjointTheory.DoubleCosetAdjoint
import LeanModularForms.HeckeRIngs.GL2.Fricke
import LeanModularForms.HeckeRIngs.GL2.Newforms.BadPrimeFDTiling
import LeanModularForms.HeckeRIngs.GL2.Newforms.LevelRaiseComm

/-!
# The bad-prime trace ↔ Fricke identity (T006-b-L4-FD-e.1, DS Ex 5.5.1(b))

For a prime `p ∣ N`, the `Γ_p(diag(p,1))`-coset trace of `g ∣ diag(p,1)` equals the Fricke
conjugate `(frickeScalar)⁻¹ · w_N U_p w_N g`.  This is the bad-prime analogue of the coprime
`ds_traceSlash_Gamma_p_α_T_p_lower_eq_diamond_inv_heckeT_p` (`DeltaBSystem.lean`), which lands
on the good-prime adjoint `⟨p⟩⁻¹ T_p g`.  At a bad prime there is no `⟨p⟩`/`T_p`; the adjoint
is genuinely the Fricke conjugate (Diamond–Shurman Exercise 5.5.1(b)).

The crux is the **matrix identity** `diag(p,1) · [1,0;-jN,1] = adj(δ_j) = w_N⁻¹ · [1,j;0,p] · w_N`
(`frickeGL_mul_adj_lunipRep_mul_frickeGL_inv`, `Fricke.lean`), summed over the
`Γ_p(diag(p,1))\Γ₁` transversal `{[1,0;-jN,1] : j ∈ Fin p}`.  Because the diagonal `diag(p,1)`
maps the lower shear `[1,0;-jN,1]` *exactly* onto `adj(δ_j)` (no `Γ₀(N)` correction, unlike the
coprime case), summing slashes turns the trace into
`(U_p(g ∣ w_N⁻¹)) ∣ w_N = (frickeScalar)⁻¹ · (U_p(g ∣ w_N)) ∣ w_N`, the Fricke-conjugated `U_p`.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.5 (Ex 5.5.1(b))
-/

noncomputable section

open CongruenceSubgroup Matrix Matrix.SpecialLinearGroup CuspForm Pointwise ConjAct
open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

/-! ### The lower shear `[1,0;m,1]` and its `Γ₁`-data -/

/-- The lower-unipotent shear `[1,0;m,1] ∈ SL₂(ℤ)`.  These are the `Γ_p(diag(p,1))\Γ₁`
transversal reps (with `m = -jN`, `j ∈ Fin p`) for the bad-prime trace. -/
private def lowerUniSL (m : ℤ) : SL(2, ℤ) :=
  ⟨!![1, 0; m, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[simp] private lemma lowerUniSL_val (m : ℤ) :
    ((lowerUniSL m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; m, 1] := rfl

@[simp] private lemma lowerUniSL_mapQ_coe (m : ℤ) :
    ((mapGL ℚ (lowerUniSL m) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      !![1, 0; (m : ℚ), 1] := by
  rw [show ((mapGL ℚ (lowerUniSL m) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (!![1, 0; m, 1]).map Int.cast from
    (Matrix.SpecialLinearGroup.mapGL_coe_matrix _).trans (by rw [algebraMap_int_eq]; rfl)]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply, Matrix.of_apply]

omit [NeZero N] in
private lemma lowerUniSL_mem_Gamma1 (m : ℤ) (hm : (N : ℤ) ∣ m) :
    lowerUniSL m ∈ Gamma1 N := by
  rw [Gamma1_mem]; refine ⟨?_, ?_, ?_⟩
  · show ((lowerUniSL m).val 0 0 : ZMod N) = 1; simp
  · show ((lowerUniSL m).val 1 1 : ZMod N) = 1; simp
  · show ((lowerUniSL m).val 1 0 : ZMod N) = 0
    simp only [lowerUniSL_val, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hm

omit [NeZero N] in
/-- `(1,0)`-entry of `lowerUniSL(a)⁻¹ · lowerUniSL(b)` is `b - a`. -/
private lemma lowerUniSL_inv_mul_entry (a b : ℤ) :
    (((lowerUniSL a)⁻¹ * lowerUniSL b).val 1 0 : ℤ) = b - a := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    lowerUniSL_val, Matrix.adjugate_fin_two_of, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

omit [NeZero N] in
/-- `(1,0)`-entry of `lowerUniSL(a)⁻¹ · γ` is `γ₁₀ - a·γ₀₀`. -/
private lemma lowerUniSL_inv_mul_gamma_entry (a : ℤ) (γ : SL(2, ℤ)) :
    (((lowerUniSL a)⁻¹ * γ).val 1 0 : ℤ) = γ.val 1 0 - a * γ.val 0 0 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    lowerUniSL_val, Matrix.adjugate_fin_two_of, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-! ### Strong membership characterization of `Γ_p(diag(p,1))` at bad primes

Unlike the coprime case (`Γ_p(diag(p,1)) = Γ₁ ⊓ Γ₀(p)`, i.e. `p ∣ γ₁₀`), at a bad prime the
condition is the *stronger* `pN ∣ γ₁₀` (the conjugate's lower-left entry `γ₁₀/p` must itself be
`≡ 0 mod N` to land in `Γ₁(N)`).  For `p ∣ N` these differ: `Γ₁` already gives `N ∣ γ₁₀ ⟹ p ∣ γ₁₀`,
so `Γ₀(p)` is no obstruction; the real index drops to `p` via `pN ∣ γ₁₀`. -/

omit [NeZero N] in
/-- **Forward strong membership.** `γ ∈ Γ_p(diag(p,1)) ⟹ pN ∣ γ₁₀` (no coprimality): the
conjugate `A·γ·A⁻¹` has lower-left `γ₁₀/p`, which is integral *and* `≡ 0 mod N` (since the
conjugate lands in `Γ₁(N)`), so `pN ∣ γ₁₀`. -/
private lemma mem_Gamma_p_α_T_p_lower_pN (p : ℕ) (hp : 0 < p)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma_p_α (N := N) (T_p_lower p hp)) :
    ((p : ℤ) * N) ∣ γ.val 1 0 := by
  have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  obtain ⟨hconj, _hγ1⟩ := Subgroup.mem_inf.mp hγ
  obtain ⟨y, hy_mem, hy_eq⟩ := mem_conjGL.mp hconj
  have hentry : ((y.val 1 0 : ℤ) : ℝ) = ((γ.val 1 0 : ℤ) : ℝ) / (p : ℝ) := by
    have h1 : ((toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) y)) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        !![((γ.val 0 0 : ℤ) : ℝ), (p : ℝ) * ((γ.val 0 1 : ℤ) : ℝ);
           ((γ.val 1 0 : ℤ) : ℝ) / (p : ℝ), ((γ.val 1 1 : ℤ) : ℝ)] := by
      rw [hy_eq, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
        conj_T_p_lower_real_val p hp γ]
    have h10 := congrFun (congrFun h1 1) 0
    simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] using h10
  have hpk : (γ.val 1 0 : ℤ) = (y.val 1 0 : ℤ) * (p : ℤ) := by
    have : ((γ.val 1 0 : ℤ) : ℝ) = ((y.val 1 0 : ℤ) : ℝ) * (p : ℝ) := by rw [hentry]; field_simp
    exact_mod_cast this
  obtain ⟨_, _, hyc⟩ := (Gamma1_mem N y).mp hy_mem
  have hN_dvd_y : (N : ℤ) ∣ y.val 1 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hyc
  obtain ⟨c, hc⟩ := hN_dvd_y
  exact ⟨c, by rw [hpk, hc]; ring⟩

omit [NeZero N] in
/-- **Reverse strong membership.** `γ ∈ Γ₁(N)` with `pN ∣ γ₁₀ ⟹ γ ∈ Γ_p(diag(p,1))`: the
witness `y = [[a, p·b], [γ₁₀/p, d]]` lies in `Γ₁(N)` (its lower-left `γ₁₀/p ≡ 0 mod N`) and
conjugates to `γ` under `diag(p,1)`. -/
private lemma mem_Gamma_p_α_T_p_lower_pN_mpr (p : ℕ) (hp : 0 < p)
    {γ : SL(2, ℤ)} (hγ₁ : γ ∈ Gamma1 N) (hdvd : ((p : ℤ) * N) ∣ γ.val 1 0) :
    γ ∈ Gamma_p_α (N := N) (T_p_lower p hp) := by
  have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  refine Subgroup.mem_inf.mpr ⟨?_, hγ₁⟩
  rw [mem_conjGL]
  obtain ⟨c, hc⟩ := hdvd
  have hk : γ.val 1 0 = (p : ℤ) * (N * c) := by rw [hc]; ring
  have hkN : ((N * c : ℤ) : ZMod N) = 0 := by push_cast; simp
  obtain ⟨ha, hd, _hc1⟩ := (Gamma1_mem N γ).mp hγ₁
  have hdet : (!![γ.val 0 0, (p : ℤ) * γ.val 0 1; N * c, γ.val 1 1] :
      Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    have hγdet : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = 1 := by
      have := γ.property; rw [Matrix.det_fin_two] at this; linarith [this]
    have : (p : ℤ) * γ.val 0 1 * (N * c) = γ.val 0 1 * γ.val 1 0 := by rw [hk]; ring
    linarith [hγdet, this]
  set y : SL(2, ℤ) := ⟨!![γ.val 0 0, (p : ℤ) * γ.val 0 1; N * c, γ.val 1 1], hdet⟩ with hy_def
  have hy_mem : y ∈ Gamma1 N := by
    rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · show ((y.val 0 0 : ℤ) : ZMod N) = 1
      simp only [hy_def, Matrix.SpecialLinearGroup.coe_mk, Matrix.cons_val', Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one]; exact ha
    · show ((y.val 1 1 : ℤ) : ZMod N) = 1
      simp only [hy_def, Matrix.SpecialLinearGroup.coe_mk, Matrix.cons_val', Matrix.of_apply,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]; exact hd
    · show ((y.val 1 0 : ℤ) : ZMod N) = 0
      simp only [hy_def, Matrix.SpecialLinearGroup.coe_mk, Matrix.cons_val', Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      exact hkN
  refine ⟨y, hy_mem, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    conj_T_p_lower_real_val p hp γ]
  have hyval : Subtype.val y = !![γ.val 0 0, (p : ℤ) * γ.val 0 1; N * c, γ.val 1 1] := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, hyval, hk]
  try field_simp

/-! ### The bad-prime relative index `[Γ₁(N) : Γ_p(diag(p,1))] = p`

The `Fin p` lower shears `{[1,0;-jN,1] : j ∈ Fin p}` form a complete `Γ_p(diag(p,1))`-transversal
of `Γ₁(N)` (distinctness from `pN ∤ (i-j)N`; covering by adjusting `γ₁₀/N mod p`). -/

/-- **[T006-b-L4-FD-e.idx]** `[Γ₁(N) : Γ_p(diag(p,1))] = p` for `p ∣ N`.  Bad-prime analogue of
the coprime `relIndex_Gamma_p_α_T_p_lower` (`p + 1`); the `M_∞` tile is absent. -/
private theorem relIndex_Gamma_p_α_T_p_lower_bad (p : ℕ) (hp : Nat.Prime p)
    (hpN : ¬ Nat.Coprime p N) :
    (Gamma_p_α (N := N) (T_p_lower p hp.pos)).relIndex (Gamma1 N) = p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hpdvd : p ∣ N := by rw [hp.coprime_iff_not_dvd, not_not] at hpN; exact hpN
  have hred : ∀ (x : ℤ), (x : ZMod N) = 1 → (x : ZMod p) = 1 := fun x h ↦ by
    have := congrArg (ZMod.castHom hpdvd (ZMod p)) h; rwa [map_intCast, map_one] at this
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  set K := Gamma_p_α (N := N) (T_p_lower p hp.pos) with hK
  set e : Fin p → (Gamma1 N) ⧸ (K.subgroupOf (Gamma1 N)) :=
    fun j ↦ QuotientGroup.mk ⟨lowerUniSL (-(j.val : ℤ) * N),
      lowerUniSL_mem_Gamma1 _ ⟨-(j.val : ℤ), by ring⟩⟩ with he_def
  have hbij : Function.Bijective e := by
    constructor
    · -- Injectivity via distinctness: `pN ∤ (b₁ - b₂)N`.
      intro b₁ b₂ hb
      by_contra hne
      rw [he_def, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hb
      simp only [InvMemClass.coe_inv, MulMemClass.coe_mul] at hb
      have hdvd := mem_Gamma_p_α_T_p_lower_pN p hp.pos hb
      rw [lowerUniSL_inv_mul_entry] at hdvd
      have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
      obtain ⟨c, hc⟩ := hdvd
      have hpd : (p : ℤ) ∣ ((b₁.val : ℤ) - b₂.val) :=
        ⟨c, mul_right_cancel₀ hN0 (by linear_combination hc)⟩
      apply hne; apply Fin.ext
      obtain ⟨d, hd⟩ := hpd
      have hb₁ := b₁.isLt; have hb₂ := b₂.isLt
      have hd0 : d = 0 := by nlinarith [hp.pos, hb₁, hb₂]
      have : (b₁.val : ℤ) = b₂.val := by rw [hd0, mul_zero] at hd; omega
      exact_mod_cast this
    · -- Surjectivity: `γ ≡ [1,0;-jN,1]` with `-j ≡ γ₁₀/N (mod p)`.
      intro q
      induction q using QuotientGroup.induction_on with | _ γ => ?_
      obtain ⟨ha, _hd, hc⟩ := (Gamma1_mem N (γ : SL(2, ℤ))).mp γ.property
      have hN_dvd : (N : ℤ) ∣ (γ : SL(2, ℤ)).val 1 0 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hc
      obtain ⟨c', hc'⟩ := hN_dvd
      set jval : ℕ := (((-c' : ℤ) : ZMod p)).val with hjval_def
      have hjval_lt : jval < p := hjval_def ▸ ZMod.val_lt _
      refine ⟨⟨jval, hjval_lt⟩, ?_⟩
      rw [he_def, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simp only [InvMemClass.coe_inv, MulMemClass.coe_mul]
      apply mem_Gamma_p_α_T_p_lower_pN_mpr p hp.pos
      · exact mul_mem ((Gamma1 N).inv_mem
          (lowerUniSL_mem_Gamma1 _ ⟨-(jval : ℤ), by ring⟩)) γ.property
      · rw [lowerUniSL_inv_mul_gamma_entry, hc',
          show (N : ℤ) * c' - (-(jval : ℤ) * N) * (γ : SL(2, ℤ)).val 0 0
              = (N : ℤ) * (c' + (jval : ℤ) * (γ : SL(2, ℤ)).val 0 0) by ring,
          show (p : ℤ) * N = N * p by ring]
        apply mul_dvd_mul_left
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [hred _ ha, mul_one]
        have hj' : ((jval : ZMod p)) = -(c' : ZMod p) := by
          have hj : ((jval : ℤ) : ZMod p) = ((-c' : ℤ) : ZMod p) := by
            rw [hjval_def]; push_cast; rw [ZMod.natCast_val, ZMod.cast_id]
          push_cast at hj ⊢; rw [hj]
        rw [hj']; ring
  rw [← Nat.card_congr (Equiv.ofBijective e hbij), Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The SL-level fiber cardinality of `slGamma_p_αToGamma1` at `diag(p,1)` for a bad prime is
`p` (versus `p + 1` in the coprime case). -/
private theorem slGamma_p_αToGamma1_fiberCard_T_p_lower_bad (p : ℕ) (hp : Nat.Prime p)
    (hpN : ¬ Nat.Coprime p N) :
    slGamma_p_αToGamma1_fiberCard (N := N) (T_p_lower p hp.pos) = p := by
  rw [slGamma_p_αToGamma1_fiberCard_eq_relIndex, relIndex_Gamma_p_α_T_p_lower_bad p hp hpN]

/-! ### The trace unfolding over the bad transversal -/

/-- **Bad transversal trace unfolding.** For a `Γ_p(diag(p,1))`-slash-invariant `G`, the
partial trace over the fiber above any `q'` is the sum over the `Fin p` lower-shear transversal:
`tr_{q'} G = ∑_{j : Fin p} G ∣[k] [1,0;-jN,1]`.  Bad-prime analogue of
`ds_p_plus_one_family_traceSlash_eq` (`Fin p`, no `M_∞`). -/
private lemma badTraceSlash_eq (p : ℕ) (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (G : UpperHalfPlane → ℂ)
    (hG : ∀ γ ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos), G ∣[k] (γ : SL(2, ℤ)) = G)
    (q' : SL(2, ℤ) ⧸ Gamma1 N) :
    traceSlash_Gamma_p_α (N := N) (k := k) (T_p_lower p hp.pos) G q' =
      ∑ j : Fin p, G ∣[k] ((lowerUniSL (-(j.val : ℤ) * N) : SL(2, ℤ))) := by
  classical
  rw [traceSlash_Gamma_p_α]
  set fib : Finset (SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp.pos)) :=
    Finset.univ.filter (fun q ↦ slGamma_p_αToGamma1 (N := N) (T_p_lower p hp.pos) q = q')
    with hfib_def
  -- The transversal map into the fiber.
  set δ : Fin p → SL(2, ℤ) := fun j ↦ lowerUniSL (-(j.val : ℤ) * N) with hδ_def
  set e : Fin p → SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp.pos) := fun j ↦
    QuotientGroup.mk ((q'.out : SL(2, ℤ)) * (δ j : SL(2, ℤ))⁻¹) with he_def
  have hδ_mem : ∀ j, δ j ∈ Gamma1 N := fun j ↦
    lowerUniSL_mem_Gamma1 _ ⟨-(j.val : ℤ), by ring⟩
  -- (i) membership in the fiber.
  have he_mem : ∀ j, e j ∈ fib := by
    intro j
    rw [hfib_def, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [he_def, slGamma_p_αToGamma1_mk]
    conv_rhs => rw [← q'.out_eq]
    rw [QuotientGroup.eq,
      show ((q'.out : SL(2, ℤ)) * (δ j : SL(2, ℤ))⁻¹)⁻¹ * q'.out = (δ j : SL(2, ℤ)) by group]
    exact hδ_mem j
  -- (ii) injectivity via distinctness mod left-`Γ_p`.
  have he_inj : ∀ j₁ j₂, e j₁ = e j₂ → j₁ = j₂ := by
    intro j₁ j₂ hjj
    rw [he_def, QuotientGroup.eq] at hjj
    rw [show ((q'.out : SL(2, ℤ)) * (δ j₁)⁻¹)⁻¹ * ((q'.out : SL(2, ℤ)) * (δ j₂)⁻¹) =
      (δ j₁ : SL(2, ℤ)) * (δ j₂)⁻¹ by group] at hjj
    -- `(δ j₁ · δ j₂⁻¹)₁₀ = -j₁N - (-j₂N) = (j₂ - j₁)N`; `pN ∤ ⟹ j₁ = j₂`.
    have hdvd := mem_Gamma_p_α_T_p_lower_pN p hp.pos hjj
    have hentry : ((δ j₁ : SL(2, ℤ)) * (δ j₂)⁻¹).val 1 0 =
        (-(j₁.val : ℤ) * N) - (-(j₂.val : ℤ) * N) := by
      rw [hδ_def]
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        lowerUniSL_val, Matrix.adjugate_fin_two_of, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      ring
    rw [hentry] at hdvd
    have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
    obtain ⟨c, hc⟩ := hdvd
    have hpd : (p : ℤ) ∣ ((j₂.val : ℤ) - j₁.val) :=
      ⟨c, mul_right_cancel₀ hN0 (by linear_combination hc)⟩
    apply Fin.ext
    obtain ⟨d, hd⟩ := hpd
    have hj₁ := j₁.isLt; have hj₂ := j₂.isLt
    have hd0 : d = 0 := by nlinarith [hp.pos, hj₁, hj₂]
    have : (j₂.val : ℤ) = j₁.val := by rw [hd0, mul_zero] at hd; omega
    exact_mod_cast this.symm
  -- (iii) the connecting-element slash identity.
  have he_conn : ∀ j, G ∣[k] (((e j).out : SL(2, ℤ))⁻¹ * (q'.out : SL(2, ℤ))) =
      G ∣[k] (δ j : SL(2, ℤ)) := by
    intro j
    set out := ((e j).out : SL(2, ℤ)) with hout
    have hquot : (QuotientGroup.mk out :
        SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp.pos)) =
        QuotientGroup.mk ((q'.out : SL(2, ℤ)) * (δ j : SL(2, ℤ))⁻¹) := by
      rw [hout, QuotientGroup.out_eq']
    rw [QuotientGroup.eq] at hquot
    -- `(out⁻¹ · q'.out) · (δ j)⁻¹ ∈ Γ_p`, so the slash is constant on the coset.
    have hmem : (out⁻¹ * (q'.out : SL(2, ℤ))) * (δ j : SL(2, ℤ))⁻¹ ∈
        Gamma_p_α (N := N) (T_p_lower p hp.pos) := by
      rwa [show out⁻¹ * ((q'.out : SL(2, ℤ)) * (δ j)⁻¹) =
        (out⁻¹ * (q'.out : SL(2, ℤ))) * (δ j : SL(2, ℤ))⁻¹ by group] at hquot
    have hslash := hG _ hmem
    rw [show G ∣[k] (out⁻¹ * (q'.out : SL(2, ℤ))) =
        (G ∣[k] ((out⁻¹ * (q'.out : SL(2, ℤ))) * (δ j : SL(2, ℤ))⁻¹)) ∣[k] (δ j : SL(2, ℤ)) by
      rw [← SlashAction.slash_mul,
        show (out⁻¹ * (q'.out : SL(2, ℤ))) * (δ j : SL(2, ℤ))⁻¹ * (δ j : SL(2, ℤ)) =
          out⁻¹ * (q'.out : SL(2, ℤ)) by group], hslash]
  -- (iv) cardinality.
  have hcard : fib.card = Fintype.card (Fin p) := by
    rw [hfib_def, Fintype.card_fin]
    refine Eq.trans ?_ ((slGamma_p_αToGamma1_fiberCard_eq (N := N) (T_p_lower p hp.pos) q').trans
      (slGamma_p_αToGamma1_fiberCard_T_p_lower_bad p hp hpN))
    congr 1
    ext q
    simp
  -- Assemble the sum-bijection.
  refine (Finset.sum_bij (fun (j : Fin p) _ ↦ e j) (fun j _ ↦ he_mem j)
    (fun j₁ _ j₂ _ h ↦ he_inj j₁ j₂ h) ?_ (fun j _ ↦ (he_conn j).symm)).symm
  intro b hb
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (fun j (_ : j ∈ Finset.univ) ↦ e j)
    (fun j _ ↦ he_mem j) (fun j₁ j₂ _ _ h ↦ he_inj j₁ j₂ h)
    (by rw [hcard]; exact le_of_eq (Finset.card_univ).symm)
  obtain ⟨a, ha, hab⟩ := hsurj b hb
  exact ⟨a, ha, hab.symm⟩

/-! ### The per-class double-coset identity and the Fricke assembly -/

omit [NeZero N] in
/-- The clean bad-prime matrix identity: `diag(p,1) · [1,0;-bN,1] = adj(δ_b)` (`δ_b = [1,0;Nb,p]`,
det `p`) — *exactly*, with no `Γ₀(N)` correction (unlike the coprime case). -/
private lemma perClass_matrix (p : ℕ) (hp : 0 < p) (b : ℕ) :
    (T_p_lower p hp : GL (Fin 2) ℚ) * (mapGL ℚ (lowerUniSL (-(b : ℤ) * N)) : GL (Fin 2) ℚ) =
      GL_adjugate (lunipRep (N := N) p hp b) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, GL_adjugate_val, lunipRep_coe,
    Matrix.adjugate_fin_two_of, T_p_lower_coe, lowerUniSL_mapQ_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/-- `adj(δ_b) = w_N⁻¹ · [1,b;0,p] · w_N` (the Fricke conjugation, `w_N² = -N·I` central). -/
private lemma adj_lunipRep_eq_frickeConj (p : ℕ) (hp : 0 < p) (b : ℕ) :
    GL_adjugate (lunipRep (N := N) p hp b) =
      (frickeGL N)⁻¹ * T_p_upper p hp b * frickeGL N := by
  have h := frickeGL_mul_adj_lunipRep_mul_frickeGL_inv (N := N) p hp b
  rw [← h]; group

/-- **Per-class Fricke identity.** Slashing `g ∣ diag(p,1)` by the transversal shear `[1,0;-bN,1]`
equals slashing `g ∣ w_N⁻¹` by `U_p`-rep `[1,b;0,p]` then by `w_N`. -/
private lemma perClass_slash (p : ℕ) (hp : 0 < p) (b : ℕ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑g ∣[k] (glMap (T_p_lower p hp) : GL (Fin 2) ℝ)) ∣[k]
        ((lowerUniSL (-(b : ℤ) * N) : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      ((⇑g ∣[k] ((frickeGL N)⁻¹ : GL (Fin 2) ℚ)) ∣[k]
        (T_p_upper p hp b : GL (Fin 2) ℚ)) ∣[k] (frickeGL N : GL (Fin 2) ℚ) := by
  rw [show (((lowerUniSL (-(b : ℤ) * N) : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
        (glMap ((mapGL ℚ : SL(2, ℤ) →* GL (Fin 2) ℚ) (lowerUniSL (-(b : ℤ) * N))) : GL (Fin 2) ℝ)
      from (glMap_mapGL_Q_eq_mapGL_R (lowerUniSL (-(b : ℤ) * N))).symm,
    show (⇑g ∣[k] (glMap (T_p_lower p hp) : GL (Fin 2) ℝ)) =
        ⇑g ∣[k] (T_p_lower p hp : GL (Fin 2) ℚ) from rfl,
    show (⇑g ∣[k] (T_p_lower p hp : GL (Fin 2) ℚ)) ∣[k]
        (glMap ((mapGL ℚ : SL(2, ℤ) →* GL (Fin 2) ℚ) (lowerUniSL (-(b : ℤ) * N))) : GL (Fin 2) ℝ) =
        ⇑g ∣[k] ((T_p_lower p hp) * (mapGL ℚ (lowerUniSL (-(b : ℤ) * N))) : GL (Fin 2) ℚ) by
      rw [SlashAction.slash_mul]; rfl,
    perClass_matrix p hp b, adj_lunipRep_eq_frickeConj p hp b,
    SlashAction.slash_mul, SlashAction.slash_mul]

/-- **Bad-prime `U_p` expansion.** `⇑(T_p f) = ∑_{b : Fin p} ⇑f ∣[k] [1,b;0,p]` for `p ∣ N`. -/
private lemma badUp_coe_eq_sum (p : ℕ) [NeZero p] (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(heckeT_n_cusp k p h) : UpperHalfPlane → ℂ) =
      ∑ b : Fin p, (⇑h ∣[k] (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ)) := by
  have h1 : (⇑(heckeT_n_cusp k p h) : UpperHalfPlane → ℂ) =
      ⇑(heckeT_n k p h.toModularForm') := by rw [← heckeT_n_cusp_toModularForm']; rfl
  rw [h1, heckeT_n_prime k hp, heckeT_p_all, dif_neg hpN]
  show heckeT_p_ut k p hp.pos (⇑h.toModularForm') = _
  rw [heckeT_p_ut]
  show (∑ b ∈ Finset.range p, ⇑h ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) = _
  rw [Finset.sum_range fun b ↦ ⇑h ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)]

/-- `g ∣ w_N⁻¹ = (frickeScalar)⁻¹ • (g ∣ w_N)` (from `w_N² = frickeScalar`). -/
private lemma g_slash_frickeInv (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑g ∣[k] ((frickeGL N)⁻¹ : GL (Fin 2) ℚ)) =
      (frickeScalar N k)⁻¹ • (⇑(frickeOperatorCusp k g) : UpperHalfPlane → ℂ) := by
  have hsq : ((⇑g ∣[k] ((frickeGL N)⁻¹ : GL (Fin 2) ℚ)) ∣[k]
      (frickeGL N * frickeGL N : GL (Fin 2) ℚ)) = ⇑g ∣[k] (frickeGL N : GL (Fin 2) ℚ) := by
    rw [← SlashAction.slash_mul,
      show (frickeGL N)⁻¹ * (frickeGL N * frickeGL N) = frickeGL N by group]
  rw [frickeGL_sq_slash] at hsq
  rw [frickeOperatorCusp_coe, eq_comm, inv_smul_eq_iff₀ (frickeScalar_ne_zero (N := N) k), eq_comm]
  exact hsq

/-! ### The main theorem -/

/-- **[T006-b-L4-FD-e.1]** The bad-prime trace ↔ Fricke identity (DS Ex 5.5.1(b)).  The
`Γ_p(diag(p,1))`-coset trace of `g ∣ diag(p,1)` equals the (unfolded) bad-prime Petersson
adjoint `U_p* g = (frickeScalar)⁻¹ · w_N U_p w_N g`.  Bad-prime analogue of
`ds_traceSlash_Gamma_p_α_T_p_lower_eq_diamond_inv_heckeT_p`, landing on the Fricke conjugate
instead of `⟨p⟩⁻¹ T_p g`. -/
theorem traceSlash_badPrime_eq_badUpAdjoint
    (p : ℕ) [NeZero p] (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q₀ : SL(2, ℤ) ⧸ Gamma1 N) :
    traceSlash_Gamma_p_α (N := N) (k := k) (T_p_lower p hp.pos)
      (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) q₀ =
    (frickeScalar N k)⁻¹ •
      (⇑(frickeOperatorCusp k (heckeT_n_cusp k p (frickeOperatorCusp k g)))) := by
  -- `g ∣ A` is `Γ_p(A)`-slash-invariant.
  have hG_slash : ∀ γ ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos),
      (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ∣[k] (γ : SL(2, ℤ)) =
        ⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) := by
    intro γ hγ
    rw [ModularForm.SL_slash,
      show (((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ) from rfl]
    exact slash_α_Gamma_p_α_invariant_cuspForm (T_p_lower p hp.pos) g hγ
  -- (1) Trace unfolding over the bad transversal.
  rw [badTraceSlash_eq p hp hpN _ hG_slash q₀]
  -- (2) Per-class Fricke identity, termwise.
  rw [show (∑ j : Fin p, (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ∣[k]
        ((lowerUniSL (-(j.val : ℤ) * N) : SL(2, ℤ)))) =
      ∑ b : Fin p, ((⇑g ∣[k] ((frickeGL N)⁻¹ : GL (Fin 2) ℚ)) ∣[k]
        (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ)) ∣[k] (frickeGL N : GL (Fin 2) ℚ) from
    Finset.sum_congr rfl fun b _ ↦ perClass_slash p hp.pos b.val g]
  -- (3) Fricke assembly.
  set c := frickeScalar N k with hc
  set h := frickeOperatorCusp k g with hh
  rw [g_slash_frickeInv g, ← hh]
  rw [show (∑ b : Fin p, (((c⁻¹ • (⇑h : UpperHalfPlane → ℂ)) ∣[k]
        (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ)) ∣[k] (frickeGL N : GL (Fin 2) ℚ))) =
      ∑ b : Fin p, c⁻¹ • ((⇑h ∣[k] (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ)) ∣[k]
        (frickeGL N : GL (Fin 2) ℚ)) from
    Finset.sum_congr rfl fun b _ ↦ by
      rw [smul_slash_pos_det k c⁻¹ _ _ (T_p_upper_det_pos p hp.pos b.val),
        smul_slash_pos_det k c⁻¹ _ _ frickeGL_det_pos]]
  rw [← Finset.smul_sum]
  congr 1
  show (∑ b : Fin p, ((⇑h ∣[k] (T_p_upper p hp.pos b.val : GL (Fin 2) ℚ)) ∣[k]
      (frickeGL N : GL (Fin 2) ℚ))) = ⇑(frickeOperatorCusp k (heckeT_n_cusp k p h))
  rw [show (⇑(frickeOperatorCusp k (heckeT_n_cusp k p h)) : UpperHalfPlane → ℂ) =
      ⇑(heckeT_n_cusp k p h) ∣[k] (frickeGL N : GL (Fin 2) ℚ) from frickeOperatorCusp_coe k _,
    badUp_coe_eq_sum p hp hpN h, SlashAction.sum_slash]

end HeckeRing.GL2

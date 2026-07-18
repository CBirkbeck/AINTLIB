/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.AdjointTheory.DeltaBSystem

/-!
# The bad-prime Hecke fundamental-domain tiling (T006-b-L4)

For a prime `p ∣ N`, the `p` upper-triangular Hecke tiles `[1,b;0,p] • Γ₁(N)-FD` (`b = 0..p-1`)
form a fundamental domain for `Γ_p(diag(1,p)) = Γ₁(N) ∩ Γ⁰(p)`.  This discharges the `hFD`
hypothesis of `petN_doubleCoset_adjoint`, closing the bad-prime Petersson adjoint (DS Prop 5.6.2).

Mirrors the coprime `isFundamentalDomain_Hecke_tiles_Gamma_p_α` (`DeltaBSystem.lean`) but for the
upper-triangular / `Γ⁰(p)` / index-`p` case — the `M_∞` tile and the Bézout machinery are
**deleted**,
because the bad-prime obstruction (`p ∣ a`) is vacuous (Diamond–Shurman §5.2, Exercise 5.2.1).
-/

noncomputable section

open CongruenceSubgroup Matrix.SpecialLinearGroup Pointwise ConjAct
open scoped MatrixGroups

namespace HeckeRing.GL2

private lemma shiftSL_loc_val' (m : ℤ) : (shiftSL_loc m).val = !![1, m; 0, 1] := rfl

variable {N : ℕ} [NeZero N]

/-! ## FD-a — `Γ_p(diag(1,p)) = Γ₁(N) ⊓ Γ⁰(p)` (no coprimality)

Mirrors the coprime `Gamma_p_α_T_p_lower_eq_inf` (`FDTransport`), with `diag(1,p)` in place of
`diag(p,1)`.  Conjugation `diag(1,p)·γ·diag(1,p)⁻¹ = [a, b/p; p·c, d]` is integral ⟺ `p ∣ b`
(the `Γ⁰(p)` upper-right condition); the lower-left `p·c ≡ 0 (mod N)` is automatic (`c ≡ 0`).
So **no `Coprime p N`** is needed (the `mpr_k_mod_N` Bézout step of the lower template is
deleted). -/

/-- The real matrix `map (Rat.castHom ℝ) (T_p_upper p hp 0) = diag(1,p)`. -/
private lemma map_T_p_upper_zero_real_val (p : ℕ) (hp : 0 < p) :
    ((Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (T_p_upper p hp 0)) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; 0, (p : ℝ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T_p_upper, Matrix.GeneralLinearGroup.map, Matrix.map_apply]

/-- The conjugate `A·(mapGL ℝ γ)·A⁻¹` for `A = diag(1,p)` has entries
`!![a, b/p; p·c, d]` (over ℝ), where `γ = !![a,b;c,d]`.  Mirror of `conj_T_p_lower_real_val`
with the roles of the off-diagonal entries swapped. -/
private lemma conj_T_p_upper_zero_real_val (p : ℕ) (hp : 0 < p) (γ : SL(2, ℤ)) :
    (((Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (T_p_upper p hp 0)) *
        (toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) *
        ((Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (T_p_upper p hp 0)))⁻¹) :
      Matrix (Fin 2) (Fin 2) ℝ) =
    !![((γ.val 0 0 : ℤ) : ℝ), ((γ.val 0 1 : ℤ) : ℝ) / (p : ℝ);
       (p : ℝ) * ((γ.val 1 0 : ℤ) : ℝ), ((γ.val 1 1 : ℤ) : ℝ)] := by
  have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hinv : ((((Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (T_p_upper p hp 0)))⁻¹ :
      GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; 0, 1 / (p : ℝ)] := by
    rw [Matrix.coe_units_inv, map_T_p_upper_zero_real_val p hp, Matrix.inv_def,
      Matrix.adjugate_fin_two_of, Ring.inverse_eq_inv']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_two_of]
    field_simp
  have hγr : ((toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      !![((γ.val 0 0 : ℤ) : ℝ), ((γ.val 0 1 : ℤ) : ℝ);
         ((γ.val 1 0 : ℤ) : ℝ), ((γ.val 1 1 : ℤ) : ℝ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [map_T_p_upper_zero_real_val p hp, hinv, hγr, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

open Pointwise ConjAct in
omit [NeZero N] in
/-- Forward direction of the membership characterization: if `γ` lies in the conjugate
intersection `conjGL Γ₁(N) (mapGL A)` (with `A = diag(1,p)`), the integral preimage `y` has
`(0,1)`-entry `γ₀₁ / p`, forcing `p ∣ γ₀₁`. -/
private lemma mem_Gamma_p_α_T_p_upper_zero_mp
    (p : ℕ) (hp : 0 < p) {γ : SL(2, ℤ)}
    (h : γ ∈ conjGL (Gamma1 N) ((T_p_upper p hp 0).map (Rat.castHom ℝ))) :
    (p : ℤ) ∣ γ.val 0 1 := by
  have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  obtain ⟨y, _, hy_eq⟩ := mem_conjGL.mp h
  -- The `(0,1)` entry of `mapGL y = A·γ·A⁻¹` is the integer `y₀₁ = b/p`, so `p ∣ b`.
  have hentry : ((y.val 0 1 : ℤ) : ℝ) = ((γ.val 0 1 : ℤ) : ℝ) / (p : ℝ) := by
    have h1 : ((toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) y)) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        !![((γ.val 0 0 : ℤ) : ℝ), ((γ.val 0 1 : ℤ) : ℝ) / (p : ℝ);
           (p : ℝ) * ((γ.val 1 0 : ℤ) : ℝ), ((γ.val 1 1 : ℤ) : ℝ)] := by
      rw [hy_eq, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
        conj_T_p_upper_zero_real_val p hp γ]
    have h01 := congrFun (congrFun h1 0) 1
    simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] using h01
  have : ((γ.val 0 1 : ℤ) : ℝ) = ((y.val 0 1 : ℤ) : ℝ) * (p : ℝ) := by
    rw [hentry]; field_simp
  have hcast : (γ.val 0 1 : ℤ) = (y.val 0 1 : ℤ) * (p : ℤ) := by exact_mod_cast this
  exact ⟨y.val 0 1, by rw [hcast]; ring⟩

/-- Helper: the explicit integral matrix `y = [[a, k], [p·c, d]]` (with `k = γ₀₁/p`) has
determinant `1`.  (`p·c·k = γ₁₀·γ₀₁` since `p·k = γ₀₁`.) -/
private lemma mem_Gamma_p_α_T_p_upper_zero_mpr_det
    (p : ℕ) {γ : SL(2, ℤ)} {k : ℤ} (hk : γ.val 0 1 = p * k) :
    (!![γ.val 0 0, k; (p : ℤ) * γ.val 1 0, γ.val 1 1] :
      Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  rw [Matrix.det_fin_two_of]
  have hγdet : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = 1 := by
    have := γ.property
    rw [Matrix.det_fin_two] at this
    linarith [this]
  have : k * ((p : ℤ) * γ.val 1 0) = γ.val 0 1 * γ.val 1 0 := by
    rw [hk]; ring
  linarith [hγdet, this]

open Pointwise ConjAct in
omit [NeZero N] in
/-- Reverse direction: given `γ ∈ Γ₁(N)` with `p ∣ γ₀₁`, the integral matrix
`y = [[a, k], [p·c, d]]` (with `k = γ₀₁/p`) lies in `Γ₁(N)` and satisfies
`mapGL y = A · mapGL γ · A⁻¹`, witnessing membership in `conjGL Γ₁(N) (mapGL A)`.

The lower-left entry `p·c ≡ 0 (mod N)` is **automatic** (`c ≡ 0`), so **no coprimality**
is required — this is exactly where the lower template's `mpr_k_mod_N` Bézout step is deleted. -/
private lemma mem_Gamma_p_α_T_p_upper_zero_mpr
    (p : ℕ) (hp : 0 < p) {γ : SL(2, ℤ)}
    (hγ₁ : γ ∈ Gamma1 N) (hdvd : (p : ℤ) ∣ γ.val 0 1) :
    γ ∈ conjGL (Gamma1 N) ((T_p_upper p hp 0).map (Rat.castHom ℝ)) := by
  have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  rw [mem_conjGL]
  obtain ⟨k, hk⟩ := hdvd
  obtain ⟨ha, hd, hc⟩ := (Gamma1_mem N γ).mp hγ₁
  have hdet := mem_Gamma_p_α_T_p_upper_zero_mpr_det p hk
  set y : SL(2, ℤ) := ⟨!![γ.val 0 0, k; (p : ℤ) * γ.val 1 0, γ.val 1 1], hdet⟩ with hy_def
  have hy_mem : y ∈ Gamma1 N := by
    rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · show ((y.val 0 0 : ℤ) : ZMod N) = 1
      simp only [hy_def, Matrix.SpecialLinearGroup.coe_mk, Matrix.cons_val', Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one]
      exact ha
    · show ((y.val 1 1 : ℤ) : ZMod N) = 1
      simp only [hy_def, Matrix.SpecialLinearGroup.coe_mk, Matrix.cons_val', Matrix.of_apply,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      exact hd
    · show ((y.val 1 0 : ℤ) : ZMod N) = 0
      simp only [hy_def, Matrix.SpecialLinearGroup.coe_mk, Matrix.cons_val', Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      push_cast; rw [hc, mul_zero]
  refine ⟨y, hy_mem, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    conj_T_p_upper_zero_real_val p hp γ]
  have hyval : Subtype.val y = !![γ.val 0 0, k; (p : ℤ) * γ.val 1 0, γ.val 1 1] := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, hyval, hk]
  field_simp

open Pointwise ConjAct in
omit [NeZero N] in
/-- **Membership characterization of `Γ_p(diag(1,p))`.** For `A = diag(1,p)`, conjugation
`A·γ·A⁻¹ = [[a, b/p], [p·c, d]]` is integral (and lands in `Γ₁(N)`) iff `p ∣ b`.  Hence
`Γ_p(A) = {γ ∈ Γ₁(N) : p ∣ γ₀₁}` (the `Γ⁰(p)`-type upper-right condition). -/
lemma mem_Gamma_p_α_T_p_upper_zero (p : ℕ) (hp : 0 < p)
    {γ : SL(2, ℤ)} :
    γ ∈ Gamma_p_α (N := N) (T_p_upper p hp 0) ↔
      γ ∈ Gamma1 N ∧ (p : ℤ) ∣ γ.val 0 1 := by
  rw [Gamma_p_α, Subgroup.mem_inf]
  refine ⟨fun ⟨h, hγ₁⟩ ↦ ⟨hγ₁, mem_Gamma_p_α_T_p_upper_zero_mp p hp h⟩, fun ⟨hγ₁, hdvd⟩ ↦ ?_⟩
  exact ⟨mem_Gamma_p_α_T_p_upper_zero_mpr p hp hγ₁ hdvd, hγ₁⟩

omit [NeZero N] in
/-- **[T006-b-L4-FD-a]** For `p ∣ N`, `Γ_p(diag(1,p)) = Γ₁(N) ⊓ Γ⁰(p)` (Diamond–Shurman
`Γ₁⁰(N,p)`, §5.2).  Unlike the coprime `Γ_p(diag(p,1)) = Γ₁(N)⊓Γ₀(p)`, this needs **no
coprimality**: the conjugate's lower-left `p·γ₁₀ ≡ 0 (mod N)` is automatic. -/
lemma Gamma_p_α_T_p_upper_zero_eq_inf (p : ℕ) (hp : Nat.Prime p) (_hpN : ¬ Nat.Coprime p N) :
    Gamma_p_α (N := N) (T_p_upper p hp.pos 0) = Gamma1 N ⊓ Gamma_up p := by
  ext γ
  rw [mem_Gamma_p_α_T_p_upper_zero p hp.pos, Subgroup.mem_inf, Gamma_up_mem,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

/-! ## FD-b — `[Γ₁(N) : Γ₁(N) ∩ Γ⁰(p)] = p` for `p ∣ N` (the index drop)

The coprime sibling `Gamma_up_relIndex_Gamma1` gives `p + 1` and routes through the
**Bézout/`M_∞` covering** (`Gamma_up_prime_index` + `Gamma1_relIndex_Gamma_up_eq_index`),
which is INAPPLICABLE here.  We give a **direct** proof: the `p` det-`1` shears
`shiftSL_loc j = [1,j;0,1]` (`j ∈ Fin p`) form a complete `Γ⁰(p)`-transversal of `Γ₁(N)`.

* **distinctness** (`b₁ ≠ b₂ ⟹ shiftSL_loc(-b₁)·shiftSL_loc b₂ ∉ Γ⁰(p)`): the `(0,1)`-entry is
  `b₂ - b₁` with `0 < |b₂-b₁| < p` — re-derived in-file (the coprime DeltaBSystem helper is
  `private`);
* **covering**: for `γ ∈ Γ₁(N)`, `p ∣ N ⟹ γ₁₁ ≡ 1 (mod p)`, so `j := γ₀₁ mod p` (no `γ₀₀⁻¹`
  needed, unlike the coprime route — the bad obstruction `p ∣ a` is vacuous, DS Ex 5.2.1).

The `p`-tile count is exactly `Nat.card (Fin p) = p`. -/

/-- **Distinctness of the `Fin p` shears.** For `b₁ ≠ b₂`, the `(0,1)`-entry of
`shiftSL_loc(-b₁)·shiftSL_loc b₂ = [1,-b₁;0,1]·[1,b₂;0,1] = [1, b₂-b₁; 0,1]` is `b₂ - b₁`,
which has `0 < |b₂-b₁| < p`, so it is not `≡ 0 (mod p)`.  (Re-derivation of the `private`
`DeltaBSystem.T_p_lower_tile_some_some_notMem_Gamma_up`, in the `⁻¹·` orientation needed for
the quotient relation.) -/
private lemma shiftSL_loc_inv_mul_notMem_Gamma_up
    (p : ℕ) (hp : Nat.Prime p) {b₁ b₂ : Fin p} (hb : b₁ ≠ b₂) :
    (shiftSL_loc (b₁.val : ℤ))⁻¹ * shiftSL_loc (b₂.val : ℤ) ∉ Gamma_up p := by
  rw [Gamma_up_mem]
  have hne : (b₂ : ℤ) ≠ (b₁ : ℤ) := by
    simp only [ne_eq, Nat.cast_inj]; exact fun h ↦ hb (by rw [Fin.ext_iff.mpr h.symm])
  have hentry : (((shiftSL_loc (b₁.val : ℤ))⁻¹ * shiftSL_loc (b₂.val : ℤ)).val 0 1 : ℤ) =
      (b₂.val : ℤ) - (b₁.val : ℤ) := by
    simp [Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, shiftSL_loc_val', Matrix.adjugate_fin_two_of,
      Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [hentry, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro hdvd
  have hlt : |(b₂.val : ℤ) - (b₁.val : ℤ)| < p := by
    rw [abs_lt]; constructor <;> [have := b₁.isLt; have := b₂.isLt] <;> omega
  have hb' : (b₂.val : ℤ) - (b₁.val : ℤ) ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨c, hc⟩ := hdvd
  have hcabs : 1 ≤ |c| := Int.one_le_abs (by rintro rfl; simp at hc; exact hb' hc)
  rw [hc, abs_mul, Nat.abs_cast] at hlt
  have hppos : 0 < p := hp.pos
  nlinarith [hlt, hcabs, hppos]

omit [NeZero N] in
/-- **[T006-b-L4-FD-b]** For `p ∣ N`, `[Γ₁(N) : Γ₁(N) ∩ Γ⁰(p)] = p`.  This is the bad-prime
index (the upper analogue of the coprime `p + 1`; the `M_∞` tile is absent because the bad
obstruction `p ∣ a` is vacuous, DS Ex 5.2.1).  Proved by the explicit `Fin p` shear
transversal `{[1,j;0,1] : j ∈ Fin p}`. -/
theorem Gamma_up_relIndex_Gamma1_of_dvd (p : ℕ) (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) :
    (Gamma_up p).relIndex (Gamma1 N) = p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hpdvd : p ∣ N := by rw [hp.coprime_iff_not_dvd, not_not] at hpN; exact hpN
  -- Reduction-mod-`p` of `Γ₁(N)`-data: `d ≡ 1 (mod p)` (since `p ∣ N`).
  have hred : ∀ (x : ℤ), (x : ZMod N) = 1 → (x : ZMod p) = 1 := fun x h ↦ by
    have := congrArg (ZMod.castHom hpdvd (ZMod p)) h
    rwa [map_intCast, map_one] at this
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  -- Forward transversal map `Fin p → Γ₁ ⧸ (Γ⁰(p).subgroupOf Γ₁)`, `j ↦ ⟦[1,j;0,1]⟧`.
  set e : Fin p → (Gamma1 N) ⧸ ((Gamma_up p).subgroupOf (Gamma1 N)) :=
    fun j ↦ QuotientGroup.mk ⟨shiftSL_loc (j.val : ℤ), shiftSL_loc_mem_Gamma1 (j.val : ℤ)⟩
    with he_def
  have hbij : Function.Bijective e := by
    constructor
    · -- Injectivity via distinctness.
      intro b₁ b₂ hb
      by_contra hne
      rw [he_def, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hb
      simp only [InvMemClass.coe_inv, MulMemClass.coe_mul] at hb
      exact shiftSL_loc_inv_mul_notMem_Gamma_up p hp hne hb
    · -- Surjectivity via covering: every `⟦γ⟧` is `⟦[1,j;0,1]⟧` with `j ≡ γ₀₁ (mod p)`.
      intro q
      induction q using QuotientGroup.induction_on with | _ γ => ?_
      obtain ⟨_, hd, _⟩ := (Gamma1_mem N (γ : SL(2, ℤ))).mp γ.property
      -- `j := (γ₀₁ : ZMod p).val` as an element of `Fin p`.
      set jval : ℕ := ((γ : SL(2, ℤ)).val 0 1 : ZMod p).val with hjval_def
      have hjval_lt : jval < p := hjval_def ▸ ZMod.val_lt _
      refine ⟨⟨jval, hjval_lt⟩, ?_⟩
      rw [he_def, QuotientGroup.eq, Subgroup.mem_subgroupOf, Gamma_up_mem]
      simp only [InvMemClass.coe_inv, MulMemClass.coe_mul]
      -- `(0,1)`-entry of `[1,j;0,1]⁻¹·γ = [1,-j;0,1]·γ` is `γ₀₁ - j·γ₁₁ ≡ γ₀₁ - j (mod p)`.
      have hentry : (((shiftSL_loc ((jval : ℤ)))⁻¹ * (γ : SL(2, ℤ))).val 0 1 : ℤ) =
          (γ : SL(2, ℤ)).val 0 1 - (jval : ℤ) * (γ : SL(2, ℤ)).val 1 1 := by
        simp [Matrix.SpecialLinearGroup.coe_mul,
          Matrix.SpecialLinearGroup.coe_inv, shiftSL_loc_val', Matrix.adjugate_fin_two_of,
          Matrix.mul_apply, Fin.sum_univ_two]
        ring
      rw [hentry]; push_cast
      rw [hred _ hd, mul_one]
      -- `(γ₀₁ : ZMod p) - (j : ZMod p) = 0` since `j = (γ₀₁ : ZMod p).val (mod p)`.
      have hj : ((jval : ZMod p)) = ((γ : SL(2, ℤ)).val 0 1 : ZMod p) := by
        rw [hjval_def, ZMod.natCast_val, ZMod.cast_id]
      rw [hj, sub_self]
  rw [← Nat.card_congr (Equiv.ofBijective e hbij), Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ## Re-derived PSL bridges (the coprime `DeltaBSystem` analogues are `private`)

The assembly mirrors the coprime `isFundamentalDomain_Hecke_tiles_Gamma_p_α` with **`α = diag(p,1)
= T_p_lower`** (the adjoint-side group `Gamma_p_α(diag(p,1))`, whose `g'=g∣diag(p,1)` invariance
is what the LHS bridge `peterssonInner_badUp_sum_slashes_eq_aggregate` supplies) and the tile
family reduced from `Option (Fin p)` to **`Fin p`** (no `M_∞`).  All needed `DeltaBSystem`
helpers are `private`, so the foundational bridges are re-derived here. -/

open Pointwise ConjAct UpperHalfPlane MeasureTheory in
open UpperHalfPlane Pointwise in
/-- **Linearization (the `some b` branch, no `M_∞`).** `diag(p,1)·[1,b;0,p] = p·[1,b;0,1]`, so at
the level of sets `glMap(T_p_lower)·(glMap(T_p_upper b)•S) = shiftSL_loc b•S`.  (Re-derivation of
`DeltaBSystem.T_p_lower_mul_T_p_upper_smul_set_eq_shift_smul`.) -/
private lemma T_p_lower_mul_T_p_upper_smul_set_eq_shift'
    (p : ℕ) (hp : 0 < p) (b : ℕ) (S : Set ℍ) :
    ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ)) • S =
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (b : ℤ)) : GL (Fin 2) ℝ) • S := by
  have hsmul : ∀ τ : ℍ,
      ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
        (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ)) • τ =
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (b : ℤ)) : GL (Fin 2) ℝ) • τ := by
    intro τ
    have h_det_LHS : 0 <
        ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
          (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ)).det.val := by
      rw [map_mul, Units.val_mul]
      exact mul_pos (glMap_det_pos_of_rat_det_pos _ (T_p_lower_det_pos p hp))
        (glMap_det_pos_of_rat_det_pos _ (T_p_upper_det_pos p hp b))
    have h_det_RHS : 0 <
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (b : ℤ)) :
          GL (Fin 2) ℝ).det.val := by
      rw [mapGL_SL_det_val_eq_one]; exact one_pos
    refine UpperHalfPlane_smul_eq_of_matrix_smul_eq _ _ h_det_LHS h_det_RHS
      (p : ℝ) (by exact_mod_cast hp.ne') ?_ τ
    have hsh : (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (b : ℤ))) :
        Matrix (Fin 2) (Fin 2) ℝ) = (!![1, (b : ℤ); 0, 1]).map Int.cast :=
      (Matrix.SpecialLinearGroup.mapGL_coe_matrix _).trans (by rw [algebraMap_int_eq]; rfl)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [glMap, T_p_lower, T_p_upper, hsh, Matrix.map_apply,
        Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.map,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Units.val_mul,
        Matrix.smul_apply]
  ext τ
  refine ⟨?_, ?_⟩ <;> rintro ⟨σ, hσ, rfl⟩
  · exact ⟨σ, hσ, (hsmul σ).symm⟩
  · exact ⟨σ, hσ, hsmul σ⟩

/-! ## The adjoint-side subgroup identity `K = toConjAct g • Γ_p(diag(p,1)) = (Γ₁ ⊓ Γ⁰(p)).map`

For `p ∣ N`, `Γ_p(diag(p,1)) = {γ ∈ Γ₁ : γ₁₀ ≡ 0 (mod pN)}` (index `p`); conjugating by
`A = diag(p,1)` sends it onto `Γ₁ ⊓ Γ⁰(p)` (also index `p`).  This is the bad-prime analogue of
`DeltaBSystem.toConjAct_GLPos_Gamma_p_α_T_p_lower_eq_Gamma1_inf_Gamma_up_map` — the forward
direction is coprimality-free; the backward direction holds because the conjugate-back matrix
`x = A⁻¹·y·A` satisfies `A·x·A⁻¹ = y ∈ Γ₁` outright. -/

omit [NeZero N] in
open Pointwise ConjAct in
/-- **Forward conjugation fact.** For `x ∈ Γ_p(diag(p,1))`, the conjugate
`y = A·x·A⁻¹` has `y₀₁ = p·x₀₁ ≡ 0 (mod p)`, so `y ∈ Γ⁰(p)`.  (Re-derivation of
`DeltaBSystem.Gamma_p_α_conjBy_mem_Gamma_up`; the coprimality argument is dropped.) -/
private lemma Gamma_p_α_conjBy_mem_Gamma_up'
    (p : ℕ) (hp : Nat.Prime p)
    (x : Gamma_p_α (N := N) (T_p_lower p hp.pos)) :
    (Gamma_p_α_conjBy (T_p_lower p hp.pos) x : SL(2, ℤ)) ∈ Gamma_up p := by
  have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  set y : SL(2, ℤ) := (Gamma_p_α_conjBy (T_p_lower p hp.pos) x : SL(2, ℤ)) with hy_def
  have hentry : ((y.val 0 1 : ℤ) : ℝ) = (p : ℝ) * ((x.val.val 0 1 : ℤ) : ℝ) := by
    have h1 : ((mapGL ℝ y : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![((x.val.val 0 0 : ℤ) : ℝ), (p : ℝ) * ((x.val.val 0 1 : ℤ) : ℝ);
           ((x.val.val 1 0 : ℤ) : ℝ) / (p : ℝ), ((x.val.val 1 1 : ℤ) : ℝ)] := by
      rw [hy_def, Gamma_p_α_conjBy_spec (T_p_lower p hp.pos) x]
      exact conj_T_p_lower_real_val p hp.pos x.val
    have h01 := congrFun (congrFun h1 0) 1
    rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix] at h01
    simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] using h01
  rw [Gamma_up_mem]
  have hdvd : (p : ℤ) ∣ y.val 0 1 := by
    have hcast : (y.val 0 1 : ℤ) = x.val.val 0 1 * (p : ℤ) := by
      have : ((y.val 0 1 : ℤ) : ℝ) = ((x.val.val 0 1 * (p : ℤ) : ℤ) : ℝ) := by
        rw [hentry]; push_cast; ring
      exact_mod_cast this
    exact ⟨x.val.val 0 1, by rw [hcast]; ring⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hdvd
  exact_mod_cast hdvd

omit [NeZero N] in
/-- The conjugate-back matrix `x = [[y₀₀, j], [p·y₁₀, y₁₁]]` belongs to `Γ₁(N)` whenever `y`
does. -/
private lemma conjBack_matrix_mem_Gamma1'
    (p : ℕ) {y : SL(2, ℤ)} {j : ℤ} (hj : y.val 0 1 = (p : ℤ) * j)
    (hy₁ : y ∈ Gamma1 N) :
    (⟨!![y.val 0 0, j; (p : ℤ) * y.val 1 0, y.val 1 1], conjBack_matrix_det p hj⟩ :
      SL(2, ℤ)) ∈ Gamma1 N := by
  obtain ⟨hy00, hy11, hy10⟩ := (Gamma1_mem N y).mp hy₁
  refine (Gamma1_mem N _).mpr ⟨?_, ?_, ?_⟩
  · show (((!![y.val 0 0, j; (p : ℤ) * y.val 1 0, y.val 1 1] :
        Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod N) = 1
    simp only [Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    exact hy00
  · show (((!![y.val 0 0, j; (p : ℤ) * y.val 1 0, y.val 1 1] :
        Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) = 1
    simp only [Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    exact hy11
  · show (((!![y.val 0 0, j; (p : ℤ) * y.val 1 0, y.val 1 1] :
        Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0
    simp only [Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast; rw [hy10, mul_zero]

open Pointwise ConjAct in
omit [NeZero N] in
/-- The conjugation identity `A · mapGL x · A⁻¹ = mapGL y` for the conjugate-back matrix
`x = [[y₀₀, j], [p·y₁₀, y₁₁]]` with `y₀₁ = p·j`, `A = T_p_lower p`. -/
private lemma conjBack_matrix_conj_eq'
    (p : ℕ) (hp : Nat.Prime p) {y : SL(2, ℤ)} {j : ℤ} (hj : y.val 0 1 = (p : ℤ) * j) :
    ((T_p_lower p hp.pos).map (Rat.castHom ℝ) : GL (Fin 2) ℝ) *
        (mapGL ℝ (⟨!![y.val 0 0, j; (p : ℤ) * y.val 1 0, y.val 1 1],
            conjBack_matrix_det p hj⟩ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        ((T_p_lower p hp.pos).map (Rat.castHom ℝ) : GL (Fin 2) ℝ)⁻¹ =
      (mapGL ℝ y : GL (Fin 2) ℝ) := by
  set x : SL(2, ℤ) :=
    ⟨!![y.val 0 0, j; (p : ℤ) * y.val 1 0, y.val 1 1], conjBack_matrix_det p hj⟩
  apply Units.ext
  rw [show ((mapGL ℝ x : GL (Fin 2) ℝ)) =
      toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) x) from rfl,
    Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    conj_T_p_lower_real_val p hp.pos x, Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  ext i j'
  fin_cases i <;> fin_cases j' <;>
    simp [x, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, hj, hpR]

open Pointwise ConjAct in
omit [NeZero N] in
/-- **Backward conjugation witness (bad case, coprimality-free).** For `y ∈ Γ₁ ⊓ Γ⁰(p)`
(`p ∣ y₀₁`), the matrix `x = A⁻¹·y·A = [[y₀₀, y₀₁/p], [p·y₁₀, y₁₁]]` is a `Γ_p(diag(p,1))`
element with `A·(mapGL x)·A⁻¹ = mapGL y`.  Membership in `Γ_p(diag(p,1))` holds because
`A·x·A⁻¹ = y ∈ Γ₁` directly (no `mem_Gamma_p_α_T_p_lower` coprimality needed). -/
private lemma exists_Gamma_p_α_conj_eq_of_mem_Gamma_up'
    (p : ℕ) (hp : Nat.Prime p)
    {y : SL(2, ℤ)} (hy₁ : y ∈ Gamma1 N) (hyU : y ∈ Gamma_up p) :
    ∃ x ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos),
      ((T_p_lower p hp.pos).map (Rat.castHom ℝ) : GL (Fin 2) ℝ) *
          (mapGL ℝ x : GL (Fin 2) ℝ) *
          ((T_p_lower p hp.pos).map (Rat.castHom ℝ) : GL (Fin 2) ℝ)⁻¹ =
        (mapGL ℝ y : GL (Fin 2) ℝ) := by
  have hdvd : (p : ℤ) ∣ y.val 0 1 := by
    have := (Gamma_up_mem (p := p) (A := y)).mp hyU
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  obtain ⟨j, hj⟩ := hdvd
  set x : SL(2, ℤ) :=
    ⟨!![y.val 0 0, j; (p : ℤ) * y.val 1 0, y.val 1 1], conjBack_matrix_det p hj⟩ with hx_def
  have hx_mem₁ : x ∈ Gamma1 N := conjBack_matrix_mem_Gamma1' (N := N) p hj hy₁
  have hconj := conjBack_matrix_conj_eq' p hp hj
  -- `x ∈ Γ_p(diag(p,1))`: both `x ∈ Γ₁` and `A·x·A⁻¹ = y ∈ Γ₁` (the `conjGL` condition).
  have hx_mem : x ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos) := by
    refine Subgroup.mem_inf.mpr ⟨?_, hx_mem₁⟩
    rw [mem_conjGL]
    exact ⟨y, hy₁, hconj.symm⟩
  exact ⟨x, hx_mem, hconj⟩

omit [NeZero N] in
open Pointwise ConjAct in
/-- **The adjoint-side subgroup identity (bad case).** `K = toConjAct g • Γ_p(diag(p,1)).map =
(Γ₁ ⊓ Γ⁰(p)).map`.  (Re-derivation of
`DeltaBSystem.toConjAct_GLPos_Gamma_p_α_T_p_lower_eq_Gamma1_inf_Gamma_up_map`, coprimality-free.) -/
private lemma toConjAct_GLPos_Gamma_p_α_T_p_lower_eq_Gamma1_inf_Gamma_up_map'
    (p : ℕ) (hp : Nat.Prime p)
    (g : PSL(2, ℝ))
    (hg : g = GLPos_to_PSL_R_term
      ⟨glMap (T_p_lower p hp.pos),
        glMap_det_pos_of_rat_det_pos _ (T_p_lower_det_pos p hp.pos)⟩) :
    (ConjAct.toConjAct g • ((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R) :
        Subgroup PSL(2, ℝ)) =
      ((Gamma1 N ⊓ Gamma_up p).map SL2Z_to_PSL2R) := by
  set A' : GL(2, ℝ)⁺ := ⟨glMap (T_p_lower p hp.pos),
    glMap_det_pos_of_rat_det_pos _ (T_p_lower_det_pos p hp.pos)⟩ with hA'_def
  have hA'_val : (A' : GL (Fin 2) ℝ) = (T_p_lower p hp.pos).map (Rat.castHom ℝ) := rfl
  apply le_antisymm
  · intro z hz
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, map_inv,
      ConjAct.ofConjAct_toConjAct, inv_inv] at hz
    obtain ⟨x, hx_mem, hx_eq⟩ := Subgroup.mem_map.mp hz
    set y : SL(2, ℤ) := (Gamma_p_α_conjBy (T_p_lower p hp.pos) ⟨x, hx_mem⟩ : SL(2, ℤ)) with hy_def
    have hy_mem₁ : y ∈ Gamma1 N := (Gamma_p_α_conjBy (T_p_lower p hp.pos) ⟨x, hx_mem⟩).property
    have hy_memU : y ∈ Gamma_up p :=
      Gamma_p_α_conjBy_mem_Gamma_up' p hp ⟨x, hx_mem⟩
    have hconj_gl : (A' : GL (Fin 2) ℝ) * (mapGL ℝ x : GL (Fin 2) ℝ) *
        (A' : GL (Fin 2) ℝ)⁻¹ = (mapGL ℝ y : GL (Fin 2) ℝ) := by
      rw [hy_def, Gamma_p_α_conjBy_spec (T_p_lower p hp.pos) ⟨x, hx_mem⟩, hA'_val]
    have hbridge := toConjAct_GLPos_smul_SL2Z_to_PSL2R A' x y hconj_gl
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, ← hg, hx_eq] at hbridge
    have hz_eq : z = SL2Z_to_PSL2R y := by rw [← hbridge]; group
    rw [hz_eq]
    exact Subgroup.mem_map_of_mem SL2Z_to_PSL2R (Subgroup.mem_inf.mpr ⟨hy_mem₁, hy_memU⟩)
  · intro z hz
    obtain ⟨y, hy_mem, hy_eq⟩ := Subgroup.mem_map.mp hz
    obtain ⟨hy₁, hyU⟩ := Subgroup.mem_inf.mp hy_mem
    obtain ⟨x, hx_mem, hconj⟩ := exists_Gamma_p_α_conj_eq_of_mem_Gamma_up' p hp hy₁ hyU
    have hconj_gl : (A' : GL (Fin 2) ℝ) * (mapGL ℝ x : GL (Fin 2) ℝ) *
        (A' : GL (Fin 2) ℝ)⁻¹ = (mapGL ℝ y : GL (Fin 2) ℝ) := by rw [hA'_val]; exact hconj
    have hbridge := toConjAct_GLPos_smul_SL2Z_to_PSL2R A' x y hconj_gl
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, ← hg] at hbridge
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, map_inv,
      ConjAct.ofConjAct_toConjAct, inv_inv, ← hy_eq, ← hbridge]
    have : g⁻¹ * (g * SL2Z_to_PSL2R x * g⁻¹) * g = SL2Z_to_PSL2R x := by group
    rw [this]
    exact Subgroup.mem_map_of_mem SL2Z_to_PSL2R hx_mem

/-! ## FD-c — the `Fin p` shear transversal and the assembly -/

omit [NeZero N] in
open Pointwise ConjAct in
/-- **The adjoint-side coset count (bad case).** `[G : K.subgroupOf G] = [Γ₁ : Γ₁ ⊓ Γ⁰(p)] = p`
(FD-b).  The `SL`-coset space `Γ₁ ⧸ (Γ₁⊓Γ⁰)` maps bijectively onto the `PSL`-coset space via
`SL2Z_to_PSL2R` (`±I`-absorption).  (Re-derivation of `DeltaBSystem.card_quotient_K_subgroupOf_G`,
returning `p` instead of `p + 1`.) -/
private lemma card_quotient_K_subgroupOf_G'
    (p : ℕ) (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (g : PSL(2, ℝ))
    (hg : g = GLPos_to_PSL_R_term
      ⟨glMap (T_p_lower p hp.pos),
        glMap_det_pos_of_rat_det_pos _ (T_p_lower_det_pos p hp.pos)⟩) :
    Nat.card (((Gamma1 N).map SL2Z_to_PSL2R) ⧸
        ((ConjAct.toConjAct g • ((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R)
          ).subgroupOf ((Gamma1 N).map SL2Z_to_PSL2R))) = p := by
  rw [toConjAct_GLPos_Gamma_p_α_T_p_lower_eq_Gamma1_inf_Gamma_up_map' p hp g hg]
  have hbij : ((Gamma1 N ⊓ Gamma_up p).map SL2Z_to_PSL2R).relIndex
      ((Gamma1 N).map SL2Z_to_PSL2R) = (Gamma1 N ⊓ Gamma_up p).relIndex (Gamma1 N) := by
    rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.index_eq_card, Subgroup.index_eq_card]
    refine Nat.card_congr (Equiv.symm (Equiv.ofBijective
      (Quotient.lift (fun a : Gamma1 N ↦
        (QuotientGroup.mk ⟨SL2Z_to_PSL2R (a : SL(2, ℤ)),
          Subgroup.mem_map_of_mem SL2Z_to_PSL2R a.2⟩ :
          ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
            ((Gamma1 N ⊓ Gamma_up p).map SL2Z_to_PSL2R).subgroupOf
              ((Gamma1 N).map SL2Z_to_PSL2R))) ?_) ?_))
    · intro a b hab
      change (QuotientGroup.leftRel _).r _ _ at hab
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simp only [InvMemClass.coe_inv, MulMemClass.coe_mul]
      rw [← map_inv, ← map_mul]
      exact (SL2Z_to_PSL2R_mem_Gamma1_inf_Gamma_up_map_iff p
        ((Gamma1 N).mul_mem ((Gamma1 N).inv_mem a.2) b.2)).mpr hab
    · constructor
      · intro x y hxy
        induction x using QuotientGroup.induction_on with | _ a => ?_
        induction y using QuotientGroup.induction_on with | _ b => ?_
        have hxy' : (QuotientGroup.mk ⟨SL2Z_to_PSL2R (a : SL(2, ℤ)),
            Subgroup.mem_map_of_mem SL2Z_to_PSL2R a.2⟩ :
            ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
              ((Gamma1 N ⊓ Gamma_up p).map SL2Z_to_PSL2R).subgroupOf
                ((Gamma1 N).map SL2Z_to_PSL2R)) =
            QuotientGroup.mk ⟨SL2Z_to_PSL2R (b : SL(2, ℤ)),
              Subgroup.mem_map_of_mem SL2Z_to_PSL2R b.2⟩ := hxy
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hxy' ⊢
        simp only [InvMemClass.coe_inv, MulMemClass.coe_mul] at hxy' ⊢
        rw [← map_inv, ← map_mul] at hxy'
        exact (SL2Z_to_PSL2R_mem_Gamma1_inf_Gamma_up_map_iff p
          ((Gamma1 N).mul_mem ((Gamma1 N).inv_mem a.2) b.2)).mp hxy'
      · intro y
        induction y using QuotientGroup.induction_on with | _ z => ?_
        obtain ⟨w, hw_mem, hw_eq⟩ := Subgroup.mem_map.mp z.2
        refine ⟨QuotientGroup.mk ⟨w, hw_mem⟩, ?_⟩
        show QuotientGroup.mk _ = QuotientGroup.mk z
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simp only [InvMemClass.coe_inv, MulMemClass.coe_mul]
        rw [← hw_eq, inv_mul_cancel]
        exact Subgroup.one_mem _
  rw [← Subgroup.index_eq_card, ← Subgroup.relIndex, hbij, inf_comm,
    Subgroup.inf_relIndex_right]
  exact Gamma_up_relIndex_Gamma1_of_dvd p hp hpN

open Pointwise ConjAct in
omit [NeZero N] in
/-- **[T006-b-L4-FD-c]** The `p` det-`1` shear reps `r i = SL2Z_to_PSL2R(shiftSL_loc i)`
(`i ∈ Fin p`, all in `Γ₁`) have inverses `(r i)⁻¹` representing *all* the cosets
`G ⧸ (K.subgroupOf G)` (`G = Γ₁.map`, `K = toConjAct g • Γ_p(diag(p,1)).map = (Γ₁⊓Γ⁰(p)).map`)
bijectively.  Mirror of `DeltaBSystem.T_p_lower_tile_transversal_bijective` over `Fin p` (no
`Option`/`M_∞`); card `= p` (`card_quotient_K_subgroupOf_G'`), injectivity from FD-b
distinctness. -/
private theorem shiftSL_loc_tile_transversal_bijective
    (p : ℕ) (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (g : PSL(2, ℝ))
    (hg : g = GLPos_to_PSL_R_term
      ⟨glMap (T_p_lower p hp.pos),
        glMap_det_pos_of_rat_det_pos _ (T_p_lower_det_pos p hp.pos)⟩) :
    Function.Bijective
      (fun i : Fin p ↦
        (QuotientGroup.mk
          ((⟨SL2Z_to_PSL2R (shiftSL_loc (i.val : ℤ)),
              Subgroup.mem_map_of_mem SL2Z_to_PSL2R (shiftSL_loc_mem_Gamma1 (i.val : ℤ))⟩ :
            ((Gamma1 N).map SL2Z_to_PSL2R))⁻¹) :
          ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
            ((ConjAct.toConjAct g • ((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R)
              ).subgroupOf ((Gamma1 N).map SL2Z_to_PSL2R)))) := by
  set G : Subgroup PSL(2, ℝ) := (Gamma1 N).map SL2Z_to_PSL2R with hG_def
  set K : Subgroup PSL(2, ℝ) :=
    ConjAct.toConjAct g • ((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R)
    with hK_def
  set r : Fin p → G := fun i ↦
    ⟨SL2Z_to_PSL2R (shiftSL_loc (i.val : ℤ)),
      Subgroup.mem_map_of_mem SL2Z_to_PSL2R (shiftSL_loc_mem_Gamma1 (i.val : ℤ))⟩
    with hr_def
  have hcard : Nat.card (G ⧸ (K.subgroupOf G)) = p :=
    card_quotient_K_subgroupOf_G' p hp hpN g hg
  haveI : Finite (G ⧸ (K.subgroupOf G)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · intro i j hij
    by_contra hne
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, inv_inv] at hij
    have hmem : SL2Z_to_PSL2R (shiftSL_loc (i.val : ℤ) * (shiftSL_loc (j.val : ℤ))⁻¹) ∈ K := by
      have : ((r i * (r j)⁻¹ : G) : PSL(2, ℝ)) =
          SL2Z_to_PSL2R (shiftSL_loc (i.val : ℤ) * (shiftSL_loc (j.val : ℤ))⁻¹) := by
        rw [hr_def]
        simp only [MulMemClass.coe_mul, InvMemClass.coe_inv]
        rw [map_mul, map_inv]
      rwa [← this]
    rw [hK_def, toConjAct_GLPos_Gamma_p_α_T_p_lower_eq_Gamma1_inf_Gamma_up_map' p hp g hg,
      SL2Z_to_PSL2R_mem_Gamma1_inf_Gamma_up_map_iff p
        ((Gamma1 N).mul_mem (shiftSL_loc_mem_Gamma1 (i.val : ℤ))
          ((Gamma1 N).inv_mem (shiftSL_loc_mem_Gamma1 (j.val : ℤ))))] at hmem
    -- `shiftSL_loc i · shiftSL_loc j⁻¹ ∈ Γ⁰(p)` contradicts FD-b distinctness (with `b₁=j, b₂=i`).
    refine shiftSL_loc_inv_mul_notMem_Gamma_up p hp (fun h ↦ hne h.symm) ?_
    -- The shears commute, so `shiftSL_loc j⁻¹ · shiftSL_loc i = shiftSL_loc i · shiftSL_loc j⁻¹`.
    have h2 := (Subgroup.mem_inf.mp hmem).2
    have hcomm : (shiftSL_loc (j.val : ℤ))⁻¹ * shiftSL_loc (i.val : ℤ) =
        shiftSL_loc (i.val : ℤ) * (shiftSL_loc (j.val : ℤ))⁻¹ := by
      apply Subtype.ext; ext u v
      fin_cases u <;> fin_cases v <;>
        simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
          shiftSL_loc_val', Matrix.adjugate_fin_two_of, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    rwa [hcomm]
  · rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin]

open Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- The shear tile sets agree:
`SL2Z_to_PSL2R(shiftSL_loc b) • FD = (mapGL ℝ (shiftSL_loc b)) • FD`. -/
private lemma iUnion_shift_smul_PSL_eq_iUnion_mapGL_smul (p : ℕ) :
    (⋃ i : Fin p,
        (SL2Z_to_PSL2R (shiftSL_loc (i.val : ℤ)) : PSL(2, ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ)) =
      ⋃ i : Fin p,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (i.val : ℤ)) :
          GL (Fin 2) ℝ) • (Gamma1_fundDomain_PSL N : Set ℍ) := by
  refine Set.iUnion_congr fun i ↦ ?_
  rw [mapGL_smul_set_eq_SL2Z_to_PSL2R_smul]

open Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- **Step I.** `A • D = ⋃ shiftSL_loc(b) • FD` is a fundamental domain for the conjugate group
`K = toConjAct g • Γ_p(diag(p,1)).map`.  Mirror of
`DeltaBSystem.iUnion_T_p_lower_tile_family_isFundamentalDomain_conj` over `Fin p`. -/
private theorem iUnion_shiftSL_loc_isFundamentalDomain_conj
    (p : ℕ) (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (g : PSL(2, ℝ))
    (hg : g = GLPos_to_PSL_R_term
      ⟨glMap (T_p_lower p hp.pos),
        glMap_det_pos_of_rat_det_pos _ (T_p_lower_det_pos p hp.pos)⟩) :
    IsFundamentalDomain
      ((ConjAct.toConjAct g • ((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R)) :
        Subgroup PSL(2, ℝ))
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
        (⋃ i : Fin p, (glMap (T_p_upper p hp.pos i.val) : GL (Fin 2) ℝ) •
          (Gamma1_fundDomain_PSL N : Set ℍ)))
      μ_hyp := by
  -- `A • (⋃ T_p_upper(b)•FD) = ⋃ shiftSL_loc(b)•FD` (the `some b` linearization).
  have hAD : (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
      (⋃ i : Fin p, (glMap (T_p_upper p hp.pos i.val) : GL (Fin 2) ℝ) •
        (Gamma1_fundDomain_PSL N : Set ℍ)) =
      ⋃ i : Fin p,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (i.val : ℤ)) : GL (Fin 2) ℝ) •
          (Gamma1_fundDomain_PSL N : Set ℍ) := by
    rw [Set.smul_set_iUnion]
    refine Set.iUnion_congr fun i ↦ ?_
    rw [← mul_smul]
    exact T_p_lower_mul_T_p_upper_smul_set_eq_shift' p hp.pos i.val (Gamma1_fundDomain_PSL N)
  rw [hAD, ← iUnion_shift_smul_PSL_eq_iUnion_mapGL_smul (N := N) p]
  set K : Subgroup PSL(2, ℝ) :=
    ConjAct.toConjAct g • ((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R)
    with hK_def
  set G : Subgroup PSL(2, ℝ) := (Gamma1 N).map SL2Z_to_PSL2R with hG_def
  have hKG : K ≤ G := by
    rw [hK_def, hG_def, hg]
    exact toConjAct_GLPos_Gamma_p_α_le_Gamma1_map (N := N)
      (T_p_lower p hp.pos) (glMap_det_pos_of_rat_det_pos _ (T_p_lower_det_pos p hp.pos))
  set r : Fin p → G := fun i ↦
    ⟨SL2Z_to_PSL2R (shiftSL_loc (i.val : ℤ)),
      Subgroup.mem_map_of_mem SL2Z_to_PSL2R (shiftSL_loc_mem_Gamma1 (i.val : ℤ))⟩
    with hr_def
  set e : Fin p ≃ G ⧸ (K.subgroupOf G) :=
    Equiv.ofBijective _ (shiftSL_loc_tile_transversal_bijective p hp hpN g hg) with he_def
  have hbase : IsFundamentalDomain G (Gamma1_fundDomain_PSL N) μ_hyp :=
    isFundamentalDomain_Gamma1_map_PSL_R (N := N)
  have htool : IsFundamentalDomain (K.subgroupOf G)
      (⋃ i, (r i : PSL(2, ℝ)) • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp :=
    hbase.iUnion_smul_of_transversal e (fun i ↦ rfl)
  have htrans := htool.image_of_equiv (Equiv.refl ℍ)
    (MeasureTheory.Measure.QuasiMeasurePreserving.id μ_hyp)
    (Subgroup.subgroupOfEquivOfLe hKG).symm.toEquiv (fun _ _ ↦ rfl)
  simp only [Equiv.coe_refl, Set.image_id] at htrans
  exact htrans

open Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- **[T006-b-L4-FD-d] The bad-prime Hecke-tile fundamental domain.** The `p` det-`p` upper
Hecke tiles `D = ⋃_{b<p} [1,b;0,p] • Γ₁-FD` form a fundamental domain for the adjoint-side group
`Γ_p(diag(p,1)) = {γ ∈ Γ₁ : γ₁₀ ≡ 0 (mod pN)}` (index `p`), at the `PSL(2, ℝ)` level.  This is
the bad-prime analogue of `DeltaBSystem.isFundamentalDomain_Hecke_tiles_Gamma_p_α` (no `M_∞`
tile, `Fin p` instead of `Option (Fin p)`).  It discharges the `hFD` hypothesis of
`petN_doubleCoset_adjoint` for the bad prime, closing the bad-prime Petersson adjoint
(DS Prop 5.6.2).

The `α = diag(p,1) = T_p_lower` is the *adjoint*-side matrix `α' = det(α)·α⁻¹` (DS 5.5.2):
`g' = g ∣ diag(p,1)` is `Γ_p(diag(p,1))`-invariant, which is what the LHS bridge
`peterssonInner_badUp_sum_slashes_eq_aggregate` produces. -/
theorem isFundamentalDomain_BadHecke_tiles
    (p : ℕ) (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) :
    IsFundamentalDomain
      (((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R))
      (⋃ b ∈ (Finset.univ : Finset (Fin p)),
        (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) •
          (Gamma1_fundDomain_PSL N : Set ℍ))
      μ_hyp := by
  set A : GL (Fin 2) ℝ := glMap (T_p_lower p hp.pos) with hA_def
  have hApos : 0 < A.det.val := glMap_det_pos_of_rat_det_pos _ (T_p_lower_det_pos p hp.pos)
  set A' : GL(2, ℝ)⁺ := ⟨A, hApos⟩ with hA'_def
  set g : PSL(2, ℝ) := GLPos_to_PSL_R_term A' with hg_def
  set D : Set ℍ := ⋃ i : Fin p, (glMap (T_p_upper p hp.pos i.val) : GL (Fin 2) ℝ) •
    (Gamma1_fundDomain_PSL N : Set ℍ) with hD_def
  -- The goal's `biUnion`-tiling equals the `iUnion`-tiling `D`.
  have hD_eq : (⋃ b ∈ (Finset.univ : Finset (Fin p)),
      (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) •
        (Gamma1_fundDomain_PSL N : Set ℍ)) = D := by
    rw [hD_def]; refine Set.iUnion_congr fun i ↦ ?_; simp
  rw [hD_eq]
  -- Step (I): FD for the conjugate group `toConjAct g • Γ_p(A).map` on `A • D`.
  have hI : IsFundamentalDomain
      ((ConjAct.toConjAct g • ((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R)) :
        Subgroup PSL(2, ℝ))
      (A • D) μ_hyp :=
    iUnion_shiftSL_loc_isFundamentalDomain_conj p hp hpN g hg_def
  -- Step (II): conjugate by `g⁻¹` to descend to `Γ_p(A).map` on `g⁻¹ • (A • D) = D`.
  have hconj : ((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R) =
      ConjAct.toConjAct g⁻¹ •
        (ConjAct.toConjAct g • ((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R)) := by
    rw [smul_smul, ConjAct.toConjAct_inv, inv_mul_cancel, one_smul]
  have hII := hI.smul_of_eq_conjAct (g := g⁻¹) hconj
  have hset : g⁻¹ • (A • D) = D := by
    have hgA : (A • D : Set ℍ) = g • D := (GLPos_to_PSL_R_term_smul_set A' D).symm
    rw [hgA, inv_smul_smul]
  rwa [hset] at hII

end HeckeRing.GL2

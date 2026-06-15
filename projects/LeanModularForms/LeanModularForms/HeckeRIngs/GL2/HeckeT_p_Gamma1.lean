/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeActionGeneral
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_GLpair

/-!
# Connection between `heckeT_p_fun` and `heckeSlash_gen (Gamma1_pair N)`

This file relates the explicit Hecke operator `T_p` defined via coset representatives in
`HeckeT_p.lean` to the abstract Hecke slash action `heckeSlash_gen (Gamma1_pair N)` from
`HeckeActionGeneral.lean`, at level `N` (not requiring SL₂(ℤ)-invariance), via the double
coset `D_p_Gamma1` and the diamond identity `slash_M_infty_eq_diamond_slash_T_p_lower`.

## References

* Diamond–Shurman, *A First Course in Modular Forms*, §5.2, Proposition 5.2.1
* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

/-- The natural number `a ∈ [0, N)` with `a ≡ p⁻¹ (mod N)`. -/
noncomputable def aInvOfCoprime (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) : ℕ :=
  (((ZMod.unitOfCoprime p hpN)⁻¹ : (ZMod N)ˣ) : ZMod N).val

/-- `aInvOfCoprime · p ≡ 1 (mod N)`. -/
lemma aInvOfCoprime_mul_eq_one (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    (aInvOfCoprime N p hpN : ZMod N) * (p : ZMod N) = 1 := by
  rw [aInvOfCoprime, ZMod.natCast_val, ZMod.cast_id, ← ZMod.coe_unitOfCoprime p hpN,
    ← Units.val_mul, inv_mul_cancel, Units.val_one]

/-- `N` divides `aInvOfCoprime · p - 1`. -/
lemma N_dvd_aInv_mul_p_sub_one (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    (N : ℤ) ∣ ((aInvOfCoprime N p hpN : ℤ) * p - 1) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  exact sub_eq_zero_of_eq (aInvOfCoprime_mul_eq_one N p hpN)

/-- The integer `m` such that `aInvOfCoprime · p - 1 = N · m`. -/
noncomputable def mIdxOfCoprime (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) : ℤ :=
  ((aInvOfCoprime N p hpN : ℤ) * p - 1) / (N : ℤ)

/-- Bezout identity: `N · mIdxOfCoprime = aInvOfCoprime · p - 1`. -/
lemma N_mul_mIdx_eq (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    (N : ℤ) * mIdxOfCoprime N p hpN = (aInvOfCoprime N p hpN : ℤ) * p - 1 :=
  Int.mul_ediv_cancel' (N_dvd_aInv_mul_p_sub_one N p hpN)

/-- `σ_p_specific = [[a, 1], [N·m, p]]` where `a · p − N · m = 1`, so the determinant
is `1` and the lower-right entry is exactly `p`. -/
noncomputable def sigma_p_specific (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) : SL(2, ℤ) :=
  ⟨!![(aInvOfCoprime N p hpN : ℤ), 1; (N : ℤ) * mIdxOfCoprime N p hpN, (p : ℤ)], by
    rw [det_fin_two_of]
    linear_combination -N_mul_mIdx_eq N p hpN⟩

@[simp] lemma sigma_p_specific_val (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    (sigma_p_specific N p hpN : Matrix (Fin 2) (Fin 2) ℤ) =
    !![(aInvOfCoprime N p hpN : ℤ), 1; (N : ℤ) * mIdxOfCoprime N p hpN, (p : ℤ)] := rfl

/-- `σ_p_specific` lies in `Gamma0 N`: lower-left entry `N · m ≡ 0 mod N`. -/
lemma sigma_p_specific_mem_Gamma0 (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    sigma_p_specific N p hpN ∈ Gamma0 N := by
  simp [Gamma0_mem, sigma_p_specific]

/-- The `Gamma0MapUnits` of `σ_p_specific` is `(p : ZMod N)ˣ`. -/
lemma Gamma0MapUnits_sigma_p_specific (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    Gamma0MapUnits ⟨sigma_p_specific N p hpN, sigma_p_specific_mem_Gamma0 N p hpN⟩ =
    ZMod.unitOfCoprime p hpN := by
  ext
  simp [Gamma0MapUnits_val, Gamma0Map, sigma_p_specific]

private lemma M_infty_det_ne_zero (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    (!![((aInvOfCoprime N p hpN : ℤ) : ℚ) * p, 1;
        ((N : ℤ) * mIdxOfCoprime N p hpN : ℚ) * p, p] : Matrix (Fin 2) (Fin 2) ℚ).det ≠ 0 := by
  have h_q : ((N : ℤ) * mIdxOfCoprime N p hpN : ℚ) = (aInvOfCoprime N p hpN : ℤ) * p - 1 :=
    mod_cast N_mul_mIdx_eq N p hpN
  refine ne_of_eq_of_ne ?_ (Nat.cast_ne_zero.mpr hp.ne' : (p : ℚ) ≠ 0)
  rw [det_fin_two_of]
  linear_combination -(p : ℚ) * h_q

/-- The `(p+1)`-th coset representative for the double coset `D_p_Gamma1`, defined
directly as the matrix `[[ap, 1], [Nmp, p]]` where `ap − Nm = 1`. It equals
`mapGL ℚ σ_p_specific · T_p_lower` (see `M_infty_eq_sigma_mul_T_p_lower`). -/
noncomputable def M_infty (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero
    !![((aInvOfCoprime N p hpN : ℤ) : ℚ) * p, 1;
       ((N : ℤ) * mIdxOfCoprime N p hpN : ℚ) * p, p]
    (M_infty_det_ne_zero N p hp hpN)

@[simp] lemma M_infty_val (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    (M_infty N p hp hpN : Matrix (Fin 2) (Fin 2) ℚ) =
    !![((aInvOfCoprime N p hpN : ℤ) : ℚ) * p, 1;
       ((N : ℤ) * mIdxOfCoprime N p hpN : ℚ) * p, p] := rfl

/-- `M_∞` equals the product `(mapGL ℚ σ_p_specific) · T_p_lower` in `GL₂(ℚ)`.
This is the form that gives the diamond-twisted slash identity. -/
lemma M_infty_eq_sigma_mul_T_p_lower (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    M_infty N p hp hpN = mapGL ℚ (sigma_p_specific N p hpN) * T_p_lower p hp := by
  apply Units.ext
  rw [M_infty_val, Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mapGL_coe_matrix]

/-- The diamond identity: for any modular form `f`, slashing `f` by `M_∞` equals
slashing `(⟨p⟩ f)` by `T_p_lower`. This ties the abstract sum (which uses `M_∞`)
to the explicit `T_p` formula (which uses `(⟨p⟩ f) ∣ T_p_lower`). -/
lemma slash_M_infty_eq_diamond_slash_T_p_lower {N : ℕ} [NeZero N] (k : ℤ) (p : ℕ) (hp : 0 < p)
    (hpN : Nat.Coprime p N) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑f ∣[k] (M_infty N p hp hpN : GL (Fin 2) ℚ) =
    ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k] (T_p_lower p hp : GL (Fin 2) ℚ) := by
  rw [M_infty_eq_sigma_mul_T_p_lower, diamondOp_eq_diamondOpAux k _
    ⟨sigma_p_specific N p hpN, sigma_p_specific_mem_Gamma0 N p hpN⟩
    (Gamma0MapUnits_sigma_p_specific N p hpN)]
  change ⇑f ∣[k] glMap (mapGL ℚ (sigma_p_specific N p hpN) * T_p_lower p hp) =
    (⇑f ∣[k] mapGL ℝ (sigma_p_specific N p hpN)) ∣[k] glMap (T_p_lower p hp)
  rw [map_mul, glMap_mapGL_eq, ← SlashAction.slash_mul]

/-- **Bridge lemma**: the explicit Γ₁(N)-level `heckeT_p_fun` sum coincides with the
naive double-coset sum (upper-triangular reps plus `M_∞`), for any modular form. The
diamond twist inside `heckeT_p_fun` is exactly absorbed by the diamond identity at `M_∞`. -/
lemma heckeT_p_fun_eq_coset_sum {N : ℕ} [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    heckeT_p_fun k p hp hpN f =
    heckeT_p_ut k p hp.pos (⇑f) + (⇑f) ∣[k] (M_infty N p hp.pos hpN : GL (Fin 2) ℚ) := by
  rw [heckeT_p_fun, slash_M_infty_eq_diamond_slash_T_p_lower k p hp.pos hpN f]

end HeckeRing.GL2

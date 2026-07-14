/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.Newforms.LevelRaiseComm

/-!
# Bad-prime stability of the extended oldform subspace

For a prime `p ∣ N`, the bad Hecke operator `U_p = heckeT_n_cusp k p` preserves the extended
oldform subspace `cuspFormsOldExtended N k`.  This is Diamond–Shurman Prop 5.6.2 / Ex 5.6.3(b)(c)
for the bad prime: the two level-raise/level-inclusion generators of the extended old space are
each sent back into the old space by `U_p`.

The good-prime, non-extended analogue is `heckeT_n_preserves_cuspFormsOld` (LevelRaiseComm.lean);
this file handles the bad prime and the extra level-inclusion generators.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open scoped MatrixGroups ModularForm Pointwise

variable {N : ℕ} [NeZero N] {k : ℤ}

lemma coe_heckeT_n_cusp_divN (p : ℕ) [NeZero p] (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(heckeT_n_cusp k p f) : UpperHalfPlane → ℂ) = heckeT_p_ut k p hp.pos (⇑f) := by
  have h1 : (⇑(heckeT_n_cusp k p f) : UpperHalfPlane → ℂ) =
      ⇑(heckeT_n k p f.toModularForm') := by
    rw [← heckeT_n_cusp_toModularForm']; rfl
  rw [h1, heckeT_n_prime k hp, heckeT_p_all_not_coprime_apply k hp hpN]
  rfl

/-- **Good-prime bridge.** For `p` coprime to `M`, the underlying function of
`T_p g' = heckeT_n_cusp k p g'` is the full Hecke sum `heckeT_p_fun`. -/
private lemma coe_heckeT_n_cusp_coprime
    {M : ℕ} [NeZero M] (p : ℕ) [NeZero p] (hp : Nat.Prime p) (hpM : Nat.Coprime p M)
    (g' : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (⇑(heckeT_n_cusp k p g') : UpperHalfPlane → ℂ) = heckeT_p_fun k p hp hpM g'.toModularForm' := by
  have h1 : (⇑(heckeT_n_cusp k p g') : UpperHalfPlane → ℂ) =
      ⇑(heckeT_n k p g'.toModularForm') := by
    rw [← heckeT_n_cusp_toModularForm']; rfl
  rw [h1, heckeT_n_prime k hp, heckeT_p_all_coprime k hp hpM]
  rfl

/-- **Bad-prime `U_p` commutes with the trivial level inclusion when `p ∣ M`.**
For `M ∣ N`, `p ∣ M` (hence `p ∣ N`), the bad operator `U_p^{(N)}` on an included form
agrees with the inclusion of `U_p^{(M)}` applied at level `M`, since both underlying
functions are the level-independent upper sum `heckeT_p_ut k p ⇑g'`. -/
private lemma heckeT_n_cusp_levelInclude_divM
    {M : ℕ} [NeZero M] (p : ℕ) [NeZero p] (hp : Nat.Prime p)
    (hpN : ¬ Nat.Coprime p N) (hpM : ¬ Nat.Coprime p M) (hMN : M ∣ N)
    (g' : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    heckeT_n_cusp k p (levelInclude_cusp hMN k g') =
      levelInclude_cusp hMN k (heckeT_n_cusp k p g') := by
  apply CuspForm.ext
  intro z
  rw [show (heckeT_n_cusp k p (levelInclude_cusp hMN k g')) z =
      (⇑(heckeT_n_cusp k p (levelInclude_cusp hMN k g')) : UpperHalfPlane → ℂ) z from rfl,
    coe_heckeT_n_cusp_divN p hp hpN (levelInclude_cusp hMN k g'), levelInclude_cusp_coe]
  rw [show (levelInclude_cusp hMN k (heckeT_n_cusp k p g')) z =
      (⇑(levelInclude_cusp hMN k (heckeT_n_cusp k p g')) : UpperHalfPlane → ℂ) z from rfl,
    levelInclude_cusp_coe, coe_heckeT_n_cusp_divN p hp hpM g']

/-- **Bad-prime `U_p` on a trivial inclusion when `p ∤ M`.**
For `M ∣ N`, `p ∣ N` but `p ∤ M`, the upper-triangular sum equals the full level-`M`
Hecke operator minus the diagonal `T_p_lower` term, the latter being the level-raise
`α_p` of `⟨p⟩ g'`.  As underlying functions (DS Ex 5.6.3(b), the `p ∤ N p⁻¹` clause):
`U_p^{(N)}(i_M g') = i_M(T_p^{(M)} g') − p^{k-1} • i_{pM}(α_p ⟨p⟩ g')`. -/
private lemma heckeT_n_cusp_levelInclude_coprimeM
    {M : ℕ} [NeZero M] (p : ℕ) [NeZero p] (hp : Nat.Prime p)
    (hpN : ¬ Nat.Coprime p N) (hpM : Nat.Coprime p M) (hMN : M ∣ N) (hpdvdN : (p : ℕ) ∣ N)
    (g' : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    haveI : NeZero (p * M) := ⟨Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne M)⟩
    heckeT_n_cusp k p (levelInclude_cusp hMN k g') =
      levelInclude_cusp hMN k (heckeT_n_cusp k p g') -
        ((p : ℂ) ^ (k - 1)) • levelInclude_cusp
          (hpM.mul_dvd_of_dvd_of_dvd hpdvdN hMN) k
          (levelRaise M p k (diamondOp_cusp k (ZMod.unitOfCoprime p hpM) g')) := by
  haveI : NeZero (p * M) := ⟨Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne M)⟩
  apply CuspForm.ext
  intro z
  -- LHS function: the level-independent upper sum.
  rw [show (heckeT_n_cusp k p (levelInclude_cusp hMN k g')) z =
      (⇑(heckeT_n_cusp k p (levelInclude_cusp hMN k g')) : UpperHalfPlane → ℂ) z from rfl,
    coe_heckeT_n_cusp_divN p hp hpN (levelInclude_cusp hMN k g'), levelInclude_cusp_coe]
  -- RHS: expand both summands' functions.
  simp only [CuspForm.coe_sub, Pi.sub_apply, levelInclude_cusp_coe,
    coe_heckeT_n_cusp_coprime p hp hpM g']
  -- Now both sides are concrete functions; unfold `heckeT_p_fun` and the `levelRaiseFun`.
  show heckeT_p_ut k p hp.pos (⇑g') z =
    (heckeT_p_ut k p hp.pos (⇑g'.toModularForm') +
      ⇑(diamondOp k (ZMod.unitOfCoprime p hpM) g'.toModularForm') ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ)) z -
    ((p : ℂ) ^ (k - 1)) • levelRaiseFun p k
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpM) g')) z
  rw [levelRaiseFun]
  have hglmap : glMap (T_p_lower p hp.pos) = levelRaiseMatrix p := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T_p_lower, levelRaiseMatrix, glMap, Matrix.GeneralLinearGroup.map,
        Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have hdia : (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpM) g') : UpperHalfPlane → ℂ) =
      ⇑(diamondOp k (ZMod.unitOfCoprime p hpM) g'.toModularForm') := rfl
  rw [hdia, ← hglmap]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (⇑g'.toModularForm' : UpperHalfPlane → ℂ) = ⇑g' from rfl]
  have hscalar : ((p : ℂ) ^ (k - 1)) * ((p : ℂ) ^ (1 - k)) = 1 := by
    rw [← zpow_add₀ (by exact_mod_cast hp.ne_zero)]; simp
  set X := (⇑(diamondOp k (ZMod.unitOfCoprime p hpM) g'.toModularForm') ∣[k]
    glMap (T_p_lower p hp.pos)) z with hX
  rw [show (⇑(diamondOp k (ZMod.unitOfCoprime p hpM) g'.toModularForm') ∣[k]
      (T_p_lower p hp.pos : GL (Fin 2) ℚ)) z = X from rfl,
    show ((p : ℂ) ^ (k - 1)) * (((p : ℂ) ^ (1 - k)) * X) =
      (((p : ℂ) ^ (k - 1)) * ((p : ℂ) ^ (1 - k))) * X by ring, hscalar, one_mul]
  ring

/-- **A level-raise (with `d > 1`) included into `N` lies in the extended old space.**
Both when the intermediate level `d*M'` equals `N` (then it is an `IsOldformGenerator`)
and when `d*M' < N` (then it is an `IsLevelInclusionOldformGenerator`). -/
private lemma levelInclude_levelRaise_mem_cuspFormsOldExtended
    {M' : ℕ} [NeZero M'] (d : ℕ) [NeZero d] (hd : 1 < d) (hdvd : d * M' ∣ N)
    (h : CuspForm ((Gamma1 M').map (mapGL ℝ)) k) :
    levelInclude_cusp hdvd k (levelRaise M' d k h) ∈ cuspFormsOldExtended N k := by
  haveI : NeZero (d * M') := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M')⟩
  rcases lt_or_eq_of_le (Nat.le_of_dvd (NeZero.pos N) hdvd) with hlt | heq
  · exact levelInclude_cusp_mem_cuspFormsOldExtended hdvd hlt (levelRaise M' d k h)
  · -- `d * M' = N`: the inclusion is a transport, so it is an oldform generator.
    have hxeq : levelInclude_cusp hdvd k (levelRaise M' d k h) =
        heq ▸ levelRaise M' d k h := by
      apply CuspForm.ext
      intro z
      rw [show (levelInclude_cusp hdvd k (levelRaise M' d k h)) z =
          (⇑(levelInclude_cusp hdvd k (levelRaise M' d k h)) : UpperHalfPlane → ℂ) z from rfl,
        levelInclude_cusp_coe, eqRec_cuspForm_apply]
    rw [hxeq]
    exact Submodule.subset_span (Or.inl ⟨M', d, inferInstance, inferInstance, hd, heq, h, rfl⟩)

/-- **Bad-prime level-raise commutation, Regime A (`p ∤ d`).**
When the level-raise amount `d` is coprime to `p` (and `p ∣ N = d*M`, forcing `p ∣ M`),
the bad operator `U_p` commutes with `levelRaise`, exactly as in the coprime case but with the
diagonal `T_p_lower` term absent.  (DS Ex 5.6.3(a) for `T = U_p` at the bad prime.) -/
private lemma heckeT_n_cusp_levelRaise_coprimeD
    {M : ℕ} [NeZero M] (p : ℕ) [NeZero p] (hp : Nat.Prime p) (d : ℕ) [NeZero d]
    (hdp : Nat.Coprime d p) (heq : d * M = N) (hpN : ¬ Nat.Coprime p N)
    (hpM : ¬ Nat.Coprime p M)
    (g' : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    heckeT_n_cusp k p (heq ▸ levelRaise M d k g') =
      heq ▸ levelRaise M d k (heckeT_n_cusp k p g') := by
  apply CuspForm.ext
  intro z
  -- LHS: bridge at level N, then `heckeT_p_ut_levelRaise` + reindex.
  subst heq
  rw [show (heckeT_n_cusp k p (levelRaise M d k g')) z =
      (⇑(heckeT_n_cusp k p (levelRaise M d k g')) : UpperHalfPlane → ℂ) z from rfl,
    coe_heckeT_n_cusp_divN p hp hpN (levelRaise M d k g')]
  rw [show (⇑(levelRaise M d k g') : UpperHalfPlane → ℂ) =
      ⇑((levelRaise M d k g').toModularForm') from rfl,
    heckeT_p_ut_levelRaise p hp M d g',
    heckeT_p_ut_levelRaise_reindex p hp M d hdp g']
  -- RHS: `levelRaise (U_p g')`, whose function is `d^{1-k} • (heckeT_p_ut ⇑g' ∣[k] α_d)`.
  rw [show (levelRaise M d k (heckeT_n_cusp k p g')) z =
      (⇑(levelRaise M d k (heckeT_n_cusp k p g')) : UpperHalfPlane → ℂ) z from rfl,
    coe_levelRaise, levelRaiseFun]
  simp only [Pi.smul_apply, smul_eq_mul]
  congr 2
  rw [show (⇑(heckeT_n_cusp k p g') : UpperHalfPlane → ℂ) =
      heckeT_p_ut k p hp.pos ⇑g' from coe_heckeT_n_cusp_divN p hp hpM g']
  rfl

/-- **Scalar-matrix slash collapse.** Slashing by `[1,0;0,p]·α_p = p·I` scales by `p^{k-2}`.
This is the algebraic core of the `U_p`-collapse in Regime B (`p ∣ d`): the bad operator
"undoes" one factor of `p` from a level raise. -/
private lemma bp_slash_scalar_collapse (p : ℕ) [NeZero p] (hp : Nat.Prime p)
    (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    (f ∣[k] (glMap (T_p_upper p hp.pos 0) * levelRaiseMatrix p)) z = ((p : ℂ) ^ (k - 2)) * f z := by
  set M := glMap (T_p_upper p hp.pos 0) * levelRaiseMatrix p with hMdef
  have hM : (↑M : Matrix (Fin 2) (Fin 2) ℝ) = !![(p : ℝ), 0; 0, p] := by
    rw [hMdef]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T_p_upper, levelRaiseMatrix, glMap, Matrix.GeneralLinearGroup.map,
        Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]
  have hp0R : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp0C : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hdetval : (M.det.val : ℝ) = (p : ℝ) ^ 2 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hM, Matrix.det_fin_two]
    simp; ring
  have hdetpos : (0 : ℝ) < M.det.val := by rw [hdetval]; positivity
  have hσ : UpperHalfPlane.σ M = ContinuousAlgEquiv.refl ℝ ℂ := by
    unfold UpperHalfPlane.σ; rw [if_pos hdetpos]
  have hdenom : UpperHalfPlane.denom M ↑z = (p : ℂ) := by
    rw [UpperHalfPlane.denom, hM]; simp
  have hsmul : M • z = z := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul, UpperHalfPlane.num, hσ, ContinuousAlgEquiv.refl_apply,
      UpperHalfPlane.denom, hM]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Complex.ofReal_natCast,
      add_zero, zero_mul, zero_add, Complex.ofReal_zero]
    rw [mul_comm, mul_div_assoc, div_self hp0C, mul_one]
  rw [ModularForm.slash_apply, hσ, hsmul, hdenom, ContinuousAlgEquiv.refl_apply, hdetval]
  rw [show |((p : ℝ) ^ 2 : ℝ)| = (p : ℝ) ^ 2 from abs_of_nonneg (by positivity)]
  rw [show (((p : ℝ) ^ 2 : ℝ) : ℂ) = (p : ℂ) ^ 2 from by push_cast; ring]
  rw [mul_assoc, ← zpow_natCast (p : ℂ) 2, ← zpow_mul, ← zpow_add₀ hp0C, mul_comm]
  congr 1
  ring

/-- `levelRaiseMatrix (p*e) = levelRaiseMatrix p * levelRaiseMatrix e`. -/
private lemma bp_levelRaiseMatrix_mul (p e : ℕ) [NeZero p] [NeZero e] :
    (levelRaiseMatrix (p * e) : GL (Fin 2) ℝ) = levelRaiseMatrix p * levelRaiseMatrix e := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- **Bad-prime level-raise collapse, Regime B (`p ∣ d`).** Writing `d = p*e`, the bad operator
`U_p` collapses one factor of `p` from a level raise, at the function level:
`heckeT_p_ut k p ⇑(levelRaise M d g') = levelRaiseFun e k ⇑g'`.
This is DS Ex 5.6.3(b)'s second sum (`Σ g[α_p][...] = p^{k-1} g`). -/
private lemma bp_heckeT_p_ut_levelRaise_collapse
    {M : ℕ} [NeZero M] (p : ℕ) [NeZero p] (hp : Nat.Prime p) (e : ℕ) [NeZero e]
    (g' : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    haveI : NeZero (p * e) := ⟨Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne e)⟩
    heckeT_p_ut k p hp.pos (⇑((levelRaise M (p * e) k g').toModularForm')) =
      levelRaiseFun e k ⇑g' := by
  haveI : NeZero (p * e) := ⟨Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne e)⟩
  rw [heckeT_p_ut_levelRaise p hp M (p * e) g']
  -- All summands have `(p*e)*b % p = 0`.
  have hmod : ∀ b : ℕ, (p * e) * b % p = 0 := fun b ↦ by
    rw [mul_assoc]; exact Nat.mul_mod_right p (e * b)
  simp_rw [hmod]
  rw [Finset.sum_const, Finset.card_range]
  -- Reduce the constant summand `(⇑g' ∣[k] T_p_upper 0) ∣[k] α_{pe}` via the scalar collapse.
  have hg'coe : (⇑g'.toModularForm' : UpperHalfPlane → ℂ) = ⇑g' := rfl
  have hF : (⇑g'.toModularForm' ∣[k] (T_p_upper p hp.pos 0 : GL (Fin 2) ℚ)) ∣[k]
      levelRaiseMatrix (p * e) = ((p : ℂ) ^ (k - 2)) • (⇑g' ∣[k] levelRaiseMatrix e) := by
    rw [hg'coe]
    rw [show (⇑g' ∣[k] (T_p_upper p hp.pos 0 : GL (Fin 2) ℚ)) =
        ⇑g' ∣[k] glMap (T_p_upper p hp.pos 0) from rfl]
    rw [← SlashAction.slash_mul, bp_levelRaiseMatrix_mul, ← mul_assoc, SlashAction.slash_mul,
      show (⇑g' ∣[k] (glMap (T_p_upper p hp.pos 0) * levelRaiseMatrix p)) =
        ((p : ℂ) ^ (k - 2)) • ⇑g' from by funext w; rw [bp_slash_scalar_collapse p hp]; rfl,
      ModularForm.smul_slash, σ_levelRaiseMatrix e, ContinuousAlgEquiv.refl_apply]
  -- Combine the scalars `p · (pe)^{1-k} · p^{k-2}` into the `levelRaiseFun e` normaliser `e^{1-k}`.
  have hp0C : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hscalar : (p : ℂ) * ((↑(p * e) : ℂ) ^ (1 - k) * (p : ℂ) ^ (k - 2)) = (e : ℂ) ^ (1 - k) := by
    have hpe : (↑(p * e) : ℂ) = (p : ℂ) * (e : ℂ) := by push_cast; ring
    rw [hpe, mul_zpow]
    rw [show (p : ℂ) * ((p : ℂ) ^ (1 - k) * (e : ℂ) ^ (1 - k) * (p : ℂ) ^ (k - 2)) =
        ((p : ℂ) ^ (1 : ℤ) * (p : ℂ) ^ (1 - k) * (p : ℂ) ^ (k - 2)) * (e : ℂ) ^ (1 - k) from by
      rw [zpow_one]; ring]
    rw [← zpow_add₀ hp0C, ← zpow_add₀ hp0C,
      show (1 : ℤ) + (1 - k) + (k - 2) = 0 from by ring, zpow_zero, one_mul]
  funext z
  rw [levelRaiseFun]
  simp only [Pi.smul_apply, nsmul_eq_mul]
  rw [hF]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show ((p : ℂ) *
      (↑(p * e) ^ (1 - k) * ((p : ℂ) ^ (k - 2) * (⇑g' ∣[k] levelRaiseMatrix e) z))) =
      ((p : ℂ) * ((↑(p * e) : ℂ) ^ (1 - k) * (p : ℂ) ^ (k - 2))) *
        ((⇑g' ∣[k] levelRaiseMatrix e) z) from by ring, hscalar]

/-- **Bad-prime level-raise membership, Regime B (`p ∣ d`).** Writing `d = p*e`, the bad
operator `U_p` on a level raise by `d` lands in the extended old space: it equals (as a cusp
form) the inclusion of the level-`e*M` raise `levelRaise M e g'`, which lies in `oldExt`. -/
private lemma heckeT_n_cusp_levelRaise_divD_mem
    {M : ℕ} [NeZero M] (p : ℕ) [NeZero p] (hp : Nat.Prime p) (e : ℕ) [NeZero e]
    (heq : (p * e) * M = N) (hpN : ¬ Nat.Coprime p N)
    (g' : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    heckeT_n_cusp k p (heq ▸ levelRaise M (p * e) k g') ∈ cuspFormsOldExtended N k := by
  haveI : NeZero (p * e) := ⟨Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne e)⟩
  haveI : NeZero (e * M) := ⟨Nat.mul_ne_zero (NeZero.ne e) (NeZero.ne M)⟩
  have heMN : e * M ∣ N := ⟨p, by rw [← heq]; ring⟩
  -- `U_p (levelRaise M (p*e) g') = levelInclude (levelRaise M e g')` as cusp forms.
  have hcusp : heckeT_n_cusp k p (heq ▸ levelRaise M (p * e) k g') =
      levelInclude_cusp heMN k (levelRaise M e k g') := by
    subst heq
    apply CuspForm.ext
    intro z
    rw [show (heckeT_n_cusp k p (levelRaise M (p * e) k g')) z =
        (⇑(heckeT_n_cusp k p (levelRaise M (p * e) k g')) : UpperHalfPlane → ℂ) z from rfl,
      coe_heckeT_n_cusp_divN p hp hpN (levelRaise M (p * e) k g')]
    rw [show (⇑(levelRaise M (p * e) k g') : UpperHalfPlane → ℂ) =
        ⇑((levelRaise M (p * e) k g').toModularForm') from rfl,
      bp_heckeT_p_ut_levelRaise_collapse p hp e g']
    rw [show (levelInclude_cusp heMN k (levelRaise M e k g')) z =
        (⇑(levelInclude_cusp heMN k (levelRaise M e k g')) : UpperHalfPlane → ℂ) z from rfl,
      levelInclude_cusp_coe, coe_levelRaise]
  rw [hcusp]
  -- Membership of `levelInclude (levelRaise M e g')`: since `e*M = N/p < N` (as `p ≥ 2`),
  -- this is a level-inclusion generator regardless of `e`.
  have heMltN : e * M < N := by
    rw [← heq]
    have hpos : 0 < e * M := Nat.mul_pos (NeZero.pos e) (NeZero.pos M)
    calc e * M = 1 * (e * M) := (one_mul _).symm
      _ < p * (e * M) := (Nat.mul_lt_mul_right hpos).mpr hp.one_lt
      _ = (p * e) * M := by ring
  exact levelInclude_cusp_mem_cuspFormsOldExtended heMN heMltN (levelRaise M e k g')

theorem heckeT_n_cusp_divN_mem_cuspFormsOldExtended
    {N : ℕ} [NeZero N] {k : ℤ} (p : ℕ) [NeZero p] (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hg : g ∈ cuspFormsOldExtended N k) :
    heckeT_n_cusp k p g ∈ cuspFormsOldExtended N k := by
  refine Submodule.span_induction
    (p := fun x _ ↦ heckeT_n_cusp k p x ∈ cuspFormsOldExtended N k)
    ?_ ?_ ?_ ?_ hg
  · -- generator case
    rintro f₀ (hgen | hinc)
    · -- IsOldformGenerator: `f₀ = heq ▸ levelRaise M d k g'`, `d*M = N`, `d > 1`.
      obtain ⟨M, d, _, _, hd, heq, g', rfl⟩ := hgen
      by_cases hdp : Nat.Coprime d p
      · -- Regime A (`p ∤ d`): `U_p` commutes with `levelRaise`; result is an oldform generator.
        have hpM : ¬ Nat.Coprime p M := by
          intro hpMc
          refine hpN ?_
          rw [← heq]
          exact (Nat.coprime_mul_iff_right).mpr ⟨hdp.symm, hpMc⟩
        rw [heckeT_n_cusp_levelRaise_coprimeD p hp d hdp heq hpN hpM g']
        exact Submodule.subset_span
          (Or.inl ⟨M, d, inferInstance, inferInstance, hd, heq, _, rfl⟩)
      · -- Regime B (`p ∣ d`): write `d = p*e` and apply the collapse-membership lemma.
        have hpd : (p : ℕ) ∣ d := by
          by_contra h; exact hdp (Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr h))
        obtain ⟨e, rfl⟩ := hpd
        haveI : NeZero e := ⟨by rintro rfl; simp at hd⟩
        exact heckeT_n_cusp_levelRaise_divD_mem p hp e heq hpN g'
    · -- IsLevelInclusionOldformGenerator: `f₀ = levelInclude_cusp hMN k g'`, `M < N`.
      obtain ⟨M, _, hMN, hMltN, g', rfl⟩ := hinc
      by_cases hpM : Nat.Coprime p M
      · -- `p ∤ M`: the bad-prime decomposition into a level inclusion and a level raise.
        haveI : NeZero (p * M) := ⟨Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne M)⟩
        have hpdvdN : (p : ℕ) ∣ N := by
          by_contra h; exact hpN (hp.coprime_iff_not_dvd.mpr h)
        rw [heckeT_n_cusp_levelInclude_coprimeM p hp hpN hpM hMN hpdvdN g']
        refine (cuspFormsOldExtended N k).sub_mem
          (levelInclude_cusp_mem_cuspFormsOldExtended hMN hMltN _)
          ((cuspFormsOldExtended N k).smul_mem _ ?_)
        exact levelInclude_levelRaise_mem_cuspFormsOldExtended p hp.one_lt _ _
      · -- `p ∣ M`: `U_p` commutes with the inclusion.
        rw [heckeT_n_cusp_levelInclude_divM p hp hpN hpM hMN g']
        exact levelInclude_cusp_mem_cuspFormsOldExtended hMN hMltN _
  · show heckeT_n_cusp k p (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsOldExtended N k
    rw [heckeT_n_cusp_zero]
    exact (cuspFormsOldExtended N k).zero_mem
  · intros f₁ f₂ _ _ ih₁ ih₂
    show heckeT_n_cusp k p (f₁ + f₂) ∈ cuspFormsOldExtended N k
    rw [heckeT_n_cusp_add]
    exact (cuspFormsOldExtended N k).add_mem ih₁ ih₂
  · intros c f₁ _ ih
    show heckeT_n_cusp k p (c • f₁) ∈ cuspFormsOldExtended N k
    rw [heckeT_n_cusp_smul]
    exact (cuspFormsOldExtended N k).smul_mem c ih

end HeckeRing.GL2

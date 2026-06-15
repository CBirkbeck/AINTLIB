/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import LeanModularForms.Eigenforms.ConductorTheorem
import LeanModularForms.HeckeRIngs.GL2.AdjointTheoryPetersson
import LeanModularForms.HeckeRIngs.GL2.CharacterDecomp
import LeanModularForms.HeckeRIngs.GL2.LevelEmbed
import LeanModularForms.HeckeRIngs.GL2.LevelRaise
import LeanModularForms.HeckeRIngs.GL2.Newforms.Basic
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.Modularforms.DimensionFormulas
import LeanModularForms.Modularforms.LFunction
import LeanModularForms.Modularforms.PeterssonLevelN
import LeanModularForms.Modularforms.SlashActionAuxil

/-!
# Newforms: level-raise / `T_p` commutation machinery

Matrix helpers for level raising and the commutation `heckeT_n_levelRaise_comm`
(Diamond–Shurman Thm 5.6.2), together with the trivial-inclusion oldform API for the
bad-prime (`p ∣ d`) case.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}

open Matrix in
/-- The shift matrix `[[1, q], [0, 1]]` as an `SL(2, ℤ)` element. -/
def shiftSL (q : ℤ) : SL(2, ℤ) :=
  ⟨!![1, q; 0, 1], by simp [Matrix.det_fin_two]⟩

/-- `shiftSL q ∈ Γ₁(M)` for any level `M`. -/
lemma shiftSL_mem_Gamma1 (M : ℕ) (q : ℤ) : shiftSL q ∈ Gamma1 M := by
  rw [Gamma1_mem]; refine ⟨?_, ?_, ?_⟩ <;> simp [shiftSL]

private lemma glMap_mapGL_eq_R (s : SL(2, ℤ)) :
    glMap (mapGL ℚ s) = (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) s := by
  apply Units.ext; ext i j
  simp only [glMap, Matrix.GeneralLinearGroup.map]
  exact (IsScalarTower.algebraMap_apply ℤ ℚ ℝ (s.1 i j)).symm

private lemma slash_mapGL_Q_Gamma1 (M : ℕ) [NeZero M] (k : ℤ) (S : SL(2, ℤ))
    (hS : S ∈ Gamma1 M) (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ⇑g ∣[k] (mapGL ℚ S : GL (Fin 2) ℚ) = ⇑g := by
  show ⇑g ∣[k] glMap (mapGL ℚ S) = ⇑g
  rw [glMap_mapGL_eq_R]
  exact g.slash_action_eq' (mapGL ℝ S) (Subgroup.mem_map.mpr ⟨S, hS, rfl⟩)

open Matrix in
private lemma T_p_upper_mod (p : ℕ) (hp : 0 < p) (a : ℕ) :
    T_p_upper p hp a = mapGL ℚ (shiftSL (↑(a / p : ℕ) : ℤ)) * T_p_upper p hp (a % p) := by
  apply Units.ext
  ext i j
  simp only [T_p_upper, shiftSL, mapGL_coe_matrix, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.mul_apply, Fin.sum_univ_two, Units.val_mul]
  fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Int.natCast_ediv]
  simp only [Int.cast_natCast]
  exact_mod_cast show (a : ℤ) = (a % p : ℤ) + (a / p : ℤ) * (p : ℤ) by
    have := Int.emod_add_mul_ediv (a : ℤ) (p : ℤ); linarith

private lemma slash_T_p_upper_mod (M : ℕ) [NeZero M] (k : ℤ) (p : ℕ) (hp : 0 < p) (a : ℕ)
    (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ⇑g ∣[k] (T_p_upper p hp a : GL (Fin 2) ℚ) =
      ⇑g ∣[k] (T_p_upper p hp (a % p) : GL (Fin 2) ℚ) := by
  rw [T_p_upper_mod p hp a, SlashAction.slash_mul]
  congr 1
  exact slash_mapGL_Q_Gamma1 M k (shiftSL (↑(a / p : ℕ))) (shiftSL_mem_Gamma1 M _) g

open Matrix in
private lemma levelRaise_mul_T_p_upper (d : ℕ) [NeZero d] (p : ℕ) (hp : 0 < p) (b : ℕ) :
    levelRaiseMatrix d * glMap (T_p_upper p hp b) =
      glMap (T_p_upper p hp (d * b)) * levelRaiseMatrix d := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    levelRaiseMatrix, glMap, Matrix.GeneralLinearGroup.map,
    Matrix.GeneralLinearGroup.mkOfDetNeZero]
  fin_cases i <;> fin_cases j <;> simp

open Matrix in
private lemma levelRaise_mul_T_p_lower (d : ℕ) [NeZero d] (p : ℕ) (hp : 0 < p) :
    levelRaiseMatrix d * glMap (T_p_lower p hp) =
      glMap (T_p_lower p hp) * levelRaiseMatrix d := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    levelRaiseMatrix, glMap, Matrix.GeneralLinearGroup.map,
    Matrix.GeneralLinearGroup.mkOfDetNeZero]
  fin_cases i <;> fin_cases j <;> (simp; try ring)

private lemma sum_reindex_mul_mod {α : Type*} [AddCommMonoid α] (d p : ℕ) (hp : Nat.Prime p)
    (hd : Nat.Coprime d p) (f : ℕ → α) :
    ∑ b ∈ Finset.range p, f (d * b % p) = ∑ b ∈ Finset.range p, f b := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h_inj : Set.InjOn (fun b ↦ d * b % p) (↑(Finset.range p)) := by
    intro b₁ hb₁ b₂ hb₂ heq
    simp only [Finset.coe_range, Set.mem_Iio] at hb₁ hb₂
    have h₂ : b₁ % p = b₂ % p := by
      have : (d : ZMod p) ≠ 0 := by
        intro h
        rw [ZMod.natCast_eq_zero_iff] at h
        exact (hp.coprime_iff_not_dvd.mp hd.symm) h
      have h₃ : ((d * b₁ : ℕ) : ZMod p) = ((d * b₂ : ℕ) : ZMod p) :=
        (ZMod.natCast_eq_natCast_iff' _ _ _).mpr heq
      simp only [Nat.cast_mul] at h₃
      exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp (mul_left_cancel₀ this h₃)
    rwa [Nat.mod_eq_of_lt hb₁, Nat.mod_eq_of_lt hb₂] at h₂
  refine Finset.sum_nbij (fun b ↦ d * b % p)
    (fun b _ ↦ Finset.mem_range.mpr (Nat.mod_lt _ hp.pos)) h_inj ?_ (fun b _ ↦ rfl)
  intro b hb
  have h_img : Finset.image (fun b ↦ d * b % p) (Finset.range p) = Finset.range p :=
    Finset.eq_of_subset_of_card_le
      (Finset.image_subset_iff.mpr fun b _ ↦ Finset.mem_range.mpr (Nat.mod_lt _ hp.pos))
      (by rw [Finset.card_image_of_injOn h_inj])
  exact Finset.mem_image.mp (by rw [h_img]; exact hb)

private lemma sum_slash_R (k : ℤ) {ι : Type*} (s : Finset ι) (φ : ι → (UpperHalfPlane → ℂ))
    (g : GL (Fin 2) ℝ) :
    (∑ b ∈ s, φ b) ∣[k] g = ∑ b ∈ s, (φ b ∣[k] g) := by
  induction s using Finset.cons_induction with
  | empty => simp [SlashAction.zero_slash]
  | cons a s has ih => simp only [Finset.sum_cons, SlashAction.add_slash, ih]

/-- Diamond/level-raise commutation equality: `⟨a⟩_N (ι_d g) = ι_d (⟨a'⟩_M g)`,
where `a' = unitsMap a` is the cast of `a` from `(ZMod N)ˣ` to `(ZMod M)ˣ`. -/
lemma diamondOp_levelRaise_eq (a : (ZMod N)ˣ) (M : ℕ) (d : ℕ) [NeZero M] [NeZero d]
    (heq : d * M = N) (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    diamondOp_cusp k a (heq ▸ levelRaise M d k g) = heq ▸ levelRaise M d k
      (diamondOpCusp k (ZMod.unitsMap (heq ▸ Nat.dvd_mul_left M d) a) g) := by
  subst heq
  obtain ⟨g₀, hg₀⟩ := Gamma0MapUnits_surjective (N := d * M) a
  set g₀'_sl : SL(2, ℤ) := levelRaiseConjOfDvd d (g₀ : SL(2, ℤ))
    (Gamma0_dmul_lower_left_dvd d M (g₀ : SL(2, ℤ)) g₀.property)
  let g₀' : ↥(Gamma0 M) :=
    ⟨g₀'_sl, levelRaiseConjOfDvd_mem_Gamma0 d M (g₀ : SL(2, ℤ)) g₀.property⟩
  have h_units : Gamma0MapUnits g₀' = ZMod.unitsMap (Nat.dvd_mul_left M d) a := by
    apply Units.ext
    rw [Gamma0MapUnits_val, ZMod.unitsMap_val, ← hg₀, Gamma0MapUnits_val]
    show ((((g₀'_sl : SL(2, ℤ)).val 1 1 : ℤ) : ZMod M)) = _
    rw [levelRaiseConjOfDvd_lower_right d (g₀ : SL(2, ℤ))
      (Gamma0_dmul_lower_left_dvd d M (g₀ : SL(2, ℤ)) g₀.property)]
    exact (ZMod.cast_intCast (Nat.dvd_mul_left M d) ((g₀ : SL(2, ℤ)).val 1 1)).symm
  apply CuspForm.ext
  intro z
  have hL : ⇑(diamondOp_cusp k a (levelRaise M d k g)) =
      ⇑(levelRaise M d k g) ∣[k] mapGL ℝ (g₀ : SL(2, ℤ)) := by
    show ⇑(diamondOpCusp k a (levelRaise M d k g)) =
      ⇑(levelRaise M d k g) ∣[k] mapGL ℝ (g₀ : SL(2, ℤ))
    rw [diamondOpCusp_eq k a g₀ hg₀]; rfl
  have hh : ⇑(diamondOpCusp k (ZMod.unitsMap (Nat.dvd_mul_left M d) a) g) =
      ⇑g ∣[k] mapGL ℝ (g₀'_sl : SL(2, ℤ)) := by
    rw [diamondOpCusp_eq k (ZMod.unitsMap (Nat.dvd_mul_left M d) a) g₀' h_units]; rfl
  rw [hL]
  have hσ_g₀ : UpperHalfPlane.σ (mapGL ℝ (g₀ : SL(2, ℤ))) =
      ContinuousAlgEquiv.refl ℝ ℂ := by
    unfold UpperHalfPlane.σ
    rw [if_pos]
    show (0 : ℝ) < (Matrix.GeneralLinearGroup.det (mapGL ℝ (g₀ : SL(2, ℤ)))).val
    rw [Matrix.SpecialLinearGroup.det_mapGL]; norm_num
  show ((((d : ℂ) ^ (1 - k)) • (⇑g ∣[k] levelRaiseMatrix d)) ∣[k]
      mapGL ℝ (g₀ : SL(2, ℤ))) z =
    (((d : ℂ) ^ (1 - k)) • (⇑(diamondOpCusp k (ZMod.unitsMap (Nat.dvd_mul_left M d) a) g)
      ∣[k] levelRaiseMatrix d)) z
  rw [ModularForm.smul_slash k _ _ ((d : ℂ) ^ (1 - k)), hσ_g₀, ContinuousAlgEquiv.refl_apply,
    show ((⇑g ∣[k] levelRaiseMatrix d) ∣[k] mapGL ℝ (g₀ : SL(2, ℤ))) =
        (⇑g ∣[k] (levelRaiseMatrix d * mapGL ℝ (g₀ : SL(2, ℤ)))) from
      (SlashAction.slash_mul k _ _ _).symm,
    show (levelRaiseMatrix d * mapGL ℝ (g₀ : SL(2, ℤ))) = mapGL ℝ g₀'_sl * levelRaiseMatrix d
      from (levelRaiseMatrix_mul_mapGL d (g₀ : SL(2, ℤ))
        (Gamma0_dmul_lower_left_dvd d M (g₀ : SL(2, ℤ)) g₀.property)).symm,
    SlashAction.slash_mul, ← hh]

private lemma heckeT_p_ut_levelRaise
    (p : ℕ) (hp : Nat.Prime p) (M d : ℕ) [NeZero M] [NeZero d]
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    heckeT_p_ut k p hp.pos (⇑((levelRaise M d k g).toModularForm')) =
      ∑ b ∈ Finset.range p, ((d : ℂ) ^ (1 - k)) •
        (⇑g.toModularForm' ∣[k] (T_p_upper p hp.pos (d * b % p) : GL (Fin 2) ℚ)) ∣[k]
          levelRaiseMatrix d := by
  simp only [heckeT_p_ut]
  simp_rw [show (⇑((levelRaise M d k g).toModularForm') : UpperHalfPlane → ℂ) =
      ((d : ℂ) ^ (1 - k)) • (⇑g ∣[k] levelRaiseMatrix d) from rfl,
    smul_slash_pos_det k _ _ _ (T_p_upper_det_pos p hp.pos _)]
  simp_rw [show ∀ b, (⇑g ∣[k] levelRaiseMatrix d) ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ) =
    ⇑g ∣[k] (levelRaiseMatrix d * glMap (T_p_upper p hp.pos b)) from
    fun b ↦ show (⇑g ∣[k] levelRaiseMatrix d) ∣[k] glMap (T_p_upper p hp.pos b) = _ from
      (SlashAction.slash_mul k _ _ _).symm]
  simp_rw [levelRaise_mul_T_p_upper d p hp.pos]
  simp_rw [show ∀ b, ⇑g ∣[k] (glMap (T_p_upper p hp.pos (d * b)) * levelRaiseMatrix d) =
    (⇑g ∣[k] (T_p_upper p hp.pos (d * b) : GL (Fin 2) ℚ)) ∣[k] levelRaiseMatrix d from
    fun b ↦ show ⇑g ∣[k] (glMap (T_p_upper p hp.pos (d * b)) * levelRaiseMatrix d) =
      (⇑g ∣[k] glMap (T_p_upper p hp.pos (d * b))) ∣[k] levelRaiseMatrix d from
      SlashAction.slash_mul k _ _ _]
  simp_rw [show ∀ b, ⇑g ∣[k] (T_p_upper p hp.pos (d * b) : GL (Fin 2) ℚ) =
    ⇑g.toModularForm' ∣[k] (T_p_upper p hp.pos (d * b % p) : GL (Fin 2) ℚ) from
    fun b ↦ slash_T_p_upper_mod M k p hp.pos (d * b) g.toModularForm']

private lemma heckeT_p_ut_levelRaise_reindex
    (p : ℕ) (hp : Nat.Prime p) (M d : ℕ) [NeZero M] [NeZero d]
    (hdp : Nat.Coprime d p) (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (∑ b ∈ Finset.range p, ((d : ℂ) ^ (1 - k)) •
        (⇑g.toModularForm' ∣[k] (T_p_upper p hp.pos (d * b % p) : GL (Fin 2) ℚ)) ∣[k]
          levelRaiseMatrix d) =
      ((d : ℂ) ^ (1 - k)) •
        (heckeT_p_ut k p hp.pos (⇑g.toModularForm') ∣[k] levelRaiseMatrix d) := by
  rw [sum_reindex_mul_mod d p hp hdp
    (fun b ↦ ((d : ℂ) ^ (1 - k)) • (⇑g.toModularForm' ∣[k]
      (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k] levelRaiseMatrix d),
    heckeT_p_ut, sum_slash_R, ← Finset.smul_sum]

private lemma diamondOp_T_p_lower_levelRaise
    (p : ℕ) (hp : Nat.Prime p) (M d : ℕ) [NeZero M] [NeZero d]
    (hpdM : Nat.Coprime p (d * M)) (hpM : Nat.Coprime p M)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (⇑(diamondOp k (ZMod.unitOfCoprime p hpdM) ((levelRaise M d k g).toModularForm')) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ)) =
      ((d : ℂ) ^ (1 - k)) •
        (⇑(diamondOp k (ZMod.unitOfCoprime p hpM) g.toModularForm') ∣[k]
          (T_p_lower p hp.pos : GL (Fin 2) ℚ)) ∣[k] levelRaiseMatrix d := by
  have hdia_fun : (⇑((diamondOp k (ZMod.unitOfCoprime p hpdM))
      ((levelRaise M d k g).toModularForm') : ModularForm _ k) : UpperHalfPlane → ℂ) =
    ((d : ℂ) ^ (1 - k)) • (⇑(diamondOpCusp k
      (ZMod.unitsMap (Nat.dvd_mul_left M d) (ZMod.unitOfCoprime p hpdM)) g) ∣[k]
      levelRaiseMatrix d) :=
    congr_arg (fun f : CuspForm _ k ↦ (⇑f : UpperHalfPlane → ℂ))
      (diamondOp_levelRaise_eq (ZMod.unitOfCoprime p hpdM) M d rfl g)
  rw [hdia_fun, smul_slash_pos_det k _ _ _ (T_p_lower_det_pos p hp.pos)]
  have h_units_eq : ZMod.unitsMap (Nat.dvd_mul_left M d) (ZMod.unitOfCoprime p hpdM) =
      ZMod.unitOfCoprime p hpM := by
    ext; simp [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime]
  rw [h_units_eq]
  have h_coe : (⇑(diamondOpCusp k (ZMod.unitOfCoprime p hpM) g) : UpperHalfPlane → ℂ) =
    ⇑((diamondOp k (ZMod.unitOfCoprime p hpM)) g.toModularForm') := rfl
  rw [h_coe,
    show (⇑((diamondOp k (ZMod.unitOfCoprime p hpM)) g.toModularForm') ∣[k]
        levelRaiseMatrix d) ∣[k] (T_p_lower p hp.pos : GL (Fin 2) ℚ) =
      ⇑((diamondOp k (ZMod.unitOfCoprime p hpM)) g.toModularForm') ∣[k]
        (levelRaiseMatrix d * glMap (T_p_lower p hp.pos)) from
      show (⇑((diamondOp k (ZMod.unitOfCoprime p hpM)) g.toModularForm') ∣[k]
          levelRaiseMatrix d) ∣[k] glMap (T_p_lower p hp.pos) = _ from
        (SlashAction.slash_mul k _ _ _).symm]
  rw [levelRaise_mul_T_p_lower d p hp.pos, SlashAction.slash_mul k _ _ _]
  rfl

private lemma heckeT_p_all_levelRaise_comm
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (M : ℕ) (d : ℕ) [NeZero M] [NeZero d] (heq : d * M = N)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    heckeT_n_cusp k p (heq ▸ levelRaise M d k g) =
      heq ▸ levelRaise M d k (heckeT_n_cusp k p g) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  subst heq
  have hpM : Nat.Coprime p M := hpN.coprime_dvd_right ⟨d, mul_comm d M⟩
  apply CuspForm.ext
  intro z
  show (heckeT_n (N := d * M) k p (levelRaise M d k g).toModularForm').toFun z =
    (((d : ℂ) ^ (1 - k)) • ((heckeT_n_cusp (N := M) k p g : CuspForm _ k).toFun
      ∣[k] levelRaiseMatrix d)) z
  rw [heckeT_n_prime k hp]
  change ((heckeT_p_all k p hp) ((levelRaise M d k) g).toModularForm').toFun z =
    (((d : ℂ) ^ (1 - k)) • ((heckeT_n (N := M) k p g.toModularForm').toFun
      ∣[k] levelRaiseMatrix d)) z
  rw [heckeT_n_prime k hp, heckeT_p_all_coprime k hp hpN, heckeT_p_all_coprime k hp hpM]
  show heckeT_p_fun k p hp hpN ((levelRaise M d k g).toModularForm') z = _
  rw [show heckeT_p_fun k p hp hpN ((levelRaise M d k g).toModularForm') =
      heckeT_p_ut k p hp.pos (⇑((levelRaise M d k g).toModularForm')) +
      ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) ((levelRaise M d k g).toModularForm')) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ) from rfl,
    heckeT_p_ut_levelRaise p hp M d g]
  simp only [Pi.add_apply]
  suffices h :
    (∑ x ∈ Finset.range p, ((d : ℂ) ^ (1 - k)) •
      (⇑g.toModularForm' ∣[k] (T_p_upper p hp.pos (d * x % p) : GL (Fin 2) ℚ)) ∣[k]
        levelRaiseMatrix d) +
    (⇑((diamondOp k (ZMod.unitOfCoprime p hpN)) ((levelRaise M d k) g).toModularForm') ∣[k]
      (T_p_lower p hp.pos : GL (Fin 2) ℚ)) =
    ((d : ℂ) ^ (1 - k)) • (((heckeT_p k p hp hpM) g.toModularForm').toFun ∣[k]
      levelRaiseMatrix d) from congr_fun h z
  rw [heckeT_p_ut_levelRaise_reindex p hp M d (hpN.symm.coprime_dvd_left (dvd_mul_right d M)) g]
  show ((d : ℂ) ^ (1 - k)) • (heckeT_p_ut k p hp.pos ⇑g.toModularForm' ∣[k] levelRaiseMatrix d) +
      ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) ((levelRaise M d k g).toModularForm')) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ) =
    ((d : ℂ) ^ (1 - k)) • (heckeT_p_fun k p hp hpM g.toModularForm' ∣[k] levelRaiseMatrix d)
  rw [show heckeT_p_fun k p hp hpM g.toModularForm' = heckeT_p_ut k p hp.pos ⇑g.toModularForm' +
      ⇑(diamondOp k (ZMod.unitOfCoprime p hpM) g.toModularForm') ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ) from rfl,
    SlashAction.add_slash, smul_add]
  congr 1
  exact diamondOp_T_p_lower_levelRaise p hp M d hpN hpM g

/-- `Γ₁(N) ≤ Γ₁(M)` for `M ∣ N`: a matrix congruent to the identity modulo `N`
is also congruent modulo `M`. -/
lemma Gamma1_le_Gamma1_of_dvd {M N : ℕ} (hMN : M ∣ N) :
    CongruenceSubgroup.Gamma1 N ≤ CongruenceSubgroup.Gamma1 M := by
  intro A hA
  rw [Gamma1_mem] at hA ⊢
  obtain ⟨h00, h11, h10⟩ := hA
  have h_cast : ∀ k : ℤ, ((k : ℤ) : ZMod M) = (ZMod.castHom hMN (ZMod M)) ((k : ℤ) : ZMod N) :=
    fun k ↦ by rw [ZMod.castHom_apply]; exact (ZMod.cast_intCast hMN _).symm
  exact ⟨by rw [h_cast, h00, map_one], by rw [h_cast, h11, map_one],
    by rw [h_cast, h10, map_zero]⟩

/-- GL-image version of `Gamma1_le_Gamma1_of_dvd`:
`(Γ₁(N)).map (mapGL ℝ) ≤ (Γ₁(M)).map (mapGL ℝ)` for `M ∣ N`. -/
lemma Gamma1_map_le_Gamma1_map_of_dvd {M N : ℕ} (hMN : M ∣ N) :
    (CongruenceSubgroup.Gamma1 N).map (mapGL ℝ) ≤
      (CongruenceSubgroup.Gamma1 M).map (mapGL ℝ) :=
  Subgroup.map_mono (Gamma1_le_Gamma1_of_dvd hMN)

/-- Trivial-inclusion CuspForm map: for `M ∣ N`, a `Γ₁(M)`-cusp form is
automatically `Γ₁(N)`-invariant, so this lifts it to a `Γ₁(N)`-cusp form
with the same underlying function. -/
def levelInclude_cusp {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N) (k : ℤ) :
    CuspForm ((Gamma1 M).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun := CuspForm.restrictSubgroup (Gamma1_map_le_Gamma1_map_of_dvd hMN)
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- **Coercion-level identity for `levelInclude_cusp`.** -/
@[simp]
lemma levelInclude_cusp_coe {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N) (k : ℤ)
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (⇑(levelInclude_cusp hMN k f) : UpperHalfPlane → ℂ) = ⇑f := rfl

/-- A cusp form `f : CuspForm Γ₁(N) k` is a *trivial-inclusion oldform generator*
if there is a strictly smaller divisor `M ∣ N, M < N` and a cusp form
`g : CuspForm Γ₁(M) k` with `f = levelInclude_cusp g`. -/
def IsLevelInclusionOldformGenerator (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    Prop :=
  ∃ (M : ℕ) (_ : NeZero M) (hMN : M ∣ N) (_ : M < N)
      (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k),
    levelInclude_cusp hMN k g = f

/-- The classical oldform subspace `S_k^old(N)`: `cuspFormsOld N k` extended with
the trivial-inclusion oldform generators, spanning both the level-raise summands
`LR_{N/M}(S_k(Γ₁(M)))` and the inclusions `S_k(Γ₁(M)) ↪ S_k(Γ₁(N))` for `M ∣ N`,
`M < N`. -/
def cuspFormsOldExtended (N : ℕ) [NeZero N] (k : ℤ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  Submodule.span ℂ {f | IsOldformGenerator f ∨ IsLevelInclusionOldformGenerator f}

/-- **`cuspFormsOld ≤ cuspFormsOldExtended`.** -/
lemma cuspFormsOld_le_cuspFormsOldExtended :
    cuspFormsOld N k ≤ cuspFormsOldExtended N k :=
  Submodule.span_mono fun _ hf ↦ Or.inl hf

/-- **`levelInclude_cusp g ∈ cuspFormsOldExtended`** (membership of a trivial
inclusion generator). -/
lemma levelInclude_cusp_mem_cuspFormsOldExtended
    {M : ℕ} [NeZero M] (hMN : M ∣ N) (hMltN : M < N)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    levelInclude_cusp hMN k g ∈ cuspFormsOldExtended N k :=
  Submodule.subset_span (Or.inr ⟨M, inferInstance, hMN, hMltN, g, rfl⟩)

/-- The **extended new subspace**: cusp forms `petN`-orthogonal to every form in
the extended oldspace `cuspFormsOldExtended N k`. It is a submodule of the
classical newspace (`cuspFormsNewExtended ⊆ cuspFormsNew`), and is the correct
object at bad primes, where classical `cuspFormsNew` is not preserved by `T_p`
(e.g. at `N = p²`). -/
def cuspFormsNewExtended (N : ℕ) [NeZero N] (k : ℤ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) where
  carrier := {f | ∀ g, g ∈ cuspFormsOldExtended N k → petN f g = 0}
  zero_mem' g _ := petN_zero_left g
  add_mem' h₁ h₂ g hg := by
    simp [petN_add_left, h₁ g hg, h₂ g hg]
  smul_mem' c f hf g hg := by
    simp [petN_conj_smul_left, hf g hg]

/-- `cuspFormsNewExtended ⊆ cuspFormsNew`. -/
lemma cuspFormsNewExtended_le_cuspFormsNew {N : ℕ} [NeZero N] {k : ℤ} :
    cuspFormsNewExtended N k ≤ cuspFormsNew N k :=
  fun _ hf g hg ↦ hf g (cuspFormsOld_le_cuspFormsOldExtended hg)

private lemma heckeT_n_cusp_decomp_of_mul {L : ℕ} [NeZero L] (k : ℤ) (a b m : ℕ) [NeZero a]
    [NeZero b] [NeZero m] (h_mul : heckeT_n (N := L) k m = heckeT_n k a * heckeT_n k b)
    (f : CuspForm ((Gamma1 L).map (mapGL ℝ)) k) :
    heckeT_n_cusp k m f = heckeT_n_cusp k a (heckeT_n_cusp k b f) := by
  apply CuspForm.ext
  intro z
  show ((heckeT_n (N := L) k m) f.toModularForm').toFun z =
    ((heckeT_n k a) ((heckeT_n k b) f.toModularForm')).toFun z
  simp only [ModularForm.toFun_eq_coe]
  rw [h_mul]
  rfl

private lemma heckeT_n_cusp_one {L : ℕ} [NeZero L] (k : ℤ)
    (f : CuspForm ((Gamma1 L).map (mapGL ℝ)) k) : heckeT_n_cusp k 1 f = f := by
  apply CuspForm.ext
  intro w
  show (heckeT_n k 1 f.toModularForm').toFun w = f w
  rw [heckeT_n_one]; rfl

private lemma heckeT_n_cusp_ppow_succ_succ
    {L : ℕ} [NeZero L] (k : ℤ) {p : ℕ} (hp : Nat.Prime p) (hpL : Nat.Coprime p L)
    (r : ℕ) (f : CuspForm ((Gamma1 L).map (mapGL ℝ)) k) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : NeZero (p ^ (r + 2)) := ⟨(pow_pos hp.pos _).ne'⟩
    haveI : NeZero (p ^ (r + 1)) := ⟨(pow_pos hp.pos _).ne'⟩
    haveI : NeZero (p ^ r) := ⟨(pow_pos hp.pos _).ne'⟩
    heckeT_n_cusp k (p ^ (r + 2)) f =
      heckeT_n_cusp k p (heckeT_n_cusp k (p ^ (r + 1)) f) -
        ((↑p : ℂ) ^ (k - 1)) • diamondOp_cusp k (ZMod.unitOfCoprime p hpL)
          (heckeT_n_cusp k (p ^ r) f) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ (r + 2)) := ⟨(pow_pos hp.pos _).ne'⟩
  haveI : NeZero (p ^ (r + 1)) := ⟨(pow_pos hp.pos _).ne'⟩
  haveI : NeZero (p ^ r) := ⟨(pow_pos hp.pos _).ne'⟩
  apply CuspForm.ext
  intro z
  show ((heckeT_n (N := L) k (p ^ (r + 2))) f.toModularForm').toFun z = _
  rw [heckeT_n_prime_pow k hp (r + 2) (by omega), heckeT_ppow_succ_succ k p hp r]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply,
    ModularForm.toFun_eq_coe, ModularForm.coe_sub, Pi.sub_apply]
  congr 1
  · show (heckeT_p_all (N := L) k p hp
      (heckeT_ppow k p hp (r + 1) f.toModularForm')).toFun z =
      ((heckeT_n k p) ((heckeT_n k (p ^ (r + 1))) f.toModularForm')).toFun z
    rw [← heckeT_n_prime k hp, ← heckeT_n_prime_pow k hp (r + 1) (by omega)]
  · have key : (diamondOp_n k p) ((heckeT_ppow k p hp r) f.toModularForm') =
        (diamondOp k (ZMod.unitOfCoprime p hpL))
          ((heckeT_n (N := L) k (p ^ r)) f.toModularForm') := by
      rw [diamondOp_n_coprime k hpL]
      cases r with
      | zero => simp [heckeT_ppow_zero, heckeT_n_one]
      | succ r => rw [← heckeT_n_prime_pow k hp (r + 1) (by omega)]
    rw [show diamondOp_n k p * heckeT_ppow k p hp r =
      (diamondOp_n k p).comp (heckeT_ppow k p hp r) from rfl] at *
    simp only [LinearMap.comp_apply] at *
    rw [key]; rfl

private lemma heckeT_ppow_levelRaise_comm_step
    (M d : ℕ) [NeZero M] [NeZero d] {p : ℕ} (hp : Nat.Prime p)
    (hpM : Nat.Coprime p M) (hpdM : Nat.Coprime p (d * M)) (r : ℕ)
    (g' : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (ih_p : haveI : NeZero p := ⟨hp.ne_zero⟩
      ∀ f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      heckeT_n_cusp k p (levelRaise M d k f) = levelRaise M d k (heckeT_n_cusp k p f))
    (ih_pv1 : haveI : NeZero (p ^ (r + 1)) := ⟨(pow_pos hp.pos _).ne'⟩
      ∀ f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      heckeT_n_cusp k (p ^ (r + 1)) (levelRaise M d k f) =
        levelRaise M d k (heckeT_n_cusp k (p ^ (r + 1)) f))
    (ih_pr : haveI : NeZero (p ^ r) := ⟨(pow_pos hp.pos _).ne'⟩
      ∀ f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      heckeT_n_cusp k (p ^ r) (levelRaise M d k f) =
        levelRaise M d k (heckeT_n_cusp k (p ^ r) f)) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : NeZero (p ^ (r + 2)) := ⟨(pow_pos hp.pos _).ne'⟩
    heckeT_n_cusp (N := d * M) k (p ^ (r + 2)) (levelRaise M d k g') =
      levelRaise M d k (heckeT_n_cusp (N := M) k (p ^ (r + 2)) g') := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ (r + 1)) := ⟨(pow_pos hp.pos _).ne'⟩
  haveI : NeZero (p ^ r) := ⟨(pow_pos hp.pos _).ne'⟩
  have h_units_eq : ZMod.unitsMap (Nat.dvd_mul_left M d)
      (ZMod.unitOfCoprime p hpdM) = ZMod.unitOfCoprime p hpM := by
    ext; simp [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime]
  have ih_dia : ∀ f, diamondOp_cusp k (ZMod.unitOfCoprime p hpdM) (levelRaise M d k f) =
      levelRaise M d k (diamondOp_cusp k (ZMod.unitOfCoprime p hpM) f) := by
    intro f
    rw [diamondOp_levelRaise_eq (ZMod.unitOfCoprime p hpdM) M d rfl f, h_units_eq]; rfl
  calc heckeT_n_cusp k (p ^ (r + 2)) (levelRaise M d k g')
      = heckeT_n_cusp k p (heckeT_n_cusp k (p ^ (r + 1)) (levelRaise M d k g')) -
          ((↑p : ℂ) ^ (k - 1)) • diamondOp_cusp k (ZMod.unitOfCoprime p hpdM)
            (heckeT_n_cusp k (p ^ r) (levelRaise M d k g')) :=
        heckeT_n_cusp_ppow_succ_succ k hp hpdM r (levelRaise M d k g')
    _ = heckeT_n_cusp k p (levelRaise M d k (heckeT_n_cusp k (p ^ (r + 1)) g')) -
          ((↑p : ℂ) ^ (k - 1)) • diamondOp_cusp k (ZMod.unitOfCoprime p hpdM)
            (levelRaise M d k (heckeT_n_cusp k (p ^ r) g')) := by
        rw [ih_pv1 g', ih_pr g']
    _ = levelRaise M d k (heckeT_n_cusp k p (heckeT_n_cusp k (p ^ (r + 1)) g')) -
          ((↑p : ℂ) ^ (k - 1)) • levelRaise M d k (diamondOp_cusp k
            (ZMod.unitOfCoprime p hpM) (heckeT_n_cusp k (p ^ r) g')) := by
        rw [ih_p (heckeT_n_cusp k (p ^ (r + 1)) g'), ih_dia (heckeT_n_cusp k (p ^ r) g')]
    _ = levelRaise M d k (heckeT_n_cusp k p (heckeT_n_cusp k (p ^ (r + 1)) g') -
          ((↑p : ℂ) ^ (k - 1)) • diamondOp_cusp k (ZMod.unitOfCoprime p hpM)
            (heckeT_n_cusp k (p ^ r) g')) := by
        rw [← (levelRaise M d k).map_smul, ← (levelRaise M d k).map_sub]
    _ = levelRaise M d k (heckeT_n_cusp k (p ^ (r + 2)) g') := by
        rw [heckeT_n_cusp_ppow_succ_succ k hp hpM r g']

private lemma heckeT_n_levelRaise_comm_ppow_case
    (M d : ℕ) [NeZero M] [NeZero d] {p : ℕ} (hp : Nat.Prime p) (r : ℕ)
    (hpcop : Nat.Coprime p (d * M))
    (ih : haveI : NeZero p := ⟨hp.ne_zero⟩
        ∀ m' < p ^ (r + 2), ∀ (_ : 0 < m'), Nat.Coprime m' (d * M) →
        ∀ f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
          haveI : NeZero m' := ⟨‹0 < m'›.ne'⟩
          heckeT_n_cusp k m' (levelRaise M d k f) =
            levelRaise M d k (heckeT_n_cusp k m' f))
    (g' : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : NeZero (p ^ (r + 2)) := ⟨(pow_pos hp.pos _).ne'⟩
    heckeT_n_cusp k (p ^ (r + 2)) (levelRaise M d k g') =
      levelRaise M d k (heckeT_n_cusp k (p ^ (r + 2)) g') := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp_lt : p < p ^ (r + 2) := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ (r + 2) := Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hpv1_lt : p ^ (r + 1) < p ^ (r + 2) := Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hpr_lt : p ^ r < p ^ (r + 2) := Nat.pow_lt_pow_right hp.one_lt (by omega)
  exact heckeT_ppow_levelRaise_comm_step M d hp
    (hpcop.coprime_dvd_right (dvd_mul_left M d)) hpcop r g'
    (fun f ↦ ih p hp_lt hp.pos hpcop f)
    (fun f ↦ ih (p ^ (r + 1)) hpv1_lt (pow_pos hp.pos _) (hpcop.pow_left _) f)
    (fun f ↦ ih (p ^ r) hpr_lt (pow_pos hp.pos _) (hpcop.pow_left _) f)

private lemma heckeT_n_levelRaise_comm_step
    (M d : ℕ) [NeZero M] [NeZero d] (m : ℕ) (hle : 1 < m)
    (hcop : Nat.Coprime m (d * M))
    (ih : ∀ m' < m, ∀ (_ : 0 < m'), Nat.Coprime m' (d * M) →
        ∀ f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
          haveI : NeZero m' := ⟨‹0 < m'›.ne'⟩
          heckeT_n_cusp k m' (levelRaise M d k f) =
            levelRaise M d k (heckeT_n_cusp k m' f))
    (g' : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    haveI : NeZero m := ⟨(by omega : 0 < m).ne'⟩
    heckeT_n_cusp k m (levelRaise M d k g') =
      levelRaise M d k (heckeT_n_cusp k m g') := by
  haveI : NeZero m := ⟨(by omega : 0 < m).ne'⟩
  set p := m.minFac
  have hpp : p.Prime := Nat.minFac_prime (by omega : m ≠ 1)
  set v := m.factorization p
  have hv_pos : 0 < v := hpp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd m)
  have hdiv_pos : 0 < m / p ^ v :=
    Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p)) (pow_pos hpp.pos v)
  have hpcop : Nat.Coprime p (d * M) := Nat.Coprime.coprime_dvd_left (Nat.minFac_dvd m) hcop
  have hpv_pos : 0 < p ^ v := pow_pos hpp.pos v
  haveI : NeZero (p ^ v) := ⟨hpv_pos.ne'⟩
  haveI : NeZero (m / p ^ v) := ⟨hdiv_pos.ne'⟩
  by_cases hpv_lt : p ^ v < m
  · have hDecomp : ∀ {L : ℕ} [NeZero L] (f : CuspForm ((Gamma1 L).map (mapGL ℝ)) k),
        heckeT_n_cusp k m f = heckeT_n_cusp k (p ^ v) (heckeT_n_cusp k (m / p ^ v) f) :=
      fun {L} _ f ↦ heckeT_n_cusp_decomp_of_mul k (p ^ v) (m / p ^ v) m
        (heckeT_n_mul_ppow_quot (N := L) (k := k) m hle p hpp rfl v rfl hv_pos hdiv_pos) f
    rw [hDecomp, ih (m / p ^ v) (heckeT_n_unfold_lt m hle) hdiv_pos
        (Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd (Nat.ordProj_dvd m p)) hcop) g',
      ih (p ^ v) hpv_lt hpv_pos (Nat.Coprime.pow_left v hpcop)
        (heckeT_n_cusp k (m / p ^ v) g')]
    congr 1; exact (hDecomp g').symm
  · have hpv_eq : p ^ v = m := le_antisymm
      (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p)) (not_lt.mp hpv_lt)
    by_cases hv1 : v = 1
    · have hpp_m : Nat.Prime m := by rw [← hpv_eq, hv1, pow_one]; exact hpp
      exact heckeT_p_all_levelRaise_comm m hpp_m hcop M d rfl g'
    · obtain ⟨r, hr⟩ : ∃ r, v = r + 2 := ⟨v - 2, by omega⟩
      haveI : NeZero p := ⟨hpp.ne_zero⟩
      haveI : NeZero (p ^ (r + 2)) := ⟨(pow_pos hpp.pos _).ne'⟩
      have hm_eq : m = p ^ (r + 2) := by rw [← hpv_eq, hr]
      calc heckeT_n_cusp k m (levelRaise M d k g')
          = heckeT_n_cusp k (p ^ (r + 2)) (levelRaise M d k g') := by simp only [hm_eq]
        _ = levelRaise M d k (heckeT_n_cusp k (p ^ (r + 2)) g') :=
            heckeT_n_levelRaise_comm_ppow_case M d hpp r hpcop (hm_eq ▸ ih) g'
        _ = levelRaise M d k (heckeT_n_cusp k m g') := by simp only [hm_eq]

/-- The commutation `T_n (LR g) = LR (T_n g)` for `n` coprime to the level. -/
lemma heckeT_n_levelRaise_comm
    (n : ℕ) [NeZero n] (hn : Nat.Coprime n N)
    (M : ℕ) (d : ℕ) [NeZero M] [NeZero d] (heq : d * M = N)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    heckeT_n_cusp k n (heq ▸ levelRaise M d k g) =
      heq ▸ levelRaise M d k (heckeT_n_cusp k n g) := by
  subst heq
  suffices h : ∀ m : ℕ, (hm : 0 < m) → Nat.Coprime m (d * M) →
      ∀ g' : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
        haveI : NeZero m := ⟨hm.ne'⟩
        heckeT_n_cusp k m (levelRaise M d k g') =
          levelRaise M d k (heckeT_n_cusp k m g') from
    h n (NeZero.pos n) hn g
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hcop g'
    haveI : NeZero m := ⟨hm.ne'⟩
    by_cases hle : 1 < m
    · exact heckeT_n_levelRaise_comm_step M d m hle hcop ih g'
    · obtain rfl : m = 1 := by omega
      rw [heckeT_n_cusp_one, heckeT_n_cusp_one]

private lemma heckeT_n_levelRaise_mem (n : ℕ) [NeZero n] (hn : Nat.Coprime n N)
    (M : ℕ) (d : ℕ) [NeZero M] [NeZero d] (hd : 1 < d) (heq : d * M = N)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    heckeT_n_cusp k n (heq ▸ levelRaise M d k g) ∈ cuspFormsOld N k := by
  rw [heckeT_n_levelRaise_comm n hn M d heq g]
  exact Submodule.subset_span ⟨M, d, _, _, hd, heq, _, rfl⟩

private lemma diamondOp_levelRaise_mem (a : (ZMod N)ˣ)
    (M : ℕ) (d : ℕ) [NeZero M] [NeZero d] (hd : 1 < d) (heq : d * M = N)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    diamondOp_cusp k a (heq ▸ levelRaise M d k g) ∈ cuspFormsOld N k := by
  subst heq
  rw [diamondOp_levelRaise_eq a M d rfl g]
  exact Submodule.subset_span ⟨M, d, _, _, hd, rfl, _, rfl⟩

/-- The oldform subspace is stable under all Hecke operators `T_n` for `(n, N) = 1`. -/
theorem heckeT_n_preserves_cuspFormsOld (n : ℕ) [NeZero n] (hn : Nat.Coprime n N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ cuspFormsOld N k) :
    heckeT_n_cusp k n f ∈ cuspFormsOld N k := by
  refine Submodule.span_induction
    (p := fun x _ ↦ heckeT_n_cusp k n x ∈ cuspFormsOld N k)
    ?_ ?_ ?_ ?_ hf
  · rintro f₀ ⟨M, d, _, _, hd, heq, g, rfl⟩
    exact heckeT_n_levelRaise_mem n hn M d hd heq g
  · show heckeT_n_cusp k n (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsOld N k
    rw [heckeT_n_cusp_zero]
    exact (cuspFormsOld N k).zero_mem
  · intros f₁ f₂ _ _ ih₁ ih₂
    show heckeT_n_cusp k n (f₁ + f₂) ∈ cuspFormsOld N k
    rw [heckeT_n_cusp_add]
    exact (cuspFormsOld N k).add_mem ih₁ ih₂
  · intros c f₁ _ ih
    show heckeT_n_cusp k n (c • f₁) ∈ cuspFormsOld N k
    rw [heckeT_n_cusp_smul]
    exact (cuspFormsOld N k).smul_mem c ih

/-- Diamond operators preserve the oldform subspace. -/
theorem diamondOp_preserves_cuspFormsOld (d : (ZMod N)ˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ cuspFormsOld N k) :
    diamondOp_cusp k d f ∈ cuspFormsOld N k := by
  refine Submodule.span_induction
    (p := fun x _ ↦ diamondOp_cusp k d x ∈ cuspFormsOld N k)
    ?_ ?_ ?_ ?_ hf
  · rintro f₀ ⟨M, d', _, _, hd', heq, g, rfl⟩
    exact diamondOp_levelRaise_mem d M d' hd' heq g
  · show diamondOp_cusp k d (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsOld N k
    rw [diamondOp_cusp_zero]
    exact (cuspFormsOld N k).zero_mem
  · intros f₁ f₂ _ _ ih₁ ih₂
    show diamondOp_cusp k d (f₁ + f₂) ∈ cuspFormsOld N k
    rw [diamondOp_cusp_add]
    exact (cuspFormsOld N k).add_mem ih₁ ih₂
  · intros c f₁ _ ih
    show diamondOp_cusp k d (c • f₁) ∈ cuspFormsOld N k
    rw [diamondOp_cusp_smul]
    exact (cuspFormsOld N k).smul_mem c ih

/-- The newform subspace is stable under all Hecke operators `T_n` for `(n, N) = 1`. -/
theorem heckeT_n_preserves_cuspFormsNew (n : ℕ) [NeZero n] (hn : Nat.Coprime n N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ cuspFormsNew N k) :
    heckeT_n_cusp k n f ∈ cuspFormsNew N k := by
  intro g hg
  rw [heckeT_n_adjoint n hn f g]
  exact hf _ (diamondOp_preserves_cuspFormsOld _ _
    (heckeT_n_preserves_cuspFormsOld n hn g hg))

/-- Diamond operators preserve the newform subspace. -/
theorem diamondOp_preserves_cuspFormsNew (d : (ZMod N)ˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ cuspFormsNew N k) :
    diamondOp_cusp k d f ∈ cuspFormsNew N k := by
  intro g hg
  have hgg : diamondOp_cusp k d (diamondOp_cusp k d⁻¹ g) = g := by
    show diamondOpCusp k d (diamondOpCusp k d⁻¹ g) = g
    rw [show (diamondOpCusp k d (diamondOpCusp k d⁻¹ g)) =
        ((diamondOpCusp k d).comp (diamondOpCusp k d⁻¹)) g from rfl,
      ← diamondOpCusp_mul, mul_inv_cancel, diamondOpCusp_one]
    rfl
  rw [← hgg, diamondOp_petersson_unitary]
  exact hf _ (diamondOp_preserves_cuspFormsOld _ _ hg)

/-- The intersection of `cuspFormsOldExtended` and `cuspFormsNewExtended` is
trivial. Mirrors `cuspFormsOld_disjoint_cuspFormsNew`. -/
theorem cuspFormsOldExtended_disjoint_cuspFormsNewExtended
    {N : ℕ} [NeZero N] {k : ℤ} :
    Disjoint (cuspFormsOldExtended N k) (cuspFormsNewExtended N k) := by
  rw [Submodule.disjoint_def]
  intro f hf_old hf_new
  exact petN_definite f (hf_new f hf_old)

end HeckeRing.GL2

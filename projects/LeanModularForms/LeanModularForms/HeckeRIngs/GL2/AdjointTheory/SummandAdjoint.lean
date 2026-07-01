/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.AdjointTheory.FDTransport

/-!
# Hecke adjoint theory: summand-level adjoint identity.

This module covers the SL₂(ℤ) continuity instance, the `T_p` adjoint via diamond
unitarity, the GL₂⁺ coset adjoint lifted to `petN`, and the summand-level adjoint /
finite-union bridge.
-/

noncomputable section

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped Pointwise MatrixGroups ModularForm

variable {k : ℤ}

namespace HeckeRing.GL2

open CuspForm

variable {N : ℕ} [NeZero N]

instance : ContinuousConstSMul SL(2, ℤ) UpperHalfPlane where
  continuous_const_smul c := by
    show Continuous fun τ ↦ (map (Int.castRingHom ℝ) c) • τ
    exact continuous_const_smul _

theorem glMap_T_p_upper_det_pos (p : ℕ) (hp : 0 < p) (b : ℕ) :
    0 < (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ).det.val := by
  show 0 < ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ).det
  rw [show ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((T_p_upper p hp b : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl,
    show (((T_p_upper p hp b : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ)).det =
        (algebraMap ℚ ℝ) (((T_p_upper p hp b : GL (Fin 2) ℚ).val).det) from
        (RingHom.map_det _ _).symm,
    show ((T_p_upper p hp b : GL (Fin 2) ℚ).val).det = (p : ℚ) by
      simp [T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.det_fin_two, Matrix.of_apply]]
  change 0 < ((p : ℚ) : ℝ)
  exact_mod_cast hp

private lemma det_val_inv_pos {α : GL (Fin 2) ℝ} (hα : 0 < α.det.val) :
    0 < (α⁻¹ : GL (Fin 2) ℝ).det.val := by
  rw [map_inv, Units.val_inv_eq_inv_val]
  exact inv_pos.mpr hα

/-- Diamond operators are unitary for the **level-N Petersson inner product** `petN`:
`⟨⟨d⟩f, ⟨d⟩g⟩_N = ⟨f, g⟩_N`. -/
theorem diamondOp_petersson_unitary
    (d : (ZMod N)ˣ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (diamondOp_cusp k d f) (diamondOp_cusp k d g) = petN f g := by
  set γ_sub := (Gamma0MapUnits_surjective d).choose
  exact petN_slash_invariant f g (γ_sub : SL(2, ℤ)) γ_sub.property
    (slash_Gamma1_eq f) (slash_Gamma1_eq g)
    (diamondOp_cusp k d f) (diamondOp_cusp k d g) rfl rfl

private lemma peterssonAdj_glMap_T_p_upper (p : ℕ) (hp : 0 < p) (b : ℕ) :
    (peterssonAdj (glMap (T_p_upper p hp b)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ), -(b : ℝ); 0, 1] := by
  rw [peterssonAdj_coe]
  have hcoe : (glMap (T_p_upper p hp b) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), (b : ℝ); 0, (p : ℝ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [glMap, T_p_upper]
  rw [hcoe, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.of_apply]

/-- `glMap (mapGL ℚ γ) = mapGL ℝ γ` for `γ : SL(2, ℤ)`: the composite
`SL(2, ℤ) → GL(2, ℚ) → GL(2, ℝ)` equals the direct map `mapGL ℝ`. -/
theorem glMap_mapGL_Q_eq_mapGL_R (γ : SL(2, ℤ)) :
    (glMap ((mapGL ℚ : SL(2, ℤ) →* GL (Fin 2) ℚ) γ) : GL (Fin 2) ℝ) =
      (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ := by
  apply Units.ext
  ext i j
  show ((glMap ((mapGL ℚ : SL(2, ℤ) →* GL (Fin 2) ℚ) γ) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) i j =
    (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ) : Matrix (Fin 2) (Fin 2) ℝ) i j
  simp [glMap, Matrix.GeneralLinearGroup.map, mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map, algebraMap_int_eq, Matrix.map_apply]

def shiftSL_loc (m : ℤ) : SL(2, ℤ) :=
  ⟨!![1, m; 0, 1], by simp [Matrix.det_fin_two]⟩

private lemma shiftSL_loc_mem_Gamma1 (m : ℤ) : shiftSL_loc m ∈ Gamma1 N := by
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> simp [shiftSL_loc]

private lemma shiftSL_loc_psl_ne_one {m : ℤ} (hm : m ≠ 0) :
    (QuotientGroup.mk (shiftSL_loc m) : PSL(2, ℤ)) ≠ 1 := by
  intro heq
  rw [QuotientGroup.eq_one_iff] at heq
  have hS : (!![(0 : ℤ), -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    simp [Matrix.det_fin_two]
  set S_mat : SL(2, ℤ) := ⟨!![0, -1; 1, 0], hS⟩
  have hcomm_val : (shiftSL_loc m : SL(2, ℤ)).val * S_mat.val =
      S_mat.val * (shiftSL_loc m : SL(2, ℤ)).val :=
    congr_arg Subtype.val (heq.comm S_mat)
  have h_00 := congr_fun (congr_fun hcomm_val 0) 0
  simp only [S_mat, shiftSL_loc, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h_00
  apply hm
  linarith

lemma peterssonAdj_T_p_upper_eq_shift_mul_lower
    (p : ℕ) (hp : 0 < p) (b : ℕ) :
    peterssonAdj (glMap (T_p_upper p hp b)) =
      (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (-(b : ℤ))) *
        glMap (T_p_lower p hp) := by
  apply Units.ext
  ext i j
  have h_rhs : ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (-(b : ℤ))) *
      glMap (T_p_lower p hp) : GL (Fin 2) ℝ).val =
      (!![(p : ℝ), -(b : ℝ); 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i' j'
    fin_cases i' <;> fin_cases j' <;>
      simp [shiftSL_loc, glMap, T_p_lower, mapGL, Matrix.SpecialLinearGroup.map,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Units.val_mul]
  show (peterssonAdj (glMap (T_p_upper p hp b)) : Matrix _ _ ℝ) i j =
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (-(b : ℤ))) *
      glMap (T_p_lower p hp) : GL (Fin 2) ℝ).val i j
  rw [peterssonAdj_glMap_T_p_upper p hp b, h_rhs]

private lemma T_p_lower_triple_product_matrix (p N : ℕ) [NeZero N] (hp : 0 < p)
    (hpN : Nat.Coprime p N) :
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) =
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (adjointGamma1Rep p N hpN)) *
      (glMap (T_p_upper p hp 0)) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) := by
  apply Units.ext
  ext i j
  have h_lhs : (glMap (T_p_lower p hp) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ), 0; 0, 1] := by
    ext i' j'
    fin_cases i' <;> fin_cases j' <;> simp [glMap, T_p_lower]
  have hbez : (p : ℤ) * Int.gcdA p N + Int.gcdB p N * N = 1 := by
    have h := Int.gcd_eq_gcd_ab p N
    rw [show (Int.gcd (↑p) (↑N) : ℤ) = 1 by exact_mod_cast hpN] at h
    linarith
  have hbezℝ : (p : ℝ) * (Int.gcdA p N : ℝ) + (Int.gcdB p N : ℝ) * (N : ℝ) = 1 := by
    have := congr_arg (Int.cast : ℤ → ℝ) hbez
    push_cast at this
    linarith
  have h_rhs : ((((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (adjointGamma1Rep p N hpN)) *
      (glMap (T_p_upper p hp 0))) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) :
      GL (Fin 2) ℝ).val =
      (!![(p : ℝ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i' j'
    fin_cases i' <;> fin_cases j' <;>
      simp [adjointGamma1Rep, adjointGamma0Rep, glMap, T_p_upper,
        mapGL, Matrix.SpecialLinearGroup.map,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Units.val_mul] <;>
      nlinarith [hbezℝ]
  show (glMap (T_p_lower p hp) : Matrix _ _ ℝ) i j =
    ((((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (adjointGamma1Rep p N hpN)) *
        (glMap (T_p_upper p hp 0))) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) : GL (Fin 2) ℝ).val i j
  rw [h_lhs, h_rhs]

private lemma slash_T_p_lower_eq_T_p_upper_zero_slash_gamma0_ModularForm
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑f ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) =
      (⇑f ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) := by
  rw [show (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) =
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (adjointGamma1Rep p N hpN)) *
      (glMap (T_p_upper p hp.pos 0)) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) from
    T_p_lower_triple_product_matrix p N hp.pos hpN]
  rw [SlashAction.slash_mul, SlashAction.slash_mul]
  congr 2
  exact SlashInvariantFormClass.slash_action_eq f _
    ⟨adjointGamma1Rep p N hpN, adjointGamma1Rep_mem_Gamma1 p N hpN, rfl⟩

lemma slash_T_p_lower_eq_T_p_upper_zero_slash_gamma0
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑f ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) =
      (⇑f ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) :=
  slash_T_p_lower_eq_T_p_upper_zero_slash_gamma0_ModularForm p hp hpN f.toModularForm'

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_add_left (D : Set ℍ) (f₁ f₂ g : ℍ → ℂ)
    (hf₁ : IntegrableOn (fun τ ↦ petersson k g f₁ τ) D μ_hyp)
    (hf₂ : IntegrableOn (fun τ ↦ petersson k g f₂ τ) D μ_hyp) :
    peterssonInner k D (f₁ + f₂) g =
      peterssonInner k D f₁ g + peterssonInner k D f₂ g := by
  rw [← peterssonInner_conj_symm k D (f₁ + f₂) g,
    peterssonInner_add_right k D g f₁ f₂ hf₁ hf₂, map_add,
    peterssonInner_conj_symm k D f₁ g, peterssonInner_conj_symm k D f₂ g]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- `petersson` is linear in its second argument over finite sums. -/
theorem petersson_sum_right {ι : Type*} (s : Finset ι) (f : ℍ → ℂ)
    (g : ι → ℍ → ℂ) (τ : ℍ) :
    petersson k f (∑ i ∈ s, g i) τ = ∑ i ∈ s, petersson k f (g i) τ := by
  simp only [petersson, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- Finset additivity of `peterssonInner` in the first argument. -/
theorem peterssonInner_sum_left
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → ℍ → ℂ)
    (g : ℍ → ℂ) (D : Set ℍ)
    (h_int : ∀ i ∈ s, IntegrableOn (fun τ ↦ petersson k g (F i) τ) D μ_hyp) :
    peterssonInner k D (∑ i ∈ s, F i) g = ∑ i ∈ s, peterssonInner k D (F i) g := by
  induction s using Finset.induction_on with
  | empty => simp [peterssonInner_zero_left]
  | insert i t hi ih =>
    rw [Finset.sum_insert hi]
    have h_t := fun j hj ↦ h_int j (Finset.mem_insert_of_mem hj)
    have h_sum_int :
        IntegrableOn (fun τ ↦ petersson k g (∑ j ∈ t, F j) τ) D μ_hyp := by
      rw [funext (petersson_sum_right t g F)]
      exact MeasureTheory.integrable_finsetSum _ h_t
    rw [peterssonInner_add_left D (F i) (∑ j ∈ t, F j) g
        (h_int i (Finset.mem_insert_self i t)) h_sum_int,
      ih h_t, Finset.sum_insert hi]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- Sum-of-slashes adjoint identity (DS Theorem 5.5.2(b) slice). -/
theorem peterssonInner_sum_slash_adjoint
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → GL (Fin 2) ℝ) (hα : ∀ i ∈ s, 0 < (α i).det.val)
    (D : Set ℍ) (f g : ℍ → ℂ)
    (h_int : ∀ i ∈ s,
      IntegrableOn (fun τ ↦ petersson k g (f ∣[k] α i) τ) D μ_hyp) :
    peterssonInner k D (∑ i ∈ s, f ∣[k] α i) g =
      ∑ i ∈ s, peterssonInner k ((α i) • D) f (g ∣[k] peterssonAdj (α i)) := by
  rw [peterssonInner_sum_left s (fun i ↦ f ∣[k] α i) g D h_int]
  exact Finset.sum_congr rfl fun i hi ↦ peterssonInner_slash_adjoint D (α i) (hα i hi) f g

open UpperHalfPlane ModularGroup MeasureTheory in
/-- Finite-union bridge (pure measure-theoretic form). -/
theorem setIntegral_biUnion_finset_ae
    {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) {S : ι → Set X} {f : X → E}
    (hm : ∀ i ∈ s, NullMeasurableSet (S i) μ)
    (hd : (↑s : Set ι).Pairwise (fun i j ↦ AEDisjoint μ (S i) (S j)))
    (hfi : IntegrableOn f (⋃ i ∈ s, S i) μ) :
    ∫ x in ⋃ i ∈ s, S i, f x ∂μ = ∑ i ∈ s, ∫ x in S i, f x ∂μ := by
  classical
  have h_biU : (⋃ i ∈ s, S i) = ⋃ i : s, S i.val := by
    ext x
    simp [Set.mem_iUnion]
  have hm' : ∀ i : s, NullMeasurableSet (S i.val) μ :=
    fun i ↦ hm i.val i.property
  have hd' : Pairwise (fun i j : s ↦ AEDisjoint μ (S i.val) (S j.val)) :=
    fun i j hij ↦ hd (Finset.mem_coe.mpr i.property) (Finset.mem_coe.mpr j.property)
      (fun h ↦ hij (Subtype.ext h))
  have hfi' : IntegrableOn f (⋃ i : s, S i.val) μ := h_biU ▸ hfi
  rw [h_biU, integral_iUnion_ae hm' hd' hfi', tsum_fintype,
    Finset.sum_coe_sort s (fun i ↦ ∫ x in S i, f x ∂μ)]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- Finite-union bridge (`peterssonInner` form). -/
theorem peterssonInner_biUnion_finset_ae
    {ι : Type*} (s : Finset ι) {D : ι → Set ℍ}
    (hm : ∀ i ∈ s, NullMeasurableSet (D i) μ_hyp)
    (hd : (↑s : Set ι).Pairwise (fun i j ↦ AEDisjoint μ_hyp (D i) (D j)))
    (f g : ℍ → ℂ)
    (hfi : IntegrableOn (fun τ ↦ petersson k f g τ) (⋃ i ∈ s, D i) μ_hyp) :
    peterssonInner k (⋃ i ∈ s, D i) f g = ∑ i ∈ s, peterssonInner k (D i) f g :=
  setIntegral_biUnion_finset_ae s hm hd hfi

open UpperHalfPlane ModularGroup MeasureTheory in
/-- Sum-of-slashes adjoint identity under a constant-RHS hypothesis. -/
theorem peterssonInner_sum_slash_adjoint_constantRHS
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → GL (Fin 2) ℝ) (hα : ∀ i ∈ s, 0 < (α i).det.val)
    (D : Set ℍ) (f g g' : ℍ → ℂ)
    (hadj : ∀ i ∈ s, g ∣[k] peterssonAdj (α i) = g')
    (h_int : ∀ i ∈ s,
      IntegrableOn (fun τ ↦ petersson k g (f ∣[k] α i) τ) D μ_hyp)
    (hm : ∀ i ∈ s, NullMeasurableSet ((α i) • D) μ_hyp)
    (hd : (↑s : Set ι).Pairwise
      (fun i j ↦ AEDisjoint μ_hyp ((α i) • D) ((α j) • D)))
    (hfi : IntegrableOn (fun τ ↦ petersson k f g' τ)
      (⋃ i ∈ s, (α i) • D) μ_hyp) :
    peterssonInner k D (∑ i ∈ s, f ∣[k] α i) g =
      peterssonInner k (⋃ i ∈ s, (α i) • D) f g' := by
  rw [peterssonInner_sum_slash_adjoint s α hα D f g h_int,
    peterssonInner_biUnion_finset_ae s hm hd f g' hfi]
  exact Finset.sum_congr rfl fun i hi ↦ by rw [hadj i hi]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- Positive-determinant `GL (Fin 2) ℝ` elements act measure-preservingly on `ℍ`
with respect to `μ_hyp`. -/
theorem measurePreserving_glPos_smul (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val) :
    MeasurePreserving ((α • ·) : ℍ → ℍ) μ_hyp μ_hyp :=
  measurePreserving_smul (⟨α, hα⟩ : GL(2, ℝ)⁺) μ_hyp

open UpperHalfPlane ModularGroup MeasureTheory in
/-- For `α₁, α₂ : GL (Fin 2) ℝ` with `α₁⁻¹` measure-preserving on ℍ, if
`α₁⁻¹ * α₂ = mapGL ℝ γ` for some `γ ∈ Γ₁(N)` non-trivial in `PSL(2,ℤ)`,
then `α₁ • D_N^PSL` and `α₂ • D_N^PSL` are AE-disjoint. -/
theorem aedisjoint_glMap_smul_of_mul_inv_eq_mapGL_Gamma1
    {N : ℕ} [NeZero N] (α₁ α₂ : GL (Fin 2) ℝ)
    (h_mp_inv : MeasurePreserving ((α₁⁻¹ • ·) : ℍ → ℍ) μ_hyp μ_hyp)
    (γ : SL(2, ℤ)) (hγ_Γ1 : γ ∈ Gamma1 N)
    (hγ_ne : (QuotientGroup.mk γ : PSL(2, ℤ)) ≠ 1)
    (h_inv_mul : α₁⁻¹ * α₂ = ((mapGL ℝ : SL(2, ℤ) →* _) γ : GL (Fin 2) ℝ)) :
    AEDisjoint μ_hyp (α₁ • (Gamma1_fundDomain_PSL N : Set ℍ))
      (α₂ • (Gamma1_fundDomain_PSL N : Set ℍ)) := by
  set D : Set ℍ := Gamma1_fundDomain_PSL N
  set q : PSL(2, ℤ) := QuotientGroup.mk γ with hq_def
  have h_inner : AEDisjoint μ_hyp D (q • D) := by
    have h_mem : (1 : PSL(2, ℤ))⁻¹ * q ∈ imageGamma1_PSL N := by
      rw [inv_one, one_mul, hq_def]
      exact Subgroup.mem_map.mpr ⟨γ, hγ_Γ1, rfl⟩
    have h_gen := isFundamentalDomain_Gamma1_coset_tiling (N := N)
      |>.aedisjoint_smul_of_mul_inv_mem h_mem (by rw [inv_one, one_mul]; exact hγ_ne)
    rwa [one_smul] at h_gen
  have h_pre_α₁ : ((α₁⁻¹ • ·) ⁻¹' D : Set ℍ) = α₁ • D := by
    ext τ
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
  have h_pre_α₂ : ((α₁⁻¹ • ·) ⁻¹' (q • D) : Set ℍ) = α₂ • D := by
    ext τ
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
    have hq_smul : ∀ σ : ℍ, (q⁻¹ • σ : ℍ) =
        (((mapGL ℝ : SL(2, ℤ) →* _) γ)⁻¹ : GL (Fin 2) ℝ) • σ := by
      intro σ
      rw [hq_def, ← QuotientGroup.mk_inv, PSL_smul_coe,
        sl_moeb, show ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) =
          ((mapGL ℝ : SL(2, ℤ) →* _) γ)⁻¹ by rw [← map_inv]; rfl]
    rw [hq_smul (α₁⁻¹ • τ)]
    have h_eq : ((mapGL ℝ : SL(2, ℤ) →* _) γ)⁻¹ = α₂⁻¹ * α₁ := by
      rw [← h_inv_mul, mul_inv_rev, inv_inv]
    rw [h_eq, mul_smul, show (α₁ • α₁⁻¹ • τ : ℍ) = τ by
      rw [← mul_smul, mul_inv_cancel, one_smul]]
  have h_pre_aedisjoint : AEDisjoint μ_hyp
      ((α₁⁻¹ • ·) ⁻¹' D) ((α₁⁻¹ • ·) ⁻¹' (q • D)) :=
    h_inner.preimage h_mp_inv.quasiMeasurePreserving
  rwa [h_pre_α₁, h_pre_α₂] at h_pre_aedisjoint

open UpperHalfPlane ModularGroup MeasureTheory in
/-- `(glMap T_p_upper(b₁))⁻¹ * (glMap T_p_upper(b₂)) = mapGL ℝ (shiftSL_loc (b₂ - b₁))`
in `GL (Fin 2) ℝ`. -/
theorem glMap_T_p_upper_inv_mul_eq_mapGL_shift
    {p : ℕ} (hp : 0 < p) (b₁ b₂ : ℕ) :
    (glMap (T_p_upper p hp b₁) : GL (Fin 2) ℝ)⁻¹ *
        (glMap (T_p_upper p hp b₂) : GL (Fin 2) ℝ) =
      ((mapGL ℝ : SL(2, ℤ) →* _) (shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ)))) := by
  have h_mul : (glMap (T_p_upper p hp b₂) : GL (Fin 2) ℝ) =
      (glMap (T_p_upper p hp b₁) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* _) (shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ)))) := by
    apply Units.ext
    ext i j
    have h_L : ((glMap (T_p_upper p hp b₂) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (b₂ : ℝ); 0, (p : ℝ)] := by
      ext i' j'
      fin_cases i' <;> fin_cases j' <;>
        simp [glMap, T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
          Matrix.GeneralLinearGroup.map, Matrix.of_apply]
    have h_R1 : ((glMap (T_p_upper p hp b₁) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (b₁ : ℝ); 0, (p : ℝ)] := by
      ext i' j'
      fin_cases i' <;> fin_cases j' <;>
        simp [glMap, T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
          Matrix.GeneralLinearGroup.map, Matrix.of_apply]
    have h_R2 : (((mapGL ℝ : SL(2, ℤ) →* _) (shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ)))) :
        Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (b₂ : ℝ) - (b₁ : ℝ); 0, 1] := by
      ext i' j'
      fin_cases i' <;> fin_cases j' <;>
        simp [mapGL_coe_matrix, shiftSL_loc, algebraMap_int_eq, Matrix.of_apply]
    show ((glMap (T_p_upper p hp b₂) : GL (Fin 2) ℝ) : Matrix _ _ ℝ) i j =
      ((glMap (T_p_upper p hp b₁) : GL (Fin 2) ℝ) *
       ((mapGL ℝ : SL(2, ℤ) →* _) (shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ)))) :
       GL (Fin 2) ℝ).val i j
    rw [h_L, Units.val_mul, h_R1, h_R2]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
  rw [h_mul, ← mul_assoc, inv_mul_cancel, one_mul]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- AE-disjointness for two `T_p_upper`-translates. -/
theorem aedisjoint_glMap_T_p_upper_pair
    {N : ℕ} [NeZero N] {p : ℕ} (hp : 0 < p) {b₁ b₂ : ℕ}
    (hne : (b₂ : ℤ) - (b₁ : ℤ) ≠ 0) :
    AEDisjoint μ_hyp
      ((glMap (T_p_upper p hp b₁) : GL (Fin 2) ℝ) •
        (Gamma1_fundDomain_PSL N : Set ℍ))
      ((glMap (T_p_upper p hp b₂) : GL (Fin 2) ℝ) •
        (Gamma1_fundDomain_PSL N : Set ℍ)) :=
  aedisjoint_glMap_smul_of_mul_inv_eq_mapGL_Gamma1
    (glMap (T_p_upper p hp b₁)) (glMap (T_p_upper p hp b₂))
    (measurePreserving_glPos_smul _ (det_val_inv_pos (glMap_T_p_upper_det_pos p hp b₁)))
    (shiftSL_loc ((b₂ : ℤ) - (b₁ : ℤ))) (shiftSL_loc_mem_Gamma1 _)
    (shiftSL_loc_psl_ne_one hne)
    (glMap_T_p_upper_inv_mul_eq_mapGL_shift hp b₁ b₂)

open UpperHalfPlane ModularGroup MeasureTheory in
/-- `μ_hyp` is invariant under positive-determinant `GL (Fin 2) ℝ` translates. -/
theorem measure_glPos_smul_eq (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val)
    {S : Set ℍ} (hS : NullMeasurableSet S μ_hyp) :
    μ_hyp (α • S) = μ_hyp S := by
  have h_eq : ((α⁻¹ • ·) : ℍ → ℍ) ⁻¹' S = α • S := by
    ext τ
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
  rw [← h_eq]
  exact (measurePreserving_glPos_smul α⁻¹ (det_val_inv_pos hα)).measure_preimage hS

open UpperHalfPlane ModularGroup MeasureTheory in
/-- A `glMap`-translate of the Γ₁(N)-fundamental domain has finite hyperbolic measure. -/
theorem measure_glPos_smul_Gamma1_fundDomain_lt_top
    {N : ℕ} [NeZero N] (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val) :
    μ_hyp (α • (Gamma1_fundDomain_PSL N : Set ℍ)) < ⊤ := by
  rw [measure_glPos_smul_eq α hα
    isFundamentalDomain_Gamma1_PSL.nullMeasurableSet]
  exact hyperbolicMeasure_Gamma1_fundDomain_PSL_lt_top

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The explicit `Γ₁(N)` factor arising from `T_p_upper(b)⁻¹ · M_∞`: the
`SL(2, ℤ)` element with matrix `!![ap − bNm, 1 − b; Nm, 1]`
(where `a = aInvOfCoprime`, `m = mIdxOfCoprime`, so `ap − Nm = 1` by Bézout). -/
noncomputable def M_infty_Gamma1_factor
    (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) (b : ℕ) : SL(2, ℤ) :=
  ⟨!![(aInvOfCoprime N p hpN : ℤ) * p - (b : ℤ) * ((N : ℤ) * mIdxOfCoprime N p hpN),
      1 - (b : ℤ);
      (N : ℤ) * mIdxOfCoprime N p hpN, 1],
    by
      rw [Matrix.det_fin_two_of]
      linarith [N_mul_mIdx_eq N p hpN]⟩

open UpperHalfPlane ModularGroup MeasureTheory in
/-- `M_infty_Gamma1_factor` lies in `Γ₁(N)`. -/
theorem M_infty_Gamma1_factor_mem_Gamma1
    (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) (b : ℕ) :
    M_infty_Gamma1_factor N p hpN b ∈ Gamma1 N := by
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩
  · change ((((aInvOfCoprime N p hpN : ℤ) * p -
        (b : ℤ) * ((N : ℤ) * mIdxOfCoprime N p hpN)) : ℤ) : ZMod N) = 1
    push_cast
    have : (((b : ℕ) : ZMod N) *
        (((N : ℕ) : ZMod N) * ((mIdxOfCoprime N p hpN : ℤ) : ZMod N))) = 0 := by
      rw [show (((N : ℕ) : ZMod N)) = 0 from ZMod.natCast_self N]
      ring
    rw [this, sub_zero]
    exact aInvOfCoprime_mul_eq_one N p hpN
  · change ((1 : ℤ) : ZMod N) = 1
    push_cast
    rfl
  · change ((((N : ℤ) * mIdxOfCoprime N p hpN) : ℤ) : ZMod N) = 0
    push_cast
    rw [show (((N : ℕ) : ZMod N)) = 0 from ZMod.natCast_self N]
    ring

open UpperHalfPlane ModularGroup MeasureTheory in
/-- `M_infty_Gamma1_factor` is non-trivial in `PSL(2, ℤ)` for `p` prime. -/
theorem M_infty_Gamma1_factor_psl_ne_one
    (N p : ℕ) [NeZero N] (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ) :
    (QuotientGroup.mk (M_infty_Gamma1_factor N p hpN b) : PSL(2, ℤ)) ≠ 1 := by
  intro heq
  rw [QuotientGroup.eq_one_iff] at heq
  have hS : (!![(0 : ℤ), -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    simp [Matrix.det_fin_two]
  set S_mat : SL(2, ℤ) := ⟨!![0, -1; 1, 0], hS⟩
  have hcomm_val : (M_infty_Gamma1_factor N p hpN b : SL(2, ℤ)).val * S_mat.val =
      S_mat.val * (M_infty_Gamma1_factor N p hpN b : SL(2, ℤ)).val :=
    congr_arg Subtype.val (heq.comm S_mat)
  have h_10 := congr_fun (congr_fun hcomm_val 1) 0
  simp only [S_mat, M_infty_Gamma1_factor, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h_10
  have h_00 := congr_fun (congr_fun hcomm_val 0) 0
  simp only [S_mat, M_infty_Gamma1_factor, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h_00
  have h_bezout := N_mul_mIdx_eq N p hpN
  have h_Nm_zero : (N : ℤ) * mIdxOfCoprime N p hpN = 0 := by
    have h_sub : (1 - (b : ℤ)) * ((N : ℤ) * mIdxOfCoprime N p hpN) = 0 := by
      linarith
    have h_subst : -((N : ℤ) * mIdxOfCoprime N p hpN) *
        ((N : ℤ) * mIdxOfCoprime N p hpN) = 0 := by
      have : (1 - (b : ℤ)) = -((N : ℤ) * mIdxOfCoprime N p hpN) := by linarith
      rw [this] at h_sub
      exact h_sub
    have h_sq : ((N : ℤ) * mIdxOfCoprime N p hpN)^2 = 0 := by nlinarith [h_subst]
    exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h_sq
  have h_ap : (aInvOfCoprime N p hpN : ℤ) * p = 1 := by linarith
  have hp_div : (p : ℤ) ∣ 1 := ⟨aInvOfCoprime N p hpN, by linarith⟩
  have hp_ge : (p : ℤ) ≥ 2 := by exact_mod_cast hp.two_le
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hp_div) with h | h <;> omega

open UpperHalfPlane ModularGroup MeasureTheory in
/-- `(T_p_upper(b))⁻¹ · M_∞ = mapGL ℝ (M_infty_Gamma1_factor)`. -/
theorem glMap_T_p_upper_inv_mul_M_infty_eq_mapGL_Gamma1
    (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) (b : ℕ) :
    (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ)⁻¹ *
        (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) =
      ((mapGL ℝ : SL(2, ℤ) →* _) (M_infty_Gamma1_factor N p hpN b)) := by
  have h_mul : (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) =
      (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* _) (M_infty_Gamma1_factor N p hpN b)) := by
    apply Units.ext
    ext i j
    have h_L : ((glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        !![((aInvOfCoprime N p hpN : ℤ) : ℝ) * (p : ℝ), 1;
           (((N : ℤ) * mIdxOfCoprime N p hpN : ℤ) : ℝ) * (p : ℝ), (p : ℝ)] := by
      ext i' j'
      fin_cases i' <;> fin_cases j' <;>
        simp [glMap, M_infty, Matrix.GeneralLinearGroup.mkOfDetNeZero,
          Matrix.GeneralLinearGroup.map, Matrix.of_apply]
    have h_R1 : ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (b : ℝ); 0, (p : ℝ)] := by
      ext i' j'
      fin_cases i' <;> fin_cases j' <;>
        simp [glMap, T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
          Matrix.GeneralLinearGroup.map, Matrix.of_apply]
    have h_R2 : (((mapGL ℝ : SL(2, ℤ) →* _) (M_infty_Gamma1_factor N p hpN b)) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        !![((aInvOfCoprime N p hpN : ℤ) : ℝ) * (p : ℝ) -
             (b : ℝ) * (((N : ℤ) * mIdxOfCoprime N p hpN : ℤ) : ℝ),
           (1 : ℝ) - (b : ℝ);
           (((N : ℤ) * mIdxOfCoprime N p hpN : ℤ) : ℝ), 1] := by
      ext i' j'
      fin_cases i' <;> fin_cases j' <;>
        simp [mapGL_coe_matrix, M_infty_Gamma1_factor, algebraMap_int_eq,
          Matrix.of_apply]
    show ((glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) : Matrix _ _ ℝ) i j =
      ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) *
       ((mapGL ℝ : SL(2, ℤ) →* _) (M_infty_Gamma1_factor N p hpN b)) :
       GL (Fin 2) ℝ).val i j
    rw [h_L, Units.val_mul, h_R1, h_R2]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, mul_comm]
  rw [h_mul, ← mul_assoc, inv_mul_cancel, one_mul]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- AE-disjointness for `T_p_upper(b)` versus `M_∞` (`p` prime). -/
theorem aedisjoint_glMap_M_infty_T_p_upper
    {N : ℕ} [NeZero N] {p : ℕ} (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ) :
    AEDisjoint μ_hyp
      ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
        (Gamma1_fundDomain_PSL N : Set ℍ))
      ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
        (Gamma1_fundDomain_PSL N : Set ℍ)) :=
  aedisjoint_glMap_smul_of_mul_inv_eq_mapGL_Gamma1
    (glMap (T_p_upper p hp.pos b)) (glMap (M_infty N p hp.pos hpN))
    (measurePreserving_glPos_smul _ (det_val_inv_pos (glMap_T_p_upper_det_pos p hp.pos b)))
    (M_infty_Gamma1_factor N p hpN b)
    (M_infty_Gamma1_factor_mem_Gamma1 N p hpN b)
    (M_infty_Gamma1_factor_psl_ne_one N p hp hpN b)
    (glMap_T_p_upper_inv_mul_M_infty_eq_mapGL_Gamma1 N p hp.pos hpN b)

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The `T_p`-double-coset family `{T_p_upper(b)}_{b<p} ∪ {M_∞}` gives pairwise
AE-disjoint translates of `Gamma1_fundDomain_PSL N`. -/
theorem aedisjoint_pairwise_T_p_family
    {N : ℕ} [NeZero N] (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    (↑(Finset.univ : Finset (Option (Fin p))) : Set (Option (Fin p))).Pairwise
      (fun i j ↦ AEDisjoint μ_hyp
          ((match i with
            | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
            | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
              (Gamma1_fundDomain_PSL N : Set ℍ))
          ((match j with
            | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
            | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
              (Gamma1_fundDomain_PSL N : Set ℍ))) := by
  intro i _ j _ hij
  match i, j, hij with
  | none, none, h => exact absurd rfl h
  | none, some b, _ =>
    exact (aedisjoint_glMap_M_infty_T_p_upper hp hpN b.val).symm
  | some b, none, _ => exact aedisjoint_glMap_M_infty_T_p_upper hp hpN b.val
  | some b₁, some b₂, hij =>
    refine aedisjoint_glMap_T_p_upper_pair hp.pos fun h_eq ↦ hij ?_
    exact congr_arg some (Fin.ext (by omega))

open UpperHalfPlane ModularGroup MeasureTheory in
/-- Petersson sum-of-slashes equals the aggregate Hecke-FD biUnion, with an
explicit union-integrability hypothesis. -/
theorem peterssonInner_T_p_family_sum_slashes_eq_aggregate_of_integrable
    {N : ℕ} [NeZero N] {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (α : ι → GL (Fin 2) ℝ) (hα : ∀ i ∈ s, 0 < (α i).det.val)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (g' : ℍ → ℂ)
    (hadj : ∀ i ∈ s, ⇑g ∣[k] peterssonAdj (α i) = g')
    (hm : ∀ i ∈ s,
      NullMeasurableSet (α i • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp)
    (hd : (↑s : Set ι).Pairwise
      (fun i j ↦ AEDisjoint μ_hyp
        (α i • (Gamma1_fundDomain_PSL N : Set ℍ))
        (α j • (Gamma1_fundDomain_PSL N : Set ℍ))))
    (h_int_per : ∀ i ∈ s,
      IntegrableOn (fun τ ↦ petersson k ⇑g (⇑f ∣[k] α i) τ)
        (Gamma1_fundDomain_PSL N) μ_hyp)
    (hfi : IntegrableOn (fun τ ↦ petersson k ⇑f g' τ)
      (⋃ i ∈ s, α i • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp) :
    peterssonInner k (Gamma1_fundDomain_PSL N) (∑ i ∈ s, ⇑f ∣[k] α i) ⇑g =
      peterssonInner k
        (⋃ i ∈ s, α i • (Gamma1_fundDomain_PSL N : Set ℍ))
        ⇑f g' :=
  peterssonInner_sum_slash_adjoint_constantRHS s α hα
    (Gamma1_fundDomain_PSL N) ⇑f ⇑g g' hadj h_int_per hm hd hfi

open UpperHalfPlane ModularGroup MeasureTheory in
/-- `glMap M_∞` has positive determinant `p` in `GL (Fin 2) ℝ`. -/
theorem glMap_M_infty_det_pos
    (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    0 < (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ).det.val := by
  show 0 < ((glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ).det
  rw [show ((glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      ((M_infty N p hp hpN : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl,
    show (((M_infty N p hp hpN : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ)).det =
      (algebraMap ℚ ℝ) (((M_infty N p hp hpN : GL (Fin 2) ℚ).val).det) from
        (RingHom.map_det _ _).symm]
  have h_det_Q : ((M_infty N p hp hpN : GL (Fin 2) ℚ).val).det = (p : ℚ) := by
    simp only [M_infty_val, Matrix.det_fin_two_of]
    have hmem_q : ((N : ℤ) * mIdxOfCoprime N p hpN : ℚ) =
        (aInvOfCoprime N p hpN : ℤ) * p - 1 := by exact_mod_cast N_mul_mIdx_eq N p hpN
    rw [hmem_q]
    ring
  rw [h_det_Q]
  change 0 < ((p : ℚ) : ℝ)
  exact_mod_cast hp

lemma peterssonAdj_glMap_T_p_upper_zero_eq_glMap_T_p_lower
    (p : ℕ) (hp : 0 < p) :
    peterssonAdj (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) =
      (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) := by
  apply Units.ext
  ext i j
  have h_L := peterssonAdj_glMap_T_p_upper p hp 0
  simp only [Nat.cast_zero, neg_zero] at h_L
  have h_R : ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![(p : ℝ), 0; 0, (1 : ℝ)] := by
    ext i' j'
    fin_cases i' <;> fin_cases j' <;> simp [glMap, T_p_lower]
  show (peterssonAdj (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) :
      Matrix _ _ ℝ) i j =
    ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) : Matrix _ _ ℝ) i j
  rw [h_L, h_R]

lemma slash_peterssonAdj_glMap_M_infty_eq_slash_T_p_upper_zero_slash_gamma0
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑g ∣[k] peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) =
      (⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) := by
  have h_M_infty_eq : (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) =
      (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* _) (M_infty_Gamma1_factor N p hpN 0)) := by
    rw [← glMap_T_p_upper_inv_mul_M_infty_eq_mapGL_Gamma1 N p hp.pos hpN 0,
      mul_inv_cancel_left]
  rw [h_M_infty_eq, peterssonAdj_mul, peterssonAdj_mapGL_SL_eq_inv,
    peterssonAdj_glMap_T_p_upper_zero_eq_glMap_T_p_lower, ← map_inv, SlashAction.slash_mul]
  have h_g_slash : ⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (M_infty_Gamma1_factor N p hpN 0)⁻¹) = ⇑g :=
    SlashInvariantFormClass.slash_action_eq g _
      ⟨(M_infty_Gamma1_factor N p hpN 0)⁻¹, inv_mem (M_infty_Gamma1_factor_mem_Gamma1 N p hpN 0),
        rfl⟩
  rw [h_g_slash]
  exact slash_T_p_lower_eq_T_p_upper_zero_slash_gamma0 p hp hpN g

lemma slash_peterssonAdj_glMap_M_infty_eq_slash_T_p_lower
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑g ∣[k] peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) =
      ⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) := by
  rw [slash_peterssonAdj_glMap_M_infty_eq_slash_T_p_upper_zero_slash_gamma0
    p hp hpN g]
  exact (slash_T_p_lower_eq_T_p_upper_zero_slash_gamma0 p hp hpN g).symm

lemma slash_peterssonAdj_glMap_T_p_upper_eq_slash_T_p_lower
    (p : ℕ) (hp : 0 < p) (b : ℕ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑g ∣[k] peterssonAdj (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) =
      ⇑g ∣[k] (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) := by
  rw [peterssonAdj_T_p_upper_eq_shift_mul_lower p hp b, SlashAction.slash_mul,
    show (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      (shiftSL_loc (-(b : ℤ))) : GL (Fin 2) ℝ)) = ⇑g from
        SlashInvariantFormClass.slash_action_eq g _
          ⟨shiftSL_loc (-(b : ℤ)), shiftSL_loc_mem_Gamma1 _, rfl⟩]

end HeckeRing.GL2

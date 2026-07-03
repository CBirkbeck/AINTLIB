import Mathlib

import LeanModularForms.HeckeRIngs.GL2.Gamma1Pair
import LeanModularForms.HeckeRIngs.GL2.Newforms

open ModularForm UpperHalfPlane MatrixGroups ComplexConjugate CongruenceSubgroup Pointwise Subgroup

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

/-- The dual of a subgroup of `GL (Fin 2) ℝ` is its conjugate by `J⁻¹`. -/
noncomputable def Subgroup.dual (Γ : Subgroup (GL (Fin 2) ℝ)) : Subgroup (GL (Fin 2) ℝ) :=
  (ConjAct.toConjAct UpperHalfPlane.J⁻¹) • Γ

private lemma J_mul_self : UpperHalfPlane.J * UpperHalfPlane.J = 1 := by
  simpa [sq] using UpperHalfPlane.J_sq

private lemma J_inv : UpperHalfPlane.J⁻¹ = UpperHalfPlane.J :=
  inv_eq_of_mul_eq_one_right J_mul_self

namespace Subgroup

open Matrix.GeneralLinearGroup

/-- Conjugation by `J` sends `upperRightHom x` to `upperRightHom (-x)`. -/
theorem dual_upperRightHom (x : ℝ) :
    ConjAct.toConjAct UpperHalfPlane.J • upperRightHom x = upperRightHom (-x) := by
  rw [ConjAct.toConjAct_smul, J_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [UpperHalfPlane.J, Matrix.GeneralLinearGroup.upperRightHom, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- Dualising a subgroup preserves its strict periods. -/
theorem dual_strictPeriods_eq (Γ : Subgroup (GL (Fin 2) ℝ)) :
    (Subgroup.dual Γ).strictPeriods = Γ.strictPeriods := by
  ext x
  simp only [mem_strictPeriods_iff, Subgroup.dual, mem_pointwise_smul_iff_inv_smul_mem,
    map_inv, inv_inv, dual_upperRightHom]
  simpa using (Subgroup.inv_mem_iff Γ (x := upperRightHom x))

end Subgroup

/-- A subgroup is self-dual when it equals its own dual. -/
class Subgroup.IsSelfDual (Γ : Subgroup (GL (Fin 2) ℝ)) : Prop where
  isSelfDual : Subgroup.dual Γ = Γ

/-- Example: the trivial subgroup is self-dual. -/
instance : Subgroup.IsSelfDual (⊥ : Subgroup (GL (Fin 2) ℝ)) where
  isSelfDual := by simp [Subgroup.dual]

/-- The dual of a modular-form-like object is its translate by `J`. -/
noncomputable def ModularFormClass.dual {F : Type*} [FunLike F UpperHalfPlane ℂ]
    [ModularFormClass F Γ k] (f : F) : ModularForm (Subgroup.dual Γ) k :=
  ModularForm.translate f UpperHalfPlane.J

/-- A modular-form-like object is self-dual when it equals its own dual. -/
def ModularFormClass.isSelfDual {F : Type*} [FunLike F UpperHalfPlane ℂ]
    [ModularFormClass F Γ k] (f : F) : Prop :=
  ⇑(ModularFormClass.dual f) = ⇑f

/-- Transporting a modular form along an equality of subgroups leaves its coercion unchanged. -/
theorem ModularForm.coe_cast_group {Γ Γ' : Subgroup (GL (Fin 2) ℝ)}
    (h : Γ = Γ') (f : ModularForm Γ k) : ⇑(h ▸ f : ModularForm Γ' k) = ⇑f := by
  cases h
  rfl

open Classical in
/-- Dualising a subgroup preserves the strict width of the cusp `∞`. -/
theorem Subgroup.dual_width_eq (Γ : Subgroup (GL (Fin 2) ℝ)) :
    strictWidthInfty (Subgroup.dual Γ) = strictWidthInfty Γ :=
  congrArg (fun H : AddSubgroup ℝ ↦
    if h : DiscreteTopology H then
      |Exists.choose <| H.isAddCyclic_iff_exists_zmultiples_eq_top.mp
        <| AddSubgroup.discrete_iff_addCyclic.mpr h|
    else 0) (Subgroup.dual_strictPeriods_eq Γ)

private lemma strictWidthInfty_mem_dual_strictPeriods (Γ : Subgroup (GL (Fin 2) ℝ))
    [Γ.IsArithmetic] : strictWidthInfty Γ ∈ (Subgroup.dual Γ).strictPeriods := by
  rw [← Subgroup.dual_width_eq Γ]
  exact (Subgroup.dual Γ).strictWidthInfty_mem_strictPeriods

private lemma qParam_J_smul (h : ℝ) (z : UpperHalfPlane) :
    Function.Periodic.qParam h ((UpperHalfPlane.J • z : UpperHalfPlane) : ℂ) =
      conj (Function.Periodic.qParam h (z : ℂ)) := by
  simp [Function.Periodic.qParam, UpperHalfPlane.coe_J_smul, ← Complex.exp_conj, map_ofNat]

/-- `f.dual` at `z` equals the complex conjugate of `f` at `ofComplex (-conj z)`. -/
theorem ModularFormClass.dual_explicit {F : Type*} [FunLike F UpperHalfPlane ℂ]
    [ModularFormClass F Γ k] (f : F) (z : UpperHalfPlane) :
    ModularFormClass.dual f z = conj (f (ofComplex (-(conj (z : ℂ))))) := by
  change (⇑(f : ModularForm Γ k) ∣[(k : ℤ)] UpperHalfPlane.J) z =
    conj (f (ofComplex (-(conj (z : ℂ)))))
  simp [ModularForm.slash_apply, UpperHalfPlane.J_smul]

private lemma hasSum_qExpansion_dual [Γ.IsArithmetic] {F : Type*} [FunLike F UpperHalfPlane ℂ]
    [ModularFormClass F Γ k] (f : F) (z : UpperHalfPlane) :
    HasSum (fun m : ℕ ↦ conj ((qExpansion (strictWidthInfty Γ) f).coeff m) •
        Function.Periodic.qParam (strictWidthInfty Γ) (z : ℂ) ^ m)
      (ModularFormClass.dual f z) := by
  have hf : HasSum (fun m : ℕ ↦ (qExpansion (strictWidthInfty Γ) f).coeff m •
      Function.Periodic.qParam (strictWidthInfty Γ)
        ((UpperHalfPlane.J • z : UpperHalfPlane) : ℂ) ^ m) (f (UpperHalfPlane.J • z)) :=
    UpperHalfPlane.hasSum_qExpansion Γ.strictWidthInfty_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex f Γ.strictWidthInfty_mem_strictPeriods)
      (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) (UpperHalfPlane.J • z)
  convert (Complex.hasSum_conj' (f := fun m : ℕ ↦
    (qExpansion (strictWidthInfty Γ) f).coeff m • Function.Periodic.qParam (strictWidthInfty Γ)
      ((UpperHalfPlane.J • z : UpperHalfPlane) : ℂ) ^ m)
    (x := f (UpperHalfPlane.J • z))).mpr hf using 1
  · ext m
    simp [qParam_J_smul, smul_eq_mul]
  · simp [ModularFormClass.dual_explicit, UpperHalfPlane.J_smul]

/-- The `q`-expansion coefficients of the dual are the complex conjugates of the original's. -/
theorem ModularFormClass.qExpansion_dual_coefficient [Γ.IsArithmetic] {F : Type*}
    [FunLike F UpperHalfPlane ℂ] [ModularFormClass F Γ k] (f : F) (n : ℕ) :
    (qExpansion (strictWidthInfty Γ) (ModularFormClass.dual f)).coeff n =
      conj ((qExpansion (strictWidthInfty Γ) f).coeff n) :=
  (ModularFormClass.qExpansion_coeff_unique (Γ := Subgroup.dual Γ)
    (c := fun m : ℕ ↦ conj ((qExpansion (strictWidthInfty Γ) f).coeff m))
    Γ.strictWidthInfty_pos (strictWidthInfty_mem_dual_strictPeriods Γ)
    (hasSum_qExpansion_dual f) n).symm

private lemma im_coeff_eq_zero_of_isSelfDual [Γ.IsArithmetic] {F : Type*}
    [FunLike F UpperHalfPlane ℂ] [ModularFormClass F Γ k] (f : F)
    (hself : ModularFormClass.isSelfDual f) (n : ℕ) :
    ((qExpansion (strictWidthInfty Γ) f).coeff n).im = 0 := by
  have hcoeff : (qExpansion (strictWidthInfty Γ) (ModularFormClass.dual f)).coeff n =
      conj ((qExpansion (strictWidthInfty Γ) f).coeff n) :=
    ModularFormClass.qExpansion_dual_coefficient f n
  have hsame : (qExpansion (strictWidthInfty Γ) (ModularFormClass.dual f)).coeff n =
      (qExpansion (strictWidthInfty Γ) f).coeff n := by
    simpa [ModularFormClass.isSelfDual] using
      congrArg (fun g : UpperHalfPlane → ℂ ↦ (qExpansion (strictWidthInfty Γ) g).coeff n) hself
  rw [hsame] at hcoeff
  exact Complex.conj_eq_iff_im.mp hcoeff.symm

private lemma isSelfDual_of_forall_im_coeff_eq_zero [Γ.IsArithmetic] {F : Type*}
    [FunLike F UpperHalfPlane ℂ] [ModularFormClass F Γ k] (f : F)
    (hreal : ∀ n, ((qExpansion (strictWidthInfty Γ) f).coeff n).im = 0) :
    ModularFormClass.isSelfDual f := by
  have hh : 0 < strictWidthInfty Γ := Γ.strictWidthInfty_pos
  have hΓ : strictWidthInfty Γ ∈ Γ.strictPeriods := Γ.strictWidthInfty_mem_strictPeriods
  have hdualΓ : strictWidthInfty Γ ∈ (Subgroup.dual Γ).strictPeriods :=
    strictWidthInfty_mem_dual_strictPeriods Γ
  have hqeq : qExpansion (strictWidthInfty Γ) (ModularFormClass.dual f) =
      qExpansion (strictWidthInfty Γ) f := by
    ext n
    exact (ModularFormClass.qExpansion_dual_coefficient f n).trans
      (Complex.conj_eq_iff_im.mpr (hreal n))
  have hqsub :
      qExpansion (strictWidthInfty Γ)
        (⇑(ModularFormClass.dual f) - ⇑f : UpperHalfPlane → ℂ) = 0 := by
    rw [UpperHalfPlane.qExpansion_sub
      (ModularFormClass.analyticAt_cuspFunction_zero (ModularFormClass.dual f) hh hdualΓ)
      (ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ), hqeq, sub_self]
  have hper : Function.Periodic
      ((⇑(ModularFormClass.dual f) - ⇑f : UpperHalfPlane → ℂ) ∘ ofComplex)
        (strictWidthInfty Γ) := by
    intro z
    simpa only [Function.comp_apply, Pi.sub_apply] using
      congrArg₂ (fun a b : ℂ ↦ a - b)
        (SlashInvariantFormClass.periodic_comp_ofComplex (ModularFormClass.dual f) hdualΓ z)
        (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ z)
  have hbdd : IsBoundedAtImInfty
      (⇑(ModularFormClass.dual f) - ⇑f : UpperHalfPlane → ℂ) := by
    have : Fact (IsCusp OnePoint.infty (Subgroup.dual Γ)) :=
      ⟨(Subgroup.dual Γ).isCusp_of_mem_strictPeriods hh hdualΓ⟩
    change Filter.BoundedAtFilter UpperHalfPlane.atImInfty
      (⇑(ModularFormClass.dual f) - ⇑f : UpperHalfPlane → ℂ)
    simpa [sub_eq_add_neg] using
      (ModularFormClass.bdd_at_infty (ModularFormClass.dual f)).add
        (ModularFormClass.bdd_at_infty f).neg
  have hzero : (⇑(ModularFormClass.dual f) - ⇑f : UpperHalfPlane → ℂ) = 0 :=
    (UpperHalfPlane.qExpansion_eq_zero_iff hh hper
      ((ModularFormClass.holo (ModularFormClass.dual f)).sub (ModularFormClass.holo f))
      hbdd).mp hqsub
  exact funext fun z ↦ sub_eq_zero.mp (congrFun hzero z)

/-- A modular-form-like object is self-dual iff all its `q`-expansion coefficients are real. -/
theorem ModularFormClass.isSelfDual_iff [Γ.IsArithmetic] {F : Type*}
    [FunLike F UpperHalfPlane ℂ] [ModularFormClass F Γ k] (f : F) :
    ModularFormClass.isSelfDual f ↔
      ∀ n, ((qExpansion (strictWidthInfty Γ) f).coeff n).im = 0 :=
  ⟨im_coeff_eq_zero_of_isSelfDual f, isSelfDual_of_forall_im_coeff_eq_zero f⟩

section Nebentypus

open Matrix.SpecialLinearGroup HeckeRing.GL2

abbrev Γ₁ (N : ℕ) : Subgroup (GL (Fin 2) ℝ) := (Gamma1 N).map (mapGL ℝ)

private def conjugateByJ (γ : SL(2, ℤ)) : SL(2, ℤ) where
  val := !![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1]
  property := by
    have hdet : γ.val.det = 1 := γ.property
    rw [Matrix.det_fin_two] at hdet
    simpa [Matrix.det_fin_two] using hdet

private lemma conjugateByJ_mem_Gamma1_iff (γ : SL(2, ℤ)) :
    conjugateByJ γ ∈ Gamma1 N ↔ γ ∈ Gamma1 N := by
  rw [Gamma1_mem, Gamma1_mem]
  simp [conjugateByJ]

private lemma conjugateByJ_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    conjugateByJ γ ∈ Gamma0 N := by
  rw [Gamma0_mem] at hγ ⊢
  simpa [conjugateByJ] using hγ

private lemma Gamma0MapUnits_conjugateByJ (γ : ↥(Gamma0 N)) :
    Gamma0MapUnits (⟨conjugateByJ (γ : SL(2, ℤ)), conjugateByJ_mem_Gamma0 (N := N) γ.property⟩ :
    ↥(Gamma0 N)) = Gamma0MapUnits γ := by
  ext
  simp [Gamma0MapUnits_val, Gamma0Map, conjugateByJ]

private lemma mapGL_conjugateByJ (γ : SL(2, ℤ)) :
    mapGL ℝ (conjugateByJ γ) = UpperHalfPlane.J * mapGL ℝ γ * UpperHalfPlane.J := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [conjugateByJ, UpperHalfPlane.J, Matrix.GeneralLinearGroup.coe_mul,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.vecHead, Matrix.vecTail,
      Fin.sum_univ_two]

private lemma J_mul_mapGL_eq_mapGL_conjugateByJ_mul_J (γ : SL(2, ℤ)) :
    UpperHalfPlane.J * mapGL ℝ γ = mapGL ℝ (conjugateByJ γ) * UpperHalfPlane.J := by
  rw [mapGL_conjugateByJ, mul_assoc, mul_assoc, J_mul_self, mul_one]

/-- `Γ₁(N)`, viewed inside `GL(2, ℝ)`, is self-dual. -/
instance CongruenceSubgroup.isSelfDual_Gamma1_map (N : ℕ) :
    Subgroup.IsSelfDual (Γ₁ N) where
  isSelfDual := by
    rw [Subgroup.dual, Γ₁]
    ext y
    simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
      ConjAct.ofConjAct_toConjAct, map_inv, inv_inv, Subgroup.mem_map]
    constructor
    · rintro ⟨σ, hσ, hσy⟩
      refine ⟨conjugateByJ σ, (conjugateByJ_mem_Gamma1_iff (N := N) σ).mpr hσ, ?_⟩
      rw [mapGL_conjugateByJ, hσy, J_inv]
      calc
      _ = (UpperHalfPlane.J * UpperHalfPlane.J) * y * (UpperHalfPlane.J * UpperHalfPlane.J) := by group
      _ = y := by simp [J_mul_self]
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨conjugateByJ σ, (conjugateByJ_mem_Gamma1_iff (N := N) σ).mpr hσ, ?_⟩
      rw [mapGL_conjugateByJ]
      simp [J_inv]

/-- The complex conjugate of a `ℂˣ`-valued character. -/
def MonoidHom.conjChar {G : Type*} [Monoid G] (χ : G →* ℂˣ) : G →* ℂˣ :=
  (Units.map (starRingEnd ℂ).toMonoidHom).comp χ

/-- Conjugating a character twice recovers the original. -/
@[simp]
theorem MonoidHom.conjChar_conjChar {G : Type*} [Monoid G] (χ : G →* ℂˣ) :
    MonoidHom.conjChar (MonoidHom.conjChar χ) = χ := by
  ext g
  simp [MonoidHom.conjChar]

namespace ModularFormClass

/-- The dual of a modular form with nebentypus `χ` has nebentypus the conjugate character. -/
theorem dual_mem_range_modFormCharSpace_inclusion_conjChar {N : ℕ} [NeZero N] (χ : (ZMod N)ˣ →* ℂˣ)
    (f : modFormCharSpace (N := N) k χ) : ((Subgroup.IsSelfDual.isSelfDual (Γ := Γ₁ N) ▸ ModularFormClass.dual
    (f : ModularForm (Γ₁ N) k) : ModularForm (Γ₁ N) k)) ∈ modFormCharSpace (N := N) k (MonoidHom.conjChar χ) := by
  let F : ModularForm (Γ₁ N) k := (Subgroup.IsSelfDual.isSelfDual (Γ := Γ₁ N) ▸
    ModularFormClass.dual (f : ModularForm (Γ₁ N) k))
  change F ∈ modFormCharSpace (N := N) k (MonoidHom.conjChar χ)
  rw [modFormCharSpace_iff_nebentypus]
  intro γ
  let γJ : ↥(Gamma0 N) := ⟨conjugateByJ (γ : SL(2, ℤ)), conjugateByJ_mem_Gamma0 (N := N) γ.property⟩
  have hf := (modFormCharSpace_iff_nebentypus k χ (f : ModularForm (Γ₁ N) k)).mp f.property γJ
  have hF : ⇑F = ⇑(ModularFormClass.dual (f : ModularForm (Γ₁ N) k)) :=
    ModularForm.coe_cast_group _ _
  rw [hF]
  change (⇑(f : ModularForm (Γ₁ N) k) ∣[k] UpperHalfPlane.J) ∣[k]
      (mapGL ℝ (γ : SL(2, ℤ))) = (↑(MonoidHom.conjChar χ (Gamma0MapUnits γ)) : ℂ) •
      (⇑(f : ModularForm (Γ₁ N) k) ∣[k] UpperHalfPlane.J)
  rw [← SlashAction.slash_mul, J_mul_mapGL_eq_mapGL_conjugateByJ_mul_J,
    SlashAction.slash_mul, hf, Gamma0MapUnits_conjugateByJ, ModularForm.smul_slash]
  simp [MonoidHom.conjChar]

end ModularFormClass

end Nebentypus

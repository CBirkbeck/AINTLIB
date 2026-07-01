/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.MeasureTheory.Measure.Hausdorff
import LeanModularForms.HeckeRIngs.GL2.FourierHecke
import LeanModularForms.HeckeRIngs.GL2.HeckeModularForm_Gamma0
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_Gamma1
import LeanModularForms.Modularforms.PeterssonInner
import LeanModularForms.Modularforms.PeterssonLevelN

/-!
# Hecke adjoint theory: core cusp/Hecke infrastructure

This file provides the foundational infrastructure for the adjoint theory of
Hecke operators with respect to the Petersson inner product: the cusp-form
Hecke operators, the cuspidality-preservation API, the algebraic double-coset
identity, and the GL₂⁺ change-of-variables lemma `peterssonInner_slash_adjoint`.

## Main results

* `heckeT_n_cusp` — the Hecke operator `T_n` on cusp forms
* `heckeT_p_cusp` / `diamondOp_cusp` — `T_p` and `⟨d⟩` restricted to cusp forms
* `adjointGamma0Rep` / `adjointGamma1Rep` / `peterssonAdj` — adjoint representatives for
  the change of variables
* `peterssonInner_slash_adjoint` — DS Proposition 5.5.2, GL₂⁺ change of variables

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.5
* [Miy] Miyake, *Modular Forms*, §4.5 (Thm 4.5.4–4.5.5)
-/

noncomputable section

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped Pointwise MatrixGroups ModularForm

variable {k : ℤ}

namespace CuspForm

/-- Every cusp form is a modular form (zero at cusps implies bounded at cusps). -/
def toModularForm' {Γ : Subgroup (GL (Fin 2) ℝ)} (f : CuspForm Γ k) : ModularForm Γ k :=
  { f with bdd_at_cusps' := fun hc g hg ↦ (f.zero_at_cusps' hc g hg).boundedAtFilter }

end CuspForm

namespace HeckeRing.GL2

open CuspForm

variable {N : ℕ} [NeZero N]

private lemma heckeT_p_ut_zero_at_cusps (p : ℕ) (hp : 0 < p)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {c : OnePoint ℝ} (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    c.IsZeroAt (heckeT_p_ut k p hp ⇑f.toModularForm') k := by
  simp only [heckeT_p_ut]
  apply Finset.sum_induction _ (fun g ↦ c.IsZeroAt g k) (fun _ _ ha hb ↦ ha.add hb)
    ((0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k).zero_at_cusps' hc)
  intro b _
  exact OnePoint.IsZeroAt.smul_iff.mp (f.zero_at_cusps' (glMap_smul_isCusp_Gamma1 N _ hc))

private lemma heckeT_p_lower_zero_at_cusps (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {c : OnePoint ℝ} (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    c.IsZeroAt (⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f.toModularForm') ∣[k]
      (T_p_lower p hp.pos : GL (Fin 2) ℚ)) k := by
  intro γ hγ
  show UpperHalfPlane.IsZeroAtImInfty
    ((⇑((diamondOp k (ZMod.unitOfCoprime p hpN)) f.toModularForm') ∣[k]
      glMap (T_p_lower p hp.pos)) ∣[k] γ)
  rw [← SlashAction.slash_mul]
  set g := (Gamma0MapUnits_surjective (ZMod.unitOfCoprime p hpN)).choose
  change UpperHalfPlane.IsZeroAtImInfty
    ((⇑f.toModularForm' ∣[k] mapGL ℝ (g : SL(2, ℤ))) ∣[k] (glMap (T_p_lower p hp.pos) * γ))
  rw [← SlashAction.slash_mul]
  have hcusp : IsCusp (mapGL ℝ (g : SL(2, ℤ)) • glMap (T_p_lower p hp.pos) • c)
      ((Gamma1 N).map (mapGL ℝ)) :=
    Gamma1_map_conjAct_eq_forward g ▸
      (glMap_smul_isCusp_Gamma1 N _ hc).smul (mapGL ℝ (g : SL(2, ℤ)))
  apply f.zero_at_cusps' hcusp
  simp [SemigroupAction.mul_smul, hγ]

private theorem heckeT_p_zero_at_cusps (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {c : OnePoint ℝ} (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    c.IsZeroAt (heckeT_p k p hp hpN f.toModularForm').toFun k := by
  show c.IsZeroAt (heckeT_p_fun k p hp hpN f.toModularForm') k
  simpa only [heckeT_p_fun] using (heckeT_p_ut_zero_at_cusps p hp.pos f hc).add
    (heckeT_p_lower_zero_at_cusps p hp hpN f hc)

/-- `T_p` restricted to cusp forms. -/
def heckeT_p_cusp (k : ℤ) (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  { heckeT_p k p hp hpN f.toModularForm' with
    zero_at_cusps' := heckeT_p_zero_at_cusps p hp hpN f }

/-- `⟨d⟩` restricted to cusp forms. -/
def diamondOp_cusp (k : ℤ) (d : (ZMod N)ˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  diamondOpCusp k d f

private theorem heckeT_p_all_zero_at_cusps (p : ℕ) (hp : Nat.Prime p)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {c : OnePoint ℝ} (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    c.IsZeroAt ((heckeT_p_all k p hp) f.toModularForm').toFun k := by
  by_cases hpN : Nat.Coprime p N
  · rw [heckeT_p_all_coprime k hp hpN]
    exact heckeT_p_zero_at_cusps p hp hpN f hc
  · show c.IsZeroAt ⇑(heckeT_p_all k p hp f.toModularForm') k
    rw [heckeT_p_all_not_coprime_apply k hp hpN]
    exact heckeT_p_ut_zero_at_cusps p hp.pos f hc

private def PreservesCusps (T : Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) :
    Prop :=
  ∀ (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {c : OnePoint ℝ},
    IsCusp c ((Gamma1 N).map (mapGL ℝ)) → c.IsZeroAt (T f.toModularForm').toFun k

omit [NeZero N] in
private theorem preservesCusps_one :
    PreservesCusps (N := N) (k := k) 1 :=
  fun f _ hc ↦ f.zero_at_cusps' hc

private theorem preservesCusps_heckeT_p_all (p : ℕ) (hp : Nat.Prime p) :
    PreservesCusps (N := N) (heckeT_p_all k p hp) :=
  fun f _ hc ↦ heckeT_p_all_zero_at_cusps p hp f hc

private theorem preservesCusps_diamondOp_n (p : ℕ) :
    PreservesCusps (N := N) (diamondOp_n k p) := by
  intro f c hc
  by_cases h : Nat.Coprime p N
  · rw [diamondOp_n_coprime k h]
    exact (diamondOpCusp k (ZMod.unitOfCoprime p h) f).zero_at_cusps' hc
  · rw [diamondOp_n_not_coprime k h]
    exact (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k).zero_at_cusps' hc

omit [NeZero N] in
private theorem preservesCusps_mul {T₁ T₂ : Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)}
    (h₁ : PreservesCusps T₁) (h₂ : PreservesCusps T₂) : PreservesCusps (T₁ * T₂) :=
  fun f _ hc ↦ h₁ { T₂ f.toModularForm' with zero_at_cusps' := h₂ f } hc

omit [NeZero N] in
private theorem preservesCusps_sub {T₁ T₂ : Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)}
    (h₁ : PreservesCusps T₁) (h₂ : PreservesCusps T₂) : PreservesCusps (T₁ - T₂) := by
  intro f c hc
  let g₁ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
    { T₁ f.toModularForm' with zero_at_cusps' := h₁ f }
  let g₂ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
    { T₂ f.toModularForm' with zero_at_cusps' := h₂ f }
  exact (g₁ - g₂).zero_at_cusps' hc

omit [NeZero N] in
private theorem preservesCusps_smul (a : ℂ)
    {T : Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)} (hT : PreservesCusps T) :
    PreservesCusps (a • T) := by
  intro f c hc g hg
  show UpperHalfPlane.IsZeroAtImInfty ((a • (T f.toModularForm').toFun) ∣[k] g)
  rw [ModularForm.smul_slash k g (T f.toModularForm').toFun a]
  exact (hT f hc g hg).smul (UpperHalfPlane.σ g a)

private theorem preservesCusps_heckeT_ppow (p : ℕ) (hp : Nat.Prime p) (r : ℕ) :
    PreservesCusps (N := N) (heckeT_ppow k p hp r) := by
  induction r using Nat.twoStepInduction with
  | zero => exact preservesCusps_one
  | one => exact preservesCusps_heckeT_p_all p hp
  | more r ih₁ ih₂ =>
    rw [heckeT_ppow_succ_succ]
    exact preservesCusps_sub (preservesCusps_mul (preservesCusps_heckeT_p_all p hp) ih₂)
      (preservesCusps_smul _ (preservesCusps_mul (preservesCusps_diamondOp_n p) ih₁))

private theorem preservesCusps_heckeT_n (n : ℕ) [NeZero n] :
    PreservesCusps (N := N) (k := k) (heckeT_n k n) := by
  show PreservesCusps (heckeT_n_aux k n)
  induction n using Nat.strong_induction_on with
  | _ m ih =>
    rw [heckeT_n_aux]
    split_ifs with hle
    · exact preservesCusps_one
    · push Not at hle
      apply preservesCusps_mul (preservesCusps_heckeT_ppow m.minFac
        (Nat.minFac_prime (by lia)) _)
      exact ih _ (heckeT_n_unfold_lt m hle)

/-- `T_n` restricted to cusp forms. -/
def heckeT_n_cusp (k : ℤ) (n : ℕ) [NeZero n]
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  { heckeT_n k n f.toModularForm' with
    zero_at_cusps' := fun hc ↦ preservesCusps_heckeT_n n f hc }

/-- Function-level decomposition for `heckeT_n_cusp`:
`T_m f = T_{p^v}(T_{m/p^v} f)` at each point. -/
theorem heckeT_n_cusp_unfold (m : ℕ) [NeZero m] (hm : 1 < m)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (z : UpperHalfPlane) :
    let p := m.minFac
    let hp := Nat.minFac_prime (by lia : m ≠ 1)
    let v := m.factorization p
    have : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
    have : NeZero (m / p ^ v) := ⟨(Nat.div_pos (Nat.le_of_dvd (by lia)
      (Nat.ordProj_dvd m p)) (pow_pos hp.pos v)).ne'⟩
    (heckeT_n_cusp k m f) z =
      (heckeT_n_cusp k (p ^ v) (heckeT_n_cusp k (m / p ^ v) f)) z := by
  have hp' := Nat.minFac_prime (show m ≠ 1 by lia)
  haveI : NeZero (m.minFac ^ m.factorization m.minFac) := ⟨(pow_pos hp'.pos _).ne'⟩
  haveI : NeZero (m / m.minFac ^ m.factorization m.minFac) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (by lia) (Nat.ordProj_dvd m m.minFac))
      (pow_pos hp'.pos _)).ne'⟩
  show (heckeT_n_aux k m f.toModularForm').toFun z =
    (heckeT_n_aux k _ (heckeT_n_aux k _ f.toModularForm')).toFun z
  rw [heckeT_n_aux, dif_neg (not_le.mpr hm), Module.End.mul_apply]
  conv_lhs => rw [show heckeT_ppow (N := N) k m.minFac hp' (m.factorization m.minFac) =
      heckeT_n_aux k (m.minFac ^ m.factorization m.minFac) from
    (heckeT_n_prime_pow k hp' _
      (hp'.factorization_pos_of_dvd (by lia) (Nat.minFac_dvd m))).symm]

@[simp]
theorem heckeT_n_cusp_toModularForm' (n : ℕ) [NeZero n]
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (heckeT_n_cusp k n f).toModularForm' = heckeT_n k n f.toModularForm' :=
  DFunLike.ext _ _ fun _ ↦ rfl

variable (N) in
/-- `heckeT_n` decomposes into prime-power * quotient, with explicit arguments. -/
theorem heckeT_n_mul_ppow_quot [NeZero N] (m : ℕ) [NeZero m] (hm : 1 < m)
    (p : ℕ) (hp : Nat.Prime p)
    (hmp : p = m.minFac) (v : ℕ) (hmv : v = m.factorization p)
    (hv_pos : 0 < v) (hdiv_pos : 0 < m / p ^ v) :
    haveI : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
    haveI : NeZero (m / p ^ v) := ⟨hdiv_pos.ne'⟩
    heckeT_n (N := N) k m =
      heckeT_n (N := N) k (p ^ v) *
        heckeT_n (N := N) k (m / p ^ v) := by
  haveI : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
  haveI : NeZero (m / p ^ v) := ⟨hdiv_pos.ne'⟩
  subst hmp hmv
  simp only [heckeT_n_unfold (N := N) k m hm]
  congr 1
  exact (heckeT_n_prime_pow k hp _
    (hp.factorization_pos_of_dvd (by lia) (Nat.minFac_dvd m))).symm

private lemma coprime_bezout_aux {p N : ℕ} (hpN : Nat.Coprime p N) :
    (1 : ℤ) = p * Int.gcdA p N + N * Int.gcdB p N := by
  simpa [Int.gcd_natCast_natCast, hpN.gcd_eq_one] using Int.gcd_eq_gcd_ab (p : ℤ) N

/-- A representative `γ₀ ∈ Γ₀(N)` whose `(0,0)`-entry is `p`, used as the adjoint
representative for `⟨d⟩` in the slash formulation. -/
noncomputable def adjointGamma0Rep (p N : ℕ) (hpN : Nat.Coprime p N) : ↥(Gamma0 N) :=
  let m := Int.gcdA p N
  let n := -(Int.gcdB p N)
  ⟨⟨!![(p : ℤ), n; (N : ℤ), m], by
      have hbez := coprime_bezout_aux hpN
      simp only [Matrix.det_fin_two_of]
      linarith⟩, by
      rw [Gamma0_mem]
      simp⟩

/-- The mod-`N` unit attached to `adjointGamma0Rep` is `(unitOfCoprime p)⁻¹`. -/
lemma adjointGamma0Rep_units (p N : ℕ) (hpN : Nat.Coprime p N) [NeZero N] :
    Gamma0MapUnits (adjointGamma0Rep p N hpN) = (ZMod.unitOfCoprime p hpN)⁻¹ := by
  have hmod : (Int.gcdA (↑p) (↑N) : ZMod N) * (p : ZMod N) = 1 := by
    have h := congr_arg (Int.cast : ℤ → ZMod N) (coprime_bezout_aux hpN)
    push_cast at h
    simpa [mul_comm] using h.symm
  rw [eq_comm, inv_eq_of_mul_eq_one_left]
  ext
  simpa [Gamma0MapUnits_val, adjointGamma0Rep, Gamma0Map] using hmod

/-- A representative `γ₁ ∈ Γ₁(N)` paired with `adjointGamma0Rep` for the slash
formulation of the adjoint identity. -/
noncomputable def adjointGamma1Rep (p N : ℕ) (hpN : Nat.Coprime p N) : SL(2, ℤ) :=
  let a := Int.gcdA p N
  let b := Int.gcdB p N
  ⟨!![(p : ℤ) * a, b; -(N : ℤ), 1], by
    have hbez := coprime_bezout_aux hpN
    simp only [Matrix.det_fin_two_of]
    linarith⟩

/-- `adjointGamma1Rep p N hpN` belongs to `Γ₁(N)`. -/
lemma adjointGamma1Rep_mem_Gamma1 (p N : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    adjointGamma1Rep p N hpN ∈ Gamma1 N := by
  rw [Gamma1_mem]
  refine ⟨?_, by simp [adjointGamma1Rep], by simp [adjointGamma1Rep]⟩
  show (((adjointGamma1Rep p N hpN).val 0 0 : ℤ) : ZMod N) = 1
  unfold adjointGamma1Rep
  have h : ((p : ℤ) * Int.gcdA p N + Int.gcdB p N * N : ZMod N) = 1 := by
    have hb := congr_arg (Int.cast : ℤ → ZMod N) (coprime_bezout_aux hpN)
    push_cast [ZMod.natCast_self] at hb ⊢
    linear_combination -hb
  simpa [ZMod.natCast_self] using h

section PeterssonAdjoint

open UpperHalfPlane MeasureTheory

/-- The "Petersson adjoint" of a GL₂(ℝ) element: `α† = det(α) · α⁻¹ = adjugate(α)`. -/
noncomputable def peterssonAdj (α : GL (Fin 2) ℝ) : GL (Fin 2) ℝ :=
  .mkOfDetNeZero (α : Matrix (Fin 2) (Fin 2) ℝ).adjugate (by
    rw [Matrix.det_adjugate]
    exact pow_ne_zero _ α.det_ne_zero)

/-- Coercion: `peterssonAdj α` as a matrix equals the adjugate of `α`. -/
lemma peterssonAdj_coe (α : GL (Fin 2) ℝ) :
    (peterssonAdj α : Matrix (Fin 2) (Fin 2) ℝ) =
      (α : Matrix (Fin 2) (Fin 2) ℝ).adjugate := rfl

/-- `det(peterssonAdj α) = det(α)` for 2×2 matrices (since det(adjugate) = det^{n-1}). -/
lemma peterssonAdj_det (α : GL (Fin 2) ℝ) :
    (peterssonAdj α).det = α.det :=
  Units.ext <| by simp [peterssonAdj_coe, Matrix.det_adjugate]

/-- `peterssonAdj` reverses products: `(αβ)† = β† · α†`. -/
lemma peterssonAdj_mul (α β : GL (Fin 2) ℝ) :
    peterssonAdj (α * β) = peterssonAdj β * peterssonAdj α :=
  Units.ext <| by simp [peterssonAdj_coe, Matrix.adjugate_mul_distrib]

/-- For an SL(2, ℤ) element cast to GL(2, ℝ), the `peterssonAdj` equals the group inverse.
Since SL elements have determinant 1, their adjugate equals their inverse. -/
lemma peterssonAdj_mapGL_SL_eq_inv (q : SL(2, ℤ)) :
    peterssonAdj ((mapGL ℝ q : GL (Fin 2) ℝ)) = (mapGL ℝ q : GL (Fin 2) ℝ)⁻¹ := by
  apply Units.ext
  rw [peterssonAdj_coe, Matrix.coe_units_inv]
  have hdet : (mapGL ℝ q : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, det_mapGL, Units.val_one]
  rw [Matrix.inv_def, Ring.inverse_eq_inv', hdet, inv_one, one_smul]

private lemma GL_inv_entry (α : GL (Fin 2) ℝ) (i j : Fin 2) :
    (α⁻¹ : GL (Fin 2) ℝ) i j = (α.det.val)⁻¹ * (α : Matrix (Fin 2) (Fin 2) ℝ).adjugate i j := by
  show (↑α⁻¹ : Matrix _ _ ℝ) i j = _
  rw [Matrix.coe_units_inv α, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply,
    smul_eq_mul, Matrix.GeneralLinearGroup.val_det_apply]

private lemma peterssonAdj_entry (α : GL (Fin 2) ℝ) (i j : Fin 2) :
    (peterssonAdj α : Matrix _ _ ℝ) i j = (α : Matrix (Fin 2) (Fin 2) ℝ).adjugate i j :=
  congrFun (congrFun (peterssonAdj_coe α) i) j

private lemma peterssonAdj_denom (α : GL (Fin 2) ℝ) (τ : ℍ) :
    UpperHalfPlane.denom (peterssonAdj α) τ = ↑(α.det.val) * UpperHalfPlane.denom α⁻¹ τ := by
  have hdet_ne : (α.det.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Units.ne_zero α.det)
  simp only [denom, peterssonAdj_entry, GL_inv_entry]
  push_cast
  field_simp

private lemma σ_peterssonAdj (α : GL (Fin 2) ℝ) : σ (peterssonAdj α) = σ α⁻¹ := by
  have hdet2 : (α⁻¹).det.val = (α.det.val)⁻¹ := by
    rw [show (α⁻¹).det = α.det⁻¹ from map_inv (Matrix.GeneralLinearGroup.det) α]
    exact Units.val_inv_eq_inv_val _
  simp only [σ, congr_arg Units.val (peterssonAdj_det α), hdet2, inv_pos]

/-- `α†` and `α⁻¹` induce the same Möbius action on the upper half-plane. -/
lemma peterssonAdj_smul_eq (α : GL (Fin 2) ℝ) (τ : ℍ) :
    (peterssonAdj α) • τ = α⁻¹ • τ := by
  have hdet_ne : (α.det.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Units.ne_zero α.det)
  have hnum : num (peterssonAdj α) (τ : ℂ) = ↑α.det.val * num α⁻¹ (τ : ℂ) := by
    simp only [num, peterssonAdj_entry, GL_inv_entry]
    push_cast
    field_simp
  ext1
  simp only [coe_smul, σ_peterssonAdj]
  congr 1
  rw [hnum, peterssonAdj_denom, mul_div_mul_left _ _ hdet_ne]

/-- Pointwise: `g ∣[k] peterssonAdj α = |det α|^{k-2} • (g ∣[k] α⁻¹)`. -/
lemma slash_peterssonAdj_eq (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val) (g : ℍ → ℂ) :
    g ∣[k] peterssonAdj α = (↑(|α.det.val| ^ (k - 2)) : ℂ) • (g ∣[k] α⁻¹) := by
  have habs : |α.det.val| = α.det.val := abs_of_pos hα
  have hdet_eq : (peterssonAdj α).det.val = α.det.val := congr_arg Units.val (peterssonAdj_det α)
  have hdet_inv_abs : |(α⁻¹).det.val| = (α.det.val)⁻¹ := by
    rw [show (α⁻¹).det = α.det⁻¹ from map_inv (Matrix.GeneralLinearGroup.det) α,
      Units.val_inv_eq_inv_val, abs_inv, habs]
  ext τ
  simp only [ModularForm.slash_apply, Pi.smul_apply, smul_eq_mul, peterssonAdj_smul_eq,
    σ_peterssonAdj, hdet_eq, peterssonAdj_denom, mul_zpow, hdet_inv_abs, habs]
  have hcd : (α.det.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hα)
  push_cast
  rw [inv_zpow']
  have h1 : (α.det.val : ℂ) ^ (k - 1) * (α.det.val : ℂ) ^ (-k) =
      (α.det.val : ℂ) ^ (k - 2) * (α.det.val : ℂ) ^ (-(k - 1)) := by
    rw [← zpow_add₀ hcd, ← zpow_add₀ hcd, show k - 1 + -k = k - 2 + -(k - 1) by ring]
  linear_combination σ α⁻¹ (g (α⁻¹ • τ)) * denom α⁻¹ (↑τ : ℂ) ^ (-k) * h1

/-- **GL₂⁺ Petersson adjoint** (DS Proposition 5.5.2a):
For `α ∈ GL(2,ℝ)` with `det(α) > 0`, and any measurable set `D ⊆ ℍ`:
```
peterssonInner k D (f∣[k]α) g = peterssonInner k (α • D) f (g∣[k] adjugate(α))
``` -/
theorem peterssonInner_slash_adjoint (D : Set ℍ) (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val)
    (f g : ℍ → ℂ) :
    peterssonInner k D (f ∣[k] α) g =
      peterssonInner k (α • D) f (g ∣[k] peterssonAdj α) := by
  have hg_decomp : g = (g ∣[k] α⁻¹) ∣[k] α := by
    rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]
  simp only [peterssonInner]
  set g' := g ∣[k] α⁻¹
  have h_eq : ∀ τ, petersson k (f ∣[k] α) g τ =
      ↑|α.det.val| ^ (k - 2) * petersson k f g' (α • τ) := by
    intro τ
    rw [hg_decomp, petersson_slash,
      show σ α = ContinuousAlgEquiv.refl ℝ ℂ by simp only [σ, hα, ↓reduceIte],
      ContinuousAlgEquiv.refl_apply]
  simp_rw [h_eq]
  symm
  have hpet_adj : ∀ τ, petersson k f (g ∣[k] peterssonAdj α) τ =
      ↑|α.det.val| ^ (k - 2) * petersson k f g' τ := by
    intro τ
    rw [slash_peterssonAdj_eq α hα g]
    simp [petersson, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hpet_adj]
  set α' : GL(2, ℝ)⁺ := ⟨α, hα⟩
  rw [show α • D = (fun τ ↦ α' • τ) '' D by rw [Set.image_smul]; rfl]
  exact (measurePreserving_smul α' μ_hyp).setIntegral_image_emb
    (measurableEmbedding_const_smul α') _ D

end PeterssonAdjoint

end HeckeRing.GL2

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.AdjointTheory.DeltaBSystem

/-!
# Hecke adjoint theory: concrete `Option (Fin p)` projective T_p tile family.

Fifth module of the split of `AdjointTheoryPetersson`. Covers the Phase E3
concrete `Option (Fin p)` projective T_p tile family and the resulting
symmetric-form adjoint identity for `petN`.
-/

noncomputable section

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped Pointwise MatrixGroups ModularForm

variable {k : ℤ}

namespace HeckeRing.GL2

open CuspForm

variable {N : ℕ} [NeZero N]

section ProjectiveTpFamily

variable (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
include hp hpN

/-- **Phase E3 — rational `Option (Fin p)` T_p tile family.** -/
noncomputable def α_T_p_Q : Option (Fin p) → GL (Fin 2) ℚ
  | none => M_infty N p hp.pos hpN
  | some b => T_p_upper p hp.pos b.val

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase E3 — concrete `Option (Fin p)` T_p tile family in `GL(2, ℝ)⁺`.** -/
noncomputable def α_T_p_GLPos : Option (Fin p) → GL(2, ℝ)⁺
  | none => ⟨glMap (M_infty N p hp.pos hpN), glMap_M_infty_det_pos N p hp.pos hpN⟩
  | some b => ⟨glMap (T_p_upper p hp.pos b.val), glMap_T_p_upper_det_pos p hp.pos b.val⟩

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase E3 — concrete `Option (Fin p)` T_p tile family in `PSL(2, ℝ)`.** -/
noncomputable def α_T_p_PSL_R : Option (Fin p) → PSL(2, ℝ) :=
  fun i ↦ GLPos_to_PSL_R_term (α_T_p_GLPos p hp hpN i)

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase E4 — set-level transfer from `α_T_p_PSL_R` to `α_T_p_GLPos`.** -/
theorem α_T_p_PSL_R_smul_set (i : Option (Fin p)) (S : Set ℍ) :
    (α_T_p_PSL_R p hp hpN i • S : Set ℍ) =
      ((α_T_p_GLPos p hp hpN i : GL(2, ℝ)⁺) • S : Set ℍ) :=
  GLPos_to_PSL_R_term_smul_set _ _

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase E4 — set-level transfer from `α_T_p_GLPos` to underlying matrix.** -/
theorem α_T_p_GLPos_smul_set_val (i : Option (Fin p)) (S : Set ℍ) :
    ((α_T_p_GLPos p hp hpN i : GL(2, ℝ)⁺) • S : Set ℍ) =
      (((α_T_p_GLPos p hp hpN i : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) • S : Set ℍ) :=
  rfl

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase E4 — set-level match form for `α_T_p_PSL_R i • S`.** -/
theorem α_T_p_PSL_R_smul_set_eq_match_GL (i : Option (Fin p)) (S : Set ℍ) :
    (α_T_p_PSL_R p hp hpN i • S : Set ℍ) =
      ((match i with
        | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
        | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
            S : Set ℍ) := by
  rw [α_T_p_PSL_R_smul_set, α_T_p_GLPos_smul_set_val]
  cases i <;> rfl

end ProjectiveTpFamily

section TpHecke

variable (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
variable (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)

include hp hpN in
open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD
    (hm : ∀ i ∈ (Finset.univ : Finset (Option (Fin p))),
      NullMeasurableSet ((match i with
        | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
        | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
        (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp)
    (h_int_per : ∀ i ∈ (Finset.univ : Finset (Option (Fin p))),
      IntegrableOn (fun τ ↦ petersson k ⇑g
        (⇑f ∣[k] (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ))) τ)
        (Gamma1_fundDomain_PSL N) μ_hyp)
    (hfi : IntegrableOn (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp) :
    peterssonInner k (Gamma1_fundDomain_PSL N)
      (∑ i ∈ (Finset.univ : Finset (Option (Fin p))),
        ⇑f ∣[k] (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ))) ⇑g =
    peterssonInner k
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ))
      ⇑f
      (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) := by
  let α : Option (Fin p) → GL (Fin 2) ℝ := fun i ↦ match i with
    | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
    | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)
  have hset_eq : (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        α i • (Gamma1_fundDomain_PSL N : Set ℍ)) =
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ)) :=
    Set.iUnion_congr fun i ↦ Set.iUnion_congr fun _ ↦ by cases i <;> rfl
  have hfi_compact : IntegrableOn (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        α i • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp := by
    rw [hset_eq]; exact hfi
  have hmain : peterssonInner k (Gamma1_fundDomain_PSL N)
      (∑ i ∈ (Finset.univ : Finset (Option (Fin p))), ⇑f ∣[k] α i) ⇑g =
    peterssonInner k
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        α i • (Gamma1_fundDomain_PSL N : Set ℍ))
      ⇑f
      (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) := by
    apply peterssonInner_T_p_family_sum_slashes_eq_aggregate_of_integrable
      (s := Finset.univ) (α := α) (f := f) (g := g)
      (g' := ⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ))
    · intro i _
      cases i with
      | none => exact glMap_M_infty_det_pos N p hp.pos hpN
      | some b => exact glMap_T_p_upper_det_pos p hp.pos b.val
    · intro i _
      cases i with
      | none => exact slash_peterssonAdj_glMap_M_infty_eq_slash_T_p_lower p hp hpN g
      | some b => exact slash_peterssonAdj_glMap_T_p_upper_eq_slash_T_p_lower p hp.pos b.val g
    · exact hm
    · exact aedisjoint_pairwise_T_p_family p hp hpN
    · exact h_int_per
    · exact hfi_compact
  rw [← hset_eq]
  exact hmain

include hp hpN in
open UpperHalfPlane ModularGroup MeasureTheory in
/-- **CORRECTED leaf 1** — LHS to the proven global aggregate's LHS.
`petN(T_p f, g) = c_N • ⟨Γ₁-FD⟩ (Σᵢ f∣β_i) g`, where `β_i` ranges over the full Hecke
family `{M_∞} ⊔ {T_p_upper b}` (DS: `Σᵢ f∣β_i = f[ΓαΓ]_k = T_p f`), and
`c_N = slToPslQuot_fiberCard N`. The fiber-count factor is forced because `petN` is the
integral over the *SL*-coset fundamental domain (`[SL:Γ₁(N)]` tiles), while
`peterssonInner k (Gamma1_fundDomain_PSL N)` is the integral over the *PSL*-coset
fundamental domain (`[PSL:imageΓ₁(N)]` tiles), the two differing by the uniform fiber
count `c_N = [SL/Γ₁ : PSL/imageΓ₁]` (`= 1` iff `-I ∈ Γ₁(N)`). The aggregate identity at
line 202 is at the PSL level (fiber-count-free) on both sides, so the `c_N •` carried here
cancels the matching `c_N •` of leaf 2.
Route (BUILD, bounded): `petN_eq_setIntegral_Gamma1_fundDomain_PSL` (the `c_N • ∫_{D₁}`
form of `petN`) + `heckeT_p_fun_eq_coset_sum` (the family-sum form of `T_p`). -/
private theorem petN_heckeT_p_LHS_eq_aggregate :
    petN (heckeT_p_cusp k p hp hpN f) g =
    slToPslQuot_fiberCard N • peterssonInner k (Gamma1_fundDomain_PSL N)
      (∑ i ∈ (Finset.univ : Finset (Option (Fin p))),
        ⇑f ∣[k] (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ))) ⇑g := by
  have h_fun : (⇑(heckeT_p_cusp k p hp hpN f) : ℍ → ℂ) =
      ∑ i ∈ (Finset.univ : Finset (Option (Fin p))),
        ⇑f ∣[k] (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) := by
    have h_Tpf : (⇑(heckeT_p_cusp k p hp hpN f) : ℍ → ℂ) =
        heckeT_p_ut k p hp.pos ⇑f.toModularForm' +
          ⇑f.toModularForm' ∣[k] (M_infty N p hp.pos hpN : GL (Fin 2) ℚ) :=
      heckeT_p_fun_eq_coset_sum k hp hpN f.toModularForm'
    rw [Fintype.sum_option, h_Tpf, add_comm]
    refine congr_arg₂ (· + ·) rfl ?_
    rw [show heckeT_p_ut k p hp.pos ⇑f.toModularForm' =
        ∑ b ∈ Finset.range p,
          ⇑f.toModularForm' ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ) from rfl,
      ← Fin.sum_univ_eq_sum_range
        (fun b ↦ ⇑f.toModularForm' ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ))]
    rfl
  rw [petN_eq_setIntegral_Gamma1_fundDomain_PSL, peterssonInner, h_fun]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The `β • Γ₁`-PSL-FD set is null-measurable whenever `β` has positive `GL(2,ℝ)`
determinant, via the `β⁻¹`-pullback of the `Γ₁(N)` FD (a measure-preserving map). -/
private lemma nullMeasurableSet_glPos_smul_Gamma1_fundDomain_PSL
    {β : GL (Fin 2) ℝ} (hβ : 0 < β.det.val) :
    NullMeasurableSet (β • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp := by
  have hinv : 0 < (β⁻¹).det.val := by
    rw [map_inv, Units.val_inv_eq_inv_val]; exact inv_pos.mpr hβ
  have h_eq : (β • (Gamma1_fundDomain_PSL N : Set ℍ)) =
      ((β⁻¹ • ·) : ℍ → ℍ) ⁻¹' (Gamma1_fundDomain_PSL N : Set ℍ) := by
    ext τ; simp [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
  rw [h_eq]
  exact isFundamentalDomain_Gamma1_PSL.nullMeasurableSet.preimage
    (measurePreserving_glPos_smul _ hinv).quasiMeasurePreserving

include hp hpN in
open UpperHalfPlane ModularGroup MeasureTheory in
/-- The `α_T_p` family aggregate has finite hyperbolic measure: each tile
`β_i • Γ₁-FD` has finite measure (via `measure_glPos_smul_Gamma1_fundDomain_lt_top`)
and the family is finite. -/
private lemma measure_α_T_p_family_aggregate_lt_top :
    μ_hyp (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
      (match i with
        | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
        | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
        (Gamma1_fundDomain_PSL N : Set ℍ)) < ⊤ := by
  simp only [Finset.mem_univ, Set.iUnion_true]
  refine (measure_iUnion_le _).trans_lt ?_
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.mpr fun i _ ↦ measure_glPos_smul_Gamma1_fundDomain_lt_top _ ?_
  cases i with
  | none => exact glMap_M_infty_det_pos N p hp.pos hpN
  | some b => exact glMap_T_p_upper_det_pos p hp.pos b.val

include hp hpN in
open UpperHalfPlane ModularGroup MeasureTheory in
/-- **CORRECTED leaf 3** — the family-aggregate measure hypotheses for invoking the proven
`peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD`: per-`i`
`NullMeasurableSet` of each `β_i•Γ₁-FD`, per-`i` `IntegrableOn` of the swapped kernel on
`Γ₁-FD`, and `IntegrableOn` of the forward kernel on the family `iUnion`.
Route (BUILD, bounded): `nullMeasurableSet`/`integrableOn` engines already used at
DeltaBSystem:1666–1736 and the `Γ_p(α)`/PSL fundamental-domain measurability of FDTransport. -/
private theorem aggregate_HeckeFD_measure_hyps :
    (∀ i ∈ (Finset.univ : Finset (Option (Fin p))),
      NullMeasurableSet ((match i with
        | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
        | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
        (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp) ∧
    (∀ i ∈ (Finset.univ : Finset (Option (Fin p))),
      IntegrableOn (fun τ ↦ petersson k ⇑g
        (⇑f ∣[k] (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ))) τ)
        (Gamma1_fundDomain_PSL N) μ_hyp) ∧
    IntegrableOn (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp := by
  refine ⟨?_, ?_, ?_⟩
  · refine fun i _ ↦ nullMeasurableSet_glPos_smul_Gamma1_fundDomain_PSL ?_
    cases i with
    | none => exact glMap_M_infty_det_pos N p hp.pos hpN
    | some b => exact glMap_T_p_upper_det_pos p hp.pos b.val
  · intro i _
    cases i with
    | none =>
      exact integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure g f
        (M_infty N p hp.pos hpN)
        (hyperbolicMeasure_Gamma1_fundDomain_PSL_lt_top (N := N))
    | some b =>
      exact integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure g f
        (T_p_upper p hp.pos b.val)
        (hyperbolicMeasure_Gamma1_fundDomain_PSL_lt_top (N := N))
  · exact integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure f g
      (T_p_lower p hp.pos) (measure_α_T_p_family_aggregate_lt_top p hp hpN)

/-- `glMap (T_p_lower p hp) = (T_p_lower p hp).map (Rat.castHom ℝ)` (the `glMap`/`.map`
identification connecting the residual's slash matrix `A = diag(p,1)` to the `Γ_p(α)` API,
which is phrased over `α.map (Rat.castHom ℝ)`). -/
private lemma glMap_T_p_lower_eq_map_castHom (p : ℕ) (hp : 0 < p) :
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) =
      ((T_p_lower p hp).map (Rat.castHom ℝ) : GL (Fin 2) ℝ) := rfl

include hp in
open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane ModularGroup MeasureTheory in
/-- **Γ_p(A)-invariance of the W5b integrand.** For `A = diag(p,1)`, the kernel
`pet f (g∣A)` is invariant under the (SL-level) action of `Γ_p(A) = A⁻¹Γ₁A ∩ Γ₁`: `f` is
`Γ₁`-invariant hence `Γ_p(A)`-invariant, and `g∣A` is `Γ_p(A)`-invariant
(`slash_α_Gamma_p_α_invariant_cuspForm`, FDT:152). -/
private lemma petersson_f_slash_T_p_lower_Gamma_p_invariant
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos)) (τ : ℍ) :
    petersson k ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) (γ • τ) =
      petersson k ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ := by
  rw [← petersson_slash_SL]
  congr 1
  · exact slash_Gamma1_eq f γ ((Gamma_p_α_le_Gamma1 _) hγ)
  · rw [ModularForm.SL_slash, glMap_T_p_lower_eq_map_castHom]
    exact slash_α_Gamma_p_α_invariant_cuspForm (T_p_lower p hp.pos) g hγ

include hp hpN in
open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane ModularGroup MeasureTheory in
/-- **W5b — the FD transfer (the consumable for W5c).** GIVEN the fundamental-domain
property of the Hecke aggregate domain `D = ⋃_i β_i • Γ₁-FD` for `Γ_p(A) = A⁻¹Γ₁A ∩ Γ₁`
(`A = diag(p,1)`), the Petersson integral over `D` transfers to the integral over the
canonical `Γ_p(A)` fundamental domain `Gamma_p_α_fundDomain_PSL A`:
```
⟨D⟩ f (g∣A) = ∫_{Γ_p(A)-FD} pet f (g∣A).
```
Both are FDs for the **same** group `(Γ_p(A)).map SL2Z_to_PSL2R` (the latter via FDT:860),
and the integrand `pet f (g∣A)` is `Γ_p(A)`-invariant
(`petersson_f_slash_T_p_lower_Gamma_p_invariant`), so the two integrals coincide by
`IsFundamentalDomain.setIntegral_eq`. This is the exact form the trace engine FDT:1612
consumes: it puts `⟨D⟩ f (g∣A)` into `∫_{Γ_p(A)-FD}` shape, where the engine fires.

The hypothesis `hFD` is the residual **W5a-2 crux** — that the `p+1` det-`p` Hecke tiles
`β_i • Γ₁-FD` tile `Γ_p(A)\ℍ` (the covering/transversal half; the AE-disjoint half is
`aedisjoint_pairwise_T_p_family`, SA:1431, and the index is `p+1` via
`slGamma_p_αToGamma1_fiberCard_T_p_lower`). See the HARD-STOP note on
`heckeT_p_aggregate_peeled_diagonal_balance`. -/
theorem aggregate_D_petersson_eq_Gamma_p_A_fundDomain
    (hFD : IsFundamentalDomain
      (((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R))
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ))
      μ_hyp) :
    peterssonInner k
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ))
      ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) =
    ∫ τ in Gamma_p_α_fundDomain_PSL (N := N) (T_p_lower p hp.pos),
      petersson k ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ ∂μ_hyp := by
  rw [peterssonInner]
  refine hFD.setIntegral_eq
    (isFundamentalDomain_Gamma_p_α_fundDomain_PSL_at_PSL_R (N := N) (T_p_lower p hp.pos))
    (fun gp τ ↦ ?_)
  exact inv_under_Gamma_p_α_PSL_R_of_inv_under_Gamma_p_α (N := N) (T_p_lower p hp.pos)
    (fun γ hγ τ ↦ petersson_f_slash_T_p_lower_Gamma_p_invariant p hp f g hγ τ) gp τ

include hp hpN in
open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory in
/-- **`hFD` discharged.** The fundamental-domain hypothesis of
`aggregate_D_petersson_eq_Gamma_p_A_fundDomain` is exactly the W5a-2 Hecke-tile FD
identification `isFundamentalDomain_Hecke_tiles_Gamma_p_α` (DeltaBSystem), modulo the
`⋃ i ∈ univ ↔ ⋃ i` biUnion/iUnion reshape. -/
theorem isFundamentalDomain_Hecke_tiles_biUnion_Gamma_p_α :
    IsFundamentalDomain
      (((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R))
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ))
      μ_hyp := by
  have hset : (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
      (match i with
        | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
        | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
        (Gamma1_fundDomain_PSL N : Set ℍ)) =
      (⋃ i : Option (Fin p),
        (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ)) := by
    refine Set.iUnion_congr fun i ↦ ?_
    cases i <;> simp
  rw [hset]
  exact isFundamentalDomain_Hecke_tiles_Gamma_p_α p hp hpN

include hp hpN in
/-- Center elements of `SL(2,ℤ)` have lower-left entry `0`, so `Γ_p(A)`- and `Γ₁`-membership
agree on the center (used for the fiber-count reconciliation). -/
private theorem center_mem_Gamma_p_α_T_p_lower_iff_mem_Gamma1
    {z : SL(2, ℤ)} (hz : z ∈ Subgroup.center SL(2, ℤ)) :
    z ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos) ↔ z ∈ Gamma1 N := by
  rw [mem_Gamma_p_α_T_p_lower p hp.pos hpN]
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_⟩⟩
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hz
  obtain ⟨c, _, hc⟩ := hz
  have : (z : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by
    rw [← hc, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide)]
  rw [this]; exact dvd_zero _

/-- Fiber-membership characterization at `[1]` (uniform across any congruence subgroup
`H ≤ SL(2,ℤ)`): the double PSL-quotient lands at the identity iff there is a central
representative `z` with `g * z ∈ H`. -/
private theorem pslQuot_eq_one_iff_exists_center_mem
    (H : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) :
    (QuotientGroup.mk (QuotientGroup.mk g : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ (H.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))))) =
      QuotientGroup.mk 1 ↔
    ∃ z ∈ Subgroup.center SL(2, ℤ), g * z ∈ H := by
  rw [QuotientGroup.eq, mul_one, Subgroup.inv_mem_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, hhe⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hhe
    refine ⟨g⁻¹ * h, ?_, by group; exact hh⟩
    have := (Subgroup.center SL(2, ℤ)).inv_mem hhe
    rwa [mul_inv_rev, inv_inv] at this
  · rintro ⟨z, hz, hgz⟩
    exact ⟨g * z, hgz, by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff _).mpr hz, mul_one]⟩

include hp hpN in
/-- Center crux: for `g₁, g₂` whose `Γ_p(A)`-fiber membership holds
(`gᵢ·zᵢ ∈ Γ_p(A)`, `zᵢ ∈ center`), the `Γ₁`- and `Γ_p(A)`-cosets of `g₁⁻¹g₂` coincide
(the discrepancy lies in the center, where the two memberships agree by
`center_mem_Gamma_p_α_T_p_lower_iff_mem_Gamma1`). -/
private theorem Gamma1_coset_iff_Gamma_p_α_coset_of_center_fiber
    (g₁ g₂ z₁ z₂ : SL(2, ℤ))
    (hz₁ : z₁ ∈ Subgroup.center SL(2, ℤ))
    (hz₂ : z₂ ∈ Subgroup.center SL(2, ℤ))
    (hg₁ : g₁ * z₁ ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos))
    (hg₂ : g₂ * z₂ ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos)) :
    g₁⁻¹ * g₂ ∈ Gamma1 N ↔ g₁⁻¹ * g₂ ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos) := by
  have hzc : z₁ * z₂⁻¹ ∈ Subgroup.center SL(2, ℤ) :=
    (Subgroup.center SL(2, ℤ)).mul_mem hz₁ ((Subgroup.center SL(2, ℤ)).inv_mem hz₂)
  have hcz₁ : ∀ x : SL(2, ℤ), z₁⁻¹ * x = x * z₁⁻¹ := fun x ↦
    (Subgroup.mem_center_iff.mp ((Subgroup.center SL(2, ℤ)).inv_mem hz₁) x).symm
  have hcz₂ : ∀ x : SL(2, ℤ), z₂⁻¹ * x = x * z₂⁻¹ := fun x ↦
    (Subgroup.mem_center_iff.mp ((Subgroup.center SL(2, ℤ)).inv_mem hz₂) x).symm
  have hsplit : g₁⁻¹ * g₂ = (g₁ * z₁)⁻¹ * ((z₁ * z₂⁻¹) * (g₂ * z₂)) := by
    rw [mul_inv_rev]
    symm
    calc (z₁⁻¹ * g₁⁻¹) * ((z₁ * z₂⁻¹) * (g₂ * z₂))
        = g₁⁻¹ * z₁⁻¹ * (z₁ * (z₂⁻¹ * (g₂ * z₂))) := by rw [hcz₁ g₁⁻¹]; group
      _ = g₁⁻¹ * (z₂⁻¹ * (g₂ * z₂)) := by rw [← mul_assoc, mul_assoc _ z₁⁻¹ z₁,
          inv_mul_cancel, mul_one]
      _ = g₁⁻¹ * (g₂ * (z₂⁻¹ * z₂)) := by rw [hcz₂ (g₂ * z₂)]; group
      _ = g₁⁻¹ * g₂ := by rw [inv_mul_cancel, mul_one]
  rw [hsplit]
  have hL₁ : (g₁ * z₁)⁻¹ ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos) :=
    (Gamma_p_α (N := N) (T_p_lower p hp.pos)).inv_mem hg₁
  refine ⟨fun h ↦ ?_, fun h ↦ (Gamma_p_α_le_Gamma1 _) h⟩
  have hmid : (z₁ * z₂⁻¹) * (g₂ * z₂) ∈ Gamma1 N := by
    have h2 := (Gamma1 N).mul_mem ((Gamma_p_α_le_Gamma1 _) hg₁) h
    rwa [← mul_assoc, mul_inv_cancel, one_mul] at h2
  have hz_mem : z₁ * z₂⁻¹ ∈ Gamma1 N := by
    have h2 := (Gamma1 N).mul_mem hmid ((Gamma1 N).inv_mem ((Gamma_p_α_le_Gamma1 _) hg₂))
    rwa [mul_assoc, mul_inv_cancel, mul_one] at h2
  have hz_memP : z₁ * z₂⁻¹ ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos) :=
    (center_mem_Gamma_p_α_T_p_lower_iff_mem_Gamma1 p hp hpN hzc).mpr hz_mem
  exact (Gamma_p_α (N := N) (T_p_lower p hp.pos)).mul_mem hL₁
    ((Gamma_p_α (N := N) (T_p_lower p hp.pos)).mul_mem hz_memP hg₂)

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory in
/-- The map `slGamma_p_αToGamma1 (T_p_lower)` sends the `Γ_p(A)`-fiber of `[1]` into the
`Γ₁`-fiber of `[1]`: a `Γ_p(A)`-fiber witness `z ∈ center, g·z ∈ Γ_p(A)` maps to the same
`z` with `g·z ∈ Γ₁(N)` via `Gamma_p_α_le_Gamma1`. -/
private theorem slGamma_p_αToGamma1_maps_into_Gamma1_fiber
    (p : ℕ) (hp : Nat.Prime p) (_hpN : Nat.Coprime p N)
    (q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp.pos))
    (hq : slToPslQuot_Gamma_p_α (N := N) (T_p_lower p hp.pos) q =
      (QuotientGroup.mk (1 : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) (T_p_lower p hp.pos))) :
    slToPslQuot (N := N) (slGamma_p_αToGamma1 (N := N) (T_p_lower p hp.pos) q) =
      (QuotientGroup.mk (1 : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ imageGamma1_PSL N) := by
  induction q using QuotientGroup.induction_on with | _ g => ?_
  rw [slToPslQuot_Gamma_p_α_mk] at hq
  rw [slGamma_p_αToGamma1_mk, slToPslQuot_mk]
  obtain ⟨z, hz, hgz⟩ := (pslQuot_eq_one_iff_exists_center_mem _ g).mp hq
  exact (pslQuot_eq_one_iff_exists_center_mem _ g).mpr
    ⟨z, hz, (Gamma_p_α_le_Gamma1 _) hgz⟩

include hp hpN in
open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory in
/-- The map `slGamma_p_αToGamma1 (T_p_lower)` is injective on the `Γ_p(A)`-fiber of `[1]`,
via `Gamma1_coset_iff_Gamma_p_α_coset_of_center_fiber`. -/
private theorem slGamma_p_αToGamma1_injective_on_Gamma_p_α_fiber
    (q₁ q₂ : SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp.pos))
    (hq₁ : slToPslQuot_Gamma_p_α (N := N) (T_p_lower p hp.pos) q₁ =
      (QuotientGroup.mk (1 : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) (T_p_lower p hp.pos)))
    (hq₂ : slToPslQuot_Gamma_p_α (N := N) (T_p_lower p hp.pos) q₂ =
      (QuotientGroup.mk (1 : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) (T_p_lower p hp.pos)))
    (heq : slGamma_p_αToGamma1 (N := N) (T_p_lower p hp.pos) q₁ =
      slGamma_p_αToGamma1 (N := N) (T_p_lower p hp.pos) q₂) :
    q₁ = q₂ := by
  induction q₁ using QuotientGroup.induction_on with | _ g₁ => ?_
  induction q₂ using QuotientGroup.induction_on with | _ g₂ => ?_
  rw [slToPslQuot_Gamma_p_α_mk] at hq₁ hq₂
  rw [slGamma_p_αToGamma1_mk, slGamma_p_αToGamma1_mk, QuotientGroup.eq] at heq
  obtain ⟨z₁, hz₁, hgz₁⟩ := (pslQuot_eq_one_iff_exists_center_mem _ g₁).mp hq₁
  obtain ⟨z₂, hz₂, hgz₂⟩ := (pslQuot_eq_one_iff_exists_center_mem _ g₂).mp hq₂
  rw [QuotientGroup.eq]
  exact (Gamma1_coset_iff_Gamma_p_α_coset_of_center_fiber p hp hpN g₁ g₂ z₁ z₂
    hz₁ hz₂ hgz₁ hgz₂).mp heq

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory in
/-- The map `slGamma_p_αToGamma1 (T_p_lower)` is surjective onto the `Γ₁`-fiber of `[1]`:
the center part `z⁻¹` of any `Γ₁`-fiber rep `g` gives the corresponding `Γ_p(A)`-fiber rep
(since `z * g = g * z` by centrality, and `(z⁻¹)⁻¹·g = g·z ∈ Γ₁(N)`). -/
private theorem slGamma_p_αToGamma1_surjective_onto_Gamma1_fiber
    (p : ℕ) (hp : Nat.Prime p) (_hpN : Nat.Coprime p N)
    (q : SL(2, ℤ) ⧸ Gamma1 N)
    (hq : slToPslQuot (N := N) q =
      (QuotientGroup.mk (1 : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ imageGamma1_PSL N)) :
    ∃ a : SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp.pos),
      slToPslQuot_Gamma_p_α (N := N) (T_p_lower p hp.pos) a =
        (QuotientGroup.mk (1 : PSL(2, ℤ)) :
          PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) (T_p_lower p hp.pos)) ∧
      slGamma_p_αToGamma1 (N := N) (T_p_lower p hp.pos) a = q := by
  induction q using QuotientGroup.induction_on with | _ g => ?_
  rw [slToPslQuot_mk] at hq
  obtain ⟨z, hz, hgz⟩ := (pslQuot_eq_one_iff_exists_center_mem _ g).mp hq
  refine ⟨QuotientGroup.mk z⁻¹, ?_, ?_⟩
  · rw [slToPslQuot_Gamma_p_α_mk]
    refine (pslQuot_eq_one_iff_exists_center_mem _ z⁻¹).mpr ⟨z, hz, ?_⟩
    rw [inv_mul_cancel]
    exact (Gamma_p_α (N := N) (T_p_lower p hp.pos)).one_mem
  · rw [slGamma_p_αToGamma1_mk, QuotientGroup.eq, inv_inv,
      (Subgroup.mem_center_iff.mp hz g).symm]
    exact hgz

include hp hpN in
open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory in
/-- **Fiber-count reconciliation.** The `SL → PSL` fiber count at `Γ_p(diag(p,1))` equals the
one at `Γ₁(N)`. Both count `[H·{±I} : H]` over the respective `H`, which is `1` or `2`
according to whether `-I ∈ H`; and `-I ∈ Γ_p(A) ↔ -I ∈ Γ₁(N)` (the `(1,0)`-entry of `-I` is
`0`, divisible by `p`). This is the `c_p`-vs-`c_N` bridge that lets leaf 1's `c_N`-weighted
`Γ_p(A)`-FD integral feed the trace engine (which carries `c_p`). -/
theorem slToPslQuot_fiberCard_Gamma_p_α_T_p_lower_eq_fiberCard :
    slToPslQuot_fiberCard_Gamma_p_α (N := N) (T_p_lower p hp.pos) =
      slToPslQuot_fiberCard N := by
  classical
  rw [slToPslQuot_fiberCard_Gamma_p_α, slToPslQuot_fiberCard]
  refine Finset.card_bij
    (fun q _ ↦ slGamma_p_αToGamma1 (N := N) (T_p_lower p hp.pos) q) ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact slGamma_p_αToGamma1_maps_into_Gamma1_fiber p hp hpN q hq
  · intro q₁ hq₁ q₂ hq₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq₁ hq₂
    exact slGamma_p_αToGamma1_injective_on_Gamma_p_α_fiber p hp hpN q₁ q₂ hq₁ hq₂ heq
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨a, ha₁, ha₂⟩ := slGamma_p_αToGamma1_surjective_onto_Gamma1_fiber p hp hpN q hq
    exact ⟨a, by simp [ha₁], ha₂⟩

include hp hpN in
open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory in
/-- **TRACE LEAF (DS 5.5.3, form-level) — the single genuine remaining gap.** Summing `g ∣ A`
over a transversal of `Γ_p(A)\Γ₁(N)` (`A = diag(p,1)`, `[Γ₁ : Γ_p(A)] = p+1`) yields the
*adjoint* Hecke operator `⟨p⟩⁻¹ T_p g`. Precisely, the partial trace
`traceSlash_Gamma_p_α A (g∣A) q₀` equals `⇑(⟨p⟩⁻¹ T_p g)` as a function `ℍ → ℂ` (independent
of the base coset `q₀`).

NON-CIRCULAR: this is a pure slash/coset identity — `traceSlash_Gamma_p_α`, `glMap`,
`diamondOp_cusp`, `heckeT_p_cusp` are all defined strictly *before* `heckeT_p_adjoint`
(in `FDTransport`/`Gamma1Pair`/`AdjointTheory`), and the statement mentions neither
`petersson`, `petN`, nor `heckeT_p_adjoint`. So `heckeT_p_adjoint`'s proof (which uses this
leaf) does not loop through itself.

MATH: the double coset `Γ₁ A Γ₁` with `A = diag(p,1)` is the *adjoint* of the standard `T_p`
coset `Γ₁ diag(1,p) Γ₁` (`diag(p,1) = det(diag(1,p))·diag(1,p)⁻¹`), and DS Thm 5.5.3 gives
`g[Γ₁ A Γ₁]_k = ⟨p⟩⁻¹ T_p g`.

PROOF SKELETON (the precise residual gap; two ordered sub-lemmas):
1. `traceSlash_Gamma_p_α A (g∣A) q₀ = ∑_{j} (g∣A) ∣[k] δ_j` over a CONCRETE transversal
   `{δ_j}` (`p+1` elements) of `Γ_p(A)\Γ₁` — where `Γ_p(A) = {γ∈Γ₁ : p ∣ γ₁₀}`
   (`mem_Gamma_p_α_T_p_lower`, the `Γ₀(p)`-type lower-left condition). A correct transversal is
   the `Γ₀(p)\Γ₁`-style lower reps (e.g. `[[1,0],[j,1]]·(level corrector)` for `j=0..p-1`
   plus an `S`-type rep). NB: `T_p_lower_tile_family` (DeltaB:687) is NOT this transversal —
   it is the transversal of the *conjugate* group `Γ₁ ∩ AΓ₁A⁻¹` (the `A•D` decomposition),
   a different coset space; building the `Γ_p(A)\Γ₁` transversal is part of this gap. The
   bridge is a `Finset.sum_bij` from the abstract fiber `{q : slGamma_p_αToGamma1 A q = q₀}`
   to `{δ_j}`, with the `Γ_p(A)`-slash-invariance of `g∣A`
   (`slash_α_Gamma_p_α_invariant_cuspForm`) absorbing the per-coset discrepancy; base-coset
   independence is `traceSlash_Gamma_p_α_indep`.
2. `∑_j (g∣A) ∣[k] δ_j = ∑_j g ∣[k] (A·δ_j) = ⇑(⟨p⟩⁻¹ T_p g)`. The matrices `{A·δ_j}` (det-`p`)
   are left-coset reps of `Γ₁\Γ₁ A Γ₁`, the *adjoint* of the standard `T_p` double coset
   `Γ₁ diag(1,p) Γ₁` (`diag(p,1) = det(diag(1,p))·diag(1,p)⁻¹`); recombine into the adjoint
   family via `heckeT_p_fun_eq_coset_sum` (HeckeT_p_Gamma1:307), `heckeT_p_comm_diamondOp`
   (HeckeT_p:1013), `glMap_M_infty_eq_mapGL_sigma_p_mul_glMap_T_p_lower` (SA:303), and the
   diamond/slash commutation. This is the genuine DS 5.5.3 / Miyake 4.5.4 content. -/
theorem traceSlash_T_p_lower_eq_diamond_inv_heckeT_p
    (q₀ : SL(2, ℤ) ⧸ Gamma1 N) :
    traceSlash_Gamma_p_α (N := N) (k := k) (T_p_lower p hp.pos)
      (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) q₀ =
    ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ (heckeT_p_cusp k p hp hpN g)) :=
  ds_traceSlash_Gamma_p_α_T_p_lower_eq_diamond_inv_heckeT_p p hp hpN g q₀

include hp in
open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory in
/-- Integrability of `pet f ((g∣A)∣γ)` (`γ : SL(2,ℤ)`) over any finite-measure set: the
slash-by-`A`-then-`γ` collapses to `g ∣ glMap(A · γ)`. -/
private theorem integrableOn_petersson_slash_T_p_lower_slash_SL
    (γ : SL(2, ℤ))
    {S : Set ℍ} (hS : μ_hyp S < ⊤) :
    IntegrableOn (fun τ ↦ petersson k ⇑f
      ((⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ∣[k] (γ : SL(2, ℤ))) τ)
      S μ_hyp := by
  have hσ : (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ∣[k] (γ : SL(2, ℤ)) =
      ⇑g ∣[k] (glMap (T_p_lower p hp.pos * mapGL ℚ γ) : GL (Fin 2) ℝ) := by
    rw [ModularForm.SL_slash, map_mul, ← SlashAction.slash_mul]; rfl
  rw [hσ]
  exact integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure f g
    (T_p_lower p hp.pos * mapGL ℚ γ) hS

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory in
/-- Integrability of `pet f (g∣A)` on the canonical `Γ_p(A)`-FD (engine hyp `h_int`). -/
private theorem h_int_FD (p : ℕ) (hp : Nat.Prime p) (_hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    IntegrableOn
      (fun τ ↦ petersson k ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) (T_p_lower p hp.pos)) μ_hyp :=
  integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure f g (T_p_lower p hp.pos)
    (hyperbolicMeasure_Gamma_p_α_fundDomain_PSL_canonical_lt_top (N := N) (T_p_lower p hp.pos))

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory Classical in
/-- Per-fiber integrability of the slashed trace summand (engine hyp `h_int_trace`). -/
private theorem h_int_trace_FD (p : ℕ) (hp : Nat.Prime p) (_hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (_q₀ : SL(2, ℤ) ⧸ Gamma1 N) :
    TraceFiberIntegrable (N := N) (k := k) (T_p_lower p hp.pos) ⇑f
      (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) := by
  intro q' q _
  refine integrableOn_petersson_slash_T_p_lower_slash_SL p hp f g
    ((q.out : SL(2, ℤ))⁻¹ * q'.out) ?_
  rw [← Set.preimage_smul (q'.out : SL(2, ℤ)) (fd : Set ℍ), measure_preimage_smul]
  exact hyperbolicMeasure_fd_lt_top

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory Classical in
/-- Integrability of `pet f (tr_{q₀}(g∣A))` on the `Γ₁`-FD (engine hyp `h_int_tr`). -/
private theorem h_int_tr_FD (p : ℕ) (hp : Nat.Prime p) (_hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (q₀ : SL(2, ℤ) ⧸ Gamma1 N) :
    IntegrableOn
      (fun τ ↦ petersson k ⇑f
        (traceSlash_Gamma_p_α (N := N) (k := k) (T_p_lower p hp.pos)
          (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) q₀) τ)
      (Gamma1_fundDomain_PSL N) μ_hyp := by
  have h_fun : (fun τ ↦ petersson k ⇑f
      (traceSlash_Gamma_p_α (N := N) (k := k) (T_p_lower p hp.pos)
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) q₀) τ) =
      fun τ ↦ ∑ q ∈ Finset.univ.filter
        (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp.pos) ↦
          slGamma_p_αToGamma1 (N := N) (T_p_lower p hp.pos) q = q₀),
        petersson k ⇑f
          ((⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ∣[k]
            ((q.out : SL(2, ℤ))⁻¹ * q₀.out)) τ := by
    funext τ
    rw [traceSlash_Gamma_p_α, petersson_sum_right]
  rw [h_fun]
  refine MeasureTheory.integrable_finset_sum _ fun q _ ↦ ?_
  exact integrableOn_petersson_slash_T_p_lower_slash_SL p hp f g
    ((q.out : SL(2, ℤ))⁻¹ * q₀.out)
    (hyperbolicMeasure_Gamma1_fundDomain_PSL_lt_top (N := N))

include hp hpN in
open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory in
/-- **DIRECT chain assembler (non-circular).** `petN(T_p f, g) = petN(f, ⟨p⟩⁻¹ T_p g)` via the
trace engine, assuming `heckeT_p_adjoint`/`symmetric_form` NOWHERE. -/
private theorem petN_heckeT_p_adjoint_via_trace :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) := by
  set q₀ : SL(2, ℤ) ⧸ Gamma1 N := QuotientGroup.mk 1
  obtain ⟨hm, h_int_per, hfi⟩ := aggregate_HeckeFD_measure_hyps p hp hpN f g
  have hF_slash : ∀ γ ∈ Gamma1 N, (⇑f : ℍ → ℂ) ∣[k] (γ : SL(2, ℤ)) = ⇑f :=
    slash_Gamma1_eq f
  have hG_slash : ∀ γ ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos),
      (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ∣[k] (γ : SL(2, ℤ)) =
        ⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) := by
    intro γ hγ
    rw [ModularForm.SL_slash, glMap_T_p_lower_eq_map_castHom]
    exact slash_α_Gamma_p_α_invariant_cuspForm (T_p_lower p hp.pos) g hγ
  rw [petN_heckeT_p_LHS_eq_aggregate p hp hpN f g,
    peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD p hp hpN f g hm h_int_per hfi,
    aggregate_D_petersson_eq_Gamma_p_A_fundDomain p hp hpN f g
      (isFundamentalDomain_Hecke_tiles_biUnion_Gamma_p_α p hp hpN),
    ← slToPslQuot_fiberCard_Gamma_p_α_T_p_lower_eq_fiberCard p hp hpN,
    setIntegral_Gamma_p_α_fundDomain_PSL_petersson_eq_traceSlash_Gamma1_fundDomain
      (N := N) (k := k) (T_p_lower p hp.pos) ⇑f
      (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) q₀ hF_slash hG_slash
      (h_int_FD p hp hpN f g) (h_int_trace_FD p hp hpN f g q₀) (h_int_tr_FD p hp hpN f g q₀),
    traceSlash_T_p_lower_eq_diamond_inv_heckeT_p p hp hpN g q₀,
    ← petN_eq_setIntegral_Gamma1_fundDomain_PSL]

include hp hpN in
/-- **DS Theorem 5.5.3**: `T_p* = ⟨p⟩⁻¹ T_p` w.r.t. the level-N Petersson product
`petN`, i.e. `⟨T_p f, g⟩_N = ⟨f, ⟨p⟩⁻¹ T_p g⟩_N`. -/
theorem heckeT_p_adjoint :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) :=
  petN_heckeT_p_adjoint_via_trace p hp hpN f g

end TpHecke

end HeckeRing.GL2

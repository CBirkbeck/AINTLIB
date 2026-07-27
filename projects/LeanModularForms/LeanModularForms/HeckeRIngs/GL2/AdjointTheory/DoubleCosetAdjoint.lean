/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.AdjointTheory.ConcreteFamily

/-!
# The generic double-coset Petersson adjoint (Diamond–Shurman Proposition 5.5.2(b))

This module formalises the **generic** double-coset Petersson adjoint, DS Prop 5.5.2(b),
abstracting away from the concrete coprime `T_p` family (`ConcreteFamily.lean`) and the
concrete bad-prime `U_p` family (`Newforms/AdjointTheoryBadPrime.lean`).

For a congruence subgroup `Γ = Γ₁(N)` and `α ∈ GL₂⁺(ℚ)`, write `α' = det(α)·α⁻¹ = adj(α)`
(`peterssonAdj`). DS Lemma 5.5.1(c) produces a finite family `βⱼ ∈ GL₂⁺(ℚ)` of common
representatives `ΓαΓ = ⊔ⱼ Γβⱼ = ⊔ⱼ βⱼΓ`; the `βⱼ` serve as the left-coset reps in the
double-coset operator `f[ΓαΓ]_k = ∑ⱼ f∣[βⱼ]_k`, and the `βⱼ' = adj(βⱼ)` serve as the reps
for `[Γα'Γ]_k`.  DS Prop 5.5.2(b) is then `⟨f[ΓαΓ]_k, g⟩_Γ = ⟨f, g[Γα'Γ]_k⟩_Γ`.

Rather than reproving the `Γ_p(α)`-fundamental-domain tiling (the genuine research-scale
wall flagged in `Newforms/AdjointTheoryBadPrime.lean`), this file isolates that tiling as a
single explicit *hypothesis* — exactly the Lemma 5.5.1(c) input that DS feeds Prop 5.5.2(b)
— and discharges everything else by reusing the existing generic engines:

* the per-summand change of variables `peterssonInner_slash_adjoint` (DS Prop 5.5.2(a))
  and its finite-sum / aggregate packaging
  `peterssonInner_T_p_family_sum_slashes_eq_aggregate_of_integrable`;
* the level-`N` Petersson product `petN` ↔ `Γ₁(N)`-fundamental-domain integral bridge
  `petN_eq_setIntegral_Gamma1_fundDomain_PSL`;
* the abstract `Γ_p(α) ↔ Γ₁(N)` trace reassembly
  `setIntegral_Gamma_p_α_fundDomain_PSL_petersson_eq_traceSlash_Gamma1_fundDomain`
  (DS Exercise 5.4.4) and the Hecke-aggregate → `Γ_p(α)`-FD transfer.

## Main results

* `petN_doubleCoset_sum_slashes_eq_aggregate` — the LHS bridge (fully generic, no
  fundamental-domain hypothesis): `petN F g = c_N • ⟨⋃ⱼ βⱼ•Γ₁-FD⟩ f g'`, whenever the cusp
  form `F` is *function-equal* to `∑ⱼ f∣βⱼ` and every summand's Petersson adjoint `g∣βⱼ'`
  collapses to the common function `g'`.
* `aggregate_petersson_eq_Gamma_p_α_fundDomain` — generic Hecke-aggregate → `Γ_p(α)`-FD
  transfer of the Petersson integral, given the Lemma-5.5.1(c) tiling hypothesis.
* `petN_doubleCoset_adjoint` — the full generic Prop 5.5.2(b): given the tiling hypothesis,
  `petN F g = c_N • ∫_{Γ₁-FD} pet f (tr g')`, with `tr g'` the `Γ_p(α)`-trace of `g'` — i.e.
  the adjoint operator `[Γα'Γ]_k` applied to `g`, reassembled at level `N`.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.5 (Lemma 5.5.1, Prop 5.5.2)
-/

noncomputable section

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open scoped MatrixGroups ModularForm Pointwise

namespace HeckeRing.GL2

open UpperHalfPlane ModularGroup MeasureTheory

variable {N : ℕ} [NeZero N] {k : ℤ}

/-! ### The LHS bridge (per-summand change of variables, no FD hypothesis)

This is the source-faithful realisation of the per-representative half of DS Prop 5.5.2:
each summand `⟨f∣βⱼ, g⟩` is exchanged into `⟨f, g∣βⱼ'⟩` over the translated domain `βⱼ•D`
via `peterssonInner_slash_adjoint` (Prop 5.5.2(a)), and the translated pieces are glued into
the single integral over the Hecke aggregate `⋃ⱼ βⱼ•D`.  No coprimality and no fundamental
domain are used here. -/

/-- **DS Prop 5.5.2 — LHS bridge (generic double-coset family).**

For a finite family `β : ι → GL(2,ℝ)` of positive-determinant matrices (the left-coset
representatives `ΓαΓ = ⊔ⱼ Γβⱼ`), if the cusp form `F` is function-equal to the double-coset
image `∑ⱼ f∣βⱼ`, then the level-`N` Petersson product `petN F g` equals
`c_N • ⟨⋃ⱼ βⱼ•Γ₁-FD⟩ f g'`, where `c_N = slToPslQuot_fiberCard N` is the fixed `SL/PSL`
fiber factor and each summand's adjoint `g∣[k] adj(βⱼ)` collapses to the single function
`g'`.

This abstracts `petN_badUp_LHS_eq_aggregate ∘ peterssonInner_badUp_sum_slashes_eq_aggregate`
(the concrete bad-prime `U_p` case) to an arbitrary representative family. -/
theorem petN_doubleCoset_sum_slashes_eq_aggregate
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (β : ι → GL (Fin 2) ℝ)
    (hβ : ∀ i ∈ s, 0 < (β i).det.val)
    (f g F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (g' : ℍ → ℂ)
    (hF : (⇑F : ℍ → ℂ) = ∑ i ∈ s, ⇑f ∣[k] β i)
    (hadj : ∀ i ∈ s, ⇑g ∣[k] peterssonAdj (β i) = g')
    (hm : ∀ i ∈ s,
      NullMeasurableSet (β i • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp)
    (hd : (↑s : Set ι).Pairwise
      (fun i j ↦ AEDisjoint μ_hyp
        (β i • (Gamma1_fundDomain_PSL N : Set ℍ))
        (β j • (Gamma1_fundDomain_PSL N : Set ℍ))))
    (h_int_per : ∀ i ∈ s,
      IntegrableOn (fun τ ↦ petersson k ⇑g (⇑f ∣[k] β i) τ)
        (Gamma1_fundDomain_PSL N) μ_hyp)
    (hfi : IntegrableOn (fun τ ↦ petersson k ⇑f g' τ)
      (⋃ i ∈ s, β i • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp) :
    petN F g =
      slToPslQuot_fiberCard N •
        peterssonInner k (⋃ i ∈ s, β i • (Gamma1_fundDomain_PSL N : Set ℍ)) ⇑f g' := by
  rw [petN_eq_setIntegral_Gamma1_fundDomain_PSL, ← peterssonInner, hF,
    peterssonInner_T_p_family_sum_slashes_eq_aggregate_of_integrable
      s β hβ f g g' hadj hm hd h_int_per hfi]

/-! ### The aggregate → `Γ_p(α)`-fundamental-domain transfer

Given the Lemma-5.5.1(c) tiling hypothesis that `⋃ⱼ βⱼ•Γ₁-FD` is a fundamental domain for
`Γ_p(α) = α⁻¹Γα ∩ Γ` (in its `PSL(2,ℝ)`-image), the aggregate Petersson integral coincides
with the integral over the canonical `Γ_p(α)`-fundamental domain, because both are
fundamental domains for the same group and the integrand `pet f g'` is `Γ_p(α)`-invariant. -/

/-- **Generic Hecke-aggregate → `Γ_p(α)`-FD transfer.** Given the tiling hypothesis `hFD`
(Lemma 5.5.1(c)) and `Γ_p(α)`-invariance of the integrand `pet f g'`, the Petersson integral
over the Hecke aggregate `⋃ⱼ βⱼ•Γ₁-FD` equals the integral over the canonical `Γ_p(α)`
fundamental domain.  Abstracts `aggregate_D_petersson_eq_Gamma_p_A_fundDomain`. -/
theorem aggregate_petersson_eq_Gamma_p_α_fundDomain
    {ι : Type*} (s : Finset ι) (β : ι → GL (Fin 2) ℝ) (α : GL (Fin 2) ℚ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (g' : ℍ → ℂ)
    (hg'_inv : ∀ γ ∈ Gamma_p_α (N := N) α, ∀ τ : ℍ,
      petersson k ⇑f g' (γ • τ) = petersson k ⇑f g' τ)
    (hFD : IsFundamentalDomain
      ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R)
      (⋃ i ∈ s, β i • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp) :
    peterssonInner k (⋃ i ∈ s, β i • (Gamma1_fundDomain_PSL N : Set ℍ)) ⇑f g' =
      ∫ τ in Gamma_p_α_fundDomain_PSL (N := N) α, petersson k ⇑f g' τ ∂μ_hyp := by
  rw [peterssonInner]
  exact hFD.setIntegral_eq
    (isFundamentalDomain_Gamma_p_α_fundDomain_PSL_at_PSL_R (N := N) α)
    (fun gp τ ↦ inv_under_Gamma_p_α_PSL_R_of_inv_under_Gamma_p_α (N := N) α hg'_inv gp τ)

/-! ### The full generic adjoint (DS Prop 5.5.2(b))

Chaining the LHS bridge, the aggregate transfer, and the `Γ_p(α) ↔ Γ₁(N)` trace reassembly
gives the complete generic Prop 5.5.2(b): the double-coset image's Petersson product against
`g` equals `petN` of `f` against the *trace* of `g'` over the `Γ_p(α)`-cosets, which is the
adjoint double-coset operator `[Γα'Γ]_k` applied to `g`. -/

/-- **DS Proposition 5.5.2(b), generic double-coset Petersson adjoint.**

Let `α ∈ GL(2,ℚ)`, `β : ι → GL(2,ℝ)` the family of pos-det left-coset representatives
(`ΓαΓ = ⊔ⱼ Γβⱼ`), and `F` a cusp form function-equal to the double-coset image `∑ⱼ f∣βⱼ`.
Assume the Lemma-5.5.1(c) tiling `hFD` (that `⋃ⱼ βⱼ•Γ₁-FD` is a `Γ_p(α)`-fundamental domain),
that every summand's adjoint `g∣[k] adj(βⱼ)` collapses to a single `Γ_p(α)`-slash-invariant
function `g'`, and the fiber-count reconciliation `hcp : c_p = c_N`
(`slToPslQuot_fiberCard_Gamma_p_α α = slToPslQuot_fiberCard N`, automatic whenever `-I`
sits the same way in `Γ_p(α)` and `Γ₁(N)`, e.g. `N ≥ 3`).  Then
`petN F g = c_p • ∫_{Γ_p(α)-FD} pet f g' = c_N • ∫_{Γ₁-FD} pet f (tr_{q₀} g')`,
where `tr_{q₀} g' = traceSlash_Gamma_p_α α g' q₀` is the `Γ_p(α)`-trace of `g'` (the action
of the adjoint operator `[Γα'Γ]_k` on `g`, reassembled at level `N`). -/
theorem petN_doubleCoset_adjoint
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (β : ι → GL (Fin 2) ℝ) (α : GL (Fin 2) ℚ)
    (hβ : ∀ i ∈ s, 0 < (β i).det.val)
    (f g F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (g' : ℍ → ℂ)
    (q₀ : SL(2, ℤ) ⧸ Gamma1 N)
    (hF : (⇑F : ℍ → ℂ) = ∑ i ∈ s, ⇑f ∣[k] β i)
    (hadj : ∀ i ∈ s, ⇑g ∣[k] peterssonAdj (β i) = g')
    (hg'_slash : ∀ γ ∈ Gamma_p_α (N := N) α, g' ∣[k] (γ : SL(2, ℤ)) = g')
    (hm : ∀ i ∈ s,
      NullMeasurableSet (β i • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp)
    (hd : (↑s : Set ι).Pairwise
      (fun i j ↦ AEDisjoint μ_hyp
        (β i • (Gamma1_fundDomain_PSL N : Set ℍ))
        (β j • (Gamma1_fundDomain_PSL N : Set ℍ))))
    (h_int_per : ∀ i ∈ s,
      IntegrableOn (fun τ ↦ petersson k ⇑g (⇑f ∣[k] β i) τ)
        (Gamma1_fundDomain_PSL N) μ_hyp)
    (hfi : IntegrableOn (fun τ ↦ petersson k ⇑f g' τ)
      (⋃ i ∈ s, β i • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp)
    (h_int_trace : TraceFiberIntegrable (N := N) (k := k) α ⇑f g')
    (h_int_tr : IntegrableOn
      (fun τ ↦ petersson k ⇑f (traceSlash_Gamma_p_α (N := N) (k := k) α g' q₀) τ)
      (Gamma1_fundDomain_PSL N) μ_hyp)
    (h_int_canonical : IntegrableOn (fun τ ↦ petersson k ⇑f g' τ)
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) μ_hyp)
    (hcp : slToPslQuot_fiberCard_Gamma_p_α (N := N) α = slToPslQuot_fiberCard N)
    (hFD : IsFundamentalDomain
      ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R)
      (⋃ i ∈ s, β i • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp) :
    petN F g =
      slToPslQuot_fiberCard N •
        ∫ τ in Gamma1_fundDomain_PSL N,
          petersson k ⇑f (traceSlash_Gamma_p_α (N := N) (k := k) α g' q₀) τ ∂μ_hyp := by
  have hg'_inv : ∀ γ ∈ Gamma_p_α (N := N) α, ∀ τ : ℍ,
      petersson k ⇑f g' (γ • τ) = petersson k ⇑f g' τ := by
    intro γ hγ τ
    rw [← petersson_slash_SL, slash_Gamma1_eq f γ (Gamma_p_α_le_Gamma1 α hγ), hg'_slash γ hγ]
  have hf_slash : ∀ γ ∈ Gamma1 N, (⇑f : ℍ → ℂ) ∣[k] (γ : SL(2, ℤ)) = ⇑f := slash_Gamma1_eq f
  rw [petN_doubleCoset_sum_slashes_eq_aggregate s β hβ f g F g' hF hadj hm hd h_int_per hfi,
    aggregate_petersson_eq_Gamma_p_α_fundDomain s β α f g' hg'_inv hFD]
  conv_lhs => rw [← hcp]
  rw [setIntegral_Gamma_p_α_fundDomain_PSL_petersson_eq_traceSlash_Gamma1_fundDomain
      (N := N) (k := k) α ⇑f g' q₀ hf_slash hg'_slash h_int_canonical h_int_trace h_int_tr]

end HeckeRing.GL2

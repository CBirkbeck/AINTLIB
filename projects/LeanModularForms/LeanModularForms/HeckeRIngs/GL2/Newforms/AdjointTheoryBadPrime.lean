/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.Newforms.LevelRaiseComm
import LeanModularForms.HeckeRIngs.GL2.Fricke
import LeanModularForms.HeckeRIngs.GL2.Newforms.FrickeOldStable
import LeanModularForms.HeckeRIngs.GL2.Newforms.BadPrimeOldStable
import LeanModularForms.HeckeRIngs.GL2.AdjointTheory.DoubleCosetAdjoint
import LeanModularForms.HeckeRIngs.GL2.Newforms.BadPrimeFDTiling
import LeanModularForms.HeckeRIngs.GL2.Newforms.BadPrimeTraceFricke

/-!
# Bad-prime `U_p` Petersson adjoint (Diamond–Shurman §5.6)

This module develops the Petersson-adjoint theory of the bad-prime Hecke operator
`U_p = heckeT_n_cusp k p` (for `p ∣ N`), towards the new-subspace stability
`heckeT_n_cusp_preserves_cuspFormsNewExtended_bad` (DS Prop 5.6.2 at bad primes).

Unlike the coprime case (`AdjointTheoryPetersson.lean`), the bad-prime operator
`U_p f = Σ_{b<p} f ∣[k] [1,b;0,p]` is a sum over only the `p` upper-triangular cosets
(no `M_∞` coset, no Bézout / `Coprime p N`).  The per-summand Petersson adjoint of
`[1,b;0,p]` is `[p,-b;0,1] = shift_{-b} · diag(p,1)`; since `shift_{-b} ∈ Γ₁(N)` acts
trivially on a `Γ₁(N)`-cusp form, **every summand's adjoint collapses to the single
function `g ∣[k] diag(p,1)`** (`slash_peterssonAdj_glMap_T_p_upper_eq_slash_T_p_lower`,
SummandAdjoint.lean).  Crucially `g ∣[k] diag(p,1)` is **not** `Γ₁(N)`-invariant, so the
adjoint operator is genuinely *not* a level-`N` Hecke operator.

## Main results

* `badUp_coe_eq_sum_slashes` — the function-level form of `U_p`.
* `petN_badUp_LHS_eq_aggregate` — LHS bridge: `petN (U_p f) g` to the `Γ₁`-FD aggregate.
* `petN_badUp_eq_aggregate_integral` — `petN (U_p f) g` as the Petersson integral over the
  `p`-tile Hecke aggregate `⋃_{b<p} [1,b;0,p] • Γ₁-FD` of `f` against `g ∣[k] diag(p,1)`.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.6 (Prop 5.6.2, Exer 5.6.3)
-/

noncomputable section

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open scoped MatrixGroups ModularForm Pointwise

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The function-level form of the bad-prime operator `U_p f = Σ_{b<p} f ∣[k] [1,b;0,p]`,
as a `Finset.univ` sum over `Fin p` of slashes by `glMap (T_p_upper p _ b)`. -/
theorem badUp_coe_eq_sum_slashes
    (p : ℕ) (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    (⇑(heckeT_n_cusp k p f) : UpperHalfPlane → ℂ) =
      ∑ b : Fin p, ⇑f ∣[k] (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hForm : (heckeT_n_cusp k p f).toModularForm' =
      heckeT_p_divN k p hp hpN f.toModularForm' := by
    rw [heckeT_n_cusp_toModularForm', heckeT_n_prime k hp,
      show heckeT_p_all k p hp = heckeT_p_divN k p hp hpN from dif_neg hpN]
  have hfun : (⇑(heckeT_n_cusp k p f) : UpperHalfPlane → ℂ) =
      heckeT_p_ut k p hp.pos (⇑f) := by
    rw [show (⇑(heckeT_n_cusp k p f) : UpperHalfPlane → ℂ) =
        ⇑(heckeT_n_cusp k p f).toModularForm' from rfl, hForm]
    rfl
  rw [hfun, show heckeT_p_ut k p hp.pos (⇑f) =
      ∑ b ∈ Finset.range p,
        ⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ) from rfl,
    ← Fin.sum_univ_eq_sum_range
      (fun b ↦ ⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ))]
  rfl

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **LHS bridge.** `petN (U_p f) g = c_N • ⟨Γ₁-FD⟩ (Σ_{b<p} f ∣ [1,b;0,p]) g`, where
`c_N = slToPslQuot_fiberCard N`.  The fiber-count factor `c_N` is forced because `petN` is
the integral over the *SL*-coset fundamental domain (`[SL:Γ₁(N)]` tiles), while
`peterssonInner k (Gamma1_fundDomain_PSL N)` is the integral over the *PSL*-coset domain. -/
theorem petN_badUp_LHS_eq_aggregate
    (p : ℕ) (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    petN (heckeT_n_cusp k p f) g =
    slToPslQuot_fiberCard N • peterssonInner k (Gamma1_fundDomain_PSL N)
      (∑ b : Fin p, ⇑f ∣[k] (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) ⇑g := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [petN_eq_setIntegral_Gamma1_fundDomain_PSL, peterssonInner,
    badUp_coe_eq_sum_slashes p hp hpN f]

open UpperHalfPlane ModularGroup MeasureTheory in
open UpperHalfPlane ModularGroup MeasureTheory in
/-- **Sum-of-slashes adjoint (bad-prime `p`-tile family).** The Petersson integral of
`Σ_{b<p} f ∣ [1,b;0,p]` against `g` over the `Γ₁(N)` PSL-FD transfers to the integral of `f`
against `g ∣ diag(p,1)` over the *aggregate* domain `⋃_{b<p} [1,b;0,p] • Γ₁-FD`.  Every
summand's adjoint collapses to `g ∣ diag(p,1)` because the per-summand shift `shift_{-b}`
lies in `Γ₁(N)` (`slash_peterssonAdj_glMap_T_p_upper_eq_slash_T_p_lower`).  No `M_∞` coset,
no `Coprime p N`. -/
theorem peterssonInner_badUp_sum_slashes_eq_aggregate
    (p : ℕ) (hp : Nat.Prime p) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k (Gamma1_fundDomain_PSL N)
      (∑ b : Fin p, ⇑f ∣[k] (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) ⇑g =
    peterssonInner k
      (⋃ b ∈ (Finset.univ : Finset (Fin p)),
        (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) •
          (Gamma1_fundDomain_PSL N : Set ℍ))
      ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) := by
  have h_sum_univ : (∑ b : Fin p, ⇑f ∣[k] (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) =
      ∑ b ∈ (Finset.univ : Finset (Fin p)),
        ⇑f ∣[k] (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) := rfl
  rw [h_sum_univ]
  exact peterssonInner_T_p_family_sum_slashes_eq_aggregate_of_integrable
    (s := Finset.univ)
    (α := fun b : Fin p ↦ (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ))
    (f := f) (g := g) (g' := ⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ))
    (fun b _ ↦ glMap_T_p_upper_det_pos p hp.pos b.val)
    (fun b _ ↦ slash_peterssonAdj_glMap_T_p_upper_eq_slash_T_p_lower p hp.pos b.val g)
    (fun b _ ↦ nullMeasurableSet_glPos_smul_Gamma1_fundDomain_PSL
      (glMap_T_p_upper_det_pos p hp.pos b.val))
    (by
      intro b₁ _ b₂ _ hne
      refine aedisjoint_glMap_T_p_upper_pair hp.pos ?_
      intro h_eq
      apply hne
      have : (b₁.val : ℤ) = (b₂.val : ℤ) := by omega
      exact Fin.ext (by exact_mod_cast this))
    (fun b _ ↦ integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure g f
      (T_p_upper p hp.pos b.val)
      (hyperbolicMeasure_Gamma1_fundDomain_PSL_lt_top (N := N)))
    (integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure f g
      (T_p_lower p hp.pos)
      (by
        simp only [Finset.mem_univ, Set.iUnion_true]
        refine (measure_iUnion_le _).trans_lt ?_
        rw [tsum_fintype]
        exact ENNReal.sum_lt_top.mpr fun b _ ↦
          measure_glPos_smul_Gamma1_fundDomain_lt_top _
            (glMap_T_p_upper_det_pos p hp.pos b.val)))

/-- `glMap (T_p_lower p) = levelRaiseMatrix p` (both are the matrix `diag(p, 1)`).
Hence `g ∣ T_p_lower = g ∣ levelRaiseMatrix p`, the (unnormalised) level-raising-by-`p`
slash; this is the natural bridge for analysing the bad-prime adjoint via the level-raise
commutation `levelRaise_mul_T_p_lower`. -/
lemma glMap_T_p_lower_eq_levelRaiseMatrix (p : ℕ) (hp : 0 < p) :
    haveI : NeZero p := ⟨hp.ne'⟩
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) = levelRaiseMatrix p := by
  haveI : NeZero p := ⟨hp.ne'⟩
  apply Units.ext
  ext i j
  have hL : ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![(p : ℝ), 0; 0, 1] := by
    ext i' j'
    fin_cases i' <;> fin_cases j' <;> simp [glMap, T_p_lower]
  have hR : ((levelRaiseMatrix p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ), 0; 0, 1] := by
    ext i' j'
    fin_cases i' <;> fin_cases j' <;>
      simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.of_apply]
  rw [hL, hR]

/-! ### The remaining genuine gap (DS Prop 5.6.2, bad-prime Petersson adjoint)

The chain so far establishes (all sorry-free, reusing the coprime measure-theory engine):
```
petN (U_p f) g = c_N • peterssonInner (⋃_{b<p} [1,b;0,p] • Γ₁-FD) f (g ∣ diag(p,1)).
```
What remains is the vanishing of this aggregate Petersson integral when `f` is new and `g`
is old.  Mathematically (DS Prop 5.6.2) this is the statement that the Petersson adjoint of
`U_p` preserves the old subspace.  Two facts are entangled in it, **neither** available in
mathlib or the present codebase for the bad-prime `p`-tile family:

* **(W-tiling)** `⋃_{b<p} [1,b;0,p] • Γ₁-FD` is a fundamental domain for
  `Γ' = Γ₁(N) ∩ Γ⁰(p)` (index `p` in `Γ₁(N)`, the upper-triangular-mod-`p` congruence group).
  This is the bad-prime analogue of `isFundamentalDomain_Hecke_tiles_Gamma_p_α`
  (`DeltaBSystem.lean`), but for a **different group** (`Γ⁰(p)`-type, NOT `Γ_p(diag(p,1))`)
  and with **only `p` tiles** (no `M_∞`; the coprime covering/transversal argument routes
  through `M_infty_Gamma1_factor` and Bézout, both requiring `Coprime p N`).
* **(old-transfer)** transferring the resulting `∫_{Γ'-FD} pet f (g ∣ diag(p,1))` to a
  level-`N` orthogonality `f ⊥ old`.  Since `g ∣ diag(p,1)` is the level-raise of `g` to
  level `pN` (`glMap_T_p_lower_eq_levelRaiseMatrix`), this is a genuine cross-level transfer.

Re-deriving the `petN` fundamental-domain-tiling machinery for `Γ'` is a multi-week
formalization comparable in scope to `AdjointTheory/{DeltaBSystem, ConcreteFamily,
SummandAdjoint}.lean` + `AdjointTheoryPetersson.lean` combined.  It is isolated here as the
single `sorry`. -/
open UpperHalfPlane ModularGroup MeasureTheory in
/-- **[WALL — DS Prop 5.6.2 bad-prime adjoint]** The bad-prime Hecke aggregate Petersson
integral of a *new* form `f` against the level-raise `g ∣ diag(p,1)` of an *old* form `g`
vanishes.  This is the Petersson-adjoint stability of the old subspace under `U_p`; see the
note above for the (research-scale, currently-missing) `Γ⁰(p)`-fundamental-domain tiling it
requires. -/
theorem peterssonInner_aggregate_eq_zero_of_new_old
    (p : ℕ) (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    {f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormsNewExtended N k) (hg : g ∈ cuspFormsOldExtended N k) :
    peterssonInner k
      (⋃ b ∈ (Finset.univ : Finset (Fin p)),
        (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) •
          (Gamma1_fundDomain_PSL N : Set ℍ))
      ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) = 0 := by
  sorry

/-! ### The Fricke route to T006-b (DS Prop 5.6.2, the source-faithful proof)

Decomposition: `.mathlib-quality/decomposition-T006b-fricke.md`. This REPLACES the
`Γ⁰(p)`-fundamental-domain-tiling route above (the `peterssonInner_aggregate_eq_zero_of_new_old`
sorry) — which is correct but not how DS proves Prop 5.6.2 and dead-ends on absent FD-tiling.

DS's route: `new = oldᗮ`, so `U_p(new) ⊆ new ⟺ U_p*(old) ⊆ old`; for bad `p`,
`U_p* = w_N U_p w_N⁻¹` (Ex 5.5.1), so it suffices that `w_N` (L2) and `U_p` (L3) preserve `old`.
The skeleton below states the leaves as `:= sorry`; see the ticket board (T006-b-L1..L5). -/

/-- **[T006-b-L1]** `frickeOperatorCusp` (= `w_N` on cusp forms) agrees with `frickeOperator`
through the `CuspForm → ModularForm` coercion — the bridge to the modular-form Fricke API. -/
@[simp] theorem frickeOperatorCusp_toModularForm' (k : ℤ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (frickeOperatorCusp k f).toModularForm' = frickeOperator k f.toModularForm' :=
  DFunLike.ext _ _ fun _ ↦ rfl

-- **[T006-b-L2]** `frickeOperatorCusp_mem_cuspFormsOldExtended` (`w_N` preserves oldExt,
-- DS Ex 5.6.3(e)) is PROVEN in `Newforms/FrickeOldStable.lean` (imported above).

-- **[T006-b-L3]** the bad-prime `U_p` old-stability `heckeT_n_cusp_divN_mem_cuspFormsOldExtended`
-- (DS Ex 5.6.3(b)(c)) is PROVEN in `Newforms/BadPrimeOldStable.lean` (imported above); it is all
-- `badUpAdjoint_mem` needs (the adjoint operator only applies `U_p` at the single bad prime `p`).

/-- `U_p` as a `ℂ`-linear endomorphism of cusp forms (for use inside `badUpAdjoint`). -/
noncomputable def heckeEndCusp (p : ℕ) [NeZero p] :
    Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) where
  toFun := heckeT_n_cusp k p
  map_add' := heckeT_n_cusp_add p
  map_smul' c f := heckeT_n_cusp_smul p c f

@[simp] lemma heckeEndCusp_apply (p : ℕ) [NeZero p]
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    heckeEndCusp p f = heckeT_n_cusp k p f := rfl

/-- The bad-prime Petersson adjoint operator `U_p* = w_N U_p w_N⁻¹ = (frickeScalar)⁻¹ · w_N U_p w_N`
(using `w_N² = frickeScalar`, so `w_N⁻¹ = (frickeScalar)⁻¹ · w_N`).  DS Ex 5.5.1(b). -/
noncomputable def badUpAdjoint (p : ℕ) [NeZero p] :
    Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  (frickeScalar N k)⁻¹ • (frickeOperatorCusp k ∘ₗ heckeEndCusp p ∘ₗ frickeOperatorCusp k)

@[simp] lemma badUpAdjoint_apply (p : ℕ) [NeZero p]
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    badUpAdjoint p g =
      (frickeScalar N k)⁻¹ •
        frickeOperatorCusp k (heckeT_n_cusp k p (frickeOperatorCusp k g)) := rfl

/-! ### Integrability mirrors (coprimality-free copies of `ConcreteFamily` privates)

The generic `petN_doubleCoset_adjoint` requires four integrability hypotheses that
`ConcreteFamily.lean` discharges with private lemmas guarded by `Coprime p N`. Their proofs
are coprimality-free (the `Coprime` hypothesis is unused), so we mirror them here for the
bad-prime instance `α = T_p_lower p`, `g' = g ∣ diag(p,1)`. -/

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory in
/-- Integrability of `pet f ((g∣A)∣γ)` (`γ : SL(2,ℤ)`) over any finite-measure set; the
slash-by-`A`-then-`γ` collapses to `g ∣ glMap(A · γ)`. (Coprimality-free mirror of
`ConcreteFamily.integrableOn_petersson_slash_T_p_lower_slash_SL`.) -/
private theorem integrableOn_petersson_slash_T_p_lower_slash_SL'
    (p : ℕ) (hp : 0 < p) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (γ : SL(2, ℤ)) {S : Set ℍ} (hS : μ_hyp S < ⊤) :
    IntegrableOn (fun τ ↦ petersson k ⇑f
      ((⇑g ∣[k] (glMap (T_p_lower p hp) : GL (Fin 2) ℝ)) ∣[k] (γ : SL(2, ℤ))) τ)
      S μ_hyp := by
  have hσ : (⇑g ∣[k] (glMap (T_p_lower p hp) : GL (Fin 2) ℝ)) ∣[k] (γ : SL(2, ℤ)) =
      ⇑g ∣[k] (glMap (T_p_lower p hp * mapGL ℚ γ) : GL (Fin 2) ℝ) := by
    rw [ModularForm.SL_slash, map_mul, ← SlashAction.slash_mul]; rfl
  rw [hσ]
  exact integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure f g
    (T_p_lower p hp * mapGL ℚ γ) hS

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory in
/-- Integrability of `pet f (g∣A)` on the canonical `Γ_p(A)`-FD (engine hyp `h_int_canonical`).
Coprimality-free mirror of `ConcreteFamily.h_int_FD`. -/
private theorem h_int_FD' (p : ℕ) (hp : 0 < p)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    IntegrableOn
      (fun τ ↦ petersson k ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp) : GL (Fin 2) ℝ)) τ)
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) (T_p_lower p hp)) μ_hyp :=
  integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure f g (T_p_lower p hp)
    (hyperbolicMeasure_Gamma_p_α_fundDomain_PSL_canonical_lt_top (N := N) (T_p_lower p hp))

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory Classical in
/-- Per-fiber integrability of the slashed trace summand (engine hyp `h_int_trace`).
Coprimality-free mirror of `ConcreteFamily.h_int_trace_FD`. -/
private theorem h_int_trace_FD' (p : ℕ) (hp : 0 < p)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    TraceFiberIntegrable (N := N) (k := k) (T_p_lower p hp) ⇑f
      (⇑g ∣[k] (glMap (T_p_lower p hp) : GL (Fin 2) ℝ)) := by
  intro q' q _
  refine integrableOn_petersson_slash_T_p_lower_slash_SL' p hp f g
    ((q.out : SL(2, ℤ))⁻¹ * q'.out) ?_
  rw [← Set.preimage_smul (q'.out : SL(2, ℤ)) (fd : Set ℍ), measure_preimage_smul]
  exact hyperbolicMeasure_fd_lt_top

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory Classical in
/-- Integrability of `pet f (tr_{q₀}(g∣A))` on the `Γ₁`-FD (engine hyp `h_int_tr`).
Coprimality-free mirror of `ConcreteFamily.h_int_tr_FD`. -/
private theorem h_int_tr_FD' (p : ℕ) (hp : 0 < p)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (q₀ : SL(2, ℤ) ⧸ Gamma1 N) :
    IntegrableOn
      (fun τ ↦ petersson k ⇑f
        (traceSlash_Gamma_p_α (N := N) (k := k) (T_p_lower p hp)
          (⇑g ∣[k] (glMap (T_p_lower p hp) : GL (Fin 2) ℝ)) q₀) τ)
      (Gamma1_fundDomain_PSL N) μ_hyp := by
  have h_fun : (fun τ ↦ petersson k ⇑f
      (traceSlash_Gamma_p_α (N := N) (k := k) (T_p_lower p hp)
        (⇑g ∣[k] (glMap (T_p_lower p hp) : GL (Fin 2) ℝ)) q₀) τ) =
      fun τ ↦ ∑ q ∈ Finset.univ.filter
        (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp) ↦
          slGamma_p_αToGamma1 (N := N) (T_p_lower p hp) q = q₀),
        petersson k ⇑f
          ((⇑g ∣[k] (glMap (T_p_lower p hp) : GL (Fin 2) ℝ)) ∣[k]
            ((q.out : SL(2, ℤ))⁻¹ * q₀.out)) τ := by
    funext τ
    rw [traceSlash_Gamma_p_α, petersson_sum_right]
  rw [h_fun]
  refine MeasureTheory.integrable_finsetSum _ fun q _ ↦ ?_
  exact integrableOn_petersson_slash_T_p_lower_slash_SL' p hp f g
    ((q.out : SL(2, ℤ))⁻¹ * q₀.out)
    (hyperbolicMeasure_Gamma1_fundDomain_PSL_lt_top (N := N))

/-! ### Bad-prime fiber-count reconciliation `c_p = c_N` (coprimality-free)

The trace engine carries the `Γ_p(A)` fiber-count `c_p`, while `petN` carries the `Γ₁(N)`
fiber-count `c_N`. The reconciliation `c_p = c_N` is the bijection
`slGamma_p_αToGamma1 A` restricted to the `[1]`-fibers, exactly as in the coprime
`ConcreteFamily.slToPslQuot_fiberCard_Gamma_p_α_T_p_lower_eq_fiberCard`. The only
coprimality-touching ingredient there is `center_mem_Gamma_p_α_T_p_lower_iff_mem_Gamma1`
(`-I ∈ Γ_p(A) ↔ -I ∈ Γ₁(N)`), which we re-prove here directly from `conjGL`-invariance of
the center (conjugation fixes `±I` in `GL(2,ℝ)`), with no coprimality. -/

open CongruenceSubgroup in
open CongruenceSubgroup in
omit [NeZero N] in
/-- `-I ∈ Γ_p(A) ↔ -I ∈ Γ₁(N)` (`A = diag(p,1)`), coprimality-free: conjugation by any
`GL(2,ℝ)` element fixes the central image `±I`, so `z ∈ conjGL Γ₁ A ↔ z ∈ Γ₁` for central
`z`. -/
private theorem center_mem_Gamma_p_α_T_p_lower_iff_mem_Gamma1'
    (p : ℕ) (hp : 0 < p) {z : SL(2, ℤ)} (hz : z ∈ Subgroup.center SL(2, ℤ)) :
    z ∈ Gamma_p_α (N := N) (T_p_lower p hp) ↔ z ∈ Gamma1 N := by
  rw [Gamma_p_α, Subgroup.mem_inf]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  rw [mem_conjGL]
  refine ⟨z, h, ?_⟩
  -- `z` central ⇒ `z` is a scalar matrix ⇒ `mapGL z` is central in `GL(2,ℝ)`,
  -- so conjugation by `A = diag(p,1)` fixes it.
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hz
  obtain ⟨r, _, hr⟩ := hz
  set A : GL (Fin 2) ℝ := (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ)) (T_p_lower p hp)
  have hz_scalar : ((toGL ((map (Int.castRingHom ℝ)) z)) : Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.scalar (Fin 2) ((r : ℤ) : ℝ) := by
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, ← hr]
    ext i j
    rw [Matrix.map_apply, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.diagonal_apply, apply_ite (Int.castRingHom ℝ)]
    simp
  have hcomm : Commute (A : Matrix (Fin 2) (Fin 2) ℝ)
      ((toGL ((map (Int.castRingHom ℝ)) z)) : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [hz_scalar]
    exact (Matrix.scalar_commute _ (fun r' ↦ Commute.all _ r') _).symm
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    hcomm.eq, mul_assoc, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.GeneralLinearGroup.coe_one, mul_one]

omit [NeZero N] in
open CongruenceSubgroup in
/-- Center crux (coprimality-free mirror of
`ConcreteFamily.Gamma1_coset_iff_Gamma_p_α_coset_of_center_fiber`). -/
private theorem Gamma1_coset_iff_Gamma_p_α_coset_of_center_fiber'
    (p : ℕ) (hp : 0 < p) (g₁ g₂ z₁ z₂ : SL(2, ℤ))
    (hz₁ : z₁ ∈ Subgroup.center SL(2, ℤ))
    (hz₂ : z₂ ∈ Subgroup.center SL(2, ℤ))
    (hg₁ : g₁ * z₁ ∈ Gamma_p_α (N := N) (T_p_lower p hp))
    (hg₂ : g₂ * z₂ ∈ Gamma_p_α (N := N) (T_p_lower p hp)) :
    g₁⁻¹ * g₂ ∈ Gamma1 N ↔ g₁⁻¹ * g₂ ∈ Gamma_p_α (N := N) (T_p_lower p hp) := by
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
  have hL₁ : (g₁ * z₁)⁻¹ ∈ Gamma_p_α (N := N) (T_p_lower p hp) :=
    (Gamma_p_α (N := N) (T_p_lower p hp)).inv_mem hg₁
  refine ⟨fun h ↦ ?_, fun h ↦ (Gamma_p_α_le_Gamma1 _) h⟩
  have hmid : (z₁ * z₂⁻¹) * (g₂ * z₂) ∈ Gamma1 N := by
    have h2 := (Gamma1 N).mul_mem ((Gamma_p_α_le_Gamma1 _) hg₁) h
    rwa [← mul_assoc, mul_inv_cancel, one_mul] at h2
  have hz_mem : z₁ * z₂⁻¹ ∈ Gamma1 N := by
    have h2 := (Gamma1 N).mul_mem hmid ((Gamma1 N).inv_mem ((Gamma_p_α_le_Gamma1 _) hg₂))
    rwa [mul_assoc, mul_inv_cancel, mul_one] at h2
  have hz_memP : z₁ * z₂⁻¹ ∈ Gamma_p_α (N := N) (T_p_lower p hp) :=
    (center_mem_Gamma_p_α_T_p_lower_iff_mem_Gamma1' p hp hzc).mpr hz_mem
  exact (Gamma_p_α (N := N) (T_p_lower p hp)).mul_mem hL₁
    ((Gamma_p_α (N := N) (T_p_lower p hp)).mul_mem hz_memP hg₂)

open CongruenceSubgroup in
/-- `slGamma_p_αToGamma1 A` maps the `Γ_p(A)`-fiber of `[1]` into the `Γ₁`-fiber of `[1]`.
Coprimality-free mirror of `ConcreteFamily.slGamma_p_αToGamma1_maps_into_Gamma1_fiber`. -/
private theorem slGamma_p_αToGamma1_maps_into_Gamma1_fiber'
    (p : ℕ) (hp : 0 < p)
    (q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp))
    (hq : slToPslQuot_Gamma_p_α (N := N) (T_p_lower p hp) q =
      (QuotientGroup.mk (1 : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) (T_p_lower p hp))) :
    slToPslQuot (N := N) (slGamma_p_αToGamma1 (N := N) (T_p_lower p hp) q) =
      (QuotientGroup.mk (1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ imageGamma1_PSL N) := by
  induction q using QuotientGroup.induction_on with | _ g => ?_
  rw [slToPslQuot_Gamma_p_α_mk] at hq
  rw [slGamma_p_αToGamma1_mk, slToPslQuot_mk]
  obtain ⟨z, hz, hgz⟩ := (pslQuot_eq_one_iff_exists_center_mem _ g).mp hq
  exact (pslQuot_eq_one_iff_exists_center_mem _ g).mpr
    ⟨z, hz, (Gamma_p_α_le_Gamma1 _) hgz⟩

open CongruenceSubgroup in
omit [NeZero N] in
/-- `slGamma_p_αToGamma1 A` is injective on the `Γ_p(A)`-fiber of `[1]`. Coprimality-free
mirror of `ConcreteFamily.slGamma_p_αToGamma1_injective_on_Gamma_p_α_fiber`. -/
private theorem slGamma_p_αToGamma1_injective_on_Gamma_p_α_fiber'
    (p : ℕ) (hp : 0 < p)
    (q₁ q₂ : SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp))
    (hq₁ : slToPslQuot_Gamma_p_α (N := N) (T_p_lower p hp) q₁ =
      (QuotientGroup.mk (1 : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) (T_p_lower p hp)))
    (hq₂ : slToPslQuot_Gamma_p_α (N := N) (T_p_lower p hp) q₂ =
      (QuotientGroup.mk (1 : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) (T_p_lower p hp)))
    (heq : slGamma_p_αToGamma1 (N := N) (T_p_lower p hp) q₁ =
      slGamma_p_αToGamma1 (N := N) (T_p_lower p hp) q₂) :
    q₁ = q₂ := by
  induction q₁ using QuotientGroup.induction_on with | _ g₁ => ?_
  induction q₂ using QuotientGroup.induction_on with | _ g₂ => ?_
  rw [slToPslQuot_Gamma_p_α_mk] at hq₁ hq₂
  rw [slGamma_p_αToGamma1_mk, slGamma_p_αToGamma1_mk, QuotientGroup.eq] at heq
  obtain ⟨z₁, hz₁, hgz₁⟩ := (pslQuot_eq_one_iff_exists_center_mem _ g₁).mp hq₁
  obtain ⟨z₂, hz₂, hgz₂⟩ := (pslQuot_eq_one_iff_exists_center_mem _ g₂).mp hq₂
  rw [QuotientGroup.eq]
  exact (Gamma1_coset_iff_Gamma_p_α_coset_of_center_fiber' p hp g₁ g₂ z₁ z₂
    hz₁ hz₂ hgz₁ hgz₂).mp heq

open CongruenceSubgroup in
/-- `slGamma_p_αToGamma1 A` is surjective onto the `Γ₁`-fiber of `[1]`. Coprimality-free
mirror of `ConcreteFamily.slGamma_p_αToGamma1_surjective_onto_Gamma1_fiber`. -/
private theorem slGamma_p_αToGamma1_surjective_onto_Gamma1_fiber'
    (p : ℕ) (hp : 0 < p)
    (q : SL(2, ℤ) ⧸ Gamma1 N)
    (hq : slToPslQuot (N := N) q =
      (QuotientGroup.mk (1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ imageGamma1_PSL N)) :
    ∃ a : SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp),
      slToPslQuot_Gamma_p_α (N := N) (T_p_lower p hp) a =
        (QuotientGroup.mk (1 : PSL(2, ℤ)) :
          PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) (T_p_lower p hp)) ∧
      slGamma_p_αToGamma1 (N := N) (T_p_lower p hp) a = q := by
  induction q using QuotientGroup.induction_on with | _ g => ?_
  rw [slToPslQuot_mk] at hq
  obtain ⟨z, hz, hgz⟩ := (pslQuot_eq_one_iff_exists_center_mem _ g).mp hq
  refine ⟨QuotientGroup.mk z⁻¹, ?_, ?_⟩
  · rw [slToPslQuot_Gamma_p_α_mk]
    refine (pslQuot_eq_one_iff_exists_center_mem _ z⁻¹).mpr ⟨z, hz, ?_⟩
    rw [inv_mul_cancel]
    exact (Gamma_p_α (N := N) (T_p_lower p hp)).one_mem
  · rw [slGamma_p_αToGamma1_mk, QuotientGroup.eq, inv_inv,
      (Subgroup.mem_center_iff.mp hz g).symm]
    exact hgz

open CongruenceSubgroup in
/-- **Bad-prime fiber-count reconciliation** `c_p = c_N` (coprimality-free mirror of
`ConcreteFamily.slToPslQuot_fiberCard_Gamma_p_α_T_p_lower_eq_fiberCard`). -/
private theorem slToPslQuot_fiberCard_Gamma_p_α_T_p_lower_eq_fiberCard'
    (p : ℕ) (hp : 0 < p) :
    slToPslQuot_fiberCard_Gamma_p_α (N := N) (T_p_lower p hp) =
      slToPslQuot_fiberCard N := by
  classical
  rw [slToPslQuot_fiberCard_Gamma_p_α, slToPslQuot_fiberCard]
  refine Finset.card_bij
    (fun q _ ↦ slGamma_p_αToGamma1 (N := N) (T_p_lower p hp) q) ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact slGamma_p_αToGamma1_maps_into_Gamma1_fiber' p hp q hq
  · intro q₁ hq₁ q₂ hq₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq₁ hq₂
    exact slGamma_p_αToGamma1_injective_on_Gamma_p_α_fiber' p hp q₁ q₂ hq₁ hq₂ heq
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨a, ha₁, ha₂⟩ := slGamma_p_αToGamma1_surjective_onto_Gamma1_fiber' p hp q hq
    exact ⟨a, by simp [ha₁], ha₂⟩

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **[T006-b-L4]** The bad-prime Petersson adjoint identity `petN (U_p f) g = petN f (U_p* g)`
with `U_p* = w_N U_p w_N⁻¹` (DS Ex 5.5.1(b) + Prop 5.5.2(b), `ds.txt:14599`/`:14446`).
Its deep core is the generic double-coset adjoint **T006-b-L4.1** (Prop 5.5.2(b)), whose
per-summand step `peterssonInner_slash_adjoint` already exists. -/
theorem petN_badUp_eq_petN_badUpAdjoint
    (p : ℕ) [NeZero p] (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_n_cusp k p f) g = petN f (badUpAdjoint p g) := by
  set q₀ : SL(2, ℤ) ⧸ Gamma1 N := QuotientGroup.mk 1
  have hadjoint := petN_doubleCoset_adjoint
    (s := (Finset.univ : Finset (Fin p)))
    (β := fun b : Fin p ↦ (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ))
    (α := T_p_lower p hp.pos)
    (f := f) (g := g) (F := heckeT_n_cusp k p f)
    (g' := (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)))
    (q₀ := q₀)
    (fun b _ ↦ glMap_T_p_upper_det_pos p hp.pos b.val)
    (badUp_coe_eq_sum_slashes p hp hpN f)
    (fun b _ ↦ slash_peterssonAdj_glMap_T_p_upper_eq_slash_T_p_lower p hp.pos b.val g)
    (fun γ hγ ↦ by
      rw [ModularForm.SL_slash,
        show (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) =
          ((T_p_lower p hp.pos).map (Rat.castHom ℝ) : GL (Fin 2) ℝ) from rfl]
      exact slash_α_Gamma_p_α_invariant_cuspForm (T_p_lower p hp.pos) g hγ)
    (fun b _ ↦ nullMeasurableSet_glPos_smul_Gamma1_fundDomain_PSL
      (glMap_T_p_upper_det_pos p hp.pos b.val))
    (by
      intro b₁ _ b₂ _ hne
      refine aedisjoint_glMap_T_p_upper_pair hp.pos ?_
      intro h_eq
      apply hne
      have : (b₁.val : ℤ) = (b₂.val : ℤ) := by omega
      exact Fin.ext (by exact_mod_cast this))
    (fun b _ ↦ integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure g f
      (T_p_upper p hp.pos b.val)
      (hyperbolicMeasure_Gamma1_fundDomain_PSL_lt_top (N := N)))
    (integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure f g
      (T_p_lower p hp.pos)
      (by
        simp only [Finset.mem_univ, Set.iUnion_true]
        refine (measure_iUnion_le _).trans_lt ?_
        rw [tsum_fintype]
        exact ENNReal.sum_lt_top.mpr fun b _ ↦
          measure_glPos_smul_Gamma1_fundDomain_lt_top _
            (glMap_T_p_upper_det_pos p hp.pos b.val)))
    (h_int_trace_FD' p hp.pos f g)
    (h_int_tr_FD' p hp.pos f g q₀)
    (h_int_FD' p hp.pos f g)
    (slToPslQuot_fiberCard_Gamma_p_α_T_p_lower_eq_fiberCard' p hp.pos)
    (isFundamentalDomain_BadHecke_tiles p hp hpN)
  rw [hadjoint, traceSlash_badPrime_eq_badUpAdjoint p hp hpN g q₀,
    petN_eq_setIntegral_Gamma1_fundDomain_PSL f (badUpAdjoint p g)]
  -- The two integrands agree: `⇑(badUpAdjoint p g)` is definitionally
  -- `(frickeScalar)⁻¹ • ⇑(w_N U_p w_N g)` (`badUpAdjoint_apply` + `CuspForm.coe_smul`).
  congr 1

/-- `U_p* = w_N U_p w_N⁻¹` preserves the extended old subspace — assembled from L2 (`w_N`)
and L3 (`U_p`). -/
theorem badUpAdjoint_mem_cuspFormsOldExtended
    (p : ℕ) [NeZero p] (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hg : g ∈ cuspFormsOldExtended N k) :
    badUpAdjoint p g ∈ cuspFormsOldExtended N k := by
  rw [badUpAdjoint_apply]
  exact (cuspFormsOldExtended N k).smul_mem _
    (frickeOperatorCusp_mem_cuspFormsOldExtended _
      (heckeT_n_cusp_divN_mem_cuspFormsOldExtended p hp hpN _
        (frickeOperatorCusp_mem_cuspFormsOldExtended g hg)))

/-- **[T006-b]** A bad prime `p ∣ N` preserves the extended new subspace:
`f ∈ cuspFormsNewExtended N k ⟹ U_p f ∈ cuspFormsNewExtended N k` (Diamond–Shurman
Prop 5.6.2 at bad primes).  **Fricke route** (DS Ex 5.6.3(d)): for `g ∈ oldExt`,
`petN (U_p f) g = petN f (U_p* g) = 0` since `U_p* g ∈ oldExt` and `f ⊥ oldExt`. -/
theorem heckeT_n_cusp_preserves_cuspFormsNewExtended_bad'
    (p : ℕ) [NeZero p] (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ cuspFormsNewExtended N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNewExtended N k := by
  intro g hg
  rw [petN_badUp_eq_petN_badUpAdjoint p hp hpN f g]
  exact hf _ (badUpAdjoint_mem_cuspFormsOldExtended p hp hpN g hg)

end HeckeRing.GL2

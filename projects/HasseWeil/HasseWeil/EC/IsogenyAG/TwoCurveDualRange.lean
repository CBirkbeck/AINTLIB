/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.IsogenyAG.TwoCurveFixedField
import HasseWeil.EC.IsogenyKernel

/-!
# The two-curve `K̄`-dual range inclusion `Im([deg φ]*) ⊆ Im(φ*)` (Silverman III.6.1)

For a separable two-curve isogeny `φ : E₁ → E₂` over a field, the deep input of Silverman III.6.1
(descent half) is the range inclusion `Im([deg φ]_{E₁}*) ⊆ Im(φ*)` of the source-`E₁`
endomorphism `[deg φ]` into the pullback of `φ`.

This file assembles it from the **fixed-field route** over a base where `#ker φ = deg φ`:

  `Im([m]_{E₁}*) ⊆ Fix(ker φ acting by translation) = Im(φ*)`,

where `m = deg φ`.  The two halves:

* **The easy inclusion** `Im([m]*) ⊆ Fix(ker φ)` (`rangeIncl_mulByInt_le_fixed_twoCurve`): every
  `k ∈ ker φ` is `m`-torsion (`ker φ ⊆ E₁[m]`, Lagrange, from `#ker φ = deg φ`), and `[m] ∘ τ_k =
  [m]` when `[m]k = 0`, so `τ_k` fixes `Im([m]*)`.  This is the source-`E₁` endomorphism covariance
  `hnu_mulByInt_general` read for `ker φ` (the `[m]`-genuineness is the division-polynomial fact,
  field-general).
* **The hard equality** `Fix(ker φ) = Im(φ*)` (`fixedField_hfix_twoCurve`, the two-curve III.4.10c
  fixed-field equality), from the per-`φ` translation covariance `xy_family` + the count.

So the genuine geometric inputs are exactly the two facts read for a two-curve `φ`: the translation
covariance `xy_family` and the cardinality match `#ker φ = deg φ`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.4.10–4.11, III.6.1.
-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

namespace Isogeny

/-- **The easy inclusion `Im([m]_{E₁}*) ⊆ Fix(ker φ)`, two-curve** (Silverman III.6.1, Lagrange
half).  For `φ : E₁ → E₂` with `#ker φ = deg φ`, every `k ∈ ker φ` is `(deg φ)`-torsion, so the
source-`E₁` endomorphism `[deg φ]` satisfies `[deg φ] ∘ τ_k = [deg φ]`, i.e. `τ_k` fixes
`Im([deg φ]*)`.  Phrased: every element of `Im([deg φ]_{E₁}*)` is fixed by every kernel
translation. -/
theorem rangeIncl_mulByInt_le_fixed_twoCurve (φ : Isogeny W₁ W₂)
    [Finite φ.kernel] (h_card : Nat.card φ.kernel = φ.degree)
    (hm : (φ.degree : ℤ) ≠ 0) :
    ∀ z ∈ (HasseWeil.mulByInt_pullbackAlgHom W₁ (φ.degree : ℤ) hm).range,
      ∀ σ ∈ (Set.range (fun k : φ.kernel => translateAlgEquivOfPoint W₁ k.val)), σ z = z := by
  rintro z ⟨w, rfl⟩ σ ⟨k, rfl⟩
  -- identify the explicit pullback AlgHom with `(mulByInt …).pullback`
  have hpb : (mulByInt W₁ (φ.degree : ℤ)).pullback =
      HasseWeil.mulByInt_pullbackAlgHom W₁ (φ.degree : ℤ) hm := dif_neg hm
  -- `[m] k = (deg φ) • k = 0` for `k ∈ ker φ` (Lagrange), so `τ_{[m]k} = τ_0 = refl`.
  have hk0 : (mulByInt W₁ (φ.degree : ℤ)).toAddMonoidHom k.val = 0 := by
    rw [mulByInt_apply, natCast_zsmul]
    exact kernel_nsmul_degree_eq_zero φ h_card k.property
  show (translateAlgEquivOfPoint W₁ k.val)
      ((HasseWeil.mulByInt_pullbackAlgHom W₁ (φ.degree : ℤ) hm) w) =
    (HasseWeil.mulByInt_pullbackAlgHom W₁ (φ.degree : ℤ) hm) w
  -- `[m]`-covariance: `τ_k([m]* w) = [m]*(τ_{[m]k} w)` (field-general genuine leaf on E₁).
  rw [← hpb, WeilPairing.hcomm_of_isGenuineWith W₁ (mulByInt W₁ (φ.degree : ℤ))
    (HasseWeil.mulByInt_isGenuineWith_general W₁ (φ.degree : ℤ) hm) k.val
    (WeilPairing.mapTranslateGenericPoint_mulByInt W₁ (φ.degree : ℤ) k.val) w, hk0]
  rfl

/-- **The two-curve `K̄`-dual range inclusion `Im([deg φ]_{E₁}*) ⊆ Im(φ*)`** (Silverman III.6.1,
descent half) — assembled from the easy inclusion + the two-curve fixed-field equality.

Inputs (the genuine geometric content, read for a two-curve `φ`):
* `h_xy_family` — the per-`φ` kernel-translation covariance on `x_gen₂`/`y_gen₂`;
* `h_card` — the cardinality match `#ker φ = deg φ` (Silverman III.4.10c).

The `[deg φ]`-side endomorphism covariance (the easy inclusion) is fully discharged
(`rangeIncl_mulByInt_le_fixed_twoCurve`); the `Fix(ker φ) = Im(φ*)` step is
`fixedField_hfix_twoCurve`. -/
theorem mulByInt_deg_rangeIncl_twoCurve (φ : Isogeny W₁ W₂)
    (h_xy_family : ∀ k : φ.kernel,
      (translateAlgEquivOfPoint W₁ k.val (φ.pullback (x_gen W₂)) = φ.pullback (x_gen W₂)) ∧
      (translateAlgEquivOfPoint W₁ k.val (φ.pullback (y_gen W₂)) = φ.pullback (y_gen W₂)))
    (h_card : Nat.card φ.kernel = φ.degree) :
    (HasseWeil.mulByInt_pullbackAlgHom W₁ (φ.degree : ℤ)
        (by exact_mod_cast (degree_pos_twoCurve φ).ne')).range ≤
      φ.pullback.range := by
  have hcov : ∀ k : φ.kernel, ∀ z : W₂.FunctionField,
      translateAlgEquivOfPoint W₁ k.val (φ.pullback z) = φ.pullback z :=
    fun k z => translate_pullback_invariance_of_xy_twoCurve φ k.val
      (h_xy_family k).1 (h_xy_family k).2 z
  haveI : Finite φ.kernel := finite_kernel_of_hcov_twoCurve φ hcov
  have hm : (φ.degree : ℤ) ≠ 0 := by exact_mod_cast (degree_pos_twoCurve φ).ne'
  rintro z hz
  rw [fixedField_hfix_twoCurve φ h_xy_family h_card z]
  exact rangeIncl_mulByInt_le_fixed_twoCurve φ h_card hm z hz

end Isogeny

end HasseWeil
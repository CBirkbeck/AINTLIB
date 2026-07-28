/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WP.Weight
import «Adic spaces».WP.RestrictedComplete
import «Adic spaces».FJP.CDVFBase
import «Adic spaces».FJP.FiniteJetRings

/-!
# The weighted-parity algebra `𝒜` ([WP] §6.1)

For a CDVF-style base `K` (the FJP-CDVF conventions: nontrivially normed ultrametric
complete field, uniformizers via `FiniteJetOver.Uniformizer`) and a weight `w : ℕ → ℕ`,
this file constructs the weighted-parity algebra as the **support subring**
(rem:formalization convention)

  `𝒜 = {∑_{(a,ν) ∈ S} c_{a,ν} W^a U^ν : c_{a,ν} → 0}`   ([WP] eq:parity-algebra)

inside the ambient radius-one restricted power-series ring `Amb K` over the variable
index `ℕ` (index `0` = `W`, index `n ≥ 1` = `U_n`), together with its instance stack
(complete normed commutative ring; Huber/Tate via the uniformizer scaling bundle,
following `FJP/Over/JetRings.lean`) and the coefficient / monomial API.

The paper's example is `w = id`; general `w` uniformly covers the Tate extensions
`𝒜⟨V_1,…,V_s⟩` (shifted weight, [WP] §6.5) — see `WP/Weight.lean`.
-/

@[expose] public section

namespace WeightedParity

open MvPowerSeries Filter FiniteJetOver

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (w : ℕ → ℕ)

/-- The ambient ring `K⟨W, U_1, U_2, …⟩`: radius-one restricted power series in
countably many variables ([WP] prop:parity-uniform-domain's "countable restricted Tate
algebra").  Index `0` is `W`; index `n ≥ 1` is `U_n`. -/
abbrev Amb : Type _ :=
  MvPowerSeries.Restricted K (fun _ : ℕ => (1 : ℝ))

/-- The weighted-parity support subring `𝒜 ⊂ K⟨W,U⟩` ([WP] eq:parity-algebra as a
support condition, per the rem:formalization support-subring convention): restricted
series whose coefficients are supported on the monoid `S`. -/
noncomputable def wpSupport : Subring (Amb K) where
  carrier := {f | ∀ t : ℕ →₀ ℕ, ¬ WPMem w t → MvPowerSeries.coeff t f.1 = 0}
  zero_mem' := by sorry
  one_mem' := by sorry
  add_mem' := by sorry
  neg_mem' := by sorry
  mul_mem' := by sorry

/-- The weighted-parity algebra `𝒜` ([WP] eq:parity-algebra), as the coerced support
subring — all normed-ring structure is inherited from the ambient via the mathlib
`SubringClass` instances (the `JetA` pattern, `FJP/Over/JetRings.lean:294`). -/
abbrev WPA : Type _ := ↥(wpSupport K w)

/-- The support subring is closed in the ambient (each membership condition is the
kernel of a continuous coefficient functional). -/
theorem isClosed_wpSupport : IsClosed ((wpSupport K w : Set (Amb K))) := by sorry

instance : CompleteSpace (WPA K w) :=
  (isClosed_wpSupport K w).completeSpace_coe

instance : NormOneClass (WPA K w) := ⟨by sorry⟩

/-! ### Coefficients and monomials -/

/-- The `t`-th coefficient of an element of `𝒜`. -/
noncomputable def coeffA (t : ℕ →₀ ℕ) (f : WPA K w) : K :=
  MvPowerSeries.coeff t f.1.1

@[simp] theorem coeffA_of_not_wpMem {t : ℕ →₀ ℕ} (ht : ¬ WPMem w t) (f : WPA K w) :
    coeffA K w t f = 0 := by sorry

theorem norm_coeffA_le (t : ℕ →₀ ℕ) (f : WPA K w) : ‖coeffA K w t f‖ ≤ ‖f‖ := by sorry

theorem norm_eq_iSup_coeffA (f : WPA K w) :
    ‖f‖ = ⨆ t : ℕ →₀ ℕ, ‖coeffA K w t f‖ := by sorry

theorem coeffA_injective : Function.Injective (fun f (t : ℕ →₀ ℕ) => coeffA K w t f) := by
  sorry

/-- The monomial `c·W^{t 0}·U^{t'}` of `𝒜`, for an allowed exponent `t ∈ S`. -/
noncomputable def wpMonomial {t : ℕ →₀ ℕ} (_ : WPMem w t) (c : K) : WPA K w := by sorry

@[simp] theorem coeffA_wpMonomial {t : ℕ →₀ ℕ} (ht : WPMem w t) (c : K) (s : ℕ →₀ ℕ) :
    coeffA K w s (wpMonomial K w ht c) = if s = t then c else 0 := by sorry

theorem norm_wpMonomial {t : ℕ →₀ ℕ} (ht : WPMem w t) (c : K) :
    ‖wpMonomial K w ht c‖ = ‖c‖ := by sorry

/-- The variable `W` ([WP] §6.1). -/
noncomputable def Wa : WPA K w := wpMonomial K w (wpMem_single_zero w 1) 1

/-- The allowed generator `Y_n = W^{w n} U_n` ([WP] eq:finite-stage-substitution at
general weight). -/
noncomputable def Ya (n : ℕ) : WPA K w := wpMonomial K w (wpMem_single_add_single w n) 1

/-- The even generator `Z_n = U_n²` ([WP] eq:finite-stage-substitution). -/
noncomputable def Za (n : ℕ) : WPA K w := wpMonomial K w (wpMem_two_nsmul_single w n 1) 1

/-! ### Scalars and the uniformizer bundle -/

/-- The constant embedding `K →+* 𝒜` (the `constA` pattern of
`FJP/Over/JetRings.lean:521`). -/
noncomputable def constA : K →+* WPA K w := by sorry

@[simp] theorem norm_constA (x : K) : ‖constA K w x‖ = ‖x‖ := by sorry

/-- Constants scale the Gauss norm exactly (the `norm_constC_mul` pattern,
`FJP/Over/JetRings.lean:535`; coefficientwise from `norm_mul` of the field). -/
theorem norm_constA_mul (x : K) (f : WPA K w) :
    ‖constA K w x * f‖ = ‖x‖ * ‖f‖ := by sorry

variable {K w} in
/-- The pseudouniformizer of `𝒜` attached to a uniformizer of `K`
(`piA` pattern, `FJP/Over/JetRings.lean:563`). -/
noncomputable def piW (ϖ : Uniformizer K) : WPA K w := constA K w ϖ.val

variable {K w} in
@[simp] theorem norm_piW (ϖ : Uniformizer K) : ‖piW (w := w) ϖ‖ = ‖ϖ.val‖ := by sorry

variable {K w} in
theorem norm_piW_lt_one (ϖ : Uniformizer K) : ‖piW (w := w) ϖ‖ < 1 := by sorry

variable {K w} in
theorem norm_piW_pos (ϖ : Uniformizer K) : 0 < ‖piW (w := w) ϖ‖ := by sorry

variable {K w} in
theorem isUnit_piW (ϖ : Uniformizer K) : IsUnit (piW (w := w) ϖ) := by sorry

variable {K w} in
theorem norm_piW_mul (ϖ : Uniformizer K) (f : WPA K w) :
    ‖piW ϖ * f‖ = ‖piW (w := w) ϖ‖ * ‖f‖ := by sorry

variable {K w} in
/-- `𝒜` is a Huber ring (via the scaling bundle,
`FiniteJet.isHuberRing_of_scale`; the `isHuberRing_JetA` pattern,
`FJP/Over/JetRings.lean:656`). -/
theorem isHuberRing_WPA (ϖ : Uniformizer K) : IsHuberRing (WPA K w) :=
  FiniteJet.isHuberRing_of_scale (piW ϖ) (isUnit_piW ϖ) (norm_piW_lt_one ϖ)
    (norm_piW_pos ϖ) (norm_piW_mul ϖ)

variable {K w} in
/-- `𝒜` is a Tate ring ([WP] prop:parity-uniform-domain: "the Tate property follows
from (eq:parity-algebra) and the topologically nilpotent unit ϖ"). -/
theorem isTateRing_WPA (ϖ : Uniformizer K) : IsTateRing (WPA K w) :=
  FiniteJet.isTateRing_of_scale (piW ϖ) (isUnit_piW ϖ) (norm_piW_lt_one ϖ)
    (norm_piW_pos ϖ) (norm_piW_mul ϖ)

/-! ### The plus subring and completeness for the right uniformity
(the `JetA` instance block, `FJP/Over/JetRings.lean:711-755`) -/

/-- Unconditional Huber instance via a norm-window element (the
`FJP/Over/Functoriality.lean:160` pattern — no uniformizer needed). -/
instance : IsHuberRing (WPA K w) := by sorry

instance : IsTateRing (WPA K w) := by sorry

noncomputable instance : ValuationSpectrum.PlusSubring (WPA K w) := by sorry

instance : ValuationSpectrum.IsRingOfIntegralElements
    ((ValuationSpectrum.ringPlus (WPA K w) : Subring (WPA K w))) := by sorry

instance : IsUniformAddGroup (WPA K w) :=
  SeminormedAddCommGroup.to_isUniformAddGroup

instance : @CompleteSpace (WPA K w) (IsTopologicalAddGroup.rightUniformSpace (WPA K w)) := by
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

/-! ### The unit ball ([WP] eq:parity-ring-of-definition) -/

/-- The ring of definition `𝒜₀` is the unit ball of the Gauss norm
([WP] eq:parity-ring-of-definition: coefficients in `k°`). -/
theorem mem_unitBall_iff_forall_coeffA (f : WPA K w) :
    f ∈ FiniteJet.unitBall (WPA K w) ↔ ∀ t, ‖coeffA K w t f‖ ≤ 1 := by sorry

end WeightedParity

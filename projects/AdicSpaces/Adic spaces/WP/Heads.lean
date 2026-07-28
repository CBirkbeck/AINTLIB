/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WP.Algebra
import «Adic spaces».FJP.CDVFNoetherian
import «Adic spaces».SheafyRing

/-!
# The affinoid heads `𝒜_N` ([WP] §6.1, lem:finite-stage-normal-form)

The `N`-th head is the **support subalgebra** of monomials involving only
`W, U_1, …, U_N` (documented route change: the paper's quotient presentation
`𝒜_N = k⟨W,Y,Z⟩/(Y_n² − W^{2n}Z_n)` is never formed; the load-bearing content of
lem:finite-stage-normal-form — the unique factorization eq:parity-factorization and
the resulting finite free module structure over the even Tate subalgebra
`T_N = k⟨W,Z_1,…,Z_N⟩` — is established directly on the support side).

Deliverables: the head subring and its instance stack; noetherianity of the head and
of its unit ball (finite free module over the Tate algebra `K⟨W,Z⟩`, whose
noetherianity is the FJP-CDVF `Uniformizer.isNoetherianRing_P` package); **strong**
noetherianity (same argument after adjoining Tate variables — NEVER inferred from
noetherianity alone, per the prior-B2 log); head sheafiness via Wedhorn 8.28(b)
(`isSheafyFor_of_stronglyNoetherianTate` / `isSheafy_of_stronglyNoetherian_828b`);
density of the union of heads ([WP] eq:A-completion-of-heads).
-/

@[expose] public section

namespace WeightedParity

open FiniteJetOver ValuationSpectrum

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (w : ℕ → ℕ) (N : ℕ)

/-- The `N`-th head support subring: allowed monomials involving only `W, U_1,…,U_N`
([WP] lem:finite-stage-normal-form). -/
noncomputable def wpHeadSupport : Subring (Amb K) where
  carrier := {f | ∀ t : ℕ →₀ ℕ, ¬ HeadMem w N t → MvPowerSeries.coeff t f.1 = 0}
  zero_mem' := by sorry
  one_mem' := by sorry
  add_mem' := by sorry
  neg_mem' := by sorry
  mul_mem' := by sorry

/-- The `N`-th affinoid head `𝒜_N` ([WP] §6.1). -/
abbrev WPHead : Type _ := ↥(wpHeadSupport K w N)

theorem wpHeadSupport_le_wpSupport : wpHeadSupport K w N ≤ wpSupport K w := by sorry

theorem wpHeadSupport_mono {N M : ℕ} (h : N ≤ M) :
    wpHeadSupport K w N ≤ wpHeadSupport K w M := by sorry

/-- The isometric inclusion `𝒜_N →+* 𝒜` ([WP]: "The transition maps are isometric"). -/
noncomputable def headIncl : WPHead K w N →+* WPA K w :=
  Subring.inclusion (wpHeadSupport_le_wpSupport K w N)

@[simp] theorem norm_headIncl (x : WPHead K w N) : ‖headIncl K w N x‖ = ‖x‖ := by sorry

theorem isClosed_wpHeadSupport : IsClosed ((wpHeadSupport K w N : Set (Amb K))) := by
  sorry

instance : CompleteSpace (WPHead K w N) :=
  (isClosed_wpHeadSupport K w N).completeSpace_coe

instance : NormOneClass (WPHead K w N) := ⟨by sorry⟩

/-- The constant embedding `K →+* 𝒜_N`. -/
noncomputable def constHead : K →+* WPHead K w N := by sorry

variable {K w N} in
/-- The pseudouniformizer of the head. -/
noncomputable def piHead (ϖ : Uniformizer K) : WPHead K w N := constHead K w N ϖ.val

variable {K w N} in
theorem norm_piHead_lt_one (ϖ : Uniformizer K) : ‖piHead (w := w) (N := N) ϖ‖ < 1 := by
  sorry

variable {K w N} in
theorem norm_piHead_pos (ϖ : Uniformizer K) : 0 < ‖piHead (w := w) (N := N) ϖ‖ := by
  sorry

variable {K w N} in
theorem isUnit_piHead (ϖ : Uniformizer K) : IsUnit (piHead (w := w) (N := N) ϖ) := by
  sorry

variable {K w N} in
theorem norm_piHead_mul (ϖ : Uniformizer K) (f : WPHead K w N) :
    ‖piHead ϖ * f‖ = ‖piHead (w := w) (N := N) ϖ‖ * ‖f‖ := by sorry

variable {K w N} in
theorem isHuberRing_WPHead (ϖ : Uniformizer K) : IsHuberRing (WPHead K w N) :=
  FiniteJet.isHuberRing_of_scale (piHead ϖ) (isUnit_piHead ϖ) (norm_piHead_lt_one ϖ)
    (norm_piHead_pos ϖ) (norm_piHead_mul ϖ)

variable {K w N} in
theorem isTateRing_WPHead (ϖ : Uniformizer K) : IsTateRing (WPHead K w N) :=
  FiniteJet.isTateRing_of_scale (piHead ϖ) (isUnit_piHead ϖ) (norm_piHead_lt_one ϖ)
    (norm_piHead_pos ϖ) (norm_piHead_mul ϖ)

/-- Unconditional Huber instance via a norm-window element (the
`FJP/Over/Functoriality.lean:160` pattern — no uniformizer needed). -/
instance : IsHuberRing (WPHead K w N) := by sorry

instance : IsTateRing (WPHead K w N) := by sorry

noncomputable instance : ValuationSpectrum.PlusSubring (WPHead K w N) := by sorry

instance : ValuationSpectrum.IsRingOfIntegralElements
    ((ValuationSpectrum.ringPlus (WPHead K w N) : Subring (WPHead K w N))) := by sorry

instance : IsUniformAddGroup (WPHead K w N) :=
  SeminormedAddCommGroup.to_isUniformAddGroup

instance : @CompleteSpace (WPHead K w N)
    (IsTopologicalAddGroup.rightUniformSpace (WPHead K w N)) := by
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

/-- The heads are integral domains (isometric subrings of the multiplicative-norm
ambient; [WP] thm:parity-rationally-reduced: "The affinoid algebra `𝒜_N` is a domain
by lem:finite-stage-normal-form"). -/
instance : IsDomain (WPHead K w N) := by sorry

/-! ### Noetherianity via the finite free module structure
([WP] lem:finite-stage-normal-form: `𝒜_N ≅ ⊕_{ε ∈ {0,1}^N} k⟨W,Z⟩·Y^ε`) -/

/-- The even Tate subalgebra `T_N = k⟨W, Z_1,…,Z_N⟩` of the head: allowed monomials
with all `U`-exponents even (hence weight `0`).  [WP] eq:finite-stage-normal-form's
coefficient ring. -/
noncomputable def wpEvenSupport : Subring (Amb K) where
  carrier := {f | ∀ t : ℕ →₀ ℕ,
    ¬ (HeadMem w N t ∧ ∀ n, n ≠ 0 → t n % 2 = 0) → MvPowerSeries.coeff t f.1 = 0}
  zero_mem' := by sorry
  one_mem' := by sorry
  add_mem' := by sorry
  neg_mem' := by sorry
  mul_mem' := by sorry

/-- `T_N` is isometrically isomorphic to the Tate algebra `K⟨T_0,…,T_N⟩ = P K (N+1)`
(the exponent-halving reindexing `(a, 2ν) ↦ (a, ν)`; [WP]
eq:finite-stage-normal-form). -/
noncomputable def evenSupportEquiv :
    ↥(wpEvenSupport K w N) ≃+* FiniteJet.GraphKoszul.P K (N + 1) := by sorry

theorem norm_evenSupportEquiv (x : ↥(wpEvenSupport K w N)) :
    ‖evenSupportEquiv K w N x‖ = ‖x‖ := by sorry

/-- The head is a finite module over its even Tate subalgebra — the formal content of
the rank-`2^N` free normal form [WP] eq:finite-stage-normal-form. -/
theorem moduleFinite_head_over_even :
    letI : Algebra ↥(wpEvenSupport K w N) (WPHead K w N) :=
      (Subring.inclusion (by sorry : wpEvenSupport K w N ≤ wpHeadSupport K w N)).toAlgebra
    Module.Finite ↥(wpEvenSupport K w N) (WPHead K w N) := by sorry

variable {K} in
/-- **The heads are noetherian** ([WP]: "`𝒜_N` is affinoid"; via
`IsNoetherianRing.of_finite` over `T_N ≅ P K (N+1)`, whose noetherianity is
`FiniteJetOver.Uniformizer.isNoetherianRing_P`). -/
theorem isNoetherianRing_WPHead (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsNoetherianRing (WPHead K w N) := by sorry

variable {K} in
/-- The unit ball of the head is noetherian (needed by the graph-Koszul layer at the
head; same finite-module argument over the unit ball of `P K (N+1)`,
`FiniteJetOver.Uniformizer.isNoetherianRing_unitBall_P`). -/
theorem isNoetherianRing_unitBall_WPHead (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsNoetherianRing (FiniteJet.unitBall (WPHead K w N)) := by sorry

variable {K} in
/-- **The heads are strongly noetherian** ([WP] §6.4: "Since `𝒜_N` is affinoid" —
the input to the head graph-Koszul bounds and to Wedhorn 8.28(b).  Proven for every
Tate-variable count by the same finite-free-module argument at head
`K⟨W,Z,T_1,…,T_k⟩`; NEVER inferred from noetherianity (prior-B2 T-SUM-6/T-Q4). -/
theorem isStronglyNoetherian_WPHead (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsStronglyNoetherian (WPHead K w N) := by sorry

variable {K} in
/-- **The heads are sheafy** (Wedhorn 8.28(b) at the head;
`isSheafy_of_stronglyNoetherian_828b` — the `isSheafy_JetB/C/D` pattern,
`FJP/Over/SheafTransfer.lean:63`). -/
theorem isSheafy_WPHead (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    ValuationSpectrum.IsSheafy (WPHead K w N) := by sorry

/-! ### Density of the heads ([WP] eq:A-completion-of-heads) -/

variable {K w} in
/-- Truncation to a head: every element of `𝒜` is approximated to any `ϖ`-power
precision by an element of some head ([WP] eq:A-completion-of-heads:
"`𝒜 = closure(⋃_N 𝒜_N)`"). -/
theorem exists_head_approx (ϖ : Uniformizer K) (f : WPA K w) (ℓ : ℕ) :
    ∃ (N : ℕ) (g : WPHead K w N),
      ‖f - headIncl K w N g‖ ≤ ‖ϖ.val‖ ^ ℓ * ‖f‖ := by sorry

end WeightedParity

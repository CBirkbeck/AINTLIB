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
  zero_mem' := fun t _ => by
    show MvPowerSeries.coeff t (0 : MvPowerSeries ℕ K) = 0
    simp
  one_mem' := fun t ht => by
    show MvPowerSeries.coeff t (1 : MvPowerSeries ℕ K) = 0
    classical
    rcases eq_or_ne t 0 with rfl | h0
    · exact absurd ⟨wpMem_zero w, fun n _ => rfl⟩ ht
    · rw [MvPowerSeries.coeff_one, if_neg h0]
  add_mem' := fun {f} {g} hf hg t ht => by
    show MvPowerSeries.coeff t (f.1 + g.1) = 0
    rw [map_add, hf t ht, hg t ht, add_zero]
  neg_mem' := fun {f} hf t ht => by
    show MvPowerSeries.coeff t (-f.1) = 0
    rw [map_neg, hf t ht, neg_zero]
  mul_mem' := fun {f} {g} hf hg t ht => by
    show MvPowerSeries.coeff t (f.1 * g.1) = 0
    classical
    rw [MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hpt : p.1 + p.2 = t := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    subst hpt
    by_cases h1 : HeadMem w N p.1
    · by_cases h2 : HeadMem w N p.2
      · exact absurd (h1.add h2) ht
      · rw [hg p.2 h2, mul_zero]
    · rw [hf p.1 h1, zero_mul]

/-- The `N`-th affinoid head `𝒜_N` ([WP] §6.1). -/
abbrev WPHead : Type _ := ↥(wpHeadSupport K w N)

theorem wpHeadSupport_le_wpSupport : wpHeadSupport K w N ≤ wpSupport K w :=
  fun f hf t ht => hf t fun hh => ht hh.1

theorem wpHeadSupport_mono {N M : ℕ} (h : N ≤ M) :
    wpHeadSupport K w N ≤ wpHeadSupport K w M :=
  fun f hf t ht => hf t fun hh => ht (hh.mono h)

/-- The isometric inclusion `𝒜_N →+* 𝒜` ([WP]: "The transition maps are isometric"). -/
noncomputable def headIncl : WPHead K w N →+* WPA K w :=
  Subring.inclusion (wpHeadSupport_le_wpSupport K w N)

@[simp] theorem norm_headIncl (x : WPHead K w N) : ‖headIncl K w N x‖ = ‖x‖ := rfl

theorem isClosed_wpHeadSupport : IsClosed ((wpHeadSupport K w N : Set (Amb K))) := by
  have h := isClosed_setOf_coeff_eq_zero (R := K) (σ := ℕ) {t | HeadMem w N t}
  convert h using 1
  ext g
  exact Iff.rfl

instance : CompleteSpace (WPHead K w N) :=
  (isClosed_wpHeadSupport K w N).completeSpace_coe

instance : NormOneClass (WPHead K w N) :=
  ⟨by rw [show ‖(1 : WPHead K w N)‖ = ‖((1 : WPHead K w N) : Amb K)‖ from rfl]
      exact norm_one⟩

/-- The constant embedding `K →+* 𝒜_N`. -/
noncomputable def constHead : K →+* WPHead K w N where
  toFun x :=
    ⟨⟨MvPowerSeries.C x, MvPowerSeries.isRestrictedGauss_C _ _⟩, fun s hs => by
      show MvPowerSeries.coeff s (MvPowerSeries.C (σ := ℕ) x) = 0
      classical
      rw [MvPowerSeries.coeff_C, if_neg (by
        intro h; subst h; exact hs ⟨wpMem_zero w, fun n _ => rfl⟩)]⟩
  map_one' := Subtype.ext (Subtype.ext (map_one (MvPowerSeries.C (σ := ℕ) (R := K))))
  map_mul' x y := Subtype.ext (Subtype.ext (map_mul (MvPowerSeries.C (σ := ℕ)) x y))
  map_zero' := Subtype.ext (Subtype.ext (map_zero (MvPowerSeries.C (σ := ℕ) (R := K))))
  map_add' x y := Subtype.ext (Subtype.ext (map_add (MvPowerSeries.C (σ := ℕ)) x y))

@[simp] theorem headIncl_constHead (x : K) :
    headIncl K w N (constHead K w N x) = constA K w x := rfl

variable {K w N} in
/-- The pseudouniformizer of the head. -/
noncomputable def piHead (ϖ : Uniformizer K) : WPHead K w N := constHead K w N ϖ.val

variable {K w N} in
theorem norm_piHead (ϖ : Uniformizer K) : ‖piHead (w := w) (N := N) ϖ‖ = ‖ϖ.val‖ := by
  rw [show ‖piHead (w := w) (N := N) ϖ‖ =
    ‖headIncl K w N (constHead K w N ϖ.val)‖ from rfl, headIncl_constHead,
    norm_constA]

variable {K w N} in
theorem norm_piHead_lt_one (ϖ : Uniformizer K) : ‖piHead (w := w) (N := N) ϖ‖ < 1 := by
  rw [norm_piHead]; exact ϖ.norm_val_lt_one

variable {K w N} in
theorem norm_piHead_pos (ϖ : Uniformizer K) : 0 < ‖piHead (w := w) (N := N) ϖ‖ := by
  rw [norm_piHead]; exact ϖ.norm_val_pos

variable {K w N} in
theorem isUnit_piHead (ϖ : Uniformizer K) : IsUnit (piHead (w := w) (N := N) ϖ) :=
  ϖ.isUnit_val.map (constHead K w N)

variable {K w N} in
theorem norm_constHead_mul (x : K) (f : WPHead K w N) :
    ‖constHead K w N x * f‖ = ‖x‖ * ‖f‖ := by
  rw [show ‖constHead K w N x * f‖ =
      ‖headIncl K w N (constHead K w N x * f)‖ from rfl,
    map_mul, headIncl_constHead, norm_constA_mul]
  rfl

variable {K w N} in
theorem norm_piHead_mul (ϖ : Uniformizer K) (f : WPHead K w N) :
    ‖piHead ϖ * f‖ = ‖piHead (w := w) (N := N) ϖ‖ * ‖f‖ := by
  rw [norm_piHead]
  exact norm_constHead_mul ϖ.val f

variable {K w N} in
theorem isHuberRing_WPHead (ϖ : Uniformizer K) : IsHuberRing (WPHead K w N) :=
  FiniteJet.isHuberRing_of_scale (piHead ϖ) (isUnit_piHead ϖ) (norm_piHead_lt_one ϖ)
    (norm_piHead_pos ϖ) (norm_piHead_mul ϖ)

variable {K w N} in
theorem isTateRing_WPHead (ϖ : Uniformizer K) : IsTateRing (WPHead K w N) :=
  FiniteJet.isTateRing_of_scale (piHead ϖ) (isUnit_piHead ϖ) (norm_piHead_lt_one ϖ)
    (norm_piHead_pos ϖ) (norm_piHead_mul ϖ)

variable {K w N} in
@[simp] theorem norm_constHead (x : K) : ‖constHead K w N x‖ = ‖x‖ := by
  rw [show ‖constHead K w N x‖ = ‖headIncl K w N (constHead K w N x)‖ from rfl,
    headIncl_constHead, norm_constA]

/-- Unconditional Huber instance via a norm-window element (the
`FJP/Over/Functoriality.lean:160` pattern — no uniformizer needed). -/
instance : IsHuberRing (WPHead K w N) := by
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window' K
  exact FiniteJet.isHuberRing_of_scale (constHead K w N c) (hcu.map (constHead K w N))
    (by rw [norm_constHead]; exact hc1) (by rw [norm_constHead]; exact hc0)
    (fun f => by rw [norm_constHead_mul, norm_constHead])

instance : IsTateRing (WPHead K w N) := by
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window' K
  exact FiniteJet.isTateRing_of_scale (constHead K w N c) (hcu.map (constHead K w N))
    (by rw [norm_constHead]; exact hc1) (by rw [norm_constHead]; exact hc0)
    (fun f => by rw [norm_constHead_mul, norm_constHead])

noncomputable instance : ValuationSpectrum.PlusSubring (WPHead K w N) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (WPHead K w N)⟩

instance : ValuationSpectrum.IsRingOfIntegralElements
    ((ValuationSpectrum.ringPlus (WPHead K w N) : Subring (WPHead K w N))) :=
  FiniteJet.isRingOfIntegralElements_powerBounded

instance : IsUniformAddGroup (WPHead K w N) :=
  SeminormedAddCommGroup.to_isUniformAddGroup

instance : @CompleteSpace (WPHead K w N)
    (IsTopologicalAddGroup.rightUniformSpace (WPHead K w N)) := by
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

variable {K w N} in
theorem norm_wphead_mul (a b : WPHead K w N) : ‖a * b‖ = ‖a‖ * ‖b‖ := by
  show ‖((a * b : WPHead K w N) : Amb K)‖ = _
  rw [show ((a * b : WPHead K w N) : Amb K) = (a : Amb K) * (b : Amb K) from rfl,
    norm_restricted_mul_general (fun x y => norm_mul x y)]
  rfl

instance : Nontrivial (WPHead K w N) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h2 := congrArg (norm : WPHead K w N → ℝ) h
  rw [norm_zero, norm_one] at h2
  exact zero_ne_one h2

instance : NoZeroDivisors (WPHead K w N) := by
  refine ⟨fun {a b} hab => ?_⟩
  by_contra hne
  push_neg at hne
  obtain ⟨ha, hb⟩ := hne
  have hna : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha
  have hnb : (0 : ℝ) < ‖b‖ := norm_pos_iff.mpr hb
  have hm := norm_wphead_mul (K := K) (w := w) (N := N) a b
  rw [hab, norm_zero] at hm
  nlinarith

/-- The heads are integral domains (isometric subrings of the multiplicative-norm
ambient; [WP] thm:parity-rationally-reduced: "The affinoid algebra `𝒜_N` is a domain
by lem:finite-stage-normal-form"). -/
instance : IsDomain (WPHead K w N) :=
  NoZeroDivisors.to_isDomain _

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

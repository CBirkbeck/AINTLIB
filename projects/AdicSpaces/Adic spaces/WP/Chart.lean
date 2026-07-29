/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WP.CoeffLocalization
import «Adic spaces».WP.Reduced
import «Adic spaces».Uniform

/-!
# The bad chart `ℬ = 𝒜⟨W/ϖ⟩` ([WP] §6.2)

The chart datum is `(W; ϖ)` — a genuine rational datum since `ϖ` is a unit
([WP] line 838).  Its entries lie in the `N = 0` head `𝒜_0 = K⟨W⟩`, so the chart is
the `N = 0` instance of the coefficientwise localization: `ℬ ≅ TailC0` over the head
localization `Q₀ = K⟨W⟩⟨X⟩/(ϖX − W) ≅ K⟨X⟩` with twist element `ρ = ϖX`.  In these
twisted coordinates the paper's weighted model ([WP] eq:weighted-chart-lattice /
eq:weighted-chart-norm) is EXACTLY the plain sup-norm `TailC0` — e.g.
`T_n = X^n U_n = ϖ^{−w n}·e_{δ_n}` is the single family with coefficient `ϖ^{−w n}`,
of norm `|ϖ|^{−w n}` (eq:Tn-power-norms).

Endpoints here ([WP] prop:weighted-chart-identification,
prop:weighted-chart-domain-nonuniform, prop-analogue of not-stable-uniformity):
`ℬ` is an integral domain (via the `Φ`-embedding into `MvPowerSeries` over the
domain `K⟨X⟩` — no classical input needed), `ℬ` is NOT uniform (the unbounded
power-bounded family `(T_n)`, needs the weight unbounded), and hence `𝒜` is not
stably uniform ([WP] thm 6.2 (4)).
-/

@[expose] public section

namespace WeightedParity

open ValuationSpectrum FiniteJetOver TopologicalRing

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (w : ℕ → ℕ)

variable {K w} in
open scoped Classical in
/-- The span of the chart pair is the unit ideal (`ϖ` is a unit; [WP] line 838:
"It is a genuine rational datum: the ideal `(ϖ,W)` is open"). -/
theorem span_chartPair_eq_top (ϖ : Uniformizer K) :
    Ideal.span (({WaHead K w 0, piHead ϖ} : Finset (WPHead K w 0)) :
      Set (WPHead K w 0)) = ⊤ := by
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ?_) (isUnit_piHead ϖ)
  rw [Finset.coe_insert, Finset.coe_singleton]
  exact Set.mem_insert_of_mem _ rfl

variable {K w} in
open scoped Classical in
/-- The head chart datum `(W; ϖ)` on the `N = 0` head `K⟨W⟩`
([WP] §6.2: "the datum `(W;ϖ)`"; project convention `s ∈ T`). -/
noncomputable def chartHeadDatum (ϖ : Uniformizer K) :
    RationalLocData (WPHead K w 0) :=
  genPieceDatum
    (FiniteJet.unitBallPod (piHead ϖ) (isUnit_piHead ϖ) (norm_piHead_lt_one ϖ)
      (norm_piHead_pos ϖ) (norm_piHead_mul ϖ))
    {WaHead K w 0, piHead ϖ} (piHead ϖ) (span_chartPair_eq_top ϖ)

variable {K w} in
open scoped Classical in
theorem chartHeadDatum_T (ϖ : Uniformizer K) :
    (chartHeadDatum (w := w) ϖ).T = {WaHead K w 0, piHead ϖ} := rfl

variable {K w} in
theorem chartHeadDatum_s (ϖ : Uniformizer K) :
    (chartHeadDatum (w := w) ϖ).s = piHead ϖ := rfl

variable {K w} in
/-- The chart datum is rational (`ϖ` is a unit, so `span {W, ϖ} = ⊤`;
[WP]: "It is a genuine rational datum: the ideal `(ϖ,W)` is open"). -/
theorem chartHeadDatum_isRational (ϖ : Uniformizer K) :
    (chartHeadDatum (w := w) ϖ).IsRational := by
  classical
  refine RationalLocData.isRational_of_span_eq_top ?_
  rw [chartHeadDatum_T]
  exact span_chartPair_eq_top ϖ

variable {K w} in
/-- The chart datum on `𝒜` — the lift of the head chart datum
(entries `W, ϖ`; [WP] §6.2). -/
noncomputable def chartDatum (ϖ : Uniformizer K) : RationalLocData (WPA K w) :=
  liftDatum (chartHeadDatum ϖ) (chartHeadDatum_isRational ϖ)

variable {K w} in
theorem chartDatum_isRational (ϖ : Uniformizer K) :
    (chartDatum (w := w) ϖ).IsRational :=
  liftDatum_isRational _ (chartHeadDatum_isRational ϖ)

/-! ### The chart head localization is `K⟨X⟩` -/

variable {K w} in
/-- At stage `0` the head support IS the even support (no odd generators, so the
evenness condition is vacuous). -/
theorem wpHeadSupport_zero_eq_even :
    wpHeadSupport K w 0 = wpEvenSupport K w 0 := by
  refine SetLike.ext fun f => ?_
  constructor
  · intro hf
    have hf' : ∀ t : ℕ →₀ ℕ, ¬ HeadMem w 0 t →
        MvPowerSeries.coeff t f.1 = 0 := hf
    show ∀ t : ℕ →₀ ℕ, ¬ EvenHeadMem w 0 t → MvPowerSeries.coeff t f.1 = 0
    intro t ht
    refine hf' t fun hh => ht ⟨hh, fun n hn => by
      rw [hh.2 n (Nat.pos_of_ne_zero hn)]⟩
  · intro hf
    have hf' : ∀ t : ℕ →₀ ℕ, ¬ EvenHeadMem w 0 t →
        MvPowerSeries.coeff t f.1 = 0 := hf
    show ∀ t : ℕ →₀ ℕ, ¬ HeadMem w 0 t → MvPowerSeries.coeff t f.1 = 0
    intro t ht
    exact hf' t fun he => ht he.1

variable {K w} in
/-- The `N = 0` head is the one-variable Tate algebra (`evenSupportEquiv` at the
degenerate stage). -/
noncomputable def headZeroEquiv : WPHead K w 0 ≃+* FiniteJet.GraphKoszul.P K 1 :=
  (RingEquiv.subringCongr (wpHeadSupport_zero_eq_even (K := K) (w := w))).trans
    (evenSupportEquiv K w 0)

variable {K w} in
theorem norm_headZeroEquiv (x : WPHead K w 0) :
    ‖headZeroEquiv (K := K) (w := w) x‖ = ‖x‖ := by
  rw [headZeroEquiv, RingEquiv.trans_apply, norm_evenSupportEquiv]
  rfl

variable {K} in
/-- `K⟨X⟩` is an integral domain (multiplicative Gauss norm). -/
theorem isDomain_P_one : IsDomain (FiniteJet.GraphKoszul.P K 1) := by
  have hmul : ∀ f g : FiniteJet.GraphKoszul.P K 1, ‖f * g‖ = ‖f‖ * ‖g‖ :=
    fun f g => norm_restricted_mul_general (fun a b => norm_mul a b) f g
  haveI : Nontrivial (FiniteJet.GraphKoszul.P K 1) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h1 := congrArg (fun z : FiniteJet.GraphKoszul.P K 1 => ‖z‖) h
    rw [show ‖(0 : FiniteJet.GraphKoszul.P K 1)‖ = 0 from norm_zero,
      show ‖(1 : FiniteJet.GraphKoszul.P K 1)‖ = 1 from norm_one] at h1
    linarith
  haveI : NoZeroDivisors (FiniteJet.GraphKoszul.P K 1) := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra hcon
    push_neg at hcon
    have h1 : ‖a * b‖ = 0 := by rw [hab, norm_zero]
    rw [hmul] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact hcon.1 (norm_eq_zero.mp h)
    · exact hcon.2 (norm_eq_zero.mp h)
  exact NoZeroDivisors.to_isDomain _

variable {K w} in
/-- The chart head model: `K⟨W⟩⟨X⟩/(ϖX − W) ≅ K⟨X⟩` via `W ↦ ϖX` (the classical
smooth chart; the univariate rescaling of `FJP/FiniteJetChart.lean:82`). -/
noncomputable def chartQHeadEquiv (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    QHead (chartHeadDatum (w := w) ϖ) ≃+* FiniteJet.GraphKoszul.P K 1 := by sorry

variable {K w} in
theorem chartQHeadEquiv_norm (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (x : QHead (chartHeadDatum (w := w) ϖ)) :
    ‖chartQHeadEquiv ϖ hK₀ x‖ = ‖x‖ := by sorry

variable {K w} in
/-- The chart head localization is an integral domain (transport from `K⟨X⟩`, whose
Gauss norm is multiplicative). -/
theorem isDomain_chartQHead (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsDomain (QHead (chartHeadDatum (w := w) ϖ)) := by sorry

/-! ### `ℬ` is a domain ([WP] prop:weighted-chart-domain-nonuniform, first half) -/

variable {K w} in
/-- **The bad chart is an integral domain** ([WP]
prop:weighted-chart-domain-nonuniform: "coefficientwise inclusion gives an injective
homomorphism `ℬ ↪ k⟨X,U_1,U_2,…⟩`; the target is a domain … therefore `ℬ` is a
domain" — realized through the `Φ`-embedding of the `TailC0` model into
`MvPowerSeries` over the domain `K⟨X⟩`). -/
theorem isDomain_chart (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsDomain (presheafValue (chartDatum (w := w) ϖ)) := by sorry

/-! ### `ℬ` is not uniform ([WP] prop:weighted-chart-domain-nonuniform, second half) -/

variable {K w} in
/-- The `T_n` family is power-bounded but unbounded in the `TailC0` chart model
([WP] eq:Tn-power-norms: `‖T_n^{2r}‖ = 1`, `‖T_n^{2r+1}‖ = |ϖ|^{−n}`; "The family
`(T_n)` is not bounded: if `ϖ^N T_n ∈ ℬ₀` then … `N ≥ n`").  Requires the weight
unbounded on the tail (`hwu`). -/
theorem not_isUniform_chartModel (hwu : ∀ M : ℕ, ∃ n : ℕ, 1 ≤ n ∧ M ≤ w n)
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    ¬ IsUniform
      (TailC0 w 0 (QHead (chartHeadDatum (w := w) ϖ))
        (rhoQ (chartHeadDatum ϖ))) := by sorry

variable {K w} in
/-- **The bad chart is not uniform** ([WP] prop:weighted-chart-domain-nonuniform:
"Hence `ℬ°` is unbounded and `ℬ` is not uniform"; transported along the
coefficientwise-localization model, the `not_isUniform_chart` pattern of
`FJP/Over/Chart.lean:1459`). -/
theorem not_isUniform_chart (hwu : ∀ M : ℕ, ∃ n : ℕ, 1 ≤ n ∧ M ≤ w n)
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    ¬ IsUniform (presheafValue (chartDatum (w := w) ϖ)) := by sorry

variable {K w} in
/-- **`𝒜` is not stably uniform** ([WP] thm 6.2, "In particular, failure of stable
uniformity need not be caused by a nilpotent in the bad rational localization"; the
`not_isStablyUniform_JetA` assembly, `FJP/Over/Chart.lean:1469`). -/
theorem not_isStablyUniform_WPA (hwu : ∀ M : ℕ, ∃ n : ℕ, 1 ≤ n ∧ M ≤ w n)
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    ¬ IsStablyUniform (WPA K w) := fun h =>
  not_isUniform_chart hwu ϖ hK₀ ⟨h.presheafValue_isUniform (chartDatum ϖ)⟩

variable {K w} in
/-- The bad chart is reduced — with NO classical input (a domain is reduced).  The
contrast with the FJP example ([WP] rem:second-example-relation: "Its bad chart
remains a domain"). -/
theorem isReduced_chart (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsReduced (presheafValue (chartDatum (w := w) ϖ)) := by sorry

end WeightedParity

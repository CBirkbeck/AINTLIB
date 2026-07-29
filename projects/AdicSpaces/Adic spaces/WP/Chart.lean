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
/-- The head chart datum `(W; ϖ)` on the `N = 0` head `K⟨W⟩`
([WP] §6.2: "the datum `(W;ϖ)`"; project convention `s ∈ T`). -/
noncomputable def chartHeadDatum (ϖ : Uniformizer K) :
    RationalLocData (WPHead K w 0) := by sorry

variable {K w} in
open scoped Classical in
theorem chartHeadDatum_T (ϖ : Uniformizer K) :
    (chartHeadDatum (w := w) ϖ).T = {WaHead K w 0, piHead ϖ} := by sorry

variable {K w} in
theorem chartHeadDatum_s (ϖ : Uniformizer K) :
    (chartHeadDatum (w := w) ϖ).s = piHead ϖ := by sorry

variable {K w} in
/-- The chart datum is rational (`ϖ` is a unit, so `span {W, ϖ} = ⊤`;
[WP]: "It is a genuine rational datum: the ideal `(ϖ,W)` is open"). -/
theorem chartHeadDatum_isRational (ϖ : Uniformizer K) :
    (chartHeadDatum (w := w) ϖ).IsRational := by sorry

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

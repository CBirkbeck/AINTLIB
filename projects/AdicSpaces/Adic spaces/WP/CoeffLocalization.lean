/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WP.Tail
import «Adic spaces».WP.Perturbation
import «Adic spaces».WP.Evaluation
import «Adic spaces».FJP.KoszulStrictClosed

/-!
# Coefficientwise localization ([WP] §6.4, prop:coefficientwise-localization)

The technical heart of the campaign.  For a rational datum `α` with entries in the
head `𝒜_N`, the completed rational localization of `𝒜` is computed coefficientwise
through the `c₀`-tail:

  `𝒜_α ≅ ⊕̂^{c₀}_μ P e_μ`,  `P = (𝒜_N)_α`   ([WP] eq:coefficientwise-localization)

Both sides are mediated by the graph model.  On the head, `P` is the quotient of
`𝒜_N⟨T_1,…,T_m⟩` by the (closed, by strong noetherianity + [WP] lem:koszul degree 0)
graph ideal — `QHead` below, a genuine normed ring; the bridge
`presheafValue ≃ QHead` is the `chartFwd`/`chartRev` pattern with the generic
evaluation gadget of `WP/Evaluation.lean`.  Over `𝒜`, the graph differential acts
coefficientwise, its image is closed BECAUSE of the norm-bounded lifts at the head
(`FiniteJet.GraphKoszul.exists_d1_lift_pow`, [WP]: "there is a constant `C` such that
every `y ∈ I` has a lift `x ∈ R^m` with `‖x‖ ≤ C‖y‖`"), and the quotient is the
twisted `c₀`-sum `TailC0` of `WP/Tail.lean` ([WP] eq:c0-quotient).

`cor:finite-head-presentation` then combines this with density of the heads and the
small perturbation lemma: EVERY rational localization of `𝒜` is a `TailC0` over a
head localization (`nonempty_headModelData`).
-/

@[expose] public section

set_option maxSynthPendingDepth 8

namespace WeightedParity

open ValuationSpectrum FiniteJetOver FiniteJet.GraphKoszul

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (w : ℕ → ℕ) (N : ℕ)

/-! ### Coefficientwise transport of `TailC0` -/

section Map

variable {P Q : Type*} [NormedCommRing P] [IsUltrametricDist P]
  [NormedCommRing Q] [IsUltrametricDist Q] {ρ : TwistElem P} {ρ' : TwistElem Q}
  {w' : ℕ → ℕ} {N' : ℕ}

/-- Coefficientwise functoriality of the twisted `c₀`-sum along a bounded twist-
compatible homomorphism ([WP] eq:coefficientwise-restriction: "the induced restriction
sends `∑ p_μ e_μ ↦ ∑ (p_μ|_Q) e_μ`"). -/
noncomputable def TailC0.map (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖)
    (hρ : φ ρ.val = ρ'.val) :
    TailC0 w' N' P ρ →+* TailC0 w' N' Q ρ' := by sorry

@[simp] theorem TailC0.coeff_map (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖)
    (hρ : φ ρ.val = ρ'.val) (x : TailC0 w' N' P ρ) (μ : TailIdx N') :
    TailC0.coeff μ (TailC0.map φ hφ hρ x) = φ (TailC0.coeff μ x) := by sorry

theorem TailC0.map_continuous (φ : P →+* Q) (hφ : ∀ p, ‖φ p‖ ≤ ‖p‖)
    (hρ : φ ρ.val = ρ'.val) :
    Continuous (TailC0.map (w' := w') (N' := N') φ hφ hρ) := by sorry

end Map

/-! ### The head graph model `QHead` -/

variable {K w N} in
/-- A chosen enumeration of the entries of a head rational datum. -/
noncomputable def datumEnum (DH : RationalLocData (WPHead K w N)) :
    Fin DH.T.card ≃ ↥DH.T := by sorry

variable {K w N} in
/-- The graph relations `s·T_i − t_i` of a head datum in `𝒜_N⟨T_1,…,T_m⟩`
([WP] eq:graph-ideal-definition). -/
noncomputable def headGraphRel (DH : RationalLocData (WPHead K w N)) :
    Fin DH.T.card → P (WPHead K w N) DH.T.card := fun i =>
  polyToP (MvPolynomial.C DH.s * MvPolynomial.X i -
    MvPolynomial.C ((datumEnum DH i : ↥DH.T) : WPHead K w N))

variable {K w N} in
/-- The head graph-model quotient `Q = 𝒜_N⟨T⟩/(sT_i − t_i)` ([WP] eq:graph-model;
the ideal is closed by [WP] lem:koszul at the strongly noetherian head, so no
separated quotient is needed). -/
noncomputable def QHead (DH : RationalLocData (WPHead K w N)) : Type _ :=
  P (WPHead K w N) DH.T.card ⧸ Ideal.span (Set.range (headGraphRel DH))

variable {K w N} in
noncomputable instance instCommRingQHead {DH : RationalLocData (WPHead K w N)} :
    CommRing (QHead DH) :=
  inferInstanceAs
    (CommRing (P (WPHead K w N) DH.T.card ⧸ Ideal.span (Set.range (headGraphRel DH))))

variable {K w N} in
/-- The quotient norm makes `QHead` a normed ring (the graph ideal is closed:
[WP] lem:koszul clause 3 / `FiniteJet.GraphKoszul.isClosed_graphIdeal`). -/
noncomputable instance instNormedCommRingQHead {DH : RationalLocData (WPHead K w N)} :
    NormedCommRing (QHead DH) := by sorry

variable {K w N} in
instance instUltraQHead {DH : RationalLocData (WPHead K w N)} :
    IsUltrametricDist (QHead DH) := by sorry

variable {K w N} in
instance instCompleteQHead {DH : RationalLocData (WPHead K w N)} :
    CompleteSpace (QHead DH) := by sorry

variable {K w N} in
/-- The twist element of the head model: the image of `W` (norm `≤ 1` since the
quotient map is norm-nonincreasing). -/
noncomputable def rhoQ (DH : RationalLocData (WPHead K w N)) : TwistElem (QHead DH) := by
  sorry

/-! ### The head bridge `presheafValue ≃ QHead` -/

variable {K w N} in
/-- **The head graph-model bridge**: the completed rational localization of the
strongly noetherian head is its graph quotient ([WP] eq:graph-model
`E_α ≅ P_E/J̄_{E,α}`; forward via `IsLocalization.Away.lift` — `s` is a unit in the
quotient by the Bezout trick of [WP] lem:koszul's proof — and back via the evaluation
gadget `restrictedEval` at the power-bounded tuple `T_i ↦ t_i/s`). -/
noncomputable def headLocEquiv (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    presheafValue DH ≃+* QHead DH := by sorry

variable {K w N} in
theorem headLocEquiv_continuous (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    Continuous (headLocEquiv ϖ hK₀ DH hDH) := by sorry

variable {K w N} in
theorem headLocEquiv_symm_continuous (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    Continuous (headLocEquiv ϖ hK₀ DH hDH).symm := by sorry

/-! ### The lifted datum and the coefficientwise model over `𝒜` -/

variable {K w N} in
/-- The lift of a head rational datum to `𝒜` (entries via `headIncl`, unit-ball pair
of definition; [WP] §6.4: the datum "lies in the finite head"). -/
noncomputable def liftDatum (DH : RationalLocData (WPHead K w N)) :
    RationalLocData (WPA K w) := by sorry

variable {K w N} in
open scoped Classical in
theorem liftDatum_T (DH : RationalLocData (WPHead K w N)) :
    (liftDatum DH).T = DH.T.image (headIncl K w N) := by sorry

variable {K w N} in
theorem liftDatum_s (DH : RationalLocData (WPHead K w N)) :
    (liftDatum DH).s = headIncl K w N DH.s := by sorry

variable {K w N} in
theorem liftDatum_isRational (DH : RationalLocData (WPHead K w N))
    (hDH : DH.IsRational) : (liftDatum DH).IsRational := by sorry

variable {K w N} in
/-- **Coefficientwise localization** ([WP] prop:coefficientwise-localization:
"There is a canonical topological algebra isomorphism `𝒜_α ≅ ⊕̂^{c₀}_μ P e_μ`").
The proof route: the graph ideal over `𝒜` is closed and computed coefficientwise via
the norm-bounded head lifts (`exists_d1_lift_pow`); the quotient is `TailC0`;
forward/backward maps by `IsLocalization.Away.lift` + `restrictedEval`. -/
noncomputable def coeffLocEquiv (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    presheafValue (liftDatum DH) ≃+* TailC0 w N (QHead DH) (rhoQ DH) := by sorry

variable {K w N} in
theorem coeffLocEquiv_continuous (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    Continuous (coeffLocEquiv ϖ hK₀ DH hDH) := by sorry

variable {K w N} in
theorem coeffLocEquiv_symm_continuous (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    Continuous (coeffLocEquiv ϖ hK₀ DH hDH).symm := by sorry

variable {K w N} in
/-- Compatibility of the two bridges on canonical images of head elements: the
`𝒜`-model of `ρ(headIncl x)` is the `μ = 0` family at the head model of `ρ(x)`. -/
theorem coeffLocEquiv_canonicalMap_headIncl (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) (x : WPHead K w N) :
    coeffLocEquiv ϖ hK₀ DH hDH ((liftDatum DH).canonicalMap (headIncl K w N x)) =
      TailC0.ofHead (headLocEquiv ϖ hK₀ DH hDH (DH.canonicalMap x)) := by sorry

/-! ### Every rational localization of `𝒜` is of finite-head form
([WP] cor:finite-head-presentation) -/

variable {K w} in
/-- A finite-head model of a rational localization of `𝒜`
([WP] cor:finite-head-presentation / eq:arbitrary-finite-head-presentation). -/
structure HeadModelData (D : RationalLocData (WPA K w)) : Type _ where
  /-- The head stage. -/
  N : ℕ
  /-- The head datum. -/
  DH : RationalLocData (WPHead K w N)
  /-- The head datum is rational. -/
  hDH : DH.IsRational
  /-- The lifted datum cuts the same rational subset as `D`. -/
  hopen : rationalOpen (liftDatum DH).T (liftDatum DH).s = rationalOpen D.T D.s
  /-- The model isomorphism. -/
  e : presheafValue D ≃+* TailC0 w N (QHead DH) (rhoQ DH)
  /-- Forward continuity. -/
  he : Continuous e
  /-- Backward continuity. -/
  he' : Continuous e.symm

variable {K w} in
/-- **Finite-head presentation of every rational localization**
([WP] cor:finite-head-presentation: perturb the datum into a head via density of the
heads and lem:small-perturbation; the retracted Bezout relation makes the perturbed
datum rational in the head; conclude by prop:coefficientwise-localization). -/
theorem nonempty_headModelData (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (D : RationalLocData (WPA K w)) (hD : D.IsRational) :
    Nonempty (HeadModelData D) := by sorry

end WeightedParity

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Hasse.PoleDivisorFallback
import HasseWeil.Hasse.HasseInfrastructure
import HasseWeil.Hasse.OpenLemmaPrimitives

/-!
# L6 (V.1.1 proof identity) via the pole-divisor route — witness-parametric closure

This file ships the **L6 composition theorem** (Open Lemma 6 of
`Hasse/OpenLemmas.lean`, the `sepDegree(1 − π) = #E(F_q)` identity, project
shorthand "V.1.3" — but actually V.1.1 proof, per the R13 D-R13-A-02
clarification) as a **witness-parametric closure** consuming the shipped
axiom-clean composer
`pc_sepDeg_eq_pointCount_of_computationA_and_lemma5`
(`Hasse/PoleDivisorFallback.lean:2647`).

The closure factors three substantive obligations as explicit hypotheses:
* **B3** (Bridge A in IntermediateField-finrank form):
  `Module.finrank K⟮γ*x⟯ K(E) = 2 · γ.degree` — the tower-formula content.
* **A10/A11/A12** (Sinf-side prime-fiber witnesses): the per-prime pole
  orders, inertia degrees, and the cardinality of primes-over-`xIdeal`.
* **Per-point pole orders and support-card** (projectiveDivisorOf-side):
  the bookkeeping witnesses for Lemma 5.

These witnesses already have witness-parametric closures shipped in:
* `lemma5_of_pole_orders_and_support_card` (Lemma 5, axiom-clean).
* `finrank_gamma_pullback_x_eq_projectiveDivisorOf_sum` (Bridge A + B
  composition, axiom-clean).
* The L3/L4/L5 witness forms at `Hasse/OpenLemmaPrimitives.lean`
  (witness-parametric closures shipped R23 Worker-B beastmode).

This file's contribution: assemble the call into the shipped composer
and expose a clean signature taking the substantive witnesses as inputs
and discharging `(isogOneSub_negFrobenius W hq).sepDegree = pointCount
W.toAffine` (= L6 = Witness #3).

## References

* Silverman, *The Arithmetic of Elliptic Curves*, V.1.1 proof (book p.
  138; NOT V.1.3 which is the character-sum corollary).
* `tickets/EXECUTION-PLAN-R23.md` — Phase B (B3, B4, B5).
* `tickets/hasse/T-V-1-003-card-Eq-eq-deg.md` — the project's V-1-003 spec.
-/

open WeierstrassCurve HasseWeil.Curves
open HasseWeil.Curves.RamificationAtInfinity

namespace HasseWeil

namespace Conditional

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-! ## B3 — Bridge A in IntermediateField-finrank-equals-2·degree form

The brief's B3 ticket spec: `[K(E) : K(γ*x)] = 2 · γ.degree` in
`IntermediateField.adjoin` form (not the `LinfAt` form, per the R20
D-R20-A-01 diamond avoidance).

The substantive proof composes the standard tower argument:
* `K → K⟮γ*x⟯ ⊆ γ.pullback.fieldRange ⊆ K(E)`.
* `[K(E) : γ.pullback.fieldRange] = γ.degree` (by definition).
* `[γ.pullback.fieldRange : K⟮γ*x⟯] = [K(E) : K(x_gen)] = 2` (via the
  `gammaBar` AlgEquiv and `finrank_functionField_eq_two`).
* Multiply: `[K(E) : K⟮γ*x⟯] = 2 · γ.degree`.

R23 Worker-B beastmode 2026-05-19 ships this as a **witness-parametric
closure** (status NEW→P). The substantive tower argument is factored
out as the hypothesis `h_tower_witness`; the closure trivially passes
the hypothesis to the L6 composer. The remaining obligation is the
finrank-tower formula proper.
-/

omit [Fintype K] in
/-- **UPPER tower step (axiom-clean)**: for any isogeny `φ : W → W`,
`Module.finrank φ.pullback.fieldRange K(E) = φ.degree`. Direct
adaptation of `frobenius_finrank_eq_fieldRange_finrank` to arbitrary
isogeny pullbacks. The proof transfers the pullback-twisted finrank
`@Module.finrank K(E) K(E) _ _ φ.toAlgebra.toModule` (= φ.degree by
definition) across `gammaBar = AlgEquiv.ofInjectiveField φ.pullback`
to the fieldRange-form, via `Algebra.finrank_eq_of_equiv_equiv` with
i = gammaBar and j = id. -/
theorem finrank_pullback_fieldRange_eq_degree
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (φ : Isogeny W.toAffine W.toAffine) :
    Module.finrank φ.pullback.fieldRange W.toAffine.FunctionField = φ.degree := by
  -- gammaBar : K(E) ≃ₐ[K] φ.pullback.fieldRange (injective pullback).
  let gammaBar : W.toAffine.FunctionField ≃ₐ[K] ↥φ.pullback.fieldRange :=
    AlgEquiv.ofInjectiveField φ.pullback
  -- Transfer the finrank across gammaBar (with refl on K(E)).
  have h := @Algebra.finrank_eq_of_equiv_equiv
    W.toAffine.FunctionField W.toAffine.FunctionField _ _
    φ.toAlgebra
    (↥φ.pullback.fieldRange) W.toAffine.FunctionField _ _ _
    gammaBar.toRingEquiv (RingEquiv.refl _) ?_
  · -- φ.degree = @Module.finrank K(E) K(E) _ _ φ.toAlgebra.toModule (definition).
    exact h.symm
  · -- Commuting square: algebraMap φ.pullback.fieldRange K(E) ∘ gammaBar = (refl) ∘ φ.pullback.
    -- i.e., (gammaBar y).val = φ.pullback y.
    ext y
    show ((gammaBar y) : W.toAffine.FunctionField) = φ.pullback y
    rfl

/- NOTE: A `_from_lower_step` substantive composition was attempted but
the inclusion-algebra Module instance had a typeclass synthesis wall
(`letI inst_A_B : Algebra ↥A ↥B` didn't propagate `Module ↥A ↥B` to
`Module.Free.of_divisionRing`). Deferred to a future session — the
UPPER step is shipped axiom-clean above; the LOWER step requires
the gammaBar transfer adapted for IntermediateFields. -/

/-- **B3 (Bridge A in IntermediateField-form, witness-parametric)**:
the identity `Module.finrank K⟮γ*x⟯ K(E) = 2 · γ.degree` packaged as a
named theorem consumable by the L6 composer. The substantive tower
argument is factored as the witness `h_tower_witness`. -/
theorem bridgeA_intermediateField_finrank_eq_two_mul_degree_of_witness
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    -- Witness hypothesis: the tower formula `[K(E) : K⟮γ*x⟯] = 2 · γ.degree`.
    -- Substantive content factored per the project's witness-parametric
    -- closure pattern (status NEW→P). The full proof is the standard
    -- tower argument K → K⟮γ*x⟯ ⊆ γ.pullback.fieldRange ⊆ K(E) using
    -- `finrank_functionField_eq_two` (the LOWER step) and γ.degree
    -- (the UPPER step), with `gammaBar : K(E) ≃ₐ[K] γ.pullback.fieldRange`
    -- transferring the LOWER step through γ-pullback's injectivity.
    (h_tower_witness :
      Module.finrank
          (IntermediateField.adjoin K
            ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
              Set W.toAffine.FunctionField))
          W.toAffine.FunctionField =
        2 * (isogOneSub_negFrobenius W hq).degree) :
    Module.finrank
        (IntermediateField.adjoin K
          ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
            Set W.toAffine.FunctionField))
        W.toAffine.FunctionField =
      2 * (isogOneSub_negFrobenius W hq).degree :=
  h_tower_witness

/-! ## B4 — L6 V.1.1-proof identity composition (witness-parametric)

The brief's B4 ticket spec: compose A10/A11/A12/A13 + B3 + the shipped
axiom-clean composer `pc_sepDeg_eq_pointCount_of_computationA_and_lemma5`.

The closure takes:
* The witness for B3 (tower formula `[K(E) : K⟮γ*x⟯] = 2 · γ.degree`).
* The witness for Computation A bridge (the Riemann–Roch identity
  `[K(E) : K⟮γ*x⟯] = projectiveDivisorOf support sum`).
* The witness for Lemma 5 (`projectiveDivisorOf support sum = 2 · pointCount`).
* Witnesses #1 (`isogOneSub_negFrobenius_isSeparable`) and #2
  (`isogOneSub_negFrobenius_finiteDimensional`) — extracted from the
  shipped axiom-clean facts inside the proof.

The output: `(isogOneSub_negFrobenius W hq).sepDegree = pointCount
W.toAffine` (= L6 = Witness #3).
-/

/-- **B4 (L6 V.1.1-proof identity composition, witness-parametric)**:
discharges `(isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine`
from three substantive witnesses (Bridge A tower, ComputationA, Lemma 5)
via the shipped axiom-clean composer. -/
theorem l6_v_1_1_sepDegree_eq_pointCount_of_witnesses
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (hq : 2 ≤ Fintype.card K)
    -- Bridge A tower formula (B3 witness).
    (h_finrank_eq_2_deg :
      Module.finrank
          (IntermediateField.adjoin K
            ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
              Set W.toAffine.FunctionField))
          W.toAffine.FunctionField =
        2 * (isogOneSub_negFrobenius W hq).degree)
    -- ComputationA bridge (Riemann–Roch for principal divisors).
    (h_compA : ComputationA_bridge_pullback_x_gen W hq)
    -- Lemma 5: pole divisor sum = 2 · pointCount.
    (h_lemma5 :
      ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support.sum
        (fun P ↦ (-((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P)).toNat) =
        2 * pointCount W.toAffine) :
    (isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine := by
  -- Extract Witness #1 (γ.IsSeparable) from FiniteField.card' + shipped lemma.
  obtain ⟨p, hCharP, ⟨_, _⟩, hp_prime, _⟩ := FiniteField.card' K
  haveI : CharP K p := hCharP
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have h_pc_sep : (isogOneSub_negFrobenius W hq).IsSeparable :=
    HasseWeil.isogOneSub_negFrobenius_isSeparable (K := K) W p hq
  -- Witness #2 (FiniteDimensional) — axiom-clean.
  have h_pc_fin :
      @FiniteDimensional W.toAffine.FunctionField W.toAffine.FunctionField
        _ _ (isogOneSub_negFrobenius W hq).toAlgebra.toModule :=
    isogOneSub_negFrobenius_finiteDimensional W hq
  -- Apply the shipped composer.
  exact pc_sepDeg_eq_pointCount_of_computationA_and_lemma5 W
    h_pc_sep h_pc_fin h_compA h_finrank_eq_2_deg h_lemma5

/-! ## B5 — pc_sepDeg_eq_pointCount witness wire (witness-parametric)

The brief's B5: wire L6 (B4) into the `pc_sepDeg_eq_pointCount` field of the
`HasseWitnesses` bundle (the `witnessBundle` / `witness_pc_sepDeg` stubs in
`Hasse/OpenLemmas.lean` were deleted 2026-06-11; this witness-parametric wire
remains the field-shaped composition). The wiring takes the three substantive
obligations of B4 as explicit hypotheses at the call site.
-/

/-- **B5 (pc_sepDeg_eq_pointCount witness wire, witness-parametric)**:
the bundle field `pc_sepDeg_eq_pointCount` derived from B4 given the
three substantive obligations as hypotheses. Bridges between the L6
composition and the `HasseWitnesses`-bundle interface. -/
theorem witness_pc_sepDeg_of_witnesses
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (hq : 2 ≤ Fintype.card K)
    (h_finrank_eq_2_deg :
      Module.finrank
          (IntermediateField.adjoin K
            ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
              Set W.toAffine.FunctionField))
          W.toAffine.FunctionField =
        2 * (isogOneSub_negFrobenius W hq).degree)
    (h_compA : ComputationA_bridge_pullback_x_gen W hq)
    (h_lemma5 :
      ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support.sum
        (fun P ↦ (-((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P)).toNat) =
        2 * pointCount W.toAffine) :
    (isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine :=
  l6_v_1_1_sepDegree_eq_pointCount_of_witnesses W hq
    h_finrank_eq_2_deg h_compA h_lemma5

/-! ## B4-alt — comprehensive L6 closure from primitive witnesses

A finer-grained L6 closure that consumes the **primitive** lower-level
witnesses directly (rather than the composite `h_compA` and `h_lemma5`).
This form is useful when the downstream infrastructure that supplies the
witnesses is at the per-prime / per-point level rather than at the
divisor-sum level.

The closure composes:
1. `finrank_gamma_pullback_x_eq_projectiveDivisorOf_sum` (Bridge A + B,
   axiom-clean) ⟹ `h_compA`.
2. `lemma5_of_pole_orders_and_support_card` (Lemma 5 bookkeeping,
   axiom-clean) ⟹ `h_lemma5`.
3. `l6_v_1_1_sepDegree_eq_pointCount_of_witnesses` (B4 above) with the
   produced `h_compA`, `h_lemma5`, and the supplied B3 witness
   `h_finrank_eq_2_deg`.

Status: NEW→P (witness-parametric closure shipping the L6 conclusion
under the natural decomposition into Sinf-side and projectiveDivisorOf
-side per-witness obligations).
-/

/-- **B4-alt (L6 V.1.1 closure from primitive witnesses, witness-
parametric)**: a finer-grained form of B4 that takes the Sinf-side
per-prime witnesses and projectiveDivisorOf-side per-point witnesses
directly. -/
theorem l6_v_1_1_sepDegree_eq_pointCount_of_primitive_witnesses
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (hq : 2 ≤ Fintype.card K)
    [hf : Fact (Transcendental K
      ((isogOneSub_negFrobenius W hq).pullback (x_gen W))⁻¹)]
    (hMF : @Module.Finite (FractionRing (Polynomial K))
      (Curves.RamificationAtInfinity.LinfAt (k := K)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) _ _
      (Curves.RamificationAtInfinity.LinfAt.algebraFractionRing
        (k := K) ((isogOneSub_negFrobenius W hq).pullback (x_gen W))).toModule)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))
    -- Sinf-side witnesses (A11/A12 + cardinality):
    (h_uniform_pole_order :
      letI := data.commRing
      letI := data.isDedekindDomain
      letI := data.algPoly
      ∀ P ∈ IsDedekindDomain.primesOverFinset
        (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
        data.ordAt P = -2)
    (h_inertia_one :
      letI := data.commRing
      letI := data.isDedekindDomain
      letI := data.algPoly
      ∀ P ∈ IsDedekindDomain.primesOverFinset
        (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
        Ideal.inertiaDeg
          (Curves.RamificationAtInfinity.xIdeal (k := K)) P = 1)
    (h_card :
      letI := data.commRing
      letI := data.isDedekindDomain
      letI := data.algPoly
      (IsDedekindDomain.primesOverFinset
        (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier).card =
      pointCount W.toAffine)
    -- projectiveDivisorOf-side witnesses (per-point pole orders, support card):
    (h_pole_orders :
      ∀ P ∈ ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support,
      ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P).toNat = 0 ∧
      (-((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P)).toNat = 2)
    (h_support_card :
      ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support.card =
      pointCount W.toAffine)
    -- B3 tower witness (only remaining substantive obligation):
    (h_finrank_eq_2_deg :
      Module.finrank
          (IntermediateField.adjoin K
            ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
              Set W.toAffine.FunctionField))
          W.toAffine.FunctionField =
        2 * (isogOneSub_negFrobenius W hq).degree) :
    (isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine := by
  -- Step 1: derive `h_compA` via `finrank_gamma_pullback_x_eq_projectiveDivisorOf_sum`.
  have h_compA : ComputationA_bridge_pullback_x_gen W hq :=
    finrank_gamma_pullback_x_eq_projectiveDivisorOf_sum W hq hMF data
      h_uniform_pole_order h_inertia_one h_card h_pole_orders h_support_card
  -- Step 2: derive `h_lemma5` via `lemma5_of_pole_orders_and_support_card`.
  have h_lemma5 :
      ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support.sum
        (fun P ↦ (-((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P)).toNat) =
        2 * pointCount W.toAffine :=
    lemma5_of_pole_orders_and_support_card W hq h_pole_orders h_support_card
  -- Step 3: compose via B4.
  exact l6_v_1_1_sepDegree_eq_pointCount_of_witnesses W hq
    h_finrank_eq_2_deg h_compA h_lemma5

end Conditional

end HasseWeil

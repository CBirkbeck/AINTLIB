/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.AdditionPullback.SamePlace
import HasseWeil.WeilPairing.WallAGeometricRealization
import HasseWeil.WeilPairing.PencilSeparable

/-!
# The affine comap-valuation identity for the concrete `(1 − π)_{K̄}` (CoordHom-free, no `he1`)

This file instantiates the **general** isogeny same-place + `e = 1` machinery of
`AdditionPullback/SamePlace.lean` (`comap_pointValuation_isog_eq_affine`) at the *concrete*
base-changed `1 − π = oneSubFrobeniusIsogBaseChange` over `K̄`, to produce the **`affine` field** of
`ComapPointValuationWitness` — the affine-image comap identity
`(pointValuation P).comap (1−π)^* = pointValuation ⟨x, y, h_ns⟩` — with the unramifiedness `e = 1`
**derived from the invariant differential** (Silverman III.4.10c / III.5.5), *not* carried as an
`he1` hypothesis.

## What is discharged here vs. carried

`comap_pointValuation_isog_eq_affine` (the general headline, axiom-clean) needs, per affine-image
point `P`:

1. `omegaPullbackCoeff (1−π)_{K̄} ≠ 0` (separability) — **discharged** via the base-change transport
   `OmegaBaseChangeNeZero` from the `K`-level `omegaPullbackCoeff (1 − π) = 1` (the substantive
   Silverman III.5.5 content, `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one`, axiom-clean);
2. the two **generator residues** `(1−π)^*x_gen ≡ x`, `(1−π)^*y_gen ≡ y` modulo `m_P`, and
3. the **non-2-torsion-image unit** `ord_P ((1−π)^*u) = 0`.

Items (2)–(3) are the genuine *closed-point geometric compatibility* of the opaque base-changed
pullback `oneSubFrobeniusPullback_L` with the point map `id − π̄` — the closed-point analogue of the
generic-point Wall A realisation `oneSub_isGenuineWith_Kbar`.  They are isolated here as the single
named residual `OneSubAffineResidues` (the `1 − π` closed-point form of the `addIsog`-only centerpiece
`oneSub_coords_at_affine`), and `comap_pointValuation_oneSub_eq_affine` reduces the affine comap
identity to it with item (1) discharged.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, II.2.5–2.6, III.4.10c, III.5.5.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil IsogenyBaseChangeConcrete

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]

noncomputable local instance instDecEqACOSCC : DecidableEq (AlgebraicClosure K) := Classical.decEq _

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]

/-! ### Step 1 — separability of the concrete `(1 − π)_{K̄}` (the `omegaPullbackCoeff ≠ 0` input) -/

/-- **`omegaPullbackCoeff (1−π)_{K̄} = 1`** — the omega-coefficient base-change VALUE transport
(Silverman III.5).  The concrete base-changed pullback is `oneSubFrobeniusPullback_L =
baseChangePullback (1−π).pullback`, so the value transport `omegaPullbackCoeff_baseChangePullback`
gives `omegaPullbackCoeff (1−π)_{K̄} = functionFieldMap (omegaPullbackCoeff (1−π) over K) =
functionFieldMap 1 = 1` (the `K`-level value `1` is the axiom-clean
`omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one`).  This single fact discharges BOTH the
separability `≠ 0` and the constancy `∈ range` inputs below, *without* carrying
`OmegaBaseChangeNeZero` or the `sorryAx`-tainted `omegaPullbackCoeff_mem_F`. -/
theorem omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_eq_one (hq : 2 ≤ Fintype.card K) :
    omegaPullbackCoeff (W.baseChange (AlgebraicClosure K))
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)) = 1 := by
  rw [omegaPullbackCoeff_baseChangePullback W (AlgebraicClosure K)
    (isogOneSub_negFrobenius W hq)
    (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
    (by rw [oneSubFrobeniusIsogBaseChange_pullback]; rfl)]
  rw [omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one W p hq]
  exact map_one _

/-- **`omegaPullbackCoeff (1−π)_{K̄} ≠ 0`** (the separability input of the general comap lemma),
discharged outright from the VALUE transport `omegaPullbackCoeff (1−π)_{K̄} = 1`
(`omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_eq_one`) — *no carried `OmegaBaseChangeNeZero`*. -/
theorem omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_ne_zero (hq : 2 ≤ Fintype.card K) :
    omegaPullbackCoeff (W.baseChange (AlgebraicClosure K))
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)) ≠ 0 := by
  rw [omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_eq_one W p r hq]; exact one_ne_zero

/-- **`omegaPullbackCoeff (1−π)_{K̄} ∈ algebraMap.range`** — discharged outright from the VALUE
transport (`= 1 = algebraMap _ _ 1`), *`sorryAx`-free* (no longer via `omegaPullbackCoeff_mem_F`). -/
theorem omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_mem_range (hq : 2 ≤ Fintype.card K) :
    omegaPullbackCoeff (W.baseChange (AlgebraicClosure K))
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)) ∈
      (algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField).range := by
  rw [omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_eq_one W p r hq]
  exact ⟨1, map_one _⟩

/-! ### Step 2 — the isolated closed-point residue datum and the affine comap identity -/

/-- **The closed-point residue datum for `(1 − π)_{K̄}`** (the `1 − π` form of the `addIsog`-only
`oneSub_coords_at_affine`).  For every smooth point `P` of `E_{K̄}` whose image `(1−π)P = some x y` is
affine, this bundles:

* the two **generator residues** `(1−π)^*x_gen ≡ x`, `(1−π)^*y_gen ≡ y` modulo `m_P` — the
  closed-point compatibility of the opaque pullback `oneSubFrobeniusPullback_L` with the point map
  `id − π̄`; and
* the **non-2-torsion-image unit** `ord_P ((1−π)^*u) = 0` (`u = 2y_gen + a₁x_gen + a₃` the invariant
  differential denominator, whose `α^*`-image is a unit at `P` exactly when `(1−π)P` is non-2-torsion).

This is the genuine closed-point geometric residual the affine comap identity rests on (the
generic-point version is the proved Wall A `oneSub_isGenuineWith_Kbar`); the `e = 1` it would
otherwise need is *derived* from the invariant differential, so no `he1` is carried. -/
def OneSubAffineResidues (hq : 2 ≤ Fintype.card K) : Prop :=
  ∀ (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x y : AlgebraicClosure K}
    (h_ns : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular x y),
    (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom P.toAffinePoint =
        Affine.Point.some x y h_ns →
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
          SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
            (x_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x) < 1 ∧
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
          SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
            (y_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y) < 1 ∧
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
          SmoothPlaneCurve (AlgebraicClosure K)).ord_P P
        (alpha_star_u (W.baseChange (AlgebraicClosure K))
          (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))) = 0

/-- **The affine comap-valuation identity for `(1 − π)_{K̄}`** (the `affine` field of
`ComapPointValuationWitness`), CoordHom-free, with `e = 1` derived (no `he1`).

For every smooth point `P` whose image `(1−π)P = some x y h_ns` is affine,
`(pointValuation P).comap (1−π)^* = pointValuation ⟨x, y, h_ns⟩` outright.  Discharged via the general
headline `comap_pointValuation_isog_eq_affine` (axiom-clean), with:

* the separability coefficient `≠ 0` and the constancy `∈ range` — BOTH now *discharged* outright
  from the omega-coefficient VALUE base-change transport `omegaPullbackCoeff (1−π)_{K̄} = 1`
  (`omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_eq_one`), so `OmegaBaseChangeNeZero`/`hcoeff_mem`
  are NO LONGER carried; and
* the two generator residues + the non-2-torsion-image unit supplied by the isolated closed-point
  residual `OneSubAffineResidues`.

The unramifiedness `e = 1` is *proved* from the invariant differential, so it is not a hypothesis.

(This is the *carried-residue* form; the fully unconditional `comap_pointValuation_oneSub_eq_affine`
— with the closed-point residues `OneSubAffineResidues` *discharged* for ALL affine images, including
the doubling and 2-torsion-image cases — is in `OneSubAffineResidues.lean`.) -/
theorem comap_pointValuation_oneSub_eq_affine_of_residues
    (hq : 2 ≤ Fintype.card K)
    (hres : OneSubAffineResidues W p r hq)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x y : AlgebraicClosure K}
    (h_ns : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular x y)
    (hQ : (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom P.toAffinePoint =
        Affine.Point.some x y h_ns) :
    ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P).comap
        (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
          (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback.toRingHom =
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation ⟨x, y, h_ns⟩ := by
  obtain ⟨hx, hy, h_u⟩ := hres P h_ns hQ
  exact comap_pointValuation_isog_eq_affine
    (omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_mem_range W p r hq)
    (omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_ne_zero W p r hq)
    P h_ns hx hy h_u

end HasseWeil.WeilPairing

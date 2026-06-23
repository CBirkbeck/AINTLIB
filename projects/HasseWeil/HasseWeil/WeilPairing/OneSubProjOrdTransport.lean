/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.OneSubDualDivisor
import HasseWeil.WeilPairing.ProjOrdTransportLocal
import HasseWeil.WeilPairing.WallAGeometricRealization
import HasseWeil.WeilPairing.OneSubInftyResidues

/-!
# `OneSubFrobeniusScaling` from the sharpened local witnesses for `1 − π` (CoordHom-free)

This file wires the general divisor-pullback reduction
`projOrdTransport_of_comap_pointValuation` (`ProjOrdTransportLocal.lean`) and the now-proved Wall A
translation-covariance `oneSub_hcommPrime_discharged` (`WallAGeometricRealization.lean`) into the
`1 − π` leaf-2 pipeline.  The net effect is to **sharpen** the carried geometric residual for
`OneSubFrobeniusScaling` and to **eliminate the `hcomm'` carry entirely**:

`oneSubFrobeniusScaling_of_comapWitness` closes `OneSubFrobeniusScaling W p r K̄ hq` from

* `hdeg_eq` — Silverman V.1.3 `deg(1 − π) = #E(𝔽_q)` (the project's known sharp residual, the same
  one every leaf-2 route carries; carries `sorryAx` upstream exactly as elsewhere);
* `hcomap` — the **local comap-valuation witnesses** `ComapPointValuationWitness` for the
  base-changed `1 − π`, i.e. the per-place identities `comap (1−π)^* = (place at (1−π)P)`.  This is a
  strictly **sharper** residual than the opaque `ProjOrdTransport (1 − π)` it replaces: it isolates
  the geometric content to the two per-place / per-uniformizer facts (the **SamePlace**
  `φ^*(m_Q) ⊆ m_P` at closed points + the **e = 1** local uniformizer at the image), the reviewer's
  round-21 "formal-local" sub-leaves;
* `hsurj` — surjectivity of `(1 − π)_{K̄}` over `K̄` (Silverman III.4.10a), needed only to build the
  divisor-pushforward dual `δ`/`hdc`.

The translation covariance `hcomm'` is **no longer a hypothesis**: it is supplied internally by
`oneSub_hcommPrime_discharged`, which is proved CoordHom-free from Wall A
(`mapTranslateGenericPoint_oneSub_canonical`).  The dual `δ`/`hdc` is the σ-bridge
`divisorPushforwardDual`, automatic given `hproj` (= the reduction's output) + `hsurj`.

So relative to `oneSubFrobeniusScaling_of_divisorDual` the carried inputs go from
`{hdeg_eq, hproj, hsurj, hcomm'}` to `{hdeg_eq, hcomap, hsurj}` — `hcomm'` discharged, `hproj`
refined to the per-place comap witnesses.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.4.10c (unramified order-transport),
  III.6.1b/III.6.2(a) (divisor-pushforward dual), III.8.1d/III.8.6.1 (the scaling), V.1.3.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.WeilPairing.DivisorPullback IsogenyBaseChangeConcrete

section Assemble

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]

noncomputable local instance instDecEqACOSPOT : DecidableEq (AlgebraicClosure K) := Classical.decEq _

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]
  [IsIntegrallyClosed
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).CoordinateRing]

omit [Fintype W.toAffine.Point]
  [IsIntegrallyClosed
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).CoordinateRing] in
/-- **`ProjOrdTransport (1 − π)_{K̄}` from the local comap witnesses** (Silverman III.4.10c),
CoordHom-free.  The divisor-pullback functoriality `div((1−π)^* h) = (1−π)^*(div h)` for the
base-changed separable `1 − π`, obtained by the general reduction
`projOrdTransport_of_comap_pointValuation` from the per-place comap-valuation identities
`ComapPointValuationWitness` (the SamePlace + e = 1 content packaged at the valuation level). -/
theorem oneSub_hproj_of_comapWitness (hq : 2 ≤ Fintype.card K)
    (hcomap : ComapPointValuationWitness (W.baseChange (AlgebraicClosure K))
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))) :
    ProjOrdTransport
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)) :=
  projOrdTransport_of_comap_pointValuation hcomap

/-- **`OneSubFrobeniusScaling` for `(1 − π)_{K̄}` from the sharpened local witnesses** (Silverman
III.8.6.1), CoordHom-free, with the translation covariance `hcomm'` **discharged**.

For `(1 − π)_{K̄}` over `L = AlgebraicClosure K`, the symplectic scaling
`e_ℓ((id − π̄) S, (id − π̄) T) = e_ℓ(S, T)^{deg(1 − π)}` on `E_{K̄}[ℓ]` (every prime `ℓ ≠ p`) holds,
from:

* `hdeg_eq` — Silverman V.1.3 `deg(1 − π) = #E(𝔽_q)` (the standing sharp residual);
* `hcomap` — the local comap-valuation witnesses `ComapPointValuationWitness` for `(1 − π)_{K̄}` (the
  sharpened replacement for the opaque `ProjOrdTransport`, isolating the geometric content to the
  per-place SamePlace + e = 1 facts);
* `hsurj` — surjectivity of `(1 − π)_{K̄}` over `K̄` (Silverman III.4.10a).

The translation covariance is supplied internally by the proved Wall A
`oneSub_hcommPrime_discharged`; the divisor-pushforward dual `δ`/`hdc` is automatic via the σ-bridge.
This is the leanest form of the `1 − π` scaling: it carries only the V.1.3 degree identity, the local
comap witnesses, and surjectivity — `hcomm'` is now a theorem, not a hypothesis. -/
theorem oneSubFrobeniusScaling_of_comapWitness (hq : 2 ≤ Fintype.card K)
    (hdeg_eq :
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).degree = pointCount W.toAffine)
    (hcomap : ComapPointValuationWitness (W.baseChange (AlgebraicClosure K))
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)))
    (hsurj : Function.Surjective
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom) :
    OneSubFrobeniusScaling W p r (AlgebraicClosure K) hq :=
  oneSubFrobeniusScaling_of_divisorDual W p r hq hdeg_eq
    (oneSub_hproj_of_comapWitness W p r hq hcomap)
    hsurj
    (oneSub_hcommPrime_discharged W p r hq)

omit [IsIntegrallyClosed
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).CoordinateRing] in
/-- **`deg(1 − π)_{K̄} = #E(𝔽_q)`** (Silverman V.1.3 + degree base-change invariance), assembled.
Chains the curve-free base-change degree invariance
`oneSubFrobeniusIsogBaseChange_degree_eq_of_finrankBaseChange` (`deg(1 − π)_{K̄} = deg(1 − π)` over
`K`, via `baseChangePullback_finrank_eq` / `Module.finrank_baseChange`) with the V.1.3 sharp residual
`isogOneSub_negFrobenius_degree_eq_pointCount` (`deg(1 − π) = pointCount` over `K`).  This
**discharges the `hdeg_eq` input**; it carries `sorryAx` upstream exactly via V.1.3, the project's
standing sharp residual that *every* leaf-2 route carries. -/
theorem oneSubFrobeniusIsogBaseChange_degree_eq_pointCount (hq : 2 ≤ Fintype.card K) :
    (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).degree = pointCount W.toAffine :=
  (oneSubFrobeniusIsogBaseChange_degree_eq_of_finrankBaseChange W p r (AlgebraicClosure K) hq).trans
    (isogOneSub_negFrobenius_degree_eq_pointCount W hq)

/-- **`OneSubFrobeniusScaling` for `(1 − π)_{K̄}` carrying only the local comap witnesses and
surjectivity** (Silverman III.8.6.1), CoordHom-free, with the degree identity `hdeg_eq`
**discharged**.  The symplectic scaling `e_ℓ((id − π̄) S, (id − π̄) T) = e_ℓ(S, T)^{deg(1 − π)}` on
`E_{K̄}[ℓ]` (every prime `ℓ ≠ p`) holds from the two carried inputs

* `hcomap` — the local comap-valuation witnesses `ComapPointValuationWitness` for `(1 − π)_{K̄}` (the
  SamePlace + `e = 1` content packaged at the valuation level);
* `hsurj` — surjectivity of `(1 − π)_{K̄}` on `E(K̄)`-points (Silverman III.4.10a, Lang's theorem
  `id − Frob` surjective; the genuinely-geometric residual).

The degree identity `deg(1 − π)_{K̄} = #E(𝔽_q)` is supplied internally by
`oneSubFrobeniusIsogBaseChange_degree_eq_pointCount` (V.1.3 + degree base change).  The translation
covariance `hcomm'` and the divisor-pullback functoriality `ProjOrdTransport` are discharged further
upstream (Wall A `oneSub_hcommPrime_discharged`; the comap witnesses via
`oneSub_hproj_of_comapWitness`).  So relative to `oneSubFrobeniusScaling_of_comapWitness` the only
remaining carried inputs are `hcomap` and `hsurj`. -/
theorem oneSubFrobeniusScaling_of_comapWitness_surj (hq : 2 ≤ Fintype.card K)
    (hcomap : ComapPointValuationWitness (W.baseChange (AlgebraicClosure K))
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)))
    (hsurj : Function.Surjective
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom) :
    OneSubFrobeniusScaling W p r (AlgebraicClosure K) hq :=
  oneSubFrobeniusScaling_of_comapWitness W p r hq
    (oneSubFrobeniusIsogBaseChange_degree_eq_pointCount W p r hq)
    hcomap
    hsurj

/-- **`OneSubFrobeniusScaling` for `(1 − π)_{K̄}` — `δ`-free and surjectivity-free** (Silverman
III.8.6.1), CoordHom-free.  The symplectic scaling
`e_ℓ((id − π̄) S, (id − π̄) T) = e_ℓ(S, T)^{deg(1 − π)}` on `E_{K̄}[ℓ]` (every prime `ℓ ≠ p`), proved
through the `δ`-free `weilScales_noδ` — **no abstract dual `δ`, no dual relation `hdc`, and no point-map
surjectivity** (reviewer round-22 Q3, image-restricted route).

Carried inputs:
* `hdeg_eq` — Silverman V.1.3 `deg(1 − π) = #E(𝔽_q)` (the standing sharp residual every leaf-2 route
  carries; carries `sorryAx` upstream exactly as elsewhere);
* `hcomap` — the local comap-valuation witnesses `ComapPointValuationWitness` for `(1 − π)_{K̄}` (the
  SamePlace + `e = 1` content, packaged at the valuation level), turned into `ProjOrdTransport` by
  `oneSub_hproj_of_comapWitness`.

The translation covariance is supplied internally by the proved Wall A `oneSub_hcommPrime_discharged`;
the `[ℓ]`-commutation by `oneSubFrobeniusIsogBaseChange_commute_mulByInt`; the degree match `#ker = deg`
by `oneSubFrobeniusIsogBaseChange_hkerdeg_of_degree_eq_pointCount` (from `hdeg_eq`).  Relative to
`oneSubFrobeniusScaling_of_comapWitness`, the `hsurj` input is **gone** — the dual is no longer
constructed. -/
theorem oneSubFrobeniusScaling_of_comapWitness_noδ (hq : 2 ≤ Fintype.card K)
    (hdeg_eq :
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).degree = pointCount W.toAffine)
    (hcomap : ComapPointValuationWitness (W.baseChange (AlgebraicClosure K))
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))) :
    OneSubFrobeniusScaling W p r (AlgebraicClosure K) hq := by
  intro ℓ hℓp _ hℓF
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have : Finite
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom.ker :=
    oneSubFrobeniusIsogBaseChange_finiteKer W p r
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)
  set φL := oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
    (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)
  refine weilScales_noδ (W.baseChange (AlgebraicClosure K)) ℓ hℓF φL
    (AddMonoidHom.id (W.baseChange (AlgebraicClosure K)).toAffine.Point -
      frobeniusHomBaseChange W p r (AlgebraicClosure K))
    (oneSubFrobeniusIsogBaseChange_toAddMonoidHom W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
    (isogOneSub_negFrobenius W hq).degree
    (oneSubFrobeniusIsogBaseChange_degree_eq_of_finrankBaseChange W p r (AlgebraicClosure K) hq)
    (oneSub_hproj_of_comapWitness W p r hq hcomap)
    (oneSubFrobeniusIsogBaseChange_commute_mulByInt W p r (AlgebraicClosure K) ((ℓ : ℕ) : ℤ)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
    (oneSubFrobeniusIsogBaseChange_hkerdeg_of_degree_eq_pointCount W p r
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq) hdeg_eq)
    ?_
  intro S T hS hφT
  exact oneSub_hcommPrime_discharged W p r hq ℓ hℓF S T hS hφT

/-- **`OneSubFrobeniusScaling` for `(1 − π)_{K̄}` carrying ONLY the local comap witnesses** —
`δ`-free, surjectivity-free, degree-identity discharged (Silverman III.8.6.1), CoordHom-free.  The
leanest leaf-2 form: the symplectic scaling holds from the *single* carried geometric residual
`hcomap` (the local comap-valuation witnesses), with the degree identity `deg(1 − π) = #E(𝔽_q)`
supplied internally by `oneSubFrobeniusIsogBaseChange_degree_eq_pointCount` (V.1.3 + degree base
change) and **no surjectivity** (the dual is never constructed).  This is
`oneSubFrobeniusScaling_of_comapWitness_surj` with `hsurj` removed. -/
theorem oneSubFrobeniusScaling_of_comapWitness_noδ_clean (hq : 2 ≤ Fintype.card K)
    (hcomap : ComapPointValuationWitness (W.baseChange (AlgebraicClosure K))
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))) :
    OneSubFrobeniusScaling W p r (AlgebraicClosure K) hq :=
  oneSubFrobeniusScaling_of_comapWitness_noδ W p r hq
    (oneSubFrobeniusIsogBaseChange_degree_eq_pointCount W p r hq)
    hcomap

omit [IsIntegrallyClosed
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).CoordinateRing] in
/-- **The local comap-valuation witnesses `ComapPointValuationWitness` for `(1 − π)_{K̄}`**, assembled
from the three proved fields (CoordHom-free, no carried geometric residual).  The structure literal
packages the affine-image comap identity (`comap_pointValuation_oneSub_eq_affine`), the infinity-image
comap identity (`comap_pointValuation_oneSub_eq_infty`), and the infinity-place order-transport
(`inftyOrdTransport_oneSub`) for the base-changed separable `1 − π = oneSubFrobeniusIsogBaseChange`. -/
theorem comapPointValuationWitness_oneSub (hq : 2 ≤ Fintype.card K) :
    ComapPointValuationWitness (W.baseChange (AlgebraicClosure K))
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)) where
  affine := fun P {_x _y} h_ns hQ ↦ comap_pointValuation_oneSub_eq_affine W p r hq P h_ns hQ
  affineToInfty := fun P hQ ↦ comap_pointValuation_oneSub_eq_infty W p r hq P hQ
  infinity := inftyOrdTransport_oneSub W p r hq

/-- **`OneSubFrobeniusScaling` for `(1 − π)_{K̄}` — CLOSED with ZERO carried geometric hypotheses**
(Silverman III.8.6.1), CoordHom-free, `δ`-free, surjectivity-free.

This is leaf 2 of `FrobBaseChangeScalings` (`FrobMatrixData.lean`), discharged outright: the symplectic
scaling `e_ℓ((id − π̄) S, (id − π̄) T) = e_ℓ(S, T)^{deg(1 − π)}` on `E_{K̄}[ℓ]` (every prime `ℓ ≠ p`)
holds with **no carried hypotheses** — the local comap-valuation witnesses are now fully assembled
(`comapPointValuationWitness_oneSub`), the surjectivity was eliminated via the `δ`-free `weilScales_noδ`
route, the translation covariance is the proved Wall A `oneSub_hcommPrime_discharged`, and the degree
identity `deg(1 − π) = #E(𝔽_q)` is supplied internally (V.1.3 + degree base change).

Axiom-clean: `#print axioms oneSubFrobeniusScaling_holds = [propext, Classical.choice, Quot.sound]`
(no `sorryAx`) — the V.1.3 degree identity `sepDegree_oneSub_eq_pointCount` it routes through is itself
axiom-clean in the current tree, and the entire local comap pipeline assembled here is axiom-clean. -/
theorem oneSubFrobeniusScaling_holds (hq : 2 ≤ Fintype.card K) :
    OneSubFrobeniusScaling W p r (AlgebraicClosure K) hq :=
  oneSubFrobeniusScaling_of_comapWitness_noδ_clean W p r hq
    (comapPointValuationWitness_oneSub W p r hq)

end Assemble

end HasseWeil.WeilPairing

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.PencilCovariance
import HasseWeil.WeilPairing.ProjOrdTransportLocal
import HasseWeil.WeilPairing.SeparableScaling
import HasseWeil.WeilPairing.PencilDualDivisor
import HasseWeil.WeilPairing.SeparableWitnesses

/-!
# `PencilScaling` for `(rπ − s)_{K̄}` from the local comap witnesses (δ-free, surjectivity-free)

This file is the **`rπ − s` analogue of the leaf-2 closer** `OneSubProjOrdTransport.lean`: it wires
the general divisor-pullback reduction `projOrdTransport_of_comap_pointValuation`
(`ProjOrdTransportLocal.lean`), the now-proved pencil translation covariance
`pencil_hcommPrime_discharged` (`PencilCovariance.lean`), the `[ℓ]`-commutation
`pencilIsogBaseChange_commute_mulByInt`, and the δ-free `WeilScales` bridge `weilScales_noδ`
(`SeparableScaling.lean`) into the leaf-3 pipeline.

The net effect, exactly as for leaf 2:

`pencilFrobeniusScaling_of_comapWitness_noδ` closes `PencilScaling W p r K̄ pencilDeg` for the
canonical base-changed pullback `pencilBaseChangePullback`, from

* `hcomap` — the **local comap-valuation witnesses** `ComapPointValuationWitness` for the
  base-changed `rπ − s` (the per-place SamePlace + e = 1 content, turned into `ProjOrdTransport` by
  `projOrdTransport_of_comap_pointValuation`); and
* `hkerdeg` — the separable degree match `#ker (rπ − s)_{K̄} = deg (rπ − s)_{K̄}` (Silverman III.4.10c,
  the pencil analogue of leaf-2's `#ker = pointCount`; supplied by `pencil_hkerdeg_galois`).

The translation covariance `hcomm'` is **no longer a hypothesis**: it is supplied internally by the
proved Wall A `pencil_hcommPrime_discharged`.  The dual `δ`/`hdc` and the surjectivity `hsurj` are
**gone** — the δ-free `weilScales_noδ` reads the dual point off the σ-bridge as `#ker • T`.

So relative to the existing δ-based `pencilScaling_of_divisorDual` (which carries
`{hproj, hsurj, hkerdeg, hcomm'}` in `PencilScalingData`), this route carries only `{hcomap, hkerdeg}`
— `hcomm'` discharged, `hsurj` eliminated, `hproj` refined to the per-place comap witnesses.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.4.10c (unramified order-transport),
  III.8.1d/III.8.6.1 (the scaling).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.WeilPairing.DivisorPullback IsogenyBaseChangeConcrete
open HasseWeil.WeilPairing.TorsionGeometric

set_option linter.style.longLine false

section Assemble

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]

noncomputable local instance instDecEqACPCS : DecidableEq (AlgebraicClosure K) := Classical.decEq _

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]
  [IsIntegrallyClosed
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).CoordinateRing]

omit [Fintype W.toAffine.Point]
  [IsIntegrallyClosed
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).CoordinateRing] in
/-- **`ProjOrdTransport (rπ − s)_{K̄}` from the local comap witnesses** (Silverman III.4.10c),
CoordHom-free.  The divisor-pullback functoriality `div((rπ−s)^* h) = (rπ−s)^*(div h)` for the
base-changed separable `rπ − s`, obtained by the general reduction
`projOrdTransport_of_comap_pointValuation` from the per-place comap-valuation identities
`ComapPointValuationWitness`.  The `rπ − s` analogue of `oneSub_hproj_of_comapWitness`. -/
theorem pencil_hproj_of_comapWitness (r' s' : ℤ)
    (pullback_L : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[AlgebraicClosure K]
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField)
    (hcomap : ComapPointValuationWitness (W.baseChange (AlgebraicClosure K))
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L)) :
    ProjOrdTransport (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L) :=
  projOrdTransport_of_comap_pointValuation hcomap

omit [Fintype W.toAffine.Point]
  [IsIntegrallyClosed
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).CoordinateRing] in
/-- **Finiteness of `ker (rπ − s)_{K̄}` from the degree match** (`#ker = deg > 0`).  The separable
degree match `#ker = deg` together with positivity of the genuine `rπ − s` degree
(`genuineIsogSmulSub_degree_pos`, transported through `hdeg_bc`) gives `Nat.card ker > 0`, hence the
kernel subtype is finite (`Nat.card_pos_iff`).  This supplies the `[Finite …ker]` instance that
`weilScales_noδ` requires, without the leaf-2 fixed-locus argument (which is special to `1 − π`). -/
theorem pencilIsogBaseChange_finiteKer_of_hkerdeg_pos (r' s' : ℤ)
    (pullback_L : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[AlgebraicClosure K]
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField)
    (hkerdeg :
      Nat.card (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).toAddMonoidHom.ker =
        (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).degree)
    (hdeg_pos : 0 < (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).degree) :
    Finite (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).toAddMonoidHom.ker := by
  have hcard_pos :
      0 < Nat.card (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).toAddMonoidHom.ker := by
    rw [hkerdeg]; exact hdeg_pos
  exact (Nat.card_pos_iff.mp hcard_pos).2

/-- **`PencilScaling` for `(rπ − s)_{K̄}` — δ-free and surjectivity-free** (Silverman III.8.6.1),
CoordHom-free, with the translation covariance `hcomm'` **discharged**.

For the canonical base-changed pullback `pencilBaseChangePullback` over `L = AlgebraicClosure K` and a
fixed `(r', s')` with `r' ≠ 0`, `s' ≠ 0`, `(r' : K) ≠ 0`, `(s' : K) ≠ 0`, the single `WeilScales`
predicate
`WeilScales (E_{K̄}) ℓ hℓF (r·π̄ − s·id) (φ.degree)` holds (every prime `ℓ ≠ p`), through the δ-free
`weilScales_noδ` — **no abstract dual `δ`, no dual relation `hdc`, and no point-map surjectivity**.

Carried inputs:
* `hcomap` — the local comap-valuation witnesses `ComapPointValuationWitness` for `(rπ − s)_{K̄}`
  (turned into `ProjOrdTransport` by `pencil_hproj_of_comapWitness`);
* `hkerdeg` — the separable degree match `#ker (rπ − s)_{K̄} = deg` (Silverman III.4.10c).

The translation covariance is supplied internally by the proved Wall A `pencil_hcommPrime_discharged`;
the `[ℓ]`-commutation by `pencilIsogBaseChange_commute_mulByInt`; finiteness of the kernel by
`pencilIsogBaseChange_finiteKer_of_hkerdeg_pos`. -/
theorem pencilScaling_one_of_comapWitness_noδ (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓF : (ℓ : AlgebraicClosure K) ≠ 0)
    (hcomap : ComapPointValuationWitness (W.baseChange (AlgebraicClosure K))
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)))
    (hkerdeg :
      Nat.card (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
          (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAddMonoidHom.ker =
        (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
          (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).degree)
    (hdeg_pos : 0 < (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
          (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).degree) :
    WeilScales (W.baseChange (AlgebraicClosure K)) ℓ hℓF
      (r' • frobeniusHomBaseChange W p r (AlgebraicClosure K) -
        s' • AddMonoidHom.id (W.baseChange (AlgebraicClosure K)).toAffine.Point)
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).degree := by
  have : Finite (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
      (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAddMonoidHom.ker :=
    pencilIsogBaseChange_finiteKer_of_hkerdeg_pos W p r r' s'
      (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK) hkerdeg hdeg_pos
  set φL := pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
    (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)
  refine weilScales_noδ (W.baseChange (AlgebraicClosure K)) ℓ hℓF φL
    (r' • frobeniusHomBaseChange W p r (AlgebraicClosure K) -
      s' • AddMonoidHom.id (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (pencilIsogBaseChange_toAddMonoidHom W p r (AlgebraicClosure K) r' s'
      (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK))
    φL.degree rfl
    (pencil_hproj_of_comapWitness W p r r' s'
      (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK) hcomap)
    (pencilIsogBaseChange_commute_mulByInt W p r (AlgebraicClosure K) ((ℓ : ℕ) : ℤ) r' s'
      (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK))
    hkerdeg
    ?_
  intro S T hS hφT
  exact pencil_hcommPrime_discharged W p r r' s' hr hs hrK hsK ℓ hℓF S T hS hφT

/-! ### The abstract-pullback δ-free bundle (handles every `(r', s')`, including `r' = 0`)

`pencilScaling_one_of_comapWitness_noδ` above uses the canonical `pencilBaseChangePullback`, whose
construction needs `r' ≠ 0`.  The full leaf `PencilScaling` quantifies over **every** `(r', s')` with
`p ∤ s'` — including `r' = 0`, where `rπ − s = [−s]`.  To cover all pairs uniformly we package the
δ-free scaling against an **abstract** `pullback_L` with a carried generic-point covariance leaf
`hgcomm` (the `MapTranslateGenericPoint`, which `pencil_hcommPrime_of_hgcomm` turns into `hcomm'` for
*any* `pullback_L`, no `r' ≠ 0` needed) plus the per-place comap witnesses and the degree match. -/

/-- **`PencilScalingComapData`** — the δ-free, surjectivity-free geometric bundle for the
base-changed `rπ − s` against an abstract `pullback_L`, per `(r', s')`.  Identical in spirit to
`PencilScalingData` but with `hcomm'`/`hsurj`/`hproj` replaced by the *sharper* δ-free inputs: the
generic-point covariance leaf `hgcomm` (Wall A), the per-place comap witnesses `hcomap`, and the
degree match `hkerdeg`.  No abstract dual, no surjectivity. -/
structure PencilScalingComapData (r' s' : ℤ) where
  /-- The base-changed pullback `AlgHom`. -/
  pullback_L : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[AlgebraicClosure K]
    (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
  /-- The generic-point covariance leaf (Wall A `MapTranslateGenericPoint`, the canonical action). -/
  hgcomm : MapTranslateGenericPoint (W.baseChange (AlgebraicClosure K))
    (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L)
    (WeierstrassCurve.Affine.Point.map (W' := W.baseChange (AlgebraicClosure K))
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).pullback)
  /-- The per-place comap-valuation witnesses (SamePlace + `e = 1`, at the valuation level). -/
  hcomap : ComapPointValuationWitness (W.baseChange (AlgebraicClosure K))
    (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L)
  /-- The separable degree match `#ker = deg` (Silverman III.4.10c). -/
  hkerdeg :
    Nat.card (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).toAddMonoidHom.ker =
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).degree
  /-- Positivity of the degree (so the kernel is finite). -/
  hdeg_pos : 0 < (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).degree

omit [Fintype W.toAffine.Point] in
/-- **One `WeilScales` instance for `(rπ − s)_{K̄}` from the abstract δ-free bundle** (Silverman
III.8.6.1), CoordHom-free, no `δ`/`hsurj`.  For any `(r', s')` and prime `ℓ`, the bundle
`PencilScalingComapData` yields
`WeilScales (E_{K̄}) ℓ hℓF (r·π̄ − s·id) (φ.degree)` via `weilScales_noδ`, with `hcomm'` derived from
the carried `hgcomm` (`pencil_hcommPrime_of_hgcomm`), `hproj` from `hcomap`, the `[ℓ]`-commutation
from `pencilIsogBaseChange_commute_mulByInt`, and finiteness from `hkerdeg`/`hdeg_pos`. -/
theorem pencilScaling_one_of_comapData (r' s' : ℤ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓF : (ℓ : AlgebraicClosure K) ≠ 0)
    (d : PencilScalingComapData W p r r' s') :
    WeilScales (W.baseChange (AlgebraicClosure K)) ℓ hℓF
      (r' • frobeniusHomBaseChange W p r (AlgebraicClosure K) -
        s' • AddMonoidHom.id (W.baseChange (AlgebraicClosure K)).toAffine.Point)
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' d.pullback_L).degree := by
  have : Finite (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' d.pullback_L).toAddMonoidHom.ker :=
    pencilIsogBaseChange_finiteKer_of_hkerdeg_pos W p r r' s' d.pullback_L d.hkerdeg d.hdeg_pos
  set φL := pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' d.pullback_L
  refine weilScales_noδ (W.baseChange (AlgebraicClosure K)) ℓ hℓF φL
    (r' • frobeniusHomBaseChange W p r (AlgebraicClosure K) -
      s' • AddMonoidHom.id (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (pencilIsogBaseChange_toAddMonoidHom W p r (AlgebraicClosure K) r' s' d.pullback_L)
    φL.degree rfl
    (pencil_hproj_of_comapWitness W p r r' s' d.pullback_L d.hcomap)
    (pencilIsogBaseChange_commute_mulByInt W p r (AlgebraicClosure K) ((ℓ : ℕ) : ℤ) r' s' d.pullback_L)
    d.hkerdeg
    ?_
  intro S T hS hφT
  exact pencil_hcommPrime_of_hgcomm W p r r' s' d.pullback_L d.hgcomm ℓ hℓF S T hS hφT

omit [Fintype W.toAffine.Point] in
/-- **`PencilScaling` for `(rπ − s)_{K̄}` from a per-pair abstract δ-free bundle** (Silverman
III.8.6.1), CoordHom-free, no `δ`/`hsurj`.  Given, for every `(r', s')`, a `PencilScalingComapData`
bundle, the full leaf `PencilScaling W p r K̄ pencilDeg` holds for
`pencilDeg r' s' := ((pencilData r' s').pullback_L-degree : ℤ)`.  The exponent matches the carried
isogeny degree (`Int.toNat_natCast`); the per-pair scaling is `pencilScaling_one_of_comapData`. -/
theorem pencilScaling_of_comapData
    (pencilData : ∀ r' s' : ℤ, PencilScalingComapData W p r r' s') :
    PencilScaling W p r (AlgebraicClosure K)
      (fun r' s' ↦ ((pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilData r' s').pullback_L).degree : ℤ)) := by
  intro r' s' _hps ℓ hℓp _hℓne hℓF
  have : Fact ℓ.Prime := ⟨hℓp⟩
  simp only [Int.toNat_natCast]
  exact pencilScaling_one_of_comapData W p r r' s' ℓ hℓF (pencilData r' s')

omit [IsIntegrallyClosed
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).CoordinateRing] in
/-- **The `hgcomm` field of `PencilScalingComapData` for the canonical pullback is DISCHARGED**
(Silverman III.8.2), CoordHom-free.  For the canonical `pencilBaseChangePullback` (`r' ≠ 0`,
`p ∤ r', s'`), the generic-point covariance leaf `MapTranslateGenericPoint` for the canonical action
is the proved Wall A `mapTranslateGenericPoint_pencil_canonical`.  So a `PencilScalingComapData` bundle
for the canonical pullback carries only `{hcomap, hkerdeg, hdeg_pos}` — `hgcomm` is no longer a
residual. -/
theorem pencilScalingComapData_hgcomm_canonical (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    MapTranslateGenericPoint (W.baseChange (AlgebraicClosure K))
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK))
      (WeierstrassCurve.Affine.Point.map (W' := W.baseChange (AlgebraicClosure K))
        (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
          (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).pullback) :=
  mapTranslateGenericPoint_pencil_canonical W p r r' s' hr hs hrK hsK

omit [Fintype W.toAffine.Point] in
/-- **`PencilScaling` for an arbitrary non-negative `deg` from the abstract δ-free bundles**, given
the carried isogeny degrees realise it.  The form a top-level caller uses to obtain `PencilScaling`
for a fixed degree function (e.g. `deg r s = (genuineIsogSmulSub …).degree`). -/
theorem pencilScaling_of_comapData_of_deg
    (deg : ℤ → ℤ → ℤ)
    (pencilData : ∀ r' s' : ℤ, PencilScalingComapData W p r r' s')
    (hdeg : ∀ r' s' : ℤ, (deg r' s').toNat =
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' (pencilData r' s').pullback_L).degree) :
    PencilScaling W p r (AlgebraicClosure K) deg := by
  intro r' s' _hps ℓ hℓp _hℓne hℓF
  have : Fact ℓ.Prime := ⟨hℓp⟩
  rw [hdeg r' s']
  exact pencilScaling_one_of_comapData W p r r' s' ℓ hℓF (pencilData r' s')

/-! ### The `#ker`-exponent bundle (drop the degree match `#ker = deg` entirely)

The bundles above pay the separable degree match `hkerdeg : #ker (rπ − s)_{K̄} = deg (rπ − s)_{K̄}`
(Silverman III.4.10c) twice: once for the *output exponent* (`WeilScales … φ.degree`) and once to get
finiteness of the kernel (`#ker = deg > 0 ⟹ Finite`).  But the bound
`hasse_bound_unconditional_of_baseChange_scalings` only forces the pencil exponent to be *some*
non-negative integer the determinant matches (`hdeg_nonneg`), and the δ-free σ-bridge already produces
the cardinality `#ker` as the exponent.  So we can take the pencil exponent to be `#ker` itself and
**eliminate `hkerdeg` completely** — replacing the degree-match-derived finiteness with an explicit
`finiteKer` field (strictly weaker than `#ker = deg`, exactly as `OneSubScalingData.finiteKer`).

The resulting `PencilScalingComapDataCard` bundle carries only `{pullback_L, hgcomm, hcomap,
finiteKer}` — **no `hkerdeg`, no `hdeg_pos`, no `δ`, no `hsurj`** — and the output is
`PencilScaling W p r K̄ pencilKerCard` with `pencilKerCard` the literal `#ker` function. -/

/-- **`pencilKerCard`** — the kernel-cardinality degree function `(r', s') ↦ #ker(rπ − s)_{K̄}`,
as an integer-valued `deg`.  Depends on a choice of base-changed pullback `pullback_L r' s'`.  This is
the non-negative integer exponent the δ-free `weilScales_noδ_card` produces directly, used as the
`deg` parameter of `hasse_bound_unconditional_of_baseChange_scalings` to **avoid** the geometric
degree match `#ker = deg`. -/
noncomputable def pencilKerCard
    (pullback_L : ∀ _ _ : ℤ,
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[AlgebraicClosure K]
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    ℤ → ℤ → ℤ :=
  fun r' s' ↦
    (Nat.card (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
      (pullback_L r' s')).toAddMonoidHom.ker : ℤ)

omit [Fintype W.toAffine.Point]
  [IsIntegrallyClosed
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).CoordinateRing] in
/-- `pencilKerCard` is non-negative — it is a cast of a `Nat.card`. -/
theorem pencilKerCard_nonneg
    (pullback_L : ∀ _ _ : ℤ,
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[AlgebraicClosure K]
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField)
    (r' s' : ℤ) : 0 ≤ pencilKerCard W p r pullback_L r' s' :=
  Nat.cast_nonneg _

/-- **`PencilScalingComapDataCard`** — the δ-free, surjectivity-free, **degree-match-free** geometric
bundle for the base-changed `rπ − s` against an abstract `pullback_L`, per `(r', s')`.  Identical to
`PencilScalingComapData` but with the degree match `hkerdeg` and the positivity `hdeg_pos`
**dropped**, replaced by an explicit `finiteKer` field (mirroring `OneSubScalingData.finiteKer`): the
output exponent is the kernel cardinality `#ker`, so `#ker = deg` is never needed.  Carries only the
generic-point covariance `hgcomm` (Wall A), the per-place comap witnesses `hcomap`, and `finiteKer`. -/
structure PencilScalingComapDataCard (r' s' : ℤ) where
  /-- The base-changed pullback `AlgHom`. -/
  pullback_L : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[AlgebraicClosure K]
    (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
  /-- The generic-point covariance leaf (Wall A `MapTranslateGenericPoint`, the canonical action). -/
  hgcomm : MapTranslateGenericPoint (W.baseChange (AlgebraicClosure K))
    (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L)
    (WeierstrassCurve.Affine.Point.map (W' := W.baseChange (AlgebraicClosure K))
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).pullback)
  /-- The per-place comap-valuation witnesses (SamePlace + `e = 1`, at the valuation level). -/
  hcomap : ComapPointValuationWitness (W.baseChange (AlgebraicClosure K))
    (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L)
  /-- Finiteness of the kernel (a separable isogeny over `K̄` has finite kernel — the weak form of the
  degree match `#ker = deg`, carried directly so `hkerdeg` is not needed). -/
  finiteKer :
    Finite (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).toAddMonoidHom.ker

omit [Fintype W.toAffine.Point] in
/-- **One `WeilScales` instance for `(rπ − s)_{K̄}` with the `#ker` exponent from the degree-match-free
bundle** (Silverman III.8.6.1), CoordHom-free, no `δ`/`hsurj`/`hkerdeg`.  For any `(r', s')` and prime
`ℓ`, the bundle `PencilScalingComapDataCard` yields
`WeilScales (E_{K̄}) ℓ hℓF (r·π̄ − s·id) (#ker(rπ − s)_{K̄})` via `weilScales_noδ_card`, with `hcomm'`
from the carried `hgcomm` (`pencil_hcommPrime_of_hgcomm`), `hproj` from `hcomap`, the
`[ℓ]`-commutation from `pencilIsogBaseChange_commute_mulByInt`, and finiteness from the carried
`finiteKer`.  **No degree match `#ker = deg`.** -/
theorem pencilScaling_one_of_comapData_card (r' s' : ℤ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓF : (ℓ : AlgebraicClosure K) ≠ 0)
    (d : PencilScalingComapDataCard W p r r' s') :
    WeilScales (W.baseChange (AlgebraicClosure K)) ℓ hℓF
      (r' • frobeniusHomBaseChange W p r (AlgebraicClosure K) -
        s' • AddMonoidHom.id (W.baseChange (AlgebraicClosure K)).toAffine.Point)
      (Nat.card (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' d.pullback_L).toAddMonoidHom.ker) := by
  have := d.finiteKer
  set φL := pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' d.pullback_L
  refine weilScales_noδ_card (W.baseChange (AlgebraicClosure K)) ℓ hℓF φL
    (r' • frobeniusHomBaseChange W p r (AlgebraicClosure K) -
      s' • AddMonoidHom.id (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (pencilIsogBaseChange_toAddMonoidHom W p r (AlgebraicClosure K) r' s' d.pullback_L)
    (pencil_hproj_of_comapWitness W p r r' s' d.pullback_L d.hcomap)
    (pencilIsogBaseChange_commute_mulByInt W p r (AlgebraicClosure K) ((ℓ : ℕ) : ℤ) r' s' d.pullback_L)
    ?_
  intro S T hS hφT
  exact pencil_hcommPrime_of_hgcomm W p r r' s' d.pullback_L d.hgcomm ℓ hℓF S T hS hφT

omit [Fintype W.toAffine.Point] in
/-- **`PencilScaling` for `(rπ − s)_{K̄}` from a per-pair degree-match-free bundle, `#ker` exponent**
(Silverman III.8.6.1), CoordHom-free, no `δ`/`hsurj`/`hkerdeg`.  Given, for every `(r', s')`, a
`PencilScalingComapDataCard` bundle, the full leaf `PencilScaling W p r K̄ pencilKerCard` holds for the
**kernel-cardinality** degree function
`pencilKerCard r' s' := (#ker(rπ − s)_{K̄} : ℤ)` — **not** the geometric degree.  The exponent matches
the carried `#ker` (`Int.toNat_natCast`); the per-pair scaling is `pencilScaling_one_of_comapData_card`.

This is the form `hasse_bound_unconditional_of_baseChange_scalings` consumes with
`deg := pencilKerCard …`, `hdeg_nonneg := pencilKerCard_nonneg …` — **the AG-frontier degree match
`#ker = deg` is never required**. -/
theorem pencilScaling_of_comapData_card
    (pencilData : ∀ r' s' : ℤ, PencilScalingComapDataCard W p r r' s') :
    PencilScaling W p r (AlgebraicClosure K)
      (pencilKerCard W p r (fun r' s' ↦ (pencilData r' s').pullback_L)) := by
  intro r' s' _hps ℓ hℓp _hℓne hℓF
  have : Fact ℓ.Prime := ⟨hℓp⟩
  simp only [pencilKerCard, Int.toNat_natCast]
  exact pencilScaling_one_of_comapData_card W p r r' s' ℓ hℓF (pencilData r' s')

end Assemble

end HasseWeil.WeilPairing

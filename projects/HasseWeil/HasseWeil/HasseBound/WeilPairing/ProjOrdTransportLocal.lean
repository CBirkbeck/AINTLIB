/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.HasseBound.WeilPairing.DivisorPullback

/-!
# `ProjOrdTransport` for a general separable isogeny from the local comap-valuation witnesses

This file abstracts the entire `[ℓ]`-`ProjOrdTransport` assembly of `DivisorPullback.lean`
(`ordTransport_affine_mulByInt` → `inftyOrdTransport_mulByInt` → `projOrdTransport_mulByInt`) away
from the multiplication isogeny `[ℓ]`, so that **any** isogeny `φ` of an elliptic curve over `K̄`
obtains `ProjOrdTransport φ` from a single sharp pair of local witnesses:

* the **affine-image comap identity**
  `(pointValuation P).comap φ.pullback = pointValuation Q` whenever `φ(P) = Q` is a finite point;
* the **infinity-image comap identity**
  `(pointValuation P).comap φ.pullback = ordAtInftyValuation` whenever `φ(P) = O`.

These two identities are *exactly* the content the general DVR order-transport glue
`comap_pointValuation_eq_of_isEquiv_of_ord_eq_one` (`EC/IsogenyOrdTransport.lean`) delivers from the
two genuine local inputs **(SamePlace)**
`((pointValuation P).comap φ.pullback).IsEquiv (place at φ(P))`
and **(e = 1)** `ord_P(φ.pullback t) = 1` for a uniformizer `t` at `φ(P)`.  So this file reduces
`ProjOrdTransport φ` — the divisor-pullback functoriality `div(φ^* h) = φ^*(div h)` that the
divisor-pushforward dual (`OneSubDualDivisor.lean`) and the whole pairing scaling consume — to those
two *per-place, per-uniformizer* facts, the reviewer's round-21 "formal-local" sub-leaves.

For `φ = [ℓ]` the two comap identities are the *proved* `comap_pointValuation_mulByInt_eq_affine` /
`_infty` (`DivisorPullback.lean`); this file's `projOrdTransport_of_comap_pointValuation` recovers
`projOrdTransport_mulByInt` as the special case (see `projOrdTransport_mulByInt'`).  For the
Frobenius pencil members `1 − π`, `rπ − s` the same two identities are the residual local content —
the generic-point covariance `hgcomm` (proved in `WallAGeometricRealization.lean`) plus a unit
formal linear coefficient (`omegaPullbackCoeff ≠ 0`, proved) would, by the reviewer's route, supply
them; those two steps (the closed-point comorphism realisation `φ^*(m_Q) ⊆ m_P` and the local
`e = 1` from the cotangent action) are the precise remaining geometric inputs, *not*
discharged here.

## What this file proves

* `ordTransport_of_comap_pointValuation` — the per-affine-point `OrdTransport φ P` from the comap
  witnesses (the verbatim generalisation of `ordTransport_affine_mulByInt`).
* `projOrdTransport_of_comap_pointValuation` — **`ProjOrdTransport φ`** assembled from the
  per-place comap identities + the infinity transport (the general reduction).

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.4.10c (unramifiedness of a separable isogeny),
  III.8.1–2.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing.DivisorPullback


variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

/-- **The local comap-valuation witnesses for a general isogeny `φ`** (Silverman III.4.10c, the
unramified order-transport, packaged at the valuation-ring level).  Bundles, for every smooth point
`P`, the comap-valuation identity `(pointValuation P).comap φ.pullback = (place at φ(P))`, split by
whether the image `φ(P)` is a finite point `Q = some x y h_ns` (affine case) or `O` (infinity case).

This is the exact pair the DVR glue `comap_pointValuation_eq_of_isEquiv_of_ord_eq_one` produces from
the two genuine local inputs (SamePlace `IsEquiv` + `e = 1` at one uniformizer); for `φ = [ℓ]` it is
the *proved* `comap_pointValuation_mulByInt_eq_affine` / `_infty`. -/
structure ComapPointValuationWitness (φ : Isogeny W.toAffine W.toAffine) : Prop where
  /-- **Affine-image comap identity**: when `φ(P) = some x y h_ns`,
  `(pointValuation P).comap φ.pullback = pointValuation ⟨x, y, h_ns⟩`. -/
  affine : ∀ (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    (_hQ : φ.toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns),
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P).comap φ.pullback.toRingHom =
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩
  /-- **Affine-image infinity comap identity**: when `φ(P) = O` for an affine smooth point `P`
  (i.e. `P` is in the kernel-coset over `O`),
  `(pointValuation P).comap φ.pullback = ordAtInftyValuation`.
  This is the affine half of the transport for points whose image is `O`. -/
  affineToInfty : ∀ (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint)
    (_hQ : φ.toAddMonoidHom P.toAffinePoint = (0 : W.toAffine.Point)),
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P).comap φ.pullback.toRingHom =
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).ordAtInftyValuation
  /-- **Infinity-place transport** `ord_∞(φ.pullback h) = ord_∞ h` (`φ(O) = O`), the comap of the
  infinity valuation along `φ.pullback`.  This is the `InftyOrdTransport φ` half — for
  `[ℓ]` it is the
  *proved* `inftyOrdTransport_mulByInt`, derived from the master pinning lemma
  `eq_ordAtInftyValuation_of_x_y` and the values `ord_∞(φ.pullback x_gen) = -2`,
  `ord_∞(φ.pullback y_gen) = -3`. -/
  infinity : InftyOrdTransport φ

variable {W}

/-- **The affine per-place order-transport for a general isogeny**, from the comap
witnesses.  For an
isogeny `φ` and an affine smooth point `P`, the order of `φ.pullback f` at `P` equals the order of
`f` at the image place `φ(P)` (finite or `∞`), with no ramification factor.  Verbatim generalisation
of `ordTransport_affine_mulByInt`: read the additive order off the comap-valuation identity via the
`exp`-bridge `pointValuation_eq_exp_neg_of_ord_P_eq`. -/
theorem ordTransport_of_comap_pointValuation {φ : Isogeny W.toAffine W.toAffine}
    (hcomap : ComapPointValuationWitness W φ)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) :
    OrdTransport φ P := by
  intro h
  rcases eq_or_ne h 0 with rfl | hh
  · rw [map_zero, (⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P_zero, WithTop.untopD_top]
    rw [projOrdAt, (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf_zero]
    rfl
  set τ := φ.pullback with hτ
  have hτh_ne : τ h ≠ 0 := fun h0 ↦ hh (φ.pullback_injective (h0.trans (map_zero _).symm))
  obtain ⟨m, hm⟩ : ∃ m : ℤ,
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P P (τ h) = (m : WithTop ℤ) := by
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
      (((⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P_eq_top_iff (τ h)).not.mpr hτh_ne)
    exact ⟨m, hm.symm⟩
  have hlhs_exp : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (τ h) = WithZero.exp (-m) :=
    pointValuation_eq_exp_neg_of_ord_P_eq (C := (⟨W.toAffine⟩ : SmoothPlaneCurve F))
      (P := P) hτh_ne hm
  rcases hQcase : φ.toAddMonoidHom P.toAffinePoint with _ | ⟨x, y, h_ns⟩
  · -- image `O`
    have hval := hcomap.affineToInfty P hQcase
    have h_at : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (τ h) =
        (⟨W.toAffine⟩ : SmoothPlaneCurve F).ordAtInftyValuation h := by
      have := congrFun (congrArg DFunLike.coe hval) h
      rwa [Valuation.comap_apply] at this
    obtain ⟨n, hn⟩ : ∃ n : ℤ, (⟨W.toAffine⟩ : SmoothPlaneCurve F).ordAtInfty h = (n : WithTop ℤ) :=
      ⟨_, (⟨W.toAffine⟩ : SmoothPlaneCurve F).ordAtInfty_of_ne hh⟩
    rw [hlhs_exp,
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq hh hn,
      WithZero.exp_inj] at h_at
    change ((⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P P (τ h)).untopD 0 =
      projOrdAt h (0 : W.toAffine.Point)
    rw [projOrdAt_zero, hm, hn, WithTop.untopD_coe, WithTop.untopD_coe]
    omega
  · -- image `some x y h_ns`
    have hval := hcomap.affine P h_ns hQcase
    have h_at : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (τ h) =
        (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩ h := by
      have := congrFun (congrArg DFunLike.coe hval) h
      rwa [Valuation.comap_apply] at this
    obtain ⟨n, hn⟩ : ∃ n : ℤ,
        (⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P ⟨x, y, h_ns⟩ h = (n : WithTop ℤ) := by
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp
        (((⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P_eq_top_iff (P := ⟨x, y, h_ns⟩) h).not.mpr hh)
      exact ⟨n, hn.symm⟩
    rw [hlhs_exp, pointValuation_eq_exp_neg_of_ord_P_eq (C := (⟨W.toAffine⟩ : SmoothPlaneCurve F))
        (P := (⟨x, y, h_ns⟩ : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint)) hh hn,
      WithZero.exp_inj] at h_at
    rw [projOrdAt_some, hm, hn, WithTop.untopD_coe, WithTop.untopD_coe]
    omega

/-- **`ProjOrdTransport φ` from the local comap witnesses** (the general reduction, Silverman
III.4.10c).  For *any* isogeny `φ` of `E` over `K̄`, the divisor-pullback functoriality
`div(φ^* h) = φ^*(div h)` — i.e. `ProjOrdTransport φ` — follows from the single pair of local
comap-valuation identities `ComapPointValuationWitness W φ` (the affine-image and infinity-image
cases), via the affine/infinity assembly `projOrdTransport_of_affine_of_infinity`.

This is the abstract form of the `[ℓ]` chain `ordTransport_affine_mulByInt` +
`inftyOrdTransport_mulByInt` ⟹ `projOrdTransport_mulByInt`, with the two comap identities — the
**SamePlace** + **e = 1** content packaged at the valuation level — taken as hypotheses.  It is the
target the divisor-pushforward dual (`OneSubDualDivisor.lean`) and the pairing scaling consume, now
reduced to the two sharp per-place witnesses the reviewer's formal-local route produces. -/
theorem projOrdTransport_of_comap_pointValuation {φ : Isogeny W.toAffine W.toAffine}
    (hcomap : ComapPointValuationWitness W φ) :
    ProjOrdTransport φ :=
  projOrdTransport_of_affine_of_infinity
    (fun P ↦ ordTransport_of_comap_pointValuation hcomap P)
    hcomap.infinity

/-! ### Sanity instantiation: `[ℓ]` recovers `projOrdTransport_mulByInt`

The two proved `[ℓ]` comap identities `comap_pointValuation_mulByInt_eq_affine` / `_infty` assemble
into a `ComapPointValuationWitness W (mulByInt W ℓ)`, so the general reduction recovers the shipped
`projOrdTransport_mulByInt`.  This confirms the abstraction is faithful (same statement, same proof
content) for the one isogeny whose local witnesses are fully proved. -/

/-- The `[ℓ]` comap-valuation witnesses, packaged from the proved affine/infinity comap
identities. -/
theorem comapPointValuationWitness_mulByInt [IsAlgClosed F] (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) :
    ComapPointValuationWitness W (mulByInt W.toAffine ℓ) where
  affine := fun P {x y} h_ns hQ ↦
    comap_pointValuation_mulByInt_eq_affine (W := W.toAffine) ℓ hℓ P (x := x) (y := y) h_ns hQ
  affineToInfty := fun P hQ ↦ comap_pointValuation_mulByInt_eq_infty (W := W.toAffine) ℓ hℓ P hQ
  infinity := by
    have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at hℓ
    exact inftyOrdTransport_mulByInt (W := W.toAffine) ℓ hℓ0 hℓ

/-- **`ProjOrdTransport [ℓ]` via the general reduction** — recovers `projOrdTransport_mulByInt` from
`projOrdTransport_of_comap_pointValuation` applied to the proved `[ℓ]` comap witnesses.  A faithful
re-derivation confirming the abstraction. -/
theorem projOrdTransport_mulByInt' [IsAlgClosed F] (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) :
    ProjOrdTransport (mulByInt W.toAffine ℓ) :=
  projOrdTransport_of_comap_pointValuation (comapPointValuationWitness_mulByInt (W := W) ℓ hℓ)

end HasseWeil.WeilPairing.DivisorPullback

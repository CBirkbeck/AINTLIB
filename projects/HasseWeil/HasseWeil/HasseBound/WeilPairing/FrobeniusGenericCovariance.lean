/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.HasseBound.WeilPairing.MapTranslateGenericAdditive
import HasseWeil.Foundation.Curves.Frobenius.FrobeniusFixedPoint
import HasseWeil.HasseBound.WeilPairing.OneSubFrobeniusBaseChangeWitnesses

/-!
# The Frobenius generic-point covariance leaf is PROVABLE over `K̄` (reviewer round-21 "Wall B")

The reviewer's round-21 formal-local route reduces the translation covariance `hcomm'` and degree
match `#ker = deg` of the separable pencil `1 − π`, `rπ − s` to the **generic-point covariance**
leaf `MapTranslateGenericPoint φ g` (`SeparableWitnesses.lean`, `MapTranslateGenericAdditive.lean`):

  `Point.map τ_S (g P_gen) = g P_gen + lift (φ.toAddMonoidHom S)`.

The structural decomposition `mapTranslateGenericPoint_add` (`MapTranslateGenericAdditive.lean`)
reduces this for `1 − π = addIsog(id, −π)` and `rπ − s = addIsog(r·π, −s·id)` to the component
leaves for `[m]` (shipped, free via the division-polynomial coordinate formula `ScratchCov`) and for
the **Frobenius** `π`.

This file proves the Frobenius component leaf **over `K̄`**, axiom-clean and CoordHom-free
(`frobeniusGenericCovariance_Kbar`):

  `Point.map τ_S (frobₗ P_gen) = frobₗ P_gen + lift (π̄ S)`,

where `frobₗ = Affine.Point.map (FiniteField.frobeniusAlgHom 𝔽_q (K̄(E)))` is the geometric action
of
the `q`-power Frobenius on the function-field points of `E_{K̄}`, and `π̄ = frobeniusHomBaseChange`
(`= geomFrobeniusPoint`) is the `q`-power Frobenius point map.

## Why this is **not** free from genuineness alone (refuting the over-strong claim)

`MapTranslateGenericPoint φ (Affine.Point.map φ.pullback)` (the **canonical** action) is **not**
derivable from genuineness of the canonical action — which is free for *every* isogeny
(`isogeny_isGenuineWith_pointMap`).  If it were, `hgcomm` would hold for **all** isogenies including
`[ℓ]`, contradicting the shipped `[ℓ]` proof (`ScratchCov.comm_point_mulByInt`), which crucially
uses
the division-polynomial coordinate formula `map_pullback_genericPoint` (`[ℓ]^* P_gen = ℓ • P_gen`)
*beyond* genuineness.  The genuine content is exactly the realization of the abstract pullback's
value
at `P_gen` as a *translatable* geometric action.

## The arithmetic at the heart of the Frobenius leaf (the `K̄`-vs-`𝔽_q` dichotomy)

Over the base field `K = 𝔽_q` the leaf is **degenerate**: `π` acts as the identity on `𝔽_q`-points
(`π S = (S_x^q, S_y^q) = S` by Fermat), so `lift (π S) = lift S`, and the honest computation
`Point.map τ_S (frobₗ P_gen) = frobₗ (P_gen + lift S) = frobₗ P_gen + lift S` already matches.

Over `K̄` the leaf is **genuine** and the same computation now produces the correct twist:
`frobₗ (lift S) = lift (π̄ S)` (`frobeniusGenericCovariance_lift_twist`), because the `q`-power on
the
`algebraMap`'d coordinates of a `K̄`-point `S` is exactly the geometric Frobenius `π̄ S = (S_x^q,
S_y^q)` (`geomFrobeniusPointFun_some`).  Crucially `frobₗ` is **only** `𝔽_q`-linear (the `q`-power
is
not `K̄`-linear), so it does *not* fix `lift S` for a general `K̄`-point — unlike over `𝔽_q`.

So the Frobenius generic-point covariance is **formal for the `q`-power Frobenius specifically** (a
coordinate-power comorphism), in contrast to a general isogeny whose comorphism is not a coordinate
power and whose covariance is genuine geometric content needing the division-polynomial formula.

## Scalar-tower note (the `Point.map` `W'` diamond)

The `q`-power Frobenius `frobₗ` on `E_{K̄}` is the `𝔽_q`-algebra hom `frobeniusAlgHom 𝔽_q (K̄(E))`;
it is **not** `K̄`-linear, so it is **not** expressible as `Affine.Point.map (W' := W.baseChange
K̄)`
(which demands `K̄`-linearity, triggering the spurious `Algebra K̄ 𝔽_q` synthesis).  We type it via
`Affine.Point.map (W' := W)` over the *base* curve `W : WeierstrassCurve 𝔽_q`, whose codomain
`W.baseChange (K̄(E))` is **definitionally** `(W.baseChange K̄).baseChange (K̄(E)) = W_KE
(W.baseChange
K̄)` by the scalar tower `𝔽_q → K̄ → K̄(E)`.  The bridge between the two `Point.map` typings of the
`K̄`-linear translation `τ_S` is `frobeniusGenericCovariance_tau_mapW` (`cases <;> rfl`).

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.8.2 (translation covariance), III.4
(Frobenius).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil


section FrobeniusKbar

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

noncomputable local instance instDecEqACFGC : DecidableEq (AlgebraicClosure K) := Classical.decEq _

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]

/-- **The geometric action of the `q`-power Frobenius on function-field points of `E_{K̄}`**:
`Affine.Point.map` of the `𝔽_q`-algebra `q`-power Frobenius `frobeniusAlgHom K (K̄(E))`, typed via
the *base* curve `W : WeierstrassCurve 𝔽_q` (so it sidesteps the `K̄`-linearity diamond — the
`q`-power is not `K̄`-linear).  Its codomain `W.baseChange (K̄(E))` is definitionally
`W_KE (W.baseChange K̄)` by the scalar tower `𝔽_q → K̄ → K̄(E)`. -/
noncomputable def frobFunctionFieldPointKbar :
    (W_KE (W.baseChange (AlgebraicClosure K))).toAffine.Point →+
      (W_KE (W.baseChange (AlgebraicClosure K))).toAffine.Point :=
  WeierstrassCurve.Affine.Point.map (W' := W)
    (FiniteField.frobeniusAlgHom K (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField)

omit [Fintype K] [DecidableEq K] [W.toAffine.IsElliptic] in
/-- **Cross-`W'` `Point.map` bridge for the translation `τ_S`** (the scalar-tower diamond fix).  The
`K̄`-linear translation `τ_S = translateAlgEquivOfPoint (W.baseChange K̄) S`, applied via
`Affine.Point.map (W' := W.baseChange K̄)`, equals its `𝔽_q`-restriction applied via
`Affine.Point.map (W' := W)` (over the base curve).  Both `Point.map`s act through the *same*
underlying ring hom on coordinates, so the equality is `cases <;> rfl`.  This lets `map_map` compose
`τ_S` with the `𝔽_q`-typed `frobFunctionFieldPointKbar` at a uniform `W' := W`. -/
theorem frobeniusGenericCovariance_tau_mapW (S : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (P : (W_KE (W.baseChange (AlgebraicClosure K))).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (W' := W.baseChange (AlgebraicClosure K))
        (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S).toAlgHom P =
      WeierstrassCurve.Affine.Point.map (W' := W)
        ((HasseWeil.translateAlgEquivOfPoint
          (W.baseChange (AlgebraicClosure K)) S).toAlgHom.restrictScalars K) P := by
  cases P <;> rfl

omit [W.toAffine.IsElliptic] in
/-- **The lift-twist fact over `K̄`** (the heart of the `K̄`-vs-`𝔽_q` dichotomy; Silverman III.4).
The `q`-power function-field Frobenius `frobFunctionFieldPointKbar` sends the lift of a `K̄`-point
`S`
to the lift of its **geometric Frobenius** `π̄ S = geomFrobeniusPointFun S`:

  `frobₗ (lift S) = lift (π̄ S)`.

Coordinate case split: `lift (some sx sy) = some (algebraMap sx) (algebraMap sy)`, and
`frobₗ (some a b) = some (a^q) (b^q)`, so `frobₗ (lift S) = some ((algebraMap sx)^q, (algebraMap
sy)^q)
= some (algebraMap (sx^q), algebraMap (sy^q)) = lift (some (sx^q, sy^q)) = lift (π̄ S)`
(`geomFrobeniusPointFun_some`).  This is **false** over `𝔽_q` only in the sense that there `π̄ =
id`;
the identity itself holds for any base, but is *non-degenerate* (twisting) precisely over `K̄`. -/
theorem frobeniusGenericCovariance_lift_twist
    (S : (W.baseChange (AlgebraicClosure K)).toAffine.Point) :
    frobFunctionFieldPointKbar W (HasseWeil.liftPointToKE (W.baseChange (AlgebraicClosure K)) S) =
      HasseWeil.liftPointToKE (W.baseChange (AlgebraicClosure K)) (geomFrobeniusPointFun W S) := by
  rcases S with _ | ⟨sx, sy, hns⟩
  · show frobFunctionFieldPointKbar W
          (HasseWeil.liftPointToKE (W.baseChange (AlgebraicClosure K)) 0) =
        HasseWeil.liftPointToKE (W.baseChange (AlgebraicClosure K)) (geomFrobeniusPointFun W 0)
    rw [geomFrobeniusPointFun_zero, map_zero, map_zero]
  · rw [geomFrobeniusPointFun_some, HasseWeil.liftPointToKE_some, HasseWeil.liftPointToKE_some,
      HasseWeil.liftSomePoint, HasseWeil.liftSomePoint]
    show WeierstrassCurve.Affine.Point.map (W' := W)
        (FiniteField.frobeniusAlgHom K (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField)
        (Affine.Point.some _ _ _) = Affine.Point.some _ _ _
    refine (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨?_, ?_⟩ <;>
      simp only [FiniteField.coe_frobeniusAlgHom] <;> rw [← map_pow]

omit [DecidableEq K] [W.toAffine.IsElliptic] in
set_option backward.isDefEq.respectTransparency false in
/-- **The `q`-power Frobenius commutes with translation on function-field points of `E_{K̄}`**
(point-level form; the `K̄` analogue of `frobeniusIsog_pullback_universal_commute`).  For the
`q`-power action `frobₗ` and the `𝔽_q`-restricted translation `τ_S` (both typed via `W' := W`):

  `Point.map τ_S (frobₗ P) = frobₗ (Point.map τ_S P)`.

Coordinate case split: on `some (x, y)` both sides are `some` whose coordinates differ only by the
commutation of the `q`-power with the ring hom `τ_S`, i.e. `τ_S (x^q) = (τ_S x)^q` (`map_pow`). -/
theorem frobeniusGenericCovariance_frob_tau_comm
    (S : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (P : (W_KE (W.baseChange (AlgebraicClosure K))).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (W' := W)
        ((HasseWeil.translateAlgEquivOfPoint
          (W.baseChange (AlgebraicClosure K)) S).toAlgHom.restrictScalars K)
        (frobFunctionFieldPointKbar W P) =
      frobFunctionFieldPointKbar W
        (WeierstrassCurve.Affine.Point.map (W' := W)
          ((HasseWeil.translateAlgEquivOfPoint
            (W.baseChange (AlgebraicClosure K)) S).toAlgHom.restrictScalars K) P) := by
  rcases P with _ | ⟨x, y, hns⟩
  · rfl
  · show WeierstrassCurve.Affine.Point.map (W' := W)
          ((HasseWeil.translateAlgEquivOfPoint
            (W.baseChange (AlgebraicClosure K)) S).toAlgHom.restrictScalars K)
          (WeierstrassCurve.Affine.Point.map (W' := W)
            (FiniteField.frobeniusAlgHom K
              (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField)
            (Affine.Point.some x y hns)) =
        WeierstrassCurve.Affine.Point.map (W' := W)
          (FiniteField.frobeniusAlgHom K (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField)
          (WeierstrassCurve.Affine.Point.map (W' := W)
            ((HasseWeil.translateAlgEquivOfPoint
              (W.baseChange (AlgebraicClosure K)) S).toAlgHom.restrictScalars K)
            (Affine.Point.some x y hns))
    rw [WeierstrassCurve.Affine.Point.map_some (W' := W),
      WeierstrassCurve.Affine.Point.map_some (W' := W),
      WeierstrassCurve.Affine.Point.map_some (W' := W),
      WeierstrassCurve.Affine.Point.map_some (W' := W)]
    refine (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨?_, ?_⟩ <;>
      · simp only [FiniteField.coe_frobeniusAlgHom]
        exact map_pow (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S) _ _

omit [W.toAffine.IsElliptic] in
/-- **The Frobenius generic-point covariance leaf over `K̄`** (Silverman III.8.2 for `π̄`),
axiom-clean
and CoordHom-free — the round-21 "Wall B" residual, **proven** for the `q`-power Frobenius:

  `Point.map τ_S (frobₗ P_gen) = frobₗ P_gen + lift (π̄ S)`,

where `frobₗ = frobFunctionFieldPointKbar` is the geometric `q`-power action and the twist
`π̄ S = geomFrobeniusPointFun S` is the geometric Frobenius (`= frobeniusHomBaseChange S`).

Proof: convert `τ_S` to the `W' := W` typing (`tau_mapW`), commute it past `frobₗ`
(`frob_tau_comm`), convert back, apply the master translation lemma
(`translateAlgEquivOfPoint_map_genericPoint`: `Point.map τ_S P_gen = P_gen + lift S`), then use that
`frobₗ` is additive (`map_add`) and the lift-twist `frobₗ (lift S) = lift (π̄ S)` (`lift_twist`). -/
theorem frobeniusGenericCovariance_Kbar (S : (W.baseChange (AlgebraicClosure K)).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (W' := W.baseChange (AlgebraicClosure K))
        (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S).toAlgHom
        (frobFunctionFieldPointKbar W
          (HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K)))) =
      frobFunctionFieldPointKbar W (HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K))) +
        HasseWeil.liftPointToKE (W.baseChange (AlgebraicClosure K))
          (geomFrobeniusPointFun W S) := by
  rw [frobeniusGenericCovariance_tau_mapW, frobeniusGenericCovariance_frob_tau_comm,
    ← frobeniusGenericCovariance_tau_mapW,
    HasseWeil.translateAlgEquivOfPoint_map_genericPoint (W.baseChange (AlgebraicClosure K)) S]
  change frobFunctionFieldPointKbar W (HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K)) +
      HasseWeil.liftPointToKE (W.baseChange (AlgebraicClosure K)) S) = _
  rw [map_add, frobeniusGenericCovariance_lift_twist]

/-- **The Frobenius generic-point covariance as a `MapTranslateGenericPoint` leaf** (the form the
`mapTranslateGenericPoint_add` decomposition consumes for the `±π` component of `1 − π` / `rπ − s`).
Packages `frobeniusGenericCovariance_Kbar` against the base-changed Frobenius isogeny
`φ = frobeniusIsog_baseChange_charP_pow` (whose point map is `π̄ = frobeniusHomBaseChange =
geomFrobeniusPoint`), with geometric action `frobₗ = frobFunctionFieldPointKbar`.

This realizes the reviewer's claim that the Frobenius covariance is **provable** (not carried) over
`K̄`, modulo only the genuineness link `frobₗ P_gen = (φ^* x_gen, φ^* y_gen)` (Wall A) for the
*concrete base-changed pullback* — which is **not** supplied here (it is the genuine residual: the
opaque `baseChangePullback` conjugate at the generic point, requiring the unbuilt `Φ`-generic-point
compatibility). -/
theorem mapTranslateGenericPoint_frobenius_Kbar
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)] :
    MapTranslateGenericPoint (W.baseChange (AlgebraicClosure K))
      (Isogeny.frobeniusIsog_baseChange_charP_pow p r W (AlgebraicClosure K))
      (frobFunctionFieldPointKbar W) := by
  intro S
  -- `φ.toAddMonoidHom S = π̄ S = geomFrobeniusPoint S = geomFrobeniusPointFun S`.
  have hπ : (Isogeny.frobeniusIsog_baseChange_charP_pow p r W
      (AlgebraicClosure K)).toAddMonoidHom S =
      geomFrobeniusPointFun W S := by
    have := frobeniusHomBaseChange_eq_geomFrobeniusPoint W p r
    rw [frobeniusHomBaseChange] at this
    rw [this]
    rfl
  rw [hπ]
  exact frobeniusGenericCovariance_Kbar W S

end FrobeniusKbar

end HasseWeil.WeilPairing

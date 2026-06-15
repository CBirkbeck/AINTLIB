/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.WallAGenericRealization
import HasseWeil.Hasse.IsogOneSubXyFamily
import HasseWeil.WeilPairing.FrobeniusGenericCovariance
import HasseWeil.WeilPairing.SeparableWitnesses

/-!
# Wall A closed for `1 − π`: the base-changed pullback is a genuine translatable action over `K̄`

This file completes Wall A (G-004) for the separable isogeny `1 − π` base-changed to `K̄`: it proves
that the **concrete** opaque base-changed pullback `pullback_L = baseChangePullback (1 − π).pullback`
is *genuine* with the translatable geometric action `g = id − π̄` over `K̄`, i.e.

  `IsGenuineWith (W.baseChange K̄) (oneSubFrobeniusIsogBaseChange … pullback_L) (id − π̄)`

(`oneSub_isGenuineWith_Kbar`), where `π̄ = frobFunctionFieldPointKbar` is the `q`-power geometric
Frobenius on function-field points of `E_{K̄}`.  This is the genuineness the `SeparableWitnesses`
reductions (`mapTranslateGenericPoint_canonical_of_genuine`, `oneSub_hcommPrime_of_hgcomm`, …)
consume, and it is established **CoordHom-free** — the entire route is the function-field
base-change naturality `functionFieldMap`, complete in the project.

## The route (reviewer round-21 transport-of-genuineness, CoordHom-free)

The genuineness unfolds to a coordinate identity at the generic point:
`g (P_gen^{K̄}) = (pullback_L x_gen^{K̄}, pullback_L y_gen^{K̄})`.  We establish it by transporting
the **`K`-level** addition-formula realization through the function-field base change:

1. **`ffBaseChangePoint`** — the function-field base-change point map `Affine.Point.map
   (functionField_baseChange)`, typed via `W' := W` over the base field `K` (scalar tower
   `K → L → K(E_L)`).  It sends `genericPoint W ↦ genericPoint (W.baseChange L)`
   (`ffBaseChangePoint_genericPoint`, `WallAGenericRealization.lean`) and intertwines the `q`-power
   geometric Frobenius (`ffbc_frob_comm`: `ffBaseChangePoint ∘ frobeniusW_KE = π̄ ∘ ffBaseChangePoint`,
   from `Affine.Point.map_some` + `map_pow` — the `q`-power commutes with the ring hom `functionFieldMap`).

2. **`gKbar_genericPoint`** — the geometric `K̄`-action `g = id − π̄` evaluated at `P_gen^{K̄}` equals
   `ffBaseChangePoint (P_gen − π(P_gen))`, the function-field base-change of the `K`-level
   geometric `1 − π` image of the generic point (additivity of `ffBaseChangePoint` + the two
   commutation facts).

3. **`genericPoint_sub_frobeniusW_KE_apply`** (shipped, `IsogOneSubXyFamily.lean`): the `K`-level
   realization `P_gen − π(P_gen) = (addPullback_x, addPullback_y)` with
   `addPullback_? = (1 − π).pullback ?_gen` (`oneSub_pullback_x/y_gen_eq`).

4. **`oneSubFrobeniusPullback_L_x/y_gen`** (the G-004 square, `WallAGenericRealization.lean`):
   `pullback_L ?_gen^{K̄} = functionFieldMap ((1 − π).pullback ?_gen)`.

Chaining 1–4: `g (P_gen^{K̄}) = ffBaseChangePoint (some addPullback_x addPullback_y) =
some (functionFieldMap addPullback_x) (functionFieldMap addPullback_y) = some (pullback_L x_gen^{K̄})
(pullback_L y_gen^{K̄})`.  This is exactly `IsGenuineWith φ_L (id − π̄)`.

## Why this is CoordHom-free and non-degenerate

The transported identity is a **generic-point** identity, where Frobenius acts *nontrivially*
(`π̄ ≠ id` over `K̄`, unlike on `𝔽_q`-points).  The opaque `pullback_L` has poles at the affine
kernel, so it admits **no** `CoordHom`; the realization goes purely through `functionFieldMap` (the
natural function-field inclusion), never through a coordinate-ring endomorphism.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, I.2 (base change), III.4.2 (generic point),
  III.4 (Frobenius), III.8.2 (translation covariance).
-/

open WeierstrassCurve HasseWeil.Curves HasseWeil HasseWeil.WeilPairing.IsogenyBaseChangeConcrete
open scoped TensorProduct

namespace HasseWeil.WeilPairing

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

noncomputable section

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] (W : WeierstrassCurve K)
  [W.toAffine.IsElliptic]

noncomputable local instance instDecEqACGeom : DecidableEq (AlgebraicClosure K) := Classical.decEq _

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]

/-- **The `q`-power geometric Frobenius commutes with the function-field base-change point map**
(Silverman III.4, base change).  For the function-field base-change point map `ffBaseChangePoint`
and the geometric `q`-power Frobenius `frobeniusW_KE` (over `K`) / `frobFunctionFieldPointKbar`
(over `K̄`):

  `ffBaseChangePoint (frobeniusW_KE P) = frobFunctionFieldPointKbar (ffBaseChangePoint P)`.

Coordinate case split: on `some (x, y)` both reduce — via `Affine.Point.map_some` — to the
commutation `functionFieldMap (x^q) = (functionFieldMap x)^q` (`map_pow`, `functionFieldMap` a
ring hom).  This is the lynchpin of `gKbar_genericPoint`. -/
theorem ffbc_frob_comm (P : (W_KE W).toAffine.Point) :
    ffBaseChangePoint W (AlgebraicClosure K) (frobeniusW_KE W P) =
      frobFunctionFieldPointKbar W (ffBaseChangePoint W (AlgebraicClosure K) P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [frobeniusW_KE_some, ffBaseChangePoint_some]
    show Affine.Point.some _ _ _ =
      WeierstrassCurve.Affine.Point.map (W' := W)
        (FiniteField.frobeniusAlgHom K (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField)
        (Affine.Point.some
          ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionField_baseChange (AlgebraicClosure K) x)
          ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionField_baseChange (AlgebraicClosure K) y) _)
    rw [WeierstrassCurve.Affine.Point.map_some]
    refine (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨?_, ?_⟩
    · show (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K) (x ^ Fintype.card K) =
        ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K) x) ^ Fintype.card K
      rw [map_pow]
    · show (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K) (y ^ Fintype.card K) =
        ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K) y) ^ Fintype.card K
      rw [map_pow]

/-- **The geometric `K̄`-action `id − π̄`** for `(1 − π)_{K̄}`: the function-field point map
`id − frobFunctionFieldPointKbar` on `E_{K̄}`-points.  This is the *translatable* action realizing
the base-changed `1 − π`. -/
noncomputable def gKbar :
    (W_KE (W.baseChange (AlgebraicClosure K))).toAffine.Point →+
      (W_KE (W.baseChange (AlgebraicClosure K))).toAffine.Point :=
  AddMonoidHom.id _ - frobFunctionFieldPointKbar W

/-- **`gKbar` at the generic point is the function-field base-change of the `K`-level `1 − π`
image** (Silverman III.8.2, base change): `gKbar (P_gen^{K̄}) = ffBaseChangePoint (P_gen − π(P_gen))`.
Additivity of `ffBaseChangePoint` + `ffBaseChangePoint_genericPoint` + `ffbc_frob_comm`. -/
theorem gKbar_genericPoint :
    gKbar W (HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K))) =
      ffBaseChangePoint W (AlgebraicClosure K)
        (HasseWeil.genericPoint W - frobeniusW_KE W (HasseWeil.genericPoint W)) := by
  rw [gKbar, AddMonoidHom.sub_apply, AddMonoidHom.id_apply]
  have h1 : ffBaseChangePoint W (AlgebraicClosure K)
      (HasseWeil.genericPoint W - frobeniusW_KE W (HasseWeil.genericPoint W)) =
      ffBaseChangePoint W (AlgebraicClosure K) (HasseWeil.genericPoint W) -
        ffBaseChangePoint W (AlgebraicClosure K) (frobeniusW_KE W (HasseWeil.genericPoint W)) :=
    map_sub (ffBaseChangePoint W (AlgebraicClosure K)) _ _
  rw [h1, ffbc_frob_comm, ffBaseChangePoint_genericPoint]
  congr 1

variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]

/-- `(1 − π).pullback x_gen = addPullback_x` (the `K`-level addition-formula x-coordinate). -/
theorem oneSub_pullback_x_gen_eq (hq : 2 ≤ Fintype.card K) :
    (HasseWeil.isogOneSub_negFrobenius W hq).pullback (HasseWeil.x_gen W) =
      HasseWeil.addPullback_x W (HasseWeil.negFrobeniusIsog W) := by
  rw [HasseWeil.isogOneSub_negFrobenius_pullback, HasseWeil.addPullbackAlgHom_negFrobenius_x_gen_eq]

/-- `(1 − π).pullback y_gen = addPullback_y` (the `K`-level addition-formula y-coordinate). -/
theorem oneSub_pullback_y_gen_eq (hq : 2 ≤ Fintype.card K) :
    (HasseWeil.isogOneSub_negFrobenius W hq).pullback (HasseWeil.y_gen W) =
      HasseWeil.addPullback_y W (HasseWeil.negFrobeniusIsog W) := by
  rw [HasseWeil.isogOneSub_negFrobenius_pullback, HasseWeil.addPullbackAlgHom_negFrobenius_y_gen_eq]

/-- `gKbar` at the generic point, typed via the `W' := W` base-change point map (the form fed to
genuineness; `gKbar_genericPoint` with `ffBaseChangePoint` unfolded). -/
theorem gKbar_genericPoint_eq_map (hq : 2 ≤ Fintype.card K) :
    gKbar W (HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K))) =
      WeierstrassCurve.Affine.Point.map (W' := W) (S := K)
        ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionField_baseChange (AlgebraicClosure K))
        (HasseWeil.genericPoint W - frobeniusW_KE W (HasseWeil.genericPoint W)) := by
  rw [gKbar_genericPoint]; rfl

set_option maxHeartbeats 1600000 in
/-- **Wall A closed for `1 − π` (CoordHom-free).**  The concrete base-changed pullback
`pullback_L = oneSubFrobeniusPullback_L` is *genuine* with the translatable geometric action
`gKbar = id − π̄` over `K̄`:

  `IsGenuineWith (W.baseChange K̄) (oneSubFrobeniusIsogBaseChange … pullback_L) (id − π̄)`.

This realizes the opaque base-changed pullback at the generic point — the genuine residual the
`SeparableWitnesses` reductions consume (via `mapTranslateGenericPoint_canonical_of_genuine`),
established purely through the function-field base-change naturality `functionFieldMap`.

Proof: `gKbar (P_gen^{K̄}) = ffBaseChangePoint (P_gen − π(P_gen))` (`gKbar_genericPoint_eq_map`)
`= ffBaseChangePoint (some addPullback_x addPullback_y _)` (`genericPoint_sub_frobeniusW_KE_apply`)
`= some (functionFieldMap addPullback_x) (functionFieldMap addPullback_y) _` (`Affine.Point.map_some`,
definitional), and `functionFieldMap addPullback_? = functionFieldMap ((1 − π).pullback ?_gen) =
pullback_L ?_gen^{K̄}` (`oneSub_pullback_?_gen_eq` + `oneSubFrobeniusPullback_L_?_gen`). -/
theorem oneSub_isGenuineWith_Kbar (hq : 2 ≤ Fintype.card K) :
    HasseWeil.IsGenuineWith (W.baseChange (AlgebraicClosure K))
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
      (gKbar W) := by
  have hgen : gKbar W (HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K))) =
      WeierstrassCurve.Affine.Point.map (W' := W) (S := K)
        ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionField_baseChange (AlgebraicClosure K))
        (HasseWeil.genericPoint W - frobeniusW_KE W (HasseWeil.genericPoint W)) :=
    gKbar_genericPoint_eq_map W hq
  rw [HasseWeil.genericPoint_sub_frobeniusW_KE_apply] at hgen
  refine ⟨_, _, _, hgen, ?_, ?_⟩
  · rw [oneSubFrobeniusIsogBaseChange_pullback,
      oneSubFrobeniusPullback_L_x_gen W (AlgebraicClosure K) hq, oneSub_pullback_x_gen_eq W hq,
      SmoothPlaneCurve.functionField_baseChange_apply]
  · rw [oneSubFrobeniusIsogBaseChange_pullback,
      oneSubFrobeniusPullback_L_y_gen W (AlgebraicClosure K) hq, oneSub_pullback_y_gen_eq W hq,
      SmoothPlaneCurve.functionField_baseChange_apply]

/-! ### Chaining: the generic-point covariance `hgcomm` for `gKbar` and for the canonical action -/

/-- **`gKbar` satisfies the generic-point covariance leaf `MapTranslateGenericPoint`** (Silverman
III.8.2 for `1 − π` over `K̄`).  Direct from the additive structure `gKbar = id − π̄`: the identity
component is the master translation lemma `translateAlgEquivOfPoint_map_genericPoint`
(`Point.map τ_S P_gen = P_gen + lift S`), the Frobenius component is `frobeniusGenericCovariance_Kbar`
(`Point.map τ_S (π̄ P_gen) = π̄ P_gen + lift (π̄ S)`), and the two lifts recombine to
`lift (S − π̄ S) = lift (φ_L S)`. -/
theorem mapTranslateGenericPoint_gKbar (hq : 2 ≤ Fintype.card K) :
    MapTranslateGenericPoint (W.baseChange (AlgebraicClosure K))
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
      (gKbar W) := by
  intro S
  set L := AlgebraicClosure K
  -- LHS: Point.map τ_S (gKbar P_gen) = Point.map τ_S (P_gen − π̄ P_gen)
  --    = Point.map τ_S P_gen − Point.map τ_S (π̄ P_gen)
  have hgK : gKbar W (HasseWeil.genericPoint (W.baseChange L)) =
      HasseWeil.genericPoint (W.baseChange L) -
        frobFunctionFieldPointKbar W (HasseWeil.genericPoint (W.baseChange L)) := by
    rw [gKbar, AddMonoidHom.sub_apply, AddMonoidHom.id_apply]
  rw [hgK]
  have hms : WeierstrassCurve.Affine.Point.map (W' := W.baseChange L)
        (HasseWeil.translateAlgEquivOfPoint (W.baseChange L) S).toAlgHom
        (HasseWeil.genericPoint (W.baseChange L) -
          frobFunctionFieldPointKbar W (HasseWeil.genericPoint (W.baseChange L))) =
      WeierstrassCurve.Affine.Point.map (W' := W.baseChange L)
        (HasseWeil.translateAlgEquivOfPoint (W.baseChange L) S).toAlgHom
        (HasseWeil.genericPoint (W.baseChange L)) -
      WeierstrassCurve.Affine.Point.map (W' := W.baseChange L)
        (HasseWeil.translateAlgEquivOfPoint (W.baseChange L) S).toAlgHom
        (frobFunctionFieldPointKbar W (HasseWeil.genericPoint (W.baseChange L))) :=
    map_sub _ _ _
  rw [hms]
  -- identity component + Frobenius component
  rw [HasseWeil.translateAlgEquivOfPoint_map_genericPoint (W.baseChange L) S,
    frobeniusGenericCovariance_Kbar W S]
  -- φ_L.toAddMonoidHom S = S − π̄ S  (= id − geomFrobeniusPoint)
  have hφS : (oneSubFrobeniusIsogBaseChange W p r L
        (oneSubFrobeniusPullback_L W L hq)).toAddMonoidHom S =
      S - geomFrobeniusPointFun W S := by
    rw [oneSubFrobeniusIsogBaseChange_toAddMonoidHom, AddMonoidHom.sub_apply, AddMonoidHom.id_apply]
    congr 1
    exact DFunLike.congr_fun (frobeniusHomBaseChange_eq_geomFrobeniusPoint W p r) S
  -- lift (S − π̄ S) = lift S − lift (π̄ S)
  have hlift : HasseWeil.liftPointToKE (W.baseChange L)
        ((oneSubFrobeniusIsogBaseChange W p r L
          (oneSubFrobeniusPullback_L W L hq)).toAddMonoidHom S) =
      HasseWeil.liftPointToKE (W.baseChange L) S -
        HasseWeil.liftPointToKE (W.baseChange L) (geomFrobeniusPointFun W S) := by
    rw [hφS, map_sub]
  rw [hlift]
  abel

/-- **The canonical-action generic-point covariance `hgcomm` for `(1 − π)_{K̄}`** (Silverman III.8.2),
CoordHom-free — the form the `SeparableWitnesses` reductions consume.  From `oneSub_isGenuineWith_Kbar`
(genuineness with `gKbar`) + `mapTranslateGenericPoint_gKbar` (the covariance for `gKbar`), via
`mapTranslateGenericPoint_canonical_of_genuine`. -/
theorem mapTranslateGenericPoint_oneSub_canonical (hq : 2 ≤ Fintype.card K) :
    MapTranslateGenericPoint (W.baseChange (AlgebraicClosure K))
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
      (WeierstrassCurve.Affine.Point.map (W' := W.baseChange (AlgebraicClosure K))
        (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
          (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback) :=
  mapTranslateGenericPoint_canonical_of_genuine (W.baseChange (AlgebraicClosure K))
    (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
    (oneSub_isGenuineWith_Kbar W p r hq) (mapTranslateGenericPoint_gKbar W p r hq)

/-- **The translation covariance `hcomm'` for `(1 − π)_{K̄}`, fully discharged (CoordHom-free).**
The `hcomm'` field of `OneSubScalingData`, with **no** carried `hgcomm` hypothesis: the canonical
generic-point covariance is supplied by Wall A (`mapTranslateGenericPoint_oneSub_canonical`), and
`oneSub_hcommPrime_of_hgcomm` (`SeparableWitnesses.lean`) turns it into the per-`(ℓ, S, T)`
covariance at `z = weilFunction …`.  This is Silverman III.8.2 for the base-changed separable
`1 − π`, realized purely from the function-field base-change naturality. -/
theorem oneSub_hcommPrime_discharged (hq : 2 ≤ Fintype.card K) :
    ∀ (ℓ : ℕ) (hℓF : (ℓ : AlgebraicClosure K) ≠ 0)
      (S T : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
      (_hS : ((ℓ : ℕ) : ℤ) • S = 0)
      (hφT : ((ℓ : ℕ) : ℤ) •
        (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
          (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom T = 0),
      translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S
          ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
            (weilFunction (W.baseChange (AlgebraicClosure K)) ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
              ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
                (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom T) hφT)) =
        (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
          (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
          (translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
            ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
              (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom S)
            (weilFunction (W.baseChange (AlgebraicClosure K)) ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
              ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
                (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom T) hφT)) :=
  oneSub_hcommPrime_of_hgcomm W p r hq (mapTranslateGenericPoint_oneSub_canonical W p r hq)

end

end HasseWeil.WeilPairing

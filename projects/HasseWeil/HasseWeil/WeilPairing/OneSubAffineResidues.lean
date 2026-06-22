/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.OneSubComapConcrete
import HasseWeil.WeilPairing.WallAGenericRealization
import HasseWeil.WeilPairing.OneSubWitnesses

/-!
# Discharging the closed-point residues of the concrete `(1 − π)_{K̄}` (CoordHom-free, axiom-clean)

This file discharges the closed-point generator residues of the concrete base-changed `1 − π`
(`OneSubComapConcrete.lean`), the input the affine comap identity rests on, via the
base-change-naturality plan, and assembles the affine comap-valuation identity for the
**non-doubling, non-2-torsion-image** case with `e = 1` *derived* (no carried
`OneSubAffineResidues`).

## The base-changed `−π` summand with an explicit pullback

The concrete pullback `(1 − π)_{K̄}^*` is opaque (the conjugate-by-`Φ` base change), and the
base-changed Frobenius isogeny `frobeniusIsog_baseChange_charP_pow` has an *opaque* pullback
(a `cast` of an iterated relative Frobenius). The decisive move is to build a **bespoke** `−π`
summand `α₂ = negFrobBaseChange` over `K̄` whose pullback is the *transparent* function-field
base change `baseChangePullback (negFrobeniusIsog W).pullback` and whose point map is `−π̄ =
−frobeniusHomBaseChange`. Its pullback is then computed *explicitly* via the WallA naturality
`baseChangePullback_functionFieldMap`:

  `α₂^* x_gen = (x_gen)^q`,  `α₂^* y_gen = −(y_gen)^q − a₁(x_gen)^q − a₃`.

## The pullback decomposition and the residues

The concrete pullback decomposes on the generators as `(1 − π)^* x_gen = addPullback_x_pair (id) α₂`
(`oneSub_pullback_x_gen_eq_addPullback_x_pair`), via the WallA realisation
`oneSubFrobeniusPullback_L_x_gen`, the `K`-level `oneSub_pullback_x_gen_eq`, and the **base-change
naturality of `addPullback_x_pair`** (`addPullback_x_pair_id_negFrobBaseChange`, built from
mathlib's `map_addX`/`map_addY`/`map_slope` plus the curve-base-change equality
`W_KE_map_functionFieldMap`).

Feeding the per-summand point images (`id(P) = P`, `α₂(P) = −π̄(P) = some (P.x^q) (negY (P.x^q)
(P.y^q))`) and closed-point residues through the general `isog_coords_at_affine_of_decomp`
(`AdditionPullback/SamePlace.lean`) gives the two generator residues `(1 − π)^* x_gen ≡ x`,
`(1 − π)^* y_gen ≡ y` at every smooth point `P` whose image is the **finite, non-doubling** point
`(1 − π)P = some x y` (the secant branch `P.x ≠ P.x^q`) — `oneSub_two_residues_nondoubling`.

## The non-2-torsion unit and the affine comap

From the two residues, the pulled-back differential denominator
`alpha_star_u (1 − π) = (1 − π)^* u_gen` residues to `2y + a₁x + a₃`, hence is a *unit* at `P` when
the image is non-2-torsion (`oneSub_alpha_star_u_ord_eq_zero`).  Combining the two residues + this
unit through the general headline `comap_pointValuation_isog_eq_affine` (with `e = 1` derived from
the invariant differential) gives the affine comap identity
`comap_pointValuation_oneSub_eq_affine_nondoubling`, axiom-clean and **without any carried
`OneSubAffineResidues`** — the `hcoeff_mem` (constancy of the omega coefficient)
is the only carried named hypothesis (its base-change *value* transport is not available; only the
`≠ 0` transport `OmegaBaseChangeNeZero` is).

## Scope (honest)

This covers the **non-doubling** (`P.x ≠ P.x^q`), **non-2-torsion-image** (`2y + a₁x + a₃ ≠ 0`)
case — the secant branch, matching the scope of the general non-2-torsion headline
`comap_pointValuation_isog_eq_affine`.  The doubling case (`P.x ∈ 𝔽_q`, where `(1 − π)P = 2P` and
the secant degenerates to the tangent) and the 2-torsion-image case (ramification `e ≤ 2` via the
`y`-uniformizer, `DifferentialOrd.ord_P_mulByInt_y_sub_const_le_one`-style) are *not* covered here;
they are separate geometric sub-cases.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, I.2 (base change), III.4 (Frobenius),
II.2.5–2.6, III.4.10c, III.5.5.
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

noncomputable local instance instDecEqACOSAR : DecidableEq (AlgebraicClosure K) := Classical.decEq _

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]

/-- **The base-changed `−π` summand isogeny** `α₂ = negFrobBaseChange` over `K̄`.  Its pullback is the
honest function-field base change `baseChangePullback (negFrobeniusIsog W).pullback` (the same
conjugate-by-`Φ` construction as `oneSubFrobeniusPullback_L`), and its point map is `−π̄ =
−frobeniusHomBaseChange` (the negation of the `q`-power Frobenius point map).  This realizes the
second summand of the decomposition `1 − π = id + (−π)` over `K̄` with a *transparently-computable*
pullback (unlike the opaque base-changed Frobenius isogeny `frobeniusIsog_baseChange_charP_pow`). -/
noncomputable def negFrobBaseChange :
    HasseWeil.Isogeny (W.baseChange (AlgebraicClosure K)).toAffine
      (W.baseChange (AlgebraicClosure K)).toAffine :=
  Isogeny.mkBaseChange (AlgebraicClosure K)
    (baseChangePullback (⟨W.toAffine⟩ : SmoothPlaneCurve K) (AlgebraicClosure K)
      (HasseWeil.negFrobeniusIsog W).pullback)
    (-frobeniusHomBaseChange W p r (AlgebraicClosure K))

@[simp] theorem negFrobBaseChange_pullback :
    (negFrobBaseChange W p r).pullback =
      baseChangePullback (⟨W.toAffine⟩ : SmoothPlaneCurve K) (AlgebraicClosure K)
        (HasseWeil.negFrobeniusIsog W).pullback :=
  Isogeny.mkBaseChange_pullback _ _ _

@[simp] theorem negFrobBaseChange_toAddMonoidHom :
    (negFrobBaseChange W p r).toAddMonoidHom =
      -frobeniusHomBaseChange W p r (AlgebraicClosure K) :=
  Isogeny.mkBaseChange_toAddMonoidHom _ _ _

/-- `α₂^* (functionFieldMap z) = functionFieldMap (negFrob^* z)` — the WallA naturality at the
`negFrobBaseChange` pullback (the conjugate intertwines `(negFrob).pullback` with `functionFieldMap`),
exactly `baseChangePullback_functionFieldMap` at this pullback. -/
theorem negFrobBaseChange_pullback_functionFieldMap (z : W.toAffine.FunctionField) :
    (negFrobBaseChange W p r).pullback
        ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K) z) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        ((HasseWeil.negFrobeniusIsog W).pullback z) := by
  rw [negFrobBaseChange_pullback]
  exact IsogenyBaseChangeConcrete.baseChangePullback_functionFieldMap
    (⟨W.toAffine⟩ : SmoothPlaneCurve K) (AlgebraicClosure K)
    (HasseWeil.negFrobeniusIsog W).pullback z

theorem negFrobBaseChange_pullback_x_gen :
    (negFrobBaseChange W p r).pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) =
      HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)) ^ Fintype.card K := by
  have hffx : (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
      (HasseWeil.x_gen W) = HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)) :=
    IsogenyBaseChangeConcrete.functionFieldMap_x_gen W (AlgebraicClosure K)
  have hstep : (negFrobBaseChange W p r).pullback
        ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
          (HasseWeil.x_gen W)) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        (HasseWeil.x_gen W ^ Fintype.card K) := by
    rw [negFrobBaseChange_pullback_functionFieldMap, HasseWeil.negFrobeniusIsog_pullback_x_gen,
      HasseWeil.frobeniusIsog_pullback_apply]
  conv_lhs => rw [← hffx, hstep, map_pow]
  congr 1

/-- **`α₂^* y_gen = −(y_gen)^q − a₁(x_gen)^q − a₃`** over `K̄`.  The `y`-analogue of
`negFrobBaseChange_pullback_x_gen`, via `negFrobeniusIsog_pullback_y_gen` (whose RHS is
`−π^* y − a₁·π^* x − a₃` with `π^* ?_gen = (?_gen)^q`), `functionFieldMap` distributing over
`−, ·, +` and fixing `algebraMap K` (`functionFieldMap_algebraMap` on the base-field coefficients),
`functionFieldMap (a_i) = algebraMap K̄ a_i` (the base curve coefficients base-change). -/
theorem negFrobBaseChange_pullback_y_gen :
    (negFrobBaseChange W p r).pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) =
      -(HasseWeil.y_gen (W.baseChange (AlgebraicClosure K)) ^ Fintype.card K) -
        algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
          (W.baseChange (AlgebraicClosure K)).a₁ *
          HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)) ^ Fintype.card K -
        algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
          (W.baseChange (AlgebraicClosure K)).a₃ := by
  have hffx : (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
      (HasseWeil.x_gen W) = HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)) :=
    IsogenyBaseChangeConcrete.functionFieldMap_x_gen W (AlgebraicClosure K)
  have hffy : (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
      (HasseWeil.y_gen W) = HasseWeil.y_gen (W.baseChange (AlgebraicClosure K)) :=
    IsogenyBaseChangeConcrete.functionFieldMap_y_gen W (AlgebraicClosure K)
  have hc₁ : (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₁) =
      algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
        (W.baseChange (AlgebraicClosure K)).a₁ := by
    rw [SmoothPlaneCurve.functionFieldMap_algebraMap_F (⟨W.toAffine⟩ : SmoothPlaneCurve K)
      (AlgebraicClosure K) W.toAffine.a₁]
    exact (IsScalarTower.algebraMap_apply K (AlgebraicClosure K)
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField W.toAffine.a₁).symm
  have hc₃ : (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₃) =
      algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
        (W.baseChange (AlgebraicClosure K)).a₃ := by
    rw [SmoothPlaneCurve.functionFieldMap_algebraMap_F (⟨W.toAffine⟩ : SmoothPlaneCurve K)
      (AlgebraicClosure K) W.toAffine.a₃]
    exact (IsScalarTower.algebraMap_apply K (AlgebraicClosure K)
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField W.toAffine.a₃).symm
  have hstep : (negFrobBaseChange W p r).pullback
        ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
          (HasseWeil.y_gen W)) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        (-(HasseWeil.y_gen W ^ Fintype.card K) -
          algebraMap K W.toAffine.FunctionField W.toAffine.a₁ * HasseWeil.x_gen W ^ Fintype.card K -
          algebraMap K W.toAffine.FunctionField W.toAffine.a₃) := by
    rw [negFrobBaseChange_pullback_functionFieldMap, HasseWeil.negFrobeniusIsog_pullback_y_gen,
      HasseWeil.frobeniusIsog_pullback_apply, HasseWeil.frobeniusIsog_pullback_apply]
  conv_lhs => rw [← hffy, hstep, map_sub, map_sub, map_neg, map_mul, map_pow, map_pow,
    hffx, hffy, hc₁, hc₃]
  rfl

/-- **`(W_KE W).map functionFieldMap = W_KE (W.baseChange K̄)`** — the curve over `K(E)` base-changes,
along the function-field inclusion `functionFieldMap`, to the curve over `K̄(E)`.  Both are `W`
base-changed to the respective function field; the ring homs `functionFieldMap ∘ algebraMap K K(E)`
and `algebraMap K K̄(E)` agree (`functionFieldMap_algebraMap_F`), so `WeierstrassCurve.map_baseChange`
identifies them. -/
theorem W_KE_map_functionFieldMap :
    (W_KE W).map ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)) =
      W_KE (W.baseChange (AlgebraicClosure K)) := by
  have key : ∀ a : K, (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        (algebraMap K W.toAffine.FunctionField a) =
      algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
        (algebraMap K (AlgebraicClosure K) a) := fun a ↦ by
    rw [SmoothPlaneCurve.functionFieldMap_algebraMap_F,
      ← IsScalarTower.algebraMap_apply K (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField]
    rfl
  apply WeierstrassCurve.ext <;>
    simp only [WeierstrassCurve.map, W_KE, WeierstrassCurve.baseChange] <;>
    exact key _

/-- **`addSlopePair (id) α₂ = functionFieldMap (addSlopePair^K (id) negFrob)`** over `K̄`.  The
addition-formula slope of the base-changed pair is the function-field base change of the `K`-level
slope, via mathlib's `map_slope` (the slope is natural under a ring hom) + the curve equality
`W_KE_map_functionFieldMap` + the generator/`negFrob`-pullback naturalities. -/
theorem addSlopePair_id_negFrobBaseChange :
    addSlopePair (Isogeny.id (W.baseChange (AlgebraicClosure K)).toAffine)
        (negFrobBaseChange W p r) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        (addSlopePair (Isogeny.id W.toAffine) (HasseWeil.negFrobeniusIsog W)) := by
  rw [addSlopePair, addSlopePair]
  rw [show (Isogeny.id (W.baseChange (AlgebraicClosure K)).toAffine).pullback
        (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) =
      HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)) from rfl,
    show (Isogeny.id (W.baseChange (AlgebraicClosure K)).toAffine).pullback
        (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) =
      HasseWeil.y_gen (W.baseChange (AlgebraicClosure K)) from rfl,
    show (Isogeny.id W.toAffine).pullback (HasseWeil.x_gen W) = HasseWeil.x_gen W from rfl,
    show (Isogeny.id W.toAffine).pullback (HasseWeil.y_gen W) = HasseWeil.y_gen W from rfl]
  rw [← IsogenyBaseChangeConcrete.functionFieldMap_x_gen W (AlgebraicClosure K),
    ← IsogenyBaseChangeConcrete.functionFieldMap_y_gen W (AlgebraicClosure K),
    negFrobBaseChange_pullback_functionFieldMap W p r (HasseWeil.x_gen W),
    negFrobBaseChange_pullback_functionFieldMap W p r (HasseWeil.y_gen W)]
  rw [← W_KE_map_functionFieldMap W]
  exact WeierstrassCurve.Affine.map_slope (W := W_KE W)
    ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K))
    (HasseWeil.x_gen W) ((HasseWeil.negFrobeniusIsog W).pullback (HasseWeil.x_gen W))
    (HasseWeil.y_gen W) ((HasseWeil.negFrobeniusIsog W).pullback (HasseWeil.y_gen W))

/-- **`addPullback_x_pair (id) α₂ = functionFieldMap (addPullback_x_pair^K (id) negFrob)`** over `K̄`.
Via mathlib's `map_addX` (the `x`-addition coordinate is natural under a ring hom), the curve equality
`W_KE_map_functionFieldMap`, the slope naturality `addSlopePair_id_negFrobBaseChange`, and the
generator/`negFrob`-pullback naturalities. -/
theorem addPullback_x_pair_id_negFrobBaseChange :
    addPullback_x_pair (Isogeny.id (W.baseChange (AlgebraicClosure K)).toAffine)
        (negFrobBaseChange W p r) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        (addPullback_x_pair (Isogeny.id W.toAffine) (HasseWeil.negFrobeniusIsog W)) := by
  rw [addPullback_x_pair, addPullback_x_pair, addSlopePair_id_negFrobBaseChange,
    show (Isogeny.id (W.baseChange (AlgebraicClosure K)).toAffine).pullback
        (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) =
      HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)) from rfl,
    show (Isogeny.id W.toAffine).pullback (HasseWeil.x_gen W) = HasseWeil.x_gen W from rfl,
    ← IsogenyBaseChangeConcrete.functionFieldMap_x_gen W (AlgebraicClosure K),
    negFrobBaseChange_pullback_functionFieldMap W p r (HasseWeil.x_gen W),
    ← W_KE_map_functionFieldMap W]
  exact WeierstrassCurve.Affine.map_addX (W' := W_KE W)
    ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K))
    (HasseWeil.x_gen W) ((HasseWeil.negFrobeniusIsog W).pullback (HasseWeil.x_gen W))
    (addSlopePair (Isogeny.id W.toAffine) (HasseWeil.negFrobeniusIsog W))

/-- **`addPullback_y_pair (id) α₂ = functionFieldMap (addPullback_y_pair^K (id) negFrob)`** over `K̄`.
The `y`-analogue of `addPullback_x_pair_id_negFrobBaseChange`, via `map_addY`. -/
theorem addPullback_y_pair_id_negFrobBaseChange :
    addPullback_y_pair (Isogeny.id (W.baseChange (AlgebraicClosure K)).toAffine)
        (negFrobBaseChange W p r) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        (addPullback_y_pair (Isogeny.id W.toAffine) (HasseWeil.negFrobeniusIsog W)) := by
  rw [addPullback_y_pair, addPullback_y_pair, addSlopePair_id_negFrobBaseChange,
    show (Isogeny.id (W.baseChange (AlgebraicClosure K)).toAffine).pullback
        (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) =
      HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)) from rfl,
    show (Isogeny.id (W.baseChange (AlgebraicClosure K)).toAffine).pullback
        (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) =
      HasseWeil.y_gen (W.baseChange (AlgebraicClosure K)) from rfl,
    show (Isogeny.id W.toAffine).pullback (HasseWeil.x_gen W) = HasseWeil.x_gen W from rfl,
    show (Isogeny.id W.toAffine).pullback (HasseWeil.y_gen W) = HasseWeil.y_gen W from rfl,
    ← IsogenyBaseChangeConcrete.functionFieldMap_x_gen W (AlgebraicClosure K),
    ← IsogenyBaseChangeConcrete.functionFieldMap_y_gen W (AlgebraicClosure K),
    negFrobBaseChange_pullback_functionFieldMap W p r (HasseWeil.x_gen W),
    ← W_KE_map_functionFieldMap W]
  exact WeierstrassCurve.Affine.map_addY (W' := W_KE W)
    (f := (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K))
    (x₁ := HasseWeil.x_gen W) (x₂ := (HasseWeil.negFrobeniusIsog W).pullback (HasseWeil.x_gen W))
    (y₁ := HasseWeil.y_gen W)
    (ℓ := addSlopePair (Isogeny.id W.toAffine) (HasseWeil.negFrobeniusIsog W))

variable [Fintype W.toAffine.Point]

/-- **The `x`-generator pullback decomposition for `(1 − π)_{K̄}`**:
`(1 − π)^* x_gen = addPullback_x_pair (id) α₂` over `K̄`, the `hpb_x` input of
`isog_coords_at_affine_of_decomp`.  Chains the WallA realisation
`oneSubFrobeniusPullback_L_x_gen` (`(1 − π)^* x_gen^{K̄} = functionFieldMap((1 − π)^K.pullback x_gen^K)`),
the `K`-level `oneSub_pullback_x_gen_eq` (`= addPullback_x^K(negFrob) = addPullback_x_pair^K(id, negFrob)`),
and the base-change naturality `addPullback_x_pair_id_negFrobBaseChange`. -/
theorem oneSub_pullback_x_gen_eq_addPullback_x_pair (hq : 2 ≤ Fintype.card K) :
    (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
        (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) =
      addPullback_x_pair (Isogeny.id (W.baseChange (AlgebraicClosure K)).toAffine)
        (negFrobBaseChange W p r) := by
  rw [oneSubFrobeniusIsogBaseChange_pullback,
    IsogenyBaseChangeConcrete.oneSubFrobeniusPullback_L_x_gen W (AlgebraicClosure K) hq,
    oneSub_pullback_x_gen_eq W hq, ← addPullback_x_pair_id (HasseWeil.negFrobeniusIsog W),
    ← addPullback_x_pair_id_negFrobBaseChange W p r]

/-- **The `y`-generator pullback decomposition for `(1 − π)_{K̄}`**:
`(1 − π)^* y_gen = addPullback_y_pair (id) α₂` over `K̄`.  The `y`-analogue of
`oneSub_pullback_x_gen_eq_addPullback_x_pair`. -/
theorem oneSub_pullback_y_gen_eq_addPullback_y_pair (hq : 2 ≤ Fintype.card K) :
    (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
        (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) =
      addPullback_y_pair (Isogeny.id (W.baseChange (AlgebraicClosure K)).toAffine)
        (negFrobBaseChange W p r) := by
  rw [oneSubFrobeniusIsogBaseChange_pullback,
    IsogenyBaseChangeConcrete.oneSubFrobeniusPullback_L_y_gen W (AlgebraicClosure K) hq,
    oneSub_pullback_y_gen_eq W hq, ← addPullback_y_pair_id (HasseWeil.negFrobeniusIsog W),
    ← addPullback_y_pair_id_negFrobBaseChange W p r]

/-- `resid`-form: `x_gen^{K̄} ≡ P.x` modulo `m_P` (the generic `x`-coordinate residues to `P.x`).
Public re-derivation of `SamePlace.resid_x_gen`. -/
theorem residPV_x_gen (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)) -
      algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
        P.x) < 1 := by
  rw [HasseWeil.x_gen_sub_const_eq_algebraMap_XClass]
  exact (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
    (C := (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K))) _ P).mpr (HasseWeil.XClass_mem_maximalIdealAt _ P P.x rfl)

/-- A residue `u ≡ a` makes `u` regular at `P` (`pV P u ≤ 1`). -/
theorem residPV_le_one {P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint}
    {u : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField} {a : AlgebraicClosure K}
    (h : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P (u - algebraMap (AlgebraicClosure K)
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) < 1) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P u ≤ 1 := by
  rw [show u = (u - algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) +
      algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a
    by ring]
  exact pointValuation_add_le_one (W.baseChange (AlgebraicClosure K)) P (le_of_lt h)
    ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation_algebraMap_F_le_one P a)

/-- Residues multiply: `u ≡ a`, `v ≡ b` ⟹ `u·v ≡ a·b`. -/
theorem residPV_mul {P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint}
    {u v : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField} {a b : AlgebraicClosure K}
    (hu : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P (u - algebraMap (AlgebraicClosure K)
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) < 1)
    (hv : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P (v - algebraMap (AlgebraicClosure K)
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField b) < 1) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P (u * v - algebraMap (AlgebraicClosure K)
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (a * b)) < 1 := by
  have hu_le := residPV_le_one W hu
  rw [show u * v - algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (a * b) =
      u * (v - algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField b) +
      algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField b *
        (u - algebraMap (AlgebraicClosure K)
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) by rw [map_mul]; ring]
  refine lt_of_le_of_lt (((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P).map_add _ _) (max_lt ?_ ?_)
  · exact pointValuation_mul_lt_one_of_le_and_lt (W.baseChange (AlgebraicClosure K)) P hu_le hv
  · exact pointValuation_mul_lt_one_of_le_and_lt (W.baseChange (AlgebraicClosure K)) P
      ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation_algebraMap_F_le_one P b) hu

/-- Residues raise to a power: `u ≡ a` ⟹ `u^n ≡ a^n`. -/
theorem residPV_pow {P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint}
    {u : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField} {a : AlgebraicClosure K}
    (hu : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P (u - algebraMap (AlgebraicClosure K)
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) < 1) (n : ℕ) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P (u ^ n - algebraMap (AlgebraicClosure K)
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (a ^ n)) < 1 := by
  induction n with
  | zero =>
    simp only [pow_zero, map_one, sub_self, map_zero]
    exact zero_lt_one
  | succ k ih => rw [pow_succ, pow_succ]; exact residPV_mul W ih hu

/-- A scalar `algebraMap c` residues to `c`. -/
theorem residPV_const (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) (c : AlgebraicClosure K) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      (algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField c -
        algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField c) < 1 := by
  rw [sub_self, map_zero]; exact zero_lt_one

/-- Residues subtract: `u ≡ a`, `v ≡ b` ⟹ `u − v ≡ a − b`. -/
theorem residPV_sub {P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint}
    {u v : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField} {a b : AlgebraicClosure K}
    (hu : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      (u - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) < 1)
    (hv : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      (v - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField b) < 1) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      (u - v - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (a - b)) < 1 := by
  have heq : u - v - algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (a - b) =
      (u - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) -
      (v - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField b) := by
    rw [map_sub]; abel
  rw [heq]
  exact lt_of_le_of_lt
    (((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P).map_sub _ _)
    (max_lt hu hv)

/-- Residues add: `u ≡ a`, `v ≡ b` ⟹ `u + v ≡ a + b`. -/
theorem residPV_add {P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint}
    {u v : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField} {a b : AlgebraicClosure K}
    (hu : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      (u - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) < 1)
    (hv : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      (v - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField b) < 1) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      (u + v - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (a + b)) < 1 := by
  have heq : u + v - algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (a + b) =
      (u - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) +
      (v - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField b) := by
    rw [map_add]; abel
  rw [heq]
  exact lt_of_le_of_lt
    (((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P).map_add _ _)
    (max_lt hu hv)

/-- Residues negate: `u ≡ a` ⟹ `−u ≡ −a`. -/
theorem residPV_neg {P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint}
    {u : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField} {a : AlgebraicClosure K}
    (hu : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      (u - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) < 1) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      (-u - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (-a)) < 1 := by
  have h0 : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      ((0 : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) -
        algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField 0) < 1 := by
    have : (0 : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) -
        algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField 0 = 0 := by
      rw [_root_.map_zero, sub_self]
    rw [this, Valuation.map_zero]
    exact zero_lt_one
  have := residPV_sub W h0 hu
  rwa [zero_sub, zero_sub] at this

/-- **`π̄` on a finite point** `some x y`: `frobeniusHomBaseChange (some x y) =
some (frobeniusAlgHom x) (frobeniusAlgHom y) _` (`= some (x^q) (y^q)` since `frobeniusAlgHom = (·^q)`),
with the nonsingularity proof carried by `geomFrobeniusPointFun_some`.  Via the linchpin
`frobeniusHomBaseChange = geomFrobeniusPoint`. -/
theorem frobeniusHomBaseChange_apply_some {x y : AlgebraicClosure K}
    (h : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular x y) :
    frobeniusHomBaseChange W p r (AlgebraicClosure K) (Affine.Point.some x y h) =
      Affine.Point.some
        ((FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) x)
        ((FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) y)
        ((WeierstrassCurve.Affine.baseChange_nonsingular W.toAffine
          (RingHom.injective
            (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)).toRingHom) x y).mpr h) := by
  rw [frobeniusHomBaseChange_eq_geomFrobeniusPoint, geomFrobeniusPoint_apply,
    geomFrobeniusPointFun_some]

/-- **`α₂` on a finite point** `some x y`: `α₂(some x y) = some (x^q) (negY (x^q) (y^q)) _`, the
negation of the geometric `q`-power Frobenius image (`−π̄`).  From
`negFrobBaseChange_toAddMonoidHom` (point map `= −frobeniusHomBaseChange`),
`frobeniusHomBaseChange_apply_some`, and `Affine.Point.neg_some`. -/
theorem negFrobBaseChange_apply_some {x y : AlgebraicClosure K}
    (h : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular x y) :
    (negFrobBaseChange W p r).toAddMonoidHom (Affine.Point.some x y h) =
      Affine.Point.some ((FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) x)
        ((W.baseChange (AlgebraicClosure K)).toAffine.negY
          ((FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) x)
          ((FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) y))
        ((WeierstrassCurve.Affine.nonsingular_neg
          (W' := (W.baseChange (AlgebraicClosure K)).toAffine) _ _).mpr
          ((WeierstrassCurve.Affine.baseChange_nonsingular W.toAffine
            (RingHom.injective
              (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)).toRingHom) x y).mpr h)) := by
  rw [negFrobBaseChange_toAddMonoidHom, AddMonoidHom.neg_apply,
    frobeniusHomBaseChange_apply_some, WeierstrassCurve.Affine.Point.neg_some]

/-- **The two generator residues for `(1 − π)_{K̄}` at a non-doubling affine image** (CoordHom-free).
For a smooth point `P` of `E_{K̄}` whose image `(1 − π)P = some x y` is finite and *non-doubling*
(`P.x ≠ P.x^q`), the two generator residues hold:

  `(1 − π)^* x_gen ≡ x`  and  `(1 − π)^* y_gen ≡ y`  (modulo `m_P`).

Via the general `isog_coords_at_affine_of_decomp` with `α₁ = id`, `α₂ = negFrobBaseChange` (the `−π`
summand), supplying the pullback decomposition `(1 − π)^* = addPullback_x_pair (id) α₂`
(`oneSub_pullback_x_gen_eq_addPullback_x_pair`), the per-summand point images and residues, and the
non-doubling `hx_ne`.  The non-doubling case is exactly the secant branch of the addition formula. -/
theorem oneSub_two_residues_nondoubling (hq : 2 ≤ Fintype.card K)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x y : AlgebraicClosure K}
    (h_ns : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular x y)
    (hx_ne : P.x ≠ (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) P.x)
    (hQ : (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom P.toAffinePoint =
        Affine.Point.some x y h_ns) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
            (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x) < 1 ∧
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
            (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y) < 1 := by
  set L := AlgebraicClosure K
  set α := oneSubFrobeniusIsogBaseChange W p r L (oneSubFrobeniusPullback_L W L hq) with hα
  have hα₁ : (Isogeny.id (W.baseChange L).toAffine).toAddMonoidHom P.toAffinePoint =
      Affine.Point.some P.x P.y P.nonsingular := rfl
  have hα₂ : (negFrobBaseChange W p r).toAddMonoidHom P.toAffinePoint =
      Affine.Point.some ((FiniteField.frobeniusAlgHom K L) P.x)
        ((W.baseChange L).toAffine.negY ((FiniteField.frobeniusAlgHom K L) P.x)
          ((FiniteField.frobeniusAlgHom K L) P.y)) _ :=
    negFrobBaseChange_apply_some W p r P.nonsingular
  have hsum_pt : α.toAddMonoidHom P.toAffinePoint =
      (Isogeny.id (W.baseChange L).toAffine).toAddMonoidHom P.toAffinePoint +
        (negFrobBaseChange W p r).toAddMonoidHom P.toAffinePoint := by
    rw [hα, oneSubFrobeniusIsogBaseChange_toAddMonoidHom, negFrobBaseChange_toAddMonoidHom,
      AddMonoidHom.sub_apply, AddMonoidHom.neg_apply, sub_eq_add_neg]
    rfl
  rw [hα₁, hα₂] at hsum_pt
  have hx₁ : (⟨(W.baseChange L).toAffine⟩ : SmoothPlaneCurve L).pointValuation P
      ((Isogeny.id (W.baseChange L).toAffine).pullback (HasseWeil.x_gen (W.baseChange L)) -
        algebraMap L (W.baseChange L).toAffine.FunctionField P.x) < 1 := residPV_x_gen W P
  have hy₁ : (⟨(W.baseChange L).toAffine⟩ : SmoothPlaneCurve L).pointValuation P
      ((Isogeny.id (W.baseChange L).toAffine).pullback (HasseWeil.y_gen (W.baseChange L)) -
        algebraMap L (W.baseChange L).toAffine.FunctionField P.y) < 1 :=
    pointValuation_y_gen_sub_const_lt_one_at_smoothPoint (W.baseChange L) P P.y rfl
  have hx₂ : (⟨(W.baseChange L).toAffine⟩ : SmoothPlaneCurve L).pointValuation P
      ((negFrobBaseChange W p r).pullback (HasseWeil.x_gen (W.baseChange L)) -
        algebraMap L (W.baseChange L).toAffine.FunctionField
          ((FiniteField.frobeniusAlgHom K L) P.x)) < 1 := by
    rw [negFrobBaseChange_pullback_x_gen, FiniteField.coe_frobeniusAlgHom]
    exact residPV_pow W (residPV_x_gen W P) (Fintype.card K)
  have hy₂ : (⟨(W.baseChange L).toAffine⟩ : SmoothPlaneCurve L).pointValuation P
      ((negFrobBaseChange W p r).pullback (HasseWeil.y_gen (W.baseChange L)) -
        algebraMap L (W.baseChange L).toAffine.FunctionField
          ((W.baseChange L).toAffine.negY ((FiniteField.frobeniusAlgHom K L) P.x)
            ((FiniteField.frobeniusAlgHom K L) P.y))) < 1 := by
    rw [negFrobBaseChange_pullback_y_gen]
    rw [show (W.baseChange L).toAffine.negY ((FiniteField.frobeniusAlgHom K L) P.x)
          ((FiniteField.frobeniusAlgHom K L) P.y) =
        -(P.y ^ Fintype.card K) - (W.baseChange L).a₁ * P.x ^ Fintype.card K - (W.baseChange L).a₃
      by simp only [WeierstrassCurve.Affine.negY, FiniteField.coe_frobeniusAlgHom]]
    have r_yq := residPV_pow W
      (pointValuation_y_gen_sub_const_lt_one_at_smoothPoint (W.baseChange L) P P.y rfl) (Fintype.card K)
    have r_xq := residPV_pow W (residPV_x_gen W P) (Fintype.card K)
    have r_a1 := residPV_const W P (W.baseChange L).a₁
    have r_a3 := residPV_const W P (W.baseChange L).a₃
    have r_step := residPV_sub W (residPV_sub W (residPV_neg W r_yq) (residPV_mul W r_a1 r_xq)) r_a3
    convert r_step using 2
  exact isog_coords_at_affine_of_decomp (W := W.baseChange L)
    (α := α) (α₁ := Isogeny.id (W.baseChange L).toAffine) (α₂ := negFrobBaseChange W p r)
    (oneSub_pullback_x_gen_eq_addPullback_x_pair W p r hq)
    (oneSub_pullback_y_gen_eq_addPullback_y_pair W p r hq)
    P h_ns hα₁ hα₂ hx₁ hx₂ hy₁ hy₂ hx_ne hsum_pt hQ

/-- A residue `u ≡ a` with `a ≠ 0` makes `u` a unit at `P` (`pV P u = 1`). -/
theorem residPV_unit {P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint}
    {u : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField} {a : AlgebraicClosure K}
    (h : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      (u - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) < 1)
    (ha : a ≠ 0) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P u = 1 := by
  have hconst : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      (algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) = 1 :=
    pointValuation_algebraMap_F_eq_one_of_ne_zero (W.baseChange (AlgebraicClosure K)) P ha
  rw [show u = (u - algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) +
      algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a by abel,
    ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P).map_add_eq_of_lt_right
      (by rw [hconst]; exact h), hconst]

/-- **Frobenius acts as `−1` on a doubling point with affine `(1 − π)`-image.**  For `P.x = P.x^q` and
`(1 − π)P = some x y` affine, `π̄(P) = some (P.x^q) (P.y^q)` satisfies `P.y^q = negY(P.x, P.y)` (so
`π̄(P) = −P`), and `P` is non-2-torsion (`P.y ≠ P.y^q`). -/
theorem oneSub_frob_eq_neg_at_doubling (hq : 2 ≤ Fintype.card K)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x y : AlgebraicClosure K}
    (h_ns : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular x y)
    (hx_eq : P.x = (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) P.x)
    (hQ : (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom P.toAffinePoint =
        Affine.Point.some x y h_ns) :
    (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) P.y =
        (W.baseChange (AlgebraicClosure K)).toAffine.negY P.x P.y ∧
      P.y ≠ (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) P.y := by
  have hfx : (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) P.x = P.x := hx_eq.symm
  have hα₂ := negFrobBaseChange_apply_some W p r P.nonsingular
  have hπ_ns : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular
      ((FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) P.x)
      ((FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) P.y) :=
    (WeierstrassCurve.Affine.baseChange_nonsingular W.toAffine
      (RingHom.injective (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)).toRingHom) P.x P.y).mpr
      P.nonsingular
  have hP_eqn : (W.baseChange (AlgebraicClosure K)).toAffine.Equation P.x P.y := P.nonsingular.left
  have hπ_eqn : (W.baseChange (AlgebraicClosure K)).toAffine.Equation P.x
      ((FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) P.y) := hfx ▸ hπ_ns.left
  -- `Y_eq_of_X_eq`: either `P.y = frob P.y` (case 1) or `P.y = negY(P.x, frob P.y)` (case 2).
  have hcases := WeierstrassCurve.Affine.Y_eq_of_X_eq
    (W := (W.baseChange (AlgebraicClosure K)).toAffine) hP_eqn hπ_eqn rfl
  have hsum : (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom P.toAffinePoint =
      P.toAffinePoint + (negFrobBaseChange W p r).toAddMonoidHom P.toAffinePoint := by
    rw [oneSubFrobeniusIsogBaseChange_toAddMonoidHom, negFrobBaseChange_toAddMonoidHom,
      AddMonoidHom.sub_apply, AddMonoidHom.neg_apply, sub_eq_add_neg]
    rfl
  -- case 1 `P.y = frob P.y` would give `(1 − π)P = P + (−P) = O`, contradicting the affine image.
  have hne1 : P.y ≠ (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) P.y := by
    intro hy_eq
    have hnegP : (negFrobBaseChange W p r).toAddMonoidHom P.toAffinePoint = -P.toAffinePoint := by
      rw [SmoothPlaneCurve.SmoothPoint.toAffinePoint_def, hα₂,
        WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hfx, by rw [hfx, ← hy_eq]⟩
    rw [hnegP, add_neg_cancel] at hsum
    rw [hsum] at hQ
    exact (WeierstrassCurve.Affine.Point.some_ne_zero h_ns) hQ.symm
  have hcase2 : P.y = (W.baseChange (AlgebraicClosure K)).toAffine.negY P.x
      ((FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) P.y) := hcases.resolve_left hne1
  refine ⟨?_, hne1⟩
  have h := congrArg ((W.baseChange (AlgebraicClosure K)).toAffine.negY P.x) hcase2
  rw [WeierstrassCurve.Affine.negY_negY] at h
  exact h.symm

set_option maxHeartbeats 5000000 in
-- The invariant-differential `L'Hôpital` proof elaborates the deeply-nested base-changed
-- `FunctionField` type through `set Wb/C/f/g/φ` + `Dω`/`addSlopePair` unfoldings; the resulting
-- `whnf` defeq cost exceeds the default budget. Decomposing the `Dω`/residue sub-blocks into
-- standalone lemmas (`/decompose-proof`) is the proper fix; until then the budget is raised.
/-- **The doubling slope residue `addSlopePair (id, −π) ≡ ν(P)/u(P)`** (the tangent / `L'Hôpital`
step).  In the doubling case `P.x = P.x^q`, the `K(E)`-element `addSlopePair (id) (−π)` is the *secant*
`(y_gen − (−π)^*y_gen)/(x_gen − x_gen^q)` (the pullbacks are distinct in `K(E)`), but it residues at
`P` to the *tangent* slope `λ = ν(P)/u(P)`, where `ν(P) = 3P.x²+2a₂P.x+a₄−a₁P.y`,
`u(P) = 2P.y+a₁P.x+a₃ ≠ 0` (non-2-torsion `P`).

The proof is the invariant-differential `L'Hôpital`: with `f := x_gen − x_gen^q` (a uniformizer at
`P`, `Dω f = u_gen` a unit since `q = 0`) and `g := y_gen − (−π)^*y_gen`, the function
`φ := g − λ·f` satisfies `Dω φ = ν_gen − λ·u_gen ≡ 0`, and both `φ` and `Dω φ` vanish at `P`, so
`ord_P φ ≥ 2` (`two_le_ord_P_of_Dω_vanishes_of_uniformizer`).  Hence
`addSlopePair − λ = φ/f` has `ord_P ≥ 1`, i.e. `addSlopePair ≡ λ`. -/
theorem oneSub_addSlopePair_resid_doubling (hq : 2 ≤ Fintype.card K)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint)
    (hx_eq : P.x = (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) P.x)
    (hfrobneg : (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) P.y =
      (W.baseChange (AlgebraicClosure K)).toAffine.negY P.x P.y)
    (huP : 2 * P.y + (W.baseChange (AlgebraicClosure K)).a₁ * P.x +
      (W.baseChange (AlgebraicClosure K)).a₃ ≠ 0) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      (addSlopePair (Isogeny.id (W.baseChange (AlgebraicClosure K)).toAffine)
          (negFrobBaseChange W p r) -
        algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
          ((3 * P.x ^ 2 + 2 * (W.baseChange (AlgebraicClosure K)).a₂ * P.x +
              (W.baseChange (AlgebraicClosure K)).a₄ -
              (W.baseChange (AlgebraicClosure K)).a₁ * P.y) /
            (2 * P.y + (W.baseChange (AlgebraicClosure K)).a₁ * P.x +
              (W.baseChange (AlgebraicClosure K)).a₃))) < 1 := by
  set L := AlgebraicClosure K
  -- `revert` so that `set Wb`/`set C` (which abstract the curve in `P`'s type) re-introduce `P`
  -- consistently, avoiding a `set`-generalisation shadow.
  revert P hx_eq hfrobneg huP
  set Wb := W.baseChange L
  set C := (⟨Wb.toAffine⟩ : SmoothPlaneCurve L)
  intro P hx_eq hfrobneg huP
  set nuP : L := 3 * P.x ^ 2 + 2 * Wb.a₂ * P.x + Wb.a₄ - Wb.a₁ * P.y with hnuP
  set uP : L := 2 * P.y + Wb.a₁ * P.x + Wb.a₃ with huP_def
  set lamC : Wb.toAffine.FunctionField := algebraMap L Wb.toAffine.FunctionField (nuP / uP) with hlamC
  set f : Wb.toAffine.FunctionField :=
    HasseWeil.x_gen Wb - HasseWeil.x_gen Wb ^ Fintype.card K with hf
  set g : Wb.toAffine.FunctionField :=
    HasseWeil.y_gen Wb - (negFrobBaseChange W p r).pullback (HasseWeil.y_gen Wb) with hg
  have hqzero : ((Fintype.card K : ℕ) : Wb.toAffine.FunctionField) = 0 := by
    haveI : CharP L p :=
      charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective K L) p
    haveI : CharP Wb.toAffine.FunctionField p :=
      charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective L Wb.toAffine.FunctionField) p
    rw [CharP.cast_eq_zero_iff Wb.toAffine.FunctionField p]
    have hcard : Fintype.card K = p ^ r := Fact.out
    have hr : 1 ≤ r := by
      by_contra! h
      have hr0 : r = 0 := by omega
      rw [hr0, pow_zero] at hcard
      omega
    rw [hcard]
    exact dvd_pow_self p (by omega)
  have hα₂x : (negFrobBaseChange W p r).pullback (HasseWeil.x_gen Wb) =
      HasseWeil.x_gen Wb ^ Fintype.card K := negFrobBaseChange_pullback_x_gen W p r
  have hidx : (Isogeny.id Wb.toAffine).pullback (HasseWeil.x_gen Wb) = HasseWeil.x_gen Wb := rfl
  have hidy : (Isogeny.id Wb.toAffine).pullback (HasseWeil.y_gen Wb) = HasseWeil.y_gen Wb := rfl
  have hxne_KE : HasseWeil.x_gen Wb ≠ HasseWeil.x_gen Wb ^ Fintype.card K := by
    intro hxe
    have hord := congrArg (W_smooth Wb).ordAtInfty hxe
    rw [HasseWeil.ordAtInfty_x_gen, HasseWeil.ordAtInfty_x_gen_pow,
      ← WithTop.coe_nsmul, WithTop.coe_inj, nsmul_eq_mul] at hord
    have hqle : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    nlinarith [hord, hqle]
  have hpb_ne : (Isogeny.id Wb.toAffine).pullback (HasseWeil.x_gen Wb) ≠
      (negFrobBaseChange W p r).pullback (HasseWeil.x_gen Wb) := by
    rw [hidx, hα₂x]; exact hxne_KE
  have hslope_eq : addSlopePair (Isogeny.id Wb.toAffine) (negFrobBaseChange W p r) = g / f := by
    rw [addSlopePair_eq_of_x_ne hpb_ne, hidx, hidy, hα₂x, hg, hf]
  have hf_ne : f ≠ 0 := by rw [hf]; exact sub_ne_zero.mpr hxne_KE
  have hDωxq : Dω Wb (HasseWeil.x_gen Wb ^ Fintype.card K) = 0 := by
    rw [Dω_pow, hqzero, zero_mul, zero_mul]
  have hDf : Dω Wb f = HasseWeil.u_gen Wb := by
    rw [hf, Dω_sub, hDωxq, Dω_x_gen]; abel
  have hα₂y : (negFrobBaseChange W p r).pullback (HasseWeil.y_gen Wb) =
      -(HasseWeil.y_gen Wb ^ Fintype.card K) -
        algebraMap L Wb.toAffine.FunctionField Wb.a₁ * HasseWeil.x_gen Wb ^ Fintype.card K -
        algebraMap L Wb.toAffine.FunctionField Wb.a₃ := negFrobBaseChange_pullback_y_gen W p r
  have hDωyq : Dω Wb (HasseWeil.y_gen Wb ^ Fintype.card K) = 0 := by
    rw [Dω_pow, hqzero, zero_mul, zero_mul]
  have hDα₂y : Dω Wb ((negFrobBaseChange W p r).pullback (HasseWeil.y_gen Wb)) = 0 := by
    rw [hα₂y]
    simp only [Dω_sub, Dω_neg, hDωyq, Dω_algebraMap, Dω_mul, mul_zero, zero_add, hDωxq]
    abel
  have hDg : Dω Wb g = 3 * HasseWeil.x_gen Wb ^ 2 +
      2 * algebraMap L Wb.toAffine.FunctionField Wb.a₂ * HasseWeil.x_gen Wb +
      algebraMap L Wb.toAffine.FunctionField Wb.a₄ -
      algebraMap L Wb.toAffine.FunctionField Wb.a₁ * HasseWeil.y_gen Wb := by
    rw [hg, Dω_sub, hDα₂y, Dω_y_gen]; abel
  have hx_res : C.pointValuation P
      (HasseWeil.x_gen Wb - algebraMap L Wb.toAffine.FunctionField P.x) < 1 := residPV_x_gen W P
  have hy_res : C.pointValuation P
      (HasseWeil.y_gen Wb - algebraMap L Wb.toAffine.FunctionField P.y) < 1 :=
    pointValuation_y_gen_sub_const_lt_one_at_smoothPoint Wb P P.y rfl
  have huu : C.pointValuation P (HasseWeil.u_gen Wb - algebraMap L Wb.toAffine.FunctionField uP) < 1 := by
    rw [show HasseWeil.u_gen Wb = 2 * HasseWeil.y_gen Wb +
          algebraMap L Wb.toAffine.FunctionField Wb.a₁ * HasseWeil.x_gen Wb +
          algebraMap L Wb.toAffine.FunctionField Wb.a₃ from rfl, huP_def]
    have r2 := residPV_const W P (2 : L)
    have ra1 := residPV_const W P Wb.a₁
    have ra3 := residPV_const W P Wb.a₃
    have := residPV_add W (residPV_add W (residPV_mul W r2 hy_res) (residPV_mul W ra1 hx_res)) ra3
    refine lt_of_eq_of_lt (congrArg _ ?_) this
    simp only [map_ofNat, map_add, map_mul]; ring
  have hu_unit : C.pointValuation P (HasseWeil.u_gen Wb) = 1 := residPV_unit W huu huP
  have hu_ne : HasseWeil.u_gen Wb ≠ 0 := HasseWeil.u_gen_ne_zero Wb
  have hxq : P.x ^ Fintype.card K = P.x := by
    rw [← FiniteField.frobeniusAlgHom_apply K (AlgebraicClosure K) P.x]; exact hx_eq.symm
  have hf_lt : C.pointValuation P f < 1 := by
    rw [hf]
    have := residPV_sub W hx_res (residPV_pow W hx_res (Fintype.card K))
    rw [hxq, sub_self, map_zero] at this
    convert this using 2
    abel
  have hDf_ord : C.ord_P P (Dω Wb f) = 0 := by
    rw [hDf]
    exact (Curves.SmoothPlaneCurve.ord_P_eq_zero_iff_pointValuation_eq_one C hu_ne).mpr hu_unit
  have hf_ord1 : C.ord_P P f = ((1 : ℤ) : WithTop ℤ) := by
    refine le_antisymm ?_ ?_
    · by_contra! hlt
      have h2le : ((2 : ℤ) : WithTop ℤ) ≤ C.ord_P P f := by
        obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp ((C.ord_P_eq_top_iff f).not.mpr hf_ne)
        rw [← hm] at hlt ⊢
        rw [WithTop.coe_lt_coe] at hlt
        rw [WithTop.coe_le_coe]
        omega
      have := one_le_ord_P_Dω_of_two_le Wb hf_ne P h2le
      rw [hDf_ord] at this
      exact absurd this (by simp)
    · exact_mod_cast (C.one_le_ord_P_iff_pointValuation_lt_one (P := P) hf_ne).mpr hf_lt
  set φ : Wb.toAffine.FunctionField := g - lamC * f with hφ
  have hg_res : C.pointValuation P g < 1 := by
    rw [hg]
    have hres_α₂y : C.pointValuation P
        ((negFrobBaseChange W p r).pullback (HasseWeil.y_gen Wb) -
          algebraMap L Wb.toAffine.FunctionField P.y) < 1 := by
      rw [hα₂y]
      have ryq := residPV_pow W hy_res (Fintype.card K)
      have rxq := residPV_pow W hx_res (Fintype.card K)
      have ra1 := residPV_const W P Wb.a₁
      have ra3 := residPV_const W P Wb.a₃
      have hstep := residPV_sub W (residPV_sub W (residPV_neg W ryq) (residPV_mul W ra1 rxq)) ra3
      have hval : -(P.y ^ Fintype.card K) - Wb.a₁ * P.x ^ Fintype.card K - Wb.a₃ = P.y := by
        have hyq : P.y ^ Fintype.card K = Wb.toAffine.negY P.x P.y := by
          rw [← FiniteField.frobeniusAlgHom_apply K (AlgebraicClosure K) P.y]; exact hfrobneg
        rw [hyq, hxq, WeierstrassCurve.Affine.negY]; ring
      rwa [hval] at hstep
    have := residPV_sub W hy_res hres_α₂y
    rw [sub_self, map_zero] at this
    convert this using 2; abel
  have hφ_res : C.pointValuation P φ < 1 := by
    rw [hφ]
    have hlamf : C.pointValuation P (lamC * f) < 1 := by
      rw [hlamC]
      exact pointValuation_mul_lt_one_of_le_and_lt (W.baseChange (AlgebraicClosure K)) P
        (C.pointValuation_algebraMap_F_le_one P (nuP / uP)) hf_lt
    exact lt_of_le_of_lt ((C.pointValuation P).map_sub _ _) (max_lt hg_res hlamf)
  have hDφ_res : C.pointValuation P (Dω Wb φ) < 1 := by
    have hDlamC : Dω Wb lamC = 0 := by rw [hlamC]; exact Dω_algebraMap _ _
    have hDφ_eq : Dω Wb φ = (3 * HasseWeil.x_gen Wb ^ 2 +
        2 * algebraMap L Wb.toAffine.FunctionField Wb.a₂ * HasseWeil.x_gen Wb +
        algebraMap L Wb.toAffine.FunctionField Wb.a₄ -
        algebraMap L Wb.toAffine.FunctionField Wb.a₁ * HasseWeil.y_gen Wb) -
        lamC * HasseWeil.u_gen Wb := by
      rw [hφ, Dω_sub, Dω_mul, hDlamC, hDf, hDg]; ring
    rw [hDφ_eq]
    have hν_res : C.pointValuation P
        ((3 * HasseWeil.x_gen Wb ^ 2 +
            2 * algebraMap L Wb.toAffine.FunctionField Wb.a₂ * HasseWeil.x_gen Wb +
            algebraMap L Wb.toAffine.FunctionField Wb.a₄ -
            algebraMap L Wb.toAffine.FunctionField Wb.a₁ * HasseWeil.y_gen Wb) -
          algebraMap L Wb.toAffine.FunctionField nuP) < 1 := by
      have r3 := residPV_const W P (3 : L)
      have ra2 := residPV_const W P Wb.a₂
      have ra4 := residPV_const W P Wb.a₄
      have ra1 := residPV_const W P Wb.a₁
      have hstep := residPV_sub W (residPV_add W (residPV_add W
        (residPV_mul W r3 (residPV_pow W hx_res 2))
        (residPV_mul W (residPV_mul W (residPV_const W P (2 : L)) ra2) hx_res)) ra4)
        (residPV_mul W ra1 hy_res)
      rw [hnuP]
      refine lt_of_eq_of_lt (congrArg _ ?_) hstep
      simp only [map_ofNat, map_add, map_mul, map_sub]; ring
    have hlamu_res : C.pointValuation P
        (lamC * HasseWeil.u_gen Wb - algebraMap L Wb.toAffine.FunctionField nuP) < 1 := by
      rw [hlamC]
      have := residPV_mul W (residPV_const W P (nuP / uP)) huu
      rw [div_mul_cancel₀ nuP huP] at this
      exact this
    have := residPV_sub W hν_res hlamu_res
    rw [sub_self, map_zero] at this
    convert this using 2; abel
  by_cases hφ0 : φ = 0
  · have hgf : g = lamC * f := by rw [hφ, sub_eq_zero] at hφ0; exact hφ0
    rw [hslope_eq, hgf, mul_div_assoc, div_self hf_ne, mul_one, hlamC, sub_self, map_zero]
    exact zero_lt_one
  · have hφ_ge1 : ((1 : ℤ) : WithTop ℤ) ≤ C.ord_P P φ :=
      (C.one_le_ord_P_iff_pointValuation_lt_one (P := P) hφ0).mpr hφ_res
    have hDφ_ge1 : ((1 : ℤ) : WithTop ℤ) ≤ C.ord_P P (Dω Wb φ) := by
      by_cases hDφ0 : Dω Wb φ = 0
      · rw [hDφ0, C.ord_P_zero]; exact le_top
      · exact (C.one_le_ord_P_iff_pointValuation_lt_one (P := P) hDφ0).mpr hDφ_res
    have hφ_ge2 : ((2 : ℤ) : WithTop ℤ) ≤ C.ord_P P φ :=
      two_le_ord_P_of_Dω_vanishes_of_uniformizer Wb hφ0 P hφ_ge1 hDφ_ge1 hf_ord1 hDf_ord
    have hdiff_eq : addSlopePair (Isogeny.id Wb.toAffine) (negFrobBaseChange W p r) - lamC =
        φ / f := by
      rw [hslope_eq, hφ, eq_comm, sub_div, mul_div_assoc, div_self hf_ne, mul_one]
    have hdiff_ne : addSlopePair (Isogeny.id Wb.toAffine) (negFrobBaseChange W p r) - lamC ≠ 0 := by
      rw [hdiff_eq]; exact div_ne_zero hφ0 hf_ne
    have hord_diff : ((1 : ℤ) : WithTop ℤ) ≤ C.ord_P P
        (addSlopePair (Isogeny.id Wb.toAffine) (negFrobBaseChange W p r) - lamC) := by
      rw [hdiff_eq, div_eq_mul_inv, C.ord_P_mul, C.ord_P_inv _ hf_ne, hf_ord1]
      calc ((1 : ℤ) : WithTop ℤ) = ((2 : ℤ) : WithTop ℤ) + (-((1 : ℤ) : WithTop ℤ)) := rfl
        _ ≤ C.ord_P P φ + (-((1 : ℤ) : WithTop ℤ)) := by gcongr
    exact (C.one_le_ord_P_iff_pointValuation_lt_one (P := P) hdiff_ne).mp hord_diff

/-- **The two generator residues for `(1 − π)_{K̄}` at a doubling affine image** (CoordHom-free).
For a smooth point `P` of `E_{K̄}` whose image `(1 − π)P = some x y` is finite and *doubling*
(`P.x = P.x^q`), the two generator residues hold:

  `(1 − π)^* x_gen ≡ x`  and  `(1 − π)^* y_gen ≡ y`  (modulo `m_P`).

Via the general slope-parametric `isog_coords_at_affine_of_decomp_slope` with `α₁ = id`,
`α₂ = negFrobBaseChange` (the `−π` summand), supplying the pullback decomposition, the per-summand
point images and residues, and the *tangent* slope residue `addSlopePair ≡ slope = ν(P)/u(P)`
(`oneSub_addSlopePair_resid_doubling`).  The doubling case `(1 − π)P = 2P` is the tangent branch. -/
theorem oneSub_two_residues_doubling (hq : 2 ≤ Fintype.card K)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x y : AlgebraicClosure K}
    (h_ns : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular x y)
    (hx_eq : P.x = (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) P.x)
    (hQ : (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom P.toAffinePoint =
        Affine.Point.some x y h_ns) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
            (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x) < 1 ∧
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
            (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y) < 1 := by
  set frob := FiniteField.frobeniusAlgHom K (AlgebraicClosure K)
  set α := oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq) with hα
  obtain ⟨hfrobneg, hne1⟩ := oneSub_frob_eq_neg_at_doubling W p r hq P h_ns hx_eq hQ
  have huP : 2 * P.y + (W.baseChange (AlgebraicClosure K)).a₁ * P.x + (W.baseChange (AlgebraicClosure K)).a₃ ≠ 0 := by
    have hne : (W.baseChange (AlgebraicClosure K)).toAffine.negY P.x P.y ≠ P.y := fun h ↦ hne1 (by rw [hfrobneg, h])
    intro h0
    apply hne
    rw [WeierstrassCurve.Affine.negY]; linear_combination -h0
  have hα₁ : (Isogeny.id (W.baseChange (AlgebraicClosure K)).toAffine).toAddMonoidHom P.toAffinePoint =
      Affine.Point.some P.x P.y P.nonsingular := rfl
  have hα₂ : (negFrobBaseChange W p r).toAddMonoidHom P.toAffinePoint =
      Affine.Point.some (frob P.x) ((W.baseChange (AlgebraicClosure K)).toAffine.negY (frob P.x) (frob P.y)) _ :=
    negFrobBaseChange_apply_some W p r P.nonsingular
  have hsum_pt : α.toAddMonoidHom P.toAffinePoint =
      (Isogeny.id (W.baseChange (AlgebraicClosure K)).toAffine).toAddMonoidHom P.toAffinePoint +
        (negFrobBaseChange W p r).toAddMonoidHom P.toAffinePoint := by
    rw [hα, oneSubFrobeniusIsogBaseChange_toAddMonoidHom, negFrobBaseChange_toAddMonoidHom,
      AddMonoidHom.sub_apply, AddMonoidHom.neg_apply, sub_eq_add_neg]
    rfl
  rw [hα₁, hα₂] at hsum_pt
  have hx₁ : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      ((Isogeny.id (W.baseChange (AlgebraicClosure K)).toAffine).pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) - algebraMap (AlgebraicClosure K) _ P.x) < 1 :=
    residPV_x_gen W P
  have hy₁ : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      ((Isogeny.id (W.baseChange (AlgebraicClosure K)).toAffine).pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) - algebraMap (AlgebraicClosure K) _ P.y) < 1 :=
    pointValuation_y_gen_sub_const_lt_one_at_smoothPoint (W.baseChange (AlgebraicClosure K)) P P.y rfl
  have hx₂ : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      ((negFrobBaseChange W p r).pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) -
        algebraMap (AlgebraicClosure K) _ (frob P.x)) < 1 := by
    rw [negFrobBaseChange_pullback_x_gen, FiniteField.coe_frobeniusAlgHom]
    exact residPV_pow W (residPV_x_gen W P) (Fintype.card K)
  have hy₂ : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      ((negFrobBaseChange W p r).pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) -
        algebraMap (AlgebraicClosure K) _ ((W.baseChange (AlgebraicClosure K)).toAffine.negY (frob P.x) (frob P.y))) < 1 := by
    rw [negFrobBaseChange_pullback_y_gen]
    rw [show (W.baseChange (AlgebraicClosure K)).toAffine.negY (frob P.x) (frob P.y) =
        -(P.y ^ Fintype.card K) - (W.baseChange (AlgebraicClosure K)).a₁ * P.x ^ Fintype.card K - (W.baseChange (AlgebraicClosure K)).a₃ by
      rw [WeierstrassCurve.Affine.negY,
        show frob P.x = P.x ^ Fintype.card K from
          FiniteField.frobeniusAlgHom_apply K (AlgebraicClosure K) P.x,
        show frob P.y = P.y ^ Fintype.card K from
          FiniteField.frobeniusAlgHom_apply K (AlgebraicClosure K) P.y]]
    have r_yq := residPV_pow W
      (pointValuation_y_gen_sub_const_lt_one_at_smoothPoint (W.baseChange (AlgebraicClosure K)) P P.y rfl) (Fintype.card K)
    have r_xq := residPV_pow W (residPV_x_gen W P) (Fintype.card K)
    have r_a1 := residPV_const W P (W.baseChange (AlgebraicClosure K)).a₁
    have r_a3 := residPV_const W P (W.baseChange (AlgebraicClosure K)).a₃
    have r_step := residPV_sub W (residPV_sub W (residPV_neg W r_yq) (residPV_mul W r_a1 r_xq)) r_a3
    convert r_step using 2
  have hslope_val : (W.baseChange (AlgebraicClosure K)).toAffine.slope P.x (frob P.x) P.y ((W.baseChange (AlgebraicClosure K)).toAffine.negY (frob P.x) (frob P.y)) =
      (3 * P.x ^ 2 + 2 * (W.baseChange (AlgebraicClosure K)).a₂ * P.x + (W.baseChange (AlgebraicClosure K)).a₄ - (W.baseChange (AlgebraicClosure K)).a₁ * P.y) /
        (2 * P.y + (W.baseChange (AlgebraicClosure K)).a₁ * P.x + (W.baseChange (AlgebraicClosure K)).a₃) := by
    have hxeq2 : P.x = frob P.x := hx_eq
    have hyne : P.y ≠ (W.baseChange (AlgebraicClosure K)).toAffine.negY (frob P.x) ((W.baseChange (AlgebraicClosure K)).toAffine.negY (frob P.x) (frob P.y)) := by
      rw [WeierstrassCurve.Affine.negY_negY]; exact hne1
    rw [WeierstrassCurve.Affine.slope_of_Y_ne hxeq2 hyne]
    have hden : P.y - (W.baseChange (AlgebraicClosure K)).toAffine.negY P.x P.y = 2 * P.y + (W.baseChange (AlgebraicClosure K)).a₁ * P.x + (W.baseChange (AlgebraicClosure K)).a₃ := by
      rw [WeierstrassCurve.Affine.negY]; ring
    rw [hden]
  have hxy_pts : ¬(P.x = frob P.x ∧
      P.y = (W.baseChange (AlgebraicClosure K)).toAffine.negY (frob P.x) ((W.baseChange (AlgebraicClosure K)).toAffine.negY (frob P.x) (frob P.y))) := by
    rintro ⟨_, h2⟩
    rw [WeierstrassCurve.Affine.negY_negY] at h2
    exact hne1 h2
  have hL : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      (addSlopePair (Isogeny.id (W.baseChange (AlgebraicClosure K)).toAffine) (negFrobBaseChange W p r) -
        algebraMap (AlgebraicClosure K) _ ((W.baseChange (AlgebraicClosure K)).toAffine.slope P.x (frob P.x) P.y
          ((W.baseChange (AlgebraicClosure K)).toAffine.negY (frob P.x) (frob P.y)))) < 1 := by
    rw [hslope_val]
    exact oneSub_addSlopePair_resid_doubling W p r hq P hx_eq hfrobneg huP
  exact isog_coords_at_affine_of_decomp_slope (W := (W.baseChange (AlgebraicClosure K)))
    (α := α) (α₁ := Isogeny.id (W.baseChange (AlgebraicClosure K)).toAffine) (α₂ := negFrobBaseChange W p r)
    (oneSub_pullback_x_gen_eq_addPullback_x_pair W p r hq)
    (oneSub_pullback_y_gen_eq_addPullback_y_pair W p r hq)
    P h_ns hα₁ hα₂ hx₁ hx₂ hy₁ hL hxy_pts hsum_pt hQ

/-- **The non-2-torsion-image unit `ord_P (α^*u) = 0` for `(1 − π)_{K̄}`** (CoordHom-free).  For a
smooth point `P` whose image `(1 − π)P = some x y` is finite *non-doubling* (`P.x ≠ P.x^q`) and
*non-2-torsion* (`2y + a₁x + a₃ ≠ 0`), the pulled-back invariant-differential denominator
`alpha_star_u (1 − π) = (1 − π)^* u_gen` is a unit at `P`, i.e. `ord_P = 0`.

`alpha_star_u (1 − π) = 2·(1 − π)^*y_gen + a₁·(1 − π)^*x_gen + a₃` residues (via the two generator
residues `oneSub_two_residues_nondoubling`) to `2y + a₁x + a₃ ≠ 0`, hence is a unit at `P`. -/
theorem oneSub_alpha_star_u_ord_eq_zero (hq : 2 ≤ Fintype.card K)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x y : AlgebraicClosure K}
    (h_ns : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular x y)
    (hx_ne : P.x ≠ (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) P.x)
    (h2tor : 2 * y + (W.baseChange (AlgebraicClosure K)).a₁ * x + (W.baseChange (AlgebraicClosure K)).a₃ ≠ 0)
    (hQ : (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom P.toAffinePoint =
        Affine.Point.some x y h_ns) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).ord_P P
        (alpha_star_u (W.baseChange (AlgebraicClosure K))
          (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))) = 0 := by
  obtain ⟨hx, hy⟩ := oneSub_two_residues_nondoubling W p r hq P h_ns hx_ne hQ
  set α := oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
    (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)
  have hu_resid : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      (alpha_star_u (W.baseChange (AlgebraicClosure K)) α -
        algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
          (2 * y + (W.baseChange (AlgebraicClosure K)).a₁ * x +
            (W.baseChange (AlgebraicClosure K)).a₃)) < 1 := by
    rw [alpha_star_u_eq, show HasseWeil.u_gen (W.baseChange (AlgebraicClosure K)) =
        2 * HasseWeil.y_gen (W.baseChange (AlgebraicClosure K)) +
          algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
            (W.baseChange (AlgebraicClosure K)).a₁ *
            HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)) +
          algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
            (W.baseChange (AlgebraicClosure K)).a₃ from rfl]
    simp only [map_add, map_mul, map_ofNat, AlgHom.commutes]
    have r2 := residPV_const W P (2 : AlgebraicClosure K)
    have ra1 := residPV_const W P (W.baseChange (AlgebraicClosure K)).a₁
    have ra3 := residPV_const W P (W.baseChange (AlgebraicClosure K)).a₃
    have r_step := residPV_add W (residPV_add W (residPV_mul W r2 hy) (residPV_mul W ra1 hx)) ra3
    convert r_step using 2
    simp [map_ofNat]
  have hunit : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      (alpha_star_u (W.baseChange (AlgebraicClosure K)) α) = 1 := residPV_unit W hu_resid h2tor
  have hau_ne : alpha_star_u (W.baseChange (AlgebraicClosure K)) α ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero] at hunit
    exact zero_ne_one hunit
  exact (Curves.SmoothPlaneCurve.ord_P_eq_zero_iff_pointValuation_eq_one
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K))
    hau_ne).mpr hunit

/-- **The non-2-torsion-image unit `ord_P (α^*u) = 0`, from the two residues** (CoordHom-free).  Same
as `oneSub_alpha_star_u_ord_eq_zero` but taking the two generator residues `(1−π)^*x_gen ≡ x`,
`(1−π)^*y_gen ≡ y` directly (so it serves *both* the doubling and non-doubling cases). -/
theorem oneSub_alpha_star_u_ord_eq_zero_of_residues (hq : 2 ≤ Fintype.card K)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x y : AlgebraicClosure K}
    (hx : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
            (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x) < 1)
    (hy : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
            (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y) < 1)
    (h2tor : 2 * y + (W.baseChange (AlgebraicClosure K)).a₁ * x +
      (W.baseChange (AlgebraicClosure K)).a₃ ≠ 0) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).ord_P P
        (alpha_star_u (W.baseChange (AlgebraicClosure K))
          (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))) = 0 := by
  set α := oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
    (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)
  have hu_resid : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      (alpha_star_u (W.baseChange (AlgebraicClosure K)) α -
        algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
          (2 * y + (W.baseChange (AlgebraicClosure K)).a₁ * x +
            (W.baseChange (AlgebraicClosure K)).a₃)) < 1 := by
    rw [alpha_star_u_eq, show HasseWeil.u_gen (W.baseChange (AlgebraicClosure K)) =
        2 * HasseWeil.y_gen (W.baseChange (AlgebraicClosure K)) +
          algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
            (W.baseChange (AlgebraicClosure K)).a₁ *
            HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)) +
          algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
            (W.baseChange (AlgebraicClosure K)).a₃ from rfl]
    simp only [map_add, map_mul, map_ofNat, AlgHom.commutes]
    have r2 := residPV_const W P (2 : AlgebraicClosure K)
    have ra1 := residPV_const W P (W.baseChange (AlgebraicClosure K)).a₁
    have ra3 := residPV_const W P (W.baseChange (AlgebraicClosure K)).a₃
    have r_step := residPV_add W (residPV_add W (residPV_mul W r2 hy) (residPV_mul W ra1 hx)) ra3
    convert r_step using 2
    simp [map_ofNat]
  have hunit : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      (alpha_star_u (W.baseChange (AlgebraicClosure K)) α) = 1 := residPV_unit W hu_resid h2tor
  have hau_ne : alpha_star_u (W.baseChange (AlgebraicClosure K)) α ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero] at hunit
    exact zero_ne_one hunit
  exact (Curves.SmoothPlaneCurve.ord_P_eq_zero_iff_pointValuation_eq_one
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K))
    hau_ne).mpr hunit

/-- **The 2-torsion-image `y`-numerator unit `ord_P ((1−π)^*ν) = 0`, from the two residues**
(CoordHom-free).  At a *2-torsion* image `Q = (1−π)P` (`2y + a₁x + a₃ = 0`), the pulled-back
`y`-numerator `(1−π)^*ν = 3((1−π)^*x_gen)²+2a₂((1−π)^*x_gen)+a₄−a₁((1−π)^*y_gen)` is a *unit* at `P`
(`ord_P = 0`): it residues to `ν(Q) = 3x²+2a₂x+a₄−a₁y`, which is non-zero because `Q` is nonsingular
and its `y`-partial `u(Q) = 2y+a₁x+a₃` vanishes.  This is the `e = 1` input of the `y`-uniformizer
route for the 2-torsion-image case. -/
theorem oneSub_alpha_star_polyX_ord_eq_zero_of_residues (hq : 2 ≤ Fintype.card K)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x y : AlgebraicClosure K}
    (h_ns : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular x y)
    (hx : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
            (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x) < 1)
    (hy : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
            (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y) < 1)
    (h2tor : 2 * y + (W.baseChange (AlgebraicClosure K)).a₁ * x +
      (W.baseChange (AlgebraicClosure K)).a₃ = 0) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).ord_P P
        (3 * ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
              (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
              (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)))) ^ 2 +
          2 * algebraMap (AlgebraicClosure K)
              (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
              (W.baseChange (AlgebraicClosure K)).a₂ *
            ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
              (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
              (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)))) +
          algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
              (W.baseChange (AlgebraicClosure K)).a₄ -
          algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
              (W.baseChange (AlgebraicClosure K)).a₁ *
            ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
              (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
              (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))))) = 0 := by
  set α := oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)
  have hνQ_ne : 3 * x ^ 2 + 2 * (W.baseChange (AlgebraicClosure K)).a₂ * x + (W.baseChange (AlgebraicClosure K)).a₄ - (W.baseChange (AlgebraicClosure K)).a₁ * y ≠ 0 := by
    intro h0
    -- both partials of the nonsingular Weierstrass equation would vanish, contradicting `h_ns`.
    rcases ((WeierstrassCurve.Affine.nonsingular_iff' (W := (W.baseChange (AlgebraicClosure K)).toAffine) x y).mp h_ns).2 with hX | hY
    · exact hX (by linear_combination -h0)
    · exact hY h2tor
  have hν_resid : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      ((3 * (α.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)))) ^ 2 +
          2 * algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (W.baseChange (AlgebraicClosure K)).a₂ * (α.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)))) +
          algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (W.baseChange (AlgebraicClosure K)).a₄ -
          algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (W.baseChange (AlgebraicClosure K)).a₁ * (α.pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))))) -
        algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (3 * x ^ 2 + 2 * (W.baseChange (AlgebraicClosure K)).a₂ * x + (W.baseChange (AlgebraicClosure K)).a₄ - (W.baseChange (AlgebraicClosure K)).a₁ * y)) < 1 := by
    have r3 := residPV_const W P (3 : (AlgebraicClosure K))
    have ra2 := residPV_const W P (W.baseChange (AlgebraicClosure K)).a₂
    have ra4 := residPV_const W P (W.baseChange (AlgebraicClosure K)).a₄
    have ra1 := residPV_const W P (W.baseChange (AlgebraicClosure K)).a₁
    have hstep := residPV_sub W (residPV_add W (residPV_add W
      (residPV_mul W r3 (residPV_pow W hx 2))
      (residPV_mul W (residPV_mul W (residPV_const W P (2 : (AlgebraicClosure K))) ra2) hx)) ra4)
      (residPV_mul W ra1 hy)
    refine lt_of_eq_of_lt (congrArg _ ?_) hstep
    simp [map_ofNat]
  have hunit : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      (3 * (α.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)))) ^ 2 +
        2 * algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (W.baseChange (AlgebraicClosure K)).a₂ * (α.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)))) +
        algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (W.baseChange (AlgebraicClosure K)).a₄ -
        algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (W.baseChange (AlgebraicClosure K)).a₁ * (α.pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))))) = 1 :=
    residPV_unit W hν_resid hνQ_ne
  have hν_ne : 3 * (α.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)))) ^ 2 +
      2 * algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (W.baseChange (AlgebraicClosure K)).a₂ * (α.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)))) +
      algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (W.baseChange (AlgebraicClosure K)).a₄ -
      algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (W.baseChange (AlgebraicClosure K)).a₁ * (α.pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K)))) ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero] at hunit
    exact zero_ne_one hunit
  exact (Curves.SmoothPlaneCurve.ord_P_eq_zero_iff_pointValuation_eq_one (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)) hν_ne).mpr hunit

/-- **The affine comap-valuation identity for `(1 − π)_{K̄}` at a non-doubling, non-2-torsion image**
(CoordHom-free, `e = 1` derived, no carried `OneSubAffineResidues`).

For a smooth point `P` of `E_{K̄}` whose image `(1 − π)P = some x y` is finite, *non-doubling*
(`P.x ≠ P.x^q`), and *non-2-torsion* (`2y + a₁x + a₃ ≠ 0`),
`(pointValuation P).comap (1 − π)^* = pointValuation ⟨x, y, h_ns⟩` outright.

This is the `affine` field of `ComapPointValuationWitness` at non-doubling non-2-torsion images,
discharged via the general headline `comap_pointValuation_isog_eq_affine` with:

* the two generator residues `oneSub_two_residues_nondoubling` (CoordHom-free, the substantive
  base-change-naturality content);
* the non-2-torsion unit `oneSub_alpha_star_u_ord_eq_zero` (`e = 1` via the invariant differential);
* the separability coefficient `≠ 0` and the constancy `∈ range` — BOTH now *discharged* from the
  omega-coefficient VALUE base-change transport `omegaPullbackCoeff (1 − π)_{K̄} = 1`
  (`omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_eq_one`), so `OmegaBaseChangeNeZero`/`hcoeff_mem`
  are NO LONGER carried. -/
theorem comap_pointValuation_oneSub_eq_affine_nondoubling
    (hq : 2 ≤ Fintype.card K)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x y : AlgebraicClosure K}
    (h_ns : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular x y)
    (hx_ne : P.x ≠ (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) P.x)
    (h2tor : 2 * y + (W.baseChange (AlgebraicClosure K)).a₁ * x +
      (W.baseChange (AlgebraicClosure K)).a₃ ≠ 0)
    (hQ : (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom P.toAffinePoint =
        Affine.Point.some x y h_ns) :
    ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P).comap
        (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
          (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback.toRingHom =
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation ⟨x, y, h_ns⟩ := by
  obtain ⟨hx, hy⟩ := oneSub_two_residues_nondoubling W p r hq P h_ns hx_ne hQ
  exact comap_pointValuation_isog_eq_affine
    (omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_mem_range W p r hq)
    (omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_ne_zero W p r hq)
    P h_ns hx hy (oneSub_alpha_star_u_ord_eq_zero W p r hq P h_ns hx_ne h2tor hQ)

/-- **The affine comap-valuation identity for `(1 − π)_{K̄}`, UNCONDITIONAL** (CoordHom-free,
`e = 1` derived, no carried `OneSubAffineResidues`, no non-doubling/non-2-torsion hypotheses).

For *every* smooth point `P` of `E_{K̄}` whose image `(1 − π)P = some x y` is affine,
`(pointValuation P).comap (1 − π)^* = pointValuation ⟨x, y, h_ns⟩` outright.  This is the universal
`affine` field of `ComapPointValuationWitness W (oneSubFrobeniusIsogBaseChange …)`.

The four cases of the addition formula are all discharged:

* **non-doubling** (`P.x ≠ P.x^q`): the two generator residues come from the secant
  (`oneSub_two_residues_nondoubling`);
* **doubling** (`P.x = P.x^q`, so `(1 − π)P = 2P`): the two generator residues come from the tangent
  (`oneSub_two_residues_doubling`, via the invariant-differential `L'Hôpital` slope residue
  `oneSub_addSlopePair_resid_doubling`);
* **non-2-torsion image** (`2y + a₁x + a₃ ≠ 0`): `e = 1` via the `x`-uniformizer
  (`comap_pointValuation_isog_eq_affine`, with `(1 − π)^*u` a unit);
* **2-torsion image** (`2y + a₁x + a₃ = 0`): `e = 1` via the `y`-uniformizer
  (`comap_pointValuation_isog_eq_affine_y`, with `(1 − π)^*ν` a unit — the other partial of the
  nonsingular Weierstrass equation).

The separability coefficient `≠ 0` and constancy `∈ range` are discharged from the omega-coefficient
VALUE transport `omegaPullbackCoeff (1 − π)_{K̄} = 1`. -/
theorem comap_pointValuation_oneSub_eq_affine
    (hq : 2 ≤ Fintype.card K)
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
  have hres : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
            (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x) < 1 ∧
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
            (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y) < 1 := by
    by_cases hx_eq : P.x = (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) P.x
    · exact oneSub_two_residues_doubling W p r hq P h_ns hx_eq hQ
    · exact oneSub_two_residues_nondoubling W p r hq P h_ns hx_eq hQ
  obtain ⟨hx, hy⟩ := hres
  by_cases h2tor : 2 * y + (W.baseChange (AlgebraicClosure K)).a₁ * x +
      (W.baseChange (AlgebraicClosure K)).a₃ = 0
  · exact comap_pointValuation_isog_eq_affine_y
      (omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_mem_range W p r hq)
      (omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_ne_zero W p r hq)
      P h_ns hx hy (oneSub_alpha_star_polyX_ord_eq_zero_of_residues W p r hq P h_ns hx hy h2tor)
  · exact comap_pointValuation_isog_eq_affine
      (omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_mem_range W p r hq)
      (omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_ne_zero W p r hq)
      P h_ns hx hy (oneSub_alpha_star_u_ord_eq_zero_of_residues W p r hq P hx hy h2tor)

end HasseWeil.WeilPairing

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.PencilComapScaling
import HasseWeil.WeilPairing.OneSubInftyResidues
import HasseWeil.WeilPairing.WallAGenericRealization
import HasseWeil.WeilPairing.SeparableWitnesses
import HasseWeil.EC.SeparableKernelTorsor

/-!
# The local comap-valuation witnesses for `(rπ − s)_{K̄}`, and `pencilScaling_holds` (leaf 3)

This is the **`rπ − s` analogue of the leaf-2 closers** `OneSubInftyResidues.lean` +
`OneSubAffineResidues.lean` + `OneSubProjOrdTransport.lean`: it assembles the three fields of
`ComapPointValuationWitness (W.baseChange K̄) (rπ − s)_{K̄}` for the canonical base-changed pullback
`pencilBaseChangePullback`, and closes the leaf-3 scaling `PencilScaling W p r K̄ pencilKerCard`.

## The infinity field (reused machinery)

The `infinity` and `affineToInfty` fields go through the **field-general** lemmas
`inftyOrdTransport_of_ordAtInfty_x_y` and
`comap_pointValuation_eq_infty_of_ordAtInfty_x_y_of_kernelInvariant` (`OneSubInftyResidues.lean`),
fed:

* the two `K̄` infinity orders of the base-changed pencil pullback on the generators
  (`ordAtInfty_pencil_pullback_x_gen` = `-2`, `ordAtInfty_pencil_pullback_y_gen` = `-3`), obtained by
  transporting the **K-level** orders `ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg` (`= -2`)
  and `ord_addPullback_y_pair_zsmul_frobenius_mulByInt_neg` (`= -3`, built in
  `AdditionPullback/Frobenius.lean`) through `ordAtInftyBaseChange_holds`; and
* the kernel-translation invariance `pencil_hcov_kernel`, the kernel specialisation of the proved
  Wall A generic-point covariance `mapTranslateGenericPoint_pencil_canonical`
  (`PencilCovariance.lean`), via `hcov_of_mapTranslateGenericPoint_canonical`.

## Current status (what is discharged vs. remaining)

**Discharged (axiom-clean):**
* the `infinity` / `affineToInfty` fields (above);
* **`finiteKer`** (`pencilIsogBaseChange_finiteKer`) — via the **trace-free** finite-dimensionality
  route `HasseWeil.finite_kernel_of_hcov`: `K(E_{K̄}) / (rπ−s)^* K(E_{K̄})` is finite-dimensional, so
  `Aut` is a `Fintype`, and the injective kernel-translation forward map (needing only
  `pencil_hcov_kernel`) embeds the kernel into it.  This **sidesteps** the Frobenius-dual route
  `ker ⊆ E[(rπ̂−s)∘(rπ−s)]`, which is a genuine wall over `K̄` (no geometric Verschiebung `V̄`, no
  characteristic-polynomial `π̄ + V̄ = [a]`);
* the **separability/constancy data** for the affine comap (`omegaPullbackCoeff_pencil`,
  `omegaPullbackCoeff_pencil_mem_range`, `omegaPullbackCoeff_pencil_ne_zero`);
* the reusable **comap → residue bridges** (`resid_x_gen_of_comap`, `resid_y_gen_of_comap`) and the
  **`[−s']` per-summand residue** (`mulByInt_neg_resid_xy`).

**Built (axiom-clean) — the `r·π̄`-summand residue** (the substantive geometric content, by the leaf-2
`negFrobBaseChange` template with `[r']` in place of `neg`): the **mulByInt base-change pullback
naturality** `mulByInt_baseChange_pullback_x/y_gen` (the linchpin, over the division-polynomial
base-change `WeierstrassCurve.map_Φ`/`map_ΨSq`/`map_ψ`/`map_ω`), the bespoke transparent summand
isogeny `rFrobBaseChange r'` with its generator pullbacks and point image, the addition-formula
naturalities (`addPullback_x/y_pair_rFrob_mulByInt`), the pullback/point decompositions, the
`r·π̄`-summand residue `rFrobBaseChange_resid_xy`, and the affine comap
`comap_pointValuation_pencil_eq_affine` itself (via the uniform `pencil_two_residues`).

**Closed since:** the doubling/tangent and `O`-summand branches (the per-summand
addition-formula case split has been removed outright in favour of the uniform
transport-to-`O` route below), the `r' = 0` member
(`pencilScalingComapDataCard_rZero`, identified with `[−s'] = mulByInt (−s')` and discharged by the
proved `comapPointValuationWitness_mulByInt`), and the inseparable `p ∣ s'` pairs (now excluded
**vacuously** in `pencilScaling_holds` by the `¬(ringChar K) ∣ s'` hypothesis — no false `#ker`-exponent
scaling is claimed for an inseparable member).

**The `O`-summand degeneracy is now DISCHARGED** by the *transport-to-`O`* lemma
`isog_resid_at_affine_of_hgcomm_hinfty`: for *any* isogeny over `K̄` carrying the canonical
generic-point covariance (`hgcomm`) and the infinity order-transport (`InftyOrdTransport`), the two
generator pullbacks residue to the image coordinates at *every* affine image `P` — with **no**
addition-formula decomposition, so the `O`-summand never arises.  The mechanism is
`ord_P P (φ^*(x_gen − x)) = ord_∞(φ^*(τ_R(x_gen − x)))` (covariance + the proved ∞-target transport
`isTranslateOrdAtInftyCompatible` at `S = −P`) `= ord_∞(τ_R(x_gen − x))` (`InftyOrdTransport`)
`= ord_R(x_gen − x) ≥ 1` (∞-source transport `ordProj_translate_infinity` + `x_gen − x ∈ m_R`), with
`R = φ P`.  `pencil_two_residues` is the application to the canonical pencil.

**Remaining (exactly ONE isolated `sorry`, a genuine geometric residual):**
* `pencilScalingComapDataCard_pDvdR` — the **`p ∣ r'` separable** bundle (`(r' : K) = 0` but
  `p ∤ s'`, so `rπ − s` is separable, `a = −s' ≠ 0`).  The irreducible obstruction is the **infinity
  order-transport** `InftyOrdTransport (rπ − s)_{K̄}` / the exact `∞`-orders `-2`, `-3`: for `p ∤ r'`
  these transport from the K-level `ord_addPullback_x_pair = -2`, whose proof rests essentially on
  `(r' : K) ≠ 0` (the inner Frobenius factor `ord_∞((r'π)^* x) = q·(-2)` needs separable `[r']`); for
  `p ∣ r'` the summand decomposition gives only `ord_∞ < 0` (`ordAtInfty_mulByInt_x_neg`), not the
  exact `-2` the separable whole pencil has.  Closing this needs the **inseparable** division-polynomial
  pole computation (the inseparable `natDegree (ΨSq r')`) or a general "separable isogeny ⟹ unramified
  at `O`" theorem — a substantial separate development.  See its docstring.

`comap_pointValuation_pencil_eq_affine` is now **axiom-clean**; `pencilScaling_holds` carries `sorryAx`
only through the single `p ∣ r'` leaf; leaves 1 (`frobeniusScaling_holds`) and 2
(`oneSubFrobeniusScaling_holds`) are axiom-clean.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, I.2 (base change), III.4.10c (unramified
  order-transport), III.5.5 (separability), III.8.6.1 (the scaling).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil IsogenyBaseChangeConcrete HasseWeil.WeilPairing.DivisorPullback

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

/-! ### K-level: the genuine pencil pullback on the generators -/

section KLevel

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

/-- **`(rπ − s)^K.pullback x_gen = addPullback_x_pair (r·π) (mulByInt -s)`**.  The genuine
`genuineIsogSmulSub` is `addIsog` of the pair `(r·π, [−s])`, whose pullback on `x_gen` is the
addition-formula `x`-coordinate `addPullback_x_pair` (`addPullbackAlgHomPair_x_gen_eq`). -/
theorem genuineIsogSmulSub_pullback_x_gen (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (genuineIsogSmulSub W r s hr hs hrK hsK).pullback (HasseWeil.x_gen W) =
      addPullback_x_pair ((frobeniusIsog W).zsmul r) (mulByInt W.toAffine (-s)) := by
  unfold genuineIsogSmulSub genuineIsogSmulSub_of_pole
  rw [addIsog_pullback]
  exact HasseWeil.OpenLemmaPrimitives.addPullbackAlgHomPair_x_gen_eq W _ _

/-- **`(rπ − s)^K.pullback y_gen = addPullback_y_pair (r·π) (mulByInt -s)`**.  The `y`-analogue. -/
theorem genuineIsogSmulSub_pullback_y_gen (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (genuineIsogSmulSub W r s hr hs hrK hsK).pullback (HasseWeil.y_gen W) =
      addPullback_y_pair ((frobeniusIsog W).zsmul r) (mulByInt W.toAffine (-s)) := by
  unfold genuineIsogSmulSub genuineIsogSmulSub_of_pole
  rw [addIsog_pullback]
  exact HasseWeil.OpenLemmaPrimitives.addPullbackAlgHomPair_y_gen_eq W _ _

/-- **`ord_∞((rπ − s)^K.pullback x_gen) = -2`** (K-level). -/
theorem ordAtInfty_genuineIsogSmulSub_pullback_x_gen (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (W_smooth W).ordAtInfty ((genuineIsogSmulSub W r s hr hs hrK hsK).pullback (HasseWeil.x_gen W)) =
      ((-2 : ℤ) : WithTop ℤ) := by
  rw [genuineIsogSmulSub_pullback_x_gen W r s hr hs hrK hsK]
  exact ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg W r s hr hs hrK hsK

/-- **`ord_∞((rπ − s)^K.pullback y_gen) = -3`** (K-level). -/
theorem ordAtInfty_genuineIsogSmulSub_pullback_y_gen (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (W_smooth W).ordAtInfty ((genuineIsogSmulSub W r s hr hs hrK hsK).pullback (HasseWeil.y_gen W)) =
      ((-3 : ℤ) : WithTop ℤ) := by
  rw [genuineIsogSmulSub_pullback_y_gen W r s hr hs hrK hsK]
  exact ord_addPullback_y_pair_zsmul_frobenius_mulByInt_neg W r s hr hs hrK hsK

end KLevel

/-! ### Base-changed: the pullback realisation and the two `K̄` infinity orders -/

section BaseChange

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]

noncomputable local instance instDecEqACPCW : DecidableEq (AlgebraicClosure K) := Classical.decEq _

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]

/-- **The base-changed pencil pullback on `x_gen^{K̄}` realised through `functionFieldMap`**
(the G-004 square, CoordHom-free): `pencilBaseChangePullback x_gen^{K̄} =
functionFieldMap ((rπ − s)^K.pullback x_gen^K)`.  Pure chaining of `functionFieldMap_x_gen` and
`baseChangePullback_functionFieldMap`, exactly as `oneSubFrobeniusPullback_L_x_gen`. -/
theorem pencilBaseChangePullback_x_gen (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK
        (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        ((genuineIsogSmulSub W r' s' hr hs hrK hsK).pullback (HasseWeil.x_gen W)) := by
  rw [pencilBaseChangePullback, ← functionFieldMap_x_gen W (AlgebraicClosure K)]
  exact baseChangePullback_functionFieldMap (⟨W.toAffine⟩ : SmoothPlaneCurve K) (AlgebraicClosure K)
    (genuineIsogSmulSub W r' s' hr hs hrK hsK).pullback (HasseWeil.x_gen W)

/-- **The base-changed pencil pullback on `y_gen^{K̄}` realised through `functionFieldMap`**.  The
`y`-analogue of `pencilBaseChangePullback_x_gen`. -/
theorem pencilBaseChangePullback_y_gen (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK
        (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        ((genuineIsogSmulSub W r' s' hr hs hrK hsK).pullback (HasseWeil.y_gen W)) := by
  rw [pencilBaseChangePullback, ← functionFieldMap_y_gen W (AlgebraicClosure K)]
  exact baseChangePullback_functionFieldMap (⟨W.toAffine⟩ : SmoothPlaneCurve K) (AlgebraicClosure K)
    (genuineIsogSmulSub W r' s' hr hs hrK hsK).pullback (HasseWeil.y_gen W)

/-- **`ord_∞^{K̄}((rπ − s)_{K̄}^* x_gen) = -2`** — the pole of order `2` at `O` over `K̄`.  Chains the
pullback realisation `pencilBaseChangePullback_x_gen`, the discharged order-transport
`ordAtInftyBaseChange_holds`, and the K-level order
`ordAtInfty_genuineIsogSmulSub_pullback_x_gen`. -/
theorem ordAtInfty_pencil_pullback_x_gen (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    (W_smooth (W.baseChange (AlgebraicClosure K))).ordAtInfty
        ((pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
            (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).pullback
            (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)))) =
      ((-2 : ℤ) : WithTop ℤ) := by
  have hbc := ordAtInftyBaseChange_holds W (AlgebraicClosure K)
  rw [pencilIsogBaseChange_pullback, pencilBaseChangePullback_x_gen W r' s' hr hs hrK hsK,
    hbc _
      (fun h0 => by
        have hcoe := ordAtInfty_genuineIsogSmulSub_pullback_x_gen W r' s' hr hs hrK hsK
        rw [(((W_smooth W).ordAtInfty_eq_top_iff _).mpr h0)] at hcoe
        exact WithTop.top_ne_coe hcoe),
    ordAtInfty_genuineIsogSmulSub_pullback_x_gen W r' s' hr hs hrK hsK]

/-- **`ord_∞^{K̄}((rπ − s)_{K̄}^* y_gen) = -3`** — the pole of order `3` at `O` over `K̄`.  The
`y`-analogue of `ordAtInfty_pencil_pullback_x_gen`, using the K-level `y`-order
`ordAtInfty_genuineIsogSmulSub_pullback_y_gen` (= `-3`, built in `AdditionPullback/Frobenius.lean`). -/
theorem ordAtInfty_pencil_pullback_y_gen (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    (W_smooth (W.baseChange (AlgebraicClosure K))).ordAtInfty
        ((pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
            (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).pullback
            (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K)))) =
      ((-3 : ℤ) : WithTop ℤ) := by
  have hbc := ordAtInftyBaseChange_holds W (AlgebraicClosure K)
  rw [pencilIsogBaseChange_pullback, pencilBaseChangePullback_y_gen W r' s' hr hs hrK hsK,
    hbc _
      (fun h0 => by
        have hcoe := ordAtInfty_genuineIsogSmulSub_pullback_y_gen W r' s' hr hs hrK hsK
        rw [(((W_smooth W).ordAtInfty_eq_top_iff _).mpr h0)] at hcoe
        exact WithTop.top_ne_coe hcoe),
    ordAtInfty_genuineIsogSmulSub_pullback_y_gen W r' s' hr hs hrK hsK]

/-! ### The omega-coefficient of `(rπ − s)_{K̄}` (separability datum for the affine comap) -/

/-- **`omegaPullbackCoeff (rπ − s)_{K̄} = algebraMap (−s')`** (CoordHom-free).  The base-changed
omega-coefficient transports *by value* from the K-level `genuineIsogSmulSub` coefficient
`= algebraMap (−s')` (`genuineIsogSmulSub_omegaPullbackCoeff`, the III.5.2 additivity content), via
`omegaPullbackCoeff_baseChangePullback` (the differential analogue of finrank base change) and the
`functionFieldMap`/`algebraMap` coherence.  This is the `≠ 0` separability datum for the affine
comap (`p ∤ s'` ⟹ `−s' ≠ 0`). -/
theorem omegaPullbackCoeff_pencil (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    omegaPullbackCoeff (W.baseChange (AlgebraicClosure K))
        (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
          (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)) =
      algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
        (algebraMap K (AlgebraicClosure K) (-s')) := by
  rw [omegaPullbackCoeff_baseChangePullback W (AlgebraicClosure K)
      (genuineIsogSmulSub W r' s' hr hs hrK hsK)
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK))
      (by rw [pencilIsogBaseChange_pullback]; rfl),
    genuineIsogSmulSub_omegaPullbackCoeff W r' s' hr hs hrK hsK,
    Curves.SmoothPlaneCurve.functionFieldMap_algebraMap_F]
  rw [← IsScalarTower.algebraMap_apply K (AlgebraicClosure K)
    (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField]
  rfl

/-- **`omegaPullbackCoeff (rπ − s)_{K̄} ∈ range (algebraMap K̄ K(E_{K̄}))`** — the constancy datum. -/
theorem omegaPullbackCoeff_pencil_mem_range (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    omegaPullbackCoeff (W.baseChange (AlgebraicClosure K))
        (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
          (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)) ∈
      (algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField).range := by
  rw [omegaPullbackCoeff_pencil W p r r' s' hr hs hrK hsK]
  exact ⟨_, rfl⟩

/-- **`omegaPullbackCoeff (rπ − s)_{K̄} ≠ 0`** — the separability datum (`p ∤ s'` ⟹ `−s' ≠ 0`). -/
theorem omegaPullbackCoeff_pencil_ne_zero (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    omegaPullbackCoeff (W.baseChange (AlgebraicClosure K))
        (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
          (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)) ≠ 0 := by
  rw [omegaPullbackCoeff_pencil W p r r' s' hr hs hrK hsK, Ne, map_eq_zero, map_eq_zero]
  exact neg_ne_zero.mpr hsK

/-! ### The `infinity` and `affineToInfty` fields of `ComapPointValuationWitness` -/

/-- **`InftyOrdTransport (rπ − s)_{K̄}`** — the `infinity` field.  The field-general pinning
`inftyOrdTransport_of_ordAtInfty_x_y` applied to the two `K̄` infinity orders `-2`, `-3`. -/
theorem inftyOrdTransport_pencil (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    DivisorPullback.InftyOrdTransport
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)) :=
  inftyOrdTransport_of_ordAtInfty_x_y (W.baseChange (AlgebraicClosure K))
    (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
      (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK))
    (ordAtInfty_pencil_pullback_x_gen W p r r' s' hr hs hrK hsK)
    (ordAtInfty_pencil_pullback_y_gen W p r r' s' hr hs hrK hsK)

/-- **Kernel-translation invariance for `(rπ − s)_{K̄}`** (Silverman III.4.10c): for
`k ∈ ker(rπ − s)`, the function-field translation `τ_k` fixes the pullback range.  The kernel
specialisation `hcov_of_mapTranslateGenericPoint_canonical` fed the proved Wall A generic-point
covariance `mapTranslateGenericPoint_pencil_canonical`. -/
theorem pencil_hcov_kernel (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0)
    (k : (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
      (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).kernel)
    (z : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) k.val
        ((pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
          (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).pullback z) =
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).pullback z :=
  hcov_of_mapTranslateGenericPoint_canonical (W.baseChange (AlgebraicClosure K))
    (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
      (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK))
    (mapTranslateGenericPoint_pencil_canonical W p r r' s' hr hs hrK hsK) k z

/-- **The infinity comap identity for `(rπ − s)_{K̄}`** — the `affineToInfty` field.  The
field-general translation-invariance trick
`comap_pointValuation_eq_infty_of_ordAtInfty_x_y_of_kernelInvariant` fed the two `K̄` infinity orders
and the kernel-translation invariance `pencil_hcov_kernel`. -/
theorem comap_pointValuation_pencil_eq_infty (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint)
    (hQ : (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAddMonoidHom
        (Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint P) =
          (0 : (W.baseChange (AlgebraicClosure K)).toAffine.Point)) :
    ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P).comap
        (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
          (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).pullback.toRingHom =
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).ordAtInftyValuation :=
  comap_pointValuation_eq_infty_of_ordAtInfty_x_y_of_kernelInvariant
    (W.baseChange (AlgebraicClosure K))
    (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
      (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK))
    (ordAtInfty_pencil_pullback_x_gen W p r r' s' hr hs hrK hsK)
    (ordAtInfty_pencil_pullback_y_gen W p r r' s' hr hs hrK hsK)
    (pencil_hcov_kernel W p r r' s' hr hs hrK hsK) P hQ

/-! ### Comap → generator-residue bridge (reusable), and the `[−s']` per-summand residue

The two helpers below extract the **generator residues** `α^* x_gen ≡ x`, `α^* y_gen ≡ y` from a full
affine-image comap identity `(pointValuation P).comap α^* = pointValuation ⟨x, y⟩` for *any* isogeny
`α` over `K̄`.  Specialised to `α = [−s'] = mulByInt (−s')` via the proved
`comap_pointValuation_mulByInt_eq_affine`, they give the `[−s']`-summand residues for the pencil's
addition decomposition. -/

/-- **Comap → `x`-generator residue.**  From an affine-image comap identity for an isogeny `α` over
`K̄`, the `x`-generator pullback `α^* x_gen` residues to `x` modulo `m_P`.  Apply the comap identity to
`x_gen − x` (which lies in `m_Q`) and push `α^*` through the subtraction. -/
theorem resid_x_gen_of_comap
    (α : Isogeny (W.baseChange (AlgebraicClosure K)).toAffine
      (W.baseChange (AlgebraicClosure K)).toAffine)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x y : AlgebraicClosure K}
    (h_ns : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular x y)
    (hcomap : ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P).comap α.pullback.toRingHom =
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation ⟨x, y, h_ns⟩) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        (α.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x) < 1 := by
  have hval : ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P).comap α.pullback.toRingHom
        (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x) =
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation ⟨x, y, h_ns⟩
        (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x) := by rw [hcomap]
  have heq : α.pullback.toRingHom (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)) -
        algebraMap (AlgebraicClosure K)
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x) =
      α.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) -
        algebraMap (AlgebraicClosure K)
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x := by
    rw [map_sub]; congr 1; exact α.pullback.commutes x
  rw [Valuation.comap_apply, heq] at hval
  rw [hval, HasseWeil.x_gen_sub_const_eq_algebraMap_XClass]
  exact (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
    (C := (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)))
    _ ⟨x, y, h_ns⟩).mpr
    (HasseWeil.XClass_mem_maximalIdealAt (W := W.baseChange (AlgebraicClosure K)) ⟨x, y, h_ns⟩ x rfl)

/-- **Comap → `y`-generator residue.**  The `y`-analogue of `resid_x_gen_of_comap`. -/
theorem resid_y_gen_of_comap
    (α : Isogeny (W.baseChange (AlgebraicClosure K)).toAffine
      (W.baseChange (AlgebraicClosure K)).toAffine)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x y : AlgebraicClosure K}
    (h_ns : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular x y)
    (hcomap : ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P).comap α.pullback.toRingHom =
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation ⟨x, y, h_ns⟩) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        (α.pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y) < 1 := by
  have hval : ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P).comap α.pullback.toRingHom
        (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K)) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y) =
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation ⟨x, y, h_ns⟩
        (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K)) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y) := by rw [hcomap]
  have heq : α.pullback.toRingHom (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K)) -
        algebraMap (AlgebraicClosure K)
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y) =
      α.pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) -
        algebraMap (AlgebraicClosure K)
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y := by
    rw [map_sub]; congr 1; exact α.pullback.commutes y
  rw [Valuation.comap_apply, heq] at hval
  rw [hval]
  exact pointValuation_y_gen_sub_const_lt_one_at_smoothPoint
    (W.baseChange (AlgebraicClosure K)) ⟨x, y, h_ns⟩ y rfl

/-- **The `[−s']` per-summand residues** (both `x` and `y`), via the proved
`comap_pointValuation_mulByInt_eq_affine` and the comap→residue bridges.  For `[−s'](P) = some x₂ y₂`,
the generator pullbacks `[−s']^* x_gen`, `[−s']^* y_gen` residue to `x₂`, `y₂`.  This discharges the
`hx₂`, `hy₂` inputs of `isog_coords_at_affine_of_decomp` for the pencil's second summand. -/
theorem mulByInt_neg_resid_xy (s' : ℤ) (hsK : (s' : K) ≠ 0)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x₂ y₂ : AlgebraicClosure K}
    (h₂ : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular x₂ y₂)
    (hQ₂ : (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s')).toAddMonoidHom
        P.toAffinePoint = Affine.Point.some x₂ y₂ h₂) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        ((mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s')).pullback
          (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x₂) < 1 ∧
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        ((mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s')).pullback
          (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y₂) < 1 := by
  have hsK' : ((-s' : ℤ) : AlgebraicClosure K) ≠ 0 := by
    rw [Int.cast_neg, neg_ne_zero,
      show ((s' : ℤ) : AlgebraicClosure K) =
          algebraMap K (AlgebraicClosure K) ((s' : ℤ) : K) from
        (map_intCast (algebraMap K (AlgebraicClosure K)) s').symm]
    exact fun h => hsK (by exact_mod_cast (map_eq_zero _).mp h)
  have hcomap := comap_pointValuation_mulByInt_eq_affine
    (W := (W.baseChange (AlgebraicClosure K)).toAffine) (-s') hsK' P h₂ hQ₂
  exact ⟨resid_x_gen_of_comap W (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s'))
      P h₂ hcomap,
    resid_y_gen_of_comap W (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s'))
      P h₂ hcomap⟩

/-! ### NEW: the `r·π̄` summand machinery (mulByInt base-change naturality + bespoke `rFrobBaseChange`)

The `r·π̄`-summand residue — the sole remaining geometric residual flagged below — is now built by
mirroring leaf 2's `negFrobBaseChange` technique with `[r']` in place of `neg`.  The linchpin is the
**mulByInt base-change pullback naturality** `(mulByInt^{K̄} m)^* x_gen = functionFieldMap((mulByInt^K m)^* x_gen)`
(via the division-polynomial base-change `WeierstrassCurve.map_Φ`/`map_ΨSq`/`map_ψ`/`map_ω`); from it the
bespoke transparent summand isogeny `rFrobBaseChange r'` (pullback `baseChangePullback ((frobeniusIsog).zsmul r')`,
point map `r'•π̄`) has computable generator residues, and the addition-formula naturality
(`addPullback_x/y_pair_rFrob_mulByInt`) assembles the pencil pullback decomposition.  Feeding the two
per-summand residues (`rFrobBaseChange_resid_xy`, `mulByInt_neg_resid_xy`) through
`isog_coords_at_affine_of_decomp` yielded the two generator residues in the former **secant**
branch (since removed — the affine comap now goes through the transport-to-`O`
`pencil_two_residues`). -/

/-- `coordRingMap` sends `algebraMap K[X] R (W.Φ m)` to `algebraMap K̄[X] R̄ ((W.baseChange).Φ m)`. -/
theorem coordRingMap_algebraMap_Φ (m : ℤ) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).coordRingMap (AlgebraicClosure K)
        (algebraMap (Polynomial K) W.toAffine.CoordinateRing (W.Φ m)) =
      algebraMap (Polynomial (AlgebraicClosure K)) (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing
        ((W.baseChange (AlgebraicClosure K)).Φ m) := by
  change WeierstrassCurve.Affine.CoordinateRing.map W.toAffine (algebraMap K (AlgebraicClosure K))
    (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C (W.Φ m))) = _
  rw [WeierstrassCurve.Affine.CoordinateRing.map_mk]
  rw [show ((Polynomial.C (W.Φ m) : Polynomial (Polynomial K)).map
        (Polynomial.mapRingHom (algebraMap K (AlgebraicClosure K)))) =
        Polynomial.C ((W.baseChange (AlgebraicClosure K)).Φ m) by
      rw [Polynomial.map_C, Polynomial.coe_mapRingHom,
        show (W.baseChange (AlgebraicClosure K)).Φ m
            = (W.map (algebraMap K (AlgebraicClosure K))).Φ m from rfl,
        WeierstrassCurve.map_Φ (W := W) (algebraMap K (AlgebraicClosure K)) m]]
  rfl

/-- `coordRingMap` sends `algebraMap K[X] R (W.ΨSq m)` to the base-changed `ΨSq`. -/
theorem coordRingMap_algebraMap_ΨSq (m : ℤ) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).coordRingMap (AlgebraicClosure K)
        (algebraMap (Polynomial K) W.toAffine.CoordinateRing (W.ΨSq m)) =
      algebraMap (Polynomial (AlgebraicClosure K)) (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing
        ((W.baseChange (AlgebraicClosure K)).ΨSq m) := by
  change WeierstrassCurve.Affine.CoordinateRing.map W.toAffine (algebraMap K (AlgebraicClosure K))
    (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C (W.ΨSq m))) = _
  rw [WeierstrassCurve.Affine.CoordinateRing.map_mk]
  rw [show ((Polynomial.C (W.ΨSq m) : Polynomial (Polynomial K)).map
        (Polynomial.mapRingHom (algebraMap K (AlgebraicClosure K)))) =
        Polynomial.C ((W.baseChange (AlgebraicClosure K)).ΨSq m) by
      rw [Polynomial.map_C, Polynomial.coe_mapRingHom,
        show (W.baseChange (AlgebraicClosure K)).ΨSq m
            = (W.map (algebraMap K (AlgebraicClosure K))).ΨSq m from rfl,
        WeierstrassCurve.map_ΨSq (W := W) (algebraMap K (AlgebraicClosure K)) m]]
  rfl

/-- `coordRingMap` sends `mk (W.ψ m)` to the base-changed `mk (ψ m)`. -/
theorem coordRingMap_mk_ψ (m : ℤ) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).coordRingMap (AlgebraicClosure K)
        (Affine.CoordinateRing.mk W.toAffine (W.ψ m)) =
      Affine.CoordinateRing.mk (W.baseChange (AlgebraicClosure K)).toAffine
        ((W.baseChange (AlgebraicClosure K)).ψ m) := by
  change WeierstrassCurve.Affine.CoordinateRing.map W.toAffine (algebraMap K (AlgebraicClosure K))
    (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (W.ψ m)) = _
  rw [WeierstrassCurve.Affine.CoordinateRing.map_mk,
    show (W.baseChange (AlgebraicClosure K)).ψ m
        = (W.map (algebraMap K (AlgebraicClosure K))).ψ m from rfl,
    WeierstrassCurve.map_ψ (W := W) (algebraMap K (AlgebraicClosure K)) m]
  rfl

/-- `coordRingMap` sends `mk (W.ω m)` to the base-changed `mk (ω m)`. -/
theorem coordRingMap_mk_ω (m : ℤ) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).coordRingMap (AlgebraicClosure K)
        (Affine.CoordinateRing.mk W.toAffine (W.ω m)) =
      Affine.CoordinateRing.mk (W.baseChange (AlgebraicClosure K)).toAffine
        ((W.baseChange (AlgebraicClosure K)).ω m) := by
  change WeierstrassCurve.Affine.CoordinateRing.map W.toAffine (algebraMap K (AlgebraicClosure K))
    (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (W.ω m)) = _
  rw [WeierstrassCurve.Affine.CoordinateRing.map_mk,
    show (W.baseChange (AlgebraicClosure K)).ω m
        = (W.map (algebraMap K (AlgebraicClosure K))).ω m from rfl,
    WeierstrassCurve.map_ω (W := W) (algebraMap K (AlgebraicClosure K)) m]
  rfl

/-- Transport of `Φ_ff` under `functionFieldMap`. -/
theorem functionFieldMap_Φ_ff (m : ℤ) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        (HasseWeil.Φ_ff W m) =
      HasseWeil.Φ_ff (W.baseChange (AlgebraicClosure K)) m := by
  rw [HasseWeil.Φ_ff, HasseWeil.Φ_ff,
    SmoothPlaneCurve.functionFieldMap_algebraMap, coordRingMap_algebraMap_Φ]
  rfl

/-- Transport of `ΨSq_ff` under `functionFieldMap`. -/
theorem functionFieldMap_ΨSq_ff (m : ℤ) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        (HasseWeil.ΨSq_ff W m) =
      HasseWeil.ΨSq_ff (W.baseChange (AlgebraicClosure K)) m := by
  rw [HasseWeil.ΨSq_ff, HasseWeil.ΨSq_ff,
    SmoothPlaneCurve.functionFieldMap_algebraMap, coordRingMap_algebraMap_ΨSq]
  rfl

/-- Transport of `ψ_ff` under `functionFieldMap`. -/
theorem functionFieldMap_ψ_ff (m : ℤ) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        (HasseWeil.ψ_ff W m) =
      HasseWeil.ψ_ff (W.baseChange (AlgebraicClosure K)) m := by
  rw [HasseWeil.ψ_ff, HasseWeil.ψ_ff,
    SmoothPlaneCurve.functionFieldMap_algebraMap, coordRingMap_mk_ψ]
  rfl

/-- Transport of `ω_ff` under `functionFieldMap`. -/
theorem functionFieldMap_ω_ff (m : ℤ) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        (HasseWeil.ω_ff W m) =
      HasseWeil.ω_ff (W.baseChange (AlgebraicClosure K)) m := by
  rw [HasseWeil.ω_ff, HasseWeil.ω_ff,
    SmoothPlaneCurve.functionFieldMap_algebraMap, coordRingMap_mk_ω]
  rfl

/-- **Transport of `mulByInt_x` under `functionFieldMap`** (the x-coordinate base-change). -/
theorem functionFieldMap_mulByInt_x (m : ℤ) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        (HasseWeil.mulByInt_x W m) =
      HasseWeil.mulByInt_x (W.baseChange (AlgebraicClosure K)) m := by
  rw [HasseWeil.mulByInt_x, HasseWeil.mulByInt_x, map_div₀,
    functionFieldMap_Φ_ff, functionFieldMap_ΨSq_ff]
  rfl

/-- **Transport of `mulByInt_y` under `functionFieldMap`** (the y-coordinate base-change). -/
theorem functionFieldMap_mulByInt_y (m : ℤ) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        (HasseWeil.mulByInt_y W m) =
      HasseWeil.mulByInt_y (W.baseChange (AlgebraicClosure K)) m := by
  rw [HasseWeil.mulByInt_y, HasseWeil.mulByInt_y, map_div₀, map_pow,
    functionFieldMap_ω_ff, functionFieldMap_ψ_ff]
  rfl

/-- **mulByInt base-change pullback naturality on `x_gen`**:
`(mulByInt^{K̄} m)^* x_gen^{K̄} = functionFieldMap((mulByInt^K m)^* x_gen)`. -/
theorem mulByInt_baseChange_pullback_x_gen (m : ℤ) (hm : m ≠ 0) :
    (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine m).pullback
        (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        ((mulByInt W.toAffine m).pullback (HasseWeil.x_gen W)) := by
  rw [show HasseWeil.x_gen W =
        algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X) from rfl,
    mulByInt_pullback_x W m hm,
    show HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)) =
        algebraMap (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
          (algebraMap (Polynomial (AlgebraicClosure K))
            (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing Polynomial.X) from rfl,
    mulByInt_pullback_x (W.baseChange (AlgebraicClosure K)) m hm,
    functionFieldMap_mulByInt_x]

/-- **mulByInt base-change pullback naturality on `y_gen`**. -/
theorem mulByInt_baseChange_pullback_y_gen (m : ℤ) (hm : m ≠ 0) :
    (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine m).pullback
        (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        ((mulByInt W.toAffine m).pullback (HasseWeil.y_gen W)) := by
  rw [show HasseWeil.y_gen W =
        algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (AdjoinRoot.root W.toAffine.polynomial) from rfl,
    mulByInt_pullback_y W m hm,
    show HasseWeil.y_gen (W.baseChange (AlgebraicClosure K)) =
        algebraMap (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
          (AdjoinRoot.root (W.baseChange (AlgebraicClosure K)).toAffine.polynomial) from rfl,
    mulByInt_pullback_y (W.baseChange (AlgebraicClosure K)) m hm,
    functionFieldMap_mulByInt_y]


/-! ### Bespoke `r·π̄` summand isogeny over K̄ (transparent pullback) -/



/-- **The base-changed `r·π̄` summand isogeny** `α₁ = rFrobBaseChange r'`.  Pullback is the transparent
base change `baseChangePullback ((frobeniusIsog W).zsmul r').pullback`; point map is `r'•π̄`. -/
noncomputable def rFrobBaseChange (r' : ℤ) :
    HasseWeil.Isogeny (W.baseChange (AlgebraicClosure K)).toAffine
      (W.baseChange (AlgebraicClosure K)).toAffine :=
  Isogeny.mkBaseChange (AlgebraicClosure K)
    (baseChangePullback (⟨W.toAffine⟩ : SmoothPlaneCurve K) (AlgebraicClosure K)
      ((HasseWeil.frobeniusIsog W).zsmul r').pullback)
    (r' • frobeniusHomBaseChange W p r (AlgebraicClosure K))

@[simp] theorem rFrobBaseChange_pullback (r' : ℤ) :
    (rFrobBaseChange W p r r').pullback =
      baseChangePullback (⟨W.toAffine⟩ : SmoothPlaneCurve K) (AlgebraicClosure K)
        ((HasseWeil.frobeniusIsog W).zsmul r').pullback :=
  Isogeny.mkBaseChange_pullback _ _ _

@[simp] theorem rFrobBaseChange_toAddMonoidHom (r' : ℤ) :
    (rFrobBaseChange W p r r').toAddMonoidHom =
      r' • frobeniusHomBaseChange W p r (AlgebraicClosure K) :=
  Isogeny.mkBaseChange_toAddMonoidHom _ _ _

theorem rFrobBaseChange_pullback_functionFieldMap (r' : ℤ) (z : W.toAffine.FunctionField) :
    (rFrobBaseChange W p r r').pullback
        ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K) z) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        (((HasseWeil.frobeniusIsog W).zsmul r').pullback z) := by
  rw [rFrobBaseChange_pullback]
  exact IsogenyBaseChangeConcrete.baseChangePullback_functionFieldMap
    (⟨W.toAffine⟩ : SmoothPlaneCurve K) (AlgebraicClosure K)
    ((HasseWeil.frobeniusIsog W).zsmul r').pullback z

/-! ### The pencil addPullback naturality (base change of `addPullback_x/y_pair`) -/

/-- **`addSlopePair (rFrob) (mulByInt -s') = functionFieldMap(addSlopePair^K ((zsmul r')) (mulByInt -s'))`**.
Mirror of leaf 2's `addSlopePair_id_negFrobBaseChange`, both summands transparent via `functionFieldMap`. -/
theorem addSlopePair_rFrob_mulByInt (r' s' : ℤ) (hs' : s' ≠ 0) :
    addSlopePair (rFrobBaseChange W p r r') (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s')) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        (addSlopePair ((HasseWeil.frobeniusIsog W).zsmul r') (mulByInt W.toAffine (-s'))) := by
  have hs'' : (-s' : ℤ) ≠ 0 := neg_ne_zero.mpr hs'
  rw [addSlopePair, addSlopePair]
  rw [mulByInt_baseChange_pullback_x_gen W (-s') hs'',
    mulByInt_baseChange_pullback_y_gen W (-s') hs'',
    ← IsogenyBaseChangeConcrete.functionFieldMap_x_gen W (AlgebraicClosure K),
    ← IsogenyBaseChangeConcrete.functionFieldMap_y_gen W (AlgebraicClosure K),
    rFrobBaseChange_pullback_functionFieldMap W p r r' (HasseWeil.x_gen W),
    rFrobBaseChange_pullback_functionFieldMap W p r r' (HasseWeil.y_gen W)]
  rw [← W_KE_map_functionFieldMap W]
  exact WeierstrassCurve.Affine.map_slope (W := W_KE W)
    ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K))
    (((HasseWeil.frobeniusIsog W).zsmul r').pullback (HasseWeil.x_gen W))
    ((mulByInt W.toAffine (-s')).pullback (HasseWeil.x_gen W))
    (((HasseWeil.frobeniusIsog W).zsmul r').pullback (HasseWeil.y_gen W))
    ((mulByInt W.toAffine (-s')).pullback (HasseWeil.y_gen W))

/-- **`addPullback_x_pair (rFrob) (mulByInt -s') = functionFieldMap(addPullback_x_pair^K ...)`**. -/
theorem addPullback_x_pair_rFrob_mulByInt (r' s' : ℤ) (hs' : s' ≠ 0) :
    addPullback_x_pair (rFrobBaseChange W p r r') (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s')) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        (addPullback_x_pair ((HasseWeil.frobeniusIsog W).zsmul r') (mulByInt W.toAffine (-s'))) := by
  have hs'' : (-s' : ℤ) ≠ 0 := neg_ne_zero.mpr hs'
  rw [addPullback_x_pair, addPullback_x_pair, addSlopePair_rFrob_mulByInt W p r r' s' hs',
    mulByInt_baseChange_pullback_x_gen W (-s') hs'',
    ← IsogenyBaseChangeConcrete.functionFieldMap_x_gen W (AlgebraicClosure K),
    rFrobBaseChange_pullback_functionFieldMap W p r r' (HasseWeil.x_gen W),
    ← W_KE_map_functionFieldMap W]
  exact WeierstrassCurve.Affine.map_addX (W' := W_KE W)
    ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K))
    (((HasseWeil.frobeniusIsog W).zsmul r').pullback (HasseWeil.x_gen W))
    ((mulByInt W.toAffine (-s')).pullback (HasseWeil.x_gen W))
    (addSlopePair ((HasseWeil.frobeniusIsog W).zsmul r') (mulByInt W.toAffine (-s')))

/-- **`addPullback_y_pair (rFrob) (mulByInt -s') = functionFieldMap(addPullback_y_pair^K ...)`**. -/
theorem addPullback_y_pair_rFrob_mulByInt (r' s' : ℤ) (hs' : s' ≠ 0) :
    addPullback_y_pair (rFrobBaseChange W p r r') (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s')) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K)
        (addPullback_y_pair ((HasseWeil.frobeniusIsog W).zsmul r') (mulByInt W.toAffine (-s'))) := by
  have hs'' : (-s' : ℤ) ≠ 0 := neg_ne_zero.mpr hs'
  rw [addPullback_y_pair, addPullback_y_pair, addSlopePair_rFrob_mulByInt W p r r' s' hs',
    mulByInt_baseChange_pullback_x_gen W (-s') hs'',
    ← IsogenyBaseChangeConcrete.functionFieldMap_x_gen W (AlgebraicClosure K),
    ← IsogenyBaseChangeConcrete.functionFieldMap_y_gen W (AlgebraicClosure K),
    rFrobBaseChange_pullback_functionFieldMap W p r r' (HasseWeil.x_gen W),
    rFrobBaseChange_pullback_functionFieldMap W p r r' (HasseWeil.y_gen W),
    ← W_KE_map_functionFieldMap W]
  exact WeierstrassCurve.Affine.map_addY (W' := W_KE W)
    (f := (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap (AlgebraicClosure K))
    (x₁ := ((HasseWeil.frobeniusIsog W).zsmul r').pullback (HasseWeil.x_gen W))
    (x₂ := (mulByInt W.toAffine (-s')).pullback (HasseWeil.x_gen W))
    (y₁ := ((HasseWeil.frobeniusIsog W).zsmul r').pullback (HasseWeil.y_gen W))
    (ℓ := addSlopePair ((HasseWeil.frobeniusIsog W).zsmul r') (mulByInt W.toAffine (-s')))


/-! ### `rFrobBaseChange` pullback on generators and point image -/

/-- **K-level**: `((frobeniusIsog).zsmul r')^* x_gen = ((mulByInt r')^* x_gen)^q`. -/
theorem zsmul_frobeniusIsog_pullback_x_gen (r' : ℤ) (hr' : r' ≠ 0) :
    ((HasseWeil.frobeniusIsog W).zsmul r').pullback (HasseWeil.x_gen W) =
      ((mulByInt W.toAffine r').pullback (HasseWeil.x_gen W)) ^ Fintype.card K := by
  rw [Isogeny.zsmul, Isogeny.comp_algebraMap_eq, HasseWeil.frobeniusIsog_pullback_apply]

/-- **K-level**: `((frobeniusIsog).zsmul r')^* y_gen = ((mulByInt r')^* y_gen)^q`. -/
theorem zsmul_frobeniusIsog_pullback_y_gen (r' : ℤ) (hr' : r' ≠ 0) :
    ((HasseWeil.frobeniusIsog W).zsmul r').pullback (HasseWeil.y_gen W) =
      ((mulByInt W.toAffine r').pullback (HasseWeil.y_gen W)) ^ Fintype.card K := by
  rw [Isogeny.zsmul, Isogeny.comp_algebraMap_eq, HasseWeil.frobeniusIsog_pullback_apply]

/-- **`(rFrobBaseChange r')^* x_gen = ((mulByInt^{K̄} r')^* x_gen)^q`** over K̄. -/
theorem rFrobBaseChange_pullback_x_gen (r' : ℤ) (hr' : r' ≠ 0) :
    (rFrobBaseChange W p r r').pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) =
      ((mulByInt (W.baseChange (AlgebraicClosure K)).toAffine r').pullback
        (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)))) ^ Fintype.card K := by
  rw [mulByInt_baseChange_pullback_x_gen W r' hr',
    ← IsogenyBaseChangeConcrete.functionFieldMap_x_gen W (AlgebraicClosure K),
    rFrobBaseChange_pullback_functionFieldMap, zsmul_frobeniusIsog_pullback_x_gen W r' hr',
    map_pow]
  rfl

/-- **`(rFrobBaseChange r')^* y_gen = ((mulByInt^{K̄} r')^* y_gen)^q`** over K̄. -/
theorem rFrobBaseChange_pullback_y_gen (r' : ℤ) (hr' : r' ≠ 0) :
    (rFrobBaseChange W p r r').pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) =
      ((mulByInt (W.baseChange (AlgebraicClosure K)).toAffine r').pullback
        (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K)))) ^ Fintype.card K := by
  rw [mulByInt_baseChange_pullback_y_gen W r' hr',
    ← IsogenyBaseChangeConcrete.functionFieldMap_y_gen W (AlgebraicClosure K),
    rFrobBaseChange_pullback_functionFieldMap, zsmul_frobeniusIsog_pullback_y_gen W r' hr',
    map_pow]
  rfl

/-- **`(card K : K(E_{K̄})) = 0`** — characteristic `p`, `q = p ^ r`.  Used to kill the `Dω` of a
`q`-power (the Frobenius pullback). -/
theorem card_eq_zero_in_functionField (p r : ℕ) [Fact p.Prime] [CharP K p]
    [Fact (Fintype.card K = p ^ r)] :
    ((Fintype.card K : ℕ) : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) = 0 := by
  haveI : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective K (AlgebraicClosure K)) p
  haveI : CharP (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField p :=
    charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective (AlgebraicClosure K)
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) p
  rw [CharP.cast_eq_zero_iff (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField p]
  have hcard : Fintype.card K = p ^ r := Fact.out
  have hr1 : 1 ≤ r := by
    by_contra h
    push_neg at h
    have hr0 : r = 0 := by omega
    rw [hr0, pow_zero] at hcard
    have h2 : 2 ≤ 1 := hcard ▸ (Fintype.one_lt_card (α := K))
    omega
  rw [hcard]; exact dvd_pow_self p (by omega)

/-- **`Dω((rFrobBaseChange r')^* x_gen) = 0`** — the Frobenius `q`-power kills the `ω`-derivative. -/
theorem Dω_rFrobBaseChange_pullback_x_gen (r' : ℤ) (hr' : r' ≠ 0) :
    Dω (W.baseChange (AlgebraicClosure K))
      ((rFrobBaseChange W p r r').pullback
        (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)))) = 0 := by
  rw [rFrobBaseChange_pullback_x_gen W p r r' hr', Dω_pow, card_eq_zero_in_functionField W p r,
    zero_mul, zero_mul]

/-- **`Dω((rFrobBaseChange r')^* y_gen) = 0`** — the `y`-analogue. -/
theorem Dω_rFrobBaseChange_pullback_y_gen (r' : ℤ) (hr' : r' ≠ 0) :
    Dω (W.baseChange (AlgebraicClosure K))
      ((rFrobBaseChange W p r r').pullback
        (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K)))) = 0 := by
  rw [rFrobBaseChange_pullback_y_gen W p r r' hr', Dω_pow, card_eq_zero_in_functionField W p r,
    zero_mul, zero_mul]

/-- **`(rFrobBaseChange r')` on a finite point**: `r'•π̄(some x y) = π̄(r'•(some x y))`. -/
theorem rFrobBaseChange_apply (r' : ℤ) (Q : (W.baseChange (AlgebraicClosure K)).toAffine.Point) :
    (rFrobBaseChange W p r r').toAddMonoidHom Q =
      frobeniusHomBaseChange W p r (AlgebraicClosure K)
        ((mulByInt (W.baseChange (AlgebraicClosure K)).toAffine r').toAddMonoidHom Q) := by
  rw [rFrobBaseChange_toAddMonoidHom, AddMonoidHom.smul_apply, mulByInt_apply,
    map_zsmul]


/-! ### The `r·π̄` per-summand residues -/

/-- **The `r·π̄` per-summand residues** (both `x` and `y`).  Given the `[r']`-image
`(mulByInt^{K̄} r') P = some x₁ y₁`, the generator pullbacks `(rFrobBaseChange r')^* x_gen`,
`^* y_gen` residue to `x₁^q`, `y₁^q` (the coords of `r'•π̄ P = π̄(r'•P) = some (x₁^q) (y₁^q)`).
Via `rFrobBaseChange_pullback_x_gen` (the pullback as `q`-power of the `mulByInt` pullback), the
`[r']`-residue at `P` (from the proved `comap_pointValuation_mulByInt_eq_affine` + the bridges), and
`residPV_pow`. -/
theorem rFrobBaseChange_resid_xy (r' : ℤ) (hr' : r' ≠ 0) (hrK : (r' : K) ≠ 0)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x₁ y₁ : AlgebraicClosure K}
    (h₁ : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular x₁ y₁)
    (hQ₁ : (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine r').toAddMonoidHom
        P.toAffinePoint = Affine.Point.some x₁ y₁ h₁) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        ((rFrobBaseChange W p r r').pullback
          (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (x₁ ^ Fintype.card K)) < 1 ∧
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        ((rFrobBaseChange W p r r').pullback
          (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (y₁ ^ Fintype.card K)) < 1 := by
  have hrK' : ((r' : ℤ) : AlgebraicClosure K) ≠ 0 := by
    rw [show ((r' : ℤ) : AlgebraicClosure K) =
        algebraMap K (AlgebraicClosure K) ((r' : ℤ) : K) from
      (map_intCast (algebraMap K (AlgebraicClosure K)) r').symm]
    exact fun h => hrK (by exact_mod_cast (map_eq_zero _).mp h)
  have hcomap := comap_pointValuation_mulByInt_eq_affine
    (W := (W.baseChange (AlgebraicClosure K)).toAffine) r' hrK' P h₁ hQ₁
  -- The `[r']`-residues at `P`.
  have hx := resid_x_gen_of_comap W (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine r')
    P h₁ hcomap
  have hy := resid_y_gen_of_comap W (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine r')
    P h₁ hcomap
  refine ⟨?_, ?_⟩
  · rw [rFrobBaseChange_pullback_x_gen W p r r' hr']
    exact residPV_pow W hx (Fintype.card K)
  · rw [rFrobBaseChange_pullback_y_gen W p r r' hr']
    exact residPV_pow W hy (Fintype.card K)

/-- **The `r·π̄` per-summand residues, separability-free** (`r' ≠ 0` only, NO `(r' : K) ≠ 0`).  Mirror
of `rFrobBaseChange_resid_xy`, but the inner `[r']`-residue comes from the *geometric* division-poly
value bridge `pointValuation_mulByInt_x/y_sub_lt_one_of_ne_zero` (which needs only `r' ≠ 0`), not from
the separability-gated `comap_pointValuation_mulByInt_eq_affine`.  This is the linchpin for the
**`p ∣ r'`** member, where `[r']` is *inseparable* but its image-coordinate residue still holds. -/
theorem rFrobBaseChange_resid_xy_of_ne_zero (r' : ℤ) (hr' : r' ≠ 0)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x₁ y₁ : AlgebraicClosure K}
    (h₁ : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular x₁ y₁)
    (hQ₁ : (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine r').toAddMonoidHom
        P.toAffinePoint = Affine.Point.some x₁ y₁ h₁) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        ((rFrobBaseChange W p r r').pullback
          (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (x₁ ^ Fintype.card K)) < 1 ∧
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        ((rFrobBaseChange W p r r').pullback
          (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (y₁ ^ Fintype.card K)) < 1 := by
  -- The separability-free `[r']`-residues at `P` (geometric value bridge, `r' ≠ 0` only).  Convert
  -- `mulByInt_x r' = (mulByInt r')^* x_gen` via `mulByInt_pullback_x`.
  have hx : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      ((mulByInt (W.baseChange (AlgebraicClosure K)).toAffine r').pullback
        (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) -
        algebraMap (AlgebraicClosure K)
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x₁) < 1 := by
    have h := pointValuation_mulByInt_x_sub_lt_one_of_ne_zero
      (W := (W.baseChange (AlgebraicClosure K)).toAffine) r' hr' P h₁ hQ₁
    rwa [show HasseWeil.mulByInt_x (W.baseChange (AlgebraicClosure K)) r' =
        (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine r').pullback
          (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) from
      (HasseWeil.mulByInt_pullback_x (W.baseChange (AlgebraicClosure K)) r' hr').symm] at h
  have hy : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      ((mulByInt (W.baseChange (AlgebraicClosure K)).toAffine r').pullback
        (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) -
        algebraMap (AlgebraicClosure K)
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y₁) < 1 := by
    have h := pointValuation_mulByInt_y_sub_lt_one_of_ne_zero
      (W := (W.baseChange (AlgebraicClosure K)).toAffine) r' hr' P h₁ hQ₁
    rwa [show HasseWeil.mulByInt_y (W.baseChange (AlgebraicClosure K)) r' =
        (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine r').pullback
          (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) from
      (HasseWeil.mulByInt_pullback_y (W.baseChange (AlgebraicClosure K)) r' hr').symm] at h
  refine ⟨?_, ?_⟩
  · rw [rFrobBaseChange_pullback_x_gen W p r r' hr']
    exact residPV_pow W hx (Fintype.card K)
  · rw [rFrobBaseChange_pullback_y_gen W p r r' hr']
    exact residPV_pow W hy (Fintype.card K)


/-! ### The pullback decomposition and point-map decomposition for the pencil -/

/-- **The `x`-generator pullback decomposition for `(rπ − s)_{K̄}`**:
`(rπ − s)^* x_gen = addPullback_x_pair (rFrobBaseChange r') (mulByInt (-s'))`. -/
theorem pencil_pullback_x_gen_eq_addPullback_x_pair (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).pullback
        (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) =
      addPullback_x_pair (rFrobBaseChange W p r r')
        (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s')) := by
  rw [pencilIsogBaseChange_pullback, pencilBaseChangePullback_x_gen W r' s' hr hs hrK hsK,
    genuineIsogSmulSub_pullback_x_gen W r' s' hr hs hrK hsK,
    ← addPullback_x_pair_rFrob_mulByInt W p r r' s' hs]

/-- **The `y`-generator pullback decomposition for `(rπ − s)_{K̄}`**. -/
theorem pencil_pullback_y_gen_eq_addPullback_y_pair (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).pullback
        (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) =
      addPullback_y_pair (rFrobBaseChange W p r r')
        (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s')) := by
  rw [pencilIsogBaseChange_pullback, pencilBaseChangePullback_y_gen W r' s' hr hs hrK hsK,
    genuineIsogSmulSub_pullback_y_gen W r' s' hr hs hrK hsK,
    ← addPullback_y_pair_rFrob_mulByInt W p r r' s' hs]

/-- **The point-map decomposition for `(rπ − s)_{K̄}`**:
`(rπ − s) P = (rFrobBaseChange r') P + (mulByInt (-s')) P`. -/
theorem pencil_toAddMonoidHom_decomp (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0)
    (Q : (W.baseChange (AlgebraicClosure K)).toAffine.Point) :
    (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAddMonoidHom Q =
      (rFrobBaseChange W p r r').toAddMonoidHom Q +
        (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s')).toAddMonoidHom Q := by
  rw [pencilIsogBaseChange_toAddMonoidHom, rFrobBaseChange_toAddMonoidHom,
    AddMonoidHom.sub_apply, AddMonoidHom.smul_apply, AddMonoidHom.smul_apply,
    mulByInt_apply, AddMonoidHom.id_apply, neg_smul, sub_eq_add_neg]


/-! ### `rFrobBaseChange` on a finite point (explicit `some` form) -/

/-- **`(rFrobBaseChange r')` on `[r']`-image `some xr yr`**: gives `some (xr^q) (yr^q)`. -/
theorem rFrobBaseChange_apply_some (r' : ℤ)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {xr yr : AlgebraicClosure K}
    (hr1 : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular xr yr)
    (hQr : (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine r').toAddMonoidHom
        P.toAffinePoint = Affine.Point.some xr yr hr1) :
    (rFrobBaseChange W p r r').toAddMonoidHom P.toAffinePoint =
      Affine.Point.some
        ((FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) xr)
        ((FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) yr)
        ((WeierstrassCurve.Affine.baseChange_nonsingular W.toAffine
          (RingHom.injective
            (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)).toRingHom) xr yr).mpr hr1) := by
  rw [rFrobBaseChange_apply, hQr, frobeniusHomBaseChange_apply_some]



/-! ### The affine comap field

The `affine` field of `ComapPointValuationWitness` for `(rπ − s)_{K̄}` is the **`rπ − s` analogue of
`comap_pointValuation_oneSub_eq_affine`** (`OneSubAffineResidues.lean`, ~1300 lines): the
unconditional affine-image comap identity at every smooth point `P` with affine image
`(rπ − s)P = some x y`.  It rests on the general headline `comap_pointValuation_isog_eq_affine`
(+ `_y` for the 2-torsion-image branch), `AdditionPullback/SamePlace.lean`, fed:

* the omega-coefficient `∈ range`/`≠ 0` — **DISCHARGED** (`omegaPullbackCoeff_pencil_mem_range` /
  `omegaPullbackCoeff_pencil_ne_zero` above): `omegaPullbackCoeff (rπ − s)_{K̄} =
  functionFieldMap (algebraMap (−s')) = algebraMap (−s')` (via `omegaPullbackCoeff_baseChangePullback`
  + the K-level `genuineIsogSmulSub_omegaPullbackCoeff`), `algebraMap` of `−s' ≠ 0` (since `p ∤ s'`);
* the **two generator residues** `(rπ − s)^* x_gen ≡ x`, `(rπ − s)^* y_gen ≡ y`, from
  `isog_coords_at_affine_of_decomp` (secant) / `_slope` (doubling) with the summand pair
  `(r·π̄, [−s'])`; and
* the **non-2-torsion / 2-torsion unit** for `e = 1` (x- vs y-uniformizer).

Unlike leaf 2 — where `1 − π = addIsog(id, −π)` has a *trivial* `id` summand and a Frobenius `−π`
summand whose pullback `x_gen^q` residues directly by `residPV_pow` — the pencil
`rπ − s = addIsog(r·π, [−s'])` has **both summands composite** (`r·π = [r]∘π` and `[−s']`).

**Status of the residue infrastructure (this file).**
* The `[−s']`-summand residues are **built** (`mulByInt_neg_resid_xy`, axiom-clean): they go through
  the proved `comap_pointValuation_mulByInt_eq_affine` and the reusable comap→residue bridges
  `resid_x_gen_of_comap` / `resid_y_gen_of_comap`.
* The **`r·π̄`-summand residue is now BUILT** (`rFrobBaseChange_resid_xy`, axiom-clean), exactly by the
  leaf-2 `negFrobBaseChange` template with `[r']` in place of `neg`.  The pieces (all axiom-clean):
  - **(b) the linchpin** `mulByInt_baseChange_pullback_x_gen`/`_y_gen`: the base-change naturality of
    the `mulByInt` pullback `(mulByInt^{K̄} m)^* x_gen = functionFieldMap((mulByInt^K m)^* x_gen)`, via
    the division-polynomial base-change `Φ_ff`/`ΨSq_ff`/`ψ_ff`/`ω_ff` transports
    (`functionFieldMap_Φ_ff` etc.) over `WeierstrassCurve.map_Φ`/`map_ΨSq`/`map_ψ`/`map_ω`;
  - **(a) the bespoke transparent summand isogeny** `rFrobBaseChange r'` (`mkBaseChange`, pullback
    `baseChangePullback ((frobeniusIsog).zsmul r')`, point map `r'•π̄`), with computable generators
    (`rFrobBaseChange_pullback_x_gen` = `((mulByInt^{K̄} r')^* x_gen)^q`) and point image
    (`rFrobBaseChange_apply_some` = `some (xr^q) (yr^q)` on the `[r']`-image `some xr yr`);
  - **(c) the addition-formula naturality** `addSlopePair_rFrob_mulByInt`,
    `addPullback_x/y_pair_rFrob_mulByInt`, and the pullback decomposition
    `pencil_pullback_x/y_gen_eq_addPullback_x/y_pair` + the point-map decomposition
    `pencil_toAddMonoidHom_decomp`.
  (The per-summand addition-formula route through `isog_coords_at_affine_of_decomp` has been
  removed — it was no longer on the critical path.)
* **The affine comap is now `O`-summand-free AND axiom-clean** via the **transport-to-`O`** lemma
  `isog_resid_at_affine_of_hgcomm_hinfty` (canonical generic-point covariance + infinity
  order-transport, **no** addition-formula case split): `pencil_two_residues` calls it directly; the
  former secant / doubling / `O`-summand branches — and the `sorryAx` the doubling branch carried —
  are gone.  `comap_pointValuation_pencil_eq_affine` is axiom-clean.
* **Sole remaining residual (for the off-domain `p ∣ r'` member only)** = the infinity order-transport
  `InftyOrdTransport (rπ − s)_{K̄}` / the exact `∞`-orders `-2`, `-3`, isolated in
  `pencilScalingComapDataCard_pDvdR`.  Everything for the canonical `p ∤ r'` member (the `r·π̄` and
  `[−s']` residues, the transport-to-`O` affine comap, the omega datum, the infinity fields, the
  scaling assembly) is complete and axiom-clean. -/
/-- **General `e=1` (non-2-torsion image) from residues**: for ANY isogeny `α` over K̄ whose
generator pullbacks residue to `x`, `y` at `P` with `2y+a₁x+a₃ ≠ 0`, the differential denominator
`α^*u` is a unit at `P`.  The `α`-agnostic form of leaf 2's `oneSub_alpha_star_u_ord_eq_zero_of_residues`. -/
theorem alpha_star_u_ord_eq_zero_of_residues
    (α : Isogeny (W.baseChange (AlgebraicClosure K)).toAffine
      (W.baseChange (AlgebraicClosure K)).toAffine)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x y : AlgebraicClosure K}
    (hx : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        (α.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x) < 1)
    (hy : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        (α.pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y) < 1)
    (h2tor : 2 * y + (W.baseChange (AlgebraicClosure K)).a₁ * x +
      (W.baseChange (AlgebraicClosure K)).a₃ ≠ 0) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).ord_P P
        (alpha_star_u (W.baseChange (AlgebraicClosure K)) α) = 0 := by
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
    intro h0; rw [h0, Valuation.map_zero] at hunit; exact zero_ne_one hunit
  exact (Curves.SmoothPlaneCurve.ord_P_eq_zero_iff_pointValuation_eq_one
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K))
    hau_ne).mpr hunit

/-- **General `e=1` (2-torsion image) from residues**: the `y`-numerator `α^*ν` is a unit at `P`. -/
theorem alpha_star_polyX_ord_eq_zero_of_residues
    (α : Isogeny (W.baseChange (AlgebraicClosure K)).toAffine
      (W.baseChange (AlgebraicClosure K)).toAffine)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x y : AlgebraicClosure K}
    (h_ns : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular x y)
    (hx : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        (α.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x) < 1)
    (hy : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        (α.pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y) < 1)
    (h2tor : 2 * y + (W.baseChange (AlgebraicClosure K)).a₁ * x +
      (W.baseChange (AlgebraicClosure K)).a₃ = 0) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).ord_P P
        (3 * (α.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)))) ^ 2 +
          2 * algebraMap (AlgebraicClosure K)
              (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
              (W.baseChange (AlgebraicClosure K)).a₂ *
            (α.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)))) +
          algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
              (W.baseChange (AlgebraicClosure K)).a₄ -
          algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
              (W.baseChange (AlgebraicClosure K)).a₁ *
            (α.pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))))) = 0 := by
  have hνQ_ne : 3 * x ^ 2 + 2 * (W.baseChange (AlgebraicClosure K)).a₂ * x + (W.baseChange (AlgebraicClosure K)).a₄ - (W.baseChange (AlgebraicClosure K)).a₁ * y ≠ 0 := by
    intro h0
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
    simp only [map_ofNat, map_add, map_mul, map_sub] <;> ring
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
    intro h0; rw [h0, Valuation.map_zero] at hunit; exact zero_ne_one hunit
  exact (Curves.SmoothPlaneCurve.ord_P_eq_zero_iff_pointValuation_eq_one (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)) hν_ne).mpr hunit

/-! ### General L'Hôpital tangent-slope residue (Frobenius-left summand)

The doubling case `x₁ = x₂` of an addition decomposition `α = addIsog(α₁, α₂)` where the **first**
summand `α₁` has differential-vanishing generator pullbacks (`Dω(α₁^*x_gen) = Dω(α₁^*y_gen) = 0`, the
case of a Frobenius-composed isogeny such as `r·π̄`).  The `K(E)`-secant `addSlopePair α₁ α₂` residues
at `P` to the *tangent* slope `λ = ν(Q)/u(Q)` of the doubling point `Q = some x₁ y₁`.  This is the
isogeny-pair generalisation of leaf 2's `oneSub_addSlopePair_resid_doubling` (where `α₁ = id`,
`α₂ = −π`); here the roles are swapped (`α₁` is the Frobenius-vanishing summand), but the
invariant-differential `L'Hôpital` argument is identical: with `f := α₁^*x − α₂^*x` (a uniformizer at
`P` since `Dω f = −Dω(α₂^*x) = −α₂^*u·a_{α₂}` is a unit) and `g := α₁^*y − α₂^*y`, the function
`φ := g − λ·f` satisfies `Dω φ ≡ 0` and `φ ≡ 0`, both at `P`, so `ord_P φ ≥ 2`, hence
`addSlopePair − λ = φ/f` has `ord_P ≥ 1`. -/
-- The eight `set`-abbreviations (`Wb`, `C`, `nuQ`, `uQ`, `lamC`, `f`, `g`) abstract the deeply nested
-- `W.baseChange (AlgebraicClosure K)` term across the full reverted goal; the `residPV_*`/`Dω`
-- residue API is stated over that literal curve, so the per-step defeq between the `Wb`-folded goal
-- and the literal-form lemmas is intrinsically heavy and exceeds the default budget. Extraction does
-- not reduce it (the folded↔literal defeq is the dominant cost); a true fix needs the residue API
-- generalised to an arbitrary smooth curve. Minimal budget (cost ≈ 4.5M; default 200k).
set_option maxHeartbeats 5000000 in
theorem addSlopePair_resid_tangent_of_DωLeft_zero
    (α₁ α₂ : Isogeny (W.baseChange (AlgebraicClosure K)).toAffine
      (W.baseChange (AlgebraicClosure K)).toAffine)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x₁ y₁ x₂ y₂ : AlgebraicClosure K}
    (hDα₁x : Dω (W.baseChange (AlgebraicClosure K))
      (α₁.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)))) = 0)
    (hDα₁y : Dω (W.baseChange (AlgebraicClosure K))
      (α₁.pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K)))) = 0)
    (hx₁ : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        (α₁.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x₁) < 1)
    (hy₁ : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        (α₁.pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y₁) < 1)
    (hx₂ : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        (α₂.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x₂) < 1)
    (hy₂ : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        (α₂.pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y₂) < 1)
    (hxeq : x₁ = x₂) (hyeq : y₁ = y₂)
    (huQ : 2 * y₁ + (W.baseChange (AlgebraicClosure K)).a₁ * x₁ +
      (W.baseChange (AlgebraicClosure K)).a₃ ≠ 0)
    (hcoeff₂ : omegaPullbackCoeff (W.baseChange (AlgebraicClosure K)) α₂ ∈
      (algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField).range)
    (hcoeff₂_ne : omegaPullbackCoeff (W.baseChange (AlgebraicClosure K)) α₂ ≠ 0)
    (hu₂ : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).ord_P P
        (alpha_star_u (W.baseChange (AlgebraicClosure K)) α₂) = 0) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      (addSlopePair α₁ α₂ -
        algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
          ((3 * x₁ ^ 2 + 2 * (W.baseChange (AlgebraicClosure K)).a₂ * x₁ +
              (W.baseChange (AlgebraicClosure K)).a₄ -
              (W.baseChange (AlgebraicClosure K)).a₁ * y₁) /
            (2 * y₁ + (W.baseChange (AlgebraicClosure K)).a₁ * x₁ +
              (W.baseChange (AlgebraicClosure K)).a₃))) < 1 := by
  revert P hx₁ hy₁ hx₂ hy₂ huQ hu₂
  set Wb := W.baseChange (AlgebraicClosure K) with hWb
  set C := (⟨Wb.toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)) with hC
  intro P hx₁ hy₁ hx₂ hy₂ huQ hu₂
  set nuQ : AlgebraicClosure K := 3 * x₁ ^ 2 + 2 * Wb.a₂ * x₁ + Wb.a₄ - Wb.a₁ * y₁ with hnuQ
  set uQ : AlgebraicClosure K := 2 * y₁ + Wb.a₁ * x₁ + Wb.a₃ with huQ_def
  set lamC : Wb.toAffine.FunctionField :=
    algebraMap (AlgebraicClosure K) Wb.toAffine.FunctionField (nuQ / uQ) with hlamC
  set f : Wb.toAffine.FunctionField :=
    α₁.pullback (HasseWeil.x_gen Wb) - α₂.pullback (HasseWeil.x_gen Wb) with hf
  set g : Wb.toAffine.FunctionField :=
    α₁.pullback (HasseWeil.y_gen Wb) - α₂.pullback (HasseWeil.y_gen Wb) with hg
  -- `Dω f = −α₂^*u·a_{α₂}` (since `Dω(α₁^*x) = 0`), a unit at `P`.
  have hDf : Dω Wb f = -(alpha_star_u Wb α₂ * omegaPullbackCoeff Wb α₂) := by
    rw [hf, Dω_sub, hDα₁x, Dω_isog_pullback_x_gen Wb α₂, zero_sub]
  -- `a_{α₂}` is a nonzero base-field constant; `α₂^*u` a unit ⟹ `Dω f` a unit at `P`.
  obtain ⟨c₂, hc₂⟩ := hcoeff₂
  have hc₂_ne : c₂ ≠ 0 := fun h => hcoeff₂_ne (by rw [h, map_zero] at hc₂; exact hc₂.symm)
  have hDf_ord : C.ord_P P (Dω Wb f) = 0 := by
    rw [hDf, SmoothPlaneCurve.ord_P_neg, C.ord_P_mul, hu₂, ← hc₂,
      C.ord_P_algebraMap_F_of_ne_zero hc₂_ne, add_zero]
  have hu₂_ne0 : alpha_star_u Wb α₂ ≠ 0 := by
    intro h0; rw [h0, C.ord_P_zero] at hu₂; exact (by simp : (⊤ : WithTop ℤ) ≠ 0) hu₂
  -- `f ≠ 0` (its `Dω` is a unit, so `f` is non-constant; in particular nonzero).
  have hDf_ne : Dω Wb f ≠ 0 := by
    rw [hDf]
    exact neg_ne_zero.mpr (mul_ne_zero hu₂_ne0 hcoeff₂_ne)
  have hf_ne : f ≠ 0 := by
    intro h0
    apply hDf_ne
    rw [h0]
    have hz : Dω Wb ((0 : Wb.toAffine.FunctionField) - 0) = Dω Wb 0 - Dω Wb 0 := Dω_sub Wb 0 0
    simpa using hz
  -- `f ≡ x₁ − x₂ = 0` at `P` (the doubling `x₁ = x₂`), so `ord_P f ≥ 1`; with `Dω f` a unit, `= 1`.
  have hf_lt : C.pointValuation P f < 1 := by
    have hstep := residPV_sub W hx₁ hx₂
    rw [hf]
    refine lt_of_eq_of_lt (congrArg _ ?_) hstep
    rw [hxeq, sub_self, map_zero]; ring
  have hf_ord1 : C.ord_P P f = ((1 : ℤ) : WithTop ℤ) := by
    refine le_antisymm ?_ ?_
    · by_contra hlt
      push_neg at hlt
      have h2le : ((2 : ℤ) : WithTop ℤ) ≤ C.ord_P P f := by
        obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp ((C.ord_P_eq_top_iff f).not.mpr hf_ne)
        rw [← hm] at hlt ⊢; rw [WithTop.coe_lt_coe] at hlt; rw [WithTop.coe_le_coe]; omega
      have := one_le_ord_P_Dω_of_two_le Wb hf_ne P h2le
      rw [hDf_ord] at this; exact absurd this (by simp)
    · exact_mod_cast (C.one_le_ord_P_iff_pointValuation_lt_one (P := P) hf_ne).mpr hf_lt
  -- `g ≡ y₁ − y₂ = 0` at `P`.
  have hg_res : C.pointValuation P g < 1 := by
    have hstep := residPV_sub W hy₁ hy₂
    rw [hg]
    refine lt_of_eq_of_lt (congrArg _ ?_) hstep
    rw [hyeq, sub_self, map_zero]; ring
  -- `x_ne` in `K(E)` for `addSlopePair_eq_of_x_ne`.
  have hpb_ne : α₁.pullback (HasseWeil.x_gen Wb) ≠ α₂.pullback (HasseWeil.x_gen Wb) :=
    sub_ne_zero.mp hf_ne
  have hslope_eq : addSlopePair α₁ α₂ = g / f := by rw [addSlopePair_eq_of_x_ne hpb_ne, hf, hg]
  -- `Dω g = −α₂^*ν·a_{α₂}` (since `Dω(α₁^*y) = 0`).
  have hDg : Dω Wb g = -((3 * (α₂.pullback (HasseWeil.x_gen Wb)) ^ 2 +
        2 * algebraMap (AlgebraicClosure K) Wb.toAffine.FunctionField Wb.a₂ *
          (α₂.pullback (HasseWeil.x_gen Wb)) +
        algebraMap (AlgebraicClosure K) Wb.toAffine.FunctionField Wb.a₄ -
        algebraMap (AlgebraicClosure K) Wb.toAffine.FunctionField Wb.a₁ *
          (α₂.pullback (HasseWeil.y_gen Wb))) *
      omegaPullbackCoeff Wb α₂) := by
    rw [hg, Dω_sub, hDα₁y, Dω_isog_pullback_y_gen Wb α₂, zero_sub]
  -- residue of `α₂^*u` to `uQ` (a unit), `α₂^*ν` to `nuQ`.
  have hu₂_resid : C.pointValuation P
      (alpha_star_u Wb α₂ - algebraMap (AlgebraicClosure K) Wb.toAffine.FunctionField uQ) < 1 := by
    rw [alpha_star_u_eq, show HasseWeil.u_gen Wb = 2 * HasseWeil.y_gen Wb +
        algebraMap (AlgebraicClosure K) Wb.toAffine.FunctionField Wb.a₁ * HasseWeil.x_gen Wb +
        algebraMap (AlgebraicClosure K) Wb.toAffine.FunctionField Wb.a₃ from rfl, huQ_def]
    simp only [map_add, map_mul, map_ofNat, AlgHom.commutes]
    have r2 := residPV_const W P (2 : AlgebraicClosure K)
    have ra1 := residPV_const W P Wb.a₁
    have ra3 := residPV_const W P Wb.a₃
    -- `α₂^*u = 2·α₂^*y + a₁·α₂^*x + a₃` residues to `2y₂ + a₁x₂ + a₃ = uQ` (using `x₂=x₁`, `y₂=y₁`).
    have hstep := residPV_add W (residPV_add W (residPV_mul W r2 hy₂) (residPV_mul W ra1 hx₂)) ra3
    rw [hxeq, hyeq]
    refine lt_of_eq_of_lt (congrArg _ ?_) hstep
    simp only [map_ofNat, map_add, map_mul]; ring
  -- `φ := g − λ·f`; show `φ ≡ 0` and `Dω φ ≡ 0` at `P`, then `ord_P φ ≥ 2`.
  set φ : Wb.toAffine.FunctionField := g - lamC * f with hφ
  have hφ_res : C.pointValuation P φ < 1 := by
    rw [hφ]
    have hlamf : C.pointValuation P (lamC * f) < 1 := by
      rw [hlamC]
      exact pointValuation_mul_lt_one_of_le_and_lt Wb P
        (C.pointValuation_algebraMap_F_le_one P (nuQ / uQ)) hf_lt
    exact lt_of_le_of_lt ((C.pointValuation P).map_sub _ _) (max_lt hg_res hlamf)
  have hDφ_res : C.pointValuation P (Dω Wb φ) < 1 := by
    have hDlamC : Dω Wb lamC = 0 := by rw [hlamC]; exact Dω_algebraMap _ _
    have hDφ_eq : Dω Wb φ = Dω Wb g - lamC * Dω Wb f := by
      rw [hφ, Dω_sub, Dω_mul, hDlamC]; ring
    rw [hDφ_eq, hDg, hDf]
    -- `Dω g = −α₂^*ν·a`, `Dω f = −α₂^*u·a`; `λ = nuQ/uQ`; both residue terms cancel.
    -- `−α₂^*ν·a − λ·(−α₂^*u·a) = −a·(α₂^*ν − λ·α₂^*u) ≡ −a·(nuQ − (nuQ/uQ)·uQ) = 0`.
    have hν₂_resid : C.pointValuation P
        ((3 * (α₂.pullback (HasseWeil.x_gen Wb)) ^ 2 +
            2 * algebraMap (AlgebraicClosure K) Wb.toAffine.FunctionField Wb.a₂ *
              (α₂.pullback (HasseWeil.x_gen Wb)) +
            algebraMap (AlgebraicClosure K) Wb.toAffine.FunctionField Wb.a₄ -
            algebraMap (AlgebraicClosure K) Wb.toAffine.FunctionField Wb.a₁ *
              (α₂.pullback (HasseWeil.y_gen Wb))) -
          algebraMap (AlgebraicClosure K) Wb.toAffine.FunctionField nuQ) < 1 := by
      have r3 := residPV_const W P (3 : AlgebraicClosure K)
      have ra2 := residPV_const W P Wb.a₂
      have ra4 := residPV_const W P Wb.a₄
      have ra1 := residPV_const W P Wb.a₁
      have hstep := residPV_sub W (residPV_add W (residPV_add W
        (residPV_mul W r3 (residPV_pow W hx₂ 2))
        (residPV_mul W (residPV_mul W (residPV_const W P (2 : AlgebraicClosure K)) ra2) hx₂)) ra4)
        (residPV_mul W ra1 hy₂)
      rw [hnuQ, hxeq, hyeq]
      refine lt_of_eq_of_lt (congrArg _ ?_) hstep
      simp only [map_ofNat, map_add, map_mul, map_sub]; ring
    -- Assemble: the whole expression residues to `0`.
    have rlam : C.pointValuation P
        (lamC - algebraMap (AlgebraicClosure K) Wb.toAffine.FunctionField (nuQ / uQ)) < 1 := by
      rw [hlamC, sub_self]; simpa using zero_lt_one
    have rc₂ : C.pointValuation P
        (omegaPullbackCoeff Wb α₂ -
          algebraMap (AlgebraicClosure K) Wb.toAffine.FunctionField c₂) < 1 := by
      rw [hc₂, sub_self]; simpa using zero_lt_one
    -- residue of the big expression to `−(nuQ·c₂) − (nuQ/uQ)·(−(uQ·c₂)) = 0`.
    have hstep := residPV_sub W
      (residPV_neg W (residPV_mul W hν₂_resid rc₂))
      (residPV_mul W rlam (residPV_neg W (residPV_mul W hu₂_resid rc₂)))
    refine lt_of_eq_of_lt (congrArg _ ?_) hstep
    have huQ_ne : uQ ≠ 0 := huQ
    have hval : -(nuQ * c₂) - nuQ / uQ * -(uQ * c₂) = 0 := by
      field_simp
      ring
    rw [hval]
    simp only [map_zero, map_neg, map_mul, map_sub, map_div₀]
    ring
  -- `ord_P φ ≥ 2` (or `φ = 0`), so `addSlopePair − λ = φ/f` has `ord ≥ 1`.
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
    have hdiff_eq : addSlopePair α₁ α₂ - lamC = φ / f := by
      rw [hslope_eq, hφ, eq_comm, sub_div, mul_div_assoc, div_self hf_ne, mul_one]
    have hdiff_ne : addSlopePair α₁ α₂ - lamC ≠ 0 := by
      rw [hdiff_eq]; exact div_ne_zero hφ0 hf_ne
    have hord_diff : ((1 : ℤ) : WithTop ℤ) ≤ C.ord_P P (addSlopePair α₁ α₂ - lamC) := by
      rw [hdiff_eq, div_eq_mul_inv, C.ord_P_mul, C.ord_P_inv _ hf_ne, hf_ord1]
      calc ((1 : ℤ) : WithTop ℤ) = ((2 : ℤ) : WithTop ℤ) + (-((1 : ℤ) : WithTop ℤ)) := rfl
        _ ≤ C.ord_P P φ + (-((1 : ℤ) : WithTop ℤ)) := by gcongr
    rw [hlamC] at hdiff_ne hord_diff
    exact (C.one_le_ord_P_iff_pointValuation_lt_one (P := P) hdiff_ne).mp hord_diff

/-! ### Transport-to-`O` affine residue (genuineness + covariance + infinity transport)

The **`O`-summand-free** affine residue.  For *any* isogeny `φ` over `K̄` carrying the canonical
generic-point covariance (`MapTranslateGenericPoint φ (Point.map φ^*)`, i.e. the translation
covariance `τ_S(φ^*z) = φ^*(τ_{φS}z)`) and the infinity order-transport (`InftyOrdTransport φ`,
`ord_∞(φ^*g) = ord_∞ g`), the two generator pullbacks residue to the image coordinates at *every*
smooth point `P` with affine image `φ P = some x y` — with **no** addition-formula decomposition, so
the `O`-summand degeneracy never arises.

The mechanism is the reviewer's *transport-to-`O`*:
`ord_P P (φ^*(x_gen − x)) = ord_∞(φ^*(τ_R(x_gen − x)))`  (translation covariance with `S = −P`, the
∞-target order-transport `isTranslateOrdAtInftyCompatible`, and `τ_{−R}∘τ_R = id`), then
`= ord_∞(τ_R(x_gen − x))` (`InftyOrdTransport φ`), then `= ord_R(x_gen − x) ≥ 1` (the ∞-source
order-transport + `x_gen − x ∈ m_R`).  Here `R = φ P = some x y`. -/

/-- **The ∞-source order transport** `ord_∞(τ_R f) = ord_R f` for `R = some xR yR` finite and `f ≠ 0`.
The `infinity`-place case of `ordProj_translate_infinity` (`τ_R` carries the order at `∞` to the order
at `O + R = R`). -/
theorem ordAtInfty_translate_eq_ord_P_some
    (xR yR : AlgebraicClosure K)
    (hR : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular xR yR)
    (f : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField)
    (hf : f ≠ 0) :
    (W_smooth (W.baseChange (AlgebraicClosure K))).ordAtInfty
        (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
          (Affine.Point.some xR yR hR) f) =
      (W_smooth (W.baseChange (AlgebraicClosure K))).ord_P ⟨xR, yR, hR⟩ f := by
  have h := HasseWeil.ordProj_translate_infinity (W := W.baseChange (AlgebraicClosure K))
    (Affine.Point.some xR yR hR) f hf ProjectiveSmoothPoint.infinity (Or.inl rfl)
  rw [HasseWeil.ordProj_infinity, HasseWeil.placeTranslate_infinity] at h
  -- `ordProj ((some xR yR hR).toProjectiveSmoothPoint) f = ord_P ⟨xR,yR,hR⟩ f` is `rfl`
  -- (`toProjectiveSmoothPoint_some` + `ordProj_affine`, both definitional).
  exact h

/-- **The transport-to-`O` identity** `ord_P P (φ^*w) = ord_∞(φ^*(τ_R w))` where `R = φ P` is finite
(`= some xR yR`).  Pure translation covariance (`hcomm`, the canonical generic-point leaf via
`hcomm_of_mapTranslateGenericPoint_canonical`) + the ∞-target order-transport
`isTranslateOrdAtInftyCompatible` (at `S = −P`, `P + (−P) = O`) + `τ_{−R}∘τ_R = id`. -/
theorem ord_P_isog_pullback_eq_ordAtInfty_translate
    (φ : Isogeny (W.baseChange (AlgebraicClosure K)).toAffine
      (W.baseChange (AlgebraicClosure K)).toAffine)
    (hgcomm : MapTranslateGenericPoint (W.baseChange (AlgebraicClosure K)) φ
      (WeierstrassCurve.Affine.Point.map (W' := W.baseChange (AlgebraicClosure K)) φ.pullback))
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {xR yR : AlgebraicClosure K}
    (hR : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular xR yR)
    (hQ : φ.toAddMonoidHom P.toAffinePoint = Affine.Point.some xR yR hR)
    (w : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    (W_smooth (W.baseChange (AlgebraicClosure K))).ord_P P (φ.pullback w) =
      (W_smooth (W.baseChange (AlgebraicClosure K))).ordAtInfty
        (φ.pullback (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
          (Affine.Point.some xR yR hR) w)) := by
  -- `S := −P`, so `φ S = −R` and `P + S = O`.  Work with the literal curve throughout.
  have hzero : P.toAffinePoint + (-P.toAffinePoint) =
      (0 : (W.baseChange (AlgebraicClosure K)).toAffine.Point) := add_neg_cancel _
  -- The covariance with `z := τ_R w`: `τ_{−P}(φ^*(τ_R w)) = φ^*(τ_{φ(−P)}(τ_R w))`.
  have hcomm := hcomm_of_mapTranslateGenericPoint_canonical (W.baseChange (AlgebraicClosure K))
    φ hgcomm (-P.toAffinePoint)
      (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
        (Affine.Point.some xR yR hR) w)
  -- `φ(−P) = −R`, so `τ_{φ(−P)}(τ_R w) = τ_{−R}(τ_R w) = τ_{R + (−R)} w = w`.
  have hround : HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
      (φ.toAddMonoidHom (-P.toAffinePoint))
      (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
        (Affine.Point.some xR yR hR) w) = w := by
    rw [map_neg, hQ,
      ← HasseWeil.translateAlgEquivOfPoint_add_apply (W.baseChange (AlgebraicClosure K))
        (Affine.Point.some xR yR hR) (-Affine.Point.some xR yR hR) w, add_neg_cancel]
    rfl
  rw [hround] at hcomm
  -- `hcomm : τ_{−P}(φ^*(τ_R w)) = φ^* w`.
  -- Apply the ∞-target transport at `k = −P` (`P + (−P) = O`) to `g := φ^*(τ_R w)`.
  have htar := isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint
    (W := W.baseChange (AlgebraicClosure K)) P (-P.toAffinePoint) hzero
    (φ.pullback (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
      (Affine.Point.some xR yR hR) w))
  -- `htar : ord_P P (τ_{−P}(φ^*(τ_R w))) = ord_∞(φ^*(τ_R w))`.
  rw [hcomm] at htar
  exact htar

/-- **The transport-to-`O` affine residue** for a genuine separable isogeny `φ` over `K̄`.  For *any*
isogeny `φ` carrying the canonical generic-point covariance `hgcomm` and the infinity transport
`hinfty`, at a smooth point `P` with affine image `φ P = some x y`, the two generator pullbacks
`φ^* x_gen`, `φ^* y_gen` residue to `x`, `y` modulo `m_P`.  **No addition-formula decomposition** — so
this covers the `O`-summand degeneracy uniformly. -/
theorem isog_resid_at_affine_of_hgcomm_hinfty
    (φ : Isogeny (W.baseChange (AlgebraicClosure K)).toAffine
      (W.baseChange (AlgebraicClosure K)).toAffine)
    (hgcomm : MapTranslateGenericPoint (W.baseChange (AlgebraicClosure K)) φ
      (WeierstrassCurve.Affine.Point.map (W' := W.baseChange (AlgebraicClosure K)) φ.pullback))
    (hinfty : DivisorPullback.InftyOrdTransport φ)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x y : AlgebraicClosure K}
    (h_ns : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular x y)
    (hQ : φ.toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        (φ.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x) < 1 ∧
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        (φ.pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y) < 1 := by
  -- Generic single-generator step: for a generator `gen` with `gen − c ≠ 0` and `ord_R (gen − c) ≥ 1`,
  -- the residue `φ^* gen ≡ c` holds.  (No `set` abbreviation — it poisons the dependent `P`/`hQ` types.)
  have step : ∀ (gen : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField)
      (c : AlgebraicClosure K),
      (gen - algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField c) ≠ 0 →
      ((1 : ℤ) : WithTop ℤ) ≤ (W_smooth (W.baseChange (AlgebraicClosure K))).ord_P ⟨x, y, h_ns⟩
        (gen - algebraMap (AlgebraicClosure K)
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField c) →
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
          SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P (φ.pullback gen -
        algebraMap (AlgebraicClosure K)
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField c) < 1 := by
    intro gen c hgc_ne hord_R
    -- abbreviation for the recurring `w := gen − c` (curve kept literal to avoid `set`-poisoning).
    set w := gen - algebraMap (AlgebraicClosure K)
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField c with hw
    -- `φ^* w = φ^* gen − c` (φ^* fixes the constant `c`).
    have hpb_w : φ.pullback w = φ.pullback gen -
        algebraMap (AlgebraicClosure K)
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField c := by
      rw [hw, map_sub]; congr 1; exact φ.pullback.commutes c
    have hpb_w_ne : φ.pullback w ≠ 0 :=
      fun h0 => hgc_ne (φ.pullback_injective (h0.trans (map_zero _).symm))
    -- transport-to-O: `ord_P P (φ^* w) = ord_∞(φ^*(τ_R w))`.
    have htrans := ord_P_isog_pullback_eq_ordAtInfty_translate W φ hgcomm P h_ns hQ w
    -- `τ_R w ≠ 0`, so `φ^*(τ_R w) ≠ 0`.
    have hτw_ne : HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
        (Affine.Point.some x y h_ns) w ≠ 0 :=
      fun h0 => hgc_ne ((HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
        (Affine.Point.some x y h_ns)).injective (h0.trans (map_zero _).symm))
    have hpbτw_ne : φ.pullback (HasseWeil.translateAlgEquivOfPoint
        (W.baseChange (AlgebraicClosure K)) (Affine.Point.some x y h_ns) w) ≠ 0 :=
      fun h0 => hτw_ne (φ.pullback_injective (h0.trans (map_zero _).symm))
    -- `InftyOrdTransport`: `ord_∞(φ^*(τ_R w)) = ord_∞(τ_R w)` (upgrade `.untopD` to `WithTop`).
    -- `InftyOrdTransport` is phrased with `(⟨·⟩ : SmoothPlaneCurve).ordAtInfty`, defeq to `W_smooth`.
    have hinf : WithTop.untopD 0
          ((W_smooth (W.baseChange (AlgebraicClosure K))).ordAtInfty (φ.pullback
            (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
              (Affine.Point.some x y h_ns) w))) =
        WithTop.untopD 0
          ((W_smooth (W.baseChange (AlgebraicClosure K))).ordAtInfty
            (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
              (Affine.Point.some x y h_ns) w)) :=
      hinfty (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
        (Affine.Point.some x y h_ns) w)
    have hinf_top : (W_smooth (W.baseChange (AlgebraicClosure K))).ordAtInfty (φ.pullback
            (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
              (Affine.Point.some x y h_ns) w)) =
        (W_smooth (W.baseChange (AlgebraicClosure K))).ordAtInfty
          (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
            (Affine.Point.some x y h_ns) w) := by
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
        (((W_smooth (W.baseChange (AlgebraicClosure K))).ordAtInfty_eq_top_iff _).not.mpr hpbτw_ne)
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp
        (((W_smooth (W.baseChange (AlgebraicClosure K))).ordAtInfty_eq_top_iff _).not.mpr hτw_ne)
      rw [← hm, ← hn] at hinf ⊢
      rw [WithTop.untopD_coe, WithTop.untopD_coe] at hinf
      rw [hinf]
    -- ∞-source transport: `ord_∞(τ_R w) = ord_R w ≥ 1`.
    have hsrc := ordAtInfty_translate_eq_ord_P_some W x y h_ns w hgc_ne
    -- Chain: `ord_P P (φ^* w) = ord_∞(φ^*(τ_R w)) = ord_∞(τ_R w) = ord_R w ≥ 1`.
    have hord_P : ((1 : ℤ) : WithTop ℤ) ≤
        (W_smooth (W.baseChange (AlgebraicClosure K))).ord_P P (φ.pullback w) := by
      rw [htrans, hinf_top, hsrc]; exact hord_R
    -- convert `ord_P ≥ 1` to `pointValuation < 1`.
    rw [← hpb_w]
    exact (Curves.SmoothPlaneCurve.one_le_ord_P_iff_pointValuation_lt_one
      (C := (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K))) hpb_w_ne).mp
      (by exact_mod_cast hord_P)
  -- Apply `step` to `x_gen, x` and `y_gen, y`, using the `m_R`-membership of `gen − c`.
  refine ⟨step (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) x ?_ ?_,
    step (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) y ?_ ?_⟩
  · rw [HasseWeil.x_gen_sub_const_eq_algebraMap_XClass]
    exact (map_ne_zero_iff _ (IsFractionRing.injective
        (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing _)).mpr
      (Affine.CoordinateRing.XClass_ne_zero (W' := (W.baseChange (AlgebraicClosure K)).toAffine) x)
  · have h_ne : HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)) -
        algebraMap (AlgebraicClosure K)
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x ≠ 0 := by
      rw [HasseWeil.x_gen_sub_const_eq_algebraMap_XClass]
      exact (map_ne_zero_iff _ (IsFractionRing.injective
          (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing _)).mpr
        (Affine.CoordinateRing.XClass_ne_zero (W' := (W.baseChange (AlgebraicClosure K)).toAffine) x)
    refine (Curves.SmoothPlaneCurve.one_le_ord_P_iff_pointValuation_lt_one
      (C := (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K))) h_ne).mpr ?_
    -- `x_gen − x ∈ m_R` (its `XClass` lies in the maximal ideal at `R = ⟨x,y,h_ns⟩`).
    rw [HasseWeil.x_gen_sub_const_eq_algebraMap_XClass]
    exact (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
      (C := (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K))) _ ⟨x, y, h_ns⟩).mpr
      (HasseWeil.XClass_mem_maximalIdealAt (W := W.baseChange (AlgebraicClosure K)) ⟨x, y, h_ns⟩ x rfl)
  · rw [HasseWeil.y_gen_sub_const_eq_algebraMap_YClass]
    exact (map_ne_zero_iff _ (IsFractionRing.injective
        (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing _)).mpr
      (Affine.CoordinateRing.YClass_ne_zero
        (W' := (W.baseChange (AlgebraicClosure K)).toAffine) (Polynomial.C y))
  · have h_ne : HasseWeil.y_gen (W.baseChange (AlgebraicClosure K)) -
        algebraMap (AlgebraicClosure K)
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y ≠ 0 := by
      rw [HasseWeil.y_gen_sub_const_eq_algebraMap_YClass]
      exact (map_ne_zero_iff _ (IsFractionRing.injective
          (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing _)).mpr
        (Affine.CoordinateRing.YClass_ne_zero
          (W' := (W.baseChange (AlgebraicClosure K)).toAffine) (Polynomial.C y))
    refine (Curves.SmoothPlaneCurve.one_le_ord_P_iff_pointValuation_lt_one
      (C := (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K))) h_ne).mpr ?_
    exact HasseWeil.pointValuation_y_gen_sub_const_lt_one_at_smoothPoint
      (W.baseChange (AlgebraicClosure K)) ⟨x, y, h_ns⟩ y rfl

/-! ### The two `∞`-orders from the affine comap at a single finite-image point (Route C)

The **keystone for the `p ∣ r'` member**: for a separable isogeny `φ` over `K̄` carrying the canonical
generic-point covariance `hgcomm`, and a *single* smooth point `P` with finite image `φ(P) = some xR yR`
at which the comap valuation equals `pointValuation ⟨xR,yR⟩` (the value-precise `e = 1` content), the
two `∞`-orders `ord_∞(φ^* x_gen) = -2`, `ord_∞(φ^* y_gen) = -3` follow — **without** any per-summand
addition-formula control, hence valid even when a summand (`r'·π̄` for `p ∣ r'`) is inseparable.

Mechanism (`Route C`): for each generator `gen` (with `ord_∞ gen = -2` resp. `-3`),
`ord_∞(φ^* gen) = ord_P(φ^*(τ_{-R} gen))` (transport-to-`O`, `τ_R ∘ τ_{-R} = id`)
`= ord_R(τ_{-R} gen)` (the comap identity `ord_P(φ^* v) = ord_R v`)
`= ord_∞ gen` (the translation transport `ordProj_translate`, `R + (-R) = O`). -/

/-- `ord_P P (φ^* v) = ord_R v` from the comap identity `(pointValuation P).comap φ^* = pointValuation R`
(both `ord_P`s are the same `if`-formula applied to equal `pointValuation` values). -/
theorem ord_P_isog_pullback_eq_of_comap
    (φ : Isogeny (W.baseChange (AlgebraicClosure K)).toAffine
      (W.baseChange (AlgebraicClosure K)).toAffine)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {xR yR : AlgebraicClosure K}
    (hR : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular xR yR)
    (hcomap : ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P).comap φ.pullback.toRingHom =
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation ⟨xR, yR, hR⟩)
    (v : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    (W_smooth (W.baseChange (AlgebraicClosure K))).ord_P P (φ.pullback v) =
      (W_smooth (W.baseChange (AlgebraicClosure K))).ord_P ⟨xR, yR, hR⟩ v := by
  have hpv : (W_smooth (W.baseChange (AlgebraicClosure K))).pointValuation P (φ.pullback v) =
      (W_smooth (W.baseChange (AlgebraicClosure K))).pointValuation ⟨xR, yR, hR⟩ v := by
    have := congrFun (congrArg DFunLike.coe hcomap) v
    rwa [Valuation.comap_apply] at this
  unfold Curves.SmoothPlaneCurve.ord_P
  rw [hpv]

/-- `ord_R (τ_{-R} gen) = ord_∞ gen` for `R = some xR yR` finite, `gen ≠ 0` — the translation transport
`ordProj_translate` at `v = affine R`, `S = -R` (so `placeTranslate (-R) (affine R) = ∞`). -/
theorem ord_P_translate_neg_eq_ordAtInfty
    (xR yR : AlgebraicClosure K)
    (hR : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular xR yR)
    (gen : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) (hgen : gen ≠ 0) :
    (W_smooth (W.baseChange (AlgebraicClosure K))).ord_P ⟨xR, yR, hR⟩
        (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
          (-(Affine.Point.some xR yR hR)) gen) =
      (W_smooth (W.baseChange (AlgebraicClosure K))).ordAtInfty gen := by
  have h := ordProj_translate (W := W.baseChange (AlgebraicClosure K))
    (-(Affine.Point.some xR yR hR)) gen hgen
    (ProjectiveSmoothPoint.affine ⟨xR, yR, hR⟩)
  -- `placeTranslate (-R) (affine R) = (R + (-R)).toProj = O.toProj = ∞`.
  have hpt : placeTranslate (W.baseChange (AlgebraicClosure K)) (-(Affine.Point.some xR yR hR))
      (ProjectiveSmoothPoint.affine ⟨xR, yR, hR⟩) = ProjectiveSmoothPoint.infinity := by
    rw [placeTranslate_affine,
      show (⟨xR, yR, hR⟩ : (W_smooth (W.baseChange (AlgebraicClosure K))).SmoothPoint).toAffinePoint =
        Affine.Point.some xR yR hR from rfl, add_neg_cancel]
    rfl
  rw [hpt, ordProj_infinity, ordProj_affine] at h
  exact h

/-- **The two `∞`-orders of `φ^* x_gen`, `φ^* y_gen` from the affine comap at a single finite-image
point** (Route C; the keystone for the `p ∣ r'` separable member).  For an isogeny `φ` with canonical
generic-point covariance `hgcomm`, and a smooth point `P` with finite image `φ(P) = some xR yR` at
which the comap valuation is `pointValuation ⟨xR,yR⟩`, the two infinity orders are `-2` and `-3`. -/
theorem ordAtInfty_isog_pullback_x_y_of_comap_at_point
    (φ : Isogeny (W.baseChange (AlgebraicClosure K)).toAffine
      (W.baseChange (AlgebraicClosure K)).toAffine)
    (hgcomm : MapTranslateGenericPoint (W.baseChange (AlgebraicClosure K)) φ
      (WeierstrassCurve.Affine.Point.map (W' := W.baseChange (AlgebraicClosure K)) φ.pullback))
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {xR yR : AlgebraicClosure K}
    (hR : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular xR yR)
    (hQ : φ.toAddMonoidHom P.toAffinePoint = Affine.Point.some xR yR hR)
    (hcomap : ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P).comap φ.pullback.toRingHom =
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation ⟨xR, yR, hR⟩) :
    (W_smooth (W.baseChange (AlgebraicClosure K))).ordAtInfty
        (φ.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)))) =
      ((-2 : ℤ) : WithTop ℤ) ∧
    (W_smooth (W.baseChange (AlgebraicClosure K))).ordAtInfty
        (φ.pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K)))) =
      ((-3 : ℤ) : WithTop ℤ) := by
  -- single-generator step: `ord_∞(φ^* gen) = ord_∞ gen` for any nonzero `gen`.
  have step : ∀ gen : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField, gen ≠ 0 →
      (W_smooth (W.baseChange (AlgebraicClosure K))).ordAtInfty (φ.pullback gen) =
        (W_smooth (W.baseChange (AlgebraicClosure K))).ordAtInfty gen := by
    intro gen hgen
    set R := Affine.Point.some xR yR hR with hRdef
    -- `w := τ_{-R} gen`; transport-to-O gives `ord_P(φ^* w) = ord_∞(φ^*(τ_R w))`, and `τ_R w = gen`.
    have htrans := ord_P_isog_pullback_eq_ordAtInfty_translate W φ hgcomm P hR hQ
      (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) (-R) gen)
    -- `τ_R(τ_{-R} gen) = τ_{-R + R} gen = τ_O gen = gen`.
    have hround : HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) R
        (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) (-R) gen) = gen := by
      rw [← HasseWeil.translateAlgEquivOfPoint_add_apply (W.baseChange (AlgebraicClosure K))
        (-R) R gen, neg_add_cancel]
      rfl
    rw [hround] at htrans
    -- `htrans : ord_P P (φ^*(τ_{-R} gen)) = ord_∞(φ^* gen)`.
    -- comap: `ord_P P (φ^*(τ_{-R} gen)) = ord_R(τ_{-R} gen)`.
    have hcom := ord_P_isog_pullback_eq_of_comap W φ P hR hcomap
      (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) (-R) gen)
    -- translation: `ord_R(τ_{-R} gen) = ord_∞ gen`.
    have htsl := ord_P_translate_neg_eq_ordAtInfty W xR yR hR gen hgen
    rw [← htrans, hcom, htsl]
  refine ⟨?_, ?_⟩
  · rw [step _ (HasseWeil.x_gen_ne_zero (W.baseChange (AlgebraicClosure K)))]
    exact HasseWeil.ordAtInfty_x_gen (W.baseChange (AlgebraicClosure K))
  · rw [step _ (HasseWeil.y_gen_ne_zero (W.baseChange (AlgebraicClosure K)))]
    exact HasseWeil.ordAtInfty_y_gen (W.baseChange (AlgebraicClosure K))

/-- **The two generator residues for `(rπ − s)_{K̄}` at any affine image**, via the **transport-to-`O`**
lemma `isog_resid_at_affine_of_hgcomm_hinfty` (canonical generic-point covariance + infinity
order-transport) — uniformly, with **no** addition-formula case split.  This subsumes the former
secant / doubling / `O`-summand branches (since removed); in particular it is **axiom-clean**,
eliminating the `sorryAx` the former L'Hôpital tangent branch carried. -/
theorem pencil_two_residues (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x y : AlgebraicClosure K}
    (h_ns : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular x y)
    (hQ : (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAddMonoidHom
        P.toAffinePoint = Affine.Point.some x y h_ns) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        ((pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
            (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).pullback
            (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x) < 1 ∧
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        ((pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
            (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).pullback
            (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y) < 1 :=
  isog_resid_at_affine_of_hgcomm_hinfty W
    (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
      (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK))
    (mapTranslateGenericPoint_pencil_canonical W p r r' s' hr hs hrK hsK)
    (inftyOrdTransport_pencil W p r r' s' hr hs hrK hsK)
    P h_ns hQ

theorem comap_pointValuation_pencil_eq_affine (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x y : AlgebraicClosure K}
    (h_ns : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular x y)
    (hQ : (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAddMonoidHom
        P.toAffinePoint = Affine.Point.some x y h_ns) :
    ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P).comap
        (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
          (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).pullback.toRingHom =
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation ⟨x, y, h_ns⟩ := by
    obtain ⟨hx, hy⟩ := pencil_two_residues W p r r' s' hr hs hrK hsK P h_ns hQ
    by_cases h2tor : 2 * y + (W.baseChange (AlgebraicClosure K)).a₁ * x +
        (W.baseChange (AlgebraicClosure K)).a₃ = 0
    · exact comap_pointValuation_isog_eq_affine_y
        (omegaPullbackCoeff_pencil_mem_range W p r r' s' hr hs hrK hsK)
        (omegaPullbackCoeff_pencil_ne_zero W p r r' s' hr hs hrK hsK)
        P h_ns hx hy
        (alpha_star_polyX_ord_eq_zero_of_residues W _ P h_ns hx hy h2tor)
    · exact comap_pointValuation_isog_eq_affine
        (omegaPullbackCoeff_pencil_mem_range W p r r' s' hr hs hrK hsK)
        (omegaPullbackCoeff_pencil_ne_zero W p r r' s' hr hs hrK hsK)
        P h_ns hx hy
        (alpha_star_u_ord_eq_zero_of_residues W _ P hx hy h2tor)

/-! ### Assembling the comap witness and `pencilScaling_holds` -/

/-- **The local comap-valuation witnesses `ComapPointValuationWitness` for `(rπ − s)_{K̄}`**, for a
fixed `(r', s')` with `r' ≠ 0`, `p ∤ r'`, `p ∤ s'`.  Assembled from the affine comap identity
`comap_pointValuation_pencil_eq_affine`, the infinity comap identity
`comap_pointValuation_pencil_eq_infty`, and the infinity order-transport `inftyOrdTransport_pencil`. -/
theorem comapPointValuationWitness_pencil (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    ComapPointValuationWitness (W.baseChange (AlgebraicClosure K))
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)) where
  affine := fun P {_x _y} h_ns hQ =>
    comap_pointValuation_pencil_eq_affine W p r r' s' hr hs hrK hsK P h_ns hQ
  affineToInfty := fun P hQ => comap_pointValuation_pencil_eq_infty W p r r' s' hr hs hrK hsK P hQ
  infinity := inftyOrdTransport_pencil W p r r' s' hr hs hrK hsK

/-- **Finiteness of `ker (rπ − s)_{K̄}`** (PROVED, axiom-clean), via the **trace-free / dual-free**
finite-dimensionality route `HasseWeil.finite_kernel_of_hcov` (Silverman III.4.10a/c).  The
function-field extension `K(E_{K̄}) / (rπ − s)_{K̄}^* K(E_{K̄})` is finite-dimensional
(`isogeny_finiteDimensional`, true for *any* isogeny), so its automorphism group is a `Fintype`; the
injective kernel-translation forward map (needing only the kernel-translation covariance
`pencil_hcov_kernel`, the kernel specialisation of the Wall A generic-point covariance) embeds
`ker (rπ − s)_{K̄}` into that finite group.

This **sidesteps the Frobenius-dual route** `ker(rπ − s) ⊆ E[(rπ̂ − s)∘(rπ − s)]`: that route needs
the integer trace relation `π̄ + V̄ = [a]` over `K̄` (the characteristic polynomial of geometric
Frobenius) together with a geometric Verschiebung `V̄`, **neither of which is available over `K̄`** (no
`FrobeniusCharPolyBaseChange`, no geometric dual of `frobeniusHomBaseChange`).  The finite-dimensional
route avoids both, requiring neither the separable degree match `#ker = deg` nor any dual. -/
theorem pencilIsogBaseChange_finiteKer (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    Finite (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
      (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK)).toAddMonoidHom.ker :=
  HasseWeil.finite_kernel_of_hcov (W.baseChange (AlgebraicClosure K))
    (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
      (pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK))
    (fun k z => pencil_hcov_kernel W p r r' s' hr hs hrK hsK k z)

/-- **The degree-match-free comap bundle `PencilScalingComapDataCard` for `(rπ − s)_{K̄}`**, for a
fixed `(r', s')` with `r' ≠ 0`, `p ∤ r'`, `p ∤ s'`, against the canonical pullback
`pencilBaseChangePullback`.  Carries the proved generic-point covariance
(`pencilScalingComapData_hgcomm_canonical`), the assembled comap witnesses
(`comapPointValuationWitness_pencil`), and kernel finiteness (`pencilIsogBaseChange_finiteKer`). -/
noncomputable def pencilScalingComapDataCard_canonical (r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0)
    (hrK : (r' : K) ≠ 0) (hsK : (s' : K) ≠ 0) :
    PencilScalingComapDataCard W p r r' s' where
  pullback_L := pencilBaseChangePullback W (AlgebraicClosure K) r' s' hr hs hrK hsK
  hgcomm := pencilScalingComapData_hgcomm_canonical W p r r' s' hr hs hrK hsK
  hcomap := comapPointValuationWitness_pencil W p r r' s' hr hs hrK hsK
  finiteKer := pencilIsogBaseChange_finiteKer W p r r' s' hr hs hrK hsK

/-! ### Handling all `(r', s')` including the edge cases `r' = 0`, `p ∣ r'`, `p ∣ s'`

`PencilScaling` quantifies over **every** `(r', s') : ℤ` with `p ∤ s'`, and the δ-free reduction
`pencilScaling_of_comapData_card` needs a `PencilScalingComapDataCard` bundle for **every** `(r', s')`
(to even *state* the `pencilKerCard` exponent function totally).  The bundles split:

* **canonical domain** `r' ≠ 0 ∧ (r' : K) ≠ 0 ∧ (s' : K) ≠ 0` (i.e. `p ∤ r', s'`): the genuine
  `genuineIsogSmulSub` is constructed and `pencilScalingComapDataCard_canonical` applies;
* **edge / off-domain pairs** (`r' = 0`, or `p ∣ r'`, or `p ∣ s'`): the genuine pencil construction
  `pencilBaseChangePullback` needs `(r' : K), (s' : K) ≠ 0`, so it is not available; a bundle for these
  is isolated as the named `pencilScalingComapDataCard_edge` (the `r' = 0` case is a pure
  `mulByInt [−s']` whose comap witness *is* the proved `comapPointValuationWitness_mulByInt`; the
  `p ∣ r'` / `p ∣ s'` cases are the inseparable/vacuous off-domain pairs).

This isolates the off-domain bundle alongside the two genuine geometric residuals (affine comap,
`finiteKer`); all other content of this file is complete and axiom-clean. -/

/-- **`pencilIsogBaseChange 0 s' ((mulByInt (−s'))^*) = mulByInt (−s')`** as isogenies.  For `r' = 0`
the pencil point map is `0·π̄ − s'·id = (−s')·id = [−s'].toAddMonoidHom`, and the pullback is chosen to
be `(mulByInt (−s'))^*`, so both structure fields agree. -/
theorem pencilIsogBaseChange_rZero_eq_mulByInt (s' : ℤ) :
    pencilIsogBaseChange W p r (AlgebraicClosure K) 0 s'
        (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s')).pullback =
      mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s') := by
  have hhom : (pencilIsogBaseChange W p r (AlgebraicClosure K) 0 s'
      (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s')).pullback).toAddMonoidHom =
      (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s')).toAddMonoidHom := by
    rw [pencilIsogBaseChange_toAddMonoidHom]
    ext P
    simp [zero_smul, neg_smul]
  -- `pencilIsogBaseChange 0 s' pb = ⟨pb, 0·π̄ − s'·id⟩` literally; rewrite its hom field to
  -- `(mulByInt (−s')).toAddMonoidHom` and recombine via structure eta.
  show (⟨(mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s')).pullback,
      (pencilIsogBaseChange W p r (AlgebraicClosure K) 0 s'
        (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s')).pullback).toAddMonoidHom⟩ :
      Isogeny _ _) = _
  rw [hhom]

/-- **The canonical-action `[m]` generic-point covariance leaf** over `K̄`.  Converts
`mapTranslateGenericPoint_mulByInt` (the `zsmulPointHom` action) to the **canonical** action
`Point.map (mulByInt m)^*` required by `PencilScalingComapDataCard.hgcomm`, using that both genuine
actions agree on the generic point (`map_pullback_genericPoint`: `Point.map [m]^* P_gen = m • P_gen =
(zsmulPointHom m) P_gen`). -/
theorem mapTranslateGenericPoint_mulByInt_canonical (m : ℤ) (hm : m ≠ 0) :
    MapTranslateGenericPoint (W.baseChange (AlgebraicClosure K))
      (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine m)
      (WeierstrassCurve.Affine.Point.map (W' := W.baseChange (AlgebraicClosure K))
        (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine m).pullback) := by
  -- `[m]` is genuine with the geometric action `zsmulPointHom m` (Fintype-free, replicating
  -- `mulByInt_isGenuineWith` from the field-general `zsmul_genericPoint_eq` + `mulByInt_pullback_x/y`).
  have hgenuine : HasseWeil.IsGenuineWith (W.baseChange (AlgebraicClosure K))
      (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine m)
      (zsmulPointHom (W.baseChange (AlgebraicClosure K)) m) := by
    obtain ⟨hns, hsmul⟩ := HasseWeil.zsmul_genericPoint_eq (W.baseChange (AlgebraicClosure K)) m hm
    refine ⟨HasseWeil.mulByInt_x (W.baseChange (AlgebraicClosure K)) m,
      HasseWeil.mulByInt_y (W.baseChange (AlgebraicClosure K)) m, hns, ?_, ?_, ?_⟩
    · rw [show zsmulPointHom (W.baseChange (AlgebraicClosure K)) m
          (HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K))) =
            m • HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K)) from rfl]
      exact Subsingleton.elim (HasseWeil.instDecidableEqFunctionField (W.baseChange (AlgebraicClosure K)))
        FractionRing.instDecidableEq ▸ hsmul
    · exact (HasseWeil.mulByInt_pullback_x (W.baseChange (AlgebraicClosure K)) m hm).symm
    · exact (HasseWeil.mulByInt_pullback_y (W.baseChange (AlgebraicClosure K)) m hm).symm
  -- Convert the `zsmulPointHom`-action covariance `mapTranslateGenericPoint_mulByInt` to the
  -- canonical `Point.map [m]^*` action via the genuine bridge.
  exact mapTranslateGenericPoint_canonical_of_genuine (W.baseChange (AlgebraicClosure K))
    (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine m) hgenuine
    (mapTranslateGenericPoint_mulByInt (W.baseChange (AlgebraicClosure K)) m)

/-- **The `r' = 0` comap bundle** (the pure `[−s']` member, `p ∤ s'`).  The pencil hom for `r' = 0` is
`0·π̄ − s'·id = [−s']`, and choosing the pullback to be `(mulByInt (−s'))^*` identifies the whole
isogeny with `mulByInt (−s')` (`pencilIsogBaseChange_rZero_eq_mulByInt`) — whose comap witnesses are
the **proved** `comapPointValuationWitness_mulByInt`, generic-point covariance the canonical-action
`mapTranslateGenericPoint_mulByInt_canonical`, and `finiteKer` the trace-free `finite_kernel_of_hcov`
fed the `hcov` derived from that covariance.

`hsbar : ((-s' : ℤ) : K̄) ≠ 0` is the separability datum (`p ∤ s'` ⟹ `−s' ≠ 0` in `K̄`). -/
noncomputable def pencilScalingComapDataCard_rZero (s' : ℤ)
    (hsbar : ((-s' : ℤ) : AlgebraicClosure K) ≠ 0) :
    PencilScalingComapDataCard W p r 0 s' :=
  have hmne : (-s' : ℤ) ≠ 0 := fun h => hsbar (by rw [h]; exact Int.cast_zero)
  { pullback_L := (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s')).pullback
    hgcomm := by
      rw [pencilIsogBaseChange_rZero_eq_mulByInt W p r s']
      exact mapTranslateGenericPoint_mulByInt_canonical W (-s') hmne
    hcomap := by
      rw [pencilIsogBaseChange_rZero_eq_mulByInt W p r s']
      exact DivisorPullback.comapPointValuationWitness_mulByInt
        (W := W.baseChange (AlgebraicClosure K)) (-s') hsbar
    finiteKer := by
      rw [pencilIsogBaseChange_rZero_eq_mulByInt W p r s']
      exact HasseWeil.finite_kernel_of_hcov (W.baseChange (AlgebraicClosure K))
        (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s'))
        (fun k z => hcov_of_mapTranslateGenericPoint_canonical (W.baseChange (AlgebraicClosure K))
          (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine (-s'))
          (mapTranslateGenericPoint_mulByInt_canonical W (-s') hmne) k z) }

/-- **The `p ∣ r'` separable comap bundle** (with `p ∤ s'`, so `(s' : K) = 0` is *false* and the member
`rπ − s` is separable, `a_{rπ−s} = −s' ≠ 0`), the **off-domain** case `(r' : K) = 0` for which the
canonical construction `pencilBaseChangePullback` (needing `(r' : K) ≠ 0`) is unavailable.

**The SOLE remaining residual of the unconditional Hasse bound**, and a genuine geometric gap (not
assembly).  The pencil pullback can be rebuilt over `K̄` through the `rFrobBaseChange r'` summand
(`addIsog (rFrobBaseChange r') (mulByInt (-s'))`, valid for any `r'`), and most of the bundle is then
reachable:

* the **affine comap** field is now `O`-summand-free via the transport-to-`O` lemma
  `isog_resid_at_affine_of_hgcomm_hinfty` (no addition-formula decomposition, so the inseparable-summand
  secant/doubling breakdown is avoided);
* the **generic-point covariance** `hgcomm` is reachable from `addIsog_isGenuineWith` (genuineness of
  the two summands over `K̄`) + the pullback-parametric `mapTranslateGenericPoint_gKbarPencil`;
* `finiteKer` follows from the covariance via `finite_kernel_of_hcov`.

The remaining obstruction is the two `∞`-orders `ord_∞((rπ − s)_{K̄}^* x_gen) = -2`,
`ord_∞(… y_gen) = -3` (the unramifiedness of the *separable* pencil at `O`); from them
`InftyOrdTransport` follows (`inftyOrdTransport_of_ordAtInfty_x_y`) and the whole bundle assembles.

**The `∞`-differential route (Route B) is now ELIMINATED** by the Route C keystone
`ordAtInfty_isog_pullback_x_y_of_comap_at_point` (above, axiom-clean): for any `φ` with the canonical
`hgcomm` and the affine comap identity `(pointValuation P).comap φ^* = pointValuation ⟨xR, yR⟩` at a
*single* smooth point `P` with finite image `φ(P) = some xR yR`, the two `∞`-orders are `-2`, `-3`.  The
mechanism is transport-to-`O` (`ord_P_isog_pullback_eq_ordAtInfty_translate`, needs only `hgcomm`) +
the comap identity (`ord_P_isog_pullback_eq_of_comap`) + the translation transport
(`ord_P_translate_neg_eq_ordAtInfty`).  So **NO `ω`-derivative machinery at `∞` is needed**; the gap
reduces to the comap at *one* finite-image point.

That comap, in turn, needs the two generator residues at `P` (secant branch via the **separability-free**
`rFrobBaseChange_resid_xy_of_ne_zero` + `mulByInt_neg_resid_xy`, both `(r' : K) = 0`-compatible) plus the
`e = 1` datum — all reachable — once the `addIsog (rFrobBaseChange r') (mulByInt (-s'))` is constructed,
which requires the **transcendence/injectivity** of `addPullback_x_pair (rFrobBaseChange r') (mulByInt (-s'))`,
i.e. its pole `ord_∞(addPullback_x_pair (rFrobBaseChange r') (mulByInt (-s'))) < 0`.

**Key fact (verified):** for `p ∣ r'` the two summand `x`-pole orders are *asymmetric*
(`ord_∞((rFrobBaseChange r')^* x) = q·M ≤ -4` with `M = ord_∞(mulByInt_x r') ≤ -2`, vs
`ord_∞((mulByInt (-s'))^* x) = -2`), so the Weierstrass-reduced addition numerator has the **unique**
strictly-dominant term `X₁²·X₂` at order `2qM - 2` (all other reduced terms are strictly less negative,
using `ord_∞(mulByInt_y r') = (3/2)·M`); hence `ord_∞(addPullback_x_pair …) = (2qM - 2) - 2qM = -2`
**exactly**.  This is *not* blocked by the BRIDGE-003 "3-way tie" of `addPullback_x_pair_x_ord_neg`
(`Verschiebung/Genuine.lean`), which is the *symmetric*-pole case.  Closing this requires the inseparable
generalisation of `ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg` (the general `ord_∞(mulByInt_y n)`
+ the reduced-numerator unique-dominant analysis with `M ≤ -2` in place of `-2`) — a substantial but
mechanical mirror.  Isolated here as the single remaining `sorry`. -/
noncomputable def pencilScalingComapDataCard_pDvdR (r' s' : ℤ) (hr : r' ≠ 0)
    (hrK0 : (r' : K) = 0) (hsK : (s' : K) ≠ 0) :
    PencilScalingComapDataCard W p r r' s' := by
  sorry

/-- A `PencilScalingComapDataCard` bundle for a **separable** `(r', s')` (`(s' : K) ≠ 0`, i.e. `p ∤ s'`)
— the canonical bundle when also `r' ≠ 0`, `(r' : K) ≠ 0` (`p ∤ r'`); the `r' = 0` mulByInt bundle when
`r' = 0`; and the `p ∣ r'` separable bundle otherwise.  No `p ∣ s'` (inseparable) case arises. -/
noncomputable def pencilScalingComapDataCard_sep (r' s' : ℤ) (hsK : (s' : K) ≠ 0) :
    PencilScalingComapDataCard W p r r' s' := by
  by_cases hr0 : r' = 0
  · subst hr0
    refine pencilScalingComapDataCard_rZero W p r s' ?_
    rw [Int.cast_neg, neg_ne_zero,
      show ((s' : ℤ) : AlgebraicClosure K) =
          algebraMap K (AlgebraicClosure K) ((s' : ℤ) : K) from
        (map_intCast (algebraMap K (AlgebraicClosure K)) s').symm]
    exact fun h => hsK (by exact_mod_cast (map_eq_zero _).mp h)
  · by_cases hrK : (r' : K) = 0
    · exact pencilScalingComapDataCard_pDvdR W p r r' s' hr0 hrK hsK
    · exact pencilScalingComapDataCard_canonical W p r r' s' hr0
        (by rintro rfl; exact hsK (by push_cast; ring)) hrK hsK

/-- A total junk pullback function (used only to *state* the kernel-cardinality exponent
`pencilKerCard`, whose value is pullback-independent since `(pencilIsogBaseChange …).toAddMonoidHom` is). -/
noncomputable def pencilJunkPullback :
    ℤ → ℤ → ((W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[AlgebraicClosure K]
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :=
  fun _ _ => AlgHom.id (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField

/-- `#ker(rπ − s)_{K̄}` is independent of the chosen base-changed pullback, since the kernel is read off
`toAddMonoidHom = r'·π̄ − s'·id`, which is pullback-independent. -/
theorem pencilKerCard_pullback_indep (r' s' : ℤ)
    (pb₁ pb₂ : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[AlgebraicClosure K]
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    Nat.card (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pb₁).toAddMonoidHom.ker =
      Nat.card (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pb₂).toAddMonoidHom.ker := by
  rw [pencilIsogBaseChange_toAddMonoidHom, pencilIsogBaseChange_toAddMonoidHom]

/-- **`pencilScaling_holds` — leaf 3 of `FrobBaseChangeScalings`** (Silverman III.8.6.1): the
symplectic Weil-pairing scaling `e_ℓ((r·π̄ − s·id) S, (r·π̄ − s·id) T) = e_ℓ(S, T)^{#ker(rπ − s)_{K̄}}`
on `E_{K̄}[ℓ]`, for every separable `(r', s')` (`p ∤ s'`) and prime `ℓ ≠ p`, with the **kernel
cardinality** exponent `pencilKerCard` (against a junk pullback — the value is pullback-independent).

Assembled per separable pair from the bundle `pencilScalingComapDataCard_sep` via
`pencilScaling_one_of_comapData_card`; the **inseparable `p ∣ s'` pairs are excluded vacuously** by the
`PencilScaling` hypothesis `¬(ringChar K) ∣ s'` (with `ringChar K = p`), so no bundle for an
inseparable member — which could not satisfy the `#ker`-exponent scaling — is ever demanded. -/
theorem pencilScaling_holds :
    PencilScaling W p r (AlgebraicClosure K)
      (pencilKerCard W p r (pencilJunkPullback W)) := by
  intro r' s' hps ℓ hℓp hℓne hℓF
  letI : Fact ℓ.Prime := ⟨hℓp⟩
  -- `p ∤ s'`, hence `(s' : K) ≠ 0` (char `p`, `ringChar K = p`).
  have hpchar : ringChar K = p := by rw [ringChar.eq_iff]; infer_instance
  have hsK : (s' : K) ≠ 0 := by
    intro h
    exact hps (by rw [hpchar]; exact (CharP.intCast_eq_zero_iff K p s').mp h)
  -- The separable bundle for `(r', s')`, and the per-pair `#ker`-exponent scaling.
  have hscale := pencilScaling_one_of_comapData_card W p r r' s' ℓ hℓF
    (pencilScalingComapDataCard_sep W p r r' s' hsK)
  rw [show (pencilKerCard W p r (pencilJunkPullback W) r' s').toNat =
      Nat.card (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilScalingComapDataCard_sep W p r r' s' hsK).pullback_L).toAddMonoidHom.ker from by
    rw [pencilKerCard, Int.toNat_natCast]
    exact pencilKerCard_pullback_indep W p r r' s' _ _]
  exact hscale

/-- **`pencilScaling_holds_coprime` — leaf 3 of `FrobBaseChangeScalingsCoprime`** (reviewer round-23,
Route B): the symplectic Weil-pairing scaling
`e_ℓ((r·π̄ − s·id) S, (r·π̄ − s·id) T) = e_ℓ(S, T)^{#ker(rπ − s)_{K̄}}` on `E_{K̄}[ℓ]`, requested only
on the genuine locus `p ∤ r' ∧ p ∤ s'`, with the **kernel cardinality** exponent `pencilKerCard`.

This is the **axiom-clean** pencil leaf.  On `p ∤ r' ∧ p ∤ s'` we have `(r' : K) ≠ 0`, `(s' : K) ≠ 0`
(char `p`), so the member `rπ − s` is genuine and its bundle is the canonical
`pencilScalingComapDataCard_canonical` — which carries **no** `p ∣ r'` `sorry` (cf.
`pencilScalingComapDataCard_pDvdR`, never invoked here).  Hence the inseparable `p ∣ r'` geometric
gap is **dropped** from the bound path. -/
theorem pencilScaling_holds_coprime :
    PencilScalingCoprime W p r (AlgebraicClosure K)
      (pencilKerCard W p r (pencilJunkPullback W)) := by
  intro r' s' hpr hps ℓ hℓp hℓne hℓF
  letI : Fact ℓ.Prime := ⟨hℓp⟩
  -- `p ∤ r'`, `p ∤ s'`, hence `(r' : K) ≠ 0`, `(s' : K) ≠ 0` (char `p`, `ringChar K = p`).
  have hpchar : ringChar K = p := by rw [ringChar.eq_iff]; infer_instance
  have hrK : (r' : K) ≠ 0 := by
    intro h
    exact hpr (by rw [hpchar]; exact (CharP.intCast_eq_zero_iff K p r').mp h)
  have hsK : (s' : K) ≠ 0 := by
    intro h
    exact hps (by rw [hpchar]; exact (CharP.intCast_eq_zero_iff K p s').mp h)
  have hr0 : r' ≠ 0 := by rintro rfl; exact hrK (by push_cast; ring)
  have hs0 : s' ≠ 0 := by rintro rfl; exact hsK (by push_cast; ring)
  -- The canonical genuine bundle for `(r', s')` (NO `p ∣ r'` input), and its `#ker`-exponent scaling.
  have hscale := pencilScaling_one_of_comapData_card W p r r' s' ℓ hℓF
    (pencilScalingComapDataCard_canonical W p r r' s' hr0 hs0 hrK hsK)
  rw [show (pencilKerCard W p r (pencilJunkPullback W) r' s').toNat =
      Nat.card (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s'
        (pencilScalingComapDataCard_canonical W p r r' s' hr0 hs0 hrK hsK).pullback_L).toAddMonoidHom.ker
      from by
    rw [pencilKerCard, Int.toNat_natCast]
    exact pencilKerCard_pullback_indep W p r r' s' _ _]
  exact hscale

end BaseChange

end HasseWeil.WeilPairing

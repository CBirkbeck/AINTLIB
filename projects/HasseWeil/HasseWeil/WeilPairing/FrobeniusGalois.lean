/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.PairingAdjoint
import HasseWeil.WeilPairing.FrobMatrixData

/-!
# The Frobenius Weil-pairing scaling (Silverman III.8.1d), CoordHom-free

This file discharges the leaf `HasseWeil.WeilPairing.FrobeniusScaling` (Silverman III.8.1d, the
Galois/Frobenius equivariance of the Weil pairing) for the `q`-power Frobenius on the base change
`E_{K̄}` of an elliptic curve `E/𝔽_q`, **without** an `Isogeny.CoordHom`.

## Why CoordHom is unavailable

`weilPairing_scaling` (`PairingAdjoint.lean`) needs `ch : φ.CoordHom`, an `L`-algebra hom
`R →ₐ[L] R` on the coordinate ring.  Over `L = K̄` the relevant Frobenius is the **geometric
`q`-power Frobenius** whose function-field pullback sends the generators `x_gen ↦ x_gen^q`,
`y_gen ↦ y_gen^q` (it is `L`-linear but purely inseparable of degree `q`).  Its `picDual`/`CoordHom`
data — which the shipped `weilPairing_scaling` consumes — is not formalised (the concrete
`Isogeny.baseChange`/separable-divisor machinery is absent for the inseparable Frobenius).

## The CoordHom-free route (Silverman III.8.6.1 specialised to Frobenius)

We reuse only `weilPairing_adjoint_core` (`PairingAdjoint.lean`), which takes an isogeny `φ`
together with its two geometric witnesses (translation covariance `hcomm` and the divisor
factorisation `hfact`) **and no `CoordHom`**.  From it:

`weilPairing_scaling_core` (fully proven, axiom-clean) — for any isogeny `φ`, the adjoint at `φT`
plus the dual-point identity `φ̂(φT) = d • T` and second-slot bilinearity give
`e_ℓ(φS, φT) = e_ℓ(S, T) ^ d`.  This is exactly Silverman III.8.6.1 written without `CoordHom`; for
`φ = π` (Frobenius), `d = q = #K`, it is III.8.1d.

`FrobeniusScaling` is then `weilPairing_scaling_core` applied to the base-changed Frobenius
`φ = frobeniusIsog_baseChange_charP_pow`, fed by a single bundled geometric leaf
`FrobeniusScalingWitnesses` carrying, per torsion `S, T`, the covariance `hcomm` and the
factorisation `hfact` (with dual point `U = q • T`).  These are the genuine geometric content of
the Frobenius scaling, carried per isogeny exactly as `DivisorPullback.ProjOrdTransport` /
`PicDual.Naturality` / `HfactLemma.PicDualDivisorClass` are throughout the project.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.8.1 (Prop 8.1d, Galois equivariance),
  III.8.6 (Prop 8.6.1, the symplectic scaling `e_ℓ(φS, φT) = e_ℓ(S,T)^{deg φ}`).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.WeilPairing.TorsionGeometric

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  [IsIntegrallyClosed
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]

local notation "KE" => W.toAffine.FunctionField

section Core

variable [IsAlgClosed F]

/-- **The Weil-pairing scaling, CoordHom-free core** (Silverman III.8.6.1 / III.8.1d).
For an isogeny `φ` of `E` with L-linear pullback (no `CoordHom` needed), `S, T ∈ E[ℓ]`, the
translation-covariance witness `hcomm` (at the point `φT`), the divisor factorisation `hfact`
(at `φT`, with the dual point `U := φ̂(φT)`), and the identification `hdual : U = d • T`
(the dual relation `φ̂ ∘ φ = [d]` at `T`, here with `d = deg φ`):
`e_ℓ(φS, φT) = e_ℓ(S, T) ^ d`.

This mirrors `weilPairing_scaling` but takes the dual point `U` and the exponent `d` abstractly,
so it does **not** require an `Isogeny.CoordHom` / `picDual` (the shipped `weilPairing_scaling`
consumes the separable `picDual` data, which is unavailable for the purely inseparable Frobenius).
Only `φ.pullback`'s `F`-algebra structure (via `weilPairing_adjoint_core`) is used.
The adjoint at `φT` gives `e_ℓ(φS, φT) = e_ℓ(S, U)`; `hdual` rewrites `U = d • T`; the
second-slot power law `weilPairing_nsmul_right` collapses to `e_ℓ(S, T) ^ d`. -/
theorem weilPairing_scaling_core (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (φ : Isogeny W.toAffine W.toAffine) (d : ℕ)
    (S T U : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0)
    (hφS : ℓ • φ.toAddMonoidHom S = 0) (hφT : ℓ • φ.toAddMonoidHom T = 0)
    (hU : ℓ • U = 0)
    (hcomm : translateAlgEquivOfPoint W S
        (φ.pullback (weilFunction W ℓ hℓ (φ.toAddMonoidHom T) hφT)) =
      φ.pullback (translateAlgEquivOfPoint W (φ.toAddMonoidHom S)
        (weilFunction W ℓ hℓ (φ.toAddMonoidHom T) hφT)))
    {c : F} {k : KE}
    (hfact : φ.pullback (weilFunction W ℓ hℓ (φ.toAddMonoidHom T) hφT) =
      algebraMap F KE c *
        (weilFunction W ℓ hℓ U hU *
          (mulByInt W.toAffine ℓ).pullback k))
    (hdual : U = d • T) :
    weilPairing W ℓ hℓ (φ.toAddMonoidHom S) (φ.toAddMonoidHom T) hφS hφT =
      weilPairing W ℓ hℓ S T hS hT ^ d := by
  -- STEP 1: adjoint at `φT`:  `e_ℓ(φS, φT) = e_ℓ(S, U)`.
  rw [weilPairing_adjoint_core W ℓ hℓ φ S (φ.toAddMonoidHom T) U hS hφT hU hφS hcomm hfact]
  -- `ℓ • (d • T) = 0` (the `ℕ`-smul form needed by `weilPairing_nsmul_right`).
  have hdN_tor : ℓ • (d • T) = 0 := smul_nsmul_eq_zero_right W ℓ T hT d
  -- STEP 2: `U = d • T`; rewrite the second slot.
  rw [weilPairing_congr_right W ℓ hℓ hS hU hdN_tor hdual]
  -- STEP 3: the `nsmul`→power law in the second slot.
  exact weilPairing_nsmul_right W ℓ hℓ S T hS hT d hdN_tor

end Core

/-! ### The base-changed Frobenius geometric leaf

`FrobeniusScalingWitnesses` packages, per `ℓ`-torsion `S, T ∈ E_{K̄}[ℓ]`, the two geometric witnesses
that `weilPairing_scaling_core` consumes for the base-changed Frobenius `φ = frobeniusIsog_baseChange_charP_pow`:

* the **translation covariance** `hcomm`: `τ_S(φ^* g_{φT}) = φ^*(τ_{φS} g_{φT})` (the function-field
  shadow of `π ∘ (·+S) = (·+πS) ∘ π` read at the Weil function `g_{φT}`), and
* the **divisor factorisation** `hfact`: `φ^* g_{φT} = c · (g_{q•T} · [ℓ]^* k)` for a constant
  `c ∈ Fˣ` and `k ∈ K(E)`, with the dual point `U = q • T = φ̂(φT)` (Silverman III.6.1 + the
  inseparable divisor-pullback functoriality `div(φ^* h) = φ^*(div h)` pulled back by `[ℓ]`).

This is the genuine geometric content of Silverman III.8.1d for the inseparable Frobenius; it is the
single residual leaf, carried per isogeny exactly as `ProjOrdTransport`/`Naturality`/
`PicDualDivisorClass` are throughout the project. -/

section BaseChange

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

/-- **The base-changed Frobenius geometric leaf** (Silverman III.8.1d / III.8.6.1 content).
For the base-changed `q`-power Frobenius `φ = frobeniusIsog_baseChange_charP_pow p r W L` on `E_{K̄}`,
this bundles, per `ℓ`-torsion `S, T`, the translation covariance `hcomm` and the divisor
factorisation `hfact` (with dual point `U = (#K) • T`) that `weilPairing_scaling_core` consumes.

The covariance and factorisation are the genuine geometric facts about the Frobenius isogeny (the
group-hom commutation `π ∘ (·+S) = (·+πS) ∘ π` and the inseparable divisor-pullback identity
`φ^*((φT) − (O)) ∼ (q•T) − (O)`), carried per isogeny in the project's witness-parametric style. -/
def FrobeniusScalingWitnesses
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic]
    [IsIntegrallyClosed (⟨(W.baseChange L).toAffine⟩ : SmoothPlaneCurve L).CoordinateRing] : Prop :=
  ∀ (ℓ : ℤ) (hℓ : (ℓ : L) ≠ 0)
    (S T : (W.baseChange L).toAffine.Point) (_hS : ℓ • S = 0) (_hT : ℓ • T = 0)
    (hφT : ℓ • (Isogeny.frobeniusIsog_baseChange_charP_pow p r W L).toAddMonoidHom T = 0),
    ∃ (U : (W.baseChange L).toAffine.Point) (hU : ℓ • U = 0) (c : L)
      (k : (W.baseChange L).toAffine.FunctionField),
      (translateAlgEquivOfPoint (W.baseChange L) S
          ((Isogeny.frobeniusIsog_baseChange_charP_pow p r W L).pullback
            (weilFunction (W.baseChange L) ℓ hℓ
              ((Isogeny.frobeniusIsog_baseChange_charP_pow p r W L).toAddMonoidHom T) hφT)) =
        (Isogeny.frobeniusIsog_baseChange_charP_pow p r W L).pullback
          (translateAlgEquivOfPoint (W.baseChange L)
            ((Isogeny.frobeniusIsog_baseChange_charP_pow p r W L).toAddMonoidHom S)
            (weilFunction (W.baseChange L) ℓ hℓ
              ((Isogeny.frobeniusIsog_baseChange_charP_pow p r W L).toAddMonoidHom T) hφT))) ∧
      ((Isogeny.frobeniusIsog_baseChange_charP_pow p r W L).pullback
          (weilFunction (W.baseChange L) ℓ hℓ
            ((Isogeny.frobeniusIsog_baseChange_charP_pow p r W L).toAddMonoidHom T) hφT) =
        algebraMap L (W.baseChange L).toAffine.FunctionField c *
          (weilFunction (W.baseChange L) ℓ hℓ U hU *
            (mulByInt (W.baseChange L).toAffine ℓ).pullback k)) ∧
      U = (Fintype.card K) • T

/-- **The Frobenius Weil-pairing scaling `FrobeniusScaling`** (Silverman III.8.1d), CoordHom-free.
Discharged from the single geometric leaf `FrobeniusScalingWitnesses` via `weilPairing_scaling_core`.

For every prime `ℓ ≠ ringChar K` with `(ℓ : K̄) ≠ 0`, `e_ℓ(π̄ S, π̄ T) = e_ℓ(S, T) ^ (#K)` on
`E_{K̄}[ℓ]`, where `π̄ = frobeniusHomBaseChange` is the `q`-power Frobenius point map and `#K = q` is
its degree.  Unfolding `WeilScales`, this is **exactly** Silverman's Prop III.8.1d. -/
theorem frobeniusScaling_of_witnesses
    (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
    (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p]
    [(W.baseChange L).toAffine.IsElliptic]
    [IsIntegrallyClosed (⟨(W.baseChange L).toAffine⟩ : SmoothPlaneCurve L).CoordinateRing]
    (hwit : FrobeniusScalingWitnesses W p r L) :
    FrobeniusScaling W p r L := by
  intro ℓ hℓp hℓne hℓF
  letI : Fact ℓ.Prime := ⟨hℓp⟩
  -- Unfold `WeilScales`: for all torsion `S T`, `e_ℓ(π̄ S, π̄ T) = e_ℓ(S,T)^{#K}`.
  intro S T
  set φ := Isogeny.frobeniusIsog_baseChange_charP_pow p r W L with hφ
  -- Torsion bookkeeping for `S, T` and their Frobenius images.
  have hS : ((ℓ : ℕ) : ℤ) • S.val = 0 := zsmul_eq_zero_of_mem_torsion (W.baseChange L) ℓ S
  have hT : ((ℓ : ℕ) : ℤ) • T.val = 0 := zsmul_eq_zero_of_mem_torsion (W.baseChange L) ℓ T
  have hφS : ((ℓ : ℕ) : ℤ) • φ.toAddMonoidHom S.val = 0 := by
    rw [← map_zsmul φ.toAddMonoidHom, hS, map_zero]
  have hφT : ((ℓ : ℕ) : ℤ) • φ.toAddMonoidHom T.val = 0 := by
    rw [← map_zsmul φ.toAddMonoidHom, hT, map_zero]
  -- The geometric witnesses for `(S, T)`.
  obtain ⟨U, hU, c, k, hcomm, hfact, hdual⟩ :=
    hwit ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF) S.val T.val hS hT hφT
  -- Apply the CoordHom-free core with `d := #K`.
  exact weilPairing_scaling_core (W.baseChange L) ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF) φ
    (Fintype.card K) S.val T.val U hS hT hφS hφT hU hcomm hfact hdual

end BaseChange

end HasseWeil.WeilPairing

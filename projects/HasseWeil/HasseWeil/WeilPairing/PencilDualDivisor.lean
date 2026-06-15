/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.OneSubDualDivisor
import HasseWeil.WeilPairing.IsogenyBaseChangeConcrete

/-!
# The divisor-pushforward dual of `rπ − s`, and the `PencilScaling` leaf (CoordHom-free)

This file discharges leaf 3 of `FrobBaseChangeScalings` — the leaf
`HasseWeil.WeilPairing.PencilScaling` (`FrobMatrixData.lean`) — the symplectic Weil-pairing scaling

  `e_ℓ((r·π̄ − s·id) S, (r·π̄ − s·id) T) = e_ℓ(S, T)^{deg(rπ − s)}` on `E_{K̄}[ℓ]`,

for the base-changed *separable* pencil `(rπ − s)_{K̄}` over `L = AlgebraicClosure K`, **without**
any `Isogeny.CoordHom` and **without** the characteristic-polynomial / trace relation `π + V = [t]`.

It is the exact mirror of the leaf-2 file `OneSubDualDivisor.lean`: the *general*
divisor-pushforward dual machinery `divisorPushforwardDual` / `divisorPushforwardDual_comp` (built
there for **any** genuine isogeny `φ` with `ProjOrdTransport φ` and surjective point map over `K̄`) and
the
CoordHom-free `WeilScales` bridge `weilScales_of_dualComp` (`SeparableScaling.lean`) are reused
verbatim; only the realising isogeny changes from `1 − π` to `rπ − s`.

## The construction

For the bare hom `ψ = r·π̄ − s·id` named in `PencilScaling`, the realising isogeny is the concrete
base-change

  `pencilIsogBaseChange r s pullback_L := mkBaseChange L pullback_L (r·π̄ − s·id)`

(`Isogeny.mkBaseChange`), whose `toAddMonoidHom` is **by construction** exactly `r·π̄ − s·id`
(`pencilIsogBaseChange_toAddMonoidHom`, `rfl`).  The function-field pullback `pullback_L` is the
base-change of the K-level genuine isogeny `genuineIsogSmulSub`'s pullback through the
function-field scalar extension `K(E_{K̄}) ≅ K(E) ⊗_K L` (the CoordHom-free `baseChangePullback`);
it is carried as a field of the bundled data exactly as `1 − π`'s `pullback_L` is in
`OneSubScalingData`.

The dual is supplied by the **divisor pushforward** `δ = κ ∘ φ^* ∘ κ⁻¹` and the dual relation
`δ ∘ φ = [#ker φ]` is *automatic* via the σ-bridge (Step 4 of `OneSubDualDivisor.lean`) — **no
characteristic polynomial / `π + V = [t]` trace relation, no `CoordHom`**.

## What this file proves vs. carries

* **Proved** (axiom-clean, no `sorry`):
  * the concrete `pencilIsogBaseChange` and its point-map identity (`= r·π̄ − s·id`, `rfl`);
  * the `[ℓ]`-commutation `hcommφ : [ℓ] ∘ φ = φ ∘ [ℓ]` (pure `map_zsmul`, no geometry);
  * `pencilScaling_of_data` / `pencilScaling_of_divisorDual` — `PencilScaling` from the bundled
    data, via the **divisor-pushforward** dual and `weilScales_of_dualComp`.

* **Carried** as the bundled `PencilScalingData` (the genuine CoordHom-free geometric content,
  identical in kind to leaf 2's `OneSubScalingData`, per separable `(r,s)`):
  * `pullback_L` — the base-changed pullback `AlgHom`;
  * `hproj : ProjOrdTransport φ` — divisor-pullback functoriality (also feeds the dual `δ`);
  * `hsurj : Function.Surjective φ` — surjectivity over `K̄` (Silverman III.4.10a);
  * `hkerdeg : #ker φ = deg φ` — the separable degree match (Silverman III.4.10c);
  * `hcomm' : …` — the translation covariance (Silverman III.8.2).

The exponent function `deg` is read off the carried isogeny degree (`deg r s := (φ.degree : ℤ)`);
non-negativity is then free.  This is the same `deg` the Hasse reduction
(`qf_nonneg_of_frob_det_residual`) accepts: the determinant facts pin `deg r s = q·r² − t·rs + s²`
internally (CRT, `deg_eq_of_frob_det_data`), so `deg` needs no external degree formula.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.6.1(b)/III.6.2(a) (the divisor pushforward
  dual + dual relation), III.4.10a/c (surjectivity over `K̄`, separable degree = kernel size),
  III.8.2 (the translation covariance behind the separable adjoint), III.8.6.1 (the symplectic
  scaling `e_ℓ(φS, φT) = e_ℓ(S,T)^{deg φ}`).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.WeilPairing.DivisorPullback HasseWeil.WeilPairing.TorsionGeometric

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

/-! ### The concrete base-changed isogeny `(rπ − s)_{K̄}` -/

section BaseChange

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
variable (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [ExpChar L p]
  [(W.baseChange L).toAffine.IsElliptic]

/-- **The concrete base-changed pencil `(rπ − s)_{K̄}`**.  Built from a base-changed pullback
`pullback_L` and the **concrete** point map `r·π̄ − s·id`, where `π̄ = frobeniusHomBaseChange W p r L`
is the `q`-power Frobenius point map on `E_{K̄}`, via `Isogeny.mkBaseChange`.

Its `toAddMonoidHom` is **definitionally** `r • frobeniusHomBaseChange W p r L - s • AddMonoidHom.id`,
i.e. exactly the bare hom named in `PencilScaling`. -/
noncomputable def pencilIsogBaseChange (r' s' : ℤ)
    (pullback_L : (W.baseChange L).toAffine.FunctionField →ₐ[L]
      (W.baseChange L).toAffine.FunctionField) :
    HasseWeil.Isogeny (W.baseChange L).toAffine (W.baseChange L).toAffine :=
  Isogeny.mkBaseChange L pullback_L
    (r' • frobeniusHomBaseChange W p r L - s' • AddMonoidHom.id (W.baseChange L).toAffine.Point)

@[simp] theorem pencilIsogBaseChange_toAddMonoidHom (r' s' : ℤ)
    (pullback_L : (W.baseChange L).toAffine.FunctionField →ₐ[L]
      (W.baseChange L).toAffine.FunctionField) :
    (pencilIsogBaseChange W p r L r' s' pullback_L).toAddMonoidHom =
      r' • frobeniusHomBaseChange W p r L - s' • AddMonoidHom.id (W.baseChange L).toAffine.Point :=
  Isogeny.mkBaseChange_toAddMonoidHom L _ _

@[simp] theorem pencilIsogBaseChange_pullback (r' s' : ℤ)
    (pullback_L : (W.baseChange L).toAffine.FunctionField →ₐ[L]
      (W.baseChange L).toAffine.FunctionField) :
    (pencilIsogBaseChange W p r L r' s' pullback_L).pullback = pullback_L :=
  Isogeny.mkBaseChange_pullback L _ _

/-- **`[ℓ] ∘ φ_L = φ_L ∘ [ℓ]`** for `φ_L = (rπ − s)_{K̄}` (any base-changed pullback), at the
`AddMonoidHom` level.  Pure `map_zsmul`: both sides send `P ↦ ℓ • (rπ̄ − s·id)(P) = (rπ̄ − s·id)(ℓ • P)`,
because the point map is a group hom. -/
theorem pencilIsogBaseChange_commute_mulByInt (ℓ : ℤ) (r' s' : ℤ)
    (pullback_L : (W.baseChange L).toAffine.FunctionField →ₐ[L]
      (W.baseChange L).toAffine.FunctionField) :
    (mulByInt (W.baseChange L).toAffine ℓ).toAddMonoidHom.comp
        (pencilIsogBaseChange W p r L r' s' pullback_L).toAddMonoidHom =
      (pencilIsogBaseChange W p r L r' s' pullback_L).toAddMonoidHom.comp
        (mulByInt (W.baseChange L).toAffine ℓ).toAddMonoidHom := by
  ext P
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, mulByInt_apply, mulByInt_apply,
    map_zsmul]

end BaseChange

/-! ### The bundled base-change data and the discharge of one `WeilScales` instance

`PencilScalingData` bundles the genuine CoordHom-free geometric residuals for the base-changed
separable isogeny `(rπ − s)_{K̄}`, carried per isogeny exactly as leaf 2's `OneSubScalingData`.
From it, `pencilScaling_of_data` proves a single `WeilScales` instance (for fixed `r', s'`) via the
shipped CoordHom-free `weilScales_of_dualComp` and the divisor-pushforward dual. -/

section Data

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
variable (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p]
  [(W.baseChange L).toAffine.IsElliptic]
  [IsIntegrallyClosed (⟨(W.baseChange L).toAffine⟩ : SmoothPlaneCurve L).CoordinateRing]

/-- **The base-changed `rπ − s` geometric data** (Silverman III.6.1/III.6.2/III.8.2 content),
CoordHom-free.  Bundles, for the base-changed separable isogeny `φ_L = (rπ − s)_{K̄}` whose point map
is the concrete `r·π̄ − s·id`:

* `pullback_L` — the base-changed pullback `AlgHom`;
* `degK` / `hdeg_bc` — the natural degree `φ_L.degree = degK` (degree preservation: `φ_L.degree`
  equals the K-level `genuineIsogSmulSub` degree, the tensor-finrank witness);
* `hproj` — `ProjOrdTransport φ_L` (the multiplicity-free divisor-pullback functoriality, which also
  feeds the divisor-pushforward dual);
* `hsurj` — surjectivity of `φ_L` on `E_{K̄}`-points (Silverman III.4.10a, automatic over `K̄`);
* `hkerdeg` — the separable degree match `#ker φ_L = φ_L.degree` (Silverman III.4.10c);
* `hcomm'` — the translation covariance `τ_S ∘ φ_L^* = φ_L^* ∘ τ_{φ_L S}` (Silverman III.8.2),
  supplied for every `ℓ`-torsion `S, T`.

These are the genuine geometric facts about the separable isogeny `rπ − s` base-changed to `K̄`,
carried per isogeny in the project's witness-parametric style (identical in kind to leaf 2). -/
structure PencilScalingData (r' s' : ℤ) where
  /-- The base-changed pullback `AlgHom` `K(E_{K̄}) →ₐ[L] K(E_{K̄})`. -/
  pullback_L : (W.baseChange L).toAffine.FunctionField →ₐ[L]
    (W.baseChange L).toAffine.FunctionField
  /-- Finiteness of `ker(φ_L)` (so the dual relation / `#ker` make sense). -/
  finiteKer :
    Finite (pencilIsogBaseChange W p r L r' s' pullback_L).toAddMonoidHom.ker
  /-- The natural degree of `φ_L` (= the K-level genuine `rπ − s` degree). -/
  degK : ℕ
  /-- **Degree preservation** `φ_L.degree = degK`. -/
  hdeg_bc : (pencilIsogBaseChange W p r L r' s' pullback_L).degree = degK
  /-- **Divisor-pullback functoriality** `ProjOrdTransport φ_L`. -/
  hproj : ProjOrdTransport (pencilIsogBaseChange W p r L r' s' pullback_L)
  /-- **Surjectivity** of `φ_L` on `E_{K̄}`-points (Silverman III.4.10a).  No longer consumed by the
  scaling itself (the image-restricted adjoint removed that dependency, reviewer round-20 Q2); it is
  retained because the divisor-pushforward dual `δ = divisorPushforwardDual` is built from it inline
  in `pencilScaling_of_data` (the `degree(φ^*D) = #ker · degree D` formula needs every place to have a
  preimage). -/
  hsurj :
    Function.Surjective (pencilIsogBaseChange W p r L r' s' pullback_L).toAddMonoidHom
  /-- **The separable degree match** `#ker φ_L = φ_L.degree` (Silverman III.4.10c). -/
  hkerdeg :
    Nat.card (pencilIsogBaseChange W p r L r' s' pullback_L).toAddMonoidHom.ker =
      (pencilIsogBaseChange W p r L r' s' pullback_L).degree
  /-- **The translation covariance** `τ_S ∘ φ_L^* = φ_L^* ∘ τ_{φ_L S}` (Silverman III.8.2),
  per `ℓ`-torsion `S, T`. -/
  hcomm' :
    ∀ (ℓ : ℕ) (hℓF : (ℓ : L) ≠ 0)
      (S T : (W.baseChange L).toAffine.Point)
      (_hS : ((ℓ : ℕ) : ℤ) • S = 0)
      (hφT : ((ℓ : ℕ) : ℤ) •
        (pencilIsogBaseChange W p r L r' s' pullback_L).toAddMonoidHom T = 0),
      translateAlgEquivOfPoint (W.baseChange L) S
          ((pencilIsogBaseChange W p r L r' s' pullback_L).pullback
            (weilFunction (W.baseChange L) ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
              ((pencilIsogBaseChange W p r L r' s' pullback_L).toAddMonoidHom T) hφT)) =
        (pencilIsogBaseChange W p r L r' s' pullback_L).pullback
          (translateAlgEquivOfPoint (W.baseChange L)
            ((pencilIsogBaseChange W p r L r' s' pullback_L).toAddMonoidHom S)
            (weilFunction (W.baseChange L) ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
              ((pencilIsogBaseChange W p r L r' s' pullback_L).toAddMonoidHom T) hφT))

/-- **One `WeilScales` instance for `rπ − s` from the bundled data** (Silverman III.8.6.1),
CoordHom-free.

For fixed `r', s'`, the prime `ℓ` (`(ℓ : L) ≠ 0`), and the bundled geometric data
`d : PencilScalingData`, the predicate `WeilScales (W.baseChange L) ℓ hℓF (r·π̄ − s·id) d.degK`
holds:
`e_ℓ((r·π̄ − s·id) S, (r·π̄ − s·id) T) = e_ℓ(S, T)^{d.degK}` on `E_{K̄}[ℓ]`.

Proof: `weilScales_of_dualComp` applied to `φ_L = pencilIsogBaseChange`, with the bare hom
`ψ := r·π̄ − s·id` (matched by the constructional `pencilIsogBaseChange_toAddMonoidHom`, `rfl`), the
degree `d.degK` (`hdeg_bc`), the **divisor-pushforward** dual `δ = divisorPushforwardDual` and the
dual relation `divisorPushforwardDual_comp` (**automatic via the σ-bridge**, no characteristic
polynomial / trace relation), degree match `hkerdeg`, the `[ℓ]`-commutation (the proven
`pencilIsogBaseChange_commute_mulByInt`), and the translation covariance `hcomm'`.  `d.hsurj` is
**no longer** passed to the scaling (reviewer round-20 Q2: the image-restricted adjoint removes that
dependency); it is consumed only by the inline `divisorPushforwardDual`/`_comp` that build `δ`. -/
theorem pencilScaling_of_data (r' s' : ℤ) (ℓ : ℕ) [Fact ℓ.Prime] (hℓF : (ℓ : L) ≠ 0)
    (d : PencilScalingData W p r L r' s') :
    WeilScales (W.baseChange L) ℓ hℓF
      (r' • frobeniusHomBaseChange W p r L -
        s' • AddMonoidHom.id (W.baseChange L).toAffine.Point)
      d.degK := by
  haveI := d.finiteKer
  -- The concrete base-changed isogeny, with point map `r·π̄ − s·id` (by construction).
  set φL := pencilIsogBaseChange W p r L r' s' d.pullback_L with hφL
  -- Apply the CoordHom-free `WeilScales` bridge to `φL`, with the divisor-pushforward dual.
  refine weilScales_of_dualComp (W.baseChange L) ℓ hℓF φL
    (r' • frobeniusHomBaseChange W p r L -
      s' • AddMonoidHom.id (W.baseChange L).toAffine.Point)
    (pencilIsogBaseChange_toAddMonoidHom W p r L r' s' d.pullback_L)
    d.degK d.hdeg_bc
    d.hproj
    (pencilIsogBaseChange_commute_mulByInt W p r L ((ℓ : ℕ) : ℤ) r' s' d.pullback_L)
    (divisorPushforwardDual (W.baseChange L) φL d.hproj d.hsurj)
    (divisorPushforwardDual_comp (W.baseChange L) φL d.hproj d.hsurj)
    d.hkerdeg ?_
  -- The translation covariance, per torsion `S, T`.
  intro S T hS hφT
  exact d.hcomm' ℓ hℓF S T hS hφT

end Data

/-! ### Discharging `PencilScaling` via the divisor-pushforward dual

`pencilScaling_of_divisorDual` assembles the full leaf `PencilScaling` over `L = AlgebraicClosure K`
from a per-`(r', s')` family of `PencilScalingData`, with the dual point `δ`/`hdc` supplied by the
divisor pushforward (CoordHom-free, the σ-bridge dual) — no characteristic polynomial / trace
relation.  The exponent function `deg` is read off the carried isogeny degrees. -/

section Assemble

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]

noncomputable local instance instDecEqACPencil : DecidableEq (AlgebraicClosure K) := Classical.decEq _

open IsogenyBaseChangeConcrete

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]
  [IsIntegrallyClosed
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).CoordinateRing]

/-- **`PencilScaling` discharged via the divisor-pushforward dual** (Silverman III.8.6.1),
CoordHom-free.  For the base-changed separable pencil `(rπ − s)_{K̄}` over `L = AlgebraicClosure K`,
the symplectic scaling `e_ℓ((r·π̄ − s·id) S, (r·π̄ − s·id) T) = e_ℓ(S, T)^{(deg r s).toNat}` on
`E_{K̄}[ℓ]` (every separable `(r, s)` with `p ∤ s`, every prime `ℓ ≠ p`) holds, from the
divisor-pushforward dual `δ`/`hdc` (`divisorPushforwardDual` + `divisorPushforwardDual_comp`, the
σ-bridge dual of `OneSubDualDivisor.lean` Step 4 — **no characteristic polynomial / `π + V = [t]`
trace relation, no `CoordHom`**) together with the project's standing CoordHom-free residuals,
carried per `(r, s)` in `PencilScalingData`:

* `pullback_L` — the base-changed pullback `AlgHom`;
* `hproj` — `ProjOrdTransport` (multiplicity-free divisor-pullback functoriality);
* `hsurj` — surjectivity of `(rπ − s)_{K̄}` over `K̄` (Silverman III.4.10a);
* `hkerdeg` — the separable degree match `#ker = deg` (Silverman III.4.10c);
* `hcomm'` — the translation covariance (Silverman III.8.2).

The exponent function is `deg r s := ((pencilData r s).degK : ℤ)` (the carried isogeny degree, =
the K-level genuine `rπ − s` degree); `(deg r s).toNat = (pencilData r s).degK` is then immediate and
non-negativity is free.  This routes the leaf-3 scaling through the **divisor pushforward** dual the
reviewer prescribed (round 19 Q3), eliminating any char-poly / dual-additivity input. -/
theorem pencilScaling_of_divisorDual
    (pencilData : ∀ r' s' : ℤ, PencilScalingData W p r (AlgebraicClosure K) r' s') :
    PencilScaling W p r (AlgebraicClosure K)
      (fun r' s' => ((pencilData r' s').degK : ℤ)) := by
  intro r' s' _hps ℓ hℓp _hℓne hℓF
  letI : Fact ℓ.Prime := ⟨hℓp⟩
  -- `((deg r' s').toNat) = (pencilData r' s').degK`.
  rw [show (((pencilData r' s').degK : ℤ)).toNat = (pencilData r' s').degK from
    Int.toNat_natCast _]
  exact pencilScaling_of_data W p r (AlgebraicClosure K) r' s' ℓ hℓF (pencilData r' s')

/-- **`PencilScaling` for an arbitrary non-negative exponent function `deg`**, given that the carried
isogeny degrees realise it.  This is the form a top-level caller uses to obtain `PencilScaling` for a
fixed `deg` (e.g. `deg r s := (genuineIsogSmulSub W r s …).degree`): supply the per-`(r, s)`
`PencilScalingData` and the per-`(r, s)` degree identification `hdeg`. -/
theorem pencilScaling_of_divisorDual_of_deg
    (deg : ℤ → ℤ → ℤ)
    (pencilData : ∀ r' s' : ℤ, PencilScalingData W p r (AlgebraicClosure K) r' s')
    (hdeg : ∀ r' s' : ℤ, (deg r' s').toNat = (pencilData r' s').degK) :
    PencilScaling W p r (AlgebraicClosure K) deg := by
  intro r' s' _hps ℓ hℓp _hℓne hℓF
  letI : Fact ℓ.Prime := ⟨hℓp⟩
  rw [hdeg r' s']
  exact pencilScaling_of_data W p r (AlgebraicClosure K) r' s' ℓ hℓF (pencilData r' s')

end Assemble

end HasseWeil.WeilPairing

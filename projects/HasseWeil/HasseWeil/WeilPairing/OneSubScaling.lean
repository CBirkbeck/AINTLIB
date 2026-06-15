/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.SeparableScaling
import HasseWeil.WeilPairing.FrobMatrixData

/-!
# The separable `1 − π` Weil-pairing scaling (Silverman III.8.6.1), CoordHom-free

This file discharges the leaf `HasseWeil.WeilPairing.OneSubFrobeniusScaling` (`FrobMatrixData.lean`)
— the symplectic Weil-pairing scaling `e_ℓ((id − π̄) S, (id − π̄) T) = e_ℓ(S, T)^{deg(1 − π)}` for
the base-changed *separable* isogeny `(1 − π)_{K̄}` over `L = K̄` — **without** ever requiring an
`Isogeny.CoordHom`.  Recall (`SeparableScaling.lean`) that `(1 − π).pullback x` has poles at the
affine kernel `E(𝔽_q)`, so no `CoordHom` exists; the whole route is therefore routed through the
CoordHom-free `weilScales_of_dualComp`, which consumes only an abstract dual `δ` with the
divisor-pushforward dual relation `δ ∘ φ = [#ker φ]` (Silverman III.6.2(a)).

## The concrete base-changed isogeny `φ_L`

The target `OneSubFrobeniusScaling` names the point map `AddMonoidHom.id _ − frobeniusHomBaseChange`
(`= id − π̄`, the genuine `q`-power Frobenius point map on `E_{K̄}`).  We build the concrete
base-changed isogeny

  `oneSubFrobeniusIsogBaseChange L pullback_L := mkBaseChange L pullback_L (id − π̄)`

(`IsogenyBaseChange.mkBaseChange`), whose `toAddMonoidHom` is **by construction** exactly
`id − π̄` (`oneSubFrobeniusIsogBaseChange_toAddMonoidHom`, `rfl`).  This is the natural base-change
of `(1 − π)`'s point map: the additive base-change functor sends `id ↦ id` and `π`'s point map to
the `q`-power Frobenius `π̄ = frobeniusHomBaseChange` (the underlying hom of
`frobeniusIsog_baseChange_charP_pow`), and preserves subtraction
(`oneSubFrobeniusIsogBaseChange_toAddMonoidHom_eq_baseChange`).  The function-field pullback
`pullback_L : K(E_{K̄}) →ₐ[L] K(E_{K̄})` is the base-change of `(1 − π).pullback` through the
function-field scalar extension `K(E_{K̄}) ≅ K(E) ⊗_K L`; it is supplied as a field of the bundled
data `OneSubScalingData` (the concrete `pullback_L`, the degree-preservation
`φ_L.degree = (1 − π).degree`, and the genuine geometric residuals), exactly as the project's other
base-change residuals (`FrobeniusScalingWitnesses`, `ProjOrdTransport`, `Naturality`) are carried.

## What is proved vs. carried

* **Proved** in this file (axiom-clean, no `sorry`):
  * the concrete `φ_L` and its point-map identity (`= id − π̄`, `rfl`);
  * `id − π̄` is the base-change of `(1 − π)`'s point map (subtraction/`id` preservation);
  * the `[ℓ]`-commutation `hcommφ : [ℓ] ∘ φ_L = φ_L ∘ [ℓ]` (pure `map_zsmul`, no geometry);
  * `oneSubFrobeniusScaling_of_data` — `OneSubFrobeniusScaling` from the bundled data, via
    `weilScales_of_dualComp`.

* **Carried** as the bundled `OneSubScalingData` (the genuine CoordHom-free geometric content of
  the separable scaling, each an exact Lean field):
  * `pullback_L` — the base-changed pullback `AlgHom`;
  * `hdeg_bc : φ_L.degree = (1 − π).degree` — degree preservation (the tensor-finrank witness,
    `Isogeny.degree_eq_of_finrank_eq` modulo `Module.finrank_baseChange` for `K(E_{K̄}) ≅ K(E)⊗L`);
  * `hproj : ProjOrdTransport φ_L` — divisor-pullback functoriality (multiplicity-free pullback);
  * `δ`, `hdc : δ ∘ φ_L = [#ker φ_L]` — the divisor-pushforward dual `1 − V̄` and III.6.2(a);
  * `hsurj : Function.Surjective φ_L` — surjectivity over `K̄` (Silverman III.4.10a);
  * `hkerdeg : #ker φ_L = φ_L.degree` — the separable degree match (III.4.10c);
  * `hcomm' : …` — translation covariance `τ_S ∘ φ_L^* = φ_L^* ∘ τ_{φ_L S}` (III.8.2).

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.6.1(b)/III.6.2(a) (the dual + dual relation),
  III.4.10a/c (surjectivity over `K̄`, separable degree = kernel size), III.8.2 (the translation
  covariance behind the separable adjoint), III.8.6.1 (the symplectic scaling
  `e_ℓ(φS, φT) = e_ℓ(S,T)^{deg φ}`).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.WeilPairing.DivisorPullback HasseWeil.WeilPairing.TorsionGeometric

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

section BaseChange

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

/-! ### The concrete base-changed isogeny `(1 − π)_{K̄}`

`oneSubFrobeniusIsogBaseChange` packages the base-changed pullback `pullback_L` together with the
**concrete** point map `id − π̄` (`π̄ = frobeniusHomBaseChange`), via `Isogeny.mkBaseChange`.  The
point map matches `OneSubFrobeniusScaling`'s `AddMonoidHom.id _ − frobeniusHomBaseChange W p r L`
by construction. -/

variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
variable (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [ExpChar L p]
  [(W.baseChange L).toAffine.IsElliptic]

/-- **The concrete base-changed `1 − π`** (`(1 − π)_{K̄}`).  Built from the base-changed pullback
`pullback_L` (a field of the bundled data, the base-change of `(1 − π).pullback` through
`K(E_{K̄}) ≅ K(E) ⊗_K L`) and the **concrete** point map `id − π̄`, where
`π̄ = frobeniusHomBaseChange W p r L` is the `q`-power Frobenius point map on `E_{K̄}`.

Its `toAddMonoidHom` is **definitionally** `AddMonoidHom.id _ − frobeniusHomBaseChange W p r L`, i.e.
exactly the bare hom named in `OneSubFrobeniusScaling`. -/
noncomputable def oneSubFrobeniusIsogBaseChange
    (pullback_L : (W.baseChange L).toAffine.FunctionField →ₐ[L]
      (W.baseChange L).toAffine.FunctionField) :
    HasseWeil.Isogeny (W.baseChange L).toAffine (W.baseChange L).toAffine :=
  Isogeny.mkBaseChange L pullback_L
    (AddMonoidHom.id _ - frobeniusHomBaseChange W p r L)

@[simp] theorem oneSubFrobeniusIsogBaseChange_toAddMonoidHom
    (pullback_L : (W.baseChange L).toAffine.FunctionField →ₐ[L]
      (W.baseChange L).toAffine.FunctionField) :
    (oneSubFrobeniusIsogBaseChange W p r L pullback_L).toAddMonoidHom =
      AddMonoidHom.id _ - frobeniusHomBaseChange W p r L :=
  Isogeny.mkBaseChange_toAddMonoidHom L _ _

@[simp] theorem oneSubFrobeniusIsogBaseChange_pullback
    (pullback_L : (W.baseChange L).toAffine.FunctionField →ₐ[L]
      (W.baseChange L).toAffine.FunctionField) :
    (oneSubFrobeniusIsogBaseChange W p r L pullback_L).pullback = pullback_L :=
  Isogeny.mkBaseChange_pullback L _ _

/-- **Degree preservation reduced to the tensor-finrank witness** (Silverman: `deg` is invariant
under base change).  The degree equality `φ_L.degree = (1 − π).degree` is *definitionally* the
`Module.finrank` equality of the two isogeny algebras (`Isogeny.degree` unfolds to the finrank over
the function field via the pullback), so it follows from `Isogeny.degree_eq_of_finrank_eq` once the
function-field base-change `K(E_{K̄}) ≅ K(E) ⊗_K L` identifies the finrank of `φ_L` (over the
base-changed function field, via `pullback_L`) with that of `1 − π` (over `K(E)`, via
`(1 − π).pullback`).  This isolates the genuinely-irreducible content as the single finrank
hypothesis `h_finrank` — the place `Module.finrank_baseChange` enters. -/
theorem oneSubFrobeniusIsogBaseChange_degree_eq_of_finrank
    (hq : 2 ≤ Fintype.card K)
    (pullback_L : (W.baseChange L).toAffine.FunctionField →ₐ[L]
      (W.baseChange L).toAffine.FunctionField)
    (h_finrank :
      @Module.finrank (W.baseChange L).toAffine.FunctionField
          (W.baseChange L).toAffine.FunctionField _ _
          (oneSubFrobeniusIsogBaseChange W p r L pullback_L).toAlgebra.toModule =
        @Module.finrank W.toAffine.FunctionField W.toAffine.FunctionField _ _
          (isogOneSub_negFrobenius W hq).toAlgebra.toModule) :
    (oneSubFrobeniusIsogBaseChange W p r L pullback_L).degree =
      (isogOneSub_negFrobenius W hq).degree :=
  Isogeny.degree_eq_of_finrank_eq L (isogOneSub_negFrobenius W hq)
    (oneSubFrobeniusIsogBaseChange W p r L pullback_L) h_finrank

/-- **`id − π̄` is the base-change of `(1 − π)`'s point map.**  The additive base-change functor
sends `(1 − π).toAddMonoidHom = id − π_K` to `id − π̄`, because `π_K`'s point map base-changes to the
`q`-power Frobenius `π̄ = frobeniusHomBaseChange` (which is *exactly* the underlying hom of the
base-changed Frobenius `frobeniusIsog_baseChange_charP_pow`, by definition of `frobeniusHomBaseChange`),
the identity base-changes to the identity, and subtraction is preserved.

Concretely, since `frobeniusHomBaseChange W p r L` is *defined* as
`(Isogeny.frobeniusIsog_baseChange_charP_pow p r W L).toAddMonoidHom`, the point map carried by
`oneSubFrobeniusIsogBaseChange` is the literal "identity minus base-changed Frobenius point map" — the
faithful base-change of the K-level `1 − π` along `K → L`. -/
theorem oneSubFrobeniusIsogBaseChange_toAddMonoidHom_eq_baseChange
    (pullback_L : (W.baseChange L).toAffine.FunctionField →ₐ[L]
      (W.baseChange L).toAffine.FunctionField) :
    (oneSubFrobeniusIsogBaseChange W p r L pullback_L).toAddMonoidHom =
      AddMonoidHom.id (W.baseChange L).toAffine.Point -
        (Isogeny.frobeniusIsog_baseChange_charP_pow p r W L).toAddMonoidHom := by
  rw [oneSubFrobeniusIsogBaseChange_toAddMonoidHom]
  rfl

/-! ### The `[ℓ]`-commutation `hcommφ` (pure point bookkeeping, no geometry)

For *any* isogeny point map `φ` (a group hom), `[ℓ]` commutes with `φ`:
`[ℓ] ∘ φ = φ ∘ [ℓ]` at the `AddMonoidHom` level, because `[ℓ] = (ℓ • ·)` and a group hom commutes
with `ℓ • ·` (`map_zsmul`).  Specialised to `φ = id − π̄`. -/

/-- **`[ℓ] ∘ φ_L = φ_L ∘ [ℓ]`** for `φ_L = (1 − π)_{K̄}` (any base-changed pullback), at the
`AddMonoidHom` level.  Pure `map_zsmul`: both sides send `P ↦ ℓ • (id − π̄)(P) = (id − π̄)(ℓ • P)`. -/
theorem oneSubFrobeniusIsogBaseChange_commute_mulByInt (ℓ : ℤ)
    (pullback_L : (W.baseChange L).toAffine.FunctionField →ₐ[L]
      (W.baseChange L).toAffine.FunctionField) :
    (mulByInt (W.baseChange L).toAffine ℓ).toAddMonoidHom.comp
        (oneSubFrobeniusIsogBaseChange W p r L pullback_L).toAddMonoidHom =
      (oneSubFrobeniusIsogBaseChange W p r L pullback_L).toAddMonoidHom.comp
        (mulByInt (W.baseChange L).toAffine ℓ).toAddMonoidHom := by
  ext P
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, mulByInt_apply, mulByInt_apply,
    map_zsmul]

end BaseChange

/-! ### The bundled base-change data and the discharge of `OneSubFrobeniusScaling`

`OneSubScalingData` bundles the genuine CoordHom-free geometric residuals for the base-changed
separable isogeny `(1 − π)_{K̄}`, carried per isogeny exactly as the project's other base-change
residuals.  From it, `oneSubFrobeniusScaling_of_data` proves `OneSubFrobeniusScaling` via the shipped
CoordHom-free `weilScales_of_dualComp`. -/

section Data

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
variable (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [IsAlgClosed L] [ExpChar L p]
  [(W.baseChange L).toAffine.IsElliptic]
  [IsIntegrallyClosed (⟨(W.baseChange L).toAffine⟩ : SmoothPlaneCurve L).CoordinateRing]

/-- **The base-changed `1 − π` geometric data** (Silverman III.6.1/III.6.2/III.8.2 content),
CoordHom-free.  Bundles, for the base-changed separable isogeny `φ_L = (1 − π)_{K̄}` whose point map
is the concrete `id − π̄`:

* `pullback_L` — the base-changed pullback `AlgHom` (the base-change of `(1 − π).pullback` through
  the function-field scalar extension `K(E_{K̄}) ≅ K(E) ⊗_K L`);
* `hdeg_bc` — **degree preservation** `φ_L.degree = (1 − π).degree` (the substantive tensor-finrank
  witness: `Isogeny.degree_eq_of_finrank_eq` once `Module.finrank_baseChange` identifies the two
  function-field finranks);
* `hproj` — `ProjOrdTransport φ_L` (the multiplicity-free divisor-pullback functoriality);
* `δ` with `hdc` — the divisor-pushforward dual (`1 − V̄`) and the dual relation
  `δ ∘ φ_L = [#ker φ_L]` (Silverman III.6.2(a));
* `hsurj` — surjectivity of `φ_L` on `E_{K̄}`-points (Silverman III.4.10a, automatic over `K̄`);
* `hkerdeg` — the separable degree match `#ker φ_L = φ_L.degree` (Silverman III.4.10c);
* `hcomm'` — the translation covariance `τ_S ∘ φ_L^* = φ_L^* ∘ τ_{φ_L S}` (Silverman III.8.2),
  supplied for every `ℓ`-torsion `S, T`.

These are the genuine geometric facts about the separable isogeny `1 − π` base-changed to `K̄`, carried
per isogeny in the project's witness-parametric style. -/
structure OneSubScalingData (hq : 2 ≤ Fintype.card K) where
  /-- The base-changed pullback `AlgHom` `K(E_{K̄}) →ₐ[L] K(E_{K̄})` (base-change of `(1−π).pullback`). -/
  pullback_L : (W.baseChange L).toAffine.FunctionField →ₐ[L]
    (W.baseChange L).toAffine.FunctionField
  /-- Finiteness of `ker(φ_L)` (so the dual relation / `#ker` make sense). -/
  finiteKer :
    Finite (oneSubFrobeniusIsogBaseChange W p r L pullback_L).toAddMonoidHom.ker
  /-- **Degree preservation**: `φ_L.degree = (1 − π).degree`.  This is *definitionally* the
  tensor-finrank witness (`Isogeny.degree` is a `Module.finrank`); supplied from the raw finrank
  equality by `oneSubFrobeniusIsogBaseChange_degree_eq_of_finrank` once `Module.finrank_baseChange`
  identifies `K(E_{K̄}) ≅ K(E) ⊗_K L`. -/
  hdeg_bc :
    (oneSubFrobeniusIsogBaseChange W p r L pullback_L).degree =
      (isogOneSub_negFrobenius W hq).degree
  /-- **Divisor-pullback functoriality** `ProjOrdTransport φ_L`. -/
  hproj : ProjOrdTransport (oneSubFrobeniusIsogBaseChange W p r L pullback_L)
  /-- The divisor-pushforward dual `δ = 1 − V̄`. -/
  δ : (W.baseChange L).toAffine.Point →+ (W.baseChange L).toAffine.Point
  /-- **The dual relation** `δ ∘ φ_L = [#ker φ_L]` (Silverman III.6.2(a)). -/
  hdc :
    δ.comp (oneSubFrobeniusIsogBaseChange W p r L pullback_L).toAddMonoidHom =
      (mulByInt (W.baseChange L).toAffine
        (Nat.card (oneSubFrobeniusIsogBaseChange W p r L pullback_L).toAddMonoidHom.ker
          : ℤ)).toAddMonoidHom
  /-- **Surjectivity** of `φ_L` on `E_{K̄}`-points (Silverman III.4.10a).  No longer consumed by the
  scaling itself (the image-restricted adjoint `weilPairing_adjoint_of_dualComp_image` removed that
  dependency, reviewer round-20 Q2); it remains the carrier of the surjectivity needed only to
  *construct* the divisor-pushforward dual `δ`/`hdc` (the `degree(φ^*D) = #ker · degree D` formula). -/
  hsurj :
    Function.Surjective (oneSubFrobeniusIsogBaseChange W p r L pullback_L).toAddMonoidHom
  /-- **The separable degree match** `#ker φ_L = φ_L.degree` (Silverman III.4.10c). -/
  hkerdeg :
    Nat.card (oneSubFrobeniusIsogBaseChange W p r L pullback_L).toAddMonoidHom.ker =
      (oneSubFrobeniusIsogBaseChange W p r L pullback_L).degree
  /-- **The translation covariance** `τ_S ∘ φ_L^* = φ_L^* ∘ τ_{φ_L S}` (Silverman III.8.2),
  per `ℓ`-torsion `S, T`. -/
  hcomm' :
    ∀ (ℓ : ℕ) (hℓF : (ℓ : L) ≠ 0)
      (S T : (W.baseChange L).toAffine.Point)
      (_hS : ((ℓ : ℕ) : ℤ) • S = 0)
      (hφT : ((ℓ : ℕ) : ℤ) •
        (oneSubFrobeniusIsogBaseChange W p r L pullback_L).toAddMonoidHom T = 0),
      translateAlgEquivOfPoint (W.baseChange L) S
          ((oneSubFrobeniusIsogBaseChange W p r L pullback_L).pullback
            (weilFunction (W.baseChange L) ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
              ((oneSubFrobeniusIsogBaseChange W p r L pullback_L).toAddMonoidHom T) hφT)) =
        (oneSubFrobeniusIsogBaseChange W p r L pullback_L).pullback
          (translateAlgEquivOfPoint (W.baseChange L)
            ((oneSubFrobeniusIsogBaseChange W p r L pullback_L).toAddMonoidHom S)
            (weilFunction (W.baseChange L) ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
              ((oneSubFrobeniusIsogBaseChange W p r L pullback_L).toAddMonoidHom T) hφT))

/-- **`OneSubFrobeniusScaling` from the bundled data** (Silverman III.8.6.1), CoordHom-free.

For the base-changed separable isogeny `φ_L = (1 − π)_{K̄}` (point map `id − π̄`), given the bundled
geometric data `d : OneSubScalingData`, the leaf `OneSubFrobeniusScaling W p r L hq` holds: for every
prime `ℓ ≠ ringChar K` with `(ℓ : K̄) ≠ 0`,
`e_ℓ((id − π̄) S, (id − π̄) T) = e_ℓ(S, T)^{deg(1 − π)}` on `E_{K̄}[ℓ]`.

Proof: `weilScales_of_dualComp` applied to `φ_L`, with the bare hom `ψ := id − π̄` (matched by the
constructional `oneSubFrobeniusIsogBaseChange_toAddMonoidHom`, `rfl`), the degree `d := (1−π).degree`
(`hdeg_bc`), the dual `δ`/`hdc`, degree match `hkerdeg`, the `[ℓ]`-commutation (the proven
`oneSubFrobeniusIsogBaseChange_commute_mulByInt`), and the translation covariance `hcomm'`.
Surjectivity `hsurj` is **no longer** passed to the scaling (it now uses the image-restricted adjoint,
reviewer round-20 Q2); `d.hsurj` is consumed only upstream, to build `δ`/`hdc`. -/
theorem oneSubFrobeniusScaling_of_data (hq : 2 ≤ Fintype.card K)
    (d : OneSubScalingData W p r L hq) :
    OneSubFrobeniusScaling W p r L hq := by
  intro ℓ hℓp hℓne hℓF
  letI : Fact ℓ.Prime := ⟨hℓp⟩
  haveI := d.finiteKer
  -- The concrete base-changed isogeny, with point map `id − π̄` (by construction).
  set φL := oneSubFrobeniusIsogBaseChange W p r L d.pullback_L with hφL
  -- Apply the CoordHom-free `WeilScales` bridge to `φL`.
  refine weilScales_of_dualComp (W.baseChange L) ℓ hℓF φL
    (AddMonoidHom.id (W.baseChange L).toAffine.Point - frobeniusHomBaseChange W p r L)
    (oneSubFrobeniusIsogBaseChange_toAddMonoidHom W p r L d.pullback_L)
    (isogOneSub_negFrobenius W hq).degree d.hdeg_bc
    d.hproj
    (oneSubFrobeniusIsogBaseChange_commute_mulByInt W p r L ((ℓ : ℕ) : ℤ) d.pullback_L)
    d.δ d.hdc d.hkerdeg ?_
  -- The translation covariance, per torsion `S, T`.
  intro S T hS hφT
  exact d.hcomm' ℓ hℓF S T hS hφT

end Data

end HasseWeil.WeilPairing

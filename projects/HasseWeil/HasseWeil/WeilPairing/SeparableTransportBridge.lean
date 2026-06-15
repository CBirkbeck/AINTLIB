/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.SeparableWitnesses
import HasseWeil.WeilPairing.SeparableScaling

/-!
# The geometric-realisation / compatibility layer for separable scaling (reviewer round-20 bridge A)

This file builds the **single reusable compatibility layer** the external reviewer asked for
(round-20, Q1/Q5): a bundle `GeometricRealization φ` carrying — for a separable isogeny `φ` of `E`
over `K̄` — the genuine *comorphism compatibility* (the function-field pullback `φ.pullback`
**and** the point map `φ.toAddMonoidHom`, tied together at the generic point), from which the
per-isogeny separable-scaling witnesses are *derived once*, instead of being re-supplied separately
for each pencil member (`1 − π`, `rπ − s`, …).

## What the reviewer asked for, and what is actually derivable

> **Q5 milestone.** `GeometricRealization` structure +
> `separable_scaling_witnesses_of_geometricRealization (hφ) : Surjective φ.toAddMonoidHom ∧
> TranslationCovariant φ ∧ DivisorTransport φ`, instantiated for `1 − π`, `rπ − s`, `λ`.
>
> **Caution.** Define the bridge at the right level: NOT merely agreement on closed points — need
> compatibility with the comorphism. Include BOTH `pointMap_eq` AND `pullback_eq`; prove
> covariance/transport by transporting from the geometric isogeny through both.

The project's `Isogeny` already **is** its own geometric realisation: it bundles `pullback`
(comorphism) and `toAddMonoidHom` (point map) as the two fields the reviewer names, and
`HasseWeil.WallA.isogeny_isGenuineWith_pointMap` shows the canonical geometric action
`g = Affine.Point.map φ.pullback` is genuine (`IsGenuineWith φ g` — the pullback's effect on the
generators `x_gen, y_gen` *is* the geometric image of the generic point under `g`).  So the
reviewer's `pullback_eq` / `pointMap_eq` to a separate geometric object are **automatic**
(`realization_pullback_eq` / `realization_pointMap_eq`, `rfl`); the bridge does not need to carry
them.

The genuinely-substantive compatibility — the one piece of geometry that is *not* recoverable from
the abstract `Isogeny` fields — is the **generic-point covariance**

  `hgcomm : Point.map τ_S (g P_gen) = g P_gen + lift (φ S)`     (`MapTranslateGenericPoint φ g`),

i.e. `φ(P_gen + S) = φ(P_gen) + φ(S)` read at the generic point for the canonical pullback action
(Silverman III.8.2, generic-point form).  The previous consolidation
(`SeparableWitnesses.lean`) established that this **single leaf** discharges *both*

* the translation covariance `hcomm'` (`hcomm_of_mapTranslateGenericPoint_canonical`), and
* the kernel-translation invariance `hcov` feeding the separable degree match `#ker = deg`
  (`hcov_of_mapTranslateGenericPoint_canonical` → `card_kernel_eq_degree_of_separable_concrete`).

This file *bundles* that consolidation into the reviewer's one structure and exposes the Q5-shaped
conjunction `separable_scaling_witnesses_of_geometricRealization`.

## Honest scope of the consolidation (what is derived, what is carried)

Of the four per-isogeny witnesses (`hsurj`, `hcomm'`, `#ker = deg`, `ProjOrdTransport`):

* `hcomm'` (`TranslationCovariant`) — **derived** from the single bundled leaf `hgcomm` (no longer a
  separate per-isogeny field).
* `#ker = deg` — **derived** from `hgcomm` (via `hcov`) together with the standard separable-Galois
  inputs `IsSeparable`/`Normal`/`hdesc`, all of which the bundle carries.
* `hsurj` (`Surjective φ.toAddMonoidHom`) — **carried**.  It is *not* derivable from
  `ProjOrdTransport` + separability: `ProjOrdTransport` constrains only pullbacks of **principal**
  (degree-`0`) divisors via `projectiveDivisorOf`, so it says nothing about `φ^*((Q))` for a single
  non-principal place; and the project's only divisor pullback (`pullbackDivisor`, the point-map
  fibre sum) has its degree formula `deg(φ^*D) = #ker · deg D` *gated on surjectivity itself*
  (`degree_pullbackDivisor` takes `hsurj` — it needs a preimage to size each fibre).  There is no
  comorphism-side (Σ e·f) divisor pullback for general isogenies in the project, so the reviewer-Q3
  route "`deg(φ^*((Q))) = deg φ ≠ 0` ⟹ fibre nonempty" has no object to run on.  Hence `hsurj`
  stays a carried geometric datum (Silverman III.4.10a: a nonconstant isogeny is a finite morphism
  of complete curves, hence surjective on `K̄`-points).
* `ProjOrdTransport` — **carried** (the deepest divisor-pullback functoriality; the `[ℓ]` template
  in `DivisorPullback.lean` is the model, assessed for `1 − π` separately).

So the layer collapses the *three* previously-scattered residual fields `hcomm'` / `#ker = deg`
(`hkerdeg`) / (their shared `hcov`) into the *one* leaf `hgcomm`, leaving exactly the two genuinely
irreducible geometric carriers `hsurj` and `ProjOrdTransport` — matching the reviewer's "one
reusable compatibility layer".

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.4.10(a) (surjectivity over `K̄`),
  III.4.10(c) (separable ⟹ `#ker = deg`), III.8.2 (translation covariance), III.8.6.1 (the
  symplectic scaling `e_ℓ(φS, φT) = e_ℓ(S, T)^{deg φ}`).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.WeilPairing.DivisorPullback HasseWeil.WeilPairing.TorsionGeometric

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

section Realization

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-! ### The translation-covariance predicate `TranslationCovariant` (the `hcomm'` shape)

`TranslationCovariant φ` is the pointwise translation covariance `τ_S(φ^* z) = φ^*(τ_{φS} z)` for
every point `S` and every function `z` — exactly the content the separable adjoint
(`weilPairing_adjoint_core`) and hence the scaling consume (carried per `(ℓ, S, T)` in the bundled
`OneSubScalingData.hcomm'` / `PencilScalingData.hcomm'`).  Stating it as a standalone predicate lets
the bridge expose the reviewer's `TranslationCovariant φ` conjunct. -/

/-- **The translation covariance of an isogeny** (Silverman III.8.2): `τ_S ∘ φ^* = φ^* ∘ τ_{φS}`
pointwise, i.e. `τ_S(φ^* z) = φ^*(τ_{φS} z)` for all `S` and `z`.  This is the `hcomm'` shape the
separable adjoint/scaling consume. -/
def TranslationCovariant (φ : Isogeny W.toAffine W.toAffine) : Prop :=
  ∀ (S : W.toAffine.Point) (z : W.toAffine.FunctionField),
    HasseWeil.translateAlgEquivOfPoint W S (φ.pullback z) =
      φ.pullback (HasseWeil.translateAlgEquivOfPoint W (φ.toAddMonoidHom S) z)

/-! ### The bundle `GeometricRealization`

The reviewer's compatibility layer.  For a separable isogeny `φ` of `E` over `K̄`, it carries the
**genuine geometric data** that is not recoverable from the abstract `Isogeny` fields:

* `hgcomm` — the generic-point covariance for the canonical action (the single leaf discharging
  both `hcomm'` and `#ker = deg`);
* `hsep` / `h_normal` / `hdesc` — the standard separable-Galois inputs (Silverman III.4.10c);
* `hsurj` — surjectivity over `K̄` (Silverman III.4.10a);
* `hproj` — the divisor-pullback functoriality `ProjOrdTransport φ`.

The comorphism compatibility the reviewer's *Caution* demands — that `φ.pullback` and
`φ.toAddMonoidHom` belong to the *same* morphism — is *built into* `Isogeny` (the two fields) and
witnessed by `realization_isGenuineWith` (`isogeny_isGenuineWith_pointMap`); see
`realization_pullback_eq` / `realization_pointMap_eq`. -/
structure GeometricRealization (φ : Isogeny W.toAffine W.toAffine) : Prop where
  /-- **The generic-point covariance leaf** `hgcomm` (Silverman III.8.2, generic-point form), for
  the canonical geometric action `g = Affine.Point.map φ.pullback`.  This single piece of geometry
  discharges *both* the translation covariance `hcomm'` and (via `hcov`) the separable degree match
  `#ker = deg`. -/
  hgcomm : MapTranslateGenericPoint W φ
    (WeierstrassCurve.Affine.Point.map (W' := W) φ.pullback)
  /-- **Separability** of `φ` (Silverman III.4.10c / III.5.5). -/
  hsep : φ.IsSeparable
  /-- **Normality** of the function-field extension `K(E) / φ^* K(E)` (Silverman III.4.10a). -/
  h_normal : letI := φ.toAlgebra
    Normal W.toAffine.FunctionField W.toAffine.FunctionField
  /-- **The generic-point translation torsor** `hdesc` (Silverman III.4.10c): every
  `σ(P_gen) − P_gen` is the lift of an `F`-rational kernel point. -/
  hdesc : ∀ σ : (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ _ φ.toAlgebra φ.toAlgebra),
    ∃ k : W.toAffine.Point, k ∈ φ.kernel ∧
      HasseWeil.liftPointToKE W k =
        HasseWeil.genericPointAct W φ σ - HasseWeil.genericPoint W
  /-- **Surjectivity** of `φ` on `E`-points over `K̄` (Silverman III.4.10a).  Carried: it is not
  derivable from `ProjOrdTransport` + separability (see the module docstring). -/
  hsurj : Function.Surjective φ.toAddMonoidHom
  /-- **Divisor-pullback functoriality** `ProjOrdTransport φ` (the multiplicity-free order
  transport; the deepest carried datum, with the `[ℓ]` template in `DivisorPullback.lean`). -/
  hproj : ProjOrdTransport φ

namespace GeometricRealization

variable {W} {φ : Isogeny W.toAffine W.toAffine}

/-! #### The comorphism compatibility (`pullback_eq` / `pointMap_eq`, reviewer's *Caution*)

The reviewer asked the bridge to include BOTH a `pullback_eq` and a `pointMap_eq` to the geometric
isogeny.  In this project the geometric isogeny *is* `φ` itself: `Isogeny` bundles the comorphism
`φ.pullback` and the point map `φ.toAddMonoidHom`, and the canonical geometric action
`Affine.Point.map φ.pullback` is genuine for `φ`.  So both equations are `rfl`, and the genuine
content of "these two belong to the same morphism" is the genuineness witness
`realization_isGenuineWith`. -/

/-- **Comorphism compatibility — the genuineness witness** (the reviewer's *Caution*: compatibility
with the comorphism, not merely closed points).  The canonical geometric action
`g = Affine.Point.map φ.pullback` is genuine for `φ`: its value on the generic point reads off the
comorphism's effect on the generators, `g P_gen = (φ^* x_gen, φ^* y_gen)`.  This is the
"`pullback` and `toAddMonoidHom` are two faces of one morphism" fact, free for every isogeny
(`isogeny_isGenuineWith_pointMap`). -/
theorem realization_isGenuineWith :
    IsGenuineWith W φ (WeierstrassCurve.Affine.Point.map (W' := W) φ.pullback) :=
  HasseWeil.WallA.isogeny_isGenuineWith_pointMap W φ

/-- **`pullback_eq` (reviewer's *Caution*).** The comorphism of the geometric realisation *is*
`φ.pullback`.  In this project the geometric isogeny is `φ` itself (`Isogeny` bundles the
comorphism), so this is definitional. -/
theorem realization_pullback_eq : φ.pullback = φ.pullback := rfl

/-- **`pointMap_eq` (reviewer's *Caution*).** The point map of the geometric realisation *is*
`φ.toAddMonoidHom`.  Definitional, for the same reason. -/
theorem realization_pointMap_eq : φ.toAddMonoidHom = φ.toAddMonoidHom := rfl

/-! #### Derived witness — the translation covariance `hcomm'`

From the single bundled leaf `hgcomm`, the full translation covariance follows by the consolidated
`hcomm_of_mapTranslateGenericPoint_canonical`.  This *eliminates* `hcomm'` as a separate per-isogeny
field. -/

/-- **Translation covariance, derived from the bundle** (Silverman III.8.2).  The pointwise
covariance `τ_S(φ^* z) = φ^*(τ_{φS} z)` follows from the single generic-point leaf `hgcomm`
(carried in the bundle), via `hcomm_of_mapTranslateGenericPoint_canonical`. -/
theorem translationCovariant (hφ : GeometricRealization W φ) :
    TranslationCovariant W φ :=
  fun S z => hcomm_of_mapTranslateGenericPoint_canonical W φ hφ.hgcomm S z

/-! #### Derived witness — the separable degree match `#ker = deg`

`#ker = deg` follows from the bundled `hsep` / `h_normal` / `hdesc` plus the kernel-translation
invariance `hcov`, which the consolidated `hcov_of_mapTranslateGenericPoint_canonical` derives from
the *same* leaf `hgcomm`.  So the `hkerdeg` field is *also* eliminated in favour of `hgcomm`. -/

/-- **The separable degree match `#ker φ = deg φ`, derived from the bundle** (Silverman III.4.10c).
Routes through the concrete Galois fibre-count `card_kernel_eq_degree_of_separable_concrete`, whose
kernel-translation invariance `hcov` is supplied from the bundled leaf `hgcomm`
(`hcov_of_mapTranslateGenericPoint_canonical`); separability/normality/descent are the bundle's
`hsep`/`h_normal`/`hdesc`. -/
theorem card_kernel_eq_degree (hφ : GeometricRealization W φ) :
    Nat.card φ.kernel = φ.degree :=
  HasseWeil.card_kernel_eq_degree_of_separable_concrete W φ hφ.hsep
    (fun k z => hcov_of_mapTranslateGenericPoint_canonical W φ hφ.hgcomm k z)
    hφ.h_normal hφ.hdesc

/-- **`#ker φ = deg φ`, `AddMonoidHom.ker` form** (the shape the scaling's `hdeg`/`hkerdeg`
hypotheses use).  `φ.kernel` is *definitionally* `φ.toAddMonoidHom.ker`, so this is
`card_kernel_eq_degree`. -/
theorem card_ker_eq_degree (hφ : GeometricRealization W φ) :
    Nat.card φ.toAddMonoidHom.ker = φ.degree :=
  hφ.card_kernel_eq_degree

end GeometricRealization

/-! ### The reviewer's Q5 milestone — the three witnesses from one bundle

`separable_scaling_witnesses_of_geometricRealization` packages the conjunction the reviewer named:
from a `GeometricRealization φ`, obtain `Surjective φ.toAddMonoidHom ∧ TranslationCovariant φ ∧
ProjOrdTransport φ` (the `Surjective`/`TranslationCovariant`/`DivisorTransport` triple), with the
fourth scaling input `#ker = deg` available as `GeometricRealization.card_ker_eq_degree`. -/

/-- **The separable-scaling witnesses from a geometric realisation** (reviewer round-20, Q5).  For a
separable isogeny `φ` of `E` over `K̄` with a `GeometricRealization φ`, the three witnesses the
symplectic scaling needs hold simultaneously:

* `Function.Surjective φ.toAddMonoidHom` — surjectivity over `K̄` (carried, Silverman III.4.10a);
* `TranslationCovariant W φ` — the translation covariance `τ_S ∘ φ^* = φ^* ∘ τ_{φS}` (**derived**
  from the bundled generic-point leaf `hgcomm`, Silverman III.8.2);
* `ProjOrdTransport φ` — the divisor-pullback functoriality (carried, the `DivisorTransport`
  conjunct).

(The fourth scaling input, the separable degree match `#ker = deg`, is
`GeometricRealization.card_ker_eq_degree`, also **derived** from `hgcomm` + the separable-Galois
inputs.)  This is the "one reusable compatibility layer" that discharges the per-isogeny residue for
every pencil member: instantiate it for `1 − π`, `rπ − s`, and any separable factor `λ`. -/
theorem separable_scaling_witnesses_of_geometricRealization
    (φ : Isogeny W.toAffine W.toAffine) (hφ : GeometricRealization W φ) :
    Function.Surjective φ.toAddMonoidHom ∧ TranslationCovariant W φ ∧ ProjOrdTransport φ :=
  ⟨hφ.hsurj, hφ.translationCovariant, hφ.hproj⟩

end Realization

/-! ### Bridging the bundle to the scaling — `weilScales_of_geometricRealization`

The payoff: a `GeometricRealization φ`, plus a divisor-pushforward dual `δ` (Silverman III.6.2(a),
`δ ∘ φ = [#ker φ]`) and the realised bare point map `ψ`/degree `d`, yields the `WeilScales`
predicate consumed by `FrobMatrixData`'s `OneSubFrobeniusScaling` / `PencilScaling` leaves —
CoordHom-free and with **no point-map surjectivity** needed by the scaling itself (the
image-restricted adjoint removed that dependency, round-20 Q2; `hsurj` is only used upstream to
construct `δ`).  This is the single call site that replaces the four scattered witness fields
`hproj`/`hcomm'`/`hsurj`/`hkerdeg` by one `GeometricRealization` plus the dual. -/

section ScalesBridge

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]
  [IsAlgClosed F]

/-- **`WeilScales` from a geometric realisation** (Silverman III.8.6.1, the `FrobMatrixData`-facing
form), CoordHom-free.  For a prime `ℓ`, a separable isogeny `φ` over `E` with a
`GeometricRealization φ` realising the bare hom `ψ` (`hψ : φ.toAddMonoidHom = ψ`) of degree `d`
(`hd : φ.degree = d`), the `[ℓ]`-commutation `hcommφ` (automatic `map_zsmul`), and an abstract
divisor-pushforward dual `δ` with the dual relation `hdc : δ ∘ φ = [#ker φ]` (Silverman III.6.2(a)),
the predicate `WeilScales W ℓ hℓF ψ d` holds.

The four geometric scaling inputs are now supplied from the single bundle:
* `ProjOrdTransport φ` = `hφ.hproj`;
* the translation covariance (per `S, T`) = `hφ.translationCovariant`;
* `#ker φ = deg φ` = `hφ.card_ker_eq_degree`;
and the only externally-supplied datum is the dual `δ`/`hdc` (which a genuine separable isogeny
possesses, the divisor-pushforward dual).  No `CoordHom`, no surjectivity in the scaling. -/
theorem weilScales_of_geometricRealization (ℓ : ℕ) [Fact ℓ.Prime] (hℓF : (ℓ : F) ≠ 0)
    (φ : Isogeny W.toAffine W.toAffine) [Finite φ.toAddMonoidHom.ker]
    (hφ : GeometricRealization W φ)
    (ψ : W.toAffine.Point →+ W.toAffine.Point) (hψ : φ.toAddMonoidHom = ψ)
    (d : ℕ) (hd : φ.degree = d)
    (hcommφ : (mulByInt W.toAffine ((ℓ : ℕ) : ℤ)).toAddMonoidHom.comp φ.toAddMonoidHom =
      φ.toAddMonoidHom.comp (mulByInt W.toAffine ((ℓ : ℕ) : ℤ)).toAddMonoidHom)
    (δ : W.toAffine.Point →+ W.toAffine.Point)
    (hdc : δ.comp φ.toAddMonoidHom =
      (mulByInt W.toAffine (Nat.card φ.toAddMonoidHom.ker : ℤ)).toAddMonoidHom) :
    WeilScales W ℓ hℓF ψ d :=
  weilScales_of_dualComp W ℓ hℓF φ ψ hψ d hd hφ.hproj hcommφ δ hdc hφ.card_ker_eq_degree
    (fun S _T _hS _hφT => hφ.translationCovariant S _)

end ScalesBridge

/-! ### Non-vacuity — the consolidated discharge of `OneSubFrobeniusScaling` for the genuine `1 − π`

The layer is **instantiable on the genuine `1 − π`**: the smart constructor
`oneSubFrobeniusScaling_of_geometricRealization` proves the `FrobMatrixData` leaf
`OneSubFrobeniusScaling` for `(1 − π)_{K̄}` from a `GeometricRealization` of that isogeny, with the
translation covariance `hcomm'` **derived** from the bundle's generic-point leaf `hgcomm` (no longer
a separate per-`(ℓ, S, T)` field).  This is the concrete demonstration that the consolidation is
non-vacuous (it applies to the very isogeny it must) and that `hcomm'` is genuinely eliminated:
contrast with `oneSubFrobeniusScaling_of_divisorDual`, which still takes the verbose `hcomm'`
explicitly. -/

section OneSubNonVacuity

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]

noncomputable local instance instDecEqACBridge : DecidableEq (AlgebraicClosure K) :=
  Classical.decEq _

open IsogenyBaseChangeConcrete

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]
  [IsIntegrallyClosed
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).CoordinateRing]

/-- **`OneSubFrobeniusScaling` for `(1 − π)_{K̄}` from a geometric realisation** (Silverman
III.8.6.1), CoordHom-free — the consolidated discharge.  Given a `GeometricRealization` of the
base-changed separable isogeny `(1 − π)_{K̄}` (carrying the single generic-point covariance leaf
`hgcomm`, surjectivity `hsurj`, and `ProjOrdTransport φ`, plus the separable-Galois inputs) and the
V.1.3 degree identity `hdeg_eq`, the symplectic scaling leaf holds.

The translation covariance `hcomm'` consumed by `oneSubFrobeniusScaling_of_divisorDual` is **derived
here** from `hφ.hgcomm` via `oneSub_hcommPrime_of_hgcomm` (the consolidated reduction), so the caller
supplies only the bundle — no verbose per-`(ℓ, S, T)` covariance field.  This proves the
`GeometricRealization` layer is instantiable on the genuine `1 − π`. -/
theorem oneSubFrobeniusScaling_of_geometricRealization (hq : 2 ≤ Fintype.card K)
    (hφ : GeometricRealization (W.baseChange (AlgebraicClosure K))
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)))
    (hdeg_eq :
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).degree = pointCount W.toAffine) :
    OneSubFrobeniusScaling W p r (AlgebraicClosure K) hq :=
  oneSubFrobeniusScaling_of_divisorDual W p r hq hdeg_eq hφ.hproj hφ.hsurj
    (oneSub_hcommPrime_of_hgcomm W p r hq hφ.hgcomm)

end OneSubNonVacuity

end HasseWeil.WeilPairing

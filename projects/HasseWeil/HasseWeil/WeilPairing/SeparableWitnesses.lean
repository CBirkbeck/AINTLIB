/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.SeparableKernelTorsor
import HasseWeil.WallA.VSideDual
import HasseWeil.WeilPairing.HcommLemma
import HasseWeil.WeilPairing.OneSubWitnesses
import HasseWeil.WeilPairing.PencilDualDivisor

/-!
# The shared separable witnesses for `(1 − π)_{K̄}` and `(rπ − s)_{K̄}` (CoordHom-free)

Route 2A reduces the Hasse bound to the symplectic Weil-pairing scalings of the base-changed
*separable* isogenies `(1 − π)_{K̄}` and `(rπ − s)_{K̄}` over `L = AlgebraicClosure K`, both
discharged CoordHom-free via the divisor-pushforward dual (`OneSubDualDivisor.lean`,
`PencilDualDivisor.lean`).  Those leaf discharges consume, *per isogeny*, the same family of
standard per-isogeny witnesses:

1. `hsurj`  — surjectivity of `φ.toAddMonoidHom` on `E_{K̄}`-points (Silverman III.4.10a);
2. `#ker φ = deg φ` (Silverman III.4.10c) — for `rπ − s` (for `1 − π` it is done via V.1.3);
3. `hcomm'` — the translation covariance `τ_S ∘ φ^* = φ^* ∘ τ_{φS}` (Silverman III.8.2);
4. `ProjOrdTransport φ` — divisor-pullback functoriality (the deepest, assessed in the module
   docstring of `DivisorPullback.lean`; *not* attacked here).

This file supplies witnesses **1–3** as far as the project's *abstract* `Isogeny` interface allows,
reducing each to a single precisely-stated CoordHom-free named leaf where a genuinely-geometric
input remains.  **No characteristic polynomial / trace relation / dual additivity (Route 1); no
`Isogeny.CoordHom`.**

## What is proved here (CoordHom-free, no `sorry` in finished decls)

### Witness 3 — `hcomm'` (the translation covariance), for **both** isogenies, uniformly

`hcomm'` is the pointwise covariance `τ_S(φ^* z) = φ^*(τ_{φS} z)` applied to `z = weilFunction …`.
The shipped `hcomm_of_isGenuineWith` (`HcommLemma.lean`) proves *exactly* this from two inputs:

* `IsGenuineWith W φ g` — **free** for the canonical action `g = Affine.Point.map φ.pullback`
  (`isogeny_isGenuineWith_pointMap`, `WallA/VSideDual.lean`); and
* `hgcomm` — the *generic-point* commutation
  `Point.map τ_S (g P_gen) = g P_gen + lift (φ S)`,
  i.e. `φ(P_gen + S) = φ(P_gen) + φ(S)` read at the generic point for the canonical pullback action.

So the **only** residual content of `hcomm'` is `hgcomm`.  `hcommPrime_of_hgcomm` packages this:
for *any* isogeny `φ` over *any* field, given `hgcomm` (per `S`), it produces the full `hcomm'`
field shape (per `ℓ, S, T`).  Instantiated at `(1 − π)_{K̄}` (`oneSub_hcommPrime_of_hgcomm`) and at
`(rπ − s)_{K̄}` (`pencil_hcommPrime_of_hgcomm`), this discharges witness 3 for both, **modulo the
single CoordHom-free leaf `hgcomm`** (= `MapTranslateGenericPoint` below).

`hgcomm` is genuinely a separate geometric fact for these isogenies (unlike `[ℓ]`, where it is the
shipped hypothesis-free `ScratchCov.comm_point_mulByInt`, available only because the explicit
division-polynomial coordinate formula gives `Point.map [ℓ]^* P_gen = ℓ • P_gen`).  For `1 − π` and
`rπ − s` there is *no* such coordinate formula in the project, so `Point.map φ^* P_gen` is not
computable in closed form and `hgcomm` cannot be derived from the abstract `Isogeny` fields — it is
the function-field shadow of the group-law identity, carried per isogeny.

### Witness 2 — `#ker (rπ − s)_{K̄} = deg (rπ − s)_{K̄}` (the separable degree match)

`pencil_hkerdeg_of_separable_witnesses` reduces this, via the **general** reviewer-endorsed Galois
fibre-count `card_kernel_eq_degree_of_separable_isogeny` (`EC/SeparableKernelTorsor.lean`,
axiom-clean modulo its two coherence inputs), to the three standard separable-isogeny facts over
`K̄`:

* `hsep`     — `(rπ − s)_{K̄}` is separable (Silverman III.5.5 / Th 5.6: `(rπ − s)^*ω = −s·ω ≠ 0`
  for `p ∤ s`, since `π^*ω = 0`);
* `h_normal` — `K(E_{K̄}) / (rπ − s)^* K(E_{K̄})` is normal;
* `h_card`   — the kernel ↔ Galois-group bijection `#ker = #Aut`.

For `1 − π` the analogous match is **already done** in `OneSubWitnesses.lean`
(`oneSubFrobeniusIsogBaseChange_hkerdeg_of_degree_eq_pointCount`, via `#ker = pointCount` + V.1.3),
re-exported here for the shared table as `oneSub_hkerdeg_of_degree_eq_pointCount`.

### Witness 1 — `hsurj` (surjectivity over `K̄`)

**Isolated, with a precise CoordHom-free signature, and a depth note explaining why it is not
free.**  The only *proved* point-map surjectivity in the project is `mulByInt_point_surjective`
(`[N]` over `K̄`, via division polynomials).  There is **no** general "nonconstant isogeny is
surjective over `K̄`" theorem (that needs genuine AG: a finite morphism of complete curves is closed
and dominant, hence surjective; or equivalently the dual).  The reduction
`…_hsurj_of_self_comp_dual` (`OneSubWitnesses.lean`) derives `hsurj` from the *other* dual
composition `φ ∘ δ = [#ker]`, but the divisor-pushforward dual `divisorPushforwardDual` provides
only `δ ∘ φ = [#ker]` (`divisorPushforwardDual_comp`) and, crucially, *requires `hsurj` as an input*
(to make `φ^*` multiply divisor degrees by `#ker`).  So that route is **circular** for this dual:
`hsurj` cannot be obtained from the divisor-pushforward dual, and is carried as a genuine
per-isogeny witness.  `HsurjWitness` records the exact statement for both isogenies.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.4.10a/c, III.5.5, III.6.1b/6.2a, III.8.2,
  III.8.6.1, V.1.3.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.WeilPairing.DivisorPullback HasseWeil.WeilPairing.TorsionGeometric

-- `oneSub_hsurj_of_self_comp_dual` carries `[Fintype W.toAffine.Point]` for the underlying
-- `OneSubWitnesses.lean` reduction, where it is structurally required though absent from this type.
set_option linter.unusedFintypeInType false

section CovarianceGeneral

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-- **The generic-point commutation leaf `hgcomm`** (Silverman III.8.2, generic-point form), for the
**canonical** geometric action `g = Affine.Point.map φ.pullback`.  This is the single residual of
the translation covariance: translating the generic-point image `g(P_gen) = (φ^* x_gen, φ^* y_gen)`
by `S` adds the lift of `φ(S)`,

  `Point.map τ_S (Point.map φ^* P_gen) = Point.map φ^* P_gen + lift (φ.toAddMonoidHom S)`,

i.e. `φ(P_gen + S) = φ(P_gen) + φ(S)` read at the generic point for the canonical pullback action.

This is **genuinely geometric content**, not derivable from the abstract `Isogeny` fields:
`Point.map φ^* P_gen` is not computable in closed form for a general `φ` (for `[ℓ]` it equals
`ℓ • P_gen` only via the explicit division-polynomial coordinate formula `mulByInt_pullback_x/y`,
the shipped `ScratchCov.map_pullback_genericPoint`).  It is the function-field shadow of the
group-law homomorphism property of `φ`, carried per isogeny.

We phrase the leaf against an abstract genuine action `g` (with `IsGenuineWith W φ g`), so the
`+ lift (φ S)` typechecks against `g`'s codomain `(W_KE W).toAffine.Point` (avoiding the
`W_KE` / `W.baseChange (FunctionField)` `HAdd` diamond raised by writing `Point.map φ^*` raw); for
the canonical action `g = Affine.Point.map φ.pullback` (the **free** genuineness
`isogeny_isGenuineWith_pointMap`) we have `g (P_gen) = Point.map φ^* (P_gen)`
(`map_pullback_genericPoint_of_isGenuineWith`), so this is exactly the generic-point commutation for
the canonical pullback action. -/
def MapTranslateGenericPoint (φ : Isogeny W.toAffine W.toAffine)
    (g : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point) : Prop :=
  ∀ S : W.toAffine.Point,
    WeierstrassCurve.Affine.Point.map (W' := W)
        (HasseWeil.translateAlgEquivOfPoint W S).toAlgHom (g (HasseWeil.genericPoint W)) =
      g (HasseWeil.genericPoint W) + HasseWeil.liftPointToKE W (φ.toAddMonoidHom S)

/-- **The translation covariance, pointwise, from the generic-point leaf** (Silverman III.8.2).  For
*any* isogeny `φ` genuine with action `g` (e.g. the **free** canonical action
`Affine.Point.map φ.pullback`, `isogeny_isGenuineWith_pointMap`), given
`MapTranslateGenericPoint φ g` (the generic-point commutation `hgcomm`), the covariance
`τ_S(φ^* z) = φ^*(τ_{φS} z)` holds for every `z`.  Pure application of the shipped
`hcomm_of_isGenuineWith` (whose `hgcomm` hypothesis is exactly
`hgcomm S`). -/
theorem hcomm_of_mapTranslateGenericPoint (φ : Isogeny W.toAffine W.toAffine)
    {g : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point} (hgen : IsGenuineWith W φ g)
    (hgcomm : MapTranslateGenericPoint W φ g) (S : W.toAffine.Point)
    (z : W.toAffine.FunctionField) :
    HasseWeil.translateAlgEquivOfPoint W S (φ.pullback z) =
      φ.pullback (HasseWeil.translateAlgEquivOfPoint W (φ.toAddMonoidHom S) z) :=
  hcomm_of_isGenuineWith W φ hgen S (hgcomm S) z

/-- **The translation covariance for the canonical action** (Silverman III.8.2): the convenience
form of `hcomm_of_mapTranslateGenericPoint` specialised to the **free** canonical genuine action
`g = Affine.Point.map φ.pullback` (`isogeny_isGenuineWith_pointMap`).  Consumes only the
generic-point leaf for that action; it is the form the two base-changed instances use. -/
theorem hcomm_of_mapTranslateGenericPoint_canonical (φ : Isogeny W.toAffine W.toAffine)
    (hgcomm : MapTranslateGenericPoint W φ
      (WeierstrassCurve.Affine.Point.map (W' := W) φ.pullback))
    (S : W.toAffine.Point) (z : W.toAffine.FunctionField) :
    HasseWeil.translateAlgEquivOfPoint W S (φ.pullback z) =
      φ.pullback (HasseWeil.translateAlgEquivOfPoint W (φ.toAddMonoidHom S) z) :=
  hcomm_of_mapTranslateGenericPoint W φ (HasseWeil.WallA.isogeny_isGenuineWith_pointMap W φ)
    hgcomm S z

/-- **The kernel-translation invariance `hcov` from the *same* generic-point leaf** (Silverman
III.4.10c, the input to the Galois fibre-count's concrete form).  For `k ∈ ker φ`, translation by
`k` fixes the pullback range: `τ_k(φ^* z) = φ^* z` for all `z`.

This is the covariance `hcomm_of_mapTranslateGenericPoint_canonical` specialised to `S = k ∈ ker φ`:
there `φ(k) = 0`, so `τ_{φ(k)} = τ_0 = AlgEquiv.refl` (`translateAlgEquivOfPoint_zero`) and the
right-hand side collapses to `φ^* z`.  Hence the `hcov` input of
`card_kernel_eq_degree_of_separable_concrete` (witness 2) and the translation covariance `hcomm'`
(witness 3) share the **same** geometric leaf `MapTranslateGenericPoint`. -/
theorem hcov_of_mapTranslateGenericPoint_canonical (φ : Isogeny W.toAffine W.toAffine)
    (hgcomm : MapTranslateGenericPoint W φ
      (WeierstrassCurve.Affine.Point.map (W' := W) φ.pullback))
    (k : φ.kernel) (z : W.toAffine.FunctionField) :
    HasseWeil.translateAlgEquivOfPoint W k.val (φ.pullback z) = φ.pullback z := by
  rw [hcomm_of_mapTranslateGenericPoint_canonical W φ hgcomm k.val z,
    (Isogeny.mem_kernel_iff φ k.val).mp k.property]
  rfl

end CovarianceGeneral

section CovarianceInstances

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]

noncomputable local instance instDecEqACSW : DecidableEq (AlgebraicClosure K) := Classical.decEq _

open IsogenyBaseChangeConcrete

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]

/-- **Witness 3 for `(1 − π)_{K̄}` — `hcomm'`, reduced to `hgcomm`** (Silverman III.8.2),
CoordHom-free.  Given the generic-point commutation leaf `MapTranslateGenericPoint` for
`(1 − π)_{K̄}`, the full `hcomm'` field of `OneSubScalingData` holds.  Pure instantiation of
`hcomm_of_mapTranslateGenericPoint` at `z = weilFunction …`. -/
theorem oneSub_hcommPrime_of_hgcomm (hq : 2 ≤ Fintype.card K)
    (hgcomm : MapTranslateGenericPoint (W.baseChange (AlgebraicClosure K))
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
      (WeierstrassCurve.Affine.Point.map (W' := W.baseChange (AlgebraicClosure K))
        (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
          (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback)) :
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
                (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom T) hφT)) := by
  intro ℓ hℓF S T _hS hφT
  exact hcomm_of_mapTranslateGenericPoint_canonical (W.baseChange (AlgebraicClosure K))
    (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)) hgcomm S _

/-- **Witness 3 for `(rπ − s)_{K̄}` — `hcomm'`, reduced to `hgcomm`** (Silverman III.8.2),
CoordHom-free.  Given the generic-point commutation leaf `MapTranslateGenericPoint` for
`(rπ − s)_{K̄}`, the full `hcomm'` field of `PencilScalingData` holds.  Pure instantiation of
`hcomm_of_mapTranslateGenericPoint` at `z = weilFunction …`. -/
theorem pencil_hcommPrime_of_hgcomm (r' s' : ℤ)
    (pullback_L : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[AlgebraicClosure K]
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField)
    (hgcomm : MapTranslateGenericPoint (W.baseChange (AlgebraicClosure K))
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L)
      (WeierstrassCurve.Affine.Point.map (W' := W.baseChange (AlgebraicClosure K))
        (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).pullback)) :
    ∀ (ℓ : ℕ) (hℓF : (ℓ : AlgebraicClosure K) ≠ 0)
      (S T : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
      (_hS : ((ℓ : ℕ) : ℤ) • S = 0)
      (hφT : ((ℓ : ℕ) : ℤ) •
        (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).toAddMonoidHom T = 0),
      translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S
          ((pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).pullback
            (weilFunction (W.baseChange (AlgebraicClosure K)) ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
              ((pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).toAddMonoidHom T)
              hφT)) =
        (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).pullback
          (translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
            ((pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).toAddMonoidHom S)
            (weilFunction (W.baseChange (AlgebraicClosure K)) ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
              ((pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).toAddMonoidHom T)
              hφT)) := by
  intro ℓ hℓF S T _hS hφT
  exact hcomm_of_mapTranslateGenericPoint_canonical (W.baseChange (AlgebraicClosure K))
    (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L) hgcomm S _

end CovarianceInstances

section KerDegPencil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]

noncomputable local instance instDecEqACKD : DecidableEq (AlgebraicClosure K) := Classical.decEq _

open IsogenyBaseChangeConcrete

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]

/-- **Witness 2 for `(rπ − s)_{K̄}` — `#ker = deg`, reduced to the separable-Galois witnesses**
(Silverman III.4.10c), CoordHom-free.  Via the general Galois fibre-count
`card_kernel_eq_degree_of_separable_isogeny`, the separable degree match `#ker φ_L = deg φ_L` for
`φ_L = (rπ − s)_{K̄}` follows from:

* `hsep`     — separability of `φ_L` (Silverman III.5.5: `(rπ − s)^*ω = −s·ω ≠ 0` for `p ∤ s`);
* `h_normal` — normality of `K(E_{K̄}) / φ_L^* K(E_{K̄})`;
* `h_card`   — the kernel ↔ Galois-group bijection `#ker φ_L = #Aut(K(E_{K̄}) / φ_L^* K(E_{K̄}))`.

This is the reviewer-endorsed (round 19 Q1) general route, supplying exactly the
`PencilScalingData.hkerdeg` field. -/
theorem pencil_hkerdeg_of_separable_witnesses (r' s' : ℤ)
    (pullback_L : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[AlgebraicClosure K]
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField)
    (hsep : (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).IsSeparable)
    (h_normal : letI := (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).toAlgebra
      Normal (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField)
    (h_card :
      Nat.card (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).kernel =
        Nat.card (@AlgEquiv
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField _ _ _
          (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).toAlgebra
          (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).toAlgebra)) :
    Nat.card (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).toAddMonoidHom.ker =
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).degree :=
  card_kernel_eq_degree_of_separable_isogeny (W.baseChange (AlgebraicClosure K))
    (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L) hsep h_normal h_card

/-- **Witness 2 for `(rπ − s)_{K̄}` — `#ker = deg`, concrete form sharing the `hgcomm` leaf**
(Silverman III.4.10c), CoordHom-free.  Routes through the *concrete* Galois fibre-count
`card_kernel_eq_degree_of_separable_concrete`, whose `hcov` (kernel-translation invariance) is
discharged here from the **same** generic-point leaf `MapTranslateGenericPoint` used by witness 3
(`hcov_of_mapTranslateGenericPoint_canonical`).  So `#ker (rπ − s)_{K̄} = deg` is reduced to:

* `hgcomm`   — the generic-point commutation `MapTranslateGenericPoint φ_L (Point.map φ_L^*)`
  (shared with witness 3's `hcomm'`);
* `hsep`     — separability of `φ_L` (Silverman III.5.5: `(rπ − s)^*ω = −s·ω ≠ 0` for `p ∤ s`);
* `h_normal` — normality of `K(E_{K̄}) / φ_L^* K(E_{K̄})`;
* `hdesc`    — the generic-point translation torsor: every `σ(P_gen) − P_gen` is an `F`-rational
  kernel point (Silverman III.4.10c).

This is the maximally-shared reduction: witnesses 2 and 3 bottom out at the *single* leaf `hgcomm`
together with the standard separable/normal/descent inputs. -/
theorem pencil_hkerdeg_of_hgcomm_separable (r' s' : ℤ)
    (pullback_L : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[AlgebraicClosure K]
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField)
    (hgcomm : MapTranslateGenericPoint (W.baseChange (AlgebraicClosure K))
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L)
      (WeierstrassCurve.Affine.Point.map (W' := W.baseChange (AlgebraicClosure K))
        (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).pullback))
    (hsep : (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).IsSeparable)
    (h_normal : letI := (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).toAlgebra
      Normal (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField)
    (hdesc : ∀ σ : (@AlgEquiv
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField _ _ _
        (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).toAlgebra
        (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).toAlgebra),
      ∃ k : (W.baseChange (AlgebraicClosure K)).toAffine.Point,
        k ∈ (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).kernel ∧
        HasseWeil.liftPointToKE (W.baseChange (AlgebraicClosure K)) k =
          HasseWeil.genericPointAct (W.baseChange (AlgebraicClosure K))
            (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L) σ -
            HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K))) :
    Nat.card (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).toAddMonoidHom.ker =
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).degree :=
  HasseWeil.card_kernel_eq_degree_of_separable_concrete (W.baseChange (AlgebraicClosure K))
    (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L) hsep
    (fun k z ↦ hcov_of_mapTranslateGenericPoint_canonical (W.baseChange (AlgebraicClosure K))
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L) hgcomm k z)
    h_normal hdesc

/-- **Witness 2 for `(1 − π)_{K̄}` — `#ker = deg` (re-export)**, CoordHom-free.  Already proved in
`OneSubWitnesses.lean` via `#ker = pointCount` (the geometric-Frobenius fixed locus) + V.1.3
`deg(1 − π) = #E(𝔽_q)`; re-stated here for the shared witness table.  Axiom-clean modulo the V.1.3
degree identity `hdeg_eq`. -/
theorem oneSub_hkerdeg_of_degree_eq_pointCount [Fintype W.toAffine.Point] (hq : 2 ≤ Fintype.card K)
    (hdeg_eq :
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).degree = pointCount W.toAffine) :
    Nat.card (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom.ker =
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).degree :=
  oneSubFrobeniusIsogBaseChange_hkerdeg_of_degree_eq_pointCount W p r
    (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq) hdeg_eq

end KerDegPencil

section SurjWitness

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]

noncomputable local instance instDecEqACSurj : DecidableEq (AlgebraicClosure K) := Classical.decEq _

open IsogenyBaseChangeConcrete

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]

/-- **Witness 1 — the surjectivity statement carried per isogeny** (Silverman III.4.10a).  For a
base-changed point map `φ_L.toAddMonoidHom` over `L = AlgebraicClosure K`, `hsurj` is exactly
`Function.Surjective φ_L.toAddMonoidHom`.  This is the precise CoordHom-free signature the leaf
discharges consume (the `hsurj` arguments of `mkOneSubScalingDataConcrete_of_divisorDual` and
`PencilScalingData.hsurj`); it is **not** derivable here (the divisor-pushforward dual needs it as
an input, and the project has no general isogeny-surjectivity theorem), so it is carried.

The standard mathematics: a nonconstant isogeny of elliptic curves is a finite morphism of complete
smooth curves, hence has closed dominant image, hence is surjective on `K̄`-points; equivalently it
follows from the dual `φ ∘ φ̂ = [deg φ]` together with surjectivity of `[deg φ]`
(`mulByInt_point_surjective`).  Both `1 − π` (`deg = #E(𝔽_q) > 0`) and `rπ − s` (`deg > 0`) are
nonconstant. -/
def HsurjWitness (φ : Isogeny (W.baseChange (AlgebraicClosure K)).toAffine
    (W.baseChange (AlgebraicClosure K)).toAffine) : Prop :=
  Function.Surjective φ.toAddMonoidHom

/-- **`hsurj` for `(1 − π)_{K̄}` from a supplied dual self-composition** (Silverman III.4.10a/b),
CoordHom-free.  Re-export of the `OneSubWitnesses.lean` reduction: from *any* `δ` with
`φ_L ∘ δ = [N]` (the dual's *second* composition) and `(N : K̄) ≠ 0`, surjectivity of `φ_L` follows
via `mulByInt_point_surjective`.  Provided here for the shared table; note that the
divisor-pushforward dual does **not** supply this `φ_L ∘ δ = [N]` direction (only `δ ∘ φ_L = [N]`),
so this consumes an externally-supplied `hself`, not the divisor-pushforward dual. -/
theorem oneSub_hsurj_of_self_comp_dual [Fintype W.toAffine.Point] (hq : 2 ≤ Fintype.card K)
    (δ : (W.baseChange (AlgebraicClosure K)).toAffine.Point →+
      (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (N : ℤ) (hN : (N : AlgebraicClosure K) ≠ 0)
    (hself :
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
          (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom.comp δ =
        (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine N).toAddMonoidHom) :
    Function.Surjective
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom :=
  oneSubFrobeniusIsogBaseChange_hsurj_of_self_comp_dual W p r
    (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq) δ N hN hself

/-- **`hsurj` for `(rπ − s)_{K̄}` from a supplied dual self-composition** (Silverman III.4.10a/b),
CoordHom-free.  Mirror of `oneSub_hsurj_of_self_comp_dual` for the pencil: from any `δ` with
`φ_L ∘ δ = [N]` and `(N : K̄) ≠ 0`, surjectivity of `φ_L` follows via `mulByInt_point_surjective`.
(Again, the divisor-pushforward dual does not supply this direction, so `hself` is external.) -/
theorem pencil_hsurj_of_self_comp_dual (r' s' : ℤ)
    (pullback_L : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[AlgebraicClosure K]
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField)
    (δ : (W.baseChange (AlgebraicClosure K)).toAffine.Point →+
      (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (N : ℤ) (hN : (N : AlgebraicClosure K) ≠ 0)
    (hself :
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).toAddMonoidHom.comp δ =
        (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine N).toAddMonoidHom) :
    Function.Surjective
      (pencilIsogBaseChange W p r (AlgebraicClosure K) r' s' pullback_L).toAddMonoidHom := by
  intro Q
  obtain ⟨R, hR⟩ := mulByInt_point_surjective (W.baseChange (AlgebraicClosure K)) N hN Q
  refine ⟨δ R, ?_⟩
  have hval := DFunLike.congr_fun hself R
  rw [AddMonoidHom.comp_apply] at hval
  rw [hval]
  rwa [mulByInt_apply] at hR ⊢

end SurjWitness

end HasseWeil.WeilPairing

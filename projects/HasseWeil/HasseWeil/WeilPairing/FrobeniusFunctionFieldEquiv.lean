/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The arithmetic Frobenius automorphism `σ` of the function field `K̄(E)`

This file constructs, for a finite field `K` with `q = #K` and a Weierstrass curve `W` over `K`
base-changed to `K̄ = AlgebraicClosure K`, the **arithmetic Frobenius** ring automorphism

```
frobeniusFunctionFieldEquiv : K̄(E) ≃+* K̄(E)
```

of the function field `K̄(E) = (W.baseChange K̄).toAffine.FunctionField`.  It is the `q`-power
arithmetic Frobenius `e = FiniteField.frobeniusAlgEquivOfAlgebraic K K̄` on the `K̄`-coefficients
(`a ↦ a^q`, fixing `K`, hence the `𝔽_q`-rational generators `x_gen, y_gen`), transported to the
function field.

## Construction

* `e : K̄ ≃ₐ[K] K̄` — the `q`-power coefficient Frobenius (`frobeniusAlgEquivOfAlgebraic`), fixing `K`.
* `CoordinateRing.map e : R[E] →+* R'[E.map e]` (mathlib) — but since `e` fixes `K`, the mapped curve
  `(W.baseChange K̄).map e` *equals* `W.baseChange K̄` (`frobeniusGalois_baseChange_map_eq`).  We prove
  `CoordinateRing.map e` is **bijective** (`coordRingMap_bijective`: injective by `map_injective` of
  the injective `e`; surjective by lifting `e.symm` through `AdjoinRoot.mk` and `Polynomial.map`), so
  it packages as a ring iso `crEquiv : R[E] ≃+* R'[E.map e]`.
* `IsFractionRing.ringEquivOfRingEquiv crEquiv` lifts it to the fraction fields, and a
  `RingEquiv.cast` along the curve equality `(W.baseChange K̄).map e = W.baseChange K̄` returns the
  codomain to `K̄(E)`, giving the *endomorphism* `frobeniusFunctionFieldEquiv`.

## What this file proves (axiom-clean, no `sorry`)

* `coordRingMap_bijective` — `CoordinateRing.map e` is bijective for a ring **equiv** `e`.
* `coordRingMap_algebraMap_base` — `CoordinateRing.map f` on a base constant `algebraMap a` is
  `algebraMap (f a)` (the `q`-power on coefficients, at the coordinate-ring level).
* `frobeniusFunctionFieldEquiv` — the arithmetic Frobenius `σ` of `K̄(E)`.
* `frobeniusFunctionFieldEquiv_algebraMap` — the **`q`-power on constants**
  `σ(algebraMap a) = algebraMap (a ^ #K)`, the third (elementary) hypothesis of
  `FrobeniusGaloisData` / `weilPairing_galois_core`.

The two remaining (geometric) hypotheses of `FrobeniusGaloisData` — the translation conjugation
`σ ∘ τ_S = τ_{π̄ S} ∘ σ` and the `σ`-naturality `σ(g_T) = c · g_{π̄ T}` (divisor Galois descent) —
are *not* in this file; see `FrobeniusGaloisScaling.lean` (`frobeniusGaloisData_holds`).

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.8.1 (Galois equivariance of the Weil pairing).
-/

open WeierstrassCurve Polynomial

namespace HasseWeil.WeilPairing

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

/-! ### Generic `CoordinateRing.map` facts (any base ring) -/

/-- **`CoordinateRing.map f` on a base constant** `algebraMap a` is `algebraMap (f a)`.  The
coordinate-ring shadow of "a field map acts on the constant coefficients": `algebraMap R R[E] a =
mk (C (C a))`, and `CoordinateRing.map f` sends `mk x ↦ mk (x.map (mapRingHom f))`, which sends
`C (C a) ↦ C (C (f a)) = algebraMap S (E.map f)[E] (f a)`. -/
theorem coordRingMap_algebraMap_base {R S : Type*} [CommRing R] [CommRing S]
    (W' : WeierstrassCurve.Affine R) (f : R →+* S) (a : R) :
    WeierstrassCurve.Affine.CoordinateRing.map W' f (algebraMap R W'.CoordinateRing a) =
      algebraMap S (W'.map f).toAffine.CoordinateRing (f a) := by
  have h1 : (algebraMap R W'.CoordinateRing a) =
      WeierstrassCurve.Affine.CoordinateRing.mk W' (C (C a)) := by
    change (AdjoinRoot.of W'.polynomial).comp (algebraMap R R[X]) a = _
    rw [RingHom.comp_apply, AdjoinRoot.of]
    rfl
  rw [h1, WeierstrassCurve.Affine.CoordinateRing.map_mk]
  have h2 : ((C (C a)).map (mapRingHom f)) = C (C (f a)) := by
    simp only [Polynomial.map_C, coe_mapRingHom]
  rw [h2]
  change (AdjoinRoot.mk (W'.map f).toAffine.polynomial) (C (C (f a))) = _
  rw [show (algebraMap S (W'.map f).toAffine.CoordinateRing (f a)) =
      (AdjoinRoot.of (W'.map f).toAffine.polynomial).comp (algebraMap S S[X]) (f a) from rfl,
    RingHom.comp_apply, AdjoinRoot.of]
  rfl

section BaseChange

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

noncomputable local instance instDecEqACFFE : DecidableEq (AlgebraicClosure K) := Classical.decEq _

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]

/-- **The `q`-power coefficient Frobenius** `e : K̄ ≃+* K̄`, `a ↦ a^q`, fixing `K` (`𝔽_q`).  This is
`FiniteField.frobeniusAlgEquivOfAlgebraic K K̄` as a `RingEquiv`. -/
noncomputable abbrev coeffFrobEquiv : AlgebraicClosure K ≃+* AlgebraicClosure K :=
  (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)).toRingEquiv

@[simp] theorem coeffFrobEquiv_apply (a : AlgebraicClosure K) :
    coeffFrobEquiv (K := K) a = a ^ Fintype.card K := by
  show (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) a = a ^ Fintype.card K
  rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]

/-- **The `q`-power coefficient Frobenius fixes the curve** `W.baseChange K̄` (as a `WeierstrassCurve`):
mapping `W.baseChange K̄` along `e = frobeniusAlgEquivOfAlgebraic K K̄` returns `W.baseChange K̄`,
because `e` is a `K`-algebra hom and so fixes `algebraMap K K̄`.  Direct from `map_map` +
`e.commutes`. -/
theorem frobeniusGalois_baseChange_map_eq :
    (W.baseChange (AlgebraicClosure K)).map
        (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)).toAlgHom.toRingHom =
      W.baseChange (AlgebraicClosure K) := by
  rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
  congr 1
  ext x
  change (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)).toAlgHom.toRingHom.comp
      (algebraMap K (AlgebraicClosure K)) x = algebraMap K (AlgebraicClosure K) x
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_algHom]
  exact (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)).commutes x

/-- **`CoordinateRing.map e` is surjective** for a ring **equiv** `e` of the base field: every
`mk q` in the target is the image of `mk (q.map (mapRingHom e.symm))`, since `e ∘ e.symm = id`. -/
theorem coordRingMap_surjective (e : AlgebraicClosure K ≃+* AlgebraicClosure K) :
    Function.Surjective
      (WeierstrassCurve.Affine.CoordinateRing.map (W.baseChange (AlgebraicClosure K)).toAffine
        (e : AlgebraicClosure K →+* AlgebraicClosure K)) := by
  intro y
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
  refine ⟨AdjoinRoot.mk _ (q.map (Polynomial.mapRingHom
    (e.symm : AlgebraicClosure K →+* AlgebraicClosure K))), ?_⟩
  rw [WeierstrassCurve.Affine.CoordinateRing.map_mk]
  congr 1
  rw [Polynomial.map_map]
  have hid : (Polynomial.mapRingHom (e : AlgebraicClosure K →+* AlgebraicClosure K)).comp
      (Polynomial.mapRingHom (e.symm : AlgebraicClosure K →+* AlgebraicClosure K)) =
      RingHom.id (AlgebraicClosure K)[X] := by
    refine Polynomial.ringHom_ext ?_ ?_
    · intro a
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
        RingHom.id_apply, RingHom.coe_coe]
      rw [RingEquiv.apply_symm_apply]
    · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X, RingHom.id_apply]
  rw [hid, Polynomial.map_id]

/-- **`CoordinateRing.map e` is bijective** for a ring equiv `e` of the base field. -/
theorem coordRingMap_bijective (e : AlgebraicClosure K ≃+* AlgebraicClosure K) :
    Function.Bijective
      (WeierstrassCurve.Affine.CoordinateRing.map (W.baseChange (AlgebraicClosure K)).toAffine
        (e : AlgebraicClosure K →+* AlgebraicClosure K)) :=
  ⟨WeierstrassCurve.Affine.CoordinateRing.map_injective
    (W' := (W.baseChange (AlgebraicClosure K)).toAffine) (EquivLike.injective e),
   coordRingMap_surjective W e⟩

/-- **The coordinate-ring arithmetic Frobenius** `R[E] ≃+* R'[E.map e]`, packaging the bijective
`CoordinateRing.map e` (where `e = coeffFrobEquiv`) as a ring isomorphism. -/
noncomputable def crFrobEquiv :
    (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing ≃+*
      ((W.baseChange (AlgebraicClosure K)).map
        (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K)).toAffine.CoordinateRing :=
  RingEquiv.ofBijective _ (coordRingMap_bijective W (coeffFrobEquiv (K := K)))

@[simp] theorem crFrobEquiv_apply (z : (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing) :
    crFrobEquiv W z =
      WeierstrassCurve.Affine.CoordinateRing.map (W.baseChange (AlgebraicClosure K)).toAffine
        (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K) z := rfl

/-- **The function-field arithmetic Frobenius (raw)** `K̄(E) ≃+* K̄(E.map e)`, lifting `crFrobEquiv`
to fraction fields via `IsFractionRing.ringEquivOfRingEquiv`. -/
noncomputable def ffFrobEquivRaw :
    (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField ≃+*
      ((W.baseChange (AlgebraicClosure K)).map
        (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K)).toAffine.FunctionField :=
  IsFractionRing.ringEquivOfRingEquiv (crFrobEquiv W)

/-- **The curve equality** `(W.baseChange K̄).map e = W.baseChange K̄` for `e = coeffFrobEquiv`
(the coefficient `q`-power Frobenius fixes `K`).  Repackaging of `frobeniusGalois_baseChange_map_eq`
with `e` as a `RingEquiv`-coerced ring hom. -/
theorem map_coeffFrobEquiv_eq :
    (W.baseChange (AlgebraicClosure K)).map
        (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K) =
      W.baseChange (AlgebraicClosure K) := by
  have h := frobeniusGalois_baseChange_map_eq W
  convert h using 2
  rfl

/-- **The codomain `RingEquiv.cast`** `K̄(E.map e) ≃+* K̄(E)` along `map_coeffFrobEquiv_eq`. -/
noncomputable def ffFrobCast :
    ((W.baseChange (AlgebraicClosure K)).map
        (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K)).toAffine.FunctionField
      ≃+* (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField :=
  RingEquiv.cast (R := fun (V : WeierstrassCurve (AlgebraicClosure K)) => V.toAffine.FunctionField)
    (map_coeffFrobEquiv_eq W)

/-- **The arithmetic Frobenius automorphism `σ` of `K̄(E)`** (Silverman III.8.1, Galois route):
the `q`-power Frobenius of `K̄ / 𝔽_q` lifted to a ring automorphism of the function field `K̄(E)`,
acting as `a ↦ a^q` on the `K̄`-coefficients and fixing the `𝔽_q`-rational generators.  Built as
`ffFrobEquivRaw` (the fraction-field lift of `crFrobEquiv = CoordinateRing.map e`) followed by the
codomain `RingEquiv.cast` back to `K̄(E)` (`ffFrobCast`). -/
noncomputable def frobeniusFunctionFieldEquiv :
    (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField ≃+*
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField :=
  (ffFrobEquivRaw W).trans (ffFrobCast W)

/-! ### The `q`-power on constants (the elementary leaf of `FrobeniusGaloisData`) -/

/-- **`ffFrobEquivRaw` on a base constant**: `σ_raw(algebraMap a) = algebraMap (a ^ #K)` (into the
mapped curve's function field).  Factor `algebraMap K̄ K̄(E) = (algebraMap R[E] K̄(E)) ∘ (algebraMap K̄
R[E])` (`IsScalarTower`), push through `IsFractionRing.ringEquivOfRingEquiv_algebraMap` and
`coordRingMap_algebraMap_base`, and use `coeffFrobEquiv a = a^#K`. -/
theorem ffFrobEquivRaw_algebraMap (a : AlgebraicClosure K) :
    ffFrobEquivRaw W (algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) =
      algebraMap (AlgebraicClosure K)
        ((W.baseChange (AlgebraicClosure K)).map
          (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K)).toAffine.FunctionField
        (a ^ Fintype.card K) := by
  rw [show (algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) =
      algebraMap (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
        (algebraMap (AlgebraicClosure K)
          (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing a) from by
    rw [← IsScalarTower.algebraMap_apply]]
  rw [ffFrobEquivRaw, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    crFrobEquiv_apply, coordRingMap_algebraMap_base,
    show (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K) a = a ^ Fintype.card K
      from coeffFrobEquiv_apply a, ← IsScalarTower.algebraMap_apply]

/-- **`ffFrobCast` commutes with the base `algebraMap`**: the codomain `RingEquiv.cast` along the
curve equality `(W.baseChange K̄).map e = W.baseChange K̄` fixes every base constant `algebraMap b`.
By `subst` on the curve equality (then the cast is `rfl`). -/
theorem ffFrobCast_algebraMap (b : AlgebraicClosure K) :
    ffFrobCast W (algebraMap (AlgebraicClosure K)
        ((W.baseChange (AlgebraicClosure K)).map
          (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K)).toAffine.FunctionField b) =
      algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField b := by
  rw [ffFrobCast]
  have key : ∀ (V : WeierstrassCurve (AlgebraicClosure K))
      (h : V = W.baseChange (AlgebraicClosure K)),
      (RingEquiv.cast
          (R := fun (U : WeierstrassCurve (AlgebraicClosure K)) => U.toAffine.FunctionField) h)
        (algebraMap (AlgebraicClosure K) V.toAffine.FunctionField b) =
      algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField b := by
    intro V h; subst h; rfl
  exact key _ (map_coeffFrobEquiv_eq W)

/-- **The `q`-power on constants** (Silverman III.8.1, the elementary leaf of `FrobeniusGaloisData`):
the arithmetic Frobenius `σ = frobeniusFunctionFieldEquiv` `q`-powers the `K̄`-coefficients,
`σ(algebraMap a) = algebraMap (a ^ #K)`.  Composition of `ffFrobEquivRaw_algebraMap` (the raw lift)
and `ffFrobCast_algebraMap` (the codomain cast fixes constants). -/
theorem frobeniusFunctionFieldEquiv_algebraMap (a : AlgebraicClosure K) :
    frobeniusFunctionFieldEquiv W (algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) =
      algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (a ^ Fintype.card K) := by
  rw [frobeniusFunctionFieldEquiv, RingEquiv.trans_apply, ffFrobEquivRaw_algebraMap,
    ffFrobCast_algebraMap]

end BaseChange

end HasseWeil.WeilPairing

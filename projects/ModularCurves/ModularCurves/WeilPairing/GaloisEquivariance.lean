/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.HasseBound.WeilPairing.Pairing
import HasseWeil.HasseBound.WeilPairing.Constancy
import HasseWeil.HasseBound.WeilPairing.DivisorGalois
import HasseWeil.HasseBound.WeilPairing.FrobeniusFunctionFieldEquiv
import HasseWeil.HasseBound.WeilPairing.FrobeniusConjugation
import HasseWeil.Foundation.EC.AffinePointMap
import HasseWeil.Foundation.EC.SeparableKernelTorsor
import HasseWeil.Foundation.EC.Translation
import HasseWeil.Foundation.Curves.Valuation.NoFinitePolesBridge

/-!
# Galois equivariance of the field-level Weil pairing (T-C0c)

The T-C0c layer of the char-0 étale-descent Weil pairing chain (see
`ModularCurves/WeilPairing/EtaleDescent.lean`): the HasseWeil field-level Weil pairing
`HasseWeil.WeilPairing.weilPairing` (Silverman III.8.1) is equivariant under any ring
automorphism `σ : F ≃+* F` of the (algebraically closed) base field that fixes the curve,
`hW : W.map σ.toRingHom = W`:

  `σ (e_ℓ(S, T)) = e_ℓ(σ • S, σ • T)`,

where `σ • P` is the coordinatewise point action `pointHom W σ hW` (an `AddMonoidHom`,
built from `HasseWeil.Affine.Point.map` and a cast along `hW`). In the intended
application `F = k̄`, `σ ∈ Gal(k̄/k)` and `W` is the base change of a curve over `k`, so
`hW` holds; keeping `hW` as an explicit equation keeps this layer independent of the
base-change bookkeeping.

## Route (the σ-generalization of HasseWeil's arithmetic-Frobenius chain)

This file is the mirror, at an arbitrary curve-fixing `σ`, of HasseWeil's Frobenius chain
(`FrobeniusFunctionFieldEquiv.lean` → `FrobeniusConjugation.lean` →
`FrobeniusDivisorGalois.lean` → `Scaling/FrobeniusGalois.lean`), whose σ-transport toolkit
(`DivisorGalois.lean`) is already stated for arbitrary ring equivalences:

1. **Function-field automorphism** (`functionFieldEquiv`): `σ` induces
   `σ_KE : F(E) ≃+* F(E)` via the bijective `CoordinateRing.map σ`, the fraction-field
   lift, and a `RingEquiv.cast` along `hW`. It acts by `σ` on constants
   (`functionFieldEquiv_algebraMap`) and fixes the generators `x_gen`, `y_gen`.
2. **Point action** (`pointHom`): `σ • (x, y) = (σ x, σ y)`, an `AddMonoidHom` by
   `HasseWeil.Affine.Point.mapAddMonoidHom` + the `hW`-cast (`pointCastHom`).
3. **Translation conjugation** (`functionFieldEquiv_conj`):
   `σ_KE ∘ τ_S = τ_{σ•S} ∘ σ_KE`, proved on the generators via the explicit translation
   formulas (`translateX_xy`/`translateY_xy` are `σ_KE`-equivariant by `Affine.map_addX`
   etc. + `hW`) and upgraded by `ringHom_ext_base_x_y_gen`, mirroring
   `frobeniusFunctionFieldEquiv_conj` but avoiding the generic-point group law.
4. **σ-naturality of the Weil function** (`functionFieldEquiv_weilFunction_eq_smul`):
   `div(σ_KE g_T) = div(g_{σ•T})` place-by-place via the `DivisorGalois` valuation
   transport, whence `σ_KE g_T = c · g_{σ•T}` for a nonzero constant `c`.
5. **Constant-ratio core** (`weilPairing_ringEquiv_core`): the σ-action variant of
   `weilPairing_galois_core` — apply `σ_KE` to the defining relation
   `τ_S g_T = e_ℓ(S,T) · g_T` and cancel.
6. **Main theorem** (`weilPairing_galois_equivariant`): assembly of 1–5.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.8.1 (Galois equivariance).
-/

open WeierstrassCurve Polynomial IsDedekindDomain HasseWeil HasseWeil.Curves
  HasseWeil.WeilPairing

namespace ModularCurves

namespace WeilPairingGalois


variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) (σ : F ≃+* F)

/-! ### Layer 1 — the function-field automorphism induced by `σ` -/

set_option linter.unusedSectionVars false in
/-- **`CoordinateRing.map σ` is surjective** for a ring equivalence `σ` of the base field:
every `mk q` in the target is the image of `mk (q.map (mapRingHom σ.symm))`, since
`σ ∘ σ.symm = id`. Mirror of `HasseWeil.WeilPairing.coordRingMap_surjective` at an
arbitrary curve `W` and ring equivalence `σ`. -/
theorem coordRingMap_surjective_of_ringEquiv :
    Function.Surjective
      (WeierstrassCurve.Affine.CoordinateRing.map W.toAffine σ.toRingHom) := by
  intro y
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
  refine ⟨AdjoinRoot.mk _ (q.map (Polynomial.mapRingHom σ.symm.toRingHom)), ?_⟩
  rw [WeierstrassCurve.Affine.CoordinateRing.map_mk]
  congr 1
  rw [Polynomial.map_map]
  have hid : (Polynomial.mapRingHom σ.toRingHom).comp
      (Polynomial.mapRingHom σ.symm.toRingHom) = RingHom.id (Polynomial F) := by
    refine Polynomial.ringHom_ext ?_ ?_
    · intro a
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
        RingHom.id_apply]
      rw [show σ.toRingHom (σ.symm.toRingHom a) = a from σ.apply_symm_apply a]
    · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
        RingHom.id_apply]
  rw [hid, Polynomial.map_id]

/-- **`CoordinateRing.map σ` is bijective** for a ring equivalence `σ` of the base field. -/
theorem coordRingMap_bijective_of_ringEquiv :
    Function.Bijective
      (WeierstrassCurve.Affine.CoordinateRing.map W.toAffine σ.toRingHom) :=
  ⟨WeierstrassCurve.Affine.CoordinateRing.map_injective
    (W' := W.toAffine) σ.toRingHom.injective,
   coordRingMap_surjective_of_ringEquiv W σ⟩

/-- The coordinate-ring automorphism `F[E] ≃+* F[E.map σ]` packaging the bijective
`CoordinateRing.map σ`. Mirror of `crFrobEquiv`. -/
noncomputable def coordRingEquiv :
    W.toAffine.CoordinateRing ≃+* (W.map σ.toRingHom).toAffine.CoordinateRing :=
  RingEquiv.ofBijective _ (coordRingMap_bijective_of_ringEquiv W σ)

@[simp] theorem coordRingEquiv_apply (z : W.toAffine.CoordinateRing) :
    coordRingEquiv W σ z =
      WeierstrassCurve.Affine.CoordinateRing.map W.toAffine σ.toRingHom z := rfl

/-- The raw function-field equivalence `F(E) ≃+* F(E.map σ)`, lifting `coordRingEquiv`
to fraction fields. Mirror of `ffFrobEquivRaw`. -/
noncomputable def functionFieldEquivRaw :
    W.toAffine.FunctionField ≃+* (W.map σ.toRingHom).toAffine.FunctionField :=
  IsFractionRing.ringEquivOfRingEquiv (coordRingEquiv W σ)

/-- The codomain cast `F(E.map σ) ≃+* F(E)` along the curve-fixing equation `hW`.
Mirror of `ffFrobCast`. -/
noncomputable def functionFieldCast (hW : W.map σ.toRingHom = W) :
    (W.map σ.toRingHom).toAffine.FunctionField ≃+* W.toAffine.FunctionField :=
  RingEquiv.cast (R := fun V : WeierstrassCurve F ↦ V.toAffine.FunctionField) hW

/-- **The function-field automorphism `σ_KE : F(E) ≃+* F(E)`** induced by a base-field
automorphism `σ` fixing the curve (`hW : W.map σ.toRingHom = W`): the fraction-field lift
of `CoordinateRing.map σ` followed by the codomain cast along `hW`. Mirror of
`frobeniusFunctionFieldEquiv` at an arbitrary curve-fixing `σ`. -/
noncomputable def functionFieldEquiv (hW : W.map σ.toRingHom = W) :
    W.toAffine.FunctionField ≃+* W.toAffine.FunctionField :=
  (functionFieldEquivRaw W σ).trans (functionFieldCast W σ hW)

/-- `functionFieldEquivRaw` acts by `σ` on base constants (into the mapped curve's
function field). Mirror of `ffFrobEquivRaw_algebraMap`. -/
theorem functionFieldEquivRaw_algebraMap (a : F) :
    functionFieldEquivRaw W σ (algebraMap F W.toAffine.FunctionField a) =
      algebraMap F (W.map σ.toRingHom).toAffine.FunctionField (σ a) := by
  rw [show (algebraMap F W.toAffine.FunctionField a) =
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (algebraMap F W.toAffine.CoordinateRing a) from by
    rw [← IsScalarTower.algebraMap_apply]]
  rw [functionFieldEquivRaw, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    coordRingEquiv_apply, coordRingMap_algebraMap_base,
    show σ.toRingHom a = σ a from rfl, ← IsScalarTower.algebraMap_apply]

set_option linter.unusedSectionVars false in
/-- The codomain cast fixes base constants. Mirror of `ffFrobCast_algebraMap`. -/
theorem functionFieldCast_algebraMap (hW : W.map σ.toRingHom = W) (b : F) :
    functionFieldCast W σ hW
        (algebraMap F (W.map σ.toRingHom).toAffine.FunctionField b) =
      algebraMap F W.toAffine.FunctionField b := by
  rw [functionFieldCast]
  have key : ∀ (V : WeierstrassCurve F) (h : V = W),
      (RingEquiv.cast (R := fun U : WeierstrassCurve F ↦ U.toAffine.FunctionField) h)
        (algebraMap F V.toAffine.FunctionField b) =
      algebraMap F W.toAffine.FunctionField b := by
    intro V h; subst h; rfl
  exact key _ hW

/-- **`σ_KE` acts by `σ` on constants**: `σ_KE (algebraMap a) = algebraMap (σ a)`.
This is the σ-analogue of the `q`-power-on-constants leaf of the Frobenius chain. -/
theorem functionFieldEquiv_algebraMap (hW : W.map σ.toRingHom = W) (a : F) :
    functionFieldEquiv W σ hW (algebraMap F W.toAffine.FunctionField a) =
      algebraMap F W.toAffine.FunctionField (σ a) := by
  rw [functionFieldEquiv, RingEquiv.trans_apply, functionFieldEquivRaw_algebraMap,
    functionFieldCast_algebraMap]

section Generators

variable [W.toAffine.IsElliptic]

/-- `σ_KE` fixes the generator `x_gen` (the coordinate function `x` is defined over the
prime field). Mirror of `frobeniusFunctionFieldEquiv_x_gen`. -/
theorem functionFieldEquiv_x_gen (hW : W.map σ.toRingHom = W) :
    functionFieldEquiv W σ hW (x_gen W) = x_gen W := by
  rw [functionFieldEquiv, RingEquiv.trans_apply]
  rw [show x_gen W =
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X) from rfl]
  rw [functionFieldEquivRaw, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    coordRingEquiv_apply, coordRingMap_X]
  rw [functionFieldCast]
  have key : ∀ (V : WeierstrassCurve F) (h : V = W),
      (RingEquiv.cast (R := fun U : WeierstrassCurve F ↦ U.toAffine.FunctionField) h)
        (algebraMap V.toAffine.CoordinateRing V.toAffine.FunctionField
          (algebraMap (Polynomial F) V.toAffine.CoordinateRing Polynomial.X)) =
      x_gen W := by
    intro V h; subst h; rfl
  exact key _ hW

/-- `σ_KE` fixes the generator `y_gen`. Mirror of `frobeniusFunctionFieldEquiv_y_gen`. -/
theorem functionFieldEquiv_y_gen (hW : W.map σ.toRingHom = W) :
    functionFieldEquiv W σ hW (y_gen W) = y_gen W := by
  rw [functionFieldEquiv, RingEquiv.trans_apply]
  rw [show y_gen W =
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (AdjoinRoot.root W.toAffine.polynomial) from rfl]
  rw [functionFieldEquivRaw, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    coordRingEquiv_apply, coordRingMap_root]
  rw [functionFieldCast]
  have key : ∀ (V : WeierstrassCurve F) (h : V = W),
      (RingEquiv.cast (R := fun U : WeierstrassCurve F ↦ U.toAffine.FunctionField) h)
        (algebraMap V.toAffine.CoordinateRing V.toAffine.FunctionField
          (AdjoinRoot.root V.toAffine.polynomial)) =
      y_gen W := by
    intro V h; subst h; rfl
  exact key _ hW

end Generators

/-! ### Layer 2 — the point action `σ • P` -/

set_option linter.unusedSectionVars false in
/-- Nonsingularity is preserved by a curve-fixing base automorphism:
`(x, y)` nonsingular on `W` implies `(σ x, σ y)` nonsingular on `W`. -/
theorem nonsingular_ringEquiv (hW : W.map σ.toRingHom = W) {x y : F}
    (h : W.toAffine.Nonsingular x y) : W.toAffine.Nonsingular (σ x) (σ y) := by
  have hmap := (WeierstrassCurve.Affine.map_nonsingular (W := W.toAffine)
    (f := σ.toRingHom) σ.toRingHom.injective x y).mpr h
  rwa [show W.toAffine.map σ.toRingHom = (W.map σ.toRingHom).toAffine from rfl,
    hW] at hmap

/-- The cast of affine points along an equality of Weierstrass curves, as an
`AddMonoidHom` (additivity is definitional after `subst`). -/
noncomputable def pointCastHom {V₁ V₂ : WeierstrassCurve F} (h : V₁ = V₂) :
    V₁.toAffine.Point →+ V₂.toAffine.Point where
  toFun P := cast (congrArg (fun V : WeierstrassCurve F ↦ V.toAffine.Point) h) P
  map_zero' := by subst h; rfl
  map_add' := by subst h; intro P Q; rfl

/-- `pointCastHom` on an affine point keeps the coordinates (the nonsingularity proof is
transported by proof irrelevance). -/
theorem pointCastHom_some {V₁ V₂ : WeierstrassCurve F} (h : V₁ = V₂) {x y : F}
    (hn : V₁.toAffine.Nonsingular x y) (hn' : V₂.toAffine.Nonsingular x y) :
    pointCastHom h (.some x y hn) = .some x y hn' := by
  subst h; rfl

/-- **The point action of a curve-fixing base automorphism**, as an `AddMonoidHom`:
`σ • (x, y) = (σ x, σ y)` and `σ • O = O`. Built as `HasseWeil.Affine.Point.map σ`
(whose additivity is `HasseWeil.Affine.Point.map_add`) followed by the point cast along
`hW`. This is the σ-analogue of `geomFrobeniusPoint`. -/
noncomputable def pointHom (hW : W.map σ.toRingHom = W) :
    W.toAffine.Point →+ W.toAffine.Point :=
  (pointCastHom hW).comp (HasseWeil.Affine.Point.mapAddMonoidHom σ.toRingHom)

@[simp] theorem pointHom_zero (hW : W.map σ.toRingHom = W) :
    pointHom W σ hW 0 = 0 := map_zero _

/-- `pointHom` on an affine point: `σ • (x, y) = (σ x, σ y)`. -/
theorem pointHom_some (hW : W.map σ.toRingHom = W) {x y : F}
    (h : W.toAffine.Nonsingular x y) (h' : W.toAffine.Nonsingular (σ x) (σ y)) :
    pointHom W σ hW (.some x y h) = .some (σ x) (σ y) h' := by
  rw [pointHom, AddMonoidHom.comp_apply,
    show HasseWeil.Affine.Point.mapAddMonoidHom σ.toRingHom (.some x y h) =
      HasseWeil.Affine.Point.map σ.toRingHom σ.toRingHom.injective (.some x y h)
      from rfl,
    HasseWeil.Affine.Point.map_some]
  exact pointCastHom_some hW _ h'

/-- The point action transports `ℓ`-torsion: `ℓ • S = 0 → ℓ • (σ • S) = 0`. -/
theorem pointHom_smul_eq_zero (hW : W.map σ.toRingHom = W) (ℓ : ℤ)
    {S : W.toAffine.Point} (hS : ℓ • S = 0) : ℓ • pointHom W σ hW S = 0 := by
  rw [← map_zsmul, hS, map_zero]

/-- The point action is injective. -/
theorem pointHom_injective (hW : W.map σ.toRingHom = W) :
    Function.Injective (pointHom W σ hW) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · rw [show (Affine.Point.zero : W.toAffine.Point) = 0 from rfl, pointHom_zero,
      pointHom_some W σ hW h₂ (nonsingular_ringEquiv W σ hW h₂)] at h
    exact absurd h.symm (WeierstrassCurve.Affine.Point.some_ne_zero _)
  · rw [show (Affine.Point.zero : W.toAffine.Point) = 0 from rfl, pointHom_zero,
      pointHom_some W σ hW h₁ (nonsingular_ringEquiv W σ hW h₁)] at h
    exact absurd h (WeierstrassCurve.Affine.Point.some_ne_zero _)
  · rw [pointHom_some W σ hW h₁ (nonsingular_ringEquiv W σ hW h₁),
      pointHom_some W σ hW h₂ (nonsingular_ringEquiv W σ hW h₂),
      WeierstrassCurve.Affine.Point.some.injEq] at h
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨σ.injective h.1, σ.injective h.2⟩

set_option linter.unusedSectionVars false in
/-- The inverse automorphism also fixes the curve: `W.map σ.symm = W` from
`W.map σ = W` (via `map_map` and `map_id`). -/
theorem map_symm_eq (hW : W.map σ.toRingHom = W) : W.map σ.symm.toRingHom = W := by
  conv_lhs => rw [← hW]
  rw [WeierstrassCurve.map_map,
    show σ.symm.toRingHom.comp σ.toRingHom = RingHom.id F from
      RingHom.ext fun a ↦ σ.symm_apply_apply a]
  exact W.map_id

/-! ### Layer 3 — the translation conjugation `σ_KE ∘ τ_S = τ_{σ•S} ∘ σ_KE` -/

section Conjugation

variable [W.toAffine.IsElliptic]

set_option linter.unusedSectionVars false in
/-- `σ_KE` fixes the base-changed curve `W_KE W = W.map (algebraMap F F(E))`: its
coefficients `algebraMap (W.aᵢ)` are sent to `algebraMap (σ W.aᵢ) = algebraMap W.aᵢ`
(by `hW`). This feeds the σ-equivariance of the translation formulas below. -/
theorem mapKE_functionFieldEquiv_eq (hW : W.map σ.toRingHom = W) :
    (W_KE W).map (functionFieldEquiv W σ hW).toRingHom = W_KE W := by
  have hcomp : (functionFieldEquiv W σ hW).toRingHom.comp
      (algebraMap F W.toAffine.FunctionField) =
      (algebraMap F W.toAffine.FunctionField).comp σ.toRingHom := by
    ext a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    exact functionFieldEquiv_algebraMap W σ hW a
  rw [W_KE, WeierstrassCurve.map_map, hcomp, ← WeierstrassCurve.map_map, hW]

set_option linter.unusedSectionVars false in
/-- **Generic σ-equivariance of the translation formulas** for a ring endomorphism `φ`
of the function field that fixes the base-changed curve, fixes the generators, and acts
by `σ` on base constants: `φ` sends `translateSlope_xy/translateX_xy/translateY_xy` at
`(xk, yk)` to the same formulas at `(σ xk, σ yk)`. Working with a `RingHom` variable
keeps mathlib's `Affine.map_slope/map_addX/map_addY` applicable syntactically (no
unfolding of the concrete function-field equivalence). -/
theorem ringHom_translate_formulas
    (φ : W.toAffine.FunctionField →+* W.toAffine.FunctionField)
    (hφW : (W_KE W).map φ = W_KE W)
    (hφx : φ (x_gen W) = x_gen W) (hφy : φ (y_gen W) = y_gen W)
    (hφc : ∀ a : F, φ (algebraMap F W.toAffine.FunctionField a) =
      algebraMap F W.toAffine.FunctionField (σ a)) (xk yk : F) :
    φ (translateSlope_xy W xk yk) = translateSlope_xy W (σ xk) (σ yk) ∧
      φ (translateX_xy W xk yk) = translateX_xy W (σ xk) (σ yk) ∧
      φ (translateY_xy W xk yk) = translateY_xy W (σ xk) (σ yk) := by
  have hcurve : (W_KE W).toAffine.map φ = (W_KE W).toAffine := hφW
  have hslope : φ (translateSlope_xy W xk yk) = translateSlope_xy W (σ xk) (σ yk) := by
    rw [translateSlope_xy, translateSlope_xy, ← WeierstrassCurve.Affine.map_slope,
      hφx, hφy, hφc, hφc, hcurve]
  refine ⟨hslope, ?_, ?_⟩
  · rw [translateX_xy, translateX_xy, ← WeierstrassCurve.Affine.map_addX,
      hφx, hφc, hslope, hcurve]
  · rw [translateY_xy, translateY_xy, ← WeierstrassCurve.Affine.map_addY,
      hφx, hφy, hφc, hslope, hcurve]

/-- `σ_KE` is equivariant on the translation formulas:
`σ_KE (translate•_xy xk yk) = translate•_xy (σ xk) (σ yk)`. Instantiation of
`ringHom_translate_formulas` at `φ = σ_KE.toRingHom`, with the coe bridged by the free
rewrites `RingEquiv.toRingHom_eq_coe`/`RingEquiv.coe_toRingHom`. -/
theorem functionFieldEquiv_translate_formulas (hW : W.map σ.toRingHom = W) (xk yk : F) :
    functionFieldEquiv W σ hW (translateSlope_xy W xk yk) =
        translateSlope_xy W (σ xk) (σ yk) ∧
      functionFieldEquiv W σ hW (translateX_xy W xk yk) =
        translateX_xy W (σ xk) (σ yk) ∧
      functionFieldEquiv W σ hW (translateY_xy W xk yk) =
        translateY_xy W (σ xk) (σ yk) := by
  have h := ringHom_translate_formulas W σ (functionFieldEquiv W σ hW).toRingHom
    (mapKE_functionFieldEquiv_eq W σ hW)
    (by
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      exact functionFieldEquiv_x_gen W σ hW)
    (by
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      exact functionFieldEquiv_y_gen W σ hW)
    (by
      intro a
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      exact functionFieldEquiv_algebraMap W σ hW a)
    xk yk
  simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using h

/-- The `S = 0` case of the translation conjugation, for any `g`: since `τ_0` is the
identity, both sides are `σ_KE g`. Proved by application-level rewrites
(`translateAlgEquivOfPoint_zero_apply`) only — abstracting the `AlgEquiv` term itself
(e.g. `rw [translateAlgEquivOfPoint_zero]` or a bare `rfl`) makes the kernel's defeq
re-check unfold the concrete fraction-field lift inside `functionFieldEquiv` and time
out. -/
theorem conj_gen_zero (hW : W.map σ.toRingHom = W) (g : W.toAffine.FunctionField) :
    functionFieldEquiv W σ hW (translateAlgEquivOfPoint W Affine.Point.zero g) =
      translateAlgEquivOfPoint W (pointHom W σ hW Affine.Point.zero)
        (functionFieldEquiv W σ hW g) := by
  have h0 : pointHom W σ hW Affine.Point.zero = Affine.Point.zero :=
    pointHom_zero W σ hW
  rw [h0, translateAlgEquivOfPoint_zero_apply, translateAlgEquivOfPoint_zero_apply]

/-- The translation conjugation on the generator `x_gen`:
`σ_KE (τ_S (x_gen)) = τ_{σ•S} (σ_KE (x_gen))`. Case-split on `S`; the nonzero case is
the pair of `translateAlgEquivOfPoint_apply_x_gen_of_some` evaluations bridged by
`functionFieldEquiv_translate_formulas`. -/
theorem conj_x_gen (hW : W.map σ.toRingHom = W) (S : W.toAffine.Point) :
    functionFieldEquiv W σ hW (translateAlgEquivOfPoint W S (x_gen W)) =
      translateAlgEquivOfPoint W (pointHom W σ hW S)
        (functionFieldEquiv W σ hW (x_gen W)) := by
  rcases S with _ | ⟨xk, yk, hns⟩
  · exact conj_gen_zero W σ hW (x_gen W)
  · rw [pointHom_some W σ hW hns (nonsingular_ringEquiv W σ hW hns),
      translateAlgEquivOfPoint_apply_x_gen_of_some,
      functionFieldEquiv_x_gen W σ hW,
      translateAlgEquivOfPoint_apply_x_gen_of_some]
    exact (functionFieldEquiv_translate_formulas W σ hW xk yk).2.1

/-- The translation conjugation on the generator `y_gen`:
`σ_KE (τ_S (y_gen)) = τ_{σ•S} (σ_KE (y_gen))`. -/
theorem conj_y_gen (hW : W.map σ.toRingHom = W) (S : W.toAffine.Point) :
    functionFieldEquiv W σ hW (translateAlgEquivOfPoint W S (y_gen W)) =
      translateAlgEquivOfPoint W (pointHom W σ hW S)
        (functionFieldEquiv W σ hW (y_gen W)) := by
  rcases S with _ | ⟨xk, yk, hns⟩
  · exact conj_gen_zero W σ hW (y_gen W)
  · rw [pointHom_some W σ hW hns (nonsingular_ringEquiv W σ hW hns),
      translateAlgEquivOfPoint_apply_y_gen_of_some,
      functionFieldEquiv_y_gen W σ hW,
      translateAlgEquivOfPoint_apply_y_gen_of_some]
    exact (functionFieldEquiv_translate_formulas W σ hW xk yk).2.2

/-- The application form of `(σ_KE.toRingHom.comp τ_S.toRingHom) g`. Mirror of
`frob_comp_tau_apply`. -/
theorem equiv_comp_translate_apply (hW : W.map σ.toRingHom = W)
    (S : W.toAffine.Point) (g : W.toAffine.FunctionField) :
    ((functionFieldEquiv W σ hW).toRingHom.comp
        (translateAlgEquivOfPoint W S).toRingEquiv.toRingHom) g =
      functionFieldEquiv W σ hW (translateAlgEquivOfPoint W S g) :=
  RingHom.comp_apply _ _ g

/-- The application form of `(τ_{σ•S}.toRingHom.comp σ_KE.toRingHom) g`. Mirror of
`tau_comp_frob_apply`. -/
theorem translate_comp_equiv_apply (hW : W.map σ.toRingHom = W)
    (S : W.toAffine.Point) (g : W.toAffine.FunctionField) :
    ((translateAlgEquivOfPoint W (pointHom W σ hW S)).toRingEquiv.toRingHom.comp
        (functionFieldEquiv W σ hW).toRingHom) g =
      translateAlgEquivOfPoint W (pointHom W σ hW S)
        (functionFieldEquiv W σ hW g) :=
  RingHom.comp_apply _ _ g

/-- The translation conjugation as a ring-hom composition equality, via extensionality on
the base and the generators. Mirror of `frobeniusFunctionFieldEquiv_comp_translate_eq`. -/
theorem functionFieldEquiv_comp_translate_eq (hW : W.map σ.toRingHom = W)
    (S : W.toAffine.Point) :
    (functionFieldEquiv W σ hW).toRingHom.comp
        (translateAlgEquivOfPoint W S).toRingEquiv.toRingHom =
      (translateAlgEquivOfPoint W (pointHom W σ hW S)).toRingEquiv.toRingHom.comp
        (functionFieldEquiv W σ hW).toRingHom := by
  refine ringHom_ext_base_x_y_gen W _ _ (fun a ↦ ?_)
    (by
      rw [equiv_comp_translate_apply, translate_comp_equiv_apply]
      exact conj_x_gen W σ hW S)
    (by
      rw [equiv_comp_translate_apply, translate_comp_equiv_apply]
      exact conj_y_gen W σ hW S)
  rw [equiv_comp_translate_apply, translate_comp_equiv_apply,
    (translateAlgEquivOfPoint W S).commutes, functionFieldEquiv_algebraMap W σ hW,
    (translateAlgEquivOfPoint W (pointHom W σ hW S)).commutes]

/-- **The translation conjugation, pointwise**: `σ_KE (τ_S g) = τ_{σ•S} (σ_KE g)`.
Mirror of `frobeniusFunctionFieldEquiv_conj`. -/
theorem functionFieldEquiv_conj (hW : W.map σ.toRingHom = W)
    (S : W.toAffine.Point) (g : W.toAffine.FunctionField) :
    functionFieldEquiv W σ hW (translateAlgEquivOfPoint W S g) =
      translateAlgEquivOfPoint W (pointHom W σ hW S)
        (functionFieldEquiv W σ hW g) := by
  rw [← equiv_comp_translate_apply, ← translate_comp_equiv_apply]
  exact RingHom.congr_fun (functionFieldEquiv_comp_translate_eq W σ hW S) g

end Conjugation

/-! ### Layer 4 — σ-naturality of the Weil function (divisor Galois descent) -/

section DivisorDescent

variable [W.toAffine.IsElliptic]

set_option linter.unusedSectionVars false in
/-- `coordRingEquiv` sends `maximalIdealAt P` to `maximalIdealAt Q` on the mapped curve,
where `Q` has coordinates `(σ P.x, σ P.y)`. Mirror of `map_maximalIdealAt_crFrobEquiv`,
via the generic `map_XYIdeal`. -/
theorem map_maximalIdealAt_coordRingEquiv
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint)
    (Q : (⟨(W.map σ.toRingHom).toAffine⟩ : SmoothPlaneCurve F).SmoothPoint)
    (hQx : Q.x = σ P.x) (hQy : Q.y = σ P.y) :
    Ideal.map (coordRingEquiv W σ).toRingHom
        ((⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt P) =
      (⟨(W.map σ.toRingHom).toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt Q := by
  have hcr : (coordRingEquiv W σ).toRingHom =
      WeierstrassCurve.Affine.CoordinateRing.map W.toAffine σ.toRingHom := rfl
  rw [hcr]
  change Ideal.map _
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal W.toAffine P.x (Polynomial.C P.y)) = _
  rw [map_XYIdeal W.toAffine _ P.x (Polynomial.C P.y)]
  change _ = WeierstrassCurve.Affine.CoordinateRing.XYIdeal _ Q.x (Polynomial.C Q.y)
  rw [hQx, hQy, Polynomial.map_C]
  rfl

/-- The smooth point of the mapped curve `W.map σ` with the same coordinates as `P` (the
nonsingularity transported along `hW`). Mirror of `pointOnMapped`. -/
noncomputable def pointOnMapped (hW : W.map σ.toRingHom = W)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) :
    (⟨(W.map σ.toRingHom).toAffine⟩ : SmoothPlaneCurve F).SmoothPoint where
  x := P.x
  y := P.y
  nonsingular := by
    have hM : (W.map σ.toRingHom).toAffine = W.toAffine := by rw [hW]
    rw [hM]; exact P.nonsingular

set_option linter.unusedSectionVars false in
@[simp] theorem pointOnMapped_x (hW : W.map σ.toRingHom = W)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) :
    (pointOnMapped W σ hW P).x = P.x := rfl

set_option linter.unusedSectionVars false in
@[simp] theorem pointOnMapped_y (hW : W.map σ.toRingHom = W)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) :
    (pointOnMapped W σ hW P).y = P.y := rfl

variable [IsAlgClosed F]
  [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]

/-- **Affine order transport for `σ_KE`**: for smooth points `P, Q` with `P = σ • Q`
coordinatewise, `ord_P (σ_KE g) = ord_Q g` (as `pointValuation`s). Mirror of
`pointValuation_frobeniusFunctionFieldEquiv`, assembled from the cast bridge, the
abstract `valuation_map_ringEquiv`, and the maximal-ideal transport. -/
theorem pointValuation_functionFieldEquiv (hW : W.map σ.toRingHom = W)
    (P Q : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint)
    (hPx : P.x = σ Q.x) (hPy : P.y = σ Q.y) (g : W.toAffine.FunctionField) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P
        (functionFieldEquiv W σ hW g) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation Q g := by
  haveI hMell : (W.map σ.toRingHom).toAffine.IsElliptic := by
    rw [hW]; infer_instance
  haveI hMic : IsIntegrallyClosed
      (⟨(W.map σ.toRingHom).toAffine⟩ : SmoothPlaneCurve F).CoordinateRing := by
    rw [hW]; infer_instance
  haveI hMdd : IsDedekindDomain
      (⟨(W.map σ.toRingHom).toAffine⟩ : SmoothPlaneCurve F).CoordinateRing :=
    SmoothPlaneCurve.isDedekindDomain_coordinateRing _
  haveI hEdd : IsDedekindDomain (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing :=
    SmoothPlaneCurve.isDedekindDomain_coordinateRing _
  rw [functionFieldEquiv, RingEquiv.trans_apply, functionFieldCast,
    pointValuation_ringEquivCast _ _ hW
      (pointOnMapped W σ hW P) P (heq_smoothPoint _ _ hW _ _ rfl rfl)]
  rw [pointValuation_eq_heightOneValuation _ (pointOnMapped W σ hW P)
      (functionFieldEquivRaw W σ g),
    pointValuation_eq_heightOneValuation _ Q g]
  rw [functionFieldEquivRaw]
  exact valuation_map_ringEquiv (coordRingEquiv W σ)
    (smoothPointToHeightOne W.toAffine Q)
    (smoothPointToHeightOne (W.map σ.toRingHom).toAffine (pointOnMapped W σ hW P))
    (by
      rw [smoothPointToHeightOne_asIdeal, smoothPointToHeightOne_asIdeal]
      exact (map_maximalIdealAt_coordRingEquiv W σ Q (pointOnMapped W σ hW P)
        (by rw [pointOnMapped_x, hPx]) (by rw [pointOnMapped_y, hPy])).symm) g

set_option linter.unusedSectionVars false in
/-- `coordRingEquiv` on the `F[X]`-basis decomposition `p • 1 + q • y`: it maps the
coefficients through `Polynomial.map σ` and fixes the basis `{1, y}`. Mirror of
`crFrobEquiv_smul_basis`. -/
theorem coordRingEquiv_smul_basis (p q : Polynomial F) :
    coordRingEquiv W σ (p • (1 : W.toAffine.CoordinateRing) +
        q • WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X) =
      (p.map σ.toRingHom) •
          (1 : (W.map σ.toRingHom).toAffine.CoordinateRing) +
        (q.map σ.toRingHom) •
          WeierstrassCurve.Affine.CoordinateRing.mk (W.map σ.toRingHom).toAffine
            Polynomial.X := by
  rw [coordRingEquiv_apply, map_add, WeierstrassCurve.Affine.CoordinateRing.map_smul,
    WeierstrassCurve.Affine.CoordinateRing.map_smul, map_one]
  congr 2
  rw [WeierstrassCurve.Affine.CoordinateRing.map_mk, Polynomial.map_X]

/-- **Norm transport for `coordRingEquiv`**: `N(coordRingEquiv u) = (N u).map σ`.
Mirror of `norm_crFrobEquiv` (both sides are the explicit `norm_smul_basis` polynomial,
and the identity commutes with the coefficient map). -/
theorem norm_coordRingEquiv (u : W.toAffine.CoordinateRing) :
    Algebra.norm (Polynomial F) (coordRingEquiv W σ u) =
      (Algebra.norm (Polynomial F) u).map σ.toRingHom := by
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq u
  rw [coordRingEquiv_smul_basis, WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis,
    WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis]
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_add, Polynomial.map_C, Polynomial.map_X, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆]

/-- `ord_∞` of an integral element transports under `coordRingEquiv`. Mirror of
`ordAtInfty_algebraMap_crFrobEquiv`, via `ordAtInfty_algebraMap_coordinateRing`
(`ord = −natDegree(N)`) and `norm_coordRingEquiv`. -/
theorem ordAtInfty_algebraMap_coordRingEquiv (u : W.toAffine.CoordinateRing) :
    (⟨(W.map σ.toRingHom).toAffine⟩ : SmoothPlaneCurve F).ordAtInfty
        (algebraMap _ _ (coordRingEquiv W σ u)) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).ordAtInfty (algebraMap _ _ u) := by
  by_cases hu : u = 0
  · subst hu
    rw [map_zero, map_zero, map_zero, SmoothPlaneCurve.ordAtInfty_zero,
      SmoothPlaneCurve.ordAtInfty_zero]
  · have hcu : coordRingEquiv W σ u ≠ 0 := fun h ↦
      hu ((EquivLike.injective (coordRingEquiv W σ)) (by rw [h, map_zero]))
    rw [(⟨(W.map σ.toRingHom).toAffine⟩ :
          SmoothPlaneCurve F).ordAtInfty_algebraMap_coordinateRing _ hcu,
      (⟨W.toAffine⟩ :
          SmoothPlaneCurve F).ordAtInfty_algebraMap_coordinateRing _ hu,
      norm_coordRingEquiv,
      Polynomial.natDegree_map_eq_of_injective σ.toRingHom.injective]

/-- The `ord_∞` transport for the raw lift `functionFieldEquivRaw`. Mirror of
`ordAtInfty_ffFrobEquivRaw` (decompose `z = u/v` and apply the integral transport). -/
theorem ordAtInfty_functionFieldEquivRaw (z : W.toAffine.FunctionField) :
    (⟨(W.map σ.toRingHom).toAffine⟩ : SmoothPlaneCurve F).ordAtInfty
        (functionFieldEquivRaw W σ z) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).ordAtInfty z := by
  by_cases hz : z = 0
  · subst hz
    rw [map_zero, SmoothPlaneCurve.ordAtInfty_zero, SmoothPlaneCurve.ordAtInfty_zero]
  obtain ⟨u, v, hv_nzd, heq⟩ :=
    IsFractionRing.div_surjective (A := W.toAffine.CoordinateRing) z
  have hv_ne : v ≠ 0 := nonZeroDivisors.ne_zero hv_nzd
  have hv_map_ne : algebraMap _ W.toAffine.FunctionField v ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hv_ne
  have hu_ne : u ≠ 0 := by intro h; exact hz (by rw [← heq, h, map_zero, zero_div])
  have hu_map_ne : algebraMap _ W.toAffine.FunctionField u ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hu_ne
  rw [← heq, (⟨W.toAffine⟩ :
      SmoothPlaneCurve F).ordAtInfty_div_eq_mul_inv _ hu_map_ne hv_map_ne,
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).ordAtInfty_inv]
  rw [map_div₀, functionFieldEquivRaw, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  have hcu_map_ne : algebraMap _ (W.map σ.toRingHom).toAffine.FunctionField
      (coordRingEquiv W σ u) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (fun h ↦ hu_ne ((EquivLike.injective (coordRingEquiv W σ)) (by rw [h, map_zero])))
  have hcv_map_ne : algebraMap _ (W.map σ.toRingHom).toAffine.FunctionField
      (coordRingEquiv W σ v) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (fun h ↦ hv_ne ((EquivLike.injective (coordRingEquiv W σ)) (by rw [h, map_zero])))
  rw [(⟨(W.map σ.toRingHom).toAffine⟩ :
      SmoothPlaneCurve F).ordAtInfty_div_eq_mul_inv _ hcu_map_ne hcv_map_ne,
    (⟨(W.map σ.toRingHom).toAffine⟩ : SmoothPlaneCurve F).ordAtInfty_inv,
    ordAtInfty_algebraMap_coordRingEquiv, ordAtInfty_algebraMap_coordRingEquiv]

/-- **`σ_KE` fixes the place at infinity**: `ord_∞ (σ_KE g) = ord_∞ g`. Mirror of
`ordAtInfty_frobeniusFunctionFieldEquiv` (raw transport + cast bridge). -/
theorem ordAtInfty_functionFieldEquiv (hW : W.map σ.toRingHom = W)
    (g : W.toAffine.FunctionField) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).ordAtInfty (functionFieldEquiv W σ hW g) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).ordAtInfty g := by
  rw [functionFieldEquiv, RingEquiv.trans_apply, functionFieldCast,
    ordAtInfty_ringEquivCast _ _ hW, ordAtInfty_functionFieldEquivRaw]

/-- The inverse-σ smooth point: coordinates `(σ⁻¹ P.x, σ⁻¹ P.y)` (so `σ • (this) = P`).
Mirror of `geomFrobSmoothPointInv`. -/
noncomputable def smoothPointInv (hW : W.map σ.toRingHom = W)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint where
  x := σ.symm P.x
  y := σ.symm P.y
  nonsingular := nonsingular_ringEquiv W σ.symm (map_symm_eq W σ hW) P.nonsingular

set_option linter.unusedSectionVars false in
@[simp] theorem smoothPointInv_x (hW : W.map σ.toRingHom = W)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) :
    (smoothPointInv W σ hW P).x = σ.symm P.x := rfl

set_option linter.unusedSectionVars false in
@[simp] theorem smoothPointInv_y (hW : W.map σ.toRingHom = W)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) :
    (smoothPointInv W σ hW P).y = σ.symm P.y := rfl

set_option linter.unusedSectionVars false in
/-- `σ • (smoothPointInv P) = P` at the affine-point level. Mirror of
`geomFrobeniusPointFun_geomFrobSmoothPointInv`. -/
theorem pointHom_smoothPointInv (hW : W.map σ.toRingHom = W)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) :
    pointHom W σ hW
        (HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint
          (smoothPointInv W σ hW P)) =
      HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint P := by
  change pointHom W σ hW
      (Affine.Point.some (smoothPointInv W σ hW P).x (smoothPointInv W σ hW P).y
        (smoothPointInv W σ hW P).nonsingular) = _
  rw [pointHom_some W σ hW _ (nonsingular_ringEquiv W σ hW
      (smoothPointInv W σ hW P).nonsingular),
    HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint_def]
  exact (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr
    ⟨σ.apply_symm_apply P.x, σ.apply_symm_apply P.y⟩

/-- `ord_P` transport restated via the inverse-σ point:
`ord_P (σ_KE g) = ord_{σ⁻¹•P} g`. Mirror of `ord_P_frobeniusFunctionFieldEquiv`. -/
theorem ord_P_functionFieldEquiv (hW : W.map σ.toRingHom = W)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint)
    (g : W.toAffine.FunctionField) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P P (functionFieldEquiv W σ hW g) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P (smoothPointInv W σ hW P) g := by
  simp only [HasseWeil.Curves.SmoothPlaneCurve.ord_P]
  rw [pointValuation_functionFieldEquiv W σ hW P (smoothPointInv W σ hW P)
    (σ.apply_symm_apply P.x).symm (σ.apply_symm_apply P.y).symm g]

set_option backward.isDefEq.respectTransparency false in
/-- **Fibre-divisor place comparison** at an affine place: the coefficient of
`[ℓ]^*(σ•T)` at `P` equals the coefficient of `[ℓ]^*(T)` at `σ⁻¹•P`, because
`[ℓ](σ⁻¹•P) = T ⟺ [ℓ]P = σ•T` (the action is additive and injective). Mirror of
`pullbackDiv_geomFrobInv_eq`. -/
theorem pullbackDiv_smoothPointInv_eq (hW : W.map σ.toRingHom = W)
    (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (T : W.toAffine.Point)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) :
    pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
        (mulByInt_ker_finite W ℓ hℓ) (pointHom W σ hW T)
        (ProjectiveSmoothPoint.affine P) =
      pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
        (mulByInt_ker_finite W ℓ hℓ) T
        (ProjectiveSmoothPoint.affine (smoothPointInv W σ hW P)) := by
  rw [pullbackDiv_apply, pullbackDiv_apply,
    HasseWeil.Curves.ProjectiveSmoothPoint.toAffinePoint_affine,
    HasseWeil.Curves.ProjectiveSmoothPoint.toAffinePoint_affine]
  simp only [mulByInt_apply]
  congr 1
  apply propext
  have hPrec := pointHom_smoothPointInv W σ hW P
  have hzsmul : ∀ Q : W.toAffine.Point,
      pointHom W σ hW (ℓ • Q) = ℓ • pointHom W σ hW Q := fun Q ↦ map_zsmul _ ℓ Q
  constructor
  · intro h
    apply pointHom_injective W σ hW
    rw [hzsmul, hPrec]
    exact h
  · intro h
    rw [show P.toAffinePoint = pointHom W σ hW
        (smoothPointInv W σ hW P).toAffinePoint from hPrec.symm, ← hzsmul, h]

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
/-- **Fibre-divisor place comparison at infinity**: `[ℓ]^*(σ•T) ∞ = [ℓ]^*(T) ∞`
(`0 = σ•T ⟺ 0 = T`). Mirror of `pullbackDiv_geomFrob_infinity`. -/
theorem pullbackDiv_pointHom_infinity (hW : W.map σ.toRingHom = W)
    (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (T : W.toAffine.Point) :
    pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
        (mulByInt_ker_finite W ℓ hℓ) (pointHom W σ hW T)
        ProjectiveSmoothPoint.infinity =
      pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
        (mulByInt_ker_finite W ℓ hℓ) T ProjectiveSmoothPoint.infinity := by
  rw [pullbackDiv_apply, pullbackDiv_apply,
    show (ProjectiveSmoothPoint.infinity).toAffinePoint =
      (0 : W.toAffine.Point) from rfl, map_zero]
  congr 1
  apply propext
  rw [eq_comm, eq_comm (a := (0 : W.toAffine.Point))]
  constructor
  · intro h
    apply pointHom_injective W σ hW
    rw [h, map_zero]
  · intro h
    rw [h, map_zero]

/-- **Divisor Galois descent for the Weil function**: `div(σ_KE g_T) = div(g_{σ•T})`,
compared place-by-place via the affine and infinity order transports and the
fibre-divisor place comparisons. Mirror of
`projectiveDivisorOf_frobeniusFunctionFieldEquiv_weilFunction`. -/
theorem projectiveDivisorOf_functionFieldEquiv_weilFunction
    (hW : W.map σ.toRingHom = W) (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (T : W.toAffine.Point) (hT : ℓ • T = 0)
    (hσT : ℓ • pointHom W σ hW T = 0) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf
        (functionFieldEquiv W σ hW (weilFunction W ℓ hℓ T hT)) =
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf
        (weilFunction W ℓ hℓ (pointHom W σ hW T) hσT) := by
  have hdivT : (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf
        (weilFunction W ℓ hℓ T hT) =
      pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
          (mulByInt_ker_finite W ℓ hℓ) T -
        pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
          (mulByInt_ker_finite W ℓ hℓ) 0 :=
    weilFunction_divisor W ℓ hℓ T hT
  have hdivσT : (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf
        (weilFunction W ℓ hℓ (pointHom W σ hW T) hσT) =
      pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
          (mulByInt_ker_finite W ℓ hℓ) (pointHom W σ hW T) -
        pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
          (mulByInt_ker_finite W ℓ hℓ) 0 :=
    weilFunction_divisor W ℓ hℓ _ hσT
  have hσ0 : pointHom W σ hW (0 : W.toAffine.Point) = 0 := map_zero _
  refine Finsupp.ext fun w ↦ ?_
  cases w with
  | infinity =>
    rw [HasseWeil.Curves.SmoothPlaneCurve.projectiveDivisorOf_apply_infinity,
      ordAtInfty_functionFieldEquiv,
      ← HasseWeil.Curves.SmoothPlaneCurve.projectiveDivisorOf_apply_infinity,
      hdivT, hdivσT, Finsupp.sub_apply, Finsupp.sub_apply,
      pullbackDiv_pointHom_infinity W σ hW ℓ hℓ T]
  | affine P =>
    rw [HasseWeil.Curves.SmoothPlaneCurve.projectiveDivisorOf_apply_affine,
      ord_P_functionFieldEquiv,
      ← HasseWeil.Curves.SmoothPlaneCurve.projectiveDivisorOf_apply_affine,
      hdivT, hdivσT, Finsupp.sub_apply, Finsupp.sub_apply]
    congr 1
    · exact (pullbackDiv_smoothPointInv_eq W σ hW ℓ hℓ T P).symm
    · have h0 := (pullbackDiv_smoothPointInv_eq W σ hW ℓ hℓ 0 P).symm
      rwa [hσ0] at h0

/-- **σ-naturality of the Weil function**: `σ_KE (g_T) = c · g_{σ•T}` for a nonzero
`c : F` (equal divisors, so the ratio is a nonzero constant). Mirror of
`frobeniusFunctionFieldEquiv_weilFunction_eq_smul`. -/
theorem functionFieldEquiv_weilFunction_eq_smul (hW : W.map σ.toRingHom = W)
    (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (T : W.toAffine.Point) (hT : ℓ • T = 0)
    (hσT : ℓ • pointHom W σ hW T = 0) :
    ∃ c : F, c ≠ 0 ∧
      functionFieldEquiv W σ hW (weilFunction W ℓ hℓ T hT) =
        algebraMap F W.toAffine.FunctionField c *
          weilFunction W ℓ hℓ (pointHom W σ hW T) hσT := by
  haveI hEdd : IsDedekindDomain (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing :=
    SmoothPlaneCurve.isDedekindDomain_coordinateRing _
  set gT := weilFunction W ℓ hℓ T hT with hgT
  set gσT := weilFunction W ℓ hℓ (pointHom W σ hW T) hσT with hgσT
  have hgT_ne : gT ≠ 0 := weilFunction_ne_zero W ℓ hℓ T hT
  have hgσT_ne : gσT ≠ 0 := weilFunction_ne_zero W ℓ hℓ _ hσT
  have hσgT_ne : functionFieldEquiv W σ hW gT ≠ 0 :=
    (map_ne_zero_iff _ (functionFieldEquiv W σ hW).injective).mpr hgT_ne
  have hdiv0 : (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf
      (functionFieldEquiv W σ hW gT / gσT) = 0 := by
    rw [div_eq_mul_inv,
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf_mul hσgT_ne
        (inv_ne_zero hgσT_ne),
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf_inv hgσT_ne,
      projectiveDivisorOf_functionFieldEquiv_weilFunction W σ hW ℓ hℓ T hT hσT,
      add_neg_cancel]
  obtain ⟨c, hc0, hc⟩ := const_unit_of_projectiveDivisorOf_eq_zero
    (W := W.toAffine) (functionFieldEquiv W σ hW gT / gσT)
    (div_ne_zero hσgT_ne hgσT_ne) hdiv0
  exact ⟨c, hc0, by rw [← (div_eq_iff hgσT_ne).mp hc]⟩

end DivisorDescent

/-! ### Layer 5 — the constant-ratio core and the main theorem -/

section Main

variable [W.toAffine.IsElliptic]
  [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]
  [IsAlgClosed F]

/-- **The σ-action constant-ratio core** (the σ-variant of `weilPairing_galois_core`):
for a function-field automorphism `σKE` with the conjugation `σKE ∘ τ_S = τ_{S'} ∘ σKE`
(at `g_T`), the σ-naturality `σKE g_T = c · g_{T'}`, and the σ-action on constants
`σKE (algebraMap a) = algebraMap (σ a)`, the pairing transforms by
`e_ℓ(S', T') = σ (e_ℓ(S, T))`. Proof: apply `σKE` to the defining relation
`τ_S g_T = e_ℓ(S,T) · g_T` and cancel the nonzero `c · g_{T'}`. -/
theorem weilPairing_ringEquiv_core (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (σKE : W.toAffine.FunctionField ≃+* W.toAffine.FunctionField)
    (S T S' T' : W.toAffine.Point)
    (hS : ℓ • S = 0) (hT : ℓ • T = 0) (hS' : ℓ • S' = 0) (hT' : ℓ • T' = 0)
    (hconj : σKE (translateAlgEquivOfPoint W S (weilFunction W ℓ hℓ T hT)) =
      translateAlgEquivOfPoint W S' (σKE (weilFunction W ℓ hℓ T hT)))
    {c : F} (hc : c ≠ 0)
    (hnat : σKE (weilFunction W ℓ hℓ T hT) =
      algebraMap F W.toAffine.FunctionField c * weilFunction W ℓ hℓ T' hT')
    (hact : ∀ a : F, σKE (algebraMap F W.toAffine.FunctionField a) =
      algebraMap F W.toAffine.FunctionField (σ a)) :
    weilPairing W ℓ hℓ S' T' hS' hT' = σ (weilPairing W ℓ hℓ S T hS hT) := by
  set e := weilPairing W ℓ hℓ S T hS hT
  set e' := weilPairing W ℓ hℓ S' T' hS' hT'
  set gT := weilFunction W ℓ hℓ T hT
  set gT' := weilFunction W ℓ hℓ T' hT'
  have hgT'_ne : gT' ≠ 0 := weilFunction_ne_zero W ℓ hℓ T' hT'
  have hc_ne : algebraMap F W.toAffine.FunctionField c ≠ 0 := by
    simpa using (map_ne_zero_iff (algebraMap F W.toAffine.FunctionField)
      (algebraMap F W.toAffine.FunctionField).injective).mpr hc
  have hrel : σKE (translateAlgEquivOfPoint W S gT) =
      σKE (algebraMap F W.toAffine.FunctionField e * gT) := by
    rw [weilPairing_translate W ℓ hℓ S T hS hT]
  rw [hconj] at hrel
  rw [map_mul, hact] at hrel
  rw [hnat] at hrel
  rw [map_mul, (translateAlgEquivOfPoint W S').commutes,
    weilPairing_translate W ℓ hℓ S' T' hS' hT'] at hrel
  have hcancel : algebraMap F W.toAffine.FunctionField e' *
        (algebraMap F W.toAffine.FunctionField c * gT') =
      algebraMap F W.toAffine.FunctionField (σ e) *
        (algebraMap F W.toAffine.FunctionField c * gT') := by
    rw [← hrel]; ring
  have hprod_ne : algebraMap F W.toAffine.FunctionField c * gT' ≠ 0 :=
    mul_ne_zero hc_ne hgT'_ne
  exact (algebraMap F W.toAffine.FunctionField).injective
    (mul_right_cancel₀ hprod_ne hcancel)

/-- **Galois equivariance of the field-level Weil pairing (T-C0c)**: for a ring
automorphism `σ : F ≃+* F` fixing the curve (`hW : W.map σ.toRingHom = W`),

  `σ (e_ℓ(S, T)) = e_ℓ(σ • S, σ • T)`,

where `σ • P = pointHom W σ hW P` is the coordinatewise point action. Assembly of the
conjugation (`functionFieldEquiv_conj`), the σ-naturality
(`functionFieldEquiv_weilFunction_eq_smul`), the σ-action on constants
(`functionFieldEquiv_algebraMap`), and the constant-ratio core
(`weilPairing_ringEquiv_core`). Silverman III.8.1 (Galois equivariance). -/
theorem weilPairing_galois_equivariant (hW : W.map σ.toRingHom = W)
    (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (S T : W.toAffine.Point)
    (hS : ℓ • S = 0) (hT : ℓ • T = 0) :
    σ (weilPairing W ℓ hℓ S T hS hT) =
      weilPairing W ℓ hℓ (pointHom W σ hW S) (pointHom W σ hW T)
        (pointHom_smul_eq_zero W σ hW ℓ hS) (pointHom_smul_eq_zero W σ hW ℓ hT) := by
  obtain ⟨c, hc, hnat⟩ := functionFieldEquiv_weilFunction_eq_smul W σ hW ℓ hℓ T hT
    (pointHom_smul_eq_zero W σ hW ℓ hT)
  exact (weilPairing_ringEquiv_core W σ ℓ hℓ (functionFieldEquiv W σ hW)
    S T (pointHom W σ hW S) (pointHom W σ hW T) hS hT
    (pointHom_smul_eq_zero W σ hW ℓ hS) (pointHom_smul_eq_zero W σ hW ℓ hT)
    (functionFieldEquiv_conj W σ hW S (weilFunction W ℓ hℓ T hT))
    hc hnat (functionFieldEquiv_algebraMap W σ hW)).symm

end Main

end WeilPairingGalois

end ModularCurves

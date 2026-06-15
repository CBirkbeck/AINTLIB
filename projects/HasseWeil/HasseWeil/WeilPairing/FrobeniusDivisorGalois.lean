/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.DivisorGalois
import HasseWeil.WeilPairing.FrobeniusFunctionFieldEquiv
import HasseWeil.WeilPairing.DivisorTranslate
import HasseWeil.WeilPairing.Pairing
import HasseWeil.WeilPairing.FrobMatrixData
import HasseWeil.Curves.FrobeniusFixedPoint
import HasseWeil.Curves.NoFinitePolesBridge

/-!
# Divisor Galois descent for the arithmetic Frobenius `σ` of `K̄(E)`

This file applies the abstract divisor-Galois-descent engine (`DivisorGalois.lean`) to the concrete
arithmetic Frobenius `σ = frobeniusFunctionFieldEquiv W` of the function field `K̄(E)`, proving the
affine order transport

```
ord_P (σ g) = ord_{Q} g     where  Q  has coordinates  (P.x^{1/q}, P.y^{1/q}) = π̄⁻¹ P.
```

This is the affine half of the divisor Galois descent `div(σ g) = π̄_*(div g)` feeding the two
geometric facts (conjugation, σ-naturality) of `FrobeniusGaloisGeometric`.
-/

open WeierstrassCurve HasseWeil.Curves IsDedekindDomain Polynomial

namespace HasseWeil.WeilPairing

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

noncomputable local instance instDecEqACFDG : DecidableEq (AlgebraicClosure K) := Classical.decEq _

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]

/-- `crFrobEquiv` (= `CoordinateRing.map e`) sends `maximalIdealAt P` to `maximalIdealAt Q`, where
`Q` is the smooth point of the **mapped** curve `(E).map e` with coordinates `(e P.x, e P.y)`.
Direct from `map_XYIdeal` (with `e (C P.y) = C (e P.y)`). -/
theorem map_maximalIdealAt_crFrobEquiv
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint)
    (Q : (⟨((W.baseChange (AlgebraicClosure K)).map
      (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint)
    (hQx : Q.x = coeffFrobEquiv (K := K) P.x)
    (hQy : Q.y = coeffFrobEquiv (K := K) P.y) :
    Ideal.map (crFrobEquiv W).toRingHom
        ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
          SmoothPlaneCurve (AlgebraicClosure K)).maximalIdealAt P) =
      (⟨((W.baseChange (AlgebraicClosure K)).map
        (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).maximalIdealAt Q := by
  have hcr : (crFrobEquiv W).toRingHom =
      WeierstrassCurve.Affine.CoordinateRing.map (W.baseChange (AlgebraicClosure K)).toAffine
        (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K) := rfl
  rw [hcr]
  change Ideal.map _
      (WeierstrassCurve.Affine.CoordinateRing.XYIdeal (W.baseChange (AlgebraicClosure K)).toAffine
        P.x (Polynomial.C P.y)) = _
  rw [map_XYIdeal (W.baseChange (AlgebraicClosure K)).toAffine _ P.x (Polynomial.C P.y)]
  change _ = WeierstrassCurve.Affine.CoordinateRing.XYIdeal _ Q.x (Polynomial.C Q.y)
  rw [hQx, hQy, Polynomial.map_C]
  rfl

/- The affine order transport `ord_P (σ g) = ord_Q g`, where `Q` is the smooth point with
`e Q.x = P.x, e Q.y = P.y` (i.e. `P = π̄ Q`, the geometric Frobenius image of `Q`). -/

/-- The smooth point of the **mapped** curve `(E).map e` with the same coordinates as `P`
(the nonsingularity proof transported across the curve equality `(E).map e = E`). -/
noncomputable def pointOnMapped
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) :
    (⟨((W.baseChange (AlgebraicClosure K)).map
      (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint where
  x := P.x
  y := P.y
  nonsingular := by
    have hM : ((W.baseChange (AlgebraicClosure K)).map
        (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K)).toAffine =
        (W.baseChange (AlgebraicClosure K)).toAffine := by rw [map_coeffFrobEquiv_eq W]
    rw [hM]; exact P.nonsingular

@[simp] theorem pointOnMapped_x (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
    SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) : (pointOnMapped W P).x = P.x := rfl

@[simp] theorem pointOnMapped_y (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
    SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) : (pointOnMapped W P).y = P.y := rfl

/-- **Affine order transport for the arithmetic Frobenius `σ`** (the affine divisor Galois descent).
For smooth points `P` and `Q` of `E_{K̄}` with `P = π̄ Q` (coordinate-wise `P.x = Q.x^q`,
`P.y = Q.y^q`), the `pointValuation` of `σ g` at `P` equals the `pointValuation` of `g` at `Q`:
```
ord_P (frobeniusFunctionFieldEquiv g) = ord_Q g .
```
Assembled from the cast bridge (`pointValuation_ringEquivCast`), the abstract valuation transport
(`valuation_map_ringEquiv` via `crFrobEquiv`), the maximal-ideal transport
(`map_maximalIdealAt_crFrobEquiv`), and the `pointValuation ↔ HeightOneSpectrum.valuation` bridge
(`pointValuation_eq_heightOneValuation`). -/
theorem pointValuation_frobeniusFunctionFieldEquiv
    (P Q : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint)
    (hPx : P.x = coeffFrobEquiv (K := K) Q.x)
    (hPy : P.y = coeffFrobEquiv (K := K) Q.y)
    (g : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        (frobeniusFunctionFieldEquiv W g) =
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation Q g := by
  haveI hMell : ((W.baseChange (AlgebraicClosure K)).map
      (coeffFrobEquiv (K := K) :
        AlgebraicClosure K →+* AlgebraicClosure K)).toAffine.IsElliptic := by
    rw [map_coeffFrobEquiv_eq W]; infer_instance
  haveI hMic : IsIntegrallyClosed (⟨((W.baseChange (AlgebraicClosure K)).map
      (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).CoordinateRing := by
    rw [map_coeffFrobEquiv_eq W]; infer_instance
  haveI hMdd : IsDedekindDomain (⟨((W.baseChange (AlgebraicClosure K)).map
      (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).CoordinateRing :=
    SmoothPlaneCurve.isDedekindDomain_coordinateRing _
  haveI hEdd : IsDedekindDomain (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).CoordinateRing :=
    SmoothPlaneCurve.isDedekindDomain_coordinateRing _
  rw [frobeniusFunctionFieldEquiv, RingEquiv.trans_apply, ffFrobCast,
    pointValuation_ringEquivCast _ _ (map_coeffFrobEquiv_eq W)
      (pointOnMapped W P) P (heq_smoothPoint _ _ (map_coeffFrobEquiv_eq W) _ _ rfl rfl)]
  rw [pointValuation_eq_heightOneValuation _ (pointOnMapped W P) (ffFrobEquivRaw W g),
    pointValuation_eq_heightOneValuation _ Q g]
  rw [ffFrobEquivRaw]
  exact valuation_map_ringEquiv (crFrobEquiv W)
    (smoothPointToHeightOne (W.baseChange (AlgebraicClosure K)).toAffine Q)
    (smoothPointToHeightOne ((W.baseChange (AlgebraicClosure K)).map
      (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K)).toAffine
      (pointOnMapped W P))
    (by
      rw [smoothPointToHeightOne_asIdeal, smoothPointToHeightOne_asIdeal]
      exact (map_maximalIdealAt_crFrobEquiv W Q (pointOnMapped W P)
        (by rw [pointOnMapped_x, hPx]) (by rw [pointOnMapped_y, hPy])).symm) g

/- The order-at-infinity transport `ordAtInfty (σ g) = ordAtInfty g`: the arithmetic Frobenius `σ`
fixes the place at infinity. Mirrors `OrdAtInftyBaseChange.lean` (the base-change `ord_∞`
transport), replacing the injective `algebraMap K L` by the coefficient Frobenius `coeffFrobEquiv`
(also injective). -/

/-- `crFrobEquiv` (= `CoordinateRing.map e`) on the `K̄[X]`-basis decomposition `p • 1 + q • y`:
it sends the coefficients `p, q` through `Polynomial.map e` and fixes the basis `{1, y}`.
Mirror of `coordRingMap_smul_basis`. -/
theorem crFrobEquiv_smul_basis (p q : Polynomial (AlgebraicClosure K)) :
    crFrobEquiv W (p • (1 : (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing) +
        q • WeierstrassCurve.Affine.CoordinateRing.mk
          (W.baseChange (AlgebraicClosure K)).toAffine Polynomial.X) =
      (p.map (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K)) •
          (1 : ((W.baseChange (AlgebraicClosure K)).map (coeffFrobEquiv (K := K) :
            AlgebraicClosure K →+* AlgebraicClosure K)).toAffine.CoordinateRing) +
        (q.map (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K)) •
          WeierstrassCurve.Affine.CoordinateRing.mk
            ((W.baseChange (AlgebraicClosure K)).map
              (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K)).toAffine
            Polynomial.X := by
  rw [crFrobEquiv_apply, map_add, WeierstrassCurve.Affine.CoordinateRing.map_smul,
    WeierstrassCurve.Affine.CoordinateRing.map_smul, map_one]
  congr 2
  rw [WeierstrassCurve.Affine.CoordinateRing.map_mk, Polynomial.map_X]

/-- **Norm transport for `crFrobEquiv`**: `N_M(crFrobEquiv u) = (N_E u).map e`.  Both sides are the
explicit `norm_smul_basis` polynomial in the basis coefficients; the identity commutes with the
coefficient Frobenius `e` because the Weierstrass coefficients of `M = E.map e` are `e (E.aᵢ)`.
Mirror of `norm_coordRingMap`. -/
theorem norm_crFrobEquiv (u : (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing) :
    Algebra.norm (Polynomial (AlgebraicClosure K)) (crFrobEquiv W u) =
      (Algebra.norm (Polynomial (AlgebraicClosure K)) u).map
        (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K) := by
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq u
  rw [crFrobEquiv_smul_basis, WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis,
    WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis]
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add,
    Polynomial.map_C, Polynomial.map_X, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]

/-- `ord_∞` of an integral element transports under `crFrobEquiv`:
`ord_∞^M(algebraMap (crFrobEquiv u)) = ord_∞^E(algebraMap u)`. Via
`ordAtInfty_algebraMap_coordinateRing` (`ord = -natDegree(N)`), `norm_crFrobEquiv`, and `natDegree`
preservation under the injective `e`. Mirror of `ordAtInfty_algebraMap_coordRingMap`. -/
theorem ordAtInfty_algebraMap_crFrobEquiv
    (u : (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing) :
    (⟨((W.baseChange (AlgebraicClosure K)).map
        (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).ordAtInfty
        (algebraMap _ _ (crFrobEquiv W u)) =
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).ordAtInfty (algebraMap _ _ u) := by
  by_cases hu : u = 0
  · subst hu
    rw [map_zero, map_zero, map_zero, SmoothPlaneCurve.ordAtInfty_zero,
      SmoothPlaneCurve.ordAtInfty_zero]
  · have hcu : crFrobEquiv W u ≠ 0 := fun h =>
      hu ((EquivLike.injective (crFrobEquiv W)) (by rw [h, map_zero]))
    rw [(⟨((W.baseChange (AlgebraicClosure K)).map _).toAffine⟩ :
          SmoothPlaneCurve (AlgebraicClosure K)).ordAtInfty_algebraMap_coordinateRing _ hcu,
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
          SmoothPlaneCurve (AlgebraicClosure K)).ordAtInfty_algebraMap_coordinateRing _ hu,
      norm_crFrobEquiv,
      Polynomial.natDegree_map_eq_of_injective
        (RingHom.injective (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K))]

/-- **The order-at-infinity transport for the raw arithmetic Frobenius** `σ_raw = ffFrobEquivRaw`:
`ord_∞^M(σ_raw z) = ord_∞^E z` for all `z`.  Decompose `z = algebraMap u / algebraMap v`, split via
`ordAtInfty_div_eq_mul_inv`/`ordAtInfty_inv`, and apply `ordAtInfty_algebraMap_crFrobEquiv`
(`σ_raw (algebraMap u) = algebraMap (crFrobEquiv u)`).  Mirror of `ordAtInfty_functionFieldMap`. -/
theorem ordAtInfty_ffFrobEquivRaw
    (z : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    (⟨((W.baseChange (AlgebraicClosure K)).map
        (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).ordAtInfty (ffFrobEquivRaw W z) =
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).ordAtInfty z := by
  by_cases hz : z = 0
  · subst hz
    rw [map_zero, SmoothPlaneCurve.ordAtInfty_zero, SmoothPlaneCurve.ordAtInfty_zero]
  obtain ⟨u, v, hv_nzd, heq⟩ :=
    IsFractionRing.div_surjective
      (A := (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing) z
  have hv_ne : v ≠ 0 := nonZeroDivisors.ne_zero hv_nzd
  have hv_map_ne : algebraMap _ (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField v ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hv_ne
  have hu_ne : u ≠ 0 := by intro h; exact hz (by rw [← heq, h, map_zero, zero_div])
  have hu_map_ne : algebraMap _ (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField u ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hu_ne
  rw [← heq, (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).ordAtInfty_div_eq_mul_inv _ hu_map_ne hv_map_ne,
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).ordAtInfty_inv]
  rw [map_div₀, ffFrobEquivRaw, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  have hcu_map_ne : algebraMap _ ((W.baseChange (AlgebraicClosure K)).map
      (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K)).toAffine.FunctionField
      (crFrobEquiv W u) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (fun h => hu_ne ((EquivLike.injective (crFrobEquiv W)) (by rw [h, map_zero])))
  have hcv_map_ne : algebraMap _ ((W.baseChange (AlgebraicClosure K)).map
      (coeffFrobEquiv (K := K) : AlgebraicClosure K →+* AlgebraicClosure K)).toAffine.FunctionField
      (crFrobEquiv W v) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (fun h => hv_ne ((EquivLike.injective (crFrobEquiv W)) (by rw [h, map_zero])))
  rw [(⟨((W.baseChange (AlgebraicClosure K)).map _).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).ordAtInfty_div_eq_mul_inv _ hcu_map_ne hcv_map_ne,
    (⟨((W.baseChange (AlgebraicClosure K)).map _).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).ordAtInfty_inv,
    ordAtInfty_algebraMap_crFrobEquiv, ordAtInfty_algebraMap_crFrobEquiv]

/-- **The order-at-infinity transport for the arithmetic Frobenius `σ`**: `σ` fixes the place at
infinity, `ordAtInfty (frobeniusFunctionFieldEquiv g) = ordAtInfty g`.  Composes the cast bridge
`ordAtInfty_ringEquivCast` with the raw transport `ordAtInfty_ffFrobEquivRaw`. -/
theorem ordAtInfty_frobeniusFunctionFieldEquiv
    (g : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).ordAtInfty (frobeniusFunctionFieldEquiv W g) =
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).ordAtInfty g := by
  rw [frobeniusFunctionFieldEquiv, RingEquiv.trans_apply, ffFrobCast,
    ordAtInfty_ringEquivCast _ _ (map_coeffFrobEquiv_eq W), ordAtInfty_ffFrobEquivRaw]

/- The inverse geometric Frobenius on smooth points: over `K̄` the geometric Frobenius `π̄` is a
bijection of points; `geomFrobSmoothPointInv P` is the smooth point with coordinates
`(e⁻¹ P.x, e⁻¹ P.y)` (so `π̄ (geomFrobSmoothPointInv P) = P`). -/

/-- The inverse-Frobenius smooth point: coordinates `(e⁻¹ P.x, e⁻¹ P.y)`, nonsingular via the
`baseChange_nonsingular` transport along the injective `e⁻¹`. -/
noncomputable def geomFrobSmoothPointInv
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint where
  x := (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)).symm P.x
  y := (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)).symm P.y
  nonsingular :=
    (W.toAffine.baseChange_nonsingular
      (f := (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)).symm.toAlgHom)
      (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)).symm.injective
      P.x P.y).mpr
      P.nonsingular

omit [DecidableEq K] [W.toAffine.IsElliptic]
  [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic] in
@[simp] theorem coeffFrobEquiv_geomFrobSmoothPointInv_x
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) :
    coeffFrobEquiv (K := K) (geomFrobSmoothPointInv W P).x = P.x := by
  show (coeffFrobEquiv (K := K))
    ((FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)).symm P.x) = P.x
  rw [AlgEquiv.coe_ringEquiv', AlgEquiv.apply_symm_apply]

omit [DecidableEq K] [W.toAffine.IsElliptic]
  [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic] in
@[simp] theorem coeffFrobEquiv_geomFrobSmoothPointInv_y
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) :
    coeffFrobEquiv (K := K) (geomFrobSmoothPointInv W P).y = P.y := by
  show (coeffFrobEquiv (K := K))
    ((FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)).symm P.y) = P.y
  rw [AlgEquiv.coe_ringEquiv', AlgEquiv.apply_symm_apply]

omit [W.toAffine.IsElliptic] [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic] in
/-- **`π̄` recovers `P` from its inverse-Frobenius point** (at the affine-point level):
`geomFrobeniusPointFun (geomFrobSmoothPointInv P).toAffinePoint = P.toAffinePoint`. -/
theorem geomFrobeniusPointFun_geomFrobSmoothPointInv
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) :
    HasseWeil.geomFrobeniusPointFun W
        (HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint
          (geomFrobSmoothPointInv W P)) =
      HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint P := by
  have he : (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) =
      ((FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) :
        AlgebraicClosure K →ₐ[K] AlgebraicClosure K) := rfl
  change HasseWeil.geomFrobeniusPointFun W
      (Affine.Point.some (geomFrobSmoothPointInv W P).x (geomFrobSmoothPointInv W P).y
        (geomFrobSmoothPointInv W P).nonsingular) = _
  rw [HasseWeil.geomFrobeniusPointFun_some,
    HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint_def,
    Affine.Point.some.injEq, he]
  exact ⟨AlgEquiv.apply_symm_apply _ P.x, AlgEquiv.apply_symm_apply _ P.y⟩

omit [DecidableEq K] [W.toAffine.IsElliptic]
  [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic] in
/-- `geomFrobeniusPointFun` is injective (it is `Point.map` of the injective Frobenius). -/
theorem geomFrobeniusPointFun_injective :
    Function.Injective (HasseWeil.geomFrobeniusPointFun W) :=
  WeierstrassCurve.Affine.Point.map_injective
    (f := FiniteField.frobeniusAlgHom K (AlgebraicClosure K))

/- The divisor Galois descent for the Weil function, and σ-naturality:
`div(σ g_T) = div(g_{π̄T})`, whence `σ(g_T) = c · g_{π̄T}` (the σ-naturality fact). -/

open HasseWeil

omit [W.toAffine.IsElliptic] in
/-- **The fibre-divisor place comparison** (the combinatorial heart of σ-naturality). The
coefficient of the fibre divisor `[ℓ]^*(π̄T)` at an affine place `P` equals the coefficient of
`[ℓ]^*(T)` at the inverse-Frobenius place `geomFrobSmoothPointInv P`, because
`[ℓ](geomFrobInv P) = π̄⁻¹([ℓ]P)`, so `[ℓ](geomFrobInv P) = T ⟺ [ℓ]P = π̄T`. -/
theorem pullbackDiv_geomFrobInv_eq (ℓ : ℤ) (hℓ : (ℓ : AlgebraicClosure K) ≠ 0)
    (T : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) :
    pullbackDiv (W := (W.baseChange (AlgebraicClosure K)).toAffine)
        (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine ℓ).toAddMonoidHom
        (mulByInt_ker_finite (W.baseChange (AlgebraicClosure K)) ℓ hℓ)
        (HasseWeil.geomFrobeniusPoint W T) (ProjectiveSmoothPoint.affine P) =
      pullbackDiv (W := (W.baseChange (AlgebraicClosure K)).toAffine)
        (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine ℓ).toAddMonoidHom
        (mulByInt_ker_finite (W.baseChange (AlgebraicClosure K)) ℓ hℓ)
        T (ProjectiveSmoothPoint.affine (geomFrobSmoothPointInv W P)) := by
  rw [pullbackDiv_apply, pullbackDiv_apply, geomFrobeniusPoint_apply,
    HasseWeil.Curves.ProjectiveSmoothPoint.toAffinePoint_affine,
    HasseWeil.Curves.ProjectiveSmoothPoint.toAffinePoint_affine]
  simp only [mulByInt_apply]
  congr 1
  apply propext
  -- `ℓ • P.toAff = π̄ T  ⟺  ℓ • (geomFrobInv P).toAff = T`, via π̄ injective and `map_zsmul`.
  have hPrec := geomFrobeniusPointFun_geomFrobSmoothPointInv W P
  have hzsmul : ∀ Q, HasseWeil.geomFrobeniusPointFun W (ℓ • Q) =
      ℓ • HasseWeil.geomFrobeniusPointFun W Q := by
    intro Q
    rw [← geomFrobeniusPoint_apply, ← geomFrobeniusPoint_apply, map_zsmul]
  constructor
  · intro h
    apply geomFrobeniusPointFun_injective W
    rw [hzsmul]
    rw [show HasseWeil.geomFrobeniusPointFun W (geomFrobSmoothPointInv W P).toAffinePoint =
        P.toAffinePoint from hPrec]
    exact h
  · intro h
    rw [show P.toAffinePoint = HasseWeil.geomFrobeniusPointFun W
        (geomFrobSmoothPointInv W P).toAffinePoint from hPrec.symm, ← hzsmul, h]

omit [W.toAffine.IsElliptic] in
/-- **The fibre-divisor place comparison at infinity**:
`pullbackDiv [ℓ] (π̄T) ∞ = pullbackDiv [ℓ] T ∞` (both equal `if 0 = Q`, and `0 = π̄T ⟺ 0 = T` since
π̄ is injective with `π̄ 0 = 0`). -/
theorem pullbackDiv_geomFrob_infinity (ℓ : ℤ) (hℓ : (ℓ : AlgebraicClosure K) ≠ 0)
    (T : (W.baseChange (AlgebraicClosure K)).toAffine.Point) :
    pullbackDiv (W := (W.baseChange (AlgebraicClosure K)).toAffine)
        (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine ℓ).toAddMonoidHom
        (mulByInt_ker_finite (W.baseChange (AlgebraicClosure K)) ℓ hℓ)
        (HasseWeil.geomFrobeniusPoint W T) ProjectiveSmoothPoint.infinity =
      pullbackDiv (W := (W.baseChange (AlgebraicClosure K)).toAffine)
        (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine ℓ).toAddMonoidHom
        (mulByInt_ker_finite (W.baseChange (AlgebraicClosure K)) ℓ hℓ)
        T ProjectiveSmoothPoint.infinity := by
  rw [pullbackDiv_apply, pullbackDiv_apply, geomFrobeniusPoint_apply,
    show ProjectiveSmoothPoint.infinity.toAffinePoint =
      (0 : (W.baseChange (AlgebraicClosure K)).toAffine.Point) from rfl, map_zero]
  congr 1
  apply propext
  -- `0 = π̄T ⟺ 0 = T`, since `π̄ 0 = 0` and `π̄` is injective.
  rw [eq_comm, eq_comm (a := (0 : (W.baseChange (AlgebraicClosure K)).toAffine.Point))]
  constructor
  · intro h
    apply geomFrobeniusPointFun_injective W
    rw [h, ← geomFrobeniusPoint_apply, map_zero]
  · intro h
    rw [h, ← geomFrobeniusPoint_apply, map_zero]

/-- **`ord_P` transport restated via the inverse-Frobenius point**:
`ord_P (σ g) = ord_{geomFrobSmoothPointInv P} g`.  This is
`pointValuation_frobeniusFunctionFieldEquiv` with `Q = geomFrobSmoothPointInv P` (so `P.x = e Q.x`),
read off through `ord_P`. -/
theorem ord_P_frobeniusFunctionFieldEquiv
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint)
    (g : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).ord_P P (frobeniusFunctionFieldEquiv W g) =
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).ord_P (geomFrobSmoothPointInv W P) g := by
  unfold HasseWeil.Curves.SmoothPlaneCurve.ord_P
  rw [pointValuation_frobeniusFunctionFieldEquiv W P (geomFrobSmoothPointInv W P)
    (coeffFrobEquiv_geomFrobSmoothPointInv_x W P).symm
    (coeffFrobEquiv_geomFrobSmoothPointInv_y W P).symm g]

/-- **The divisor Galois descent for the Weil function** (the heart of σ-naturality):
`div(σ g_T) = div(g_{π̄T})`, where `π̄ = geomFrobeniusPoint`. Compared place-by-place via the
affine order transport `ord_P_frobeniusFunctionFieldEquiv`, the ∞-order transport
`ordAtInfty_frobeniusFunctionFieldEquiv`, and the fibre-divisor place comparisons
`pullbackDiv_geomFrobInv_eq` / `pullbackDiv_geomFrob_infinity` (with `π̄ 0 = 0`). -/
theorem projectiveDivisorOf_frobeniusFunctionFieldEquiv_weilFunction
    (ℓ : ℤ) (hℓ : (ℓ : AlgebraicClosure K) ≠ 0)
    (T : (W.baseChange (AlgebraicClosure K)).toAffine.Point) (hT : ℓ • T = 0)
    (hπT : ℓ • HasseWeil.geomFrobeniusPoint W T = 0) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).projectiveDivisorOf
        (frobeniusFunctionFieldEquiv W
          (weilFunction (W.baseChange (AlgebraicClosure K)) ℓ hℓ T hT)) =
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).projectiveDivisorOf
        (weilFunction (W.baseChange (AlgebraicClosure K)) ℓ hℓ
          (HasseWeil.geomFrobeniusPoint W T) hπT) := by
  -- The Weil-function divisors as Finsupp equalities (defeq `W_smooth ↔ ⟨⟩` curve form).
  have hdivT : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).projectiveDivisorOf
        (weilFunction (W.baseChange (AlgebraicClosure K)) ℓ hℓ T hT) =
      pullbackDiv (W := (W.baseChange (AlgebraicClosure K)).toAffine)
          (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine ℓ).toAddMonoidHom
          (mulByInt_ker_finite (W.baseChange (AlgebraicClosure K)) ℓ hℓ) T -
        pullbackDiv (W := (W.baseChange (AlgebraicClosure K)).toAffine)
          (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine ℓ).toAddMonoidHom
          (mulByInt_ker_finite (W.baseChange (AlgebraicClosure K)) ℓ hℓ) 0 :=
    weilFunction_divisor (W.baseChange (AlgebraicClosure K)) ℓ hℓ T hT
  have hdivπT : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).projectiveDivisorOf
        (weilFunction (W.baseChange (AlgebraicClosure K)) ℓ hℓ
          (HasseWeil.geomFrobeniusPoint W T) hπT) =
      pullbackDiv (W := (W.baseChange (AlgebraicClosure K)).toAffine)
          (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine ℓ).toAddMonoidHom
          (mulByInt_ker_finite (W.baseChange (AlgebraicClosure K)) ℓ hℓ)
          (HasseWeil.geomFrobeniusPoint W T) -
        pullbackDiv (W := (W.baseChange (AlgebraicClosure K)).toAffine)
          (mulByInt (W.baseChange (AlgebraicClosure K)).toAffine ℓ).toAddMonoidHom
          (mulByInt_ker_finite (W.baseChange (AlgebraicClosure K)) ℓ hℓ) 0 :=
    weilFunction_divisor (W.baseChange (AlgebraicClosure K)) ℓ hℓ _ hπT
  have hπ0 : HasseWeil.geomFrobeniusPoint W
      (0 : (W.baseChange (AlgebraicClosure K)).toAffine.Point) =
      (0 : (W.baseChange (AlgebraicClosure K)).toAffine.Point) := map_zero _
  refine Finsupp.ext fun w => ?_
  cases w with
  | infinity =>
    rw [HasseWeil.Curves.SmoothPlaneCurve.projectiveDivisorOf_apply_infinity,
      ordAtInfty_frobeniusFunctionFieldEquiv,
      ← HasseWeil.Curves.SmoothPlaneCurve.projectiveDivisorOf_apply_infinity,
      hdivT, hdivπT, Finsupp.sub_apply, Finsupp.sub_apply,
      pullbackDiv_geomFrob_infinity W ℓ hℓ T]
  | affine P =>
    rw [HasseWeil.Curves.SmoothPlaneCurve.projectiveDivisorOf_apply_affine,
      ord_P_frobeniusFunctionFieldEquiv,
      ← HasseWeil.Curves.SmoothPlaneCurve.projectiveDivisorOf_apply_affine,
      hdivT, hdivπT, Finsupp.sub_apply, Finsupp.sub_apply]
    congr 1
    · exact (pullbackDiv_geomFrobInv_eq W ℓ hℓ T P).symm
    · rw [← hπ0]; exact (pullbackDiv_geomFrobInv_eq W ℓ hℓ 0 P).symm

/-- **σ-naturality of the Weil function** (Silverman III.8.1, the second geometric fact): for the
arithmetic Frobenius `σ`, `σ(g_T) = c · g_{π̄T}` for a nonzero `c : K̄`. Since
`div(σ g_T) = div(g_{π̄T})` (the divisor Galois descent above), the ratio `σ(g_T)/g_{π̄T}` has
trivial divisor, hence is a nonzero constant (`const_unit_of_projectiveDivisorOf_eq_zero`). -/
theorem frobeniusFunctionFieldEquiv_weilFunction_eq_smul
    (ℓ : ℤ) (hℓ : (ℓ : AlgebraicClosure K) ≠ 0)
    (T : (W.baseChange (AlgebraicClosure K)).toAffine.Point) (hT : ℓ • T = 0)
    (hπT : ℓ • HasseWeil.geomFrobeniusPoint W T = 0) :
    ∃ c : AlgebraicClosure K, c ≠ 0 ∧
      frobeniusFunctionFieldEquiv W (weilFunction (W.baseChange (AlgebraicClosure K)) ℓ hℓ T hT) =
        algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField c *
          weilFunction (W.baseChange (AlgebraicClosure K)) ℓ hℓ
            (HasseWeil.geomFrobeniusPoint W T) hπT := by
  haveI hEdd : IsDedekindDomain (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).CoordinateRing :=
    SmoothPlaneCurve.isDedekindDomain_coordinateRing _
  set gT := weilFunction (W.baseChange (AlgebraicClosure K)) ℓ hℓ T hT with hgT
  set gπT := weilFunction (W.baseChange (AlgebraicClosure K)) ℓ hℓ
    (HasseWeil.geomFrobeniusPoint W T) hπT with hgπT
  have hgT_ne : gT ≠ 0 := weilFunction_ne_zero _ ℓ hℓ T hT
  have hgπT_ne : gπT ≠ 0 := weilFunction_ne_zero _ ℓ hℓ _ hπT
  have hσgT_ne : frobeniusFunctionFieldEquiv W gT ≠ 0 :=
    (map_ne_zero_iff _ (frobeniusFunctionFieldEquiv W).injective).mpr hgT_ne
  -- `div(σ gT / gπT) = div(σ gT) − div(gπT) = 0`.
  have hdiv0 : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).projectiveDivisorOf
      (frobeniusFunctionFieldEquiv W gT / gπT) = 0 := by
    rw [div_eq_mul_inv, (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).projectiveDivisorOf_mul hσgT_ne
          (inv_ne_zero hgπT_ne),
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).projectiveDivisorOf_inv hgπT_ne,
      projectiveDivisorOf_frobeniusFunctionFieldEquiv_weilFunction W ℓ hℓ T hT hπT, add_neg_cancel]
  obtain ⟨c, hc0, hc⟩ := const_unit_of_projectiveDivisorOf_eq_zero
    (W := (W.baseChange (AlgebraicClosure K)).toAffine)
    (frobeniusFunctionFieldEquiv W gT / gπT) (div_ne_zero hσgT_ne hgπT_ne) hdiv0
  exact ⟨c, hc0, by rw [← (div_eq_iff hgπT_ne).mp hc]⟩

end HasseWeil.WeilPairing

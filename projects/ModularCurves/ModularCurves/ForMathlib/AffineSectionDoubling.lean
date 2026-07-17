/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.SectionCoordinates
import ModularCurves.ForMathlib.ThreeTorsionRingCertificate

/-!
# Ring-level doubling coordinates (`RING-DBL`, part A/B)

**(STREAM-OMEGA 2026-07-17, CHARTER-O v10.316.)** The ring-level doubling coordinates
of an affine point with unit tangent denominator, and their field-fibre value: over a
field, doubling a nonsingular point with `tangentDen ≠ 0` lands at exactly these
coordinates (mathlib's `addX`/`addY` at the tangent slope). The slope is carried by an
explicit inverse witness `e` (`tangentDen * e = 1`) so that everything transports along
arbitrary ring maps.

The scheme-level identity `2 • affineSection = affineSection (dblX, dblY)` is built on
top of this in `AffineSectionDoublingIdentity.lean` via the universal-domain transport
(KM's banked route, `decomposition-km-integral.md` [RING-DBL]).
-/

universe u

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The tangent slope at `(p, q)` against an explicit inverse `e` of the tangent
denominator. -/
def dblSlope (p q e : R) : R := W.tangentNum p q * e

/-- The ring-level doubling `X`-coordinate: mathlib's `addX` at the tangent slope. -/
def dblX (p q e : R) : R := W.toAffine.addX p p (W.dblSlope p q e)

/-- The ring-level doubling `Y`-coordinate: mathlib's `addY` at the tangent slope. -/
def dblY (p q e : R) : R := W.toAffine.addY p p q (W.dblSlope p q e)

/-- `dblSlope` is natural in the ring. -/
theorem map_dblSlope {S : Type*} [CommRing S] (φ : R →+* S) (p q e : R) :
    (W.map φ).dblSlope (φ p) (φ q) (φ e) = φ (W.dblSlope p q e) := by
  simp only [dblSlope, tangentNum, map_mul, map_add, map_sub, map_pow, map_ofNat]
  rfl

/-- `dblX` is natural in the ring. -/
theorem map_dblX {S : Type*} [CommRing S] (φ : R →+* S) (p q e : R) :
    (W.map φ).dblX (φ p) (φ q) (φ e) = φ (W.dblX p q e) := by
  simp only [dblX, Affine.addX, map_dblSlope, map_add, map_sub, map_mul, map_pow]
  rfl

/-- `dblY` is natural in the ring. -/
theorem map_dblY {S : Type*} [CommRing S] (φ : R →+* S) (p q e : R) :
    (W.map φ).dblY (φ p) (φ q) (φ e) = φ (W.dblY p q e) := by
  simp only [dblY, Affine.addY, Affine.negAddY, Affine.negY, Affine.addX,
    map_dblSlope, map_add, map_sub, map_mul, map_pow, map_neg]
  rfl

section Field

variable {F : Type*} [Field F] [DecidableEq F] {W' : WeierstrassCurve F}

/-- Over a field, the mathlib tangent slope equals `dblSlope` against any inverse
witness. -/
theorem slope_eq_dblSlope {p q e : F} (he : W'.tangentDen p q * e = 1) :
    W'.toAffine.slope p p q q = W'.dblSlope p q e := by
  have hd : W'.tangentDen p q ≠ 0 := fun hc => by
    rw [hc, zero_mul] at he
    exact zero_ne_one he
  have hyne : q ≠ W'.toAffine.negY p q := by
    intro hc
    refine hd ?_
    rw [tangentDen]
    have := congrArg (fun z => q - z) hc
    simp only [sub_self] at this
    rw [Affine.negY] at this
    linear_combination -this
  rw [Affine.slope_of_Y_ne rfl hyne]
  have hden : q - W'.toAffine.negY p q = W'.tangentDen p q := by
    rw [Affine.negY, tangentDen]
    ring
  rw [hden, dblSlope, tangentNum]
  rw [show W'.toAffine.a₂ = W'.a₂ from rfl, show W'.toAffine.a₄ = W'.a₄ from rfl,
    show W'.toAffine.a₁ = W'.a₁ from rfl, div_eq_iff hd]
  linear_combination (-(3 * p ^ 2 + 2 * W'.a₂ * p + W'.a₄ - W'.a₁ * q)) * he

/-- **(RING-DBL, the field fibre)** Over a field, doubling a nonsingular point with an
invertible tangent denominator lands at the ring-level doubling coordinates. -/
theorem two_zsmul_some_eq_dbl {p q e : F} (h : W'.toAffine.Nonsingular p q)
    (he : W'.tangentDen p q * e = 1)
    (hns : W'.toAffine.Nonsingular (W'.dblX p q e) (W'.dblY p q e)) :
    (2 : ℤ) • (Affine.Point.some _ _ h : W'.toAffine.Point) =
      Affine.Point.some _ _ hns := by
  have hd : W'.tangentDen p q ≠ 0 := fun hc => by
    rw [hc, zero_mul] at he
    exact zero_ne_one he
  have hyne : q ≠ W'.toAffine.negY p q := by
    intro hc
    refine hd ?_
    rw [tangentDen]
    have := congrArg (fun z => q - z) hc
    simp only [sub_self] at this
    rw [Affine.negY] at this
    linear_combination -this
  have hne : ¬(p = p ∧ q = W'.toAffine.negY p q) := fun hc => hyne hc.2
  rw [two_zsmul, Affine.Point.add_some hne]
  have hX : W'.toAffine.addX p p (W'.toAffine.slope p p q q) = W'.dblX p q e := by
    rw [slope_eq_dblSlope he, dblX]
  have hY : W'.toAffine.addY p p q (W'.toAffine.slope p p q q) = W'.dblY p q e := by
    rw [slope_eq_dblSlope he, dblY]
  congr 1 <;> first
    | exact hX
    | exact hY

/-- **(the field `2`-torsion criterion)** Over a field, doubling a nonsingular point
with invertible tangent denominator is nonzero. -/
theorem two_zsmul_some_ne_zero {p q e : F} (h : W'.toAffine.Nonsingular p q)
    (he : W'.tangentDen p q * e = 1) :
    (2 : ℤ) • (Affine.Point.some _ _ h : W'.toAffine.Point) ≠ 0 := by
  have hd : W'.tangentDen p q ≠ 0 := fun hc => by
    rw [hc, zero_mul] at he
    exact zero_ne_one he
  have hyne : q ≠ W'.toAffine.negY p q := by
    intro hc
    refine hd ?_
    rw [tangentDen]
    have := congrArg (fun z => q - z) hc
    simp only [sub_self] at this
    rw [Affine.negY] at this
    linear_combination -this
  have hne : ¬(p = p ∧ q = W'.toAffine.negY p q) := fun hc => hyne hc.2
  rw [two_zsmul, Affine.Point.add_some hne]
  exact Affine.Point.some_ne_zero _

end Field

end WeierstrassCurve

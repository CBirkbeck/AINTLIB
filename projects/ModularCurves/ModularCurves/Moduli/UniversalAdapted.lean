/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# The universal ω-adapted curve and its moduli ring (T-E12, E12-D1)

**(E12-D, STREAM-OMEGA 2026-07-14; board [T-E12] E12-D decompose.)**

The `R`-relative moduli ring of T-E12, `R₁ = R[A₄, A₆][Δ⁻¹]`, and the universal
short-normal-form Weierstrass curve `y² = x³ + A₄x + A₆` over it — the curve that
`M₁ = Spec R₁` will carry as the universal `(E, ω)` (GME Thm 2.2.3; the classical
`ℤ[1/6, g₂, g₃, Δ⁻¹]` presentation differs by the invertible rescaling
`(g₂, g₃) = (−4A₄, −4A₆)`-style; the short form matches `adaptedCoeff₄/₆`,
`Moduli/AdaptedModel.lean`).
-/

universe u

namespace ModularCurves

open MvPolynomial

variable (R : Type u) [CommRing R]

/-- The discriminant polynomial `Δ(A₄, A₆) = −16(4A₄³ + 27A₆²)` of the universal
short Weierstrass curve. -/
noncomputable def shortDeltaPoly : MvPolynomial (Fin 2) R :=
  -16 * (4 * (X 0) ^ 3 + 27 * (X 1) ^ 2)

/-- **(E12-D1)** The T-E12 moduli ring `R₁ = R[A₄, A₆][Δ⁻¹]`. -/
abbrev ModuliRingE12 : Type u :=
  Localization.Away (shortDeltaPoly R)

/-- **(E12-D1)** The universal short-normal-form Weierstrass curve
`y² = x³ + A₄x + A₆` over the moduli ring. -/
noncomputable def universalShortNF : WeierstrassCurve (ModuliRingE12 R) :=
  ⟨0, 0, 0, algebraMap (MvPolynomial (Fin 2) R) (ModuliRingE12 R) (X 0),
    algebraMap (MvPolynomial (Fin 2) R) (ModuliRingE12 R) (X 1)⟩

instance : (universalShortNF R).IsShortNF :=
  ⟨rfl, rfl, rfl⟩

/-- The discriminant of the universal curve is the localized discriminant
polynomial. -/
theorem universalShortNF_Δ :
    (universalShortNF R).Δ =
      algebraMap (MvPolynomial (Fin 2) R) (ModuliRingE12 R) (shortDeltaPoly R) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, universalShortNF, shortDeltaPoly,
    map_mul, map_add, map_pow, map_neg, map_ofNat]
  ring

/-- **(E12-D1)** The universal curve is elliptic: its discriminant is the localized
unit. -/
instance : (universalShortNF R).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, universalShortNF_Δ]
  exact IsLocalization.Away.algebraMap_isUnit (S := ModuliRingE12 R) (shortDeltaPoly R)

end ModularCurves

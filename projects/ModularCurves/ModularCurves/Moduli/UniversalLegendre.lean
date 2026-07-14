/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.LegendreDelta

/-!
# The universal Legendre object over `M'₂ = Spec R[λ][(λ(λ−1))⁻¹]` (T-E14-AX1)

**(STREAM-OMEGA 2026-07-14; the T-E12-D replay for KM 4.6.2's Legendre `δ`.)** The
moduli ring `R[λ][(λ(λ−1))⁻¹]`, the universal Legendre curve `y² = x(x−1)(x−λ)` over
it, its ellipticity when `2` is invertible, its tautological chart presentation, the
universal `ω`-basis, and the tautologically marked sections `P = (0,0)`, `Q = (1,0)`
(via `projModelAffineSection`) — the ingredients of KM engine axiom 1 for the
corrected `δ` (`legendreDelta_representable_by_affine`).
-/

universe u

noncomputable section

namespace ModularCurves

open AlgebraicGeometry CategoryTheory Scheme MvPolynomial LocalPresentation

variable (R : CommRingCat.{u})

/-- **(T-E14-AX1)** The Legendre parameter polynomial `λ(λ−1)` in `R[λ]`. -/
def legendrePoly : MvPolynomial (Fin 1) R :=
  X 0 * (X 0 - 1)

/-- **(T-E14-AX1)** The T-E14 moduli ring `R[λ][(λ(λ−1))⁻¹]` — KM 4.6.2's
`M'₂` (over `ℤ[1/2]`: `Spec ℤ[1/2][λ][(λ(λ−1))⁻¹]`). -/
abbrev LegendreModuliRing : Type u :=
  Localization.Away (legendrePoly R)

/-- **(T-E14-AX1)** The universal Legendre parameter `λ`. -/
def universalLambda : LegendreModuliRing R :=
  algebraMap (MvPolynomial (Fin 1) R) (LegendreModuliRing R) (X 0)

/-- **(T-E14-AX1)** The universal Legendre curve `y² = x(x−1)(x−λ)` over the moduli
ring. -/
def universalLegendre : WeierstrassCurve (LegendreModuliRing R) :=
  legendreCurve (universalLambda R)

instance : (universalLegendre R).IsCharNeTwoNF :=
  ⟨rfl, rfl⟩

/-- `λ(λ−1)` is invertible in the moduli ring (self-localization). -/
theorem isUnit_universalLambda_mul :
    IsUnit (universalLambda R * (universalLambda R - 1)) := by
  have e1 : algebraMap (MvPolynomial (Fin 1) R) (LegendreModuliRing R)
      (X 0 * (X 0 - 1)) = universalLambda R * (universalLambda R - 1) := by
    rw [map_mul, map_sub, map_one]
    rfl
  rw [show universalLambda R * (universalLambda R - 1) =
    algebraMap (MvPolynomial (Fin 1) R) (LegendreModuliRing R) (legendrePoly R) from
    e1.symm]
  exact IsLocalization.Away.algebraMap_isUnit (S := LegendreModuliRing R)
    (legendrePoly R)

/-- **(T-E14-AX1)** Over `2`-invertible bases the universal Legendre curve is
elliptic: `Δ = 16 λ²(λ−1)²` with both factors units. -/
theorem universalLegendre_isElliptic (hR : IsUnit (2 : R)) :
    (universalLegendre R).IsElliptic := by
  rw [universalLegendre, legendreCurve_isElliptic_iff]
  · exact isUnit_universalLambda_mul R
  · have h2 : IsUnit ((algebraMap R (LegendreModuliRing R)) (2 : R)) := hR.map _
    rwa [map_ofNat] at h2

/-- **(T-E14-AX1)** The universal Legendre `Ell/R`-object: `M'₂` carrying the
universal Legendre curve. -/
def universalLegendreObj (hR : IsUnit (2 : R)) : EllObj R :=
  haveI := universalLegendre_isElliptic R hR
  { base := Spec (CommRingCat.of (LegendreModuliRing R))
    structMap := Spec.map (CommRingCat.ofHom (algebraMap R (LegendreModuliRing R)))
    curve := modelEllipticCurve (universalLegendre R) }

/-- **(T-E14-AX1)** The universally marked section `P = (0, 0)` of the universal
Legendre curve. -/
def universalLegendreP (hR : IsUnit (2 : R)) :
    (universalLegendreObj R hR).curve.Section :=
  ⟨projModelAffineSection (universalLegendre R) 0 0
      (legendreCurve_equation_zero (universalLambda R)),
    projModelAffineSection_projModelπ _ _ _ _⟩

/-- **(T-E14-AX1)** The universally marked section `Q = (1, 0)` of the universal
Legendre curve. -/
def universalLegendreQ (hR : IsUnit (2 : R)) :
    (universalLegendreObj R hR).curve.Section :=
  ⟨projModelAffineSection (universalLegendre R) 1 0
      (legendreCurve_equation_one (universalLambda R)),
    projModelAffineSection_projModelπ _ _ _ _⟩

/-- **(T-E14-AX1)** The universal `ω`-basis of the Legendre object, from the
tautological presentation (mirrors `universalOmegaBasis`). -/
def universalLegendreOmega (hR : IsUnit (2 : R)) :
    OmegaBasis (universalLegendreObj R hR).curve.toEllipticCurveGeom :=
  haveI := universalLegendre_isElliptic R hR
  OmegaBasis.ofPresentation rfl (tautPresentation (universalLegendre R))

end ModularCurves

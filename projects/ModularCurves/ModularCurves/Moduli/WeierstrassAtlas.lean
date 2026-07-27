/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.Basic
import ModularCurves.EllipticCurve.Comparison
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The universal Weierstrass atlas `U` and the universal Weierstrass curve `E_U → U`

**(T-W5, Stream W — Weierstrass atlas & quotient stack for `M_ell`)**, per the v8 expert
review. The scheme of nonsingular Weierstrass equations is
`U := Spec ℤ[a₁,a₂,a₃,a₄,a₆][Δ⁻¹]`, and over it lives the tautological (universal)
Weierstrass elliptic curve `E_U := projModel W_univ`, elliptic because `Δ` is inverted.

This is the atlas of the quotient-stack presentation `M_ell^W = [U/G]` (`G =
WeierstrassCurve.VariableChange`, T-W4). Concretely built over `Localization.Away Δ` of the
coefficient polynomial ring; the universe is `0` (the coefficient ring is `Type 0`).
-/

open AlgebraicGeometry CategoryTheory WeierstrassCurve

namespace ModularCurves

/-- The **universal Weierstrass curve** over the polynomial ring in its five coefficients:
`a_i = X_i`. Every Weierstrass curve over any ring is a specialisation of this one. -/
noncomputable def universalWeierstrass : WeierstrassCurve (MvPolynomial (Fin 5) ℤ) where
  a₁ := MvPolynomial.X 0
  a₂ := MvPolynomial.X 1
  a₃ := MvPolynomial.X 2
  a₄ := MvPolynomial.X 3
  a₆ := MvPolynomial.X 4

/-- The **Weierstrass-atlas coefficient ring** `ℤ[a₁,…,a₆][Δ⁻¹]`: the coefficient polynomial
ring with the discriminant inverted. -/
abbrev WeierstrassAtlasRing : Type := Localization.Away universalWeierstrass.Δ

/-- **(T-W7.0a-i)** The universal discriminant is nonzero: evaluate the coefficients at the
elliptic curve `y² = x³ − x` (i.e. `(a₁,…,a₆) = (0,0,0,−1,0)`) over `ℚ`, where `Δ = 64 ≠ 0`.
Working over `ℚ` avoids the characteristic-2/3 degeneracies of the discriminant. -/
theorem universalWeierstrass_Δ_ne_zero : universalWeierstrass.Δ ≠ 0 := by
  intro h
  have key : (MvPolynomial.aeval ![(0 : ℚ), 0, 0, -1, 0]).toRingHom universalWeierstrass.Δ
      = 64 := by
    rw [← WeierstrassCurve.map_Δ universalWeierstrass
      (MvPolynomial.aeval ![(0 : ℚ), 0, 0, -1, 0]).toRingHom]
    show (universalWeierstrass.map _).Δ = 64
    simp only [WeierstrassCurve.map, universalWeierstrass, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three,
      Matrix.cons_val_four]
    norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
  rw [h, map_zero] at key
  norm_num at key

/-- **(T-W7.0a)** The Weierstrass-atlas coefficient ring `ℤ[a₁..a₆][Δ⁻¹]` is an integral domain
(localisation of the polynomial domain away from the nonzero discriminant). -/
instance : IsDomain WeierstrassAtlasRing :=
  IsLocalization.isDomain_localization
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero universalWeierstrass_Δ_ne_zero))

/-- The Weierstrass-atlas coefficient ring is noetherian (localisation of a noetherian ring). -/
instance : IsNoetherianRing WeierstrassAtlasRing :=
  IsLocalization.isNoetherianRing (Submonoid.powers universalWeierstrass.Δ) _ inferInstance

/-- The universal Weierstrass curve pushed to the atlas ring (discriminant inverted). -/
noncomputable def universalWeierstrassLoc : WeierstrassCurve WeierstrassAtlasRing :=
  universalWeierstrass.map (algebraMap _ _)

/-- Over the atlas ring the discriminant is a unit, so the universal curve is elliptic. -/
instance : universalWeierstrassLoc.IsElliptic :=
  IsElliptic.mk <| by
    rw [universalWeierstrassLoc, map_Δ]
    exact IsLocalization.map_units (Localization.Away universalWeierstrass.Δ)
      ⟨universalWeierstrass.Δ, Submonoid.mem_powers _⟩

/-- The **Weierstrass atlas** `U = Spec ℤ[a₁,…,a₆][Δ⁻¹]`. -/
noncomputable def weierstrassAtlas : Scheme.{0} := Spec (.of WeierstrassAtlasRing)

instance : IsAffine weierstrassAtlas := isAffine_Spec _

/-- The **universal Weierstrass elliptic curve** `E_U`, the total space over the atlas. -/
noncomputable def universalCurve : Scheme.{0} := projModel universalWeierstrassLoc

/-- The structure morphism `E_U → U` of the universal Weierstrass curve. -/
noncomputable def universalCurveπ : universalCurve ⟶ weierstrassAtlas :=
  projModelπ universalWeierstrassLoc

/-- The universal Weierstrass curve is **proper** over the atlas. -/
instance : IsProper universalCurveπ := projModelπ_isProper _

/-- The universal Weierstrass curve is **smooth of relative dimension one** over the atlas. -/
theorem universalCurve_smooth : SmoothOfRelativeDimension 1 universalCurveπ :=
  projModel_smooth _

/-- The **zero section** `U → E_U` of the universal Weierstrass curve. -/
noncomputable def universalCurveZero : weierstrassAtlas ⟶ universalCurve :=
  projModelZero universalWeierstrassLoc

@[simp]
theorem universalCurveZero_π : universalCurveZero ≫ universalCurveπ = 𝟙 weierstrassAtlas :=
  projModelZero_projModelπ universalWeierstrassLoc

/-- The top affine chart's `isoSpec.hom`, composed with the scheme's own `isoSpec.inv`, is the
top inclusion. Stated over an arbitrary affine-open proof `h` (rather than `isAffineOpen_top`)
so that it matches the `LocallyWeierstrass` witness's proof term up to proof irrelevance. -/
theorem isAffineOpen_top_isoSpec_hom_isoSpec_inv
    (h : IsAffineOpen (⊤ : (weierstrassAtlas).Opens)) :
    h.isoSpec.hom ≫ weierstrassAtlas.isoSpec.inv = (⊤ : (weierstrassAtlas).Opens).ι := by
  rw [← IsAffineOpen.fromSpec_top, ← IsAffineOpen.isoSpec_inv_ι, Iso.hom_inv_id_assoc]

/-- The universal Weierstrass curve is locally Weierstrass (it *is* a global Weierstrass
model over the affine atlas — the whole space `⊤` witnesses it). -/
theorem universalCurve_localModel :
    LocallyWeierstrass universalCurveπ universalCurveZero universalCurveZero_π :=
  locallyWeierstrass_projModel universalWeierstrassLoc

/-- **The universal elliptic curve** `E_U → U` over the Weierstrass atlas, as an
`EllipticCurveGeom`: the projective Weierstrass model of the tautological elliptic curve, proper,
smooth of relative dimension one, with its zero section, and locally Weierstrass (globally, on the
single chart `⊤`). This is the atlas object the quotient-stack description of `M_ell` is built on
(tickets `T-W5`/`T-W6`). -/
noncomputable def universalEllipticCurve : EllipticCurveGeom weierstrassAtlas where
  E := universalCurve
  π := universalCurveπ
  zero := universalCurveZero
  zero_π := universalCurveZero_π
  smooth := universalCurve_smooth
  proper := inferInstance
  localModel := universalCurve_localModel

end ModularCurves

import ModularCurves.EllipticCurve.WeierstrassModel
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

end ModularCurves

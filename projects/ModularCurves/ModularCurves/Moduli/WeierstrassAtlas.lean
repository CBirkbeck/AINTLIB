import ModularCurves.EllipticCurve.Basic
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

open Limits in
/-- The universal Weierstrass curve is locally Weierstrass (it *is* a global Weierstrass
model over the affine atlas — the whole space `⊤` witnesses it). -/
theorem universalCurve_localModel :
    LocallyWeierstrass universalCurveπ universalCurveZero universalCurveZero_π := by
  intro s
  letI : Algebra WeierstrassAtlasRing
      ↑Γ(weierstrassAtlas, (⊤ : (weierstrassAtlas).Opens)) :=
    (Scheme.ΓSpecIso (.of WeierstrassAtlasRing)).inv.hom.toAlgebra
  haveI : IsIso (⊤ : (weierstrassAtlas).Opens).ι := by
    rw [← Scheme.topIso_hom]; infer_instance
  haveI : IsIso (Spec.map (CommRingCat.ofHom
      (algebraMap WeierstrassAtlasRing ↑Γ(weierstrassAtlas, (⊤ : (weierstrassAtlas).Opens))))) := by
    have : CommRingCat.ofHom (algebraMap WeierstrassAtlasRing
        ↑Γ(weierstrassAtlas, (⊤ : (weierstrassAtlas).Opens))) =
        (Scheme.ΓSpecIso (.of WeierstrassAtlasRing)).inv := rfl
    rw [this]; infer_instance
  refine ⟨⟨⊤, isAffineOpen_top _⟩, trivial,
    universalWeierstrassLoc.map (algebraMap WeierstrassAtlasRing _), inferInstance,
    asIso (pullback.fst universalCurveπ (⊤ : (weierstrassAtlas).Opens).ι) ≪≫
      (asIso (pullback.fst (projModelπ universalWeierstrassLoc) (Spec.map (CommRingCat.ofHom
        (algebraMap WeierstrassAtlasRing
          ↑Γ(weierstrassAtlas, (⊤ : (weierstrassAtlas).Opens))))))).symm ≪≫
      (isPullback_projModelBaseChange universalWeierstrassLoc).isoPullback.symm,
    ?c1, ?c2⟩
  -- T-W5a: chart compatibilities. Math is trivial (affine single-chart special case of
  -- `LocallyWeierstrass.baseChange`, proven in EllipticCurve/Basic.lean). Reduction derived:
  --   c1 = simp [Iso.trans_hom, asIso_hom, asIso_inv, IsPullback.isoPullback_inv_snd]
  --        + `inv(fst)≫snd = universalCurveπ ≫ inv φ` (pullback.condition)
  --        + pullback.condition + `⊤.ι ≫ inv φ = isoSpec.hom` (Scheme.isoSpec_Spec_inv,
  --          IsAffineOpen.fromSpec_top, IsAffineOpen.isoSpec_inv_ι); c2 analogous + projModelZero.
  -- Blocked on Lean elaboration (not math): `inv φ` fails IsIso synth (defeq at instances
  -- transparency on algebraMap; `set φ` let-unfolds; `isoSpec` presheaf-type skew). Fix path:
  -- hoist hid/hbc/c1/c2 to top-level lemmas with explicit `@inv` instance args.
  case c1 => sorry
  case c2 => sorry

end ModularCurves

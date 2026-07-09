/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.WeierstrassModel
import ModularCurves.EllipticCurve.ModelVariableChange
import ModularCurves.ForMathlib.WeierstrassInvariant

/-!
# The quotient curve's Weierstrass model, geometrically ([a5-iv], geometry)

`ForMathlib/WeierstrassInvariant.lean` proves the **algebraic** heart of `[a5]`: for a free `G`-action
on `A` with `Aᴳ` local and a `VariableChange`-cocycle action on `W₀ : WeierstrassCurve A`, there is
`E` and a descended `W₁ : WeierstrassCurve Aᴳ` with `W₁.map (Aᴳ ↪ A) = E⁻¹ • W₀`
(`exists_invariant_descent`).

This file supplies the **geometric** consequence: the universal curve `projModel W₀` over `Spec A`
is the base change of the quotient model `projModel W₁` over `Spec Aᴳ`:

  `projModel W₀ ≅ (projModel W₁) ×_{Spec Aᴳ} Spec A`,

compatibly with the structure maps and zero sections. This is a pure assembly of proven isos —
`isPullback_projModelBaseChange` (base change of `projModel` is a pullback) and `projModelVCIso`
(the change-of-variables iso `projModel (C•W) ≅ projModel W`). Combined with `isPullback_quotientπ`
(`E ≅ (E/G) ×_{X/G} X`) and fppf descent of the resulting iso along the finite étale surjection
`X → X/G`, it yields the `LocallyWeierstrass` iso of `locallyWeierstrass_quotientπ`.
-/

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve

universe u

namespace ModularCurves

variable {R : Type u} [CommRing R] {R₀ : Type u} [CommRing R₀] [Algebra R₀ R]

/-- **([a5-iv], geometry — the base-change descent iso)** If a Weierstrass curve `W₁` over the
subring `R₀` base-changes up to `E⁻¹ • W₀` over `R` (`W₁.map (R₀ ↪ R) = E⁻¹ • W₀`), then the model
`projModel W₀` is the base change of `projModel W₁`:

  `projModel W₀ ≅ (projModel W₁) ×_{Spec R₀} Spec R`.

Composite of `(projModelVCIso E⁻¹ W₀).symm : projModel W₀ ≅ projModel (E⁻¹•W₀)`, the equality
`E⁻¹•W₀ = W₁.map (R₀↪R)`, and `(isPullback_projModelBaseChange W₁).isoPullback`. -/
noncomputable def projModel_descentIso (W₀ : WeierstrassCurve R) (W₁ : WeierstrassCurve R₀)
    (E : VariableChange R) (hW₁ : W₁.map (algebraMap R₀ R) = E⁻¹ • W₀) :
    projModel W₀ ≅
      pullback (projModelπ W₁) (Spec.map (CommRingCat.ofHom (algebraMap R₀ R))) :=
  (projModelVCIso E⁻¹ W₀).symm ≪≫
    eqToIso (congrArg projModel hW₁.symm) ≪≫
      (isPullback_projModelBaseChange (R' := R) W₁).isoPullback

/-- The descent iso lies over `Spec (R₀ ↪ R)`: its `pullback.snd` leg is the structure map of
`projModel W₀` followed by `Spec (R₀ ↪ R)`. Routed plan: after unfolding `projModel_descentIso` and
`IsPullback.isoPullback_hom_snd`, the goal is the π-compatibility of `projModelVCIso E⁻¹`
(`projModelVCIso_π`) composed with `projModelBaseChange_π` (base change respects `π`) and the
`eqToHom`-transport along `hW₁`. -/
theorem projModel_descentIso_hom_snd (W₀ : WeierstrassCurve R) (W₁ : WeierstrassCurve R₀)
    (E : VariableChange R) (hW₁ : W₁.map (algebraMap R₀ R) = E⁻¹ • W₀) :
    (projModel_descentIso W₀ W₁ E hW₁).hom ≫
        pullback.snd (projModelπ W₁) (Spec.map (CommRingCat.ofHom (algebraMap R₀ R)))
      = projModelπ W₀ := by
  have transπ : ∀ {W W' : WeierstrassCurve R} (h : W = W'),
      eqToHom (congrArg projModel h) ≫ projModelπ W' = projModelπ W := by
    rintro W W' rfl; simp
  rw [projModel_descentIso, Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc,
    IsPullback.isoPullback_hom_snd, eqToIso.hom, transπ hW₁.symm, Iso.symm_hom,
    ← projModelVCIso_π, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end ModularCurves

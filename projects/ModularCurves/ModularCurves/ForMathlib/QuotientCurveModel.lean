/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.WeierstrassModel
import ModularCurves.EllipticCurve.ModelVariableChange
import ModularCurves.EllipticCurve.Comparison
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

/-! ### a5-ii — the `VariableChange` cocycle from the geometric action -/

open scoped Pointwise in
/-- Base change of `projModel` along a ring **automorphism** `g` (the `G`-action) is a pullback —
the `algebraMap`-form `isPullback_projModelBaseChange` applied through `RingHom.toAlgebra g`. -/
theorem isPullback_projModelBaseChange_hom (g : R →+* R) (W : WeierstrassCurve R) :
    IsPullback (projModelBaseChange g W) (projModelπ (W.map g)) (projModelπ W)
      (Spec.map (CommRingCat.ofHom g)) := by
  letI : Algebra R R := g.toAlgebra
  have h := isPullback_projModelBaseChange (R := R) (R' := R) W
  have he : (algebraMap R R : R →+* R) = g := g.algebraMap_toAlgebra
  rw [he] at h
  convert h using 2 <;> rw [he]

/-- **([a5-ii], the pointed iso)** If `g` acts on `projModel W` by a *cartesian* square over
`Spec (g)` (the geometric `G`-action, `IsCurveAction.cartesian`), then — since base change along `g`
is also cartesian over `Spec (g)` (`isPullback_projModelBaseChange_hom`) — the two pullbacks give a
canonical iso `projModel W ≅ projModel (W.map g)` respecting `π` (`isoIsPullback_hom_snd`). This is
the pointed iso `pointedIso_exists_variableChange` turns into the cocycle value `C_g`. -/
theorem cartesianIso_hom_π (g : R →+* R) (W : WeierstrassCurve R)
    {act : projModel W ⟶ projModel W}
    (hcart : IsPullback act (projModelπ W) (projModelπ W) (Spec.map (CommRingCat.ofHom g))) :
    (hcart.isoIsPullback _ _ (isPullback_projModelBaseChange_hom g W)).hom ≫
        projModelπ (W.map g) = projModelπ W :=
  hcart.isoIsPullback_hom_snd _ _ (isPullback_projModelBaseChange_hom g W)

open scoped Pointwise in
/-- Base-change of the section at infinity along a ring **automorphism** `g` — the automorphism
form of `projModelZero_baseChange` (T-A5b zero-leg) via `RingHom.toAlgebra g`. -/
theorem projModelZero_baseChange_hom (g : R →+* R) (W : WeierstrassCurve R) :
    projModelZero (W.map g) ≫ projModelBaseChange g W =
      Spec.map (CommRingCat.ofHom g) ≫ projModelZero W := by
  letI : Algebra R R := g.toAlgebra
  have h := projModelZero_baseChange (R := R) (R' := R) W
  have he : (algebraMap R R : R →+* R) = g := g.algebraMap_toAlgebra
  rw [he] at h
  exact h

/-- **([a5-ii], the pointed iso is pointed)** If the cartesian action `act` is also
*zero-equivariant* (`projModelZero W ≫ act = Spec (g) ≫ projModelZero W`, the geometric
`IsCurveAction.zero_equivariant`), then the induced iso `projModel W ≅ projModel (W.map g)` carries
the section at infinity of `W` to that of `W.map g`. Proof: pullback uniqueness against
`isPullback_projModelBaseChange_hom`, checking both legs — the `projModelBaseChange` leg via
`projModelZero_baseChange_hom` + zero-equivariance, the `π` leg via `cartesianIso_hom_π` +
`projModelZero_projModelπ`. -/
theorem cartesianIso_hom_zero (g : R →+* R) (W : WeierstrassCurve R)
    {act : projModel W ⟶ projModel W}
    (hcart : IsPullback act (projModelπ W) (projModelπ W) (Spec.map (CommRingCat.ofHom g)))
    (hzero : projModelZero W ≫ act = Spec.map (CommRingCat.ofHom g) ≫ projModelZero W) :
    projModelZero W ≫ (hcart.isoIsPullback _ _ (isPullback_projModelBaseChange_hom g W)).hom
      = projModelZero (W.map g) := by
  apply (isPullback_projModelBaseChange_hom g W).hom_ext
  · rw [Category.assoc, hcart.isoIsPullback_hom_fst _ _ (isPullback_projModelBaseChange_hom g W),
      hzero, projModelZero_baseChange_hom]
  · rw [Category.assoc, cartesianIso_hom_π, projModelZero_projModelπ, projModelZero_projModelπ]

/-! ### Cocycle-ness infrastructure — base-change automorphism forms -/

/-- Automorphism form of `projModelVCIso_map` (base-change naturality of the change-of-variables
iso), via `RingHom.toAlgebra g`. Backbone of the cocycle identity: it commutes a `projModelVCIso`
past a `projModelBaseChange`. -/
theorem projModelVCIso_map_hom (g : R →+* R) (C : VariableChange R) (W : WeierstrassCurve R) :
    projModelBaseChange g (C • W) ≫ (projModelVCIso C W).hom =
      eqToHom (by rw [map_variableChange]) ≫
        (projModelVCIso (C.map g) (W.map g)).hom ≫ projModelBaseChange g W := by
  letI : Algebra R R := g.toAlgebra
  have h := projModelVCIso_map (R' := R) C W
  have he : (algebraMap R R : R →+* R) = g := g.algebraMap_toAlgebra
  rw [he] at h
  exact h

/-- Base change of `projModel` along a hom whose `Spec` map is an isomorphism is itself an
isomorphism — the `fst` leg of the pullback square `isPullback_projModelBaseChange_hom` over the
iso base `Spec (g)`. For a group action `g = MulSemiringAction.toRingHom G R γ` this always applies
(`isIso_specMap_toRingHom`), making every `projModelBaseChange (toRingHom γ)` cancellable. -/
theorem isIso_projModelBaseChange (g : R →+* R) [IsIso (Spec.map (CommRingCat.ofHom g))]
    (W : WeierstrassCurve R) : IsIso (projModelBaseChange g W) := by
  have hP := isPullback_projModelBaseChange_hom g W
  rw [← hP.isoPullback_hom_fst]
  infer_instance

/-- `Spec` of the ring automorphism `MulSemiringAction.toRingHom G R γ` is an isomorphism (its
inverse is `Spec` of `toRingHom G R γ⁻¹`), since `γ` is a group element. -/
instance isIso_specMap_toRingHom {G : Type u} [Group G] [MulSemiringAction G R] (g : G) :
    IsIso (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G R g))) := by
  have h1 : (MulSemiringAction.toRingHom G R g).comp (MulSemiringAction.toRingHom G R g⁻¹)
      = RingHom.id R := by ext a; simp [MulSemiringAction.toRingHom, ← mul_smul]
  have h2 : (MulSemiringAction.toRingHom G R g⁻¹).comp (MulSemiringAction.toRingHom G R g)
      = RingHom.id R := by ext a; simp [MulSemiringAction.toRingHom, ← mul_smul]
  refine ⟨Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G R g⁻¹)), ?_, ?_⟩ <;>
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] <;>
    simp [h1, h2]

open scoped Pointwise in
/-- **([a5-ii], per-`g` extraction)** A *pointed* iso `projModel W₀ ≅ projModel (g•W₀)` yields the
`VariableChange` `C_g` with `C_g • (g•W₀) = W₀` (`pointedIso_exists_variableChange`, T-W7.1b). -/
theorem exists_vc_of_pointedIso {G : Type u} [Group G] [MulSemiringAction G R]
    (W₀ : WeierstrassCurve R) (g : G)
    (e : projModel W₀ ≅ projModel (W₀.map (MulSemiringAction.toRingHom G R g)))
    (heπ : e.hom ≫ projModelπ (W₀.map (MulSemiringAction.toRingHom G R g)) = projModelπ W₀)
    (hez : projModelZero W₀ ≫ e.hom
      = projModelZero (W₀.map (MulSemiringAction.toRingHom G R g))) :
    ∃ C : VariableChange R, C • (W₀.map (MulSemiringAction.toRingHom G R g)) = W₀ := by
  obtain ⟨C, hC, _⟩ := pointedIso_exists_variableChange W₀
    (W₀.map (MulSemiringAction.toRingHom G R g)) e heπ hez
  exact ⟨C, hC⟩

open scoped Pointwise in
/-- **([a5-ii], per-`g` extraction from the geometric action — the assembled form)** Given the
geometric `G`-action on `projModel W₀` (a cartesian, `π`- and zero-equivariant square over
`Spec (g)`, i.e. the data of `IsCurveAction` at `g`), extract the `VariableChange` `C_g` with
`C_g • (g•W₀) = W₀`. Feeds the cocycle `C : G → VariableChange R` that `exists_invariant_descent`
consumes. Assembles `cartesianIso_hom_π` (π-leg) and `cartesianIso_hom_zero` (zero-leg) into the
pointed iso, then `pointedIso_exists_variableChange` (T-W7.1b). -/
theorem exists_vc_of_curveAction {G : Type u} [Group G] [MulSemiringAction G R]
    (W₀ : WeierstrassCurve R) (g : G)
    {act : projModel W₀ ⟶ projModel W₀}
    (hcart : IsPullback act (projModelπ W₀) (projModelπ W₀)
      (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G R g))))
    (hzero : projModelZero W₀ ≫ act =
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G R g)) ≫ projModelZero W₀) :
    ∃ C : VariableChange R, C • (W₀.map (MulSemiringAction.toRingHom G R g)) = W₀ :=
  exists_vc_of_pointedIso W₀ g
    (hcart.isoIsPullback _ _ (isPullback_projModelBaseChange_hom _ W₀))
    (cartesianIso_hom_π _ W₀ hcart)
    (cartesianIso_hom_zero _ W₀ hcart hzero)

end ModularCurves

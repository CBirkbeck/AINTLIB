/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.Comparison
import ModularCurves.EllipticCurve.ModelVariableChange
import ModularCurves.EllipticCurve.WeierstrassModel
import ModularCurves.ForMathlib.WeierstrassInvariant

/-!
# The quotient curve's Weierstrass model, geometrically ([a5-iv], geometry)

`ForMathlib/WeierstrassInvariant.lean` proves the **algebraic** heart of `[a5]`: for a free
`G`-action on `A` with `Aᴳ` local and a `VariableChange`-cocycle action on
`W₀ : WeierstrassCurve A`, there is `E` and a descended `W₁ : WeierstrassCurve Aᴳ` with
`W₁.map (Aᴳ ↪ A) = E⁻¹ • W₀` (`exists_invariant_descent`).

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
  convert h using 2

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

/-! ### a5-ii — the `VariableChange` cocycle from the geometric action (the geometric half) -/

/-- Naturality of `projModelBaseChange φ` under an equality of source curves. -/
private theorem projModelBaseChange_natEq (φ : R →+* R) {W1 W2 : WeierstrassCurve R}
    (hW : W1 = W2) :
    projModelBaseChange φ W1 ≫ eqToHom (congrArg projModel hW)
      = eqToHom (congrArg projModel (congrArg (WeierstrassCurve.map · φ) hW))
        ≫ projModelBaseChange φ W2 := by
  subst hW
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Naturality of `(projModelVCIso C W).hom` under equalities of the variable change and curve. -/
private theorem projModelVCIso_natEq {C1 C2 : VariableChange R} {W1 W2 : WeierstrassCurve R}
    (hV : C1 = C2) (hW : W1 = W2) :
    (projModelVCIso C1 W1).hom ≫ eqToHom (congrArg projModel hW)
      = eqToHom (congrArg projModel (by rw [hV, hW])) ≫ (projModelVCIso C2 W2).hom := by
  subst hV; subst hW
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Rearranged base-change naturality of the VC iso: `V(C.map φ, W.map φ) ≫ bc φ W` factors as
`eqToHom ≫ bc φ (C•W) ≫ V(C, W)` — the no-leading-eqToHom variant used in the cocycle collapse. -/
private theorem projModelVCIso_map_hom' (φ : R →+* R) (C : VariableChange R)
    (W : WeierstrassCurve R) :
    (projModelVCIso (C.map φ) (W.map φ)).hom ≫ projModelBaseChange φ W
      = eqToHom (congrArg projModel (map_variableChange (W := W) (φ := φ) (C := C)))
        ≫ projModelBaseChange φ (C • W) ≫ (projModelVCIso C W).hom := by
  rw [projModelVCIso_map_hom φ C W, ← Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp]

open scoped Pointwise in
/-- The middle-and-tail collapse of the geometric cocycle: `V_{g•C h} ≫ eqToHom ≫ β_g^{Wh} ≫ β_h`
factors, via base-change naturality of the VC iso (`projModelVCIso_map_hom'`) and `hΨ h`, as
`eqToHom ≫ β_g ≫ act h`. (Note: `projModel` is a large `Proj`, so this collapse is factored out of
the main proof and uses `reassoc_of%` — never `slice`/`isDefEq` on `projModel` — to stay cheap.) -/
private theorem key_middle {G : Type u} [Group G] [MulSemiringAction G R]
    (W₀ : WeierstrassCurve R) (C : G → VariableChange R) (g h : G)
    (acth : projModel W₀ ⟶ projModel W₀)
    (hCh : C h • W₀.map (MulSemiringAction.toRingHom G R h) = W₀)
    (hΨh : (projModelVCIso (C h) (W₀.map (MulSemiringAction.toRingHom G R h))).hom
        ≫ projModelBaseChange (MulSemiringAction.toRingHom G R h) W₀
      = eqToHom (congrArg projModel hCh) ≫ acth)
    (hCurveOuter : (g • C h) • W₀.map (MulSemiringAction.toRingHom G R (g * h))
      = W₀.map (MulSemiringAction.toRingHom G R g)) :
    (projModelVCIso (g • C h) (W₀.map (MulSemiringAction.toRingHom G R (g * h)))).hom
        ≫ eqToHom (congrArg projModel (map_toRingHom_mul W₀ g h))
        ≫ projModelBaseChange (MulSemiringAction.toRingHom G R g)
            (W₀.map (MulSemiringAction.toRingHom G R h))
        ≫ projModelBaseChange (MulSemiringAction.toRingHom G R h) W₀
      = eqToHom (congrArg projModel hCurveOuter)
        ≫ projModelBaseChange (MulSemiringAction.toRingHom G R g) W₀ ≫ acth := by
  have hVC : g • C h = (C h).map (MulSemiringAction.toRingHom G R g) := by
    rw [vcSMul_smul_def, vcSMul_eq_map]
  rw [← Category.assoc, projModelVCIso_natEq hVC (map_toRingHom_mul W₀ g h), Category.assoc,
    reassoc_of% projModelVCIso_map_hom' (MulSemiringAction.toRingHom G R g) (C h)
      (W₀.map (MulSemiringAction.toRingHom G R h)), hΨh,
    reassoc_of% projModelBaseChange_natEq (MulSemiringAction.toRingHom G R g) hCh]
  simp only [← Category.assoc, eqToHom_trans]

open scoped Pointwise in
/-- **([a5-ii], the cocycle — geometric half)** A geometric `G`-action `act` on `projModel W₀`
(a family of cartesian, `π`- and zero-equivariant squares over `Spec (toRingHom g)`, i.e. the data
of `IsCurveAction` transported to the chart) yields a `VariableChange`-valued cocycle
`C : G → VariableChange R` (`IsVCocycle C`) with `C g • (g•W₀) = W₀`. This is the datum
`exists_invariant_descent` consumes. The `hact`-side is `pointedIso_exists_variableChange` per `g`;
the cocycle identity is faithfulness of the model action (`projModelVCIso_injective`) applied to the
geometric multiplicativity (`hmul` + `projModelVCIso_mul`/`_map_hom` + `projModelBaseChange_comp`,
with the base changes cancellable because `toRingHom g` is an automorphism). -/
theorem isVCocycle_of_curveActionFamily' {G : Type u} [Group G] [MulSemiringAction G R]
    (W₀ : WeierstrassCurve R) (act : G → (projModel W₀ ⟶ projModel W₀))
    (hmul : ∀ g h, act (g * h) = act g ≫ act h)
    (hcart : ∀ g, IsPullback (act g) (projModelπ W₀) (projModelπ W₀)
      (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G R g))))
    (hzero : ∀ g, projModelZero W₀ ≫ act g
      = Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G R g)) ≫ projModelZero W₀) :
    ∃ (C : G → VariableChange R)
      (hC : ∀ g, C g • (W₀.map (MulSemiringAction.toRingHom G R g)) = W₀),
      IsVCocycle C ∧
      ∀ x, (projModelVCIso (C x) (W₀.map (MulSemiringAction.toRingHom G R x))).hom
          ≫ projModelBaseChange (MulSemiringAction.toRingHom G R x) W₀
        = eqToHom (congrArg projModel (hC x)) ≫ act x := by
  choose C hC hiso using fun g => pointedIso_exists_variableChange W₀
    (W₀.map (MulSemiringAction.toRingHom G R g))
    ((hcart g).isoIsPullback _ _ (isPullback_projModelBaseChange_hom _ W₀))
    (cartesianIso_hom_π _ W₀ (hcart g))
    (cartesianIso_hom_zero _ W₀ (hcart g) (hzero g))
  have hΨ : ∀ x : G, (projModelVCIso (C x) (W₀.map (MulSemiringAction.toRingHom G R x))).hom
      ≫ projModelBaseChange (MulSemiringAction.toRingHom G R x) W₀
      = eqToHom (congrArg projModel (hC x)) ≫ act x := by
    intro x
    have hfst := (hcart x).isoIsPullback_hom_fst _ _ (isPullback_projModelBaseChange_hom _ W₀)
    rw [hiso x, Category.assoc] at hfst
    rw [← hfst, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  refine ⟨C, hC, fun g h => ?_, hΨ⟩
  have hW : C (g * h) • (W₀.map (MulSemiringAction.toRingHom G R (g * h)))
      = (C g * g • C h) • (W₀.map (MulSemiringAction.toRingHom G R (g * h))) := by
    rw [hC (g * h)]; exact (vc_mul_smul_eq W₀ hC g h).symm
  refine projModelVCIso_injective _ _ _ hW ?_
  have hcore : (projModelVCIso (C g * g • C h)
        (W₀.map (MulSemiringAction.toRingHom G R (g * h)))).hom
      ≫ projModelBaseChange (MulSemiringAction.toRingHom G R (g * h)) W₀
      = eqToHom (congrArg projModel (vc_mul_smul_eq W₀ hC g h)) ≫ act (g * h) := by
    have hτ : MulSemiringAction.toRingHom G R (g * h)
        = (MulSemiringAction.toRingHom G R g).comp (MulSemiringAction.toRingHom G R h) := by
      ext a; simp [MulSemiringAction.toRingHom, mul_smul]
    have hbc : ∀ {f f' : R →+* R} (p : f = f'),
        projModelBaseChange f W₀ = eqToHom (by rw [p]) ≫ projModelBaseChange f' W₀ := by
      intro f f' p; subst p; simp
    have hβ : projModelBaseChange (MulSemiringAction.toRingHom G R (g * h)) W₀
        = eqToHom (congrArg projModel (map_toRingHom_mul W₀ g h))
          ≫ projModelBaseChange (MulSemiringAction.toRingHom G R g)
            (W₀.map (MulSemiringAction.toRingHom G R h))
          ≫ projModelBaseChange (MulSemiringAction.toRingHom G R h) W₀ := by
      rw [hbc hτ, projModelBaseChange_comp]; rfl
    have hVC : g • C h = (C h).map (MulSemiringAction.toRingHom G R g) := by
      rw [vcSMul_smul_def, vcSMul_eq_map]
    have hCurveOuter : (g • C h) • (W₀.map (MulSemiringAction.toRingHom G R (g * h)))
        = W₀.map (MulSemiringAction.toRingHom G R g) := by
      rw [hVC, map_toRingHom_mul, map_variableChange, hC h]
    have key := key_middle W₀ C g h (act h) (hC h) (hΨ h) hCurveOuter
    rw [projModelVCIso_mul (C g) (g • C h)
      (W₀.map (MulSemiringAction.toRingHom G R (g * h))), hβ]
    simp only [Category.assoc]
    rw [key, reassoc_of% projModelVCIso_natEq (rfl : C g = C g) hCurveOuter,
      reassoc_of% hΨ g, ← hmul]
    simp only [← Category.assoc, eqToHom_trans]
  haveI := isIso_projModelBaseChange (MulSemiringAction.toRingHom G R (g * h)) W₀
  refine (cancel_mono (projModelBaseChange (MulSemiringAction.toRingHom G R (g * h)) W₀)).mp ?_
  rw [Category.assoc, hcore, hΨ (g * h), ← Category.assoc, eqToHom_trans]

open scoped Pointwise in
/-- **([a5-ii], the cocycle — geometric half)** The un-primed form: a geometric `G`-action on
`projModel W₀` yields a `VariableChange` cocycle with `C g • (g•W₀) = W₀`. (The primed variant
also exposes the `hΨ` link `VCIso (C g) ≫ β_g = eqToHom ≫ act g` used by the fppf-comparison's
`G`-invariance.) -/
theorem isVCocycle_of_curveActionFamily {G : Type u} [Group G] [MulSemiringAction G R]
    (W₀ : WeierstrassCurve R) (act : G → (projModel W₀ ⟶ projModel W₀))
    (hmul : ∀ g h, act (g * h) = act g ≫ act h)
    (hcart : ∀ g, IsPullback (act g) (projModelπ W₀) (projModelπ W₀)
      (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G R g))))
    (hzero : ∀ g, projModelZero W₀ ≫ act g
      = Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G R g)) ≫ projModelZero W₀) :
    ∃ C : G → VariableChange R, IsVCocycle C ∧
      ∀ g, C g • (W₀.map (MulSemiringAction.toRingHom G R g)) = W₀ := by
  obtain ⟨C, hC, hcoc, -⟩ := isVCocycle_of_curveActionFamily' W₀ act hmul hcart hzero
  exact ⟨C, hcoc, hC⟩

open scoped Pointwise in
/-- **([a5], the local descent — cocycle + algebra assembled)** Given the geometric `G`-action on
`projModel W₀` over a *local* base `Aᴳ` with the action free, the descended Weierstrass model `W₁`
over `Aᴳ` exists with `W₁.map (Aᴳ ↪ A) = E⁻¹ • W₀`. Combines `isVCocycle_of_curveActionFamily` (the
geometric cocycle) with `exists_invariant_descent` (the H¹-vanishing descent). -/
theorem exists_descended_model_of_curveActionFamily
    {G : Type u} [Group G] [Fintype G] [DecidableEq G] [Nontrivial R] [MulSemiringAction G R]
    [IsLocalRing (FixedPoints.subalgebra ℤ R G)] (hfree : IsFreeAlgebraAction G ℤ R)
    (W₀ : WeierstrassCurve R) (act : G → (projModel W₀ ⟶ projModel W₀))
    (hmul : ∀ g h, act (g * h) = act g ≫ act h)
    (hcart : ∀ g, IsPullback (act g) (projModelπ W₀) (projModelπ W₀)
      (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G R g))))
    (hzero : ∀ g, projModelZero W₀ ≫ act g
      = Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G R g)) ≫ projModelZero W₀) :
    ∃ (E : VariableChange R) (W₁ : WeierstrassCurve (FixedPoints.subring R G)),
      W₁.map (algebraMap (FixedPoints.subring R G) R) = E⁻¹ • W₀ := by
  obtain ⟨C, hCoc, hact⟩ := isVCocycle_of_curveActionFamily W₀ act hmul hcart hzero
  exact exists_invariant_descent hfree W₀ hCoc hact


/-! ### [a5-W3] The descent comparison and its `G`-invariance -/

attribute [local instance] MvPolynomial.gradedAlgebra

variable {G : Type u} [Group G] [MulSemiringAction G R]

/-! ### Private transport / functoriality helpers -/

/-- Mixed-ring functoriality of the projective-model base change: base change along a composite
`F.comp φ` factors as the two base changes. (The endomorphism form `projModelBaseChange_comp`
lives in `WeierstrassModel.lean`; this is the same proof for three different rings, which the
graded machinery supports verbatim.) -/
private theorem projModelBaseChange_comp' {S₀ S₁ S₂ : Type u} [CommRing S₀] [CommRing S₁]
    [CommRing S₂] (F : S₁ →+* S₂) (φ : S₀ →+* S₁) (W : WeierstrassCurve S₀) :
    projModelBaseChange (F.comp φ) W
      = projModelBaseChange F (W.map φ) ≫ projModelBaseChange φ W := by
  have bmk : ∀ {T T' : Type u} [CommRing T] [CommRing T'] (ψ : T →+* T')
      (V : WeierstrassCurve T) (p : MvPolynomial (Fin 3) T),
      baseChangeGradedHom ψ V (Ideal.Quotient.mk (projIdeal V).toIdeal p)
        = Ideal.Quotient.mk (projIdeal (V.map ψ)).toIdeal (MvPolynomial.map ψ p) :=
    fun ψ V p => HomogeneousIdeal.quotientGradingMap_mk (mvMapGraded ψ) (projIdeal V)
      (projIdeal (V.map ψ)) (projIdeal_le_comap ψ V) p
  have hgraded : baseChangeGradedHom (F.comp φ) W
      = (baseChangeGradedHom F (W.map φ)).comp (baseChangeGradedHom φ W) := by
    refine GradedRingHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    show baseChangeGradedHom (F.comp φ) W (Ideal.Quotient.mk _ a)
      = baseChangeGradedHom F (W.map φ) (baseChangeGradedHom φ W (Ideal.Quotient.mk _ a))
    rw [bmk, bmk, bmk]
    exact congrArg (Ideal.Quotient.mk _) (MvPolynomial.map_map φ F a).symm
  have key := Proj.map_comp (baseChangeGradedHom φ W) (baseChangeGradedHom F (W.map φ))
    (baseChangeGradedHom_irrelevant_le φ W) (baseChangeGradedHom_irrelevant_le F (W.map φ))
  refine Eq.trans ?_ key
  show Proj.map (baseChangeGradedHom (F.comp φ) W)
      (baseChangeGradedHom_irrelevant_le (F.comp φ) W)
    = Proj.map ((baseChangeGradedHom F (W.map φ)).comp (baseChangeGradedHom φ W)) _
  congr 1

/-- Transport of `(projModelVCIso C V).hom` along an equality of variable changes. -/
private theorem projModelVCIso_congr {C1 C2 : VariableChange R} (hC : C1 = C2)
    (V : WeierstrassCurve R) :
    (projModelVCIso C1 V).hom
      = eqToHom (congrArg projModel (by rw [hC])) ≫ (projModelVCIso C2 V).hom := by
  subst hC; simp

/-- Transport of `(projModelVCIso C V).inv` along an equality of variable changes. -/
private theorem projModelVCIso_inv_congr {C1 C2 : VariableChange R} (hC : C1 = C2)
    (V : WeierstrassCurve R) :
    (projModelVCIso C1 V).inv
      = (projModelVCIso C2 V).inv ≫ eqToHom (congrArg projModel (by rw [hC])) := by
  subst hC; simp

/-- The change-of-variables iso of `E` based at `E⁻¹ • W` is the inverse of the one of `E⁻¹`
based at `W` (up to the transport `E • (E⁻¹ • W) = W`) — the geometric form of `(E⁻¹)⁻¹ = E`,
via `projModelVCIso_mul` and `projModelVCIso_one`. -/
private theorem projModelVCIso_hom_inv_smul (E : VariableChange R) (W : WeierstrassCurve R) :
    (projModelVCIso E (E⁻¹ • W)).hom
      = eqToHom (congrArg projModel (smul_inv_smul E W)) ≫ (projModelVCIso E⁻¹ W).inv := by
  have hone : ((E * E⁻¹) • W) = W := by rw [mul_inv_cancel, one_smul]
  have h1 : (projModelVCIso (E * E⁻¹) W).hom = eqToHom (congrArg projModel hone) := by
    rw [projModelVCIso_congr (mul_inv_cancel E) W, projModelVCIso_one, eqToHom_trans]
  rw [Iso.eq_comp_inv]
  rw [← cancel_epi (eqToHom (congrArg projModel (mul_smul E E⁻¹ W)))]
  rw [← projModelVCIso_mul E E⁻¹ W, h1, eqToHom_trans]

/-- The comparison morphism of the descent: `projModel W₀ ⟶ projModel W₁` over `Spec (R₀ → R)`. -/
noncomputable def descentComparison (W₀ : WeierstrassCurve R) (W₁ : WeierstrassCurve R₀)
    (E : VariableChange R) (hW₁ : W₁.map (algebraMap R₀ R) = E⁻¹ • W₀) :
    projModel W₀ ⟶ projModel W₁ :=
  (projModelVCIso E⁻¹ W₀).inv ≫ eqToHom (congrArg projModel hW₁.symm)
    ≫ projModelBaseChange (algebraMap R₀ R) W₁

/-- π-compatibility of the comparison. -/
theorem descentComparison_π (W₀ : WeierstrassCurve R) (W₁ : WeierstrassCurve R₀)
    (E : VariableChange R) (hW₁ : W₁.map (algebraMap R₀ R) = E⁻¹ • W₀) :
    descentComparison W₀ W₁ E hW₁ ≫ projModelπ W₁
      = projModelπ W₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ R)) := by
  have transπ : ∀ {W W' : WeierstrassCurve R} (h : W = W'),
      eqToHom (congrArg projModel h) ≫ projModelπ W' = projModelπ W := by
    rintro W W' rfl; simp
  rw [descentComparison, Category.assoc, Category.assoc, projModelBaseChange_π,
    reassoc_of% (transπ hW₁.symm), Iso.inv_comp_eq,
    reassoc_of% (projModelVCIso_π E⁻¹ W₀)]

/-- zero-compatibility of the comparison. -/
theorem descentComparison_zero (W₀ : WeierstrassCurve R) (W₁ : WeierstrassCurve R₀)
    (E : VariableChange R) (hW₁ : W₁.map (algebraMap R₀ R) = E⁻¹ • W₀) :
    projModelZero W₀ ≫ descentComparison W₀ W₁ E hW₁
      = Spec.map (CommRingCat.ofHom (algebraMap R₀ R)) ≫ projModelZero W₁ := by
  have transz : ∀ {W W' : WeierstrassCurve R} (h : W = W'),
      projModelZero W ≫ eqToHom (congrArg projModel h) = projModelZero W' := by
    rintro W W' rfl; simp
  rw [descentComparison, ← Category.assoc,
    show projModelZero W₀ ≫ (projModelVCIso E⁻¹ W₀).inv = projModelZero (E⁻¹ • W₀) from by
      rw [Iso.comp_inv_eq, projModelVCIso_zero],
    reassoc_of% (transz hW₁.symm), projModelZero_baseChange]

/-! ### Named steps of the `G`-invariance of the descent comparison -/

/-- The inverse companion of `projModelVCIso_map_hom`: commuting a base change `β_φ` past the
inverse change-of-variables iso `(projModelVCIso C W).inv` rewrites it as the inverse of the
transported iso `(projModelVCIso (C.map φ) (W.map φ)).inv` followed by the base change of the
transformed curve `C • W`. -/
private theorem projModelVCIso_map_inv (φ : R →+* R) (C : VariableChange R)
    (W : WeierstrassCurve R) :
    projModelBaseChange φ W ≫ (projModelVCIso C W).inv
      = (projModelVCIso (C.map φ) (W.map φ)).inv
        ≫ eqToHom (congrArg projModel (map_variableChange W C φ))
        ≫ projModelBaseChange φ (C • W) := by
  rw [Iso.comp_inv_eq]
  simp only [Category.assoc]
  rw [projModelVCIso_map_hom, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Iso.inv_hom_id_assoc]

omit [Algebra R₀ R] in
/-- When `φ : R →+* R` fixes the sub-hom `ψ : R₀ →+* R` (`φ.comp ψ = ψ`), the base change of
`W₁.map ψ` along `φ` followed by the base change along `ψ` collapses — up to the transport
`(W₁.map ψ).map φ = W₁.map ψ` — to the single base change along `ψ`. The mixed-ring
`projModelBaseChange_comp'` composed with the invariance `φ.comp ψ = ψ`. -/
private theorem projModelBaseChange_comp_of_comp_eq (φ : R →+* R) {ψ : R₀ →+* R}
    (W₁ : WeierstrassCurve R₀) (hφψ : φ.comp ψ = ψ) :
    projModelBaseChange φ (W₁.map ψ) ≫ projModelBaseChange ψ W₁
      = eqToHom (congrArg projModel
          (show (W₁.map ψ).map φ = W₁.map ψ by rw [WeierstrassCurve.map_map, hφψ]))
        ≫ projModelBaseChange ψ W₁ := by
  rw [← projModelBaseChange_comp']
  have hbc : ∀ {f f' : R₀ →+* R} (p : f = f'),
      projModelBaseChange f W₁ = eqToHom (by rw [p]) ≫ projModelBaseChange f' W₁ := by
    intro f f' p; subst p; simp
  exact hbc hφψ

/-- The inverse of the `E⁻¹`-iso at `W` equals — up to the transport `E • (E⁻¹ • W) = W` — the
`E`-iso at `E⁻¹ • W`; the `.hom`-side rearrangement of `projModelVCIso_hom_inv_smul`. -/
private theorem projModelVCIso_inv_eq_hom_smul (E : VariableChange R) (W : WeierstrassCurve R) :
    (projModelVCIso E⁻¹ W).inv
      = eqToHom (congrArg projModel (smul_inv_smul E W).symm)
        ≫ (projModelVCIso E (E⁻¹ • W)).hom := by
  rw [projModelVCIso_hom_inv_smul E W, ← Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp]

/-- **Step B of `descentComparison_invariant`.** The change-of-variables isos collapse via the
coboundary identity: with `Cg = E * (g • E)⁻¹` (`hEC`) and `E⁻¹.map τ_g = (g • E)⁻¹` (`hF`), the
composite `V(Cg) ≫ V(E⁻¹.map τ_g)⁻¹` reduces — up to transports — to `V(E⁻¹)⁻¹`. -/
private theorem descentComparison_invariant_stepB
    (W₀ : WeierstrassCurve R) (W₁ : WeierstrassCurve R₀) (E : VariableChange R) (g : G)
    (Cg : VariableChange R)
    (hCW : Cg • (W₀.map (MulSemiringAction.toRingHom G R g)) = W₀)
    (hEC : Cg = E * (g • E)⁻¹)
    (hF : E⁻¹.map (MulSemiringAction.toRingHom G R g) = (g • E)⁻¹)
    (hFW : (g • E)⁻¹ • (W₀.map (MulSemiringAction.toRingHom G R g)) = E⁻¹ • W₀)
    (hc : (E⁻¹.map (MulSemiringAction.toRingHom G R g))
          • (W₀.map (MulSemiringAction.toRingHom G R g)) = W₁.map (algebraMap R₀ R))
    (hW₁ : W₁.map (algebraMap R₀ R) = E⁻¹ • W₀) :
    (projModelVCIso Cg (W₀.map (MulSemiringAction.toRingHom G R g))).hom
        ≫ (projModelVCIso (E⁻¹.map (MulSemiringAction.toRingHom G R g))
            (W₀.map (MulSemiringAction.toRingHom G R g))).inv
        ≫ eqToHom (congrArg projModel hc)
      = eqToHom (congrArg projModel hCW)
        ≫ (projModelVCIso E⁻¹ W₀).inv ≫ eqToHom (congrArg projModel hW₁.symm) := by
  rw [projModelVCIso_congr hEC, projModelVCIso_mul E ((g • E)⁻¹),
    projModelVCIso_inv_congr hF]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, eqToHom_trans, eqToHom_trans_assoc]
  rw [projModelVCIso_natEq rfl (hFW.trans hW₁.symm), projModelVCIso_inv_eq_hom_smul E W₀]
  simp only [Category.assoc, eqToHom_trans_assoc]
  rw [projModelVCIso_natEq rfl hW₁.symm]
  simp only [eqToHom_trans_assoc]

/-- **([a5-W3], G-invariance of the comparison)** With the coboundary identity, the comparison
coequalizes the action: `act g ≫ ψ = ψ`. -/
theorem descentComparison_invariant (W₀ : WeierstrassCurve R) (W₁ : WeierstrassCurve R₀)
    (E : VariableChange R) (hW₁ : W₁.map (algebraMap R₀ R) = E⁻¹ • W₀)
    (Cvc : G → VariableChange R)
    (hCvc : ∀ g, Cvc g • (W₀.map (MulSemiringAction.toRingHom G R g)) = W₀)
    (hE : ∀ g, Cvc g = E * (g • E)⁻¹)
    (hR₀ : ∀ (g : G) (r₀ : R₀), g • (algebraMap R₀ R r₀) = algebraMap R₀ R r₀)
    (act : G → (projModel W₀ ⟶ projModel W₀))
    (hΨ : ∀ g, (projModelVCIso (Cvc g) (W₀.map (MulSemiringAction.toRingHom G R g))).hom
        ≫ projModelBaseChange (MulSemiringAction.toRingHom G R g) W₀
      = eqToHom (congrArg projModel (hCvc g)) ≫ act g)
    (g : G) :
    act g ≫ descentComparison W₀ W₁ E hW₁ = descentComparison W₀ W₁ E hW₁ := by
  -- ring-level: `τ_g ∘ algebraMap = algebraMap` (the subring is `G`-invariant)
  have htau : (MulSemiringAction.toRingHom G R g).comp (algebraMap R₀ R) = algebraMap R₀ R := by
    ext r₀
    exact hR₀ g r₀
  -- variable-change level: `E⁻¹.map τ_g = (g • E)⁻¹`
  have hF : E⁻¹.map (MulSemiringAction.toRingHom G R g) = (g • E)⁻¹ := by
    rw [← vcSMul_eq_map, ← vcSMul_smul_def, smul_inv']
  -- curve level: `(g•E)⁻¹ • (g•W₀) = E⁻¹ • W₀` (from the coboundary identity)
  have hFW : (g • E)⁻¹ • (W₀.map (MulSemiringAction.toRingHom G R g)) = E⁻¹ • W₀ :=
    eq_inv_smul_iff.mpr (by rw [← mul_smul, ← hE g]; exact hCvc g)
  -- curve level: the transported base change of `W₀` is `W₁.map algebraMap`
  have hc : (E⁻¹.map (MulSemiringAction.toRingHom G R g))
        • (W₀.map (MulSemiringAction.toRingHom G R g))
      = W₁.map (algebraMap R₀ R) := by
    rw [hF, hFW, hW₁]
  -- Step A: commute `β_g` past `(projModelVCIso E⁻¹ W₀).inv`
  have hA := projModelVCIso_map_inv (MulSemiringAction.toRingHom G R g) E⁻¹ W₀
  -- Step C: the two base changes compose to a transported single one (`τ_g ∘ alg = alg`)
  have hC2 := projModelBaseChange_comp_of_comp_eq (MulSemiringAction.toRingHom G R g) W₁ htau
  -- Step B: the variable-change isos collapse via the coboundary identity
  have hB := descentComparison_invariant_stepB W₀ W₁ E g (Cvc g) (hCvc g) (hE g) hF hFW hc hW₁
  -- Assemble: reduce `act g ≫ ψ = ψ` to Steps A, C, B via `hΨ g`
  rw [descentComparison]
  rw [← cancel_epi (eqToHom (congrArg projModel (hCvc g))), ← Category.assoc, ← hΨ g]
  simp only [Category.assoc]
  rw [reassoc_of% hA,
    reassoc_of% (projModelBaseChange_natEq (MulSemiringAction.toRingHom G R g) hW₁.symm),
    hC2]
  simp only [eqToHom_trans_assoc]
  rw [reassoc_of% hB]

end ModularCurves

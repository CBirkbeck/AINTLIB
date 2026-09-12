/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.AdditionBaseChange
import ModularCurves.EllipticCurve.Comparison
import ModularCurves.EllipticCurve.GroupLawDescent
import ModularCurves.EllipticCurve.GroupLawConstruction
import ModularCurves.EllipticCurve.WeierstrassAtlasBundle
import ModularCurves.ForMathlib.UnitCocycleSheaf
import ModularCurves.ForMathlib.BaseChangeAlongCompat

/-!
# The invariant differential `ω_{E/S}` (T-OM-B*, route R1)

**(T-E-OMEGA, `/develop --decompose` 2026-07-13, STREAM-OMEGA;
decomposition: `.mathlib-quality/decomposition-omega-r1.md`.)**

For a geometric elliptic curve `G : EllipticCurveGeom S`, the invertible sheaf
`ω_{E/S}` on `S`, DEFINED as the line bundle glued from the Weierstrass-atlas
transition cocycle: on each chart `(U, W, e)` the classical `ω = dx/(2y + a₁x + a₃)`
trivializes `π_*Ω¹_{E/S}`, and on overlaps the two chart bases differ by the unit `u`
of the comparison variable change (Silverman III Table 1.2; KM 2.2; Hida GME §2.2).
Since neither `Ω¹` nor the cotangent complex exists in mathlib, the presentation IS
the definition; every repo consumer (T-E12/T-E13/T-E14 ω-data, T-A4 trivialization,
the modular-forms Hodge bundle) consumes exactly this presentation.

* `LocalPresentation`: a pointed Weierstrass chart of `G` over an affine open.
* `LocalPresentation.transVC`: the UNIQUE variable change comparing two charts over
  the same affine open — existence from the comparison theorem
  `pointedIso_exists_variableChange` (T-W7.1b), uniqueness from
  `projModelVCIso_injective`; the group laws of `transVC` are free from uniqueness.
* `LocalPresentation.transport`: transport of a chart along a cartesian pointed
  square (base change) or along a smaller affine open (restriction, `f = 𝟙`).
* `omegaCocycle`: the glued transition-unit cocycle of the atlas (units glued over
  the possibly non-affine pairwise intersections via `Scheme.exists_unit_glue`).
* `omegaModules` ★: `ω_{E/S}` as an object of `S.Modules`, with
  `Scheme.Modules.IsInvertible` and chart trivializations from the generic layer.
* `OmegaBasis`: the `S`-bases of `ω_{E/S}` (KM 4.6.2's "an S-basis ω of ω_{E/S}"),
  a pseudotorsor under `Γ(S, ⊤)ˣ`; the `{±1} ⊆ Γ(S, ⊤)ˣ` scaling is KM's ±ω.
* `negVC`: the negation variable change `(x, y) ↦ (x, −y − a₁x − a₃)` with unit `−1`;
  `negModelHom` is its model isomorphism — the chart-level input for "the elliptic
  inversion acts on `ω` by `−1`" (assembled at the `(Ell)`-functor level with T-E14).

The `(Ell/R)`-functoriality (base change of bases along cartesian pointed squares,
`omegaBasisMap`) is in `Moduli/OmegaFunctor.lean` (T-OM-B7).
-/

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace ModularCurves

variable {S : Scheme.{u}}

/-! ### T-OM-B1: pointed Weierstrass presentations over an affine open -/

/-- The pullback side-condition for the zero section over an affine open. Extracted from the
`compat_zero` field of `LocalPresentation`: inlining it as a tactic block makes the structure
declaration exceed the elaborator's `whnf` budget on the v4.33 pin. -/
theorem localPresentationZeroCond (G : EllipticCurveGeom S) (V : S.affineOpens) :
    (V.1.ι ≫ G.zero) ≫ G.π = 𝟙 (V.1 : Scheme.{u}) ≫ V.1.ι := by
  rw [Category.assoc, G.zero_π, Category.comp_id, Category.id_comp]

-- The whole elaboration cost of this declaration is the auto-generated injectivity lemma
-- `LocalPresentation.mk.injEq`: proving it forces the kernel to reduce the `e`-field type
-- `pullback G.π V.1.ι ≅ projModel W` — and `projModel` is `@[reducible]`, unfolding to
-- `Proj (quotientGrading (projIdeal W))` — once per field. Measured on the v4.33 pin: with
-- `genInjectivity` on, the declaration needs between 400000 and 1000000 heartbeats (it is the
-- reason this declaration used to carry a 32x heartbeat override); with it off the declaration
-- elaborates in ~2s at the default budget. Nothing in the library uses `mk.injEq` for this
-- structure — presentations are compared through `transVC`/`transUnit`, never by field
-- injectivity — and every projection is still generated, so the field names and types are
-- untouched and all consumers are unaffected.
set_option genInjectivity false in
/-- **(T-OM-B1)** A pointed Weierstrass presentation of a geometric elliptic curve over
an affine open `V`: an elliptic Weierstrass curve over the sections together with a
pointed chart isomorphism — the per-index data of `WeierstrassAtlasData` at a single
affine open. -/
structure LocalPresentation (G : EllipticCurveGeom S) (V : S.affineOpens) where
  /-- The chart Weierstrass curve. -/
  W : WeierstrassCurve Γ(S, V.1)
  /-- The chart curve is elliptic. -/
  elliptic : W.IsElliptic
  /-- The pointed chart isomorphism. -/
  e : pullback G.π V.1.ι ≅ projModel W
  /-- The chart isomorphism respects the structure morphisms. -/
  compat_π : e.hom ≫ projModelπ W = pullback.snd G.π V.1.ι ≫ V.2.isoSpec.hom
  /-- The chart isomorphism respects the zero sections. -/
  compat_zero : (V.2.isoSpec.inv ≫ pullback.lift (V.1.ι ≫ G.zero) (𝟙 _)
      (localPresentationZeroCond G V)) ≫ e.hom =
    projModelZero W

variable {G : EllipticCurveGeom S}

/-- **(T-OM-B1)** The atlas chart at an index, as a `LocalPresentation`. -/
noncomputable def WeierstrassAtlasData.presentation (A : WeierstrassAtlasData G)
    (i : A.ι) : LocalPresentation G (A.U i) where
  W := A.W i
  elliptic := A.elliptic i
  e := A.e i
  compat_π := A.compat_π i
  compat_zero := A.compat_zero i

namespace LocalPresentation

variable {V : S.affineOpens}

/-! ### T-OM-B2: the comparison variable change of two presentations -/

/-- **(T-OM-B2)** The pointed isomorphism of the two chart models induced by two
presentations over the same affine open. -/
noncomputable def pointedIso (P Q : LocalPresentation G V) :
    projModel P.W ≅ projModel Q.W :=
  P.e.symm ≪≫ Q.e

/-- **(T-OM-B2)** The induced model isomorphism respects the structure morphisms. -/
theorem pointedIso_π (P Q : LocalPresentation G V) :
    (P.pointedIso Q).hom ≫ projModelπ Q.W = projModelπ P.W := by
  show (P.e.symm ≪≫ Q.e).hom ≫ projModelπ Q.W = projModelπ P.W
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, Q.compat_π, ← P.compat_π,
    Iso.inv_hom_id_assoc]

/-- **(T-OM-B2)** The induced model isomorphism respects the points at infinity. -/
theorem pointedIso_zero (P Q : LocalPresentation G V) :
    projModelZero P.W ≫ (P.pointedIso Q).hom = projModelZero Q.W := by
  show projModelZero P.W ≫ (P.e.symm ≪≫ Q.e).hom = projModelZero Q.W
  rw [Iso.trans_hom, Iso.symm_hom, ← P.compat_zero, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc, ← Category.assoc]
  exact Q.compat_zero

/-- **(T-OM-B2)** The comparison variable change of two presentations over the same
affine open: the unique `C` with `C • Q.W = P.W` inducing the chart comparison — KM
2.2.5's "two Weierstrass presentations differ by a variable change", by the comparison
theorem (T-W7.1b). -/
noncomputable def transVC (P Q : LocalPresentation G V) : VariableChange Γ(S, V.1) :=
  (pointedIso_exists_variableChange P.W Q.W (P.pointedIso Q) (P.pointedIso_π Q)
    (P.pointedIso_zero Q)).choose

/-- **(T-OM-B2)** The comparison variable change acts by `C • Q.W = P.W`. -/
theorem transVC_smul (P Q : LocalPresentation G V) : P.transVC Q • Q.W = P.W :=
  (pointedIso_exists_variableChange P.W Q.W (P.pointedIso Q) (P.pointedIso_π Q)
    (P.pointedIso_zero Q)).choose_spec.choose

/-- **(T-OM-B2)** The defining property: the chart comparison is the model isomorphism
of the comparison variable change. -/
theorem transVC_spec (P Q : LocalPresentation G V) :
    (P.pointedIso Q).hom =
      eqToHom (by rw [P.transVC_smul Q]) ≫ (projModelVCIso (P.transVC Q) Q.W).hom :=
  (pointedIso_exists_variableChange P.W Q.W (P.pointedIso Q) (P.pointedIso_π Q)
    (P.pointedIso_zero Q)).choose_spec.choose_spec

/-- Transport of the model isomorphism along an equality of curves. -/
private theorem projModelVCIso_congr {R : Type u} [CommRing R]
    {W₁ W₂ : WeierstrassCurve R} (h : W₁ = W₂) (C : VariableChange R) :
    (projModelVCIso C W₁).hom =
      eqToHom (by rw [h]) ≫ (projModelVCIso C W₂).hom ≫ eqToHom (by rw [h]) := by
  cases h
  simp

/-- **(T-OM-B2)** Uniqueness: any variable change with the defining property is the
comparison variable change (faithfulness of the model action,
`projModelVCIso_injective`). -/
theorem transVC_unique (P Q : LocalPresentation G V) (C : VariableChange Γ(S, V.1))
    (hC : C • Q.W = P.W)
    (h : (P.pointedIso Q).hom = eqToHom (by rw [hC]) ≫ (projModelVCIso C Q.W).hom) :
    C = P.transVC Q := by
  refine projModelVCIso_injective C (P.transVC Q) Q.W
    (by rw [hC, P.transVC_smul Q]) ?_
  have h2 := (P.transVC_spec Q).symm.trans h
  -- h2 : eqToHom b ≫ isoT.hom = eqToHom a ≫ isoC.hom
  have h3 := congrArg
    (fun t => eqToHom (show projModel (C • Q.W) = projModel P.W by rw [hC]) ≫ t) h2.symm
  simpa [eqToHom_trans_assoc] using h3

/-- **(T-OM-B2)** Reflexivity: the comparison of a presentation with itself is the
identity variable change (`projModelVCIso_one` + uniqueness). -/
theorem transVC_self (P : LocalPresentation G V) : P.transVC P = 1 :=
  (P.transVC_unique P 1 (one_smul _ _) (by
    show (P.e.symm ≪≫ P.e).hom = _
    rw [Iso.trans_hom, Iso.symm_hom, Iso.inv_hom_id, projModelVCIso_one, eqToHom_trans,
      eqToHom_refl])).symm

/-- **(T-OM-B2)** The cocycle law: comparisons compose according to the group law
(`projModelVCIso_mul` + uniqueness). -/
theorem transVC_trans (P Q R' : LocalPresentation G V) :
    P.transVC Q * Q.transVC R' = P.transVC R' := by
  refine P.transVC_unique R' (P.transVC Q * Q.transVC R')
    (by rw [mul_smul, Q.transVC_smul R', P.transVC_smul Q]) ?_
  have hsplit : (P.pointedIso R').hom = (P.pointedIso Q).hom ≫ (Q.pointedIso R').hom := by
    show (P.e.symm ≪≫ R'.e).hom =
      (P.e.symm ≪≫ Q.e).hom ≫ (Q.e.symm ≪≫ R'.e).hom
    simp [Iso.trans_hom, Iso.symm_hom]
  rw [hsplit, P.transVC_spec Q, Q.transVC_spec R', projModelVCIso_mul]
  rw [projModelVCIso_congr
    (show Q.transVC R' • R'.W = Q.W from Q.transVC_smul R') (P.transVC Q)]
  simp [eqToHom_trans_assoc, Category.assoc]

/-- **(T-OM-B2)** The transition unit of two presentations: the `u`-component of the
comparison variable change — the number by which the two classical chart bases
`dx/(2y + a₁x + a₃)` differ (Silverman III Table 1.2). -/
noncomputable def transUnit (P Q : LocalPresentation G V) : Γ(S, V.1)ˣ :=
  (P.transVC Q).u

/-- **(T-OM-B2)** The transition unit is normalized on the diagonal. -/
theorem transUnit_self (P : LocalPresentation G V) : P.transUnit P = 1 := by
  rw [transUnit, P.transVC_self]
  rfl

/-- **(T-OM-B2)** The transition units satisfy the cocycle law. -/
theorem transUnit_trans (P Q R' : LocalPresentation G V) :
    P.transUnit Q * Q.transUnit R' = P.transUnit R' := by
  rw [transUnit, transUnit, transUnit, ← P.transVC_trans Q R']
  rfl

/-! ### T-OM-B3: transport along a cartesian pointed square, and restriction -/

/-- Sections comparison map along `f : S' ⟶ S` between opens `V' ≤ f ⁻¹ᵁ V`. -/
noncomputable def _root_.ModularCurves.sectionsMapLE {S' : Scheme.{u}} (f : S' ⟶ S)
    {V : S.Opens} {V' : S'.Opens} (h : V' ≤ f ⁻¹ᵁ V) : Γ(S, V) →+* Γ(S', V') :=
  (f.appLE V V' h).hom

/-- The sections comparison map only depends on the morphism (congruence transport;
the inclusion proof adapts along the equality). -/
theorem _root_.ModularCurves.sectionsMapLE_congr_hom {S' : Scheme.{u}} {f g : S' ⟶ S}
    (hfg : f = g) {V : S.Opens} {V' : S'.Opens} (h : V' ≤ f ⁻¹ᵁ V) :
    sectionsMapLE f h = sectionsMapLE g (hfg ▸ h) := by
  cases hfg
  rfl

/-- Transport of an inverse along an `eqToHom`-comparison of the corresponding homs: the
abstract `Iso`/`eqToHom` step shared by every coherence proof below. -/
private theorem inv_eq_eqToHom_comp_inv {C : Type*} [Category C] {X Y Z : C}
    {e₁ : X ≅ Z} {e₂ : X ≅ Y} {w : Y = Z} (h : e₁.hom = e₂.hom ≫ eqToHom w) :
    e₁.inv = eqToHom w.symm ≫ e₂.inv := by
  rw [← cancel_mono e₁.hom, Iso.inv_hom_id, h, Category.assoc, ← Category.assoc e₂.inv,
    Iso.inv_hom_id, Category.id_comp, eqToHom_trans, eqToHom_refl]

/-- Ring-hom form of `projModelVCIso_map`: the model action of a variable change is natural
under coefficient base change. Stated with an explicit ring hom so that the base-change map
has a single spelling (`projModelVCIso_map` phrases it through `algebraMap`). -/
private theorem projModelVCIso_map' {R R' : Type u} [CommRing R] [CommRing R']
    (σ : R →+* R') (C : WeierstrassCurve.VariableChange R) (W : WeierstrassCurve R) :
    projModelBaseChange σ (C • W) ≫ (projModelVCIso C W).hom =
      eqToHom (by rw [map_variableChange]) ≫
        (projModelVCIso (C.map σ) (W.map σ)).hom ≫ projModelBaseChange σ W := by
  letI : Algebra R R' := σ.toAlgebra
  exact projModelVCIso_map C W

section Transport

variable {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}

/-- The scheme-level restriction of `f` intertwines the affine-chart isomorphisms with
`Spec` of the sections comparison (naturality of `isoSpec`; mirrors
`SchemeQuotient.resLE_isoSpec_hom`). -/
lemma resLE_isoSpec_naturality (f : S' ⟶ S) {V : S.affineOpens}
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    f.resLE V.1 V'.1 hV' ≫ V.2.isoSpec.hom =
      V'.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (sectionsMapLE f hV')) := by
  haveI : IsAffine (V.1 : Scheme.{u}) := V.2
  haveI : IsAffine (V'.1 : Scheme.{u}) := V'.2
  have hnat := Scheme.isoSpec_hom_naturality (f.resLE V.1 V'.1 hV')
  show f.resLE V.1 V'.1 hV' ≫
      ((V.1 : Scheme.{u}).isoSpec ≪≫ Scheme.Spec.mapIso V.1.topIso.symm.op).hom =
    ((V'.1 : Scheme.{u}).isoSpec ≪≫ Scheme.Spec.mapIso V'.1.topIso.symm.op).hom ≫
      Spec.map (CommRingCat.ofHom (sectionsMapLE f hV'))
  rw [Iso.trans_hom, ← Category.assoc, ← hnat, Iso.trans_hom, Category.assoc,
    Category.assoc]
  congr 1
  show Spec.map (f.resLE V.1 V'.1 hV').appTop ≫ Spec.map V.1.topIso.inv =
    Spec.map V'.1.topIso.inv ≫ Spec.map (CommRingCat.ofHom (sectionsMapLE f hV'))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  show V.1.topIso.inv ≫ (f.resLE V.1 V'.1 hV').app ⊤ =
    CommRingCat.ofHom (sectionsMapLE f hV') ≫ V'.1.topIso.inv
  rw [Scheme.Hom.resLE_app_top]
  erw [Iso.inv_hom_id_assoc]
  show f.appLE V.1 V'.1 hV' ≫ V'.1.topIso.inv =
    CommRingCat.ofHom ((f.appLE V.1 V'.1 hV').hom) ≫ V'.1.topIso.inv
  rw [CommRingCat.ofHom_hom]

/-- The induced comparison of the restricted curves over a cartesian pointed square. -/
noncomputable def transportTheta (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) {V : S.affineOpens}
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    (pullback G'.π V'.1.ι : Scheme.{u}) ⟶ pullback G.π V.1.ι :=
  pullback.lift (pullback.fst _ _ ≫ t) (pullback.snd _ _ ≫ f.resLE V.1 V'.1 hV') (by
    rw [Category.assoc, hsq.w, ← Category.assoc, pullback.condition, Category.assoc,
      Category.assoc, Scheme.Hom.resLE_comp_ι])

/-- The restricted curves form a cartesian square over the restricted morphism. -/
private lemma transport_isPullback (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) {V : S.affineOpens}
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    IsPullback (transportTheta f t hsq hV') (pullback.snd G'.π V'.1.ι)
      (pullback.snd G.π V.1.ι) (f.resLE V.1 V'.1 hV') := by
  have big := (IsPullback.of_hasPullback G'.π V'.1.ι).paste_horiz hsq
  rw [show V'.1.ι ≫ f = f.resLE V.1 V'.1 hV' ≫ V.1.ι from
    (Scheme.Hom.resLE_comp_ι f hV').symm] at big
  unfold transportTheta
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback G.π V.1.ι)
  rwa [pullback.lift_fst]

/-- The base-change square of the projective model along the sections comparison. -/
lemma transport_isPullback_model (f : S' ⟶ S) {V : S.affineOpens}
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) (P : LocalPresentation G V) :
    IsPullback
      (projModelBaseChange (sectionsMapLE f hV') P.W)
      (projModelπ (P.W.map (sectionsMapLE f hV')))
      (projModelπ P.W)
      (Spec.map (CommRingCat.ofHom (sectionsMapLE f hV'))) := by
  letI : Algebra Γ(S, V.1) Γ(S', V'.1) := (sectionsMapLE f hV').toAlgebra
  exact isPullback_projModelBaseChange P.W

/-- The restricted-curve square transported to the model/`Spec` presentation. -/
private lemma transport_isPullback' (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) {V : S.affineOpens} (P : LocalPresentation G V)
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    IsPullback (transportTheta f t hsq hV' ≫ P.e.hom)
      (pullback.snd G'.π V'.1.ι ≫ V'.2.isoSpec.hom)
      (projModelπ P.W)
      (Spec.map (CommRingCat.ofHom (sectionsMapLE f hV'))) := by
  refine (transport_isPullback f t hsq hV').of_iso (Iso.refl _) P.e V'.2.isoSpec
    V.2.isoSpec ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.id_comp]
  · rw [Iso.refl_hom, Category.id_comp]
  · exact P.compat_π.symm
  · exact resLE_isoSpec_naturality f hV'

/-- The transported chart isomorphism: both sides are pullbacks of the model along
`Spec` of the sections comparison. -/
private noncomputable def transportE (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) {V : S.affineOpens} (P : LocalPresentation G V)
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    (pullback G'.π V'.1.ι : Scheme.{u}) ≅ projModel (P.W.map (sectionsMapLE f hV')) :=
  (transport_isPullback' f t hsq P hV').isoPullback ≪≫
    (transport_isPullback_model f hV' P).isoPullback.symm

private lemma transportE_π (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) {V : S.affineOpens} (P : LocalPresentation G V)
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    (transportE f t hsq P hV').hom ≫ projModelπ (P.W.map (sectionsMapLE f hV')) =
      pullback.snd G'.π V'.1.ι ≫ V'.2.isoSpec.hom := by
  rw [transportE, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    show (transport_isPullback_model f hV' P).isoPullback.inv ≫
        projModelπ (P.W.map (sectionsMapLE f hV')) =
      pullback.snd (projModelπ P.W)
        (Spec.map (CommRingCat.ofHom (sectionsMapLE f hV'))) from
      (transport_isPullback_model f hV' P).isoPullback_inv_snd,
    (transport_isPullback' f t hsq P hV').isoPullback_hom_snd]

/-- **(T-OM-B3 helper, exposed for GH's [GHA3] β2-heart, STREAM-OMEGA v10.262)** The
transported chart isomorphism factors as `transportTheta ≫ P.e` post-composed with the
coefficient base change: the geometric-pull leg of the transport. GH's β2-heart consumes
this as the double-base-change geometric-pull transport (`levelSpaceΓ` on `E` vs `E_T`
matched through the T-D8 fibrewise-generation bridge). -/
lemma transportE_baseChange (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) {V : S.affineOpens} (P : LocalPresentation G V)
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    (transportE f t hsq P hV').hom ≫ projModelBaseChange (sectionsMapLE f hV') P.W =
      transportTheta f t hsq hV' ≫ P.e.hom := by
  rw [transportE, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    show (transport_isPullback_model f hV' P).isoPullback.inv ≫
        projModelBaseChange (sectionsMapLE f hV') P.W =
      pullback.fst (projModelπ P.W)
        (Spec.map (CommRingCat.ofHom (sectionsMapLE f hV'))) from
      (transport_isPullback_model f hV' P).isoPullback_inv_fst,
    (transport_isPullback' f t hsq P hV').isoPullback_hom_fst]

/-- **(T-OM-B3)** Transport of a presentation along a cartesian pointed square over
`f : S' ⟶ S`, to an affine open inside the preimage of the chart: the chart curve is
the coefficient base change, the chart isomorphism the induced comparison of pullbacks
(`isPullback_projModelBaseChange` + pasting). Restriction is the case `f = 𝟙 S`. -/
noncomputable def transport (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    (P : LocalPresentation G V)
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    LocalPresentation G' V' where
  W := P.W.map (sectionsMapLE f hV')
  elliptic := by
    letI := P.elliptic
    exact ⟨by rw [WeierstrassCurve.map_Δ]; exact P.W.isUnit_Δ.map _⟩
  e := transportE f t hsq P hV'
  compat_π := transportE_π f t hsq P hV'
  compat_zero := by
    letI : Algebra Γ(S, V.1) Γ(S', V'.1) := (sectionsMapLE f hV').toAlgebra
    refine (transport_isPullback_model f hV' P).hom_ext ?_ ?_
    · -- the `projModelBaseChange` leg: reduce to `P.compat_zero` via the zero-section
      -- naturality `hz` and `resLE`/`isoSpec` naturality
      rw [Category.assoc, transportE_baseChange,
        show projModelZero (P.W.map (sectionsMapLE f hV')) ≫
            projModelBaseChange (sectionsMapLE f hV') P.W =
          Spec.map (CommRingCat.ofHom (sectionsMapLE f hV')) ≫ projModelZero P.W from
          projModelZero_baseChange P.W]
      -- lift' ≫ θ = resLE ≫ liftV
      rw [show (V'.2.isoSpec.inv ≫ pullback.lift (V'.1.ι ≫ G'.zero) (𝟙 _)
          (by rw [Category.assoc, G'.zero_π, Category.comp_id, Category.id_comp])) ≫
            transportTheta f t hsq hV' ≫ P.e.hom =
          V'.2.isoSpec.inv ≫ (pullback.lift (V'.1.ι ≫ G'.zero) (𝟙 _)
            (by rw [Category.assoc, G'.zero_π, Category.comp_id, Category.id_comp]) ≫
              transportTheta f t hsq hV') ≫ P.e.hom by
            simp only [Category.assoc]]
      rw [show pullback.lift (V'.1.ι ≫ G'.zero) (𝟙 _)
          (by rw [Category.assoc, G'.zero_π, Category.comp_id, Category.id_comp]) ≫
            transportTheta f t hsq hV' =
          f.resLE V.1 V'.1 hV' ≫ pullback.lift (V.1.ι ≫ G.zero) (𝟙 _)
            (by rw [Category.assoc, G.zero_π, Category.comp_id, Category.id_comp]) from ?_]
      · -- finish: isoSpec-naturality + `P.compat_zero`
        rw [show V'.2.isoSpec.inv ≫ (f.resLE V.1 V'.1 hV' ≫ pullback.lift (V.1.ι ≫ G.zero)
            (𝟙 _) (by rw [Category.assoc, G.zero_π, Category.comp_id, Category.id_comp])) ≫
              P.e.hom =
            (V'.2.isoSpec.inv ≫ f.resLE V.1 V'.1 hV' ≫ V.2.isoSpec.hom) ≫
              (V.2.isoSpec.inv ≫ pullback.lift (V.1.ι ≫ G.zero) (𝟙 _)
                (by rw [Category.assoc, G.zero_π, Category.comp_id, Category.id_comp])) ≫
                P.e.hom by simp only [Category.assoc, Iso.hom_inv_id_assoc]]
        rw [P.compat_zero, resLE_isoSpec_naturality f hV', Iso.inv_hom_id_assoc]
      · -- the two lifts agree (compare both pullback legs; `hz` enters the `fst` leg)
        unfold transportTheta
        refine pullback.hom_ext ?_ ?_
        · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
            Category.assoc, hz, ← Category.assoc, ← Scheme.Hom.resLE_comp_ι f hV',
            Category.assoc, Category.assoc, pullback.lift_fst]
        · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
            Category.id_comp, Category.assoc, pullback.lift_snd, Category.comp_id]
    · -- the `π` leg: both sides are the identity on `Spec Γ(V')`
      rw [Category.assoc, transportE_π, projModelZero_projModelπ]
      rw [show (V'.2.isoSpec.inv ≫ pullback.lift (V'.1.ι ≫ G'.zero) (𝟙 _)
          (by rw [Category.assoc, G'.zero_π, Category.comp_id, Category.id_comp])) ≫
            pullback.snd G'.π V'.1.ι ≫ V'.2.isoSpec.hom =
          V'.2.isoSpec.inv ≫ (pullback.lift (V'.1.ι ≫ G'.zero) (𝟙 _)
            (by rw [Category.assoc, G'.zero_π, Category.comp_id, Category.id_comp]) ≫
              pullback.snd G'.π V'.1.ι) ≫ V'.2.isoSpec.hom by simp only [Category.assoc]]
      rw [pullback.lift_snd, Category.id_comp, Iso.inv_hom_id]
      rfl

end Transport

@[simp] theorem transport_W {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    (P : LocalPresentation G V)
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    (P.transport f t hsq hz hV').W = P.W.map (sectionsMapLE f hV') :=
  rfl

/-- The chart isomorphism of a transported presentation, as a `transportE`. Doing this
reduction once, on free variables, keeps every coherence proof below from re-unfolding
`transport` under a projection-headed term. -/
private theorem transport_e {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    (P : LocalPresentation G V)
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    (P.transport f t hsq hz hV').e = transportE f t hsq P hV' :=
  rfl

/-- **(T-OM-B3)** Restriction of a presentation to a smaller affine open: transport
along the identity square. -/
noncomputable def restrict (P : LocalPresentation G V) {V' : S.affineOpens}
    (h : V'.1 ≤ V.1) : LocalPresentation G V' :=
  P.transport (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩) (by simp)
    (by simpa using h)

/-- The chart isomorphism of a restricted presentation, as a `transportE`. -/
private theorem restrict_e (P : LocalPresentation G V) {V' : S.affineOpens}
    (h : V'.1 ≤ V.1) :
    (P.restrict h).e = transportE (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩) P
      (show V'.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ V.1 by simpa using h) :=
  rfl

/-! ### T-OM-B4: naturality of the comparison under transport -/

lemma projModelZero_congr {R : Type u} [CommRing R] {W₁ W₂ : WeierstrassCurve R}
    (h : W₁ = W₂) :
    projModelZero W₁ = projModelZero W₂ ≫ eqToHom (by rw [h]) := by
  cases h
  simp

lemma projModelBaseChange_congr_hom {R : Type u} [CommRing R] {R' : Type u}
    [CommRing R'] {σ₁ σ₂ : R →+* R'} (h : σ₁ = σ₂) (W : WeierstrassCurve R) :
    projModelBaseChange σ₁ W =
      eqToHom (by rw [h]) ≫ projModelBaseChange σ₂ W := by
  cases h
  simp

lemma projModelBaseChange_congr'' {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
    (σ : R →+* R') {W₁ W₂ : WeierstrassCurve R} (h : W₁ = W₂) :
    projModelBaseChange σ W₁ =
      eqToHom (by rw [h]) ≫ projModelBaseChange σ W₂ ≫ eqToHom (by rw [h]) := by
  cases h
  simp

lemma projModelπ_congr {R : Type u} [CommRing R] {W₁ W₂ : WeierstrassCurve R}
    (h : W₁ = W₂) :
    eqToHom (congrArg projModel h) ≫ projModelπ W₂ = projModelπ W₁ := by
  cases h; simp

private lemma projModelBaseChange_congr {R R' : Type u} [CommRing R] [CommRing R']
    (σ : R →+* R') {W₁ W₂ : WeierstrassCurve R} (h : W₁ = W₂) :
    projModelBaseChange σ W₂ ≫ eqToHom (show projModel W₂ = projModel W₁ by rw [h]) =
      eqToHom (show projModel (W₂.map σ) = projModel (W₁.map σ) by rw [h]) ≫
        projModelBaseChange σ W₁ := by
  cases h; simp

/-- **(T-OM-B4)** The comparison variable change of two presentations, base-changed, acts on
the transported chart curves (`map_variableChange` + `transVC_smul`). -/
private theorem transVC_map_smul_transport {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    (P Q : LocalPresentation G V)
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    (P.transVC Q).map (sectionsMapLE f hV') • (Q.transport f t hsq hz hV').W =
      (P.transport f t hsq hz hV').W := by
  show (P.transVC Q).map (sectionsMapLE f hV') • Q.W.map (sectionsMapLE f hV') =
    P.W.map (sectionsMapLE f hV')
  rw [map_variableChange, P.transVC_smul Q]

/-- The variable-change half of the naturality of the comparison under transport, on free
curves: base-changing the model action of `C` gives the model action of `C.map σ`. Stated with
no scheme, presentation or `transport` in sight, so the `eqToHom` bookkeeping never has to be
reassociated underneath a projection-headed term. -/
private theorem projModelBaseChange_vcIso {R R' : Type u} [CommRing R] [CommRing R']
    (σ : R →+* R') (C : WeierstrassCurve.VariableChange R) (W₁ W₂ : WeierstrassCurve R)
    (hC : C • W₂ = W₁) (hm : C.map σ • W₂.map σ = W₁.map σ) :
    projModelBaseChange σ W₁ ≫
        eqToHom (congrArg projModel hC.symm) ≫ (projModelVCIso C W₂).hom =
      (eqToHom (congrArg projModel hm.symm) ≫
        (projModelVCIso (C.map σ) (W₂.map σ)).hom) ≫ projModelBaseChange σ W₂ := by
  rw [← Category.assoc, projModelBaseChange_congr σ hC, Category.assoc,
    projModelVCIso_map' σ C W₂, ← Category.assoc, eqToHom_trans, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The geometric half of the naturality of the comparison under transport: the comparison of
the two transported presentations intertwines the model base changes with the comparison
downstairs. Kept separate from the variable-change bookkeeping below so that neither half has
to reassociate under a projection-headed `transport` term. -/
private theorem pointedIso_transport_hom {S' : Scheme.{u}}
    {G' : EllipticCurveGeom S'} (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    (P Q : LocalPresentation G V)
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    ((P.transport f t hsq hz hV').pointedIso (Q.transport f t hsq hz hV')).hom ≫
        projModelBaseChange (sectionsMapLE f hV') Q.W =
      projModelBaseChange (sectionsMapLE f hV') P.W ≫ (P.pointedIso Q).hom := by
  rw [show ((P.transport f t hsq hz hV').pointedIso (Q.transport f t hsq hz hV')).hom =
    (transportE f t hsq P hV').inv ≫ (transportE f t hsq Q hV').hom from rfl]
  simp only [Category.assoc]
  rw [transportE_baseChange f t hsq Q hV']
  rw [show transportTheta f t hsq hV' ≫ Q.e.hom =
    (transportTheta f t hsq hV' ≫ P.e.hom) ≫ (P.pointedIso Q).hom by
      simp [pointedIso, Iso.trans_hom, Iso.symm_hom]]
  rw [← transportE_baseChange f t hsq P hV', Category.assoc, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The model-base-change leg of the naturality of the comparison under transport. -/
private theorem pointedIso_transport_baseChange {S' : Scheme.{u}}
    {G' : EllipticCurveGeom S'} (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    (P Q : LocalPresentation G V)
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1)
    (hsmul : (P.transVC Q).map (sectionsMapLE f hV') • (Q.transport f t hsq hz hV').W =
      (P.transport f t hsq hz hV').W) :
    ((P.transport f t hsq hz hV').pointedIso (Q.transport f t hsq hz hV')).hom ≫
        projModelBaseChange (sectionsMapLE f hV') Q.W =
      (eqToHom (congrArg projModel hsmul.symm) ≫
        (projModelVCIso ((P.transVC Q).map (sectionsMapLE f hV'))
          (Q.transport f t hsq hz hV').W).hom) ≫
        projModelBaseChange (sectionsMapLE f hV') Q.W := by
  rw [pointedIso_transport_hom f t hsq hz P Q hV', P.transVC_spec Q]
  exact projModelBaseChange_vcIso (sectionsMapLE f hV') (P.transVC Q) P.W Q.W
    (P.transVC_smul Q) hsmul

/-- The `projModelπ` leg of the naturality of the comparison under transport. -/
private theorem pointedIso_transport_π {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    (P Q : LocalPresentation G V)
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1)
    (hsmul : (P.transVC Q).map (sectionsMapLE f hV') • (Q.transport f t hsq hz hV').W =
      (P.transport f t hsq hz hV').W) :
    ((P.transport f t hsq hz hV').pointedIso (Q.transport f t hsq hz hV')).hom ≫
        projModelπ (Q.transport f t hsq hz hV').W =
      (eqToHom (congrArg projModel hsmul.symm) ≫
        (projModelVCIso ((P.transVC Q).map (sectionsMapLE f hV'))
          (Q.transport f t hsq hz hV').W).hom) ≫
        projModelπ (Q.transport f t hsq hz hV').W := by
  rw [(P.transport f t hsq hz hV').pointedIso_π (Q.transport f t hsq hz hV'),
    Category.assoc, projModelVCIso_π, projModelπ_congr]
  exact hsmul.symm

set_option backward.isDefEq.respectTransparency false in
/-- **(T-OM-B4)** The comparison variable change is natural under transport: the
comparison of the transported presentations is the coefficient base change of the
comparison (`projModelVCIso_map` + `map_variableChange` + uniqueness). -/
theorem transVC_transport {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    (P Q : LocalPresentation G V)
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    (P.transport f t hsq hz hV').transVC (Q.transport f t hsq hz hV') =
      (P.transVC Q).map (sectionsMapLE f hV') := by
  have hsmul := transVC_map_smul_transport f t hsq hz P Q hV'
  refine ((P.transport f t hsq hz hV').transVC_unique (Q.transport f t hsq hz hV')
    ((P.transVC Q).map (sectionsMapLE f hV')) hsmul ?_).symm
  refine (transport_isPullback_model f hV' Q).hom_ext ?_ ?_
  · exact pointedIso_transport_baseChange f t hsq hz P Q hV' hsmul
  · exact pointedIso_transport_π f t hsq hz P Q hV' hsmul

/-- **(T-OM-B4)** The transition unit is natural under transport. -/
theorem transUnit_transport {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    (P Q : LocalPresentation G V)
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    (P.transport f t hsq hz hV').transUnit (Q.transport f t hsq hz hV') =
      Units.map (sectionsMapLE f hV').toMonoidHom (P.transUnit Q) := by
  rw [transUnit, transUnit, transVC_transport f t hsq hz P Q hV']
  rfl

/-- The sections comparison of the identity morphism is restriction. -/
theorem sectionsMapLE_id {V' V : S.Opens} (h : V' ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ V) :
    sectionsMapLE (𝟙 S) h = Scheme.resLE (X := S) (show V' ≤ V by simpa using h) := by
  have harr : (𝟙 S : S ⟶ S).appLE V V' h =
      S.presheaf.map (homOfLE (show V' ≤ V by simpa using h)).op := by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    erw [Category.id_comp]
    rfl
  exact congrArg CommRingCat.Hom.hom harr

/-- The chart curve of a doubly restricted presentation is the chart curve of the composite
restriction (`WeierstrassCurve.map_map` through `Scheme.resLE_comp`). -/
private theorem restrict_restrict_W {VP : S.affineOpens} (P : LocalPresentation G VP)
    {V V'' : S.affineOpens} (p : V.1 ≤ VP.1) (h : V''.1 ≤ V.1) :
    (P.restrict (h.trans p)).W = ((P.restrict p).restrict h).W := by
  show P.W.map _ = (P.W.map _).map _
  rw [WeierstrassCurve.map_map]
  congr 1
  rw [sectionsMapLE_id, sectionsMapLE_id, sectionsMapLE_id, Scheme.resLE_comp]

/-- **(T-OM-B4)** Restriction form of the naturality: transition units restrict to
transition units. -/
theorem transUnit_restrict (P Q : LocalPresentation G V) {V' : S.affineOpens}
    (h : V'.1 ≤ V.1) :
    (P.restrict h).transUnit (Q.restrict h) =
      Scheme.resUnit h (P.transUnit Q) := by
  rw [restrict, restrict, transUnit_transport (𝟙 S) (𝟙 G.E)
    (IsPullback.of_horiz_isIso ⟨by simp⟩) (by simp) P Q (by simpa using h)]
  refine Units.ext ?_
  show sectionsMapLE (𝟙 S) (by simpa using h) (P.transUnit Q).val = _
  rw [sectionsMapLE_id]
  rfl

/-- The induced comparisons of restrictions compose. -/
private lemma transportTheta_comp {V V'' : S.affineOpens} {VP : S.affineOpens}
    (p : V.1 ≤ VP.1) (h : V''.1 ≤ V.1) :
    transportTheta (G' := G) (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
        (V := V) (V' := V'') (by simpa using h) ≫
      transportTheta (G' := G) (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
        (V := VP) (V' := V) (by simpa using p) =
    transportTheta (G' := G) (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
        (V := VP) (V' := V'') (by simpa using h.trans p) := by
  unfold transportTheta
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
      pullback.lift_fst, Category.assoc, Category.comp_id, Category.comp_id]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
      pullback.lift_snd, Category.assoc, Scheme.Hom.resLE_comp_resLE]
    congr 1

private lemma projModelBaseChangeOf_congr_f {U R : Type u} [CommRing U] [CommRing R]
    {f f' : U →+* R} (hf : f = f') (W₀ : WeierstrassCurve U) (W : WeierstrassCurve R)
    (hh : W₀.map f = W) (hh' : W₀.map f' = W) :
    projModelBaseChangeOf f W₀ W hh = projModelBaseChangeOf f' W₀ W hh' := by
  subst hf; rfl

/-- ★ The transport-coherence square, stated once and abstractly. Two morphisms out of the
same scheme into the successive coefficient base changes of `W` along a factorisation
`σ = σ₂ ∘ σ₁`, each compatible with the base-change morphism and with the model projection,
agree up to the canonical transport `eqToHom`; this is uniqueness of maps into the
base-change pullback square `isPullback_projModelBaseChangeOf`. All four transport-coherence
lemmas below (`restrict`/`restrict`, `restrict`/`transport`, `transport`/`restrict`,
`transport`/`transport`) are instances of it. -/
private lemma transportE_comp {R R₁ R₂ : Type u} [CommRing R] [CommRing R₁] [CommRing R₂]
    {σ₁ : R →+* R₁} {σ₂ : R₁ →+* R₂} {σ : R →+* R₂} (hσ : σ = σ₂.comp σ₁)
    {W : WeierstrassCurve R} (hW : W.map σ = (W.map σ₁).map σ₂)
    {X X₁ X₂ : Scheme.{u}} (a : X ⟶ projModel W) (θ₁ : X₁ ⟶ X) (θ₂ : X₂ ⟶ X₁)
    (e₁ : X₁ ⟶ projModel (W.map σ₁))
    {e₂ : X₂ ⟶ projModel ((W.map σ₁).map σ₂)} {e : X₂ ⟶ projModel (W.map σ)}
    {p₂ : X₂ ⟶ Spec (CommRingCat.of R₂)}
    (he₁ : e₁ ≫ projModelBaseChange σ₁ W = θ₁ ≫ a)
    (he₂ : e₂ ≫ projModelBaseChange σ₂ (W.map σ₁) = θ₂ ≫ e₁)
    (he₂π : e₂ ≫ projModelπ ((W.map σ₁).map σ₂) = p₂)
    (he : e ≫ projModelBaseChange σ W = θ₂ ≫ θ₁ ≫ a)
    (heπ : e ≫ projModelπ (W.map σ) = p₂) :
    e₂ = e ≫ eqToHom (congrArg projModel hW) := by
  refine (isPullback_projModelBaseChangeOf σ W ((W.map σ₁).map σ₂) hW).hom_ext ?_ ?_
  · have hL : e₂ ≫ projModelBaseChangeOf σ W ((W.map σ₁).map σ₂) hW = θ₂ ≫ θ₁ ≫ a := by
      rw [projModelBaseChangeOf_congr_f hσ W _ hW (by rw [← hσ]; exact hW),
        projModelBaseChangeOf_comp σ₂ σ₁ W (W.map σ₁) rfl ((W.map σ₁).map σ₂) rfl,
        projModelBaseChangeOf_rfl, projModelBaseChangeOf_rfl, ← Category.assoc, he₂,
        Category.assoc, he₁]
    have hR : (e ≫ eqToHom (congrArg projModel hW)) ≫
        projModelBaseChangeOf σ W ((W.map σ₁).map σ₂) hW = θ₂ ≫ θ₁ ≫ a := by
      rw [Category.assoc, projModelBaseChangeOf, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp, he]
    exact hL.trans hR.symm
  · rw [Category.assoc, projModelπ_congr hW, heπ, he₂π]

set_option backward.isDefEq.respectTransparency false in
/-- Double restriction agrees with the composite restriction on chart isomorphisms
(uniqueness of pullback comparisons, through `projModelBaseChangeOf`). -/
private lemma transportE_restrict_restrict {VP : S.affineOpens}
    (P : LocalPresentation G VP)
    {V V'' : S.affineOpens} (p : V.1 ≤ VP.1) (h : V''.1 ≤ V.1) :
    ((P.restrict p).restrict h).e.hom =
      (P.restrict (h.trans p)).e.hom ≫
        eqToHom (congrArg projModel (restrict_restrict_W P p h)) := by
  have hfeq : sectionsMapLE (𝟙 S)
      (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using h.trans p) =
      (sectionsMapLE (𝟙 S) (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ V.1 by simpa using h)).comp
        (sectionsMapLE (𝟙 S) (show V.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using p)) := by
    rw [sectionsMapLE_id, sectionsMapLE_id, sectionsMapLE_id, Scheme.resLE_comp]
  have hbc := transportE_baseChange (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩) P
    (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using h.trans p)
  rw [← transportTheta_comp p h, Category.assoc] at hbc
  rw [restrict_e (P.restrict p) h, restrict_e P (h.trans p)]
  exact transportE_comp hfeq (restrict_restrict_W P p h) _ _ _ _
    (transportE_baseChange (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩) P
      (show V.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using p))
    (transportE_baseChange (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
      (P.restrict p) (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ V.1 by simpa using h))
    (transportE_π (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
      (P.restrict p) (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ V.1 by simpa using h))
    hbc
    (transportE_π (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩) P
      (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using h.trans p))

/-- **(T-OM-B7 coherence)** The comparison variable change only depends on the
presentations through their charts up to the canonical transport: presentations with
equal curves and `eqToHom`-related chart isomorphisms have equal comparisons. -/
theorem transVC_congr {V'' : S.affineOpens} (P₁ P₂ Q₁ Q₂ : LocalPresentation G V'')
    (w₁ : Q₁.W = P₁.W) (w₂ : Q₂.W = P₂.W)
    (he₁ : P₁.e.hom = Q₁.e.hom ≫ eqToHom (by rw [w₁]))
    (he₂ : P₂.e.hom = Q₂.e.hom ≫ eqToHom (by rw [w₂])) :
    P₁.transVC P₂ = Q₁.transVC Q₂ := by
  have hQ₁inv : Q₁.e.inv =
      eqToHom (show projModel Q₁.W = projModel P₁.W by rw [w₁]) ≫ P₁.e.inv :=
    inv_eq_eqToHom_comp_inv (w := show projModel P₁.W = projModel Q₁.W by rw [w₁])
      (by rw [he₁, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])
  have hQ₂hom : Q₂.e.hom = P₂.e.hom ≫
      eqToHom (show projModel P₂.W = projModel Q₂.W by rw [w₂]) := by
    rw [he₂, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  refine Q₁.transVC_unique Q₂ (P₁.transVC P₂) (by rw [w₂, w₁]; exact P₁.transVC_smul P₂) ?_
  show (Q₁.e.symm ≪≫ Q₂.e).hom = _
  rw [Iso.trans_hom, Iso.symm_hom, hQ₁inv, hQ₂hom]
  simp only [Category.assoc]
  rw [← Category.assoc P₁.e.inv,
    show P₁.e.inv ≫ P₂.e.hom = (P₁.pointedIso P₂).hom from rfl, P₁.transVC_spec P₂,
    projModelVCIso_congr w₂ (P₁.transVC P₂)]
  simp only [Category.assoc, eqToHom_trans_assoc]

/-- **(T-OM-B7 coherence, unit form)** -/
theorem transUnit_congr {V'' : S.affineOpens} (P₁ P₂ Q₁ Q₂ : LocalPresentation G V'')
    (w₁ : Q₁.W = P₁.W) (w₂ : Q₂.W = P₂.W)
    (he₁ : P₁.e.hom = Q₁.e.hom ≫ eqToHom (by rw [w₁]))
    (he₂ : P₂.e.hom = Q₂.e.hom ≫ eqToHom (by rw [w₂])) :
    P₁.transUnit P₂ = Q₁.transUnit Q₂ := by
  rw [transUnit, transUnit, transVC_congr P₁ P₂ Q₁ Q₂ w₁ w₂ he₁ he₂]

set_option backward.isDefEq.respectTransparency false in
/-- **(T-OM-B5 coherence)** Double restriction agrees with the composite restriction on
comparison variable changes (uniqueness through the chart-isomorphism coherence).
(Un-`private`d for the engine mouth core's Stage-3 chart-Čech cocycle laws,
`Moduli/EngineDescent.lean`.) -/
theorem transVC_restrict_restrict {VP VQ : S.affineOpens}
    (P : LocalPresentation G VP) (Q : LocalPresentation G VQ)
    {V V'' : S.affineOpens} (p : V.1 ≤ VP.1) (q : V.1 ≤ VQ.1) (h : V''.1 ≤ V.1) :
    ((P.restrict p).restrict h).transVC ((Q.restrict q).restrict h) =
      (P.restrict (h.trans p)).transVC (Q.restrict (h.trans q)) :=
  transVC_congr _ _ _ _ (restrict_restrict_W P p h) (restrict_restrict_W Q q h)
    (transportE_restrict_restrict P p h) (transportE_restrict_restrict Q q h)

set_option backward.isDefEq.respectTransparency false in
/-- **(T-OM-B5 coherence, unit form)** Restricting a transition unit twice agrees with
the composite restriction. -/
theorem transUnit_restrict_restrict {VP VQ : S.affineOpens}
    (P : LocalPresentation G VP) (Q : LocalPresentation G VQ)
    {V V'' : S.affineOpens} (p : V.1 ≤ VP.1) (q : V.1 ≤ VQ.1) (h : V''.1 ≤ V.1) :
    ((P.restrict p).restrict h).transUnit ((Q.restrict q).restrict h) =
      (P.restrict (h.trans p)).transUnit (Q.restrict (h.trans q)) := by
  rw [transUnit, transUnit, transVC_restrict_restrict P Q p q h]

/-- Sections comparisons compose with restrictions. -/
theorem sectionsMapLE_comp_resLE {S' : Scheme.{u}} (f : S' ⟶ S) {V : S.Opens}
    {V' V'' : S'.Opens} (hV' : V' ≤ f ⁻¹ᵁ V) (h : V'' ≤ V') :
    (Scheme.resLE h).comp (sectionsMapLE f hV') = sectionsMapLE f (h.trans hV') :=
  RingHom.ext fun r => Scheme.resLE_appLE f hV' h r

/-- The chart curve of a restricted transport is the chart curve of the composite transport. -/
private theorem transport_restrict_W {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    {V : S.affineOpens} (P : LocalPresentation G V)
    {V' V'' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) (h : V''.1 ≤ V'.1) :
    (P.transport f t hsq hz (h.trans hV')).W =
      ((P.transport f t hsq hz hV').restrict h).W := by
  show P.W.map _ = (P.W.map _).map _
  rw [WeierstrassCurve.map_map]
  congr 1
  rw [sectionsMapLE_id, sectionsMapLE_comp_resLE f hV' h]

/-- The induced comparison of a restriction followed by a transport composes. -/
private lemma transportTheta_comp' {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E) (hsq : IsPullback t G'.π G.π f)
    {V : S.affineOpens} {V' V'' : S'.affineOpens}
    (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) (h : V''.1 ≤ V'.1) :
    transportTheta (G' := G') (𝟙 S') (𝟙 G'.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
        (V := V') (V' := V'') (by simpa using h) ≫
      transportTheta f t hsq hV' =
    transportTheta f t hsq (h.trans hV') := by
  unfold transportTheta
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
      pullback.lift_fst, Category.assoc, Category.id_comp]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
      pullback.lift_snd, Category.assoc, Scheme.Hom.resLE_comp_resLE]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- **(T-OM-B7 coherence)** Restricting a transported chart agrees with transporting
to the smaller affine open. -/
private lemma transportE_restrict_transport {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    {V : S.affineOpens} (P : LocalPresentation G V)
    {V' V'' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) (h : V''.1 ≤ V'.1) :
    ((P.transport f t hsq hz hV').restrict h).e.hom =
      (P.transport f t hsq hz (h.trans hV')).e.hom ≫
        eqToHom (show projModel (P.transport f t hsq hz (h.trans hV')).W =
            projModel ((P.transport f t hsq hz hV').restrict h).W by
          show projModel (P.W.map _) = projModel ((P.W.map _).map _)
          rw [WeierstrassCurve.map_map]
          congr 2
          rw [sectionsMapLE_id, sectionsMapLE_comp_resLE f hV' h]) := by
  have hfeq : sectionsMapLE f (h.trans hV') =
      (sectionsMapLE (𝟙 S') (show V''.1 ≤ (𝟙 S' : S' ⟶ S') ⁻¹ᵁ V'.1 by simpa using h)).comp
        (sectionsMapLE f hV') := by
    rw [sectionsMapLE_id, sectionsMapLE_comp_resLE f hV' h]
  have hbc := transportE_baseChange f t hsq P (h.trans hV')
  rw [← transportTheta_comp' f t hsq hV' h, Category.assoc] at hbc
  rw [restrict_e (P.transport f t hsq hz hV') h, transport_e f t hsq hz P (h.trans hV')]
  exact transportE_comp hfeq (transport_restrict_W f t hsq hz P hV' h) _ _ _ _
    (transportE_baseChange f t hsq P hV')
    (transportE_baseChange (𝟙 S') (𝟙 G'.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
      (P.transport f t hsq hz hV')
      (show V''.1 ≤ (𝟙 S' : S' ⟶ S') ⁻¹ᵁ V'.1 by simpa using h))
    (transportE_π (𝟙 S') (𝟙 G'.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
      (P.transport f t hsq hz hV')
      (show V''.1 ≤ (𝟙 S' : S' ⟶ S') ⁻¹ᵁ V'.1 by simpa using h))
    hbc (transportE_π f t hsq P (h.trans hV'))


/-- Sections comparisons absorb restrictions on the source side. -/
theorem resLE_comp_sectionsMapLE {S' : Scheme.{u}} (f : S' ⟶ S) {U U' : S.Opens}
    (hU : U ≤ U') {W : S'.Opens} (h : W ≤ f ⁻¹ᵁ U) :
    (sectionsMapLE f h).comp (Scheme.resLE hU) =
      sectionsMapLE f (h.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hU)).le) :=
  RingHom.ext fun r => Scheme.appLE_resLE f hU h r

/-- The chart curve of a transported restriction is the chart curve of the composite
transport. -/
private theorem restrict_transport_W {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    {VP : S.affineOpens} (P : LocalPresentation G VP)
    {W₀ : S.affineOpens} {V'' : S'.affineOpens}
    (w : W₀.1 ≤ VP.1) (hV'' : V''.1 ≤ f ⁻¹ᵁ W₀.1) :
    (P.transport f t hsq hz
        (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le)).W =
      ((P.restrict w).transport f t hsq hz hV'').W := by
  show P.W.map _ = (P.W.map _).map _
  rw [WeierstrassCurve.map_map]
  congr 1
  rw [sectionsMapLE_id, resLE_comp_sectionsMapLE f w hV'']

/-- The induced comparison of a transport followed by a restriction composes. -/
private lemma transportTheta_comp'' {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E) (hsq : IsPullback t G'.π G.π f)
    {W₀ VP : S.affineOpens} {V'' : S'.affineOpens}
    (w : W₀.1 ≤ VP.1) (hV'' : V''.1 ≤ f ⁻¹ᵁ W₀.1) :
    transportTheta f t hsq hV'' ≫
      transportTheta (G' := G) (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
        (V := VP) (V' := W₀) (by simpa using w) =
    transportTheta f t hsq (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le) := by
  unfold transportTheta
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
      pullback.lift_fst, Category.assoc, Category.comp_id]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
      pullback.lift_snd, Category.assoc, Scheme.Hom.resLE_comp_resLE]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- **(T-OM-B7 coherence)** Transporting a restricted chart agrees with transporting
along the composite. -/
lemma transportE_transport_restrict {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    {VP : S.affineOpens} (P : LocalPresentation G VP)
    {W₀ : S.affineOpens} {V'' : S'.affineOpens}
    (w : W₀.1 ≤ VP.1) (hV'' : V''.1 ≤ f ⁻¹ᵁ W₀.1) :
    ((P.restrict w).transport f t hsq hz hV'').e.hom =
      (P.transport f t hsq hz
        (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le)).e.hom ≫
        eqToHom (show projModel (P.transport f t hsq hz
            (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le)).W =
            projModel ((P.restrict w).transport f t hsq hz hV'').W by
          show projModel (P.W.map _) = projModel ((P.W.map _).map _)
          rw [WeierstrassCurve.map_map]
          congr 2
          rw [sectionsMapLE_id, resLE_comp_sectionsMapLE f w hV'']) := by
  have hfeq : sectionsMapLE f (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le) =
      (sectionsMapLE f hV'').comp
        (sectionsMapLE (𝟙 S) (show W₀.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using w)) := by
    rw [sectionsMapLE_id, resLE_comp_sectionsMapLE f w hV'']
  have hbc := transportE_baseChange f t hsq P
    (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le)
  rw [← transportTheta_comp'' f t hsq w hV'', Category.assoc] at hbc
  rw [transport_e f t hsq hz (P.restrict w) hV'', transport_e f t hsq hz P
    (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le)]
  exact transportE_comp hfeq (restrict_transport_W f t hsq hz P w hV'') _ _ _ _
    (transportE_baseChange (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩) P
      (show W₀.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using w))
    (transportE_baseChange f t hsq (P.restrict w) hV'')
    (transportE_π f t hsq (P.restrict w) hV'')
    hbc
    (transportE_π f t hsq P
      (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le))


/-- **(T-OM-B7 coherence, packaged)** Restricting a transported pair agrees with the
composite transports. -/
theorem transUnit_transport_pair_restrict {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    {VA VB : S.affineOpens} (A : LocalPresentation G VA) (B : LocalPresentation G VB)
    {V' V'' : S'.affineOpens} (hA : V'.1 ≤ f ⁻¹ᵁ VA.1) (hB : V'.1 ≤ f ⁻¹ᵁ VB.1)
    (h : V''.1 ≤ V'.1) :
    ((A.transport f t hsq hz hA).restrict h).transUnit
      ((B.transport f t hsq hz hB).restrict h) =
    (A.transport f t hsq hz (h.trans hA)).transUnit
      (B.transport f t hsq hz (h.trans hB)) := by
  refine transUnit_congr _ _ _ _ ?_ ?_ ?_ ?_
  · exact transport_restrict_W f t hsq hz A hA h
  · exact transport_restrict_W f t hsq hz B hB h
  · exact transportE_restrict_transport f t hsq hz A hA h
  · exact transportE_restrict_transport f t hsq hz B hB h

/-- **(T-OM-B7 coherence, packaged)** Transporting a restricted pair agrees with the
composite transports. -/
theorem transUnit_restrict_pair_transport {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    {VA VB : S.affineOpens} (A : LocalPresentation G VA) (B : LocalPresentation G VB)
    {W₀ : S.affineOpens} {V'' : S'.affineOpens}
    (wA : W₀.1 ≤ VA.1) (wB : W₀.1 ≤ VB.1) (hV'' : V''.1 ≤ f ⁻¹ᵁ W₀.1) :
    ((A.restrict wA).transport f t hsq hz hV'').transUnit
      ((B.restrict wB).transport f t hsq hz hV'') =
    (A.transport f t hsq hz
        (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE wA)).le)).transUnit
      (B.transport f t hsq hz
        (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE wB)).le)) := by
  refine transUnit_congr _ _ _ _ ?_ ?_ ?_ ?_
  · exact restrict_transport_W f t hsq hz A wA hV''
  · exact restrict_transport_W f t hsq hz B wB hV''
  · exact transportE_transport_restrict f t hsq hz A wA hV''
  · exact transportE_transport_restrict f t hsq hz B wB hV''

/-- Sections comparisons compose along composable morphisms. -/
theorem sectionsMapLE_comp {S'' S' : Scheme.{u}} (f : S'' ⟶ S') (g : S' ⟶ S)
    {V : S.Opens} {V' : S'.Opens} {V'' : S''.Opens}
    (hV' : V' ≤ g ⁻¹ᵁ V) (hV'' : V'' ≤ f ⁻¹ᵁ V') :
    (sectionsMapLE f hV'').comp (sectionsMapLE g hV') =
      sectionsMapLE (f ≫ g)
        (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le) := by
  refine RingHom.ext fun r => ?_
  show (g.appLE V V' hV' ≫ f.appLE V' V'' hV'').hom r = _
  rw [Scheme.Hom.appLE_comp_appLE]
  rfl

/-- The chart curve of a doubly transported presentation is the chart curve of the transport
along the pasted square. -/
private theorem transport_transport_W {S'' S' : Scheme.{u}}
    {G'' : EllipticCurveGeom S''} {G' : EllipticCurveGeom S'}
    (f : S'' ⟶ S') (g : S' ⟶ S) (t : G''.E ⟶ G'.E) (s : G'.E ⟶ G.E)
    (hsq_f : IsPullback t G''.π G'.π f) (hsq_g : IsPullback s G'.π G.π g)
    (hz_f : G''.zero ≫ t = f ≫ G'.zero) (hz_g : G'.zero ≫ s = g ≫ G.zero)
    (hzc : G''.zero ≫ t ≫ s = (f ≫ g) ≫ G.zero)
    {V : S.affineOpens} (P : LocalPresentation G V)
    {V' : S'.affineOpens} {V'' : S''.affineOpens}
    (hV' : V'.1 ≤ g ⁻¹ᵁ V.1) (hV'' : V''.1 ≤ f ⁻¹ᵁ V'.1) :
    (P.transport (f ≫ g) (t ≫ s) (hsq_f.paste_horiz hsq_g) hzc
        (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le)).W =
      ((P.transport g s hsq_g hz_g hV').transport f t hsq_f hz_f hV'').W := by
  show P.W.map _ = (P.W.map _).map _
  rw [WeierstrassCurve.map_map]
  congr 1
  rw [sectionsMapLE_comp f g hV' hV'']

/-- The induced comparisons compose along composable squares. -/
private lemma transportTheta_transportTheta {S'' S' : Scheme.{u}}
    {G'' : EllipticCurveGeom S''} {G' : EllipticCurveGeom S'}
    (f : S'' ⟶ S') (g : S' ⟶ S) (t : G''.E ⟶ G'.E) (s : G'.E ⟶ G.E)
    (hsq_f : IsPullback t G''.π G'.π f) (hsq_g : IsPullback s G'.π G.π g)
    {V : S.affineOpens} {V' : S'.affineOpens} {V'' : S''.affineOpens}
    (hV' : V'.1 ≤ g ⁻¹ᵁ V.1) (hV'' : V''.1 ≤ f ⁻¹ᵁ V'.1) :
    transportTheta f t hsq_f hV'' ≫ transportTheta g s hsq_g hV' =
      transportTheta (f ≫ g) (t ≫ s) (hsq_f.paste_horiz hsq_g)
        (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le) := by
  unfold transportTheta
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
      pullback.lift_fst, Category.assoc]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
      pullback.lift_snd, Category.assoc, Scheme.Hom.resLE_comp_resLE]

set_option backward.isDefEq.respectTransparency false in
/-- **(T-OM-B7 coherence)** Transporting a transported chart agrees with transporting
along the composite square. -/
lemma transportE_transport_transport {S'' S' : Scheme.{u}}
    {G'' : EllipticCurveGeom S''} {G' : EllipticCurveGeom S'}
    (f : S'' ⟶ S') (g : S' ⟶ S) (t : G''.E ⟶ G'.E) (s : G'.E ⟶ G.E)
    (hsq_f : IsPullback t G''.π G'.π f) (hsq_g : IsPullback s G'.π G.π g)
    (hz_f : G''.zero ≫ t = f ≫ G'.zero) (hz_g : G'.zero ≫ s = g ≫ G.zero)
    {V : S.affineOpens} (P : LocalPresentation G V)
    {V' : S'.affineOpens} {V'' : S''.affineOpens}
    (hV' : V'.1 ≤ g ⁻¹ᵁ V.1) (hV'' : V''.1 ≤ f ⁻¹ᵁ V'.1) :
    ((P.transport g s hsq_g hz_g hV').transport f t hsq_f hz_f hV'').e.hom =
      (P.transport (f ≫ g) (t ≫ s) (hsq_f.paste_horiz hsq_g)
        (by rw [← Category.assoc, hz_f, Category.assoc, hz_g, ← Category.assoc] :
          G''.zero ≫ t ≫ s = (f ≫ g) ≫ G.zero)
        (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le)).e.hom ≫
        eqToHom (show projModel (P.transport (f ≫ g) (t ≫ s) (hsq_f.paste_horiz hsq_g) _
            (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le)).W =
            projModel ((P.transport g s hsq_g hz_g hV').transport f t hsq_f hz_f hV'').W by
          show projModel (P.W.map _) = projModel ((P.W.map _).map _)
          rw [WeierstrassCurve.map_map]
          congr 2
          rw [sectionsMapLE_comp f g hV' hV'']) := by
  have hzc : G''.zero ≫ t ≫ s = (f ≫ g) ≫ G.zero := by
    rw [← Category.assoc, hz_f, Category.assoc, hz_g, ← Category.assoc]
  have hfeq : sectionsMapLE (f ≫ g)
      (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le) =
      (sectionsMapLE f hV'').comp (sectionsMapLE g hV') := by
    rw [sectionsMapLE_comp f g hV' hV'']
  have hbc := transportE_baseChange (f ≫ g) (t ≫ s) (hsq_f.paste_horiz hsq_g) P
    (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le)
  rw [← transportTheta_transportTheta f g t s hsq_f hsq_g hV' hV'', Category.assoc] at hbc
  rw [transport_e f t hsq_f hz_f (P.transport g s hsq_g hz_g hV') hV'',
    transport_e (f ≫ g) (t ≫ s) (hsq_f.paste_horiz hsq_g) hzc P
      (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le)]
  exact transportE_comp hfeq
    (transport_transport_W f g t s hsq_f hsq_g hz_f hz_g hzc P hV' hV'') _ _ _ _
    (transportE_baseChange g s hsq_g P hV')
    (transportE_baseChange f t hsq_f (P.transport g s hsq_g hz_g hV') hV'')
    (transportE_π f t hsq_f (P.transport g s hsq_g hz_g hV') hV'')
    hbc
    (transportE_π (f ≫ g) (t ≫ s) (hsq_f.paste_horiz hsq_g) P
      (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le))


/-- **(T-OM-B7 coherence, packaged)** Transporting a transported pair agrees with the
composite transports. -/
theorem transUnit_transport_pair_transport {S'' S' : Scheme.{u}}
    {G'' : EllipticCurveGeom S''} {G' : EllipticCurveGeom S'}
    (f : S'' ⟶ S') (g : S' ⟶ S) (t : G''.E ⟶ G'.E) (s : G'.E ⟶ G.E)
    (hsq_f : IsPullback t G''.π G'.π f) (hsq_g : IsPullback s G'.π G.π g)
    (hz_f : G''.zero ≫ t = f ≫ G'.zero) (hz_g : G'.zero ≫ s = g ≫ G.zero)
    {VA VB : S.affineOpens} (A : LocalPresentation G VA) (B : LocalPresentation G VB)
    {V'A : S'.affineOpens} {V'B : S'.affineOpens} {V'' : S''.affineOpens}
    (hA : V'A.1 ≤ g ⁻¹ᵁ VA.1) (hB : V'B.1 ≤ g ⁻¹ᵁ VB.1)
    (hA' : V''.1 ≤ f ⁻¹ᵁ V'A.1) (hB' : V''.1 ≤ f ⁻¹ᵁ V'B.1) :
    ((A.transport g s hsq_g hz_g hA).transport f t hsq_f hz_f hA').transUnit
      ((B.transport g s hsq_g hz_g hB).transport f t hsq_f hz_f hB') =
    (A.transport (f ≫ g) (t ≫ s) (hsq_f.paste_horiz hsq_g)
        (by rw [← Category.assoc, hz_f, Category.assoc, hz_g, ← Category.assoc])
        (hA'.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hA)).le)).transUnit
      (B.transport (f ≫ g) (t ≫ s) (hsq_f.paste_horiz hsq_g)
        (by rw [← Category.assoc, hz_f, Category.assoc, hz_g, ← Category.assoc])
        (hB'.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hB)).le)) := by
  refine transUnit_congr _ _ _ _ ?_ ?_ ?_ ?_
  · exact transport_transport_W f g t s hsq_f hsq_g hz_f hz_g
      (by rw [← Category.assoc, hz_f, Category.assoc, hz_g, ← Category.assoc]) A hA hA'
  · exact transport_transport_W f g t s hsq_f hsq_g hz_f hz_g
      (by rw [← Category.assoc, hz_f, Category.assoc, hz_g, ← Category.assoc]) B hB hB'
  · exact transportE_transport_transport f g t s hsq_f hsq_g hz_f hz_g A hA hA'
  · exact transportE_transport_transport f g t s hsq_f hsq_g hz_f hz_g B hB hB'

/-- **(T-OM-B7 coherence, packaged)** Restriction of a transported presentation is the
transported presentation, up to the canonical comparison — the `transUnit`-level form
consumed by the ω-functoriality glue. -/
theorem transUnit_restrict_transport {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    {VQ : S'.affineOpens} (Q : LocalPresentation G' VQ)
    {V : S.affineOpens} (P : LocalPresentation G V)
    {V' V'' : S'.affineOpens} (hQ : V'.1 ≤ VQ.1) (hV' : V'.1 ≤ f ⁻¹ᵁ V.1)
    (h : V''.1 ≤ V'.1) :
    ((Q.restrict hQ).restrict h).transUnit ((P.transport f t hsq hz hV').restrict h) =
      (Q.restrict (h.trans hQ)).transUnit (P.transport f t hsq hz (h.trans hV')) := by
  refine transUnit_congr _ _ _ _ ?_ ?_ ?_ ?_
  · exact restrict_restrict_W Q hQ h
  · exact transport_restrict_W f t hsq hz P hV' h
  · exact transportE_restrict_restrict Q hQ h
  · exact transportE_restrict_transport f t hsq hz P hV' h

end LocalPresentation

/-! ### T-OM-B5: the ω-cocycle of the atlas -/

open Scheme in
/-- The glued transition unit of a pair of atlas charts, with its affine-local
characterization. -/
private noncomputable def omegaGlue (G : EllipticCurveGeom S) (i j : G.atlas.ι) :
    { g : Γ(S, (G.atlas.U i).1 ⊓ (G.atlas.U j).1)ˣ //
      ∀ (V : S.affineOpens) (hV : V.1 ≤ (G.atlas.U i).1 ⊓ (G.atlas.U j).1),
        resUnit hV g =
          ((G.atlas.presentation i).restrict (hV.trans inf_le_left)).transUnit
            ((G.atlas.presentation j).restrict (hV.trans inf_le_right)) } := by
  have hglue := Scheme.exists_unit_glue S ((G.atlas.U i).1 ⊓ (G.atlas.U j).1)
    (fun V hV =>
      ((G.atlas.presentation i).restrict (hV.trans inf_le_left)).transUnit
        ((G.atlas.presentation j).restrict (hV.trans inf_le_right)))
    (fun V V' hV h => by
      rw [← LocalPresentation.transUnit_restrict,
        LocalPresentation.transUnit_restrict_restrict])
  exact ⟨hglue.choose, hglue.choose_spec.1⟩

open Scheme in
/-- **(T-OM-B5)** The transition cocycle of the invariant differential: on each pair of
atlas charts, the transition units of the affine-locally restricted chart comparisons,
glued over the pairwise intersection (`Scheme.exists_unit_glue`); the cocycle laws hold
affine-locally by `transUnit_trans` and glue by uniqueness. -/
noncomputable def omegaCocycle (G : EllipticCurveGeom S) : UnitCocycle S where
  ι := G.atlas.ι
  U i := (G.atlas.U i).1
  covers := G.atlas.covers
  u i j := (omegaGlue G i j).1
  u_self i := Scheme.unit_ext_of_affine_res S (fun V hV => by
    rw [(omegaGlue G i i).2 V hV, LocalPresentation.transUnit_self, map_one])
  u_cocycle i j k := Scheme.unit_ext_of_affine_res S (fun V hV => by
    rw [map_mul, Scheme.resUnit_resUnit, Scheme.resUnit_resUnit, Scheme.resUnit_resUnit,
      (omegaGlue G i j).2 V _, (omegaGlue G j k).2 V _, (omegaGlue G i k).2 V _,
      LocalPresentation.transUnit_trans])

open Scheme in
/-- **(T-OM-B5)** The defining property of the glued cocycle: on every affine open
inside a pairwise intersection, it restricts to the transition unit of the restricted
chart comparisons. -/
theorem omegaCocycle_res (G : EllipticCurveGeom S) (i j : G.atlas.ι)
    (V : S.affineOpens) (hV : V.1 ≤ (G.atlas.U i).1 ⊓ (G.atlas.U j).1) :
    resUnit hV ((omegaCocycle G).u i j) =
      ((G.atlas.presentation i).restrict (hV.trans inf_le_left)).transUnit
        ((G.atlas.presentation j).restrict (hV.trans inf_le_right)) :=
  (omegaGlue G i j).2 V hV

/-! ### T-OM-B6 ★: the invariant differential -/

open Scheme in
/-- **(T-OM-B6 ★)** The invariant differential `ω_{E/S}`: the invertible sheaf on `S`
glued from the Weierstrass-atlas transition cocycle. On each chart it is trivialized by
the classical `dx/(2y + a₁x + a₃)` (KM 2.2, GME §2.2); the transitions are the
comparison units (Silverman III Table 1.2). -/
noncomputable def omegaModules (G : EllipticCurveGeom S) : S.Modules :=
  (omegaCocycle G).lineBundle

open Scheme in
/-- **(T-OM-B6 ★)** `ω_{E/S}` is an invertible `𝒪_S`-module. -/
theorem omegaModules_isInvertible (G : EllipticCurveGeom S) :
    Modules.IsInvertible (omegaModules G) :=
  (omegaCocycle G).lineBundle_isInvertible

open Scheme in
/-- **(T-OM-B6)** An `S`-basis of `ω_{E/S}` (KM 4.6.2: "an `S`-basis `ω` of
`ω_{E/S}`"): a global section that is a unit in every chart trivialization. -/
def OmegaBasis (G : EllipticCurveGeom S) : Type u :=
  {b : (omegaCocycle G).sections ⊤ // (omegaCocycle G).IsBasis b}

open Scheme in
/-- **(T-OM-B6)** The global units act on the `S`-bases of `ω_{E/S}` — the `{±1}`
action of KM 4.6.2 is the restriction of this action to `⟨-1⟩`. -/
noncomputable instance (G : EllipticCurveGeom S) : SMul Γ(S, ⊤)ˣ (OmegaBasis G) :=
  ⟨fun g b => ⟨g.val • b.1, ((omegaCocycle G).isBasis_smul_iff g b.1).mpr b.2⟩⟩

open Scheme in
/-- **(T-OM-B6)** The `S`-bases of `ω_{E/S}` form a pseudotorsor under the global
units: any two bases differ by a unique global unit — the `𝔾ₘ`-trivialization the
board records as "ω3 = T-A4's torsor form". -/
theorem OmegaBasis.existsUnique_unit_smul {G : EllipticCurveGeom S}
    (b b' : OmegaBasis G) : ∃! g : Γ(S, ⊤)ˣ, g • b = b' := by
  obtain ⟨g₀, hg₀, hg₀uniq⟩ := (omegaCocycle G).exists_unique_smul_eq b.2 b'.1
  obtain ⟨h₀, hh₀, -⟩ := (omegaCocycle G).exists_unique_smul_eq b'.2 b.1
  have hgh : g₀ * h₀ = 1 := by
    refine (omegaCocycle G).smul_left_injective b'.2 (g := g₀ * h₀) (g' := 1) ?_
    rw [mul_smul, hh₀, hg₀, one_smul]
  have hhg : h₀ * g₀ = 1 := by rw [mul_comm]; exact hgh
  refine ⟨⟨g₀, h₀, hgh, hhg⟩, Subtype.ext hg₀, fun g₁ hg₁ => Units.ext ?_⟩
  exact hg₀uniq g₁.val (congrArg Subtype.val hg₁)

/-! ### T-OM-B8: the negation variable change -/

variable {R : Type u} [CommRing R]

/-- **(T-OM-B8)** The negation variable change `(x, y) ↦ (x, −y − a₁x − a₃)`
(Silverman III.1): `u = −1`, `r = 0`, `s = −a₁`, `t = −a₃`. -/
def negVC (W : WeierstrassCurve R) : VariableChange R :=
  ⟨-1, 0, -W.a₁, -W.a₃⟩

/-- **(T-OM-B8)** The negation variable change has unit `−1` — through the ω-cocycle,
the elliptic inversion scales every basis of `ω_{E/S}` by `−1` (KM 4.6.2's `{±1}`). -/
@[simp] theorem negVC_u (W : WeierstrassCurve R) : (negVC W).u = -1 :=
  rfl

/-- **(T-OM-B8)** The negation variable change fixes the curve. -/
theorem negVC_smul (W : WeierstrassCurve R) : negVC W • W = W := by
  ext <;>
    simp [negVC, WeierstrassCurve.variableChange_def, Units.val_neg, Units.val_one] <;>
    ring

/-- **(T-OM-B8)** The negation and variable-change substitution vectors agree. -/
theorem vcMvSubst_negVC (W : WeierstrassCurve R) : vcMvSubst (negVC W) = negVec W := by
  funext i
  fin_cases i <;>
    simp [vcMvSubst, negVC, negVec, MvPolynomial.smul_eq_C_mul, Units.val_neg,
      Units.val_one] <;>
    ring

private lemma mk_heq' {R' : Type u} [CommRing R'] {V V' : WeierstrassCurve R'} (e : V = V')
    (q : MvPolynomial (Fin 3) R') :
    HEq (Ideal.Quotient.mk (projIdeal V).toIdeal q)
      (Ideal.Quotient.mk (projIdeal V').toIdeal q) := by
  subst e; rfl

private lemma gradedHom_heq' {R' : Type u} [CommRing R'] (W : WeierstrassCurve R')
    {V V' : WeierstrassCurve R'} (e : V = V')
    (g : GradedRingHom (quotientGrading (projIdeal W))
      (quotientGrading (projIdeal V)))
    (g' : GradedRingHom (quotientGrading (projIdeal W))
      (quotientGrading (projIdeal V')))
    (h : ∀ x, HEq (g x) (g' x)) : HEq g g' := by
  subst e
  exact heq_of_eq (GradedRingHom.ext fun x => eq_of_heq (h x))

private lemma projMap_transport_heq' {R' : Type u} [CommRing R'] (W : WeierstrassCurve R')
    {V V' : WeierstrassCurve R'} (e : V' = V)
    (g : GradedRingHom (quotientGrading (projIdeal W))
      (quotientGrading (projIdeal V)))
    (hg : (quotientGrading (projIdeal V))₊ ≤ ((quotientGrading (projIdeal W))₊).map g)
    (g' : GradedRingHom (quotientGrading (projIdeal W))
      (quotientGrading (projIdeal V')))
    (hg' : (quotientGrading (projIdeal V'))₊ ≤ ((quotientGrading (projIdeal W))₊).map g')
    (hgg : HEq g g') :
    Proj.map g hg = eqToHom (congrArg projModel e.symm) ≫ Proj.map g' hg' := by
  subst e
  obtain rfl := eq_of_heq hgg
  rw [eqToHom_refl, Category.id_comp]

/-- **(T-OM-B8)** The negation morphism of the projective model is the model
isomorphism of the negation variable change: both are `Proj.map` of the same graded
substitution (`negVec` vs `vcMvSubst (negVC W)`). -/
theorem negModelHom_eq_negVC (W : WeierstrassCurve R) :
    negModelHom W = eqToHom (by rw [negVC_smul]) ≫ (projModelVCIso (negVC W) W).hom := by
  have key : (projModelVCIso (negVC W) W).hom =
      eqToHom (congrArg projModel (negVC_smul W)) ≫ negModelHom W := by
    rw [show (projModelVCIso (negVC W) W).hom =
      Proj.map (vcGradedHom (negVC W) W) (vcGradedHom_irrelevant_le (negVC W) W) from rfl,
      negModelHom]
    refine projMap_transport_heq' W (e := (negVC_smul W).symm) _ _ _ _
      (gradedHom_heq' W (negVC_smul W) _ _ fun x => ?_)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [vcGradedHom, quotientGradingMap_mk, negGradedQuot,
      quotientGradingMap_mk]
    refine (mk_heq' (negVC_smul W) _).trans (heq_of_eq (congrArg _ ?_))
    show MvPolynomial.aeval (vcMvSubst (negVC W)) a = (MvPolynomial.aeval (negVec W)) a
    rw [vcMvSubst_negVC]
  rw [key, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

/-! ### T-OM-B9 (geometric half): the inversion transports charts by `negVC` -/

/-- **(T-OM-B9)** The negation variable change commutes with coefficient base change. -/
theorem negVC_map {R' : Type u} [CommRing R'] (σ : R →+* R') (W : WeierstrassCurve R) :
    (negVC W).map σ = negVC (W.map σ) := by
  ext <;> simp [negVC, WeierstrassCurve.VariableChange.map, WeierstrassCurve.map]

set_option backward.isDefEq.respectTransparency false in
/-- **(T-OM-B9)** The glued negation is an involution (per-chart:
`negModelHom_negModelHom` conjugated through the chart isomorphisms). -/
theorem negHomOf_negHomOf {S : Scheme.{u}} {G : EllipticCurveGeom S}
    (A : WeierstrassAtlasData G) : negHomOf A ≫ negHomOf A = 𝟙 G.E := by
  refine (atlasTotalCover A).hom_ext _ _ (fun i => ?_)
  haveI := A.elliptic (show A.ι from i)
  rw [Category.comp_id, ← Category.assoc, negHomOf_piece]
  show ((A.e i).hom ≫ negModelHom (A.W i) ≫ (A.e i).inv ≫
      pullback.fst G.π (A.U i).1.ι) ≫ negHomOf A = (atlasTotalCover A).f i
  simp only [Category.assoc, negHomOf_piece']
  simp only [negPiece, Category.assoc]
  rw [Iso.inv_hom_id_assoc, reassoc_of% negModelHom_negModelHom (A.W i),
    Iso.hom_inv_id_assoc, atlasTotalCover_f]

/-- **(T-OM-B9)** The negation of a geometric elliptic curve is an involution. -/
theorem EllipticCurveGeom.negHom_negHom {S : Scheme.{u}} (G : EllipticCurveGeom S) :
    G.negHom ≫ G.negHom = 𝟙 G.E :=
  negHomOf_negHomOf G.atlas

instance {S : Scheme.{u}} (G : EllipticCurveGeom S) : IsIso G.negHom :=
  ⟨G.negHom, G.negHom_negHom, G.negHom_negHom⟩

/-- **(T-OM-B9)** The negation square of a geometric elliptic curve is cartesian over
the identity. -/
theorem EllipticCurveGeom.isPullback_negHom {S : Scheme.{u}} (G : EllipticCurveGeom S) :
    IsPullback G.negHom G.π G.π (𝟙 S) :=
  IsPullback.of_horiz_isIso ⟨by rw [G.negHom_π, Category.comp_id]⟩

/-- **(T-OM-B9)** The negation square is pointed. -/
theorem EllipticCurveGeom.negHom_zero_w {S : Scheme.{u}} (G : EllipticCurveGeom S) :
    G.zero ≫ G.negHom = 𝟙 S ≫ G.zero :=
  G.negHom_zero.trans (Category.id_comp _).symm

namespace LocalPresentation

variable {S : Scheme.{u}} {G : EllipticCurveGeom S}

set_option backward.isDefEq.respectTransparency false in
/-- The comparison of the restricted curves along the negation square factors as the
identity comparison followed by the chart-conjugated model negation (the
presentation-level `negPiece` identity). -/
private theorem transportTheta_neg (i : G.atlas.ι)
    (hsq : IsPullback G.negHom G.π G.π (𝟙 S))
    {V' : S.affineOpens} (hV' : V'.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ (G.atlas.U i).1) :
    transportTheta (𝟙 S) G.negHom hsq hV' =
      transportTheta (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩) hV' ≫
        (G.atlas.e i).hom ≫ negModelHom (G.atlas.W i) ≫ (G.atlas.e i).inv := by
  haveI := G.atlas.elliptic i
  have hconj : (G.atlas.e i).hom ≫ negModelHom (G.atlas.W i) ≫ (G.atlas.e i).inv ≫
      pullback.snd G.π (G.atlas.U i).1.ι = pullback.snd G.π (G.atlas.U i).1.ι := by
    have hinv : (G.atlas.e i).inv ≫ pullback.snd G.π (G.atlas.U i).1.ι =
        projModelπ (G.atlas.W i) ≫ (G.atlas.U i).2.isoSpec.inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, G.atlas.compat_π i, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    rw [hinv, reassoc_of% negModelHom_π (G.atlas.W i), ← Category.assoc,
      G.atlas.compat_π i, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine pullback.hom_ext ?_ ?_
  · show transportTheta (𝟙 S) G.negHom hsq hV' ≫ pullback.fst G.π (G.atlas.U i).1.ι = _
    unfold transportTheta
    rw [pullback.lift_fst]
    simp only [Category.assoc]
    rw [show (G.atlas.e i).hom ≫ negModelHom (G.atlas.W i) ≫ (G.atlas.e i).inv ≫
        pullback.fst G.π (G.atlas.U i).1.ι = negPiece G.atlas i from rfl,
      ← negHomOf_piece', ← Category.assoc, pullback.lift_fst]
    simp only [Category.comp_id, Category.id_comp, Category.assoc]
    rfl
  · show transportTheta (𝟙 S) G.negHom hsq hV' ≫ pullback.snd G.π (G.atlas.U i).1.ι = _
    unfold transportTheta
    rw [pullback.lift_snd]
    simp only [Category.assoc]
    rw [hconj, pullback.lift_snd]

set_option backward.isDefEq.respectTransparency false in
/-- **(T-OM-B9 core)** Transporting an atlas chart along the inversion square compares
to its plain restriction by exactly the negation variable change — KM 4.6.2's `{±1}`:
`[-1]^* ω = −ω` chartwise (through `negModelHom_eq_negVC`). -/
theorem transVC_transport_neg (i : G.atlas.ι)
    (hsq : IsPullback G.negHom G.π G.π (𝟙 S)) (hz : G.zero ≫ G.negHom = 𝟙 S ≫ G.zero)
    {V' : S.affineOpens} (hV' : V'.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ (G.atlas.U i).1) :
    ((G.atlas.presentation i).restrict hV').transVC
        ((G.atlas.presentation i).transport (𝟙 S) G.negHom hsq hz hV') =
      negVC (((G.atlas.presentation i).restrict hV').W) := by
  haveI := G.atlas.elliptic i
  refine (transVC_unique ((G.atlas.presentation i).restrict hV')
    ((G.atlas.presentation i).transport (𝟙 S) G.negHom hsq hz hV')
    (negVC (((G.atlas.presentation i).restrict hV').W)) (negVC_smul _) ?_).symm
  refine Eq.trans ?_ (negModelHom_eq_negVC _)
  -- the pointed comparison is the model negation of the restricted chart
  show (((G.atlas.presentation i).restrict hV').e.symm ≪≫
      ((G.atlas.presentation i).transport (𝟙 S) G.negHom hsq hz hV').e).hom = _
  rw [Iso.trans_hom, Iso.symm_hom, Iso.inv_comp_eq]
  -- both `e`s are `transportE`s sharing the model-square factor
  show (transportE (𝟙 S) G.negHom hsq (G.atlas.presentation i) hV').hom =
    (transportE (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
      (G.atlas.presentation i) hV').hom ≫ negModelHom _
  unfold transportE
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.comp_inv_eq]
  simp only [Category.assoc]
  refine pullback.hom_ext ?_ ?_
  · -- the base-change leg: `negModelHom_baseChange` through the model square
    rw [Category.assoc, Category.assoc, Category.assoc,
      (transport_isPullback' (𝟙 S) G.negHom hsq (G.atlas.presentation i)
        hV').isoPullback_hom_fst,
      show (transport_isPullback_model (𝟙 S) hV'
          (G.atlas.presentation i)).isoPullback.hom ≫
          pullback.fst (projModelπ (G.atlas.presentation i).W)
            (Spec.map (CommRingCat.ofHom (sectionsMapLE (𝟙 S) hV'))) =
        projModelBaseChange (sectionsMapLE (𝟙 S) hV') (G.atlas.presentation i).W from
        (transport_isPullback_model (𝟙 S) hV'
          (G.atlas.presentation i)).isoPullback_hom_fst,
      negModelHom_baseChange (sectionsMapLE (𝟙 S) hV') (G.atlas.presentation i).W,
      reassoc_of% (transport_isPullback_model (𝟙 S) hV'
        (G.atlas.presentation i)).isoPullback_inv_fst,
      reassoc_of% (transport_isPullback' (𝟙 S) (𝟙 G.E)
        (IsPullback.of_horiz_isIso ⟨by simp⟩) (G.atlas.presentation i)
        hV').isoPullback_hom_fst,
      transportTheta_neg i hsq hV']
    simp only [Category.assoc]
    show transportTheta (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩) hV' ≫
        (G.atlas.e i).hom ≫ negModelHom (G.atlas.W i) ≫ (G.atlas.e i).inv ≫
        (G.atlas.e i).hom =
      transportTheta (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩) hV' ≫
        (G.atlas.e i).hom ≫ negModelHom (G.atlas.W i)
    rw [Iso.inv_hom_id, Category.comp_id (negModelHom (G.atlas.W i))]
  · -- the `π` leg: negation is over the base
    rw [Category.assoc, Category.assoc, Category.assoc,
      (transport_isPullback' (𝟙 S) G.negHom hsq (G.atlas.presentation i)
        hV').isoPullback_hom_snd,
      show (transport_isPullback_model (𝟙 S) hV'
          (G.atlas.presentation i)).isoPullback.hom ≫
          pullback.snd (projModelπ (G.atlas.presentation i).W)
            (Spec.map (CommRingCat.ofHom (sectionsMapLE (𝟙 S) hV'))) =
        projModelπ ((G.atlas.presentation i).W.map (sectionsMapLE (𝟙 S) hV')) from
        (transport_isPullback_model (𝟙 S) hV'
          (G.atlas.presentation i)).isoPullback_hom_snd,
      negModelHom_π ((G.atlas.presentation i).W.map (sectionsMapLE (𝟙 S) hV')),
      (transport_isPullback_model (𝟙 S) hV'
        (G.atlas.presentation i)).isoPullback_inv_snd,
      (transport_isPullback' (𝟙 S) (𝟙 G.E)
        (IsPullback.of_horiz_isIso ⟨by simp⟩) (G.atlas.presentation i)
        hV').isoPullback_hom_snd]

/-- **(T-OM-B9)** The transition unit of the inversion transport is `−1`. -/
theorem transUnit_transport_neg (i : G.atlas.ι)
    (hsq : IsPullback G.negHom G.π G.π (𝟙 S)) (hz : G.zero ≫ G.negHom = 𝟙 S ≫ G.zero)
    {V' : S.affineOpens} (hV' : V'.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ (G.atlas.U i).1) :
    ((G.atlas.presentation i).restrict hV').transUnit
        ((G.atlas.presentation i).transport (𝟙 S) G.negHom hsq hz hV') = -1 := by
  rw [transUnit, transVC_transport_neg]
  rfl

open Scheme WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-B)** The `π`-compatibility of the twist of a presentation by a variable
change (`projModelVCIso_π`). -/
private theorem chartCompatπ_ofVC {V : S.affineOpens} (P : LocalPresentation G V)
    (C : VariableChange Γ(S, V.1)) :
    (P.e ≪≫ (projModelVCIso C P.W).symm).hom ≫ projModelπ (C • P.W) =
      pullback.snd G.π V.1.ι ≫ V.2.isoSpec.hom := by
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← projModelVCIso_π C P.W,
    Iso.inv_hom_id_assoc]
  exact P.compat_π

open Scheme WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-B)** The zero-section compatibility of the twist of a presentation by a
variable change (`projModelVCIso_zero`). -/
private theorem chartCompatZero_ofVC {V : S.affineOpens} (P : LocalPresentation G V)
    (C : VariableChange Γ(S, V.1)) :
    (V.2.isoSpec.inv ≫ pullback.lift (V.1.ι ≫ G.zero) (𝟙 _)
        (localPresentationZeroCond G V)) ≫ (P.e ≪≫ (projModelVCIso C P.W).symm).hom =
      projModelZero (C • P.W) := by
  rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, P.compat_zero, Iso.comp_inv_eq]
  exact (projModelVCIso_zero C P.W).symm

open Scheme WeierstrassCurve in
/-- **(E12-B)** Twist a presentation by a variable change: same chart of `E`, the
model read through `projModelVCIso`. The chart curve becomes `C • P.W`. -/
noncomputable def ofVC {V : S.affineOpens} (P : LocalPresentation G V)
    (C : VariableChange Γ(S, V.1)) : LocalPresentation G V where
  W := C • P.W
  elliptic := by letI := P.elliptic; infer_instance
  e := P.e ≪≫ (projModelVCIso C P.W).symm
  compat_π := chartCompatπ_ofVC P C
  compat_zero := chartCompatZero_ofVC P C

@[simp] theorem ofVC_W {V : S.affineOpens} (P : LocalPresentation G V)
    (C : WeierstrassCurve.VariableChange Γ(S, V.1)) : (P.ofVC C).W = C • P.W :=
  rfl

open Scheme in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-B)** The comparison of a twist against the original is the twisting
variable change itself. -/
theorem transVC_ofVC {V : S.affineOpens} (P : LocalPresentation G V)
    (C : WeierstrassCurve.VariableChange Γ(S, V.1)) :
    (P.ofVC C).transVC P = C := by
  refine ((P.ofVC C).transVC_unique P C rfl ?_).symm
  show ((P.ofVC C).e.symm ≪≫ P.e).hom = _
  rw [Iso.trans_hom, Iso.symm_hom,
    show (P.ofVC C).e = P.e ≪≫ (projModelVCIso C P.W).symm from rfl]
  rw [Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    eqToHom_refl, Category.id_comp]

open Scheme WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-B)** Twisting commutes with restriction through the base-changed variable
change: the comparison of the restricted twist against the restriction is the
coefficient-mapped variable change (`projModelVCIso_map` geometrically). -/
theorem transVC_restrict_ofVC {V : S.affineOpens} (P : LocalPresentation G V)
    (C : VariableChange Γ(S, V.1)) {V' : S.affineOpens} (h : V'.1 ≤ V.1) :
    ((P.ofVC C).restrict h).transVC (P.restrict h) =
      C.map (sectionsMapLE (𝟙 S) h) := by
  rw [restrict, restrict, transVC_transport (𝟙 S) (𝟙 G.E)
    (IsPullback.of_horiz_isIso ⟨by simp⟩) (by simp) (P.ofVC C) P (by simpa using h),
    transVC_ofVC]

set_option backward.isDefEq.respectTransparency false in
/-- **(E12-C coherence)** Left-argument collapse: double restriction in the first
argument of a comparison. -/
theorem transVC_restrict_restrict_left {VP : S.affineOpens}
    (P : LocalPresentation G VP) {V V'' : S.affineOpens}
    (R : LocalPresentation G V'') (p : V.1 ≤ VP.1) (h : V''.1 ≤ V.1) :
    ((P.restrict p).restrict h).transVC R = (P.restrict (h.trans p)).transVC R := by
  exact transVC_congr _ _ _ _ (restrict_restrict_W P p h) rfl
    (transportE_restrict_restrict P p h)
    (by rw [eqToHom_refl, Category.comp_id])

set_option backward.isDefEq.respectTransparency false in
/-- **(E12-D4 coherence)** Left-argument collapse of a restricted transport. -/
theorem transVC_transport_restrict_left {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    {VP : S.affineOpens} (P : LocalPresentation G VP)
    {V' V'' : S'.affineOpens} (R' : LocalPresentation G' V'')
    (hV' : V'.1 ≤ f ⁻¹ᵁ VP.1) (h : V''.1 ≤ V'.1) :
    ((P.transport f t hsq hz hV').restrict h).transVC R' =
      (P.transport f t hsq hz (h.trans hV')).transVC R' := by
  exact transVC_congr _ _ _ _ (transport_restrict_W f t hsq hz P hV' h) rfl
    (transportE_restrict_transport f t hsq hz P hV' h)
    (by rw [eqToHom_refl, Category.comp_id])

set_option backward.isDefEq.respectTransparency false in
/-- **(E12-D4 coherence, unit form)** -/
theorem transUnit_transport_restrict_left {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    {VP : S.affineOpens} (P : LocalPresentation G VP)
    {V' V'' : S'.affineOpens} (R' : LocalPresentation G' V'')
    (hV' : V'.1 ≤ f ⁻¹ᵁ VP.1) (h : V''.1 ≤ V'.1) :
    ((P.transport f t hsq hz hV').restrict h).transUnit R' =
      (P.transport f t hsq hz (h.trans hV')).transUnit R' := by
  rw [transUnit, transUnit, transVC_transport_restrict_left]

set_option backward.isDefEq.respectTransparency false in
/-- **(E12-D4 coherence)** Right-argument collapse: double restriction in the second
argument of a comparison. -/
theorem transVC_restrict_restrict_right {VQ : S.affineOpens}
    {V V'' : S.affineOpens} (R' : LocalPresentation G V'')
    (Q : LocalPresentation G VQ) (q : V.1 ≤ VQ.1) (h : V''.1 ≤ V.1) :
    R'.transVC ((Q.restrict q).restrict h) = R'.transVC (Q.restrict (h.trans q)) := by
  exact transVC_congr _ _ _ _ rfl (restrict_restrict_W Q q h)
    (by rw [eqToHom_refl, Category.comp_id]) (transportE_restrict_restrict Q q h)

set_option backward.isDefEq.respectTransparency false in
/-- **(E12-D4 coherence, unit form)** -/
theorem transUnit_restrict_restrict_right {VQ : S.affineOpens}
    {V V'' : S.affineOpens} (R' : LocalPresentation G V'')
    (Q : LocalPresentation G VQ) (q : V.1 ≤ VQ.1) (h : V''.1 ≤ V.1) :
    R'.transUnit ((Q.restrict q).restrict h) =
      R'.transUnit (Q.restrict (h.trans q)) := by
  rw [transUnit, transUnit, transVC_restrict_restrict_right]

set_option backward.isDefEq.respectTransparency false in
/-- **(E12-C coherence, unit form)** -/
theorem transUnit_restrict_restrict_left {VP : S.affineOpens}
    (P : LocalPresentation G VP) {V V'' : S.affineOpens}
    (R : LocalPresentation G V'') (p : V.1 ≤ VP.1) (h : V''.1 ≤ V.1) :
    ((P.restrict p).restrict h).transUnit R = (P.restrict (h.trans p)).transUnit R := by
  rw [transUnit, transUnit, transVC_restrict_restrict_left]

open Scheme in
/-- **(E12-D3-E3)** The inclusion of chart pullbacks along a smaller affine (the
`f = 𝟙` comparison map, exposed). -/
noncomputable def restrictTheta {G : EllipticCurveGeom S} {V V' : S.affineOpens}
    (h : V'.1 ≤ V.1) :
    (pullback G.π V'.1.ι : Scheme.{u}) ⟶ pullback G.π V.1.ι :=
  transportTheta (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
    (show V'.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ V.1 from h)

open Scheme in
@[reassoc (attr := simp)]
theorem restrictTheta_fst {G : EllipticCurveGeom S} {V V' : S.affineOpens}
    (h : V'.1 ≤ V.1) :
    restrictTheta (G := G) h ≫ pullback.fst G.π V.1.ι =
      pullback.fst G.π V'.1.ι := by
  show transportTheta (𝟙 S) (𝟙 G.E) _ _ ≫ pullback.fst G.π V.1.ι = _
  unfold transportTheta
  rw [pullback.lift_fst, Category.comp_id]

open Scheme in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-D4)** The transported chart isomorphism intertwines the model base change
with the square comparison (`transportE_baseChange`, exposed). -/
theorem transport_e_baseChange {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    {V : S.affineOpens} (P : LocalPresentation G V)
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    (P.transport f t hsq hz hV').e.hom ≫
        projModelBaseChange (sectionsMapLE f hV') P.W =
      transportTheta f t hsq hV' ≫ P.e.hom :=
  transportE_baseChange f t hsq P hV'

open Scheme in
@[reassoc]
theorem transportTheta_fst {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f)
    {V : S.affineOpens} {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    transportTheta f t hsq hV' ≫ pullback.fst G.π V.1.ι =
      pullback.fst G'.π V'.1.ι ≫ t := by
  unfold transportTheta
  rw [pullback.lift_fst]

open Scheme in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-D3-E3)** The restricted chart isomorphism intertwines the model base change
with the pullback inclusion (`transportE_baseChange` at the identity square). -/
theorem restrict_e_baseChange {G : EllipticCurveGeom S} {V : S.affineOpens}
    (P : LocalPresentation G V) {V' : S.affineOpens} (h : V'.1 ≤ V.1) :
    (P.restrict h).e.hom ≫ projModelBaseChange (sectionsMapLE (𝟙 S) h) P.W =
      restrictTheta h ≫ P.e.hom :=
  transportE_baseChange (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩) P
    (show V'.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ V.1 from h)

end LocalPresentation

end ModularCurves

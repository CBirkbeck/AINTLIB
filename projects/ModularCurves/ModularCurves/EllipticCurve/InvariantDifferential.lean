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

/-- The curve half of `LocalPresentation`. The five fields cannot share one `structure`:
each field type is cheap alone, and the iso field over a *parameter* `W` is cheap too, but a
field whose type mentions a *preceding* field makes the telescope exceed the heartbeat
budget. Splitting on that dependency keeps every piece inside the default. -/
structure LocalPresentationData (G : EllipticCurveGeom S) (V : S.affineOpens) where
  /-- The chart Weierstrass curve. -/
  W : WeierstrassCurve Γ(S, V.1)
  /-- The chart curve is elliptic. -/
  elliptic : W.IsElliptic

/-- The chart half of `LocalPresentation`, over a *parameter* `W`. -/
structure LocalPresentationChart (G : EllipticCurveGeom S) (V : S.affineOpens)
    (W : WeierstrassCurve Γ(S, V.1)) where
  /-- The pointed chart isomorphism. -/
  e : pullback G.π V.1.ι ≅ projModel W
  /-- The chart isomorphism respects the structure morphisms. -/
  compat_π : e.hom ≫ projModelπ W = pullback.snd G.π V.1.ι ≫ V.2.isoSpec.hom
  /-- The chart isomorphism respects the zero sections. -/
  compat_zero : (V.2.isoSpec.inv ≫ pullback.lift (V.1.ι ≫ G.zero) (𝟙 _)
      (localPresentationZeroCond G V)) ≫ e.hom = projModelZero W

/-- **(T-OM-B1)** A pointed Weierstrass presentation of a geometric elliptic curve over
an affine open `V`. -/
structure LocalPresentation (G : EllipticCurveGeom S) (V : S.affineOpens) where
  /-- The curve and its ellipticity. -/
  data : LocalPresentationData G V
  /-- The chart isomorphism and its compatibilities. -/
  chart : LocalPresentationChart G V data.W

/-! Original field names preserved for consumers; types inferred so they do not
re-elaborate what the split avoids. -/

/-- The chart Weierstrass curve. -/
abbrev LocalPresentation.W {G : EllipticCurveGeom S} {V : S.affineOpens}
    (P : LocalPresentation G V) := P.data.W

/-- The chart curve is elliptic. -/
abbrev LocalPresentation.elliptic {G : EllipticCurveGeom S} {V : S.affineOpens}
    (P : LocalPresentation G V) := P.data.elliptic

/-- The pointed chart isomorphism. -/
abbrev LocalPresentation.e {G : EllipticCurveGeom S} {V : S.affineOpens}
    (P : LocalPresentation G V) := P.chart.e

/-- The chart isomorphism respects the structure morphisms. -/
abbrev LocalPresentation.compat_π {G : EllipticCurveGeom S} {V : S.affineOpens}
    (P : LocalPresentation G V) := P.chart.compat_π

/-- The chart isomorphism respects the zero sections. -/
abbrev LocalPresentation.compat_zero {G : EllipticCurveGeom S} {V : S.affineOpens}
    (P : LocalPresentation G V) := P.chart.compat_zero
variable {G : EllipticCurveGeom S}

/-- **(T-OM-B1)** The atlas chart at an index, as a `LocalPresentation`. -/
noncomputable def WeierstrassAtlasData.presentation (A : WeierstrassAtlasData G)
    (i : A.ι) : LocalPresentation G (A.U i) where
  data := { W := A.W i, elliptic := A.elliptic i }
  chart := { e := A.e i, compat_π := A.compat_π i, compat_zero := A.compat_zero i }

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

/-- The zero-section compatibility of `LocalPresentation.transport`, extracted so the
structure instance is a thin assembly. -/
private theorem transport_compat_zero (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    (P : LocalPresentation G V)
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    (V'.2.isoSpec.inv ≫ pullback.lift (V'.1.ι ≫ G'.zero) (𝟙 _)
        (localPresentationZeroCond G' V')) ≫ (transportE f t hsq P hV').hom =
      projModelZero (P.W.map (sectionsMapLE f hV')) := by
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


/-- **(T-OM-B3)** Transport of a presentation along a cartesian pointed square over
`f : S' ⟶ S`, to an affine open inside the preimage of the chart: the chart curve is
the coefficient base change, the chart isomorphism the induced comparison of pullbacks
(`isPullback_projModelBaseChange` + pasting). Restriction is the case `f = 𝟙 S`. -/
noncomputable def transport (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    (P : LocalPresentation G V)
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    LocalPresentation G' V' where
  data :=
    { W := P.W.map (sectionsMapLE f hV')
      elliptic := by
        letI := P.elliptic
        exact ⟨by rw [WeierstrassCurve.map_Δ]; exact P.W.isUnit_Δ.map _⟩ }
  chart :=
    { e := transportE f t hsq P hV'
      compat_π := transportE_π f t hsq P hV'
      compat_zero := transport_compat_zero f t hsq hz P hV' }
end Transport

@[simp] theorem transport_W {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    (P : LocalPresentation G V)
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    (P.transport f t hsq hz hV').W = P.W.map (sectionsMapLE f hV') :=
  rfl

/-- **(T-OM-B3)** Restriction of a presentation to a smaller affine open: transport
along the identity square. -/
noncomputable def restrict (P : LocalPresentation G V) {V' : S.affineOpens}
    (h : V'.1 ≤ V.1) : LocalPresentation G V' :=
  P.transport (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩) (by simp)
    (by simpa using h)

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

set_option maxHeartbeats 6400000 in
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
  letI : Algebra Γ(S, V.1) Γ(S', V'.1) := (sectionsMapLE f hV').toAlgebra
  have hsmul : (P.transVC Q).map (sectionsMapLE f hV') •
      (Q.transport f t hsq hz hV').W = (P.transport f t hsq hz hV').W := by
    show (P.transVC Q).map (sectionsMapLE f hV') • Q.W.map (sectionsMapLE f hV') =
      P.W.map (sectionsMapLE f hV')
    rw [map_variableChange, P.transVC_smul Q]
  refine ((P.transport f t hsq hz hV').transVC_unique (Q.transport f t hsq hz hV')
    ((P.transVC Q).map (sectionsMapLE f hV')) hsmul ?_).symm
  -- both sides of the defining equation are maps into the base-change pullback of `Q`
  refine (transport_isPullback_model f hV' Q).hom_ext ?_ ?_
  · -- the `projModelBaseChange` leg
    show ((P.transport f t hsq hz hV').pointedIso (Q.transport f t hsq hz hV')).hom ≫
        projModelBaseChange (sectionsMapLE f hV') Q.W = _
    rw [show ((P.transport f t hsq hz hV').pointedIso (Q.transport f t hsq hz hV')).hom =
      (transportE f t hsq P hV').inv ≫ (transportE f t hsq Q hV').hom from rfl]
    simp only [Category.assoc]
    rw [transportE_baseChange f t hsq Q hV']
    rw [show transportTheta f t hsq hV' ≫ Q.e.hom =
      (transportTheta f t hsq hV' ≫ P.e.hom) ≫ (P.pointedIso Q).hom by
        simp [pointedIso, Iso.trans_hom, Iso.symm_hom]]
    rw [← transportE_baseChange f t hsq P hV', Category.assoc, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
    -- LHS is now `projModelBaseChange σ P.W ≫ (P.pointedIso Q).hom`
    rw [P.transVC_spec Q]
    -- RHS: unfold via `projModelVCIso_map`
    have hmap := projModelVCIso_map (R' := Γ(S', V'.1)) (P.transVC Q) Q.W
    rw [show algebraMap Γ(S, V.1) Γ(S', V'.1) = sectionsMapLE f hV' from rfl] at hmap
    rw [← Category.assoc,
      projModelBaseChange_congr (sectionsMapLE f hV')
        (show P.transVC Q • Q.W = P.W from P.transVC_smul Q),
      Category.assoc, hmap, ← Category.assoc, eqToHom_trans]
    rfl
  · -- the `projModelπ` leg
    show ((P.transport f t hsq hz hV').pointedIso (Q.transport f t hsq hz hV')).hom ≫
        projModelπ (Q.transport f t hsq hz hV').W =
      (eqToHom _ ≫ (projModelVCIso ((P.transVC Q).map (sectionsMapLE f hV'))
        (Q.transport f t hsq hz hV').W).hom) ≫
        projModelπ (Q.transport f t hsq hz hV').W
    rw [(P.transport f t hsq hz hV').pointedIso_π (Q.transport f t hsq hz hV')]
    rw [Category.assoc, projModelVCIso_π, projModelπ_congr]
    exact hsmul.symm

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

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in
/-- Double restriction agrees with the composite restriction on chart isomorphisms
(uniqueness of pullback comparisons, through `projModelBaseChangeOf`). -/
private lemma transportE_restrict_restrict {VP : S.affineOpens}
    (P : LocalPresentation G VP)
    {V V'' : S.affineOpens} (p : V.1 ≤ VP.1) (h : V''.1 ≤ V.1) :
    ((P.restrict p).restrict h).e.hom =
      (P.restrict (h.trans p)).e.hom ≫
        eqToHom (show projModel (P.restrict (h.trans p)).W =
            projModel ((P.restrict p).restrict h).W by
          show projModel (P.W.map _) = projModel ((P.W.map _).map _)
          rw [WeierstrassCurve.map_map]
          congr 2
          rw [sectionsMapLE_id, sectionsMapLE_id, sectionsMapLE_id, Scheme.resLE_comp]) := by
  have hWW : (P.restrict (h.trans p)).W = ((P.restrict p).restrict h).W := by
    show P.W.map _ = (P.W.map _).map _
    rw [WeierstrassCurve.map_map]
    congr 1
    rw [sectionsMapLE_id, sectionsMapLE_id, sectionsMapLE_id, Scheme.resLE_comp]
  have hWcomp : P.W.map (sectionsMapLE (𝟙 S)
      (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using h.trans p)) =
    ((P.restrict p).restrict h).W := by
    show _ = (P.W.map _).map _
    rw [WeierstrassCurve.map_map]
    congr 1
    rw [sectionsMapLE_id, sectionsMapLE_id, sectionsMapLE_id, Scheme.resLE_comp]
  refine (isPullback_projModelBaseChangeOf
    (sectionsMapLE (𝟙 S) (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using h.trans p))
    P.W ((P.restrict p).restrict h).W hWcomp).hom_ext ?_ ?_
  · -- the base-change leg: both reduce to `θ_h ≫ θ_p ≫ P.e.hom`
    have hfeq : sectionsMapLE (𝟙 S)
        (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using h.trans p) =
      (sectionsMapLE (𝟙 S) (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ V.1 by simpa using h)).comp
        (sectionsMapLE (𝟙 S) (show V.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using p)) := by
      rw [sectionsMapLE_id, sectionsMapLE_id, sectionsMapLE_id, Scheme.resLE_comp]
    have hLHS : ((P.restrict p).restrict h).e.hom ≫
        projModelBaseChangeOf (sectionsMapLE (𝟙 S)
          (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using h.trans p))
          P.W ((P.restrict p).restrict h).W hWcomp =
        (transportTheta (G' := G) (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
            (V := V) (V' := V'') (by simpa using h) ≫
          transportTheta (G' := G) (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
            (V := VP) (V' := V) (by simpa using p)) ≫ P.e.hom := by
      rw [projModelBaseChangeOf_congr_f hfeq P.W ((P.restrict p).restrict h).W hWcomp
        (by rw [← hfeq]; exact hWcomp)]
      rw [projModelBaseChangeOf_comp
        (sectionsMapLE (𝟙 S) (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ V.1 by simpa using h))
        (sectionsMapLE (𝟙 S) (show V.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using p))
        P.W (P.restrict p).W rfl ((P.restrict p).restrict h).W rfl]
      rw [show projModelBaseChangeOf
          (sectionsMapLE (𝟙 S) (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ V.1 by simpa using h))
          (P.restrict p).W ((P.restrict p).restrict h).W rfl =
        projModelBaseChange
          (sectionsMapLE (𝟙 S) (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ V.1 by simpa using h))
          (P.restrict p).W from by
          rw [projModelBaseChangeOf]; simp]
      rw [show projModelBaseChangeOf
          (sectionsMapLE (𝟙 S) (show V.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using p))
          P.W (P.restrict p).W rfl =
        projModelBaseChange
          (sectionsMapLE (𝟙 S) (show V.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using p))
          P.W from by
          rw [projModelBaseChangeOf]; simp]
      rw [show ((P.restrict p).restrict h).e = transportE (𝟙 S) (𝟙 G.E)
          (IsPullback.of_horiz_isIso ⟨by simp⟩) (P.restrict p)
          (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ V.1 by simpa using h) from rfl]
      rw [← Category.assoc,
        transportE_baseChange (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
          (P.restrict p) (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ V.1 by simpa using h)]
      rw [show (P.restrict p).e = transportE (𝟙 S) (𝟙 G.E)
          (IsPullback.of_horiz_isIso ⟨by simp⟩) P
          (show V.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using p) from rfl]
      rw [Category.assoc, Category.assoc,
        transportE_baseChange (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
          P (show V.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using p)]
    have hRHS : ((P.restrict (h.trans p)).e.hom ≫
        eqToHom (by exact congrArg projModel hWW)) ≫
        projModelBaseChangeOf (sectionsMapLE (𝟙 S)
          (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using h.trans p))
          P.W ((P.restrict p).restrict h).W hWcomp =
        (transportTheta (G' := G) (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
            (V := V) (V' := V'') (by simpa using h) ≫
          transportTheta (G' := G) (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
            (V := VP) (V' := V) (by simpa using p)) ≫ P.e.hom := by
      rw [Category.assoc]
      rw [show eqToHom (by exact congrArg projModel hWW) ≫
          projModelBaseChangeOf (sectionsMapLE (𝟙 S)
            (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using h.trans p))
            P.W ((P.restrict p).restrict h).W hWcomp =
        projModelBaseChangeOf (sectionsMapLE (𝟙 S)
          (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using h.trans p))
          P.W (P.restrict (h.trans p)).W (hWcomp.trans hWW.symm) from by
          rw [projModelBaseChangeOf, projModelBaseChangeOf, eqToHom_trans_assoc]]
      rw [show projModelBaseChangeOf (sectionsMapLE (𝟙 S)
          (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using h.trans p))
          P.W (P.restrict (h.trans p)).W (hWcomp.trans hWW.symm) =
        projModelBaseChange (sectionsMapLE (𝟙 S)
          (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using h.trans p)) P.W from by
          rw [projModelBaseChangeOf]; simp]
      rw [show (P.restrict (h.trans p)).e = transportE (𝟙 S) (𝟙 G.E)
          (IsPullback.of_horiz_isIso ⟨by simp⟩) P
          (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using h.trans p) from rfl]
      rw [transportE_baseChange (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
          P (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using h.trans p),
        ← transportTheta_comp p h]
    exact hLHS.trans hRHS.symm
  · -- the `π` leg: both sides are the chart projection of `V''`
    rw [Category.assoc,
      show eqToHom (by rw [hWW] :
          projModel (P.restrict (h.trans p)).W =
            projModel ((P.restrict p).restrict h).W) ≫
        projModelπ ((P.restrict p).restrict h).W =
      projModelπ (P.restrict (h.trans p)).W from projModelπ_congr hWW]
    rw [show ((P.restrict p).restrict h).e = transportE (𝟙 S) (𝟙 G.E)
        (IsPullback.of_horiz_isIso ⟨by simp⟩) (P.restrict p)
        (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ V.1 by simpa using h) from rfl,
      show (P.restrict (h.trans p)).e = transportE (𝟙 S) (𝟙 G.E)
        (IsPullback.of_horiz_isIso ⟨by simp⟩) P
        (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using h.trans p) from rfl]
    exact (transportE_π (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
      (P.restrict p) (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ V.1 by simpa using h)).trans
      (transportE_π (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
        P (show V''.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using h.trans p)).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6400000 in
/-- **(T-OM-B5 coherence)** Double restriction agrees with the composite restriction on
comparison variable changes (uniqueness through the chart-isomorphism coherence).
(Un-`private`d for the engine mouth core's Stage-3 chart-Čech cocycle laws,
`Moduli/EngineDescent.lean`.) -/
theorem transVC_restrict_restrict {VP VQ : S.affineOpens}
    (P : LocalPresentation G VP) (Q : LocalPresentation G VQ)
    {V V'' : S.affineOpens} (p : V.1 ≤ VP.1) (q : V.1 ≤ VQ.1) (h : V''.1 ≤ V.1) :
    ((P.restrict p).restrict h).transVC ((Q.restrict q).restrict h) =
      (P.restrict (h.trans p)).transVC (Q.restrict (h.trans q)) := by
  have hWWP : (P.restrict (h.trans p)).W = ((P.restrict p).restrict h).W := by
    show P.W.map _ = (P.W.map _).map _
    rw [WeierstrassCurve.map_map]
    congr 1
    rw [sectionsMapLE_id, sectionsMapLE_id, sectionsMapLE_id, Scheme.resLE_comp]
  have hWWQ : (Q.restrict (h.trans q)).W = ((Q.restrict q).restrict h).W := by
    show Q.W.map _ = (Q.W.map _).map _
    rw [WeierstrassCurve.map_map]
    congr 1
    rw [sectionsMapLE_id, sectionsMapLE_id, sectionsMapLE_id, Scheme.resLE_comp]
  have hP := transportE_restrict_restrict P p h
  have hQ := transportE_restrict_restrict Q q h
  -- invert the `P`-coherence
  have hPinv : (((P.restrict p).restrict h).e).inv =
      eqToHom (congrArg projModel hWWP).symm ≫ (P.restrict (h.trans p)).e.inv := by
    rw [← cancel_mono (((P.restrict p).restrict h).e.hom), Iso.inv_hom_id, hP,
      Category.assoc, ← Category.assoc ((P.restrict (h.trans p)).e.inv),
      Iso.inv_hom_id, Category.id_comp, eqToHom_trans, eqToHom_refl]
  refine ((((P.restrict p).restrict h).transVC_unique ((Q.restrict q).restrict h)
    ((P.restrict (h.trans p)).transVC (Q.restrict (h.trans q))) ?_ ?_)).symm
  · rw [← hWWQ, ← hWWP]
    exact (P.restrict (h.trans p)).transVC_smul (Q.restrict (h.trans q))
  · show (((P.restrict p).restrict h).e.symm ≪≫ ((Q.restrict q).restrict h).e).hom = _
    rw [Iso.trans_hom, Iso.symm_hom, hPinv, hQ]
    simp only [Category.assoc]
    rw [← Category.assoc ((P.restrict (h.trans p)).e.inv)]
    rw [show (P.restrict (h.trans p)).e.inv ≫ (Q.restrict (h.trans q)).e.hom =
      ((P.restrict (h.trans p)).pointedIso (Q.restrict (h.trans q))).hom from rfl]
    rw [(P.restrict (h.trans p)).transVC_spec (Q.restrict (h.trans q))]
    rw [projModelVCIso_congr hWWQ ((P.restrict (h.trans p)).transVC (Q.restrict (h.trans q)))]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- **(T-OM-B5 coherence, unit form)** Restricting a transition unit twice agrees with
the composite restriction. -/
theorem transUnit_restrict_restrict {VP VQ : S.affineOpens}
    (P : LocalPresentation G VP) (Q : LocalPresentation G VQ)
    {V V'' : S.affineOpens} (p : V.1 ≤ VP.1) (q : V.1 ≤ VQ.1) (h : V''.1 ≤ V.1) :
    ((P.restrict p).restrict h).transUnit ((Q.restrict q).restrict h) =
      (P.restrict (h.trans p)).transUnit (Q.restrict (h.trans q)) := by
  rw [transUnit, transUnit, transVC_restrict_restrict P Q p q h]

set_option maxHeartbeats 6400000 in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-OM-B7 coherence)** The comparison variable change only depends on the
presentations through their charts up to the canonical transport: presentations with
equal curves and `eqToHom`-related chart isomorphisms have equal comparisons. -/
theorem transVC_congr {V'' : S.affineOpens} (P₁ P₂ Q₁ Q₂ : LocalPresentation G V'')
    (w₁ : Q₁.W = P₁.W) (w₂ : Q₂.W = P₂.W)
    (he₁ : P₁.e.hom = Q₁.e.hom ≫ eqToHom (by exact congrArg projModel w₁))
    (he₂ : P₂.e.hom = Q₂.e.hom ≫ eqToHom (by exact congrArg projModel w₂)) :
    P₁.transVC P₂ = Q₁.transVC Q₂ := by
  have hPinv : P₁.e.inv = eqToHom (show projModel P₁.W = projModel Q₁.W by rw [w₁]) ≫
      Q₁.e.inv := by
    rw [← cancel_mono P₁.e.hom, Iso.inv_hom_id, he₁, Category.assoc,
      ← Category.assoc Q₁.e.inv, Iso.inv_hom_id, Category.id_comp, eqToHom_trans,
      eqToHom_refl]
  refine Q₁.transVC_unique Q₂ (P₁.transVC P₂) ?_ ?_
  · rw [w₂, w₁]
    exact P₁.transVC_smul P₂
  · show (Q₁.e.symm ≪≫ Q₂.e).hom = _
    have hQ₁inv : Q₁.e.inv =
        eqToHom (show projModel Q₁.W = projModel P₁.W by rw [w₁]) ≫ P₁.e.inv := by
      rw [hPinv, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    have hQ₂hom : Q₂.e.hom = P₂.e.hom ≫
        eqToHom (show projModel P₂.W = projModel Q₂.W from congrArg projModel w₂.symm) := by
      rw [he₂, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rw [Iso.trans_hom, Iso.symm_hom, hQ₁inv, hQ₂hom]
    simp only [Category.assoc]
    rw [← Category.assoc P₁.e.inv]
    rw [show P₁.e.inv ≫ P₂.e.hom = (P₁.pointedIso P₂).hom from rfl]
    rw [P₁.transVC_spec P₂]
    rw [projModelVCIso_congr w₂ (P₁.transVC P₂)]
    simp only [Category.assoc, eqToHom_trans_assoc]

/-- **(T-OM-B7 coherence, unit form)** -/
theorem transUnit_congr {V'' : S.affineOpens} (P₁ P₂ Q₁ Q₂ : LocalPresentation G V'')
    (w₁ : Q₁.W = P₁.W) (w₂ : Q₂.W = P₂.W)
    (he₁ : P₁.e.hom = Q₁.e.hom ≫ eqToHom (by exact congrArg projModel w₁))
    (he₂ : P₂.e.hom = Q₂.e.hom ≫ eqToHom (by exact congrArg projModel w₂)) :
    P₁.transUnit P₂ = Q₁.transUnit Q₂ := by
  rw [transUnit, transUnit, transVC_congr P₁ P₂ Q₁ Q₂ w₁ w₂ he₁ he₂]

/-- Sections comparisons compose with restrictions. -/
theorem sectionsMapLE_comp_resLE {S' : Scheme.{u}} (f : S' ⟶ S) {V : S.Opens}
    {V' V'' : S'.Opens} (hV' : V' ≤ f ⁻¹ᵁ V) (h : V'' ≤ V') :
    (Scheme.resLE h).comp (sectionsMapLE f hV') = sectionsMapLE f (h.trans hV') :=
  RingHom.ext fun r => Scheme.resLE_appLE f hV' h r

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
set_option maxHeartbeats 6400000 in
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
  have hWW : (P.transport f t hsq hz (h.trans hV')).W =
      ((P.transport f t hsq hz hV').restrict h).W := by
    show P.W.map _ = (P.W.map _).map _
    rw [WeierstrassCurve.map_map]
    congr 1
    rw [sectionsMapLE_id, sectionsMapLE_comp_resLE f hV' h]
  have hWcomp : P.W.map (sectionsMapLE f (h.trans hV')) =
      ((P.transport f t hsq hz hV').restrict h).W := hWW
  have hfeq : sectionsMapLE f (h.trans hV') =
      (sectionsMapLE (𝟙 S') (show V''.1 ≤ (𝟙 S' : S' ⟶ S') ⁻¹ᵁ V'.1 by simpa using h)).comp
        (sectionsMapLE f hV') := by
    rw [sectionsMapLE_id, sectionsMapLE_comp_resLE f hV' h]
  refine (isPullback_projModelBaseChangeOf (sectionsMapLE f (h.trans hV'))
    P.W ((P.transport f t hsq hz hV').restrict h).W hWcomp).hom_ext ?_ ?_
  · have hLHS : ((P.transport f t hsq hz hV').restrict h).e.hom ≫
        projModelBaseChangeOf (sectionsMapLE f (h.trans hV'))
          P.W ((P.transport f t hsq hz hV').restrict h).W hWcomp =
        (transportTheta (G' := G') (𝟙 S') (𝟙 G'.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
            (V := V') (V' := V'') (by simpa using h) ≫
          transportTheta f t hsq hV') ≫ P.e.hom := by
      rw [projModelBaseChangeOf_congr_f hfeq P.W
        ((P.transport f t hsq hz hV').restrict h).W hWcomp (by rw [← hfeq]; exact hWcomp)]
      rw [projModelBaseChangeOf_comp
        (sectionsMapLE (𝟙 S') (show V''.1 ≤ (𝟙 S' : S' ⟶ S') ⁻¹ᵁ V'.1 by simpa using h))
        (sectionsMapLE f hV')
        P.W (P.transport f t hsq hz hV').W rfl
        ((P.transport f t hsq hz hV').restrict h).W rfl]
      rw [show projModelBaseChangeOf
          (sectionsMapLE (𝟙 S') (show V''.1 ≤ (𝟙 S' : S' ⟶ S') ⁻¹ᵁ V'.1 by simpa using h))
          (P.transport f t hsq hz hV').W ((P.transport f t hsq hz hV').restrict h).W rfl =
        projModelBaseChange
          (sectionsMapLE (𝟙 S') (show V''.1 ≤ (𝟙 S' : S' ⟶ S') ⁻¹ᵁ V'.1 by simpa using h))
          (P.transport f t hsq hz hV').W from by
          rw [projModelBaseChangeOf]; simp]
      rw [show projModelBaseChangeOf (sectionsMapLE f hV')
          P.W (P.transport f t hsq hz hV').W rfl =
        projModelBaseChange (sectionsMapLE f hV') P.W from by
          rw [projModelBaseChangeOf]; simp]
      rw [show ((P.transport f t hsq hz hV').restrict h).e = transportE (𝟙 S') (𝟙 G'.E)
          (IsPullback.of_horiz_isIso ⟨by simp⟩) (P.transport f t hsq hz hV')
          (show V''.1 ≤ (𝟙 S' : S' ⟶ S') ⁻¹ᵁ V'.1 by simpa using h) from rfl]
      rw [← Category.assoc,
        transportE_baseChange (𝟙 S') (𝟙 G'.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
          (P.transport f t hsq hz hV')
          (show V''.1 ≤ (𝟙 S' : S' ⟶ S') ⁻¹ᵁ V'.1 by simpa using h)]
      rw [show (P.transport f t hsq hz hV').e = transportE f t hsq P hV' from rfl]
      rw [Category.assoc, Category.assoc, transportE_baseChange f t hsq P hV']
    have hRHS : ((P.transport f t hsq hz (h.trans hV')).e.hom ≫
        eqToHom (by exact congrArg projModel hWW)) ≫
        projModelBaseChangeOf (sectionsMapLE f (h.trans hV'))
          P.W ((P.transport f t hsq hz hV').restrict h).W hWcomp =
        (transportTheta (G' := G') (𝟙 S') (𝟙 G'.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
            (V := V') (V' := V'') (by simpa using h) ≫
          transportTheta f t hsq hV') ≫ P.e.hom := by
      rw [Category.assoc]
      rw [show eqToHom (by exact congrArg projModel hWW) ≫
          projModelBaseChangeOf (sectionsMapLE f (h.trans hV'))
            P.W ((P.transport f t hsq hz hV').restrict h).W hWcomp =
        projModelBaseChangeOf (sectionsMapLE f (h.trans hV'))
          P.W (P.transport f t hsq hz (h.trans hV')).W (hWcomp.trans hWW.symm) from by
          rw [projModelBaseChangeOf, projModelBaseChangeOf, eqToHom_trans_assoc]]
      rw [show projModelBaseChangeOf (sectionsMapLE f (h.trans hV'))
          P.W (P.transport f t hsq hz (h.trans hV')).W (hWcomp.trans hWW.symm) =
        projModelBaseChange (sectionsMapLE f (h.trans hV')) P.W from by
          rw [projModelBaseChangeOf]; simp]
      rw [show (P.transport f t hsq hz (h.trans hV')).e =
        transportE f t hsq P (h.trans hV') from rfl]
      rw [transportE_baseChange f t hsq P (h.trans hV'), ← transportTheta_comp' f t hsq hV' h]
    exact hLHS.trans hRHS.symm
  · rw [Category.assoc,
      show eqToHom (by rw [hWW] :
          projModel (P.transport f t hsq hz (h.trans hV')).W =
            projModel ((P.transport f t hsq hz hV').restrict h).W) ≫
        projModelπ ((P.transport f t hsq hz hV').restrict h).W =
      projModelπ (P.transport f t hsq hz (h.trans hV')).W from projModelπ_congr hWW]
    rw [show ((P.transport f t hsq hz hV').restrict h).e = transportE (𝟙 S') (𝟙 G'.E)
        (IsPullback.of_horiz_isIso ⟨by simp⟩) (P.transport f t hsq hz hV')
        (show V''.1 ≤ (𝟙 S' : S' ⟶ S') ⁻¹ᵁ V'.1 by simpa using h) from rfl,
      show (P.transport f t hsq hz (h.trans hV')).e =
        transportE f t hsq P (h.trans hV') from rfl]
    exact (transportE_π (𝟙 S') (𝟙 G'.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
      (P.transport f t hsq hz hV')
      (show V''.1 ≤ (𝟙 S' : S' ⟶ S') ⁻¹ᵁ V'.1 by simpa using h)).trans
      (transportE_π f t hsq P (h.trans hV')).symm

/-- Sections comparisons absorb restrictions on the source side. -/
theorem resLE_comp_sectionsMapLE {S' : Scheme.{u}} (f : S' ⟶ S) {U U' : S.Opens}
    (hU : U ≤ U') {W : S'.Opens} (h : W ≤ f ⁻¹ᵁ U) :
    (sectionsMapLE f h).comp (Scheme.resLE hU) =
      sectionsMapLE f (h.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hU)).le) :=
  RingHom.ext fun r => Scheme.appLE_resLE f hU h r

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
set_option maxHeartbeats 6400000 in
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
  have hWW : (P.transport f t hsq hz
      (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le)).W =
      ((P.restrict w).transport f t hsq hz hV'').W := by
    show P.W.map _ = (P.W.map _).map _
    rw [WeierstrassCurve.map_map]
    congr 1
    rw [sectionsMapLE_id, resLE_comp_sectionsMapLE f w hV'']
  have hWcomp : P.W.map (sectionsMapLE f
      (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le)) =
      ((P.restrict w).transport f t hsq hz hV'').W := hWW
  have hfeq : sectionsMapLE f (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le) =
      (sectionsMapLE f hV'').comp
        (sectionsMapLE (𝟙 S) (show W₀.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using w)) := by
    rw [sectionsMapLE_id, resLE_comp_sectionsMapLE f w hV'']
  refine (isPullback_projModelBaseChangeOf
    (sectionsMapLE f (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le))
    P.W ((P.restrict w).transport f t hsq hz hV'').W hWcomp).hom_ext ?_ ?_
  · have hLHS : ((P.restrict w).transport f t hsq hz hV'').e.hom ≫
        projModelBaseChangeOf
          (sectionsMapLE f (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le))
          P.W ((P.restrict w).transport f t hsq hz hV'').W hWcomp =
        (transportTheta f t hsq hV'' ≫
          transportTheta (G' := G) (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
            (V := VP) (V' := W₀) (by simpa using w)) ≫ P.e.hom := by
      rw [projModelBaseChangeOf_congr_f hfeq P.W
        ((P.restrict w).transport f t hsq hz hV'').W hWcomp (by rw [← hfeq]; exact hWcomp)]
      rw [projModelBaseChangeOf_comp
        (sectionsMapLE f hV'')
        (sectionsMapLE (𝟙 S) (show W₀.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using w))
        P.W (P.restrict w).W rfl
        ((P.restrict w).transport f t hsq hz hV'').W rfl]
      rw [show projModelBaseChangeOf (sectionsMapLE f hV'')
          (P.restrict w).W ((P.restrict w).transport f t hsq hz hV'').W rfl =
        projModelBaseChange (sectionsMapLE f hV'') (P.restrict w).W from by
          rw [projModelBaseChangeOf]; simp]
      rw [show projModelBaseChangeOf
          (sectionsMapLE (𝟙 S) (show W₀.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using w))
          P.W (P.restrict w).W rfl =
        projModelBaseChange
          (sectionsMapLE (𝟙 S) (show W₀.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using w))
          P.W from by
          rw [projModelBaseChangeOf]; simp]
      rw [show ((P.restrict w).transport f t hsq hz hV'').e =
        transportE f t hsq (P.restrict w) hV'' from rfl]
      rw [← Category.assoc, transportE_baseChange f t hsq (P.restrict w) hV'']
      rw [show (P.restrict w).e = transportE (𝟙 S) (𝟙 G.E)
          (IsPullback.of_horiz_isIso ⟨by simp⟩) P
          (show W₀.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using w) from rfl]
      rw [Category.assoc, Category.assoc,
        transportE_baseChange (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
          P (show W₀.1 ≤ (𝟙 S : S ⟶ S) ⁻¹ᵁ VP.1 by simpa using w)]
    have hRHS : ((P.transport f t hsq hz
        (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le)).e.hom ≫
        eqToHom (by exact congrArg projModel hWW)) ≫
        projModelBaseChangeOf
          (sectionsMapLE f (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le))
          P.W ((P.restrict w).transport f t hsq hz hV'').W hWcomp =
        (transportTheta f t hsq hV'' ≫
          transportTheta (G' := G) (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
            (V := VP) (V' := W₀) (by simpa using w)) ≫ P.e.hom := by
      rw [Category.assoc]
      rw [show eqToHom (by exact congrArg projModel hWW) ≫
          projModelBaseChangeOf
            (sectionsMapLE f (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le))
            P.W ((P.restrict w).transport f t hsq hz hV'').W hWcomp =
        projModelBaseChangeOf
          (sectionsMapLE f (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le))
          P.W (P.transport f t hsq hz
            (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le)).W
          (hWcomp.trans hWW.symm) from by
          rw [projModelBaseChangeOf, projModelBaseChangeOf, eqToHom_trans_assoc]]
      rw [show projModelBaseChangeOf
          (sectionsMapLE f (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le))
          P.W (P.transport f t hsq hz
            (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le)).W
          (hWcomp.trans hWW.symm) =
        projModelBaseChange
          (sectionsMapLE f (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le))
          P.W from by
          rw [projModelBaseChangeOf]; simp]
      rw [show (P.transport f t hsq hz
          (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le)).e =
        transportE f t hsq P (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le) from rfl]
      rw [transportE_baseChange f t hsq P
          (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le),
        ← transportTheta_comp'' f t hsq w hV'']
    exact hLHS.trans hRHS.symm
  · rw [Category.assoc,
      show eqToHom (by rw [hWW] :
          projModel (P.transport f t hsq hz
            (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le)).W =
            projModel ((P.restrict w).transport f t hsq hz hV'').W) ≫
        projModelπ ((P.restrict w).transport f t hsq hz hV'').W =
      projModelπ (P.transport f t hsq hz
        (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le)).W from projModelπ_congr hWW]
    rw [show ((P.restrict w).transport f t hsq hz hV'').e =
        transportE f t hsq (P.restrict w) hV'' from rfl,
      show (P.transport f t hsq hz
          (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le)).e =
        transportE f t hsq P (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le) from rfl]
    exact (transportE_π f t hsq (P.restrict w) hV'').trans
      (transportE_π f t hsq P (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE w)).le)).symm

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
  · show A.W.map _ = (A.W.map _).map _
    rw [WeierstrassCurve.map_map]
    congr 1
    rw [sectionsMapLE_id, sectionsMapLE_comp_resLE f hA h]
  · show B.W.map _ = (B.W.map _).map _
    rw [WeierstrassCurve.map_map]
    congr 1
    rw [sectionsMapLE_id, sectionsMapLE_comp_resLE f hB h]
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
  · show A.W.map _ = (A.W.map _).map _
    rw [WeierstrassCurve.map_map]
    congr 1
    rw [sectionsMapLE_id, resLE_comp_sectionsMapLE f wA hV'']
  · show B.W.map _ = (B.W.map _).map _
    rw [WeierstrassCurve.map_map]
    congr 1
    rw [sectionsMapLE_id, resLE_comp_sectionsMapLE f wB hV'']
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
set_option maxHeartbeats 6400000 in
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
  have hWW : (P.transport (f ≫ g) (t ≫ s) (hsq_f.paste_horiz hsq_g) hzc
      (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le)).W =
      ((P.transport g s hsq_g hz_g hV').transport f t hsq_f hz_f hV'').W := by
    show P.W.map _ = (P.W.map _).map _
    rw [WeierstrassCurve.map_map]
    congr 1
    rw [sectionsMapLE_comp f g hV' hV'']
  have hWcomp : P.W.map (sectionsMapLE (f ≫ g)
      (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le)) =
      ((P.transport g s hsq_g hz_g hV').transport f t hsq_f hz_f hV'').W := hWW
  have hfeq : sectionsMapLE (f ≫ g)
      (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le) =
      (sectionsMapLE f hV'').comp (sectionsMapLE g hV') := by
    rw [sectionsMapLE_comp f g hV' hV'']
  refine (isPullback_projModelBaseChangeOf (sectionsMapLE (f ≫ g)
      (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le))
    P.W ((P.transport g s hsq_g hz_g hV').transport f t hsq_f hz_f hV'').W
    hWcomp).hom_ext ?_ ?_
  · have hLHS : ((P.transport g s hsq_g hz_g hV').transport f t hsq_f hz_f hV'').e.hom ≫
        projModelBaseChangeOf (sectionsMapLE (f ≫ g)
          (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le))
          P.W ((P.transport g s hsq_g hz_g hV').transport f t hsq_f hz_f hV'').W hWcomp =
        (transportTheta f t hsq_f hV'' ≫ transportTheta g s hsq_g hV') ≫ P.e.hom := by
      rw [projModelBaseChangeOf_congr_f hfeq P.W
        ((P.transport g s hsq_g hz_g hV').transport f t hsq_f hz_f hV'').W hWcomp
        (by rw [← hfeq]; exact hWcomp)]
      rw [projModelBaseChangeOf_comp (sectionsMapLE f hV'') (sectionsMapLE g hV')
        P.W (P.transport g s hsq_g hz_g hV').W rfl
        ((P.transport g s hsq_g hz_g hV').transport f t hsq_f hz_f hV'').W rfl]
      rw [show projModelBaseChangeOf (sectionsMapLE f hV'')
          (P.transport g s hsq_g hz_g hV').W
          ((P.transport g s hsq_g hz_g hV').transport f t hsq_f hz_f hV'').W rfl =
        projModelBaseChange (sectionsMapLE f hV'')
          (P.transport g s hsq_g hz_g hV').W from by
          rw [projModelBaseChangeOf]; simp]
      rw [show projModelBaseChangeOf (sectionsMapLE g hV') P.W
          (P.transport g s hsq_g hz_g hV').W rfl =
        projModelBaseChange (sectionsMapLE g hV') P.W from by
          rw [projModelBaseChangeOf]; simp]
      rw [show ((P.transport g s hsq_g hz_g hV').transport f t hsq_f hz_f hV'').e =
        transportE f t hsq_f (P.transport g s hsq_g hz_g hV') hV'' from rfl]
      rw [← Category.assoc,
        transportE_baseChange f t hsq_f (P.transport g s hsq_g hz_g hV') hV'']
      rw [show (P.transport g s hsq_g hz_g hV').e = transportE g s hsq_g P hV' from rfl]
      rw [Category.assoc, Category.assoc, transportE_baseChange g s hsq_g P hV']
    have hRHS : ((P.transport (f ≫ g) (t ≫ s) (hsq_f.paste_horiz hsq_g)
        hzc
        (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le)).e.hom ≫
        eqToHom (by exact congrArg projModel hWW)) ≫
        projModelBaseChangeOf (sectionsMapLE (f ≫ g)
          (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le))
          P.W ((P.transport g s hsq_g hz_g hV').transport f t hsq_f hz_f hV'').W hWcomp =
        (transportTheta f t hsq_f hV'' ≫ transportTheta g s hsq_g hV') ≫ P.e.hom := by
      rw [Category.assoc]
      rw [show eqToHom (by exact congrArg projModel hWW) ≫
          projModelBaseChangeOf (sectionsMapLE (f ≫ g)
            (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le))
            P.W ((P.transport g s hsq_g hz_g hV').transport f t hsq_f hz_f hV'').W
            hWcomp =
        projModelBaseChangeOf (sectionsMapLE (f ≫ g)
          (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le))
          P.W (P.transport (f ≫ g) (t ≫ s) (hsq_f.paste_horiz hsq_g)
            hzc
            (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le)).W
          (hWcomp.trans hWW.symm) from by
          rw [projModelBaseChangeOf, projModelBaseChangeOf, ← Category.assoc,
            eqToHom_trans]]
      rw [show projModelBaseChangeOf (sectionsMapLE (f ≫ g)
          (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le))
          P.W (P.transport (f ≫ g) (t ≫ s) (hsq_f.paste_horiz hsq_g)
            hzc
            (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le)).W
          (hWcomp.trans hWW.symm) =
        projModelBaseChange (sectionsMapLE (f ≫ g)
          (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le))
          P.W from by
          rw [projModelBaseChangeOf]; simp]
      rw [show (P.transport (f ≫ g) (t ≫ s) (hsq_f.paste_horiz hsq_g)
          hzc
          (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le)).e =
        transportE (f ≫ g) (t ≫ s) (hsq_f.paste_horiz hsq_g) P
          (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le)
        from rfl]
      rw [transportE_baseChange (f ≫ g) (t ≫ s) (hsq_f.paste_horiz hsq_g) P
          (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le),
        ← transportTheta_transportTheta f g t s hsq_f hsq_g hV' hV'']
    exact hLHS.trans hRHS.symm
  · rw [Category.assoc,
      show eqToHom (by rw [hWW] :
          projModel (P.transport (f ≫ g) (t ≫ s) (hsq_f.paste_horiz hsq_g)
            hzc
            (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le)).W =
            projModel ((P.transport g s hsq_g hz_g hV').transport f t hsq_f
              hz_f hV'').W) ≫
        projModelπ ((P.transport g s hsq_g hz_g hV').transport f t hsq_f hz_f hV'').W =
      projModelπ (P.transport (f ≫ g) (t ≫ s) (hsq_f.paste_horiz hsq_g)
        hzc
        (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le)).W
      from projModelπ_congr hWW]
    rw [show ((P.transport g s hsq_g hz_g hV').transport f t hsq_f hz_f hV'').e =
        transportE f t hsq_f (P.transport g s hsq_g hz_g hV') hV'' from rfl,
      show (P.transport (f ≫ g) (t ≫ s) (hsq_f.paste_horiz hsq_g)
          hzc
          (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le)).e =
        transportE (f ≫ g) (t ≫ s) (hsq_f.paste_horiz hsq_g) P
          (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le)
        from rfl]
    exact (transportE_π f t hsq_f (P.transport g s hsq_g hz_g hV') hV'').trans
      (transportE_π (f ≫ g) (t ≫ s) (hsq_f.paste_horiz hsq_g) P
        (hV''.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hV')).le)).symm

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
  · show A.W.map _ = (A.W.map _).map _
    rw [WeierstrassCurve.map_map]
    congr 1
    rw [sectionsMapLE_comp f g hA hA']
  · show B.W.map _ = (B.W.map _).map _
    rw [WeierstrassCurve.map_map]
    congr 1
    rw [sectionsMapLE_comp f g hB hB']
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
  · show Q.W.map _ = (Q.W.map _).map _
    rw [WeierstrassCurve.map_map]
    congr 1
    rw [sectionsMapLE_id, sectionsMapLE_id, sectionsMapLE_id, Scheme.resLE_comp]
  · show P.W.map _ = (P.W.map _).map _
    rw [WeierstrassCurve.map_map]
    congr 1
    rw [sectionsMapLE_id, sectionsMapLE_comp_resLE f hV' h]
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
set_option maxHeartbeats 6400000 in
set_option backward.isDefEq.respectTransparency false in
/-- **(E12-B)** Twist a presentation by a variable change: same chart of `E`, the
model read through `projModelVCIso`. The chart curve becomes `C • P.W`. -/
noncomputable def ofVC {V : S.affineOpens} (P : LocalPresentation G V)
    (C : VariableChange Γ(S, V.1)) : LocalPresentation G V where
  data :=
    { W := C • P.W
      elliptic := by letI := P.elliptic; infer_instance }
  chart :=
    { e := P.e ≪≫ (projModelVCIso C P.W).symm
      compat_π := by
        rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← P.compat_π]
        congr 1
        rw [← projModelVCIso_π C P.W, Iso.inv_hom_id_assoc]
      compat_zero := by
        rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, P.compat_zero,
          Iso.comp_inv_eq]
        exact (projModelVCIso_zero C P.W).symm }

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
set_option maxHeartbeats 6400000 in
/-- **(E12-B)** Twisting commutes with restriction through the base-changed variable
change: the comparison of the restricted twist against the restriction is the
coefficient-mapped variable change (`projModelVCIso_map` geometrically). -/
theorem transVC_restrict_ofVC {V : S.affineOpens} (P : LocalPresentation G V)
    (C : VariableChange Γ(S, V.1)) {V' : S.affineOpens} (h : V'.1 ≤ V.1) :
    ((P.ofVC C).restrict h).transVC (P.restrict h) =
      C.map (sectionsMapLE (𝟙 S) h) := by
  letI := P.elliptic
  letI : Algebra Γ(S, V.1) Γ(S, V'.1) := (sectionsMapLE (𝟙 S) h).toAlgebra
  have hWeq : ((P.ofVC C).restrict h).W =
      (C.map (sectionsMapLE (𝟙 S) h)) • (P.restrict h).W :=
    (map_variableChange ..).symm
  refine (transVC_unique _ _ _ hWeq.symm ?_).symm
  show (((P.ofVC C).restrict h).e.symm ≪≫ (P.restrict h).e).hom = _
  rw [Iso.trans_hom, Iso.symm_hom, Iso.inv_comp_eq]
  show (transportE (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩) P h).hom =
    (transportE (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩) (P.ofVC C) h).hom ≫
      eqToHom (congrArg projModel hWeq) ≫
      (projModelVCIso (C.map (sectionsMapLE (𝟙 S) h))
        (P.W.map (sectionsMapLE (𝟙 S) h))).hom
  unfold transportE
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq]
  simp only [Category.assoc]
  refine pullback.hom_ext ?_ ?_
  · -- the base-change leg: `projModelVCIso_map`
    simp only [Category.assoc]
    have hmap : projModelBaseChange (sectionsMapLE (𝟙 S) h) (C • P.W) ≫
        (projModelVCIso C P.W).hom =
      eqToHom (by rw [map_variableChange]) ≫
        (projModelVCIso (C.map (sectionsMapLE (𝟙 S) h))
          (P.W.map (sectionsMapLE (𝟙 S) h))).hom ≫
        projModelBaseChange (sectionsMapLE (𝟙 S) h) P.W :=
      projModelVCIso_map C P.W
    have hmap' : (projModelVCIso (C.map (sectionsMapLE (𝟙 S) h))
          (P.W.map (sectionsMapLE (𝟙 S) h))).hom ≫
        projModelBaseChange (sectionsMapLE (𝟙 S) h) P.W =
      eqToHom (congrArg projModel (map_variableChange ..)) ≫
        projModelBaseChange (sectionsMapLE (𝟙 S) h) (C • P.W) ≫
        (projModelVCIso C P.W).hom := by
      have h2 := congrArg
        (fun t => eqToHom (congrArg projModel (map_variableChange
          (φ := sectionsMapLE (𝟙 S) h) (C := C) (W := P.W))) ≫ t) hmap
      simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at h2
      exact h2.symm
    rw [(transport_isPullback' (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩)
        P h).isoPullback_hom_fst,
      show (transport_isPullback_model (𝟙 S) h P).isoPullback.hom ≫
          pullback.fst (projModelπ P.W)
            (Spec.map (CommRingCat.ofHom (sectionsMapLE (𝟙 S) h))) =
        projModelBaseChange (sectionsMapLE (𝟙 S) h) P.W from
        (transport_isPullback_model (𝟙 S) h P).isoPullback_hom_fst,
      hmap', eqToHom_trans_assoc, eqToHom_refl]
    simp only [Category.id_comp]
    have hinvfst : (transport_isPullback_model (𝟙 S) h
        (P.ofVC C)).isoPullback.inv ≫
        projModelBaseChange (sectionsMapLE (𝟙 S) h) (C • P.W) =
      pullback.fst (projModelπ (P.ofVC C).W)
        (Spec.map (CommRingCat.ofHom (sectionsMapLE (𝟙 S) h))) :=
      (transport_isPullback_model (𝟙 S) h (P.ofVC C)).isoPullback_inv_fst
    rw [reassoc_of% hinvfst,
      reassoc_of% (transport_isPullback' (𝟙 S) (𝟙 G.E)
        (IsPullback.of_horiz_isIso ⟨by simp⟩) (P.ofVC C) h).isoPullback_hom_fst]
    show transportTheta (𝟙 S) (𝟙 G.E) _ h ≫ P.e.hom =
      transportTheta (𝟙 S) (𝟙 G.E) _ h ≫ ((P.e ≪≫ (projModelVCIso C P.W).symm).hom ≫
        (projModelVCIso C P.W).hom)
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id]
    simp only [Category.comp_id]
  · -- the `π` leg
    simp only [Category.assoc]
    have h1 : (transport_isPullback_model (𝟙 S) h P).isoPullback.hom ≫
        pullback.snd (projModelπ P.W)
          (Spec.map (CommRingCat.ofHom (sectionsMapLE (𝟙 S) h))) =
      projModelπ (P.W.map (sectionsMapLE (𝟙 S) h)) :=
      (transport_isPullback_model (𝟙 S) h P).isoPullback_hom_snd
    have h2 : (projModelVCIso (C.map (sectionsMapLE (𝟙 S) h))
          (P.W.map (sectionsMapLE (𝟙 S) h))).hom ≫
        projModelπ (P.W.map (sectionsMapLE (𝟙 S) h)) =
      projModelπ ((C.map (sectionsMapLE (𝟙 S) h)) •
        (P.W.map (sectionsMapLE (𝟙 S) h))) :=
      projModelVCIso_π _ _
    have h3 : eqToHom (congrArg projModel hWeq) ≫
        projModelπ ((C.map (sectionsMapLE (𝟙 S) h)) •
          (P.W.map (sectionsMapLE (𝟙 S) h))) =
      projModelπ ((C • P.W).map (sectionsMapLE (𝟙 S) h)) :=
      projModelπ_congr ((map_variableChange (φ := sectionsMapLE (𝟙 S) h)
        (C := C) (W := P.W)).symm)
    have h4 : (transport_isPullback_model (𝟙 S) h (P.ofVC C)).isoPullback.inv ≫
        projModelπ ((C • P.W).map (sectionsMapLE (𝟙 S) h)) =
      pullback.snd (projModelπ (P.ofVC C).W)
        (Spec.map (CommRingCat.ofHom (sectionsMapLE (𝟙 S) h))) :=
      (transport_isPullback_model (𝟙 S) h (P.ofVC C)).isoPullback_inv_snd
    have h5 : (transport_isPullback' (𝟙 S) (𝟙 G.E)
        (IsPullback.of_horiz_isIso ⟨by simp⟩) (P.ofVC C) h).isoPullback.hom ≫
        pullback.snd (projModelπ (P.ofVC C).W)
          (Spec.map (CommRingCat.ofHom (sectionsMapLE (𝟙 S) h))) =
      pullback.snd G.π V'.1.ι ≫ V'.2.isoSpec.hom :=
      (transport_isPullback' (𝟙 S) (𝟙 G.E)
        (IsPullback.of_horiz_isIso ⟨by simp⟩) (P.ofVC C) h).isoPullback_hom_snd
    have h0 : (transport_isPullback' (𝟙 S) (𝟙 G.E)
        (IsPullback.of_horiz_isIso ⟨by simp⟩) P h).isoPullback.hom ≫
        pullback.snd (projModelπ P.W)
          (Spec.map (CommRingCat.ofHom (sectionsMapLE (𝟙 S) h))) =
      pullback.snd G.π V'.1.ι ≫ V'.2.isoSpec.hom :=
      (transport_isPullback' (𝟙 S) (𝟙 G.E)
        (IsPullback.of_horiz_isIso ⟨by simp⟩) P h).isoPullback_hom_snd
    rw [h0, h1, h2, h3, h4, h5]

set_option backward.isDefEq.respectTransparency false in
/-- **(E12-C coherence)** Left-argument collapse: double restriction in the first
argument of a comparison. -/
theorem transVC_restrict_restrict_left {VP : S.affineOpens}
    (P : LocalPresentation G VP) {V V'' : S.affineOpens}
    (R : LocalPresentation G V'') (p : V.1 ≤ VP.1) (h : V''.1 ≤ V.1) :
    ((P.restrict p).restrict h).transVC R = (P.restrict (h.trans p)).transVC R := by
  have hWWP : (P.restrict (h.trans p)).W = ((P.restrict p).restrict h).W := by
    show P.W.map _ = (P.W.map _).map _
    rw [WeierstrassCurve.map_map]
    congr 1
    rw [sectionsMapLE_id, sectionsMapLE_id, sectionsMapLE_id, Scheme.resLE_comp]
  exact transVC_congr _ _ _ _ hWWP rfl (transportE_restrict_restrict P p h)
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
  have hWW : (P.transport f t hsq hz (h.trans hV')).W =
      ((P.transport f t hsq hz hV').restrict h).W := by
    show P.W.map _ = (P.W.map _).map _
    rw [WeierstrassCurve.map_map]
    congr 1
    rw [sectionsMapLE_id, sectionsMapLE_comp_resLE f hV' h]
  exact transVC_congr _ _ _ _ hWW rfl
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
  have hWWQ : (Q.restrict (h.trans q)).W = ((Q.restrict q).restrict h).W := by
    show Q.W.map _ = (Q.W.map _).map _
    rw [WeierstrassCurve.map_map]
    congr 1
    rw [sectionsMapLE_id, sectionsMapLE_id, sectionsMapLE_id, Scheme.resLE_comp]
  exact transVC_congr _ _ _ _ rfl hWWQ
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

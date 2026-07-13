/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.Comparison
import ModularCurves.EllipticCurve.GroupLawConstruction
import ModularCurves.EllipticCurve.WeierstrassAtlasBundle
import ModularCurves.ForMathlib.UnitCocycleSheaf

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
      (by rw [Category.assoc, G.zero_π, Category.comp_id, Category.id_comp])) ≫ e.hom =
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

section Transport

variable {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}

/-- The scheme-level restriction of `f` intertwines the affine-chart isomorphisms with
`Spec` of the sections comparison (naturality of `isoSpec`; mirrors
`SchemeQuotient.resLE_isoSpec_hom`). -/
private lemma resLE_isoSpec_naturality (f : S' ⟶ S) {V : S.affineOpens}
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
private noncomputable def transportTheta (f : S' ⟶ S) (t : G'.E ⟶ G.E)
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
private lemma transport_isPullback_model (f : S' ⟶ S) {V : S.affineOpens}
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

private lemma transportE_baseChange (f : S' ⟶ S) (t : G'.E ⟶ G.E)
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

/-- **(T-OM-B3)** Restriction of a presentation to a smaller affine open: transport
along the identity square. -/
noncomputable def restrict (P : LocalPresentation G V) {V' : S.affineOpens}
    (h : V'.1 ≤ V.1) : LocalPresentation G V' :=
  P.transport (𝟙 S) (𝟙 G.E) (IsPullback.of_horiz_isIso ⟨by simp⟩) (by simp)
    (by simpa using h)

/-! ### T-OM-B4: naturality of the comparison under transport -/

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
  sorry

/-- **(T-OM-B4)** The transition unit is natural under transport. -/
theorem transUnit_transport {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E)
    (hsq : IsPullback t G'.π G.π f) (hz : G'.zero ≫ t = f ≫ G.zero)
    (P Q : LocalPresentation G V)
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    (P.transport f t hsq hz hV').transUnit (Q.transport f t hsq hz hV') =
      Units.map (sectionsMapLE f hV').toMonoidHom (P.transUnit Q) := by
  sorry

/-- **(T-OM-B4)** Restriction form of the naturality: transition units restrict to
transition units. -/
theorem transUnit_restrict (P Q : LocalPresentation G V) {V' : S.affineOpens}
    (h : V'.1 ≤ V.1) :
    (P.restrict h).transUnit (Q.restrict h) =
      Units.map (sectionsMapLE (𝟙 S) (by simpa using h)).toMonoidHom (P.transUnit Q) := by
  sorry

end LocalPresentation

/-! ### T-OM-B5: the ω-cocycle of the atlas -/

open Scheme in
/-- **(T-OM-B5)** The transition cocycle of the invariant differential: on each pair of
atlas charts, the transition units of the affine-locally restricted chart comparisons,
glued over the pairwise intersection (`Scheme.exists_unit_glue`); the cocycle laws hold
affine-locally by `transUnit_trans` and glue by uniqueness. -/
noncomputable def omegaCocycle (G : EllipticCurveGeom S) : UnitCocycle S where
  ι := G.atlas.ι
  U i := (G.atlas.U i).1
  covers := G.atlas.covers
  u i j := by sorry
  u_self := by sorry
  u_cocycle := by sorry

open Scheme in
/-- **(T-OM-B5)** The defining property of the glued cocycle: on every affine open
inside a pairwise intersection, it restricts to the transition unit of the restricted
chart comparisons. -/
theorem omegaCocycle_res (G : EllipticCurveGeom S) (i j : G.atlas.ι)
    (V : S.affineOpens) (hV : V.1 ≤ (G.atlas.U i).1 ⊓ (G.atlas.U j).1) :
    resUnit hV ((omegaCocycle G).u i j) =
      ((G.atlas.presentation i).restrict (hV.trans inf_le_left)).transUnit
        ((G.atlas.presentation j).restrict (hV.trans inf_le_right)) := by
  sorry

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
  simp

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

end ModularCurves

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.ComparisonInjective

/-!
# The comparison theorem (T-W7.1b) — capstone

The four leaves of the comparison theorem, assembled from the `b1`/`b2` construction
(`pointedIsoCoordEquiv`, `pointedIsoCoordEquiv_filtration` in `ModelVariableChange`) and the
coefficient-extraction / bridge / injectivity content of
`Comparison{Coefficients,Bridge,Injective}`. Those files import `ModelVariableChange`, so the
leaves are discharged here, above the whole stack. Statements are the verbatim ticketed forms.

## Main results

* `pointedIsoCoordEquiv_coordX` / `_coordY` (b3x/b3y): the induced coordinate isomorphism sends
  `x'`, `y'` to `αx + β`, `γy + δx + ε` with `α`, `γ` units.
* `pointedIso_exists_variableChange` (main): every pointed isomorphism of projective Weierstrass
  models is induced by a variable change.
* `projModelVCIso_injective` (b5): the model action of `VariableChange` is faithful.
-/

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace ModularCurves

variable {R : Type u} [CommRing R]

/-- **(T-W7.1b-b3x, coordinator §2)** Coefficient extraction, `x`-side: `Φ(x') = αx + β`
with `α` a unit (from `F₂`-preservation + the freeness of `{1, x}`). Shared-witness
`∃`-bundle (α, β and the unitness travel together into b3y/the relation-matching). -/
theorem pointedIsoCoordEquiv_coordX {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W') :
    ∃ α β : R, IsUnit α ∧
      pointedIsoCoordEquiv e heπ hez (coordX W') =
        algebraMap R _ α * coordX W + algebraMap R _ β :=
  exists_coordX_image_of_filtration (pointedIsoCoordEquiv e heπ hez)
    (fun n => pointedIsoCoordEquiv_filtration e heπ hez n)

/-- **(T-W7.1b-b3y, coordinator §2)** Coefficient extraction, `y`-side:
`Φ(y') = γy + δx + ε` with `γ` a unit (from `F₃`-preservation). The five variable-change
coefficient equations + `α³ = γ²` (yielding `u := γ/α`) are the body of the main theorem
below, consuming b3x/b3y. -/
theorem pointedIsoCoordEquiv_coordY {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W') :
    ∃ γ δ ε : R, IsUnit γ ∧
      pointedIsoCoordEquiv e heπ hez (coordY W') =
        algebraMap R _ γ * coordY W + algebraMap R _ δ * coordX W + algebraMap R _ ε :=
  exists_coordY_image_of_filtration (pointedIsoCoordEquiv e heπ hez)
    (fun n => pointedIsoCoordEquiv_filtration e heπ hez n)

/-- **(generic, opaque)** Mid-factor cancellation: if `l ≫ g ≫ r = l ≫ g' ≫ r` (as `≃+*`)
with `l`, `r` fixed, then `g = g'`. Stated on small carriers so the kernel never sees the
heavy chart-iso terms. -/
lemma ringEquiv_trans_mid_inj {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C]
    [CommRing D] (l : A ≃+* B) (r : C ≃+* D) {g g' : B ≃+* C}
    (h : l.trans (g.trans r) = l.trans (g'.trans r)) : g = g' := by
  apply RingEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := l.surjective y
  have := DFunLike.congr_fun h x
  simp only [RingEquiv.trans_apply] at this
  exact r.injective this

/-- **(T-W7.1b-faith, S1)** Equal coordinate isos have equal `pointedIsoΓ`. RESOLVED
(faith-infra, def-level refactor): the fixed chart conjugator `coordRingToZSection`
(`ModelVariableChange`) exposes the whnf-free interface `pointedIsoCoordEquiv_apply` with a
*small* RHS — the four-fold composite stays sealed inside `coordRingToZSection`, so
rewriting the interface never triggers the previous `isDefEq` blow-up. `pointedIsoCoordEquiv`
factors as `(coordRingToZSection W).symm ∘ pointedIsoΓ e ∘ coordRingToZSection W'` with the
two fixed chart identifications; cancelling them (they are bijections) reads `pointedIsoΓ` off
`pointedIsoCoordEquiv` pointwise. -/
lemma pointedIsoΓ_eq_of_coordEquiv {W W' : WeierstrassCurve R}
    (e e' : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    (heπ' : e'.hom ≫ projModelπ W' = projModelπ W)
    (hez' : projModelZero W ≫ e'.hom = projModelZero W')
    (hc : pointedIsoCoordEquiv e heπ hez = pointedIsoCoordEquiv e' heπ' hez') :
    pointedIsoΓ e hez = pointedIsoΓ e' hez' := by
  refine RingEquiv.ext fun y => ?_
  have hkey := DFunLike.congr_fun hc ((coordRingToZSection W').symm y)
  rw [pointedIsoCoordEquiv_apply, pointedIsoCoordEquiv_apply,
    RingEquiv.apply_symm_apply] at hkey
  exact (coordRingToZSection W).symm.injective hkey

/-- **(T-W7.1b-faith, appLE bridge)** The `appLE` of a pointed iso from the target `Z`-chart to
the source `Z`-chart (both `X₂`-basic-opens) is exactly `pointedIsoΓ` as a ring map: both unfold
to `e.hom.app(Z') ≫ (restriction along the preimage-equality)`, and the two restriction arrows
agree because morphisms in `Opens` are unique. -/
lemma appLE_zChart_eq_pointedIsoΓ {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (hez : projModelZero W ≫ e.hom = projModelZero W') :
    e.hom.appLE
        (Proj.basicOpen (quotientGrading (projIdeal W'))
          ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2)))
        (Proj.basicOpen (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))
        (pointedIso_preimage_zChart e hez).ge =
      CommRingCat.ofHom (pointedIsoΓ e hez).toRingHom := by
  apply CommRingCat.hom_ext
  ext w
  rw [CommRingCat.hom_ofHom]
  rw [show (pointedIsoΓ e hez).toRingHom w = pointedIsoΓ e hez w from rfl, pointedIsoΓ_apply,
    Scheme.Hom.appLE]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  congr 1

/-- **(T-W7.1b-faith, reconstruction)** Two pointed isomorphisms of projective models with the
same induced `Γ`-level map on the `Z`-chart have equal underlying morphism. Reduces to agreement
on the `Z`-chart cover via `projModel_hom_ext_of_affine`; the `Z`-chart restriction of a pointed
iso is `Spec` of (a chart-transport of) `pointedIsoΓ`, so equal `pointedIsoΓ` forces equal
restrictions. -/
lemma pointedIso_hom_eq_of_pointedIsoΓ {W W' : WeierstrassCurve R}
    (e e' : projModel W ≅ projModel W')
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    (hez' : projModelZero W ≫ e'.hom = projModelZero W')
    (hΓ : pointedIsoΓ e hez = pointedIsoΓ e' hez') :
    e.hom = e'.hom := by
  refine projModel_hom_ext_of_affine W (Z := projModel W') ?_
  rw [Scheme.AffineOpenCover.openCover_f]
  have hUZ' : IsAffineOpen (Proj.basicOpen (quotientGrading (projIdeal W'))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))) :=
    Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W' 2) one_pos
  have happLE : e.hom.appLE _ _ (pointedIso_preimage_zChart e hez).ge =
      e'.hom.appLE _ _ (pointedIso_preimage_zChart e' hez').ge := by
    rw [appLE_zChart_eq_pointedIsoΓ e hez, appLE_zChart_eq_pointedIsoΓ e' hez', hΓ]
  have hKEY : (Proj.isAffineOpen_basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos).fromSpec ≫ e.hom =
      (Proj.isAffineOpen_basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos).fromSpec ≫ e'.hom := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec e.hom hUZ' _ (pointedIso_preimage_zChart e hez).ge,
        ← IsAffineOpen.SpecMap_appLE_fromSpec e'.hom hUZ' _ (pointedIso_preimage_zChart e' hez').ge,
        happLE]
  rw [Proj_fromSpec_awayToSection_awayι _ _ (mk_X_mem_quotientGrading_one W 2) one_pos] at hKEY
  haveI : IsIso (Proj.awayToSection (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))) :=
    inferInstanceAs (IsIso (Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W 2) one_pos).hom)
  have h2 := congrArg (fun t => inv (Spec.map (Proj.awayToSection (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))) ≫ t) hKEY
  simp only [Category.assoc, IsIso.inv_hom_id_assoc] at h2
  exact h2

/-- **(T-W7.1b, main — the comparison theorem)** Every isomorphism of projective Weierstrass
models over a ring `R` that respects the structure morphisms and the points at infinity is
induced by a variable change: there is a `C : VariableChange R` with `C • W' = W`, and `e` is
the transport of `projModelVCIso` along that equality. The proof route is the pole filtration:
a pointed iso preserves the affine part (`projModel_hom_ext_of_affine` territory) and the
filtration `F_n`, whose low-degree freeness forces `Φ(x') = αx + β`, `Φ(y') = γy + δx + ε`
with `α, γ` units; matching the two Weierstrass relations forces `α³ = γ²`, and
`u := γ/α` yields `C`. Source: audit A1; KM §2.2-style; prior-B2 fix-option (3). -/
theorem pointedIso_exists_variableChange (W W' : WeierstrassCurve R)
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W') :
    ∃ C : VariableChange R, ∃ hW : C • W' = W,
      e.hom = eqToHom (by rw [← hW]) ≫ (projModelVCIso C W').hom := by
  obtain ⟨C, hW, hx, hy⟩ := exists_variableChange_of_filtration
    (pointedIsoCoordEquiv e heπ hez) (fun n => pointedIsoCoordEquiv_filtration e heπ hez n)
  refine ⟨C, hW, ?_⟩
  set e' : projModel W ≅ projModel W' := eqToIso
    (congrArg projModel hW.symm) ≪≫ projModelVCIso C W' with he'def
  have he'hom : e'.hom = eqToHom (congrArg projModel hW.symm) ≫ (projModelVCIso C W').hom := by
    rw [he'def, Iso.trans_hom, eqToIso.hom]
  have transπ : ∀ {A B : WeierstrassCurve R} (h : A = B),
      eqToHom (congrArg projModel h) ≫ projModelπ B = projModelπ A := by
    intro A B h; cases h; simp
  have transZero : ∀ {A B : WeierstrassCurve R} (h : A = B),
      projModelZero A ≫ eqToHom (congrArg projModel h) = projModelZero B := by
    intro A B h; cases h; simp
  have heπ' : e'.hom ≫ projModelπ W' = projModelπ W := by
    rw [he'hom, Category.assoc, projModelVCIso_π, transπ hW.symm]
  have hez' : projModelZero W ≫ e'.hom = projModelZero W' := by
    rw [he'hom, ← Category.assoc, transZero hW.symm, projModelVCIso_zero]
  have coordEquiv_ext : ∀ (φ ψ : W'.toAffine.CoordinateRing →ₐ[R] W.toAffine.CoordinateRing),
      φ (coordX W') = ψ (coordX W') → φ (coordY W') = ψ (coordY W') → φ = ψ := by
    intro φ ψ hX hY
    have htest :
      (AdjoinRoot.of W'.toAffine.polynomial) Polynomial.X = coordX W' := by rw [coordX]; rfl
    have hofC : ∀ a : R,
      AdjoinRoot.of W'.toAffine.polynomial
      (Polynomial.C a) = algebraMap R W'.toAffine.CoordinateRing a := by
      intro a; rw [← AdjoinRoot.algebraMap_eq, ← Polynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply]
    have key : ∀ r : Polynomial R,
      AdjoinRoot.of W'.toAffine.polynomial r = Polynomial.aeval (coordX W') r := by
      intro r
      induction r using Polynomial.induction_on with
      | C a => rw [Polynomial.aeval_C, hofC]
      | add p q hp hq => rw [map_add, map_add, hp, hq]
      | monomial n a ih => rw [map_mul, map_pow, map_mul, map_pow, htest, hofC, Polynomial.aeval_X,
        Polynomial.aeval_C]
    have hof : ∀ r : Polynomial R,
      φ (AdjoinRoot.of W'.toAffine.polynomial r) = ψ (AdjoinRoot.of W'.toAffine.polynomial r) := by
      intro r
      rw [key, ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply, hX]
    apply AlgHom.ext
    intro a
    obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq a
    rw [WeierstrassCurve.Affine.CoordinateRing.smul, WeierstrassCurve.Affine.CoordinateRing.smul,
      mul_one, map_add, map_add, map_mul, map_mul,
      show Affine.CoordinateRing.mk W'.toAffine
        (Polynomial.C p) = AdjoinRoot.of W'.toAffine.polynomial p from rfl,
      show Affine.CoordinateRing.mk W'.toAffine
        (Polynomial.C q) = AdjoinRoot.of W'.toAffine.polynomial q from rfl,
      show Affine.CoordinateRing.mk W'.toAffine Polynomial.X = coordY W' from rfl,
      hof p, hof q, hY]
  have hXagree : (pointedIsoCoordEquiv e heπ hez) (coordX W') = (pointedIsoCoordEquiv e' heπ' hez')
    (coordX W') := by
    rw [hx,
      transport_general hW.symm e' (projModelVCIso C W') heπ' hez' (projModelVCIso_π C W')
      (projModelVCIso_zero C W') he'hom (coordX W'), bridge_coordX]
    simp only [map_add, coordRingCongr_algebraMap_mul_coordX, coordRingCongr_algebraMap]
  have hYagree : (pointedIsoCoordEquiv e heπ hez) (coordY W') = (pointedIsoCoordEquiv e' heπ' hez')
    (coordY W') := by
    rw [hy,
      transport_general hW.symm e' (projModelVCIso C W') heπ' hez' (projModelVCIso_π C W')
      (projModelVCIso_zero C W') he'hom (coordY W'), bridge_coordY]
    simp only [map_add, coordRingCongr_algebraMap_mul_coordY, coordRingCongr_algebraMap_mul_coordX,
      coordRingCongr_algebraMap]
  have hcoord : pointedIsoCoordEquiv e heπ hez = pointedIsoCoordEquiv e' heπ' hez' := by
    refine AlgEquiv.ext fun x => ?_
    exact DFunLike.congr_fun (coordEquiv_ext (pointedIsoCoordEquiv e heπ hez).toAlgHom
      (pointedIsoCoordEquiv e' heπ' hez').toAlgHom hXagree hYagree) x
  have hΓ : pointedIsoΓ e hez = pointedIsoΓ e' hez' :=
    pointedIsoΓ_eq_of_coordEquiv e e' heπ hez heπ' hez' hcoord
  have hhom : e.hom = e'.hom := pointedIso_hom_eq_of_pointedIsoΓ e e' hez hez' hΓ
  rw [hhom, he'hom]

/-- **(T-W7.1b, uniqueness — faithfulness of the model action)** The variable change inducing
a given pointed model isomorphism is unique: distinct variable changes with the same action on
`W` induce distinct model isomorphisms. (Uniqueness is NOT "C with C • W' = W is unique" —
automorphisms exist for special `W`; it is the pinning by the induced isomorphism.) Source:
audit A1 (b5); the filtration argument reads `(u, r, s, t)` off `Φ(x'), Φ(y')`. -/
theorem projModelVCIso_injective (C₁ C₂ : VariableChange R) (W : WeierstrassCurve R)
    (hW : C₁ • W = C₂ • W)
    (h : (projModelVCIso C₁ W).hom = eqToHom (by rw [hW]) ≫ (projModelVCIso C₂ W).hom) :
    C₁ = C₂ :=
  projModelVCIso_injective' C₁ C₂ W hW h

/-- The affine scheme's canonical `Spec` isomorphism agrees with the isomorphism attached
to any proof that its top open is affine. -/
private lemma isoSpec_hom_comp_isoSpec_inv_top (S : Scheme.{u}) [IsAffine S]
    (h : IsAffineOpen (⊤ : S.Opens)) :
    h.isoSpec.hom ≫ S.isoSpec.inv = (⊤ : S.Opens).ι := by
  rw [← IsAffineOpen.fromSpec_top, ← IsAffineOpen.isoSpec_inv_ι,
    Iso.hom_inv_id_assoc]

/-- The projective model of an elliptic Weierstrass curve is locally Weierstrass. The
whole affine base is one chart; the only bookkeeping identifies the global sections of
`Spec A` with `A` and compares the resulting base change of the projective model. -/
theorem locallyWeierstrass_projModel {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    [W.IsElliptic] :
    LocallyWeierstrass (projModelπ W) (projModelZero W) (projModelZero_projModelπ W) := by
  intro s
  let S := Spec (CommRingCat.of A)
  letI : Algebra A ↑Γ(S, (⊤ : S.Opens)) :=
    (Scheme.ΓSpecIso (.of A)).inv.hom.toAlgebra
  haveI : IsIso (⊤ : S.Opens).ι := by
    rw [← Scheme.topIso_hom]
    infer_instance
  haveI : IsIso (Spec.map (CommRingCat.ofHom
      (algebraMap A ↑Γ(S, (⊤ : S.Opens))))) := by
    have h : CommRingCat.ofHom (algebraMap A ↑Γ(S, (⊤ : S.Opens))) =
        (Scheme.ΓSpecIso (.of A)).inv := rfl
    rw [h]
    infer_instance
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap A ↑Γ(S, (⊤ : S.Opens)))) =
      S.isoSpec.inv := (Scheme.isoSpec_Spec_inv (.of A)).symm
  refine ⟨⟨⊤, isAffineOpen_top _⟩, trivial,
    W.map (algebraMap A ↑Γ(S, (⊤ : S.Opens))), inferInstance,
    asIso (pullback.fst (projModelπ W) (⊤ : S.Opens).ι) ≪≫
      (asIso (pullback.fst (projModelπ W) (Spec.map (CommRingCat.ofHom
        (algebraMap A ↑Γ(S, (⊤ : S.Opens))))))).symm ≪≫
      (isPullback_projModelBaseChange W).isoPullback.symm, ?_, ?_⟩
  · have hcrux : ∀ (h : (⊤ : S.Opens) ∈ S.affineOpens),
        (IsAffineOpen.isoSpec h).hom ≫ Spec.map (CommRingCat.ofHom
          (algebraMap A ↑Γ(S, (⊤ : S.Opens)))) = (⊤ : S.Opens).ι := by
      exact fun h => hφ ▸ isoSpec_hom_comp_isoSpec_inv_top S h
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom
      (algebraMap A ↑Γ(S, (⊤ : S.Opens)))))]
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc,
      IsPullback.isoPullback_inv_snd]
    conv_rhs => erw [hcrux]
    erw [← pullback.condition, IsIso.inv_hom_id_assoc]
    exact pullback.condition
  · have hcrux : (isAffineOpen_top S).isoSpec.inv ≫ (⊤ : S.Opens).ι =
        Spec.map (CommRingCat.ofHom (algebraMap A ↑Γ(S, (⊤ : S.Opens)))) :=
      hφ ▸ (IsAffineOpen.isoSpec_inv_ι _).trans IsAffineOpen.fromSpec_top
    have hcrux_assoc : ∀ {Z : Scheme.{u}} (g : S ⟶ Z),
        (isAffineOpen_top S).isoSpec.inv ≫ (⊤ : S.Opens).ι ≫ g =
          Spec.map (CommRingCat.ofHom
            (algebraMap A ↑Γ(S, (⊤ : S.Opens)))) ≫ g := fun g => by
      rw [← Category.assoc]
      exact congrArg (· ≫ g) hcrux
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc]
    rw [pullback.lift_fst_assoc]
    simp only [Category.assoc]
    conv_lhs => erw [hcrux_assoc]
    erw [← reassoc_of% projModelZero_baseChange W,
      ← (isPullback_projModelBaseChange W).isoPullback_hom_fst_assoc,
      IsIso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The residue-field map `R → κ(p)` of `Spec R` — the structure-sheaf composite
`toStalk ≫ residue` — sends every element of the prime `p` to zero. -/
private lemma toStalk_residue_hom_apply_eq_zero (p : ↥(Spec (CommRingCat.of R))) {a : R}
    (ha : a ∈ p.asIdeal) :
    (StructureSheaf.toStalk R p ≫ (Spec (CommRingCat.of R)).residue p) a = 0 := by
  have hcomp := Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of R) p
  have happ := congrArg (fun f => f a) hcomp
  change (Scheme.Spec.residueFieldIso (CommRingCat.of R) p).inv
      (algebraMap R p.asIdeal.ResidueField a) =
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (structurePresheafInCommRingCat R).germ ⊤ p trivial ≫
      (Spec (CommRingCat.of R)).residue p) a at happ
  rw [Ideal.algebraMap_residueField_eq_zero.mpr ha, map_zero] at happ
  change (Spec (CommRingCat.of R)).residue p
    ((structurePresheafInCommRingCat R).germ ⊤ p trivial
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) = 0
  exact happ.symm

/-- The fibre of the projective model `projModelπ W` at a point `p` of `Spec R` is, as a pointed
model, the projective model of the residue-field base change `W.map (algebraMap R κ(p))`. Paste
the fibre square (`Spec_fromSpecResidueField_eq`) against the base-change square
(`isPullback_projModelBaseChange`), both taken over the canonical `Spec κ(p) ⟶ Spec R`; the
resulting isomorphism carries `fiberToSpecResidueField` to the base-changed structure morphism and
the section point to the base-changed zero section. The hypothesis `halg` fixes the residue-field
algebra structure to that canonical composite (`rfl` for the structure-sheaf instance). -/
private lemma exists_projModelFiber_iso_baseChange (W : WeierstrassCurve R)
    (p : ↥(Spec (CommRingCat.of R)))
    [Algebra R ↑((Spec (CommRingCat.of R)).residueField p)]
    (halg : algebraMap R ↑((Spec (CommRingCat.of R)).residueField p) =
      (StructureSheaf.toStalk R p ≫ (Spec (CommRingCat.of R)).residue p).hom) :
    ∃ em : (projModelπ W).fiber p ≅
        projModel (W.map (algebraMap R ↑((Spec (CommRingCat.of R)).residueField p))),
      em.hom ≫ projModelπ (W.map (algebraMap R ↑((Spec (CommRingCat.of R)).residueField p))) =
          (projModelπ W).fiberToSpecResidueField p ∧
      sectionFiberPoint (projModelπ W) (projModelZero W) (projModelZero_projModelπ W) p ≫ em.hom =
          projModelZero (W.map (algebraMap R ↑((Spec (CommRingCat.of R)).residueField p))) := by
  have hofrfl : CommRingCat.ofHom
      (algebraMap R ↑((Spec (CommRingCat.of R)).residueField p)) =
      StructureSheaf.toStalk R p ≫ (Spec (CommRingCat.of R)).residue p := by
    rw [halg]; exact CommRingCat.ofHom_hom _
  have hfib : IsPullback ((projModelπ W).fiberι p)
      ((projModelπ W).fiberToSpecResidueField p) (projModelπ W)
      (Spec.map (StructureSheaf.toStalk R p ≫ (Spec (CommRingCat.of R)).residue p)) :=
    Spec_fromSpecResidueField_eq R p ▸ IsPullback.of_hasPullback (projModelπ W)
      ((Spec (CommRingCat.of R)).fromSpecResidueField p)
  have hbc : IsPullback
      (projModelBaseChange (algebraMap R ↑((Spec (CommRingCat.of R)).residueField p)) W)
      (projModelπ (W.map (algebraMap R ↑((Spec (CommRingCat.of R)).residueField p))))
      (projModelπ W)
      (Spec.map (StructureSheaf.toStalk R p ≫ (Spec (CommRingCat.of R)).residue p)) := by
    have hbc0 := isPullback_projModelBaseChange
      (R' := ↑((Spec (CommRingCat.of R)).residueField p)) W
    rwa [hofrfl] at hbc0
  refine ⟨hfib.isoPullback ≪≫ hbc.isoPullback.symm, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [(Iso.inv_comp_eq _).mpr hbc.isoPullback_hom_snd.symm, hfib.isoPullback_hom_snd]
  · rw [← cancel_mono hbc.isoPullback.hom]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hfib.isoPullback_hom_fst, hbc.isoPullback_hom_fst, projModelZero_baseChange, hofrfl]
      simp only [sectionFiberPoint, Scheme.Hom.fiberι]
      exact (pullback.lift_fst _ _ _).trans
        (congrArg (· ≫ projModelZero W) (Spec_fromSpecResidueField_eq R p))
    · simp only [Category.assoc]
      rw [hfib.isoPullback_hom_snd, hbc.isoPullback_hom_snd]
      simp only [sectionFiberPoint, Scheme.Hom.fiberToSpecResidueField, projModelZero_projModelπ]
      exact pullback.lift_snd _ _ _

/-- A Weierstrass model whose residue-field fibres are elliptic in the pointed-model
sense already has unit discriminant over the base ring. Indeed, compare each base-changed
model with the elliptic model supplied by `FibrewiseElliptic`; the pointed comparison theorem
makes the isomorphism a variable change, so it preserves unit discriminant. A nonunit
discriminant would vanish in the residue field of a maximal ideal, giving a contradiction. -/
theorem isElliptic_of_fibrewiseElliptic_projModel (W : WeierstrassCurve R)
    (h : FibrewiseElliptic (projModelπ W) (projModelZero W)
      (projModelZero_projModelπ W)) : W.IsElliptic := by
  constructor
  by_contra hΔ
  obtain ⟨I, hI, hΔI⟩ := exists_max_ideal_of_mem_nonunits
    (mem_nonunits_iff.mpr hΔ)
  let p : Spec (CommRingCat.of R) := ⟨I, hI.isPrime⟩
  obtain ⟨W', hW', e, heπ, hez⟩ := h p
  letI : Algebra R ↑((Spec (CommRingCat.of R)).residueField p) :=
    (StructureSheaf.toStalk R p ≫ (Spec (CommRingCat.of R)).residue p).hom.toAlgebra
  obtain ⟨em, emπ, emz⟩ := exists_projModelFiber_iso_baseChange W p rfl
  let e' : projModel (W.map (algebraMap R
      ↑((Spec (CommRingCat.of R)).residueField p))) ≅ projModel W' := em.symm ≪≫ e
  have he'π : e'.hom ≫ projModelπ W' =
      projModelπ (W.map (algebraMap R ↑((Spec (CommRingCat.of R)).residueField p))) := by
    simp only [e', Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [heπ, ← emπ, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have emz_inv :
      projModelZero (W.map (algebraMap R ↑((Spec (CommRingCat.of R)).residueField p))) ≫
        em.inv = sectionFiberPoint (projModelπ W) (projModelZero W)
          (projModelZero_projModelπ W) p := by
    rw [← cancel_mono em.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, emz]
  have he'z :
      projModelZero (W.map (algebraMap R ↑((Spec (CommRingCat.of R)).residueField p))) ≫
        e'.hom = projModelZero W' := by
    simp only [e', Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
    rw [emz_inv, hez]
  obtain ⟨C, hC, -⟩ := pointedIso_exists_variableChange
    (W.map (algebraMap R ↑((Spec (CommRingCat.of R)).residueField p))) W' e' he'π he'z
  letI : W'.IsElliptic := hW'
  haveI : (C • W').IsElliptic := inferInstance
  have hmapUnit : IsUnit
      (W.map (algebraMap R ↑((Spec (CommRingCat.of R)).residueField p))).Δ := by
    rw [← hC]
    exact (C • W').isUnit_Δ
  have hmapUnit' : IsUnit
      (algebraMap R ↑((Spec (CommRingCat.of R)).residueField p) W.Δ) := by
    rw [← W.map_Δ]
    exact hmapUnit
  have hmapZero : algebraMap R ↑((Spec (CommRingCat.of R)).residueField p) W.Δ = 0 :=
    toStalk_residue_hom_apply_eq_zero p hΔI
  exact hmapUnit'.ne_zero hmapZero

/-- For a globally presented Weierstrass model, the fibrewise condition is equivalent to
unit discriminant over the base ring. -/
theorem fibrewiseElliptic_projModel_iff_isElliptic (W : WeierstrassCurve R) :
    FibrewiseElliptic (projModelπ W) (projModelZero W) (projModelZero_projModelπ W) ↔
      W.IsElliptic := by
  constructor
  · exact isElliptic_of_fibrewiseElliptic_projModel W
  · intro hW
    letI : W.IsElliptic := hW
    exact fibrewiseElliptic_projModel W

/-- For a globally presented Weierstrass model, being locally Weierstrass is equivalent
to unit discriminant. -/
theorem locallyWeierstrass_projModel_iff_isElliptic (W : WeierstrassCurve R) :
    LocallyWeierstrass (projModelπ W) (projModelZero W) (projModelZero_projModelπ W) ↔
      W.IsElliptic := by
  constructor
  · intro hW
    exact isElliptic_of_fibrewiseElliptic_projModel W hW.fibrewiseElliptic
  · intro hW
    letI : W.IsElliptic := hW
    exact locallyWeierstrass_projModel W

/-- The full fibrewise/local comparison for a family already supplied with one global
Weierstrass equation. The unresolved general comparison is precisely the construction
of such an equation Zariski-locally from an abstract smooth proper family. -/
theorem fibrewiseElliptic_iff_locallyWeierstrass_projModel (W : WeierstrassCurve R) :
    FibrewiseElliptic (projModelπ W) (projModelZero W) (projModelZero_projModelπ W) ↔
      LocallyWeierstrass (projModelπ W) (projModelZero W)
        (projModelZero_projModelπ W) :=
  (fibrewiseElliptic_projModel_iff_isElliptic W).trans
    (locallyWeierstrass_projModel_iff_isElliptic W).symm

end ModularCurves

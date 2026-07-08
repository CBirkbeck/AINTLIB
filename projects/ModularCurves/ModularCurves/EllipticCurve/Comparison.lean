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
  set e' : projModel W ≅ projModel W' := eqToIso (congrArg projModel hW.symm) ≪≫ projModelVCIso C W' with he'def
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
    have htest : (AdjoinRoot.of W'.toAffine.polynomial) Polynomial.X = coordX W' := by rw [coordX]; rfl
    have hofC : ∀ a : R, AdjoinRoot.of W'.toAffine.polynomial (Polynomial.C a) = algebraMap R W'.toAffine.CoordinateRing a := by
      intro a; rw [← AdjoinRoot.algebraMap_eq, ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    have key : ∀ r : Polynomial R, AdjoinRoot.of W'.toAffine.polynomial r = Polynomial.aeval (coordX W') r := by
      intro r
      induction r using Polynomial.induction_on with
      | C a => rw [Polynomial.aeval_C, hofC]
      | add p q hp hq => rw [map_add, map_add, hp, hq]
      | monomial n a ih => rw [map_mul, map_pow, map_mul, map_pow, htest, hofC, Polynomial.aeval_X, Polynomial.aeval_C]
    have hof : ∀ r : Polynomial R, φ (AdjoinRoot.of W'.toAffine.polynomial r) = ψ (AdjoinRoot.of W'.toAffine.polynomial r) := by
      intro r
      rw [key, ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply, hX]
    apply AlgHom.ext
    intro a
    obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq a
    rw [WeierstrassCurve.Affine.CoordinateRing.smul, WeierstrassCurve.Affine.CoordinateRing.smul, mul_one, map_add, map_add, map_mul, map_mul,
      show Affine.CoordinateRing.mk W'.toAffine (Polynomial.C p) = AdjoinRoot.of W'.toAffine.polynomial p from rfl,
      show Affine.CoordinateRing.mk W'.toAffine (Polynomial.C q) = AdjoinRoot.of W'.toAffine.polynomial q from rfl,
      show Affine.CoordinateRing.mk W'.toAffine Polynomial.X = coordY W' from rfl,
      hof p, hof q, hY]
  have hXagree : (pointedIsoCoordEquiv e heπ hez) (coordX W') = (pointedIsoCoordEquiv e' heπ' hez') (coordX W') := by
    rw [hx, transport_general hW.symm e' (projModelVCIso C W') heπ' hez' (projModelVCIso_π C W') (projModelVCIso_zero C W') he'hom (coordX W'), bridge_coordX]
    simp only [map_add, coordRingCongr_algebraMap_mul_coordX, coordRingCongr_algebraMap]
  have hYagree : (pointedIsoCoordEquiv e heπ hez) (coordY W') = (pointedIsoCoordEquiv e' heπ' hez') (coordY W') := by
    rw [hy, transport_general hW.symm e' (projModelVCIso C W') heπ' hez' (projModelVCIso_π C W') (projModelVCIso_zero C W') he'hom (coordY W'), bridge_coordY]
    simp only [map_add, coordRingCongr_algebraMap_mul_coordY, coordRingCongr_algebraMap_mul_coordX, coordRingCongr_algebraMap]
  have hcoord : pointedIsoCoordEquiv e heπ hez = pointedIsoCoordEquiv e' heπ' hez' := by
    refine AlgEquiv.ext fun x => ?_
    exact DFunLike.congr_fun (coordEquiv_ext (pointedIsoCoordEquiv e heπ hez).toAlgHom (pointedIsoCoordEquiv e' heπ' hez').toAlgHom hXagree hYagree) x
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

end ModularCurves

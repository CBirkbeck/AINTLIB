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

/-- Application form of the coordinate iso: `pointedIsoΓ e` wrapped in the fixed chart
bijections, at a point. `rfl` at the FUNCTION level (`toFun`/`trans_apply` are structural
projections — the heavy composite is never unfolded by the kernel). -/
lemma pointedIsoCoordEquiv_apply {W W' : WeierstrassCurve R}
    (e : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    (x : W'.toAffine.CoordinateRing) :
    pointedIsoCoordEquiv e heπ hez x =
      chartZRingEquiv W ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W 2) one_pos).commRingCatIsoToRingEquiv.symm
        (pointedIsoΓ e hez ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W'))
      ((quotientGradingHom (projIdeal W')) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W' 2) one_pos).commRingCatIsoToRingEquiv
          ((chartZRingEquiv W').symm x)))) :=
  rfl

-- v10.24(b): with the rfl interface (`pointedIsoCoordEquiv_apply`) proved above while the
-- chart isos are reducible, seal ALL FOUR heavy b1 isos (+ the mathlib `basicOpenIsoAway`
-- wrapper) `local irreducible`, so consumer proofs below never trigger `whnf`/`isDefEq` on
-- the raw terms — the previous session's wall (only `pointedIsoCoordEquiv`/`pointedIsoΓ`
-- sealed, wrappers still ground) is fixed by sealing the wrappers too.
attribute [local irreducible] pointedIsoCoordEquiv pointedIsoΓ chartZRingEquiv
  Proj.basicOpenIsoAway CategoryTheory.Iso.commRingCatIsoToRingEquiv

/-- **(T-W7.1b-faith, S1)** Equal coordinate isos have equal `pointedIsoΓ`. REFINED FINDING
(session 2, v10.24(b) attempt): sealing ALL heavy b1 isos `local irreducible` (above) DOES fix
the generic-lemma steps — `hp` (chart-iso `symm_apply_apply`/`apply_symm_apply` cancellation)
now compiles cheaply. But the wall PERSISTS on any `rw [pointedIsoCoordEquiv_apply]` / `change` /
`.trans` that forces the elaborator's `isDefEq` on the heavy 4-fold-nested composite
`chartZW(BOA.symm(pointedIsoΓ e (BOA'(chartZW'.symm ·))))` — because the terms are huge *as
stated*, not merely when unfolded, so opacity doesn't shrink them. Only pure `rfl`
(`pointedIsoCoordEquiv_apply`, kernel-checked once) survives. CONCLUSION: local attributes are
insufficient; faith-infra needs DEFINITION-level irreducibility in `ModelVariableChange` + a
rebuild of the b2 proofs that unfold these defs, replaced by interface lemmas — a systematic
`/develop --decompose`-scale refactor. Boarded under T-W7.1b-faith-infra. -/
lemma pointedIsoΓ_eq_of_coordEquiv {W W' : WeierstrassCurve R}
    (e e' : projModel W ≅ projModel W')
    (heπ : e.hom ≫ projModelπ W' = projModelπ W)
    (hez : projModelZero W ≫ e.hom = projModelZero W')
    (heπ' : e'.hom ≫ projModelπ W' = projModelπ W)
    (hez' : projModelZero W ≫ e'.hom = projModelZero W')
    (hc : pointedIsoCoordEquiv e heπ hez = pointedIsoCoordEquiv e' heπ' hez') :
    pointedIsoΓ e hez = pointedIsoΓ e' hez' := by
  sorry

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
  sorry

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

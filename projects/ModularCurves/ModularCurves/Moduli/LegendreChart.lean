/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.E3DatumAssembly
import ModularCurves.Moduli.LevelMarking
import ModularCurves.ForMathlib.NegModelAffineSection

/-!
# The Legendre chart: normalising a marked char-≠2 presentation (T-G3a-SUB2)

**(STREAM-OMEGA 2026-07-25; the `N = 2` mirror of `isE3Chart`.)** The scheme-level
counterpart of `ModularCurves.exists_legendre_variableChange_of_two_torsion`: given a
local presentation `P₀` in char-≠2 normal form (`a₁ = a₃ = 0`) marking two sections at
`(p, 0)` and `(p', 0)`, together with

* Vieta data `e₃` expressing the cubic as `(x−p)(x−p')(x−e₃)`, and
* a unit square root `u` of `p' − p`,

the twisted chart `P₀.ofVC ⟨u, p, 0, 0⟩` is a **Legendre** chart: its curve is
`legendreCurve λ` for `λ = u⁻²(e₃ − p)`, it marks the first section at `(0, 0)` and the
second at `(1, 0)`. Together with `LocalPresentation.IsAdapted.ofVC` this discharges all
four conjuncts of `IsLegendreDatum` at a point.

The field/algebraically-closed hypotheses are **not** needed here — they enter only when
producing `e₃` (`exists_third_root_vieta`) and `u` (`IsAlgClosed.exists_pow_nat_eq`).
-/

universe u

open CategoryTheory AlgebraicGeometry Limits WeierstrassCurve

namespace ModularCurves

open LocalPresentation

variable {S : Scheme.{u}} {G : EllipticCurveGeom S} {V : S.affineOpens}

set_option backward.isDefEq.respectTransparency false in
/-- **(T-G3a-SUB2, the `2`-torsion negation bridge ★)** A chart-marked `2`-torsion
section is negation-symmetric in its chart coordinates: `negY p q = q`, i.e.
`−q − a₁p − a₃ = q`. The `N = 2` mirror of `hdbl_of_marked_three_torsion`, but with no
doubling needed — `2 • Z = 0` gives `−Z = Z` directly, and the negation coordinate is
`negModelHom_affineSection_general`. -/
theorem negY_marked_eq_of_two_torsion {S : Scheme.{u}} {E : EllipticCurve S}
    {V : S.affineOpens} (Pr : LocalPresentation E.toEllipticCurveGeom V)
    {σ : S ⟶ E.toEllipticCurveGeom.E} {hσ : σ ≫ E.toEllipticCurveGeom.π = 𝟙 S}
    {p q : Γ(S, V.1)} (heq : Pr.W.toAffine.Equation p q)
    (hMeq : (V.2.isoSpec.inv ≫ sectionLift E.toEllipticCurveGeom hσ V) ≫ Pr.e.hom =
      projModelAffineSection Pr.W p q heq)
    (hkill : (2 : ℤ) • (⟨σ, hσ⟩ : E.Section) = 0) :
    Pr.W.toAffine.negY p q = q := by
  letI := Pr.elliptic
  set σm := chartPointsEquiv Pr (𝟙 (Spec Γ(S, V.1)))
    (EllipticCurve.Point.pull E (𝟙 (Spec Γ(S, V.1)) ≫ chartρ V) ⟨σ, hσ⟩) with hσm
  have hσmval : σm = ⟨projModelAffineSection Pr.W p q heq,
      projModelAffineSection_projModelπ _ _ _ _⟩ := by
    refine Subtype.ext ?_
    rw [hσm, chartPointsEquiv_pull_marked Pr (𝟙 _) heq hMeq]
    exact Category.id_comp _
  have hkillE : (2 : ℤ) • EllipticCurve.Point.pull E
      (𝟙 (Spec Γ(S, V.1)) ≫ chartρ V) ⟨σ, hσ⟩ = 0 := by
    rw [← EllipticCurve.Point.pull_zsmul, hkill, EllipticCurve.Point.pull_zero]
  have h2 : (2 : ℤ) • σm = 0 := by
    rw [hσm, ← map_zsmul, hkillE, map_zero]
  have hneg : -σm = σm := by
    refine neg_eq_of_add_eq_zero_left ?_
    rw [← two_zsmul]
    exact h2
  have hnegval : -σm = (⟨projModelAffineSection Pr.W p (Pr.W.toAffine.negY p q)
      ((Pr.W.toAffine.equation_neg p q).mpr heq),
      projModelAffineSection_projModelπ _ _ _ _⟩ :
    (modelEllipticCurve Pr.W).Section) := by
    refine Subtype.ext ?_
    have hv : (-σm).1 = σm.1 ≫ (modelEllipticCurve Pr.W).mulByHom (-1) := by
      rw [show -σm = (-1 : ℤ) • σm from (neg_one_zsmul σm).symm]
      exact (modelEllipticCurve Pr.W).point_smul_eq_comp_mulBy _ (-1) σm
    rw [hv, modelEllipticCurve_mulByHom_neg_one, hσmval]
    exact negModelHom_affineSection_general Pr.W p q heq
  have hvals : projModelAffineSection Pr.W p (Pr.W.toAffine.negY p q)
      ((Pr.W.toAffine.equation_neg p q).mpr heq)
      = projModelAffineSection Pr.W p q heq :=
    congrArg Subtype.val (hnegval.symm.trans (hneg.trans hσmval))
  exact (projModelAffineSection_injective Pr.W (heq := hvals)).2

set_option backward.isDefEq.respectTransparency false in
/-- **(T-G3a-SUB2, the Legendre chart ★)** A char-≠2 chart marking two sections at
`(p, 0)`, `(p', 0)`, with Vieta data and a square root `u² = p' − p`, becomes a Legendre
chart after the variable change `⟨u, p, 0, 0⟩`: the curve is `legendreCurve (u⁻²(e₃−p))`
and the two marks move to `(0, 0)` and `(1, 0)`.

This is the `N = 2` mirror of `isE3Chart`; the algebraic heart is
`scale_translate_smul_eq_legendreCurve` and the marking transport is
`LocalPresentation.MarksAt.ofVC`. -/
theorem isLegendreChart (P₀ : LocalPresentation G V)
    (ha₁ : P₀.W.a₁ = 0) (ha₃ : P₀.W.a₃ = 0)
    {σP σQ : S ⟶ G.E} {hσP : σP ≫ G.π = 𝟙 S} {hσQ : σQ ≫ G.π = 𝟙 S}
    {p p' e₃ : Γ(S, V.1)} (hMP : P₀.MarksAt hσP p 0) (hMQ : P₀.MarksAt hσQ p' 0)
    (ha₂ : P₀.W.a₂ = -(p + p' + e₃))
    (ha₄ : P₀.W.a₄ = p * p' + p * e₃ + p' * e₃)
    (ha₆ : P₀.W.a₆ = -(p * p' * e₃))
    (u : Γ(S, V.1)ˣ) (hu : ((u : Γ(S, V.1))) ^ 2 = p' - p) :
    (P₀.ofVC ⟨u, p, 0, 0⟩).W =
        legendreCurve (((u⁻¹ : Γ(S, V.1)ˣ) : Γ(S, V.1)) ^ 2 * (e₃ - p)) ∧
      (P₀.ofVC ⟨u, p, 0, 0⟩).MarksAt hσP 0 0 ∧
      (P₀.ofVC ⟨u, p, 0, 0⟩).MarksAt hσQ 1 0 := by
  set C : VariableChange Γ(S, V.1) := ⟨u, p, 0, 0⟩ with hC
  set lam : Γ(S, V.1) := ((u⁻¹ : Γ(S, V.1)ˣ) : Γ(S, V.1)) ^ 2 * (e₃ - p) with hlam
  have hW : (P₀.ofVC C).W = legendreCurve lam :=
    scale_translate_smul_eq_legendreCurve ha₁ ha₃ u ha₂ ha₄ ha₆ hu
  refine ⟨hW, ?_, ?_⟩
  · have hEq : (C • P₀.W).toAffine.Equation 0 0 := by
      rw [show C • P₀.W = legendreCurve lam from hW]
      exact legendreCurve_equation_zero lam
    refine LocalPresentation.MarksAt.ofVC P₀ C hEq ?_
    rw [hC]
    simpa using hMP
  · have hEq : (C • P₀.W).toAffine.Equation 1 0 := by
      rw [show C • P₀.W = legendreCurve lam from hW]
      exact legendreCurve_equation_one lam
    refine LocalPresentation.MarksAt.ofVC P₀ C hEq ?_
    rw [hC]
    have hp' : (u : Γ(S, V.1)) ^ 2 + p = p' := by rw [hu]; ring
    simpa [hp'] using hMQ


set_option backward.isDefEq.respectTransparency false in
/-- **(T-G3a-SUB2, the marked char-≠2 chart ★)** From a naive full level-`2` structure on
`E/S` and any chart, the square-completing variable change produces a chart with
`a₁ = a₃ = 0` marking the two level sections at `(p, 0)`, `(p', 0)` with `p' − p` a unit,
and the chart cubic splits as `(x−p)(x−p')(x−e₃)`.

The three inputs are: `negY_marked_eq_of_two_torsion` + `two_torsion_coords_of_charNeTwoNF`
(the marks are `2`-torsion, so `q = 0` and the abscissae are roots),
`isUnit_x_diff_of_marked_pair` + `pull_ne_pm_of_isNaiveFullLevel` (the abscissa difference
is a unit), and `exists_third_root_vieta` (the third root). -/
theorem exists_marked_charNeTwo_chart {S : Scheme.{u}} {E : EllipticCurve S}
    {V : S.affineOpens} (Pr : LocalPresentation E.toEllipticCurveGeom V)
    (h2 : IsUnit (2 : Γ(S, V.1))) (hN : NIsInvertible S 2)
    {P Q : E.Section} (hL : E.IsNaiveFullLevel 2 P Q) :
    ∃ (C : VariableChange Γ(S, V.1)) (p p' e₃ : Γ(S, V.1)),
      (C.u : Γ(S, V.1)) = 1 ∧
      (Pr.ofVC C).W.a₁ = 0 ∧ (Pr.ofVC C).W.a₃ = 0 ∧
      (Pr.ofVC C).MarksAt P.2 p 0 ∧ (Pr.ofVC C).MarksAt Q.2 p' 0 ∧
      (Pr.ofVC C).W.a₂ = -(p + p' + e₃) ∧
      (Pr.ofVC C).W.a₄ = p * p' + p * e₃ + p' * e₃ ∧
      (Pr.ofVC C).W.a₆ = -(p * p' * e₃) ∧
      IsUnit (p' - p) := by
  classical
  -- the square-completing variable change
  set C : VariableChange Γ(S, V.1) :=
    ⟨1, 0, -((h2.unit⁻¹ : Γ(S, V.1)ˣ) : Γ(S, V.1)) * Pr.W.a₁,
      -((h2.unit⁻¹ : Γ(S, V.1)ˣ) : Γ(S, V.1)) * Pr.W.a₃⟩ with hC
  have ha₁ : (Pr.ofVC C).W.a₁ = 0 := completeSquareVC_a₁ h2
  have ha₃ : (Pr.ofVC C).W.a₃ = 0 := completeSquareVC_a₃ h2
  -- markings of the two level sections on the square-completed chart
  obtain ⟨p, q, hMP⟩ := (Pr.ofVC C).marksAt_of_forall_pull_ne_zero P.2
    (fun k _ _ t => E.pull_ne_zero_left_of_isNaiveFullLevel 2 one_lt_two hN hL k t)
  obtain ⟨p', q', hMQ⟩ := (Pr.ofVC C).marksAt_of_forall_pull_ne_zero Q.2
    (fun k _ _ t => E.pull_ne_zero_right_of_isNaiveFullLevel 2 one_lt_two hN hL k t)
  -- both sections are `2`-torsion, so `q = q' = 0` and the abscissae are cubic roots
  have hkillP : (2 : ℤ) • (⟨(P : S ⟶ E.E), P.2⟩ : E.Section) = 0 := by
    have h := hL.1.1
    exact_mod_cast h
  have hkillQ : (2 : ℤ) • (⟨(Q : S ⟶ E.E), Q.2⟩ : E.Section) = 0 := by
    have h := hL.1.2
    exact_mod_cast h
  obtain ⟨heqP, hMeqP⟩ := id hMP
  obtain ⟨heqQ, hMeqQ⟩ := id hMQ
  have hnegP := negY_marked_eq_of_two_torsion (Pr.ofVC C) heqP hMeqP hkillP
  have hnegQ := negY_marked_eq_of_two_torsion (Pr.ofVC C) heqQ hMeqQ hkillQ
  obtain ⟨hq0, hcubP⟩ := two_torsion_coords_of_charNeTwoNF h2 ha₁ ha₃ heqP hnegP
  obtain ⟨hq0', hcubQ⟩ := two_torsion_coords_of_charNeTwoNF h2 ha₁ ha₃ heqQ hnegQ
  subst hq0
  subst hq0'
  -- the abscissa difference is a unit (`Q̄ ≠ ±P̄` fibrewise)
  have hdiff : IsUnit (p' - p) :=
    isUnit_x_diff_of_marked_pair (Pr.ofVC C) heqP hMeqP heqQ hMeqQ
      (fun k _ _ tk => E.pull_ne_pm_of_isNaiveFullLevel 2 one_lt_two hN hL k tk)
  -- the third root
  obtain ⟨e₃, ha₂v, ha₄v, ha₆v⟩ := exists_third_root_vieta hcubP hcubQ
    (by simpa using hdiff.neg)
  exact ⟨C, p, p', e₃, rfl, ha₁, ha₃, hMP, hMQ, ha₂v, ha₄v, ha₆v, hdiff⟩

/-! ## The Legendre datum over an algebraically closed field -/

set_option backward.isDefEq.respectTransparency false in
/-- Over `Spec k` with `k` algebraically closed, a unit has a unit square root. -/
theorem exists_unit_sq_eq_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    {x : Γ(Spec (CommRingCat.of k), (⊤ : (Spec (CommRingCat.of k)).Opens))}
    (hx : IsUnit x) :
    ∃ w : Γ(Spec (CommRingCat.of k), (⊤ : (Spec (CommRingCat.of k)).Opens))ˣ,
      ((w : Γ(Spec (CommRingCat.of k), (⊤ : (Spec (CommRingCat.of k)).Opens)))) ^ 2 = x := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq
    ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom x) (n := 2) (by norm_num)
  refine ⟨?_, ?_⟩
  · refine IsUnit.unit (a := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom y) ?_
    refine isUnit_of_mul_isUnit_left (y := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom y) ?_
    rw [← map_mul, show y * y = y ^ 2 from (sq y).symm, hy]
    have : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom x) = x := by
      rw [← CommRingCat.comp_apply, (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id]
      rfl
    rw [this]; exact hx
  · rw [IsUnit.unit_spec, ← map_pow, hy, ← CommRingCat.comp_apply,
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- **(T-G3a-SUB2h ★)** Over an algebraically closed field in which `2` is invertible,
every elliptic curve carries a **Legendre datum**. -/
theorem exists_isLegendreDatum_of_isAlgClosed {R : CommRingCat.{u}} (X : EllObj R)
    (k : Type u) [Field k] [IsAlgClosed k] (hk : (2 : k) ≠ 0)
    (t : Spec (CommRingCat.of k) ⟶ X.base) :
    ∃ (L : (X.pullbackAlong t).curve.FullLevelPt 2)
      (b : OmegaBasis (X.pullbackAlong t).curve.toEllipticCurveGeom),
      IsLegendreDatum (X.pullbackAlong t) L b := by
  classical
  set X' : EllObj R := X.pullbackAlong t with hX'
  set S : Scheme.{u} := Spec (CommRingCat.of k) with hS
  set E : EllipticCurve S := X'.curve with hE
  -- the level structure and the invertibility of `2` on the base
  obtain ⟨P, Q, hPQ⟩ := EllipticCurve.exists_isNaiveFullLevel_of_le_two k E 2 le_rfl hk
  have hN : NIsInvertible S 2 := (nIsInvertible_spec_iff k 2).mpr hk
  -- the chart: over `Spec k` the atlas chart at the unique point is all of `S`
  set V₀ : S.affineOpens := ⟨⊤, isAffineOpen_top S⟩ with hV₀
  obtain ⟨s₀⟩ : Nonempty ↥S := inferInstance
  obtain ⟨i, hsi⟩ := E.toEllipticCurveGeom.atlas.covers s₀
  have hle : V₀.1 ≤ (E.toEllipticCurveGeom.atlas.U i).1 := by
    intro x _
    rwa [Subsingleton.elim x s₀]
  set P₁ : LocalPresentation E.toEllipticCurveGeom V₀ :=
    (E.toEllipticCurveGeom.atlas.presentation i).restrict hle with hP₁
  set b₀ : OmegaBasis E.toEllipticCurveGeom := OmegaBasis.ofPresentation rfl P₁ with hb₀
  have hAd₀ : P₁.IsAdapted b₀ := by
    have h : ((P₁.restrict (le_refl V₀.1)).basisUnitAt b₀).1 = 1 :=
      isAdapted_restrict_ofPresentation rfl P₁ (le_refl _)
    show (P₁.basisUnitAt b₀).1 = 1
    rw [← basisUnitAt_restrict P₁ b₀ (le_refl _)] at h
    rw [← h]
    exact (Units.ext (by simp)).symm
  -- `2` is a unit on the chart
  have h2 : IsUnit (2 : Γ(S, V₀.1)) := by
    have h := (isUnit_iff_ne_zero.mpr hk).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    rwa [map_ofNat] at h
  -- the square-completed, marked chart with its Vieta data
  obtain ⟨C, p, p', e₃, hCu, ha₁, ha₃, hMP, hMQ, ha₂v, ha₄v, ha₆v, hdiff⟩ :=
    exists_marked_charNeTwo_chart P₁ h2 hN hPQ
  -- the square root of the abscissa difference
  obtain ⟨w, hw⟩ := exists_unit_sq_eq_of_isAlgClosed (x := p' - p) hdiff
  -- the Legendre chart
  obtain ⟨hW, hM0, hM1⟩ :=
    isLegendreChart (P₁.ofVC C) ha₁ ha₃ hMP hMQ ha₂v ha₄v ha₆v w hw
  -- adaptedness is transported through the two twists
  have hAd₁ : (P₁.ofVC C).IsAdapted ((1 : Γ(S, ⊤)ˣ)⁻¹ • b₀) := by
    refine IsAdapted.ofVC hAd₀ C 1 ?_
    refine Units.ext ?_
    rw [Scheme.resUnit_val, hCu]
    simp
  have hAd₂ : ((P₁.ofVC C).ofVC ⟨w, p, 0, 0⟩).IsAdapted
      (w⁻¹ • ((1 : Γ(S, ⊤)ˣ)⁻¹ • b₀)) := by
    refine IsAdapted.ofVC hAd₁ ⟨w, p, 0, 0⟩ w ?_
    refine Units.ext ?_
    rw [Scheme.resUnit_val]
    exact Scheme.resLE_rfl _ _
  refine ⟨⟨⟨P, Q⟩, hPQ⟩, w⁻¹ • ((1 : Γ(S, ⊤)ˣ)⁻¹ • b₀), fun s => ?_⟩
  exact ⟨V₀, trivial, (P₁.ofVC C).ofVC ⟨w, p, 0, 0⟩,
    ((w⁻¹ : Γ(S, V₀.1)ˣ) : Γ(S, V₀.1)) ^ 2 * (e₃ - p), hAd₂, hW, hM0, hM1⟩

end ModularCurves

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.UniversalAdapted
import ModularCurves.Moduli.Representability
import ModularCurves.Moduli.GammaH
import ModularCurves.EllipticCurve.AffinePointSection
import ModularCurves.EllipticCurve.LegendreNormalForm

/-!
# The Legendre `δ`: KM 4.6.2's coupled marking condition (T-E14b)

**(STREAM-OMEGA 2026-07-14; the corrected T-E14 statement layer.)** KM 4.6.2's
Legendre problem is NOT the plain product `Γ(2)-naive × ω` — it is the subfunctor of
pairs `((P, Q), ω)` *"for which the adapted `x` satisfies `x(P₂) = 0, x(Q₂) = 1`"*:
the level datum is coupled to the `ω`-datum through the `ω`-adapted Weierstrass model.

This file makes that condition formal:

* `LocalPresentation.MarksAt`: a chart presentation carries a global section of the
  curve to the affine-point section `[p : q : 1]` of its chart model
  (`projModelAffineSection`).
* `MarksAt.transport`: the marking transports along cartesian pointed squares — the
  section-analog of `LocalPresentation.transport`'s `compat_zero`, with
  `projModelAffineSection_baseChange` in place of `projModelZero_baseChange`.
* `IsLegendreDatum`: locally on the base there is a `b`-adapted presentation whose
  chart curve IS a Legendre curve, marking `P` at `(0, 0)` and `Q` at `(1, 0)`.
  This is KM's `δ`-condition in local-existence form (by the translation-torsor
  uniqueness `transVC_of_isAdapted_charNeTwo` + the `{±1}`-rigidity
  `legendreCurve_vc_marked`, the witness is in fact unique — upgrading to canonical
  global data is the business of the representability proof, not the statement).
* `IsLegendreDatum.map`: the condition is functorial along `Ell/R`-morphisms.

The engine axioms 1/2 for this `δ` (representability by
`M'₂ = Spec ℤ[1/2][λ][(λ(λ−1))⁻¹]`, finite-étale torsor fibres) are T-E14's remaining
proof obligations, stated in `Moduli/Bootstrap.lean`.
-/

universe u

noncomputable section

namespace ModularCurves

open AlgebraicGeometry CategoryTheory Limits Scheme TopologicalSpace

variable {S : Scheme.{u}} {G : EllipticCurveGeom S}

/-- The chart-restriction of a global section of the curve: the induced morphism from
the affine piece into the chart pullback. -/
def sectionLift (G : EllipticCurveGeom S) {σ : S ⟶ G.E} (hσ : σ ≫ G.π = 𝟙 S)
    (V : S.affineOpens) : (V.1 : Scheme.{u}) ⟶ pullback G.π V.1.ι :=
  pullback.lift (V.1.ι ≫ σ) (𝟙 _)
    (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])

namespace LocalPresentation

/-- **(T-E14b-2)** The presentation `Pr` **marks** the section `σ` at the affine point
`(p, q)` of its chart curve: through the chart isomorphism, the restricted section is
the affine-point section `[p : q : 1]`. This is the formal "`x(σ) = p` (and
`y(σ) = q`) in the chart model". -/
def MarksAt {V : S.affineOpens} (Pr : LocalPresentation G V)
    {σ : S ⟶ G.E} (hσ : σ ≫ G.π = 𝟙 S) (p q : Γ(S, V.1)) : Prop :=
  ∃ h : Pr.W.toAffine.Equation p q,
    (V.2.isoSpec.inv ≫ sectionLift G hσ V) ≫ Pr.e.hom =
      projModelAffineSection Pr.W p q h

set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14b-2 ★)** Markings transport along cartesian pointed squares: if `Pr` marks
`σ` at `(p, q)` and `σ'` lies over `σ` (`σ' ≫ t = f ≫ σ`), the transported
presentation marks `σ'` at the restricted point. Mirrors the `compat_zero` field of
`LocalPresentation.transport` with the affine-point section in place of the zero
section. -/
theorem MarksAt.transport {S' : Scheme.{u}} {G' : EllipticCurveGeom S'}
    (f : S' ⟶ S) (t : G'.E ⟶ G.E) (hsq : IsPullback t G'.π G.π f)
    (hz : G'.zero ≫ t = f ≫ G.zero)
    {V : S.affineOpens} {Pr : LocalPresentation G V}
    {σ : S ⟶ G.E} {hσ : σ ≫ G.π = 𝟙 S} {p q : Γ(S, V.1)}
    (hM : Pr.MarksAt hσ p q)
    {σ' : S' ⟶ G'.E} (hσ' : σ' ≫ G'.π = 𝟙 S') (hcomm : σ' ≫ t = f ≫ σ)
    {V' : S'.affineOpens} (hV' : V'.1 ≤ f ⁻¹ᵁ V.1) :
    (Pr.transport f t hsq hz hV').MarksAt hσ'
      (sectionsMapLE f hV' p) (sectionsMapLE f hV' q) := by
  obtain ⟨h, hMeq⟩ := hM
  letI : Algebra Γ(S, V.1) Γ(S', V'.1) := (sectionsMapLE f hV').toAlgebra
  have h' : ((Pr.transport f t hsq hz hV').W).toAffine.Equation
      (sectionsMapLE f hV' p) (sectionsMapLE f hV' q) :=
    WeierstrassCurve.Affine.Equation.map (sectionsMapLE f hV') h
  refine ⟨h', ?_⟩
  refine (transport_isPullback_model f hV' Pr).hom_ext ?_ ?_
  · -- the base-change leg: reduce to `hMeq` via `hcomm` + `resLE`/`isoSpec` naturality
    rw [Category.assoc]
    rw [show (Pr.transport f t hsq hz hV').e.hom ≫
        projModelBaseChange (sectionsMapLE f hV') Pr.W =
      transportTheta f t hsq hV' ≫ Pr.e.hom from
      transport_e_baseChange f t hsq hz Pr hV']
    rw [show projModelAffineSection ((Pr.transport f t hsq hz hV').W)
        (sectionsMapLE f hV' p) (sectionsMapLE f hV' q) h' ≫
        projModelBaseChange (sectionsMapLE f hV') Pr.W =
      Spec.map (CommRingCat.ofHom (sectionsMapLE f hV')) ≫
        projModelAffineSection Pr.W p q h from
      projModelAffineSection_baseChange Pr.W p q h h']
    rw [show (V'.2.isoSpec.inv ≫ sectionLift G' hσ' V') ≫
          transportTheta f t hsq hV' ≫ Pr.e.hom =
        V'.2.isoSpec.inv ≫ (sectionLift G' hσ' V' ≫
          transportTheta f t hsq hV') ≫ Pr.e.hom by
      simp only [Category.assoc]]
    rw [show sectionLift G' hσ' V' ≫ transportTheta f t hsq hV' =
        f.resLE V.1 V'.1 hV' ≫ sectionLift G hσ V from ?_]
    · rw [show V'.2.isoSpec.inv ≫ (f.resLE V.1 V'.1 hV' ≫ sectionLift G hσ V) ≫
            Pr.e.hom =
          (V'.2.isoSpec.inv ≫ f.resLE V.1 V'.1 hV' ≫ V.2.isoSpec.hom) ≫
            (V.2.isoSpec.inv ≫ sectionLift G hσ V) ≫ Pr.e.hom by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]]
      rw [hMeq, resLE_isoSpec_naturality f hV', Iso.inv_hom_id_assoc]
    · -- the two lifts agree (compare both pullback legs; `hcomm` enters `fst`)
      unfold sectionLift transportTheta
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
          Category.assoc, hcomm, ← Category.assoc, ← Scheme.Hom.resLE_comp_ι f hV',
          Category.assoc, Category.assoc, pullback.lift_fst]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
          Category.id_comp, Category.assoc, pullback.lift_snd, Category.comp_id]
  · -- the `π` leg: both sides are the identity on `Spec Γ(V')`
    rw [Category.assoc]
    rw [show (Pr.transport f t hsq hz hV').e.hom ≫
        projModelπ (Pr.W.map (sectionsMapLE f hV')) =
      pullback.snd G'.π V'.1.ι ≫ V'.2.isoSpec.hom from
      (Pr.transport f t hsq hz hV').compat_π]
    rw [show projModelAffineSection ((Pr.transport f t hsq hz hV').W)
        (sectionsMapLE f hV' p) (sectionsMapLE f hV' q) h' ≫
        projModelπ (Pr.W.map (sectionsMapLE f hV')) =
      𝟙 _ from projModelAffineSection_projModelπ _ _ _ _]
    rw [show (V'.2.isoSpec.inv ≫ sectionLift G' hσ' V') ≫
          pullback.snd G'.π V'.1.ι ≫ V'.2.isoSpec.hom =
        V'.2.isoSpec.inv ≫ (sectionLift G' hσ' V' ≫
          pullback.snd G'.π V'.1.ι) ≫ V'.2.isoSpec.hom by
      simp only [Category.assoc]]
    unfold sectionLift
    rw [pullback.lift_snd, Category.id_comp, Iso.inv_hom_id]
    exact rfl

set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14-CLS-2)** Markings restrict: the identity-square case of
`MarksAt.transport`, with `sectionsMapLE (𝟙 S) = resLE`. -/
theorem MarksAt.restrict {V : S.affineOpens} {Pr : LocalPresentation G V}
    {σ : S ⟶ G.E} {hσ : σ ≫ G.π = 𝟙 S} {p q : Γ(S, V.1)}
    (hM : Pr.MarksAt hσ p q) {V' : S.affineOpens} (h : V'.1 ≤ V.1) :
    (Pr.restrict h).MarksAt hσ
      (Scheme.resLE h p) (Scheme.resLE h q) := by
  have hres := MarksAt.transport (𝟙 S) (𝟙 G.E)
    (IsPullback.of_horiz_isIso ⟨by simp⟩) (by simp) hM hσ
    (by rw [Category.comp_id, Category.id_comp])
    (V' := V') (by simpa using h)
  have hval : ∀ r : Γ(S, V.1),
      sectionsMapLE (𝟙 S) (V' := V'.1) (by simpa using h) r = Scheme.resLE h r :=
    fun r => congrArg (fun (g : Γ(S, V.1) →+* Γ(S, V'.1)) => g r)
      (sectionsMapLE_id (by simpa using h))
  rw [hval p, hval q] at hres
  exact hres

/-- Marking only depends on the section (the section-property is proof-irrelevant). -/
theorem MarksAt.congr_section {V : S.affineOpens} {Pr : LocalPresentation G V}
    {σ₁ σ₂ : S ⟶ G.E} (hs : σ₁ = σ₂) {h₁ : σ₁ ≫ G.π = 𝟙 S}
    (h₂ : σ₂ ≫ G.π = 𝟙 S) {p q : Γ(S, V.1)} (hM : Pr.MarksAt h₁ p q) :
    Pr.MarksAt h₂ p q := by
  subst hs
  exact hM

end LocalPresentation

open LocalPresentation in
/-- **(T-E14b, the corrected KM 4.6.2 `δ`-condition ★)** A **Legendre datum** on
`E/S`: a naive full level-`2` structure `(P, Q)` together with an `ω`-basis `b` such
that, locally on `S`, there is a `b`-adapted chart presentation whose curve IS a
Legendre curve `y² = x(x−1)(x−λ)`, marking `P` at `x = 0` and `Q` at `x = 1`. KM
4.6.2 verbatim: *"pairs `(φ₂, ω) … for which the adapted `x` satisfies
`x(P₂) = 0, x(Q₂) = 1`"*. Stated in local-existence form; the witness presentation is
unique by `transVC_of_isAdapted_charNeTwo` + `legendreCurve_vc_marked`. -/
def IsLegendreDatum {R : CommRingCat.{u}} (X : EllObj R)
    (L : X.curve.FullLevelPt 2)
    (b : OmegaBasis X.curve.toEllipticCurveGeom) : Prop :=
  ∀ s : X.base, ∃ (V : X.base.affineOpens) (_ : s ∈ V.1)
    (Pr : LocalPresentation X.curve.toEllipticCurveGeom V)
    (lam : Γ(X.base, V.1)),
      Pr.IsAdapted b ∧ Pr.W = legendreCurve lam ∧
      Pr.MarksAt L.1.1.2 0 0 ∧ Pr.MarksAt L.1.2.2 1 0

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14b ★)** The Legendre condition is functorial: it pulls back along
`Ell/R`-morphisms (level datum by `EllHom.pullSection`, `ω`-datum by
`omegaBasisMap`, witness presentations by `LocalPresentation.transport`). -/
theorem IsLegendreDatum.map {R : CommRingCat.{u}} {X' X : EllObj R} (φ : X' ⟶ X)
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (L' : X'.curve.FullLevelPt 2)
    (hL'P : L'.1.1.1 = (EllHom.pullSection R φ L.1.1).1)
    (hL'Q : L'.1.2.1 = (EllHom.pullSection R φ L.1.2).1) :
    IsLegendreDatum X' L' (omegaBasisMap φ b) := by
  intro s'
  obtain ⟨V, hsV, Pr, lam, hAd, hW, hP, hQ⟩ := hD (φ.baseHom.base s')
  obtain ⟨V'₀, hV'aff, hs'V', hV'sub⟩ := exists_isAffineOpen_mem_and_subset
    (show s' ∈ (φ.baseHom ⁻¹ᵁ V.1 : X'.base.Opens) from hsV)
  have hle : (⟨V'₀, hV'aff⟩ : X'.base.affineOpens).1 ≤ φ.baseHom ⁻¹ᵁ V.1 := hV'sub
  refine ⟨⟨V'₀, hV'aff⟩, hs'V',
    Pr.transport φ.baseHom φ.top φ.isPullback φ.zero_w hle,
    sectionsMapLE φ.baseHom hle lam, ?_, ?_, ?_, ?_⟩
  · exact IsAdapted.transport φ hAd hle
  · rw [transport_W, hW, legendreCurve_map]
  · have h0 := MarksAt.transport φ.baseHom φ.top φ.isPullback φ.zero_w hP
      (EllHom.pullSection R φ L.1.1).2
      (φ.isPullback.lift_fst _ _ _) hle
    rw [map_zero] at h0
    exact MarksAt.congr_section hL'P.symm L'.1.1.2 h0
  · have h1 := MarksAt.transport φ.baseHom φ.top φ.isPullback φ.zero_w hQ
      (EllHom.pullSection R φ L.1.2).2
      (φ.isPullback.lift_fst _ _ _) hle
    rw [map_one, map_zero] at h1
    exact MarksAt.congr_section hL'Q.symm L'.1.2.2 h1

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(T-E14, the corrected `δ` of KM 4.6.2 ★★)** The Legendre moduli problem: the
subfunctor of the ambient `Γ(2)-naive × ω` product cut out by the marking condition
*"the adapted `x` satisfies `x(P₂) = 0, x(Q₂) = 1`"*. This — not the ambient
product — is the `δ` whose engine axioms feed KM 4.7.0 over `ℤ[1/2]`. -/
noncomputable def legendreDeltaProblem (R : CommRingCat.{u}) : ModuliProblem R where
  obj X := { x : (gammaFullNaiveProblem R 2).obj X × (omegaProblem R).obj X //
    IsLegendreDatum X.unop x.1 x.2 }
  map φ := ↾fun x => ⟨⟨(gammaFullNaiveProblem R 2).map φ x.1.1,
    (omegaProblem R).map φ x.1.2⟩,
    IsLegendreDatum.map φ.unop x.2 _ rfl rfl⟩
  map_id X := by
    ext x
    · exact FunctorToTypes.map_id_apply (gammaFullNaiveProblem R 2) x.1.1
    · exact FunctorToTypes.map_id_apply (omegaProblem R) x.1.2
  map_comp {X Y Z} φ ψ := by
    ext x
    · exact FunctorToTypes.map_comp_apply (gammaFullNaiveProblem R 2) φ ψ x.1.1
    · exact FunctorToTypes.map_comp_apply (omegaProblem R) φ ψ x.1.2

end ModularCurves

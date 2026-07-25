/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.LevelStructure.CombinationLevel
import ModularCurves.Moduli.LegendreDelta
import ModularCurves.Moduli.LevelLocusNatural
import ModularCurves.Moduli.QuotientProblem

/-!
# Relative representability of the Legendre `δ`: the scale-torsor funnel

The reduction of `legendreDelta_relativelyRepresentable_finiteEtale` (Bootstrap
T-E14-AX2) to its single remaining geometric input: a **finite étale scale-torsor**
`Z₂ → fullLevelLocus 2` whose sections over a level-`2` point classify the ω-bases
completing it to a Legendre datum (the `±ω` pair fixing `u² = x(Q) − x(P)`; rank
`12 = 6 × 2` in total).

The `Γ(2)`-layer is the `N = 2` instance of the E3 template
(`fullLevelLocus`/`fullLevelLocusPointsEquiv`, N-generic, axiom-clean); this file is
pure plumbing: fibre the composite `Z₂ → locus → S` over the locus points
(`sectionsCompSigmaEquiv`, a `subst`-trick fibration) and re-index along the
classifying equivalence (`Equiv.sigmaCongrLeft`/`sigmaCongrRight`).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u v

namespace ModularCurves

open EllipticCurve

/-- Sections of a composite fibre over sections of the second leg. -/
noncomputable def sectionsCompSigmaEquiv {ZS WS TS SS : Scheme.{u}}
    (q : ZS ⟶ WS) (p : WS ⟶ SS) (g : TS ⟶ SS) :
    { h : TS ⟶ ZS // h ≫ (q ≫ p) = g } ≃
      Σ w : { w : TS ⟶ WS // w ≫ p = g }, { s : TS ⟶ ZS // s ≫ q = w.1 } where
  toFun h := ⟨⟨h.1 ≫ q, by rw [Category.assoc]; exact h.2⟩, ⟨h.1, rfl⟩⟩
  invFun ws := ⟨ws.2.1, by rw [← Category.assoc, ws.2.2]; exact ws.1.2⟩
  left_inv h := rfl
  right_inv := by
    rintro ⟨⟨w, hw⟩, ⟨s, hs⟩⟩
    refine Sigma.ext (Subtype.ext hs) ((Subtype.heq_iff_coe_eq ?_).mpr rfl)
    intro x
    show x ≫ q = s ≫ q ↔ x ≫ q = w
    exact ⟨fun h' => h'.trans hs, fun h' => h'.trans hs.symm⟩

/-- Collapse a sigma of subtypes over a pair condition into the subtype of pairs. -/
def sigmaSubtypePairEquiv {α β : Type v} (D : α → β → Prop) :
    (Σ a : α, { b : β // D a b }) ≃ { x : α × β // D x.1 x.2 } where
  toFun ab := ⟨(ab.1, ab.2.1), ab.2.2⟩
  invFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  left_inv ab := rfl
  right_inv x := rfl

variable (R : CommRingCat.{u})

/-- The `NIsInvertible`-form of a unit hypothesis, over the base of an `Ell/R`
object. -/
theorem nIsInvertible_base_of_isUnit {n : ℕ} (hn : IsUnit ((n : ℕ) : R))
    (X : EllObj R) : NIsInvertible X.base n := by
  have h0 : NIsInvertible (Spec R) n := by
    rw [NIsInvertible]
    have := hn.map (Scheme.ΓSpecIso R).inv.hom
    rwa [map_natCast] at this
  exact h0.of_hom X.structMap

/-- **The scale-torsor funnel (T-E14-AX2 reduction).** Suppose that over the `N = 2`
full-level locus of `X.curve` there is a finite étale `Z₂` whose sections over a locus
point `w` (lying over `g : T ⟶ X.base`) classify the ω-bases completing the
corresponding level structure to a Legendre datum. Then the Legendre `δ` is relatively
representable by the finite étale composite `Z₂ → locus → X.base`. -/
theorem legendreDelta_relRep_finiteEtale_of_scaleTorsor
    (X : EllObj R) (h2 : NIsInvertible X.base 2)
    (Z₂ : Scheme.{u}) (q : Z₂ ⟶ X.curve.fullLevelLocus 2 h2)
    (hqF : IsFinite q) (hqE : Etale q)
    (spec : ∀ {T : Scheme.{u}} (g : T ⟶ X.base)
      (w : { w : T ⟶ X.curve.fullLevelLocus 2 h2 //
        w ≫ X.curve.fullLevelLocusπ 2 h2 = g }),
      { s : T ⟶ Z₂ // s ≫ q = w.1 } ≃
        { b : OmegaBasis (X.pullbackAlong g).curve.toEllipticCurveGeom //
          IsLegendreDatum (X.pullbackAlong g)
            (X.curve.fullLevelLocusPointsEquiv 2 h2 g w) b }) :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ X.base), IsFinite f ∧ Etale f ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ X.base), Nonempty
        ({ h : T ⟶ Z // h ≫ f = g } ≃
          (legendreDeltaProblem R).obj (Opposite.op (X.pullbackAlong g))) := by
  refine ⟨Z₂, q ≫ X.curve.fullLevelLocusπ 2 h2,
    MorphismProperty.comp_mem _ _ _ hqF (X.curve.fullLevelLocusπ_isFinite 2 h2),
    MorphismProperty.comp_mem _ _ _ hqE (X.curve.fullLevelLocusπ_etale 2 h2),
    fun {T} g => ⟨?_⟩⟩
  refine (sectionsCompSigmaEquiv q (X.curve.fullLevelLocusπ 2 h2) g).trans ?_
  refine (Equiv.sigmaCongrRight (fun w => spec g w)).trans ?_
  exact (Equiv.sigmaCongrLeft (X.curve.fullLevelLocusPointsEquiv 2 h2 g)).trans
    (sigmaSubtypePairEquiv (fun L b => IsLegendreDatum (X.pullbackAlong g) L b))

section NaturalFunnel

variable (X : EllObj R) (h2 : NIsInvertible X.base 2)
  (Z₂ : Scheme.{u}) (q : Z₂ ⟶ X.curve.fullLevelLocus 2 h2)

/-- The classifying family of the funnel, as a standalone definition (elaborating it
inside the `RelRepData` literal overflows `whnf`). -/
noncomputable def legendreFunnelEquiv
    (spec : ∀ {T : Scheme.{u}} (g : T ⟶ X.base)
      (w : { w : T ⟶ X.curve.fullLevelLocus 2 h2 //
        w ≫ X.curve.fullLevelLocusπ 2 h2 = g }),
      { s : T ⟶ Z₂ // s ≫ q = w.1 } ≃
        { b : OmegaBasis (X.pullbackAlong g).curve.toEllipticCurveGeom //
          IsLegendreDatum (X.pullbackAlong g)
            (X.curve.fullLevelLocusPointsEquiv 2 h2 g w) b })
    {T : Scheme.{u}} (g : T ⟶ X.base) :
    { h : T ⟶ Z₂ // h ≫ (q ≫ X.curve.fullLevelLocusπ 2 h2) = g } ≃
      (legendreDeltaProblem R).obj (Opposite.op (X.pullbackAlong g)) :=
  (sectionsCompSigmaEquiv q (X.curve.fullLevelLocusπ 2 h2) g).trans
    ((Equiv.sigmaCongrRight (fun w => spec g w)).trans
      ((Equiv.sigmaCongrLeft (X.curve.fullLevelLocusPointsEquiv 2 h2 g)).trans
        (sigmaSubtypePairEquiv (fun L b => IsLegendreDatum (X.pullbackAlong g) L b))))

/-- **(pinning of the funnel)** The value of `legendreFunnelEquiv` is, on the nose, the
locus dictionary on the level component and `spec` on the `ω` component. -/
theorem legendreFunnelEquiv_apply
    (spec : ∀ {T : Scheme.{u}} (g : T ⟶ X.base)
      (w : { w : T ⟶ X.curve.fullLevelLocus 2 h2 //
        w ≫ X.curve.fullLevelLocusπ 2 h2 = g }),
      { s : T ⟶ Z₂ // s ≫ q = w.1 } ≃
        { b : OmegaBasis (X.pullbackAlong g).curve.toEllipticCurveGeom //
          IsLegendreDatum (X.pullbackAlong g)
            (X.curve.fullLevelLocusPointsEquiv 2 h2 g w) b })
    {T : Scheme.{u}} (g : T ⟶ X.base)
    (h : { h : T ⟶ Z₂ // h ≫ (q ≫ X.curve.fullLevelLocusπ 2 h2) = g }) :
    (legendreFunnelEquiv R X h2 Z₂ q spec g h).1 =
      (X.curve.fullLevelLocusPointsEquiv 2 h2 g
          ⟨h.1 ≫ q, by rw [Category.assoc]; exact h.2⟩,
        (spec g ⟨h.1 ≫ q, by rw [Category.assoc]; exact h.2⟩ ⟨h.1, rfl⟩).1) :=
  rfl

end NaturalFunnel

end ModularCurves

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ModularCurve.RhoSmooth

/-!
# `T`-points of the representing curve as pairs `(E, α)`

**[T-YR-7a–d]** For a representing object `X` of `rhoProblem D`, the `T`-points of
`X.base` over `ℚ` are exactly the pairs `(E, α)` — an elliptic curve over `T` with a
ρ-level structure — modulo pointed isomorphisms carrying the structure across. This
is the `Quot`-points clause of `RepresentsYRho` (in the DEF-17 corrected form).
-/

noncomputable section

namespace ModularCurves

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

variable {N : ℕ} [NeZero N]

/-- The tautological cartesian projection onto `X` from the pullback of its curve,
with the base object's structure map presented as `sT`. -/
def pullbackπOf {X : EllObj (CommRingCat.of ℚ)} {T : Scheme.{0}}
    {sT : T ⟶ Spec (CommRingCat.of ℚ)} {h : T ⟶ X.base}
    (p : h ≫ X.structMap = sT) :
    (⟨T, sT, X.curve.baseChange h⟩ : EllObj (CommRingCat.of ℚ)) ⟶ X where
  baseHom := h
  base_w := p
  top := pullback.fst X.curve.π h
  isPullback := IsPullback.of_hasPullback X.curve.π h
  zero_w := pullback.lift_fst _ _ _

open scoped FintypeCatDiscrete in
/-- **[T-YR-7a]** A `T`-point of the representing curve over `ℚ` yields a pair
`(E, α)`: the pullback of the universal curve with its ρ-level structure. -/
def pointToPair (D : GaloisRepData N) {X : EllObj (CommRingCat.of ℚ)}
    (r : (rhoProblem D).RepresentableBy X) {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ))
    (h : { h : T ⟶ X.base // h ≫ X.structMap = sT }) :
    Σ E : EllipticCurve T, RhoLevelStructure D sT E :=
  ⟨X.curve.baseChange h.1, r.homEquiv (pullbackπOf h.2)⟩

open scoped FintypeCatDiscrete in
/-- **[T-YR-7b]** A pair `(E, α)` over `T` yields a `T`-point of the representing
curve over `ℚ`: the base component of its classifying morphism. -/
def pairToPoint (D : GaloisRepData N) {X : EllObj (CommRingCat.of ℚ)}
    (r : (rhoProblem D).RepresentableBy X) {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ))
    (a : Σ E : EllipticCurve T, RhoLevelStructure D sT E) :
    { h : T ⟶ X.base // h ≫ X.structMap = sT } :=
  ⟨(r.homEquiv.symm (show (rhoProblem D).obj (op ⟨T, sT, a.1⟩) from a.2)).baseHom,
    (r.homEquiv.symm (show (rhoProblem D).obj (op ⟨T, sT, a.1⟩) from a.2)).base_w⟩

open scoped FintypeCatDiscrete in
/-- **[T-YR-7d, roundtrip 1]** Classifying the pair attached to a point returns the
point. -/
theorem pairToPoint_pointToPair (D : GaloisRepData N) {X : EllObj (CommRingCat.of ℚ)}
    (r : (rhoProblem D).RepresentableBy X) {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ))
    (h : { h : T ⟶ X.base // h ≫ X.structMap = sT }) :
    pairToPoint D r sT (pointToPair D r sT h) = h := by
  apply Subtype.ext
  show (r.homEquiv.symm (r.homEquiv (pullbackπOf h.2))).baseHom = h.1
  rw [Equiv.symm_apply_apply]
  rfl

open scoped FintypeCatDiscrete in
/-- **[T-YR-7c]** The classifying point only depends on the pair up to a pointed
isomorphism carrying the level structure: the DEF-17 relation is respected. -/
theorem pairToPoint_congr (D : GaloisRepData N) {X : EllObj (CommRingCat.of ℚ)}
    (r : (rhoProblem D).RepresentableBy X) {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ))
    (a b : Σ E : EllipticCurve T, RhoLevelStructure D sT E)
    (f : a.1 ≅ b.1) (hf : a.2 = RhoLevelStructure.pull D (ellHomOfCurveIso sT f) b.2) :
    pairToPoint D r sT a = pairToPoint D r sT b := by
  apply Subtype.ext
  show (r.homEquiv.symm (show (rhoProblem D).obj (op ⟨T, sT, a.1⟩) from a.2)).baseHom =
    (r.homEquiv.symm (show (rhoProblem D).obj (op ⟨T, sT, b.1⟩) from b.2)).baseHom
  have hmap : (show (rhoProblem D).obj (op ⟨T, sT, a.1⟩) from a.2) =
      (rhoProblem D).map (ellHomOfCurveIso sT f).op
        (show (rhoProblem D).obj (op ⟨T, sT, b.1⟩) from b.2) := hf
  rw [hmap, ← r.comp_homEquiv_symm]
  show (𝟙 T) ≫ _ = _
  rw [Category.id_comp]

/-- The comparison isomorphism of curves attached to an `Ell/ℚ`-morphism out of
`⟨T, sT, E⟩`: its cartesian square identifies `E` with the pullback of the target's
curve. -/
def curveIsoOfPullback {T : Scheme.{0}} {sT : T ⟶ Spec (CommRingCat.of ℚ)}
    {E : EllipticCurve T} {X : EllObj (CommRingCat.of ℚ)}
    (u : (⟨T, sT, E⟩ : EllObj (CommRingCat.of ℚ)) ⟶ X) :
    E ≅ X.curve.baseChange u.baseHom where
  hom :=
    { hom := u.isPullback.isoPullback.hom
      over_w := u.isPullback.isoPullback_hom_snd
      zero_w := by
        apply pullback.hom_ext
        · show (E.zero ≫ u.isPullback.isoPullback.hom) ≫ pullback.fst X.curve.π u.baseHom
            = _
          rw [Category.assoc, u.isPullback.isoPullback_hom_fst]
          show E.zero ≫ u.top = pullback.lift (u.baseHom ≫ X.curve.zero) (𝟙 T) _ ≫
            pullback.fst X.curve.π u.baseHom
          rw [pullback.lift_fst]
          exact u.zero_w
        · show (E.zero ≫ u.isPullback.isoPullback.hom) ≫ pullback.snd X.curve.π u.baseHom
            = _
          rw [Category.assoc, u.isPullback.isoPullback_hom_snd]
          show E.zero ≫ E.π = pullback.lift (u.baseHom ≫ X.curve.zero) (𝟙 T) _ ≫
            pullback.snd X.curve.π u.baseHom
          rw [pullback.lift_snd, E.zero_π] }
  inv :=
    { hom := u.isPullback.isoPullback.inv
      over_w := by
        show u.isPullback.isoPullback.inv ≫ E.π = pullback.snd X.curve.π u.baseHom
        rw [Iso.inv_comp_eq]
        exact u.isPullback.isoPullback_hom_snd.symm
      zero_w := by
        have h : E.zero ≫ u.isPullback.isoPullback.hom =
            (X.curve.baseChange u.baseHom).zero := by
          apply pullback.hom_ext
          · show (E.zero ≫ u.isPullback.isoPullback.hom) ≫
              pullback.fst X.curve.π u.baseHom = _
            rw [Category.assoc, u.isPullback.isoPullback_hom_fst]
            show E.zero ≫ u.top = pullback.lift (u.baseHom ≫ X.curve.zero) (𝟙 T) _ ≫
              pullback.fst X.curve.π u.baseHom
            rw [pullback.lift_fst]
            exact u.zero_w
          · show (E.zero ≫ u.isPullback.isoPullback.hom) ≫
              pullback.snd X.curve.π u.baseHom = _
            rw [Category.assoc, u.isPullback.isoPullback_hom_snd]
            show E.zero ≫ E.π = pullback.lift (u.baseHom ≫ X.curve.zero) (𝟙 T) _ ≫
              pullback.snd X.curve.π u.baseHom
            rw [pullback.lift_snd, E.zero_π]
        rw [Iso.comp_inv_eq]
        exact h.symm }
  hom_inv_id := EllipticCurve.HomOver.ext (Iso.hom_inv_id _)
  inv_hom_id := EllipticCurve.HomOver.ext (Iso.inv_hom_id _)

@[simp] lemma curveIsoOfPullback_hom_hom {T : Scheme.{0}}
    {sT : T ⟶ Spec (CommRingCat.of ℚ)} {E : EllipticCurve T}
    {X : EllObj (CommRingCat.of ℚ)}
    (u : (⟨T, sT, E⟩ : EllObj (CommRingCat.of ℚ)) ⟶ X) :
    (curveIsoOfPullback u).hom.hom = u.isPullback.isoPullback.hom := rfl

open scoped FintypeCatDiscrete in
/-- **[T-YR-7d, roundtrip 2]** The pair attached to the classifying point of `(E, α)`
is related to `(E, α)` by the DEF-17 relation: the cartesian comparison isomorphism
carries the pulled-back universal structure to `α`. -/
theorem rel_pointToPair_pairToPoint (D : GaloisRepData N)
    {X : EllObj (CommRingCat.of ℚ)} (r : (rhoProblem D).RepresentableBy X)
    {T : Scheme.{0}} (sT : T ⟶ Spec (CommRingCat.of ℚ))
    (a : Σ E : EllipticCurve T, RhoLevelStructure D sT E) :
    ∃ f : a.1 ≅ (pointToPair D r sT (pairToPoint D r sT a)).1,
      a.2 = RhoLevelStructure.pull D (ellHomOfCurveIso sT f)
        (pointToPair D r sT (pairToPoint D r sT a)).2 := by
  obtain ⟨E, α⟩ := a
  set u := r.homEquiv.symm (show (rhoProblem D).obj (op ⟨T, sT, E⟩) from α) with hu
  refine ⟨curveIsoOfPullback u, ?_⟩
  show α = (rhoProblem D).map (ellHomOfCurveIso sT (curveIsoOfPullback u)).op
    (r.homEquiv (pullbackπOf (pairToPoint D r sT ⟨E, α⟩).2))
  rw [← r.homEquiv_comp]
  have hcomp : ellHomOfCurveIso sT (curveIsoOfPullback u) ≫
      pullbackπOf (pairToPoint D r sT ⟨E, α⟩).2 = u := by
    refine EllHom.ext (Category.id_comp _) ?_
    show u.isPullback.isoPullback.hom ≫ pullback.fst X.curve.π u.baseHom = u.top
    exact u.isPullback.isoPullback_hom_fst
  rw [hcomp, hu, Equiv.apply_symm_apply]

end ModularCurves

end

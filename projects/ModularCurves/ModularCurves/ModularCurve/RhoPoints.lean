/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ModularCurve.RhoSmooth
import ModularCurves.Moduli.LegendreTorsor

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

open scoped FintypeCatDiscrete in
/-- **[T-YR-7, clause 3]** The `T`-points of the representing curve over `ℚ` are the
pairs `(E, α)` modulo pointed isomorphisms carrying the level structure — the
`Quot`-points clause of `RepresentsYRho` (DEF-17 form). -/
def pointsEquivQuot (D : GaloisRepData N) {X : EllObj (CommRingCat.of ℚ)}
    (r : (rhoProblem D).RepresentableBy X) {T : Scheme.{0}}
    (sT : T ⟶ Spec (CommRingCat.of ℚ)) :
    { h : T ⟶ X.base // h ≫ X.structMap = sT } ≃
      Quot (fun (a b : Σ E : EllipticCurve T, RhoLevelStructure D sT E) =>
        ∃ f : a.1 ≅ b.1,
          a.2 = RhoLevelStructure.pull D (ellHomOfCurveIso sT f) b.2) where
  toFun h := Quot.mk _ (pointToPair D r sT h)
  invFun := Quot.lift (pairToPoint D r sT)
    (fun a b hab => pairToPoint_congr D r sT a b hab.choose hab.choose_spec)
  left_inv h := pairToPoint_pointToPair D r sT h
  right_inv := by
    refine Quot.ind fun a => ?_
    show Quot.mk _ (pointToPair D r sT (pairToPoint D r sT a)) = Quot.mk _ a
    exact (Quot.sound (rel_pointToPair_pairToPoint D r sT a)).symm

open scoped FintypeCatDiscrete in
/-- **[T-YR-7 assembly]** A representing object of `rhoProblem D` whose structure map
is smooth of relative dimension one represents the ρ-moduli problem in the sense of
`RepresentsYRho`. (Affineness is automatic; the points clause is `pointsEquivQuot`.) -/
theorem representsYRho_of_smooth (D : GaloisRepData N) [Fact (1 < N)]
    (hN : 3 ≤ (N : ℤ)) {X : EllObj (CommRingCat.of ℚ)}
    (r : (rhoProblem D).RepresentableBy X)
    (hsm : SmoothOfRelativeDimension 1 X.structMap) :
    RepresentsYRho D X.base X.structMap :=
  ⟨hsm, rhoProblem_isAffineHom_structMap D hN r,
    fun T sT => ⟨pointsEquivQuot D r sT⟩⟩

open scoped FintypeCatDiscrete in
/-- **[T-YR-7 assembly, `∃`-form]** `yRho_representable` modulo the smoothness leaf
(T-YR-6-APP): once some representing object has a smooth-of-relative-dimension-one
structure map, the twisted modular curve exists. -/
theorem exists_representsYRho_of_exists_smooth (D : GaloisRepData N) [Fact (1 < N)]
    (hN : 3 ≤ (N : ℤ))
    (hsm : ∃ (X : EllObj (CommRingCat.of ℚ)) (_ : (rhoProblem D).RepresentableBy X),
      SmoothOfRelativeDimension 1 X.structMap) :
    ∃ (Y : Scheme.{0}) (sY : Y ⟶ Spec (CommRingCat.of ℚ)), RepresentsYRho D Y sY := by
  obtain ⟨X, r, h⟩ := hsm
  exact ⟨X.base, X.structMap, representsYRho_of_smooth D hN r h⟩

open scoped FintypeCatDiscrete in
/-- **[T-YR-7, `∃`-form modulo the Legendre-cover surjectivity]** Assembling the three
clauses: with the smoothness input supplied, the twisted modular curve exists. -/
theorem exists_representsYRho_of_legendre_cover (D : GaloisRepData N) [Fact (1 < N)]
    (hN : 3 ≤ (N : ℤ)) (hR : IsUnit (2 : CommRingCat.of ℚ))
    {X : EllObj (CommRingCat.of ℚ)} (r : (rhoProblem D).RepresentableBy X)
    (rL : (legendreDeltaProblem (CommRingCat.of ℚ)).RepresentableBy
      (universalLegendreObj (CommRingCat.of ℚ) hR))
    (dL : ModuliProblem.RelRepData (legendreDeltaProblem (CommRingCat.of ℚ)) X)
    (hLfin : IsFinite dL.f) (hLet : Etale dL.f) (hLsurj : Surjective dL.f)
    (dρ : ModuliProblem.RelRepData (rhoProblem D)
      (universalLegendreObj (CommRingCat.of ℚ) hR))
    (hρfin : IsFinite dρ.f) (hρet : Etale dρ.f) :
    ∃ (Y : Scheme.{0}) (sY : Y ⟶ Spec (CommRingCat.of ℚ)), RepresentsYRho D Y sY :=
  ⟨X.base, X.structMap,
    representsYRho_of_smooth D hN r
      (rhoProblem_smoothOfRelativeDimension_one D hN hR r rL dL hLfin hLet hLsurj
        dρ hρfin hρet)⟩

open scoped FintypeCatDiscrete in
/-- **[T-YR-7 = `yRho_representable`]** The twisted modular curve exists: for `N ≥ 3`
there is a smooth affine `ℚ`-curve representing the ρ-level moduli problem in the sense
of `RepresentsYRho` (DEF-17 form).

Inputs: representability and affineness of the representing base (T-YR-5, T-YR-6-APP i),
the points dictionary (T-YR-7a–d), and the smoothness leaf (T-YR-6 descent machinery
applied at the Legendre cover, whose finiteness, étaleness and surjectivity come from the
Legendre torsor package). -/
theorem exists_representsYRho (D : GaloisRepData N) [Fact (1 < N)] (hN : 3 ≤ (N : ℤ))
    (hR : IsUnit (2 : CommRingCat.of ℚ))
    (hL : (universalLegendreObj (CommRingCat.of ℚ) hR).curve.IsNaiveFullLevel 2
      (universalLegendreP (CommRingCat.of ℚ) hR)
      (universalLegendreQ (CommRingCat.of ℚ) hR)) :
    ∃ (Y : Scheme.{0}) (sY : Y ⟶ Spec (CommRingCat.of ℚ)), RepresentsYRho D Y sY := by
  obtain ⟨X, -, ⟨r⟩⟩ := rhoProblem_exists_representableBy_isAffine D hN
  obtain ⟨dρ, hρfin, hρet⟩ := rhoProblem_exists_relRepData_finiteEtale D
    (universalLegendreObj (CommRingCat.of ℚ) hR)
  refine exists_representsYRho_of_legendre_cover D hN hR r
    (legendreDeltaRepresentableBy (CommRingCat.of ℚ) hR hL)
    (legendreDeltaGEquiv (CommRingCat.of ℚ) hR X).toRelRepData
    (legendreDeltaGEquiv (CommRingCat.of ℚ) hR X).finite
    (legendreDeltaGEquiv (CommRingCat.of ℚ) hR X).etale
    (legendreDelta_surjective_of (legendreDeltaGEquiv (CommRingCat.of ℚ) hR X))
    dρ hρfin hρet

end ModularCurves

end

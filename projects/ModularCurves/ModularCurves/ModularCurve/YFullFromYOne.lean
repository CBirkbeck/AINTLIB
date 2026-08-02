/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.GroupScheme.NaiveGammaOneLocus
import ModularCurves.ModularCurve.YFullToYOne
import ModularCurves.Moduli.QuotientProblem
import ModularCurves.LevelStructure.NaiveGammaOneLevel

/-!
# The candidate `Y(N)` built over `Y₁(N)` (WP-D2c)

`YFull.exists_representing_smooth_affine` asks for **some** object representing the naive
full level-`N` problem whose structure morphism is smooth and affine. Since
`YFull.smooth_affine_of_representableBy` is generic in the moduli problem, exhibiting one
such object settles it for all of them.

The object to exhibit is the universal curve over `Y₁(N)` pulled back to the full-level
locus:

  `X₀ := X₁.pullbackAlong (X₁.curve.fullLevelLocusπ N h)`,

where `X₁` represents `gammaOneNaiveProblem` and is already known smooth and affine
(`gammaOneNaive_representable`, axiom-verified).

This file proves the **free half** (WP-D2c-2): `X₀.structMap` is smooth and affine, because
it factors as a finite étale morphism followed by a smooth affine one. Nothing here needs
new mathematics — `Etale ⟹ Smooth` is an instance, and `Smooth`, `IsAffineHom` and
`IsFinite` all compose.

What remains (WP-D2c-3) is that `X₀` *represents* the full-level problem; the functorial
half of that is `yFullToYOneFibreEquiv` (WP-D2b) and the relative half is
`fullLevelLocusPointsEquiv`.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace ModularCurves

variable {R : CommRingCat.{u}}

/-- **(WP-D2c-1, corrected)** The candidate representing object for the naive full level-`N`
problem: the universal curve over a `Γ₁(N)`-object, pulled back to the **completion locus**
of the universal `Γ₁`-section.

The earlier version used the whole full-level locus; that is wrong — by
`ModuliProblem.simulRepresentableBy` it represents `Γ(N) × Γ₁(N)` with the two structures
unrelated. Cutting down to the completions of the given section is exactly the missing
compatibility. -/
noncomputable def yFullCandidate (N : ℕ) [NeZero N] (X₁ : EllObj R)
    (h : NIsInvertible X₁.base N) (P : X₁.base ⟶ X₁.curve.torsion N) : EllObj R :=
  X₁.pullbackAlong (X₁.curve.completionLocusπ N h P)

@[simp] theorem yFullCandidate_base (N : ℕ) [NeZero N] (X₁ : EllObj R)
    (h : NIsInvertible X₁.base N) (P : X₁.base ⟶ X₁.curve.torsion N) :
    (yFullCandidate N X₁ h P).base = X₁.curve.completionLocus N h P := rfl

@[simp] theorem yFullCandidate_structMap (N : ℕ) [NeZero N] (X₁ : EllObj R)
    (h : NIsInvertible X₁.base N) (P : X₁.base ⟶ X₁.curve.torsion N) :
    (yFullCandidate N X₁ h P).structMap =
      X₁.curve.completionLocusπ N h P ≫ X₁.structMap := rfl

/-- **(WP-D2c-2)** The candidate's structure morphism is smooth: it is a finite étale
morphism followed by a smooth one. -/
theorem yFullCandidate_structMap_smooth (N : ℕ) [NeZero N] (X₁ : EllObj R)
    (h : NIsInvertible X₁.base N) (P : X₁.base ⟶ X₁.curve.torsion N)
    (hsm : Smooth X₁.structMap) :
    Smooth (yFullCandidate N X₁ h P).structMap := by
  haveI : Etale (X₁.curve.completionLocusπ N h P) := X₁.curve.completionLocusπ_etale N h P
  haveI : Smooth (X₁.curve.completionLocusπ N h P) := inferInstance
  haveI := hsm
  rw [yFullCandidate_structMap]
  exact MorphismProperty.comp_mem _ _ _ inferInstance hsm

/-- **(WP-D2c-2)** The candidate's structure morphism is affine: it is a finite morphism
followed by an affine one. -/
theorem yFullCandidate_structMap_isAffineHom (N : ℕ) [NeZero N] (X₁ : EllObj R)
    (h : NIsInvertible X₁.base N) (P : X₁.base ⟶ X₁.curve.torsion N)
    [IsAffineHom X₁.structMap] :
    IsAffineHom (yFullCandidate N X₁ h P).structMap := by
  haveI : IsFinite (X₁.curve.completionLocusπ N h P) :=
    X₁.curve.completionLocusπ_isFinite N h P
  haveI hfa : IsAffineHom (X₁.curve.completionLocusπ N h P) := inferInstance
  rw [yFullCandidate_structMap]
  -- the composition instance does not fire through the `abbrev`, so inline its proof
  refine ⟨fun U hU => ?_⟩
  haveI := hfa
  exact (hU.preimage X₁.structMap).preimage (X₁.curve.completionLocusπ N h P)

/-- **(WP-D2c-2)** Both at once — the shape `smooth_affine_of_representableBy` consumes. -/
theorem yFullCandidate_smooth_affine (N : ℕ) [NeZero N] (X₁ : EllObj R)
    (h : NIsInvertible X₁.base N) (P : X₁.base ⟶ X₁.curve.torsion N)
    (hsm : Smooth X₁.structMap) (ha : IsAffineHom X₁.structMap) :
    Smooth (yFullCandidate N X₁ h P).structMap ∧
      IsAffineHom (yFullCandidate N X₁ h P).structMap :=
  haveI := ha
  ⟨yFullCandidate_structMap_smooth N X₁ h P hsm,
    yFullCandidate_structMap_isAffineHom N X₁ h P⟩

/-! ### The per-`u` fibre (WP-D2c-3, step 2–3)

For a fixed `u : Y ⟶ X₁`, the lifts of `u.baseHom` through `completionLocusπ` are the naive
full level structures on `Y` whose first member is the pullback of `P`. This is
`completionLocusClassifies` transported along `isoPullbackAlong u`. -/

/-- Transport of the full-level problem along the canonical iso `Y ≅ X₁.pullbackAlong
u.baseHom`. -/
noncomputable def transportAlongIso (N : ℕ) [NeZero N] {X₁ Y : EllObj R} (u : Y ⟶ X₁) :
    (gammaFullNaiveProblem R N).obj (Opposite.op (X₁.pullbackAlong u.baseHom)) ≃
      (gammaFullNaiveProblem R N).obj (Opposite.op Y) :=
  ((gammaFullNaiveProblem R N).mapIso (EllObj.isoPullbackAlong u).op).toEquiv

/-- **(WP-D2c-3, per-`u` fibre)** The lifts of `u.baseHom` through `completionLocusπ`
correspond to the naive full level structures on `Y` whose first member is the transported
pullback of `P`. -/
noncomputable def completionFibreEquiv (N : ℕ) [NeZero N] (X₁ : EllObj R)
    (h : NIsInvertible X₁.base N) (P : X₁.base ⟶ X₁.curve.torsion N)
    (hP : P ≫ X₁.curve.torsionπ N = 𝟙 X₁.base) {Y : EllObj R} (u : Y ⟶ X₁) :
    { b : Y.base ⟶ X₁.curve.completionLocus N h P //
        b ≫ X₁.curve.completionLocusπ N h P = u.baseHom } ≃
      { PQ : (gammaFullNaiveProblem R N).obj (Opposite.op Y) //
          ((transportAlongIso N u).symm PQ).1.1 =
            X₁.curve.torsionMapSection N u.baseHom (u.baseHom ≫ P)
              (by rw [Category.assoc, hP, Category.comp_id]) } :=
  (X₁.curve.completionLocusClassifies N h P hP u.baseHom).trans
    ((transportAlongIso N u).subtypeEquiv (fun PQ => by
      simp only [Equiv.symm_apply_apply]
      exact Iff.rfl))

/-- **(WP-D2c-3, glue)** The section attached to "a base map composed with a torsion
section" is the pullback of that section along the tautological projection.

Both sides are sections of `X₁.curve.baseChange g`, so by `baseChange_section_ext` it is
enough to compare their composites with `pullback.fst`: the left is
`(g ≫ pointToTorsion Q) ≫ torsionι = g ≫ Q` by `pointToTorsion_torsionι`, and the right is
`g ≫ Q` by the defining property of `pullSection`. -/
theorem torsionMapSection_comp_eq_pullSection (N : ℕ) [NeZero N] (X₁ : EllObj R)
    {T : Scheme.{u}} (g : T ⟶ X₁.base) (Q : X₁.curve.Section)
    (hQ : (Q : X₁.base ⟶ X₁.curve.E) ≫ X₁.curve.mulByHom N = 𝟙 X₁.base ≫ X₁.curve.zero)
    (hg : (g ≫ X₁.curve.pointToTorsion Q hQ) ≫ X₁.curve.torsionπ N = g) :
    X₁.curve.torsionMapSection N g (g ≫ X₁.curve.pointToTorsion Q hQ) hg =
      EllHom.pullSection R (X₁.pullbackAlongπ g) Q := by
  refine X₁.curve.baseChange_section_ext ?_
  have hL : ((X₁.curve.torsionMapSection N g (g ≫ X₁.curve.pointToTorsion Q hQ) hg).1 :
        T ⟶ pullback X₁.curve.π g) ≫ pullback.fst X₁.curve.π g =
      g ≫ (Q : X₁.base ⟶ X₁.curve.E) := by
    rw [X₁.curve.torsionMapSection_fst N g _ hg, Category.assoc,
      X₁.curve.pointToTorsion_torsionι Q hQ]
  have hR : ((EllHom.pullSection R (X₁.pullbackAlongπ g) Q).1 :
        T ⟶ pullback X₁.curve.π g) ≫ pullback.fst X₁.curve.π g =
      g ≫ (Q : X₁.base ⟶ X₁.curve.E) :=
    (X₁.pullbackAlongπ g).isPullback.lift_fst _ _ _
  rw [hL]
  exact hR.symm

/-! ### The collapse (WP-D2c-3, step 4)

The `Σ` over `u : Y ⟶ X₁` is redundant: the fibre condition pins `u`'s `Γ₁`-structure to be
the `Γ₁`-part of the full level structure, and by WP-D1a that part is *determined* by the
structure. Formally this is `Equiv.sigmaFiberEquiv` for the forgetful map. -/

/-- The forgetful map on structures over a fixed `Y`, as a plain function — the fibre map
whose `Σ` collapses. -/
noncomputable def forgetAt (N : ℕ) [NeZero N] (hinv : IsUnit (N : R)) (Y : EllObj R) :
    (gammaFullNaiveProblem R N).obj (Opposite.op Y) →
      (gammaOneNaiveProblem R N).obj (Opposite.op Y) :=
  fun PQ => (gammaFullToGammaOne N hinv).app (Opposite.op Y) PQ

/-- **(WP-D2c-3, step 4)** The collapse: summing the fibres of the forgetful map over all
`Γ₁`-structures recovers the full level structures. This is where WP-D1a is consumed — the
`Γ₁`-part is not extra data. -/
noncomputable def sigmaForgetEquiv (N : ℕ) [NeZero N] (hinv : IsUnit (N : R))
    (Y : EllObj R) :
    (Σ y : (gammaOneNaiveProblem R N).obj (Opposite.op Y),
        { PQ : (gammaFullNaiveProblem R N).obj (Opposite.op Y) //
          forgetAt N hinv Y PQ = y }) ≃
      (gammaFullNaiveProblem R N).obj (Opposite.op Y) :=
  Equiv.sigmaFiberEquiv (forgetAt N hinv Y)

/-- **(WP-D2c-3, step 4)** Reindexed by `rOne`: the `Σ` over morphisms `Y ⟶ X₁` also
collapses. -/
noncomputable def sigmaHomForgetEquiv (N : ℕ) [NeZero N] (hinv : IsUnit (N : R))
    {X₁ : EllObj R} (rOne : (gammaOneNaiveProblem R N).RepresentableBy X₁) (Y : EllObj R) :
    (Σ u : Y ⟶ X₁, { PQ : (gammaFullNaiveProblem R N).obj (Opposite.op Y) //
        forgetAt N hinv Y PQ = rOne.homEquiv u }) ≃
      (gammaFullNaiveProblem R N).obj (Opposite.op Y) :=
  (Equiv.sigmaCongrLeft' (rOne.homEquiv (X := Y))).trans
    ((Equiv.sigmaCongrRight fun _ =>
      Equiv.subtypeEquivRight fun _ => by rw [Equiv.apply_symm_apply]).trans
      (sigmaForgetEquiv N hinv Y))

/-- **(WP-D2c-3, the chain)** The representing equivalence at a fixed `Y`, assembled from
the four steps. The `Σ`-reindexing is `Equiv.subtypeProdEquivSigmaSubtype`; the fibre
conditions are matched by `torsionMapSection_comp_eq_pullSection` together with
`homEquiv_eq_map_universalGammaOne`. -/
noncomputable def yFullCandidateHomEquiv (N : ℕ) [NeZero N] (X₁ : EllObj R)
    (hinv : IsUnit (N : R)) (h : NIsInvertible X₁.base N)
    (P : X₁.base ⟶ X₁.curve.torsion N)
    (hPsec : P ≫ X₁.curve.torsionπ N = 𝟙 X₁.base)
    (rOne : (gammaOneNaiveProblem R N).RepresentableBy X₁)
    (hmatch : ∀ (Y : EllObj R) (u : Y ⟶ X₁)
      (PQ : (gammaFullNaiveProblem R N).obj (Opposite.op Y)),
      (((transportAlongIso N u).symm PQ).1.1 =
          X₁.curve.torsionMapSection N u.baseHom (u.baseHom ≫ P)
            (by rw [Category.assoc, hPsec, Category.comp_id])) ↔
        forgetAt N hinv Y PQ = rOne.homEquiv u)
    (Y : EllObj R) :
    (Y ⟶ yFullCandidate N X₁ h P) ≃
      (gammaFullNaiveProblem R N).obj (Opposite.op Y) :=
  (EllObj.homPullbackAlongEquiv X₁ (X₁.curve.completionLocusπ N h P) Y).trans
    ((Equiv.subtypeProdEquivSigmaSubtype
        (fun (u : Y ⟶ X₁) (b : Y.base ⟶ X₁.curve.completionLocus N h P) =>
          b ≫ X₁.curve.completionLocusπ N h P = u.baseHom)).trans
      ((Equiv.sigmaCongrRight fun u =>
          (completionFibreEquiv N X₁ h P hPsec u).trans
            (Equiv.subtypeEquivRight (hmatch Y u))).trans
        (sigmaHomForgetEquiv N hinv rOne Y)))

/-- Pulling sections back along an isomorphism is injective. -/
theorem pullSection_iso_injective {X Y : EllObj R} (e : X ≅ Y) :
    Function.Injective (EllHom.pullSection R e.hom) := by
  intro A B hab
  have h := congrArg (EllHom.pullSection R e.inv) hab
  rw [← EllHom.pullSection_comp, ← EllHom.pullSection_comp, e.inv_hom_id,
    EllHom.pullSection_id, EllHom.pullSection_id] at h
  exact h

@[simp] theorem transportAlongIso_symm_fst (N : ℕ) [NeZero N] {X₁ Y : EllObj R}
    (u : Y ⟶ X₁) (PQ : (gammaFullNaiveProblem R N).obj (Opposite.op Y)) :
    ((transportAlongIso N u).symm PQ).1.1 =
      EllHom.pullSection R (EllObj.isoPullbackAlong u).inv PQ.1.1 := rfl

/-- **(WP-D2c-3, `hmatch`)** The two fibre conditions agree: "the transported first member
is the section attached to `u.baseHom ≫ P`" says exactly "the `Γ₁`-part of `PQ` is `u`'s
structure".

Both directions are the injectivity of `pullSection` along the iso: pulling back along
`(isoPullbackAlong u).hom` cancels the `inv` on one side and, by
`toPullbackAlong_pullbackAlongπ`, turns the tautological projection into `u` on the
other. -/
theorem fibre_condition_iff (N : ℕ) [NeZero N] (hinv : IsUnit (N : R)) (X₁ : EllObj R)
    (P : X₁.base ⟶ X₁.curve.torsion N)
    (hPsec : P ≫ X₁.curve.torsionπ N = 𝟙 X₁.base)
    (rOne : (gammaOneNaiveProblem R N).RepresentableBy X₁)
    (hP : P = X₁.curve.pointToTorsion (universalGammaOne R N rOne).1
      ((X₁.curve.smul_eq_zero_iff_comp_mulByHom (𝟙 X₁.base) N _).mp
        (universalGammaOne R N rOne).2.1))
    (Y : EllObj R) (u : Y ⟶ X₁)
    (PQ : (gammaFullNaiveProblem R N).obj (Opposite.op Y)) :
    (((transportAlongIso N u).symm PQ).1.1 =
        X₁.curve.torsionMapSection N u.baseHom (u.baseHom ≫ P)
          (by rw [Category.assoc, hPsec, Category.comp_id])) ↔
      forgetAt N hinv Y PQ = rOne.homEquiv u := by
  set e := EllObj.isoPullbackAlong u with he
  -- the right-hand condition, unfolded
  have hRHS : (forgetAt N hinv Y PQ = rOne.homEquiv u) ↔
      PQ.1.1 = EllHom.pullSection R u (universalGammaOne R N rOne).1 := by
    rw [homEquiv_eq_map_universalGammaOne R N rOne u]
    exact ⟨fun hh => congrArg Subtype.val hh, fun hh => Subtype.ext hh⟩
  -- the left-hand condition, with `hP` and the glue lemma
  have hglue : X₁.curve.torsionMapSection N u.baseHom (u.baseHom ≫ P)
        (by rw [Category.assoc, hPsec, Category.comp_id]) =
      EllHom.pullSection R (X₁.pullbackAlongπ u.baseHom)
        (universalGammaOne R N rOne).1 := by
    subst hP
    exact torsionMapSection_comp_eq_pullSection N X₁ u.baseHom _ _ _
  rw [transportAlongIso_symm_fst, hglue, hRHS]
  constructor
  · intro hh
    have := congrArg (EllHom.pullSection R e.hom) hh
    rwa [← EllHom.pullSection_comp, ← EllHom.pullSection_comp, e.hom_inv_id,
      EllHom.pullSection_id, he, EllObj.isoPullbackAlong_hom,
      EllObj.toPullbackAlong_pullbackAlongπ] at this
  · intro hh
    refine pullSection_iso_injective e ?_
    rw [← EllHom.pullSection_comp, ← EllHom.pullSection_comp, e.hom_inv_id,
      EllHom.pullSection_id, he, EllObj.isoPullbackAlong_hom,
      EllObj.toPullbackAlong_pullbackAlongπ]
    exact hh

/-! ### `yFullCandidate` represents the full-level problem (WP-D2c-3)

The single remaining step of the D-chain. Stated here so the interface is fixed and
type-checked; the proof is the one piece still open.

**Proof plan.** Write `B := X₁.curve.fullLevelLocus N h` and `π_B := fullLevelLocusπ`.

*Forward.* Given `u : T ⟶ yFullCandidate N X₁ h`, its base map is `u.baseHom : T.base ⟶ B`,
and `u ≫ X₁.pullbackAlongπ π_B : T ⟶ X₁` has base map `u.baseHom ≫ π_B`. Feeding
`⟨u.baseHom, _⟩` to `fullLevelLocusPointsEquiv` yields a naive full level structure on
`X₁.curve.baseChange (u.baseHom ≫ π_B) = (X₁.pullbackAlong (u.baseHom ≫ π_B)).curve`;
transport it to `T.curve` along the isomorphism `toPullbackAlong` supplies
(`Moduli/QuotientProblem.lean:73`, with `toPullbackAlong_pullbackAlongπ` as its defining
property).

*Backward.* Given a full level structure `(P, Q)` on `T`, its first member is a naive
`Γ₁(N)`-structure by `isNaiveGammaOne_of_isNaiveFullLevel` (WP-D1a), so
`v := rOne.homEquiv.symm ⟨P, _⟩ : T ⟶ X₁` classifies it. Transporting `(P, Q)` along
`toPullbackAlong v` and applying `fullLevelLocusPointsEquiv.symm` gives a lift
`T.base ⟶ B` over `v.baseHom`; combining with `toPullbackAlong v` produces
`T ⟶ yFullCandidate N X₁ h`.

*Round trips* are the two `Equiv` laws of `fullLevelLocusPointsEquiv` together with
`toPullbackAlong_pullbackAlongπ`; *naturality* is
`fullLevelLocusPointsEquiv`'s naturality (`Moduli/LevelLocusNatural.lean`) plus
functoriality of `toPullbackAlong`.

Note `rOne` is a hypothesis: the candidate is built from a `Γ₁(N)`-representing object, and
the backward direction is exactly where that representability is consumed. -/
theorem yFullCandidate_representableBy (N : ℕ) [NeZero N] (X₁ : EllObj R)
    (h : NIsInvertible X₁.base N) (P : X₁.base ⟶ X₁.curve.torsion N)
    (rOne : (gammaOneNaiveProblem R N).RepresentableBy X₁)
    (hP : P = X₁.curve.pointToTorsion (universalGammaOne R N rOne).1
      ((X₁.curve.smul_eq_zero_iff_comp_mulByHom (𝟙 X₁.base) N _).mp
        (universalGammaOne R N rOne).2.1))
    (hinv : ∀ (X : EllObj R) (k : Type u) [Field k] [IsAlgClosed k],
      (Spec (CommRingCat.of k) ⟶ X.base) → (N : k) ≠ 0) :
    Nonempty ((gammaFullNaiveProblem R N).RepresentableBy (yFullCandidate N X₁ h P)) := by
  sorry

/-- **(WP-D2c-4)** Given WP-D2c-3, every object representing the naive full level-`N`
problem has smooth affine structure morphism — which is exactly
`YFull.exists_representing_smooth_affine`. -/
theorem exists_representing_smooth_affine_of_candidate (N : ℕ) [NeZero N] (X₁ : EllObj R)
    (h : NIsInvertible X₁.base N) (P : X₁.base ⟶ X₁.curve.torsion N)
    (hsm : Smooth X₁.structMap) (ha : IsAffineHom X₁.structMap)
    (hrep : Nonempty ((gammaFullNaiveProblem R N).RepresentableBy
      (yFullCandidate N X₁ h P))) :
    ∃ X₀ : EllObj R, Nonempty ((gammaFullNaiveProblem R N).RepresentableBy X₀) ∧
      Smooth X₀.structMap ∧ IsAffineHom X₀.structMap :=
  haveI := ha
  ⟨yFullCandidate N X₁ h P, hrep, yFullCandidate_structMap_smooth N X₁ h P hsm,
    yFullCandidate_structMap_isAffineHom N X₁ h P⟩

end ModularCurves

/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.AdditionSpecPoints
import ModularCurves.EllipticCurve.NegModelBaseChange
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Group axioms for the two-law multiplication (T-W7.0g, [0c-i])

The five monoid/group axioms for `mulOver` at the `Over (Spec R)` level, for every elliptic
Weierstrass curve over every ring. Architecture (universality-by-instantiation, audit A6):

1. **T-G1 (this section)** — the 0e instance pack at the universe-`u` ULift atlas
   `WeierstrassAtlasRingU`: the universal curve and its fibre powers are integral (hence
   reduced), and the model is separated. This is what the field-points extensionality
   principle `hom_ext_of_forall_specPoint` consumes.
2. **T-G2** — the field-point leg API on fibre powers: a `K`-point of `E ×_U E` is a pair of
   `SpecPoints` reassembled by `pullback.lift`, and the multiplication/associator/whiskering
   morphisms evaluate legwise.
3. **T-G3** — the five equations at the atlas, by extensionality + the c6 spec
   `mulModelHom_specPoints` + the dictionary + mathlib's group law on `Affine.Point`.
4. **T-G4** — transport to every `R` along the classifying map: both sides of each equation
   are morphisms into the base-change pullback, identified leg-by-leg (`IsPullback.hom_ext`;
   π-legs by the `Over`-compatibilities, base-change legs by `mulModelHom_map` naturality).
5. **T-G5** — the `Over`-level statements (`mulOver_assoc` … `invOver_mulOver`).

Sources: Bosma–Lenstra Thm 2 + p. 231 (universality); mathlib `Affine.Point` group instance;
reviewer round 1 §Q4/Q5; audit A5/A6.
-/

open MvPolynomial AlgebraicGeometry CategoryTheory Limits WeierstrassCurve HomogeneousIdeal
  MonoidalCategory CartesianMonoidalCategory

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

/- Local shorthand for the universe-`u` universal curve. This is a purely notational
abbreviation — it expands at parse time to `𝕌`, so every
declaration below elaborates to exactly the same term as its fully-spelled form. It keeps the
defeq-sensitive T-G4 transport statements within the line-length budget. -/
local notation:max "𝕌" => universalWeierstrassLocU

/-! ## T-G1 — the 0e instance pack at the universe-`u` atlas -/

/-- The atlas ring `ℤ[a₁..a₆][Δ⁻¹]` is noetherian (localization of a finite-variable
polynomial ring over `ℤ`). -/
instance : IsNoetherianRing WeierstrassAtlasRing :=
  IsLocalization.isNoetherianRing (Submonoid.powers universalWeierstrass.Δ)
    WeierstrassAtlasRing inferInstance

/-- The universe-`u` atlas ring is noetherian (transport along `ULift.ringEquiv`). -/
instance : IsNoetherianRing WeierstrassAtlasRingU.{u} :=
  isNoetherianRing_of_ringEquiv WeierstrassAtlasRing
    (ULift.ringEquiv (R := WeierstrassAtlasRing)).symm

/-- **(T-W7.0e-proj at universe `u`)** The projective model of a Weierstrass curve over a
field in any universe is an integral scheme — the universe-polymorphic restatement of
`isIntegral_projModel` (whose proof is verbatim universe-polymorphic). -/
instance isIntegral_projModel_u {K : Type u} [Field K] (W : WeierstrassCurve K) :
    IsIntegral (projModel W) := by
  show IsIntegral (Proj (quotientGrading (projIdeal W)))
  refine AlgebraicGeometry.Proj.isIntegral_of_isDomain (𝒜 := quotientGrading (projIdeal W)) ?_
  refine ⟨1, one_pos, Ideal.Quotient.mk _ (MvPolynomial.X 0), ?_, ?_⟩
  · exact mk_mem_quotientGrading _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (MvPolynomial.isHomogeneous_X _ _))
  · rw [Ne, Ideal.Quotient.eq_zero_iff_mem, projIdeal_toIdeal, Ideal.mem_span_singleton]
    intro hdvd
    have hX0 : (MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) K) ≠ 0 :=
      MvPolynomial.X_ne_zero _
    have hF0 : W.toProjective.polynomial ≠ 0 := by
      rintro h
      rw [h] at hdvd
      exact hX0 (zero_dvd_iff.mp hdvd)
    have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdvd hX0
    rw [(projective_polynomial_isHomogeneous W).totalDegree hF0,
      MvPolynomial.totalDegree_X] at hle
    omega

/-- The projective model of any Weierstrass curve is separated (it is a `Proj`). -/
instance isSeparated_projModel {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    (projModel W).IsSeparated :=
  inferInstanceAs (Scheme.IsSeparated (Proj (quotientGrading (projIdeal W))))

/-- The universe-`u` universal curve is smooth of relative dimension 1 over the atlas. -/
instance : SmoothOfRelativeDimension 1 (projModelπ 𝕌) :=
  projModel_smooth 𝕌

instance : Smooth (projModelπ 𝕌) :=
  SmoothOfRelativeDimension.smooth 1 (projModelπ 𝕌)

/-- **(T-W7.0e crux at universe `u`)** Geometric integrality of the universe-`u` universal
curve: each geometric fibre is a projective plane Weierstrass cubic, integral by
`isIntegral_projModel_u`; the base change is identified by `isPullback_projModelBaseChange`. -/
instance geometricallyIntegral_universalCurveπU :
    GeometricallyIntegral (projModelπ universalWeierstrassLocU.{u}) := by
  rw [geometricallyIntegral_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  letI : Algebra WeierstrassAtlasRingU.{u} K := (Spec.preimage y).hom.toAlgebra
  have hy : y = Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    have h1 : CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K) = Spec.preimage y :=
      CommRingCat.ofHom_hom _
    rw [h1, Spec.map_preimage]
  have hpb := isPullback_projModelBaseChange (R := WeierstrassAtlasRingU.{u}) (R' := K)
    𝕌
  rw [← hy] at hpb
  exact ObjectProperty.prop_of_iso (IsIntegral ·) hpb.isoPullback (isIntegral_projModel_u _)

/-- The universe-`u` universal curve is an integral scheme. -/
instance : IsIntegral (projModel 𝕌) :=
  GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
    (projModelπ 𝕌)

/-- The universe-`u` universal curve is locally noetherian. -/
instance : IsLocallyNoetherian (projModel 𝕌) :=
  LocallyOfFiniteType.isLocallyNoetherian (projModelπ 𝕌)

instance : IsReduced (projModel 𝕌) := inferInstance

/-- **(T-W7.0e n = 2 at universe `u`)** The fibre square of the universe-`u` universal curve
is integral, hence reduced. -/
instance : IsIntegral (pullback (projModelπ 𝕌)
    (projModelπ 𝕌)) := inferInstance

instance : IsReduced (pullback (projModelπ 𝕌)
    (projModelπ 𝕌)) := inferInstance

/-- **(T-W7.0e n = 3 at universe `u`)** The fibre cube, `snd`-associated spelling. -/
instance : IsIntegral (pullback (projModelπ 𝕌)
    (pullback.snd (projModelπ 𝕌)
      (projModelπ 𝕌) ≫ projModelπ 𝕌)) :=
  inferInstance

/-- **(T-W7.0e n = 3 at universe `u`)** The fibre cube, `fst`-associated spelling. -/
instance : IsIntegral (pullback
    (pullback.fst (projModelπ 𝕌)
      (projModelπ 𝕌) ≫ projModelπ 𝕌)
    (projModelπ 𝕌)) := inferInstance

instance : IsReduced (pullback (projModelπ 𝕌)
    (pullback.snd (projModelπ 𝕌)
      (projModelπ 𝕌) ≫ projModelπ 𝕌)) :=
  inferInstance

instance : IsReduced (pullback
    (pullback.fst (projModelπ 𝕌)
      (projModelπ 𝕌) ≫ projModelπ 𝕌)
    (projModelπ 𝕌)) := inferInstance

/-! ## T-G2/T-G3 — the atlas equations, by field-points extensionality + the c6 spec

Every equation is proven on an arbitrary field-valued point `p` of the relevant fibre power:
decompose `p` into its `SpecPoints` legs (the canonical algebra on `K` comes from
`Spec.preimage` of the structure composite), evaluate both sides through the c6 spec
`mulModelHom_specPoints` (and `negModelHom_specPoints` / `projModelPointsEquiv_zero`), apply
the corresponding group law on `Affine.Point`, and close by injectivity of the dictionary. -/

section AtlasEquations

/-- **(spec-shape of a structure composite)** For a `K`-point `q` of the atlas base, equipped
with its canonical algebra `(Spec.preimage q).hom.toAlgebra`, `q` is the `Spec` of the structure
ring map. This is the spec-shape identity that opens every atlas field-point computation
(the `hσ`/`hπ₁` steps of `mulModelHom_comm_atlas`, `mulOver_assoc_atlas`, `mulOver_oneOver_atlas`,
`invOver_mulOver_atlas`). -/
private lemma structure_eq_specMap {K : Type u} [Field K]
    (q : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of WeierstrassAtlasRingU.{u})) :
    letI : Algebra WeierstrassAtlasRingU.{u} K := (Spec.preimage q).hom.toAlgebra
    q = Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
  letI : Algebra WeierstrassAtlasRingU.{u} K := (Spec.preimage q).hom.toAlgebra
  have h1 : CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K) = Spec.preimage q :=
    CommRingCat.ofHom_hom _
  rw [h1, Spec.map_preimage]

/-- **(T-G3-comm)** Commutativity of the two-law multiplication at the universe-`u` atlas:
swapping the factors of `E ×_U E` does not change the product. -/
theorem mulModelHom_comm_atlas :
    (pullbackSymmetry (projModelπ universalWeierstrassLocU.{u})
          (projModelπ universalWeierstrassLocU.{u})).hom ≫
        (mulModelHom universalWeierstrassLocU.{u}) =
      (mulModelHom universalWeierstrassLocU.{u}) := by
  classical
  refine hom_ext_of_forall_specPoint fun K _ p => ?_
  -- the canonical algebra on `K`, from the structure composite of the first leg
  letI : Algebra WeierstrassAtlasRingU.{u} K :=
    ((Spec.preimage
      (p ≫ pullback.fst (projModelπ 𝕌) (projModelπ 𝕌) ≫ (projModelπ 𝕌))).hom).toAlgebra
  have hσ := structure_eq_specMap
    (p ≫ pullback.fst (projModelπ 𝕌) (projModelπ 𝕌) ≫ (projModelπ 𝕌))
  have hπP : (p ≫ pullback.fst (projModelπ 𝕌) (projModelπ 𝕌)) ≫ (projModelπ 𝕌) =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    rw [Category.assoc]; exact hσ
  have hπQ : (p ≫ pullback.snd (projModelπ 𝕌) (projModelπ 𝕌)) ≫ (projModelπ 𝕌) =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]; exact hπP
  -- both sides at `p` are spec-shaped lifts
  have hQP := mulModelHom_specPoints 𝕌 K
    ⟨p ≫ pullback.snd (projModelπ 𝕌) (projModelπ 𝕌), hπQ⟩
    ⟨p ≫ pullback.fst (projModelπ 𝕌) (projModelπ 𝕌), hπP⟩
  have hPQ := mulModelHom_specPoints 𝕌 K
    ⟨p ≫ pullback.fst (projModelπ 𝕌) (projModelπ 𝕌), hπP⟩
    ⟨p ≫ pullback.snd (projModelπ 𝕌) (projModelπ 𝕌), hπQ⟩
  have keyval := congrArg Subtype.val
    ((projModelPointsEquiv 𝕌 K).injective
      (hQP.trans ((add_comm _ _).trans hPQ.symm)))
  have hL : p ≫ ((pullbackSymmetry (projModelπ 𝕌) (projModelπ 𝕌)).hom ≫ (mulModelHom 𝕌)) =
      pullback.lift (p ≫ pullback.snd (projModelπ 𝕌) (projModelπ 𝕌))
          (p ≫ pullback.fst (projModelπ 𝕌) (projModelπ 𝕌))
        (hπQ.trans hπP.symm) ≫ (mulModelHom 𝕌) := by
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, pullback.lift_fst]
    · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.lift_snd]
  have hR : p = pullback.lift (p ≫ pullback.fst (projModelπ 𝕌) (projModelπ 𝕌))
      (p ≫ pullback.snd (projModelπ 𝕌) (projModelπ 𝕌))
      (hπP.trans hπQ.symm) := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd]
  exact hL.trans (keyval.trans (congrArg (· ≫ (mulModelHom 𝕌)) hR.symm))

/-- **(atlas group-law associativity, point level)** For three `K`-points `a, b, c` of the
universal model sharing a base, the two bracketings of the two-law product agree. This is the
`Affine.Point` `add_assoc` core of `mulOver_assoc_atlas`, isolated from the fibre-cube geometry:
it evaluates the three relevant `mulModelHom` lifts through `mulModelHom_specPoints`, applies
`add_assoc` under the dictionary `projModelPointsEquiv`, and re-injects. -/
private lemma mulModelHom_assoc_specPoints {K : Type u} [Field K]
    [Algebra WeierstrassAtlasRingU.{u} K]
    (a b c : Spec (CommRingCat.of K) ⟶ projModel 𝕌)
    (ha : a ≫ projModelπ 𝕌 = Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)))
    (hb : b ≫ projModelπ 𝕌 = Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)))
    (hc : c ≫ projModelπ 𝕌 = Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)))
    (h12 : (pullback.lift a b (ha.trans hb.symm) ≫ mulModelHom 𝕌) ≫ projModelπ 𝕌 =
        Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)))
    (h23 : (pullback.lift b c (hb.trans hc.symm) ≫ mulModelHom 𝕌) ≫ projModelπ 𝕌 =
        Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K))) :
    pullback.lift (pullback.lift a b (ha.trans hb.symm) ≫ mulModelHom 𝕌) c (h12.trans hc.symm) ≫
        mulModelHom 𝕌 =
      pullback.lift a (pullback.lift b c (hb.trans hc.symm) ≫ mulModelHom 𝕌) (ha.trans h23.symm) ≫
        mulModelHom 𝕌 := by
  classical
  have hP₁₂ := mulModelHom_specPoints 𝕌 K ⟨a, ha⟩ ⟨b, hb⟩
  have hP₂₃ := mulModelHom_specPoints 𝕌 K ⟨b, hb⟩ ⟨c, hc⟩
  have hL2 := mulModelHom_specPoints 𝕌 K ⟨_, h12⟩ ⟨c, hc⟩
  have hR2 := mulModelHom_specPoints 𝕌 K ⟨a, ha⟩ ⟨_, h23⟩
  have e2 : projModelPointsEquiv 𝕌 K ⟨_, h12⟩ =
      projModelPointsEquiv 𝕌 K ⟨a, ha⟩ + projModelPointsEquiv 𝕌 K ⟨b, hb⟩ :=
    (congrArg (projModelPointsEquiv 𝕌 K) (Subtype.ext rfl)).trans hP₁₂
  have e4 : projModelPointsEquiv 𝕌 K ⟨_, h23⟩ =
      projModelPointsEquiv 𝕌 K ⟨b, hb⟩ + projModelPointsEquiv 𝕌 K ⟨c, hc⟩ :=
    (congrArg (projModelPointsEquiv 𝕌 K) (Subtype.ext rfl)).trans hP₂₃
  have ebigL := hL2.trans (congrArg (· + projModelPointsEquiv 𝕌 K ⟨c, hc⟩) e2)
  have ebigR := hR2.trans (congrArg (projModelPointsEquiv 𝕌 K ⟨a, ha⟩ + ·) e4)
  exact congrArg Subtype.val
    ((projModelPointsEquiv 𝕌 K).injective (ebigL.trans ((add_assoc _ _ _).trans ebigR.symm)))

set_option backward.isDefEq.respectTransparency.types false in
/-- **(T-G3-assoc)** Associativity of the two-law multiplication at the universe-`u` atlas,
at the `Over (Spec 𝕌)` level: evaluate on a field point of the fibre cube, reduce both
sides to spec-shaped lifts, and apply `add_assoc` on `Affine.Point`. -/
theorem mulOver_assoc_atlas :
    (mulOver universalWeierstrassLocU.{u} ▷ modelOver universalWeierstrassLocU.{u}) ≫
        mulOver universalWeierstrassLocU.{u} =
      (α_ (modelOver universalWeierstrassLocU.{u}) (modelOver universalWeierstrassLocU.{u})
          (modelOver universalWeierstrassLocU.{u})).hom ≫
        (modelOver universalWeierstrassLocU.{u} ◁ mulOver universalWeierstrassLocU.{u}) ≫
        mulOver universalWeierstrassLocU.{u} := by
  classical
  apply Over.OverMorphism.ext
  haveI hred : IsReduced (((modelOver 𝕌 ⊗
      modelOver 𝕌) ⊗ modelOver 𝕌).left) :=
    inferInstanceAs (IsReduced (pullback
      (pullback.fst (projModelπ 𝕌) (projModelπ 𝕌) ≫ (projModelπ 𝕌)) (projModelπ 𝕌)))
  haveI hsep : ((modelOver 𝕌).left).IsSeparated :=
    inferInstanceAs ((projModel 𝕌).IsSeparated)
  refine hom_ext_of_forall_specPoint fun K _ p => ?_
  -- three legs of the cube point (all projModelπ-spelled; defeq to the `.hom` tensor form)
  letI : Algebra WeierstrassAtlasRingU.{u} K :=
    ((Spec.preimage ((p ≫
      pullback.fst (pullback.fst (projModelπ 𝕌) (projModelπ 𝕌) ≫ (projModelπ 𝕌)) (projModelπ 𝕌) ≫
      pullback.fst (projModelπ 𝕌) (projModelπ 𝕌)) ≫ (projModelπ 𝕌))).hom).toAlgebra
  have hπ₁ := structure_eq_specMap
    ((p ≫ pullback.fst (pullback.fst (projModelπ 𝕌) (projModelπ 𝕌) ≫ (projModelπ 𝕌))
        (projModelπ 𝕌) ≫
      pullback.fst (projModelπ 𝕌) (projModelπ 𝕌)) ≫ (projModelπ 𝕌))
  have hπ₂ : ((p ≫ pullback.fst (pullback.fst (projModelπ 𝕌) (projModelπ 𝕌) ≫ (projModelπ 𝕌))
        (projModelπ 𝕌) ≫
      pullback.snd (projModelπ 𝕌) (projModelπ 𝕌)) ≫ (projModelπ 𝕌)) =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    rw [← hπ₁]
    simp only [Category.assoc]
    congr 2
    exact pullback.condition.symm
  have hπ₃ : ((p ≫ pullback.snd (pullback.fst (projModelπ 𝕌) (projModelπ 𝕌) ≫ (projModelπ 𝕌))
        (projModelπ 𝕌)) ≫ (projModelπ 𝕌)) =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    rw [← hπ₁]
    simp only [Category.assoc]
    exact congrArg (p ≫ ·)
      (pullback.condition (f := pullback.fst (projModelπ 𝕌) (projModelπ 𝕌) ≫ (projModelπ 𝕌))
        (g := (projModelπ 𝕌))).symm
  have hπ₁₂ : (pullback.lift _ _ ((hπ₁).trans (hπ₂).symm) ≫
      mulModelHom 𝕌) ≫ (projModelπ 𝕌) =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    rw [Category.assoc, show mulModelHom 𝕌 ≫ (projModelπ 𝕌) = _ from mulModelHom_π 𝕌,
      ← Category.assoc, pullback.lift_fst]
    exact hπ₁
  have hπ₂₃ : (pullback.lift _ _ ((hπ₂).trans (hπ₃).symm) ≫
      mulModelHom 𝕌) ≫ (projModelπ 𝕌) =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    rw [Category.assoc, show mulModelHom 𝕌 ≫ (projModelπ 𝕌) = _ from mulModelHom_π 𝕌,
      ← Category.assoc, pullback.lift_fst]
    exact hπ₂
  have keyval := mulModelHom_assoc_specPoints _ _ _ hπ₁ hπ₂ hπ₃ hπ₁₂ hπ₂₃
  -- outer first projection of the cube through the (mo⊗mo)-factor is the (f,g) input lift
  have hp₁₂p :
      p ≫ pullback.fst (pullback.fst (projModelπ 𝕌)
              (projModelπ 𝕌) ≫ projModelπ 𝕌)
            (projModelπ 𝕌) =
        pullback.lift
          (p ≫ pullback.fst (pullback.fst (projModelπ 𝕌)
                  (projModelπ 𝕌) ≫ projModelπ 𝕌)
                (projModelπ 𝕌) ≫
            pullback.fst (projModelπ 𝕌) (projModelπ 𝕌))
          (p ≫ pullback.fst (pullback.fst (projModelπ 𝕌)
                  (projModelπ 𝕌) ≫ projModelπ 𝕌)
                (projModelπ 𝕌) ≫
            pullback.snd (projModelπ 𝕌) (projModelπ 𝕌))
          (hπ₁.trans hπ₂.symm) := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc]
    · rw [pullback.lift_snd, Category.assoc]
  -- associator middle leg: p through α to the (g,h)-factor is the (g,h) input lift
  have hq :
      p ≫ (α_ (modelOver 𝕌) (modelOver 𝕌)
            (modelOver 𝕌)).hom.left ≫
          pullback.snd (projModelπ 𝕌)
            (pullback.fst (projModelπ 𝕌) (projModelπ 𝕌) ≫
              projModelπ 𝕌) =
        pullback.lift
          (p ≫ pullback.fst (pullback.fst (projModelπ 𝕌)
                  (projModelπ 𝕌) ≫ projModelπ 𝕌)
                (projModelπ 𝕌) ≫
            pullback.snd (projModelπ 𝕌) (projModelπ 𝕌))
          (p ≫ pullback.snd (pullback.fst (projModelπ 𝕌)
                  (projModelπ 𝕌) ≫ projModelπ 𝕌)
                (projModelπ 𝕌))
          (hπ₂.trans hπ₃.symm) := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, Category.assoc]
      exact congrArg (p ≫ ·) (Over.associator_hom_left_snd_fst _ _ _)
    · rw [pullback.lift_snd, Category.assoc, Category.assoc]
      exact congrArg (p ≫ ·) (Over.associator_hom_left_snd_snd _ _ _)
  have hL : p ≫ ((mulOver 𝕌 ▷ modelOver 𝕌) ≫
        mulOver 𝕌).left =
      pullback.lift _ _ ((hπ₁₂).trans (hπ₃).symm) ≫ mulModelHom 𝕌 := by
    rw [Over.comp_left, mulOver_left, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans
        ((congrArg (p ≫ ·) (Over.whiskerRight_left_fst (mulOver 𝕌))).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ mulModelHom 𝕌) hp₁₂p).trans
              (pullback.lift_fst _ _ _).symm)))
    · exact (Category.assoc _ _ _).trans
        ((congrArg (p ≫ ·) (Over.whiskerRight_left_snd (mulOver 𝕌))).trans
          (pullback.lift_snd _ _ _).symm)
  -- associator side, pre-`mul` lift identity
  have hR0 : p ≫ ((α_ (modelOver 𝕌) (modelOver 𝕌)
        (modelOver 𝕌)).hom.left ≫
        (modelOver 𝕌 ◁ mulOver 𝕌).left) =
      pullback.lift _ _ ((hπ₁).trans (hπ₂₃).symm) := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans
        ((congrArg (p ≫ ·)
          ((Category.assoc _ _ _).trans
            ((congrArg ((α_ (modelOver 𝕌)
                  (modelOver 𝕌)
                  (modelOver 𝕌)).hom.left ≫ ·)
                (Over.whiskerLeft_left_fst (mulOver 𝕌))).trans
              (Over.associator_hom_left_fst _ _ _)))).trans
          (pullback.lift_fst _ _ _).symm)
    · exact (Category.assoc _ _ _).trans
        ((congrArg (p ≫ ·)
            ((Category.assoc _ _ _).trans
              (congrArg ((α_ (modelOver 𝕌)
                  (modelOver 𝕌)
                  (modelOver 𝕌)).hom.left ≫ ·)
                (Over.whiskerLeft_left_snd (mulOver 𝕌))))).trans
          ((congrArg (p ≫ ·) (Category.assoc _ _ _).symm).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (· ≫ mulModelHom 𝕌) hq).trans
                (pullback.lift_snd _ _ _).symm))))
  have hR : p ≫ ((α_ (modelOver 𝕌) (modelOver 𝕌)
        (modelOver 𝕌)).hom ≫
        (modelOver 𝕌 ◁ mulOver 𝕌) ≫
        mulOver 𝕌).left =
      pullback.lift _ _ ((hπ₁).trans (hπ₂₃).symm) ≫ mulModelHom 𝕌 := by
    rw [Over.comp_left, Over.comp_left, mulOver_left]
    exact ((congrArg (p ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm).trans
      (congrArg (· ≫ mulModelHom 𝕌) hR0)
  exact hL.trans (keyval.trans hR.symm)

set_option backward.isDefEq.respectTransparency.types false in
/-- **(T-G3-mul-one)** Right unit law at the atlas. -/
theorem mulOver_oneOver_atlas :
    (modelOver universalWeierstrassLocU.{u} ◁ oneOver universalWeierstrassLocU.{u}) ≫
        mulOver universalWeierstrassLocU.{u} =
      (ρ_ (modelOver universalWeierstrassLocU.{u})).hom := by
  classical
  apply Over.OverMorphism.ext
  rw [Over.comp_left, mulOver_left, Over.rightUnitor_hom_left]
  haveI : IsReduced ((modelOver 𝕌 ⊗
      𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).left) :=
    ObjectProperty.prop_of_iso (IsReduced ·)
      ((Over.forget _).mapIso (ρ_ (modelOver 𝕌))).symm
      (inferInstanceAs (IsReduced (projModel 𝕌)))
  haveI : (modelOver 𝕌).left.IsSeparated :=
    inferInstanceAs ((projModel 𝕌).IsSeparated)
  refine hom_ext_of_forall_specPoint fun K _ p => ?_
  letI : Algebra WeierstrassAtlasRingU.{u} K :=
    ((Spec.preimage ((p ≫ pullback.fst (projModelπ 𝕌)
      (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom) ≫
        projModelπ 𝕌)).hom).toAlgebra
  have hσ := structure_eq_specMap ((p ≫ pullback.fst (projModelπ 𝕌)
    (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom) ≫ projModelπ 𝕌)
  have hπZ : (Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) ≫
      projModelZero 𝕌) ≫ projModelπ 𝕌 =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    rw [Category.assoc, projModelZero_projModelπ, Category.comp_id]
  have hcond : pullback.fst (projModelπ 𝕌)
      (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom ≫
      projModelπ 𝕌 =
      pullback.snd (projModelπ 𝕌)
      (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom ≫
      (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom :=
    pullback.condition
  have hsndσ : (p ≫ pullback.snd (projModelπ 𝕌)
      (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom) ≫
      (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) :=
    (Category.assoc _ _ _).trans ((congrArg (p ≫ ·) hcond.symm).trans
      ((Category.assoc _ _ _).symm.trans hσ))
  have hZeval : p ≫ (pullback.snd (projModelπ 𝕌)
      (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom ≫
        (oneOver 𝕌).left) =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) ≫
        projModelZero 𝕌 := by
    rw [oneOver_left]
    exact (Category.assoc _ _ _).symm.trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ projModelZero 𝕌) hsndσ))
  have hspec := mulModelHom_specPoints 𝕌 K
    ⟨p ≫ pullback.fst (projModelπ 𝕌)
      (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom, hσ⟩
    ⟨Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) ≫
      projModelZero 𝕌, hπZ⟩
  have hkey := congrArg Subtype.val
    ((projModelPointsEquiv 𝕌 K).injective
      (hspec.trans ((congrArg (projModelPointsEquiv 𝕌 K
          ⟨p ≫ pullback.fst (projModelπ 𝕌)
            (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom, hσ⟩ + ·)
          (projModelPointsEquiv_zero 𝕌 K)).trans (add_zero _))))
  have hL : p ≫ ((modelOver 𝕌 ◁ oneOver 𝕌).left ≫
        mulModelHom 𝕌) =
      pullback.lift _ _ (hσ.trans hπZ.symm) ≫ mulModelHom 𝕌 := by
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans
        ((congrArg (p ≫ ·) (Over.whiskerLeft_left_fst (oneOver 𝕌))).trans
          (pullback.lift_fst _ _ _).symm)
    · exact (Category.assoc _ _ _).trans
        ((congrArg (p ≫ ·) (Over.whiskerLeft_left_snd (oneOver 𝕌))).trans
          (hZeval.trans (pullback.lift_snd _ _ _).symm))
  exact hL.trans hkey

set_option backward.isDefEq.respectTransparency.types false in
/-- **(T-G3-inv)** Left inverse law at the atlas. -/
theorem invOver_mulOver_atlas :
    lift (invOver universalWeierstrassLocU.{u}) (𝟙 (modelOver universalWeierstrassLocU.{u})) ≫
        mulOver universalWeierstrassLocU.{u} =
      toUnit (modelOver universalWeierstrassLocU.{u}) ≫ oneOver universalWeierstrassLocU.{u} := by
  classical
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, mulOver_left, Over.toUnit_left, oneOver_left]
  haveI : IsReduced (modelOver 𝕌).left :=
    inferInstanceAs (IsReduced (projModel 𝕌))
  haveI : (modelOver 𝕌).left.IsSeparated :=
    inferInstanceAs ((projModel 𝕌).IsSeparated)
  refine hom_ext_of_forall_specPoint fun K _ p => ?_
  letI : Algebra WeierstrassAtlasRingU.{u} K :=
    ((Spec.preimage (p ≫ projModelπ 𝕌)).hom).toAlgebra
  have hσ := structure_eq_specMap (p ≫ projModelπ 𝕌)
  have hπneg : (p ≫ negModelHom 𝕌) ≫ projModelπ 𝕌 =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) :=
    (Category.assoc _ _ _).trans
      ((congrArg (p ≫ ·) (negModelHom_π 𝕌)).trans hσ)
  have hπZ : (Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) ≫
      projModelZero 𝕌) ≫ projModelπ 𝕌 =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    rw [Category.assoc, projModelZero_projModelπ, Category.comp_id]
  have hspec := mulModelHom_specPoints 𝕌 K
    ⟨p ≫ negModelHom 𝕌, hπneg⟩ ⟨p, hσ⟩
  have hneg := negModelHom_specPoints 𝕌 K ⟨p, hσ⟩
  have hkey := congrArg Subtype.val
    ((projModelPointsEquiv 𝕌 K).injective
      ((hspec.trans ((congrArg (· + projModelPointsEquiv 𝕌 K ⟨p, hσ⟩) hneg).trans
          (neg_add_cancel _))).trans
        (projModelPointsEquiv_zero 𝕌 K).symm))
  have hL : p ≫ ((lift (invOver 𝕌)
        (𝟙 (modelOver 𝕌))).left ≫
        mulModelHom 𝕌) =
      pullback.lift _ _ (hπneg.trans hσ.symm) ≫ mulModelHom 𝕌 := by
    rw [Over.lift_left, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans
        ((congrArg (p ≫ ·) (pullback.lift_fst _ _ _)).trans
          ((congrArg (p ≫ ·) (invOver_left 𝕌)).trans
            (pullback.lift_fst _ _ _).symm))
    · exact (Category.assoc _ _ _).trans
        ((congrArg (p ≫ ·) (pullback.lift_snd _ _ _)).trans
          ((congrArg (p ≫ ·) (Over.id_left (modelOver 𝕌))).trans
            ((Category.comp_id p).trans (pullback.lift_snd _ _ _).symm)))
  have hRHS : p ≫ ((modelOver 𝕌).hom ≫
      ((𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom ≫
        projModelZero 𝕌)) =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) ≫
        projModelZero 𝕌 := by
    rw [Over.tensorUnit_hom, Category.id_comp, ← Category.assoc]
    exact congrArg (· ≫ projModelZero 𝕌) hσ
  exact (hL.trans hkey).trans hRHS.symm

end AtlasEquations

section Transport

variable {R : Type u} [CommRing R]

/-- **(T-G4 helper)** `(modelOver W).hom = projModelπ W` as a simp lemma keyed on `modelOver`
(mathlib's `Over.mk_hom` will not fire on the folded abbrev). Needed to collapse the
Over-monoidal `.hom`/`.left` spelling to raw `projModelπ`/`projModel` in the transports. -/
@[simp] lemma modelOver_hom (W : WeierstrassCurve R) : (modelOver W).hom = projModelπ W := rfl

/-- **(T-G4 helper)** `(modelOver W).left = projModel W`, keyed on `modelOver`. -/
@[simp] lemma modelOver_left (W : WeierstrassCurve R) : (modelOver W).left = projModel W := rfl

/-- **(T-G4 helper)** Of-form base-change naturality of the zero section — the eqToHom-free
wrapper of `projModelZero_baseChange` (dissolves `projModelBaseChangeOf`'s eqToHom layer by
`subst`), mirroring `mulModelHomBC_baseChange`. Consumed by the unit-law transports. -/
lemma projModelZero_baseChangeOf {U : Type u} [CommRing U] (f : U →+* R)
    (W₀ : WeierstrassCurve U) (W : WeierstrassCurve R) (h : W₀.map f = W) :
    projModelZero W ≫ projModelBaseChangeOf f W₀ W h =
      Spec.map (CommRingCat.ofHom f) ≫ projModelZero W₀ := by
  subst h
  rw [projModelBaseChangeOf, eqToHom_refl, Category.id_comp]
  letI : Algebra U R := f.toAlgebra
  exact projModelZero_baseChange W₀

/-- **(T-G4-comm-raw)** Commutativity of `mulModelHom` at the raw scheme level, for every
elliptic `W` over every `R` — the base-change transport of `mulModelHom_comm_atlas`. -/
theorem mulModelHom_comm (W : WeierstrassCurve R) [W.IsElliptic] :
    (pullbackSymmetry (projModelπ W) (projModelπ W)).hom ≫ mulModelHom W = mulModelHom W := by
  have raw : (pullbackSymmetry (projModelπ 𝕌)
        (projModelπ 𝕌)).hom ≫
      WeierstrassCurve.Projective.mulModelHom 𝕌
        (𝕌).isUnit_Δ =
      WeierstrassCurve.Projective.mulModelHom 𝕌
        (𝕌).isUnit_Δ := by
    rw [← mulModelHom_universalWeierstrassLocU]; exact mulModelHom_comm_atlas
  have hbc : mulModelHom W ≫ projModelBaseChangeOf (classifyRingHomU W)
        𝕌 W (universalWeierstrassLocU_map_classifyRingHomU W) =
      pullbackMapBaseChangeOf (classifyRingHomU W) 𝕌 W
        (universalWeierstrassLocU_map_classifyRingHomU W) ≫
      WeierstrassCurve.Projective.mulModelHom 𝕌
        (𝕌).isUnit_Δ :=
    mulModelHomBC_baseChange (classifyRingHomU W) 𝕌
      (𝕌).isUnit_Δ W (universalWeierstrassLocU_map_classifyRingHomU W)
  have hsym : (pullbackSymmetry (projModelπ W) (projModelπ W)).hom ≫
      pullbackMapBaseChangeOf (classifyRingHomU W) 𝕌 W
        (universalWeierstrassLocU_map_classifyRingHomU W) =
      pullbackMapBaseChangeOf (classifyRingHomU W) 𝕌 W
        (universalWeierstrassLocU_map_classifyRingHomU W) ≫
      (pullbackSymmetry (projModelπ 𝕌)
        (projModelπ 𝕌)).hom := by
    apply pullback.hom_ext <;>
      simp only [pullbackMapBaseChangeOf, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd,
        pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc]
  apply (isPullback_projModelBaseChangeOf (classifyRingHomU W) 𝕌 W
    (universalWeierstrassLocU_map_classifyRingHomU W)).hom_ext
  · rw [Category.assoc]
    show _ = mulModelHom W ≫ _
    rw [hbc, ← Category.assoc, hsym, Category.assoc, raw]
  · rw [Category.assoc]
    show _ = mulModelHom W ≫ _
    rw [mulModelHom_π, ← Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact (pullback.condition).symm

/-- **(T-W7.0g-comm)** Commutativity of the two-law multiplication, as the braided
monoid-object equation in `Over (Spec R)`, for every elliptic `W` over every `R`. -/
theorem mulOver_comm (W : WeierstrassCurve R) [W.IsElliptic] :
    (β_ (modelOver W) (modelOver W)).hom ≫ mulOver W = mulOver W := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.braiding_hom_left, mulOver_left]
  exact mulModelHom_comm W

/-- (e₂) The single-factor base-change compatibility over `Spec`: the model structure map
commutes with the base change. -/
private lemma BaseChangeOf.modelOver_hom (f : WeierstrassAtlasRingU.{u} →+* R)
    [((𝕌).map f).IsElliptic] :
    (modelOver ((𝕌).map f)).hom ≫ Spec.map (CommRingCat.ofHom f) =
      projModelBaseChangeOf f 𝕌 ((𝕌).map f) rfl ≫ (modelOver 𝕌).hom := by
  simp only [ModularCurves.modelOver_hom]
  exact (isPullback_projModelBaseChangeOf f 𝕌 ((𝕌).map f) rfl).w.symm

/-- (e₁) The tensor-square base-change compatibility over `Spec`: the tensor structure map
commutes with the fibre-square base change. -/
private lemma BaseChangeOf.tensorObj_hom (f : WeierstrassAtlasRingU.{u} →+* R)
    [((𝕌).map f).IsElliptic] :
    (modelOver ((𝕌).map f) ⊗
        modelOver ((𝕌).map f)).hom ≫
      Spec.map (CommRingCat.ofHom f) =
      pullbackMapBaseChangeOf f 𝕌
          ((𝕌).map f) rfl ≫
        (modelOver 𝕌 ⊗ modelOver 𝕌).hom := by
  rw [Over.tensorObj_hom, Over.tensorObj_hom]
  simp only [ModularCurves.modelOver_hom]
  have hmap : pullbackMapBaseChangeOf f 𝕌
      ((𝕌).map f) rfl ≫
      pullback.fst (projModelπ 𝕌)
        (projModelπ 𝕌) =
      pullback.fst (projModelπ ((𝕌).map f))
        (projModelπ ((𝕌).map f)) ≫
        projModelBaseChangeOf f 𝕌
          ((𝕌).map f) rfl := by
    erw [pullbackMapBaseChangeOf, pullback.map, pullback.lift_fst]
  have hw := (isPullback_projModelBaseChangeOf f 𝕌
    ((𝕌).map f) rfl).w
  calc pullback.fst (projModelπ ((𝕌).map f))
        (projModelπ ((𝕌).map f)) ≫
        projModelπ ((𝕌).map f) ≫ Spec.map (CommRingCat.ofHom f)
      = pullback.fst (projModelπ ((𝕌).map f))
          (projModelπ ((𝕌).map f)) ≫
          (projModelπ ((𝕌).map f) ≫ Spec.map (CommRingCat.ofHom f)) :=
        rfl
    _ = pullback.fst (projModelπ ((𝕌).map f))
          (projModelπ ((𝕌).map f)) ≫
          (projModelBaseChangeOf f 𝕌
            ((𝕌).map f) rfl ≫
            projModelπ 𝕌) := by rw [← hw]
    _ = (pullback.fst (projModelπ ((𝕌).map f))
          (projModelπ ((𝕌).map f)) ≫
          projModelBaseChangeOf f 𝕌
            ((𝕌).map f) rfl) ≫
          projModelπ 𝕌 := (Category.assoc _ _ _).symm
    _ = (pullbackMapBaseChangeOf f 𝕌
          ((𝕌).map f) rfl ≫
          pullback.fst (projModelπ 𝕌)
            (projModelπ 𝕌)) ≫
          projModelπ 𝕌 := by rw [hmap]
    _ = pullbackMapBaseChangeOf f 𝕌
          ((𝕌).map f) rfl ≫
          pullback.fst (projModelπ 𝕌)
            (projModelπ 𝕌) ≫
          projModelπ 𝕌 := Category.assoc _ _ _

/-- The triple-tensor base-change comparison, hoisted to a top-level definition so its
`pullback.map` obligations (the e₁/e₂ compatibilities) elaborate once, outside the
tensor-heavy proof context (avoiding a `whnf` timeout inside the tactic block). -/
private noncomputable def BaseChangeOf.tripleMap (f : WeierstrassAtlasRingU.{u} →+* R)
    [((𝕌).map f).IsElliptic] :
    ((modelOver ((𝕌).map f) ⊗
        modelOver ((𝕌).map f)) ⊗
      modelOver ((𝕌).map f)).left ⟶
      ((modelOver 𝕌 ⊗ modelOver 𝕌) ⊗
        modelOver 𝕌).left :=
  pullback.map
    (modelOver ((𝕌).map f) ⊗
      modelOver ((𝕌).map f)).hom
    (modelOver ((𝕌).map f)).hom
    (modelOver 𝕌 ⊗ modelOver 𝕌).hom
    (modelOver 𝕌).hom
    (pullbackMapBaseChangeOf f 𝕌
      ((𝕌).map f) rfl)
    (projModelBaseChangeOf f 𝕌
      ((𝕌).map f) rfl)
    (Spec.map (CommRingCat.ofHom f))
    (BaseChangeOf.tensorObj_hom f) (BaseChangeOf.modelOver_hom f)

/-- The fibre-square base change, retyped at the Over-monoidal tensor: these helpers live in
the `Over` spelling, and the standard-spelled content bridges to them by term-mode `exact`. -/
private noncomputable def BaseChangeOf.pairMap (f : WeierstrassAtlasRingU.{u} →+* R)
    [((𝕌).map f).IsElliptic] :
    (modelOver ((𝕌).map f) ⊗ modelOver ((𝕌).map f)).left ⟶
      (modelOver 𝕌 ⊗ modelOver 𝕌).left :=
  pullbackMapBaseChangeOf f 𝕌 ((𝕌).map f) rfl

private lemma BaseChangeOf.pairMap_fst (f : WeierstrassAtlasRingU.{u} →+* R)
    [((𝕌).map f).IsElliptic] :
    BaseChangeOf.pairMap f ≫
      pullback.fst (modelOver 𝕌).hom (modelOver 𝕌).hom =
      pullback.fst (modelOver ((𝕌).map f)).hom (modelOver ((𝕌).map f)).hom ≫
        projModelBaseChangeOf f 𝕌 ((𝕌).map f) rfl :=
  (limit.lift_π _ _).trans rfl

private lemma BaseChangeOf.pairMap_snd (f : WeierstrassAtlasRingU.{u} →+* R)
    [((𝕌).map f).IsElliptic] :
    BaseChangeOf.pairMap f ≫
      pullback.snd (modelOver 𝕌).hom (modelOver 𝕌).hom =
      pullback.snd (modelOver ((𝕌).map f)).hom (modelOver ((𝕌).map f)).hom ≫
        projModelBaseChangeOf f 𝕌 ((𝕌).map f) rfl :=
  (limit.lift_π _ _).trans rfl

/-- Triple projection, `BaseChangeOf.pairMap`-spelled (fst). -/
private lemma BaseChangeOf.tripleMap_fst (f : WeierstrassAtlasRingU.{u} →+* R)
    [((𝕌).map f).IsElliptic] :
    BaseChangeOf.tripleMap f ≫
      pullback.fst (modelOver 𝕌 ⊗ modelOver 𝕌).hom
        (modelOver 𝕌).hom =
      pullback.fst (modelOver ((𝕌).map f) ⊗ modelOver ((𝕌).map f)).hom
        (modelOver ((𝕌).map f)).hom ≫ BaseChangeOf.pairMap f :=
  (limit.lift_π _ _).trans rfl

/-- Triple projection, Over-spelled (snd). -/
private lemma BaseChangeOf.tripleMap_snd (f : WeierstrassAtlasRingU.{u} →+* R)
    [((𝕌).map f).IsElliptic] :
    BaseChangeOf.tripleMap f ≫
      pullback.snd (modelOver 𝕌 ⊗ modelOver 𝕌).hom
        (modelOver 𝕌).hom =
      pullback.snd (modelOver ((𝕌).map f) ⊗ modelOver ((𝕌).map f)).hom
        (modelOver ((𝕌).map f)).hom ≫
        projModelBaseChangeOf f 𝕌 ((𝕌).map f) rfl :=
  (limit.lift_π _ _).trans rfl

/-- **(T-G4 shared BC-leg)** The multiplication morphism intertwines the base change to
`(𝕌).map f`: pushing `mulModelHom` across `projModelBaseChangeOf` equals whiskering
`pullbackMapBaseChangeOf` into the universal `mulModelHom`. This is the base-change leg shared,
verbatim, by the `*_of_map` transports (`BaseChangeOf.mulOver_left`, `mulOver_oneOver_of_map`,
`invOver_mulOver_of_map`); each `hbc` step is a call to this lemma. -/
private lemma BaseChangeOf.mulModelHom (f : WeierstrassAtlasRingU.{u} →+* R)
    [((𝕌).map f).IsElliptic] :
    mulModelHom ((𝕌).map f) ≫ projModelBaseChangeOf f 𝕌 ((𝕌).map f) rfl =
      pullbackMapBaseChangeOf f 𝕌 ((𝕌).map f) rfl ≫
        WeierstrassCurve.Projective.mulModelHom 𝕌 (𝕌).isUnit_Δ := by
  rw [mulModelHom_map_eq_BC f]
  exact mulModelHomBC_baseChange f 𝕌 (𝕌).isUnit_Δ ((𝕌).map f) rfl

/-- The multiplication intertwines the base change, in the Over spelling (`hbc` bridged). -/
private lemma BaseChangeOf.mulOver_left (f : WeierstrassAtlasRingU.{u} →+* R)
    [((𝕌).map f).IsElliptic] :
    (mulOver ((𝕌).map f)).left ≫
      projModelBaseChangeOf f 𝕌 ((𝕌).map f) rfl =
      BaseChangeOf.pairMap f ≫ (mulOver 𝕌).left := by
  have hbc := BaseChangeOf.mulModelHom f
  have hmm : (mulOver 𝕌).left =
      WeierstrassCurve.Projective.mulModelHom 𝕌
        (𝕌).isUnit_Δ := by
    rw [ModularCurves.mulOver_left, mulModelHom_universalWeierstrassLocU]
  rw [ModularCurves.mulOver_left, hmm]
  exact hbc

/-- The associator-then-snd composite intertwines the base changes (the `mid` bridge of the
◁-side naturality; both legs meet on the triple projections). -/
private lemma BaseChangeOf.assocSnd_pairMap (f : WeierstrassAtlasRingU.{u} →+* R)
    [((𝕌).map f).IsElliptic] :
    ((α_ (modelOver ((𝕌).map f)) (modelOver ((𝕌).map f)) (modelOver ((𝕌).map f))).hom.left ≫
        pullback.snd (modelOver ((𝕌).map f)).hom
          (pullback.fst (modelOver ((𝕌).map f)).hom (modelOver ((𝕌).map f)).hom ≫
            (modelOver ((𝕌).map f)).hom)) ≫ BaseChangeOf.pairMap f =
    BaseChangeOf.tripleMap f ≫
      (α_ (modelOver 𝕌) (modelOver 𝕌) (modelOver 𝕌)).hom.left ≫
        pullback.snd (modelOver 𝕌).hom
          (pullback.fst (modelOver 𝕌).hom (modelOver 𝕌).hom ≫
            (modelOver 𝕌).hom) := by
  apply pullback.hom_ext
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((α_ (modelOver ((𝕌).map f)) (modelOver ((𝕌).map f))
        (modelOver ((𝕌).map f))).hom.left ≫
        pullback.snd (modelOver ((𝕌).map f)).hom
          (pullback.fst (modelOver ((𝕌).map f)).hom (modelOver ((𝕌).map f)).hom ≫
            (modelOver ((𝕌).map f)).hom) ≫ ·) (BaseChangeOf.pairMap_fst f)).trans ?_
    refine (Over.associator_hom_left_snd_fst_assoc (modelOver ((𝕌).map f))
        (modelOver ((𝕌).map f)) (modelOver ((𝕌).map f))
        (projModelBaseChangeOf f 𝕌 ((𝕌).map f) rfl)).trans ?_
    refine Eq.symm ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (BaseChangeOf.tripleMap f ≫ ·) (Category.assoc _ _ _)).trans ?_
    refine (congrArg (BaseChangeOf.tripleMap f ≫ ·)
        (Over.associator_hom_left_snd_fst (modelOver 𝕌)
          (modelOver 𝕌) (modelOver 𝕌))).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ pullback.snd (modelOver 𝕌).hom (modelOver 𝕌).hom)
        (BaseChangeOf.tripleMap_fst f)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (pullback.fst (modelOver ((𝕌).map f) ⊗ modelOver ((𝕌).map f)).hom
        (modelOver ((𝕌).map f)).hom ≫ ·) (BaseChangeOf.pairMap_snd f)
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((α_ (modelOver ((𝕌).map f)) (modelOver ((𝕌).map f))
        (modelOver ((𝕌).map f))).hom.left ≫
        pullback.snd (modelOver ((𝕌).map f)).hom
          (pullback.fst (modelOver ((𝕌).map f)).hom (modelOver ((𝕌).map f)).hom ≫
            (modelOver ((𝕌).map f)).hom) ≫ ·) (BaseChangeOf.pairMap_snd f)).trans ?_
    refine (Over.associator_hom_left_snd_snd_assoc (modelOver ((𝕌).map f))
        (modelOver ((𝕌).map f)) (modelOver ((𝕌).map f))
        (projModelBaseChangeOf f 𝕌 ((𝕌).map f) rfl)).trans ?_
    refine Eq.symm ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (BaseChangeOf.tripleMap f ≫ ·) (Category.assoc _ _ _)).trans ?_
    refine (congrArg (BaseChangeOf.tripleMap f ≫ ·)
        (Over.associator_hom_left_snd_snd (modelOver 𝕌)
          (modelOver 𝕌) (modelOver 𝕌))).trans ?_
    exact BaseChangeOf.tripleMap_snd f

private lemma BaseChangeOf.whisker_fst_f (f : WeierstrassAtlasRingU.{u} →+* R)
    [((𝕌).map f).IsElliptic] :
    (modelOver ((𝕌).map f) ◁ mulOver ((𝕌).map f)).left ≫
      pullback.fst (modelOver ((𝕌).map f)).hom (modelOver ((𝕌).map f)).hom =
      pullback.fst (modelOver ((𝕌).map f)).hom
        (pullback.fst (modelOver ((𝕌).map f)).hom (modelOver ((𝕌).map f)).hom ≫
          (modelOver ((𝕌).map f)).hom) :=
  Over.whiskerLeft_left_fst (mulOver ((𝕌).map f))

private lemma BaseChangeOf.whisker_fst_U :
    (modelOver 𝕌 ◁ mulOver 𝕌).left ≫
      pullback.fst (modelOver 𝕌).hom (modelOver 𝕌).hom =
      pullback.fst (modelOver 𝕌).hom
        (pullback.fst (modelOver 𝕌).hom (modelOver 𝕌).hom ≫ (modelOver 𝕌).hom) :=
  Over.whiskerLeft_left_fst (mulOver 𝕌)

private lemma BaseChangeOf.whisker_snd_f (f : WeierstrassAtlasRingU.{u} →+* R)
    [((𝕌).map f).IsElliptic] :
    (modelOver ((𝕌).map f) ◁ mulOver ((𝕌).map f)).left ≫
      pullback.snd (modelOver ((𝕌).map f)).hom (modelOver ((𝕌).map f)).hom =
      pullback.snd (modelOver ((𝕌).map f)).hom
        (pullback.fst (modelOver ((𝕌).map f)).hom (modelOver ((𝕌).map f)).hom ≫
          (modelOver ((𝕌).map f)).hom) ≫
        (mulOver ((𝕌).map f)).left :=
  Over.whiskerLeft_left_snd (mulOver ((𝕌).map f))

private lemma BaseChangeOf.whisker_snd_U :
    (modelOver 𝕌 ◁ mulOver 𝕌).left ≫
      pullback.snd (modelOver 𝕌).hom (modelOver 𝕌).hom =
      pullback.snd (modelOver 𝕌).hom
        (pullback.fst (modelOver 𝕌).hom (modelOver 𝕌).hom ≫ (modelOver 𝕌).hom) ≫
        (mulOver 𝕌).left :=
  Over.whiskerLeft_left_snd (mulOver 𝕌)

private lemma BaseChangeOf.assoc_fst_f (f : WeierstrassAtlasRingU.{u} →+* R)
    [((𝕌).map f).IsElliptic] :
    (α_ (modelOver ((𝕌).map f)) (modelOver ((𝕌).map f)) (modelOver ((𝕌).map f))).hom.left ≫
      pullback.fst (modelOver ((𝕌).map f)).hom
        (pullback.fst (modelOver ((𝕌).map f)).hom (modelOver ((𝕌).map f)).hom ≫
          (modelOver ((𝕌).map f)).hom) =
      pullback.fst (modelOver ((𝕌).map f) ⊗ modelOver ((𝕌).map f)).hom (modelOver ((𝕌).map f)).hom ≫
        pullback.fst (modelOver ((𝕌).map f)).hom (modelOver ((𝕌).map f)).hom :=
  Over.associator_hom_left_fst (modelOver ((𝕌).map f)) (modelOver ((𝕌).map f))
    (modelOver ((𝕌).map f))

private lemma BaseChangeOf.assoc_fst_U :
    (α_ (modelOver 𝕌) (modelOver 𝕌) (modelOver 𝕌)).hom.left ≫
      pullback.fst (modelOver 𝕌).hom
        (pullback.fst (modelOver 𝕌).hom (modelOver 𝕌).hom ≫ (modelOver 𝕌).hom) =
      pullback.fst (modelOver 𝕌 ⊗ modelOver 𝕌).hom (modelOver 𝕌).hom ≫
        pullback.fst (modelOver 𝕌).hom (modelOver 𝕌).hom :=
  Over.associator_hom_left_fst (modelOver 𝕌) (modelOver 𝕌) (modelOver 𝕌)

/-- The ◁-whisker/associator side of the assoc transport: the base-change naturality of
`α ≫ (mo ◁ mulOver)`, Over-spelled. -/
private lemma BaseChangeOf.assoc_whiskerLeft (f : WeierstrassAtlasRingU.{u} →+* R)
    [((𝕌).map f).IsElliptic] :
    (α_ (modelOver ((𝕌).map f)) (modelOver ((𝕌).map f)) (modelOver ((𝕌).map f))).hom.left ≫
      (modelOver ((𝕌).map f) ◁ mulOver ((𝕌).map f)).left ≫ BaseChangeOf.pairMap f =
    BaseChangeOf.tripleMap f ≫
      (α_ (modelOver 𝕌) (modelOver 𝕌) (modelOver 𝕌)).hom.left ≫
        (modelOver 𝕌 ◁ mulOver 𝕌).left := by
  apply pullback.hom_ext
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((α_ (modelOver ((𝕌).map f)) (modelOver ((𝕌).map f))
        (modelOver ((𝕌).map f))).hom.left ≫ ·) ((Category.assoc _ _ _).trans
        ((congrArg ((modelOver ((𝕌).map f) ◁ mulOver ((𝕌).map f)).left ≫ ·)
          (BaseChangeOf.pairMap_fst f)).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ projModelBaseChangeOf f 𝕌
              ((𝕌).map f) rfl) (BaseChangeOf.whisker_fst_f f)))))).trans ?_
    refine ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ projModelBaseChangeOf f 𝕌
          ((𝕌).map f) rfl) (BaseChangeOf.assoc_fst_f f))).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (pullback.fst (modelOver ((𝕌).map f) ⊗ modelOver ((𝕌).map f)).hom
        (modelOver ((𝕌).map f)).hom ≫ ·) (BaseChangeOf.pairMap_fst f).symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ pullback.fst (modelOver 𝕌).hom (modelOver 𝕌).hom)
        (BaseChangeOf.tripleMap_fst f).symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans (congrArg (BaseChangeOf.tripleMap f ≫ ·) ?_) (Category.assoc _ _ _).symm
    refine BaseChangeOf.assoc_fst_U.symm.trans ?_
    exact Eq.trans (congrArg ((α_ (modelOver 𝕌) (modelOver 𝕌)
        (modelOver 𝕌)).hom.left ≫ ·) BaseChangeOf.whisker_fst_U.symm)
      (Category.assoc _ _ _).symm
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((α_ (modelOver ((𝕌).map f)) (modelOver ((𝕌).map f))
        (modelOver ((𝕌).map f))).hom.left ≫ ·) ((Category.assoc _ _ _).trans
        ((congrArg ((modelOver ((𝕌).map f) ◁ mulOver ((𝕌).map f)).left ≫ ·)
          (BaseChangeOf.pairMap_snd f)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ projModelBaseChangeOf f 𝕌
              ((𝕌).map f) rfl) (BaseChangeOf.whisker_snd_f f)).trans
              ((Category.assoc _ _ _).trans
                (congrArg (pullback.snd (modelOver ((𝕌).map f)).hom
                  (pullback.fst (modelOver ((𝕌).map f)).hom (modelOver ((𝕌).map f)).hom ≫
                    (modelOver ((𝕌).map f)).hom) ≫ ·)
                  (BaseChangeOf.mulOver_left f)))))))).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (mulOver 𝕌).left)
        ((Category.assoc _ _ _).symm.trans (BaseChangeOf.assocSnd_pairMap f))).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans (congrArg (BaseChangeOf.tripleMap f ≫ ·) ?_) (Category.assoc _ _ _).symm
    refine (Category.assoc _ _ _).trans ?_
    exact Eq.trans (congrArg ((α_ (modelOver 𝕌) (modelOver 𝕌)
        (modelOver 𝕌)).hom.left ≫ ·) BaseChangeOf.whisker_snd_U.symm)
      (Category.assoc _ _ _).symm

/-- **(T-G4 raw assoc)** The `.left` (raw scheme-level) projection of the atlas associativity
`mulOver_assoc_atlas`, with the three `Over.comp_left`s pushed through. The `raw` input to the
associativity transport. -/
private lemma mulOver_assoc_atlas_left :
    (mulOver 𝕌 ▷ modelOver 𝕌).left ≫ (mulOver 𝕌).left =
      (α_ (modelOver 𝕌) (modelOver 𝕌) (modelOver 𝕌)).hom.left ≫
        (modelOver 𝕌 ◁ mulOver 𝕌).left ≫ (mulOver 𝕌).left := by
  have h2 := congrArg (fun m => m.left) mulOver_assoc_atlas
  rw [Over.comp_left, Over.comp_left, Over.comp_left] at h2
  exact h2

/-- **(T-W7.0g-assoc·of_map)** Associativity at the base-changed universal curve (the `h = rfl`
case). The whisker-BC naturalities are Over-spelled double-pullback-valued equations proven by
`pullback.hom_ext` on named projection lemmas (never constructing an inline triple
`pullback.map`, never crossing the Over-vs-standard instance seam inside a tactic goal); the
snd-leg is structural `Over.w`. -/
theorem mulOver_assoc_of_map (f : WeierstrassAtlasRingU.{u} →+* R)
    [((𝕌).map f).IsElliptic] :
    (mulOver ((𝕌).map f) ▷ modelOver ((𝕌).map f)) ≫
        mulOver ((𝕌).map f) =
      (α_ (modelOver ((𝕌).map f))
          (modelOver ((𝕌).map f))
          (modelOver ((𝕌).map f))).hom ≫
        (modelOver ((𝕌).map f) ◁
            mulOver ((𝕌).map f)) ≫
          mulOver ((𝕌).map f) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, Over.comp_left]
  have raw := mulOver_assoc_atlas_left
  have hL : (mulOver ((𝕌).map f) ▷
        modelOver ((𝕌).map f)).left ≫ BaseChangeOf.pairMap f =
      BaseChangeOf.tripleMap f ≫
        (mulOver 𝕌 ▷ modelOver 𝕌).left := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (BaseChangeOf.pairMap_fst f)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ _) (Over.whiskerRight_left_fst
                (mulOver ((𝕌).map f)))).trans
              ((Category.assoc _ _ _).trans
                ((congrArg (_ ≫ ·) (BaseChangeOf.mulOver_left f)).trans
                  ((Category.assoc _ _ _).symm.trans
                    ((congrArg (· ≫ _) (BaseChangeOf.tripleMap_fst f).symm).trans
                      ((Category.assoc _ _ _).trans
                        ((congrArg (_ ≫ ·) (Over.whiskerRight_left_fst
                            (mulOver 𝕌)).symm).trans
                          (Category.assoc _ _ _).symm)))))))))
    · exact (Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (BaseChangeOf.pairMap_snd f)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ _) (Over.whiskerRight_left_snd
                (mulOver ((𝕌).map f)))).trans
              ((BaseChangeOf.tripleMap_snd f).symm.trans
                ((congrArg (_ ≫ ·) (Over.whiskerRight_left_snd
                    (mulOver 𝕌)).symm).trans
                  (Category.assoc _ _ _).symm)))))
  have hR : (α_ (modelOver ((𝕌).map f))
        (modelOver ((𝕌).map f))
        (modelOver ((𝕌).map f))).hom.left ≫
      (modelOver ((𝕌).map f) ◁
        mulOver ((𝕌).map f)).left ≫ BaseChangeOf.pairMap f =
      BaseChangeOf.tripleMap f ≫
        (α_ (modelOver 𝕌) (modelOver 𝕌)
            (modelOver 𝕌)).hom.left ≫
          (modelOver 𝕌 ◁ mulOver 𝕌).left :=
    BaseChangeOf.assoc_whiskerLeft f
  -- assembly: hom_ext legs of the base-change square
  apply (isPullback_projModelBaseChangeOf f 𝕌
    ((𝕌).map f) rfl).hom_ext
  · -- fst-leg: push the multiplication across the base change on both sides, then hL/hR + raw
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((mulOver ((𝕌).map f) ▷
        modelOver ((𝕌).map f)).left ≫ ·) (BaseChangeOf.mulOver_left f)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (mulOver 𝕌).left) hL).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.symm ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((α_ (modelOver ((𝕌).map f)) (modelOver ((𝕌).map f))
        (modelOver ((𝕌).map f))).hom.left ≫ ·) (Category.assoc _ _ _)).trans ?_
    refine (congrArg (fun m => (α_ (modelOver ((𝕌).map f)) (modelOver ((𝕌).map f))
        (modelOver ((𝕌).map f))).hom.left ≫
        (modelOver ((𝕌).map f) ◁ mulOver ((𝕌).map f)).left ≫ m)
        (BaseChangeOf.mulOver_left f)).trans ?_
    refine (congrArg ((α_ (modelOver ((𝕌).map f)) (modelOver ((𝕌).map f))
        (modelOver ((𝕌).map f))).hom.left ≫ ·) (Category.assoc _ _ _).symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (mulOver 𝕌).left)
        ((Category.assoc _ _ _).trans hR)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (BaseChangeOf.tripleMap f ≫ ·) raw.symm
  · -- snd-leg: structural Over.w on both original Over morphisms
    have hga := Over.w (((mulOver ((𝕌).map f) ▷
        modelOver ((𝕌).map f)) ≫
        mulOver ((𝕌).map f)))
    have hgb := Over.w ((α_ (modelOver ((𝕌).map f))
        (modelOver ((𝕌).map f))
        (modelOver ((𝕌).map f))).hom ≫
        (modelOver ((𝕌).map f) ◁
            mulOver ((𝕌).map f)) ≫
          mulOver ((𝕌).map f))
    rw [Over.comp_left] at hga
    rw [Over.comp_left, Over.comp_left] at hgb
    exact ((Category.assoc _ _ _).symm.trans hga).trans
      (hgb.symm.trans (Category.assoc _ _ _)).symm.symm

/-- **(T-W7.0g-assoc·of_eq)** Associativity at any `W` presented as a base change; `subst`
reduces to the `of_map` case. -/
theorem mulOver_assoc_of_eq (f : WeierstrassAtlasRingU.{u} →+* R) (W : WeierstrassCurve R)
    [W.IsElliptic] (h : (𝕌).map f = W) :
    (mulOver W ▷ modelOver W) ≫ mulOver W =
      (α_ (modelOver W) (modelOver W) (modelOver W)).hom ≫
        (modelOver W ◁ mulOver W) ≫ mulOver W := by
  subst h
  exact mulOver_assoc_of_map f

/-- **(T-W7.0g-assoc)** Associativity, as the monoid-object equation in `Over (Spec R)`. -/
theorem mulOver_assoc (W : WeierstrassCurve R) [W.IsElliptic] :
    (mulOver W ▷ modelOver W) ≫ mulOver W =
      (α_ (modelOver W) (modelOver W) (modelOver W)).hom ≫
        (modelOver W ◁ mulOver W) ≫ mulOver W :=
  mulOver_assoc_of_eq (classifyRingHomU W) W (universalWeierstrassLocU_map_classifyRingHomU W)

/-- **(T-G4 raw mul-one)** The `.left` projection of the atlas right-unit law
`mulOver_oneOver_atlas`, rewritten into the raw `mulModelHom`/`pullback.fst` spelling via
`mulModelHom_universalWeierstrassLocU`. The `raw` input to the right-unit transport. -/
private lemma mulOver_oneOver_atlas_left :
    (modelOver 𝕌 ◁ oneOver 𝕌).left ≫
        WeierstrassCurve.Projective.mulModelHom 𝕌 (𝕌).isUnit_Δ =
      pullback.fst (projModelπ 𝕌)
        (𝟙 (Spec (CommRingCat.of WeierstrassAtlasRingU.{u}))) := by
  have h2 := congrArg (fun m => m.left) mulOver_oneOver_atlas
  rw [Over.comp_left, mulOver_left, Over.rightUnitor_hom_left,
    mulModelHom_universalWeierstrassLocU] at h2
  exact h2

/-- **(T-W7.0g-mul-one·of_map)** Right unit law at the base-changed universal curve
`universalWeierstrassLocU.map f` (the `h = rfl` case). The whisker-BC naturality `hnat` is
discharged by `pullback.map_comp` on both sides (the Over-monoidal `HasPullback` instance and
the standard one agree by proof irrelevance — `erw` bridges), the π-leg by the structural
`Over.w`. This is the hard proof; every general `W` reduces to it by `subst`. -/
theorem mulOver_oneOver_of_map (f : WeierstrassAtlasRingU.{u} →+* R)
    [((𝕌).map f).IsElliptic] :
    (modelOver ((𝕌).map f) ◁ oneOver ((𝕌).map f)) ≫
        mulOver ((𝕌).map f) =
      (ρ_ (modelOver ((𝕌).map f))).hom := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, mulOver_left, Over.rightUnitor_hom_left]
  have raw := mulOver_oneOver_atlas_left
  have hbc := BaseChangeOf.mulModelHom f
  have hw1 : projModelπ ((𝕌).map f) ≫ Spec.map (CommRingCat.ofHom f) =
      projModelBaseChangeOf f 𝕌
        ((𝕌).map f) rfl ≫ projModelπ 𝕌 :=
    (isPullback_projModelBaseChangeOf f 𝕌
      ((𝕌).map f) rfl).w.symm
  have hw2 : 𝟙 (Spec (CommRingCat.of R)) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom f) ≫ 𝟙 (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})) := by
    rw [Category.comp_id, Category.id_comp]
  set X :=
    pullback.map (projModelπ ((𝕌).map f)) (𝟙 (Spec (CommRingCat.of R)))
      (projModelπ 𝕌)
      (𝟙 (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))
      (projModelBaseChangeOf f 𝕌
        ((𝕌).map f) rfl)
      (Spec.map (CommRingCat.ofHom f)) (Spec.map (CommRingCat.ofHom f)) hw1 hw2 with hXdef
  have hnat : (modelOver ((𝕌).map f) ◁
        oneOver ((𝕌).map f)).left ≫
      pullbackMapBaseChangeOf f 𝕌
        ((𝕌).map f) rfl =
      X ≫ (modelOver 𝕌 ◁ oneOver 𝕌).left := by
    rw [Over.whiskerLeft_left, pullbackMapBaseChangeOf, hXdef, Over.whiskerLeft_left]
    simp only [modelOver_hom, modelOver_left, Over.tensorUnit_hom, Over.tensorUnit_left]
    erw [pullback.map_comp, pullback.map_comp]
    congr 1
    erw [oneOver_left, oneOver_left, Over.tensorUnit_hom, Over.tensorUnit_hom, Category.id_comp,
      Category.id_comp, projModelZero_baseChangeOf]
  apply (isPullback_projModelBaseChangeOf f 𝕌
    ((𝕌).map f) rfl).hom_ext
  · erw [Category.assoc, hbc, ← Category.assoc, hnat, Category.assoc, raw, hXdef, pullback.map,
      pullback.lift_fst]
    rfl
  · have hga := Over.w ((modelOver ((𝕌).map f) ◁
        oneOver ((𝕌).map f)) ≫ mulOver ((𝕌).map f))
    have hgb := Over.w (ρ_ (modelOver ((𝕌).map f))).hom
    rw [Over.comp_left, mulOver_left] at hga
    rw [Over.rightUnitor_hom_left] at hgb
    exact hga.trans hgb.symm

/-- **(T-W7.0g-mul-one·of_eq)** Right unit law at any `W` presented as a base change
`universalWeierstrassLocU.map f = W`; `subst` reduces to the `of_map` case. -/
theorem mulOver_oneOver_of_eq (f : WeierstrassAtlasRingU.{u} →+* R) (W : WeierstrassCurve R)
    [W.IsElliptic] (h : (𝕌).map f = W) :
    (modelOver W ◁ oneOver W) ≫ mulOver W = (ρ_ (modelOver W)).hom := by
  subst h
  exact mulOver_oneOver_of_map f

/-- **(T-W7.0g-mul-one)** Right unit law, for every elliptic `W` over every `R` — the classifying
map `classifyRingHomU W` presents `W` as a base change of the universal curve. -/
theorem mulOver_oneOver (W : WeierstrassCurve R) [W.IsElliptic] :
    (modelOver W ◁ oneOver W) ≫ mulOver W = (ρ_ (modelOver W)).hom :=
  mulOver_oneOver_of_eq (classifyRingHomU W) W (universalWeierstrassLocU_map_classifyRingHomU W)

/-- **(T-W7.0g-one-mul)** Left unit law — derived from the right unit `mulOver_oneOver` and
commutativity `mulOver_comm` by braiding naturality and the braiding–unitor coherence
`braiding_rightUnitor`, halving the unit-law work. -/
theorem oneOver_mulOver (W : WeierstrassCurve R) [W.IsElliptic] :
    (oneOver W ▷ modelOver W) ≫ mulOver W = (λ_ (modelOver W)).hom := by
  rw [← mulOver_comm W, ← Category.assoc, BraidedCategory.braiding_naturality_left,
    Category.assoc, mulOver_oneOver, braiding_rightUnitor]

/-- **(T-G4 raw inv-law)** The `.left` projection of the atlas inverse law
`invOver_mulOver_atlas`, rewritten into the raw `mulModelHom`/`projModelZero` spelling via
`mulModelHom_universalWeierstrassLocU`. The `raw` input to the inverse-law transport. -/
private lemma invOver_mulOver_atlas_left :
    (lift (invOver 𝕌) (𝟙 (modelOver 𝕌))).left ≫
        WeierstrassCurve.Projective.mulModelHom 𝕌 (𝕌).isUnit_Δ =
      (modelOver 𝕌).hom ≫
        (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom ≫
          projModelZero 𝕌 := by
  have h2 := congrArg (fun m => m.left) invOver_mulOver_atlas
  rw [Over.comp_left, Over.comp_left, mulOver_left, Over.toUnit_left, oneOver_left,
    mulModelHom_universalWeierstrassLocU] at h2
  exact h2

/-- **(T-W7.0g-inv-law·of_map)** The left inverse law at the base-changed universal curve
`universalWeierstrassLocU.map f` (the `h = rfl` case). The whisker-BC naturality `hnat` here has a
single-object domain (`projModel`), so it reduces by `pullback.hom_ext` to
`negModelHom_baseChange` (fst-leg) and triviality (snd-leg); the fst assembly-leg closes via the
base-change square `.w` and `projModelZero_baseChangeOf`, the π-leg by the structural `Over.w`. -/
theorem invOver_mulOver_of_map (f : WeierstrassAtlasRingU.{u} →+* R)
    [((𝕌).map f).IsElliptic] :
    lift (invOver ((𝕌).map f))
        (𝟙 (modelOver ((𝕌).map f))) ≫
        mulOver ((𝕌).map f) =
      toUnit (modelOver ((𝕌).map f)) ≫
        oneOver ((𝕌).map f) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, mulOver_left, Over.toUnit_left, oneOver_left]
  have raw := invOver_mulOver_atlas_left
  have hbc := BaseChangeOf.mulModelHom f
  have hnat : (lift (invOver ((𝕌).map f))
        (𝟙 (modelOver ((𝕌).map f)))).left ≫
      pullbackMapBaseChangeOf f 𝕌
        ((𝕌).map f) rfl =
      projModelBaseChangeOf f 𝕌
        ((𝕌).map f) rfl ≫
      (lift (invOver 𝕌)
        (𝟙 (modelOver 𝕌))).left := by
    rw [Over.lift_left, Over.lift_left]
    simp only [invOver_left, Over.id_left, pullbackMapBaseChangeOf, projModelBaseChangeOf_rfl]
    apply pullback.hom_ext
    · erw [Category.assoc, pullback.map, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
        Category.assoc, pullback.lift_fst]
      exact negModelHom_baseChange f 𝕌
    · erw [Category.assoc, pullback.map, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
        Category.assoc, pullback.lift_snd, Category.id_comp]
  apply (isPullback_projModelBaseChangeOf f 𝕌
    ((𝕌).map f) rfl).hom_ext
  · erw [Category.assoc, hbc, ← Category.assoc, hnat, Category.assoc, raw]
    simp only [modelOver_hom, Over.tensorUnit_hom]
    erw [Category.id_comp, Category.id_comp]
    have hw := (isPullback_projModelBaseChangeOf f 𝕌
      ((𝕌).map f) rfl).w
    have hz := projModelZero_baseChangeOf f 𝕌
      ((𝕌).map f) rfl
    calc projModelBaseChangeOf f 𝕌
            ((𝕌).map f) rfl ≫
          projModelπ 𝕌 ≫ projModelZero 𝕌
        = (projModelBaseChangeOf f 𝕌
              ((𝕌).map f) rfl ≫ projModelπ 𝕌) ≫
            projModelZero 𝕌 := (Category.assoc _ _ _).symm
      _ = (projModelπ ((𝕌).map f) ≫ Spec.map (CommRingCat.ofHom f)) ≫
            projModelZero 𝕌 := by rw [hw]
      _ = projModelπ ((𝕌).map f) ≫
            Spec.map (CommRingCat.ofHom f) ≫ projModelZero 𝕌 :=
          Category.assoc _ _ _
      _ = projModelπ ((𝕌).map f) ≫
            projModelZero ((𝕌).map f) ≫
            projModelBaseChangeOf f 𝕌
              ((𝕌).map f) rfl := by rw [← hz]
      _ = (projModelπ ((𝕌).map f) ≫
              projModelZero ((𝕌).map f)) ≫
            projModelBaseChangeOf f 𝕌
              ((𝕌).map f) rfl := (Category.assoc _ _ _).symm
  · have hga := Over.w (lift (invOver ((𝕌).map f))
        (𝟙 (modelOver ((𝕌).map f))) ≫
        mulOver ((𝕌).map f))
    have hgb := Over.w (toUnit (modelOver ((𝕌).map f)) ≫
        oneOver ((𝕌).map f))
    rw [Over.comp_left, mulOver_left] at hga
    rw [Over.comp_left, Over.toUnit_left, oneOver_left] at hgb
    exact hga.trans hgb.symm

/-- **(T-W7.0g-inv-law·of_eq)** The left inverse law at any `W` presented as a base change; `subst`
reduces to the `of_map` case. -/
theorem invOver_mulOver_of_eq (f : WeierstrassAtlasRingU.{u} →+* R) (W : WeierstrassCurve R)
    [W.IsElliptic] (h : (𝕌).map f = W) :
    lift (invOver W) (𝟙 (modelOver W)) ≫ mulOver W = toUnit (modelOver W) ≫ oneOver W := by
  subst h
  exact invOver_mulOver_of_map f

/-- **(T-W7.0g-inv-law)** The left inverse law, for every elliptic `W` over every `R` — via the
classifying map `classifyRingHomU W`. Consumes `negModelHom_baseChange`. -/
theorem invOver_mulOver (W : WeierstrassCurve R) [W.IsElliptic] :
    lift (invOver W) (𝟙 (modelOver W)) ≫ mulOver W = toUnit (modelOver W) ≫ oneOver W :=
  invOver_mulOver_of_eq (classifyRingHomU W) W (universalWeierstrassLocU_map_classifyRingHomU W)

end Transport

end ModularCurves

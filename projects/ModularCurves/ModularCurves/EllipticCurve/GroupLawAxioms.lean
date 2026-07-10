import ModularCurves.EllipticCurve.AdditionSpecPoints
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
instance : SmoothOfRelativeDimension 1 (projModelπ universalWeierstrassLocU.{u}) :=
  projModel_smooth universalWeierstrassLocU.{u}

instance : Smooth (projModelπ universalWeierstrassLocU.{u}) :=
  SmoothOfRelativeDimension.smooth 1 (projModelπ universalWeierstrassLocU.{u})

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
    universalWeierstrassLocU.{u}
  rw [← hy] at hpb
  exact ObjectProperty.prop_of_iso (IsIntegral ·) hpb.isoPullback (isIntegral_projModel_u _)

/-- The universe-`u` universal curve is an integral scheme. -/
instance : IsIntegral (projModel universalWeierstrassLocU.{u}) :=
  GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
    (projModelπ universalWeierstrassLocU.{u})

/-- The universe-`u` universal curve is locally noetherian. -/
instance : IsLocallyNoetherian (projModel universalWeierstrassLocU.{u}) :=
  LocallyOfFiniteType.isLocallyNoetherian (projModelπ universalWeierstrassLocU.{u})

instance : IsReduced (projModel universalWeierstrassLocU.{u}) := inferInstance

/-- **(T-W7.0e n = 2 at universe `u`)** The fibre square of the universe-`u` universal curve
is integral, hence reduced. -/
instance : IsIntegral (pullback (projModelπ universalWeierstrassLocU.{u})
    (projModelπ universalWeierstrassLocU.{u})) := inferInstance

instance : IsReduced (pullback (projModelπ universalWeierstrassLocU.{u})
    (projModelπ universalWeierstrassLocU.{u})) := inferInstance

/-- **(T-W7.0e n = 3 at universe `u`)** The fibre cube, `snd`-associated spelling. -/
instance : IsIntegral (pullback (projModelπ universalWeierstrassLocU.{u})
    (pullback.snd (projModelπ universalWeierstrassLocU.{u})
      (projModelπ universalWeierstrassLocU.{u}) ≫ projModelπ universalWeierstrassLocU.{u})) :=
  inferInstance

/-- **(T-W7.0e n = 3 at universe `u`)** The fibre cube, `fst`-associated spelling. -/
instance : IsIntegral (pullback
    (pullback.fst (projModelπ universalWeierstrassLocU.{u})
      (projModelπ universalWeierstrassLocU.{u}) ≫ projModelπ universalWeierstrassLocU.{u})
    (projModelπ universalWeierstrassLocU.{u})) := inferInstance

instance : IsReduced (pullback (projModelπ universalWeierstrassLocU.{u})
    (pullback.snd (projModelπ universalWeierstrassLocU.{u})
      (projModelπ universalWeierstrassLocU.{u}) ≫ projModelπ universalWeierstrassLocU.{u})) :=
  inferInstance

instance : IsReduced (pullback
    (pullback.fst (projModelπ universalWeierstrassLocU.{u})
      (projModelπ universalWeierstrassLocU.{u}) ≫ projModelπ universalWeierstrassLocU.{u})
    (projModelπ universalWeierstrassLocU.{u})) := inferInstance

/-! ## T-G2/T-G3 — the atlas equations, by field-points extensionality + the c6 spec

Every equation is proven on an arbitrary field-valued point `p` of the relevant fibre power:
decompose `p` into its `SpecPoints` legs (the canonical algebra on `K` comes from
`Spec.preimage` of the structure composite), evaluate both sides through the c6 spec
`mulModelHom_specPoints` (and `negModelHom_specPoints` / `projModelPointsEquiv_zero`), apply
the corresponding group law on `Affine.Point`, and close by injectivity of the dictionary. -/

section AtlasEquations

/-- **(T-G3-comm)** Commutativity of the two-law multiplication at the universe-`u` atlas:
swapping the factors of `E ×_U E` does not change the product. -/
theorem mulModelHom_comm_atlas :
    (pullbackSymmetry (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u})).hom ≫ (mulModelHom universalWeierstrassLocU.{u}) = (mulModelHom universalWeierstrassLocU.{u}) := by
  classical
  refine hom_ext_of_forall_specPoint fun K _ p => ?_
  -- the canonical algebra on `K`, from the structure composite of the first leg
  letI : Algebra WeierstrassAtlasRingU.{u} K :=
    ((Spec.preimage (p ≫ pullback.fst (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u}) ≫ (projModelπ universalWeierstrassLocU.{u}))).hom).toAlgebra
  have hσ : p ≫ pullback.fst (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u}) ≫ (projModelπ universalWeierstrassLocU.{u}) =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    have h1 : CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K) =
        Spec.preimage (p ≫ pullback.fst (projModelπ universalWeierstrassLocU.{u})
          (projModelπ universalWeierstrassLocU.{u}) ≫ (projModelπ universalWeierstrassLocU.{u})) :=
      CommRingCat.ofHom_hom _
    rw [h1, Spec.map_preimage]
  have hπP : (p ≫ pullback.fst (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u})) ≫ (projModelπ universalWeierstrassLocU.{u}) =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    rw [Category.assoc]; exact hσ
  have hπQ : (p ≫ pullback.snd (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u})) ≫ (projModelπ universalWeierstrassLocU.{u}) =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]; exact hπP
  -- both sides at `p` are spec-shaped lifts
  have hQP := mulModelHom_specPoints universalWeierstrassLocU.{u} K
    ⟨p ≫ pullback.snd (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u}), hπQ⟩ ⟨p ≫ pullback.fst (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u}), hπP⟩
  have hPQ := mulModelHom_specPoints universalWeierstrassLocU.{u} K
    ⟨p ≫ pullback.fst (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u}), hπP⟩ ⟨p ≫ pullback.snd (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u}), hπQ⟩
  have keyval := congrArg Subtype.val
    ((projModelPointsEquiv universalWeierstrassLocU.{u} K).injective
      (hQP.trans ((add_comm _ _).trans hPQ.symm)))
  have hL : p ≫ ((pullbackSymmetry (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u})).hom ≫ (mulModelHom universalWeierstrassLocU.{u})) =
      pullback.lift (p ≫ pullback.snd (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u})) (p ≫ pullback.fst (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u}))
        (hπQ.trans hπP.symm) ≫ (mulModelHom universalWeierstrassLocU.{u}) := by
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, pullback.lift_fst]
    · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.lift_snd]
  have hR : p = pullback.lift (p ≫ pullback.fst (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u})) (p ≫ pullback.snd (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u}))
      (hπP.trans hπQ.symm) := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd]
  exact hL.trans (keyval.trans (congrArg (· ≫ (mulModelHom universalWeierstrassLocU.{u})) hR.symm))

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
  haveI hred : IsReduced (((modelOver universalWeierstrassLocU.{u} ⊗
      modelOver universalWeierstrassLocU.{u}) ⊗ modelOver universalWeierstrassLocU.{u}).left) :=
    inferInstanceAs (IsReduced (pullback
      (pullback.fst (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u}) ≫ (projModelπ universalWeierstrassLocU.{u})) (projModelπ universalWeierstrassLocU.{u})))
  haveI hsep : ((modelOver universalWeierstrassLocU.{u}).left).IsSeparated :=
    inferInstanceAs ((projModel universalWeierstrassLocU.{u}).IsSeparated)
  refine hom_ext_of_forall_specPoint fun K _ p => ?_
  -- three legs of the cube point (all projModelπ-spelled; defeq to the `.hom` tensor form)
  letI : Algebra WeierstrassAtlasRingU.{u} K :=
    ((Spec.preimage ((p ≫
      pullback.fst (pullback.fst (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u}) ≫ (projModelπ universalWeierstrassLocU.{u})) (projModelπ universalWeierstrassLocU.{u}) ≫
      pullback.fst (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u})) ≫ (projModelπ universalWeierstrassLocU.{u}))).hom).toAlgebra
  have hπ₁ : ((p ≫ pullback.fst (pullback.fst (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u}) ≫ (projModelπ universalWeierstrassLocU.{u})) (projModelπ universalWeierstrassLocU.{u}) ≫
      pullback.fst (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u})) ≫ (projModelπ universalWeierstrassLocU.{u})) =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    have h1 : CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K) =
        Spec.preimage ((p ≫ pullback.fst (pullback.fst (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u}) ≫ (projModelπ universalWeierstrassLocU.{u})) (projModelπ universalWeierstrassLocU.{u}) ≫
          pullback.fst (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u})) ≫ (projModelπ universalWeierstrassLocU.{u})) :=
      CommRingCat.ofHom_hom _
    rw [h1, Spec.map_preimage]
  have hπ₂ : ((p ≫ pullback.fst (pullback.fst (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u}) ≫ (projModelπ universalWeierstrassLocU.{u})) (projModelπ universalWeierstrassLocU.{u}) ≫
      pullback.snd (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u})) ≫ (projModelπ universalWeierstrassLocU.{u})) =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    rw [← hπ₁]
    simp only [Category.assoc]
    congr 2
    exact pullback.condition.symm
  have hπ₃ : ((p ≫ pullback.snd (pullback.fst (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u}) ≫ (projModelπ universalWeierstrassLocU.{u})) (projModelπ universalWeierstrassLocU.{u})) ≫ (projModelπ universalWeierstrassLocU.{u})) =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    rw [← hπ₁]
    simp only [Category.assoc]
    exact congrArg (p ≫ ·)
      (pullback.condition (f := pullback.fst (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u}) ≫ (projModelπ universalWeierstrassLocU.{u})) (g := (projModelπ universalWeierstrassLocU.{u}))).symm
  have hP₁₂ := mulModelHom_specPoints universalWeierstrassLocU.{u} K ⟨_, hπ₁⟩ ⟨_, hπ₂⟩
  have hP₂₃ := mulModelHom_specPoints universalWeierstrassLocU.{u} K ⟨_, hπ₂⟩ ⟨_, hπ₃⟩
  have hπ₁₂ : (pullback.lift _ _ ((hπ₁).trans (hπ₂).symm) ≫
      mulModelHom universalWeierstrassLocU.{u}) ≫ (projModelπ universalWeierstrassLocU.{u}) =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    rw [Category.assoc, show mulModelHom universalWeierstrassLocU.{u} ≫ (projModelπ universalWeierstrassLocU.{u}) = _ from mulModelHom_π universalWeierstrassLocU.{u},
      ← Category.assoc, pullback.lift_fst]
    exact hπ₁
  have hπ₂₃ : (pullback.lift _ _ ((hπ₂).trans (hπ₃).symm) ≫
      mulModelHom universalWeierstrassLocU.{u}) ≫ (projModelπ universalWeierstrassLocU.{u}) =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    rw [Category.assoc, show mulModelHom universalWeierstrassLocU.{u} ≫ (projModelπ universalWeierstrassLocU.{u}) = _ from mulModelHom_π universalWeierstrassLocU.{u},
      ← Category.assoc, pullback.lift_fst]
    exact hπ₂
  have hL2 := mulModelHom_specPoints universalWeierstrassLocU.{u} K ⟨_, hπ₁₂⟩ ⟨_, hπ₃⟩
  have hR2 := mulModelHom_specPoints universalWeierstrassLocU.{u} K ⟨_, hπ₁⟩ ⟨_, hπ₂₃⟩
  have e2 : projModelPointsEquiv universalWeierstrassLocU.{u} K ⟨_, hπ₁₂⟩ =
      projModelPointsEquiv universalWeierstrassLocU.{u} K ⟨_, hπ₁⟩ +
      projModelPointsEquiv universalWeierstrassLocU.{u} K ⟨_, hπ₂⟩ :=
    (congrArg (projModelPointsEquiv universalWeierstrassLocU.{u} K) (Subtype.ext rfl)).trans hP₁₂
  have e4 : projModelPointsEquiv universalWeierstrassLocU.{u} K ⟨_, hπ₂₃⟩ =
      projModelPointsEquiv universalWeierstrassLocU.{u} K ⟨_, hπ₂⟩ +
      projModelPointsEquiv universalWeierstrassLocU.{u} K ⟨_, hπ₃⟩ :=
    (congrArg (projModelPointsEquiv universalWeierstrassLocU.{u} K) (Subtype.ext rfl)).trans hP₂₃
  have ebigL := hL2.trans
    (congrArg (· + projModelPointsEquiv universalWeierstrassLocU.{u} K ⟨_, hπ₃⟩) e2)
  have ebigR := hR2.trans
    (congrArg (projModelPointsEquiv universalWeierstrassLocU.{u} K ⟨_, hπ₁⟩ + ·) e4)
  have keyval : (pullback.lift _ _ ((hπ₁₂).trans (hπ₃).symm) ≫ mulModelHom universalWeierstrassLocU.{u}) =
      (pullback.lift _ _ ((hπ₁).trans (hπ₂₃).symm) ≫ mulModelHom universalWeierstrassLocU.{u}) :=
    congrArg Subtype.val
      ((projModelPointsEquiv universalWeierstrassLocU.{u} K).injective
        (ebigL.trans ((add_assoc _ _ _).trans ebigR.symm)))
  -- outer first projection of the cube through the (mo⊗mo)-factor is the (f,g) input lift
  have hp₁₂p :
      p ≫ pullback.fst (pullback.fst (projModelπ universalWeierstrassLocU.{u})
              (projModelπ universalWeierstrassLocU.{u}) ≫ projModelπ universalWeierstrassLocU.{u})
            (projModelπ universalWeierstrassLocU.{u}) =
        pullback.lift
          (p ≫ pullback.fst (pullback.fst (projModelπ universalWeierstrassLocU.{u})
                  (projModelπ universalWeierstrassLocU.{u}) ≫ projModelπ universalWeierstrassLocU.{u})
                (projModelπ universalWeierstrassLocU.{u}) ≫
            pullback.fst (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u}))
          (p ≫ pullback.fst (pullback.fst (projModelπ universalWeierstrassLocU.{u})
                  (projModelπ universalWeierstrassLocU.{u}) ≫ projModelπ universalWeierstrassLocU.{u})
                (projModelπ universalWeierstrassLocU.{u}) ≫
            pullback.snd (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u}))
          (hπ₁.trans hπ₂.symm) := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc]
    · rw [pullback.lift_snd, Category.assoc]
  -- associator middle leg: p through α to the (g,h)-factor is the (g,h) input lift
  have hq :
      p ≫ (α_ (modelOver universalWeierstrassLocU.{u}) (modelOver universalWeierstrassLocU.{u})
            (modelOver universalWeierstrassLocU.{u})).hom.left ≫
          pullback.snd (projModelπ universalWeierstrassLocU.{u})
            (pullback.fst (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u}) ≫
              projModelπ universalWeierstrassLocU.{u}) =
        pullback.lift
          (p ≫ pullback.fst (pullback.fst (projModelπ universalWeierstrassLocU.{u})
                  (projModelπ universalWeierstrassLocU.{u}) ≫ projModelπ universalWeierstrassLocU.{u})
                (projModelπ universalWeierstrassLocU.{u}) ≫
            pullback.snd (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u}))
          (p ≫ pullback.snd (pullback.fst (projModelπ universalWeierstrassLocU.{u})
                  (projModelπ universalWeierstrassLocU.{u}) ≫ projModelπ universalWeierstrassLocU.{u})
                (projModelπ universalWeierstrassLocU.{u}))
          (hπ₂.trans hπ₃.symm) := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, Category.assoc]
      exact congrArg (p ≫ ·) (Over.associator_hom_left_snd_fst _ _ _)
    · rw [pullback.lift_snd, Category.assoc, Category.assoc]
      exact congrArg (p ≫ ·) (Over.associator_hom_left_snd_snd _ _ _)
  have hL : p ≫ ((mulOver universalWeierstrassLocU.{u} ▷ modelOver universalWeierstrassLocU.{u}) ≫
        mulOver universalWeierstrassLocU.{u}).left =
      pullback.lift _ _ ((hπ₁₂).trans (hπ₃).symm) ≫ mulModelHom universalWeierstrassLocU.{u} := by
    rw [Over.comp_left, mulOver_left, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans
        ((congrArg (p ≫ ·) (Over.whiskerRight_left_fst (mulOver universalWeierstrassLocU.{u}))).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ mulModelHom universalWeierstrassLocU.{u}) hp₁₂p).trans
              (pullback.lift_fst _ _ _).symm)))
    · exact (Category.assoc _ _ _).trans
        ((congrArg (p ≫ ·) (Over.whiskerRight_left_snd (mulOver universalWeierstrassLocU.{u}))).trans
          (pullback.lift_snd _ _ _).symm)
  -- associator side, pre-`mul` lift identity
  have hR0 : p ≫ ((α_ (modelOver universalWeierstrassLocU.{u}) (modelOver universalWeierstrassLocU.{u})
        (modelOver universalWeierstrassLocU.{u})).hom.left ≫
        (modelOver universalWeierstrassLocU.{u} ◁ mulOver universalWeierstrassLocU.{u}).left) =
      pullback.lift _ _ ((hπ₁).trans (hπ₂₃).symm) := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans
        ((congrArg (p ≫ ·)
          ((Category.assoc _ _ _).trans
            ((congrArg ((α_ (modelOver universalWeierstrassLocU.{u})
                  (modelOver universalWeierstrassLocU.{u})
                  (modelOver universalWeierstrassLocU.{u})).hom.left ≫ ·)
                (Over.whiskerLeft_left_fst (mulOver universalWeierstrassLocU.{u}))).trans
              (Over.associator_hom_left_fst _ _ _)))).trans
          (pullback.lift_fst _ _ _).symm)
    · exact (Category.assoc _ _ _).trans
        ((congrArg (p ≫ ·)
            ((Category.assoc _ _ _).trans
              (congrArg ((α_ (modelOver universalWeierstrassLocU.{u})
                  (modelOver universalWeierstrassLocU.{u})
                  (modelOver universalWeierstrassLocU.{u})).hom.left ≫ ·)
                (Over.whiskerLeft_left_snd (mulOver universalWeierstrassLocU.{u}))))).trans
          ((congrArg (p ≫ ·) (Category.assoc _ _ _).symm).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (· ≫ mulModelHom universalWeierstrassLocU.{u}) hq).trans
                (pullback.lift_snd _ _ _).symm))))
  have hR : p ≫ ((α_ (modelOver universalWeierstrassLocU.{u}) (modelOver universalWeierstrassLocU.{u})
        (modelOver universalWeierstrassLocU.{u})).hom ≫
        (modelOver universalWeierstrassLocU.{u} ◁ mulOver universalWeierstrassLocU.{u}) ≫
        mulOver universalWeierstrassLocU.{u}).left =
      pullback.lift _ _ ((hπ₁).trans (hπ₂₃).symm) ≫ mulModelHom universalWeierstrassLocU.{u} := by
    rw [Over.comp_left, Over.comp_left, mulOver_left]
    exact ((congrArg (p ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm).trans
      (congrArg (· ≫ mulModelHom universalWeierstrassLocU.{u}) hR0)
  exact hL.trans (keyval.trans hR.symm)

end AtlasEquations

end ModularCurves

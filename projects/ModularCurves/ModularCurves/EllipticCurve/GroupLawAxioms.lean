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

/-- **(T-G3-comm, Over level)** Commutativity as the braided monoid-object equation at the
atlas — the `Over`-level wrapper of `mulModelHom_comm_atlas`. -/
theorem mulOver_comm_atlas :
    (β_ (modelOver universalWeierstrassLocU.{u}) (modelOver universalWeierstrassLocU.{u})).hom ≫ mulOver universalWeierstrassLocU.{u} = mulOver universalWeierstrassLocU.{u} := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.braiding_hom_left, mulOver_left]
  exact mulModelHom_comm_atlas

/-- **(T-G3-one-mul)** Left unit law at the atlas. -/
theorem oneOver_mulOver_atlas :
    (oneOver universalWeierstrassLocU.{u} ▷ modelOver universalWeierstrassLocU.{u}) ≫ mulOver universalWeierstrassLocU.{u} = (λ_ (modelOver universalWeierstrassLocU.{u})).hom := by
  classical
  apply Over.OverMorphism.ext
  rw [Over.comp_left, mulOver_left, Over.leftUnitor_hom_left]
  haveI : IsReduced ((𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u}))) ⊗
      modelOver universalWeierstrassLocU.{u}).left) :=
    ObjectProperty.prop_of_iso (IsReduced ·)
      ((Over.forget _).mapIso (λ_ (modelOver universalWeierstrassLocU.{u}))).symm
      (inferInstanceAs (IsReduced (projModel universalWeierstrassLocU.{u})))
  haveI : (modelOver universalWeierstrassLocU.{u}).left.IsSeparated :=
    inferInstanceAs ((projModel universalWeierstrassLocU.{u}).IsSeparated)
  refine hom_ext_of_forall_specPoint fun K _ p => ?_
  letI : Algebra WeierstrassAtlasRingU.{u} K :=
    ((Spec.preimage ((p ≫ pullback.snd (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom
      (projModelπ universalWeierstrassLocU.{u})) ≫ projModelπ universalWeierstrassLocU.{u})).hom).toAlgebra
  have hσ : (p ≫ pullback.snd (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom
      (projModelπ universalWeierstrassLocU.{u})) ≫ projModelπ universalWeierstrassLocU.{u} =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    have h1 : CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K) =
        Spec.preimage ((p ≫ pullback.snd (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom
          (projModelπ universalWeierstrassLocU.{u})) ≫ projModelπ universalWeierstrassLocU.{u}) :=
      CommRingCat.ofHom_hom _
    rw [h1, Spec.map_preimage]
  have hπZ : (Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) ≫
      projModelZero universalWeierstrassLocU.{u}) ≫ projModelπ universalWeierstrassLocU.{u} =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    rw [Category.assoc, projModelZero_projModelπ, Category.comp_id]
  have hcond : pullback.fst (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom
      (projModelπ universalWeierstrassLocU.{u}) ≫
      (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom =
      pullback.snd (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom
      (projModelπ universalWeierstrassLocU.{u}) ≫ projModelπ universalWeierstrassLocU.{u} :=
    pullback.condition
  have hfstσ : (p ≫ pullback.fst (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom
      (projModelπ universalWeierstrassLocU.{u})) ≫
      (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) :=
    (Category.assoc _ _ _).trans ((congrArg (p ≫ ·) hcond).trans
      ((Category.assoc _ _ _).symm.trans hσ))
  have hZeval : p ≫ (pullback.fst (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom
      (projModelπ universalWeierstrassLocU.{u}) ≫ (oneOver universalWeierstrassLocU.{u}).left) =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) ≫
        projModelZero universalWeierstrassLocU.{u} := by
    rw [oneOver_left]
    exact (Category.assoc _ _ _).symm.trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ projModelZero universalWeierstrassLocU.{u}) hfstσ))
  have hspec := mulModelHom_specPoints universalWeierstrassLocU.{u} K
    ⟨Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) ≫
      projModelZero universalWeierstrassLocU.{u}, hπZ⟩
    ⟨p ≫ pullback.snd (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom
      (projModelπ universalWeierstrassLocU.{u}), hσ⟩
  have hkey := congrArg Subtype.val
    ((projModelPointsEquiv universalWeierstrassLocU.{u} K).injective
      (hspec.trans ((congrArg (· + projModelPointsEquiv universalWeierstrassLocU.{u} K
          ⟨p ≫ pullback.snd (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom
            (projModelπ universalWeierstrassLocU.{u}), hσ⟩)
          (projModelPointsEquiv_zero universalWeierstrassLocU.{u} K)).trans (zero_add _))))
  have hL : p ≫ ((oneOver universalWeierstrassLocU.{u} ▷ modelOver universalWeierstrassLocU.{u}).left ≫
        mulModelHom universalWeierstrassLocU.{u}) =
      pullback.lift _ _ (hπZ.trans hσ.symm) ≫ mulModelHom universalWeierstrassLocU.{u} := by
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans
        ((congrArg (p ≫ ·) (Over.whiskerRight_left_fst (oneOver universalWeierstrassLocU.{u}))).trans
          (hZeval.trans (pullback.lift_fst _ _ _).symm))
    · exact (Category.assoc _ _ _).trans
        ((congrArg (p ≫ ·) (Over.whiskerRight_left_snd (oneOver universalWeierstrassLocU.{u}))).trans
          (pullback.lift_snd _ _ _).symm)
  exact hL.trans hkey

/-- **(T-G3-mul-one)** Right unit law at the atlas. -/
theorem mulOver_oneOver_atlas :
    (modelOver universalWeierstrassLocU.{u} ◁ oneOver universalWeierstrassLocU.{u}) ≫ mulOver universalWeierstrassLocU.{u} = (ρ_ (modelOver universalWeierstrassLocU.{u})).hom := by
  classical
  apply Over.OverMorphism.ext
  rw [Over.comp_left, mulOver_left, Over.rightUnitor_hom_left]
  haveI : IsReduced ((modelOver universalWeierstrassLocU.{u} ⊗
      𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).left) :=
    ObjectProperty.prop_of_iso (IsReduced ·)
      ((Over.forget _).mapIso (ρ_ (modelOver universalWeierstrassLocU.{u}))).symm
      (inferInstanceAs (IsReduced (projModel universalWeierstrassLocU.{u})))
  haveI : (modelOver universalWeierstrassLocU.{u}).left.IsSeparated :=
    inferInstanceAs ((projModel universalWeierstrassLocU.{u}).IsSeparated)
  refine hom_ext_of_forall_specPoint fun K _ p => ?_
  letI : Algebra WeierstrassAtlasRingU.{u} K :=
    ((Spec.preimage ((p ≫ pullback.fst (projModelπ universalWeierstrassLocU.{u})
      (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom) ≫
        projModelπ universalWeierstrassLocU.{u})).hom).toAlgebra
  have hσ : (p ≫ pullback.fst (projModelπ universalWeierstrassLocU.{u})
      (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom) ≫
      projModelπ universalWeierstrassLocU.{u} =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    have h1 : CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K) =
        Spec.preimage ((p ≫ pullback.fst (projModelπ universalWeierstrassLocU.{u})
          (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom) ≫
            projModelπ universalWeierstrassLocU.{u}) :=
      CommRingCat.ofHom_hom _
    rw [h1, Spec.map_preimage]
  have hπZ : (Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) ≫
      projModelZero universalWeierstrassLocU.{u}) ≫ projModelπ universalWeierstrassLocU.{u} =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    rw [Category.assoc, projModelZero_projModelπ, Category.comp_id]
  have hcond : pullback.fst (projModelπ universalWeierstrassLocU.{u})
      (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom ≫
      projModelπ universalWeierstrassLocU.{u} =
      pullback.snd (projModelπ universalWeierstrassLocU.{u})
      (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom ≫
      (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom :=
    pullback.condition
  have hsndσ : (p ≫ pullback.snd (projModelπ universalWeierstrassLocU.{u})
      (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom) ≫
      (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) :=
    (Category.assoc _ _ _).trans ((congrArg (p ≫ ·) hcond.symm).trans
      ((Category.assoc _ _ _).symm.trans hσ))
  have hZeval : p ≫ (pullback.snd (projModelπ universalWeierstrassLocU.{u})
      (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom ≫
        (oneOver universalWeierstrassLocU.{u}).left) =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) ≫
        projModelZero universalWeierstrassLocU.{u} := by
    rw [oneOver_left]
    exact (Category.assoc _ _ _).symm.trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ projModelZero universalWeierstrassLocU.{u}) hsndσ))
  have hspec := mulModelHom_specPoints universalWeierstrassLocU.{u} K
    ⟨p ≫ pullback.fst (projModelπ universalWeierstrassLocU.{u})
      (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom, hσ⟩
    ⟨Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) ≫
      projModelZero universalWeierstrassLocU.{u}, hπZ⟩
  have hkey := congrArg Subtype.val
    ((projModelPointsEquiv universalWeierstrassLocU.{u} K).injective
      (hspec.trans ((congrArg (projModelPointsEquiv universalWeierstrassLocU.{u} K
          ⟨p ≫ pullback.fst (projModelπ universalWeierstrassLocU.{u})
            (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom, hσ⟩ + ·)
          (projModelPointsEquiv_zero universalWeierstrassLocU.{u} K)).trans (add_zero _))))
  have hL : p ≫ ((modelOver universalWeierstrassLocU.{u} ◁ oneOver universalWeierstrassLocU.{u}).left ≫
        mulModelHom universalWeierstrassLocU.{u}) =
      pullback.lift _ _ (hσ.trans hπZ.symm) ≫ mulModelHom universalWeierstrassLocU.{u} := by
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans
        ((congrArg (p ≫ ·) (Over.whiskerLeft_left_fst (oneOver universalWeierstrassLocU.{u}))).trans
          (pullback.lift_fst _ _ _).symm)
    · exact (Category.assoc _ _ _).trans
        ((congrArg (p ≫ ·) (Over.whiskerLeft_left_snd (oneOver universalWeierstrassLocU.{u}))).trans
          (hZeval.trans (pullback.lift_snd _ _ _).symm))
  exact hL.trans hkey

/-- **(T-G3-inv)** Left inverse law at the atlas. -/
theorem invOver_mulOver_atlas :
    lift (invOver universalWeierstrassLocU.{u}) (𝟙 (modelOver universalWeierstrassLocU.{u})) ≫ mulOver universalWeierstrassLocU.{u} =
      toUnit (modelOver universalWeierstrassLocU.{u}) ≫ oneOver universalWeierstrassLocU.{u} := by
  classical
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, mulOver_left, Over.toUnit_left, oneOver_left]
  haveI : IsReduced (modelOver universalWeierstrassLocU.{u}).left :=
    inferInstanceAs (IsReduced (projModel universalWeierstrassLocU.{u}))
  haveI : (modelOver universalWeierstrassLocU.{u}).left.IsSeparated :=
    inferInstanceAs ((projModel universalWeierstrassLocU.{u}).IsSeparated)
  refine hom_ext_of_forall_specPoint fun K _ p => ?_
  letI : Algebra WeierstrassAtlasRingU.{u} K :=
    ((Spec.preimage (p ≫ projModelπ universalWeierstrassLocU.{u})).hom).toAlgebra
  have hσ : p ≫ projModelπ universalWeierstrassLocU.{u} =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    have h1 : CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K) =
        Spec.preimage (p ≫ projModelπ universalWeierstrassLocU.{u}) :=
      CommRingCat.ofHom_hom _
    rw [h1, Spec.map_preimage]
  have hπneg : (p ≫ negModelHom universalWeierstrassLocU.{u}) ≫ projModelπ universalWeierstrassLocU.{u} =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) :=
    (Category.assoc _ _ _).trans
      ((congrArg (p ≫ ·) (negModelHom_π universalWeierstrassLocU.{u})).trans hσ)
  have hπZ : (Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) ≫
      projModelZero universalWeierstrassLocU.{u}) ≫ projModelπ universalWeierstrassLocU.{u} =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) := by
    rw [Category.assoc, projModelZero_projModelπ, Category.comp_id]
  have hspec := mulModelHom_specPoints universalWeierstrassLocU.{u} K
    ⟨p ≫ negModelHom universalWeierstrassLocU.{u}, hπneg⟩ ⟨p, hσ⟩
  have hneg := negModelHom_specPoints universalWeierstrassLocU.{u} K ⟨p, hσ⟩
  have hkey := congrArg Subtype.val
    ((projModelPointsEquiv universalWeierstrassLocU.{u} K).injective
      ((hspec.trans ((congrArg (· + projModelPointsEquiv universalWeierstrassLocU.{u} K ⟨p, hσ⟩) hneg).trans
          (neg_add_cancel _))).trans
        (projModelPointsEquiv_zero universalWeierstrassLocU.{u} K).symm))
  have hL : p ≫ ((lift (invOver universalWeierstrassLocU.{u})
        (𝟙 (modelOver universalWeierstrassLocU.{u}))).left ≫
        mulModelHom universalWeierstrassLocU.{u}) =
      pullback.lift _ _ (hπneg.trans hσ.symm) ≫ mulModelHom universalWeierstrassLocU.{u} := by
    rw [Over.lift_left, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans
        ((congrArg (p ≫ ·) (pullback.lift_fst _ _ _)).trans
          ((congrArg (p ≫ ·) (invOver_left universalWeierstrassLocU.{u})).trans
            (pullback.lift_fst _ _ _).symm))
    · exact (Category.assoc _ _ _).trans
        ((congrArg (p ≫ ·) (pullback.lift_snd _ _ _)).trans
          ((congrArg (p ≫ ·) (Over.id_left (modelOver universalWeierstrassLocU.{u}))).trans
            ((Category.comp_id p).trans (pullback.lift_snd _ _ _).symm)))
  have hRHS : p ≫ ((modelOver universalWeierstrassLocU.{u}).hom ≫
      ((𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom ≫
        projModelZero universalWeierstrassLocU.{u})) =
      Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} K)) ≫
        projModelZero universalWeierstrassLocU.{u} := by
    rw [Over.tensorUnit_hom, Category.id_comp, ← Category.assoc]
    exact congrArg (· ≫ projModelZero universalWeierstrassLocU.{u}) hσ
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
  have raw : (pullbackSymmetry (projModelπ universalWeierstrassLocU.{u})
        (projModelπ universalWeierstrassLocU.{u})).hom ≫
      WeierstrassCurve.Projective.mulModelHom universalWeierstrassLocU.{u}
        universalWeierstrassLocU.isUnit_Δ =
      WeierstrassCurve.Projective.mulModelHom universalWeierstrassLocU.{u}
        universalWeierstrassLocU.isUnit_Δ := by
    rw [← mulModelHom_universalWeierstrassLocU]; exact mulModelHom_comm_atlas
  have hbc : mulModelHom W ≫ projModelBaseChangeOf (classifyRingHomU W)
        universalWeierstrassLocU.{u} W (universalWeierstrassLocU_map_classifyRingHomU W) =
      pullbackMapBaseChangeOf (classifyRingHomU W) universalWeierstrassLocU.{u} W
        (universalWeierstrassLocU_map_classifyRingHomU W) ≫
      WeierstrassCurve.Projective.mulModelHom universalWeierstrassLocU.{u}
        universalWeierstrassLocU.isUnit_Δ :=
    mulModelHomBC_baseChange (classifyRingHomU W) universalWeierstrassLocU.{u}
      universalWeierstrassLocU.isUnit_Δ W (universalWeierstrassLocU_map_classifyRingHomU W)
  have hsym : (pullbackSymmetry (projModelπ W) (projModelπ W)).hom ≫
      pullbackMapBaseChangeOf (classifyRingHomU W) universalWeierstrassLocU.{u} W
        (universalWeierstrassLocU_map_classifyRingHomU W) =
      pullbackMapBaseChangeOf (classifyRingHomU W) universalWeierstrassLocU.{u} W
        (universalWeierstrassLocU_map_classifyRingHomU W) ≫
      (pullbackSymmetry (projModelπ universalWeierstrassLocU.{u})
        (projModelπ universalWeierstrassLocU.{u})).hom := by
    apply pullback.hom_ext <;>
      simp only [pullbackMapBaseChangeOf, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd,
        pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_snd_assoc,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  apply (isPullback_projModelBaseChangeOf (classifyRingHomU W) universalWeierstrassLocU.{u} W
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
private lemma modelOver_hom_baseChangeOf (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic] :
    (modelOver (universalWeierstrassLocU.{u}.map f)).hom ≫ Spec.map (CommRingCat.ofHom f) =
      projModelBaseChangeOf f universalWeierstrassLocU.{u}
          (universalWeierstrassLocU.{u}.map f) rfl ≫
        (modelOver universalWeierstrassLocU.{u}).hom := by
  simp only [modelOver_hom]
  exact (isPullback_projModelBaseChangeOf f universalWeierstrassLocU.{u}
    (universalWeierstrassLocU.{u}.map f) rfl).w.symm

/-- (e₁) The tensor-square base-change compatibility over `Spec`: the tensor structure map
commutes with the fibre-square base change (`docs/tg4/mulOver_assoc.plan.md`, banked). -/
private lemma tensorObj_hom_baseChangeOf (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic] :
    (modelOver (universalWeierstrassLocU.{u}.map f) ⊗
        modelOver (universalWeierstrassLocU.{u}.map f)).hom ≫
      Spec.map (CommRingCat.ofHom f) =
      pullbackMapBaseChangeOf f universalWeierstrassLocU.{u}
          (universalWeierstrassLocU.{u}.map f) rfl ≫
        (modelOver universalWeierstrassLocU.{u} ⊗ modelOver universalWeierstrassLocU.{u}).hom := by
  rw [Over.tensorObj_hom, Over.tensorObj_hom]
  simp only [modelOver_hom]
  have hmap : pullbackMapBaseChangeOf f universalWeierstrassLocU.{u}
      (universalWeierstrassLocU.{u}.map f) rfl ≫
      pullback.fst (projModelπ universalWeierstrassLocU.{u})
        (projModelπ universalWeierstrassLocU.{u}) =
      pullback.fst (projModelπ (universalWeierstrassLocU.{u}.map f))
        (projModelπ (universalWeierstrassLocU.{u}.map f)) ≫
        projModelBaseChangeOf f universalWeierstrassLocU.{u}
          (universalWeierstrassLocU.{u}.map f) rfl := by
    erw [pullbackMapBaseChangeOf, pullback.map, pullback.lift_fst]
  have hw := (isPullback_projModelBaseChangeOf f universalWeierstrassLocU.{u}
    (universalWeierstrassLocU.{u}.map f) rfl).w
  calc pullback.fst (projModelπ (universalWeierstrassLocU.{u}.map f))
        (projModelπ (universalWeierstrassLocU.{u}.map f)) ≫
        projModelπ (universalWeierstrassLocU.{u}.map f) ≫ Spec.map (CommRingCat.ofHom f)
      = pullback.fst (projModelπ (universalWeierstrassLocU.{u}.map f))
          (projModelπ (universalWeierstrassLocU.{u}.map f)) ≫
          (projModelπ (universalWeierstrassLocU.{u}.map f) ≫ Spec.map (CommRingCat.ofHom f)) :=
        rfl
    _ = pullback.fst (projModelπ (universalWeierstrassLocU.{u}.map f))
          (projModelπ (universalWeierstrassLocU.{u}.map f)) ≫
          (projModelBaseChangeOf f universalWeierstrassLocU.{u}
            (universalWeierstrassLocU.{u}.map f) rfl ≫
            projModelπ universalWeierstrassLocU.{u}) := by rw [← hw]
    _ = (pullback.fst (projModelπ (universalWeierstrassLocU.{u}.map f))
          (projModelπ (universalWeierstrassLocU.{u}.map f)) ≫
          projModelBaseChangeOf f universalWeierstrassLocU.{u}
            (universalWeierstrassLocU.{u}.map f) rfl) ≫
          projModelπ universalWeierstrassLocU.{u} := (Category.assoc _ _ _).symm
    _ = (pullbackMapBaseChangeOf f universalWeierstrassLocU.{u}
          (universalWeierstrassLocU.{u}.map f) rfl ≫
          pullback.fst (projModelπ universalWeierstrassLocU.{u})
            (projModelπ universalWeierstrassLocU.{u})) ≫
          projModelπ universalWeierstrassLocU.{u} := by rw [hmap]
    _ = pullbackMapBaseChangeOf f universalWeierstrassLocU.{u}
          (universalWeierstrassLocU.{u}.map f) rfl ≫
          pullback.fst (projModelπ universalWeierstrassLocU.{u})
            (projModelπ universalWeierstrassLocU.{u}) ≫
          projModelπ universalWeierstrassLocU.{u} := Category.assoc _ _ _

/-- The fibre-square base change projects to the single base change (fst). -/
private lemma pullbackMapBaseChangeOf_fst (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic] :
    pullbackMapBaseChangeOf f universalWeierstrassLocU.{u}
        (universalWeierstrassLocU.{u}.map f) rfl ≫
      pullback.fst (projModelπ universalWeierstrassLocU.{u})
        (projModelπ universalWeierstrassLocU.{u}) =
      pullback.fst (projModelπ (universalWeierstrassLocU.{u}.map f))
        (projModelπ (universalWeierstrassLocU.{u}.map f)) ≫
        projModelBaseChangeOf f universalWeierstrassLocU.{u}
          (universalWeierstrassLocU.{u}.map f) rfl := by
  erw [pullbackMapBaseChangeOf, pullback.map, pullback.lift_fst]

/-- The fibre-square base change projects to the single base change (snd). -/
private lemma pullbackMapBaseChangeOf_snd (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic] :
    pullbackMapBaseChangeOf f universalWeierstrassLocU.{u}
        (universalWeierstrassLocU.{u}.map f) rfl ≫
      pullback.snd (projModelπ universalWeierstrassLocU.{u})
        (projModelπ universalWeierstrassLocU.{u}) =
      pullback.snd (projModelπ (universalWeierstrassLocU.{u}.map f))
        (projModelπ (universalWeierstrassLocU.{u}.map f)) ≫
        projModelBaseChangeOf f universalWeierstrassLocU.{u}
          (universalWeierstrassLocU.{u}.map f) rfl := by
  erw [pullbackMapBaseChangeOf, pullback.map, pullback.lift_snd]

/-- The triple-tensor base-change comparison, hoisted to a top-level definition so its
`pullback.map` obligations (the banked e₁/e₂ compatibilities) elaborate once, outside the
tensor-heavy proof context (the plan's whnf-timeout sidestep). -/
private noncomputable def tripleMapBaseChangeOf (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic] :
    ((modelOver (universalWeierstrassLocU.{u}.map f) ⊗
        modelOver (universalWeierstrassLocU.{u}.map f)) ⊗
      modelOver (universalWeierstrassLocU.{u}.map f)).left ⟶
      ((modelOver universalWeierstrassLocU.{u} ⊗ modelOver universalWeierstrassLocU.{u}) ⊗
        modelOver universalWeierstrassLocU.{u}).left :=
  pullback.map
    (modelOver (universalWeierstrassLocU.{u}.map f) ⊗
      modelOver (universalWeierstrassLocU.{u}.map f)).hom
    (modelOver (universalWeierstrassLocU.{u}.map f)).hom
    (modelOver universalWeierstrassLocU.{u} ⊗ modelOver universalWeierstrassLocU.{u}).hom
    (modelOver universalWeierstrassLocU.{u}).hom
    (pullbackMapBaseChangeOf f universalWeierstrassLocU.{u}
      (universalWeierstrassLocU.{u}.map f) rfl)
    (projModelBaseChangeOf f universalWeierstrassLocU.{u}
      (universalWeierstrassLocU.{u}.map f) rfl)
    (Spec.map (CommRingCat.ofHom f))
    (tensorObj_hom_baseChangeOf f) (modelOver_hom_baseChangeOf f)

/-- The triple base-change comparison projects to the fibre-square base change (fst). -/
private lemma tripleMapBaseChangeOf_fst (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic] :
    tripleMapBaseChangeOf f ≫
      pullback.fst (modelOver universalWeierstrassLocU.{u} ⊗
          modelOver universalWeierstrassLocU.{u}).hom
        (modelOver universalWeierstrassLocU.{u}).hom =
      pullback.fst (modelOver (universalWeierstrassLocU.{u}.map f) ⊗
          modelOver (universalWeierstrassLocU.{u}.map f)).hom
        (modelOver (universalWeierstrassLocU.{u}.map f)).hom ≫
        pullbackMapBaseChangeOf f universalWeierstrassLocU.{u}
          (universalWeierstrassLocU.{u}.map f) rfl :=
  (limit.lift_π _ _).trans rfl

/-- The triple base-change comparison projects to the single base change (snd). -/
private lemma tripleMapBaseChangeOf_snd (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic] :
    tripleMapBaseChangeOf f ≫
      pullback.snd (modelOver universalWeierstrassLocU.{u} ⊗
          modelOver universalWeierstrassLocU.{u}).hom
        (modelOver universalWeierstrassLocU.{u}).hom =
      pullback.snd (modelOver (universalWeierstrassLocU.{u}.map f) ⊗
          modelOver (universalWeierstrassLocU.{u}.map f)).hom
        (modelOver (universalWeierstrassLocU.{u}.map f)).hom ≫
        projModelBaseChangeOf f universalWeierstrassLocU.{u}
          (universalWeierstrassLocU.{u}.map f) rfl :=
  (limit.lift_π _ _).trans rfl

/-- The fibre-square base change, retyped at the Over-monoidal tensor (the v10.132 spelling
discipline: helpers live in the Over spelling; the standard-spelled content bridges by
term-mode `exact`). -/
private noncomputable def pairMapBaseChangeOf (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic] :
    (modelOver (universalWeierstrassLocU.{u}.map f) ⊗ modelOver (universalWeierstrassLocU.{u}.map f)).left ⟶
      (modelOver universalWeierstrassLocU.{u} ⊗ modelOver universalWeierstrassLocU.{u}).left :=
  pullbackMapBaseChangeOf f universalWeierstrassLocU.{u} (universalWeierstrassLocU.{u}.map f) rfl

private lemma pairMapBaseChangeOf_fst (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic] :
    pairMapBaseChangeOf f ≫
      pullback.fst (modelOver universalWeierstrassLocU.{u}).hom (modelOver universalWeierstrassLocU.{u}).hom =
      pullback.fst (modelOver (universalWeierstrassLocU.{u}.map f)).hom (modelOver (universalWeierstrassLocU.{u}.map f)).hom ≫
        projModelBaseChangeOf f universalWeierstrassLocU.{u} (universalWeierstrassLocU.{u}.map f) rfl :=
  (limit.lift_π _ _).trans rfl

private lemma pairMapBaseChangeOf_snd (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic] :
    pairMapBaseChangeOf f ≫
      pullback.snd (modelOver universalWeierstrassLocU.{u}).hom (modelOver universalWeierstrassLocU.{u}).hom =
      pullback.snd (modelOver (universalWeierstrassLocU.{u}.map f)).hom (modelOver (universalWeierstrassLocU.{u}.map f)).hom ≫
        projModelBaseChangeOf f universalWeierstrassLocU.{u} (universalWeierstrassLocU.{u}.map f) rfl :=
  (limit.lift_π _ _).trans rfl

/-- Triple projection, `pairMapBaseChangeOf`-spelled (fst). -/
private lemma tripleMapBaseChangeOf_fst' (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic] :
    tripleMapBaseChangeOf f ≫
      pullback.fst (modelOver universalWeierstrassLocU.{u} ⊗ modelOver universalWeierstrassLocU.{u}).hom
        (modelOver universalWeierstrassLocU.{u}).hom =
      pullback.fst (modelOver (universalWeierstrassLocU.{u}.map f) ⊗ modelOver (universalWeierstrassLocU.{u}.map f)).hom
        (modelOver (universalWeierstrassLocU.{u}.map f)).hom ≫ pairMapBaseChangeOf f :=
  (limit.lift_π _ _).trans rfl

/-- Triple projection, Over-spelled (snd). -/
private lemma tripleMapBaseChangeOf_snd' (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic] :
    tripleMapBaseChangeOf f ≫
      pullback.snd (modelOver universalWeierstrassLocU.{u} ⊗ modelOver universalWeierstrassLocU.{u}).hom
        (modelOver universalWeierstrassLocU.{u}).hom =
      pullback.snd (modelOver (universalWeierstrassLocU.{u}.map f) ⊗ modelOver (universalWeierstrassLocU.{u}.map f)).hom
        (modelOver (universalWeierstrassLocU.{u}.map f)).hom ≫
        projModelBaseChangeOf f universalWeierstrassLocU.{u} (universalWeierstrassLocU.{u}.map f) rfl :=
  (limit.lift_π _ _).trans rfl

/-- The multiplication intertwines the base change, in the Over spelling (`hbc` bridged). -/
private lemma mulOver_left_baseChangeOf (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic] :
    (mulOver (universalWeierstrassLocU.{u}.map f)).left ≫
      projModelBaseChangeOf f universalWeierstrassLocU.{u} (universalWeierstrassLocU.{u}.map f) rfl =
      pairMapBaseChangeOf f ≫ (mulOver universalWeierstrassLocU.{u}).left := by
  have hbc : mulModelHom (universalWeierstrassLocU.{u}.map f) ≫
        projModelBaseChangeOf f universalWeierstrassLocU.{u} (universalWeierstrassLocU.{u}.map f) rfl =
      pullbackMapBaseChangeOf f universalWeierstrassLocU.{u} (universalWeierstrassLocU.{u}.map f) rfl ≫
      WeierstrassCurve.Projective.mulModelHom universalWeierstrassLocU.{u}
        universalWeierstrassLocU.isUnit_Δ := by
    rw [mulModelHom_map_eq_BC f]
    exact mulModelHomBC_baseChange f universalWeierstrassLocU.{u}
      universalWeierstrassLocU.isUnit_Δ (universalWeierstrassLocU.{u}.map f) rfl
  have hmm : (mulOver universalWeierstrassLocU.{u}).left =
      WeierstrassCurve.Projective.mulModelHom universalWeierstrassLocU.{u}
        universalWeierstrassLocU.isUnit_Δ := by
    rw [mulOver_left, mulModelHom_universalWeierstrassLocU]
  rw [mulOver_left, hmm]
  exact hbc

/-- The associator-then-snd composite intertwines the base changes (the `mid` bridge of the
◁-side naturality; both legs meet on the triple projections). -/
private lemma assocSnd_pairMap_baseChangeOf (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic] :
    ((α_ (modelOver (universalWeierstrassLocU.{u}.map f)) (modelOver (universalWeierstrassLocU.{u}.map f)) (modelOver (universalWeierstrassLocU.{u}.map f))).hom.left ≫
        pullback.snd (modelOver (universalWeierstrassLocU.{u}.map f)).hom
          (pullback.fst (modelOver (universalWeierstrassLocU.{u}.map f)).hom (modelOver (universalWeierstrassLocU.{u}.map f)).hom ≫
            (modelOver (universalWeierstrassLocU.{u}.map f)).hom)) ≫ pairMapBaseChangeOf f =
    tripleMapBaseChangeOf f ≫
      (α_ (modelOver universalWeierstrassLocU.{u}) (modelOver universalWeierstrassLocU.{u}) (modelOver universalWeierstrassLocU.{u})).hom.left ≫
        pullback.snd (modelOver universalWeierstrassLocU.{u}).hom
          (pullback.fst (modelOver universalWeierstrassLocU.{u}).hom (modelOver universalWeierstrassLocU.{u}).hom ≫
            (modelOver universalWeierstrassLocU.{u}).hom) := by
  apply pullback.hom_ext
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((α_ (modelOver (universalWeierstrassLocU.{u}.map f)) (modelOver (universalWeierstrassLocU.{u}.map f))
        (modelOver (universalWeierstrassLocU.{u}.map f))).hom.left ≫
        pullback.snd (modelOver (universalWeierstrassLocU.{u}.map f)).hom
          (pullback.fst (modelOver (universalWeierstrassLocU.{u}.map f)).hom (modelOver (universalWeierstrassLocU.{u}.map f)).hom ≫
            (modelOver (universalWeierstrassLocU.{u}.map f)).hom) ≫ ·) (pairMapBaseChangeOf_fst f)).trans ?_
    refine (Over.associator_hom_left_snd_fst_assoc (modelOver (universalWeierstrassLocU.{u}.map f))
        (modelOver (universalWeierstrassLocU.{u}.map f)) (modelOver (universalWeierstrassLocU.{u}.map f))
        (projModelBaseChangeOf f universalWeierstrassLocU.{u} (universalWeierstrassLocU.{u}.map f) rfl)).trans ?_
    refine Eq.symm ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (tripleMapBaseChangeOf f ≫ ·) (Category.assoc _ _ _)).trans ?_
    refine (congrArg (tripleMapBaseChangeOf f ≫ ·)
        (Over.associator_hom_left_snd_fst (modelOver universalWeierstrassLocU.{u})
          (modelOver universalWeierstrassLocU.{u}) (modelOver universalWeierstrassLocU.{u}))).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ pullback.snd (modelOver universalWeierstrassLocU.{u}).hom (modelOver universalWeierstrassLocU.{u}).hom)
        (tripleMapBaseChangeOf_fst' f)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (pullback.fst (modelOver (universalWeierstrassLocU.{u}.map f) ⊗ modelOver (universalWeierstrassLocU.{u}.map f)).hom
        (modelOver (universalWeierstrassLocU.{u}.map f)).hom ≫ ·) (pairMapBaseChangeOf_snd f)
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((α_ (modelOver (universalWeierstrassLocU.{u}.map f)) (modelOver (universalWeierstrassLocU.{u}.map f))
        (modelOver (universalWeierstrassLocU.{u}.map f))).hom.left ≫
        pullback.snd (modelOver (universalWeierstrassLocU.{u}.map f)).hom
          (pullback.fst (modelOver (universalWeierstrassLocU.{u}.map f)).hom (modelOver (universalWeierstrassLocU.{u}.map f)).hom ≫
            (modelOver (universalWeierstrassLocU.{u}.map f)).hom) ≫ ·) (pairMapBaseChangeOf_snd f)).trans ?_
    refine (Over.associator_hom_left_snd_snd_assoc (modelOver (universalWeierstrassLocU.{u}.map f))
        (modelOver (universalWeierstrassLocU.{u}.map f)) (modelOver (universalWeierstrassLocU.{u}.map f))
        (projModelBaseChangeOf f universalWeierstrassLocU.{u} (universalWeierstrassLocU.{u}.map f) rfl)).trans ?_
    refine Eq.symm ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (tripleMapBaseChangeOf f ≫ ·) (Category.assoc _ _ _)).trans ?_
    refine (congrArg (tripleMapBaseChangeOf f ≫ ·)
        (Over.associator_hom_left_snd_snd (modelOver universalWeierstrassLocU.{u})
          (modelOver universalWeierstrassLocU.{u}) (modelOver universalWeierstrassLocU.{u}))).trans ?_
    exact tripleMapBaseChangeOf_snd' f

private lemma whiskerLeftMul_fst_f (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic] :
    (modelOver (universalWeierstrassLocU.{u}.map f) ◁ mulOver (universalWeierstrassLocU.{u}.map f)).left ≫
      pullback.fst (modelOver (universalWeierstrassLocU.{u}.map f)).hom (modelOver (universalWeierstrassLocU.{u}.map f)).hom =
      pullback.fst (modelOver (universalWeierstrassLocU.{u}.map f)).hom
        (pullback.fst (modelOver (universalWeierstrassLocU.{u}.map f)).hom (modelOver (universalWeierstrassLocU.{u}.map f)).hom ≫ (modelOver (universalWeierstrassLocU.{u}.map f)).hom) :=
  Over.whiskerLeft_left_fst (mulOver (universalWeierstrassLocU.{u}.map f))

private lemma whiskerLeftMul_fst_U :
    (modelOver universalWeierstrassLocU.{u} ◁ mulOver universalWeierstrassLocU.{u}).left ≫
      pullback.fst (modelOver universalWeierstrassLocU.{u}).hom (modelOver universalWeierstrassLocU.{u}).hom =
      pullback.fst (modelOver universalWeierstrassLocU.{u}).hom
        (pullback.fst (modelOver universalWeierstrassLocU.{u}).hom (modelOver universalWeierstrassLocU.{u}).hom ≫ (modelOver universalWeierstrassLocU.{u}).hom) :=
  Over.whiskerLeft_left_fst (mulOver universalWeierstrassLocU.{u})

private lemma whiskerLeftMul_snd_f (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic] :
    (modelOver (universalWeierstrassLocU.{u}.map f) ◁ mulOver (universalWeierstrassLocU.{u}.map f)).left ≫
      pullback.snd (modelOver (universalWeierstrassLocU.{u}.map f)).hom (modelOver (universalWeierstrassLocU.{u}.map f)).hom =
      pullback.snd (modelOver (universalWeierstrassLocU.{u}.map f)).hom
        (pullback.fst (modelOver (universalWeierstrassLocU.{u}.map f)).hom (modelOver (universalWeierstrassLocU.{u}.map f)).hom ≫ (modelOver (universalWeierstrassLocU.{u}.map f)).hom) ≫
        (mulOver (universalWeierstrassLocU.{u}.map f)).left :=
  Over.whiskerLeft_left_snd (mulOver (universalWeierstrassLocU.{u}.map f))

private lemma whiskerLeftMul_snd_U :
    (modelOver universalWeierstrassLocU.{u} ◁ mulOver universalWeierstrassLocU.{u}).left ≫
      pullback.snd (modelOver universalWeierstrassLocU.{u}).hom (modelOver universalWeierstrassLocU.{u}).hom =
      pullback.snd (modelOver universalWeierstrassLocU.{u}).hom
        (pullback.fst (modelOver universalWeierstrassLocU.{u}).hom (modelOver universalWeierstrassLocU.{u}).hom ≫ (modelOver universalWeierstrassLocU.{u}).hom) ≫
        (mulOver universalWeierstrassLocU.{u}).left :=
  Over.whiskerLeft_left_snd (mulOver universalWeierstrassLocU.{u})

private lemma assocMul_fst_f (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic] :
    (α_ (modelOver (universalWeierstrassLocU.{u}.map f)) (modelOver (universalWeierstrassLocU.{u}.map f)) (modelOver (universalWeierstrassLocU.{u}.map f))).hom.left ≫
      pullback.fst (modelOver (universalWeierstrassLocU.{u}.map f)).hom
        (pullback.fst (modelOver (universalWeierstrassLocU.{u}.map f)).hom (modelOver (universalWeierstrassLocU.{u}.map f)).hom ≫ (modelOver (universalWeierstrassLocU.{u}.map f)).hom) =
      pullback.fst (modelOver (universalWeierstrassLocU.{u}.map f) ⊗ modelOver (universalWeierstrassLocU.{u}.map f)).hom (modelOver (universalWeierstrassLocU.{u}.map f)).hom ≫
        pullback.fst (modelOver (universalWeierstrassLocU.{u}.map f)).hom (modelOver (universalWeierstrassLocU.{u}.map f)).hom :=
  Over.associator_hom_left_fst (modelOver (universalWeierstrassLocU.{u}.map f)) (modelOver (universalWeierstrassLocU.{u}.map f)) (modelOver (universalWeierstrassLocU.{u}.map f))

private lemma assocMul_fst_U :
    (α_ (modelOver universalWeierstrassLocU.{u}) (modelOver universalWeierstrassLocU.{u}) (modelOver universalWeierstrassLocU.{u})).hom.left ≫
      pullback.fst (modelOver universalWeierstrassLocU.{u}).hom
        (pullback.fst (modelOver universalWeierstrassLocU.{u}).hom (modelOver universalWeierstrassLocU.{u}).hom ≫ (modelOver universalWeierstrassLocU.{u}).hom) =
      pullback.fst (modelOver universalWeierstrassLocU.{u} ⊗ modelOver universalWeierstrassLocU.{u}).hom (modelOver universalWeierstrassLocU.{u}).hom ≫
        pullback.fst (modelOver universalWeierstrassLocU.{u}).hom (modelOver universalWeierstrassLocU.{u}).hom :=
  Over.associator_hom_left_fst (modelOver universalWeierstrassLocU.{u}) (modelOver universalWeierstrassLocU.{u}) (modelOver universalWeierstrassLocU.{u})

/-- The ◁-whisker/associator side of the assoc transport: the base-change naturality of
`α ≫ (mo ◁ mulOver)`, Over-spelled. -/
private lemma assoc_whiskerLeft_baseChangeOf (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic] :
    (α_ (modelOver (universalWeierstrassLocU.{u}.map f)) (modelOver (universalWeierstrassLocU.{u}.map f)) (modelOver (universalWeierstrassLocU.{u}.map f))).hom.left ≫
      (modelOver (universalWeierstrassLocU.{u}.map f) ◁ mulOver (universalWeierstrassLocU.{u}.map f)).left ≫ pairMapBaseChangeOf f =
    tripleMapBaseChangeOf f ≫
      (α_ (modelOver universalWeierstrassLocU.{u}) (modelOver universalWeierstrassLocU.{u}) (modelOver universalWeierstrassLocU.{u})).hom.left ≫
        (modelOver universalWeierstrassLocU.{u} ◁ mulOver universalWeierstrassLocU.{u}).left := by
  apply pullback.hom_ext
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((α_ (modelOver (universalWeierstrassLocU.{u}.map f)) (modelOver (universalWeierstrassLocU.{u}.map f))
        (modelOver (universalWeierstrassLocU.{u}.map f))).hom.left ≫ ·) ((Category.assoc _ _ _).trans
        ((congrArg ((modelOver (universalWeierstrassLocU.{u}.map f) ◁ mulOver (universalWeierstrassLocU.{u}.map f)).left ≫ ·)
          (pairMapBaseChangeOf_fst f)).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ projModelBaseChangeOf f universalWeierstrassLocU.{u}
              (universalWeierstrassLocU.{u}.map f) rfl) (whiskerLeftMul_fst_f f)))))).trans ?_
    refine ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ projModelBaseChangeOf f universalWeierstrassLocU.{u}
          (universalWeierstrassLocU.{u}.map f) rfl) (assocMul_fst_f f))).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (pullback.fst (modelOver (universalWeierstrassLocU.{u}.map f) ⊗ modelOver (universalWeierstrassLocU.{u}.map f)).hom
        (modelOver (universalWeierstrassLocU.{u}.map f)).hom ≫ ·) (pairMapBaseChangeOf_fst f).symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ pullback.fst (modelOver universalWeierstrassLocU.{u}).hom (modelOver universalWeierstrassLocU.{u}).hom)
        (tripleMapBaseChangeOf_fst' f).symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans (congrArg (tripleMapBaseChangeOf f ≫ ·) ?_) (Category.assoc _ _ _).symm
    refine assocMul_fst_U.symm.trans ?_
    exact Eq.trans (congrArg ((α_ (modelOver universalWeierstrassLocU.{u}) (modelOver universalWeierstrassLocU.{u})
        (modelOver universalWeierstrassLocU.{u})).hom.left ≫ ·) whiskerLeftMul_fst_U.symm)
      (Category.assoc _ _ _).symm
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((α_ (modelOver (universalWeierstrassLocU.{u}.map f)) (modelOver (universalWeierstrassLocU.{u}.map f))
        (modelOver (universalWeierstrassLocU.{u}.map f))).hom.left ≫ ·) ((Category.assoc _ _ _).trans
        ((congrArg ((modelOver (universalWeierstrassLocU.{u}.map f) ◁ mulOver (universalWeierstrassLocU.{u}.map f)).left ≫ ·)
          (pairMapBaseChangeOf_snd f)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ projModelBaseChangeOf f universalWeierstrassLocU.{u}
              (universalWeierstrassLocU.{u}.map f) rfl) (whiskerLeftMul_snd_f f)).trans
              ((Category.assoc _ _ _).trans
                (congrArg (pullback.snd (modelOver (universalWeierstrassLocU.{u}.map f)).hom
                  (pullback.fst (modelOver (universalWeierstrassLocU.{u}.map f)).hom (modelOver (universalWeierstrassLocU.{u}.map f)).hom ≫
                    (modelOver (universalWeierstrassLocU.{u}.map f)).hom) ≫ ·)
                  (mulOver_left_baseChangeOf f)))))))).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (mulOver universalWeierstrassLocU.{u}).left)
        ((Category.assoc _ _ _).symm.trans (assocSnd_pairMap_baseChangeOf f))).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans (congrArg (tripleMapBaseChangeOf f ≫ ·) ?_) (Category.assoc _ _ _).symm
    refine (Category.assoc _ _ _).trans ?_
    exact Eq.trans (congrArg ((α_ (modelOver universalWeierstrassLocU.{u}) (modelOver universalWeierstrassLocU.{u})
        (modelOver universalWeierstrassLocU.{u})).hom.left ≫ ·) whiskerLeftMul_snd_U.symm)
      (Category.assoc _ _ _).symm

/-- **(T-W7.0g-assoc·of_map)** Associativity at the base-changed universal curve (the `h = rfl`
case) — the last T-G4 transport, option (b) of the banked plan (`docs/tg4/mulOver_assoc.plan.md`):
the whisker-BC naturalities are Over-spelled double-pullback-valued equations proven by
`pullback.hom_ext` on named projection lemmas (never constructing an inline triple
`pullback.map`, never crossing the Over-vs-standard instance seam inside a tactic goal); the
snd-leg is structural `Over.w`. -/
theorem mulOver_assoc_of_map (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic] :
    (mulOver (universalWeierstrassLocU.{u}.map f) ▷ modelOver (universalWeierstrassLocU.{u}.map f)) ≫
        mulOver (universalWeierstrassLocU.{u}.map f) =
      (α_ (modelOver (universalWeierstrassLocU.{u}.map f))
          (modelOver (universalWeierstrassLocU.{u}.map f))
          (modelOver (universalWeierstrassLocU.{u}.map f))).hom ≫
        (modelOver (universalWeierstrassLocU.{u}.map f) ◁
            mulOver (universalWeierstrassLocU.{u}.map f)) ≫
          mulOver (universalWeierstrassLocU.{u}.map f) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, Over.comp_left]
  have raw : (mulOver universalWeierstrassLocU.{u} ▷ modelOver universalWeierstrassLocU.{u}).left ≫
      (mulOver universalWeierstrassLocU.{u}).left =
      (α_ (modelOver universalWeierstrassLocU.{u}) (modelOver universalWeierstrassLocU.{u})
          (modelOver universalWeierstrassLocU.{u})).hom.left ≫
        (modelOver universalWeierstrassLocU.{u} ◁ mulOver universalWeierstrassLocU.{u}).left ≫
          (mulOver universalWeierstrassLocU.{u}).left := by
    have h2 := congrArg (fun m => m.left) mulOver_assoc_atlas
    rw [Over.comp_left, Over.comp_left, Over.comp_left] at h2
    exact h2
  have hL : (mulOver (universalWeierstrassLocU.{u}.map f) ▷
        modelOver (universalWeierstrassLocU.{u}.map f)).left ≫ pairMapBaseChangeOf f =
      tripleMapBaseChangeOf f ≫
        (mulOver universalWeierstrassLocU.{u} ▷ modelOver universalWeierstrassLocU.{u}).left := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (pairMapBaseChangeOf_fst f)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ _) (Over.whiskerRight_left_fst
                (mulOver (universalWeierstrassLocU.{u}.map f)))).trans
              ((Category.assoc _ _ _).trans
                ((congrArg (_ ≫ ·) (mulOver_left_baseChangeOf f)).trans
                  ((Category.assoc _ _ _).symm.trans
                    ((congrArg (· ≫ _) (tripleMapBaseChangeOf_fst' f).symm).trans
                      ((Category.assoc _ _ _).trans
                        ((congrArg (_ ≫ ·) (Over.whiskerRight_left_fst
                            (mulOver universalWeierstrassLocU.{u})).symm).trans
                          (Category.assoc _ _ _).symm)))))))))
    · exact (Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (pairMapBaseChangeOf_snd f)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ _) (Over.whiskerRight_left_snd
                (mulOver (universalWeierstrassLocU.{u}.map f)))).trans
              ((tripleMapBaseChangeOf_snd' f).symm.trans
                ((congrArg (_ ≫ ·) (Over.whiskerRight_left_snd
                    (mulOver universalWeierstrassLocU.{u})).symm).trans
                  (Category.assoc _ _ _).symm)))))
  have hR : (α_ (modelOver (universalWeierstrassLocU.{u}.map f))
        (modelOver (universalWeierstrassLocU.{u}.map f))
        (modelOver (universalWeierstrassLocU.{u}.map f))).hom.left ≫
      (modelOver (universalWeierstrassLocU.{u}.map f) ◁
        mulOver (universalWeierstrassLocU.{u}.map f)).left ≫ pairMapBaseChangeOf f =
      tripleMapBaseChangeOf f ≫
        (α_ (modelOver universalWeierstrassLocU.{u}) (modelOver universalWeierstrassLocU.{u})
            (modelOver universalWeierstrassLocU.{u})).hom.left ≫
          (modelOver universalWeierstrassLocU.{u} ◁ mulOver universalWeierstrassLocU.{u}).left :=
    assoc_whiskerLeft_baseChangeOf f
  -- assembly: hom_ext legs of the base-change square
  apply (isPullback_projModelBaseChangeOf f universalWeierstrassLocU.{u}
    (universalWeierstrassLocU.{u}.map f) rfl).hom_ext
  · -- fst-leg: push the multiplication across the base change on both sides, then hL/hR + raw
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((mulOver (universalWeierstrassLocU.{u}.map f) ▷
        modelOver (universalWeierstrassLocU.{u}.map f)).left ≫ ·) (mulOver_left_baseChangeOf f)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (mulOver universalWeierstrassLocU.{u}).left) hL).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.symm ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((α_ (modelOver (universalWeierstrassLocU.{u}.map f)) (modelOver (universalWeierstrassLocU.{u}.map f))
        (modelOver (universalWeierstrassLocU.{u}.map f))).hom.left ≫ ·) (Category.assoc _ _ _)).trans ?_
    refine (congrArg (fun m => (α_ (modelOver (universalWeierstrassLocU.{u}.map f)) (modelOver (universalWeierstrassLocU.{u}.map f))
        (modelOver (universalWeierstrassLocU.{u}.map f))).hom.left ≫
        (modelOver (universalWeierstrassLocU.{u}.map f) ◁ mulOver (universalWeierstrassLocU.{u}.map f)).left ≫ m)
        (mulOver_left_baseChangeOf f)).trans ?_
    refine (congrArg ((α_ (modelOver (universalWeierstrassLocU.{u}.map f)) (modelOver (universalWeierstrassLocU.{u}.map f))
        (modelOver (universalWeierstrassLocU.{u}.map f))).hom.left ≫ ·) (Category.assoc _ _ _).symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (mulOver universalWeierstrassLocU.{u}).left)
        ((Category.assoc _ _ _).trans hR)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg (tripleMapBaseChangeOf f ≫ ·) raw.symm
  · -- snd-leg: structural Over.w on both original Over morphisms
    have hga := Over.w (((mulOver (universalWeierstrassLocU.{u}.map f) ▷
        modelOver (universalWeierstrassLocU.{u}.map f)) ≫
        mulOver (universalWeierstrassLocU.{u}.map f)))
    have hgb := Over.w ((α_ (modelOver (universalWeierstrassLocU.{u}.map f))
        (modelOver (universalWeierstrassLocU.{u}.map f))
        (modelOver (universalWeierstrassLocU.{u}.map f))).hom ≫
        (modelOver (universalWeierstrassLocU.{u}.map f) ◁
            mulOver (universalWeierstrassLocU.{u}.map f)) ≫
          mulOver (universalWeierstrassLocU.{u}.map f))
    rw [Over.comp_left] at hga
    rw [Over.comp_left, Over.comp_left] at hgb
    exact ((Category.assoc _ _ _).symm.trans hga).trans
      (hgb.symm.trans (Category.assoc _ _ _)).symm.symm

/-- **(T-W7.0g-assoc·of_eq)** Associativity at any `W` presented as a base change; `subst`
reduces to the `of_map` case. -/
theorem mulOver_assoc_of_eq (f : WeierstrassAtlasRingU.{u} →+* R) (W : WeierstrassCurve R)
    [W.IsElliptic] (h : universalWeierstrassLocU.{u}.map f = W) :
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

/-- **(T-W7.0g-mul-one·of_map)** Right unit law at the base-changed universal curve
`universalWeierstrassLocU.map f` (the `h = rfl` case). The whisker-BC naturality `hnat` is
discharged by `pullback.map_comp` on both sides (the Over-monoidal `HasPullback` instance and
the standard one agree by proof irrelevance — `erw` bridges), the π-leg by the structural
`Over.w`. This is the hard proof; every general `W` reduces to it by `subst`. -/
theorem mulOver_oneOver_of_map (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic] :
    (modelOver (universalWeierstrassLocU.{u}.map f) ◁ oneOver (universalWeierstrassLocU.{u}.map f)) ≫
        mulOver (universalWeierstrassLocU.{u}.map f) =
      (ρ_ (modelOver (universalWeierstrassLocU.{u}.map f))).hom := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, mulOver_left, Over.rightUnitor_hom_left]
  have raw : (modelOver universalWeierstrassLocU.{u} ◁ oneOver universalWeierstrassLocU.{u}).left ≫
      WeierstrassCurve.Projective.mulModelHom universalWeierstrassLocU.{u}
        universalWeierstrassLocU.isUnit_Δ =
      pullback.fst (projModelπ universalWeierstrassLocU.{u})
        (𝟙 (Spec (CommRingCat.of WeierstrassAtlasRingU.{u}))) := by
    have h2 := congrArg (fun m => m.left) mulOver_oneOver_atlas
    rw [Over.comp_left, mulOver_left, Over.rightUnitor_hom_left,
      mulModelHom_universalWeierstrassLocU] at h2
    exact h2
  have hbc : mulModelHom (universalWeierstrassLocU.{u}.map f) ≫
        projModelBaseChangeOf f universalWeierstrassLocU.{u}
          (universalWeierstrassLocU.{u}.map f) rfl =
      pullbackMapBaseChangeOf f universalWeierstrassLocU.{u}
        (universalWeierstrassLocU.{u}.map f) rfl ≫
      WeierstrassCurve.Projective.mulModelHom universalWeierstrassLocU.{u}
        universalWeierstrassLocU.isUnit_Δ := by
    rw [mulModelHom_map_eq_BC f]
    exact mulModelHomBC_baseChange f universalWeierstrassLocU.{u}
      universalWeierstrassLocU.isUnit_Δ (universalWeierstrassLocU.{u}.map f) rfl
  have hw1 : projModelπ (universalWeierstrassLocU.{u}.map f) ≫ Spec.map (CommRingCat.ofHom f) =
      projModelBaseChangeOf f universalWeierstrassLocU.{u}
        (universalWeierstrassLocU.{u}.map f) rfl ≫ projModelπ universalWeierstrassLocU.{u} :=
    (isPullback_projModelBaseChangeOf f universalWeierstrassLocU.{u}
      (universalWeierstrassLocU.{u}.map f) rfl).w.symm
  have hw2 : 𝟙 (Spec (CommRingCat.of R)) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom f) ≫ 𝟙 (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})) := by
    rw [Category.comp_id, Category.id_comp]
  set X :=
    pullback.map (projModelπ (universalWeierstrassLocU.{u}.map f)) (𝟙 (Spec (CommRingCat.of R)))
      (projModelπ universalWeierstrassLocU.{u})
      (𝟙 (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))
      (projModelBaseChangeOf f universalWeierstrassLocU.{u}
        (universalWeierstrassLocU.{u}.map f) rfl)
      (Spec.map (CommRingCat.ofHom f)) (Spec.map (CommRingCat.ofHom f)) hw1 hw2 with hXdef
  have hnat : (modelOver (universalWeierstrassLocU.{u}.map f) ◁
        oneOver (universalWeierstrassLocU.{u}.map f)).left ≫
      pullbackMapBaseChangeOf f universalWeierstrassLocU.{u}
        (universalWeierstrassLocU.{u}.map f) rfl =
      X ≫ (modelOver universalWeierstrassLocU.{u} ◁ oneOver universalWeierstrassLocU.{u}).left := by
    rw [Over.whiskerLeft_left, pullbackMapBaseChangeOf, hXdef, Over.whiskerLeft_left]
    simp only [modelOver_hom, modelOver_left, Over.tensorUnit_hom, Over.tensorUnit_left]
    erw [pullback.map_comp, pullback.map_comp]
    congr 1
    erw [oneOver_left, oneOver_left, Over.tensorUnit_hom, Over.tensorUnit_hom, Category.id_comp,
      Category.id_comp, projModelZero_baseChangeOf]
  apply (isPullback_projModelBaseChangeOf f universalWeierstrassLocU.{u}
    (universalWeierstrassLocU.{u}.map f) rfl).hom_ext
  · erw [Category.assoc, hbc, ← Category.assoc, hnat, Category.assoc, raw, hXdef, pullback.map,
      pullback.lift_fst]
    rfl
  · have hga := Over.w ((modelOver (universalWeierstrassLocU.{u}.map f) ◁
        oneOver (universalWeierstrassLocU.{u}.map f)) ≫ mulOver (universalWeierstrassLocU.{u}.map f))
    have hgb := Over.w (ρ_ (modelOver (universalWeierstrassLocU.{u}.map f))).hom
    rw [Over.comp_left, mulOver_left] at hga
    rw [Over.rightUnitor_hom_left] at hgb
    exact hga.trans hgb.symm

/-- **(T-W7.0g-mul-one·of_eq)** Right unit law at any `W` presented as a base change
`universalWeierstrassLocU.map f = W`; `subst` reduces to the `of_map` case. -/
theorem mulOver_oneOver_of_eq (f : WeierstrassAtlasRingU.{u} →+* R) (W : WeierstrassCurve R)
    [W.IsElliptic] (h : universalWeierstrassLocU.{u}.map f = W) :
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

/-- **(T-W7.0g-inv-law·of_map)** The left inverse law at the base-changed universal curve
`universalWeierstrassLocU.map f` (the `h = rfl` case). The whisker-BC naturality `hnat` here has a
single-object domain (`projModel`), so it reduces by `pullback.hom_ext` to beastmode-A's
`negModelHom_baseChange` (fst-leg) and triviality (snd-leg); the fst assembly-leg closes via the
base-change square `.w` and `projModelZero_baseChangeOf`, the π-leg by the structural `Over.w`. -/
theorem invOver_mulOver_of_map (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic] :
    lift (invOver (universalWeierstrassLocU.{u}.map f))
        (𝟙 (modelOver (universalWeierstrassLocU.{u}.map f))) ≫
        mulOver (universalWeierstrassLocU.{u}.map f) =
      toUnit (modelOver (universalWeierstrassLocU.{u}.map f)) ≫
        oneOver (universalWeierstrassLocU.{u}.map f) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, mulOver_left, Over.toUnit_left, oneOver_left]
  have raw : (lift (invOver universalWeierstrassLocU.{u})
        (𝟙 (modelOver universalWeierstrassLocU.{u}))).left ≫
      WeierstrassCurve.Projective.mulModelHom universalWeierstrassLocU.{u}
        universalWeierstrassLocU.isUnit_Δ =
      (modelOver universalWeierstrassLocU.{u}).hom ≫
        (𝟙_ (Over (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})))).hom ≫
          projModelZero universalWeierstrassLocU.{u} := by
    have h2 := congrArg (fun m => m.left) invOver_mulOver_atlas
    rw [Over.comp_left, Over.comp_left, mulOver_left, Over.toUnit_left, oneOver_left,
      mulModelHom_universalWeierstrassLocU] at h2
    exact h2
  have hbc : mulModelHom (universalWeierstrassLocU.{u}.map f) ≫
        projModelBaseChangeOf f universalWeierstrassLocU.{u}
          (universalWeierstrassLocU.{u}.map f) rfl =
      pullbackMapBaseChangeOf f universalWeierstrassLocU.{u}
        (universalWeierstrassLocU.{u}.map f) rfl ≫
      WeierstrassCurve.Projective.mulModelHom universalWeierstrassLocU.{u}
        universalWeierstrassLocU.isUnit_Δ := by
    rw [mulModelHom_map_eq_BC f]
    exact mulModelHomBC_baseChange f universalWeierstrassLocU.{u}
      universalWeierstrassLocU.isUnit_Δ (universalWeierstrassLocU.{u}.map f) rfl
  have hnat : (lift (invOver (universalWeierstrassLocU.{u}.map f))
        (𝟙 (modelOver (universalWeierstrassLocU.{u}.map f)))).left ≫
      pullbackMapBaseChangeOf f universalWeierstrassLocU.{u}
        (universalWeierstrassLocU.{u}.map f) rfl =
      projModelBaseChangeOf f universalWeierstrassLocU.{u}
        (universalWeierstrassLocU.{u}.map f) rfl ≫
      (lift (invOver universalWeierstrassLocU.{u})
        (𝟙 (modelOver universalWeierstrassLocU.{u}))).left := by
    rw [Over.lift_left, Over.lift_left]
    simp only [invOver_left, Over.id_left, pullbackMapBaseChangeOf, projModelBaseChangeOf_rfl]
    apply pullback.hom_ext
    · erw [Category.assoc, pullback.map, pullback.lift_fst, ← Category.assoc, pullback.lift_fst,
        Category.assoc, pullback.lift_fst]
      exact negModelHom_baseChange f universalWeierstrassLocU.{u}
    · erw [Category.assoc, pullback.map, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
        Category.assoc, pullback.lift_snd, Category.id_comp]
  apply (isPullback_projModelBaseChangeOf f universalWeierstrassLocU.{u}
    (universalWeierstrassLocU.{u}.map f) rfl).hom_ext
  · erw [Category.assoc, hbc, ← Category.assoc, hnat, Category.assoc, raw]
    simp only [modelOver_hom, Over.tensorUnit_hom]
    erw [Category.id_comp, Category.id_comp]
    have hw := (isPullback_projModelBaseChangeOf f universalWeierstrassLocU.{u}
      (universalWeierstrassLocU.{u}.map f) rfl).w
    have hz := projModelZero_baseChangeOf f universalWeierstrassLocU.{u}
      (universalWeierstrassLocU.{u}.map f) rfl
    calc projModelBaseChangeOf f universalWeierstrassLocU.{u}
            (universalWeierstrassLocU.{u}.map f) rfl ≫
          projModelπ universalWeierstrassLocU.{u} ≫ projModelZero universalWeierstrassLocU.{u}
        = (projModelBaseChangeOf f universalWeierstrassLocU.{u}
              (universalWeierstrassLocU.{u}.map f) rfl ≫ projModelπ universalWeierstrassLocU.{u}) ≫
            projModelZero universalWeierstrassLocU.{u} := (Category.assoc _ _ _).symm
      _ = (projModelπ (universalWeierstrassLocU.{u}.map f) ≫ Spec.map (CommRingCat.ofHom f)) ≫
            projModelZero universalWeierstrassLocU.{u} := by rw [hw]
      _ = projModelπ (universalWeierstrassLocU.{u}.map f) ≫
            Spec.map (CommRingCat.ofHom f) ≫ projModelZero universalWeierstrassLocU.{u} :=
          Category.assoc _ _ _
      _ = projModelπ (universalWeierstrassLocU.{u}.map f) ≫
            projModelZero (universalWeierstrassLocU.{u}.map f) ≫
            projModelBaseChangeOf f universalWeierstrassLocU.{u}
              (universalWeierstrassLocU.{u}.map f) rfl := by rw [← hz]
      _ = (projModelπ (universalWeierstrassLocU.{u}.map f) ≫
              projModelZero (universalWeierstrassLocU.{u}.map f)) ≫
            projModelBaseChangeOf f universalWeierstrassLocU.{u}
              (universalWeierstrassLocU.{u}.map f) rfl := (Category.assoc _ _ _).symm
  · have hga := Over.w (lift (invOver (universalWeierstrassLocU.{u}.map f))
        (𝟙 (modelOver (universalWeierstrassLocU.{u}.map f))) ≫
        mulOver (universalWeierstrassLocU.{u}.map f))
    have hgb := Over.w (toUnit (modelOver (universalWeierstrassLocU.{u}.map f)) ≫
        oneOver (universalWeierstrassLocU.{u}.map f))
    rw [Over.comp_left, mulOver_left] at hga
    rw [Over.comp_left, Over.toUnit_left, oneOver_left] at hgb
    exact hga.trans hgb.symm

/-- **(T-W7.0g-inv-law·of_eq)** The left inverse law at any `W` presented as a base change; `subst`
reduces to the `of_map` case. -/
theorem invOver_mulOver_of_eq (f : WeierstrassAtlasRingU.{u} →+* R) (W : WeierstrassCurve R)
    [W.IsElliptic] (h : universalWeierstrassLocU.{u}.map f = W) :
    lift (invOver W) (𝟙 (modelOver W)) ≫ mulOver W = toUnit (modelOver W) ≫ oneOver W := by
  subst h
  exact invOver_mulOver_of_map f

/-- **(T-W7.0g-inv-law)** The left inverse law, for every elliptic `W` over every `R` — via the
classifying map `classifyRingHomU W`. Consumes beastmode-A's `negModelHom_baseChange`. -/
theorem invOver_mulOver (W : WeierstrassCurve R) [W.IsElliptic] :
    lift (invOver W) (𝟙 (modelOver W)) ≫ mulOver W = toUnit (modelOver W) ≫ oneOver W :=
  invOver_mulOver_of_eq (classifyRingHomU W) W (universalWeierstrassLocU_map_classifyRingHomU W)

end Transport

end ModularCurves

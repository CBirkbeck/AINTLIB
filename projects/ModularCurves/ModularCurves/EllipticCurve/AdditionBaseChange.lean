/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.AdditionChartGlobal
import ModularCurves.EllipticCurve.WeierstrassAtlasBundle
import ModularCurves.ForMathlib.IntJacobson

/-!
# Base change of the Bosma–Lenstra multiplication (T-W7.0c·c4.5)

The two-law multiplication `mulModelHom` (AdditionChartGlobal) exists over Jacobson domains — in
particular over the universal atlas ring. This file transports it to EVERY ring:

* `WeierstrassAtlasRingU`, `universalWeierstrassLocU`, `classifyRingHomU` — the universe-`u` lift
  of the universal Weierstrass atlas (`ULift`), with its `IsDomain`/`IsJacobsonRing`/`IsElliptic`
  instances; `universalWeierstrassLocU_map_classifyRingHomU` is the classifying property.
* `projModelBaseChangeOf`, `isPullback_projModelBaseChangeOf` — the T-A5a base-change square,
  stated for an arbitrary ring hom `f` and a curve `W` with `W₀.map f = W` (the `eqToHom` of the
  transport lives here, and only here; the lemma is proven by `subst`).
* `mulModelHomBC` — THE base-changed multiplication `E_W ×_R E_W ⟶ E_W`: the universal property
  lift of `(base-change product) ≫ mulModelHom_U` against the square. Its `lift_fst` spec
  (`mulModelHomBC_baseChange`) is the base-change-naturality seed; its `lift_snd` spec
  (`mulModelHomBC_projModelπ`) is `mulModelHom_π` over `R` for free.

Instantiated at `f := classifyRingHomU W` this fills GLC's `mulModelHom` for every elliptic `W`
over every ring (T-W7.0c·c4 + T-W7.0d), with `mulModelHom_map` following from lift-uniqueness.
-/

open MvPolynomial ModularCurves AlgebraicGeometry CategoryTheory Limits WeierstrassCurve

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace ModularCurves

/-- The universal atlas ring is Jacobson (finite type over the Jacobson ℤ + localization). -/
instance : IsJacobsonRing WeierstrassAtlasRing :=
  isJacobsonRing_localization (R := MvPolynomial (Fin 5) ℤ) (y := universalWeierstrass.Δ)

/-- The universe-`u` universal atlas ring. -/
abbrev WeierstrassAtlasRingU : Type u := ULift.{u} WeierstrassAtlasRing

instance : IsDomain (WeierstrassAtlasRingU.{u}) :=
  (ULift.ringEquiv (R := WeierstrassAtlasRing)).toMulEquiv.isDomain WeierstrassAtlasRing

instance : IsJacobsonRing (WeierstrassAtlasRingU.{u}) :=
  isJacobsonRing_of_surjective
    ⟨(ULift.ringEquiv (R := WeierstrassAtlasRing)).symm.toRingHom,
      (ULift.ringEquiv.symm).surjective⟩

/-- The universal Weierstrass curve over the universe-`u` atlas ring. -/
noncomputable def universalWeierstrassLocU : WeierstrassCurve (WeierstrassAtlasRingU.{u}) :=
  universalWeierstrassLoc.map (ULift.ringEquiv (R := WeierstrassAtlasRing)).symm.toRingHom

instance : (universalWeierstrassLocU.{u}).IsElliptic := by
  rw [universalWeierstrassLocU]
  constructor
  rw [map_Δ]
  exact universalWeierstrassLoc.isUnit_Δ.map _

variable {R : Type u} [CommRing R]

/-- The universe-`u` classifying map. -/
noncomputable def classifyRingHomU (W : WeierstrassCurve R) [W.IsElliptic] :
    WeierstrassAtlasRingU.{u} →+* R :=
  (classifyRingHom W).comp (ULift.ringEquiv (R := WeierstrassAtlasRing)).toRingHom

/-- The universe-`u` classifying property. -/
theorem universalWeierstrassLocU_map_classifyRingHomU (W : WeierstrassCurve R) [W.IsElliptic] :
    universalWeierstrassLocU.map (classifyRingHomU W) = W := by
  rw [universalWeierstrassLocU, WeierstrassCurve.map_map, classifyRingHomU, RingHom.comp_assoc]
  have h : (ULift.ringEquiv (R := WeierstrassAtlasRing)).toRingHom.comp
      (ULift.ringEquiv (R := WeierstrassAtlasRing)).symm.toRingHom = RingHom.id _ := by
    ext x
    simp
  rw [h, RingHom.comp_id, universalWeierstrassLoc_map_classifyRingHom]


section BaseChangeOf

variable {U : Type u} [CommRing U] {R : Type u} [CommRing R]

/-- Base change along an arbitrary ring hom, with the target curve given by a propositional
equality — the `eqToHom` lives here, and only here. -/
noncomputable def projModelBaseChangeOf (f : U →+* R) (W₀ : WeierstrassCurve U)
    (W : WeierstrassCurve R) (h : W₀.map f = W) :
    projModel W ⟶ projModel W₀ :=
  eqToHom (congrArg projModel h.symm) ≫ projModelBaseChange f W₀

/-- The transported base-change square: `projModel W` is the pullback of `projModel W₀` along
`Spec f`, whenever `W₀.map f = W`. -/
theorem isPullback_projModelBaseChangeOf (f : U →+* R) (W₀ : WeierstrassCurve U)
    (W : WeierstrassCurve R) (h : W₀.map f = W) :
    IsPullback (projModelBaseChangeOf f W₀ W h) (projModelπ W) (projModelπ W₀)
      (Spec.map (CommRingCat.ofHom f)) := by
  subst h
  rw [projModelBaseChangeOf]
  simp only [eqToHom_refl, Category.id_comp]
  letI : Algebra U R := f.toAlgebra
  exact isPullback_projModelBaseChange W₀

/-- The base-change map on the fibre-square `E ×_R E ⟶ E₀ ×_U E₀`. -/
noncomputable def pullbackMapBaseChangeOf (f : U →+* R) (W₀ : WeierstrassCurve U)
    (W : WeierstrassCurve R) (h : W₀.map f = W) :
    pullback (projModelπ W) (projModelπ W) ⟶ pullback (projModelπ W₀) (projModelπ W₀) :=
  pullback.map _ _ _ _ (projModelBaseChangeOf f W₀ W h) (projModelBaseChangeOf f W₀ W h)
    (Spec.map (CommRingCat.ofHom f))
    (isPullback_projModelBaseChangeOf f W₀ W h).w.symm
    (isPullback_projModelBaseChangeOf f W₀ W h).w.symm

/-- The `fst`-leg of the base-change fibre-square map. Stated for a generic transport proof `h`,
so it can be instantiated at `h := rfl` (where direct `rw`-unfolding of the definition fails). -/
private lemma pullbackMapBaseChangeOf_fst (f : U →+* R) (W₀ : WeierstrassCurve U)
    (W : WeierstrassCurve R) (h : W₀.map f = W) :
    pullbackMapBaseChangeOf f W₀ W h ≫ pullback.fst (projModelπ W₀) (projModelπ W₀) =
      pullback.fst (projModelπ W) (projModelπ W) ≫ projModelBaseChangeOf f W₀ W h := by
  simp only [pullbackMapBaseChangeOf, pullback.lift_fst]

/-- The `snd`-leg of the base-change fibre-square map. -/
private lemma pullbackMapBaseChangeOf_snd (f : U →+* R) (W₀ : WeierstrassCurve U)
    (W : WeierstrassCurve R) (h : W₀.map f = W) :
    pullbackMapBaseChangeOf f W₀ W h ≫ pullback.snd (projModelπ W₀) (projModelπ W₀) =
      pullback.snd (projModelπ W) (projModelπ W) ≫ projModelBaseChangeOf f W₀ W h := by
  simp only [pullbackMapBaseChangeOf, pullback.lift_snd]

/-- The lift agreement: the base-changed multiplication and the structure map agree over
`Spec U`. -/
lemma pullbackMap_mulModelHom_agree (f : U →+* R) (W₀ : WeierstrassCurve U)
    [IsDomain U] [IsJacobsonRing U] (hΔ₀ : IsUnit W₀.Δ)
    (W : WeierstrassCurve R) (h : W₀.map f = W) :
    (pullbackMapBaseChangeOf f W₀ W h ≫ WeierstrassCurve.Projective.mulModelHom W₀ hΔ₀) ≫
        projModelπ W₀ =
      (pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W) ≫
        Spec.map (CommRingCat.ofHom f) := by
  simp only [Category.assoc]
  rw [WeierstrassCurve.Projective.mulModelHom_projModelπ W₀ hΔ₀]
  rw [pullbackMapBaseChangeOf]
  rw [pullback.lift_fst_assoc]
  rw [Category.assoc, (isPullback_projModelBaseChangeOf f W₀ W h).w]

/-- **(c4.5, the base-change multiplication)** The multiplication morphism over `R`, obtained from
the two-law `mulModelHom` over the Jacobson domain `U` by the universal property of the base-change
square. -/
noncomputable def mulModelHomBC (f : U →+* R) (W₀ : WeierstrassCurve U)
    [IsDomain U] [IsJacobsonRing U] (hΔ₀ : IsUnit W₀.Δ)
    (W : WeierstrassCurve R) (h : W₀.map f = W) :
    pullback (projModelπ W) (projModelπ W) ⟶ projModel W :=
  (isPullback_projModelBaseChangeOf f W₀ W h).lift
    (pullbackMapBaseChangeOf f W₀ W h ≫ WeierstrassCurve.Projective.mulModelHom W₀ hΔ₀)
    (pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W)
    (pullbackMap_mulModelHom_agree f W₀ hΔ₀ W h)

/-- The lift restricts to `mulModelHom_U` through the base-change product. -/
@[reassoc]
lemma mulModelHomBC_baseChange (f : U →+* R) (W₀ : WeierstrassCurve U)
    [IsDomain U] [IsJacobsonRing U] (hΔ₀ : IsUnit W₀.Δ)
    (W : WeierstrassCurve R) (h : W₀.map f = W) :
    mulModelHomBC f W₀ hΔ₀ W h ≫ projModelBaseChangeOf f W₀ W h =
      pullbackMapBaseChangeOf f W₀ W h ≫ WeierstrassCurve.Projective.mulModelHom W₀ hΔ₀ :=
  (isPullback_projModelBaseChangeOf f W₀ W h).lift_fst _ _ _

/-- The lift is over `Spec R` — `mulModelHom_π` for the base-changed multiplication. -/
@[reassoc]
lemma mulModelHomBC_projModelπ (f : U →+* R) (W₀ : WeierstrassCurve U)
    [IsDomain U] [IsJacobsonRing U] (hΔ₀ : IsUnit W₀.Δ)
    (W : WeierstrassCurve R) (h : W₀.map f = W) :
    mulModelHomBC f W₀ hΔ₀ W h ≫ projModelπ W =
      pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W :=
  (isPullback_projModelBaseChangeOf f W₀ W h).lift_snd _ _ _

/-- Restrictions of one morphism to two opens agree on the intersection — the trivial form of
`addOn_agree` once both laws are (definitionally) restrictions of the same `mulModelHom`. -/
lemma restrict_inf_agree {X Y : Scheme} (M : X ⟶ Y) (U V : X.Opens) :
    X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ U.ι ≫ M =
      X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ V.ι ≫ M := by
  rw [← Category.assoc, Scheme.homOfLE_ι, ← Category.assoc, Scheme.homOfLE_ι]

section ClassifyNaturality

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']

/-- **(c4.5 nat, A1)** Classifying maps are natural: the classifying map of a base-changed curve
is the composite. Two maps out of the Δ-localized universal ring agreeing on the `aᵢ` generators
agree (`IsLocalization.ringHom_ext` + `MvPolynomial.ringHom_ext`). -/
theorem classifyRingHom_map (f : R →+* R') (W : WeierstrassCurve R)
    [W.IsElliptic] [(W.map f).IsElliptic] :
    classifyRingHom (W.map f) = f.comp (classifyRingHom W) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers universalWeierstrass.Δ)
  have h1 : (classifyRingHom (W.map f)).comp
      (algebraMap (MvPolynomial (Fin 5) ℤ) WeierstrassAtlasRing) = classifyCoeffHom (W.map f) := by
    simp only [classifyRingHom, IsLocalization.Away.lift_comp]
  have h2 : (classifyRingHom W).comp
      (algebraMap (MvPolynomial (Fin 5) ℤ) WeierstrassAtlasRing) = classifyCoeffHom W := by
    simp only [classifyRingHom, IsLocalization.Away.lift_comp]
  rw [h1, RingHom.comp_assoc, h2]
  apply MvPolynomial.ringHom_ext
  · intro n
    simp [classifyCoeffHom]
  · intro i
    fin_cases i <;>
      simp [classifyCoeffHom, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]

/-- The universe-`u` form of `classifyRingHom_map`. -/
theorem classifyRingHomU_map (f : R →+* R') (W : WeierstrassCurve R)
    [W.IsElliptic] [(W.map f).IsElliptic] :
    classifyRingHomU (W.map f) = f.comp (classifyRingHomU W) := by
  rw [classifyRingHomU, classifyRingHomU, classifyRingHom_map f W, RingHom.comp_assoc]

section BaseChangeFunctoriality

variable {U R R' : Type u} [CommRing U] [CommRing R] [CommRing R']

/-- (A2 core) Three-ring functoriality of the projective-model base change. -/
theorem projModelBaseChange_comp' (F : R →+* R') (G : U →+* R) (W : WeierstrassCurve U) :
    projModelBaseChange (F.comp G) W
      = projModelBaseChange F (W.map G) ≫ projModelBaseChange G W := by
  have bmk₁ : ∀ p : MvPolynomial (Fin 3) U,
      baseChangeGradedHom (F.comp G) W (Ideal.Quotient.mk (projIdeal W).toIdeal p)
        = Ideal.Quotient.mk (projIdeal (W.map (F.comp G))).toIdeal
            (MvPolynomial.map (F.comp G) p) :=
    fun p => HomogeneousIdeal.quotientGradingMap_mk (mvMapGraded (F.comp G)) (projIdeal W)
      (projIdeal (W.map (F.comp G))) (projIdeal_le_comap (F.comp G) W) p
  have bmk₂ : ∀ p : MvPolynomial (Fin 3) U,
      baseChangeGradedHom G W (Ideal.Quotient.mk (projIdeal W).toIdeal p)
        = Ideal.Quotient.mk (projIdeal (W.map G)).toIdeal (MvPolynomial.map G p) :=
    fun p => HomogeneousIdeal.quotientGradingMap_mk (mvMapGraded G) (projIdeal W)
      (projIdeal (W.map G)) (projIdeal_le_comap G W) p
  have bmk₃ : ∀ p : MvPolynomial (Fin 3) R,
      baseChangeGradedHom F (W.map G) (Ideal.Quotient.mk (projIdeal (W.map G)).toIdeal p)
        = Ideal.Quotient.mk (projIdeal ((W.map G).map F)).toIdeal (MvPolynomial.map F p) :=
    fun p => HomogeneousIdeal.quotientGradingMap_mk (mvMapGraded F) (projIdeal (W.map G))
      (projIdeal ((W.map G).map F)) (projIdeal_le_comap F (W.map G)) p
  have hgraded : baseChangeGradedHom (F.comp G) W
      = (baseChangeGradedHom F (W.map G)).comp (baseChangeGradedHom G W) := by
    refine GradedRingHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    show baseChangeGradedHom (F.comp G) W (Ideal.Quotient.mk _ a)
      = baseChangeGradedHom F (W.map G) (baseChangeGradedHom G W (Ideal.Quotient.mk _ a))
    rw [bmk₁, bmk₂, bmk₃]
    exact congrArg (Ideal.Quotient.mk _) (MvPolynomial.map_map G F a).symm
  have key := Proj.map_comp (baseChangeGradedHom G W) (baseChangeGradedHom F (W.map G))
    (baseChangeGradedHom_irrelevant_le G W) (baseChangeGradedHom_irrelevant_le F (W.map G))
  refine Eq.trans ?_ key
  show Proj.map (baseChangeGradedHom (F.comp G) W) (baseChangeGradedHom_irrelevant_le (F.comp G) W)
    = Proj.map ((baseChangeGradedHom F (W.map G)).comp (baseChangeGradedHom G W)) _
  congr 1
/-- (A2 assembly) The transported base-change morphism is functorial: along a composite it factors
through the intermediate curve. -/
theorem projModelBaseChangeOf_comp (F : R →+* R') (G : U →+* R) (W₀ : WeierstrassCurve U)
    (W : WeierstrassCurve R) (h : W₀.map G = W) (W' : WeierstrassCurve R') (h' : W.map F = W') :
    projModelBaseChangeOf (F.comp G) W₀ W'
        (by rw [← WeierstrassCurve.map_map, h, h']) =
      projModelBaseChangeOf F W W' h' ≫ projModelBaseChangeOf G W₀ W h := by
  subst h h'
  rw [projModelBaseChangeOf, projModelBaseChangeOf, projModelBaseChangeOf]
  simp only [eqToHom_refl, Category.id_comp]
  exact projModelBaseChange_comp' F G W₀
/-- Transport across an equality of classifying homs (proofs are irrelevant). -/
theorem mulModelHomBC_congr (f₁ f₂ : U →+* R) (hf : f₁ = f₂) (W₀ : WeierstrassCurve U)
    [IsDomain U] [IsJacobsonRing U] (hΔ₀ : IsUnit W₀.Δ)
    (W : WeierstrassCurve R) (h₁ : W₀.map f₁ = W) (h₂ : W₀.map f₂ = W) :
    mulModelHomBC f₁ W₀ hΔ₀ W h₁ = mulModelHomBC f₂ W₀ hΔ₀ W h₂ := by
  subst hf; rfl

/-- The transported base change at `h := rfl` is the plain base change. -/
theorem projModelBaseChangeOf_rfl (f : U →+* R) (W₀ : WeierstrassCurve U) :
    projModelBaseChangeOf f W₀ (W₀.map f) rfl = projModelBaseChange f W₀ := by
  rw [projModelBaseChangeOf]
  simp

/-- `projModelBaseChange f W ≫ bcOf G = bcOf (f.comp G)` — the composite collapse. -/
theorem projModelBaseChange_comp_projModelBaseChangeOf (G : U →+* R) (f : R →+* R')
    (W₀ : WeierstrassCurve U) (W : WeierstrassCurve R) (h : W₀.map G = W) :
    projModelBaseChange f W ≫ projModelBaseChangeOf G W₀ W h =
      projModelBaseChangeOf (f.comp G) W₀ (W.map f)
        (by rw [← WeierstrassCurve.map_map, h]) := by
  rw [projModelBaseChangeOf_comp f G W₀ W h (W.map f) rfl, projModelBaseChangeOf_rfl]

/-- The base-change fibre-square maps compose. -/
@[reassoc]
theorem pullbackMapBaseChangeOf_comp (G : U →+* R) (f : R →+* R')
    (W₀ : WeierstrassCurve U) (W : WeierstrassCurve R) (h : W₀.map G = W) :
    pullback.map (projModelπ (W.map f)) (projModelπ (W.map f)) (projModelπ W) (projModelπ W)
        (projModelBaseChange f W) (projModelBaseChange f W) (Spec.map (CommRingCat.ofHom f))
        (projModelBaseChange_π f W).symm (projModelBaseChange_π f W).symm ≫
      pullbackMapBaseChangeOf G W₀ W h =
    pullbackMapBaseChangeOf (f.comp G) W₀ (W.map f)
      (by rw [← WeierstrassCurve.map_map, h]) := by
  apply pullback.hom_ext
  · simp only [pullbackMapBaseChangeOf, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      projModelBaseChange_comp_projModelBaseChangeOf G f W₀ W h]
  · simp only [pullbackMapBaseChangeOf, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
      projModelBaseChange_comp_projModelBaseChangeOf G f W₀ W h]

/-- **(c4.5 nat, BC level)** Base-change naturality of the lifted multiplication, classify-free. -/
theorem mulModelHomBC_map (G : U →+* R) (f : R →+* R') (W₀ : WeierstrassCurve U)
    [IsDomain U] [IsJacobsonRing U] (hΔ₀ : IsUnit W₀.Δ)
    (W : WeierstrassCurve R) (h : W₀.map G = W) :
    mulModelHomBC (f.comp G) W₀ hΔ₀ (W.map f)
        (by rw [← WeierstrassCurve.map_map, h]) ≫ projModelBaseChange f W =
      pullback.map (projModelπ (W.map f)) (projModelπ (W.map f)) (projModelπ W) (projModelπ W)
          (projModelBaseChange f W) (projModelBaseChange f W) (Spec.map (CommRingCat.ofHom f))
          (projModelBaseChange_π f W).symm (projModelBaseChange_π f W).symm ≫
        mulModelHomBC G W₀ hΔ₀ W h := by
  apply (isPullback_projModelBaseChangeOf G W₀ W h).hom_ext
  · -- fst-leg: both collapse to (pbmap of f.comp G) ≫ mulModelHom_U
    simp only [Category.assoc, projModelBaseChange_comp_projModelBaseChangeOf G f W₀ W h,
      mulModelHomBC_baseChange,
      pullbackMapBaseChangeOf_comp_assoc G f W₀ W h]
  · -- snd-leg: both collapse to fst ≫ π ≫ Spec f
    simp only [Category.assoc, projModelBaseChange_π, mulModelHomBC_projModelπ,
      mulModelHomBC_projModelπ_assoc, pullback.lift_fst_assoc]
end BaseChangeFunctoriality

section IdCollapse

/-- The universal curve classifies itself by the identity. -/
theorem classifyRingHom_universalWeierstrassLoc :
    classifyRingHom universalWeierstrassLoc = RingHom.id WeierstrassAtlasRing := by
  apply IsLocalization.ringHom_ext (Submonoid.powers universalWeierstrass.Δ)
  have h1 : (classifyRingHom universalWeierstrassLoc).comp
      (algebraMap (MvPolynomial (Fin 5) ℤ) WeierstrassAtlasRing) =
      classifyCoeffHom universalWeierstrassLoc := by
    simp only [classifyRingHom, IsLocalization.Away.lift_comp]
  rw [h1, RingHom.id_comp]
  apply MvPolynomial.ringHom_ext
  · intro n
    simp [classifyCoeffHom]
  · intro i
    fin_cases i <;>
      simp [classifyCoeffHom, universalWeierstrassLoc, universalWeierstrass,
        map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]

variable {R : Type u} [CommRing R]

/-- Base change along the identity is the identity (`Proj.map_id` through the graded quotient). -/
theorem projModelBaseChange_id (W : WeierstrassCurve R) :
    projModelBaseChange (RingHom.id R) W = 𝟙 (projModel W) := by
  have bmk : ∀ p : MvPolynomial (Fin 3) R,
      baseChangeGradedHom (RingHom.id R) W (Ideal.Quotient.mk (projIdeal W).toIdeal p)
        = Ideal.Quotient.mk (projIdeal (W.map (RingHom.id R))).toIdeal
            (MvPolynomial.map (RingHom.id R) p) :=
    fun p => HomogeneousIdeal.quotientGradingMap_mk (mvMapGraded (RingHom.id R)) (projIdeal W)
      (projIdeal (W.map (RingHom.id R))) (projIdeal_le_comap (RingHom.id R) W) p
  have hgraded : baseChangeGradedHom (RingHom.id R) W = GradedRingHom.id _ := by
    refine GradedRingHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    show baseChangeGradedHom (RingHom.id R) W (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a
    rw [bmk]
    exact congrArg (Ideal.Quotient.mk _) (MvPolynomial.map_id a)
  rw [projModelBaseChange]
  refine Eq.trans ?_ Proj.map_id
  congr 1
/-- [C6-U3a] The ULift universal curve classifies itself by the identity. -/
theorem classifyRingHomU_universalWeierstrassLocU :
    classifyRingHomU universalWeierstrassLocU.{u} = RingHom.id (WeierstrassAtlasRingU.{u}) := by
  suffices h : (classifyRingHomU universalWeierstrassLocU.{u}).comp
      (ULift.ringEquiv (R := WeierstrassAtlasRing)).symm.toRingHom =
      (RingHom.id (WeierstrassAtlasRingU.{u})).comp
        (ULift.ringEquiv (R := WeierstrassAtlasRing)).symm.toRingHom by
    refine RingHom.ext fun x => ?_
    have hx := RingHom.congr_fun h (ULift.ringEquiv x)
    simpa using hx
  apply IsLocalization.ringHom_ext (Submonoid.powers universalWeierstrass.Δ)
  have hcoe : (classifyRingHom universalWeierstrassLocU.{u}).comp
      (algebraMap (MvPolynomial (Fin 5) ℤ) WeierstrassAtlasRing) =
      classifyCoeffHom universalWeierstrassLocU.{u} := by
    simp only [classifyRingHom, IsLocalization.Away.lift_comp]
  refine MvPolynomial.ringHom_ext (fun n => ?_) (fun i => ?_)
  · simp [classifyRingHomU]
  · have hx := RingHom.congr_fun hcoe (MvPolynomial.X i)
    rw [RingHom.comp_apply] at hx
    simp only [classifyRingHomU, RingHom.comp_apply, RingHom.id_apply,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply]
    rw [hx]
    fin_cases i <;>
      simp [classifyCoeffHom, universalWeierstrassLocU, universalWeierstrassLoc,
        universalWeierstrass, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]

theorem projModelBaseChangeOf_id (W : WeierstrassCurve R) :
    projModelBaseChangeOf (RingHom.id R) W W rfl = 𝟙 (projModel W) :=
  (projModelBaseChangeOf_rfl (RingHom.id R) W).trans (projModelBaseChange_id W)

/-- The fibre-square base-change map at the identity is the identity. -/
theorem pullbackMapBaseChangeOf_id (W : WeierstrassCurve R) :
    pullbackMapBaseChangeOf (RingHom.id R) W W rfl = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [pullbackMapBaseChangeOf_fst (RingHom.id R) W W rfl, Category.id_comp,
      projModelBaseChangeOf_id, Category.comp_id]
  · rw [pullbackMapBaseChangeOf_snd (RingHom.id R) W W rfl, Category.id_comp,
      projModelBaseChangeOf_id, Category.comp_id]

/-- At the identity, the base-change lift IS the two-law multiplication (lift uniqueness). -/
theorem mulModelHomBC_id (W : WeierstrassCurve R) [IsDomain R] [IsJacobsonRing R]
    (hΔ : IsUnit W.Δ) :
    mulModelHomBC (RingHom.id R) W hΔ W rfl = WeierstrassCurve.Projective.mulModelHom W hΔ := by
  apply (isPullback_projModelBaseChangeOf (RingHom.id R) W W rfl).hom_ext
  · rw [mulModelHomBC_baseChange (RingHom.id R) W hΔ W rfl, pullbackMapBaseChangeOf_id,
      Category.id_comp, projModelBaseChangeOf_id, Category.comp_id]
  · rw [mulModelHomBC_projModelπ (RingHom.id R) W hΔ W rfl]
    exact (WeierstrassCurve.Projective.mulModelHom_projModelπ W hΔ).symm

end IdCollapse


end ClassifyNaturality

end BaseChangeOf

end ModularCurves

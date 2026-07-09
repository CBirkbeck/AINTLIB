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

/-- The lift agreement: the base-changed multiplication and the structure map agree over `Spec U`. -/
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
lemma mulModelHomBC_baseChange (f : U →+* R) (W₀ : WeierstrassCurve U)
    [IsDomain U] [IsJacobsonRing U] (hΔ₀ : IsUnit W₀.Δ)
    (W : WeierstrassCurve R) (h : W₀.map f = W) :
    mulModelHomBC f W₀ hΔ₀ W h ≫ projModelBaseChangeOf f W₀ W h =
      pullbackMapBaseChangeOf f W₀ W h ≫ WeierstrassCurve.Projective.mulModelHom W₀ hΔ₀ :=
  (isPullback_projModelBaseChangeOf f W₀ W h).lift_fst _ _ _

/-- The lift is over `Spec R` — `mulModelHom_π` for the base-changed multiplication. -/
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
end BaseChangeFunctoriality

end ClassifyNaturality

end BaseChangeOf

end ModularCurves

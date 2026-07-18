/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.GrassmannianTransition
import ModularCurves.ForMathlib.GrassmannianChart
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The Grassmannian chart atlas as scheme glue data ([NISOG-GRASS], [GR-D]+[GR-F] opening)

Spec-level packaging of the completed transition ring layer
(`GrassmannianTransition.lean`): the affine charts `Spec (ChartRing R ι)`, their
overlaps `Spec ((ChartRing R ι)[1/det ι ι'])` with open-immersion structure maps
([GR-D]), the transition morphisms `Spec (ringHomAway)`, and the `t_id` law. The
`Scheme.GlueData` assembly (t' on pullbacks via `pullbackSpecIso`, t_fac, cocycle — all
reducing to the ring layer per the pinned architecture) is the next increment.

Decomposition artifact: `.mathlib-quality/decomposition-nisog-grass.md` ([STREAM-FP],
fable-FP, [GR-F] architecture pin).
-/

universe u

namespace Module.Grassmannian

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

variable (R : Type u) [CommRing R] {k n : ℕ}

/-- The ι-chart of `Grass(k, R^n)` as an affine scheme: `Spec R[X_{j,i}]`. -/
noncomputable def chartScheme (ι : Fin k ↪ Fin n) : Scheme.{u} :=
  Spec (CommRingCat.of (ChartRing R ι))

/-- The (ι,ι')-overlap: the basic open `D(det ι ι')` of the ι-chart, as the Spec of the
localization. -/
noncomputable def overlapScheme (ι ι' : Fin k ↪ Fin n) : Scheme.{u} :=
  Spec (CommRingCat.of (Localization.Away (Transition.det (R := R) ι ι')))

/-- **[GR-D]** The overlap's structure map into the ι-chart — an open immersion onto
`D(det ι ι')`. -/
noncomputable def overlapι (ι ι' : Fin k ↪ Fin n) :
    overlapScheme R ι ι' ⟶ chartScheme R ι :=
  Spec.map (CommRingCat.ofHom (algebraMap (ChartRing R ι)
    (Localization.Away (Transition.det (R := R) ι ι'))))

instance (ι ι' : Fin k ↪ Fin n) : IsOpenImmersion (overlapι R ι ι') :=
  IsOpenImmersion.of_isLocalization (Transition.det (R := R) ι ι')

/-- The transition morphism between overlaps, `Spec` of `ringHomAway`. -/
noncomputable def overlapTransition (ι ι' : Fin k ↪ Fin n) :
    overlapScheme R ι ι' ⟶ overlapScheme R ι' ι :=
  Spec.map (CommRingCat.ofHom (Transition.ringHomAway (R := R) ι ι'))

/-- The `t_id` law: the self-transition is the identity. -/
lemma overlapTransition_self (ι : Fin k ↪ Fin n) :
    overlapTransition R ι ι = 𝟙 (overlapScheme R ι ι) := by
  rw [overlapTransition, Transition.ringHomAway_self]
  exact Spec.map_id _

/-- The transitions are mutually inverse. -/
lemma overlapTransition_comp (ι ι' : Fin k ↪ Fin n) :
    overlapTransition R ι ι' ≫ overlapTransition R ι' ι
      = 𝟙 (overlapScheme R ι ι') := by
  show Spec.map (CommRingCat.ofHom (Transition.ringHomAway (R := R) ι ι')) ≫
      Spec.map (CommRingCat.ofHom (Transition.ringHomAway (R := R) ι' ι))
    = 𝟙 (Spec (CommRingCat.of (Localization.Away (Transition.det (R := R) ι ι'))))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Transition.ringHomAway_comp_ringHomAway,
    CommRingCat.ofHom_id, Spec.map_id]

section TPrime

open TensorProduct Matrix

variable (ι ι' ι'' : Fin k ↪ Fin n)

/-- The double-overlap coordinate ring `D(ι; ι', ι'')`: the `pullbackSpecIso`
presentation of `D(det ι ι') ∩ D(det ι ι'')` inside the ι-chart. -/
noncomputable abbrev doubleRing : Type u :=
  Localization.Away (Transition.det (R := R) ι ι') ⊗[ChartRing R ι]
    Localization.Away (Transition.det (R := R) ι ι'')

/-- The base leg of the `t'`-map: `ChartRing ι'` into the ι-side double ring, through
the forward transition. -/
noncomputable def tPrimeBase : ChartRing R ι' →+* doubleRing R ι ι' ι'' :=
  Algebra.TensorProduct.includeLeftRingHom.comp (Transition.ringHom (R := R) ι ι')

/-- The reverse determinant is a unit under the base leg ([GR-F1] mapped along
`includeLeft`). -/
lemma isUnit_tPrimeBase_det_left :
    IsUnit (tPrimeBase R ι ι' ι'' (Transition.det (R := R) ι' ι)) := by
  rw [tPrimeBase, RingHom.comp_apply]
  exact (Transition.isUnit_ringHom_det ι ι').map _

/-- The third-chart determinant is a unit under the base leg — [GR-F3]'s abstract unit
condition discharged by the base-element slide `d ⊗ₜ 1 = 1 ⊗ₜ d`. -/
lemma isUnit_tPrimeBase_det_right :
    IsUnit (tPrimeBase R ι ι' ι'' (Transition.det (R := R) ι' ι'')) := by
  rw [tPrimeBase, RingHom.comp_apply]
  refine Transition.isUnit_map_ringHom_det_triple ι ι' ι''
    (Algebra.TensorProduct.includeLeftRingHom :
      Localization.Away (Transition.det (R := R) ι ι') →+* doubleRing R ι ι' ι'') ?_
  have hslide : (Algebra.TensorProduct.includeLeftRingHom :
      Localization.Away (Transition.det (R := R) ι ι') →+* doubleRing R ι ι' ι'')
      (algebraMap (ChartRing R ι) (Localization.Away (Transition.det (R := R) ι ι'))
        (Transition.det (R := R) ι ι''))
      = Algebra.TensorProduct.includeRight
          (algebraMap (ChartRing R ι)
            (Localization.Away (Transition.det (R := R) ι ι''))
            (Transition.det (R := R) ι ι'')) := by
    rw [Algebra.TensorProduct.includeRight_apply]
    rw [show (Algebra.TensorProduct.includeLeftRingHom :
        Localization.Away (Transition.det (R := R) ι ι') →+* doubleRing R ι ι' ι'')
        (algebraMap (ChartRing R ι) (Localization.Away (Transition.det (R := R) ι ι'))
          (Transition.det (R := R) ι ι''))
        = algebraMap (ChartRing R ι) (Localization.Away (Transition.det (R := R) ι ι'))
            (Transition.det (R := R) ι ι'') ⊗ₜ 1 from rfl]
    rw [← Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.algebraMap_apply']
  rw [hslide]
  exact (IsLocalization.Away.algebraMap_isUnit
    (Transition.det (R := R) ι ι'')).map _

/-- The right t'-leg: `Away (det ι' ι'') →+* D(ι; ι', ι'')`, the `Away.lift` of the
base leg at the [GR-F3] unit. -/
noncomputable def tPrimeLegRight :
    Localization.Away (Transition.det (R := R) ι' ι'') →+* doubleRing R ι ι' ι'' :=
  IsLocalization.Away.lift (Transition.det (R := R) ι' ι'')
    (isUnit_tPrimeBase_det_right R ι ι' ι'')

/-- The left t'-leg: `Away (det ι' ι) →+* D(ι; ι', ι'')`, the `Away.lift` of the base
leg at the [GR-F1] unit. -/
noncomputable def tPrimeLegLeft :
    Localization.Away (Transition.det (R := R) ι' ι) →+* doubleRing R ι ι' ι'' :=
  IsLocalization.Away.lift (Transition.det (R := R) ι' ι)
    (isUnit_tPrimeBase_det_left R ι ι' ι'')

/-- **[GR-F t']** The t'-map at ring level: out of the ι'-side double ring into the
ι-side one, `x ⊗ₜ y ↦ legRight x * legLeft y`. -/
noncomputable def tPrimeRing :
    doubleRing R ι' ι'' ι →+* doubleRing R ι ι' ι'' :=
  letI : Algebra (ChartRing R ι') (doubleRing R ι ι' ι'') :=
    (tPrimeBase R ι ι' ι'').toAlgebra
  (Algebra.TensorProduct.productMap
    ({ tPrimeLegRight R ι ι' ι'' with
        commutes' := fun c =>
          IsLocalization.Away.lift_eq _ (isUnit_tPrimeBase_det_right R ι ι' ι'') c } :
      Localization.Away (Transition.det (R := R) ι' ι'') →ₐ[ChartRing R ι']
        doubleRing R ι ι' ι'')
    ({ tPrimeLegLeft R ι ι' ι'' with
        commutes' := fun c =>
          IsLocalization.Away.lift_eq _ (isUnit_tPrimeBase_det_left R ι ι' ι'') c } :
      Localization.Away (Transition.det (R := R) ι' ι) →ₐ[ChartRing R ι']
        doubleRing R ι ι' ι'')).toRingHom

lemma tPrimeRing_tmul (x : Localization.Away (Transition.det (R := R) ι' ι''))
    (y : Localization.Away (Transition.det (R := R) ι' ι)) :
    tPrimeRing R ι ι' ι'' (x ⊗ₜ y)
      = tPrimeLegRight R ι ι' ι'' x * tPrimeLegLeft R ι ι' ι'' y := rfl

/-- The left t'-leg is the transition followed by the left inclusion — the ring-level
`t_fac` identity. -/
lemma tPrimeLegLeft_eq :
    tPrimeLegLeft R ι ι' ι''
      = (Algebra.TensorProduct.includeLeftRingHom :
          Localization.Away (Transition.det (R := R) ι ι') →+* doubleRing R ι ι' ι'').comp
        (Transition.ringHomAway (R := R) ι ι') := by
  refine IsLocalization.ringHom_ext
    (Submonoid.powers (Transition.det (R := R) ι' ι)) ?_
  refine RingHom.ext fun q => ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
    Transition.ringHomAway_algebraMap]
  exact IsLocalization.Away.lift_eq _ (isUnit_tPrimeBase_det_left R ι ι' ι'') q

/-- **[GR-F t']** The t'-morphism of the chart atlas: conjugate `Spec` of `tPrimeRing`
by the `pullbackSpecIso` presentations. -/
noncomputable def tPrimeScheme :
    pullback (overlapι R ι ι') (overlapι R ι ι'')
      ⟶ pullback (overlapι R ι' ι'') (overlapι R ι' ι) :=
  (pullbackSpecIso (ChartRing R ι) _ _).hom ≫
    Spec.map (CommRingCat.ofHom (tPrimeRing R ι ι' ι'')) ≫
      (pullbackSpecIso (ChartRing R ι') _ _).inv

/-- The `t_fac` law of the atlas glue data. -/
lemma tPrimeScheme_fac :
    tPrimeScheme R ι ι' ι'' ≫ pullback.snd (overlapι R ι' ι'') (overlapι R ι' ι)
      = pullback.fst (overlapι R ι ι') (overlapι R ι ι'') ≫
          overlapTransition R ι ι' := by
  show (pullbackSpecIso (ChartRing R ι)
        (Localization.Away (Transition.det (R := R) ι ι'))
        (Localization.Away (Transition.det (R := R) ι ι''))).hom ≫
      Spec.map (CommRingCat.ofHom (tPrimeRing R ι ι' ι'')) ≫
        (pullbackSpecIso (ChartRing R ι')
          (Localization.Away (Transition.det (R := R) ι' ι''))
          (Localization.Away (Transition.det (R := R) ι' ι))).inv ≫
          pullback.snd
            (Spec.map (CommRingCat.ofHom (algebraMap (ChartRing R ι')
              (Localization.Away (Transition.det (R := R) ι' ι'')))))
            (Spec.map (CommRingCat.ofHom (algebraMap (ChartRing R ι')
              (Localization.Away (Transition.det (R := R) ι' ι)))))
    = pullback.fst
        (Spec.map (CommRingCat.ofHom (algebraMap (ChartRing R ι)
          (Localization.Away (Transition.det (R := R) ι ι')))))
        (Spec.map (CommRingCat.ofHom (algebraMap (ChartRing R ι)
          (Localization.Away (Transition.det (R := R) ι ι''))))) ≫
        Spec.map (CommRingCat.ofHom (Transition.ringHomAway (R := R) ι ι'))
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [show (tPrimeRing R ι ι' ι'').comp
        ((Algebra.TensorProduct.includeRight :
          Localization.Away (Transition.det (R := R) ι' ι) →ₐ[ChartRing R ι']
            doubleRing R ι' ι'' ι) :
          Localization.Away (Transition.det (R := R) ι' ι) →+* doubleRing R ι' ι'' ι)
      = tPrimeLegLeft R ι ι' ι'' from by
    refine RingHom.ext fun y => ?_
    rw [RingHom.comp_apply]
    rw [show (((Algebra.TensorProduct.includeRight :
        Localization.Away (Transition.det (R := R) ι' ι) →ₐ[ChartRing R ι']
          doubleRing R ι' ι'' ι) :
        Localization.Away (Transition.det (R := R) ι' ι) →+* doubleRing R ι' ι'' ι) y :
        doubleRing R ι' ι'' ι)
        = (1 : Localization.Away (Transition.det (R := R) ι' ι'')) ⊗ₜ y from rfl]
    rw [tPrimeRing_tmul, map_one, one_mul]]
  rw [tPrimeLegLeft_eq]
  have hsplit : (CommRingCat.ofHom
      ((Algebra.TensorProduct.includeLeftRingHom :
        Localization.Away (Transition.det (R := R) ι ι') →+* doubleRing R ι ι' ι'').comp
        (Transition.ringHomAway (R := R) ι ι')) :
        CommRingCat.of (Localization.Away (Transition.det (R := R) ι' ι)) ⟶
          CommRingCat.of (doubleRing R ι ι' ι''))
      = CommRingCat.ofHom (Transition.ringHomAway (R := R) ι ι') ≫
        CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          Localization.Away (Transition.det (R := R) ι ι') →+* doubleRing R ι ι' ι'') := rfl
  rw [hsplit, Spec.map_comp, pullbackSpecIso_hom_fst_assoc]

private lemma tPrimeRing_comp_includeLeft :
    (tPrimeRing R ι ι' ι'').comp (Algebra.TensorProduct.includeLeftRingHom :
      Localization.Away (Transition.det (R := R) ι' ι'') →+* doubleRing R ι' ι'' ι)
      = tPrimeLegRight R ι ι' ι'' := by
  refine RingHom.ext fun x => ?_
  rw [RingHom.comp_apply]
  rw [show (Algebra.TensorProduct.includeLeftRingHom x : doubleRing R ι' ι'' ι)
      = x ⊗ₜ 1 from rfl]
  rw [tPrimeRing_tmul, map_one, mul_one]

private lemma tPrimeRing_comp_includeRight :
    (tPrimeRing R ι ι' ι'').comp
      ((Algebra.TensorProduct.includeRight :
        Localization.Away (Transition.det (R := R) ι' ι) →ₐ[ChartRing R ι']
          doubleRing R ι' ι'' ι) :
        Localization.Away (Transition.det (R := R) ι' ι) →+* doubleRing R ι' ι'' ι)
      = tPrimeLegLeft R ι ι' ι'' := by
  refine RingHom.ext fun y => ?_
  rw [RingHom.comp_apply]
  rw [show (((Algebra.TensorProduct.includeRight :
      Localization.Away (Transition.det (R := R) ι' ι) →ₐ[ChartRing R ι']
        doubleRing R ι' ι'' ι) :
      Localization.Away (Transition.det (R := R) ι' ι) →+* doubleRing R ι' ι'' ι) y :
      doubleRing R ι' ι'' ι) = (1 : Localization.Away
        (Transition.det (R := R) ι' ι'')) ⊗ₜ y from rfl]
  rw [tPrimeRing_tmul, map_one, one_mul]

/-- The two base inclusions agree on the chart ring — the base-element slide at map
level. -/
private lemma includeLeft_algebraMap_eq_includeRight_algebraMap :
    ((Algebra.TensorProduct.includeLeftRingHom :
      Localization.Away (Transition.det (R := R) ι ι') →+* doubleRing R ι ι' ι'').comp
        (algebraMap (ChartRing R ι) (Localization.Away (Transition.det (R := R) ι ι'))))
    = ((Algebra.TensorProduct.includeRight :
        Localization.Away (Transition.det (R := R) ι ι'') →ₐ[ChartRing R ι]
          doubleRing R ι ι' ι'') :
        Localization.Away (Transition.det (R := R) ι ι'') →+* doubleRing R ι ι' ι'').comp
        (algebraMap (ChartRing R ι)
          (Localization.Away (Transition.det (R := R) ι ι''))) := by
  refine RingHom.ext fun q => ?_
  rw [RingHom.comp_apply, RingHom.comp_apply]
  rw [show ((Algebra.TensorProduct.includeLeftRingHom :
      Localization.Away (Transition.det (R := R) ι ι') →+* doubleRing R ι ι' ι'')
      (algebraMap (ChartRing R ι) (Localization.Away (Transition.det (R := R) ι ι')) q) :
      doubleRing R ι ι' ι'')
      = algebraMap (ChartRing R ι) (Localization.Away (Transition.det (R := R) ι ι')) q
        ⊗ₜ 1 from rfl]
  rw [show (((Algebra.TensorProduct.includeRight :
      Localization.Away (Transition.det (R := R) ι ι'') →ₐ[ChartRing R ι]
        doubleRing R ι ι' ι'') :
      Localization.Away (Transition.det (R := R) ι ι'') →+* doubleRing R ι ι' ι'')
      (algebraMap (ChartRing R ι) (Localization.Away (Transition.det (R := R) ι ι'')) q) :
      doubleRing R ι ι' ι'')
      = (1 : Localization.Away (Transition.det (R := R) ι ι')) ⊗ₜ
          algebraMap (ChartRing R ι)
            (Localization.Away (Transition.det (R := R) ι ι'')) q from rfl]
  rw [← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']

/-- The right t'-leg precomposed with the base `algebraMap` is the base leg
`tPrimeBase` — the defining `IsLocalization.Away.lift` equation of `tPrimeLegRight`. -/
lemma tPrimeLegRight_algebraMap (q : ChartRing R ι') :
    tPrimeLegRight R ι ι' ι'' (algebraMap (ChartRing R ι')
        (Localization.Away (Transition.det (R := R) ι' ι'')) q)
      = tPrimeBase R ι ι' ι'' q :=
  IsLocalization.Away.lift_eq _ (isUnit_tPrimeBase_det_right R ι ι' ι'') q

/-- The middle telescope step: transporting the ι''→ι base `algebraMap` up through the
right leg and `tPrimeRing` lands on the right leg of the ι'→ι'' transition. -/
lemma tPrimeRing_tPrimeLegRight_algebraMap (q : ChartRing R ι'') :
    tPrimeRing R ι ι' ι'' (tPrimeLegRight R ι' ι'' ι
        (algebraMap (ChartRing R ι'')
          (Localization.Away (Transition.det (R := R) ι'' ι)) q))
      = tPrimeLegRight R ι ι' ι'' (Transition.ringHom (R := R) ι' ι'' q) := by
  rw [tPrimeLegRight_algebraMap R ι' ι'' ι q]
  have hcl := RingHom.congr_fun (tPrimeRing_comp_includeLeft R ι ι' ι'')
    (Transition.ringHom (R := R) ι' ι'' q)
  rw [RingHom.comp_apply] at hcl
  exact hcl

/-- The ι→ι'' telescope matrix (`matrix ι ι''` pushed into the ι-side double ring through
`includeLeft ∘ algebraMap`) has unit determinant: its determinant is
`includeLeft (algebraMap (det ι ι''))`, a unit by the base-element slide. -/
private lemma isUnit_det_matrix_includeLeft :
    IsUnit (((Transition.matrix (R := R) ι ι'').map (fun q =>
      (Algebra.TensorProduct.includeLeftRingHom :
          Localization.Away (Transition.det (R := R) ι ι') →+* doubleRing R ι ι' ι'')
        (algebraMap (ChartRing R ι)
          (Localization.Away (Transition.det (R := R) ι ι')) q))).det) := by
  have hKdet' : ((Transition.matrix (R := R) ι ι'').map (fun q =>
      (Algebra.TensorProduct.includeLeftRingHom :
          Localization.Away (Transition.det (R := R) ι ι') →+* doubleRing R ι ι' ι'')
        (algebraMap (ChartRing R ι)
          (Localization.Away (Transition.det (R := R) ι ι')) q))).det
      = (Algebra.TensorProduct.includeLeftRingHom :
          Localization.Away (Transition.det (R := R) ι ι') →+* doubleRing R ι ι' ι'')
        (algebraMap (ChartRing R ι)
          (Localization.Away (Transition.det (R := R) ι ι'))
          (Transition.det (R := R) ι ι'')) := by
    rw [show ((Transition.matrix (R := R) ι ι'').map
        (fun q => (Algebra.TensorProduct.includeLeftRingHom :
            Localization.Away (Transition.det (R := R) ι ι') →+* doubleRing R ι ι' ι'')
          (algebraMap (ChartRing R ι)
            (Localization.Away (Transition.det (R := R) ι ι')) q)))
        = (Transition.matrix (R := R) ι ι'').map
          ⇑((Algebra.TensorProduct.includeLeftRingHom :
              Localization.Away (Transition.det (R := R) ι ι') →+*
                doubleRing R ι ι' ι'').comp
            (algebraMap (ChartRing R ι)
              (Localization.Away (Transition.det (R := R) ι ι')))) from rfl]
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  rw [hKdet']
  have hsw := RingHom.congr_fun
    (includeLeft_algebraMap_eq_includeRight_algebraMap R ι ι' ι'')
    (Transition.det (R := R) ι ι'')
  rw [RingHom.comp_apply, RingHom.comp_apply] at hsw
  rw [hsw]
  exact (IsLocalization.Away.algebraMap_isUnit
    (Transition.det (R := R) ι ι'')).map _

/-- The core of the cocycle: the triple transition composite restricted to the ι-chart
ring is the canonical base map. Proven by the matrix telescope `N₂ = N₃⁻¹ · M₁⁻¹`. -/
private lemma cocycle_core :
    (((tPrimeRing R ι ι' ι'').comp (tPrimeLegRight R ι' ι'' ι)).comp
        (Transition.ringHom (R := R) ι'' ι))
      = (Algebra.TensorProduct.includeLeftRingHom :
          Localization.Away (Transition.det (R := R) ι ι') →+* doubleRing R ι ι' ι'').comp
        (algebraMap (ChartRing R ι)
          (Localization.Away (Transition.det (R := R) ι ι'))) := by
  classical
  set inclL : Localization.Away (Transition.det (R := R) ι ι') →+* doubleRing R ι ι' ι'' :=
    Algebra.TensorProduct.includeLeftRingHom with hinclL
  -- composition specs, all in nested-application form
  have hF₃alg : ∀ q, tPrimeLegRight R ι ι' ι''
      (algebraMap (ChartRing R ι')
        (Localization.Away (Transition.det (R := R) ι' ι'')) q)
      = inclL (Transition.ringHom (R := R) ι ι' q) := fun q =>
    tPrimeLegRight_algebraMap R ι ι' ι'' q
  have hF₂alg : ∀ q, tPrimeRing R ι ι' ι'' (tPrimeLegRight R ι' ι'' ι
      (algebraMap (ChartRing R ι'')
        (Localization.Away (Transition.det (R := R) ι'' ι)) q))
      = tPrimeLegRight R ι ι' ι'' (Transition.ringHom (R := R) ι' ι'' q) := fun q =>
    tPrimeRing_tPrimeLegRight_algebraMap R ι ι' ι'' q
  -- the telescope matrices (function-literal maps) and their determinant units
  set M₁ : Matrix (Fin k) (Fin k) (doubleRing R ι ι' ι'') :=
    (Transition.matrix (R := R) ι ι').map (fun q => inclL (algebraMap (ChartRing R ι)
      (Localization.Away (Transition.det (R := R) ι ι')) q)) with hM₁
  set K : Matrix (Fin k) (Fin k) (doubleRing R ι ι' ι'') :=
    (Transition.matrix (R := R) ι ι'').map (fun q => inclL (algebraMap (ChartRing R ι)
      (Localization.Away (Transition.det (R := R) ι ι')) q)) with hK
  set N₃ : Matrix (Fin k) (Fin k) (doubleRing R ι ι' ι'') :=
    (Transition.matrix (R := R) ι' ι'').map (fun q => tPrimeLegRight R ι ι' ι''
      (algebraMap (ChartRing R ι')
        (Localization.Away (Transition.det (R := R) ι' ι'')) q)) with hN₃
  set N₂ : Matrix (Fin k) (Fin k) (doubleRing R ι ι' ι'') :=
    (Transition.matrix (R := R) ι'' ι).map (fun q => tPrimeRing R ι ι' ι''
      (tPrimeLegRight R ι' ι'' ι (algebraMap (ChartRing R ι'')
        (Localization.Away (Transition.det (R := R) ι'' ι)) q))) with hN₂
  have hM₁eq : M₁ = (Transition.matrixAway (R := R) ι ι').map ⇑inclL := by
    rw [hM₁, Transition.matrixAway, Matrix.map_map]
    rfl
  have hM₁det : IsUnit M₁.det := by
    rw [hM₁eq, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (Transition.isUnit_det_matrixAway ι ι').map _
  have hKdet : IsUnit K.det := isUnit_det_matrix_includeLeft R ι ι' ι''
  have hN₃eq : N₃ = M₁⁻¹ * K := by
    have h1 : N₃ = ((Transition.matrix (R := R) ι' ι'').map
        ⇑(Transition.ringHom (R := R) ι ι')).map ⇑inclL := by
      rw [hN₃, Matrix.map_map]
      exact congrArg (Matrix.map (Transition.matrix (R := R) ι' ι''))
        (funext fun q => hF₃alg q)
    have h2 : ((Transition.matrixAway (R := R) ι ι')⁻¹ *
        (Transition.matrix (R := R) ι ι'').map (algebraMap (ChartRing R ι)
          (Localization.Away (Transition.det (R := R) ι ι')))).map ⇑inclL
        = ((Transition.matrixAway (R := R) ι ι')⁻¹.map ⇑inclL) *
          (((Transition.matrix (R := R) ι ι'').map (algebraMap (ChartRing R ι)
            (Localization.Away (Transition.det (R := R) ι ι')))).map ⇑inclL) := by
      funext i₁ i₂
      simp [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul]
    rw [h1, Transition.map_ringHom_matrix_triple, h2,
      ← Transition.map_nonsing_inv inclL _ (Transition.isUnit_det_matrixAway ι ι'),
      ← hM₁eq, hK, Matrix.map_map]
    rfl
  have hN₃det : IsUnit N₃.det := by
    rw [hN₃eq, Matrix.det_mul]
    exact (Matrix.isUnit_det_of_left_inverse
      (Matrix.mul_nonsing_inv _ hM₁det)).mul hKdet
  have hN₃away : (Transition.matrixAway (R := R) ι' ι'').map
      ⇑(tPrimeLegRight R ι ι' ι'') = N₃ := by
    rw [hN₃, Transition.matrixAway, Matrix.map_map]
    rfl
  have hN₂eq : N₂ = N₃⁻¹ * M₁⁻¹ := by
    have h1 : N₂ = ((Transition.matrix (R := R) ι'' ι).map
        ⇑(Transition.ringHom (R := R) ι' ι'')).map
          ⇑(tPrimeLegRight R ι ι' ι'') := by
      rw [hN₂, Matrix.map_map]
      exact congrArg (Matrix.map (Transition.matrix (R := R) ι'' ι))
        (funext fun q => hF₂alg q)
    have h2 : ((Transition.matrixAway (R := R) ι' ι'')⁻¹ *
        (Transition.matrix (R := R) ι' ι).map (algebraMap (ChartRing R ι')
          (Localization.Away (Transition.det (R := R) ι' ι'')))).map
          ⇑(tPrimeLegRight R ι ι' ι'')
        = ((Transition.matrixAway (R := R) ι' ι'')⁻¹.map
            ⇑(tPrimeLegRight R ι ι' ι'')) *
          (((Transition.matrix (R := R) ι' ι).map (algebraMap (ChartRing R ι')
            (Localization.Away (Transition.det (R := R) ι' ι'')))).map
            ⇑(tPrimeLegRight R ι ι' ι'')) := by
      funext i₁ i₂
      simp [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul]
    have h3 : ((Transition.matrix (R := R) ι' ι).map (algebraMap (ChartRing R ι')
        (Localization.Away (Transition.det (R := R) ι' ι'')))).map
        ⇑(tPrimeLegRight R ι ι' ι'')
        = ((Transition.matrix (R := R) ι' ι).map
          ⇑(Transition.ringHom (R := R) ι ι')).map ⇑inclL := by
      rw [Matrix.map_map, Matrix.map_map]
      exact congrArg (Matrix.map (Transition.matrix (R := R) ι' ι))
        (funext fun q => hF₃alg q)
    rw [h1, Transition.map_ringHom_matrix_triple, h2,
      ← Transition.map_nonsing_inv (tPrimeLegRight R ι ι' ι'') _
        (Transition.isUnit_det_matrixAway ι' ι''), hN₃away, h3,
      Transition.map_ringHom_matrix,
      ← Transition.map_nonsing_inv inclL _ (Transition.isUnit_det_matrixAway ι ι'),
      ← hM₁eq]
  have hN₂det : IsUnit N₂.det := by
    rw [hN₂eq, Matrix.det_mul]
    exact (Matrix.isUnit_det_of_left_inverse
      (Matrix.mul_nonsing_inv _ hN₃det)).mul
      (Matrix.isUnit_det_of_left_inverse (Matrix.mul_nonsing_inv _ hM₁det))
  -- generator check
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun p => ?_)
  · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply]
    rw [show Transition.ringHom (R := R) ι'' ι (MvPolynomial.C a)
        = algebraMap (ChartRing R ι'')
            (Localization.Away (Transition.det (R := R) ι'' ι))
            (MvPolynomial.C a) from MvPolynomial.eval₂Hom_C _ _ a]
    rw [hF₂alg]
    rw [show Transition.ringHom (R := R) ι' ι'' (MvPolynomial.C a)
        = algebraMap (ChartRing R ι')
            (Localization.Away (Transition.det (R := R) ι' ι''))
            (MvPolynomial.C a) from MvPolynomial.eval₂Hom_C _ _ a]
    rw [hF₃alg]
    rw [show Transition.ringHom (R := R) ι ι' (MvPolynomial.C a)
        = algebraMap (ChartRing R ι)
            (Localization.Away (Transition.det (R := R) ι ι'))
            (MvPolynomial.C a) from MvPolynomial.eval₂Hom_C _ _ a]
  · obtain ⟨⟨j, hj⟩, i⟩ := p
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply]
    have hX : (MvPolynomial.X (⟨j, hj⟩, i) : ChartRing R ι)
        = Transition.column ι j i :=
      (congrFun (Transition.column_notMem ι hj) i).symm
    rw [hX]
    -- the three transport steps, normalized to nested-application form
    have h1 := Transition.comp_ringHom_column (R := R) ι'' ι
      ((tPrimeRing R ι ι' ι'').comp (tPrimeLegRight R ι' ι'' ι))
      (by
        rw [show (Transition.matrix (R := R) ι'' ι).map
            (⇑((tPrimeRing R ι ι' ι'').comp (tPrimeLegRight R ι' ι'' ι)) ∘
              ⇑(algebraMap (ChartRing R ι'')
                (Localization.Away (Transition.det (R := R) ι'' ι))))
            = N₂ from by rw [hN₂]; rfl]
        exact hN₂det) j
    simp only [RingHom.coe_comp, Function.comp_apply, Function.comp_def] at h1
    have h2 := Transition.comp_ringHom_column (R := R) ι' ι''
      (tPrimeLegRight R ι ι' ι'')
      (by
        rw [show (Transition.matrix (R := R) ι' ι'').map
            (⇑(tPrimeLegRight R ι ι' ι'') ∘ ⇑(algebraMap (ChartRing R ι')
              (Localization.Away (Transition.det (R := R) ι' ι''))))
            = N₃ from by rw [hN₃]; rfl]
        exact hN₃det) j
    simp only [Function.comp_def] at h2
    have h3 := Transition.comp_ringHom_column (R := R) ι ι' inclL
      (by
        rw [show (Transition.matrix (R := R) ι ι').map
            (⇑inclL ∘ ⇑(algebraMap (ChartRing R ι)
              (Localization.Away (Transition.det (R := R) ι ι'))))
            = M₁ from by rw [hM₁]; rfl]
        exact hM₁det) j
    simp only [Function.comp_def] at h3
    -- assemble the telescoped vector identity
    have h1' : (fun l => tPrimeRing R ι ι' ι'' (tPrimeLegRight R ι' ι'' ι
        (Transition.ringHom (R := R) ι'' ι (Transition.column ι j l))))
        = N₂⁻¹ *ᵥ (fun l => tPrimeRing R ι ι' ι'' (tPrimeLegRight R ι' ι'' ι
          (algebraMap (ChartRing R ι'')
            (Localization.Away (Transition.det (R := R) ι'' ι))
            (Transition.column ι'' j l)))) := by
      rw [hN₂]
      exact h1
    have h12 : (fun l => tPrimeRing R ι ι' ι'' (tPrimeLegRight R ι' ι'' ι
        (algebraMap (ChartRing R ι'')
          (Localization.Away (Transition.det (R := R) ι'' ι))
          (Transition.column ι'' j l))))
        = fun l => tPrimeLegRight R ι ι' ι''
            (Transition.ringHom (R := R) ι' ι'' (Transition.column ι'' j l)) :=
      funext fun l => hF₂alg _
    have h2' : (fun l => tPrimeLegRight R ι ι' ι''
        (Transition.ringHom (R := R) ι' ι'' (Transition.column ι'' j l)))
        = N₃⁻¹ *ᵥ (fun l => tPrimeLegRight R ι ι' ι''
          (algebraMap (ChartRing R ι')
            (Localization.Away (Transition.det (R := R) ι' ι''))
            (Transition.column ι' j l))) := by
      rw [hN₃]
      exact h2
    have h23 : (fun l => tPrimeLegRight R ι ι' ι''
        (algebraMap (ChartRing R ι')
          (Localization.Away (Transition.det (R := R) ι' ι''))
          (Transition.column ι' j l)))
        = fun l => inclL (Transition.ringHom (R := R) ι ι'
            (Transition.column ι' j l)) :=
      funext fun l => hF₃alg _
    have h3' : (fun l => inclL (Transition.ringHom (R := R) ι ι'
        (Transition.column ι' j l)))
        = M₁⁻¹ *ᵥ (fun l => inclL (algebraMap (ChartRing R ι)
          (Localization.Away (Transition.det (R := R) ι ι'))
          (Transition.column ι j l))) := by
      rw [hM₁]
      exact h3
    have hvec : (fun l => tPrimeRing R ι ι' ι'' (tPrimeLegRight R ι' ι'' ι
        (Transition.ringHom (R := R) ι'' ι (Transition.column ι j l))))
        = N₂⁻¹ *ᵥ (N₃⁻¹ *ᵥ (M₁⁻¹ *ᵥ
          fun l => inclL (algebraMap (ChartRing R ι)
            (Localization.Away (Transition.det (R := R) ι ι'))
            (Transition.column ι j l)))) := by
      rw [h1', h12, h2', h23, h3']
    have hN₂inv : N₂⁻¹ = M₁ * N₃ := by
      rw [hN₂eq, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hN₃det,
        Matrix.nonsing_inv_nonsing_inv _ hM₁det]
    have hfin := congrFun hvec i
    rw [show tPrimeRing R ι ι' ι'' (tPrimeLegRight R ι' ι'' ι
        (Transition.ringHom (R := R) ι'' ι (Transition.column ι j i)))
        = (N₂⁻¹ *ᵥ (N₃⁻¹ *ᵥ (M₁⁻¹ *ᵥ
          fun l => inclL (algebraMap (ChartRing R ι)
            (Localization.Away (Transition.det (R := R) ι ι'))
            (Transition.column ι j l))))) i from hfin]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hN₂inv]
    rw [show M₁ * N₃ * N₃⁻¹ * M₁⁻¹ = 1 from by
      rw [Matrix.mul_assoc M₁ N₃, Matrix.mul_nonsing_inv _ hN₃det, Matrix.mul_one,
        Matrix.mul_nonsing_inv _ hM₁det]]
    rw [Matrix.one_mulVec]

/-- **[GR-F cocycle, ring level]** The triple composite of t'-maps is the identity —
the last glue condition of the chart atlas. -/
theorem tPrimeRing_cocycle :
    (tPrimeRing R ι ι' ι'').comp
        ((tPrimeRing R ι' ι'' ι).comp (tPrimeRing R ι'' ι ι'))
      = RingHom.id (doubleRing R ι ι' ι'') := by
  have hcore := cocycle_core R ι ι' ι''
  refine Algebra.TensorProduct.ringHom_ext ?_ ?_
  · refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply, RingHom.id_apply]
    -- reduce the first transition on the left factor
    have s1 : tPrimeRing R ι'' ι ι'
        ((Algebra.TensorProduct.includeLeftRingHom :
          Localization.Away (Transition.det (R := R) ι ι') →+*
            doubleRing R ι ι' ι'') x)
        = tPrimeLegRight R ι'' ι ι' x := by
      have := RingHom.congr_fun (tPrimeRing_comp_includeLeft R ι'' ι ι') x
      rw [RingHom.comp_apply] at this
      exact this
    rw [s1]
    -- both remaining composites out of Away(det ι ι'): compare on the base ring
    have hAB : ((tPrimeRing R ι ι' ι'').comp ((tPrimeRing R ι' ι'' ι).comp
        (tPrimeLegRight R ι'' ι ι')))
        = (Algebra.TensorProduct.includeLeftRingHom :
          Localization.Away (Transition.det (R := R) ι ι') →+*
            doubleRing R ι ι' ι'') := by
      refine IsLocalization.ringHom_ext
        (Submonoid.powers (Transition.det (R := R) ι ι')) (RingHom.ext fun q => ?_)
      simp only [RingHom.comp_apply]
      have s2 : tPrimeLegRight R ι'' ι ι' (algebraMap (ChartRing R ι)
          (Localization.Away (Transition.det (R := R) ι ι')) q)
          = tPrimeBase R ι'' ι ι' q :=
        IsLocalization.Away.lift_eq _ (isUnit_tPrimeBase_det_right R ι'' ι ι') q
      rw [s2]
      rw [show (tPrimeBase R ι'' ι ι' q : doubleRing R ι'' ι ι')
          = Algebra.TensorProduct.includeLeftRingHom
              (Transition.ringHom (R := R) ι'' ι q) from rfl]
      have s3 : tPrimeRing R ι' ι'' ι
          ((Algebra.TensorProduct.includeLeftRingHom :
            Localization.Away (Transition.det (R := R) ι'' ι) →+*
              doubleRing R ι'' ι ι')
            (Transition.ringHom (R := R) ι'' ι q))
          = tPrimeLegRight R ι' ι'' ι (Transition.ringHom (R := R) ι'' ι q) := by
        have := RingHom.congr_fun (tPrimeRing_comp_includeLeft R ι' ι'' ι)
          (Transition.ringHom (R := R) ι'' ι q)
        rw [RingHom.comp_apply] at this
        exact this
      rw [s3]
      have s4 := RingHom.congr_fun hcore q
      simp only [RingHom.comp_apply] at s4
      exact s4
    have := RingHom.congr_fun hAB x
    simp only [RingHom.comp_apply] at this
    exact this
  · refine RingHom.ext fun y => ?_
    simp only [RingHom.comp_apply, RingHom.id_apply]
    -- reduce the first transition on the right factor
    have s1 : tPrimeRing R ι'' ι ι'
        ((Algebra.TensorProduct.includeRight (R := ChartRing R ι)
          (A := Localization.Away (Transition.det (R := R) ι ι'))
          (B := Localization.Away (Transition.det (R := R) ι ι''))).toRingHom y)
        = tPrimeLegLeft R ι'' ι ι' y := by
      have := RingHom.congr_fun (tPrimeRing_comp_includeRight R ι'' ι ι') y
      rw [RingHom.comp_apply] at this
      exact this
    rw [s1]
    have hAB : ((tPrimeRing R ι ι' ι'').comp ((tPrimeRing R ι' ι'' ι).comp
        (tPrimeLegLeft R ι'' ι ι')))
        = (Algebra.TensorProduct.includeRight (R := ChartRing R ι)
          (A := Localization.Away (Transition.det (R := R) ι ι'))
          (B := Localization.Away (Transition.det (R := R) ι ι''))).toRingHom := by
      refine IsLocalization.ringHom_ext
        (Submonoid.powers (Transition.det (R := R) ι ι'')) (RingHom.ext fun q => ?_)
      simp only [RingHom.comp_apply]
      have s2 : tPrimeLegLeft R ι'' ι ι' (algebraMap (ChartRing R ι)
          (Localization.Away (Transition.det (R := R) ι ι'')) q)
          = Algebra.TensorProduct.includeLeftRingHom
              (Transition.ringHomAway (R := R) ι'' ι
                (algebraMap (ChartRing R ι)
                  (Localization.Away (Transition.det (R := R) ι ι'')) q)) := by
        have := RingHom.congr_fun (tPrimeLegLeft_eq R ι'' ι ι')
          (algebraMap (ChartRing R ι)
            (Localization.Away (Transition.det (R := R) ι ι'')) q)
        rw [RingHom.comp_apply] at this
        exact this
      rw [s2, Transition.ringHomAway_algebraMap]
      have s3 : tPrimeRing R ι' ι'' ι
          ((Algebra.TensorProduct.includeLeftRingHom :
            Localization.Away (Transition.det (R := R) ι'' ι) →+*
              doubleRing R ι'' ι ι')
            (Transition.ringHom (R := R) ι'' ι q))
          = tPrimeLegRight R ι' ι'' ι (Transition.ringHom (R := R) ι'' ι q) := by
        have := RingHom.congr_fun (tPrimeRing_comp_includeLeft R ι' ι'' ι)
          (Transition.ringHom (R := R) ι'' ι q)
        rw [RingHom.comp_apply] at this
        exact this
      rw [s3]
      have s4 := RingHom.congr_fun hcore q
      simp only [RingHom.comp_apply] at s4
      rw [s4]
      have s5 := RingHom.congr_fun
        (includeLeft_algebraMap_eq_includeRight_algebraMap R ι ι' ι'') q
      simp only [RingHom.comp_apply] at s5
      exact s5
    have := RingHom.congr_fun hAB y
    simp only [RingHom.comp_apply] at this
    exact this

set_option backward.isDefEq.respectTransparency false in
/-- The Spec-level cocycle: the triple `tPrimeScheme` composite telescopes to the
identity through `Spec.map`-functoriality over the ring cocycle. -/
lemma tPrimeScheme_cocycle :
    tPrimeScheme R ι ι' ι'' ≫ tPrimeScheme R ι' ι'' ι ≫ tPrimeScheme R ι'' ι ι'
      = 𝟙 (pullback (overlapι R ι ι') (overlapι R ι ι'')) := by
  rw [tPrimeScheme, tPrimeScheme, tPrimeScheme]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  rw [show ((tPrimeRing R ι ι' ι'').comp (tPrimeRing R ι' ι'' ι)).comp
        (tPrimeRing R ι'' ι ι')
      = RingHom.id (doubleRing R ι ι' ι'') from by
    rw [RingHom.comp_assoc]
    exact tPrimeRing_cocycle R ι ι' ι'']
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Iso.hom_inv_id]

end TPrime

/-- The self-overlap immersion is an isomorphism: the self-transition determinant is
`1`, so the localization is trivial. -/
instance overlapι_self_isIso (ι : Fin k ↪ Fin n) : IsIso (overlapι R ι ι) := by
  have hu : IsUnit (Transition.det (R := R) ι ι) := by
    rw [Transition.det_self]
    exact isUnit_one
  have he := IsLocalization.atUnit (ChartRing R ι)
    (S := Localization.Away (Transition.det (R := R) ι ι))
    (Transition.det (R := R) ι ι) hu
  have hfun : ⇑(algebraMap (ChartRing R ι)
      (Localization.Away (Transition.det (R := R) ι ι))) = ⇑he := by
    funext q
    exact (he.commutes q).symm
  have hbij : Function.Bijective (algebraMap (ChartRing R ι)
      (Localization.Away (Transition.det (R := R) ι ι))) := by
    rw [hfun]
    exact he.bijective
  have : IsIso (CommRingCat.ofHom (algebraMap (ChartRing R ι)
      (Localization.Away (Transition.det (R := R) ι ι)))) :=
    (RingEquiv.toCommRingCatIso (RingEquiv.ofBijective _ hbij)).isIso_hom
  have hspec : IsIso (Spec.map (CommRingCat.ofHom (algebraMap (ChartRing R ι)
      (Localization.Away (Transition.det (R := R) ι ι))))) := inferInstance
  exact hspec

/-- **[GR-F] The Grassmannian chart-atlas glue data**: the affine charts
`Spec R[X_{j,i}]` glued along the transition maps over the determinant opens — every
condition proven from the transition ring layer. -/
noncomputable def glueData (R : Type u) [CommRing R] (k n : ℕ) : Scheme.GlueData.{u} where
  J := ULift.{u} (Fin k ↪ Fin n)
  U ι := chartScheme R ι.down
  V p := overlapScheme R p.1.down p.2.down
  f ι ι' := overlapι R ι.down ι'.down
  f_mono _ _ := inferInstance
  f_id _ := inferInstance
  t ι ι' := overlapTransition R ι.down ι'.down
  t_id ι := overlapTransition_self R ι.down
  t' ι ι' ι'' := tPrimeScheme R ι.down ι'.down ι''.down
  t_fac ι ι' ι'' := tPrimeScheme_fac R ι.down ι'.down ι''.down
  cocycle ι ι' ι'' := tPrimeScheme_cocycle R ι.down ι'.down ι''.down
  f_open ι ι' := inferInstance

/-- **[GR-F] The Grassmannian scheme** `Grass(k, R^n)`: the glued chart atlas. -/
noncomputable def grassmannianScheme (R : Type u) [CommRing R] (k n : ℕ) : Scheme.{u} :=
  (glueData R k n).glued

section Points

open MvPolynomial

variable {R} {A : Type u} [CommRing A] [Algebra R A] {n : ℕ}

/-- Evaluation of the ι-chart coordinate ring (with `R`-coefficients) at a chart member
over an `R`-algebra `A`. -/
noncomputable def evalAtR (ι : Fin k ↪ Fin n) (N : G(k, (Fin n → A); A))
    (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N) :
    ChartRing R ι →+* A :=
  eval₂Hom (algebraMap R A) (fun p => chartMatrix n ι N h p.1 p.2)

/-- **[GR-G], point construction**: a chart member over `A` gives an `A`-point of the
Grassmannian scheme, through its chart. -/
noncomputable def pointOfChartMember (ι : Fin k ↪ Fin n) (N : G(k, (Fin n → A); A))
    (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N) :
    Spec (CommRingCat.of A) ⟶ grassmannianScheme R k n :=
  Spec.map (CommRingCat.ofHom (evalAtR ι N h)) ≫ (glueData R k n).ι (ULift.up ι)

end Points

end Module.Grassmannian

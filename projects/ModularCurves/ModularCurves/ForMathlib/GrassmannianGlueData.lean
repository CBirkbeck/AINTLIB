/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.GrassmannianTransition
import ModularCurves.ForMathlib.GrassmannianChart
import ModularCurves.ForMathlib.GrassmannianOverlap
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

/-- The ι-chart of `Grass(k, R^n)` as an affine scheme: `Spec R[X_{j,i}]`. Reducible so that
`chartScheme R ι` and `Spec (of (ChartRing R ι))` are interchangeable for the point-atlas
morphism algebra. -/
noncomputable abbrev chartScheme (ι : Fin k ↪ Fin n) : Scheme.{u} :=
  Spec (CommRingCat.of (ChartRing R ι))

/-- The (ι,ι')-overlap: the basic open `D(det ι ι')` of the ι-chart, as the Spec of the
localization. Reducible (see `chartScheme`). -/
noncomputable abbrev overlapScheme (ι ι' : Fin k ↪ Fin n) : Scheme.{u} :=
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

open MvPolynomial Matrix
open scoped TensorProduct

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

/-! ### [GR-G-ASM] The R-coefficient evaluation SPEC (coefficient-change naturality)

The point construction evaluates the `R`-coefficient chart ring `ChartRing R ι` at a chart
member over `A`. Chart-independence of the resulting glued point (the heart of the T-point
equivalence) needs the `R`-coefficient transition `Transition.ringHom (R := R)` — the actual
`glueData` datum — to intertwine the two chart evaluations. Everything transfers from the
already-proven `A`-coefficient SPEC (`evalAwayAt_comp_ringHom`, `GrassmannianOverlap.lean`)
through the base-change `MvPolynomial.map (algebraMap R A) : ChartRing R ι →+* ChartRing A ι`,
because `column`/`matrix`/`det`/`ringHom` are all `map`-stable and `evalAtR` factors as the
`A`-coefficient `evalAt` after this base change (`eval₂_map` naturality). -/

/-- `evalAtR` (evaluation of the `R`-coefficient chart ring at an `A`-member) factors as
base change to `A`-coefficients followed by the `A`-coefficient evaluation `evalAt`. This is
the `MvPolynomial.eval₂_map` naturality that carries the whole `A`-coefficient SPEC down to
`R`-coefficients. -/
theorem evalAtR_eq_comp_map (ι : Fin k ↪ Fin n) (N : G(k, (Fin n → A); A))
    (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N) :
    evalAtR ι N h = (evalAt ι N h).comp (MvPolynomial.map (algebraMap R A)) := by
  refine RingHom.ext fun p => ?_
  show evalAtR ι N h p = (evalAt ι N h) (MvPolynomial.map (algebraMap R A) p)
  simp only [evalAtR, evalAt, MvPolynomial.coe_eval₂Hom]
  rw [MvPolynomial.eval₂_map, RingHom.id_comp]

/-- The generic ι-column is stable under coefficient base change: the `R`-column maps to the
`A`-column. -/
theorem column_map (ι : Fin k ↪ Fin n) (j : Fin n) :
    (fun i => MvPolynomial.map (algebraMap R A) (Transition.column ι j i))
      = Transition.column (R := A) ι j := by
  classical
  funext i
  by_cases hj : j ∈ Set.range ι
  · obtain ⟨i₀, rfl⟩ := hj
    rw [congrFun (Transition.column_mem (R := R) ι i₀) i,
      congrFun (Transition.column_mem (R := A) ι i₀) i, Pi.single_apply, Pi.single_apply,
      apply_ite (MvPolynomial.map (algebraMap R A)), map_one, map_zero]
  · rw [congrFun (Transition.column_notMem (R := R) ι hj) i,
      congrFun (Transition.column_notMem (R := A) ι hj) i, MvPolynomial.map_X]

/-- `evalAtR` on the `R`-column equals `evalAt` on the `A`-column — the bridge that carries
`evalAt_column`/`evalAt_matrix` to `R`-coefficients. -/
theorem evalAtR_column (ι : Fin k ↪ Fin n) (N : G(k, (Fin n → A); A))
    (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N) (j : Fin n) (i : Fin k) :
    evalAtR (R := R) ι N h (Transition.column (R := R) ι j i)
      = evalAt ι N h (Transition.column (R := A) ι j i) := by
  rw [evalAtR_eq_comp_map, RingHom.comp_apply]
  exact congrArg (evalAt ι N h) (congrFun (column_map (R := R) (A := A) ι j) i)

/-- The generic transition matrix is stable under coefficient base change. -/
theorem matrix_map (ι ι' : Fin k ↪ Fin n) :
    (Transition.matrix (R := R) ι ι').map (MvPolynomial.map (algebraMap R A))
      = Transition.matrix (R := A) ι ι' := by
  funext i₁ i₂
  rw [Matrix.map_apply, Transition.matrix_apply, Transition.matrix_apply]
  exact congrFun (column_map (R := R) (A := A) ι (ι' i₂)) i₁

/-- The transition determinant is stable under coefficient base change: `det R` maps to
`det A`. -/
theorem det_map (ι ι' : Fin k ↪ Fin n) :
    MvPolynomial.map (algebraMap R A) (Transition.det (R := R) ι ι')
      = Transition.det (R := A) ι ι' := by
  rw [Transition.det, Transition.det, RingHom.map_det, RingHom.mapMatrix_apply, matrix_map]

variable (ι ι' : Fin k ↪ Fin n) (N : G(k, (Fin n → A); A))

/-- `evalAtR` on the `R`-transition determinant equals `evalAt` on the `A`-transition
determinant (base-change factorization + `det_map`). -/
theorem evalAtR_det (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N) :
    evalAtR (R := R) ι N h (Transition.det (R := R) ι ι')
      = evalAt ι N h (Transition.det (R := A) ι ι') := by
  rw [evalAtR_eq_comp_map, RingHom.comp_apply, det_map]

/-- The `R`-transition determinant evaluates to a unit at a chart member charted at both
`ι` and `ι'`. -/
theorem isUnit_evalAtR_det (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N)
    (hι' : IsChartAt (fun i => Pi.single (ι' i) (1 : A)) N) :
    IsUnit (evalAtR (R := R) ι N h (Transition.det (R := R) ι ι')) := by
  rw [evalAtR_det]
  exact isUnit_evalAt_det ι ι' N h hι'

/-- **[GR-G-ASM]** The `R`-coefficient evaluation extended over the overlap localization —
the `R`-coefficient counterpart of `evalAwayAt`. -/
noncomputable def evalAwayAtR (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N)
    (hι' : IsChartAt (fun i => Pi.single (ι' i) (1 : A)) N) :
    Localization.Away (Transition.det (R := R) ι ι') →+* A :=
  IsLocalization.Away.lift (Transition.det (R := R) ι ι') (isUnit_evalAtR_det ι ι' N h hι')

/-- `evalAwayAtR` restricts to `evalAtR` on the chart ring. -/
theorem evalAwayAtR_algebraMap (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N)
    (hι' : IsChartAt (fun i => Pi.single (ι' i) (1 : A)) N) (q : ChartRing R ι) :
    evalAwayAtR ι ι' N h hι'
        (algebraMap (ChartRing R ι) (Localization.Away (Transition.det (R := R) ι ι')) q)
      = evalAtR (R := R) ι N h q :=
  IsLocalization.Away.lift_eq _ (isUnit_evalAtR_det ι ι' N h hι') q

/-- `evalAtR` carries the generic transition matrix to the pointwise one — the
`R`-coefficient counterpart of `evalAt_matrix`. -/
theorem evalAtR_matrix (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N)
    (h' : Function.Bijective
      ⇑(N.toSubmodule.mkQ ∘ₗ coordMap (fun i => Pi.single (ι i) (1 : A)))) :
    (Transition.matrix (R := R) ι ι').map ⇑(evalAtR (R := R) ι N h)
      = transitionMatrixAt ι ι' N h := by
  funext i₁ i₂
  rw [Matrix.map_apply, Transition.matrix_apply, evalAtR_column]
  exact congrFun (congrFun (evalAt_matrix ι ι' N h h') i₁) i₂

/-- **[GR-G-ASM], the R-coefficient SPEC.** Extending the `R`-coefficient ι-evaluation over
the overlap and precomposing with the *generic* (`R`-coefficient) transition map — the
actual `glueData` transition datum — recovers the `R`-coefficient ι'-evaluation. The
`R`-coefficient counterpart of `evalAwayAt_comp_ringHom`; the algebraic heart of chart-
independence of `pointOfChartMember`. Proof mirrors the `A`-coefficient SPEC with the
base-changed infrastructure (`evalAwayAtR_algebraMap`, `evalAtR_matrix`). -/
theorem evalAwayAtR_comp_ringHom (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N)
    (hι' : IsChartAt (fun i => Pi.single (ι' i) (1 : A)) N) :
    (evalAwayAtR ι ι' N h hι').comp (Transition.ringHom (R := R) ι ι')
      = evalAtR (R := R) ι' N hι' := by
  classical
  have h'ι : Function.Bijective
      ⇑(N.toSubmodule.mkQ ∘ₗ coordMap (fun i => Pi.single (ι i) (1 : A))) := h
  have h'ι' : Function.Bijective
      ⇑(N.toSubmodule.mkQ ∘ₗ coordMap (fun i => Pi.single (ι' i) (1 : A))) := hι'
  set T := transitionMatrixAt ι ι' N h with hT
  have hdetT : IsUnit T.det := (isChartAt_iff_isUnit_det ι ι' N h).mp hι'
  -- the extended R-evaluation carries the localized R-transition matrix to `T`
  have hMap : (Transition.matrixAway (R := R) ι ι').map ⇑(evalAwayAtR ι ι' N h hι') = T := by
    funext i₁ i₂
    simp only [Transition.matrixAway, Matrix.map_apply]
    rw [evalAwayAtR_algebraMap]
    exact congrFun (congrFun (evalAtR_matrix ι ι' N h h'ι) i₁) i₂
  apply MvPolynomial.ringHom_ext
  · intro a
    rw [RingHom.comp_apply, Transition.ringHom, eval₂Hom_C, RingHom.comp_apply,
      evalAwayAtR_algebraMap]
    rw [evalAtR, eval₂Hom_C, evalAtR, eval₂Hom_C]
  · intro p
    obtain ⟨⟨j', hj'⟩, i'⟩ := p
    rw [RingHom.comp_apply, Transition.ringHom, eval₂Hom_X']
    set u : Fin k → Localization.Away (Transition.det (R := R) ι ι') :=
      (Transition.matrixAway (R := R) ι ι')⁻¹ *ᵥ
        (fun i₁ => algebraMap (ChartRing R ι) _ (Transition.column ι j' i₁)) with hu
    -- the evaluated solution solves `T *ᵥ ? = (ι-retraction of the j'-column)`
    have hTu : T *ᵥ (⇑(evalAwayAtR ι ι' N h hι') ∘ u)
        = fun i₁ => evalAt ι N h (Transition.column (R := A) ι j' i₁) := by
      funext i₁
      rw [← hMap, ← RingHom.map_mulVec, hu]
      rw [show (Transition.matrixAway (R := R) ι ι') *ᵥ
          ((Transition.matrixAway (R := R) ι ι')⁻¹ *ᵥ
            (fun i₁ => algebraMap (ChartRing R ι) _ (Transition.column ι j' i₁)))
          = fun i₁ => algebraMap (ChartRing R ι) _ (Transition.column ι j' i₁) by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
          (Transition.isUnit_det_matrixAway ι ι'), Matrix.one_mulVec]]
      show evalAwayAtR ι ι' N h hι'
          (algebraMap (ChartRing R ι) _ (Transition.column ι j' i₁))
        = evalAt ι N h (Transition.column (R := A) ι j' i₁)
      rw [evalAwayAtR_algebraMap, evalAtR_column]
    -- the ι'-chart matrix solves the same equation
    have hTw : T *ᵥ chartMatrix n ι' N hι' ⟨j', hj'⟩
        = fun i₁ => evalAt ι N h (Transition.column (R := A) ι j' i₁) := by
      rw [hT, transitionMatrixAt_mulVec ι ι' N h h'ι]
      have hmk : N.toSubmodule.mkQ
          (coordMap (fun i => Pi.single (ι' i) (1 : A))
            (chartMatrix n ι' N hι' ⟨j', hj'⟩))
          = N.toSubmodule.mkQ (Pi.single j' 1) := by
        show (N.toSubmodule.mkQ ∘ₗ coordMap (fun i => Pi.single (ι' i) (1 : A)))
          (chartMatrix n ι' N hι' ⟨j', hj'⟩) = _
        rw [show chartMatrix n ι' N hι' ⟨j', hj'⟩
            = (LinearEquiv.ofBijective _ h'ι').symm
              (N.toSubmodule.mkQ (Pi.single j' 1)) from rfl]
        exact (LinearEquiv.ofBijective _ h'ι').apply_symm_apply _
      rw [hmk]
      exact (evalAt_column ι N h h'ι j').symm
    -- cancel the invertible matrix
    have hcancel : ⇑(evalAwayAtR ι ι' N h hι') ∘ u
        = chartMatrix n ι' N hι' ⟨j', hj'⟩ := by
      have hEq := hTu.trans hTw.symm
      have := congrArg (fun v => T⁻¹ *ᵥ v) hEq
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdetT,
        Matrix.one_mulVec] using this
    have hfin := congrFun hcancel i'
    rw [Function.comp_apply] at hfin
    rw [hfin, evalAtR, eval₂Hom_X']

/-- The localized-transition composite of the two chart evaluations: precomposing the
ι-evaluation with the localized transition `ringHomAway ι ι'` recovers the ι'-evaluation
over the reverse overlap. Lift-uniqueness reduces this to the SPEC. -/
theorem evalAwayAtR_comp_ringHomAway (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N)
    (hι' : IsChartAt (fun i => Pi.single (ι' i) (1 : A)) N) :
    (evalAwayAtR ι ι' N h hι').comp (Transition.ringHomAway (R := R) ι ι')
      = evalAwayAtR ι' ι N hι' h := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (Transition.det (R := R) ι' ι))
    (RingHom.ext fun q => ?_)
  show evalAwayAtR ι ι' N h hι' (Transition.ringHomAway (R := R) ι ι'
      (algebraMap (ChartRing R ι') (Localization.Away (Transition.det (R := R) ι' ι)) q))
    = evalAwayAtR ι' ι N hι' h
      (algebraMap (ChartRing R ι') (Localization.Away (Transition.det (R := R) ι' ι)) q)
  rw [Transition.ringHomAway_algebraMap, evalAwayAtR_algebraMap]
  exact RingHom.congr_fun (evalAwayAtR_comp_ringHom ι ι' N h hι') q

/-- The evaluation `A`-point of the ι-chart, extended over the (ι,ι')-overlap: an
`A`-point of the overlap scheme `overlapScheme R ι ι'`. -/
noncomputable def pointOverlap (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N)
    (hι' : IsChartAt (fun i => Pi.single (ι' i) (1 : A)) N) :
    Spec (CommRingCat.of A) ⟶ overlapScheme R ι ι' :=
  Spec.map (CommRingCat.ofHom (evalAwayAtR ι ι' N h hι'))

/-- The evaluation `A`-point of the ι-chart factors through the (ι,ι')-overlap open
immersion: `evalAtR ι` sends `det ι ι'` to a unit, so it extends over the localization. -/
theorem specEvalAtR_eq_overlapι (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N)
    (hι' : IsChartAt (fun i => Pi.single (ι' i) (1 : A)) N) :
    Spec.map (CommRingCat.ofHom (evalAtR (R := R) ι N h))
      = pointOverlap (R := R) ι ι' N h hι' ≫ overlapι R ι ι' := by
  have he : CommRingCat.ofHom (evalAtR (R := R) ι N h)
      = CommRingCat.ofHom (algebraMap (ChartRing R ι)
          (Localization.Away (Transition.det (R := R) ι ι')))
        ≫ CommRingCat.ofHom (evalAwayAtR ι ι' N h hι') := by
    rw [← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom
      (RingHom.ext (evalAwayAtR_algebraMap ι ι' N h hι')).symm
  rw [he, Spec.map_comp]
  rfl

/-- The overlap point transported by the glue transition is the reverse-chart overlap
point (the scheme-level shadow of `evalAwayAtR_comp_ringHomAway`). -/
@[reassoc]
theorem pointOverlap_comp_overlapTransition
    (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N)
    (hι' : IsChartAt (fun i => Pi.single (ι' i) (1 : A)) N) :
    pointOverlap (R := R) ι ι' N h hι' ≫ overlapTransition R ι ι'
      = pointOverlap (R := R) ι' ι N hι' h := by
  have key : CommRingCat.ofHom (Transition.ringHomAway (R := R) ι ι')
        ≫ CommRingCat.ofHom (evalAwayAtR ι ι' N h hι')
      = CommRingCat.ofHom (evalAwayAtR ι' ι N hι' h) := by
    rw [← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom (evalAwayAtR_comp_ringHomAway ι ι' N h hι')
  show Spec.map (CommRingCat.ofHom (evalAwayAtR ι ι' N h hι'))
      ≫ Spec.map (CommRingCat.ofHom (Transition.ringHomAway (R := R) ι ι'))
    = Spec.map (CommRingCat.ofHom (evalAwayAtR ι' ι N hι' h))
  rw [← Spec.map_comp, key]

/-- **[GR-G-ASM], chart-independence of the point construction.** A member charted at both
`ι` and `ι'` gives the same `A`-point of the Grassmannian scheme through either chart —
the well-definedness heart of the T-point map. The two chart evaluations are intertwined
by the glue transition (`evalAwayAtR_comp_ringHomAway`, itself the SPEC), and the two glued
inclusions agree on the overlap by `GlueData.glue_condition`. -/
theorem pointOfChartMember_eq (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N)
    (hι' : IsChartAt (fun i => Pi.single (ι' i) (1 : A)) N) :
    pointOfChartMember (R := R) ι N h = pointOfChartMember (R := R) ι' N hι' := by
  have hgc : overlapTransition R ι ι' ≫ overlapι R ι' ι ≫ (glueData R k n).ι (ULift.up ι')
      = overlapι R ι ι' ≫ (glueData R k n).ι (ULift.up ι) :=
    (glueData R k n).glue_condition (ULift.up ι) (ULift.up ι')
  rw [pointOfChartMember, pointOfChartMember,
    specEvalAtR_eq_overlapι ι ι' N h hι', specEvalAtR_eq_overlapι ι' ι N hι' h]
  simp only [Category.assoc]
  erw [← hgc]
  erw [pointOverlap_comp_overlapTransition_assoc]
  rfl

/-! ### [GR-G-ASM] inverse-direction foundation: the chart covering as a spanning family -/

/-- **[GR-G-ASM], the covering.** For any member `N` over `A`, the chart-witnessing elements
`f_p` (one per prime `p`, from `exists_isChartAt_congr_localizationAway`) span the unit ideal
— so the basic opens `D(f_p)` cover `Spec A`, and on each the localized-and-`piScalarRight`-
normalized member is charted at `ι_p` in the exact `Pi.single`-tuple form that
`pointOfChartMember` consumes. This is the spanning family + per-piece chart data feeding
`affineOpenCoverOfSpanRangeEqTop` for the prime-indexed `Scheme.OpenCover` of `Spec A` and its
`glueMorphisms` assembly (recipe steps 2-4). -/
theorem exists_spanning_chart_witnesses (N : G(k, A ⊗[R] (Fin n → R); A)) :
    ∃ (s : PrimeSpectrum A → A), Ideal.span (Set.range s) = ⊤ ∧
      ∀ p : PrimeSpectrum A, ∃ (ι : Fin k ↪ Fin n), s p ∉ p.asIdeal ∧
        IsChartAt (fun i => Pi.single (ι i) (1 : Localization.Away (s p)))
          (Module.Grassmannian.congr
            (TensorProduct.piScalarRight R (Localization.Away (s p))
              (Localization.Away (s p)) (Fin n))
            (N.map (IsScalarTower.toAlgHom R A (Localization.Away (s p))))) := by
  classical
  choose ι fw hfw hchart using
    fun p : PrimeSpectrum A => exists_isChartAt_congr_localizationAway n N p.asIdeal
  refine ⟨fw, ?_, fun p => ⟨ι p, hfw p, hchart p⟩⟩
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  exact hfw ⟨M, hM.isPrime⟩ (hle (Ideal.subset_span ⟨⟨M, hM.isPrime⟩, rfl⟩))

/-- **[GR-G-ASM], functoriality of the point construction.** The `A`-point of a globally-
charted member, transported by a base-change `g : A →ₐ[R] B`, is the `B`-point of the pushed
member `normMap g N` — the naturality that discharges the `glueMorphisms` compatibility
obligation on overlaps. Reduces to `chartMatrix_normMap` (entrywise chart-matrix naturality)
through `comp_eval₂Hom`. -/
theorem pointOfChartMember_naturality {B : Type u} [CommRing B] [Algebra R B]
    (ι : Fin k ↪ Fin n) (N : G(k, (Fin n → A); A)) (g : A →ₐ[R] B)
    (h : IsChartAt (fun i => Pi.single (ι i) (1 : A)) N) :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ pointOfChartMember (R := R) ι N h
      = pointOfChartMember (R := R) ι (normMap n g N) (isChartAt_normMap n ι g N h) := by
  have hring : (g.toRingHom).comp (evalAtR (R := R) ι N h)
      = evalAtR (R := R) ι (normMap n g N) (isChartAt_normMap n ι g N h) := by
    rw [evalAtR, evalAtR, comp_eval₂Hom]
    congr 1
    · exact g.comp_algebraMap
    · funext p
      exact (congrFun (congrFun (chartMatrix_normMap n ι g N h) p.1) p.2).symm
  rw [pointOfChartMember, pointOfChartMember, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, hring]

/-- `normMap g` of a covering member `congr piScalarRight (N.map a)` is again a covering
member, for the composite structure map `g ∘ a`. -/
theorem normMap_covering_member {S T : Type u} [CommRing S] [Algebra R S] [CommRing T]
    [Algebra R T] (a : A →ₐ[R] S) (g : S →ₐ[R] T)
    (N : G(k, A ⊗[R] (Fin n → R); A)) :
    normMap n g (Module.Grassmannian.congr (TensorProduct.piScalarRight R S S (Fin n))
        (N.map a))
      = Module.Grassmannian.congr (TensorProduct.piScalarRight R T T (Fin n))
        (N.map (g.comp a)) := by
  rw [normMap, congr_symm_congr, Module.Grassmannian.map_comp]

/-- **[GR-G-ASM], the member-agreement heart of the `glueMorphisms` compat.** Two covering
members `congr piScalarRight (N.map a)` and `congr piScalarRight (N.map b)`, pushed by
`g : S →ₐ D` and `g' : T →ₐ D` whose composites with the structure maps agree
(`g ∘ a = g' ∘ b` — the double-localization tensor structure), become the *same* member over
`D`. Feeds chart-independence to close the compat. -/
theorem normMap_covering_member_eq {S T D : Type u} [CommRing S] [Algebra R S] [CommRing T]
    [Algebra R T] [CommRing D] [Algebra R D] (a : A →ₐ[R] S) (b : A →ₐ[R] T)
    (g : S →ₐ[R] D) (g' : T →ₐ[R] D) (hcompat : g.comp a = g'.comp b)
    (N : G(k, A ⊗[R] (Fin n → R); A)) :
    normMap n g (Module.Grassmannian.congr (TensorProduct.piScalarRight R S S (Fin n))
        (N.map a))
      = normMap n g' (Module.Grassmannian.congr (TensorProduct.piScalarRight R T T (Fin n))
        (N.map b)) := by
  rw [normMap_covering_member, normMap_covering_member, hcompat]

/-- **[GR-G-ASM], the T-point forward map.** Every member `N ∈ G(k, A^n; A)` (in the
`A ⊗[R] R^n` presentation) gives an `A`-point of `grassmannianScheme R k n`, glued from the
per-chart points `pointOfChartMember` over the covering `D(f_p)` (`exists_spanning_chart_
witnesses`) via `OpenCover.glueMorphisms`. The overlap compatibility is discharged by
`pullbackSpecIso` (identifying the pullback fst/snd with the localization inclusions),
`pointOfChartMember_naturality`, `normMap_covering_member_eq` (the two localized members agree
over the double localization), and `pointOfChartMember_eq` (chart-independence). -/
noncomputable def pointOfMember (N : G(k, A ⊗[R] (Fin n → R); A)) :
    Spec (CommRingCat.of A) ⟶ grassmannianScheme R k n := by
  classical
  set s := (exists_spanning_chart_witnesses N).choose with hs_def
  have hspan : Ideal.span (Set.range s) = ⊤ := (exists_spanning_chart_witnesses N).choose_spec.1
  have hdata := (exists_spanning_chart_witnesses N).choose_spec.2
  choose ιc hs hchart using hdata
  refine (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of A) s hspan).openCover.glueMorphisms
      (fun p => pointOfChartMember (R := R) (ιc p) _ (hchart p)) ?_
  intro p q
  show pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (s p)))))
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (s q)))))
      ≫ pointOfChartMember (R := R) (ιc p) _ (hchart p)
    = pullback.snd _ _ ≫ pointOfChartMember (R := R) (ιc q) _ (hchart q)
  set S := Localization.Away (s p)
  set T := Localization.Away (s q)
  -- the two localization inclusions, as R-algebra homs into the double localization
  set iL : S →ₐ[R] TensorProduct A S T :=
    (Algebra.TensorProduct.includeLeft : S →ₐ[A] TensorProduct A S T).restrictScalars R with hiL
  set iR : T →ₐ[R] TensorProduct A S T :=
    (Algebra.TensorProduct.includeRight : T →ₐ[A] TensorProduct A S T).restrictScalars R with hiR
  -- cancel the pullbackSpecIso and reduce fst/snd to those inclusions
  rw [← cancel_epi (pullbackSpecIso A S T).inv, pullbackSpecIso_inv_fst_assoc,
    pullbackSpecIso_inv_snd_assoc]
  -- naturality: transport the two chart points to the double localization
  erw [pointOfChartMember_naturality (ιc p) _ iL (hchart p),
    pointOfChartMember_naturality (ιc q) _ iR (hchart q)]
  -- the structure composites agree: both are the `A → S ⊗[A] T` map
  have hcompat : iL.comp (IsScalarTower.toAlgHom R A S)
      = iR.comp (IsScalarTower.toAlgHom R A T) := by
    ext a
    show iL (algebraMap A S a) = iR (algebraMap A T a)
    rw [hiL, hiR, AlgHom.restrictScalars_apply, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  -- the two members agree over the double localization
  have hM := normMap_covering_member_eq (IsScalarTower.toAlgHom R A S)
    (IsScalarTower.toAlgHom R A T) iL iR hcompat N
  -- chart-independence on the common member (witnesses are `Prop`s, so proof-irrelevant)
  refine (pointOfChartMember_eq (ιc p) (ιc q) (normMap n iL
      (Module.Grassmannian.congr (TensorProduct.piScalarRight R S S (Fin n))
        (N.map (IsScalarTower.toAlgHom R A S))))
    (isChartAt_normMap n (ιc p) iL _ (hchart p))
    (hM ▸ isChartAt_normMap n (ιc q) iR _ (hchart q))).trans ?_
  congr 1

/-- **[GR-G-ASM], round-trip seed.** The point of the *universal* chart member is the chart
inclusion itself: `evalAtR` of the universal member is the identity (its chart matrix is the
generic variable matrix), so `Spec.map` of it is `𝟙`. This is the fixed point that makes
`pointOfMember`/inverse a genuine round trip on each chart. -/
theorem pointOfChartMember_universalChartMember (ι : Fin k ↪ Fin n) :
    pointOfChartMember (R := R) ι (universalChartMember R n ι).1
        (universalChartMember R n ι).2
      = (glueData R k n).ι (ULift.up ι) := by
  have hid : evalAtR (R := R) ι (universalChartMember R n ι).1
      (universalChartMember R n ι).2 = RingHom.id (ChartRing R ι) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun p => ?_)
    · rw [evalAtR, eval₂Hom_C, RingHom.id_apply]; rfl
    · rw [evalAtR, eval₂Hom_X', RingHom.id_apply,
        chartMatrix_universalChartMember (R := R) n ι]
  rw [pointOfChartMember, hid, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

/-- **[GR-G-ASM], the chart-local round-trip.** A chart-ring point `φ : ChartRing R ι → A'`
(i.e. an `A'`-point of the ι-chart) recovers the member `normMap φ (universal)`, whose
`pointOfMember`-style point is `φ` composed with the chart inclusion. Together with
`pointOfChartMember_universalChartMember` this exhibits `pointOfChartMember` as inverse to the
chart projection on each chart — the local half of the T-point equivalence's inverse. -/
theorem pointOfChartMember_normMap_universal {A' : Type u} [CommRing A'] [Algebra R A']
    (ι : Fin k ↪ Fin n) (φ : ChartRing R ι →ₐ[R] A') :
    pointOfChartMember (R := R) ι (normMap n φ (universalChartMember R n ι).1)
        (isChartAt_normMap n ι φ (universalChartMember R n ι).1
          (universalChartMember R n ι).2)
      = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (glueData R k n).ι (ULift.up ι) := by
  rw [← pointOfChartMember_naturality ι (universalChartMember R n ι).1 φ
      (universalChartMember R n ι).2]
  congr 1
  exact pointOfChartMember_universalChartMember (R := R) ι

end Points

end Module.Grassmannian

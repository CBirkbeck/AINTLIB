import ModularCurves.ForMathlib.GrassmannianTransition
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

open AlgebraicGeometry CategoryTheory

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

open TensorProduct

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

end TPrime

end Module.Grassmannian

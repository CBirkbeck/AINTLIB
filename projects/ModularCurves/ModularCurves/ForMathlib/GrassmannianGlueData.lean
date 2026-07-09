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

end Module.Grassmannian

import ModularCurves.EllipticCurve.GroupLawConstruction
import ModularCurves.EllipticCurve.WeierstrassAtlasBundle
import ModularCurves.EllipticCurve.GroupLaw
import ModularCurves.EllipticCurve.RecordGroupUnique
import ModularCurves.EllipticCurve.Comparison
import ModularCurves.EllipticCurve.ModelVCEquivariance

/-!
# Descent of the group law to every locally-Weierstrass family

**(T-W7 skeleton, join of lanes P0–P5 — `/develop --decompose` 2026-07-07.)** The group law
on an arbitrary geometric elliptic curve `G/S`: per chart of a bundled atlas, transport the
model group law (a base change of the universal one along the classifying map); overlap
agreement is the comparison theorem (`pointedIso_exists_variableChange` — the transition
between two pointed chart presentations is a variable change) composed with global
variable-change equivariance (`mulModelHom_vc`); glue. Each group axiom holds chart-locally
as a base change of the model identity (no flatness needed, no reducedness of `S` invoked),
hence globally by the cover extensionality. This yields the existence milestone **T-W7a**:
`abelEnrichment_exists`.

Sources: reviewer round 1 §3/§Q5 (existence by base change + atlas gluing, valid over
non-reduced `S`); audits A1/A6; `Scheme.Cover.glueMorphisms`/`hom_ext` (mathlib, verified).
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

variable {S : Scheme.{u}} (G : EllipticCurveGeom S)

/-! ## Base change of the geometric record -/

/-- **(helper)** Base change of a geometric elliptic curve `G/S` along `g : T ⟶ S`: the
total space is `E ×_S T`, structure morphism the second projection, zero section the lifted
zero. The geometry props are base-change stability; the local-model condition is
`LocallyWeierstrass.baseChange`. (The group-free companion of `EllipticCurve.baseChange`.) -/
noncomputable def EllipticCurveGeom.baseChange {T : Scheme.{u}} (g : T ⟶ S) :
    EllipticCurveGeom T where
  E := pullback G.π g
  π := pullback.snd G.π g
  zero := pullback.lift (g ≫ G.zero) (𝟙 T)
    (by rw [Category.assoc, G.zero_π, Category.comp_id, Category.id_comp])
  zero_π := pullback.lift_snd _ _ _
  smooth := by
    haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
      AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange 1
    exact MorphismProperty.pullback_snd _ _ G.smooth
  proper := MorphismProperty.pullback_snd _ _ G.proper
  localModel := G.localModel.baseChange g

@[simp] theorem EllipticCurveGeom.baseChange_π {T : Scheme.{u}} (g : T ⟶ S) :
    (G.baseChange g).π = pullback.snd G.π g := rfl

@[simp] theorem EllipticCurveGeom.baseChange_zero {T : Scheme.{u}} (g : T ⟶ S) :
    (G.baseChange g).zero = pullback.lift (g ≫ G.zero) (𝟙 T)
      (by rw [Category.assoc, G.zero_π, Category.comp_id, Category.id_comp]) := rfl

/-! ## The atlas cover of `E` and `E ×_S E` -/

section AtlasCover

variable {G} (A : WeierstrassAtlasData G)

/-- The open cover of the base `S` by the affine opens of a bundled atlas. -/
noncomputable def atlasBaseCover : S.OpenCover :=
  Scheme.Cover.mkOfCovers A.ι (fun i => (A.U i).1) (fun i => (A.U i).1.ι)
    (fun x => by obtain ⟨i, hi⟩ := A.covers x; exact ⟨i, ⟨x, hi⟩, rfl⟩)

@[simp] theorem atlasBaseCover_f (i : A.ι) : (atlasBaseCover A).f i = (A.U i).1.ι := rfl

/-- The open cover of the total space `E` by the atlas charts `pullback G.π (U i).ι`,
built directly (so the cover accessors `I₀`/`X`/`f` reduce to `A.ι` /
`pullback G.π (U i).ι` / `pullback.fst G.π (U i).ι` transparently — a `pullback₁` of the
base cover would leave `.I₀` un-reducible at `instances` transparency and poison `rw`). -/
noncomputable def atlasTotalCover : G.E.OpenCover :=
  Scheme.Cover.mkOfCovers A.ι (fun i => pullback G.π (A.U i).1.ι)
    (fun i => pullback.fst G.π (A.U i).1.ι)
    (fun x => by
      obtain ⟨i, hi⟩ := A.covers (G.π.base x)
      have hx : x ∈ Set.range (pullback.fst G.π (A.U i).1.ι).base := by
        rw [Scheme.Pullback.range_fst, Set.mem_preimage, Scheme.Opens.range_ι, SetLike.mem_coe]
        exact hi
      obtain ⟨y, hy⟩ := hx
      exact ⟨i, y, hy⟩)

@[simp] theorem atlasTotalCover_X (i : A.ι) :
    (atlasTotalCover A).X i = pullback G.π (A.U i).1.ι := rfl

@[simp] theorem atlasTotalCover_f (i : A.ι) :
    (atlasTotalCover A).f i = pullback.fst G.π (A.U i).1.ι := rfl

end AtlasCover

/-! ## Variable-change equivariance of the model negation -/

/-- **(T-W7.0h-neg)** Variable-change equivariance of the model negation: the model
isomorphism of a variable change intertwines the two model negations. Negation analogue of
`mulModelHom_vc`, but proven directly: `projModelVCIso C W` is a pointed isomorphism of the
T-G4 group objects (`vcOver_one` for the unit, `isMonHom_of_pointedIso_records` for the
multiplication), hence a monoid homomorphism, and a monoid homomorphism of group objects
respects the inverse (`GrpObj.inv_hom`). Taking underlying morphisms (`invOver_left`) gives
the negation equation. -/
theorem negModelHom_vc {R : Type u} [CommRing R] (C : WeierstrassCurve.VariableChange R)
    (W : WeierstrassCurve R) [W.IsElliptic] [(C • W).IsElliptic] :
    negModelHom (C • W) ≫ (projModelVCIso C W).hom =
      (projModelVCIso C W).hom ≫ negModelHom W := by
  let e : (modelEllipticCurve (C • W)).asOver ≅ (modelEllipticCurve W).asOver :=
    Over.isoMk (projModelVCIso C W) (projModelVCIso_π C W)
  have hη : (η[(modelEllipticCurve (C • W)).asOver] :
        𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ (modelEllipticCurve (C • W)).asOver) ≫ e.hom =
      η[(modelEllipticCurve W).asOver] :=
    vcOver_one C W
  haveI : IsMonHom e.hom :=
    { one_hom := hη
      mul_hom := isMonHom_of_pointedIso_records (modelEllipticCurve (C • W))
        (modelEllipticCurve W) e hη }
  have hinv := congrArg CommaMorphism.left (GrpObj.inv_hom e.hom)
  rw [Over.comp_left, Over.comp_left] at hinv
  exact hinv

/-! ## Negation, glued from the per-chart model negations -/

section Negation

variable {G} (A : WeierstrassAtlasData G)

/-- The per-chart negation piece: transport the model negation `negModelHom (W i)` through
the chart isomorphism `A.e i` and embed back into `E` via the chart's open immersion. Its
domain is the *clean* `pullback G.π (U i).ι` (defeq to `(atlasTotalCover A).X i`, but the
cover accessor is a semireducible `def` whose projections do not reduce at `instances`
transparency, which would poison every `rw`). -/
noncomputable def negPiece (i : A.ι) : pullback G.π (A.U i).1.ι ⟶ G.E :=
  haveI := A.elliptic i
  (A.e i).hom ≫ negModelHom (A.W i) ≫ (A.e i).inv ≫ pullback.fst G.π (A.U i).1.ι

/-- The per-chart negations agree on the overlaps of the atlas total cover: on the overlap
the two pointed chart presentations differ by a variable change, and `negModelHom` is
variable-change equivariant. -/
theorem negPiece_agree (i j : A.ι) :
    pullback.fst ((atlasTotalCover A).f i) ((atlasTotalCover A).f j) ≫ negPiece A i =
      pullback.snd ((atlasTotalCover A).f i) ((atlasTotalCover A).f j) ≫ negPiece A j :=
  sorry

/-- Negation glued from the per-chart model negations. -/
noncomputable def negHomOf : G.E ⟶ G.E :=
  (atlasTotalCover A).glueMorphisms (negPiece A) (negPiece_agree A)

@[reassoc]
theorem negHomOf_piece (i : A.ι) :
    (atlasTotalCover A).f i ≫ negHomOf A = negPiece A i :=
  (atlasTotalCover A).ι_glueMorphisms _ _ i

/-- Each negation piece is a morphism over `S`. -/
theorem negPiece_π (i : A.ι) :
    negPiece A i ≫ G.π = pullback.fst G.π (A.U i).1.ι ≫ G.π := by
  haveI := A.elliptic i
  have hcompat := A.compat_π i
  have hsnd : pullback.snd G.π (A.U i).1.ι ≫ (A.U i).1.ι =
      (A.e i).hom ≫ projModelπ (A.W i) ≫ (A.U i).2.isoSpec.inv ≫ (A.U i).1.ι := by
    have h := congrArg (· ≫ (A.U i).2.isoSpec.inv ≫ (A.U i).1.ι) hcompat
    simp only [Category.assoc, Iso.hom_inv_id_assoc] at h
    exact h.symm
  have hfst : pullback.fst G.π (A.U i).1.ι ≫ G.π =
      (A.e i).hom ≫ projModelπ (A.W i) ≫ (A.U i).2.isoSpec.inv ≫ (A.U i).1.ι :=
    pullback.condition.trans hsnd
  rw [negPiece]
  simp only [Category.assoc]
  rw [hfst, Iso.inv_hom_id_assoc, negModelHom_π_assoc]

/-- The lifted zero `E`-point of chart `i`: the section of `pullback G.π (U i).ι` over
`U i` given by the zero section. -/
noncomputable def zLift (i : A.ι) : (A.U i).1.toScheme ⟶ pullback G.π (A.U i).1.ι :=
  pullback.lift ((A.U i).1.ι ≫ G.zero) (𝟙 _)
    (by rw [Category.assoc, G.zero_π, Category.comp_id, Category.id_comp])

theorem zLift_fst (i : A.ι) :
    zLift A i ≫ pullback.fst G.π (A.U i).1.ι = (A.U i).1.ι ≫ G.zero :=
  pullback.lift_fst _ _ _

/-- The chart lift of the zero section transports (through `A.e i`) to the model zero
section (up to the affine-open `Spec` identification). -/
theorem zLift_totalIso (i : A.ι) :
    haveI := A.elliptic i
    zLift A i ≫ (A.e i).hom = (A.U i).2.isoSpec.hom ≫ projModelZero (A.W i) := by
  haveI := A.elliptic i
  have h : ((A.U i).2.isoSpec.inv ≫ zLift A i) ≫ (A.e i).hom = projModelZero (A.W i) :=
    A.compat_zero i
  rw [Category.assoc] at h
  rw [← h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- `pullback.fst ≫ negHom` is the negation piece (the clean-`pullback.fst` form of
`negHomOf_piece`). -/
theorem negHomOf_piece' (i : A.ι) :
    pullback.fst G.π (A.U i).1.ι ≫ negHomOf A = negPiece A i := by
  rw [← atlasTotalCover_f]; exact negHomOf_piece A i

/-- Negation fixes the chart lift of the zero section: `zLift ≫ neg = zLift ≫ fst`. -/
theorem zLift_negPiece (i : A.ι) :
    zLift A i ≫ negPiece A i = (A.U i).1.ι ≫ G.zero := by
  haveI := A.elliptic i
  have hzinv : projModelZero (A.W i) ≫ (A.e i).inv = (A.U i).2.isoSpec.inv ≫ zLift A i := by
    rw [← cancel_mono (A.e i).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, zLift_totalIso,
      Iso.inv_hom_id_assoc]
  rw [negPiece, ← Category.assoc, zLift_totalIso]
  simp only [Category.assoc]
  rw [← Category.assoc (projModelZero (A.W i)), negModelHom_zero,
    ← Category.assoc (projModelZero (A.W i)), hzinv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [zLift_fst]

/-- Per-chart statement of `negHom_zero`: over each atlas chart, negation fixes the zero
section. -/
theorem negHomOf_zero_chart (i : A.ι) :
    (A.U i).1.ι ≫ G.zero ≫ negHomOf A = (A.U i).1.ι ≫ G.zero := by
  conv_lhs => rw [← Category.assoc, ← zLift_fst A i, Category.assoc, negHomOf_piece',
    zLift_negPiece]

end Negation

/-- **(T-W7.1)** Negation on a geometric elliptic curve, glued from the per-chart model
negations (overlaps agree: transitions are variable changes by the comparison theorem, and
negation is variable-change equivariant). -/
noncomputable def EllipticCurveGeom.negHom : G.E ⟶ G.E :=
  negHomOf G.atlas

/-- **(T-W7.1-π)** Negation is a morphism over `S`. -/
@[reassoc]
theorem EllipticCurveGeom.negHom_π : G.negHom ≫ G.π = G.π := by
  show negHomOf G.atlas ≫ G.π = G.π
  refine (atlasTotalCover G.atlas).hom_ext _ _ (fun i => ?_)
  exact (negHomOf_piece_assoc G.atlas i G.π).trans
    ((negPiece_π G.atlas i).trans (congrArg (· ≫ G.π) (atlasTotalCover_f G.atlas i)).symm)

/-- **(T-W7.1-zero)** Negation fixes the zero section. -/
theorem EllipticCurveGeom.negHom_zero : G.zero ≫ G.negHom = G.zero := by
  show G.zero ≫ negHomOf G.atlas = G.zero
  refine (atlasBaseCover G.atlas).hom_ext _ _ (fun i => ?_)
  exact negHomOf_zero_chart G.atlas i

/-- **(T-W7.2)** Multiplication on a geometric elliptic curve, glued over the pullback cover
of `E ×_S E` induced by a bundled atlas from the per-chart base changes of the model
multiplication; overlap agreement = comparison theorem + variable-change equivariance. -/
noncomputable def EllipticCurveGeom.mulHom : pullback G.π G.π ⟶ G.E :=
  sorry

/-- **(T-W7.2-π)** Multiplication is a morphism over `S`. -/
@[reassoc]
theorem EllipticCurveGeom.mulHom_π :
    G.mulHom ≫ G.π = pullback.fst G.π G.π ≫ G.π := by
  sorry

/-- **(T-W7.3 → T-W7.6, the packaged group object)** The group-object structure on
`E/S` in `Over S`: multiplication and inverse glued above, unit the zero section; every
axiom holds because it holds per chart (base change of the model identity of
`GroupLawConstruction`) and morphism equality is chart-local (`Cover.hom_ext`). -/
noncomputable def EllipticCurveGeom.grpObj : GrpObj (Over.mk G.π) :=
  sorry

/-- **(T-W7.6-comm)** The glued structure is commutative (per chart: `mulOver_comm`). -/
theorem EllipticCurveGeom.grpObj_isCommMonObj :
    letI := G.grpObj
    IsCommMonObj (Over.mk G.π) := by
  sorry

/-- **(T-W7.6-one)** The unit of the glued structure is the zero section. -/
theorem EllipticCurveGeom.grpObj_one_eq_zero :
    letI := G.grpObj
    (η[Over.mk G.π] : _ ⟶ Over.mk G.π).left = (𝟙_ (Over S)).hom ≫ G.zero := by
  sorry

/-- **(T-W7.6 = MILESTONE T-W7a, assembly)** Every geometric elliptic curve enriches to the
working record: package `grpObj`, commutativity, and the unit normalisation. Discharges
`abelEnrichment_exists` as `⟨G.toEllipticCurve, toEllipticCurve_geom G⟩`. No rigidity, no
cohomology, no reducedness of `S` anywhere on this path. -/
noncomputable def EllipticCurveGeom.toEllipticCurve : EllipticCurve S :=
  { G with
    grp := G.grpObj
    comm := G.grpObj_isCommMonObj
    one_eq_zero := G.grpObj_one_eq_zero }

/-- **(T-W7.6-spec)** The enrichment forgets to the given geometry (definitional). -/
theorem EllipticCurveGeom.toEllipticCurve_geom :
    G.toEllipticCurve.toEllipticCurveGeom = G := rfl

end ModularCurves

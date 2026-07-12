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

/-- The open cover of the square `E ×_S E` by the atlas charts: the part lying over chart `i`
is the base change of the square along the chart inclusion (`pullback.fst` of the structure
map `E ×_S E → S` against `(U i).ι`). Built directly for transparent cover accessors, exactly
as `atlasTotalCover`. -/
noncomputable def atlasSquareCover : (pullback G.π G.π).OpenCover :=
  Scheme.Cover.mkOfCovers A.ι
    (fun i => pullback (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι)
    (fun i => pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι)
    (fun x => by
      obtain ⟨i, hi⟩ := A.covers ((pullback.fst G.π G.π ≫ G.π).base x)
      have hx : x ∈ Set.range (pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι).base := by
        rw [Scheme.Pullback.range_fst, Set.mem_preimage, Scheme.Opens.range_ι, SetLike.mem_coe]
        exact hi
      obtain ⟨y, hy⟩ := hx
      exact ⟨i, y, hy⟩)

@[simp] theorem atlasSquareCover_f (i : A.ι) :
    (atlasSquareCover A).f i = pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι := rfl

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
  letI := modelGrpObj (C • W)
  letI := modelGrpObj W
  haveI : IsMonHom (vcOver C W) :=
    { one_hom := by
        apply Over.OverMorphism.ext
        show ((𝟙_ (Over (Spec (CommRingCat.of R)))).hom ≫ projModelZero (C • W)) ≫
          (projModelVCIso C W).hom =
            (𝟙_ (Over (Spec (CommRingCat.of R)))).hom ≫ projModelZero W
        exact (Category.assoc _ _ _).trans
          (congrArg ((𝟙_ (Over (Spec (CommRingCat.of R)))).hom ≫ ·) (projModelVCIso_zero C W))
      mul_hom := by
        apply Over.OverMorphism.ext
        rw [Over.comp_left, Over.comp_left, Over.tensorHom_left]
        exact mulModelHom_vc C W }
  have hinv := congrArg CommaMorphism.left (GrpObj.inv_hom (vcOver C W))
  simp only [Over.comp_left, vcOver_left] at hinv
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

/-! ### Overlap agreement core (shared by negation and multiplication) -/

/-- The affine classifying map of an open `O' ≤ U k`: `O' ↪ U k ≅ Spec Γ(S, U k)`. -/
private noncomputable def ovlToChart (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    O'.toScheme ⟶ Spec Γ(S, (A.U k).1) :=
  S.homOfLE h ≫ (A.U k).2.isoSpec.hom

/-- The base change of the model chart record `modelEllipticCurve (W k)` to an open
`O' ≤ U k`. Carries its full group structure by base change (no gluing). -/
private noncomputable def bcChart (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    EllipticCurve O'.toScheme :=
  haveI := A.elliptic k
  (modelEllipticCurve (A.W k)).baseChange (ovlToChart A k h)

/-- The restriction of total spaces induced by an open inclusion `O' ≤ U k`. -/
private noncomputable def chartRestr (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    pullback G.π O'.ι ⟶ pullback G.π (A.U k).1.ι :=
  pullback.lift (pullback.fst G.π O'.ι) (pullback.snd G.π O'.ι ≫ S.homOfLE h)
    (by rw [Category.assoc, Scheme.homOfLE_ι]; exact pullback.condition)

@[reassoc] private theorem chartRestr_fst (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    chartRestr A k h ≫ pullback.fst G.π (A.U k).1.ι = pullback.fst G.π O'.ι :=
  pullback.lift_fst _ _ _

@[reassoc] private theorem chartRestr_snd (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    chartRestr A k h ≫ pullback.snd G.π (A.U k).1.ι = pullback.snd G.π O'.ι ≫ S.homOfLE h :=
  pullback.lift_snd _ _ _

/-- The base-changed inverse `ι[E_k]` acts as the base change of `negModelHom` on the first
leg (the group inverse of the base-changed record is `Over.pullback g .map (invOver W)`). -/
@[reassoc] private theorem bcChart_inv_fst (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    (ι[(bcChart A k h).asOver]).left ≫ pullback.fst (projModelπ (A.W k)) (ovlToChart A k h) =
      pullback.fst (projModelπ (A.W k)) (ovlToChart A k h) ≫ negModelHom (A.W k) :=
  pullback.lift_fst _ _ _

/-- The first-leg component of the chart-overlap comparison morphism. -/
private theorem bcChart_aux_inv (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    (A.e k).inv ≫ pullback.snd G.π (A.U k).1.ι =
      projModelπ (A.W k) ≫ (A.U k).2.isoSpec.inv := by
  haveI := A.elliptic k
  rw [← cancel_epi (A.e k).hom, Iso.hom_inv_id_assoc, ← Category.assoc, A.compat_π k,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- `O' ↪ Spec Γ(U k) ↪ U k ↪ S` is the overlap inclusion. -/
@[reassoc] private theorem ovlToChart_isoSpec_inv_ι (k : A.ι) {O' : S.Opens}
    (h : O' ≤ (A.U k).1) :
    ovlToChart A k h ≫ (A.U k).2.isoSpec.inv ≫ (A.U k).1.ι = O'.ι := by
  rw [ovlToChart, Category.assoc, Iso.hom_inv_id_assoc, Scheme.homOfLE_ι]

/-- The chart-overlap comparison morphism `E_k.E ⟶ pullback G.π O'`. -/
private noncomputable def bcChartHom (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    (bcChart A k h).E ⟶ pullback G.π O'.ι :=
  haveI := A.elliptic k
  pullback.lift
    (pullback.fst (projModelπ (A.W k)) (ovlToChart A k h) ≫
      (A.e k).inv ≫ pullback.fst G.π (A.U k).1.ι)
    (pullback.snd (projModelπ (A.W k)) (ovlToChart A k h))
    ((Category.assoc (pullback.fst (projModelπ (A.W k)) (ovlToChart A k h))
        ((A.e k).inv ≫ pullback.fst G.π (A.U k).1.ι) G.π).trans <|
      (congrArg (pullback.fst (projModelπ (A.W k)) (ovlToChart A k h) ≫ ·)
        (Category.assoc (A.e k).inv (pullback.fst G.π (A.U k).1.ι) G.π)).trans <|
      (congrArg (fun t => pullback.fst (projModelπ (A.W k)) (ovlToChart A k h) ≫
          (A.e k).inv ≫ t) (pullback.condition (f := G.π) (g := (A.U k).1.ι))).trans <|
      (congrArg (pullback.fst (projModelπ (A.W k)) (ovlToChart A k h) ≫ ·)
        (Category.assoc (A.e k).inv (pullback.snd G.π (A.U k).1.ι) (A.U k).1.ι).symm).trans <|
      (congrArg (fun t => pullback.fst (projModelπ (A.W k)) (ovlToChart A k h) ≫
          t ≫ (A.U k).1.ι) (bcChart_aux_inv A k h)).trans <|
      (congrArg (pullback.fst (projModelπ (A.W k)) (ovlToChart A k h) ≫ ·)
        (Category.assoc (projModelπ (A.W k)) (A.U k).2.isoSpec.inv (A.U k).1.ι)).trans <|
      (Category.assoc (pullback.fst (projModelπ (A.W k)) (ovlToChart A k h))
        (projModelπ (A.W k)) ((A.U k).2.isoSpec.inv ≫ (A.U k).1.ι)).symm.trans <|
      (congrArg (· ≫ (A.U k).2.isoSpec.inv ≫ (A.U k).1.ι)
        (pullback.condition (f := projModelπ (A.W k)) (g := ovlToChart A k h))).trans <|
      (Category.assoc (pullback.snd (projModelπ (A.W k)) (ovlToChart A k h))
        (ovlToChart A k h) ((A.U k).2.isoSpec.inv ≫ (A.U k).1.ι)).trans <|
      congrArg (pullback.snd (projModelπ (A.W k)) (ovlToChart A k h) ≫ ·)
        (ovlToChart_isoSpec_inv_ι A k h))

@[reassoc] private theorem bcChartHom_fst (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    bcChartHom A k h ≫ pullback.fst G.π O'.ι =
      pullback.fst (projModelπ (A.W k)) (ovlToChart A k h) ≫
        (A.e k).inv ≫ pullback.fst G.π (A.U k).1.ι :=
  pullback.lift_fst _ _ _

@[reassoc] private theorem bcChartHom_snd (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    bcChartHom A k h ≫ pullback.snd G.π O'.ι =
      pullback.snd (projModelπ (A.W k)) (ovlToChart A k h) :=
  pullback.lift_snd _ _ _

/-- `O' ↪ Spec Γ(U k) ↪ U k` (the affine-chart form of the overlap inclusion). -/
private theorem ovlToChart_isoSpec_inv (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    ovlToChart A k h ≫ (A.U k).2.isoSpec.inv = S.homOfLE h := by
  rw [ovlToChart, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The chart-overlap comparison morphism in the other direction. -/
private noncomputable def bcChartInv (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    pullback G.π O'.ι ⟶ (bcChart A k h).E :=
  haveI := A.elliptic k
  pullback.lift (chartRestr A k h ≫ (A.e k).hom) (pullback.snd G.π O'.ι)
    ((Category.assoc (chartRestr A k h) (A.e k).hom (projModelπ (A.W k))).trans <|
      (congrArg (chartRestr A k h ≫ ·) (A.compat_π k)).trans <|
      (Category.assoc (chartRestr A k h) (pullback.snd G.π (A.U k).1.ι)
        (A.U k).2.isoSpec.hom).symm.trans <|
      (congrArg (· ≫ (A.U k).2.isoSpec.hom) (chartRestr_snd A k h)).trans <|
      Category.assoc (pullback.snd G.π O'.ι) (S.homOfLE h) (A.U k).2.isoSpec.hom)

@[reassoc] private theorem bcChartInv_fst (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    bcChartInv A k h ≫ pullback.fst (projModelπ (A.W k)) (ovlToChart A k h) =
      chartRestr A k h ≫ (A.e k).hom :=
  pullback.lift_fst _ _ _

@[reassoc] private theorem bcChartInv_snd (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    bcChartInv A k h ≫ pullback.snd (projModelπ (A.W k)) (ovlToChart A k h) =
      pullback.snd G.π O'.ι :=
  pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The two comparison morphisms cancel through `chartRestr`. -/
@[reassoc] private theorem bcChartHom_chartRestr (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    bcChartHom A k h ≫ chartRestr A k h =
      pullback.fst (projModelπ (A.W k)) (ovlToChart A k h) ≫ (A.e k).inv := by
  haveI := A.elliptic k
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, chartRestr_fst A k h, bcChartHom_fst A k h, Category.assoc]
  · rw [Category.assoc, chartRestr_snd A k h, bcChartHom_snd_assoc A k h, Category.assoc,
      bcChart_aux_inv A k h, ← Category.assoc,
      pullback.condition (f := projModelπ (A.W k)) (g := ovlToChart A k h),
      Category.assoc, ovlToChart_isoSpec_inv A k h]

set_option backward.isDefEq.respectTransparency false in
/-- The chart-overlap scheme isomorphism: the base-changed model total space over `O'` is the
record total space over `O'`. Built with explicit legs so pointedness and inversion compute. -/
private noncomputable def bcChartSchemeIso (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    (bcChart A k h).E ≅ pullback G.π O'.ι :=
  haveI := A.elliptic k
  { hom := bcChartHom A k h
    inv := bcChartInv A k h
    hom_inv_id := by
      refine pullback.hom_ext ?_ ?_
      · simp only [modelEllipticCurve_π]
        rw [Category.assoc, bcChartInv_fst A k h, bcChartHom_chartRestr_assoc A k h,
          Iso.inv_hom_id, Category.comp_id, Category.id_comp]
      · simp only [modelEllipticCurve_π]
        rw [Category.assoc, bcChartInv_snd A k h, bcChartHom_snd A k h, Category.id_comp]
    inv_hom_id := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, bcChartHom_fst, bcChartInv_fst_assoc, Iso.hom_inv_id_assoc,
          chartRestr_fst, Category.id_comp]
      · rw [Category.assoc, bcChartHom_snd, bcChartInv_snd, Category.id_comp] }

/-- The pointed chart-overlap isomorphism in `Over O'`. -/
private noncomputable def bcChartOverIso (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    (bcChart A k h).asOver ≅ Over.mk (pullback.snd G.π O'.ι) :=
  haveI := A.elliptic k
  Over.isoMk (bcChartSchemeIso A k h) (bcChartHom_snd A k h)

@[simp] private theorem bcChartOverIso_hom_left (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    (bcChartOverIso A k h).hom.left = bcChartHom A k h :=
  rfl

@[simp] private theorem bcChartOverIso_inv_left (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    (bcChartOverIso A k h).inv.left = bcChartInv A k h :=
  rfl

private theorem bcChart_zero_fst (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    (bcChart A k h).zero ≫ pullback.fst (projModelπ (A.W k)) (ovlToChart A k h) =
      ovlToChart A k h ≫ projModelZero (A.W k) :=
  pullback.lift_fst _ _ _

private theorem bcChart_zero_snd (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    (bcChart A k h).zero ≫ pullback.snd (projModelπ (A.W k)) (ovlToChart A k h) =
      𝟙 O'.toScheme :=
  pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The chart-overlap isomorphism is pointed: it carries the base-changed zero section to the
record zero section over `O'`. -/
private theorem bcChartZero_pt (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    (bcChart A k h).zero ≫ bcChartHom A k h =
      pullback.lift (O'.ι ≫ G.zero) (𝟙 O'.toScheme)
        (by rw [Category.assoc, G.zero_π, Category.comp_id, Category.id_comp]) := by
  haveI := A.elliptic k
  have hz : projModelZero (A.W k) ≫ (A.e k).inv = (A.U k).2.isoSpec.inv ≫ zLift A k := by
    rw [← cancel_mono (A.e k).hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Category.assoc, zLift_totalIso, Iso.inv_hom_id_assoc]
  have hzf : projModelZero (A.W k) ≫ (A.e k).inv ≫ pullback.fst G.π (A.U k).1.ι =
      (A.U k).2.isoSpec.inv ≫ (A.U k).1.ι ≫ G.zero := by
    rw [← Category.assoc, hz, Category.assoc, zLift_fst]
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, bcChartHom_fst, ← Category.assoc, bcChart_zero_fst, pullback.lift_fst,
      Category.assoc, hzf, ovlToChart_isoSpec_inv_ι_assoc]
  · rw [Category.assoc, bcChartHom_snd, bcChart_zero_snd, pullback.lift_snd]

set_option backward.isDefEq.respectTransparency false in
/-- The conjugate of the base-changed inverse through the chart-overlap isomorphism, read into
the record total space, is the overlap-restricted negation piece. -/
private theorem bcChart_conjInv_fst (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    (bcChartInv A k h ≫ ι[(bcChart A k h).asOver].left ≫ bcChartHom A k h) ≫
        pullback.fst G.π O'.ι =
      chartRestr A k h ≫ negPiece A k := by
  haveI := A.elliptic k
  simp only [negPiece, Category.assoc, bcChartHom_fst, bcChart_inv_fst_assoc, bcChartInv_fst_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The overlap comparison isomorphism `θ = ψ_i ∘ ψ_j⁻¹` is a monoid homomorphism of the two
base-changed model records: pointed by the shared record zero (`bcChartZero_pt`), hence its
multiplicativity is `isMonHom_of_pointedIso_records`. Shared by both the negation and
multiplication overlap-agreement arguments. -/
private theorem chart_pair_isMonHom (i j : A.ι) {O' : S.Opens}
    (hi : O' ≤ (A.U i).1) (hj : O' ≤ (A.U j).1) :
    haveI := A.elliptic i
    haveI := A.elliptic j
    IsMonHom (bcChartOverIso A i hi ≪≫ (bcChartOverIso A j hj).symm).hom := by
  haveI := A.elliptic i
  haveI := A.elliptic j
  have hpt : η[(bcChart A i hi).asOver] ≫ (bcChartOverIso A i hi).hom =
      η[(bcChart A j hj).asOver] ≫ (bcChartOverIso A j hj).hom := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, bcChartOverIso_hom_left, bcChartOverIso_hom_left,
      (bcChart A i hi).one_eq_zero, (bcChart A j hj).one_eq_zero, Category.assoc, Category.assoc,
      bcChartZero_pt, bcChartZero_pt]
  have hη : η[(bcChart A i hi).asOver] ≫
      (bcChartOverIso A i hi ≪≫ (bcChartOverIso A j hj).symm).hom =
      η[(bcChart A j hj).asOver] := by
    rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, hpt, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  exact { one_hom := hη
          mul_hom := isMonHom_of_pointedIso_records (bcChart A i hi) (bcChart A j hj)
            (bcChartOverIso A i hi ≪≫ (bcChartOverIso A j hj).symm) hη }

set_option backward.isDefEq.respectTransparency false in
/-- **(overlap core, negation)** The per-chart negations agree on the overlap `O'` of two
charts: both transport to the base-changed model records, whose group inverses
`chart_pair_isMonHom` + `GrpObj.inv_hom` identify. -/
private theorem chart_pair_neg_agree (i j : A.ι) {O' : S.Opens}
    (hi : O' ≤ (A.U i).1) (hj : O' ≤ (A.U j).1) :
    chartRestr A i hi ≫ negPiece A i = chartRestr A j hj ≫ negPiece A j := by
  haveI := A.elliptic i
  haveI := A.elliptic j
  haveI := chart_pair_isMonHom A i j hi hj
  have hinv := GrpObj.inv_hom (bcChartOverIso A i hi ≪≫ (bcChartOverIso A j hj).symm).hom
  have hκ : (bcChartOverIso A i hi).inv ≫ ι[(bcChart A i hi).asOver] ≫
        (bcChartOverIso A i hi).hom =
      (bcChartOverIso A j hj).inv ≫ ι[(bcChart A j hj).asOver] ≫ (bcChartOverIso A j hj).hom := by
    have h1 := congrArg
      (fun m => (bcChartOverIso A i hi).inv ≫ m ≫ (bcChartOverIso A j hj).hom) hinv
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc] at h1
    exact h1
  have hκL := congrArg CommaMorphism.left hκ
  simp only [Over.comp_left, bcChartOverIso_hom_left, bcChartOverIso_inv_left] at hκL
  have hfin := congrArg (· ≫ pullback.fst G.π O'.ι) hκL
  exact (bcChart_conjInv_fst A i hi).symm.trans (hfin.trans (bcChart_conjInv_fst A j hj))

/-- The per-chart negations agree on the overlaps of the atlas total cover: on the overlap
the two pointed chart presentations differ by a variable change, and `negModelHom` is
variable-change equivariant. -/
theorem negPiece_agree (i j : A.ι) :
    pullback.fst ((atlasTotalCover A).f i) ((atlasTotalCover A).f j) ≫ negPiece A i =
      pullback.snd ((atlasTotalCover A).f i) ((atlasTotalCover A).f j) ≫ negPiece A j := by
  simp only [atlasTotalCover_f]
  have hi : (A.U i).1 ⊓ (A.U j).1 ≤ (A.U i).1 := inf_le_left
  have hj : (A.U i).1 ⊓ (A.U j).1 ≤ (A.U j).1 := inf_le_right
  have hbij : (pullback.fst (pullback.fst G.π (A.U i).1.ι) (pullback.fst G.π (A.U j).1.ι) ≫
        pullback.snd G.π (A.U i).1.ι) ≫ (A.U i).1.ι =
      (pullback.snd (pullback.fst G.π (A.U i).1.ι) (pullback.fst G.π (A.U j).1.ι) ≫
        pullback.snd G.π (A.U j).1.ι) ≫ (A.U j).1.ι := by
    rw [Category.assoc, Category.assoc, ← pullback.condition (f := G.π) (g := (A.U i).1.ι),
      ← pullback.condition (f := G.π) (g := (A.U j).1.ι), ← Category.assoc, ← Category.assoc,
      pullback.condition]
  set b := (isPullback_opens_inf (A.U i).1 (A.U j).1).lift _ _ hbij with hb
  have hbfst : b ≫ S.homOfLE hi = pullback.fst (pullback.fst G.π (A.U i).1.ι)
      (pullback.fst G.π (A.U j).1.ι) ≫ pullback.snd G.π (A.U i).1.ι :=
    (isPullback_opens_inf (A.U i).1 (A.U j).1).lift_fst _ _ _
  have hbsnd : b ≫ S.homOfLE hj = pullback.snd (pullback.fst G.π (A.U i).1.ι)
      (pullback.fst G.π (A.U j).1.ι) ≫ pullback.snd G.π (A.U j).1.ι :=
    (isPullback_opens_inf (A.U i).1 (A.U j).1).lift_snd _ _ _
  have hab : (pullback.fst (pullback.fst G.π (A.U i).1.ι) (pullback.fst G.π (A.U j).1.ι) ≫
        pullback.fst G.π (A.U i).1.ι) ≫ G.π = b ≫ ((A.U i).1 ⊓ (A.U j).1).ι := by
    rw [Category.assoc, pullback.condition (f := G.π) (g := (A.U i).1.ι), ← Category.assoc,
      ← hbfst, Category.assoc, Scheme.homOfLE_ι]
  set w := pullback.lift _ b hab with hw
  have hwfst : w ≫ pullback.fst G.π ((A.U i).1 ⊓ (A.U j).1).ι =
      pullback.fst (pullback.fst G.π (A.U i).1.ι) (pullback.fst G.π (A.U j).1.ι) ≫
        pullback.fst G.π (A.U i).1.ι :=
    pullback.lift_fst _ _ _
  have hwsnd : w ≫ pullback.snd G.π ((A.U i).1 ⊓ (A.U j).1).ι = b := pullback.lift_snd _ _ _
  have hwi : w ≫ chartRestr A i hi = pullback.fst (pullback.fst G.π (A.U i).1.ι)
      (pullback.fst G.π (A.U j).1.ι) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, chartRestr_fst, hwfst]
    · rw [Category.assoc, chartRestr_snd, ← Category.assoc, hwsnd, hbfst]
  have hwj : w ≫ chartRestr A j hj = pullback.snd (pullback.fst G.π (A.U i).1.ι)
      (pullback.fst G.π (A.U j).1.ι) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, chartRestr_fst, hwfst, pullback.condition]
    · rw [Category.assoc, chartRestr_snd, ← Category.assoc, hwsnd, hbsnd]
  exact (congrArg (· ≫ negPiece A i) hwi.symm).trans <|
    (Category.assoc w (chartRestr A i hi) (negPiece A i)).trans <|
    (congrArg (w ≫ ·) (chart_pair_neg_agree A i j hi hj)).trans <|
    (Category.assoc w (chartRestr A j hj) (negPiece A j)).symm.trans <|
    congrArg (· ≫ negPiece A j) hwj

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

/-! ### Multiplication pieces (over the atlas square cover) -/

/-- The first component of a square point over chart `i`, as a point of `pullback G.π (U i).ι`. -/
noncomputable def sqLift1 (i : A.ι) :
    pullback (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι ⟶ pullback G.π (A.U i).1.ι :=
  pullback.lift
    (pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι ≫ pullback.fst G.π G.π)
    (pullback.snd (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι)
    (by rw [Category.assoc]; exact pullback.condition)

/-- The second component of a square point over chart `i`, as a point of
`pullback G.π (U i).ι`. -/
noncomputable def sqLift2 (i : A.ι) :
    pullback (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι ⟶ pullback G.π (A.U i).1.ι :=
  pullback.lift
    (pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι ≫ pullback.snd G.π G.π)
    (pullback.snd (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι)
    (by
      rw [Category.assoc, ← pullback.condition (f := G.π) (g := G.π)]
      exact pullback.condition)

@[reassoc] theorem sqLift1_snd (i : A.ι) :
    sqLift1 A i ≫ pullback.snd G.π (A.U i).1.ι =
      pullback.snd (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι :=
  pullback.lift_snd _ _ _

@[reassoc] theorem sqLift2_snd (i : A.ι) :
    sqLift2 A i ≫ pullback.snd G.π (A.U i).1.ι =
      pullback.snd (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι :=
  pullback.lift_snd _ _ _

@[reassoc] theorem sqLift1_fst (i : A.ι) :
    sqLift1 A i ≫ pullback.fst G.π (A.U i).1.ι =
      pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι ≫ pullback.fst G.π G.π :=
  pullback.lift_fst _ _ _

@[reassoc] theorem sqLift2_fst (i : A.ι) :
    sqLift2 A i ≫ pullback.fst G.π (A.U i).1.ι =
      pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι ≫ pullback.snd G.π G.π :=
  pullback.lift_fst _ _ _

@[reassoc] theorem sqLift1_hom_π (i : A.ι) :
    haveI := A.elliptic i
    (sqLift1 A i ≫ (A.e i).hom) ≫ projModelπ (A.W i) =
      pullback.snd (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι ≫ (A.U i).2.isoSpec.hom := by
  haveI := A.elliptic i
  rw [Category.assoc, A.compat_π i, sqLift1_snd_assoc]

@[reassoc] theorem sqLift2_hom_π (i : A.ι) :
    haveI := A.elliptic i
    (sqLift2 A i ≫ (A.e i).hom) ≫ projModelπ (A.W i) =
      pullback.snd (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι ≫ (A.U i).2.isoSpec.hom := by
  haveI := A.elliptic i
  rw [Category.assoc, A.compat_π i, sqLift2_snd_assoc]

/-- The per-chart multiplication piece: transport both square components through the chart
isomorphism to the model square, apply the model multiplication `mulModelHom (W i)`, and embed
back into `E`. -/
noncomputable def mulPiece (i : A.ι) :
    pullback (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι ⟶ G.E :=
  haveI := A.elliptic i
  pullback.lift (sqLift1 A i ≫ (A.e i).hom) (sqLift2 A i ≫ (A.e i).hom)
    ((sqLift1_hom_π A i).trans (sqLift2_hom_π A i).symm) ≫
    mulModelHom (A.W i) ≫ (A.e i).inv ≫ pullback.fst G.π (A.U i).1.ι

/-! ### Overlap agreement of the multiplication pieces -/

/-- The first component of a square point over `O'`, as a point of `pullback G.π O'`. -/
noncomputable def sqComp1 {O' : S.Opens} :
    pullback (pullback.fst G.π G.π ≫ G.π) O'.ι ⟶ pullback G.π O'.ι :=
  pullback.lift
    (pullback.fst (pullback.fst G.π G.π ≫ G.π) O'.ι ≫ pullback.fst G.π G.π)
    (pullback.snd (pullback.fst G.π G.π ≫ G.π) O'.ι)
    (by rw [Category.assoc]; exact pullback.condition)

/-- The second component of a square point over `O'`, as a point of `pullback G.π O'`. -/
noncomputable def sqComp2 {O' : S.Opens} :
    pullback (pullback.fst G.π G.π ≫ G.π) O'.ι ⟶ pullback G.π O'.ι :=
  pullback.lift
    (pullback.fst (pullback.fst G.π G.π ≫ G.π) O'.ι ≫ pullback.snd G.π G.π)
    (pullback.snd (pullback.fst G.π G.π ≫ G.π) O'.ι)
    (by
      rw [Category.assoc, ← pullback.condition (f := G.π) (g := G.π)]
      exact pullback.condition)

@[reassoc] theorem sqComp1_snd {O' : S.Opens} :
    sqComp1 (G := G) (O' := O') ≫ pullback.snd G.π O'.ι =
      pullback.snd (pullback.fst G.π G.π ≫ G.π) O'.ι :=
  pullback.lift_snd _ _ _

@[reassoc] theorem sqComp2_snd {O' : S.Opens} :
    sqComp2 (G := G) (O' := O') ≫ pullback.snd G.π O'.ι =
      pullback.snd (pullback.fst G.π G.π ≫ G.π) O'.ι :=
  pullback.lift_snd _ _ _

@[reassoc] theorem sqComp1_fst {O' : S.Opens} :
    sqComp1 (G := G) (O' := O') ≫ pullback.fst G.π O'.ι =
      pullback.fst (pullback.fst G.π G.π ≫ G.π) O'.ι ≫ pullback.fst G.π G.π :=
  pullback.lift_fst _ _ _

@[reassoc] theorem sqComp2_fst {O' : S.Opens} :
    sqComp2 (G := G) (O' := O') ≫ pullback.fst G.π O'.ι =
      pullback.fst (pullback.fst G.π G.π ≫ G.π) O'.ι ≫ pullback.snd G.π G.π :=
  pullback.lift_fst _ _ _

/-- The restriction of the square total space along an open inclusion `O' ≤ U k`. -/
noncomputable def sqChartRestr (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    pullback (pullback.fst G.π G.π ≫ G.π) O'.ι ⟶
      pullback (pullback.fst G.π G.π ≫ G.π) (A.U k).1.ι :=
  pullback.lift (pullback.fst (pullback.fst G.π G.π ≫ G.π) O'.ι)
    (pullback.snd (pullback.fst G.π G.π ≫ G.π) O'.ι ≫ S.homOfLE h)
    (by rw [Category.assoc, Scheme.homOfLE_ι]; exact pullback.condition)

@[reassoc] theorem sqChartRestr_fst (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    sqChartRestr A k h ≫ pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U k).1.ι =
      pullback.fst (pullback.fst G.π G.π ≫ G.π) O'.ι :=
  pullback.lift_fst _ _ _

@[reassoc] theorem sqChartRestr_snd (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    sqChartRestr A k h ≫ pullback.snd (pullback.fst G.π G.π ≫ G.π) (A.U k).1.ι =
      pullback.snd (pullback.fst G.π G.π ≫ G.π) O'.ι ≫ S.homOfLE h :=
  pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The square over `O'` mapped into the base-changed model square of chart `k`, via
`bcChartInv` on both components. -/
noncomputable def sqBcInv (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    pullback (pullback.fst G.π G.π ≫ G.π) O'.ι ⟶
      pullback (pullback.snd (projModelπ (A.W k)) (ovlToChart A k h))
        (pullback.snd (projModelπ (A.W k)) (ovlToChart A k h)) :=
  haveI := A.elliptic k
  pullback.lift (sqComp1 (G := G) (O' := O') ≫ bcChartInv A k h)
    (sqComp2 (G := G) (O' := O') ≫ bcChartInv A k h)
    (by
      have e1 : (sqComp1 (G := G) (O' := O') ≫ bcChartInv A k h) ≫
          pullback.snd (projModelπ (A.W k)) (ovlToChart A k h) =
          pullback.snd (pullback.fst G.π G.π ≫ G.π) O'.ι := by
        rw [Category.assoc, bcChartInv_snd, sqComp1_snd]
      have e2 : (sqComp2 (G := G) (O' := O') ≫ bcChartInv A k h) ≫
          pullback.snd (projModelπ (A.W k)) (ovlToChart A k h) =
          pullback.snd (pullback.fst G.π G.π ≫ G.π) O'.ι := by
        rw [Category.assoc, bcChartInv_snd, sqComp2_snd]
      rw [e1, e2])

@[reassoc] theorem sqBcInv_fst (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    sqBcInv A k h ≫ pullback.fst (pullback.snd (projModelπ (A.W k)) (ovlToChart A k h))
        (pullback.snd (projModelπ (A.W k)) (ovlToChart A k h)) =
      sqComp1 (G := G) (O' := O') ≫ bcChartInv A k h :=
  pullback.lift_fst _ _ _

@[reassoc] theorem sqBcInv_snd (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    sqBcInv A k h ≫ pullback.snd (pullback.snd (projModelπ (A.W k)) (ovlToChart A k h))
        (pullback.snd (projModelπ (A.W k)) (ovlToChart A k h)) =
      sqComp2 (G := G) (O' := O') ≫ bcChartInv A k h :=
  pullback.lift_snd _ _ _

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

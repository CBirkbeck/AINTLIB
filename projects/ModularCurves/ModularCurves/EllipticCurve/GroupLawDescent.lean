/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.GroupLaw
import ModularCurves.EllipticCurve.GroupLawConstruction
import ModularCurves.EllipticCurve.WeierstrassAtlasBundle
import ModularCurves.EllipticCurve.GroupLaw
import ModularCurves.EllipticCurve.RecordGroupUnique
import ModularCurves.EllipticCurve.Comparison
import ModularCurves.EllipticCurve.ModelVCEquivariance
import ModularCurves.ForMathlib.BaseChangeAlongCompat

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

-- v4.33 bump: opens/hom coercions are no longer transparent enough for the
-- `≫`-associativity and `comp_apply` rewrites below.
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

/-- The structure morphism of the monoidal unit of `Over T` is the identity. -/
private theorem overUnit_hom (T : Scheme.{u}) : (𝟙_ (Over T)).hom = 𝟙 T := rfl

/-- **(model unit law, lift form)** At the model, `mul (zero ∘ π, id) = id`: the scheme-level
lift form of the left unit law `oneOver_mulOver`, obtained at the `Over` level by identifying
`⟨zero ∘ π, id⟩` with `(λ_).inv ≫ (η ▷ X)` and cancelling the left unitor. -/
private theorem model_one_mul_lift {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    [W.IsElliptic] :
    pullback.lift (projModelπ W ≫ projModelZero W) (𝟙 (projModel W))
        (by rw [Category.assoc, projModelZero_projModelπ, Category.comp_id, Category.id_comp]) ≫
      mulModelHom W = 𝟙 (projModel W) := by
  have key : CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.toUnit (modelOver W) ≫ oneOver W) (𝟙 (modelOver W)) ≫
      mulOver W = 𝟙 (modelOver W) := by
    have hlu : CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.toUnit (modelOver W) ≫ oneOver W) (𝟙 (modelOver W)) =
        (λ_ (modelOver W)).inv ≫ (oneOver W ▷ modelOver W) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp
      · simp
    rw [hlu, Category.assoc, oneOver_mulOver W, Iso.inv_hom_id]
  have h := congrArg CommaMorphism.left key
  simp only [Over.comp_left, Over.lift_left, Over.toUnit_left, oneOver_left, Over.id_left,
    overUnit_hom, mulOver_left] at h
  exact h

/-- **(model unit law, lift form, right)** At the model, `mul (id, zero ∘ π) = id`: the
scheme-level lift form of the right unit law `mulOver_oneOver`. -/
private theorem model_mul_one_lift {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    [W.IsElliptic] :
    pullback.lift (𝟙 (projModel W)) (projModelπ W ≫ projModelZero W)
        (by rw [Category.id_comp, Category.assoc, projModelZero_projModelπ, Category.comp_id]) ≫
      mulModelHom W = 𝟙 (projModel W) := by
  have key : CartesianMonoidalCategory.lift (𝟙 (modelOver W))
        (CartesianMonoidalCategory.toUnit (modelOver W) ≫ oneOver W) ≫
      mulOver W = 𝟙 (modelOver W) := by
    have hru : CartesianMonoidalCategory.lift (𝟙 (modelOver W))
          (CartesianMonoidalCategory.toUnit (modelOver W) ≫ oneOver W) =
        (ρ_ (modelOver W)).inv ≫ (modelOver W ◁ oneOver W) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp
      · simp
    rw [hru, Category.assoc, mulOver_oneOver W, Iso.inv_hom_id]
  have h := congrArg CommaMorphism.left key
  simp only [Over.comp_left, Over.lift_left, Over.toUnit_left, oneOver_left, Over.id_left,
    overUnit_hom, mulOver_left] at h
  exact h

/-- **(model associativity, lift form)** `mul (mul (a, b), c) = mul (a, mul (b, c))` at the
model, from `MonObj.lift_lift_assoc` at the T-G4 model group object. -/
private theorem model_mul_assoc_lift {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    [W.IsElliptic] {Z : Scheme.{u}} (a b c : Z ⟶ projModel W)
    (hab : a ≫ projModelπ W = b ≫ projModelπ W) (hbc : b ≫ projModelπ W = c ≫ projModelπ W) :
    pullback.lift (pullback.lift a b hab ≫ mulModelHom W) c
        (by rw [Category.assoc, mulModelHom_π, ← Category.assoc, pullback.lift_fst]
            exact hab.trans hbc) ≫ mulModelHom W =
      pullback.lift a (pullback.lift b c hbc ≫ mulModelHom W)
        (by rw [Category.assoc, mulModelHom_π, ← Category.assoc, pullback.lift_fst]
            exact hab) ≫ mulModelHom W := by
  letI := modelGrpObj W
  have h := congrArg CommaMorphism.left (MonObj.lift_lift_assoc (B := modelOver W)
    (A := Over.mk (a ≫ projModelπ W))
    (Over.homMk a rfl) (Over.homMk b hab.symm) (Over.homMk c (hab.trans hbc).symm))
  simp only [Over.comp_left, Over.lift_left, Over.homMk_left] at h
  exact h

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

/-- The open cover of the cube `(E ×_S E) ×_S E` (the underlying scheme of `(X ⊗ X) ⊗ X`) by
the atlas charts — the base change of the cube along the chart inclusion. Used for the
associativity axiom. -/
noncomputable def atlasCubeCover :
    (pullback (pullback.fst G.π G.π ≫ G.π) G.π).OpenCover :=
  Scheme.Cover.mkOfCovers A.ι
    (fun i => pullback (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫
      (pullback.fst G.π G.π ≫ G.π)) (A.U i).1.ι)
    (fun i => pullback.fst (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫
      (pullback.fst G.π G.π ≫ G.π)) (A.U i).1.ι)
    (fun x => by
      obtain ⟨i, hi⟩ := A.covers ((pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫
        (pullback.fst G.π G.π ≫ G.π)).base x)
      have hx : x ∈ Set.range (pullback.fst (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫
          (pullback.fst G.π G.π ≫ G.π)) (A.U i).1.ι).base := by
        rw [Scheme.Pullback.range_fst, Set.mem_preimage, Scheme.Opens.range_ι, SetLike.mem_coe]
        exact hi
      obtain ⟨y, hy⟩ := hx
      exact ⟨i, y, hy⟩)

@[simp] theorem atlasCubeCover_f (i : A.ι) :
    (atlasCubeCover A).f i = pullback.fst (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫
      (pullback.fst G.π G.π ≫ G.π)) (A.U i).1.ι := rfl

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
@[reassoc] private theorem bcChart_aux_inv (k : A.ι) :
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
          t ≫ (A.U k).1.ι) (bcChart_aux_inv A k)).trans <|
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
      bcChart_aux_inv A k, ← Category.assoc,
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

/-- The base-changed model multiplication acts, on the first leg, as `mulModelHom` on the
square projections. The `CartesianMonoidalCategory (Over Scheme)` instance is definitionally
the generic `Over.cartesianMonoidalCategory`, so `convert … <;> rfl` bridges the reducibility
gap (using `letI` on `modelGrpObj` to keep `μ[modelOver] = mulOver` transparent) — no diamond,
no `μ`-re-resolution. -/
@[reassoc] theorem bcChart_mul_fst (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    (μ[(bcChart A k h).asOver]).left ≫ pullback.fst (projModelπ (A.W k)) (ovlToChart A k h) =
      pullback.lift
        (pullback.fst (pullback.snd (projModelπ (A.W k)) (ovlToChart A k h))
            (pullback.snd (projModelπ (A.W k)) (ovlToChart A k h)) ≫
          pullback.fst (projModelπ (A.W k)) (ovlToChart A k h))
        (pullback.snd (pullback.snd (projModelπ (A.W k)) (ovlToChart A k h))
            (pullback.snd (projModelπ (A.W k)) (ovlToChart A k h)) ≫
          pullback.fst (projModelπ (A.W k)) (ovlToChart A k h))
        (by
          simp only [Category.assoc]
          rw [pullback.condition (f := projModelπ (A.W k)) (g := ovlToChart A k h),
            ← Category.assoc, pullback.condition (f := pullback.snd (projModelπ (A.W k))
              (ovlToChart A k h)) (g := pullback.snd (projModelπ (A.W k)) (ovlToChart A k h)),
            Category.assoc]) ≫
        mulModelHom (A.W k) := by
  haveI := A.elliptic k
  letI := modelGrpObj (A.W k)
  convert Over.grpObjMkPullbackSnd_mul_left_fst (projModelπ (A.W k)) (ovlToChart A k h) using 2 <;>
    rfl

/-- The first square component commutes with the chart / overlap restrictions. -/
@[reassoc] theorem sqComp1_chartRestr (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    sqComp1 (G := G) (O' := O') ≫ chartRestr A k h = sqChartRestr A k h ≫ sqLift1 A k := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, chartRestr_fst, sqComp1_fst, Category.assoc, sqLift1_fst,
      sqChartRestr_fst_assoc]
  · rw [Category.assoc, chartRestr_snd, ← Category.assoc, sqComp1_snd, Category.assoc,
      sqLift1_snd, sqChartRestr_snd]

/-- The second square component commutes with the chart / overlap restrictions. -/
@[reassoc] theorem sqComp2_chartRestr (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    sqComp2 (G := G) (O' := O') ≫ chartRestr A k h = sqChartRestr A k h ≫ sqLift2 A k := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, chartRestr_fst, sqComp2_fst, Category.assoc, sqLift2_fst,
      sqChartRestr_fst_assoc]
  · rw [Category.assoc, chartRestr_snd, ← Category.assoc, sqComp2_snd, Category.assoc,
      sqLift2_snd, sqChartRestr_snd]

set_option backward.isDefEq.respectTransparency false in
/-- **(mul cprime)** The conjugate of the base-changed model multiplication through the
chart-overlap isomorphism, read into the record, is the overlap-restricted multiplication
piece. -/
theorem bcChart_conjMul_fst (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    (sqBcInv A k h ≫ (μ[(bcChart A k h).asOver]).left ≫ bcChartHom A k h) ≫
        pullback.fst G.π O'.ι =
      sqChartRestr A k h ≫ mulPiece A k := by
  haveI := A.elliptic k
  have hPM : sqBcInv A k h ≫ pullback.lift
        (pullback.fst (pullback.snd (projModelπ (A.W k)) (ovlToChart A k h))
            (pullback.snd (projModelπ (A.W k)) (ovlToChart A k h)) ≫
          pullback.fst (projModelπ (A.W k)) (ovlToChart A k h))
        (pullback.snd (pullback.snd (projModelπ (A.W k)) (ovlToChart A k h))
            (pullback.snd (projModelπ (A.W k)) (ovlToChart A k h)) ≫
          pullback.fst (projModelπ (A.W k)) (ovlToChart A k h))
        (by
          simp only [Category.assoc]
          rw [pullback.condition (f := projModelπ (A.W k)) (g := ovlToChart A k h),
            ← Category.assoc, pullback.condition (f := pullback.snd (projModelπ (A.W k))
              (ovlToChart A k h)) (g := pullback.snd (projModelπ (A.W k)) (ovlToChart A k h)),
            Category.assoc]) =
      sqChartRestr A k h ≫ pullback.lift (sqLift1 A k ≫ (A.e k).hom) (sqLift2 A k ≫ (A.e k).hom)
        ((sqLift1_hom_π A k).trans (sqLift2_hom_π A k).symm) := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst, sqBcInv_fst_assoc, bcChartInv_fst,
        sqComp1_chartRestr_assoc]
    · simp only [Category.assoc, pullback.lift_snd, sqBcInv_snd_assoc, bcChartInv_fst,
        sqComp2_chartRestr_assoc]
  rw [mulPiece]
  simp only [Category.assoc, bcChartHom_fst, bcChart_mul_fst_assoc]
  rw [reassoc_of% hPM]

@[reassoc] theorem bcChartInv_hom_id (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    bcChartInv A k h ≫ bcChartHom A k h = 𝟙 (pullback G.π O'.ι) :=
  haveI := A.elliptic k
  (bcChartSchemeIso A k h).inv_hom_id

@[simp] theorem bcChart_asOver_hom (k : A.ι) {O' : S.Opens} (h : O' ≤ (A.U k).1) :
    haveI := A.elliptic k
    (bcChart A k h).asOver.hom = pullback.snd (projModelπ (A.W k)) (ovlToChart A k h) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **(overlap core, multiplication)** The per-chart multiplications agree on the overlap `O'`
of two charts: `chart_pair_isMonHom`'s multiplicativity intertwines the two base-changed model
multiplications, which `bcChart_conjMul_fst` identifies with the multiplication pieces. -/
private theorem chart_pair_mul_agree (i j : A.ι) {O' : S.Opens}
    (hi : O' ≤ (A.U i).1) (hj : O' ≤ (A.U j).1) :
    sqChartRestr A i hi ≫ mulPiece A i = sqChartRestr A j hj ≫ mulPiece A j := by
  haveI := A.elliptic i
  haveI := A.elliptic j
  haveI := chart_pair_isMonHom A i j hi hj
  have hθl : (bcChartOverIso A i hi ≪≫ (bcChartOverIso A j hj).symm).hom.left =
      bcChartHom A i hi ≫ bcChartInv A j hj := by
    rw [Iso.trans_hom, Iso.symm_hom, Over.comp_left, bcChartOverIso_hom_left,
      bcChartOverIso_inv_left]
  have hmulL := congrArg CommaMorphism.left
    (IsMonHom.mul_hom (bcChartOverIso A i hi ≪≫ (bcChartOverIso A j hj).symm).hom)
  simp only [Over.comp_left] at hmulL
  have hsq : sqBcInv A i hi ≫
      ((bcChartOverIso A i hi ≪≫ (bcChartOverIso A j hj).symm).hom ⊗ₘ
        (bcChartOverIso A i hi ≪≫ (bcChartOverIso A j hj).symm).hom).left = sqBcInv A j hj := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc]
      erw [Over.tensorHom_left_fst]
      simp only [bcChart_asOver_hom]
      rw [← Category.assoc, sqBcInv_fst, hθl, Category.assoc, bcChartInv_hom_id_assoc, sqBcInv_fst]
    · rw [Category.assoc]
      erw [Over.tensorHom_left_snd]
      simp only [bcChart_asOver_hom]
      rw [← Category.assoc, sqBcInv_snd, hθl, Category.assoc, bcChartInv_hom_id_assoc, sqBcInv_snd]
  have hθb : (bcChartOverIso A i hi ≪≫ (bcChartOverIso A j hj).symm).hom.left ≫
      bcChartHom A j hj = bcChartHom A i hi := by
    rw [hθl, Category.assoc, bcChartInv_hom_id, Category.comp_id]
  have hconj : sqBcInv A i hi ≫ (μ[(bcChart A i hi).asOver]).left ≫ bcChartHom A i hi =
      sqBcInv A j hj ≫ (μ[(bcChart A j hj).asOver]).left ≫ bcChartHom A j hj := by
    rw [← hθb, reassoc_of% hmulL, reassoc_of% hsq]
  have hfin := congrArg (· ≫ pullback.fst G.π O'.ι) hconj
  exact (bcChart_conjMul_fst A i hi).symm.trans (hfin.trans (bcChart_conjMul_fst A j hj))

/-- The per-chart multiplications agree on the overlaps of the atlas square cover. -/
theorem mulPiece_agree (i j : A.ι) :
    pullback.fst ((atlasSquareCover A).f i) ((atlasSquareCover A).f j) ≫ mulPiece A i =
      pullback.snd ((atlasSquareCover A).f i) ((atlasSquareCover A).f j) ≫ mulPiece A j := by
  simp only [atlasSquareCover_f]
  have hi : (A.U i).1 ⊓ (A.U j).1 ≤ (A.U i).1 := inf_le_left
  have hj : (A.U i).1 ⊓ (A.U j).1 ≤ (A.U j).1 := inf_le_right
  have hbij : (pullback.fst (pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι)
        (pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U j).1.ι) ≫
        pullback.snd (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι) ≫ (A.U i).1.ι =
      (pullback.snd (pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι)
        (pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U j).1.ι) ≫
        pullback.snd (pullback.fst G.π G.π ≫ G.π) (A.U j).1.ι) ≫ (A.U j).1.ι := by
    rw [Category.assoc, Category.assoc,
      ← pullback.condition (f := pullback.fst G.π G.π ≫ G.π) (g := (A.U i).1.ι),
      ← pullback.condition (f := pullback.fst G.π G.π ≫ G.π) (g := (A.U j).1.ι)]
    simp only [← Category.assoc]
    rw [pullback.condition (f := pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι)
        (g := pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U j).1.ι)]
  set b := (isPullback_opens_inf (A.U i).1 (A.U j).1).lift _ _ hbij with hb
  have hbfst : b ≫ S.homOfLE hi =
      pullback.fst (pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι)
        (pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U j).1.ι) ≫
        pullback.snd (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι :=
    (isPullback_opens_inf (A.U i).1 (A.U j).1).lift_fst _ _ _
  have hbsnd : b ≫ S.homOfLE hj =
      pullback.snd (pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι)
        (pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U j).1.ι) ≫
        pullback.snd (pullback.fst G.π G.π ≫ G.π) (A.U j).1.ι :=
    (isPullback_opens_inf (A.U i).1 (A.U j).1).lift_snd _ _ _
  have hab : (pullback.fst (pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι)
        (pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U j).1.ι) ≫
        pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι) ≫ (pullback.fst G.π G.π ≫ G.π) =
      b ≫ ((A.U i).1 ⊓ (A.U j).1).ι := by
    rw [Category.assoc, pullback.condition (f := pullback.fst G.π G.π ≫ G.π) (g := (A.U i).1.ι),
      ← Category.assoc, ← hbfst, Category.assoc, Scheme.homOfLE_ι]
  set w := pullback.lift _ b hab with hw
  have hwfst : w ≫ pullback.fst (pullback.fst G.π G.π ≫ G.π) ((A.U i).1 ⊓ (A.U j).1).ι =
      pullback.fst (pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι)
        (pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U j).1.ι) ≫
        pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι :=
    pullback.lift_fst _ _ _
  have hwsnd : w ≫ pullback.snd (pullback.fst G.π G.π ≫ G.π) ((A.U i).1 ⊓ (A.U j).1).ι = b :=
    pullback.lift_snd _ _ _
  have hwi : w ≫ sqChartRestr A i hi =
      pullback.fst (pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι)
        (pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U j).1.ι) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, sqChartRestr_fst, hwfst]
    · rw [Category.assoc, sqChartRestr_snd, ← Category.assoc, hwsnd, hbfst]
  have hwj : w ≫ sqChartRestr A j hj =
      pullback.snd (pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι)
        (pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U j).1.ι) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, sqChartRestr_fst, hwfst,
        pullback.condition (f := pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι)
          (g := pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U j).1.ι)]
    · rw [Category.assoc, sqChartRestr_snd, ← Category.assoc, hwsnd, hbsnd]
  exact (congrArg (· ≫ mulPiece A i) hwi.symm).trans <|
    (Category.assoc w (sqChartRestr A i hi) (mulPiece A i)).trans <|
    (congrArg (w ≫ ·) (chart_pair_mul_agree A i j hi hj)).trans <|
    (Category.assoc w (sqChartRestr A j hj) (mulPiece A j)).symm.trans <|
    congrArg (· ≫ mulPiece A j) hwj

/-- Multiplication glued from the per-chart model multiplications. -/
noncomputable def mulHomOf : pullback G.π G.π ⟶ G.E :=
  (atlasSquareCover A).glueMorphisms (mulPiece A) (mulPiece_agree A)

@[reassoc]
theorem mulHomOf_piece (i : A.ι) :
    (atlasSquareCover A).f i ≫ mulHomOf A = mulPiece A i :=
  (atlasSquareCover A).ι_glueMorphisms _ _ i

/-- Each multiplication piece is a morphism over `S`. -/
theorem mulPiece_π (i : A.ι) :
    mulPiece A i ≫ G.π =
      pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι ≫ (pullback.fst G.π G.π ≫ G.π) := by
  haveI := A.elliptic i
  rw [mulPiece]
  simp only [Category.assoc]
  rw [pullback.condition (f := G.π) (g := (A.U i).1.ι), bcChart_aux_inv_assoc,
    mulModelHom_π_assoc, ← Category.assoc, pullback.lift_fst]
  simp only [Category.assoc]
  rw [reassoc_of% (A.compat_π i), Iso.hom_inv_id_assoc, sqLift1_snd_assoc]
  exact (pullback.condition (f := pullback.fst G.π G.π ≫ G.π) (g := (A.U i).1.ι)).symm

set_option backward.isDefEq.respectTransparency false in
/-- **(chart-local multiplication)** `mulHomOf` applied to a pair of chart-`i` points — presented
as model points `um`, `vm` transported into `E` via `(A.e i).inv` — is the model multiplication
`mulModelHom (A.W i)` of `um`, `vm`, transported back into `E`. This single bridge turns every
glued group axiom into the corresponding model group law over `A.W i`. -/
private theorem mulHom_chart_pair (i : A.ι) :
    haveI := A.elliptic i
    ∀ {Z : Scheme.{u}} (um vm : Z ⟶ projModel (A.W i))
      (hum : um ≫ projModelπ (A.W i) = vm ≫ projModelπ (A.W i)),
      pullback.lift (um ≫ (A.e i).inv ≫ pullback.fst G.π (A.U i).1.ι)
          (vm ≫ (A.e i).inv ≫ pullback.fst G.π (A.U i).1.ι)
          (by
            simp only [Category.assoc]
            rw [pullback.condition (f := G.π) (g := (A.U i).1.ι), bcChart_aux_inv_assoc,
              reassoc_of% hum]) ≫ mulHomOf A =
        pullback.lift um vm hum ≫ mulModelHom (A.W i) ≫ (A.e i).inv ≫
          pullback.fst G.π (A.U i).1.ι := by
  haveI := A.elliptic i
  intro Z um vm hum
  have hc : (um ≫ (A.e i).inv ≫ pullback.fst G.π (A.U i).1.ι) ≫ G.π =
      (vm ≫ (A.e i).inv ≫ pullback.fst G.π (A.U i).1.ι) ≫ G.π := by
    simp only [Category.assoc]
    rw [pullback.condition (f := G.π) (g := (A.U i).1.ι), bcChart_aux_inv_assoc,
      reassoc_of% hum]
  have hst : pullback.lift (um ≫ (A.e i).inv ≫ pullback.fst G.π (A.U i).1.ι)
        (vm ≫ (A.e i).inv ≫ pullback.fst G.π (A.U i).1.ι) hc ≫ (pullback.fst G.π G.π ≫ G.π) =
      (um ≫ projModelπ (A.W i) ≫ (A.U i).2.isoSpec.inv) ≫ (A.U i).1.ι := by
    rw [← Category.assoc, pullback.lift_fst]
    simp only [Category.assoc]
    rw [pullback.condition (f := G.π) (g := (A.U i).1.ι), bcChart_aux_inv_assoc]
  set SQ := pullback.lift (pullback.lift (um ≫ (A.e i).inv ≫ pullback.fst G.π (A.U i).1.ι)
      (vm ≫ (A.e i).inv ≫ pullback.fst G.π (A.U i).1.ι) hc)
      (um ≫ projModelπ (A.W i) ≫ (A.U i).2.isoSpec.inv) hst with hSQ
  have hSQfst : SQ ≫ pullback.fst (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι =
      pullback.lift (um ≫ (A.e i).inv ≫ pullback.fst G.π (A.U i).1.ι)
        (vm ≫ (A.e i).inv ≫ pullback.fst G.π (A.U i).1.ι) hc := pullback.lift_fst _ _ _
  have hSQsnd : SQ ≫ pullback.snd (pullback.fst G.π G.π ≫ G.π) (A.U i).1.ι =
      um ≫ projModelπ (A.W i) ≫ (A.U i).2.isoSpec.inv := pullback.lift_snd _ _ _
  have hSQ1 : SQ ≫ sqLift1 A i = um ≫ (A.e i).inv := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, sqLift1_fst, ← Category.assoc, hSQfst, pullback.lift_fst,
        Category.assoc]
    · rw [Category.assoc, sqLift1_snd, hSQsnd, Category.assoc, bcChart_aux_inv]
  have hSQ2 : SQ ≫ sqLift2 A i = vm ≫ (A.e i).inv := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, sqLift2_fst, ← Category.assoc, hSQfst, pullback.lift_snd,
        Category.assoc]
    · rw [Category.assoc, sqLift2_snd, hSQsnd, Category.assoc, bcChart_aux_inv, reassoc_of% hum]
  have hMS : SQ ≫ pullback.lift (sqLift1 A i ≫ (A.e i).hom) (sqLift2 A i ≫ (A.e i).hom)
        ((sqLift1_hom_π A i).trans (sqLift2_hom_π A i).symm) = pullback.lift um vm hum := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hSQ1, Category.assoc,
        Iso.inv_hom_id, Category.comp_id, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hSQ2, Category.assoc,
        Iso.inv_hom_id, Category.comp_id, pullback.lift_snd]
  trans (SQ ≫ mulPiece A i)
  · rw [← mulHomOf_piece A i, atlasSquareCover_f, reassoc_of% hSQfst]
  · rw [mulPiece, reassoc_of% hMS]

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
  mulHomOf G.atlas

/-- **(T-W7.2-π)** Multiplication is a morphism over `S`. -/
@[reassoc]
theorem EllipticCurveGeom.mulHom_π :
    G.mulHom ≫ G.π = pullback.fst G.π G.π ≫ G.π := by
  show mulHomOf G.atlas ≫ G.π = pullback.fst G.π G.π ≫ G.π
  refine (atlasSquareCover G.atlas).hom_ext _ _ (fun i => ?_)
  exact (mulHomOf_piece_assoc G.atlas i G.π).trans
    ((mulPiece_π G.atlas i).trans
      (congrArg (· ≫ (pullback.fst G.π G.π ≫ G.π)) (atlasSquareCover_f G.atlas i)).symm)

/-- The unit of the glued group object: the zero section, as an `Over S`-morphism from the
monoidal unit. -/
private noncomputable def EllipticCurveGeom.oneHomG : 𝟙_ (Over S) ⟶ Over.mk G.π :=
  Over.homMk ((𝟙_ (Over S)).hom ≫ G.zero) <| by
    show ((𝟙_ (Over S)).hom ≫ G.zero) ≫ G.π = (𝟙_ (Over S)).hom
    rw [Category.assoc, G.zero_π, Category.comp_id]

/-- The multiplication of the glued group object, as an `Over S`-morphism. -/
private noncomputable def EllipticCurveGeom.mulHomG :
    Over.mk G.π ⊗ Over.mk G.π ⟶ Over.mk G.π :=
  Over.homMk G.mulHom G.mulHom_π

/-- The inverse of the glued group object, as an `Over S`-morphism. -/
private noncomputable def EllipticCurveGeom.invHomG : Over.mk G.π ⟶ Over.mk G.π :=
  Over.homMk G.negHom G.negHom_π

@[simp] private theorem EllipticCurveGeom.oneHomG_left :
    (G.oneHomG).left = (𝟙_ (Over S)).hom ≫ G.zero := rfl

@[simp] private theorem EllipticCurveGeom.mulHomG_left : (G.mulHomG).left = G.mulHom := rfl

@[simp] private theorem EllipticCurveGeom.invHomG_left : (G.invHomG).left = G.negHom := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem EllipticCurveGeom.grpObj_one_mul :
    G.oneHomG ▷ Over.mk G.π ≫ G.mulHomG = (λ_ (Over.mk G.π)).hom := by
  have key : CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.toUnit (Over.mk G.π) ≫ G.oneHomG) (𝟙 (Over.mk G.π)) ≫
      G.mulHomG = 𝟙 (Over.mk G.π) := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.lift_left, Over.toUnit_left, oneHomG_left, mulHomG_left,
      Over.id_left, overUnit_hom]
    show pullback.lift (G.π ≫ G.zero) (𝟙 G.E)
        (by rw [Category.assoc, G.zero_π, Category.comp_id, Category.id_comp]) ≫
      mulHomOf G.atlas = 𝟙 G.E
    refine (atlasTotalCover G.atlas).hom_ext _ _ (fun i => ?_)
    haveI := G.atlas.elliptic i
    have hz : projModelZero (G.atlas.W i) ≫ (G.atlas.e i).inv =
        (G.atlas.U i).2.isoSpec.inv ≫ zLift G.atlas i := by
      rw [← cancel_mono (G.atlas.e i).hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
        Category.assoc, zLift_totalIso, Iso.inv_hom_id_assoc]
    have hum : ((G.atlas.e i).hom ≫ projModelπ (G.atlas.W i) ≫ projModelZero (G.atlas.W i)) ≫
          projModelπ (G.atlas.W i) = (G.atlas.e i).hom ≫ projModelπ (G.atlas.W i) := by
      rw [Category.assoc, Category.assoc, projModelZero_projModelπ, Category.comp_id]
    have key := mulHom_chart_pair G.atlas i
      ((G.atlas.e i).hom ≫ projModelπ (G.atlas.W i) ≫ projModelZero (G.atlas.W i))
      (G.atlas.e i).hom hum
    have hlift_e : pullback.lift ((G.atlas.e i).hom ≫ projModelπ (G.atlas.W i) ≫
          projModelZero (G.atlas.W i)) (G.atlas.e i).hom hum =
        (G.atlas.e i).hom ≫ pullback.lift (projModelπ (G.atlas.W i) ≫ projModelZero (G.atlas.W i))
          (𝟙 (projModel (G.atlas.W i)))
          (by rw [Category.assoc, projModelZero_projModelπ, Category.comp_id,
            Category.id_comp]) := by
      refine pullback.hom_ext ?_ ?_
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id]
    have hL : pullback.fst G.π (G.atlas.U i).1.ι ≫ pullback.lift (G.π ≫ G.zero) (𝟙 G.E)
          (by rw [Category.assoc, G.zero_π, Category.comp_id, Category.id_comp]) =
        pullback.lift (((G.atlas.e i).hom ≫ projModelπ (G.atlas.W i) ≫
            projModelZero (G.atlas.W i)) ≫ (G.atlas.e i).inv ≫ pullback.fst G.π (G.atlas.U i).1.ι)
          ((G.atlas.e i).hom ≫ (G.atlas.e i).inv ≫ pullback.fst G.π (G.atlas.U i).1.ι)
          (by simp only [Category.assoc]
              rw [pullback.condition (f := G.π) (g := (G.atlas.U i).1.ι), bcChart_aux_inv_assoc,
                reassoc_of% hum]) := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
        simp only [Category.assoc]
        rw [reassoc_of% (G.atlas.compat_π i), reassoc_of% hz, Iso.hom_inv_id_assoc, zLift_fst,
          reassoc_of% (pullback.condition (f := G.π) (g := (G.atlas.U i).1.ι))]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id,
          Iso.hom_inv_id_assoc]
    rw [atlasTotalCover_f, ← Category.assoc, hL, key, hlift_e, Category.assoc,
      reassoc_of% (model_one_mul_lift (G.atlas.W i)), Iso.hom_inv_id_assoc, Category.comp_id]
  have hlu : CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.toUnit (Over.mk G.π) ≫ G.oneHomG) (𝟙 (Over.mk G.π)) =
      (λ_ (Over.mk G.π)).inv ≫ (G.oneHomG ▷ Over.mk G.π) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp
  have hk : (λ_ (Over.mk G.π)).inv ≫ G.oneHomG ▷ Over.mk G.π ≫ G.mulHomG = 𝟙 (Over.mk G.π) := by
    rw [← Category.assoc, ← hlu]; exact key
  calc G.oneHomG ▷ Over.mk G.π ≫ G.mulHomG
      = (λ_ (Over.mk G.π)).hom ≫ (λ_ (Over.mk G.π)).inv ≫ G.oneHomG ▷ Over.mk G.π ≫ G.mulHomG := by
        rw [Iso.hom_inv_id_assoc]
    _ = (λ_ (Over.mk G.π)).hom := by rw [hk, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem EllipticCurveGeom.grpObj_mul_one :
    Over.mk G.π ◁ G.oneHomG ≫ G.mulHomG = (ρ_ (Over.mk G.π)).hom := by
  have key : CartesianMonoidalCategory.lift (𝟙 (Over.mk G.π))
        (CartesianMonoidalCategory.toUnit (Over.mk G.π) ≫ G.oneHomG) ≫
      G.mulHomG = 𝟙 (Over.mk G.π) := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.lift_left, Over.toUnit_left, oneHomG_left, mulHomG_left,
      Over.id_left, overUnit_hom]
    show pullback.lift (𝟙 G.E) (G.π ≫ G.zero)
        (by rw [Category.id_comp, Category.assoc, G.zero_π, Category.comp_id]) ≫
      mulHomOf G.atlas = 𝟙 G.E
    refine (atlasTotalCover G.atlas).hom_ext _ _ (fun i => ?_)
    haveI := G.atlas.elliptic i
    have hz : projModelZero (G.atlas.W i) ≫ (G.atlas.e i).inv =
        (G.atlas.U i).2.isoSpec.inv ≫ zLift G.atlas i := by
      rw [← cancel_mono (G.atlas.e i).hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
        Category.assoc, zLift_totalIso, Iso.inv_hom_id_assoc]
    have hum : (G.atlas.e i).hom ≫ projModelπ (G.atlas.W i) =
        ((G.atlas.e i).hom ≫ projModelπ (G.atlas.W i) ≫ projModelZero (G.atlas.W i)) ≫
          projModelπ (G.atlas.W i) := by
      rw [Category.assoc, Category.assoc, projModelZero_projModelπ, Category.comp_id]
    have key := mulHom_chart_pair G.atlas i (G.atlas.e i).hom
      ((G.atlas.e i).hom ≫ projModelπ (G.atlas.W i) ≫ projModelZero (G.atlas.W i)) hum
    have hlift_e : pullback.lift (G.atlas.e i).hom ((G.atlas.e i).hom ≫ projModelπ (G.atlas.W i) ≫
          projModelZero (G.atlas.W i)) hum =
        (G.atlas.e i).hom ≫ pullback.lift (𝟙 (projModel (G.atlas.W i)))
          (projModelπ (G.atlas.W i) ≫ projModelZero (G.atlas.W i))
          (by rw [Category.id_comp, Category.assoc, projModelZero_projModelπ,
            Category.comp_id]) := by
      refine pullback.hom_ext ?_ ?_
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, Category.comp_id]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
    have hL : pullback.fst G.π (G.atlas.U i).1.ι ≫ pullback.lift (𝟙 G.E) (G.π ≫ G.zero)
          (by rw [Category.id_comp, Category.assoc, G.zero_π, Category.comp_id]) =
        pullback.lift ((G.atlas.e i).hom ≫ (G.atlas.e i).inv ≫ pullback.fst G.π (G.atlas.U i).1.ι)
          (((G.atlas.e i).hom ≫ projModelπ (G.atlas.W i) ≫ projModelZero (G.atlas.W i)) ≫
            (G.atlas.e i).inv ≫ pullback.fst G.π (G.atlas.U i).1.ι)
          (by simp only [Category.assoc]
              rw [pullback.condition (f := G.π) (g := (G.atlas.U i).1.ι), bcChart_aux_inv_assoc,
                reassoc_of% hum]) := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.comp_id,
          Iso.hom_inv_id_assoc]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
        simp only [Category.assoc]
        rw [reassoc_of% (G.atlas.compat_π i), reassoc_of% hz, Iso.hom_inv_id_assoc, zLift_fst,
          reassoc_of% (pullback.condition (f := G.π) (g := (G.atlas.U i).1.ι))]
    rw [atlasTotalCover_f, ← Category.assoc, hL, key, hlift_e, Category.assoc,
      reassoc_of% (model_mul_one_lift (G.atlas.W i)), Iso.hom_inv_id_assoc, Category.comp_id]
  have hru : CartesianMonoidalCategory.lift (𝟙 (Over.mk G.π))
        (CartesianMonoidalCategory.toUnit (Over.mk G.π) ≫ G.oneHomG) =
      (ρ_ (Over.mk G.π)).inv ≫ (Over.mk G.π ◁ G.oneHomG) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp
  have hk : (ρ_ (Over.mk G.π)).inv ≫ Over.mk G.π ◁ G.oneHomG ≫ G.mulHomG = 𝟙 (Over.mk G.π) := by
    rw [← Category.assoc, ← hru]; exact key
  calc Over.mk G.π ◁ G.oneHomG ≫ G.mulHomG
      = (ρ_ (Over.mk G.π)).hom ≫ (ρ_ (Over.mk G.π)).inv ≫ Over.mk G.π ◁ G.oneHomG ≫ G.mulHomG := by
        rw [Iso.hom_inv_id_assoc]
    _ = (ρ_ (Over.mk G.π)).hom := by rw [hk, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem EllipticCurveGeom.grpObj_mul_assoc :
    (G.mulHomG ▷ Over.mk G.π) ≫ G.mulHomG =
      (α_ (Over.mk G.π) (Over.mk G.π) (Over.mk G.π)).hom ≫
        (Over.mk G.π ◁ G.mulHomG) ≫ G.mulHomG := by
  have hLHS' : G.mulHomG ▷ Over.mk G.π =
      CartesianMonoidalCategory.lift (CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst _ _ ≫ CartesianMonoidalCategory.fst _ _)
        (CartesianMonoidalCategory.fst _ _ ≫ CartesianMonoidalCategory.snd _ _) ≫ G.mulHomG)
        (CartesianMonoidalCategory.snd _ _) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hα : (α_ (Over.mk G.π) (Over.mk G.π) (Over.mk G.π)).hom =
      CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst _ _ ≫ CartesianMonoidalCategory.fst _ _)
        (CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.fst _ _ ≫ CartesianMonoidalCategory.snd _ _)
          (CartesianMonoidalCategory.snd _ _)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · apply CartesianMonoidalCategory.hom_ext <;> simp
  have hRHS' : (α_ (Over.mk G.π) (Over.mk G.π) (Over.mk G.π)).hom ≫ Over.mk G.π ◁ G.mulHomG =
      CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst _ _ ≫ CartesianMonoidalCategory.fst _ _)
        (CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.fst _ _ ≫ CartesianMonoidalCategory.snd _ _)
          (CartesianMonoidalCategory.snd _ _) ≫ G.mulHomG) := by
    rw [hα, CartesianMonoidalCategory.lift_whiskerLeft]
  rw [hLHS', ← Category.assoc, hRHS']
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.lift_left, mulHomG_left, Over.fst_left, Over.snd_left,
    Over.tensorObj_hom]
  show pullback.lift (pullback.lift
        (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫ pullback.fst G.π G.π)
        (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫ pullback.snd G.π G.π) _ ≫ mulHomOf G.atlas)
      (pullback.snd (pullback.fst G.π G.π ≫ G.π) G.π) _ ≫ mulHomOf G.atlas =
    pullback.lift (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫ pullback.fst G.π G.π)
      (pullback.lift (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫ pullback.snd G.π G.π)
        (pullback.snd (pullback.fst G.π G.π ≫ G.π) G.π) _ ≫ mulHomOf G.atlas) _ ≫ mulHomOf G.atlas
  refine (atlasCubeCover G.atlas).hom_ext _ _ (fun (i : G.atlas.ι) => ?_)
  haveI := G.atlas.elliptic i
  rw [atlasCubeCover_f]
  -- The three cube legs, composed with the cube-chart embedding `c`, land over chart `i`.
  have hcA : (pullback.fst (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫
        pullback.fst G.π G.π ≫ G.π) (G.atlas.U i).1.ι ≫
        (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫ pullback.fst G.π G.π)) ≫ G.π =
      pullback.snd (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫ pullback.fst G.π G.π ≫ G.π)
        (G.atlas.U i).1.ι ≫ (G.atlas.U i).1.ι := by
    rw [Category.assoc, Category.assoc]
    exact pullback.condition
  have hcB : (pullback.fst (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫
        pullback.fst G.π G.π ≫ G.π) (G.atlas.U i).1.ι ≫
        (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫ pullback.snd G.π G.π)) ≫ G.π =
      pullback.snd (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫ pullback.fst G.π G.π ≫ G.π)
        (G.atlas.U i).1.ι ≫ (G.atlas.U i).1.ι := by
    rw [Category.assoc, Category.assoc, ← pullback.condition (f := G.π) (g := G.π)]
    exact pullback.condition
  have hcC : (pullback.fst (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫
        pullback.fst G.π G.π ≫ G.π) (G.atlas.U i).1.ι ≫
        pullback.snd (pullback.fst G.π G.π ≫ G.π) G.π) ≫ G.π =
      pullback.snd (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫ pullback.fst G.π G.π ≫ G.π)
        (G.atlas.U i).1.ι ≫ (G.atlas.U i).1.ι := by
    rw [Category.assoc, ← pullback.condition (f := pullback.fst G.π G.π ≫ G.π) (g := G.π)]
    exact pullback.condition
  -- The three model points obtained by transporting the embedded legs through the chart iso.
  set uA := pullback.lift (pullback.fst (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫
      pullback.fst G.π G.π ≫ G.π) (G.atlas.U i).1.ι ≫
      (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫ pullback.fst G.π G.π))
      (pullback.snd (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫ pullback.fst G.π G.π ≫ G.π)
        (G.atlas.U i).1.ι) hcA ≫ (G.atlas.e i).hom with huA
  set uB := pullback.lift (pullback.fst (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫
      pullback.fst G.π G.π ≫ G.π) (G.atlas.U i).1.ι ≫
      (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫ pullback.snd G.π G.π))
      (pullback.snd (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫ pullback.fst G.π G.π ≫ G.π)
        (G.atlas.U i).1.ι) hcB ≫ (G.atlas.e i).hom with huB
  set uC := pullback.lift (pullback.fst (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫
      pullback.fst G.π G.π ≫ G.π) (G.atlas.U i).1.ι ≫
      pullback.snd (pullback.fst G.π G.π ≫ G.π) G.π)
      (pullback.snd (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫ pullback.fst G.π G.π ≫ G.π)
        (G.atlas.U i).1.ι) hcC ≫ (G.atlas.e i).hom with huC
  -- Per-leg identity: embedded leg = model point transported back into `E`.
  have hpA : pullback.fst (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫
        pullback.fst G.π G.π ≫ G.π) (G.atlas.U i).1.ι ≫
        (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫ pullback.fst G.π G.π) =
      uA ≫ (G.atlas.e i).inv ≫ pullback.fst G.π (G.atlas.U i).1.ι := by
    rw [huA, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst]
  have hpB : pullback.fst (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫
        pullback.fst G.π G.π ≫ G.π) (G.atlas.U i).1.ι ≫
        (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫ pullback.snd G.π G.π) =
      uB ≫ (G.atlas.e i).inv ≫ pullback.fst G.π (G.atlas.U i).1.ι := by
    rw [huB, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst]
  have hpC : pullback.fst (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫
        pullback.fst G.π G.π ≫ G.π) (G.atlas.U i).1.ι ≫
        pullback.snd (pullback.fst G.π G.π ≫ G.π) G.π =
      uC ≫ (G.atlas.e i).inv ≫ pullback.fst G.π (G.atlas.U i).1.ι := by
    rw [huC, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst]
  -- π-compatibility of the three model points (all equal `cs ≫ isoSpec.hom`).
  have hπA : uA ≫ projModelπ (G.atlas.W i) =
      pullback.snd (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫ pullback.fst G.π G.π ≫ G.π)
        (G.atlas.U i).1.ι ≫ (G.atlas.U i).2.isoSpec.hom := by
    rw [huA, Category.assoc, G.atlas.compat_π i]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (G.atlas.U i).2.isoSpec.hom) (pullback.lift_snd _ _ _))
  have hπB : uB ≫ projModelπ (G.atlas.W i) =
      pullback.snd (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫ pullback.fst G.π G.π ≫ G.π)
        (G.atlas.U i).1.ι ≫ (G.atlas.U i).2.isoSpec.hom := by
    rw [huB, Category.assoc, G.atlas.compat_π i]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (G.atlas.U i).2.isoSpec.hom) (pullback.lift_snd _ _ _))
  have hπC : uC ≫ projModelπ (G.atlas.W i) =
      pullback.snd (pullback.fst (pullback.fst G.π G.π ≫ G.π) G.π ≫ pullback.fst G.π G.π ≫ G.π)
        (G.atlas.U i).1.ι ≫ (G.atlas.U i).2.isoSpec.hom := by
    rw [huC, Category.assoc, G.atlas.compat_π i]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (G.atlas.U i).2.isoSpec.hom) (pullback.lift_snd _ _ _))
  have hAB := hπA.trans hπB.symm
  have hBC := hπB.trans hπC.symm
  clear_value uA uB uC
  have hC : (pullback.lift uA uB hAB ≫ mulModelHom (G.atlas.W i)) ≫ projModelπ (G.atlas.W i) =
      uC ≫ projModelπ (G.atlas.W i) := by
    rw [Category.assoc, mulModelHom_π]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ projModelπ (G.atlas.W i)) (pullback.lift_fst _ _ _)).trans (hAB.trans hBC))
  have hC' : uA ≫ projModelπ (G.atlas.W i) =
      (pullback.lift uB uC hBC ≫ mulModelHom (G.atlas.W i)) ≫ projModelπ (G.atlas.W i) := by
    rw [Category.assoc, mulModelHom_π]
    exact hAB.trans
      ((congrArg (· ≫ projModelπ (G.atlas.W i)) (pullback.lift_fst _ _ _)).symm.trans
        (Category.assoc _ _ _))
  -- Distribute the cube-chart embedding through a `pullback.lift ≫ mulHomOf`.
  have dist : ∀ {V : Scheme.{u}} (f : V ⟶ pullback (pullback.fst G.π G.π ≫ G.π) G.π)
      (P Q : pullback (pullback.fst G.π G.π ≫ G.π) G.π ⟶ G.E) (hPQ : P ≫ G.π = Q ≫ G.π),
      f ≫ pullback.lift P Q hPQ ≫ mulHomOf G.atlas =
        pullback.lift (f ≫ P) (f ≫ Q)
          (by rw [Category.assoc, hPQ, Category.assoc]) ≫ mulHomOf G.atlas := by
    intro V f P Q hPQ
    rw [← Category.assoc]
    exact congrArg (· ≫ mulHomOf G.atlas)
      (pullback.hom_ext (by simp only [Category.assoc, pullback.lift_fst])
        (by simp only [Category.assoc, pullback.lift_snd]))
  -- Distribute the cube embedding through both nested lifts (`simp` copes with the dependent
  -- `pullback.lift` proofs where `rw` cannot), substitute the per-leg identities, then bridge
  -- both inner and outer chart-pairs to `mulModelHom` via `mulHom_chart_pair`.
  simp only [dist, hpA, hpB, hpC, mulHom_chart_pair G.atlas i uA uB hAB,
    mulHom_chart_pair G.atlas i uB uC hBC,
    ← Category.assoc (pullback.lift uA uB hAB) (mulModelHom (G.atlas.W i)),
    ← Category.assoc (pullback.lift uB uC hBC) (mulModelHom (G.atlas.W i)),
    mulHom_chart_pair G.atlas i (pullback.lift uA uB hAB ≫ mulModelHom (G.atlas.W i)) uC hC,
    mulHom_chart_pair G.atlas i uA (pullback.lift uB uC hBC ≫ mulModelHom (G.atlas.W i)) hC']
  -- The goal is now the model associativity law, transported back into `E` via `(A.e i).inv`.
  rw [reassoc_of% (model_mul_assoc_lift (G.atlas.W i) uA uB uC hAB hBC)]

set_option backward.isDefEq.respectTransparency false in
private theorem EllipticCurveGeom.grpObj_left_inv :
    CartesianMonoidalCategory.lift G.invHomG (𝟙 (Over.mk G.π)) ≫ G.mulHomG =
      CartesianMonoidalCategory.toUnit (Over.mk G.π) ≫ G.oneHomG := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.lift_left, Over.toUnit_left, oneHomG_left, mulHomG_left,
    invHomG_left, Over.id_left]
  show pullback.lift G.negHom (𝟙 G.E) _ ≫ mulHomOf G.atlas = G.π ≫ (𝟙_ (Over S)).hom ≫ G.zero
  refine (atlasTotalCover G.atlas).hom_ext _ _ (fun i => ?_)
  haveI := G.atlas.elliptic i
  have hum : ((G.atlas.e i).hom ≫ negModelHom (G.atlas.W i)) ≫ projModelπ (G.atlas.W i) =
      (G.atlas.e i).hom ≫ projModelπ (G.atlas.W i) := by rw [Category.assoc, negModelHom_π]
  have key := mulHom_chart_pair G.atlas i ((G.atlas.e i).hom ≫ negModelHom (G.atlas.W i))
    (G.atlas.e i).hom hum
  have hmodel : pullback.lift (negModelHom (G.atlas.W i)) (𝟙 (projModel (G.atlas.W i)))
        (by rw [negModelHom_π, Category.id_comp]) ≫ mulModelHom (G.atlas.W i) =
      projModelπ (G.atlas.W i) ≫ projModelZero (G.atlas.W i) := by
    have h := congrArg CommaMorphism.left (invOver_mulOver (G.atlas.W i))
    simp only [Over.comp_left, Over.lift_left, Over.toUnit_left, mulOver_left, oneOver_left,
      invOver_left, Over.id_left, overUnit_hom] at h
    rw [← Category.id_comp (projModelZero (G.atlas.W i))]
    exact h
  have hz : projModelZero (G.atlas.W i) ≫ (G.atlas.e i).inv =
      (G.atlas.U i).2.isoSpec.inv ≫ zLift G.atlas i := by
    rw [← cancel_mono (G.atlas.e i).hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Category.assoc, zLift_totalIso, Iso.inv_hom_id_assoc]
  have hlift_e : pullback.lift ((G.atlas.e i).hom ≫ negModelHom (G.atlas.W i)) (G.atlas.e i).hom
        hum = (G.atlas.e i).hom ≫ pullback.lift (negModelHom (G.atlas.W i))
        (𝟙 (projModel (G.atlas.W i))) (by rw [negModelHom_π, Category.id_comp]) := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id]
  have hL : pullback.fst G.π (G.atlas.U i).1.ι ≫ pullback.lift G.negHom (𝟙 G.E)
        (by rw [G.negHom_π, Category.id_comp]) =
      pullback.lift (((G.atlas.e i).hom ≫ negModelHom (G.atlas.W i)) ≫ (G.atlas.e i).inv ≫
          pullback.fst G.π (G.atlas.U i).1.ι)
        ((G.atlas.e i).hom ≫ (G.atlas.e i).inv ≫ pullback.fst G.π (G.atlas.U i).1.ι)
        (by simp only [Category.assoc]
            rw [pullback.condition (f := G.π) (g := (G.atlas.U i).1.ι), bcChart_aux_inv_assoc,
              reassoc_of% hum]) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      exact negHomOf_piece' G.atlas i
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id, ← Category.assoc,
        Iso.hom_inv_id, Category.id_comp]
  rw [atlasTotalCover_f, ← Category.assoc (pullback.fst G.π (G.atlas.U i).1.ι), hL, key, hlift_e,
    Category.assoc, reassoc_of% hmodel, reassoc_of% (G.atlas.compat_π i), reassoc_of% hz,
    Iso.hom_inv_id_assoc, zLift_fst, overUnit_hom, Category.id_comp,
    reassoc_of% (pullback.condition (f := G.π) (g := (G.atlas.U i).1.ι))]

set_option backward.isDefEq.respectTransparency false in
private theorem EllipticCurveGeom.grpObj_right_inv :
    CartesianMonoidalCategory.lift (𝟙 (Over.mk G.π)) G.invHomG ≫ G.mulHomG =
      CartesianMonoidalCategory.toUnit (Over.mk G.π) ≫ G.oneHomG := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.lift_left, Over.toUnit_left, oneHomG_left, mulHomG_left,
    invHomG_left, Over.id_left]
  show pullback.lift (𝟙 G.E) G.negHom _ ≫ mulHomOf G.atlas = G.π ≫ (𝟙_ (Over S)).hom ≫ G.zero
  refine (atlasTotalCover G.atlas).hom_ext _ _ (fun i => ?_)
  haveI := G.atlas.elliptic i
  have hum : (G.atlas.e i).hom ≫ projModelπ (G.atlas.W i) =
      ((G.atlas.e i).hom ≫ negModelHom (G.atlas.W i)) ≫ projModelπ (G.atlas.W i) := by
    rw [Category.assoc, negModelHom_π]
  have key := mulHom_chart_pair G.atlas i (G.atlas.e i).hom
    ((G.atlas.e i).hom ≫ negModelHom (G.atlas.W i)) hum
  have hmodel : pullback.lift (𝟙 (projModel (G.atlas.W i))) (negModelHom (G.atlas.W i))
        (by rw [Category.id_comp, negModelHom_π]) ≫ mulModelHom (G.atlas.W i) =
      projModelπ (G.atlas.W i) ≫ projModelZero (G.atlas.W i) := by
    letI := modelGrpObj (G.atlas.W i)
    have h := congrArg CommaMorphism.left (GrpObj.right_inv (modelOver (G.atlas.W i)))
    simp only [Over.comp_left, Over.lift_left, Over.toUnit_left, mulOver_left, oneOver_left,
      invOver_left, Over.id_left, overUnit_hom] at h
    rw [← Category.id_comp (projModelZero (G.atlas.W i))]
    exact h
  have hz : projModelZero (G.atlas.W i) ≫ (G.atlas.e i).inv =
      (G.atlas.U i).2.isoSpec.inv ≫ zLift G.atlas i := by
    rw [← cancel_mono (G.atlas.e i).hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Category.assoc, zLift_totalIso, Iso.inv_hom_id_assoc]
  have hlift_e : pullback.lift (G.atlas.e i).hom ((G.atlas.e i).hom ≫ negModelHom (G.atlas.W i))
        hum = (G.atlas.e i).hom ≫ pullback.lift (𝟙 (projModel (G.atlas.W i)))
        (negModelHom (G.atlas.W i)) (by rw [Category.id_comp, negModelHom_π]) := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, Category.comp_id]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
  have hL : pullback.fst G.π (G.atlas.U i).1.ι ≫ pullback.lift (𝟙 G.E) G.negHom
        (by rw [Category.id_comp, G.negHom_π]) =
      pullback.lift ((G.atlas.e i).hom ≫ (G.atlas.e i).inv ≫
          pullback.fst G.π (G.atlas.U i).1.ι)
        (((G.atlas.e i).hom ≫ negModelHom (G.atlas.W i)) ≫ (G.atlas.e i).inv ≫
          pullback.fst G.π (G.atlas.U i).1.ι)
        (by simp only [Category.assoc]
            rw [pullback.condition (f := G.π) (g := (G.atlas.U i).1.ι), bcChart_aux_inv_assoc,
              reassoc_of% hum]) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.comp_id, ← Category.assoc,
        Iso.hom_inv_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
      exact negHomOf_piece' G.atlas i
  rw [atlasTotalCover_f, ← Category.assoc (pullback.fst G.π (G.atlas.U i).1.ι), hL, key, hlift_e,
    Category.assoc, reassoc_of% hmodel, reassoc_of% (G.atlas.compat_π i), reassoc_of% hz,
    Iso.hom_inv_id_assoc, zLift_fst, overUnit_hom, Category.id_comp,
    reassoc_of% (pullback.condition (f := G.π) (g := (G.atlas.U i).1.ι))]

/-- **(T-W7.3 → T-W7.6, the packaged group object)** The group-object structure on
`E/S` in `Over S`: multiplication and inverse glued above, unit the zero section; every
axiom holds because it holds per chart (base change of the model identity of
`GroupLawConstruction`) and morphism equality is chart-local (`Cover.hom_ext`). -/
@[reducible] noncomputable def EllipticCurveGeom.grpObj : GrpObj (Over.mk G.π) where
  one := G.oneHomG
  mul := G.mulHomG
  inv := G.invHomG
  one_mul := G.grpObj_one_mul
  mul_one := G.grpObj_mul_one
  mul_assoc := G.grpObj_mul_assoc
  left_inv := G.grpObj_left_inv
  right_inv := G.grpObj_right_inv

set_option backward.isDefEq.respectTransparency false in
/-- **(T-W7.6-comm)** The glued structure is commutative (per chart: `mulOver_comm`). -/
theorem EllipticCurveGeom.grpObj_isCommMonObj :
    letI := G.grpObj
    IsCommMonObj (Over.mk G.π) := by
  letI := G.grpObj
  refine ⟨?_⟩
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.braiding_hom_left]
  show (pullbackSymmetry G.π G.π).hom ≫ mulHomOf G.atlas = mulHomOf G.atlas
  refine (atlasSquareCover G.atlas).hom_ext _ _ (fun i => ?_)
  haveI := G.atlas.elliptic i
  have hum : (sqLift2 G.atlas i ≫ (G.atlas.e i).hom) ≫ projModelπ (G.atlas.W i) =
      (sqLift1 G.atlas i ≫ (G.atlas.e i).hom) ≫ projModelπ (G.atlas.W i) := by
    rw [sqLift2_hom_π, sqLift1_hom_π]
  have key := mulHom_chart_pair G.atlas i (sqLift2 G.atlas i ≫ (G.atlas.e i).hom)
    (sqLift1 G.atlas i ≫ (G.atlas.e i).hom) hum
  have hswap : pullback.fst (pullback.fst G.π G.π ≫ G.π) (G.atlas.U i).1.ι ≫
        (pullbackSymmetry G.π G.π).hom =
      pullback.lift ((sqLift2 G.atlas i ≫ (G.atlas.e i).hom) ≫ (G.atlas.e i).inv ≫
          pullback.fst G.π (G.atlas.U i).1.ι)
        ((sqLift1 G.atlas i ≫ (G.atlas.e i).hom) ≫ (G.atlas.e i).inv ≫
          pullback.fst G.π (G.atlas.U i).1.ι)
        (by simp only [Category.assoc]
            rw [pullback.condition (f := G.π) (g := (G.atlas.U i).1.ι), bcChart_aux_inv_assoc,
              reassoc_of% hum]) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullbackSymmetry_hom_comp_fst, pullback.lift_fst, Category.assoc,
        Iso.hom_inv_id_assoc, sqLift2_fst]
    · rw [Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.lift_snd, Category.assoc,
        Iso.hom_inv_id_assoc, sqLift1_fst]
  have hcomm : pullback.lift (sqLift2 G.atlas i ≫ (G.atlas.e i).hom)
        (sqLift1 G.atlas i ≫ (G.atlas.e i).hom) hum ≫ mulModelHom (G.atlas.W i) =
      pullback.lift (sqLift1 G.atlas i ≫ (G.atlas.e i).hom)
        (sqLift2 G.atlas i ≫ (G.atlas.e i).hom)
        ((sqLift1_hom_π G.atlas i).trans (sqLift2_hom_π G.atlas i).symm) ≫
        mulModelHom (G.atlas.W i) := by
    conv_rhs => rw [← mulModelHom_comm (G.atlas.W i)]
    rw [← Category.assoc]
    congr 1
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, pullbackSymmetry_hom_comp_fst, pullback.lift_snd]
    · rw [pullback.lift_snd, Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.lift_fst]
  rw [atlasSquareCover_f, ← Category.assoc, hswap, key, reassoc_of% hcomm]
  conv_rhs => rw [← atlasSquareCover_f, mulHomOf_piece, mulPiece]

/-- **(T-W7.6-one)** The unit of the glued structure is the zero section. -/
theorem EllipticCurveGeom.grpObj_one_eq_zero :
    letI := G.grpObj
    (η[Over.mk G.π] : _ ⟶ Over.mk G.π).left = (𝟙_ (Over S)).hom ≫ G.zero :=
  rfl

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

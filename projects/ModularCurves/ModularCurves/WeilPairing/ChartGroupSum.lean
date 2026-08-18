/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.ModelRecord
import ModularCurves.EllipticCurve.RecordGroupUnique
import ModularCurves.WeilPairing.ChartFromUniversalPair

/-!
# The Weierstrass chart isomorphism is a group isomorphism (B3-step5b)

`WeilPairing/ChartFromUniversalPair.lean` reduced the relative theorem of the square over an
arbitrary base to a single hypothesis, `IsSquareIdentity.of_forall_chart_sum`'s `hsum`: that
the Weierstrass chart isomorphism of `LocallyWeierstrass` carries the third section to the
`mulModelHom`-**sum** of the first two.

`hsum` is stated there for a *bare* morphism `f : Y ⟶ T` with four *bare* sections
`P Q R Z`, where it is of course not provable — `R` is arbitrary. It becomes provable exactly
when `f` carries an elliptic-curve **working record** and `R` is the group sum `P + Q` of the
first two sections. That is what this file supplies, over an arbitrary base:

* `point_add_val_of_pointedIso` — **the group-theoretic core.** A *pointed* isomorphism of
  working records over a fixed base carries point addition to point addition. This is
  `isMonHom_of_pointedIso_records` (`EllipticCurve/RecordGroupUnique.lean`, proved over an
  arbitrary base via `grpObj_mul_unique` / `modelGrpObj_unique`, and *not* gated on the
  sorried `abelEnrichment_unique`) read on `T`-points through `pointEquivOverHom`.
* `point_add_val_restrict` — point addition commutes with restriction along a base morphism.
* `chartSumLegIso`, `chartSumPoint`, `chartSumPoint_legIso` — the plumbing that presents an
  affine chart `V` of the base as the base change of the record along
  `chartSumBase V : Spec Γ(S, V) ⟶ S`, and identifies the base change of a section with the
  `secBC` restriction that `of_forall_chart_sum` speaks about.
* `chartSumPoint_add_val` — that presentation is additive on points (`Point.baseChangeEquiv`
  is an `AddEquiv`, and `point_add_val_restrict` handles the restriction half).
* `chartSumRecordIso`, `chartSumRecordIso_one` — **the chart isomorphism packaged as a pointed
  isomorphism of working records** `(E.baseChange (chartSumBase V)).asOver ≅
  (modelEllipticCurve W).asOver`. Pointedness is exactly the `hez` hypothesis of
  `of_forall_chart_sum`.
* `chartSum_secBC_add` — **the sub-leaf**: `hsum` for a working record. Composed from the four
  previous items plus `modelEllipticCurve_point_add_val` (`EllipticCurve/ModelRecord.lean`),
  which says that point addition on the model record *computes* as `mulModelHom`.
* `isSquareIdentity_point_add` — **the result**: the relative theorem of the square for an
  elliptic-curve working record over an arbitrary base, with the third section the group sum
  of the first two. `of_forall_chart_sum` with every hypothesis discharged.

Nothing here needs the base to be reduced or Noetherian: that gap was closed upstream by
`IsSquareIdentity.of_projModel'`, and the group-isomorphism primitive
`isMonHom_of_pointedIso_records` is already an arbitrary-base statement.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace ModularCurves

section Points

variable {S : Scheme.{u}}

/-! ### Point addition through a pointed isomorphism of working records -/

private theorem lift_left_fst (E : EllipticCurve S) {T : Scheme.{u}} (g : T ⟶ S)
    (a b : E.Point g) :
    (lift (E.pointEquivOverHom g a) (E.pointEquivOverHom g b)).left ≫
      pullback.fst E.π E.π = a.1 :=
  (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left (lift_fst _ _))

private theorem lift_left_snd (E : EllipticCurve S) {T : Scheme.{u}} (g : T ⟶ S)
    (a b : E.Point g) :
    (lift (E.pointEquivOverHom g a) (E.pointEquivOverHom g b)).left ≫
      pullback.snd E.π E.π = b.1 :=
  (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left (lift_snd _ _))

/-- The underlying morphism of a point sum, in `lift … ≫ μ` form. -/
private theorem point_add_val_eq (E : EllipticCurve S) {T : Scheme.{u}} (g : T ⟶ S)
    (a b : E.Point g) :
    (a + b).1 =
      (lift (E.pointEquivOverHom g a) (E.pointEquivOverHom g b)).left ≫ (μ[E.asOver]).left :=
  (congrArg CommaMorphism.left (E.pointEquivOverHom_add g a b)).trans
    (Over.comp_left _ _ _ _ _)

/-- **[B3-step5b, the group-theoretic core] Point addition transports along a pointed
isomorphism of working records.** The records-level canonicity primitive
`isMonHom_of_pointedIso_records` says a pointed isomorphism of working records is a
homomorphism of their group structures over an arbitrary base; reading that on `T`-points
through `pointEquivOverHom` (whose transport of addition is `lift … ≫ μ`) is this statement. -/
theorem point_add_val_of_pointedIso (E E' : EllipticCurve S) (α : E.asOver ≅ E'.asOver)
    (hη : (η[E.asOver] : 𝟙_ (Over S) ⟶ E.asOver) ≫ α.hom = η[E'.asOver])
    {T : Scheme.{u}} (g : T ⟶ S) (P Q : E.Point g) (P' Q' : E'.Point g)
    (hP : P.1 ≫ α.hom.left = P'.1) (hQ : Q.1 ≫ α.hom.left = Q'.1) :
    (P + Q).1 ≫ α.hom.left = (P' + Q').1 := by
  have hφ : ∀ (X : E.Point g) (X' : E'.Point g), X.1 ≫ α.hom.left = X'.1 →
      E.pointEquivOverHom g X ≫ α.hom = E'.pointEquivOverHom g X' := fun X X' h =>
    Over.OverMorphism.ext ((Over.comp_left _ _ _ _ _).trans h)
  have hmon := isMonHom_of_pointedIso_records E E' α hη
  calc (P + Q).1 ≫ α.hom.left
      = ((lift (E.pointEquivOverHom g P) (E.pointEquivOverHom g Q)).left ≫
          (μ[E.asOver]).left) ≫ α.hom.left :=
        congrArg (· ≫ α.hom.left) (point_add_val_eq E g P Q)
    _ = (lift (E.pointEquivOverHom g P) (E.pointEquivOverHom g Q)).left ≫
          (μ[E.asOver] ≫ α.hom).left := by rw [Category.assoc, Over.comp_left]
    _ = (lift (E.pointEquivOverHom g P) (E.pointEquivOverHom g Q)).left ≫
          ((α.hom ⊗ₘ α.hom) ≫ μ[E'.asOver]).left := by rw [hmon]
    _ = ((lift (E.pointEquivOverHom g P) (E.pointEquivOverHom g Q)) ≫
          (α.hom ⊗ₘ α.hom)).left ≫ (μ[E'.asOver]).left := by
        rw [Over.comp_left, Over.comp_left, Category.assoc]
    _ = (lift (E'.pointEquivOverHom g P') (E'.pointEquivOverHom g Q')).left ≫
          (μ[E'.asOver]).left := by rw [lift_map, hφ P P' hP, hφ Q Q' hQ]
    _ = (P' + Q').1 := (point_add_val_eq E' g P' Q').symm

/-- **Point addition is compatible with restriction along a base morphism**, at the level of
underlying morphisms (so no reindexing of the point types is needed). -/
theorem point_add_val_restrict (E : EllipticCurve S) {T T' : Scheme.{u}} {g : T ⟶ S}
    {g' : T' ⟶ S} (k : T' ⟶ T) (P Q : E.Point g) (P' Q' : E.Point g')
    (hP : P'.1 = k ≫ P.1) (hQ : Q'.1 = k ≫ Q.1) :
    (P' + Q').1 = k ≫ (P + Q).1 := by
  have hlift : (lift (E.pointEquivOverHom g' P') (E.pointEquivOverHom g' Q')).left =
      k ≫ (lift (E.pointEquivOverHom g P) (E.pointEquivOverHom g Q)).left :=
    pullback.hom_ext
      (((lift_left_fst E g' P' Q').trans hP).trans
        (((Category.assoc _ _ _).trans (congrArg (k ≫ ·) (lift_left_fst E g P Q))).symm))
      (((lift_left_snd E g' P' Q').trans hQ).trans
        (((Category.assoc _ _ _).trans (congrArg (k ≫ ·) (lift_left_snd E g P Q))).symm))
  exact (point_add_val_eq E g' P' Q').trans
    ((congrArg (· ≫ (μ[E.asOver]).left) hlift).trans
      ((Category.assoc _ _ _).trans (congrArg (k ≫ ·) (point_add_val_eq E g P Q).symm)))

/-! ### The affine chart as a base change of the record -/

variable (E : EllipticCurve S) (V : S.affineOpens)

/-- The base morphism of the affine chart `V`: `Spec Γ(S, V) ≅ V ↪ S`. -/
noncomputable abbrev chartSumBase : Spec Γ(S, V.1) ⟶ S := V.2.isoSpec.inv ≫ V.1.ι

/-- Base-changing along `chartSumBase V` is base-changing along `V ↪ S`, up to the affine
identification of the chart. -/
theorem isPullback_chartSumLeg :
    IsPullback (pullback.fst E.π (chartSumBase V))
      (pullback.snd E.π (chartSumBase V) ≫ V.2.isoSpec.inv) E.π V.1.ι :=
  (IsPullback.of_hasPullback E.π (chartSumBase V)).of_iso (Iso.refl _) (Iso.refl _)
    V.2.isoSpec.symm (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

/-- **The chart leg isomorphism.** -/
noncomputable def chartSumLegIso : pullback E.π (chartSumBase V) ≅ pullback E.π V.1.ι :=
  (isPullback_chartSumLeg E V).isoIsPullback _ _ (IsPullback.of_hasPullback E.π V.1.ι)

@[reassoc]
theorem chartSumLegIso_hom_fst :
    (chartSumLegIso E V).hom ≫ pullback.fst E.π V.1.ι = pullback.fst E.π (chartSumBase V) :=
  IsPullback.isoIsPullback_hom_fst _ _ (isPullback_chartSumLeg E V)
    (IsPullback.of_hasPullback E.π V.1.ι)

@[reassoc]
theorem chartSumLegIso_hom_snd :
    (chartSumLegIso E V).hom ≫ pullback.snd E.π V.1.ι =
      pullback.snd E.π (chartSumBase V) ≫ V.2.isoSpec.inv :=
  IsPullback.isoIsPullback_hom_snd _ _ (isPullback_chartSumLeg E V)
    (IsPullback.of_hasPullback E.π V.1.ι)

/-- A section of the record, read as a section of its base change to the chart. -/
noncomputable def chartSumPoint (P : E.Point (𝟙 S)) :
    (E.baseChange (chartSumBase V)).Point (𝟙 (Spec Γ(S, V.1))) :=
  ⟨pullback.lift (chartSumBase V ≫ P.1) (𝟙 _)
      (by rw [Category.assoc, P.2, Category.comp_id, Category.id_comp]),
    pullback.lift_snd _ _ _⟩

/-- **The leg bridge**: through `chartSumLegIso`, the chart base change of a section is the
`secBC` restriction of that section — the presentation `of_forall_chart_sum` speaks in. -/
theorem chartSumPoint_legIso (P : E.Point (𝟙 S)) :
    (chartSumPoint E V P).1 ≫ (chartSumLegIso E V).hom =
      V.2.isoSpec.inv ≫ secBC P.2 V.1.ι := by
  have hpfst : (chartSumPoint E V P).1 ≫ pullback.fst E.π (chartSumBase V) =
      chartSumBase V ≫ P.1 := pullback.lift_fst _ _ _
  have hpsnd : (chartSumPoint E V P).1 ≫ pullback.snd E.π (chartSumBase V) = 𝟙 _ :=
    pullback.lift_snd _ _ _
  have hsfst : secBC P.2 V.1.ι ≫ pullback.fst E.π V.1.ι = V.1.ι ≫ P.1 :=
    pullback.lift_fst _ _ _
  have hssnd : secBC P.2 V.1.ι ≫ pullback.snd E.π V.1.ι = 𝟙 _ := pullback.lift_snd _ _ _
  refine pullback.hom_ext ?_ ?_
  · exact ((Category.assoc _ _ _).trans
        ((congrArg ((chartSumPoint E V P).1 ≫ ·) (chartSumLegIso_hom_fst E V)).trans
          hpfst)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (V.2.isoSpec.inv ≫ ·) hsfst).trans (Category.assoc _ _ _).symm)).symm
  · exact ((Category.assoc _ _ _).trans
        ((congrArg ((chartSumPoint E V P).1 ≫ ·) (chartSumLegIso_hom_snd E V)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ V.2.isoSpec.inv) hpsnd).trans (Category.id_comp _))))).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (V.2.isoSpec.inv ≫ ·) hssnd).trans (Category.comp_id _))).symm

/-- **The chart presentation of sections is additive.** `Point.baseChangeEquiv` is an
`AddEquiv`, and `point_add_val_restrict` covers the restriction half. -/
theorem chartSumPoint_add_val (P Q : E.Point (𝟙 S)) :
    (chartSumPoint E V (P + Q)).1 = (chartSumPoint E V P + chartSumPoint E V Q).1 := by
  have hfstP : (EllipticCurve.Point.baseChangeEquiv E (chartSumBase V) (𝟙 _)
      (chartSumPoint E V P)).1 = chartSumBase V ≫ P.1 := pullback.lift_fst _ _ _
  have hfstQ : (EllipticCurve.Point.baseChangeEquiv E (chartSumBase V) (𝟙 _)
      (chartSumPoint E V Q)).1 = chartSumBase V ≫ Q.1 := pullback.lift_fst _ _ _
  have hsum := point_add_val_restrict E (chartSumBase V) P Q _ _ hfstP hfstQ
  have hmap : (EllipticCurve.Point.baseChangeEquiv E (chartSumBase V) (𝟙 _)
        (chartSumPoint E V P + chartSumPoint E V Q)).1 =
      (EllipticCurve.Point.baseChangeEquiv E (chartSumBase V) (𝟙 _) (chartSumPoint E V P) +
        EllipticCurve.Point.baseChangeEquiv E (chartSumBase V) (𝟙 _) (chartSumPoint E V Q)).1 :=
    congrArg Subtype.val (map_add _ _ _)
  refine pullback.hom_ext ?_ ?_
  · exact (pullback.lift_fst _ _ _).trans (hmap.trans hsum).symm
  · exact (pullback.lift_snd _ _ _).trans (chartSumPoint E V P + chartSumPoint E V Q).2.symm

/-! ### The chart isomorphism as a pointed isomorphism of working records -/

variable {W : WeierstrassCurve Γ(S, V.1)} [W.IsElliptic]
  (e : pullback E.π V.1.ι ≅ projModel W)

/-- The chart total isomorphism onto the projective Weierstrass model. -/
noncomputable def chartSumTotalIso : pullback E.π (chartSumBase V) ≅ projModel W :=
  chartSumLegIso E V ≪≫ e

omit [W.IsElliptic] in
theorem chartSumTotalIso_hom_π
    (heπ : e.hom ≫ projModelπ W = pullback.snd E.π V.1.ι ≫ V.2.isoSpec.hom) :
    (chartSumTotalIso E V e).hom ≫ projModelπ W = pullback.snd E.π (chartSumBase V) := by
  rw [chartSumTotalIso, Iso.trans_hom, Category.assoc, heπ, ← Category.assoc,
    chartSumLegIso_hom_snd, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The Weierstrass chart isomorphism, as an isomorphism of working records.** -/
noncomputable def chartSumRecordIso
    (heπ : e.hom ≫ projModelπ W = pullback.snd E.π V.1.ι ≫ V.2.isoSpec.hom) :
    (E.baseChange (chartSumBase V)).asOver ≅ (modelEllipticCurve W).asOver :=
  Over.isoMk (chartSumTotalIso E V e) (chartSumTotalIso_hom_π E V e heπ)

theorem chartSumRecordIso_hom_left
    (heπ : e.hom ≫ projModelπ W = pullback.snd E.π V.1.ι ≫ V.2.isoSpec.hom) :
    (chartSumRecordIso E V e heπ).hom.left = (chartSumLegIso E V).hom ≫ e.hom := rfl

/-- A section of the record, read through the chart record isomorphism, is its `secBC`
restriction read through `e`. -/
theorem chartSumPoint_recordIso
    (heπ : e.hom ≫ projModelπ W = pullback.snd E.π V.1.ι ≫ V.2.isoSpec.hom)
    (P : E.Point (𝟙 S)) :
    (chartSumPoint E V P).1 ≫ (chartSumRecordIso E V e heπ).hom.left =
      V.2.isoSpec.inv ≫ secBC P.2 V.1.ι ≫ e.hom :=
  (congrArg ((chartSumPoint E V P).1 ≫ ·) (chartSumRecordIso_hom_left E V e heπ)).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ e.hom) (chartSumPoint_legIso E V P)).trans (Category.assoc _ _ _)))

/-- **The chart record isomorphism is pointed** — which is exactly the zero-section hypothesis
`hez` of `LocallyWeierstrass` / `IsSquareIdentity.of_forall_chart_sum`. -/
theorem chartSumRecordIso_one
    (heπ : e.hom ≫ projModelπ W = pullback.snd E.π V.1.ι ≫ V.2.isoSpec.hom)
    (hez : V.2.isoSpec.inv ≫ secBC E.zero_π V.1.ι ≫ e.hom = projModelZero W) :
    (η[(E.baseChange (chartSumBase V)).asOver] :
        𝟙_ (Over (Spec Γ(S, V.1))) ⟶ (E.baseChange (chartSumBase V)).asOver) ≫
      (chartSumRecordIso E V e heπ).hom = η[(modelEllipticCurve W).asOver] := by
  refine Over.OverMorphism.ext ?_
  have hkey : (E.baseChange (chartSumBase V)).zero ≫ (chartSumRecordIso E V e heπ).hom.left =
      projModelZero W := (chartSumPoint_recordIso E V e heπ ⟨E.zero, E.zero_π⟩).trans hez
  exact ((Over.comp_left _ _ _ _ _).trans
      ((congrArg (· ≫ (chartSumRecordIso E V e heπ).hom.left)
          (E.baseChange (chartSumBase V)).one_eq_zero).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hkey)))).trans
    (modelEllipticCurve W).one_eq_zero.symm

/-! ### The chart isomorphism carries the point sum to the `mulModelHom` sum -/

/-- **[B3-step5b, THE SUB-LEAF] The Weierstrass chart isomorphism is a *group* isomorphism**:
it carries the group sum of two sections of a working record to the `mulModelHom`-sum of their
chart readings. This is `IsSquareIdentity.of_forall_chart_sum`'s `hsum` for a working record.

The chart datum is repackaged as a *pointed* isomorphism of working records onto
`modelEllipticCurve W` (`chartSumRecordIso`, `chartSumRecordIso_one`), where
`point_add_val_of_pointedIso` — i.e. `isMonHom_of_pointedIso_records` — transports the sum, and
`modelEllipticCurve_point_add_val` computes the model record's addition as `mulModelHom`. -/
theorem chartSum_secBC_add
    (heπ : e.hom ≫ projModelπ W = pullback.snd E.π V.1.ι ≫ V.2.isoSpec.hom)
    (hez : V.2.isoSpec.inv ≫ secBC E.zero_π V.1.ι ≫ e.hom = projModelZero W)
    (P Q : E.Point (𝟙 S)) :
    V.2.isoSpec.inv ≫ secBC (P + Q).2 V.1.ι ≫ e.hom =
      pullback.lift (V.2.isoSpec.inv ≫ secBC P.2 V.1.ι ≫ e.hom)
          (V.2.isoSpec.inv ≫ secBC Q.2 V.1.ι ≫ e.hom)
          ((section_projModelπ_of_chartIso e heπ P.2).trans
            (section_projModelπ_of_chartIso e heπ Q.2).symm) ≫
        mulModelHom W := by
  set mP : (modelEllipticCurve W).Point (𝟙 (Spec Γ(S, V.1))) :=
    ⟨V.2.isoSpec.inv ≫ secBC P.2 V.1.ι ≫ e.hom, section_projModelπ_of_chartIso e heπ P.2⟩
  set mQ : (modelEllipticCurve W).Point (𝟙 (Spec Γ(S, V.1))) :=
    ⟨V.2.isoSpec.inv ≫ secBC Q.2 V.1.ι ≫ e.hom, section_projModelπ_of_chartIso e heπ Q.2⟩
  have htrans := point_add_val_of_pointedIso (E.baseChange (chartSumBase V))
    (modelEllipticCurve W) (chartSumRecordIso E V e heπ) (chartSumRecordIso_one E V e heπ hez)
    (𝟙 (Spec Γ(S, V.1))) (chartSumPoint E V P) (chartSumPoint E V Q) mP mQ
    (chartSumPoint_recordIso E V e heπ P) (chartSumPoint_recordIso E V e heπ Q)
  exact ((chartSumPoint_recordIso E V e heπ (P + Q)).symm.trans
    ((congrArg (· ≫ (chartSumRecordIso E V e heπ).hom.left)
      (chartSumPoint_add_val E V P Q)).trans htrans)).trans
    (modelEllipticCurve_point_add_val W mP mQ)

end Points

/-! ### The relative theorem of the square for a working record -/

/-- **[B3-step5, THE RESULT] The relative theorem of the square for an elliptic-curve working
record over an ARBITRARY base**, with the third section the group sum of the first two:

  `I(D_P) ⊗ I(D_Q) ≅ (I(D_{P+Q}) ⊗ I(D_0)) ⊗ π^*N` for some invertible `N` on the base.

`IsSquareIdentity.of_forall_chart_sum` with every hypothesis discharged: `hsm`/`hZ`/`hlw` are
record fields, `hf` is `EllipticCurveGeom.universallyOConnected`, and `hsum` — the last
sub-leaf, that the chart isomorphism is a *group* isomorphism — is `chartSum_secBC_add`.

The exact tensor identity is false (`Picard/SelfAdjointN.lean`: the two sides differ by `π^*`
of the normal bundle `0^*𝒪(D_0) ≅ ω⁻¹`, and the Poincaré/biextension obstruction survives on
charts), so the `f^*N` form is essential and is what is proved here. -/
theorem isSquareIdentity_point_add {S : Scheme.{u}} (E : EllipticCurve S) [IsSeparated E.π]
    (P Q : E.Point (𝟙 S)) : IsSquareIdentity E.π P.1 Q.1 (P + Q).1 E.zero :=
  IsSquareIdentity.of_forall_chart_sum E.smooth
    E.toEllipticCurveGeom.universallyOConnected.isIso_app P.2 Q.2 (P + Q).2 E.zero_π
    E.localModel fun V _W _ e heπ hez => chartSum_secBC_add E V e heπ hez P Q

end ModularCurves

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.TheoremOfSquareBaseChange

/-!
# Weierstrass charts as base changes of the universal pair (B3-step5a)

`WeilPairing/TheoremOfSquareBaseChange.lean` reduced the relative theorem of the square over an
arbitrary base to a statement about `projModel W` over the ring `Γ(T, V)` of an affine chart
(`IsSquareIdentity.of_forall_chart`), and proved that statement for a **reduced Noetherian**
chart ring with the third section pinned to the `mulModelHom`-sum
(`IsSquareIdentity.of_projModel`). `Γ(T, V)` is an arbitrary commutative ring, and the seesaw
genuinely needs a reduced base — fibrewise triviality does not imply triviality over
`k[ε]/(ε²)` — so the two are not yet matched. This file removes the reducedness/Noetherianity
gap, which is the first of the two sub-leaves left open there.

## The device

The chart datum `(A, W, P, Q)` — an elliptic Weierstrass curve over an arbitrary ring together
with two sections of its projective model — is *classified*. Writing `𝕌` for the universal
Weierstrass curve over the universe-`u` atlas ring `RU`, `W` is `𝕌.map (classifyRingHomU W)`,
so `projModel W` is the fibre of `projModel 𝕌` over `Spec A` (`isPullback_pairChartBC`), and the
pair `(P, Q)` is then a point of

  `B = pairBase (projModelπ 𝕌) = projModel 𝕌 ×_{Spec RU} projModel 𝕌`,

the base of `WeilPairing/TautologicalPair.lean`'s tautological pair (`pairChartClassify`). `B`
is **integral** (`EllipticCurve/GroupLawAxioms.lean`) and **Noetherian**
(`isNoetherian_pairBase`, using `IsNoetherianRing WeierstrassAtlasRingU`), so every affine open
`U` of `B` is the `Spec` of a reduced Noetherian ring — exactly what the seesaw wants.

* `univPairRingHom`, `univPairCurve`, `univPairP`, `univPairQ`, `univPairSum` — the universal
  pair datum of an affine open `U` of `B`: the classifying ring hom `RU →+* Γ(B, U)`, the
  Weierstrass curve it induces, and the two tautological points with their `mulModelHom`-sum.
* `isSquareIdentity_univPair` — **the square identity for that datum**, which is
  `IsSquareIdentity.of_projModel` verbatim, now legitimately applied.
* `pairChartClassify`, `pairChartOpen`, `pairChartTau` — the classifying map of a chart datum,
  the piece of `Spec A` over which it lands in `U`, and the induced map to `Spec Γ(B, U)`.
* `pairChartIso` — **the identification**: over `pairChartOpen`, the chart family and the
  tautological family are two pastings of the *same* base-change square over `projModel 𝕌`
  along the *same* morphism (`pairChartOpen_ι_Spec_map`), hence canonically isomorphic.
* `pairChartOpen_ι_fst_match`, `_snd_match`, `_zero_match`, `_sum_match` — the four sections
  correspond. The sum case runs on `mulModelHom`'s base-change naturality
  (`mulModelHom_baseChangeOf`, the `projModelBaseChangeOf` form of `mulModelHom_map`), applied
  once on each side; the zero case on `projModelZero_baseChangeOf`.
* `isSquareIdentity_pairChartOpen` — `IsSquareIdentity.baseChange` followed by
  `IsSquareIdentity.of_iso`, over each piece of the cover.
* `IsSquareIdentity.of_projModel'` — **the result**: `IsSquareIdentity.of_projModel` with
  `[IsReduced A]` and `[IsNoetherianRing A]` deleted.

## Why no shrinking of the chart is needed

The classifying map `Spec A ⟶ B` need not land in a single affine open of `B`, and one might
expect to have to refine the chart `V` around each point of `T`. That is unnecessary: the
preimages `pairChartOpen` of the affine opens of `B` already cover `Spec A`
(`isOpenCover_pairChartOpen`), and `IsSquareIdentity` is Zariski-local on the base
(`IsSquareIdentity.of_locally`). So the gluing happens over `Spec A` itself and
`IsSquareIdentity.of_forall_chart` can be used unchanged.

## What is still missing

`IsSquareIdentity.of_forall_chart_sum` is `of_forall_chart` with its chart hypothesis reduced to
the **second** sub-leaf only: that the Weierstrass chart isomorphism of `LocallyWeierstrass`
carries the third section to the `mulModelHom`-sum of the first two, i.e. that it is a *group*
isomorphism. That is not attempted here; its arbitrary-base primitive is
`isMonHom_of_pointedIso_records` (`EllipticCurve/RecordGroupUnique.lean`, proved).
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

/-! ### Base-change naturality of `mulModelHom`, in the transported presentation -/

/-- `mulModelHom_map` for `projModelBaseChangeOf`: the multiplication commutes with the
transported base-change morphism of a curve presented as `W₀.map f = W`. -/
theorem mulModelHom_baseChangeOf {U R : Type u} [CommRing U] [CommRing R] (f : U →+* R)
    (W₀ : WeierstrassCurve U) [W₀.IsElliptic] (W : WeierstrassCurve R) [W.IsElliptic]
    (h : W₀.map f = W) :
    mulModelHom W ≫ projModelBaseChangeOf f W₀ W h =
      pullback.map (projModelπ W) (projModelπ W) (projModelπ W₀) (projModelπ W₀)
          (projModelBaseChangeOf f W₀ W h) (projModelBaseChangeOf f W₀ W h)
          (Spec.map (CommRingCat.ofHom f))
          (isPullback_projModelBaseChangeOf f W₀ W h).w.symm
          (isPullback_projModelBaseChangeOf f W₀ W h).w.symm ≫
        mulModelHom W₀ := by
  subst h
  simp only [projModelBaseChangeOf_rfl]
  exact mulModelHom_map f W₀

/-! ### The universal pair datum -/

/-- **The base of the universal pair of points**: `E_𝕌 ×_{Spec RU} E_𝕌` for the universal
Weierstrass model. It is integral — in particular reduced — and Noetherian, which is exactly
what the seesaw needs and what an arbitrary chart ring lacks. -/
noncomputable abbrev univPairBase : Scheme.{u} :=
  pairBase (projModelπ universalWeierstrassLocU.{u})

instance : IsNoetherian (univPairBase.{u}) :=
  isNoetherian_pairBase (projModelπ universalWeierstrassLocU.{u})

variable (U : (univPairBase.{u}).affineOpens)

/-- The classifying ring hom of an affine open `U` of the universal pair base: the composite
`Spec Γ(B, U) ≅ U ↪ B ⟶ Spec RU`, read as a map of rings. -/
noncomputable def univPairRingHom : WeierstrassAtlasRingU.{u} →+* Γ(univPairBase.{u}, U.1) :=
  (Spec.preimage (U.2.isoSpec.inv ≫ U.1.ι ≫
    pairBaseπ (projModelπ universalWeierstrassLocU.{u}))).hom

/-- `Spec` of the classifying ring hom is the structural composite. -/
theorem Spec_map_univPairRingHom :
    Spec.map (CommRingCat.ofHom (univPairRingHom U)) =
      U.2.isoSpec.inv ≫ U.1.ι ≫ pairBaseπ (projModelπ universalWeierstrassLocU.{u}) := by
  simp [univPairRingHom]

/-- **The universal Weierstrass curve of an affine open of the pair base.** -/
noncomputable def univPairCurve : WeierstrassCurve Γ(univPairBase.{u}, U.1) :=
  universalWeierstrassLocU.map (univPairRingHom U)

instance : (univPairCurve U).IsElliptic := by
  rw [univPairCurve]; infer_instance

/-- The base-change square presenting `projModel (univPairCurve U)` as the fibre of the
universal model over `Spec Γ(B, U)`. -/
noncomputable abbrev univPairBC :
    projModel (univPairCurve U) ⟶ projModel universalWeierstrassLocU.{u} :=
  projModelBaseChangeOf (univPairRingHom U) universalWeierstrassLocU (univPairCurve U) rfl

theorem isPullback_univPairBC :
    IsPullback (univPairBC U) (projModelπ (univPairCurve U))
      (projModelπ universalWeierstrassLocU.{u})
      (Spec.map (CommRingCat.ofHom (univPairRingHom U))) :=
  isPullback_projModelBaseChangeOf _ _ _ rfl

/-! ### The two tautological points over an affine open of the pair base -/

/-- **The first tautological point** of `U`, as a section of `projModel (univPairCurve U)`:
the first projection `U ↪ B ⟶ E_𝕌`, lifted through the base-change square. -/
noncomputable def univPairP : Spec Γ(univPairBase.{u}, U.1) ⟶ projModel (univPairCurve U) :=
  (isPullback_univPairBC U).lift
    (U.2.isoSpec.inv ≫ U.1.ι ≫ pullback.fst (projModelπ universalWeierstrassLocU.{u})
      (projModelπ universalWeierstrassLocU.{u})) (𝟙 _) <| by
    rw [Category.id_comp, Spec_map_univPairRingHom]
    simp

/-- **The second tautological point** of `U`, from the second projection. -/
noncomputable def univPairQ : Spec Γ(univPairBase.{u}, U.1) ⟶ projModel (univPairCurve U) :=
  (isPullback_univPairBC U).lift
    (U.2.isoSpec.inv ≫ U.1.ι ≫ pullback.snd (projModelπ universalWeierstrassLocU.{u})
      (projModelπ universalWeierstrassLocU.{u})) (𝟙 _) <| by
    rw [Category.id_comp, Spec_map_univPairRingHom]
    simp only [Category.assoc, ← pullback.condition]

@[reassoc (attr := simp)]
theorem univPairP_projModelπ : univPairP U ≫ projModelπ (univPairCurve U) = 𝟙 _ :=
  (isPullback_univPairBC U).lift_snd _ _ _

@[reassoc (attr := simp)]
theorem univPairQ_projModelπ : univPairQ U ≫ projModelπ (univPairCurve U) = 𝟙 _ :=
  (isPullback_univPairBC U).lift_snd _ _ _

@[reassoc (attr := simp)]
theorem univPairP_univPairBC : univPairP U ≫ univPairBC U =
    U.2.isoSpec.inv ≫ U.1.ι ≫ pullback.fst (projModelπ universalWeierstrassLocU.{u})
      (projModelπ universalWeierstrassLocU.{u}) :=
  (isPullback_univPairBC U).lift_fst _ _ _

@[reassoc (attr := simp)]
theorem univPairQ_univPairBC : univPairQ U ≫ univPairBC U =
    U.2.isoSpec.inv ≫ U.1.ι ≫ pullback.snd (projModelπ universalWeierstrassLocU.{u})
      (projModelπ universalWeierstrassLocU.{u}) :=
  (isPullback_univPairBC U).lift_fst _ _ _

/-- **The sum of the two tautological points**, the third section of the square identity. -/
noncomputable def univPairSum : Spec Γ(univPairBase.{u}, U.1) ⟶ projModel (univPairCurve U) :=
  pullback.lift (univPairP U) (univPairQ U)
    ((univPairP_projModelπ U).trans (univPairQ_projModelπ U).symm) ≫
      mulModelHom (univPairCurve U)

theorem univPairSum_projModelπ : univPairSum U ≫ projModelπ (univPairCurve U) = 𝟙 _ := by
  rw [univPairSum, Category.assoc, mulModelHom_π, ← Category.assoc, pullback.lift_fst,
    univPairP_projModelπ]

/-- `mulModelHom_baseChangeOf` at the universal-pair presentation. -/
theorem mulModelHom_univPairBC :
    mulModelHom (univPairCurve U) ≫ univPairBC U =
      pullback.map (projModelπ (univPairCurve U)) (projModelπ (univPairCurve U))
          (projModelπ universalWeierstrassLocU.{u}) (projModelπ universalWeierstrassLocU.{u})
          (univPairBC U) (univPairBC U) (Spec.map (CommRingCat.ofHom (univPairRingHom U)))
          (isPullback_univPairBC U).w.symm (isPullback_univPairBC U).w.symm ≫
        mulModelHom universalWeierstrassLocU.{u} :=
  mulModelHom_baseChangeOf _ _ _ rfl

/-- Read through the base-change square, the sum of the two tautological points of `U` is the
universal multiplication applied to the tautological pair itself. -/
@[reassoc]
theorem univPairSum_univPairBC : univPairSum U ≫ univPairBC U =
    (U.2.isoSpec.inv ≫ U.1.ι) ≫ mulModelHom universalWeierstrassLocU.{u} := by
  rw [univPairSum, Category.assoc, mulModelHom_univPairBC, ← Category.assoc]
  congr 1
  refine pullback.hom_ext ?_ ?_ <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, univPairP_univPairBC, univPairQ_univPairBC]

/-- **[B3-step5a, the reduced model] The square identity for the tautological pair.**

`Γ(B, U)` is reduced (`B` is integral, `EllipticCurve/GroupLawAxioms.lean`) and Noetherian
(`isNoetherian_pairBase` + `IsLocallyNoetherian.component_noetherian`), which is precisely
what `IsSquareIdentity.of_projModel` — hence the seesaw — asks for and an arbitrary chart ring
does not provide. -/
theorem isSquareIdentity_univPair :
    IsSquareIdentity (projModelπ (univPairCurve U)) (univPairP U) (univPairQ U)
      (univPairSum U) (projModelZero (univPairCurve U)) :=
  haveI : IsNoetherianRing Γ(univPairBase.{u}, U.1) :=
    IsLocallyNoetherian.component_noetherian U
  IsSquareIdentity.of_projModel (univPairP_projModelπ U) (univPairQ_projModelπ U)
    (univPairSum_projModelπ U) rfl

/-! ### The chart datum, and its classifying map to the universal pair base -/

variable {A : Type u} [CommRing A]

/-- The transported base-change morphism presenting `projModel W` as the fibre of the universal
model over `Spec A`, along the classifying map of `W`. -/
noncomputable abbrev pairChartBC (W : WeierstrassCurve A) [W.IsElliptic] :
    projModel W ⟶ projModel universalWeierstrassLocU.{u} :=
  projModelBaseChangeOf (classifyRingHomU W) universalWeierstrassLocU W
    (universalWeierstrassLocU_map_classifyRingHomU W)

theorem isPullback_pairChartBC (W : WeierstrassCurve A) [W.IsElliptic] :
    IsPullback (pairChartBC W) (projModelπ W) (projModelπ universalWeierstrassLocU.{u})
      (Spec.map (CommRingCat.ofHom (classifyRingHomU W))) :=
  isPullback_projModelBaseChangeOf _ _ _ _

variable {W : WeierstrassCurve A} [W.IsElliptic] {P Q : Spec (CommRingCat.of A) ⟶ projModel W}

theorem pairChartBC_section (hP : P ≫ projModelπ W = 𝟙 _) :
    (P ≫ pairChartBC W) ≫ projModelπ universalWeierstrassLocU.{u} =
      Spec.map (CommRingCat.ofHom (classifyRingHomU W)) := by
  rw [Category.assoc, (isPullback_pairChartBC W).w, ← Category.assoc, hP, Category.id_comp]

/-- `mulModelHom_baseChangeOf` at the chart presentation. -/
theorem mulModelHom_pairChartBC :
    mulModelHom W ≫ pairChartBC W =
      pullback.map (projModelπ W) (projModelπ W) (projModelπ universalWeierstrassLocU.{u})
          (projModelπ universalWeierstrassLocU.{u}) (pairChartBC W) (pairChartBC W)
          (Spec.map (CommRingCat.ofHom (classifyRingHomU W)))
          (isPullback_pairChartBC W).w.symm (isPullback_pairChartBC W).w.symm ≫
        mulModelHom universalWeierstrassLocU.{u} :=
  mulModelHom_baseChangeOf _ _ _ _

theorem projModelZero_pairChartBC :
    projModelZero W ≫ pairChartBC W = Spec.map (CommRingCat.ofHom (classifyRingHomU W)) ≫
      projModelZero universalWeierstrassLocU.{u} :=
  projModelZero_baseChangeOf _ _ _ _

variable (hP : P ≫ projModelπ W = 𝟙 _) (hQ : Q ≫ projModelπ W = 𝟙 _)

/-- **The classifying map of a chart datum**: the pair `(P, Q)` of sections, read through the
base-change square, is a point of `E_𝕌 ×_{Spec RU} E_𝕌`. -/
noncomputable def pairChartClassify : Spec (CommRingCat.of A) ⟶ univPairBase.{u} :=
  pairClassify (projModelπ universalWeierstrassLocU.{u})
    (Spec.map (CommRingCat.ofHom (classifyRingHomU W)))
    ⟨P ≫ pairChartBC W, pairChartBC_section hP⟩
    ⟨Q ≫ pairChartBC W, pairChartBC_section hQ⟩

@[reassoc (attr := simp)]
theorem pairChartClassify_fst :
    pairChartClassify hP hQ ≫ pullback.fst (projModelπ universalWeierstrassLocU.{u})
      (projModelπ universalWeierstrassLocU.{u}) = P ≫ pairChartBC W :=
  pairClassify_fst _ _ _ _

@[reassoc (attr := simp)]
theorem pairChartClassify_snd :
    pairChartClassify hP hQ ≫ pullback.snd (projModelπ universalWeierstrassLocU.{u})
      (projModelπ universalWeierstrassLocU.{u}) = Q ≫ pairChartBC W :=
  pairClassify_snd _ _ _ _

@[reassoc]
theorem pairChartClassify_pairBaseπ :
    pairChartClassify hP hQ ≫ pairBaseπ (projModelπ universalWeierstrassLocU.{u}) =
      Spec.map (CommRingCat.ofHom (classifyRingHomU W)) :=
  pairClassify_π _ _ _ _

/-- **The third section of a chart datum is classified too**: read through the base-change
square, the `mulModelHom`-sum of `P` and `Q` is the universal multiplication applied to the
classifying map of the pair. -/
theorem pairChartSum_pairChartBC :
    (pullback.lift P Q (hP.trans hQ.symm) ≫ mulModelHom W) ≫ pairChartBC W =
      pairChartClassify hP hQ ≫ mulModelHom universalWeierstrassLocU.{u} := by
  rw [Category.assoc, mulModelHom_pairChartBC, ← Category.assoc]
  congr 1
  refine pullback.hom_ext ?_ ?_ <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, pairChartClassify_fst, pairChartClassify_snd]

/-! ### The cover of the chart base pulled back from the universal pair base -/

variable (U : (univPairBase.{u}).affineOpens)

/-- The piece of `Spec A` over which the classifying map lands in the affine open `U`. These
opens cover `Spec A` as `U` runs over the affine opens of the universal pair base. -/
noncomputable abbrev pairChartOpen : (Spec (CommRingCat.of A)).Opens :=
  pairChartClassify hP hQ ⁻¹ᵁ U.1

/-- The classifying map of `pairChartOpen`, landing in the *affine* open `U` and read as a map
to `Spec Γ(B, U)` — the base over which the tautological square identity is available. -/
noncomputable def pairChartTau :
    (pairChartOpen hP hQ U).toScheme ⟶ Spec Γ(univPairBase.{u}, U.1) :=
  (pairChartClassify hP hQ ∣_ U.1) ≫ U.2.isoSpec.hom

/-- `pairChartTau` really is the classifying map restricted to `pairChartOpen`. -/
@[reassoc]
theorem pairChartTau_isoSpec_inv_ι : pairChartTau hP hQ U ≫ U.2.isoSpec.inv ≫ U.1.ι =
    (pairChartOpen hP hQ U).ι ≫ pairChartClassify hP hQ := by
  rw [pairChartTau, Category.assoc, Iso.hom_inv_id_assoc]
  exact morphismRestrict_ι _ _

/-- The two `Spec`-level classifying maps agree over `pairChartOpen`: this is the identity that
makes the chart family and the tautological family two base changes of *the same* universal
model along *the same* morphism. -/
@[reassoc]
theorem pairChartOpen_ι_Spec_map :
    (pairChartOpen hP hQ U).ι ≫ Spec.map (CommRingCat.ofHom (classifyRingHomU W)) =
      pairChartTau hP hQ U ≫ Spec.map (CommRingCat.ofHom (univPairRingHom U)) := by
  rw [Spec_map_univPairRingHom, pairChartTau_isoSpec_inv_ι_assoc,
    pairChartClassify_pairBaseπ]

/-! ### The chart family and the tautological family are the same base change -/

/-- The chart family over `pairChartOpen`, pasted onto the chart base-change square: it is the
fibre of the *universal* model over `pairChartOpen`. -/
theorem isPullback_pairChartFamily :
    IsPullback (pullback.fst (projModelπ W) (pairChartOpen hP hQ U).ι ≫ pairChartBC W)
      (pullback.snd (projModelπ W) (pairChartOpen hP hQ U).ι)
      (projModelπ universalWeierstrassLocU.{u})
      ((pairChartOpen hP hQ U).ι ≫ Spec.map (CommRingCat.ofHom (classifyRingHomU W))) :=
  (IsPullback.of_hasPullback _ _).paste_horiz (isPullback_pairChartBC W)

/-- The tautological family over `pairChartOpen` (via `pairChartTau`), pasted onto the
universal-pair base-change square: it is the fibre of the *same* universal model over
`pairChartOpen`, along the *same* morphism, by `pairChartOpen_ι_Spec_map`. -/
theorem isPullback_univPairFamily :
    IsPullback
      (pullback.fst (projModelπ (univPairCurve U)) (pairChartTau hP hQ U) ≫ univPairBC U)
      (pullback.snd (projModelπ (univPairCurve U)) (pairChartTau hP hQ U))
      (projModelπ universalWeierstrassLocU.{u})
      ((pairChartOpen hP hQ U).ι ≫ Spec.map (CommRingCat.ofHom (classifyRingHomU W))) := by
  rw [pairChartOpen_ι_Spec_map]
  exact (IsPullback.of_hasPullback _ _).paste_horiz (isPullback_univPairBC U)

/-- **[B3-step5a, the identification] The chart family over `pairChartOpen` IS the tautological
family**, both being the fibre of the universal Weierstrass model over the same morphism. -/
noncomputable def pairChartIso :
    pullback (projModelπ W) (pairChartOpen hP hQ U).ι ≅
      pullback (projModelπ (univPairCurve U)) (pairChartTau hP hQ U) :=
  (isPullback_pairChartFamily hP hQ U).isoIsPullback _ _ (isPullback_univPairFamily hP hQ U)

@[reassoc]
theorem pairChartIso_hom_fst : (pairChartIso hP hQ U).hom ≫
    (pullback.fst (projModelπ (univPairCurve U)) (pairChartTau hP hQ U) ≫ univPairBC U) =
      pullback.fst (projModelπ W) (pairChartOpen hP hQ U).ι ≫ pairChartBC W :=
  IsPullback.isoIsPullback_hom_fst _ _ (isPullback_pairChartFamily hP hQ U)
    (isPullback_univPairFamily hP hQ U)

@[reassoc]
theorem pairChartIso_hom_snd : (pairChartIso hP hQ U).hom ≫
    pullback.snd (projModelπ (univPairCurve U)) (pairChartTau hP hQ U) =
      pullback.snd (projModelπ W) (pairChartOpen hP hQ U).ι :=
  IsPullback.isoIsPullback_hom_snd _ _ (isPullback_pairChartFamily hP hQ U)
    (isPullback_univPairFamily hP hQ U)

/-! ### The four sections match -/

/-- The first chart section restricted to `pairChartOpen` is the first tautological point. -/
theorem pairChartOpen_ι_fst_match :
    (pairChartOpen hP hQ U).ι ≫ P ≫ pairChartBC W =
      pairChartTau hP hQ U ≫ univPairP U ≫ univPairBC U := by
  rw [univPairP_univPairBC, pairChartTau_isoSpec_inv_ι_assoc, pairChartClassify_fst]

/-- The second chart section restricted to `pairChartOpen` is the second tautological point. -/
theorem pairChartOpen_ι_snd_match :
    (pairChartOpen hP hQ U).ι ≫ Q ≫ pairChartBC W =
      pairChartTau hP hQ U ≫ univPairQ U ≫ univPairBC U := by
  rw [univPairQ_univPairBC, pairChartTau_isoSpec_inv_ι_assoc, pairChartClassify_snd]

theorem projModelZero_univPairBC : projModelZero (univPairCurve U) ≫ univPairBC U =
    Spec.map (CommRingCat.ofHom (univPairRingHom U)) ≫
      projModelZero universalWeierstrassLocU.{u} :=
  projModelZero_baseChangeOf _ _ _ rfl

/-- The zero sections match — both are the universal zero section pulled back. -/
theorem pairChartOpen_ι_zero_match :
    (pairChartOpen hP hQ U).ι ≫ projModelZero W ≫ pairChartBC W =
      pairChartTau hP hQ U ≫ projModelZero (univPairCurve U) ≫ univPairBC U := by
  rw [projModelZero_pairChartBC, projModelZero_univPairBC, pairChartOpen_ι_Spec_map_assoc]

/-- The third chart section restricted to `pairChartOpen` is the sum of the two tautological
points. This is where `mulModelHom`'s base-change naturality is used — twice, once on each
side of the identification. -/
theorem pairChartOpen_ι_sum_match {Rs : Spec (CommRingCat.of A) ⟶ projModel W}
    (hRs : Rs = pullback.lift P Q (hP.trans hQ.symm) ≫ mulModelHom W) :
    (pairChartOpen hP hQ U).ι ≫ Rs ≫ pairChartBC W =
      pairChartTau hP hQ U ≫ univPairSum U ≫ univPairBC U := by
  rw [hRs, pairChartSum_pairChartBC, univPairSum_univPairBC]
  simp only [Category.assoc]
  rw [pairChartTau_isoSpec_inv_ι_assoc]

/-! ### The square identity over each piece of the cover -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[B3-step5a, the local statement] The square identity for a chart datum over the piece of
`Spec A` where the classifying map lands in the affine open `U`.**

The chart family restricted there is the tautological family base-changed along `pairChartTau`
(`pairChartIso`), the four sections correspond (the four `_match` lemmas), and over
`Spec Γ(B, U)` — a *reduced Noetherian* ring — the identity is `isSquareIdentity_univPair`. -/
theorem isSquareIdentity_pairChartOpen {Rs : Spec (CommRingCat.of A) ⟶ projModel W}
    (hR : Rs ≫ projModelπ W = 𝟙 _)
    (hRs : Rs = pullback.lift P Q (hP.trans hQ.symm) ≫ mulModelHom W) :
    IsSquareIdentity (pullback.snd (projModelπ W) (pairChartOpen hP hQ U).ι)
      (secBC hP (pairChartOpen hP hQ U).ι) (secBC hQ (pairChartOpen hP hQ U).ι)
      (secBC hR (pairChartOpen hP hQ U).ι)
      (secBC (projModelZero_projModelπ W) (pairChartOpen hP hQ U).ι) := by
  haveI : IsSeparated (pullback.snd (projModelπ W) (pairChartOpen hP hQ U).ι) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  haveI : IsSeparated (pullback.snd (projModelπ (univPairCurve U)) (pairChartTau hP hQ U)) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  refine IsSquareIdentity.of_iso
    (MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ (projModel_smooth W))
    (MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _
      (projModel_smooth (univPairCurve U)))
    (pairChartIso hP hQ U) (Iso.refl _)
    (by rw [Iso.refl_hom, Category.comp_id]; exact pairChartIso_hom_snd hP hQ U)
    (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _)
    (pullback.lift_snd _ _ _) ?_ ?_ ?_ ?_
    ((isSquareIdentity_univPair U).baseChange (projModel_smooth (univPairCurve U))
      (univPairP_projModelπ U) (univPairQ_projModelπ U) (univPairSum_projModelπ U)
      (projModelZero_projModelπ (univPairCurve U)) (pairChartTau hP hQ U))
  · refine (isPullback_univPairFamily hP hQ U).hom_ext ?_ ?_
    · simp only [Iso.refl_inv, Category.id_comp, Category.assoc, pairChartIso_hom_fst,
        pullback.lift_fst_assoc]
      exact pairChartOpen_ι_fst_match hP hQ U
    · simp only [Iso.refl_inv, Category.id_comp, Category.assoc, pairChartIso_hom_snd,
        pullback.lift_snd]
  · refine (isPullback_univPairFamily hP hQ U).hom_ext ?_ ?_
    · simp only [Iso.refl_inv, Category.id_comp, Category.assoc, pairChartIso_hom_fst,
        pullback.lift_fst_assoc]
      exact pairChartOpen_ι_snd_match hP hQ U
    · simp only [Iso.refl_inv, Category.id_comp, Category.assoc, pairChartIso_hom_snd,
        pullback.lift_snd]
  · refine (isPullback_univPairFamily hP hQ U).hom_ext ?_ ?_
    · simp only [Iso.refl_inv, Category.id_comp, Category.assoc, pairChartIso_hom_fst,
        pullback.lift_fst_assoc]
      exact pairChartOpen_ι_sum_match hP hQ U hRs
    · simp only [Iso.refl_inv, Category.id_comp, Category.assoc, pairChartIso_hom_snd,
        pullback.lift_snd]
  · refine (isPullback_univPairFamily hP hQ U).hom_ext ?_ ?_
    · simp only [Iso.refl_inv, Category.id_comp, Category.assoc, pairChartIso_hom_fst,
        pullback.lift_fst_assoc]
      exact pairChartOpen_ι_zero_match hP hQ U
    · simp only [Iso.refl_inv, Category.id_comp, Category.assoc, pairChartIso_hom_snd,
        pullback.lift_snd]

/-! ### Gluing: the chart statement over an arbitrary ring -/

/-- The pieces `pairChartOpen` cover `Spec A`: they are the preimages under the classifying map
of the affine opens of the universal pair base, which cover it. -/
theorem isOpenCover_pairChartOpen :
    IsOpenCover fun U : (univPairBase.{u}).affineOpens => pairChartOpen hP hQ U :=
  (pairChartClassify hP hQ).iSup_preimage_eq_top (iSup_affineOpens_eq_top _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[B3-step5a, THE RESULT] The relative theorem of the square for the projective Weierstrass
model over an ARBITRARY commutative ring** — `IsSquareIdentity.of_projModel` with its
`IsReduced` and `IsNoetherianRing` hypotheses discharged.

The chart datum `(A, W, P, Q)` is classified by a morphism `Spec A ⟶ B` to the base of the
tautological pair `B = pairBase (projModelπ 𝕌)` (`pairChartClassify`). `B` is integral and
Noetherian, so each of its affine opens is the `Spec` of a **reduced Noetherian** ring, where
the seesaw — hence `of_projModel` — applies (`isSquareIdentity_univPair`). Over the preimage of
such an affine open the chart family *is* the tautological family base-changed (`pairChartIso`,
two pastings of the same base-change square over the universal model) with the four sections
matching, and `IsSquareIdentity.baseChange` + `IsSquareIdentity.of_iso` transport the identity
(`isSquareIdentity_pairChartOpen`). These preimages cover `Spec A`, and the identity is
Zariski-local on the base (`IsSquareIdentity.of_locally`), so no shrinking of the chart is
needed: the statement holds over `Spec A` itself.

This is the first of the two leaves left between `IsSquareIdentity.of_forall_chart` and
`IsSquareIdentity.of_projModel`. The second — that the chart isomorphism of
`LocallyWeierstrass` is a *group* isomorphism, so that the third section really is the
`mulModelHom`-sum — is untouched here and is still the hypothesis `hRs`. -/
theorem IsSquareIdentity.of_projModel' {A : Type u} [CommRing A] {W₀ : WeierstrassCurve A}
    [W₀.IsElliptic] {P Q Rs : Spec (CommRingCat.of A) ⟶ projModel W₀}
    (hP : P ≫ projModelπ W₀ = 𝟙 _) (hQ : Q ≫ projModelπ W₀ = 𝟙 _)
    (hR : Rs ≫ projModelπ W₀ = 𝟙 _)
    (hRs : Rs = pullback.lift P Q (hP.trans hQ.symm) ≫ mulModelHom W₀) :
    IsSquareIdentity (projModelπ W₀) P Q Rs (projModelZero W₀) :=
  IsSquareIdentity.of_locally (projModel_smooth W₀)
    ((modelEllipticCurve W₀).toEllipticCurveGeom.universallyOConnected).isIso_app hP hQ hR
    (projModelZero_projModelπ W₀) _ (isOpenCover_pairChartOpen hP hQ)
    fun U => isSquareIdentity_pairChartOpen hP hQ U hR hRs

/-! ### Feeding `IsSquareIdentity.of_forall_chart` -/

/-- A section of the family, read through a Weierstrass chart isomorphism, is a section of the
model. -/
theorem section_projModelπ_of_chartIso {Y T : Scheme.{u}} {f : Y ⟶ T} {V : T.affineOpens}
    {W : WeierstrassCurve Γ(T, V.1)} (e : pullback f V.1.ι ≅ projModel W)
    (heπ : e.hom ≫ projModelπ W = pullback.snd f V.1.ι ≫ V.2.isoSpec.hom) {S : T ⟶ Y}
    (hS : S ≫ f = 𝟙 T) :
    (V.2.isoSpec.inv ≫ secBC hS V.1.ι ≫ e.hom) ≫ projModelπ W = 𝟙 _ := by
  rw [Category.assoc, Category.assoc, heπ, ← Category.assoc (secBC hS V.1.ι),
    pullback.lift_snd, Category.id_comp, Iso.inv_hom_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[B3-step5, packaged modulo sub-leaf 2] The relative theorem of the square from
`LocallyWeierstrass`, with the chart ring no longer required to be reduced or Noetherian.**

`IsSquareIdentity.of_forall_chart`'s `hchart` is discharged by
`IsSquareIdentity.of_projModel'`, so the only thing left to supply about a Weierstrass chart is
that the chart isomorphism carries the third section to the `mulModelHom`-**sum** of the first
two — i.e. that the chart isomorphism is a *group* isomorphism. That is the second sub-leaf,
whose arbitrary-base primitive is `isMonHom_of_pointedIso_records`
(`EllipticCurve/RecordGroupUnique.lean`, proved); it is taken as the hypothesis `hsum` here and
is deliberately **not** attempted in this file. -/
theorem IsSquareIdentity.of_forall_chart_sum {Y T : Scheme.{u}} {f : Y ⟶ T} [IsSeparated f]
    (hsm : SmoothOfRelativeDimension 1 f) (hf : ∀ W : T.Opens, IsIso (f.app W))
    {P Q R Z : T ⟶ Y} (hP : P ≫ f = 𝟙 T) (hQ : Q ≫ f = 𝟙 T) (hR : R ≫ f = 𝟙 T)
    (hZ : Z ≫ f = 𝟙 T) (hlw : LocallyWeierstrass f Z hZ)
    (hsum : ∀ (V : T.affineOpens) (W : WeierstrassCurve Γ(T, V.1)) [W.IsElliptic]
      (e : pullback f V.1.ι ≅ projModel W)
      (heπ : e.hom ≫ projModelπ W = pullback.snd f V.1.ι ≫ V.2.isoSpec.hom),
      V.2.isoSpec.inv ≫ secBC hZ V.1.ι ≫ e.hom = projModelZero W →
      V.2.isoSpec.inv ≫ secBC hR V.1.ι ≫ e.hom =
        pullback.lift (V.2.isoSpec.inv ≫ secBC hP V.1.ι ≫ e.hom)
          (V.2.isoSpec.inv ≫ secBC hQ V.1.ι ≫ e.hom)
          ((section_projModelπ_of_chartIso e heπ hP).trans
            (section_projModelπ_of_chartIso e heπ hQ).symm) ≫ mulModelHom W) :
    IsSquareIdentity f P Q R Z :=
  IsSquareIdentity.of_forall_chart hsm hf hP hQ hR hZ hlw fun V W hell e heπ hez =>
    haveI := hell
    IsSquareIdentity.of_projModel' (section_projModelπ_of_chartIso e heπ hP)
      (section_projModelπ_of_chartIso e heπ hQ) (section_projModelπ_of_chartIso e heπ hR)
      (hsum V W e heπ hez)

end ModularCurves

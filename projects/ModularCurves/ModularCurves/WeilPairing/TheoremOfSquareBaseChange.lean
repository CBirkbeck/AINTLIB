/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.DescentFromCharts
import ModularCurves.WeilPairing.TheoremOfSquareUniversal

/-!
# The relative theorem of the square, transported and glued (B3-step5)

This file supplies the *base-independent* reductions that carry the relative theorem of the
square from the Weierstrass-model family, where it is proved (`TheoremOfSquareUniversal`'s
`exists_invertible_tensor_idealModule_add_projModel'`, over a reduced Noetherian ring), down to an
arbitrary — possibly non-reduced — base.

* `IsSquareIdentity f P Q R Z` — the conclusion shape of the leaf
  `Picard/SelfAdjointN.lean`'s `exists_invertible_tensor_idealModule_add`, stated for a bare
  morphism `f` and four bare sections: `I(D_P) ⊗ I(D_Q) ≅ (I(D_R) ⊗ I(D_Z)) ⊗ f^*N` for some
  invertible `N` on the base.
* `IsSquareIdentity.baseChange` — **transport along a base change.** The identity for
  `π : C ⟶ S` gives the identity for `pullback.snd π t` and the base-changed sections, with the
  base bundle `t^*N`. Nothing but monoidality of `f^*` (`nonempty_pullback_tensorObj`) and the
  ideal-module base-change comparison (`nonempty_pullback_tensorObj_idealModule_pair`).
* `IsSquareIdentity.of_iso` — **transport along a chart isomorphism.** An isomorphism of total
  spaces over an isomorphism of bases, carrying the four sections to the four sections, carries
  the identity back, with base bundle `γ^*N`. The ideal-module half is
  `nonempty_pullback_idealModule_ker_of_iso`, whose arithmetic core is
  `IdealSheafData.comap_ker_comp_iso` (`comap α` inverts `map α` for an isomorphism `α`).
* `IsSquareIdentity.of_locally` / `of_forall_exists_opens` — **gluing.** The identity is
  Zariski-local on the base: it is `WeilPairing/RelPicLocal.lean`'s
  `exists_pullback_twist_of_locally'` at `M = I(D_P) ⊗ I(D_Q)`, `M' = I(D_R) ⊗ I(D_Z)`, whose
  conclusion is *literally* `IsSquareIdentity`. The local input is accepted in the base-change
  presentation (over `Limits.pullback f V.ι`), which is what `IsSquareIdentity.baseChange`
  produces; the bridge to the `restrict` presentation that
  `exists_pullback_twist_of_locally'` consumes is `nonempty_restrict_iso_pullback_fst`.
* `IsSquareIdentity.of_forall_chart` — **the packaged reduction**, the headline: for a separated
  smooth relative curve whose zero section makes it `LocallyWeierstrass`, the identity over an
  arbitrary base follows from the identity on every Weierstrass chart, for the three non-zero
  sections read through the chart isomorphism.
* `IsSquareIdentity.of_projModel` — the proved chart input restated in this vocabulary, for a
  **reduced Noetherian** chart ring and with the third section pinned to `mulModelHom`.

Gluing is needed because the passage from an arbitrary elliptic curve to a Weierstrass model —
and hence to the universal Weierstrass parameter space, which is where the base becomes reduced
and the seesaw applies — is only Zariski-local on the base.

## What is still missing between `of_forall_chart` and `of_projModel`

`of_forall_chart` reduces `Picard/SelfAdjointN.lean`'s leaf to a statement about `projModel W`
over the ring `Γ(T, V)` of an affine chart; `of_projModel` proves such a statement. Two gaps
remain between them, both of which are genuinely about the chart, not about the base:

1. **Reducedness/Noetherianity of the chart ring.** `Γ(T, V)` is an arbitrary commutative ring.
   The seesaw needs a reduced base (`Seesaw needs a reduced base`: fibrewise triviality does not
   imply triviality over `k[ε]/(ε²)`), so the chart datum `(Γ(T,V), W, P, Q)` has to be
   exhibited as a base change of the *universal* pair datum. The universal object is
   `pairBase (projModelπ 𝕌) = projModel 𝕌 ×_{Spec RU} projModel 𝕌`, which is integral
   (`EllipticCurve/GroupLawAxioms.lean`) and Noetherian (`isNoetherian_pairBase`, using
   `IsNoetherianRing WeierstrassAtlasRingU`), so each of its affine opens is the `Spec` of a
   reduced Noetherian ring; refining the chart so that the classifying map lands in one such
   affine open turns `IsSquareIdentity.baseChange` + `of_iso` into the missing step.
2. **The chart isomorphism is a group isomorphism**, i.e. the third section really is the
   `mulModelHom`-sum on the chart. This is *not* the sorried `abelEnrichment_unique`: the
   arbitrary-base primitive `isMonHom_of_pointedIso_records`
   (`EllipticCurve/RecordGroupUnique.lean`, proved, via `modelGrpObj_unique`) says a pointed
   isomorphism of working records is a homomorphism of their group structures over any base.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

/-- **The conclusion shape of the relative theorem of the square.** For a morphism `f : Y ⟶ T`
and four morphisms `P Q R Z : T ⟶ Y` (in practice sections of `f`, but the property does not
need that): the two ideal-module products agree up to a line bundle pulled back from the base.

This is `Picard/SelfAdjointN.lean`'s `exists_invertible_tensor_idealModule_add` verbatim, with
the family and the four sections abstracted. -/
def IsSquareIdentity {Y T : Scheme.{u}} (f : Y ⟶ T) (P Q R Z : T ⟶ Y) : Prop :=
  ∃ N : T.Modules, IsInvertible N ∧
    Nonempty (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker P))
          (Scheme.Modules.idealModule (Scheme.Hom.ker Q)) ≅
      tensorObj (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker R))
          (Scheme.Modules.idealModule (Scheme.Hom.ker Z)))
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N))

/-- The base change of a section along `t : T ⟶ S`, in the explicit `pullback.lift` form the
ideal-module comparison lemmas are stated in. -/
noncomputable abbrev secBC {C S T : Scheme.{u}} {π : C ⟶ S} {z : S ⟶ C} (hz : z ≫ π = 𝟙 S)
    (t : T ⟶ S) : T ⟶ Limits.pullback π t :=
  Limits.pullback.lift (t ≫ z) (𝟙 T)
    (by rw [Category.assoc, hz, Category.comp_id, Category.id_comp])

/-- Pulling a module back from the base along the two legs of a fibre square agree:
`(pullback.fst π t)^* π^* N ≅ (pullback.snd π t)^* t^* N`. -/
theorem nonempty_pullback_fst_pullback_iso {C S T : Scheme.{u}} (π : C ⟶ S) (t : T ⟶ S)
    (N : S.Modules) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback (Limits.pullback.fst π t)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (Limits.pullback.snd π t)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback t).obj N)) :=
  ⟨(pullbackComp (Limits.pullback.fst π t) π).app N ≪≫
    (pullbackCongr (Limits.pullback.condition (f := π) (g := t))).app N ≪≫
    ((pullbackComp (Limits.pullback.snd π t) t).app N).symm⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[B3-step5, transport] The square identity base-changes.** For a separated smooth relative
curve `π` with four sections, the identity over `S` gives the identity over any `T ⟶ S`, with
base bundle `t^*N`. -/
theorem IsSquareIdentity.baseChange {C S T : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π) {P Q R Z : S ⟶ C}
    (hP : P ≫ π = 𝟙 S) (hQ : Q ≫ π = 𝟙 S) (hR : R ≫ π = 𝟙 S) (hZ : Z ≫ π = 𝟙 S)
    (t : T ⟶ S) (h : IsSquareIdentity π P Q R Z) :
    IsSquareIdentity (Limits.pullback.snd π t) (secBC hP t) (secBC hQ t) (secBC hR t)
      (secBC hZ t) := by
  obtain ⟨N, hN, he⟩ := h
  refine ⟨(AlgebraicGeometry.Scheme.Modules.pullback t).obj N, hN.pullback t, ⟨?_⟩⟩
  refine (nonempty_pullback_tensorObj_idealModule_pair hsm P Q hP hQ t).some.symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback (Limits.pullback.fst π t)).mapIso he.some ≪≫
    (nonempty_pullback_tensorObj (Limits.pullback.fst π t)
      (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker R))
        (Scheme.Modules.idealModule (Scheme.Hom.ker Z)))
      ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N)).some ≪≫
    tensorObjCongr (nonempty_pullback_tensorObj_idealModule_pair hsm R Z hR hZ t).some
      (nonempty_pullback_fst_pullback_iso π t N).some

/-! ### Transport along an isomorphism of families -/

/-- Pushing an ideal sheaf forward along an isomorphism is pulling it back along the inverse.
Both `comap α.hom` and `comap α.inv` are monotone and mutually inverse, so `comap α.inv` is a
right adjoint of `comap α.hom`; `map α.hom` is another one. -/
theorem IdealSheafData.map_eq_comap_inv {Y Y' : Scheme.{u}} (α : Y ≅ Y') (I : Y.IdealSheafData) :
    I.map α.hom = I.comap α.inv := by
  refine le_antisymm ?_ ?_
  · have h2 := Scheme.IdealSheafData.comap_mono α.inv
      (Scheme.IdealSheafData.comap_map_le I α.hom)
    dsimp only at h2
    rwa [← Scheme.IdealSheafData.comap_comp, α.inv_hom_id,
      Scheme.IdealSheafData.comap_id] at h2
  · have h3 := Scheme.IdealSheafData.le_map_comap (I.comap α.inv) α.hom
    rwa [← Scheme.IdealSheafData.comap_comp, α.hom_inv_id,
      Scheme.IdealSheafData.comap_id] at h3

/-- The kernel ideal of a morphism postcomposed with an isomorphism pulls back to the kernel
ideal of the morphism. -/
theorem IdealSheafData.comap_ker_comp_iso {Y Y' T : Scheme.{u}} (α : Y ≅ Y') (P : T ⟶ Y) :
    (Scheme.Hom.ker (P ≫ α.hom)).comap α.hom = Scheme.Hom.ker P := by
  rw [← Scheme.IdealSheafData.map_ker, IdealSheafData.map_eq_comap_inv,
    ← Scheme.IdealSheafData.comap_comp, α.hom_inv_id, Scheme.IdealSheafData.comap_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Ideal-module transport along a chart isomorphism.** For an isomorphism `α : Y ≅ Y'` of
total spaces lying over an isomorphism `γ : T ≅ T'` of bases, the ideal module of the section
`γ⁻¹ ≫ P ≫ α` of `f'` pulls back along `α` to the ideal module of the section `P` of `f`. -/
theorem nonempty_pullback_idealModule_ker_of_iso {Y T Y' T' : Scheme.{u}} {f : Y ⟶ T}
    {f' : Y' ⟶ T'} [IsSeparated f] [IsSeparated f'] (hsm : SmoothOfRelativeDimension 1 f)
    (hsm' : SmoothOfRelativeDimension 1 f') (α : Y ≅ Y') (γ : T ≅ T')
    (hα : α.hom ≫ f' = f ≫ γ.hom) {P : T ⟶ Y} (hP : P ≫ f = 𝟙 T) {P' : T' ⟶ Y'}
    (hPP : γ.inv ≫ P ≫ α.hom = P') :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback α.hom).obj
        (Scheme.Modules.idealModule (Scheme.Hom.ker P')) ≅
      Scheme.Modules.idealModule (Scheme.Hom.ker P)) := by
  have hker : (Scheme.Hom.ker P').comap α.hom = Scheme.Hom.ker P := by
    rw [← hPP, Scheme.Hom.ker_comp_of_isIso γ.inv (P ≫ α.hom),
      IdealSheafData.comap_ker_comp_iso]
  have h1 : P ≫ f ≫ γ.hom = γ.hom := by rw [← Category.assoc, hP, Category.id_comp]
  have hP' : P' ≫ f' = 𝟙 T' := by
    rw [← hPP, Category.assoc, Category.assoc, hα, h1, γ.inv_hom_id]
  have hJ := (ModularCurves.RelEffCartierDiv.sectionDivisor_isOfficial hsm' P'
    hP').locallyPrincipal
  have hJ' : ∀ c : ↥Y, ∃ V : Y.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(Y, V.1),
      ((Scheme.Hom.ker P').comap α.hom).ideal V = Ideal.span {g} ∧
        g ∈ nonZeroDivisors Γ(Y, V.1) := by
    rw [hker]
    exact (ModularCurves.RelEffCartierDiv.sectionDivisor_isOfficial hsm P hP).locallyPrincipal
  exact ⟨(AlgebraicGeometry.Scheme.Modules.nonempty_pullback_idealModule α.hom
    (Scheme.Hom.ker P') hJ hJ').some ≪≫ eqToIso (congrArg Scheme.Modules.idealModule hker)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[B3-step5, chart transport] The square identity transports along an isomorphism of
families.** If `α : Y ≅ Y'` lies over `γ : T ≅ T'` and carries the four sections of `f` to the
four sections of `f'`, then the identity for `f'` gives the identity for `f`, with base bundle
`γ^*N`. This is what turns the Weierstrass chart isomorphism of `LocallyWeierstrass` into a
statement about the original family. -/
theorem IsSquareIdentity.of_iso {Y T Y' T' : Scheme.{u}} {f : Y ⟶ T} {f' : Y' ⟶ T'}
    [IsSeparated f] [IsSeparated f'] (hsm : SmoothOfRelativeDimension 1 f)
    (hsm' : SmoothOfRelativeDimension 1 f') (α : Y ≅ Y') (γ : T ≅ T')
    (hα : α.hom ≫ f' = f ≫ γ.hom) {P Q R Z : T ⟶ Y} (hP : P ≫ f = 𝟙 T) (hQ : Q ≫ f = 𝟙 T)
    (hR : R ≫ f = 𝟙 T) (hZ : Z ≫ f = 𝟙 T) {P' Q' R' Z' : T' ⟶ Y'}
    (hPP : γ.inv ≫ P ≫ α.hom = P') (hQQ : γ.inv ≫ Q ≫ α.hom = Q')
    (hRR : γ.inv ≫ R ≫ α.hom = R') (hZZ : γ.inv ≫ Z ≫ α.hom = Z')
    (h : IsSquareIdentity f' P' Q' R' Z') :
    IsSquareIdentity f P Q R Z := by
  obtain ⟨N, hN, he⟩ := h
  refine ⟨(AlgebraicGeometry.Scheme.Modules.pullback γ.hom).obj N, hN.pullback γ.hom, ⟨?_⟩⟩
  refine tensorObjCongr
      (nonempty_pullback_idealModule_ker_of_iso hsm hsm' α γ hα hP hPP).some.symm
      (nonempty_pullback_idealModule_ker_of_iso hsm hsm' α γ hα hQ hQQ).some.symm ≪≫
    (nonempty_pullback_tensorObj α.hom (Scheme.Modules.idealModule (Scheme.Hom.ker P'))
      (Scheme.Modules.idealModule (Scheme.Hom.ker Q'))).some.symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback α.hom).mapIso he.some ≪≫
    (nonempty_pullback_tensorObj α.hom _ _).some ≪≫ tensorObjCongr
      ((nonempty_pullback_tensorObj α.hom (Scheme.Modules.idealModule (Scheme.Hom.ker R'))
          (Scheme.Modules.idealModule (Scheme.Hom.ker Z'))).some ≪≫
        tensorObjCongr (nonempty_pullback_idealModule_ker_of_iso hsm hsm' α γ hα hR hRR).some
          (nonempty_pullback_idealModule_ker_of_iso hsm hsm' α γ hα hZ hZZ).some)
      ((pullbackComp α.hom f').app N ≪≫ (pullbackCongr hα).app N ≪≫
        ((pullbackComp f γ.hom).app N).symm)

/-! ### The gluing bridge: restriction to `f ⁻¹ᵁ V` versus base change along `V.ι` -/

/-- The preimage of an open of the base is the base change of the family along that open:
`f ⁻¹ᵁ V ≅ Y ×_T V`. This is `isPullback_morphismRestrict` read as an isomorphism. -/
noncomputable def restrictOpensIso {Y T : Scheme.{u}} (f : Y ⟶ T) (V : T.Opens) :
    (f ⁻¹ᵁ V).toScheme ≅ Limits.pullback f V.ι :=
  (isPullback_morphismRestrict f V).flip.isoPullback

@[reassoc (attr := simp)]
theorem restrictOpensIso_hom_fst {Y T : Scheme.{u}} (f : Y ⟶ T) (V : T.Opens) :
    (restrictOpensIso f V).hom ≫ Limits.pullback.fst f V.ι = (f ⁻¹ᵁ V).ι :=
  (isPullback_morphismRestrict f V).flip.isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem restrictOpensIso_hom_snd {Y T : Scheme.{u}} (f : Y ⟶ T) (V : T.Opens) :
    (restrictOpensIso f V).hom ≫ Limits.pullback.snd f V.ι = f ∣_ V :=
  (isPullback_morphismRestrict f V).flip.isoPullback_hom_snd

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Restricting a module on the total space to `f ⁻¹ᵁ V` is pulling it back along the first
projection of `Y ×_T V`, transported along `restrictOpensIso`. -/
theorem nonempty_restrict_iso_pullback_fst {Y T : Scheme.{u}} (f : Y ⟶ T) (V : T.Opens)
    (M : Y.Modules) :
    Nonempty (M.restrict (f ⁻¹ᵁ V).ι ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (restrictOpensIso f V).hom).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback (Limits.pullback.fst f V.ι)).obj M)) :=
  ⟨(restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app M ≪≫
    (pullbackCongr (restrictOpensIso_hom_fst f V).symm).app M ≪≫
    ((pullbackComp (restrictOpensIso f V).hom (Limits.pullback.fst f V.ι)).app M).symm⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pulling a module back from `V` along the second projection of `Y ×_T V` and transporting
along `restrictOpensIso` is pulling it back along the restricted family `f ∣_ V`. -/
theorem nonempty_pullback_snd_iso_morphismRestrict {Y T : Scheme.{u}} (f : Y ⟶ T) (V : T.Opens)
    (N : V.toScheme.Modules) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback (restrictOpensIso f V).hom).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback (Limits.pullback.snd f V.ι)).obj N) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (f ∣_ V)).obj N) :=
  ⟨(pullbackComp (restrictOpensIso f V).hom (Limits.pullback.snd f V.ι)).app N ≪≫
    (pullbackCongr (restrictOpensIso_hom_snd f V)).app N⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The `f^*`-twist equivalence is Zariski-local on the base, in base-change presentation.**
`exists_pullback_twist_of_locally'` with its local input restated over `Y ×_T U i` instead of
`f ⁻¹ᵁ U i` — the presentation every base-change transport produces. -/
theorem exists_pullback_twist_of_locally_baseChange {Y T : Scheme.{u}} (f : Y ⟶ T)
    (hf : ∀ W : T.Opens, IsIso (f.app W)) {M M' : Y.Modules}
    (hM : IsInvertible M) (hM' : IsInvertible M')
    {ι : Type u} (U : ι → T.Opens) (hU : IsOpenCover U)
    (hloc : ∀ i, ∃ N : (U i).toScheme.Modules, IsInvertible N ∧
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
            (Limits.pullback.fst f (U i).ι)).obj M ≅
        tensorObj ((AlgebraicGeometry.Scheme.Modules.pullback
            (Limits.pullback.fst f (U i).ι)).obj M')
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (Limits.pullback.snd f (U i).ι)).obj N))) :
    ∃ N₀ : T.Modules, IsInvertible N₀ ∧
      Nonempty (M ≅ tensorObj M' ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N₀)) := by
  choose N hN he using hloc
  refine exists_pullback_twist_of_locally' f hf hM hM' U hU N hN fun i => ⟨?_⟩
  exact (nonempty_restrict_iso_pullback_fst f (U i) M).some ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback
      (restrictOpensIso f (U i)).hom).mapIso (he i).some ≪≫
    (nonempty_pullback_tensorObj (restrictOpensIso f (U i)).hom _ _).some ≪≫
    tensorObjCongr (nonempty_restrict_iso_pullback_fst f (U i) M').some.symm
      (nonempty_pullback_snd_iso_morphismRestrict f (U i) (N i)).some

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[B3-step5, gluing] The square identity is Zariski-local on the base.** If the identity
holds for the family base-changed to each member of an open cover of the base — with the four
sections base-changed — then it holds over the base.

The `hf` hypothesis is the section-component condition of the descent; `UniversallyOConnected`
supplies it (`UniversallyOConnected.isIso_app`). -/
theorem IsSquareIdentity.of_locally {Y T : Scheme.{u}} {f : Y ⟶ T} [IsSeparated f]
    (hsm : SmoothOfRelativeDimension 1 f) (hf : ∀ W : T.Opens, IsIso (f.app W))
    {P Q R Z : T ⟶ Y} (hP : P ≫ f = 𝟙 T) (hQ : Q ≫ f = 𝟙 T) (hR : R ≫ f = 𝟙 T)
    (hZ : Z ≫ f = 𝟙 T) {ι : Type u} (U : ι → T.Opens) (hU : IsOpenCover U)
    (hloc : ∀ i, IsSquareIdentity (Limits.pullback.snd f (U i).ι)
      (secBC hP (U i).ι) (secBC hQ (U i).ι) (secBC hR (U i).ι) (secBC hZ (U i).ι)) :
    IsSquareIdentity f P Q R Z := by
  refine exists_pullback_twist_of_locally_baseChange f hf
    ((isInvertible_idealModule_of_section hsm P hP).tensorObj
      (isInvertible_idealModule_of_section hsm Q hQ))
    ((isInvertible_idealModule_of_section hsm R hR).tensorObj
      (isInvertible_idealModule_of_section hsm Z hZ)) U hU fun i => ?_
  obtain ⟨N, hN, he⟩ := hloc i
  exact ⟨N, hN, ⟨(nonempty_pullback_tensorObj_idealModule_pair hsm P Q hP hQ (U i).ι).some ≪≫
    he.some ≪≫ tensorObjCongr
      (nonempty_pullback_tensorObj_idealModule_pair hsm R Z hR hZ (U i).ι).some.symm
      (Iso.refl _)⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[B3-step5, gluing — pointwise form]** `IsSquareIdentity.of_locally` with the cover
produced from a pointwise statement: an open neighbourhood of every point of the base over
which the base-changed identity holds. -/
theorem IsSquareIdentity.of_forall_exists_opens {Y T : Scheme.{u}} {f : Y ⟶ T} [IsSeparated f]
    (hsm : SmoothOfRelativeDimension 1 f) (hf : ∀ W : T.Opens, IsIso (f.app W))
    {P Q R Z : T ⟶ Y} (hP : P ≫ f = 𝟙 T) (hQ : Q ≫ f = 𝟙 T) (hR : R ≫ f = 𝟙 T)
    (hZ : Z ≫ f = 𝟙 T)
    (hloc : ∀ x : T, ∃ V : T.Opens, x ∈ V ∧ IsSquareIdentity (Limits.pullback.snd f V.ι)
      (secBC hP V.ι) (secBC hQ V.ι) (secBC hR V.ι) (secBC hZ V.ι)) :
    IsSquareIdentity f P Q R Z := by
  classical
  choose V hV hsq using hloc
  refine IsSquareIdentity.of_locally hsm hf hP hQ hR hZ V ?_ hsq
  refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun x => ?_)
  rw [TopologicalSpace.Opens.coe_iSup]
  exact Set.mem_iUnion.mpr ⟨x, hV x⟩

/-! ### The proved input: the Weierstrass model over a reduced Noetherian ring -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[B3-steps 2–4, in `IsSquareIdentity` form]** `TheoremOfSquareUniversal`'s
`exists_invertible_tensor_idealModule_add_projModel'` restated as `IsSquareIdentity`, with its
`⊗`-inverse datum supplied by the canonical dual. This is the exact input the chart leaf of
`IsSquareIdentity.of_forall_chart` has to be matched against: the two things it asks for beyond
the chart data are that the chart ring be **reduced and Noetherian** and that the third section
be the `mulModelHom`-sum of the first two. -/
theorem IsSquareIdentity.of_projModel {A : Type u} [CommRing A] [IsReduced A] [IsNoetherianRing A]
    {W₀ : WeierstrassCurve A} [W₀.IsElliptic]
    {P Q Rs : Spec (CommRingCat.of A) ⟶ projModel W₀} (hP : P ≫ projModelπ W₀ = 𝟙 _)
    (hQ : Q ≫ projModelπ W₀ = 𝟙 _) (hR : Rs ≫ projModelπ W₀ = 𝟙 _)
    (hRs : Rs = Limits.pullback.lift P Q (hP.trans hQ.symm) ≫ mulModelHom W₀) :
    IsSquareIdentity (projModelπ W₀) P Q Rs (projModelZero W₀) :=
  exists_invertible_tensor_idealModule_add_projModel' hP hQ hR hRs
    (dualObj (tensorObj (Scheme.Modules.idealModule (Scheme.Hom.ker P))
      (Scheme.Modules.idealModule (Scheme.Hom.ker Q))))
    (nonempty_eval_iso
      ((isInvertible_idealModule_of_section (projModel_smooth W₀) P hP).tensorObj
        (isInvertible_idealModule_of_section (projModel_smooth W₀) Q hQ)))

/-! ### The reduction to a Weierstrass chart -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[B3-step5, the reduction] From Weierstrass charts to an arbitrary base.** For a separated
smooth relative curve with four sections, whose zero section makes it locally Weierstrass, the
square identity follows from the square identity on every Weierstrass chart, for the three
non-zero sections read through the chart isomorphism.

This is the whole base-independent content of B3-step5: `LocallyWeierstrass` supplies the chart
around each point of the base, `IsSquareIdentity.of_iso` reads the chart statement back on the
base-changed family, and `IsSquareIdentity.of_forall_exists_opens` glues. What is left for the
consumer is a statement about `projModel W` over the ring `Γ(T, V)` of an affine open — the
shape `TheoremOfSquareUniversal`'s `exists_invertible_tensor_idealModule_add_projModel'` proves
(there, for a reduced Noetherian ring and with the third section pinned to `mulModelHom`). -/
theorem IsSquareIdentity.of_forall_chart {Y T : Scheme.{u}} {f : Y ⟶ T} [IsSeparated f]
    (hsm : SmoothOfRelativeDimension 1 f) (hf : ∀ W : T.Opens, IsIso (f.app W))
    {P Q R Z : T ⟶ Y} (hP : P ≫ f = 𝟙 T) (hQ : Q ≫ f = 𝟙 T) (hR : R ≫ f = 𝟙 T)
    (hZ : Z ≫ f = 𝟙 T) (hlw : LocallyWeierstrass f Z hZ)
    (hchart : ∀ (V : T.affineOpens) (W : WeierstrassCurve Γ(T, V.1)) (_ : W.IsElliptic)
      (e : Limits.pullback f V.1.ι ≅ projModel W),
      e.hom ≫ projModelπ W = Limits.pullback.snd f V.1.ι ≫ V.2.isoSpec.hom →
      V.2.isoSpec.inv ≫ secBC hZ V.1.ι ≫ e.hom = projModelZero W →
      IsSquareIdentity (projModelπ W) (V.2.isoSpec.inv ≫ secBC hP V.1.ι ≫ e.hom)
        (V.2.isoSpec.inv ≫ secBC hQ V.1.ι ≫ e.hom)
        (V.2.isoSpec.inv ≫ secBC hR V.1.ι ≫ e.hom) (projModelZero W)) :
    IsSquareIdentity f P Q R Z := by
  refine IsSquareIdentity.of_forall_exists_opens hsm hf hP hQ hR hZ fun x => ?_
  obtain ⟨V, hxV, W, hell, e, heπ, hez⟩ := hlw x
  refine ⟨V.1, hxV, ?_⟩
  haveI : IsSeparated (Limits.pullback.snd f V.1.ι) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) f V.1.ι ‹_›
  haveI : IsSeparated (projModelπ W) := inferInstance
  have hsmV : SmoothOfRelativeDimension 1 (Limits.pullback.snd f V.1.ι) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) f V.1.ι hsm
  refine IsSquareIdentity.of_iso hsmV (projModel_smooth W) e V.2.isoSpec heπ
    (Limits.pullback.lift_snd _ _ _) (Limits.pullback.lift_snd _ _ _)
    (Limits.pullback.lift_snd _ _ _) (Limits.pullback.lift_snd _ _ _) rfl rfl rfl
    (by rw [← hez, Category.assoc]) (hchart ⟨V.1, V.2⟩ W hell e heπ ?_)
  rw [← hez, Category.assoc]

end ModularCurves

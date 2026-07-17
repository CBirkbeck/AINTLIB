import ModularCurves.Picard.DualPullback.NaturalityCore

/-!
# Local pullback naturality

The remaining staged coherence proof for restriction of the local pullback comparison.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

theorem targetRestrictionEqF {U V : X.Opens} (i : V ⟶ U) :
    V.ι = X.homOfLE (leOfHom i) ≫ U.ι :=
  (X.homOfLE_ι (leOfHom i)).symm

theorem sourceRestrictionEqF (f : Y ⟶ X) {U V : X.Opens} (i : V ⟶ U) :
    (f ⁻¹ᵁ V).ι =
      Y.homOfLE (f.preimage_mono (leOfHom i)) ≫ (f ⁻¹ᵁ U).ι :=
  (Y.homOfLE_ι (f.preimage_mono (leOfHom i))).symm

theorem pastedRestrictionEqF (f : Y ⟶ X) {U V : X.Opens} (i : V ⟶ U) :
    (f ∣_ V) ≫ (X.homOfLE (leOfHom i) ≫ U.ι) =
      (Y.homOfLE (f.preimage_mono (leOfHom i)) ≫ (f ⁻¹ᵁ U).ι) ≫ f :=
  (Category.assoc (f ∣_ V) (X.homOfLE (leOfHom i)) U.ι).symm.trans
    ((congrArg (· ≫ U.ι)
      (morphismRestrict_homOfLE f V U (leOfHom i))).trans
      ((Category.assoc (Y.homOfLE (f.preimage_mono (leOfHom i)))
          (f ∣_ U) U.ι).trans
        ((congrArg (Y.homOfLE (f.preimage_mono (leOfHom i)) ≫ ·)
          (morphismRestrict_ι f U)).trans
          (Category.assoc (Y.homOfLE (f.preimage_mono (leOfHom i)))
            (f ⁻¹ᵁ U).ι f).symm)))

noncomputable def localPullbackNaturalitySquareBeforeF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  let x := X.homOfLE (leOfHom i)
  let y := Y.homOfLE (f.preimage_mono (leOfHom i))
  let yu := (f ⁻¹ᵁ U).ι
  let fu := f ∣_ U
  let fv := f ∣_ V
  (pullbackSquareIso fv x y fu
      (morphismRestrict_homOfLE f V U (leOfHom i))).hom.app
        ((pullback U.ι).obj M) ≫
    (pullback y).map
      ((pullbackSquareIso fu U.ι yu f
        (morphismRestrict_ι f U)).hom.app M)

noncomputable def localPullbackNaturalityPostSquareF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  let y := Y.homOfLE (f.preimage_mono (leOfHom i))
  let yu := (f ⁻¹ᵁ U).ι
  (pullback y).map
      ((restrictFunctorIsoPullback yu).inv.app ((pullback f).obj M)) ≫
    (restrictFunctorIsoPullback y).inv.app
      ((restrictFunctor yu).obj ((pullback f).obj M))

noncomputable def localPullbackNaturalityTailGroupedF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  localPullbackNaturalitySquareBeforeF f M i ≫
    localPullbackNaturalityPostSquareF f M i

theorem localPullbackNaturality_tail2_eq_groupedF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    localPullbackNaturalityTail2F f M i =
      localPullbackNaturalityTailGroupedF f M i := by
  simp only [localPullbackNaturalityTail2F,
    localPullbackNaturalityTailGroupedF,
    localPullbackNaturalitySquareBeforeF,
    localPullbackNaturalityPostSquareF, Category.assoc]

noncomputable def localPullbackNaturalityHeadAfterF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  localPullbackNaturalityPrefixF f M i ≫
    localPullbackNaturalityTargetAfterF f M i

noncomputable def localPullbackNaturalityMiddle2GroupedF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  localPullbackNaturalityHeadAfterF f M i ≫
    localPullbackNaturalityTailGroupedF f M i

theorem localPullbackNaturality_middle2_eq_groupedF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    localPullbackNaturalityMiddle2F f M i =
      localPullbackNaturalityMiddle2GroupedF f M i := by
  calc
    localPullbackNaturalityMiddle2F f M i =
        (localPullbackNaturalityPrefixF f M i ≫
          localPullbackNaturalityTargetAfterF f M i) ≫
            localPullbackNaturalityTail2F f M i :=
      (Category.assoc _ _ _).symm
    _ = localPullbackNaturalityHeadAfterF f M i ≫
          localPullbackNaturalityTail2F f M i := rfl
    _ = localPullbackNaturalityHeadAfterF f M i ≫
          localPullbackNaturalityTailGroupedF f M i :=
      congrArg (fun k => localPullbackNaturalityHeadAfterF f M i ≫ k)
        (localPullbackNaturality_tail2_eq_groupedF f M i)
    _ = localPullbackNaturalityMiddle2GroupedF f M i := rfl

noncomputable def localPullbackNaturalitySquareCoreF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  let x := X.homOfLE (leOfHom i)
  let y := Y.homOfLE (f.preimage_mono (leOfHom i))
  let yu := (f ⁻¹ᵁ U).ι
  let fv := f ∣_ V
  (pullback fv).map ((pullbackComp x U.ι).hom.app M) ≫
    (pullbackSquareIso fv (x ≫ U.ι) (y ≫ yu) f
      (pastedRestrictionEqF f i)).hom.app M

noncomputable def localPullbackNaturalitySquareSourceCompF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  let y := Y.homOfLE (f.preimage_mono (leOfHom i))
  let yu := (f ⁻¹ᵁ U).ι
  (pullbackComp y yu).inv.app ((pullback f).obj M)

noncomputable def localPullbackNaturalitySquareAfterF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  localPullbackNaturalitySquareCoreF f M i ≫
    localPullbackNaturalitySquareSourceCompF f M i

theorem localPullbackNaturality_squareBefore_eq_afterF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    localPullbackNaturalitySquareBeforeF f M i =
      localPullbackNaturalitySquareAfterF f M i := by
  exact pullbackSquareIso_vcomp_app
    (f ∣_ V) (X.homOfLE (leOfHom i))
      (Y.homOfLE (f.preimage_mono (leOfHom i))) (f ∣_ U)
      U.ι (f ⁻¹ᵁ U).ι f
      (morphismRestrict_homOfLE f V U (leOfHom i))
      (morphismRestrict_ι f U) M

noncomputable def localPullbackNaturalityMiddle3PastedF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  localPullbackNaturalityHeadAfterF f M i ≫
    localPullbackNaturalitySquareAfterF f M i ≫
    localPullbackNaturalityPostSquareF f M i

theorem localPullbackNaturality_grouped_eq_middle3PastedF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    localPullbackNaturalityMiddle2GroupedF f M i =
      localPullbackNaturalityMiddle3PastedF f M i :=
  congrArg
    (fun k => localPullbackNaturalityHeadAfterF f M i ≫ k ≫
      localPullbackNaturalityPostSquareF f M i)
    (localPullbackNaturality_squareBefore_eq_afterF f M i)

noncomputable def localPullbackNaturalitySourceBeforeF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  localPullbackNaturalitySquareSourceCompF f M i ≫
    localPullbackNaturalityPostSquareF f M i

noncomputable def localPullbackNaturalityMiddle3F (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  localPullbackNaturalityHeadAfterF f M i ≫
    localPullbackNaturalitySquareCoreF f M i ≫
    localPullbackNaturalitySourceBeforeF f M i

theorem localPullbackNaturality_middle3Pasted_eq_middle3F (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    localPullbackNaturalityMiddle3PastedF f M i =
      localPullbackNaturalityMiddle3F f M i := by
  exact congrArg
    (fun k => localPullbackNaturalityHeadAfterF f M i ≫ k)
    (Category.assoc
      (localPullbackNaturalitySquareCoreF f M i)
      (localPullbackNaturalitySquareSourceCompF f M i)
      (localPullbackNaturalityPostSquareF f M i))

noncomputable def localPullbackNaturalitySourceAfterF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  let y := Y.homOfLE (f.preimage_mono (leOfHom i))
  let yu := (f ⁻¹ᵁ U).ι
  (restrictFunctorIsoPullback (y ≫ yu)).inv.app ((pullback f).obj M) ≫
    (restrictFunctorComp y yu).hom.app ((pullback f).obj M)

theorem localPullbackNaturality_sourceBefore_eq_afterF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    localPullbackNaturalitySourceBeforeF f M i =
      localPullbackNaturalitySourceAfterF f M i := by
  exact restrictFunctorIsoPullback_comp_inv
    (Y.homOfLE (f.preimage_mono (leOfHom i))) (f ⁻¹ᵁ U).ι
      ((pullback f).obj M)

noncomputable def localPullbackNaturalityMiddle4F (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  localPullbackNaturalityHeadAfterF f M i ≫
    localPullbackNaturalitySquareCoreF f M i ≫
    localPullbackNaturalitySourceAfterF f M i

theorem localPullbackNaturality_middle3_eq_middle4F (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    localPullbackNaturalityMiddle3F f M i =
      localPullbackNaturalityMiddle4F f M i :=
  congrArg
    (fun k => localPullbackNaturalityHeadAfterF f M i ≫
      localPullbackNaturalitySquareCoreF f M i ≫ k)
    (localPullbackNaturality_sourceBefore_eq_afterF f M i)

noncomputable def localPullbackNaturalityCongrMapF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  (pullback (f ∣_ V)).map
    ((restrictFunctorCongr (targetRestrictionEqF i)).hom.app M)

noncomputable def localPullbackNaturalityRestrictCompMapF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  (pullback (f ∣_ V)).map
    ((restrictFunctorComp (X.homOfLE (leOfHom i)) U.ι).hom.app M)

noncomputable def localPullbackNaturalityPullbackCompTargetMapF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  (pullback (f ∣_ V)).map
    ((pullbackComp (X.homOfLE (leOfHom i)) U.ι).hom.app M)

noncomputable def localPullbackNaturalitySquareIsoCoreF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  (pullbackSquareIso (f ∣_ V)
    (X.homOfLE (leOfHom i) ≫ U.ι)
    (Y.homOfLE (f.preimage_mono (leOfHom i)) ≫ (f ⁻¹ᵁ U).ι) f
    (pastedRestrictionEqF f i)).hom.app M

noncomputable def localPullbackNaturalityTargetCompBeforeF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  localPullbackNaturalityRestrictCompMapF f M i ≫
    localPullbackNaturalityTargetAfterF f M i ≫
    localPullbackNaturalityPullbackCompTargetMapF f M i

noncomputable def localPullbackNaturalityTargetCompAfterF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  (pullback (f ∣_ V)).map
    ((restrictFunctorIsoPullback
      (X.homOfLE (leOfHom i) ≫ U.ι)).hom.app M)

theorem localPullbackNaturality_targetCompBefore_eq_afterF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    localPullbackNaturalityTargetCompBeforeF f M i =
      localPullbackNaturalityTargetCompAfterF f M i := by
  let x := X.homOfLE (leOfHom i)
  let fv := f ∣_ V
  let rU := (restrictFunctorIsoPullback U.ι).hom.app M
  let rxU' := (restrictFunctorIsoPullback x).hom.app
    ((pullback U.ι).obj M)
  let pX := (pullbackComp x U.ι).hom.app M
  let rhoCompX := (restrictFunctorIsoPullback (x ≫ U.ι)).hom.app M
  change (pullback fv).map ((restrictFunctorComp x U.ι).hom.app M) ≫
      (pullback fv).map ((restrictFunctor x).map rU) ≫
      (pullback fv).map rxU' ≫ (pullback fv).map pX =
    (pullback fv).map rhoCompX
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (pullback fv).map
    (restrictFunctorIsoPullback_comp x U.ι M)

noncomputable def localPullbackNaturalityTargetHeadBeforeF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  localPullbackNaturalityCongrMapF f M i ≫
    localPullbackNaturalityTargetCompBeforeF f M i

noncomputable def localPullbackNaturalityTargetHeadAfterF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  localPullbackNaturalityCongrMapF f M i ≫
    localPullbackNaturalityTargetCompAfterF f M i

noncomputable def localPullbackNaturalityMiddle4TargetF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  localPullbackNaturalityTargetHeadBeforeF f M i ≫
    localPullbackNaturalitySquareIsoCoreF f M i ≫
    localPullbackNaturalitySourceAfterF f M i

theorem localPullbackNaturality_middle4_eq_targetF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    localPullbackNaturalityMiddle4F f M i =
      localPullbackNaturalityMiddle4TargetF f M i := by
  let a := localPullbackNaturalityCongrMapF f M i
  let b := localPullbackNaturalityRestrictCompMapF f M i
  let c := localPullbackNaturalityTargetAfterF f M i
  let d := localPullbackNaturalityPullbackCompTargetMapF f M i
  let e := localPullbackNaturalitySquareIsoCoreF f M i
  let q := localPullbackNaturalitySourceAfterF f M i
  change a ≫ b ≫ c ≫ (d ≫ e) ≫ q = a ≫ (b ≫ c ≫ d) ≫ e ≫ q
  simp only [Category.assoc]

noncomputable def localPullbackNaturalityMiddle5F (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  localPullbackNaturalityTargetHeadAfterF f M i ≫
    localPullbackNaturalitySquareIsoCoreF f M i ≫
    localPullbackNaturalitySourceAfterF f M i

theorem localPullbackNaturality_middle4Target_eq_middle5F (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    localPullbackNaturalityMiddle4TargetF f M i =
      localPullbackNaturalityMiddle5F f M i := by
  have hhead : localPullbackNaturalityTargetHeadBeforeF f M i =
      localPullbackNaturalityTargetHeadAfterF f M i :=
    congrArg (fun k => localPullbackNaturalityCongrMapF f M i ≫ k)
      (localPullbackNaturality_targetCompBefore_eq_afterF f M i)
  exact congrArg
    (fun k => k ≫ localPullbackNaturalitySquareIsoCoreF f M i ≫
      localPullbackNaturalitySourceAfterF f M i) hhead

noncomputable def localPullbackNaturalityRhoVMapF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (_i : V ⟶ U) :=
  (pullback (f ∣_ V)).map
    ((restrictFunctorIsoPullback V.ι).hom.app M)

noncomputable def localPullbackNaturalityPullbackCongrTargetMapF
    (f : Y ⟶ X) (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  (pullback (f ∣_ V)).map
    ((pullbackCongr (targetRestrictionEqF i)).hom.app M)

noncomputable def localPullbackNaturalityCanonicalHeadF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  localPullbackNaturalityRhoVMapF f M i ≫
    localPullbackNaturalityPullbackCongrTargetMapF f M i

theorem localPullbackNaturality_targetHeadAfter_eq_canonicalHeadF
    (f : Y ⟶ X) (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    localPullbackNaturalityTargetHeadAfterF f M i =
      localPullbackNaturalityCanonicalHeadF f M i := by
  let fv := f ∣_ V
  have h := restrictFunctorIsoPullback_congr (targetRestrictionEqF i) M
  change (pullback fv).map
        ((restrictFunctorCongr (targetRestrictionEqF i)).hom.app M) ≫
      (pullback fv).map ((restrictFunctorIsoPullback
        (X.homOfLE (leOfHom i) ≫ U.ι)).hom.app M) =
    (pullback fv).map ((restrictFunctorIsoPullback V.ι).hom.app M) ≫
      (pullback fv).map
        ((pullbackCongr (targetRestrictionEqF i)).hom.app M)
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (pullback fv).map h

noncomputable def localPullbackNaturalityCanonicalF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  localPullbackNaturalityCanonicalHeadF f M i ≫
    localPullbackNaturalitySquareIsoCoreF f M i ≫
    localPullbackNaturalitySourceAfterF f M i

theorem localPullbackNaturality_middle5_eq_canonicalF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    localPullbackNaturalityMiddle5F f M i =
      localPullbackNaturalityCanonicalF f M i :=
  congrArg
    (fun k => k ≫ localPullbackNaturalitySquareIsoCoreF f M i ≫
      localPullbackNaturalitySourceAfterF f M i)
    (localPullbackNaturality_targetHeadAfter_eq_canonicalHeadF f M i)

noncomputable def localPullbackNaturalitySourceCongrExpandedF
    (f : Y ⟶ X) (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  (pullbackCongr (sourceRestrictionEqF f i)).inv.app ((pullback f).obj M) ≫
    (restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).inv.app ((pullback f).obj M) ≫
    (restrictFunctorCongr (sourceRestrictionEqF f i)).hom.app
      ((pullback f).obj M)

noncomputable def localPullbackNaturalitySourceExpandedTailF
    (f : Y ⟶ X) (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  localPullbackNaturalitySourceCongrExpandedF f M i ≫
    (restrictFunctorComp
      (Y.homOfLE (f.preimage_mono (leOfHom i))) (f ⁻¹ᵁ U).ι).hom.app
        ((pullback f).obj M)

theorem localPullbackNaturality_sourceAfter_eq_expandedTailF
    (f : Y ⟶ X) (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    localPullbackNaturalitySourceAfterF f M i =
      localPullbackNaturalitySourceExpandedTailF f M i := by
  have h := restrictFunctorIsoPullback_congr_inv
    (sourceRestrictionEqF f i) ((pullback f).obj M)
  exact congrArg
    (fun k => k ≫ (restrictFunctorComp
      (Y.homOfLE (f.preimage_mono (leOfHom i))) (f ⁻¹ᵁ U).ι).hom.app
        ((pullback f).obj M)) h.symm

noncomputable def localPullbackNaturalitySourceExpandedF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  localPullbackNaturalityCanonicalHeadF f M i ≫
    localPullbackNaturalitySquareIsoCoreF f M i ≫
    localPullbackNaturalitySourceExpandedTailF f M i

theorem localPullbackNaturality_canonical_eq_sourceExpandedF
    (f : Y ⟶ X) (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    localPullbackNaturalityCanonicalF f M i =
      localPullbackNaturalitySourceExpandedF f M i :=
  congrArg
    (fun k => localPullbackNaturalityCanonicalHeadF f M i ≫
      localPullbackNaturalitySquareIsoCoreF f M i ≫ k)
    (localPullbackNaturality_sourceAfter_eq_expandedTailF f M i)

noncomputable def localPullbackNaturalitySquareCongrBeforeF
    (f : Y ⟶ X) (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  (Functor.isoWhiskerRight (pullbackCongr (targetRestrictionEqF i))
      (pullback (f ∣_ V)) ≪≫
    pullbackSquareIso (f ∣_ V)
      (X.homOfLE (leOfHom i) ≫ U.ι)
      (Y.homOfLE (f.preimage_mono (leOfHom i)) ≫ (f ⁻¹ᵁ U).ι) f
      (pastedRestrictionEqF f i) ≪≫
    Functor.isoWhiskerLeft (pullback f)
      (pullbackCongr (sourceRestrictionEqF f i)).symm).hom.app M

noncomputable def localPullbackNaturalityDirectTailF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  (restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).inv.app ((pullback f).obj M) ≫
    (restrictFunctorCongr (sourceRestrictionEqF f i)).hom.app
      ((pullback f).obj M) ≫
    (restrictFunctorComp
      (Y.homOfLE (f.preimage_mono (leOfHom i))) (f ⁻¹ᵁ U).ι).hom.app
        ((pullback f).obj M)

noncomputable def localPullbackNaturalityExpandedF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  localPullbackNaturalityRhoVMapF f M i ≫
    localPullbackNaturalitySquareCongrBeforeF f M i ≫
    localPullbackNaturalityDirectTailF f M i

theorem localPullbackNaturality_sourceExpanded_eq_expandedF
    (f : Y ⟶ X) (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    localPullbackNaturalitySourceExpandedF f M i =
      localPullbackNaturalityExpandedF f M i := by
  simp only [localPullbackNaturalitySourceExpandedF,
    localPullbackNaturalityExpandedF,
    localPullbackNaturalityCanonicalHeadF,
    localPullbackNaturalitySourceExpandedTailF,
    localPullbackNaturalitySourceCongrExpandedF,
    localPullbackNaturalitySquareCongrBeforeF,
    localPullbackNaturalityDirectTailF,
    Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Category.assoc]
  congr 1

noncomputable def localPullbackNaturalitySquareCongrAfterF
    (f : Y ⟶ X) (M : X.Modules) {U V : X.Opens} (_i : V ⟶ U) :=
  (pullbackSquareIso (f ∣_ V) V.ι (f ⁻¹ᵁ V).ι f
    (morphismRestrict_ι f V)).hom.app M

theorem localPullbackNaturality_squareCongrBefore_eq_afterF
    (f : Y ⟶ X) (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    localPullbackNaturalitySquareCongrBeforeF f M i =
      localPullbackNaturalitySquareCongrAfterF f M i := by
  have h := congrArg (fun e => e.hom.app M)
    (pullbackSquareIso_congr (f ∣_ V) f
      (targetRestrictionEqF i) (sourceRestrictionEqF f i)
      (morphismRestrict_ι f V) (pastedRestrictionEqF f i))
  exact h

noncomputable def localPullbackNaturalityRightNormalF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :=
  localPullbackNaturalityRhoVMapF f M i ≫
    localPullbackNaturalitySquareCongrAfterF f M i ≫
    localPullbackNaturalityDirectTailF f M i

theorem localPullbackNaturality_expanded_eq_rightNormalF
    (f : Y ⟶ X) (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    localPullbackNaturalityExpandedF f M i =
      localPullbackNaturalityRightNormalF f M i :=
  congrArg
    (fun k => localPullbackNaturalityRhoVMapF f M i ≫ k ≫
      localPullbackNaturalityDirectTailF f M i)
    (localPullbackNaturality_squareCongrBefore_eq_afterF f M i)

theorem localPullbackNaturality_rightNormal_eq_rightF
    (f : Y ⟶ X) (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    localPullbackNaturalityRightNormalF f M i =
      (localPullbackRestrictIsoF f M V).hom ≫
        (restrictOpenCompIsoF
          ((TopologicalSpace.Opens.map f.base).map i)).hom.app
            ((pullback f).obj M) := by
  simp only [localPullbackNaturalityRightNormalF,
    localPullbackNaturalityRhoVMapF,
    localPullbackNaturalitySquareCongrAfterF,
    localPullbackNaturalityDirectTailF,
    localPullbackRestrictIsoF, restrictOpenCompIsoF,
    Iso.trans_hom, NatTrans.comp_app, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc]
  congr 1

theorem localPullbackRestrictIso_naturalityF (f : Y ⟶ X)
    (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    (pullback (f ∣_ V)).map ((restrictOpenCompIsoF i).hom.app M) ≫
        (openPullbackRestrictIsoF f i).hom.app
          ((restrictFunctor U.ι).obj M) ≫
        (restrictFunctor
          (Y.homOfLE (f.preimage_mono (leOfHom i)))).map
            (localPullbackRestrictIsoF f M U).hom =
      (localPullbackRestrictIsoF f M V).hom ≫
        (restrictOpenCompIsoF
          ((TopologicalSpace.Opens.map f.base).map i)).hom.app
            ((pullback f).obj M) := by
  calc
    _ = localPullbackNaturalityMiddle1F f M i :=
      localPullbackNaturality_left_eq_middle1F f M i
    _ = localPullbackNaturalityMiddle1aF f M i :=
      localPullbackNaturality_middle1_eq_middle1aF f M i
    _ = localPullbackNaturalityMiddle2F f M i :=
      localPullbackNaturality_middle1a_eq_middle2F f M i
    _ = localPullbackNaturalityMiddle2GroupedF f M i :=
      localPullbackNaturality_middle2_eq_groupedF f M i
    _ = localPullbackNaturalityMiddle3PastedF f M i :=
      localPullbackNaturality_grouped_eq_middle3PastedF f M i
    _ = localPullbackNaturalityMiddle3F f M i :=
      localPullbackNaturality_middle3Pasted_eq_middle3F f M i
    _ = localPullbackNaturalityMiddle4F f M i :=
      localPullbackNaturality_middle3_eq_middle4F f M i
    _ = localPullbackNaturalityMiddle4TargetF f M i :=
      localPullbackNaturality_middle4_eq_targetF f M i
    _ = localPullbackNaturalityMiddle5F f M i :=
      localPullbackNaturality_middle4Target_eq_middle5F f M i
    _ = localPullbackNaturalityCanonicalF f M i :=
      localPullbackNaturality_middle5_eq_canonicalF f M i
    _ = localPullbackNaturalitySourceExpandedF f M i :=
      localPullbackNaturality_canonical_eq_sourceExpandedF f M i
    _ = localPullbackNaturalityExpandedF f M i :=
      localPullbackNaturality_sourceExpanded_eq_expandedF f M i
    _ = localPullbackNaturalityRightNormalF f M i :=
      localPullbackNaturality_expanded_eq_rightNormalF f M i
    _ = _ := localPullbackNaturality_rightNormal_eq_rightF f M i

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.EllipticCurve.PoleSheafProjectiveBaseChange
import ModularCurves.ForMathlib.ProjectiveFactorizationFiniteSections
import ModularCurves.ForMathlib.RelativeProjectiveAffineFactorization
import ModularCurves.ForMathlib.SchemeModuleRestrictPushforward

/-!
# Finite-type pushforwards along relative projective factorizations

Over a locally Noetherian base, the pushforward of a finite-type quasicoherent module along a
relative projective factorization is finite type.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction along an open immersion preserves finite-type quasicoherent modules. -/
theorem isFiniteType_restrict_of_isOpenImmersion
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i]
    (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    (M.restrict i).IsFiniteType := by
  let N := M.restrict i
  letI : N.IsQuasicoherent := inferInstance
  apply isFiniteType_of_sections_module_finite N
  intro U
  let V : Y.affineOpens :=
    ⟨i ''ᵁ U.1, U.2.image_of_isOpenImmersion i⟩
  have hfinite : Module.Finite Γ(Y, V.1) Γ(M, V.1) :=
    sections_module_finite_of_isFiniteType_of_isAffineOpen M V
  let σ : Γ(X, U.1) →+* Γ(Y, i ''ᵁ U.1) :=
    (i.appIso U.1).inv.hom
  letI : RingHomSurjective σ :=
    ⟨(i.appIso U.1).symm.commRingCatIsoToRingEquiv.surjective⟩
  let e : Γ(N, U.1) →ₛₗ[σ] Γ(M, i ''ᵁ U.1) :=
    { toFun := (M.restrictAppIso i U.1).hom
      map_add' := (M.restrictAppIso i U.1).hom.hom.map_add
      map_smul' := by
        intro r x
        exact smul_restrictAppIso_hom_apply i M U.1 r x }
  have he : Function.Bijective e :=
    ConcreteCategory.bijective_of_isIso (M.restrictAppIso i U.1).hom
  exact (e.finite_iff_of_bijective he).mpr hfinite

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.IsRelativeProjectiveFactorization

private theorem baseSections_module_finite_of_comp_isIso
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsIso g]
    (M : X.Modules)
    [Module.Finite Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections (f ≫ g) M)] :
    Module.Finite Γ(Y, (⊤ : Y.Opens))
      (Scheme.Modules.baseSections f M) := by
  let eComp := Scheme.Modules.baseSectionsCompIso f g M
  have hRestrict : Module.Finite Γ(S, (⊤ : S.Opens))
      ((ModuleCat.restrictScalars g.appTop.hom).obj
        (Scheme.Modules.baseSections f M)) :=
    Module.Finite.equiv eComp.symm.toLinearEquiv
  let σ : Γ(S, (⊤ : S.Opens)) →+* Γ(Y, (⊤ : Y.Opens)) :=
    g.appTop.hom
  letI : IsIso g.appTop :=
    inferInstanceAs (IsIso (Scheme.Γ.map g.op))
  letI : RingHomSurjective σ :=
    ⟨(ConcreteCategory.bijective_of_isIso g.appTop).surjective⟩
  let e :
      ((ModuleCat.restrictScalars σ).obj
          (Scheme.Modules.baseSections f M) : Type u) →ₛₗ[σ]
        (Scheme.Modules.baseSections f M : Type u) :=
    { toFun := id
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; rfl }
  exact (e.finite_iff_of_bijective Function.bijective_id).mp hRestrict

private theorem restrictedBaseSections_module_finite
    {k : Type u} [CommRing k] {X S : Scheme.{u}}
    {s : S ⟶ Spec (.of k)} {f : X ⟶ S}
    [IsLocallyNoetherian S]
    (h : IsRelativeProjectiveFactorization s f)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (U : S.affineOpens) :
    Module.Finite Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))
      (Scheme.Modules.baseSections (morphismRestrict f U.1)
        (M.restrict (f ⁻¹ᵁ U.1).ι)) := by
  letI : IsNoetherianRing Γ(S, U.1) :=
    IsLocallyNoetherian.component_noetherian U
  letI : Algebra k Γ(S, U.1) :=
    (affineOpenCoefficientMap s U.1 U.2).hom.toAlgebra
  let fU := morphismRestrict f U.1
  let MU := M.restrict (f ⁻¹ᵁ U.1).ι
  letI : MU.IsFiniteType :=
    Scheme.Modules.isFiniteType_restrict_of_isOpenImmersion
      (f ⁻¹ᵁ U.1).ι M
  let hf := h.isProjectiveFactorization_affineOpen U.1 U.2
  have hfinite : Module.Finite
      Γ(Spec (.of Γ(S, U.1)), (⊤ : (Spec (.of Γ(S, U.1))).Opens))
      (Scheme.Modules.baseSections (fU ≫ U.2.isoSpec.hom) MU) :=
    hf.baseSections_module_finite MU
  letI : Module.Finite
      Γ(Spec (.of Γ(S, U.1)), (⊤ : (Spec (.of Γ(S, U.1))).Opens))
      (Scheme.Modules.baseSections (fU ≫ U.2.isoSpec.hom) MU) :=
    hfinite
  exact baseSections_module_finite_of_comp_isIso
    fU U.2.isoSpec.hom MU

private theorem pushforward_sections_module_finite
    {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    (U : S.affineOpens)
    [Module.Finite Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))
      (Scheme.Modules.baseSections (morphismRestrict f U.1)
        (M.restrict (f ⁻¹ᵁ U.1).ι))] :
    Module.Finite Γ(S, U.1)
      Γ((Scheme.Modules.pushforward f).obj M, U.1) := by
  let V := f ⁻¹ᵁ U.1
  let fU := morphismRestrict f U.1
  let MU := M.restrict V.ι
  let P := (Scheme.Modules.pushforward fU).obj MU
  let N := (Scheme.Modules.pushforward f).obj M
  let C := Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))
  have hbase : Module.Finite C (Scheme.Modules.baseSections fU MU) :=
    inferInstance
  let ePush := Scheme.Modules.baseSectionsPushforwardTopIso fU MU
  have hbasePresheaf : Module.Finite C
      ((Scheme.Modules.baseModulePresheaf (𝟙 U.1.toScheme) P).obj
        (Opposite.op (⊤ : U.1.toScheme.Opens))) :=
    Module.Finite.equiv ePush.toLinearEquiv
  let eId : ModuleCat.of C Γ(P, (⊤ : U.1.toScheme.Opens)) ≅
      (Scheme.Modules.baseModulePresheaf (𝟙 U.1.toScheme) P).obj
        (Opposite.op (⊤ : U.1.toScheme.Opens)) := by
    refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    ext (x : Γ(P, (⊤ : U.1.toScheme.Opens)))
    change U.1.toScheme.presheaf.map (homOfLE le_rfl).op
        ((Scheme.Hom.appTop (𝟙 U.1.toScheme)).hom r) • x = r • x
    rw [Scheme.Hom.id_appTop]
    rw [Subsingleton.elim (homOfLE le_rfl).op (𝟙 _)]
    rw [CategoryTheory.Functor.map_id]
    rfl
  letI : Module.Finite C
      ((Scheme.Modules.baseModulePresheaf (𝟙 U.1.toScheme) P).obj
        (Opposite.op (⊤ : U.1.toScheme.Opens))) :=
    hbasePresheaf
  have hP : Module.Finite C Γ(P, (⊤ : U.1.toScheme.Opens)) :=
    Module.Finite.equiv eId.symm.toLinearEquiv
  let eRestrict :=
    Scheme.Modules.restrictPushforwardIsoOfIsPullbackApp
      f fU V.ι U.1.ι (isPullback_morphismRestrict f U.1) M
  let eTop :
      Γ(P, (⊤ : U.1.toScheme.Opens)) ≃ₗ[C]
        Γ(N.restrict U.1.ι, (⊤ : U.1.toScheme.Opens)) :=
    { toFun := fun x => eRestrict.inv.val.app
          (Opposite.op (⊤ : U.1.toScheme.Opens)) x
      invFun := fun x => eRestrict.hom.val.app
          (Opposite.op (⊤ : U.1.toScheme.Opens)) x
      map_add' := by
        intro x y
        exact (eRestrict.inv.val.app
          (Opposite.op (⊤ : U.1.toScheme.Opens))).hom.map_add x y
      map_smul' := by
        intro r x
        exact (eRestrict.inv.val.app
          (Opposite.op (⊤ : U.1.toScheme.Opens))).hom.map_smul r x
      left_inv := by
        intro x
        have hx := ConcreteCategory.congr_hom
          (congrArg
            (fun q => q.val.app
              (Opposite.op (⊤ : U.1.toScheme.Opens)))
            eRestrict.inv_hom_id)
          (show
            ((Scheme.Modules.pushforward fU).obj
              ((Scheme.Modules.restrictFunctor V.ι).obj M)).val.obj
                (Opposite.op (⊤ : U.1.toScheme.Opens))
            from x)
        change eRestrict.hom.val.app
          (Opposite.op (⊤ : U.1.toScheme.Opens))
            (eRestrict.inv.val.app
              (Opposite.op (⊤ : U.1.toScheme.Opens)) x) = x at hx
        exact hx
      right_inv := by
        intro x
        have hx := ConcreteCategory.congr_hom
          (congrArg
            (fun q => q.val.app
              (Opposite.op (⊤ : U.1.toScheme.Opens)))
            eRestrict.hom_inv_id)
          (show
            ((Scheme.Modules.restrictFunctor U.1.ι).obj
              ((Scheme.Modules.pushforward f).obj M)).val.obj
                (Opposite.op (⊤ : U.1.toScheme.Opens))
            from x)
        change eRestrict.inv.val.app
          (Opposite.op (⊤ : U.1.toScheme.Opens))
            (eRestrict.hom.val.app
              (Opposite.op (⊤ : U.1.toScheme.Opens)) x) = x at hx
        exact hx }
  letI : Module.Finite C Γ(P, (⊤ : U.1.toScheme.Opens)) := hP
  have hRestrict : Module.Finite C
      Γ(N.restrict U.1.ι, (⊤ : U.1.toScheme.Opens)) :=
    Module.Finite.equiv eTop
  let σ : C →+* Γ(S, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)) :=
    (U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv.hom
  letI : IsIso (U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv :=
    (U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).isIso_inv
  letI : RingHomSurjective σ :=
    ⟨(ConcreteCategory.bijective_of_isIso
      (U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv).surjective⟩
  let e :
      Γ(N.restrict U.1.ι, (⊤ : U.1.toScheme.Opens)) →ₛₗ[σ]
        Γ(N, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)) :=
    { toFun := (N.restrictAppIso U.1.ι
          (⊤ : U.1.toScheme.Opens)).hom
      map_add' := (N.restrictAppIso U.1.ι
        (⊤ : U.1.toScheme.Opens)).hom.hom.map_add
      map_smul' := by
        intro r x
        exact Scheme.Modules.smul_restrictAppIso_hom_apply
          U.1.ι N (⊤ : U.1.toScheme.Opens) r x }
  have he : Function.Bijective e :=
    ConcreteCategory.bijective_of_isIso
      (N.restrictAppIso U.1.ι (⊤ : U.1.toScheme.Opens)).hom
  have htarget : Module.Finite
      Γ(S, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))
      Γ(N, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)) :=
    (e.finite_iff_of_bijective he).mp hRestrict
  rw [U.1.ι_image_top] at htarget
  exact htarget

end AlgebraicGeometry.IsRelativeProjectiveFactorization

namespace AlgebraicGeometry.Scheme.Modules

/-- Pushforward along a proper morphism preserves quasicoherent modules. -/
theorem isQuasicoherent_pushforward_of_isProper
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  have hlocal (U : S.affineOpens) :
      (((pushforward f).obj M).over U.1).IsQuasicoherent := by
    let V := f ⁻¹ᵁ U.1
    let fU := morphismRestrict f U.1
    let MU := M.restrict V.ι
    letI : IsAffine U.1.toScheme := U.2
    letI : IsProper fU := by infer_instance
    have hPush :
        ((pushforward fU).obj MU).IsQuasicoherent :=
      isQuasicoherent_pushforward_of_isProper_to_affine fU MU
    have hRestrict :
        (((pushforward f).obj M).restrict U.1.ι).IsQuasicoherent :=
      (isQuasicoherent U.1).prop_of_iso
        (restrictPushforwardIsoOfIsPullbackApp
          f fU V.ι U.1.ι
          (isPullback_morphismRestrict f U.1) M).symm
        hPush
    letI :
        (((pushforward f).obj M).restrict U.1.ι).IsQuasicoherent :=
      hRestrict
    exact isQuasicoherent_over_of_restrict_of_isAffineOpen
      ((pushforward f).obj M) U.1
  have hcover : (Opens.grothendieckTopology S).CoversTop
      (fun U : S.affineOpens => (U : S.Opens)) := by
    rw [Opens.coversTop_iff, IsOpenCover, iSup_affineOpens_eq_top S]
  exact @SheafOfModules.IsQuasicoherent.of_coversTop
    _ _ _ _ _ _ _ _ ((pushforward f).obj M) _
      (fun U : S.affineOpens => (U : S.Opens)) hcover hlocal

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.IsRelativeProjectiveFactorization

/-- The pushforward of a finite-type quasicoherent module along a relative
projective factorization over a locally Noetherian base is finite type. -/
theorem isFiniteType_pushforward
    {k : Type u} [CommRing k] {X S : Scheme.{u}}
    {s : S ⟶ Spec (.of k)} {f : X ⟶ S}
    [IsLocallyNoetherian S]
    (h : IsRelativeProjectiveFactorization s f)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ((Scheme.Modules.pushforward f).obj M).IsFiniteType := by
  let N := (Scheme.Modules.pushforward f).obj M
  letI : IsProper f := h.isProper
  letI : N.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pushforward_of_isProper f M
  apply Scheme.Modules.isFiniteType_of_sections_module_finite N
  intro U
  letI : Module.Finite
      Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))
      (Scheme.Modules.baseSections (morphismRestrict f U.1)
        (M.restrict (f ⁻¹ᵁ U.1).ι)) :=
    restrictedBaseSections_module_finite h M U
  exact pushforward_sections_module_finite f M U

end AlgebraicGeometry.IsRelativeProjectiveFactorization

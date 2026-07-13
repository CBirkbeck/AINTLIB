import ModularCurves.ForMathlib.AffineModulePatchBaseChange

/-!
# Naturality of affine module patch base change

The affine-patch module comparison commutes with restriction to a smaller
affine source patch.  This is the compatibility needed to assemble the
patchwise comparisons into a base-linear Cech complex.
-/

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace TensorProduct
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry.Scheme.Modules

private theorem two_comp_apply {R : Type u} [CommRing R]
    {A B C : ModuleCat.{u} R} (a : A ⟶ B) (b : B ⟶ C) (x : A) :
    (a ≫ b) x = b (a x) := by
  rfl

private theorem eq_of_eq_same {A : Sort u} {a b c : A}
    (ha : a = c) (hb : b = c) : a = b :=
  ha.trans hb.symm

private theorem extendScalars_hom_ext
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    {a b : (ModuleCat.extendScalars f).obj M ⟶ N}
    (h : ∀ m : M,
      a ((1 : S) ⊗ₜ[R, f] m) = b ((1 : S) ⊗ₜ[R, f] m)) : a = b := by
  exact ModuleCat.ExtendScalars.hom_ext h

/-- The affine-patch module base-change comparison commutes with restriction
between affine source patches. -/
theorem affineModuleSectionsBaseChangeIso_naturality
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    {U V : X.Opens} (hVU : V ≤ U) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) [IsAffine S] [IsAffine T]
    [M.IsQuasicoherent] :
    (ModuleCat.extendScalars t.appTop.hom).map
          ((baseModulePresheaf f M).map (homOfLE hVU).op) ≫
        (affineModuleSectionsBaseChangeIso f t M V hV).hom =
      (affineModuleSectionsBaseChangeIso f t M U hU).hom ≫
        (baseModulePresheaf (pullback.snd f t)
          ((pullback (pullback.fst f t)).obj M)).map
            (homOfLE ((pullback.fst f t).preimage_mono hVU)).op := by
  apply extendScalars_hom_ext t.appTop.hom
  intro m
  rw [two_comp_apply, two_comp_apply]
  have hmap :
      (ModuleCat.extendScalars t.appTop.hom).map
          ((baseModulePresheaf f M).map (homOfLE hVU).op)
            ((1 : Γ(T, (⊤ : T.Opens)))
              ⊗ₜ[Γ(S, (⊤ : S.Opens)), t.appTop.hom] m) =
        ((1 : Γ(T, (⊤ : T.Opens)))
          ⊗ₜ[Γ(S, (⊤ : S.Opens)), t.appTop.hom]
            ((baseModulePresheaf f M).map (homOfLE hVU).op m) :
          (ModuleCat.extendScalars t.appTop.hom).obj
            ((baseModulePresheaf f M).obj (op V))) := by
    exact ModuleCat.ExtendScalars.map_tmul
      (f := t.appTop.hom)
        ((baseModulePresheaf f M).map (homOfLE hVU).op)
        (1 : Γ(T, (⊤ : T.Opens))) m
  have hmapLift := congrArg
    (affineModuleSectionsBaseChangeIso f t M V hV).hom hmap
  have hgeneratorV :=
    affineModuleSectionsBaseChangeIso_hom_one_tmul f t M V hV
      ((baseModulePresheaf f M).map (homOfLE hVU).op m)
  have hgeneratorU :=
    affineModuleSectionsBaseChangeIso_hom_one_tmul f t M U hU m
  have hgeneratorUMap := congrArg
    ((baseModulePresheaf (pullback.snd f t)
      ((pullback (pullback.fst f t)).obj M)).map
        (homOfLE ((pullback.fst f t).preimage_mono hVU)).op)
    hgeneratorU
  have hunitNaturality := PresheafOfModules.naturality_apply
    ((pullbackPushforwardAdjunction (pullback.fst f t)).unit.app M).val
      (homOfLE hVU).op m
  let pulledM := (pullback (pullback.fst f t)).obj M
  let unitU :=
    (((pullbackPushforwardAdjunction (pullback.fst f t)).unit.app M).val.app
      (op U)) m
  have htarget :
      (((pullback (pullback.fst f t) ⋙
          pushforward (pullback.fst f t)).obj M).val.map
            (homOfLE hVU).op) unitU =
        (baseModulePresheaf (pullback.snd f t) pulledM).map
          (homOfLE ((pullback.fst f t).preimage_mono hVU)).op unitU := by
    calc
      _ = pulledM.presheaf.map
          (((TopologicalSpace.Opens.map (pullback.fst f t).base).map
            (homOfLE hVU)).op) unitU := by
        rfl
      _ = pulledM.presheaf.map
          (homOfLE ((pullback.fst f t).preimage_mono hVU)).op unitU :=
        pulledM.val.congr_map_apply (Subsingleton.elim _ _) unitU
      _ = _ := by
        rfl
  have hleftGenerator := hmapLift.trans hgeneratorV
  have hleftNatural := hleftGenerator.trans hunitNaturality
  have hleftTarget := hleftNatural.trans htarget
  exact eq_of_eq_same hleftTarget hgeneratorUMap

end AlgebraicGeometry.Scheme.Modules

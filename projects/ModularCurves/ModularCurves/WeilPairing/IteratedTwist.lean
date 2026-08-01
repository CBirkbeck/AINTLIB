/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.LineVerticalConsumers

/-!
# Iterated twists and the multiplier calculus

The divisor-restriction pipeline of `LineVertical.lean` is stated for the twist map
`divisorTwistHom J L`, whose source is `I(J) ⊗ L`. For the theorem-of-the-square
assembly the *iterated* form is wanted instead — restriction to `[P] + [Q]` realised as
the composite

`I(P) ⊗ (I(Q) ⊗ L) ⟶ I(Q) ⊗ L ⟶ L`,

whose source is already in the tensor shape that `Picard/DivisorClass.lean` consumes.
This avoids the multiplicativity isomorphism `I(J₁J₂) ≅ I(J₁) ⊗ I(J₂)`, which is a map
between two ideal-module machines and runs into the kernel wall.

The pipeline only ever uses the map through its *chart multiplier* — the unit-endomorphism
that the chart trivializations conjugate it to — so everything is done here for a general
map of invertible modules, and the key computation is that the multiplier of a composite
is the product of the multipliers (`chartMultiplier_comp`).
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory Matrix

namespace AlgebraicGeometry.Scheme.Modules

variable {C : Scheme.{u}}

section GeneralMultiplier

variable {M L : C.Modules} (U : C.Opens)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[G1] The chart multiplier of a map of modules**: the section of the structure
sheaf that the chart trivializations conjugate the map to. -/
noncomputable def chartMultiplier (f : M ⟶ L)
    (eM : (restrictFunctor U.ι).obj M ≅ unitObj U.toScheme)
    (eL : (restrictFunctor U.ι).obj L ≅ unitObj U.toScheme) :
    Γ(U.toScheme, (⊤ : U.toScheme.Opens)) :=
  (eM.inv ≫ (restrictFunctor U.ι).map f ≫ eL.hom).val.app
    (Opposite.op (⊤ : U.toScheme.Opens))
    (1 : Γ(U.toScheme, (⊤ : U.toScheme.Opens)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The conjugated map *is* multiplication by the chart multiplier. -/
theorem conj_eq_unitEndo_chartMultiplier (f : M ⟶ L)
    (eM : (restrictFunctor U.ι).obj M ≅ unitObj U.toScheme)
    (eL : (restrictFunctor U.ι).obj L ≅ unitObj U.toScheme) :
    eM.inv ≫ (restrictFunctor U.ι).map f ≫ eL.hom =
      ModularCurves.unitEndomorphismOfTopSection (chartMultiplier U f eM eL) :=
  unit_endo_eq_ofTopSection _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[G4] The multiplier of a composite is the product of the multipliers.** -/
theorem chartMultiplier_comp {N : C.Modules} (f : M ⟶ N) (g : N ⟶ L)
    (eM : (restrictFunctor U.ι).obj M ≅ unitObj U.toScheme)
    (eN : (restrictFunctor U.ι).obj N ≅ unitObj U.toScheme)
    (eL : (restrictFunctor U.ι).obj L ≅ unitObj U.toScheme) :
    chartMultiplier U (f ≫ g) eM eL =
      chartMultiplier U f eM eN * chartMultiplier U g eN eL := by
  have hsplit : eM.inv ≫ (restrictFunctor U.ι).map (f ≫ g) ≫ eL.hom =
      (eM.inv ≫ (restrictFunctor U.ι).map f ≫ eN.hom) ≫
        (eN.inv ≫ (restrictFunctor U.ι).map g ≫ eL.hom) := by
    rw [Functor.map_comp]
    rw [show (eM.inv ≫ (restrictFunctor U.ι).map f ≫ eN.hom) ≫
        (eN.inv ≫ (restrictFunctor U.ι).map g ≫ eL.hom) =
      eM.inv ≫ (restrictFunctor U.ι).map f ≫ (eN.hom ≫ eN.inv) ≫
        (restrictFunctor U.ι).map g ≫ eL.hom by
      simp only [Category.assoc]]
    rw [eN.hom_inv_id, Category.id_comp]
    simp only [Category.assoc]
  have hprod : eM.inv ≫ (restrictFunctor U.ι).map (f ≫ g) ≫ eL.hom =
      ModularCurves.unitEndomorphismOfTopSection
        (chartMultiplier U f eM eN * chartMultiplier U g eN eL) := by
    rw [hsplit, conj_eq_unitEndo_chartMultiplier, conj_eq_unitEndo_chartMultiplier,
      ModularCurves.unitEndomorphismOfTopSection_comp]
  have hval := congrArg (fun (φ : unitObj U.toScheme ⟶ unitObj U.toScheme) =>
    φ.val.app (Opposite.op (⊤ : U.toScheme.Opens))
      (1 : Γ(U.toScheme, (⊤ : U.toScheme.Opens)))) hprod
  refine hval.trans ?_
  rw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
  have hres : (U.toScheme).presheaf.map
      (homOfLE (le_top : (⊤ : U.toScheme.Opens) ≤ ⊤)).op
      (chartMultiplier U f eM eN * chartMultiplier U g eN eL) =
      chartMultiplier U f eM eN * chartMultiplier U g eN eL := by
    rw [show (homOfLE (le_top : (⊤ : U.toScheme.Opens) ≤ ⊤)) =
      𝟙 (⊤ : U.toScheme.Opens) from rfl, op_id, CategoryTheory.Functor.map_id]
    rfl
  rw [hres]
  exact one_mul (chartMultiplier U f eM eN * chartMultiplier U g eN eL)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[G2] The restricted map's cokernel is the multiplier's cokernel.** -/
noncomputable def cokernelRestrictUnitEndoIso (f : M ⟶ L)
    (eM : (restrictFunctor U.ι).obj M ≅ unitObj U.toScheme)
    (eL : (restrictFunctor U.ι).obj L ≅ unitObj U.toScheme) :
    Limits.cokernel ((restrictFunctor U.ι).map f) ≅
      Limits.cokernel (ModularCurves.unitEndomorphismOfTopSection
        (chartMultiplier U f eM eL)) := by
  refine Limits.cokernel.mapIso _ _ eM eL ?_
  calc (restrictFunctor U.ι).map f ≫ eL.hom
      = eM.hom ≫ (eM.inv ≫ (restrictFunctor U.ι).map f ≫ eL.hom) :=
        (Iso.hom_inv_id_assoc _ _).symm
    _ = eM.hom ≫ ModularCurves.unitEndomorphismOfTopSection
          (chartMultiplier U f eM eL) := by
        rw [conj_eq_unitEndo_chartMultiplier]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The multiplier is a nonzerodivisor when the restricted map is a monomorphism —
the input the rank splitting needs. -/
theorem mono_unitEndo_chartMultiplier (f : M ⟶ L)
    (eM : (restrictFunctor U.ι).obj M ≅ unitObj U.toScheme)
    (eL : (restrictFunctor U.ι).obj L ≅ unitObj U.toScheme)
    [Mono ((restrictFunctor U.ι).map f)] :
    Mono (ModularCurves.unitEndomorphismOfTopSection (chartMultiplier U f eM eL)) := by
  rw [← conj_eq_unitEndo_chartMultiplier]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[G3, rank two] The rank-two coordinates for a general map of invertibles.**
Concentration on the chart is a hypothesis (`hbij`), as is the span identification of
the chart multiplier as a product of two generators. Instantiating at
`divisorTwistHom` recovers the divisor form; instantiating at an iterated twist gives
the tensor-shaped form the Picard assembly consumes. -/
theorem nonempty_baseSections_cokernel_equiv_pair_of_mono
    {S : Scheme.{u}} {π : C ⟶ S} {M L : C.Modules} (f : M ⟶ L)
    (Ua : C.affineOpens)
    (eM : (restrictFunctor Ua.1.ι).obj M ≅ unitObj Ua.1.toScheme)
    (eL : (restrictFunctor Ua.1.ι).obj L ≅ unitObj Ua.1.toScheme)
    (hbij : Function.Bijective
      (((Scheme.Modules.toSheaf C).obj (Limits.cokernel f)).1.map
        (homOfLE (le_top : Ua.1 ≤ (⊤ : C.Opens))).op))
    [Mono ((restrictFunctor Ua.1.ι).map f)]
    (rP' rQ' : Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens)))
    (hv : Ideal.span {chartMultiplier Ua.1 f eM eL} =
      Ideal.span {rP' * rQ'})
    (hrP' : rP' ∈ nonZeroDivisors Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens)))
    [Algebra Γ(S, (⊤ : S.Opens)) Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens))]
    (halg : ∀ r : Γ(S, (⊤ : S.Opens)),
      algebraMap Γ(S, (⊤ : S.Opens))
        Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens)) r =
        (Scheme.Hom.appTop (Ua.1.ι ≫ π)).hom r)
    (eP : (Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens)) ⧸ Ideal.span {rP'})
      ≃ₗ[Γ(S, (⊤ : S.Opens))] Γ(S, (⊤ : S.Opens)))
    (eQ : (Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens)) ⧸ Ideal.span {rQ'})
      ≃ₗ[Γ(S, (⊤ : S.Opens))] Γ(S, (⊤ : S.Opens))) :
    Nonempty ((Scheme.Modules.baseSections π (Limits.cokernel f))
      ≃ₗ[Γ(S, (⊤ : S.Opens))] (Fin 2 → Γ(S, (⊤ : S.Opens)))) := by
  classical
  haveI : IsAffine Ua.1.toScheme := Ua.2
  haveI hMonoEndo : Mono (ModularCurves.unitEndomorphismOfTopSection
      (chartMultiplier Ua.1 f eM eL)) :=
    mono_unitEndo_chartMultiplier Ua.1 f eM eL
  let i1 := Scheme.Modules.baseSectionsRestrictIsoOfBijective π
    (Limits.cokernel f) Ua.1 hbij
  let i2 := Scheme.Modules.baseSectionsMapIso (Ua.1.ι ≫ π)
    (Limits.PreservesCokernel.iso (restrictFunctor Ua.1.ι) f)
  let i3 := Scheme.Modules.baseSectionsMapIso (Ua.1.ι ≫ π)
    (cokernelRestrictUnitEndoIso Ua.1 f eM eL)
  obtain ⟨eCore⟩ := nonempty_baseSections_cokernel_unitEndo_equiv
    (Ua.1.ι ≫ π) (chartMultiplier Ua.1 f eM eL) halg
  let eA : (Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens)) ⧸
      Ideal.span {chartMultiplier Ua.1 f eM eL}) ≃ₗ[
        Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens))]
      (Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens)) ⧸
        Ideal.span {rP' * rQ'}) :=
    Submodule.quotEquivOfEq _ _ hv
  let eSpan := eA.restrictScalars Γ(S, (⊤ : S.Opens))
  let e3a := ModularCurves.quotientSpanMulEquivProd rP' rQ' hrP' eP eQ
  exact ⟨(((i1 ≪≫ i2 ≪≫ i3).toLinearEquiv).trans eCore).trans
    (eSpan.trans e3a)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[G3, rank one]** The single-generator analogue. -/
theorem nonempty_baseSections_cokernel_equiv_single_of_mono
    {S : Scheme.{u}} {π : C ⟶ S} {M L : C.Modules} (f : M ⟶ L)
    (Ua : C.affineOpens)
    (eM : (restrictFunctor Ua.1.ι).obj M ≅ unitObj Ua.1.toScheme)
    (eL : (restrictFunctor Ua.1.ι).obj L ≅ unitObj Ua.1.toScheme)
    (hbij : Function.Bijective
      (((Scheme.Modules.toSheaf C).obj (Limits.cokernel f)).1.map
        (homOfLE (le_top : Ua.1 ≤ (⊤ : C.Opens))).op))
    [Mono ((restrictFunctor Ua.1.ι).map f)]
    (r' : Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens)))
    (hv : Ideal.span {chartMultiplier Ua.1 f eM eL} = Ideal.span {r'})
    [Algebra Γ(S, (⊤ : S.Opens)) Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens))]
    (halg : ∀ r : Γ(S, (⊤ : S.Opens)),
      algebraMap Γ(S, (⊤ : S.Opens))
        Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens)) r =
        (Scheme.Hom.appTop (Ua.1.ι ≫ π)).hom r)
    (eP : (Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens)) ⧸ Ideal.span {r'})
      ≃ₗ[Γ(S, (⊤ : S.Opens))] Γ(S, (⊤ : S.Opens))) :
    Nonempty ((Scheme.Modules.baseSections π (Limits.cokernel f))
      ≃ₗ[Γ(S, (⊤ : S.Opens))] Γ(S, (⊤ : S.Opens))) := by
  classical
  haveI : IsAffine Ua.1.toScheme := Ua.2
  haveI hMonoEndo : Mono (ModularCurves.unitEndomorphismOfTopSection
      (chartMultiplier Ua.1 f eM eL)) :=
    mono_unitEndo_chartMultiplier Ua.1 f eM eL
  let i1 := Scheme.Modules.baseSectionsRestrictIsoOfBijective π
    (Limits.cokernel f) Ua.1 hbij
  let i2 := Scheme.Modules.baseSectionsMapIso (Ua.1.ι ≫ π)
    (Limits.PreservesCokernel.iso (restrictFunctor Ua.1.ι) f)
  let i3 := Scheme.Modules.baseSectionsMapIso (Ua.1.ι ≫ π)
    (cokernelRestrictUnitEndoIso Ua.1 f eM eL)
  obtain ⟨eCore⟩ := nonempty_baseSections_cokernel_unitEndo_equiv
    (Ua.1.ι ≫ π) (chartMultiplier Ua.1 f eM eL) halg
  let eA : (Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens)) ⧸
      Ideal.span {chartMultiplier Ua.1 f eM eL}) ≃ₗ[
        Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens))]
      (Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens)) ⧸ Ideal.span {r'}) :=
    Submodule.quotEquivOfEq _ _ hv
  let eSpan := eA.restrictScalars Γ(S, (⊤ : S.Opens))
  exact ⟨(((i1 ≪≫ i2 ≪≫ i3).toLinearEquiv).trans eCore).trans (eSpan.trans eP)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[G5] Concentration for a composite**: if both factors' cokernels vanish on an
open, so does the composite's — the composite is an epimorphism there, being a
composite of epimorphisms. -/
theorem isZero_restrict_cokernel_comp {N : C.Modules} (f : M ⟶ N) (g : N ⟶ L)
    (V : C.Opens)
    (hf : Limits.IsZero ((restrictFunctor V.ι).obj (Limits.cokernel f)))
    (hg : Limits.IsZero ((restrictFunctor V.ι).obj (Limits.cokernel g))) :
    Limits.IsZero ((restrictFunctor V.ι).obj (Limits.cokernel (f ≫ g))) := by
  haveI hepif : Epi ((restrictFunctor V.ι).map f) :=
    Preadditive.epi_of_isZero_cokernel _
      (hf.of_iso (Limits.PreservesCokernel.iso (restrictFunctor V.ι) f).symm)
  haveI hepig : Epi ((restrictFunctor V.ι).map g) :=
    Preadditive.epi_of_isZero_cokernel _
      (hg.of_iso (Limits.PreservesCokernel.iso (restrictFunctor V.ι) g).symm)
  haveI : Epi ((restrictFunctor V.ι).map (f ≫ g)) := by
    rw [Functor.map_comp]
    infer_instance
  have hz := Limits.isZero_cokernel_of_epi ((restrictFunctor V.ι).map (f ≫ g))
  exact hz.of_iso (Limits.PreservesCokernel.iso (restrictFunctor V.ι) (f ≫ g))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Concentration of global sections from vanishing of the restricted cokernel on the
complementary open (the general form of `cokernel_divisorTwistHom_bijective_restrict`). -/
theorem cokernel_bijective_restrict_of_isZero (f : M ⟶ L) (Uo V : C.Opens)
    (hUV : Uo ⊔ V = ⊤)
    (hzero : ∀ W : C.Opens, W ≤ V →
      Limits.IsZero ((restrictFunctor W.ι).obj (Limits.cokernel f))) :
    Function.Bijective fun s : Γ(Limits.cokernel f, (⊤ : C.Opens)) ↦
      (Limits.cokernel f).presheaf.map
        (homOfLE (le_top : Uo ≤ (⊤ : C.Opens))).op s := by
  let Mc := Limits.cokernel f
  let F := (SheafOfModules.toSheaf C.ringCatSheaf).obj Mc
  haveI hVsections : Subsingleton Γ(Mc, V) :=
    Scheme.Modules.subsingleton_sections_of_isZero_restrict Mc V (hzero V le_rfl)
  haveI hVsheaf : Subsingleton (ToType (F.1.obj (Opposite.op V))) := by
    change Subsingleton Γ(Mc, V)
    infer_instance
  haveI hoverlap : Subsingleton Γ(Mc, Uo ⊓ V) :=
    Scheme.Modules.subsingleton_sections_of_isZero_restrict Mc (Uo ⊓ V)
      (hzero (Uo ⊓ V) inf_le_right)
  haveI hoverlapSheaf : Subsingleton (ToType (F.1.obj (Opposite.op (Uo ⊓ V)))) := by
    change Subsingleton Γ(Mc, Uo ⊓ V)
    infer_instance
  exact TopCat.Sheaf.bijective_restrict_of_sup_eq_top_of_subsingleton F hUV

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by a unit is an isomorphism of the structure sheaf. -/
theorem isIso_unitEndomorphismOfTopSection_of_isUnit {Z : Scheme.{u}}
    {c : Γ(Z, (⊤ : Z.Opens))} (hc : IsUnit c) :
    IsIso (ModularCurves.unitEndomorphismOfTopSection c) := by
  obtain ⟨u, rfl⟩ := hc
  exact (ModularCurves.unitAutomorphismOfTopUnit u).isIso_hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The unit-multiplier iso criterion.** A map of modules that is trivialized on a
cover and whose chart multipliers are units there is an isomorphism. This is how a
section vanishing to *exactly* the divisor order trivializes the twist. -/
theorem isIso_of_chartMultiplier_isUnit {M L : C.Modules} (f : M ⟶ L)
    {ι : Type u} (W : ι → C.Opens) (hW : iSup W = ⊤)
    (eM : ∀ i, (restrictFunctor (W i).ι).obj M ≅ unitObj (W i).toScheme)
    (eL : ∀ i, (restrictFunctor (W i).ι).obj L ≅ unitObj (W i).toScheme)
    (hunit : ∀ i, IsUnit (chartMultiplier (W i) f (eM i) (eL i))) :
    IsIso f := by
  refine isIso_of_isIso_restrict f W hW fun i => ?_
  haveI : IsIso (ModularCurves.unitEndomorphismOfTopSection
      (chartMultiplier (W i) f (eM i) (eL i))) :=
    isIso_unitEndomorphismOfTopSection_of_isUnit (hunit i)
  have hconj : (restrictFunctor (W i).ι).map f =
      (eM i).hom ≫ ModularCurves.unitEndomorphismOfTopSection
        (chartMultiplier (W i) f (eM i) (eL i)) ≫ (eL i).inv := by
    rw [← conj_eq_unitEndo_chartMultiplier]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hconj]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The general section lift**: a global section of `L` killed by the cokernel of a
monomorphism `f : M ⟶ L` factors through `f`. -/
noncomputable def monoSectionLift {M L : C.Modules} (f : M ⟶ L) [Mono f]
    (ℓ : Γ(L, (⊤ : C.Opens)))
    (hℓ : (Limits.cokernel.π f).app (⊤ : C.Opens) ℓ = 0) :
    unitObj C ⟶ M :=
  CategoryTheory.Abelian.monoLift f (unitHomOfTopSection ℓ)
    (by rw [unitHomOfTopSection_comp, hℓ, unitHomOfTopSection_zero])

@[reassoc (attr := simp)]
theorem monoSectionLift_comp {M L : C.Modules} (f : M ⟶ L) [Mono f]
    (ℓ : Γ(L, (⊤ : C.Opens)))
    (hℓ : (Limits.cokernel.π f).app (⊤ : C.Opens) ℓ = 0) :
    monoSectionLift f ℓ hℓ ≫ f = unitHomOfTopSection ℓ :=
  CategoryTheory.Abelian.monoLift_comp _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The exact-order criterion.** The lift of a section through a monomorphism is an
isomorphism as soon as, on a trivializing cover, the section's own multiplier is the
multiplier of `f` times a unit — "the section vanishes to exactly the order of `f`".
The multiplier identity is the multiplicativity of chart multipliers along the
factorization `lift ≫ f = ℓ`. -/
theorem isIso_monoSectionLift_of_chartMultiplier_isUnit
    {M L : C.Modules} (f : M ⟶ L) [Mono f]
    (ℓ : Γ(L, (⊤ : C.Opens)))
    (hℓ : (Limits.cokernel.π f).app (⊤ : C.Opens) ℓ = 0)
    {ι : Type u} (W : ι → C.Opens) (hW : iSup W = ⊤)
    (eM : ∀ i, (restrictFunctor (W i).ι).obj M ≅ unitObj (W i).toScheme)
    (eL : ∀ i, (restrictFunctor (W i).ι).obj L ≅ unitObj (W i).toScheme)
    (eU : ∀ i, (restrictFunctor (W i).ι).obj (unitObj C) ≅ unitObj (W i).toScheme)
    (hunit : ∀ i, IsUnit (chartMultiplier (W i) (monoSectionLift f ℓ hℓ)
      (eU i) (eM i))) :
    IsIso (monoSectionLift f ℓ hℓ) :=
  isIso_of_chartMultiplier_isUnit _ W hW eU eM hunit

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The section's chart multiplier factors as (lift multiplier) · (twist multiplier):
the arithmetic behind the exact-order criterion. -/
theorem chartMultiplier_unitHomOfTopSection_eq {M L : C.Modules} (f : M ⟶ L) [Mono f]
    (ℓ : Γ(L, (⊤ : C.Opens)))
    (hℓ : (Limits.cokernel.π f).app (⊤ : C.Opens) ℓ = 0) (U : C.Opens)
    (eU : (restrictFunctor U.ι).obj (unitObj C) ≅ unitObj U.toScheme)
    (eM : (restrictFunctor U.ι).obj M ≅ unitObj U.toScheme)
    (eL : (restrictFunctor U.ι).obj L ≅ unitObj U.toScheme) :
    chartMultiplier U (unitHomOfTopSection ℓ) eU eL =
      chartMultiplier U (monoSectionLift f ℓ hℓ) eU eM *
        chartMultiplier U f eM eL := by
  rw [← chartMultiplier_comp U (monoSectionLift f ℓ hℓ) f eU eM eL,
    monoSectionLift_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Evaluating multiplication-by-`x` on the global `1` returns `x`. -/
theorem unitEndomorphismOfTopSection_app_top_one {Z : Scheme.{u}}
    (x : Γ(Z, (⊤ : Z.Opens))) :
    (ModularCurves.unitEndomorphismOfTopSection x).val.app
      (Opposite.op (⊤ : Z.Opens)) (1 : Γ(Z, (⊤ : Z.Opens))) = x := by
  rw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
  rw [show Z.presheaf.map (homOfLE (le_top : (⊤ : Z.Opens) ≤ ⊤)).op x = x from by
    rw [show (homOfLE (le_top : (⊤ : Z.Opens) ≤ ⊤)) = 𝟙 (⊤ : Z.Opens) from rfl,
      op_id, CategoryTheory.Functor.map_id]
    rfl]
  exact one_mul x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A monomorphic multiplication has a nonzerodivisor multiplier. -/
theorem mem_nonZeroDivisors_of_mono_unitEndo {Z : Scheme.{u}}
    (c : Γ(Z, (⊤ : Z.Opens)))
    [Mono (ModularCurves.unitEndomorphismOfTopSection c)] :
    c ∈ nonZeroDivisors Γ(Z, (⊤ : Z.Opens)) := by
  have hkill : ∀ x : Γ(Z, (⊤ : Z.Opens)), x * c = 0 → x = 0 := by
    intro x hx
    have hzero : ModularCurves.unitEndomorphismOfTopSection x ≫
        ModularCurves.unitEndomorphismOfTopSection c =
        ModularCurves.unitEndomorphismOfTopSection (0 : Γ(Z, (⊤ : Z.Opens))) ≫
          ModularCurves.unitEndomorphismOfTopSection c := by
      rw [ModularCurves.unitEndomorphismOfTopSection_comp,
        ModularCurves.unitEndomorphismOfTopSection_comp, hx, zero_mul]
    have hx0 : ModularCurves.unitEndomorphismOfTopSection x =
        ModularCurves.unitEndomorphismOfTopSection (0 : Γ(Z, (⊤ : Z.Opens))) :=
      (cancel_mono _).mp hzero
    have hval := congrArg (fun (φ : unitObj Z ⟶ unitObj Z) =>
      φ.val.app (Opposite.op (⊤ : Z.Opens)) (1 : Γ(Z, (⊤ : Z.Opens)))) hx0
    exact ((unitEndomorphismOfTopSection_app_top_one x).symm.trans hval).trans
      (unitEndomorphismOfTopSection_app_top_one (0 : Γ(Z, (⊤ : Z.Opens))))
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun x hx => hkill x (by rw [mul_comm]; exact hx), hkill⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The exact-order trivialization.** If, on each chart of a trivializing cover, the
section's multiplier is a unit multiple of the map's multiplier, then the lift is an
isomorphism: the twisted module is trivial. -/
theorem isIso_monoSectionLift_of_multiplier_eq_unit_mul
    {M L : C.Modules} (f : M ⟶ L) [Mono f]
    (ℓ : Γ(L, (⊤ : C.Opens)))
    (hℓ : (Limits.cokernel.π f).app (⊤ : C.Opens) ℓ = 0)
    {ι : Type u} (W : ι → C.Opens) (hW : iSup W = ⊤)
    (eM : ∀ i, (restrictFunctor (W i).ι).obj M ≅ unitObj (W i).toScheme)
    (eL : ∀ i, (restrictFunctor (W i).ι).obj L ≅ unitObj (W i).toScheme)
    (eU : ∀ i, (restrictFunctor (W i).ι).obj (unitObj C) ≅ unitObj (W i).toScheme)
    (hmono : ∀ i, Mono ((restrictFunctor (W i).ι).map f))
    (u : ∀ i, Γ(((W i).toScheme), (⊤ : ((W i).toScheme).Opens))ˣ)
    (hexact : ∀ i, chartMultiplier (W i) (unitHomOfTopSection ℓ) (eU i) (eL i) =
      (u i : Γ(((W i).toScheme), (⊤ : ((W i).toScheme).Opens))) *
        chartMultiplier (W i) f (eM i) (eL i)) :
    IsIso (monoSectionLift f ℓ hℓ) := by
  refine isIso_of_chartMultiplier_isUnit _ W hW eU eM fun i => ?_
  haveI := hmono i
  haveI hMonoEndo : Mono (ModularCurves.unitEndomorphismOfTopSection
      (chartMultiplier (W i) f (eM i) (eL i))) :=
    mono_unitEndo_chartMultiplier (W i) f (eM i) (eL i)
  have hnzd := mem_nonZeroDivisors_of_mono_unitEndo
    (chartMultiplier (W i) f (eM i) (eL i))
  have hfac := chartMultiplier_unitHomOfTopSection_eq f ℓ hℓ (W i) (eU i) (eM i) (eL i)
  have heq : chartMultiplier (W i) (monoSectionLift f ℓ hℓ) (eU i) (eM i) *
      chartMultiplier (W i) f (eM i) (eL i) =
      (u i : Γ(((W i).toScheme), (⊤ : ((W i).toScheme).Opens))) *
        chartMultiplier (W i) f (eM i) (eL i) := by
    rw [← hfac, hexact i]
  have hcancel := (mul_cancel_right_mem_nonZeroDivisors hnzd).mp heq
  rw [hcancel]
  exact (u i).isUnit

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- **A chart trivialization is a generating section.** The component of the inverse
trivialization at the preimage of `W` sends `1` to a section whose multiples exhaust the
sections there — the input shape of the descent machinery
(`Picard/GlueTrivialization.lean`). -/
theorem bijective_smul_restrictIso_inv_app {M : C.Modules} (U : C.Opens)
    (e : (restrictFunctor U.ι).obj M ≅ unitObj U.toScheme) (W : C.Opens) :
    Function.Bijective (fun r : Γ(U.toScheme, U.ι ⁻¹ᵁ W) =>
      r • (e.inv.app (U.ι ⁻¹ᵁ W)
        (show Γ(unitObj U.toScheme, U.ι ⁻¹ᵁ W) from
          (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ W))))) := by
  have hiso : IsIso (e.inv.app (U.ι ⁻¹ᵁ W)) :=
    Hom.isIso_iff_isIso_app.mp inferInstance _
  have hbij := (ConcreteCategory.isIso_iff_bijective
    (e.inv.app (U.ι ⁻¹ᵁ W))).mp hiso
  have hfun : (fun r : Γ(U.toScheme, U.ι ⁻¹ᵁ W) =>
      r • (e.inv.app (U.ι ⁻¹ᵁ W)
        (show Γ(unitObj U.toScheme, U.ι ⁻¹ᵁ W) from
          (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ W))))) =
      fun r : Γ(U.toScheme, U.ι ⁻¹ᵁ W) =>
        e.inv.app (U.ι ⁻¹ᵁ W) (show Γ(unitObj U.toScheme, U.ι ⁻¹ᵁ W) from r) := by
    funext r
    have hsmul := Scheme.Modules.Hom.app_smul e.inv
      (U := U.ι ⁻¹ᵁ W) r
      (show Γ(unitObj U.toScheme, U.ι ⁻¹ᵁ W) from (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ W)))
    have hone : (r • (show Γ(unitObj U.toScheme, U.ι ⁻¹ᵁ W) from
        (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ W)))) =
        (show Γ(unitObj U.toScheme, U.ι ⁻¹ᵁ W) from r) := by
      show r * 1 = r
      exact mul_one r
    rw [hone] at hsmul
    exact hsmul.symm
  rw [hfun]
  exact hbij

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W2-b] Two generating sections differ by a unit.** If `s` and `t` both generate
`Γ(M, ·)` freely over an open and all its sub-opens, the comparison scalar is a unit.
This supplies the overlap data of the rigidified descent. -/
theorem exists_isUnit_smul_eq_of_generators {M : C.Modules} (V : C.Opens)
    (s t : Γ(M, V))
    (hs : Function.Bijective (fun r : Γ(C, V) => r • s))
    (ht : Function.Bijective (fun r : Γ(C, V) => r • t)) :
    ∃ u : Γ(C, V), IsUnit u ∧ s = u • t := by
  obtain ⟨u, hu⟩ := ht.surjective s
  obtain ⟨w, hw⟩ := hs.surjective t
  refine ⟨u, ?_, hu.symm⟩
  have hws : w • s = t := hw
  have hut : u • t = s := hu
  have hchain : (u * w) • s = (1 : Γ(C, V)) • s := by
    rw [mul_smul, hws, hut, one_smul]
  have huw : u * w = 1 := hs.injective hchain
  exact isUnit_of_mul_isUnit_left (show IsUnit (u * w) from by
    rw [huw]; exact isUnit_one)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The restriction of a generating section generates: bijectivity descends along the
trivialization's naturality. -/
theorem bijective_smul_restrict_of_restrictIso {M : C.Modules} (U : C.Opens)
    (e : (restrictFunctor U.ι).obj M ≅ unitObj U.toScheme) (W W' : C.Opens)
    (hWW' : U.ι ⁻¹ᵁ W' ≤ U.ι ⁻¹ᵁ W) :
    Function.Bijective (fun r : Γ(U.toScheme, U.ι ⁻¹ᵁ W') =>
      r • (((restrictFunctor U.ι).obj M).presheaf.map (homOfLE hWW').op
        (e.inv.app (U.ι ⁻¹ᵁ W)
          (show Γ(unitObj U.toScheme, U.ι ⁻¹ᵁ W) from
            (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ W)))))) := by
  have hnat := (e.inv.val.naturality (homOfLE hWW').op)
  have hval : ((restrictFunctor U.ι).obj M).presheaf.map (homOfLE hWW').op
      (e.inv.app (U.ι ⁻¹ᵁ W)
        (show Γ(unitObj U.toScheme, U.ι ⁻¹ᵁ W) from
          (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ W)))) =
      e.inv.app (U.ι ⁻¹ᵁ W')
        (show Γ(unitObj U.toScheme, U.ι ⁻¹ᵁ W') from
          (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ W'))) := by
    have h := PresheafOfModules.naturality_apply e.inv.val (homOfLE hWW').op
      (show Γ(unitObj U.toScheme, U.ι ⁻¹ᵁ W) from
        (1 : Γ(U.toScheme, U.ι ⁻¹ᵁ W)))
    refine h.symm.trans (congrArg (e.inv.app (U.ι ⁻¹ᵁ W')) ?_)
    exact map_one ((U.toScheme).presheaf.map (homOfLE hWW').op).hom
  rw [hval]
  exact bijective_smul_restrictIso_inv_app U e W'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Transport of the generating property along an equality of opens. -/
theorem bijective_smul_congr_opens {M : C.Modules} {A B : C.Opens} (hAB : A = B)
    (mB : Γ(M, B))
    (h : Function.Bijective (fun r : Γ(C, A) =>
      r • M.presheaf.map (eqToHom hAB).op mB)) :
    Function.Bijective (fun r : Γ(C, B) => r • mB) := by
  subst hAB
  simpa using h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The image of the top open under an open immersion of opens. -/
theorem image_top_eq (V : C.Opens) : V.ι ''ᵁ (⊤ : V.toScheme.Opens) = V := by
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W2-c] The generating section of a chart trivialization, on the base scheme.**
A trivialization of `M` over `V` produces a section over `V` all of whose restrictions
generate — the exact input of `Picard/GlueTrivialization.lean`. -/
noncomputable def generatorOfRestrictIso {M : C.Modules} (V : C.Opens)
    (e : (restrictFunctor V.ι).obj M ≅ unitObj V.toScheme) : Γ(M, V) :=
  M.presheaf.map (eqToHom (image_top_eq V).symm).op
    (e.inv.app (⊤ : V.toScheme.Opens)
      (show Γ(unitObj V.toScheme, (⊤ : V.toScheme.Opens)) from
        (1 : Γ(V.toScheme, (⊤ : V.toScheme.Opens)))))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The generator of a trivialization generates over the whole open. -/
theorem bijective_smul_generatorOfRestrictIso {M : C.Modules} (V : C.Opens)
    (e : (restrictFunctor V.ι).obj M ≅ unitObj V.toScheme) :
    Function.Bijective (fun r : Γ(C, V) => r • generatorOfRestrictIso V e) := by
  refine bijective_smul_congr_opens (image_top_eq V) _ ?_
  have hb := bijective_smul_restrictIso_inv_app V e V
  have hpre : V.ι ⁻¹ᵁ V = (⊤ : V.toScheme.Opens) := V.ι_preimage_self
  have hb' : Function.Bijective
      (fun r : Γ(V.toScheme, (⊤ : V.toScheme.Opens)) =>
        r • (e.inv.app (⊤ : V.toScheme.Opens)
          (show Γ(unitObj V.toScheme, (⊤ : V.toScheme.Opens)) from
            (1 : Γ(V.toScheme, (⊤ : V.toScheme.Opens)))))) := by
    rw [← hpre]
    exact hb
  have hcast : (fun r : Γ(C, V.ι ''ᵁ (⊤ : V.toScheme.Opens)) =>
      r • M.presheaf.map (eqToHom (image_top_eq V)).op
        (generatorOfRestrictIso V e)) =
      (fun r : Γ(V.toScheme, (⊤ : V.toScheme.Opens)) =>
        r • (e.inv.app (⊤ : V.toScheme.Opens)
          (show Γ(unitObj V.toScheme, (⊤ : V.toScheme.Opens)) from
            (1 : Γ(V.toScheme, (⊤ : V.toScheme.Opens)))))) := by
    have hsec : M.presheaf.map (eqToHom (image_top_eq V)).op
        (generatorOfRestrictIso V e) =
        e.inv.app (⊤ : V.toScheme.Opens)
          (show Γ(unitObj V.toScheme, (⊤ : V.toScheme.Opens)) from
            (1 : Γ(V.toScheme, (⊤ : V.toScheme.Opens)))) := by
      show M.presheaf.map (eqToHom (image_top_eq V)).op
          (M.presheaf.map (eqToHom (image_top_eq V).symm).op
            (e.inv.app (⊤ : V.toScheme.Opens)
              (show Γ(unitObj V.toScheme, (⊤ : V.toScheme.Opens)) from
                (1 : Γ(V.toScheme, (⊤ : V.toScheme.Opens)))))) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rw [show ((eqToHom (image_top_eq V).symm).op ≫ (eqToHom (image_top_eq V)).op) =
        𝟙 _ from by
        rw [← op_comp, eqToHom_trans, eqToHom_refl, op_id]]
      rw [CategoryTheory.Functor.map_id]
      rfl
    funext r
    rw [hsec]
    have hIso : (V.ι.appIso (⊤ : V.toScheme.Opens)).inv.hom r = r := by
      rw [Scheme.Opens.ι_appIso]
      rfl
    conv_lhs => rw [← hIso]
    rfl
  rw [hcast]
  exact hb'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 residue (i)] The multiplier of a section is its chart coefficient.** For a
normalized trivialization of the restricted unit (`eU.inv 1 = 1`), the chart multiplier
of `unitHomOfTopSection ℓ` is the image of `ℓ` under the chart trivialization of `L` —
i.e. exactly the coefficient that the pole-sheaf chart API computes. -/
theorem chartMultiplier_unitHom_eq_coefficient {L : C.Modules} (U : C.Opens)
    (ℓ : Γ(L, (⊤ : C.Opens)))
    (eU : (restrictFunctor U.ι).obj (unitObj C) ≅ unitObj U.toScheme)
    (eL : (restrictFunctor U.ι).obj L ≅ unitObj U.toScheme)
    (hnorm : eU.inv.app (⊤ : U.toScheme.Opens)
      (show Γ(unitObj U.toScheme, (⊤ : U.toScheme.Opens)) from
        (1 : Γ(U.toScheme, (⊤ : U.toScheme.Opens)))) =
      (show Γ((restrictFunctor U.ι).obj (unitObj C), (⊤ : U.toScheme.Opens)) from
        (1 : Γ(C, U.ι ''ᵁ (⊤ : U.toScheme.Opens))))) :
    chartMultiplier U (unitHomOfTopSection ℓ) eU eL =
      eL.hom.app (⊤ : U.toScheme.Opens)
        (L.presheaf.map (homOfLE (le_top :
          U.ι ''ᵁ (⊤ : U.toScheme.Opens) ≤ (⊤ : C.Opens))).op ℓ) := by
  show (eU.inv ≫ (restrictFunctor U.ι).map (unitHomOfTopSection ℓ) ≫
    eL.hom).val.app (Opposite.op (⊤ : U.toScheme.Opens))
      (1 : Γ(U.toScheme, (⊤ : U.toScheme.Opens))) = _
  have hsplit : (eU.inv ≫ (restrictFunctor U.ι).map (unitHomOfTopSection ℓ) ≫
      eL.hom).val.app (Opposite.op (⊤ : U.toScheme.Opens))
      (1 : Γ(U.toScheme, (⊤ : U.toScheme.Opens))) =
      eL.hom.app (⊤ : U.toScheme.Opens)
        (((restrictFunctor U.ι).map (unitHomOfTopSection ℓ)).app
          (⊤ : U.toScheme.Opens)
          (eU.inv.app (⊤ : U.toScheme.Opens)
            (show Γ(unitObj U.toScheme, (⊤ : U.toScheme.Opens)) from
              (1 : Γ(U.toScheme, (⊤ : U.toScheme.Opens)))))) := rfl
  rw [hsplit, hnorm]
  congr 1
  have hval := unitHomOfTopSection_app_one (M := L) ℓ
    (U.ι ''ᵁ (⊤ : U.toScheme.Opens))
  exact hval

end GeneralMultiplier

section IteratedTwist

variable {S : Scheme.{u}} {π : C ⟶ S}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The twist's chart multiplier is the general chart multiplier of the twist map. -/
theorem twistChartMultiplier_eq_chartMultiplier (J : C.IdealSheafData) (L : C.Modules)
    (U : C.Opens)
    (eI : (restrictFunctor U.ι).obj (idealModule J) ≅ unitObj U.toScheme)
    (eL : (restrictFunctor U.ι).obj L ≅ unitObj U.toScheme) :
    twistChartMultiplier J L U eI eL =
      chartMultiplier U (divisorTwistHom J L) (twistChartTensorTriv J L U eI eL) eL :=
  rfl

/-- The iterated twist: restriction to `[J₁] + [J₂]` realised on the tensor-shaped
source `I(J₁) ⊗ (I(J₂) ⊗ L)`. -/
noncomputable abbrev iteratedTwistHom (J₁ J₂ : C.IdealSheafData) (L : C.Modules) :
    tensorObj (idealModule J₁) (tensorObj (idealModule J₂) L) ⟶ L :=
  divisorTwistHom J₁ (tensorObj (idealModule J₂) L) ≫ divisorTwistHom J₂ L

/-- The chart trivialization of the iterated twist's source. -/
noncomputable abbrev iteratedChartTriv (J₁ J₂ : C.IdealSheafData) (L : C.Modules)
    (U : C.Opens)
    (eI₁ : (restrictFunctor U.ι).obj (idealModule J₁) ≅ unitObj U.toScheme)
    (eI₂ : (restrictFunctor U.ι).obj (idealModule J₂) ≅ unitObj U.toScheme)
    (eL : (restrictFunctor U.ι).obj L ≅ unitObj U.toScheme) :
    (restrictFunctor U.ι).obj
      (tensorObj (idealModule J₁) (tensorObj (idealModule J₂) L)) ≅
        unitObj U.toScheme :=
  twistChartTensorTriv J₁ (tensorObj (idealModule J₂) L) U eI₁
    (twistChartTensorTriv J₂ L U eI₂ eL)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[G6] The iterated twist's multiplier spans the product of the two generators.**
No ideal-multiplicativity isomorphism is used: the multiplier of the composite is the
product of the multipliers, and each factor's span is computed by the twist-span
theorem. -/
theorem span_iteratedChartMultiplier_eq (J₁ J₂ : C.IdealSheafData) (L : C.Modules)
    (U : C.affineOpens) (g₁ g₂ : Γ(C, U.1))
    (hspan₁ : J₁.ideal U = Ideal.span {g₁})
    (hnzd₁ : g₁ ∈ nonZeroDivisors Γ(C, U.1))
    (hspan₂ : J₂.ideal U = Ideal.span {g₂})
    (hnzd₂ : g₂ ∈ nonZeroDivisors Γ(C, U.1))
    (eI₁ : (restrictFunctor U.1.ι).obj (idealModule J₁) ≅ unitObj U.1.toScheme)
    (eI₂ : (restrictFunctor U.1.ι).obj (idealModule J₂) ≅ unitObj U.1.toScheme)
    (eL : (restrictFunctor U.1.ι).obj L ≅ unitObj U.1.toScheme) :
    Ideal.span {chartMultiplier U.1 (iteratedTwistHom J₁ J₂ L)
        (iteratedChartTriv J₁ J₂ L U.1 eI₁ eI₂ eL) eL} =
      Ideal.span {(U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g₁ *
        (U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g₂} := by
  rw [chartMultiplier_comp U.1 (divisorTwistHom J₁ (tensorObj (idealModule J₂) L))
    (divisorTwistHom J₂ L) (iteratedChartTriv J₁ J₂ L U.1 eI₁ eI₂ eL)
    (twistChartTensorTriv J₂ L U.1 eI₂ eL) eL]
  rw [← Ideal.span_singleton_mul_span_singleton,
    ← Ideal.span_singleton_mul_span_singleton]
  congr 1
  · rw [← twistChartMultiplier_eq_chartMultiplier]
    exact span_twistChartMultiplier_eq J₁ (tensorObj (idealModule J₂) L) U g₁
      hspan₁ hnzd₁ eI₁ (twistChartTensorTriv J₂ L U.1 eI₂ eL)
  · rw [← twistChartMultiplier_eq_chartMultiplier]
    exact span_twistChartMultiplier_eq J₂ L U g₂ hspan₂ hnzd₂ eI₂ eL

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[G8] The rank-`m` coordinates for a general map of invertibles.** The chart
multiplier is a product of `m` generators, each the kernel generator of an algebra
retraction; the KM 1.1.2 filtration splits the quotient into `m` copies of the base. -/
theorem nonempty_baseSections_cokernel_equiv_pi_of_mono
    {M L : C.Modules} (f : M ⟶ L) (Ua : C.affineOpens)
    (eM : (restrictFunctor Ua.1.ι).obj M ≅ unitObj Ua.1.toScheme)
    (eL : (restrictFunctor Ua.1.ι).obj L ≅ unitObj Ua.1.toScheme)
    (hbij : Function.Bijective
      (((Scheme.Modules.toSheaf C).obj (Limits.cokernel f)).1.map
        (homOfLE (le_top : Ua.1 ≤ (⊤ : C.Opens))).op))
    [Mono ((restrictFunctor Ua.1.ι).map f)]
    [Algebra Γ(S, (⊤ : S.Opens)) Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens))]
    (halg : ∀ r : Γ(S, (⊤ : S.Opens)),
      algebraMap Γ(S, (⊤ : S.Opens))
        Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens)) r =
        (Scheme.Hom.appTop (Ua.1.ι ≫ π)).hom r)
    (m : ℕ) (r : Fin m → Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens)))
    (hnzd : ∀ i, r i ∈ nonZeroDivisors Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens)))
    (σ : Fin m → (Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens)) →ₐ[Γ(S, (⊤ : S.Opens))]
      Γ(S, (⊤ : S.Opens))))
    (hker : ∀ i, RingHom.ker (σ i) = Ideal.span {r i})
    (hv : Ideal.span {chartMultiplier Ua.1 f eM eL} = Ideal.span {∏ i, r i}) :
    Nonempty ((Scheme.Modules.baseSections π (Limits.cokernel f))
      ≃ₗ[Γ(S, (⊤ : S.Opens))] (Fin m → Γ(S, (⊤ : S.Opens)))) := by
  classical
  haveI : IsAffine Ua.1.toScheme := Ua.2
  haveI hMonoEndo : Mono (ModularCurves.unitEndomorphismOfTopSection
      (chartMultiplier Ua.1 f eM eL)) :=
    mono_unitEndo_chartMultiplier Ua.1 f eM eL
  let i1 := Scheme.Modules.baseSectionsRestrictIsoOfBijective π
    (Limits.cokernel f) Ua.1 hbij
  let i2 := Scheme.Modules.baseSectionsMapIso (Ua.1.ι ≫ π)
    (Limits.PreservesCokernel.iso (restrictFunctor Ua.1.ι) f)
  let i3 := Scheme.Modules.baseSectionsMapIso (Ua.1.ι ≫ π)
    (cokernelRestrictUnitEndoIso Ua.1 f eM eL)
  obtain ⟨eCore⟩ := nonempty_baseSections_cokernel_unitEndo_equiv
    (Ua.1.ι ≫ π) (chartMultiplier Ua.1 f eM eL) halg
  let eA : (Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens)) ⧸
      Ideal.span {chartMultiplier Ua.1 f eM eL}) ≃ₗ[
        Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens))]
      (Γ(Ua.1.toScheme, (⊤ : Ua.1.toScheme.Opens)) ⧸ Ideal.span {∏ i, r i}) :=
    Submodule.quotEquivOfEq _ _ hv
  let eSpan := eA.restrictScalars Γ(S, (⊤ : S.Opens))
  obtain ⟨eFree⟩ :=
    ModularCurves.RelEffCartierDiv.SectionsIdeal.free_quotient m r hnzd σ hker
  exact ⟨(((i1 ≪≫ i2 ≪≫ i3).toLinearEquiv).trans eCore).trans
    (eSpan.trans eFree)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[G7] The rank-two coordinates of the iterated restriction at a section pair.**
Tensor-shaped source `I(P) ⊗ (I(Q) ⊗ L)`, so the output feeds the Picard assembly
directly. All hypotheses are at the level of principal kernel ideals on a chart. -/
theorem nonempty_baseSections_cokernel_iteratedTwist_equiv_pair_of_sections
    [IsSeparated π] (hsm : SmoothOfRelativeDimension 1 π)
    (P Q : { w : S ⟶ C // w ≫ π = 𝟙 S })
    (U : C.affineOpens)
    (hPU : P.1 ⁻¹ᵁ U.1 = ⊤) (hQU : Q.1 ⁻¹ᵁ U.1 = ⊤)
    (rP rQ : Γ(C, U.1))
    (hP : (Scheme.Hom.ker P.1).ideal U = Ideal.span {rP})
    (hQ : (Scheme.Hom.ker Q.1).ideal U = Ideal.span {rQ})
    (hnzdP : rP ∈ nonZeroDivisors Γ(C, U.1))
    (hnzdQ : rQ ∈ nonZeroDivisors Γ(C, U.1))
    (L : C.Modules) (hL : IsInvertible L)
    (eL : (restrictFunctor U.1.ι).obj L ≅ unitObj U.1.toScheme)
    [Algebra Γ(S, (⊤ : S.Opens)) Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))]
    (halg : ∀ r : Γ(S, (⊤ : S.Opens)),
      algebraMap Γ(S, (⊤ : S.Opens)) Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) r =
        (Scheme.Hom.appTop (U.1.ι ≫ π)).hom r) :
    Nonempty ((Scheme.Modules.baseSections π (Limits.cokernel
        (iteratedTwistHom (Scheme.Hom.ker P.1) (Scheme.Hom.ker Q.1) L)))
      ≃ₗ[Γ(S, (⊤ : S.Opens))] (Fin 2 → Γ(S, (⊤ : S.Opens)))) := by
  classical
  haveI hclP : IsClosedImmersion P.1 :=
    ModularCurves.RelEffCartierDiv.SectionsIdeal.isClosedImmersion P.2
  haveI hclQ : IsClosedImmersion Q.1 :=
    ModularCurves.RelEffCartierDiv.SectionsIdeal.isClosedImmersion Q.2
  haveI hLQ : IsInvertible (tensorObj (idealModule (Scheme.Hom.ker Q.1)) L) := by
    refine IsInvertible.tensorObj ?_ hL
    refine isInvertible_idealModule (J := Scheme.Hom.ker Q.1) ?_
    intro c
    obtain ⟨V, hcV, hV⟩ :=
      ModularCurves.RelEffCartierDiv.SectionsIdeal.exists_multiChart π hsm ![Q] c
    obtain ⟨f₀, hf₀, hf₀nzd⟩ := hV 0
    exact ⟨V, hcV, f₀, hf₀, hf₀nzd⟩
  -- the chart trivializations
  let eIP : (restrictFunctor U.1.ι).obj (idealModule (Scheme.Hom.ker P.1)) ≅
      unitObj U.1.toScheme :=
    idealModuleRestrictTrivOfSpan U rP hP hnzdP
  let eIQ : (restrictFunctor U.1.ι).obj (idealModule (Scheme.Hom.ker Q.1)) ≅
      unitObj U.1.toScheme :=
    idealModuleRestrictTrivOfSpan U rQ hQ hnzdQ
  -- the principal covers (for the two mono factors)
  have hcoverP : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      (Scheme.Hom.ker P.1).ideal V = Ideal.span {g} ∧
        g ∈ nonZeroDivisors Γ(C, V.1) := by
    intro c
    obtain ⟨V, hcV, hV⟩ :=
      ModularCurves.RelEffCartierDiv.SectionsIdeal.exists_multiChart π hsm ![P] c
    obtain ⟨f₀, hf₀, hf₀nzd⟩ := hV 0
    exact ⟨V, hcV, f₀, hf₀, hf₀nzd⟩
  have hcoverQ : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      (Scheme.Hom.ker Q.1).ideal V = Ideal.span {g} ∧
        g ∈ nonZeroDivisors Γ(C, V.1) := by
    intro c
    obtain ⟨V, hcV, hV⟩ :=
      ModularCurves.RelEffCartierDiv.SectionsIdeal.exists_multiChart π hsm ![Q] c
    obtain ⟨f₀, hf₀, hf₀nzd⟩ := hV 0
    exact ⟨V, hcV, f₀, hf₀, hf₀nzd⟩
  haveI hMonoP : Mono ((restrictFunctor U.1.ι).map
      (divisorTwistHom (Scheme.Hom.ker P.1)
        (tensorObj (idealModule (Scheme.Hom.ker Q.1)) L))) :=
    mono_restrictFunctor_map_of_isLocallyInjective _
      (isLocallyInjective_divisorTwistHom _ _ hcoverP hLQ) U.1
  haveI hMonoQ : Mono ((restrictFunctor U.1.ι).map
      (divisorTwistHom (Scheme.Hom.ker Q.1) L)) :=
    mono_restrictFunctor_map_of_isLocallyInjective _
      (isLocallyInjective_divisorTwistHom _ L hcoverQ hL) U.1
  haveI hMono : Mono ((restrictFunctor U.1.ι).map
      (iteratedTwistHom (Scheme.Hom.ker P.1) (Scheme.Hom.ker Q.1) L)) := by
    rw [show (restrictFunctor U.1.ι).map
        (iteratedTwistHom (Scheme.Hom.ker P.1) (Scheme.Hom.ker Q.1) L) =
      (restrictFunctor U.1.ι).map (divisorTwistHom (Scheme.Hom.ker P.1)
        (tensorObj (idealModule (Scheme.Hom.ker Q.1)) L)) ≫
      (restrictFunctor U.1.ι).map (divisorTwistHom (Scheme.Hom.ker Q.1) L) from
      Functor.map_comp _ _ _]
    infer_instance
  -- concentration off the two section images
  have hrangeP : ∀ s, P.1.base s ∈ U.1 := fun s => by
    have : s ∈ P.1 ⁻¹ᵁ U.1 := by rw [hPU]; trivial
    exact this
  have hrangeQ : ∀ s, Q.1.base s ∈ U.1 := fun s => by
    have : s ∈ Q.1 ⁻¹ᵁ U.1 := by rw [hQU]; trivial
    exact this
  let V : C.Opens := ⟨(Set.range P.1.base ∪ Set.range Q.1.base)ᶜ,
    (IsClosed.union P.1.isClosedEmbedding.isClosed_range
      Q.1.isClosedEmbedding.isClosed_range).isOpen_compl⟩
  have hUV : U.1 ⊔ V = ⊤ := by
    refine le_antisymm le_top ?_
    intro c _
    by_cases hc : c ∈ Set.range P.1.base ∪ Set.range Q.1.base
    · rcases hc with ⟨s, rfl⟩ | ⟨s, rfl⟩
      · exact Or.inl (hrangeP s)
      · exact Or.inl (hrangeQ s)
    · exact Or.inr hc
  have hzero : ∀ W : C.Opens, W ≤ V →
      Limits.IsZero ((restrictFunctor W.ι).obj (Limits.cokernel
        (iteratedTwistHom (Scheme.Hom.ker P.1) (Scheme.Hom.ker Q.1) L))) := by
    intro W hWV
    refine isZero_restrict_cokernel_comp _ _ W ?_ ?_
    · refine isZero_restrict_cokernel_divisorTwistHom _ _ W ?_
      intro W' hW'
      refine one_mem_idealSections_of_disjoint_support _ W' ?_
      rw [Scheme.Hom.support_ker,
        P.1.isClosedEmbedding.isClosed_range.closure_eq]
      refine Set.disjoint_left.mpr fun c hc hcW => ?_
      exact (hWV (hW' hcW)) (Or.inl hc)
    · refine isZero_restrict_cokernel_divisorTwistHom _ _ W ?_
      intro W' hW'
      refine one_mem_idealSections_of_disjoint_support _ W' ?_
      rw [Scheme.Hom.support_ker,
        Q.1.isClosedEmbedding.isClosed_range.closure_eq]
      refine Set.disjoint_left.mpr fun c hc hcW => ?_
      exact (hWV (hW' hcW)) (Or.inr hc)
  have hbij := cokernel_bijective_restrict_of_isZero _ U.1 V hUV hzero
  -- the span of the composite multiplier and the evaluation equivalences
  have hv := span_iteratedChartMultiplier_eq (Scheme.Hom.ker P.1)
    (Scheme.Hom.ker Q.1) L U rP rQ hP hnzdP hQ hnzdQ eIP eIQ eL
  have hg'nzdP : (U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom rP ∈
      nonZeroDivisors Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) := by
    rw [← MulEquivClass.map_nonZeroDivisors
      (asIso (U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge)).commRingCatIsoToRingEquiv]
    exact ⟨rP, hnzdP, rfl⟩
  obtain ⟨eP⟩ := nonempty_evaluation_quotEquiv_of_ker_span P.1 P.2 U hPU rP hP halg
  obtain ⟨eQ⟩ := nonempty_evaluation_quotEquiv_of_ker_span Q.1 Q.2 U hQU rQ hQ halg
  exact nonempty_baseSections_cokernel_equiv_pair_of_mono _ U
    (iteratedChartTriv (Scheme.Hom.ker P.1) (Scheme.Hom.ker Q.1) L U.1 eIP eIQ eL)
    eL hbij _ _ hv hg'nzdP halg eP eQ

/-- The triple iterated twist: restriction to `[J₁] + [J₂] + [J₃]` on the
tensor-shaped source. -/
noncomputable abbrev iteratedTwistHom₃ (J₁ J₂ J₃ : C.IdealSheafData) (L : C.Modules) :
    tensorObj (idealModule J₁)
      (tensorObj (idealModule J₂) (tensorObj (idealModule J₃) L)) ⟶ L :=
  divisorTwistHom J₁ (tensorObj (idealModule J₂) (tensorObj (idealModule J₃) L)) ≫
    iteratedTwistHom J₂ J₃ L

/-- The chart trivialization of the triple iterated twist's source. -/
noncomputable abbrev iteratedChartTriv₃ (J₁ J₂ J₃ : C.IdealSheafData) (L : C.Modules)
    (U : C.Opens)
    (eI₁ : (restrictFunctor U.ι).obj (idealModule J₁) ≅ unitObj U.toScheme)
    (eI₂ : (restrictFunctor U.ι).obj (idealModule J₂) ≅ unitObj U.toScheme)
    (eI₃ : (restrictFunctor U.ι).obj (idealModule J₃) ≅ unitObj U.toScheme)
    (eL : (restrictFunctor U.ι).obj L ≅ unitObj U.toScheme) :
    (restrictFunctor U.ι).obj (tensorObj (idealModule J₁)
      (tensorObj (idealModule J₂) (tensorObj (idealModule J₃) L))) ≅
        unitObj U.toScheme :=
  twistChartTensorTriv J₁ (tensorObj (idealModule J₂) (tensorObj (idealModule J₃) L))
    U eI₁ (iteratedChartTriv J₂ J₃ L U eI₂ eI₃ eL)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[G9] The triple iterated twist's multiplier spans the product of the three chart
generators.** -/
theorem span_iteratedChartMultiplier₃_eq (J₁ J₂ J₃ : C.IdealSheafData) (L : C.Modules)
    (U : C.affineOpens) (g₁ g₂ g₃ : Γ(C, U.1))
    (hspan₁ : J₁.ideal U = Ideal.span {g₁})
    (hnzd₁ : g₁ ∈ nonZeroDivisors Γ(C, U.1))
    (hspan₂ : J₂.ideal U = Ideal.span {g₂})
    (hnzd₂ : g₂ ∈ nonZeroDivisors Γ(C, U.1))
    (hspan₃ : J₃.ideal U = Ideal.span {g₃})
    (hnzd₃ : g₃ ∈ nonZeroDivisors Γ(C, U.1))
    (eI₁ : (restrictFunctor U.1.ι).obj (idealModule J₁) ≅ unitObj U.1.toScheme)
    (eI₂ : (restrictFunctor U.1.ι).obj (idealModule J₂) ≅ unitObj U.1.toScheme)
    (eI₃ : (restrictFunctor U.1.ι).obj (idealModule J₃) ≅ unitObj U.1.toScheme)
    (eL : (restrictFunctor U.1.ι).obj L ≅ unitObj U.1.toScheme) :
    Ideal.span {chartMultiplier U.1 (iteratedTwistHom₃ J₁ J₂ J₃ L)
        (iteratedChartTriv₃ J₁ J₂ J₃ L U.1 eI₁ eI₂ eI₃ eL) eL} =
      Ideal.span {(U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g₁ *
        ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g₂ *
          (U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g₃)} := by
  rw [chartMultiplier_comp U.1
    (divisorTwistHom J₁ (tensorObj (idealModule J₂) (tensorObj (idealModule J₃) L)))
    (iteratedTwistHom J₂ J₃ L)
    (iteratedChartTriv₃ J₁ J₂ J₃ L U.1 eI₁ eI₂ eI₃ eL)
    (iteratedChartTriv J₂ J₃ L U.1 eI₂ eI₃ eL) eL]
  rw [← Ideal.span_singleton_mul_span_singleton,
    ← Ideal.span_singleton_mul_span_singleton]
  congr 1
  · rw [← twistChartMultiplier_eq_chartMultiplier]
    exact span_twistChartMultiplier_eq J₁
      (tensorObj (idealModule J₂) (tensorObj (idealModule J₃) L)) U g₁
      hspan₁ hnzd₁ eI₁ (iteratedChartTriv J₂ J₃ L U.1 eI₂ eI₃ eL)
  · exact span_iteratedChartMultiplier_eq J₂ J₃ L U g₂ g₃ hspan₂ hnzd₂ hspan₃ hnzd₃
      eI₂ eI₃ eL

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[G9] The rank-three coordinates of the triple iterated restriction.** For three
sections on a common principal chart, the base sections of the triple restriction
cokernel are free of rank three, on the tensor-shaped source
`I(P) ⊗ (I(Q) ⊗ (I(R) ⊗ L))`. -/
theorem nonempty_baseSections_cokernel_iteratedTwist₃_equiv_of_sections
    [IsSeparated π] (hsm : SmoothOfRelativeDimension 1 π)
    (P Q R : { w : S ⟶ C // w ≫ π = 𝟙 S })
    (U : C.affineOpens)
    (hPU : P.1 ⁻¹ᵁ U.1 = ⊤) (hQU : Q.1 ⁻¹ᵁ U.1 = ⊤) (hRU : R.1 ⁻¹ᵁ U.1 = ⊤)
    (rP rQ rR : Γ(C, U.1))
    (hP : (Scheme.Hom.ker P.1).ideal U = Ideal.span {rP})
    (hQ : (Scheme.Hom.ker Q.1).ideal U = Ideal.span {rQ})
    (hR : (Scheme.Hom.ker R.1).ideal U = Ideal.span {rR})
    (hnzdP : rP ∈ nonZeroDivisors Γ(C, U.1))
    (hnzdQ : rQ ∈ nonZeroDivisors Γ(C, U.1))
    (hnzdR : rR ∈ nonZeroDivisors Γ(C, U.1))
    (L : C.Modules) (hL : IsInvertible L)
    (eL : (restrictFunctor U.1.ι).obj L ≅ unitObj U.1.toScheme)
    [Algebra Γ(S, (⊤ : S.Opens)) Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))]
    (halg : ∀ r : Γ(S, (⊤ : S.Opens)),
      algebraMap Γ(S, (⊤ : S.Opens)) Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) r =
        (Scheme.Hom.appTop (U.1.ι ≫ π)).hom r) :
    Nonempty ((Scheme.Modules.baseSections π (Limits.cokernel
        (iteratedTwistHom₃ (Scheme.Hom.ker P.1) (Scheme.Hom.ker Q.1)
          (Scheme.Hom.ker R.1) L)))
      ≃ₗ[Γ(S, (⊤ : S.Opens))] (Fin 3 → Γ(S, (⊤ : S.Opens)))) := by
  classical
  haveI hclP : IsClosedImmersion P.1 :=
    ModularCurves.RelEffCartierDiv.SectionsIdeal.isClosedImmersion P.2
  haveI hclQ : IsClosedImmersion Q.1 :=
    ModularCurves.RelEffCartierDiv.SectionsIdeal.isClosedImmersion Q.2
  haveI hclR : IsClosedImmersion R.1 :=
    ModularCurves.RelEffCartierDiv.SectionsIdeal.isClosedImmersion R.2
  -- principal covers for each section (for invertibility and the mono chain)
  have hcover : ∀ (Z : { w : S ⟶ C // w ≫ π = 𝟙 S }) (c : ↥C),
      ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
        (Scheme.Hom.ker Z.1).ideal V = Ideal.span {g} ∧
          g ∈ nonZeroDivisors Γ(C, V.1) := by
    intro Z c
    obtain ⟨V, hcV, hV⟩ :=
      ModularCurves.RelEffCartierDiv.SectionsIdeal.exists_multiChart π hsm ![Z] c
    obtain ⟨f₀, hf₀, hf₀nzd⟩ := hV 0
    exact ⟨V, hcV, f₀, hf₀, hf₀nzd⟩
  haveI hLR : IsInvertible (tensorObj (idealModule (Scheme.Hom.ker R.1)) L) :=
    IsInvertible.tensorObj
      (isInvertible_idealModule (J := Scheme.Hom.ker R.1) (hcover R)) hL
  haveI hLQR : IsInvertible (tensorObj (idealModule (Scheme.Hom.ker Q.1))
      (tensorObj (idealModule (Scheme.Hom.ker R.1)) L)) :=
    IsInvertible.tensorObj
      (isInvertible_idealModule (J := Scheme.Hom.ker Q.1) (hcover Q)) hLR
  let eIP := idealModuleRestrictTrivOfSpan U rP hP hnzdP
  let eIQ := idealModuleRestrictTrivOfSpan U rQ hQ hnzdQ
  let eIR := idealModuleRestrictTrivOfSpan U rR hR hnzdR
  -- monos
  haveI hMonoR : Mono ((restrictFunctor U.1.ι).map
      (divisorTwistHom (Scheme.Hom.ker R.1) L)) :=
    mono_restrictFunctor_map_of_isLocallyInjective _
      (isLocallyInjective_divisorTwistHom _ L (hcover R) hL) U.1
  haveI hMonoQ : Mono ((restrictFunctor U.1.ι).map
      (divisorTwistHom (Scheme.Hom.ker Q.1)
        (tensorObj (idealModule (Scheme.Hom.ker R.1)) L))) :=
    mono_restrictFunctor_map_of_isLocallyInjective _
      (isLocallyInjective_divisorTwistHom _ _ (hcover Q) hLR) U.1
  haveI hMonoP : Mono ((restrictFunctor U.1.ι).map
      (divisorTwistHom (Scheme.Hom.ker P.1)
        (tensorObj (idealModule (Scheme.Hom.ker Q.1))
          (tensorObj (idealModule (Scheme.Hom.ker R.1)) L)))) :=
    mono_restrictFunctor_map_of_isLocallyInjective _
      (isLocallyInjective_divisorTwistHom _ _ (hcover P) hLQR) U.1
  haveI hMono : Mono ((restrictFunctor U.1.ι).map
      (iteratedTwistHom₃ (Scheme.Hom.ker P.1) (Scheme.Hom.ker Q.1)
        (Scheme.Hom.ker R.1) L)) := by
    rw [show (restrictFunctor U.1.ι).map (iteratedTwistHom₃ (Scheme.Hom.ker P.1)
        (Scheme.Hom.ker Q.1) (Scheme.Hom.ker R.1) L) =
      (restrictFunctor U.1.ι).map (divisorTwistHom (Scheme.Hom.ker P.1)
        (tensorObj (idealModule (Scheme.Hom.ker Q.1))
          (tensorObj (idealModule (Scheme.Hom.ker R.1)) L))) ≫
      ((restrictFunctor U.1.ι).map (divisorTwistHom (Scheme.Hom.ker Q.1)
        (tensorObj (idealModule (Scheme.Hom.ker R.1)) L)) ≫
        (restrictFunctor U.1.ι).map (divisorTwistHom (Scheme.Hom.ker R.1) L)) from by
      rw [← Functor.map_comp, ← Functor.map_comp]]
    infer_instance
  -- concentration off the three section images
  have hrange : ∀ (Z : { w : S ⟶ C // w ≫ π = 𝟙 S }),
      Z.1 ⁻¹ᵁ U.1 = ⊤ → ∀ s, Z.1.base s ∈ U.1 := by
    intro Z hZU s
    have : s ∈ Z.1 ⁻¹ᵁ U.1 := by rw [hZU]; trivial
    exact this
  let V : C.Opens := ⟨(Set.range P.1.base ∪ Set.range Q.1.base ∪
      Set.range R.1.base)ᶜ,
    ((P.1.isClosedEmbedding.isClosed_range.union
      Q.1.isClosedEmbedding.isClosed_range).union
      R.1.isClosedEmbedding.isClosed_range).isOpen_compl⟩
  have hUV : U.1 ⊔ V = ⊤ := by
    refine le_antisymm le_top ?_
    intro c _
    by_cases hc : c ∈ Set.range P.1.base ∪ Set.range Q.1.base ∪ Set.range R.1.base
    · rcases hc with (⟨s, rfl⟩ | ⟨s, rfl⟩) | ⟨s, rfl⟩
      · exact Or.inl (hrange P hPU s)
      · exact Or.inl (hrange Q hQU s)
      · exact Or.inl (hrange R hRU s)
    · exact Or.inr hc
  have hzeroOf : ∀ (Z : { w : S ⟶ C // w ≫ π = 𝟙 S })
      (_ : IsClosedImmersion Z.1) (N : C.Modules) (W : C.Opens),
      (∀ c, c ∈ W → c ∉ Set.range Z.1.base) →
      Limits.IsZero ((restrictFunctor W.ι).obj (Limits.cokernel
        (divisorTwistHom (Scheme.Hom.ker Z.1) N))) := by
    intro Z hZ N W hW
    haveI := hZ
    refine isZero_restrict_cokernel_divisorTwistHom _ _ W ?_
    intro W' hW'
    refine one_mem_idealSections_of_disjoint_support _ W' ?_
    rw [Scheme.Hom.support_ker, Z.1.isClosedEmbedding.isClosed_range.closure_eq]
    refine Set.disjoint_left.mpr fun c hc hcW => ?_
    exact hW c (hW' hcW) hc
  have hzero : ∀ W : C.Opens, W ≤ V →
      Limits.IsZero ((restrictFunctor W.ι).obj (Limits.cokernel
        (iteratedTwistHom₃ (Scheme.Hom.ker P.1) (Scheme.Hom.ker Q.1)
          (Scheme.Hom.ker R.1) L))) := by
    intro W hWV
    refine isZero_restrict_cokernel_comp _ _ W
      (hzeroOf P hclP _ W fun c hc hcr => (hWV hc) (Or.inl (Or.inl hcr))) ?_
    refine isZero_restrict_cokernel_comp _ _ W
      (hzeroOf Q hclQ _ W fun c hc hcr => (hWV hc) (Or.inl (Or.inr hcr)))
      (hzeroOf R hclR _ W fun c hc hcr => (hWV hc) (Or.inr hcr))
  have hbij := cokernel_bijective_restrict_of_isZero _ U.1 V hUV hzero
  -- the three retractions and the span of the composite multiplier
  obtain ⟨σP, hσP⟩ := exists_algHom_ker_eq_span_of_section P.1 P.2 U hPU rP hP halg
  obtain ⟨σQ, hσQ⟩ := exists_algHom_ker_eq_span_of_section Q.1 Q.2 U hQU rQ hQ halg
  obtain ⟨σR, hσR⟩ := exists_algHom_ker_eq_span_of_section R.1 R.2 U hRU rR hR halg
  have hnzdOf : ∀ g : Γ(C, U.1), g ∈ nonZeroDivisors Γ(C, U.1) →
      (U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g ∈
        nonZeroDivisors Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) := by
    intro g hg
    rw [← MulEquivClass.map_nonZeroDivisors
      (asIso (U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge)).commRingCatIsoToRingEquiv]
    exact ⟨g, hg, rfl⟩
  have hv := span_iteratedChartMultiplier₃_eq (Scheme.Hom.ker P.1)
    (Scheme.Hom.ker Q.1) (Scheme.Hom.ker R.1) L U rP rQ rR
    hP hnzdP hQ hnzdQ hR hnzdR eIP eIQ eIR eL
  refine nonempty_baseSections_cokernel_equiv_pi_of_mono _ U
    (iteratedChartTriv₃ (Scheme.Hom.ker P.1) (Scheme.Hom.ker Q.1)
      (Scheme.Hom.ker R.1) L U.1 eIP eIQ eIR eL) eL hbij halg 3
    ![(U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom rP,
      (U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom rQ,
      (U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom rR]
    ?_ ![σP, σQ, σR] ?_ ?_
  · intro i
    fin_cases i
    · exact hnzdOf rP hnzdP
    · exact hnzdOf rQ hnzdQ
    · exact hnzdOf rR hnzdR
  · intro i
    fin_cases i
    · exact hσP
    · exact hσQ
    · exact hσR
  · rw [hv, Fin.prod_univ_three]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [mul_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The iterated line.** For a section pair on a principal chart and an invertible
`L` with a rank-three basis of base sections, the kernel of the iterated restriction
is free of rank one, spanned by the cross product of the evaluation rows — the
tensor-shaped counterpart of `exists_ker_baseSectionsMap_cokernel_eq_span_of_sections`.
The surjectivity input is where the cohomology enters. -/
theorem exists_ker_baseSectionsMap_cokernel_iteratedTwist_eq_span_of_sections
    [IsSeparated π] (hsm : SmoothOfRelativeDimension 1 π)
    (P Q : { w : S ⟶ C // w ≫ π = 𝟙 S })
    (U : C.affineOpens)
    (hPU : P.1 ⁻¹ᵁ U.1 = ⊤) (hQU : Q.1 ⁻¹ᵁ U.1 = ⊤)
    (rP rQ : Γ(C, U.1))
    (hP : (Scheme.Hom.ker P.1).ideal U = Ideal.span {rP})
    (hQ : (Scheme.Hom.ker Q.1).ideal U = Ideal.span {rQ})
    (hnzdP : rP ∈ nonZeroDivisors Γ(C, U.1))
    (hnzdQ : rQ ∈ nonZeroDivisors Γ(C, U.1))
    (L : C.Modules) (hL : IsInvertible L)
    (eL : (restrictFunctor U.1.ι).obj L ≅ unitObj U.1.toScheme)
    [Algebra Γ(S, (⊤ : S.Opens)) Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))]
    (halg : ∀ r : Γ(S, (⊤ : S.Opens)),
      algebraMap Γ(S, (⊤ : S.Opens)) Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) r =
        (Scheme.Hom.appTop (U.1.ι ≫ π)).hom r)
    (hsurj : Function.Surjective
      ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π
        (iteratedTwistHom (Scheme.Hom.ker P.1) (Scheme.Hom.ker Q.1) L))).hom))
    (b3 : Module.Basis (Fin 3) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π L)) :
    ∃ ℓ : Scheme.Modules.baseSections π L,
      LinearMap.ker ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π
        (iteratedTwistHom (Scheme.Hom.ker P.1) (Scheme.Hom.ker Q.1) L))).hom) =
      Submodule.span Γ(S, (⊤ : S.Opens)) {ℓ} := by
  classical
  obtain ⟨e2⟩ := nonempty_baseSections_cokernel_iteratedTwist_equiv_pair_of_sections
    hsm P Q U hPU hQU rP rQ hP hQ hnzdP hnzdQ L hL eL halg
  exact ⟨b3.equivFun.symm
      ((fun j => e2 ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π
        (iteratedTwistHom (Scheme.Hom.ker P.1) (Scheme.Hom.ker Q.1) L)))
          (b3 j)) 0) ⨯₃
       (fun j => e2 ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π
        (iteratedTwistHom (Scheme.Hom.ker P.1) (Scheme.Hom.ker Q.1) L)))
          (b3 j)) 1)),
    ker_baseSectionsMap_cokernel_eq_span_crossProduct_of_surjective _ b3 e2 hsurj⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Monomorphy of the triple iterated twist, from principal covers of the three
ideals and invertibility of the ambient module. -/
theorem mono_iteratedTwistHom₃ (J₁ J₂ J₃ : C.IdealSheafData) (L : C.Modules)
    (h₁ : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      J₁.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (h₂ : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      J₂.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (h₃ : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      J₃.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (hL : IsInvertible L) :
    Mono (iteratedTwistHom₃ J₁ J₂ J₃ L) := by
  haveI hL₃ : IsInvertible (tensorObj (idealModule J₃) L) :=
    IsInvertible.tensorObj (isInvertible_idealModule (J := J₃) h₃) hL
  haveI hL₂₃ : IsInvertible (tensorObj (idealModule J₂)
      (tensorObj (idealModule J₃) L)) :=
    IsInvertible.tensorObj (isInvertible_idealModule (J := J₂) h₂) hL₃
  haveI m₃ : Mono (divisorTwistHom J₃ L) := mono_divisorTwistHom _ L h₃ hL
  haveI m₂ : Mono (divisorTwistHom J₂ (tensorObj (idealModule J₃) L)) :=
    mono_divisorTwistHom _ _ h₂ hL₃
  haveI m₁ : Mono (divisorTwistHom J₁ (tensorObj (idealModule J₂)
      (tensorObj (idealModule J₃) L))) :=
    mono_divisorTwistHom _ _ h₁ hL₂₃
  exact mono_comp _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Monomorphy of the restricted triple iterated twist on every open. -/
theorem mono_restrict_iteratedTwistHom₃ (J₁ J₂ J₃ : C.IdealSheafData) (L : C.Modules)
    (h₁ : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      J₁.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (h₂ : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      J₂.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (h₃ : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      J₃.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (hL : IsInvertible L) (W : C.Opens) :
    Mono ((restrictFunctor W.ι).map (iteratedTwistHom₃ J₁ J₂ J₃ L)) := by
  haveI hL₃ : IsInvertible (tensorObj (idealModule J₃) L) :=
    IsInvertible.tensorObj (isInvertible_idealModule (J := J₃) h₃) hL
  haveI hL₂₃ : IsInvertible (tensorObj (idealModule J₂)
      (tensorObj (idealModule J₃) L)) :=
    IsInvertible.tensorObj (isInvertible_idealModule (J := J₂) h₂) hL₃
  haveI m₃ : Mono ((restrictFunctor W.ι).map (divisorTwistHom J₃ L)) :=
    mono_restrictFunctor_map_of_isLocallyInjective _
      (isLocallyInjective_divisorTwistHom _ L h₃ hL) W
  haveI m₂ : Mono ((restrictFunctor W.ι).map
      (divisorTwistHom J₂ (tensorObj (idealModule J₃) L))) :=
    mono_restrictFunctor_map_of_isLocallyInjective _
      (isLocallyInjective_divisorTwistHom _ _ h₂ hL₃) W
  haveI m₁ : Mono ((restrictFunctor W.ι).map (divisorTwistHom J₁
      (tensorObj (idealModule J₂) (tensorObj (idealModule J₃) L)))) :=
    mono_restrictFunctor_map_of_isLocallyInjective _
      (isLocallyInjective_divisorTwistHom _ _ h₁ hL₂₃) W
  rw [show (restrictFunctor W.ι).map (iteratedTwistHom₃ J₁ J₂ J₃ L) =
    (restrictFunctor W.ι).map (divisorTwistHom J₁ (tensorObj (idealModule J₂)
      (tensorObj (idealModule J₃) L))) ≫
    ((restrictFunctor W.ι).map (divisorTwistHom J₂
      (tensorObj (idealModule J₃) L)) ≫
      (restrictFunctor W.ι).map (divisorTwistHom J₃ L)) from by
    rw [← Functor.map_comp, ← Functor.map_comp]]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[CHORD-PKG] The triple trivialization from the exact-order chart identity.**
A global section of `L` that vanishes on `[J₁] + [J₂] + [J₃]` and whose chart
multiplier is, on each chart of a trivializing cover, a unit multiple of the product
of the three generators, trivializes the triple twist:
`I(J₁) ⊗ (I(J₂) ⊗ (I(J₃) ⊗ L)) ≅ 𝒪`. This is the exact shape the theorem-of-the-square
assembly consumes. -/
theorem nonempty_iso_unitObj_of_exact_order₃
    (J₁ J₂ J₃ : C.IdealSheafData) (L : C.Modules)
    (h₁ : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      J₁.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (h₂ : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      J₂.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (h₃ : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      J₃.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (hL : IsInvertible L)
    (ℓ : Γ(L, (⊤ : C.Opens)))
    (hℓ : (Limits.cokernel.π (iteratedTwistHom₃ J₁ J₂ J₃ L)).app (⊤ : C.Opens) ℓ = 0)
    {ι : Type u} (W : ι → C.Opens) (hW : iSup W = ⊤)
    (eM : ∀ i, (restrictFunctor (W i).ι).obj (tensorObj (idealModule J₁)
      (tensorObj (idealModule J₂) (tensorObj (idealModule J₃) L))) ≅
        unitObj (W i).toScheme)
    (eL : ∀ i, (restrictFunctor (W i).ι).obj L ≅ unitObj (W i).toScheme)
    (eU : ∀ i, (restrictFunctor (W i).ι).obj (unitObj C) ≅ unitObj (W i).toScheme)
    (u : ∀ i, Γ(((W i).toScheme), (⊤ : ((W i).toScheme).Opens))ˣ)
    (hexact : ∀ i, chartMultiplier (W i) (unitHomOfTopSection ℓ) (eU i) (eL i) =
      (u i : Γ(((W i).toScheme), (⊤ : ((W i).toScheme).Opens))) *
        chartMultiplier (W i) (iteratedTwistHom₃ J₁ J₂ J₃ L) (eM i) (eL i)) :
    Nonempty (tensorObj (idealModule J₁)
      (tensorObj (idealModule J₂) (tensorObj (idealModule J₃) L)) ≅ unitObj C) := by
  haveI hmono : Mono (iteratedTwistHom₃ J₁ J₂ J₃ L) :=
    mono_iteratedTwistHom₃ J₁ J₂ J₃ L h₁ h₂ h₃ hL
  haveI hiso : IsIso (monoSectionLift (iteratedTwistHom₃ J₁ J₂ J₃ L) ℓ hℓ) :=
    isIso_monoSectionLift_of_multiplier_eq_unit_mul _ ℓ hℓ W hW eM eL eU
      (fun i => mono_restrict_iteratedTwistHom₃ J₁ J₂ J₃ L h₁ h₂ h₃ hL (W i))
      u hexact
  exact ⟨(asIso (monoSectionLift (iteratedTwistHom₃ J₁ J₂ J₃ L) ℓ hℓ)).symm⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[VERT-PKG] The two-factor trivialization from the exact-order chart identity** —
the vertical's counterpart of `nonempty_iso_unitObj_of_exact_order₃`. -/
theorem nonempty_iso_unitObj_of_exact_order₂
    (J₁ J₂ : C.IdealSheafData) (L : C.Modules)
    (h₁ : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      J₁.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (h₂ : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      J₂.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (hL : IsInvertible L)
    (ℓ : Γ(L, (⊤ : C.Opens)))
    (hℓ : (Limits.cokernel.π (iteratedTwistHom J₁ J₂ L)).app (⊤ : C.Opens) ℓ = 0)
    {ι : Type u} (W : ι → C.Opens) (hW : iSup W = ⊤)
    (eM : ∀ i, (restrictFunctor (W i).ι).obj (tensorObj (idealModule J₁)
      (tensorObj (idealModule J₂) L)) ≅ unitObj (W i).toScheme)
    (eL : ∀ i, (restrictFunctor (W i).ι).obj L ≅ unitObj (W i).toScheme)
    (eU : ∀ i, (restrictFunctor (W i).ι).obj (unitObj C) ≅ unitObj (W i).toScheme)
    (u : ∀ i, Γ(((W i).toScheme), (⊤ : ((W i).toScheme).Opens))ˣ)
    (hexact : ∀ i, chartMultiplier (W i) (unitHomOfTopSection ℓ) (eU i) (eL i) =
      (u i : Γ(((W i).toScheme), (⊤ : ((W i).toScheme).Opens))) *
        chartMultiplier (W i) (iteratedTwistHom J₁ J₂ L) (eM i) (eL i)) :
    Nonempty (tensorObj (idealModule J₁) (tensorObj (idealModule J₂) L) ≅
      unitObj C) := by
  haveI hL₂ : IsInvertible (tensorObj (idealModule J₂) L) :=
    IsInvertible.tensorObj (isInvertible_idealModule (J := J₂) h₂) hL
  haveI m₂ : Mono (divisorTwistHom J₂ L) := mono_divisorTwistHom _ L h₂ hL
  haveI m₁ : Mono (divisorTwistHom J₁ (tensorObj (idealModule J₂) L)) :=
    mono_divisorTwistHom _ _ h₁ hL₂
  haveI hmono : Mono (iteratedTwistHom J₁ J₂ L) := mono_comp _ _
  haveI hiso : IsIso (monoSectionLift (iteratedTwistHom J₁ J₂ L) ℓ hℓ) := by
    refine isIso_monoSectionLift_of_multiplier_eq_unit_mul _ ℓ hℓ W hW eM eL eU
      (fun i => ?_) u hexact
    haveI mr₂ : Mono ((restrictFunctor (W i).ι).map (divisorTwistHom J₂ L)) :=
      mono_restrictFunctor_map_of_isLocallyInjective _
        (isLocallyInjective_divisorTwistHom _ L h₂ hL) (W i)
    haveI mr₁ : Mono ((restrictFunctor (W i).ι).map
        (divisorTwistHom J₁ (tensorObj (idealModule J₂) L))) :=
      mono_restrictFunctor_map_of_isLocallyInjective _
        (isLocallyInjective_divisorTwistHom _ _ h₁ hL₂) (W i)
    rw [show (restrictFunctor (W i).ι).map (iteratedTwistHom J₁ J₂ L) =
      (restrictFunctor (W i).ι).map
        (divisorTwistHom J₁ (tensorObj (idealModule J₂) L)) ≫
      (restrictFunctor (W i).ι).map (divisorTwistHom J₂ L) from
      Functor.map_comp _ _ _]
    infer_instance
  exact ⟨(asIso (monoSectionLift (iteratedTwistHom J₁ J₂ L) ℓ hℓ)).symm⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1-b] The chord exists from unimodular evaluation data.** With the rank-two
coordinates of the pair restriction and a rank-three basis upstairs, unimodularity of
the evaluation rows' cross product produces a section of `L` spanning the kernel of the
restriction to `[P] + [Q]` — the chord, with no cohomological input. -/
theorem exists_chord_of_unimodular
    [IsSeparated π] (hsm : SmoothOfRelativeDimension 1 π)
    (P Q : { w : S ⟶ C // w ≫ π = 𝟙 S })
    (U : C.affineOpens)
    (hPU : P.1 ⁻¹ᵁ U.1 = ⊤) (hQU : Q.1 ⁻¹ᵁ U.1 = ⊤)
    (rP rQ : Γ(C, U.1))
    (hP : (Scheme.Hom.ker P.1).ideal U = Ideal.span {rP})
    (hQ : (Scheme.Hom.ker Q.1).ideal U = Ideal.span {rQ})
    (hnzdP : rP ∈ nonZeroDivisors Γ(C, U.1))
    (hnzdQ : rQ ∈ nonZeroDivisors Γ(C, U.1))
    (L : C.Modules) (hL : IsInvertible L)
    (eL : (restrictFunctor U.1.ι).obj L ≅ unitObj U.1.toScheme)
    [Algebra Γ(S, (⊤ : S.Opens)) Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))]
    (halg : ∀ r : Γ(S, (⊤ : S.Opens)),
      algebraMap Γ(S, (⊤ : S.Opens)) Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) r =
        (Scheme.Hom.appTop (U.1.ι ≫ π)).hom r)
    (b3 : Module.Basis (Fin 3) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π L))
    (e2 : Scheme.Modules.baseSections π (Limits.cokernel
        (iteratedTwistHom (Scheme.Hom.ker P.1) (Scheme.Hom.ker Q.1) L))
      ≃ₗ[Γ(S, (⊤ : S.Opens))] (Fin 2 → Γ(S, (⊤ : S.Opens))))
    (huni : Ideal.span (Set.range
      ((fun j => e2 ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π
          (iteratedTwistHom (Scheme.Hom.ker P.1) (Scheme.Hom.ker Q.1) L)))
            (b3 j)) 0) ⨯₃
       (fun j => e2 ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π
          (iteratedTwistHom (Scheme.Hom.ker P.1) (Scheme.Hom.ker Q.1) L)))
            (b3 j)) 1))) = ⊤) :
    ∃ ℓ : Scheme.Modules.baseSections π L,
      LinearMap.ker ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π
        (iteratedTwistHom (Scheme.Hom.ker P.1) (Scheme.Hom.ker Q.1) L))).hom) =
      Submodule.span Γ(S, (⊤ : S.Opens)) {ℓ} :=
  exists_ker_baseSectionsMap_cokernel_iteratedTwist_eq_span_of_sections
    hsm P Q U hPU hQU rP rQ hP hQ hnzdP hnzdQ L hL eL halg
    (surjective_baseSectionsMap_cokernel_of_unimodular _ b3 e2 huni) b3

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1-c] The vertical exists from a unimodular evaluation row** — the rank-one
counterpart of `exists_chord_of_unimodular`. -/
theorem exists_vertical_of_unimodular
    [IsSeparated π] (hsm : SmoothOfRelativeDimension 1 π)
    (R : { w : S ⟶ C // w ≫ π = 𝟙 S })
    (U : C.affineOpens) (hRU : R.1 ⁻¹ᵁ U.1 = ⊤)
    (rR : Γ(C, U.1))
    (hR : (Scheme.Hom.ker R.1).ideal U = Ideal.span {rR})
    (hnzdR : rR ∈ nonZeroDivisors Γ(C, U.1))
    (L : C.Modules) (hL : IsInvertible L)
    (eL : (restrictFunctor U.1.ι).obj L ≅ unitObj U.1.toScheme)
    [Algebra Γ(S, (⊤ : S.Opens)) Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))]
    (halg : ∀ r : Γ(S, (⊤ : S.Opens)),
      algebraMap Γ(S, (⊤ : S.Opens)) Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) r =
        (Scheme.Hom.appTop (U.1.ι ≫ π)).hom r)
    (b2 : Module.Basis (Fin 2) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π L))
    (e1 : Scheme.Modules.baseSections π (Limits.cokernel
        (divisorTwistHom (ModularCurves.RelEffCartierDiv.sectionsDivisor
          π ![R]).ideal L))
      ≃ₗ[Γ(S, (⊤ : S.Opens))] Γ(S, (⊤ : S.Opens)))
    (huni : Ideal.span (Set.range (fun j => e1
      ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π
        (divisorTwistHom (ModularCurves.RelEffCartierDiv.sectionsDivisor
          π ![R]).ideal L))) (b2 j)))) = ⊤) :
    ∃ v : Scheme.Modules.baseSections π L,
      LinearMap.ker ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π
        (divisorTwistHom (ModularCurves.RelEffCartierDiv.sectionsDivisor
          π ![R]).ideal L))).hom) =
      Submodule.span Γ(S, (⊤ : S.Opens)) {v} :=
  exists_ker_baseSectionsMap_cokernel_eq_span_perp_of_section hsm R U hRU rR hR hnzdR
    L hL eL halg
    (surjective_baseSectionsMap_cokernel_of_unimodular_row _ b2 e1 huni) b2

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 E2] The triple twist's multiplier is a unit multiple of the generator
product.** Upgrading `span_iteratedChartMultiplier₃_eq` from spans to elements, using
that the multiplier is a nonzerodivisor (which monomorphy of the restricted twist
provides). -/
theorem exists_unit_chartMultiplier₃_eq (J₁ J₂ J₃ : C.IdealSheafData) (L : C.Modules)
    (U : C.affineOpens) (g₁ g₂ g₃ : Γ(C, U.1))
    (hspan₁ : J₁.ideal U = Ideal.span {g₁})
    (hnzd₁ : g₁ ∈ nonZeroDivisors Γ(C, U.1))
    (hspan₂ : J₂.ideal U = Ideal.span {g₂})
    (hnzd₂ : g₂ ∈ nonZeroDivisors Γ(C, U.1))
    (hspan₃ : J₃.ideal U = Ideal.span {g₃})
    (hnzd₃ : g₃ ∈ nonZeroDivisors Γ(C, U.1))
    (eI₁ : (restrictFunctor U.1.ι).obj (idealModule J₁) ≅ unitObj U.1.toScheme)
    (eI₂ : (restrictFunctor U.1.ι).obj (idealModule J₂) ≅ unitObj U.1.toScheme)
    (eI₃ : (restrictFunctor U.1.ι).obj (idealModule J₃) ≅ unitObj U.1.toScheme)
    (eL : (restrictFunctor U.1.ι).obj L ≅ unitObj U.1.toScheme)
    [Mono ((restrictFunctor U.1.ι).map (iteratedTwistHom₃ J₁ J₂ J₃ L))] :
    ∃ u : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))ˣ,
      chartMultiplier U.1 (iteratedTwistHom₃ J₁ J₂ J₃ L)
          (iteratedChartTriv₃ J₁ J₂ J₃ L U.1 eI₁ eI₂ eI₃ eL) eL =
        (u : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))) *
          ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g₁ *
            ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g₂ *
              (U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g₃)) := by
  haveI : IsAffine U.1.toScheme := U.2
  haveI hMonoEndo : Mono (ModularCurves.unitEndomorphismOfTopSection
      (chartMultiplier U.1 (iteratedTwistHom₃ J₁ J₂ J₃ L)
        (iteratedChartTriv₃ J₁ J₂ J₃ L U.1 eI₁ eI₂ eI₃ eL) eL)) :=
    mono_unitEndo_chartMultiplier U.1 _ _ eL
  have hnzd := mem_nonZeroDivisors_of_mono_unitEndo
    (chartMultiplier U.1 (iteratedTwistHom₃ J₁ J₂ J₃ L)
      (iteratedChartTriv₃ J₁ J₂ J₃ L U.1 eI₁ eI₂ eI₃ eL) eL)
  refine ModularCurves.exists_unit_mul_of_span_eq _ _ ?_ ?_
  · exact span_iteratedChartMultiplier₃_eq J₁ J₂ J₃ L U g₁ g₂ g₃
      hspan₁ hnzd₁ hspan₂ hnzd₂ hspan₃ hnzd₃ eI₁ eI₂ eI₃ eL
  · intro t ht
    exact (mem_nonZeroDivisors_iff.mp hnzd).1 t ht

end IteratedTwist

end AlgebraicGeometry.Scheme.Modules

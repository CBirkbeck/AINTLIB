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

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory

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

end IteratedTwist

end AlgebraicGeometry.Scheme.Modules

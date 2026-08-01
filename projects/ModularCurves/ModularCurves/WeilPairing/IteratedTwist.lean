/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.LineVertical

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

end GeneralMultiplier

end AlgebraicGeometry.Scheme.Modules

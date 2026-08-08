/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.DualPullback
import ModularCurves.Picard.DualPullback.LocalTrivializationSection
import ModularCurves.Picard.InvertibleSheafCocycle
import ModularCurves.WeilPairing.TensorSection
import ModularCurves.WeilPairing.UnitSheaf
import ModularCurves.Picard.InvertibleSheafBaseCechFlat

/-!
# Zariski locality of the relative Picard equivalence (`AP2-B1`, KM p. 65)

Katz–Mazur, *Arithmetic Moduli of Elliptic Curves*, p. 65, verbatim: *"if we are given `ℒ` and `ℒ'`
on `E`, an affine open covering `{U_i}` of `S`, invertible sheaves `ℒ_{0,i}` on `U_i`, and
isomorphisms `φ_i : ℒ ≅ ℒ' ⊗ f^*(ℒ_{0,i})` on `f⁻¹(U_i)`, then there exists an `ℒ₀` on `S` and an
isomorphism `φ : ℒ ≅ ℒ' ⊗ f^*(ℒ₀)`."* — the sheaf condition for `Pic_{E_T/T} = Pic(E_T)/f_T^*Pic(T)`,
in its consumable form. KM's proof (p. 65): *"Because `E/S` is proper and smooth with geometrically
connected fibers, we have `f_*(𝒪_E) = 𝒪_S`, whence `f_*f^*(ℒ_{0,i}) = ℒ_{0,i}` on `U_i`. Therefore
the existence of the isomorphism `φ_i` shows that both `f_*(ℒ⁻¹ ⊗ ℒ')`, `f_*(ℒ ⊗ (ℒ')⁻¹)` are
invertible sheaves on `𝒪_S`, inverse to each other. If we call the second one `ℒ₀`, and write
`ℒ'' = ℒ' ⊗ f^*(ℒ₀)`, we find canonical isomorphisms `f_*(ℒ⁻¹ ⊗ ℒ'') = 𝒪_S = f_*(ℒ ⊗ (ℒ'')⁻¹)`,
under which the unit section `1 ∈ Γ(S, 𝒪_S)` is the required isomorphism `ℒ ≅ ℒ''`."*

Hida's corresponding locality claim (p. 109, *"Since the formation of invertible sheaf is local,
`Pic_{E/S}` is local"*) is a non-sequitur — isomorphism *classes* are not a Zariski sheaf — and the
`f_*𝒪 = 𝒪` input above is exactly what repairs it (`decomposition-gme2.md`, CORRECTIONS item 3).
Round-19 architecture step `[B′]`; consumed by `AP2-B4`'s naturality and by `AP-D5`'s cocycle
refinement independence.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

/-- **(AP2-B1, KM p. 65)** The `f^*`-twist equivalence on invertible sheaves is Zariski-local on the
base: isomorphisms `M ≅ M' ⊗ f^*(N i)` over the preimages of an open cover of `T` glue to a global
`M ≅ M' ⊗ f^*N₀` — the sheaf condition for `Pic(E_T)/f_T^*Pic(T)`.

Skeleton (`:= by sorry`); proof recipe is KM p. 65's, quoted in the module docstring, with the glue
supplied by `UniversallyOConnected` and the tree's pushforward machinery. -/
theorem exists_pullback_twist_of_locally {X S : Scheme.{u}} {p : X ⟶ S} {T : Scheme.{u}}
    (g : T ⟶ S) (hp : UniversallyOConnected p)
    {M M' : (pullback p g).Modules} (hM : IsInvertible M) (hM' : IsInvertible M')
    {ι : Type u} (U : ι → T.Opens) (hU : IsOpenCover U)
    (N : ∀ i, (U i).toScheme.Modules) (hN : ∀ i, IsInvertible (N i))
    (hglue : ∀ i, Nonempty
      (M.restrict (pullback.snd p g ⁻¹ᵁ U i).ι ≅
        tensorObj (M'.restrict (pullback.snd p g ⁻¹ᵁ U i).ι)
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (pullback.snd p g ∣_ U i)).obj (N i)))) :
    ∃ N₀ : T.Modules, IsInvertible N₀ ∧
      Nonempty (M ≅ tensorObj M'
        ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj N₀)) := by
  -- KM p. 65 assembly, decomposed (2026-08-08; sub-leaves below this theorem):
  -- N₀ := f_*(M ⊗ (M')^∨); locally N₀|Uᵢ ≅ f_*f^*(Nᵢ) ≅ Nᵢ (P-restrict + P-local +
  -- nonempty_pushforwardPullback_iso on the restricted family), hence invertible;
  -- the twist iso by the counit-cancellation (P-counit).
  sorry


/-- The pushforward-slot generating section of the glue: over a trivialising open `V` of `N`, the
canonical section of `f_*f^*N` obtained from a trivialisation `e` through the pullback dictionaries
(`sheafOfModulesEquivOverUnit`, `pullbackUnitIso`, `localPullbackModuleIso`), read via `unitHomEquiv`
at the top of the over-site. -/
noncomputable def glueSectionA {X S : Scheme.{u}} {p : X ⟶ S} {T : Scheme.{u}} (g : T ⟶ S)
    (N : T.Modules) (V : T.Opens)
    (e : (AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj N ≅ unitObj V.toScheme) :
    ↑Γ((AlgebraicGeometry.Scheme.Modules.pushforward (pullback.snd p g)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj N), V) :=
  ((((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj N).over
      (pullback.snd p g ⁻¹ᵁ V)).unitHomEquiv
    ((AlgebraicGeometry.Scheme.Modules.overEquiv
        (pullback.snd p g ⁻¹ᵁ V)).functor.preimage
      (((pullback.snd p g ⁻¹ᵁ V).sheafOfModulesEquivOverUnit
          (pullback p g).ringCatSheaf).hom ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
          (pullback.snd p g ∣_ V)).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback
          (pullback.snd p g ∣_ V)).map e.inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback
          (pullback.snd p g ∣_ V)).map
          (((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv V).app N ≪≫
            (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback V.ι).app N).inv) ≫
        (AlgebraicGeometry.Scheme.Modules.localPullbackModuleIso
          (pullback.snd p g) N V).hom))).val
    (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ V))))

/-- The over-site form of a pullback trivialisation: `N.over V ≅ unit`, through the
`overEquiv`/`restrictFunctorIsoPullback`/`sheafOfModulesEquivOverUnit` dictionaries. This is the form
`trivializationTransitionUnit` (`Picard/InvertibleSheafCocycle.lean:44`) consumes. -/
noncomputable def overTrivialization {T : Scheme.{u}} (N : T.Modules) (V : T.Opens)
    (e : (AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj N ≅ unitObj V.toScheme) :
    N.over V ≅ _root_.SheafOfModules.unit (T.ringCatSheaf.over V) :=
  (AlgebraicGeometry.Scheme.Modules.overEquiv V).functor.preimageIso
    ((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv V).app N ≪≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback V.ι).app N ≪≫
      e ≪≫ (V.sheafOfModulesEquivOverUnit T.ringCatSheaf).symm)

/-- The base-side generating element of `glueSectionA`: the value of the inverse over-site
trivialisation on `1`, a section of `N` over `V`. `glueSectionA` is the image of this seed
under the pullback–pushforward adjunction unit (`glueSectionA_eq_adjUnit`), which makes its
overlap behaviour a base-side computation. -/
noncomputable def glueSectionASeed {T : Scheme.{u}} (N : T.Modules) (V : T.Opens)
    (e : (AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj N ≅ unitObj V.toScheme) :
    N.val.obj (Opposite.op V) :=
  (overTrivialization N V e).inv.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 V)))
    (show (T.ringCatSheaf.over V).obj.obj
      (Opposite.op (CategoryTheory.Over.mk (𝟙 V))) from 1)

set_option backward.isDefEq.respectTransparency false in
/-- **`glueSectionA` in adjunction-unit form.** The pushforward-slot section is the image of
the base-side seed under the pullback–pushforward adjunction unit: `glueSectionA`'s chain is
the inverse of the canonical pulled trivialisation of
`ModularCurves.Picard.DualPullback.LocalTrivializationSection`, evaluated on `1`. -/
theorem glueSectionA_eq_adjUnit {X S : Scheme.{u}} {p : X ⟶ S} {T : Scheme.{u}} (g : T ⟶ S)
    (N : T.Modules) (V : T.Opens)
    (e : (AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj N ≅ unitObj V.toScheme) :
    glueSectionA (p := p) g N V e =
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
          (pullback.snd p g)).unit.app N).val.app (Opposite.op V)
        (glueSectionASeed N V e) := by
  have hx : (overTrivialization N V e).hom.val.app
      (Opposite.op (CategoryTheory.Over.mk (𝟙 V)))
      (glueSectionASeed N V e) =
      (show (T.ringCatSheaf.over V).obj.obj
        (Opposite.op (CategoryTheory.Over.mk (𝟙 V))) from 1) := by
    have hcomp := congrArg
      (fun q ↦ q.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 V))))
      (overTrivialization N V e).inv_hom_id
    have h := CategoryTheory.ConcreteCategory.congr_hom hcomp
      (show (T.ringCatSheaf.over V).obj.obj
        (Opposite.op (CategoryTheory.Over.mk (𝟙 V))) from 1)
    erw [AlgebraicGeometry.Scheme.Modules.sheafOfModules_comp_app_apply] at h
    exact h
  have hp : (AlgebraicGeometry.Scheme.Modules.overEquiv
      (pullback.snd p g ⁻¹ᵁ V)).functor.map
      (AlgebraicGeometry.Scheme.Modules.localPullbackTrivializationT
        (pullback.snd p g) N V (overTrivialization N V e)).hom =
      (AlgebraicGeometry.Scheme.Modules.localPullbackModuleIso (pullback.snd p g) N V).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g ∣_ V)).map
          ((AlgebraicGeometry.Scheme.Modules.overEquiv V).functor.map
            (overTrivialization N V e).hom) ≫
        (AlgebraicGeometry.Scheme.Modules.localPullbackUnitIso (pullback.snd p g) V).hom := by
    dsimp only [AlgebraicGeometry.Scheme.Modules.localPullbackTrivializationT]
    simp only [Functor.FullyFaithful.preimageIso_hom,
      Functor.FullyFaithful.map_preimage, Iso.trans_hom, Functor.mapIso_hom]
    rfl
  have hone := AlgebraicGeometry.Scheme.Modules.localPullbackTrivialization_inv_one_ofSection
    (pullback.snd p g) N V (overTrivialization N V e) (glueSectionASeed N V e)
    (AlgebraicGeometry.Scheme.Modules.localPullbackTrivializationT
      (pullback.snd p g) N V (overTrivialization N V e)) hx hp
  have hψ : (AlgebraicGeometry.Scheme.Modules.overEquiv
      (pullback.snd p g ⁻¹ᵁ V)).functor.preimage
      ((((pullback.snd p g ⁻¹ᵁ V).sheafOfModulesEquivOverUnit
          (pullback p g).ringCatSheaf).hom ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
          (pullback.snd p g ∣_ V)).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback
          (pullback.snd p g ∣_ V)).map e.inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback
          (pullback.snd p g ∣_ V)).map
          (((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv V).app N ≪≫
            (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback V.ι).app N).inv) ≫
        (AlgebraicGeometry.Scheme.Modules.localPullbackModuleIso
          (pullback.snd p g) N V).hom)) =
      (AlgebraicGeometry.Scheme.Modules.localPullbackTrivializationT
        (pullback.snd p g) N V (overTrivialization N V e)).inv := by
    apply (AlgebraicGeometry.Scheme.Modules.overEquiv
      (pullback.snd p g ⁻¹ᵁ V)).functor.map_injective
    rw [Functor.map_preimage]
    dsimp only [AlgebraicGeometry.Scheme.Modules.localPullbackTrivializationT]
    simp only [Functor.FullyFaithful.preimageIso_inv, Functor.FullyFaithful.map_preimage,
      Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Functor.mapIso_hom,
      AlgebraicGeometry.Scheme.Modules.localPullbackUnitIso, overTrivialization,
      Functor.preimageIso_inv, Functor.map_preimage, Functor.map_comp, Category.assoc]
    conv_rhs => rw [← Functor.map_comp_assoc]
    rw [Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact (congrArg (fun q ↦ q.val.app
      (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ V))))
      (show ((pullback p g).ringCatSheaf.over (pullback.snd p g ⁻¹ᵁ V)).obj.obj
        (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ V)))) from 1)) hψ).trans
    hone

/-- The transition unit of two pullback trivialisations on the overlap: pass each to over-form
(`overTrivialization`), restrict **at the over level** with `restrictOverTrivialization`
(`Picard/Dual.lean:792`), and take `trivializationTransitionUnit`. Restricting at the over level —
rather than with the pullback-level `restrictTrivialization` — makes the comparison lemmas below
consume the transition-unit API (`overUnitScalarEnd_transitionUnit`,
`restrictOverTrivialization_hom_eq_comp_scalar`) directly, with no route-coherence lemma. -/
noncomputable def glueTransitionUnit {T : Scheme.{u}} (N : T.Modules) {Vi Vj : T.Opens}
    (ei : (AlgebraicGeometry.Scheme.Modules.pullback Vi.ι).obj N ≅ unitObj Vi.toScheme)
    (ej : (AlgebraicGeometry.Scheme.Modules.pullback Vj.ι).obj N ≅ unitObj Vj.toScheme) :
    ↑Γ(T, Vi ⊓ Vj)ˣ :=
  AlgebraicGeometry.Scheme.Modules.trivializationTransitionUnit (Vi ⊓ Vj)
    (ModularCurves.SheafOfModules.restrictOverTrivialization T.ringCatSheaf N Vj
      (overTrivialization N Vj ej)
      (CategoryTheory.Over.mk (homOfLE (inf_le_right : Vi ⊓ Vj ≤ Vj))))
    (ModularCurves.SheafOfModules.restrictOverTrivialization T.ringCatSheaf N Vi
      (overTrivialization N Vi ei)
      (CategoryTheory.Over.mk (homOfLE (inf_le_left : Vi ⊓ Vj ≤ Vi))))

/-- The dual-slot generating section of the glue: the functional on `N` over `V` induced by a
trivialisation `e`, as a section of `dualObj N` (whose sections over `V` are definitionally the
Hom-type `N.over V ⟶ unit`). -/
noncomputable def glueSectionB {T : Scheme.{u}} (N : T.Modules) (V : T.Opens)
    (e : (AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj N ≅ unitObj V.toScheme) :
    ↑Γ(AlgebraicGeometry.Scheme.Modules.dualObj N, V) :=
  (fun (φ : N.over V ⟶ _root_.SheafOfModules.unit (T.ringCatSheaf.over V)) => φ)
    (overTrivialization N V e).hom


/-- **(AP2-B1a, seed comparison)** On the overlap the two base-side seeds differ by the
inverse transition unit: the restricted inverse over-trivialisations satisfy
`rOTᵢ.inv = E(u⁻¹) ≫ rOTⱼ.inv` by `overUnitScalarEnd_transitionUnit` and multiplicativity of
the scalar-endomorphism ring hom, and evaluating at `1` on the top of the overlap's over-site
turns the scalar endomorphism into the module smul. -/
theorem glueSectionASeed_compat {T : Scheme.{u}} (N : T.Modules) {Vi Vj : T.Opens}
    (ei : (AlgebraicGeometry.Scheme.Modules.pullback Vi.ι).obj N ≅ unitObj Vi.toScheme)
    (ej : (AlgebraicGeometry.Scheme.Modules.pullback Vj.ι).obj N ≅ unitObj Vj.toScheme) :
    N.presheaf.map (homOfLE (inf_le_left : Vi ⊓ Vj ≤ Vi)).op (glueSectionASeed N Vi ei) =
      (((glueTransitionUnit N ei ej)⁻¹ : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj)) •
        N.presheaf.map (homOfLE (inf_le_right : Vi ⊓ Vj ≤ Vj)).op
          (glueSectionASeed N Vj ej) := by
  let rOTi : N.over (Vi ⊓ Vj) ≅
      _root_.SheafOfModules.unit (T.ringCatSheaf.over (Vi ⊓ Vj)) :=
    ModularCurves.SheafOfModules.restrictOverTrivialization T.ringCatSheaf N Vi
      (overTrivialization N Vi ei)
      (CategoryTheory.Over.mk (homOfLE (inf_le_left : Vi ⊓ Vj ≤ Vi)))
  let rOTj : N.over (Vi ⊓ Vj) ≅
      _root_.SheafOfModules.unit (T.ringCatSheaf.over (Vi ⊓ Vj)) :=
    ModularCurves.SheafOfModules.restrictOverTrivialization T.ringCatSheaf N Vj
      (overTrivialization N Vj ej)
      (CategoryTheory.Over.mk (homOfLE (inf_le_right : Vi ⊓ Vj ≤ Vj)))
  have hseedL : N.presheaf.map (homOfLE (inf_le_left : Vi ⊓ Vj ≤ Vi)).op
      (glueSectionASeed N Vi ei) =
      rOTi.inv.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 (Vi ⊓ Vj))))
        (show (T.ringCatSheaf.over (Vi ⊓ Vj)).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 (Vi ⊓ Vj)))) from 1) := by
    have hnat := PresheafOfModules.naturality_apply (overTrivialization N Vi ei).inv.val
      (CategoryTheory.Over.mkIdTerminal.from
        (CategoryTheory.Over.mk (homOfLE (inf_le_left : Vi ⊓ Vj ≤ Vi)))).op
      (show (T.ringCatSheaf.over Vi).obj.obj
        (Opposite.op (CategoryTheory.Over.mk (𝟙 Vi))) from 1)
    have h1 : (_root_.SheafOfModules.unit (T.ringCatSheaf.over Vi)).val.map
        (CategoryTheory.Over.mkIdTerminal.from
          (CategoryTheory.Over.mk (homOfLE (inf_le_left : Vi ⊓ Vj ≤ Vi)))).op
        (show (T.ringCatSheaf.over Vi).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 Vi))) from 1) =
        (show (T.ringCatSheaf.over Vi).obj.obj
          (Opposite.op (CategoryTheory.Over.mk
            (homOfLE (inf_le_left : Vi ⊓ Vj ≤ Vi)))) from 1) :=
      PresheafOfModules.unit_map_one (T.ringCatSheaf.over Vi).obj
        (CategoryTheory.Over.mkIdTerminal.from
          (CategoryTheory.Over.mk (homOfLE (inf_le_left : Vi ⊓ Vj ≤ Vi)))).op
    rw [h1] at hnat
    exact hnat.symm
  have hseedR : N.presheaf.map (homOfLE (inf_le_right : Vi ⊓ Vj ≤ Vj)).op
      (glueSectionASeed N Vj ej) =
      rOTj.inv.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 (Vi ⊓ Vj))))
        (show (T.ringCatSheaf.over (Vi ⊓ Vj)).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 (Vi ⊓ Vj)))) from 1) := by
    have hnat := PresheafOfModules.naturality_apply (overTrivialization N Vj ej).inv.val
      (CategoryTheory.Over.mkIdTerminal.from
        (CategoryTheory.Over.mk (homOfLE (inf_le_right : Vi ⊓ Vj ≤ Vj)))).op
      (show (T.ringCatSheaf.over Vj).obj.obj
        (Opposite.op (CategoryTheory.Over.mk (𝟙 Vj))) from 1)
    have h1 : (_root_.SheafOfModules.unit (T.ringCatSheaf.over Vj)).val.map
        (CategoryTheory.Over.mkIdTerminal.from
          (CategoryTheory.Over.mk (homOfLE (inf_le_right : Vi ⊓ Vj ≤ Vj)))).op
        (show (T.ringCatSheaf.over Vj).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 Vj))) from 1) =
        (show (T.ringCatSheaf.over Vj).obj.obj
          (Opposite.op (CategoryTheory.Over.mk
            (homOfLE (inf_le_right : Vi ⊓ Vj ≤ Vj)))) from 1) :=
      PresheafOfModules.unit_map_one (T.ringCatSheaf.over Vj).obj
        (CategoryTheory.Over.mkIdTerminal.from
          (CategoryTheory.Over.mk (homOfLE (inf_le_right : Vi ⊓ Vj ≤ Vj)))).op
    rw [h1] at hnat
    exact hnat.symm
  rw [hseedL, hseedR]
  have hE : ModularCurves.SheafOfModules.overUnitScalarEnd T.ringCatSheaf (Vi ⊓ Vj)
      ((glueTransitionUnit N ei ej : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj)) =
      rOTj.inv ≫ rOTi.hom :=
    AlgebraicGeometry.Scheme.Modules.overUnitScalarEnd_transitionUnit (Vi ⊓ Vj) rOTj rOTi
  have hcancel : ModularCurves.SheafOfModules.overUnitScalarEnd T.ringCatSheaf (Vi ⊓ Vj)
      (((glueTransitionUnit N ei ej)⁻¹ : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj)) ≫
      ModularCurves.SheafOfModules.overUnitScalarEnd T.ringCatSheaf (Vi ⊓ Vj)
        ((glueTransitionUnit N ei ej : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj)) =
      𝟙 (_root_.SheafOfModules.unit (T.ringCatSheaf.over (Vi ⊓ Vj))) := by
    have h1 : (ModularCurves.SheafOfModules.overUnitScalarEndRingHom
        T.ringCatSheaf (Vi ⊓ Vj))
        (((glueTransitionUnit N ei ej : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj)) *
          (((glueTransitionUnit N ei ej)⁻¹ : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj))) =
        𝟙 (_root_.SheafOfModules.unit (T.ringCatSheaf.over (Vi ⊓ Vj))) := by
      rw [Units.mul_inv]
      exact map_one _
    have h2 := map_mul (ModularCurves.SheafOfModules.overUnitScalarEndRingHom
        T.ringCatSheaf (Vi ⊓ Vj))
      ((glueTransitionUnit N ei ej : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj))
      (((glueTransitionUnit N ei ej)⁻¹ : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj))
    exact (h2.symm.trans h1 : _)
  have hinv : rOTi.inv =
      ModularCurves.SheafOfModules.overUnitScalarEnd T.ringCatSheaf (Vi ⊓ Vj)
        (((glueTransitionUnit N ei ej)⁻¹ : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj)) ≫
        rOTj.inv := by
    calc rOTi.inv
        = 𝟙 (_root_.SheafOfModules.unit (T.ringCatSheaf.over (Vi ⊓ Vj))) ≫ rOTi.inv :=
          (Category.id_comp _).symm
      _ = (ModularCurves.SheafOfModules.overUnitScalarEnd T.ringCatSheaf (Vi ⊓ Vj)
            (((glueTransitionUnit N ei ej)⁻¹ : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj)) ≫
          ModularCurves.SheafOfModules.overUnitScalarEnd T.ringCatSheaf (Vi ⊓ Vj)
            ((glueTransitionUnit N ei ej : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj))) ≫
          rOTi.inv := by rw [hcancel]
      _ = ModularCurves.SheafOfModules.overUnitScalarEnd T.ringCatSheaf (Vi ⊓ Vj)
            (((glueTransitionUnit N ei ej)⁻¹ : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj)) ≫
          ModularCurves.SheafOfModules.overUnitScalarEnd T.ringCatSheaf (Vi ⊓ Vj)
            ((glueTransitionUnit N ei ej : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj)) ≫
          rOTi.inv := by rw [Category.assoc]
      _ = ModularCurves.SheafOfModules.overUnitScalarEnd T.ringCatSheaf (Vi ⊓ Vj)
            (((glueTransitionUnit N ei ej)⁻¹ : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj)) ≫
          (rOTj.inv ≫ rOTi.hom) ≫ rOTi.inv := by rw [hE]
      _ = ModularCurves.SheafOfModules.overUnitScalarEnd T.ringCatSheaf (Vi ⊓ Vj)
            (((glueTransitionUnit N ei ej)⁻¹ : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj)) ≫
          rOTj.inv := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have happ := CategoryTheory.ConcreteCategory.congr_hom
    (congrArg (fun q : _root_.SheafOfModules.unit (T.ringCatSheaf.over (Vi ⊓ Vj)) ⟶
        N.over (Vi ⊓ Vj) ↦
      q.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 (Vi ⊓ Vj))))) hinv)
    (show (T.ringCatSheaf.over (Vi ⊓ Vj)).obj.obj
      (Opposite.op (CategoryTheory.Over.mk (𝟙 (Vi ⊓ Vj)))) from 1)
  have hsplit : (ModularCurves.SheafOfModules.overUnitScalarEnd T.ringCatSheaf (Vi ⊓ Vj)
      (((glueTransitionUnit N ei ej)⁻¹ : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj)) ≫
        rOTj.inv).val.app
      (Opposite.op (CategoryTheory.Over.mk (𝟙 (Vi ⊓ Vj))))
      (show (T.ringCatSheaf.over (Vi ⊓ Vj)).obj.obj
        (Opposite.op (CategoryTheory.Over.mk (𝟙 (Vi ⊓ Vj)))) from 1) =
      rOTj.inv.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 (Vi ⊓ Vj))))
        ((ModularCurves.SheafOfModules.overUnitScalarEnd T.ringCatSheaf (Vi ⊓ Vj)
          (((glueTransitionUnit N ei ej)⁻¹ : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj))).val.app
          (Opposite.op (CategoryTheory.Over.mk (𝟙 (Vi ⊓ Vj))))
          (show (T.ringCatSheaf.over (Vi ⊓ Vj)).obj.obj
            (Opposite.op (CategoryTheory.Over.mk (𝟙 (Vi ⊓ Vj)))) from 1)) := rfl
  refine (happ.trans hsplit).trans ?_
  have hEapp : (ModularCurves.SheafOfModules.overUnitScalarEnd T.ringCatSheaf (Vi ⊓ Vj)
      (((glueTransitionUnit N ei ej)⁻¹ : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj))).val.app
      (Opposite.op (CategoryTheory.Over.mk (𝟙 (Vi ⊓ Vj))))
      (show (T.ringCatSheaf.over (Vi ⊓ Vj)).obj.obj
        (Opposite.op (CategoryTheory.Over.mk (𝟙 (Vi ⊓ Vj)))) from 1) =
      (show (T.ringCatSheaf.over (Vi ⊓ Vj)).obj.obj
        (Opposite.op (CategoryTheory.Over.mk (𝟙 (Vi ⊓ Vj)))) from
        (((glueTransitionUnit N ei ej)⁻¹ : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj))) := by
    have h0 : (ModularCurves.SheafOfModules.overUnitScalarEnd T.ringCatSheaf (Vi ⊓ Vj)
        (((glueTransitionUnit N ei ej)⁻¹ : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj))).val.app
        (Opposite.op (CategoryTheory.Over.mk (𝟙 (Vi ⊓ Vj))))
        (show (T.ringCatSheaf.over (Vi ⊓ Vj)).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 (Vi ⊓ Vj)))) from 1) =
        (show (T.ringCatSheaf.over (Vi ⊓ Vj)).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 (Vi ⊓ Vj)))) from 1) *
        (show (T.ringCatSheaf.over (Vi ⊓ Vj)).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 (Vi ⊓ Vj)))) from
          T.ringCatSheaf.obj.map (𝟙 (Vi ⊓ Vj)).op
            (((glueTransitionUnit N ei ej)⁻¹ : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj))) := rfl
    rw [h0, one_mul]
    show T.ringCatSheaf.obj.map (𝟙 (Vi ⊓ Vj)).op
        (((glueTransitionUnit N ei ej)⁻¹ : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj)) = _
    rw [CategoryTheory.op_id, CategoryTheory.Functor.map_id]
    rfl
  rw [hEapp]
  have hsm : (show (T.ringCatSheaf.over (Vi ⊓ Vj)).obj.obj
      (Opposite.op (CategoryTheory.Over.mk (𝟙 (Vi ⊓ Vj)))) from
      (((glueTransitionUnit N ei ej)⁻¹ : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj))) =
      (show (T.ringCatSheaf.over (Vi ⊓ Vj)).obj.obj
        (Opposite.op (CategoryTheory.Over.mk (𝟙 (Vi ⊓ Vj)))) from
        (((glueTransitionUnit N ei ej)⁻¹ : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj))) •
      (show (T.ringCatSheaf.over (Vi ⊓ Vj)).obj.obj
        (Opposite.op (CategoryTheory.Over.mk (𝟙 (Vi ⊓ Vj)))) from 1) := by
    rw [smul_eq_mul, mul_one]
  rw [hsm]
  exact map_smul (CategoryTheory.ConcreteCategory.hom
    (rOTj.inv.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 (Vi ⊓ Vj)))))) _ _

/-- **(AP2-B1a, comparison A — the pushforward slot picks up the INVERSE transition unit,
since `glueSectionA`'s chain uses `e.inv`.)** On the overlap the
two `glueSectionA`s differ by `glueTransitionUnit`. Cocycle content of KM p. 65's glue. -/
theorem glueSectionA_compat {X S : Scheme.{u}} {p : X ⟶ S} {T : Scheme.{u}} (g : T ⟶ S)
    (N : T.Modules) {Vi Vj : T.Opens}
    (ei : (AlgebraicGeometry.Scheme.Modules.pullback Vi.ι).obj N ≅ unitObj Vi.toScheme)
    (ej : (AlgebraicGeometry.Scheme.Modules.pullback Vj.ι).obj N ≅ unitObj Vj.toScheme) :
    ((AlgebraicGeometry.Scheme.Modules.pushforward (pullback.snd p g)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj N)).presheaf.map
        (homOfLE (inf_le_left : Vi ⊓ Vj ≤ Vi)).op (glueSectionA g N Vi ei) =
      (((glueTransitionUnit N ei ej)⁻¹ : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj)) •
        ((AlgebraicGeometry.Scheme.Modules.pushforward (pullback.snd p g)).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj N)).presheaf.map
          (homOfLE (inf_le_right : Vi ⊓ Vj ≤ Vj)).op (glueSectionA g N Vj ej) := by
  rw [glueSectionA_eq_adjUnit g N Vi ei, glueSectionA_eq_adjUnit g N Vj ej]
  set φ : N ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward (pullback.snd p g)).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj N) :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
      (pullback.snd p g)).unit.app N with hφ
  have hnatL := PresheafOfModules.naturality_apply φ.val
    (homOfLE (inf_le_left : Vi ⊓ Vj ≤ Vi)).op (glueSectionASeed N Vi ei)
  have hnatR := PresheafOfModules.naturality_apply φ.val
    (homOfLE (inf_le_right : Vi ⊓ Vj ≤ Vj)).op (glueSectionASeed N Vj ej)
  have happL : AlgebraicGeometry.Scheme.Modules.Hom.app φ (Vi ⊓ Vj)
      (N.presheaf.map (homOfLE (inf_le_left : Vi ⊓ Vj ≤ Vi)).op
        (glueSectionASeed N Vi ei)) =
      (((glueTransitionUnit N ei ej)⁻¹ : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj)) •
      AlgebraicGeometry.Scheme.Modules.Hom.app φ (Vi ⊓ Vj)
        (N.presheaf.map (homOfLE (inf_le_right : Vi ⊓ Vj ≤ Vj)).op
          (glueSectionASeed N Vj ej)) := by
    rw [glueSectionASeed_compat N ei ej]
    exact AlgebraicGeometry.Scheme.Modules.Hom.app_smul φ _ _
  exact hnatL.symm.trans (happL.trans (congrArg
    (fun z : ↑Γ((AlgebraicGeometry.Scheme.Modules.pushforward (pullback.snd p g)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj N), Vi ⊓ Vj) ↦
      (((glueTransitionUnit N ei ej)⁻¹ : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj)) • z)
    hnatR))

/-- **(AP2-B1a, comparison B — the dual slot picks up the transition unit: `u • φ = φ ≫ E(u)` and
`E(u) = e_jV.inv ≫ e_iV.hom` by `overUnitScalarEnd_transitionUnit`.)** -/
theorem glueSectionB_compat {T : Scheme.{u}} (N : T.Modules) {Vi Vj : T.Opens}
    (ei : (AlgebraicGeometry.Scheme.Modules.pullback Vi.ι).obj N ≅ unitObj Vi.toScheme)
    (ej : (AlgebraicGeometry.Scheme.Modules.pullback Vj.ι).obj N ≅ unitObj Vj.toScheme) :
    (AlgebraicGeometry.Scheme.Modules.dualObj N).presheaf.map
        (homOfLE (inf_le_left : Vi ⊓ Vj ≤ Vi)).op (glueSectionB N Vi ei) =
      (glueTransitionUnit N ei ej : ↑Γ(T, Vi ⊓ Vj)) •
        (AlgebraicGeometry.Scheme.Modules.dualObj N).presheaf.map
          (homOfLE (inf_le_right : Vi ⊓ Vj ≤ Vj)).op (glueSectionB N Vj ej) := by
  have hstep1R : (AlgebraicGeometry.Scheme.Modules.dualObj N).presheaf.map
      (homOfLE (inf_le_right : Vi ⊓ Vj ≤ Vj)).op (glueSectionB N Vj ej) =
    (fun (φ : N.over (Vi ⊓ Vj) ⟶
        _root_.SheafOfModules.unit (T.ringCatSheaf.over (Vi ⊓ Vj))) => φ)
      (ModularCurves.SheafOfModules.restrictOverTrivialization T.ringCatSheaf N Vj
        (overTrivialization N Vj ej)
        (CategoryTheory.Over.mk (homOfLE (inf_le_right : Vi ⊓ Vj ≤ Vj)))).hom := rfl
  have hstep1L : (AlgebraicGeometry.Scheme.Modules.dualObj N).presheaf.map
      (homOfLE (inf_le_left : Vi ⊓ Vj ≤ Vi)).op (glueSectionB N Vi ei) =
    (fun (φ : N.over (Vi ⊓ Vj) ⟶
        _root_.SheafOfModules.unit (T.ringCatSheaf.over (Vi ⊓ Vj))) => φ)
      (ModularCurves.SheafOfModules.restrictOverTrivialization T.ringCatSheaf N Vi
        (overTrivialization N Vi ei)
        (CategoryTheory.Over.mk (homOfLE (inf_le_left : Vi ⊓ Vj ≤ Vi)))).hom := rfl
  rw [hstep1L, hstep1R]
  have hE := AlgebraicGeometry.Scheme.Modules.overUnitScalarEnd_transitionUnit (Vi ⊓ Vj)
    (ModularCurves.SheafOfModules.restrictOverTrivialization T.ringCatSheaf N Vj
      (overTrivialization N Vj ej)
      (CategoryTheory.Over.mk (homOfLE (inf_le_right : Vi ⊓ Vj ≤ Vj))))
    (ModularCurves.SheafOfModules.restrictOverTrivialization T.ringCatSheaf N Vi
      (overTrivialization N Vi ei)
      (CategoryTheory.Over.mk (homOfLE (inf_le_left : Vi ⊓ Vj ≤ Vi))))
  show (ModularCurves.SheafOfModules.restrictOverTrivialization T.ringCatSheaf N Vi
      (overTrivialization N Vi ei)
      (CategoryTheory.Over.mk (homOfLE (inf_le_left : Vi ⊓ Vj ≤ Vi)))).hom =
    (ModularCurves.SheafOfModules.restrictOverTrivialization T.ringCatSheaf N Vj
      (overTrivialization N Vj ej)
      (CategoryTheory.Over.mk (homOfLE (inf_le_right : Vi ⊓ Vj ≤ Vj)))).hom ≫
      ModularCurves.SheafOfModules.overUnitScalarEnd T.ringCatSheaf (Vi ⊓ Vj)
        ((glueTransitionUnit N ei ej : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj))
  rw [show ModularCurves.SheafOfModules.overUnitScalarEnd T.ringCatSheaf (Vi ⊓ Vj)
      ((glueTransitionUnit N ei ej : ↑Γ(T, Vi ⊓ Vj)ˣ) : ↑Γ(T, Vi ⊓ Vj)) = _ from hE,
    Iso.hom_inv_id_assoc]

/-- **(AP2-B1a′, ⊗-self — discharged)** Invertibility pairing `N ⊗ N^∨ ≅ 𝒪`: exactly the tree's
`nonempty_eval_iso` (`Picard/PicComparison.lean`), proved. Kept as a named wrapper for the assembly. -/
theorem nonempty_tensorObj_dualObj_unitObj {T : Scheme.{u}} {N : T.Modules}
    (hN : IsInvertible N) :
    Nonempty (tensorObj N (dualObj N) ≅ unitObj T) :=
  nonempty_eval_iso hN

/-- **(AP2-B1a, hbij factor α)** The pushforward-slot section generates: multiplication into
the restricted `glueSectionA` is bijective on every open inside the trivialising one. Via
`glueSectionA_eq_adjUnit` the section is the adjunction-unit image of the seed, and
`hp g W` identifies `Γ(T, W)` with the pulled structure sections; the pulled trivialisation
`e` carries the generation statement. -/
theorem bijective_smul_glueSectionA_res {X S : Scheme.{u}} {p : X ⟶ S} {T : Scheme.{u}}
    (g : T ⟶ S) (hp : UniversallyOConnected p) (N : T.Modules) {V : T.Opens}
    (e : (AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj N ≅ unitObj V.toScheme)
    {W : T.Opens} (hW : W ≤ V) :
    Function.Bijective (fun r : ↑Γ(T, W) ↦ r •
      ((AlgebraicGeometry.Scheme.Modules.pushforward (pullback.snd p g)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj N)).presheaf.map
        (homOfLE hW).op (glueSectionA g N V e)) := by
  -- the restricted over-trivialisation and its seed
  set rOTW : N.over W ≅ _root_.SheafOfModules.unit (T.ringCatSheaf.over W) :=
    ModularCurves.SheafOfModules.restrictOverTrivialization T.ringCatSheaf N V
      (overTrivialization N V e) (CategoryTheory.Over.mk (homOfLE hW)) with hrOTW
  -- the restricted seed is the restricted trivialisation's seed
  have hseedW : N.presheaf.map (homOfLE hW).op (glueSectionASeed N V e) =
      rOTW.inv.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 W)))
        (show (T.ringCatSheaf.over W).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 W))) from 1) := by
    have hnat := PresheafOfModules.naturality_apply (overTrivialization N V e).inv.val
      (CategoryTheory.Over.mkIdTerminal.from
        (CategoryTheory.Over.mk (homOfLE hW))).op
      (show (T.ringCatSheaf.over V).obj.obj
        (Opposite.op (CategoryTheory.Over.mk (𝟙 V))) from 1)
    have h1 : (_root_.SheafOfModules.unit (T.ringCatSheaf.over V)).val.map
        (CategoryTheory.Over.mkIdTerminal.from
          (CategoryTheory.Over.mk (homOfLE hW))).op
        (show (T.ringCatSheaf.over V).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 V))) from 1) =
        (show (T.ringCatSheaf.over V).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (homOfLE hW))) from 1) :=
      PresheafOfModules.unit_map_one (T.ringCatSheaf.over V).obj
        (CategoryTheory.Over.mkIdTerminal.from
          (CategoryTheory.Over.mk (homOfLE hW))).op
    rw [h1] at hnat
    exact hnat.symm
  -- normalisation of the restricted trivialisation's seed
  have hxW : rOTW.hom.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 W)))
      (N.presheaf.map (homOfLE hW).op (glueSectionASeed N V e)) =
      (show (T.ringCatSheaf.over W).obj.obj
        (Opposite.op (CategoryTheory.Over.mk (𝟙 W))) from 1) := by
    rw [hseedW]
    have hcomp := congrArg
      (fun q ↦ q.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 W)))) rOTW.inv_hom_id
    have h := CategoryTheory.ConcreteCategory.congr_hom hcomp
      (show (T.ringCatSheaf.over W).obj.obj
        (Opposite.op (CategoryTheory.Over.mk (𝟙 W))) from 1)
    erw [AlgebraicGeometry.Scheme.Modules.sheafOfModules_comp_app_apply] at h
    exact h
  -- the chain identification for the pulled trivialisation at W
  have hpW : (AlgebraicGeometry.Scheme.Modules.overEquiv
      (pullback.snd p g ⁻¹ᵁ W)).functor.map
      (AlgebraicGeometry.Scheme.Modules.localPullbackTrivializationT
        (pullback.snd p g) N W rOTW).hom =
      (AlgebraicGeometry.Scheme.Modules.localPullbackModuleIso (pullback.snd p g) N W).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g ∣_ W)).map
          ((AlgebraicGeometry.Scheme.Modules.overEquiv W).functor.map rOTW.hom) ≫
        (AlgebraicGeometry.Scheme.Modules.localPullbackUnitIso (pullback.snd p g) W).hom := by
    dsimp only [AlgebraicGeometry.Scheme.Modules.localPullbackTrivializationT]
    simp only [Functor.FullyFaithful.preimageIso_hom,
      Functor.FullyFaithful.map_preimage, Iso.trans_hom, Functor.mapIso_hom]
    rfl
  have hone := AlgebraicGeometry.Scheme.Modules.localPullbackTrivialization_inv_one_ofSection
    (pullback.snd p g) N W rOTW
    (N.presheaf.map (homOfLE hW).op (glueSectionASeed N V e))
    (AlgebraicGeometry.Scheme.Modules.localPullbackTrivializationT
      (pullback.snd p g) N W rOTW) hxW hpW
  -- the target section is the pulled trivialisation's inverse image of 1
  have hσ : ((AlgebraicGeometry.Scheme.Modules.pushforward (pullback.snd p g)).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj N)).presheaf.map
      (homOfLE hW).op (glueSectionA g N V e) =
      (AlgebraicGeometry.Scheme.Modules.localPullbackTrivializationT
        (pullback.snd p g) N W rOTW).inv.val.app
        (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ W))))
        (show ((pullback p g).ringCatSheaf.over (pullback.snd p g ⁻¹ᵁ W)).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ W)))) from 1) := by
    rw [glueSectionA_eq_adjUnit g N V e]
    refine (PresheafOfModules.naturality_apply
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
        (pullback.snd p g)).unit.app N).val (homOfLE hW).op
      (glueSectionASeed N V e)).symm.trans ?_
    exact hone.symm
  rw [funext (fun r : ↑Γ(T, W) ↦ congrArg (fun z ↦ r • z) hσ)]
  -- bijectivity: ring sections iso (hp) composed with the iso-component against 1
  have hstep : ∀ (r : ↑Γ(T, W))
      (X : ↑Γ((AlgebraicGeometry.Scheme.Modules.pushforward (pullback.snd p g)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj N), W)),
      X = (AlgebraicGeometry.Scheme.Modules.localPullbackTrivializationT
        (pullback.snd p g) N W rOTW).inv.val.app
        (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ W))))
        (show ((pullback p g).ringCatSheaf.over (pullback.snd p g ⁻¹ᵁ W)).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ W)))) from 1) →
      r • X = (AlgebraicGeometry.Scheme.Modules.localPullbackTrivializationT
        (pullback.snd p g) N W rOTW).inv.val.app
        (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ W))))
        (show ((pullback p g).ringCatSheaf.over (pullback.snd p g ⁻¹ᵁ W)).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ W)))) from
          ((pullback.snd p g).app W).hom r) := by
    intro r X hX
    have h1 : (show ((pullback p g).ringCatSheaf.over (pullback.snd p g ⁻¹ᵁ W)).obj.obj
        (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ W)))) from
        ((pullback.snd p g).app W).hom r) =
        (show ((pullback p g).ringCatSheaf.over (pullback.snd p g ⁻¹ᵁ W)).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ W)))) from
          ((pullback.snd p g).app W).hom r) •
        (show ((pullback p g).ringCatSheaf.over (pullback.snd p g ⁻¹ᵁ W)).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ W)))) from 1) := by
      rw [smul_eq_mul, mul_one]
    have h2 := map_smul (CategoryTheory.ConcreteCategory.hom
      ((AlgebraicGeometry.Scheme.Modules.localPullbackTrivializationT
        (pullback.snd p g) N W rOTW).inv.val.app
        (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ W))))))
      (show ((pullback p g).ringCatSheaf.over (pullback.snd p g ⁻¹ᵁ W)).obj.obj
        (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ W)))) from
        ((pullback.snd p g).app W).hom r)
      (show ((pullback p g).ringCatSheaf.over (pullback.snd p g ⁻¹ᵁ W)).obj.obj
        (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ W)))) from 1)
    rw [hX]
    show (show ((pullback p g).ringCatSheaf.over (pullback.snd p g ⁻¹ᵁ W)).obj.obj
        (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ W)))) from
        ((pullback.snd p g).app W).hom r) •
      ((AlgebraicGeometry.Scheme.Modules.localPullbackTrivializationT
        (pullback.snd p g) N W rOTW).inv.val.app
        (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ W))))
        (show ((pullback p g).ringCatSheaf.over (pullback.snd p g ⁻¹ᵁ W)).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ W)))) from 1)) = _
    exact h2.symm.trans (congrArg (fun z ↦
      (AlgebraicGeometry.Scheme.Modules.localPullbackTrivializationT
        (pullback.snd p g) N W rOTW).inv.val.app
        (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ W)))) z) h1.symm)
  rw [funext (fun r ↦ hstep r _ rfl)]
  refine Function.Bijective.comp ?_ ?_
  · -- the inverse-trivialisation component is bijective (two-sided inverse: the hom component)
    refine Function.bijective_iff_has_inverse.mpr
      ⟨fun y ↦ (AlgebraicGeometry.Scheme.Modules.localPullbackTrivializationT
        (pullback.snd p g) N W rOTW).hom.val.app
        (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ W)))) y,
        fun y ↦ ?_, fun y ↦ ?_⟩
    · have hcomp := congrArg (fun q ↦ q.val.app
        (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ W)))))
        (AlgebraicGeometry.Scheme.Modules.localPullbackTrivializationT
          (pullback.snd p g) N W rOTW).inv_hom_id
      have h := CategoryTheory.ConcreteCategory.congr_hom hcomp y
      erw [AlgebraicGeometry.Scheme.Modules.sheafOfModules_comp_app_apply] at h
      exact h
    · have hcomp := congrArg (fun q ↦ q.val.app
        (Opposite.op (CategoryTheory.Over.mk (𝟙 (pullback.snd p g ⁻¹ᵁ W)))))
        (AlgebraicGeometry.Scheme.Modules.localPullbackTrivializationT
          (pullback.snd p g) N W rOTW).hom_inv_id
      have h := CategoryTheory.ConcreteCategory.congr_hom hcomp y
      erw [AlgebraicGeometry.Scheme.Modules.sheafOfModules_comp_app_apply] at h
      exact h
  · -- the structure map on sections is bijective: universal O-connectedness
    haveI := hp g W
    have hb : Function.Bijective ((pullback.snd p g).app W).hom :=
      (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp inferInstance
    exact hb

/-- **(AP2-B1a, base generation)** Multiplication into the restricted seed is bijective:
the restricted seed is the restricted over-trivialisation's inverse image of `1`, so the
map is the trivialisation's inverse component composed with the identity bridge into the
over-site unit. No `O`-connectedness needed — the base-side twin of
`bijective_smul_glueSectionA_res`. -/
theorem bijective_smul_glueSectionASeed_res {T : Scheme.{u}} (N : T.Modules) {V : T.Opens}
    (e : (AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj N ≅ unitObj V.toScheme)
    {W : T.Opens} (hW : W ≤ V) :
    Function.Bijective (fun r : ↑Γ(T, W) ↦ r •
      N.presheaf.map (homOfLE hW).op (glueSectionASeed N V e)) := by
  set rOTW : N.over W ≅ _root_.SheafOfModules.unit (T.ringCatSheaf.over W) :=
    ModularCurves.SheafOfModules.restrictOverTrivialization T.ringCatSheaf N V
      (overTrivialization N V e) (CategoryTheory.Over.mk (homOfLE hW)) with hrOTW
  have hseedW : N.presheaf.map (homOfLE hW).op (glueSectionASeed N V e) =
      rOTW.inv.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 W)))
        (show (T.ringCatSheaf.over W).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 W))) from 1) := by
    have hnat := PresheafOfModules.naturality_apply (overTrivialization N V e).inv.val
      (CategoryTheory.Over.mkIdTerminal.from
        (CategoryTheory.Over.mk (homOfLE hW))).op
      (show (T.ringCatSheaf.over V).obj.obj
        (Opposite.op (CategoryTheory.Over.mk (𝟙 V))) from 1)
    have h1 : (_root_.SheafOfModules.unit (T.ringCatSheaf.over V)).val.map
        (CategoryTheory.Over.mkIdTerminal.from
          (CategoryTheory.Over.mk (homOfLE hW))).op
        (show (T.ringCatSheaf.over V).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 V))) from 1) =
        (show (T.ringCatSheaf.over V).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (homOfLE hW))) from 1) :=
      PresheafOfModules.unit_map_one (T.ringCatSheaf.over V).obj
        (CategoryTheory.Over.mkIdTerminal.from
          (CategoryTheory.Over.mk (homOfLE hW))).op
    rw [h1] at hnat
    exact hnat.symm
  have hstep : ∀ (r : ↑Γ(T, W)) (X : ↑Γ(N, W)),
      X = rOTW.inv.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 W)))
        (show (T.ringCatSheaf.over W).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 W))) from 1) →
      r • X = rOTW.inv.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 W)))
        (show (T.ringCatSheaf.over W).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 W))) from r) := by
    intro r X hX
    have h1 : (show (T.ringCatSheaf.over W).obj.obj
        (Opposite.op (CategoryTheory.Over.mk (𝟙 W))) from r) =
        (show (T.ringCatSheaf.over W).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 W))) from r) •
        (show (T.ringCatSheaf.over W).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 W))) from 1) := by
      rw [smul_eq_mul, mul_one]
    have h2 := map_smul (CategoryTheory.ConcreteCategory.hom
      (rOTW.inv.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 W)))))
      (show (T.ringCatSheaf.over W).obj.obj
        (Opposite.op (CategoryTheory.Over.mk (𝟙 W))) from r)
      (show (T.ringCatSheaf.over W).obj.obj
        (Opposite.op (CategoryTheory.Over.mk (𝟙 W))) from 1)
    rw [hX]
    show (show (T.ringCatSheaf.over W).obj.obj
        (Opposite.op (CategoryTheory.Over.mk (𝟙 W))) from r) •
      (rOTW.inv.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 W)))
        (show (T.ringCatSheaf.over W).obj.obj
          (Opposite.op (CategoryTheory.Over.mk (𝟙 W))) from 1)) = _
    exact h2.symm.trans (congrArg (fun z ↦
      rOTW.inv.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 W))) z) h1.symm)
  rw [funext (fun r : ↑Γ(T, W) ↦ hstep r _ hseedW)]
  refine Function.Bijective.comp ?_ ?_
  · refine Function.bijective_iff_has_inverse.mpr
      ⟨fun y ↦ rOTW.hom.val.app (Opposite.op (CategoryTheory.Over.mk (𝟙 W))) y,
        fun y ↦ ?_, fun y ↦ ?_⟩
    · have hcomp := congrArg (fun q ↦ q.val.app
        (Opposite.op (CategoryTheory.Over.mk (𝟙 W)))) rOTW.inv_hom_id
      have h := CategoryTheory.ConcreteCategory.congr_hom hcomp y
      erw [AlgebraicGeometry.Scheme.Modules.sheafOfModules_comp_app_apply] at h
      exact h
    · have hcomp := congrArg (fun q ↦ q.val.app
        (Opposite.op (CategoryTheory.Over.mk (𝟙 W)))) rOTW.hom_inv_id
      have h := CategoryTheory.ConcreteCategory.congr_hom hcomp y
      erw [AlgebraicGeometry.Scheme.Modules.sheafOfModules_comp_app_apply] at h
      exact h
  · exact ⟨fun a b h ↦ h, fun y ↦ ⟨y, rfl⟩⟩

/-- **(AP2-B1a, KM p. 65: "`f_*f^*(ℒ_{0,i}) = ℒ_{0,i}`")** Over a universally `O`-connected family,
`f_*f^*N ≅ N` for invertible `N` — assembled by cancelling the dual twist
(`nonempty_iso_of_tensorObj_unitObj`, `PicComparison.lean:909`) between the two obligations above.
Replaces the earlier opaque-adjunction-unit form (see the AP2-B1a REPLAN note on the board): KM's
proof consumes only this identification, not the unit. -/
theorem nonempty_pushforwardPullback_iso {X S : Scheme.{u}} {p : X ⟶ S}
    {T : Scheme.{u}} (g : T ⟶ S) (hp : UniversallyOConnected p)
    {N : T.Modules} (hN : IsInvertible N) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pushforward (pullback.snd p g)).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj N) ≅ N) := by
  obtain ⟨κ, V, hV, htriv⟩ := hN
  haveI : IsIso ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
      (pullback.snd p g)).unit.app N) := by
    refine AlgebraicGeometry.Scheme.Modules.isIso_of_bijective_app_on_cover _ V hV
      (fun i W hW ↦ ?_)
    have hα := bijective_smul_glueSectionA_res g hp N (htriv i).some hW
    have hseed := bijective_smul_glueSectionASeed_res N (htriv i).some hW
    have hfac : (fun r : ↑Γ(T, W) ↦ r •
        ((AlgebraicGeometry.Scheme.Modules.pushforward (pullback.snd p g)).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd p g)).obj N)).presheaf.map
          (homOfLE hW).op (glueSectionA g N (V i) (htriv i).some)) =
        (AlgebraicGeometry.Scheme.Modules.Hom.app
          ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
            (pullback.snd p g)).unit.app N) W) ∘
        (fun r : ↑Γ(T, W) ↦ r •
          N.presheaf.map (homOfLE hW).op (glueSectionASeed N (V i) (htriv i).some)) := by
      funext r
      show r • _ = AlgebraicGeometry.Scheme.Modules.Hom.app _ W
        (r • N.presheaf.map (homOfLE hW).op (glueSectionASeed N (V i) (htriv i).some))
      rw [AlgebraicGeometry.Scheme.Modules.Hom.app_smul]
      refine congrArg (fun z ↦ r • z) ?_
      rw [glueSectionA_eq_adjUnit g N (V i) (htriv i).some]
      exact (PresheafOfModules.naturality_apply
        ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
          (pullback.snd p g)).unit.app N).val (homOfLE hW).op
        (glueSectionASeed N (V i) (htriv i).some)).symm
    rw [hfac] at hα
    exact (Function.Bijective.of_comp_iff _ hseed).mp hα
  exact ⟨(asIso ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
    (pullback.snd p g)).unit.app N)).symm⟩

end ModularCurves

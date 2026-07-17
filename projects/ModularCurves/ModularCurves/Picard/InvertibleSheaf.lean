/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.Modules.Sheaf

import ModularCurves.ForMathlib.OpensMapFinal
import ModularCurves.ForMathlib.SheafOfModulesMonoidal

/-!
# Invertible sheaves of modules on a scheme

Stage P1 of the AINTLIB ModularCurves T-PIC0 stream (Pic of a scheme; GME 2.2.2,
pp. 108–109): the tensor product of `𝒪ₓ`-modules and the invertibility predicate, on
mathlib's `X.Modules = SheafOfModules X.ringCatSheaf`.

* `Scheme.Modules.tensorObj M N`: the sheafification of the presheaf tensor product
  `M.val ⊗ N.val` (mathlib has the monoidal structure on presheaves of modules and the
  sheafification functor; their composite is the classical `𝓛 ⊗_{𝒪ₓ} 𝓛'`).
* `Scheme.Modules.IsInvertible M`: `M` is trivialized by some open cover — "the
  formation of an invertible sheaf is local" (GME p. 109, proof of (2.17)).
* `isInvertible_unit`, `IsInvertible.pullback`, `nonempty_tensorObj_unit_iso`: the unit
  is invertible; invertibility is stable under pullback along any morphism of schemes;
  tensoring with the unit is trivial. (`IsInvertible.tensorObj` — stability under tensor
  product — lives in `ForMathlib/PullbackTensorMonoidal.lean`, proved sorry-free through
  the open-immersion pullback–tensor compatibility.)

The Picard group `Pic X` (iso classes of invertibles under `tensorObj`, GME (2.16))
and the fibre degree are staged behind this file. The only remaining GAP-1 residual is
the general-`f` form of `nonempty_pullback_tensorObj` below (registered
[PIC-P1b-MONO]-general): its open-immersion case is proved in
`ForMathlib/PullbackTensorMonoidal.lean` and is all the invertibility layer consumes,
so nothing here is gated by it. Everything else here is gap-free.

Decomposition, verbatim source quotes and adversarial attack logs:
`.mathlib-quality/decomposition-pic-coh.md` (stream v10.11, worker fable-PIC0).
Upstream candidate (mathlib `RingTheory/PicardGroup.lean` has the ring case and a
TODO "Connect to invertible sheaves on `Spec R`").
-/

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The monoidal structure on `X.PresheafOfModules`, transported through the definitional
equality `X.ringCatSheaf.obj = X.sheaf.obj ⋙ forget₂ CommRingCat RingCat`. -/
noncomputable instance (X : Scheme.{u}) : MonoidalCategoryStruct X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategoryStruct
    (_root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))

/-- The full monoidal category structure on `X.PresheafOfModules` (same transport as the
struct instance above), needed to transport isomorphisms through the tensor. -/
noncomputable instance (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory
    (_root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))

variable (X) in
/-- The structure sheaf as the unit `𝒪ₓ`-module. -/
noncomputable def unitObj : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- The tensor product of two `𝒪ₓ`-modules: the sheafification of the presheaf tensor
product (GME p. 108: "`Pic⁰` is a group functor with the identity `𝒪_E` under the
multiplication: `𝓛 · 𝓛' = 𝓛 ⊗ 𝓛'`"). -/
noncomputable def tensorObj (M N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (M.val ⊗ N.val)

/-- An `𝒪ₓ`-module is invertible if some open cover of `X` trivializes it (GME p. 109:
"The formation of an invertible sheaf is local"). Equivalently it is locally free of
rank one; the comparison with `SheafOfModules.IsLocallyFree` is deferred API. -/
def IsInvertible (M : X.Modules) : Prop :=
  ∃ (ι : Type u) (U : ι → X.Opens), iSup U = ⊤ ∧
    ∀ i, Nonempty ((Modules.pullback (U i).ι).obj M ≅ unitObj ↑(U i))

set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback of the structure sheaf along any morphism of schemes is the structure
sheaf (mathlib's `pullbackObjUnitToUnit` isomorphism, available because the
opens-preimage site functor is final — `Opens.map_final`; repackaged across the
`X.Modules` category-instance wrapper). -/
noncomputable def pullbackUnitIso (f : Y ⟶ X) :
    (Modules.pullback f).obj (unitObj X) ≅ unitObj Y :=
  let e := asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
  ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩

/-- The structure sheaf is an invertible `𝒪ₓ`-module. -/
theorem isInvertible_unit : IsInvertible (unitObj X) :=
  ⟨PUnit, fun _ ↦ ⊤, iSup_const, fun _ ↦ ⟨pullbackUnitIso (⊤ : X.Opens).ι⟩⟩

/-- Sheafification of the presheaf underlying a sheaf of modules is the sheaf itself
(the counit of the sheafification adjunction, an isomorphism on sheaves). Stated over
`SheafOfModules X.ringCatSheaf` (definitionally `X.Modules`): the `≅`-type must
elaborate with the `SheafOfModules` category instance for the mathlib counit-iso
instance to be found — the `X.Modules` category wrapper puts the goal in
instance-clothing the counit instances don't match (board v10.11.3/v10.35 dossier;
root cause + banked antidotes: v10.36).
The body is `asIso` of the *whole* counit, applied at `M` (mathlib's own idiom, cf.
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`): on this pin the per-object
`asIso (….counit.app M)` fails `IsIso` synthesis in instance-implicit position
(T-PIC1c anomaly), while the whole-counit instance head matches directly. -/
noncomputable def sheafifyValIso (M : SheafOfModules X.ringCatSheaf) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj M.val ≅ M :=
  (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app M

/-- A presheaf-of-modules morphism that is bijective on every open inside a covering
family is inverted by sheafification. -/
theorem sheafificationW_of_bijective_on_cover {A B : X.PresheafOfModules}
    (g : A ⟶ B) {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (hbij : ∀ (i : ι) (W : X.Opens), W ≤ U i →
      Function.Bijective (g.app (Opposite.op W))) :
    PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj) g := by
  have hsieve : ∀ (V : (TopologicalSpace.Opens ↥X)ᵒᵖ) (S : Sieve V.unop),
      (∀ (i : ι) (W : X.Opens) (hWi : W ≤ U i) (hWV : W ≤ V.unop), S (homOfLE hWV)) →
      S ∈ Opens.grothendieckTopology ↥X V.unop := by
    intro V S hS
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    have hxT : x ∈ iSup U := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxT
    exact ⟨V.unop ⊓ U i, homOfLE inf_le_left,
      hS i (V.unop ⊓ U i) inf_le_right inf_le_left, ⟨hx, hi⟩⟩
  haveI hinj : Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥X)
      ((PresheafOfModules.toPresheaf _).map g) := by
    constructor
    intro V x y hxy
    refine hsieve V _ (fun i W hWi hWV => ?_)
    refine (hbij i W hWi).injective ?_
    have hnx := PresheafOfModules.naturality_apply g (homOfLE hWV).op x
    have hny := PresheafOfModules.naturality_apply g (homOfLE hWV).op y
    exact hnx.trans ((congrArg (fun z => B.map (homOfLE hWV).op z) hxy).trans hny.symm)
  haveI hsurj : Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥X)
      ((PresheafOfModules.toPresheaf _).map g) := by
    constructor
    intro V s
    refine hsieve (Opposite.op V) _ (fun i W hWi hWV => ?_)
    obtain ⟨t, ht⟩ := (hbij i W hWi).surjective (B.map (homOfLE hWV).op s)
    exact ⟨t, ht⟩
  exact (PresheafOfModules.sheafificationW_iff_isLocallyBijective _ g).mpr ⟨hinj, hsurj⟩

/-- Being an isomorphism of `𝒪ₓ`-modules is Zariski-local. -/
theorem isIso_of_isIso_restrict {A B : X.Modules} (g : A ⟶ B) {ι : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤)
    (h : ∀ i, IsIso ((restrictFunctor (U i).ι).map g)) : IsIso g := by
  have happ : ∀ (i : ι) (W : X.Opens), W ≤ U i → IsIso (g.app W) := by
    intro i W hW
    have h1 := Hom.isIso_iff_isIso_app.mp (h i) ((U i).ι ⁻¹ᵁ W)
    have h2 : (U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ W) = W := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.mpr hW]
    rw [← h2]
    exact h1
  have hw : PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj) g.val := by
    refine sheafificationW_of_bijective_on_cover g.val U hU (fun i W hW => ?_)
    haveI := happ i W hW
    exact (ConcreteCategory.isIso_iff_bijective (g.app W)).mp inferInstance
  rw [PresheafOfModules.sheafificationW_iff] at hw
  have hnat := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).counit.naturality g
  have hg : g = (sheafifyValIso A).inv ≫
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map g.val ≫
      (sheafifyValIso B).hom := by
    let shMap :=
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map g.val
    have hnat' : (sheafifyValIso A).hom ≫ g =
        shMap ≫ (sheafifyValIso B).hom := hnat.symm
    have hleft := congrArg (fun m ↦ (sheafifyValIso A).inv ≫ m) hnat'
    have hcancel : (sheafifyValIso A).inv ≫
        ((sheafifyValIso A).hom ≫ g) = g := by
      exact (congrArg (fun m ↦ m ≫ g)
        (sheafifyValIso A).inv_hom_id).trans (Category.id_comp g)
    change g = (sheafifyValIso A).inv ≫
      (shMap ≫ (sheafifyValIso B).hom)
    exact hcancel.symm.trans hleft
  rw [hg]
  haveI : IsIso ((PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map g.val) := hw
  exact IsIso.comp_isIso' (sheafifyValIso A).isIso_inv
    (IsIso.comp_isIso' hw (sheafifyValIso B).isIso_hom)

/-- Tensoring with the unit is trivial: `M ⊗ 𝒪ₓ ≅ M` (presheaf unitor + the
sheafification of a sheaf being itself; no GAP-1 content). -/
theorem nonempty_tensorObj_unit_iso (M : X.Modules) : Nonempty (tensorObj M (unitObj X) ≅ M) :=
  ⟨((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (ρ_ M.val)).trans
    (sheafifyValIso M)⟩

/-- Invertibility is stable under pullback: a trivializing cover of `X` pulls back to
a trivializing cover of `Y` (GME p. 108: "If `g : T' → T` is an `S`-morphism, we have
`g_E = 1_E ×_S g : E_{T'} → E_T`. This induces `Pic^ν(g)(𝓛) = g_E^*(𝓛)`"). -/
theorem IsInvertible.pullback {M : X.Modules} (hM : IsInvertible M) (f : Y ⟶ X) :
    IsInvertible ((Modules.pullback f).obj M) := by
  obtain ⟨ι, U, hU, htriv⟩ := hM
  refine ⟨ι, fun i ↦ f ⁻¹ᵁ U i, f.iSup_preimage_eq_top hU, fun i ↦ ?_⟩
  obtain ⟨e⟩ := htriv i
  exact ⟨(Modules.pullbackComp (f ⁻¹ᵁ U i).ι f).app M ≪≫
    (Modules.pullbackCongr (morphismRestrict_ι f (U i)).symm).app M ≪≫
    (Modules.pullbackComp (f ∣_ U i) (U i).ι).symm.app M ≪≫
    (Modules.pullback (f ∣_ U i)).mapIso e ≪≫ pullbackUnitIso (f ∣_ U i)⟩

/-- The sheafified tensor respects isomorphisms in each variable (functoriality of the
presheaf tensor followed by `sheafification`). GAP-1-free. -/
noncomputable def tensorObjCongr {M M' N N' : X.Modules} (eM : M ≅ M') (eN : N ≅ N') :
    tensorObj M N ≅ tensorObj M' N' :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (Functor.mapIso (SheafOfModules.forget X.ringCatSheaf) eM ⊗ᵢ
      Functor.mapIso (SheafOfModules.forget X.ringCatSheaf) eN)

/-- A trivialization of `P` on an open `U` restricts to a trivialization on any smaller
open `W ≤ U`: pull the `U`-trivialization back along the inclusion `W ↪ U` and use that
pullback preserves the structure sheaf. `W.ι` factors as `X.homOfLE e ≫ U.ι`, so
`pullbackComp`/`pullbackCongr` reduce the `W`-pullback to a pullback of the trivial
`U`-pullback. GAP-1-free. -/
noncomputable def restrictTrivialization {P : X.Modules} {U W : X.Opens} (e : W ≤ U)
    (eP : (Modules.pullback U.ι).obj P ≅ unitObj ↑U) :
    (Modules.pullback W.ι).obj P ≅ unitObj ↑W :=
  (Modules.pullbackCongr (X.homOfLE_ι e).symm).app P ≪≫
    ((Modules.pullbackComp (X.homOfLE e) U.ι).app P).symm ≪≫
    (Modules.pullback (X.homOfLE e)).mapIso eP ≪≫
    pullbackUnitIso (X.homOfLE e)

/-- `IsInvertible` is phrased with *pullback* trivializations, while the consumers of a
trivialization (`overTrivializationOfRestrictIso`, the dual, the base-Čech flatness route)
want the *restriction* form. These two bridges are the only place the
`restrictFunctorIsoPullback` plumbing needs to appear. -/
noncomputable def restrictIsoOfPullbackIso (M : X.Modules) (U : X.Opens)
    (e : (Modules.pullback U.ι).obj M ≅ unitObj U.toScheme) :
    M.restrict U.ι ≅ unitObj U.toScheme :=
  (restrictFunctorIsoPullback U.ι).app M ≪≫ e

/-- The converse bridge of `restrictIsoOfPullbackIso`: a restriction trivialization gives the
pullback trivialization that `IsInvertible` asks for. -/
noncomputable def pullbackIsoOfRestrictIso (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ unitObj U.toScheme) :
    (Modules.pullback U.ι).obj M ≅ unitObj U.toScheme :=
  (restrictFunctorIsoPullback U.ι).symm.app M ≪≫ e

/-- A trivialization on an open subscheme induces the corresponding trivialization
on the over-site of that open. -/
noncomputable def overTrivializationOfRestrictIso (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ unitObj U.toScheme) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (overEquiv U).fullyFaithfulFunctor.preimageIso
    ((overFunctorEquiv U).app M ≪≫ e ≪≫
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm)

end AlgebraicGeometry.Scheme.Modules

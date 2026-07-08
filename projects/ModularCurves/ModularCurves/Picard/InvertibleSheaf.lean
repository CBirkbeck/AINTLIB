/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import ModularCurves.ForMathlib.OpensMapFinal

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
* `isInvertible_unit`, `IsInvertible.pullback`, `exists_tensorObj_unit_iso`,
  `IsInvertible.tensorObj`: the unit is invertible; invertibility is stable under
  pullback along any morphism of schemes and under tensor product; tensoring with the
  unit is trivial.

The Picard group `Pic X` (iso classes of invertibles under `tensorObj`, GME (2.16))
and the fibre degree are staged behind this file; the group law's coherence isos
rest on the sheafification ⊗-compatibility gap **GAP-1** recorded in
`.mathlib-quality/decomposition-pic-coh.md`, which gates `IsInvertible.tensorObj`
below and the future group structure. Everything else here is gap-free.

Decomposition, verbatim source quotes and adversarial attack logs:
`.mathlib-quality/decomposition-pic-coh.md` (stream v10.11, worker fable-PIC0).
Upstream candidate (mathlib `RingTheory/PicardGroup.lean` has the ring case and a
TODO "Connect to invertible sheaves on `Spec R`").
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The monoidal structure on presheaves of modules over `X.ringCatSheaf.obj`,
transported through the definitional equality
`X.ringCatSheaf.obj = X.sheaf.val ⋙ forget₂ CommRingCat RingCat`. -/
noncomputable instance (X : Scheme.{u}) :
    MonoidalCategoryStruct (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  inferInstanceAs (MonoidalCategoryStruct
    (_root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))

variable (X) in
/-- The structure sheaf as the unit `𝒪ₓ`-module. -/
noncomputable def unitObj : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- The tensor product of two `𝒪ₓ`-modules: the sheafification of the presheaf tensor
product (GME p. 108: "`Pic⁰` is a group functor with the identity `𝒪_E` under the
multiplication: `𝓛 · 𝓛' = 𝓛 ⊗ 𝓛'`"). -/
noncomputable def tensorObj (M N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (MonoidalCategoryStruct.tensorObj M.val N.val)

/-- An `𝒪ₓ`-module is invertible if some open cover of `X` trivializes it (GME p. 109:
"The formation of an invertible sheaf is local"). Equivalently it is locally free of
rank one; the comparison with `SheafOfModules.IsLocallyFree` is deferred API. -/
def IsInvertible (M : X.Modules) : Prop :=
  ∃ (ι : Type u) (U : ι → X.Opens), iSup U = ⊤ ∧
    ∀ i, Nonempty ((Modules.pullback (U i).ι).obj M ≅ unitObj ↑(U i))

/-- Pullback of the structure sheaf along any morphism of schemes is the structure
sheaf (mathlib's `pullbackObjUnitToUnit` isomorphism, available because the
opens-preimage site functor is final — `Opens.map_final`; repackaged across the
`X.Modules` category-instance wrapper). -/
noncomputable def pullbackUnitIso (f : Y ⟶ X) :
    (Modules.pullback f).obj (unitObj X) ≅ unitObj Y :=
  let e : (SheafOfModules.pullback (Scheme.Hom.toRingCatSheafHom f)).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅ SheafOfModules.unit Y.ringCatSheaf :=
    asIso (SheafOfModules.pullbackObjUnitToUnit (Scheme.Hom.toRingCatSheafHom f))
  ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩

/-- The structure sheaf is an invertible `𝒪ₓ`-module. -/
theorem isInvertible_unit : IsInvertible (unitObj X) :=
  ⟨PUnit, fun _ => ⊤, iSup_const, fun _ => ⟨pullbackUnitIso (⊤ : X.Opens).ι⟩⟩

/-- Sheafification of the presheaf underlying a sheaf of modules is the sheaf itself
(the counit of the sheafification adjunction, an isomorphism on sheaves). Stated over
`SheafOfModules X.ringCatSheaf` (definitionally `X.Modules`): the `≅`-type must
elaborate with the `SheafOfModules` category instance for the mathlib counit-iso
instance to be found — the `X.Modules` category wrapper puts the goal in
instance-clothing the counit instances don't match (board v10.11.3/v10.35 dossier). -/
noncomputable def sheafifyValIso (M : SheafOfModules X.ringCatSheaf) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj M.val ≅ M := by
  have h : IsIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit.app M) := by infer_instance
  exact @asIso _ _ _ _ _ h

/-- Tensoring with the unit is trivial: `M ⊗ 𝒪ₓ ≅ M` (presheaf unitor + the
sheafification of a sheaf being itself; no GAP-1 content). -/
theorem exists_tensorObj_unit_iso (M : X.Modules) :
    Nonempty (tensorObj M (unitObj X) ≅ M) := by
  have e : (tensorObj M (unitObj X) : SheafOfModules X.ringCatSheaf) ≅ M :=
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (MonoidalCategoryStruct.rightUnitor M.val)).trans (sheafifyValIso M)
  exact ⟨⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩

/-- Invertibility is stable under pullback: a trivializing cover of `X` pulls back to
a trivializing cover of `Y` (GME p. 108: "If `g : T' → T` is an `S`-morphism, we have
`g_E = 1_E ×_S g : E_{T'} → E_T`. This induces `Pic^ν(g)(𝓛) = g_E^*(𝓛)`"). -/
theorem IsInvertible.pullback {M : X.Modules} (hM : IsInvertible M) (f : Y ⟶ X) :
    IsInvertible ((Modules.pullback f).obj M) := by
  obtain ⟨ι, U, hU, htriv⟩ := hM
  refine ⟨ι, fun i => f ⁻¹ᵁ U i, f.iSup_preimage_eq_top hU, fun i => ?_⟩
  obtain ⟨e⟩ := htriv i
  exact ⟨((Modules.pullbackComp (f ⁻¹ᵁ U i).ι f).app M).trans <|
    (eqToIso (by rw [← morphismRestrict_ι])).trans <|
      ((Modules.pullbackComp (f ∣_ U i) (U i).ι).symm.app M).trans <|
        ((Modules.pullback (f ∣_ U i)).mapIso e).trans (pullbackUnitIso (f ∣_ U i))⟩

/-- The tensor product of invertible `𝒪ₓ`-modules is invertible (GME p. 108: `Pic(E_T)`
is "the group of isomorphism classes of all invertible sheaves"). **GAP-1-gated**: the
proof needs restriction-to-opens to commute with the sheafified tensor; see the
decomposition artifact. -/
theorem IsInvertible.tensorObj {M N : X.Modules}
    (hM : IsInvertible M) (hN : IsInvertible N) : IsInvertible (tensorObj M N) := by
  sorry

end AlgebraicGeometry.Scheme.Modules

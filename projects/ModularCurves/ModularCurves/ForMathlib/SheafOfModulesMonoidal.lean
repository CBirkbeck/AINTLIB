/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Localization.Monoidal.Basic

/-!
# Towards the monoidal structure on sheaves of modules ([GAP1-W-MONO])

The AINTLIB ModularCurves GAP-1 development, route (b′) (board v10.64/v10.65): equip
`SheafOfModules` with a monoidal structure by localizing the monoidal category of
presheaves of modules at the class of morphisms inverted by sheafification, via
mathlib's `LocalizedMonoidal` machinery. The single load-bearing mathematical leaf is
tensor-stability of that class; everything else is registration plumbing.

* `PresheafOfModules.sheafificationW`: the inverted class.
* `sheafificationW_isLocalization`: the `IsLocalization` registration at `α = 𝟙`
  (reflective case), via `Adjunction.isLocalization`.
* `sheafificationW_iff_isLocallyBijective`: membership = locally injective + locally
  surjective on underlying presheaves of abelian groups (through mathlib's
  `WEqualsLocallyBijective` and the reflection of isomorphisms by `toSheaf`).
* `[GAP1-W-MONO]` (staged): tensor-stability. The locally-surjective half
  (`IsLocallySurjective.tensorHom`) is proven at the level of sections; the
  locally-injective half (`IsLocallyInjective.tensorHom`) is the stalkwise/filtered
  argument (no flatness — stalks of a locally bijective map are isomorphisms) and is
  a registered work-in-progress leaf.

Once the leaf closes, `LocalizedMonoidal (sheafification (𝟙 _)) (sheafificationW _) ε`
with `ε` the sheafified-unit counit iso hands `SheafOfModules` its monoidal structure
with monoidal sheafification — the GAP-1 kernel, tensor-closure of invertible sheaves,
and the Pic-group coherences (board v10.64).
-/

universe v v' u u'

open CategoryTheory MonoidalCategory

namespace PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

/-- The class of morphisms of presheaves of modules inverted by the sheafification
functor: the localizing class for `SheafOfModules`. -/
def sheafificationW : MorphismProperty (PresheafOfModules.{v} R₀) :=
  (MorphismProperty.isomorphisms _).inverseImage (sheafification.{v} α)

lemma sheafificationW_iff {M N : PresheafOfModules.{v} R₀} (f : M ⟶ N) :
    sheafificationW.{v} α f ↔ IsIso ((sheafification.{v} α).map f) :=
  Iff.rfl

/-- Membership in the localizing class is local bijectivity of the underlying morphism
of presheaves of abelian groups: the sheafification of modules inverts exactly the
locally bijective maps. -/
lemma sheafificationW_iff_isLocallyBijective {M N : PresheafOfModules.{v} R₀}
    (f : M ⟶ N) :
    sheafificationW.{v} α f ↔
      Presheaf.IsLocallyInjective J ((toPresheaf R₀).map f) ∧
        Presheaf.IsLocallySurjective J ((toPresheaf R₀).map f) := by
  rw [sheafificationW_iff]
  constructor
  · intro h
    have h1 : IsIso ((SheafOfModules.toSheaf R).map ((sheafification.{v} α).map f)) :=
      inferInstance
    have h2 : IsIso ((presheafToSheaf J AddCommGrpCat).map ((toPresheaf R₀).map f)) := h1
    have h3 : J.W ((toPresheaf R₀).map f) := (J.W_iff _).mpr h2
    exact ⟨h3.isLocallyInjective, h3.isLocallySurjective⟩
  · rintro ⟨h1, h2⟩
    have h3 : J.W ((toPresheaf R₀).map f) := J.W_of_isLocallyBijective _
    have h4 : IsIso ((presheafToSheaf J AddCommGrpCat).map ((toPresheaf R₀).map f)) :=
      (J.W_iff _).mp h3
    have h5 : IsIso ((SheafOfModules.toSheaf R).map ((sheafification.{v} α).map f)) := h4
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf R)

section Reflective

variable (R' : Sheaf J RingCat.{u})

/-- At `α = 𝟙` the sheafification adjunction is reflective (`forget` is fully faithful
and `restrictScalars (𝟙 _)` is an equivalence), so the sheafification functor is a
localization at `sheafificationW`. -/
instance sheafificationW_isLocalization :
    (sheafification.{v} (𝟙 R'.obj)).IsLocalization (sheafificationW.{v} (𝟙 R'.obj)) := by
  have h : ((SheafOfModules.forget R' ⋙ restrictScalars (𝟙 R'.obj))).Full :=
    Functor.Full.comp _ _
  have h' : ((SheafOfModules.forget R' ⋙ restrictScalars (𝟙 R'.obj))).Faithful :=
    Functor.Faithful.comp _ _
  exact (sheafificationAdjunction (𝟙 R'.obj)).isLocalization

end Reflective

section Tensor

variable {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  {M₁ M₂ N₁ N₂ : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}

/-- The locally-surjective half of the [GAP1-W-MONO] tensor-stability leaf: the tensor
product of locally surjective morphisms of presheaves of modules is locally surjective.
Sections of the tensor presheaf are finite sums of simple tensors; each factor is
locally hit, and the finitely many image sieves intersect to a covering sieve. -/
lemma isLocallySurjective_tensorHom (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
    [Presheaf.IsLocallySurjective J ((toPresheaf _).map f)]
    [Presheaf.IsLocallySurjective J ((toPresheaf _).map g)] :
    Presheaf.IsLocallySurjective J ((toPresheaf _).map (f ⊗ₘ g)) := by
  constructor
  intro U t
  induction t using TensorProduct.induction_on with
  | zero =>
      refine J.superset_covering (fun V p _ => ⟨0, ?_⟩) (J.top_mem U)
      show (f ⊗ₘ g).app (Opposite.op V) 0 = (M₂ ⊗ N₂).map p.op 0
      erw [map_zero]
  | tmul m n =>
      refine J.superset_covering ?_ (J.intersection_covering
        (Presheaf.imageSieve_mem J ((toPresheaf _).map f) m)
        (Presheaf.imageSieve_mem J ((toPresheaf _).map g) n))
      rintro V p ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      refine ⟨a ⊗ₜ b, ?_⟩
      have ha' : f.app (Opposite.op V) a = M₂.map p.op m := ha
      have hb' : g.app (Opposite.op V) b = N₂.map p.op n := hb
      show (f ⊗ₘ g).app (Opposite.op V) (a ⊗ₜ b) = (M₂ ⊗ N₂).map p.op (m ⊗ₜ n)
      erw [Monoidal.tensorHom_app, ModuleCat.MonoidalCategory.tensorHom_tmul,
        Monoidal.tensorObj_map_tmul]
      rw [ha', hb']
      rfl
  | add t₁ t₂ h₁ h₂ =>
      refine J.superset_covering ?_ (J.intersection_covering h₁ h₂)
      rintro V p ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
      refine ⟨x₁ + x₂, ?_⟩
      have hx₁' : (f ⊗ₘ g).app (Opposite.op V) x₁ = (M₂ ⊗ N₂).map p.op t₁ := hx₁
      have hx₂' : (f ⊗ₘ g).app (Opposite.op V) x₂ = (M₂ ⊗ N₂).map p.op t₂ := hx₂
      show (f ⊗ₘ g).app (Opposite.op V) (x₁ + x₂) = (M₂ ⊗ N₂).map p.op (t₁ + t₂)
      erw [map_add, map_add]
      rw [hx₁', hx₂']
      rfl

/-- The locally-injective half of the [GAP1-W-MONO] tensor-stability leaf — for
LOCALLY BIJECTIVE `f` and `g` (bijectivity, not mere injectivity, is essential: the
tensor product is not left exact, but stalks of locally bijective maps are
isomorphisms and isomorphisms tensor to isomorphisms — no flatness). Stalkwise/
filtered-colimit argument; registered WIP (board v10.69; decompose on fork per
v10.24). -/
lemma isLocallyInjective_tensorHom (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
    [Presheaf.IsLocallyInjective J ((toPresheaf _).map f)]
    [Presheaf.IsLocallySurjective J ((toPresheaf _).map f)]
    [Presheaf.IsLocallyInjective J ((toPresheaf _).map g)]
    [Presheaf.IsLocallySurjective J ((toPresheaf _).map g)] :
    Presheaf.IsLocallyInjective J ((toPresheaf _).map (f ⊗ₘ g)) := by
  sorry

/-- **([W-MONO-inj])** Precomposition with the tensor of locally surjective morphisms
is injective on morphisms into a presheaf of modules whose underlying presheaf is a
sheaf: two maps out of the tensor agreeing after `f ⊗ₘ g` agree on simple tensors
locally, hence agree by separatedness. -/
theorem tensorHom_precomp_injective (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
    [Presheaf.IsLocallySurjective J ((toPresheaf _).map f)]
    [Presheaf.IsLocallySurjective J ((toPresheaf _).map g)]
    {P : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}
    (hP : Presheaf.IsSheaf J P.presheaf) :
    Function.Injective (fun (ψ : M₂ ⊗ N₂ ⟶ P) => (f ⊗ₘ g) ≫ ψ) := by
  intro ψ₁ ψ₂ h
  refine hom_ext (fun U => ?_)
  ext t
  induction t using TensorProduct.induction_on with
  | zero => erw [map_zero, map_zero]
  | tmul m n =>
      have key : ∀ (ψ : M₂ ⊗ N₂ ⟶ P) {V : C} (p : V ⟶ U.unop)
          (a : M₁.obj (Opposite.op V)) (b : N₁.obj (Opposite.op V))
          (ha : f.app (Opposite.op V) a = M₂.map p.op m)
          (hb : g.app (Opposite.op V) b = N₂.map p.op n),
          P.map p.op (ψ.app U (m ⊗ₜ n)) =
            ((f ⊗ₘ g) ≫ ψ).app (Opposite.op V) (a ⊗ₜ b) := by
        intro ψ V p a b ha hb
        have hnat : ∀ x, P.map p.op (ψ.app U x) =
            ψ.app (Opposite.op V) ((M₂ ⊗ N₂).map p.op x) :=
          fun x => (CategoryTheory.congr_fun (ψ.naturality p.op) x).symm
        rw [hnat]
        have hres : (M₂ ⊗ N₂).map p.op (m ⊗ₜ n) =
            (f ⊗ₘ g).app (Opposite.op V) (a ⊗ₜ b) := by
          erw [Monoidal.tensorObj_map_tmul, Monoidal.tensorHom_app,
            ModuleCat.MonoidalCategory.tensorHom_tmul]
          rw [ha, hb]
          rfl
        rw [hres]
        rfl
      obtain ⟨U⟩ := U
      apply hP.isSeparated _ _ (J.intersection_covering
        (Presheaf.imageSieve_mem J ((toPresheaf _).map f) m)
        (Presheaf.imageSieve_mem J ((toPresheaf _).map g) n))
      rintro V p ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      have ha' : f.app (Opposite.op V) a = M₂.map p.op m := ha
      have hb' : g.app (Opposite.op V) b = N₂.map p.op n := hb
      exact (key ψ₁ p a b ha' hb').trans ((congrArg (fun φ => φ.app (Opposite.op V)
        (a ⊗ₜ b)) h).trans (key ψ₂ p a b ha' hb').symm)
  | add s t hs ht =>
      erw [map_add, map_add]
      rw [hs, ht]

end Tensor

end PresheafOfModules

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

section Glue

/- The gluing construction is stated over a small site (`C : Type u`, `Category.{u}`,
modules in `.{u}`) so that the Type-level amalgamation bridge
(`isSheaf_iff_isSheaf_forget`, which needs `forget` to land in `Type (max v₁ u₁)`)
applies — exactly the shape of GAP-1's consumer, the small Zariski site of a scheme. -/

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  {M₁ M₂ N₁ N₂ : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}
  (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
  [Presheaf.IsLocallyInjective J ((toPresheaf _).map f)]
  [Presheaf.IsLocallySurjective J ((toPresheaf _).map f)]
  [Presheaf.IsLocallyInjective J ((toPresheaf _).map g)]
  [Presheaf.IsLocallySurjective J ((toPresheaf _).map g)]
  {P : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}
  (hP : Presheaf.IsSheaf J P.presheaf) (χ : M₁ ⊗ N₁ ⟶ P)

include hP in
/-- Any two preimage-pairs of the same sections give the same `χ`-value: locally the
pairs agree (local injectivity), so the values agree locally, so they agree
(separatedness). The workhorse of the [W-MONO-glue] construction. -/
private lemma chi_app_congr {V : C} (a a' : M₁.obj (Opposite.op V))
    (b b' : N₁.obj (Opposite.op V))
    (hfa : f.app (Opposite.op V) a = f.app (Opposite.op V) a')
    (hgb : g.app (Opposite.op V) b = g.app (Opposite.op V) b') :
    χ.app (Opposite.op V) (a ⊗ₜ b) = χ.app (Opposite.op V) (a' ⊗ₜ b') := by
  have hfa' : ((toPresheaf _).map f).app (Opposite.op V) a =
      ((toPresheaf _).map f).app (Opposite.op V) a' := hfa
  have hgb' : ((toPresheaf _).map g).app (Opposite.op V) b =
      ((toPresheaf _).map g).app (Opposite.op V) b' := hgb
  apply hP.isSeparated _ _ (J.intersection_covering
    (Presheaf.equalizerSieve_mem J ((toPresheaf _).map f) a a' hfa')
    (Presheaf.equalizerSieve_mem J ((toPresheaf _).map g) b b' hgb'))
  rintro W q ⟨hqa, hqb⟩
  have hnat : ∀ x : ((M₁ ⊗ N₁).obj (Opposite.op V) : Type u),
      P.presheaf.map q.op (χ.app (Opposite.op V) x) =
        χ.app (Opposite.op W) ((M₁ ⊗ N₁).map q.op x) :=
    fun x => (CategoryTheory.congr_fun (χ.naturality q.op) x).symm
  erw [hnat, hnat]
  congr 1
  erw [Monoidal.tensorObj_map_tmul, Monoidal.tensorObj_map_tmul]
  have hqa' : M₁.map q.op a = M₁.map q.op a' := hqa
  have hqb' : N₁.map q.op b = N₁.map q.op b' := hqb
  rw [hqa', hqb']

/-- The defining property of the glued pairing section at `(m, n)`: it restricts to
the `χ`-value of every local preimage-pair. -/
private def IsPairingSection {U : Cᵒᵖ} (m : M₂.obj U) (n : N₂.obj U)
    (s : P.obj U) : Prop :=
  ∀ ⦃V : C⦄ (p : V ⟶ U.unop) (a : M₁.obj (Opposite.op V)) (b : N₁.obj (Opposite.op V)),
    f.app (Opposite.op V) a = M₂.map p.op m → g.app (Opposite.op V) b = N₂.map p.op n →
    P.map p.op s = χ.app (Opposite.op V) (a ⊗ₜ b)

include hP in
/-- Existence and uniqueness of the glued pairing section: amalgamate the `χ`-values
of chosen local preimage-pairs over the intersection of the two image sieves
(compatibility and the defining property both reduce to `chi_app_congr`). -/
private lemma existsUnique_isPairingSection {U : Cᵒᵖ} (m : M₂.obj U) (n : N₂.obj U) :
    ∃! s : P.obj U, IsPairingSection f g χ m n s := by
  have hT : Presieve.IsSheaf J (P.presheaf ⋙ forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget J P.presheaf (forget _)).mp hP)
  have hSv : (Presheaf.imageSieve ((toPresheaf _).map f) m ⊓
      Presheaf.imageSieve ((toPresheaf _).map g) n) ∈ J U.unop :=
    J.intersection_covering
      (Presheaf.imageSieve_mem J ((toPresheaf _).map f) m)
      (Presheaf.imageSieve_mem J ((toPresheaf _).map g) n)
  set Sv := Presheaf.imageSieve ((toPresheaf _).map f) m ⊓
      Presheaf.imageSieve ((toPresheaf _).map g) n with hSvdef
  -- the choice family of χ-values
  set x : Presieve.FamilyOfElements (P.presheaf ⋙ forget AddCommGrpCat) Sv.arrows :=
    fun V p hp => χ.app (Opposite.op V) (hp.1.choose ⊗ₜ hp.2.choose) with hxdef
  have hchoice : ∀ {V : C} (p : V ⟶ U.unop) (hp : Sv.arrows p),
      f.app (Opposite.op V) hp.1.choose = M₂.map p.op m ∧
        g.app (Opposite.op V) hp.2.choose = N₂.map p.op n :=
    fun p hp => ⟨hp.1.choose_spec, hp.2.choose_spec⟩
  -- naturality helper at Type level
  have hnat : ∀ {V W : C} (q : W ⟶ V) (t : (M₁ ⊗ N₁).obj (Opposite.op V)),
      P.presheaf.map q.op (χ.app (Opposite.op V) t) =
        χ.app (Opposite.op W) ((M₁ ⊗ N₁).map q.op t) :=
    fun q t => (CategoryTheory.congr_fun (χ.naturality q.op) t).symm
  -- restriction of a preimage-pair is a preimage-pair
  have hres : ∀ {V W : C} (q : W ⟶ V) (p : V ⟶ U.unop)
      (a : M₁.obj (Opposite.op V)) (b : N₁.obj (Opposite.op V))
      (ha : f.app (Opposite.op V) a = M₂.map p.op m)
      (hb : g.app (Opposite.op V) b = N₂.map p.op n),
      f.app (Opposite.op W) (M₁.map q.op a) = M₂.map (q ≫ p).op m ∧
        g.app (Opposite.op W) (N₁.map q.op b) = N₂.map (q ≫ p).op n := by
    intro V W q p a b ha hb
    constructor
    · have h1 : f.app (Opposite.op W) (M₁.map q.op a) =
          M₂.map q.op (f.app (Opposite.op V) a) :=
        (CategoryTheory.congr_fun (f.naturality q.op) a)
      rw [h1, ha]
      exact (show M₂.presheaf.map (q ≫ p).op m =
          M₂.presheaf.map q.op (M₂.presheaf.map p.op m) by
        rw [op_comp, M₂.presheaf.map_comp]
        rfl).symm
    · have h1 : g.app (Opposite.op W) (N₁.map q.op b) =
          N₂.map q.op (g.app (Opposite.op V) b) :=
        (CategoryTheory.congr_fun (g.naturality q.op) b)
      rw [h1, hb]
      exact (show N₂.presheaf.map (q ≫ p).op n =
          N₂.presheaf.map q.op (N₂.presheaf.map p.op n) by
        rw [op_comp, N₂.presheaf.map_comp]
        rfl).symm
  -- value of χ on restricted pairs, as needed below
  have hvalue : ∀ {V W : C} (q : W ⟶ V) (a : M₁.obj (Opposite.op V))
      (b : N₁.obj (Opposite.op V)),
      P.presheaf.map q.op (χ.app (Opposite.op V) (a ⊗ₜ b)) =
        χ.app (Opposite.op W) (M₁.map q.op a ⊗ₜ N₁.map q.op b) := by
    intro V W q a b
    rw [hnat]
    exact congrArg (χ.app (Opposite.op W)) (by erw [Monoidal.tensorObj_map_tmul]; rfl)
  -- compatibility of the choice family
  have hx : x.Compatible := by
    intro V₁ V₂ W g₁ g₂ p₁ p₂ h₁ h₂ hcomm
    rw [hxdef]
    dsimp only
    erw [hvalue, hvalue]
    have hp₁ := hchoice p₁ h₁
    have hp₂ := hchoice p₂ h₂
    have hr₁ := hres g₁ p₁ _ _ hp₁.1 hp₁.2
    have hr₂ := hres g₂ p₂ _ _ hp₂.1 hp₂.2
    exact chi_app_congr f g hP χ _ _ _ _
      (hr₁.1.trans (by rw [hcomm]; exact hr₂.1.symm))
      (hr₁.2.trans (by rw [hcomm]; exact hr₂.2.symm))
  -- the amalgam
  refine ⟨(hT Sv hSv).amalgamate x hx, ?_, ?_⟩
  · intro V p a b ha hb
    apply hP.isSeparated _ _ (J.pullback_stable p hSv)
    intro W q hq
    have hglue := (hT Sv hSv).valid_glue hx (q ≫ p) hq
    have hcomp : P.presheaf.map q.op (P.presheaf.map p.op ((hT Sv hSv).amalgamate x hx)) =
        P.presheaf.map (q ≫ p).op ((hT Sv hSv).amalgamate x hx) := by
      rw [op_comp, P.presheaf.map_comp]
      rfl
    erw [hcomp, hglue, hxdef]
    dsimp only
    erw [hvalue]
    have hc := hchoice (q ≫ p) hq
    have hr := hres q p a b ha hb
    exact chi_app_congr f g hP χ _ _ _ _ (hc.1.trans hr.1.symm) (hc.2.trans hr.2.symm)
  · intro s hs
    apply hP.isSeparated _ _ hSv
    intro V p hp
    have hc := hchoice p hp
    have h1 := hs p _ _ hc.1 hc.2
    have h2 := (hT Sv hSv).valid_glue hx p hp
    erw [h1, h2, hxdef]

end Glue

end PresheafOfModules

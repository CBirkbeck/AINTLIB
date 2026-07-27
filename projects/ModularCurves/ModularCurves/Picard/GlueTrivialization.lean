/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.PicComparison
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Gluing a trivialization from cover-local generating sections

The workhorse behind the relative theorem of the square. An `𝒪ₓ`-module `M` is trivial as
soon as it admits **cover-local generating sections that agree on overlaps**:

* `globalSectionHom` — a global section `m` of `M` as a map `𝒪ₓ ⟶ M`, `1 ↦ m`;
* `nonempty_unitObj_iso_of_glue` — if the `m i` agree on overlaps and each generates `M`
  over every open inside `U i`, then `𝒪ₓ ≅ M`.

The point of gluing *sections* rather than *isomorphisms* is that sections glue by the sheaf
axiom for `M` itself (`TopCat.Sheaf.existsUnique_gluing`), whereas gluing isomorphisms of
sheaves of modules would need descent data. The glued global morphism is then tested by
`isIso_of_bijective_app_on_cover`, i.e. the "bijective on opens inside a cover member"
criterion.

In the intended application `M` is the difference bundle of a theorem-of-the-square identity
on `E ×_S T`; the overlap agreement is *forced*, not checked, because the local sections are
normalized along the zero section and `ModularCurves.eq_one_of_pullback_eq_one` says a unit
which is `1` along the zero section is `1`.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)

/-- The restrictions of a global section form a compatible family. -/
noncomputable def globalSectionFamily (m : Γ(M, ⊤)) : M.val.sections :=
  PresheafOfModules.sectionsMk
    (fun V => M.val.map (homOfLE (le_top : V.unop ≤ ⊤)).op m)
    (fun {V W} f => by
      have harr : (homOfLE (le_top : V.unop ≤ ⊤)).op ≫ f
          = (homOfLE (le_top : W.unop ≤ ⊤)).op := Subsingleton.elim _ _
      rw [← PresheafOfModules.map_comp_apply, harr])

/-- Multiplication by a global section: the map `𝒪ₓ ⟶ M` sending `1` to `m`. -/
noncomputable def globalSectionHom (m : Γ(M, ⊤)) : unitObj X ⟶ M :=
  M.unitHomEquiv.symm (globalSectionFamily M m)

@[simp] theorem globalSectionHom_app_one (m : Γ(M, ⊤)) (W : X.Opens) :
    (globalSectionHom M m).app W (1 : Γ(X, W)) = M.val.map (homOfLE le_top).op m := by
  show (M.unitHomEquiv (globalSectionHom M m)).val (op W) = _
  rw [globalSectionHom, Equiv.apply_symm_apply]
  rfl

/-- **Sections glue.** The sheaf axiom for `M`, in the concrete form the trivialization
argument consumes: cover-local sections agreeing on overlaps come from a global one. -/
theorem exists_globalSection_restrict {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (m : ∀ i, Γ(M, U i))
    (hcompat : ∀ i j, M.presheaf.map (Opens.infLELeft (U i) (U j)).op (m i)
        = M.presheaf.map (Opens.infLERight (U i) (U j)).op (m j)) :
    ∃ m₀ : Γ(M, ⊤), ∀ i, M.presheaf.map (homOfLE le_top).op m₀ = m i := by
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (F := (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X)) U ⊤
    (fun _ => homOfLE le_top) (by rw [hU]) m hcompat
  exact ⟨s, hs⟩

/-- **The trivialization criterion.** A global section that generates `M` over every open
inside a member of a cover trivializes `M`. -/
theorem nonempty_unitObj_iso_of_globalSection {ι : Type u} (U : ι → X.Opens)
    (hU : iSup U = ⊤) (m : Γ(M, ⊤))
    (hbij : ∀ (i : ι) (W : X.Opens), W ≤ U i →
      Function.Bijective ((globalSectionHom M m).app W)) :
    Nonempty (unitObj X ≅ M) := by
  haveI := isIso_of_bijective_app_on_cover (globalSectionHom M m) U hU hbij
  exact ⟨asIso (globalSectionHom M m)⟩

theorem globalSectionHom_app (m : Γ(M, ⊤)) (W : X.Opens) (r : Γ(X, W)) :
    (globalSectionHom M m).app W r = r • M.presheaf.map (homOfLE le_top).op m := by
  have h1 : (globalSectionHom M m).app W (r • (1 : Γ(X, W)))
      = r • (globalSectionHom M m).app W (1 : Γ(X, W)) := Hom.app_smul _ r _
  have h2 : (r • (1 : Γ(X, W))) = r := by
    show r * 1 = r
    exact mul_one r
  rw [h2, globalSectionHom_app_one] at h1
  exact h1

/-- **(DESCENT, module form)** An `𝒪ₓ`-module is trivial as soon as it admits cover-local
generating sections that agree on overlaps.

The sections glue by the sheaf axiom; the glued global section then generates everywhere,
and `isIso_of_bijective_app_on_cover` upgrades that to an isomorphism `𝒪ₓ ≅ M`. -/
theorem nonempty_unitObj_iso_of_glue {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (m : ∀ i, Γ(M, U i))
    (hcompat : ∀ i j, M.presheaf.map (Opens.infLELeft (U i) (U j)).op (m i)
        = M.presheaf.map (Opens.infLERight (U i) (U j)).op (m j))
    (hbij : ∀ (i : ι) (W : X.Opens) (hW : W ≤ U i),
      Function.Bijective (fun r : Γ(X, W) => r • M.presheaf.map (homOfLE hW).op (m i))) :
    Nonempty (unitObj X ≅ M) := by
  obtain ⟨m₀, hm₀⟩ := exists_globalSection_restrict M U hU m hcompat
  refine nonempty_unitObj_iso_of_globalSection M U hU m₀ (fun i W hW => ?_)
  have hres : M.presheaf.map (homOfLE le_top).op m₀
      = M.presheaf.map (homOfLE hW).op (m i) := by
    rw [← hm₀ i, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact congrArg (fun φ => (ConcreteCategory.hom (M.presheaf.map φ)) m₀)
      (Subsingleton.elim _ _)
  have heq : (fun r : Γ(X, W) => r • M.presheaf.map (homOfLE hW).op (m i))
      = fun r : Γ(X, W) => (globalSectionHom M m₀).app W r := by
    funext r
    rw [globalSectionHom_app, hres]
  have hb := hbij i W hW
  rw [heq] at hb
  exact hb

/-! ## Passing to `Pic`

The descent theorems above produce a `Nonempty (𝒪ₓ ≅ M)`. Every consumer needs the
consequence *in the group* `Pic X = (Skeleton X.Modules)ˣ`, which is what these two lemmas
supply. -/

/-- A trivial module has trivial class: `Skeleton` identifies isomorphic objects. -/
theorem IsInvertible.unit_eq_one {M : X.Modules} (hM : IsInvertible M)
    (h : Nonempty (unitObj X ≅ M)) :
    letI := Modules.monoidalCategory X
    letI := Modules.symmetricCategory X
    hM.isUnit_toSkeleton.unit = 1 := by
  letI := Modules.monoidalCategory X
  letI := Modules.symmetricCategory X
  obtain ⟨e⟩ := h
  obtain ⟨eU⟩ := nonempty_unitObj_iso_unit (X := X)
  refine Units.ext ?_
  show toSkeleton M = (1 : Skeleton X.Modules)
  rw [Skeleton.one_eq]
  exact toSkeleton_eq_toSkeleton_iff.mpr ⟨e.symm ≪≫ eU⟩

/-- Isomorphic invertible modules have the same class in `Pic`. -/
theorem IsInvertible.unit_eq_unit_of_iso {M N : X.Modules} (hM : IsInvertible M)
    (hN : IsInvertible N) (h : Nonempty (M ≅ N)) :
    letI := Modules.monoidalCategory X
    letI := Modules.symmetricCategory X
    hM.isUnit_toSkeleton.unit = hN.isUnit_toSkeleton.unit := by
  letI := Modules.monoidalCategory X
  letI := Modules.symmetricCategory X
  exact Units.ext (toSkeleton_eq_toSkeleton_iff.mpr h)

end AlgebraicGeometry.Scheme.Modules

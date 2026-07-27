/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.RingTheory.Flat.Basic
import Common
import ModularCurves.ForMathlib.SchemeModuleBaseCechBasic

/-!
# Flat terms in the base-linear Cech complex

A degree of the base-linear Cech complex is flat whenever all of its
intersection-section factors are flat, via `Module.Flat.pi` (finite products of flat
modules are flat) from the shared `Common` library.
-/

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- One intersection-section factor in a degree of the base-linear Cech
complex. -/
abbrev baseCechFactor {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) {ι : Type u}
    (U : ι → X.Opens) (n : ℕ) (i : Fin (n + 1) → ι) :=
  (baseModulePresheaf π M).obj (op (∏ᶜ fun k : Fin (n + 1) => U (i k)))

/-- A degree of the base-linear Cech complex is the concrete dependent
product of its intersection-section factors. -/
def baseCechXIsoPi {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) {ι : Type u}
    (U : ι → X.Opens) (n : ℕ) : (baseCechComplex π M U).X n ≅
      ModuleCat.of Γ(S, (⊤ : S.Opens))
        (∀ i : Fin (n + 1) → ι, baseCechFactor π M U n i) :=
  ModuleCat.piIsoPi _

/-- A degree of the base-linear Cech complex is flat over the base ring if
all of its intersection-section factors are flat. -/
theorem baseCechComplex_X_flat_of_factors {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) {ι : Type u} [Finite ι] (U : ι → X.Opens) (n : ℕ)
    (hflat : ∀ i : Fin (n + 1) → ι,
      Module.Flat Γ(S, (⊤ : S.Opens)) (baseCechFactor π M U n i)) :
    Module.Flat Γ(S, (⊤ : S.Opens)) ((baseCechComplex π M U).X n) := by
  letI := hflat
  exact Module.Flat.of_linearEquiv (baseCechXIsoPi π M U n).toLinearEquiv

end

end AlgebraicGeometry.Scheme.Modules

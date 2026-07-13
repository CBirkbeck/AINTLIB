import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.RingTheory.Flat.Basic
import ModularCurves.ForMathlib.SchemeModuleBaseCechBasic

/-!
# Flat terms in the base-linear Cech complex

Finite products of flat modules are flat. Consequently, a degree of the
base-linear Cech complex is flat whenever all of its intersection-section
factors are flat.
-/

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Opposite
  TopologicalSpace

universe u v w

namespace Module.Flat

/-- A finite dependent product of flat modules is flat. (An *arbitrary* product of
flat modules need not be flat, so the `Finite` hypothesis is essential — mathlib has the
`directSum`/`dfinsupp`/`finsupp` instances but no `Pi` one.) -/
instance pi
    {R : Type u} [CommSemiring R] {ι : Type v} [Finite ι]
    {M : ι → Type w} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] [∀ i, Module.Flat R (M i)] :
    Module.Flat R (∀ i, M i) := by
  classical
  letI := Fintype.ofFinite ι
  exact Module.Flat.of_linearEquiv
    (DFinsupp.linearEquivFunOnFintype (R := R) (M := M)).symm

end Module.Flat

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- One intersection-section factor in a degree of the base-linear Cech
complex. -/
abbrev baseCechFactor
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : Fin (n + 1) → ι) :=
  (baseModulePresheaf π M).obj
    (op (∏ᶜ fun k : Fin (n + 1) => U (i k)))

/-- A degree of the base-linear Cech complex is the concrete dependent
product of its intersection-section factors. -/
noncomputable def baseCechXIsoPi
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (baseCechComplex π M U).X n ≅
      ModuleCat.of Γ(S, (⊤ : S.Opens))
        (∀ i : Fin (n + 1) → ι, baseCechFactor π M U n i) := by
  change (∏ᶜ fun i : Fin (n + 1) → ι =>
      baseCechFactor π M U n i) ≅ _
  exact ModuleCat.piIsoPi _

/-- A degree of the base-linear Cech complex is flat over the base ring if
all of its intersection-section factors are flat. -/
theorem baseCechComplex_X_flat_of_factors
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (n : ℕ)
    (hflat : ∀ i : Fin (n + 1) → ι,
      Module.Flat Γ(S, (⊤ : S.Opens)) (baseCechFactor π M U n i)) :
    Module.Flat Γ(S, (⊤ : S.Opens)) ((baseCechComplex π M U).X n) := by
  haveI : ∀ i : Fin (n + 1) → ι,
      Module.Flat Γ(S, (⊤ : S.Opens)) (baseCechFactor π M U n i) := hflat
  exact Module.Flat.of_linearEquiv
    (baseCechXIsoPi π M U n).toLinearEquiv

end

end AlgebraicGeometry.Scheme.Modules

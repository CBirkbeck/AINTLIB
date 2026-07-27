import Common.Analysis.DirichletBounds
import Mathlib.RingTheory.Flat.Basic

/-!
# AINTLIB.Common

Shared lemmas refactored out of the consolidated projects during deduplication.

As cross-project cleanup finds results that genuinely belong to more than one project
(shared cyclotomic, modular-forms, valuation lemmas, …), they get promoted here and
consumers are rewired to it.

`Common` is also published as a standalone package on the same mathlib so the origin
repos can `require` it and reuse these results on the development side — see
`docs/superpowers/specs/2026-06-14-ant-consolidation-monorepo-design.md`.
-/

/-- Finite products of flat modules are flat. (An *arbitrary* product of flat modules need
not be flat, so `Finite ι` is essential; mathlib has the `directSum`/`dfinsupp`/`finsupp`
instances but no `Pi` one.) This follows from the equivalence `(∀ i, M i) ≃ (⨁ i, M i)` for
finite `ι` and `Module.Flat.directSum`.

Promoted to `Common` during cross-project dedup — previously duplicated in AdicSpaces
`FlatnessResults` and ModularCurves `ForMathlib/SchemeModuleBaseCechFlat`. -/
instance Module.Flat.pi {R : Type*} [CommSemiring R] {ι : Type*} [Finite ι]
    {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Flat R (M i)] : Module.Flat R (∀ i, M i) := by
  cases nonempty_fintype ι
  exact Module.Flat.of_linearEquiv
    (DirectSum.linearEquivFunOnFintype R ι M).symm

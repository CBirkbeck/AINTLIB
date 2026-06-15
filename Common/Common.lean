/-!
# AINTLIB.Common

Shared lemmas refactored out of the consolidated projects during deduplication.

This library is intentionally empty for now. As cross-project cleanup finds results
that genuinely belong to more than one project (shared cyclotomic, modular-forms,
valuation lemmas, …), they get promoted here and consumers are rewired to it.

`Common` is also published as a standalone package on the same mathlib so the origin
repos can `require` it and reuse these results on the development side — see
`docs/superpowers/specs/2026-06-14-ant-consolidation-monorepo-design.md`.
-/

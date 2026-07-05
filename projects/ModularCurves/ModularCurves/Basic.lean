import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Modular curves — foundations

Entry point for the AINTLIB modular-curves formalisation. The goal of the project is to
build the theory of the modular curves

* `Y(Γ) = Γ \ ℍ`  (the open modular curve), and
* `X(Γ)`          (its compactification, adding the cusps),

for congruence subgroups `Γ ≤ SL₂(ℤ)` — as Riemann surfaces first, and eventually as
algebraic curves / moduli spaces of elliptic curves with level structure.

See `projects/ModularCurves/docs/` for the source bibliography and the project plan.

## Existing infrastructure we build on (reuse — do not re-prove)

* `Mathlib.Analysis.Complex.UpperHalfPlane.*` — the upper half plane `ℍ` and the Möbius action.
* `Mathlib.NumberTheory.Modular` — the `SL(2, ℤ)` action and its standard fundamental domain.
* `Mathlib.NumberTheory.ModularForms.CongruenceSubgroups` — `Γ(N)`, `Γ₀(N)`, `Γ₁(N)`.
* `Mathlib.NumberTheory.ModularForms.*` — slash actions, (cusp) forms, cusps, `q`-expansions.
* In-repo: `projects/LeanModularForms/` and `projects/HasseWeil/` (see `docs/sources.md`).

This file is intentionally a stub: it fixes the module root and pins the core imports. Real
development happens in sibling files under `ModularCurves/`.
-/

namespace ModularCurves

end ModularCurves

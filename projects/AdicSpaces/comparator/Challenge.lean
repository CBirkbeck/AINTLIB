/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.FiniteJetMain
import «Adic spaces».FJP.FiniteJetChart

/-!
# Comparator challenge — the FJP headline theorems

The statements that `Solution.lean` must prove, for
[`leanprover/comparator`](https://github.com/leanprover/comparator).

Every theorem here is `sorry`. Comparator checks that the same-named theorems in
`Solution.lean` prove *these* statements, are accepted by the Lean kernel, and use no axioms
beyond the permitted three. That is a stronger guarantee than `#print axioms`: the statement
being proved is pinned by this file rather than taken on trust from the solution.

The challenge set is [FJP] Theorem 1.3 — the paper's headline result, all five conclusions —
plus [FJP] Corollary 3.2, the non-uniformity of the rational localization that Theorem 1.3's
last clause rests on.

The binders are written with `variable`, exactly as the library states them, so that the
challenge and the solution elaborate to the same type without either restating the other.

**This file must not be imported by the library**: it is full of `sorry`. It is reachable only
as its own `lean_lib`, which is deliberately absent from `defaultTargets`.
-/

open FiniteJet ValuationSpectrum TopologicalRing

universe u

variable (F : Type u) [Field F]

/-- **[FJP] Theorem 1.3 (sheafy)**: the pinching algebra `𝓐` is sheafy. -/
theorem fjp_1_3_isSheafy : IsSheafy (JetA F) := sorry

/-- **[FJP] Theorem 1.3 (uniform)**: `𝓐` is uniform. -/
theorem fjp_1_3_isUniform : IsUniform (JetA F) := sorry

/-- **[FJP] Theorem 1.3 (domain)**: `𝓐` is an integral domain. -/
theorem fjp_1_3_isDomain : IsDomain (JetA F) := sorry

/-- **[FJP] Theorem 1.3 (nonnoetherian)**: `𝓐` is not noetherian. -/
theorem fjp_1_3_not_isNoetherianRing : ¬ IsNoetherianRing (JetA F) := sorry

/-- **[FJP] Theorem 1.3 (not stably uniform)**: `𝓐` is not stably uniform. -/
theorem fjp_1_3_not_isStablyUniform : ¬ IsStablyUniform (JetA F) := sorry

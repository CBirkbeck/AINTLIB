/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.FiniteJetRings
import «Adic spaces».Uniform

/-!
# Comparator challenge: [FJP] Theorem 1.3

The five conclusions of the paper's headline theorem, stated with `sorry` proofs, for
verification by [leanprover/comparator](https://github.com/leanprover/comparator) against the
real proofs in `«Adic spaces».FJP.FiniteJetMain` (the solution module): identical statements,
axiom budget `[propext, Quot.sound, Classical.choice]`, and kernel acceptance.

This module imports only the **definition layer** — `FJP.FiniteJetRings` (which defines
`JetA` and carries its `IsHuberRing` / `PlusSubring` / `CompleteSpace` /
`IsRingOfIntegralElements` instances) and `Uniform` (which defines `IsUniform` /
`IsStablyUniform`). Their combined import closure provably does not reach any of the
four modules that *prove* these statements (`FiniteJetMain`, `FiniteJetSheafTransfer`,
`FiniteJetChart`, `FiniteJetUniformDomain`), so the statements here are independent
restatements rather than echoes of the proofs being judged.

It is intentionally excluded from the default build: the `«Adic spaces»` `lean_lib` declares
no `globs`, so only its root module is a build target and nothing imports this file.
-/

namespace FiniteJet

variable (F : Type*) [Field F]

/-- **[FJP] Theorem 1.3 (sheafy)**: `(𝓐, 𝓐°)` is sheafy. -/
theorem finiteJet_isSheafy : ValuationSpectrum.IsSheafy (JetA F) := sorry

/-- **[FJP] Theorem 1.3 (uniform)**: 𝓐 is uniform. -/
theorem finiteJet_isUniform : TopologicalRing.IsUniform (JetA F) := sorry

/-- **[FJP] Theorem 1.3 (domain)**: 𝓐 is an integral domain. -/
theorem finiteJet_isDomain : IsDomain (JetA F) := sorry

/-- **[FJP] Theorem 1.3 (nonnoetherian)**: 𝓐 is not noetherian. -/
theorem finiteJet_not_noetherian : ¬ IsNoetherianRing (JetA F) := sorry

/-- **[FJP] Theorem 1.3 (not stably uniform)**: 𝓐 is not stably uniform. -/
theorem finiteJet_not_stablyUniform : ¬ TopologicalRing.IsStablyUniform (JetA F) := sorry

end FiniteJet

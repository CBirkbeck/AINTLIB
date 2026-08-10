/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.FiniteJetRings
import «Adic spaces».Uniform

/-!
# Comparator challenge: [FJP] Theorem 1.3

The five conclusions of the paper's headline theorem (`thm:main` of *Uniform sheafy Tate
domains that are not stably uniform*; Theorem 1.3 in the revision the library's docstrings
cite), stated with `sorry` proofs, for verification by
[leanprover/comparator](https://github.com/leanprover/comparator) against `Solution.lean`.

This module imports only the **definition layer** — `FJP.FiniteJetRings` (defines `JetA` and
carries its instances) and `Uniform` (defines `IsUniform` / `IsStablyUniform`). Their combined
import closure contains no `FJP` module beyond `FiniteJetRings` and `RestrictedLaurent` — in
particular none of the modules that *prove* these statements (`FiniteJetMain`,
`FiniteJetSheafyEndpoints`, `FiniteJetSheafTransfer`, `FiniteJetChart`,
`FiniteJetUniformDomain`, `FiniteJetNoetherianVertices`), so the statements here are
independent restatements rather than echoes of the proofs being judged.

The names are deliberately *not* the library's: comparator builds the solution module in a
sandbox, so the solution must be a small file that forwards to the library, and it could not
re-declare `FiniteJet.finiteJet_isSheafy` without clashing with the import that provides it.

Excluded from the default build: the `«Adic spaces»` `lean_lib` declares no `globs`, so only its
root module is a build target and nothing imports this file.
-/

open FiniteJet ValuationSpectrum TopologicalRing

universe u

variable (F : Type u) [Field F]

/-- **[FJP] Theorem 1.3 (sheafy)**: `(𝓐, 𝓐°)` is sheafy. -/
theorem fjp_1_3_isSheafy : IsSheafy (JetA F) := sorry

/-- **[FJP] Theorem 1.3 (uniform)**: 𝓐 is uniform. -/
theorem fjp_1_3_isUniform : IsUniform (JetA F) := sorry

/-- **[FJP] Theorem 1.3 (domain)**: 𝓐 is an integral domain. -/
theorem fjp_1_3_isDomain : IsDomain (JetA F) := sorry

/-- **[FJP] Theorem 1.3 (nonnoetherian)**: 𝓐 is not noetherian. -/
theorem fjp_1_3_not_isNoetherianRing : ¬ IsNoetherianRing (JetA F) := sorry

/-- **[FJP] Theorem 1.3 (not stably uniform)**: 𝓐 is not stably uniform. -/
theorem fjp_1_3_not_isStablyUniform : ¬ IsStablyUniform (JetA F) := sorry

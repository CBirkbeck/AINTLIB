/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WP.Algebra
import «Adic spaces».SheafyRing
import «Adic spaces».Uniform

/-!
# Comparator challenge: [WP] Theorem 8.1 (the weighted-parity example)

The seven conclusions of the paper's second headline theorem (Theorem 8.1 of the
current revision; the library's docstrings cite it as `[WP] thm 6.2`, the revision
they were written against), stated with `sorry` proofs, for verification by
[leanprover/comparator](https://github.com/leanprover/comparator) against the real
proofs in `«Adic spaces».WP.Main` (via `Comparator/WPSolution.lean`): identical
statements, axiom budget `[propext, Quot.sound, Classical.choice]`, and kernel
acceptance.

This module imports only the **definition layer** — `WP.Algebra` (defines the
weighted-parity algebra `WPA` and carries its `CompleteSpace` / `IsHuberRing` /
`IsTateRing` / `PlusSubring` instances), `SheafyRing` (defines `IsSheafyComplete`)
and `Uniform` (defines `IsUniform` / `IsStablyUniform`). Its import closure contains
**none** of the modules that prove these statements (`WP.Main`, `WP.UniformDomain`,
`WP.Nonnoetherian`, `WP.Sheafy`, `WP.Chart`, `WP.Reduced`, the `WP.HeadReduced*` /
`WP.Graph*` chain), so the statements here are independent restatements rather than
echoes of the proofs being judged.

The paper's weight `w = id` is spelled `fun k => k` here: the library's abbreviation
`WeightedParity.idWeight` lives in the proving layer (`WP.Main`), so naming it would
pull that module into the trusted side. The statements are over the layer-2 base
(`[IsDiscreteValuationRing 𝒪[K]]`), where the paper's uniformizer is chosen rather
than carried as data.

Intentionally excluded from the default build: the `«Adic spaces»` `lean_lib`
declares no `globs`, so only its root module is a build target and nothing imports
this file.
-/

open WeightedParity ValuationSpectrum TopologicalRing
open scoped NormedField Valued

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable [IsDiscreteValuationRing 𝒪[K]]

/-- **[WP] Theorem 8.1 (uniform)**: `𝒜` is uniform. -/
theorem wp_8_1_isUniform : IsUniform (WPA K (fun k => k)) := sorry

/-- **[WP] Theorem 8.1 (domain)**: `𝒜` is an integral domain. -/
theorem wp_8_1_isDomain : IsDomain (WPA K (fun k => k)) := sorry

/-- **[WP] Theorem 8.1 (nonnoetherian)**: `𝒜` is not noetherian. -/
theorem wp_8_1_not_isNoetherianRing : ¬ IsNoetherianRing (WPA K (fun k => k)) := sorry

/-- **[WP] Theorem 8.1 (`𝒜° = 𝒜₀`)**: the power-bounded subring is the unit ball. -/
theorem wp_8_1_powerBounded_eq_unitBall :
    powerBoundedSubring (WPA K (fun k => k)) =
      (FiniteJet.unitBall (WPA K (fun k => k)) : Set (WPA K (fun k => k))) := sorry

/-- **[WP] Theorem 8.1 (sheafy)**: `(𝒜, 𝒜°)` is sheafy — every valid pair. -/
theorem wp_8_1_isSheafyComplete : IsSheafyComplete (WPA K (fun k => k)) := sorry

/-- **[WP] Theorem 8.1 (strongly sheafy)**: every shifted-weight algebra
`𝒜⟨V₁,…,Vₛ⟩` is sheafy. -/
theorem wp_8_1_stronglySheafy (s : ℕ) :
    IsSheafyComplete (WPA K (shiftWeight (fun k => k) s)) := sorry

/-- **[WP] Theorem 8.1 (not stably uniform)**: `𝒜` is not stably uniform. -/
theorem wp_8_1_not_isStablyUniform : ¬ IsStablyUniform (WPA K (fun k => k)) := sorry

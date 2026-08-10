/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WP.Algebra
import «Adic spaces».WP.ChainReducedDef
import «Adic spaces».SheafyRing
import «Adic spaces».Uniform

/-!
# Comparator challenge: [WP] Theorem 6.2 (the rationally stably reduced example)

The conclusions of the paper's second headline theorem ([WP]
thm:rationally-reduced-example), stated with `sorry` proofs, for verification by
[leanprover/comparator](https://github.com/leanprover/comparator) against the real
proofs in `«Adic spaces».WP.Main` (via `Comparator/WPSolution.lean`): identical
statements, axiom budget `[propext, Quot.sound, Classical.choice]`, and kernel
acceptance.

This module imports only the **definition layer** — `WP.Algebra` (defines the
weighted-parity algebra `WPA` and carries its `CompleteSpace` / `IsHuberRing` /
`IsTateRing` / `PlusSubring` instances), `WP.ChainReducedDef` (defines
`ChainReduced`), `SheafyRing` (defines `IsSheafyComplete`) and `Uniform` (defines
`IsUniform` / `IsStablyUniform`). Its import closure contains **none** of the
modules that prove these statements (`WP.Main`, `WP.UniformDomain`,
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

/-- **[WP] Theorem 6.2 (1, uniform)**: `𝒜` is uniform. -/
theorem wp_6_2_isUniform : IsUniform (WPA K (fun k => k)) := sorry

/-- **[WP] Theorem 6.2 (1, domain)**: `𝒜` is an integral domain. -/
theorem wp_6_2_isDomain : IsDomain (WPA K (fun k => k)) := sorry

/-- **[WP] Theorem 6.2 (1, nonnoetherian)**: `𝒜` is not noetherian. -/
theorem wp_6_2_not_isNoetherianRing : ¬ IsNoetherianRing (WPA K (fun k => k)) := sorry

/-- **[WP] Theorem 6.2 (1, `𝒜° = 𝒜₀`)**: the power-bounded subring is the unit ball. -/
theorem wp_6_2_powerBounded_eq_unitBall :
    powerBoundedSubring (WPA K (fun k => k)) =
      (FiniteJet.unitBall (WPA K (fun k => k)) : Set (WPA K (fun k => k))) := sorry

/-- **[WP] Theorem 6.2 (2, sheafy)**: `(𝒜, 𝒜°)` is sheafy — every valid pair. -/
theorem wp_6_2_isSheafyComplete : IsSheafyComplete (WPA K (fun k => k)) := sorry

/-- **[WP] Theorem 6.2 (2, strongly sheafy)**: every shifted-weight algebra
`𝒜⟨V₁,…,Vₛ⟩` is sheafy. -/
theorem wp_6_2_stronglySheafy (s : ℕ) :
    IsSheafyComplete (WPA K (shiftWeight (fun k => k) s)) := sorry

/-- **[WP] Theorem 6.2 (3, rationally stably reduced)**: every finite iterated
rational localization of `𝒜` is reduced.

**NOT in `theorem_names` yet.** The library's proof is complete in every
example-specific input (all head-reducedness leaves are discharged at maximal
ideals), but still consumes the core development's Wedhorn Prop 8.30 restriction
flatness (`prop_8_30_flat_clean`), whose own proof is an open frontier of the
general 8.28(b) campaign — so its axiom set currently includes `sorryAx` and
comparator would rightly reject it. The statement is pinned here so the
certificate only needs the name added back once 8.30 lands. -/
theorem wp_6_2_chainReduced (n : ℕ) : ChainReduced (WPA K (fun k => k)) n := sorry

/-- **[WP] Theorem 6.2 (4 ⇒, not stably uniform)**: `𝒜` is not stably uniform.
Together with (3) this pins the paper's "in particular": some rational localization
of `𝒜` is non-uniform, yet — by (3) — reduced. -/
theorem wp_6_2_not_isStablyUniform : ¬ IsStablyUniform (WPA K (fun k => k)) := sorry

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WP.Main

/-!
# Comparator solution: [WP] Theorem 6.2

Forwards each statement of `WPChallenge.lean` to the library's proof. This is the
module comparator rebuilds inside the sandbox, so it is deliberately tiny: the
project itself is already built, and only this file is treated as the untrusted
submission.

The binder block is identical to the challenge's, so the two elaborate to the same
type; the paper's weight `w = id` is spelled `fun k => k` exactly as there
(definitionally `WeightedParity.idWeight`).
-/

open WeightedParity ValuationSpectrum TopologicalRing FiniteJetOver
open scoped NormedField Valued

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable [IsDiscreteValuationRing 𝒪[K]]

/-- **[WP] Theorem 6.2 (1, uniform)**. -/
theorem wp_6_2_isUniform : IsUniform (WPA K (fun k => k)) :=
  weightedParity_isUniform_of_dvr K

/-- **[WP] Theorem 6.2 (1, domain)**. -/
theorem wp_6_2_isDomain : IsDomain (WPA K (fun k => k)) :=
  weightedParity_isDomain K

/-- **[WP] Theorem 6.2 (1, nonnoetherian)**. -/
theorem wp_6_2_not_isNoetherianRing : ¬ IsNoetherianRing (WPA K (fun k => k)) :=
  weightedParity_not_noetherian K

/-- **[WP] Theorem 6.2 (1, `𝒜° = 𝒜₀`)**. -/
theorem wp_6_2_powerBounded_eq_unitBall :
    powerBoundedSubring (WPA K (fun k => k)) =
      (FiniteJet.unitBall (WPA K (fun k => k)) : Set (WPA K (fun k => k))) :=
  weightedParity_powerBounded_eq_unitBall (Uniformizer.ofDVR K)

/-- **[WP] Theorem 6.2 (2, sheafy)**. -/
theorem wp_6_2_isSheafyComplete : IsSheafyComplete (WPA K (fun k => k)) :=
  weightedParity_isSheafyComplete_of_dvr K

/-- **[WP] Theorem 6.2 (2, strongly sheafy)**. -/
theorem wp_6_2_stronglySheafy (s : ℕ) :
    IsSheafyComplete (WPA K (shiftWeight (fun k => k) s)) :=
  weightedParity_stronglySheafy_of_dvr K s

/-- **[WP] Theorem 6.2 (3, rationally stably reduced)**. NOT in `theorem_names`:
the proof is complete in every example-specific input but still consumes the core
development's Wedhorn Prop 8.30 flatness (`prop_8_30_flat_clean`, an open frontier
of the general 8.28(b) campaign), so its axiom set currently includes `sorryAx`. -/
theorem wp_6_2_chainReduced (n : ℕ) : ChainReduced (WPA K (fun k => k)) n :=
  weightedParity_chainReduced_unconditional_of_dvr K n

/-- **[WP] Theorem 6.2 (4 ⇒, not stably uniform)**. -/
theorem wp_6_2_not_isStablyUniform : ¬ IsStablyUniform (WPA K (fun k => k)) :=
  weightedParity_not_stablyUniform_of_dvr K

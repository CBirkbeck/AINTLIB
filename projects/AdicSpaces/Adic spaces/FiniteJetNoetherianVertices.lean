/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FiniteJetRings
import «Adic spaces».WedhornCechAcyclicity

/-!
# The comparison vertices 𝓑, 𝓒, 𝓓 are strongly noetherian, hence sheafy

Source: [FJP] Prop 2.1 (verbatim): "Each of ℬ, 𝒞, 𝒟 is a quotient of a finite Tate algebra
over k, so each is strongly noetherian." and Theorem 5.3's proof: "The three comparison
rings are strongly noetherian. Huber's direct sheaf theorem [4, Theorem 2.2] gives the
rational-cover sheaf condition for their structure presheaves."

Strategy (design decision DD5, `plan.md`): everything reduces to `IsStronglyNoetherian K`
(`ExampleLaurentSeries.lean`) through
* the flattening pattern of `ExampleUnitDisc.lean` (`exists_flatten'`, `restrictedGaussEquiv`),
* a surjection `K⟨W,V,Z₁,…,Zₙ⟩ ↠ L⟨Z₁,…,Zₙ⟩` (evaluation `W ↦ Wu, V ↦ Wu⁻¹`, surjective via
  the norm-preserving monomial section — noetherianity passes along surjections; no kernel
  identification needed),
* `DualNumber S` noetherian for noetherian `S` (`JetDualNumberNorm.lean`), with the
  coefficientwise flattening `(DualNumber S)⟨Z⟩ ≅ DualNumber (S⟨Z⟩)`.

The payoff instances feed `isSheafy_of_stronglyNoetherian_828b` exactly as in the unit-disc
example. Note 𝓑 and 𝓓 are non-reduced; the 828b hypothesis bundle does not require reduced
or domain, so it applies ([FJP] Lemma 4.2's "possibly nonreduced" is mirrored here).
-/

open Filter Topology

namespace FiniteJet

open RestrictedLaurent

variable (F : Type*) [Field F]

local notation "K" => LaurentSeries F

/-! ### Strong noetherianity of the four coefficient rings -/

/-- Restricted extensions of the Laurent ring are noetherian: `L⟨Z₁,…,Zₘ⟩` is a quotient of
the noetherian `K⟨W,V,Z₁,…,Zₘ⟩` ([FJP] Prop 2.1; the presentation `L = k⟨W,V⟩/(WV−1)`). -/
theorem isNoetherianRing_restricted_L (m : ℕ) :
    IsNoetherianRing (restrictedMvPowerSeriesSubring m (L F)) := by sorry

/-- `L = K⟨W,W⁻¹⟩` is strongly noetherian. -/
instance : IsStronglyNoetherian (L F) :=
  ⟨isNoetherianRing_restricted_L F⟩

instance : IsNoetherianRing (L F) := IsStronglyNoetherian.isNoetherianRing (L F)

/-- `𝒞 = L⟨Q⟩` is strongly noetherian (flattening `𝒞⟨Z₁,…,Zₘ⟩ ≅ L⟨Q,Z₁,…,Zₘ⟩`, exactly the
unit-disc pattern over the base `L`). -/
instance : IsStronglyNoetherian (JetC F) := by sorry

instance : IsNoetherianRing (JetC F) := IsStronglyNoetherian.isNoetherianRing (JetC F)

/-- Jet flattening: restricted extension commutes with dual numbers,
`(DualNumber S)⟨Z₁,…,Zₘ⟩ ≅ DualNumber (S⟨Z₁,…,Zₘ⟩)` coefficientwise. Stated for the two
bases we use. -/
theorem isNoetherianRing_restricted_dualNumber
    (S : Type*) [NormedCommRing S] [IsUltrametricDist S]
    (hS : ∀ m : ℕ, IsNoetherianRing (restrictedMvPowerSeriesSubring m S)) (m : ℕ) :
    IsNoetherianRing (restrictedMvPowerSeriesSubring m (DualNumber S)) := by sorry

/-- `𝓑 = K⟨W⟩[Q]/(Q²)` is strongly noetherian ([FJP] Prop 2.1). -/
instance : IsStronglyNoetherian (JetB F) := by sorry

instance : IsNoetherianRing (JetB F) := IsStronglyNoetherian.isNoetherianRing (JetB F)

/-- `𝓓 = L[Q]/(Q²)` is strongly noetherian ([FJP] Prop 2.1). -/
instance : IsStronglyNoetherian (JetD F) := by sorry

instance : IsNoetherianRing (JetD F) := IsStronglyNoetherian.isNoetherianRing (JetD F)

/-! ### Noetherian unit-ball pods (inputs to the graph–Koszul layer)

[FJP] Lemma 4.2 constructs a noetherian ring of definition for each affinoid vertex; in our
concrete models these are the unit balls: `DualNumber (k°⟨W⟩)`, `L₀⟨Q⟩`, `DualNumber L₀`. -/

theorem isNoetherianRing_unitBall_L : IsNoetherianRing (unitBall (L F)) := by sorry

theorem isNoetherianRing_unitBall_JetB : IsNoetherianRing (unitBall (JetB F)) := by sorry

theorem isNoetherianRing_unitBall_JetC : IsNoetherianRing (unitBall (JetC F)) := by sorry

theorem isNoetherianRing_unitBall_JetD : IsNoetherianRing (unitBall (JetD F)) := by sorry

/-! ### The payoff: the three comparison vertices are sheafy

[FJP] Theorem 5.3 (input): "The three comparison rings are strongly noetherian. Huber's
direct sheaf theorem [4, Theorem 2.2] gives the rational-cover sheaf condition for their
structure presheaves."  In the project's vocabulary this is
`isSheafy_of_stronglyNoetherian_828b`, whose hypothesis bundle (`PlusSubring`, `IsTateRing`,
`IsStronglyNoetherian`, `T2Space`, `IsRingOfIntegralElements A⁺`, right-uniformity
completeness) was assembled in `FiniteJetRings.lean` — with the maximal plus rings, which for
𝓑 and 𝓓 are unbounded ([FJP] (2.1d)); no domain/reducedness hypothesis is needed. -/

theorem isSheafy_JetB : ValuationSpectrum.IsSheafy (JetB F) := by sorry

theorem isSheafy_JetC : ValuationSpectrum.IsSheafy (JetC F) := by sorry

theorem isSheafy_JetD : ValuationSpectrum.IsSheafy (JetD F) := by sorry

end FiniteJet

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WedhornCechAcyclicity
import «Adic spaces».RationalIntersection

/-!
# All-degree Čech acyclicity of rational covers (campaign C skeleton)

Wedhorn's Lemmas 8.33 and 8.34 are **all-degree** statements: for a 2-cover the
augmented alternating complex `0 → O(X) → O(U₁) × O(U₂) → O(U₁∩U₂) → 0` is exact
([Wedhorn] l.4151: "the augmented Čech complex (with alternating cochains) … is
exact"), and `O_X`-acyclicity of the ideal-generated covers follows by the
Prop A.3 product/refinement calculus. The project's `IsOXAcyclic` renders only the
degree-zero content (separation + gluing); for a 2-cover the only missing degree
is **surjectivity of the difference map onto the intersection**, stated here.

The q-fold machinery (multi-intersection data, the Čech complex on
`RationalCoveringData`, A.3 in all degrees) and the per-example headlines
(`JetA` via the Milnor LES, `WPA` via coefficientwise `c₀`-primitives) are the
API gap C-AG1 — see `decomposition.md`.
-/

@[expose] public section

noncomputable section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]
variable [DecidableEq (RationalLocData A)]

/-- **C-L1 (Wedhorn 8.33, the missing degree)**: for the Laurent 2-cover
`{R(f/1), R(1/f)}` of a rational base, the difference map onto the value on the
intersection is surjective. [Wedhorn] l.4200: "The equations
`A⟨ζ,ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹A⟨ζ⁻¹⟩` … show the surjectivity of λ and λ′." Together
with the existing `IsOXAcyclic` content this is exactness of the full augmented
2-cover complex. -/
theorem wedhorn_lemma_833_deg1_surjective [DecidableEq A]
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A]
    (D₀ : RationalLocData A) (hD₀ : D₀.IsRational) (f : A)
    (hP : Ideal.span (((laurentPlusDatum D₀ f).T : Finset A) : Set A) = ⊤)
    (hM : Ideal.span (((laurentMinusDatum D₀ f).T : Finset A) : Set A) = ⊤) :
    ∀ z : presheafValue
        ((laurentPlusDatum D₀ f).interDatum (laurentMinusDatum D₀ f) hP hM),
      ∃ (x : presheafValue (laurentPlusDatum D₀ f))
        (y : presheafValue (laurentMinusDatum D₀ f)),
        restrictionMap _ _
            ((laurentPlusDatum D₀ f).interDatum_subset_left
              (laurentMinusDatum D₀ f) hP hM) x -
          restrictionMap _ _
            ((laurentPlusDatum D₀ f).interDatum_subset_right
              (laurentMinusDatum D₀ f) hP hM) y = z := by
  sorry

end ValuationSpectrum

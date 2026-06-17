/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».RelativePieceKeystone
import «Adic spaces».RestrictionFlatness

/-!
# Leaf-A chain assembly (Wedhorn Prop 8.30, whole-space residual)

The downstream fold that assembles the Remark 7.55 flatness chain for the whole-space
image piece `𝒪_B(im E)` over `B = 𝒪_X(D)`. This is the join point of two otherwise parallel
branches:

* the **per-step machinery** (`RelativePieceKeystone`): `flat_chainStep_domUnit` (the
  `CompatiblePlusSubring`-free domUnit step, span⊤ from the dominating unit),
  `flat_presheafValue_coUnitDatum_at_base` (the `X₀` coUnit base step),
  `remark755_dominating_unit_over_presheafValue` (the dominating unit `u`, `|u| ≤ |s|`);
* the **chain fold** (`RestrictionFlatness`): `restrictionMap_flat_chain`.

The chain invariant `h_pb : u·s⁻¹ ∈ B⁺` is **structural** — `u` is a *generator* of the step
piece `{tᵢ, u}` over the denominator `s`, so `u·s⁻¹ = divByS u s ∈ locPlusSubring ⊆ B⁺`
(`RationalLocData.divByS_mem_locPlusSubring`, upstream in `Presheaf`); no power-bounded keystone
or Spa pullback is needed (so `WedhornCechAcyclicity` is NOT imported).

Wedhorn Remark 7.55 (wedhorn.txt:3504-3517): `Spa B ⊇ X₀ ⊇ ⋯ ⊇ Xₙ = im E`, `X₀` the
dominating-unit piece (where `s` becomes a unit), each `Xᵢ = Xᵢ₋₁ ∩ {x(tᵢ) ≤ x(s)}`.
Every piece is a rational subset of `Spa B` (two-level `presheafValue`), so the whole fold
stays two-level — the `𝒪(X₀)`-relative chain would be three-level and exceed the elaborator.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Remark 7.55, Prop 8.30 (wedhorn.txt:3504-3517)
-/

namespace ValuationSpectrum

open Pointwise

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]

/-- **Whole-space Prop 8.30 (Remark 7.55 chain), assembled downstream.**
`𝒪_B(im E)` is flat over `B = 𝒪_X(D)`, for `im E = imagePieceDatum D E.T E.s` the whole-space
image of a `span = ⊤` rational piece. Proven by folding `flat_chainStep_domUnit` over `E.T`'s
generators (the `CompatiblePlusSubring`-free domUnit per-step) on top of the `X₀` dominating-unit
coUnit base, discharging the chain invariant `h_pb` via the [Hu2] 3.3 power-bounded keystone.
The downstream counterpart of `prop_8_30_imagePiece_wholeSpace_flat`. -/
theorem prop_8_30_imagePiece_assembled
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [CompatiblePlusSubring A]
    (D E : RationalLocData A) (hspanE : Ideal.span (E.T : Set A) = ⊤) :
    @Module.Flat (presheafValue D) (presheafValue (imagePieceDatum D E.T E.s hspanE)) _ _
      ((imagePieceDatum D E.T E.s hspanE).canonicalMap).toModule := by
  sorry

end ValuationSpectrum

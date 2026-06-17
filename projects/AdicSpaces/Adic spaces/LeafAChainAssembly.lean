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

/-- **genPieceUnit `rationalOpen`-eq** — `R({↑u}/sB) = R({1}/(sB·↑u⁻¹))` for `↑u` a unit
(`x(↑u) ≤ x(sB) ⟺ x(1) ≤ x(sB·↑u⁻¹)`, unit cancellation). Extracted so the engine's `h_ro` is
a one-liner (matching `imagePieceDatum_domUnit_rationalOpen_eq`'s structure). -/
theorem genPieceUnit_coUnit_rationalOpen_eq (P : PairOfDefinition A) (u : Aˣ) (sB : A)
    (hspan : Ideal.span (({(↑u : A)} : Finset A) : Set A) = ⊤) :
    rationalOpen (genPieceDatum P {(↑u : A)} sB hspan).T (genPieceDatum P {(↑u : A)} sB hspan).s =
      rationalOpen (coUnitDatum P (sB * ↑u⁻¹)).T (coUnitDatum P (sB * ↑u⁻¹)).s := by
  classical
  have hui : (↑u : A) * (↑u⁻¹ : A) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hiu : (↑u⁻¹ : A) * (↑u : A) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hWT : (genPieceDatum P {(↑u : A)} sB hspan).T = {(↑u : A)} := rfl
  have hWs : (genPieceDatum P {(↑u : A)} sB hspan).s = sB := rfl
  have hUT : (coUnitDatum P (sB * ↑u⁻¹)).T = {(1 : A)} := rfl
  have hUs : (coUnitDatum P (sB * ↑u⁻¹)).s = sB * ↑u⁻¹ := rfl
  rw [hWT, hWs, hUT, hUs]
  apply Set.ext
  intro w
  rw [rationalOpen, rationalOpen, Set.mem_sep_iff, Set.mem_sep_iff]
  refine and_congr_right fun hspa => ?_
  constructor
  · rintro ⟨hgen, hnz⟩
    have h1 : w.vle (↑u : A) sB := hgen _ (Finset.mem_singleton_self _)
    refine ⟨fun t ht => ?_, ?_⟩
    · rw [Finset.mem_singleton] at ht; subst ht
      have h2 := w.mul_vle_mul_left h1 (↑u⁻¹ : A)
      rwa [hui] at h2
    · intro h0
      exact hnz (by have h2 := w.mul_vle_mul_left h0 (↑u : A)
                    rwa [mul_assoc, hiu, mul_one, zero_mul] at h2)
  · rintro ⟨hgen, hnz⟩
    have h1 : w.vle (1 : A) (sB * ↑u⁻¹) := hgen _ (Finset.mem_singleton_self _)
    refine ⟨fun t ht => ?_, ?_⟩
    · rw [Finset.mem_singleton] at ht; subst ht
      have h2 := w.mul_vle_mul_left h1 (↑u : A)
      rwa [one_mul, mul_assoc, hiu, mul_one] at h2
    · intro h0
      exact hnz (by have h2 := w.mul_vle_mul_left h0 (↑u⁻¹ : A)
                    rwa [zero_mul] at h2)

/-- **Flat transport across equal `rationalOpen`** — generic in `D₁ D₂`: if they have the same
`rationalOpen` and `𝒪(D₁)` is flat over `A`, so is `𝒪(D₂)`. The restriction `𝒪(D₂) ≃+* 𝒪(D₁)` is
the iso (`restrictionMap_bijective_of_rationalOpen_eq`); flatness transports
(`Module.Flat.of_linearEquiv`). Generic so the transport elaborates ONCE for OPAQUE data — applied to
specific datums it is a direct `exact`, sidestepping the per-datum (two-nontrivial-denominator) `whnf`
blow-up that an inline transport hits. -/
theorem flat_of_rationalOpen_eq
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    (D₁ D₂ : RationalLocData A)
    (h_ro : rationalOpen D₂.T D₂.s = rationalOpen D₁.T D₁.s)
    (hflat : @Module.Flat A (presheafValue D₁) _ _ (RingHom.toModule D₁.canonicalMap)) :
    @Module.Flat A (presheafValue D₂) _ _ (RingHom.toModule D₂.canonicalMap) := by
  let e : presheafValue D₂ ≃+* presheafValue D₁ :=
    RingEquiv.ofBijective (restrictionMapHom D₂ D₁ h_ro.symm.le)
      (restrictionMap_bijective_of_rationalOpen_eq D₂ D₁ h_ro)
  letI : Module A (presheafValue D₁) := RingHom.toModule D₁.canonicalMap
  letI : Module A (presheafValue D₂) := RingHom.toModule D₂.canonicalMap
  have he_smul : ∀ (a : A) (x : presheafValue D₂), e (a • x) = a • e x := by
    intro a x
    change e (D₂.canonicalMap a * x) = D₁.canonicalMap a * e x
    rw [e.map_mul]; congr 1
    exact restrictionMapHom_canonicalMap D₂ D₁ h_ro.symm.le a
  exact @Module.Flat.of_linearEquiv A (presheafValue D₁) (presheafValue D₂)
    _ _ _ _ _ hflat
    { toLinearMap := { toFun := e, map_add' := e.map_add, map_smul' := he_smul }
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

/-- **genPieceUnit engine** — `𝒪(genPieceDatum P {↑u} sB)` flat over `A` (`↑u` a unit). Same
`rationalOpen` as `coUnitDatum (sB·↑u⁻¹)`, flat by the coUnit engine; one-line transport via the
generic `flat_of_rationalOpen_eq`. -/
theorem presheafValue_flat_of_genPieceUnit_faithful
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    (P : PairOfDefinition A) (u : Aˣ) (sB : A)
    (hspan : Ideal.span (({(↑u : A)} : Finset A) : Set A) = ⊤) :
    @Module.Flat A (presheafValue (genPieceDatum P {(↑u : A)} sB hspan)) _ _
      (RingHom.toModule (genPieceDatum P {(↑u : A)} sB hspan).canonicalMap) := by
  have h_ro := genPieceUnit_coUnit_rationalOpen_eq P u sB hspan
  have hflat := presheafValue_flat_of_coUnitDatum_faithful P (sB * ↑u⁻¹)
  exact flat_of_rationalOpen_eq _ _ h_ro hflat

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
  classical
  haveI hTateB : IsTateRing (presheafValue D) := presheafValue_isTateRing_concrete D
  haveI : IsNoetherianRing (presheafValue D) := presheafValue_isNoetherianRing_faithful D
  haveI : IsStronglyNoetherian (presheafValue D) := presheafValue_isStronglyNoetherian_faithful D
  haveI : IsHuberRing (presheafValue D) := hTateB.toIsHuberRing
  haveI hCompleteB : @CompleteSpace (presheafValue D)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D)) :=
    presheafValue_completeSpace_rightUniformSpace D
  -- Remark 7.55 dominating unit `u` (`|u| ≤ |sB|` on `rationalOpen (im E)`).
  obtain ⟨u, hu⟩ := remark755_dominating_unit_over_presheafValue D E hspanE
  have hspan_u : Ideal.span (({(↑u : presheafValue D)} : Finset (presheafValue D)) :
      Set (presheafValue D)) = ⊤ := by
    rw [Finset.coe_singleton]; exact Ideal.span_singleton_eq_top.mpr u.isUnit
  -- X₀ = R({↑u}/sB), flat over B (the dominating-unit base; genPieceUnit engine at A := B).
  have hX0 := presheafValue_flat_of_genPieceUnit_faithful (presheafValue_concretePair D) u
    (imagePieceDatum D E.T E.s hspanE).s hspan_u
  sorry

end ValuationSpectrum

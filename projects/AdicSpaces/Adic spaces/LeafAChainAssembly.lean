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

/-- **Per-step `h_pb` discharge** — `canMap t · (canMap (D₀.s))⁻¹ ∈ D₀⁺` for any generator
`t ∈ D₀.T`. STRUCTURAL: `t/(D₀.s) = divByS t (D₀.s) ∈ locPlusSubring` (the generator-over-denominator
is a defining generator of the plus-subring, `divByS_mem_locPlusSubring`), and its `coeRingHom`-image
lies in `completedPlusSubring = (presheafValue D₀)⁺` (`coeRingHom_mem_completedPlusSubring`). The
element equals `coeRingHom (divByS t (D₀.s))` since `canMap = coeRingHom ∘ algebraMap`,
`Ring.inverse (canMap (D₀.s)) = invS`, `invS = coeRingHom (divByS 1 (D₀.s))`, and `divByS t (D₀.s)
= algebraMap t · divByS 1 (D₀.s)`. -/
theorem domUnit_invDenom_mem_completedPlus (D₀ : RationalLocData A) {t : A} (ht : t ∈ D₀.T) :
    D₀.canonicalMap t * Ring.inverse (D₀.canonicalMap D₀.s) ∈ D₀.completedPlusSubring := by
  have e1 := algebraMap_s_mul_divByS D₀ t
  have e2 := algebraMap_s_mul_divByS D₀ (1 : A)
  rw [map_one] at e2
  have hb : divByS t D₀.s =
      algebraMap A (Localization.Away D₀.s) t * divByS (1 : A) D₀.s := by
    calc divByS t D₀.s
        = (algebraMap A (Localization.Away D₀.s) D₀.s * divByS (1 : A) D₀.s) * divByS t D₀.s := by
            rw [e2, one_mul]
      _ = divByS (1 : A) D₀.s *
            (algebraMap A (Localization.Away D₀.s) D₀.s * divByS t D₀.s) := by ring
      _ = divByS (1 : A) D₀.s * algebraMap A (Localization.Away D₀.s) t := by rw [e1]
      _ = algebraMap A (Localization.Away D₀.s) t * divByS (1 : A) D₀.s := by ring
  have hinv : Ring.inverse (D₀.canonicalMap D₀.s) = invS D₀ := by
    have h1 : Ring.inverse (D₀.canonicalMap D₀.s) * D₀.canonicalMap D₀.s = 1 :=
      Ring.inverse_mul_cancel _ D₀.canonicalMap_s_isUnit
    calc Ring.inverse (D₀.canonicalMap D₀.s)
        = Ring.inverse (D₀.canonicalMap D₀.s) * (D₀.canonicalMap D₀.s * invS D₀) := by
            rw [canonicalMap_s_mul_invS, mul_one]
      _ = Ring.inverse (D₀.canonicalMap D₀.s) * D₀.canonicalMap D₀.s * invS D₀ := by ring
      _ = invS D₀ := by rw [h1, one_mul]
  have heq : D₀.canonicalMap t * Ring.inverse (D₀.canonicalMap D₀.s) =
      D₀.coeRingHom (divByS t D₀.s) := by
    rw [hinv, invS_eq_coeRingHom_divByS_one, hb, map_mul]
    simp only [RationalLocData.canonicalMap, RingHom.comp_apply]
  rw [heq]
  exact D₀.coeRingHom_mem_completedPlusSubring (D₀.divByS_mem_locPlusSubring ht)

/-- **`sB`-relative `h_pb` discharge** — `canMap u · (canMap sB)⁻¹ ∈ D⁺` whenever `sB` divides the
denominator (`D.s = sB·c`) and the witness `u·c ∈ D.T`. Reduces to `domUnit_invDenom_mem_completedPlus`
at `u·c` over `D.s` via the cofactor identity `u/sB = (u·c)/D.s` (`canMap c` is a unit since `c ∣ D.s`).
This is what discharges each chain step's `h_pb`: `interSamePair` multiplies denoms so `Xⱼ.s = sB^{j+1}`,
but the product structure keeps `↑u·sB^j ∈ Xⱼ.T`, so `↑u/sB` is structural at every piece. -/
theorem domUnit_invDenom_mem_completedPlus_general (D : RationalLocData A) (u sB c : A)
    (hs : D.s = sB * c) (hmem : u * c ∈ D.T) :
    D.canonicalMap u * Ring.inverse (D.canonicalMap sB) ∈ D.completedPlusSubring := by
  have hsc : D.canonicalMap D.s = D.canonicalMap sB * D.canonicalMap c := by rw [hs, map_mul]
  have hc_unit : IsUnit (D.canonicalMap c) :=
    isUnit_of_mul_isUnit_right (hsc ▸ D.canonicalMap_s_isUnit)
  have heq : D.canonicalMap u * Ring.inverse (D.canonicalMap sB) =
      D.canonicalMap (u * c) * Ring.inverse (D.canonicalMap D.s) := by
    rw [map_mul, hsc, Ring.mul_inverse_rev, ← mul_assoc,
      mul_assoc (D.canonicalMap u) (D.canonicalMap c) (Ring.inverse (D.canonicalMap c)),
      Ring.mul_inverse_cancel _ hc_unit, mul_one]
  rw [heq]
  exact domUnit_invDenom_mem_completedPlus D hmem

/-- `sB` is a unit in `𝒪(D)` when it divides the denominator `D.s` (`D.s = sB·c`). -/
theorem canonicalMap_isUnit_of_dvd_s (D : RationalLocData A) (sB c : A) (hs : D.s = sB * c) :
    IsUnit (D.canonicalMap sB) :=
  isUnit_of_mul_isUnit_left
    (show IsUnit (D.canonicalMap sB * D.canonicalMap c) by
      rw [← map_mul, ← hs]; exact D.canonicalMap_s_isUnit)

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

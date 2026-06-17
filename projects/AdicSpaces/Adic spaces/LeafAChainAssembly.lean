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
open Classical

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

/-- `span{g, ↑u} = ⊤` for `↑u` a unit (the dominating unit makes every chain-step piece rational). -/
theorem span_pair_unit_eq_top (g : A) (u : Aˣ) :
    Ideal.span ((({g, (↑u : A)} : Finset A)) : Set A) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) u.isUnit

/-- One Remark-7.55 chain step: intersect `D'` with the dominating-unit piece `R({g, ↑u}/sB)`
(`interSamePair`, so the denominator becomes `D'.s · sB`). -/
noncomputable def chainStep (u : Aˣ) (sB : A)
    (D' : RationalLocData A) (g : A) : RationalLocData A :=
  D'.interSamePair (genPieceDatum D'.P {g, (↑u : A)} sB (span_pair_unit_eq_top g u)) rfl

/-- `interSamePair`'s generator set as a pointwise product `(insert D₁.s D₁.T) * (insert D₂.s D₂.T)`
(symbolic in `D₂`, so applying it to a concrete second datum avoids reducing that datum's `hopen`). -/
theorem interSamePair_T_mul (D₁ D₂ : RationalLocData A) (hP : D₂.P = D₁.P) :
    (D₁.interSamePair D₂ hP).T = (insert D₁.s D₁.T) * (insert D₂.s D₂.T) := by
  rw [Finset.mul_def]; rfl

/-- **Chain invariant propagation** — the structural witness `∃c, D.s = sB·c ∧ ↑u·c ∈ D.T` survives
one `chainStep`: the denominator multiplies by `sB` (new cofactor `c·sB`) and `(↑u·c)·sB` lands in the
product generator set. This is what keeps `h_pb`/`hs_unit` structural along the whole fold. -/
theorem chainStep_invariant (u : Aˣ) (sB c : A)
    (D' : RationalLocData A) (g : A) (hs : D'.s = sB * c) (hmem : (↑u : A) * c ∈ D'.T) :
    (chainStep u sB D' g).s = sB * (c * sB) ∧
      (↑u : A) * (c * sB) ∈ (chainStep u sB D' g).T := by
  refine ⟨by show D'.s * sB = sB * (c * sB); rw [hs]; ring, ?_⟩
  have hrw : (↑u : A) * (c * sB) = ((↑u : A) * c) * sB := by ring
  rw [hrw,
    show (chainStep u sB D' g).T = _ from
      interSamePair_T_mul D' (genPieceDatum D'.P {g, (↑u : A)} sB (span_pair_unit_eq_top g u)) rfl,
    genPieceDatum_s, genPieceDatum_T]
  exact Finset.mul_mem_mul (Finset.mem_insert_of_mem hmem) (Finset.mem_insert_self _ _)

/-- The fold's `rationalOpen` shrinks: `R(foldl gens D₀) ⊆ R(D₀)` (each step is an intersection). -/
theorem foldl_chainStep_subset (u : Aˣ) (sB : A) (gens : List A) (D₀ : RationalLocData A) :
    rationalOpen (gens.foldl (chainStep u sB) D₀).T (gens.foldl (chainStep u sB) D₀).s ⊆
      rationalOpen D₀.T D₀.s := by
  induction gens generalizing D₀ with
  | nil => exact subset_refl _
  | cons g gs ih =>
    exact (ih (chainStep u sB D₀ g)).trans
      (RationalLocData.interSamePair_subset_left D₀
        (genPieceDatum D₀.P {g, (↑u : A)} sB (span_pair_unit_eq_top g u)) rfl)

/-- **The Remark-7.55 fold (list-induction core).** Folding `chainStep` over `gens` keeps `𝒪(foldl)`
flat over `𝒪(D₀)`: each step is `flat_chainStep_domUnit` (the `CompatiblePlusSubring`-free domUnit
step, whose `hs_unit`/`h_pb` are discharged structurally from the carried invariant `D₀.s = sB·c ∧
↑u·c ∈ D₀.T`), composed by `restrictionMap_flat_trans`; the invariant propagates by
`chainStep_invariant`. No added hypothesis on the headline — `c` is the cofactor witness, discharged
at the call site (`c = 1` for `X₀`). -/
theorem flat_domUnit_listFold
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    (u : Aˣ) (sB : A) (gens : List A) (D₀ : RationalLocData A) (c : A)
    (hs : D₀.s = sB * c) (hmem : (↑u : A) * c ∈ D₀.T) :
    @Module.Flat (presheafValue D₀) (presheafValue (gens.foldl (chainStep u sB) D₀)) _ _
      (restrictionMapHom D₀ (gens.foldl (chainStep u sB) D₀)
        (foldl_chainStep_subset u sB gens D₀)).toModule := by
  induction gens generalizing D₀ c with
  | nil => exact restrictionMapHom_refl_flat D₀ (foldl_chainStep_subset u sB [] D₀)
  | cons g gs ih =>
    obtain ⟨hs', hmem'⟩ := chainStep_invariant u sB c D₀ g hs hmem
    exact restrictionMap_flat_trans D₀ (chainStep u sB D₀ g)
      (gs.foldl (chainStep u sB) (chainStep u sB D₀ g))
      (RationalLocData.interSamePair_subset_left D₀
        (genPieceDatum D₀.P {g, (↑u : A)} sB (span_pair_unit_eq_top g u)) rfl)
      (foldl_chainStep_subset u sB gs (chainStep u sB D₀ g))
      (flat_chainStep_domUnit D₀ g sB (↑u) (span_pair_unit_eq_top g u)
        (canonicalMap_isUnit_of_dvd_s D₀ sB c hs)
        (domUnit_invDenom_mem_completedPlus_general D₀ (↑u) sB c hs hmem))
      (ih (chainStep u sB D₀ g) (c * sB) hs' hmem')

/-- **Compose `A → 𝒪(X₀) → 𝒪(D')`** — flatness of the whole-space-canonical `A → 𝒪(D')` from the
base step `A → 𝒪(X₀)` (`X₀.canonicalMap`) and the relative step `𝒪(X₀) → 𝒪(D')` (`restrictionMapHom`),
via `Module.Flat.trans`. The scalar tower is `restrictionMapHom_canonicalMap` (restriction commutes with
the canonical map). Generic in `X₀ D'` so the tower elaborates once. -/
theorem flat_trans_via_canonicalMap
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    (X₀ D' : RationalLocData A) (h : rationalOpen D'.T D'.s ⊆ rationalOpen X₀.T X₀.s)
    (hX0 : @Module.Flat A (presheafValue X₀) _ _ (RingHom.toModule X₀.canonicalMap))
    (hfold : @Module.Flat (presheafValue X₀) (presheafValue D') _ _
      (restrictionMapHom X₀ D' h).toModule) :
    @Module.Flat A (presheafValue D') _ _ (RingHom.toModule D'.canonicalMap) := by
  letI : Algebra A (presheafValue X₀) := X₀.canonicalMap.toAlgebra
  letI : Algebra (presheafValue X₀) (presheafValue D') := (restrictionMapHom X₀ D' h).toAlgebra
  letI : Algebra A (presheafValue D') := D'.canonicalMap.toAlgebra
  letI : Module A (presheafValue X₀) := Algebra.toModule
  letI : Module (presheafValue X₀) (presheafValue D') := Algebra.toModule
  letI : Module A (presheafValue D') := Algebra.toModule
  haveI : IsScalarTower A (presheafValue X₀) (presheafValue D') :=
    IsScalarTower.of_algebraMap_eq fun x => (restrictionMapHom_canonicalMap X₀ D' h x).symm
  haveI : Module.Flat A (presheafValue X₀) := hX0
  haveI : Module.Flat (presheafValue X₀) (presheafValue D') := hfold
  exact Module.Flat.trans A (presheafValue X₀) (presheafValue D')

/-- One `chainStep`'s `rationalOpen` is the intersection `R(D') ∩ R({g,↑u}/sB)`
(`interSamePair_rationalOpen` + the `genPieceDatum` field projections). -/
theorem chainStep_rationalOpen (u : Aˣ) (sB : A) (D' : RationalLocData A) (g : A) :
    rationalOpen (chainStep u sB D' g).T (chainStep u sB D' g).s =
      rationalOpen D'.T D'.s ∩ rationalOpen ({g, (↑u : A)} : Finset A) sB := by
  simp only [chainStep]
  rw [RationalLocData.interSamePair_rationalOpen, genPieceDatum_T, genPieceDatum_s]

/-- **The fold's `rationalOpen` membership.** `v ∈ R(foldl gens X₀)` iff `v ∈ R(X₀)` and `v` lies
in each step piece `R({g,↑u}/sB)`. By induction on `gens` (each step is the intersection
`chainStep_rationalOpen`). -/
theorem mem_foldl_chainStep (u : Aˣ) (sB : A) (gens : List A) (X₀ : RationalLocData A) (v : Spv A) :
    v ∈ rationalOpen (gens.foldl (chainStep u sB) X₀).T (gens.foldl (chainStep u sB) X₀).s ↔
      v ∈ rationalOpen X₀.T X₀.s ∧
        ∀ g ∈ gens, v ∈ rationalOpen ({g, (↑u : A)} : Finset A) sB := by
  induction gens generalizing X₀ with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih (chainStep u sB X₀ g), chainStep_rationalOpen,
      Set.mem_inter_iff, List.forall_mem_cons]
    tauto

/-- **Endpoint: `R(W/sB) = R(foldl W.toList X₀)`** (Wedhorn `Xₙ = im E`). The fold over `W`'s
generators (on the dominating-unit base `X₀ = R({↑u}/sB)`) recovers `R(W/sB)`: the fold carries an
extra `v(↑u) ≤ v(sB)` condition (from `X₀` and each step piece), which is **free** on `R(W/sB)` via
the dominating-unit hypothesis `hu` (Cor 7.32). -/
theorem foldl_rationalOpen_eq_base (P : PairOfDefinition A) (u : Aˣ) (sB : A) (W : Finset A)
    (hspan_u : Ideal.span (({(↑u : A)} : Finset A) : Set A) = ⊤)
    (hu : ∀ v ∈ rationalOpen W sB, v.vle (↑u) sB) :
    rationalOpen W sB =
      rationalOpen (W.toList.foldl (chainStep u sB) (genPieceDatum P {(↑u : A)} sB hspan_u)).T
        (W.toList.foldl (chainStep u sB) (genPieceDatum P {(↑u : A)} sB hspan_u)).s := by
  ext v
  rw [mem_foldl_chainStep]
  constructor
  · intro hv
    have huv := hu v hv
    obtain ⟨hspa, hgen, hsupp⟩ := hv
    refine ⟨⟨hspa, ?_, hsupp⟩, fun g hg => ⟨hspa, ?_, hsupp⟩⟩
    · intro t ht
      rw [genPieceDatum_T, Finset.mem_singleton] at ht; subst ht
      rw [genPieceDatum_s]; exact huv
    · intro t ht
      rw [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hgen t (Finset.mem_toList.mp hg)
      · exact huv
  · rintro ⟨hX₀, hg⟩
    obtain ⟨hspa, -, hsupp⟩ := hX₀
    refine ⟨hspa, ?_, hsupp⟩
    intro t ht
    exact (hg t (Finset.mem_toList.mpr ht)).2.1 t (Finset.mem_insert_self t _)

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
  set sB := (imagePieceDatum D E.T E.s hspanE).s with hsB
  set X₀ := genPieceDatum (presheafValue_concretePair D) {(↑u : presheafValue D)} sB hspan_u with hX₀
  set gens := (imagePieceDatum D E.T E.s hspanE).T.toList with hgens
  -- The Remark-7.55 fold is flat over `𝒪(X₀)` (invariant `X₀.s = sB·1`, `↑u·1 ∈ X₀.T = {↑u}`).
  have hfold := flat_domUnit_listFold u sB gens X₀ 1
    (by rw [hX₀, genPieceDatum_s, mul_one])
    (by rw [hX₀, genPieceDatum_T, mul_one]; exact Finset.mem_singleton_self _)
  -- Compose `B → 𝒪(X₀) → 𝒪(foldl)`.
  have hfoldB := flat_trans_via_canonicalMap X₀ (gens.foldl (chainStep u sB) X₀)
    (foldl_chainStep_subset u sB gens X₀) hX0 hfold
  -- Endpoint: `foldl gens X₀ ≈ im E` (same `rationalOpen`), the `↑u`-condition free via `hu`.
  have h_ro : rationalOpen (imagePieceDatum D E.T E.s hspanE).T
        (imagePieceDatum D E.T E.s hspanE).s =
      rationalOpen (gens.foldl (chainStep u sB) X₀).T (gens.foldl (chainStep u sB) X₀).s :=
    foldl_rationalOpen_eq_base (presheafValue_concretePair D) u sB
      (imagePieceDatum D E.T E.s hspanE).T hspan_u
      (fun v hv => (hu ⟨v, rationalOpen_subset_spa hv⟩ hv).1)
  exact flat_of_rationalOpen_eq (gens.foldl (chainStep u sB) X₀)
    (imagePieceDatum D E.T E.s hspanE) h_ro hfoldB

end ValuationSpectrum

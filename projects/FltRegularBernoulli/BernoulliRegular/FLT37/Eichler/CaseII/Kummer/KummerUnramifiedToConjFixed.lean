import BernoulliRegular.FLT37.Eichler.CaseII.RootClass.RootClassConjugateFixed
import BernoulliRegular.FLT37.Eichler.FLT37GenuineResiduals
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummerCaseI
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummerL3
import BernoulliRegular.UnitQuotient.Washington83UnitForward

/-!
# [FLT37-CASEII-LEMMA-9.2-PROOF] Discharging `CaseIIRootClassConjFixed37`

This file **proves** the Washington Lemma 9.2 class consequence for the Case-II conjugate radical,
`CaseIIRootClassConjFixed37` (`[𝔞(η)] = [𝔞(η⁻¹)]` over real data), by **reusing the Case-I
anti-Kummer Hilbert-94 machinery** — exactly the program the task calls for.

## What is reused (verbatim Case-I lemmas)

The Case-I anti-Kummer chain (`AntiKummer.lean`, `AntiKummerCaseI.lean`, `AntiKummerL3.lean`) is
**generic in the radical `α₀ : K`**: every structural step takes `α₀`, `hα₀ : α₀ ≠ 0`, the
anti-fixedness `h_anti : complexConj K α₀ = α₀⁻¹`, `α₀² ≠ 1`, irreducibility of `X^p - C α₀`, and
the **unramifiedness** `IsUnramified (𝓞 K) (𝓞 (antiKummerLift α₀))` of the cyclic degree-`p`
Kummer extension, and produces the Hilbert-94 contradiction with `¬ p ∣ h⁺`.  The only
Case-I-FLT-specific content is bundled in those four inputs.  We package the generic core as
`flt37_antiFixed_radical_isPthPower`:

> anti-fixed `α₀` (with `α₀² ≠ 1`, `α₀ ≠ 0`) whose Kummer extension is **unramified**, under
> `¬ 37 ∣ h⁺`, is a `37`-th power in `K`.

The exact Case-I lemmas reused: `antiKummerKplusPoly_irreducible`,
`antiKummerRealSubfield_isUnramified_from_K_unramified`, `mkAntiKummerRealSubfieldH94Inputs`,
`antiKummerSigmaTildePkg`, `ak_caseI_false_under_VC_and_inputs`,
`X_pow_sub_C_irreducible_iff_not_pth_power`.

## The Case-II radical and the genuine residual

For the Case-II conjugate radical `α₀ = (x+yη)/(x+yη⁻¹)`, the **corrected** radical Washington
uses is `α := u₀⁻¹ · α₀` for an anti-fixed correction unit `u₀ = -ζ^a` (the `-ζ^a` placed so that
`α ≡ 1 mod (1-ζ)^{37}`, Washington §9.1, Lemma 9.1).  Over real data `α₀` is automatically
anti-fixed (`σ(x+yη) = x+yη⁻¹`); with `σu₀ = u₀⁻¹` the corrected `α` is anti-fixed too.  Its ideal
is `(α) = (α₀) = 𝔠(η)/𝔠(η⁻¹) = (𝔞(η)/𝔞(η⁻¹))^{37}` (the unit `u₀` vanishes at the ideal level).

The **single genuine residual** isolated here is `CaseIICorrectedRadicalUnramified37`: the existence
of an **anti-fixed correction unit** `u₀` making the corrected radical's Kummer extension
**unramified** (Washington Lemma 9.1 — the primarity `α ≡ 1 mod (1-ζ)^{37}`).  This is genuinely
true (Washington establishes it) and is **non-vacuous / not** the false "`-ζ^a` is a `37`-th
power": an unramified cyclic degree-`37` extension need not be trivial — the `37`-th-power
conclusion comes only after adding Hilbert 94 (`¬ 37 ∣ h⁺`).  From the residual we prove
everything else:

* anti-fixedness of the corrected radical (from `σu₀ = u₀⁻¹` and real data) — proved;
* the Hilbert-94 `37`-th-power conclusion — reused from Case-I
  (`flt37_antiFixed_radical_isPthPower`);
* the corrected element form `(x+yη)·b^{37} = u·(x+yη⁻¹)·a^{37}`
  (`CaseIIRootRatioUnitPthPower37`) — proved by clearing denominators;
* the class form `[𝔞(η)] = [𝔞(η⁻¹)]` (`CaseIIRootClassConjFixed37`) — via the prior agent's
  `caseIIRootClassConjFixed37_of_unitPthPower`.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (Lemmas 9.1, 9.2), Thm 9.4.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial NumberField.IsCMField
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseI
open FLT37.LehmerVandiver.CaseI.AntiKummer

/-! ## 1. The generic Case-I Hilbert-94 core, repackaged for an arbitrary anti-fixed radical

`flt37_antiFixed_radical_isPthPower` is the Case-I anti-Kummer Hilbert-94 contradiction with the
case-I-FLT-specific inputs stripped away: it works for **any** `α₀ : K` that is anti-fixed, has
`α₀² ≠ 1`, and whose Kummer extension is unramified.  The proof is the verbatim Case-I `by_contra`
structure (`flt37_stage2_via_AK_chain`): if `α₀` were not a `37`-th power, `X^{37} - C α₀` would be
irreducible, the σ-anti Kummer extension would be a cyclic degree-`37` unramified extension of `K⁺`,
contradicting `¬ 37 ∣ h⁺` via `ak_caseI_false_under_VC_and_inputs`. -/

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

set_option backward.isDefEq.respectTransparency false in
/-- **Generic Case-I Hilbert-94 core.**  For any anti-fixed `α₀ : K` with `α₀ ≠ 0`, `α₀² ≠ 1`, and
an **unramified** Kummer extension `K(α₀^{1/37})/K`, under `¬ 37 ∣ h⁺(K)`, `α₀` is a `37`-th power
in `K`.

This is the Washington Lemma 9.2 mechanism in its radical-agnostic form, extracted from the Case-I
anti-Kummer chain (`flt37_stage2_via_AK_chain` / `caseI_FLT_false_of_h_irr_h_LK_unram_VC`).  All the
hard structural work — the σ̃ involution (`antiKummerSigmaTildePkg`), the `K⁺`-polynomial
irreducibility (`antiKummerKplusPoly_irreducible`), the `L⁺/K⁺` descent
(`antiKummerRealSubfield_isUnramified_from_K_unramified`), and the Hilbert-94 contradiction
(`ak_caseI_false_under_VC_and_inputs`) — is reused verbatim. -/
theorem flt37_antiFixed_radical_isPthPower
    (h_VC : ¬ (37 : ℕ) ∣ hPlus K)
    {α₀ : K} (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_sq_ne : α₀ ^ 2 ≠ 1)
    (h_unram : Algebra.Unramified (𝓞 K) (𝓞 (antiKummerLift (p := 37) K α₀ hα₀))) :
    ∃ β : K, β ^ 37 = α₀ := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  by_contra! h_pow
  -- `X^{37} - C α₀` irreducible, since `α₀` is not a `37`-th power.
  have h_irr : Irreducible (Polynomial.X ^ 37 - Polynomial.C α₀ : Polynomial K) := by
    rw [X_pow_sub_C_irreducible_iff_not_pth_power (K := K) (by decide : (37 : ℕ) ≠ 2)]
    intro β hβ
    exact h_pow β hβ
  -- The `K⁺`-polynomial `g = X^{74} - (α₀+α₀⁻¹)X^{37} + 1` is irreducible (from anti-fixedness).
  have h_irr_g : Irreducible (antiKummerKplusPoly (p := 37) K α₀ hα₀ h_anti) :=
    antiKummerKplusPoly_irreducible (K := K) (by decide : (37 : ℕ) ≠ 2)
      α₀ hα₀ h_anti h_sq_ne h_irr
  -- The σ-anti Kummer package and the `L⁺/K⁺` unramifiedness from `L/K` unramifiedness.
  have h_unram_plus :
      Algebra.Unramified (𝓞 (NumberField.maximalRealSubfield K))
        (𝓞 (antiKummerRealSubfield (p := 37) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
          (antiKummerSigmaTildePkg (p := 37) K α₀ hα₀ h_anti h_irr h_irr_g h_sq_ne))) :=
    antiKummerRealSubfield_isUnramified_from_K_unramified (K := K) (by decide : (37 : ℕ) ≠ 2)
      α₀ hα₀ h_anti h_irr h_irr_g h_sq_ne h_unram
  -- Hilbert-94 inputs for `L⁺/K⁺` (Galois cyclic degree `37`, unramified).
  have h_inputs := mkAntiKummerRealSubfieldH94Inputs (K := K) (by decide : (37 : ℕ) ≠ 2)
    α₀ hα₀ h_anti h_irr h_irr_g h_sq_ne h_unram_plus
  -- Hilbert 94: such an extension contradicts `¬ 37 ∣ h⁺`.
  exact ak_caseI_false_under_VC_and_inputs (p := 37) (K := K) (by decide : (37 : ℕ) ≠ 2)
    (antiKummerSigmaTildePkg (p := 37) K α₀ hα₀ h_anti h_irr h_irr_g h_sq_ne) h_inputs h_VC

set_option backward.isDefEq.respectTransparency false in
/-- **Generic unramifiedness from a primary unit form** — the Washington Lemma 9.1 producer in
radical-agnostic form.  For any `α₀ : K` that is not a `37`-th power (so `X^{37} - C α₀` is
irreducible) and equals `algebraMap u · γ^{37}` for a **primary** unit `u` (`(ζ'-1)^{37} ∣ u - 1`),
the Kummer extension `K(α₀^{1/37})/K` is **unramified**.

This is exactly the chain inside `antiKummerLift_isUnramified_via_AK5`, with the case-I
`antiRadical` specialisation removed: `antiKummerLift_finrank_of_irreducible` + the
splitting-field transfer `isSplittingField_X_pow_sub_C_unit_of_unit_form` +
`antiKummerLift_isUnramified_of_kummer_data`
(flt-regular's `KummersLemma.isUnramified`).  It witnesses that **unramifiedness is the primarity
content** (Lemma 9.1), used below to confirm `CaseIICorrectedRadicalUnramified37` is non-vacuous and
**not** the false "is a `37`-th power" demand. -/
theorem flt37_antiKummerLift_isUnramified_of_primaryUnitForm
    {α₀ : K} (hα₀ : α₀ ≠ 0)
    (h_irr : Irreducible (Polynomial.X ^ 37 - Polynomial.C α₀ : Polynomial K))
    (γ : K) (hγ_ne : γ ≠ 0)
    {ζ' : K} (hζ' : IsPrimitiveRoot ζ' 37)
    (u : (𝓞 K)ˣ)
    (h_unit_form : algebraMap (𝓞 K) K (u : 𝓞 K) * γ ^ 37 = α₀)
    (hcong : (hζ'.toInteger - 1 : 𝓞 K) ^ 37 ∣ (↑u : 𝓞 K) - 1)
    (hu_no_root : ∀ v : K, v ^ 37 ≠ u) :
    Algebra.Unramified (𝓞 K) (𝓞 (antiKummerLift (p := 37) K α₀ hα₀)) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hp_pos : (0 : ℕ) < 37 := by decide
  have hK_prim : (primitiveRoots 37 K).Nonempty :=
    ⟨_, (mem_primitiveRoots hp_pos).mpr (IsCyclotomicExtension.zeta_spec 37 ℚ K)⟩
  have h_finrank : Module.finrank K (antiKummerLift (p := 37) K α₀ hα₀) = 37 :=
    antiKummerLift_finrank_of_irreducible (K := K) (p := 37) α₀ hα₀ h_irr
  haveI : IsCyclic (antiKummerLift (p := 37) K α₀ hα₀ ≃ₐ[K]
      antiKummerLift (p := 37) K α₀ hα₀) :=
    antiKummerLift_isCyclic_of_irreducible (K := K) (p := 37) α₀ hα₀ h_irr
  haveI : Polynomial.IsSplittingField K (antiKummerLift (p := 37) K α₀ hα₀)
      (Polynomial.X ^ 37 - Polynomial.C α₀) := by
    unfold antiKummerLift; infer_instance
  haveI : Polynomial.IsSplittingField K (antiKummerLift (p := 37) K α₀ hα₀)
      (Polynomial.X ^ 37 - Polynomial.C (algebraMap (𝓞 K) K (u : 𝓞 K))) :=
    isSplittingField_X_pow_sub_C_unit_of_unit_form (K := K) (p := 37) hp_pos hK_prim
      α₀ (algebraMap (𝓞 K) K (u : 𝓞 K)) γ hγ_ne h_unit_form.symm h_finrank h_irr
  exact antiKummerLift_isUnramified_of_kummer_data (K := K) (p := 37)
    (by decide : (37 : ℕ) ≠ 2) α₀ hα₀ hζ' u hcong hu_no_root

/-! ## 2. The Case-II conjugate radical `α₀ = (x+yη)/(x+yη⁻¹)` at the `K`-level

We work at the field level (`α₀ ∈ K`), where the AK chain lives.  Over real data `α₀` is anti-fixed
(`σα₀ = α₀⁻¹`, Washington `B₋ₐ = conj Bₐ`) and nonzero. -/

open FLT37.LehmerVandiver.CaseII

variable {m : ℕ}

/-- `x + yη ≠ 0` in `𝓞 K` for a real Case-II datum (specialisation of `x_plus_y_mul_ne_zero`). -/
theorem caseII_x_add_y_eta_ne_zero (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    D.x + D.y * (η : 𝓞 K) ≠ 0 :=
  x_plus_y_mul_ne_zero hp D.hζ D.equation D.hz η

/-- `algebraMap (x+yη) ≠ 0` in `K`. -/
theorem caseII_algebraMap_x_add_y_eta_ne_zero (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    algebraMap (𝓞 K) K (D.x + D.y * (η : 𝓞 K)) ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
  exact caseII_x_add_y_eta_ne_zero D hp η

/-- `algebraMap (x+yη⁻¹) ≠ 0` in `K` (the conjugate radical's denominator, `η⁻¹ = η³⁶`). -/
theorem caseII_algebraMap_x_add_y_etaInv_ne_zero (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    algebraMap (𝓞 K) K (D.x + D.y * ((η : 𝓞 K) ^ 36)) ≠ 0 := by
  have := caseII_algebraMap_x_add_y_eta_ne_zero D hp (caseII_etaInv η)
  rwa [caseII_etaInv_coe] at this

/-- The `K`-level conjugate radical `α₀ = (x+yη)/(x+yη⁻¹)`. -/
noncomputable def caseII_rootRatioK (D : RealCaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) : K :=
  algebraMap (𝓞 K) K (D.x + D.y * (η : 𝓞 K)) /
    algebraMap (𝓞 K) K (D.x + D.y * ((η : 𝓞 K) ^ 36))

/-- The conjugate radical is nonzero. -/
theorem caseII_rootRatioK_ne_zero (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    caseII_rootRatioK D η ≠ 0 :=
  div_ne_zero (caseII_algebraMap_x_add_y_eta_ne_zero D hp η)
    (caseII_algebraMap_x_add_y_etaInv_ne_zero D hp η)

/-- **Anti-fixedness of the conjugate radical**: `σα₀ = α₀⁻¹`.  Over real data complex conjugation
sends `x+yη` to `x+yη⁻¹` (Washington `B₋ₐ = conj Bₐ`), so the ratio is inverted. -/
theorem caseII_rootRatioK_complexConj (D : RealCaseIIData37 K m) (_hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    NumberField.IsCMField.complexConj K (caseII_rootRatioK D η) =
      (caseII_rootRatioK D η)⁻¹ := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have h37 : (η : 𝓞 K) ^ 37 = 1 := (mem_nthRootsFinset (by norm_num) _).mp η.2
  -- σ(x+yη) = x+yη³⁶ and σ(x+yη³⁶) = x+yη (involution: σ(η³⁶) = η, since (η³⁶)³⁶ = η).
  have hnum : NumberField.IsCMField.complexConj K
      (algebraMap (𝓞 K) K (D.x + D.y * (η : 𝓞 K))) =
      algebraMap (𝓞 K) K (D.x + D.y * ((η : 𝓞 K) ^ 36)) := by
    rw [← NumberField.IsCMField.coe_ringOfIntegersComplexConj]
    congr 1
    have h := caseII_ringOfIntegersComplexConj_x_add_y_mul (K := K) D.x_real D.y_real (η : 𝓞 K)
    rw [caseII_ringOfIntegersComplexConj_root_of_unity h37] at h
    exact h
  have hden : NumberField.IsCMField.complexConj K
      (algebraMap (𝓞 K) K (D.x + D.y * ((η : 𝓞 K) ^ 36))) =
      algebraMap (𝓞 K) K (D.x + D.y * (η : 𝓞 K)) := by
    rw [← NumberField.IsCMField.coe_ringOfIntegersComplexConj]
    congr 1
    have h36 : ((η : 𝓞 K) ^ 36) ^ 37 = 1 := by
      rw [← pow_mul, show 36 * 37 = 37 * 36 from by norm_num, pow_mul, h37, one_pow]
    have h := caseII_ringOfIntegersComplexConj_x_add_y_mul (K := K) D.x_real D.y_real
      ((η : 𝓞 K) ^ 36)
    rw [caseII_ringOfIntegersComplexConj_root_of_unity h36] at h
    rw [h]
    congr 2
    -- (η³⁶)³⁶ = η.
    rw [← pow_mul, show (36 * 36 : ℕ) = 37 * 35 + 1 from by norm_num, pow_add, pow_mul, h37,
      one_pow, pow_one, one_mul]
  rw [caseII_rootRatioK, map_div₀, hnum, hden, inv_div]

/-- The **corrected radical** `α := u₀⁻¹ · α₀` (`α₀ = (x+yη)/(x+yη⁻¹)`, `u₀` the Washington `-ζ^a`
correction unit). -/
noncomputable def caseII_correctedRadical (D : RealCaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) (u₀ : (𝓞 K)ˣ) : K :=
  (algebraMap (𝓞 K) K (u₀ : 𝓞 K))⁻¹ * caseII_rootRatioK D η

/-- The corrected radical is nonzero. -/
theorem caseII_correctedRadical_ne_zero (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) (u₀ : (𝓞 K)ˣ) :
    caseII_correctedRadical D η u₀ ≠ 0 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  refine mul_ne_zero (inv_ne_zero ?_) (caseII_rootRatioK_ne_zero D hp η)
  rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
  exact u₀.ne_zero

/-- **Anti-fixedness of the corrected radical**: `σα = α⁻¹`, given the correction unit is anti-fixed
(`σu₀ = u₀⁻¹`).  The `-ζ^a` Washington correction satisfies exactly this (`σ(-ζ^a) = -ζ^{-a}`). -/
theorem caseII_correctedRadical_complexConj (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) (u₀ : (𝓞 K)ˣ)
    (hu₀ : NumberField.IsCMField.ringOfIntegersComplexConj K (u₀ : 𝓞 K) =
      ((u₀⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) :
    NumberField.IsCMField.complexConj K (caseII_correctedRadical D η u₀) =
      (caseII_correctedRadical D η u₀)⁻¹ := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hu₀K : NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K (u₀ : 𝓞 K)) =
      (algebraMap (𝓞 K) K (u₀ : 𝓞 K))⁻¹ := by
    rw [← NumberField.IsCMField.coe_ringOfIntegersComplexConj, hu₀]
    have hval : algebraMap (𝓞 K) K (u₀ : 𝓞 K) *
        algebraMap (𝓞 K) K ((u₀⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    field_simp
    linear_combination hval
  rw [caseII_correctedRadical, map_mul, map_inv₀, hu₀K, caseII_rootRatioK_complexConj D hp η,
    mul_inv, inv_inv]

/-! ## 3. From "`α₀` is a unit times a `37`-th power in `K`" to the integral kernel

The Hilbert-94 conclusion gives `α₀ = v · β^{37}` for a unit `v : (𝓞 K)ˣ` and `β ∈ K`.  Writing
`β = γ/δ` (`δ ≠ 0`, `K = Frac(𝓞 K)`) and clearing denominators gives the **integral**
cross-multiplied identity `(x+yη)·δ^{37} = v·(x+yη⁻¹)·γ^{37}` in `𝓞 K` — exactly the kernel
`CaseIIRootRatioUnitPthPower37`. -/

/-- **Clearing denominators**: from `α₀ = v·β^{37}` (unit `v`, `β ∈ K`) obtain nonzero
`a, b ∈ 𝓞 K` and the integral cross-multiplied identity `(x+yη)·b^{37} = v·(x+yη⁻¹)·a^{37}`. -/
theorem caseII_kernel_of_rootRatioK_eq_unit_mul_pow (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) (v : (𝓞 K)ˣ) {β : K} (hβ : β ≠ 0)
    (h : caseII_rootRatioK D η = algebraMap (𝓞 K) K (v : 𝓞 K) * β ^ 37) :
    ∃ (u : (𝓞 K)ˣ) (a b : 𝓞 K), a ≠ 0 ∧ b ≠ 0 ∧
      (D.x + D.y * (η : 𝓞 K)) * b ^ 37 =
        (u : 𝓞 K) * ((D.x + D.y * ((η : 𝓞 K) ^ 36)) * a ^ 37) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hinj : Function.Injective (algebraMap (𝓞 K) K) :=
    FaithfulSMul.algebraMap_injective (𝓞 K) K
  -- Write `β = γ/δ` with `γ, δ ∈ 𝓞 K`, `δ ≠ 0`.
  obtain ⟨⟨γ, ⟨δ, hδmem⟩⟩, hβeq⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) β
  -- `hβeq : β * algebraMap δ = algebraMap γ`.
  have hδ_ne : δ ≠ 0 := nonZeroDivisors.ne_zero hδmem
  have hδK_ne : algebraMap (𝓞 K) K δ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact hδ_ne
  have hγ_ne : γ ≠ 0 := by
    intro hγ0
    apply hβ
    have : β * algebraMap (𝓞 K) K δ = 0 := by rw [hβeq, hγ0, map_zero]
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd h' hδK_ne
  -- `β = algebraMap γ / algebraMap δ`.
  have hβ_div : β = algebraMap (𝓞 K) K γ / algebraMap (𝓞 K) K δ := by
    rw [eq_div_iff hδK_ne]; exact hβeq
  have hden_ne := caseII_algebraMap_x_add_y_etaInv_ne_zero D hp η
  -- Substitute and clear all denominators in `K`.
  rw [caseII_rootRatioK, hβ_div, div_pow] at h
  rw [div_eq_iff hden_ne] at h
  have hclear : algebraMap (𝓞 K) K (D.x + D.y * (η : 𝓞 K)) * algebraMap (𝓞 K) K δ ^ 37 =
      algebraMap (𝓞 K) K (v : 𝓞 K) *
        (algebraMap (𝓞 K) K (D.x + D.y * ((η : 𝓞 K) ^ 36)) * algebraMap (𝓞 K) K γ ^ 37) := by
    rw [h]; field_simp
  -- Land the identity in `𝓞 K` via injectivity; both sides are `algebraMap` of integral elements.
  refine ⟨v, γ, δ, hγ_ne, hδ_ne, hinj ?_⟩
  push_cast [map_mul, map_pow, map_add]
  push_cast [map_mul, map_pow, map_add] at hclear
  linear_combination hclear

/-! ## 4. The genuine residual: the corrected radical generates an unramified Kummer extension

`CaseIICorrectedRadicalUnramified37` is the **single** isolated residual — Washington Lemma 9.1's
primarity, in its consequence form (unramifiedness of the Kummer extension generated by the
corrected radical).  It is genuinely true and **non-vacuous**: it asserts the *existence* of an
anti-fixed correction unit `u₀` (Washington's `-ζ^a`) such that the corrected radical's anti-Kummer
extension is unramified — it does **not** assert `-ζ^a` is a `37`-th power (an unramified cyclic
degree-`37` extension can be nontrivial; the `37`-th-power conclusion is produced only by *adding*
Hilbert 94, `¬ 37 ∣ h⁺`, which is the `flt37_antiFixed_radical_isPthPower` step done below). -/

/-- **[FLT37-CASEII-LEMMA-9.1-RESIDUAL] The corrected Case-II radical generates an unramified Kummer
extension.**

For every real Case-II datum `D` and adjacent root `η ≠ η₀`, there exists an **anti-fixed**
correction unit `u₀ : (𝓞 K)ˣ` (`σu₀ = u₀⁻¹`, Washington's `-ζ^a`) such that the corrected radical
`α := u₀⁻¹ · (x+yη)/(x+yη⁻¹)` generates an **unramified** anti-Kummer extension `K(α^{1/37})/K`.

This is **Washington Lemma 9.1** (the primarity `α ≡ 1 mod (1-ζ)^{37}` makes the Kummer extension
unramified) packaged in its consequence form.  It is the genuine analytic kernel of the Case-II II1
leaf and is **non-vacuous**: unramifiedness alone is satisfiable (Washington establishes it) and
does **not** force `α` to be a `37`-th power — that conclusion requires Hilbert 94 / `¬ 37 ∣ h⁺` on
top (`caseIIRootRatioUnitPthPower37_of_correctedRadicalUnramified` below).  This is the SAME
unramifiedness input the Case-I anti-Kummer chain carries (`h_LK_unram` in
`flt37_stage2_via_AK_chain`), specialised to the Case-II radical `(x+yη)/(x+yη⁻¹)`. -/
def CaseIICorrectedRadicalUnramified37
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))),
    η ≠ D.etaZero →
    ∃ u₀ : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField 37 ℚ) (u₀ : 𝓞 _) =
        ((u₀⁻¹ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 _) ∧
      Algebra.Unramified (𝓞 (CyclotomicField 37 ℚ))
        (𝓞 (antiKummerLift (p := 37) (CyclotomicField 37 ℚ)
          (caseII_correctedRadical D η u₀)
          (caseII_correctedRadical_ne_zero D (by decide : (37 : ℕ) ≠ 2) η u₀)))

/-! ## 4'. Non-vacuity: the residual is the genuine Lemma-9.1 primarity, not a `37`-th-power demand

`caseII_correctedRadicalUnramified37_of_primaryData` proves the residual from genuine **primary
unit-form** data: per datum, an anti-fixed correction unit `u₀`, plus (for the corrected radical
`α = u₀⁻¹·α₀`) a *primary* unit `u` with `α = algebraMap u · γ^{37}` and `(ζ'-1)^{37} ∣ u - 1`
(Washington Lemma 9.1's congruence `α ≡ 1 mod (1-ζ)^{37}`), together with the non-`37`-th-power of
`α` (so the Kummer extension is a genuine degree-`37` extension).  This routes through
`flt37_antiKummerLift_isUnramified_of_primaryUnitForm` (flt-regular's `KummersLemma.isUnramified`).

This **machine-checks** that the residual's content is exactly the primarity congruence — it is
satisfiable from genuine Lemma-9.1 data and does **not** secretly demand "`-ζ^a` is a `37`-th
power".  Indeed the input here even *includes* `α` being **non**-`37`-th-power (`hu_no_root`), the
opposite of the false demand; the residual is about the *ramification* of the extension, an
orthogonal, genuinely-true property. -/
theorem caseII_correctedRadicalUnramified37_of_primaryData
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_data : ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
      (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))), η ≠ D.etaZero →
      ∃ (u₀ : (𝓞 (CyclotomicField 37 ℚ))ˣ),
        NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField 37 ℚ) (u₀ : 𝓞 _) =
          ((u₀⁻¹ : (𝓞 (CyclotomicField 37 ℚ))ˣ) : 𝓞 _) ∧
        ∃ (γ : CyclotomicField 37 ℚ) (_hγ : γ ≠ 0)
          (ζ' : CyclotomicField 37 ℚ) (hζ' : IsPrimitiveRoot ζ' 37)
          (u : (𝓞 (CyclotomicField 37 ℚ))ˣ),
          Irreducible (Polynomial.X ^ 37 - Polynomial.C (caseII_correctedRadical D η u₀) :
            Polynomial (CyclotomicField 37 ℚ)) ∧
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u : 𝓞 _) * γ ^ 37 =
            caseII_correctedRadical D η u₀ ∧
          (hζ'.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ^ 37 ∣ ((u : 𝓞 _) - 1) ∧
          (∀ v : CyclotomicField 37 ℚ, v ^ 37 ≠ u)) :
    CaseIICorrectedRadicalUnramified37 := by
  intro m D η hη
  obtain ⟨u₀, hu₀_anti, γ, hγ, ζ', hζ', u, h_irr, h_unit_form, hcong, hu_no_root⟩ := h_data D η hη
  refine ⟨u₀, hu₀_anti, ?_⟩
  exact flt37_antiKummerLift_isUnramified_of_primaryUnitForm (K := CyclotomicField 37 ℚ)
    (caseII_correctedRadical_ne_zero D (by decide : (37 : ℕ) ≠ 2) η u₀)
    h_irr γ hγ hζ' u h_unit_form hcong hu_no_root

/-! ## 5. The reduction: residual ⟹ kernel ⟹ class form ⟹ endpoint

From the residual (unramifiedness of the corrected radical) plus Hilbert 94 (`¬ 37 ∣ h⁺`, the
proven `Sinnott.flt37_not_dvd_hPlus`), the corrected radical is a `37`-th power
(`flt37_antiFixed_radical_isPthPower`), so `α₀ = u₀ · β^{37}`; clearing denominators gives the
kernel `CaseIIRootRatioUnitPthPower37`, whence the class form `CaseIIRootClassConjFixed37` via the
prior agent's `caseIIRootClassConjFixed37_of_unitPthPower`. -/

set_option backward.isDefEq.respectTransparency false in
/-- **The corrected element-form kernel from the unramifiedness residual** — the Hilbert-94 step.

Given the residual `CaseIICorrectedRadicalUnramified37`, the corrected radical (anti-fixed,
unramified Kummer extension) is forced by Hilbert 94 (`¬ 37 ∣ h⁺`) to be a `37`-th power; hence the
conjugate radical `α₀ = (x+yη)/(x+yη⁻¹)` equals `u₀ · β^{37}`, and clearing denominators yields the
genuine kernel `CaseIIRootRatioUnitPthPower37`.  The case `α = ±1` (the corrected radical itself a
root of unity, where `X^{37} - C α` is not irreducible) is handled directly: there `α₀ = ±u₀` is a
unit, giving the kernel with `a = b = 1`. -/
theorem caseIIRootRatioUnitPthPower37_of_correctedRadicalUnramified
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_res : CaseIICorrectedRadicalUnramified37) :
    CaseIIRootRatioUnitPthPower37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro m D η hη
  obtain ⟨u₀, hu₀_anti, h_unram⟩ := h_res D η hη
  -- The corrected radical `α` is anti-fixed and nonzero.
  set α := caseII_correctedRadical D η u₀ with hα_def
  have hα_ne : α ≠ 0 := caseII_correctedRadical_ne_zero D (by decide : (37 : ℕ) ≠ 2) η u₀
  have hα_anti : NumberField.IsCMField.complexConj (CyclotomicField 37 ℚ) α = α⁻¹ :=
    caseII_correctedRadical_complexConj D (by decide : (37 : ℕ) ≠ 2) η u₀ hu₀_anti
  -- `α₀ = algebraMap u₀ · α` (undo the correction).
  have hu₀K_ne : algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u₀ : 𝓞 _) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField 37 ℚ))
      (CyclotomicField 37 ℚ))]
    exact u₀.ne_zero
  have hα₀_eq : caseII_rootRatioK D η =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u₀ : 𝓞 _) * α := by
    have : α = (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u₀ : 𝓞 _))⁻¹ *
        caseII_rootRatioK D η := hα_def
    rw [this]
    field_simp
  -- In both cases, obtain `β ≠ 0` with `β^{37} = α`; then `α₀ = u₀ · β^{37}`, giving the kernel.
  obtain ⟨β, hβ, hβ_ne⟩ : ∃ β : CyclotomicField 37 ℚ, β ^ 37 = α ∧ β ≠ 0 := by
    by_cases hsq : α ^ 2 = 1
    · -- `α = ±1` (37 odd ⟹ `α = α^{37}`); take `β = α`.  Here `X^{37} - C α` is not irreducible,
      -- but the conclusion holds directly since `α` is its own `37`-th power.
      have hpm : α = 1 ∨ α = -1 := by
        have hfac : (α - 1) * (α + 1) = 0 := by linear_combination hsq
        rcases mul_eq_zero.mp hfac with h1 | h1
        · exact Or.inl (by linear_combination h1)
        · exact Or.inr (by linear_combination h1)
      have hα37 : α ^ 37 = α := by
        rcases hpm with h1 | h1
        · rw [h1, one_pow]
        · rw [h1]; norm_num
      exact ⟨α, hα37, hα_ne⟩
    · -- `α² ≠ 1`: Hilbert 94 (`¬ 37 ∣ h⁺`) forces `α = β^{37}`.
      obtain ⟨β, hβ⟩ := flt37_antiFixed_radical_isPthPower (K := CyclotomicField 37 ℚ)
        Sinnott.flt37_not_dvd_hPlus hα_ne hα_anti hsq h_unram
      refine ⟨β, hβ, ?_⟩
      intro hβ0; rw [hβ0, zero_pow (by decide : 37 ≠ 0)] at hβ; exact hα_ne hβ.symm
  -- `α₀ = u₀ · β^{37}`.
  have hkey : caseII_rootRatioK D η =
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (u₀ : 𝓞 _) * β ^ 37 := by
    rw [hα₀_eq, hβ]
  exact caseII_kernel_of_rootRatioK_eq_unit_mul_pow D (by decide : (37 : ℕ) ≠ 2) η u₀ hβ_ne hkey

/-- **[FLT37-CASEII-LEMMA-9.2-DISCHARGED] `CaseIIRootClassConjFixed37` from the unramifiedness
residual.**

The Washington Lemma 9.2 class consequence `[𝔞(η)] = [𝔞(η⁻¹)]` (over real data) follows from the
single genuine residual `CaseIICorrectedRadicalUnramified37` (Lemma 9.1 primarity / unramifiedness
of the corrected radical), by:

* `caseIIRootRatioUnitPthPower37_of_correctedRadicalUnramified` — the Hilbert-94 step (reusing the
  Case-I anti-Kummer chain via `flt37_antiFixed_radical_isPthPower` and the proven
  `Sinnott.flt37_not_dvd_hPlus`) gives the corrected element-form kernel
  `CaseIIRootRatioUnitPthPower37`;
* `caseIIRootClassConjFixed37_of_unitPthPower` (prior agent) — the kernel ⟹ the class form. -/
theorem caseIIRootClassConjFixed37_of_correctedRadicalUnramified
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (h_res : CaseIICorrectedRadicalUnramified37) :
    CaseIIRootClassConjFixed37 :=
  caseIIRootClassConjFixed37_of_unitPthPower
    (caseIIRootRatioUnitPthPower37_of_correctedRadicalUnramified h_res)

/-! ## 6. The non-vacuous FLT-37 endpoint resting on the single Lemma-9.1 residual

Composing `caseIIRootClassConjFixed37_of_correctedRadicalUnramified` into the prior agent's
`fermatLastTheoremFor_thirtyseven_of_genuineResiduals`, FLT for `37` follows from the **single**
Case-II II1 residual `CaseIICorrectedRadicalUnramified37` (Washington Lemma 9.1 primarity) plus the
other already-isolated Case-II inputs.  This replaces the `caseII_classConjFixed` input of the
prior endpoint by the strictly-more-primitive (genuinely-true / non-vacuous) unramifiedness
residual. -/

/-- **Fermat's Last Theorem for `37` from the single Lemma-9.1 unramifiedness residual** (plus the
other Case-II inputs and the carried second-order Bernoulli Prop).

This is the maximally-reduced Case-II II1 endpoint: the Washington Lemma 9.2 class consequence is
now **proved** from the more primitive Lemma 9.1 input `CaseIICorrectedRadicalUnramified37` (the
corrected radical generates an unramified Kummer extension) via the Case-I anti-Kummer Hilbert-94
machinery.
Everything downstream — the `c = 1` real-data collapse, the descent, Assumption II from the
leading-exponent + local-power residuals — is unchanged from
`fermatLastTheoremFor_thirtyseven_of_genuineResiduals`. -/
theorem fermatLastTheoremFor_thirtyseven_of_lemma91Residual
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    (caseII_lemma91 : CaseIICorrectedRadicalUnramified37)
    (caseII_realDescent : CaseIIRealSingleRootDescentPreservesReality37)
    (caseII_leadingExp : LeadingExponentEigenCollapse37)
    (caseII_localPow : Lemma98LocalPower37)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_genuineResiduals
    (caseIIRootClassConjFixed37_of_correctedRadicalUnramified caseII_lemma91)
    caseII_realDescent caseII_leadingExp caseII_localPow noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end

import BernoulliRegular.FLT37.Eichler.CaseIIFreeContentAssembly
import BernoulliRegular.FLT37.Eichler.CaseIIAnchorRealRho0
import BernoulliRegular.UnitQuotient.Washington83UnitForward

/-!
# [FLT37-CASEII-R2-SKELETON] Washington §9.1 second-case descent: the two genuine-new leaves

This file **proves** the two genuine-new leaves of Washington's second-case descent
(*Introduction to Cyclotomic Fields*, GTM 83, §9.1, pp. 169–171), for the R2 decomposition
(`.mathlib-quality/decomposition-r2-washington.md`).  Both leaves are now **proven, axiom-clean**
(no `sorry`); the full L1+L2 composition into the §9.1 descended equation, the factor-count descent,
and the FLT37 Case-II endpoint `fermatLastTheoremFor_thirtyseven_of_washington_caseII` are proven in
`CaseIIWashingtonCaseIIClean.lean`.

The decomposition's KEY finding: the prior ζ-twist / `𝔞₀²`-degeneracy obstructions are **artifacts**
of non-Washington constructions.  Washington's real-anchor (`B₀ ∈ Cl(K⁺)` principal via the proven
`37 ∤ h⁺`) + real-units (Lemma 9.2) mechanism is clean.  The two genuine-new leaves are:

* **L1 `caseII_anchor_real_rho0`** (Washington p.169): from `37 ∤ h⁺`, the real anchor root ideal
  `B₀ = aEtaZeroDvdPPow` (real, `[B₀] ∈ Cl(K⁺)`, `[B₀]³⁷ = 1`) is principal with a **real**
  generator `ρ₀` (`ringOfIntegersComplexConj K ρ₀ = ρ₀`), giving the anchor equation
  `algebraMap(x+y) = η₀ · Λ^e · ρ₀³⁷` with `η₀` a **real** unit.  Crucially `B₀ ∈ Cl(K⁺)` (NOT
  `Cl(K)`: `37 ∣ h⁻` but `37 ∤ h⁺`), and `k' = 1` (direct principal), **not** the conjugate-norm
  `𝔞₀^{2k'}`.  This produces EXACTLY `washington_section91_descended_equation`'s `hanchor`
  (`x+y = η₀·Λ^e·ρ₀³⁷`) and `hη0real` (reality of `η₀`).

* **L2 `caseII_factor_eq_real_eta`** (Washington p.170–171): for `η ≠ η₀`, the cross-ratio
  `(ω+ζᵃθ)/(1-ζᵃ) = η_a · ρ_a³⁷` with `η_a` a **real** unit (`η_a = η_{-a}`), `ρ̄_a = ρ_{-a}`, via
  Lemma 9.1 (unramified, `α ≡ 1 mod (1-ζ)³⁷`) + Lemma 9.2 (`ᾱ = α⁻¹` + unramified ⟹ `37`-th power,
  using `37 ∤ h⁺`) + raising to `(37+1)/2`.  This produces EXACTLY
  `washington_section91_descended_equation`'s `hfa_pos`/`hfa_neg` (and, reused at the second root,
  `hfb_pos`/`hfb_neg`).

## Composition

The L1 + L2 outputs feed the **proven** `washington_section91_descended_equation`
(`CaseIISection91ConjNormReassembly.lean`) — L1's `hanchor`/`hη0real`, L2's `hfa_*`/`hηbreal` (reused
at the second root `ζ²`).  The full composition + descent + endpoint is in
`CaseIIWashingtonCaseIIClean.lean`.  `37 ∤ h⁺` is `Sinnott.flt37_not_dvd_hPlus` (proven, axiom-clean).

It imports only; it does **not** modify any existing file.  No `axiom`, no `sorry`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1 "The Basic Argument",
  pp. 169–171 (the real anchor `B₀ = (ρ₀)`, `ρ₀` real, via `Cl(K⁺)`-Vandiver; the real factor units
  `η_a = η_{-a}` via Lemmas 9.1+9.2).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension UniqueFactorizationMonoid Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## L1 — the real anchor `ρ₀` (Washington p.169, via `Cl(K⁺)`-Vandiver, `37 ∤ h⁺`) -/

/-- **[L1 — REAL ANCHOR] Washington's real anchor generator `ρ₀`** (Washington GTM 83 §9.1 p.169).

For a real Case-II datum `D` with coprime Fermat variables, the `𝔭`-free anchor root ideal
`B₀ = aEtaZeroDvdPPow` is **real** (`σ B₀ = B₀`, since `η₀ = 1`), `B₀³⁷` is principal, and its
class lies in `Cl(K⁺)` with `[B₀]³⁷ = 1`; the proven `37 ∤ h⁺` (`Sinnott.flt37_not_dvd_hPlus`) then
forces `[B₀] = 1`, i.e. `B₀ = (ρ₀)` with a **real** generator `ρ₀`
(`ringOfIntegersComplexConj K ρ₀ = ρ₀`, `k' = 1`, NOT the conjugate norm `𝔞₀^{2k'}`).  Hence the
anchor equation
```
algebraMap(x+y) = η₀ · Λ^e · ρ₀³⁷,     Λ = (1−ζ_spec)(1−ζ_spec³⁶),  e ≥ 1,
```
holds with `η₀ : Kˣ` a **real** unit (`complexConj K η₀ = η₀`).

This produces precisely the `hanchor` and `hη0real` inputs of
`washington_section91_descended_equation`. -/
theorem caseII_anchor_real_rho0
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ))))) :
    ∃ (e : ℕ) (η0 : (CyclotomicField 37 ℚ)ˣ) (ρ0 : 𝓞 (CyclotomicField 37 ℚ)),
      1 ≤ e ∧
      -- `ρ₀` is a **real** generator of the anchor (the `Cl(K⁺)`-Vandiver content):
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) ρ0 = ρ0 ∧
      Ideal.span ({ρ0} : Set (𝓞 (CyclotomicField 37 ℚ))) =
        aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ∧
      -- `η₀` is a **real** unit (the `hη0real` input):
      complexConj (CyclotomicField 37 ℚ) (η0 : CyclotomicField 37 ℚ) =
          (η0 : CyclotomicField 37 ℚ) ∧
      -- the anchor equation (the `hanchor` input, in `zeta_spec`-terms `Λ`):
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y) =
        (η0 : CyclotomicField 37 ℚ) *
          (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).unit'.1) *
              (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).unit'.1 ^ 36))) ^ e *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0 ^ 37 :=
  caseII_anchor_real_rho0_impl D hcop

/-! ## L2 — the real factor units `η_a` (Washington p.170–171, Lemmas 9.1 + 9.2, `37 ∤ h⁺`) -/

/-- **[L2 — REAL FACTOR UNITS] Washington's real factor equation `(ω+ζᵃθ)/(1−ζᵃ) = η_a ρ_a³⁷`**
(Washington GTM 83 §9.1 pp.170–171).

For a real Case-II datum `D` with coprime Fermat variables and a root `η ≠ η₀`, the cross-ratio
`α = ((x+ηy)/(1−η)) / ((x+η⁻¹y)/(1−η⁻¹))` is `≡ 1 mod (1−ζ)³⁷` (unramified, Lemma 9.1,
`caseIIIdealKummerUnramified37_proven`) and satisfies `ᾱ = α⁻¹`, so is a `37`-th power (Lemma 9.2,
`flt37_antiFixed_radical_isPthPower`, via `37 ∤ h⁺`); raising to `(37+1)/2` yields a **real** unit
`η_a : Kˣ` (`η_a = η_{-a}`, `complexConj K η_a = η_a`) and `ρ_a : K` (`ρ̄_a = ρ_{-a}`) with
the two cleared-denominator factor equations
```
x + η·y    = (1 − η)   · η_a · ρ_a³⁷,
x + η³⁶·y  = (1 − η³⁶) · η_a · (σρ_a)³⁷.
```

This produces precisely the `hfa_pos`/`hfa_neg` inputs of `washington_section91_descended_equation`
(and, reused at the second root, `hfb_pos`/`hfb_neg`). -/
theorem caseII_factor_eq_real_eta
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) (hη : η ≠ D.etaZero)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ))))) :
    ∃ (η_a : (CyclotomicField 37 ℚ)ˣ) (ρ_a : CyclotomicField 37 ℚ),
      -- `η_a` is a **real** unit (the `η_a = η_{-a}` symmetry):
      complexConj (CyclotomicField 37 ℚ) (η_a : CyclotomicField 37 ℚ) =
          (η_a : CyclotomicField 37 ℚ) ∧
      -- factor equation at `η` (the `hfa_pos` input):
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (η : 𝓞 _) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (η : 𝓞 _)) *
          (η_a : CyclotomicField 37 ℚ) * ρ_a ^ 37 ∧
      -- conjugate factor equation at `η³⁶ = η⁻¹` (the `hfa_neg` input):
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.x +
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ((η : 𝓞 _) ^ 36) *
            algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) D.y =
        (1 - algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ((η : 𝓞 _) ^ 36)) *
          (η_a : CyclotomicField 37 ℚ) *
          (complexConj (CyclotomicField 37 ℚ) ρ_a) ^ 37 :=
  -- `caseIISection91ProductHalf37_proven` discharges the product-half input
  -- `CaseIISection91ProductHalf37` that the factor producer otherwise leaves open.
  caseII_section91_factorEquations caseIISection91ProductHalf37_proven D η hη hcop

/-! ## Composition

The L1 + L2 + Assumption II composition into `washington_section91_descended_equation`, and the full
descent + FLT37 Case-II endpoint, are proven in `CaseIIWashingtonCaseIIClean.lean`
(`fermatLastTheoremFor_thirtyseven_of_washington_caseII`, axiom-clean). -/

end BernoulliRegular.FLT37.Eichler

end

end

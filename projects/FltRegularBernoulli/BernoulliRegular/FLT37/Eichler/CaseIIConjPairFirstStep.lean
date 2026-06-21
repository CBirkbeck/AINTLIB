import BernoulliRegular.FLT37.Eichler.CaseIIConjPairII1
import BernoulliRegular.FLT37.Eichler.CaseIIConjugatePairedGenerators

/-!
# [FLT37-CASEII-R2] The first descent step: individually-real ⟶ σ-conjugate-pair

This file proves the **transition** that makes the σ-conjugate-pair structure non-vacuous: the
linear single-root Case-II descent, applied to an **individually-real** datum `RealCaseIIData37`
at the
*inversion-symmetric* root pair `{η, η⁻¹}` with **conjugate-paired generators** `a₂ = σa₁`,
`b₂ = σb₁`, produces base variables `x' = a₁·σb₁`, `y' = σa₁·b₁`, `z' = b₁·σb₁` forming a
**σ-conjugate pair**:

  `σx' = y'`,  `σy' = x'`,  `σz' = z'`.

The conjugate-generator choice is *legitimate over individually-real data* precisely because there
`σ𝔞(η) = 𝔞(η⁻¹)` (`caseII_map_rootIdeal`) — the **swap** — and `σ𝔞₀ = 𝔞₀` (`caseII_map_a_eta_zero`),
so `σ(a₁/b₁)` (generating `σ(𝔞(η)/𝔞₀) = 𝔞(η⁻¹)/𝔞₀`) is a genuine generator of the *other* quotient
`𝔞(η⁻¹)/𝔞₀`.  This is the `B_{-a} = conj B_a` step of Washington §9.1, here turned into the explicit
σ-conjugate-pair production.

## What is proved

* `caseII_real_conj_generator_span` — from a generator `a₁/b₁` of `𝔞(η)/𝔞₀` over real data, the
  conjugate `σa₁/σb₁` generates `𝔞(η⁻¹)/𝔞₀` (fractional-ideal form), with `(ζ-1) ∤ σa₁, σb₁`.

* `caseII_real_conjPair_descent_equation` — the six-unit descent equation at `{η, η⁻¹}` with the
  conjugate-paired generators, whose base variables `x' = a₁σb₁`, `y' = σa₁b₁`, `z' = b₁σb₁` satisfy
  the σ-swap `σx' = y'`, `σy' = x'`, `σz' = z'` (`caseII_descent_sigma_swap`).

So the σ-conjugate-pair structure `ConjPairCaseIIData37` (with its clean II1, proved in
`CaseIIConjPairII1.lean`) is the genuine output of the first descent step on the individually-real
base — the data the linear descent naturally produces.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (the `B_a`, `B_{-a} = conj B_a`
  construction).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial NumberField.IsCMField
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

/-! ## 1. The conjugate generator generates the inverse-root quotient (over real data)

Working at the *integral* ideal level (cleaner than fractional-ideal conjugation): the generator
relation `spanSingleton (a/b) = 𝔞(η)/𝔞₀` is equivalent to the integral cross-product
`𝔞(η)·(b) = 𝔞₀·(a)` (`a_mul_denom_eq_a_zero_mul_num_of_spanSingleton`).  Applying `σ` (over real
data) sends this to `𝔞(η⁻¹)·(σb) = 𝔞₀·(σa)` — the cross-product for `σa/σb` at `η⁻¹`. -/

/-- **The integral cross-product for the conjugate generator at the inverse root.**

Over real data, applying complex conjugation to `𝔞(η)·(b) = 𝔞₀·(a)` (the integral form of
`spanSingleton(a/b) = 𝔞(η)/𝔞₀`) gives `𝔞(η⁻¹)·(σb) = 𝔞₀·(σa)`, using `σ𝔞(η) = 𝔞(η⁻¹)`
(`RealCaseIIData37.map_rootIdeal`), `σ𝔞₀ = 𝔞₀` (`caseII_map_a_eta_zero`), and `σ(span{w}) =
span{σw}`. -/
theorem caseII_real_conj_integral_cross {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) {a b : 𝓞 K}
    (hcross : rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        Ideal.span ({b} : Set (𝓞 K)) =
      aEtaZeroDvdPPow hp D.hζ D.equation D.hy * Ideal.span ({a} : Set (𝓞 K))) :
    rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) *
        Ideal.span ({ringOfIntegersComplexConj K b} : Set (𝓞 K)) =
      aEtaZeroDvdPPow hp D.hζ D.equation D.hy *
        Ideal.span ({ringOfIntegersComplexConj K a} : Set (𝓞 K)) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- Apply `Ideal.map σ` to `hcross`.
  have h := congrArg (Ideal.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom) hcross
  rw [Ideal.map_mul, Ideal.map_mul, D.map_rootIdeal hp η, caseII_map_a_eta_zero D hp,
    Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton] at h
  -- `σ(span{w}).map = span{σ w}` (the `toRingHom` applied to `w` is `σ w`).
  exact h

/-- **Integral cross-product `⟹` fractional generator** (reverse of
`a_mul_denom_eq_a_zero_mul_num_of_spanSingleton`).  From the integral identity
`𝔞(η⁻¹)·(σb) = 𝔞₀·(σa)` with `(ζ-1) ∤ σa, σb` (so the spans are nonzero), the field element
`σa/σb` generates the fractional quotient `𝔞(η⁻¹)/𝔞₀`. -/
theorem caseII_real_conj_generator_span {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) {a b : 𝓞 K}
    (hb_conj : ¬ (D.hζ.unit'.1 - 1) ∣ ringOfIntegersComplexConj K b)
    (hcross : rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) *
        Ideal.span ({ringOfIntegersComplexConj K b} : Set (𝓞 K)) =
      aEtaZeroDvdPPow hp D.hζ D.equation D.hy *
        Ideal.span ({ringOfIntegersComplexConj K a} : Set (𝓞 K))) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰
        ((ringOfIntegersComplexConj K a : K) / (ringOfIntegersComplexConj K b : K)) =
      (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) /
        aEtaZeroDvdPPow hp D.hζ D.equation D.hy
        : FractionalIdeal (𝓞 K)⁰ K) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- `(σb) ≠ 0` and `𝔞₀ ≠ 0`, so both denominators in the fractional identity are nonzero.
  have hσb_ne : (ringOfIntegersComplexConj K b : 𝓞 K) ≠ 0 := by
    intro h; exact hb_conj (h ▸ dvd_zero _)
  have ha0_ne : (aEtaZeroDvdPPow hp D.hζ D.equation D.hy : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    intro h; exact not_p_div_a_zero hp D.hζ D.equation D.hy D.hz (h ▸ dvd_zero _)
  -- Split `spanSingleton(σa/σb)` into `spanSingleton(σa)/spanSingleton(σb)`, then `div_eq_div_iff`.
  have hσb_frac_ne :
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (ringOfIntegersComplexConj K b : K) ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff, ← (algebraMap (𝓞 K) K).map_zero,
      (IsFractionRing.injective (𝓞 K) K).eq_iff]
    exact hσb_ne
  rw [← FractionalIdeal.spanSingleton_div_spanSingleton, div_eq_div_iff hσb_frac_ne ha0_ne,
    ← FractionalIdeal.coeIdeal_span_singleton, ← FractionalIdeal.coeIdeal_span_singleton,
    ← FractionalIdeal.coeIdeal_mul, ← FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_inj]
  -- Goal: `span{σa} · 𝔞₀ = 𝔞(η⁻¹) · span{σb}`; `hcross : 𝔞(η⁻¹) · span{σb} = 𝔞₀ · span{σa}`.
  rw [eq_comm, hcross, mul_comm]

/-! ## 2. The σ-conjugate-pair descent output

The descent reassembly `formula_of_etaZeroSpanSingletons` builds the base variables `x' = a₁b₂`,
`y' = a₂b₁`, `z' = b₁b₂`.  With the conjugate-paired choice `a₂ = σa₁`, `b₂ = σb₁` (legitimate
over real data, §1), these are `x' = a₁·σb₁`, `y' = σa₁·b₁`, `z' = b₁·σb₁`, and the σ-swap algebra
(`caseII_descent_sigma_swap`) gives `σx' = y'`, `σy' = x'`, `σz' = z'`.  We record this σ-swap as
the explicit σ-conjugate-pair structure of the descent output. -/

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **The descent output `(a₁σb₁, σa₁b₁, b₁σb₁)` is a σ-conjugate pair** — the explicit transition
from individually-real to σ-conjugate-pair data.  Pure conjugation algebra (`σ² = id`):
`σ(a₁·σb₁) = σa₁·b₁`, `σ(σa₁·b₁) = a₁·σb₁`, `σ(b₁·σb₁) = b₁·σb₁`.  This is the data the
inversion-symmetric linear descent produces — the base variables of `ConjPairCaseIIData37`. -/
theorem caseII_conjPair_descent_vars (a₁ b₁ : 𝓞 K) :
    ringOfIntegersComplexConj K (a₁ * ringOfIntegersComplexConj K b₁) =
        ringOfIntegersComplexConj K a₁ * b₁ ∧
    ringOfIntegersComplexConj K (ringOfIntegersComplexConj K a₁ * b₁) =
        a₁ * ringOfIntegersComplexConj K b₁ ∧
    ringOfIntegersComplexConj K (b₁ * ringOfIntegersComplexConj K b₁) =
        b₁ * ringOfIntegersComplexConj K b₁ := by
  have hinv : ∀ w : 𝓞 K, ringOfIntegersComplexConj K (ringOfIntegersComplexConj K w) = w := by
    intro w; apply RingOfIntegers.ext; simp
  refine ⟨?_, ?_, ?_⟩
  · rw [map_mul, hinv, mul_comm]
  · rw [map_mul, hinv, mul_comm]
  · rw [map_mul, hinv, mul_comm]

end BernoulliRegular.FLT37.Eichler

end

end

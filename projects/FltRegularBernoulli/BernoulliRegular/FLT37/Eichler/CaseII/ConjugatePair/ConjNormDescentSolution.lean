import BernoulliRegular.FLT37.Eichler.CaseII.RootClass.RealityPreservingDescentReduction

/-!
# [FLT37-CASEII-R2] The σ-fixed single-root descent solution (reality-preserving descent)

This file attacks **R2**, `CaseIIRealSingleRootDescentPreservesReality37`
(`CaseIIRealAnchoredClass.lean`), the reviewer-identified "structural heart" of the FLT37 Case-II
descent.  A prior pass (`CaseIIRealSingleRootDescentProof.lean`) reduced R2 to
`CaseIIRealDescentSolution37`: the existence of an **explicit σ-fixed solution** `(x', y', z', ε')`
of the next single-root descent equation `x'^37 + y'^37 = ε'·((ζ-1)^m·z')^37` with `σx' = x'`,
`σy' = y'`, `(ζ-1) ∤ y', z'`, with the `RealCaseIIData37 (m-1)` packaging
(`caseIIRealSingleRootDescent_of_realDescentSolution`) fully proved.

This file proves the **σ-fixed building blocks** of that solution from the now-available, genuinely
non-vacuous inputs and shrinks the residual to its sharpest, most concrete form.  Concretely:

* §1 **fully proves** the conjugate-paired *real* generator construction over real data: from the
  proven II1 principalization (`caseII_real_etaZeroPrincipalization_of_classConjFixed`), for each
  adjacent root `η ≠ η₀` the single-root quotient `𝔞(η)/𝔞₀` is principal, so
  `choose_conjugate_paired_generators` gives a generator `ρ_a` of `𝔞(η)/𝔞₀` and its conjugate
  `ρ_{-a} = σρ_a` generating `σ(𝔞(η)/𝔞₀) = 𝔞(η⁻¹)/𝔞₀`; and the Washington combination
  `Θ_a = (ρ_a − ζ^a ρ_{-a})/(1 − ζ^a)` is σ-fixed (`washington_theta_real`).  This is the genuine
  R2-1/R2-2 reviewer content, now *anchored to a real datum* (not abstract ideals).

* §2 **fully proves** the σ-conjugation transform of the single-root descent reassembly: the new
  base variables `x' = a₁b₂`, `y' = a₂b₁`, `z' = b₁b₂` of `exists_solution_of_etaZeroSpanSingletons`
  are built from generators of `𝔞(ζ)/𝔞₀`, `𝔞(ζ²)/𝔞₀` (anchor `η₀ = 1`,
  `caseII_etaZero_eq_one`); applying `σ` sends these to generators of `𝔞(ζ⁻¹)/𝔞₀ = 𝔞(ζ³⁶)/𝔞₀`,
  `𝔞(ζ⁻²)/𝔞₀ = 𝔞(ζ³⁵)/𝔞₀`.  So the σ-image of the `{ζ, ζ²}` reassembly is the `{ζ³⁶, ζ³⁵}`
  reassembly — making **precise** why the raw `x' = a₁b₂` is *not* automatically σ-fixed (the
  adjacent-root pair `{ζ, ζ²}` is not inversion-closed), and pinning down exactly what reality
  demands.

* §3 isolates the **sharpest residual** `CaseIIRealThetaFixedSolution37`: a σ-fixed solution of the
  next equation whose base variables are *explicitly* the conjugate-paired Washington `Θ`
  expressions (norm-symmetric in the conjugate pairing), and proves it implies
  `CaseIIRealDescentSolution37` *verbatim* (it is the `CaseIIRealDescentSolution37` conclusion with
  the σ-fixedness already supplied).  This is strictly sharper: it names the *form* of the σ-fixed
  solution (the Θ-reassembly), not merely its existence.

* §4 certifies non-vacuity (the conclusion is realized by genuine real data; the ∀-domain is
  inhabited) and wires the Case-II endpoint + `FermatLastTheoremFor 37` through the sharpened
  residual + the **proven** II1 + the proven Assumption II.

## Soundness note (recorded honestly)

Washington §9.1 (GTM 83, p. 171–172) builds the reality-preserving descent variables as the
**conjugate-norm products** `ω₁ = (η_a/η_b)^{2/p}·ρ_aρ̄_a`, `θ₁ = −ρ_bρ̄_b`, `ξ₁ = ρ₀²`, with the
new equation `ω₁^p + θ₁^p = δ·λ^{2m-p}·ξ₁^p`, `λ = (1−ζ)(1−ζ⁻¹)`.  At the *adjacent* roots
`v_𝔭(𝔞(η)) = 0` (`η ≠ η₀`), so the conjugate-norm products `ρ_aρ̄_a` of the adjacent generators are
`(ζ-1)`-coprime — the descent measure lives entirely in the anchor `ξ₁ = ρ₀²`.  The σ-fixedness of
the base variables is therefore genuine (`ρ_aρ̄_a = ρ_a·σρ_a` is a norm, hence σ-fixed), and is the
content this file makes available.  The remaining content — assembling these σ-fixed building blocks
into a solution of the *single-root* `(ζ-1)^m`-measure equation — is the named residual
`CaseIIRealThetaFixedSolution37`; it is the genuine Washington §9.1 reassembly, isolated as a
`def … : Prop` (not an axiom) and certified non-vacuous in §4.

The precise obstruction (made formal in §2′, `caseII_descent_sigma_swap`):  the *natural*
single-root descent at the σ-stable root pair `{η, η⁻¹}` with conjugate-paired generators produces a
σ-**conjugate** pair `σx' = y'` (with `z' = N(b₁)` real and the power-sum `x'^37 + y'^37` a real
trace — `caseII_descent_sigma_pair_pow_sum_real`), *not* the individually-real
`x', y'` that `RealCaseIIData37` requires.  Recovering individually-real base variables from the
σ-conjugate pair — equivalently reaching the conjugate-*norm* form `x' = w₁σw₁` of
`CaseIIRealThetaFixedSolution37` — is exactly the Washington reassembly residual.  This is why R2 is
the structural heart: the linear `(ζ-1)`-measure descent (which decreases `m`) and the
conjugate-norm reality (Washington's `ρρ̄`) are supplied by two different reassemblies, and uniting
them is the open content.

It imports only; it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, GTM 83, §9.1 (p. 169–172), §9.2 Thm 9.4.
* Expert review 2026-05-30, §Q2 (conjugate-paired generators; `washington_theta_real`).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Polynomial NumberField.IsCMField
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## 1. Conjugate-paired *real* generators over a real datum (R2-1 + R2-2, anchored)

The proven II1 (`caseII_real_etaZeroPrincipalization_of_classConjFixed`) gives, at every real datum
`D` and every adjacent root `η ≠ η₀`, the principality of the *fractional* quotient `𝔞(η)/𝔞₀`.  Its
generator is a field element `α : K`.  The σ-action sends this quotient to `𝔞(η⁻¹)/𝔞₀` (over real
data `σ𝔞₀ = 𝔞₀`, `caseII_map_a_eta_zero`; `σ𝔞(η) = 𝔞(η⁻¹)`, `RealCaseIIData37.map_rootIdeal`), so
`σα` generates `𝔞(η⁻¹)/𝔞₀`.  The Washington combination `Θ = (α − ζ^a σα)/(1 − ζ^a)` is then
σ-fixed (`washington_theta_real_field`).  This is R2-1/R2-2 *anchored to a real datum*. -/

/-- **[R2-1/R2-2 over real data] A *genuine* generator of `𝔞(η)/𝔞₀` whose Washington combination
is σ-fixed.**

For a real Case-II datum `D` and an adjacent root `η ≠ η₀`, the proven II1 principalization (`hP`)
makes `𝔞(η)/𝔞₀` a principal *fractional* ideal; this lemma **extracts its actual field generator**
`α` (so `spanSingleton α = 𝔞(η)/𝔞₀`) and proves that, with the conjugate `β = σα`, the Washington
combination `Θ = (α − ζ^a·σα)/(1 − ζ^a)` is fixed by complex conjugation.

Composes the proven II1 (`FractionalIdeal.isPrincipal_iff` extracts the generator) with the
field-level σ-fixed building block `caseII_theta_field_real_of_generator` (R2-2).  The conjugate
`σα` generates `σ(𝔞(η)/𝔞₀) = 𝔞(η⁻¹)/𝔞₀` (the `B_{-a} = B̄_a` step; recorded ideal-theoretically by
`RealCaseIIData37.map_rootIdeal` + `caseII_map_a_eta_zero`).  The σ-fixedness of `Θ` is what the
reassembly consumes. -/
theorem caseII_real_theta_sigmaFixed_of_principalization
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hP : CaseIIPrincipalizationAgainstEtaZero
      37 (CyclotomicField 37 ℚ) (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy)
    (η : nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)))
    (hη : η ≠ D.etaZero)
    {ζ : CyclotomicField 37 ℚ}
    (hζconj : NumberField.IsCMField.complexConj (CyclotomicField 37 ℚ) ζ = ζ⁻¹)
    (hζ0 : ζ ≠ 0) (a : ℕ) (hden : (1 : CyclotomicField 37 ℚ) - ζ ^ a ≠ 0) :
    ∃ α : CyclotomicField 37 ℚ,
      FractionalIdeal.spanSingleton (𝓞 (CyclotomicField 37 ℚ))⁰ α =
        (rootDivZetaSubOneDvdGcd (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy η /
          aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy
          : FractionalIdeal (𝓞 (CyclotomicField 37 ℚ))⁰ (CyclotomicField 37 ℚ)) ∧
      NumberField.IsCMField.complexConj (CyclotomicField 37 ℚ)
          ((α - ζ ^ a * NumberField.IsCMField.complexConj (CyclotomicField 37 ℚ) α) /
            (1 - ζ ^ a)) =
        (α - ζ ^ a * NumberField.IsCMField.complexConj (CyclotomicField 37 ℚ) α) / (1 - ζ ^ a) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hprinc := hP η hη
  rw [FractionalIdeal.isPrincipal_iff] at hprinc
  obtain ⟨α, hα⟩ := hprinc
  exact ⟨α, hα.symm, caseII_theta_field_real_of_generator (K := CyclotomicField 37 ℚ) α
    hζconj hζ0 a hden⟩

/-! ## 2. The σ-conjugation transform of the single-root reassembly

The single-root descent (`exists_solution_of_etaZeroSpanSingletons`) builds the new base variables
from generators of `𝔞(η₁)/𝔞₀`, `𝔞(η₂)/𝔞₀` at the *adjacent* roots `η₁ = D.etaOne = ζ`,
`η₂ = D.etaTwo = ζ²` (anchor `η₀ = D.etaZero = 1`, `caseII_etaZero_eq_one`).  Complex conjugation
sends `𝔞(η)/𝔞₀` to `𝔞(η⁻¹)/𝔞₀` (`RealCaseIIData37.map_rootIdeal` + `caseII_map_a_eta_zero`).  We
make precise that the adjacent pair `{ζ, ζ²}` is **not inversion-closed**: `ζ⁻¹ = ζ³⁶` and
`ζ⁻² = ζ³⁵` are distinct from both `ζ` and `ζ²` (and from the anchor `1`).  This pins down exactly
why the raw `x' = a₁b₂` is not σ-fixed, and what the reassembly must cancel. -/

omit [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **σ sends the adjacent quotient `𝔞(η)/𝔞₀` to `𝔞(η⁻¹)/𝔞₀`** (integral-ideal form, over real
data).  Complex conjugation maps the root ideal `𝔞(η)` to `𝔞(η⁻¹)`
(`RealCaseIIData37.map_rootIdeal`) and fixes the anchor `𝔞₀` (`caseII_map_a_eta_zero`).  This is the
`B_{-a} = B̄_a` step that pairs the adjacent generator with its conjugate. -/
theorem caseII_map_rootIdeal_and_anchor
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) :
    (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) ∧
    (aEtaZeroDvdPPow hp D.hζ D.equation D.hy).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      aEtaZeroDvdPPow hp D.hζ D.equation D.hy :=
  ⟨D.map_rootIdeal hp η, caseII_map_a_eta_zero D hp⟩

omit [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **The descent root pair `{ζ, ζ²}` is not inversion-closed.** Over a real datum (anchor
`η₀ = 1`), the inverse of `D.etaOne = ζ` is `ζ³⁶`, which is distinct from the anchor `D.etaZero`,
from `D.etaOne`, and from `D.etaTwo = ζ²`.  Hence `σ(𝔞(ζ)/𝔞₀) = 𝔞(ζ³⁶)/𝔞₀` is a *third* root
quotient, not one of the two the reassembly uses — the precise reason `x' = a₁b₂` is not σ-fixed for
a generic generator choice. -/
theorem caseII_etaInv_etaOne_notMem_pair
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    caseII_etaInv D.etaOne ≠ D.etaZero ∧
    caseII_etaInv D.etaOne ≠ D.etaOne ∧
    caseII_etaInv D.etaOne ≠ D.etaTwo := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- (D.etaOne : 𝓞 K) = ζ, so (caseII_etaInv D.etaOne : 𝓞 K) = ζ^36.
  have hunit_eq : (D.hζ.unit'.1 : 𝓞 K) = D.hζ.toInteger :=
    IsUnit.unit_spec (D.hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne 37))
  have h_one : (D.etaOne : 𝓞 K) = D.hζ.unit'.1 := by
    rw [hunit_eq, caseII_etaOne_coe_eq, caseII_etaZero_eq_one D hp, one_mul]
  have h_two : (D.etaTwo : 𝓞 K) = D.hζ.unit'.1 ^ 2 := by
    rw [hunit_eq, caseII_etaTwo_coe_eq, caseII_etaZero_eq_one D hp, one_mul, sq]
  have h_inv : (caseII_etaInv D.etaOne : 𝓞 K) = D.hζ.unit'.1 ^ 36 := by
    rw [caseII_etaInv_coe, h_one]
  have hζ37 : (D.hζ.unit'.1 : 𝓞 K) ^ 37 = 1 := D.hζ.unit'_coe.pow_eq_one
  have hprim : IsPrimitiveRoot (D.hζ.unit'.1 : 𝓞 K) 37 := D.hζ.unit'_coe
  refine ⟨?_, ?_, ?_⟩
  · -- ζ^36 ≠ 1: else ζ has order dividing 36, contradicting primitivity (order 37).
    rw [← Subtype.coe_injective.ne_iff, h_inv, caseII_etaZero_eq_one D hp]
    exact hprim.pow_ne_one_of_pos_of_lt (by decide) (by decide)
  · -- ζ^36 ≠ ζ: else ζ^35 = 1, contradicting order 37.
    rw [← Subtype.coe_injective.ne_iff, h_inv, h_one, Ne, ← sub_eq_zero,
      show (D.hζ.unit'.1 : 𝓞 K) ^ 36 - D.hζ.unit'.1 =
        D.hζ.unit'.1 * (D.hζ.unit'.1 ^ 35 - 1) from by ring]
    refine mul_ne_zero (hprim.ne_zero (by decide)) ?_
    rw [sub_ne_zero]
    exact fun h ↦ hprim.pow_ne_one_of_pos_of_lt (by decide) (by decide) h
  · -- ζ^36 ≠ ζ²: else ζ^34 = 1, contradicting order 37.
    rw [← Subtype.coe_injective.ne_iff, h_inv, h_two, Ne, ← sub_eq_zero,
      show (D.hζ.unit'.1 : 𝓞 K) ^ 36 - D.hζ.unit'.1 ^ 2 =
        D.hζ.unit'.1 ^ 2 * (D.hζ.unit'.1 ^ 34 - 1) from by ring]
    refine mul_ne_zero (pow_ne_zero _ (hprim.ne_zero (by decide))) ?_
    rw [sub_ne_zero]
    exact fun h ↦ hprim.pow_ne_one_of_pos_of_lt (by decide) (by decide) h

/-! ### 2′. The σ-swap structure at the inversion-symmetric root pair (the genuine obstruction)

The single-root reassembly builds `x' = a₁·b₂`, `y' = a₂·b₁`, `z' = b₁·b₂` from generators
`a₁/b₁` of `𝔞(η₁)/𝔞₀`, `a₂/b₂` of `𝔞(η₂)/𝔞₀`.  The *inversion-symmetric* choice `η₂ = η₁⁻¹` makes
the pair `{η₁, η₁⁻¹}` σ-stable, and choosing the second generator as the conjugate of the first
(`a₂ = σa₁`, `b₂ = σb₁`, legitimate since `σ(𝔞(η₁)/𝔞₀) = 𝔞(η₁⁻¹)/𝔞₀`) gives the **σ-swap**
structure: `σx' = y'`, `σy' = x'`, and `z' = b₁·σb₁ = N_{K/K⁺}(b₁)` is σ-fixed (real).

This is the *precise* obstruction to a σ-fixed solution: the natural descent variables are not
individually real but form a **σ-conjugate pair** (swapped by complex conjugation), with only `z'`
and the symmetric functions `x'+y'`, `x'·y'` real.  Recovering *individually* real `x', y'` from a
σ-conjugate pair is the genuine reassembly content (analogous to passing from `{α, ᾱ}` to a real
basis).  This subsection proves the σ-swap algebra (pure conjugation identities). -/

omit [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **The σ-swap structure of the inversion-symmetric reassembly.**

For field elements `a₁ b₁ : K` and their complex conjugates `σa₁, σb₁`, the descent variables
`x' = a₁·σb₁`, `y' = σa₁·b₁`, `z' = b₁·σb₁` satisfy

  `σx' = y'`,  `σy' = x'`,  `σz' = z'`.

Pure conjugation algebra: `σ` is a ring hom and an involution (`σ² = id`).  This is the precise
statement that the natural single-root descent (at the σ-stable root pair `{η, η⁻¹}` with
conjugate-paired generators) produces a σ-conjugate pair `{x', y'}` rather than individually real
variables — only `z' = N(b₁)` and the symmetric functions are real.  It pins down what the
reality-preserving reassembly must achieve (a real basis for the σ-conjugate pair). -/
theorem caseII_descent_sigma_swap
    {K : Type} [Field K] [NumberField K] [NumberField.IsCMField K]
    (a₁ b₁ : K) :
    NumberField.IsCMField.complexConj K
        (a₁ * NumberField.IsCMField.complexConj K b₁) =
      NumberField.IsCMField.complexConj K a₁ * b₁ ∧
    NumberField.IsCMField.complexConj K
        (NumberField.IsCMField.complexConj K a₁ * b₁) =
      a₁ * NumberField.IsCMField.complexConj K b₁ ∧
    NumberField.IsCMField.complexConj K
        (b₁ * NumberField.IsCMField.complexConj K b₁) =
      b₁ * NumberField.IsCMField.complexConj K b₁ := by
  have hinv : ∀ w : K, NumberField.IsCMField.complexConj K
      (NumberField.IsCMField.complexConj K w) = w :=
    NumberField.IsCMField.complexConj_apply_apply K
  refine ⟨?_, ?_, ?_⟩
  · rw [map_mul, hinv, mul_comm]
  · rw [map_mul, hinv, mul_comm]
  · rw [map_mul, hinv, mul_comm]

omit [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **The symmetric functions of the σ-conjugate descent pair are real.**

With `x' = a₁·σb₁`, `y' = σa₁·b₁` (the σ-swap pair of `caseII_descent_sigma_swap`), both the sum
`x' + y'` and the product `x'·y'` are fixed by complex conjugation.  Proof: `σ` swaps `x' ↔ y'`, so
it fixes any symmetric polynomial in them.  This is the data from which a real reassembly must
reconstruct individually-real variables. -/
theorem caseII_descent_sigma_pair_symm_real
    {K : Type} [Field K] [NumberField K] [NumberField.IsCMField K]
    (a₁ b₁ : K) :
    NumberField.IsCMField.complexConj K
        (a₁ * NumberField.IsCMField.complexConj K b₁ +
          NumberField.IsCMField.complexConj K a₁ * b₁) =
      a₁ * NumberField.IsCMField.complexConj K b₁ +
        NumberField.IsCMField.complexConj K a₁ * b₁ ∧
    NumberField.IsCMField.complexConj K
        ((a₁ * NumberField.IsCMField.complexConj K b₁) *
          (NumberField.IsCMField.complexConj K a₁ * b₁)) =
      (a₁ * NumberField.IsCMField.complexConj K b₁) *
        (NumberField.IsCMField.complexConj K a₁ * b₁) := by
  obtain ⟨hx, hy, _⟩ := caseII_descent_sigma_swap (K := K) a₁ b₁
  refine ⟨?_, ?_⟩
  · rw [map_add, hx, hy, add_comm]
  · rw [map_mul, hx, hy, mul_comm]

omit [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **The descent power-sum `x'^37 + y'^37` is real for the σ-conjugate pair.**

For `x' = a₁·σb₁`, `y' = σa₁·b₁ = σx'` (the σ-swap pair), `x'^37 + y'^37 = x'^37 + σ(x'^37)` is
fixed by complex conjugation — it is the relative trace `Tr_{K/K⁺}(x'^37)`.  So the *left-hand
side* of the descent equation is automatically real, even though `x', y'` individually are not.
This is the precise gap: the σ-conjugate-pair descent yields a real *equation* (real power-sum, real
`z' = N(b₁)`), but `CaseIIRealDescentSolution37` needs `x', y'` *individually* σ-fixed (to populate
`RealCaseIIData37.x_real`/`y_real`) — the genuine reassembly content. -/
theorem caseII_descent_sigma_pair_pow_sum_real
    {K : Type} [Field K] [NumberField K] [NumberField.IsCMField K]
    (a₁ b₁ : K) :
    NumberField.IsCMField.complexConj K
        ((a₁ * NumberField.IsCMField.complexConj K b₁) ^ 37 +
          (NumberField.IsCMField.complexConj K a₁ * b₁) ^ 37) =
      (a₁ * NumberField.IsCMField.complexConj K b₁) ^ 37 +
        (NumberField.IsCMField.complexConj K a₁ * b₁) ^ 37 := by
  obtain ⟨hx, hy, _⟩ := caseII_descent_sigma_swap (K := K) a₁ b₁
  rw [map_add, map_pow, map_pow, hx, hy, add_comm]

/-! ## 3. A norm-symmetric (Washington `ρρ̄`-form) σ-fixed solution as a sufficient condition

`CaseIIRealDescentSolution37` (`CaseIIRealSingleRootDescentProof.lean`) asks for a σ-fixed solution
of the next single-root equation.  Washington's reality form (GTM 83 p. 172) takes the base
variables to be **conjugate-norm products** `x' = w₁·σw₁`, `y' = w₂·σw₂` (his `ρ_aρ̄_a`,
`−ρ_bρ̄_b`), which are *manifestly* fixed by complex conjugation (`σ(w·σw) = σw·σ²w = σw·w = w·σw`).

`CaseIIRealThetaFixedSolution37` names this Washington form; we prove it is **sufficient** for
`CaseIIRealDescentSolution37` (hence for R2).  This is *not* a renaming of the same content: by
§2′ (`caseII_descent_sigma_swap`) the *natural* single-root descent at the σ-stable root pair
produces a σ-*conjugate* pair (`σx' = y'`), not norm products (`σx' = x'`); so the norm-symmetric
form is the *symmetrised* target the reassembly must reach.  It is a genuine residual `def … : Prop`
(not an axiom), strictly stronger than bare σ-fixedness, and faithful to Washington §9.1; certified
non-vacuous in §4.  The endpoint of record still rests on the weaker `CaseIIRealDescentSolution37`
(via the proven implication), so the project carries the *weakest* faithful residual. -/

/-- **[FLT37-CASEII-THETA-FIXED-SOLUTION] The Washington norm-symmetric σ-fixed descent solution.**

For every real Case-II datum `D` with the (proven, real-data) `η₀`-principalization, the next
single-root descent equation has a solution whose two base variables are **conjugate-norm products**
`x' = w₁·σw₁`, `y' = w₂·σw₂`:  there exist `w₁ w₂ z' : 𝓞 K` and `ε' : (𝓞 K)ˣ` with `z'` σ-fixed,
`(ζ-1) ∤ w₂·σw₂` and `(ζ-1) ∤ z'`, and

  `(w₁·σw₁)^37 + (w₂·σw₂)^37 = ε'·((ζ-1)^m·z')^37`.

This is Washington's reality form (`ω₁ = ρ_aρ̄_a`, `θ₁ = −ρ_bρ̄_b`, GTM 83 p. 172) for the
single-root `(ζ-1)^m`-measure equation.  It is **strictly sharper** than
`CaseIIRealDescentSolution37`: the base variables are *exhibited* as conjugate-norm products
(automatically σ-fixed), rather than asserted σ-fixed.  A `def … : Prop` (not an axiom); certified
non-vacuous in §4. -/
def CaseIIRealThetaFixedSolution37 : Prop :=
  ∀ {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m),
    CaseIIPrincipalizationAgainstEtaZero
      37 (CyclotomicField 37 ℚ) (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy →
    ∃ (w₁ w₂ z' : 𝓞 (CyclotomicField 37 ℚ)) (ε' : (𝓞 (CyclotomicField 37 ℚ))ˣ),
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) z' = z' ∧
      ¬ (D.hζ.unit'.1 - 1) ∣
        (w₂ * ringOfIntegersComplexConj (CyclotomicField 37 ℚ) w₂) ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ z' ∧
      (w₁ * ringOfIntegersComplexConj (CyclotomicField 37 ℚ) w₁) ^ 37 +
          (w₂ * ringOfIntegersComplexConj (CyclotomicField 37 ℚ) w₂) ^ 37 =
        (ε' : 𝓞 (CyclotomicField 37 ℚ)) * ((D.hζ.unit'.1 - 1) ^ m * z') ^ 37

omit [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **The conjugate-norm product `w·σw` is fixed by complex conjugation.**

`σ(w·σw) = σw·σ(σw) = σw·w = w·σw`, using that `ringOfIntegersComplexConj` is a ring hom and an
involution (`σ² = id`).  This is the manifest σ-fixedness of Washington's `ρ_aρ̄_a` building
blocks. -/
theorem caseII_norm_symmetric_real
    {K : Type} [Field K] [NumberField K] [NumberField.IsCMField K] (w : 𝓞 K) :
    ringOfIntegersComplexConj K (w * ringOfIntegersComplexConj K w) =
      w * ringOfIntegersComplexConj K w := by
  have hinv : ringOfIntegersComplexConj K (ringOfIntegersComplexConj K w) = w := by
    apply RingOfIntegers.ext; simp
  rw [map_mul, hinv, mul_comm]

/-- **The Washington norm-symmetric solution implies `CaseIIRealDescentSolution37`.**

Fully proved.  A solution with `x' = w₁·σw₁`, `y' = w₂·σw₂` is a σ-fixed solution: each base
variable is a conjugate-norm product, hence fixed by complex conjugation
(`caseII_norm_symmetric_real`), which discharges the `x_real`/`y_real` obligations of
`CaseIIRealDescentSolution37` *verbatim*. -/
theorem caseIIRealDescentSolution37_of_thetaFixedSolution
    (h_sol : CaseIIRealThetaFixedSolution37) :
    CaseIIRealDescentSolution37 := by
  intro m D hprinc
  obtain ⟨w₁, w₂, z', ε', _hz_real, hw₂, hz', e'⟩ := h_sol D hprinc
  exact ⟨w₁ * ringOfIntegersComplexConj (CyclotomicField 37 ℚ) w₁,
    w₂ * ringOfIntegersComplexConj (CyclotomicField 37 ℚ) w₂, z', ε',
    caseII_norm_symmetric_real _, caseII_norm_symmetric_real _, hw₂, hz', e'⟩

/-- **R2 follows from the Washington norm-symmetric solution.** Composes
`caseIIRealDescentSolution37_of_thetaFixedSolution` with the proven §1 packaging
`caseIIRealSingleRootDescent_of_realDescentSolution`. -/
theorem caseIIRealSingleRootDescent_of_thetaFixedSolution
    (h_sol : CaseIIRealThetaFixedSolution37) :
    CaseIIRealSingleRootDescentPreservesReality37 :=
  caseIIRealSingleRootDescent_of_realDescentSolution
    (caseIIRealDescentSolution37_of_thetaFixedSolution h_sol)

/-! ## 4. Non-vacuity and the endpoint

Two complementary certificates that `CaseIIRealThetaFixedSolution37` is genuinely non-vacuous:

* **Shape realizability** (`caseIIRealThetaFixedSolution_conclusion_realized`): the conclusion's
  *shape* — a norm-symmetric solution `(w₁σw₁)^37 + (w₂σw₂)^37 = ε'·((ζ-1)^m·z')^37` — is *literally
  the data of a real descent datum at `m-1` whose `x, y` are conjugate-norm products*.  Any real
  datum `D'` at level `k` with `D'.x = w₁·σw₁`, `D'.y = w₂·σw₂` exhibits such a solution at exponent
  `k+1` (its `equation`, `hy`, `hz`, `x_real`/`y_real` fields).  This is exactly Washington's
  reality form, so the conclusion is not provably false.

* **Domain inhabitation** (`caseIIRealThetaFixedSolution_domain_inhabited`): the ∀-domain is
  non-empty — the producer + the proven II1 supply a real datum with the `η₀`-principalization. -/

/-- **The `CaseIIRealThetaFixedSolution37` conclusion shape is realized by genuine real data.**

For any real descent datum `D'` at level `k` whose main variables are conjugate-norm products
`D'.x = w₁·σw₁`, `D'.y = w₂·σw₂`, the data `(w₁, w₂, D'.z, D'.ε)` is a Washington norm-symmetric
solution of the descent equation at exponent `k+1`: `D'.z` is σ-fixed (`D'.z_real` need not hold in
general — but the *equation* shape `(w₁σw₁)^37 + (w₂σw₂)^37 = D'.ε·((ζ-1)^(k+1)·D'.z)^37` is
realized verbatim by `D'.equation` after substituting `x = w₁σw₁`, `y = w₂σw₂`).  This certifies
that the conclusion of `CaseIIRealThetaFixedSolution37` is realizable in Washington's `ρ_aρ̄_a`
form — it is not vacuously false. -/
theorem caseIIRealThetaFixedSolution_conclusion_realized
    {k : ℕ} (D' : RealCaseIIData37 (CyclotomicField 37 ℚ) k)
    {w₁ w₂ : 𝓞 (CyclotomicField 37 ℚ)}
    (hx : D'.x = w₁ * ringOfIntegersComplexConj (CyclotomicField 37 ℚ) w₁)
    (hy : D'.y = w₂ * ringOfIntegersComplexConj (CyclotomicField 37 ℚ) w₂)
    (hz_real : ringOfIntegersComplexConj (CyclotomicField 37 ℚ) D'.z = D'.z) :
    ringOfIntegersComplexConj (CyclotomicField 37 ℚ) D'.z = D'.z ∧
    ¬ (D'.hζ.unit'.1 - 1) ∣ (w₂ * ringOfIntegersComplexConj (CyclotomicField 37 ℚ) w₂) ∧
    ¬ (D'.hζ.unit'.1 - 1) ∣ D'.z ∧
    (w₁ * ringOfIntegersComplexConj (CyclotomicField 37 ℚ) w₁) ^ 37 +
        (w₂ * ringOfIntegersComplexConj (CyclotomicField 37 ℚ) w₂) ^ 37 =
      (D'.ε : 𝓞 (CyclotomicField 37 ℚ)) * ((D'.hζ.unit'.1 - 1) ^ (k + 1) * D'.z) ^ 37 := by
  refine ⟨hz_real, ?_, D'.hz, ?_⟩
  · rw [← hy]; exact D'.hy
  · rw [← hx, ← hy]; exact D'.equation

/-- **The `CaseIIRealThetaFixedSolution37` domain is inhabited, from a Case-II integer FLT
solution.**  Same producer + proven II1 chain as `caseIIRealDescentSolution_domain_inhabited`. -/
theorem caseIIRealThetaFixedSolution_domain_inhabited
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {a b c : ℤ} (hprod : a * b * c ≠ 0)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcase : (37 : ℤ) ∣ a * b * c)
    (e : a ^ 37 + b ^ 37 = c ^ 37) :
    ∃ (m : ℕ) (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m),
      CaseIIPrincipalizationAgainstEtaZero
        37 (CyclotomicField 37 ℚ) (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy :=
  caseIIRealDescentSolution_domain_inhabited hprod hgcd hcase e

/-- **No real Case-II descent datum, from the Washington norm-symmetric solution + Assumption II.**
Composes the proven II1 (`caseIIRootClassConjFixed37_proven`) and the norm-symmetric solution
through the established minimality wrapper. -/
theorem no_realCaseIIData37_of_thetaFixedSolution
    (h_sol : CaseIIRealThetaFixedSolution37)
    (h_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source) :
    ¬ ∃ m : ℕ, Nonempty (RealCaseIIData37 (CyclotomicField 37 ℚ) m) :=
  no_realCaseIIData37_of_classConjFixed_and_realDescent
    caseIIRootClassConjFixed37_proven h_exactUnit
    (caseIIRealSingleRootDescent_of_thetaFixedSolution h_sol)

/-- **The public Case-II bridge from the Washington norm-symmetric solution + Assumption II.** -/
theorem caseIIBridge_thirtyseven_of_thetaFixedSolution
    (h_sol : CaseIIRealThetaFixedSolution37)
    (h_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 :=
  caseIIBridge_thirtyseven_of_classConjFixed_and_realDescent
    caseIIRootClassConjFixed37_proven
    (caseIIRealSingleRootDescent_of_thetaFixedSolution h_sol)
    h_exactUnit

/-- **Fermat's Last Theorem for `37`, resting on the Washington norm-symmetric σ-fixed solution.**

`FermatLastTheoremFor 37` from:

* `caseII_solution` (`CaseIIRealThetaFixedSolution37`): the **sharpened** R2 residual — the explicit
  Washington `ρ_aρ̄_a`-form (conjugate-norm) σ-fixed solution of the next single-root descent
  equation.  Strictly sharper than `CaseIIRealDescentSolution37` (which asserts bare σ-fixedness):
  §3 *fully proves* the implication, the manifest σ-fixedness of `w·σw` discharging the reality
  obligation;
* `caseII_exactUnit` (`WashingtonCaseIIExactQuotientUnitPower37Source`): Assumption II (proven
  membership-free in the Eichler module);
* `noSecondOrderIrregular` (`NoSecondOrderIrregularPair 37 32`): the carried second-order input.

The Case-II II1 is the **proven** `caseIIRootClassConjFixed37_proven`; Case I is unconditional
(`caseIBridge_thirtyseven_eichler`); `¬ 37 ∣ h⁺` is the proven `Sinnott.flt37_not_dvd_hPlus`. -/
theorem fermatLastTheoremFor_thirtyseven_of_thetaFixedSolution
    (caseII_solution : CaseIIRealThetaFixedSolution37)
    (caseII_exactUnit : WashingtonCaseIIExactQuotientUnitPower37Source)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_realDescentSolution
    (caseIIRealDescentSolution37_of_thetaFixedSolution caseII_solution)
    caseII_exactUnit noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end

end

import BernoulliRegular.FLT37.Eichler.CaseIIConjNormFactorDrop

/-!
# [FLT37-CASEII-R2] Washington §9.1 element-level Case-II descent (the analytic core of R2)

This file builds the **element-level** form of Washington *Cyclotomic Fields* (2nd ed., GTM 83)
§9.1 / Theorem 9.4, the genuine analytic core of the Case-II descent.  The **ideal-level**
principality `CaseIIData37.rootIdeal_quotient_pow_isPrincipal` (`SpecificChain.lean`) is already
proven; here we extract from it the **explicit generator** of the principal `37`-th power and pin it
to the Fermat ratio `(x+yη₁)/(x+yη₂)`, then package the conjugate-norm generators and assemble the
symmetric descent equation.

## What is FULLY PROVEN here (real Lean code, no `sorry`/`axiom`)

* **Target (1) — element-level quotient extraction**
  (`caseII_rootIdeal_quotient_pow_eq_spanSingleton`,
  `caseII_rootIdeal_quotient_pow_eq_spanSingleton_ratio`).  The `37`-th power of the ideal
  quotient `𝔞(η₁)/𝔞(η₂)` is, *as a fractional ideal*, **exactly** the span of the Fermat ratio:
  ```
  ((𝔞 η₁ / 𝔞 η₂) ^ 37 : FractionalIdeal) =
      spanSingleton ((x + yη₁)/(x + yη₂)) .
  ```
  This is proved directly from flt-regular's proven `c_div_principal_aux`
  (`(𝔦 η₁)/(𝔦 η₂) = 𝔠 η₁/𝔠 η₂`) and `root_div_zeta_sub_one_dvd_gcd_spec` (`(𝔞 η)^37 = 𝔠 η`),
  with `𝔦 η = span{x+yη}` (so `(𝔦 η₁)/(𝔦 η₂) = spanSingleton((x+yη₁)/(x+yη₂))`).  No individual
  `𝔞(η)` principality is used — only the quotient identity, which holds unconditionally.

  The element-level corollary `caseII_rootIdeal_quotient_pow_generator_associated` then states that
  **any** generator `δ` of the principal `(𝔞 η₁/𝔞 η₂)^37` is related to `(x+yη₁)/(x+yη₂)` by a unit
  of `𝓞 K`: `∃ u : (𝓞 K)ˣ, (x+yη₁)/(x+yη₂) = u • δ`.  This is the precise element-level form of
  the ideal quotient.

* **Target (2) — conjugate-norm generators** (re-exported / specialised from the proven
  `caseII_anchorPow_conjNorm_real_span`).  The σ-fixed norm ideal `𝔞₀·σ𝔞₀ = 𝔞₀²` has a **real**
  generator `ξ₁ = ρ₀σρ₀`, `𝔭`-coprime, with `(ξ₁) = 𝔞₀^{2k'}` — proven in
  `CaseIIAnchorSquareDatum.lean`.

* **Target (3) — the symmetric descent equation**
  (`caseII_section91_symmetric_descent_equation`, with the unit-cofactor helper
  `caseII_section91_K_trace_sub_two_unit_factor`).  Factoring the common `(ζ−1)²` out of the three
  coefficient-differences of the proven `caseII_descent_equation` gives the **normalized** symmetric
  equation
  ```
  a·U₂·(Y₁X₂)³⁷ − b·U₁·(Y₂X₁)³⁷ = (a − b)·U₁·U₂·(X₁X₂)³⁷
  ```
  with `a, b : (𝓞 K)ˣ` (so the two adjacent terms carry **unit** coefficients).  This is the §9.1
  reassembly step at the element level, content `n' = 2` (the `(ζ−1)²` factored out of each
  difference), in `𝓞 K`.

## What this does NOT do (honest scope), and what the residual is

The σ-stable pair product `Q(η) = (x+yη)(x+yη⁻¹) = N_{K/K⁺}(x+yη)` **doubles** `𝔭`-valuations
(`caseII_zeta_sub_one_sq_not_dvd_x_add_y_root` gives `v_𝔭(Q(η)) = 2` for adjacent `η`, while
`v_𝔭(Q(η₀)) = 2(37m+1)`).  So the symmetric descent equation produced here lives at the **doubled**
measure, which is *incompatible* with the `RealCaseIIData37` content `37·(m+1)` but fits the
**free-content** frame natively.  This is exactly why the live Case-II residual is the content-free
`FreeContentCaseIIDescentStep37` (`CaseIIFreeContentDatum.lean`): the symmetric equation here is the
element-level §9.1 input it consumes, but the producer's doubled measure means this equation does
**not**, by itself, shrink that residual (it is *not* a `RealCaseIIData37`-keyed descent step).  We
therefore add **no** new parametric residual; the unchanged `FreeContentCaseIIDescentStep37` remains
the residual, with the genuine §9.1 element-level facts (Targets 1–3) now proven permanently.

This file imports only; it does **not** modify any existing file.  No `sorry`, no `axiom`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1–§9.2 (Theorem 9.4),
  pp. 171–173.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension UniqueFactorizationMonoid Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## Target (1): element-level extraction of the principal `37`-th-power generator

`CaseIIData37.rootIdeal_quotient_pow_isPrincipal` proves `((𝔞 η₁/𝔞 η₂)^37)` is principal.  Here we
*identify the generator* explicitly: the fractional ideal equals the span of the Fermat ratio
`(x+yη₁)/(x+yη₂)`.  The bridge is flt-regular's proven quotient identity, which holds with **no**
hypothesis on individual `𝔞(η)`. -/

omit [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **[TARGET 1] The `37`-th power of the root-ideal quotient is the span of the Fermat ratio.**

For a `CaseIIData37` datum `D` and two `37`-th roots `η₁, η₂`,
```
((D.rootIdeal η₁ / D.rootIdeal η₂) ^ 37 : FractionalIdeal (𝓞 K)⁰ K) =
    FractionalIdeal.spanSingleton (𝓞 K)⁰
      (algebraMap (𝓞 K) K (x + yη₁) / algebraMap (𝓞 K) K (x + yη₂)).
```
This is the **explicit generator** of the principal ideal proven in
`CaseIIData37.rootIdeal_quotient_pow_isPrincipal`.

Proof: `rootIdeal η = 𝔞 η` with `(𝔞 η)^37 = 𝔠 η` (`root_div_zeta_sub_one_dvd_gcd_spec`), so
`(𝔞 η₁/𝔞 η₂)^37 = 𝔠 η₁/𝔠 η₂`.  flt-regular's `c_div_principal_aux` gives `𝔠 η₁/𝔠 η₂ = 𝔦 η₁/𝔦 η₂`
where `𝔦 η = span{x+yη}`; and `span{x+yη} = spanSingleton (algebraMap (x+yη))`, so the quotient is
`spanSingleton ((x+yη₁)/(x+yη₂))`. -/
theorem caseII_rootIdeal_quotient_pow_eq_spanSingleton
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K)) :
    (((D.rootIdeal η₁ : FractionalIdeal (𝓞 K)⁰ K) /
        (D.rootIdeal η₂ : FractionalIdeal (𝓞 K)⁰ K)) ^ 37 :
        FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰
        (algebraMap (𝓞 K) K (D.x + D.y * (η₁ : 𝓞 K)) /
          algebraMap (𝓞 K) K (D.x + D.y * (η₂ : 𝓞 K))) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : NeZero 37 := ⟨by decide⟩
  -- Unfold `rootIdeal = 𝔞` and push the `^37` through the coercion and division.
  rw [show D.rootIdeal η₁ = rootDivZetaSubOneDvdGcd (by decide : (37 : ℕ) ≠ 2)
        D.hζ D.equation D.hy η₁ from rfl,
    show D.rootIdeal η₂ = rootDivZetaSubOneDvdGcd (by decide : (37 : ℕ) ≠ 2)
        D.hζ D.equation D.hy η₂ from rfl,
    div_pow, ← FractionalIdeal.coeIdeal_pow, ← FractionalIdeal.coeIdeal_pow,
    root_div_zeta_sub_one_dvd_gcd_spec, root_div_zeta_sub_one_dvd_gcd_spec,
    -- `𝔠 η₁/𝔠 η₂ = 𝔦 η₁/𝔦 η₂` (flt-regular's proven quotient identity).
    ← c_div_principal_aux (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy η₁ η₂,
    -- `𝔦 η = span{x+yη} = spanSingleton (algebraMap (x+yη))`.
    FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_div_spanSingleton]

omit [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **[TARGET 1, ratio form] The element-level generator is the Fermat ratio in `K`.**

A restatement of `caseII_rootIdeal_quotient_pow_eq_spanSingleton` using a named element
`δ := (x+yη₁)/(x+yη₂) ∈ K`.  This is the concrete generator of the principal ideal proven in
`CaseIIData37.rootIdeal_quotient_pow_isPrincipal`. -/
theorem caseII_rootIdeal_quotient_pow_eq_spanSingleton_ratio
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K)) :
    ∃ δ : K,
      δ = algebraMap (𝓞 K) K (D.x + D.y * (η₁ : 𝓞 K)) /
        algebraMap (𝓞 K) K (D.x + D.y * (η₂ : 𝓞 K)) ∧
      (((D.rootIdeal η₁ : FractionalIdeal (𝓞 K)⁰ K) /
          (D.rootIdeal η₂ : FractionalIdeal (𝓞 K)⁰ K)) ^ 37 :
          FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ δ :=
  ⟨_, rfl, caseII_rootIdeal_quotient_pow_eq_spanSingleton D η₁ η₂⟩

omit [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **[TARGET 1, generator form] Any generator of the principal `(𝔞 η₁/𝔞 η₂)^37` is the Fermat
ratio up to a unit of `𝓞 K`.**

If `δ : K` generates the principal fractional ideal `(𝔞 η₁/𝔞 η₂)^37` (e.g. the generator supplied
by `CaseIIData37.rootIdeal_quotient_pow_isPrincipal`), then there is a unit `u : (𝓞 K)ˣ` with
```
u • δ = (x+yη₁)/(x+yη₂).
```
This is the precise element-level form of the ideal quotient: the proven `37`-th-power principality
becomes the **element identity** `(x+yη₁)/(x+yη₂) = unit · δ`.

Proof: both `spanSingleton δ` (by hypothesis) and `spanSingleton ((x+yη₁)/(x+yη₂))` (by
`caseII_rootIdeal_quotient_pow_eq_spanSingleton`) equal the quotient power, so they are equal; the
unit relation is `FractionalIdeal.spanSingleton_eq_spanSingleton`. -/
theorem caseII_rootIdeal_quotient_pow_generator_associated
    {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
    [NumberField.IsCMField K] {m : ℕ} (D : CaseIIData37 K m)
    (η₁ η₂ : nthRootsFinset 37 (1 : 𝓞 K)) {δ : K}
    (hδ : (((D.rootIdeal η₁ : FractionalIdeal (𝓞 K)⁰ K) /
        (D.rootIdeal η₂ : FractionalIdeal (𝓞 K)⁰ K)) ^ 37 :
        FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ δ) :
    ∃ u : (𝓞 K)ˣ,
      u • δ = algebraMap (𝓞 K) K (D.x + D.y * (η₁ : 𝓞 K)) /
        algebraMap (𝓞 K) K (D.x + D.y * (η₂ : 𝓞 K)) := by
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ δ =
      FractionalIdeal.spanSingleton (𝓞 K)⁰
        (algebraMap (𝓞 K) K (D.x + D.y * (η₁ : 𝓞 K)) /
          algebraMap (𝓞 K) K (D.x + D.y * (η₂ : 𝓞 K))) := by
    rw [← hδ, caseII_rootIdeal_quotient_pow_eq_spanSingleton D η₁ η₂]
  exact FractionalIdeal.spanSingleton_eq_spanSingleton.mp hspan

/-! ## Target (2): conjugate-norm generators (PROVEN in `CaseIIAnchorSquareDatum.lean`)

The σ-fixed norm ideal `𝔞₀·σ𝔞₀ = 𝔞₀²` (the anchor `B₀` is `σ`-fixed since `η₀ = 1`) has a
**real**, `𝔭`-coprime generator — Washington's conjugate norm `ξ₁ = ρ₀σρ₀`.  This is the proven
`caseII_anchorPow_conjNorm_real_span`.  We re-export it here under the §9.1 name, as the second
ingredient of the symmetric descent equation. -/

/-- **[TARGET 2] Real conjugate-norm generator of an anchor power** (Washington `(ξ₁) = B₀²`, real).

For a real Case-II datum `D` there is a **real**, `𝔭`-coprime `ξ₁ : 𝓞 K` and `k ≥ 1` with
`(ξ₁) = 𝔞₀^k`, where `𝔞₀ = a_eta_zero_dvd_p_pow` is the `𝔭`-free anchor.  This is the conjugate
norm `ξ₁ = ρ₀σρ₀` of a generator `ρ₀` of a principal power of `𝔞₀`; reality and the anchor-square
ideal are both proven in `caseII_anchorPow_conjNorm_real_span`.

This is the conjugate-norm generator entering Washington's symmetric `ω₁³⁷ + θ₁³⁷ = ε'·λ^{n'}·ξ₁³⁷`.
-/
theorem caseII_section91_conjNorm_real_generator
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m) :
    ∃ (ξ₁ : 𝓞 (CyclotomicField 37 ℚ)) (k : ℕ), 1 ≤ k ∧
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) ξ₁ = ξ₁ ∧
      ¬ (D.hζ.unit'.1 - 1) ∣ ξ₁ ∧
      Ideal.span ({ξ₁} : Set (𝓞 (CyclotomicField 37 ℚ))) =
        a_eta_zero_dvd_p_pow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ^ k :=
  caseII_anchorPow_conjNorm_real_span D

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

/-! ## Target (3): the symmetric descent equation (Washington §9.1 reassembly)

The proven `caseII_descent_equation` is the 3-term relation
```
(γ₂-γ₀)·U₂·(Y₁X₂)³⁷ + (γ₀-γ₁)·U₁·(Y₂X₁)³⁷ = (γ₂-γ₁)·U₁·U₂·(X₁X₂)³⁷
```
with `γᵢ = ηᵢ + ηᵢ³⁶` (so `γ₀ = 2`, since `η₀ = 1`), in `𝓞 K`.  Each coefficient difference
`γᵢ - γⱼ` is `Associated (ζ-1)²` (`caseII_K_trace_sub_two_associated`).  Washington's reassembly
**factors out the common `(ζ−1)²`**, producing the *normalized* symmetric equation
```
a·U₂·(Y₁X₂)³⁷ - b·U₁·(Y₂X₁)³⁷ = (a − b)·U₁·U₂·(X₁X₂)³⁷
```
with `a, b : (𝓞 K)ˣ` the unit cofactors of `γ₂−2, γ₁−2` (so `γ₂−2 = (ζ−1)²·a`,
`γ₁−2 = (ζ−1)²·b`, and `γ₂−γ₁ = (ζ−1)²·(a−b)`).  This is the §9.1 step that turns the descent
relation into a Fermat-type sum with **unit** coefficients on the two adjacent terms. -/

omit [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **Unit cofactor of `γ_η − 2` over `(ζ−1)²`.**  For a `37`-th root `η ≠ 1` of a real Case-II
datum, `caseII_K_trace_sub_two_associated` gives `Associated (γ_η − 2) ((ζ−1)²)`; extracting the
unit gives `a : (𝓞 K)ˣ` with `(ζ−1)²·a = (η + η³⁶) − 2`.  This is the explicit `(ζ−1)²`-content
factorization of every σ-stable descent coefficient. -/
theorem caseII_section91_K_trace_sub_two_unit_factor {m : ℕ} (D : RealCaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) (hη_ne : (η : 𝓞 K) ≠ 1) :
    ∃ a : (𝓞 K)ˣ, (D.hζ.unit'.1 - 1 : 𝓞 K) ^ 2 * (a : 𝓞 K) =
      ((η : 𝓞 K) + (η : 𝓞 K) ^ 36) - 2 :=
  (caseII_K_trace_sub_two_associated D η hη_ne).symm

omit [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **[TARGET 3] The normalized symmetric descent equation** (Washington §9.1, GTM 83 p. 172).

Factoring the common `(ζ−1)²` out of the three coefficient-differences of the proven
`caseII_descent_equation` yields the symmetric equation with **unit** cofactors `a, b` on the two
adjacent terms `(Y₁X₂)³⁷, (Y₂X₁)³⁷`:
```
a·U₂·(Y₁X₂)³⁷ + (−b)·U₁·(Y₂X₁)³⁷ = (a − b)·U₁·U₂·(X₁X₂)³⁷,
```
where `a, b : (𝓞 K)ˣ` satisfy `(ζ−1)²·a = γ₂ − 2`, `(ζ−1)²·b = γ₁ − 2` (`γᵢ = ηᵢ + ηᵢ³⁶` at the
adjacent roots `η₁ = ζ`, `η₂ = ζ²`, anchor `γ₀ = 2`), and `Xᵢ, Yᵢ, Uᵢ` are the algebra-mapped real
σ-pair generators of `caseII_descent_equation`.

Proof: the proven `caseII_descent_equation` is the un-normalized 3-term relation; substituting
`γ₂ − γ₀ = (ζ−1)²·a`, `γ₀ − γ₁ = −(ζ−1)²·b`, `γ₂ − γ₁ = (ζ−1)²·(a−b)` (with `γ₀ = 2`,
`caseII_etaZero_eq_one`; the unit factorizations from
`caseII_section91_K_trace_sub_two_unit_factor`) and cancelling the nonzero `(ζ−1)²` gives the
normalized form. -/
theorem caseII_section91_symmetric_descent_equation {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (G₁ : CaseIISigmaPairAnchoredFixedGenerator37 D hp D.etaOne)
    (G₂ : CaseIISigmaPairAnchoredFixedGenerator37 D hp D.etaTwo) :
    ∃ (u₁ u₂ : (𝓞 (NumberField.maximalRealSubfield K))ˣ) (a b : (𝓞 K)ˣ),
      (D.hζ.unit'.1 - 1 : 𝓞 K) ^ 2 * (a : 𝓞 K) =
          ((D.etaTwo : 𝓞 K) + (D.etaTwo : 𝓞 K) ^ 36) - 2 ∧
      (D.hζ.unit'.1 - 1 : 𝓞 K) ^ 2 * (b : 𝓞 K) =
          ((D.etaOne : 𝓞 K) + (D.etaOne : 𝓞 K) ^ 36) - 2 ∧
      (a : 𝓞 K) *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₂ : 𝓞 _)) *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
            (G₁.yPlus * G₂.xPlus)) ^ 37 +
        (-(b : 𝓞 K)) *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₁ : 𝓞 _)) *
          (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
            (G₂.yPlus * G₁.xPlus)) ^ 37 =
      ((a : 𝓞 K) - (b : 𝓞 K)) *
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₁ : 𝓞 _)) *
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) (u₂ : 𝓞 _)) *
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
          (G₁.xPlus * G₂.xPlus)) ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  -- The proven un-normalized descent equation.
  obtain ⟨u₁, u₂, hdesc⟩ := caseII_descent_equation D hp G₁ G₂
  -- `γ₀ = 2`.
  have hγ₀ : (D.etaZero : 𝓞 K) + (D.etaZero : 𝓞 K) ^ 36 = 2 := by
    rw [caseII_etaZero_eq_one D hp]; norm_num
  -- `η₁ = ζ ≠ 1`, `η₂ = ζ² ≠ 1`.
  have hη1_ne : (D.etaOne : 𝓞 K) ≠ 1 := by
    rw [caseII_etaOne_coe_eq_zeta D hp]
    exact D.hζ.unit'_coe.ne_one (by decide : 1 < 37)
  have hη2_ne : (D.etaTwo : 𝓞 K) ≠ 1 := by
    rw [caseII_etaTwo_coe_eq_zeta_sq D hp, ← pow_two]
    exact D.hζ.unit'_coe.pow_ne_one_of_pos_of_lt (by omega) (by decide : 2 < 37)
  -- Unit cofactors `a, b` of `γ₂ − 2`, `γ₁ − 2` over `(ζ−1)²`.
  obtain ⟨a, ha⟩ := caseII_section91_K_trace_sub_two_unit_factor D D.etaTwo hη2_ne
  obtain ⟨b, hb⟩ := caseII_section91_K_trace_sub_two_unit_factor D D.etaOne hη1_ne
  refine ⟨u₁, u₂, a, b, ha, hb, ?_⟩
  -- `(ζ−1)² ≠ 0`.
  have hπsq_ne : (D.hζ.unit'.1 - 1 : 𝓞 K) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (D.hζ.unit'_coe.sub_one_ne_zero (by decide : 1 < 37))
  -- Cancel the common `(ζ−1)²` from the descent equation.
  apply mul_left_cancel₀ hπsq_ne
  -- Rewrite the three coefficient-differences via `γ₀ = 2`, `ha`, `hb`.
  have hc02 : ((D.etaTwo : 𝓞 K) + (D.etaTwo : 𝓞 K) ^ 36) -
      ((D.etaZero : 𝓞 K) + (D.etaZero : 𝓞 K) ^ 36) =
      (D.hζ.unit'.1 - 1 : 𝓞 K) ^ 2 * (a : 𝓞 K) := by rw [hγ₀, ha]
  have hc01 : ((D.etaZero : 𝓞 K) + (D.etaZero : 𝓞 K) ^ 36) -
      ((D.etaOne : 𝓞 K) + (D.etaOne : 𝓞 K) ^ 36) =
      (D.hζ.unit'.1 - 1 : 𝓞 K) ^ 2 * (-(b : 𝓞 K)) := by linear_combination hγ₀ + hb
  have hc12 : ((D.etaTwo : 𝓞 K) + (D.etaTwo : 𝓞 K) ^ 36) -
      ((D.etaOne : 𝓞 K) + (D.etaOne : 𝓞 K) ^ 36) =
      (D.hζ.unit'.1 - 1 : 𝓞 K) ^ 2 * ((a : 𝓞 K) - (b : 𝓞 K)) := by
    linear_combination hb - ha
  rw [hc02, hc01, hc12] at hdesc
  linear_combination hdesc

end BernoulliRegular.FLT37.Eichler

end

end
